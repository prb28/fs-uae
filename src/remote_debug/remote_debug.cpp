// UAE - The Un*x Amiga Emulator
//
// GDB Stub for UAE.
//
// (c) 1995 Bernd Schmidt
// (c) 2006 Toni Wilen
// (c) 2016-2007 Daniel Collin (files remote_debug_* Semi GDB Implementation/remote debugger interface)
//
// This implementation is done from scratch and doesn't use any existing gdb-stub code.
// The idea is to supply a fairly minimal implementation in order to reduce maintaince.
//
// This is what according to the GDB protocol dock over here https://sourceware.org/gdb/current/onlinedocs/gdb/Overview.html
// is required of a stub:
//
// "At a minimum, a stub is required to support the 'g' and 'G' commands for register access, and the 'm' and 'M' commands for memory access.
// Stubs that only control single-threaded targets can implement run control with the 'c' (continue), and 's' (step) commands.
// Stubs that support multi-threading targets should support the 'vCont' command.
//
// All other commands are optional."
//
// This stub implements a set of extensions that isn't really used by GDB but makes sense in terms of Amiga.
// Some of these are copper debugging, blitter, dma, custom chipset stats, etc
//
// TODO: List and implement extensions
//
// DMA extent not really working yet
//-----------------
//
// QDmaLine
//
// GDB Extension for Amiga that shows DMA timings on one raster-line
//
// x size * u16 event, u16 type
//
// QDmaFrame
//
// Send a full-frame worth of timing data

#include "debug.h"
#include "remote_debug.h"
#ifdef REMOTE_DEBUGGER

#include "remote_debug_conn.h"

#include <string.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

#include "fs/conf.h"
#include "fs/log.h"
#include "sysconfig.h"
#include "sysdeps.h"
#include "options.h"
#include "memory.h"
#include "custom.h"
#include "newcpu.h"
#include "traps.h"
#include "autoconf.h"
#include "execlib.h"
#include "uae.h"
#include "debugmem.h"

//extern int exception_debugging;
extern int debugger_active;
extern bool debugmem_trace;
static rconn *s_conn = 0;

extern int debug_illegal;
extern uae_u64 debug_illegal_mask;

extern bool debugger_boot();

extern uae_u8 *save_custom(int *len, uae_u8 *dstptr, int full);

extern int debug_dma;

#define GDB_SIGNAL_INT 2			// Interrupt
#define GDB_SIGNAL_ILL 4			// Illegal instruction
#define GDB_SIGNAL_TRAP 5			// Trace/breakpoint trap
#define GDB_SIGNAL_EMT 7			// Emulation trap
#define GDB_SIGNAL_FPE 8 			// Arithmetic exception
#define GDB_SIGNAL_BUS 10			// Bus error
#define GDB_SIGNAL_SEGV 11			// Segmentation fault

#define DEFAULT_TRACEFRAME -1		// Traceframe default index

static char s_exe_to_run[4096];

static bool log_remote_protocol_enabled = false; // system env configuration : FS_DEBUG_REMOTE_PROTOCOL=1
static int old_active_debugger = 0;

typedef struct dma_info {
	uae_u32 event;
	uae_u32 type;
} dma_info;

typedef struct segment_info {
	uae_u32 address;
	uae_u32 size;
} segment_info;

static int live_mode = 0;
static int debug_dma_frame = 0;
static int dma_max_sizes[2][2];
static segment_info s_segment_info[512];
static int s_segment_count = 0;
static int remote_debug_illegal = 0;
static uae_u64 remote_debug_illegal_mask = 0;

#define MAX_BREAKPOINT_COUNT 512

enum DebuggerState
{
    Running,
    Tracing,
    // Used to step the CPU until we endup in the program we are debugging
    TraceToProgram,
};

static DebuggerState s_state = Running;

//
// Internal socket code
//

static bool step_cpu = false;
static bool did_step_cpu = false;
static uae_u8 s_lastSent[1024];
static int s_lastSize = 0;
static unsigned int s_socket_update_count = 0;
static int last_exception = 0;
static bool last_exception_sent = true;
static bool exception_send_pending = false;
static bool processing_message = false;
static uae_u32 last_exception_pc = 0;

bool need_ack = true;
static bool vRunCalled = false;
int current_traceframe = DEFAULT_TRACEFRAME;

// Declaration of the update_connection function
static void update_connection(void);

extern "C" {
    int remote_debugging = 0;
}


// This handles the case that we need to check if the emulator is quiting as we can be inside a loop
// and stepping. This works a bit different on FS-UAE and WinUAE so we handle it by having a diffrent impl for each emulator

#ifdef FSUAE

extern "C" int fs_emu_is_quitting();
int is_quiting() { return fs_emu_is_quitting(); }

#else

extern int quit_program;
int is_quiting() { return quit_program; }

#endif

// Return non-zero if the start of STRING matches PATTERN, zero
//   otherwise.
static inline int startswith (const char *string, const char *pattern)
{
  return strncmp (string, pattern, strlen (pattern)) == 0;
}

// Test if it is a hex value
static bool ishex(int ch, int *val)
{
	if ((ch >= 'a') && (ch <= 'f'))
	{
		*val = ch - 'a' + 10;
		return true;
	}
	if ((ch >= 'A') && (ch <= 'F'))
	{
		*val = ch - 'A' + 10;
		return true;
	}
	if ((ch >= '0') && (ch <= '9'))
	{
		*val = ch - '0';
		return true;
	}
	return false;
}

// Reads a hex value from the buffer
// TODO : remove this function
const char *unpack_varlen_hex(const char *buff, uae_u32 *result)
{
	int nibble;
	uae_u32 retval = 0;

	while (ishex(*buff, &nibble))
	{
		buff++;
		retval = retval << 4;
		retval |= nibble & 0x0f;
	}
	*result = retval;
	return buff;
}

//
// port allows to modify the server socket port
// time_out allows to set the time UAE will wait at startup for a connection.
// This is useful when wanting to debug things at early startup.
// If this is zero no time-out is set and if -1 no remote connection will be setup
//

static void remote_debug_init_ (int port, int time_out)
{
	if (s_conn || time_out < 0)
		return;

	log_remote_protocol_enabled = getenv("FS_DEBUG_REMOTE_DEBUGGER") && (getenv("FS_DEBUG_REMOTE_DEBUGGER")[0] == '1');
    if (fs_config_get_int(OPTION_REMOTE_DEBUGGER_LOG) > 0) {
        fs_log("[REMOTE_DEBUGGER] enable remote debugger logging\n");
        log_remote_protocol_enabled = 1;
    }

	fs_log("[REMOTE_DEBUGGER] creating connection...\n");

	if (!(s_conn = rconn_create (ConnectionType_Listener, port)))
		return;

	fs_log("[REMOTE_DEBUGGER] remote debugger active\n");

	debugmem_enable_stackframe(true);
	debugmem_trace = true;
	remote_debugging = 1;
	// if time_out > 0 we wait that number of seconds for a connection to be made. If
	// none has been done within the given time-frame we just continue

	for (int i = 0; i < time_out * 10; i++)	{
		update_connection();

		if (vRunCalled)
			return;

		sleep_millis (100); // sleep for 100 ms to not hammer on the socket while waiting
	}
}

struct Breakpoint {
    uaecptr address;
    uaecptr seg_address;
    uaecptr seg_id;
    bool enabled;
    bool needs_resolve;
    bool temp_break;
};

// used when skipping an instruction
static uaecptr s_skip_to_pc = 0xffffffff;

static Breakpoint s_breakpoints[MAX_BREAKPOINT_COUNT];
static int s_breakpoint_count = 0;

static int hex(char ch)
{
    if ((ch >= 'a') && (ch <= 'f'))
	    return ch - 'a' + 10;

    if ((ch >= '0') && (ch <= '9'))
	    return ch - '0';

    if ((ch >= 'A') && (ch <= 'F'))
	    return ch - 'A' + 10;

    return -1;
}

const int find_marker(const char* packet, const int offset, const char c, const int length)
{
    for (int i = 0; i < length; ++i) {
	    if (packet[i] == c)
		    return i;
    }

    return -1;
}

// Updated the parameters to activate the exception debugging
static void update_debug_illegal() {
	debug_illegal = remote_debug_illegal;
	debug_illegal_mask = remote_debug_illegal_mask; //0b1111111000000010000011110000000000000000011111111111100; //1 << 4;
}

static const char s_hexchars [] = "0123456789abcdef";
static const char* s_ok = "$OK#9a";

static int safe_addr (uaecptr addr, int size)
{
    addrbank* ab = &get_mem_bank (addr);

    if (!ab)
	    return 0;

    if (ab->flags & ABFLAG_SAFE)
	    return 1;

    if (!ab->check (addr, size))
	    return 0;

    if (ab->flags & (ABFLAG_RAM | ABFLAG_ROM | ABFLAG_ROMIN | ABFLAG_SAFE))
	    return 1;

    return 0;
}

static bool reply_ok()
{
	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] [<----] %s\n", s_ok);
	}
	return rconn_send (s_conn, s_ok, 6, 0) == 6;
}

static uae_u8* write_u32 (unsigned char* dest, uae_u32 v)
{
	uae_u8 c0 = (v >> 24) & 0xff;
	uae_u8 c1 = (v >> 16) & 0xff;
	uae_u8 c2 = (v >> 8) & 0xff;
	uae_u8 c3 = (v >> 0) & 0xff;

	*dest++ = s_hexchars[c0 >> 4];
	*dest++ = s_hexchars[c0 & 0xf];
	*dest++ = s_hexchars[c1 >> 4];
	*dest++ = s_hexchars[c1 & 0xf];
	*dest++ = s_hexchars[c2 >> 4];
	*dest++ = s_hexchars[c2 & 0xf];
	*dest++ = s_hexchars[c3 >> 4];
	*dest++ = s_hexchars[c3 & 0xf];

	return dest;
}

static uae_u8* write_u16 (unsigned char* dest, uae_u16 v)
{
    uae_u8 c0 = (v >> 8) & 0xff;
    uae_u8 c1 = (v >> 0) & 0xff;

    dest[0] = s_hexchars[c0 >> 4];
    dest[1] = s_hexchars[c0 & 0xf];
    dest[2] = s_hexchars[c1 >> 4];
    dest[3] = s_hexchars[c1 & 0xf];

    return dest + 4;
}

static uae_u8* write_u8 (unsigned char* dest, uae_u8 v)
{
    dest[0] = s_hexchars[v >> 4];
    dest[1] = s_hexchars[v & 0xf];

    return dest + 2;
}

static uae_u8* write_string (unsigned char* dest, const char* name)
{
    int len = strlen(name);
    memcpy(dest, name, len);
    return dest + len;
}


static uae_u8* write_double (uae_u8* dest, double v)
{
    union
    {
        double fp64;
        uae_u8 u8[8];
    } t;

    t.fp64 = v;

    for (int i = 0; i < 8; ++i)
    {
        uae_u8 c = t.u8[i];
        *dest++ = s_hexchars[c >> 4];
        *dest++ = s_hexchars[c & 0xf];
    }

    return dest;
}

//
// This code assumes that '$' has been added at the start and the length is subtrackted to not include it
//

static bool send_packet_in_place (unsigned char* t, int length)
{
    uae_u8 cs = 0;

    // + 1 as we calculate the cs one byte into the stream
    for (int i = 1; i < length+1; ++i) {
        uae_u8 temp = t[i];
        cs += t[i];
    }

    t[length + 1] = '#';
    t[length + 2] = s_hexchars[cs >> 4];
    t[length + 3] = s_hexchars[cs & 0xf];
    t[length + 4] = 0;

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] [<----] %s\n", t);
	}
    return rconn_send(s_conn, t, length + 4, 0) == length + 4;
}

static void send_packet_string (const char* string)
{
    uae_u8* s;
    uae_u8* t;
    uae_u8 cs = 0;
    int len = (int)strlen (string);
    s = t = xmalloc (uae_u8, len + 5);

    for (int i = 0; i < len; ++i)
	    cs += string[i];

    *t++ = '$';
    memcpy (t, string, len);

    t[len + 0] = '#';
    t[len + 1] = s_hexchars[cs >> 4];
    t[len + 2] = s_hexchars[cs & 0xf];
    t[len + 3] = 0;

    rconn_send(s_conn, s, len + 4, 0);

	if (log_remote_protocol_enabled) {
    	fs_log("[REMOTE_DEBUGGER] [<----] %s\n", s);
	}
    xfree(s);
}

static bool send_registers (void)
{
    uae_u8 registerBuffer[((18 * 4) + (8 * 8)) + (3 * 4) + 5 + 1] = { 0 }; // 16+2 regs + 8 (optional) FPU regs + 3 FPU control regs + space for tags
    uae_u8* t = registerBuffer;
    uae_u8* buffer = registerBuffer;

    uae_u32 temp;

    *buffer++ = '$';
	if (current_traceframe < 0) 
	{
		for (int i = 0; i < 8; ++i)
			buffer = write_u32 (buffer, m68k_dreg (regs, i));

		for (int i = 0; i < 8; ++i)
			buffer = write_u32 (buffer, m68k_areg (regs, i));

		buffer = write_u32 (buffer, regs.sr);
		buffer = write_u32 (buffer, m68k_getpc ());

		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] current pc %08x\n", m68k_getpc ());
		}

#ifdef FPUEMU
		/*
		if (currprefs.fpu_model)
		{
			for (int i = 0; i < 8; ++i)
				buffer = write_double (buffer, regs.fp[i].fp);

			buffer = write_u32 (buffer, regs.fpcr);
			buffer = write_u32 (buffer, regs.fpsr);
			buffer = write_u32 (buffer, regs.fpiar);
		}
		*/
#endif
	}
	else
	{
		// Retrive the curren frame
		int tfnum;
		debugstackframe *tframe = find_traceframe(false, current_traceframe, &tfnum);
		if (tframe)
		{
			for (int i = 0; i < 16; ++i)
				buffer = write_u32 (buffer, tframe->regs[i]);

			buffer = write_u32 (buffer, tframe->sr);
			buffer = write_u32 (buffer, tframe->current_pc);
		}
		else
		{
			fs_log("[REMOTE_DEBUGGER] The frame id '%d' is invalid\n", current_traceframe);
			send_packet_string (ERROR_INVALID_FRAME_ID);
			return false;
		}
		
	}

	if (log_remote_protocol_enabled) {
	    fs_log("[REMOTE_DEBUGGER] sending registers back\n");
	}

    return send_packet_in_place(t, (int)((uintptr_t)buffer - (uintptr_t)t) - 1);
}

static bool send_memory (char* packet)
{
    uae_u8* t;
    uae_u8* mem;
	uae_u8 *p1 = NULL;
	int len = 0;

	uaecptr address;
    int size;

    if (sscanf (packet, "%x,%x:", &address, &size) != 2)
    {
        fs_log("[REMOTE_DEBUGGER] failed to parse memory packet: %s\n", packet);
        send_packet_string (ERROR_SEND_MEMORY_PARSE);
        return false;
    }

    t = mem = xmalloc(uae_u8, (size * 2) + 7);

    *t++ = '$';

    for (int i = 0; i < size; ++i)
    {
	uae_u8 v = '?';

	if (safe_addr (address, 1)) {
		v = get_byte (address);
	} else {
		if (p1 == NULL) {
			p1 = save_custom(&len, 0, 1);
		}
		int idx = (address & 0x1ff) + 4;
		if (idx < len) {
			v = p1[idx];
		}
	}

	t[0] = s_hexchars[v >> 4];
	t[1] = s_hexchars[v & 0xf];

	address++; t += 2;
    }

    send_packet_in_place(mem, size * 2);

	if (p1 != NULL) {
		xfree(p1);
	}
    xfree(mem);

    return true;
}

bool set_memory (char* packet, int packet_length)
{
    uae_u8* t;
    uae_u8* mem;

    uaecptr address;
    int size;
    int memory_start = 0;

    if (sscanf (packet, "%x,%x:", &address, &size) != 2) {
	fs_log("[REMOTE_DEBUGGER] failed to parse set_memory packet: %s\n", packet);
	send_packet_string (ERROR_SET_MEMORY_PARSE);
	return false;
    }

    for (int i = 0; i < packet_length; ++i) {
	const uae_u8 t = packet[i];

	if (t == ':' || t == '#') {
	    memory_start = i + 1;
	    break;
	}
    }

    if (memory_start == 0) {
	fs_log("[REMOTE_DEBUGGER] Unable to find end tag for packet %s\n", packet);
	send_packet_string (ERROR_SET_MEMORY_PARSE_MISSING_END);
	return false;
    }

    packet += memory_start;

	if (log_remote_protocol_enabled) {
	    fs_log("[REMOTE_DEBUGGER] memory start %d - %s\n", memory_start, packet);
	}	

    for (int i = 0; i < size; ++i)
    {
	if (!safe_addr (address, 1)) {
	    send_packet_string (ERROR_SET_MEMORY_INVALID_ADDRESS);
	    return false;
	}

	uae_u8 t = hex(packet[0]) << 4 | hex(packet[1]);

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] setting memory %x-%x [%x] to %x\n", packet[0], packet[1], t, address);
	}
	packet += 2;

	put_byte (address++, t);
    }

    return reply_ok ();
}

bool set_register (char* packet, int packet_length)
{
    char name[256];
	int registerNumber;
	uaecptr value;

	if (sscanf (packet, "%x=%x#", &registerNumber, &value) != 2) {
		fs_log("[REMOTE_DEBUGGER] failed to parse set_register packet: %s\n", packet);
		send_packet_string (ERROR_SET_REGISTER_PARSE);
		return false;
    }

	if ((registerNumber < 0) || (registerNumber > REGISTER_LAST_VALID_INDEX)) {
		fs_log("[REMOTE_DEBUGGER] The register name '%s' is invalid\n", name);
		send_packet_string (ERROR_UNKOWN_REGISTER);
		return false;
	}
	if ((registerNumber <= REGISTER_D0_INDEX+7) && (registerNumber >= REGISTER_D0_INDEX)) {
		m68k_dreg (regs, registerNumber) = value;
	} else 	if ((registerNumber <= REGISTER_A0_INDEX+7) && (registerNumber >= REGISTER_A0_INDEX)) {
		m68k_areg (regs, registerNumber) = value;
	} else {
		fs_log("[REMOTE_DEBUGGER] The register name '%s' not supported\n", name);
		send_packet_string (ERROR_SET_REGISTER_NON_SUPPORTED);
		return false;
	}

    return reply_ok ();
}

bool get_register (char* packet, int packet_length)
{
	int registerNumber;
    uae_u8 messageBuffer[20] = { 0 };
    uae_u8* buffer = messageBuffer;
	*buffer++ = '$';

	if (sscanf(packet, "%x#", &registerNumber) != 1)
	{
		fs_log("[REMOTE_DEBUGGER] failed to parse get_register packet: %s\n", packet);
		send_packet_string (ERROR_GET_REGISTER_PARSE);
		return false;
    }

	if (current_traceframe < 0) 
	{
		if (registerNumber == REGISTER_PC_INDEX)
		{
			buffer = write_u32 (buffer, m68k_getpc());
		}
		else if (registerNumber == REGISTER_SR_INDEX)
		{
			buffer = write_u32 (buffer, regs.sr);
		}
		else if ((registerNumber <= REGISTER_D0_INDEX+7) && (registerNumber >= REGISTER_D0_INDEX))
		{
			buffer = write_u32 (buffer, m68k_dreg (regs, registerNumber - REGISTER_D0_INDEX));
		}
		else 	if ((registerNumber <= REGISTER_A0_INDEX+7) && (registerNumber >= REGISTER_A0_INDEX))
		{
			buffer = write_u32 (buffer, m68k_areg (regs, registerNumber - REGISTER_A0_INDEX));
		} else {
			fs_log("[REMOTE_DEBUGGER] The register number '%d' is invalid\n", registerNumber);
			send_packet_string (ERROR_UNKOWN_REGISTER);
			return false;
		}
	}
	else
	{
		// Retrive the curren frame
		int tfnum;
		debugstackframe *tframe = find_traceframe(false, current_traceframe, &tfnum);
		if (tframe)
		{
			if (registerNumber == REGISTER_PC_INDEX)
			{
				buffer = write_u32 (buffer, tframe->current_pc);
			}
			else if (registerNumber == REGISTER_SR_INDEX)
			{
				buffer = write_u32 (buffer, tframe->sr);
			}
			else if ((registerNumber <= REGISTER_D0_INDEX+7) && (registerNumber >= REGISTER_D0_INDEX))
			{
				buffer = write_u32(buffer, tframe->regs[registerNumber]);
			}
			else 	if ((registerNumber <= REGISTER_A0_INDEX+7) && (registerNumber >= REGISTER_A0_INDEX))
			{
				buffer = write_u32(buffer, tframe->regs[registerNumber]);
			} else {
				fs_log("[REMOTE_DEBUGGER] The register number '%d' is invalid\n", registerNumber);
				send_packet_string (ERROR_UNKOWN_REGISTER);
				return false;
			}
		}
		else
		{
			fs_log("[REMOTE_DEBUGGER] The frame id '%d' is invalid\n", current_traceframe);
			send_packet_string (ERROR_INVALID_FRAME_ID);
			return false;
		}
	}
	return send_packet_in_place(messageBuffer, 8);
}


static uae_u32 get_u32 (const uae_u8** data)
{
    const uae_u8* temp = *data;

    uae_u32 t[4];

    for (int i = 0; i < 4; ++i) {
	t[i] = hex(temp[0]) << 4 | hex(temp[1]);
	temp += 2;
    }

    *data = temp;

    return (t[0] << 24) | (t[1] << 16) | (t[2] << 8) | t[3];
}

static uae_u32 get_double (const uae_u8** data)
{
	const uae_u8* temp = *data;

	union {
	    double d;
	    uae_u8 u8[4];
	} t;

	for (int i = 0; i < 8; ++i) {
	    t.u8[i] = hex(temp[0]) << 4 | hex(temp[1]);
	    temp += 2;
	}

	*data = temp;

	return t.d;
}

static bool set_registers (const uae_u8* data)
{
    // order of registers are assumed to be
    // d0-d7, a0-a7, sr, pc [optional fp0-fp7, control, sr, iar)

    for (int i = 0; i < 8; ++i)
	m68k_dreg (regs, i) = get_u32(&data);

    for (int i = 0; i < 8; ++i)
	m68k_areg (regs, i) = get_u32(&data);

    regs.sr = get_u32 (&data);
    regs.pc = get_u32 (&data);

#ifdef FPUEMU
    /*
    if (currprefs.fpu_model)
    {
	for (int i = 0; i < 8; ++i)
		regs.fp[i].fp = get_double (&data);

	regs.fpcr = get_u32 (&data);
	regs.fpsr = get_u32 (&data);
	regs.fpiar = get_u32 (&data);
    }
    */
#endif

    reply_ok ();

    return false;
}


static int map_68k_exception(int exception) {
    int sig = 0;

    switch (exception)
    {
        case 2: sig = GDB_SIGNAL_BUS; break; // bus error
        case 3: sig = GDB_SIGNAL_BUS; break; // address error
        case 4: sig = GDB_SIGNAL_ILL; break; // illegal instruction
        case 5: sig = GDB_SIGNAL_FPE; break; // zero divide
        case 6: sig = GDB_SIGNAL_FPE; break; // chk instruction
        case 7: sig = GDB_SIGNAL_FPE; break; // trapv instruction
        case 8: sig = GDB_SIGNAL_SEGV; break; // privilege violation
        case 9: sig = GDB_SIGNAL_TRAP; break; // trace trap
        case 10: sig = GDB_SIGNAL_ILL; break; // line 1010 emulator
        case 11: sig = GDB_SIGNAL_ILL; break; // line 1111 emulator
        case 13: sig = GDB_SIGNAL_BUS; break; // Coprocessor protocol violation.  Using a standard MMU or FPU this cannot be triggered by software.  Call it a SIGBUS.
        case 31: sig = GDB_SIGNAL_INT; break; // interrupt
        case 32: sig = GDB_SIGNAL_TRAP; break; // interrupt
        case 33: sig = GDB_SIGNAL_TRAP; break; // breakpoint
        case 34: sig = GDB_SIGNAL_TRAP; break; // breakpoint
        case 40: sig = GDB_SIGNAL_FPE; break; // floating point err
        case 48: sig = GDB_SIGNAL_FPE; break; // floating point err
        case 49: sig = GDB_SIGNAL_FPE; break; // floating point err
        case 50: sig = GDB_SIGNAL_FPE; break; // zero divide
        case 51: sig = GDB_SIGNAL_FPE; break; // underflow
        case 52: sig = GDB_SIGNAL_FPE; break; // operand error
        case 53: sig = GDB_SIGNAL_FPE; break; // overflow
        case 54: sig = GDB_SIGNAL_FPE; break; // NAN
        default: sig = GDB_SIGNAL_EMT; // "software generated"
    }

    if ((sig == GDB_SIGNAL_ILL) || (sig == GDB_SIGNAL_FPE)) {
		fs_log("[REMOTE_DEBUGGER] exception %08x pc %08x: sig %08x\n", exception, last_exception_pc, sig);
		m68k_setpc (last_exception_pc);
    }

	return sig;
}


static bool send_exception (bool detailed) {
	if (processing_message) {
		// send is delayed
		exception_send_pending = true;
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] send exception delayed\n");
		}
		return true;
	}
	// this function will just exit if already connected
	rconn_update_listner(s_conn);

	unsigned char messageBuffer[512] = { 0 };
	uae_u8 *t = messageBuffer;
	uae_u8 *buffer = messageBuffer;
	int sig = 0;
	if (regs.spcflags & SPCFLAG_BRK) {
		// It's a breakpoint
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] send breakpoint halt %d\n", regs.spcflags);
		}
		sig = 5;
	} else {
		// It's a cpu exception
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] send exception %d\n", last_exception);
		}
		sig = map_68k_exception(last_exception);
	}

	*buffer++ = '$';
	if (detailed) {
		*buffer++ = 'T';
	} else  {
		*buffer++ = 'S';
	}
	buffer = write_u8(buffer, sig);

	if (detailed)
	{
		int regId = REGISTER_D0_INDEX;
		for (int i = 0; i < 8; ++i) {
			buffer = write_u8(buffer, regId++);
			*buffer++ = ':';
			buffer = write_u32 (buffer, m68k_dreg (regs, i));
			*buffer++ = ';';
		}

		regId = REGISTER_A0_INDEX;
		for (int i = 0; i < 8; ++i) {
			buffer = write_u8(buffer, regId++);
			*buffer++ = ':';
			buffer = write_u32 (buffer, m68k_areg (regs, i));
			*buffer++ = ';';
		}

		buffer = write_u8(buffer, REGISTER_SR_INDEX);
		*buffer++ = ':';
		buffer = write_u32 (buffer, regs.sr);
		*buffer++ = ';';
		buffer = write_u8(buffer, REGISTER_PC_INDEX);
		*buffer++ = ':';
		buffer = write_u32 (buffer, m68k_getpc ());
	}
    return send_packet_in_place(t, (int)((uintptr_t)buffer - (uintptr_t)t) - 1);
}


void remote_debug_check_exception_ (void) {
	int	nr = regs.exception;
	uae_u32 exception_pc = x_get_long (m68k_areg (regs, 7) + 2);
	if ((nr > 0) && debug_illegal && (nr <= 63) && (debug_illegal_mask & ((uae_u64)1 << nr)))
	{
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] Exception raised pc 0x%08x - code 0x%08x\n", exception_pc, nr);
		}
		last_exception = nr;
		last_exception_pc = exception_pc;
		last_exception_sent = false;
	}
}

static bool step()
{
	current_traceframe = DEFAULT_TRACEFRAME;
	set_special(SPCFLAG_BRK);
	step_cpu = true;
	did_step_cpu = true;

	if (s_segment_count > 0)
		s_state = TraceToProgram;
	else
		s_state = Tracing;

    activate_debugger ();

	//exception_debugging = 0;
	return true;
}

static bool step_next_instruction () {
	current_traceframe = DEFAULT_TRACEFRAME;
	uaecptr nextpc = 0;
	uaecptr pc = m68k_getpc ();
	m68k_disasm (pc, &nextpc, 0xffffffff, 1);

    activate_debugger ();

	step_cpu = true;
	did_step_cpu = true;
	//exception_debugging = 0;

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] current pc 0x%08x - next pc 0x%08x\n", pc, nextpc);
	}

	s_skip_to_pc = nextpc;
	s_state = Running;

	return true;
}

static void mem2hex(unsigned char* output, const unsigned char* input, int count)
{
	for (int i = 0; i < count; ++i)
	{
		unsigned char ch = *input++;
		*output++ = s_hexchars[ch >> 4];
		*output++ = s_hexchars[ch & 0xf];
	}

	*output = 0;
}

static bool handle_vrun (char* packet)
{
	// extract the args for vRun
	char* pch = strtok (packet, ";");

	if (log_remote_protocol_enabled) {
	    fs_log("[REMOTE_DEBUGGER] %s:%d\n", __FILE__, __LINE__);
	}

	if (pch) {
		strcpy(s_exe_to_run, pch);
		pch = strtok (0, pch);
		fs_log("[REMOTE_DEBUGGER] exe to run %s\n", s_exe_to_run);
	}

	//fs_log("[REMOTE_DEBUGGER] %s:%d\n", __FILE__, __LINE__);

	if (s_segment_count > 0) {
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] %s:%d\n", __FILE__, __LINE__);
		}
	    fs_log("[REMOTE_DEBUGGER] Is a program already running? Skip executing\n");
	    return true;
	}

	if (log_remote_protocol_enabled) {
	    fs_log("[REMOTE_DEBUGGER] %s:%d\n", __FILE__, __LINE__);
	}

	fs_log("[REMOTE_DEBUGGER] running debugger_boot\n");

	// TODO: Extract args
	vRunCalled = true;

	return true;
}

static bool handle_multi_letter_packet (char* packet, int length)
{
	int i = 0;

	// ‘v’ Packets starting with ‘v’ are identified by a multi-letter name, up to the first ‘;’ or ‘?’ (or the end of the packet).

	for (i = 0; i < length; ++i)
	{
		const char c = packet[i];

		if (c == ';' || c == '?' || c == '#')
			break;
	}

	// fine to assume that i is valid here as we have already checked that # is present

	packet[i] = 0;

	if (!strcmp(packet, "vRun")) {
		return handle_vrun (packet + 5);
	} else if (!strcmp(packet, "vCtrlC")) {
		set_special (SPCFLAG_BRK);
		send_exception (false);
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] switching to tracing\n");
		}
		s_state = Tracing;
		return true;
	} else {
		send_packet_string ("");
	}

	return false;
}

static bool handle_qtframe_packet(char *packet)
{
	uae_u32 frame, pc, lo, hi, num;
	int tfnum, tpnum, tfnumFound;
	struct debugstackframe *tframe;
	uae_u8 messageBuffer[50] = { 0 };
	uae_u8 *buffer = messageBuffer;
	uae_u8 *t = messageBuffer;
	*buffer++ = '$';

	packet += strlen("QTFrame:");

	if (*packet == '-')
	{
		// Must be '-1' : asking to reset the current frame
		tfnum = -1;
	}
	else
	{
		unpack_varlen_hex(packet, &frame);
		tfnum = (int)frame;
	}
	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] Want to look at traceframe %d", tfnum);
	}
	tframe = find_traceframe(false, tfnum, &tfnumFound);
	if (tframe)
	{
		current_traceframe = tfnum;
		*buffer++ = 'F';
		if (tfnumFound <= 0)
		{
			*buffer++ = '-';
			*buffer++ = '1';
		}
		else 
		{
			buffer = write_u32 (buffer, tfnumFound);
		}
	}
	else
	{
		*buffer++ = 'F';
		*buffer++ = '-';
		*buffer++ = '1';
	}
    return send_packet_in_place(t, (int)((uintptr_t)buffer - (uintptr_t)t) - 1);
}

static bool handle_query_packet(char* packet, int length)
{
	int i = 0;

	// ‘v’ Packets starting with ‘v’ are identified by a multi-letter name, up to the first ‘;’ or ‘?’ (or the end of the packet).

	for (i = 0; i < length; ++i)
	{
		const char c = packet[i];

		if (c == ':' || c == '?' || c == '#')
			break;
	}

	packet[i] = 0;

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] [query] %s\n", packet);
		fs_log("[REMOTE_DEBUGGER] handle_query_packet %d\n", __LINE__);
	}

	if (!strcmp ("QStartNoAckMode", packet)) {
		need_ack = false;
		return reply_ok ();
	}
	else if (!strcmp (packet, "qSupported")) {
		send_packet_string ("QStartNoAckMode+");
	}
	else if (!strcmp (packet, "QTFrame")) {
		handle_qtframe_packet(packet);
	}
	else {
		send_packet_string ("");
	}

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] handle_query_packet %d\n", __LINE__);
	}

	return true;
}

static bool handle_thread ()
{
	send_packet_string ("OK");
	return true;
}

static void deactive_debugger () {
	set_special (SPCFLAG_BRK);
	s_state = Running;
	debugger_active = 0;
	old_active_debugger = 0;
	exception_debugging = 0;
	step_cpu = true;
}

static bool kill_program () {
	deactive_debugger ();
	uae_reset (0, 0);
    s_segment_count = 0;

	return true;
}


static bool continue_exec (char* packet)
{
	// 'c [addr] Continue at addr, which is the address to resume. If addr is omitted, resume at current address.

	if (*packet != '#')
	{
		uae_u32 address;

		if (sscanf (packet, "%x#", &address) != 1)
		{
			fs_log("[REMOTE_DEBUGGER] Unable to parse continnue packet %s\n", packet);
			return false;
		}

		m68k_setpci(address);
	}

	fs_log("[REMOTE_DEBUGGER] remote_debug: start running...\n");

	deactive_debugger ();

	reply_ok ();

	return true;
}

static int has_breakpoint_address(uaecptr address)
{
	for (int i = 0; i < s_breakpoint_count; ++i)
	{
		if (s_breakpoints[i].address == address)
			return i;
	}

	return -1;
}

static void resolve_breakpoint_seg_offset (Breakpoint* breakpoint)
{
    uaecptr seg_id = breakpoint->seg_id;
    uaecptr seg_address = breakpoint->seg_address;

    if (seg_id >= s_segment_count)
    {
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] Segment id >= segment_count (%d - %d)\n", seg_id, s_segment_count);
		}
		breakpoint->needs_resolve = true;
		return;
    }

    breakpoint->address = s_segment_info[seg_id].address + seg_address;
    breakpoint->needs_resolve = false;

	if (log_remote_protocol_enabled) {
	    fs_log("[REMOTE_DEBUGGER] resolved breakpoint (%x - %x) -> 0x%08x\n", seg_address, seg_id, breakpoint->address);
	}
}

static bool set_offset_seg_breakpoint (uaecptr address, uae_u32 segment_id, int add)
{
    // Remove breakpoint

    if (!add)
    {
		for (int i = 0; i < s_breakpoint_count; ++i)
		{
			if (s_breakpoints[i].seg_address == address && s_breakpoints[i].seg_id == segment_id) {
			s_breakpoints[i] = s_breakpoints[s_breakpoint_count - 1];
			s_breakpoint_count--;
			return reply_ok ();
			}
		}
    }

	s_breakpoints[s_breakpoint_count].seg_address = address;
	s_breakpoints[s_breakpoint_count].seg_id = segment_id;

    resolve_breakpoint_seg_offset (&s_breakpoints[s_breakpoint_count]);

	s_breakpoint_count++;

    return reply_ok ();
}

static bool set_breakpoint_address (char* packet, int add)
{
	uaecptr address;
	uaecptr segment;

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] parsing breakpoint\n");
	}

	// if we have two args it means that the data is of type offset,segment and we need to resolve that.
	// if we are in running state we try to resolve it directly otherwise we just add it to the list
	// and resolve it after we loaded the executable

	int scan_res = sscanf (packet, "%x,%d", &address, &segment);

	if (scan_res == 2)
	{
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] offset 0x%x seg_id %d\n", address, segment);
		}
		return set_offset_seg_breakpoint (address, segment, add);
	}

	if (scan_res != 1)
	{
		fs_log("[REMOTE_DEBUGGER] failed to parse memory packet: %s\n", packet);
		send_packet_string ("");
		return false;
	}

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] parsed 0x%x\n", address);
		fs_log("[REMOTE_DEBUGGER] %s:%d\n", __FILE__, __LINE__);
	}

	int bp_offset = has_breakpoint_address(address);

	// Check if we already have a breakpoint at the address, if we do skip it

	if (!add)
	{
		if (bp_offset != -1)
		{
			if (log_remote_protocol_enabled) {
				fs_log("[REMOTE_DEBUGGER] Removed breakpoint at 0x%8x\n", address);
			}
			s_breakpoints[bp_offset] = s_breakpoints[s_breakpoint_count - 1];
			s_breakpoint_count--;
		}
		return reply_ok ();
	}

	if (s_breakpoint_count + 1 >= MAX_BREAKPOINT_COUNT)
	{
		fs_log("[REMOTE_DEBUGGER] Max number of breakpoints (%d) has been reached. Removed some to add new ones", MAX_BREAKPOINT_COUNT);
		send_packet_string ("");
		return false;
	}

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] Added breakpoint at 0x%08x\n", address);
	}

	s_breakpoints[s_breakpoint_count].address = address;
	s_breakpoint_count++;

	return reply_ok ();
}

// The message is z1,0,0;Xf,nnnnnnnnnnnnnnnn
//  address is 0 : not used
//  One parameter with 16 chars is the 64bit mask for exception filtering
static bool set_exception_breakpoint (char* packet, int add) {
	if (add < 1) {
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] Disabling exception debugging\n");
		}
		remote_debug_illegal = 0;
		remote_debug_illegal_mask = 0;
		update_debug_illegal();
		return reply_ok();
	} else {
		char mask[20] = {0};
		uae_u32 size;
		int scan_res = sscanf(packet, "0,0;X%x,%s#", &size, mask);
		if (scan_res == 2)
		{
			if (log_remote_protocol_enabled) {
				fs_log("[REMOTE_DEBUGGER] Mask read: %d\n", mask);
			}
			remote_debug_illegal = 1;
			remote_debug_illegal_mask = strtoul(mask, NULL, 16);
			update_debug_illegal();
			return reply_ok();
		}
		else
		{
			fs_log("[REMOTE_DEBUGGER] failed to parse memory packet: %s\n", packet);
			send_packet_string ("");
			return false;
		}
	}
}

static bool set_breakpoint (char* packet, int add)
{
	switch (*packet)
	{
		case '0' :
		{
			// software breakpoint
			// skip zero and  ,
			return set_breakpoint_address(packet + 2, add);
		}
		case '1' :
		{
			// Hardware breakpoint : used for exception breakpoint
			// skip 1 and  ,
			return set_exception_breakpoint(packet + 2, add);
		}
		default:
		{
			fs_log("[REMOTE_DEBUGGER] unknown breakpoint type\n");
			send_packet_string ("");
			return false;
		}
	}
}


static bool handle_packet(char* packet, int length)
{
	const char command = *packet;

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] handle packet %s\n", packet);
	}

	// ‘v’ Packets starting with ‘v’ are identified by a multi-letter name, up to the first ‘;’ or ‘?’ (or the end of the packet).

	if (command == 'v')
		return handle_multi_letter_packet(packet, length);

	if (command == 'q' || command == 'Q')
		return handle_query_packet(packet, length);

	switch (command)
	{
		case 'g' : return send_registers ();
		case 's' : return step ();
		case 'n' : return step_next_instruction ();
		case 'H' : return handle_thread ();
		case 'G' : return set_registers ((const uae_u8*)packet + 1);
		case '?' : return send_exception (true);
		case 'k' : return kill_program ();
		case 'm' : return send_memory (packet + 1);
		case 'M' : return set_memory (packet + 1, length - 1);
		case 'p' : return get_register (packet + 1, length - 1);
		case 'P' : return set_register (packet + 1, length - 1);
		case 'c' : return continue_exec (packet + 1);
		case 'Z' : return set_breakpoint (packet + 1, 1);
		case 'z' : return set_breakpoint (packet + 1, 0);

		default : send_packet_string ("");
	}

	return false;
}

static bool parse_packet(char* packet, int size)
{
	uae_u8 calc_checksum = 0;
	uae_u8 read_checksum = 0;
	int start, end;

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] parsing packet %s\n", packet);
	}

	/*
	if (*packet == '-' && size == 1)
	{
		fs_log("[REMOTE_DEBUGGER] *** Resending\n");
		rconn_send (s_conn, s_lastSent, s_lastSize, 0);
		return true;
	}
	*/

	// TODO: Do we need to handle data that strides several packtes?

	if ((start = find_marker(packet, 0, '$', size)) == -1)
		return false;

	if ((end = find_marker(packet, start, '#', size - start)) == -1)
		return false;

	// calc checksus

	for (int i = start + 1; i < end; ++i)
		calc_checksum += packet[i];

	// Read read the checksum and make sure they match

	read_checksum = hex(packet[end + 1]) << 4;
	read_checksum += hex(packet[end + 2]);

	if (read_checksum != calc_checksum) {
		if (need_ack) {
			if (log_remote_protocol_enabled) {
				fs_log("[REMOTE_DEBUGGER] [<----] -\n");
			}
			rconn_send (s_conn, "-", 1, 0);
		}

		fs_log("[REMOTE_DEBUGGER] mismatching checksum (calc 0x%x read 0x%x)\n", calc_checksum, read_checksum);
		return false;
	}

	if (need_ack) {
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] [<----] +\n");
		}
		rconn_send (s_conn, "+", 1, 0);
	}

	// set end of string on the end marker

	return handle_packet(&packet[start + 1], size - 1);
}


static void update_connection (void)
{
	if (is_quiting())
	    return;

	//fs_log("[REMOTE_DEBUGGER] updating connection\n");

	// this function will just exit if already connected
	rconn_update_listner (s_conn);

	if (rconn_poll_read(s_conn)) {
		char temp[1024] = { 0 };

		int size = rconn_recv(s_conn, temp, sizeof(temp), 0);

		processing_message = true;

		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] [---->] %s\n", temp);
		}

		if (size > 0)
			parse_packet(temp, size);

		processing_message = false;
	} else {
		if (exception_send_pending) {
			if (log_remote_protocol_enabled) {
				fs_log("[REMOTE_DEBUGGER] exception delayed (pending) sent\n");
			}
			send_exception(true);
			exception_send_pending = false;
		}
	}
}

// Main function that will be called when doing the actual debugging

static void remote_debug_ (void)
{
	uaecptr pc = m68k_getpc ();

	// As an exception stored
	if (!last_exception_sent && (last_exception > 0)) {
		send_exception (true);
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] switching to tracing\n");
		}
		s_state = Tracing;
		last_exception_sent = true;
	}
	else
	{
		// used when stepping over an instruction (useful to skip bsr/jsr/etc)

		if (s_skip_to_pc != 0xffffffff)
		{
			set_special (SPCFLAG_BRK);

			if (s_skip_to_pc == pc) {
				send_exception (false);
				s_state = Tracing;
				s_skip_to_pc = 0xffffffff;
			}
		}

		//fs_log("[REMOTE_DEBUGGER] update remote-Debug %d\n", s_state);

		for (int i = 0; i < s_breakpoint_count; ++i)
		{
			if (s_breakpoints[i].needs_resolve) {
				continue;
			}

			set_special (SPCFLAG_BRK);

			//fs_log("[REMOTE_DEBUGGER] checking breakpoint %08x - %08x\n", s_breakpoints[i].address, pc);

			if (s_breakpoints[i].address == pc)
			{
				//activate_debugger ();
				send_exception (false);
				if (log_remote_protocol_enabled) {
					fs_log("[REMOTE_DEBUGGER] switching to tracing\n");
				}
				s_state = Tracing;
				break;
			}
		}

		if (s_state == TraceToProgram)
		{
			set_special (SPCFLAG_BRK);

			for (int i = 0, end = s_segment_count; i < end; ++i) {
				const segment_info* seg = &s_segment_info[i];

				uae_u32 seg_start = seg->address;
				uae_u32 seg_end = seg->address + seg->size;

				if (pc >= seg_start && pc < seg_end) {
					if (log_remote_protocol_enabled) {
						fs_log("[REMOTE_DEBUGGER] switching to tracing\n");
					}
					s_state = Tracing;
					break;
				}
			}
		}

		/*
		if (debugger_active == 1 && old_active_debugger == 0) {
			did_step_cpu = true;
			step_cpu = false;
			s_state = Tracing;
			old_active_debugger = 1;
		}
		*/
	}

	// Check if we hit some breakpoint and then switch to tracing if we do

	switch (s_state)
	{
		case Running:
		{
			update_connection ();
			s_socket_update_count = 0;

			break;
		}

		case Tracing:
		{
			if (did_step_cpu) {
				if (log_remote_protocol_enabled) {
					fs_log("[REMOTE_DEBUGGER] did step cpu\n");
				}
				send_exception (false);
				did_step_cpu = false;
			}

			while (1)
			{
				update_connection ();

				if (step_cpu)
				{
					if (log_remote_protocol_enabled) {
						fs_log("[REMOTE_DEBUGGER] jumping back to uae for cpu step\n");
					}
					step_cpu = false;
					break;
				}

				if (is_quiting())
				{
					if (log_remote_protocol_enabled) {
						fs_log("[REMOTE_DEBUGGER] request quit\n");
					}
					s_state = Running;
					rconn_destroy(s_conn);
					s_conn = 0;
					break;
				}

				sleep_millis (1);	// don't hammer
			}

			break;
		}

		default:
			break;
	}
}

// This function needs to be called at regular interval to keep the socket connection alive

static void remote_debug_update_ (void)
{
	if (!s_conn)
		return;

	rconn_update_listner (s_conn);

	remote_debug_ ();
    activate_debugger ();
	//exception_debugging = 0;

	if (rconn_poll_read(s_conn)) {
		activate_debugger ();
		//exception_debugging = 0;
	}
	if (vRunCalled) {
		vRunCalled = !debugger_boot();
	}
}

extern uaecptr get_base (const uae_char *name, int offset);

// Called from debugger_helper. At this point CreateProcess has been called
// and we are resposible for filling out the data needed by the "RunCommand"
// that looks like this:
//
//    rc = RunCommand(seglist, stacksize, argptr, argsize)
//    D0		D1	   D2	    D3	    D4
//
//    LONG RunCommand(BPTR, ULONG, STRPTR, ULONG)
//
void remote_debug_start_executable (struct TrapContext *context)
{
#ifdef FSUAE
	uaecptr filename = ds (s_exe_to_run);
	uaecptr args = ds ("");
#else
	uaecptr filename = ds (_T(s_exe_to_run));
	uaecptr args = ds (_T(""));
#endif

	// so this is a hack to say that we aren't running from cli

	m68k_areg (regs, 1) = 0;
	uae_u32 curr_task = CallLib (context, get_long (4), -0x126); /* FindTask */

	// Patch wb message to say that we have no message to send otherwise
	// applications that tests this gets confused
	uae_u8* wb_message = get_real_address (curr_task + 0xac);
	wb_message[0] = 0;
	wb_message[1] = 0;
	wb_message[2] = 0;
	wb_message[3] = 1;

	uaecptr dosbase = get_base ("dos.library", 378);

	if (dosbase == 0) {
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] Unable to get dosbase\n");
		}
		return;
	}

    m68k_dreg (regs, 1) = filename;
	CallLib (context, dosbase, -150);

	// Get the segments for the executables (sent to debugger to match up the debug info)
    uaecptr segs = m68k_dreg (regs, 0);
	uaecptr seglist_addr = segs << 2;

    if (segs == 0) {
		fs_log("[REMOTE_DEBUGGER] Unable to load segs\n");
		return;
	}

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] About to send segments\n");
	}

	char buffer[1024] = { 0 };
	strcpy(buffer, "AS");

	s_segment_count = 0;

	uae_u32 ptr = seglist_addr;
	while(ptr != 0) {
		char temp[64];
		unsigned char addrStrTemp[9] = { 0 };
		unsigned char sizeStrTemp[9] = { 0 };

		uae_u32 size = get_long(ptr - 4) - 8; // size of BPTR + segment
		uae_u32 addr = ptr + 4;

		s_segment_info[s_segment_count].address = addr;
		s_segment_info[s_segment_count].size = size;

		write_u32(addrStrTemp, addr);
		write_u32(sizeStrTemp, size);
		sprintf(temp, ";%s;%s", addrStrTemp, sizeStrTemp);
		strcat(buffer, temp);

		s_segment_count++;

		ptr = get_long(ptr) << 2; // BPTR to next segment
	}

	// Resolving breakpoints before we start running. The allows us to have breakpoints before
	// the execution of the program (such stop at "main")

	for (int i = 0; i < s_breakpoint_count; ++i)
	{
	    Breakpoint* bp = &s_breakpoints[i];

	    if (!bp->needs_resolve)
			continue;

		resolve_breakpoint_seg_offset (bp);
	}

	send_packet_string (buffer);

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] segs to send back %s\n", buffer);
	}

	context_set_areg(context, 6, dosbase);
	context_set_dreg(context, 1, segs);
	context_set_dreg(context, 2, 4096);
	context_set_dreg(context, 3, args);
	context_set_dreg(context, 4, 0);

	update_debug_illegal();
	deactive_debugger ();

	fs_log("[REMOTE_DEBUGGER] remote_debug_start_executable\n");
}

void remote_debug_end_executable (struct TrapContext *context)
{
	fs_log("[REMOTE_DEBUGGER] remote_debug_end_executable\n");
	char buffer[1024] = {0};
	strcpy(buffer, "W00");
	send_packet_string(buffer);
}

//
// These are just wrappers to expose the code to C from C++
//

extern "C"
{
	void remote_debug_init(int port, int time_out) { return remote_debug_init_(port, time_out); }
	void remote_debug(void) { remote_debug_(); }
	void remote_debug_update(void) { remote_debug_update_(); }
	void remote_debug_check_exception(void) { remote_debug_check_exception_(); }
}

#endif


