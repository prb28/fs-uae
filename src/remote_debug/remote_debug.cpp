// UAE - The Un*x Amiga Emulator
//
// GDB Stub for UAE.
//
// (c) 1995 Bernd Schmidt
// (c) 2006 Toni Wilen
// (c) 2016-2007 Daniel Collin (files remote_debug_* Semi GDB Implementation/remote debugger interface)
// (c) 2019-2018 Paul Raingeard (Extension of GDB Implementation/remote debugger interface)
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
//-----------------
//
//-----------------
// The tracepoint implementation is incorrect
//  the QTFrame is used to select a frame, that modifies the behaviour of g command to get the registers
//  A phantom register (of index REGISTER_COPPER_ADDR_INDEX) is added to get the copper current address
//      this register can be retrieved with the get_register request
//-----------------
// Test with gdb (needs a gdb compiled for amiga arch)
// Example of launch command for fs-uae
//    fs-uae --chip_memory=1024 --hard_drive_0=vscode-amiga-wks-example/fs-uae/hd0 --joystick_port_1=none
//                --amiga_model=A1200 --slow_memory=1792 --remote_debugger=2000 --remote_debugger_log=1
//                --automatic_input_grab=0
// '.gdbinit' file:
//        set debug remote 1
//        set logging on
//        set logging overwrite on
//        target extended-remote localhost:6860
//        file vscode-amiga-wks-example/fs-uae/hd0/gencop
//        set remote exec-file dh0:gencop
//        run


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

extern int exception_debugging;
extern int debugger_active;
extern bool debugmem_trace;
static rconn *s_conn = 0;

extern int debug_illegal;
extern uae_u64 debug_illegal_mask;

extern bool debugger_boot();

extern uae_u8 *save_custom(int *len, uae_u8 *dstptr, int full);

extern int debug_dma;

extern int debug_copper;

#define GDB_SIGNAL_INT 2			// Interrupt
#define GDB_SIGNAL_ILL 4			// Illegal instruction
#define GDB_SIGNAL_TRAP 5			// Trace/breakpoint trap
#define GDB_SIGNAL_EMT 7			// Emulation trap
#define GDB_SIGNAL_FPE 8 			// Arithmetic exception
#define GDB_SIGNAL_BUS 10			// Bus error
#define GDB_SIGNAL_SEGV 11			// Segmentation fault

#define DEFAULT_TRACEFRAME -1		// Traceframe default index

#define PROCESS_ID_SYSTEM 1			// Process id designating system interrupts
#define THREAD_ID_AUD0	0			// Thread id designating AUDIO 0 interrupt
#define THREAD_ID_AUD1	1			// Thread id designating AUDIO 1 interrupt
#define THREAD_ID_AUD2	2			// Thread id designating AUDIO 2 interrupt
#define THREAD_ID_AUD3	3			// Thread id designating AUDIO 3 interrupt
#define THREAD_ID_DSK	4			// Thread id designating DISK interrupt
#define THREAD_ID_SPR	5			// Thread id designating SPRITE interrupt
#define THREAD_ID_BLT	6			// Thread id designating BLITTER interrupt
#define THREAD_ID_COP	7			// Thread id designating COPPER interrupt
#define THREAD_ID_BPL	8			// Thread id designating BIT-PLANE interrupt
#define THREAD_ID_CPU	0xf			// Thread id designating default cpu execution

#define BREAKPOINT_KIND_SEG_ID_MAX		99  // Maximum segment Id accepted in Breakpoint kind
#define BREAKPOINT_KIND_ABSOLUTE_ADDR	100 // Breakpoint Kind = Absolute address (no segment defined)
#define BREAKPOINT_KIND_MAX				100 // Maximum value for breakpoint kind

#define PACKET_SIZE		10240 // Communication packet max size

#define EXE_TO_RUN_BUFFER_SIZE 4096
static char s_exe_to_run[EXE_TO_RUN_BUFFER_SIZE];

static bool log_remote_protocol_enabled = false; // system env configuration : FS_DEBUG_REMOTE_PROTOCOL=1

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

// In real multi-process mode it should be useful
static int selected_process_id = PROCESS_ID_SYSTEM;
static int selected_thread_id = THREAD_ID_CPU;

// Multi process support act on thread id name : ppid.tid
static bool support_multiprocess = true;

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
static bool did_step_copper = false;
static uae_u8 s_last_sent[1024];
static int s_last_size = 0;
static unsigned int s_socket_update_count = 0;
static int last_exception = 0;
static bool last_exception_sent = true;
static bool exception_send_pending = false;
static int exception_send_pending_pid = PROCESS_ID_SYSTEM;
static int exception_send_pending_tid = THREAD_ID_CPU;
static bool processing_message = false;
static uae_u32 last_exception_pc = 0;

bool need_ack = true;
static bool vrun_called = false;
static bool debugger_boot_done = false;
int current_traceframe = DEFAULT_TRACEFRAME;
int current_vstopped_idx = 0;

// Declaration of the update_connection function
static void update_connection(void);
static void set_offset_seg_breakpoint (uaecptr offset, uae_u32 kind);

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

// Local command to deactivate the debugger
static void remote_deactivate_debugger () {
	set_special (SPCFLAG_BRK);
	s_state = Running;
	debugger_active = 0;
	exception_debugging = 0;
	step_cpu = true;
}

// Local command to activate the debugger
static void remote_activate_debugger () {
	// We keep the copper in debug mode to check the breakpoints
	if (debug_copper <= 0) {
		debug_copper = 1;
	}
	activate_debugger();
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

		if (vrun_called)
			return;

		sleep_millis (100); // sleep for 100 ms to not hammer on the socket while waiting
	}
}

/** Structure of a breakpoint */
struct Breakpoint {
    uaecptr address;		// Absolute address
    uaecptr offset;			// Offset in the segment
    uaecptr seg_id;			// id of the segment
	uae_u32 kind;			// Kind of breakpoint : BREAKPOINT_KIND_*
    bool needs_resolve;		// Has it been resolved : seg_id / offset only can be resolved when the program is loaded
};

// used when skipping an instruction
static uaecptr s_skip_to_pc = 0xffffffff;

static Breakpoint s_breakpoints[MAX_BREAKPOINT_COUNT];
static int s_breakpoint_count = 0;


/**
 * Parses an int from a hex char
 * 
 * @param ch char to parse
 * @return the integer value
 */
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

/**
 * Finds a marker in a buffer
 * 
 * @param packet packet buffer to search in
 * @param offset offset to start search
 * @param marker marker to search
 * @param length length of the packet
 * @return a position or -1 if it was not found
 */
const int find_marker(const char* packet, const int offset, const char marker, const int length)
{
    for (int i = offset; i < length; ++i) {
	    if (packet[i] == marker) {
		    return i;
		}
    }
    return -1;
}

/** Updated the parameters to activate the exception debugging */
static void update_debug_illegal() {
	debug_illegal = remote_debug_illegal;
	debug_illegal_mask = remote_debug_illegal_mask; //0b1111111000000010000011110000000000000000011111111111100; //1 << 4;
}

static const char s_hexchars [] = "0123456789abcdef";
static const char* s_ok = "$OK#9a";


/**
 * Finds if it is a safe address or not
 * 
 * @param addr Address to check
 * @param size Size of the address
 * @return true if it is a safe address
 */
static bool safe_addr (uaecptr addr, int size)
{
    addrbank* ab = &get_mem_bank (addr);

    if (!ab)
	    return false;

    if (ab->flags & ABFLAG_SAFE)
	    return true;

    if (!ab->check (addr, size))
	    return false;

    if (ab->flags & (ABFLAG_RAM | ABFLAG_ROM | ABFLAG_ROMIN | ABFLAG_SAFE))
	    return true;

    return false;
}


/**
 *  Reply a simple OK message
 */
static bool reply_ok()
{
	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] [<----] %s\n", s_ok);
	}
	return rconn_send (s_conn, s_ok, 6, 0) == 6;
}

/**
 * Write a u32 integer to a hex buffer
 * 
 * @param dest the destination buffer
 * @param v the value to insert
 * @return The next position (pointer) in the destination buffer
 */
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

/**
 * Write a u16 integer to a hex buffer
 * 
 * @param dest the destination buffer
 * @param v the value to insert
 * @return The next position (pointer) in the destination buffer
 */
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

/**
 * Write a u8 integer to a hex buffer
 * 
 * @param dest the destination buffer
 * @param v the value to insert
 * @return The next position (pointer) in the destination buffer
 */
static uae_u8* write_u8 (unsigned char* dest, uae_u8 v)
{
    dest[0] = s_hexchars[v >> 4];
    dest[1] = s_hexchars[v & 0xf];

    return dest + 2;
}

/**
 * Writes a string to the a buffer
 * 
 * @param dest the destination buffer
 * @param str string to write
 * @return The next position (pointer) in the destination buffer
 */
static uae_u8* write_string (unsigned char* dest, const char* str)
{
    int len = strlen(str);
    memcpy(dest, str, len);
    return dest + len;
}

/**
 * Reads a string in a hex buffer
 * 
 * @param hex_buffer Hex encoded buffer
 * @param dest_buffer Destination buffer for the decoded string
 * @param dest_buffer_size Destination buffer size
 */
static void read_string(const char *hex_buffer, char* dest_buffer, int dest_buffer_size)
{
	const char* current_hex = hex_buffer;
	int current_pos_dest = 0;
	size_t len = strlen(hex_buffer)/2;
	if (len > dest_buffer_size) {
		len = dest_buffer_size-1;
	}
	if (len > 0) {
		for (size_t i = 0; i < len; ++i) {
			dest_buffer[current_pos_dest] = hex(current_hex[0]) * 16 + hex(current_hex[1]);
			current_hex += 2;
			current_pos_dest++;
		}
	}
	if (current_pos_dest < dest_buffer_size) {
		dest_buffer[current_pos_dest] = '\0';
	}
}

/**
 * Writes a char to the a buffer
 * 
 * @param dest the destination buffer
 * @param c char to write
 * @return The next position (pointer) in the destination buffer
 */
static uae_u8* write_char (unsigned char* dest, const char c)
{
	*dest = c;
    return dest + 1;
}

/**
 * Writes the thread id in the destination buffer
 * 
 * @param dest the destination buffer
 * @param process_id the process id
 * @param thread_id the thread id
 * @return The next position (pointer) in the destination buffer
 */
static uae_u8* write_thread_id (unsigned char* dest, uae_u8 process_id, uae_u8 thread_id) {
	unsigned char* new_dest = dest;
	if (support_multiprocess) {
		new_dest = write_char(new_dest, 'p');
		new_dest = write_u8(new_dest, process_id);
		new_dest = write_char(new_dest, '.');
	}
	return write_u8(new_dest, thread_id);
}

/**
 * Write a double to a hex buffer
 * 
 * @param dest the destination buffer
 * @param v the value to insert
 * @return The next position (pointer) in the destination buffer
 */
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

/**
 * Sends a buffer
 * This code assumes that '$' has been added at the start and the length is subtrackted to not include it
 * 
 * @param t Buffer to send
 * @param length length of the buffer to send
 * @return True if it was send
 */
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

/**
 * Send a string message
 * 
 * @param string String to send
 * @return True if the send was done with no error
 */
static bool send_packet_string (const char* string)
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

    bool rc = rconn_send(s_conn, s, len + 4, 0);

	if (log_remote_protocol_enabled) {
    	fs_log("[REMOTE_DEBUGGER] [<----] %s\n", s);
	}
    xfree(s);
	return rc;
}

/**
 * Send the registers values
 * 
 * ‘XX…’
 *   Each byte of register data is described by two hex digits. The bytes with the register are transmitted in target byte order. The size of each register and their position within the ‘g’ packet are determined by the GDB internal gdbarch functions DEPRECATED_REGISTER_RAW_SIZE and gdbarch_register_name.
 *   When reading registers from a trace frame (see Using the Collected Data), the stub may also return a string of literal ‘x’’s in place of the register data digits, to indicate that the corresponding register has not been collected, thus its value is unavailable. For example, for an architecture with 4 registers of 4 bytes each, the following reply indicates to GDB that registers 0 and 2 have not been collected, while registers 1 and 3 have been collected, and both have zero value:
 *
 *  -> g
 *  <- xxxxxxxx00000000xxxxxxxx00000000
 *
 *‘E NN’
 *
 *   for an error. 
 *
 * @return true if was send without error
 */
static bool send_registers (void)
{
    uae_u8 register_buffer[((18 * 4) + (8 * 8)) + (3 * 4) + 5 + 1] = { 0 }; // 16+2 regs + 8 (optional) FPU regs + 3 FPU control regs + space for tags
    uae_u8* t = register_buffer;
    uae_u8* buffer = register_buffer;

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
		// if (currprefs.fpu_model)
		// {
		// 	for (int i = 0; i < 8; ++i)
		// 		buffer = write_double (buffer, regs.fp[i].fp);
		// 	buffer = write_u32 (buffer, regs.fpcr);
		// 	buffer = write_u32 (buffer, regs.fpsr);
		// 	buffer = write_u32 (buffer, regs.fpiar);
		// }
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
			fs_log("[REMOTE_DEBUGGER] Frame id '%d' is invalid\n", current_traceframe);
			send_packet_string (ERROR_INVALID_FRAME_ID);
			return false;
		}
		
	}

	if (log_remote_protocol_enabled) {
	    fs_log("[REMOTE_DEBUGGER] sending registers back\n");
	}

    return send_packet_in_place(t, (int)((uintptr_t)buffer - (uintptr_t)t) - 1);
}


/**
 * Handles a read memory request the dumped memory
 * 
 * ‘m addr,length’
 *   Read length addressable memory units starting at address addr (see addressable memory unit). Note that addr may not be aligned to any particular boundary.
 *   The stub need not use any particular size or alignment when gathering data from memory for the response; even if addr is word-aligned and length is a multiple of the word size, the stub is free to use byte accesses, or not. For this reason, this packet may not be suitable for accessing memory-mapped I/O devices.
 *   Reply:
 *   ‘XX…’
 *       Memory contents; each byte is transmitted as a two-digit hexadecimal number. The reply may contain fewer addressable memory units than requested if the server was able to read only part of the region of memory. 
 *   ‘E NN’
 *       NN is errno 
 * @param packet packet containing the request message
 * @return true if was send without error
 */
static bool handle_read_memory (char* packet)
{
    uae_u8* t;
    uae_u8* mem;
	uae_u8 *p1 = NULL;
	int len = 0;
	bool valid_output = false;

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
		valid_output = true;
	} else {
		if ((address >= 0xdff000) && (address < 0xdff1fe)) {
			if (p1 == NULL) {
				p1 = save_custom(&len, 0, 1);
			}
			int idx = (address & 0x1ff) + 4;
			if ((idx > 0) && (idx < len)) {
				v = p1[idx];
				valid_output = true;
			}
		}
	}

	t[0] = s_hexchars[v >> 4];
	t[1] = s_hexchars[v & 0xf];

	address++; t += 2;
    }

	if (valid_output) {
    	send_packet_in_place(mem, size * 2);
	} else {
		fs_log("[REMOTE_DEBUGGER] Invalid memory address required by packet: %s\n", packet);
		send_packet_string (ERROR_INVALID_MEMORY_LOCATION);
	}

	if (p1 != NULL) {
		xfree(p1);
	}
    xfree(mem);

    return valid_output;
}

/**
 * Handles a set memory request
 * ‘M addr,length:XX…’
 *   Write length addressable memory units starting at address addr (see addressable memory unit). The data is given by XX…; each byte is transmitted as a two-digit hexadecimal number.
 *   Reply:
 *   ‘OK’
 *       for success 
 *   ‘E NN’
 *       for an error (this includes the case where only part of the data was written). 
 * @param packet packet containing the request message
 * @param packet_length Length of the packet
 * @return true if was send without error
 */
bool handle_set_memory (char* packet, int packet_length)
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

/**
 * Handles a set register request
 *‘P n…=r…’
 *   Write register n… with value r…. The register number n is in hexadecimal, and r… contains two hex digits for each byte in the register (target byte order).
 *   Reply:
 *   ‘OK’
 *       for success 
 *   ‘E NN’
 *       for an error 
 * @param packet packet containing the request message
 * @param packet_length Length of the packet
 * @return true if was send without error
 */
bool handle_set_register (char* packet, int packet_length)
{
    char name[256];
	int register_number;
	uaecptr value;

	if (sscanf (packet, "%x=%x#", &register_number, &value) != 2) {
		fs_log("[REMOTE_DEBUGGER] failed to parse set_register packet: %s\n", packet);
		send_packet_string (ERROR_SET_REGISTER_PARSE);
		return false;
    }

	if ((register_number < 0) || (register_number > REGISTER_LAST_VALID_INDEX)) {
		fs_log("[REMOTE_DEBUGGER] The register name '%s' is invalid\n", name);
		send_packet_string (ERROR_UNKOWN_REGISTER);
		return false;
	}
	if ((register_number <= REGISTER_D0_INDEX+7) && (register_number >= REGISTER_D0_INDEX)) {
		m68k_dreg (regs, register_number) = value;
	} else 	if ((register_number <= REGISTER_A0_INDEX+7) && (register_number >= REGISTER_A0_INDEX)) {
		m68k_areg (regs, register_number) = value;
	} else {
		fs_log("[REMOTE_DEBUGGER] The register name '%s' not supported\n", name);
		send_packet_string (ERROR_SET_REGISTER_NON_SUPPORTED);
		return false;
	}

    return reply_ok ();
}

/**
 * Handles a get register request
 *‘p n’
 *   Read the value of register n; n is in hex. See read registers packet, for a description of how the returned register value is encoded.
 *   Reply:
 *   ‘XX…’
 *       the register’s value 
 *   ‘E NN’
 *       for an error 
 *   ‘’
 *       Indicating an unrecognized query. 
 * @param packet packet containing the request message
 * @param packet_length Length of the packet
 * @return true if was send without error
 */
bool handle_get_register (char* packet, int packet_length)
{
	int register_number;
    uae_u8 message_buffer[20] = { 0 };
    uae_u8* buffer = message_buffer;
	*buffer++ = '$';

	if (sscanf(packet, "%x#", &register_number) != 1)
	{
		fs_log("[REMOTE_DEBUGGER] failed to parse get_register packet: %s\n", packet);
		send_packet_string (ERROR_GET_REGISTER_PARSE);
		return false;
    }

	if (current_traceframe < 0) 
	{
		if (register_number == REGISTER_PC_INDEX)
		{
			buffer = write_u32 (buffer, m68k_getpc());
		}
		else if (register_number == REGISTER_COPPER_ADDR_INDEX)
		{
			buffer = write_u32 (buffer, get_copper_address(-1));
		}
		else if (register_number == REGISTER_SR_INDEX)
		{
			buffer = write_u32 (buffer, regs.sr);
		}
		else if ((register_number <= REGISTER_D0_INDEX+7) && (register_number >= REGISTER_D0_INDEX))
		{
			buffer = write_u32 (buffer, m68k_dreg (regs, register_number - REGISTER_D0_INDEX));
		}
		else if ((register_number <= REGISTER_A0_INDEX+7) && (register_number >= REGISTER_A0_INDEX))
		{
			buffer = write_u32 (buffer, m68k_areg (regs, register_number - REGISTER_A0_INDEX));
		} else {
			fs_log("[REMOTE_DEBUGGER] The register number '%d' is invalid\n", register_number);
			buffer = write_string (buffer, "xxxxxxxx");
		}
	}
	else
	{
		// Retrive the curren frame
		int tfnum;
		debugstackframe *tframe = find_traceframe(false, current_traceframe, &tfnum);
		if (tframe)
		{
			if (register_number == REGISTER_PC_INDEX)
			{
				buffer = write_u32 (buffer, tframe->current_pc);
			}
			else if (register_number == REGISTER_COPPER_ADDR_INDEX)
			{
				buffer = write_u32 (buffer, get_copper_address(-1));
			}
			else if (register_number == REGISTER_SR_INDEX)
			{
				buffer = write_u32 (buffer, tframe->sr);
			}
			else if ((register_number <= REGISTER_D0_INDEX+7) && (register_number >= REGISTER_D0_INDEX))
			{
				buffer = write_u32(buffer, tframe->regs[register_number]);
			}
			else 	if ((register_number <= REGISTER_A0_INDEX+7) && (register_number >= REGISTER_A0_INDEX))
			{
				buffer = write_u32(buffer, tframe->regs[register_number]);
			} else {
				fs_log("[REMOTE_DEBUGGER] The register number '%d' is invalid\n", register_number);
				buffer = write_string (buffer, "xxxxxxxx");
			}
		}
		else
		{
			fs_log("[REMOTE_DEBUGGER] The frame id '%d' is invalid\n", current_traceframe);
			send_packet_string (ERROR_INVALID_FRAME_ID);
			return false;
		}
	}
	return send_packet_in_place(message_buffer, 8);
}

/**
 * Get the u32 value from hex data
 * 
 * @param data Data to parse
 * @return value parsed
 */
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

/**
 * Get the double value from hex data
 * 
 * @param data Data to parse
 * @return value parsed
 */
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

/**
 * Handles a set registers request
 *‘G XX…’
 *   Write general registers. See read registers packet, for a description of the XX… data.
 *   Reply:
 *   ‘OK’
 *       for success 
 *   ‘E NN’
 *       for an error 
 * @param data Data containing the registers values
 * @return true if was send without error
 */
static bool handle_set_registers (const uae_u8* data)
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
    return reply_ok ();
}


/**
 * Maps m68k exception signals to GDB standard signals
 * 
 * @param exception signal
 * @return GDB signal
 */
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

/**
 * Write a exception description in a reply buffer
 * ‘S AA’
 *   The program received signal number AA (a two-digit hexadecimal number). This is equivalent to a ‘T’ response with no n:r pairs.
 *‘T AA n1:r1;n2:r2;…’
 *   The program received signal number AA (a two-digit hexadecimal number). This is equivalent to an ‘S’ response, except that the ‘n:r’ pairs can carry values of important registers and other information directly in the stop reply packet, reducing round-trip latency. Single-step and breakpoint traps are reported this way. Each ‘n:r’ pair is interpreted as follows:
 *       If n is a hexadecimal number, it is a register number, and the corresponding r gives that register’s value. The data r is a series of bytes in target byte order, with each byte given by a two-digit hex number.
 *       If n is ‘thread’, then r is the thread-id of the stopped thread, as specified in thread-id syntax.
 *       If n is ‘core’, then r is the hexadecimal number of the core on which the stop event was detected.
 *       If n is a recognized stop reason, it describes a more specific event that stopped the target. The currently defined stop reasons are listed below. The aa should be ‘05’, the trap signal. At most one stop reason should be present.
 *       Otherwise, GDB should ignore this ‘n:r’ pair and go on to the next; this allows us to extend the protocol in the future. 
 * @param message_buffer Message buffer destination
 * @param process_id Process id
 * @param thread_id Thread id
 * @param detailed If true we will send a detailed message 'T', if false a standard message 'S'
 * @param is_notification If true the message will be formated as a notification, with a name
 * @return uae_u8* Next position to write in the buffer
 */
static uae_u8* write_exception (unsigned char *message_buffer, int process_id, int thread_id, bool detailed, bool is_notification) {
	uae_u8 *buffer = message_buffer;
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

	buffer = write_char(buffer, '$');
	if (is_notification) {
		buffer = write_string(buffer, "%Stop:");
	}
	if (detailed) {
		buffer = write_char(buffer, 'T');
	} else  {
		buffer = write_char(buffer, 'S');
	}
	buffer = write_u8(buffer, sig);
	buffer = write_char(buffer, ';');

	if (detailed)
	{
		// Stop reason
		if (sig == GDB_SIGNAL_TRAP) {
			buffer = write_string(buffer, "swbreak");
		} else {
			buffer = write_string(buffer, "hwbreak");
		}
		buffer = write_char(buffer, ':');
		buffer = write_char(buffer, ';');
		
		// Thread id
		buffer = write_string(buffer, "thread");
		buffer = write_char(buffer, ':');
		buffer = write_thread_id(buffer, process_id, thread_id);
		buffer = write_char(buffer, ';');

		int reg_id = REGISTER_D0_INDEX;
		for (int i = 0; i < 8; ++i) {
			buffer = write_u8(buffer, reg_id++);
			buffer = write_char(buffer, ':');
			buffer = write_u32 (buffer, m68k_dreg (regs, i));
			buffer = write_char(buffer, ';');
		}

		reg_id = REGISTER_A0_INDEX;
		for (int i = 0; i < 8; ++i) {
			buffer = write_u8(buffer, reg_id++);
			buffer = write_char(buffer, ':');
			buffer = write_u32 (buffer, m68k_areg (regs, i));
			buffer = write_char(buffer, ';');
		}

		buffer = write_u8(buffer, REGISTER_SR_INDEX);
		buffer = write_char(buffer, ':');
		buffer = write_u32 (buffer, regs.sr);
		buffer = write_char(buffer, ';');
		buffer = write_u8(buffer, REGISTER_PC_INDEX);
		buffer = write_char(buffer, ':');
		buffer = write_u32 (buffer, m68k_getpc ());
		buffer = write_char(buffer, ';');

		// // Other registers filled with 0
		// for (int i = REGISTER_PC_INDEX + 1; i < REGISTER_COPPER_ADDR_INDEX; i++) {
		// 	buffer = write_u8(buffer, i);
		// 	buffer = write_char(buffer, ':');
		// 	buffer = write_u32 (buffer, 0);
		// 	buffer = write_char(buffer, ';');
		// }
	}
	return buffer;
}


/**
 * Write a exception description in a reply buffer
 * 
 * @param process_id Process id
 * @param thread_id Thread id
 * @param detailed If true we will send a detailed message 'T', if false a standard message 'S'
 * @param send_now If false the exception will be sent later in the process
 * @param is_notification If true the message will be formated as a notification, with a name
 * @return true if the response was sent without error
 */
static bool send_exception (int process_id, int thread_id, bool detailed, bool send_now, bool is_notification) {
	if (processing_message && !send_now) {
		// send is delayed
		exception_send_pending = true;
		exception_send_pending_pid = process_id;
		exception_send_pending_tid = thread_id;
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] send exception delayed\n");
		}
		return true;
	}
	// this function will just exit if already connected
	rconn_update_listner(s_conn);

	unsigned char message_buffer[512] = { 0 };
	uae_u8 *t = message_buffer;
	uae_u8 *buffer = write_exception (message_buffer, process_id, thread_id, detailed, is_notification);
    return send_packet_in_place(t, (int)((uintptr_t)buffer - (uintptr_t)t) - 1);
}

/**
 * Callback to let the remote debugger check if there is an exception triggered
 */
void remote_debug_check_exception_ (void) {
	int	nr = regs.exception;
	if ((nr > 0) && debug_illegal && (nr <= 63) && (debug_illegal_mask & ((uae_u64)1 << nr)))
	{
		uae_u32 exception_pc = x_get_long (m68k_areg (regs, 7) + 2);
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] Exception raised pc 0x%08x - code 0x%08x\n", exception_pc, nr);
		}
		last_exception = nr;
		last_exception_pc = exception_pc;
		last_exception_sent = false;
	}
}

/**
 * Step command
 * 
 * @param process_id Process id
 * @param thread_id Thread id
 * @return true if there is no error
 */
static bool step(int process_id, int thread_id)
{
	current_traceframe = DEFAULT_TRACEFRAME;
	if (thread_id == THREAD_ID_CPU) {
		// cpu step
		set_special(SPCFLAG_BRK);
		step_cpu = true;
		did_step_cpu = true;

		if (s_segment_count > 0)
			s_state = TraceToProgram;
		else
			s_state = Tracing;

		remote_activate_debugger ();
	} else if (thread_id == THREAD_ID_COP) {
		// copper step
		debug_copper = 1|2;
		did_step_copper = true;
		remote_deactivate_debugger();
	}
	//exception_debugging = 0;
	return true;
}

/**
 * Step to the next instruction command
 * 
 * @param process_id Process id
 * @param thread_id Thread id
 * @return true if there is no error
 */
static bool step_next_instruction (int process_id, int thread_id) {
	current_traceframe = DEFAULT_TRACEFRAME;
	if (thread_id == THREAD_ID_CPU) {
		uaecptr nextpc = 0;
		uaecptr pc = m68k_getpc ();
		m68k_disasm (pc, &nextpc, 0xffffffff, 1);

		remote_activate_debugger ();

		step_cpu = true;
		did_step_cpu = true;
		//exception_debugging = 0;

		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] current pc 0x%08x - next pc 0x%08x\n", pc, nextpc);
		}

		s_skip_to_pc = nextpc;
		s_state = Running;
	} else if (thread_id == THREAD_ID_COP) {
		// copper step
		debug_copper = 1|2;
		did_step_copper = true;
		remote_deactivate_debugger();
	}
	return true;
}

/**
 * Handles a vRun command 
 * ‘vRun;filename[;argument]…’
 *   Run the program filename, passing it each argument on its command line. The file and arguments are hex-encoded strings. If filename is an empty string, the stub may use a default program (e.g. the last program run). The program is created in the stopped state.
 *   This packet is only available in extended mode (see extended mode).
 *   Reply:
 *   ‘E nn’
 *       for an error 
 *   ‘Any stop packet’
 *       for success (see Stop Reply Packets) 
 * @param packet Containing the request
 * @return true if the response was sent without error
 */
static bool handle_vrun (char* packet)
{
	// extract the args for vRun
	char* pch = strtok (packet, ";");

	if (log_remote_protocol_enabled) {
	    fs_log("[REMOTE_DEBUGGER] %s:%d\n", __FILE__, __LINE__);
	}

	if (pch) {
		// The filename is coded in ascii/hex
		read_string(pch, s_exe_to_run, EXE_TO_RUN_BUFFER_SIZE);
		pch = strtok (0, pch);		
		fs_log("[REMOTE_DEBUGGER] exe to run %s\n", s_exe_to_run);
	}

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

	// adding the entry point breakpoint -> needed for the multi protocol of gdbserver
	// The first instruction in an amiga program is at Seg 0 offset 0
	set_offset_seg_breakpoint(0, 0);

	fs_log("[REMOTE_DEBUGGER] running debugger_boot\n");

	// TODO: Extract args
	vrun_called = true;

	// The return is sent a stop packet after the program launch.
	return true;
}

/**
 * Handles a QTFrame command 
 * ! Partial implementation : Not real tracepoint implentation
 *‘QTFrame:n’
 *   Select the n’th tracepoint frame from the buffer, and use the register and memory contents recorded there to answer subsequent request packets from GDB.
 *   A successful reply from the stub indicates that the stub has found the requested frame. The response is a series of parts, concatenated without separators, describing the frame we selected. Each part has one of the following forms:
 *   ‘F f’
 *       The selected frame is number n in the trace frame buffer; f is a hexadecimal number. If f is ‘-1’, then there was no frame matching the criteria in the request packet.
 *   ‘T t’
 *       The selected trace frame records a hit of tracepoint number t; t is a hexadecimal number.
 * @param packet Containing the request
 * @return true if the response was sent without error
 */
static bool handle_qtframe_packet(char *packet)
{
	uae_u32 frame, pc, lo, hi, num;
	int tfnum, tpnum, tfnum_found;
	struct debugstackframe *tframe;
	uae_u8 message_buffer[50] = { 0 };
	uae_u8 *buffer = message_buffer;
	uae_u8 *t = message_buffer;
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
	tframe = find_traceframe(false, tfnum, &tfnum_found);
	if (tframe)
	{
		current_traceframe = tfnum;
		*buffer++ = 'F';
		if (tfnum_found <= 0)
		{
			*buffer++ = '-';
			*buffer++ = '1';
		}
		else 
		{
			buffer = write_u32 (buffer, tfnum_found);
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


/**
 * Reponse to the qfThreadInfo
 * Reply:
 *     ‘m thread-id’
 *   A single thread ID 
 *		‘m thread-id,thread-id…’
 *   a comma-separated list of thread IDs 
 *		‘l’
 * @param packet Containing the request
 * @return true if the response was sent without error
 */
static bool handle_qfthreadinfo_packet(char *packet)
{
	if (vrun_called) {
		uae_u8 message_buffer[1024] = { 0 };
		uae_u8 *buffer = message_buffer;
		uae_u8 *t = message_buffer;

		// TODO: activate with DMACON options
		buffer = write_char(buffer, '$');
		buffer = write_char(buffer, 'm');
		buffer = write_thread_id(buffer, PROCESS_ID_SYSTEM, THREAD_ID_CPU);
		buffer = write_char(buffer, ',');
		buffer = write_thread_id(buffer, PROCESS_ID_SYSTEM, THREAD_ID_COP);

		return send_packet_in_place(t, (int)((uintptr_t)buffer - (uintptr_t)t) - 1);
	} else {
		return send_packet_string("l");
	}
}


/**
 * Handles the qSupported query
 * ‘qSupported [:gdbfeature [;gdbfeature]… ]’
 *	Response
 *   ‘stubfeature [;stubfeature]…’
 * ‘stubfeature format used :
 *		‘name=value’
 *			The remote protocol feature name is supported, and associated with the specified value. The format of value depends on the feature, but it must not include a semicolon. 
 *		‘name+’
 * 			The remote protocol feature name is supported, and does not need an associated value. 
 *   no response is equivalent to ‘name-’
 * @param packet Containing the request
 * @return true if the response was sent without error
 */
static bool handle_qsupported_packet(char *packet)
{
	char *token;
	uae_u8 message_buffer[1024] = { 0 };
	uae_u8 *buffer = message_buffer;
	uae_u8 *t = message_buffer;

	buffer = write_string(buffer, "$qSupported:");
	buffer = write_string(buffer, "PacketSize=");
	buffer = write_u32(buffer, PACKET_SIZE); // TODO: Add a real size .... not just 10kb
	buffer = write_char(buffer, ';');

	packet += strlen("qSupported");
	if (*packet == ':') {
		packet++;
	}
	// skip white spaces
	while (*packet == ' ') {
		packet++;
	}
	/* get the first token */
	token = strtok(packet, ";");
	/* walk through other tokens */
	while (token != NULL) {
		if (!strcmp ("multiprocess+", token)) {
			support_multiprocess = true;
		}
		token = strtok(NULL, ";");
	}
	buffer = write_string(buffer, "QStartNoAckMode+;multiprocess+;vContSupported+;QThreadEvents+;QNonStop+;swbreak+;hwbreak+;QTFrame+");
    return send_packet_in_place(t, (int)((uintptr_t)buffer - (uintptr_t)t) - 1);
}

/**
 * Handles the qC packet
 *‘qC’
 *   Return the current thread ID.
 *   Reply:
 *   ‘QC thread-id’
 *       Where thread-id is a thread ID as documented in thread-id syntax. 
 *   ‘(anything else)’
 *       Any other reply implies the old thread ID.
 * @return true if the response was sent without error
 */
static bool handle_qc_packet() {
	uae_u8 message_buffer[1024] = { 0 };
	uae_u8 *buffer = message_buffer;
	uae_u8 *t = message_buffer;
	buffer = write_char(buffer, '$');
	buffer = write_string(buffer, "QC");
	buffer = write_thread_id(buffer, PROCESS_ID_SYSTEM, THREAD_ID_CPU);
	return send_packet_in_place(t, (int)((uintptr_t)buffer - (uintptr_t)t) - 1);
}

/**
 * Handles the qAttached packet
 *‘qAttached:pid’
 *   Return an indication of whether the remote server attached to an existing process or created a new process. When the multiprocess protocol extensions are supported (see multiprocess extensions), pid is an integer in hexadecimal format identifying the target process. Otherwise, GDB will omit the pid field and the query packet will be simplified as ‘qAttached’.
 *   This query is used, for example, to know whether the remote process should be detached or killed when a GDB session is ended with the quit command.
 *   Reply:
 *   ‘1’
 *       The remote server attached to an existing process. 
 *   ‘0’
 *       The remote server created a new process. 
 *   ‘E NN’
 *       A badly formed request or an error was encountered. 
 * @return true if the response was sent without error
 */
static bool handle_qattached() {
	if (vrun_called) {
		// process attached
		return send_packet_string("1");
	} else {
		// new process created
		return send_packet_string("0");
	}
}

/**
 * Handles the qOffsets packet
 *‘qOffsets’
 *   Get section offsets that the target used when relocating the downloaded image.
 *   Reply:
 *   ‘Text=xxx;Data=yyy[;Bss=zzz]’
 *       Relocate the Text section by xxx from its original address. Relocate the Data section by yyy from its original address. If the object file format provides segment information (e.g. ELF ‘PT_LOAD’ program headers), GDB will relocate entire segments by the supplied offsets.
 *       Note: while a Bss offset may be included in the response, GDB ignores this and instead applies the Data offset to the Bss section.
 *   ‘TextSeg=xxx[;DataSeg=yyy]’
 *       Relocate the first segment of the object file, which conventionally contains program code, to a starting address of xxx. If ‘DataSeg’ is specified, relocate the second segment, which conventionally contains modifiable data, to a starting address of yyy. GDB will report an error if the object file does not contain segment information, or does not contain at least as many segments as mentioned in the reply. Extra segments are kept at fixed offsets relative to the last relocated segment. 
 * @return true if the response was sent without error
 */
static bool handle_qoffsets_packet() {
	if (vrun_called) {
		uae_u8 message_buffer[1024] = { 0 };
		uae_u8 *buffer = message_buffer;
		uae_u8 *t = message_buffer;
		buffer = write_string(buffer, "$TextSeg=");
		buffer = write_u32(buffer, s_segment_info[0].address);
		if (s_segment_count > 1) {
			buffer = write_string(buffer, ";DataSeg=");
			buffer = write_u32(buffer, s_segment_info[1].address);
		}
		return send_packet_in_place(t, (int)((uintptr_t)buffer - (uintptr_t)t) - 1);
	} else {
		return send_packet_string("");
	}
}

/**
 * Handles the qTStatus packet
 * Partial implementation : Not real tracepoint implentation
 *‘qTStatus’
 *   Ask the stub if there is a trace experiment running right now.
 *   The reply has the form:
 *   ‘Trunning[;field]…’
 *       running is a single digit 1 if the trace is presently running, or 0 if not. It is followed by semicolon-separated optional fields that an agent may use to report additional status.
 *   If the trace is not running, the agent may report any of several explanations as one of the optional fields:
 *   ‘tnotrun:0’
 *       No trace has been run yet.
 * @return true if the response was sent without error
 */
static bool handle_qtstatus_packet() {
	return send_packet_string("T1");
}

/**
 * Handles the qTfV packet
 * Partial implementation : Not real tracepoint implentation
 *‘qTfV’
 *‘qTsV’
 *   These packets request data about trace state variables that are on the target. GDB sends qTfV to get the first vari of data, and multiple qTsV to get additional variables. Replies to these packets follow the syntax of the QTDV packets that define trace state variables.
 * @return true if the response was sent without error
 */
static bool handle_qtfv() {
	return send_packet_string("");
}

/**
 * Handles a query packet
 * 
 * @param packet Containing the request
 * @param length Length of the packet
 * @return true if the response was sent without error
 */
static bool handle_query_packet(char* packet, int length)
{
	int i = 0;

	// ‘v’ Packets starting with ‘v’ are identified by a multi-letter name, up to the first ‘;’ or ‘?’ (or the end of the packet).

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] [query] %s\n", packet);
		fs_log("[REMOTE_DEBUGGER] handle_query_packet %d\n", __LINE__);
	}

	if (!strncmp (packet, "QStartNoAckMode", 15)) {
		need_ack = false;
		return reply_ok ();
	}
	else if (!strncmp (packet, "qSupported", 10)) {
		return handle_qsupported_packet(packet);
	}
	else if (!strncmp (packet, "QNonStop", 8)) {
		return reply_ok ();
	}
	else if (!strncmp (packet, "QTFrame", 7)) {
		return handle_qtframe_packet(packet);
	}
	else if (!strncmp (packet, "qOffsets", 8)) {
		return handle_qoffsets_packet();
	}
	else if (!strncmp (packet, "qTStatus", 8)) {
		return handle_qtstatus_packet();
	}
	else if (!strncmp (packet, "qfThreadInfo", 12)) {
		return handle_qfthreadinfo_packet(packet);
	}
	else if (!strncmp (packet, "qsThreadInfo", 12)) {
		// end of threads
		return send_packet_string("l");
	}
	else if (!strncmp (packet, "qC", 9)) {
		// asks for current thread ID
		return handle_qc_packet();
	}
	else if (!strncmp (packet, "qAttached", 9)) {
		return handle_qattached();
	}
	else if (!strncmp (packet, "qTfV", 9)) {
		return handle_qtfv();
	}	
	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] handle_query_packet %d\n", __LINE__);
	}
	//send_packet_string (ERROR_PACKET_NOT_SUPPORTED);
	// Not supported
	return send_packet_string("");
}

/**
 * Handles a Thread request packet
 *‘H op thread-id’
 *   Set thread for subsequent operations (‘m’, ‘M’, ‘g’, ‘G’, et.al.). Depending on the operation to be performed, op should be ‘c’ for step and continue operations (note that this is deprecated, supporting the ‘vCont’ command is a better option), and ‘g’ for other operations. The thread designator thread-id has the format and interpretation described in thread-id syntax.
 *   Reply:
 *   ‘OK’
 *       for success 
 *   ‘E NN’
 *       for an error 
 * @param packet Containing the request
 * @param length Length of the packet
 * @return true if the response was sent without error
 */
static bool handle_thread (char* packet, int length)
{
	if (length > 1) {
		char command = packet[0];
		int process_id = PROCESS_ID_SYSTEM;
		int thread_id = THREAD_ID_CPU;
		bool parse_error = false;
		packet++;
		if (support_multiprocess) {
			int scan_res = sscanf (packet, "p%x.%x", &process_id, &thread_id);
			parse_error =  (scan_res != 2);
		} else {
			int scan_res = sscanf (packet, "%x", &thread_id);
			parse_error =  (scan_res != 1);
		}
		if (parse_error)	{
			fs_log("[REMOTE_DEBUGGER] Error during thread command parse of thread id '%s'\n", packet);
			return send_packet_string (ERROR_THREAD_COMMAND_PARSE);
		}
		switch (command) {
			case 'g':
			selected_thread_id = thread_id;
			selected_process_id = process_id;
			return reply_ok();
			break;
			default:
			// not implemented
			return send_packet_string (ERROR_PACKET_NOT_SUPPORTED);
			break;
		}
	} else {
		fs_log("[REMOTE_DEBUGGER] Error during thread command parse '%s'\n", packet);
		return send_packet_string (ERROR_THREAD_COMMAND_PARSE);
	}
}

/**
 * Handles a vStopped or ? request
 * ‘?’
 *   Indicate the reason the target halted. The reply is the same as for step and continue. This packet has a special interpretation when the target is in non-stop mode; see Remote Non-Stop.
 *   Reply: See Stop Reply Packets, for the reply specifications.
 * 	See send_exception function for response details
 * @return true if the response was sent without error
 */
static bool handle_vstopped ()
{
	if (vrun_called) {
		bool exception_sent = false;
		if (current_vstopped_idx == 0) {
			exception_sent = send_exception (PROCESS_ID_SYSTEM, THREAD_ID_CPU, true, true, false);
			current_vstopped_idx++;
		} else if (current_vstopped_idx == 1) {
			exception_sent = send_exception (PROCESS_ID_SYSTEM, THREAD_ID_COP, true, true, false);
			current_vstopped_idx++;
		} else {
			reply_ok();
			current_vstopped_idx = 0;
			exception_sent= true;
		}
		return exception_sent;
	} else {
		return send_packet_string("W00");
	}
}

/**
 * Handles ? request
 * ‘?’
 *   Indicate the reason the target halted. The reply is the same as for step and continue. This packet has a special interpretation when the target is in non-stop mode; see Remote Non-Stop.
 *   Reply: See Stop Reply Packets, for the reply specifications.
 * 	See send_exception function for response details
 * @return true if the response was sent without error
 */
static bool handle_qmark ()
{
	// Abandonning vStopped reports
	current_vstopped_idx = 0;
	// Send first exception
	return handle_vstopped ();
}

/**
 * Handles extended mode request
 * ‘!’
 *   Enable extended mode. In extended mode, the remote server is made persistent. The ‘R’ packet is used to restart the program being debugged.
 *   Reply:
 *   ‘OK’
 *       The remote target both supports and has enabled extended mode. 
 * @return true if the response was sent without error
 */
static bool handle_extended_mode ()
{
	// Accepted
	return reply_ok();
}

/**
 * Kills the running program
 * @return true if it was killed
 */
static bool kill_program () {
	remote_deactivate_debugger ();
	uae_reset (0, 0);
    s_segment_count = 0;
	return true;
}

/**
 * Handles continue reques
 *‘c [addr]’
 *   Continue at addr, which is the address to resume. If addr is omitted, resume at current address.
 *   This packet is deprecated for multi-threading support. See vCont packet.
 *   Reply: See Stop Reply Packets, for the reply specifications.
 * @param process_id Process id
 * @param thread_id Thread id
 * @param packet Request packet
 * @return true if the response was sent without error
 */
static bool handle_continue_exec (int process_id, int thread_id, char* packet)
{
	// 'c [addr] Continue at addr, which is the address to resume. If addr is omitted, resume at current address.
	if ((packet != NULL) && (*packet != '#'))
	{
		uae_u32 address;
		if (sscanf (packet, "%x#", &address) != 1)
		{
			fs_log("[REMOTE_DEBUGGER] Unable to parse continnue packet %s\n", packet);
			return false;
		}
		m68k_setpci(address);
	}
	fs_log("[REMOTE_DEBUGGER] remote_debug: continue execution...\n");
	debug_copper = 1|4;
	remote_deactivate_debugger ();
	return reply_ok ();
}

/**
 * Checks if the address has a breakpoint attached
 * 
 * @param address Address tested
 * @return Index of the breakpoint or -1
 */
static int has_breakpoint_address(uaecptr address)
{
	for (int i = 0; i < s_breakpoint_count; ++i)
	{
		if (s_breakpoints[i].address == address)
			return i;
	}
	return -1;
}

/**
 * Resolves the address of a breakpoint.
 * Transforms from seg/offset to absolute momory address
 * 
 * @param breakpoint Breakpoint to process
 */
static void resolve_breakpoint_seg_offset (Breakpoint* breakpoint)
{
    uae_u32 seg_id = breakpoint->kind;
    uaecptr offset = breakpoint->offset;

    if (seg_id >= s_segment_count) {
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] Segment id >= segment_count (%d - %d)\n", seg_id, s_segment_count);
		}
		breakpoint->needs_resolve = true;
		return;
    } else  {
		breakpoint->seg_id = seg_id;
    	breakpoint->address = s_segment_info[seg_id].address + offset;
	}
    breakpoint->needs_resolve = false;
	if (log_remote_protocol_enabled) {
	    fs_log("[REMOTE_DEBUGGER] resolved breakpoint (%x - %x) -> 0x%08x\n", offset, seg_id, breakpoint->address);
	}
}

/**
 * Adds an offset/seg breakpoint
 * 
 * @param offset Offset in code segment
 * @param kind Kind of breakpoint
 */
static void set_offset_seg_breakpoint (uaecptr offset, uae_u32 kind)
{
	s_breakpoints[s_breakpoint_count].offset = offset;
	s_breakpoints[s_breakpoint_count].kind = kind;
    resolve_breakpoint_seg_offset (&s_breakpoints[s_breakpoint_count]);
	s_breakpoint_count++;
}

/**
 * Adds an absolute address breakpoint
 * 
 * @param address Absolute address
 */
static bool set_absolute_address_breakpoint (uaecptr address)
{
	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] Added absolute address breakpoint at 0x%08x \n", address);
	}
	s_breakpoints[s_breakpoint_count].address = address;
	s_breakpoints[s_breakpoint_count].kind = BREAKPOINT_KIND_ABSOLUTE_ADDR;
	s_breakpoints[s_breakpoint_count].needs_resolve = false;
	s_breakpoint_count++;
	return reply_ok ();
}

/**
 * Removes a breakpoint
 * 
 * @param offset offset or address
 * @param kind Kid of breakpoint
 * @return true if it was removed
 */
static bool remove_breakpoint (uaecptr offset, uae_u32 kind) 
{
	for (int i = 0; i < s_breakpoint_count; ++i) {
		if ((s_breakpoints[i].address == offset) ||
			(s_breakpoints[i].offset == offset && s_breakpoints[i].seg_id == kind)) {
			s_breakpoints[i] = s_breakpoints[s_breakpoint_count - 1];
			s_breakpoint_count--;
			return reply_ok ();
		}
	}
	return reply_ok ();
}


/**
 * Handles set breakpoint request for an address
 * see handle_set_breakpoint
 * @param packet Packet of the request
 * @param add If true it's a add, if not it's a remove request
 * @return true if the response was sent without error
 */
static bool handle_set_breakpoint_address (char* packet, bool add)
{
	uaecptr offset;
	uae_u32 kind = BREAKPOINT_KIND_ABSOLUTE_ADDR;

	if (s_breakpoint_count + 1 >= MAX_BREAKPOINT_COUNT)
	{
		fs_log("[REMOTE_DEBUGGER] Max number of breakpoints (%d) has been reached. Removed some to add new ones", MAX_BREAKPOINT_COUNT);
		send_packet_string (ERROR_MAX_BREAKPOINTS_REACHED);
		return false;
	}

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] parsing breakpoint\n");
	}
	
	// if we have two args it means that the data is of type offset,kind and we need to resolve that.
	// if we are in running state we try to resolve it directly otherwise we just add it to the list
	// and resolve it after we loaded the executable
	// THe kind can be a segment id or an absolute or copper address

	int scan_res = sscanf (packet, "%x,%x", &offset, &kind);

	if (scan_res < 1)
	{
		fs_log("[REMOTE_DEBUGGER] failed to parse memory packet: %s\n", packet);
		send_packet_string (ERROR_SET_BREAKPOINT_PARSE);
		return false;
	}
	if (!add) {
		remove_breakpoint(offset, kind);
	} else if (kind > BREAKPOINT_KIND_MAX) {
		fs_log("[REMOTE_DEBUGGER] Breakpoint kind invalid: %d\n", kind);
		send_packet_string (ERROR_UNKNOWN_BREAKPOINT_KIND);
		return false;
	} else if (kind <= BREAKPOINT_KIND_SEG_ID_MAX) {
		set_offset_seg_breakpoint (offset, kind);
		return reply_ok ();
    } else {
		return set_absolute_address_breakpoint (offset);
    }
}

/**
 * Handles set breakpoint request for an exception
 * The message is z1,0,0;Xf,nnnnnnnnnnnnnnnn
 *  address is 0 : not used
 *  One parameter with 16 chars is the 64bit mask for exception filtering
 * @param packet Packet of the request
 * @param add If true it's a add, if not it's a remove request
 * @return true if the response was sent without error
 */
static bool handle_set_exception_breakpoint (char* packet, bool add) {
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
			send_packet_string (ERROR_MAX_BREAKPOINTS_REACHED);
			return false;
		}
	}
}

/**
 * Handles set breakpoint request
 *‘z type,addr,kind’
 *‘Z type,addr,kind’
 *   Insert (‘Z’) or remove (‘z’) a type breakpoint or watchpoint starting at address address of kind kind.
 *   Each breakpoint and watchpoint packet type is documented separately.
 *   Implementation notes: A remote target shall return an empty string for an unrecognized breakpoint or watchpoint packet type. A remote target shall support either both or neither of a given ‘Ztype…’ and ‘ztype…’ packet pair. To avoid potential problems with duplicate packets, the operations should be implemented in an idempotent way.
 *‘z0,addr,kind’
 *‘Z0,addr,kind[;cond_list…][;cmds:persist,cmd_list…]’
 *   Insert (‘Z0’) or remove (‘z0’) a software breakpoint at address addr of type kind.
 *   A software breakpoint is implemented by replacing the instruction at addr with a software breakpoint or trap instruction. The kind is target-specific and typically indicates the size of the breakpoint in bytes that should be inserted. E.g., the ARM and MIPS can insert either a 2 or 4 byte breakpoint. Some architectures have additional meanings for kind (see Architecture-Specific Protocol Details); if no architecture-specific value is being used, it should be ‘0’. kind is hex-encoded. cond_list is an optional list of conditional expressions in bytecode form that should be evaluated on the target’s side. These are the conditions that should be taken into consideration when deciding if the breakpoint trigger should be reported back to GDB.
 *   See also the ‘swbreak’ stop reason (see swbreak stop reason) for how to best report a software breakpoint event to GDB.
 *   The cond_list parameter is comprised of a series of expressions, concatenated without separators. Each expression has the following form:
 *   ‘X len,expr’
 *       len is the length of the bytecode expression and expr is the actual conditional expression in bytecode form.
 *   The optional cmd_list parameter introduces commands that may be run on the target, rather than being reported back to GDB. The parameter starts with a numeric flag persist; if the flag is nonzero, then the breakpoint may remain active and the commands continue to be run even when GDB disconnects from the target. Following this flag is a series of expressions concatenated with no separators. Each expression has the following form:
 *   ‘X len,expr’
 *       len is the length of the bytecode expression and expr is the actual commands expression in bytecode form.
 *   Implementation note: It is possible for a target to copy or move code that contains software breakpoints (e.g., when implementing overlays). The behavior of this packet, in the presence of such a target, is not defined.
 *   Reply:
 *   ‘OK’
 *       success 
 *   ‘’
 *       not supported 
 *   ‘E NN’
 *       for an error 
 * @param packet Packet of the request
 * @param add If true it's a add, if not it's a remove request
 * @return true if the response was sent without error
 */
static bool handle_set_breakpoint (char* packet, bool add)
{
	switch (*packet)
	{
		case '0' :
		{
			// software breakpoint
			// skip zero and  ,
			return handle_set_breakpoint_address(packet + 2, add);
		}
		case '1' :
		{
			// Hardware breakpoint : used for exception breakpoint
			// skip 1 and  ,
			return handle_set_exception_breakpoint(packet + 2, add);
		}
		default:
		{
			fs_log("[REMOTE_DEBUGGER] unknown breakpoint type\n");
			send_packet_string (ERROR_UNKNOWN_BREAKPOINT_TYPE);
			return false;
		}
	}
}

/**
 * Pause process execution
 * 
 * @param process_id Process id
 * @param thread_id Thread id
 * @return true if it was done
 */
static bool pause_exec(int process_id, int thread_id) {
	if (thread_id == THREAD_ID_CPU) {
		set_special (SPCFLAG_BRK);
	} else if (thread_id == THREAD_ID_COP) {
		// Stop the copper
		debug_copper = 1|2;
	}
	send_exception (process_id, thread_id, true, true, false);
	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] pause demanded -> switching to tracing\n");
	}
	s_state = Tracing;
	return true;
}


/**
 * Handles vCont request
 *‘vCont[;action[:thread-id]]…’
 *   Resume the inferior, specifying different actions for each thread.
 *   For each inferior thread, the leftmost action with a matching thread-id is applied. Threads that don’t match any action remain in their current state. Thread IDs are specified using the syntax described in thread-id syntax. If multiprocess extensions (see multiprocess extensions) are supported, actions can be specified to match all threads in a process by using the ‘ppid.-1’ form of the thread-id. An action with no thread-id matches all threads. Specifying no actions is an error.
 *   Currently supported actions are:
 *   ‘c’
 *       Continue. 
 *   ‘C sig’
 *       Continue with signal sig. The signal sig should be two hex digits. 
 *   ‘s’
 *       Step. 
 *   ‘S sig’
 *       Step with signal sig. The signal sig should be two hex digits. 
 *   ‘t’
 *       Stop. 
 *   ‘r start,end’
 *       Step once, and then keep stepping as long as the thread stops at addresses between start (inclusive) and end (exclusive). The remote stub reports a stop reply when either the thread goes out of the range or is stopped due to an unrelated reason, such as hitting a breakpoint. See range stepping.
 *       If the range is empty (start == end), then the action becomes equivalent to the ‘s’ action. In other words, single-step once, and report the stop (even if the stepped instruction jumps to start).
 *       (A stop reply may be sent at any point even if the PC is still within the stepping range; for example, it is valid to implement this packet in a degenerate way as a single instruction step operation.)
 *   The optional argument addr normally associated with the ‘c’, ‘C’, ‘s’, and ‘S’ packets is not supported in ‘vCont’.
 *   The ‘t’ action is only relevant in non-stop mode (see Remote Non-Stop) and may be ignored by the stub otherwise. A stop reply should be generated for any affected thread not already stopped. When a thread is stopped by means of a ‘t’ action, the corresponding stop reply should indicate that the thread has stopped with signal ‘0’, regardless of whether the target uses some other signal as an implementation detail.
 *   The server must ignore ‘c’, ‘C’, ‘s’, ‘S’, and ‘r’ actions for threads that are already running. Conversely, the server must ignore ‘t’ actions for threads that are already stopped.
 *   Note: In non-stop mode, a thread is considered running until GDB acknowleges an asynchronous stop notification for it with the ‘vStopped’ packet (see Remote Non-Stop).
 *   The stub must support ‘vCont’ if it reports support for multiprocess extensions (see multiprocess extensions).
 *   Reply: See Stop Reply Packets, for the reply specifications.
 * @param packet Recieved packet
 * @return true if the response was sent without error
 */
static bool handle_vcont (char* packet)
{
	char *token;
	/* get the first command */
	token = strtok(packet, ";");
	/* walk through other commands */
	while (token != NULL) {
		// has thread id ?
		char command_buffer[4] = {0};
		char command = token[0];
		int process_id = PROCESS_ID_SYSTEM;
		int thread_id = THREAD_ID_CPU;
		int start_address = -2;
		int end_address = -2;
		bool has_thread_id = false;
		bool parse_error = false;
		for (int i = 0; i< strlen(token); i++) {
			if (token[i] == ':') {
				has_thread_id = true;
				break;
			}
		}
		if (has_thread_id) {
			if (command == 'r') {
				// extract thread id
				if (support_multiprocess) {
					int scan_res = sscanf (token, "r%x,%x:p%x.%x", &start_address, &end_address, &process_id, &thread_id);
					parse_error =  (scan_res != 4);
				} else {
					int scan_res = sscanf (token, "r%x,%x:%x", &start_address, &end_address, &thread_id);
					parse_error =  (scan_res != 3);
				}
			} else {
				// extract thread id
				if (support_multiprocess) {
					int scan_res = sscanf (token, "%3[^:]:p%x.%x", command_buffer, &process_id, &thread_id);
					parse_error =  (scan_res != 3);
				} else {
					int scan_res = sscanf (token, "%3[^:]:%x", command_buffer, &thread_id);
					parse_error =  (scan_res != 2);
				}
			}
		} else if (command == 'r') {
			// extract thread id
			int scan_res = sscanf (token, "r%x,%x", &start_address, &end_address);
			parse_error =  (scan_res != 2);
		}
		if (parse_error)	{
			fs_log("[REMOTE_DEBUGGER] Error during vCont command parse '%s'\n", token);
			send_packet_string (ERROR_VCONT_PARSE);
			return false;
		}
		switch (command) {
			case 's':
			case 'S':
			// step
			return step(process_id, thread_id);
			break;
			case 't':
			// stop
			return pause_exec(process_id, thread_id);
			break;
			case 'c':
			case 'C':
			// continue
			return handle_continue_exec(process_id, thread_id, NULL);
			break;
			case 'r':
			// step range
			// TODO: use start_address and end_address
			return step_next_instruction(process_id, thread_id);
			break;
			default:
			// not implemented
			break;
		}
		token = strtok(NULL, ";");
	}
	fs_log("[REMOTE_DEBUGGER] Error during vCont command parse '%s'\n", token);
	send_packet_string (ERROR_VCONT_PARSE);
	return false;
}

/**
 * Handles vCont?
 *‘vCont?’
 *   Request a list of actions supported by the ‘vCont’ packet.
 *   Reply:
 *   ‘vCont[;action…]’
 *       The ‘vCont’ packet is supported. Each action is a supported command in the ‘vCont’ packet. 
 *   ‘’
 *       The ‘vCont’ packet is not supported. 
 * @return true if the response was sent without error
 */
static bool handle_vcont_query ()
{
	return send_packet_string ("vCont;c;C;s;S;t;r");
}

/**
 * Handles thread break
 * ‘vCtrlC’
 *   Interrupt remote target as if a control-C was pressed on the remote terminal. This is the equivalent to reacting to the ^C (‘\003’, the control-C character) character in all-stop mode while the target is running, except this works in non-stop mode. See interrupting remote targets, for more info on the all-stop variant.
 *   Reply:
 *   ‘E nn’
 *       for an error 
 *   ‘OK’
 *       for success 
 * @return true if the response was sent without error
 */
static bool handle_vctrlc()
{
	return pause_exec(PROCESS_ID_SYSTEM, THREAD_ID_CPU);
}

/**
 * Handles thread break
 *‘D’
 *‘D;pid’
 *   The first form of the packet is used to detach GDB from the remote system. It is sent to the remote target before GDB disconnects via the detach command.
 *   The second form, including a process ID, is used when multiprocess protocol extensions are enabled (see multiprocess extensions), to detach only a specific process. The pid is specified as a big-endian hex string.
 *   Reply:
 *   ‘OK’
 *       for success 
 *   ‘E NN’
 *       for an error 
 * @return true if the response was sent without error
 */
static bool handle_detach()
{
	// Stop debugging
	return handle_continue_exec(PROCESS_ID_SYSTEM, THREAD_ID_CPU, NULL);
}

/**
 * Removes the checksum from a request packet
 * Adds a '\0' at the end
 * @param packet Packet to process
 * @param length Length of the packet
 * @return Resulting length
 */
static int remove_checksum(char* packet, int length) {
	for (int i = length; i > 0; --i) {
		const char c = packet[i];
		if (c == '#') {
			packet[i] = 0;
			return i;
		}
	}	
	return length;
}


/**
 * Handles a multi-letter packet
 * 
 * @param packet Packet to process
 * @param length Length of the packet
 * @return true if the response was sent without error
 */
static bool handle_multi_letter_packet (char* packet, int length)
{
	int i = 0;
	// ‘v’ Packets starting with ‘v’ are identified by a multi-letter name, up to the first ‘;’ or ‘?’ (or the end of the packet).
	remove_checksum (packet, length);
	// multi letters packet ends with '?' or ';' 
	if (!strncmp(packet, "vCont;", 6)) {
		return handle_vcont (packet + 6);
	} else if (!strncmp(packet, "vCtrlC", 6)) {
		return handle_vctrlc();
	} else if (!strncmp(packet, "vRun", 4)) {
		return handle_vrun (packet + 5);
	} else if (!strncmp(packet, "vStopped", 8)) {
		return handle_vstopped ();
	} else if (!strncmp(packet, "vCont?", 6)) {
		return handle_vcont_query();
	} else if (!strncmp(packet, "vMustReplyEmpty", 15)) {
		return send_packet_string("");
	} else if (!strncmp(packet, "vKill", 5)) {
		// TODO: really kill the program
		//kill_program ();
		return reply_ok();
	} else {
		fs_log("[REMOTE_DEBUGGER] Multi letter packet not supported '%s'\n", packet);
		send_packet_string (ERROR_PACKET_NOT_SUPPORTED);
	}

	return false;
}

/**
 * Handles a request packet
 * 
 * @param packet Packet to process
 * @param initial_length initial length of the packet
 * @return true if the response was sent without error
 */
static bool handle_packet(char* packet, int initial_length)
{
	const char command = *packet;

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] handle packet %s\n", packet);
	}

	int length = remove_checksum(packet, initial_length);

	// ‘v’ Packets starting with ‘v’ are identified by a multi-letter name, up to the first ‘;’ or ‘?’ (or the end of the packet).

	if (command == 'v')
		return handle_multi_letter_packet(packet, length);

	if (command == 'q' || command == 'Q')
		return handle_query_packet(packet, length);

	switch (command)
	{
		case 'g' : return send_registers ();
		case 's' : return step (PROCESS_ID_SYSTEM, THREAD_ID_CPU);
		case 'n' : return step_next_instruction (PROCESS_ID_SYSTEM, THREAD_ID_CPU);
		case 'H' : return handle_thread (packet + 1, length - 1);
		case 'G' : return handle_set_registers ((const uae_u8*)packet + 1);
		case '?' : return handle_qmark ();
		case '!' : return handle_extended_mode ();
		case 'k' : return kill_program ();
		case 'm' : return handle_read_memory (packet + 1);
		case 'M' : return handle_set_memory (packet + 1, length - 1);
		case 'p' : return handle_get_register (packet + 1, length - 1);
		case 'P' : return handle_set_register (packet + 1, length - 1);
		case 'c' : return handle_continue_exec (PROCESS_ID_SYSTEM, THREAD_ID_CPU, packet + 1);
		case 'D' : return handle_detach();
		case 'Z' : return handle_set_breakpoint (packet + 1, true);
		case 'z' : return handle_set_breakpoint (packet + 1, false);

		default : send_packet_string (ERROR_PACKET_NOT_SUPPORTED);
	}

	return false;
}

/**
 * Parses a request packet
 * 
 * @param packet Packet to process
 * @param size Length of the packet
 * @return true if the response was sent without error
 */
static bool parse_packet(char* packet, int size)
{
	uae_u8 calc_checksum = 0;
	uae_u8 read_checksum = 0;
	int start, end;

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] parsing packet %s\n", packet);
	}

	if (*packet == 3 && size == 1)
	{
		// interrupt signal
		return handle_vctrlc();
	}
	/*
	if (*packet == '-' && size == 1)
	{
		fs_log("[REMOTE_DEBUGGER] *** Resending\n");
		rconn_send (s_conn, s_last_sent, s_last_size, 0);
		return true;
	}
	*/

	// TODO: Do we need to handle data that strides several packets?

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


/**
 * Updates a connection status
 * 
 */
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
			send_exception(exception_send_pending_pid, exception_send_pending_tid, true, false, true);
			exception_send_pending = false;
		}
	}
}


/**
 * Main function that will be called when doing the actual debugging
 * 
 */
static void remote_debug_ (void)
{
	bool step_exception_sent = false;
	uaecptr pc = m68k_getpc ();

	// As an exception stored
	if (!last_exception_sent && (last_exception > 0)) {
		send_exception (PROCESS_ID_SYSTEM, THREAD_ID_CPU, true, false, true);
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
				send_exception (PROCESS_ID_SYSTEM, THREAD_ID_CPU, true, false, false);
				s_state = Tracing;
				s_skip_to_pc = 0xffffffff;
				step_exception_sent = true;
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
				//remote_activate_debugger ();
				send_exception (PROCESS_ID_SYSTEM, THREAD_ID_CPU, true, false, true);
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
				if (!step_exception_sent) {
					send_exception (PROCESS_ID_SYSTEM, THREAD_ID_CPU, true, false, false);
				}
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

/** 
 * Main function that will be called when doing the copper debugging
 */
static void remote_debug_copper_ (uaecptr addr, uae_u16 word1, uae_u16 word2, int hpos, int vpos)
{
	// scan breakpoints for the current address
	if (!(debug_copper & 8)) {
		for (int i = 0; i < s_breakpoint_count; ++i)
		{
			Breakpoint bp = s_breakpoints[i];
			uaecptr real_addr = get_copper_address(-1);
			if (!bp.needs_resolve && real_addr >= bp.address && real_addr <= bp.address + 3) {
				debug_copper = 1|8;
				remote_activate_debugger ();
				send_exception (PROCESS_ID_SYSTEM, THREAD_ID_COP, true, true, true);
				if (log_remote_protocol_enabled) {
					fs_log("[REMOTE_DEBUGGER] Copper breakpoint reached\n");
				}
				debug_copper = 1;
				s_state = Tracing;
				break;
			}
		}
	}
	if (debug_copper & 2) {
		debug_copper = 1;
		remote_activate_debugger ();
		send_exception (PROCESS_ID_SYSTEM, THREAD_ID_COP, true, true, false);
		if (log_remote_protocol_enabled) {
			fs_log("[REMOTE_DEBUGGER] Copper step reached\n");
		}
		s_state = Tracing;
	}
}

/**
 * This function needs to be called at regular interval to keep the socket connection alive
 */
static void remote_debug_update_ (void)
{
	if (!s_conn)
		return;

	rconn_update_listner (s_conn);

	remote_debug_ ();
    remote_activate_debugger ();
	//exception_debugging = 0;

	if (rconn_poll_read(s_conn)) {
		remote_activate_debugger ();
		//exception_debugging = 0;
	}
	if (vrun_called && !debugger_boot_done) {
		debugger_boot_done = debugger_boot();
	}
}

extern uaecptr get_base (const uae_char *name, int offset);

/**
 * Called from debugger_helper. At this point CreateProcess has been called
 * and we are resposible for filling out the data needed by the "RunCommand"
 * that looks like this:
 *
 *    rc = RunCommand(seglist, stacksize, argptr, argsize)
 *    D0		D1	   D2	    D3	    D4
 *
 *    LONG RunCommand(BPTR, ULONG, STRPTR, ULONG)
 *
 * For Kickstart under 2.0 - we use CreateProc
 *    process = CreateProc( name, pri, seglist, stackSize )
 *    D0                    D1    D2   D3       D4
 *
 *   struct MsgPort *CreateProc(STRPTR, LONG, BPTR, LONG)
 * @param context Context of trap execution
 */
void remote_debug_start_executable (struct TrapContext *context)
{
	bool use_create_proc = kickstart_version && kickstart_version < 36;
#ifdef FSUAE
	uaecptr filename = ds (s_exe_to_run);
	uaecptr args = ds ("");
	uaecptr procname = ds ("debug");
#else
	uaecptr filename = ds (_T(s_exe_to_run));
	uaecptr args = ds (_T(""));
	uaecptr procname = ds (_T("debug"));
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
		send_packet_string(ERROR_UNABLE_LOAD_SEGMENTS);
		return;
	}

	if (log_remote_protocol_enabled) {
		fs_log("[REMOTE_DEBUGGER] About to send segments\n");
	}

	s_segment_count = 0;

	uae_u32 ptr = seglist_addr;
	while(ptr != 0) {
		unsigned char addr_str_temp[9] = { 0 };
		unsigned char size_str_temp[9] = { 0 };

		uae_u32 size = get_long(ptr - 4) - 8; // size of BPTR + segment
		uae_u32 addr = ptr + 4;

		s_segment_info[s_segment_count].address = addr;
		s_segment_info[s_segment_count].size = size;

		write_u32(addr_str_temp, addr);
		write_u32(size_str_temp, size);

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

	context_set_areg(context, 6, dosbase);
	if (use_create_proc) {
		context_set_dreg(context, 1, procname); // proc name
		context_set_dreg(context, 2, 128); // priority
		context_set_dreg(context, 3, segs);
		context_set_dreg(context, 4, 4096); // stack size
	} else {	
		context_set_dreg(context, 1, segs);
		context_set_dreg(context, 2, 4096);
		context_set_dreg(context, 3, args);
		context_set_dreg(context, 4, 0);
	}

	update_debug_illegal();
	remote_deactivate_debugger ();

	fs_log("[REMOTE_DEBUGGER] remote_debug_start_executable\n");
}

/**
 * Send notification of program end
 * 
 * @param context Context of trap execution
 */
void remote_debug_end_executable (struct TrapContext *context)
{
	fs_log("[REMOTE_DEBUGGER] remote_debug_end_executable\n");
	send_packet_string("W00");
}

//
// These are just wrappers to expose the code to C from C++
//

extern "C"
{
	void remote_debug_init(int port, int time_out) { return remote_debug_init_(port, time_out); }
	void remote_debug(void) { remote_debug_(); }
	void remote_debug_copper(uaecptr addr, uae_u16 word1, uae_u16 word2, int hpos, int vpos) { remote_debug_copper_(addr, word1, word2, hpos, vpos); }
	void remote_debug_update(void) { remote_debug_update_(); }
	void remote_debug_check_exception(void) { remote_debug_check_exception_(); }
}

#endif


