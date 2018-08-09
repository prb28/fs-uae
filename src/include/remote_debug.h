 /*
  * UAE - The Un*x Amiga Emulator
  *
  * Debugger
  *
  * (c) 1995 Bernd Schmidt
  *
  * Remote debugger code (c) 2015 Daniel Collin.
  */

#ifndef UAE_REMOTE_DEBUG_H
#define UAE_REMOTE_DEBUG_H

#define REMOTE_DEBUGGER

#ifdef REMOTE_DEBUGGER

#ifdef __cplusplus
extern "C" {
#endif

//
// Set to 1 if remote debugging is enabled otherwise 0
//

extern int remote_debugging;

struct TrapContext;

//
// port allows to modify the server socket port
// time_out allows to set the time UAE will wait at startup for a connection.
// This is useful when wanting to debug things at early startup.
// If this is zero no time-out is set and if -1 no remote connection will be setup
//

void remote_debug_init (int port, int time_out);

// Main function that will be called when doing the actual debugging

void remote_debug (void);

// This function needs to be called at regular interval to keep the socket connection alive

void remote_debug_update (void);

void remote_debug_start_executable (struct TrapContext* ctx);
void remote_debug_end_executable (struct TrapContext* ctx);
void remote_debug_check_exception();

#ifdef __cplusplus
}
#endif

// Default server socket port
#define REMOTE_DEBUGGER_DEFAULT_PORT 6860

// Error codes for the remote protocol
#define ERROR_SEND_MEMORY_PARSE               "E0f" // Error during the packet parse for command send memory
#define ERROR_SET_MEMORY_PARSE                "E10" // Error during the packet parse for command set memory
#define ERROR_SET_MEMORY_PARSE_MISSING_END    "E11" // Missing end packet for a set memory message
#define ERROR_SET_MEMORY_INVALID_ADDRESS      "E12" // Address not safe for a set memory command
#define ERROR_SET_REGISTER_PARSE              "E13" // Error during the packet parse for command set register
#define ERROR_SET_REGISTER_PARSE_NAME_INVALID "E14" // Invalid register name for command set register

#endif // REMOTE_DEBUGGER

#endif // UATE_REMOTE_DEBUG

