#ifndef UAE_DEBUGMEM_H
#define UAE_DEBUGMEM_H

#include "traps.h"
#include "uae/types.h"

uaecptr debugmem_reloc(uaecptr exeaddress, uae_u32 len, uaecptr task, uae_u32 *stack);
void debugmem_init(bool);
uaecptr debugmem_allocmem(int mode, uae_u32 size, uae_u32 flags, uae_u32 caller);
uae_u32 debugmem_freemem(int mode, uaecptr addr, uae_u32 size, uae_u32 caller);
void debugmem_trap(uaecptr addr);
void debugmem_addsegs(TrapContext *ctx, uaecptr seg, uaecptr name, uae_u32 lock, bool residentonly);
void debugmem_remsegs(uaecptr seg);
uae_u32 debugmem_exit(void);
bool debugmem_break(int);
bool debugmem_inhibit_break(int mode);
void debugmem_disable(void);
void debugmem_enable(void);
int debugmem_get_segment(uaecptr addr, bool *exact, bool *ext, TCHAR *out, TCHAR *name);
int debugmem_get_symbol(uaecptr addr, TCHAR *out, int maxsize);
bool debugmem_get_symbol_value(const TCHAR *name, uae_u32 *valp);
bool debugmem_list_segment(int mode, uaecptr addr);
int debugmem_get_sourceline(uaecptr addr, TCHAR *out, int maxsize);
bool debugmem_get_range(uaecptr*, uaecptr*);
bool debugmem_isactive(void);
bool debugger_load_libraries(void);
void debugger_scan_libraries(void);
bool debugger_get_library_symbol(uaecptr base, uaecptr addr, TCHAR *out);
bool debugmem_break_stack_pop(void);
bool debugmem_break_stack_push(void);
bool debugmem_illg(uae_u16);

// Stack frame functions
typedef struct debugstackframe
{
	uaecptr current_pc;
	uaecptr branch_pc;
	uaecptr next_pc;
	uaecptr stack;
	uae_u32 regs[16];
	uae_u16 sr;
};
extern bool debugmem_list_stackframe(bool super);
extern bool debugmem_enable_stackframe(bool enable);
extern void branch_stack_push(uaecptr oldpc, uaecptr newpc);
extern void branch_stack_pop_rts(uaecptr oldpc);
extern void branch_stack_pop_rte(uaecptr);
extern struct debugstackframe *find_traceframe(bool super, int num, int *tfnump);

extern uae_u32 debugmem_chiplimit;
extern uae_u32 debugmem_chiphit(uaecptr addr, uae_u32 v, int size);
extern bool debugmem_extinvalidmem(uaecptr addr, uae_u32 v, int size);
#endif /* UAE_DEBUGMEM_H */