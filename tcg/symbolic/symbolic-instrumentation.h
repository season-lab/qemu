#ifndef SYMBOLIC_INSTRUMENTATION_H
#define SYMBOLIC_INSTRUMENTATION_H

#define SYMBOLIC_INSTRUMENTATION
#define SYMBOLIC_CALLSTACK_INSTRUMENTATION 0

extern uint64_t  symbolic_start_code;
extern uint64_t  symbolic_end_code;
extern int       symbolic_force_flush_cache;
extern void qemu_syscall_helper(uintptr_t syscall_no, uintptr_t syscall_arg0,
                                uintptr_t syscall_arg1, uintptr_t syscall_arg2,
                                uintptr_t syscall_arg3, uintptr_t syscall_arg4,
                                uintptr_t syscall_arg5, uintptr_t syscall_arg6,
                                uintptr_t ret_val);
void symbolic_clear_mem(uintptr_t addr, uintptr_t size);

#include "syscall_nr.h"

#endif // SYMBOLIC_INSTRUMENTATION_H