#ifndef SYMBOLIC_INSTRUMENTATION_H
#define SYMBOLIC_INSTRUMENTATION_H

#define SYMBOLIC_INSTRUMENTATION
#define SYMBOLIC_CALLSTACK_INSTRUMENTATION 0

extern int  symbolic_force_flush_cache;
extern void qemu_syscall_helper(uintptr_t syscall_no, uintptr_t syscall_arg0,
                                uintptr_t syscall_arg1, uintptr_t syscall_arg2,
                                uintptr_t ret_val);

#include "syscall_nr.h"

#endif // SYMBOLIC_INSTRUMENTATION_H