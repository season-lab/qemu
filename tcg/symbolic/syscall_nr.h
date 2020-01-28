
#ifndef SYMBOLIC_SYSCALL_NR_H
#define SYMBOLIC_SYSCALL_NR_H

typedef enum SyscallNo {
    SYS_OPEN,
    SYS_OPENAT,
    SYS_READ,
    SYS_CLOSE,
    SYS_NOT_INTERESTING
} SyscallNo;

#endif // SYMBOLIC_SYSCALL_NR_H