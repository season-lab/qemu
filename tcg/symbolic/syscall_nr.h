
#ifndef SYMBOLIC_SYSCALL_NR_H
#define SYMBOLIC_SYSCALL_NR_H

typedef enum SyscallNo {
    SYS_OPEN,
    SYS_OPENAT,
    SYS_READ,
    SYS_CLOSE,
    SYS_SEEK,
    SYS_EXIT,
    SYS_DUP,
    SYS_MMAP,
    SYS_MMAP2,
    SYS_MUNMAP,
    SYS_NOT_INTERESTING
} SyscallNo;

#define MAX_N_SYSCALL_ARGS 6

typedef struct {
    int nr;
    uintptr_t arg[MAX_N_SYSCALL_ARGS];
    uintptr_t ret;
    void* aux;
} SyscallContext;

typedef struct {
	size_t	nargs;
	size_t	save_args;
    size_t  retval_args;
	size_t	map_args[MAX_N_SYSCALL_ARGS];
	void	(* pre)(SyscallContext*);
	void	(* post)(SyscallContext*);
} SyscallDesc;

#endif // SYMBOLIC_SYSCALL_NR_H