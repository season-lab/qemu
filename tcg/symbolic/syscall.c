#include "../tcg/symbolic/symbolic-instrumentation.h"

#define MAX_SYSCALL_NR TARGET_NR_seccomp

static SyscallDesc kSyscallDesc[MAX_SYSCALL_NR];
static int symbolic_syscall_init = 0;

#include <ustat.h>
#include <linux/unistd.h>
#include <asm/ldt.h>
#include <linux/aio_abi.h>
#include <linux/perf_event.h>
#include <linux/hw_breakpoint.h>

struct getcpu_cache {
	unsigned long blob[128 / sizeof(long)];
};

static void init_syscall_handler(void)
{
  kSyscallDesc[TARGET_NR_time] = (SyscallDesc){1, 0, 1, {sizeof(time_t), 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_stat] = (SyscallDesc){2, 0, 1, {0, sizeof(struct stat), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_fstat] = (SyscallDesc){2, 0, 1, {0, sizeof(struct stat), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_pipe] = (SyscallDesc){1, 0, 1, {sizeof(int)*2, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_times] = (SyscallDesc){1, 0, 1, {sizeof(struct tms), 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_ustat] = (SyscallDesc){2, 0, 1, {0, sizeof(struct ustat), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_getrlimit] = (SyscallDesc){2, 0, 1, {0, sizeof(struct rlimit), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_getrusage] = (SyscallDesc){2, 0, 1, {0, sizeof(struct rusage), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_gettimeofday] = (SyscallDesc){2, 0, 1, {sizeof(struct timeval), sizeof(struct timezone), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_select] = (SyscallDesc){5, 0, 1, {0, sizeof(fd_set), sizeof(fd_set), sizeof(fd_set), sizeof(struct timeval), 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_lstat] = (SyscallDesc){2, 0, 1, {0, sizeof(struct stat), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_statfs] = (SyscallDesc){2, 0, 1, {0, sizeof(struct statfs), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_fstatfs] = (SyscallDesc){2, 0, 1, {0, sizeof(struct statfs), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_setitimer] = (SyscallDesc){3, 0, 1, {0, 0, sizeof(struct itimerval), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_getitimer] = (SyscallDesc){2, 0, 1, {0, sizeof(struct itimerval), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_stat] = (SyscallDesc){2, 0, 1, {0, sizeof(struct stat), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_fstat] = (SyscallDesc){2, 0, 1, {0, sizeof(struct stat), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_uname] = (SyscallDesc){1, 0, 1, {sizeof(struct new_utsname), 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_wait4] = (SyscallDesc){4, 0, 1, {0, sizeof(int), 0, sizeof(struct rusage), 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_sysinfo] = (SyscallDesc){1, 0, 1, {sizeof(struct sysinfo), 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_clone] = (SyscallDesc){5, 0, 1, {0, 0, sizeof(int), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_uname] = (SyscallDesc){1, 0, 1, {sizeof(struct new_utsname), 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_adjtimex] = (SyscallDesc){1, 0, 1, {sizeof(struct timex), 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_getdents] = (SyscallDesc){3, 0, 1, {0, sizeof(struct linux_dirent), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_select] = (SyscallDesc){5, 0, 1, {0, sizeof(fd_set), sizeof(fd_set), sizeof(fd_set), sizeof(struct timeval), 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_sched_getparam] = (SyscallDesc){2, 0, 1, {0, sizeof(struct sched_param), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_sched_rr_get_interval] = (SyscallDesc){2, 0, 1, {0, sizeof(struct timespec), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_nanosleep] = (SyscallDesc){2, 0, 1, {0, sizeof(struct timespec), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_getresuid] = (SyscallDesc){3, 0, 1, {sizeof(uid_t), sizeof(uid_t), sizeof(uid_t), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_getresgid] = (SyscallDesc){3, 0, 1, {sizeof(gid_t), sizeof(gid_t), sizeof(gid_t), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_rt_sigtimedwait] = (SyscallDesc){4, 0, 1, {0, sizeof(siginfo_t), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_rt_sigqueueinfo] = (SyscallDesc){3, 0, 1, {0, 0, sizeof(siginfo_t), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_capget] = (SyscallDesc){2, 0, 1, {sizeof(cap_user_header_t), sizeof(cap_user_data_t), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_sigaltstack] = (SyscallDesc){2, 0, 1, {0, sizeof(stack_t), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_sendfile] = (SyscallDesc){4, 0, 1, {0, 0, sizeof(off_t), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_getrlimit] = (SyscallDesc){2, 0, 1, {0, sizeof(struct rlimit), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_getresuid] = (SyscallDesc){3, 0, 1, {sizeof(uid_t), sizeof(uid_t), sizeof(uid_t), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_getresgid] = (SyscallDesc){3, 0, 1, {sizeof(gid_t), sizeof(gid_t), sizeof(gid_t), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_sched_getaffinity] = (SyscallDesc){3, 0, 1, {0, 0, sizeof(cpu_set_t), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_get_thread_area] = (SyscallDesc){1, 0, 1, {sizeof(struct user_desc), 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_io_setup] = (SyscallDesc){2, 0, 1, {0, sizeof(aio_context_t), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_io_cancel] = (SyscallDesc){3, 0, 1, {0, 0, sizeof(struct io_event), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_timer_create] = (SyscallDesc){3, 0, 1, {0, 0, sizeof(timer_t), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_timer_settime] = (SyscallDesc){4, 0, 1, {0, 0, 0, sizeof(struct itimerspec), 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_timer_gettime] = (SyscallDesc){2, 0, 1, {0, sizeof(struct itimerspec), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_clock_gettime] = (SyscallDesc){2, 0, 1, {0, sizeof(struct timespec), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_clock_getres] = (SyscallDesc){2, 0, 1, {0, sizeof(struct timespec), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_clock_nanosleep] = (SyscallDesc){4, 0, 1, {0, 0, 0, sizeof(struct timespec), 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_get_robust_list] = (SyscallDesc){3, 0, 1, {0, sizeof(struct robust_list_head*), sizeof(size_t), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_splice] = (SyscallDesc){6, 0, 1, {0, sizeof(loff_t), 0, sizeof(loff_t), 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_mq_getsetattr] = (SyscallDesc){3, 0, 1, {0, 0, sizeof(struct mq_attr), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_waitid] = (SyscallDesc){4, 0, 1, {0, 0, sizeof(siginfo_t), 0, sizeof(struct rusage), 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_pselect6] = (SyscallDesc){6, 0, 1, {0, sizeof(fd_set), sizeof(fd_set), sizeof(fd_set), 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_move_pages] = (SyscallDesc){6, 0, 1, {0, 0, 0, 0, sizeof(int), 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_getcpu] = (SyscallDesc){3, 0, 1, {sizeof(unsigned), sizeof(unsigned), sizeof(struct getcpu_cache), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_timerfd_settime] = (SyscallDesc){4, 0, 1, {0, 0, 0, sizeof(struct itimerspec), 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_timerfd_gettime] = (SyscallDesc){2, 0, 1, {0, sizeof(struct itimerspec), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_rt_tgsigqueueinfo] = (SyscallDesc){4, 0, 1, {0, 0, 0, sizeof(siginfo_t), 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_rt_tgsigqueueinfo] = (SyscallDesc){4, 0, 1, {0, 0, 0, sizeof(siginfo_t), 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_perf_event_open] = (SyscallDesc){5, 0, 1, {sizeof(struct perf_event_attr), 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_name_to_handle_at] = (SyscallDesc){5, 0, 1, {0, 0, sizeof(struct file_handle), sizeof(int), 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_open_by_handle_at] = (SyscallDesc){3, 0, 1, {0, sizeof(struct file_handle), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_clock_adjtime] = (SyscallDesc){2, 0, 1, {0, sizeof(struct timex), 0, 0, 0, 0}, NULL, NULL};
#if 0
  kSyscallDesc[TARGET_NR_fcntl] = (SyscallDesc){3, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postFcntlHook};
  kSyscallDesc[TARGET_NR_getgroups] = (SyscallDesc){2, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postGetGroups16Hook};
  kSyscallDesc[TARGET_NR_readlink] = (SyscallDesc){3, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postReadHook};
  kSyscallDesc[TARGET_NR_uselib] = (SyscallDesc){1, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postUseLibHook};
  kSyscallDesc[TARGET_NR_syslog] = (SyscallDesc){3, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postSyslogHook};
  kSyscallDesc[TARGET_NR_modify_ldt] = (SyscallDesc){3, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postModifyLdtHook};
  kSyscallDesc[TARGET_NR_quotactl] = (SyscallDesc){4, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postQuotatlHook};
  kSyscallDesc[TARGET_NR_readv] = (SyscallDesc){3, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postReadvHook};
  kSyscallDesc[TARGET_NR__sysctl] = (SyscallDesc){1, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postSysctlHook};
  kSyscallDesc[TARGET_NR_mremap] = (SyscallDesc){5, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postMRemapHook};
  kSyscallDesc[TARGET_NR_getgroups] = (SyscallDesc){2, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postGetGroupsHook};
  kSyscallDesc[TARGET_NR_mincore] = (SyscallDesc){3, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postMincoreHook};
  kSyscallDesc[TARGET_NR_getdents] = (SyscallDesc){3, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postGetDentsHook};
  kSyscallDesc[TARGET_NR_getxattr] = (SyscallDesc){4, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postGetxattrHook};
  kSyscallDesc[TARGET_NR_lgetxattr] = (SyscallDesc){4, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postGetxattrHook};
  kSyscallDesc[TARGET_NR_fgetxattr] = (SyscallDesc){4, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postGetxattrHook};
  kSyscallDesc[TARGET_NR_listxattr] = (SyscallDesc){3, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postListXattrHook};
  kSyscallDesc[TARGET_NR_llistxattr] = (SyscallDesc){3, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postListXattrHook};
  kSyscallDesc[TARGET_NR_flistxattr] = (SyscallDesc){3, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postListXattrHook};
  kSyscallDesc[TARGET_NR_io_getevents] = (SyscallDesc){5, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postIoGetEventsHook};
  kSyscallDesc[TARGET_NR_lookup_dcookie] = (SyscallDesc){3, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postLookupDcookieHook};
  kSyscallDesc[TARGET_NR_epoll_wait] = (SyscallDesc){4, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postEpollWaitHook};
  kSyscallDesc[TARGET_NR_mq_timedreceive] = (SyscallDesc){5, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postMqTimedReceiveHook};
  kSyscallDesc[TARGET_NR_readlinkat] = (SyscallDesc){4, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postReadLinkAtHook};
  kSyscallDesc[TARGET_NR_ppoll] = (SyscallDesc){5, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postPollHook};
  kSyscallDesc[TARGET_NR_get_mempolicy] = (SyscallDesc){5, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postGetMemPolicy};
  kSyscallDesc[TARGET_NR_epoll_pwait] = (SyscallDesc){6, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postEpollWaitHook};
  kSyscallDesc[TARGET_NR_preadv] = (SyscallDesc){5, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postReadvHook};
  kSyscallDesc[TARGET_NR_recvmmsg] = (SyscallDesc){5, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postRecvMmsgHook};

#ifdef __i386__
  kSyscallDesc[TARGET_NR_waitpid] = (SyscallDesc){3, 0, 1, {0, sizeof(int), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_break] = (SyscallDesc){0, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_umount] = (SyscallDesc){1, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_stime] = (SyscallDesc){1, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_stty] = (SyscallDesc){0, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_gtty] = (SyscallDesc){0, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_nice] = (SyscallDesc){1, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_ftime] = (SyscallDesc){0, 0, 1, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_prof] = (SyscallDesc){0, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_signal] = (SyscallDesc){2, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_lock] = (SyscallDesc){0, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_mpx] = (SyscallDesc){0, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_ulimit] = (SyscallDesc){0, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_olduname] = (SyscallDesc){1, 0, 1, {sizeof(struct oldold_utsname), 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_rt_sigaction] = (SyscallDesc){4, 0, 1, {0, 0, sizeof(struct sigaction), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_sgetmask] = (SyscallDesc){0, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_ssetmask] = (SyscallDesc){1, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_sigreturn] = (SyscallDesc){1, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_sigprocmask] = (SyscallDesc){3, 0, 1, {0, 0, sizeof(old_sigset_t), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_sigsuspend] = (SyscallDesc){1, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_sigpending] = (SyscallDesc){1, 0, 1, {sizeof(old_sigset_t), 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_rt_sigreturn] = (SyscallDesc){1, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_rt_sigprocmask] = (SyscallDesc){4, 0, 1, {0, 0, sizeof(sigset_t), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_rt_sigpending] = (SyscallDesc){2, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postRtSigPendingHook};
  kSyscallDesc[TARGET_NR_readdir] = (SyscallDesc){3, 0, 1, {0, sizeof(struct old_linux_dirent), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_profil] = (SyscallDesc){0, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_socketcall] = (SyscallDesc){2, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postSocketCallHook};
  kSyscallDesc[TARGET_NR_idle] = (SyscallDesc){0, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_vm86old] = (SyscallDesc){2, 0, 1, {sizeof(struct vm86_struct ), 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_ipc] = (SyscallDesc){6, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postIpcHook};
  kSyscallDesc[TARGET_NR_bdflush] = (SyscallDesc){2, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR__llseek] = (SyscallDesc){5, 0, 1, {0, 0, 0, sizeof(loff_t), 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_vm86] = (SyscallDesc){3, 0, 1, {0, sizeof(struct vm86plus_struct ), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_mmap2] = (SyscallDesc){6, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postMMapHook};
  kSyscallDesc[TARGET_NR_truncate64] = (SyscallDesc){2, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_ftruncate64] = (SyscallDesc){2, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_stat64] = (SyscallDesc){2, 0, 1, {0, sizeof(struct stat64), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_lstat64] = (SyscallDesc){2, 0, 1, {0, sizeof(struct stat64), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_fstat64] = (SyscallDesc){2, 0, 1, {0, sizeof(struct stat64), 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_fcntl64] = (SyscallDesc){3, 1, 0, {0, 0, 0, 0, 0, 0}, NULL, postFcntlHook};
  kSyscallDesc[TARGET_NR_sendfile64] = (SyscallDesc){4, 0, 1, {0, 0, sizeof(loff_t), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_statfs64] = (SyscallDesc){3, 0, 1, {0, 0, sizeof(struct statfs64), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_fstatfs64] = (SyscallDesc){3, 0, 1, {0, 0, sizeof(struct statfs64), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_fadvise64_64] = (SyscallDesc){4, 0, 0, {0, 0, 0, 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_fstatat64] = (SyscallDesc){4, 0, 1, {0, 0, sizeof(struct stat64), 0, 0, 0}, NULL, NULL};
  kSyscallDesc[TARGET_NR_sigaction] = (SyscallDesc){3, 0, 1, {0, 0, sizeof(struct sigaction), 0, 0, 0}, NULL, NULL};
#endif
#endif
}
