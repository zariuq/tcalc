#ifndef TC_STACK_GUARD_H
#define TC_STACK_GUARD_H

/* Stack room for the recursive checkers, and an explicit outcome when it runs out.
 *
 * The checkers walk terms recursively, so an input that nests deeply enough exhausts the
 * stack.  tc_stack_guard(argv), called first in main, does two things:
 *
 *   1. It asks for a stack of TC_STACK_GUARD_BYTES (less where the hard limit is lower).
 *      A larger stack limit takes full effect only for a process started under it, so the
 *      program starts itself again once.  Where that is not possible the request still
 *      applies as far as the address-space layout of the running process allows.
 *
 *   2. It installs a handler, on its own signal stack, for the fault raised when the stack
 *      cannot grow any further.  The handler prints one line and exits with status
 *      TC_STACK_GUARD_EXIT: no verdict.  That status is neither an acceptance nor a refusal
 *      of the input.  Every other invalid access keeps its default outcome.
 *
 * Under AddressSanitizer and ThreadSanitizer the function does nothing: those tools manage
 * stacks and faults themselves.
 *
 * The including file must select POSIX.1-2008 with the XSI extension (_XOPEN_SOURCE 700)
 * before its first system header: the alternate signal stack is an XSI facility.
 */

#include <signal.h>
#include <stdint.h>
#include <string.h>
#include <sys/resource.h>
#include <unistd.h>

#define TC_STACK_GUARD_BYTES ((rlim_t)1 << 30)
#define TC_STACK_GUARD_EXIT 2

#if defined(__SANITIZE_ADDRESS__) || defined(__SANITIZE_THREAD__)
#define TC_STACK_GUARD_OFF 1
#elif defined(__has_feature)
#if __has_feature(address_sanitizer) || __has_feature(thread_sanitizer)
#define TC_STACK_GUARD_OFF 1
#endif
#endif

#ifndef TC_STACK_GUARD_OFF

static uintptr_t tc_stack_guard_top;    /* an address in the frame of main */
static uintptr_t tc_stack_guard_span;   /* how far below it a stack access can fall */
static const char *tc_stack_guard_prog = "checker";
static char tc_stack_guard_signal_stack[1 << 16];

/* A fault whose address lies in the range the stack may grow into is a stack that could not
 * grow.  Only async-signal-safe calls are made here. */
static void tc_stack_guard_on_fault(int sig, siginfo_t *si, void *context) {
  (void)context;
  uintptr_t at = (uintptr_t)si->si_addr;
  if (at < tc_stack_guard_top && tc_stack_guard_top - at <= tc_stack_guard_span) {
    static const char msg[] = ": no verdict: the input nests more deeply than the stack allows\n";
    if (write(2, tc_stack_guard_prog, strlen(tc_stack_guard_prog)) < 0) {}
    if (write(2, msg, sizeof msg - 1) < 0) {}
    _exit(TC_STACK_GUARD_EXIT);
  }
  signal(sig, SIG_DFL);                 /* not the stack: fault again with the default outcome */
}

#endif

static inline void tc_stack_guard(char **argv) {
#ifdef TC_STACK_GUARD_OFF
  (void)argv;
#else
  struct rlimit rl;
  if (getrlimit(RLIMIT_STACK, &rl) != 0) return;
  rlim_t want = TC_STACK_GUARD_BYTES;
  if (rl.rlim_max != RLIM_INFINITY && rl.rlim_max < want) want = rl.rlim_max;
  if (rl.rlim_cur != RLIM_INFINITY && rl.rlim_cur < want) {
    rl.rlim_cur = want;
    /* After a successful restart the limit already equals `want`, so this branch is not
     * taken a second time.  execv returns only when the restart is not possible. */
    if (setrlimit(RLIMIT_STACK, &rl) == 0) execv("/proc/self/exe", argv);
    if (getrlimit(RLIMIT_STACK, &rl) != 0) return;
  }

  const uintptr_t slack = (uintptr_t)16 << 20;   /* one frame may reach this far past the limit */
  const uintptr_t widest = (uintptr_t)16 << 30;  /* range assumed under an unlimited stack */
  tc_stack_guard_top = (uintptr_t)&rl;
  tc_stack_guard_span = (rl.rlim_cur == RLIM_INFINITY || (uintptr_t)rl.rlim_cur > widest ? widest : (uintptr_t)rl.rlim_cur) + slack;
  if (argv && argv[0]) {
    const char *slash = strrchr(argv[0], '/');
    tc_stack_guard_prog = slash ? slash + 1 : argv[0];
  }

  stack_t ss;
  memset(&ss, 0, sizeof ss);
  ss.ss_sp = tc_stack_guard_signal_stack;
  ss.ss_size = sizeof tc_stack_guard_signal_stack;
  if (sigaltstack(&ss, NULL) != 0) return;

  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_sigaction = tc_stack_guard_on_fault;
  sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
  sigemptyset(&sa.sa_mask);
  sigaction(SIGSEGV, &sa, NULL);
  sigaction(SIGBUS, &sa, NULL);
#endif
}

#endif
