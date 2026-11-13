/* Shared helpers for the kernel controls.
   A control exits 0 when the guarantee it names holds and 1 when it is violated.
   Exit 2 means the control could not set its scene up (no verdict). */
#pragma once
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include "tcalc.h"

static int kc_violations;
#define SETUP(c) do { if (!(c)) { printf("NO VERDICT (setup failed) line %d: %s\n", __LINE__, #c); exit(2); } } while (0)
#define HOLDS(c, what) do { if (c) printf("  holds:    %s\n", what); else { printf("  VIOLATED: %s\n", what); kc_violations++; } } while (0)
#define FINISH(name) do { printf("%s: %s\n", name, kc_violations ? "VIOLATED" : "holds"); return kc_violations ? 1 : 0; } while (0)

/* Run f in a child; returns 0 if it returned normally, the signal number if it died. */
static int kc_survives(void (*f)(void)) {
  fflush(stdout);
  pid_t pid = fork();
  if (pid < 0) { printf("NO VERDICT (fork failed)\n"); exit(2); }
  if (pid == 0) { f(); fflush(stdout); _exit(0); }
  int st = 0;
  waitpid(pid, &st, 0);
  if (WIFSIGNALED(st)) return WTERMSIG(st);
  if (WIFEXITED(st) && WEXITSTATUS(st) != 0) return 1000 + WEXITSTATUS(st);
  return 0;
}

/* A small first-order theory used by most controls.
   Sorts: NAT (data), THM (provable). Space 1 is the protected store.
   Constructors: Z:NAT, S:NAT->NAT, EQ:NAT*NAT->THM, A1,B1,W1:NAT->THM, PAIR:NAT*NAT->THM. */
static int NAT, THM, Zc, Sc, EQc, A1c, B1c, W1c, PAIRc;
static Term kc_z(void) { return tc_app(Zc, NULL); }
static Term kc_s(Term x) { return tc_app(Sc, &x); }
static Term kc_num(int n) { Term t = kc_z(); for (int i = 0; i < n && t; i++) t = kc_s(t); return t; }
static Term kc_eq(Term a, Term b) { Term x[2] = { a, b }; return tc_app(EQc, x); }
static Term kc_u(int con, Term a) { return tc_app(con, &a); }
static Term kc_pair(Term a, Term b) { Term x[2] = { a, b }; return tc_app(PAIRc, x); }
static void kc_theory(void) {
  SETUP(tc_init(1u << 12, 1u << 8));
  NAT = tc_sort(0); THM = tc_sort(SORT_PROVABLE);
  Binder n1 = { (uint16_t)NAT, 0, 0 };
  Binder n2[2] = { { (uint16_t)NAT, 0, 0 }, { (uint16_t)NAT, 0, 0 } };
  Zc = tc_con((uint16_t)NAT, 0, 0, NULL);
  Sc = tc_con((uint16_t)NAT, 0, 1, &n1);
  EQc = tc_con((uint16_t)THM, 0, 2, n2);
  A1c = tc_con((uint16_t)THM, 0, 1, &n1);
  B1c = tc_con((uint16_t)THM, 0, 1, &n1);
  W1c = tc_con((uint16_t)THM, 0, 1, &n1);
  PAIRc = tc_con((uint16_t)THM, 0, 2, n2);
  SETUP(NAT > 0 && THM > 0 && Zc >= 0 && Sc >= 0 && EQc >= 0 && A1c >= 0 && B1c >= 0 && W1c >= 0 && PAIRc >= 0);
}
static void kc_ctx_nat(int n) {
  Binder b[8];
  for (int i = 0; i < n; i++) b[i] = (Binder){ (uint16_t)NAT, 0, 0 };
  SETUP(tc_ctx(n, b));
}
