#include <stdio.h>
#include <signal.h>
#include <setjmp.h>
#include <stdint.h>
static sigjmp_buf env; static volatile int sig;
static void h(int s){ sig=s; siglongjmp(env,1); }
static char buf[256] __attribute__((aligned(64)));
#define T(name, asmstr) \
  for (int off = 0; off < 32; off++) { sig = 0; char *p = buf + 64 + off; uint64_t v = 0, st = 0; \
    if (!sigsetjmp(env,1)) { asm volatile(asmstr : "+r"(v), "+r"(st) : "r"(p) : "memory"); } \
    printf("%s off=%2d %s\n", name, off, sig ? "FAULT" : "ok"); }
int main(){ signal(SIGBUS,h); signal(SIGSEGV,h);
  T("ldxr  x", "ldxr %0, [%2]")
  T("ldxr  w", "ldxr %w0, [%2]")
  T("ldaxrh", "ldaxrh %w0, [%2]")
  T("ldar  x", "ldar %0, [%2]")
  T("ldar  w", "ldar %w0, [%2]")
  T("stlr  x", "stlr %0, [%2]")
  T("ldadd x", "ldadd %0, %1, [%2]")
  T("ldadd w", "ldadd %w0, %w1, [%2]")
  T("swp   h", "swph %w0, %w1, [%2]")
  T("cas   x", "cas %0, %1, [%2]")
  T("stxr  x", "ldxr %0, [%2]\n stxr %w1, %0, [%2]")
  T("ldapr x", "ldapr %0, [%2]")
}
