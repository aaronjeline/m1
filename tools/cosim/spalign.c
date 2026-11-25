#include <stdio.h>
#include <signal.h>
#include <setjmp.h>
#include <stdint.h>
static sigjmp_buf env; static volatile int sig;
static void h(int s){ sig=s; siglongjmp(env,1); }
int main(){
  static char alt[65536]; stack_t ss={.ss_sp=alt,.ss_size=sizeof alt}; sigaltstack(&ss,0);
  struct sigaction sa={0}; sa.sa_handler=h; sa.sa_flags=SA_ONSTACK; sigaction(SIGBUS,&sa,0); sigaction(SIGSEGV,&sa,0);
  for (int mis = 0; mis < 16; mis += 4) {
    uint64_t v = 0; sig = 0;
    if (!sigsetjmp(env,1)) asm volatile("mov x9, sp\n sub sp, x9, %1\n ldr %0, [sp, #-16]\n mov sp, x9" : "=&r"(v) : "r"((uint64_t)(32 + mis)) : "x9", "memory");
    printf("ldr [sp] with sp%%16=%d: %s\n", (16 - mis % 16) % 16, sig ? "FAULT" : "ok");
    sig = 0;
    if (!sigsetjmp(env,1)) asm volatile("mov x9, sp\n sub sp, x9, %1\n ldapur %0, [sp, #-16]\n mov sp, x9" : "=&r"(v) : "r"((uint64_t)(32 + mis)) : "x9", "memory");
    printf("ldapur [sp] with sp%%16=%d: %s\n", (16 - mis % 16) % 16, sig ? "FAULT" : "ok");
    sig = 0;
    if (!sigsetjmp(env,1)) asm volatile("mov x9, sp\n sub sp, x9, %0\n add x10, sp, #8\n mov sp, x9" : : "r"((uint64_t)(32 + mis)) : "x9", "x10", "memory");
    printf("add x, sp (no access) with sp%%16=%d: %s\n", (16 - mis % 16) % 16, sig ? "FAULT" : "ok");
  }
}
