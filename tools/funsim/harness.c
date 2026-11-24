// Runs functions of a dylib natively and records inputs and outputs.
//
//   harness <image.dylib> <tests.txt>
//
// Each test line:  <function> <seed> <x0..x7> <d0..d7>
// where an x token "@k+off" means: pointer to buffer k plus off. Buffers are
// NBUF x BUFSZ bytes, filled from the seed (see byte_fn) with their last byte 0.
// Output line per test (all hex):
//   F <entry> <seed> <buf0> <buf1> <buf2> ; X <x0..x7> ; D <d0..d7> ;
//     OK <x0> <x1> <q0lo> <q0hi> <q1lo> <q1hi> ; H <fnv(buf0)> <fnv(buf1)> <fnv(buf2)>
// or "; SIG <n>" if the call crashed.
#include <dlfcn.h>
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NBUF 3
#define BUFSZ 4096

void call_fn(void *fn, const uint64_t *x, const uint64_t *d, uint64_t *out);

static sigjmp_buf env;
static void handler(int sig) { siglongjmp(env, sig); }

static uint8_t byte_fn(uint64_t seed, uint64_t i) {
  return (uint8_t)(((i * 0x9E3779B1ull + seed * 0x85EBCA77ull) >> 16) & 0xff);
}

static uint64_t fnv(const uint8_t *p, size_t n) {
  uint64_t h = 0xcbf29ce484222325ull;
  for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 0x100000001b3ull; }
  return h;
}

int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage\n"); return 2; }
  void *lib = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
  if (!lib) { fprintf(stderr, "%s\n", dlerror()); return 1; }
  FILE *f = fopen(argv[2], "r");
  static uint8_t *buf[NBUF];
  for (int k = 0; k < NBUF; k++) buf[k] = aligned_alloc(4096, BUFSZ);
  static char stack[65536];
  stack_t ss = {.ss_sp = stack, .ss_size = sizeof stack};
  sigaltstack(&ss, 0);
  struct sigaction sa = {.sa_handler = handler, .sa_flags = SA_ONSTACK | SA_NODEFER};
  sigaction(SIGSEGV, &sa, 0); sigaction(SIGBUS, &sa, 0); sigaction(SIGILL, &sa, 0);
  sigaction(SIGFPE, &sa, 0); sigaction(SIGTRAP, &sa, 0);
  char name[256], tok[64];
  unsigned long long seed;
  while (fscanf(f, "%255s %llx", name, &seed) == 2) {
    uint64_t x[8], d[8], out[6] = {0};
    for (int i = 0; i < 8; i++) {
      fscanf(f, "%63s", tok);
      if (tok[0] == '@') {
        int k = tok[1] - '0';
        x[i] = (uint64_t)buf[k] + strtoull(tok + 3, 0, 16);
      } else x[i] = strtoull(tok, 0, 16);
    }
    for (int i = 0; i < 8; i++) { fscanf(f, "%63s", tok); d[i] = strtoull(tok, 0, 16); }
    void *fn = dlsym(lib, name);
    Dl_info info;
    if (!fn || !dladdr(fn, &info)) { fprintf(stderr, "no symbol %s\n", name); return 1; }
    for (int k = 0; k < NBUF; k++) {
      for (int i = 0; i < BUFSZ; i++) buf[k][i] = byte_fn(seed + k, i);
      buf[k][BUFSZ - 1] = 0;
    }
    printf("F %llx %llx", (unsigned long long)((uint8_t *)fn - (uint8_t *)info.dli_fbase), seed);
    for (int k = 0; k < NBUF; k++) printf(" %llx", (unsigned long long)(uintptr_t)buf[k]);
    printf(" ; X");
    for (int i = 0; i < 8; i++) printf(" %llx", (unsigned long long)x[i]);
    printf(" ; D");
    for (int i = 0; i < 8; i++) printf(" %llx", (unsigned long long)d[i]);
    int sig = sigsetjmp(env, 1);
    if (sig) { printf(" ; SIG %d\n", sig); continue; }
    call_fn(fn, x, d, out);
    printf(" ; OK");
    for (int i = 0; i < 6; i++) printf(" %llx", (unsigned long long)out[i]);
    printf(" ; H");
    for (int k = 0; k < NBUF; k++) printf(" %llx", (unsigned long long)fnv(buf[k], BUFSZ));
    printf("\n");
  }
  return 0;
}
