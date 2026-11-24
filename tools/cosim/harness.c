// Co-simulation harness: executes single A64 instructions on the host CPU
// (an Apple M1) and prints input and output architectural state.
#include <setjmp.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#define PAGE 16384
#define GUARD (4 * PAGE)
#define BUFSZ PAGE

struct ctx {
  uint64_t x[31];
  uint64_t sp;
  uint64_t nzcv;
  uint64_t csp;
  uint64_t path;
  uint64_t pad;
  uint64_t v[64];
  uint64_t fpcr;
  uint64_t fpsr;
} __attribute__((aligned(16)));
_Static_assert(offsetof(struct ctx, sp) == 248, "layout");
_Static_assert(offsetof(struct ctx, nzcv) == 256, "layout");
_Static_assert(offsetof(struct ctx, path) == 272, "layout");
_Static_assert(offsetof(struct ctx, v) == 288, "layout");
_Static_assert(offsetof(struct ctx, fpcr) == 800, "layout");

#pragma pack(push, 1)
struct tin {
  uint32_t word;
  uint32_t seed;
  uint8_t kind[32]; // 0 = absolute, 1 = buffer-relative, 2 = instruction-relative
  uint64_t x[31];
  uint64_t nzcv;
  uint64_t v[64];
  uint64_t fpcr;
  uint64_t fpsr;
};
#pragma pack(pop)

extern void *cosim_tests[]; // pairs: (stub, instruction address)

static struct ctx C;
static sigjmp_buf env;
static volatile sig_atomic_t sig;
static volatile sig_atomic_t sigcode;

static void handler(int s, siginfo_t *si, void *uc) {
  (void)uc;
  // The instruction may have run with floating-point traps enabled.
  __asm__ volatile("msr fpcr, xzr");
  sig = s;
  sigcode = si ? si->si_code : 0;
  siglongjmp(env, 1);
}

static uint8_t byte_fn(uint64_t seed, uint64_t i) {
  return (uint8_t)(((i * 0x9E3779B1ull + seed * 0x85EBCA77ull) >> 16) & 0xff);
}

static void print_state(const char *tag, const struct ctx *c) {
  printf(" %s", tag);
  for (int r = 0; r < 31; r++) printf(" %llx", (unsigned long long)c->x[r]);
  printf(" %llx %llx", (unsigned long long)c->sp, (unsigned long long)c->nzcv);
  for (int r = 0; r < 64; r++) printf(" %llx", (unsigned long long)c->v[r]);
  printf(" %llx %llx", (unsigned long long)c->fpcr, (unsigned long long)c->fpsr);
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: harness inputs.bin\n"); return 2; }
  FILE *f = fopen(argv[1], "rb");
  if (!f) { perror("open"); return 2; }
  fseek(f, 0, SEEK_END);
  long len = ftell(f);
  fseek(f, 0, SEEK_SET);
  size_t n = (size_t)len / sizeof(struct tin);
  struct tin *tests = malloc(len);
  if (fread(tests, sizeof(struct tin), n, f) != n) { perror("read"); return 2; }
  fclose(f);

  uint8_t *region = mmap(NULL, 2 * GUARD + BUFSZ, PROT_NONE, MAP_PRIVATE | MAP_ANON, -1, 0);
  if (region == MAP_FAILED) { perror("mmap"); return 2; }
  uint8_t *buf = region + GUARD;
  if (mprotect(buf, BUFSZ, PROT_READ | PROT_WRITE)) { perror("mprotect"); return 2; }

  static uint8_t altstack[1 << 16];
  stack_t ss = {.ss_sp = altstack, .ss_size = sizeof altstack, .ss_flags = 0};
  sigaltstack(&ss, NULL);
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_sigaction = handler;
  sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
  int sigs[] = {SIGILL, SIGSEGV, SIGBUS, SIGTRAP, SIGFPE, SIGSYS};
  for (unsigned i = 0; i < sizeof sigs / sizeof *sigs; i++) sigaction(sigs[i], &sa, NULL);

  static uint8_t init[BUFSZ];
  for (size_t t = 0; t < n; t++) {
    struct tin *in = &tests[t];
    uint64_t inst = (uint64_t)cosim_tests[2 * t + 1];
    for (uint64_t i = 0; i < BUFSZ; i++) init[i] = byte_fn(in->seed, i);
    memcpy(buf, init, BUFSZ);
    memset(&C, 0, sizeof C);
    for (int r = 0; r < 31; r++) {
      uint64_t base = in->kind[r] == 1 ? (uint64_t)buf : in->kind[r] == 2 ? inst : 0;
      C.x[r] = base + in->x[r];
    }
    C.sp = (uint64_t)&C;
    C.nzcv = in->nzcv;
    memcpy(C.v, in->v, sizeof C.v);
    C.fpcr = in->fpcr;
    C.fpsr = in->fpsr;

    printf("T %08x %llx %llx %x %x ;", in->word, (unsigned long long)inst,
           (unsigned long long)(uint64_t)buf, BUFSZ, in->seed);
    print_state("I", &C);
    printf(" ;");
    fflush(stdout);

    sig = 0;
    if (sigsetjmp(env, 1) == 0) {
      ((void (*)(struct ctx *))cosim_tests[2 * t])(&C);
    }
    if (sig) {
      printf(" SIG %d %d\n", (int)sig, (int)sigcode);
      continue;
    }
    printf(" OK %llu ;", (unsigned long long)C.path);
    print_state("O", &C);
    printf(" ; M");
    for (uint64_t i = 0; i < BUFSZ; i++)
      if (buf[i] != init[i]) printf(" %llx:%x", (unsigned long long)i, buf[i]);
    printf("\n");
  }
  return 0;
}
