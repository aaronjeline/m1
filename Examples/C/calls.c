// A non-leaf function: builds a stack frame and calls a helper twice.
__attribute__((noinline)) long sq(long x) { return x * x; }

long sumsq(long a, long b) { return sq(a) + sq(b); }
