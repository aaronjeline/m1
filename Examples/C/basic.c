// Small functions whose clang -O2 machine code is verified in Examples/Basic.
long max(long a, long b) { return a > b ? a : b; }

unsigned long gcd(unsigned long a, unsigned long b) {
  while (b) {
    unsigned long t = a % b;
    a = b;
    b = t;
  }
  return a;
}

long sum(const long *p, unsigned long n) {
  long s = 0;
  for (unsigned long i = 0; i < n; i++) s += p[i];
  return s;
}
