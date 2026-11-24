// Typical integer loops, compiled at default -O2 (auto-vectorisation on) to
// measure which instructions real compiler output needs.
#include <stddef.h>
#include <stdint.h>
long sum64(const long *p, size_t n) { long s = 0; for (size_t i = 0; i < n; i++) s += p[i]; return s; }
int sum32(const int *p, size_t n) { int s = 0; for (size_t i = 0; i < n; i++) s += p[i]; return s; }
unsigned sum8(const unsigned char *p, size_t n) { unsigned s = 0; for (size_t i = 0; i < n; i++) s += p[i]; return s; }
void add_arrays(int *a, const int *b, const int *c, size_t n) { for (size_t i = 0; i < n; i++) a[i] = b[i] + c[i]; }
void scale(long *a, long k, size_t n) { for (size_t i = 0; i < n; i++) a[i] *= k; }
int max_arr(const int *p, size_t n) { int m = p[0]; for (size_t i = 1; i < n; i++) if (p[i] > m) m = p[i]; return m; }
size_t count_eq(const int *p, size_t n, int v) { size_t c = 0; for (size_t i = 0; i < n; i++) c += p[i] == v; return c; }
void memset_u8(unsigned char *p, unsigned char v, size_t n) { for (size_t i = 0; i < n; i++) p[i] = v; }
void copy_u32(uint32_t *d, const uint32_t *s, size_t n) { for (size_t i = 0; i < n; i++) d[i] = s[i]; }
void reverse(int *p, size_t n) { for (size_t i = 0; i < n / 2; i++) { int t = p[i]; p[i] = p[n-1-i]; p[n-1-i] = t; } }
size_t my_strlen(const char *s) { size_t n = 0; while (s[n]) n++; return n; }
int my_strcmp(const char *a, const char *b) { while (*a && *a == *b) { a++; b++; } return (unsigned char)*a - (unsigned char)*b; }
uint32_t fnv1a(const unsigned char *p, size_t n) { uint32_t h = 2166136261u; for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 16777619u; } return h; }
int popcount_arr(const uint64_t *p, size_t n) { int c = 0; for (size_t i = 0; i < n; i++) c += __builtin_popcountll(p[i]); return c; }
void to_upper(char *s, size_t n) { for (size_t i = 0; i < n; i++) if (s[i] >= 'a' && s[i] <= 'z') s[i] -= 32; }
long dot(const int *a, const int *b, size_t n) { long s = 0; for (size_t i = 0; i < n; i++) s += (long)a[i] * b[i]; return s; }
void widen(long *d, const int *s, size_t n) { for (size_t i = 0; i < n; i++) d[i] = s[i]; }
void narrow(short *d, const int *s, size_t n) { for (size_t i = 0; i < n; i++) d[i] = (short)s[i]; }
void shift_arr(uint32_t *a, size_t n) { for (size_t i = 0; i < n; i++) a[i] = (a[i] >> 3) ^ (a[i] << 5); }
void abs_arr(int *a, size_t n) { for (size_t i = 0; i < n; i++) a[i] = a[i] < 0 ? -a[i] : a[i]; }
void clamp(int *a, size_t n) { for (size_t i = 0; i < n; i++) a[i] = a[i] < 0 ? 0 : a[i] > 255 ? 255 : a[i]; }
void insertion_sort(int *a, size_t n) { for (size_t i = 1; i < n; i++) { int x = a[i]; size_t j = i; while (j > 0 && a[j-1] > x) { a[j] = a[j-1]; j--; } a[j] = x; } }
long bsearch_idx(const long *a, size_t n, long k) { size_t lo = 0, hi = n; while (lo < hi) { size_t m = lo + (hi - lo) / 2; if (a[m] < k) lo = m + 1; else hi = m; } return lo; }
struct node { struct node *next; long v; };
long list_sum(const struct node *p) { long s = 0; for (; p; p = p->next) s += p->v; return s; }
int switch_fn(int x) { switch (x) { case 0: return 7; case 1: return 13; case 2: return 99; case 3: return -4; case 4: return 1000; case 5: return 3; default: return 0; } }
uint64_t mix(uint64_t x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
uint32_t bswap_sum(const uint32_t *p, size_t n) { uint32_t s = 0; for (size_t i = 0; i < n; i++) s += __builtin_bswap32(p[i]); return s; }
void histogram(unsigned *h, const unsigned char *p, size_t n) { for (size_t i = 0; i < n; i++) h[p[i]]++; }
long matmul_trace(const long *a, const long *b, size_t n) { long t = 0; for (size_t i = 0; i < n; i++) for (size_t k = 0; k < n; k++) t += a[i*n+k] * b[k*n+i]; return t; }
void prefix_sum(long *a, size_t n) { for (size_t i = 1; i < n; i++) a[i] += a[i-1]; }
int all_zero(const unsigned char *p, size_t n) { unsigned char acc = 0; for (size_t i = 0; i < n; i++) acc |= p[i]; return acc == 0; }
uint8_t min_u8(const uint8_t *p, size_t n) { uint8_t m = 255; for (size_t i = 0; i < n; i++) if (p[i] < m) m = p[i]; return m; }
