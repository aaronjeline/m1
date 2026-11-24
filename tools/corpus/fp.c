// Typical floating-point code, compiled at -O2 (auto-vectorisation on).
#include <stddef.h>
#include <math.h>
double dsum(const double *p, size_t n) { double s = 0; for (size_t i = 0; i < n; i++) s += p[i]; return s; }
float fdot(const float *a, const float *b, size_t n) { float s = 0; for (size_t i = 0; i < n; i++) s += a[i] * b[i]; return s; }
void saxpy(float *y, const float *x, float a, size_t n) { for (size_t i = 0; i < n; i++) y[i] += a * x[i]; }
void daxpy(double *y, const double *x, double a, size_t n) { for (size_t i = 0; i < n; i++) y[i] = a * x[i] + y[i]; }
double poly(double x) { return ((3.0 * x + 2.0) * x - 7.5) * x + 1.0; }
double mean(const double *p, size_t n) { double s = 0; for (size_t i = 0; i < n; i++) s += p[i]; return n ? s / n : 0; }
double dmax(const double *p, size_t n) { double m = -INFINITY; for (size_t i = 0; i < n; i++) m = fmax(m, p[i]); return m; }
float fclamp(float x, float lo, float hi) { return x < lo ? lo : x > hi ? hi : x; }
long to_long(double x) { return (long)x; }
int round_int(double x) { return (int)lround(x); }
double floor_d(double x) { return floor(x); }
double hyp(double a, double b) { return sqrt(a * a + b * b); }
void scale_f(float *a, float k, size_t n) { for (size_t i = 0; i < n; i++) a[i] *= k; }
void int_to_float(float *d, const int *s, size_t n) { for (size_t i = 0; i < n; i++) d[i] = (float)s[i]; }
void float_to_int(int *d, const float *s, size_t n) { for (size_t i = 0; i < n; i++) d[i] = (int)s[i]; }
void d2f(float *d, const double *s, size_t n) { for (size_t i = 0; i < n; i++) d[i] = (float)s[i]; }
void fabs_arr(double *a, size_t n) { for (size_t i = 0; i < n; i++) a[i] = fabs(a[i]); }
int count_pos(const float *a, size_t n) { int c = 0; for (size_t i = 0; i < n; i++) c += a[i] > 0.0f; return c; }
void relu(float *a, size_t n) { for (size_t i = 0; i < n; i++) a[i] = a[i] > 0 ? a[i] : 0; }
double horner(const double *c, size_t n, double x) { double r = 0; for (size_t i = n; i-- > 0;) r = r * x + c[i]; return r; }
void matvec(float *y, const float *A, const float *x, size_t n) { for (size_t i = 0; i < n; i++) { float s = 0; for (size_t j = 0; j < n; j++) s += A[i*n+j] * x[j]; y[i] = s; } }
double norm2(const double *a, size_t n) { double s = 0; for (size_t i = 0; i < n; i++) s += a[i] * a[i]; return sqrt(s); }
void lerp(float *d, const float *a, const float *b, float t, size_t n) { for (size_t i = 0; i < n; i++) d[i] = a[i] + t * (b[i] - a[i]); }
float fminv(const float *a, size_t n) { float m = INFINITY; for (size_t i = 0; i < n; i++) m = fminf(m, a[i]); return m; }
void div_arr(double *a, const double *b, size_t n) { for (size_t i = 0; i < n; i++) a[i] /= b[i]; }
void sqrt_arr(float *a, size_t n) { for (size_t i = 0; i < n; i++) a[i] = sqrtf(a[i]); }
void neg_arr(double *a, size_t n) { for (size_t i = 0; i < n; i++) a[i] = -a[i]; }
void u2d(double *d, const unsigned long *s, size_t n) { for (size_t i = 0; i < n; i++) d[i] = (double)s[i]; }
