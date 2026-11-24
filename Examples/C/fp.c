// Floating-point examples. Note that clang contracts a*b + c into a fused
// multiply-add by default (-ffp-contract=on), which the specs make explicit.
double poly(double x) { return ((3.0 * x + 2.0) * x - 7.5) * x + 1.0; }
float clampf(float x, float lo, float hi) { return x < lo ? lo : x > hi ? hi : x; }
long to_long(double x) { return (long)x; }
