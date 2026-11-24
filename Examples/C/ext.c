// Calls to an external (libc) function, verified against an assumed contract.
#include <stdlib.h>
// A die roll: 1..6.
int roll(void) { return rand() % 6 + 1; }
