// void call_fn(void *fn, const uint64_t x[8], const uint64_t d[8], uint64_t out[6])
// Calls fn with x0-x7 and d0-d7 set, and stores x0, x1, q0, q1 into out.
    .text
    .p2align 2
    .globl _call_fn
_call_fn:
    stp x29, x30, [sp, #-32]!
    mov x29, sp
    stp x19, x20, [sp, #16]
    mov x16, x0
    mov x19, x3
    ldp d0, d1, [x2]
    ldp d2, d3, [x2, #16]
    ldp d4, d5, [x2, #32]
    ldp d6, d7, [x2, #48]
    mov x17, x1
    ldp x0, x1, [x17]
    ldp x2, x3, [x17, #16]
    ldp x4, x5, [x17, #32]
    ldp x6, x7, [x17, #48]
    blr x16
    stp x0, x1, [x19]
    str q0, [x19, #16]
    str q1, [x19, #32]
    ldp x19, x20, [sp, #16]
    ldp x29, x30, [sp], #32
    ret
