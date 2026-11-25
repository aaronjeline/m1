#!/usr/bin/env python3
"""Generate random single-instruction co-simulation tests.

Writes <out>/tests.s (one stub per test) and <out>/inputs.bin (initial states)
for harness.c.
"""
import argparse
import random
import struct

M64 = (1 << 64) - 1
SPECIAL = [0, 1, 2, 3, 31, 32, 63, 64, M64, M64 - 1, 1 << 63, (1 << 63) - 1,
           0xFFFFFFFF, 0x7FFFFFFF, 0x80000000, 0x100000000, 0xFFFFFFFF00000000]


def rand_val(rng):
    r = rng.random()
    if r < 0.3:
        return rng.getrandbits(64)
    if r < 0.5:
        return rng.choice(SPECIAL)
    if r < 0.7:
        return rng.getrandbits(rng.choice([8, 16, 32]))
    if r < 0.85:
        return (-rng.getrandbits(16)) & M64
    return rng.getrandbits(6)


def rbits(rng):
    return rng.getrandbits(32)


def set_field(w, lo, n, v):
    mask = ((1 << n) - 1) << lo
    return (w & ~mask) | ((v << lo) & mask)


def gen_dp_imm(rng):
    w = (rbits(rng) & ~0x1C000000) | 0x10000000
    cls = (w >> 23) & 7
    sp_dest = (cls == 2 and not (w >> 29) & 1) or (cls == 4 and ((w >> 29) & 3) != 3)
    if sp_dest and (w & 31) == 31:
        w ^= 1
    return w, 'dpimm'


def gen_dp_reg(rng):
    w = (rbits(rng) & ~0x0E000000) | 0x0A000000
    # Bias towards the encoding groups that exist.
    r = rng.random()
    if r < 0.6:
        w = (w & ~(1 << 28)) if r < 0.3 else (w | (1 << 28))
    if (w & 0x1F200000) == 0x0B200000 and not (w >> 29) & 1 and (w & 31) == 31:
        w ^= 1
    return w, 'dpreg'


def gen_ldst(rng):
    while True:
        w = (rbits(rng) & ~0x0A000000) | 0x08000000
        r = rng.random()
        if r < 0.45:   # single register
            w = (w & ~0x3A000000) | 0x38000000
        elif r < 0.7:  # pair
            w = (w & ~0x3A000000) | 0x28000000
        elif r < 0.8:  # exclusive / ordered / CAS
            w = (w & ~0x3F000000) | 0x08000000
        if (w & 0x3B000000) == 0x18000000:
            continue  # literal loads read code memory
        if (w >> 5) & 31 == 31:
            w ^= 1 << 5  # avoid SP as base: SP points at the harness context
        return w, 'ldst'


def gen_rcpc2(rng):
    """LDAPUR/STLUR (unscaled immediate, FEAT_LRCPC2): every size and opc
    (including the unallocated ones) and a random 9-bit offset. The base is
    buffer-relative at a random alignment, so this exercises the 16-byte
    alignment rule on base + offset."""
    w = ((rng.getrandbits(2) << 30) | 0x19000000 | (rng.getrandbits(2) << 22)
         | (rng.getrandbits(9) << 12) | (rng.getrandbits(5) << 5) | rng.getrandbits(5))
    if (w >> 5) & 31 == 31:
        w ^= 1 << 5  # avoid SP as base: SP points at the harness context
    return w, 'ldst'


def gen_branch(rng):
    k = rng.randrange(4)
    if k == 0:
        return 0x14000002 | (rng.getrandbits(1) << 31), 'branch'
    if k == 1:
        return 0x54000040 | rng.getrandbits(4), 'branch'
    if k == 2:
        return (rng.getrandbits(1) << 31) | 0x34000000 | (rng.getrandbits(1) << 24) | (2 << 5) | rng.getrandbits(5), 'branch'
    return (rng.getrandbits(1) << 31) | 0x36000000 | (rng.getrandbits(1) << 24) | (rng.getrandbits(5) << 19) | (2 << 5) | rng.getrandbits(5), 'branch'


def gen_simd(rng):
    k = rng.randrange(4)
    w = rbits(rng)
    if k == 0:
        return (w & ~0x9FE08400) | 0x0E000400, 'simd'
    if k == 1:
        return (w & ~0x9F200400) | 0x0E200400, 'simd'
    if k == 2:
        return (w & ~0x9FF80400) | 0x0F000400, 'simd'
    base = rng.choice([0x1E260000, 0x1E270000, 0x9E660000, 0x9E670000, 0x9EAE0000, 0x9EAF0000])
    return base | (w & 0x3FF), 'simd'


def gen_simd2(rng):
    """Two-reg misc, across lanes, permute, EXT, TBL, shift by immediate,
    three different, dot product, CRC32."""
    w = rbits(rng)
    k = rng.randrange(11)
    if k == 0:
        return (w & ~0x9F3E0C00) | 0x0E200800, 'simd'
    if k == 1:
        return (w & ~0x9F3E0C00) | 0x0E300800, 'simd'
    if k == 2:
        return (w & ~0xBF208C00) | 0x0E000800, 'simd'
    if k == 3:
        return (w & ~0xBFE08400) | 0x2E000000, 'simd'
    if k == 4:
        return (w & ~0xBFE08C00) | 0x0E000000, 'simd'
    if k == 5:
        w = (w & ~0x9F800400) | 0x0F000400
        return (w | (1 << 19)) if (w >> 19) & 15 == 0 else w, 'simd'
    if k == 6:
        return (w & ~0x9F200C00) | 0x0E200000, 'simd'
    if k == 7:
        return (w & ~0x9FE0FC00) | 0x0E809400, 'simd'
    if k == 8:
        return (w & 0x801F03FF) | 0x1AC04000 | (rng.getrandbits(3) << 10), 'dpreg'
    if rng.random() < 0.3:  # scalar shift by immediate
        return (w & ~0xDF800400) | 0x5F000400 | (1 << 22), 'simd'
    if rng.random() < 0.8:  # vector x indexed element
        return (w & ~0x9F000400) | 0x0F000000, 'simd'
    return 0x5EF1B800 | (w & 0x3FF), 'simd'


def gen_vldst(rng):
    """Advanced SIMD structure loads/stores."""
    w = rbits(rng)
    if rng.random() < 0.5:
        w = (w & ~0xBF200000) | 0x0C000000
        if not (w >> 23) & 1:
            w &= ~0x001F0000
    else:
        w = (w & ~0xBF000000) | 0x0D000000
        if not (w >> 23) & 1:
            w &= ~0x001F0000
    if (w >> 5) & 31 == 31:
        w ^= 1 << 5
    return w, 'ldst'


def gen_fp(rng):
    """Scalar floating point (all classes; mostly single/double)."""
    w = rbits(rng)
    ftype = rng.choice([0, 1, 0, 1, 0, 1, 3])
    k = rng.randrange(9)
    if k == 0:    # 1 source
        w = (w & ~0xFF3FFC00) | 0x1E204000 | (rng.randrange(16) << 15)
    elif k == 1:  # 2 source
        w = (w & ~0xFF200C00) | 0x1E200800
    elif k == 2:  # 3 source
        w = (w & ~0xFF000000) | 0x1F000000
    elif k == 3:  # compare
        w = (w & ~0xFF20FC07) | 0x1E202000
        if rng.random() < 0.5 and w & 8:
            w &= ~0x001F0000
    elif k == 4:  # conditional compare
        w = (w & ~0xFF200C00) | 0x1E200400
    elif k == 5:  # conditional select
        w = (w & ~0xFF200C00) | 0x1E200C00
    elif k == 6:  # immediate
        w = (w & ~0xFF201FE0) | 0x1E201000
    else:         # conversions to/from integer
        w = (w & ~0x7F20FC00) | 0x1E200000
        w = set_field(w, 16, 3, rng.randrange(6))
    w = set_field(w, 22, 2, ftype)
    return w, 'fp'


F32 = [0x00000000, 0x80000000, 0x3F800000, 0xBF800000, 0x7F800000, 0xFF800000,
       0x7FC00000, 0x7FA00001, 0xFFC12345, 0xFF812345, 0x00000001, 0x807FFFFF,
       0x00800000, 0x7F7FFFFF, 0x3F000000, 0x3FC00000, 0x40200000, 0x4F000000,
       0xCF000000, 0x5F000000, 0x4B000001, 0x3EAAAAAB, 0x34000000, 0x33800000]
F64 = [0x0, 0x8000000000000000, 0x3FF0000000000000, 0xBFF0000000000000,
       0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000000,
       0x7FF4000000000001, 0xFFF8123456789ABC, 0xFFF0000000000123, 0x1,
       0x800FFFFFFFFFFFFF, 0x0010000000000000, 0x7FEFFFFFFFFFFFFF,
       0x3FE0000000000000, 0x3FF8000000000000, 0x4004000000000000,
       0x43E0000000000000, 0xC3E0000000000000, 0x41E0000000000000,
       0xC1E0000000000000, 0x41EFFFFFFFE00000, 0x4330000000000001,
       0x3FD5555555555555, 0x3CA0000000000000, 0x3C90000000000000,
       0x36A0000000000000, 0x47EFFFFFE0000000, 0x47EFFFFFF0000000]


F16 = [0x0000, 0x8000, 0x3C00, 0xBC00, 0x7C00, 0xFC00, 0x7E00, 0x7D01, 0xFE12, 0x0001,
       0x83FF, 0x0400, 0x7BFF, 0x3800, 0x3E00, 0x4100, 0x5BFF, 0x7800, 0x1400, 0x0C00]


def fp_val(rng):
    r = rng.random()
    if r < 0.15:   # half-precision lanes
        v = 0
        for i in range(4):
            v |= (rng.choice(F16) if rng.random() < 0.6 else
                  (rng.randrange(0x2C00, 0x5000) | rng.getrandbits(1) << 15)) << (16 * i)
        return v
    r = rng.random()
    if r < 0.25:
        return rng.choice(F64)
    if r < 0.5:
        hi = rng.choice([0, rng.choice(F32), rng.getrandbits(32)])
        return rng.choice(F32) | (hi << 32)
    if r < 0.65:  # random double near 1
        return (rng.randrange(0x3F00, 0x4100) << 48) | rng.getrandbits(48)
    if r < 0.8:   # random singles near 1
        return (((rng.randrange(0x3C00, 0x4400) << 16) | rng.getrandbits(16)) << 32) | \
            (rng.randrange(0x3C00, 0x4400) << 16) | rng.getrandbits(16)
    if r < 0.9:   # small integers as doubles / singles
        v = float(rng.randrange(-100, 100)) + rng.choice([0, 0.5, 0.25, 0.75])
        return struct.unpack('<Q', struct.pack('<d', v))[0] if rng.random() < 0.5 \
            else struct.unpack('<I', struct.pack('<f', v))[0]
    return rng.getrandbits(64)


def gen_fpmore(rng):
    """Less common FP: estimates/steps, FMULX, scalar three same, FHM, FCMA, FRINTTS, FJCVTZS."""
    w = rbits(rng)
    k = rng.randrange(10)
    if k == 0:    # scalar three same (single/double or half)
        if rng.random() < 0.7:
            w = (w & ~0xDF20C400) | 0x5E20C400
        else:
            w = (w & ~0xDF60C400) | 0x5E400400
    elif k == 1:  # FCMLA / FCADD
        w = (w & ~0xBF20E400) | 0x2E00C400 if rng.random() < 0.5 else (w & ~0xBF20EC00) | 0x2E00E400
    elif k == 2:  # FMLAL family (vector)
        w = (w & ~0x9FE0FC00) | 0x0E20EC00 | (rng.getrandbits(1) << 23)
        if rng.random() < 0.5:
            w = (w & ~(0x1F << 11)) | (1 << 29) | (0x19 << 11)
    elif k == 3:  # FMLAL family (by element)
        w = (w & ~0x9FC0F400) | 0x0F800000 | (rng.choice([0, 4]) << 12)
        if rng.random() < 0.5:
            w |= (1 << 29) | (1 << 15)
    elif k == 4:  # scalar by element, single/double/half
        if rng.random() < 0.7:
            w = (w & ~0xDF800400) | 0x5F800000
        else:
            w = (w & ~0xDFC00400) | 0x5F000000
        w = set_field(w, 12, 4, rng.choice([1, 5, 9]))
    elif k == 5:  # vector by element FMULX
        w = (w & ~0x9F80F400) | 0x2F809000
    elif k == 6:  # estimates (vector/scalar) and FRINT32/64
        sc = rng.random() < 0.4
        w = (w & ~0xDF3E0C00) | (0x5E200800 if sc else 0x0E200800)
        w = set_field(w, 12, 5, rng.choice([0x1C, 0x1D, 0x1E, 0x1F]))
    elif k == 7:  # scalar FRINT32/64
        w = (w & ~0xFF3FFC00) | 0x1E204000 | (rng.randrange(16, 20) << 15) | (rng.getrandbits(1) << 22)
    elif k == 8:  # FJCVTZS
        w = (w & 0x3FF) | 0x1E7E0000
    else:         # FMULX / FRECPS / FRSQRTS vector
        w = (w & ~0x9F20C400) | 0x0E20C400
        w = set_field(w, 11, 3, rng.choice([3, 7]))
        w &= ~(1 << 29)
    return w, 'fp'


def gen_fpvec(rng):
    """Advanced SIMD floating point."""
    w = rbits(rng)
    k = rng.randrange(7)
    if k <= 1:   # three same
        w = (w & ~0x9F20C400) | 0x0E20C400
    elif k == 2:  # two-reg misc, vector
        w = (w & ~0x9F3E0C00) | 0x0E200800 | (1 << 23 if rng.random() < 0.5 else 0)
        w = set_field(w, 12, 5, rng.choice([0x0C, 0x0D, 0x0E, 0x0F, 0x16, 0x17, 0x18, 0x19,
                                            0x1A, 0x1B, 0x1C, 0x1D, 0x1F]))
    elif k == 3:  # two-reg misc, scalar
        w = (w & ~0xDF3E0C00) | 0x5E200800
        w = set_field(w, 12, 5, rng.choice([0x0C, 0x0D, 0x0E, 0x1A, 0x1B, 0x1C, 0x1D]))
    elif k == 4:  # by element
        w = (w & ~0x9F800400) | 0x0F800000
        w = set_field(w, 12, 4, rng.choice([1, 5, 9, 9, rng.randrange(16)]))
    elif k == 5:  # scalar pairwise / across lanes
        if rng.random() < 0.5:
            w = (w & ~0xFF3E0C00) | 0x7E300800
        else:
            w = (w & ~0xBF3E0C00) | 0x2E300800
        w = set_field(w, 12, 5, rng.choice([0x0C, 0x0D, 0x0F]))
    elif k == 6 and rng.random() < 0.3:  # scalar DUP (element)
        w = (w & ~0xFFE0FC00) | 0x5E000400
    else:         # half precision forms
        j = rng.randrange(6)
        if j <= 1:
            w = (w & ~0x9F60C400) | 0x0E400400
        elif j == 2:
            w = (w & ~0x9F7E0C00) | 0x0E780800
            w = set_field(w, 12, 5, rng.choice([0x0C, 0x0D, 0x0E, 0x0F, 0x18, 0x19,
                                                0x1A, 0x1B, 0x1C, 0x1D, 0x1F]))
        elif j == 3:
            w = (w & ~0xDF7E0C00) | 0x5E780800
            w = set_field(w, 12, 5, rng.choice([0x0C, 0x0D, 0x0E, 0x1A, 0x1B, 0x1C, 0x1D]))
        elif j == 4:
            w = (w & ~0x9FC00400) | 0x0F000000
            w = set_field(w, 12, 4, rng.choice([1, 5, 9]))
        else:
            w = (w & ~0xBF7E0C00) | (rng.choice([0x0E300800, 0x5E300800]))
            w = set_field(w, 12, 5, rng.choice([0x0C, 0x0D, 0x0F]))
            w &= ~(1 << 29)
    return w, 'fp'


def gen_scalar(rng):
    """Scalar integer SIMD and the saturating doubling multiplies."""
    w = rbits(rng)
    base, mask = rng.choice([(0x5E200400, 0xDF200400), (0x7E008400, 0xFF20F400),
                             (0x5E200800, 0xDF3E0C00), (0x5F000400, 0xDF800400),
                             (0x5E200000, 0xDF200C00), (0x5F000000, 0xDF000400),
                             (0x2E008400, 0xBF20F400), (0x0E200800, 0x9F3E0C00),
                             (0x0E200000, 0x9F200C00), (0x0F000000, 0x9F000400)])
    w = (w & ~mask) | base
    if base == 0x5E200800 or base == 0x0E200800:
        w = set_field(w, 12, 5, rng.choice([0x03, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x12, 0x14]))
    if base == 0x0E200000 or base == 0x5E200000:
        w = set_field(w, 12, 4, rng.choice([0x9, 0xB, 0xD]))
    if base == 0x0F000000 or base == 0x5F000000:
        w = set_field(w, 12, 4, rng.choice([0x3, 0x7, 0xB, 0xC, 0xD, 0xF]))
    return w, 'simd'


def gen_crypto(rng):
    """AES, SHA-1/256/512, SHA-3, PMULL."""
    w = rbits(rng)
    base, mask = rng.choice([(0x4E284800, 0xFFFFCC00), (0x5E000000, 0xFFE08C00),
                             (0x5E280800, 0xFFFFCC00), (0xCE608000, 0xFFE0F000),
                             (0xCEC08000, 0xFFFFFC00), (0xCE000000, 0xFFE08000),
                             (0xCE200000, 0xFFE08000), (0xCE800000, 0xFFE00000),
                             (0x0E20E000 | (rng.choice([0, 3]) << 22), 0xBFE0FC00)])
    return (w & ~mask) | base, 'simd'


def gen_sys(rng):
    rt = rng.getrandbits(5)
    return rng.choice([0xD53B4200 | rt, 0xD51B4200 | rt, 0xD503201F, 0xD503203F,
                       0xD5033BBF, 0xD5033B9F, 0xD5033FDF, 0xD503305F]), 'sys'


GENS = [(gen_dp_imm, 3), (gen_dp_reg, 4), (gen_ldst, 4), (gen_rcpc2, 0.5), (gen_branch, 1), (gen_simd, 2), (gen_simd2, 3), (gen_vldst, 1.5), (gen_fp, 4), (gen_fpvec, 3), (gen_fpmore, 2), (gen_crypto, 1), (gen_scalar, 2),
        (gen_sys, 0.3)]


ONLY = None


def gen_test(rng):
    gens, weights = zip(*[(g, wt) for g, wt in GENS if ONLY is None or g.__name__ in ONLY])
    g = rng.choices(gens, weights)[0]
    word, cls = g(rng)
    kind = [0] * 32
    xs = [rand_val(rng) for _ in range(31)]
    if cls == 'ldst':
        # Base register points into the buffer; the (possible) offset register
        # holds a small index, so addresses stay inside the guarded buffer.
        rn, rm = (word >> 5) & 31, (word >> 16) & 31
        if rm < 31 and rm != 18:
            xs[rm] = rng.randrange(0, 64)
        if rm == rn:
            return gen_test(rng)
        kind[rn] = 1
        xs[rn] = 8192 + rng.randrange(-600, 600)
    if cls == 'branch' and rng.random() < 0.3:
        # Exercise BR/BLR/RET with a target of instruction + 8.
        rn = rng.randrange(31)
        word = rng.choice([0xD61F0000, 0xD63F0000, 0xD65F0000]) | (rn << 5)
        kind[rn] = 2
        xs[rn] = 8
    # macOS reserves x18 and may zero it at any time.
    kind[18], xs[18] = 0, 0
    nzcv = rng.getrandbits(4) << 28
    vs = [rand_val(rng) for _ in range(64)]
    if cls == 'fp':
        vs = [fp_val(rng) if i % 2 == 0 or rng.random() < 0.7
              else rng.choice([0, rng.getrandbits(64)]) for i in range(64)]
    seed = rng.getrandbits(32)
    fpcr, fpsr = 0, 0
    if cls in ('fp', 'simd') and rng.random() < 0.5:
        # Random modes: RMode, FZ, DN, AHP, FZ16; sometimes exception traps.
        fpcr = rng.getrandbits(2) << 22
        for b in (24, 25, 26, 19):
            if rng.random() < 0.35:
                fpcr |= 1 << b
        if rng.random() < 0.15:
            fpcr |= rng.getrandbits(8) << 8 & 0x9F00
    if rng.random() < 0.3:
        fpsr = rng.getrandbits(32) & 0x0800009F
    return word, seed, kind, xs, nzcv, vs, fpcr, fpsr


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('-n', type=int, default=10000)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--out', default='.')
    ap.add_argument('--only', help='comma-separated generator names, e.g. gen_fp')
    args = ap.parse_args()
    global ONLY
    ONLY = args.only.split(',') if args.only else None
    rng = random.Random(args.seed)
    with open(f'{args.out}/inputs.bin', 'wb') as fb, open(f'{args.out}/tests.s', 'w') as fs:
        fs.write('    .text\n    .p2align 2\n')
        for i in range(args.n):
            word, seed, kind, xs, nzcv, vs, fpcr, fpsr = gen_test(rng)
            fb.write(struct.pack('<II32s31QQ64QQQ', word, seed, bytes(kind), *xs, nzcv, *vs,
                                 fpcr, fpsr))
            fs.write(f'_t{i}:\n    stp x29, x30, [sp, #-16]!\n    bl _cosim_enter\n'
                     f'    ldr x30, [sp, #240]\n_t{i}_i:\n    .inst 0x{word:08x}\n'
                     f'    b _cosim_save1\n    b _cosim_save2\n')
        fs.write('    .data\n    .p2align 3\n    .globl _cosim_tests\n_cosim_tests:\n')
        for i in range(args.n):
            fs.write(f'    .quad _t{i}, _t{i}_i\n')


if __name__ == '__main__':
    main()
