#!/usr/bin/env python3
"""Whole-function co-simulation.

Compiles C files into a dylib, calls its functions natively on this machine
with random arguments and buffers, and runs the same machine code from the
same initial state in the Lean model (`m1 funsim`), comparing the returned
registers (x0, x1, q0, q1) and the contents of every buffer.

    tools/funsim/run.py [-n TESTS_PER_FUNCTION] [--seed S] [--cflags=...] files.c...

Function signatures come from SIGS below (or `// sig: name kinds` comments in
the sources). Kinds, in argument order:
  p  pointer to the next buffer       n  small count (0..20)
  i  random 64-bit integer            s  small signed integer (-3..9)
  d  double                           f  float
"""
import argparse
import os
import random
import re
import struct
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'tools'))
from extract import sections  # noqa: E402

SIGS = {
    # tools/corpus/loops.c
    'sum64': 'pn', 'sum32': 'pn', 'sum8': 'pn', 'add_arrays': 'pppn', 'scale': 'pin',
    'max_arr': 'pn', 'count_eq': 'pni', 'memset_u8': 'pin', 'copy_u32': 'ppn',
    'reverse': 'pn', 'my_strlen': 'p', 'my_strcmp': 'pp', 'fnv1a': 'pn',
    'popcount_arr': 'pn', 'to_upper': 'pn', 'dot': 'ppn', 'widen': 'ppn', 'narrow': 'ppn',
    'shift_arr': 'pn', 'abs_arr': 'pn', 'clamp': 'pn', 'insertion_sort': 'pn',
    'bsearch_idx': 'pni', 'switch_fn': 's', 'mix': 'i', 'bswap_sum': 'pn',
    'histogram': 'ppn', 'matmul_trace': 'ppn', 'prefix_sum': 'pn', 'all_zero': 'pn',
    'min_u8': 'pn',
    # tools/corpus/fp.c
    'dsum': 'pn', 'fdot': 'ppn', 'saxpy': 'ppfn', 'daxpy': 'ppdn', 'poly': 'd', 'mean': 'pn',
    'dmax': 'pn', 'fclamp': 'fff', 'to_long': 'd', 'round_int': 'd', 'floor_d': 'd',
    'hyp': 'dd', 'scale_f': 'pfn', 'int_to_float': 'ppn', 'float_to_int': 'ppn',
    'd2f': 'ppn', 'fabs_arr': 'pn', 'count_pos': 'pn', 'relu': 'pn', 'horner': 'pnd',
    'matvec': 'pppn', 'norm2': 'pn', 'lerp': 'pppfn', 'fminv': 'pn', 'div_arr': 'ppn',
    'sqrt_arr': 'pn', 'neg_arr': 'pn', 'u2d': 'ppn',
    # Examples/C
    'max': 'ii', 'gcd': 'ii', 'sum': 'pn', 'sq': 'i', 'sumsq': 'ii', 'clampf': 'fff',
}

SPECIAL_D = [0.0, -0.0, 1.0, -1.0, 0.5, 1e308, -1e308, 5e-324, 2.2250738585072014e-308,
             float('inf'), float('-inf'), 9.2e18, -9.3e18, 2.5, 3.5, -2.5]


def dbits(v):
    return struct.unpack('<Q', struct.pack('<d', v))[0]


def fbits(v):
    return struct.unpack('<I', struct.pack('<f', v))[0]


def rand_double(rng):
    r = rng.random()
    if r < 0.2:
        return dbits(rng.choice(SPECIAL_D))
    if r < 0.25:
        return 0x7FF8000000000000 | rng.getrandbits(51)  # NaNs
    if r < 0.9:
        return dbits(rng.uniform(-1000, 1000))
    return rng.getrandbits(64)


def rand_float(rng):
    r = rng.random()
    if r < 0.2:
        v = rng.choice(SPECIAL_D)
        try:
            return fbits(v)
        except OverflowError:
            return fbits(float('inf') if v > 0 else float('-inf'))
    if r < 0.25:
        return 0x7FC00000 | rng.getrandbits(22)
    if r < 0.9:
        return fbits(rng.uniform(-1000, 1000))
    return rng.getrandbits(32)


def gen_args(rng, kinds):
    xs, ds, nbuf = [], [], 0
    for k in kinds:
        if k == 'p':
            xs.append(f'@{nbuf}+{rng.choice([0, 0, 0, 8, 16, 64]):x}')
            nbuf += 1
        elif k == 'n':
            xs.append(f'{rng.randrange(0, 21):x}')
        elif k == 'i':
            xs.append(f'{rng.getrandbits(64) if rng.random() < 0.7 else rng.randrange(0, 300):x}')
        elif k == 's':
            xs.append(f'{rng.randrange(-3, 10) & (2**64 - 1):x}')
        elif k == 'd':
            ds.append(f'{rand_double(rng):x}')
        elif k == 'f':
            ds.append(f'{rand_float(rng):x}')
    xs += [f'{rng.getrandbits(64):x}' for _ in range(8 - len(xs))]
    ds += [f'{rng.getrandbits(64):x}' for _ in range(8 - len(ds))]
    return xs, ds


def dump_image(image, out):
    """TEXT <base> <words...> and DATA <addr> <hex bytes> lines for the model."""
    secs = sections(image)
    blob = open(image, 'rb').read()
    base, size, off = secs[('__TEXT', '__text')]
    words = struct.unpack(f'<{size // 4}I', blob[off:off + size])
    with open(out, 'w') as f:
        f.write(f'TEXT {base:x} ' + ' '.join(f'{w:x}' for w in words) + '\n')
        for (seg, sect), (a, sz, o) in secs.items():
            if seg == '__TEXT' and sect != '__text' and sect not in ('__stubs', '__unwind_info',
                                                                      '__eh_frame') and sz:
                f.write(f'DATA {a:x} ' + blob[o:o + sz].hex() + '\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('files', nargs='+')
    ap.add_argument('-n', type=int, default=50)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--cflags', default='-O2')
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    out = args.out or tempfile.mkdtemp()
    os.makedirs(out, exist_ok=True)
    image = os.path.join(out, 'image.dylib')
    subprocess.run(['clang', '-arch', 'arm64', '-shared', '-o', image] + args.files +
                   args.cflags.split(), check=True)
    harness = os.path.join(out, 'harness')
    subprocess.run(['clang', '-O1', '-o', harness, os.path.join(HERE, 'harness.c'),
                    os.path.join(HERE, 'call.s')], check=True)
    sigs = dict(SIGS)
    for path in args.files:
        for m in re.finditer(r'//\s*sig:\s*(\w+)\s+(\w+)', open(path).read()):
            sigs[m.group(1)] = m.group(2)
    nm = subprocess.run(['nm', '-g', '--defined-only', image], capture_output=True,
                        text=True, check=True).stdout
    funcs = [l.split()[2].lstrip('_') for l in nm.splitlines() if l.split()[1] == 'T']
    rng = random.Random(args.seed)
    tests = os.path.join(out, 'tests.txt')
    skipped = [f for f in funcs if f not in sigs]
    with open(tests, 'w') as f:
        for fn in funcs:
            if fn not in sigs:
                continue
            for _ in range(args.n):
                xs, ds = gen_args(rng, sigs[fn])
                f.write(f'{fn} {rng.getrandbits(32):x} ' + ' '.join(xs + ds) + '\n')
    if skipped:
        print('no signature (skipped):', ' '.join(skipped))
    hw = os.path.join(out, 'hw.txt')
    with open(hw, 'w') as f:
        subprocess.run([harness, image, tests], stdout=f, check=True)
    imgtxt = os.path.join(out, 'image.txt')
    dump_image(image, imgtxt)
    subprocess.run(['lake', 'build', 'm1'], cwd=ROOT, check=True, capture_output=True)
    r = subprocess.run([os.path.join(ROOT, '.lake/build/bin/m1'), 'funsim', imgtxt, hw], cwd=ROOT)
    sys.exit(r.returncode)


if __name__ == '__main__':
    main()
