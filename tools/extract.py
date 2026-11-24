#!/usr/bin/env python3
"""Extract machine code from an arm64 Mach-O image into a Lean module.

    tools/extract.py foo.c   --module Examples.Foo --out Examples/Foo/Code.lean [--cflags "-O2"]
    tools/extract.py foo.dylib --module Examples.Foo --out ...

A C source is first compiled and linked into a dylib (so that intra-image
branches and PC-relative references are resolved). The generated module
contains

  * `text`      : the words of `__TEXT,__text`, each annotated with its
                  disassembly;
  * `textBase`  : the load address of the first word;
  * `prog`      : the `M1.Program` for the image;
  * `sym_<f>`   : the address of every exported function;
  * `data`      : the bytes of the data sections, with their addresses, and
                  `DataLoaded s`, the hypothesis that they are in memory.
"""
import argparse
import os
import re
import struct
import subprocess

import tempfile

DATA_SECTIONS = [('__TEXT', '__const'), ('__TEXT', '__cstring'), ('__TEXT', '__literal4'),
                 ('__TEXT', '__literal8'), ('__TEXT', '__literal16'),
                 ('__DATA', '__data'), ('__DATA_CONST', '__const'), ('__DATA', '__const')]


def sh(*cmd):
    return subprocess.run(cmd, check=True, capture_output=True, text=True).stdout


def sections(path):
    out = sh('otool', '-l', path)
    secs = {}
    cur = None
    for line in out.splitlines():
        line = line.strip()
        if line.startswith('sectname'):
            cur = {'sect': line.split()[1]}
        elif cur is not None:
            k, *v = line.split()
            if k in ('segname', 'addr', 'size', 'offset'):
                cur[k] = v[0]
            if k == 'offset':
                secs[(cur['segname'], cur['sect'])] = (int(cur['addr'], 16), int(cur['size'], 16),
                                                     int(cur['offset']))
                cur = None
    return secs


def disasm(path):
    out = sh('otool', '-tvV', path)
    res = {}
    for line in out.splitlines():
        m = re.match(r'^([0-9a-f]{16})\s+(.*)$', line)
        if m:
            res[int(m.group(1), 16)] = re.sub(r'\s+', ' ', m.group(2)).strip()
    return res


def symbols(path):
    res = []
    for line in sh('nm', '-n', '-g', '--defined-only', path).splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[1] in 'Tt':
            res.append((parts[2].lstrip('_'), int(parts[0], 16)))
    return res


def stubs(path):
    """(name, address) of each `__TEXT,__stubs` entry: calls to external functions."""
    res = []
    cur = None
    for line in sh('otool', '-Iv', path).splitlines():
        if line.startswith('Indirect symbols for'):
            cur = '(__TEXT,__stubs)' in line
        elif cur:
            m = re.match(r'^0x([0-9a-f]+)\s+\d+\s+(\S+)$', line.strip())
            if m:
                res.append((m.group(2).lstrip('_'), int(m.group(1), 16)))
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('input')
    ap.add_argument('--module', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--cflags', default='-O2')
    args = ap.parse_args()

    src = args.input
    tmp = tempfile.mkdtemp()
    if src.endswith('.c'):
        image = os.path.join(tmp, 'image.dylib')
        cmd = ['clang', '-arch', 'arm64', '-shared', '-o', image, src] + args.cflags.split()
        subprocess.run(cmd, check=True)
        how = ' '.join(['clang'] + args.cflags.split() + ['-shared', os.path.basename(src)])
        clang = sh('clang', '--version').splitlines()[0]
    else:
        image, how, clang = src, os.path.basename(src), ''

    blob = open(image, 'rb').read()
    secs = sections(image)
    base, size, off = secs[('__TEXT', '__text')]
    words = struct.unpack(f'<{size // 4}I', blob[off:off + size])
    dis = disasm(image)
    syms = symbols(image)

    ns = args.module
    L = []
    L.append(f'/-\n  Machine code extracted by tools/extract.py from `{os.path.basename(src)}`.')
    L.append(f'  Built with: {how}')
    if clang:
        L.append(f'  Compiler: {clang}')
    L.append('  DO NOT EDIT: regenerate instead.\n-/')
    L.append('import M1\n')
    L.append(f'namespace {ns}\nopen M1\n')
    L.append(f'def textBase : BitVec 64 := 0x{base:x}#64\n')
    L.append('/-- `__TEXT,__text` -/')
    L.append('def text : List (BitVec 32) := [')
    names = {a: n for n, a in syms}
    for i, w in enumerate(words):
        a = base + 4 * i
        if a in names:
            L.append(f'  -- {names[a]}:')
        sep = ',' if i + 1 < len(words) else ' '
        L.append(f'  0x{w:08x}#32{sep} -- {a:#06x}: {dis.get(a, "")}')
    L.append(']\n')
    L.append('abbrev prog : Program := Program.ofList textBase text\n')
    for n, a in syms:
        if base <= a < base + size:
            L.append(f'def sym_{n} : BitVec 64 := 0x{a:x}#64')
    ext = stubs(image)
    if ext:
        L.append('\n/-! Entry points of external functions (calls go through `__stubs`). Their code')
        L.append('is not part of `prog`: specify them as hypotheses about a program extending')
        L.append('`prog` (see `Program.Extends`). -/')
        for n, a in ext:
            L.append(f'def ext_{n} : BitVec 64 := 0x{a:x}#64')
    L.append('')
    data = []
    for key in DATA_SECTIONS:
        if key in secs:
            a, sz, o = secs[key]
            if sz:
                data.append((key, a, blob[o:o + sz]))
    L.append('/-- Initialised data sections: (address, bytes). -/')
    L.append('def data : List (BitVec 64 × List (BitVec 8)) := [')
    for j, (key, a, bs) in enumerate(data):
        body = ', '.join(f'0x{b:02x}' for b in bs)
        sep = ',' if j + 1 < len(data) else ''
        L.append(f'  -- {key[0]},{key[1]}')
        L.append(f'  (0x{a:x}#64, [{body}]){sep}')
    L.append(']\n')
    L.append('/-- The data sections are loaded at their link addresses. -/')
    L.append('def DataLoaded (s : State) : Prop :=')
    L.append('  ∀ d ∈ data, ∀ i (h : i < d.2.length), s.mem (d.1 + BitVec.ofNat 64 i) = d.2[i]\n')
    L.append(f'end {ns}')
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, 'w') as f:
        f.write('\n'.join(L) + '\n')


if __name__ == '__main__':
    main()
