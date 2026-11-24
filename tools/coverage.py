#!/usr/bin/env python3
"""Measure how much of a real arm64 Mach-O binary's code the model decodes.

    tools/coverage.py /opt/homebrew/lib/libz.dylib [more images...]

Prints the fraction of instructions in __TEXT,__text that decode, and the most
common mnemonics that do not.
"""
import collections
import os
import re
import struct
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(__file__))
from extract import sections  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def main():
    total, ok = 0, 0
    missing = collections.Counter()
    examples = {}
    for image in sys.argv[1:]:
        secs = sections(image)
        if ('__TEXT', '__text') not in secs:
            continue
        base, size, off = secs[('__TEXT', '__text')]
        blob = open(image, 'rb').read()[off:off + size]
        words = struct.unpack(f'<{size // 4}I', blob[:size // 4 * 4])
        dis = {}
        out = subprocess.run(['otool', '-tv', image], capture_output=True, text=True).stdout
        for line in out.splitlines():
            m = re.match(r'^([0-9a-f]{16})\s+(\S+)\s*(.*)$', line)
            if m:
                dis[int(m.group(1), 16)] = (m.group(2), m.group(3))
        with tempfile.NamedTemporaryFile('w', delete=False) as f:
            f.write('\n'.join(f'{w:x}' for w in words) + '\n')
        res = subprocess.run([os.path.join(ROOT, '.lake/build/bin/m1'), 'decode', f.name],
                             capture_output=True, text=True, check=True).stdout.split()
        os.unlink(f.name)
        for i, (w, r) in enumerate(zip(words, res)):
            a = base + 4 * i
            mn = dis.get(a, ('?', ''))[0]
            if mn in ('?',) or mn.startswith('.'):
                continue  # data in code
            total += 1
            if r == '1':
                ok += 1
            else:
                missing[mn] += 1
                examples.setdefault(mn, f'{w:08x}  {mn} {dis[a][1]}')
    print(f'instructions: {total}  decoded: {ok} ({100 * ok / max(total, 1):.2f}%)')
    print('most common unsupported mnemonics:')
    for mn, c in missing.most_common(60):
        print(f'  {c:7d} ({100 * c / max(total, 1):5.2f}%)  {examples[mn]}')


if __name__ == '__main__':
    main()
