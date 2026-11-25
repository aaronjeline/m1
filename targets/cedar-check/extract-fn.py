#!/usr/bin/env python3
"""Extract one function of the M1 cedar-check dylib into a Lean module.

    targets/cedar-check/extract-fn.py SYMBOL_SUFFIX MODULE OUT.lean [dylib]

SYMBOL_SUFFIX may also be the function's address (`0x...`), for symbols whose
names are not unique (outlined functions).

e.g. extract-fn.py 12cedar_policy3api15eval_expression Examples.Cedar.Eval.Code \
         Examples/Cedar/Eval/Code.lean

The module defines `prog` (exactly the function's instruction words, from its
symbol to the next one), `sym_fn` (its entry), and one `ext_<i>` per distinct
direct-call or tail-call target, with the callee's (mangled) name in its doc comment. The
callees' code is not part of `prog`; proofs take their contracts as
hypotheses about a program extending `prog` (see `Program.Extends`).

Needs llvm-nm-18, llvm-objdump-18 and llvm-otool-18.
"""
import os
import re
import struct
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SUFFIX, MODULE, OUT = sys.argv[1:4]
DYLIB = sys.argv[4] if len(sys.argv) > 4 else f'{HERE}/target/aarch64-apple-darwin/release/libcedar_check.dylib'


def sh(*cmd):
    return subprocess.run(cmd, check=True, capture_output=True, text=True).stdout


# (name, address) pairs: names are not unique (e.g. `_OUTLINED_FUNCTION_0`).
syms = []
for line in sh('llvm-nm-18', '-n', DYLIB).splitlines():
    parts = line.split()
    if len(parts) == 3 and parts[1] in 'Tt':
        syms.append((parts[2], int(parts[0], 16)))
if SUFFIX.startswith('0x'):
    ((name, start),) = [(n, a) for n, a in syms if a == int(SUFFIX, 16)]
else:
    ((name, start),) = [(n, a) for n, a in syms if n.endswith(SUFFIX)]
end = min(a for _, a in syms if a > start)

lc = sh('llvm-otool-18', '-l', DYLIB)
m = re.search(r'sectname __text\n\s*segname __TEXT\n\s*addr 0x([0-9a-f]+)\n\s*size 0x[0-9a-f]+\n\s*offset (\d+)', lc)
text_addr, text_off = int(m.group(1), 16), int(m.group(2))
blob = open(DYLIB, 'rb').read()
words = struct.unpack(f'<{(end - start) // 4}I',
                      blob[text_off + start - text_addr:text_off + end - text_addr])

dis, callees = {}, {}
for line in sh('llvm-objdump-18', '-d', '--no-show-raw-insn', '--mattr=+v8.5a,+lse,+rcpc,+rcpc-immo',
               f'--start-address={start}', f'--stop-address={end}', DYLIB).splitlines():
    m = re.match(r'^\s*([0-9a-f]+):\s+(.*)$', line)
    if not m:
        continue
    d = re.sub(r'\s+', ' ', m.group(2)).strip()
    # Calls (`bl`) and tail calls (`b` to another symbol's start).
    c = re.match(r'bl? 0x([0-9a-f]+) <([^>+]+)>', d)
    if c and not start <= int(c.group(1), 16) < end:
        callees.setdefault(int(c.group(1), 16), c.group(2))
    # Short names in comments: the last identifier of a mangled path.
    d = re.sub(r'<_*R\w*?\d+(\w+?)(?:\.llvm\.\d+)?(\+0x[0-9a-f]+)?>',
               lambda k: f'<{k.group(1)}{k.group(2) or ""}>', d)
    dis[int(m.group(1), 16)] = d

lines = []
for i, w in enumerate(words):
    a = start + 4 * i
    sep = ',' if i + 1 < len(words) else ' '
    lines.append(f'  0x{w:08x}#32{sep} -- 0x{a:x}: {dis.get(a, "?")}')
ext = []
for i, (a, n) in enumerate(sorted(callees.items())):
    ext.append(f'/-- `{n}` -/\ndef ext_{i} : BitVec 64 := 0x{a:x}#64')

os.makedirs(os.path.dirname(os.path.abspath(OUT)), exist_ok=True)
open(OUT, 'w').write(f'''/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `{name}`.
  Compiler: {sh("rustc", "--version").strip()}
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace {MODULE.rsplit('.', 1)[0]}
open M1

def textBase : BitVec 64 := 0x{start:x}#64

def text : List (BitVec 32) := [
{chr(10).join(lines)}
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x{start:x}#64

/-! Direct-call targets (not part of `prog`). -/
{chr(10).join(ext)}

end {MODULE.rsplit('.', 1)[0]}
''')
print(f'{name}: {len(words)} words at 0x{start:x}; {len(callees)} callees')
for i, (a, n) in enumerate(sorted(callees.items())):
    print(f'  ext_{i} = 0x{a:x}  {n[:110]}')
