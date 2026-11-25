#!/usr/bin/env python3
"""Extract `type_soundness_violation` .. end of `verdict` from the M1 dylib into
Examples/Cedar/Code.lean (the code verified in Examples/Cedar/Proofs.lean).

    targets/cedar-check/extract-verdict.py [dylib] [out.lean]

Needs llvm-objdump and llvm-nm (LLVM 18). The range is contiguous: it starts
at `type_soundness_violation` (the `brk #0xc0de`) and ends after `verdict`,
so the assertion is part of the extracted program, not an external call.
"""
import os
import re
import struct
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DYLIB = sys.argv[1] if len(sys.argv) > 1 else f'{HERE}/target/aarch64-apple-darwin/release/libcedar_check.dylib'
OUT = sys.argv[2] if len(sys.argv) > 2 else f'{HERE}/../../Examples/Cedar/Code.lean'
NM, OBJDUMP = 'llvm-nm-18', 'llvm-objdump-18'


def sh(*cmd):
    return subprocess.run(cmd, check=True, capture_output=True, text=True).stdout


syms = {}
for line in sh(NM, '-n', DYLIB).splitlines():
    parts = line.split()
    if len(parts) == 3 and parts[1] in 'Tt':
        syms[parts[2]] = int(parts[0], 16)


def find(fragment):
    (name,) = [n for n in syms if n.endswith(fragment)]
    return name, syms[name]


brk_name, start = find('11cedar_check24type_soundness_violation')
verdict_name, verdict = find('11cedar_check7verdict')
tc_name, _ = find('11cedar_check13typechecks_in')
after = min(a for a in syms.values() if a > verdict)

# __TEXT,__text: file offset of address a is a - addr + offset.
lc = sh('llvm-otool-18', '-l', DYLIB)
m = re.search(r'sectname __text\n\s*segname __TEXT\n\s*addr 0x([0-9a-f]+)\n\s*size 0x[0-9a-f]+\n\s*offset (\d+)', lc)
text_addr, text_off = int(m.group(1), 16), int(m.group(2))
blob = open(DYLIB, 'rb').read()
words = struct.unpack(f'<{(after - start) // 4}I',
                      blob[text_off + start - text_addr:text_off + after - text_addr])

dis = {}
for line in sh(OBJDUMP, '-d', '--no-show-raw-insn', '--mattr=+v8.5a,+lse,+rcpc,+rcpc-immo',
               f'--start-address={start}', f'--stop-address={after}', DYLIB).splitlines():
    m = re.match(r'^\s*([0-9a-f]+):\s+(.*)$', line)
    if m:
        d = re.sub(r'\s+', ' ', m.group(2)).strip()
        d = re.sub(r'<__R\w*?(\d+)(verdict|typechecks_in|type_soundness_violation|eval_expression)\w*>',
                   r'<\2>', d)
        dis[int(m.group(1), 16)] = re.sub(r'<(__R\w+)>', '<…>', d)

calls = {}
for a, d in dis.items():
    m = re.match(r'bl (0x[0-9a-f]+) <(\w+)>', d)
    if m:
        calls[int(m.group(1), 16)] = m.group(2)
eval_addr = [a for a, n in calls.items() if n == 'eval_expression'][0]

labels = {start: 'type_soundness_violation', verdict: 'verdict'}
lines = []
for i, w in enumerate(words):
    a = start + 4 * i
    if a in labels:
        lines.append(f'  -- {labels[a]}:')
    sep = ',' if i + 1 < len(words) else ' '
    lines.append(f'  0x{w:08x}#32{sep} -- 0x{a:04x}: {dis.get(a, "?")}')

open(OUT, 'w').write(f'''/-
  Machine code extracted by targets/cedar-check/extract-verdict.py from the
  M1 build of targets/cedar-check (`build-m1.sh`): the contiguous range from
  `type_soundness_violation` (the assertion, `brk #0xc0de`) to the end of
  `verdict` (the only function that calls it).
  Compiler: {sh("rustc", "--version").strip()}
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar
open M1

def textBase : BitVec 64 := 0x{start:x}#64

def text : List (BitVec 32) := [
{chr(10).join(lines)}
]

abbrev prog : Program := Program.ofList textBase text

/-- `cedar_check::type_soundness_violation`: `brk #0xc0de`. -/
def sym_violation : BitVec 64 := 0x{start:x}#64
/-- `cedar_check::verdict` -/
def sym_verdict : BitVec 64 := 0x{verdict:x}#64

/-! Functions `verdict` calls. Their code is not part of `prog`: they are
specified by hypotheses about a program extending `prog`. -/
/-- `cedar_check::typechecks_in` -/
def ext_typechecks : BitVec 64 := 0x{syms[tc_name]:x}#64
/-- `cedar_policy::eval_expression` -/
def ext_eval : BitVec 64 := 0x{eval_addr:x}#64

end Examples.Cedar
''')
print(f'{len(words)} words, 0x{start:x}..0x{after:x}; verdict at 0x{verdict:x}; '
      f'typechecks_in 0x{syms[tc_name]:x}; eval_expression 0x{eval_addr:x}')
