/-
  Machine code extracted by tools/extract.py from `basic.c`.
  Built with: clang -O2 -fno-vectorize -shared basic.c
  Compiler: Apple clang version 21.0.0 (clang-2100.4.1.1)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Basic
open M1

def textBase : BitVec 64 := 0x310#64

/-- `__TEXT,__text` -/
def text : List (BitVec 32) := [
  -- max:
  0xeb01001f#32, -- 0x0310: cmp x0, x1
  0x9a81c000#32, -- 0x0314: csel x0, x0, x1, gt
  0xd65f03c0#32, -- 0x0318: ret
  -- gcd:
  0xb40000e1#32, -- 0x031c: cbz x1, 0x338
  0xaa0103e8#32, -- 0x0320: mov x8, x1
  0x9ac10809#32, -- 0x0324: udiv x9, x0, x1
  0x9b018121#32, -- 0x0328: msub x1, x9, x1, x0
  0xaa0803e0#32, -- 0x032c: mov x0, x8
  0xb5ffff81#32, -- 0x0330: cbnz x1, 0x320
  0xaa0803e0#32, -- 0x0334: mov x0, x8
  0xd65f03c0#32, -- 0x0338: ret
  -- sum:
  0xd2800008#32, -- 0x033c: mov x8, #0x0
  0xb40000a1#32, -- 0x0340: cbz x1, 0x354
  0xf8408409#32, -- 0x0344: ldr x9, [x0], #0x8
  0x8b080128#32, -- 0x0348: add x8, x9, x8
  0xf1000421#32, -- 0x034c: subs x1, x1, #0x1
  0x54ffffa1#32, -- 0x0350: b.ne 0x344
  0xaa0803e0#32, -- 0x0354: mov x0, x8
  0xd65f03c0#32  -- 0x0358: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_max : BitVec 64 := 0x310#64
def sym_gcd : BitVec 64 := 0x31c#64
def sym_sum : BitVec 64 := 0x33c#64

/-- Initialised data sections: (address, bytes). -/
def data : List (BitVec 64 × List (BitVec 8)) := [
]

/-- The data sections are loaded at their link addresses. -/
def DataLoaded (s : State) : Prop :=
  ∀ d ∈ data, ∀ i (h : i < d.2.length), s.mem (d.1 + BitVec.ofNat 64 i) = d.2[i]

end Examples.Basic
