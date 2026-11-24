/-
  Machine code extracted by tools/extract.py from `fp.c`.
  Built with: clang -O2 -shared fp.c
  Compiler: Apple clang version 21.0.0 (clang-2100.4.1.1)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.FP
open M1

def textBase : BitVec 64 := 0x310#64

/-- `__TEXT,__text` -/
def text : List (BitVec 32) := [
  -- poly:
  0x1e601001#32, -- 0x0310: fmov d1, #2.00000000
  0x1e611002#32, -- 0x0314: fmov d2, #3.00000000
  0x1f420401#32, -- 0x0318: fmadd d1, d0, d2, d1
  0x1e73d002#32, -- 0x031c: fmov d2, #-7.50000000
  0x1f400821#32, -- 0x0320: fmadd d1, d1, d0, d2
  0x1e6e1002#32, -- 0x0324: fmov d2, #1.00000000
  0x1f400820#32, -- 0x0328: fmadd d0, d1, d0, d2
  0xd65f03c0#32, -- 0x032c: ret
  -- clampf:
  0x1e222000#32, -- 0x0330: fcmp s0, s2
  0x1e20cc42#32, -- 0x0334: fcsel s2, s2, s0, gt
  0x1e212000#32, -- 0x0338: fcmp s0, s1
  0x1e224c20#32, -- 0x033c: fcsel s0, s1, s2, mi
  0xd65f03c0#32, -- 0x0340: ret
  -- to_long:
  0x9e780000#32, -- 0x0344: fcvtzs x0, d0
  0xd65f03c0#32  -- 0x0348: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_poly : BitVec 64 := 0x310#64
def sym_clampf : BitVec 64 := 0x330#64
def sym_to_long : BitVec 64 := 0x344#64

/-- Initialised data sections: (address, bytes). -/
def data : List (BitVec 64 × List (BitVec 8)) := [
]

/-- The data sections are loaded at their link addresses. -/
def DataLoaded (s : State) : Prop :=
  ∀ d ∈ data, ∀ i (h : i < d.2.length), s.mem (d.1 + BitVec.ofNat 64 i) = d.2[i]

end Examples.FP
