/-
  Machine code extracted by tools/extract.py from `calls.c`.
  Built with: clang -O2 -shared calls.c
  Compiler: Apple clang version 21.0.0 (clang-2100.4.1.1)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Calls
open M1

def textBase : BitVec 64 := 0x310#64

/-- `__TEXT,__text` -/
def text : List (BitVec 32) := [
  -- sq:
  0x9b007c00#32, -- 0x0310: mul x0, x0, x0
  0xd65f03c0#32, -- 0x0314: ret
  -- sumsq:
  0xa9be4ff4#32, -- 0x0318: stp x20, x19, [sp, #-0x20]!
  0xa9017bfd#32, -- 0x031c: stp x29, x30, [sp, #0x10]
  0x910043fd#32, -- 0x0320: add x29, sp, #0x10
  0xaa0103f3#32, -- 0x0324: mov x19, x1
  0x97fffffa#32, -- 0x0328: bl _sq
  0xaa0003f4#32, -- 0x032c: mov x20, x0
  0xaa1303e0#32, -- 0x0330: mov x0, x19
  0x97fffff7#32, -- 0x0334: bl _sq
  0x8b140000#32, -- 0x0338: add x0, x0, x20
  0xa9417bfd#32, -- 0x033c: ldp x29, x30, [sp, #0x10]
  0xa8c24ff4#32, -- 0x0340: ldp x20, x19, [sp], #0x20
  0xd65f03c0#32  -- 0x0344: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_sq : BitVec 64 := 0x310#64
def sym_sumsq : BitVec 64 := 0x318#64

/-- Initialised data sections: (address, bytes). -/
def data : List (BitVec 64 × List (BitVec 8)) := [
]

/-- The data sections are loaded at their link addresses. -/
def DataLoaded (s : State) : Prop :=
  ∀ d ∈ data, ∀ i (h : i < d.2.length), s.mem (d.1 + BitVec.ofNat 64 i) = d.2[i]

end Examples.Calls
