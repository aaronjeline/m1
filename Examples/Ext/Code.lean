/-
  Machine code extracted by tools/extract.py from `ext.c`.
  Built with: clang -O2 -shared ext.c
  Compiler: Apple clang version 21.0.0 (clang-2100.4.1.1)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Ext
open M1

def textBase : BitVec 64 := 0x3f8#64

/-- `__TEXT,__text` -/
def text : List (BitVec 32) := [
  -- roll:
  0xa9bf7bfd#32, -- 0x03f8: stp x29, x30, [sp, #-0x10]!
  0x910003fd#32, -- 0x03fc: mov x29, sp
  0x9400000c#32, -- 0x0400: bl 0x430 ; symbol stub for: _rand
  0x52955568#32, -- 0x0404: mov w8, #0xaaab
  0x72a55548#32, -- 0x0408: movk w8, #0x2aaa, lsl #16
  0x9b287c08#32, -- 0x040c: smull x8, w0, w8
  0xd37ffd09#32, -- 0x0410: lsr x9, x8, #63
  0xd360fd08#32, -- 0x0414: lsr x8, x8, #32
  0x0b090108#32, -- 0x0418: add w8, w8, w9
  0x528000c9#32, -- 0x041c: mov w9, #0x6
  0x1b098108#32, -- 0x0420: msub w8, w8, w9, w0
  0x11000500#32, -- 0x0424: add w0, w8, #0x1
  0xa8c17bfd#32, -- 0x0428: ldp x29, x30, [sp], #0x10
  0xd65f03c0#32  -- 0x042c: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_roll : BitVec 64 := 0x3f8#64

/-! Entry points of external functions (calls go through `__stubs`). Their code
is not part of `prog`: specify them as hypotheses about a program extending
`prog` (see `Program.Extends`). -/
def ext_rand : BitVec 64 := 0x430#64

/-- Initialised data sections: (address, bytes). -/
def data : List (BitVec 64 × List (BitVec 8)) := [
]

/-- The data sections are loaded at their link addresses. -/
def DataLoaded (s : State) : Prop :=
  ∀ d ∈ data, ∀ i (h : i < d.2.length), s.mem (d.1 + BitVec.ofNat 64 i) = d.2[i]

end Examples.Ext
