/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvMsn_NtCs6SjEax68zxx_5alloc4syncINtB5_3ArceE9drop_slowCsgxgKyGee4kT_14regex_automata`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.ArcStrDropSlow
open M1

def textBase : BitVec 64 := 0x2be708#64

def text : List (BitVec 32) := [
  0xaa0003e8#32, -- 0x2be708: mov x8, x0
  0xf9400000#32, -- 0x2be70c: ldr x0, [x0]
  0xb100041f#32, -- 0x2be710: cmn x0, #0x1
  0x540001a0#32, -- 0x2be714: b.eq 0x2be748 <SjEax68zxx_5alloc4syncINtB5_3ArceE9drop_slowCsgxgKyGee4kT_14regex_automata+0x40>
  0xf9400508#32, -- 0x2be718: ldr x8, [x8, #0x8]
  0x91002009#32, -- 0x2be71c: add x9, x0, #0x8
  0x9280000a#32, -- 0x2be720: mov x10, #-0x1 ; =-1
  0xf86a0129#32, -- 0x2be724: ldaddl x10, x9, [x9]
  0xf100053f#32, -- 0x2be728: cmp x9, #0x1
  0x540000e1#32, -- 0x2be72c: b.ne 0x2be748 <SjEax68zxx_5alloc4syncINtB5_3ArceE9drop_slowCsgxgKyGee4kT_14regex_automata+0x40>
  0xd50339bf#32, -- 0x2be730: dmb ishld
  0x91005d08#32, -- 0x2be734: add x8, x8, #0x17
  0xf27df101#32, -- 0x2be738: ands x1, x8, #0xfffffffffffffff8
  0x54000060#32, -- 0x2be73c: b.eq 0x2be748 <SjEax68zxx_5alloc4syncINtB5_3ArceE9drop_slowCsgxgKyGee4kT_14regex_automata+0x40>
  0x52800102#32, -- 0x2be740: mov w2, #0x8 ; =8
  0x17f5a253#32, -- 0x2be744: b 0x27090 <hJ03s5DiqP_7___rustc14___rust_dealloc>
  0xd65f03c0#32  -- 0x2be748: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x2be708#64

/-! Direct-call targets (not part of `prog`). -/
/-- `__RNvCs9hJ03s5DiqP_7___rustc14___rust_dealloc` -/
def ext_0 : BitVec 64 := 0x27090#64

end Examples.Cedar.NoPanic.Fn.ArcStrDropSlow
