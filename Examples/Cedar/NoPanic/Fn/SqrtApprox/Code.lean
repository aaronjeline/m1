/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvNtNtNtNtCskumHb0IaX0X_4core5slice4sort6stable5drift11sqrt_approx`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.SqrtApprox
open M1

def textBase : BitVec 64 := 0x3503d8#64

def text : List (BitVec 32) := [
  0xb2400008#32, -- 0x3503d8: orr x8, x0, #0x1
  0xdac01108#32, -- 0x3503dc: clz x8, x8
  0x52001508#32, -- 0x3503e0: eor w8, w8, #0x3f
  0x12000109#32, -- 0x3503e4: and w9, w8, #0x1
  0x0b480528#32, -- 0x3503e8: add w8, w9, w8, lsr #1
  0x52800029#32, -- 0x3503ec: mov w9, #0x1 ; =1
  0x9ac82129#32, -- 0x3503f0: lsl x9, x9, x8
  0x9ac82408#32, -- 0x3503f4: lsr x8, x0, x8
  0x8b080128#32, -- 0x3503f8: add x8, x9, x8
  0xd341fd00#32, -- 0x3503fc: lsr x0, x8, #1
  0xd65f03c0#32  -- 0x350400: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x3503d8#64

/-! Direct-call targets (not part of `prog`). -/


end Examples.Cedar.NoPanic.Fn.SqrtApprox
