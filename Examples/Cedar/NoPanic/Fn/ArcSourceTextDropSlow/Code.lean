/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvMsn_NtCs6SjEax68zxx_5alloc4syncINtB5_3ArcNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core6parser3loc15SourceTextInnerE9drop_slowBM_`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.ArcSourceTextDropSlow
open M1

def textBase : BitVec 64 := 0x1259c8#64

def text : List (BitVec 32) := [
  0xa9be4ff4#32, -- 0x1259c8: stp x20, x19, [sp, #-0x20]!
  0xa9017bfd#32, -- 0x1259cc: stp x29, x30, [sp, #0x10]
  0x910043fd#32, -- 0x1259d0: add x29, sp, #0x10
  0xf9400013#32, -- 0x1259d4: ldr x19, [x0]
  0xf9400e61#32, -- 0x1259d8: ldr x1, [x19, #0x18]
  0xb4000081#32, -- 0x1259dc: cbz x1, 0x1259ec <SjEax68zxx_5alloc4syncINtB5_3ArcNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core6parser3loc15SourceTextInnerE9drop_slowBM_+0x24>
  0xf9400a60#32, -- 0x1259e0: ldr x0, [x19, #0x10]
  0x52800022#32, -- 0x1259e4: mov w2, #0x1 ; =1
  0x97fc05aa#32, -- 0x1259e8: bl 0x27090 <hJ03s5DiqP_7___rustc14___rust_dealloc>
  0xb100067f#32, -- 0x1259ec: cmn x19, #0x1
  0x540001a0#32, -- 0x1259f0: b.eq 0x125a24 <SjEax68zxx_5alloc4syncINtB5_3ArcNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core6parser3loc15SourceTextInnerE9drop_slowBM_+0x5c>
  0x91002268#32, -- 0x1259f4: add x8, x19, #0x8
  0x92800009#32, -- 0x1259f8: mov x9, #-0x1 ; =-1
  0xf8690108#32, -- 0x1259fc: ldaddl x9, x8, [x8]
  0xf100051f#32, -- 0x125a00: cmp x8, #0x1
  0x54000101#32, -- 0x125a04: b.ne 0x125a24 <SjEax68zxx_5alloc4syncINtB5_3ArcNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core6parser3loc15SourceTextInnerE9drop_slowBM_+0x5c>
  0xd50339bf#32, -- 0x125a08: dmb ishld
  0xaa1303e0#32, -- 0x125a0c: mov x0, x19
  0x52800501#32, -- 0x125a10: mov w1, #0x28 ; =40
  0x52800102#32, -- 0x125a14: mov w2, #0x8 ; =8
  0xa9417bfd#32, -- 0x125a18: ldp x29, x30, [sp, #0x10]
  0xa8c24ff4#32, -- 0x125a1c: ldp x20, x19, [sp], #0x20
  0x17fc059c#32, -- 0x125a20: b 0x27090 <hJ03s5DiqP_7___rustc14___rust_dealloc>
  0xa9417bfd#32, -- 0x125a24: ldp x29, x30, [sp, #0x10]
  0xa8c24ff4#32, -- 0x125a28: ldp x20, x19, [sp], #0x20
  0xd65f03c0#32  -- 0x125a2c: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x1259c8#64

/-! Direct-call targets (not part of `prog`). -/
/-- `__RNvCs9hJ03s5DiqP_7___rustc14___rust_dealloc` -/
def ext_0 : BitVec 64 := 0x27090#64

end Examples.Cedar.NoPanic.Fn.ArcSourceTextDropSlow
