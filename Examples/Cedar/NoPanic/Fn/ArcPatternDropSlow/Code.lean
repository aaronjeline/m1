/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvMsn_NtCs6SjEax68zxx_5alloc4syncINtB5_3ArcINtNtB7_3vec3VecNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast7pattern11PatternElemEE9drop_slowB12_`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.ArcPatternDropSlow
open M1

def textBase : BitVec 64 := 0x124fec#64

def text : List (BitVec 32) := [
  0xa9be4ff4#32, -- 0x124fec: stp x20, x19, [sp, #-0x20]!
  0xa9017bfd#32, -- 0x124ff0: stp x29, x30, [sp, #0x10]
  0x910043fd#32, -- 0x124ff4: add x29, sp, #0x10
  0xf9400013#32, -- 0x124ff8: ldr x19, [x0]
  0xf9400a68#32, -- 0x124ffc: ldr x8, [x19, #0x10]
  0xb40000a8#32, -- 0x125000: cbz x8, 0x125014 <SjEax68zxx_5alloc4syncINtB5_3ArcINtNtB7_3vec3VecNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast7pattern11PatternElemEE9drop_slowB12_+0x28>
  0xf9400e60#32, -- 0x125004: ldr x0, [x19, #0x18]
  0xd37ef501#32, -- 0x125008: lsl x1, x8, #2
  0x52800082#32, -- 0x12500c: mov w2, #0x4 ; =4
  0x97fc0820#32, -- 0x125010: bl 0x27090 <hJ03s5DiqP_7___rustc14___rust_dealloc>
  0xb100067f#32, -- 0x125014: cmn x19, #0x1
  0x540001a0#32, -- 0x125018: b.eq 0x12504c <SjEax68zxx_5alloc4syncINtB5_3ArcINtNtB7_3vec3VecNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast7pattern11PatternElemEE9drop_slowB12_+0x60>
  0x91002268#32, -- 0x12501c: add x8, x19, #0x8
  0x92800009#32, -- 0x125020: mov x9, #-0x1 ; =-1
  0xf8690108#32, -- 0x125024: ldaddl x9, x8, [x8]
  0xf100051f#32, -- 0x125028: cmp x8, #0x1
  0x54000101#32, -- 0x12502c: b.ne 0x12504c <SjEax68zxx_5alloc4syncINtB5_3ArcINtNtB7_3vec3VecNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast7pattern11PatternElemEE9drop_slowB12_+0x60>
  0xd50339bf#32, -- 0x125030: dmb ishld
  0xaa1303e0#32, -- 0x125034: mov x0, x19
  0x52800501#32, -- 0x125038: mov w1, #0x28 ; =40
  0x52800102#32, -- 0x12503c: mov w2, #0x8 ; =8
  0xa9417bfd#32, -- 0x125040: ldp x29, x30, [sp, #0x10]
  0xa8c24ff4#32, -- 0x125044: ldp x20, x19, [sp], #0x20
  0x17fc0812#32, -- 0x125048: b 0x27090 <hJ03s5DiqP_7___rustc14___rust_dealloc>
  0xa9417bfd#32, -- 0x12504c: ldp x29, x30, [sp, #0x10]
  0xa8c24ff4#32, -- 0x125050: ldp x20, x19, [sp], #0x20
  0xd65f03c0#32  -- 0x125054: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x124fec#64

/-! Direct-call targets (not part of `prog`). -/
/-- `__RNvCs9hJ03s5DiqP_7___rustc14___rust_dealloc` -/
def ext_0 : BitVec 64 := 0x27090#64

end Examples.Cedar.NoPanic.Fn.ArcPatternDropSlow
