/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvMsn_NtCs6SjEax68zxx_5alloc4syncINtB5_3ArcDNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast9extension22InternalExtensionValueEL_E9drop_slowBN_`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.ArcDynDropSlow
open M1

def textBase : BitVec 64 := 0x124d4c#64

def text : List (BitVec 32) := [
  0xa9bd57f6#32, -- 0x124d4c: stp x22, x21, [sp, #-0x30]!
  0xa9014ff4#32, -- 0x124d50: stp x20, x19, [sp, #0x10]
  0xa9027bfd#32, -- 0x124d54: stp x29, x30, [sp, #0x20]
  0x910083fd#32, -- 0x124d58: add x29, sp, #0x20
  0xa9405413#32, -- 0x124d5c: ldp x19, x21, [x0]
  0xf9400ab4#32, -- 0x124d60: ldr x20, [x21, #0x10]
  0xf94002a8#32, -- 0x124d64: ldr x8, [x21]
  0xb40000c8#32, -- 0x124d68: cbz x8, 0x124d80 <SjEax68zxx_5alloc4syncINtB5_3ArcDNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast9extension22InternalExtensionValueEL_E9drop_slowBN_+0x34>
  0xd1000689#32, -- 0x124d6c: sub x9, x20, #0x1
  0x927ced29#32, -- 0x124d70: and x9, x9, #0xfffffffffffffff0
  0x8b090269#32, -- 0x124d74: add x9, x19, x9
  0x91004120#32, -- 0x124d78: add x0, x9, #0x10
  0xd63f0100#32, -- 0x124d7c: blr x8
  0xb100067f#32, -- 0x124d80: cmn x19, #0x1
  0x540002a0#32, -- 0x124d84: b.eq 0x124dd8 <SjEax68zxx_5alloc4syncINtB5_3ArcDNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast9extension22InternalExtensionValueEL_E9drop_slowBN_+0x8c>
  0x91002268#32, -- 0x124d88: add x8, x19, #0x8
  0x92800009#32, -- 0x124d8c: mov x9, #-0x1 ; =-1
  0xf8690108#32, -- 0x124d90: ldaddl x9, x8, [x8]
  0xf100051f#32, -- 0x124d94: cmp x8, #0x1
  0x54000201#32, -- 0x124d98: b.ne 0x124dd8 <SjEax68zxx_5alloc4syncINtB5_3ArcDNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast9extension22InternalExtensionValueEL_E9drop_slowBN_+0x8c>
  0xd50339bf#32, -- 0x124d9c: dmb ishld
  0xf94006a8#32, -- 0x124da0: ldr x8, [x21, #0x8]
  0x52800109#32, -- 0x124da4: mov w9, #0x8 ; =8
  0xf100229f#32, -- 0x124da8: cmp x20, #0x8
  0x9a898282#32, -- 0x124dac: csel x2, x20, x9, hi
  0x8b080048#32, -- 0x124db0: add x8, x2, x8
  0x91003d08#32, -- 0x124db4: add x8, x8, #0xf
  0xcb0203e9#32, -- 0x124db8: neg x9, x2
  0xea090101#32, -- 0x124dbc: ands x1, x8, x9
  0x540000c0#32, -- 0x124dc0: b.eq 0x124dd8 <SjEax68zxx_5alloc4syncINtB5_3ArcDNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast9extension22InternalExtensionValueEL_E9drop_slowBN_+0x8c>
  0xaa1303e0#32, -- 0x124dc4: mov x0, x19
  0xa9427bfd#32, -- 0x124dc8: ldp x29, x30, [sp, #0x20]
  0xa9414ff4#32, -- 0x124dcc: ldp x20, x19, [sp, #0x10]
  0xa8c357f6#32, -- 0x124dd0: ldp x22, x21, [sp], #0x30
  0x17fc08af#32, -- 0x124dd4: b 0x27090 <hJ03s5DiqP_7___rustc14___rust_dealloc>
  0xa9427bfd#32, -- 0x124dd8: ldp x29, x30, [sp, #0x20]
  0xa9414ff4#32, -- 0x124ddc: ldp x20, x19, [sp, #0x10]
  0xa8c357f6#32, -- 0x124de0: ldp x22, x21, [sp], #0x30
  0xd65f03c0#32  -- 0x124de4: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x124d4c#64

/-! Direct-call targets (not part of `prog`). -/
/-- `__RNvCs9hJ03s5DiqP_7___rustc14___rust_dealloc` -/
def ext_0 : BitVec 64 := 0x27090#64

end Examples.Cedar.NoPanic.Fn.ArcDynDropSlow
