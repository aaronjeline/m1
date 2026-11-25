/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvYNvYNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.TypeLt
open M1

def textBase : BitVec 64 := 0xe0cc0#64

def text : List (BitVec 32) := [
  0xa9bc5ff8#32, -- 0xe0cc0: stp x24, x23, [sp, #-0x40]!
  0xa90157f6#32, -- 0xe0cc4: stp x22, x21, [sp, #0x10]
  0xa9024ff4#32, -- 0xe0cc8: stp x20, x19, [sp, #0x20]
  0xa9037bfd#32, -- 0xe0ccc: stp x29, x30, [sp, #0x30]
  0x9100c3fd#32, -- 0xe0cd0: add x29, sp, #0x30
  0xf9400008#32, -- 0xe0cd4: ldr x8, [x0]
  0xf9400029#32, -- 0xe0cd8: ldr x9, [x1]
  0xeb09011f#32, -- 0xe0cdc: cmp x8, x9
  0x54000421#32, -- 0xe0ce0: b.ne 0xe0d64 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xa4>
  0xf100151f#32, -- 0xe0ce4: cmp x8, #0x5
  0x540004c0#32, -- 0xe0ce8: b.eq 0xe0d80 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xc0>
  0xf100191f#32, -- 0xe0cec: cmp x8, #0x6
  0x540003a1#32, -- 0xe0cf0: b.ne 0xe0d64 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xa4>
  0xaa0003f4#32, -- 0xe0cf4: mov x20, x0
  0x91002000#32, -- 0xe0cf8: add x0, x0, #0x8
  0xaa0103f3#32, -- 0xe0cfc: mov x19, x1
  0x91002021#32, -- 0xe0d00: add x1, x1, #0x8
  0x9406b897#32, -- 0xe0d04: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x12001c08#32, -- 0xe0d08: and w8, w0, #0xff
  0x7103f51f#32, -- 0xe0d0c: cmp w8, #0xfd
  0x540007cc#32, -- 0xe0d10: b.gt 0xe0e08 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x148>
  0x35000a68#32, -- 0xe0d14: cbnz w8, 0xe0e60 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0xf9401289#32, -- 0xe0d18: ldr x9, [x20, #0x20]
  0xf9401268#32, -- 0xe0d1c: ldr x8, [x19, #0x20]
  0xf9401135#32, -- 0xe0d20: ldr x21, [x9, #0x20]
  0xf9401116#32, -- 0xe0d24: ldr x22, [x8, #0x20]
  0xeb1502df#32, -- 0xe0d28: cmp x22, x21
  0x9a9532d7#32, -- 0xe0d2c: csel x23, x22, x21, lo
  0xb40005f7#32, -- 0xe0d30: cbz x23, 0xe0dec <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x12c>
  0xf9400d33#32, -- 0xe0d34: ldr x19, [x9, #0x18]
  0xf9400d14#32, -- 0xe0d38: ldr x20, [x8, #0x18]
  0xaa1303e0#32, -- 0xe0d3c: mov x0, x19
  0xaa1403e1#32, -- 0xe0d40: mov x1, x20
  0x9406b887#32, -- 0xe0d44: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x72001c1f#32, -- 0xe0d48: tst w0, #0xff
  0x540007e1#32, -- 0xe0d4c: b.ne 0xe0e48 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x188>
  0x91006294#32, -- 0xe0d50: add x20, x20, #0x18
  0x91006273#32, -- 0xe0d54: add x19, x19, #0x18
  0xf10006f7#32, -- 0xe0d58: subs x23, x23, #0x1
  0x54ffff01#32, -- 0xe0d5c: b.ne 0xe0d3c <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x7c>
  0x14000023#32, -- 0xe0d60: b 0xe0dec <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x12c>
  0xeb09011f#32, -- 0xe0d64: cmp x8, x9
  0x1a9f27e0#32, -- 0xe0d68: cset w0, lo
  0xa9437bfd#32, -- 0xe0d6c: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0xe0d70: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0xe0d74: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0xe0d78: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0xe0d7c: ret
  0xaa0003f4#32, -- 0xe0d80: mov x20, x0
  0x91002000#32, -- 0xe0d84: add x0, x0, #0x8
  0xaa0103f3#32, -- 0xe0d88: mov x19, x1
  0x91002021#32, -- 0xe0d8c: add x1, x1, #0x8
  0x9406b874#32, -- 0xe0d90: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x12001c08#32, -- 0xe0d94: and w8, w0, #0xff
  0x7103f51f#32, -- 0xe0d98: cmp w8, #0xfd
  0x5400046c#32, -- 0xe0d9c: b.gt 0xe0e28 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x168>
  0x35000608#32, -- 0xe0da0: cbnz w8, 0xe0e60 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0xf9401289#32, -- 0xe0da4: ldr x9, [x20, #0x20]
  0xf9401268#32, -- 0xe0da8: ldr x8, [x19, #0x20]
  0xf9401135#32, -- 0xe0dac: ldr x21, [x9, #0x20]
  0xf9401116#32, -- 0xe0db0: ldr x22, [x8, #0x20]
  0xeb1502df#32, -- 0xe0db4: cmp x22, x21
  0x9a9532d7#32, -- 0xe0db8: csel x23, x22, x21, lo
  0xb4000197#32, -- 0xe0dbc: cbz x23, 0xe0dec <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x12c>
  0xf9400d33#32, -- 0xe0dc0: ldr x19, [x9, #0x18]
  0xf9400d14#32, -- 0xe0dc4: ldr x20, [x8, #0x18]
  0xaa1303e0#32, -- 0xe0dc8: mov x0, x19
  0xaa1403e1#32, -- 0xe0dcc: mov x1, x20
  0x9406b864#32, -- 0xe0dd0: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x72001c1f#32, -- 0xe0dd4: tst w0, #0xff
  0x54000381#32, -- 0xe0dd8: b.ne 0xe0e48 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x188>
  0x91006294#32, -- 0xe0ddc: add x20, x20, #0x18
  0x91006273#32, -- 0xe0de0: add x19, x19, #0x18
  0xf10006f7#32, -- 0xe0de4: subs x23, x23, #0x1
  0x54ffff01#32, -- 0xe0de8: b.ne 0xe0dc8 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x108>
  0xeb1602bf#32, -- 0xe0dec: cmp x21, x22
  0x1a9f27e0#32, -- 0xe0df0: cset w0, lo
  0xa9437bfd#32, -- 0xe0df4: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0xe0df8: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0xe0dfc: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0xe0e00: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0xe0e04: ret
  0x7103f91f#32, -- 0xe0e08: cmp w8, #0xfe
  0x540002a0#32, -- 0xe0e0c: b.eq 0xe0e60 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0x52800020#32, -- 0xe0e10: mov w0, #0x1 ; =1
  0xa9437bfd#32, -- 0xe0e14: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0xe0e18: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0xe0e1c: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0xe0e20: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0xe0e24: ret
  0x7103f91f#32, -- 0xe0e28: cmp w8, #0xfe
  0x540001a0#32, -- 0xe0e2c: b.eq 0xe0e60 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0x52800020#32, -- 0xe0e30: mov w0, #0x1 ; =1
  0xa9437bfd#32, -- 0xe0e34: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0xe0e38: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0xe0e3c: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0xe0e40: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0xe0e44: ret
  0x12001c08#32, -- 0xe0e48: and w8, w0, #0xff
  0x13001c09#32, -- 0xe0e4c: sxtb w9, w0
  0x7100013f#32, -- 0xe0e50: cmp w9, #0x0
  0x1a9f57e0#32, -- 0xe0e54: cset w0, mi
  0x7103f91f#32, -- 0xe0e58: cmp w8, #0xfe
  0x54fff881#32, -- 0xe0e5c: b.ne 0xe0d6c <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xac>
  0x52800000#32, -- 0xe0e60: mov w0, #0x0 ; =0
  0xa9437bfd#32, -- 0xe0e64: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0xe0e68: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0xe0e6c: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0xe0e70: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32  -- 0xe0e74: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0xe0cc0#64

/-- The addresses of the function's instructions. -/
def pcs : List (BitVec 64) := [0xe0cc0#64, 0xe0cc4#64, 0xe0cc8#64, 0xe0ccc#64, 0xe0cd0#64, 0xe0cd4#64, 0xe0cd8#64, 0xe0cdc#64, 0xe0ce0#64, 0xe0ce4#64, 0xe0ce8#64, 0xe0cec#64, 0xe0cf0#64, 0xe0cf4#64, 0xe0cf8#64, 0xe0cfc#64, 0xe0d00#64, 0xe0d04#64, 0xe0d08#64, 0xe0d0c#64, 0xe0d10#64, 0xe0d14#64, 0xe0d18#64, 0xe0d1c#64, 0xe0d20#64, 0xe0d24#64, 0xe0d28#64, 0xe0d2c#64, 0xe0d30#64, 0xe0d34#64, 0xe0d38#64, 0xe0d3c#64, 0xe0d40#64, 0xe0d44#64, 0xe0d48#64, 0xe0d4c#64, 0xe0d50#64, 0xe0d54#64, 0xe0d58#64, 0xe0d5c#64, 0xe0d60#64, 0xe0d64#64, 0xe0d68#64, 0xe0d6c#64, 0xe0d70#64, 0xe0d74#64, 0xe0d78#64, 0xe0d7c#64, 0xe0d80#64, 0xe0d84#64, 0xe0d88#64, 0xe0d8c#64, 0xe0d90#64, 0xe0d94#64, 0xe0d98#64, 0xe0d9c#64, 0xe0da0#64, 0xe0da4#64, 0xe0da8#64, 0xe0dac#64, 0xe0db0#64, 0xe0db4#64, 0xe0db8#64, 0xe0dbc#64, 0xe0dc0#64, 0xe0dc4#64, 0xe0dc8#64, 0xe0dcc#64, 0xe0dd0#64, 0xe0dd4#64, 0xe0dd8#64, 0xe0ddc#64, 0xe0de0#64, 0xe0de4#64, 0xe0de8#64, 0xe0dec#64, 0xe0df0#64, 0xe0df4#64, 0xe0df8#64, 0xe0dfc#64, 0xe0e00#64, 0xe0e04#64, 0xe0e08#64, 0xe0e0c#64, 0xe0e10#64, 0xe0e14#64, 0xe0e18#64, 0xe0e1c#64, 0xe0e20#64, 0xe0e24#64, 0xe0e28#64, 0xe0e2c#64, 0xe0e30#64, 0xe0e34#64, 0xe0e38#64, 0xe0e3c#64, 0xe0e40#64, 0xe0e44#64, 0xe0e48#64, 0xe0e4c#64, 0xe0e50#64, 0xe0e54#64, 0xe0e58#64, 0xe0e5c#64, 0xe0e60#64, 0xe0e64#64, 0xe0e68#64, 0xe0e6c#64, 0xe0e70#64, 0xe0e74#64]

/-! Direct-call targets (not part of `prog`). -/
/-- `__RNvXsd_CsbhszFemdqnT_8smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp` -/
def ext_0 : BitVec 64 := 0x28ef60#64

end Examples.Cedar.NoPanic.Fn.TypeLt
