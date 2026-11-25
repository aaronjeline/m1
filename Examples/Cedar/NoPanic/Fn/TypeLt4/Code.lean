/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvYNvYNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.TypeLt4
open M1

def textBase : BitVec 64 := 0x22702c#64

def text : List (BitVec 32) := [
  0xa9bc5ff8#32, -- 0x22702c: stp x24, x23, [sp, #-0x40]!
  0xa90157f6#32, -- 0x227030: stp x22, x21, [sp, #0x10]
  0xa9024ff4#32, -- 0x227034: stp x20, x19, [sp, #0x20]
  0xa9037bfd#32, -- 0x227038: stp x29, x30, [sp, #0x30]
  0x9100c3fd#32, -- 0x22703c: add x29, sp, #0x30
  0xf9400008#32, -- 0x227040: ldr x8, [x0]
  0xf9400029#32, -- 0x227044: ldr x9, [x1]
  0xeb09011f#32, -- 0x227048: cmp x8, x9
  0x54000421#32, -- 0x22704c: b.ne 0x2270d0 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xa4>
  0xf100151f#32, -- 0x227050: cmp x8, #0x5
  0x540004c0#32, -- 0x227054: b.eq 0x2270ec <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xc0>
  0xf100191f#32, -- 0x227058: cmp x8, #0x6
  0x540003a1#32, -- 0x22705c: b.ne 0x2270d0 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xa4>
  0xaa0003f4#32, -- 0x227060: mov x20, x0
  0x91002000#32, -- 0x227064: add x0, x0, #0x8
  0xaa0103f3#32, -- 0x227068: mov x19, x1
  0x91002021#32, -- 0x22706c: add x1, x1, #0x8
  0x94019fbc#32, -- 0x227070: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x12001c08#32, -- 0x227074: and w8, w0, #0xff
  0x7103f51f#32, -- 0x227078: cmp w8, #0xfd
  0x540007cc#32, -- 0x22707c: b.gt 0x227174 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x148>
  0x35000a68#32, -- 0x227080: cbnz w8, 0x2271cc <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0xf9401289#32, -- 0x227084: ldr x9, [x20, #0x20]
  0xf9401268#32, -- 0x227088: ldr x8, [x19, #0x20]
  0xf9401135#32, -- 0x22708c: ldr x21, [x9, #0x20]
  0xf9401116#32, -- 0x227090: ldr x22, [x8, #0x20]
  0xeb1502df#32, -- 0x227094: cmp x22, x21
  0x9a9532d7#32, -- 0x227098: csel x23, x22, x21, lo
  0xb40005f7#32, -- 0x22709c: cbz x23, 0x227158 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x12c>
  0xf9400d33#32, -- 0x2270a0: ldr x19, [x9, #0x18]
  0xf9400d14#32, -- 0x2270a4: ldr x20, [x8, #0x18]
  0xaa1303e0#32, -- 0x2270a8: mov x0, x19
  0xaa1403e1#32, -- 0x2270ac: mov x1, x20
  0x94019fac#32, -- 0x2270b0: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x72001c1f#32, -- 0x2270b4: tst w0, #0xff
  0x540007e1#32, -- 0x2270b8: b.ne 0x2271b4 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x188>
  0x91006294#32, -- 0x2270bc: add x20, x20, #0x18
  0x91006273#32, -- 0x2270c0: add x19, x19, #0x18
  0xf10006f7#32, -- 0x2270c4: subs x23, x23, #0x1
  0x54ffff01#32, -- 0x2270c8: b.ne 0x2270a8 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x7c>
  0x14000023#32, -- 0x2270cc: b 0x227158 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x12c>
  0xeb09011f#32, -- 0x2270d0: cmp x8, x9
  0x1a9f27e0#32, -- 0x2270d4: cset w0, lo
  0xa9437bfd#32, -- 0x2270d8: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x2270dc: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x2270e0: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x2270e4: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0x2270e8: ret
  0xaa0003f4#32, -- 0x2270ec: mov x20, x0
  0x91002000#32, -- 0x2270f0: add x0, x0, #0x8
  0xaa0103f3#32, -- 0x2270f4: mov x19, x1
  0x91002021#32, -- 0x2270f8: add x1, x1, #0x8
  0x94019f99#32, -- 0x2270fc: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x12001c08#32, -- 0x227100: and w8, w0, #0xff
  0x7103f51f#32, -- 0x227104: cmp w8, #0xfd
  0x5400046c#32, -- 0x227108: b.gt 0x227194 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x168>
  0x35000608#32, -- 0x22710c: cbnz w8, 0x2271cc <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0xf9401289#32, -- 0x227110: ldr x9, [x20, #0x20]
  0xf9401268#32, -- 0x227114: ldr x8, [x19, #0x20]
  0xf9401135#32, -- 0x227118: ldr x21, [x9, #0x20]
  0xf9401116#32, -- 0x22711c: ldr x22, [x8, #0x20]
  0xeb1502df#32, -- 0x227120: cmp x22, x21
  0x9a9532d7#32, -- 0x227124: csel x23, x22, x21, lo
  0xb4000197#32, -- 0x227128: cbz x23, 0x227158 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x12c>
  0xf9400d33#32, -- 0x22712c: ldr x19, [x9, #0x18]
  0xf9400d14#32, -- 0x227130: ldr x20, [x8, #0x18]
  0xaa1303e0#32, -- 0x227134: mov x0, x19
  0xaa1403e1#32, -- 0x227138: mov x1, x20
  0x94019f89#32, -- 0x22713c: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x72001c1f#32, -- 0x227140: tst w0, #0xff
  0x54000381#32, -- 0x227144: b.ne 0x2271b4 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x188>
  0x91006294#32, -- 0x227148: add x20, x20, #0x18
  0x91006273#32, -- 0x22714c: add x19, x19, #0x18
  0xf10006f7#32, -- 0x227150: subs x23, x23, #0x1
  0x54ffff01#32, -- 0x227154: b.ne 0x227134 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x108>
  0xeb1602bf#32, -- 0x227158: cmp x21, x22
  0x1a9f27e0#32, -- 0x22715c: cset w0, lo
  0xa9437bfd#32, -- 0x227160: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x227164: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x227168: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x22716c: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0x227170: ret
  0x7103f91f#32, -- 0x227174: cmp w8, #0xfe
  0x540002a0#32, -- 0x227178: b.eq 0x2271cc <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0x52800020#32, -- 0x22717c: mov w0, #0x1 ; =1
  0xa9437bfd#32, -- 0x227180: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x227184: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x227188: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x22718c: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0x227190: ret
  0x7103f91f#32, -- 0x227194: cmp w8, #0xfe
  0x540001a0#32, -- 0x227198: b.eq 0x2271cc <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0x52800020#32, -- 0x22719c: mov w0, #0x1 ; =1
  0xa9437bfd#32, -- 0x2271a0: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x2271a4: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x2271a8: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x2271ac: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0x2271b0: ret
  0x12001c08#32, -- 0x2271b4: and w8, w0, #0xff
  0x13001c09#32, -- 0x2271b8: sxtb w9, w0
  0x7100013f#32, -- 0x2271bc: cmp w9, #0x0
  0x1a9f57e0#32, -- 0x2271c0: cset w0, mi
  0x7103f91f#32, -- 0x2271c4: cmp w8, #0xfe
  0x54fff881#32, -- 0x2271c8: b.ne 0x2270d8 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xac>
  0x52800000#32, -- 0x2271cc: mov w0, #0x0 ; =0
  0xa9437bfd#32, -- 0x2271d0: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x2271d4: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x2271d8: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x2271dc: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32  -- 0x2271e0: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x22702c#64

/-- The addresses of the function's instructions. -/
def pcs : List (BitVec 64) := [0x22702c#64, 0x227030#64, 0x227034#64, 0x227038#64, 0x22703c#64, 0x227040#64, 0x227044#64, 0x227048#64, 0x22704c#64, 0x227050#64, 0x227054#64, 0x227058#64, 0x22705c#64, 0x227060#64, 0x227064#64, 0x227068#64, 0x22706c#64, 0x227070#64, 0x227074#64, 0x227078#64, 0x22707c#64, 0x227080#64, 0x227084#64, 0x227088#64, 0x22708c#64, 0x227090#64, 0x227094#64, 0x227098#64, 0x22709c#64, 0x2270a0#64, 0x2270a4#64, 0x2270a8#64, 0x2270ac#64, 0x2270b0#64, 0x2270b4#64, 0x2270b8#64, 0x2270bc#64, 0x2270c0#64, 0x2270c4#64, 0x2270c8#64, 0x2270cc#64, 0x2270d0#64, 0x2270d4#64, 0x2270d8#64, 0x2270dc#64, 0x2270e0#64, 0x2270e4#64, 0x2270e8#64, 0x2270ec#64, 0x2270f0#64, 0x2270f4#64, 0x2270f8#64, 0x2270fc#64, 0x227100#64, 0x227104#64, 0x227108#64, 0x22710c#64, 0x227110#64, 0x227114#64, 0x227118#64, 0x22711c#64, 0x227120#64, 0x227124#64, 0x227128#64, 0x22712c#64, 0x227130#64, 0x227134#64, 0x227138#64, 0x22713c#64, 0x227140#64, 0x227144#64, 0x227148#64, 0x22714c#64, 0x227150#64, 0x227154#64, 0x227158#64, 0x22715c#64, 0x227160#64, 0x227164#64, 0x227168#64, 0x22716c#64, 0x227170#64, 0x227174#64, 0x227178#64, 0x22717c#64, 0x227180#64, 0x227184#64, 0x227188#64, 0x22718c#64, 0x227190#64, 0x227194#64, 0x227198#64, 0x22719c#64, 0x2271a0#64, 0x2271a4#64, 0x2271a8#64, 0x2271ac#64, 0x2271b0#64, 0x2271b4#64, 0x2271b8#64, 0x2271bc#64, 0x2271c0#64, 0x2271c4#64, 0x2271c8#64, 0x2271cc#64, 0x2271d0#64, 0x2271d4#64, 0x2271d8#64, 0x2271dc#64, 0x2271e0#64]

/-! Direct-call targets (not part of `prog`). -/
/-- `__RNvXsd_CsbhszFemdqnT_8smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp` -/
def ext_0 : BitVec 64 := 0x28ef60#64

end Examples.Cedar.NoPanic.Fn.TypeLt4
