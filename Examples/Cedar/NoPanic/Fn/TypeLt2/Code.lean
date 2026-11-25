/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvYNvYNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.TypeLt2
open M1

def textBase : BitVec 64 := 0x23d694#64

def text : List (BitVec 32) := [
  0xa9bc5ff8#32, -- 0x23d694: stp x24, x23, [sp, #-0x40]!
  0xa90157f6#32, -- 0x23d698: stp x22, x21, [sp, #0x10]
  0xa9024ff4#32, -- 0x23d69c: stp x20, x19, [sp, #0x20]
  0xa9037bfd#32, -- 0x23d6a0: stp x29, x30, [sp, #0x30]
  0x9100c3fd#32, -- 0x23d6a4: add x29, sp, #0x30
  0xf9400008#32, -- 0x23d6a8: ldr x8, [x0]
  0xf9400029#32, -- 0x23d6ac: ldr x9, [x1]
  0xeb09011f#32, -- 0x23d6b0: cmp x8, x9
  0x54000421#32, -- 0x23d6b4: b.ne 0x23d738 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xa4>
  0xf100151f#32, -- 0x23d6b8: cmp x8, #0x5
  0x540004c0#32, -- 0x23d6bc: b.eq 0x23d754 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xc0>
  0xf100191f#32, -- 0x23d6c0: cmp x8, #0x6
  0x540003a1#32, -- 0x23d6c4: b.ne 0x23d738 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xa4>
  0xaa0003f4#32, -- 0x23d6c8: mov x20, x0
  0x91002000#32, -- 0x23d6cc: add x0, x0, #0x8
  0xaa0103f3#32, -- 0x23d6d0: mov x19, x1
  0x91002021#32, -- 0x23d6d4: add x1, x1, #0x8
  0x94014622#32, -- 0x23d6d8: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x12001c08#32, -- 0x23d6dc: and w8, w0, #0xff
  0x7103f51f#32, -- 0x23d6e0: cmp w8, #0xfd
  0x540007cc#32, -- 0x23d6e4: b.gt 0x23d7dc <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x148>
  0x35000a68#32, -- 0x23d6e8: cbnz w8, 0x23d834 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0xf9401289#32, -- 0x23d6ec: ldr x9, [x20, #0x20]
  0xf9401268#32, -- 0x23d6f0: ldr x8, [x19, #0x20]
  0xf9401135#32, -- 0x23d6f4: ldr x21, [x9, #0x20]
  0xf9401116#32, -- 0x23d6f8: ldr x22, [x8, #0x20]
  0xeb1502df#32, -- 0x23d6fc: cmp x22, x21
  0x9a9532d7#32, -- 0x23d700: csel x23, x22, x21, lo
  0xb40005f7#32, -- 0x23d704: cbz x23, 0x23d7c0 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x12c>
  0xf9400d33#32, -- 0x23d708: ldr x19, [x9, #0x18]
  0xf9400d14#32, -- 0x23d70c: ldr x20, [x8, #0x18]
  0xaa1303e0#32, -- 0x23d710: mov x0, x19
  0xaa1403e1#32, -- 0x23d714: mov x1, x20
  0x94014612#32, -- 0x23d718: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x72001c1f#32, -- 0x23d71c: tst w0, #0xff
  0x540007e1#32, -- 0x23d720: b.ne 0x23d81c <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x188>
  0x91006294#32, -- 0x23d724: add x20, x20, #0x18
  0x91006273#32, -- 0x23d728: add x19, x19, #0x18
  0xf10006f7#32, -- 0x23d72c: subs x23, x23, #0x1
  0x54ffff01#32, -- 0x23d730: b.ne 0x23d710 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x7c>
  0x14000023#32, -- 0x23d734: b 0x23d7c0 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x12c>
  0xeb09011f#32, -- 0x23d738: cmp x8, x9
  0x1a9f27e0#32, -- 0x23d73c: cset w0, lo
  0xa9437bfd#32, -- 0x23d740: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x23d744: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x23d748: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x23d74c: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0x23d750: ret
  0xaa0003f4#32, -- 0x23d754: mov x20, x0
  0x91002000#32, -- 0x23d758: add x0, x0, #0x8
  0xaa0103f3#32, -- 0x23d75c: mov x19, x1
  0x91002021#32, -- 0x23d760: add x1, x1, #0x8
  0x940145ff#32, -- 0x23d764: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x12001c08#32, -- 0x23d768: and w8, w0, #0xff
  0x7103f51f#32, -- 0x23d76c: cmp w8, #0xfd
  0x5400046c#32, -- 0x23d770: b.gt 0x23d7fc <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x168>
  0x35000608#32, -- 0x23d774: cbnz w8, 0x23d834 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0xf9401289#32, -- 0x23d778: ldr x9, [x20, #0x20]
  0xf9401268#32, -- 0x23d77c: ldr x8, [x19, #0x20]
  0xf9401135#32, -- 0x23d780: ldr x21, [x9, #0x20]
  0xf9401116#32, -- 0x23d784: ldr x22, [x8, #0x20]
  0xeb1502df#32, -- 0x23d788: cmp x22, x21
  0x9a9532d7#32, -- 0x23d78c: csel x23, x22, x21, lo
  0xb4000197#32, -- 0x23d790: cbz x23, 0x23d7c0 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x12c>
  0xf9400d33#32, -- 0x23d794: ldr x19, [x9, #0x18]
  0xf9400d14#32, -- 0x23d798: ldr x20, [x8, #0x18]
  0xaa1303e0#32, -- 0x23d79c: mov x0, x19
  0xaa1403e1#32, -- 0x23d7a0: mov x1, x20
  0x940145ef#32, -- 0x23d7a4: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x72001c1f#32, -- 0x23d7a8: tst w0, #0xff
  0x54000381#32, -- 0x23d7ac: b.ne 0x23d81c <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x188>
  0x91006294#32, -- 0x23d7b0: add x20, x20, #0x18
  0x91006273#32, -- 0x23d7b4: add x19, x19, #0x18
  0xf10006f7#32, -- 0x23d7b8: subs x23, x23, #0x1
  0x54ffff01#32, -- 0x23d7bc: b.ne 0x23d79c <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x108>
  0xeb1602bf#32, -- 0x23d7c0: cmp x21, x22
  0x1a9f27e0#32, -- 0x23d7c4: cset w0, lo
  0xa9437bfd#32, -- 0x23d7c8: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x23d7cc: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x23d7d0: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x23d7d4: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0x23d7d8: ret
  0x7103f91f#32, -- 0x23d7dc: cmp w8, #0xfe
  0x540002a0#32, -- 0x23d7e0: b.eq 0x23d834 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0x52800020#32, -- 0x23d7e4: mov w0, #0x1 ; =1
  0xa9437bfd#32, -- 0x23d7e8: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x23d7ec: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x23d7f0: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x23d7f4: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0x23d7f8: ret
  0x7103f91f#32, -- 0x23d7fc: cmp w8, #0xfe
  0x540001a0#32, -- 0x23d800: b.eq 0x23d834 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0x52800020#32, -- 0x23d804: mov w0, #0x1 ; =1
  0xa9437bfd#32, -- 0x23d808: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x23d80c: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x23d810: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x23d814: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0x23d818: ret
  0x12001c08#32, -- 0x23d81c: and w8, w0, #0xff
  0x13001c09#32, -- 0x23d820: sxtb w9, w0
  0x7100013f#32, -- 0x23d824: cmp w9, #0x0
  0x1a9f57e0#32, -- 0x23d828: cset w0, mi
  0x7103f91f#32, -- 0x23d82c: cmp w8, #0xfe
  0x54fff881#32, -- 0x23d830: b.ne 0x23d740 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xac>
  0x52800000#32, -- 0x23d834: mov w0, #0x0 ; =0
  0xa9437bfd#32, -- 0x23d838: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x23d83c: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x23d840: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x23d844: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32  -- 0x23d848: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x23d694#64

/-- The addresses of the function's instructions. -/
def pcs : List (BitVec 64) := [0x23d694#64, 0x23d698#64, 0x23d69c#64, 0x23d6a0#64, 0x23d6a4#64, 0x23d6a8#64, 0x23d6ac#64, 0x23d6b0#64, 0x23d6b4#64, 0x23d6b8#64, 0x23d6bc#64, 0x23d6c0#64, 0x23d6c4#64, 0x23d6c8#64, 0x23d6cc#64, 0x23d6d0#64, 0x23d6d4#64, 0x23d6d8#64, 0x23d6dc#64, 0x23d6e0#64, 0x23d6e4#64, 0x23d6e8#64, 0x23d6ec#64, 0x23d6f0#64, 0x23d6f4#64, 0x23d6f8#64, 0x23d6fc#64, 0x23d700#64, 0x23d704#64, 0x23d708#64, 0x23d70c#64, 0x23d710#64, 0x23d714#64, 0x23d718#64, 0x23d71c#64, 0x23d720#64, 0x23d724#64, 0x23d728#64, 0x23d72c#64, 0x23d730#64, 0x23d734#64, 0x23d738#64, 0x23d73c#64, 0x23d740#64, 0x23d744#64, 0x23d748#64, 0x23d74c#64, 0x23d750#64, 0x23d754#64, 0x23d758#64, 0x23d75c#64, 0x23d760#64, 0x23d764#64, 0x23d768#64, 0x23d76c#64, 0x23d770#64, 0x23d774#64, 0x23d778#64, 0x23d77c#64, 0x23d780#64, 0x23d784#64, 0x23d788#64, 0x23d78c#64, 0x23d790#64, 0x23d794#64, 0x23d798#64, 0x23d79c#64, 0x23d7a0#64, 0x23d7a4#64, 0x23d7a8#64, 0x23d7ac#64, 0x23d7b0#64, 0x23d7b4#64, 0x23d7b8#64, 0x23d7bc#64, 0x23d7c0#64, 0x23d7c4#64, 0x23d7c8#64, 0x23d7cc#64, 0x23d7d0#64, 0x23d7d4#64, 0x23d7d8#64, 0x23d7dc#64, 0x23d7e0#64, 0x23d7e4#64, 0x23d7e8#64, 0x23d7ec#64, 0x23d7f0#64, 0x23d7f4#64, 0x23d7f8#64, 0x23d7fc#64, 0x23d800#64, 0x23d804#64, 0x23d808#64, 0x23d80c#64, 0x23d810#64, 0x23d814#64, 0x23d818#64, 0x23d81c#64, 0x23d820#64, 0x23d824#64, 0x23d828#64, 0x23d82c#64, 0x23d830#64, 0x23d834#64, 0x23d838#64, 0x23d83c#64, 0x23d840#64, 0x23d844#64, 0x23d848#64]

/-! Direct-call targets (not part of `prog`). -/
/-- `__RNvXsd_CsbhszFemdqnT_8smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp` -/
def ext_0 : BitVec 64 := 0x28ef60#64

end Examples.Cedar.NoPanic.Fn.TypeLt2
