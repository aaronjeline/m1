/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvYNvYNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_.llvm.4595567767768807451`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.TypeLt3
open M1

def textBase : BitVec 64 := 0x287054#64

def text : List (BitVec 32) := [
  0xa9bc5ff8#32, -- 0x287054: stp x24, x23, [sp, #-0x40]!
  0xa90157f6#32, -- 0x287058: stp x22, x21, [sp, #0x10]
  0xa9024ff4#32, -- 0x28705c: stp x20, x19, [sp, #0x20]
  0xa9037bfd#32, -- 0x287060: stp x29, x30, [sp, #0x30]
  0x9100c3fd#32, -- 0x287064: add x29, sp, #0x30
  0xf9400008#32, -- 0x287068: ldr x8, [x0]
  0xf9400029#32, -- 0x28706c: ldr x9, [x1]
  0xeb09011f#32, -- 0x287070: cmp x8, x9
  0x54000421#32, -- 0x287074: b.ne 0x2870f8 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xa4>
  0xf100151f#32, -- 0x287078: cmp x8, #0x5
  0x540004c0#32, -- 0x28707c: b.eq 0x287114 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xc0>
  0xf100191f#32, -- 0x287080: cmp x8, #0x6
  0x540003a1#32, -- 0x287084: b.ne 0x2870f8 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xa4>
  0xaa0003f4#32, -- 0x287088: mov x20, x0
  0x91002000#32, -- 0x28708c: add x0, x0, #0x8
  0xaa0103f3#32, -- 0x287090: mov x19, x1
  0x91002021#32, -- 0x287094: add x1, x1, #0x8
  0x94001fb2#32, -- 0x287098: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x12001c08#32, -- 0x28709c: and w8, w0, #0xff
  0x7103f51f#32, -- 0x2870a0: cmp w8, #0xfd
  0x540007cc#32, -- 0x2870a4: b.gt 0x28719c <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x148>
  0x35000a68#32, -- 0x2870a8: cbnz w8, 0x2871f4 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0xf9401289#32, -- 0x2870ac: ldr x9, [x20, #0x20]
  0xf9401268#32, -- 0x2870b0: ldr x8, [x19, #0x20]
  0xf9401135#32, -- 0x2870b4: ldr x21, [x9, #0x20]
  0xf9401116#32, -- 0x2870b8: ldr x22, [x8, #0x20]
  0xeb1502df#32, -- 0x2870bc: cmp x22, x21
  0x9a9532d7#32, -- 0x2870c0: csel x23, x22, x21, lo
  0xb40005f7#32, -- 0x2870c4: cbz x23, 0x287180 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x12c>
  0xf9400d33#32, -- 0x2870c8: ldr x19, [x9, #0x18]
  0xf9400d14#32, -- 0x2870cc: ldr x20, [x8, #0x18]
  0xaa1303e0#32, -- 0x2870d0: mov x0, x19
  0xaa1403e1#32, -- 0x2870d4: mov x1, x20
  0x94001fa2#32, -- 0x2870d8: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x72001c1f#32, -- 0x2870dc: tst w0, #0xff
  0x540007e1#32, -- 0x2870e0: b.ne 0x2871dc <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x188>
  0x91006294#32, -- 0x2870e4: add x20, x20, #0x18
  0x91006273#32, -- 0x2870e8: add x19, x19, #0x18
  0xf10006f7#32, -- 0x2870ec: subs x23, x23, #0x1
  0x54ffff01#32, -- 0x2870f0: b.ne 0x2870d0 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x7c>
  0x14000023#32, -- 0x2870f4: b 0x287180 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x12c>
  0xeb09011f#32, -- 0x2870f8: cmp x8, x9
  0x1a9f27e0#32, -- 0x2870fc: cset w0, lo
  0xa9437bfd#32, -- 0x287100: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x287104: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x287108: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x28710c: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0x287110: ret
  0xaa0003f4#32, -- 0x287114: mov x20, x0
  0x91002000#32, -- 0x287118: add x0, x0, #0x8
  0xaa0103f3#32, -- 0x28711c: mov x19, x1
  0x91002021#32, -- 0x287120: add x1, x1, #0x8
  0x94001f8f#32, -- 0x287124: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x12001c08#32, -- 0x287128: and w8, w0, #0xff
  0x7103f51f#32, -- 0x28712c: cmp w8, #0xfd
  0x5400046c#32, -- 0x287130: b.gt 0x2871bc <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x168>
  0x35000608#32, -- 0x287134: cbnz w8, 0x2871f4 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0xf9401289#32, -- 0x287138: ldr x9, [x20, #0x20]
  0xf9401268#32, -- 0x28713c: ldr x8, [x19, #0x20]
  0xf9401135#32, -- 0x287140: ldr x21, [x9, #0x20]
  0xf9401116#32, -- 0x287144: ldr x22, [x8, #0x20]
  0xeb1502df#32, -- 0x287148: cmp x22, x21
  0x9a9532d7#32, -- 0x28714c: csel x23, x22, x21, lo
  0xb4000197#32, -- 0x287150: cbz x23, 0x287180 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x12c>
  0xf9400d33#32, -- 0x287154: ldr x19, [x9, #0x18]
  0xf9400d14#32, -- 0x287158: ldr x20, [x8, #0x18]
  0xaa1303e0#32, -- 0x28715c: mov x0, x19
  0xaa1403e1#32, -- 0x287160: mov x1, x20
  0x94001f7f#32, -- 0x287164: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x72001c1f#32, -- 0x287168: tst w0, #0xff
  0x54000381#32, -- 0x28716c: b.ne 0x2871dc <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x188>
  0x91006294#32, -- 0x287170: add x20, x20, #0x18
  0x91006273#32, -- 0x287174: add x19, x19, #0x18
  0xf10006f7#32, -- 0x287178: subs x23, x23, #0x1
  0x54ffff01#32, -- 0x28717c: b.ne 0x28715c <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x108>
  0xeb1602bf#32, -- 0x287180: cmp x21, x22
  0x1a9f27e0#32, -- 0x287184: cset w0, lo
  0xa9437bfd#32, -- 0x287188: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x28718c: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x287190: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x287194: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0x287198: ret
  0x7103f91f#32, -- 0x28719c: cmp w8, #0xfe
  0x540002a0#32, -- 0x2871a0: b.eq 0x2871f4 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0x52800020#32, -- 0x2871a4: mov w0, #0x1 ; =1
  0xa9437bfd#32, -- 0x2871a8: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x2871ac: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x2871b0: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x2871b4: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0x2871b8: ret
  0x7103f91f#32, -- 0x2871bc: cmp w8, #0xfe
  0x540001a0#32, -- 0x2871c0: b.eq 0x2871f4 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0x1a0>
  0x52800020#32, -- 0x2871c4: mov w0, #0x1 ; =1
  0xa9437bfd#32, -- 0x2871c8: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x2871cc: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x2871d0: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x2871d4: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32, -- 0x2871d8: ret
  0x12001c08#32, -- 0x2871dc: and w8, w0, #0xff
  0x13001c09#32, -- 0x2871e0: sxtb w9, w0
  0x7100013f#32, -- 0x2871e4: cmp w9, #0x0
  0x1a9f57e0#32, -- 0x2871e8: cset w0, mi
  0x7103f91f#32, -- 0x2871ec: cmp w8, #0xfe
  0x54fff881#32, -- 0x2871f0: b.ne 0x287100 <iCjQZ9Ydc0_17cedar_policy_core3ast5types4TypeNtNtCskumHb0IaX0X_4core3cmp10PartialOrd2ltINtNtNtB11_3ops8function5FnMutTRB5_B28_EE8call_mutBb_+0xac>
  0x52800000#32, -- 0x2871f4: mov w0, #0x0 ; =0
  0xa9437bfd#32, -- 0x2871f8: ldp x29, x30, [sp, #0x30]
  0xa9424ff4#32, -- 0x2871fc: ldp x20, x19, [sp, #0x20]
  0xa94157f6#32, -- 0x287200: ldp x22, x21, [sp, #0x10]
  0xa8c45ff8#32, -- 0x287204: ldp x24, x23, [sp], #0x40
  0xd65f03c0#32  -- 0x287208: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x287054#64

/-- The addresses of the function's instructions. -/
def pcs : List (BitVec 64) := [0x287054#64, 0x287058#64, 0x28705c#64, 0x287060#64, 0x287064#64, 0x287068#64, 0x28706c#64, 0x287070#64, 0x287074#64, 0x287078#64, 0x28707c#64, 0x287080#64, 0x287084#64, 0x287088#64, 0x28708c#64, 0x287090#64, 0x287094#64, 0x287098#64, 0x28709c#64, 0x2870a0#64, 0x2870a4#64, 0x2870a8#64, 0x2870ac#64, 0x2870b0#64, 0x2870b4#64, 0x2870b8#64, 0x2870bc#64, 0x2870c0#64, 0x2870c4#64, 0x2870c8#64, 0x2870cc#64, 0x2870d0#64, 0x2870d4#64, 0x2870d8#64, 0x2870dc#64, 0x2870e0#64, 0x2870e4#64, 0x2870e8#64, 0x2870ec#64, 0x2870f0#64, 0x2870f4#64, 0x2870f8#64, 0x2870fc#64, 0x287100#64, 0x287104#64, 0x287108#64, 0x28710c#64, 0x287110#64, 0x287114#64, 0x287118#64, 0x28711c#64, 0x287120#64, 0x287124#64, 0x287128#64, 0x28712c#64, 0x287130#64, 0x287134#64, 0x287138#64, 0x28713c#64, 0x287140#64, 0x287144#64, 0x287148#64, 0x28714c#64, 0x287150#64, 0x287154#64, 0x287158#64, 0x28715c#64, 0x287160#64, 0x287164#64, 0x287168#64, 0x28716c#64, 0x287170#64, 0x287174#64, 0x287178#64, 0x28717c#64, 0x287180#64, 0x287184#64, 0x287188#64, 0x28718c#64, 0x287190#64, 0x287194#64, 0x287198#64, 0x28719c#64, 0x2871a0#64, 0x2871a4#64, 0x2871a8#64, 0x2871ac#64, 0x2871b0#64, 0x2871b4#64, 0x2871b8#64, 0x2871bc#64, 0x2871c0#64, 0x2871c4#64, 0x2871c8#64, 0x2871cc#64, 0x2871d0#64, 0x2871d4#64, 0x2871d8#64, 0x2871dc#64, 0x2871e0#64, 0x2871e4#64, 0x2871e8#64, 0x2871ec#64, 0x2871f0#64, 0x2871f4#64, 0x2871f8#64, 0x2871fc#64, 0x287200#64, 0x287204#64, 0x287208#64]

/-! Direct-call targets (not part of `prog`). -/
/-- `__RNvXsd_CsbhszFemdqnT_8smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp` -/
def ext_0 : BitVec 64 := 0x28ef60#64

end Examples.Cedar.NoPanic.Fn.TypeLt3
