/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvXsf_NtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.LiteralPartialCmp
open M1

def textBase : BitVec 64 := 0xe084c#64

def text : List (BitVec 32) := [
  0xa9bb67fa#32, -- 0xe084c: stp x26, x25, [sp, #-0x50]!
  0xa9015ff8#32, -- 0xe0850: stp x24, x23, [sp, #0x10]
  0xa90257f6#32, -- 0xe0854: stp x22, x21, [sp, #0x20]
  0xa9034ff4#32, -- 0xe0858: stp x20, x19, [sp, #0x30]
  0xa9047bfd#32, -- 0xe085c: stp x29, x30, [sp, #0x40]
  0x910103fd#32, -- 0xe0860: add x29, sp, #0x40
  0x39400008#32, -- 0xe0864: ldrb w8, [x0]
  0x51006909#32, -- 0xe0868: sub w9, w8, #0x1a
  0x5280004a#32, -- 0xe086c: mov w10, #0x2 ; =2
  0x7100651f#32, -- 0xe0870: cmp w8, #0x19
  0x1a8a8129#32, -- 0xe0874: csel w9, w9, w10, hi
  0x12001d28#32, -- 0xe0878: and w8, w9, #0xff
  0x3940002b#32, -- 0xe087c: ldrb w11, [x1]
  0x5100696c#32, -- 0xe0880: sub w12, w11, #0x1a
  0x7100657f#32, -- 0xe0884: cmp w11, #0x19
  0x1a8a818a#32, -- 0xe0888: csel w10, w12, w10, hi
  0x6b2a011f#32, -- 0xe088c: cmp w8, w10, uxtb
  0x540001a1#32, -- 0xe0890: b.ne 0xe08c4 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x78>
  0x7100051f#32, -- 0xe0894: cmp w8, #0x1
  0x540002ac#32, -- 0xe0898: b.gt 0xe08ec <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0xa0>
  0x35000388#32, -- 0xe089c: cbnz w8, 0xe090c <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0xc0>
  0x39400408#32, -- 0xe08a0: ldrb w8, [x0, #0x1]
  0x39400429#32, -- 0xe08a4: ldrb w9, [x1, #0x1]
  0x4b090100#32, -- 0xe08a8: sub w0, w8, w9
  0xa9447bfd#32, -- 0xe08ac: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0xe08b0: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0xe08b4: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0xe08b8: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0xe08bc: ldp x26, x25, [sp], #0x50
  0xd65f03c0#32, -- 0xe08c0: ret
  0x92401d28#32, -- 0xe08c4: and x8, x9, #0xff
  0xeb2a011f#32, -- 0xe08c8: cmp x8, w10, uxtb
  0x1a9fd7e8#32, -- 0xe08cc: cset w8, gt
  0x5a9fa100#32, -- 0xe08d0: csinv w0, w8, wzr, ge
  0xa9447bfd#32, -- 0xe08d4: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0xe08d8: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0xe08dc: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0xe08e0: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0xe08e4: ldp x26, x25, [sp], #0x50
  0xd65f03c0#32, -- 0xe08e8: ret
  0x7100091f#32, -- 0xe08ec: cmp w8, #0x2
  0x54000161#32, -- 0xe08f0: b.ne 0xe091c <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0xd0>
  0xa9447bfd#32, -- 0xe08f4: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0xe08f8: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0xe08fc: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0xe0900: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0xe0904: ldp x26, x25, [sp], #0x50
  0x1406b996#32, -- 0xe0908: b 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0xf9400408#32, -- 0xe090c: ldr x8, [x0, #0x8]
  0xf9400429#32, -- 0xe0910: ldr x9, [x1, #0x8]
  0xeb09011f#32, -- 0xe0914: cmp x8, x9
  0x17ffffed#32, -- 0xe0918: b 0xe08cc <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x80>
  0xf9400415#32, -- 0xe091c: ldr x21, [x0, #0x8]
  0xf9400436#32, -- 0xe0920: ldr x22, [x1, #0x8]
  0x910042a0#32, -- 0xe0924: add x0, x21, #0x10
  0x910042c1#32, -- 0xe0928: add x1, x22, #0x10
  0x9406b98d#32, -- 0xe092c: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x12001c08#32, -- 0xe0930: and w8, w0, #0xff
  0x7103f51f#32, -- 0xe0934: cmp w8, #0xfd
  0x5400046c#32, -- 0xe0938: b.gt 0xe09c4 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x178>
  0x35000568#32, -- 0xe093c: cbnz w8, 0xe09e8 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x19c>
  0xf94016a9#32, -- 0xe0940: ldr x9, [x21, #0x28]
  0xf94016c8#32, -- 0xe0944: ldr x8, [x22, #0x28]
  0xf9401137#32, -- 0xe0948: ldr x23, [x9, #0x20]
  0xf9401118#32, -- 0xe094c: ldr x24, [x8, #0x20]
  0xeb17031f#32, -- 0xe0950: cmp x24, x23
  0x9a973319#32, -- 0xe0954: csel x25, x24, x23, lo
  0xb4000199#32, -- 0xe0958: cbz x25, 0xe0988 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x13c>
  0xf9400d33#32, -- 0xe095c: ldr x19, [x9, #0x18]
  0xf9400d14#32, -- 0xe0960: ldr x20, [x8, #0x18]
  0xaa1303e0#32, -- 0xe0964: mov x0, x19
  0xaa1403e1#32, -- 0xe0968: mov x1, x20
  0x9406b97d#32, -- 0xe096c: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x72001c1f#32, -- 0xe0970: tst w0, #0xff
  0x54000101#32, -- 0xe0974: b.ne 0xe0994 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x148>
  0x91006294#32, -- 0xe0978: add x20, x20, #0x18
  0x91006273#32, -- 0xe097c: add x19, x19, #0x18
  0xf1000739#32, -- 0xe0980: subs x25, x25, #0x1
  0x54ffff01#32, -- 0xe0984: b.ne 0xe0964 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x118>
  0xeb1802ff#32, -- 0xe0988: cmp x23, x24
  0x1a9f97e8#32, -- 0xe098c: cset w8, hi
  0x5a9f2100#32, -- 0xe0990: csinv w0, w8, wzr, hs
  0x12001c08#32, -- 0xe0994: and w8, w0, #0xff
  0x7103f51f#32, -- 0xe0998: cmp w8, #0xfd
  0x5400014c#32, -- 0xe099c: b.gt 0xe09c4 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x178>
  0x35000248#32, -- 0xe09a0: cbnz w8, 0xe09e8 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x19c>
  0x910122a0#32, -- 0xe09a4: add x0, x21, #0x48
  0x910122c1#32, -- 0xe09a8: add x1, x22, #0x48
  0xa9447bfd#32, -- 0xe09ac: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0xe09b0: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0xe09b4: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0xe09b8: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0xe09bc: ldp x26, x25, [sp], #0x50
  0x1406b968#32, -- 0xe09c0: b 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x7103f91f#32, -- 0xe09c4: cmp w8, #0xfe
  0x54fff720#32, -- 0xe09c8: b.eq 0xe08ac <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x60>
  0x52801fe0#32, -- 0xe09cc: mov w0, #0xff ; =255
  0xa9447bfd#32, -- 0xe09d0: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0xe09d4: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0xe09d8: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0xe09dc: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0xe09e0: ldp x26, x25, [sp], #0x50
  0xd65f03c0#32, -- 0xe09e4: ret
  0x52800020#32, -- 0xe09e8: mov w0, #0x1 ; =1
  0xa9447bfd#32, -- 0xe09ec: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0xe09f0: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0xe09f4: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0xe09f8: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0xe09fc: ldp x26, x25, [sp], #0x50
  0xd65f03c0#32  -- 0xe0a00: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0xe084c#64

/-- The addresses of the function's instructions. -/
def pcs : List (BitVec 64) := [0xe084c#64, 0xe0850#64, 0xe0854#64, 0xe0858#64, 0xe085c#64, 0xe0860#64, 0xe0864#64, 0xe0868#64, 0xe086c#64, 0xe0870#64, 0xe0874#64, 0xe0878#64, 0xe087c#64, 0xe0880#64, 0xe0884#64, 0xe0888#64, 0xe088c#64, 0xe0890#64, 0xe0894#64, 0xe0898#64, 0xe089c#64, 0xe08a0#64, 0xe08a4#64, 0xe08a8#64, 0xe08ac#64, 0xe08b0#64, 0xe08b4#64, 0xe08b8#64, 0xe08bc#64, 0xe08c0#64, 0xe08c4#64, 0xe08c8#64, 0xe08cc#64, 0xe08d0#64, 0xe08d4#64, 0xe08d8#64, 0xe08dc#64, 0xe08e0#64, 0xe08e4#64, 0xe08e8#64, 0xe08ec#64, 0xe08f0#64, 0xe08f4#64, 0xe08f8#64, 0xe08fc#64, 0xe0900#64, 0xe0904#64, 0xe0908#64, 0xe090c#64, 0xe0910#64, 0xe0914#64, 0xe0918#64, 0xe091c#64, 0xe0920#64, 0xe0924#64, 0xe0928#64, 0xe092c#64, 0xe0930#64, 0xe0934#64, 0xe0938#64, 0xe093c#64, 0xe0940#64, 0xe0944#64, 0xe0948#64, 0xe094c#64, 0xe0950#64, 0xe0954#64, 0xe0958#64, 0xe095c#64, 0xe0960#64, 0xe0964#64, 0xe0968#64, 0xe096c#64, 0xe0970#64, 0xe0974#64, 0xe0978#64, 0xe097c#64, 0xe0980#64, 0xe0984#64, 0xe0988#64, 0xe098c#64, 0xe0990#64, 0xe0994#64, 0xe0998#64, 0xe099c#64, 0xe09a0#64, 0xe09a4#64, 0xe09a8#64, 0xe09ac#64, 0xe09b0#64, 0xe09b4#64, 0xe09b8#64, 0xe09bc#64, 0xe09c0#64, 0xe09c4#64, 0xe09c8#64, 0xe09cc#64, 0xe09d0#64, 0xe09d4#64, 0xe09d8#64, 0xe09dc#64, 0xe09e0#64, 0xe09e4#64, 0xe09e8#64, 0xe09ec#64, 0xe09f0#64, 0xe09f4#64, 0xe09f8#64, 0xe09fc#64, 0xe0a00#64]

/-! Direct-call targets (not part of `prog`). -/
/-- `__RNvXsd_CsbhszFemdqnT_8smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp` -/
def ext_0 : BitVec 64 := 0x28ef60#64

end Examples.Cedar.NoPanic.Fn.LiteralPartialCmp
