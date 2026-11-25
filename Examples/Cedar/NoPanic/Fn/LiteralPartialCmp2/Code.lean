/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvXsf_NtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.LiteralPartialCmp2
open M1

def textBase : BitVec 64 := 0x284ea4#64

def text : List (BitVec 32) := [
  0xa9bb67fa#32, -- 0x284ea4: stp x26, x25, [sp, #-0x50]!
  0xa9015ff8#32, -- 0x284ea8: stp x24, x23, [sp, #0x10]
  0xa90257f6#32, -- 0x284eac: stp x22, x21, [sp, #0x20]
  0xa9034ff4#32, -- 0x284eb0: stp x20, x19, [sp, #0x30]
  0xa9047bfd#32, -- 0x284eb4: stp x29, x30, [sp, #0x40]
  0x910103fd#32, -- 0x284eb8: add x29, sp, #0x40
  0x39400008#32, -- 0x284ebc: ldrb w8, [x0]
  0x51006909#32, -- 0x284ec0: sub w9, w8, #0x1a
  0x5280004a#32, -- 0x284ec4: mov w10, #0x2 ; =2
  0x7100651f#32, -- 0x284ec8: cmp w8, #0x19
  0x1a8a8129#32, -- 0x284ecc: csel w9, w9, w10, hi
  0x12001d28#32, -- 0x284ed0: and w8, w9, #0xff
  0x3940002b#32, -- 0x284ed4: ldrb w11, [x1]
  0x5100696c#32, -- 0x284ed8: sub w12, w11, #0x1a
  0x7100657f#32, -- 0x284edc: cmp w11, #0x19
  0x1a8a818a#32, -- 0x284ee0: csel w10, w12, w10, hi
  0x6b2a011f#32, -- 0x284ee4: cmp w8, w10, uxtb
  0x540001a1#32, -- 0x284ee8: b.ne 0x284f1c <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x78>
  0x7100051f#32, -- 0x284eec: cmp w8, #0x1
  0x540002ac#32, -- 0x284ef0: b.gt 0x284f44 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0xa0>
  0x35000388#32, -- 0x284ef4: cbnz w8, 0x284f64 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0xc0>
  0x39400408#32, -- 0x284ef8: ldrb w8, [x0, #0x1]
  0x39400429#32, -- 0x284efc: ldrb w9, [x1, #0x1]
  0x4b090100#32, -- 0x284f00: sub w0, w8, w9
  0xa9447bfd#32, -- 0x284f04: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0x284f08: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0x284f0c: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0x284f10: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0x284f14: ldp x26, x25, [sp], #0x50
  0xd65f03c0#32, -- 0x284f18: ret
  0x92401d28#32, -- 0x284f1c: and x8, x9, #0xff
  0xeb2a011f#32, -- 0x284f20: cmp x8, w10, uxtb
  0x1a9fd7e8#32, -- 0x284f24: cset w8, gt
  0x5a9fa100#32, -- 0x284f28: csinv w0, w8, wzr, ge
  0xa9447bfd#32, -- 0x284f2c: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0x284f30: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0x284f34: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0x284f38: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0x284f3c: ldp x26, x25, [sp], #0x50
  0xd65f03c0#32, -- 0x284f40: ret
  0x7100091f#32, -- 0x284f44: cmp w8, #0x2
  0x54000161#32, -- 0x284f48: b.ne 0x284f74 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0xd0>
  0xa9447bfd#32, -- 0x284f4c: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0x284f50: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0x284f54: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0x284f58: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0x284f5c: ldp x26, x25, [sp], #0x50
  0x14002800#32, -- 0x284f60: b 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0xf9400408#32, -- 0x284f64: ldr x8, [x0, #0x8]
  0xf9400429#32, -- 0x284f68: ldr x9, [x1, #0x8]
  0xeb09011f#32, -- 0x284f6c: cmp x8, x9
  0x17ffffed#32, -- 0x284f70: b 0x284f24 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x80>
  0xf9400415#32, -- 0x284f74: ldr x21, [x0, #0x8]
  0xf9400436#32, -- 0x284f78: ldr x22, [x1, #0x8]
  0x910042a0#32, -- 0x284f7c: add x0, x21, #0x10
  0x910042c1#32, -- 0x284f80: add x1, x22, #0x10
  0x940027f7#32, -- 0x284f84: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x12001c08#32, -- 0x284f88: and w8, w0, #0xff
  0x7103f51f#32, -- 0x284f8c: cmp w8, #0xfd
  0x5400046c#32, -- 0x284f90: b.gt 0x28501c <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x178>
  0x35000568#32, -- 0x284f94: cbnz w8, 0x285040 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x19c>
  0xf94016a9#32, -- 0x284f98: ldr x9, [x21, #0x28]
  0xf94016c8#32, -- 0x284f9c: ldr x8, [x22, #0x28]
  0xf9401137#32, -- 0x284fa0: ldr x23, [x9, #0x20]
  0xf9401118#32, -- 0x284fa4: ldr x24, [x8, #0x20]
  0xeb17031f#32, -- 0x284fa8: cmp x24, x23
  0x9a973319#32, -- 0x284fac: csel x25, x24, x23, lo
  0xb4000199#32, -- 0x284fb0: cbz x25, 0x284fe0 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x13c>
  0xf9400d33#32, -- 0x284fb4: ldr x19, [x9, #0x18]
  0xf9400d14#32, -- 0x284fb8: ldr x20, [x8, #0x18]
  0xaa1303e0#32, -- 0x284fbc: mov x0, x19
  0xaa1403e1#32, -- 0x284fc0: mov x1, x20
  0x940027e7#32, -- 0x284fc4: bl 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x72001c1f#32, -- 0x284fc8: tst w0, #0xff
  0x54000101#32, -- 0x284fcc: b.ne 0x284fec <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x148>
  0x91006294#32, -- 0x284fd0: add x20, x20, #0x18
  0x91006273#32, -- 0x284fd4: add x19, x19, #0x18
  0xf1000739#32, -- 0x284fd8: subs x25, x25, #0x1
  0x54ffff01#32, -- 0x284fdc: b.ne 0x284fbc <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x118>
  0xeb1802ff#32, -- 0x284fe0: cmp x23, x24
  0x1a9f97e8#32, -- 0x284fe4: cset w8, hi
  0x5a9f2100#32, -- 0x284fe8: csinv w0, w8, wzr, hs
  0x12001c08#32, -- 0x284fec: and w8, w0, #0xff
  0x7103f51f#32, -- 0x284ff0: cmp w8, #0xfd
  0x5400014c#32, -- 0x284ff4: b.gt 0x28501c <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x178>
  0x35000248#32, -- 0x284ff8: cbnz w8, 0x285040 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x19c>
  0x910122a0#32, -- 0x284ffc: add x0, x21, #0x48
  0x910122c1#32, -- 0x285000: add x1, x22, #0x48
  0xa9447bfd#32, -- 0x285004: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0x285008: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0x28500c: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0x285010: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0x285014: ldp x26, x25, [sp], #0x50
  0x140027d2#32, -- 0x285018: b 0x28ef60 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp>
  0x7103f91f#32, -- 0x28501c: cmp w8, #0xfe
  0x54fff720#32, -- 0x285020: b.eq 0x284f04 <iCjQZ9Ydc0_17cedar_policy_core3ast7literalNtB5_7LiteralNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x60>
  0x52801fe0#32, -- 0x285024: mov w0, #0xff ; =255
  0xa9447bfd#32, -- 0x285028: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0x28502c: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0x285030: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0x285034: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0x285038: ldp x26, x25, [sp], #0x50
  0xd65f03c0#32, -- 0x28503c: ret
  0x52800020#32, -- 0x285040: mov w0, #0x1 ; =1
  0xa9447bfd#32, -- 0x285044: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0x285048: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0x28504c: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0x285050: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0x285054: ldp x26, x25, [sp], #0x50
  0xd65f03c0#32  -- 0x285058: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x284ea4#64

/-- The addresses of the function's instructions. -/
def pcs : List (BitVec 64) := [0x284ea4#64, 0x284ea8#64, 0x284eac#64, 0x284eb0#64, 0x284eb4#64, 0x284eb8#64, 0x284ebc#64, 0x284ec0#64, 0x284ec4#64, 0x284ec8#64, 0x284ecc#64, 0x284ed0#64, 0x284ed4#64, 0x284ed8#64, 0x284edc#64, 0x284ee0#64, 0x284ee4#64, 0x284ee8#64, 0x284eec#64, 0x284ef0#64, 0x284ef4#64, 0x284ef8#64, 0x284efc#64, 0x284f00#64, 0x284f04#64, 0x284f08#64, 0x284f0c#64, 0x284f10#64, 0x284f14#64, 0x284f18#64, 0x284f1c#64, 0x284f20#64, 0x284f24#64, 0x284f28#64, 0x284f2c#64, 0x284f30#64, 0x284f34#64, 0x284f38#64, 0x284f3c#64, 0x284f40#64, 0x284f44#64, 0x284f48#64, 0x284f4c#64, 0x284f50#64, 0x284f54#64, 0x284f58#64, 0x284f5c#64, 0x284f60#64, 0x284f64#64, 0x284f68#64, 0x284f6c#64, 0x284f70#64, 0x284f74#64, 0x284f78#64, 0x284f7c#64, 0x284f80#64, 0x284f84#64, 0x284f88#64, 0x284f8c#64, 0x284f90#64, 0x284f94#64, 0x284f98#64, 0x284f9c#64, 0x284fa0#64, 0x284fa4#64, 0x284fa8#64, 0x284fac#64, 0x284fb0#64, 0x284fb4#64, 0x284fb8#64, 0x284fbc#64, 0x284fc0#64, 0x284fc4#64, 0x284fc8#64, 0x284fcc#64, 0x284fd0#64, 0x284fd4#64, 0x284fd8#64, 0x284fdc#64, 0x284fe0#64, 0x284fe4#64, 0x284fe8#64, 0x284fec#64, 0x284ff0#64, 0x284ff4#64, 0x284ff8#64, 0x284ffc#64, 0x285000#64, 0x285004#64, 0x285008#64, 0x28500c#64, 0x285010#64, 0x285014#64, 0x285018#64, 0x28501c#64, 0x285020#64, 0x285024#64, 0x285028#64, 0x28502c#64, 0x285030#64, 0x285034#64, 0x285038#64, 0x28503c#64, 0x285040#64, 0x285044#64, 0x285048#64, 0x28504c#64, 0x285050#64, 0x285054#64, 0x285058#64]

/-! Direct-call targets (not part of `prog`). -/
/-- `__RNvXsd_CsbhszFemdqnT_8smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp` -/
def ext_0 : BitVec 64 := 0x28ef60#64

end Examples.Cedar.NoPanic.Fn.LiteralPartialCmp2
