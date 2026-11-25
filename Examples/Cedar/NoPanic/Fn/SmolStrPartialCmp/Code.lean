/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvXsd_CsbhszFemdqnT_8smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.SmolStrPartialCmp
open M1

def textBase : BitVec 64 := 0x28ef60#64

def text : List (BitVec 32) := [
  0x39400008#32, -- 0x28ef60: ldrb w8, [x0]
  0xd1005d09#32, -- 0x28ef64: sub x9, x8, #0x17
  0x71005d1f#32, -- 0x28ef68: cmp w8, #0x17
  0x9a9f8129#32, -- 0x28ef6c: csel x9, x9, xzr, hi
  0xb40001a9#32, -- 0x28ef70: cbz x9, 0x28efa4 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x44>
  0xf100053f#32, -- 0x28ef74: cmp x9, #0x1
  0x540002e1#32, -- 0x28ef78: b.ne 0x28efd4 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x74>
  0xaa0003e8#32, -- 0x28ef7c: mov x8, x0
  0xf9400400#32, -- 0x28ef80: ldr x0, [x0, #0x8]
  0xf9400908#32, -- 0x28ef84: ldr x8, [x8, #0x10]
  0x39400029#32, -- 0x28ef88: ldrb w9, [x1]
  0xd1005d2a#32, -- 0x28ef8c: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x28ef90: cmp w9, #0x17
  0x9a9f814a#32, -- 0x28ef94: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x28ef98: cmp x10, #0x2
  0x54000121#32, -- 0x28ef9c: b.ne 0x28efc0 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x60>
  0x14000015#32, -- 0x28efa0: b 0x28eff4 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x94>
  0x91000400#32, -- 0x28efa4: add x0, x0, #0x1
  0x39400029#32, -- 0x28efa8: ldrb w9, [x1]
  0xd1005d2a#32, -- 0x28efac: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x28efb0: cmp w9, #0x17
  0x9a9f814a#32, -- 0x28efb4: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x28efb8: cmp x10, #0x2
  0x540001c0#32, -- 0x28efbc: b.eq 0x28eff4 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x94>
  0xf100055f#32, -- 0x28efc0: cmp x10, #0x1
  0x540001e1#32, -- 0x28efc4: b.ne 0x28f000 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0xa0>
  0xa940a42a#32, -- 0x28efc8: ldp x10, x9, [x1, #0x8]
  0xaa0a03e1#32, -- 0x28efcc: mov x1, x10
  0x1400000d#32, -- 0x28efd0: b 0x28f004 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0xa4>
  0xa940a009#32, -- 0x28efd4: ldp x9, x8, [x0, #0x8]
  0x91004120#32, -- 0x28efd8: add x0, x9, #0x10
  0x39400029#32, -- 0x28efdc: ldrb w9, [x1]
  0xd1005d2a#32, -- 0x28efe0: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x28efe4: cmp w9, #0x17
  0x9a9f814a#32, -- 0x28efe8: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x28efec: cmp x10, #0x2
  0x54fffe81#32, -- 0x28eff0: b.ne 0x28efc0 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0x60>
  0xa940a42a#32, -- 0x28eff4: ldp x10, x9, [x1, #0x8]
  0x91004141#32, -- 0x28eff8: add x1, x10, #0x10
  0x14000002#32, -- 0x28effc: b 0x28f004 <smol_strNtB5_7SmolStrNtNtCskumHb0IaX0X_4core3cmp10PartialOrd11partial_cmp+0xa4>
  0x91000421#32, -- 0x28f000: add x1, x1, #0x1
  0xa9be4ff4#32, -- 0x28f004: stp x20, x19, [sp, #-0x20]!
  0xa9017bfd#32, -- 0x28f008: stp x29, x30, [sp, #0x10]
  0x910043fd#32, -- 0x28f00c: add x29, sp, #0x10
  0xeb090113#32, -- 0x28f010: subs x19, x8, x9
  0x9a893102#32, -- 0x28f014: csel x2, x8, x9, lo
  0x94031ac8#32, -- 0x28f018: bl 0x355b38 <dyld_stub_binder+0x355b38>
  0x93407c08#32, -- 0x28f01c: sxtw x8, w0
  0x7100001f#32, -- 0x28f020: cmp w0, #0x0
  0x9a880268#32, -- 0x28f024: csel x8, x19, x8, eq
  0xf100011f#32, -- 0x28f028: cmp x8, #0x0
  0x1a9fd7e8#32, -- 0x28f02c: cset w8, gt
  0x5a9f5100#32, -- 0x28f030: csinv w0, w8, wzr, pl
  0xa9417bfd#32, -- 0x28f034: ldp x29, x30, [sp, #0x10]
  0xa8c24ff4#32, -- 0x28f038: ldp x20, x19, [sp], #0x20
  0xd65f03c0#32  -- 0x28f03c: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x28ef60#64

/-- The addresses of the function's instructions. -/
def pcs : List (BitVec 64) := [0x28ef60#64, 0x28ef64#64, 0x28ef68#64, 0x28ef6c#64, 0x28ef70#64, 0x28ef74#64, 0x28ef78#64, 0x28ef7c#64, 0x28ef80#64, 0x28ef84#64, 0x28ef88#64, 0x28ef8c#64, 0x28ef90#64, 0x28ef94#64, 0x28ef98#64, 0x28ef9c#64, 0x28efa0#64, 0x28efa4#64, 0x28efa8#64, 0x28efac#64, 0x28efb0#64, 0x28efb4#64, 0x28efb8#64, 0x28efbc#64, 0x28efc0#64, 0x28efc4#64, 0x28efc8#64, 0x28efcc#64, 0x28efd0#64, 0x28efd4#64, 0x28efd8#64, 0x28efdc#64, 0x28efe0#64, 0x28efe4#64, 0x28efe8#64, 0x28efec#64, 0x28eff0#64, 0x28eff4#64, 0x28eff8#64, 0x28effc#64, 0x28f000#64, 0x28f004#64, 0x28f008#64, 0x28f00c#64, 0x28f010#64, 0x28f014#64, 0x28f018#64, 0x28f01c#64, 0x28f020#64, 0x28f024#64, 0x28f028#64, 0x28f02c#64, 0x28f030#64, 0x28f034#64, 0x28f038#64, 0x28f03c#64]

/-! Direct-call targets (not part of `prog`). -/
/-- `_memcmp` -/
def ext_0 : BitVec 64 := 0x355b38#64

end Examples.Cedar.NoPanic.Fn.SmolStrPartialCmp
