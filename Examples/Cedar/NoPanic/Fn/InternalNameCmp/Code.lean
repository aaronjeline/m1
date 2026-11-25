/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvXNvNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.InternalNameCmp
open M1

def textBase : BitVec 64 := 0x9a7d4#64

def text : List (BitVec 32) := [
  0xa9bb67fa#32, -- 0x9a7d4: stp x26, x25, [sp, #-0x50]!
  0xa9015ff8#32, -- 0x9a7d8: stp x24, x23, [sp, #0x10]
  0xa90257f6#32, -- 0x9a7dc: stp x22, x21, [sp, #0x20]
  0xa9034ff4#32, -- 0x9a7e0: stp x20, x19, [sp, #0x30]
  0xa9047bfd#32, -- 0x9a7e4: stp x29, x30, [sp, #0x40]
  0x910103fd#32, -- 0x9a7e8: add x29, sp, #0x40
  0xaa0103f3#32, -- 0x9a7ec: mov x19, x1
  0xaa0003f4#32, -- 0x9a7f0: mov x20, x0
  0x39400008#32, -- 0x9a7f4: ldrb w8, [x0]
  0xd1005d09#32, -- 0x9a7f8: sub x9, x8, #0x17
  0x71005d1f#32, -- 0x9a7fc: cmp w8, #0x17
  0x9a9f8129#32, -- 0x9a800: csel x9, x9, xzr, hi
  0xb4000169#32, -- 0x9a804: cbz x9, 0x9a830 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x5c>
  0xf100053f#32, -- 0x9a808: cmp x9, #0x1
  0x54000281#32, -- 0x9a80c: b.ne 0x9a85c <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x88>
  0xa940a280#32, -- 0x9a810: ldp x0, x8, [x20, #0x8]
  0x39400269#32, -- 0x9a814: ldrb w9, [x19]
  0xd1005d2a#32, -- 0x9a818: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x9a81c: cmp w9, #0x17
  0x9a9f814a#32, -- 0x9a820: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x9a824: cmp x10, #0x2
  0x54000121#32, -- 0x9a828: b.ne 0x9a84c <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x78>
  0x14000014#32, -- 0x9a82c: b 0x9a87c <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0xa8>
  0x91000680#32, -- 0x9a830: add x0, x20, #0x1
  0x39400269#32, -- 0x9a834: ldrb w9, [x19]
  0xd1005d2a#32, -- 0x9a838: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x9a83c: cmp w9, #0x17
  0x9a9f814a#32, -- 0x9a840: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x9a844: cmp x10, #0x2
  0x540001a0#32, -- 0x9a848: b.eq 0x9a87c <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0xa8>
  0xf100055f#32, -- 0x9a84c: cmp x10, #0x1
  0x540001c1#32, -- 0x9a850: b.ne 0x9a888 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0xb4>
  0xa940a661#32, -- 0x9a854: ldp x1, x9, [x19, #0x8]
  0x1400000d#32, -- 0x9a858: b 0x9a88c <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0xb8>
  0xa940a289#32, -- 0x9a85c: ldp x9, x8, [x20, #0x8]
  0x91004120#32, -- 0x9a860: add x0, x9, #0x10
  0x39400269#32, -- 0x9a864: ldrb w9, [x19]
  0xd1005d2a#32, -- 0x9a868: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x9a86c: cmp w9, #0x17
  0x9a9f814a#32, -- 0x9a870: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x9a874: cmp x10, #0x2
  0x54fffea1#32, -- 0x9a878: b.ne 0x9a84c <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x78>
  0xa940a66a#32, -- 0x9a87c: ldp x10, x9, [x19, #0x8]
  0x91004141#32, -- 0x9a880: add x1, x10, #0x10
  0x14000002#32, -- 0x9a884: b 0x9a88c <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0xb8>
  0x91000661#32, -- 0x9a888: add x1, x19, #0x1
  0xeb090115#32, -- 0x9a88c: subs x21, x8, x9
  0x9a893102#32, -- 0x9a890: csel x2, x8, x9, lo
  0x940aeca9#32, -- 0x9a894: bl 0x355b38 <dyld_stub_binder+0x355b38>
  0x93407c08#32, -- 0x9a898: sxtw x8, w0
  0x7100001f#32, -- 0x9a89c: cmp w0, #0x0
  0x9a8802a8#32, -- 0x9a8a0: csel x8, x21, x8, eq
  0xf100011f#32, -- 0x9a8a4: cmp x8, #0x0
  0x1a9fd7e9#32, -- 0x9a8a8: cset w9, gt
  0x5a9f5120#32, -- 0x9a8ac: csinv w0, w9, wzr, pl
  0xb40000e8#32, -- 0x9a8b0: cbz x8, 0x9a8cc <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0xf8>
  0xa9447bfd#32, -- 0x9a8b4: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0x9a8b8: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0x9a8bc: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0x9a8c0: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0x9a8c4: ldp x26, x25, [sp], #0x50
  0xd65f03c0#32, -- 0x9a8c8: ret
  0xf9400e89#32, -- 0x9a8cc: ldr x9, [x20, #0x18]
  0xf9400e68#32, -- 0x9a8d0: ldr x8, [x19, #0x18]
  0xf9401133#32, -- 0x9a8d4: ldr x19, [x9, #0x20]
  0xf9401114#32, -- 0x9a8d8: ldr x20, [x8, #0x20]
  0xeb13029f#32, -- 0x9a8dc: cmp x20, x19
  0x9a933295#32, -- 0x9a8e0: csel x21, x20, x19, lo
  0xb4000735#32, -- 0x9a8e4: cbz x21, 0x9a9c8 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x1f4>
  0xd2800016#32, -- 0x9a8e8: mov x22, #0x0 ; =0
  0xf9400d37#32, -- 0x9a8ec: ldr x23, [x9, #0x18]
  0xf9400d18#32, -- 0x9a8f0: ldr x24, [x8, #0x18]
  0x38766ae8#32, -- 0x9a8f4: ldrb w8, [x23, x22]
  0xd1005d09#32, -- 0x9a8f8: sub x9, x8, #0x17
  0x71005d1f#32, -- 0x9a8fc: cmp w8, #0x17
  0x9a9f8129#32, -- 0x9a900: csel x9, x9, xzr, hi
  0xb4000189#32, -- 0x9a904: cbz x9, 0x9a934 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x160>
  0x8b1602e8#32, -- 0x9a908: add x8, x23, x22
  0xf100053f#32, -- 0x9a90c: cmp x9, #0x1
  0x540002c1#32, -- 0x9a910: b.ne 0x9a968 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x194>
  0xa940a100#32, -- 0x9a914: ldp x0, x8, [x8, #0x8]
  0x38766b09#32, -- 0x9a918: ldrb w9, [x24, x22]
  0xd1005d2a#32, -- 0x9a91c: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x9a920: cmp w9, #0x17
  0x9a9f814a#32, -- 0x9a924: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x9a928: cmp x10, #0x2
  0x54000141#32, -- 0x9a92c: b.ne 0x9a954 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x180>
  0x14000016#32, -- 0x9a930: b 0x9a988 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x1b4>
  0x8b1602e9#32, -- 0x9a934: add x9, x23, x22
  0x91000520#32, -- 0x9a938: add x0, x9, #0x1
  0x38766b09#32, -- 0x9a93c: ldrb w9, [x24, x22]
  0xd1005d2a#32, -- 0x9a940: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x9a944: cmp w9, #0x17
  0x9a9f814a#32, -- 0x9a948: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x9a94c: cmp x10, #0x2
  0x540001c0#32, -- 0x9a950: b.eq 0x9a988 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x1b4>
  0xf100055f#32, -- 0x9a954: cmp x10, #0x1
  0x54000201#32, -- 0x9a958: b.ne 0x9a998 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x1c4>
  0x8b160309#32, -- 0x9a95c: add x9, x24, x22
  0xa940a521#32, -- 0x9a960: ldp x1, x9, [x9, #0x8]
  0x1400000f#32, -- 0x9a964: b 0x9a9a0 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x1cc>
  0xa940a109#32, -- 0x9a968: ldp x9, x8, [x8, #0x8]
  0x91004120#32, -- 0x9a96c: add x0, x9, #0x10
  0x38766b09#32, -- 0x9a970: ldrb w9, [x24, x22]
  0xd1005d2a#32, -- 0x9a974: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x9a978: cmp w9, #0x17
  0x9a9f814a#32, -- 0x9a97c: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x9a980: cmp x10, #0x2
  0x54fffe81#32, -- 0x9a984: b.ne 0x9a954 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x180>
  0x8b160309#32, -- 0x9a988: add x9, x24, x22
  0xa940a52a#32, -- 0x9a98c: ldp x10, x9, [x9, #0x8]
  0x91004141#32, -- 0x9a990: add x1, x10, #0x10
  0x14000003#32, -- 0x9a994: b 0x9a9a0 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x1cc>
  0x8b16030a#32, -- 0x9a998: add x10, x24, x22
  0x91000541#32, -- 0x9a99c: add x1, x10, #0x1
  0xeb090119#32, -- 0x9a9a0: subs x25, x8, x9
  0x9a893102#32, -- 0x9a9a4: csel x2, x8, x9, lo
  0x940aec64#32, -- 0x9a9a8: bl 0x355b38 <dyld_stub_binder+0x355b38>
  0x93407c08#32, -- 0x9a9ac: sxtw x8, w0
  0x7100001f#32, -- 0x9a9b0: cmp w0, #0x0
  0x9a880328#32, -- 0x9a9b4: csel x8, x25, x8, eq
  0xb50001a8#32, -- 0x9a9b8: cbnz x8, 0x9a9ec <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x218>
  0x910062d6#32, -- 0x9a9bc: add x22, x22, #0x18
  0xf10006b5#32, -- 0x9a9c0: subs x21, x21, #0x1
  0x54fff981#32, -- 0x9a9c4: b.ne 0x9a8f4 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x120>
  0xeb14027f#32, -- 0x9a9c8: cmp x19, x20
  0x1a9f97e8#32, -- 0x9a9cc: cset w8, hi
  0x5a9f2100#32, -- 0x9a9d0: csinv w0, w8, wzr, hs
  0xa9447bfd#32, -- 0x9a9d4: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0x9a9d8: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0x9a9dc: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0x9a9e0: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0x9a9e4: ldp x26, x25, [sp], #0x50
  0xd65f03c0#32, -- 0x9a9e8: ret
  0xf100011f#32, -- 0x9a9ec: cmp x8, #0x0
  0x1a9fd7e8#32, -- 0x9a9f0: cset w8, gt
  0x5a9f5100#32, -- 0x9a9f4: csinv w0, w8, wzr, pl
  0xa9447bfd#32, -- 0x9a9f8: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0x9a9fc: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0x9aa00: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0x9aa04: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0x9aa08: ldp x26, x25, [sp], #0x50
  0xd65f03c0#32  -- 0x9aa0c: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x9a7d4#64

/-- The addresses of the function's instructions. -/
def pcs : List (BitVec 64) := [0x9a7d4#64, 0x9a7d8#64, 0x9a7dc#64, 0x9a7e0#64, 0x9a7e4#64, 0x9a7e8#64, 0x9a7ec#64, 0x9a7f0#64, 0x9a7f4#64, 0x9a7f8#64, 0x9a7fc#64, 0x9a800#64, 0x9a804#64, 0x9a808#64, 0x9a80c#64, 0x9a810#64, 0x9a814#64, 0x9a818#64, 0x9a81c#64, 0x9a820#64, 0x9a824#64, 0x9a828#64, 0x9a82c#64, 0x9a830#64, 0x9a834#64, 0x9a838#64, 0x9a83c#64, 0x9a840#64, 0x9a844#64, 0x9a848#64, 0x9a84c#64, 0x9a850#64, 0x9a854#64, 0x9a858#64, 0x9a85c#64, 0x9a860#64, 0x9a864#64, 0x9a868#64, 0x9a86c#64, 0x9a870#64, 0x9a874#64, 0x9a878#64, 0x9a87c#64, 0x9a880#64, 0x9a884#64, 0x9a888#64, 0x9a88c#64, 0x9a890#64, 0x9a894#64, 0x9a898#64, 0x9a89c#64, 0x9a8a0#64, 0x9a8a4#64, 0x9a8a8#64, 0x9a8ac#64, 0x9a8b0#64, 0x9a8b4#64, 0x9a8b8#64, 0x9a8bc#64, 0x9a8c0#64, 0x9a8c4#64, 0x9a8c8#64, 0x9a8cc#64, 0x9a8d0#64, 0x9a8d4#64, 0x9a8d8#64, 0x9a8dc#64, 0x9a8e0#64, 0x9a8e4#64, 0x9a8e8#64, 0x9a8ec#64, 0x9a8f0#64, 0x9a8f4#64, 0x9a8f8#64, 0x9a8fc#64, 0x9a900#64, 0x9a904#64, 0x9a908#64, 0x9a90c#64, 0x9a910#64, 0x9a914#64, 0x9a918#64, 0x9a91c#64, 0x9a920#64, 0x9a924#64, 0x9a928#64, 0x9a92c#64, 0x9a930#64, 0x9a934#64, 0x9a938#64, 0x9a93c#64, 0x9a940#64, 0x9a944#64, 0x9a948#64, 0x9a94c#64, 0x9a950#64, 0x9a954#64, 0x9a958#64, 0x9a95c#64, 0x9a960#64, 0x9a964#64, 0x9a968#64, 0x9a96c#64, 0x9a970#64, 0x9a974#64, 0x9a978#64, 0x9a97c#64, 0x9a980#64, 0x9a984#64, 0x9a988#64, 0x9a98c#64, 0x9a990#64, 0x9a994#64, 0x9a998#64, 0x9a99c#64, 0x9a9a0#64, 0x9a9a4#64, 0x9a9a8#64, 0x9a9ac#64, 0x9a9b0#64, 0x9a9b4#64, 0x9a9b8#64, 0x9a9bc#64, 0x9a9c0#64, 0x9a9c4#64, 0x9a9c8#64, 0x9a9cc#64, 0x9a9d0#64, 0x9a9d4#64, 0x9a9d8#64, 0x9a9dc#64, 0x9a9e0#64, 0x9a9e4#64, 0x9a9e8#64, 0x9a9ec#64, 0x9a9f0#64, 0x9a9f4#64, 0x9a9f8#64, 0x9a9fc#64, 0x9aa00#64, 0x9aa04#64, 0x9aa08#64, 0x9aa0c#64]

/-! Direct-call targets (not part of `prog`). -/
/-- `_memcmp` -/
def ext_0 : BitVec 64 := 0x355b38#64

end Examples.Cedar.NoPanic.Fn.InternalNameCmp
