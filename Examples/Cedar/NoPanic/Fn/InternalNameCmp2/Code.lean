/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvXNvNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp.llvm.7875525832594653720`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.InternalNameCmp2
open M1

def textBase : BitVec 64 := 0x23c2e4#64

def text : List (BitVec 32) := [
  0xa9bb67fa#32, -- 0x23c2e4: stp x26, x25, [sp, #-0x50]!
  0xa9015ff8#32, -- 0x23c2e8: stp x24, x23, [sp, #0x10]
  0xa90257f6#32, -- 0x23c2ec: stp x22, x21, [sp, #0x20]
  0xa9034ff4#32, -- 0x23c2f0: stp x20, x19, [sp, #0x30]
  0xa9047bfd#32, -- 0x23c2f4: stp x29, x30, [sp, #0x40]
  0x910103fd#32, -- 0x23c2f8: add x29, sp, #0x40
  0xaa0103f3#32, -- 0x23c2fc: mov x19, x1
  0xaa0003f4#32, -- 0x23c300: mov x20, x0
  0x39400008#32, -- 0x23c304: ldrb w8, [x0]
  0xd1005d09#32, -- 0x23c308: sub x9, x8, #0x17
  0x71005d1f#32, -- 0x23c30c: cmp w8, #0x17
  0x9a9f8129#32, -- 0x23c310: csel x9, x9, xzr, hi
  0xb4000169#32, -- 0x23c314: cbz x9, 0x23c340 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x5c>
  0xf100053f#32, -- 0x23c318: cmp x9, #0x1
  0x54000281#32, -- 0x23c31c: b.ne 0x23c36c <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x88>
  0xa940a280#32, -- 0x23c320: ldp x0, x8, [x20, #0x8]
  0x39400269#32, -- 0x23c324: ldrb w9, [x19]
  0xd1005d2a#32, -- 0x23c328: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x23c32c: cmp w9, #0x17
  0x9a9f814a#32, -- 0x23c330: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x23c334: cmp x10, #0x2
  0x54000121#32, -- 0x23c338: b.ne 0x23c35c <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x78>
  0x14000014#32, -- 0x23c33c: b 0x23c38c <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0xa8>
  0x91000680#32, -- 0x23c340: add x0, x20, #0x1
  0x39400269#32, -- 0x23c344: ldrb w9, [x19]
  0xd1005d2a#32, -- 0x23c348: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x23c34c: cmp w9, #0x17
  0x9a9f814a#32, -- 0x23c350: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x23c354: cmp x10, #0x2
  0x540001a0#32, -- 0x23c358: b.eq 0x23c38c <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0xa8>
  0xf100055f#32, -- 0x23c35c: cmp x10, #0x1
  0x540001c1#32, -- 0x23c360: b.ne 0x23c398 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0xb4>
  0xa940a661#32, -- 0x23c364: ldp x1, x9, [x19, #0x8]
  0x1400000d#32, -- 0x23c368: b 0x23c39c <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0xb8>
  0xa940a289#32, -- 0x23c36c: ldp x9, x8, [x20, #0x8]
  0x91004120#32, -- 0x23c370: add x0, x9, #0x10
  0x39400269#32, -- 0x23c374: ldrb w9, [x19]
  0xd1005d2a#32, -- 0x23c378: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x23c37c: cmp w9, #0x17
  0x9a9f814a#32, -- 0x23c380: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x23c384: cmp x10, #0x2
  0x54fffea1#32, -- 0x23c388: b.ne 0x23c35c <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x78>
  0xa940a66a#32, -- 0x23c38c: ldp x10, x9, [x19, #0x8]
  0x91004141#32, -- 0x23c390: add x1, x10, #0x10
  0x14000002#32, -- 0x23c394: b 0x23c39c <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0xb8>
  0x91000661#32, -- 0x23c398: add x1, x19, #0x1
  0xeb090115#32, -- 0x23c39c: subs x21, x8, x9
  0x9a893102#32, -- 0x23c3a0: csel x2, x8, x9, lo
  0x940465e5#32, -- 0x23c3a4: bl 0x355b38 <dyld_stub_binder+0x355b38>
  0x93407c08#32, -- 0x23c3a8: sxtw x8, w0
  0x7100001f#32, -- 0x23c3ac: cmp w0, #0x0
  0x9a8802a8#32, -- 0x23c3b0: csel x8, x21, x8, eq
  0xf100011f#32, -- 0x23c3b4: cmp x8, #0x0
  0x1a9fd7e9#32, -- 0x23c3b8: cset w9, gt
  0x5a9f5120#32, -- 0x23c3bc: csinv w0, w9, wzr, pl
  0xb40000e8#32, -- 0x23c3c0: cbz x8, 0x23c3dc <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0xf8>
  0xa9447bfd#32, -- 0x23c3c4: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0x23c3c8: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0x23c3cc: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0x23c3d0: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0x23c3d4: ldp x26, x25, [sp], #0x50
  0xd65f03c0#32, -- 0x23c3d8: ret
  0xf9400e89#32, -- 0x23c3dc: ldr x9, [x20, #0x18]
  0xf9400e68#32, -- 0x23c3e0: ldr x8, [x19, #0x18]
  0xf9401133#32, -- 0x23c3e4: ldr x19, [x9, #0x20]
  0xf9401114#32, -- 0x23c3e8: ldr x20, [x8, #0x20]
  0xeb13029f#32, -- 0x23c3ec: cmp x20, x19
  0x9a933295#32, -- 0x23c3f0: csel x21, x20, x19, lo
  0xb4000735#32, -- 0x23c3f4: cbz x21, 0x23c4d8 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x1f4>
  0xd2800016#32, -- 0x23c3f8: mov x22, #0x0 ; =0
  0xf9400d37#32, -- 0x23c3fc: ldr x23, [x9, #0x18]
  0xf9400d18#32, -- 0x23c400: ldr x24, [x8, #0x18]
  0x38766ae8#32, -- 0x23c404: ldrb w8, [x23, x22]
  0xd1005d09#32, -- 0x23c408: sub x9, x8, #0x17
  0x71005d1f#32, -- 0x23c40c: cmp w8, #0x17
  0x9a9f8129#32, -- 0x23c410: csel x9, x9, xzr, hi
  0xb4000189#32, -- 0x23c414: cbz x9, 0x23c444 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x160>
  0x8b1602e8#32, -- 0x23c418: add x8, x23, x22
  0xf100053f#32, -- 0x23c41c: cmp x9, #0x1
  0x540002c1#32, -- 0x23c420: b.ne 0x23c478 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x194>
  0xa940a100#32, -- 0x23c424: ldp x0, x8, [x8, #0x8]
  0x38766b09#32, -- 0x23c428: ldrb w9, [x24, x22]
  0xd1005d2a#32, -- 0x23c42c: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x23c430: cmp w9, #0x17
  0x9a9f814a#32, -- 0x23c434: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x23c438: cmp x10, #0x2
  0x54000141#32, -- 0x23c43c: b.ne 0x23c464 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x180>
  0x14000016#32, -- 0x23c440: b 0x23c498 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x1b4>
  0x8b1602e9#32, -- 0x23c444: add x9, x23, x22
  0x91000520#32, -- 0x23c448: add x0, x9, #0x1
  0x38766b09#32, -- 0x23c44c: ldrb w9, [x24, x22]
  0xd1005d2a#32, -- 0x23c450: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x23c454: cmp w9, #0x17
  0x9a9f814a#32, -- 0x23c458: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x23c45c: cmp x10, #0x2
  0x540001c0#32, -- 0x23c460: b.eq 0x23c498 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x1b4>
  0xf100055f#32, -- 0x23c464: cmp x10, #0x1
  0x54000201#32, -- 0x23c468: b.ne 0x23c4a8 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x1c4>
  0x8b160309#32, -- 0x23c46c: add x9, x24, x22
  0xa940a521#32, -- 0x23c470: ldp x1, x9, [x9, #0x8]
  0x1400000f#32, -- 0x23c474: b 0x23c4b0 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x1cc>
  0xa940a109#32, -- 0x23c478: ldp x9, x8, [x8, #0x8]
  0x91004120#32, -- 0x23c47c: add x0, x9, #0x10
  0x38766b09#32, -- 0x23c480: ldrb w9, [x24, x22]
  0xd1005d2a#32, -- 0x23c484: sub x10, x9, #0x17
  0x71005d3f#32, -- 0x23c488: cmp w9, #0x17
  0x9a9f814a#32, -- 0x23c48c: csel x10, x10, xzr, hi
  0xf100095f#32, -- 0x23c490: cmp x10, #0x2
  0x54fffe81#32, -- 0x23c494: b.ne 0x23c464 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x180>
  0x8b160309#32, -- 0x23c498: add x9, x24, x22
  0xa940a52a#32, -- 0x23c49c: ldp x10, x9, [x9, #0x8]
  0x91004141#32, -- 0x23c4a0: add x1, x10, #0x10
  0x14000003#32, -- 0x23c4a4: b 0x23c4b0 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x1cc>
  0x8b16030a#32, -- 0x23c4a8: add x10, x24, x22
  0x91000541#32, -- 0x23c4ac: add x1, x10, #0x1
  0xeb090119#32, -- 0x23c4b0: subs x25, x8, x9
  0x9a893102#32, -- 0x23c4b4: csel x2, x8, x9, lo
  0x940465a0#32, -- 0x23c4b8: bl 0x355b38 <dyld_stub_binder+0x355b38>
  0x93407c08#32, -- 0x23c4bc: sxtw x8, w0
  0x7100001f#32, -- 0x23c4c0: cmp w0, #0x0
  0x9a880328#32, -- 0x23c4c4: csel x8, x25, x8, eq
  0xb50001a8#32, -- 0x23c4c8: cbnz x8, 0x23c4fc <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x218>
  0x910062d6#32, -- 0x23c4cc: add x22, x22, #0x18
  0xf10006b5#32, -- 0x23c4d0: subs x21, x21, #0x1
  0x54fff981#32, -- 0x23c4d4: b.ne 0x23c404 <iCjQZ9Ydc0_17cedar_policy_core3ast4names2_1__NtB4_12InternalNameNtNtCskumHb0IaX0X_4core3cmp3Ord3cmp+0x120>
  0xeb14027f#32, -- 0x23c4d8: cmp x19, x20
  0x1a9f97e8#32, -- 0x23c4dc: cset w8, hi
  0x5a9f2100#32, -- 0x23c4e0: csinv w0, w8, wzr, hs
  0xa9447bfd#32, -- 0x23c4e4: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0x23c4e8: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0x23c4ec: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0x23c4f0: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0x23c4f4: ldp x26, x25, [sp], #0x50
  0xd65f03c0#32, -- 0x23c4f8: ret
  0xf100011f#32, -- 0x23c4fc: cmp x8, #0x0
  0x1a9fd7e8#32, -- 0x23c500: cset w8, gt
  0x5a9f5100#32, -- 0x23c504: csinv w0, w8, wzr, pl
  0xa9447bfd#32, -- 0x23c508: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0x23c50c: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0x23c510: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0x23c514: ldp x24, x23, [sp, #0x10]
  0xa8c567fa#32, -- 0x23c518: ldp x26, x25, [sp], #0x50
  0xd65f03c0#32  -- 0x23c51c: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x23c2e4#64

/-- The addresses of the function's instructions. -/
def pcs : List (BitVec 64) := [0x23c2e4#64, 0x23c2e8#64, 0x23c2ec#64, 0x23c2f0#64, 0x23c2f4#64, 0x23c2f8#64, 0x23c2fc#64, 0x23c300#64, 0x23c304#64, 0x23c308#64, 0x23c30c#64, 0x23c310#64, 0x23c314#64, 0x23c318#64, 0x23c31c#64, 0x23c320#64, 0x23c324#64, 0x23c328#64, 0x23c32c#64, 0x23c330#64, 0x23c334#64, 0x23c338#64, 0x23c33c#64, 0x23c340#64, 0x23c344#64, 0x23c348#64, 0x23c34c#64, 0x23c350#64, 0x23c354#64, 0x23c358#64, 0x23c35c#64, 0x23c360#64, 0x23c364#64, 0x23c368#64, 0x23c36c#64, 0x23c370#64, 0x23c374#64, 0x23c378#64, 0x23c37c#64, 0x23c380#64, 0x23c384#64, 0x23c388#64, 0x23c38c#64, 0x23c390#64, 0x23c394#64, 0x23c398#64, 0x23c39c#64, 0x23c3a0#64, 0x23c3a4#64, 0x23c3a8#64, 0x23c3ac#64, 0x23c3b0#64, 0x23c3b4#64, 0x23c3b8#64, 0x23c3bc#64, 0x23c3c0#64, 0x23c3c4#64, 0x23c3c8#64, 0x23c3cc#64, 0x23c3d0#64, 0x23c3d4#64, 0x23c3d8#64, 0x23c3dc#64, 0x23c3e0#64, 0x23c3e4#64, 0x23c3e8#64, 0x23c3ec#64, 0x23c3f0#64, 0x23c3f4#64, 0x23c3f8#64, 0x23c3fc#64, 0x23c400#64, 0x23c404#64, 0x23c408#64, 0x23c40c#64, 0x23c410#64, 0x23c414#64, 0x23c418#64, 0x23c41c#64, 0x23c420#64, 0x23c424#64, 0x23c428#64, 0x23c42c#64, 0x23c430#64, 0x23c434#64, 0x23c438#64, 0x23c43c#64, 0x23c440#64, 0x23c444#64, 0x23c448#64, 0x23c44c#64, 0x23c450#64, 0x23c454#64, 0x23c458#64, 0x23c45c#64, 0x23c460#64, 0x23c464#64, 0x23c468#64, 0x23c46c#64, 0x23c470#64, 0x23c474#64, 0x23c478#64, 0x23c47c#64, 0x23c480#64, 0x23c484#64, 0x23c488#64, 0x23c48c#64, 0x23c490#64, 0x23c494#64, 0x23c498#64, 0x23c49c#64, 0x23c4a0#64, 0x23c4a4#64, 0x23c4a8#64, 0x23c4ac#64, 0x23c4b0#64, 0x23c4b4#64, 0x23c4b8#64, 0x23c4bc#64, 0x23c4c0#64, 0x23c4c4#64, 0x23c4c8#64, 0x23c4cc#64, 0x23c4d0#64, 0x23c4d4#64, 0x23c4d8#64, 0x23c4dc#64, 0x23c4e0#64, 0x23c4e4#64, 0x23c4e8#64, 0x23c4ec#64, 0x23c4f0#64, 0x23c4f4#64, 0x23c4f8#64, 0x23c4fc#64, 0x23c500#64, 0x23c504#64, 0x23c508#64, 0x23c50c#64, 0x23c510#64, 0x23c514#64, 0x23c518#64, 0x23c51c#64]

/-! Direct-call targets (not part of `prog`). -/
/-- `_memcmp` -/
def ext_0 : BitVec 64 := 0x355b38#64

end Examples.Cedar.NoPanic.Fn.InternalNameCmp2
