/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvNtNtCskumHb0IaX0X_4core5slice6memchr14memchr_aligned`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.MemchrAligned
open M1

def textBase : BitVec 64 := 0x34fae0#64

def text : List (BitVec 32) := [
  0x12001c09#32, -- 0x34fae0: and w9, w0, #0xff
  0x91001c28#32, -- 0x34fae4: add x8, x1, #0x7
  0x927df108#32, -- 0x34fae8: and x8, x8, #0xfffffffffffffff8
  0xeb010108#32, -- 0x34faec: subs x8, x8, x1
  0x54000081#32, -- 0x34faf0: b.ne 0x34fb00 <IaX0X_4core5slice6memchr14memchr_aligned+0x20>
  0xd280000a#32, -- 0x34faf4: mov x10, #0x0 ; =0
  0xd100404b#32, -- 0x34faf8: sub x11, x2, #0x10
  0x14000010#32, -- 0x34fafc: b 0x34fb3c <IaX0X_4core5slice6memchr14memchr_aligned+0x5c>
  0xeb08005f#32, -- 0x34fb00: cmp x2, x8
  0x9a88304a#32, -- 0x34fb04: csel x10, x2, x8, lo
  0xb4000122#32, -- 0x34fb08: cbz x2, 0x34fb2c <IaX0X_4core5slice6memchr14memchr_aligned+0x4c>
  0xd2800008#32, -- 0x34fb0c: mov x8, #0x0 ; =0
  0x52800020#32, -- 0x34fb10: mov w0, #0x1 ; =1
  0x3868682b#32, -- 0x34fb14: ldrb w11, [x1, x8]
  0x6b09017f#32, -- 0x34fb18: cmp w11, w9
  0x540004c0#32, -- 0x34fb1c: b.eq 0x34fbb4 <IaX0X_4core5slice6memchr14memchr_aligned+0xd4>
  0x91000508#32, -- 0x34fb20: add x8, x8, #0x1
  0xeb08015f#32, -- 0x34fb24: cmp x10, x8
  0x54ffff61#32, -- 0x34fb28: b.ne 0x34fb14 <IaX0X_4core5slice6memchr14memchr_aligned+0x34>
  0xd100404b#32, -- 0x34fb2c: sub x11, x2, #0x10
  0xaa0a03e8#32, -- 0x34fb30: mov x8, x10
  0xeb0b015f#32, -- 0x34fb34: cmp x10, x11
  0x540002a8#32, -- 0x34fb38: b.hi 0x34fb8c <IaX0X_4core5slice6memchr14memchr_aligned+0xac>
  0xb200c3ec#32, -- 0x34fb3c: mov x12, #0x101010101010101 ; =72340172838076673
  0xf280200c#32, -- 0x34fb40: movk x12, #0x100
  0xb200c3e8#32, -- 0x34fb44: mov x8, #0x101010101010101 ; =72340172838076673
  0x9b087d2d#32, -- 0x34fb48: mul x13, x9, x8
  0xb201c3ee#32, -- 0x34fb4c: mov x14, #-0x7f7f7f7f7f7f7f80 ; =-9187201950435737472
  0xaa0a03e8#32, -- 0x34fb50: mov x8, x10
  0x8b08002a#32, -- 0x34fb54: add x10, x1, x8
  0xa940294f#32, -- 0x34fb58: ldp x15, x10, [x10]
  0xca0d01ef#32, -- 0x34fb5c: eor x15, x15, x13
  0xcb0f0190#32, -- 0x34fb60: sub x16, x12, x15
  0xaa0f020f#32, -- 0x34fb64: orr x15, x16, x15
  0xca0d014a#32, -- 0x34fb68: eor x10, x10, x13
  0xcb0a0190#32, -- 0x34fb6c: sub x16, x12, x10
  0xaa0a020a#32, -- 0x34fb70: orr x10, x16, x10
  0x8a0a01ea#32, -- 0x34fb74: and x10, x15, x10
  0xea2a01df#32, -- 0x34fb78: bics xzr, x14, x10
  0x54000081#32, -- 0x34fb7c: b.ne 0x34fb8c <IaX0X_4core5slice6memchr14memchr_aligned+0xac>
  0x91004108#32, -- 0x34fb80: add x8, x8, #0x10
  0xeb0b011f#32, -- 0x34fb84: cmp x8, x11
  0x54fffe69#32, -- 0x34fb88: b.ls 0x34fb54 <IaX0X_4core5slice6memchr14memchr_aligned+0x74>
  0xeb08005f#32, -- 0x34fb8c: cmp x2, x8
  0x54000100#32, -- 0x34fb90: b.eq 0x34fbb0 <IaX0X_4core5slice6memchr14memchr_aligned+0xd0>
  0x52800020#32, -- 0x34fb94: mov w0, #0x1 ; =1
  0x3868682a#32, -- 0x34fb98: ldrb w10, [x1, x8]
  0x6b09015f#32, -- 0x34fb9c: cmp w10, w9
  0x540000a0#32, -- 0x34fba0: b.eq 0x34fbb4 <IaX0X_4core5slice6memchr14memchr_aligned+0xd4>
  0x91000508#32, -- 0x34fba4: add x8, x8, #0x1
  0xeb08005f#32, -- 0x34fba8: cmp x2, x8
  0x54ffff61#32, -- 0x34fbac: b.ne 0x34fb98 <IaX0X_4core5slice6memchr14memchr_aligned+0xb8>
  0xd2800000#32, -- 0x34fbb0: mov x0, #0x0 ; =0
  0xaa0803e1#32, -- 0x34fbb4: mov x1, x8
  0xd65f03c0#32  -- 0x34fbb8: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x34fae0#64

/-- The addresses of the function's instructions. -/
def pcs : List (BitVec 64) := [0x34fae0#64, 0x34fae4#64, 0x34fae8#64, 0x34faec#64, 0x34faf0#64, 0x34faf4#64, 0x34faf8#64, 0x34fafc#64, 0x34fb00#64, 0x34fb04#64, 0x34fb08#64, 0x34fb0c#64, 0x34fb10#64, 0x34fb14#64, 0x34fb18#64, 0x34fb1c#64, 0x34fb20#64, 0x34fb24#64, 0x34fb28#64, 0x34fb2c#64, 0x34fb30#64, 0x34fb34#64, 0x34fb38#64, 0x34fb3c#64, 0x34fb40#64, 0x34fb44#64, 0x34fb48#64, 0x34fb4c#64, 0x34fb50#64, 0x34fb54#64, 0x34fb58#64, 0x34fb5c#64, 0x34fb60#64, 0x34fb64#64, 0x34fb68#64, 0x34fb6c#64, 0x34fb70#64, 0x34fb74#64, 0x34fb78#64, 0x34fb7c#64, 0x34fb80#64, 0x34fb84#64, 0x34fb88#64, 0x34fb8c#64, 0x34fb90#64, 0x34fb94#64, 0x34fb98#64, 0x34fb9c#64, 0x34fba0#64, 0x34fba4#64, 0x34fba8#64, 0x34fbac#64, 0x34fbb0#64, 0x34fbb4#64, 0x34fbb8#64]

/-! Direct-call targets (not part of `prog`). -/


end Examples.Cedar.NoPanic.Fn.MemchrAligned
