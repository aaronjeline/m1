/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `_OUTLINED_FUNCTION_0`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.Outlined0
open M1

def textBase : BitVec 64 := 0xe1300#64

def text : List (BitVec 32) := [
  0xd10007a8#32, -- 0xe1300: sub x8, x29, #0x1
  0xf9000fe8#32, -- 0xe1304: str x8, [sp, #0x18]
  0x910023e8#32, -- 0xe1308: add x8, sp, #0x8
  0xf81f03a8#32, -- 0xe130c: stur x8, [x29, #-0x10]
  0xd65f03c0#32  -- 0xe1310: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0xe1300#64

/-! Direct-call targets (not part of `prog`). -/


end Examples.Cedar.NoPanic.Fn.Outlined0
