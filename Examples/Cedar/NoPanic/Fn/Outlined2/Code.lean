/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `_OUTLINED_FUNCTION_2`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.Outlined2
open M1

def textBase : BitVec 64 := 0xe1320#64

def text : List (BitVec 32) := [
  0x910103ff#32, -- 0xe1320: add sp, sp, #0x40
  0xd65f03c0#32  -- 0xe1324: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0xe1320#64

/-! Direct-call targets (not part of `prog`). -/


end Examples.Cedar.NoPanic.Fn.Outlined2
