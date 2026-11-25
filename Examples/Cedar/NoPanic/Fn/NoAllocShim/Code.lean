/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvCs9hJ03s5DiqP_7___rustc35___rust_no_alloc_shim_is_unstable_v2`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.NoAllocShim
open M1

def textBase : BitVec 64 := 0x2709c#64

def text : List (BitVec 32) := [
  0xd65f03c0#32  -- 0x2709c: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x2709c#64

/-! Direct-call targets (not part of `prog`). -/


end Examples.Cedar.NoPanic.Fn.NoAllocShim
