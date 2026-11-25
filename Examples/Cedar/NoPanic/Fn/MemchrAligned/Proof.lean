import Examples.Cedar.NoPanic.Fn.MemchrAligned.Code
import Examples.Cedar.NoPanic.Frame

/-!
# `core::slice::memchr::memchr_aligned` at `0x34fae0`

A leaf (no frame, no stores, three loops): it reads memory and returns
`Option<usize>` in `(x0, x1)`. Its contract (`np`) has no precondition (loads
cannot fault in the model) and says nothing about the result: it never
panics, and changes nothing its caller can see. Proved with the
whole-function invariant `leaf_np` (one symbolic step per instruction).
-/

set_option linter.unusedSimpArgs false

namespace Examples.Cedar.NoPanic.Fn.MemchrAligned
open M1 Examples.Cedar.Eval Examples.Cedar.NoPanic

theorem np (p : Program) (hp : p.Extends prog) (top : BitVec 64) :
    NP p top sym_fn (fun _ => True) (fun _ => 0#64) 0 (fun _ _ => True) := by
  refine leaf_np pcs (by decide) ?_
  leaf_auto pcs

end Examples.Cedar.NoPanic.Fn.MemchrAligned
