import Examples.Cedar.NoPanic.Fn.NoAllocShim.Code
import Examples.Cedar.NoPanic.Lemmas

/-!
# `__rust_no_alloc_shim_is_unstable_v2` at `0x2709c`: `ret`

Called before every `__rust_alloc`; a single `ret` in this build. Its
contract is proved, not assumed: it returns at once and changes nothing.
-/

namespace Examples.Cedar.NoPanic.Fn.NoAllocShim
open M1 Examples.Cedar.Eval Examples.Cedar.NoPanic

theorem np (p : Program) (hp : p.Extends prog) (top : BitVec 64) :
    NP p top sym_fn (fun _ => True) (fun _ => 0#64) 0 (fun s s' => s' = { s with pc := s.gpr 30 }) := by
  rintro n s hpc hst -
  simp only [sym_fn] at hpc
  m1_safe_step
  exact SafeN.done ⟨rfl, rfl, CalleeSaved.refl _, Keeps.of_mem rfl, rfl, by cases s; simp_all⟩

end Examples.Cedar.NoPanic.Fn.NoAllocShim
