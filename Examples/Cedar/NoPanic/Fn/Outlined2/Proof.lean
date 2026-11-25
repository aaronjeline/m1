import Examples.Cedar.NoPanic.Fn.Outlined2.Code
import Examples.Cedar.NoPanic.Spec

/-!
# `_OUTLINED_FUNCTION_2` at `0xe1320`: `add sp, sp, #0x40; ret`

A shared epilogue tail, entered by a tail jump (`b`) after the caller has
reloaded `x29`/`x30`: it pops the caller's 0x40-byte frame and returns to the
caller's caller. It does not follow the AAPCS64 (it changes `SP`), so its
contract is the exact final state rather than an `NP` contract: a caller's
proof replaces the jump by this state.
-/

namespace Examples.Cedar.NoPanic.Fn.Outlined2
open M1 Examples.Cedar.NoPanic

theorem spec (p : Program) (hp : p.Extends prog) :
    SafeSpec p Panic sym_fn (fun _ => True)
      (fun s s' => s' = { s with sp := s.sp + 0x40#64, pc := s.gpr 30 }) := by
  intro n s hpc hst _
  simp only [sym_fn] at hpc
  m1_safe_step
  m1_safe_step
  apply SafeN.done
  refine ⟨rfl, rfl, ?_⟩
  cases s; simp_all

end Examples.Cedar.NoPanic.Fn.Outlined2
