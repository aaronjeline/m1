import Examples.Calls.Code

namespace Examples.Calls
open M1

/-- `sq` squares its argument and changes nothing else (it is a leaf). -/
theorem sq_spec : FunSpec prog sym_sq (fun _ => True)
    (fun s s' => s'.gpr 0 = s.gpr 0 * s.gpr 0 ∧ (∀ r, r ≠ 0#5 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem) := by
  intro s hpc hst _
  simp only [sym_sq] at hpc
  m1_step; m1_step
  refine Reaches.done ⟨rfl, rfl, by simp [upd], fun r hr => by simp [upd, hr], rfl, rfl⟩

/-- `sumsq` (a non-leaf function with a stack frame and two calls) returns
`a*a + b*b`, preserves the callee-saved registers it uses and restores SP.
The only precondition is the ABI's 16-byte stack alignment. -/
theorem sumsq_spec : FunSpec prog sym_sumsq (fun s => s.sp &&& 15#64 = 0#64)
    (fun s s' => s'.gpr 0 = s.gpr 0 * s.gpr 0 + s.gpr 1 * s.gpr 1 ∧
      s'.gpr 19 = s.gpr 19 ∧ s'.gpr 20 = s.gpr 20 ∧ s'.gpr 29 = s.gpr 29 ∧ s'.sp = s.sp) := by
  intro s hpc hst hsp
  simp only [sym_sumsq] at hpc
  m1_step; m1_step; m1_step; m1_step; m1_step
  -- first call: bl _sq
  refine Reaches.trans (sq_spec _ rfl rfl trivial) ?_
  rintro s1 ⟨h1pc, h1st, h1x0, h1r, h1sp, h1mem⟩
  m1_step; m1_step; m1_step
  -- second call
  refine Reaches.trans (sq_spec _ rfl rfl trivial) ?_
  rintro s2 ⟨h2pc, h2st, h2x0, h2r, h2sp, h2mem⟩
  m1_step; m1_step; m1_step; m1_step
  refine Reaches.done ?_
  simp only [upd, BitVec.reduceEq, ite_true, ite_false]
  exact ⟨trivial, trivial, BitVec.add_comm _ _, trivial, trivial, trivial, trivial⟩

end Examples.Calls
