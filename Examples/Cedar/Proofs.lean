import Examples.Cedar.Code

/-!
# The Cedar type-soundness assertion is unreachable

`targets/cedar-check` checks a Cedar expression: it parses it, typechecks it,
evaluates it, and if evaluation of a well-typed expression raises a type error
it executes `brk #0xc0de` (`type_soundness_violation`). The only call to that
function is in `verdict`, whose machine code (`Code.lean`, extracted from the
M1 build) is verified here: started in any state meeting its precondition,
`verdict` returns to its caller still running, so it never executes the
`brk`.

`verdict` calls two functions whose code is not part of `prog`:
`typechecks_in` (Cedar's validator) and `eval_expression` (Cedar's
evaluator). As in `Examples/Ext`, the theorem holds for every program `p`
extending `prog` that satisfies their contracts, which are hypotheses:

* `TypechecksSpec`: called on valid inputs, `typechecks_in(env, expr)`
  returns per the AAPCS64 without writing its caller's frame, and when it
  returns `true` the expression is well-typed (`WT`).
* `EvalSpec`: `eval_expression` on a well-typed expression returns a result
  that is not `Err(EvaluationError::TypeError(_))`. This is the soundness of
  Cedar's typechecker with respect to its evaluator, assumed here, not
  proved: it is about the code of the validator and evaluator, outside
  `prog`.

`Valid` and `WT` are abstract predicates (any predicates for which the
contracts hold), so the result does not depend on how they are defined.

What the theorem establishes about the machine code is everything else: that
the compiled control flow reaches the `brk` only when `eval_expression`
returns the encoding of `Err(TypeError)` (a first word below 7 in rustc's
layout of `Result<EvalResult, EvaluationError>`), that the expression
evaluated is the one that was typechecked, that the environment passed to
both is the same, and that every other path returns to the caller with the
`Outcome` written.
-/

namespace Examples.Cedar
open M1

/-- Contract of `typechecks_in(env, expr)` (`x0` = `env`, `x1` = `expr`):
returns, with bit 0 of `w0` set only if the expression is well-typed, and
does not write the 256 bytes above its entry `SP` (its caller's frame). -/
def TypechecksSpec (p : Program) (Valid WT : Memory → BitVec 64 → BitVec 64 → Prop) : Prop :=
  FunSpec p ext_typechecks
    (fun s => s.sp &&& 15#64 = 0#64 ∧ Valid s.mem (s.gpr 0) (s.gpr 1))
    (fun s s' => ((s'.gpr 0).getLsbD 0 = true → WT s'.mem (s.gpr 0) (s.gpr 1)) ∧
      CalleeSaved s s' ∧ FramePreserved 0x100 s s')

/-- Contract of `eval_expression(&request, &entities, expr)` with the result
written at `x8`: for a well-typed expression (`x0` = the environment, whose
request is its first field and whose entities are at offset `0x1b0`), the
result's first word is not below 7, i.e. the result is not
`Err(EvaluationError::TypeError(_))`. Within the 256 bytes above its entry
`SP` it writes only the 200-byte result. -/
def EvalSpec (p : Program) (WT : Memory → BitVec 64 → BitVec 64 → Prop) : Prop :=
  FunSpec p ext_eval
    (fun s => s.sp &&& 15#64 = 0#64 ∧ s.gpr 1 = s.gpr 0 + 0x1b0#64 ∧ WT s.mem (s.gpr 0) (s.gpr 2))
    (fun s s' => 7 ≤ (s'.mem.read64 (s.gpr 8)).toNat ∧ CalleeSaved s s' ∧
      ∀ a, (a - s.sp).toNat < 0x100 → 0xc8 ≤ (a - s.gpr 8).toNat → s'.mem a = s.mem a)

/-! ### Memory facts -/

/-- A sub-range of the output object (`o + c`, within its `0xd0` bytes) is
disjoint from a sub-range of `verdict`'s frame (`F + e`, within its `0x100`
bytes), given that the two are disjoint. -/
theorem disj_sub {o F : BitVec 64} (h : Memory.Disjoint o 0xd0 F 0x100)
    (c e : BitVec 64) (n k : Nat) (hn : 0 < n) (hk : 0 < k) (hc : c.toNat + n ≤ 0xd0)
    (he : e.toNat + k ≤ 0x100) :
    Memory.Disjoint (o + c) n (F + e) k := by
  obtain ⟨h1, h2⟩ := h
  -- Y = o - F and Z = F - o add up to 2^64 (they are both nonzero).
  have hsum : (o - F).toNat + (F - o).toNat = 2 ^ 64 := by
    have h0 : (o - F + (F - o)).toNat = 0 := by
      rw [show o - F + (F - o) = 0#64 by grind]; rfl
    rw [BitVec.toNat_add] at h0
    have := (o - F).isLt; have := (F - o).isLt
    omega
  have hcl := c.isLt; have hel := e.isLt
  constructor
  · -- (F + e) - (o + c) = (F - o) + e - c, without wrap-around.
    rw [show F + e - (o + c) = (F - o + e) - c by grind]
    have ha : (F - o + e).toNat = (F - o).toNat + e.toNat :=
      BitVec.toNat_add_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (x := F - o + e) (y := c) (by rw [BitVec.le_def, ha]; omega), ha]
    omega
  · rw [show o + c - (F + e) = (o - F + c) - e by grind]
    have ha : (o - F + c).toNat = (o - F).toNat + c.toNat :=
      BitVec.toNat_add_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (x := o - F + c) (y := e) (by rw [BitVec.le_def, ha]; omega), ha]
    omega

theorem disj_sub0 {o F : BitVec 64} (h : Memory.Disjoint o 0xd0 F 0x100)
    (e : BitVec 64) (n k : Nat) (hn : 0 < n) (hk : 0 < k) (hc : n ≤ 0xd0)
    (he : e.toNat + k ≤ 0x100) :
    Memory.Disjoint o n (F + e) k := by
  have := disj_sub h 0 e n k hn hk (by simpa using hc) he
  simpa using this

/-- A write of 8 bytes inside `verdict`'s frame (`F + off`) leaves every byte
at least 256 bytes above `F` unchanged. -/
theorem frame_write64 {m : Memory} {F x : BitVec 64} (h : 256 ≤ (x - F).toNat)
    (off : BitVec 64) (v : BitVec 64) (ho : off.toNat + 8 ≤ 256) :
    (m.write64 (F + off) v) x = m x := by
  rw [Memory.writes64 m _ v x]
  have hl := (x - F).isLt
  rw [show x - (F + off) = (x - F) - off by grind,
    BitVec.toNat_sub_of_le (x := x - F) (y := off) (by rw [BitVec.le_def]; omega)]
  simp only [ite_eq_right_iff]
  omega

/-- `eval_expression`'s frame clause, for the 8 bytes at `sp + off` with
`off ≥ 0xd0` (above its 200-byte result at `sp + 8`). -/
theorem eval_keeps {m m' : Memory} {sp : BitVec 64}
    (h : ∀ a, (a - sp).toNat < 0x100 → 0xc8 ≤ (a - (sp + 8#64)).toNat → m' a = m a)
    (off : Nat) (h1 : 0xd0 ≤ off) (h2 : off + 8 ≤ 0x100) :
    m'.read64 (sp + BitVec.ofNat 64 off) = m.read64 (sp + BitVec.ofNat 64 off) := by
  apply Memory.read64_congr
  intro i hi
  apply h
  · rw [BitVec.add_assoc, BitVec.add_comm sp, BitVec.add_sub_cancel]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · rw [show sp + BitVec.ofNat 64 off + BitVec.ofNat 64 i - (sp + 8#64) =
        BitVec.ofNat 64 off + BitVec.ofNat 64 i - 8#64 by bv_omega]
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- `CMN a, b` (`ADDS XZR, a, b`) followed by `B.EQ`. -/
theorem cond_eq_cmn (a b : BitVec 64) :
    conditionHolds 0#4 (addSub true false a b false).2 = (a + b == 0#64) := by
  simp [conditionHolds, addSub, addWithCarry]

/-! ### Stopped machines stay stopped -/

theorem run_stopped (p : Program) (s : State) (h : s.status ≠ .running) (n : Nat) :
    run p n s = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ]
    have : step p s = s := by
      unfold step; split
      · contradiction
      · rfl
    rw [this, ih]

/-- If the machine is running after `n` steps, it was running at every
earlier step: no `brk` (or any other stop) happened on the way. -/
theorem running_before (p : Program) (s : State) (n : Nat) (h : (run p n s).status = .running) :
    ∀ k ≤ n, (run p k s).status = .running := by
  intro k hk
  by_cases hne : (run p k s).status = .running
  · exact hne
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [run_add, run_stopped p _ hne] at h
    exact absurd h hne

/-! ### `verdict` -/

theorem verdict_spec (p : Program) (hp : p.Extends prog)
    (Valid WT : Memory → BitVec 64 → BitVec 64 → Prop)
    (htc : TypechecksSpec p Valid WT) (hev : EvalSpec p WT) :
    FunSpec p sym_verdict
      (fun s => s.sp &&& 15#64 = 0#64 ∧
        (∀ m : Memory, (∀ a, 0x100 ≤ (a - (s.sp - 0x100#64)).toNat → m a = s.mem a) →
          Valid m (s.gpr 0) (s.gpr 1)) ∧
        Memory.Disjoint (s.gpr 8) 0xd0 (s.sp - 0x100#64) 0x100)
      (fun s s' => (s'.mem.read32 (s.gpr 8)).toNat ∈ [1, 2, 3]) := by
  intro s hpc hst ⟨hsp, hval, hdisj⟩
  simp only [sym_verdict] at hpc
  have hsp' : s.sp - 256#64 &&& 15#64 = 0#64 := by bv_decide
  have hd := disj_sub hdisj
  have hd0 := disj_sub0 hdisj
  m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
  -- bl typechecks_in
  refine Reaches.trans (htc _ rfl rfl ⟨hsp', hval _ ?_⟩) ?_
  · intro a ha
    simp only [frame_write64 ha, BitVec.reduceToNat, Nat.reduceAdd, Nat.reduceLeDiff]
  rintro s2 ⟨h2pc, h2st, h2tc, ⟨h2r, h2sp, h2v, h2fpcr⟩, h2fr⟩
  have h2fp := h2fr.read64 0xf0
  have h2lr := h2fr.read64 0xf8
  have h2x19 := h2r 19 (by decide) (by decide)
  have h2x20 := h2r 20 (by decide) (by decide)
  have h2x21 := h2r 21 (by decide) (by decide)
  simp only [upd, BitVec.reduceEq, ite_true, ite_false, BitVec.ofNat_eq_ofNat] at h2pc h2sp h2fp h2lr h2x19 h2x20 h2x21 h2tc
  simp only [Memory.read64_write64_same, Memory.read64_write64_of_disjoint, Memory.disjoint_add_add,
    Memory.disjoint_ofNat, BitVec.reduceSub, BitVec.reduceToNat, Nat.reduceLeDiff, and_self] at h2fp h2lr
  cases hb : (s2.gpr 0#5).getLsbD 0
  · -- `typechecks_in` returned false: `Outcome::IllTyped` (1).
    m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
    exact Reaches.done ⟨rfl, rfl, by simp⟩
  · -- Well-typed: `eval_expression` (result at `sp + 8`).
    have hwt := h2tc hb
    m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
    refine Reaches.trans (hev _ rfl rfl ⟨hsp', by simp [upd], by simpa [upd] using hwt⟩) ?_
    rintro s4 ⟨h4pc, h4st, h4tag, ⟨h4r, h4sp, h4v, h4fpcr⟩, h4keep⟩
    have h4x19 := h4r 19 (by decide) (by decide)
    simp only [upd, BitVec.reduceEq, ite_true, ite_false, BitVec.ofNat_eq_ofNat, h2x19] at h4pc h4sp h4x19 h4tag h4keep
    have h4fp := eval_keeps h4keep 240 (by decide) (by decide)
    have h4lr := eval_keeps h4keep 248 (by decide) (by decide)
    simp only [h2fp, h2lr] at h4fp h4lr
    -- The result tag is not `Err(TypeError)`'s (below 7).
    generalize ht : s4.mem.read64 (s.sp - 256#64 + 8#64) = t at h4tag
    have hn7 : ¬ t < 7#64 := by rw [BitVec.lt_def]; simp; omega
    have hcmn := cond_eq_cmn
    m1_step; m1_step
    by_cases h1 : t + 1#64 = 0#64
    · -- `Ok(v)`: `Outcome::Value` (2).
      m1_step
      m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
      m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
      exact Reaches.done ⟨rfl, rfl, by simp⟩
    · -- Neither `Ok` nor `Err(TypeError)`: `Outcome::EvalError` (3). The `b.lo`
      -- to `type_soundness_violation` is not taken: this is the assertion.
      m1_step; m1_step; m1_step
      m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
      m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
      m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
      m1_step; m1_step; m1_step
      exact Reaches.done ⟨rfl, rfl, by simp⟩

/-! ### The assertion is unreachable -/

/-- Executing `type_soundness_violation` stops the machine with `brk #0xc0de`. -/
theorem violation_brk (p : Program) (hp : p.Extends prog) (s : State)
    (hpc : s.pc = sym_violation) (hst : s.status = .running) :
    (step p s).status = .brk 0xc0de#16 := by
  simp only [sym_violation] at hpc
  rw [step_of_extends hp s (by m1_simp_step)]
  m1_simp_step

/-- **The type-soundness assertion is unreachable.** Started at `verdict` in
a state meeting its precondition, in any program that extends this code and
whose `typechecks_in` and `eval_expression` meet their contracts (the latter
being Cedar's type soundness), execution returns to the caller still
running, and no state before the return is at `type_soundness_violation`:
the `brk #0xc0de` is never executed. -/
theorem violation_unreachable (p : Program) (hp : p.Extends prog)
    (Valid WT : Memory → BitVec 64 → BitVec 64 → Prop)
    (htc : TypechecksSpec p Valid WT) (hev : EvalSpec p WT) (s : State)
    (hpc : s.pc = sym_verdict) (hst : s.status = .running)
    (hsp : s.sp &&& 15#64 = 0#64)
    (hval : ∀ m : Memory, (∀ a, 0x100 ≤ (a - (s.sp - 0x100#64)).toNat → m a = s.mem a) →
      Valid m (s.gpr 0) (s.gpr 1))
    (hdisj : Memory.Disjoint (s.gpr 8) 0xd0 (s.sp - 0x100#64) 0x100) :
    ∃ n, (run p n s).pc = s.gpr 30 ∧ (run p n s).status = .running ∧
      ∀ k < n, (run p k s).pc ≠ sym_violation := by
  obtain ⟨n, hret, hrun, -⟩ := verdict_spec p hp Valid WT htc hev s hpc hst ⟨hsp, hval, hdisj⟩
  refine ⟨n, hret, hrun, fun k hk hat => ?_⟩
  have hk1 := running_before p s n hrun (k + 1) hk
  have hk0 := running_before p s n hrun k (Nat.le_of_lt hk)
  rw [run_add p k 1 s] at hk1
  have := violation_brk p hp (run p k s) hat hk0
  simp only [run, this] at hk1
  cases hk1

end Examples.Cedar
