import Examples.Cedar.Proofs
import Examples.Cedar.Eval.Proofs

/-!
# The Cedar assertion, with `eval_expression` proved

`Examples/Cedar/Proofs.lean` proves `verdict` from a contract on
`eval_expression` (`EvalSpec`). `Examples/Cedar/Eval/Proofs.lean` proves
`eval_expression`'s machine code from contracts on *its* callees
(`eval_spec : EvalSpec'`). Here they are composed: the assertion is
unreachable given contracts for `typechecks_in`, for `eval_expression`'s
callees, and for `Evaluator::interpret` (`InterpretSpec`, the type-soundness
assumption, now one layer further down).
-/

namespace Examples.Cedar
open M1 Eval

/-- `typechecks_in`'s contract, also leaving the TLV descriptor alone. -/
def TypechecksSpec' (p : Program) (Valid WT : Memory → BitVec 64 → BitVec 64 → Prop) : Prop :=
  FunSpec p ext_typechecks
    (fun s => s.sp &&& 15#64 = 0#64 ∧ Valid s.mem (s.gpr 0) (s.gpr 1))
    (fun s s' => ((s'.gpr 0).getLsbD 0 = true → WT s'.mem (s.gpr 0) (s.gpr 1)) ∧
      CalleeSaved s s' ∧ FramePreserved 0x100 s s' ∧ s'.mem.read64 tlvDesc = s.mem.read64 tlvDesc)

/-- `verdict`'s precondition: as in `verdict_spec`, plus what `eval_expression`
needs: the TLV descriptor, room on the stack `[lo, top)` for both frames, and
the expression (`x1`) on the stack, outside both frames. -/
def VerdictPre (Valid : Memory → BitVec 64 → BitVec 64 → Prop) (lo top T : BitVec 64) (s : State) : Prop :=
  s.sp &&& 15#64 = 0#64 ∧
  (∀ m : Memory, (∀ a, 0x100 ≤ (a - (s.sp - 0x100#64)).toNat → m a = s.mem a) →
    Valid m (s.gpr 0) (s.gpr 1)) ∧
  Memory.Disjoint (s.gpr 8) 0xd0 (s.sp - 0x100#64) 0x100 ∧
  s.mem.read64 tlvDesc = T ∧ (∀ i < 8, ¬ OnStack lo top (tlvDesc + BitVec.ofNat 64 i)) ∧
  0x450 ≤ (s.sp - lo).toNat ∧ (s.sp - lo).toNat ≤ (top - lo).toNat ∧
  Memory.Disjoint (s.gpr 1) 0x78 (s.sp - 0x450#64) 0x450 ∧
  ∀ i < 0x78, OnStack lo top (s.gpr 1 + BitVec.ofNat 64 i)

theorem sp256_lo (s : State) {lo : BitVec 64} (hlo : 0x450 ≤ (s.sp - lo).toNat) :
    (s.sp - 256#64 - lo).toNat = (s.sp - lo).toNat - 256 := by
  rw [show s.sp - 256#64 - lo = (s.sp - lo) - 256#64 by grind,
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]; omega)]
  simp

theorem lo_eval (s : State) {lo : BitVec 64} (hlo : 0x450 ≤ (s.sp - lo).toNat) :
    0x350 ≤ (s.sp - 256#64 - lo).toNat := by
  rw [sp256_lo s hlo]; omega

theorem top_eval (s : State) {lo top : BitVec 64} (hlo : 0x450 ≤ (s.sp - lo).toNat)
    (htop : (s.sp - lo).toNat ≤ (top - lo).toNat) :
    (s.sp - 256#64 - lo).toNat + 0x100 ≤ (top - lo).toNat := by
  rw [sp256_lo s hlo]; omega

theorem disj_eval (s : State) {e : BitVec 64} (h : Memory.Disjoint e 0x78 (s.sp - 0x450#64) 0x450) :
    Memory.Disjoint e 0x78 (s.sp - 256#64 - 0x350#64) 0x350 := by
  rw [show s.sp - 256#64 - 0x350#64 = s.sp - 0x450#64 by grind]
  exact ⟨h.1, Nat.le_trans (by decide) h.2⟩

/-- Bytes of `verdict`'s frame are on the stack. -/
theorem onStack_v (s : State) {lo top : BitVec 64} (hlo : 0x450 ≤ (s.sp - lo).toNat)
    (htop : (s.sp - lo).toNat ≤ (top - lo).toNat) (c : BitVec 64) (n : Nat) (hc : c.toNat + n ≤ 256) :
    ∀ j < n, OnStack lo top (s.sp - 256#64 + c + BitVec.ofNat 64 j) := by
  intro j hj
  unfold OnStack
  rw [show s.sp - 256#64 + c + BitVec.ofNat 64 j - lo = (s.sp - 256#64 - lo) + (c + BitVec.ofNat 64 j) by
    grind, BitVec.toNat_add, BitVec.toNat_add, sp256_lo s hlo]
  simp only [BitVec.toNat_ofNat]
  have := (top - lo).isLt
  omega

theorem verdict_spec' (p : Program) (hp : p.Extends prog)
    (Valid : Memory → BitVec 64 → BitVec 64 → Prop) (P : Eval.Preds) (lo top T : BitVec 64)
    (htc : TypechecksSpec' p Valid P.WT) (hev : Eval.EvalSpec' P lo top p T) :
    FunSpec p sym_verdict (VerdictPre Valid lo top T)
      (fun s s' => (s'.mem.read32 (s.gpr 8)).toNat ∈ [1, 2, 3]) := by
  intro s hpc hst ⟨hsp, hval, hdisj, htlv, htlvoff, hlo, htop, hedisj, heon⟩
  simp only [sym_verdict] at hpc
  have hsp' : s.sp - 256#64 &&& 15#64 = 0#64 := by bv_decide
  have hd := disj_sub hdisj
  have hd0 := disj_sub0 hdisj
  m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
  -- bl typechecks_in
  refine Reaches.trans (htc _ rfl rfl ⟨hsp', hval _ ?_⟩) ?_
  · intro a ha
    simp only [frame_write64 ha, BitVec.reduceToNat, Nat.reduceAdd, Nat.reduceLeDiff]
  rintro s2 ⟨h2pc, h2st, h2tc, ⟨h2r, h2sp, h2v, h2fpcr⟩, h2fr, h2tlv⟩
  -- The prologue's stores (on the stack) keep the TLV descriptor (off the stack).
  have htlv2 : s2.mem.read64 tlvDesc = T := by
    rw [h2tlv, ← htlv]
    apply Memory.read64_congr
    intro i hi
    dsimp only
    have hst : ∀ c n, c.toNat + n ≤ 256 → n ≤ (tlvDesc + BitVec.ofNat 64 i - (s.sp - 256#64 + c)).toNat :=
      fun c n hc => Mem.far_of (Q := fun x => ¬ OnStack lo top x) (htlvoff i hi) fun j hj hn =>
        hn (onStack_v s hlo htop c n hc j hj)
    simp (disch := (apply hst; simp only [BitVec.reduceToNat]; omega)) only [write64_keep]
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
    refine Reaches.trans (hev _ rfl rfl ⟨hsp', by simp [upd], by simpa [upd] using hwt, by simp [upd],
      htlv2, htlvoff, lo_eval s hlo, top_eval s hlo htop,
      by simpa [upd] using disj_eval s hedisj, by simpa [upd] using heon⟩) ?_
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


/-- **The type-soundness assertion is unreachable**, with `eval_expression`'s
machine code proved. Started at `verdict` in a state meeting `VerdictPre`, in
any program that extends the code of `verdict` (with the assertion) and of
`eval_expression`, and whose remaining callees meet their contracts:

* `typechecks_in` (`TypechecksSpec'`): returns `true` only for well-typed
  expressions;
* `eval_expression`'s callees (`Eval.Callees`, `Eval.Frames`, `Eval.Facts`):
  `Extensions::all_available`, `Request::clone`, `Evaluator::new`, the
  `KEYS` TLV thunk, `hashmap_random_keys`, `EvalResult::from` and three drop
  functions, with the footprints of the abstract objects;
* `Evaluator::interpret` (`Eval.InterpretSpec`): **type soundness**, on a
  well-typed expression the result is not `Err(TypeError)`;

execution returns to the caller still running, and no state before the
return is at `type_soundness_violation`. -/
theorem violation_unreachable' (p : Program) (hp : p.Extends prog) (hpe : p.Extends Eval.prog)
    (Valid : Memory → BitVec 64 → BitVec 64 → Prop) (P : Eval.Preds) (lo top T : BitVec 64)
    (htc : TypechecksSpec' p Valid P.WT) (hc : Eval.Callees P lo top p T)
    (hfr : Eval.Frames P lo top) (hf : Eval.Facts P lo top) (hi : Eval.InterpretSpec P top p)
    (s : State) (hpc : s.pc = sym_verdict) (hst : s.status = .running)
    (hpre : VerdictPre Valid lo top T s) :
    ∃ n, (run p n s).pc = s.gpr 30 ∧ (run p n s).status = .running ∧
      ∀ k < n, (run p k s).pc ≠ sym_violation := by
  have hev := Eval.eval_spec P lo top p hpe T hc hfr hf hi
  obtain ⟨n, hret, hrun, -⟩ := verdict_spec' p hp Valid P lo top T htc hev s hpc hst hpre
  refine ⟨n, hret, hrun, fun k hk hat => ?_⟩
  have hk1 := running_before p s n hrun (k + 1) hk
  have hk0 := running_before p s n hrun k (Nat.le_of_lt hk)
  rw [run_add p k 1 s] at hk1
  have := violation_brk p hp (run p k s) hat hk0
  simp only [run, this] at hk1
  cases hk1

end Examples.Cedar
