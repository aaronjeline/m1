import Examples.Basic.Code

namespace Examples.Basic
open M1

/-- `max` returns the signed maximum of its arguments. -/
theorem max_correct : FunSpec prog sym_max (fun _ => True)
    (fun s s' => s'.gpr 0 = if (s.gpr 1).slt (s.gpr 0) then s.gpr 0 else s.gpr 1) := by
  intro s hpc hst _
  simp only [sym_max] at hpc
  m1_step; m1_step; m1_step
  exact Reaches.done (by simp)

theorem gcd_correct : FunSpec prog sym_gcd (fun _ => True)
    (fun s s' => (s'.gpr 0).toNat = Nat.gcd (s.gpr 0).toNat (s.gpr 1).toNat) := by
  intro s hpc hst _
  simp only [sym_gcd] at hpc
  m1_step
  apply Reaches.ite
  · intro h
    m1_step
    exact Reaches.done (by simp)
  · intro h
    refine Reaches.loop
      (fun t => t.pc = 0x320#64 ∧ t.status = .running ∧ t.gpr 30 = s.gpr 30 ∧ t.gpr 1 ≠ 0 ∧
        Nat.gcd (t.gpr 0).toNat (t.gpr 1).toNat = Nat.gcd (s.gpr 0).toNat (s.gpr 1).toNat)
      (fun t => (t.gpr 1).toNat) ?_ _ ⟨rfl, rfl, rfl, h, rfl⟩
    rintro t ⟨tpc, tst, tlr, tnz, tg⟩
    m1_step; m1_step; m1_step; m1_step; m1_step
    apply Reaches.ite
    · -- remainder non-zero: back to the loop head
      intro hr
      refine Reaches.done (Or.inl ⟨⟨rfl, rfl, by simpa using tlr, by simpa using hr, ?_⟩, ?_⟩)
      · simp only [upd, BitVec.reduceEq, BitVec.toNat_umod, ite_false, ite_true]
        rw [← tg, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
      · have : 0 < (t.gpr 1#5).toNat := by
          rcases Nat.eq_zero_or_pos (t.gpr 1#5).toNat with h0 | h0
          · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) tnz
          · exact h0
        simp only [upd, BitVec.reduceEq, BitVec.toNat_umod, ite_false, ite_true]
        exact Nat.mod_lt _ this
    · -- remainder zero: return t.gpr 1
      intro hr
      m1_step; m1_step
      refine Reaches.done (Or.inr ⟨by simp, rfl, ?_⟩)
      simp only [upd, BitVec.reduceEq, ite_false, ite_true] at hr ⊢
      rw [← tg]
      have hr' : (t.gpr 0#5).toNat % (t.gpr 1#5).toNat = 0 := by
        simpa using congrArg BitVec.toNat (Classical.not_not.mp hr)
      exact (Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero hr')).symm

/-- Sum (mod 2^64) of the first `k` 64-bit words at `p`. -/
def arraySum (m : Memory) (p : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | k + 1 => arraySum m p k + m.read64 (p + BitVec.ofNat 64 (8 * k))

theorem sum_correct : FunSpec prog sym_sum (fun _ => True)
    (fun s s' => s'.gpr 0 = arraySum s.mem (s.gpr 0) (s.gpr 1).toNat) := by
  intro s hpc hst _
  simp only [sym_sum] at hpc
  m1_step; m1_step
  have hn := (s.gpr 1#5).isLt
  generalize hN : (s.gpr 1#5).toNat = n at hn
  apply Reaches.ite
  · intro h0
    m1_step; m1_step
    refine Reaches.done ⟨rfl, rfl, ?_⟩
    have : n = 0 := by rw [← hN, h0]; rfl
    simp [upd, this, arraySum]
  · intro h0
    have hpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa [hN] using h)) h0
      · exact h
    refine Reaches.loop
      (fun t => ∃ k, k < n ∧ t.pc = 0x344#64 ∧ t.status = .running ∧ t.gpr 30#5 = s.gpr 30#5 ∧
        t.mem = s.mem ∧ t.gpr 1#5 = BitVec.ofNat 64 (n - k) ∧
        t.gpr 0#5 = s.gpr 0#5 + BitVec.ofNat 64 (8 * k) ∧ t.gpr 8#5 = arraySum s.mem (s.gpr 0#5) k)
      (fun t => (t.gpr 1#5).toNat) ?_ _ ⟨0, hpos, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · rintro t ⟨k, hk, tpc, tst, tlr, tmem, t1, t0, t8⟩
      m1_step; m1_step; m1_step; m1_step
      have hnk : n - k < 2 ^ 64 := by omega
      apply Reaches.ite
      · intro hne
        have hne' : n - k ≠ 1 := fun h => hne (by rw [h])
        refine Reaches.done (Or.inl ⟨⟨k + 1, by omega, rfl, rfl, by simpa [upd] using tlr, rfl,
          ?_, ?_, ?_⟩, ?_⟩)
        · simp only [upd, BitVec.reduceEq, ite_true, ite_false]
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_sub, Nat.mod_eq_of_lt hnk]
          omega
        · simp only [upd, BitVec.reduceEq, ite_true, ite_false]
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add]
          omega
        · simp only [upd, BitVec.reduceEq, ite_true, ite_false, arraySum]
          rw [BitVec.add_comm]
        · simp [upd, BitVec.toNat_sub, Nat.mod_eq_of_lt hnk]
          omega
      · intro heq
        have hk1 : n = k + 1 := by
          have := congrArg BitVec.toNat (Classical.not_not.mp heq)
          simp [Nat.mod_eq_of_lt hnk] at this
          omega
        m1_step; m1_step
        refine Reaches.done (Or.inr ⟨by simp, rfl, ?_⟩)
        simp only [upd, BitVec.reduceEq, ite_true, ite_false, arraySum]
        rw [BitVec.add_comm]
    · simp [upd, ← hN]
    · simp [upd]
    · simp [upd, arraySum]

end Examples.Basic
