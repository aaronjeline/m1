/-
  Lemmas connecting floating-point comparisons (`FCMP`, which sets NZCV) to
  the condition codes that consume them, stated with the FPCompareEQ/GE/GT
  predicates of `M1.FP`. Used by symbolic execution of FP code.
-/
import M1.Exec

namespace M1.FP

/-- The four outcomes of `compare`, as a function of `cmpEQ` and `cmpGT`. -/
theorem compare_eq (N x y : Nat) : compare N x y =
    if isNaN (unpack N x) || isNaN (unpack N y) then ⟨false, false, true, true⟩
    else if cmpEQ N x y then ⟨false, true, true, false⟩
    else if cmpGT N y x then ⟨true, false, false, false⟩
    else ⟨false, false, true, false⟩ := by
  unfold compare compareV cmpEQ cmpGT
  cases unpack N x <;> cases unpack N y <;> simp [isNaN]

set_option hygiene false in
/-- Case split on the NaN-ness and order of two values. -/
local macro "ord_cases" : tactic => `(tactic| (
  dsimp only; generalize unpack N x = a; generalize unpack N y = b
  have h₁ := lt_asymm a b; have h₂ := lt_asymm b a
  cases isNaN a <;> cases isNaN b <;> cases ha : lt a b <;> cases hb : lt b a <;> simp_all))

theorem cmpEQ_comm (N x y : Nat) : cmpEQ N x y = cmpEQ N y x := by
  unfold cmpEQ eq; ord_cases

theorem cmpGE_iff (N x y : Nat) : cmpGE N x y = (cmpEQ N x y || cmpGT N x y) := by
  unfold cmpGE cmpEQ cmpGT eq; ord_cases

private theorem cases_ (N x y : Nat) (P : NZCV → Prop)
    (hu : isNaN (unpack N x) || isNaN (unpack N y) → P ⟨false, false, true, true⟩)
    (he : cmpEQ N x y → P ⟨false, true, true, false⟩)
    (hl : cmpGT N y x → P ⟨true, false, false, false⟩)
    (hg : cmpGT N x y → P ⟨false, false, true, false⟩) : P (compare N x y) := by
  rw [compare_eq]
  have ord : ¬(isNaN (unpack N x) || isNaN (unpack N y)) → ¬cmpEQ N x y → ¬cmpGT N y x →
      cmpGT N x y := by
    unfold cmpEQ cmpGT eq; ord_cases
  split
  · exact hu (by assumption)
  split
  · exact he (by assumption)
  split
  · exact hl (by assumption)
  · exact hg (ord (by assumption) (by assumption) (by assumption))

/-- In each ordering outcome the others are false. -/
private theorem excl (N x y : Nat) :
    (cmpEQ N x y → !cmpGT N x y ∧ !cmpGT N y x) ∧
    (cmpGT N x y → !cmpGT N y x ∧ !cmpEQ N x y) ∧
    ((isNaN (unpack N x) || isNaN (unpack N y)) → !cmpEQ N x y ∧ !cmpGT N x y ∧ !cmpGT N y x) := by
  unfold cmpEQ cmpGT eq; ord_cases

set_option hygiene false in
local macro "fcases" : tactic => `(tactic| (
  refine cases_ N x y (fun f => conditionHolds _ f = _) ?_ ?_ ?_ ?_ <;> intro h <;>
    simp_all [conditionHolds, cmpGE_iff, cmpEQ_comm N y x] <;>
    have := excl N x y <;> simp_all <;> (try (rcases h with h | h <;> simp_all))))

@[simp] theorem cond_eq (N x y : Nat) : conditionHolds 0#4 (compare N x y) = cmpEQ N x y := by fcases
@[simp] theorem cond_ne (N x y : Nat) : conditionHolds 1#4 (compare N x y) = !cmpEQ N x y := by fcases
/-- `HS`/`CS`: greater, equal or unordered. -/
@[simp] theorem cond_hs (N x y : Nat) : conditionHolds 2#4 (compare N x y) = !cmpGT N y x := by fcases
/-- `LO`/`CC`: less than. -/
@[simp] theorem cond_lo (N x y : Nat) : conditionHolds 3#4 (compare N x y) = cmpGT N y x := by fcases
/-- `MI`: less than. -/
@[simp] theorem cond_mi (N x y : Nat) : conditionHolds 4#4 (compare N x y) = cmpGT N y x := by fcases
@[simp] theorem cond_pl (N x y : Nat) : conditionHolds 5#4 (compare N x y) = !cmpGT N y x := by fcases
/-- `VS`: unordered. -/
@[simp] theorem cond_vs (N x y : Nat) :
    conditionHolds 6#4 (compare N x y) = (isNaN (unpack N x) || isNaN (unpack N y)) := by
  fcases
@[simp] theorem cond_vc (N x y : Nat) :
    conditionHolds 7#4 (compare N x y) = !(isNaN (unpack N x) || isNaN (unpack N y)) := by
  fcases
/-- `HI`: greater than or unordered. -/
@[simp] theorem cond_hi (N x y : Nat) : conditionHolds 8#4 (compare N x y) = !cmpGE N y x := by fcases
/-- `LS`: less than or equal. -/
@[simp] theorem cond_ls (N x y : Nat) : conditionHolds 9#4 (compare N x y) = cmpGE N y x := by fcases
@[simp] theorem cond_ge (N x y : Nat) : conditionHolds 10#4 (compare N x y) = cmpGE N x y := by fcases
/-- `LT`: less than or unordered. -/
@[simp] theorem cond_lt (N x y : Nat) : conditionHolds 11#4 (compare N x y) = !cmpGE N x y := by fcases
@[simp] theorem cond_gt (N x y : Nat) : conditionHolds 12#4 (compare N x y) = cmpGT N x y := by fcases
/-- `LE`: less than, equal or unordered. -/
@[simp] theorem cond_le (N x y : Nat) : conditionHolds 13#4 (compare N x y) = !cmpGT N x y := by fcases

end M1.FP

namespace M1

theorem fpArg_fpRes64 (r : Nat) : fpArg (fpRes 64 r) 64 = r % 2 ^ 64 := fpArg_fpRes 64 r
theorem fpArg_fpRes32 (r : Nat) : fpArg (fpRes 32 r) 32 = r % 2 ^ 32 := fpArg_fpRes 32 r
theorem fpArg_fpRes16 (r : Nat) : fpArg (fpRes 16 r) 16 = r % 2 ^ 16 := fpArg_fpRes 16 r
/-- `fpArg_fpRes` with `fpArg` unfolded and the modulus a literal. -/
theorem toNat_fpRes64 (r : Nat) : (fpRes 64 r).toNat % 18446744073709551616 = r % 2 ^ 64 :=
  fpArg_fpRes 64 r
theorem toNat_fpRes32 (r : Nat) : (fpRes 32 r).toNat % 4294967296 = r % 2 ^ 32 :=
  fpArg_fpRes 32 r

end M1
