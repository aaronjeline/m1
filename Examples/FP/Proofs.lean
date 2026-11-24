import Examples.FP.Code

/-!
Verified floating-point code. Values are IEEE 754 encodings (as in the
registers), and the specifications use the operations of `M1.FP`, which are
correctly rounded by construction and validated against the M1.
-/

namespace Examples.FP
open M1

/-- `a + x * y` in double precision with a single rounding (`FMADD`). -/
def fmadd (a x y : Nat) : Nat := FP.mulAdd 64 a x y % 2 ^ 64

/-- What `poly` computes: clang contracted every `t * x + c` into a fused
multiply-add, so the result is *not* the C abstract machine's separately
rounded `((3x + 2)x - 7.5)x + 1`, but this: -/
def polyRef (x : Nat) : Nat :=
  fmadd 0x3FF0000000000000          -- 1.0
    (fmadd 0xC01E000000000000       -- -7.5
      (fmadd 0x4000000000000000 x 0x4008000000000000) x) x  -- 2.0 + x * 3.0

theorem poly_correct : FunSpec prog sym_poly FPDefault
    (fun s s' => fpArg (s'.vreg 0) 64 = polyRef (fpArg (s.vreg 0) 64)) := by
  intro s hpc hst hfp
  simp only [FPDefault] at hfp
  simp only [sym_poly] at hpc
  m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
  refine Reaches.done ⟨rfl, rfl, ?_⟩
  have h1 : FP.expandImm 64 112 % 2 ^ 64 = 0x3FF0000000000000 := by decide
  have h2 : FP.expandImm 64 158 % 2 ^ 64 = 0xC01E000000000000 := by decide
  have h3 : FP.expandImm 64 0 % 2 ^ 64 = 0x4000000000000000 := by decide
  have h4 : FP.expandImm 64 8 % 2 ^ 64 = 0x4008000000000000 := by decide
  simp only [upd, BitVec.reduceEq, ite_true, ite_false, fpArg_fpRes64, Nat.reducePow, h1, h2, h3,
    h4] at *
  rfl

/-- `clampf(x, lo, hi)`: IEEE comparisons are false on NaN, so a NaN `x` is
returned unchanged, as in C. -/
theorem clampf_correct : FunSpec prog sym_clampf FPDefault
    (fun s s' =>
      let x := fpArg (s.vreg 0) 32
      let lo := fpArg (s.vreg 1) 32
      let hi := fpArg (s.vreg 2) 32
      fpArg (s'.vreg 0) 32 =
        if FP.cmpGT 32 lo x then lo else if FP.cmpGT 32 x hi then hi else x) := by
  intro s hpc hst hfp
  simp only [FPDefault] at hfp
  simp only [sym_clampf] at hpc
  m1_step; m1_step; m1_step; m1_step; m1_step
  refine Reaches.done ⟨rfl, rfl, ?_⟩
  simp only [upd, BitVec.reduceEq, ite_true, ite_false, fpArg_fpRes32, Nat.reducePow]
  split <;> (try split) <;> simp [fpArg, toNat_fpRes32]

/-- `(long)x` truncates towards zero, saturating; NaN becomes 0 (FCVTZS). -/
theorem to_long_correct : FunSpec prog sym_to_long FPDefault
    (fun s s' => s'.gpr 0 = BitVec.ofInt 64 (FP.toInt 64 .z true 64 (fpArg (s.vreg 0) 64))) := by
  intro s hpc hst hfp
  simp only [FPDefault] at hfp
  simp only [sym_to_long] at hpc
  m1_step; m1_step
  refine Reaches.done ⟨rfl, rfl, ?_⟩
  simp only [upd, ite_true]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt]
  omega

end Examples.FP
