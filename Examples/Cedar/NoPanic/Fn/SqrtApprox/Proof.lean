import Examples.Cedar.NoPanic.Fn.SqrtApprox.Code
import Examples.Cedar.NoPanic.Spec

namespace Examples.Cedar.NoPanic.Fn.SqrtApprox
open M1 Examples.Cedar.Eval Examples.Cedar.NoPanic

/-- `core::slice::sort::stable::drift::sqrt_approx(n)`:
`shift = (ilog2(n | 1) + 1) / 2; ((1 << shift) + (n >> shift)) / 2`, with
`ilog2(x) = 63 - clz(x)`. -/
def sqrtApprox (n : BitVec 64) : BitVec 64 :=
  let k : BitVec 64 := (63#64 - BitVec.ofNat 64 (countLeadingZeros (n ||| 1#64)) + 1#64) >>> 1
  ((1#64 <<< k) + (n >>> k)) >>> 1

theorem clz_go_le (x : BitVec 64) (h : x.getLsbD 0 = true) :
    ∀ i, 1 ≤ i → countLeadingZeros.go x i ≤ 63
  | 0, h0 => absurd h0 (by decide)
  | 1, _ => by simp [countLeadingZeros.go, h]
  | i + 2, _ => by
    unfold countLeadingZeros.go
    split
    · omega
    · exact clz_go_le x h (i + 1) (by omega)

theorem clz_or_one_le (n : BitVec 64) : countLeadingZeros (n ||| 1#64) ≤ 63 :=
  clz_go_le _ (by simp) 64 (by decide)

theorem shl_toNat_mod (a b : BitVec 64) : a <<< (b.toNat % 64) = a <<< (b % 64#64) := by
  rw [BitVec.shiftLeft_eq', BitVec.toNat_umod]; rfl
theorem shr_toNat_mod (a b : BitVec 64) : a >>> (b.toNat % 64) = a >>> (b % 64#64) := by
  rw [BitVec.ushiftRight_eq', BitVec.toNat_umod]; rfl

theorem np (p : Program) (hp : p.Extends prog) (top : BitVec 64) :
    NP p top sym_fn (fun _ => True) (fun _ => 0) 0 (fun s s' => s'.gpr 0 = sqrtApprox (s.gpr 0)) := by
  rintro n s hpc hst ⟨hal, -⟩
  simp only [sym_fn] at hpc
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  apply SafeN.done
  refine ⟨rfl, rfl, ⟨?_, rfl, fun _ _ _ => rfl, rfl⟩, fun _ _ _ => rfl, rfl, ?_⟩
  · intro r h1 h2
    simp (disch := bv_omega) only [upd_other]
  · have hc := clz_or_one_le (s.gpr 0)
    simp (config := { decide := true }) only [upd, ite_true, sqrtApprox, bitfieldCompute,
      shl_toNat_mod, shr_toNat_mod]
    clear hpc hst hal hp
    generalize countLeadingZeros (s.gpr 0#5 ||| 1#64) = c at hc ⊢
    have hx : BitVec.ofNat 64 c ≤ 63#64 := by
      rw [BitVec.le_def, BitVec.toNat_ofNat]; simp only [BitVec.toNat_ofNat]; omega
    generalize BitVec.ofNat 64 c = x at hx ⊢
    generalize s.gpr 0#5 = a
    bv_decide

end Examples.Cedar.NoPanic.Fn.SqrtApprox
