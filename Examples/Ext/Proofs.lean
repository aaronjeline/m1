import Examples.Ext.Code

namespace Examples.Ext
open M1

/-- The contract assumed of libc's `rand`: it returns (in `w0`) an `int` in
`[0, RAND_MAX]`, follows the AAPCS64, and does not touch its caller's frame. -/
def RandSpec (p : Program) : Prop :=
  FunSpec p ext_rand (fun _ => True) fun s s' =>
    ((s'.gpr 0).setWidth 32).msb = false ∧ CalleeSaved s s' ∧ FramePreserved 16 s s'

/-! Small bit-vector facts used to bring clang's `% 6` sequence into linear
arithmetic: `lsr` is `UBFM`, and sign extension of a non-negative value is
zero extension. -/

theorem lsr32 (y p : BitVec 64) :
    bitfieldCompute BitfieldOp.ubfm y p 32 63 18446744073709551615#64 4294967295#64 = p >>> 32 := by
  simp [bitfieldCompute]; bv_decide

theorem lsr63 (y p : BitVec 64) :
    bitfieldCompute BitfieldOp.ubfm y p 63 63 18446744073709551615#64 1#64 = p >>> 63 := by
  simp [bitfieldCompute]; bv_decide

theorem sext_of_msb (a : BitVec 32) (h : a.msb = false) : a.signExtend 64 = a.setWidth 64 := by
  bv_decide

theorem msb_lt (a : BitVec 32) (h : a.msb = false) : a.toNat < 2 ^ 31 := by
  have := BitVec.msb_eq_decide a; simp_all

theorem prod_toNat (a : BitVec 32) (ha : a.toNat < 2 ^ 31) :
    (a.setWidth 64 * 715827883#64).toNat = a.toNat * 715827883 := by
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have e1 : a.toNat % 2 ^ 64 = a.toNat := Nat.mod_eq_of_lt (by omega)
  have e2 : (715827883 : Nat) % 2 ^ 64 = 715827883 := Nat.mod_eq_of_lt (by decide)
  rw [e1, e2]
  exact Nat.mod_eq_of_lt (by omega)

/-- For `0 ≤ a < 2^31`, clang's quotient `(a * 0x2AAAAAAB) >> 32` is `a / 6`, so
`a - 6q + 1` is in `[1, 6]`. -/
theorem div6_rem (a : BitVec 32) (h : a.msb = false) :
    let q := ((a.setWidth 64 * 715827883#64) >>> 32).setWidth 32
    1 ≤ (a - q * 6#32 + 1#32).toNat ∧ (a - q * 6#32 + 1#32).toNat ≤ 6 := by
  intro q
  have ha := msb_lt a h
  have hqv : q.toNat = a.toNat * 715827883 / 2 ^ 32 := by
    show (((a.setWidth 64 * 715827883#64) >>> 32).setWidth 32).toNat = _
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, prod_toNat a ha, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega)]
  have h6 : 6 * q.toNat ≤ a.toNat ∧ a.toNat < 6 * q.toNat + 6 := by omega
  have hm : (q * 6#32).toNat = q.toNat * 6 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
    have e : (6 : Nat) % 2 ^ 32 = 6 := by decide
    rw [e, Nat.mod_eq_of_lt (by omega)]
  have hs : (a - q * 6#32).toNat = a.toNat - q.toNat * 6 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hm]; omega), hm]
  have hr : (a - q * 6#32 + 1#32).toNat = a.toNat - q.toNat * 6 + 1 := by
    rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat]
    have e : (1 : Nat) % 2 ^ 32 = 1 := by decide
    rw [e, Nat.mod_eq_of_lt (by omega)]
  rw [hr]; omega

theorem msb_product (x : BitVec 64) (h : (x.setWidth 32).msb = false) :
    ((x.setWidth 32).setWidth 64 * 715827883#64) >>> 63 = 0#64 := by
  have ha := msb_lt _ h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, prod_toNat _ ha, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)]
  rfl

/-- The value the instruction sequence leaves in `w0`, folded (the product is
treated as an opaque `p`, so this is a cheap SAT problem). -/
theorem fold_rem (x p : BitVec 64) (hp : p >>> 63 = 0#64) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (x - BitVec.setWidth 64 (BitVec.setWidth 32 (p >>> 32) +
        BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (p >>> 63)))) * 6#64))) +
      1#32)) =
    x.setWidth 32 - (p >>> 32).setWidth 32 * 6#32 + 1#32 := by
  bv_decide

theorem roll_correct (p : Program) (hp : p.Extends prog) (hrand : RandSpec p) :
    FunSpec p sym_roll (fun s => s.sp &&& 15#64 = 0#64) fun s s' =>
      (1 ≤ ((s'.gpr 0).setWidth 32).toNat ∧ ((s'.gpr 0).setWidth 32).toNat ≤ 6) ∧
      CalleeSaved s s' := by
  intro s hpc hst hsp
  simp only [sym_roll] at hpc
  m1_step; m1_step; m1_step
  refine Reaches.trans (hrand _ rfl rfl trivial) ?_
  rintro s1 ⟨h1pc, h1st, h1w, ⟨h1r, h1sp, h1v, h1fpcr⟩, h1fr⟩
  -- The saved frame survives the call.
  have hfp := h1fr.read64 0
  have hlr := h1fr.read64 8
  simp only [upd, BitVec.reduceEq, ite_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    BitVec.add_assoc, BitVec.reduceAdd] at h1pc h1sp hfp hlr
  simp only [Memory.read64_write64_same] at hfp hlr
  m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
  refine Reaches.done ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  rotate_left
  · -- x19-x29: untouched by `roll` (x29 restored from the frame), preserved by `rand`.
    intro r hlo hhi
    have hr := h1r r hlo hhi
    clear h1fpcr
    simp only [upd] at hr ⊢
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all <;> omega
  · simp
  · intro r hlo hhi; simpa using h1v r hlo hhi
  · simp
  · -- `rand() % 6 + 1` via clang's multiply-high reciprocal, for any `rand()` in
    -- `[0, 2^31)`.
    simp only [upd, BitVec.reduceEq, ite_true, ite_false, lsr32, lsr63, sext_of_msb _ h1w]
    generalize s1.gpr 0#5 = x at h1w ⊢
    rw [fold_rem x _ (msb_product _ h1w)]
    exact div6_rem _ h1w

end Examples.Ext
