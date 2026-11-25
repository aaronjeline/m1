import M1

/-!
# Frame reasoning for modular proofs

Lemmas used by the Cedar proofs to carry facts about memory across calls
(whose contracts say which bytes they may change) and across the caller's own
stores.
-/

namespace Examples.Cedar
open M1

namespace Mem

/-- `Agree` is an equivalence on each range. -/
theorem agree_refl (m : Memory) (b : BitVec 64) (k : Nat) : Memory.Agree m m b k := fun _ _ => rfl

theorem agree_trans {m₁ m₂ m₃ : Memory} {b : BitVec 64} {k : Nat}
    (h₁ : Memory.Agree m₁ m₂ b k) (h₂ : Memory.Agree m₂ m₃ b k) : Memory.Agree m₁ m₃ b k :=
  fun i hi => (h₁ i hi).trans (h₂ i hi)

/-- A sub-range of an agreeing range agrees. -/
theorem agree_sub {m m' : Memory} {b : BitVec 64} {k : Nat} (h : Memory.Agree m m' b k)
    (j len : Nat) (hj : j + len ≤ k) : Memory.Agree m m' (b + BitVec.ofNat 64 j) len := by
  intro i hi
  have := h (j + i) (by omega)
  rwa [BitVec.add_assoc, show BitVec.ofNat 64 j + BitVec.ofNat 64 i = BitVec.ofNat 64 (j + i) by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.add_mod]]

/-- Stores outside a range leave it unchanged. -/
theorem agree_write64 {m : Memory} {a b : BitVec 64} {k : Nat} (v : BitVec 64)
    (h : Memory.Disjoint a 8 b k) : Memory.Agree (m.write64 a v) m b k :=
  (Memory.writes64 m a v).agree_disjoint h (by decide)

theorem agree_write128 {m : Memory} {a b : BitVec 64} {k : Nat} (v : BitVec 128)
    (h : Memory.Disjoint a 16 b k) : Memory.Agree (m.write128 a v) m b k :=
  (Memory.writes128 m a v).agree_disjoint h (by decide)

theorem agree_write32 {m : Memory} {a b : BitVec 64} {k : Nat} (v : BitVec 32)
    (h : Memory.Disjoint a 4 b k) : Memory.Agree (m.write32 a v) m b k :=
  (Memory.writes32 m a v).agree_disjoint h (by decide)

theorem agree_write8 {m : Memory} {a b : BitVec 64} {k : Nat} (v : BitVec 8)
    (h : Memory.Disjoint a 1 b k) : Memory.Agree (m.write8 a v) m b k :=
  (Memory.writes8 m a v).agree_disjoint h (by decide)

/-- The range `[a, a+n)` (no wrap-around) never meets `[b, b+k)`. -/
theorem disjoint_of_ne {a b : BitVec 64} {n k : Nat} (hn : 0 < n) (hk : 0 < k)
    (h : ∀ i < n, ∀ j < k, a + BitVec.ofNat 64 i ≠ b + BitVec.ofNat 64 j) :
    Memory.Disjoint a n b k := by
  constructor
  · apply Nat.not_lt.mp; intro hlt
    apply h (b - a).toNat hlt 0 hk
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_sub]
    have := a.isLt; have := b.isLt; omega
  · apply Nat.not_lt.mp; intro hlt
    apply h 0 hn (a - b).toNat hlt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_sub]
    have := a.isLt; have := b.isLt; omega

end Mem

end Examples.Cedar
