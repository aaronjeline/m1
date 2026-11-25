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

/-- The `i`-th byte of a 16-byte read. -/
theorem byte_read128 (m : Memory) (r : BitVec 64) (i : Nat) (hi : i < 16) :
    Memory.byte (m.read128 r) i = m (r + BitVec.ofNat 64 i) := by
  rw [Memory.read128_eq]
  match i, hi with
  | 0, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat, BitVec.add_zero]; bv_decide
  | 1, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | 2, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | 3, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | 4, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | 5, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | 6, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | 7, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | 8, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | 9, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | 10, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | 11, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | 12, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | 13, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | 14, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | 15, _ => simp only [Memory.byte, BitVec.ofNat_eq_ofNat]; bv_decide
  | _ + 16, h => exact absurd h (by omega)

/-- The `i`-th byte written by a 16-byte store. -/
theorem write128_byte (m : Memory) (w : BitVec 64) (v : BitVec 128) (i : Nat) (hi : i < 16) :
    (m.write128 w v) (w + BitVec.ofNat 64 i) = Memory.byte v i :=
  (Memory.writes128 m w v).read_byte i hi (by decide)

/-- A store at `w` of `n` bytes leaves `a` alone when `a` is at least `n` past `w`. -/
theorem write128_keep {m : Memory} {w a : BitVec 64} (v : BitVec 128) (h : 16 ≤ (a - w).toNat) :
    (m.write128 w v) a = m a := by
  rw [Memory.writes128 m w v a]; simp only [ite_eq_right_iff]; omega

/-- Three 16-byte loads from `a` stored at `b`, `b + 16`, `b + 32` copy 48 bytes. -/
theorem copy48 (m m0 : Memory) (a b : BitVec 64) (i : Nat) (hi : i < 0x30) :
    (((m.write128 b (m0.read128 a)).write128 (b + 16#64) (m0.read128 (a + 16#64))).write128
      (b + 32#64) (m0.read128 (a + 32#64))) (b + BitVec.ofNat 64 i) = m0 (a + BitVec.ofNat 64 i) := by
  have off : ∀ c : Nat, c ≤ i → b + BitVec.ofNat 64 i = (b + BitVec.ofNat 64 c) + BitVec.ofNat 64 (i - c) := by
    intro c hc; rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have offa : ∀ c : Nat, c ≤ i → a + BitVec.ofNat 64 i = (a + BitVec.ofNat 64 c) + BitVec.ofNat 64 (i - c) := by
    intro c hc; rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have far : ∀ c : Nat, i < c → c ≤ 0x30 → 16 ≤ (b + BitVec.ofNat 64 i - (b + BitVec.ofNat 64 c)).toNat := by
    intro c h1 h2
    rw [show b + BitVec.ofNat 64 i - (b + BitVec.ofNat 64 c) = BitVec.ofNat 64 i - BitVec.ofNat 64 c by
      grind]
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  by_cases h32 : 32 ≤ i
  · rw [off 32 h32, write128_byte _ _ _ _ (by omega), byte_read128 _ _ _ (by omega), ← offa 32 h32]
  · rw [write128_keep _ (by simpa using far 32 (by omega) (by omega))]
    by_cases h16 : 16 ≤ i
    · rw [off 16 h16, write128_byte _ _ _ _ (by omega), byte_read128 _ _ _ (by omega), ← offa 16 h16]
    · rw [write128_keep _ (by simpa using far 16 (by omega) (by omega)),
        show b + BitVec.ofNat 64 i = b + BitVec.ofNat 64 i from rfl,
        (by simpa using write128_byte m b (m0.read128 a) i (by omega) :
          (m.write128 b (m0.read128 a)) (b + BitVec.ofNat 64 i) = Memory.byte (m0.read128 a) i),
        byte_read128 _ _ _ (by omega)]

/-- `copy48` with the six addresses given separately (so that it unifies with
symbolic-execution output whose constant offsets are already folded). -/
theorem copy48' (m m0 : Memory) (a1 a2 a3 b1 b2 b3 : BitVec 64) (ha2 : a2 = a1 + 16#64)
    (ha3 : a3 = a1 + 32#64) (hb2 : b2 = b1 + 16#64) (hb3 : b3 = b1 + 32#64) (i : Nat) (hi : i < 0x30) :
    (((m.write128 b1 (m0.read128 a1)).write128 b2 (m0.read128 a2)).write128 b3 (m0.read128 a3))
      (b1 + BitVec.ofNat 64 i) = m0 (a1 + BitVec.ofNat 64 i) := by
  subst ha2 ha3 hb2 hb3; exact copy48 m m0 a1 b1 i hi

/-- `a` satisfies `Q` and no byte of `[w, w+n)` does: `a` is at least `n` past `w`. -/
theorem far_of {Q : BitVec 64 → Prop} {a w : BitVec 64} {n : Nat} (ha : Q a)
    (hw : ∀ i < n, ¬ Q (w + BitVec.ofNat 64 i)) : n ≤ (a - w).toNat := by
  apply Nat.not_lt.mp; intro hlt
  apply hw _ hlt
  have : w + BitVec.ofNat 64 (a - w).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rwa [this]

end Mem

end Examples.Cedar
