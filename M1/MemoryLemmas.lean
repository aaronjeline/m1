/-
  Reasoning about the byte-addressed memory.

  * `Memory.writeK_apply`: byte-level characterisation of every write.
  * `Memory.readK_eq`: every read as a concatenation of bytes `m (a + i)`.
  * `Memory.Disjoint a n b k`: the address ranges `[a, a+n)` and `[b, b+k)`
    (modulo 2^64) do not overlap.
  * Read-over-write simp lemmas: same address (`readK_writeK_same`) and
    disjoint ranges (`readK_writeJ_disjoint`) for all access sizes.
-/
import M1.State

namespace M1
namespace Memory

/-- Byte `i` (little-endian) of a bit vector. -/
def byte {w : Nat} (v : BitVec w) (i : Nat) : BitVec 8 := (v >>> (8 * i)).setWidth 8

/-- `m'` is `m` with the `k` bytes from `a` replaced by `f 0, ..., f (k-1)`. -/
def Writes (m' m : Memory) (a : BitVec 64) (k : Nat) (f : Nat → BitVec 8) : Prop :=
  ∀ x, m' x = if (x - a).toNat < k then f (x - a).toNat else m x

theorem toNat_sub_add (x a : BitVec 64) (k : Nat) :
    (x - (a + BitVec.ofNat 64 k)).toNat = ((x - a).toNat + (2 ^ 64 - k % 2 ^ 64)) % 2 ^ 64 := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := x.isLt; have := a.isLt
  omega

theorem Writes.compose {m m₁ m₂ : Memory} {a : BitVec 64} {k : Nat} {f g : Nat → BitVec 8}
    (hk : 2 * k < 2 ^ 64) (h₁ : Writes m₁ m a k f) (h₂ : Writes m₂ m₁ (a + BitVec.ofNat 64 k) k g) :
    Writes m₂ m a (2 * k) (fun i => if i < k then f i else g (i - k)) := by
  intro x
  rw [h₂ x, h₁ x, toNat_sub_add]
  have hd := (x - a).isLt
  generalize (x - a).toNat = d at *
  by_cases h1 : d < k
  · have : ¬ (d + (2 ^ 64 - k % 2 ^ 64)) % 2 ^ 64 < k := by omega
    simp [this, h1, show d < 2 * k by omega]
  · by_cases h2 : d < 2 * k
    · have e : (d + (2 ^ 64 - k % 2 ^ 64)) % 2 ^ 64 = d - k := by omega
      simp [e, h1, h2, show d - k < k by omega]
    · have : ¬ (d + (2 ^ 64 - k % 2 ^ 64)) % 2 ^ 64 < k := by omega
      simp [this, h1, h2]

theorem byte_extractLsb' {w : Nat} (v : BitVec w) (lo c len i : Nat) (hlo : lo = 8 * c)
    (hi : 8 * (i + 1) ≤ len) : byte (v.extractLsb' lo len) i = byte v (c + i) := by
  subst hlo
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  simp only [byte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb']
  simp only [ht, decide_true, Bool.true_and]
  have : 8 * i + t < len := by omega
  simp only [this, decide_true, Bool.true_and]
  congr 1
  omega

theorem byte_setWidth {w : Nat} (v : BitVec w) (len i : Nat) (hi : 8 * (i + 1) ≤ len) :
    byte (v.setWidth len) i = byte v i := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  simp only [byte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  simp only [ht, decide_true, Bool.true_and]
  have : 8 * i + t < len := by omega
  simp [this]

theorem writes8 (m : Memory) (a : BitVec 64) (v : BitVec 8) :
    Writes (write8 m a v) m a 1 (byte v) := by
  intro x
  simp only [write8, upd]
  by_cases h : x = a
  · subst h; simp [byte]
  · have hne : x.toNat ≠ a.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    have : ¬ (x - a).toNat < 1 := by
      simp only [BitVec.toNat_sub]; have := x.isLt; have := a.isLt; omega
    simp only [h, this, ite_false]

theorem writes_congr {m' m : Memory} {a : BitVec 64} {k : Nat} {f g : Nat → BitVec 8}
    (h : Writes m' m a k f) (hfg : ∀ i < k, f i = g i) : Writes m' m a k g := by
  intro x
  rw [h x]
  split <;> simp_all

theorem writes16 (m : Memory) (a : BitVec 64) (v : BitVec 16) :
    Writes (write16 m a v) m a 2 (byte v) := by
  have := Writes.compose (by decide) (writes8 m a (v.extractLsb' 0 8))
    (writes8 _ (a + BitVec.ofNat 64 1) (v.extractLsb' 8 8))
  refine writes_congr this fun i hi => ?_
  split
  · rw [byte_extractLsb' v 0 0 8 i rfl (by omega)]; simp
  · rw [byte_extractLsb' v 8 1 8 (i - 1) rfl (by omega)]; congr 1; omega

theorem writes32 (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    Writes (write32 m a v) m a 4 (byte v) := by
  have := Writes.compose (by decide) (writes16 m a (v.extractLsb' 0 16))
    (writes16 _ (a + BitVec.ofNat 64 2) (v.extractLsb' 16 16))
  refine writes_congr this fun i hi => ?_
  split
  · rw [byte_extractLsb' v 0 0 16 i rfl (by omega)]; simp
  · rw [byte_extractLsb' v 16 2 16 (i - 2) rfl (by omega)]; congr 1; omega

theorem writes64 (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    Writes (write64 m a v) m a 8 (byte v) := by
  have := Writes.compose (by decide) (writes32 m a (v.extractLsb' 0 32))
    (writes32 _ (a + BitVec.ofNat 64 4) (v.extractLsb' 32 32))
  refine writes_congr this fun i hi => ?_
  split
  · rw [byte_extractLsb' v 0 0 32 i rfl (by omega)]; simp
  · rw [byte_extractLsb' v 32 4 32 (i - 4) rfl (by omega)]; congr 1; omega

theorem writes128 (m : Memory) (a : BitVec 64) (v : BitVec 128) :
    Writes (write128 m a v) m a 16 (byte v) := by
  have := Writes.compose (by decide) (writes64 m a (v.extractLsb' 0 64))
    (writes64 _ (a + BitVec.ofNat 64 8) (v.extractLsb' 64 64))
  refine writes_congr this fun i hi => ?_
  split
  · rw [byte_extractLsb' v 0 0 64 i rfl (by omega)]; simp
  · rw [byte_extractLsb' v 64 8 64 (i - 8) rfl (by omega)]; congr 1; omega

/-! ### Reads as byte concatenations -/

theorem read16_eq (m : Memory) (a : BitVec 64) : read16 m a = m (a + 1) ++ m a := rfl

theorem read32_eq (m : Memory) (a : BitVec 64) :
    read32 m a = (m (a + 3) ++ m (a + 2)) ++ (m (a + 1) ++ m a) := by
  simp only [read32, read16, BitVec.add_assoc, BitVec.reduceAdd]; rfl

theorem read64_eq (m : Memory) (a : BitVec 64) :
    read64 m a = ((m (a + 7) ++ m (a + 6)) ++ (m (a + 5) ++ m (a + 4))) ++
      ((m (a + 3) ++ m (a + 2)) ++ (m (a + 1) ++ m a)) := by
  simp only [read64, read32, read16, BitVec.add_assoc, BitVec.reduceAdd]; rfl

theorem read128_eq (m : Memory) (a : BitVec 64) :
    read128 m a =
      (((m (a + 15) ++ m (a + 14)) ++ (m (a + 13) ++ m (a + 12))) ++
        ((m (a + 11) ++ m (a + 10)) ++ (m (a + 9) ++ m (a + 8)))) ++
      (((m (a + 7) ++ m (a + 6)) ++ (m (a + 5) ++ m (a + 4))) ++
        ((m (a + 3) ++ m (a + 2)) ++ (m (a + 1) ++ m a))) := by
  simp only [read128, read64, read32, read16, BitVec.add_assoc, BitVec.reduceAdd]; rfl

/-- Two memories agree on the `k` bytes from `b`. -/
def Agree (m m' : Memory) (b : BitVec 64) (k : Nat) : Prop :=
  ∀ i < k, m (b + BitVec.ofNat 64 i) = m' (b + BitVec.ofNat 64 i)

theorem Agree.at {m m' : Memory} {b : BitVec 64} {k : Nat} (h : Agree m m' b k) (i : Nat)
    (hi : i < k := by decide) : m (b + BitVec.ofNat 64 i) = m' (b + BitVec.ofNat 64 i) := h i hi

theorem Agree.at0 {m m' : Memory} {b : BitVec 64} {k : Nat} (h : Agree m m' b k)
    (hk : 0 < k := by decide) : m b = m' b := by
  have := h 0 hk; simpa using this

theorem read8_congr {m m' : Memory} {b : BitVec 64} (h : Agree m m' b 1) :
    read8 m b = read8 m' b := h.at0

theorem read16_congr {m m' : Memory} {b : BitVec 64} (h : Agree m m' b 2) :
    read16 m b = read16 m' b := by
  have := h.at 1
  rw [read16_eq, read16_eq, h.at0]
  simp only [BitVec.ofNat_eq_ofNat] at *
  rw [this]

theorem read32_congr {m m' : Memory} {b : BitVec 64} (h : Agree m m' b 4) :
    read32 m b = read32 m' b := by
  rw [read32_eq, read32_eq, h.at0]
  simp only [BitVec.ofNat_eq_ofNat] at *
  have := h.at 1; have := h.at 2; have := h.at 3
  simp_all

theorem read64_congr {m m' : Memory} {b : BitVec 64} (h : Agree m m' b 8) :
    read64 m b = read64 m' b := by
  rw [read64_eq, read64_eq, h.at0]
  simp only [BitVec.ofNat_eq_ofNat] at *
  have := h.at 1; have := h.at 2; have := h.at 3; have := h.at 4
  have := h.at 5; have := h.at 6; have := h.at 7
  simp_all

theorem read128_congr {m m' : Memory} {b : BitVec 64} (h : Agree m m' b 16) :
    read128 m b = read128 m' b := by
  rw [read128_eq, read128_eq, h.at0]
  simp only [BitVec.ofNat_eq_ofNat] at *
  have := h.at 1; have := h.at 2; have := h.at 3; have := h.at 4
  have := h.at 5; have := h.at 6; have := h.at 7; have := h.at 8
  have := h.at 9; have := h.at 10; have := h.at 11; have := h.at 12
  have := h.at 13; have := h.at 14; have := h.at 15
  simp_all

/-! ### Disjointness -/

/-- The byte ranges `[a, a+n)` and `[b, b+k)` (modulo 2^64) are disjoint. -/
def Disjoint (a : BitVec 64) (n : Nat) (b : BitVec 64) (k : Nat) : Prop :=
  n ≤ (b - a).toNat ∧ k ≤ (a - b).toNat

theorem Disjoint.symm {a b : BitVec 64} {n k : Nat} (h : Disjoint a n b k) : Disjoint b k a n :=
  ⟨h.2, h.1⟩

theorem Disjoint.offset {a b : BitVec 64} {n k : Nat} (h : Disjoint a n b k) (hn : 0 < n)
    (i : Nat) (hi : i < k) : ¬ (b + BitVec.ofNat 64 i - a).toNat < n := by
  have h1 := h.1; have h2 := h.2
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at *
  have := a.isLt; have := b.isLt
  omega

theorem Writes.agree_disjoint {m' m : Memory} {a b : BitVec 64} {n k : Nat} {f : Nat → BitVec 8}
    (hw : Writes m' m a n f) (hd : Disjoint a n b k) (hn : 0 < n) : Agree m' m b k := by
  intro i hi
  rw [hw, ite_eq_right_of_eq_false _ _ (eq_false (hd.offset hn i hi))]

/-- A write followed by a read of the same bytes. -/
theorem Writes.read_byte {m' m : Memory} {a : BitVec 64} {n : Nat} {f : Nat → BitVec 8}
    (hw : Writes m' m a n f) (i : Nat) (hi : i < n) (hn : n < 2 ^ 64) :
    m' (a + BitVec.ofNat 64 i) = f i := by
  rw [hw]
  have : (a + BitVec.ofNat 64 i - a).toNat = i := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  rw [this, ite_eq_left_of_eq_true _ _ (eq_true hi)]

/-! ### Read-over-write: same address -/

@[simp] theorem read8_write8_same (m : Memory) (a : BitVec 64) (v : BitVec 8) :
    read8 (write8 m a v) a = v := by simp [read8, write8]

@[simp] theorem read16_write16_same (m : Memory) (a : BitVec 64) (v : BitVec 16) :
    read16 (write16 m a v) a = v := by
  have h := (writes16 m a v).read_byte
  rw [read16_eq]
  have h0 := h 0 (by decide) (by decide); have h1 := h 1 (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at *
  rw [h0, h1]; simp only [byte]; bv_decide

@[simp] theorem read32_write32_same (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    read32 (write32 m a v) a = v := by
  have h := (writes32 m a v).read_byte
  rw [read32_eq]
  have h0 := h 0 (by decide) (by decide); have h1 := h 1 (by decide) (by decide)
  have h2 := h 2 (by decide) (by decide); have h3 := h 3 (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at *
  rw [h0, h1, h2, h3]; simp only [byte]; bv_decide

@[simp] theorem read64_write64_same (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    read64 (write64 m a v) a = v := by
  have h := (writes64 m a v).read_byte
  rw [read64_eq]
  have h0 := h 0 (by decide) (by decide); have h1 := h 1 (by decide) (by decide)
  have h2 := h 2 (by decide) (by decide); have h3 := h 3 (by decide) (by decide)
  have h4 := h 4 (by decide) (by decide); have h5 := h 5 (by decide) (by decide)
  have h6 := h 6 (by decide) (by decide); have h7 := h 7 (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at *
  rw [h0, h1, h2, h3, h4, h5, h6, h7]; simp only [byte]; bv_decide

@[simp] theorem read128_write128_same (m : Memory) (a : BitVec 64) (v : BitVec 128) :
    read128 (write128 m a v) a = v := by
  have h := (writes128 m a v).read_byte
  rw [read128_eq]
  have h0 := h 0 (by decide) (by decide); have h1 := h 1 (by decide) (by decide)
  have h2 := h 2 (by decide) (by decide); have h3 := h 3 (by decide) (by decide)
  have h4 := h 4 (by decide) (by decide); have h5 := h 5 (by decide) (by decide)
  have h6 := h 6 (by decide) (by decide); have h7 := h 7 (by decide) (by decide)
  have h8 := h 8 (by decide) (by decide); have h9 := h 9 (by decide) (by decide)
  have h10 := h 10 (by decide) (by decide); have h11 := h 11 (by decide) (by decide)
  have h12 := h 12 (by decide) (by decide); have h13 := h 13 (by decide) (by decide)
  have h14 := h 14 (by decide) (by decide); have h15 := h 15 (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at *
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  simp only [byte]; bv_decide


/-! ### Read-over-write: disjoint ranges -/
@[simp] theorem read8_write8_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 8}
    (h : Disjoint a 1 b 1) : read8 (write8 m a v) b = read8 m b :=
  read8_congr ((writes8 m a v).agree_disjoint h (by decide))
@[simp] theorem read8_write16_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 16}
    (h : Disjoint a 2 b 1) : read8 (write16 m a v) b = read8 m b :=
  read8_congr ((writes16 m a v).agree_disjoint h (by decide))
@[simp] theorem read8_write32_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 32}
    (h : Disjoint a 4 b 1) : read8 (write32 m a v) b = read8 m b :=
  read8_congr ((writes32 m a v).agree_disjoint h (by decide))
@[simp] theorem read8_write64_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 64}
    (h : Disjoint a 8 b 1) : read8 (write64 m a v) b = read8 m b :=
  read8_congr ((writes64 m a v).agree_disjoint h (by decide))
@[simp] theorem read8_write128_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 128}
    (h : Disjoint a 16 b 1) : read8 (write128 m a v) b = read8 m b :=
  read8_congr ((writes128 m a v).agree_disjoint h (by decide))
@[simp] theorem read16_write8_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 8}
    (h : Disjoint a 1 b 2) : read16 (write8 m a v) b = read16 m b :=
  read16_congr ((writes8 m a v).agree_disjoint h (by decide))
@[simp] theorem read16_write16_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 16}
    (h : Disjoint a 2 b 2) : read16 (write16 m a v) b = read16 m b :=
  read16_congr ((writes16 m a v).agree_disjoint h (by decide))
@[simp] theorem read16_write32_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 32}
    (h : Disjoint a 4 b 2) : read16 (write32 m a v) b = read16 m b :=
  read16_congr ((writes32 m a v).agree_disjoint h (by decide))
@[simp] theorem read16_write64_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 64}
    (h : Disjoint a 8 b 2) : read16 (write64 m a v) b = read16 m b :=
  read16_congr ((writes64 m a v).agree_disjoint h (by decide))
@[simp] theorem read16_write128_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 128}
    (h : Disjoint a 16 b 2) : read16 (write128 m a v) b = read16 m b :=
  read16_congr ((writes128 m a v).agree_disjoint h (by decide))
@[simp] theorem read32_write8_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 8}
    (h : Disjoint a 1 b 4) : read32 (write8 m a v) b = read32 m b :=
  read32_congr ((writes8 m a v).agree_disjoint h (by decide))
@[simp] theorem read32_write16_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 16}
    (h : Disjoint a 2 b 4) : read32 (write16 m a v) b = read32 m b :=
  read32_congr ((writes16 m a v).agree_disjoint h (by decide))
@[simp] theorem read32_write32_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 32}
    (h : Disjoint a 4 b 4) : read32 (write32 m a v) b = read32 m b :=
  read32_congr ((writes32 m a v).agree_disjoint h (by decide))
@[simp] theorem read32_write64_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 64}
    (h : Disjoint a 8 b 4) : read32 (write64 m a v) b = read32 m b :=
  read32_congr ((writes64 m a v).agree_disjoint h (by decide))
@[simp] theorem read32_write128_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 128}
    (h : Disjoint a 16 b 4) : read32 (write128 m a v) b = read32 m b :=
  read32_congr ((writes128 m a v).agree_disjoint h (by decide))
@[simp] theorem read64_write8_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 8}
    (h : Disjoint a 1 b 8) : read64 (write8 m a v) b = read64 m b :=
  read64_congr ((writes8 m a v).agree_disjoint h (by decide))
@[simp] theorem read64_write16_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 16}
    (h : Disjoint a 2 b 8) : read64 (write16 m a v) b = read64 m b :=
  read64_congr ((writes16 m a v).agree_disjoint h (by decide))
@[simp] theorem read64_write32_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 32}
    (h : Disjoint a 4 b 8) : read64 (write32 m a v) b = read64 m b :=
  read64_congr ((writes32 m a v).agree_disjoint h (by decide))
@[simp] theorem read64_write64_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 64}
    (h : Disjoint a 8 b 8) : read64 (write64 m a v) b = read64 m b :=
  read64_congr ((writes64 m a v).agree_disjoint h (by decide))
@[simp] theorem read64_write128_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 128}
    (h : Disjoint a 16 b 8) : read64 (write128 m a v) b = read64 m b :=
  read64_congr ((writes128 m a v).agree_disjoint h (by decide))
@[simp] theorem read128_write8_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 8}
    (h : Disjoint a 1 b 16) : read128 (write8 m a v) b = read128 m b :=
  read128_congr ((writes8 m a v).agree_disjoint h (by decide))
@[simp] theorem read128_write16_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 16}
    (h : Disjoint a 2 b 16) : read128 (write16 m a v) b = read128 m b :=
  read128_congr ((writes16 m a v).agree_disjoint h (by decide))
@[simp] theorem read128_write32_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 32}
    (h : Disjoint a 4 b 16) : read128 (write32 m a v) b = read128 m b :=
  read128_congr ((writes32 m a v).agree_disjoint h (by decide))
@[simp] theorem read128_write64_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 64}
    (h : Disjoint a 8 b 16) : read128 (write64 m a v) b = read128 m b :=
  read128_congr ((writes64 m a v).agree_disjoint h (by decide))
@[simp] theorem read128_write128_of_disjoint {m : Memory} {a b : BitVec 64} {v : BitVec 128}
    (h : Disjoint a 16 b 16) : read128 (write128 m a v) b = read128 m b :=
  read128_congr ((writes128 m a v).agree_disjoint h (by decide))
/-! ### Deciding disjointness of constant offsets from a common base -/

theorem disjoint_add_add (x c₁ c₂ : BitVec 64) (n k : Nat) :
    Disjoint (x + c₁) n (x + c₂) k ↔ Disjoint c₁ n c₂ k := by
  simp only [Disjoint]
  rw [show x + c₂ - (x + c₁) = c₂ - c₁ by bv_omega, show x + c₁ - (x + c₂) = c₁ - c₂ by bv_omega]

theorem disjoint_base_add (x c : BitVec 64) (n k : Nat) :
    Disjoint x n (x + c) k ↔ Disjoint 0 n c k := by
  have := disjoint_add_add x 0 c n k; simpa using this

theorem disjoint_add_base (x c : BitVec 64) (n k : Nat) :
    Disjoint (x + c) n x k ↔ Disjoint c n 0 k := by
  have := disjoint_add_add x c 0 n k; simpa using this

/-- Disjointness of two literal addresses reduces to arithmetic on literals. -/
theorem disjoint_ofNat (a b n k : Nat) :
    Disjoint (BitVec.ofNat 64 a) n (BitVec.ofNat 64 b) k ↔
      n ≤ (BitVec.ofNat 64 b - BitVec.ofNat 64 a).toNat ∧
        k ≤ (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat := Iff.rfl

instance (a b : BitVec 64) (n k : Nat) : Decidable (Disjoint a n b k) := by
  unfold Disjoint; infer_instance

end Memory
end M1
