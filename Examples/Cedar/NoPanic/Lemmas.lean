import Examples.Cedar.NoPanic.Externals

/-!
# Lemmas shared by the per-function no-panic proofs
-/

namespace Examples.Cedar.NoPanic
open M1 Examples.Cedar.Eval

/-- `CMN a, b` (`ADDS XZR, a, b`) followed by `B.EQ`. -/
theorem cond_eq_cmn (a b : BitVec 64) :
    conditionHolds 0#4 (addSub true false a b false).2 = (a + b == 0#64) := by
  simp [conditionHolds, addSub, addWithCarry]

/-- `CMN a, b` followed by `B.NE`. -/
theorem cond_ne_cmn (a b : BitVec 64) :
    conditionHolds 1#4 (addSub true false a b false).2 = (a + b != 0#64) := by
  simp [conditionHolds, addSub, addWithCarry, bne]

/-- `ANDS`/`TST` (64-bit) followed by `B.EQ`. -/
theorem cond_eq_logic64 (r : BitVec 64) : conditionHolds 0#4 (logicFlags true r) = (r == 0#64) := by
  simp [conditionHolds, logicFlags]

/-- `ANDS`/`TST` (64-bit) followed by `B.NE`. -/
theorem cond_ne_logic64 (r : BitVec 64) : conditionHolds 1#4 (logicFlags true r) = (r != 0#64) := by
  simp [conditionHolds, logicFlags, bne]

/-- The bytes a 64-bit store changes are among the 8 it writes. -/
theorem write64_changed {m : Memory} {w x : BitVec 64} {v : BitVec 64}
    (h : (m.write64 w v) x ≠ m x) : (x - w).toNat < 8 := by
  rw [Memory.writes64 m w v x] at h
  by_cases hc : (x - w).toNat < 8
  · exact hc
  · simp only [hc, ite_false] at h; exact absurd rfl h

/-- `Keeps` composes. -/
theorem Keeps.trans {top out : BitVec 64} {n : Nat} {s₁ s₂ s₃ : State} (h₁ : Keeps top out n s₁ s₂)
    (h₂ : Keeps top out n s₂ s₃) (hsp : s₂.sp = s₁.sp) : Keeps top out n s₁ s₃ := by
  intro a h1 h2
  rw [← h₁ a h1 h2]
  exact h₂ a (by rw [hsp]; exact h1) h2

/-- A 64-bit store changes only its own 8 bytes. -/
theorem write64_keep {m : Memory} {w a : BitVec 64} (v : BitVec 64) (h : 8 ≤ (a - w).toNat) :
    (m.write64 w v) a = m a := by
  rw [Memory.writes64 m w v a]; simp only [ite_eq_right_iff]; omega

/-- `Keeps` with no output keeps every byte, whatever the output. -/
theorem Keeps.of_none {top out out' : BitVec 64} {n : Nat} {s s' : State} (h : Keeps top out' 0 s s') :
    Keeps top out n s s' := fun a h1 _ => h a h1 (Nat.zero_le _)

/-- A state whose memory is unchanged keeps every byte. -/
theorem Keeps.of_mem {top out : BitVec 64} {n : Nat} {s s' : State} (h : s'.mem = s.mem) :
    Keeps top out n s s' := fun _ _ _ => by rw [h]

/-- A single 64-bit store at the declared output keeps every other byte. -/
theorem Keeps.of_write64 {top w : BitVec 64} {s s' : State} {v : BitVec 64}
    (h : s'.mem = s.mem.write64 w v) : Keeps top w 8 s s' := fun _ _ h2 => by
  rw [h]; exact write64_keep v h2

/-- A block stays live across a store inside a live block (`MemFacts.frame`). -/
theorem live_write64 {H : Heap} {lo top : BitVec 64} (hH : MemFacts H lo top) {m : Memory}
    {b n al a nb alb w v : BitVec 64} (hl : H.Live m b n al) (ha : H.Live m a nb alb)
    (hin : (w - a).toNat + 8 ≤ nb.toNat) : H.Live (m.write64 w v) b n al := by
  refine hH.frame _ _ _ _ _ hl fun x hx => Or.inr ⟨a, nb, alb, ha, ?_⟩
  have h1 := write64_changed hx
  rw [show x - a = (x - w) + (w - a) by bv_omega, BitVec.toNat_add]
  have := Nat.mod_le ((x - w).toNat + (w - a).toNat) (2 ^ 64)
  omega

/-- A sub-range of a range disjoint from `[b, b+k)` is disjoint from it. -/
theorem _root_.M1.Memory.Disjoint.sub {a b c : BitVec 64} {n k m : Nat} (h : Memory.Disjoint a n b k)
    (hc : (c - a).toNat + m ≤ n) (hm : 0 < m) : Memory.Disjoint c m b k := by
  obtain ⟨h1, h2⟩ := h
  have hsum : (b - a).toNat + (a - b).toNat = 2 ^ 64 := by
    have h0 : (b - a + (a - b)).toNat = 0 := by
      rw [show b - a + (a - b) = 0#64 by bv_omega]; rfl
    rw [BitVec.toNat_add] at h0
    have := (b - a).isLt; have := (a - b).isLt
    have : (b - a).toNat ≠ 0 := by omega
    omega
  constructor
  · rw [show b - c = (b - a) - (c - a) by bv_omega, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
    omega
  · rw [show c - b = (c - a) + (a - b) by bv_omega, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    omega

/-! ### Changes confined to the stack -/

/-- `m'` differs from `m` only on the stack `[lo, top)`. -/
def StackOnly (lo top : BitVec 64) (m m' : Memory) : Prop := ∀ x, ¬ OnStack lo top x → m' x = m x

theorem StackOnly.refl (lo top : BitVec 64) (m : Memory) : StackOnly lo top m m := fun _ _ => rfl

theorem StackOnly.trans {lo top : BitVec 64} {m₁ m₂ m₃ : Memory} (h₁ : StackOnly lo top m₁ m₂)
    (h₂ : StackOnly lo top m₂ m₃) : StackOnly lo top m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

/-- A store of 8 bytes on the stack changes only the stack. -/
theorem StackOnly.write64 {lo top w : BitVec 64} (m : Memory) (v : BitVec 64)
    (h : ∀ i < 8, OnStack lo top (w + BitVec.ofNat 64 i)) : StackOnly lo top m (m.write64 w v) := by
  intro x hx
  by_cases hc : (x - w).toNat < 8
  · exfalso; apply hx
    have := h _ hc
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at this
  · exact write64_keep v (by omega)

/-- The TLV descriptor is off the stack, so a change confined to the stack keeps it. -/
theorem StackOnly.tlv {H : Heap} {lo top : BitVec 64} (hM : MemFacts H lo top) {m m' : Memory}
    (h : StackOnly lo top m m') : m'.read64 tlvDesc = m.read64 tlvDesc :=
  Memory.read64_congr fun i hi => h _ (hM.tlvOffStack i hi)

/-- A change confined to the stack keeps every live block live, with its contents. -/
theorem StackOnly.heapKept {H : Heap} {lo top : BitVec 64} (hM : MemFacts H lo top) {s s' : State}
    (h : StackOnly lo top s.mem s'.mem) (keep : BitVec 64 → Prop) : HeapKept H keep s s' :=
  fun _ _ _ _ hl => ⟨hM.frame _ _ _ _ _ hl fun x hx => Or.inl (Classical.byContradiction fun hc => hx (h x hc)),
    fun i hi => h _ (hM.offStack _ _ _ _ hl i hi)⟩

theorem HeapKept.trans {H : Heap} {k₁ k₂ : BitVec 64 → Prop} {s₁ s₂ s₃ : State}
    (h₁ : HeapKept H k₁ s₁ s₂) (h₂ : HeapKept H k₂ s₂ s₃) (hk : ∀ b, k₁ b → k₂ b) :
    HeapKept H k₁ s₁ s₃ := fun b n al hb hl =>
  ⟨(h₂ b n al (hk b hb) (h₁ b n al hb hl).1).1,
    fun i hi => ((h₂ b n al (hk b hb) (h₁ b n al hb hl).1).2 i hi).trans ((h₁ b n al hb hl).2 i hi)⟩

theorem HeapKept.mono {H : Heap} {k₁ k₂ : BitVec 64 → Prop} {s₁ s₂ : State}
    (h : HeapKept H k₂ s₁ s₂) (hk : ∀ b, k₁ b → k₂ b) : HeapKept H k₁ s₁ s₂ :=
  fun b n al hb hl => h b n al (hk b hb) hl

/-! ### Stack addresses -/

/-- `n` bytes at `w`, within `[sp, top)`, are on the stack when `sp` is. -/
theorem onStack_above {lo top sp w : BitVec 64} {n : Nat} (hsp : (sp - lo).toNat ≤ (top - lo).toNat)
    (hw : (w - sp).toNat + n ≤ (top - sp).toNat) : ∀ i < n, OnStack lo top (w + BitVec.ofNat 64 i) := by
  intro i hi
  unfold OnStack
  have e1 : (top - sp).toNat = (top - lo).toNat - (sp - lo).toNat := by
    rw [show top - sp = (top - lo) - (sp - lo) by grind,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
  rw [show w + BitVec.ofNat 64 i - lo = ((w - sp) + BitVec.ofNat 64 i) + (sp - lo) by grind,
    BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := (top - lo).isLt
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (a := (w - sp).toNat + i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- Bytes in the `f` bytes below `sp` are on the stack when the stack has room. -/
theorem onStack_below {lo top sp : BitVec 64} {f : Nat} (hlo : f ≤ (sp - lo).toNat)
    (hsp : (sp - lo).toNat ≤ (top - lo).toNat) (c : BitVec 64) (k : Nat)
    (hc : 2 ^ 64 - f ≤ c.toNat) (hk : c.toNat + k ≤ 2 ^ 64) :
    ∀ i < k, OnStack lo top (sp + c + BitVec.ofNat 64 i) := by
  intro i hi
  unfold OnStack
  rw [show sp + c + BitVec.ofNat 64 i - lo = (sp - lo) + (c + BitVec.ofNat 64 i) by grind,
    BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := (sp - lo).isLt
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (a := c.toNat + i) (by omega)]
  have : 2 ^ 64 ≤ (sp - lo).toNat + (c.toNat + i) := by omega
  rw [Nat.mod_eq_sub_mod this, Nat.mod_eq_of_lt (by omega)]
  omega

end Examples.Cedar.NoPanic
