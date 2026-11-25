import Examples.Cedar.Eval.Contracts
import Examples.Cedar.Proofs
import Examples.Cedar.Frame

namespace Examples.Cedar.Eval
open M1

variable (P : Preds) (lo top : BitVec 64)

/-- `eval_expression`'s contract as used by `verdict` (result at `sp + 8`). -/
def EvalSpec' (p : Program) (T : BitVec 64) : Prop :=
  FunSpec p sym_fn
    (fun s => s.sp &&& 15#64 = 0#64 ∧ s.gpr 1 = s.gpr 0 + 0x1b0#64 ∧ P.WT s.mem (s.gpr 0) (s.gpr 2) ∧
      s.gpr 8 = s.sp + 8#64 ∧ s.mem.read64 tlvDesc = T ∧
      (∀ i < 8, ¬ OnStack lo top (tlvDesc + BitVec.ofNat 64 i)) ∧
      0x350 ≤ (s.sp - lo).toNat ∧ (s.sp - lo).toNat + 0x100 ≤ (top - lo).toNat ∧
      Memory.Disjoint (s.gpr 2) 0x78 (s.sp - 0x350#64) 0x350)
    (fun s s' => 7 ≤ (s'.mem.read64 (s.gpr 8)).toNat ∧ CalleeSaved s s' ∧
      ∀ a, (a - s.sp).toNat < 0x100 → 0xc8 ≤ (a - s.gpr 8).toNat → s'.mem a = s.mem a)

/-- The registers saved by the prologue, at `E - 0x50 .. E`. -/
def Saved (s0 : State) (m : Memory) : Prop :=
  m.read64 (s0.sp + 0xffffffffffffffb0#64) = s0.gpr 28 ∧
  m.read64 (s0.sp + 0xffffffffffffffb8#64) = s0.gpr 27 ∧
  m.read64 (s0.sp + 0xffffffffffffffc0#64) = s0.gpr 24 ∧
  m.read64 (s0.sp + 0xffffffffffffffc8#64) = s0.gpr 23 ∧
  m.read64 (s0.sp + 0xffffffffffffffd0#64) = s0.gpr 22 ∧
  m.read64 (s0.sp + 0xffffffffffffffd8#64) = s0.gpr 21 ∧
  m.read64 (s0.sp + 0xffffffffffffffe0#64) = s0.gpr 20 ∧
  m.read64 (s0.sp + 0xffffffffffffffe8#64) = s0.gpr 19 ∧
  m.read64 (s0.sp + 0xfffffffffffffff0#64) = s0.gpr 29 ∧
  m.read64 (s0.sp + 0xfffffffffffffff8#64) = s0.gpr 30

/-- What holds throughout `eval_expression` after its prologue (`s0`: entry). -/
structure Inv (s0 s : State) : Prop where
  sp : s.sp = s0.sp + 0xfffffffffffffcb0#64
  saved : Saved s0 s.mem
  x25 : s.gpr 25 = s0.gpr 25
  x26 : s.gpr 26 = s0.gpr 26
  v : ∀ r : BitVec 5, 8 ≤ r.toNat → r.toNat ≤ 15 → (s.vreg r).setWidth 64 = (s0.vreg r).setWidth 64
  fpcr : s.fpcr = s0.fpcr
  /-- The caller's frame (256 bytes above entry `SP`) is unchanged outside the result. -/
  above : ∀ a, (a - s0.sp).toNat < 0x100 → 0xc8 ≤ (a - (s0.sp + 8#64)).toNat → s.mem a = s0.mem a

/-- Offsets from the frame base `S`: `(a - (S + d)) = (a - S) - d` modulo `2^64`. -/
theorem toNat_sub_add (a S d : BitVec 64) :
    (a - (S + d)).toNat = ((a - S).toNat + (2 ^ 64 - d.toNat)) % 2 ^ 64 := by
  rw [show a - (S + d) = (a - S) - d by grind, BitVec.toNat_sub]; omega

/-- The bytes `Inv` tracks: the saved registers and the caller's frame outside
the result, `[S + 0x300, S + 0x358)` and `[S + 0x420, S + 0x450)`. -/
def Tracked (S a : BitVec 64) : Prop :=
  0x300 ≤ (a - S).toNat ∧ (a - S).toNat < 0x450 ∧ ((a - S).toNat < 0x358 ∨ 0x420 ≤ (a - S).toNat)

/-- `Inv` survives a call whose contract keeps every tracked byte. -/
theorem Inv.of_call {s0 s s' : State} {out : BitVec 64} {n : Nat} (h : Inv s0 s)
    (hcs : CalleeSaved s s') (hk : Keeps top out n s s')
    (htop : 0x450 ≤ (top - (s0.sp + 0xfffffffffffffcb0#64)).toNat)
    (hout : ∀ a, Tracked (s0.sp + 0xfffffffffffffcb0#64) a → n ≤ (a - out).toNat) : Inv s0 s' := by
  obtain ⟨hr, hsp, hv, hf⟩ := hcs
  have keep : ∀ a, Tracked (s0.sp + 0xfffffffffffffcb0#64) a → s'.mem a = s.mem a := by
    intro a ha
    apply hk a _ (hout a ha)
    rw [h.sp]; unfold Tracked at ha; omega
  -- The saved registers: 80 bytes at `S + 0x300`.
  have hag : Memory.Agree s'.mem s.mem (s0.sp + 0xfffffffffffffcb0#64 + 0x300#64) 0x50 := by
    intro i hi
    apply keep
    unfold Tracked
    rw [show s0.sp + 0xfffffffffffffcb0#64 + 0x300#64 + BitVec.ofNat 64 i - (s0.sp + 0xfffffffffffffcb0#64) =
      0x300#64 + BitVec.ofNat 64 i by grind]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have rd : ∀ j, j + 8 ≤ 0x50 → s'.mem.read64 (s0.sp + 0xfffffffffffffcb0#64 + 0x300#64 + BitVec.ofNat 64 j) =
      s.mem.read64 (s0.sp + 0xfffffffffffffcb0#64 + 0x300#64 + BitVec.ofNat 64 j) :=
    fun j hj => Memory.read64_congr (Mem.agree_sub hag j 8 hj)
  have hsv := h.saved
  unfold Saved at hsv
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at rd
  have r0 := rd 0 (by decide); have r1 := rd 8 (by decide); have r2 := rd 16 (by decide)
  have r3 := rd 24 (by decide); have r4 := rd 32 (by decide); have r5 := rd 40 (by decide)
  have r6 := rd 48 (by decide); have r7 := rd 56 (by decide); have r8 := rd 64 (by decide)
  have r9 := rd 72 (by decide)
  simp only [BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceOfNat] at r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  refine ⟨hsp.trans h.sp, ?_, (hr 25 (by decide) (by decide)).trans h.x25,
    (hr 26 (by decide) (by decide)).trans h.x26,
    fun r h1 h2 => (hv r h1 h2).trans (h.v r h1 h2), hf.trans h.fpcr, ?_⟩
  · unfold Saved; rw [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9]; exact hsv
  · intro a h1 h2
    rw [← h.above a h1 h2]
    apply keep
    unfold Tracked
    rw [show a - (s0.sp + 0xfffffffffffffcb0#64) = (a - s0.sp) + 0x350#64 by grind]
    rw [toNat_sub_add] at h2
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h2 ⊢
    omega

/-- A word a callee's contract keeps. -/
theorem Keeps.read64 {s s' : State} {out : BitVec 64} {n : Nat} (hk : Keeps top out n s s')
    (b : BitVec 64)
    (hb : ∀ i < 8, (b + BitVec.ofNat 64 i - s.sp).toNat < (top - s.sp).toNat ∧
      n ≤ (b + BitVec.ofNat 64 i - out).toNat) :
    s'.mem.read64 b = s.mem.read64 b :=
  Memory.read64_congr fun i hi => hk _ (hb i hi).1 (hb i hi).2

/-- `CMN a, b` followed by `B.NE`. -/
theorem cond_ne_cmn (a b : BitVec 64) :
    conditionHolds 1#4 (addSub true false a b false).2 = (a + b != 0#64) := by
  simp [conditionHolds, addSub, addWithCarry, bne]

/-- `Inv` only depends on these fields. -/
theorem Inv.congr {s0 s s' : State} (h : Inv s0 s) (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem)
    (h25 : s'.gpr 25 = s.gpr 25) (h26 : s'.gpr 26 = s.gpr 26) (hv : s'.vreg = s.vreg)
    (hf : s'.fpcr = s.fpcr) : Inv s0 s' :=
  ⟨hsp.trans h.sp, hm ▸ h.saved, h25.trans h.x25, h26.trans h.x26, hv ▸ h.v, hf.trans h.fpcr,
    fun a h1 h2 => hm ▸ h.above a h1 h2⟩

theorem toNat_add_sub_add (x c d : BitVec 64) (i : Nat) :
    (x + c + BitVec.ofNat 64 i - (x + d)).toNat = (c.toNat + i + (2 ^ 64 - d.toNat)) % 2 ^ 64 := by
  rw [show x + c + BitVec.ofNat 64 i - (x + d) = c + BitVec.ofNat 64 i - d by grind,
    BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := c.isLt; have := d.isLt
  omega

theorem add_sub_self (x y : BitVec 64) : x + y - x = y := by grind

/-- Tracked bytes are outside a callee's output object (both relative to `s0.sp`). -/
macro "out_tac" : tactic => `(tactic| (
  intro a ha; unfold Tracked at ha
  simp only [upd, BitVec.reduceEq, reduceIte, ite_true, ite_false] at ha ⊢
  simp only [toNat_sub_add, BitVec.reduceToNat, Nat.reducePow, Nat.reduceSub] at ha ⊢
  omega))

/-- A word at `s0.sp + c` is kept by a callee (entry `SP` = `s0.sp - 0x350`). -/
macro "keep_tac" hsp:term : tactic => `(tactic| (
  intro i hi
  simp only [upd, BitVec.reduceEq, reduceIte, ite_true, ite_false, $hsp:term]
  constructor <;>
    simp only [toNat_add_sub_add, toNat_sub_add, BitVec.reduceToNat, Nat.reducePow, Nat.reduceSub,
      BitVec.add_assoc, BitVec.reduceAdd, add_sub_self, BitVec.toNat_add, BitVec.toNat_ofNat] at * <;>
    omega))

/-- Disjointness of two objects at constant offsets from `s0.sp`. -/
macro "disj_tac" : tactic => `(tactic| (
  simp only [upd, BitVec.reduceEq, reduceIte, ite_true, ite_false, Memory.disjoint_add_add]
  decide))

/-- The epilogue (`0x6113c`): restore the saved registers and return. -/
theorem epilogue (p : Program) (hp : p.Extends prog) (s0 s : State) (h : Inv s0 s)
    (hpc : s.pc = 0x6113c#64) (hst : s.status = .running) (hal0 : s0.sp &&& 15#64 = 0#64)
    (htag : 7 ≤ (s.mem.read64 (s0.sp + 8#64)).toNat) :
    Reaches p s fun s' => s'.pc = s0.gpr 30 ∧ s'.status = .running ∧
      7 ≤ (s'.mem.read64 (s0.sp + 8#64)).toNat ∧ CalleeSaved s0 s' ∧
      ∀ a, (a - s0.sp).toNat < 0x100 → 0xc8 ≤ (a - (s0.sp + 8#64)).toNat → s'.mem a = s0.mem a := by
  have hsp := h.sp
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := h.saved
  m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
  refine Reaches.done ⟨by simp [upd, e9], rfl, htag, ⟨?_, by simp, h.v, h.fpcr⟩, h.above⟩
  intro r h1 h2
  have h25 := h.x25; have h26 := h.x26
  have hr : r = 19#5 ∨ r = 20#5 ∨ r = 21#5 ∨ r = 22#5 ∨ r = 23#5 ∨ r = 24#5 ∨ r = 25#5 ∨
      r = 26#5 ∨ r = 27#5 ∨ r = 28#5 ∨ r = 29#5 := by bv_omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [upd, e0, e1, e2, e3, e4, e5, e6, e7, e8, h25, h26]
  all_goals first | exact h.x25 | exact h.x26

/-! ### The function's own stores -/

theorem write64_keep {m : Memory} {w a : BitVec 64} (v : BitVec 64) (h : 8 ≤ (a - w).toNat) :
    (m.write64 w v) a = m a := by
  rw [Memory.writes64 m w v a]; simp only [ite_eq_right_iff]; omega
theorem write128_keep {m : Memory} {w a : BitVec 64} (v : BitVec 128) (h : 16 ≤ (a - w).toNat) :
    (m.write128 w v) a = m a := by
  rw [Memory.writes128 m w v a]; simp only [ite_eq_right_iff]; omega
theorem write32_keep {m : Memory} {w a : BitVec 64} (v : BitVec 32) (h : 4 ≤ (a - w).toNat) :
    (m.write32 w v) a = m a := by
  rw [Memory.writes32 m w v a]; simp only [ite_eq_right_iff]; omega
theorem write8_keep {m : Memory} {w a : BitVec 64} (v : BitVec 8) (h : 1 ≤ (a - w).toNat) :
    (m.write8 w v) a = m a := by
  rw [Memory.writes8 m w v a]; simp only [ite_eq_right_iff]; omega

theorem sub_add_sub' (a b c : BitVec 64) : a - b + (b - c) = a - c := by grind

theorem add_sub_add_l (x c d : BitVec 64) : x + c - (x + d) = c - d := by grind

/-- A stack byte is at least `n` bytes past the start of an off-stack range of `n` bytes. -/
theorem far_of_off {a w : BitVec 64} {n : Nat} (ha : OnStack lo top a)
    (hw : ∀ i < n, ¬ OnStack lo top (w + BitVec.ofNat 64 i)) : n ≤ (a - w).toNat := by
  apply Nat.not_lt.mp; intro hlt
  apply hw _ hlt
  have : w + BitVec.ofNat 64 (a - w).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rwa [this]

/-- Bytes of `[S, S + 0x450)` (this frame and the caller's) are on the stack. -/
theorem onStack_of_frame {s0 : State} (hlo : 0x350 ≤ (s0.sp - lo).toNat)
    (htop : (s0.sp - lo).toNat + 0x100 ≤ (top - lo).toNat) {a : BitVec 64}
    (ha : (a - (s0.sp + 0xfffffffffffffcb0#64)).toNat < 0x450) : OnStack lo top a := by
  unfold OnStack
  have hS : (s0.sp + 0xfffffffffffffcb0#64 - lo).toNat = (s0.sp - lo).toNat - 0x350 := by
    rw [BitVec.sub_add_comm.symm, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat]
    have := (s0.sp - lo).isLt
    omega
  have htl := (top - lo).isLt
  rw [← sub_add_sub' a (s0.sp + 0xfffffffffffffcb0#64) lo, BitVec.toNat_add, hS]
  omega

theorem onStack_of_tracked {s0 : State} (hlo : 0x350 ≤ (s0.sp - lo).toNat)
    (htop : (s0.sp - lo).toNat + 0x100 ≤ (top - lo).toNat) {a : BitVec 64}
    (ha : Tracked (s0.sp + 0xfffffffffffffcb0#64) a) : OnStack lo top a :=
  onStack_of_frame lo top hlo htop ha.2.1

/-- A byte `d` into `[F, F+K)` is at least `N` past `e` when `[e, e+N)` and `[F, F+K)` are disjoint. -/
theorem far_of_disjoint {e F : BitVec 64} {N K : Nat} (hd : Memory.Disjoint e N F K) (d : Nat)
    (hdK : d < K) (hK : K < 2 ^ 63) : N ≤ (F + BitVec.ofNat 64 d - e).toNat := by
  obtain ⟨h1, h2⟩ := hd
  have hsum : (e - F).toNat + (F - e).toNat = 2 ^ 64 := by
    have h0 : (e - F + (F - e)).toNat = 0 := by
      rw [show e - F + (F - e) = 0#64 by grind]; rfl
    rw [BitVec.toNat_add] at h0
    have := (e - F).isLt; have := (F - e).isLt
    omega
  rw [show F + BitVec.ofNat 64 d - e = (F - e) + BitVec.ofNat 64 d by grind, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega

/-- A byte inside an on-stack object is on the stack. -/
theorem onStack_of_in {a e : BitVec 64} {n : Nat} (hin : (a - e).toNat < n)
    (h : ∀ i < n, OnStack lo top (e + BitVec.ofNat 64 i)) : OnStack lo top a := by
  have := h _ hin
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at this

/-- A byte of this frame (`F = S`) is at least `0x78` past the expression `e`. -/
theorem far_e {e F : BitVec 64} (hd : Memory.Disjoint e 0x78 F 0x350) (x : BitVec 64)
    (hx : (x - F).toNat < 0x350) : 0x78 ≤ (x - e).toNat := by
  have := far_of_disjoint hd (x - F).toNat hx (by decide)
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at this

/-- A range at `s0.sp + c` within `[S, S + 0x450)` is on the stack. -/
theorem onStack_range {s0 : State} (hlo : 0x350 ≤ (s0.sp - lo).toNat)
    (htop : (s0.sp - lo).toNat + 0x100 ≤ (top - lo).toNat) (c : BitVec 64) (n : Nat)
    (hc : (c - 0xfffffffffffffcb0#64).toNat + n ≤ 0x450) :
    ∀ i < n, OnStack lo top (s0.sp + c + BitVec.ofNat 64 i) := by
  intro i hi
  apply onStack_of_frame lo top hlo htop
  rw [toNat_add_sub_add, BitVec.toNat_sub] at *
  have := c.isLt
  simp only [BitVec.toNat_ofNat] at *
  omega

/-- A range at `s0.sp + c` within `[S, S + 0x350)` (this frame) is past the expression. -/
theorem far_e_range {s0 : State} {e : BitVec 64}
    (hd : Memory.Disjoint e 0x78 (s0.sp + 0xfffffffffffffcb0#64) 0x350) (c : BitVec 64) (n : Nat)
    (hc : (c - 0xfffffffffffffcb0#64).toNat + n ≤ 0x350) :
    ∀ i < n, ¬ (s0.sp + c + BitVec.ofNat 64 i - e).toNat < 0x78 := by
  intro i hi
  apply Nat.not_lt.mpr
  apply far_e hd
  rw [toNat_add_sub_add, BitVec.toNat_sub] at *
  have := c.isLt
  simp only [BitVec.toNat_ofNat] at *
  omega

/-- A byte of an object `[B, B+k)` is at least `n` before a range `[W, W+n)` above it. -/
theorem far_below {a B W : BitVec 64} {k n : Nat} (hin : (a - B).toNat < k)
    (hd : k ≤ (W - B).toNat) (hn : (W - B).toNat + n ≤ 2 ^ 64) : n ≤ (a - W).toNat := by
  rw [← sub_add_sub' a B W, BitVec.toNat_add]
  have h1 : (B - W).toNat = 2 ^ 64 - (W - B).toNat := by
    rw [show B - W = 0#64 - (W - B) by grind, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
    have := (W - B).isLt; omega
  rw [h1]; have := (a - B).isLt; omega

/-- `Inv` survives a change of memory that keeps the tracked bytes. -/
theorem Inv.of_mem {s0 s s' : State} (h : Inv s0 s) (hsp : s'.sp = s.sp)
    (h25 : s'.gpr 25 = s.gpr 25) (h26 : s'.gpr 26 = s.gpr 26) (hv : s'.vreg = s.vreg)
    (hf : s'.fpcr = s.fpcr)
    (hm : ∀ a, Tracked (s0.sp + 0xfffffffffffffcb0#64) a → s'.mem a = s.mem a) : Inv s0 s' := by
  have hag : Memory.Agree s'.mem s.mem (s0.sp + 0xfffffffffffffcb0#64 + 0x300#64) 0x50 := by
    intro i hi
    apply hm
    unfold Tracked
    rw [show s0.sp + 0xfffffffffffffcb0#64 + 0x300#64 + BitVec.ofNat 64 i - (s0.sp + 0xfffffffffffffcb0#64) =
      0x300#64 + BitVec.ofNat 64 i by grind]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have rd : ∀ j, j + 8 ≤ 0x50 → s'.mem.read64 (s0.sp + 0xfffffffffffffcb0#64 + 0x300#64 + BitVec.ofNat 64 j) =
      s.mem.read64 (s0.sp + 0xfffffffffffffcb0#64 + 0x300#64 + BitVec.ofNat 64 j) :=
    fun j hj => Memory.read64_congr (Mem.agree_sub hag j 8 hj)
  have hsv := h.saved
  unfold Saved at hsv
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at rd
  have r0 := rd 0 (by decide); have r1 := rd 8 (by decide); have r2 := rd 16 (by decide)
  have r3 := rd 24 (by decide); have r4 := rd 32 (by decide); have r5 := rd 40 (by decide)
  have r6 := rd 48 (by decide); have r7 := rd 56 (by decide); have r8 := rd 64 (by decide)
  have r9 := rd 72 (by decide)
  simp only [BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceOfNat] at r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  refine ⟨hsp.trans h.sp, ?_, h25.trans h.x25, h26.trans h.x26, hv ▸ h.v, hf.trans h.fpcr, ?_⟩
  · unfold Saved; rw [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9]; exact hsv
  · intro a h1 h2
    rw [← h.above a h1 h2]
    apply hm
    unfold Tracked
    rw [show a - (s0.sp + 0xfffffffffffffcb0#64) = (a - s0.sp) + 0x350#64 by grind]
    rw [toNat_sub_add] at h2
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h2 ⊢
    omega

set_option maxHeartbeats 1000000 in
/-- From `0x61100` (result written): drop the evaluator's fields and return. -/
theorem tail (p : Program) (hp : p.Extends prog) (T : BitVec 64) (hc : Callees P lo top p T)
    (s0 s : State) (h : Inv s0 s) (hpc : s.pc = 0x61100#64) (hst : s.status = .running)
    (hal0 : s0.sp &&& 15#64 = 0#64) (hx21 : s.gpr 21 = s0.sp + 0xfffffffffffffcb0#64)
    (hal : s0.sp + 0xfffffffffffffcb0#64 &&& 15#64 = 0#64)
    (htopS : 0x450 ≤ (top - (s0.sp + 0xfffffffffffffcb0#64)).toNat)
    (htag : 7 ≤ (s.mem.read64 (s0.sp + 8#64)).toNat)
    (hu1 : P.UidOK s.mem (s0.sp + 0xfffffffffffffd20#64))
    (hu2 : P.UidOK s.mem (s0.sp + 0xfffffffffffffd70#64))
    (hu3 : P.UidOK s.mem (s0.sp + 0xfffffffffffffdc0#64))
    (hval : s.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) = 0xfffffffffffffffe#64 →
      P.ValOK s.mem (s0.sp + 0xfffffffffffffcb8#64))
    (hexp : s.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) ≠ 0xfffffffffffffffe#64 →
      P.ExprOK s.mem (s0.sp + 0xfffffffffffffcb0#64)) :
    Reaches p s fun s' => s'.pc = s0.gpr 30 ∧ s'.status = .running ∧
      7 ≤ (s'.mem.read64 (s0.sp + 8#64)).toNat ∧ CalleeSaved s0 s' ∧
      ∀ a, (a - s0.sp).toNat < 0x100 → 0xc8 ≤ (a - (s0.sp + 8#64)).toNat → s'.mem a = s0.mem a := by
  have hsp := h.sp
  -- drop(evaluator.principal)
  m1_step; m1_step
  refine Reaches.trans (hc.dropUid _ rfl rfl ⟨by simpa [hsp] using hal, by simpa [upd, hx21] using hu1⟩) ?_
  rintro s1 ⟨h1pc, h1st, h1cs, h1k, -, h1u, h1e, h1v⟩
  have I1 : Inv s0 s1 := by
    refine Inv.of_call top (Inv.congr h ?_ ?_ ?_ ?_ ?_ ?_) h1cs h1k htopS ?_
    · simp [hsp]
    · rfl
    · simp [upd]
    · simp [upd]
    · rfl
    · rfl
    · out_tac
  have h1sp : s1.sp = s0.sp + 0xfffffffffffffcb0#64 := I1.sp
  have h1x21 : s1.gpr 21 = s0.sp + 0xfffffffffffffcb0#64 :=
    (h1cs.1 21 (by decide) (by decide)).trans (by simp [upd, hx21])
  have h1u2 := h1u _ (by disj_tac) hu2
  have h1u3 := h1u _ (by disj_tac) hu3
  have h1w : s1.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) = s.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) :=
    Keeps.read64 top h1k _ (by keep_tac htopS)
  have h1t : s1.mem.read64 (s0.sp + 8#64) = s.mem.read64 (s0.sp + 8#64) :=
    Keeps.read64 top h1k _ (by keep_tac htopS)
  have h1val : s1.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) = 0xfffffffffffffffe#64 →
      P.ValOK s1.mem (s0.sp + 0xfffffffffffffcb8#64) :=
    fun hw => h1v _ (by disj_tac) (hval (h1w.symm.trans hw))
  have h1exp : s1.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) ≠ 0xfffffffffffffffe#64 →
      P.ExprOK s1.mem (s0.sp + 0xfffffffffffffcb0#64) :=
    fun hw => h1e _ (by disj_tac) (hexp (fun h' => hw (h1w.trans h')))
  simp only [upd, BitVec.reduceEq, reduceIte, ite_true, ite_false] at h1pc
  -- drop(evaluator.action)
  m1_step; m1_step
  refine Reaches.trans (hc.dropUid _ rfl rfl ⟨by simpa [h1sp] using hal, by simpa [upd, h1x21] using h1u2⟩) ?_
  rintro s2 ⟨h2pc, h2st, h2cs, h2k, -, h2u, h2e, h2v⟩
  have I2 : Inv s0 s2 := by
    refine Inv.of_call top (Inv.congr I1 ?_ ?_ ?_ ?_ ?_ ?_) h2cs h2k htopS ?_
    · simp [h1sp]
    · rfl
    · simp [upd]
    · simp [upd]
    · rfl
    · rfl
    · out_tac
  have h2sp : s2.sp = s0.sp + 0xfffffffffffffcb0#64 := I2.sp
  have h2x21 : s2.gpr 21 = s0.sp + 0xfffffffffffffcb0#64 :=
    (h2cs.1 21 (by decide) (by decide)).trans (by simp [upd, h1x21])
  have h2u3 := h2u _ (by disj_tac) h1u3
  have h2w : s2.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) = s.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) :=
    (Keeps.read64 top h2k _ (by keep_tac htopS)).trans h1w
  have h2t : s2.mem.read64 (s0.sp + 8#64) = s.mem.read64 (s0.sp + 8#64) :=
    (Keeps.read64 top h2k _ (by keep_tac htopS)).trans h1t
  have h2val : s.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) = 0xfffffffffffffffe#64 →
      P.ValOK s2.mem (s0.sp + 0xfffffffffffffcb8#64) :=
    fun hw => h2v _ (by disj_tac) (h1val (h1w.trans hw))
  have h2exp : s.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) ≠ 0xfffffffffffffffe#64 →
      P.ExprOK s2.mem (s0.sp + 0xfffffffffffffcb0#64) :=
    fun hw => h2e _ (by disj_tac) (h1exp (fun h' => hw (h1w.symm.trans h')))
  simp only [upd, BitVec.reduceEq, reduceIte, ite_true, ite_false] at h2pc
  -- drop(evaluator.resource)
  m1_step; m1_step
  refine Reaches.trans (hc.dropUid _ rfl rfl ⟨by simpa [h2sp] using hal, by simpa [upd, h2x21] using h2u3⟩) ?_
  rintro s3 ⟨h3pc, h3st, h3cs, h3k, -, h3u, h3e, h3v⟩
  have I3 : Inv s0 s3 := by
    refine Inv.of_call top (Inv.congr I2 ?_ ?_ ?_ ?_ ?_ ?_) h3cs h3k htopS ?_
    · simp [h2sp]
    · rfl
    · simp [upd]
    · simp [upd]
    · rfl
    · rfl
    · out_tac
  have h3sp : s3.sp = s0.sp + 0xfffffffffffffcb0#64 := I3.sp
  have h3w : s3.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) = s.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) :=
    (Keeps.read64 top h3k _ (by keep_tac htopS)).trans h2w
  have h3t : s3.mem.read64 (s0.sp + 8#64) = s.mem.read64 (s0.sp + 8#64) :=
    (Keeps.read64 top h3k _ (by keep_tac htopS)).trans h2t
  have h3val : s.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) = 0xfffffffffffffffe#64 →
      P.ValOK s3.mem (s0.sp + 0xfffffffffffffcb8#64) :=
    fun hw => h3v _ (by disj_tac) (h2val hw)
  have h3exp : s.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) ≠ 0xfffffffffffffffe#64 →
      P.ExprOK s3.mem (s0.sp + 0xfffffffffffffcb0#64) :=
    fun hw => h3e _ (by disj_tac) (h2exp hw)
  simp only [upd, BitVec.reduceEq, reduceIte, ite_true, ite_false] at h3pc
  -- The context: a `Value` (first word `-2`) or an `Expr`.
  have hne := cond_ne_cmn
  m1_step; m1_step; m1_step
  split
  · -- drop_in_place::<Expr>(context): the first word is not `-2`.
    rename_i hne2
    have hw : s.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) ≠ 0xfffffffffffffffe#64 := by
      intro hc'; apply hne2; rw [hc']; rfl
    m1_step; m1_step
    refine Reaches.trans (hc.dropExpr _ rfl rfl ⟨by simpa [h3sp] using hal,
      by simpa [upd, h3sp] using h3exp hw⟩) ?_
    rintro s4 ⟨h4pc, h4st, h4cs, h4k, -, -⟩
    have I4 : Inv s0 s4 := by
      refine Inv.of_call top (Inv.congr I3 ?_ ?_ ?_ ?_ ?_ ?_) h4cs h4k htopS ?_
      · simp [h3sp]
      · rfl
      · simp [upd]
      · simp [upd]
      · rfl
      · rfl
      · out_tac
    have h4t : s4.mem.read64 (s0.sp + 8#64) = s.mem.read64 (s0.sp + 8#64) :=
      (Keeps.read64 top h4k _ (by keep_tac htopS)).trans h3t
    simp only [upd, BitVec.reduceEq, ite_true, ite_false] at h4pc
    refine epilogue p hp s0 s4 I4 h4pc h4st hal0 ?_
    rw [h4t]; exact htag
  · -- drop_in_place::<Value>(context + 8)
    rename_i hne2
    have hw : s.mem.read64 (s0.sp + 0xfffffffffffffcb0#64) = 0xfffffffffffffffe#64 := by
      simp only [Decidable.not_not] at hne2; bv_omega
    m1_step; m1_step; m1_step
    refine Reaches.trans (hc.dropVal _ rfl rfl ⟨by simpa [h3sp] using hal,
      by simpa [upd, h3sp] using h3val hw⟩) ?_
    rintro s4 ⟨h4pc, h4st, h4cs, h4k, -, -⟩
    have I4 : Inv s0 s4 := by
      refine Inv.of_call top (Inv.congr I3 ?_ ?_ ?_ ?_ ?_ ?_) h4cs h4k htopS ?_
      · simp [h3sp]
      · rfl
      · simp [upd]
      · simp [upd]
      · rfl
      · rfl
      · out_tac
    have h4t : s4.mem.read64 (s0.sp + 8#64) = s.mem.read64 (s0.sp + 8#64) :=
      (Keeps.read64 top h4k _ (by keep_tac htopS)).trans h3t
    simp only [upd, BitVec.reduceEq, ite_true, ite_false] at h4pc
    m1_step
    refine epilogue p hp s0 _ (Inv.congr I4 rfl rfl rfl rfl rfl rfl) rfl rfl hal0 ?_
    show 7 ≤ (s4.mem.read64 (s0.sp + 8#64)).toNat
    rw [h4t]; exact htag


set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- From `0x61028` (`x0` = the `KEYS` cell, `x8`/`x1` = its keys): build the
slot map, call `interpret`, write the result, and continue with `tail`. -/
theorem mid (p : Program) (hp : p.Extends prog) (T : BitVec 64) (hc : Callees P lo top p T)
    (hfr : Frames P lo top) (hf : Facts P lo top) (hi : InterpretSpec P top p)
    (s0 s : State) (env A : BitVec 64) (h : Inv s0 s) (hpc : s.pc = 0x61028#64)
    (hst : s.status = .running) (hal0 : s0.sp &&& 15#64 = 0#64)
    (hlo : 0x350 ≤ (s0.sp - lo).toNat) (htop : (s0.sp - lo).toNat + 0x100 ≤ (top - lo).toNat)
    (htopS : 0x450 ≤ (top - (s0.sp + 0xfffffffffffffcb0#64)).toNat)
    (hx0 : s.gpr 0 = A) (hKA : P.Keys A) (hAoff : ∀ i < 0x18, ¬ OnStack lo top (A + BitVec.ofNat 64 i))
    (hx19 : s.gpr 19 = s0.sp + 8#64) (hx20 : s.gpr 20 = s0.gpr 2)
    (hx24 : s.gpr 24 = s0.sp + 0xfffffffffffffe20#64) (hx29 : s.gpr 29 = s0.sp + 0xfffffffffffffff0#64)
    (hev : P.EvalOf s.mem (s0.sp + 0xfffffffffffffcb0#64) env) (hwt : P.WT s.mem env (s0.gpr 2))
    (heon : ∀ i < 0x78, OnStack lo top (s0.gpr 2 + BitVec.ofNat 64 i))
    (hedisj : Memory.Disjoint (s0.gpr 2) 0x78 (s0.sp - 0x350#64) 0x350) :
    Reaches p s fun s' => s'.pc = s0.gpr 30 ∧ s'.status = .running ∧
      7 ≤ (s'.mem.read64 (s0.sp + 8#64)).toNat ∧ CalleeSaved s0 s' ∧
      ∀ a, (a - s0.sp).toNat < 0x100 → 0xc8 ≤ (a - (s0.sp + 8#64)).toNat → s'.mem a = s0.mem a := by
  have hsp := h.sp
  have hal : s0.sp + 0xfffffffffffffcb0#64 &&& 15#64 = 0#64 := by bv_decide
  -- KEYS.k0 += 1; the slot map (an empty `HashMap` with these keys) at `E - 0xb0`.
  m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
  -- interpret(&evaluator = sp, expr, &slots), result at sp + 0x170
  m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
  have hedisj' : Memory.Disjoint (s0.gpr 2) 0x78 (s0.sp + 0xfffffffffffffcb0#64) 0x350 := by
    rwa [show s0.sp - 0x350#64 = s0.sp + 0xfffffffffffffcb0#64 by grind] at hedisj
  have hS := toNat_sub_add
  refine Reaches.trans (hi env _ rfl rfl ⟨by simpa using hal, ?_, ?_⟩) ?_
  · -- The evaluator survives the stores (KEYS cell, slot map).
    simp only [upd, BitVec.reduceEq, ite_true, ite_false]
    refine hfr.ev _ env s.mem _ hev ?_
    intro a ha
    rcases ha with hin | ⟨hoff, hnk⟩
    · have hon : OnStack lo top a := onStack_of_frame lo top hlo htop (Nat.lt_of_lt_of_le hin (by decide))
      have hA8 : 8 ≤ (a - A).toNat :=
        Nat.le_trans (show 8 ≤ 0x18 by decide) (Mem.far_of (Q := OnStack lo top) hon hAoff)
      have hst : ∀ c n, 0x170 ≤ (s0.sp + c - (s0.sp + 0xfffffffffffffcb0#64)).toNat →
          (s0.sp + c - (s0.sp + 0xfffffffffffffcb0#64)).toNat + n ≤ 2 ^ 64 → n ≤ (a - (s0.sp + c)).toNat :=
        fun c n h1 h2 => far_below hin h1 h2
      rw [write64_keep _ (hst _ 8 ?_ ?_), write64_keep _ (hst _ 8 ?_ ?_),
        Mem.write128_keep _ (hst _ 16 ?_ ?_), Mem.write128_keep _ (hst _ 16 ?_ ?_), write64_keep _ hA8]
      all_goals (rw [add_sub_add_l]; simp only [BitVec.reduceSub, BitVec.reduceToNat]; omega)
    · have hA8 : 8 ≤ (a - A).toNat := Nat.le_trans (show 8 ≤ 0x18 by decide) (hnk A hKA)
      have hst : ∀ c n, (c - 0xfffffffffffffcb0#64).toNat + n ≤ 0x450 → n ≤ (a - (s0.sp + c)).toNat :=
        fun c n hc => Mem.far_of (Q := fun x => ¬ OnStack lo top x) hoff fun i hi hn =>
          hn (onStack_range lo top hlo htop c n hc i hi)
      rw [write64_keep _ (hst _ 8 ?_), write64_keep _ (hst _ 8 ?_),
        Mem.write128_keep _ (hst _ 16 ?_), Mem.write128_keep _ (hst _ 16 ?_), write64_keep _ hA8]
      all_goals (simp only [BitVec.reduceSub, BitVec.reduceToNat]; omega)
  · -- The expression stays well-typed.
    simp only [upd, BitVec.reduceEq, ite_true, ite_false]
    refine hfr.wt env _ s.mem _ hwt ?_
    intro a ha
    rcases ha with hin | ⟨hoff, hnk⟩
    · have hon : OnStack lo top a := onStack_of_in lo top hin heon
      have hA8 : 8 ≤ (a - A).toNat :=
        Nat.le_trans (show 8 ≤ 0x18 by decide) (Mem.far_of (Q := OnStack lo top) hon hAoff)
      have hst : ∀ c n, (c - 0xfffffffffffffcb0#64).toNat + n ≤ 0x350 → n ≤ (a - (s0.sp + c)).toNat :=
        fun c n hc => Mem.far_of (Q := fun x => (x - s0.gpr 2).toNat < 0x78) hin
          (far_e_range hedisj' c n hc)
      rw [write64_keep _ (hst _ 8 ?_), write64_keep _ (hst _ 8 ?_),
        Mem.write128_keep _ (hst _ 16 ?_), Mem.write128_keep _ (hst _ 16 ?_), write64_keep _ hA8]
      all_goals (simp only [BitVec.reduceSub, BitVec.reduceToNat]; omega)
    · have hA8 : 8 ≤ (a - A).toNat := Nat.le_trans (show 8 ≤ 0x18 by decide) (hnk A hKA)
      have hst : ∀ c n, (c - 0xfffffffffffffcb0#64).toNat + n ≤ 0x450 → n ≤ (a - (s0.sp + c)).toNat :=
        fun c n hc => Mem.far_of (Q := fun x => ¬ OnStack lo top x) hoff fun i hi hn =>
          hn (onStack_range lo top hlo htop c n hc i hi)
      rw [write64_keep _ (hst _ 8 ?_), write64_keep _ (hst _ 8 ?_),
        Mem.write128_keep _ (hst _ 16 ?_), Mem.write128_keep _ (hst _ 16 ?_), write64_keep _ hA8]
      all_goals (simp only [BitVec.reduceSub, BitVec.reduceToNat]; omega)
  · sorry

theorem eval_spec (p : Program) (hp : p.Extends prog) (T : BitVec 64)
    (hc : Callees P lo top p T) (hfr : Frames P lo top) (hf : Facts P lo top)
    (hi : InterpretSpec P top p) :
    EvalSpec' P lo top p T := by
  intro s hpc hst ⟨hsp, hx1, hwt, hx8, htlv, htlvoff, hlo, htop, hdisj⟩
  simp only [sym_fn] at hpc
  m1_step; m1_step; m1_step; m1_step; m1_step; m1_step; m1_step
  trace_state
  sorry

end Examples.Cedar.Eval
