/-
  The AAPCS64 procedure call standard, as Apple's arm64 ABI uses it: names
  for arguments and results, the conditions under which every function is
  entered, the obligations every function meets, and the rule for composing
  a call with the callee's specification.
-/
import M1.Spec
import M1.Sym

namespace M1.ABI

/-! ### Arguments and results -/

/-- The `i`-th integer/pointer argument (`x0`–`x7`). -/
def arg (s : State) (i : Nat) : BitVec 64 := s.gpr (BitVec.ofNat 5 i)

/-- The `i`-th integer argument of a 32-bit type (`w0`–`w7`). Apple's ABI
extends sub-32-bit arguments to 32 bits at the caller; the high half of the
register is unspecified. -/
def arg32 (s : State) (i : Nat) : BitVec 32 := (arg s i).setWidth 32

/-- The `i`-th floating-point argument of `N` bits (`d0`–`d7`, `s0`–`s7`,
`h0`–`h7`), as an IEEE bit pattern. -/
def fpArgN (s : State) (N i : Nat) : Nat := fpArg (s.vreg (BitVec.ofNat 5 i)) N

/-- The `k`-th 8-byte stack slot at entry (arguments beyond the registers;
Apple packs smaller stack arguments to their natural alignment, so read
those with `Memory.read32` etc. at the right offset). -/
def stackArg (s : State) (k : Nat) : BitVec 64 := s.mem.read64 (s.sp + BitVec.ofNat 64 (8 * k))

/-- The integer/pointer result (`x0`). -/
def ret (s : State) : BitVec 64 := s.gpr 0

/-- A 32-bit integer result (`w0`). -/
def ret32 (s : State) : BitVec 32 := (s.gpr 0).setWidth 32

/-- An `N`-bit floating-point result (`d0`/`s0`/`h0`). -/
def fpRet (s : State) (N : Nat) : Nat := fpArg (s.vreg 0) N

attribute [m1_sym] arg arg32 fpArgN stackArg ret ret32 fpRet

/-! ### Entry conditions and obligations -/

/-- The state at every function entry under the ABI: SP 16-byte aligned and
the default floating-point environment (unless the program uses `fenv`). -/
def Entry (s : State) : Prop := s.sp &&& 15#64 = 0#64 ∧ FPDefault s

/-- A function specification under the ABI: from any entry state satisfying
`Entry` and `pre`, the function returns to `x30` with the callee-saved state
preserved, and `post` holds. -/
def Spec (p : Program) (entry : BitVec 64) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  FunSpec p entry (fun s => Entry s ∧ pre s) fun s s' => CalleeSaved s s' ∧ post s s'

theorem _root_.M1.CalleeSaved.refl (s : State) : CalleeSaved s s :=
  ⟨fun _ _ _ => rfl, rfl, fun _ _ _ => rfl, rfl⟩

theorem _root_.M1.CalleeSaved.trans {s₁ s₂ s₃ : State} (h₁ : CalleeSaved s₁ s₂) (h₂ : CalleeSaved s₂ s₃) :
    CalleeSaved s₁ s₃ :=
  ⟨fun r a b => (h₂.1 r a b).trans (h₁.1 r a b), h₂.2.1.trans h₁.2.1,
   fun r a b => (h₂.2.2.1 r a b).trans (h₁.2.2.1 r a b), h₂.2.2.2.trans h₁.2.2.2⟩

/-- Individual callee-saved registers, for use after a call. -/
theorem _root_.M1.CalleeSaved.gpr {s s' : State} (h : CalleeSaved s s') (r : BitVec 5)
    (h1 : 19 ≤ r.toNat := by decide) (h2 : r.toNat ≤ 29 := by decide) : s'.gpr r = s.gpr r :=
  h.1 r h1 h2

theorem _root_.M1.CalleeSaved.sp {s s' : State} (h : CalleeSaved s s') : s'.sp = s.sp := h.2.1

theorem _root_.M1.CalleeSaved.fpcr {s s' : State} (h : CalleeSaved s s') : s'.fpcr = s.fpcr := h.2.2.2

/-- The FP environment survives a call. -/
theorem _root_.M1.CalleeSaved.fpDefault {s s' : State} (h : CalleeSaved s s') (hd : FPDefault s) :
    FPDefault s' := by
  simp only [FPDefault, h.fpcr]; exact hd

/-- The ABI entry conditions survive a call (SP and FPCR are preserved). -/
theorem _root_.M1.CalleeSaved.entry {s s' : State} (h : CalleeSaved s s') (he : Entry s) : Entry s' := by
  refine ⟨?_, h.fpDefault he.2⟩
  rw [h.sp]; exact he.1

/-! ### Calls -/

/-- **Call rule.** At the callee's entry (after `BL`/`BLR`, so `x30` is the
return address) in a state meeting its precondition, execution reaches the
return address with the callee-saved state preserved and the callee's
postcondition; the caller then continues from there. -/
theorem Spec.call {p : Program} {entry : BitVec 64} {pre : State → Prop}
    {post : State → State → Prop} (h : Spec p entry pre post) {s : State} {Q : State → Prop}
    (hpc : s.pc = entry) (hst : s.status = .running) (he : Entry s) (hpre : pre s)
    (k : ∀ s', s'.pc = s.gpr 30 → s'.status = .running → CalleeSaved s s' → post s s' →
      Reaches p s' Q) : Reaches p s Q :=
  Reaches.trans (h s hpc hst ⟨he, hpre⟩) fun _ ⟨h1, h2, h3, h4⟩ => k _ h1 h2 h3 h4

/-- Weakening a specification. -/
theorem Spec.mono {p : Program} {entry : BitVec 64} {pre pre' : State → Prop}
    {post post' : State → State → Prop} (h : Spec p entry pre post)
    (hpre : ∀ s, pre' s → pre s) (hpost : ∀ s s', pre' s → post s s' → post' s s') :
    Spec p entry pre' post' := by
  intro s hpc hst ⟨he, hp⟩
  exact (h s hpc hst ⟨he, hpre s hp⟩).mono fun s' ⟨a, b, c, d⟩ => ⟨a, b, c, hpost s s' hp d⟩

end M1.ABI
