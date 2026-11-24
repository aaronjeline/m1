/-
  A small program logic for total correctness of machine code.

  `Reaches p s Q` says that running program `p` from state `s` eventually
  (after finitely many steps) yields a state satisfying `Q`. Because a stopped
  machine (fault, SVC, BRK) never changes again, postconditions that require
  `status = .running` at a return address rule out every fault.
-/
import M1.Step
import M1.MemoryLemmas

namespace M1

/-- From `s`, execution of `p` reaches a state satisfying `Q`. -/
def Reaches (p : Program) (s : State) (Q : State → Prop) : Prop :=
  ∃ n, Q (run p n s)

namespace Reaches

variable {p : Program} {s : State} {Q R : State → Prop}

theorem done (h : Q s) : Reaches p s Q := ⟨0, h⟩

theorem step (h : Reaches p (M1.step p s) Q) : Reaches p s Q :=
  let ⟨n, h⟩ := h; ⟨n + 1, h⟩

theorem of_run (k : Nat) (h : Reaches p (run p k s) Q) : Reaches p s Q :=
  let ⟨n, h⟩ := h; ⟨k + n, by rw [run_add]; exact h⟩

theorem mono (h : Reaches p s Q) (hq : ∀ s, Q s → R s) : Reaches p s R :=
  let ⟨n, h⟩ := h; ⟨n, hq _ h⟩

/-- Sequential composition. -/
theorem trans (h : Reaches p s Q) (h2 : ∀ s', Q s' → Reaches p s' R) : Reaches p s R :=
  let ⟨n, h⟩ := h
  let ⟨m, h'⟩ := h2 _ h
  ⟨n + m, by rw [run_add]; exact h'⟩

theorem ite {c : Prop} [Decidable c] {s₁ s₂ : State}
    (h₁ : c → Reaches p s₁ Q) (h₂ : ¬c → Reaches p s₂ Q) :
    Reaches p (if c then s₁ else s₂) Q := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h₁ hc
  · simp only [hc, ite_false]; exact h₂ hc

/-- Loop rule: if from every state satisfying the invariant we either reach
the exit condition or come back to the invariant with a smaller measure,
then the exit condition is reached. -/
theorem loop (Inv : State → Prop) (μ : State → Nat)
    (body : ∀ s, Inv s → Reaches p s (fun s' => (Inv s' ∧ μ s' < μ s) ∨ Q s')) :
    ∀ s, Inv s → Reaches p s Q := by
  intro s
  induction h : μ s using Nat.strongRecOn generalizing s with
  | _ n ih =>
    intro hinv
    refine trans (body s hinv) ?_
    rintro s' (⟨hinv', hlt⟩ | hq)
    · exact ih (μ s') (h ▸ hlt) s' rfl hinv'
    · exact done hq

end Reaches

/-- Specification of a function at address `entry` under the AArch64
procedure call standard: started at `entry` in a running state satisfying
`pre`, execution returns to the caller (PC = the initial `X30`) still running,
with the initial and final states related by `post`. -/
def FunSpec (p : Program) (entry : BitVec 64) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ s, s.pc = entry → s.status = .running → pre s →
    Reaches p s fun s' => s'.pc = s.gpr 30 ∧ s'.status = .running ∧ post s s'

/-- The registers an AAPCS64 callee must preserve: `x19`–`x29`, `SP`, the
low 64 bits of `v8`–`v15`, and `FPCR` (its modes are global state that only
the `fenv` functions may change). -/
def CalleeSaved (s s' : State) : Prop :=
  (∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
  (∀ r : BitVec 5, 8 ≤ r.toNat → r.toNat ≤ 15 → (s'.vreg r).setWidth 64 = (s.vreg r).setWidth 64) ∧
  s'.fpcr = s.fpcr

/-- `FPCR` selects the default floating-point modes (round to nearest, no
flush-to-zero, no default NaN, IEEE half precision, traps disabled): the
precondition under which floating-point instructions are modelled. This is
the state of every macOS thread unless the program changes it via `fenv`. -/
def FPDefault (s : State) : Prop := s.fpcr &&& fpcrModeMask = 0

/-- The callee does not write the `n` bytes above its entry `SP` (the caller's
frame). -/
def FramePreserved (n : Nat) (s s' : State) : Prop :=
  ∀ a : BitVec 64, (a - s.sp).toNat < n → s'.mem a = s.mem a

theorem FramePreserved.agree {n : Nat} {s s' : State} (h : FramePreserved n s s') (off k : Nat)
    (hk : off + k ≤ n) (hn : n ≤ 2 ^ 64 := by decide) :
    Memory.Agree s'.mem s.mem (s.sp + BitVec.ofNat 64 off) k := by
  intro i hi
  apply h
  rw [BitVec.add_assoc, BitVec.add_comm s.sp, BitVec.add_sub_cancel]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1 : off % 2 ^ 64 = off := Nat.mod_eq_of_lt (by omega)
  have h2 : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A 64-bit load from the caller's frame, across a call that preserves it. -/
theorem FramePreserved.read64 {n : Nat} {s s' : State} (h : FramePreserved n s s') (off : Nat)
    (hk : off + 8 ≤ n := by decide) (hn : n ≤ 2 ^ 64 := by decide) :
    s'.mem.read64 (s.sp + BitVec.ofNat 64 off) = s.mem.read64 (s.sp + BitVec.ofNat 64 off) :=
  Memory.read64_congr (h.agree off 8 hk hn)

end M1
