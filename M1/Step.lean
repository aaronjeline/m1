/-
  The fetch–decode–execute cycle.
-/
import M1.Decode
import M1.Exec

namespace M1

/-- Instruction memory: the 32-bit word at each (4-byte aligned) address, if
any code is mapped there. -/
abbrev Program := BitVec 64 → Option (BitVec 32)

namespace Program

/-- A contiguous block of instruction words starting at `base`. -/
def ofList (base : BitVec 64) (ws : List (BitVec 32)) : Program := fun a =>
  let off := a - base
  if off.toNat < 4 * ws.length ∧ off.toNat % 4 = 0 then ws[off.toNat / 4]? else none

/-- Union of two programs (left-biased). -/
def union (p q : Program) : Program := fun a => (p a).orElse fun _ => q a

/-- `p` contains all of `q`'s code (and possibly more, e.g. the libraries `q`
calls). Proving a specification for every `p` extending a binary's code, under
hypotheses about the external functions it calls, verifies the binary in any
process into which it is loaded together with conforming libraries. -/
def Extends (p q : Program) : Prop := ∀ a w, q a = some w → p a = some w

theorem Extends.refl (p : Program) : p.Extends p := fun _ _ h => h

end Program

/-- Execute one instruction. A stopped machine does not change. -/
def step (p : Program) (s : State) : State :=
  match s.status with
  | .running =>
    if !aligned s.pc 4 then s.fault (.pcAlignment s.pc) else
    match p s.pc with
    | none => s.fault (.fetch s.pc)
    | some w =>
      match decode w with
      | none => s.fault (.unsupported w)
      | some i => exec w i s
  | _ => s

/-- Where `q` has code, a program extending it executes the same instruction. -/
theorem step_of_extends {p q : Program} (h : p.Extends q) (s : State)
    (hf : (q s.pc).isSome = true) : step p s = step q s := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hf
  simp only [step, h _ _ hw, hw]

/-- Execute `n` instructions. -/
def run (p : Program) : Nat → State → State
  | 0, s => s
  | n + 1, s => run p n (step p s)

theorem run_zero (p : Program) (s : State) : run p 0 s = s := rfl
theorem run_succ (p : Program) (n : Nat) (s : State) : run p (n + 1) s = run p n (step p s) := rfl

theorem run_add (p : Program) (m n : Nat) (s : State) : run p (m + n) s = run p n (run p m s) := by
  induction m generalizing s with
  | zero => simp [run]
  | succ m ih => rw [Nat.add_right_comm, run_succ, run_succ, ih]

end M1
