/-
  A program logic for safety (partial correctness) of machine code.

  `Reaches` (in `Spec.lean`) is total correctness: execution must get to the
  postcondition. Some properties are better stated as safety: "execution never
  gets to a bad state (one that has stopped, or whose PC is in a set `B` of
  forbidden addresses, e.g. the entry points of the panic machinery) before it
  gets to `Q`". Running forever without getting to a bad state is allowed, so
  loops and recursion need invariants but no termination measures.

  The definition is step-indexed: `SafeN p B n s Q` looks only at the first `n`
  steps, and `Safe p B s Q` is `SafeN` for every `n`. The index is what makes
  recursive functions provable: to prove a function's specification at index
  `n + 1`, its first instruction is executed by `SafeN.step` (dropping to `n`),
  every later instruction by `SafeN.step'` (keeping `n`), and recursive calls use
  the specification at index `n` (`SafeFun.fix`).
-/
import M1.Spec

namespace M1

/-- A good state: running, with its PC outside the forbidden set `B`. -/
def Good (B : BitVec 64 → Prop) (s : State) : Prop := s.status = .running ∧ ¬ B s.pc

/-- In the first `n` steps from `s`, execution gets to `Q` before it gets to a
state that is not `Good B`, or does not get to such a state at all. -/
def SafeN (p : Program) (B : BitVec 64 → Prop) : Nat → State → (State → Prop) → Prop
  | 0, _, _ => True
  | n + 1, s, Q => Q s ∨ (Good B s ∧ SafeN p B n (step p s) Q)

/-- Execution of `p` from `s` never gets to a state that is not `Good B` before
it gets to `Q`. -/
def Safe (p : Program) (B : BitVec 64 → Prop) (s : State) (Q : State → Prop) : Prop :=
  ∀ n, SafeN p B n s Q

namespace SafeN

variable {p : Program} {B : BitVec 64 → Prop} {Q R : State → Prop}

theorem zero (s : State) : SafeN p B 0 s Q := trivial

theorem done {n : Nat} {s : State} (h : Q s) : SafeN p B n s Q := by
  cases n
  · trivial
  · exact Or.inl h

/-- Fewer steps: a smaller index. -/
theorem le {n : Nat} : ∀ {m : Nat} {s : State}, m ≤ n → SafeN p B n s Q → SafeN p B m s Q := by
  induction n with
  | zero => intro m s hm _; cases m <;> first | trivial | omega
  | succ n ih =>
    intro m s hm h
    cases m with
    | zero => trivial
    | succ m =>
      rcases h with h | ⟨hg, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨hg, ih (by omega) h⟩

theorem mono {n : Nat} {s : State} (h : SafeN p B n s Q) (hq : ∀ s, Q s → R s) :
    SafeN p B n s R := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    rcases h with h | ⟨hg, h⟩
    · exact Or.inl (hq _ h)
    · exact Or.inr ⟨hg, ih h⟩

/-- One step, using up one unit of the index. -/
theorem step {n : Nat} {s : State} (hr : s.status = .running) (hb : ¬ B s.pc)
    (h : SafeN p B n (M1.step p s) Q) : SafeN p B (n + 1) s Q :=
  Or.inr ⟨⟨hr, hb⟩, h⟩

/-- One step, keeping the index. -/
theorem step' {n : Nat} {s : State} (hr : s.status = .running) (hb : ¬ B s.pc)
    (h : SafeN p B n (M1.step p s) Q) : SafeN p B n s Q :=
  le (Nat.le_succ n) (step hr hb h)

/-- Sequential composition. -/
theorem trans {n : Nat} {s : State} (h : SafeN p B n s Q) (h2 : ∀ s', Q s' → SafeN p B n s' R) :
    SafeN p B n s R := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    rcases h with h | ⟨hg, h⟩
    · exact h2 _ h
    · exact Or.inr ⟨hg, ih h fun s' hq => le (Nat.le_succ n) (h2 s' hq)⟩

theorem ite {n : Nat} {c : Prop} [Decidable c] {s₁ s₂ : State}
    (h₁ : c → SafeN p B n s₁ Q) (h₂ : ¬c → SafeN p B n s₂ Q) :
    SafeN p B n (if c then s₁ else s₂) Q := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h₁ hc
  · simp only [hc, ite_false]; exact h₂ hc

/-- Loop rule (no measure: running forever is safe). From every state
satisfying the invariant, the body takes at least one good step and then
gets back to the invariant or to the exit condition. -/
theorem loop (Inv : State → Prop)
    (body : ∀ n s, Inv s → Good B s ∧ SafeN p B n (M1.step p s) (fun s' => Inv s' ∨ Q s')) :
    ∀ n s, Inv s → SafeN p B n s Q := by
  intro n
  induction n with
  | zero => intro _ _; trivial
  | succ n ih =>
    intro s hinv
    obtain ⟨hg, h⟩ := body n s hinv
    refine Or.inr ⟨hg, trans h ?_⟩
    rintro s' (hi | hq)
    · exact ih s' hi
    · exact done hq

end SafeN

namespace Safe

variable {p : Program} {B : BitVec 64 → Prop} {s : State} {Q R : State → Prop}

theorem done (h : Q s) : Safe p B s Q := fun _ => SafeN.done h

theorem step (hr : s.status = .running) (hb : ¬ B s.pc) (h : Safe p B (M1.step p s) Q) :
    Safe p B s Q := fun n => SafeN.step' hr hb (h n)

theorem mono (h : Safe p B s Q) (hq : ∀ s, Q s → R s) : Safe p B s R := fun n => (h n).mono hq

theorem trans (h : Safe p B s Q) (h2 : ∀ s', Q s' → Safe p B s' R) : Safe p B s R :=
  fun n => (h n).trans fun s' hq => h2 s' hq n

/-- **What `Safe` means.** If execution gets to a state that is not `Good B`
after `k` steps, it got to `Q` at or before step `k`. -/
theorem good_until (h : Safe p B s Q) (k : Nat) (hk : ¬ Good B (run p k s)) :
    ∃ j ≤ k, Q (run p j s) := by
  have := h (k + 1)
  clear h
  induction k generalizing s with
  | zero =>
    rcases this with hq | ⟨hg, _⟩
    · exact ⟨0, Nat.le_refl _, hq⟩
    · exact absurd hg hk
  | succ k ih =>
    rcases this with hq | ⟨_, h⟩
    · exact ⟨0, Nat.zero_le _, hq⟩
    · obtain ⟨j, hj, hq⟩ := ih (by rw [run_succ] at hk; exact hk) h
      exact ⟨j + 1, by omega, by rw [run_succ]; exact hq⟩

end Safe

/-- A function's safety specification at step index `n`: started at `entry`,
running, in a state satisfying `pre`, execution stays good for `n` steps unless
it returns to the caller (`PC` = the initial `X30`, still running) in a state
related to the initial one by `post`. -/
def SafeFun (p : Program) (B : BitVec 64 → Prop) (entry : BitVec 64) (pre : State → Prop)
    (post : State → State → Prop) (n : Nat) : Prop :=
  ∀ s, s.pc = entry → s.status = .running → pre s →
    SafeN p B n s fun s' => s'.pc = s.gpr 30 ∧ s'.status = .running ∧ post s s'

/-- A function's safety specification: it never gets to a bad state before it
returns, and when it returns, `post` holds. (Partial correctness: it may also
run forever.) -/
def SafeSpec (p : Program) (B : BitVec 64 → Prop) (entry : BitVec 64) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ n, SafeFun p B entry pre post n

namespace SafeFun

variable {p : Program} {B : BitVec 64 → Prop} {entry : BitVec 64} {pre : State → Prop}
  {post : State → State → Prop}

theorem le {m n : Nat} (hmn : m ≤ n) (h : SafeFun p B entry pre post n) :
    SafeFun p B entry pre post m :=
  fun s hpc hr hpre => (h s hpc hr hpre).le hmn

/-- **Recursion.** To prove a (possibly recursive) function at every index, it
suffices to prove it at index `n + 1` assuming it at index `n`: the function's
first step uses up one unit of the index (`SafeN.step`), so a recursive call,
which comes later, is covered by the assumption. -/
theorem fix (h : ∀ n, SafeFun p B entry pre post n → SafeFun p B entry pre post (n + 1)) :
    SafeSpec p B entry pre post := by
  intro n
  induction n with
  | zero => intro _ _ _ _; trivial
  | succ n ih => exact h n ih

end SafeFun

/-- Using a callee's specification at a call site: at its entry, with `X30` the
return address, the caller's goal follows from what holds after the return. -/
theorem SafeFun.call {p : Program} {B : BitVec 64 → Prop} {entry : BitVec 64} {pre : State → Prop}
    {post : State → State → Prop} {n : Nat} {s : State} {R : State → Prop}
    (hf : SafeFun p B entry pre post n) (hpc : s.pc = entry) (hr : s.status = .running) (hpre : pre s)
    (hk : ∀ s', s'.pc = s.gpr 30 → s'.status = .running → post s s' → SafeN p B n s' R) :
    SafeN p B n s R :=
  (hf s hpc hr hpre).trans fun s' ⟨h1, h2, h3⟩ => hk s' h1 h2 h3

end M1
