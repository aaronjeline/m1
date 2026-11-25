/-
  Block-level symbolic execution for `SafeN` goals.

  * `m1_run` steps a goal `SafeN p B n s Q` (with `m1_safe_step`) through a
    basic block: it stops after a conditional branch (the state is then an
    `if`), a call (`bl`/`blr`: the PC is the callee's entry), a `ret`/`br`, when
    the PC leaves the code the run started in (a tail call; the code of
    another `Program.Extends` hypothesis, e.g. a callee's, is not entered),
    or when the PC is one of the given stop addresses: `m1_run until 0x348f2c#64`
    (if the PC already is one, nothing happens).
    Unconditional branches inside the code are followed.
  * `m1_run1` is the same, but the first instruction uses up one unit of the
    index (`m1_safe_step1`, for `SafeFun.fix`).
  * `m1_ite h` splits a goal on an `if` state (`SafeN.ite`), naming the
    condition `h` in both branches.
-/
import M1.Sym

namespace M1

namespace SafeRun

open Lean Meta Elab Tactic

/-- The literal PC of a state term: a structure literal (after stepping), or a
local hypothesis `s.pc = lit`. -/
def statePC? (st : Expr) : TacticM (Option (BitVec 64)) := do
  let e ← whnfR (mkApp (mkConst ``State.pc) st)
  if let some v ← Sym.getBV64 e then return some v
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, l, r) := ty.eq? then
      if l.isAppOfArity ``State.pc 1 && (← isDefEq l.appArg! st) then
        if let some v ← Sym.getBV64 r then return some v
  return none

/-- The instruction at `pc`, fetched from the code of a `Program.Extends`
hypothesis (only from the code starting at `only`, if given), with that code's base. -/
def fetch? (pc : BitVec 64) (only : Option (BitVec 64) := none) : TacticM (Option (Instr × BitVec 64)) := do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Program.Extends 2 then
      let q ← whnfR ty.appArg!
      let_expr Program.ofList b ws ← q | continue
      let some bv ← Sym.getBV64 b | continue
      if let some o := only then
        if o != bv then continue
      let some xs ← Sym.getListLit ws | continue
      let off := (pc - bv).toNat
      if off % 4 = 0 ∧ off / 4 < xs.length then
        let w := xs[off / 4]!
        let some ⟨k, v⟩ ← getBitVecValue? w | continue
        if h : k = 32 then
          return (decode (h ▸ v)).map (·, bv)
  return none

/-- Instructions after which `m1_run` stops. -/
def stopsAfter : Instr → Bool
  | .branch true _ => true
  | .branchCond .. | .cmpBranch .. | .testBranch .. | .branchReg .. => true
  | .svc _ | .brk _ => true
  | _ => false

/-- The goal's state, if the goal is `SafeN p B n s Q`. -/
def goalState? : TacticM (Option Expr) := do
  let ty ← instantiateMVars (← getMainTarget)
  let ty ← whnfR ty
  if ty.isAppOfArity ``SafeN 5 then return some (ty.getArg! 3) else return none

def run (stops : List (BitVec 64)) (first : Bool) : TacticM Unit := do
  let mut first := first
  let mut steps := 0
  -- The code the run started in: the run stops when it leaves it.
  let mut code : Option (BitVec 64) := none
  repeat
    -- `some (some i)`: step `i`; `some none`: the PC is not a literal (e.g. after
    -- a callee's exact-state contract), try a step; `none`: stop.
    let some oi ← withMainContext do
        let some st ← goalState? | return none
        if st.isAppOf ``ite || st.isAppOf ``dite then return none
        let some pc ← statePC? st | return some none
        if stops.contains pc then return none
        return (← fetch? pc code).map some
      | break
    let i ← match oi with
      | some (i, bv) => code := some bv; pure i
      | none =>
        let saved ← saveState
        try
          evalTactic (← if first then `(tactic| m1_safe_step1) else `(tactic| m1_safe_step))
          first := false
          steps := steps + 1
          continue
        catch _ =>
          restoreState saved
          break
    if first then
      evalTactic (← `(tactic| m1_safe_step1))
      first := false
    else
      evalTactic (← `(tactic| m1_safe_step))
    steps := steps + 1
    if stopsAfter i then break
  if steps = 0 && stops.isEmpty then throwError "m1_run: no instruction to step at the current state"

end SafeRun

open Lean Elab Tactic in
/-- Step a `SafeN` goal through a basic block (see the module doc). -/
elab "m1_run" " until"? stops:(ppSpace colGt term:max)* : tactic => do
  let mut ps := []
  for t in stops do
    let e ← Term.elabTerm t (some (mkApp (mkConst ``BitVec) (mkNatLit 64)))
    let some v ← Sym.getBV64 (← instantiateMVars e) | throwError "m1_run: not a 64-bit literal: {t}"
    ps := v :: ps
  SafeRun.run ps false

open Lean Elab Tactic in
/-- `m1_run`, with the first step using up one unit of the index (`m1_safe_step1`). -/
elab "m1_run1" " until"? stops:(ppSpace colGt term:max)* : tactic => do
  let mut ps := []
  for t in stops do
    let e ← Term.elabTerm t (some (mkApp (mkConst ``BitVec) (mkNatLit 64)))
    let some v ← Sym.getBV64 (← instantiateMVars e) | throwError "m1_run1: not a 64-bit literal: {t}"
    ps := v :: ps
  SafeRun.run ps true

/-- Split a goal `SafeN p B n (if c then s₁ else s₂) Q` into the two branches,
with the condition (`c` or `¬c`) named `h`. -/
macro "m1_ite " h:ident : tactic =>
  `(tactic| refine SafeN.ite (fun $h => ?_) (fun $h => ?_))

end M1

namespace M1.SafeRun
open Lean Meta Elab Tactic

/-- Split a hypothesis that is a chain of disjunctions into one goal per disjunct. -/
partial def splitOrs (n : Name) : TacticM Unit := do
  let isOr ← withMainContext do
    let ty ← instantiateMVars (← getLocalDeclFromUserName n).type
    return ty.isAppOfArity ``Or 2
  if isOr then
    let id := mkIdent n
    evalTactic (← `(tactic| rcases $id:ident with $id:ident | $id:ident))
    let gs ← getGoals
    let mut acc := []
    for g in gs do
      setGoals [g]
      splitOrs n
      acc := acc ++ (← getGoals)
    setGoals acc

/-- `split_ors h`: one goal per disjunct of `h : a ∨ b ∨ ...`, each named `h`. -/
elab "split_ors " h:ident : tactic => splitOrs h.getId

end M1.SafeRun
