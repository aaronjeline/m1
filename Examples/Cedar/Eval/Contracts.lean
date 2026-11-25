import Examples.Cedar.Eval.Code

/-!
# Contracts for the callees of `eval_expression`

`eval_expression(&request, &entities, expr)` (114 instructions, `Code.lean`)
builds an `Evaluator` (cloning the request), reads std's hashmap `KEYS`
thread-local (through its TLV descriptor) to make an empty slot map, calls
`Evaluator::interpret`, converts the result and drops the evaluator.

Its callees are specified by the contracts below; `Proofs.lean` proves
`eval_expression` from them. The type-soundness assumption moves from
`eval_expression` to `Evaluator::interpret` (`InterpretSpec`).

**Memory framing.** Objects are described by abstract predicates (`Preds`).
Two kinds of facts keep them valid across code that does not own them:

* every contract says which stack bytes the callee may change (`Keeps`): none
  in the frames above its entry `SP` (up to the stack top `top`), except its
  output object;
* each predicate is `Framed`: it depends only on its object's bytes and on
  memory off the stack (`[lo, top)`) other than the `KEYS` cells; callees
  that may change off-stack memory state which predicates they preserve.
-/

namespace Examples.Cedar.Eval
open M1

/-- Link address of the TLV descriptor of std's hashmap `KEYS` thread-local
(`__thread_vars`); its first word is the thunk dyld binds at load time. -/
def tlvDesc : BitVec 64 := 0x43e5e0#64

/-- `a` is in the stack, `[lo, top)`. -/
def OnStack (lo top a : BitVec 64) : Prop := (a - lo).toNat < (top - lo).toNat

/-- From `s` to `s'`, no byte in `[s.sp, top)` changes except the `n` bytes
at `out`. -/
def Keeps (top out : BitVec 64) (n : Nat) (s s' : State) : Prop :=
  ∀ a, (a - s.sp).toNat < (top - s.sp).toNat → n ≤ (a - out).toNat → s'.mem a = s.mem a

/-- The abstract objects. -/
structure Preds where
  /-- `WT m env e`: the expression at `e` is well-typed for the environment
  at `env` (established by `typechecks_in`). -/
  WT : Memory → BitVec 64 → BitVec 64 → Prop
  /-- A valid environment (its request is its first field). -/
  EnvOK : Memory → BitVec 64 → Prop
  /-- The static `Extensions`. -/
  ExtOK : BitVec 64 → Prop
  /-- `ReqCl m a env`: a clone of `env`'s request at `a`. -/
  ReqCl : Memory → BitVec 64 → BitVec 64 → Prop
  /-- `EvalOf m a env`: an `Evaluator` at `a` for `env`'s request and entities. -/
  EvalOf : Memory → BitVec 64 → BitVec 64 → Prop
  /-- An owned `Value` (0x30 bytes). -/
  ValOK : Memory → BitVec 64 → Prop
  /-- An owned `Expr` (0x70 bytes). -/
  ExprOK : Memory → BitVec 64 → Prop
  /-- An owned `EntityUIDEntry` (0x50 bytes). -/
  UidOK : Memory → BitVec 64 → Prop
  /-- `a` is a thread's `KEYS` cell (0x18 bytes). -/
  Keys : BitVec 64 → Prop

variable (P : Preds) (lo top : BitVec 64)

/-- `Q` depends only on the `n` bytes at `base` and on off-stack memory that
is not in a `KEYS` cell. -/
def Framed (base : BitVec 64) (n : Nat) (Q : Memory → Prop) : Prop :=
  ∀ m m', Q m →
    (∀ a, ((a - base).toNat < n ∨
        (¬ OnStack lo top a ∧ ∀ k, P.Keys k → 0x18 ≤ (a - k).toNat)) → m' a = m a) → Q m'

/-- The predicates' footprints. -/
structure Frames : Prop where
  wt : ∀ env e, Framed P lo top e 0x78 (fun m => P.WT m env e)
  ev : ∀ a env, Framed P lo top a 0x170 (fun m => P.EvalOf m a env)
  val : ∀ a, Framed P lo top a 0x30 (fun m => P.ValOK m a)
  expr : ∀ a, Framed P lo top a 0x70 (fun m => P.ExprOK m a)
  uid : ∀ a, Framed P lo top a 0x50 (fun m => P.UidOK m a)

/-- A call per the AAPCS64 that changes no stack byte above its `SP` other
than the `n` bytes at `out s`, and does not change the TLV descriptor (dyld's
`__thread_vars`, which Rust code never writes). -/
def Contract (p : Program) (entry : BitVec 64) (pre : State → Prop) (out : State → BitVec 64)
    (n : Nat) (post : State → State → Prop) : Prop :=
  FunSpec p entry (fun s => s.sp &&& 15#64 = 0#64 ∧ pre s)
    (fun s s' => CalleeSaved s s' ∧ Keeps top (out s) n s s' ∧
      s'.mem.read64 tlvDesc = s.mem.read64 tlvDesc ∧ post s s')

/-- The callee preserves every well-typedness fact. -/
def StableWT (s s' : State) : Prop := ∀ env e, P.WT s.mem env e → P.WT s'.mem env e
/-- The callee preserves every evaluator. -/
def StableEv (s s' : State) : Prop := ∀ a env, P.EvalOf s.mem a env → P.EvalOf s'.mem a env

/-- Contracts of `eval_expression`'s callees (`T` is the `KEYS` TLV thunk). -/
structure Callees (p : Program) (T : BitVec 64) : Prop where
  /-- `Extensions::all_available()` -/
  allAvailable : Contract top p ext_7 (fun _ => True) (fun _ => 0) 0
    (fun s s' => P.ExtOK (s'.gpr 0) ∧ StableWT P s s')
  /-- `Request::clone(out = x0, &request = x1)` -/
  clone : Contract top p ext_4 (fun s => P.EnvOK s.mem (s.gpr 1)) (fun s => s.gpr 0) 0x100
    (fun s s' => P.ReqCl s'.mem (s.gpr 0) (s.gpr 1) ∧ StableWT P s s')
  /-- `Evaluator::new(out = x8, request = x0 (moved), &entities = x1, &extensions = x2)` -/
  new : ∀ env, Contract top p ext_5
    (fun s => P.ReqCl s.mem (s.gpr 0) env ∧ s.gpr 1 = env + 0x1b0#64 ∧ P.ExtOK (s.gpr 2))
    (fun s => s.gpr 8) 0x170
    (fun s s' => P.EvalOf s'.mem (s.gpr 8) env ∧ StableWT P s s')
  /-- The TLV thunk: returns the calling thread's `KEYS` cell, off the stack. -/
  thunk : Contract top p T (fun _ => True) (fun _ => 0) 0
    (fun s s' => P.Keys (s'.gpr 0) ∧ (∀ i < 0x18, ¬ OnStack lo top (s'.gpr 0 + BitVec.ofNat 64 i)) ∧
      StableWT P s s' ∧ StableEv P s s')
  /-- `hashmap_random_keys()` -/
  randomKeys : Contract top p ext_8 (fun _ => True) (fun _ => 0) 0
    (fun s s' => StableWT P s s' ∧ StableEv P s s')
  /-- `EvalResult::from(value = x0 (moved), out = x8)` -/
  fromValue : Contract top p ext_3 (fun s => P.ValOK s.mem (s.gpr 0)) (fun s => s.gpr 8) 0xc0
    (fun s s' => StableEv P s s')
  /-- `drop_in_place::<EntityUIDEntry>(x0)`: other owned objects stay valid. -/
  dropUid : Contract top p ext_2 (fun s => P.UidOK s.mem (s.gpr 0)) (fun s => s.gpr 0) 0x50
    (fun s s' => (∀ a, Memory.Disjoint a 0x50 (s.gpr 0) 0x50 → P.UidOK s.mem a → P.UidOK s'.mem a) ∧
      (∀ a, Memory.Disjoint a 0x70 (s.gpr 0) 0x50 → P.ExprOK s.mem a → P.ExprOK s'.mem a) ∧
      (∀ a, Memory.Disjoint a 0x30 (s.gpr 0) 0x50 → P.ValOK s.mem a → P.ValOK s'.mem a))
  /-- `drop_in_place::<Expr>(x0)` -/
  dropExpr : Contract top p ext_0 (fun s => P.ExprOK s.mem (s.gpr 0)) (fun s => s.gpr 0) 0x70
    (fun _ _ => True)
  /-- `drop_in_place::<Value>(x0)` -/
  dropVal : Contract top p ext_1 (fun s => P.ValOK s.mem (s.gpr 0)) (fun s => s.gpr 0) 0x30
    (fun _ _ => True)

/-- Facts relating the abstract objects. -/
structure Facts : Prop where
  /-- A well-typed expression's environment is valid. -/
  envOfWT : ∀ m env e, P.WT m env e → P.EnvOK m env
  /-- An evaluator's fields: request entries at `+0x70`, `+0xc0`, `+0x110`;
  its context is a `Value` at `+8` when the first word is `-2`, else an `Expr`. -/
  fields : ∀ m a env, P.EvalOf m a env →
    P.UidOK m (a + 0x70#64) ∧ P.UidOK m (a + 0xc0#64) ∧ P.UidOK m (a + 0x110#64) ∧
    (m.read64 a = 0xfffffffffffffffe#64 → P.ValOK m (a + 8#64)) ∧
    (m.read64 a ≠ 0xfffffffffffffffe#64 → P.ExprOK m a)
  /-- Moving a `Value`'s 0x30 bytes (and leaving the rest of memory off the
  stack alone) moves the `Value`. -/
  moveVal : ∀ m m' a b, P.ValOK m a → (∀ i < 0x30, m' (b + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) →
    (∀ x, ¬ OnStack lo top x → m' x = m x) → P.ValOK m' b

/-- **The remaining assumption: type soundness of `Evaluator::interpret`.**
`interpret(&evaluator = x0, expr = x1, &slots = x2)`, result at `x8`: on an
evaluator for `env` and an expression well-typed for `env`, the result is not
`Err(EvaluationError::TypeError)` (first word below 7); an `Ok` (first word
`-1`) holds a valid `Value` at `+8`; the evaluator is unchanged. -/
def InterpretSpec (p : Program) : Prop :=
  ∀ env, Contract top p ext_6
    (fun s => P.EvalOf s.mem (s.gpr 0) env ∧ P.WT s.mem env (s.gpr 1))
    (fun s => s.gpr 8) 0xd0
    (fun s s' => 7 ≤ (s'.mem.read64 (s.gpr 8)).toNat ∧
      (s'.mem.read64 (s.gpr 8) = 0xffffffffffffffff#64 → P.ValOK s'.mem (s.gpr 8 + 8#64)) ∧
      P.EvalOf s'.mem (s.gpr 0) env)

end Examples.Cedar.Eval
