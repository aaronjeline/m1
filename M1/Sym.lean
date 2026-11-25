/-
  Symbolic execution support.

  * `reduceDecode` evaluates `decode w` for a literal instruction word (using
    the compiled decoder; the result is checked by the kernel by `rfl`).
  * `reduceFetch` evaluates `Program.ofList base ws a` for literal `base`, `a`
    and a literal list `ws` (possibly behind definitions).
  * The `m1_sym` simp set unfolds `step`/`exec` and the state accessors.
  * Lemmas turn `CMP`/`SUBS` + condition codes into BitVec comparisons.
  * `m1_step` performs one symbolic step on a goal `Reaches p s Q`.
-/
import Lean
import M1.Spec
import M1.MemoryLemmas
import M1.FPLemmas
import M1.SimpAttr

namespace M1

open Lean

deriving instance ToExpr for ShiftType
deriving instance ToExpr for AddrMode
deriving instance ToExpr for MemOp
deriving instance ToExpr for LogicOp
deriving instance ToExpr for MoveWideOp
deriving instance ToExpr for BitfieldOp
deriving instance ToExpr for DP1Op
deriving instance ToExpr for DP2Op
deriving instance ToExpr for DP3Op
deriving instance ToExpr for BranchRegOp
deriving instance ToExpr for AtomicOp
deriving instance ToExpr for FP.Rounding
deriving instance ToExpr for FP1Op
deriving instance ToExpr for FP2Op
deriving instance ToExpr for VecOp
deriving instance ToExpr for FVecOp
deriving instance ToExpr for FVec2Op
deriving instance ToExpr for FRedOp
deriving instance ToExpr for Vec2Op
deriving instance ToExpr for VecRedOp
deriving instance ToExpr for VecPermOp
deriving instance ToExpr for VecShiftOp
deriving instance ToExpr for VecLongOp
deriving instance ToExpr for VecElemOp
deriving instance ToExpr for CryptoOp
deriving instance ToExpr for Instr

namespace Sym

open Meta Simp

/-- Get a 64-bit literal, unfolding definitions if needed. -/
partial def getBV64 (e : Expr) : MetaM (Option (BitVec 64)) := do
  if let some ⟨n, v⟩ ← getBitVecValue? e then
    if h : n = 64 then return some (h ▸ v) else return none
  match ← withDefault (unfoldDefinition? e) with
  | some e' => getBV64 e'
  | none => return none

/-- Substitute every `let`/`have` binding in `e`. -/
partial def zetaAll : Expr → Expr
  | .letE _ _ v b _ => zetaAll (b.instantiate1 (zetaAll v))
  | .app f a => .app (zetaAll f) (zetaAll a)
  | e => e

/-- Get the elements of a list literal, unfolding definitions if needed. -/
partial def getListLit (e : Expr) : MetaM (Option (List Expr)) := do
  if let some (_, xs) := e.listLit? then return some xs
  -- Long list literals elaborate into chunks bound by `have`: substitute them.
  if e.isLet then return ← getListLit (zetaAll e)
  match ← withDefault (unfoldDefinition? e) with
  | some e' => getListLit e'
  | none => return none

/-- Evaluate `decode w` for a literal word. -/
dsimproc reduceDecode (decode _) := fun e => do
  let_expr decode w ← e | return .continue
  let some ⟨n, v⟩ ← getBitVecValue? w | return .continue
  if h : n = 32 then
    let ty := mkConst ``Instr
    match decode (h ▸ v) with
    | some i => return .done (mkApp2 (mkConst ``Option.some [0]) ty (toExpr i))
    | none => return .done (mkApp (mkConst ``Option.none [0]) ty)
  else return .continue

/-- Evaluate an instruction fetch from a literal program. -/
dsimproc reduceFetch (Program.ofList _ _ _) := fun e => do
  let e ← whnfR e
  let_expr Program.ofList b ws a ← e | return .continue
  let some bv ← getBV64 b | return .continue
  let some av ← getBV64 a | return .continue
  let some xs ← getListLit ws | return .continue
  let off := (av - bv).toNat
  let ty := mkApp (mkConst ``BitVec) (mkNatLit 32)
  if off < 4 * xs.length ∧ off % 4 = 0 then
    return .done (mkApp2 (mkConst ``Option.some [0]) ty xs[off / 4]!)
  else
    return .done (mkApp (mkConst ``Option.none [0]) ty)

end Sym

/-! ### Arithmetic and flag lemmas -/

section Flags

variable (a b : BitVec 64)

@[simp] theorem addSub_add64 (c : Bool) : (addSub true false a b c).1 = a + b + (if c then 1 else 0) := by
  simp only [addSub, addWithCarry, Bool.false_eq_true, ite_false, ite_true]

@[simp] theorem addSub_sub64 : (addSub true true a b true).1 = a - b := by
  simp only [addSub, addWithCarry, ite_true]; bv_decide

@[simp] theorem addSub_add32 : (addSub false false a b false).1 = (a.setWidth 32 + b.setWidth 32).setWidth 64 := by
  simp only [addSub, addWithCarry, Bool.false_eq_true, ite_false]; bv_decide

@[simp] theorem addSub_sub32 : (addSub false true a b true).1 = (a.setWidth 32 - b.setWidth 32).setWidth 64 := by
  simp only [addSub, addWithCarry, ite_true, Bool.false_eq_true, ite_false]; bv_decide

/-! Condition codes after `CMP a, b` (`SUBS XZR, a, b`), 64-bit. -/
@[simp] theorem cond_eq64 : conditionHolds 0#4 (addSub true true a b true).2 = (a == b) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_ne64 : conditionHolds 1#4 (addSub true true a b true).2 = (a != b) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_hs64 : conditionHolds 2#4 (addSub true true a b true).2 = decide (b ≤ a) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_lo64 : conditionHolds 3#4 (addSub true true a b true).2 = decide (a < b) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_hi64 : conditionHolds 8#4 (addSub true true a b true).2 = decide (b < a) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_ls64 : conditionHolds 9#4 (addSub true true a b true).2 = decide (a ≤ b) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_ge64 : conditionHolds 10#4 (addSub true true a b true).2 = b.sle a := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_lt64 : conditionHolds 11#4 (addSub true true a b true).2 = a.slt b := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_gt64 : conditionHolds 12#4 (addSub true true a b true).2 = b.slt a := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_le64 : conditionHolds 13#4 (addSub true true a b true).2 = a.sle b := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide

/-! Condition codes after `CMP wa, wb` (32-bit). -/
@[simp] theorem cond_eq32 : conditionHolds 0#4 (addSub false true a b true).2 = (a.setWidth 32 == b.setWidth 32) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_ne32 : conditionHolds 1#4 (addSub false true a b true).2 = (a.setWidth 32 != b.setWidth 32) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_hs32 : conditionHolds 2#4 (addSub false true a b true).2 = decide (b.setWidth 32 ≤ a.setWidth 32) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_lo32 : conditionHolds 3#4 (addSub false true a b true).2 = decide (a.setWidth 32 < b.setWidth 32) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_hi32 : conditionHolds 8#4 (addSub false true a b true).2 = decide (b.setWidth 32 < a.setWidth 32) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_ls32 : conditionHolds 9#4 (addSub false true a b true).2 = decide (a.setWidth 32 ≤ b.setWidth 32) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_ge32 : conditionHolds 10#4 (addSub false true a b true).2 = (b.setWidth 32).sle (a.setWidth 32) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_lt32 : conditionHolds 11#4 (addSub false true a b true).2 = (a.setWidth 32).slt (b.setWidth 32) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_gt32 : conditionHolds 12#4 (addSub false true a b true).2 = (b.setWidth 32).slt (a.setWidth 32) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide
@[simp] theorem cond_le32 : conditionHolds 13#4 (addSub false true a b true).2 = (a.setWidth 32).sle (b.setWidth 32) := by
  simp [conditionHolds, addSub, addWithCarry]; bv_decide

/-- `AL` -/
@[simp] theorem cond_al (f : NZCV) : conditionHolds 14#4 f = true := rfl

end Flags

/-! ### Arithmetic -/

/-- `MSUB q, b, a` after `UDIV q, a, b` computes the remainder. -/
theorem sub_udiv_mul_eq_umod {n : Nat} (a b : BitVec n) : a - a / b * b = a % b := by
  apply BitVec.eq_of_toNat_eq
  have hle : a.toNat / b.toNat * b.toNat ≤ a.toNat := Nat.div_mul_le_self _ _
  have ha := a.isLt
  have hm : (a.toNat / b.toNat * b.toNat) % 2 ^ n = a.toNat / b.toNat * b.toNat :=
    Nat.mod_eq_of_lt (by omega)
  simp only [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_umod, hm]
  have hd := Nat.mod_add_div a.toNat b.toNat
  rw [Nat.mul_comm] at hd
  generalize a.toNat / b.toNat * b.toNat = q at *
  generalize 2 ^ n = N at *
  rw [show N - q + a.toNat = (a.toNat - q) + N by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- Adding a multiple of 16 preserves 16-byte alignment (stack pointer updates). -/
theorem add_and15 (x c : BitVec 64) (h : c &&& 15#64 = 0#64) : (x + c) &&& 15#64 = x &&& 15#64 := by
  bv_decide

/-! ### State accessor lemmas -/

namespace State
variable (s : State) (r r' : Reg) (v : BitVec 64)

@[simp] theorem x_zr : s.x 31#5 = 0 := rfl
@[simp] theorem setX_zr : s.setX 31#5 v = s := rfl

end State

/-! ### The stepping tactic -/

-- `exec` is unfolded only through its per-instruction equations, so that a
-- step from an unknown instruction (e.g. a symbolic PC) gets stuck instead of
-- expanding every instruction's semantics. (One equation per `Instr` constructor.)
open Lean Elab Command in
/-- Tag every equation lemma of `exec` with `m1_sym`. -/
elab "m1_tag_exec_eqns" : command => do
  let some eqs ← liftTermElabM (Meta.getEqnsFor? ``M1.exec) | throwError "no equations for exec"
  for e in eqs do
    elabCommand (← `(attribute [m1_sym] $(mkIdent e)))

m1_tag_exec_eqns

-- Floating-point comparisons feeding condition codes, and FP register round trips.
attribute [m1_sym] FP.cond_eq FP.cond_ne FP.cond_hs FP.cond_lo FP.cond_mi FP.cond_pl FP.cond_vs
  FP.cond_vc FP.cond_hi FP.cond_ls FP.cond_ge FP.cond_lt FP.cond_gt FP.cond_le
  fpArg_fpRes64 fpArg_fpRes32 fpArg_fpRes16

-- Unfolding lemmas used for symbolic stepping.
attribute [m1_sym]
  add_and15 BitVec.add_assoc
  step fpOp satOp State.orFPSR VecOp.saturating Vec2Op.saturating VecShiftOp.saturating
  VecElemOp.saturating VecLongOp.saturating vec3QC vec2QC vshiftQC vlongQC velemQC
  Bool.false_and ctlOf_default trapped_default FP.fold_add FP.fold_sub FP.fold_mul FP.fold_mulx
  FP.fold_div FP.fold_mulAdd FP.fold_sqrt FP.fold_maxMin FP.fold_maxMinNum FP.fold_convert
  FP.fold_toInt FP.fold_ofInt FP.fold_compare FP.fold_cmpEQ FP.fold_cmpGE FP.fold_cmpGT
  FP.Ctl.fzN shiftReg BitVec.ofNat_eq_ofNat sub_udiv_mul_eq_umod
  dp1Compute dp2Compute dp3Compute BitVec.zero_or
  BitVec.or_zero BitVec.add_zero BitVec.zero_add BitVec.zero_and
  BitVec.and_zero BitVec.xor_zero BitVec.zero_xor Bool.bne_false
  beq_iff_eq bne_iff_ne BitVec.shiftLeft_zero BitVec.ushiftRight_zero
  BitVec.setWidth_eq Bool.not_eq_true' aligned
  atomicAligned State.x State.xsp State.setX
  State.setXSP State.setV State.setFlags State.setPC
  State.nextPC State.setMem State.fault upd
  trunc sized logicWrite logicCompute
  ldstOne withAddr spFault Memory.readN
  Memory.writeN zextBytes sextBytes addSub_add64
  addSub_sub64 addSub_add32 addSub_sub32 cond_eq64
  cond_ne64 cond_hs64 cond_lo64 cond_hi64
  cond_ls64 cond_ge64 cond_lt64 cond_gt64
  cond_le64 cond_eq32 cond_ne32 cond_hs32
  cond_lo32 cond_hi32 cond_ls32 cond_ge32
  cond_lt32 cond_gt32 cond_le32 cond_al
  ite_true ite_false dite_true dite_false
  Bool.not_true Bool.not_false Bool.true_and Bool.false_and
  Bool.and_true Bool.and_false Bool.or_true Bool.or_false
  Bool.true_or Bool.false_or beq_self_eq_true Option.some.injEq
  ne_eq not_false_eq_true not_true_eq_false and_self
  and_true true_and Bool.false_eq_true decide_true
  decide_false Bool.decide_eq_true
  Memory.read8_write8_same Memory.read8_write8_of_disjoint Memory.read8_write16_of_disjoint
  Memory.read8_write32_of_disjoint Memory.read8_write64_of_disjoint Memory.read8_write128_of_disjoint
  Memory.read16_write16_same Memory.read16_write8_of_disjoint Memory.read16_write16_of_disjoint
  Memory.read16_write32_of_disjoint Memory.read16_write64_of_disjoint Memory.read16_write128_of_disjoint
  Memory.read32_write32_same Memory.read32_write8_of_disjoint Memory.read32_write16_of_disjoint
  Memory.read32_write32_of_disjoint Memory.read32_write64_of_disjoint Memory.read32_write128_of_disjoint
  Memory.read64_write64_same Memory.read64_write8_of_disjoint Memory.read64_write16_of_disjoint
  Memory.read64_write32_of_disjoint Memory.read64_write64_of_disjoint Memory.read64_write128_of_disjoint
  Memory.read128_write128_same Memory.read128_write8_of_disjoint Memory.read128_write16_of_disjoint
  Memory.read128_write32_of_disjoint Memory.read128_write64_of_disjoint Memory.read128_write128_of_disjoint
  Memory.disjoint_add_add Memory.disjoint_base_add Memory.disjoint_add_base Memory.disjoint_ofNat id_eq
  Memory.readV Memory.writeV Option.isSome_some

/-- Simplify with the symbolic-execution simp set (plus all hypotheses). -/
macro "m1_simp_step" : tactic =>
  `(tactic| simp only
      [m1_sym, *, Nat.reduceLeDiff, Nat.reduceBEq, Nat.reduceBNe, decide_eq_true_eq, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceBNe, BitVec.reduceNe, Sym.reduceDecode, Sym.reduceFetch, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceAnd, BitVec.reduceOfNat, BitVec.reduceHShiftLeft, BitVec.reduceNot, BitVec.reduceToNat, BitVec.reduceOr, BitVec.reduceXOr, BitVec.reduceMul, BitVec.reduceHShiftRight, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceSignExtend, BitVec.reduceExtractLsb', BitVec.reduceAllOnes, BitVec.reduceAppend, BitVec.reduceGetLsb, BitVec.reduceULT, BitVec.reduceULE, BitVec.reduceLT, BitVec.reduceLE, BitVec.reduceRotateRight, BitVec.reduceSShiftRight, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, reduceDIte, reduceCtorEq, ↓reduceIte])

/-- Symbolically execute one instruction. The goal is `Reaches p s Q`, where
either `p` is a concrete program (`Program.ofList ...`) or there is a
hypothesis `p.Extends q` with `q` concrete; in the latter case the instruction
is fetched from `q` (which must have code at the current PC). Uses the
hypotheses in context (e.g. `s.pc = ...`, `s.status = .running`). -/
macro "m1_step" : tactic =>
  `(tactic| (apply Reaches.step; try simp only [BitVec.ofNat_eq_ofNat] at *
             try (rw [step_of_extends (by assumption) _ (by m1_simp_step)])
             m1_simp_step))

end M1
