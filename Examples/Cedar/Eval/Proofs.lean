import Examples.Cedar.Eval.Contracts
import Examples.Cedar.Proofs

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
