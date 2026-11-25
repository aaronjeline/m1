import M1
import Examples.Cedar.Eval.Contracts
import Examples.Cedar.NoPanic.Sinks

/-!
# The evaluator never panics: statement and contract shape

The property: started at `Evaluator::interpret`, execution never gets to a
state that has stopped (fault, `brk`, `svc`) or whose PC is the entry of
the panic machinery (`Panic`, the sinks listed in `INVENTORY.md`), unless it
has returned to its caller first. It is a safety property (`M1.Safe`), so
it says nothing about termination.

Every function reachable from `interpret` gets a contract of the shape
`NPContract`: a `SafeSpec` (never gets to a bad state; if it returns, it
returns per the AAPCS64), plus the frame facts its callers need for control-
flow integrity: callee-saved registers are restored and no byte of the
callers' frames changes except the callee's declared output. Those frame facts
are what keep saved return addresses intact, so every `ret` goes back to
its caller.

What is assumed rather than proved (see `LEDGER.md`):
* allocation succeeds (`__rust_alloc` and friends return non-null, or
  `handle_alloc_error` is never reached), and the stack does not overflow;
* the contracts of the external functions (allocator, `memcpy`, ...).
-/

namespace Examples.Cedar.NoPanic
open M1 Examples.Cedar.Eval

/-- A call per the AAPCS64 that never gets to a bad state (stopped, or a PC in
`B`) before it returns, and when it returns: callee-saved registers are
restored, no stack byte above its entry `SP` changes other than the `n` bytes at
`out s`, the TLV descriptor is unchanged, and `post` holds. -/
def NPContract (p : Program) (B : BitVec 64 → Prop) (top : BitVec 64) (entry : BitVec 64)
    (pre : State → Prop) (out : State → BitVec 64) (n : Nat) (post : State → State → Prop) : Prop :=
  SafeSpec p B entry (fun s => s.sp &&& 15#64 = 0#64 ∧ pre s)
    (fun s s' => CalleeSaved s s' ∧ Keeps top (out s) n s s' ∧
      s'.mem.read64 tlvDesc = s.mem.read64 tlvDesc ∧ post s s')

/-- `NPContract` at one step index (for recursive functions, `SafeFun.fix`). -/
def NPContractN (p : Program) (B : BitVec 64 → Prop) (top : BitVec 64) (entry : BitVec 64)
    (pre : State → Prop) (out : State → BitVec 64) (n : Nat) (post : State → State → Prop)
    (k : Nat) : Prop :=
  SafeFun p B entry (fun s => s.sp &&& 15#64 = 0#64 ∧ pre s)
    (fun s s' => CalleeSaved s s' ∧ Keeps top (out s) n s s' ∧
      s'.mem.read64 tlvDesc = s.mem.read64 tlvDesc ∧ post s s') k

/-- `NPContract` with the bad PCs fixed to `Panic` (the panic machinery). -/
abbrev NP (p : Program) := NPContract p Panic

end Examples.Cedar.NoPanic
