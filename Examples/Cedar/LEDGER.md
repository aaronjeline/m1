# Cedar soundness proof: ledger

Goal: prove, in the M1 model, with no assumption about Cedar's code, that
`type_soundness_violation` (`brk #0xc0de`) in `targets/cedar-check` is never
executed. Work proceeds bottom-up: each assumed contract is replaced by a
proof of that function's machine code from contracts of *its* callees.

Code reachable by direct calls from `typechecks_in` and `eval_expression`
(not counting indirect calls): about 961 functions, 158,000 instructions,
5,180 loops, 42 directly recursive functions, plus libSystem's allocator.

## Proved (machine code, `lake build`)

| Function | Instructions | File |
| --- | --- | --- |
| `verdict` | 78 | `Examples/Cedar/Proofs.lean` (`verdict_spec`, `violation_unreachable`) |

## In progress

| Function | Instructions | Status |
| --- | --- | --- |
| `eval_expression` | 114 | contracts written (`Eval/Contracts.lean`); proof `Eval/Proofs.lean` in progress |

## Assumed (hypotheses of the current top theorem)

| Contract | What it says | Notes |
| --- | --- | --- |
| `EvalSpec` (`eval_expression`) | on a well-typed expression, the result is not `Err(TypeError)` | to be replaced by `InterpretSpec` once `eval_expression` is proved |
| `TypechecksSpec` (`typechecks_in`) | returns `true` only for well-typed expressions | the validator: ~56,000 instructions reachable |

Under `InterpretSpec`, the soundness assumption sits on `Evaluator::interpret`
(81 instructions, calls `partial_interpret`, the recursive evaluator).
