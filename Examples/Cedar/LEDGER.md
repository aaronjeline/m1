# Cedar soundness proof: ledger

Goal: prove, in the M1 model, with no assumption about Cedar's code, that
`type_soundness_violation` (`brk #0xc0de`) in `targets/cedar-check` is never
executed. Work proceeds bottom-up: each assumed contract is replaced by a
proof of that function's machine code from contracts of *its* callees.

Code reachable by direct calls from `typechecks_in` and `eval_expression`
(not counting indirect calls): about 961 functions, 158,000 instructions,
5,180 loops, 42 directly recursive functions, plus libSystem's allocator.

Current top theorem: `Examples.Cedar.violation_unreachable'`
(`Examples/Cedar/Main.lean`). Checked by `lake build`; axioms: Lean's
standard three plus `bv_decide` certificates; no `sorry`.

## Proved (machine code)

| Function | Instructions | Where |
| --- | --- | --- |
| `cedar_check::verdict` (incl. the assertion) | 78 (+2) | `Main.lean` (`verdict_spec'`) |
| `cedar_policy::eval_expression` | 114 | `Eval/Proofs.lean` (`eval_spec`) |

## Assumed (hypotheses of `violation_unreachable'`)

| Contract | Function | Status / notes |
| --- | --- | --- |
| **`InterpretSpec`** | `Evaluator::interpret` (81 instr., calls `partial_interpret`, the recursive evaluator) | **type soundness**: on a well-typed expression the result is not `Err(TypeError)` |
| `TypechecksSpec'` | `typechecks_in` (the validator, ~56,000 instr. reachable) | returns `true` only for well-typed expressions |
| `Callees.allAvailable` | `Extensions::all_available` | ABI and framing |
| `Callees.clone` | `Request::clone` | produces a clone of the request |
| `Callees.new` | `Evaluator::new` (66 instr.) | builds an evaluator for the environment |
| `Callees.thunk` | dyld's TLV thunk (libdyld) | returns the thread's `KEYS` cell, off the stack |
| `Callees.randomKeys` | `std::sys::random::hashmap_random_keys` | ABI and framing |
| `Callees.fromValue` | `EvalResult::from(Value)` | ABI and framing |
| `Callees.drop*` | drop glue for `EntityUIDEntry`, `Expr`, `Value` | ABI and framing |
| `Frames`, `Facts` | — | footprints of the abstract objects; an evaluator's fields; moving a `Value` |

## Next

1. `Evaluator::interpret` from a contract on `partial_interpret` (moves
   the assumption into the recursive evaluator).
2. A Lean model of Cedar values, types and expressions, and a relation
   between it and the byte layouts of `Expr`, `Value`, `Type`, so that
   `WT` and the evaluator's contracts can say *what* they compute.
3. `partial_interpret` by induction on the expression, case by case, from
   contracts on its leaf operations.
4. The validator (`typechecks_in`): the largest part.
