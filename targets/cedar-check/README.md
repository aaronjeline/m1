# cedar-check: a Cedar type-soundness target

A verification target for the M1 model, built from the
[Cedar](https://github.com/cedar-policy/cedar) policy language (pinned to
commit `165f5ed`).

`cedar_check(src, len)` (C ABI, exported from the dylib):

1. **parses** the bytes as a Cedar expression → returns `0` if they are not
   UTF-8 or not an expression;
2. **typechecks** it with Cedar's validator in strict mode, against the schema
   in `src/lib.rs` → returns `1` if it is ill-typed;
3. **evaluates** it against a request and entity store that conform to that
   schema → returns `2` for a value, `3` for an error the typechecker does
   not rule out (missing entity, integer overflow, extension failure, ...);
4. if evaluation raises a **type error**, the typechecker was unsound:
   that path is asserted unreachable. On AArch64 it is a single
   `brk #0xc0de` (function `type_soundness_violation`), which stops the
   model with status `.brk 0xc0de`.

The property to verify is that `cedar_check` never reaches `brk #0xc0de`.

## Verification (`Examples/Cedar/Proofs.lean`)

The only call to `type_soundness_violation` in the whole binary is in
`verdict` (typecheck, evaluate, classify), which is kept out of line so that
its machine code is small: 78 instructions, extracted with
`./extract-verdict.py` into `Examples/Cedar/Code.lean` together with the
`brk` itself. `violation_unreachable` proves, in the M1 model, that started
at `verdict` in a state meeting its precondition, execution returns to the
caller still running, and no state before the return is at
`type_soundness_violation`.

**Proved** (about the extracted machine code): the compiled control flow
reaches the `brk` only when `eval_expression` returns a result whose first
word is below 7, which is rustc's encoding of `Err(EvaluationError::TypeError)`
in `Result<EvalResult, EvaluationError>`; the expression and environment
evaluated are the ones that were typechecked (same pointers, memory unchanged
in between); and every other path (ill-typed, value, other evaluation error)
returns to the caller with the `Outcome` tag 1, 2 or 3 written, its saved
registers restored from a frame that neither the callees nor the stores to
the result clobber.

**Assumed** (hypotheses of the theorem, about code outside the extracted
range):

* `TypechecksSpec`: `typechecks_in` returns per the AAPCS64 without writing
  its caller's frame, and when it returns `true` the expression satisfies the
  abstract predicate `WT` (well-typed in the environment).
* `EvalSpec`: `eval_expression` returns, writes only its result within its
  caller's frame, and on a `WT` expression the result is not
  `Err(TypeError)`. **This is Cedar's type soundness**, for the compiled
  validator and evaluator; it is not proved here. Cedar's own soundness
  proof (in the Lean `cedar-spec`) is about its Lean model of the language,
  not this Rust code, and the compiled validator and evaluator (with the
  allocator in libSystem) are far beyond instruction-level symbolic
  execution.
* The precondition of `verdict`: an AAPCS64 call (16-byte aligned `SP`),
  valid inputs (`Valid`, which does not depend on the 256 bytes below `SP`)
  and an output object disjoint from `verdict`'s frame.

`Valid` and `WT` are universally quantified, so the result holds for any
meaning that makes the contracts true. The instructions of `verdict` are all
in hardware-validated classes (none of the pending FEAT_LRCPC2 ones).

`Code.lean` must be regenerated (`./build-m1.sh && ./extract-verdict.py`) if
the build changes; the proof then needs rechecking with `lake build`.

The validator checks policies, whose condition must be `Bool`, so an
expression `e` of any type is checked as the AST of
`permit(principal, action, resource) when { e == e };`, which typechecks exactly
when `e` does. It is built as an AST, so the input cannot escape it.

## Building

```sh
cargo test --release      # host tests, incl. 20,000 random expressions
./build-m1.sh             # -> target/aarch64-apple-darwin/release/libcedar_check.dylib
```

`build-m1.sh` cross-compiles from Linux with clang and `ld64.lld`, without a
macOS SDK: it links once allowing undefined symbols to learn the image's
imports, writes a `libSystem.tbd` stub listing exactly those, and relinks
against it. The dylib binds to the real `/usr/lib/libSystem.B.dylib` at
load time.
