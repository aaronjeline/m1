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
