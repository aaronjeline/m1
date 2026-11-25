# Pending hardware validation

Parts of the model that have **not yet been co-simulated on an M1**. Every
other instruction class was validated as described under
[Validation](README.md#validation). A proof whose code executes one of the
instructions below depends on the assumptions listed here until they are
validated.

When an entry is validated, record the run in the README's Validation section,
remove the `NOT YET VALIDATED` comment in `M1/Exec.lean`, and delete the entry.

## FEAT_LRCPC2: `LDAPUR*` / `STLUR*` (unscaled immediate)

**Added:** 2026-11-25. Rust's `aarch64-apple-darwin` target (CPU `apple-m1`)
emits these for atomic loads and stores at a nonzero field offset. The Cedar
target (`targets/cedar-check`) contains 37 of them: in the typechecker,
`OnceLock`, and the ip/decimal/datetime parsers, so they are on the path of
`cedar_check`. Before this, the model stopped at them as unsupported.

**What was added:**

| | |
| --- | --- |
| Encoding | `size 011001 opc 0 imm9 00 Rn Rt` (mask `0x3F200C00`, value `0x19000000`) |
| Instructions | `STLURB`, `STLURH`, `STLUR` (W, X); `LDAPURB`, `LDAPURH`, `LDAPUR` (W, X); `LDAPURSB`, `LDAPURSH` (to W or X), `LDAPURSW` |
| AST | `Instr.ldstOrderedImm size op offset rn rt` (`M1/Instr.lean`) |
| Decode | `M1/Decode.lean`, in `ldSt`. `(size, opc)` follows the single-register table (`intMemOp`), except that `size = 3, opc = 2` (`PRFM` there) is unallocated. `size = 2, 3` with `opc = 3` are unallocated, as in `intMemOp`. |
| Semantics | `M1/Exec.lean`: address `X[n]|SP + SignExtend(imm9)`, no writeback, then the same access as `LDUR*`/`STUR*` of that size and extension (`ldstOne`). Acquire/release ordering has no effect (single-threaded model). |

**Already checked (no hardware):** the decoder against LLVM's disassembler
(`llvm-mc`, `+rcpc-immo`) on 1,536 encodings covering every `size`, `opc`,
bit 21 and bits 11:10 value, with edge offsets and registers: 0 mismatches. All
156 words LLVM disassembles as `LDAPUR*`/`STLUR*` decode with the same size,
extension, offset and registers, and none of the other 1,380 words (unallocated
forms and neighbours such as MTE `LDG`/`STG`) decode. All existing proofs still
check.

**Assumptions to validate on the M1:**

1. **Implemented at EL0.** The M1 implements FEAT_LRCPC2, and the instructions
   execute at EL0 rather than raising `SIGILL`
   (`sysctl hw.optional.arm.FEAT_LRCPC2` should print `1`).
2. **Alignment (the main assumption).** As for `LDAPR`/`STLR` (FEAT_LSE2,
   measured), an access faults with `.dataAlignment` (`SIGBUS`) **exactly
   when** `[addr, addr + size)` crosses a 16-byte boundary, where `addr` is
   **base + offset**, not the base. Ordinary `LDUR`/`STUR` never fault on
   alignment, so this is where the model would be wrong if the M1 treats these
   as normal accesses for alignment.
3. **SP base.** With `Rn = SP`, the access faults with `.spAlignment` unless SP
   is 16-byte aligned, independent of the offset (as for every other SP-based
   access).
4. **Values.** The zero/sign extensions per form, the unscaled offset with the
   full signed 9-bit range, and `Rt = 31` read as XZR for stores and discarded
   for loads.
5. **Unallocated encodings** (`size = 3, opc = 2`; `size = 2, 3, opc = 3`) raise
   `SIGILL`, so they agree with the model as "both undefined".

**How to validate (on an M1 Mac):**

```sh
# 2: alignment. buf + 64 is 64-byte aligned, so addr % 16 = (off + imm) % 16.
# Expect FAULT exactly when (off + imm) % 16 + size > 16 (imm is the #offset in
# the label, size is 8/4/2/1 for x/w/h/b).
clang -O1 -o /tmp/align tools/cosim/align.c && /tmp/align | grep -E 'ldapur|stlur'

# 3: SP base. Expect `ldapur [sp]` to be ok for sp%16=0 and FAULT otherwise,
# matching `ldr [sp]`.
clang -O1 -o /tmp/spalign tools/cosim/spalign.c && /tmp/spalign

# 1, 4, 5 (and 2 at random alignments): random single-instruction cosim of
# just this class. Expect 0 mismatches. Unallocated forms should show up as
# "both undefined", and nothing as "unmodelled".
tools/cosim/run.sh 20000 1 gen_rcpc2

# Adding gen_rcpc2 changed the random stream of the default mix, so also rerun
# the full mix once.
tools/cosim/run.sh 20000 1
```

If (2) or (3) disagree, change the alignment check in the `ldstOrderedImm` case
of `M1/Exec.lean` (for example, drop `atomicAligned` if the M1 treats these as
ordinary accesses), then rerun the commands above.
