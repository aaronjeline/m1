# m1: a formal model of the Apple M1 (AArch64, EL0) in Lean 4

`M1` is an executable semantics of the user-mode (EL0) AArch64 instruction set
as implemented by Apple M1-family cores running macOS. It is intended for
**verifying real machine code**: you compile C (or anything else) with clang,
extract the bytes from the Mach-O image, and prove theorems about what that
exact code does.

The model is validated against the hardware by co-simulation (see
[Validation](#validation)): random instructions are executed both on the M1 and
in the model, and every register, flag, vector register, memory byte and the
next PC are compared.

## Layout

| File | Contents |
| --- | --- |
| `M1/Bits.lean` | Bit-level helpers from the Arm ARM pseudocode: `AddWithCarry`, `ConditionHolds`, `DecodeBitMasks`, shifts, extends, CLZ/CLS, … |
| `M1/State.lean` | Machine state: `X0`–`X30`, `SP`, `PC`, `NZCV`, `V0`–`V31` (128-bit), byte-addressed little-endian memory, exclusive monitor, run status (`running`, `svc`, `brk`, `fault`). |
| `M1/Instr.lean` | Instruction AST. |
| `M1/Decode.lean` | `decode : BitVec 32 → Option Instr`, following the A64 encoding tables (Arm ARM C4.1). `none` = not modelled. |
| `M1/Exec.lean` | `exec : BitVec 32 → Instr → State → State`, the semantics of each instruction. |
| `M1/Step.lean` | `Program`, `step` (fetch, decode, execute) and `run`. |
| `M1/Spec.lean` | Program logic: `Reaches`, `FunSpec`, sequencing, branching and loop rules. |
| `M1/Crypto.lean` | AES, SHA-1/256/512 and carry-less multiply, following the Arm pseudocode. |
| `M1/FP.lean` | IEEE 754 half/single/double arithmetic following the Arm pseudocode (`FPRound`, `FPProcessNaNs`, `FPMulAdd`, …), correctly rounded by construction (exact rational result, one rounding). |
| `M1/FPLemmas.lean` | Condition codes after `FCMP` in terms of `cmpEQ`/`cmpGE`/`cmpGT`. |
| `M1/MemoryLemmas.lean` | Read-over-write lemmas for all access sizes, and disjointness of address ranges. |
| `M1/Sym.lean` | Symbolic execution: the `m1_step` tactic and its simp set and simprocs. |
| `M1/Tools/Cosim.lean` | Compares single-instruction hardware traces against the model (`m1 cosim`). |
| `M1/Tools/FunSim.lean` | Runs whole compiled functions in the model and compares with native runs (`m1 funsim`). |
| `tools/extract.py` | Compiles C and extracts machine code into a Lean module. |
| `tools/coverage.py` | Reports how much of a binary's code the decoder covers. |
| `tools/cosim/` | Single-instruction hardware co-simulation harness. |
| `tools/funsim/` | Whole-function co-simulation harness. |
| `Examples/` | Verified clang `-O2` output. |

## What is modelled

**Integer:** all of data processing (immediate and register): add/sub (with
shifted or extended register, carry, flags), logical, move wide, bitfield
(`UBFM`/`SBFM`/`BFM`, and so all shifts and extends), `EXTR`, conditional
select/compare, `CLZ`/`CLS`/`RBIT`/`REV*`, multiply, multiply-add, `SMULH`/`UMULH`,
widening multiplies, divide, variable shifts, `CRC32`/`CRC32C`, `ADR`/`ADRP`.

**Branches and system:** `B`, `BL`, `B.cond`, `CBZ`/`CBNZ`, `TBZ`/`TBNZ`, `BR`,
`BLR`, `RET`, `NOP` and hints, barriers,
`CLREX`, `SVC` and `BRK` (both stop the machine with a status that records the
immediate), `MRS`/`MSR` of `NZCV`, `FPCR` and `FPSR`.

**Loads and stores:** every integer addressing mode (unsigned offset, unscaled,
pre-/post-index, register offset with extend/shift, literal), pairs, sign- and
zero-extending loads, `PRFM` (no-op), exclusives (`LDXR`/`STXR`, acquire/release
forms), `LDAR`/`STLR` and friends, LSE atomics (`LDADD`, `LDCLR`, `LDEOR`,
`LDSET`, `LD{S,U}{MAX,MIN}`, `SWP`, `CAS`), and the FEAT_LRCPC2 unscaled
`LDAPUR*`/`STLUR*` (**not yet validated on hardware**: see
[VALIDATION.md](VALIDATION.md)).

**SIMD:** FP/SIMD register loads and stores (all sizes and modes), `LD1`–`LD4`
and `ST1`–`ST4` (multiple structures and single lane), `LD1R`–`LD4R`,
`MOVI`/`MVNI`/`ORR`/`BIC` (immediate), `FMOV` (to and from general registers),
`DUP`/`INS`/`UMOV`/`SMOV`, the integer three-same group (arithmetic, compares,
bitwise, min/max, pairwise, saturating, halving, shifts, `MLA`/`MLS`),
two-register miscellaneous (`CNT`, `REV*`, `CLZ`, `ABS`, `NEG`, compare against
zero, `XTN`, pairwise long adds), across-lanes reductions (`ADDV`, `UADDLV`,
`{S,U}{MAX,MIN}V`), permutes (`UZP`, `ZIP`, `TRN`), `EXT`, `TBL`/`TBX`, shifts by
immediate, vector and 64-bit scalar (`SHL`, `USHR`, `SSRA`, `SLI`, `SRI`,
rounding `S/URSHR`, `S/URSRA`, saturating `SQSHL`/`UQSHL`/`SQSHLU`), narrowing
shifts (`SHRN`, `RSHRN`, `SQ(R)SHR(U)N`, `UQ(R)SHRN`), widening (`SSHLL`,
`USHLL`, `SHLL`), saturating narrows (`SQXTN`, `UQXTN`, `SQXTUN`), saturating
and rounding register shifts (`S/U{Q}{R}SHL`), `SQDMULH`/`SQRDMULH`,
three-different ops (`SADDL`, `UADDW`, `SMLAL`, `UMULL`, `S/UABDL`, `S/UABAL`,
`ADDHN`/`RADDHN`/`SUBHN`/`RSUBHN`, `PMULL`/`PMULL2`, …), by-element integer
multiplies (`MUL`, `MLA`, `MLS`, `S/UMULL`, `S/UMLAL`, `S/UMLSL`,
`SQ(R)DMULH`, `SQDMULL`/`SQDMLAL`/`SQDMLSL`, `SQRDMLAH`/`SQRDMLSH`),
`SQABS`/`SQNEG`/`SUQADD`/`USQADD`, and `SDOT`/`UDOT`; and the scalar forms
of all of these.

**Cryptographic extensions:** `AESE`, `AESD`, `AESMC`, `AESIMC`, `SHA1C`/`P`/`M`/`H`,
`SHA1SU0`/`SU1`, `SHA256H`/`H2`/`SU0`/`SU1`, `SHA512H`/`H2`/`SU0`/`SU1`, `EOR3`,
`BCAX`, `RAX1`, `XAR` (`M1/Crypto.lean`, following the Arm pseudocode).

**Floating point** (half, single and double precision): `FADD`, `FSUB`, `FMUL`,
`FNMUL`, `FDIV`, `FSQRT`, `FMADD`/`FMSUB`/`FNMADD`/`FNMSUB` (fused), `FMAX`,
`FMIN`, `FMAXNM`, `FMINNM`, `FABS`, `FNEG`, `FMOV` (register and immediate),
`FCMP`/`FCMPE`, `FCCMP`, `FCSEL`, `FCVT` between all three formats,
`FRINT{N,P,M,Z,A,X,I}`, `FRINT32{Z,X}`/`FRINT64{Z,X}`, `SCVTF`/`UCVTF` and
`FCVT{N,P,M,Z,A}{S,U}` (to and from general registers, including fixed
point), `FJCVTZS`; and the
vector and scalar SIMD forms: lane-wise arithmetic, `FMLA`/`FMLS`, `FMULX`,
compares (`FCMEQ`, `FCMGE`, `FCMGT`, `FACGE`, `FACGT`, and against zero),
pairwise ops, `FABD`, by-element `FMLA`/`FMLS`/`FMUL`/`FMULX`, the estimate
and Newton-step instructions (`FRECPE`, `FRSQRTE`, `FRECPX`, `FRECPS`,
`FRSQRTS`, `URECPE`, `URSQRTE`), conversions and rounding (including fixed
point), `FCVTN`/`FCVTL`/`FCVTXN`,
`FMLAL`/`FMLSL{2}` (vector and by element), `FCMLA`/`FCADD`, and reductions
(`FMAXNMV`, `FADDP`, …). NaN propagation, signed zeros, subnormals, overflow
and saturation all follow the Arm pseudocode.

On a corpus of real libraries (zlib, lz4, liblzma, pcre2, libevent, gmp) the
decoder covers **99.98%** of instructions (the rest are `UDF`, which is
undefined), and libpng/libjpeg with their hand-written NEON **100%**. On
libcrypto and libsodium (hand-written AES/SHA/NEON assembly) it covers
99.73%; what remains is SVE code, which those libraries only select at run
time on CPUs that have it (the M1 does not: it is UNDEFINED there, and stuck
in the model), `UDF`, six reads of the cycle counter (`MRS CNTPCT_EL0`, whose
value the model does not predict) and one pointer-authenticated load. On corpora of auto-vectorised clang integer and floating-point
loops (`tools/corpus/`) it covers **100%**. Run `tools/coverage.py <image>...`
to measure your own binaries.

## Modelling decisions and assumptions

These are the places where the model makes a choice that a proof relies on.

* **Unmodelled means stuck.** An encoding that `decode` does not recognise sets
  the status to `fault (.unsupported w)` and the machine stops. A theorem whose
  postcondition requires `status = .running` therefore implies that no
  unmodelled instruction was executed. The model never silently guesses.
* **CONSTRAINED UNPREDICTABLE is stuck too.** Encodings the Arm ARM leaves
  CONSTRAINED UNPREDICTABLE (e.g. writeback loads whose base equals the
  destination) decode to `Instr.unpredictable` and stop the machine. This is a
  sound over-approximation: proofs never depend on which of the permitted
  behaviours the M1 picks.
* **Instructions are fetched from a separate `Program`**, not from data memory
  (a Harvard view). This is justified on macOS by W^X: code pages are not
  writable, so stores cannot change the instructions executed. Self-modifying
  and JIT code are out of scope.
* **Memory is a total function** `BitVec 64 → BitVec 8`. There is no model of
  unmapped pages, so a proof does not show that accesses are mapped; it shows
  what the code computes, given that they are. State this as a precondition
  where it matters.
* **Alignment, as measured on the M1:**
  * ordinary loads and stores may be unaligned;
  * SP alignment checking is on: any load or store whose base register is `SP`
    faults (`.spAlignment`) unless `SP` is 16-byte aligned. Arithmetic on `SP` is
    never checked;
  * exclusives, load-acquire/store-release, LSE atomics and `CAS` fault
    (`.dataAlignment`) exactly when the access crosses a 16-byte boundary
    (FEAT_LSE2). `LDAPUR*`/`STLUR*` are assumed to follow the same rule on
    base + offset; that has not been measured yet ([VALIDATION.md](VALIDATION.md));
  * a branch to a non-multiple of 4 faults (`.pcAlignment`).
* **The exclusive monitor is deterministic:** `STXR` succeeds exactly when the
  monitor holds the same address and size from a preceding `LDXR`. Real
  hardware may also fail spuriously; code that retries in a loop is verified
  under the deterministic model.
* **`x18` is reserved by macOS** and may be zeroed by the OS at any time.
  Clang never uses it; code that does is outside the guarantees of the model.
* **Floating-point control and status (`FPCR`, `FPSR`)** are architectural
  state, read and written by `MRS`/`MSR` with exactly the bits the M1
  implements (measured: `FPCR` `0x07FF9F00`, `FPSR` `0x0800009F`). Every
  `FPCR` setting is modelled:
  * rounding mode (`RMode`), flush-to-zero (`FZ`, `FZ16`), default NaN
    (`DN`) and the alternative half-precision format (`AHP`), following the
    Arm pseudocode (`FPUnpack`, `FPRoundBase`, `FPProcessNaN`, ...);
  * every instruction sets the cumulative exception flags it raises (`IOC`,
    `DZC`, `OFC`, `UFC`, `IXC`, `IDC`), and the saturating integer SIMD
    instructions set `QC`;
  * an exception whose trap is enabled (`IOE`, `DZE`, `OFE`, `UFE`, `IXE`,
    `IDE`) stops the machine with `.fpTrap`. The M1 implements these traps
    (macOS delivers them as `SIGILL`).

  The plain operations in `M1.FP` (`FP.add`, `FP.mulAdd`, ...) are the
  default-mode ones; proofs about FP code take `FPDefault s` (no modes, no
  traps: how macOS starts every thread) as a precondition, under which
  symbolic execution produces exactly those operations. `CalleeSaved`
  includes `FPCR`, as AAPCS64 requires.
* **Single-threaded:** no other agent writes memory. Atomics are given their
  sequential semantics.

## Verifying a program

1. **Extract the code.**

   ```sh
   tools/extract.py Examples/C/basic.c --module Examples.Basic \
       --out Examples/Basic/Code.lean --cflags="-O2"
   ```

   This links the C file into a dylib (so calls and PC-relative references are
   resolved) and generates a module with `prog : Program` (the `__TEXT,__text`
   words annotated with their disassembly), `sym_<name>` for each function,
   the initialised data sections, and `DataLoaded s` (they are in memory). An
   existing Mach-O image can be given instead of a C file.

2. **State a specification** with `FunSpec prog sym_f pre post`: started at
   `sym_f` in a running state satisfying `pre`, the code returns to the
   address in the initial `x30`, still running, in a state related to the
   initial one by `post`.

3. **Prove it** by symbolic execution. `m1_step` executes one instruction
   (fetch, decode and semantics are all evaluated by simprocs whose results
   are checked by the kernel); `Reaches.ite` splits on a conditional branch;
   `Reaches.loop` takes a loop invariant and a decreasing measure;
   `Reaches.trans` composes, for example with the `FunSpec` of a callee.

   ```lean
   theorem max_correct : FunSpec prog sym_max (fun _ => True)
       (fun s s' => s'.gpr 0 = if (s.gpr 1).slt (s.gpr 0) then s.gpr 0 else s.gpr 1) := by
     intro s hpc hst _
     simp only [sym_max] at hpc
     m1_step; m1_step; m1_step
     exact Reaches.done (by simp)
   ```

4. **Calls to external functions** (libc and other dylibs) go through
   `__stubs`, whose targets are bound by `dyld` at load time, so their code is
   not in `prog`. `extract.py` names each stub entry `ext_<name>`. State the
   theorem for **every program `p` extending `prog`**
   (`p.Extends prog`), with the callee's contract as a hypothesis
   `FunSpec p ext_<name> pre post`. This is sound and non-vacuous: it says the
   code is correct when loaded with any library that meets the contract.
   `m1_step` fetches from `prog` automatically when there is an `Extends`
   hypothesis. `CalleeSaved s s'` (AAPCS64 callee-saved registers and `FPCR`) and
   `FramePreserved n s s'` (the caller's frame is untouched) are available for
   writing contracts, and `FramePreserved.read64` reloads saved registers
   after a call.

   ```lean
   def RandSpec (p : Program) : Prop :=
     FunSpec p ext_rand (fun _ => True) fun s s' =>
       ((s'.gpr 0).setWidth 32).msb = false ∧ CalleeSaved s s' ∧ FramePreserved 16 s s'

   theorem roll_correct (p : Program) (hp : p.Extends prog) (hrand : RandSpec p) :
       FunSpec p sym_roll (fun s => s.sp &&& 15#64 = 0#64) fun s s' =>
         (1 ≤ ((s'.gpr 0).setWidth 32).toNat ∧ ((s'.gpr 0).setWidth 32).toNat ≤ 6) ∧
         CalleeSaved s s'
   ```

   See `Examples/Basic/Proofs.lean` (a loop computing `gcd`, and a loop
   summing an array from memory), `Examples/Calls/Proofs.lean` (a function
   with a stack frame calling another function twice, verified modularly
   against the callee's spec, including callee-saved registers) and
   `Examples/FP/Proofs.lean` (floating point: a polynomial whose spec shows
   that clang contracted it into fused multiply-adds, a NaN-aware clamp, and
   a saturating `double` to `long` conversion) and `Examples/Ext/Proofs.lean`
   (`rand() % 6 + 1` against libc's `rand` contract, including clang's
   multiply-high replacement of `% 6`, and preservation of callee-saved
   registers).

   Tips:
   * Always step from a concrete PC. Stepping from a symbolic PC (for example
     right after `ret`) cannot make progress.
   * Stack and other memory accesses are resolved by the read-over-write
     lemmas in `M1/MemoryLemmas.lean`; disjointness of `base + c₁` and
     `base + c₂` for literal offsets is discharged automatically.
   * Results come out as `upd` chains; `simp [upd]` turns them into the values.
   * A scalar FP register's value is `fpArg (s.vreg r) N` (the `N`-bit
     encoding, a `Nat`); comparisons followed by `B.cond`/`FCSEL` are
     rewritten to `FP.cmpEQ`/`cmpGE`/`cmpGT`.

## Validation

`tools/cosim/run.sh N SEED` generates `N` random instructions across all
modelled classes (and many unmodelled ones), runs each on this machine's CPU
in a harness that captures the full register file, flags, vector registers,
a 16 KiB guarded memory buffer and the next PC (or the signal raised), then
runs `step` in the model from the same initial state and compares everything.

Each test is classified as: agree; both undefined (the model does not decode
it and the CPU raises `SIGILL`); unpredictable (stuck in the model, as above);
unmodelled (the CPU executes it but the model does not decode it; reported
for coverage); hardware memory fault (the generated address left the buffer);
or **mismatch**. The run fails if there is any mismatch.

At the time of writing, more than 490,000 random single-instruction tests
(including about 290,000 floating-point, SIMD and crypto tests) have been run
on an M1 Max with **zero mismatches**. Every issue the harness found during
development was fixed in the model: LSE2 alignment, SP alignment checking,
`x18` clobbering, decoding of unprivileged `PRFM`, the field layout of SIMD
structure loads, and `FCMP #0.0` ignoring its `Rm` field.

Instructions added since the last hardware run are listed, with what to
check, in [VALIDATION.md](VALIDATION.md).

Run it again after changing the model (optionally restricted to some
generators, e.g. `gen_fp,gen_fpvec,gen_fpmore,gen_crypto`):

```sh
tools/cosim/run.sh 20000 1
```

**Whole functions.** `tools/funsim/run.py` compiles C files into a dylib and
calls its functions natively with random arguments (pointers to
pseudo-random buffers, counts, integers, doubles and floats, including NaNs,
infinities and subnormals). It then runs the same machine code with `run` in
the model, starting from the same registers and memory, until the function
returns. It compares `x0`, `x1`, `q0`, `q1` and every byte of every buffer.
On the corpora in `tools/corpus/` (loops, string functions, sorting, hashing,
switch tables, auto-vectorised integer and floating-point code), compiled at
`-O1`, `-O2`, `-O3 -mcpu=apple-m1` and `-Os`, **9,132 calls agree, with no
mismatch** (2,283 per optimisation level; earlier runs including the
examples' C sources added 2,513 more).
Functions that call into libSystem (clang turns some loops into
`memset`/`strlen` calls) stop with a fetch fault at the stub, as they should.

```sh
tools/funsim/run.py -n 30 tools/corpus/loops.c tools/corpus/fp.c
```

## Building

Lean 4 (see `lean-toolchain`); no dependencies.

```sh
lake build          # model, examples (all proofs checked) and the `m1` tool
```
