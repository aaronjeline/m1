# No-panic proofs: ledger

The pilot of the per-function pipeline (see `Spec.lean` for the contract shape
`NP`, `INVENTORY.md` for the functions). Everything listed under "Proved"
builds with no `sorry` (`lake build Examples`); the proofs use the standard
axioms plus `bv_decide`'s native-decide axioms (as the rest of the repo does).

## Proved

| function | address | module | contract |
|---|---|---|---|
| `core::slice::sort::stable::drift::sqrt_approx` | `0x3503d8` | `Fn/SqrtApprox` | `NP`, no precondition, writes nothing; `x0' = sqrtApprox x0` (the Rust formula, `ilog2 = 63 - clz`) |
| `_OUTLINED_FUNCTION_0` | `0xe1300` | `Fn/Outlined0` | not AAPCS (writes its caller's frame through the caller's `SP`/`x29`): `SafeSpec` with the exact final state (`x8 := sp+8`, `[sp+0x18] := x29-1`, `[x29-0x10] := sp+8`); pre: `SP` 16-aligned |
| `_OUTLINED_FUNCTION_2` | `0xe1320` | `Fn/Outlined2` | not AAPCS (a shared epilogue tail, entered by `b`): `SafeSpec` with the exact final state (`sp += 0x40`, `pc := x30`) |
| `__rust_no_alloc_shim_is_unstable_v2` | `0x2709c` | `Fn/NoAllocShim` | `NP`, a single `ret`: final state = entry state with `pc := x30` |
| `<Arc<str>>::drop_slow` (regex_automata instance) | `0x2be708` | `Fn/ArcStrDropSlow` | `NP`; pre: `x0 → (ptr, len)`, unless `ptr = usize::MAX` the `ArcInner<str>` is `Live` with layout `((len+0x17)&!7, 8)` and `len ≤ isize::MAX`; may change only the weak count (`out = ptr+8`, 8 bytes); every other live block stays live. Tail-calls `__rust_dealloc` |
| `<RawVecInner>::finish_grow` (alloc instance, align 1) | `0x348eac` | `Fn/FinishGrow` | `NP`; pre `Room` (stack has 0x20 bytes for the frame; the 24-byte result at `x0` is in the caller's part of the stack) and `Old` (if `old_size ≠ 0`, the old block is `Live` and `new_size ≠ 0`); post `Post`: `Ok` = `[0, ptr≠0, new_size]` with `ptr` live of the new size and (after `realloc`) holding the old bytes, or `Err` = `[1, ..]` only if `new_size > isize::MAX` or `Fails`; every live block other than the old one stays live with its contents |

All `NP` contracts are stated for any `p` with `p.Extends prog` (and
`p.Extends Callee.prog` for proved callees), with the external contracts
(`Allocator H Fails p top`) and the memory-layout facts (`MemFacts H lo top`) as
hypotheses. Each module with callees checks that the extracted `ext_i` are the
addresses the contracts are about (`ext_eqs`, `ext_0_eq`, by `rfl`).

Rough time per function (including building the shared infrastructure the
first time it was needed): sqrt_approx 15 min, the outlined functions and the
shim 5 min each, drop_slow 30 min, finish_grow 90 min.

## Assumed (`Externals.lean`)

* `Heap`: one abstract predicate `Live m a size align` (in memory `m`,
  `[a, a+size)` is a live allocation with that layout).
* `MemFacts H lo top` (the stack is `[lo, top)`):
  * `frame`: changes confined to the stack and to live blocks keep every block
    live (the allocator's metadata is in neither);
  * `aligned`: a live block is aligned as requested;
  * `offStack`: a live block is off the stack;
  * `offTlv`: a live block does not overlap the TLV descriptor;
  * `tlvOffStack`: the TLV descriptor is off the stack.
* `Allocator H Fails p top`: `NP` contracts (AAPCS, callee-saved registers, no
  stack byte above `SP` changes, TLV descriptor unchanged, never reaches a
  `Panic` sink) of
  * `__rust_alloc(size, align)` (valid layout, `size ≠ 0`): null (only if
    `Fails`) or a non-null new live block; every live block stays live with
    its contents;
  * `__rust_alloc_zeroed`: the same, the new bytes are 0;
  * `__rust_dealloc(ptr, size, align)`: needs `Live ptr size align`; every
    other live block stays live with its contents;
  * `__rust_realloc(ptr, old, align, new)`: needs `Live ptr old align`,
    `new ≠ 0`, `(new, align)` valid; null (only if `Fails`; nothing changes) or
    a non-null live block of the new layout holding the first `min old new`
    old bytes, every other block kept.
* **Allocation success** is the parameter `Fails`: `Allocator H True p top` is
  the honest allocator, `Allocator H False p top` is the explicit assumption
  that allocation never fails. All proofs so far are generic in `Fails`;
  callers that reach `handle_alloc_error`/`handle_error` on failure will need
  `Fails := False` (and, for `handle_error` after `finish_grow`, that
  capacities stay below `isize::MAX`).
* Not yet stated: `memcpy`/`memmove`/`memcmp`/`memset`, `_Unwind_Resume`, the
  dispatch/pthread functions (see `INVENTORY.md`, "Externals called").

## Infrastructure added

* `M1/Sym.lean`:
  * `m1_rw_extends` (used by `m1_step`, `m1_safe_step`, `m1_safe_step1`):
    fetches through whichever `p.Extends q` hypothesis has code at the PC;
  * fixed `m1_safe_step`/`m1_safe_step1`: the `¬ B s.pc` side condition was
    left as `¬(False ∨ … ∨ False)` (the simp set had no `or_false`); now
    discharged by the new `m1_safe_bad`;
  * `atomicCompute` is unfolded by `m1_sym` (LSE atomics, e.g. `ldaddl` in
    every `Arc` drop);
  * `extendReg_{uxtx,sxtx,uxtw,sxtw}` (`m1_sym`): register-offset addressing
    `[xn, xm]`, `[xn, wm, uxtw]` used to leave `extendReg …` unreduced.
* `M1/State.lean`: `upd_upd_same` (simp).
* `targets/cedar-check/extract-fn.py`: accepts an address instead of a symbol
  suffix (outlined function names are not unique; the symbol table is now a
  list, so the end of a function is right even when names repeat); records
  tail calls (`b` to another symbol) as callees.
* `Lemmas.lean`: flags after `cmn`/`ands` (`cond_eq_cmn`, `cond_eq_logic64`,
  …), `Keeps` composition, `write64_keep`/`write64_changed`,
  `Memory.Disjoint.sub`, `StackOnly` (changes confined to the stack: keeps the
  TLV descriptor and the heap), `onStack_above`/`onStack_below`,
  `HeapKept.trans/mono`, `live_write64`.

## Lessons (how to prove the next ~265)

**Shape of a proof.**
* Leaf functions with no stack frame: `rintro n s hpc hst ⟨hal, hpre⟩`,
  `simp only [sym_fn] at hpc`, one `m1_safe_step` per instruction, branches
  by `rw [cond_…]` + `refine SafeN.ite (fun hc => ?_) (fun hc => ?_)`, then
  `SafeN.done ⟨rfl, rfl, ⟨?_, rfl, fun _ _ _ => rfl, rfl⟩, Keeps…, …⟩`.
  Callee-saved registers after `upd` chains:
  `intro r h1 h2; simp (disch := bv_omega) only [upd_other]`.
* Functions with a frame (`FinishGrow` is the template):
  1. cut after the prologue with `refine SafeN.trans (Q := fun s1 => s1.pc = … ∧
     s1.status = .running ∧ Inv s s1 ∧ …) ?_ ?_`: the rest of the proof works on
     an opaque `s1` with a few hypotheses instead of a growing record;
  2. `Inv` (frame invariant: `SP`, saved slots, callee-saved registers, `Keeps`
     of the caller's frame, TLV, `HeapKept`) with three lemmas: `Inv.call`
     (after a callee's `NP` contract), `Inv.of_mem` (after stores into the
     declared output), `epilogue`;
  3. shared tails as lemmas (`ok_tail`, `err_tail`) concluding
     `Fin ∧ s'.mem = <the stores>`, combined per path with `SafeN.mono`.
  Most of `Inv`/`Inv.call`/`Inv.of_mem`/`epilogue` is the same for every
  function up to the list of saved registers and the frame size: **the next
  step should be a generic `Frame` invariant parameterized by
  `(frame size, [(offset, register)])` with generic `call`/`store`/`epilogue`
  lemmas** (or a generator emitting them per function).
* Calls: `refine SafeFun.call (A.alloc n) rfl rfl ⟨align, pre⟩ ?_`, then
  `rintro s2 h2pc h2st ⟨hcs, hk, htl, hpost⟩` and
  `simp only [upd, BitVec.reduceEq, ite_true, ite_false] at h2pc hpost`.
  Alignment at the call: `show (s.sp + c) &&& 15#64 = 0#64; rw [add_and15 _ _ (by decide), hal]`.
  Exact-state contracts (outlined helpers, the shim): `rintro _ - - ⟨-, -, -, rfl⟩`
  substitutes the state and stepping continues on the record.

**Pitfalls (each cost time).**
* `m1_step`/`m1_safe_step` used to fetch with `step_of_extends (by assumption)`:
  with two `p.Extends _` hypotheses in context it picked the last one and
  failed with "simp made no progress". Fixed: the new `m1_rw_extends` tries
  each `Extends` hypothesis (`FinishGrow` keeps both its own and the shim's).
* Literals: after a step, register indices are `BitVec.ofNat` (`s.gpr 0#5`);
  hand-written statements elaborate `s.gpr 0` as `OfNat`. They are different
  terms for `rw`/`omega`. Normalize with `simp only [BitVec.ofNat_eq_ofNat] at …`
  (unfold your own defs such as `Post` first, or the goal keeps `OfNat`).
* `rfl` for `record.sp = s1.sp` when the step rewrote the field to `s.sp + c`
  hits "maximum recursion depth": pass the hypothesis (`h1sp.symm`).
* Terms mentioning the current record must be elaborated after it is known:
  `refine (lemma … ?_ …).mono ?_` then `· exact …`, and give implicit
  arguments that occur only in the conclusion by name (`(H := H)`).
* `grind` on goals with 64-bit literals (`0xffffffffffffffe0#64`) exhausted
  memory; prove generic identities (`x + c + j - x = c + j`) with `grind` and
  `rw` with them. `bv_omega` on 4-variable identities was also very slow.
* `rintro` patterns with `-` clear the component (it is gone for
  `contradiction`).

**What will be hard next.** Callers with panic sites (`unwrap` on `None`,
`handle_error` on `Err`, index checks) need functional invariants of Rust
objects (`Vec`, `Arc`, `BTreeMap` nodes, `SmolStr`) as abstract predicates
with `Framed`-style footprints, as in `Eval/Contracts.lean`; the heap part
(`Live`, `HeapKept`) is a start. Recursive SCCs use `SafeFun.fix` with
`m1_safe_step1` for the first instruction.
