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
| `<RawVecInner>::finish_grow` (generic instance) | `0x21d0fc` | `Fn/FinishGrow2` | `NP`; pre: `Room 0x30`, result in the callers' frames, `align` a power of two, `Old` (if `old_cap ≠ 0`, the old block `(elem*old_cap, align)` is live and `elem*new_cap ≠ 0`); post: `Ok = [0, ptr≠0, elem*new_cap]` (ptr live with that layout, holding the old bytes after `realloc`) or `Err = [1, ..]` only if `elem*new_cap + align > 2^63` (incl. `umulh` overflow) or `Fails`; other live blocks kept |
| `<Arc<SourceTextInner>>::drop_slow` | `0x1259c8` | `Fn/ArcSourceTextDropSlow` | `NP`, out none; pre: `Room 0x20`, `x0 → ptr` outside the free stack, `ArcInner` live `(0x28, 8)`, the `String` buffer live `(cap, 1)` if `cap ≠ 0` and distinct; post: every live block other than `ptr` and the buffer kept (with contents) |
| `<Arc<Vec<PatternElem>>>::drop_slow` | `0x124fec` | `Fn/ArcPatternDropSlow` | the same, buffer layout `(4*cap, 4)` |
| `<Arc<dyn InternalExtensionValue>>::drop_slow` | `0x124d4c` | `Fn/ArcDynDropSlow` | `NP`, out none; the `blr` to the vtable's drop fn is covered by an **assumed** `DropFn` contract (a hypothesis of `np`, see below); pre: `Room (0x30 + Fd)`, `(ptr, vt)` and the vtable outside the free stack, `align` a power of two, `ArcInner` live with its layout (`arcSize`, `arcAlign`), not owned by the value, disjoint from the vtable, `DPre`; post: blocks not owned by the value and `≠ ptr` kept |
| `<Storage<Cell<Option<usize>>>>::get_or_init_slow<STACK_LIMIT>` | `0x287dec` | `Fn/StackLimitInit` | `NP`, out `x0` (17 bytes); pre: `Room 0x20`, the storage off the stack and off the TLV descriptor; post: `x0` returned, `OnlyWrites` the storage (and the free stack). Uses the assumed `pthread_*` contracts |
| `core::slice::memchr::memchr_aligned` | `0x34fae0` | `Fn/MemchrAligned` | `NP`, no pre, post `True` (frameless leaf, no stores, 3 loops): `leaf_np` |
| `<SmolStr as PartialOrd>::partial_cmp` | `0x28ef60` | `Fn/SmolStrPartialCmp` | `NP`, pre `Room 0x20`, post `OnlyWrites` nothing (read-only; calls `memcmp`); shrink-wrapped frame: `leaf_to` up to the prologue |
| `<Type as PartialOrd>::lt` (`call_mut`), 4 instances | `0xe0cc0`, `0x23d694`, `0x287054`, `0x22702c` | `Fn/TypeLt`, `TypeLt2..4` | `NP`, pre `Room (0x40 + 0x20)`, read-only (`OnlyWrites` nothing); calls `partial_cmp` in loops: `body_loop` (`TypeLt2..4` generated) |
| `<Literal as PartialOrd>::partial_cmp`, 2 instances | `0xe084c`, `0x284ea4` | `Fn/LiteralPartialCmp`, `..2` | the same (`Room (0x50 + 0x20)`; tail calls to `partial_cmp`), generated |
| `<InternalName as Ord>::cmp`, 2 instances | `0x9a7d4`, `0x23c2e4` | `Fn/InternalNameCmp`, `..2` | the same (`memcmp`), generated |

The read-only contracts (the last four rows) say nothing about the result:
they suffice for callers whose panic sites do not depend on it.

All `NP` contracts are stated for any `p` with `p.Extends prog` (and
`p.Extends Callee.prog` for proved callees), with the external contracts
(`Allocator H Fails p top`) and the memory-layout facts (`MemFacts H lo top`) as
hypotheses. Each module with callees checks that the extracted `ext_i` are the
addresses the contracts are about (`ext_eqs`, `ext_0_eq`, by `rfl`).

Rough time per function (including building the shared infrastructure the
first time it was needed): sqrt_approx 15 min, the outlined functions and the
shim 5 min each, drop_slow 30 min, finish_grow 90 min.

**Time log (second round, with the new infrastructure; wall clock, including
the infrastructure each function first needed):**

| function | time | proof lines | notes |
|---|---|---|---|
| `Frame.lean` (frame invariant, lemmas, tactics) + `M1/SafeRun.lean` (`m1_run`) | ~60 min | — | first version, debugged on the next one |
| `ArcSourceTextDropSlow` | ~35 min | 109 | first user of `frame_enter`/`frame_upd`/`frame_epi`/`frame_tail` |
| `FinishGrow2` (`0x21d0fc`) | ~35 min | 276 | vs. 503 for `FinishGrow` (the simpler align-1 instance); +`umulh_eq_zero`, `mem_range`, `HeapKept.of_out` |
| `ArcPatternDropSlow` | ~8 min | 112 | copy of the above; +`lsl`/`lsr` (`UBFM`) simp lemmas |
| `ArcDynDropSlow` (`blr`) | ~25 min | 167 | +`DropFn` assumption, `Outside.sub`, `Frame.callRoom` |
| `StackLimitInit` | ~20 min | 117 | +`LibC` pthread contracts, `SafeN.withEntry`, `NPPost.rebase`, `frame_call` |
| `MemchrAligned` | ~15 min | 24 (2-line proof) | +`leaf_np`, `leaf_auto`, `split_ors`, `pcs` in `extract-fn.py` |
| `SmolStrPartialCmp` | ~15 min | 80 | +`leaf_to` (frameless code before a shrink-wrapped prologue) |
| `TypeLt` | ~45 min | 51 (8-line proof) | +`body_loop`, `body_case`, `BodyInv` |
| `TypeLt2..4`, `LiteralPartialCmp{,2}`, `InternalNameCmp{,2}` | ~2 min each | 45 each (generated) | `gen-ro-proof.py`; +tail-call case in `body_case`; checking takes 55–80 s each |


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
* `MemFacts.disjoint` (new): distinct live blocks do not overlap (needed to
  show that a store into one block keeps the others' contents).
* `LibC H p lo top Self` (new; `NP` contracts, stated per length `len` since
  `NPContract`'s output size is a constant):
  * `memcpy(dst, src, len)`: `dst` `Writable` (in the callers' frames or inside
    a live block), ranges disjoint; returns `dst`; `OnlyWrites` `dst` (and the
    free stack below its `SP`); `dst[i] = src[i]`;
  * `memmove`: the same without disjointness;
  * `memset(dst, c, len)`: `dst[i] = c`;
  * `memcmp(a, b, n)`: no pre; writes nothing; `w0 = 0` iff equal, else its
    sign is that of the first differing (unsigned) byte pair;
  * `pthread_self() = Self`; `pthread_get_stackaddr_np(Self)`,
    `pthread_get_stacksize_np(Self)`: some value, write nothing.
* `ArcDynDropSlow.DropFn` (an assumption the *caller* of `<Arc<dyn ..>>::drop_slow`
  discharges for the concrete vtable, not a global axiom): the vtable's drop
  function has an `NP` contract with precondition `DPre` (depending only on
  memory off the stack) and stack room `Fd`, and keeps every live block the
  value does not own (`Own`) and the vtable's 24 bytes.
* Not yet stated: `_Unwind_Resume`, `free`/`malloc`/`posix_memalign`, the
  dispatch functions, `CCRandomGenerateBytes`, `__tlv_atexit`, `abort`
  (see `INVENTORY.md`, "Externals called").

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

**Second round** (generic frame + block stepping):

* `M1/SafeRun.lean` (not imported by `M1.lean`, to avoid rebuilding every
  `Code.lean`; imported by `Frame.lean`): `m1_run [until a b ..]` steps a
  `SafeN` goal through a basic block: it stops after a conditional branch (the
  state is an `if`), `bl`/`blr`, `ret`/`br`, `svc`/`brk`, when the PC leaves the
  code it started in (a tail call; another `Extends` hypothesis's code, e.g.
  a callee's, is never entered), or at a stop address. `m1_run1` uses up one
  index unit first (`SafeFun.fix`). `m1_ite h` splits on the `if`.
  `split_ors h` splits a disjunction chain into goals.
* `Frame.lean`: the generic frame invariant `Frame L lo top out n s0 s` for a
  `Layout` (size, `(register, slot)` list, optional `d8`–`d15` slots), with
  `Frame.intro`/`Entered.intro`, `Frame.update`, `Frame.call`,
  `Frame.callRoom`, `Frame.ret(_np)`, `Frame.ret_goal` + `tail_np`, writable
  bytes `Frame.W` (locals, declared output, heap); the tactics `frame_enter`,
  `frame_upd`, `frame_update`, `frame_mem`, `mem_range`, `frame_call`,
  `frame_epi`, `frame_ret`, `frame_tail`, `frame_regs`, `frame_simp`; the
  whole-function invariants `leaf_np`/`leaf_to` + `leaf_auto` (frameless,
  store-free) and `body_loop` + `body_case` (`BodyInv`: frame + no stores but
  in the free stack; calls to read-only callees, `ret` and tail calls);
  heap lemmas (`HeapKept.of_block`, `.write64`, `.of_out`, `Outside`),
  `OnlyWrites` ↔ `MemW`; `lsl`/`lsr` simp lemmas, `umulh_eq_zero`,
  `atomic8_ok`; the flags of `cmn`/`ands` are in `m1_sym`.
* `targets/cedar-check/extract-fn.py`: symbol aliases (several names at one
  address); calls through stubs (`<dyld_stub_binder+0x..>`) are recorded as
  externals (names from `inventory.json`); emits `pcs` (the instruction
  addresses).
* `targets/cedar-check/gen-ro-proof.py`: generates the whole proof of a
  read-only function with a standard frame from its `Code.lean` (layout and
  body read off the prologue/epilogues).

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

**Lessons from the second round.**
* A function with a frame is now: `frame_enter` (prologue), facts about the
  arguments in terms of the entry state (`E.args`, `E.read64` with an
  `Outside` precondition for pointer arguments), `generalize` the loaded
  values, then `m1_run` / `m1_ite` per block, `frame_upd`+`frame_mem` before
  a join or epilogue, `frame_call` (or `SafeFun.call` + `Frame.call`) per call,
  `frame_epi` / `frame_tail` at the end; shared tails as `have tail : ∀ s2, ..`.
* Keep the frame facts in literal form (`hsp : s1.sp = s.sp + 0xffe0#64`, by
  `frame_simp L at`), so the stepping simp sees the same terms as `frame_simp`
  produces from the layout.
* Never let a `by` block inside a `refine` term decide a state metavariable
  (`rfl` on records, `frame_update` inside `(by ..)`): use `?_` holes and solve
  them afterwards; `trivial` on `Room ..` (a decidable-looking `≤` on
  `toNat`) and `rfl` between distinct `BitVec` literals blow the recursion
  limit, which `first` does not catch.
* A hand-written `s.gpr 0` is `OfNat`: `simp only [BitVec.ofNat_eq_ofNat] at *`
  right after `rintro` (the generalized names then match the stepped terms).
* `ldaddl` checks 16-byte non-crossing: have `atomic8_ok (hM.aligned ..)` in
  context before stepping it.
* The heap: `MemFacts.frame` + `MemFacts.disjoint` give `HeapKept` across a
  store into one block (`HeapKept.write64`); stack-only changes keep it
  (`StackOnly.heapKept`, `HeapKept.of_out`).
* Read-only functions need no loop invariants: `leaf_np` / `body_loop` check
  one step from every PC with an invariant that ignores data registers. Their
  cost is checking time (~0.7 s per instruction; 55–80 s for 110–143
  instructions): `body_case` re-simplifies the whole step for every
  instruction.

**What will be hard next.** Callers with panic sites (`unwrap` on `None`,
`handle_error` on `Err`, index checks) need functional invariants of Rust
objects (`Vec`, `Arc`, `BTreeMap` nodes, `SmolStr`) as abstract predicates
with `Framed`-style footprints, as in `Eval/Contracts.lean`; the heap part
(`Live`, `HeapKept`) is a start. Recursive SCCs use `SafeFun.fix` with
`m1_safe_step1` (or `m1_run1`) for the first instruction.

The next bottleneck (after round two): every remaining function that is not
read-only drops, clones or builds Rust objects (`drop_glue<..>`, the
`Arc<..>::drop_slow` of containers, `clone`, `BTreeMap` insert/iterators).
Their preconditions need **ownership predicates with reference counts**: e.g.
`<Arc<Vec<Id>>>::drop_slow` loops over `SmolStr`s whose heap variant is an
`Arc<str>` that other `SmolStr`s may share (strong count ≥ the number of
owners); a loop invariant must say which elements remain owned, and the
`Arc<str>` drop must keep the other elements' blocks (separation per owner).
`Live` + `HeapKept` + `disjoint` is the base; an abstract `Owns m a T`
family with framing lemmas (as `Framed` in `Eval/Contracts.lean`) and an
`ArcRef` predicate with counts are the next infrastructure. Callers with panic
sites (`unwrap` on a `get`, `handle_error` after `finish_grow`) also need
functional postconditions of the read-only functions proved so far.
