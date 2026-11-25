import Examples.Cedar.NoPanic.Spec

/-!
# Assumed contracts of the external functions (the allocator)

The functions reachable from `Evaluator::interpret` call the Rust allocator
shims `__rust_alloc`, `__rust_dealloc`, `__rust_realloc` and
`__rust_alloc_zeroed` (each a single `b` to `__rdl_*`, which calls the
system `malloc`/`free`/`posix_memalign`/`realloc`). These are **not proved**:
their contracts below are hypotheses (`Allocator`), stated in `NP` form so
that a caller's proof uses them with `SafeFun.call` like any proved contract.
(`__rust_no_alloc_shim_is_unstable_v2` is a single `ret`: its contract is
proved, `Fn/NoAllocShim`.)

**The heap.** Machine memory is a flat `BitVec 64 → BitVec 8`; the
allocator's bookkeeping lives somewhere in it. It is described by one
abstract predicate, `Heap.Live m a size align`: in memory `m`, `[a, a+size)`
is a live block allocated with layout `(size, align)`. What is assumed of it
(`MemFacts`, which also places the TLV descriptor off the stack):
* `frame`: the allocator's own data is neither on the stack nor inside a live
  block, so a change of memory confined to the stack and to live blocks keeps
  every block live;
* `aligned`: a live block is aligned as requested;
* `offStack`: a live block is off the stack `[lo, top)`;
* `offTlv`: a live block does not overlap the TLV descriptor (a static).

**What the allocator functions promise** (`Allocator`): the AAPCS64 and the
`NP` frame conditions (callee-saved registers, no stack byte above `SP`
changes, the TLV descriptor is unchanged), never reaching a panic sink, and:
* `alloc(size, align)` (valid layout, `size ≠ 0`) returns null or a new live
  block of that layout; every live block stays live with its contents;
* `alloc_zeroed`: the same, the new block's bytes are 0;
* `dealloc(ptr, size, align)` needs `ptr` live with that layout; every other
  live block stays live with its contents;
* `realloc(ptr, old, align, new)` needs `ptr` live with layout `(old, align)`,
  `new ≠ 0` and `(new, align)` valid; it returns null (and then changes no
  live block) or a live block of layout `(new, align)` holding the first
  `min old new` bytes of the old one (and every other live block stays live
  with its contents).

Allocation may fail (return null): Rust code checks, and the callers that
then call `handle_alloc_error` (a `Panic` sink) need the explicit assumption
that it does not. `Allocator` takes it as a parameter `Fails`: a null result
comes with a proof of `Fails`. Proofs are generic in `Fails`; a caller that
needs allocation to succeed instantiates `Fails := False`.
-/

namespace Examples.Cedar.NoPanic
open M1 Examples.Cedar.Eval

/-- `__rustc::__rust_alloc` -/
def rustAlloc : BitVec 64 := 0x2708c#64
/-- `__rustc::__rust_dealloc` -/
def rustDealloc : BitVec 64 := 0x27090#64
/-- `__rustc::__rust_realloc` -/
def rustRealloc : BitVec 64 := 0x27094#64
/-- `__rustc::__rust_alloc_zeroed` -/
def rustAllocZeroed : BitVec 64 := 0x27098#64

/-- A valid `core::alloc::Layout`: `align` a power of two and `size` rounded
up to `align` at most `isize::MAX`. -/
def ValidLayout (size align : BitVec 64) : Prop :=
  align ≠ 0#64 ∧ align &&& (align - 1#64) = 0#64 ∧ size.toNat + align.toNat ≤ 2 ^ 63

/-- An abstraction of the allocator's state. -/
structure Heap where
  /-- `Live m a size align`: in memory `m`, `[a, a + size)` is a live block
  allocated with layout `(size, align)`. -/
  Live : Memory → BitVec 64 → BitVec 64 → BitVec 64 → Prop

/-- From `s` to `s'`, every live block at an address satisfying `keep` stays
live, with its contents. -/
def HeapKept (H : Heap) (keep : BitVec 64 → Prop) (s s' : State) : Prop :=
  ∀ b n al, keep b → H.Live s.mem b n al →
    H.Live s'.mem b n al ∧ ∀ i < n.toNat, s'.mem (b + BitVec.ofNat 64 i) = s.mem (b + BitVec.ofNat 64 i)

/-- Assumed facts about the memory layout: the stack is `[lo, top)`; the heap
is described by `H`; the TLV descriptor (a static) is off the stack. -/
structure MemFacts (H : Heap) (lo top : BitVec 64) : Prop where
  /-- The allocator's own data is neither on the stack nor in a live block. -/
  frame : ∀ (m m' : Memory) a n al, H.Live m a n al →
    (∀ x, m' x ≠ m x → OnStack lo top x ∨ ∃ b nb alb, H.Live m b nb alb ∧ (x - b).toNat < nb.toNat) →
    H.Live m' a n al
  /-- A live block is aligned as requested. -/
  aligned : ∀ m a n al, H.Live m a n al → a &&& (al - 1#64) = 0#64
  /-- A live block is off the stack. -/
  offStack : ∀ m a n al, H.Live m a n al → ∀ i < n.toNat, ¬ OnStack lo top (a + BitVec.ofNat 64 i)
  /-- A live block does not overlap the TLV descriptor (a static). -/
  offTlv : ∀ m a n al, H.Live m a n al → Memory.Disjoint a n.toNat tlvDesc 8
  /-- The TLV descriptor is off the stack. -/
  tlvOffStack : ∀ i < 8, ¬ OnStack lo top (tlvDesc + BitVec.ofNat 64 i)
  /-- Distinct live blocks do not overlap. -/
  disjoint : ∀ m a n al b n' al', H.Live m a n al → H.Live m b n' al' → a ≠ b →
    Memory.Disjoint a n.toNat b n'.toNat

/-- **Assumed**: the contracts of the allocator shims. An allocation may fail
(return null) only if `Fails` holds: `Allocator H True p top` is the actual
allocator; `Allocator H False p top` is the explicit assumption that
allocation always succeeds. -/
structure Allocator (H : Heap) (Fails : Prop) (p : Program) (top : BitVec 64) : Prop where
  /-- `__rust_alloc(size = x0, align = x1) -> x0` -/
  alloc : NP p top rustAlloc (fun s => ValidLayout (s.gpr 0) (s.gpr 1) ∧ s.gpr 0 ≠ 0#64)
    (fun _ => 0#64) 0
    (fun s s' => ((s'.gpr 0 = 0#64 ∧ Fails) ∨ (s'.gpr 0 ≠ 0#64 ∧ H.Live s'.mem (s'.gpr 0) (s.gpr 0) (s.gpr 1))) ∧
      HeapKept H (fun _ => True) s s')
  /-- `__rust_alloc_zeroed(size = x0, align = x1) -> x0` -/
  allocZeroed : NP p top rustAllocZeroed (fun s => ValidLayout (s.gpr 0) (s.gpr 1) ∧ s.gpr 0 ≠ 0#64)
    (fun _ => 0#64) 0
    (fun s s' => ((s'.gpr 0 = 0#64 ∧ Fails) ∨ (s'.gpr 0 ≠ 0#64 ∧ H.Live s'.mem (s'.gpr 0) (s.gpr 0) (s.gpr 1) ∧
        ∀ i < (s.gpr 0).toNat, s'.mem (s'.gpr 0 + BitVec.ofNat 64 i) = 0#8)) ∧
      HeapKept H (fun _ => True) s s')
  /-- `__rust_dealloc(ptr = x0, size = x1, align = x2)` -/
  dealloc : NP p top rustDealloc (fun s => H.Live s.mem (s.gpr 0) (s.gpr 1) (s.gpr 2))
    (fun _ => 0#64) 0
    (fun s s' => HeapKept H (· ≠ s.gpr 0) s s')
  /-- `__rust_realloc(ptr = x0, old_size = x1, align = x2, new_size = x3) -> x0` -/
  realloc : NP p top rustRealloc
    (fun s => H.Live s.mem (s.gpr 0) (s.gpr 1) (s.gpr 2) ∧ s.gpr 3 ≠ 0#64 ∧
      ValidLayout (s.gpr 3) (s.gpr 2))
    (fun _ => 0#64) 0
    (fun s s' => (s'.gpr 0 = 0#64 ∧ Fails ∧ HeapKept H (fun _ => True) s s') ∨
      (s'.gpr 0 ≠ 0#64 ∧ H.Live s'.mem (s'.gpr 0) (s.gpr 3) (s.gpr 2) ∧
        (∀ i, i < (s.gpr 1).toNat → i < (s.gpr 3).toNat →
          s'.mem (s'.gpr 0 + BitVec.ofNat 64 i) = s.mem (s.gpr 0 + BitVec.ofNat 64 i)) ∧
        HeapKept H (· ≠ s.gpr 0) s s'))


/-!
# Assumed contracts of the C library functions

`memcpy`, `memmove`, `memset` and `memcmp` (libSystem, called through stubs)
are not proved either: their contracts (`LibC`) are hypotheses, in `NP` form.
They change no memory other than their destination and the free part of the
stack below their entry `SP` (their own frame); the destination must be
writable: in the callers' frames (above `SP`) or inside a live heap block.
`memcpy`'s ranges must not overlap. Lengths are byte counts (`x2`); the contracts are stated per length `len`
(the `Keeps` output size of `NPContract` is a constant).

The `pthread` functions used to find the stack's bounds (`stacker`) return
values and change nothing but their own frame. `pthread_self` returns the
current thread's handle `Self`; the others need it as argument.
-/

/-- `_memcpy` stub -/
def libcMemcpy : BitVec 64 := 0x355b2c#64
/-- `_memcmp` stub -/
def libcMemcmp : BitVec 64 := 0x355b38#64
/-- `_memmove` stub -/
def libcMemmove : BitVec 64 := 0x355b44#64
/-- `_memset` stub -/
def libcMemset : BitVec 64 := 0x355b50#64
/-- `_pthread_get_stacksize_np` stub -/
def libcStacksize : BitVec 64 := 0x355b5c#64
/-- `_pthread_self` stub -/
def libcSelf : BitVec 64 := 0x355b68#64
/-- `_pthread_get_stackaddr_np` stub -/
def libcStackaddr : BitVec 64 := 0x355b74#64

/-- `x` is in the free part of the stack, below `sp`. -/
def FreeStack (lo sp x : BitVec 64) : Prop := (x - lo).toNat < (sp - lo).toNat

/-- `n` bytes at `dst` may be written by a callee entered with `SP = sp`: in the
callers' frames, or inside a live heap block. -/
def Writable (H : Heap) (top sp : BitVec 64) (m : Memory) (dst : BitVec 64) (n : Nat) : Prop :=
  n = 0 ∨ (dst - sp).toNat + n ≤ (top - sp).toNat ∨
    ∃ b nb al, H.Live m b nb al ∧ (dst - b).toNat + n ≤ nb.toNat

/-- From `s` to `s'`, no byte changed except the `n` bytes at `dst` and the
free part of the stack below `s.sp`. -/
def OnlyWrites (lo : BitVec 64) (dst : BitVec 64) (n : Nat) (s s' : State) : Prop :=
  ∀ x, ¬ FreeStack lo s.sp x → n ≤ (x - dst).toNat → s'.mem x = s.mem x

/-- **Assumed**: the contracts of `memcpy`, `memmove`, `memset`, `memcmp` and
the `pthread` stack queries (`Self`: the current thread's handle). -/
structure LibC (H : Heap) (p : Program) (lo top : BitVec 64) (Self : BitVec 64) : Prop where
  /-- `memcpy(dst = x0, src = x1, n = x2) -> dst`: non-overlapping ranges. -/
  memcpy : ∀ len : Nat, NP p top libcMemcpy
    (fun s => (s.gpr 2).toNat = len ∧ Writable H top s.sp s.mem (s.gpr 0) len ∧
      (len = 0 ∨ Memory.Disjoint (s.gpr 0) len (s.gpr 1) len))
    (fun s => s.gpr 0) len
    (fun s s' => s'.gpr 0 = s.gpr 0 ∧ OnlyWrites lo (s.gpr 0) (s.gpr 2).toNat s s' ∧
      ∀ i < (s.gpr 2).toNat, s'.mem (s.gpr 0 + BitVec.ofNat 64 i) = s.mem (s.gpr 1 + BitVec.ofNat 64 i))
  /-- `memmove(dst = x0, src = x1, n = x2) -> dst`: the ranges may overlap. -/
  memmove : ∀ len : Nat, NP p top libcMemmove
    (fun s => (s.gpr 2).toNat = len ∧ Writable H top s.sp s.mem (s.gpr 0) len)
    (fun s => s.gpr 0) len
    (fun s s' => s'.gpr 0 = s.gpr 0 ∧ OnlyWrites lo (s.gpr 0) (s.gpr 2).toNat s s' ∧
      ∀ i < (s.gpr 2).toNat, s'.mem (s.gpr 0 + BitVec.ofNat 64 i) = s.mem (s.gpr 1 + BitVec.ofNat 64 i))
  /-- `memset(dst = x0, c = w1, n = x2) -> dst`. -/
  memset : ∀ len : Nat, NP p top libcMemset
    (fun s => (s.gpr 2).toNat = len ∧ Writable H top s.sp s.mem (s.gpr 0) len)
    (fun s => s.gpr 0) len
    (fun s s' => s'.gpr 0 = s.gpr 0 ∧ OnlyWrites lo (s.gpr 0) (s.gpr 2).toNat s s' ∧
      ∀ i < (s.gpr 2).toNat, s'.mem (s.gpr 0 + BitVec.ofNat 64 i) = (s.gpr 1).setWidth 8)
  /-- `memcmp(a = x0, b = x1, n = x2) -> w0`: 0 iff the ranges are equal; else
  negative iff at the first difference `a`'s byte is smaller (unsigned). -/
  memcmp : NP p top libcMemcmp (fun _ => True) (fun _ => 0#64) 0
    (fun s s' => OnlyWrites lo 0#64 0 s s' ∧
      ((s'.gpr 0).setWidth 32 = 0#32 ↔
        ∀ i < (s.gpr 2).toNat, s.mem (s.gpr 0 + BitVec.ofNat 64 i) = s.mem (s.gpr 1 + BitVec.ofNat 64 i)) ∧
      ∀ j < (s.gpr 2).toNat,
        (∀ i < j, s.mem (s.gpr 0 + BitVec.ofNat 64 i) = s.mem (s.gpr 1 + BitVec.ofNat 64 i)) →
        s.mem (s.gpr 0 + BitVec.ofNat 64 j) ≠ s.mem (s.gpr 1 + BitVec.ofNat 64 j) →
        (((s'.gpr 0).setWidth 32).slt 0#32 ↔ s.mem (s.gpr 0 + BitVec.ofNat 64 j) < s.mem (s.gpr 1 + BitVec.ofNat 64 j)))
  /-- `pthread_self() -> Self`. -/
  self : NP p top libcSelf (fun _ => True) (fun _ => 0#64) 0
    (fun s s' => s'.gpr 0 = Self ∧ OnlyWrites lo 0#64 0 s s')
  /-- `pthread_get_stackaddr_np(Self) -> x0` (some value). -/
  stackaddr : NP p top libcStackaddr (fun s => s.gpr 0 = Self) (fun _ => 0#64) 0
    (fun s s' => OnlyWrites lo 0#64 0 s s')
  /-- `pthread_get_stacksize_np(Self) -> x0` (some value). -/
  stacksize : NP p top libcStacksize (fun s => s.gpr 0 = Self) (fun _ => 0#64) 0
    (fun s s' => OnlyWrites lo 0#64 0 s s')

end Examples.Cedar.NoPanic
