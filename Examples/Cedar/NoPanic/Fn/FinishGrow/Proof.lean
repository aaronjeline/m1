import Examples.Cedar.NoPanic.Fn.FinishGrow.Code
import Examples.Cedar.NoPanic.Fn.NoAllocShim.Proof

/-!
# `<RawVecInner>::finish_grow` at `0x348eac` (the `alloc` instance, align 1)

`finish_grow(out = x0, old_size = x1, old_ptr = x2, new_size = x3)` writes a
`Result<NonNull<[u8]>, TryReserveError>` (24 bytes) at `out`:
* `new_size > isize::MAX`: `Err(CapacityOverflow)` = `[1, 0, _]`;
* `old_size ≠ 0`: `__rust_realloc(old_ptr, old_size, 1, new_size)`;
* else `new_size = 0`: `Ok(dangling)` = `[0, 1, 0]`;
* else `__rust_no_alloc_shim_is_unstable_v2()`, `__rust_alloc(new_size, 1)`;
* a null result: `Err(AllocError { align: 1, size })` = `[1, 1, size]`; else
  `Ok(ptr, size)` = `[0, ptr, size]`.

Contract (`np`): `Post`. It never panics (it has no panic sites; its callers
call `handle_error` on `Err`). `Err` happens only for `new_size > isize::MAX`
or when the allocator fails (`Fails`, see `Externals.lean`).

Proof structure: a cut after the prologue (`SafeN.trans`) establishes the
frame invariant `Inv`; `Inv.call` carries it across a call (from the callee's
`NP` contract), `Inv.of_mem` across stores into the result; the shared tails
(`ok_tail`, `err_tail`) and the epilogue are lemmas used by every path.
-/

namespace Examples.Cedar.NoPanic.Fn.FinishGrow
open M1 Examples.Cedar.Eval Examples.Cedar.NoPanic

variable (H : Heap) (Fails : Prop) (lo top : BitVec 64)

/-- The direct callees are the allocator shims. -/
theorem ext_eqs : ext_0 = rustAlloc ∧ ext_1 = rustRealloc ∧ ext_2 = NoAllocShim.sym_fn :=
  ⟨rfl, rfl, rfl⟩

/-- What holds after the prologue (`s0`: the entry state; the frame is the 0x20
bytes below `s0.sp`; blocks satisfying `keep` are kept). -/
structure Inv (keep : BitVec 64 → Prop) (s0 s : State) : Prop where
  al : s0.sp &&& 15#64 = 0#64
  sp : s.sp = s0.sp + 0xffffffffffffffe0#64
  x20 : s.gpr 20 = s0.gpr 0
  s20 : s.mem.read64 (s0.sp + 0xffffffffffffffe0#64) = s0.gpr 20
  s19 : s.mem.read64 (s0.sp + 0xffffffffffffffe8#64) = s0.gpr 19
  s29 : s.mem.read64 (s0.sp + 0xfffffffffffffff0#64) = s0.gpr 29
  s30 : s.mem.read64 (s0.sp + 0xfffffffffffffff8#64) = s0.gpr 30
  cs : ∀ r : BitVec 5, 21 ≤ r.toNat → r.toNat ≤ 28 → s.gpr r = s0.gpr r
  v : ∀ r : BitVec 5, 8 ≤ r.toNat → r.toNat ≤ 15 → (s.vreg r).setWidth 64 = (s0.vreg r).setWidth 64
  fpcr : s.fpcr = s0.fpcr
  keeps : Keeps top (s0.gpr 0) 24 s0 s
  tlv : s.mem.read64 tlvDesc = s0.mem.read64 tlvDesc
  heap : HeapKept H keep s0 s

/-- What holds on return (`s'.mem` is the memory at the epilogue). -/
def Fin (keep : BitVec 64 → Prop) (s0 s' : State) : Prop :=
  s'.pc = s0.gpr 30 ∧ s'.status = .running ∧ CalleeSaved s0 s' ∧ Keeps top (s0.gpr 0) 24 s0 s' ∧
    s'.mem.read64 tlvDesc = s0.mem.read64 tlvDesc ∧ HeapKept H keep s0 s'

/-- The stack has room for the frame, and the result (24 bytes at `x0`) is in
the caller's part of the stack. -/
def Room (s0 : State) : Prop :=
  0x20 ≤ (s0.sp - lo).toNat ∧ (s0.sp - lo).toNat ≤ (top - lo).toNat ∧
    (s0.gpr 0 - s0.sp).toNat + 24 ≤ (top - s0.sp).toNat

variable {H lo top}

theorem Room.T {s0 : State} (h : Room lo top s0) : (top - s0.sp).toNat + 32 ≤ (top - lo).toNat := by
  obtain ⟨h1, h2, -⟩ := h
  rw [show top - s0.sp = (top - lo) - (s0.sp - lo) by grind,
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
  omega

/-- Offsets from the frame base `S = sp - 0x20`. -/
theorem sub_S (x sp : BitVec 64) :
    (x - (sp + 0xffffffffffffffe0#64)).toNat = ((x - sp).toNat + 32) % 2 ^ 64 := by
  have := Memory.toNat_sub_add x sp (2 ^ 64 - 32)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod] at this
  exact this

theorem sub_via (x y z : BitVec 64) : x - y = (x - z) - (y - z) := by grind
theorem add_add_sub_self (x c j : BitVec 64) : x + c + j - x = c + j := by grind
theorem add_add_sub_self.aux (x c : BitVec 64) : x + c - x = c := by grind

/-- A byte off the stack is not in the result. -/
theorem far_out {s0 : State} (hr : Room lo top s0) {x : BitVec 64} (hx : ¬ OnStack lo top x) :
    24 ≤ (x - s0.gpr 0).toNat := by
  apply Nat.not_lt.mp; intro hlt
  apply hx
  have := onStack_above hr.2.1 hr.2.2 _ hlt
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at this

/-- The saved-register slots (byte `j < 32` of the frame) are not in the result. -/
theorem far_saved {s0 : State} (hr : Room lo top s0) (j : Nat) (hj : j < 32) :
    24 ≤ (s0.sp + 0xffffffffffffffe0#64 + BitVec.ofNat 64 j - s0.gpr 0).toNat := by
  have hT := hr.T
  have h3 := hr.2.2
  have := (top - lo).isLt
  rw [sub_via _ _ s0.sp, add_add_sub_self]
  rw [BitVec.toNat_sub_of_le]
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · rw [BitVec.le_def]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem read64_saved {s0 : State} (hr : Room lo top s0) {m m' : Memory} (k : Nat) (hk : k + 8 ≤ 32)
    (hm : ∀ x, 24 ≤ (x - s0.gpr 0).toNat → m' x = m x) :
    m'.read64 (s0.sp + 0xffffffffffffffe0#64 + BitVec.ofNat 64 k) =
      m.read64 (s0.sp + 0xffffffffffffffe0#64 + BitVec.ofNat 64 k) := by
  apply Memory.read64_congr
  intro i hi
  apply hm
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact far_saved hr (k + i) (by omega)
/-- `Inv` survives a step that changes memory only in the result. -/
theorem Inv.of_mem {keep : BitVec 64 → Prop} {s0 s s' : State} (h : Inv H top keep s0 s)
    (hM : MemFacts H lo top) (hr : Room lo top s0)
    (hsp : s'.sp = s.sp) (h20 : s'.gpr 20 = s.gpr 20)
    (hcs : ∀ r : BitVec 5, 21 ≤ r.toNat → r.toNat ≤ 28 → s'.gpr r = s.gpr r)
    (hv : s'.vreg = s.vreg) (hf : s'.fpcr = s.fpcr)
    (hm : ∀ x, 24 ≤ (x - s0.gpr 0).toNat → s'.mem x = s.mem x) : Inv H top keep s0 s' := by
  have hso : StackOnly lo top s.mem s'.mem := fun x hx => hm x (far_out hr hx)
  refine ⟨h.al, hsp.trans h.sp, h20.trans h.x20, ?_, ?_, ?_, ?_, fun r h1 h2 => (hcs r h1 h2).trans (h.cs r h1 h2),
    fun r h1 h2 => by rw [hv]; exact h.v r h1 h2, hf.trans h.fpcr, ?_, ?_, ?_⟩
  · have e := read64_saved hr 0 (by decide) hm
    simp only [BitVec.add_zero] at e; rw [e]; exact h.s20
  · have e := read64_saved hr 8 (by decide) hm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at e; rw [e]; exact h.s19
  · have e := read64_saved hr 16 (by decide) hm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at e; rw [e]; exact h.s29
  · have e := read64_saved hr 24 (by decide) hm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at e; rw [e]; exact h.s30
  · intro a h1 h2; rw [hm a h2]; exact h.keeps a h1 h2
  · rw [hso.tlv hM]; exact h.tlv
  · exact h.heap.trans (hso.heapKept hM _) (fun _ _ => trivial)

/-- `Inv` survives a call (entered with `SP` = the frame base) whose contract
keeps every stack byte above its `SP`. -/
theorem Inv.call {keep k : BitVec 64 → Prop} {s0 s s' : State} (h : Inv H top keep s0 s)
    (hr : Room lo top s0) (hcs : CalleeSaved s s') {o : BitVec 64} (hk : Keeps top o 0 s s')
    (htl : s'.mem.read64 tlvDesc = s.mem.read64 tlvDesc) (hh : HeapKept H k s s')
    (hkk : ∀ b, keep b → k b) : Inv H top keep s0 s' := by
  have hT := hr.T
  have := (top - lo).isLt
  have hTS : (top - s.sp).toNat = (top - s0.sp).toNat + 32 := by
    rw [h.sp, sub_S, Nat.mod_eq_of_lt (by omega)]
  have rd : ∀ j, j + 8 ≤ 32 → s'.mem.read64 (s0.sp + 0xffffffffffffffe0#64 + BitVec.ofNat 64 j) =
      s.mem.read64 (s0.sp + 0xffffffffffffffe0#64 + BitVec.ofNat 64 j) := by
    intro j hj
    apply Memory.read64_congr
    intro i hi
    apply hk _ _ (Nat.zero_le _)
    rw [hTS, h.sp, BitVec.add_assoc, add_add_sub_self.aux]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨h.al, hcs.sp.trans h.sp, (hcs.gpr 20).trans h.x20, ?_, ?_, ?_, ?_,
    fun r h1 h2 => (hcs.1 r (by omega) (by omega)).trans (h.cs r h1 h2),
    fun r h1 h2 => (hcs.2.2.1 r h1 h2).trans (h.v r h1 h2), hcs.fpcr.trans h.fpcr, ?_, htl.trans h.tlv,
    h.heap.trans hh hkk⟩
  · have e := rd 0 (by decide)
    simp only [BitVec.add_zero] at e; rw [e]; exact h.s20
  · have e := rd 8 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at e; rw [e]; exact h.s19
  · have e := rd 16 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at e; rw [e]; exact h.s29
  · have e := rd 24 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at e; rw [e]; exact h.s30
  · intro a h1 h2
    rw [← h.keeps a h1 h2]
    apply hk _ _ (Nat.zero_le _)
    rw [hTS, h.sp, sub_S, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The epilogue (`0x348f2c`): reload the saved registers and return. -/
theorem epilogue (p : Program) (hp : p.Extends prog) (keep : BitVec 64 → Prop) (s0 s : State)
    (n : Nat) (h : Inv H top keep s0 s) (hpc : s.pc = 0x348f2c#64) (hst : s.status = .running) :
    SafeN p Panic n s fun s' => Fin H top keep s0 s' ∧ s'.mem = s.mem := by
  have hal := h.al; have hsp := h.sp; have h20 := h.s20; have h19 := h.s19; have h29 := h.s29
  have h30 := h.s30
  m1_safe_step
  m1_safe_step
  m1_safe_step
  apply SafeN.done
  refine ⟨⟨rfl, rfl, ⟨fun r h1 h2 => ?_, rfl, h.v, h.fpcr⟩, h.keeps, h.tlv, h.heap⟩, rfl⟩
  rcases (show r = 19#5 ∨ r = 20#5 ∨ r = 29#5 ∨ (21 ≤ r.toNat ∧ r.toNat ≤ 28) by bv_omega) with
    rfl | rfl | rfl | ⟨h3, h4⟩
  · rfl
  · rfl
  · rfl
  · simp (disch := bv_omega) only [upd_other]; exact h.cs r h3 h4

/-- A store into the result keeps the bytes 24 or more past its start. -/
theorem out_keep {m : Memory} {o x v : BitVec 64} (d : Nat) (hd : d + 8 ≤ 24)
    (hx : 24 ≤ (x - o).toNat) : (m.write64 (o + BitVec.ofNat 64 d) v) x = m x := by
  apply write64_keep
  rw [Memory.toNat_sub_add]
  have := (x - o).isLt
  rw [Nat.mod_eq_of_lt (a := d) (by omega)]
  have : 2 ^ 64 ≤ (x - o).toNat + (2 ^ 64 - d) := by omega
  rw [Nat.mod_eq_sub_mod this, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A store in the frame (`c` = `-0x20`, `-0x18`, `-0x10`, `-8`) keeps the bytes above `SP`. -/
theorem frame_keep {m : Memory} {sp x v c : BitVec 64} (hc : 2 ^ 64 - 32 ≤ c.toNat ∧ c.toNat + 8 ≤ 2 ^ 64)
    (hx : (x - sp).toNat + 32 < 2 ^ 64) : (m.write64 (sp + c) v) x = m x := by
  apply write64_keep
  have e := Memory.toNat_sub_add x sp c.toNat
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at e
  rw [e]
  have := c.isLt
  rw [Nat.mod_eq_of_lt (a := c.toNat) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- `Inv` after the prologue. -/
theorem prologue_inv {s0 s : State} (hM : MemFacts H lo top) (hr : Room lo top s0)
    (hal : s0.sp &&& 15#64 = 0#64) (hsp : s.sp = s0.sp + 0xffffffffffffffe0#64)
    (h20 : s.gpr 20 = s0.gpr 0)
    (hcs : ∀ r : BitVec 5, 21 ≤ r.toNat → r.toNat ≤ 28 → s.gpr r = s0.gpr r)
    (hv : s.vreg = s0.vreg) (hf : s.fpcr = s0.fpcr)
    (hm : s.mem = (((s0.mem.write64 (s0.sp + 0xffffffffffffffe0#64) (s0.gpr 20)).write64
      (s0.sp + 0xffffffffffffffe8#64) (s0.gpr 19)).write64 (s0.sp + 0xfffffffffffffff0#64) (s0.gpr 29)).write64
      (s0.sp + 0xfffffffffffffff8#64) (s0.gpr 30)) :
    Inv H top (fun _ => True) s0 s := by
  have hT := hr.T
  have := (top - lo).isLt
  have hso : StackOnly lo top s0.mem s.mem := by
    rw [hm]
    have hb := onStack_below hr.1 hr.2.1
    refine ((((StackOnly.refl _ _ _).trans (StackOnly.write64 _ _ (hb _ 8 ?_ ?_))).trans
      (StackOnly.write64 _ _ (hb _ 8 ?_ ?_))).trans (StackOnly.write64 _ _ (hb _ 8 ?_ ?_))).trans
      (StackOnly.write64 _ _ (hb _ 8 ?_ ?_)) <;> simp
  refine ⟨hal, hsp, h20, ?_, ?_, ?_, ?_, hcs, fun r _ _ => by rw [hv], hf, ?_, ?_, ?_⟩
  all_goals try (clear hso hT this hcs; rw [hm]; m1_simp_step; done)
  · intro a h1 _
    have : (a - s0.sp).toNat + 32 < 2 ^ 64 := by omega
    rw [hm, frame_keep (by decide) this, frame_keep (by decide) this, frame_keep (by decide) this,
      frame_keep (by decide) this]
  · exact hso.tlv hM
  · exact hso.heapKept hM _

/-- Stores into the result keep `Inv`. -/
theorem Inv.of_out {keep : BitVec 64 → Prop} {s0 s s' : State} (h : Inv H top keep s0 s)
    (hM : MemFacts H lo top) (hr : Room lo top s0)
    (hsp : s'.sp = s.sp) (h20 : s'.gpr 20 = s.gpr 20)
    (hcs : ∀ r : BitVec 5, 21 ≤ r.toNat → r.toNat ≤ 28 → s'.gpr r = s.gpr r)
    (hv : s'.vreg = s.vreg) (hf : s'.fpcr = s.fpcr) (a b c : BitVec 64)
    (hm : s'.mem = ((s.mem.write64 (s0.gpr 0 + 8#64) a).write64 (s0.gpr 0 + 16#64) b).write64 (s0.gpr 0) c) :
    Inv H top keep s0 s' := by
  refine Inv.of_mem h hM hr hsp h20 hcs hv hf fun x hx => ?_
  rw [hm, write64_keep _ (by omega), out_keep 16 (by decide) hx, out_keep 8 (by decide) hx]

theorem Inv.weaken {keep keep' : BitVec 64 → Prop} {s0 s : State} (h : Inv H top keep s0 s)
    (hk : ∀ b, keep' b → keep b) : Inv H top keep' s0 s :=
  { h with heap := h.heap.mono hk }

/-- The result's three words. -/
theorem reads_out (m : Memory) (o a b c : BitVec 64) :
    (((m.write64 (o + 8#64) a).write64 (o + 16#64) b).write64 o c).read64 o = c ∧
    (((m.write64 (o + 8#64) a).write64 (o + 16#64) b).write64 o c).read64 (o + 8#64) = a ∧
    (((m.write64 (o + 8#64) a).write64 (o + 16#64) b).write64 o c).read64 (o + 16#64) = b := by
  refine ⟨by simp, ?_, ?_⟩ <;> m1_simp_step

/-- Writing the result changes only the stack. -/
theorem out_stackOnly {s0 : State} (hr : Room lo top s0) (m : Memory) (a b c : BitVec 64) :
    StackOnly lo top m (((m.write64 (s0.gpr 0 + 8#64) a).write64 (s0.gpr 0 + 16#64) b).write64 (s0.gpr 0) c) :=
  fun x hx => by
    have hx := far_out hr hx
    rw [write64_keep _ (by omega), out_keep 16 (by decide) hx, out_keep 8 (by decide) hx]

theorem lt_of_bit63 {x : BitVec 64} (h : ¬ x.getLsbD 63 = true) : x.toNat < 2 ^ 63 := by
  have : x < 0x8000000000000000#64 := by bv_decide
  rw [BitVec.lt_def] at this; simpa using this

/-- From `0x348f18` (`Ok`, pointer in `x0`, size in `x19`): write the result and return. -/
theorem ok_tail (p : Program) (hp : p.Extends prog) {keep : BitVec 64 → Prop} (s0 s : State) (n : Nat)
    (h : Inv H top keep s0 s) (hM : MemFacts H lo top) (hr : Room lo top s0)
    (hpc : s.pc = 0x348f18#64) (hst : s.status = .running) :
    SafeN p Panic n s fun s' => Fin H top keep s0 s' ∧
      s'.mem = ((s.mem.write64 (s0.gpr 0 + 8#64) (s.gpr 0)).write64 (s0.gpr 0 + 16#64) (s.gpr 19)).write64
        (s0.gpr 0) 0#64 := by
  have h20 := h.x20; have hsp := h.sp; have hal := h.al
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  refine (epilogue (H := H) (top := top) p hp keep s0 _ n ?_ rfl rfl).mono fun s' ⟨hf, hm⟩ => ⟨hf, hm⟩
  refine Inv.of_out h hM hr hsp.symm ?_ ?_ rfl rfl _ _ _ rfl
  · simp [upd]
  · intro r h1 h2; simp (disch := bv_omega) only [upd_other]

/-- From `0x348f08` (allocation failed, size in `x19`): write `Err` and return. -/
theorem err_tail (p : Program) (hp : p.Extends prog) {keep : BitVec 64 → Prop} (s0 s : State) (n : Nat)
    (h : Inv H top keep s0 s) (hM : MemFacts H lo top) (hr : Room lo top s0)
    (hpc : s.pc = 0x348f08#64) (hst : s.status = .running) :
    SafeN p Panic n s fun s' => Fin H top keep s0 s' ∧
      s'.mem = ((s.mem.write64 (s0.gpr 0 + 8#64) 1#64).write64 (s0.gpr 0 + 16#64) (s.gpr 19)).write64
        (s0.gpr 0) 1#64 := by
  have h20 := h.x20; have hsp := h.sp; have hal := h.al
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  refine (epilogue (H := H) (top := top) p hp keep s0 _ n ?_ rfl rfl).mono fun s' ⟨hf, hm⟩ => ⟨hf, hm⟩
  refine Inv.of_out h hM hr hsp.symm ?_ ?_ rfl rfl _ _ _ rfl
  · simp [upd]
  · intro r h1 h2; simp (disch := bv_omega) only [upd_other]

variable (H lo top)

/-- The precondition on the current allocation: if there is one (`x1`, its
size, is not 0) it is live at `x2` with layout `(x1, 1)`, and the new size
`x3` is not 0. -/
def Old (s : State) : Prop :=
  s.gpr 1 ≠ 0#64 → H.Live s.mem (s.gpr 2) (s.gpr 1) 1#64 ∧ s.gpr 3 ≠ 0#64

/-- The result `Result<NonNull<[u8]>, TryReserveError>` written at `out = x0`:
either `Ok` (first word 0) with a non-null pointer to a live block of the new
size `x3` (holding the old block's bytes, after a `realloc`), or `Err` (first
word 1), which happens only if `x3 > isize::MAX` or allocation failed
(`Fails`). Every live block other than the old one stays live with its contents. -/
def Post (s s' : State) : Prop :=
  ((s'.mem.read64 (s.gpr 0) = 0#64 ∧ s'.mem.read64 (s.gpr 0 + 8#64) ≠ 0#64 ∧
      s'.mem.read64 (s.gpr 0 + 16#64) = s.gpr 3 ∧
      (s.gpr 3 ≠ 0#64 → H.Live s'.mem (s'.mem.read64 (s.gpr 0 + 8#64)) (s.gpr 3) 1#64 ∧
        (s.gpr 1 ≠ 0#64 → ∀ i, i < (s.gpr 1).toNat → i < (s.gpr 3).toNat →
          s'.mem (s'.mem.read64 (s.gpr 0 + 8#64) + BitVec.ofNat 64 i) = s.mem (s.gpr 2 + BitVec.ofNat 64 i)))) ∨
    (s'.mem.read64 (s.gpr 0) = 1#64 ∧ ((s.gpr 3).getLsbD 63 = true ∨ Fails))) ∧
  HeapKept H (fun b => s.gpr 1 = 0#64 ∨ b ≠ s.gpr 2) s s'

theorem np (p : Program) (hp : p.Extends prog) (hs : p.Extends NoAllocShim.prog)
    (A : Allocator H Fails p top) (hM : MemFacts H lo top) :
    NP p top sym_fn (fun s => Room lo top s ∧ Old H s) (fun s => s.gpr 0) 24 (Post H Fails) := by
  have shim := NoAllocShim.np p hs top
  -- (`m1_safe_step` tries each `Extends` hypothesis, so `hs` may stay.)
  rintro n s hpc hst ⟨hal, hr, hold⟩
  simp only [sym_fn] at hpc
  -- The prologue.
  refine SafeN.trans (Q := fun s1 => s1.pc = 0x348ebc#64 ∧ s1.status = .running ∧
    Inv H top (fun _ => True) s s1 ∧ s1.gpr 1 = s.gpr 1 ∧ s1.gpr 2 = s.gpr 2 ∧ s1.gpr 3 = s.gpr 3) ?_ ?_
  · m1_safe_step
    m1_safe_step
    m1_safe_step
    m1_safe_step
    refine SafeN.done ⟨rfl, rfl, prologue_inv hM hr hal rfl rfl ?_ rfl rfl rfl, rfl, rfl, rfl⟩
    intro r h1 h2; simp (disch := bv_omega) only [upd_other]
  rintro s1 ⟨h1pc, h1st, I1, h11, h12, h13⟩
  have h1sp := I1.sp; have h120 := I1.x20
  clear hpc hst
  m1_safe_step
  refine SafeN.ite (fun hb => ?_) (fun hb => ?_)
  · -- `new_size > isize::MAX`: `Err(CapacityOverflow)`.
    m1_safe_step
    m1_safe_step
    m1_safe_step
    m1_safe_step
    m1_safe_step
    m1_safe_step
    refine (epilogue (H := H) (top := top) p hp (fun _ => True) s _ n ?_ rfl rfl).mono ?_
    · refine Inv.of_mem I1 hM hr h1sp.symm ?_ ?_ rfl rfl ?_
      · simp [upd]
      · intro r h1 h2; simp (disch := bv_omega) only [upd_other]
      · intro x hx
        dsimp only; simp only [BitVec.ofNat_eq_ofNat] at hx
        rw [write64_keep _ (by omega), out_keep 8 (by decide) hx]
    · rintro s' ⟨⟨hpc', hst', hcs', hk', htl', hh'⟩, hm'⟩
      exact ⟨hpc', hst', hcs', hk', htl', Or.inr ⟨by rw [hm']; simp, Or.inl hb⟩,
        hh'.mono fun _ _ => trivial⟩
  have hsz := lt_of_bit63 hb
  m1_safe_step
  m1_safe_step
  refine SafeN.ite (fun h1z => ?_) (fun h1z => ?_)
  · -- No current allocation.
    m1_safe_step
    refine SafeN.ite (fun h3z => ?_) (fun h3z => ?_)
    · -- `new_size = 0`: `Ok(dangling)`.
      m1_safe_step
      refine (ok_tail p hp (keep := fun _ => True) s _ n ?_ hM hr rfl rfl).mono ?_
      · exact Inv.of_mem I1 hM hr h1sp.symm (by simp [upd])
          (fun r h1 h2 => by simp (disch := bv_omega) only [upd_other]) rfl rfl fun _ _ => rfl
      rintro s' ⟨⟨hpc', hst', hcs', hk', htl', hh'⟩, hm'⟩
      obtain ⟨r0, r8, r16⟩ := reads_out s1.mem (s.gpr 0) 1#64 0#64 0#64
      dsimp only at hm'
      simp only [upd, BitVec.reduceEq, ite_true, ite_false, BitVec.ofNat_eq_ofNat] at hm'
      unfold Post
      simp only [BitVec.ofNat_eq_ofNat] at r0 r8 r16 hpc' hk' hh' ⊢
      rw [← hm'] at r0 r8 r16
      exact ⟨hpc', hst', hcs', hk', htl', Or.inl ⟨r0, by rw [r8]; decide, by rw [r16]; exact h3z.symm,
        fun h => absurd h3z h⟩, hh'.mono fun _ _ => trivial⟩
    -- `__rust_no_alloc_shim_is_unstable_v2()`, then `__rust_alloc(new_size, 1)`.
    m1_safe_step
    refine SafeFun.call (shim n) rfl rfl ⟨?_, trivial⟩ ?_
    · show (s.sp + 0xffffffffffffffe0#64) &&& 15#64 = 0#64
      rw [add_and15 _ _ (by decide), hal]
    rintro _ - - ⟨-, -, -, rfl⟩
    m1_safe_step
    m1_safe_step
    m1_safe_step
    refine SafeFun.call (A.alloc n) rfl rfl ⟨?_, ?_, ?_⟩ ?_
    · show (s.sp + 0xffffffffffffffe0#64) &&& 15#64 = 0#64
      rw [add_and15 _ _ (by decide), hal]
    · simp only [upd, BitVec.reduceEq, ite_true, ite_false]
      refine ⟨by decide, by decide, by simp only [BitVec.toNat_ofNat]; omega⟩
    · simp only [upd, BitVec.reduceEq, ite_true, ite_false]; exact h3z
    rintro s2 h2pc h2st ⟨hcs2, hk2, htl2, hpost2, hh2⟩
    have I2 : Inv H top (fun _ => True) s s2 := by
      refine Inv.call (k := fun _ => True) ?_ hr hcs2 hk2 htl2 hh2 fun _ _ => trivial
      refine Inv.of_mem I1 hM hr h1sp.symm ?_ ?_ rfl rfl fun _ _ => rfl
      · simp [upd]
      · intro r h1 h2; simp (disch := bv_omega) only [upd_other]
    simp only [upd, BitVec.reduceEq, ite_true, ite_false] at h2pc hpost2
    have h219 : s2.gpr 19 = s.gpr 3 := (hcs2.gpr 19).trans (by simp [upd])
    have h2sp := I2.sp; have h220 := I2.x20
    clear hcs2 hk2 htl2 hh2
    m1_safe_step
    refine SafeN.ite (fun hz => ?_) (fun hz => ?_)
    · -- `alloc` succeeded: `Ok`.
      refine (ok_tail p hp (keep := fun _ => True) s _ n ?_ hM hr rfl rfl).mono ?_
      · exact Inv.of_mem I2 hM hr h2sp.symm rfl (fun _ _ _ => rfl) rfl rfl fun _ _ => rfl
      rintro s' ⟨⟨hpc', hst', hcs', hk', htl', hh'⟩, hm'⟩
      obtain ⟨h0, -⟩ | ⟨-, hl2⟩ := hpost2
      · exact absurd h0 hz
      have hso := out_stackOnly hr s2.mem (s2.gpr 0) (s.gpr 3) 0#64
      obtain ⟨r0, r8, r16⟩ := reads_out s2.mem (s.gpr 0) (s2.gpr 0) (s.gpr 3) 0#64
      dsimp only at hm'
      unfold Post
      simp only [BitVec.ofNat_eq_ofNat] at hm' hso r0 r8 r16 hpc' hk' hh' ⊢
      rw [h219] at hm'
      rw [← hm'] at hso r0 r8 r16
      refine ⟨hpc', hst', hcs', hk', htl', Or.inl ⟨r0, by rw [r8]; exact hz, r16, fun _ => ⟨?_,
        fun h => absurd h1z h⟩⟩, hh'.mono fun _ _ => trivial⟩
      rw [r8]
      exact hM.frame _ _ _ _ _ hl2 fun x hx => Or.inl (Classical.byContradiction fun hc => hx (hso x hc))
    · -- `alloc` failed: `Err(AllocError)`.
      refine (err_tail p hp (keep := fun _ => True) s _ n ?_ hM hr rfl rfl).mono ?_
      · exact Inv.of_mem I2 hM hr h2sp.symm rfl (fun _ _ _ => rfl) rfl rfl fun _ _ => rfl
      rintro s' ⟨⟨hpc', hst', hcs', hk', htl', hh'⟩, hm'⟩
      obtain ⟨-, hf⟩ | ⟨hnz, -⟩ := hpost2
      · obtain ⟨r0, -, -⟩ := reads_out s2.mem (s.gpr 0) 1#64 (s2.gpr 19) 1#64
        dsimp only at hm'
        rw [← hm'] at r0
        exact ⟨hpc', hst', hcs', hk', htl', Or.inr ⟨r0, Or.inr hf⟩, hh'.mono fun _ _ => trivial⟩
      · exact absurd (Decidable.not_not.mp hz) hnz
  -- `realloc(ptr, old_size, 1, new_size)`.
  obtain ⟨hlive, h3nz⟩ := hold h1z
  have hlive1 := (I1.heap _ _ _ trivial hlive).1
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  refine SafeFun.call (A.realloc n) rfl rfl ⟨?_, ?_⟩ ?_
  · show (s.sp + 0xffffffffffffffe0#64) &&& 15#64 = 0#64
    rw [add_and15 _ _ (by decide), hal]
  · refine ⟨?_, ?_, ?_⟩
    · simp only [upd, BitVec.reduceEq, ite_true, ite_false, BitVec.ofNat_eq_ofNat, h11]; exact hlive1
    · simp only [upd, BitVec.reduceEq, ite_true, ite_false]; exact h3nz
    · simp only [upd, BitVec.reduceEq, ite_true, ite_false]
      refine ⟨by decide, by decide, by simp only [BitVec.toNat_ofNat]; omega⟩
  rintro s2 h2pc h2st ⟨hcs2, hk2, htl2, hpost2⟩
  have I2 : Inv H top (fun b => s.gpr 1 = 0#64 ∨ b ≠ s.gpr 2) s s2 := by
    refine Inv.call (k := fun b => b ≠ s.gpr 2) ?_ hr hcs2 hk2 htl2 ?_ ?_
    · refine Inv.of_mem (I1.weaken fun _ _ => trivial) hM hr h1sp.symm ?_ ?_ rfl rfl fun _ _ => rfl
      · simp [upd]
      · intro r h1 h2; simp (disch := bv_omega) only [upd_other]
    · rcases hpost2 with ⟨-, -, h⟩ | ⟨-, -, -, h⟩
      · exact h.mono fun _ _ => trivial
      · exact h.mono fun b hb => by simpa [upd] using hb
    · intro b hb; simp only [BitVec.ofNat_eq_ofNat] at hb h1z; simpa [h1z] using hb
  simp only [upd, BitVec.reduceEq, ite_true, ite_false] at h2pc hpost2
  have h219 : s2.gpr 19 = s.gpr 3 := (hcs2.gpr 19).trans (by simp [upd])
  have h2sp := I2.sp; have h220 := I2.x20
  clear hcs2 hk2 htl2
  m1_safe_step
  refine SafeN.ite (fun hz => ?_) (fun hz => ?_)
  · -- `realloc` succeeded: `Ok`.
    refine (ok_tail p hp (keep := fun b => s.gpr 1 = 0#64 ∨ b ≠ s.gpr 2) s _ n ?_ hM hr rfl rfl).mono ?_
    · exact Inv.of_mem I2 hM hr h2sp.symm rfl (fun _ _ _ => rfl) rfl rfl fun _ _ => rfl
    rintro s' ⟨⟨hpc', hst', hcs', hk', htl', hh'⟩, hm'⟩
    obtain ⟨h0, -, -⟩ | ⟨-, hl2, hcopy, -⟩ := hpost2
    · exact absurd h0 hz
    have hso := out_stackOnly hr s2.mem (s2.gpr 0) (s.gpr 3) 0#64
    obtain ⟨r0, r8, r16⟩ := reads_out s2.mem (s.gpr 0) (s2.gpr 0) (s.gpr 3) 0#64
    dsimp only at hm'
    unfold Post
    simp only [BitVec.ofNat_eq_ofNat] at hm' hso r0 r8 r16 hpc' hk' hh' ⊢
    rw [h219] at hm'
    rw [← hm'] at hso r0 r8 r16
    refine ⟨hpc', hst', hcs', hk', htl', Or.inl ⟨r0, by rw [r8]; exact hz, r16, fun _ => ⟨?_, fun _ i hi1 hi2 => ?_⟩⟩, hh'⟩
    · rw [r8]
      exact hM.frame _ _ _ _ _ hl2 fun x hx => Or.inl (Classical.byContradiction fun hc => hx (hso x hc))
    · rw [r8, hso _ (hM.offStack _ _ _ _ hl2 i hi2)]
      rw [hcopy i (by rw [h11]; exact hi1) hi2]
      exact (I1.heap _ _ _ trivial hlive).2 i hi1
  · -- `realloc` failed: `Err(AllocError)`.
    m1_safe_step
    refine (err_tail p hp (keep := fun b => s.gpr 1 = 0#64 ∨ b ≠ s.gpr 2) s _ n ?_ hM hr rfl rfl).mono ?_
    · exact Inv.of_mem I2 hM hr h2sp.symm rfl (fun _ _ _ => rfl) rfl rfl fun _ _ => rfl
    rintro s' ⟨⟨hpc', hst', hcs', hk', htl', hh'⟩, hm'⟩
    obtain ⟨-, hf, -⟩ | ⟨h0, -⟩ := hpost2
    · obtain ⟨r0, -, -⟩ := reads_out s2.mem (s.gpr 0) 1#64 (s2.gpr 19) 1#64
      dsimp only at hm'
      rw [← hm'] at r0
      exact ⟨hpc', hst', hcs', hk', htl', Or.inr ⟨r0, Or.inr hf⟩, hh'⟩
    · exact absurd (Decidable.not_not.mp hz) h0

end Examples.Cedar.NoPanic.Fn.FinishGrow
