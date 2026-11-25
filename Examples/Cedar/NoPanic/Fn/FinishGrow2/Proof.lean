import Examples.Cedar.NoPanic.Fn.FinishGrow2.Code
import Examples.Cedar.NoPanic.Fn.NoAllocShim.Proof
import Examples.Cedar.NoPanic.Frame

/-!
# `<RawVecInner>::finish_grow` at `0x21d0fc` (the generic instance)

`finish_grow(out = x0, old_cap = x1, old_ptr = x2, new_cap = x3, align = x4,
elem_size = x5)` writes a `Result<NonNull<[u8]>, TryReserveError>` (24 bytes)
at `out`:
* `elem_size * new_cap` overflows, or exceeds `isize::MAX + 1 - align`:
  `Err(CapacityOverflow)` = `[1, 0, _]`;
* `old_cap ≠ 0`: `__rust_realloc(old_ptr, elem_size * old_cap, align, size)`;
* else `size = 0`: `Ok(dangling)` = `[0, align, 0]`;
* else `__rust_no_alloc_shim_is_unstable_v2()`, `__rust_alloc(size, align)`;
* a null result: `Err(AllocError { align, size })` = `[1, align, size]`; else
  `Ok(ptr, size)` = `[0, ptr, size]`.

The proof uses the generic frame invariant (`Frame.lean`): compare
`Fn/FinishGrow` (the same function for align 1, proved before it existed).
-/

set_option linter.unusedSimpArgs false

namespace Examples.Cedar.NoPanic.Fn.FinishGrow2
open M1 Examples.Cedar.Eval Examples.Cedar.NoPanic

variable (H : Heap) (Fails : Prop) (lo top : BitVec 64)

theorem ext_eqs : ext_0 = rustAlloc ∧ ext_1 = rustRealloc ∧ ext_2 = NoAllocShim.sym_fn := ⟨rfl, rfl, rfl⟩

def L : Layout := ⟨0x30, [(22#5, 0), (21#5, 8), (20#5, 0x10), (19#5, 0x18), (29#5, 0x20), (30#5, 0x28)], []⟩

/-- The result's stores (`0x21d198`) and the epilogue. -/
theorem fin (p : Program) (hp : p.Extends prog) {s0 s : State} {n : Nat}
    (F : Frame L lo top (s0.gpr 0) 24 s0 s) (hout : (s0.gpr 0 - s0.sp).toNat + 24 ≤ (top - s0.sp).toNat)
    (hpc : s.pc = 0x21d198#64) (hst : s.status = .running) (h19 : s.gpr 19 = s0.gpr 0)
    (h10 : s.gpr 10 = 8#64 ∨ s.gpr 10 = 16#64) :
    SafeN p Panic n s (NPPost top (s0.gpr 0) 24 (fun _ s' =>
      s'.mem = (s.mem.write64 (s0.gpr 0 + s.gpr 10) (s.gpr 9)).write64 (s0.gpr 0) (s.gpr 8)) s0) := by
  have hsp := F.sp; frame_simp L at hsp
  simp only [BitVec.ofNat_eq_ofNat] at h19 h10
  m1_run until 0x21d1a0#64
  frame_upd F L as F'
  · refine MemW.write64' _ (MemW.write64' _ (MemW.refl _) (F.wr_out (d := (s.gpr 10#5).toNat) ?_ ?_ hout))
      (F.wr_out (d := 0) (by simp) (by decide) hout)
    · simp [add_sub_self_left]
    · rcases h10 with h | h <;> rw [h] <;> decide
  frame_epi F' L
  rfl

/-- `Ok(x0, x20)` from `0x21d188`. -/
theorem ok_tail (p : Program) (hp : p.Extends prog) {s0 s : State} {n : Nat}
    (F : Frame L lo top (s0.gpr 0) 24 s0 s) (hout : (s0.gpr 0 - s0.sp).toNat + 24 ≤ (top - s0.sp).toNat)
    (hpc : s.pc = 0x21d188#64) (hst : s.status = .running) (h19 : s.gpr 19 = s0.gpr 0) :
    SafeN p Panic n s (NPPost top (s0.gpr 0) 24 (fun _ s' => s'.mem =
      ((s.mem.write64 (s0.gpr 0 + 8#64) (s.gpr 0)).write64 (s0.gpr 0 + 16#64) (s.gpr 20)).write64 (s0.gpr 0) 0#64) s0) := by
  have hsp := F.sp; frame_simp L at hsp
  simp only [BitVec.ofNat_eq_ofNat] at h19 ⊢
  m1_run until 0x21d198#64
  frame_upd F L as F'
  · exact MemW.write64' _ (MemW.refl _) (F.wr_out (d := 8) (by simp [add_sub_self_left]) (by decide) hout)
  refine (fin lo top p hp F' hout rfl rfl (by simp [upd, h19]) (Or.inr (by simp [upd]))).mono ?_
  rintro s' ⟨a, b, c, d, e, hm⟩
  exact ⟨a, b, c, d, e, by simp only [upd, BitVec.reduceEq, ite_true, ite_false] at hm; exact hm⟩

/-- `Err(AllocError { align: x21, size: x20 })` from `0x21d178`. -/
theorem err_tail (p : Program) (hp : p.Extends prog) {s0 s : State} {n : Nat}
    (F : Frame L lo top (s0.gpr 0) 24 s0 s) (hout : (s0.gpr 0 - s0.sp).toNat + 24 ≤ (top - s0.sp).toNat)
    (hpc : s.pc = 0x21d178#64) (hst : s.status = .running) (h19 : s.gpr 19 = s0.gpr 0) :
    SafeN p Panic n s (NPPost top (s0.gpr 0) 24 (fun _ s' => s'.mem =
      ((s.mem.write64 (s0.gpr 0 + 8#64) (s.gpr 21)).write64 (s0.gpr 0 + 16#64) (s.gpr 20)).write64 (s0.gpr 0) 1#64) s0) := by
  have hsp := F.sp; frame_simp L at hsp
  simp only [BitVec.ofNat_eq_ofNat] at h19 ⊢
  m1_run until 0x21d198#64
  frame_upd F L as F'
  · exact MemW.write64' _ (MemW.refl _) (F.wr_out (d := 8) (by simp [add_sub_self_left]) (by decide) hout)
  refine (fin lo top p hp F' hout rfl rfl (by simp [upd, h19]) (Or.inr (by simp [upd]))).mono ?_
  rintro s' ⟨a, b, c, d, e, hm⟩
  exact ⟨a, b, c, d, e, by simp only [upd, BitVec.reduceEq, ite_true, ite_false] at hm; exact hm⟩

/-- The current allocation, if `old_cap ≠ 0`: live at `old_ptr` with layout
`(elem_size * old_cap, align)`; the new size is then not 0. -/
def Old (s : State) : Prop :=
  s.gpr 1 ≠ 0#64 → H.Live s.mem (s.gpr 2) (s.gpr 5 * s.gpr 1) (s.gpr 4) ∧ s.gpr 5 * s.gpr 3 ≠ 0#64

/-- Stack room, the result in the callers' part of the stack, `align` a power of two. -/
def Pre (s : State) : Prop :=
  Room lo top 0x30 s ∧ (s.gpr 0 - s.sp).toNat + 24 ≤ (top - s.sp).toNat ∧
    s.gpr 4 ≠ 0#64 ∧ s.gpr 4 &&& (s.gpr 4 - 1#64) = 0#64 ∧ Old H s

/-- `Ok(ptr, size)` (`ptr` live with the new layout, holding the old bytes after
a `realloc`) or `Err` (only if `elem_size * new_cap + align > 2^63`, or the
allocator failed); every live block other than the old one is kept. -/
def Post (s s' : State) : Prop :=
  ((s'.mem.read64 (s.gpr 0) = 0#64 ∧ s'.mem.read64 (s.gpr 0 + 8#64) ≠ 0#64 ∧
      s'.mem.read64 (s.gpr 0 + 16#64) = s.gpr 5 * s.gpr 3 ∧
      (s.gpr 5 * s.gpr 3 ≠ 0#64 → H.Live s'.mem (s'.mem.read64 (s.gpr 0 + 8#64)) (s.gpr 5 * s.gpr 3) (s.gpr 4) ∧
        (s.gpr 1 ≠ 0#64 → ∀ i, i < (s.gpr 5 * s.gpr 1).toNat → i < (s.gpr 5 * s.gpr 3).toNat →
          s'.mem (s'.mem.read64 (s.gpr 0 + 8#64) + BitVec.ofNat 64 i) = s.mem (s.gpr 2 + BitVec.ofNat 64 i)))) ∨
    (s'.mem.read64 (s.gpr 0) = 1#64 ∧ (2 ^ 63 < (s.gpr 5).toNat * (s.gpr 3).toNat + (s.gpr 4).toNat ∨ Fails))) ∧
  HeapKept H (fun b => s.gpr 1 = 0#64 ∨ b ≠ s.gpr 2) s s'

theorem np (p : Program) (hp : p.Extends prog) (hs : p.Extends NoAllocShim.prog)
    (A : Allocator H Fails p top) (hM : MemFacts H lo top) :
    NP p top sym_fn (Pre H lo top) (fun s => s.gpr 0) 24 (Post H Fails) := by
  have shim := NoAllocShim.np p hs top
  rintro n s hpc hst ⟨hal, ⟨hr, hr'⟩, hout, ha0, ha2, hold⟩
  simp only [sym_fn, BitVec.ofNat_eq_ofNat] at *
  have ht := hM.tlvOffStack
  frame_enter L lo top (s.gpr 0#5) 24 0x21d10c#64 as s1 E
  have F1 := E.frame; have h1pc := E.pc; have h1st := E.status
  have hsp1 : s1.sp = s.sp + 0xffffffffffffffd0#64 := by have := F1.sp; frame_simp L at this; exact this
  have ha : ∀ r : BitVec 5, r.toNat < 19 → s1.gpr r = s.gpr r := E.args
  have h0 := ha 0#5 (by decide); have h1 := ha 1#5 (by decide); have h2 := ha 2#5 (by decide)
  have h3 := ha 3#5 (by decide); have h4 := ha 4#5 (by decide); have h5 := ha 5#5 (by decide)
  have hk1 := E.stackOnly.heapKept hM (fun _ => True)
  clear ha E hpc hst
  have heap : ∀ s' : State, MemW (fun x => (x - s.gpr 0#5).toNat < 24) s1.mem s'.mem →
      HeapKept H (fun _ => True) s s' := fun s' hm => HeapKept.of_out hM hk1 hr' hout hm
  m1_run
  m1_ite hov
  · -- `elem_size * new_cap` overflows: `Err(CapacityOverflow)`.
    frame_upd F1 L as F2
    · frame_mem
    refine (fin lo top p hp F2 hout rfl rfl (by simp [upd]) (Or.inl (by simp [upd]))).mono ?_
    rintro s' ⟨a, b, c, d, e, hm⟩
    simp only [upd, BitVec.reduceEq, ite_true, ite_false] at hm
    refine ⟨a, b, c, d, e, Or.inr ⟨by rw [hm]; m1_simp_step, Or.inl ?_⟩, ?_⟩
    · have h : ¬ (s.gpr 5#5).toNat * (s.gpr 3#5).toNat < 2 ^ 64 := fun hlt =>
        hov (by rw [(umulh_eq_zero _ _).mpr hlt])
      simp only [BitVec.ofNat_eq_ofNat]; omega
    · exact (heap s' (by rw [hm]; mem_range)).mono fun _ _ => trivial
  have hnov := (umulh_eq_zero (s.gpr 5#5) (s.gpr 3#5)).mp (by simpa [eq_comm] using hov)
  have hsz : (s.gpr 5#5 * s.gpr 3#5).toNat = (s.gpr 5#5).toNat * (s.gpr 3#5).toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hnov]
  have hal4 : (s.gpr 4#5).toNat ≤ 2 ^ 63 := by
    have : s.gpr 4#5 ≤ 0x8000000000000000#64 := by bv_decide
    rw [BitVec.le_def] at this; simpa using this
  clear hov
  m1_run
  m1_ite hhi
  · -- The size exceeds `isize::MAX + 1 - align`: `Err(CapacityOverflow)`.
    frame_upd F1 L as F2
    · frame_mem
    refine (fin lo top p hp F2 hout rfl rfl (by simp [upd]) (Or.inl (by simp [upd]))).mono ?_
    rintro s' ⟨a, b, c, d, e, hm⟩
    simp only [upd, BitVec.reduceEq, ite_true, ite_false] at hm
    refine ⟨a, b, c, d, e, Or.inr ⟨by rw [hm]; m1_simp_step, Or.inl ?_⟩, ?_⟩
    · rw [BitVec.lt_def, hsz, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using hal4)] at hhi
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] at hhi ⊢; omega
    · exact (heap s' (by rw [hm]; mem_range)).mono fun _ _ => trivial
  have hvl : ValidLayout (s.gpr 5#5 * s.gpr 3#5) (s.gpr 4#5) := by
    refine ⟨ha0, ha2, ?_⟩
    rw [BitVec.lt_def, hsz, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using hal4)] at hhi
    simp only [BitVec.toNat_ofNat] at hhi; rw [hsz]; omega
  clear hhi
  m1_run
  m1_ite h1z
  · -- No current allocation.
    m1_run
    m1_ite h3z
    · -- `size = 0`: `Ok(dangling)`.
      m1_run until 0x21d188#64
      frame_upd F1 L as F2
      · frame_mem
      refine (ok_tail lo top p hp F2 hout rfl rfl (by simp [upd])).mono ?_
      rintro s' ⟨a, b, c, d, e, hm⟩
      simp only [upd, BitVec.reduceEq, ite_true, ite_false] at hm
      unfold Post; simp only [BitVec.ofNat_eq_ofNat]
      refine ⟨a, b, c, d, e, Or.inl ⟨by rw [hm]; m1_simp_step, by rw [hm]; m1_simp_step,
        by rw [hm]; m1_simp_step, fun h => absurd h3z h⟩, ?_⟩
      exact (heap s' (by rw [hm]; mem_range)).mono fun _ _ => trivial
    -- `__rust_no_alloc_shim_is_unstable_v2()`, then `__rust_alloc(size, align)`.
    m1_run
    refine SafeFun.call (shim n) rfl rfl ⟨by m1_simp_step, trivial⟩ ?_
    rintro _ - - ⟨-, -, -, rfl⟩
    m1_run
    refine SafeFun.call (A.alloc n) rfl rfl ⟨by m1_simp_step, by simp [upd]; exact hvl, by simp [upd]; exact h3z⟩ ?_
    rintro s2 h2pc h2st ⟨hcs, hk, htl, hpost, hh⟩
    have F2 : Frame L lo top (s.gpr 0#5) 24 s s2 := by
      refine Frame.call ?_ hcs hk htl (fun _ h => absurd h (Nat.not_lt_zero _))
      frame_update F1 L
      frame_mem
    simp only [upd, BitVec.reduceEq, ite_true, ite_false] at h2pc hpost
    have h219 : s2.gpr 19#5 = s.gpr 0#5 := (hcs.gpr 19#5).trans (by simp [upd])
    have h220 : s2.gpr 20#5 = s.gpr 5#5 * s.gpr 3#5 := (hcs.gpr 20#5).trans (by simp [upd])
    have h221 : s2.gpr 21#5 = s.gpr 4#5 := (hcs.gpr 21#5).trans (by simp [upd])
    have heap2 : ∀ s' : State, MemW (fun x => (x - s.gpr 0#5).toNat < 24) s2.mem s'.mem →
        HeapKept H (fun _ => True) s s' := fun s' hm =>
      HeapKept.of_out hM ((hk1.trans hh fun _ _ => trivial)) hr' hout hm
    have hsp2 : s2.sp = s.sp + 0xffffffffffffffd0#64 := by have := F2.sp; frame_simp L at this; exact this
    clear hcs hk htl hh
    m1_run
    m1_ite hz
    · -- `Ok`
      frame_upd F2 L as F3
      · frame_mem
      refine (ok_tail lo top p hp F3 hout rfl rfl (by simp [upd, h219])).mono ?_
      rintro s' ⟨a, b, c, d, e, hm⟩
      simp only [upd, BitVec.reduceEq, ite_true, ite_false, h220] at hm
      obtain ⟨h0, -⟩ | ⟨-, hl2⟩ := hpost
      · exact absurd h0 hz
      have hso : StackOnly lo top s2.mem s'.mem := out_stackOnly hr' hout (by rw [hm]; mem_range)
      unfold Post; simp only [BitVec.ofNat_eq_ofNat]
      refine ⟨a, b, c, d, e, Or.inl ⟨by rw [hm]; m1_simp_step, by rw [hm]; m1_simp_step,
        by rw [hm]; m1_simp_step, fun _ => ⟨?_, fun h => absurd h1z h⟩⟩, ?_⟩
      · rw [show s'.mem.read64 (s.gpr 0#5 + 8#64) = s2.gpr 0#5 by rw [hm]; m1_simp_step]
        exact hM.frame _ _ _ _ _ hl2 fun x hx => Or.inl (Classical.byContradiction fun hc => hx (hso x hc))
      · exact (heap2 s' (by rw [hm]; mem_range)).mono fun _ _ => trivial
    · -- `Err(AllocError)`
      frame_upd F2 L as F3
      · frame_mem
      refine (err_tail lo top p hp F3 hout rfl rfl (by simp [upd, h219])).mono ?_
      rintro s' ⟨a, b, c, d, e, hm⟩
      simp only [upd, BitVec.reduceEq, ite_true, ite_false, h220, h221] at hm
      obtain ⟨-, hf⟩ | ⟨hnz, -⟩ := hpost
      · refine ⟨a, b, c, d, e, Or.inr ⟨by rw [hm]; m1_simp_step, Or.inr hf⟩, ?_⟩
        exact (heap2 s' (by rw [hm]; mem_range)).mono fun _ _ => trivial
      · exact absurd (Decidable.not_not.mp hz) hnz
  -- `__rust_realloc(old_ptr, elem_size * old_cap, align, size)`.
  obtain ⟨hlive, h3nz⟩ := hold h1z
  have hlive1 := (hk1 _ _ _ trivial hlive).1
  m1_run
  refine SafeFun.call (A.realloc n) rfl rfl ⟨by m1_simp_step, ?_, ?_, ?_⟩ ?_
  · simp [upd]; exact hlive1
  · simp [upd]; exact h3nz
  · simp [upd]; exact hvl
  rintro s2 h2pc h2st ⟨hcs, hk, htl, hpost⟩
  have F2 : Frame L lo top (s.gpr 0#5) 24 s s2 := by
    refine Frame.call ?_ hcs hk htl (fun _ h => absurd h (Nat.not_lt_zero _))
    frame_update F1 L
    frame_mem
  simp only [upd, BitVec.reduceEq, ite_true, ite_false] at h2pc hpost
  have h219 : s2.gpr 19#5 = s.gpr 0#5 := (hcs.gpr 19#5).trans (by simp [upd])
  have h220 : s2.gpr 20#5 = s.gpr 5#5 * s.gpr 3#5 := (hcs.gpr 20#5).trans (by simp [upd])
  have h221 : s2.gpr 21#5 = s.gpr 4#5 := (hcs.gpr 21#5).trans (by simp [upd])
  have hsp2 : s2.sp = s.sp + 0xffffffffffffffd0#64 := by have := F2.sp; frame_simp L at this; exact this
  clear hcs hk htl
  m1_run
  m1_ite hz
  · -- `Ok`
    frame_upd F2 L as F3
    · frame_mem
    refine (ok_tail lo top p hp F3 hout rfl rfl (by simp [upd, h219])).mono ?_
    rintro s' ⟨a, b, c, d, e, hm⟩
    simp only [upd, BitVec.reduceEq, ite_true, ite_false, h220] at hm
    obtain ⟨h0, -⟩ | ⟨-, hl2, hcopy, hh⟩ := hpost
    · exact absurd h0 hz
    have hso : StackOnly lo top s2.mem s'.mem := out_stackOnly hr' hout (by rw [hm]; mem_range)
    have hr8 : s'.mem.read64 (s.gpr 0#5 + 8#64) = s2.gpr 0#5 := by rw [hm]; m1_simp_step
    unfold Post; simp only [BitVec.ofNat_eq_ofNat]
    refine ⟨a, b, c, d, e, Or.inl ⟨by rw [hm]; m1_simp_step, by rw [hr8]; exact hz,
      by rw [hm]; m1_simp_step, fun _ => ⟨?_, fun _ i hi1 hi2 => ?_⟩⟩, ?_⟩
    · rw [hr8]
      exact hM.frame _ _ _ _ _ hl2 fun x hx => Or.inl (Classical.byContradiction fun hc => hx (hso x hc))
    · rw [hr8, hso _ (hM.offStack _ _ _ _ hl2 i hi2), hcopy i hi1 hi2]
      exact (hk1 _ _ _ trivial hlive).2 i hi1
    · exact HeapKept.of_out hM ((hk1.mono fun _ _ => trivial).trans hh fun b hb => by
        rcases hb with hb | hb
        · exact absurd hb h1z
        · exact hb) hr' hout (by rw [hm]; mem_range)
  · -- `Err(AllocError)`
    m1_run until 0x21d178#64
    frame_upd F2 L as F3
    · frame_mem
    refine (err_tail lo top p hp F3 hout rfl rfl (by simp [upd, h219])).mono ?_
    rintro s' ⟨a, b, c, d, e, hm⟩
    simp only [upd, BitVec.reduceEq, ite_true, ite_false, h220, h221] at hm
    obtain ⟨-, hf, hh⟩ | ⟨hnz, -⟩ := hpost
    · refine ⟨a, b, c, d, e, Or.inr ⟨by rw [hm]; m1_simp_step, Or.inr hf⟩, ?_⟩
      exact HeapKept.of_out hM ((hk1.trans hh fun _ _ => trivial).mono fun _ _ => trivial) hr' hout
        (by rw [hm]; mem_range)
    · exact absurd (Decidable.not_not.mp hz) hnz

end Examples.Cedar.NoPanic.Fn.FinishGrow2
