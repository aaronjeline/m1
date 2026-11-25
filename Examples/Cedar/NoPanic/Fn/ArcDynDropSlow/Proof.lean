import Examples.Cedar.NoPanic.Fn.ArcDynDropSlow.Code
import Examples.Cedar.NoPanic.Frame

/-!
# `<Arc<dyn InternalExtensionValue>>::drop_slow` at `0x124d4c`

`drop_slow(self: &mut Arc<dyn T>)` (`x0` points at the fat pointer
`(ptr, vtable)`): calls the value's `drop_in_place` (the vtable's first entry,
if not null) on the value inside the `ArcInner` (at `ptr + round_up(16, align)`)
through `blr`, then decrements the weak count and, if it was 1, tail-calls
`__rust_dealloc(ptr, size', align')` with the `ArcInner`'s layout
(`align' = max(align, 8)`, `size' = (align' + size + 15) & -align'`), where
`size` and `align` are the vtable's second and third entries.

**The indirect call.** Its target is not known statically. The contract takes
an *assumption* on it (`DropFn`): the drop function has an `NP` contract that
needs some predicate `DPre` of the memory (depending only on memory off the
stack) and `Fd` bytes of stack, and keeps every live block the value does not
own (`Own`) and the vtable's 24 bytes. A caller discharges it for the concrete
vtable (here: the `InternalExtensionValue` implementations' drop glue).
-/

set_option linter.unusedSimpArgs false

namespace Examples.Cedar.NoPanic.Fn.ArcDynDropSlow
open M1 Examples.Cedar.Eval Examples.Cedar.NoPanic

variable (H : Heap) (Fails : Prop) (lo top : BitVec 64)

theorem ext_0_eq : ext_0 = rustDealloc := rfl

def L : Layout := ⟨0x30, [(22#5, 0), (21#5, 8), (20#5, 0x10), (19#5, 0x18), (29#5, 0x20), (30#5, 0x28)], []⟩

/-- **Assumed** (by the caller, for the concrete vtable): the contract of the
drop function `D` of a value at `data` with vtable `vt`. -/
structure DropFn (p : Program) (D vt data : BitVec 64) (Fd : Nat) (DPre : Memory → Prop)
    (Own : BitVec 64 → Prop) : Prop where
  framed : ∀ m m', StackOnly lo top m m' → DPre m → DPre m'
  np : NP p top D (fun s => s.gpr 0 = data ∧ Room lo top Fd s ∧ DPre s.mem) (fun _ => 0#64) 0
    (fun s s' => HeapKept H (fun b => ¬ Own b) s s' ∧
      ∀ i < 24, s'.mem (vt + BitVec.ofNat 64 i) = s.mem (vt + BitVec.ofNat 64 i))

/-- The `ArcInner`'s alignment and size for the value's `(size, align)`. -/
def arcAlign (al : BitVec 64) : BitVec 64 := if 8#64 < al then al else 8#64
def arcSize (sz al : BitVec 64) : BitVec 64 := (arcAlign al + sz + 0xf#64) &&& (0#64 - arcAlign al)

/-- The epilogue at `0x124dd8`. -/
theorem epi (p : Program) (hp : p.Extends prog) {s0 s : State} {n : Nat} {out : BitVec 64} {k : Nat}
    (F : Frame L lo top out k s0 s) (hpc : s.pc = 0x124dd8#64) (hst : s.status = .running) :
    SafeN p Panic n s (NPPost top out k (fun _ s' => s'.mem = s.mem) s0) := by
  frame_epi F L
  rfl

/-- `x0` points at `(ptr, vt)` (outside the free stack); the vtable (24 bytes,
outside the free stack) holds `(D, Sz, Al)` with `Al` a power of two; the
`ArcInner` is live with its layout and is not owned by the value; the value's
drop precondition holds; the stack has room for the frame and the drop function. -/
def Pre (D vt ptr Sz Al : BitVec 64) (Fd : Nat) (DPre : Memory → Prop) (Own : BitVec 64 → Prop)
    (s : State) : Prop :=
  Room lo top (0x30 + Fd) s ∧ Outside lo s.sp (s.gpr 0) 16 ∧ Outside lo s.sp vt 24 ∧
  s.mem.read64 (s.gpr 0) = ptr ∧ s.mem.read64 (s.gpr 0 + 8#64) = vt ∧ s.mem.read64 vt = D ∧
  s.mem.read64 (vt + 8#64) = Sz ∧ s.mem.read64 (vt + 16#64) = Al ∧ Al ≠ 0#64 ∧ Al &&& (Al - 1#64) = 0#64 ∧
  H.Live s.mem ptr (arcSize Sz Al) (arcAlign Al) ∧ 16 ≤ (arcSize Sz Al).toNat ∧
  Memory.Disjoint ptr (arcSize Sz Al).toNat vt 24 ∧ ¬ Own ptr ∧ DPre s.mem

theorem np (p : Program) (hp : p.Extends prog) (A : Allocator H Fails p top) (hM : MemFacts H lo top)
    (D vt ptr Sz Al : BitVec 64) (Fd : Nat) (DPre : Memory → Prop) (Own : BitVec 64 → Prop)
    (hD : D ≠ 0#64 → DropFn H lo top p D vt (ptr + (((Al - 1#64) &&& 0xfffffffffffffff0#64) + 0x10#64))
      Fd DPre Own) :
    NP p top sym_fn (Pre H lo top D vt ptr Sz Al Fd DPre Own) (fun _ => 0#64) 0
      (fun s s' => HeapKept H (fun b => ¬ Own b ∧ b ≠ ptr) s s') := by
  rintro n s hpc hst ⟨hal, ⟨hr, hr'⟩, hx0, hvt, hP, hV, hDv, hSz, hAl, ha0, ha2, hlive, h16, hdj, hown, hdp⟩
  simp only [sym_fn, BitVec.ofNat_eq_ofNat] at *
  have ht := hM.tlvOffStack
  have hr0 : 0x30 ≤ (s.sp - lo).toNat := by omega
  frame_enter L lo top 0#64 0 0x124d5c#64 as s1 E
  have F1 := E.frame; have h1pc := E.pc; have h1st := E.status
  have hsp1 : s1.sp = s.sp + 0xffffffffffffffd0#64 := by have := F1.sp; frame_simp L at this; exact this
  have h0 : s1.gpr 0#5 = s.gpr 0#5 := E.args 0#5 (by decide)
  have hP1 : s1.mem.read64 (s.gpr 0#5) = ptr := by rw [E.read64 (by simpa using hx0.sub 0 8 (by decide)), hP]
  have hV1 : s1.mem.read64 (s.gpr 0#5 + 8#64) = vt := by rw [E.read64 (hx0.sub 8 8 (by decide)), hV]
  have hD1 : s1.mem.read64 vt = D := by rw [E.read64 (by simpa using hvt.sub 0 8 (by decide)), hDv]
  have hS1 : s1.mem.read64 (vt + 8#64) = Sz := by rw [E.read64 (hvt.sub 8 8 (by decide)), hSz]
  have hA1 : s1.mem.read64 (vt + 16#64) = Al := by rw [E.read64 (hvt.sub 16 8 (by decide)), hAl]
  have hk1 := E.stackOnly.heapKept hM (fun _ => True)
  have hdp1 := (hD · |>.framed _ _ E.stackOnly hdp)
  have hl1 := (hk1 _ _ _ trivial hlive).1
  clear E hP hV hDv hSz hAl hx0 hpc hst
  have hdj8 : Memory.Disjoint (vt + 8#64) 8 (ptr + 8#64) 8 := by
    have h1 := hdj.symm.sub (c := vt + 8#64) (m := 8) (by simp [add_sub_self_left]) (by decide)
    exact (h1.symm.sub (c := ptr + 8#64) (m := 8) (by simp [add_sub_self_left]; omega) (by decide)).symm
  have hdj8' := hdj8.symm
  have hAA : (if 8#64 < Al then Al else 8#64) = arcAlign Al := rfl
  have hAS : arcAlign Al + (Sz + 15#64) &&& 0#64 - arcAlign Al = arcSize Sz Al := by
    simp only [arcSize, BitVec.add_assoc]
  have hnz : arcSize Sz Al ≠ 0#64 := fun h => by rw [h] at h16; simp at h16
  have hat : ((ptr + 8#64) &&& 15#64).toNat ≤ 8 := by
    have h := hM.aligned _ _ _ _ hlive
    unfold arcAlign at h
    apply atomic8_ok
    by_cases h8 : 8#64 < Al
    · simp only [h8, ite_true] at h
      have : ptr &&& 7#64 = 0#64 := by bv_decide
      simpa using this
    · simp only [h8, ite_false] at h; simpa using h
  -- From `0x124d80` (after the value's drop): drop the weak reference.
  have tail : ∀ s2 : State, s2.pc = 0x124d80#64 → s2.status = .running → Frame L lo top 0#64 0 s s2 →
      s2.gpr 19#5 = ptr → s2.gpr 20#5 = Al → s2.gpr 21#5 = vt → s2.mem.read64 (vt + 8#64) = Sz →
      H.Live s2.mem ptr (arcSize Sz Al) (arcAlign Al) → HeapKept H (fun b => ¬ Own b) s s2 →
      SafeN p Panic n s2 (NPPost top 0#64 0 (fun s s' => HeapKept H (fun b => ¬ Own b ∧ b ≠ ptr) s s') s) := by
    intro s2 h2pc h2st F2 h19 h20 h21 hS2 hl2 hk2
    have hsp2 : s2.sp = s.sp + 0xffffffffffffffd0#64 := by have := F2.sp; frame_simp L at this; exact this
    m1_run
    m1_ite hm
    · frame_upd F2 L as F3
      · frame_mem
      exact (epi lo top p hp F3 rfl rfl).mono fun s' ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, by
        intro b' n' al' hb' hl'; rw [show s'.mem = s2.mem from f]; exact hk2 b' n' al' hb'.1 hl'⟩
    m1_run
    have hk3 : ∀ s' : State, s'.mem = s2.mem.write64 (ptr + 8#64) (s2.mem.read64 (ptr + 8#64) + 18446744073709551615#64) →
        HeapKept H (fun b => ¬ Own b ∧ b ≠ ptr) s s' := fun s' h =>
      (hk2.mono fun b hb => hb.1).trans (HeapKept.write64 hM hl2 (by simp [add_sub_self_left]; omega) h)
        fun b hb => hb.2
    m1_ite hw
    · -- Other weak references remain.
      frame_upd F2 L as F3
      · exact MemW.write64' _ (MemW.refl _) (Frame.wr_heap hM hl2 (by simp [add_sub_self_left]; omega))
      exact (epi lo top p hp F3 rfl rfl).mono fun s' ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, hk3 s' f⟩
    m1_run
    frame_upd F2 L as F3
    · exact MemW.write64' _ (MemW.refl _) (Frame.wr_heap hM hl2 (by simp [add_sub_self_left]; omega))
    m1_run
    frame_tail F3 L as hcs h30 hk htl
    refine SafeFun.call (A.dealloc n) rfl rfl ⟨hal, ?_⟩ ?_
    · simp only [upd, BitVec.reduceEq, ite_true, ite_false, h19]
      exact live_write64 hM hl2 hl2 (by simp [add_sub_self_left]; omega)
    rintro s' h1 h2 ⟨hcs', hk', htl', hkept⟩
    refine SafeN.done (tail_np hcs h30 hk htl h1 h2 hcs' hk' htl' (Or.inl rfl) ?_)
    simp only [upd, BitVec.reduceEq, ite_true, ite_false, h19] at hkept
    exact (hk3 _ (by rfl)).trans hkept fun b hb => hb.2
  m1_run
  m1_ite hDz
  · refine tail _ rfl rfl ?_ (by simp [upd]) (by simp [upd]) (by simp [upd]) hS1 hl1 (hk1.mono fun _ _ => trivial)
    frame_update F1 L
    frame_mem
  -- The value's `drop_in_place`.
  have DF := hD hDz
  m1_run
  refine SafeFun.call (DF.np n) rfl rfl ⟨by m1_simp_step, by simp [upd], ?_, hdp1 hDz⟩ ?_
  · refine Frame.callRoom (L := L) (s0 := s) (lo := lo) (top := top) (out := 0#64) (n := 0) ?_ ?_
    · frame_update F1 L
      frame_mem
    · simp only [L]; omega
  rintro s2 h2pc h2st ⟨hcs, hk, htl, hh, hv⟩
  have F2 : Frame L lo top 0#64 0 s s2 := by
    refine Frame.call ?_ hcs hk htl (fun _ h => absurd h (Nat.not_lt_zero _))
    frame_update F1 L
    frame_mem
  simp only [upd, BitVec.reduceEq, ite_true, ite_false] at h2pc
  refine tail s2 h2pc h2st F2 ((hcs.gpr 19#5).trans (by simp [upd])) ((hcs.gpr 20#5).trans (by simp [upd]))
    ((hcs.gpr 21#5).trans (by simp [upd])) ?_ (hh _ _ _ hown hl1).1 ((hk1.mono fun _ _ => trivial).trans hh fun _ h => h)
  rw [← hS1]
  exact Memory.read64_congr fun i hi => by
    have := hv (8 + i) (by omega)
    rwa [BitVec.ofNat_add, ← BitVec.add_assoc] at this

end Examples.Cedar.NoPanic.Fn.ArcDynDropSlow
