import Examples.Cedar.NoPanic.Fn.StackLimitInit.Code
import Examples.Cedar.NoPanic.Frame

/-!
# `<Storage<Cell<Option<usize>>, !>>::get_or_init_slow` for `stacker::STACK_LIMIT` at `0x287dec`

The lazy initialisation of `stacker`'s thread-local `STACK_LIMIT`
(`x0` = the storage: `Option<usize>` (16 bytes), then a state byte): if the
state byte's bit 0 is set it returns at once; otherwise it stores
`Some(pthread_get_stackaddr_np(self) - pthread_get_stacksize_np(self))` and
sets the state byte (the `pthread` functions: `LibC`, assumed). Returns `x0`.

Contract: the storage (17 bytes) is off the stack and off the TLV descriptor
(it is thread-local data); only those bytes (and the free stack) change.
-/

set_option linter.unusedSimpArgs false

namespace Examples.Cedar.NoPanic.Fn.StackLimitInit
open M1 Examples.Cedar.Eval Examples.Cedar.NoPanic

variable (H : Heap) (lo top Self : BitVec 64)

theorem ext_eqs : ext_0 = libcStacksize ∧ ext_1 = libcSelf ∧ ext_2 = libcStackaddr := ⟨rfl, rfl, rfl⟩

def L : Layout := ⟨0x20, [(20#5, 0), (19#5, 8), (29#5, 0x10), (30#5, 0x18)], []⟩

def Pre (s : State) : Prop :=
  Room lo top 0x20 s ∧ ∀ i < 17, ¬ OnStack lo top (s.gpr 0 + BitVec.ofNat 64 i) ∧
    ∀ j < 8, s.gpr 0 + BitVec.ofNat 64 i ≠ tlvDesc + BitVec.ofNat 64 j

/-- The epilogue at `0x287e30`. -/
theorem epi (p : Program) (hp : p.Extends prog) {s0 s : State} {n : Nat} {out : BitVec 64} {k : Nat}
    (F : Frame L lo top out k s0 s) (hpc : s.pc = 0x287e30#64) (hst : s.status = .running) :
    SafeN p Panic n s (NPPost top out k (fun _ s' => s'.mem = s.mem ∧ s'.gpr 0 = s.gpr 0) s0) := by
  frame_epi F L
  exact ⟨rfl, by simp [upd]⟩

theorem np (p : Program) (hp : p.Extends prog) (C : LibC H p lo top Self) (hM : MemFacts H lo top) :
    NP p top sym_fn (Pre lo top) (fun s => s.gpr 0) 17
      (fun s s' => s'.gpr 0 = s.gpr 0 ∧ OnlyWrites lo (s.gpr 0) 17 s s') := by
  rintro n s hpc hst ⟨hal, ⟨hr, hr'⟩, hsto⟩
  simp only [sym_fn, BitVec.ofNat_eq_ofNat] at *
  have ht := hM.tlvOffStack
  m1_run
  m1_ite hinit
  · -- Already initialised.
    m1_run
    exact SafeN.done ⟨rfl, rfl, ⟨fun r h1 h2 => by simp (disch := bv_omega) only [upd_other], rfl,
      fun _ _ _ => rfl, rfl⟩, Keeps.of_mem rfl, rfl, by simp (disch := bv_omega) only [upd_other],
      fun _ _ _ => rfl⟩
  -- Run the rest from the state after the check.
  refine SafeN.withEntry (fun s0 s' => NPPost top (s.gpr 0#5) 17 (fun s0 s' => s'.gpr 0 = s0.gpr 0 ∧
    MemW (fun x => FreeStack lo s0.sp x ∨ (x - s0.gpr 0).toNat < 17) s0.mem s'.mem) s0 s') ?_ ?_
  rotate_left
  · intro s' h
    refine NPPost.rebase (s0 := s) (post' := fun s s' => s'.gpr 0 = s.gpr 0 ∧ OnlyWrites lo (s.gpr 0) 17 s s') h rfl (fun r h1 h2 => by simp (disch := bv_omega) only [upd_other]) rfl rfl rfl ?_
    exact fun ⟨a, b⟩ => ⟨a.trans (by simp [upd]), OnlyWrites.of_memW (by simpa [upd] using b)⟩
  frame_enter L lo top (s.gpr 0#5) 17 0x287e00#64 as s1 E
  have F1 := E.frame; have h1pc := E.pc; have h1st := E.status
  have hsp1 : s1.sp = s.sp + 0xffffffffffffffe0#64 := by have := F1.sp; frame_simp L at this; exact this
  have h0 : s1.gpr 0#5 = s.gpr 0#5 := (E.args 0#5 (by decide)).trans (by simp [upd])
  have hfs : ∀ st : State, st.sp = s.sp + 0xffffffffffffffe0#64 → (st.sp - lo).toNat ≤ (s.sp - lo).toNat := by
    intro st h; rw [h, show s.sp + 0xffffffffffffffe0#64 - lo = (s.sp - lo) - 32#64 by bv_omega,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using hr)]; omega
  have hm1 : MemW (fun x => FreeStack lo s.sp x ∨ (x - s.gpr 0#5).toNat < 17) s.mem s1.mem :=
    E.mem.mono fun x hx => Or.inl (frame_freeStack (L := L) hr hr' hx)
  clear E
  m1_run
  frame_call F1 L (C.self n) as s2 F2 hcs2 hp2
  · trivial
  obtain ⟨hself, hw2⟩ := hp2
  have h220 : s2.gpr 20#5 = s.gpr 0#5 := (hcs2.gpr 20#5).trans (by simp [upd])
  have hm2 := hm1.trans (hw2.memW0 (hfs _ rfl) _)
  have hsp2 : s2.sp = s.sp + 0xffffffffffffffe0#64 := by have := F2.sp; frame_simp L at this; exact this
  clear hcs2 hw2
  m1_run
  frame_call F2 L (C.stackaddr n) as s3 F3 hcs3 hw3
  · simp [upd, hself]
  have h320 : s3.gpr 20#5 = s.gpr 0#5 := (hcs3.gpr 20#5).trans (by simp [upd, h220])
  have hm3 := hm2.trans (hw3.memW0 (hfs _ rfl) _)
  have hsp3 : s3.sp = s.sp + 0xffffffffffffffe0#64 := by have := F3.sp; frame_simp L at this; exact this
  clear hcs3 hw3
  m1_run
  frame_call F3 L (C.self n) as s4 F4 hcs4 hp4
  · trivial
  obtain ⟨hself4, hw4⟩ := hp4
  have h420 : s4.gpr 20#5 = s.gpr 0#5 := (hcs4.gpr 20#5).trans (by simp [upd, h320])
  have hm4 := hm3.trans (hw4.memW0 (hfs _ rfl) _)
  have hsp4 : s4.sp = s.sp + 0xffffffffffffffe0#64 := by have := F4.sp; frame_simp L at this; exact this
  clear hcs4 hw4
  m1_run
  frame_call F4 L (C.stacksize n) as s5 F5 hcs5 hw5
  · simp [upd, hself4]
  have h520 : s5.gpr 20#5 = s.gpr 0#5 := (hcs5.gpr 20#5).trans (by simp [upd, h420])
  have hm5 := hm4.trans (hw5.memW0 (hfs _ rfl) _)
  have hsp5 : s5.sp = s.sp + 0xffffffffffffffe0#64 := by have := F5.sp; frame_simp L at this; exact this
  clear hcs5 hw5
  -- Store `Some(addr - size)` and the state byte.
  have hw : ∀ s0 k j, k + j ≤ 17 → ∀ i < j,
      Frame.W L lo top (s.gpr 0#5) 17 s0 (s.gpr 0#5 + BitVec.ofNat 64 k + BitVec.ofNat 64 i) := by
    intro s0 k j hk i hi; right; right
    have := hsto (k + i) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at this; exact this
  m1_run until 0x287e30#64
  frame_upd F5 L as F6
  · refine MemW.write8' _ (MemW.write64' _ (MemW.write64' _ (MemW.refl _) ?_) ?_) ?_
    · simpa using hw _ 0 8 (by decide)
    · exact hw _ 8 8 (by decide)
    · exact hw _ 16 1 (by decide)
  refine (epi lo top p hp F6 rfl rfl).mono fun s' ⟨a, b, c, d, e, hm, h0'⟩ => ⟨a, b, c, d, e, ?_, ?_⟩
  · simp only [BitVec.ofNat_eq_ofNat] at h0' ⊢; rw [h0']; simp [upd, h520]
  · refine hm5.trans (hm ▸ ?_)
    refine MemW.write8' _ (MemW.write64' _ (MemW.write64' _ (MemW.refl _) ?_) ?_) ?_ <;> intro i hi <;> right
    all_goals (refine in_range ?_ i hi; simp [upd, h520, add_sub_self_left])

end Examples.Cedar.NoPanic.Fn.StackLimitInit
