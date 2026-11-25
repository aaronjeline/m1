import Examples.Cedar.NoPanic.Fn.ArcPatternDropSlow.Code
import Examples.Cedar.NoPanic.Frame

set_option linter.unusedSimpArgs false

namespace Examples.Cedar.NoPanic.Fn.ArcPatternDropSlow
open M1 Examples.Cedar.Eval Examples.Cedar.NoPanic

variable (H : Heap) (Fails : Prop) (lo top : BitVec 64)

theorem ext_0_eq : ext_0 = rustDealloc := rfl

def L : Layout := ⟨0x20, [(20#5, 0), (19#5, 8), (29#5, 0x10), (30#5, 0x18)], []⟩

/-- The epilogue at `0x12504c`. -/
theorem epi (p : Program) (hp : p.Extends prog) {s0 s : State} {n : Nat} {out : BitVec 64} {k : Nat}
    (F : Frame L lo top out k s0 s) (hpc : s.pc = 0x12504c#64) (hst : s.status = .running) :
    SafeN p Panic n s (NPPost top out k (fun _ s' => s'.mem = s.mem) s0) := by
  frame_epi F L
  rfl

/-- `x0` points at the `Arc` (outside the free stack); its `ArcInner` (counts,
then the `Vec<PatternElem>`: capacity at `0x10`, buffer at `0x18`) is live,
and so is the buffer (layout `(4 * cap, 4)`) if the capacity is not 0. -/
def Pre (s : State) : Prop :=
  Outside lo s.sp (s.gpr 0) 8 ∧
  H.Live s.mem (s.mem.read64 (s.gpr 0)) 0x28#64 8#64 ∧
  (s.mem.read64 (s.mem.read64 (s.gpr 0) + 0x10#64) ≠ 0#64 →
    H.Live s.mem (s.mem.read64 (s.mem.read64 (s.gpr 0) + 0x18#64))
      (s.mem.read64 (s.mem.read64 (s.gpr 0) + 0x10#64) <<< 2) 4#64 ∧
    s.mem.read64 (s.mem.read64 (s.gpr 0) + 0x18#64) ≠ s.mem.read64 (s.gpr 0))

theorem np (p : Program) (hp : p.Extends prog) (A : Allocator H Fails p top) (hM : MemFacts H lo top) :
    NP p top sym_fn (fun s => Room lo top 0x20 s ∧ Pre H lo s) (fun _ => 0#64) 0
      (fun s s' => HeapKept H (fun b => b ≠ s.mem.read64 (s.gpr 0) ∧
        b ≠ s.mem.read64 (s.mem.read64 (s.gpr 0) + 0x18#64)) s s') := by
  rintro n s hpc hst ⟨hal, ⟨hr, hr'⟩, hx0, hlive, hbuf⟩
  simp only [sym_fn, BitVec.ofNat_eq_ofNat] at *
  have ht := hM.tlvOffStack
  frame_enter L lo top 0#64 0 0x124ff8#64 as s1 E
  have F1 := E.frame; have h1pc := E.pc; have h1st := E.status
  have hsp1 : s1.sp = s.sp + 0xffffffffffffffe0#64 := by have := F1.sp; frame_simp L at this; exact this
  have rd : ∀ a, (a - s.mem.read64 (s.gpr 0#5)).toNat + 8 ≤ 0x28 → s1.mem.read64 a = s.mem.read64 a :=
    fun a ha => E.read64 (Outside.of_live hM hlive hr' (by simpa using ha))
  have hP1 : s1.mem.read64 (s1.gpr 0#5) = s.mem.read64 (s.gpr 0#5) := by
    rw [E.args 0#5 (by decide), E.read64 hx0]
  have hC1 := rd (s.mem.read64 (s.gpr 0#5) + 0x18#64) (by simp [add_sub_self_left])
  have hB1 := rd (s.mem.read64 (s.gpr 0#5) + 0x10#64) (by simp [add_sub_self_left])
  have hk1 := E.stackOnly.heapKept hM (fun _ => True)
  have hat := atomic8_ok (hM.aligned _ _ _ _ hlive)
  generalize s.mem.read64 (s.gpr 0#5) = P at hlive hbuf hP1 hC1 hB1 rd hat ⊢
  generalize s.mem.read64 (P + 0x10#64) = C at hbuf hB1
  generalize s.mem.read64 (P + 0x18#64) = Bf at hbuf hC1 ⊢
  have hl1 := (hk1 _ _ _ trivial hlive).1
  clear E hx0 hpc hst rd
  -- From `0x1259ec` (both paths): drop the `Arc`'s weak reference.
  have tail : ∀ s2 : State, s2.pc = 0x125014#64 → s2.status = .running → Frame L lo top 0#64 0 s s2 →
      s2.gpr 19#5 = P → H.Live s2.mem P 0x28#64 8#64 → HeapKept H (fun b => b ≠ P ∧ b ≠ Bf) s s2 →
      SafeN p Panic n s2 (NPPost top 0#64 0 (fun s s' => HeapKept H (fun b => b ≠ P ∧ b ≠ Bf) s s') s) := by
    intro s2 h2pc h2st F2 h19 hl2 hk2
    have hsp2 : s2.sp = s.sp + 0xffffffffffffffe0#64 := by have := F2.sp; frame_simp L at this; exact this
    m1_run
    m1_ite hm
    · frame_upd F2 L as F3
      · frame_mem
      exact (epi lo top p hp F3 rfl rfl).mono fun s' ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, by
        intro b' n' al' hb' hl'; rw [f]; exact hk2 b' n' al' hb' hl'⟩
    m1_run
    have hk3 : ∀ s' : State, s'.mem = s2.mem.write64 (P + 8#64) (s2.mem.read64 (P + 8#64) + 18446744073709551615#64) →
        HeapKept H (fun b => b ≠ P ∧ b ≠ Bf) s s' := fun s' h =>
      hk2.trans (HeapKept.write64 hM hl2 (by simp [add_sub_self_left]) h) fun b hb => hb.1
    m1_ite hw
    · -- Other weak references remain.
      frame_upd F2 L as F3
      · exact MemW.write64' _ (MemW.refl _) (Frame.wr_heap hM hl2 (by simp [add_sub_self_left]))
      exact (epi lo top p hp F3 rfl rfl).mono fun s' ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, by
        intro b' n' al' hb' hl'
        exact hk3 s' f b' n' al' hb' hl'⟩
    · -- The last weak reference: free the `ArcInner` (a tail call).
      m1_run until 0x125040#64
      frame_upd F2 L as F3
      · exact MemW.write64' _ (MemW.refl _) (Frame.wr_heap hM hl2 (by simp [add_sub_self_left]))
      m1_run
      frame_tail F3 L as hcs h30 hk htl
      refine SafeFun.call (A.dealloc n) rfl rfl ⟨hal, ?_⟩ ?_
      · simp only [upd, BitVec.reduceEq, ite_true, ite_false]
        exact live_write64 hM hl2 hl2 (by simp [add_sub_self_left])
      rintro s' h1 h2 ⟨hcs', hk', htl', hkept⟩
      refine SafeN.done (tail_np hcs h30 hk htl h1 h2 hcs' hk' htl' (Or.inl rfl) ?_)
      simp only [upd, BitVec.reduceEq, ite_true, ite_false] at hkept
      exact (hk3 _ (by rfl)).trans hkept fun b hb => hb.1
  m1_run
  m1_ite hc
  · refine tail _ rfl rfl ?_ (by simp [upd]) hl1 (hk1.mono fun _ _ => trivial)
    frame_update F1 L
    frame_mem
  -- Free the string's buffer.
  obtain ⟨hlb, hne⟩ := hbuf hc
  have hlb1 := (hk1 _ _ _ trivial hlb).1
  m1_run
  refine SafeFun.call (A.dealloc n) rfl rfl ⟨by m1_simp_step, ?_⟩ ?_
  · simp only [upd, BitVec.reduceEq, ite_true, ite_false]; exact hlb1
  rintro s2 h2pc h2st ⟨hcs, hk, htl, hkept⟩
  have F2 : Frame L lo top 0#64 0 s s2 := by
    refine Frame.call ?_ hcs hk htl (fun _ h => absurd h (Nat.not_lt_zero _))
    frame_update F1 L
    frame_mem
  simp only [upd, BitVec.reduceEq, ite_true, ite_false] at h2pc hkept
  refine tail s2 h2pc h2st F2 ((hcs.gpr 19#5).trans (by simp [upd])) (hkept _ _ _ (Ne.symm hne) hl1).1 ?_
  exact (hk1.mono fun _ _ => trivial).trans hkept fun b hb => hb.2

end Examples.Cedar.NoPanic.Fn.ArcPatternDropSlow
