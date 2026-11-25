import Examples.Cedar.NoPanic.Fn.ArcStrDropSlow.Code
import Examples.Cedar.NoPanic.Lemmas

/-!
# `<Arc<str>>::drop_slow` at `0x2be708` (the `regex_automata` instance)

`drop_slow(self: &mut Arc<str>)` (`x0` points at the fat pointer `(ptr, len)`)
runs after the strong count reached 0: unless `ptr` is `usize::MAX` (a
dangling `Weak`), it decrements the weak count at `ptr + 8` (`ldaddl`) and, if
it was 1, tail-calls `__rust_dealloc(ptr, (len + 0x17) & !7, 8)` (the
`ArcInner<str>` layout: two counts, then `len` bytes, rounded up to 8).

Contract (`np`): if `ptr ≠ usize::MAX`, the `ArcInner` is a live block of that
layout and `len ≤ isize::MAX`. It may change only the 8 bytes of the weak
count (`out = ptr + 8`); every other live block stays live.
-/

namespace Examples.Cedar.NoPanic.Fn.ArcStrDropSlow
open M1 Examples.Cedar.Eval Examples.Cedar.NoPanic

variable (H : Heap) (Fails : Prop) (lo top : BitVec 64)

/-- The tail call goes to the allocator's `__rust_dealloc`. -/
theorem ext_0_eq : ext_0 = rustDealloc := rfl

/-- The precondition: `x0` points at `(ptr, len)`; unless `ptr` is `usize::MAX`
its `ArcInner<str>` is live. -/
def Pre (s : State) : Prop :=
  s.mem.read64 (s.gpr 0) ≠ 0xffffffffffffffff#64 →
    (s.mem.read64 (s.gpr 0 + 8#64)).toNat < 2 ^ 63 ∧
    H.Live s.mem (s.mem.read64 (s.gpr 0)) ((s.mem.read64 (s.gpr 0 + 8#64) + 0x17#64) &&& 0xfffffffffffffff8#64) 8#64

theorem np (p : Program) (hp : p.Extends prog)
    (A : Allocator H Fails p top) (hH : MemFacts H lo top) :
    NP p top sym_fn (Pre H) (fun s => s.mem.read64 (s.gpr 0) + 8#64) 8
      (fun s s' => ∀ b n al, b ≠ s.mem.read64 (s.gpr 0) → H.Live s.mem b n al → H.Live s'.mem b n al) := by
  rintro n s hpc hst ⟨hal, hpre⟩
  simp only [sym_fn] at hpc
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  rw [cond_eq_cmn]
  refine SafeN.ite (fun hc => ?_) (fun hc => ?_)
  · -- `ptr = usize::MAX`: a dangling `Weak`, nothing to do.
    m1_safe_step
    apply SafeN.done
    refine ⟨rfl, rfl, ⟨fun r h1 h2 => ?_, rfl, fun _ _ _ => rfl, rfl⟩, fun _ _ _ => rfl, rfl,
      fun _ _ _ _ h => h⟩
    simp (disch := bv_omega) only [upd_other]
  · have hne : s.mem.read64 (s.gpr 0) ≠ 0xffffffffffffffff#64 := by
      intro h; apply hc; simp only [BitVec.ofNat_eq_ofNat] at h ⊢; rw [h]; decide
    obtain ⟨hlen, hlive⟩ := hpre hne
    have hA := hH.aligned _ _ _ _ hlive
    have hat : ((s.mem.read64 (s.gpr 0) + 8#64) &&& 15#64).toNat ≤ 8 := by
      have : (s.mem.read64 (s.gpr 0) + 8#64) &&& 15#64 ≤ 8#64 := by bv_decide
      rw [BitVec.le_def] at this; simpa using this
    clear hpre hc hA
    have hsz : 16 ≤ ((s.mem.read64 (s.gpr 0 + 8#64) + 0x17#64) &&& 0xfffffffffffffff8#64).toNat := by
      have : 16#64 ≤ (s.mem.read64 (s.gpr 0 + 8#64) + 0x17#64) &&& 0xfffffffffffffff8#64 := by
        have : s.mem.read64 (s.gpr 0 + 8#64) < 0x8000000000000000#64 := by
          rw [BitVec.lt_def]; simpa using hlen
        bv_decide
      rw [BitVec.le_def] at this; simpa using this
    have hwin : ((s.mem.read64 (s.gpr 0) + 8#64) - s.mem.read64 (s.gpr 0)).toNat + 8 ≤
        ((s.mem.read64 (s.gpr 0 + 8#64) + 0x17#64) &&& 0xfffffffffffffff8#64).toNat := by
      rw [show s.mem.read64 (s.gpr 0) + 8#64 - s.mem.read64 (s.gpr 0) = 8#64 by bv_omega]
      simp only [BitVec.toNat_ofNat]; omega
    have hl1 := fun v => live_write64 (v := v) hH hlive hlive hwin
    have hkeep := fun b n al (h : H.Live s.mem b n al) v => live_write64 (v := v) hH h hlive hwin
    have htlv := (hH.offTlv _ _ _ _ hlive).sub hwin (by decide)
    simp only [BitVec.ofNat_eq_ofNat] at hlen hlive hat hsz hl1 hkeep htlv ⊢
    generalize hL : s.mem.read64 (s.gpr 0#5 + 8#64) = len at hlen hlive hsz hl1 hkeep ⊢
    clear hlen hwin
    generalize hP : s.mem.read64 (s.gpr 0#5) = ptr at hlive hat hsz hl1 hkeep hne htlv ⊢
    m1_safe_step
    m1_safe_step
    m1_safe_step
    m1_safe_step
    m1_safe_step
    m1_safe_step
    refine SafeN.ite (fun hw => ?_) (fun hw => ?_)
    · -- Other weak references remain.
      m1_safe_step
      apply SafeN.done
      refine ⟨rfl, rfl, ⟨fun r h1 h2 => ?_, rfl, fun _ _ _ => rfl, rfl⟩, Keeps.of_write64 rfl,
        Memory.read64_write64_of_disjoint htlv, fun b n al _ h => hkeep b n al h _⟩
      simp (disch := bv_omega) only [upd_other]
    · m1_safe_step
      m1_safe_step
      m1_safe_step
      m1_safe_step
      have hz : (len + 23#64 &&& 18446744073709551608#64 == 0#64) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro h; rw [h] at hsz; simp at hsz
      rw [cond_eq_logic64, hz]
      simp only [Bool.false_eq_true, ite_false]
      m1_safe_step
      m1_safe_step
      -- The tail call `__rust_dealloc(ptr, size, 8)`.
      refine SafeFun.call (A.dealloc n) rfl rfl ⟨hal, ?_⟩ ?_
      · simp only [upd, BitVec.reduceEq, ite_true, ite_false]; exact hl1 _
      rintro s' h1 h2 ⟨hcs, hk, htl, hkept⟩
      apply SafeN.done
      simp only [upd, BitVec.reduceEq, ite_true, ite_false] at h1 hkept
      refine ⟨h1, h2, CalleeSaved.trans ?_ hcs, Keeps.trans (Keeps.of_write64 rfl) (Keeps.of_none hk) ?_,
        htl.trans (Memory.read64_write64_of_disjoint htlv),
        fun b n al hb h => (hkept b n al hb (hkeep b n al h _)).1⟩
      · exact ⟨fun r h1 h2 => by simp (disch := bv_omega) only [upd_other], rfl, fun _ _ _ => rfl, rfl⟩
      · rfl