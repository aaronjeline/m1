import Examples.Cedar.NoPanic.Fn.SmolStrPartialCmp.Code
import Examples.Cedar.NoPanic.Frame

/-!
# `<SmolStr as PartialOrd>::partial_cmp` at `0x28ef60`

`partial_cmp(a = x0, b = x1)`: computes each string's `(ptr, len)` from its
representation (inline: tag byte ≤ 0x17 is the length, bytes at `+1`; static
`&str`: `(ptr, len)` at `+8`; heap `Arc<str>`: `ArcInner` at `+8`, data at
`+0x10`), then (with a shrink-wrapped frame) `memcmp(pa, pb, min(la, lb))`
and the length difference. It reads only: its contract has no precondition
besides stack room (loads cannot fault in the model), and says nothing about
the result yet: it never panics and changes nothing but its own frame.

The frameless part up to the prologue (`0x28f004`) is proved with `leaf_to`
(one step per instruction, `leaf_auto`); the rest with the frame invariant.
-/

set_option linter.unusedSimpArgs false

namespace Examples.Cedar.NoPanic.Fn.SmolStrPartialCmp
open M1 Examples.Cedar.Eval Examples.Cedar.NoPanic

variable (H : Heap) (lo top Self : BitVec 64)

theorem ext_0_eq : ext_0 = libcMemcmp := rfl

def L : Layout := ⟨0x20, [(20#5, 0), (19#5, 8), (29#5, 0x10), (30#5, 0x18)], []⟩

/-- The instructions before the prologue. -/
def prePcs : List (BitVec 64) := pcs.take 41

/-- The epilogue at `0x28f034`. -/
theorem epi (p : Program) (hp : p.Extends prog) {s0 s : State} {n : Nat} {out : BitVec 64} {k : Nat}
    (F : Frame L lo top out k s0 s) (hpc : s.pc = 0x28f034#64) (hst : s.status = .running) :
    SafeN p Panic n s (NPPost top out k (fun _ s' => s'.mem = s.mem) s0) := by
  frame_epi F L
  rfl

theorem np (p : Program) (hp : p.Extends prog) (C : LibC H p lo top Self) (hM : MemFacts H lo top) :
    NP p top sym_fn (Room lo top 0x20) (fun _ => 0#64) 0 (fun s s' => OnlyWrites lo 0#64 0 s s') := by
  rintro n s hpc hst ⟨hal, hr, hr'⟩
  simp only [sym_fn, BitVec.ofNat_eq_ofNat] at *
  have ht := hM.tlvOffStack
  refine (leaf_to (p := p) prePcs 0x28f004#64 (by simp only [hpc]; decide) hst ?_).trans ?_
  · simp only [prePcs, pcs, List.take]
    leaf_auto prePcs
  rintro st ⟨hpc', hst', hsp', hg', hv', hf', hm'⟩
  have hal' : st.sp &&& 15#64 = 0#64 := by rw [hsp']; exact hal
  have hr0 : 0x20 ≤ (st.sp - lo).toNat := by rw [hsp']; exact hr
  have hr0' : (st.sp - lo).toNat ≤ (top - lo).toNat := by rw [hsp']; exact hr'
  refine SafeN.withEntry (fun s0 s' => NPPost top 0#64 0 (fun s0 s' =>
    MemW (fun x => FreeStack lo s0.sp x ∨ (x - 0#64).toNat < 0) s0.mem s'.mem) s0 s') ?_ ?_
  rotate_left
  · intro s' h
    refine NPPost.rebase (s0 := s) (post' := fun s s' => OnlyWrites lo 0#64 0 s s') h hsp' hg' hv' hf' hm' ?_
    intro hw; exact OnlyWrites.of_memW (by rw [← hsp', ← hm']; exact hw)
  clear hsp' hg' hv' hf' hm' hpc hst
  frame_enter L lo top 0#64 0 0x28f010#64 as s1 E
  have F1 := E.frame; have h1pc := E.pc; have h1st := E.status
  have hsp1 : s1.sp = st.sp + 0xffffffffffffffe0#64 := by have := F1.sp; frame_simp L at this; exact this
  have hm1 : MemW (fun x => FreeStack lo st.sp x ∨ (x - 0#64).toNat < 0) st.mem s1.mem :=
    E.mem.mono fun x hx => Or.inl (frame_freeStack (L := L) hr0 hr0' hx)
  have hfs : (st.sp + 0xffffffffffffffe0#64 - lo).toNat ≤ (st.sp - lo).toNat := by
    rw [show st.sp + 0xffffffffffffffe0#64 - lo = (st.sp - lo) - 32#64 by bv_omega,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using hr0)]; omega
  clear E
  m1_run
  frame_call F1 L (C.memcmp n) as s2 F2 hcs2 hp2
  · trivial
  have hm2 := hm1.trans (hp2.1.memW0 hfs _)
  have hsp2 : s2.sp = st.sp + 0xffffffffffffffe0#64 := by have := F2.sp; frame_simp L at this; exact this
  clear hcs2 hp2
  m1_run until 0x28f034#64
  frame_upd F2 L as F3
  · frame_mem
  exact (epi lo top p hp F3 rfl rfl).mono fun s' ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, by
    show MemW _ st.mem s'.mem; rw [show s'.mem = s2.mem from f]; exact hm2⟩

end Examples.Cedar.NoPanic.Fn.SmolStrPartialCmp
