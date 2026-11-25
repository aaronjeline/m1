import Examples.Cedar.NoPanic.Fn.TypeLt.Code
import Examples.Cedar.NoPanic.Fn.SmolStrPartialCmp.Proof

/-!
# `<Type as PartialOrd>::lt` as `FnMut` (`call_mut`) at `0xe0cc0`

Compares two `Type`s (`x0`, `x1`) by discriminant and, for entity/record-like
variants, their names (`SmolStr::partial_cmp` on the basename, then the
namespace path element by element: a loop with calls). It reads only.
Contract: no precondition besides stack room (for its frame and
`partial_cmp`'s); it never panics and writes only its own frame (and its
callees' frames).

Proved with the whole-body invariant `body_loop` and `body_case` (one case
per instruction, generated mechanically).
-/

set_option linter.unusedSimpArgs false

namespace Examples.Cedar.NoPanic.Fn.TypeLt
open M1 Examples.Cedar.Eval Examples.Cedar.NoPanic

variable (H : Heap) (lo top Self : BitVec 64)

theorem ext_0_eq : ext_0 = SmolStrPartialCmp.sym_fn := rfl

def L : Layout := ⟨0x40, [(24#5, 0), (23#5, 8), (22#5, 0x10), (21#5, 0x18), (20#5, 0x20), (19#5, 0x28),
  (29#5, 0x30), (30#5, 0x38)], []⟩

/-- The body: every instruction but the prologue and the epilogues. -/
def body : List (BitVec 64) := [0xe0cd4#64, 0xe0cd8#64, 0xe0cdc#64, 0xe0ce0#64, 0xe0ce4#64, 0xe0ce8#64, 0xe0cec#64, 0xe0cf0#64, 0xe0cf4#64, 0xe0cf8#64, 0xe0cfc#64, 0xe0d00#64, 0xe0d04#64, 0xe0d08#64, 0xe0d0c#64, 0xe0d10#64, 0xe0d14#64, 0xe0d18#64, 0xe0d1c#64, 0xe0d20#64, 0xe0d24#64, 0xe0d28#64, 0xe0d2c#64, 0xe0d30#64, 0xe0d34#64, 0xe0d38#64, 0xe0d3c#64, 0xe0d40#64, 0xe0d44#64, 0xe0d48#64, 0xe0d4c#64, 0xe0d50#64, 0xe0d54#64, 0xe0d58#64, 0xe0d5c#64, 0xe0d60#64, 0xe0d64#64, 0xe0d68#64, 0xe0d80#64, 0xe0d84#64, 0xe0d88#64, 0xe0d8c#64, 0xe0d90#64, 0xe0d94#64, 0xe0d98#64, 0xe0d9c#64, 0xe0da0#64, 0xe0da4#64, 0xe0da8#64, 0xe0dac#64, 0xe0db0#64, 0xe0db4#64, 0xe0db8#64, 0xe0dbc#64, 0xe0dc0#64, 0xe0dc4#64, 0xe0dc8#64, 0xe0dcc#64, 0xe0dd0#64, 0xe0dd4#64, 0xe0dd8#64, 0xe0ddc#64, 0xe0de0#64, 0xe0de4#64, 0xe0de8#64, 0xe0dec#64, 0xe0df0#64, 0xe0e08#64, 0xe0e0c#64, 0xe0e10#64, 0xe0e28#64, 0xe0e2c#64, 0xe0e30#64, 0xe0e48#64, 0xe0e4c#64, 0xe0e50#64, 0xe0e54#64, 0xe0e58#64, 0xe0e5c#64, 0xe0e60#64]

set_option maxHeartbeats 2000000 in
theorem np (p : Program) (hp : p.Extends prog) (hs : p.Extends SmolStrPartialCmp.prog)
    (C : LibC H p lo top Self) (hM : MemFacts H lo top) :
    NP p top sym_fn (Room lo top (0x40 + 0x20)) (fun _ => 0#64) 0 (fun s s' => OnlyWrites lo 0#64 0 s s') := by
  have PC := SmolStrPartialCmp.np H lo top Self p hs C hM
  rintro n s hpc hst ⟨hal, hr, hr'⟩
  simp only [sym_fn, BitVec.ofNat_eq_ofNat] at *
  have ht := hM.tlvOffStack
  have hr0 : 0x40 ≤ (s.sp - lo).toNat := by omega
  frame_enter L lo top 0#64 0 0xe0cd4#64 as s1 E
  refine body_loop body ⟨E.frame, E.mem.mono fun x hx => Or.inl (frame_freeStack (L := L) hr0 hr' hx), E.status⟩
    (by rw [E.pc]; decide) ?_
  clear E hpc hst
  intro n s2 hI hpc
  simp only [body, List.mem_cons, List.mem_nil_iff, or_false] at hpc
  split_ors hpc
  all_goals body_case L body hI hpc (PC n)

end Examples.Cedar.NoPanic.Fn.TypeLt
