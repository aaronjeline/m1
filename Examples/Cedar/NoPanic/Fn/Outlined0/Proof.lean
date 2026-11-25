import Examples.Cedar.NoPanic.Fn.Outlined0.Code
import Examples.Cedar.NoPanic.Spec

/-!
# `_OUTLINED_FUNCTION_0` at `0xe1300`

```
sub  x8, x29, #0x1
str  x8, [sp, #0x18]
add  x8, sp, #0x8
stur x8, [x29, #-0x10]
ret
```
A machine-outliner helper called (`bl`) from the bodies of the
`OnceLock::initialize` instances: it fills two slots of the caller's frame
(`[sp + 0x18] := x29 - 1`, `[x29 - 0x10] := sp + 8`) and sets `x8 := sp + 8`.
It does not follow the AAPCS64 (it writes its caller's frame, through the
caller's `SP` and `x29`), so its contract is the exact final state. Its only
precondition: `SP` is 16-byte aligned (the `str` uses `SP` as base).
-/

namespace Examples.Cedar.NoPanic.Fn.Outlined0
open M1 Examples.Cedar.NoPanic

theorem spec (p : Program) (hp : p.Extends prog) :
    SafeSpec p Panic sym_fn (fun s => s.sp &&& 15#64 = 0#64)
      (fun s s' => s' = { s with
        gpr := upd s.gpr 8 (s.sp + 8#64),
        mem := (s.mem.write64 (s.sp + 0x18#64) (s.gpr 29 - 1#64)).write64
          (s.gpr 29 - 0x10#64) (s.sp + 8#64),
        pc := s.gpr 30 }) := by
  intro n s hpc hst hal
  simp only [sym_fn] at hpc
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  m1_safe_step
  apply SafeN.done
  refine ⟨rfl, rfl, ?_⟩
  rw [upd_upd_same, show s.gpr 29#5 + 0xfffffffffffffff0#64 = s.gpr 29#5 - 0x10#64 by bv_decide]

end Examples.Cedar.NoPanic.Fn.Outlined0
