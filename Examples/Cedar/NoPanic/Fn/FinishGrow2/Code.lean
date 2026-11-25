/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvMs4_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growCs7iCjQZ9Ydc0_17cedar_policy_core.llvm.13161227911452821267`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.FinishGrow2
open M1

def textBase : BitVec 64 := 0x21d0fc#64

def text : List (BitVec 32) := [
  0xa9bd57f6#32, -- 0x21d0fc: stp x22, x21, [sp, #-0x30]!
  0xa9014ff4#32, -- 0x21d100: stp x20, x19, [sp, #0x10]
  0xa9027bfd#32, -- 0x21d104: stp x29, x30, [sp, #0x20]
  0x910083fd#32, -- 0x21d108: add x29, sp, #0x20
  0xaa0003f3#32, -- 0x21d10c: mov x19, x0
  0xd2800009#32, -- 0x21d110: mov x9, #0x0 ; =0
  0x9bc37cab#32, -- 0x21d114: umulh x11, x5, x3
  0x52800028#32, -- 0x21d118: mov w8, #0x1 ; =1
  0x5280010a#32, -- 0x21d11c: mov w10, #0x8 ; =8
  0xeb0b03ff#32, -- 0x21d120: cmp xzr, x11
  0x540003a1#32, -- 0x21d124: b.ne 0x21d198 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growCs7iCjQZ9Ydc0_17cedar_policy_core+0x9c>
  0xaa0403f5#32, -- 0x21d128: mov x21, x4
  0x9b037cb4#32, -- 0x21d12c: mul x20, x5, x3
  0xd2f0000b#32, -- 0x21d130: mov x11, #-0x8000000000000000 ; =-9223372036854775808
  0xcb04016b#32, -- 0x21d134: sub x11, x11, x4
  0xeb0b029f#32, -- 0x21d138: cmp x20, x11
  0x540002e8#32, -- 0x21d13c: b.hi 0x21d198 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growCs7iCjQZ9Ydc0_17cedar_policy_core+0x9c>
  0xb4000101#32, -- 0x21d140: cbz x1, 0x21d160 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growCs7iCjQZ9Ydc0_17cedar_policy_core+0x64>
  0x9b017ca1#32, -- 0x21d144: mul x1, x5, x1
  0xaa0203e0#32, -- 0x21d148: mov x0, x2
  0xaa1503e2#32, -- 0x21d14c: mov x2, x21
  0xaa1403e3#32, -- 0x21d150: mov x3, x20
  0x97f827d0#32, -- 0x21d154: bl 0x27094 <hJ03s5DiqP_7___rustc14___rust_realloc>
  0xb5000180#32, -- 0x21d158: cbnz x0, 0x21d188 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growCs7iCjQZ9Ydc0_17cedar_policy_core+0x8c>
  0x14000007#32, -- 0x21d15c: b 0x21d178 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growCs7iCjQZ9Ydc0_17cedar_policy_core+0x7c>
  0xb4000134#32, -- 0x21d160: cbz x20, 0x21d184 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growCs7iCjQZ9Ydc0_17cedar_policy_core+0x88>
  0x97f827ce#32, -- 0x21d164: bl 0x2709c <hJ03s5DiqP_7___rustc35___rust_no_alloc_shim_is_unstable_v2>
  0xaa1403e0#32, -- 0x21d168: mov x0, x20
  0xaa1503e1#32, -- 0x21d16c: mov x1, x21
  0x97f827c7#32, -- 0x21d170: bl 0x2708c <hJ03s5DiqP_7___rustc12___rust_alloc>
  0xb50000a0#32, -- 0x21d174: cbnz x0, 0x21d188 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growCs7iCjQZ9Ydc0_17cedar_policy_core+0x8c>
  0xf9000675#32, -- 0x21d178: str x21, [x19, #0x8]
  0x52800028#32, -- 0x21d17c: mov w8, #0x1 ; =1
  0x14000004#32, -- 0x21d180: b 0x21d190 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growCs7iCjQZ9Ydc0_17cedar_policy_core+0x94>
  0xaa1503e0#32, -- 0x21d184: mov x0, x21
  0xd2800008#32, -- 0x21d188: mov x8, #0x0 ; =0
  0xf9000660#32, -- 0x21d18c: str x0, [x19, #0x8]
  0x5280020a#32, -- 0x21d190: mov w10, #0x10 ; =16
  0xaa1403e9#32, -- 0x21d194: mov x9, x20
  0xf82a6a69#32, -- 0x21d198: str x9, [x19, x10]
  0xf9000268#32, -- 0x21d19c: str x8, [x19]
  0xa9427bfd#32, -- 0x21d1a0: ldp x29, x30, [sp, #0x20]
  0xa9414ff4#32, -- 0x21d1a4: ldp x20, x19, [sp, #0x10]
  0xa8c357f6#32, -- 0x21d1a8: ldp x22, x21, [sp], #0x30
  0xd65f03c0#32  -- 0x21d1ac: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x21d0fc#64

/-! Direct-call targets (not part of `prog`). -/
/-- `__RNvCs9hJ03s5DiqP_7___rustc12___rust_alloc` -/
def ext_0 : BitVec 64 := 0x2708c#64
/-- `__RNvCs9hJ03s5DiqP_7___rustc14___rust_realloc` -/
def ext_1 : BitVec 64 := 0x27094#64
/-- `__RNvCs9hJ03s5DiqP_7___rustc35___rust_no_alloc_shim_is_unstable_v2` -/
def ext_2 : BitVec 64 := 0x2709c#64

end Examples.Cedar.NoPanic.Fn.FinishGrow2
