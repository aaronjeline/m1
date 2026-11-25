/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvMs4_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growB7_`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.FinishGrow
open M1

def textBase : BitVec 64 := 0x348eac#64

def text : List (BitVec 32) := [
  0xa9be4ff4#32, -- 0x348eac: stp x20, x19, [sp, #-0x20]!
  0xa9017bfd#32, -- 0x348eb0: stp x29, x30, [sp, #0x10]
  0x910043fd#32, -- 0x348eb4: add x29, sp, #0x10
  0xaa0003f4#32, -- 0x348eb8: mov x20, x0
  0xb7f80123#32, -- 0x348ebc: tbnz x3, #0x3f, 0x348ee0 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growB7_+0x34>
  0xaa0303f3#32, -- 0x348ec0: mov x19, x3
  0xb4000161#32, -- 0x348ec4: cbz x1, 0x348ef0 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growB7_+0x44>
  0xaa0203e0#32, -- 0x348ec8: mov x0, x2
  0x52800022#32, -- 0x348ecc: mov w2, #0x1 ; =1
  0xaa1303e3#32, -- 0x348ed0: mov x3, x19
  0x97f37870#32, -- 0x348ed4: bl 0x27094 <hJ03s5DiqP_7___rustc14___rust_realloc>
  0xb5000200#32, -- 0x348ed8: cbnz x0, 0x348f18 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growB7_+0x6c>
  0x1400000b#32, -- 0x348edc: b 0x348f08 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growB7_+0x5c>
  0xd2800013#32, -- 0x348ee0: mov x19, #0x0 ; =0
  0x52800028#32, -- 0x348ee4: mov w8, #0x1 ; =1
  0x52800109#32, -- 0x348ee8: mov w9, #0x8 ; =8
  0x1400000e#32, -- 0x348eec: b 0x348f24 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growB7_+0x78>
  0xb4000133#32, -- 0x348ef0: cbz x19, 0x348f14 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growB7_+0x68>
  0x97f3786a#32, -- 0x348ef4: bl 0x2709c <hJ03s5DiqP_7___rustc35___rust_no_alloc_shim_is_unstable_v2>
  0xaa1303e0#32, -- 0x348ef8: mov x0, x19
  0x52800021#32, -- 0x348efc: mov w1, #0x1 ; =1
  0x97f37863#32, -- 0x348f00: bl 0x2708c <hJ03s5DiqP_7___rustc12___rust_alloc>
  0xb50000a0#32, -- 0x348f04: cbnz x0, 0x348f18 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growB7_+0x6c>
  0x52800028#32, -- 0x348f08: mov w8, #0x1 ; =1
  0xf9000688#32, -- 0x348f0c: str x8, [x20, #0x8]
  0x14000004#32, -- 0x348f10: b 0x348f20 <_NtCs6SjEax68zxx_5alloc7raw_vecNtB5_11RawVecInner11finish_growB7_+0x74>
  0x52800020#32, -- 0x348f14: mov w0, #0x1 ; =1
  0xd2800008#32, -- 0x348f18: mov x8, #0x0 ; =0
  0xf9000680#32, -- 0x348f1c: str x0, [x20, #0x8]
  0x52800209#32, -- 0x348f20: mov w9, #0x10 ; =16
  0xf8296a93#32, -- 0x348f24: str x19, [x20, x9]
  0xf9000288#32, -- 0x348f28: str x8, [x20]
  0xa9417bfd#32, -- 0x348f2c: ldp x29, x30, [sp, #0x10]
  0xa8c24ff4#32, -- 0x348f30: ldp x20, x19, [sp], #0x20
  0xd65f03c0#32  -- 0x348f34: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x348eac#64

/-! Direct-call targets (not part of `prog`). -/
/-- `__RNvCs9hJ03s5DiqP_7___rustc12___rust_alloc` -/
def ext_0 : BitVec 64 := 0x2708c#64
/-- `__RNvCs9hJ03s5DiqP_7___rustc14___rust_realloc` -/
def ext_1 : BitVec 64 := 0x27094#64
/-- `__RNvCs9hJ03s5DiqP_7___rustc35___rust_no_alloc_shim_is_unstable_v2` -/
def ext_2 : BitVec 64 := 0x2709c#64

end Examples.Cedar.NoPanic.Fn.FinishGrow
