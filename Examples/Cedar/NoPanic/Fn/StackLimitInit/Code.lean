/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RINvMs0_NtNtNtNtCsfiKLhsWjRsE_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCskumHb0IaX0X_4core4cell4CellINtNtB1j_6option6OptionjEEzE16get_or_init_slowNvNvCsid02NQM9GFQ_7stacker11STACK_LIMIT27___rust_std_internal_init_fnEB2A_`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.NoPanic.Fn.StackLimitInit
open M1

def textBase : BitVec 64 := 0x287dec#64

def text : List (BitVec 32) := [
  0x39404008#32, -- 0x287dec: ldrb w8, [x0, #0x10]
  0x37000248#32, -- 0x287df0: tbnz w8, #0x0, 0x287e38 <_NtNtNtNtCsfiKLhsWjRsE_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCskumHb0IaX0X_4core4cell4CellINtNtB1j_6option6OptionjEEzE16get_or_init_slowNvNvCsid02NQM9GFQ_7stacker11STACK_LIMIT27___rust_std_internal_init_fnEB2A_+0x4c>
  0xa9be4ff4#32, -- 0x287df4: stp x20, x19, [sp, #-0x20]!
  0xa9017bfd#32, -- 0x287df8: stp x29, x30, [sp, #0x10]
  0x910043fd#32, -- 0x287dfc: add x29, sp, #0x10
  0xaa0003f4#32, -- 0x287e00: mov x20, x0
  0x94033759#32, -- 0x287e04: bl 0x355b68 <dyld_stub_binder+0x355b68>
  0x9403375b#32, -- 0x287e08: bl 0x355b74 <dyld_stub_binder+0x355b74>
  0xaa0003f3#32, -- 0x287e0c: mov x19, x0
  0x94033756#32, -- 0x287e10: bl 0x355b68 <dyld_stub_binder+0x355b68>
  0x94033752#32, -- 0x287e14: bl 0x355b5c <dyld_stub_binder+0x355b5c>
  0xaa0003e8#32, -- 0x287e18: mov x8, x0
  0xaa1403e0#32, -- 0x287e1c: mov x0, x20
  0xcb080268#32, -- 0x287e20: sub x8, x19, x8
  0x52800029#32, -- 0x287e24: mov w9, #0x1 ; =1
  0xa9002289#32, -- 0x287e28: stp x9, x8, [x20]
  0x39004289#32, -- 0x287e2c: strb w9, [x20, #0x10]
  0xa9417bfd#32, -- 0x287e30: ldp x29, x30, [sp, #0x10]
  0xa8c24ff4#32, -- 0x287e34: ldp x20, x19, [sp], #0x20
  0xd65f03c0#32  -- 0x287e38: ret
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x287dec#64

/-! Direct-call targets (not part of `prog`). -/
/-- `_pthread_get_stacksize_np` -/
def ext_0 : BitVec 64 := 0x355b5c#64
/-- `_pthread_self` -/
def ext_1 : BitVec 64 := 0x355b68#64
/-- `_pthread_get_stackaddr_np` -/
def ext_2 : BitVec 64 := 0x355b74#64

end Examples.Cedar.NoPanic.Fn.StackLimitInit
