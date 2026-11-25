/-
  Machine code extracted by targets/cedar-check/extract-fn.py from the M1
  build of targets/cedar-check (`build-m1.sh`): the function
  `__RNvNtCs1oRiJWPcAiX_12cedar_policy3api15eval_expression`.
  Compiler: rustc 1.97.0 (2d8144b78 2026-07-07)
  DO NOT EDIT: regenerate instead.
-/
import M1

namespace Examples.Cedar.Eval
open M1

def textBase : BitVec 64 := 0x60fb0#64

def text : List (BitVec 32) := [
  0xa9bb6ffc#32, -- 0x60fb0: stp x28, x27, [sp, #-0x50]!
  0xa9015ff8#32, -- 0x60fb4: stp x24, x23, [sp, #0x10]
  0xa90257f6#32, -- 0x60fb8: stp x22, x21, [sp, #0x20]
  0xa9034ff4#32, -- 0x60fbc: stp x20, x19, [sp, #0x30]
  0xa9047bfd#32, -- 0x60fc0: stp x29, x30, [sp, #0x40]
  0x910103fd#32, -- 0x60fc4: add x29, sp, #0x40
  0xd10c03ff#32, -- 0x60fc8: sub sp, sp, #0x300
  0xaa0203f4#32, -- 0x60fcc: mov x20, x2
  0xaa0103f5#32, -- 0x60fd0: mov x21, x1
  0xaa0003f6#32, -- 0x60fd4: mov x22, x0
  0xaa0803f3#32, -- 0x60fd8: mov x19, x8
  0x9105c3f8#32, -- 0x60fdc: add x24, sp, #0x170
  0x9406e8e0#32, -- 0x60fe0: bl 0x21b360 <iCjQZ9Ydc0_17cedar_policy_core10extensionsNtB2_10Extensions13all_available>
  0xaa0003f7#32, -- 0x60fe4: mov x23, x0
  0x9105c3e0#32, -- 0x60fe8: add x0, sp, #0x170
  0xaa1603e1#32, -- 0x60fec: mov x1, x22
  0x940002a0#32, -- 0x60ff0: bl 0x61a70 <iCjQZ9Ydc0_17cedar_policy_core3ast7requestNtB5_7RequestNtNtCskumHb0IaX0X_4core5clone5Clone5clone>
  0x910003e8#32, -- 0x60ff4: mov x8, sp
  0x9105c3e0#32, -- 0x60ff8: add x0, sp, #0x170
  0xaa1503e1#32, -- 0x60ffc: mov x1, x21
  0xaa1703e2#32, -- 0x61000: mov x2, x23
  0x94051b4c#32, -- 0x61004: bl 0x1a7d34 <iCjQZ9Ydc0_17cedar_policy_core9evaluatorNtB4_9Evaluator3new>
  0xb0001ee0#32, -- 0x61008: adrp x0, 0x43e000 <_NtNtNtCsfiKLhsWjRsE_3std12backtrace_rs9symbolize5gimliNtB7_5Cache11with_global14MAPPINGS_CACHE+0x3e8>
  0x91178000#32, -- 0x6100c: add x0, x0, #0x5e0
  0xf9400008#32, -- 0x61010: ldr x8, [x0]
  0xd63f0100#32, -- 0x61014: blr x8
  0x39404008#32, -- 0x61018: ldrb w8, [x0, #0x10]
  0x7100051f#32, -- 0x6101c: cmp w8, #0x1
  0x540009c1#32, -- 0x61020: b.ne 0x61158 <oRiJWPcAiX_12cedar_policy3api15eval_expression+0x1a8>
  0xa9400408#32, -- 0x61024: ldp x8, x1, [x0]
  0x91000509#32, -- 0x61028: add x9, x8, #0x1
  0xf9000009#32, -- 0x6102c: str x9, [x0]
  0x90001c89#32, -- 0x61030: adrp x9, 0x3f1000 <_anon.9eca74fca53a9fcfd6d76f562475c99c.1.llvm.4307364285142747578+0x48>
  0x910fc129#32, -- 0x61034: add x9, x9, #0x3f0
  0xad400520#32, -- 0x61038: ldp q0, q1, [x9]
  0xad3b07a0#32, -- 0x6103c: stp q0, q1, [x29, #-0xa0]
  0xa93807a8#32, -- 0x61040: stp x8, x1, [x29, #-0x80]
  0x910003f5#32, -- 0x61044: mov x21, sp
  0x9105c3e8#32, -- 0x61048: add x8, sp, #0x170
  0x910003e0#32, -- 0x6104c: mov x0, sp
  0xd10283a2#32, -- 0x61050: sub x2, x29, #0xa0
  0xaa1403e1#32, -- 0x61054: mov x1, x20
  0x94051d0b#32, -- 0x61058: bl 0x1a8484 <iCjQZ9Ydc0_17cedar_policy_core9evaluatorNtB4_9Evaluator9interpret>
  0xf940bbe8#32, -- 0x6105c: ldr x8, [sp, #0x170]
  0x3cc08300#32, -- 0x61060: ldur q0, [x24, #0x8]
  0x3cc18301#32, -- 0x61064: ldur q1, [x24, #0x18]
  0xad3987a0#32, -- 0x61068: stp q0, q1, [x29, #-0xd0]
  0x3cc28300#32, -- 0x6106c: ldur q0, [x24, #0x28]
  0x3c9503a0#32, -- 0x61070: stur q0, [x29, #-0xb0]
  0xb100051f#32, -- 0x61074: cmn x8, #0x1
  0x54000320#32, -- 0x61078: b.eq 0x610dc <oRiJWPcAiX_12cedar_policy3api15eval_expression+0x12c>
  0x3cc88300#32, -- 0x6107c: ldur q0, [x24, #0x88]
  0x3c888260#32, -- 0x61080: stur q0, [x19, #0x88]
  0x3cc98300#32, -- 0x61084: ldur q0, [x24, #0x98]
  0x3c898260#32, -- 0x61088: stur q0, [x19, #0x98]
  0x3cca8300#32, -- 0x6108c: ldur q0, [x24, #0xa8]
  0x3c8a8260#32, -- 0x61090: stur q0, [x19, #0xa8]
  0x3ccb8300#32, -- 0x61094: ldur q0, [x24, #0xb8]
  0x3c8b8260#32, -- 0x61098: stur q0, [x19, #0xb8]
  0x3cc48300#32, -- 0x6109c: ldur q0, [x24, #0x48]
  0x3c848260#32, -- 0x610a0: stur q0, [x19, #0x48]
  0x3cc58300#32, -- 0x610a4: ldur q0, [x24, #0x58]
  0x3c858260#32, -- 0x610a8: stur q0, [x19, #0x58]
  0x3cc68300#32, -- 0x610ac: ldur q0, [x24, #0x68]
  0x3c868260#32, -- 0x610b0: stur q0, [x19, #0x68]
  0x3cc78300#32, -- 0x610b4: ldur q0, [x24, #0x78]
  0x3c878260#32, -- 0x610b8: stur q0, [x19, #0x78]
  0x3cc38300#32, -- 0x610bc: ldur q0, [x24, #0x38]
  0x3c838260#32, -- 0x610c0: stur q0, [x19, #0x38]
  0xad7987a0#32, -- 0x610c4: ldp q0, q1, [x29, #-0xd0]
  0x3c808260#32, -- 0x610c8: stur q0, [x19, #0x8]
  0x3c818261#32, -- 0x610cc: stur q1, [x19, #0x18]
  0x3cd503a0#32, -- 0x610d0: ldur q0, [x29, #-0xb0]
  0x3c828260#32, -- 0x610d4: stur q0, [x19, #0x28]
  0x14000009#32, -- 0x610d8: b 0x610fc <oRiJWPcAiX_12cedar_policy3api15eval_expression+0x14c>
  0xad7987a0#32, -- 0x610dc: ldp q0, q1, [x29, #-0xd0]
  0xad3c87a0#32, -- 0x610e0: stp q0, q1, [x29, #-0x70]
  0x3cd503a0#32, -- 0x610e4: ldur q0, [x29, #-0xb0]
  0x3c9b03a0#32, -- 0x610e8: stur q0, [x29, #-0x50]
  0x91002268#32, -- 0x610ec: add x8, x19, #0x8
  0xd101c3a0#32, -- 0x610f0: sub x0, x29, #0x70
  0x9400004f#32, -- 0x610f4: bl 0x61230 <m_NtCs1oRiJWPcAiX_12cedar_policy3apiNtB6_10EvalResultINtNtCskumHb0IaX0X_4core7convert4FromNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast5value5ValueE4from>
  0x92800008#32, -- 0x610f8: mov x8, #-0x1 ; =-1
  0xf9000268#32, -- 0x610fc: str x8, [x19]
  0x9101c2a0#32, -- 0x61100: add x0, x21, #0x70
  0x97fffb46#32, -- 0x61104: bl 0x5fe1c <IaX0X_4core3ptr9drop_glueNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast7request14EntityUIDEntryECs1oRiJWPcAiX_12cedar_policy>
  0x910302a0#32, -- 0x61108: add x0, x21, #0xc0
  0x97fffb44#32, -- 0x6110c: bl 0x5fe1c <IaX0X_4core3ptr9drop_glueNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast7request14EntityUIDEntryECs1oRiJWPcAiX_12cedar_policy>
  0x910442a0#32, -- 0x61110: add x0, x21, #0x110
  0x97fffb42#32, -- 0x61114: bl 0x5fe1c <IaX0X_4core3ptr9drop_glueNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast7request14EntityUIDEntryECs1oRiJWPcAiX_12cedar_policy>
  0xf94003e8#32, -- 0x61118: ldr x8, [sp]
  0xb100091f#32, -- 0x6111c: cmn x8, #0x2
  0x540000a1#32, -- 0x61120: b.ne 0x61134 <oRiJWPcAiX_12cedar_policy3api15eval_expression+0x184>
  0x910003e8#32, -- 0x61124: mov x8, sp
  0x91002100#32, -- 0x61128: add x0, x8, #0x8
  0x97fffae3#32, -- 0x6112c: bl 0x5fcb8 <IaX0X_4core3ptr9drop_glueNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast5value5ValueECs1oRiJWPcAiX_12cedar_policy>
  0x14000003#32, -- 0x61130: b 0x6113c <oRiJWPcAiX_12cedar_policy3api15eval_expression+0x18c>
  0x910003e0#32, -- 0x61134: mov x0, sp
  0x97fff995#32, -- 0x61138: bl 0x5f78c <IaX0X_4core3ptr9drop_glueNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast4expr4ExprECs1oRiJWPcAiX_12cedar_policy>
  0x910c03ff#32, -- 0x6113c: add sp, sp, #0x300
  0xa9447bfd#32, -- 0x61140: ldp x29, x30, [sp, #0x40]
  0xa9434ff4#32, -- 0x61144: ldp x20, x19, [sp, #0x30]
  0xa94257f6#32, -- 0x61148: ldp x22, x21, [sp, #0x20]
  0xa9415ff8#32, -- 0x6114c: ldp x24, x23, [sp, #0x10]
  0xa8c56ffc#32, -- 0x61150: ldp x28, x27, [sp], #0x50
  0xd65f03c0#32, -- 0x61154: ret
  0xaa0003f5#32, -- 0x61158: mov x21, x0
  0x940b63b7#32, -- 0x6115c: bl 0x33a038 <std3sys6random19hashmap_random_keys>
  0xaa0003e8#32, -- 0x61160: mov x8, x0
  0xaa1503e0#32, -- 0x61164: mov x0, x21
  0xf90006a1#32, -- 0x61168: str x1, [x21, #0x8]
  0x52800029#32, -- 0x6116c: mov w9, #0x1 ; =1
  0x390042a9#32, -- 0x61170: strb w9, [x21, #0x10]
  0x17ffffad#32  -- 0x61174: b 0x61028 <oRiJWPcAiX_12cedar_policy3api15eval_expression+0x78>
]

abbrev prog : Program := Program.ofList textBase text

def sym_fn : BitVec 64 := 0x60fb0#64

/-! Direct-call targets (not part of `prog`). -/
/-- `__RINvNtCskumHb0IaX0X_4core3ptr9drop_glueNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast4expr4ExprECs1oRiJWPcAiX_12cedar_policy` -/
def ext_0 : BitVec 64 := 0x5f78c#64
/-- `__RINvNtCskumHb0IaX0X_4core3ptr9drop_glueNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast5value5ValueECs1oRiJWPcAiX_12cedar_policy` -/
def ext_1 : BitVec 64 := 0x5fcb8#64
/-- `__RINvNtCskumHb0IaX0X_4core3ptr9drop_glueNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast7request14EntityUIDEntryECs1oRiJWPcAiX_12cedar_policy` -/
def ext_2 : BitVec 64 := 0x5fe1c#64
/-- `__RNvXs1m_NtCs1oRiJWPcAiX_12cedar_policy3apiNtB6_10EvalResultINtNtCskumHb0IaX0X_4core7convert4FromNtNtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast5value5ValueE4from` -/
def ext_3 : BitVec 64 := 0x61230#64
/-- `__RNvXsf_NtNtCs7iCjQZ9Ydc0_17cedar_policy_core3ast7requestNtB5_7RequestNtNtCskumHb0IaX0X_4core5clone5Clone5clone.llvm.714907334299088634` -/
def ext_4 : BitVec 64 := 0x61a70#64
/-- `__RNvMs_NtCs7iCjQZ9Ydc0_17cedar_policy_core9evaluatorNtB4_9Evaluator3new` -/
def ext_5 : BitVec 64 := 0x1a7d34#64
/-- `__RNvMs_NtCs7iCjQZ9Ydc0_17cedar_policy_core9evaluatorNtB4_9Evaluator9interpret` -/
def ext_6 : BitVec 64 := 0x1a8484#64
/-- `__RNvMNtCs7iCjQZ9Ydc0_17cedar_policy_core10extensionsNtB2_10Extensions13all_available` -/
def ext_7 : BitVec 64 := 0x21b360#64
/-- `__RNvNtNtCsfiKLhsWjRsE_3std3sys6random19hashmap_random_keys` -/
def ext_8 : BitVec 64 := 0x33a038#64

end Examples.Cedar.Eval
