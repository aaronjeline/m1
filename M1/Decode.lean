/-
  A64 instruction decoder: 32-bit instruction words to `Instr`.

  The structure follows the encoding index of the Arm ARM (C4.1). Any word that
  is not recognised — whether architecturally UNDEFINED or simply not modelled —
  decodes to `none`, and the machine stops with `Fault.unsupported`.
  Encodings that the architecture calls CONSTRAINED UNPREDICTABLE decode to
  `Instr.unpredictable`, which also stops the machine.
-/
import M1.Instr

namespace M1
namespace Decode

/-- Bits `lo+len-1 : lo` of `w` as a natural number. -/
@[inline] def fld (w : BitVec 32) (lo len : Nat) : Nat := (w.toNat >>> lo) % 2 ^ len
@[inline] def bit (w : BitVec 32) (i : Nat) : Bool := w.getLsbD i
@[inline] def reg (w : BitVec 32) (lo : Nat) : Reg := BitVec.ofNat 5 (fld w lo 5)
/-- Sign-extend the `len`-bit field at `lo`, scaled by `2^scale`, to 64 bits. -/
@[inline] def simm (w : BitVec 32) (lo len scale : Nat) : BitVec 64 :=
  (BitVec.ofNat len (fld w lo len)).signExtend 64 <<< scale

/-- Wrap the decoder for widths: decode bit masks at the datasize, zero
extend to 64. -/
def bitMasks64 (sf immN : Bool) (imms immr : BitVec 6) (immediate : Bool) :
    Option (BitVec 64 × BitVec 64) :=
  if sf then decodeBitMasks immN imms immr immediate 64
  else (decodeBitMasks immN imms immr immediate 32).map
    fun (a, b) => (a.setWidth 64, b.setWidth 64)

/-! ### Data processing — immediate -/

def dpImm (w : BitVec 32) : Option Instr :=
  let sf := bit w 31
  let rd := reg w 0
  let rn := reg w 5
  match fld w 23 3 with
  | 0 | 1 =>
    let imm := (BitVec.ofNat 21 (fld w 5 19 * 4 + fld w 29 2)).signExtend 64
    if sf then some (.pcRel true (imm <<< 12) rd) else some (.pcRel false imm rd)
  | 2 =>
    let imm : BitVec 64 := BitVec.ofNat 64 (fld w 10 12 <<< (if bit w 22 then 12 else 0))
    some (.addSubImm sf (bit w 30) (bit w 29) imm rn rd)
  | 4 =>
    let immN := bit w 22
    if !sf && immN then none else
    let op : LogicOp := match fld w 29 2 with
      | 0 => .and | 1 => .orr | 2 => .eor | _ => .ands
    match bitMasks64 sf immN (BitVec.ofNat 6 (fld w 10 6)) (BitVec.ofNat 6 (fld w 16 6)) true with
    | some (imm, _) => some (.logicImm sf op imm rn rd)
    | none => none
  | 5 =>
    let hw := fld w 21 2
    if !sf && hw ≥ 2 then none else
    let imm16 := BitVec.ofNat 16 (fld w 5 16)
    match fld w 29 2 with
    | 0 => some (.moveWide sf .movn (hw * 16) imm16 rd)
    | 2 => some (.moveWide sf .movz (hw * 16) imm16 rd)
    | 3 => some (.moveWide sf .movk (hw * 16) imm16 rd)
    | _ => none
  | 6 =>
    let immN := bit w 22
    let immr := fld w 16 6
    let imms := fld w 10 6
    if sf && !immN then none else
    if !sf && (immN || immr ≥ 32 || imms ≥ 32) then none else
    let op? : Option BitfieldOp := match fld w 29 2 with
      | 0 => some .sbfm | 1 => some .bfm | 2 => some .ubfm | _ => none
    match op?, bitMasks64 sf immN (BitVec.ofNat 6 imms) (BitVec.ofNat 6 immr) false with
    | some op, some (wmask, tmask) => some (.bitfield sf op immr imms wmask tmask rn rd)
    | _, _ => none
  | 7 =>
    let imms := fld w 10 6
    if fld w 29 2 != 0 || bit w 21 || bit w 22 != sf || (!sf && imms ≥ 32) then none
    else some (.extr sf imms (reg w 16) rn rd)
  | _ => none

/-! ### Branches, exception generating and system instructions -/

def branchSys (w : BitVec 32) : Option Instr :=
  let n := w.toNat
  if n &&& 0x7C000000 == 0x14000000 then
    some (.branch (bit w 31) (simm w 0 26 2))
  else if n &&& 0x7E000000 == 0x34000000 then
    some (.cmpBranch (bit w 31) (bit w 24) (simm w 5 19 2) (reg w 0))
  else if n &&& 0x7E000000 == 0x36000000 then
    some (.testBranch ((if bit w 31 then 32 else 0) + fld w 19 5) (bit w 24) (simm w 5 14 2) (reg w 0))
  else if n &&& 0xFF000010 == 0x54000000 then
    some (.branchCond (BitVec.ofNat 4 (fld w 0 4)) (simm w 5 19 2))
  else if n &&& 0xFFE0001F == 0xD4000001 then
    some (.svc (BitVec.ofNat 16 (fld w 5 16)))
  else if n &&& 0xFFE0001F == 0xD4200000 then
    some (.brk (BitVec.ofNat 16 (fld w 5 16)))
  else if n &&& 0xFFFFF01F == 0xD503201F then
    -- Hints: NOP, YIELD. Other hints (WFE/WFI/SEV, pointer authentication,
    -- BTI, ...) are not modelled.
    match fld w 8 4, fld w 5 3 with
    | 0, 0 => some .nop
    | 0, 1 => some .nop
    | _, _ => none
  else if n &&& 0xFFFFF01F == 0xD503301F then
    -- Barriers: no effect on a single sequential core.
    match fld w 5 3 with
    | 2 => some .clrex
    | 4 | 5 | 6 => some .nop
    | _ => none
  else if n &&& 0xFFFFFFE0 == 0xD53B4200 then
    some (.mrsNZCV (reg w 0))
  else if n &&& 0xFFFFFFE0 == 0xD51B4200 then
    some (.msrNZCV (reg w 0))
  else if n &&& 0xFFFFFFC0 == 0xD53B4400 then
    some (.mrsFP (bit w 5) (reg w 0))
  else if n &&& 0xFFFFFFC0 == 0xD51B4400 then
    some (.msrFP (bit w 5) (reg w 0))
  else if n &&& 0xFFFFFC1F == 0xD61F0000 then
    some (.branchReg .br (reg w 5))
  else if n &&& 0xFFFFFC1F == 0xD63F0000 then
    some (.branchReg .blr (reg w 5))
  else if n &&& 0xFFFFFC1F == 0xD65F0000 then
    some (.branchReg .ret (reg w 5))
  else none

/-! ### Loads and stores -/

/-- Integer `(size, opc)` to the memory operation, per the shared decode of
the "load/store register" classes. -/
def intMemOp (size opc : Nat) : Option MemOp :=
  match opc with
  | 0 => some .store
  | 1 => some .load
  | 2 => if size == 3 then some .prefetch else some .loadSigned64
  | _ => if size == 3 || size == 2 then none else some .loadSigned32

/-- `wback && n == t && n != 31` for loads/stores of general registers. -/
def wbConflict (mode : AddrMode) (op : MemOp) (rn rt : Reg) : Bool :=
  mode != .offset && op != .prefetch && rn == rt && rn != 31

def ldSt (w : BitVec 32) : Option Instr :=
  let n := w.toNat
  let rt := reg w 0
  let rn := reg w 5
  let size := fld w 30 2
  let v := bit w 26
  if n &&& 0x3F000000 == 0x08000000 then
    -- Load/store exclusive, load-acquire/store-release, compare and swap.
    if v then none else
    let bytes := 2 ^ size
    let rs := reg w 16
    let load := bit w 22
    match bit w 23, bit w 21 with
    | false, false =>
      if !load && (rs == rt || (rs == rn && rn != 31)) then some .unpredictable
      else some (.ldstExcl bytes load rs rn rt)
    | true, false => some (.ldstOrdered bytes load rn rt)
    | true, true => if fld w 10 5 == 31 then some (.cas bytes rs rn rt) else none
    | false, true => none
  else if n &&& 0x3F200C00 == 0x19000000 then
    -- LDAPR/STLR (unscaled immediate), FEAT_LRCPC2:
    -- size 011001 opc 0 imm9 00 Rn Rt. The (size, opc) table is the one of
    -- the single-register class, except that size = 3, opc = 2 (PRFM there)
    -- is unallocated.
    let opc := fld w 22 2
    if size == 3 && opc == 2 then none else
    match intMemOp size opc with
    | none => none
    | some op => some (.ldstOrderedImm (2 ^ size) op (simm w 12 9 0) rn rt)
  else if n &&& 0x3B000000 == 0x18000000 then
    -- Load register (literal).
    let off := simm w 5 19 2
    let opc := fld w 30 2
    if v then
      match opc with
      | 0 => some (.vldrLit 4 off rt)
      | 1 => some (.vldrLit 8 off rt)
      | 2 => some (.vldrLit 16 off rt)
      | _ => none
    else
      match opc with
      | 0 => some (.ldrLit 4 .load off rt)
      | 1 => some (.ldrLit 8 .load off rt)
      | 2 => some (.ldrLit 4 .loadSigned64 off rt)
      | _ => some (.ldrLit 8 .prefetch off rt)
  else if n &&& 0x3A000000 == 0x28000000 then
    -- Load/store pair.
    let opc := fld w 30 2
    let load := bit w 22
    let modeBits := fld w 23 2
    let mode : AddrMode := match modeBits with
      | 1 => .post | 3 => .pre | _ => .offset
    let rt2 := reg w 10
    if v then
      if opc == 3 then none else
      let bytes := 2 ^ (2 + opc)
      if load && rt == rt2 then some .unpredictable
      else some (.vldstPair bytes load mode (simm w 15 7 (2 + opc)) rt2 rn rt)
    else
      let shape : Option (Nat × Bool) := match opc with
        | 0 => some (4, false)
        | 1 => if load && modeBits != 0 then some (4, true) else none
        | 2 => some (8, false)
        | _ => none
      match shape with
      | none => none
      | some (bytes, signed) =>
        let scale := if bytes == 8 then 3 else 2
        if load && rt == rt2 then some .unpredictable
        else if mode != .offset && (rt == rn || rt2 == rn) && rn != 31 then some .unpredictable
        else some (.ldstPair bytes load signed mode (simm w 15 7 scale) rt2 rn rt)
  else if n &&& 0x3A000000 == 0x38000000 then
    -- Load/store single register.
    let opc := fld w 22 2
    let unsignedImm := bit w 24
    let kind := fld w 10 2
    if !unsignedImm && bit w 21 && kind == 0 then
      -- Atomic memory operations (FEAT_LSE).
      if v then none else
      let bytes := 2 ^ size
      let rs := reg w 16
      match bit w 15, fld w 12 3 with
      | false, o =>
        let op : AtomicOp := match o with
          | 0 => .add | 1 => .clr | 2 => .eor | 3 => .set
          | 4 => .smax | 5 => .smin | 6 => .umax | _ => .umin
        some (.atomic bytes op rs rn rt)
      | true, 0 => some (.atomic bytes .swp rs rn rt)
      | true, 4 =>
        -- LDAPR: load-acquire RCpc; requires A=1, R=0, Rs=11111.
        if bit w 23 && !bit w 22 && rs == 31 then some (.ldstOrdered bytes true rn rt) else none
      | _, _ => none
    else
    -- Decode operation.
    let regOffset := !unsignedImm && bit w 21 && kind == 2
    if !unsignedImm && bit w 21 && !regOffset then none else
    let mode : AddrMode :=
      if unsignedImm || regOffset then .offset
      else match kind with | 1 => .post | 3 => .pre | _ => .offset
    if v then
      let scale := (opc / 2) * 4 + size
      if scale > 4 then none else
      if !unsignedImm && !regOffset && kind == 2 then none else
      let bytes := 2 ^ scale
      let load := opc % 2 == 1
      if regOffset then
        let option := fld w 13 3
        if option % 4 < 2 then none
        else some (.vldstReg bytes load (BitVec.ofNat 3 option) (if bit w 12 then scale else 0)
          (reg w 16) rn rt)
      else if unsignedImm then
        some (.vldstImm bytes load .offset (BitVec.ofNat 64 (fld w 10 12 <<< scale)) rn rt)
      else
        some (.vldstImm bytes load mode (simm w 12 9 0) rn rt)
    else
      match intMemOp size opc with
      | none => none
      | some op =>
        let bytes := 2 ^ size
        if regOffset then
          let option := fld w 13 3
          if option % 4 < 2 then none
          else some (.ldstReg bytes op (BitVec.ofNat 3 option) (if bit w 12 then size else 0)
            (reg w 16) rn rt)
        else if unsignedImm then
          some (.ldstImm bytes op .offset (BitVec.ofNat 64 (fld w 10 12 <<< size)) rn rt)
        else if op == .prefetch && kind != 0 then none  -- only PRFUM (unscaled)
        else if wbConflict mode op rn rt then some .unpredictable
        else some (.ldstImm bytes op mode (simm w 12 9 0) rn rt)
  else none

/-! ### Data processing — register -/

def dpReg (w : BitVec 32) : Option Instr :=
  let n := w.toNat
  let sf := bit w 31
  let rd := reg w 0
  let rn := reg w 5
  let rm := reg w 16
  let imm6 := fld w 10 6
  if n &&& 0x1F000000 == 0x0A000000 then
    if !sf && imm6 ≥ 32 then none else
    let op : LogicOp := match fld w 29 2 with
      | 0 => .and | 1 => .orr | 2 => .eor | _ => .ands
    some (.logicShift sf op (bit w 21) (ShiftType.ofBits (BitVec.ofNat 2 (fld w 22 2))) imm6 rm rn rd)
  else if n &&& 0x1F200000 == 0x0B000000 then
    if fld w 22 2 == 3 || (!sf && imm6 ≥ 32) then none else
    some (.addSubShift sf (bit w 30) (bit w 29) (ShiftType.ofBits (BitVec.ofNat 2 (fld w 22 2)))
      imm6 rm rn rd)
  else if n &&& 0x1F200000 == 0x0B200000 then
    let imm3 := fld w 10 3
    if fld w 22 2 != 0 || imm3 > 4 then none else
    some (.addSubExt sf (bit w 30) (bit w 29) (BitVec.ofNat 3 (fld w 13 3)) imm3 rm rn rd)
  else if n &&& 0x1FE00000 == 0x1A000000 then
    if imm6 != 0 then none else
    some (.addSubCarry sf (bit w 30) (bit w 29) rm rn rd)
  else if n &&& 0x1FE00000 == 0x1A400000 then
    if !bit w 29 || bit w 10 || bit w 4 then none else
    some (.condCmp sf (bit w 30) (bit w 11) (BitVec.ofNat 64 (fld w 16 5)) rm
      (BitVec.ofNat 4 (fld w 12 4)) (BitVec.ofNat 4 (fld w 0 4)) rn)
  else if n &&& 0x1FE00000 == 0x1A800000 then
    if bit w 29 || bit w 11 then none else
    some (.condSel sf (bit w 30) (bit w 10) (BitVec.ofNat 4 (fld w 12 4)) rm rn rd)
  else if n &&& 0x5FE00000 == 0x5AC00000 then
    if bit w 29 || fld w 16 5 != 0 then none else
    let op? : Option DP1Op := match fld w 10 6, sf with
      | 0, _ => some .rbit
      | 1, _ => some .rev16
      | 2, true => some .rev32
      | 2, false => some .rev
      | 3, true => some .rev
      | 4, _ => some .clz
      | 5, _ => some .cls
      | _, _ => none
    op?.map fun op => .dp1 sf op rn rd
  else if n &&& 0x5FE00000 == 0x1AC00000 then
    if bit w 29 then none else
    let opc := fld w 10 6
    if opc / 8 == 2 then
      -- CRC32 / CRC32C: sf must be set exactly for the 64-bit (X) form.
      let sz := opc % 4
      if sf != (sz == 3) then none
      else some (.crc32 (2 ^ sz) (opc % 8 ≥ 4) rm rn rd)
    else
    let op? : Option DP2Op := match opc with
      | 2 => some .udiv | 3 => some .sdiv
      | 8 => some .lslv | 9 => some .lsrv | 10 => some .asrv | 11 => some .rorv
      | _ => none
    op?.map fun op => .dp2 sf op rm rn rd
  else if n &&& 0x1F000000 == 0x1B000000 then
    if fld w 29 2 != 0 then none else
    let o0 := bit w 15
    let op? : Option DP3Op := match fld w 21 3, o0, sf with
      | 0, false, _ => some .madd
      | 0, true, _ => some .msub
      | 1, false, true => some .smaddl
      | 1, true, true => some .smsubl
      | 2, false, true => some .smulh
      | 5, false, true => some .umaddl
      | 5, true, true => some .umsubl
      | 6, false, true => some .umulh
      | _, _, _ => none
    op?.map fun op => .dp3 sf op rm (reg w 10) rn rd
  else none

/-! ### SIMD and floating point (subset) -/

/-- `AdvSIMDExpandImm(op, cmode, imm8)`. -/
def advSIMDExpandImm (op : Bool) (cmode : Nat) (imm8 : Nat) : Option (BitVec 64) :=
  let rep2 (x : Nat) : BitVec 64 := BitVec.ofNat 64 (x ||| (x <<< 32))
  let rep4 (x : Nat) : BitVec 64 := BitVec.ofNat 64 (replicateNat x 16 64)
  let b (i : Nat) : Nat := (imm8 >>> i) % 2
  match cmode / 2 with
  | 0 => some (rep2 imm8)
  | 1 => some (rep2 (imm8 <<< 8))
  | 2 => some (rep2 (imm8 <<< 16))
  | 3 => some (rep2 (imm8 <<< 24))
  | 4 => some (rep4 imm8)
  | 5 => some (rep4 (imm8 <<< 8))
  | 6 => if cmode % 2 == 0 then some (rep2 ((imm8 <<< 8) ||| 0xFF))
         else some (rep2 ((imm8 <<< 16) ||| 0xFFFF))
  | _ =>
    match cmode % 2, op with
    | 0, false => some (BitVec.ofNat 64 (replicateNat imm8 8 64))
    | 0, true => some (BitVec.ofNat 64
        ((List.range 8).foldl (fun acc i => acc ||| ((b i * 0xFF) <<< (8 * i))) 0))
    | _, false =>
      let imm32 := (b 7 <<< 31) ||| ((1 - b 6) <<< 30) ||| ((b 6 * 0x1F) <<< 25) |||
        ((imm8 % 64) <<< 19)
      some (rep2 imm32)
    | _, true =>
      let imm64 := (b 7 <<< 63) ||| ((1 - b 6) <<< 62) ||| ((b 6 * 0xFF) <<< 54) |||
        ((imm8 % 64) <<< 48)
      some (BitVec.ofNat 64 imm64)


/-- Further Advanced SIMD classes: two-register misc, across lanes, permute,
EXT, TBL, shift by immediate, three different, dot product, structure
loads/stores; and CRC32 (data processing, 2 source). -/
def simd2 (w : BitVec 32) : Option Instr :=
  let n := w.toNat
  let rd := reg w 0
  let rn := reg w 5
  let rm := reg w 16
  let q := bit w 30
  let u := bit w 29
  let size := fld w 22 2
  let esize := 8 <<< size
  if n &&& 0xBF20F400 == 0x2E008400 then
    -- Three same extra: SQRDMLAH / SQRDMLSH.
    if size == 1 || size == 2 then
      some (.vec3 q esize (if bit w 11 then .sqrdmlsh else .sqrdmlah) rm rn rd)
    else none
  else if n &&& 0x9F3E0C00 == 0x0E200800 then
    -- Two-register miscellaneous.
    let notD := !(size == 3 && !q)
    let mk (op : Vec2Op) (ok : Bool) (es : Nat := esize) : Option Instr :=
      if ok then some (.vec2 q es op rn rd) else none
    match fld w 12 5, u with
    | 0x00, false => mk .rev64 (size != 3)
    | 0x01, false => mk .rev16 (size == 0)
    | 0x00, true => mk .rev32 (size ≤ 1)
    | 0x05, false => mk .cnt (size == 0)
    | 0x05, true => if size == 0 then mk .not true else if size == 1 then mk .rbit true 8 else none
    | 0x04, false => mk .cls (size != 3)
    | 0x04, true => mk .clz (size != 3)
    | 0x0B, false => mk .abs notD
    | 0x0B, true => mk .neg notD
    | 0x08, false => mk .cmgt0 notD
    | 0x09, false => mk .cmeq0 notD
    | 0x0A, false => mk .cmlt0 notD
    | 0x08, true => mk .cmge0 notD
    | 0x09, true => mk .cmle0 notD
    | 0x12, false => mk .xtn (size != 3)
    | 0x02, false => mk .saddlp (size != 3)
    | 0x02, true => mk .uaddlp (size != 3)
    | 0x06, false => mk .sadalp (size != 3)
    | 0x06, true => mk .uadalp (size != 3)
    | 0x14, false => mk .sqxtn (size != 3)
    | 0x14, true => mk .uqxtn (size != 3)
    | 0x12, true => mk .sqxtun (size != 3)
    | 0x13, true => mk .shll (size != 3)
    | 0x07, false => mk .sqabs notD
    | 0x07, true => mk .sqneg notD
    | 0x03, false => mk .suqadd notD
    | 0x03, true => mk .usqadd notD
    | _, _ => none
  else if n &&& 0x9F3E0C00 == 0x0E300800 then
    -- Across lanes.
    if size == 3 || (size == 2 && !q) then none else
    let mk (op : VecRedOp) : Option Instr := some (.vreduce q esize op rn rd)
    match fld w 12 5, u with
    | 0x03, false => mk .saddlv
    | 0x03, true => mk .uaddlv
    | 0x0A, false => mk .smaxv
    | 0x0A, true => mk .umaxv
    | 0x1A, false => mk .sminv
    | 0x1A, true => mk .uminv
    | 0x1B, false => mk .addv
    | _, _ => none
  else if n &&& 0xFFFFFC00 == 0x5EF1B800 then
    some (.addpScalar rn rd)
  else if n &&& 0xBF208C00 == 0x0E000800 then
    -- Permute.
    if size == 3 && !q then none else
    let op? : Option VecPermOp := match fld w 12 3 with
      | 1 => some .uzp1 | 2 => some .trn1 | 3 => some .zip1
      | 5 => some .uzp2 | 6 => some .trn2 | 7 => some .zip2 | _ => none
    op?.map fun op => .vperm q esize op rm rn rd
  else if n &&& 0xBFE08400 == 0x2E000000 then
    let imm4 := fld w 11 4
    if !q && imm4 ≥ 8 then none else some (.vext q imm4 rm rn rd)
  else if n &&& 0xBFE08C00 == 0x0E000000 then
    some (.vtbl q (fld w 13 2 + 1) (bit w 12) rm rn rd)
  else if n &&& 0xDFC00400 == 0x5F400400 then
    -- Scalar shift by immediate, 64-bit forms (immh = 1xxx): the one-lane
    -- `.1D` vector computation, which zeroes the upper half as required.
    let immhb := fld w 16 7
    let rshift := 128 - immhb
    let lshift := immhb - 64
    let mk (op : VecShiftOp) (sh : Nat) : Option Instr := some (.vshift false 64 op sh rn rd)
    match fld w 11 5, u with
    | 0x00, false => mk .sshr rshift | 0x00, true => mk .ushr rshift
    | 0x02, false => mk .ssra rshift | 0x02, true => mk .usra rshift
    | 0x04, false => mk .srshr rshift | 0x04, true => mk .urshr rshift
    | 0x06, false => mk .srsra rshift | 0x06, true => mk .ursra rshift
    | 0x08, true => mk .sri rshift
    | 0x0A, false => mk .shl lshift | 0x0A, true => mk .sli lshift
    | 0x0C, true => mk .sqshlu lshift
    | 0x0E, false => mk .sqshl lshift | 0x0E, true => mk .uqshl lshift
    | 0x1C, sg => some (.fvec2 false true 64 (.cvtfFix (!sg) rshift) rn rd)
    | 0x1F, sg => some (.fvec2 false true 64 (.fcvtFix (!sg) rshift) rn rd)
    | _, _ => none
  else if n &&& 0x9F800400 == 0x0F000400 && fld w 19 4 != 0 then
    -- Shift by immediate.
    let immh := fld w 19 4
    let immhb := fld w 16 7
    let hsb := Nat.log2 immh
    let es := 8 <<< hsb
    let rshift := 2 * es - immhb
    let lshift := immhb - es
    let full := !(immh ≥ 8 && !q)
    let mk (op : VecShiftOp) (sh : Nat) (ok : Bool) : Option Instr :=
      if ok then some (.vshift q es op sh rn rd) else none
    match fld w 11 5, u with
    | 0x00, false => mk .sshr rshift full
    | 0x00, true => mk .ushr rshift full
    | 0x02, false => mk .ssra rshift full
    | 0x02, true => mk .usra rshift full
    | 0x0A, false => mk .shl lshift full
    | 0x0A, true => mk .sli lshift full
    | 0x08, true => mk .sri rshift full
    | 0x14, false => mk .sshll lshift (immh < 8)
    | 0x14, true => mk .ushll lshift (immh < 8)
    | 0x10, false => mk .shrn rshift (immh < 8)
    | 0x04, false => mk .srshr rshift full
    | 0x04, true => mk .urshr rshift full
    | 0x06, false => mk .srsra rshift full
    | 0x06, true => mk .ursra rshift full
    | 0x0C, true => mk .sqshlu lshift full
    | 0x0E, false => mk .sqshl lshift full
    | 0x0E, true => mk .uqshl lshift full
    | 0x11, false => mk .rshrn rshift (immh < 8)
    | 0x12, false => mk .sqshrn rshift (immh < 8)
    | 0x12, true => mk .uqshrn rshift (immh < 8)
    | 0x13, false => mk .sqrshrn rshift (immh < 8)
    | 0x13, true => mk .uqrshrn rshift (immh < 8)
    | 0x10, true => mk .sqshrun rshift (immh < 8)
    | 0x11, true => mk .sqrshrun rshift (immh < 8)
    | 0x1C, sg => if es ≥ 16 && full then some (.fvec2 q false es (.cvtfFix (!sg) rshift) rn rd) else none
    | 0x1F, sg => if es ≥ 16 && full then some (.fvec2 q false es (.fcvtFix (!sg) rshift) rn rd) else none
    | _, _ => none
  else if n &&& 0x9F200C00 == 0x0E200000 then
    -- Three different.
    if fld w 12 4 == 0xE && !u && (size == 0 || size == 3) then
      some (.pmull q (size == 3) rm rn rd) else
    if size == 3 then none else
    let mk (op : VecLongOp) : Option Instr := some (.vlong q esize op rm rn rd)
    match fld w 12 4, u with
    | 0x0, false => mk .saddl | 0x0, true => mk .uaddl
    | 0x1, false => mk .saddw | 0x1, true => mk .uaddw
    | 0x2, false => mk .ssubl | 0x2, true => mk .usubl
    | 0x3, false => mk .ssubw | 0x3, true => mk .usubw
    | 0x8, false => mk .smlal | 0x8, true => mk .umlal
    | 0xA, false => mk .smlsl | 0xA, true => mk .umlsl
    | 0xC, false => mk .smull | 0xC, true => mk .umull
    | 0x5, false => mk .sabal | 0x5, true => mk .uabal
    | 0x7, false => mk .sabdl | 0x7, true => mk .uabdl
    | 0x4, false => mk .addhn | 0x4, true => mk .raddhn
    | 0x6, false => mk .subhn | 0x6, true => mk .rsubhn
    | 0x9, false => if size == 1 || size == 2 then mk .sqdmlal else none
    | 0xB, false => if size == 1 || size == 2 then mk .sqdmlsl else none
    | 0xD, false => if size == 1 || size == 2 then mk .sqdmull else none
    | _, _ => none
  else if n &&& 0x9F000400 == 0x0F000000 && (size == 1 || size == 2) then
    -- Vector x indexed element (integer).
    let h := if bit w 11 then 1 else 0
    let l := if bit w 21 then 1 else 0
    let mBit := if bit w 20 then 1 else 0
    let (index, rmE) := if size == 1 then (4 * h + 2 * l + mBit, reg w 16 &&& 15)
      else (2 * h + l, rm)
    let mk (op : VecElemOp) : Option Instr := some (.velem q esize op index rmE rn rd)
    match fld w 12 4, u with
    | 0x8, false => mk .mul
    | 0x0, true => mk .mla
    | 0x4, true => mk .mls
    | 0xC, false => mk .sqdmulh
    | 0xD, false => mk .sqrdmulh
    | 0xA, false => mk .smull | 0xA, true => mk .umull
    | 0x2, false => mk .smlal | 0x2, true => mk .umlal
    | 0x6, false => mk .smlsl | 0x6, true => mk .umlsl
    | 0x3, false => mk .sqdmlal | 0x7, false => mk .sqdmlsl | 0xB, false => mk .sqdmull
    | 0xD, true => mk .sqrdmlah | 0xF, true => mk .sqrdmlsh
    | _, _ => none
  else if n &&& 0x9FE0FC00 == 0x0E809400 then
    some (.vdot q (!u) rm rn rd)
  else if n &&& 0xBFBF0000 == 0x0C000000 || n &&& 0xBFA00000 == 0x0C800000 then
    -- Load/store multiple structures (size is in bits 11:10 here).
    let size := fld w 10 2
    let esize := 8 <<< size
    let wback := bit w 23
    let shape : Option (Nat × Nat) := match fld w 12 4 with
      | 0x0 => some (1, 4) | 0x2 => some (4, 1) | 0x4 => some (1, 3) | 0x6 => some (3, 1)
      | 0x7 => some (1, 1) | 0x8 => some (1, 2) | 0xA => some (2, 1) | _ => none
    match shape with
    | none => none
    | some (rpt, selem) =>
      if size == 3 && !q && selem > 1 then none
      else some (.vldstMulti q esize (bit w 22) rpt selem wback (if wback then rm else 31) rn rd)
  else if n &&& 0xBF9F0000 == 0x0D000000 || n &&& 0xBF800000 == 0x0D800000 then
    -- Load/store single structure: LD1-LD4 / ST1-ST4 (one lane), LD1R-LD4R.
    let size := fld w 10 2
    let esize := 8 <<< size
    let wback := bit w 23
    let load := bit w 22
    let sBit := if bit w 12 then 1 else 0
    let qBit := if q then 1 else 0
    let rmw := if wback then rm else 31
    let selem := (if bit w 13 then 2 else 0) + (if bit w 21 then 1 else 0) + 1
    match fld w 14 2 with
    | 3 => if !load || sBit == 1 then none
           else some (.vldstLane q true true selem esize 0 wback rmw rn rd)
    | 0 => some (.vldstLane q load false selem 8 (qBit * 8 + sBit * 4 + size) wback rmw rn rd)
    | 1 => if size % 2 == 1 then none
           else some (.vldstLane q load false selem 16 (qBit * 4 + sBit * 2 + size / 2) wback rmw rn rd)
    | _ =>
      if size ≥ 2 then none
      else if size == 0 then some (.vldstLane q load false selem 32 (qBit * 2 + sBit) wback rmw rn rd)
      else if sBit == 1 then none
      else some (.vldstLane q load false selem 64 qBit wback rmw rn rd)
  else none


/-- Cryptographic extensions. -/
def cryptoDec (w : BitVec 32) : Option Instr :=
  let n := w.toNat
  let rd := reg w 0
  let rn := reg w 5
  let rm := reg w 16
  let mk (op : CryptoOp) : Option Instr := some (.crypto op rm rn rd)
  if n &&& 0xFFFFCC00 == 0x4E284800 then
    match fld w 12 2 with
    | 0 => mk .aese | 1 => mk .aesd | 2 => mk .aesmc | _ => mk .aesimc
  else if n &&& 0xFFE08C00 == 0x5E000000 then
    match fld w 12 3 with
    | 0 => mk .sha1c | 1 => mk .sha1p | 2 => mk .sha1m | 3 => mk .sha1su0
    | 4 => mk .sha256h | 5 => mk .sha256h2 | 6 => mk .sha256su1 | _ => none
  else if n &&& 0xFFFFCC00 == 0x5E280800 then
    match fld w 12 2 with
    | 0 => mk .sha1h | 1 => mk .sha1su1 | 2 => mk .sha256su0 | _ => none
  else if n &&& 0xFFE0F000 == 0xCE608000 then
    match fld w 10 2 with
    | 0 => mk .sha512h | 1 => mk .sha512h2 | 2 => mk .sha512su1 | _ => mk .rax1
  else if n &&& 0xFFFFFC00 == 0xCEC08000 then mk .sha512su0
  else if n &&& 0xFFE08000 == 0xCE000000 then some (.eor3 false rm (reg w 10) rn rd)
  else if n &&& 0xFFE08000 == 0xCE200000 then some (.eor3 true rm (reg w 10) rn rd)
  else if n &&& 0xFFE00000 == 0xCE800000 then some (.xar (fld w 10 6) rm rn rd)
  else none

/-- Scalar floating point (single and double precision only). -/
def fpScalar (w : BitVec 32) : Option Instr :=
  let n := w.toNat
  let rd := reg w 0
  let rn := reg w 5
  let rm := reg w 16
  let ftype := fld w 22 2
  let fsize := if ftype == 0 then 32 else if ftype == 1 then 64 else 16
  let cond := BitVec.ofNat 4 (fld w 12 4)
  if n &&& 0x5F000000 != 0x1E000000 || ftype == 2 then
    -- Not scalar FP, or reserved type.
    if n &&& 0xFF000000 == 0x1F000000 && ftype != 2 then
      some (.fp3 fsize (bit w 21) (bit w 15) (reg w 10) rm rn rd)
    else none
  else if n &&& 0xFF207C00 == 0x1E204000 then
    -- Data-processing (1 source).
    let mk (op : FP1Op) : Option Instr := some (.fp1 fsize op rn rd)
    match fld w 15 6 with
    | 0 => mk .fmov | 1 => mk .fabs | 2 => mk .fneg | 3 => mk .fsqrt
    | 4 => if ftype != 0 then mk (.fcvt 32) else none
    | 5 => if ftype != 1 then mk (.fcvt 64) else none
    | 7 => if ftype != 3 then mk (.fcvt 16) else none
    | 8 => mk (.frint .n) | 9 => mk (.frint .p) | 10 => mk (.frint .m)
    | 11 => mk (.frint .z) | 12 => mk (.frint .a) | 14 => mk .frintx | 15 => mk .frinti
    | 16 => if ftype < 2 then mk (.frintN false 32) else none
    | 17 => if ftype < 2 then mk (.frintN true 32) else none
    | 18 => if ftype < 2 then mk (.frintN false 64) else none
    | 19 => if ftype < 2 then mk (.frintN true 64) else none
    | _ => none
  else if n &&& 0xFF20FC07 == 0x1E202000 then
    -- Compare (the Rm field of the #0.0 forms is ignored, as on the M1).
    some (.fcmp fsize (bit w 4) (bit w 3) rm rn)
  else if n &&& 0xFF201FE0 == 0x1E201000 then
    some (.fmovImm fsize (fld w 13 8) rd)
  else if n &&& 0xFF200C00 == 0x1E200400 then
    some (.fccmp fsize (bit w 4) cond (BitVec.ofNat 4 (fld w 0 4)) rm rn)
  else if n &&& 0xFF200C00 == 0x1E200800 then
    let op? : Option FP2Op := match fld w 12 4 with
      | 0 => some .fmul | 1 => some .fdiv | 2 => some .fadd | 3 => some .fsub
      | 4 => some .fmax | 5 => some .fmin | 6 => some .fmaxnm | 7 => some .fminnm
      | 8 => some .fnmul | _ => none
    op?.map fun op => .fp2 fsize op rm rn rd
  else if n &&& 0xFF200C00 == 0x1E200C00 then
    some (.fcsel fsize cond rm rn rd)
  else if n &&& 0x7F20FC00 == 0x1E200000 then
    -- Conversion between floating point and integer.
    let sf := bit w 31
    let rmode := fld w 19 2
    let opc := fld w 16 3
    let mode : FP.Rounding := match rmode with | 0 => .n | 1 => .p | 2 => .m | _ => .z
    match opc with
    | 0 => some (.fcvtToInt sf fsize true mode 0 rn rd)
    | 1 => some (.fcvtToInt sf fsize false mode 0 rn rd)
    | 2 => if rmode == 0 then some (.intToFP sf fsize true 0 rn rd) else none
    | 3 => if rmode == 0 then some (.intToFP sf fsize false 0 rn rd) else none
    | 4 => if rmode == 0 then some (.fcvtToInt sf fsize true .a 0 rn rd) else none
    | 5 => if rmode == 0 then some (.fcvtToInt sf fsize false .a 0 rn rd) else none
    | 6 => if rmode == 3 && !sf && ftype == 1 then some (.fjcvtzs rn rd) else none
    | _ => none  -- FMOV (general): handled by `simd`
  else if n &&& 0x7F200000 == 0x1E000000 then
    -- Conversion between floating point and fixed point.
    let sf := bit w 31
    let scale := fld w 10 6
    let fb := 64 - scale
    if !sf && scale < 32 then none else
    match fld w 19 2, fld w 16 3 with
    | 0, 2 => some (.intToFP sf fsize true fb rn rd)
    | 0, 3 => some (.intToFP sf fsize false fb rn rd)
    | 3, 0 => some (.fcvtToInt sf fsize true .z fb rn rd)
    | 3, 1 => some (.fcvtToInt sf fsize false .z fb rn rd)
    | _, _ => none
  else none

/-- Advanced SIMD scalar integer instructions (three same, two-register misc,
shift by immediate, three different, by element): each is the corresponding
one-lane vector instruction (see `Instr.scalar`). -/
def scalarInt (w : BitVec 32) : Option Instr :=
  let n := w.toNat
  let rd := reg w 0
  let rn := reg w 5
  let rm := reg w 16
  let u := bit w 29
  let size := fld w 22 2
  let esize := 8 <<< size
  let wrap (bits : Nat) (i : Instr) : Option Instr := some (.scalar bits rd i)
  if n &&& 0xDF200400 == 0x5E200400 then
    -- Scalar three same.
    let mk (op : VecOp) (ok : Bool) : Option Instr :=
      if ok then wrap esize (.vec3 false esize op rm rn rd) else none
    let d := size == 3
    match fld w 11 5, u with
    | 0x01, false => mk .sqadd true | 0x01, true => mk .uqadd true
    | 0x05, false => mk .sqsub true | 0x05, true => mk .uqsub true
    | 0x09, false => mk .sqshl true | 0x09, true => mk .uqshl true
    | 0x0B, false => mk .sqrshl true | 0x0B, true => mk .uqrshl true
    | 0x06, false => mk .cmgt d | 0x06, true => mk .cmhi d
    | 0x07, false => mk .cmge d | 0x07, true => mk .cmhs d
    | 0x08, false => mk .sshl d | 0x08, true => mk .ushl d
    | 0x0A, false => mk .srshl d | 0x0A, true => mk .urshl d
    | 0x10, false => mk .add d | 0x10, true => mk .sub d
    | 0x11, false => mk .cmtst d | 0x11, true => mk .cmeq d
    | 0x16, false => mk .sqdmulh (size == 1 || size == 2)
    | 0x16, true => mk .sqrdmulh (size == 1 || size == 2)
    | _, _ => none
  else if n &&& 0xFF20F400 == 0x7E008400 && (size == 1 || size == 2) then
    -- Scalar three same extra: SQRDMLAH / SQRDMLSH.
    wrap esize (.vec3 false esize (if bit w 11 then .sqrdmlsh else .sqrdmlah) rm rn rd)
  else if n &&& 0xDF3E0C00 == 0x5E200800 then
    -- Scalar two-register miscellaneous.
    let mk (op : Vec2Op) (ok : Bool) : Option Instr :=
      if ok then wrap esize (.vec2 false esize op rn rd) else none
    let d := size == 3
    match fld w 12 5, u with
    | 0x03, false => mk .suqadd true | 0x03, true => mk .usqadd true
    | 0x07, false => mk .sqabs true | 0x07, true => mk .sqneg true
    | 0x08, false => mk .cmgt0 d | 0x08, true => mk .cmge0 d
    | 0x09, false => mk .cmeq0 d | 0x09, true => mk .cmle0 d
    | 0x0A, false => mk .cmlt0 d
    | 0x0B, false => mk .abs d | 0x0B, true => mk .neg d
    | 0x14, false => mk .sqxtn (size != 3) | 0x14, true => mk .uqxtn (size != 3)
    | 0x12, true => mk .sqxtun (size != 3)
    | _, _ => none
  else if n &&& 0xDF800400 == 0x5F000400 && fld w 19 4 != 0 && fld w 19 4 < 8 then
    -- Scalar shift by immediate, 8-32-bit elements (64-bit: see `simd2`).
    let immh := fld w 19 4
    let immhb := fld w 16 7
    let es := 8 <<< Nat.log2 immh
    let rshift := 2 * es - immhb
    let lshift := immhb - es
    let mk (op : VecShiftOp) (sh : Nat) : Option Instr := wrap es (.vshift false es op sh rn rd)
    match fld w 11 5, u with
    | 0x0C, true => mk .sqshlu lshift
    | 0x0E, false => mk .sqshl lshift | 0x0E, true => mk .uqshl lshift
    | 0x12, false => mk .sqshrn rshift | 0x12, true => mk .uqshrn rshift
    | 0x13, false => mk .sqrshrn rshift | 0x13, true => mk .uqrshrn rshift
    | 0x10, true => mk .sqshrun rshift | 0x11, true => mk .sqrshrun rshift
    | 0x1C, sg => if es ≥ 16 then some (.fvec2 false true es (.cvtfFix (!sg) rshift) rn rd) else none
    | 0x1F, sg => if es ≥ 16 then some (.fvec2 false true es (.fcvtFix (!sg) rshift) rn rd) else none
    | _, _ => none
  else if n &&& 0xDF200C00 == 0x5E200000 && !u && (size == 1 || size == 2) then
    -- Scalar three different: SQDMLAL / SQDMLSL / SQDMULL.
    let mk (op : VecLongOp) : Option Instr := wrap (2 * esize) (.vlong false esize op rm rn rd)
    match fld w 12 4 with
    | 0x9 => mk .sqdmlal | 0xB => mk .sqdmlsl | 0xD => mk .sqdmull | _ => none
  else if n &&& 0xDF000400 == 0x5F000000 && (size == 1 || size == 2) then
    -- Scalar by element (integer).
    let h := if bit w 11 then 1 else 0
    let l := if bit w 21 then 1 else 0
    let mBit := if bit w 20 then 1 else 0
    let (index, rmE) := if size == 1 then (4 * h + 2 * l + mBit, reg w 16 &&& 15)
      else (2 * h + l, rm)
    let mk (op : VecElemOp) (bits : Nat) : Option Instr :=
      wrap bits (.velem false esize op index rmE rn rd)
    match fld w 12 4, u with
    | 0xC, false => mk .sqdmulh esize | 0xD, false => mk .sqrdmulh esize
    | 0xD, true => mk .sqrdmlah esize | 0xF, true => mk .sqrdmlsh esize
    | 0x3, false => mk .sqdmlal (2 * esize) | 0x7, false => mk .sqdmlsl (2 * esize)
    | 0xB, false => mk .sqdmull (2 * esize)
    | _, _ => none
  else none

/-- Advanced SIMD floating point (single and double precision), and the
scalar `DUP` (element). -/
def simdFP (w : BitVec 32) : Option Instr :=
  let n := w.toNat
  let rd := reg w 0
  let rn := reg w 5
  let rm := reg w 16
  let q := bit w 30
  let u := bit w 29
  let a := bit w 23
  let sz := bit w 22
  let N := if sz then 64 else 32
  let okQ := !(sz && !q)
  -- FP16 forms reuse the single/double operation tables.
  let h3 := n &&& 0x9F60C400 == 0x0E400400
  let h2 := n &&& 0x9F7E0C00 == 0x0E780800 || n &&& 0xDF7E0C00 == 0x5E780800
  let N := if h3 || h2 then 16 else N
  let okQ := okQ || h3 || h2
  let fp3op (o : Nat) (u a : Bool) : Option FVecOp := match o, u, a with
      | 0, false, false => some .fmaxnm | 0, false, true => some .fminnm
      | 0, true, false => some .fmaxnmp | 0, true, true => some .fminnmp
      | 1, false, false => some .fmla | 1, false, true => some .fmls
      | 2, false, false => some .fadd | 2, false, true => some .fsub
      | 2, true, false => some .faddp | 2, true, true => some .fabd
      | 3, false, false => some .fmulx
      | 3, true, false => some .fmul
      | 4, false, false => some .fcmeq | 4, true, false => some .fcmge
      | 4, true, true => some .fcmgt
      | 5, true, false => some .facge | 5, true, true => some .facgt
      | 6, false, false => some .fmax | 6, false, true => some .fmin
      | 6, true, false => some .fmaxp | 6, true, true => some .fminp
      | 7, false, false => some .frecps | 7, false, true => some .frsqrts
      | 7, true, false => some .fdiv
      | _, _, _ => none
  if n &&& 0xDF20C400 == 0x5E20C400 || n &&& 0xDF60C400 == 0x5E400400 then
    -- Scalar three same (floating point).
    let N := if n &&& 0xDF60C400 == 0x5E400400 then 16 else N
    match fp3op (fld w 11 3) u a with
    | some op =>
      if op ∈ [.fmulx, .fcmeq, .frecps, .fcmge, .facge, .frsqrts, .fabd, .fcmgt, .facgt] then
        some (.fscalar3 N op none rm rn rd) else none
    | none => none
  else if n &&& 0xBF20E400 == 0x2E00C400 && fld w 22 2 != 0 then
    let fs := 8 <<< fld w 22 2
    if fs == 64 && !q then none else some (.fcmla q fs (fld w 11 2) rm rn rd)
  else if n &&& 0xBF20EC00 == 0x2E00E400 && fld w 22 2 != 0 then
    let fs := 8 <<< fld w 22 2
    if fs == 64 && !q then none else some (.fcadd q fs (bit w 12) rm rn rd)
  else if n &&& 0x9F60C400 == 0x0E20C400 && fld w 11 3 % 4 == 1 &&
      (u == (fld w 11 3 == 1)) then
    -- FMLAL/FMLSL (vector): `U = 0, opcode 11101` and `U = 1, opcode 11001`.
    some (.fmlal q a u none rm rn rd)
  else if n &&& 0x9FC00400 == 0x0F800000 && fld w 12 2 == 0 && (u == bit w 15) then
    -- FMLAL/FMLSL (by element): opcode 0000/0100 (U = 0), 1000/1100 (U = 1).
    let index := 4 * (if bit w 11 then 1 else 0) + 2 * (if bit w 21 then 1 else 0) +
      (if bit w 20 then 1 else 0)
    some (.fmlal q (bit w 14) u (some index) (reg w 16 &&& 15) rn rd)
  else if n &&& 0x9F20C400 == 0x0E20C400 || h3 then
    -- Three same (floating point).
    if !okQ then none else
    (fp3op (fld w 11 3) u a).map fun op => .fvec3 q N op rm rn rd
  else if n &&& 0x9F3E0C00 == 0x0E200800 || n &&& 0xDF3E0C00 == 0x5E200800 || h2 then
    -- Two-register miscellaneous (vector, or scalar when bit 28 is set).
    let scalar := bit w 28
    let opc := fld w 12 5
    if !scalar && !h2 && opc == 0x16 && !u && !a then
      some (.fcvtnl q true (if sz then 64 else 32) rn rd)
    else if !h2 && opc == 0x16 && u && !a && sz then
      some (.fcvtxn q scalar rn rd)
    else if !scalar && !h2 && opc == 0x17 && !u && !a then
      some (.fcvtnl q false (if sz then 64 else 32) rn rd)
    else
    if !scalar && !okQ then none else
    let op? : Option FVec2Op := match opc, u, a with
      | 0x0C, false, true => some .fcmgt0 | 0x0C, true, true => some .fcmge0
      | 0x0D, false, true => some .fcmeq0 | 0x0D, true, true => some .fcmle0
      | 0x0E, false, true => some .fcmlt0
      | 0x1A, sg, false => some (.fcvt .n !sg) | 0x1A, sg, true => some (.fcvt .p !sg)
      | 0x1B, sg, false => some (.fcvt .m !sg) | 0x1B, sg, true => some (.fcvt .z !sg)
      | 0x1C, sg, false => some (.fcvt .a !sg)
      | 0x1D, sg, false => some (.cvtf !sg)
      | 0x1D, false, true => some .frecpe
      | 0x1D, true, true => some .frsqrte
      | 0x1F, false, true => if scalar then some .frecpx else none
      | 0x1C, false, true => if scalar || sz || h2 then none else some .urecpe
      | 0x1C, true, true => if scalar || sz || h2 then none else some .ursqrte
      | _, _, _ =>
        if scalar then none else
        match opc, u, a with
        | 0x1E, false, false => if h2 then none else some (.frintN false 32)
        | 0x1E, true, false => if h2 then none else some (.frintN true 32)
        | 0x1F, false, false => if h2 then none else some (.frintN false 64)
        | 0x1F, true, false => if h2 then none else some (.frintN true 64)
        | 0x0F, false, true => some .fabs | 0x0F, true, true => some .fneg
        | 0x1F, true, true => some .fsqrt
        | 0x18, false, false => some (.frint .n) | 0x18, true, false => some (.frint .a)
        | 0x18, false, true => some (.frint .p)
        | 0x19, false, false => some (.frint .m) | 0x19, true, false => some .frintx
        | 0x19, false, true => some (.frint .z) | 0x19, true, true => some .frinti
        | _, _, _ => none
    op?.map fun op => .fvec2 q scalar N op rn rd
  else if n &&& 0x9F800400 == 0x0F800000 || n &&& 0xDF800400 == 0x5F800000 then
    -- By element, floating point (size = 1x), vector or scalar.
    let scalar := bit w 28
    let h := if bit w 11 then 1 else 0
    let l := if bit w 21 then 1 else 0
    if (!scalar && !okQ) || (sz && l == 1) then none else
    let index := if sz then h else 2 * h + l
    let op? : Option FVecOp := match fld w 12 4, u with
      | 1, false => some .fmla | 5, false => some .fmls | 9, false => some .fmul
      | 9, true => some .fmulx | _, _ => none
    op?.map fun op =>
      if scalar then .fscalar3 N op (some index) rm rn rd else .fvecElem q N op index rm rn rd
  else if n &&& 0x9FC00400 == 0x0F000000 || n &&& 0xDFC00400 == 0x5F000000 then
    -- By element, half precision (size = 00), vector or scalar.
    let scalar := bit w 28
    let index := 4 * (if bit w 11 then 1 else 0) + 2 * (if bit w 21 then 1 else 0) +
      (if bit w 20 then 1 else 0)
    let rm := reg w 16 &&& 15
    let op? : Option FVecOp := match fld w 12 4, u with
      | 1, false => some .fmla | 5, false => some .fmls | 9, false => some .fmul
      | 9, true => some .fmulx | _, _ => none
    op?.map fun op =>
      if scalar then .fscalar3 16 op (some index) rm rn rd else .fvecElem q 16 op index rm rn rd
  else if n &&& 0xFF7E0C00 == 0x5E300800 then
    -- Scalar pairwise, half precision.
    let op? : Option FRedOp := match fld w 12 5, a with
      | 0x0C, false => some .fmaxnm | 0x0C, true => some .fminnm
      | 0x0D, false => some .fadd
      | 0x0F, false => some .fmax | 0x0F, true => some .fmin
      | _, _ => none
    op?.map fun op => .freduce false true 16 op rn rd
  else if n &&& 0xBF7E0C00 == 0x0E300800 && (fld w 12 5 == 0x0C || fld w 12 5 == 0x0F) then
    -- Across lanes, half precision.
    let op? : Option FRedOp := match fld w 12 5, a with
      | 0x0C, false => some .fmaxnm | 0x0C, true => some .fminnm
      | 0x0F, false => some .fmax | _, _ => some .fmin
    op?.map fun op => .freduce q false 16 op rn rd
  else if n &&& 0xFF3E0C00 == 0x7E300800 then
    -- Scalar pairwise (floating point, U = 1).
    let op? : Option FRedOp := match fld w 12 5, a with
      | 0x0C, false => some .fmaxnm | 0x0C, true => some .fminnm
      | 0x0D, false => some .fadd
      | 0x0F, false => some .fmax | 0x0F, true => some .fmin
      | _, _ => none
    op?.map fun op => .freduce false true N op rn rd
  else if n &&& 0xBF3E0C00 == 0x2E300800 then
    -- Across lanes (floating point): only the .4S form exists.
    if sz || !q then none else
    let op? : Option FRedOp := match fld w 12 5, a with
      | 0x0C, false => some .fmaxnm | 0x0C, true => some .fminnm
      | 0x0F, false => some .fmax | 0x0F, true => some .fmin
      | _, _ => none
    op?.map fun op => .freduce true false 32 op rn rd
  else if n &&& 0xFFE0FC00 == 0x5E000400 then
    -- DUP (element), scalar.
    let imm5 := fld w 16 5
    if imm5 % 2 == 1 then some (.dupScalar 8 (imm5 / 2) rn rd)
    else if imm5 % 4 == 2 then some (.dupScalar 16 (imm5 / 4) rn rd)
    else if imm5 % 8 == 4 then some (.dupScalar 32 (imm5 / 8) rn rd)
    else if imm5 % 16 == 8 then some (.dupScalar 64 (imm5 / 16) rn rd)
    else none
  else none

def simd (w : BitVec 32) : Option Instr :=
  let n := w.toNat
  let rd := reg w 0
  let rn := reg w 5
  let q := bit w 30
  if let some i := fpScalar w then some i
  else if let some i := simdFP w then some i
  else if let some i := cryptoDec w then some i
  else if let some i := scalarInt w then some i
  else if n &&& 0x7FFFFC00 == 0x1EE60000 then some (.fmovGen true 2 false rn rd)
  else if n &&& 0x7FFFFC00 == 0x1EE70000 then some (.fmovGen false 2 false rn rd)
  else if n &&& 0xFFFFFC00 == 0x1E260000 then some (.fmovGen true 4 false rn rd)
  else if n &&& 0xFFFFFC00 == 0x1E270000 then some (.fmovGen false 4 false rn rd)
  else if n &&& 0xFFFFFC00 == 0x9E660000 then some (.fmovGen true 8 false rn rd)
  else if n &&& 0xFFFFFC00 == 0x9E670000 then some (.fmovGen false 8 false rn rd)
  else if n &&& 0xFFFFFC00 == 0x9EAE0000 then some (.fmovGen true 8 true rn rd)
  else if n &&& 0xFFFFFC00 == 0x9EAF0000 then some (.fmovGen false 8 true rn rd)
  else if n &&& 0x9FF80400 == 0x0F000400 then
    -- Advanced SIMD modified immediate.
    if bit w 11 then none else
    let op := bit w 29
    let cmode := fld w 12 4
    let imm8 := (fld w 16 3 <<< 5) ||| fld w 5 5
    if cmode == 15 && op && !q then none else
    match advSIMDExpandImm op cmode imm8 with
    | none => none
    | some imm =>
      if cmode ≥ 12 then
        -- MOVI/MVNI (shifting ones), MOVI (8/64-bit), FMOV (vector, immediate)
        let inv := op && cmode < 14
        some (.vmovImm q 0 (if inv then ~~~imm else imm) rd)
      else if cmode % 2 == 1 then
        some (.vmovImm q (if op then 2 else 1) imm rd)
      else
        some (.vmovImm q 0 (if op then ~~~imm else imm) rd)
  else if n &&& 0x9FE08400 == 0x0E000400 then
    -- Advanced SIMD copy.
    let imm5 := fld w 16 5
    let imm4 := fld w 11 4
    let op := bit w 29
    if imm5 % 16 == 0 then none else
    let size := if imm5 % 2 == 1 then 0 else if imm5 % 4 == 2 then 1
                else if imm5 % 8 == 4 then 2 else 3
    let esize := 8 <<< size
    let index := imm5 >>> (size + 1)
    if op then
      if q then some (.insElem esize index (imm4 >>> size) rn rd) else none
    else match imm4 with
      | 0 => if size == 3 && !q then none else some (.dupElem q esize index rn rd)
      | 1 => if size == 3 && !q then none else some (.dupGen q esize rn rd)
      | 3 => if q then some (.insGen esize index rn rd) else none
      | 5 => if (q && size ≤ 2) || (!q && size ≤ 1) then
               some (.movToGen q true esize index rn rd) else none
      | 7 => if (q && size == 3) || (!q && size ≤ 2) then
               some (.movToGen q false esize index rn rd) else none
      | _ => none
  else if n &&& 0x9F200400 == 0x0E200400 then
    -- Advanced SIMD three same (integer subset).
    let u := bit w 29
    let size := fld w 22 2
    let esize := 8 <<< size
    let rm := reg w 16
    let opcode := fld w 11 5
    let mk (op : VecOp) (ok : Bool) : Option Instr :=
      if ok then some (.vec3 q esize op rm rn rd) else none
    let notD := !(size == 3 && !q)
    match opcode, u with
    | 0x10, false => mk .add notD
    | 0x10, true => mk .sub notD
    | 0x03, false => mk (match size with | 0 => .and | 1 => .bic | 2 => .orr | _ => .orn) true
    | 0x03, true => mk (match size with | 0 => .eor | 1 => .bsl | 2 => .bit | _ => .bif) true
    | 0x11, false => mk .cmtst notD
    | 0x11, true => mk .cmeq notD
    | 0x06, false => mk .cmgt notD
    | 0x06, true => mk .cmhi notD
    | 0x07, false => mk .cmge notD
    | 0x07, true => mk .cmhs notD
    | 0x0C, false => mk .smax (size != 3)
    | 0x0C, true => mk .umax (size != 3)
    | 0x0D, false => mk .smin (size != 3)
    | 0x0D, true => mk .umin (size != 3)
    | 0x13, false => mk .mul (size != 3)
    | 0x17, false => mk .addp notD
    | 0x14, false => mk .smaxp (size != 3)
    | 0x14, true => mk .umaxp (size != 3)
    | 0x15, false => mk .sminp (size != 3)
    | 0x15, true => mk .uminp (size != 3)
    | 0x12, false => mk .mla (size != 3)
    | 0x12, true => mk .mls (size != 3)
    | 0x08, false => mk .sshl notD
    | 0x08, true => mk .ushl notD
    | 0x01, false => mk .sqadd notD
    | 0x01, true => mk .uqadd notD
    | 0x05, false => mk .sqsub notD
    | 0x05, true => mk .uqsub notD
    | 0x00, false => mk .shadd (size != 3)
    | 0x00, true => mk .uhadd (size != 3)
    | 0x02, false => mk .srhadd (size != 3)
    | 0x02, true => mk .urhadd (size != 3)
    | 0x0E, false => mk .sabd (size != 3)
    | 0x0E, true => mk .uabd (size != 3)
    | 0x0A, false => mk .srshl notD
    | 0x0A, true => mk .urshl notD
    | 0x09, false => mk .sqshl notD
    | 0x09, true => mk .uqshl notD
    | 0x0B, false => mk .sqrshl notD
    | 0x0B, true => mk .uqrshl notD
    | 0x16, false => mk .sqdmulh (size == 1 || size == 2)
    | 0x16, true => mk .sqrdmulh (size == 1 || size == 2)
    | _, _ => none
  else simd2 w

end Decode

/-- Decode a 32-bit A64 instruction word. -/
def decode (w : BitVec 32) : Option Instr :=
  let op0 := Decode.fld w 25 4
  if op0 &&& 0b1110 == 0b1000 then Decode.dpImm w
  else if op0 &&& 0b1110 == 0b1010 then Decode.branchSys w
  -- Advanced SIMD load/store multiple/single structures.
  else if w.toNat &&& 0xBE000000 == 0x0C000000 then Decode.simd2 w
  else if op0 &&& 0b0101 == 0b0100 then Decode.ldSt w
  else if op0 &&& 0b0111 == 0b0101 then Decode.dpReg w
  else if op0 &&& 0b0111 == 0b0111 then Decode.simd w
  else none

end M1
