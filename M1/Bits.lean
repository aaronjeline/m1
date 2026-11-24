/-
  Bit-level primitives used by the A64 instruction semantics.

  Names follow the shared pseudocode library of the Arm Architecture Reference
  Manual for A-profile (DDI 0487), e.g. `AddWithCarry`, `DecodeBitMasks`,
  `ConditionHolds`, `ExtendReg`, `ShiftReg`.
-/
import Std.Tactic.BVDecide

namespace M1

/-- The PSTATE condition flags. -/
structure NZCV where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
deriving DecidableEq, Repr, Inhabited

namespace NZCV

/-- Pack as the 4-bit value `N:Z:C:V`. -/
def toBits (f : NZCV) : BitVec 4 :=
  BitVec.ofBool f.n ++ BitVec.ofBool f.z ++ BitVec.ofBool f.c ++ BitVec.ofBool f.v

/-- Unpack a 4-bit `N:Z:C:V` value (as found in the `nzcv` field of CCMP etc). -/
def ofBits (b : BitVec 4) : NZCV :=
  ⟨b.getLsbD 3, b.getLsbD 2, b.getLsbD 1, b.getLsbD 0⟩

def zero : NZCV := ⟨false, false, false, false⟩

end NZCV

/-- `AddWithCarry(x, y, carry_in)` from the Arm pseudocode: returns the
`n`-bit sum and the resulting NZCV flags. The carry is the carry out of bit
`n-1` (computed in `n+1` bits) and V is signed overflow. -/
def addWithCarry {n : Nat} (x y : BitVec n) (carry : Bool) : BitVec n × NZCV :=
  let c : BitVec n := if carry then 1 else 0
  let r := x + y + c
  let wide : BitVec (n + 1) :=
    x.setWidth (n + 1) + y.setWidth (n + 1) + (if carry then 1 else 0)
  let cOut := wide.msb
  let vOut := (x.msb == y.msb) && (r.msb != x.msb)
  (r, ⟨r.msb, r == 0, cOut, vOut⟩)

/-- `ConditionHolds(cond)` from the Arm pseudocode. -/
def conditionHolds (cond : BitVec 4) (f : NZCV) : Bool :=
  let base :=
    match cond.toNat / 2 with
    | 0 => f.z
    | 1 => f.c
    | 2 => f.n
    | 3 => f.v
    | 4 => f.c && !f.z
    | 5 => f.n == f.v
    | 6 => (f.n == f.v) && !f.z
    | _ => true
  if cond.getLsbD 0 && cond != 0b1111#4 then !base else base

/-- Shift type of shifted-register operands (`shift` field). -/
inductive ShiftType where
  | lsl | lsr | asr | ror
deriving DecidableEq, Repr, Inhabited

def ShiftType.ofBits (b : BitVec 2) : ShiftType :=
  match b.toNat with
  | 0 => .lsl
  | 1 => .lsr
  | 2 => .asr
  | _ => .ror

/-- `ShiftReg` applied to a value. -/
def shiftReg {n : Nat} (x : BitVec n) (t : ShiftType) (amount : Nat) : BitVec n :=
  match t with
  | .lsl => x <<< amount
  | .lsr => x >>> amount
  | .asr => x.sshiftRight amount
  | .ror => x.rotateRight amount

/-- `ExtendReg(reg, exttype, shift, N)`: `option` is the 3-bit extend type
(UXTB, UXTH, UXTW, UXTX, SXTB, SXTH, SXTW, SXTX). -/
def extendReg {n : Nat} (x : BitVec 64) (option : BitVec 3) (shift : Nat) : BitVec n :=
  let len : Nat := 8 <<< (option.toNat % 4)
  let signed := option.getLsbD 2
  let v : BitVec n :=
    match len with
    | 8  => if signed then (x.setWidth 8).signExtend n else (x.setWidth 8).setWidth n
    | 16 => if signed then (x.setWidth 16).signExtend n else (x.setWidth 16).setWidth n
    | 32 => if signed then (x.setWidth 32).signExtend n else (x.setWidth 32).setWidth n
    | _  => x.setWidth n
  v <<< shift

/-! ### `DecodeBitMasks`

Computed with natural numbers: it is only ever applied to the (constant)
fields of an instruction word at decode time. -/

/-- Replicate the low `esize` bits of `e` to fill `m` bits. -/
def replicateNat (e esize m : Nat) : Nat :=
  (List.range (m / esize)).foldl (fun acc i => acc ||| (e <<< (i * esize))) 0

/-- Rotate the `esize`-bit value `x` right by `r`. -/
def rorNat (x r esize : Nat) : Nat :=
  ((x >>> r) ||| (x <<< (esize - r))) % 2 ^ esize

/-- `DecodeBitMasks(immN, imms, immr, immediate, M)` returning `(wmask, tmask)`,
or `none` where the pseudocode is UNDEFINED. -/
def decodeBitMasks (immN : Bool) (imms immr : BitVec 6) (immediate : Bool) (m : Nat) :
    Option (BitVec m × BitVec m) :=
  let combined : Nat := (if immN then 64 else 0) + (63 - imms.toNat)
  let len := Nat.log2 combined
  if combined = 0 ∨ len < 1 ∨ m < 2 ^ len then none
  else
    let esize := 2 ^ len
    let levels := esize - 1
    let s := imms.toNat &&& levels
    let r := immr.toNat &&& levels
    if immediate && s == levels then none
    else
      let d := (s + esize - r) % esize
      let welem := 2 ^ (s + 1) - 1
      let telem := 2 ^ (d + 1) - 1
      let wmask := replicateNat (rorNat welem r esize) esize m
      let tmask := replicateNat telem esize m
      some (BitVec.ofNat m wmask, BitVec.ofNat m tmask)

/-! ### Bit counting / reversal -/

/-- Count leading zero bits. -/
def countLeadingZeros {n : Nat} (x : BitVec n) : Nat :=
  go n
where
  go : Nat → Nat
    | 0 => n
    | i + 1 => if x.getLsbD i then n - 1 - i else go i

/-- `CountLeadingSignBits(x)` = `CountLeadingZeroBits(x<N-1:1> EOR x<N-2:0>)`. -/
def countLeadingSignBits {n : Nat} (x : BitVec n) : Nat :=
  countLeadingZeros ((x >>> 1) ^^^ (x &&& BitVec.allOnes n >>> 1)) - 1

/-- Reverse the order of `esize`-bit containers... more precisely: reverse the
bytes within each `csize`-bit container (REV16/REV32/REV64 semantics). -/
def revBytes {n : Nat} (x : BitVec n) (csize : Nat) : BitVec n :=
  let nbytes := csize / 8
  BitVec.ofNat n <| (List.range (n / 8)).foldl
    (fun acc i =>
      let c := i / nbytes
      let j := i % nbytes
      let src := c * nbytes + (nbytes - 1 - j)
      acc ||| (((x.toNat >>> (8 * src)) % 256) <<< (8 * i)))
    0

/-- Sign-extend an immediate field to 64 bits. -/
@[inline] def sext64 {n : Nat} (x : BitVec n) : BitVec 64 := x.signExtend 64

/-- Zero-extend to 64 bits. -/
@[inline] def zext64 {n : Nat} (x : BitVec n) : BitVec 64 := x.setWidth 64

end M1
