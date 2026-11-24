/-
  Execution semantics of decoded A64 instructions, following the "operation"
  pseudocode of each instruction in the Arm ARM.
-/
import M1.State
import M1.Instr

namespace M1

/-! ### Width helpers -/

/-- Truncate to the datasize (32 bits when `sf = false`) and zero-extend back
to 64 bits — the effect of writing a W register. -/
@[inline] def trunc (sf : Bool) (v : BitVec 64) : BitVec 64 :=
  if sf then v else (v.setWidth 32).setWidth 64

/-- Evaluate a width-generic computation at the datasize and zero-extend. -/
@[inline] def sized (sf : Bool) (f : (n : Nat) → BitVec n) : BitVec 64 :=
  if sf then f 64 else (f 32).setWidth 64

/-- `AddWithCarry` at the datasize, with `sub` inverting the second operand. -/
def addSub (sf sub : Bool) (a b : BitVec 64) (carry : Bool) : BitVec 64 × NZCV :=
  if sf then addWithCarry a (if sub then ~~~b else b) carry
  else
    let r := addWithCarry (a.setWidth 32) (if sub then ~~~(b.setWidth 32) else b.setWidth 32) carry
    (r.1.setWidth 64, r.2)

/-- Flags set by `ANDS`/`BICS`/`TST`. -/
def logicFlags (sf : Bool) (r : BitVec 64) : NZCV :=
  if sf then ⟨r.msb, r == 0, false, false⟩
  else ⟨r.getLsbD 31, r.setWidth 32 == 0, false, false⟩

def logicCompute (op : LogicOp) (a b : BitVec 64) : BitVec 64 :=
  match op with
  | .and | .ands => a &&& b
  | .orr => a ||| b
  | .eor => a ^^^ b

/-- Write the result of a logical operation (`ANDS` sets flags and writes
XZR-style; immediate forms of the others write SP-style when `spDest`). -/
def logicWrite (s : State) (sf : Bool) (op : LogicOp) (r : BitVec 64) (rd : Reg)
    (spDest : Bool) : State :=
  let r := trunc sf r
  match op with
  | .ands => (s.setX rd r).setFlags (logicFlags sf r)
  | _ => if spDest then s.setXSP rd r else s.setX rd r

/-- Sign-extend the low `size` bytes of `v` to 64 bits. -/
def sextBytes (size : Nat) (v : BitVec 64) : BitVec 64 :=
  match size with
  | 1 => (v.setWidth 8).signExtend 64
  | 2 => (v.setWidth 16).signExtend 64
  | 4 => (v.setWidth 32).signExtend 64
  | _ => v

/-- Zero-extend the low `size` bytes of `v` to 64 bits. -/
def zextBytes (size : Nat) (v : BitVec 64) : BitVec 64 :=
  match size with
  | 1 => (v.setWidth 8).setWidth 64
  | 2 => (v.setWidth 16).setWidth 64
  | 4 => (v.setWidth 32).setWidth 64
  | _ => v

/-- Is `a` aligned to `size` bytes (`size` a power of two)? -/
def aligned (a : BitVec 64) (size : Nat) : Bool :=
  a &&& BitVec.ofNat 64 (size - 1) == 0

/-- Alignment rule for load-acquire/store-release, exclusive, atomic and CAS
accesses on the M1 (FEAT_LSE2): the access faults iff it crosses a 16-byte
boundary. (Measured on hardware; see `tools/cosim/align.c`.) -/
def atomicAligned (a : BitVec 64) (size : Nat) : Bool :=
  (a &&& 15).toNat + size ≤ 16

/-! ### Advanced SIMD lanes

Lanes are passed around zero-extended in 64 bits. -/

def laneMask (esize : Nat) : BitVec 128 := BitVec.allOnes 128 >>> (128 - esize)

def getLane (v : BitVec 128) (esize i : Nat) : BitVec 64 :=
  ((v >>> (i * esize)) &&& laneMask esize).setWidth 64

def setLane (v : BitVec 128) (esize i : Nat) (x : BitVec 64) : BitVec 128 :=
  (v &&& ~~~(laneMask esize <<< (i * esize))) |||
    ((x.setWidth 128 &&& laneMask esize) <<< (i * esize))

/-- Sign-extend an `esize`-bit lane (held in 64 bits). -/
def sextLane (esize : Nat) (x : BitVec 64) : BitVec 64 :=
  (x <<< (64 - esize)).sshiftRight (64 - esize)

/-- Build a vector (64 or 128 bits wide, upper half zero when `q = false`)
by computing each lane. -/
def mkVec (q : Bool) (esize : Nat) (f : Nat → BitVec 64) : BitVec 128 :=
  (List.range ((if q then 128 else 64) / esize)).foldl (fun acc i => setLane acc esize i (f i)) 0

/-- Clear the upper 64 bits unless `q`. -/
def vtrunc (q : Bool) (v : BitVec 128) : BitVec 128 :=
  if q then v else (v.setWidth 64).setWidth 128

def boolLane (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

def vec3Compute (q : Bool) (esize : Nat) (op : VecOp) (d n m : BitVec 128) : BitVec 128 :=
  let lanes (f : BitVec 64 → BitVec 64 → BitVec 64) : BitVec 128 :=
    mkVec q esize fun i => f (getLane n esize i) (getLane m esize i)
  let sx := sextLane esize
  match op with
  | .add => lanes (· + ·)
  | .sub => lanes (· - ·)
  | .mul => lanes (· * ·)
  | .and => vtrunc q (n &&& m)
  | .bic => vtrunc q (n &&& ~~~m)
  | .orr => vtrunc q (n ||| m)
  | .orn => vtrunc q (n ||| ~~~m)
  | .eor => vtrunc q (n ^^^ m)
  | .bsl => vtrunc q (m ^^^ ((m ^^^ n) &&& d))
  | .bit => vtrunc q (d ^^^ ((d ^^^ n) &&& m))
  | .bif => vtrunc q (d ^^^ ((d ^^^ n) &&& ~~~m))
  | .cmeq => lanes fun a b => boolLane (a == b)
  | .cmtst => lanes fun a b => boolLane (a &&& b != 0)
  | .cmhi => lanes fun a b => boolLane (b < a)
  | .cmhs => lanes fun a b => boolLane (b ≤ a)
  | .cmgt => lanes fun a b => boolLane ((sx b).slt (sx a))
  | .cmge => lanes fun a b => boolLane ((sx b).sle (sx a))
  | .umax => lanes fun a b => if b < a then a else b
  | .umin => lanes fun a b => if a < b then a else b
  | .smax => lanes fun a b => if (sx b).slt (sx a) then a else b
  | .smin => lanes fun a b => if (sx a).slt (sx b) then a else b
  -- The remaining operations are defined by `vec3Extra`.
  | _ => 0


/-! ### More Advanced SIMD helpers -/

/-- Unsigned value of an `esize`-bit lane. -/
def laneU (x : BitVec 64) : Int := x.toNat
/-- Signed value of an `esize`-bit lane. -/
def laneS (esize : Nat) (x : BitVec 64) : Int := (sextLane esize x).toInt

/-- Saturate an integer to the range of an `esize`-bit lane. -/
def satU (esize : Nat) (v : Int) : BitVec 64 :=
  if v < 0 then 0 else if v ≥ 2 ^ esize then BitVec.ofNat 64 (2 ^ esize - 1) else BitVec.ofInt 64 v
def satS (esize : Nat) (v : Int) : BitVec 64 :=
  if v < -(2 ^ (esize - 1)) then BitVec.ofInt 64 (-(2 ^ (esize - 1)))
  else if v ≥ 2 ^ (esize - 1) then BitVec.ofNat 64 (2 ^ (esize - 1) - 1)
  else BitVec.ofInt 64 v

/-- Element `i` of the concatenation `hi:lo` of two vectors of `count` lanes. -/
def concatLane (lo hi : BitVec 128) (esize count i : Nat) : BitVec 64 :=
  if i < count then getLane lo esize i else getLane hi esize (i - count)

/-- Signed/unsigned shift of a lane by the signed amount in the bottom byte of
`m` (`SSHL`/`USHL`, no rounding or saturation). -/
def shlBy (signed : Bool) (esize : Nat) (x m : BitVec 64) : BitVec 64 :=
  let sh := (m.setWidth 8).toInt
  if sh ≥ 0 then x <<< sh.toNat
  else if signed then (sextLane esize x).sshiftRight (-sh).toNat
  else x >>> (-sh).toNat

/-- Number of lanes of a 64- or 128-bit vector. -/
def lanes (q : Bool) (esize : Nat) : Nat := (if q then 128 else 64) / esize

/-- Rounding arithmetic shift right of an integer (`sh ≥ 1`). -/
def rshr (v : Int) (sh : Nat) : Int := (v + 2 ^ sh / 2) / 2 ^ sh

/-- Shift by a signed amount (negative = right), optionally rounding right
shifts: the integer `element` of the Arm `{S,U}{Q}{R}SHL` pseudocode. -/
def shiftInt (round : Bool) (v : Int) (sh : Int) : Int :=
  if 0 ≤ sh then v * 2 ^ sh.toNat
  else (v + (if round then 2 ^ (-sh).toNat / 2 else 0)) / 2 ^ (-sh).toNat

/-- The signed shift amount in the bottom byte of a lane. -/
def shAmt (m : BitVec 64) : Int := (m.setWidth 8).toInt

/-- Write narrow lanes to the low half (`q = false`, upper half zeroed) or to
the upper half (`q = true`, lower half kept) of `d`. -/
def narrowInsert (q : Bool) (esize : Nat) (d : BitVec 128) (f : Nat → BitVec 64) : BitVec 128 :=
  let r := mkVec false esize f
  if q then (r <<< 64) ||| (d.setWidth 64).setWidth 128 else r

def vec3Extra (q : Bool) (esize : Nat) (op : VecOp) (d n m : BitVec 128) : BitVec 128 :=
  let cnt := lanes q esize
  let ln (f : BitVec 64 → BitVec 64 → BitVec 64) : BitVec 128 :=
    mkVec q esize fun i => f (getLane n esize i) (getLane m esize i)
  let pair (f : BitVec 64 → BitVec 64 → BitVec 64) : BitVec 128 :=
    mkVec q esize fun i => f (concatLane n m esize cnt (2 * i)) (concatLane n m esize cnt (2 * i + 1))
  let sx := sextLane esize
  let S := laneS esize
  match op with
  | .addp => pair (· + ·)
  | .umaxp => pair fun a b => if b < a then a else b
  | .uminp => pair fun a b => if a < b then a else b
  | .smaxp => pair fun a b => if (sx b).slt (sx a) then a else b
  | .sminp => pair fun a b => if (sx a).slt (sx b) then a else b
  | .mla => mkVec q esize fun i => getLane d esize i + getLane n esize i * getLane m esize i
  | .mls => mkVec q esize fun i => getLane d esize i - getLane n esize i * getLane m esize i
  | .sshl => ln (shlBy true esize)
  | .ushl => ln (shlBy false esize)
  | .uqadd => ln fun a b => satU esize (laneU a + laneU b)
  | .uqsub => ln fun a b => satU esize (laneU a - laneU b)
  | .sqadd => ln fun a b => satS esize (S a + S b)
  | .sqsub => ln fun a b => satS esize (S a - S b)
  | .uhadd => ln fun a b => BitVec.ofInt 64 ((laneU a + laneU b) / 2)
  | .shadd => ln fun a b => BitVec.ofInt 64 ((S a + S b) / 2)
  | .urhadd => ln fun a b => BitVec.ofInt 64 ((laneU a + laneU b + 1) / 2)
  | .srhadd => ln fun a b => BitVec.ofInt 64 ((S a + S b + 1) / 2)
  | .uabd => ln fun a b => BitVec.ofInt 64 (laneU a - laneU b).natAbs
  | .sabd => ln fun a b => BitVec.ofInt 64 (S a - S b).natAbs
  | .srshl => ln fun a b => BitVec.ofInt 64 (shiftInt true (S a) (shAmt b))
  | .urshl => ln fun a b => BitVec.ofInt 64 (shiftInt true (laneU a) (shAmt b))
  | .sqshl => ln fun a b => satS esize (shiftInt false (S a) (shAmt b))
  | .uqshl => ln fun a b => satU esize (shiftInt false (laneU a) (shAmt b))
  | .sqrshl => ln fun a b => satS esize (shiftInt true (S a) (shAmt b))
  | .uqrshl => ln fun a b => satU esize (shiftInt true (laneU a) (shAmt b))
  | .sqdmulh => ln fun a b => satS esize ((2 * S a * S b) / 2 ^ esize)
  | .sqrdmulh => ln fun a b => satS esize ((2 * S a * S b + 2 ^ (esize - 1)) / 2 ^ esize)
  | .sqrdmlah => mkVec q esize fun i =>
      let (x, y) := (S (getLane n esize i), S (getLane m esize i))
      satS esize ((S (getLane d esize i) * 2 ^ esize + 2 * x * y + 2 ^ (esize - 1)) / 2 ^ esize)
  | .sqrdmlsh => mkVec q esize fun i =>
      let (x, y) := (S (getLane n esize i), S (getLane m esize i))
      satS esize ((S (getLane d esize i) * 2 ^ esize - 2 * x * y + 2 ^ (esize - 1)) / 2 ^ esize)
  | _ => vec3Compute q esize op d n m

/-- Reverse the order of `esize`-bit lanes within each `csize`-bit container. -/
def revLanes (q : Bool) (esize csize : Nat) (n : BitVec 128) : BitVec 128 :=
  mkVec q esize fun i => getLane n esize (i ^^^ (csize / esize - 1))

def popcount8 (x : BitVec 64) : Nat :=
  (List.range 8).foldl (fun acc i => acc + (if x.getLsbD i then 1 else 0)) 0

def vec2Compute (q : Bool) (esize : Nat) (op : Vec2Op) (d n : BitVec 128) : BitVec 128 :=
  let ln (f : BitVec 64 → BitVec 64) : BitVec 128 := mkVec q esize fun i => f (getLane n esize i)
  let sx := sextLane esize
  let wide (acc : Bool) (signed : Bool) : BitVec 128 :=
    mkVec q (2 * esize) fun i =>
      let ext := fun x => if signed then sextLane esize x else x
      let s := ext (getLane n esize (2 * i)) + ext (getLane n esize (2 * i + 1))
      if acc then getLane d (2 * esize) i + s else s
  match op with
  | .rev16 => revLanes q esize 16 n
  | .rev32 => revLanes q esize 32 n
  | .rev64 => revLanes q esize 64 n
  | .cnt => ln fun x => BitVec.ofNat 64 (popcount8 x)
  | .clz => ln fun x => BitVec.ofNat 64 (countLeadingZeros (x.setWidth esize))
  | .cls => ln fun x => BitVec.ofNat 64 (countLeadingSignBits (x.setWidth esize))
  | .not => vtrunc q (~~~n)
  | .rbit => ln fun x => ((x.setWidth 8).reverse).setWidth 64
  | .abs => ln fun x => if (sx x).slt 0 then 0 - x else x
  | .neg => ln fun x => 0 - x
  | .cmgt0 => ln fun x => boolLane ((0 : BitVec 64).slt (sx x))
  | .cmeq0 => ln fun x => boolLane (x == 0)
  | .cmlt0 => ln fun x => boolLane ((sx x).slt 0)
  | .cmge0 => ln fun x => boolLane ((0 : BitVec 64).sle (sx x))
  | .cmle0 => ln fun x => boolLane ((sx x).sle 0)
  | .xtn =>
    let r := mkVec false esize fun i => getLane n (2 * esize) i
    if q then (r <<< 64) ||| (d.setWidth 64).setWidth 128 else r
  | .saddlp => wide false true
  | .uaddlp => wide false false
  | .sadalp => wide true true
  | .uadalp => wide true false
  | .sqxtn => narrowInsert q esize d fun i => satS esize (laneS (2 * esize) (getLane n (2 * esize) i))
  | .uqxtn => narrowInsert q esize d fun i => satU esize (laneU (getLane n (2 * esize) i))
  | .sqxtun => narrowInsert q esize d fun i => satU esize (laneS (2 * esize) (getLane n (2 * esize) i))
  | .sqabs => ln fun x => satS esize (laneS esize x).natAbs
  | .sqneg => ln fun x => satS esize (-(laneS esize x))
  | .suqadd => mkVec q esize fun i => satS esize (laneS esize (getLane d esize i) + laneU (getLane n esize i))
  | .usqadd => mkVec q esize fun i => satU esize (laneU (getLane d esize i) + laneS esize (getLane n esize i))
  | .shll =>
    let src := if q then n >>> 64 else n
    mkVec true (2 * esize) fun i => getLane src esize i <<< esize

def vreduceCompute (q : Bool) (esize : Nat) (op : VecRedOp) (n : BitVec 128) : BitVec 128 :=
  let xs := (List.range (lanes q esize)).map (getLane n esize)
  let sx := sextLane esize
  let r : BitVec 64 := match op with
    | .addv => xs.foldl (· + ·) 0
    | .uaddlv => xs.foldl (· + ·) 0
    | .saddlv => xs.foldl (fun a x => a + sx x) 0
    | .umaxv => xs.foldl (fun a x => if a < x then x else a) 0
    | .uminv => xs.foldl (fun a x => if x < a then x else a) (getLane n esize 0)
    | .smaxv => xs.foldl (fun a x => if (sx a).slt (sx x) then x else a) (getLane n esize 0)
    | .sminv => xs.foldl (fun a x => if (sx x).slt (sx a) then x else a) (getLane n esize 0)
  let rsize := if op == .uaddlv || op == .saddlv then 2 * esize else esize
  setLane 0 rsize 0 r

def vpermCompute (q : Bool) (esize : Nat) (op : VecPermOp) (n m : BitVec 128) : BitVec 128 :=
  let cnt := lanes q esize
  let half := cnt / 2
  match op with
  | .uzp1 => mkVec q esize fun i => concatLane n m esize cnt (2 * i)
  | .uzp2 => mkVec q esize fun i => concatLane n m esize cnt (2 * i + 1)
  | .trn1 => mkVec q esize fun i =>
      if i % 2 == 0 then getLane n esize i else getLane m esize (i - 1)
  | .trn2 => mkVec q esize fun i =>
      if i % 2 == 0 then getLane n esize (i + 1) else getLane m esize i
  | .zip1 => mkVec q esize fun i =>
      if i % 2 == 0 then getLane n esize (i / 2) else getLane m esize (i / 2)
  | .zip2 => mkVec q esize fun i =>
      if i % 2 == 0 then getLane n esize (half + i / 2) else getLane m esize (half + i / 2)

def vextCompute (q : Bool) (pos : Nat) (n m : BitVec 128) : BitVec 128 :=
  if q then ((m ++ n) >>> (8 * pos)).setWidth 128
  else ((((m.setWidth 64) ++ (n.setWidth 64)) >>> (8 * pos)).setWidth 64).setWidth 128

def vtblCompute (q : Bool) (nregs : Nat) (tbx : Bool) (s : State) (rm rn rd : Reg) : BitVec 128 :=
  let idx := s.vreg rm
  let d := s.vreg rd
  mkVec q 8 fun i =>
    let k := (getLane idx 8 i).toNat
    if k < 16 * nregs then getLane (s.vreg (rn + BitVec.ofNat 5 (k / 16))) 8 (k % 16)
    else if tbx then getLane d 8 i else 0

def vshiftCompute (q : Bool) (esize : Nat) (op : VecShiftOp) (sh : Nat) (d n : BitVec 128) :
    BitVec 128 :=
  let ln (f : BitVec 64 → BitVec 64 → BitVec 64) : BitVec 128 :=
    mkVec q esize fun i => f (getLane d esize i) (getLane n esize i)
  let sx := sextLane esize
  let ones : BitVec 64 := BitVec.allOnes 64 >>> (64 - esize)
  let src := if q then n >>> 64 else n
  let nw (f : BitVec 64 → BitVec 64) : BitVec 128 :=
    narrowInsert q esize d fun i => f (getLane n (2 * esize) i)
  match op with
  | .sshr => ln fun _ x => (sx x).sshiftRight sh
  | .ushr => ln fun _ x => x >>> sh
  | .ssra => ln fun a x => a + (sx x).sshiftRight sh
  | .usra => ln fun a x => a + (x >>> sh)
  | .shl => ln fun _ x => x <<< sh
  | .sli => ln fun a x => (a &&& ~~~(ones <<< sh)) ||| (x <<< sh)
  | .sri => ln fun a x => (a &&& ~~~(ones >>> sh)) ||| (x >>> sh)
  | .sshll => mkVec true (2 * esize) fun i => sx (getLane src esize i) <<< sh
  | .ushll => mkVec true (2 * esize) fun i => getLane src esize i <<< sh
  | .shrn =>
    let r := mkVec false esize fun i => getLane n (2 * esize) i >>> sh
    if q then (r <<< 64) ||| (d.setWidth 64).setWidth 128 else r
  | .srshr => ln fun _ x => BitVec.ofInt 64 (rshr (laneS esize x) sh)
  | .urshr => ln fun _ x => BitVec.ofInt 64 (rshr (laneU x) sh)
  | .srsra => ln fun a x => a + BitVec.ofInt 64 (rshr (laneS esize x) sh)
  | .ursra => ln fun a x => a + BitVec.ofInt 64 (rshr (laneU x) sh)
  | .sqshlu => ln fun _ x => satU esize (laneS esize x * 2 ^ sh)
  | .sqshl => ln fun _ x => satS esize (laneS esize x * 2 ^ sh)
  | .uqshl => ln fun _ x => satU esize (laneU x * 2 ^ sh)
  | .rshrn => nw fun x => BitVec.ofInt 64 (rshr (laneU x) sh)
  | .sqshrn => nw fun x => satS esize (laneS (2 * esize) x / 2 ^ sh)
  | .uqshrn => nw fun x => satU esize (laneU x / 2 ^ sh)
  | .sqrshrn => nw fun x => satS esize (rshr (laneS (2 * esize) x) sh)
  | .uqrshrn => nw fun x => satU esize (rshr (laneU x) sh)
  | .sqshrun => nw fun x => satU esize (laneS (2 * esize) x / 2 ^ sh)
  | .sqrshrun => nw fun x => satU esize (rshr (laneS (2 * esize) x) sh)

def vlongCompute (q : Bool) (esize : Nat) (op : VecLongOp) (d n m : BitVec 128) : BitVec 128 :=
  -- High-half narrowing forms.
  let hn (sub round : Bool) : BitVec 128 := narrowInsert q esize d fun i =>
    let a := getLane n (2 * esize) i
    let b := getLane m (2 * esize) i
    let r := (if sub then a - b else a + b) + (if round then BitVec.ofNat 64 (2 ^ (esize - 1)) else 0)
    r >>> esize
  if op == .addhn then hn false false else if op == .raddhn then hn false true
  else if op == .subhn then hn true false else if op == .rsubhn then hn true true else
  let signed := op ∈ [.saddl, .saddw, .ssubl, .ssubw, .smlal, .smlsl, .smull, .sabal, .sabdl,
    .sqdmull, .sqdmlal, .sqdmlsl]
  let ext := fun x => if signed then sextLane esize x else x
  let half (v : BitVec 128) : BitVec 128 := if q then v >>> 64 else v
  let a (i : Nat) : BitVec 64 :=
    if op ∈ [.saddw, .uaddw, .ssubw, .usubw] then getLane n (2 * esize) i
    else ext (getLane (half n) esize i)
  let b (i : Nat) : BitVec 64 := ext (getLane (half m) esize i)
  let acc (i : Nat) : BitVec 64 := getLane d (2 * esize) i
  mkVec true (2 * esize) fun i =>
    match op with
    | .saddl | .uaddl | .saddw | .uaddw => a i + b i
    | .ssubl | .usubl | .ssubw | .usubw => a i - b i
    | .smlal | .umlal => acc i + a i * b i
    | .smlsl | .umlsl => acc i - a i * b i
    | .smull | .umull => a i * b i
    | .sabdl | .sabal | .uabdl | .uabal =>
      let diff : Int := if signed then (a i).toInt - (b i).toInt else (a i).toNat - (b i).toNat
      let r := BitVec.ofNat 64 diff.natAbs
      if op == .sabal || op == .uabal then acc i + r else r
    | .sqdmull => satS (2 * esize) (2 * (a i).toInt * (b i).toInt)
    | .sqdmlal => satS (2 * esize) (laneS (2 * esize) (acc i) +
        laneS (2 * esize) (satS (2 * esize) (2 * (a i).toInt * (b i).toInt)))
    | .sqdmlsl => satS (2 * esize) (laneS (2 * esize) (acc i) -
        laneS (2 * esize) (satS (2 * esize) (2 * (a i).toInt * (b i).toInt)))
    | _ => 0

def velemCompute (q : Bool) (esize : Nat) (op : VecElemOp) (index : Nat) (d n m : BitVec 128) :
    BitVec 128 :=
  let e := getLane m esize index
  let S := laneS esize
  match op with
  | .mul => mkVec q esize fun i => getLane n esize i * e
  | .mla => mkVec q esize fun i => getLane d esize i + getLane n esize i * e
  | .mls => mkVec q esize fun i => getLane d esize i - getLane n esize i * e
  | .sqdmulh => mkVec q esize fun i => satS esize ((2 * S (getLane n esize i) * S e) / 2 ^ esize)
  | .sqrdmulh => mkVec q esize fun i =>
      satS esize ((2 * S (getLane n esize i) * S e + 2 ^ (esize - 1)) / 2 ^ esize)
  | .sqrdmlah => mkVec q esize fun i =>
      satS esize ((S (getLane d esize i) * 2 ^ esize + 2 * S (getLane n esize i) * S e +
        2 ^ (esize - 1)) / 2 ^ esize)
  | .sqrdmlsh => mkVec q esize fun i =>
      satS esize ((S (getLane d esize i) * 2 ^ esize - 2 * S (getLane n esize i) * S e +
        2 ^ (esize - 1)) / 2 ^ esize)
  | .sqdmull | .sqdmlal | .sqdmlsl =>
    let src := if q then n >>> 64 else n
    let W := 2 * esize
    mkVec true W fun i =>
      let p := laneS W (satS W (2 * S (getLane src esize i) * S e))
      let acc := laneS W (getLane d W i)
      satS W (match op with | .sqdmlal => acc + p | .sqdmlsl => acc - p | _ => p)
  | _ =>
    let signed := op ∈ [.smull, .smlal, .smlsl]
    let ext := fun x => if signed then sextLane esize x else x
    let src := if q then n >>> 64 else n
    mkVec true (2 * esize) fun i =>
      let p := ext (getLane src esize i) * ext e
      match op with
      | .smlal | .umlal => getLane d (2 * esize) i + p
      | .smlsl | .umlsl => getLane d (2 * esize) i - p
      | _ => p

def vdotCompute (q signed : Bool) (d n m : BitVec 128) : BitVec 128 :=
  let ext := fun x => if signed then sextLane 8 x else x
  mkVec q 32 fun i =>
    (List.range 4).foldl (fun acc j =>
      acc + ext (getLane n 8 (4 * i + j)) * ext (getLane m 8 (4 * i + j))) (getLane d 32 i)

/-- `LD1`..`LD4` / `ST1`..`ST4` (multiple structures) at `addr`. -/
def ldstMulti (s : State) (q : Bool) (esize : Nat) (load : Bool) (rpt selem : Nat)
    (addr : BitVec 64) (rt : Reg) : State :=
  let ebytes := esize / 8
  let elems := lanes q esize
  -- (register, element, byte offset) of every element transfer, in order.
  let xfers := (List.range rpt).flatMap fun r => (List.range elems).flatMap fun e =>
    (List.range selem).map fun k =>
      (rt + BitVec.ofNat 5 (r + k), e, ((r * elems + e) * selem + k) * ebytes)
  if load then
    -- Registers written are zero-extended from the datasize.
    let s := (List.range (rpt * selem)).foldl
      (fun s j => s.setV (rt + BitVec.ofNat 5 j) (vtrunc q (s.vreg (rt + BitVec.ofNat 5 j)))) s
    xfers.foldl (fun s (t, e, off) =>
      s.setV t (setLane (s.vreg t) esize e (s.mem.readN (addr + BitVec.ofNat 64 off) ebytes))) s
  else
    xfers.foldl (fun s (t, e, off) =>
      s.setMem (s.mem.writeN (addr + BitVec.ofNat 64 off) ebytes (getLane (s.vreg t) esize e))) s

/-- `CRC32` checksum update over the low `size` bytes of `v` (bit-reflected). -/
def crc32Update (castagnoli : Bool) (acc v : BitVec 64) (size : Nat) : BitVec 64 :=
  let poly : BitVec 32 := if castagnoli then 0x82F63B78 else 0xEDB88320
  let r := (List.range (8 * size)).foldl (fun (c : BitVec 32) i =>
      let b := c.getLsbD 0 != v.getLsbD i
      (c >>> 1) ^^^ (if b then poly else 0)) (acc.setWidth 32)
  r.setWidth 64

/-! ### Floating point -/

/-- The `N`-bit floating-point value held in the low bits of a vector register. -/
def fpArg (v : BitVec 128) (N : Nat) : Nat := v.toNat % 2 ^ N

/-- A scalar floating-point result: written to the low `N` bits of the
register, the rest zeroed. -/
def fpRes (N : Nat) (r : Nat) : BitVec 128 := BitVec.ofNat 128 (r % 2 ^ N)

theorem fpArg_fpRes (N r : Nat) (h : N ≤ 128 := by decide) : fpArg (fpRes N r) N = r % 2 ^ N := by
  simp only [fpArg, fpRes, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos N))
    (Nat.pow_le_pow_right (by decide) h)), Nat.mod_mod]


def flane (v : BitVec 128) (N i : Nat) : Nat := (getLane v N i).toNat

def fboolLane (N : Nat) (b : Bool) : Nat := if b then 2 ^ N - 1 else 0

/-- Build a vector from per-lane `(value, exceptions)` pairs, OR-ing the
exceptions. -/
def mkVecF (q : Bool) (N : Nat) (f : Nat → Nat × Nat) : BitVec 128 × Nat :=
  (mkVec q N fun i => BitVec.ofNat 64 (f i).1,
   (List.range (lanes q N)).foldl (fun acc i => acc ||| (f i).2) 0)

/-- A comparison result as an all-ones/all-zeros lane. -/
def fcmpLane (N : Nat) (r : Bool × Nat) : Nat × Nat := (fboolLane N r.1, r.2)

def fbin (c : FP.Ctl) (N : Nat) (op : FVecOp) (d x y : Nat) : Nat × Nat :=
  match op with
  | .fadd | .faddp => FP.addC c N x y
  | .fsub => FP.subC c N x y
  | .fmul => FP.mulC c N false x y
  | .fdiv => FP.divC c N x y
  | .fmax | .fmaxp => FP.maxMinC c N true x y
  | .fmin | .fminp => FP.maxMinC c N false x y
  | .fmaxnm | .fmaxnmp => FP.maxMinNumC c N true x y
  | .fminnm | .fminnmp => FP.maxMinNumC c N false x y
  | .fmla => FP.mulAddC c N d x y
  | .fmls => FP.mulAddC c N d (FP.neg N x) y
  | .fabd => let r := FP.subC c N x y; (FP.abs N r.1, r.2)
  | .fcmeq => fcmpLane N (FP.cmpC c N .eq x y)
  | .fcmge => fcmpLane N (FP.cmpC c N .ge x y)
  | .fcmgt => fcmpLane N (FP.cmpC c N .gt x y)
  | .facge => fcmpLane N (FP.cmpC c N .ge (FP.abs N x) (FP.abs N y))
  | .facgt => fcmpLane N (FP.cmpC c N .gt (FP.abs N x) (FP.abs N y))
  | .fmulx => FP.mulC c N true x y
  | .frecps => FP.stepFusedC c N false x y
  | .frsqrts => FP.stepFusedC c N true x y

def fvec3Compute (c : FP.Ctl) (q : Bool) (N : Nat) (op : FVecOp) (d n m : BitVec 128) :
    BitVec 128 × Nat :=
  let cnt := lanes q N
  let pairwise := op ∈ [.faddp, .fmaxnmp, .fminnmp, .fmaxp, .fminp]
  mkVecF q N fun i =>
    if pairwise then
      fbin c N op 0 (concatLane n m N cnt (2 * i)).toNat (concatLane n m N cnt (2 * i + 1)).toNat
    else fbin c N op (flane d N i) (flane n N i) (flane m N i)

/-- The signed (`signed`) or unsigned integer held in an `N`-bit lane. -/
def laneInt (signed : Bool) (N x : Nat) : Int :=
  if signed && x ≥ 2 ^ (N - 1) then (x : Int) - ((2 ^ N : Nat) : Int) else x

def fun1 (c : FP.Ctl) (N : Nat) (op : FVec2Op) (x : Nat) : Nat × Nat :=
  let toLane (r : Int × Nat) : Nat × Nat := ((r.1 % (2 ^ N : Nat) : Int).toNat, r.2)
  match op with
  | .fabs => (FP.abs N x, 0)
  | .fneg => (FP.neg N x, 0)
  | .fsqrt => FP.sqrtC c N x
  | .fcmgt0 => fcmpLane N (FP.cmpC c N .gt x 0)
  | .fcmge0 => fcmpLane N (FP.cmpC c N .ge x 0)
  | .fcmeq0 => fcmpLane N (FP.cmpC c N .eq x 0)
  | .fcmle0 => fcmpLane N (FP.cmpC c N .ge 0 x)
  | .fcmlt0 => fcmpLane N (FP.cmpC c N .gt 0 x)
  | .fcvt mode signed => toLane (FP.toIntC c N mode signed N 0 x)
  | .cvtf signed => FP.ofIntC c N c.rm 0 (laneInt signed N x)
  | .fcvtFix signed fb => toLane (FP.toIntC c N .z signed N fb x)
  | .cvtfFix signed fb => FP.ofIntC c N c.rm fb (laneInt signed N x)
  | .frint mode => FP.roundToIntegralC c N mode false x
  | .frintx => FP.roundToIntegralC c N c.rm true x
  | .frinti => FP.roundToIntegralC c N c.rm false x
  | .frintN xm k => FP.roundIntNC c N (if xm then c.rm else .z) k x
  | .frecpe => FP.recipEstC c N x
  | .frsqrte => FP.rsqrtEstC c N x
  | .frecpx => FP.recpXC c N x
  | .urecpe => (FP.urecpe x, 0)
  | .ursqrte => (FP.ursqrte x, 0)

/-- FMLAL{2}/FMLSL{2}: lane `i` of the result is `d[i] ± n'[i] * m'[i]` where
`n'`, `m'` are the half-precision lanes of the selected halves. -/
def fmlalCompute (c : FP.Ctl) (q sub top : Bool) (index : Option Nat) (d n m : BitVec 128) :
    BitVec 128 × Nat :=
  let half := if q then 64 else 32
  let part (v : BitVec 128) := if top then v >>> half else v
  mkVecF q 32 fun i =>
    let x := flane (part n) 16 i
    let x := if sub then FP.neg 16 x else x
    let y := match index with
      | some k => flane m 16 k
      | none => flane (part m) 16 i
    FP.mulAddHC c 32 (flane d 32 i) x y

def fcmlaCompute (c : FP.Ctl) (q : Bool) (N rot : Nat) (d n m : BitVec 128) : BitVec 128 × Nat :=
  let neg := FP.neg N
  mkVecF q N fun i =>
    let e := i / 2
    let re := flane m N (2 * e)
    let im := flane m N (2 * e + 1)
    let nre := flane n N (2 * e)
    let nim := flane n N (2 * e + 1)
    -- (element1, element2) for the even lane, (element3, element4) for the odd lane.
    let (e1, e2, e3, e4) := match rot with
      | 0 => (re, nre, im, nre)
      | 1 => (neg im, nim, re, nim)
      | 2 => (neg re, nre, neg im, nre)
      | _ => (im, nim, neg re, nim)
    if i % 2 == 0 then FP.mulAddC c N (flane d N i) e2 e1 else FP.mulAddC c N (flane d N i) e4 e3

def fcaddCompute (c : FP.Ctl) (q : Bool) (N : Nat) (rot270 : Bool) (n m : BitVec 128) :
    BitVec 128 × Nat :=
  mkVecF q N fun i =>
    let e := i / 2
    let re := flane m N (2 * e)
    let im := flane m N (2 * e + 1)
    let (e1, e3) := if rot270 then (im, FP.neg N re) else (FP.neg N im, re)
    FP.addC c N (flane n N i) (if i % 2 == 0 then e1 else e3)

def fvec2Compute (c : FP.Ctl) (q scalar : Bool) (N : Nat) (op : FVec2Op) (n : BitVec 128) :
    BitVec 128 × Nat :=
  if scalar then let r := fun1 c N op (flane n N 0); (BitVec.ofNat 128 r.1, r.2)
  else mkVecF q N fun i => fun1 c N op (flane n N i)

def fred (c : FP.Ctl) (N : Nat) (op : FRedOp) (x y : Nat) : Nat × Nat :=
  match op with
  | .fadd => FP.addC c N x y
  | .fmax => FP.maxMinC c N true x y
  | .fmin => FP.maxMinC c N false x y
  | .fmaxnm => FP.maxMinNumC c N true x y
  | .fminnm => FP.maxMinNumC c N false x y

/-- The Arm `Reduce` tree: `op (Reduce lo) (Reduce hi)` over halves, OR-ing
the exceptions. -/
def reduceTree (f : Nat → Nat → Nat × Nat) : Nat → List Nat → Nat × Nat
  | 0, xs => (xs.headD 0, 0)
  | k + 1, xs =>
    let h := xs.length / 2
    let a := reduceTree f k (xs.take h)
    let b := reduceTree f k (xs.drop h)
    let r := f a.1 b.1
    (r.1, a.2 ||| b.2 ||| r.2)

def freduceCompute (c : FP.Ctl) (q pairwise : Bool) (N : Nat) (op : FRedOp) (n : BitVec 128) :
    BitVec 128 × Nat :=
  let cnt := if pairwise then 2 else lanes q N
  let xs := (List.range cnt).map (flane n N)
  let r := reduceTree (fred c N op) (Nat.log2 cnt) xs
  (BitVec.ofNat 128 r.1, r.2)

def fcvtnlCompute (c : FP.Ctl) (q narrow : Bool) (W : Nat) (d n : BitVec 128) : BitVec 128 × Nat :=
  let N := W / 2
  if narrow then
    let r := mkVecF false N fun i => FP.convertC c W N c.rm (flane n W i)
    ((if q then (r.1 <<< 64) ||| (d.setWidth 64).setWidth 128 else r.1), r.2)
  else
    let src := if q then n >>> 64 else n
    mkVecF true W fun i => FP.convertC c N W c.rm (flane src N i)

/-- FCVTXN{2}: double to single, rounding to odd. -/
def fcvtxnCompute (c : FP.Ctl) (q scalar : Bool) (d n : BitVec 128) : BitVec 128 × Nat :=
  if scalar then let r := FP.convertC c 64 32 .odd (flane n 64 0); (BitVec.ofNat 128 r.1, r.2)
  else
    let r := mkVecF false 32 fun i => FP.convertC c 64 32 .odd (flane n 64 i)
    ((if q then (r.1 <<< 64) ||| (d.setWidth 64).setWidth 128 else r.1), r.2)

/-! ### Data-processing helpers -/

def bitfieldCompute {n : Nat} (op : BitfieldOp) (dst src : BitVec n) (r s : Nat)
    (wmask tmask : BitVec n) : BitVec n :=
  let dst := if op == .bfm then dst else 0
  let bot := (dst &&& ~~~wmask) ||| (src.rotateRight r &&& wmask)
  let top := if op == .sbfm then (if src.getLsbD s then BitVec.allOnes n else 0) else dst
  (top &&& ~~~tmask) ||| (bot &&& tmask)

def dp1Compute {n : Nat} (op : DP1Op) (x : BitVec n) : BitVec n :=
  match op with
  | .rbit => x.reverse
  | .rev16 => revBytes x 16
  | .rev32 => revBytes x 32
  | .rev => revBytes x n
  | .clz => BitVec.ofNat n (countLeadingZeros x)
  | .cls => BitVec.ofNat n (countLeadingSignBits x)

def dp2Compute {n : Nat} (op : DP2Op) (a b : BitVec n) : BitVec n :=
  match op with
  | .udiv => if b == 0 then 0 else a / b
  | .sdiv => if b == 0 then 0 else a.sdiv b
  | .lslv => a <<< (b.toNat % n)
  | .lsrv => a >>> (b.toNat % n)
  | .asrv => a.sshiftRight (b.toNat % n)
  | .rorv => a.rotateRight (b.toNat % n)

def dp3Compute (sf : Bool) (op : DP3Op) (m a n : BitVec 64) : BitVec 64 :=
  let s32 (x : BitVec 64) : BitVec 64 := (x.setWidth 32).signExtend 64
  let u32 (x : BitVec 64) : BitVec 64 := (x.setWidth 32).setWidth 64
  match op with
  | .madd => trunc sf (a + n * m)
  | .msub => trunc sf (a - n * m)
  | .smaddl => a + s32 n * s32 m
  | .smsubl => a - s32 n * s32 m
  | .umaddl => a + u32 n * u32 m
  | .umsubl => a - u32 n * u32 m
  | .smulh => (n.signExtend 128 * m.signExtend 128).extractLsb' 64 64
  | .umulh => (n.setWidth 128 * m.setWidth 128).extractLsb' 64 64

def atomicCompute (size : Nat) (op : AtomicOp) (old v : BitVec 64) : BitVec 64 :=
  let sx := sextBytes size
  match op with
  | .add => old + v
  | .clr => old &&& ~~~v
  | .eor => old ^^^ v
  | .set => old ||| v
  | .smax => if (sx v).slt (sx old) then old else v
  | .smin => if (sx old).slt (sx v) then old else v
  | .umax => if v < old then old else v
  | .umin => if old < v then old else v
  | .swp => v

/-! ### Memory access helpers -/

/-- Does using `rn` as a base register raise an SP alignment fault? Register 31
is SP, which must be 16-byte aligned when used as a base (stack alignment
checking, SCTLR_EL1.SA0, is enabled for EL0 on macOS; see `tools/cosim/spalign.c`). -/
def spFault (s : State) (rn : Reg) : Bool :=
  rn == 31 && !aligned s.sp 16

/-- Integer load/store of a single register at `addr`. -/
def ldstOne (s : State) (size : Nat) (op : MemOp) (addr : BitVec 64) (rt : Reg) : State :=
  match op with
  | .store => s.setMem (s.mem.writeN addr size (s.x rt))
  | .load => s.setX rt (s.mem.readN addr size)
  | .loadSigned64 => s.setX rt (sextBytes size (s.mem.readN addr size))
  | .loadSigned32 => s.setX rt (trunc false (sextBytes size (s.mem.readN addr size)))
  | .prefetch => s

/-- Common shape of an immediate-offset access with optional writeback. -/
def withAddr (s : State) (rn : Reg) (mode : AddrMode) (offset : BitVec 64)
    (access : State → BitVec 64 → State) : State :=
  if spFault s rn then s.fault .spAlignment else
    let base := s.xsp rn
    let addr := if mode == .post then base else base + offset
    let s := access s addr
    let s := if mode == .offset then s else s.setXSP rn (base + offset)
    s.nextPC

/-! ### Execute -/

/-- The floating-point controls selected by an `FPCR` value. -/
def ctlOf (f : BitVec 64) : FP.Ctl where
  rm := let r := (f >>> 22) &&& 3
    if r = 0 then .n else if r = 1 then .p else if r = 2 then .m else .z
  fz := f.getLsbD 24
  fz16 := f.getLsbD 19
  dn := f.getLsbD 25
  ahp := f.getLsbD 26
  ufe := f.getLsbD 11

/-- Whether exceptions `fl` (FPSR bit layout) include one whose trap is
enabled: enable bit `8 + k` of `FPCR` traps FPSR flag `k`. -/
def trapped (f : BitVec 64) (fl : Nat) : Bool := (f >>> 8) &&& BitVec.ofNat 64 fl &&& 0x9F != 0

theorem ctlOf_default {f : BitVec 64} (h : f &&& fpcrModeMask = 0) : ctlOf f = {} := by
  simp only [fpcrModeMask] at h
  have h1 : (f >>> 22) &&& 3 = 0 := by bv_decide
  have h2 : f.getLsbD 24 = false := by bv_decide
  have h3 : f.getLsbD 19 = false := by bv_decide
  have h4 : f.getLsbD 25 = false := by bv_decide
  have h5 : f.getLsbD 26 = false := by bv_decide
  have h6 : f.getLsbD 11 = false := by bv_decide
  simp only [ctlOf, h1, h2, h3, h4, h5, h6, ite_true]

theorem trapped_default {f : BitVec 64} (h : f &&& fpcrModeMask = 0) (fl : Nat) :
    trapped f fl = false := by
  simp only [fpcrModeMask] at h
  have : (f >>> 8) &&& BitVec.ofNat 64 fl &&& 159#64 = 0#64 := by bv_decide
  simp [trapped, this]

/-- Execute a floating-point instruction: `k` computes, under the `FPCR`
controls, the exceptions raised and the resulting state. An exception whose
trap is enabled stops the machine; otherwise the exceptions accumulate in
`FPSR`. -/
def fpOp (w : BitVec 32) (s : State) (k : FP.Ctl → Nat × State) : State :=
  let r := k (ctlOf s.fpcr)
  if trapped s.fpcr r.1 then s.fault (.fpTrap w) else r.2.orFPSR r.1

/-- `FPSR.QC`, the cumulative saturation flag. -/
def QC : Nat := 2 ^ 27

/-- `k s`, setting `FPSR.QC` if the instruction saturated. -/
def satOp (sat : Bool) (s : State) (k : State → State) : State :=
  if sat then (k s).orFPSR QC else k s

/-! ### Saturation (FPSR.QC) -/

def VecOp.saturating (op : VecOp) : Bool :=
  op == .sqadd || op == .uqadd || op == .sqsub || op == .uqsub || op == .sqshl ||
  op == .uqshl || op == .sqrshl || op == .uqrshl || op == .sqdmulh || op == .sqrdmulh ||
  op == .sqrdmlah || op == .sqrdmlsh
def Vec2Op.saturating (op : Vec2Op) : Bool :=
  op == .sqxtn || op == .uqxtn || op == .sqxtun || op == .sqabs || op == .sqneg ||
  op == .suqadd || op == .usqadd
def VecLongOp.saturating (op : VecLongOp) : Bool :=
  op == .sqdmull || op == .sqdmlal || op == .sqdmlsl
def VecShiftOp.saturating (op : VecShiftOp) : Bool :=
  op == .sqshlu || op == .sqshl || op == .uqshl || op == .sqshrn || op == .uqshrn ||
  op == .sqrshrn || op == .uqrshrn || op == .sqshrun || op == .sqrshrun
def VecElemOp.saturating (op : VecElemOp) : Bool :=
  op == .sqdmulh || op == .sqrdmulh || op == .sqdmull || op == .sqdmlal || op == .sqdmlsl ||
  op == .sqrdmlah || op == .sqrdmlsh

def outS (esize : Nat) (v : Int) : Bool := v < -(2 ^ (esize - 1)) || v ≥ 2 ^ (esize - 1)
def outU (esize : Nat) (v : Int) : Bool := v < 0 || v ≥ 2 ^ esize
def anyLane (cnt : Nat) (f : Nat → Bool) : Bool := (List.range cnt).any f

/-- Whether any of the first `cnt` lanes of a three-same op saturates. -/
def vec3QC (cnt esize : Nat) (op : VecOp) (d n m : BitVec 128) : Bool :=
  let S := laneS esize
  op.saturating && anyLane cnt fun i =>
    let a := getLane n esize i
    let b := getLane m esize i
    let c := getLane d esize i
    match op with
    | .uqadd => outU esize (laneU a + laneU b)
    | .uqsub => outU esize (laneU a - laneU b)
    | .sqadd => outS esize (S a + S b)
    | .sqsub => outS esize (S a - S b)
    | .sqshl => outS esize (shiftInt false (S a) (shAmt b))
    | .uqshl => outU esize (shiftInt false (laneU a) (shAmt b))
    | .sqrshl => outS esize (shiftInt true (S a) (shAmt b))
    | .uqrshl => outU esize (shiftInt true (laneU a) (shAmt b))
    | .sqdmulh => outS esize ((2 * S a * S b) / 2 ^ esize)
    | .sqrdmulh => outS esize ((2 * S a * S b + 2 ^ (esize - 1)) / 2 ^ esize)
    | .sqrdmlah => outS esize ((S c * 2 ^ esize + 2 * S a * S b + 2 ^ (esize - 1)) / 2 ^ esize)
    | .sqrdmlsh => outS esize ((S c * 2 ^ esize - 2 * S a * S b + 2 ^ (esize - 1)) / 2 ^ esize)
    | _ => false

def vec2QC (cnt esize : Nat) (op : Vec2Op) (d n : BitVec 128) : Bool :=
  op.saturating && anyLane cnt fun i =>
    let x := getLane n esize i
    let w := getLane n (2 * esize) i
    match op with
    | .sqxtn => outS esize (laneS (2 * esize) w)
    | .uqxtn => outU esize (laneU w)
    | .sqxtun => outU esize (laneS (2 * esize) w)
    | .sqabs => outS esize (laneS esize x).natAbs
    | .sqneg => outS esize (-(laneS esize x))
    | .suqadd => outS esize (laneS esize (getLane d esize i) + laneU x)
    | .usqadd => outU esize (laneU (getLane d esize i) + laneS esize x)
    | _ => false

def vshiftQC (cnt esize : Nat) (op : VecShiftOp) (sh : Nat) (n : BitVec 128) : Bool :=
  op.saturating && anyLane cnt fun i =>
    let x := getLane n esize i
    let w := getLane n (2 * esize) i
    match op with
    | .sqshlu => outU esize (laneS esize x * 2 ^ sh)
    | .sqshl => outS esize (laneS esize x * 2 ^ sh)
    | .uqshl => outU esize (laneU x * 2 ^ sh)
    | .sqshrn => outS esize (laneS (2 * esize) w / 2 ^ sh)
    | .uqshrn => outU esize (laneU w / 2 ^ sh)
    | .sqrshrn => outS esize (rshr (laneS (2 * esize) w) sh)
    | .uqrshrn => outU esize (rshr (laneU w) sh)
    | .sqshrun => outU esize (laneS (2 * esize) w / 2 ^ sh)
    | .sqrshrun => outU esize (rshr (laneS (2 * esize) w) sh)
    | _ => false

/-- Saturation of a doubling multiply-(accumulate) long: of the product, or of
the accumulation. -/
def dmlQC (esize : Nat) (sub acc : Bool) (a b : Int) (d : BitVec 64) : Bool :=
  let W := 2 * esize
  let p := 2 * a * b
  let ps := laneS W (satS W p)
  let c := laneS W d
  outS W p || (acc && outS W (if sub then c - ps else c + ps))

def vlongQC (cnt esize : Nat) (q : Bool) (op : VecLongOp) (d n m : BitVec 128) : Bool :=
  let half (v : BitVec 128) : BitVec 128 := if q then v >>> 64 else v
  op.saturating && anyLane cnt fun i =>
    let a := laneS esize (getLane (half n) esize i)
    let b := laneS esize (getLane (half m) esize i)
    let c := getLane d (2 * esize) i
    match op with
    | .sqdmull => dmlQC esize false false a b c
    | .sqdmlal => dmlQC esize false true a b c
    | .sqdmlsl => dmlQC esize true true a b c
    | _ => false

def velemQC (cnt esize : Nat) (q : Bool) (op : VecElemOp) (index : Nat) (d n m : BitVec 128) :
    Bool :=
  let e := laneS esize (getLane m esize index)
  let src := if q then n >>> 64 else n
  op.saturating && anyLane cnt fun i =>
    let x := laneS esize (getLane n esize i)
    let c := laneS esize (getLane d esize i)
    let xl := laneS esize (getLane src esize i)
    let dl := getLane d (2 * esize) i
    match op with
    | .sqdmulh => outS esize ((2 * x * e) / 2 ^ esize)
    | .sqrdmulh => outS esize ((2 * x * e + 2 ^ (esize - 1)) / 2 ^ esize)
    | .sqrdmlah => outS esize ((c * 2 ^ esize + 2 * x * e + 2 ^ (esize - 1)) / 2 ^ esize)
    | .sqrdmlsh => outS esize ((c * 2 ^ esize - 2 * x * e + 2 ^ (esize - 1)) / 2 ^ esize)
    | .sqdmull => dmlQC esize false false xl e dl
    | .sqdmlal => dmlQC esize false true xl e dl
    | .sqdmlsl => dmlQC esize true true xl e dl
    | _ => false

/-- Lane counts: narrowing and widening ops have 64 / esize lanes. -/
def Vec2Op.narrow (op : Vec2Op) : Bool := op == .sqxtn || op == .uqxtn || op == .sqxtun
def VecShiftOp.narrow (op : VecShiftOp) : Bool :=
  op == .sqshrn || op == .uqshrn || op == .sqrshrn || op == .uqrshrn || op == .sqshrun ||
  op == .sqrshrun
def VecElemOp.long (op : VecElemOp) : Bool := op == .sqdmull || op == .sqdmlal || op == .sqdmlsl

/-- The QC flag of a one-lane (scalar) form of a vector instruction. -/
def scalarQC (i : Instr) (s : State) : Bool :=
  match i with
  | .vec3 _ e op rm rn rd => vec3QC 1 e op (s.vreg rd) (s.vreg rn) (s.vreg rm)
  | .vec2 _ e op rn rd => vec2QC 1 e op (s.vreg rd) (s.vreg rn)
  | .vshift _ e op sh rn _ => vshiftQC 1 e op sh (s.vreg rn)
  | .vlong q e op rm rn rd => vlongQC 1 e q op (s.vreg rd) (s.vreg rn) (s.vreg rm)
  | .velem q e op index rm rn rd => velemQC 1 e q op index (s.vreg rd) (s.vreg rn) (s.vreg rm)
  | _ => false

/-- Execute one decoded instruction (`w` is its encoding, used for fault
reports). Updates `PC`. -/
def exec (w : BitVec 32) (i : Instr) (s : State) : State :=
  match i with
  | .unpredictable => s.fault (.unpredictable w)
  -- Data processing — immediate
  | .pcRel page imm rd =>
    let base := if page then s.pc &&& ~~~0xFFF else s.pc
    (s.setX rd (base + imm)).nextPC
  | .addSubImm sf sub setF imm rn rd =>
    let rf := addSub sf sub (s.xsp rn) imm sub
    (if setF then (s.setX rd rf.1).setFlags rf.2 else s.setXSP rd rf.1).nextPC
  | .logicImm sf op imm rn rd =>
    (logicWrite s sf op (logicCompute op (s.x rn) imm) rd true).nextPC
  | .moveWide sf op pos imm16 rd =>
    let v : BitVec 64 := imm16.setWidth 64 <<< pos
    let r := match op with
      | .movz => v
      | .movn => ~~~v
      | .movk => (s.x rd &&& ~~~((0xFFFF : BitVec 64) <<< pos)) ||| v
    (s.setX rd (trunc sf r)).nextPC
  | .bitfield sf op r sImm wmask tmask rn rd =>
    let res := sized sf fun n =>
      bitfieldCompute op ((s.x rd).setWidth n) ((s.x rn).setWidth n) r sImm
        (wmask.setWidth n) (tmask.setWidth n)
    (s.setX rd res).nextPC
  | .extr sf lsb rm rn rd =>
    let res := sized sf fun n =>
      (((s.x rn).setWidth n ++ (s.x rm).setWidth n) >>> lsb).setWidth n
    (s.setX rd res).nextPC
  -- Data processing — register
  | .logicShift sf op invert shift amount rm rn rd =>
    let op2 := sized sf fun n => shiftReg ((s.x rm).setWidth n) shift amount
    let op2 := if invert then ~~~op2 else op2
    (logicWrite s sf op (logicCompute op (s.x rn) op2) rd false).nextPC
  | .addSubShift sf sub setF shift amount rm rn rd =>
    let op2 := sized sf fun n => shiftReg ((s.x rm).setWidth n) shift amount
    let rf := addSub sf sub (s.x rn) op2 sub
    (if setF then (s.setX rd rf.1).setFlags rf.2 else s.setX rd rf.1).nextPC
  | .addSubExt sf sub setF option shift rm rn rd =>
    let op2 : BitVec 64 := extendReg (s.x rm) option shift
    let rf := addSub sf sub (s.xsp rn) op2 sub
    (if setF then (s.setX rd rf.1).setFlags rf.2 else s.setXSP rd rf.1).nextPC
  | .addSubCarry sf sub setF rm rn rd =>
    let rf := addSub sf sub (s.x rn) (s.x rm) s.flags.c
    (if setF then (s.setX rd rf.1).setFlags rf.2 else s.setX rd rf.1).nextPC
  | .condCmp sf sub useImm imm rm cond nzcv rn =>
    let f :=
      if conditionHolds cond s.flags then
        (addSub sf sub (s.x rn) (if useImm then imm else s.x rm) sub).2
      else NZCV.ofBits nzcv
    (s.setFlags f).nextPC
  | .condSel sf inv inc cond rm rn rd =>
    let r :=
      if conditionHolds cond s.flags then s.x rn
      else
        let v := if inv then ~~~(s.x rm) else s.x rm
        if inc then v + 1 else v
    (s.setX rd (trunc sf r)).nextPC
  | .dp1 sf op rn rd =>
    (s.setX rd (sized sf fun n => dp1Compute op ((s.x rn).setWidth n))).nextPC
  | .dp2 sf op rm rn rd =>
    (s.setX rd (sized sf fun n => dp2Compute op ((s.x rn).setWidth n) ((s.x rm).setWidth n))).nextPC
  | .dp3 sf op rm ra rn rd =>
    (s.setX rd (dp3Compute sf op (s.x rm) (s.x ra) (s.x rn))).nextPC
  -- Branches and system
  | .branch link offset =>
    let s := if link then s.setX 30 (s.pc + 4) else s
    s.setPC (s.pc + offset)
  | .branchCond cond offset =>
    if conditionHolds cond s.flags then s.setPC (s.pc + offset) else s.nextPC
  | .cmpBranch sf nonzero offset rt =>
    if (trunc sf (s.x rt) == 0) != nonzero then s.setPC (s.pc + offset) else s.nextPC
  | .testBranch b nonzero offset rt =>
    if (s.x rt).getLsbD b == nonzero then s.setPC (s.pc + offset) else s.nextPC
  | .branchReg op rn =>
    let target := s.x rn
    let s := if op == .blr then s.setX 30 (s.pc + 4) else s
    s.setPC target
  | .nop => s.nextPC
  | .clrex => { s with excl := none }.nextPC
  | .svc imm => { s with status := .svc imm }.nextPC
  | .brk imm => { s with status := .brk imm }
  | .mrsNZCV rt => (s.setX rt (s.flags.toBits.setWidth 64 <<< 28)).nextPC
  | .msrNZCV rt => (s.setFlags (NZCV.ofBits ((s.x rt).extractLsb' 28 4))).nextPC
  | .mrsFP false rt => (s.setX rt s.fpcr).nextPC
  | .mrsFP true rt => (s.setX rt s.fpsr).nextPC
  | .msrFP false rt => { s with fpcr := s.x rt &&& fpcrWritable }.nextPC
  | .msrFP true rt => { s with fpsr := s.x rt &&& fpsrWritable }.nextPC
  -- Loads and stores
  | .ldstImm size op mode offset rn rt =>
    withAddr s rn mode offset fun s addr => ldstOne s size op addr rt
  | .ldstReg size op option shift rm rn rt =>
    let offset : BitVec 64 := extendReg (s.x rm) option shift
    withAddr s rn .offset offset fun s addr => ldstOne s size op addr rt
  | .ldrLit size op offset rt => (ldstOne s size op (s.pc + offset) rt).nextPC
  | .ldstPair size load signed mode offset rt2 rn rt =>
    withAddr s rn mode offset fun s addr =>
      let a2 := addr + BitVec.ofNat 64 size
      if load then
        let ext := if signed then sextBytes size else id
        let v1 := ext (s.mem.readN addr size)
        let v2 := ext (s.mem.readN a2 size)
        (s.setX rt v1).setX rt2 v2
      else
        let v1 := s.x rt
        let v2 := s.x rt2
        s.setMem ((s.mem.writeN addr size v1).writeN a2 size v2)
  | .ldstExcl size load rs rn rt =>
    if spFault s rn then s.fault .spAlignment else
      let addr := s.xsp rn
      if !atomicAligned addr size then s.fault (.dataAlignment addr) else
      if load then
        { s.setX rt (s.mem.readN addr size) with excl := some (addr, size) }.nextPC
      else
        let ok := s.excl == some (addr, size)
        let s := if ok then s.setMem (s.mem.writeN addr size (s.x rt)) else s
        { s.setX rs (if ok then 0 else 1) with excl := none }.nextPC
  | .ldstOrdered size load rn rt =>
    if spFault s rn then s.fault .spAlignment else
      let addr := s.xsp rn
      if !atomicAligned addr size then s.fault (.dataAlignment addr) else
      (ldstOne s size (if load then .load else .store) addr rt).nextPC
  | .atomic size op rs rn rt =>
    if spFault s rn then s.fault .spAlignment else
      let addr := s.xsp rn
      if !atomicAligned addr size then s.fault (.dataAlignment addr) else
      let old := s.mem.readN addr size
      let new := atomicCompute size op old (zextBytes size (s.x rs))
      ((s.setMem (s.mem.writeN addr size new)).setX rt old).nextPC
  | .cas size rs rn rt =>
    if spFault s rn then s.fault .spAlignment else
      let addr := s.xsp rn
      if !atomicAligned addr size then s.fault (.dataAlignment addr) else
      let old := s.mem.readN addr size
      let s := if old == zextBytes size (s.x rs) then s.setMem (s.mem.writeN addr size (s.x rt))
               else s
      (s.setX rs old).nextPC
  -- SIMD & FP
  | .vldstImm size load mode offset rn rt =>
    withAddr s rn mode offset fun s addr =>
      if load then s.setV rt (s.mem.readV addr size)
      else s.setMem (s.mem.writeV addr size (s.vreg rt))
  | .vldstReg size load option shift rm rn rt =>
    let offset : BitVec 64 := extendReg (s.x rm) option shift
    withAddr s rn .offset offset fun s addr =>
      if load then s.setV rt (s.mem.readV addr size)
      else s.setMem (s.mem.writeV addr size (s.vreg rt))
  | .vldrLit size offset rt => (s.setV rt (s.mem.readV (s.pc + offset) size)).nextPC
  | .vldstPair size load mode offset rt2 rn rt =>
    withAddr s rn mode offset fun s addr =>
      let a2 := addr + BitVec.ofNat 64 size
      if load then
        let v1 := s.mem.readV addr size
        let v2 := s.mem.readV a2 size
        (s.setV rt v1).setV rt2 v2
      else
        s.setMem ((s.mem.writeV addr size (s.vreg rt)).writeV a2 size (s.vreg rt2))
  | .fmovGen toGpr size top rn rd =>
    if toGpr then
      let v := s.vreg rn
      let r := if top then v.extractLsb' 64 64 else zextBytes size (v.setWidth 64)
      (s.setX rd r).nextPC
    else
      let x := s.x rn
      let r := if top then x ++ (s.vreg rd).setWidth 64
               else (zextBytes size x).setWidth 128
      (s.setV rd r).nextPC
  | .vmovImm q op imm rd =>
    let imm128 : BitVec 128 := if q then imm ++ imm else imm.setWidth 128
    let r := match op with
      | 0 => imm128
      | 1 => vtrunc q (s.vreg rd ||| imm128)
      | _ => vtrunc q (s.vreg rd &&& ~~~imm128)
    (s.setV rd r).nextPC
  | .dupGen q esize rn rd =>
    (s.setV rd (mkVec q esize fun _ => s.x rn)).nextPC
  | .dupElem q esize index rn rd =>
    let e := getLane (s.vreg rn) esize index
    (s.setV rd (mkVec q esize fun _ => e)).nextPC
  | .insGen esize index rn rd =>
    (s.setV rd (setLane (s.vreg rd) esize index (s.x rn))).nextPC
  | .insElem esize dst src rn rd =>
    (s.setV rd (setLane (s.vreg rd) esize dst (getLane (s.vreg rn) esize src))).nextPC
  | .movToGen sf signed esize index rn rd =>
    let e := getLane (s.vreg rn) esize index
    let r := if signed then trunc sf (sextLane esize e) else e
    (s.setX rd r).nextPC

  | .vec3 q esize op rm rn rd =>
    satOp (vec3QC (lanes q esize) esize op (s.vreg rd) (s.vreg rn) (s.vreg rm)) s fun s =>
    (s.setV rd (vec3Extra q esize op (s.vreg rd) (s.vreg rn) (s.vreg rm))).nextPC
  | .vec2 q esize op rn rd =>
    satOp (vec2QC (if op.narrow then 64 / esize else lanes q esize) esize op (s.vreg rd)
      (s.vreg rn)) s fun s =>
    (s.setV rd (vec2Compute q esize op (s.vreg rd) (s.vreg rn))).nextPC
  | .vreduce q esize op rn rd => (s.setV rd (vreduceCompute q esize op (s.vreg rn))).nextPC
  | .addpScalar rn rd =>
    (s.setV rd ((getLane (s.vreg rn) 64 0 + getLane (s.vreg rn) 64 1).setWidth 128)).nextPC
  | .vperm q esize op rm rn rd =>
    (s.setV rd (vpermCompute q esize op (s.vreg rn) (s.vreg rm))).nextPC
  | .vext q pos rm rn rd => (s.setV rd (vextCompute q pos (s.vreg rn) (s.vreg rm))).nextPC
  | .vtbl q nregs tbx rm rn rd => (s.setV rd (vtblCompute q nregs tbx s rm rn rd)).nextPC
  | .vshift q esize op sh rn rd =>
    satOp (vshiftQC (if op.narrow then 64 / esize else lanes q esize) esize op sh (s.vreg rn)) s
      fun s =>
    (s.setV rd (vshiftCompute q esize op sh (s.vreg rd) (s.vreg rn))).nextPC
  | .scalar bits rd inner =>
    let s1 := exec w inner s
    let s1 := s1.setV rd (s1.vreg rd &&& (BitVec.allOnes 128 >>> (128 - bits)))
    -- QC from the one significant lane only.
    let qc := BitVec.ofNat 64 QC
    { s1 with fpsr := (s1.fpsr &&& ~~~qc) ||| (s.fpsr &&& qc) ||| (if scalarQC inner s then qc else 0) }
  | .vlong q esize op rm rn rd =>
    satOp (vlongQC (64 / esize) esize q op (s.vreg rd) (s.vreg rn) (s.vreg rm)) s fun s =>
    (s.setV rd (vlongCompute q esize op (s.vreg rd) (s.vreg rn) (s.vreg rm))).nextPC
  | .velem q esize op index rm rn rd =>
    satOp (velemQC (if op.long then 64 / esize else lanes q esize) esize q op index (s.vreg rd)
      (s.vreg rn) (s.vreg rm)) s fun s =>
    (s.setV rd (velemCompute q esize op index (s.vreg rd) (s.vreg rn) (s.vreg rm))).nextPC
  | .crypto op rm rn rd =>
    let d := s.vreg rd
    let n := s.vreg rn
    let m := s.vreg rm
    let r : BitVec 128 := match op with
      | .aese => Crypto.subBytes (Crypto.shiftRows (d ^^^ n))
      | .aesd => Crypto.invSubBytes (Crypto.invShiftRows (d ^^^ n))
      | .aesmc => Crypto.mixColumns n
      | .aesimc => Crypto.invMixColumns n
      | .sha1c => Crypto.sha1hash Crypto.choose d (n.setWidth 32) m
      | .sha1p => Crypto.sha1hash Crypto.parity d (n.setWidth 32) m
      | .sha1m => Crypto.sha1hash Crypto.majority d (n.setWidth 32) m
      | .sha1su0 => Crypto.sha1su0 d n m
      | .sha1h => ((n.setWidth 32).rotateLeft 30).setWidth 128
      | .sha1su1 => Crypto.sha1su1 d n
      | .sha256h => Crypto.sha256hash d n m true
      | .sha256h2 => Crypto.sha256hash n d m false
      | .sha256su0 => Crypto.sha256su0 d n
      | .sha256su1 => Crypto.sha256su1 d n m
      | .sha512h => Crypto.sha512h d n m
      | .sha512h2 => Crypto.sha512h2 d n m
      | .sha512su0 => Crypto.sha512su0 d n
      | .sha512su1 => Crypto.sha512su1 d n m
      | .rax1 => Crypto.of64 (Crypto.lo64 n ^^^ (Crypto.lo64 m).rotateLeft 1)
          (Crypto.hi64 n ^^^ (Crypto.hi64 m).rotateLeft 1)
    (s.setV rd r).nextPC
  | .eor3 bcax rm ra rn rd =>
    let r := if bcax then s.vreg rn ^^^ (s.vreg rm &&& ~~~(s.vreg ra))
      else s.vreg rn ^^^ s.vreg rm ^^^ s.vreg ra
    (s.setV rd r).nextPC
  | .xar imm rm rn rd =>
    let t := s.vreg rn ^^^ s.vreg rm
    (s.setV rd (Crypto.of64 ((Crypto.lo64 t).rotateRight imm) ((Crypto.hi64 t).rotateRight imm))).nextPC
  | .pmull q wide rm rn rd =>
    let src (v : BitVec 128) : BitVec 128 := if q then v >>> 64 else v
    let n := src (s.vreg rn)
    let m := src (s.vreg rm)
    let r := if wide then BitVec.ofNat 128 (Crypto.clmul (Crypto.lo64 n).toNat (Crypto.lo64 m).toNat 64)
      else mkVec true 16 fun i =>
        BitVec.ofNat 64 (Crypto.clmul (getLane n 8 i).toNat (getLane m 8 i).toNat 8)
    (s.setV rd r).nextPC
  | .vdot q signed rm rn rd =>
    (s.setV rd (vdotCompute q signed (s.vreg rd) (s.vreg rn) (s.vreg rm))).nextPC
  | .vldstMulti q esize load rpt selem wback rm rn rt =>
    if spFault s rn then s.fault .spAlignment else
      let addr := s.xsp rn
      let s := ldstMulti s q esize load rpt selem addr rt
      let total := BitVec.ofNat 64 ((if q then 16 else 8) * rpt * selem)
      let s := if wback then s.setXSP rn (addr + (if rm = 31 then total else s.x rm)) else s
      s.nextPC
  | .vldstLane q load replicate selem esize index wback rm rn rt =>
    if spFault s rn then s.fault .spAlignment else
      let addr := s.xsp rn
      let ebytes := esize / 8
      -- Element `k` of the structure is register `rt + k`, at `addr + k * ebytes`.
      let s := (List.range selem).foldl (fun s k =>
        let t := rt + BitVec.ofNat 5 k
        let a := addr + BitVec.ofNat 64 (k * ebytes)
        if replicate then
          let e := s.mem.readN a ebytes
          s.setV t (mkVec q esize fun _ => e)
        else if load then s.setV t (setLane (s.vreg t) esize index (s.mem.readN a ebytes))
        else s.setMem (s.mem.writeN a ebytes (getLane (s.vreg t) esize index))) s
      let s := if wback then
          s.setXSP rn (addr + (if rm = 31 then BitVec.ofNat 64 (selem * ebytes) else s.x rm)) else s
      s.nextPC
  | .fp1 N op rn rd => fpOp w s fun c =>
    let x := fpArg (s.vreg rn) N
    let r : Nat × Nat := match op with
      | .fmov => (x, 0)
      | .fabs => (FP.abs N x, 0)
      | .fneg => (FP.neg N x, 0)
      | .fsqrt => FP.sqrtC c N x
      | .fcvt M => FP.convertC c N M c.rm x
      | .frint mode => FP.roundToIntegralC c N mode false x
      | .frintx => FP.roundToIntegralC c N c.rm true x
      | .frinti => FP.roundToIntegralC c N c.rm false x
      | .frintN xm k => FP.roundIntNC c N (if xm then c.rm else .z) k x
    let width := match op with
      | .fcvt M => M
      | _ => N
    (r.2, (s.setV rd (fpRes width r.1)).nextPC)
  | .fp2 N op rm rn rd => fpOp w s fun c =>
    let x := fpArg (s.vreg rn) N
    let y := fpArg (s.vreg rm) N
    let r : Nat × Nat := match op with
      | .fadd => FP.addC c N x y
      | .fsub => FP.subC c N x y
      | .fmul => FP.mulC c N false x y
      | .fnmul => let p := FP.mulC c N false x y; (FP.neg N p.1, p.2)
      | .fdiv => FP.divC c N x y
      | .fmax => FP.maxMinC c N true x y
      | .fmin => FP.maxMinC c N false x y
      | .fmaxnm => FP.maxMinNumC c N true x y
      | .fminnm => FP.maxMinNumC c N false x y
    (r.2, (s.setV rd (fpRes N r.1)).nextPC)
  | .fp3 N o1 o0 ra rm rn rd => fpOp w s fun c =>
    let a := fpArg (s.vreg ra) N
    let x := fpArg (s.vreg rn) N
    let y := fpArg (s.vreg rm) N
    let x := if o0 != o1 then FP.neg N x else x
    let a := if o1 then FP.neg N a else a
    let r := FP.mulAddC c N a x y
    (r.2, (s.setV rd (fpRes N r.1)).nextPC)
  | .fcmp N signal zero rm rn => fpOp w s fun c =>
    let x := fpArg (s.vreg rn) N
    let y := if zero then 0 else fpArg (s.vreg rm) N
    let r := FP.compareC c N signal x y
    (r.2, (s.setFlags r.1).nextPC)
  | .fccmp N signal cond nzcv rm rn => fpOp w s fun c =>
    let x := fpArg (s.vreg rn) N
    let y := fpArg (s.vreg rm) N
    let r := if conditionHolds cond s.flags then FP.compareC c N signal x y
      else (NZCV.ofBits nzcv, 0)
    (r.2, (s.setFlags r.1).nextPC)
  | .fcsel N cond rm rn rd =>
    let v := if conditionHolds cond s.flags then s.vreg rn else s.vreg rm
    (s.setV rd (fpRes N v.toNat)).nextPC
  | .fmovImm N imm8 rd => (s.setV rd (fpRes N (FP.expandImm N imm8))).nextPC
  | .fcvtToInt sf N signed mode fb rn rd => fpOp w s fun c =>
    let size := if sf then 64 else 32
    let r := FP.toIntC c N mode signed size fb (fpArg (s.vreg rn) N)
    (r.2, (s.setX rd (BitVec.ofNat 64 (r.1 % (2 ^ size : Nat) : Int).toNat)).nextPC)
  | .intToFP sf N signed fb rn rd => fpOp w s fun c =>
    let size := if sf then 64 else 32
    let u : Nat := (s.x rn).toNat % 2 ^ size
    let r := FP.ofIntC c N c.rm fb (laneInt signed size u)
    (r.2, (s.setV rd (fpRes N r.1)).nextPC)
  | .fvec3 q N op rm rn rd => fpOp w s fun c =>
    let r := fvec3Compute c q N op (s.vreg rd) (s.vreg rn) (s.vreg rm)
    (r.2, (s.setV rd r.1).nextPC)
  | .fvec2 q scalar N op rn rd => fpOp w s fun c =>
    let r := fvec2Compute c q scalar N op (s.vreg rn)
    (r.2, (s.setV rd r.1).nextPC)
  | .fvecElem q N op index rm rn rd => fpOp w s fun c =>
    let e := flane (s.vreg rm) N index
    let d := s.vreg rd
    let n := s.vreg rn
    let r := mkVecF q N fun i => fbin c N op (flane d N i) (flane n N i) e
    (r.2, (s.setV rd r.1).nextPC)
  | .fscalar3 N op index rm rn rd => fpOp w s fun c =>
    let y := match index with
      | some k => flane (s.vreg rm) N k
      | none => flane (s.vreg rm) N 0
    let r := fbin c N op (flane (s.vreg rd) N 0) (flane (s.vreg rn) N 0) y
    (r.2, (s.setV rd (BitVec.ofNat 128 r.1)).nextPC)
  | .fmlal q sub top index rm rn rd => fpOp w s fun c =>
    let r := fmlalCompute c q sub top index (s.vreg rd) (s.vreg rn) (s.vreg rm)
    (r.2, (s.setV rd r.1).nextPC)
  | .fcmla q N rot rm rn rd => fpOp w s fun c =>
    let r := fcmlaCompute c q N rot (s.vreg rd) (s.vreg rn) (s.vreg rm)
    (r.2, (s.setV rd r.1).nextPC)
  | .fcadd q N rot270 rm rn rd => fpOp w s fun c =>
    let r := fcaddCompute c q N rot270 (s.vreg rn) (s.vreg rm)
    (r.2, (s.setV rd r.1).nextPC)
  | .fjcvtzs rn rd => fpOp w s fun c =>
    let r := FP.toFixedJSC c (fpArg (s.vreg rn) 64)
    (r.2.2, ((s.setX rd (BitVec.ofNat 64 r.1)).setFlags ⟨false, r.2.1, false, false⟩).nextPC)
  | .fcvtnl q narrow W rn rd => fpOp w s fun c =>
    let r := fcvtnlCompute c q narrow W (s.vreg rd) (s.vreg rn)
    (r.2, (s.setV rd r.1).nextPC)
  | .fcvtxn q scalar rn rd => fpOp w s fun c =>
    let r := fcvtxnCompute c q scalar (s.vreg rd) (s.vreg rn)
    (r.2, (s.setV rd r.1).nextPC)
  | .freduce q pairwise N op rn rd => fpOp w s fun c =>
    let r := freduceCompute c q pairwise N op (s.vreg rn)
    (r.2, (s.setV rd r.1).nextPC)
  | .dupScalar esize index rn rd =>
    (s.setV rd ((getLane (s.vreg rn) esize index).setWidth 128)).nextPC
  | .crc32 size castagnoli rm rn rd =>
    (s.setX rd (crc32Update castagnoli (s.x rn) (s.x rm) size)).nextPC

end M1
