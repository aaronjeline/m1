/-
  IEEE 754 binary16 / binary32 / binary64 arithmetic as specified by the Arm ARM
  pseudocode (FPUnpack, FPRoundBase, FPProcessNaNs, FPAdd, FPMul, FPDiv,
  FPMulAdd, FPSqrt, FPMax/FPMin(Num), FPCompare, FPConvert, FPToFixed,
  FixedToFP, FPRoundInt, ...), under any FPCR setting the M1 supports:
  rounding mode (RMode), flush-to-zero (FZ, FZ16), default NaN (DN) and the
  alternative half-precision format (AHP).

  Every operation computes the exact real result (as a rational) and rounds
  it once, so the results are correctly rounded by construction. Each
  `...C` operation takes the controls (`Ctl`) and returns the result encoding
  together with the floating-point exceptions it raises, as FPSR cumulative
  flag bits (`IOC`, `DZC`, `OFC`, `UFC`, `IXC`, `IDC`).

  The plain operations (`add`, `mulAdd`, ...) are the same operations under
  the default controls (round to nearest even, no flush-to-zero, no default
  NaN, IEEE half precision), which is how macOS runs every thread.

  Floating-point values are passed as `Nat`s holding the `N`-bit encoding
  (`N = 16`, `32` or `64`).
-/
import M1.Bits

namespace M1.FP

/-- Rounding modes. `odd` (round to odd) is used only by `FCVTXN`. -/
inductive Rounding where
  /-- to nearest, ties to even -/
  | n
  /-- towards +∞ -/
  | p
  /-- towards -∞ -/
  | m
  /-- towards zero -/
  | z
  /-- to nearest, ties away from zero -/
  | a
  /-- to odd -/
  | odd
deriving DecidableEq, Repr, Inhabited

/-- The FPCR controls that affect floating-point results. -/
structure Ctl where
  /-- FPCR.RMode -/
  rm : Rounding := .n
  /-- FPCR.FZ (single and double precision) -/
  fz : Bool := false
  /-- FPCR.FZ16 (half precision) -/
  fz16 : Bool := false
  /-- FPCR.DN -/
  dn : Bool := false
  /-- FPCR.AHP (conversions only) -/
  ahp : Bool := false
  /-- FPCR.UFE: with the underflow trap enabled, a tiny result signals
  underflow even when exact. -/
  ufe : Bool := false
deriving DecidableEq, Repr, Inhabited

/-! FPSR cumulative exception flags. -/
def IOC : Nat := 1
def DZC : Nat := 2
def OFC : Nat := 4
def UFC : Nat := 8
def IXC : Nat := 16
def IDC : Nat := 128

def ebits (N : Nat) : Nat := if N = 16 then 5 else if N = 32 then 8 else 11
def fbits (N : Nat) : Nat := if N = 16 then 10 else if N = 32 then 23 else 52
def bias (N : Nat) : Nat := 2 ^ (ebits N - 1) - 1

def signBit (N : Nat) (s : Bool) : Nat := if s then 2 ^ (N - 1) else 0
def zeroBits (N : Nat) (s : Bool) : Nat := signBit N s
def infBits (N : Nat) (s : Bool) : Nat := signBit N s + (2 ^ ebits N - 1) * 2 ^ fbits N
def maxNormal (N : Nat) (s : Bool) : Nat := signBit N s + (2 ^ ebits N - 1) * 2 ^ fbits N - 1
def defaultNaN (N : Nat) : Nat := (2 ^ ebits N - 1) * 2 ^ fbits N + 2 ^ (fbits N - 1)
def quiet (N : Nat) (x : Nat) : Nat := x ||| 2 ^ (fbits N - 1)
def neg (N : Nat) (x : Nat) : Nat := x ^^^ 2 ^ (N - 1)
def abs (N : Nat) (x : Nat) : Nat := x % 2 ^ (N - 1)

/-- Classification of an encoding. `num s m e` has value `±m * 2^e`, `m > 0`. -/
inductive Val where
  | zero (s : Bool)
  | inf (s : Bool)
  | nan (signalling : Bool)
  | num (s : Bool) (m : Nat) (e : Int)

def unpack (N : Nat) (x : Nat) : Val :=
  let F := fbits N
  let E := ebits N
  let s := x.testBit (N - 1)
  let ex := (x >>> F) % 2 ^ E
  let fr := x % 2 ^ F
  if ex == 0 then
    if fr == 0 then .zero s else .num s fr (1 - (bias N : Int) - F)
  else if ex == 2 ^ E - 1 then
    if fr == 0 then .inf s else .nan (!fr.testBit (F - 1))
  else .num s (fr + 2 ^ F) ((ex : Int) - bias N - F)

/-- FPUnpackBase: `fz` flushes denormal inputs to zero (raising IDC except for
half precision); `ahp` reads half precision in the alternative format, where
the top exponent encodes ordinary numbers. -/
def unpackF (fz ahp : Bool) (N : Nat) (x : Nat) : Val × Nat :=
  let F := fbits N
  let E := ebits N
  let ex := (x >>> F) % 2 ^ E
  let fr := x % 2 ^ F
  if fz && ex == 0 && fr != 0 then (.zero (x.testBit (N - 1)), if N = 16 then 0 else IDC)
  else if ahp && N = 16 && ex == 2 ^ E - 1 then
    (.num (x.testBit (N - 1)) (fr + 2 ^ F) ((ex : Int) - bias N - F), 0)
  else (unpack N x, 0)

theorem unpackF_false (N x : Nat) : unpackF false false N x = (unpack N x, 0) := by
  simp [unpackF]

/-- The flush-to-zero control that applies to format `N`. -/
def Ctl.fzN (c : Ctl) (N : Nat) : Bool := if N = 16 then c.fz16 else c.fz

/-- FPUnpack (arithmetic): AHP is ignored. -/
def unp (c : Ctl) (N : Nat) (x : Nat) : Val × Nat := unpackF (c.fzN N) false N x

/-- `n * 2^k ≥ d` -/
def geScaled (n : Nat) (k : Int) (d : Nat) : Bool :=
  if 0 ≤ k then n <<< k.toNat ≥ d else n ≥ d <<< (-k).toNat

/-- FPRoundBase: round the positive value `num / den * 2^e`, with sign `s`, to
format `N` in rounding mode `mode`. Returns the encoding and the exceptions
raised. `fz` flushes results that are tiny before rounding to zero (with UFC);
`ahp` selects the alternative half-precision format. -/
def roundF (fz ahp ufe : Bool) (mode : Rounding) (N : Nat) (s : Bool) (num den : Nat) (e : Int) :
    Nat × Nat :=
  let F := fbits N
  let B : Int := bias N
  let minExp : Int := 1 - B
  -- L = ⌊log₂ (num / den * 2^e)⌋
  let L0 : Int := (num.log2 : Int) - den.log2 + e
  let L := if geScaled num (e - L0) den then L0 else L0 - 1
  if fz && L < minExp then (zeroBits N s, UFC) else
  let k := max (L - F) (minExp - F)
  let d := e - k
  let nn := if 0 ≤ d then num <<< d.toNat else num
  let dd := if 0 ≤ d then den else den <<< (-d).toNat
  let q := nn / dd
  let r := nn % dd
  -- Underflow: tiny before rounding, and inexact (or the trap is enabled).
  let uf := if L < minExp && (r != 0 || ufe) then UFC else 0
  let up := match mode with
    | .n => 2 * r > dd || (2 * r == dd && q % 2 == 1)
    | .a => 2 * r ≥ dd
    | .p => r != 0 && !s
    | .m => r != 0 && s
    | .z | .odd => false
  let q := if up then q + 1 else q
  let q := if mode == .odd && r != 0 then q ||| 1 else q
  -- Normal: biased exponent k + F + B with implicit bit in q; subnormal:
  -- k + F + B - 1 = 0. A carry out of q moves into the exponent.
  let bits := (k + F + B - 1).toNat * 2 ^ F + q
  let ix := if r != 0 then IXC else 0
  if N != 16 || !ahp then
    if bits ≥ (2 ^ ebits N - 1) * 2 ^ F then
      let toInf := match mode with
        | .n | .a => true
        | .p => !s
        | .m => s
        | .z | .odd => false
      (if toInf then infBits N s else maxNormal N s, uf ||| OFC ||| IXC)
    else (signBit N s + bits, uf ||| ix)
  else
    -- Alternative half precision: no infinities; overflow is invalid.
    if bits ≥ 2 ^ ebits N * 2 ^ F then (signBit N s + 2 ^ (N - 1) - 1, uf ||| IOC)
    else (signBit N s + bits, uf ||| ix)

/-- FPRound under the controls `c` (AHP ignored), in mode `mode`. -/
def rndM (c : Ctl) (mode : Rounding) (N : Nat) (s : Bool) (num den : Nat) (e : Int) : Nat × Nat :=
  roundF (c.fzN N) false c.ufe mode N s num den e

/-- FPRound in the FPCR rounding mode. -/
def rnd (c : Ctl) (N : Nat) (s : Bool) (num den : Nat) (e : Int) : Nat × Nat :=
  rndM c c.rm N s num den e

/-- Round to nearest even under the default controls. -/
def round (N : Nat) (s : Bool) (num den : Nat) (e : Int) : Nat :=
  (roundF false false false .n N s num den e).1

/-- Exact `(sign, magnitude, exponent)` of a zero or finite number. -/
def exact : Val → Bool × Nat × Int
  | .num s m e => (s, m, e)
  | .zero s => (s, 0, 0)
  | _ => (false, 0, 0)

def isZero : Val → Bool
  | .zero _ => true
  | _ => false

def isInf : Val → Bool
  | .inf _ => true
  | _ => false

def isSNaN : Val → Bool
  | .nan true => true
  | _ => false

def isQNaN : Val → Bool
  | .nan false => true
  | _ => false

def sign : Val → Bool
  | .zero s | .inf s | .num s _ _ => s
  | .nan _ => false

def negV : Val → Val
  | .zero s => .zero !s
  | .inf s => .inf !s
  | .num s m e => .num (!s) m e
  | v => v

/-- `±m * 2^e` is an integer. -/
def isExactInt (m : Nat) (e : Int) : Bool := 0 ≤ e || m % 2 ^ (-e).toNat == 0

/-- Exact sum of two signed values `±m * 2^e`. -/
def addExact (a b : Bool × Nat × Int) : Bool × Nat × Int :=
  let (s1, m1, e1) := a
  let (s2, m2, e2) := b
  let e := min e1 e2
  let x : Int := (if s1 then -1 else 1) * ((m1 <<< (e1 - e).toNat : Nat) : Int)
  let y : Int := (if s2 then -1 else 1) * ((m2 <<< (e2 - e).toNat : Nat) : Int)
  let t := x + y
  (t < 0, t.natAbs, e)

/-- FPConvertNaN between formats: the payload below the quiet bit is aligned
at the top of a 51-bit field and truncated to the destination. -/
def convertNaN (N M : Nat) (x : Nat) : Nat :=
  let s := x.testBit (N - 1)
  let frac : Nat := (x % 2 ^ (fbits N - 1)) <<< (51 - (fbits N - 1))
  let payload := frac >>> (51 - (fbits M - 1))
  signBit M s + (2 ^ (ebits M + 1) - 1) * 2 ^ (fbits M - 1) + payload

/-! ### NaN processing -/

/-- FPProcessNaN: quiet a signalling NaN (raising IOC); default NaN when DN. -/
def nanC (c : Ctl) (N : Nat) (x : Nat) : Val → Option (Nat × Nat)
  | .nan true => some (if c.dn then defaultNaN N else quiet N x, IOC)
  | .nan false => some (if c.dn then defaultNaN N else x, 0)
  | _ => none

/-- FPProcessNaNs: signalling NaNs first, then quiet ones, in operand order. -/
def nans2 (c : Ctl) (N : Nat) (x y : Nat) (a b : Val) : Option (Nat × Nat) :=
  match a, b with
  | .nan true, _ => nanC c N x a
  | _, .nan true => nanC c N y b
  | .nan false, _ => nanC c N x a
  | _, .nan false => nanC c N y b
  | _, _ => none

/-- A one-operand operation: unpack, process NaNs, else `k`. -/
def un (c : Ctl) (N : Nat) (x : Nat) (k : Val → Nat × Nat) : Nat × Nat :=
  let (a, f) := unp c N x
  let (r, g) := match nanC c N x a with
    | some r => r
    | none => k a
  (r, f ||| g)

/-- A two-operand operation: unpack both, process NaNs, else `k`. -/
def bin (c : Ctl) (N : Nat) (x y : Nat) (k : Val → Val → Nat × Nat) : Nat × Nat :=
  let (a, f1) := unp c N x
  let (b, f2) := unp c N y
  let (r, g) := match nans2 c N x y a b with
    | some r => r
    | none => k a b
  (r, f1 ||| f2 ||| g)

/-! ### Arithmetic -/

/-- The FPAdd core on non-NaN operands. -/
def addV (c : Ctl) (N : Nat) (a b : Val) : Nat × Nat :=
  match a, b with
  | .inf s1, .inf s2 => if s1 == s2 then (infBits N s1, 0) else (defaultNaN N, IOC)
  | .inf s, _ | _, .inf s => (infBits N s, 0)
  | _, _ =>
    if isZero a && isZero b && sign a == sign b then (zeroBits N (sign a), 0) else
    let (s, m, e) := addExact (exact a) (exact b)
    -- An exact zero sum is +0, or -0 when rounding towards -∞.
    if m == 0 then (zeroBits N (c.rm == .m), 0) else rnd c N s m 1 e

def addC (c : Ctl) (N : Nat) (x y : Nat) : Nat × Nat := bin c N x y (addV c N)
def subC (c : Ctl) (N : Nat) (x y : Nat) : Nat × Nat := bin c N x y fun a b => addV c N a (negV b)

/-- FPMul (`mulx = false`) / FPMulX (`mulx = true`: ∞ × 0 = ±2). -/
def mulC (c : Ctl) (N : Nat) (mulx : Bool) (x y : Nat) : Nat × Nat :=
  bin c N x y fun a b =>
    let s := sign a != sign b
    if (isInf a && isZero b) || (isZero a && isInf b) then
      if mulx then (signBit N s + 2 ^ (ebits N - 1) * 2 ^ fbits N, 0) else (defaultNaN N, IOC)
    else if isInf a || isInf b then (infBits N s, 0)
    else if isZero a || isZero b then (zeroBits N s, 0)
    else
      let (_, m1, e1) := exact a
      let (_, m2, e2) := exact b
      rnd c N s (m1 * m2) 1 (e1 + e2)

def divC (c : Ctl) (N : Nat) (x y : Nat) : Nat × Nat :=
  bin c N x y fun a b =>
    let s := sign a != sign b
    if (isInf a && isInf b) || (isZero a && isZero b) then (defaultNaN N, IOC)
    else if isInf a then (infBits N s, 0)
    else if isZero b then (infBits N s, DZC)
    else if isZero a || isInf b then (zeroBits N s, 0)
    else
      let (_, m1, e1) := exact a
      let (_, m2, e2) := exact b
      rnd c N s m1 m2 (e1 - e2)

/-- The FPMulAdd core (`addend + x * y`, one rounding) on non-NaN operands. -/
def mulAddV (c : Ctl) (N : Nat) (ta t1 t2 : Val) : Nat × Nat :=
  let sp := sign t1 != sign t2
  let infP := isInf t1 || isInf t2
  let zeroP := isZero t1 || isZero t2
  let infZero := (isInf t1 && isZero t2) || (isZero t1 && isInf t2)
  if infZero || (isInf ta && infP && sign ta != sp) then (defaultNaN N, IOC)
  else if (isInf ta && !sign ta) || (infP && !sp) then (infBits N false, 0)
  else if (isInf ta && sign ta) || (infP && sp) then (infBits N true, 0)
  else if isZero ta && zeroP && sign ta == sp then (zeroBits N (sign ta), 0)
  else
    let (_, m1, e1) := exact t1
    let (_, m2, e2) := exact t2
    let (s, m, e) := addExact (exact ta) (sp, m1 * m2, e1 + e2)
    if m == 0 then (zeroBits N (c.rm == .m), 0) else rnd c N s m 1 e

/-- FPProcessNaNs3 followed by the FPMulAdd core. `n1`/`n2` process a NaN
factor (for FPMulAddH they also convert it from the narrower format). -/
def mulAddGen (c : Ctl) (N : Nat) (ta t1 t2 : Val) (addend : Nat)
    (n1 : Val → Option (Nat × Nat)) (n2 : Val → Option (Nat × Nat)) : Nat × Nat :=
  let infZero := (isInf t1 && isZero t2) || (isZero t1 && isInf t2)
  let nan? : Option (Nat × Nat) := match ta, t1, t2 with
    | .nan true, _, _ => nanC c N addend ta
    | _, .nan true, _ => n1 t1
    | _, _, .nan true => n2 t2
    | .nan false, _, _ => nanC c N addend ta
    | _, .nan false, _ => n1 t1
    | _, _, .nan false => n2 t2
    | _, _, _ => none
  -- A quiet-NaN addend with ∞ × 0 is an invalid operation.
  if isQNaN ta && infZero then (defaultNaN N, IOC) else
  match nan? with
  | some r => r
  | none => mulAddV c N ta t1 t2

def mulAddC (c : Ctl) (N : Nat) (addend x y : Nat) : Nat × Nat :=
  let (ta, fa) := unp c N addend
  let (t1, f1) := unp c N x
  let (t2, f2) := unp c N y
  let (r, g) := mulAddGen c N ta t1 t2 addend (nanC c N x) (nanC c N y)
  (r, fa ||| f1 ||| f2 ||| g)

/-- FPMulAddH: `addend + x * y` with an `N`-bit addend and `N/2`-bit factors. -/
def mulAddHC (c : Ctl) (N : Nat) (addend x y : Nat) : Nat × Nat :=
  let H := N / 2
  let (ta, fa) := unp c N addend
  let (t1, f1) := unp c H x
  let (t2, f2) := unp c H y
  let cv (v : Nat) (t : Val) : Option (Nat × Nat) :=
    (nanC c H v t).map fun (r, f) => (convertNaN H N r, f)
  let (r, g) := mulAddGen c N ta t1 t2 addend (cv x) (cv y)
  (r, fa ||| f1 ||| f2 ||| g)

/-- Integer square root (`⌊√n⌋`), bit by bit. -/
def isqrt (n : Nat) : Nat :=
  (List.range (n.log2 / 2 + 1)).reverse.foldl
    (fun r i => let c := r ||| (1 <<< i); if c * c ≤ n then c else r) 0

def sqrtC (c : Ctl) (N : Nat) (x : Nat) : Nat × Nat :=
  un c N x fun
    | .zero s => (zeroBits N s, 0)
    | .inf false => (infBits N false, 0)
    | .num false m e =>
      let (m, e) := if e % 2 == 0 then (m, e) else (2 * m, e - 1)
      -- ⌊√(m·4^K)⌋ has at least F + 3 bits; an odd sticky bit below it
      -- preserves the rounding decision (in every mode) and inexactness.
      let K := fbits N + 3
      let M := m <<< (2 * K)
      let r := isqrt M
      let sticky := if r * r == M then 0 else 1
      rnd c N false (2 * r + sticky) 1 (e / 2 - K - 1)
    | _ => (defaultNaN N, IOC)

/-! ### Comparisons -/

/-- Exponent of a finite value (0 for others). -/
def expOf : Val → Int
  | .num _ _ e => e
  | _ => 0

/-- The signed integer `v / 2^e` (exact when `e ≤ expOf v`); 0 for zeros. -/
def scaled (v : Val) (e : Int) : Int :=
  match v with
  | .num s m e1 => (if s then -1 else 1) * ((m <<< (e1 - e).toNat : Nat) : Int)
  | _ => 0

/-- `a < b` for non-NaN values (exact comparison of the real values). -/
def lt (a b : Val) : Bool :=
  match a, b with
  | .inf sa, .inf sb => sa && !sb
  | .inf sa, _ => sa
  | _, .inf sb => !sb
  | _, _ => let e := min (expOf a) (expOf b); decide (scaled a e < scaled b e)

theorem lt_asymm (a b : Val) (h : lt a b = true) : lt b a = false := by
  cases a <;> cases b <;> simp_all [lt] <;> rw [Int.min_comm] <;> omega

def eq (a b : Val) : Bool := !lt a b && !lt b a

def isNaN : Val → Bool
  | .nan _ => true
  | _ => false

/-- The FPCompare result on two unpacked values, as NZCV: unordered 0011,
equal 0110, less 1000, greater 0010. -/
def compareV (a b : Val) : NZCV :=
  match a, b with
  | .nan _, _ | _, .nan _ => ⟨false, false, true, true⟩
  | _, _ =>
    if eq a b then ⟨false, true, true, false⟩
    else if lt a b then ⟨true, false, false, false⟩
    else ⟨false, false, true, false⟩

/-- FPCompare under the default controls. -/
def compare (N : Nat) (x y : Nat) : NZCV := compareV (unpack N x) (unpack N y)

/-- FPCompare: any NaN raises IOC when `signal` (FCMPE), else only a
signalling one does. -/
def compareC (c : Ctl) (N : Nat) (signal : Bool) (x y : Nat) : NZCV × Nat :=
  let (a, f1) := unp c N x
  let (b, f2) := unp c N y
  let inv := isSNaN a || isSNaN b || (signal && (isNaN a || isNaN b))
  (compareV a b, f1 ||| f2 ||| (if inv then IOC else 0))

/-- FPCompareEQ / GE / GT (false when unordered). -/
def cmpEQ (N : Nat) (x y : Nat) : Bool :=
  let a := unpack N x; let b := unpack N y
  !isNaN a && !isNaN b && eq a b
def cmpGE (N : Nat) (x y : Nat) : Bool :=
  let a := unpack N x; let b := unpack N y
  !isNaN a && !isNaN b && !lt a b
def cmpGT (N : Nat) (x y : Nat) : Bool :=
  let a := unpack N x; let b := unpack N y
  !isNaN a && !isNaN b && lt b a

/-- Kinds of vector comparison. -/
inductive Cmp where
  | eq | ge | gt
deriving DecidableEq, Repr, Inhabited

/-- FPCompareEQ (IOC on a signalling NaN) / GE / GT (IOC on any NaN). -/
def cmpC (c : Ctl) (N : Nat) (k : Cmp) (x y : Nat) : Bool × Nat :=
  let (a, f1) := unp c N x
  let (b, f2) := unp c N y
  let ord := !isNaN a && !isNaN b
  let r := match k with
    | .eq => ord && eq a b
    | .ge => ord && !lt a b
    | .gt => ord && lt b a
  let inv := match k with
    | .eq => isSNaN a || isSNaN b
    | _ => isNaN a || isNaN b
  (r, f1 ||| f2 ||| (if inv then IOC else 0))

/-- FPMax / FPMin. -/
def maxMinC (c : Ctl) (N : Nat) (isMax : Bool) (x y : Nat) : Nat × Nat :=
  bin c N x y fun a b =>
    if isZero a && isZero b then
      (zeroBits N (if isMax then sign a && sign b else sign a || sign b), 0)
    else
      match if lt b a == isMax then a else b with
      | .inf s => (infBits N s, 0)
      | .zero s => (zeroBits N s, 0)
      | .num s m e => rnd c N s m 1 e
      | .nan _ => (defaultNaN N, 0)

/-- FPMaxNum / FPMinNum: a single quiet NaN operand is ignored. -/
def maxMinNumC (c : Ctl) (N : Nat) (isMax : Bool) (x y : Nat) : Nat × Nat :=
  let a := unpack N x
  let b := unpack N y
  let other := infBits N isMax
  let x' := if isQNaN a && !isQNaN b then other else x
  let y' := if isQNaN b && !isQNaN a then other else y
  maxMinC c N isMax x' y'

/-! ### Conversions -/

/-- FPConvert (FCVT, FCVTN, FCVTL, FCVTXN) from format `N` to `M` in mode
`mode`. Conversions ignore FZ16 and honour AHP. -/
def convertC (c : Ctl) (N M : Nat) (mode : Rounding) (x : Nat) : Nat × Nat :=
  let (a, f) := unpackF (if N = 16 then false else c.fz) c.ahp N x
  let altM := M == 16 && c.ahp
  let (r, g) := match a with
    | .nan sn =>
      if altM then (zeroBits M (x.testBit (N - 1)), IOC)
      else (if c.dn then defaultNaN M else convertNaN N M x, if sn then IOC else 0)
    | .inf s => if altM then (signBit M s + 2 ^ (M - 1) - 1, IOC) else (infBits M s, 0)
    | .zero s => (zeroBits M s, 0)
    | .num s m e => roundF (if M = 16 then false else c.fz) c.ahp c.ufe mode M s m 1 e
  (r, f ||| g)

/-- Round `±m * 2^e` to an integer. -/
def roundInt (mode : Rounding) (s : Bool) (m : Nat) (e : Int) : Int :=
  let mag : Nat :=
    if 0 ≤ e then m <<< e.toNat else
      let k := (-e).toNat
      let q := m >>> k
      let r := m % 2 ^ k
      let half := 2 ^ k / 2
      let up := match mode with
        | .n => r > half || (r == half && q % 2 == 1)
        | .a => r ≥ half
        | .z | .odd => false
        | .p => r != 0 && !s
        | .m => r != 0 && s
      if up then q + 1 else q
  if s then -(mag : Int) else mag

/-- FPToFixed: `x * 2^fbits` rounded in `mode` to a `size`-bit integer,
saturating. NaNs give 0; NaNs and out-of-range values raise IOC. -/
def toIntC (c : Ctl) (N : Nat) (mode : Rounding) (signed : Bool) (size fbits : Nat) (x : Nat) :
    Int × Nat :=
  let lo : Int := if signed then -(2 ^ (size - 1)) else 0
  let hi : Int := if signed then 2 ^ (size - 1) - 1 else 2 ^ size - 1
  let (a, f) := unp c N x
  match a with
  | .nan _ => (0, f ||| IOC)
  | .zero _ => (0, f)
  | .inf s => (if s then lo else hi, f ||| IOC)
  | .num s m e =>
    let e := e + (fbits : Int)
    let v := roundInt mode s m e
    if v < lo then (lo, f ||| IOC) else if v > hi then (hi, f ||| IOC)
    else (v, f ||| (if isExactInt m e then 0 else IXC))

/-- FixedToFP (SCVTF / UCVTF): `v / 2^fbits` rounded in mode `mode`. -/
def ofIntC (c : Ctl) (N : Nat) (mode : Rounding) (fbits : Nat) (v : Int) : Nat × Nat :=
  if v == 0 then (zeroBits N false, 0) else rndM c mode N (v < 0) v.natAbs 1 (-(fbits : Int))

/-- FPRoundInt (FRINT{N,P,M,Z,A,X,I}); `exact` (FRINTX) raises IXC when the
value changes. -/
def roundToIntegralC (c : Ctl) (N : Nat) (mode : Rounding) (exact : Bool) (x : Nat) : Nat × Nat :=
  un c N x fun
    | .num s m e =>
      let v := roundInt mode s m e
      let r := if v == 0 then zeroBits N s else round N s v.natAbs 1 0
      (r, if exact && !isExactInt m e then IXC else 0)
    | .zero s => (zeroBits N s, 0)
    | .inf s => (infBits N s, 0)
    | .nan _ => (defaultNaN N, 0)

/-- FPRoundIntN (FRINT32*, FRINT64*): out-of-range values, NaNs and
infinities become the most negative `intsize`-bit integer (with IOC). -/
def roundIntNC (c : Ctl) (N : Nat) (mode : Rounding) (intsize : Nat) (x : Nat) : Nat × Nat :=
  let minInt := round N true (2 ^ (intsize - 1)) 1 0
  let (a, f) := unp c N x
  match a with
  | .num s m e =>
    let v := roundInt mode s m e
    if v < -(2 ^ (intsize - 1) : Int) || v > 2 ^ (intsize - 1) - 1 then (minInt, f ||| IOC)
    else ((if v == 0 then zeroBits N s else round N s v.natAbs 1 0),
      f ||| (if isExactInt m e then 0 else IXC))
  | .zero s => (zeroBits N s, f)
  | _ => (minInt, f ||| IOC)

/-- FJCVTZS: JavaScript conversion of a double to int32 (modulo 2^32, rounding
towards zero), whether it was exact and in range (the Z flag), and the
exceptions raised. -/
def toFixedJSC (c : Ctl) (x : Nat) : Nat × Bool × Nat :=
  let (a, f) := unp c 64 x
  match a with
  | .num s m e =>
    let v := roundInt .z s m e
    let ex := isExactInt m e
    let inRange := -(2 ^ 31 : Int) ≤ v && v ≤ 2 ^ 31 - 1
    ((v % 2 ^ 32).toNat, ex && inRange, f ||| (if !inRange then IOC else if !ex then IXC else 0))
  | .zero s => (0, !s, f)
  | _ => (0, false, f ||| IOC)

/-- VFPExpandImm. -/
def expandImm (N : Nat) (imm8 : Nat) : Nat :=
  let E := ebits N
  let F := fbits N
  let s := imm8.testBit 7
  let b6 := if imm8.testBit 6 then 1 else 0
  let exp := (1 - b6) * 2 ^ (E - 1) + (b6 * (2 ^ (E - 3) - 1)) * 4 + (imm8 >>> 4) % 4
  signBit N s + exp * 2 ^ F + (imm8 % 16) * 2 ^ (F - 4)

/-! ### Estimates and Newton-Raphson steps -/

def two (N : Nat) : Nat := 2 ^ (ebits N - 1) * 2 ^ fbits N
def onePointFive (N : Nat) : Nat := (2 ^ (ebits N - 1) - 1) * 2 ^ fbits N + 2 ^ (fbits N - 1)

/-- FPRecipStepFused (`2 - x*y`) and FPRSqrtStepFused (`(3 - x*y) / 2`),
with a single rounding. -/
def stepFusedC (c : Ctl) (N : Nat) (rsqrt : Bool) (x y : Nat) : Nat × Nat :=
  bin c N (neg N x) y fun a b =>
    if (isInf a && isZero b) || (isZero a && isInf b) then
      (if rsqrt then onePointFive N else two N, 0)
    else if isInf a || isInf b then (infBits N (sign a != sign b), 0)
    else
      let (s1, m1, e1) := exact a
      let (s2, m2, e2) := exact b
      let (s, m, e) := addExact (false, if rsqrt then 3 else 2, 0) (s1 != s2, m1 * m2, e1 + e2)
      if m == 0 then (zeroBits N (c.rm == .m), 0)
      else rnd c N s m 1 (if rsqrt then e - 1 else e)

/-- The 52-bit-wide fraction field (`F` bits, left-aligned) and exponent field. -/
def fracExp (N : Nat) (x : Nat) : Nat × Int :=
  ((x % 2 ^ fbits N) <<< (52 - fbits N), ((x >>> fbits N) % 2 ^ ebits N : Nat))

/-- RecipEstimate: `a` in [256, 512) → estimate in [256, 512]. -/
def recipEstimate (a : Nat) : Nat := (2 ^ 19 / (2 * a + 1) + 1) / 2

/-- RecipSqrtEstimate: `a` in [128, 512) → estimate in [256, 512). -/
def rsqrtEstimate (a : Nat) : Nat :=
  let a := if a < 256 then 2 * a + 1 else ((a >>> 1) <<< 1 + 1) * 2
  -- The largest b ≥ 512 with a (b+1)² < 2^28 (b < 1024 always).
  let b := (List.range 512).foldl (fun b i => if a * (513 + i) * (513 + i) < 2 ^ 28 then 513 + i else b) 512
  (b + 1) / 2

/-- FPRecipEstimate (FRECPE), without FEAT_RPRES. -/
def recipEstC (c : Ctl) (N : Nat) (x : Nat) : Nat × Nat :=
  un c N x fun
    | .inf s => (zeroBits N s, 0)
    | .zero s => (infBits N s, DZC)
    | .num s m e =>
      -- |value| < 2^-(2^(E-1)) overflows.
      if (m : Int) < 2 ^ ((-(2 ^ (ebits N - 1) : Int) - e).toNat) && -(2 ^ (ebits N - 1) : Int) - e > 0
      then
        let toInf := match c.rm with
          | .p => !s
          | .m => s
          | .z => false
          | _ => true
        (if toInf then infBits N s else maxNormal N s, OFC ||| IXC)
      -- With flush-to-zero, results that would be denormal are flushed.
      else if c.fzN N && geScaled m (e - ((bias N : Int) - 1)) 1 then (zeroBits N s, UFC)
      else
      let (frac, ex) := fracExp N x
      let (frac, ex) := if ex == 0 then
          (if frac.testBit 51 then ((frac <<< 1) % 2 ^ 52, ex) else ((frac <<< 2) % 2 ^ 52, -1))
        else (frac, ex)
      let scaled := 256 + frac / 2 ^ 44
      let resExp : Int := 2 * (2 ^ (ebits N - 1) - 1 : Nat) - 1 - ex
      let est := recipEstimate scaled
      let fr := (est % 256) <<< 44
      let (fr, resExp) := if resExp == 0 then (2 ^ 51 + fr / 2, 0)
        else if resExp == -1 then (2 ^ 50 + fr / 4, 0) else (fr, resExp)
      (signBit N s + resExp.toNat * 2 ^ fbits N + fr / 2 ^ (52 - fbits N), 0)
    | .nan _ => (defaultNaN N, 0)

/-- FPRSqrtEstimate (FRSQRTE). -/
def rsqrtEstC (c : Ctl) (N : Nat) (x : Nat) : Nat × Nat :=
  un c N x fun
    | .zero s => (infBits N s, DZC)
    | .inf false => (zeroBits N false, 0)
    | .num false _ _ =>
      let (frac, ex) := fracExp N x
      -- Normalise a subnormal input.
      let (frac, ex) := if ex == 0 then
          let k := 51 - frac.log2  -- leading zeros above bit 51
          (((frac <<< (k + 1)) % 2 ^ 52), -(k : Int))
        else (frac, ex)
      let scaled := if ex % 2 == 0 then 256 + frac / 2 ^ 44 else 128 + frac / 2 ^ 45
      let resExp : Int := ((3 * (2 ^ (ebits N - 1) - 1 : Nat) - 1 : Nat) - ex) / 2
      let est := rsqrtEstimate scaled
      (resExp.toNat * 2 ^ fbits N + ((est % 256) <<< (fbits N - 8)), 0)
    | _ => (defaultNaN N, IOC)

/-- URECPE / URSQRTE on a 32-bit lane. -/
def urecpe (x : Nat) : Nat :=
  if x < 2 ^ 31 then 2 ^ 32 - 1 else (recipEstimate (x / 2 ^ 23 % 256 + 256) % 512) <<< 23
def ursqrte (x : Nat) : Nat :=
  if x < 2 ^ 30 then 2 ^ 32 - 1 else (rsqrtEstimate (x / 2 ^ 23) % 512) <<< 23

/-- FPRecpX (FRECPX). -/
def recpXC (c : Ctl) (N : Nat) (x : Nat) : Nat × Nat :=
  un c N x fun _ =>
    let ex := (x >>> fbits N) % 2 ^ ebits N
    let s := x.testBit (N - 1)
    let e' := if ex == 0 then 2 ^ ebits N - 2 else (2 ^ ebits N - 1) - ex
    (signBit N s + e' * 2 ^ fbits N, 0)

/-! ### The operations under the default controls -/

def add (N : Nat) (x y : Nat) : Nat := (addC {} N x y).1
def sub (N : Nat) (x y : Nat) : Nat := (subC {} N x y).1
def mul (N : Nat) (x y : Nat) : Nat := (mulC {} N false x y).1
def mulx (N : Nat) (x y : Nat) : Nat := (mulC {} N true x y).1
def div (N : Nat) (x y : Nat) : Nat := (divC {} N x y).1
/-- FPMulAdd: `addend + x * y` with a single rounding. -/
def mulAdd (N : Nat) (addend x y : Nat) : Nat := (mulAddC {} N addend x y).1
def sqrt (N : Nat) (x : Nat) : Nat := (sqrtC {} N x).1
def maxMin (N : Nat) (isMax : Bool) (x y : Nat) : Nat := (maxMinC {} N isMax x y).1
def maxMinNum (N : Nat) (isMax : Bool) (x y : Nat) : Nat := (maxMinNumC {} N isMax x y).1
def convert (N M : Nat) (x : Nat) : Nat := (convertC {} N M .n x).1
/-- FCVT{N,A,P,M,Z}{S,U}: float to a `size`-bit integer, saturating; NaN → 0. -/
def toInt (N : Nat) (mode : Rounding) (signed : Bool) (size : Nat) (x : Nat) : Int :=
  (toIntC {} N mode signed size 0 x).1
def ofInt (N : Nat) (v : Int) : Nat := (ofIntC {} N .n 0 v).1

/-! Under the default controls the operations are the plain ones (used to
state specifications of code run under `FPDefault`). -/

theorem fold_add (N x y : Nat) : (addC {} N x y).1 = add N x y := rfl
theorem fold_sub (N x y : Nat) : (subC {} N x y).1 = sub N x y := rfl
theorem fold_mul (N x y : Nat) : (mulC {} N false x y).1 = mul N x y := rfl
theorem fold_mulx (N x y : Nat) : (mulC {} N true x y).1 = mulx N x y := rfl
theorem fold_div (N x y : Nat) : (divC {} N x y).1 = div N x y := rfl
theorem fold_mulAdd (N a x y : Nat) : (mulAddC {} N a x y).1 = mulAdd N a x y := rfl
theorem fold_sqrt (N x : Nat) : (sqrtC {} N x).1 = sqrt N x := rfl
theorem fold_maxMin (N : Nat) (b : Bool) (x y : Nat) : (maxMinC {} N b x y).1 = maxMin N b x y := rfl
theorem fold_maxMinNum (N : Nat) (b : Bool) (x y : Nat) :
    (maxMinNumC {} N b x y).1 = maxMinNum N b x y := rfl
theorem fold_convert (N M x : Nat) : (convertC {} N M .n x).1 = convert N M x := rfl
theorem fold_toInt (N : Nat) (mode : Rounding) (signed : Bool) (size x : Nat) :
    (toIntC {} N mode signed size 0 x).1 = toInt N mode signed size x := rfl
theorem fold_ofInt (N : Nat) (v : Int) : (ofIntC {} N .n 0 v).1 = ofInt N v := rfl

theorem unp_default (N x : Nat) : unp {} N x = (unpack N x, 0) := by
  simp [unp, Ctl.fzN, unpackF_false]

theorem fold_compare (N : Nat) (signal : Bool) (x y : Nat) :
    (compareC {} N signal x y).1 = compare N x y := by
  simp [compareC, compare, unp_default]
theorem fold_cmpEQ (N x y : Nat) : (cmpC {} N .eq x y).1 = cmpEQ N x y := by
  simp [cmpC, cmpEQ, unp_default]
theorem fold_cmpGE (N x y : Nat) : (cmpC {} N .ge x y).1 = cmpGE N x y := by
  simp [cmpC, cmpGE, unp_default]
theorem fold_cmpGT (N x y : Nat) : (cmpC {} N .gt x y).1 = cmpGT N x y := by
  simp [cmpC, cmpGT, unp_default]

end M1.FP
