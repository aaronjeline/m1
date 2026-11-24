/-
  The cryptographic extensions implemented by the M1 (FEAT_AES, FEAT_SHA1,
  FEAT_SHA256, FEAT_SHA512, FEAT_SHA3, FEAT_PMULL), following the Arm ARM
  pseudocode (AESShiftRows, AESSubBytes, AESMixColumns, SHA256hash, ...).
-/
import M1.Bits

namespace M1.Crypto

def sbox : Array Nat := #[99, 124, 119, 123, 242, 107, 111, 197, 48, 1, 103, 43, 254, 215, 171, 118, 202, 130, 201, 125, 250, 89, 71, 240, 173, 212, 162, 175, 156, 164, 114, 192, 183, 253, 147, 38, 54, 63, 247, 204, 52, 165, 229, 241, 113, 216, 49, 21, 4, 199, 35, 195, 24, 150, 5, 154, 7, 18, 128, 226, 235, 39, 178, 117, 9, 131, 44, 26, 27, 110, 90, 160, 82, 59, 214, 179, 41, 227, 47, 132, 83, 209, 0, 237, 32, 252, 177, 91, 106, 203, 190, 57, 74, 76, 88, 207, 208, 239, 170, 251, 67, 77, 51, 133, 69, 249, 2, 127, 80, 60, 159, 168, 81, 163, 64, 143, 146, 157, 56, 245, 188, 182, 218, 33, 16, 255, 243, 210, 205, 12, 19, 236, 95, 151, 68, 23, 196, 167, 126, 61, 100, 93, 25, 115, 96, 129, 79, 220, 34, 42, 144, 136, 70, 238, 184, 20, 222, 94, 11, 219, 224, 50, 58, 10, 73, 6, 36, 92, 194, 211, 172, 98, 145, 149, 228, 121, 231, 200, 55, 109, 141, 213, 78, 169, 108, 86, 244, 234, 101, 122, 174, 8, 186, 120, 37, 46, 28, 166, 180, 198, 232, 221, 116, 31, 75, 189, 139, 138, 112, 62, 181, 102, 72, 3, 246, 14, 97, 53, 87, 185, 134, 193, 29, 158, 225, 248, 152, 17, 105, 217, 142, 148, 155, 30, 135, 233, 206, 85, 40, 223, 140, 161, 137, 13, 191, 230, 66, 104, 65, 153, 45, 15, 176, 84, 187, 22]
def invSbox : Array Nat := #[82, 9, 106, 213, 48, 54, 165, 56, 191, 64, 163, 158, 129, 243, 215, 251, 124, 227, 57, 130, 155, 47, 255, 135, 52, 142, 67, 68, 196, 222, 233, 203, 84, 123, 148, 50, 166, 194, 35, 61, 238, 76, 149, 11, 66, 250, 195, 78, 8, 46, 161, 102, 40, 217, 36, 178, 118, 91, 162, 73, 109, 139, 209, 37, 114, 248, 246, 100, 134, 104, 152, 22, 212, 164, 92, 204, 93, 101, 182, 146, 108, 112, 72, 80, 253, 237, 185, 218, 94, 21, 70, 87, 167, 141, 157, 132, 144, 216, 171, 0, 140, 188, 211, 10, 247, 228, 88, 5, 184, 179, 69, 6, 208, 44, 30, 143, 202, 63, 15, 2, 193, 175, 189, 3, 1, 19, 138, 107, 58, 145, 17, 65, 79, 103, 220, 234, 151, 242, 207, 206, 240, 180, 230, 115, 150, 172, 116, 34, 231, 173, 53, 133, 226, 249, 55, 232, 28, 117, 223, 110, 71, 241, 26, 113, 29, 41, 197, 137, 111, 183, 98, 14, 170, 24, 190, 27, 252, 86, 62, 75, 198, 210, 121, 32, 154, 219, 192, 254, 120, 205, 90, 244, 31, 221, 168, 51, 136, 7, 199, 49, 177, 18, 16, 89, 39, 128, 236, 95, 96, 81, 127, 169, 25, 181, 74, 13, 45, 229, 122, 159, 147, 201, 156, 239, 160, 224, 59, 77, 174, 42, 245, 176, 200, 235, 187, 60, 131, 83, 153, 97, 23, 43, 4, 126, 186, 119, 214, 38, 225, 105, 20, 99, 85, 33, 12, 125]

def byte (v : BitVec 128) (i : Nat) : Nat := ((v >>> (8 * i)).setWidth 8).toNat
def ofBytes (f : Nat → Nat) : BitVec 128 :=
  (List.range 16).foldl (fun acc i => acc ||| (BitVec.ofNat 128 (f i % 256) <<< (8 * i))) 0

def subBytes (v : BitVec 128) : BitVec 128 := ofBytes fun i => sbox[byte v i]!
def invSubBytes (v : BitVec 128) : BitVec 128 := ofBytes fun i => invSbox[byte v i]!
/-- Byte `4c + r` (column `c`, row `r`). -/
def shiftRows (v : BitVec 128) : BitVec 128 :=
  ofBytes fun i => byte v (4 * ((i / 4 + i % 4) % 4) + i % 4)
def invShiftRows (v : BitVec 128) : BitVec 128 :=
  ofBytes fun i => byte v (4 * ((i / 4 + 4 - i % 4) % 4) + i % 4)

/-- Multiplication in GF(2^8) modulo x^8 + x^4 + x^3 + x + 1. -/
def gmul (a b : Nat) : Nat :=
  (List.range 8).foldl (fun (acc : Nat × Nat) i =>
    let (r, a) := acc
    let r := if b.testBit i then r ^^^ a else r
    let a := if a ≥ 128 then ((a <<< 1) ^^^ 0x11b) else a <<< 1
    (r, a)) (0, a) |>.1

def mixWith (m : Array Nat) (v : BitVec 128) : BitVec 128 :=
  ofBytes fun i =>
    let c := i / 4
    let r := i % 4
    (List.range 4).foldl (fun acc k => acc ^^^ gmul m[(k + 4 - r) % 4]! (byte v (4 * c + k))) 0

def mixColumns : BitVec 128 → BitVec 128 := mixWith #[2, 3, 1, 1]
def invMixColumns : BitVec 128 → BitVec 128 := mixWith #[14, 11, 13, 9]

def w32 (v : BitVec 128) (e : Nat) : BitVec 32 := (v >>> (32 * e)).setWidth 32
def of32 (a b c d : BitVec 32) : BitVec 128 := d ++ c ++ b ++ a
def hi64 (v : BitVec 128) : BitVec 64 := (v >>> 64).setWidth 64
def lo64 (v : BitVec 128) : BitVec 64 := v.setWidth 64
def of64 (lo hi : BitVec 64) : BitVec 128 := hi ++ lo

def choose (x y z : BitVec 32) : BitVec 32 := ((y ^^^ z) &&& x) ^^^ z
def parity (x y z : BitVec 32) : BitVec 32 := x ^^^ y ^^^ z
def majority (x y z : BitVec 32) : BitVec 32 := (x &&& y) ||| ((x ||| y) &&& z)

/-- SHA1C / SHA1P / SHA1M. -/
def sha1hash (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) (x0 : BitVec 128)
    (y0 : BitVec 32) (w : BitVec 128) : BitVec 128 :=
  let (x, _) := (List.range 4).foldl (fun (acc : BitVec 128 × BitVec 32) e =>
    let (x, y) := acc
    let t := f (w32 x 1) (w32 x 2) (w32 x 3)
    let y := y + (w32 x 0).rotateLeft 5 + t + w32 w e
    let x := of32 (w32 x 0) ((w32 x 1).rotateLeft 30) (w32 x 2) (w32 x 3)
    -- ROL(Y:X, 32)
    (of32 y (w32 x 0) (w32 x 1) (w32 x 2), w32 x 3)) (x0, y0)
  x

def sigma0 (x : BitVec 32) : BitVec 32 := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
def sigma1 (x : BitVec 32) : BitVec 32 := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

def sha256hash (x0 y0 w : BitVec 128) (part1 : Bool) : BitVec 128 :=
  let (x, y) := (List.range 4).foldl (fun (acc : BitVec 128 × BitVec 128) e =>
    let (x, y) := acc
    let chs := choose (w32 y 0) (w32 y 1) (w32 y 2)
    let maj := majority (w32 x 0) (w32 x 1) (w32 x 2)
    let t := w32 y 3 + sigma1 (w32 y 0) + chs + w32 w e
    let x3 := t + w32 x 3
    let y3 := t + sigma0 (w32 x 0) + maj
    -- ROL(Y:X, 32) on the 256-bit Y:X with the new top words.
    (of32 y3 (w32 x 0) (w32 x 1) (w32 x 2), of32 x3 (w32 y 0) (w32 y 1) (w32 y 2))) (x0, y0)
  if part1 then x else y

def sha1su0 (d n m : BitVec 128) : BitVec 128 := of64 (hi64 d) (lo64 n) ^^^ d ^^^ m

def sha1su1 (d n : BitVec 128) : BitVec 128 :=
  let t := d ^^^ (n >>> 32)
  of32 ((w32 t 0).rotateLeft 1) ((w32 t 1).rotateLeft 1) ((w32 t 2).rotateLeft 1)
    ((w32 t 3).rotateLeft 1 ^^^ (w32 t 0).rotateLeft 2)

def sha256su0 (d n : BitVec 128) : BitVec 128 :=
  let t := of32 (w32 d 1) (w32 d 2) (w32 d 3) (w32 n 0)
  let f (e : Nat) : BitVec 32 :=
    let x := w32 t e
    (x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> 3) + w32 d e
  of32 (f 0) (f 1) (f 2) (f 3)

def sha256su1 (d n m : BitVec 128) : BitVec 128 :=
  let t0 := of32 (w32 n 1) (w32 n 2) (w32 n 3) (w32 m 0)
  let s (x : BitVec 32) : BitVec 32 := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> 10
  let r0 := s (w32 m 2) + w32 d 0 + w32 t0 0
  let r1 := s (w32 m 3) + w32 d 1 + w32 t0 1
  let r2 := s r0 + w32 d 2 + w32 t0 2
  let r3 := s r1 + w32 d 3 + w32 t0 3
  of32 r0 r1 r2 r3

def sha512h (d n m : BitVec 128) : BitVec 128 :=
  let s1 (x : BitVec 64) : BitVec 64 := x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41
  let hiT := ((hi64 m &&& lo64 n) ^^^ (~~~(hi64 m) &&& hi64 n)) + s1 (hi64 m) + hi64 d
  let tmp := hiT + lo64 m
  let loT := ((tmp &&& hi64 m) ^^^ (~~~tmp &&& lo64 n)) + s1 tmp + lo64 d
  of64 loT hiT

def sha512h2 (d n m : BitVec 128) : BitVec 128 :=
  let s0 (x : BitVec 64) : BitVec 64 := x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39
  let hiT := ((lo64 n &&& hi64 m) ^^^ (lo64 n &&& lo64 m) ^^^ (hi64 m &&& lo64 m)) +
    s0 (lo64 m) + hi64 d
  let loT := ((hiT &&& lo64 m) ^^^ (hiT &&& hi64 m) ^^^ (hi64 m &&& lo64 m)) + s0 hiT + lo64 d
  of64 loT hiT

def sha512su0 (d n : BitVec 128) : BitVec 128 :=
  let s (x : BitVec 64) : BitVec 64 := x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ x >>> 7
  of64 (lo64 d + s (hi64 d)) (hi64 d + s (lo64 n))

def sha512su1 (d n m : BitVec 128) : BitVec 128 :=
  let s (x : BitVec 64) : BitVec 64 := x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ x >>> 6
  of64 (lo64 d + s (lo64 n) + lo64 m) (hi64 d + s (hi64 n) + hi64 m)

/-- Carry-less multiplication of `a` and `b` (as polynomials over GF(2)). -/
def clmul (a b : Nat) (bits : Nat) : Nat :=
  (List.range bits).foldl (fun acc i => if b.testBit i then acc ^^^ (a <<< i) else acc) 0

end M1.Crypto
