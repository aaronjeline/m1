/-
  Whole-function co-simulation checker (see `tools/funsim`): runs functions of
  a real compiled image in the model from the initial states recorded on the
  hardware, and compares return registers and buffer contents.
-/
import M1.Step
import M1.Tools.Cosim

namespace M1.FunSim
open Cosim (parseHex hex byteFn words)

def nbuf : Nat := 3
def bufSize : Nat := 4096
/-- Return address given to the function: the run stops when it is reached. -/
def sentinel : BitVec 64 := 0xDEAD0000#64
/-- Initial stack pointer (any 16-byte aligned address away from the buffers). -/
def stackTop : BitVec 64 := 0x7FFF00000000#64

structure Image where
  base : Nat
  text : Array (BitVec 32)
  data : Array (Nat × ByteArray)

def hexBytes (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    let h := (Cosim.hexVal cs[2 * i]!).getD 0
    let l := (Cosim.hexVal cs[2 * i + 1]!).getD 0
    out := out.push (UInt8.ofNat (h * 16 + l))
  return out

def parseImage (txt : String) : Image := Id.run do
  let mut img : Image := ⟨0, #[], #[]⟩
  for line in txt.splitOn "\n" do
    match words line with
    | "TEXT" :: b :: ws =>
      img := { img with base := (parseHex b).getD 0,
                        text := (ws.map fun w => BitVec.ofNat 32 ((parseHex w).getD 0)).toArray }
    | ["DATA", a, bs] => img := { img with data := img.data.push ((parseHex a).getD 0, hexBytes bs) }
    | _ => pure ()
  return img

/-- Array-backed instruction fetch for the image's `__text`. -/
def Image.program (img : Image) : Program := fun a =>
  let n := a.toNat
  if n < img.base || n % 4 != 0 then none else img.text[(n - img.base) / 4]?

structure Test where
  entry : Nat
  seed : Nat
  bufs : Array Nat
  x : Array Nat
  d : Array Nat
  /-- `none` if the native call crashed. -/
  result : Option (Array Nat × Array Nat)

def parseTest (line : String) : Option Test := do
  let parts := line.splitOn " ; "
  let f ← parts[0]?
  let hdr ← (words f).tail.mapM parseHex
  let x ← ((words (← parts[1]?)).drop 1).mapM parseHex
  let d ← ((words (← parts[2]?)).drop 1).mapM parseHex
  let r ← parts[3]?
  let result ← match words r with
    | "OK" :: outs =>
      let h ← ((words (← parts[4]?)).drop 1).mapM parseHex
      some (some ((← outs.mapM parseHex).toArray, h.toArray))
    | _ => some none
  some ⟨hdr[0]!, hdr[1]!, (hdr.drop 2).toArray, x.toArray, d.toArray, result⟩

def initMem (img : Image) (t : Test) : Memory := fun a =>
  let n := a.toNat
  let inBuf := (List.range nbuf).find? fun k => t.bufs[k]! ≤ n && n < t.bufs[k]! + bufSize
  match inBuf with
  | some k =>
    let off := n - t.bufs[k]!
    if off == bufSize - 1 then 0 else byteFn (t.seed + k) off
  | none =>
    match img.data.find? fun (b, bs) => b ≤ n && n < b + bs.size with
    | some (b, bs) => BitVec.ofNat 8 (bs.get! (n - b)).toNat
    | none => 0

def initState (img : Image) (t : Test) : State :=
  let s := State.init (BitVec.ofNat 64 t.entry)
  { s with
    gpr := fun r =>
      if r.toNat < 8 then BitVec.ofNat 64 t.x[r.toNat]!
      else if r = 30 then sentinel else 0
    sp := stackTop
    vreg := fun r => if r.toNat < 8 then BitVec.ofNat 128 t.d[r.toNat]! else 0
    mem := initMem img t }

/-- Run until the function returns to the sentinel, stops, or runs out of fuel. -/
def runToReturn (p : Program) (s : State) : Nat → State × Nat
  | 0 => (s, 0)
  | fuel + 1 =>
    if s.pc == sentinel || s.status != .running then (s, fuel + 1)
    else runToReturn p (step p s) fuel

def fnv (m : Memory) (base : Nat) : Nat := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  for i in [0:bufSize] do
    h := (h ^^^ (m (BitVec.ofNat 64 (base + i))).toNat.toUInt64) * 0x100000001b3
  return h.toNat

inductive Outcome where
  | agree
  | nativeFault
  | stuck (why : String)
  | mismatch (why : String)

def check (img : Image) (t : Test) (fuel : Nat := 1000000) : Outcome :=
  match t.result with
  | none => .nativeFault
  | some (outs, hashes) =>
    let (s, left) := runToReturn img.program (initState img t) fuel
    if left == 0 then .stuck "out of fuel" else
    if s.status != .running then .stuck (reprStr s.status) else
    let got := #[(s.gpr 0).toNat, (s.gpr 1).toNat,
      (s.vreg 0).toNat % 2 ^ 64, (s.vreg 0).toNat / 2 ^ 64,
      (s.vreg 1).toNat % 2 ^ 64, (s.vreg 1).toNat / 2 ^ 64]
    let names := #["x0", "x1", "q0.lo", "q0.hi", "q1.lo", "q1.hi"]
    let regDiffs := (List.range 6).filterMap fun i =>
      if got[i]! == outs[i]! then none
      else some s!"{names[i]!}: model {hex got[i]!} hw {hex outs[i]!}"
    let memDiffs := (List.range nbuf).filterMap fun k =>
      if fnv s.mem t.bufs[k]! == hashes[k]! then none else some s!"buffer {k} differs"
    if regDiffs.isEmpty && memDiffs.isEmpty then .agree
    else .mismatch (", ".intercalate (regDiffs ++ memDiffs))

def main (imagePath hwPath : String) : IO UInt32 := do
  let img := parseImage (← IO.FS.readFile imagePath)
  let lines := (← IO.FS.readFile hwPath).splitOn "\n" |>.filter (· ≠ "")
  let mut agree := 0
  let mut native := 0
  let mut stuck : Std.HashMap String Nat := {}
  let mut mism := 0
  for line in lines do
    let some t := parseTest line | IO.eprintln s!"bad line: {line.take 80}"
    match check img t with
    | .agree => agree := agree + 1
    | .nativeFault => native := native + 1
    | .stuck why =>
      stuck := stuck.insert s!"{hex t.entry}: {why}" (stuck.getD s!"{hex t.entry}: {why}" 0 + 1)
    | .mismatch why =>
      mism := mism + 1
      IO.println s!"MISMATCH entry {hex t.entry} seed {hex t.seed}: {why}"
  for (k, n) in stuck.toList do
    IO.println s!"stuck ({n}x) at {k}"
  IO.println s!"calls: {lines.length}  agree: {agree}  native-fault: {native}  model-stuck: {stuck.fold (fun a _ n => a + n) 0}  MISMATCHES: {mism}"
  return if mism == 0 then 0 else 1

end M1.FunSim
