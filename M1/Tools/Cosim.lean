/-
  Co-simulation checker: replays single-instruction tests recorded on real
  hardware (see `tools/cosim`) through the model and reports any difference.
-/
import M1.Step

namespace M1.Cosim

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def parseHex (s : String) : Option Nat :=
  if s.isEmpty then none else s.toList.foldlM (fun acc c => (hexVal c).map (acc * 16 + ·)) 0

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def byteFn (seed i : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((((i * 0x9E3779B1 + seed * 0x85EBCA77) % 2 ^ 64) >>> 16) % 256)

structure Snapshot where
  x : Array Nat
  sp : Nat
  nzcv : Nat
  v : Array Nat
  fpcr : Nat
  fpsr : Nat

def parseSnapshot (toks : List String) : Option Snapshot := do
  let ns ← toks.mapM parseHex
  let a := ns.toArray
  if a.size != 31 + 2 + 64 + 2 then none
  let v := (List.range 32).toArray.map fun r => a[33 + 2 * r]! + a[34 + 2 * r]! * 2 ^ 64
  some ⟨a.extract 0 31, a[31]!, a[32]!, v, a[97]!, a[98]!⟩

structure Test where
  word : Nat
  pc : Nat
  membase : Nat
  memsize : Nat
  seed : Nat
  input : Snapshot
  /-- `none` when the hardware raised a signal. -/
  output : Option (Nat × Snapshot × List (Nat × Nat))
  signal : Nat

def words (s : String) : List String := (s.splitOn " ").filter (· ≠ "")

def parseLine (line : String) : Option Test := do
  let parts := line.splitOn " ;"
  let hdr := words parts[0]!
  let [_, w, pc, mb, ms, sd] := hdr | none
  let inp ← parseSnapshot (words parts[1]!).tail
  let res := words parts[2]!
  let base : Test := ⟨← parseHex w, ← parseHex pc, ← parseHex mb, ← parseHex ms, ← parseHex sd,
    inp, none, 0⟩
  match res with
  | "SIG" :: n :: _ => some { base with signal := n.toNat! }
  | ["OK", path] =>
    let out ← parseSnapshot (words parts[3]!).tail
    let mems ← (words parts[4]!).tail.mapM fun t => do
      let [o, b] := t.splitOn ":" | none
      pure (← parseHex o, ← parseHex b)
    some { base with output := some (path.toNat!, out, mems) }
  | _ => none

def initState (t : Test) : State :=
  { gpr := fun r => BitVec.ofNat 64 (t.input.x[r.toNat]?.getD 0)
    sp := BitVec.ofNat 64 t.input.sp
    pc := BitVec.ofNat 64 t.pc
    flags := NZCV.ofBits (BitVec.ofNat 4 (t.input.nzcv >>> 28))
    vreg := fun r => BitVec.ofNat 128 (t.input.v[r.toNat]?.getD 0)
    mem := fun a =>
      let off := (a - BitVec.ofNat 64 t.membase).toNat
      if off < t.memsize then byteFn t.seed off else 0
    excl := none
    fpcr := BitVec.ofNat 64 t.input.fpcr
    fpsr := BitVec.ofNat 64 t.input.fpsr
    status := .running }

inductive Outcome where
  | agree
  | bothUndefined
  /-- Model: CONSTRAINED UNPREDICTABLE (stuck); any hardware behaviour is allowed. -/
  | unpredictable
  /-- Model does not handle an encoding the hardware executes. -/
  | gap
  /-- Hardware memory fault the (total-memory) model cannot observe. -/
  | hwMemFault
  | mismatch (msg : String)

def compare (t : Test) : Outcome :=
  let s0 := initState t
  let w : BitVec 32 := BitVec.ofNat 32 t.word
  let prog : Program := fun a => if a = s0.pc then some w else none
  let s1 := step prog s0
  let dec := decode w
  let pre := s!"{hex t.word} {repr dec}: "
  if s1.status == .fault (.unpredictable w) then .unpredictable else
  match t.output with
  | none =>
    match s1.status, t.signal with
    | .fault (.unsupported _), 4 => .bothUndefined
    | .fault (.unsupported _), _ => .gap
    | .brk _, 5 => .agree
    | .fault (.dataAlignment _), 10 => .agree
    | .fault .spAlignment, 10 => .agree
    | .fault (.fpTrap _), 4 | .fault (.fpTrap _), 8 => .agree
    | _, 10 | _, 11 => .hwMemFault
    | st, sig => .mismatch (pre ++ s!"hardware signal {sig}, model status {repr st}")
  | some (path, out, mems) =>
    match s1.status with
    | .fault (.unsupported _) => .gap
    | .running =>
      Id.run do
        let mut errs : Array String := #[]
        let dpc := (s1.pc - s0.pc).toNat
        if dpc != 4 * path then errs := errs.push s!"pc +{dpc}, hw path {path}"
        for r in List.range 31 do
          let mv := (s1.gpr (BitVec.ofNat 5 r)).toNat
          -- macOS may zero x18 (the platform register) at any context switch.
          if mv != out.x[r]! && !(r == 18 && out.x[r]! == 0) then
            errs := errs.push s!"x{r}: model {hex mv} hw {hex out.x[r]!} (in {hex t.input.x[r]!})"
        if s1.sp.toNat != out.sp then errs := errs.push s!"sp: model {hex s1.sp.toNat} hw {hex out.sp}"
        let mf := s1.flags.toBits.toNat <<< 28
        if mf != out.nzcv then errs := errs.push s!"nzcv: model {hex mf} hw {hex out.nzcv}"
        if s1.fpsr.toNat != out.fpsr then
          errs := errs.push s!"fpsr: model {hex s1.fpsr.toNat} hw {hex out.fpsr} (in {hex t.input.fpsr}, fpcr {hex t.input.fpcr})"
        if s1.fpcr.toNat != out.fpcr then
          errs := errs.push s!"fpcr: model {hex s1.fpcr.toNat} hw {hex out.fpcr}"
        for r in List.range 32 do
          let mv := (s1.vreg (BitVec.ofNat 5 r)).toNat
          if mv != out.v[r]! then
            errs := errs.push s!"v{r}: model {hex mv} hw {hex out.v[r]!} (in {hex t.input.v[r]!})"
        -- Memory: every byte of the buffer.
        let mut hwMem : Std.HashMap Nat Nat := {}
        for (o, b) in mems do hwMem := hwMem.insert o b
        for i in List.range t.memsize do
          let mb := (s1.mem (BitVec.ofNat 64 (t.membase + i))).toNat
          let hb := hwMem.getD i (byteFn t.seed i).toNat
          if mb != hb then errs := errs.push s!"mem[+{hex i}]: model {hex mb} hw {hex hb}"
        if errs.isEmpty then return .agree
        return .mismatch (pre ++ ", ".intercalate (errs.toList.take 6))
    | st => .mismatch (pre ++ s!"hardware OK, model status {repr st}")

def main (path : String) : IO UInt32 := do
  let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (· ≠ "")
  let mut agree := 0
  let mut undef := 0
  let mut gaps : Array String := #[]
  let mut memf := 0
  let mut unpred := 0
  let mut bad := 0
  for line in lines do
    match parseLine line with
    | none => IO.eprintln s!"unparseable: {line.take 80}"; bad := bad + 1
    | some t =>
      match compare t with
      | .agree => agree := agree + 1
      | .bothUndefined => undef := undef + 1
      | .gap => gaps := gaps.push (hex t.word)
      | .hwMemFault => memf := memf + 1
      | .unpredictable => unpred := unpred + 1
      | .mismatch m => IO.println s!"MISMATCH {m}"; bad := bad + 1
  IO.println s!"tests: {lines.length}  agree: {agree}  both-undefined: {undef}  \
    hw-memory-fault: {memf}  unpredictable: {unpred}  unmodelled: {gaps.size}  MISMATCHES: {bad}"
  if !gaps.isEmpty then
    IO.println s!"unmodelled encodings executed by hardware (first 40): {gaps.toList.take 40}"
  return if bad == 0 then 0 else 1

end M1.Cosim
