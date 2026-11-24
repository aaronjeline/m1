import M1
import M1.Tools.Cosim
import M1.Tools.FunSim

/-- Read hex instruction words (one per line) and print `1` for each word the
model decodes and `0` for each it does not. -/
def decodeFile (path : String) : IO UInt32 := do
  let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (· ≠ "")
  let mut out := ""
  for l in lines do
    let w := (M1.Cosim.parseHex l.trimAscii.toString).getD 0
    out := out.push (if (M1.decode (BitVec.ofNat 32 w)).isSome then '1' else '0')
    out := out.push '\n'
  IO.print out
  return 0

/-- Print the decoded instruction (or `none`) for each hex word in a file. -/
def showFile (path : String) : IO UInt32 := do
  let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (· ≠ "")
  for l in lines do
    let w := (M1.Cosim.parseHex l.trimAscii.toString).getD 0
    IO.println s!"{l.trimAscii} {(reprStr (M1.decode (BitVec.ofNat 32 w))).replace "\n" " "}"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["cosim", path] => M1.Cosim.main path
  | ["decode", path] => decodeFile path
  | ["show", path] => showFile path
  | ["funsim", image, trace] => M1.FunSim.main image trace
  | _ =>
    IO.println "usage: m1 cosim <hardware-trace> | m1 decode <hex-words-file> | m1 funsim <image> <trace>"
    return 2
