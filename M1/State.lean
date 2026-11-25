/-
  Architectural state of an M1 core executing in AArch64 EL0 (user mode).

  Modelled state:
  * `X0`–`X30` general purpose registers, `SP` (`SP_EL0`), `PC`;
  * `PSTATE.{N,Z,C,V}`;
  * `FPCR` and `FPSR` (see `fpcr`, `fpsr`);
  * the 32 128-bit SIMD&FP registers `V0`–`V31`;
  * a flat 64-bit byte-addressed, little-endian data memory;
  * the local exclusive monitor (for LDXR/STXR);
  * a run status recording whether execution has stopped and why.

  Instruction fetch is modelled separately (see `M1.Program`): on macOS
  executable pages are never simultaneously writable (W^X is enforced by the
  OS and by the M1's `APRR`/`SPRR` hardware), so a running user program cannot
  modify its own code and instruction memory can be treated as a read-only map.
-/
import M1.Bits

namespace M1

/-- Why the processor stopped. A verified program must be shown to reach a
`running` state at its exit point, so every stop reason here is "stuck". -/
inductive Fault where
  /-- No instruction mapped at this PC. -/
  | fetch (pc : BitVec 64)
  /-- PC not 4-byte aligned. -/
  | pcAlignment (pc : BitVec 64)
  /-- SP used as a base register while not 16-byte aligned. -/
  | spAlignment
  /-- Misaligned access that the architecture requires to be aligned
  (exclusives and atomics). -/
  | dataAlignment (addr : BitVec 64)
  /-- Encoding not handled by this model (includes architecturally UNDEFINED
  encodings and features that are not modelled). -/
  | unsupported (w : BitVec 32)
  /-- An encoding whose behaviour is CONSTRAINED UNPREDICTABLE. -/
  | unpredictable (w : BitVec 32)
  /-- A floating-point exception whose trap is enabled in `FPCR` (`IOE`, `DZE`,
  `OFE`, `UFE`, `IXE`, `IDE`); macOS delivers it as a signal. -/
  | fpTrap (w : BitVec 32)
deriving DecidableEq, Repr, Inhabited

inductive Status where
  | running
  /-- `SVC #imm` was executed (a system call). `PC` holds the preferred return
  address (the next instruction). -/
  | svc (imm : BitVec 16)
  /-- `BRK #imm` was executed (`PC` still points at the BRK). -/
  | brk (imm : BitVec 16)
  | fault (f : Fault)
deriving DecidableEq, Repr, Inhabited

abbrev Memory := BitVec 64 → BitVec 8

structure State where
  /-- `X0`..`X30`; entry 31 is never read or written (it encodes XZR/SP). -/
  gpr : BitVec 5 → BitVec 64
  sp : BitVec 64
  pc : BitVec 64
  flags : NZCV
  vreg : BitVec 5 → BitVec 128
  mem : Memory
  /-- Local exclusive monitor: address and size of the last exclusive load. -/
  excl : Option (BitVec 64 × Nat)
  /-- `FPCR`, with the bits the M1 implements (`fpcrWritable`). -/
  fpcr : BitVec 64
  /-- `FPSR`: the cumulative floating-point exception flags and `QC`. -/
  fpsr : BitVec 64
  status : Status

/-- Point update of a function. -/
@[inline] def upd {α : Type} {β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

@[simp] theorem upd_same {α β} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

@[simp] theorem upd_other {α β} [DecidableEq α] (f : α → β) (a x : α) (b : β) (h : x ≠ a) :
    upd f a b x = f x := by simp [upd, h]

/-- A second write to the same point overrides the first. -/
@[simp] theorem upd_upd_same {α β} [DecidableEq α] (f : α → β) (a : α) (b c : β) :
    upd (upd f a b) a c = upd f a c := by
  funext x; simp only [upd]; split <;> rfl

/-! ### Memory: little-endian multi-byte access -/

namespace Memory

def read8 (m : Memory) (a : BitVec 64) : BitVec 8 := m a
def read16 (m : Memory) (a : BitVec 64) : BitVec 16 := m (a + 1) ++ m a
def read32 (m : Memory) (a : BitVec 64) : BitVec 32 := read16 m (a + 2) ++ read16 m a
def read64 (m : Memory) (a : BitVec 64) : BitVec 64 := read32 m (a + 4) ++ read32 m a
def read128 (m : Memory) (a : BitVec 64) : BitVec 128 := read64 m (a + 8) ++ read64 m a

def write8 (m : Memory) (a : BitVec 64) (v : BitVec 8) : Memory := upd m a v
def write16 (m : Memory) (a : BitVec 64) (v : BitVec 16) : Memory :=
  write8 (write8 m a (v.extractLsb' 0 8)) (a + 1) (v.extractLsb' 8 8)
def write32 (m : Memory) (a : BitVec 64) (v : BitVec 32) : Memory :=
  write16 (write16 m a (v.extractLsb' 0 16)) (a + 2) (v.extractLsb' 16 16)
def write64 (m : Memory) (a : BitVec 64) (v : BitVec 64) : Memory :=
  write32 (write32 m a (v.extractLsb' 0 32)) (a + 4) (v.extractLsb' 32 32)
def write128 (m : Memory) (a : BitVec 64) (v : BitVec 128) : Memory :=
  write64 (write64 m a (v.extractLsb' 0 64)) (a + 8) (v.extractLsb' 64 64)

/-- Read `size` bytes (1, 2, 4 or 8), zero-extended to 64 bits. -/
def readN (m : Memory) (a : BitVec 64) (size : Nat) : BitVec 64 :=
  match size with
  | 1 => (read8 m a).setWidth 64
  | 2 => (read16 m a).setWidth 64
  | 4 => (read32 m a).setWidth 64
  | _ => read64 m a

/-- Write the low `size` bytes (1, 2, 4 or 8) of `v`. -/
def writeN (m : Memory) (a : BitVec 64) (size : Nat) (v : BitVec 64) : Memory :=
  match size with
  | 1 => write8 m a (v.setWidth 8)
  | 2 => write16 m a (v.setWidth 16)
  | 4 => write32 m a (v.setWidth 32)
  | _ => write64 m a v

/-- Read `size` bytes (1, 2, 4, 8 or 16), zero-extended to 128 bits. -/
def readV (m : Memory) (a : BitVec 64) (size : Nat) : BitVec 128 :=
  match size with
  | 16 => read128 m a
  | _ => (readN m a size).setWidth 128

/-- Write the low `size` bytes (1, 2, 4, 8 or 16) of `v`. -/
def writeV (m : Memory) (a : BitVec 64) (size : Nat) (v : BitVec 128) : Memory :=
  match size with
  | 16 => write128 m a v
  | _ => writeN m a size (v.setWidth 64)

end Memory

/-- `FPCR` bits implemented by the M1 (measured: AHP, DN, FZ, RMode, Stride,
FZ16, Len, IDE, IXE, UFE, OFE, DZE, IOE). -/
def fpcrWritable : BitVec 64 := 0x07FF9F00
/-- `FPCR` bits affecting AArch64 floating point: AHP, DN, FZ, RMode, FZ16 and
the trap enables. When they are 0 (`FPDefault`), floating point behaves as
the plain `FP` operations describe. -/
def fpcrModeMask : BitVec 64 := 0x07C89F00
/-- `FPSR` bits implemented by the M1: QC, IDC, IXC, UFC, OFC, DZC, IOC. -/
def fpsrWritable : BitVec 64 := 0x0800009F

namespace State

/-- `X[r]` read at width `n` (register 31 reads as zero: XZR/WZR). -/
def x (s : State) (r : BitVec 5) : BitVec 64 :=
  if r = 31 then 0 else s.gpr r

/-- `X[r]` or `SP` (register 31 reads SP). -/
def xsp (s : State) (r : BitVec 5) : BitVec 64 :=
  if r = 31 then s.sp else s.gpr r

/-- Write `X[r]` (writes to register 31 are discarded). -/
def setX (s : State) (r : BitVec 5) (v : BitVec 64) : State :=
  if r = 31 then s else { s with gpr := upd s.gpr r v }

/-- Write `X[r]` or `SP` (register 31 writes SP). -/
def setXSP (s : State) (r : BitVec 5) (v : BitVec 64) : State :=
  if r = 31 then { s with sp := v } else { s with gpr := upd s.gpr r v }

def setV (s : State) (r : BitVec 5) (v : BitVec 128) : State :=
  { s with vreg := upd s.vreg r v }

def setFlags (s : State) (f : NZCV) : State := { s with flags := f }

def setPC (s : State) (pc : BitVec 64) : State := { s with pc := pc }

def nextPC (s : State) : State := { s with pc := s.pc + 4 }

def fault (s : State) (f : Fault) : State := { s with status := .fault f }

def setMem (s : State) (m : Memory) : State := { s with mem := m }

/-- Set cumulative `FPSR` flags (bits as in `FPSR`). -/
def orFPSR (s : State) (fl : Nat) : State := { s with fpsr := s.fpsr ||| BitVec.ofNat 64 fl }

/-- A state with all registers and memory zero, `PC = pc`. -/
def init (pc : BitVec 64) : State where
  gpr := fun _ => 0
  sp := 0
  pc := pc
  flags := NZCV.zero
  vreg := fun _ => 0
  mem := fun _ => 0
  excl := none
  fpcr := 0
  fpsr := 0
  status := .running

end State

end M1
