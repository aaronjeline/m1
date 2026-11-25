/-
  Decoded A64 instructions.

  Each constructor corresponds to an encoding class of the Arm ARM (section
  C4.1 "A64 instruction set encoding"); fields are the instruction's operand
  fields after the "decode" part of the Arm pseudocode has run (immediates are
  already shifted / sign-extended / expanded).

  `sf = true` selects the 64-bit form (X registers), `false` the 32-bit form.
-/
import M1.Bits
import M1.FP
import M1.Crypto

namespace M1

abbrev Reg := BitVec 5

/-- Addressing mode for immediate-offset loads and stores. -/
inductive AddrMode where
  /-- `[Xn, #imm]` -/
  | offset
  /-- `[Xn, #imm]!` -/
  | pre
  /-- `[Xn], #imm` -/
  | post
deriving DecidableEq, Repr, Inhabited

/-- Integer load/store operation (`MemOp` + signedness + register size). -/
inductive MemOp where
  | store
  /-- Load, zero-extending into the register. -/
  | load
  /-- Load, sign-extending to 64 bits (`LDRSB Xt` etc). -/
  | loadSigned64
  /-- Load, sign-extending to 32 bits and zeroing the top half (`LDRSB Wt`). -/
  | loadSigned32
  | prefetch
deriving DecidableEq, Repr, Inhabited

inductive LogicOp where
  | and | orr | eor | ands
deriving DecidableEq, Repr, Inhabited

inductive MoveWideOp where
  | movn | movz | movk
deriving DecidableEq, Repr, Inhabited

inductive BitfieldOp where
  | sbfm | bfm | ubfm
deriving DecidableEq, Repr, Inhabited

inductive DP1Op where
  | rbit | rev16 | rev32 | rev | clz | cls
deriving DecidableEq, Repr, Inhabited

inductive DP2Op where
  | udiv | sdiv | lslv | lsrv | asrv | rorv
deriving DecidableEq, Repr, Inhabited

inductive DP3Op where
  /-- `MADD`/`MSUB` at the instruction's datasize. -/
  | madd | msub
  | smaddl | smsubl | umaddl | umsubl
  | smulh | umulh
deriving DecidableEq, Repr, Inhabited

inductive BranchRegOp where
  | br | blr | ret
deriving DecidableEq, Repr, Inhabited

/-- LSE atomic memory operations (`LD<op>`, `SWP`). -/
inductive AtomicOp where
  | add | clr | eor | set | smax | smin | umax | umin | swp
deriving DecidableEq, Repr, Inhabited

/-- Advanced SIMD "three same" integer operations (lane-wise). -/
inductive VecOp where
  | add | sub | and | bic | orr | orn | eor
  | cmeq | cmgt | cmge | cmhi | cmhs | cmtst
  | umax | umin | smax | smin | mul
  | bsl | bit | bif
  | addp | umaxp | uminp | smaxp | sminp
  | mla | mls | sshl | ushl
  | sqadd | uqadd | sqsub | uqsub
  | shadd | uhadd | srhadd | urhadd | sabd | uabd
  | srshl | urshl | sqshl | uqshl | sqrshl | uqrshl | sqdmulh | sqrdmulh
  | sqrdmlah | sqrdmlsh
deriving DecidableEq, Repr, Inhabited

/-- Scalar floating-point one-source operations. -/
inductive FP1Op where
  | fmov | fabs | fneg | fsqrt
  /-- `FCVT` to the format of the given width (32 or 64). -/
  | fcvt (dst : Nat)
  /-- `FRINT{N,P,M,Z,A}` -/
  | frint (mode : FP.Rounding)
  /-- `FRINTX` (inexact signalled) / `FRINTI`, in the FPCR rounding mode. -/
  | frintx | frinti
  /-- `FRINT32Z`/`FRINT64Z` (`x = false`), `FRINT32X`/`FRINT64X` (FPCR mode). -/
  | frintN (x : Bool) (intsize : Nat)
deriving DecidableEq, Repr, Inhabited

/-- Scalar floating-point two-source operations. -/
inductive FP2Op where
  | fmul | fdiv | fadd | fsub | fmax | fmin | fmaxnm | fminnm | fnmul
deriving DecidableEq, Repr, Inhabited

/-- Advanced SIMD floating-point "three same" operations. -/
inductive FVecOp where
  | fadd | fsub | fmul | fdiv | fmax | fmin | fmaxnm | fminnm | fmla | fmls | fabd
  | fcmeq | fcmge | fcmgt | facge | facgt
  | faddp | fmaxnmp | fminnmp | fmaxp | fminp
  | fmulx | frecps | frsqrts
deriving DecidableEq, Repr, Inhabited

/-- Advanced SIMD floating-point unary operations (vector or scalar). -/
inductive FVec2Op where
  | fabs | fneg | fsqrt
  | fcmgt0 | fcmge0 | fcmeq0 | fcmle0 | fcmlt0
  /-- `FCVT{N,P,M,Z,A}{S,U}` (to same-size integer lanes) -/
  | fcvt (mode : FP.Rounding) (signed : Bool)
  /-- `SCVTF` / `UCVTF` -/
  | cvtf (signed : Bool)
  | frint (mode : FP.Rounding)
  | frintx | frinti
  | frintN (x : Bool) (intsize : Nat)
  /-- `FCVTZ{S,U}` / `{S,U}CVTF` (vector or scalar, fixed point with `fbits`
  fraction bits). -/
  | fcvtFix (signed : Bool) (fbits : Nat)
  | cvtfFix (signed : Bool) (fbits : Nat)
  | frecpe | frsqrte | frecpx
  /-- `URECPE` / `URSQRTE` (32-bit integer lanes). -/
  | urecpe | ursqrte
deriving DecidableEq, Repr, Inhabited

/-- Floating-point reductions (across lanes, or scalar pairwise). -/
inductive FRedOp where
  | fadd | fmax | fmin | fmaxnm | fminnm
deriving DecidableEq, Repr, Inhabited

/-- Advanced SIMD "two-register miscellaneous" integer operations. -/
inductive Vec2Op where
  | rev16 | rev32 | rev64 | cnt | cls | clz | not | rbit | abs | neg
  | cmgt0 | cmeq0 | cmlt0 | cmge0 | cmle0
  /-- `XTN`/`XTN2`: `esize` is the destination element size. -/
  | xtn
  | saddlp | uaddlp | sadalp | uadalp
  /-- Saturating narrows (`esize` is the destination size). -/
  | sqxtn | uqxtn | sqxtun
  /-- `SHLL{2}`: widen, shifting left by the source element size. -/
  | shll
  | sqabs | sqneg
  /-- Saturating accumulate of an unsigned (`SUQADD`) / signed (`USQADD`) value. -/
  | suqadd | usqadd
deriving DecidableEq, Repr, Inhabited

/-- Advanced SIMD "across lanes" reductions. -/
inductive VecRedOp where
  | addv | saddlv | uaddlv | smaxv | umaxv | sminv | uminv
deriving DecidableEq, Repr, Inhabited

/-- Advanced SIMD permutes. -/
inductive VecPermOp where
  | uzp1 | uzp2 | zip1 | zip2 | trn1 | trn2
deriving DecidableEq, Repr, Inhabited

/-- Advanced SIMD shift by immediate. For the long forms (`SSHLL`, `USHLL`)
`esize` is the source element size; for `SHRN` the destination size. -/
inductive VecShiftOp where
  | sshr | ushr | ssra | usra | shl | sli | sri | sshll | ushll | shrn
  | srshr | urshr | srsra | ursra | sqshlu | sqshl | uqshl
  /-- Narrowing (`esize` is the destination size). -/
  | rshrn | sqshrn | uqshrn | sqrshrn | uqrshrn | sqshrun | sqrshrun
deriving DecidableEq, Repr, Inhabited

/-- Advanced SIMD "three different" (widening) operations; `esize` is the
narrow (source) element size. -/
inductive VecLongOp where
  | saddl | uaddl | saddw | uaddw | ssubl | usubl | ssubw | usubw
  | smlal | umlal | smlsl | umlsl | smull | umull
  | sabal | uabal | sabdl | uabdl
  | sqdmull | sqdmlal | sqdmlsl
  /-- High-half narrowing (`esize` is the destination size). -/
  | addhn | raddhn | subhn | rsubhn
deriving DecidableEq, Repr, Inhabited

/-- Cryptographic-extension operations on vector registers. -/
inductive CryptoOp where
  | aese | aesd | aesmc | aesimc
  | sha1c | sha1p | sha1m | sha1su0 | sha1h | sha1su1
  | sha256h | sha256h2 | sha256su0 | sha256su1
  | sha512h | sha512h2 | sha512su0 | sha512su1
  | rax1
deriving DecidableEq, Repr, Inhabited

/-- Advanced SIMD integer "by element" operations. -/
inductive VecElemOp where
  | mul | mla | mls | sqdmulh | sqrdmulh
  /-- Widening (`esize` is the source size). -/
  | smull | umull | smlal | umlal | smlsl | umlsl
  | sqdmull | sqdmlal | sqdmlsl | sqrdmlah | sqrdmlsh
deriving DecidableEq, Repr, Inhabited

inductive Instr where
  -- Data processing — immediate
  /-- `ADR` (`page = false`) / `ADRP` (`page = true`); `imm` is the
  sign-extended byte offset (for ADRP already shifted left by 12). -/
  | pcRel (page : Bool) (imm : BitVec 64) (rd : Reg)
  /-- `ADD`/`ADDS`/`SUB`/`SUBS` (immediate); `imm` already shifted. -/
  | addSubImm (sf sub setFlags : Bool) (imm : BitVec 64) (rn rd : Reg)
  /-- `AND`/`ORR`/`EOR`/`ANDS` (immediate); `imm` is the decoded bitmask. -/
  | logicImm (sf : Bool) (op : LogicOp) (imm : BitVec 64) (rn rd : Reg)
  /-- `MOVN`/`MOVZ`/`MOVK`; `pos` = hw*16. -/
  | moveWide (sf : Bool) (op : MoveWideOp) (pos : Nat) (imm16 : BitVec 16) (rd : Reg)
  /-- `SBFM`/`BFM`/`UBFM` with decoded masks. -/
  | bitfield (sf : Bool) (op : BitfieldOp) (r s : Nat) (wmask tmask : BitVec 64) (rn rd : Reg)
  /-- `EXTR` -/
  | extr (sf : Bool) (lsb : Nat) (rm rn rd : Reg)
  -- Data processing — register
  /-- `AND`/`BIC`/`ORR`/`ORN`/`EOR`/`EON`/`ANDS`/`BICS` (shifted register). -/
  | logicShift (sf : Bool) (op : LogicOp) (invert : Bool) (shift : ShiftType) (amount : Nat)
      (rm rn rd : Reg)
  /-- `ADD`/`ADDS`/`SUB`/`SUBS` (shifted register). -/
  | addSubShift (sf sub setFlags : Bool) (shift : ShiftType) (amount : Nat) (rm rn rd : Reg)
  /-- `ADD`/`ADDS`/`SUB`/`SUBS` (extended register). -/
  | addSubExt (sf sub setFlags : Bool) (option : BitVec 3) (shift : Nat) (rm rn rd : Reg)
  /-- `ADC`/`ADCS`/`SBC`/`SBCS` -/
  | addSubCarry (sf sub setFlags : Bool) (rm rn rd : Reg)
  /-- `CCMN`/`CCMP` (register or immediate second operand). -/
  | condCmp (sf sub : Bool) (useImm : Bool) (imm : BitVec 64) (rm : Reg) (cond : BitVec 4)
      (nzcv : BitVec 4) (rn : Reg)
  /-- `CSEL` (`inv=false, inc=false`), `CSINC`, `CSINV`, `CSNEG` (`inv && inc`). -/
  | condSel (sf inv inc : Bool) (cond : BitVec 4) (rm rn rd : Reg)
  | dp1 (sf : Bool) (op : DP1Op) (rn rd : Reg)
  | dp2 (sf : Bool) (op : DP2Op) (rm rn rd : Reg)
  | dp3 (sf : Bool) (op : DP3Op) (rm ra rn rd : Reg)
  -- Branches, exceptions, system
  /-- `B`/`BL` with byte offset. -/
  | branch (link : Bool) (offset : BitVec 64)
  | branchCond (cond : BitVec 4) (offset : BitVec 64)
  /-- `CBZ`/`CBNZ` -/
  | cmpBranch (sf nonzero : Bool) (offset : BitVec 64) (rt : Reg)
  /-- `TBZ`/`TBNZ` -/
  | testBranch (bit : Nat) (nonzero : Bool) (offset : BitVec 64) (rt : Reg)
  | branchReg (op : BranchRegOp) (rn : Reg)
  /-- Hints and barriers that have no effect on a single-core sequential model
  (`NOP`, `YIELD`, `DMB`, `DSB`, `ISB`, ...). -/
  | nop
  | clrex
  | svc (imm : BitVec 16)
  | brk (imm : BitVec 16)
  /-- `MRS Xt, NZCV` -/
  | mrsNZCV (rt : Reg)
  /-- `MSR NZCV, Xt` -/
  | msrNZCV (rt : Reg)
  /-- `MRS Xt, FPCR` (`fpsr = false`) / `MRS Xt, FPSR`. -/
  | mrsFP (fpsr : Bool) (rt : Reg)
  /-- `MSR FPCR, Xt` (`fpsr = false`) / `MSR FPSR, Xt`. -/
  | msrFP (fpsr : Bool) (rt : Reg)
  -- Loads and stores (general-purpose registers)
  /-- Single register, immediate offset (`LDR`/`STR`/`LDUR`/`LDRB`/...); `size` in bytes. -/
  | ldstImm (size : Nat) (op : MemOp) (mode : AddrMode) (offset : BitVec 64) (rn rt : Reg)
  /-- Single register, register offset; `option`/`shift` as for `ExtendReg`. -/
  | ldstReg (size : Nat) (op : MemOp) (option : BitVec 3) (shift : Nat) (rm rn rt : Reg)
  /-- `LDR` (literal) / `LDRSW` (literal) / `PRFM` (literal). -/
  | ldrLit (size : Nat) (op : MemOp) (offset : BitVec 64) (rt : Reg)
  /-- `LDP`/`STP`/`LDPSW`/`LDNP`/`STNP`; `size` in bytes of each element;
  `signed` for LDPSW. -/
  | ldstPair (size : Nat) (load signed : Bool) (mode : AddrMode) (offset : BitVec 64)
      (rt2 rn rt : Reg)
  /-- `LDXR`/`LDAXR` (load) and `STXR`/`STLXR` (store, status to `rs`). -/
  | ldstExcl (size : Nat) (load : Bool) (rs rn rt : Reg)
  /-- `LDAR`/`LDLAR` (load) and `STLR`/`STLLR` (store). -/
  | ldstOrdered (size : Nat) (load : Bool) (rn rt : Reg)
  /-- `LDAPUR`/`LDAPURB`/`LDAPURH`/`LDAPURS{B,H,W}` (load-acquire RCpc) and
  `STLUR`/`STLURB`/`STLURH` (store-release) with an unscaled signed immediate
  offset and no writeback (FEAT_LRCPC2). `op` is never `prefetch`. -/
  | ldstOrderedImm (size : Nat) (op : MemOp) (offset : BitVec 64) (rn rt : Reg)
  /-- LSE atomics `LDADD`/.../`SWP` (all ordering variants). -/
  | atomic (size : Nat) (op : AtomicOp) (rs rn rt : Reg)
  /-- `CAS` (all ordering variants). -/
  | cas (size : Nat) (rs rn rt : Reg)
  -- SIMD & FP registers
  /-- `LDR`/`STR`/`LDUR`/`STUR` of a B/H/S/D/Q register, immediate offset. -/
  | vldstImm (size : Nat) (load : Bool) (mode : AddrMode) (offset : BitVec 64) (rn rt : Reg)
  /-- `LDR`/`STR` of a B/H/S/D/Q register, register offset. -/
  | vldstReg (size : Nat) (load : Bool) (option : BitVec 3) (shift : Nat) (rm rn rt : Reg)
  /-- `LDR` (literal) of an S/D/Q register. -/
  | vldrLit (size : Nat) (offset : BitVec 64) (rt : Reg)
  /-- `LDP`/`STP`/`LDNP`/`STNP` of S/D/Q registers. -/
  | vldstPair (size : Nat) (load : Bool) (mode : AddrMode) (offset : BitVec 64) (rt2 rn rt : Reg)
  /-- `FMOV` between a general register and (part of) a vector register:
  `toGpr` selects direction, `size` is 4 or 8 bytes, `top` selects `Vn.D[1]`. -/
  | fmovGen (toGpr : Bool) (size : Nat) (top : Bool) (rn rd : Reg)
  /-- `MOVI`/`MVNI`/`ORR`/`BIC` (vector, immediate) with expanded 64-bit
  immediate replicated per `q`. `op`: 0 = MOVI/MVNI (move), 1 = ORR, 2 = BIC. -/
  | vmovImm (q : Bool) (op : Nat) (imm : BitVec 64) (rd : Reg)
  /-- `DUP Vd.T, Rn` (general register to all lanes; `esize` in bits). -/
  | dupGen (q : Bool) (esize : Nat) (rn rd : Reg)
  /-- `DUP Vd.T, Vn.Ts[index]` -/
  | dupElem (q : Bool) (esize : Nat) (index : Nat) (rn rd : Reg)
  /-- `INS Vd.Ts[index], Rn` -/
  | insGen (esize : Nat) (index : Nat) (rn rd : Reg)
  /-- `INS Vd.Ts[i1], Vn.Ts[i2]` -/
  | insElem (esize : Nat) (dst src : Nat) (rn rd : Reg)
  /-- `UMOV`/`SMOV` (`signed`), result size 32 or 64 bits (`sf`). -/
  | movToGen (sf signed : Bool) (esize : Nat) (index : Nat) (rn rd : Reg)
  /-- Advanced SIMD three-same integer and logical operations. -/
  | vec3 (q : Bool) (esize : Nat) (op : VecOp) (rm rn rd : Reg)
  | vec2 (q : Bool) (esize : Nat) (op : Vec2Op) (rn rd : Reg)
  | vreduce (q : Bool) (esize : Nat) (op : VecRedOp) (rn rd : Reg)
  /-- `ADDP Dd, Vn.2D` -/
  | addpScalar (rn rd : Reg)
  | vperm (q : Bool) (esize : Nat) (op : VecPermOp) (rm rn rd : Reg)
  /-- `EXT Vd, Vn, Vm, #pos` (byte position). -/
  | vext (q : Bool) (pos : Nat) (rm rn rd : Reg)
  /-- `TBL`/`TBX` with a table of `nregs` consecutive registers from `rn`. -/
  | vtbl (q : Bool) (nregs : Nat) (tbx : Bool) (rm rn rd : Reg)
  | vshift (q : Bool) (esize : Nat) (op : VecShiftOp) (shift : Nat) (rn rd : Reg)
  | vlong (q : Bool) (esize : Nat) (op : VecLongOp) (rm rn rd : Reg)
  /-- Integer multiply (accumulate) by element `index` of `rm`. -/
  | velem (q : Bool) (esize : Nat) (op : VecElemOp) (index : Nat) (rm rn rd : Reg)
  /-- AES, SHA-1/256/512 and `RAX1` (operands as encoded; unused ones ignored). -/
  | crypto (op : CryptoOp) (rm rn rd : Reg)
  /-- `EOR3` (`bcax = false`) / `BCAX`. -/
  | eor3 (bcax : Bool) (rm ra rn rd : Reg)
  /-- `XAR Vd.2D, Vn.2D, Vm.2D, #imm` -/
  | xar (imm : Nat) (rm rn rd : Reg)
  /-- `PMULL{2}`: 8 × 8-bit (`wide = false`) or 1 × 64-bit (`wide = true`). -/
  | pmull (q wide : Bool) (rm rn rd : Reg)
  /-- A scalar integer SIMD instruction: the one-lane vector instruction
  `inner`, after which `rd` keeps only its low `bits` bits. -/
  | scalar (bits : Nat) (rd : Reg) (inner : Instr)
  /-- `SDOT`/`UDOT` (vector). -/
  | vdot (q signed : Bool) (rm rn rd : Reg)
  /-- `LD1`-`LD4`/`ST1`-`ST4` (multiple structures): `rpt` repetitions of
  `selem`-element structures; `wback` with `rm` (31 = immediate post-index). -/
  | vldstMulti (q : Bool) (esize : Nat) (load : Bool) (rpt selem : Nat) (wback : Bool)
      (rm rn rt : Reg)
  /-- `LD1`/`ST1` (single structure) of lane `index`, or `LD1R` (`replicate`). -/
  | vldstLane (q load replicate : Bool) (selem esize index : Nat) (wback : Bool) (rm rn rt : Reg)
  -- Scalar floating point; `fsize` is 16 (half), 32 (single) or 64 (double).
  | fp1 (fsize : Nat) (op : FP1Op) (rn rd : Reg)
  | fp2 (fsize : Nat) (op : FP2Op) (rm rn rd : Reg)
  /-- `FMADD`/`FMSUB`/`FNMADD`/`FNMSUB` (`o1`, `o0` as encoded). -/
  | fp3 (fsize : Nat) (o1 o0 : Bool) (ra rm rn rd : Reg)
  /-- `FCMP`/`FCMPE` (`signal`: any NaN is invalid; with `#0.0` when `zero`). -/
  | fcmp (fsize : Nat) (signal zero : Bool) (rm rn : Reg)
  /-- `FCCMP`/`FCCMPE` -/
  | fccmp (fsize : Nat) (signal : Bool) (cond : BitVec 4) (nzcv : BitVec 4) (rm rn : Reg)
  | fcsel (fsize : Nat) (cond : BitVec 4) (rm rn rd : Reg)
  | fmovImm (fsize : Nat) (imm8 : Nat) (rd : Reg)
  /-- `FCVT{N,A,P,M,Z}{S,U}` (scalar, to a general register; fixed point with
  `fbits` fraction bits). -/
  | fcvtToInt (sf : Bool) (fsize : Nat) (signed : Bool) (mode : FP.Rounding) (fbits : Nat)
      (rn rd : Reg)
  /-- `SCVTF` / `UCVTF` (scalar, from a general register; fixed point with
  `fbits` fraction bits). -/
  | intToFP (sf : Bool) (fsize : Nat) (signed : Bool) (fbits : Nat) (rn rd : Reg)
  -- Advanced SIMD floating point.
  | fvec3 (q : Bool) (fsize : Nat) (op : FVecOp) (rm rn rd : Reg)
  /-- Lane-wise unary op; `scalar` = the AdvSIMD scalar form (one element). -/
  | fvec2 (q scalar : Bool) (fsize : Nat) (op : FVec2Op) (rn rd : Reg)
  /-- `FMLA`/`FMLS`/`FMUL` (by element); `op` is `fmla`, `fmls` or `fmul`. -/
  | fvecElem (q : Bool) (fsize : Nat) (op : FVecOp) (index : Nat) (rm rn rd : Reg)
  /-- Scalar forms of the "three same" / "by element" FP operations
  (`index = none` for three same). -/
  | fscalar3 (fsize : Nat) (op : FVecOp) (index : Option Nat) (rm rn rd : Reg)
  /-- `FMLAL{2}` / `FMLSL{2}` (half-precision products accumulated into single),
  vector or by element. -/
  | fmlal (q sub top : Bool) (index : Option Nat) (rm rn rd : Reg)
  /-- `FCMLA` with rotation `rot * 90` degrees. -/
  | fcmla (q : Bool) (fsize rot : Nat) (rm rn rd : Reg)
  /-- `FCADD` with rotation 90 (`rot270 = false`) or 270. -/
  | fcadd (q : Bool) (fsize : Nat) (rot270 : Bool) (rm rn rd : Reg)
  /-- `FJCVTZS Wd, Dn`. -/
  | fjcvtzs (rn rd : Reg)
  /-- `FCVTN{2}` (wide to narrow) when `narrow`, else `FCVTL{2}` (narrow to wide);
  `wsize` is the wide element size (64: double/single, 32: single/half). -/
  | fcvtnl (q narrow : Bool) (wsize : Nat) (rn rd : Reg)
  /-- `FCVTXN{2}` (double to single, rounding to odd), vector or scalar. -/
  | fcvtxn (q scalar : Bool) (rn rd : Reg)
  /-- Reduction of all lanes (`FMAXNMV`, ...; `q` with 32-bit lanes) or, when
  `pairwise`, of the two lanes of a scalar pairwise op (`FADDP Dd, Vn.2D`). -/
  | freduce (q pairwise : Bool) (fsize : Nat) (op : FRedOp) (rn rd : Reg)
  /-- `DUP` (element, scalar form), alias `MOV Dd, Vn.D[i]`. -/
  | dupScalar (esize index : Nat) (rn rd : Reg)
  /-- `CRC32{B,H,W,X}` / `CRC32C{B,H,W,X}`; `size` in bytes. -/
  | crc32 (size : Nat) (castagnoli : Bool) (rm rn rd : Reg)
  /-- An encoding whose behaviour is CONSTRAINED UNPREDICTABLE (e.g. a
  writeback load whose base register is also the destination). -/
  | unpredictable
deriving Repr, Inhabited

end M1
