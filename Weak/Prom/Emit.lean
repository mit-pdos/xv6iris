/-
Weak/Prom: **emission v2** — the Sail instance of machine v2 (`Weak/Prom/Machine.lean`), definitions only (S1M-def).

Plan: `~/dev/weak-orch/promising/plan.md` §1 (M0, M1–M4, M9, M10, M16, M19; the "Deliverable S1M" emission list),
Table C findings FC-1, FC-4, FC-5 (`~/dev/weak-orch/promising/s0t/tableC.md`), Table S C-S column
(`…/s0t/tableS.md` §13), owner rulings [OWN.P1], [OWN.P2], [OWN.P3].

A NEW instance beside today's `Weak/WeakEvInst.lean` (`pnodeStep`/`pstepEv`), which is untouched.  It reuses only
pure vocabulary: the Sail model, `MachCSL`'s access-kind classifiers and device fabric, and `Weak.WeakDeps`'
decoder (`depsOfIb`), whose SOURCE LISTS are used here as the syntactic reference (M19), not the dynamic read set
of today's emission (DEC-7).

## Scope ([OWN.P3]: OQ-1 punted)

Programs that NEVER ENABLE ADDRESS TRANSLATION (`translationOff`, §6): every reachable register file has
`satp.MODE = Bare`.  So no `Read_ttw` walk read, no A/D pair and no translation-cache read is ever emitted; the arms
for them are absent (a walk read is STUCK here, `isTtw`), as extension points.  The scope is a predicate on
programs, not an ordering assumption.  Not modelled yet (each listed with what adding it needs in
PROGRESS-S1Mdef.md): page walks (M14, M18), the translation cache (M21), A/D updates (M20), `sfence.vma`
(`LSfence`), PBMT, the disk agent and the PLIC wire (today's `pstepDisk`/`pstepPlic`).

## FIX S0rest-F1 (2026-11-03, S0-P part (4), probe family G2): the OLD CSR view of a CSR read-modify-write

Found by G2 (`Weak/Prom/ProbeG2.lean`, CARRY variant of every `csrrw/csrrs/csrrc` on a tracked CSR, 63 probes):
Sail writes the CSR BEFORE `rd` (`csr_val ← read; write_CSR; X(rd) := csr_val`), so `rd`'s source `[p]`
(`depsRd2`) was evaluated AFTER `p`'s own `LRegW p [rs1, …]` — `rd` inherited `rs1`'s view (STRONGER: the LB
outcome through `ld a0; add x6,x6,s(a0); csrrw x5,csr,x6; … sd f(x5)` was forbidden; the text allows it:
rvwmo.adoc:487–495 "carries a dependency from rs1 to csr and from csr to rd", rd receives the OLD csr).  Fix: at
the FIRST read of the CSR's register in such an instruction (`csrCapture`), the instance emits `LRegW 53 [p]` into
a fresh dependency key (`csrOldKey`, the view of the old CSR), and `rd`'s sources are `[DReg 53]` (`regSrcs`).
Mark after the fix: FAITHFUL (rd depends on the CSR's previous writer, not on rs1).

## What changes from today's emission, item by item

* M19 / NA-4 — EVERY register write of a tracked register is `LRegW r srcs`, never `LSilent`: `srcs` is the
  decoder's SYNTACTIC source list when `r` is the decoded destination, `[]` otherwise (non-destination writes such
  as trap entry's `sepc`/`scause`: D-S0-4, SR-20; destinations of `ORnone` classes: SR-19).  No DEC-5/6/7 source:
  the `sret`/`mret` control sources through `sepc`/`mepc` are removed (`v2Roles`), and no `satp`/`mstatus` source
  exists because sources are syntactic.
* D-8 fixed — a load's (and an LR's) label carries its address sources (`depsAddr`).
* FC-4 — the control label is SYNTACTIC: every `nextPC` write emits `LCtrl (depsCtrl …)`; the first one is Sail's
  `nextPC := PC + 4/2` right after the announce (Step.lean:368, :402), which every instruction passes before any
  register write, so a NOT-TAKEN branch's rule-11 dependency is emitted with the views of `rs1`/`rs2` it reads.
* M10 — an exclusive read/write is classified by the decoded instruction: LR/SC (`LExLoad`/`LExStore`) or an AMO
  half (`LAmoLd`/`LAmoSt`, the `wRmw` slot).  aq is the read's `akSync`, rl the write's (M10 (2)).
* FIX S0P2-D3 — a read label's release bit and a write label's acquire bit are `akStrong` (Sail's `aq && rl`
  kinds, `AK_arch`): `lr.aqrl`'s release-RCsc and `sc.aqrl`'s acquire-RCsc annotations (rvwmo.adoc:124–128).
* FC-1 — the SC failure answer is `.Err ()` at an SC write only: Sail maps every `.Ok _` of `sail_mem_write` to
  success (PhysMemInterface.lean:325–329), `.Err ()` to `false`, and `execute_STORECON` writes `rd := 1`.  The
  label is `LExFail`.  Never offered to an AMO write (`internal_error "AMO got false …"`).
* M16 (c1) + FC-5 — at the end of every SC instruction that did not trap, the boundary emits `LExFail` before
  `LInstr`.  `trapped` is set at the trap's `mcause`/`scause` write (no `.takeException` call site exists, FC-5).
* M4 — a successful SC's `rd` gets `[DLdRes]` (the machine has put `ts` into `wLdv`); a failed SC's `rd` gets `[]`.
* [OWN.P1] — answers are nondeterministic where the text is permissive: a misaligned access's Sail pieces, and a
  `cbo.zero` write, may be decomposed into any contiguous chunks (`splittable`); an I/O address with no device
  answers any value and accepts any write; `getCycleCount` answers any value; a failed `amocas` may write back the
  old value (zacas.adoc:159–161).  Items that cannot be realised in the instance are STOP-AND-ASK items in
  PROGRESS-S1Mdef.md (misaligned-exception choice, unrealised hooks, the `.error` arm, `cbo.inval`).  The `.error`
  arm is HAVOC ([OWN.P8]/[OWN.P9], MachFix-havoc): stuck here, run-level "every outcome" in MachHavoc.lean.
* [OWN.P2] — `FENCE.I` (`Barrier_RISCV_i`) emits `LFenceI`; a fetch emits `LIFetch`; the announce no longer resets
  anything (it banks the bits only), so the fetch view `wIfv` survives into the instruction.
-/
import Weak.Prom.Machine
import Weak.WeakEvLang

namespace Weak.Prom

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Weak (Dsrc OpRoles depsOfIb depsCtrl depsAddr depsVsrc depsRd depsRd2 eregNum ibOfBvn ebarNow ebarPark
  paZ ibits)
open PLabel

/-! ## 1. Decoding what the instance needs from the announced bits -/

/-- THE v2 OPERAND ROLES (M19): today's decoder, minus the DEC-6 control sources of `sret`/`mret` (`ORjalr 0 SEPC`
/ `ORjalr 0 MEPC`, WeakDeps.lean:565–575).  §rvwmo: a control dependency comes from "a branch or indirect jump"
(rvwmo.adoc:242–246); `sret`/`mret` are neither and the listing has no row for them, so RVWMO gives no such
source.  Every other role (including each CSR instruction's own csr operand) is kept. -/
def v2Roles (ib : Option (BitVec 32)) : OpRoles :=
  match depsOfIb ib with
  | .ORjalr rd rs1 => if 32 ≤ rs1 then .ORnone else .ORjalr rd rs1
  | r => r

/-- The opcode, `funct3` and `funct5` fields. -/
def opc (w : BitVec 32) : Int := ibits w 6 0
def fn3 (w : BitVec 32) : Int := ibits w 14 12
def fn5 (w : BitVec 32) : Int := ibits w 31 27

/-- An SC (`sc.w`/`sc.d`): opcode AMO (`0x2F`), `funct5 = 00011`. -/
def isSC (ib : Option (BitVec 32)) : Bool :=
  match ib with
  | some w => decide (opc w = 47 ∧ fn5 w = 3)
  | none => false

/-- An LR (`lr.w`/`lr.d`): opcode AMO, `funct5 = 00010`. -/
def isLR (ib : Option (BitVec 32)) : Bool :=
  match ib with
  | some w => decide (opc w = 47 ∧ fn5 w = 2)
  | none => false

/-- An AMOCAS (Zacas `amocas.w/d/q`, Zabha `amocas.b/h`): opcode AMO, `funct5 = 00101`. -/
def isAmocas (ib : Option (BitVec 32)) : Bool :=
  match ib with
  | some w => decide (opc w = 47 ∧ fn5 w = 5)
  | none => false

/-- `cbo.zero` (Zicboz): MISC-MEM (`0x0F`), `funct3 = 010`, `rd = 0`, `imm[11:0] = 4`. -/
def isCboZero (ib : Option (BitVec 32)) : Bool :=
  match ib with
  | some w => decide (opc w = 15 ∧ fn3 w = 2 ∧ ibits w 11 7 = 0 ∧ ibits w 31 20 = 4)
  | none => false

/-- The Zicbom management instruction (`cbo.inval`/`cbo.clean`/`cbo.flush`: MISC-MEM, `funct3 = 010`, `rd = 0`,
`imm[11:0] = 0/1/2`) and its operation.  Sail's `process_clean_inval` emits no memory event (ZicbomInsts.lean:
340–360), so the instance emits the operation at the end of the instruction (`bndStep`).  A `cbo.inval` is emitted
as an invalidate in every mode: where `menvcfg`/`senvcfg.CBIE = 01` the text makes it a flush (cmo.adoc:524ff),
and an invalidate admits every value a flush does (a flush is a clean followed by an invalidate), so that case is
WEAKER, sound; FAITHFUL in M-mode and with `CBIE = 11`. -/
def cboKind (ib : Option (BitVec 32)) : Option CmoKind :=
  match ib with
  | some w =>
    if opc w = 15 ∧ fn3 w = 2 ∧ ibits w 11 7 = 0 then
      (match ibits w 31 20 with
       | 0 => some .inval | 1 => some .clean | 2 => some .flush | _ => none)
    else none
  | none => none

/-- The value of GPR number `r` (`0` for `x0` and out of range). -/
def gprVal (rs : RegFile) (r : Int) : BitVec 64 :=
  match r with
  | 1 => rs .x1 | 2 => rs .x2 | 3 => rs .x3 | 4 => rs .x4 | 5 => rs .x5 | 6 => rs .x6 | 7 => rs .x7
  | 8 => rs .x8 | 9 => rs .x9 | 10 => rs .x10 | 11 => rs .x11 | 12 => rs .x12 | 13 => rs .x13
  | 14 => rs .x14 | 15 => rs .x15 | 16 => rs .x16 | 17 => rs .x17 | 18 => rs .x18 | 19 => rs .x19
  | 20 => rs .x20 | 21 => rs .x21 | 22 => rs .x22 | 23 => rs .x23 | 24 => rs .x24 | 25 => rs .x25
  | 26 => rs .x26 | 27 => rs .x27 | 28 => rs .x28 | 29 => rs .x29 | 30 => rs .x30 | 31 => rs .x31
  | _ => 0#64

/-- The cache block size of the platform (`2 ^ plat_cache_block_size_exp`, PlatformConfig.lean:237). -/
def cboLen : Nat := 2 ^ LeanRV64D.Functions.plat_cache_block_size_exp

/-- The block a Zicbom instruction operates on: `rs1` rounded down to the block (ZicbomInsts.lean:345–347); under
`translationOff` the virtual address is the physical one. -/
def cboBase (rs : RegFile) (w : BitVec 32) : Int :=
  ((gprVal rs (ibits w 19 15)).toNat / cboLen * cboLen : Nat)

/-- THE ACCESS WIDTH of a scalar load/store instruction (base `LOAD`/`STORE`/`LOAD-FP`/`STORE-FP` by `funct3`, and
the C-extension forms incl. Zcb), `none` for anything else.  Used only to recognise a Sail PIECE of a misaligned
access (a request narrower than the instruction's width). -/
def accWidth (ib : Option (BitVec 32)) : Option Nat :=
  match ib with
  | none => none
  | some w =>
    match ibits w 1 0 with
    | 3 =>
      if opc w = 3 then
        (match fn3 w with
         | 0 | 4 => some 1 | 1 | 5 => some 2 | 2 | 6 => some 4 | 3 => some 8 | _ => none)
      else if opc w = 35 then
        (match fn3 w with | 0 => some 1 | 1 => some 2 | 2 => some 4 | 3 => some 8 | _ => none)
      else if opc w = 7 ∨ opc w = 39 then
        (match fn3 w with | 1 => some 2 | 2 => some 4 | 3 => some 8 | 4 => some 16 | _ => none)
      else none
    | 0 =>
      (match ibits w 15 13 with
       | 1 | 3 | 5 | 7 => some 8 | 2 | 6 => some 4
       | 4 => (match ibits w 12 10 with | 0 | 2 => some 1 | 1 | 3 => some 2 | _ => none)
       | _ => none)
    | 2 =>
      (match ibits w 15 13 with
       | 1 | 3 | 5 | 7 => some 8 | 2 | 6 => some 4 | _ => none)
    | _ => none

/-- [OWN.P1] MAY THIS RAM REQUEST BE DECOMPOSED?  (i) A piece of a misaligned scalar access (Sail split it, so the
piece is narrower than the instruction): rvwmo.adoc:92–93 "A misaligned load or store instruction may be
decomposed into a set of component memory operations of any granularity" (and RV-U11, byte by byte).  (ii) The
`cbo.zero` block write: cmo.adoc:137–138 "An implementation may or may not update the entire set of bytes
atomically with a single store operation".  An aligned access is never decomposed (single-copy atomicity). -/
def splittable (ib : Option (BitVec 32)) (n : Nat) : Bool :=
  isCboZero ib ||
  (match accWidth ib with
   | some wd => decide (n < wd)
   | none => false)

/-- FIX S0rest-F1: the dependency key that holds a CSR instruction's OLD CSR view (one past `WeakDeps`' keys
32–52; `wRegv` is a map, every key is fresh). -/
def csrOldKey : Nat := 53

/-- FIX S0rest-F1: the second destination with the old-CSR source: a Zicsr read-modify-write's `rd` receives the
CSR's OLD value, whose view `csrOldKey` captured at the CSR read (`csrCapture`). -/
def v2Rd2 (ib : Option (BitVec 32)) : Option (Nat × List Dsrc) :=
  match v2Roles ib with
  | .ORcsr p s rd => (depsRd2 (.ORcsr p s rd)).map (fun e => (e.1, [.DReg csrOldKey]))
  | r => depsRd2 r

/-- THE SOURCES OF A REGISTER WRITE (M19, D-S0-4): the decoded destination's syntactic sources, else `[]`.  An SC's
`rd` gets `[DLdRes]` only after a successful write (M4); a failed SC's `rd` gets `[]` ([R3.s2]). -/
def regSrcs (ib : Option (BitVec 32)) (scOk : Bool) (n : Nat) : List Dsrc :=
  if isSC ib && !scOk then []
  else
    match depsRd (v2Roles ib) with
    | some (rd, srcs) =>
        if rd = n then srcs
        else (match v2Rd2 ib with
              | some (rd2, srcs2) => if rd2 = n then srcs2 else []
              | none => [])
    | none =>
        (match v2Rd2 ib with
         | some (rd2, srcs2) => if rd2 = n then srcs2 else []
         | none => [])

/-- `rs1` as an address source. -/
def dsrcOfRs1 (w : BitVec 32) : List Dsrc := Weak.dsrcOfNum (ibits w 19 15)

/-- The barrier label: FENCE.I is `LFenceI` ([OWN.P2]); every other barrier is its applied-now half (M6). -/
def barLabel (b : barrier_kind) : PLabel :=
  match b with
  | .Barrier_RISCV_i => LFenceI
  | _ =>
    match ebarNow b with
    | some (pr, pw, sr, sw) => LFence pr pw sr sw
    | none => LFence false false false false

/-- THE SECOND ANNOTATION OF AN `aqrl` ACCESS (FIX S0P2-D3, 2026-11-02).  Sail encodes an LR's and an SC's flags as
`aq` / `aq && rl` (LR: `vmem_read … aq (aq && rl) true`, InstsEnd.lean:18236) and `aq && rl` / `rl` (SC:
`vmem_write … (aq && rl) rl true`, :17769–17770), mapped by `read_kind_of_flags`/`write_kind_of_flags`
(Mem.lean:222–255) and `read_ram`/`write_ram` (PhysMemInterface.lean:296–365): `(aq, aq && rl) = (true, true)` is
`Read_RISCV_reserved_strong_acquire` ↦ `AK_arch`, `(true, true)` on a write is
`Write_RISCV_conditional_strong_release` ↦ `AK_arch`; a one-bit kind is `AK_explicit` with `AS_rel_or_acq`.  So
`AK_arch` is exactly an `lr.aqrl` / `sc.aqrl`, whose second annotation (release on the LR, acquire on the SC) is
rvwmo.adoc:124–128 "An AMO, lr, or sc instruction with both aq and rl set has both acquire-RCsc and release-RCsc
annotations".  (Sail has no Zalasr kind: an unreserved acquire load or release store is an `internal_error`, so a
plain access is never `AK_arch`.)  Mark: FAITHFUL. -/
def akStrong (k : AK) : Bool :=
  match k with
  | .AK_arch _ => true
  | _ => false

/-- A page-table walk read (`AK_ttw`): no arm in this increment (translation deferred, [OWN.P3]). -/
def isTtw (k : AK) : Bool :=
  match k with
  | .AK_ttw _ => true
  | _ => false

/-! ## 2. The hart's program state -/

/-- THE PER-INSTRUCTION INSTANCE CHANNEL (v2's `Ibch`): reset at every instruction boundary.
* `bits` — the announced instruction (the decoder's input);
* `trapped` — the instruction trapped (FC-5: set at the trap's `mcause`/`scause` write);
* `scOk` — this SC's conditional write succeeded (M4); `scEnd` — the end-of-SC `LExFail` was emitted (M16 (c1));
* `amoRd` — an AMO read's base and old bytes; `amoWr` — its write happened; `wbDone` — the failed-`amocas`
  write-back was emitted (zacas.adoc:159–161);
* `racc` / `woff` — a decomposition in progress ([OWN.P1]): the bytes answered so far / the bytes written so far;
* `cmoDone` — the Zicbom operation was emitted. -/
structure Ix where
  bits : Option (BitVec 32)
  trapped : Bool
  scOk : Bool
  scEnd : Bool
  amoRd : Option (Int × List (BitVec 8))
  amoWr : Bool
  wbDone : Bool
  racc : List (Nat × BitVec 8)
  woff : Nat
  cmoDone : Bool
  /-- FIX S0rest-F1: the old CSR view was captured into `csrOldKey` -/
  csrOld : Bool

/-- The empty channel (an instruction boundary). -/
def ixNone : Ix := ⟨none, false, false, false, none, false, false, [], 0, false, false⟩

/-- A hart: its CPU, the residual Sail monad of the current step, its register file, the parked FENCE.TSO half
(M6; it gates every later step of the hart, so it is applied before the next memory event), and the channel. -/
structure HState where
  cpu : CPU
  m : SailM Unit
  rs : RegFile
  fn : Option (Bool × Bool × Bool × Bool)
  ix : Ix

/-! ## 3. The node dispatch -/

/-- FIX S0rest-F1: is this register read the (first) read of the CSR of a Zicsr read-modify-write with a GPR
destination?  Then the key of the CSR. -/
def csrCapture (ix : Ix) (r : Register) : Option Nat :=
  if ix.csrOld then none else
  match v2Roles ix.bits with
  | .ORcsr p _ rd =>
    if rd = 0 then none else
    match eregNum r with
    | some n => if (n : Int) = p then some n else none
    | none => none
  | _ => none


/-- The answered bytes `tvs` are the bytes of `w` (little-endian). -/
def answers (n : Nat) (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)) : Prop :=
  tvs.length = n ∧ ∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)

/-- THE BOUNDARY (`.pure`): the end-of-instruction events, then the reset.
* end of SC (M16 (c1), FC-5, D-S0-5): an SC that did not trap clears the reservation (`LExFail`) first;
* failed `amocas` write-back ([OWN.P1], zacas.adoc:159–161 "An unsuccessful amocas.w/d/q may either not perform a
  memory write or may write back the old value loaded from memory. The memory write, if produced, does not have
  release semantics, regardless of rl"): OPTIONAL, as the AMO write half (atomic with the read through the slot),
  rl false, data = the old bytes;
* a Zicbom operation ([OWN.P1], `cboKind`), mandatory unless the instruction trapped; its address source is `rs1`;
* `LInstr`: the next Sail step. -/
def bndStep (h : HState) (l : PLabel) (h' : HState) : Prop :=
  (isSC h.ix.bits = true ∧ h.ix.trapped = false ∧ h.ix.scEnd = false ∧
    l = LExFail ∧ h' = { h with ix := { h.ix with scEnd := true } }) ∨
  (∃ b old, isAmocas h.ix.bits = true ∧ h.ix.amoRd = some (b, old) ∧ h.ix.amoWr = false ∧
    h.ix.wbDone = false ∧ h.ix.trapped = false ∧
    l = LAmoSt false b old (depsAddr (v2Roles h.ix.bits)) [] ∧
    h' = { h with ix := { h.ix with wbDone := true } }) ∨
  (∃ k w, cboKind h.ix.bits = some k ∧ h.ix.bits = some w ∧ h.ix.trapped = false ∧ h.ix.cmoDone = false ∧
    l = LCmo k (cboBase h.rs w) cboLen (dsrcOfRs1 w) ∧
    h' = { h with ix := { h.ix with cmoDone := true } }) ∨
  (∃ tick : Bool, (isSC h.ix.bits = false ∨ h.ix.trapped = true ∨ h.ix.scEnd = true) ∧
    ((cboKind h.ix.bits).isNone ∨ h.ix.trapped = true ∨ h.ix.cmoDone = true) ∧
    l = LInstr ∧ h' = { h with m := riscvStep tick, ix := ixNone })

/-- THE RAM READ ARM (plain, LR, AMO read, fetch).  A decomposable read ([OWN.P1]) answers its bytes in any
contiguous chunks, each its own `LLoad`; the Sail node continues when the last chunk is answered. -/
def ramRead (h : HState) (n : Nat) (pa : PAddr) (ak : AK) (k : Result ((BitVec (8 * n)) × Option Bool) Unit → SailM Unit)
    (l : PLabel) (h' : HState) : Prop :=
  isTtw ak = false ∧
  if akIfetch ak then
    -- [OWN.P2]: THE FETCH (no aq, no address sources)
    ∃ (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)),
      answers n w tvs ∧ l = LIFetch (paZ pa) tvs ∧ h' = { h with m := k (.Ok (w, none)) }
  else if akExcl ak then
    ∃ (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)),
      answers n w tvs ∧ h'.m = k (.Ok (w, none)) ∧ h'.cpu = h.cpu ∧ h'.rs = h.rs ∧ h'.fn = h.fn ∧
      (if isLR h.ix.bits then
         -- LR (M3: address sources on the label)
         l = LExLoad (akAcq ak) (akStrong ak) (paZ pa) tvs (depsAddr (v2Roles h.ix.bits)) ∧ h'.ix = h.ix
       else
         -- AMO read half (M10)
         l = LAmoLd (akAcq ak) (paZ pa) tvs (depsAddr (v2Roles h.ix.bits)) ∧
         h'.ix = { h.ix with amoRd := some (paZ pa, tvs.map Prod.snd) })
  else
    -- plain RAM load (D-8 fixed: address sources on the label), possibly decomposed
    ∃ (tvs : List (Nat × BitVec 8)),
      tvs ≠ [] ∧ h.ix.racc.length + tvs.length ≤ n ∧
      (splittable h.ix.bits n = true ∨ tvs.length = n) ∧
      l = LLoad (akAcq ak) (akStrong ak) (paZ pa + h.ix.racc.length) tvs (depsAddr (v2Roles h.ix.bits)) ∧
      (if h.ix.racc.length + tvs.length = n then
         ∃ w : BitVec (8 * n), answers n w (h.ix.racc ++ tvs) ∧
           h' = { h with m := k (.Ok (w, none)), ix := { h.ix with racc := [] } }
       else h' = { h with ix := { h.ix with racc := h.ix.racc ++ tvs } })

/-- THE RAM WRITE ARM (plain, SC, AMO write). -/
def ramWrite (h : HState) (n : Nat) (pa : PAddr) (ak : AK) (v : BitVec (8 * n))
    (k : Result (Option Bool) Unit → SailM Unit) (l : PLabel) (h' : HState) : Prop :=
  let bs := Weak.WeakInterpProj.wbytes n v
  let asrc := depsAddr (v2Roles h.ix.bits)
  let vsrc := depsVsrc (v2Roles h.ix.bits)
  n ≠ 0 ∧
  if akExcl ak then
    if isSC h.ix.bits then
      -- SC: success, or the memory-level failure answer `.Err ()` (FC-1)
      (l = LExStore (akStrong ak) (akRel ak) (paZ pa) bs asrc vsrc ∧
        h' = { h with m := k (.Ok (some true)), ix := { h.ix with scOk := true } }) ∨
      (l = LExFail ∧ h' = { h with m := k (.Err ()) })
    else
      -- AMO write half (M10); `.Ok (some true)` only
      l = LAmoSt (akAcq ak) (paZ pa) bs asrc vsrc ∧
      h' = { h with m := k (.Ok (some true)), ix := { h.ix with amoWr := true } }
  else
    -- plain RAM store, possibly decomposed ([OWN.P1])
    ∃ c : Nat, 0 < c ∧ h.ix.woff + c ≤ n ∧ (splittable h.ix.bits n = true ∨ c = n) ∧
      l = LStore (akStrong ak) (akRel ak) (paZ pa + h.ix.woff) ((bs.drop h.ix.woff).take c) asrc vsrc ∧
      (if h.ix.woff + c = n then h' = { h with m := k (.Ok (some true)), ix := { h.ix with woff := 0 } }
       else h' = { h with ix := { h.ix with woff := h.ix.woff + c } })

/-- THE REGISTER-WRITE ARM (M19, FC-4, FC-5).  `nextPC` ↦ the syntactic control label; a tracked register ↦
`LRegW` with `regSrcs`; any other register ↦ `LSilent`.  A write of `mcause`/`scause` marks the trap. -/
def regWriteStep (h : HState) (r : Register) (v : RegisterType r) (k : PUnit → SailM Unit) (l : PLabel)
    (h' : HState) : Prop :=
  h' = { h with m := k PUnit.unit, rs := h.rs.set r v,
                ix := { h.ix with trapped := h.ix.trapped || decide (r = .mcause ∨ r = .scause) } } ∧
  (if r = .nextPC then l = LCtrl (depsCtrl (v2Roles h.ix.bits))
   else match eregNum r with
     | some num => l = LRegW num (regSrcs h.ix.bits h.ix.scOk num)
     | none => l = LSilent)

/-- THE NODE DISPATCH: one arm per lean-sail `Outcome` constructor (Table C family C-E). -/
def hnodeStep (h : HState) (d : DevStates) (l : PLabel) (h' : HState) (d' : DevStates) : Prop :=
  match h.m with
  | .pure _ => d' = d ∧ bndStep h l h'
  -- MachFix-havoc ([OWN.P8]/[OWN.P9]): a remaining Sail error site is HAVOC — no step here; a valid run reaching it
  -- makes every observation possible (MachHavoc.lean `allowedH`, EmitHavoc.lean `sailErr`)
  | .impure (.error _) _ => False
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k =>
        d' = d ∧
        (match csrCapture h.ix r with
         | some n => l = LRegW csrOldKey [.DReg n] ∧                       -- FIX S0rest-F1
             h' = { h with m := k (h.rs r), ix := { h.ix with csrOld := true } }
         | none => l = LSilent ∧ h' = { h with m := k (h.rs r) })
    | .regWrite r v, k => d' = d ∧ regWriteStep h r v k l h'
    | .memRead n _va req, k =>
        if devAddr req.pa then
          -- MMIO READ (M12: `LDev`, no view); [OWN.P1]: no device at the address ⇒ any answer, fabric unchanged
          ∃ w : BitVec (8 * n),
            (devRead d req.pa n = some (w, d') ∨ (devRead d req.pa n = none ∧ d' = d)) ∧
            l = LDev .rd (paZ req.pa) (Weak.WeakInterpProj.wbytes n w) (depsAddr (v2Roles h.ix.bits)) [] ∧
            h' = { h with m := k (.Ok (w, none)) }
        else d' = d ∧ ramRead h n req.pa req.access_kind k l h'
    | .memWrite n _va req, k =>
        match req.value with
        | some v =>
          if devAddr req.pa then
            -- MMIO WRITE; [OWN.P1]: no device ⇒ accepted, fabric unchanged
            (devWrite d req.pa n v = some d' ∨ (devWrite d req.pa n v = none ∧ d' = d)) ∧
            l = LDev .wr (paZ req.pa) (Weak.WeakInterpProj.wbytes n v) (depsAddr (v2Roles h.ix.bits))
              (depsVsrc (v2Roles h.ix.bits)) ∧
            h' = { h with m := k (.Ok (some true)) }
          else d' = d ∧ ramWrite h n req.pa req.access_kind v k l h'
        | none => False
    | .barrier b, k =>
        l = barLabel b ∧ d' = d ∧ h' = { h with m := k (), fn := ebarPark b }
    -- the announce banks the bits and resets nothing (the fetch view must survive, PA-1f)
    | .instrAnnounce _ w, k =>
        l = LSilent ∧ d' = d ∧ h' = { h with m := k (), ix := { h.ix with bits := some (ibOfBvn w) } }
    | .branchAnnounce _ _, k => l = LSilent ∧ d' = d ∧ h' = { h with m := k () }
    | .cacheOp _, k => l = LSilent ∧ d' = d ∧ h' = { h with m := k () }
    | .tlbi _, k => l = LSilent ∧ d' = d ∧ h' = { h with m := k () }
    | .takeException _, k => l = LSilent ∧ d' = d ∧ h' = { h with m := k (), ix := { h.ix with trapped := true } }
    | .returnException _, k => l = LSilent ∧ d' = d ∧ h' = { h with m := k () }
    | .translationStart _, k => l = LSilent ∧ d' = d ∧ h' = { h with m := k () }
    | .translationEnd _, k => l = LSilent ∧ d' = d ∧ h' = { h with m := k () }
    | .cycleCount, k => l = LSilent ∧ d' = d ∧ h' = { h with m := k () }
    | .message _, k => l = LSilent ∧ d' = d ∧ h' = { h with m := k () }
    -- [OWN.P1] C-S constant row: the cycle counter is not fixed by the text; any answer
    | .getCycleCount, k => ∃ c : Nat, l = LSilent ∧ d' = d ∧ h' = { h with m := k c }
    | .choose _, k => ∃ ch, l = LSilent ∧ d' = d ∧ h' = { h with m := k ch }
    | .readRam .., _ => False
    | .writeRam .., _ => False

/-- THE HART STEP: the parked FENCE.TSO half gates everything (M6, SR-24); otherwise the node dispatch. -/
def hstep (h : HState) (d : DevStates) (l : PLabel) (h' : HState) (d' : DevStates) : Prop :=
  match h.fn with
  | some (pr, pw, sr, sw) => l = LFence pr pw sr sw ∧ d' = d ∧ h' = { h with fn := none }
  | none => hnodeStep h d l h' d'

/-! ## 4. The program step at machine v2's type -/

/-- THE PROGRAM STEP of emission v2 (harts only in this increment): the `pstep` argument of `Machine.pmStep`, with
`P := HState` and fabric `D := DevStates`.  The CPU never changes. -/
def pstepV2 (h : HState) (d : DevStates) (l : PLabel) (h' : HState) (d' : DevStates) : Prop :=
  h'.cpu = h.cpu ∧ hstep h d l h' d'

/-! ## 5. The scope predicate ([OWN.P3]) -/

/-- `satp.MODE = Bare` (bits 63:60 are zero) in a register file. -/
def satpBare (rs : RegFile) : Prop :=
  BitVec.extractLsb 63 60 (rs Register.satp) = 0#4

/-- Reachability in the program LTS, over any labels and any fabric values. -/
inductive reachH : HState → HState → Prop
  | refl (h : HState) : reachH h h
  | step (h h1 h2 : HState) (d d' : DevStates) (l : PLabel) :
      pstepV2 h d l h1 d' → reachH h1 h2 → reachH h h2

/-- THE SCOPE OF THIS INCREMENT: no reachable state of any hart enables translation.  (In M-mode translation is
Bare whatever `satp` holds; requiring `satp.MODE = Bare` also covers S/U-mode and `mstatus.MPRV`.) -/
def translationOff (ps : List HState) : Prop :=
  ∀ h ∈ ps, ∀ h', reachH h h' → satpBare h'.rs

/-- A hart at an instruction boundary, ready to run. -/
def hartInit (cpu : CPU) (rs : RegFile) : HState := ⟨cpu, .pure (), rs, none, ixNone⟩

end Weak.Prom
