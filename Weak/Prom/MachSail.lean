/-
Weak/Prom: **machine v2 on litmus programs THROUGH THE SAIL MODEL** (S0-P part (2), milestone 3): each litmus hart
is assembled into RV64 machine code, run by the Sail model's own `riscvStep` (at reservation platform `P`,
`Weak/Prom/SailExec.lean`) through an executable transcription of emission v2 (`Weak/Prom/Emit.lean`
`hnodeStep`/`hstep`, M-mode, phase-1 scope `translationOff`), and the label streams it emits are fed to the
milestone-1 explorer (`MachExplore.succ`, plus the three arms the label level never needs: `LIFetch`, `LAmoLd`,
`LAmoSt`).

## The program side (Sail, one hart)

* MEMORY IMAGE.  Phase-1 Sail RAM is `[0x80000000, 0x88000000)` (model/sail-config-rv64d.json `memory.regions`;
  everything below is MMIO, `MachCSL.devAddr`), so the test's locations are RELOCATED by `OFF = 0x80000000`
  (`x 0x1000 ↦ 0x80001000`, …): the image's bytes, initial register values that are location addresses, and `li`
  immediates that are location addresses.  Final register values in a location's window are mapped back, so outcomes
  compare with the label level's.  An initial memory value that is a location address is out of scope ("pointer in
  memory").  Hart `h`'s code is at `codeBase h = 0x80400000 + 0x10000·h` (image bytes, timestamp 0; never written).
* ASSEMBLY (`asmInstr`): the standard RV64 encodings (unpriv base / Zalrsc / Zaamo / FENCE / Zifencei);
  `li rd, v` is `addi` when `v` fits 12 bits, else `lui`+`addiw` (`v` a sign-extended 32-bit value) or
  `lui`+`addiw`+`slli 32`+`srli 32` (`v < 2^32`, the relocated addresses): no source register, so the same
  (empty) dependency.  Out of scope: Zalasr `l*.aq`/`s*.rl` and the RCpc forms (Sail has no such access kind:
  `read_kind_of_flags`/`write_kind_of_flags` raise `internal_error`, Mem.lean:222–255), `csrr`.
* START STATE: the platform's power-on register file (`MachCSL.bootProg` run by `bootRun`, as `Vtest.bootRegsOf`:
  M-mode, `satp = 0`, interrupts disabled), then `PC := codeBase h` and the test's GPRs.
* EMISSION (`sNext`): one Sail event per call, the label of `Emit.hnodeStep`/`hstep` for that event (register reads
  and the other silent events are `LSilent`; `nextPC` writes `LCtrl (depsCtrl …)`; tracked register writes
  `LRegW r (regSrcs …)` — the DECODER's sources; loads/LR `LLoad`/`LExLoad` with `akAcq`/`akStrong`; plain stores and
  SCs `LStore`/`LExStore` with `akStrong`/`akRel`; the AMO halves `LAmoLd`/`LAmoSt` through the `wRmw` slot; an SC
  write may also take Sail's failure answer `.Err ()` (label `LExFail`); the end-of-SC `LExFail` at the boundary;
  barriers `barLabel` with FENCE.TSO's second half PARKED (`fn`) and applied before the next event; fetches
  `LIFetch`).  A hart is DONE at an instruction boundary whose `PC` is its code end.  Stopped (counted, never a
  verdict): a trap (the write of `mcause`, or `takeException`), an MMIO access, a decomposable access, `choose`,
  `getCycleCount`, `amocas`/Zicbom, fuel.  The clock tick is not taken (`riscvStep false`): it changes only the
  timer state, and interrupts are disabled.
* THE PROGRAM TREE (`build`): the hart's Sail run with every read answered from a value DOMAIN (all byte runs),
  as a tree of non-silent labels: reads branch on the answered bytes, an SC write on success / `.Err ()`.  The tree
  depends only on the answers (the Sail side never sees views or timestamps), so it is built ONCE per hart per
  domain and walked by every machine run.

## The explorer (as milestone 1, `MachLitmus.lean`, with the program side replaced)

Candidate final memories: per hart the message lists of its tree over the domain, iterated from the image as in
`sigmaAll` (Sail-level free runs instead of the litmus interpreter's).  For each arrangement `M` each hart walks its
tree against `M` (`runT`): a read node takes every `succ`-successor and follows the child with the answered bytes
(a missing child is a DOMAIN MISS, counted and reported: it would mean the domain is not closed); a write node
every `succ`-successor of its template.  Reservation platforms: the SC addresses `A` of the all-true trees; every
`P` with `P a ∈ {true, false}` for `a ∈ A` (`2^|A|`, consistently for all harts and all SCs of a run); the outcome
set is the union.
-/
import Weak.Prom.SailExec
import Weak.Prom.MachLitmus
import Vtest.XState

namespace Weak.Prom.SailLit

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Weak (Image Dsrc depsCtrl depsAddr depsVsrc eregNum ebarPark ibOfBvn paZ)
open Weak.Prom
open Weak.Prom.Mach
open Weak.Prom.Ref (Instr Test two64 AmoOp Alu BrC)
open PLabel

/-! ## 1. Layout and relocation -/

def OFF : Nat := 0x80000000

def codeBase (h : Nat) : Nat := 0x80400000 + 0x10000 * h

/-- Is `v` an address in a location's window (`[a, a + 0x1000)`)? -/
def isLoc (locs : List Nat) (v : Nat) : Bool := locs.any (fun a => decide (a ≤ v) && decide (v < a + 0x1000))

def reloc (locs : List Nat) (v : Nat) : Nat := if isLoc locs v then v + OFF else v

def unreloc (locs : List Nat) (v : Nat) : Nat :=
  if decide (OFF ≤ v) && isLoc locs (v - OFF) then v - OFF else v

/-! ## 2. The assembler -/

def fld (v hi lo : Nat) : Nat := (v >>> lo) % 2 ^ (hi - lo + 1)

def rType (f7 rs2 rs1 f3 rd op : Nat) : Nat :=
  (f7 <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) ||| (f3 <<< 12) ||| (rd <<< 7) ||| op

def iType (imm rs1 f3 rd op : Nat) : Nat :=
  ((imm % 4096) <<< 20) ||| (rs1 <<< 15) ||| (f3 <<< 12) ||| (rd <<< 7) ||| op

def sType (imm rs2 rs1 f3 op : Nat) : Nat :=
  (fld imm 11 5 <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) ||| (f3 <<< 12) ||| (fld imm 4 0 <<< 7) ||| op

def bType (off rs2 rs1 f3 : Nat) : Nat :=
  (fld off 12 12 <<< 31) ||| (fld off 10 5 <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) ||| (f3 <<< 12) |||
    (fld off 4 1 <<< 8) ||| (fld off 11 11 <<< 7) ||| 0x63

def jType (off rd : Nat) : Nat :=
  (fld off 20 20 <<< 31) ||| (fld off 10 1 <<< 21) ||| (fld off 11 11 <<< 20) ||| (fld off 19 12 <<< 12) |||
    (rd <<< 7) ||| 0x6F

/-- A 64-bit two's-complement value fits a signed 12-bit immediate. -/
def fits12 (v : Nat) : Bool := decide (v < 2048) || decide (two64 - 2048 ≤ v ∧ v < two64)

def b2n (b : Bool) : Nat := if b then 1 else 0

/-- `li rd, v`. -/
def liSeq (rd v : Nat) : Except String (List Nat) :=
  if fits12 v then .ok [iType v 0 0 rd 0x13] else
  -- `lui`+`addiw` produce the sign extension of a 32-bit pattern `w`
  let luiAddiw := fun (w : Nat) =>
    let lo := w % 4096
    let hi := ((w + 2048) >>> 12) % 1048576
    [(hi <<< 12) ||| (rd <<< 7) ||| 0x37, iType lo rd 0 rd 0x1B]
  if v < 2 ^ 31 || (two64 - 2 ^ 31 ≤ v && v < two64) then .ok (luiAddiw (v % 2 ^ 32))
  else if v < 2 ^ 32 then
    .ok (luiAddiw v ++ [iType 32 rd 1 rd 0x13, iType 32 rd 5 rd 0x13])
  else .error s!"li immediate {v}"

def aluF (op : Alu) : Option (Nat × Nat) :=   -- (funct7, funct3) of the R-type form
  match op with
  | .add => some (0, 0) | .sub => some (0x20, 0) | .sll => some (0, 1) | .slt => some (0, 2)
  | .sltu => some (0, 3) | .xor => some (0, 4) | .srl => some (0, 5) | .sra => some (0x20, 5)
  | .or => some (0, 6) | .and => some (0, 7) | .mul => some (1, 0)

def amoF5 (op : AmoOp) : Nat :=
  match op with
  | .add => 0 | .swap => 1 | .xor => 4 | .or => 8 | .and => 12 | .min => 16 | .max => 20 | .minu => 24
  | .maxu => 28

def szF3 (sz : Nat) : Except String Nat :=
  match sz with
  | 1 => .ok 0 | 2 => .ok 1 | 4 => .ok 2 | 8 => .ok 3 | _ => .error s!"size {sz}"

def brF3 (c : BrC) : Nat :=
  match c with
  | .eq => 0 | .ne => 1 | .lt => 4 | .ge => 5 | .ltu => 6 | .geu => 7

/-- The words of one instruction at address `pc`; `addrOf k` is the address of instruction `k`. -/
def asmInstr (locs : List Nat) (addrOf : Nat → Nat) (pc : Nat) : Instr → Except String (List Nat)
  | .alui op rd rs1 imm =>
    match op with
    | .add =>
      if rs1 = 0 then liSeq rd (reloc locs imm)
      else if fits12 imm then .ok [iType imm rs1 0 rd 0x13] else .error "addi immediate"
    | .xor | .or | .and | .slt | .sltu =>
      let f3 := match op with | .xor => 4 | .or => 6 | .and => 7 | .slt => 2 | _ => 3
      if fits12 imm then .ok [iType imm rs1 f3 rd 0x13] else .error "immediate"
    | .sll => if imm < 64 then .ok [iType imm rs1 1 rd 0x13] else .error "shift"
    | .srl => if imm < 64 then .ok [iType imm rs1 5 rd 0x13] else .error "shift"
    | .sra => if imm < 64 then .ok [iType (imm ||| 0x400) rs1 5 rd 0x13] else .error "shift"
    | _ => .error "alui op"
  | .alu op rd rs1 rs2 =>
    match aluF op with
    | some (f7, f3) => .ok [rType f7 rs2 rs1 f3 rd 0x33]
    | none => .error "alu op"
  | .load sz sgn rd rs1 off => do
    let f3 ← match sz, sgn with
      | 1, true => pure 0 | 2, true => pure 1 | 4, true => pure 2 | 8, _ => pure 3
      | 1, false => pure 4 | 2, false => pure 5 | 4, false => pure 6 | _, _ => throw "load size"
    if fits12 off then pure [iType off rs1 f3 rd 0x03] else throw "load offset"
  | .store sz rs2 rs1 off => do
    let f3 ← szF3 sz
    if fits12 off then pure [sType off rs2 rs1 f3 0x23] else throw "store offset"
  | .loadAq .. => .error "Zalasr load-acquire (no Sail access kind)"
  | .storeRl .. => .error "Zalasr store-release (no Sail access kind)"
  | .loadAqPc .. => .error "RCpc load"
  | .storeRlPc .. => .error "RCpc store"
  | .lr sz aq rl rd rs1 => do
    let f3 ← szF3 sz
    pure [rType ((2 <<< 2) ||| (b2n aq <<< 1) ||| b2n rl) 0 rs1 f3 rd 0x2F]
  | .sc sz aq rl rd rs2 rs1 => do
    let f3 ← szF3 sz
    pure [rType ((3 <<< 2) ||| (b2n aq <<< 1) ||| b2n rl) rs2 rs1 f3 rd 0x2F]
  | .amo op sz aq rl rd rs2 rs1 => do
    let f3 ← szF3 sz
    pure [rType ((amoF5 op <<< 2) ||| (b2n aq <<< 1) ||| b2n rl) rs2 rs1 f3 rd 0x2F]
  | .fence f =>
    let pred := (b2n f.pi <<< 3) ||| (b2n f.po <<< 2) ||| (b2n f.pr <<< 1) ||| b2n f.pw
    let succ := (b2n f.si <<< 3) ||| (b2n f.so <<< 2) ||| (b2n f.sr <<< 1) ||| b2n f.sw
    .ok [(pred <<< 24) ||| (succ <<< 20) ||| 0x0F]
  | .fenceTso => .ok [0x8330000F]
  | .br c rs1 rs2 tgt =>
    let off := addrOf tgt - pc
    if addrOf tgt ≤ pc || 4096 ≤ off then .error "branch target" else .ok [bType off rs2 rs1 (brF3 c)]
  | .jmp tgt =>
    let off := addrOf tgt - pc
    if addrOf tgt ≤ pc || 2 ^ 20 ≤ off then .error "jump target" else .ok [jType off 0]
  | .csrr .. => .error "csrr (no CSR number)"
  | .fencei => .ok [0x0000100F]
  | .nop => .ok [0x13]

/-- The number of words of an instruction (independent of the targets). -/
def nWords (locs : List Nat) (i : Instr) : Nat :=
  match asmInstr locs (fun _ => 0) 0 i with
  | .ok ws => ws.length
  | .error _ => 1

/-- A hart's program as words at `codeBase h`; the end address. -/
def asmProg (locs : List Nat) (h : Nat) (prog : List Instr) : Except String (List Nat × Nat) := do
  let sizes := prog.map (nWords locs)
  let starts := (sizes.foldl (fun (acc : List Nat × Nat) s => (acc.1 ++ [acc.2], acc.2 + 4 * s)) ([], codeBase h))
  let addrOf := fun (k : Nat) => (starts.1[k]?).getD starts.2
  let words ← (List.range prog.length).foldlM (fun (acc : List Nat) k => do
    let i := (prog[k]?).getD .nop
    let ws ← asmInstr locs addrOf (addrOf k) i
    pure (acc ++ ws)) []
  pure (words, starts.2)

/-! ## 3. The start state -/

/-- The power-on register file of hart `hid` (the platform's boot program from the all-default file, as
`Vtest.bootRegsOf`), as an `XRegs`. -/
def bootX (hid : Nat) : Vtest.XRegs :=
  let f : RegFile := ((bootRun (bootProg (BitVec.ofNat 64 hid) bootPMA) Vtest.zeroRegs).map (·.2)).getD Vtest.zeroRegs
  (List.range Vtest.nRegs).foldl (fun m k => let r := Register.ofNat k; m.insert r (f r)) ∅

def setGpr (x : Vtest.XRegs) (n : Nat) (v : BitVec 64) : Vtest.XRegs :=
  match n with
  | 1 => x.insert .x1 v | 2 => x.insert .x2 v | 3 => x.insert .x3 v | 4 => x.insert .x4 v
  | 5 => x.insert .x5 v | 6 => x.insert .x6 v | 7 => x.insert .x7 v | 8 => x.insert .x8 v
  | 9 => x.insert .x9 v | 10 => x.insert .x10 v | 11 => x.insert .x11 v | 12 => x.insert .x12 v
  | 13 => x.insert .x13 v | 14 => x.insert .x14 v | 15 => x.insert .x15 v | 16 => x.insert .x16 v
  | 17 => x.insert .x17 v | 18 => x.insert .x18 v | 19 => x.insert .x19 v | 20 => x.insert .x20 v
  | 21 => x.insert .x21 v | 22 => x.insert .x22 v | 23 => x.insert .x23 v | 24 => x.insert .x24 v
  | 25 => x.insert .x25 v | 26 => x.insert .x26 v | 27 => x.insert .x27 v | 28 => x.insert .x28 v
  | 29 => x.insert .x29 v | 30 => x.insert .x30 v | 31 => x.insert .x31 v
  | _ => x

/-- The GPR values `x0 … x31`. -/
def gprsOf (x : Vtest.XRegs) : Array Nat :=
  ((List.range 32).map (fun r => (gprVal (Vtest.XRegs.file x) (r : Int)).toNat)).toArray

/-! ## 4. The emission, executably (Emit.lean `hstep` / `hnodeStep`) -/

/-- A Sail hart: the residual model computation, the register file, the parked FENCE.TSO half, the channel. -/
structure SH where
  m : SailM Unit
  rs : Vtest.XRegs
  fn : Option (Bool × Bool × Bool × Bool)
  ix : Ix

/-- A read template. -/
inductive RdK where
  | ld (aq rl : Bool) (asrc : List Dsrc)
  | lr (aq rl : Bool) (asrc : List Dsrc)
  | amo (aq : Bool) (asrc : List Dsrc)
  | fetch

/-- A write template. -/
inductive WrK where
  | st (aq rl : Bool) (asrc vsrc : List Dsrc)
  | sc (aq rl : Bool) (asrc vsrc : List Dsrc)
  | amo (rl : Bool) (asrc vsrc : List Dsrc)

/-- The next event of a Sail hart. -/
inductive SEv where
  | lab (l : PLabel) (h : SH)
  | rd (k : RdK) (base : Int) (sz : Nat) (cont : List (BitVec 8) → SH)
  | wr (k : WrK) (base : Int) (data : List (BitVec 8)) (ok : SH) (ko : Option SH)
  | done
  | stop (why : String)

instance : Inhabited SEv := ⟨.done⟩

def isReg (r r' : Register) : Bool := r.ctorIdx == r'.ctorIdx

/-- ONE EVENT (Emit.lean `hstep`; the boundary is `bndStep`, the rest `hnodeStep`'s arms). -/
def sNext (P : BitVec 64 → Bool) (endPC : BitVec 64) (h : SH) : SEv :=
  match h.fn with
  | some (pr, pw, sr, sw) => .lab (LFence pr pw sr sw) { h with fn := none }
  | none =>
  match h.m with
  | .pure _ =>
    if isSC h.ix.bits && !h.ix.trapped && !h.ix.scEnd then
      .lab LExFail { h with ix := { h.ix with scEnd := true } }
    else if h.ix.trapped then .stop "trap"
    else if isAmocas h.ix.bits then .stop "amocas"
    else if (cboKind h.ix.bits).isSome then .stop "cbo"
    else if h.rs.get .PC == endPC then .done
    else .lab LInstr { h with m := riscvStepP P false, ix := ixNone }
  | .impure (.error _) _ => .stop "sail-error"
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k => .lab LSilent { h with m := k (h.rs.get r) }
    | .regWrite r v, k =>
      if isReg r .mcause || isReg r .scause then .stop "trap" else
      let h' : SH := { h with m := k PUnit.unit, rs := h.rs.insert r v }
      if isReg r .nextPC then .lab (LCtrl (depsCtrl (v2Roles h.ix.bits))) h'
      else match eregNum r with
        | some num => .lab (LRegW num (regSrcs h.ix.bits h.ix.scOk num)) h'
        | none => .lab LSilent h'
    | .memRead n _ req, k =>
      if devAddr req.pa then .stop "mmio" else
      let ak := req.access_kind
      if isTtw ak then .stop "ttw" else
      let asrc := depsAddr (v2Roles h.ix.bits)
      let pa := paZ req.pa
      if akIfetch ak then
        .rd .fetch pa n (fun bs => { h with m := k (.Ok (bvOfBytes n bs, none)) })
      else if akExcl ak then
        if isLR h.ix.bits then
          .rd (.lr (akAcq ak) (akStrong ak) asrc) pa n (fun bs => { h with m := k (.Ok (bvOfBytes n bs, none)) })
        else
          .rd (.amo (akAcq ak) asrc) pa n (fun bs =>
            { h with m := k (.Ok (bvOfBytes n bs, none)), ix := { h.ix with amoRd := some (pa, bs) } })
      else if splittable h.ix.bits n then .stop "decomposable"
      else .rd (.ld (akAcq ak) (akStrong ak) asrc) pa n (fun bs => { h with m := k (.Ok (bvOfBytes n bs, none)) })
    | .memWrite n _ req, k =>
      match req.value with
      | none => .stop "write-no-value"
      | some v =>
        if devAddr req.pa then .stop "mmio" else
        if n = 0 then .stop "empty-write" else
        let ak := req.access_kind
        let bs := Weak.WeakInterpProj.wbytes n v
        let asrc := depsAddr (v2Roles h.ix.bits)
        let vsrc := depsVsrc (v2Roles h.ix.bits)
        let pa := paZ req.pa
        if akExcl ak then
          if isSC h.ix.bits then
            .wr (.sc (akStrong ak) (akRel ak) asrc vsrc) pa bs
              { h with m := k (.Ok (some true)), ix := { h.ix with scOk := true } }
              (some { h with m := k (.Err ()) })
          else
            .wr (.amo (akAcq ak) asrc vsrc) pa bs
              { h with m := k (.Ok (some true)), ix := { h.ix with amoWr := true } } none
        else if splittable h.ix.bits n then .stop "decomposable"
        else .wr (.st (akStrong ak) (akRel ak) asrc vsrc) pa bs { h with m := k (.Ok (some true)) } none
    | .barrier b, k => .lab (barLabel b) { h with m := k (), fn := ebarPark b }
    | .instrAnnounce _ w, k => .lab LSilent { h with m := k (), ix := { h.ix with bits := some (ibOfBvn w) } }
    | .branchAnnounce _ _, k => .lab LSilent { h with m := k () }
    | .cacheOp _, k => .lab LSilent { h with m := k () }
    | .tlbi _, k => .lab LSilent { h with m := k () }
    | .takeException _, _ => .stop "trap"
    | .returnException _, k => .lab LSilent { h with m := k () }
    | .translationStart _, k => .lab LSilent { h with m := k () }
    | .translationEnd _, k => .lab LSilent { h with m := k () }
    | .cycleCount, k => .lab LSilent { h with m := k () }
    | .message _, k => .lab LSilent { h with m := k () }
    | .getCycleCount, _ => .stop "getCycleCount"
    | .choose _, _ => .stop "choose"
    | .readRam .., _ => .stop "readRam"
    | .writeRam .., _ => .stop "writeRam"

/-- Skip silent events (a loop). -/
partial def sNextNS (P : BitVec 64 → Bool) (endPC : BitVec 64) (h : SH) (n : Nat) : SEv × Nat :=
  match sNext P endPC h with
  | .lab LSilent h' => sNextNS P endPC h' (n + 1)
  | e => (e, n)

/-! ## 5. The program tree -/

inductive STree where
  | done (regs : Array Nat)
  | stop (why : String)
  | lab (l : PLabel) (t : STree)
  | rd (k : RdK) (base : Int) (sz : Nat) (kids : List (List (BitVec 8) × STree))
  | wr (k : WrK) (base : Int) (data : List (BitVec 8)) (ok : STree) (ko : Option STree)

instance : Inhabited STree := ⟨.stop "default"⟩

structure BCfg where
  P : BitVec 64 → Bool
  endPC : BitVec 64
  ans : Int → Nat → List (List (BitVec 8))
  maxInstr : Nat
  budget : Nat

/-- Build statistics: tree nodes, Sail events. -/
structure BSt where
  nodes : Nat := 0
  events : Nat := 0
  over : Bool := false

partial def build (c : BCfg) (h : SH) (ninstr : Nat) : StateM BSt STree := do
  let (e, n) := sNextNS c.P c.endPC h 0
  modify fun s => { s with nodes := s.nodes + 1, events := s.events + n + 1 }
  if (← get).nodes > c.budget then
    modify fun s => { s with over := true }
    return .stop "budget"
  match e with
  | .lab LInstr h' =>
    if ninstr ≥ c.maxInstr then return .stop "fuel"
    return .lab LInstr (← build c h' (ninstr + 1))
  | .lab l h' => return .lab l (← build c h' ninstr)
  | .rd k base sz cont =>
    let kids ← (c.ans base sz).mapM (fun bs => do return (bs, ← build c (cont bs) ninstr))
    return .rd k base sz kids
  | .wr k base data ok ko =>
    let t1 ← build c ok ninstr
    match ko with
    | some h2 => return .wr k base data t1 (some (← build c h2 ninstr))
    | none => return .wr k base data t1 none
  | .done => return .done (gprsOf h.rs)
  | .stop why => return .stop why

def wrCls : WrK → PClass
  | .st _ rl _ _ => stClass rl
  | .sc .. => .excl
  | .amo .. => .excl

/-- The message lists of the tree's complete paths. -/
partial def msgLists (i : Nat) : STree → List (List PMsg)
  | .done _ => [[]]
  | .stop _ => []
  | .lab _ t => msgLists i t
  | .rd _ _ _ kids => (kids.flatMap (fun p => msgLists i p.2)).eraseDups
  | .wr k base data ok ko =>
    ((msgLists i ok).map (⟨base, data, some i, wrCls k⟩ :: ·) ++
      (match ko with | some t => msgLists i t | none => [])).eraseDups

/-- The SC write addresses of the tree. -/
partial def scAddrs : STree → List Int
  | .done _ | .stop _ => []
  | .lab _ t => scAddrs t
  | .rd _ _ _ kids => (kids.flatMap (fun p => scAddrs p.2)).eraseDups
  | .wr k base _ ok ko =>
    ((match k with | .sc .. => [base] | _ => []) ++ scAddrs ok ++
      (match ko with | some t => scAddrs t | none => [])).eraseDups

/-- The stop reasons of the tree. -/
partial def stops : STree → List String
  | .done _ => []
  | .stop w => [w]
  | .lab _ t => stops t
  | .rd _ _ _ kids => (kids.flatMap (fun p => stops p.2)).eraseDups
  | .wr _ _ _ ok ko => (stops ok ++ (match ko with | some t => stops t | none => [])).eraseDups

/-! ## 6. The machine arms the label level never needs -/

/-- `memStep.amoLd`. -/
def succAmoLd (img : Image) (log : List PMsg) (prom : GSet Nat) (ws : PState) (aq : Bool) (base : Int) (sz : Nat)
    (asrc : List Dsrc) : List Succ :=
  let va := srcsView ws asrc
  let vpre := ldPre ws aq false va
  (readCands img log ws vpre base sz).filterMap (fun tvs =>
    if loadOkB img log ws vpre base tvs then
      some ⟨LAmoLd aq base tvs asrc, none,
        { loadRun ws aq false va base tvs with wRmw := some ⟨base, tvs.map Prod.fst, aq⟩ }, prom⟩
    else none)

/-- `memStep.amoSt`. -/
def succAmoSt (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) : List Succ :=
  match ws.wRmw with
  | none => []
  | some R =>
    if R.rmBase != base || R.rmTs.length != data.length then [] else
    let va := srcsView ws asrc
    let vd := srcsView ws vsrc
    ((writeTs log i prom ws base data .excl (stPre ws rl va vd)).filter (fun ts =>
        exclOkB log i base R.rmTs ts)).map (fun ts =>
      ⟨LAmoSt rl base data asrc vsrc, some ts,
        { amoPost (storeRun ws rl va ts base data.length ts) R.rmAq ts with wRmw := none }, prom \ {ts}⟩)

/-- `memStep.fetch`: every byte from every timestamp it is admissible at (`fetchByteOk`), complete by brute
force (a byte's timestamp is at most `|log|`). -/
def succFetch (img : Image) (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) (base : Int) (sz : Nat) :
    List Succ :=
  let opts := (List.range sz).map (fun k : Nat =>
    let a := base + (k : Int)
    (List.range (log.length + 1)).filterMap (fun t =>
      match memByte img log t a with
      | some v => if !writesInB log a t ws.wIfl then some (t, v) else none
      | none => none))
  let rec prod : List (List (Nat × BitVec 8)) → List (List (Nat × BitVec 8))
    | [] => [[]]
    | os :: rest => (prod rest).flatMap (fun tl => os.map (· :: tl))
  (prod opts).map (fun tvs =>
    ⟨LIFetch base tvs, none,
      { ws with
        wIfr := max ws.wIfr (bytesMax (fun _ t => t) base tvs)
        wIfv := max ws.wIfv (fetchView log i prom base tvs) }, prom⟩)

def rdSuccs (img : Image) (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) :
    RdK → Int → Nat → List Succ
  | .ld aq rl asrc, base, sz => succ img log i prom ws (.ld aq rl base sz asrc)
  | .lr aq rl asrc, base, sz => succ img log i prom ws (.lr aq rl base sz asrc)
  | .amo aq asrc, base, sz => succAmoLd img log prom ws aq base sz asrc
  | .fetch, base, sz => succFetch img log i prom ws base sz

def wrSuccs (img : Image) (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) :
    WrK → Int → List (BitVec 8) → List Succ
  | .st aq rl asrc vsrc, base, data => succ img log i prom ws (.st aq rl base data asrc vsrc)
  | .sc aq rl asrc vsrc, base, data => succ img log i prom ws (.sc aq rl base data asrc vsrc)
  | .amo rl asrc vsrc, base, data => succAmoSt log i prom ws rl base data asrc vsrc

/-! ## 7. A hart's runs against a final memory -/

structure MR where
  fin : List (Array Nat) := []
  oos : List String := []
  miss : Nat := 0
  nodes : Nat := 0

instance : Inhabited MR := ⟨{}⟩

def MR.add (a b : MR) : MR := ⟨a.fin ++ b.fin, (a.oos ++ b.oos).eraseDups, a.miss + b.miss, a.nodes + b.nodes⟩

/-- Walk the tree against `M` (every `succ`-successor at every node). -/
partial def runT (img : Image) (log : List PMsg) (i : Nat) (t : STree) (ws : PState) (prom : GSet Nat) : MR :=
  match t with
  | .done regs => if promDone log prom then { fin := [regs], nodes := 1 } else { nodes := 1 }
  | .stop why => { oos := [why], nodes := 1 }
  | .lab l t' =>
    match fixPost ws l with
    | some ws' => let r := runT img log i t' ws' prom; { r with nodes := r.nodes + 1 }
    | none => { oos := ["label needs answers"], nodes := 1 }
  | .rd k base sz kids =>
    (rdSuccs img log i prom ws k base sz).foldl (fun acc s =>
      let vals := ((labelReads s.l).map (fun p => p.2.map Prod.snd)).getD []
      match kids.lookup vals with
      | some t' => acc.add (runT img log i t' s.ws s.prom)
      | none => acc.add { miss := 1 }) { nodes := 1 }
  | .wr k base data ok ko =>
    let r1 := (wrSuccs img log i prom ws k base data).foldl (fun acc s =>
      acc.add (runT img log i ok s.ws s.prom)) { nodes := 1 }
    match ko with
    | some t' => r1.add (runT img log i t' { ws with wRes := none } prom)
    | none => r1

/-! ## 8. A test through Sail -/

/-- A test prepared for Sail: relocated image, per-hart start state, code end, instruction bound. -/
structure STest where
  T : Test
  locs : List Nat
  img : Image
  harts : List (SH × BitVec 64 × Nat)

/-- The relocated image: code bytes, then the test's bytes at `OFF + a`, zero elsewhere. -/
def mkImg (T : Test) (code : List (Nat × List Nat)) : Image :=
  let tbl : Std.HashMap Int (BitVec 8) := code.foldl (fun m (base, ws) =>
    (List.range ws.length).foldl (fun m k =>
      let w := (ws[k]?).getD 0
      (List.range 4).foldl (fun m j => m.insert ((base + 4 * k + j : Nat) : Int) (bv8 ((w >>> (8 * j)) % 256))) m)
      m) {}
  fun a => match tbl.get? a with
    | some b => some b
    | none => if (OFF : Int) ≤ a then some (bv8 (T.imgF (a - OFF).toNat)) else some 0#8

/-- Prepare a test (`locs`: the location addresses of the parse). -/
def prepare (T : Test) (locs : List Nat) (boot : Nat → Vtest.XRegs) : Except String STest := do
  -- an initial memory value that is a location address is out of scope
  for (a, _) in T.img do
    for w in [4, 8] do
      if a % w == 0 && isLoc locs (Ref.bytesVal ((List.range w).map (fun j => T.imgF (a + j)))) &&
          isLoc locs a then
        throw "pointer in memory"
  let progs ← (List.range T.harts.length).mapM (fun h => do
    let (ws, e) ← asmProg locs h (T.prog h)
    pure (h, ws, e))
  let img := mkImg T (progs.map (fun (h, ws, _) => (codeBase h, ws)))
  let harts := progs.map (fun (h, ws, e) =>
    let x0 := (boot h).insert .PC (BitVec.ofNat 64 (codeBase h))
    let x := (((T.regs0[h]?).getD []).foldl (fun x (r, v) => setGpr x r (BitVec.ofNat 64 (reloc locs v))) x0)
    ((⟨.pure (), x, none, ixNone⟩ : SH), BitVec.ofNat 64 e, ws.length + 4))
  pure ⟨T, locs, img, harts⟩

/-- The trees of every hart over the domain `d` at platform `P` (`none`: a budget was exceeded). -/
def trees (S : STest) (P : BitVec 64 → Bool) (d : Dom) (budget : Nat) : Option (List STree) × Nat :=
  S.harts.foldl (fun (acc : Option (List STree) × Nat) (h, e, mi) =>
    match acc.1 with
    | none => acc
    | some ts =>
      let c : BCfg := ⟨P, e, fun base sz => domRuns S.img d base sz, mi, budget⟩
      let (t, st) := (build c h 0).run {}
      (if st.over then none else some (ts ++ [t]), acc.2 + st.events)) (some [], 0)

/-- THE CLOSURE (as `sigmaAll`): the trees over the final domain and every hart's message lists. -/
def closure (S : STest) (P : BitVec 64 → Bool) (budget : Nat) :
    Option (List STree × List (List (List PMsg)) × Nat) × Nat :=
  let K := storeInstrs S.T
  let rec go : Nat → Dom → Nat → Nat → Option (List STree × List (List (List PMsg)) × Nat) × Nat
    | 0, _, _, ev => (none, ev)
    | fuel + 1, d, it, ev =>
      match trees S P d budget with
      | (none, ev') => (none, ev + ev')
      | (some ts, ev') =>
        let sig := (List.range ts.length).map (fun i => msgLists i ((ts[i]?).getD default))
        let d' := domOf S.img (sig.flatMap (fun s => s.flatten))
        if domSize d' == domSize d || K ≤ it then
          -- the trees over the final domain (re-built if the domain grew at the bound)
          if domSize d' == domSize d then (some (ts, sig, it + 1), ev + ev') else
          match trees S P d' budget with
          | (none, ev'') => (none, ev + ev' + ev'')
          | (some ts', ev'') => (some (ts', sig, it + 1), ev + ev' + ev'')
        else go fuel d' (it + 1) (ev + ev')
  go (K + 2) [] 0 0

/-- Statistics of a Sail-level test. -/
structure SStat where
  plats : Nat := 0
  cands : Nat := 0
  valid : Nat := 0
  nodes : Nat := 0
  events : Nat := 0
  iters : Nat := 0
  oos : List String := []
  miss : Nat := 0
  budget : Bool := false
  /-- the union differs from the all-true platform's set -/
  platDiff : Bool := false

/-- The outcomes for one final memory `M` (as `outcomesM`), registers mapped back from the relocation. -/
def outcomesS (S : STest) (ts : List STree) (obs : List Key) (M : List PMsg) : Option (List (List Nat)) × MR :=
  let rec harts : Nat → MR → Option (List (List (Nat × Nat × Nat))) × MR
    | 0, st => (some [[]], st)
    | k + 1, st =>
      let i := ts.length - (k + 1)
      let r := runT S.img M i ((ts[i]?).getD default) psInit (promsOf M i)
      let st := { st with oos := (st.oos ++ r.oos).eraseDups, miss := st.miss + r.miss, nodes := st.nodes + r.nodes }
      if r.fin.isEmpty then (none, st) else
      let proj := (r.fin.map (fun regs => (regsOf obs i).map (fun rr =>
        (i, rr, unreloc S.locs ((regs[rr]?).getD 0))))).eraseDups
      match harts k st with
      | (none, st) => (none, st)
      | (some rest, st) => (some (proj.flatMap (fun p => rest.map (p ++ ·))), st)
  match harts ts.length {} with
  | (none, st) => (none, st)
  | (some rows, st) =>
    let outs := rows.map (fun row => obs.map (fun k => match k with
      | .reg h r => ((row.find? (fun e => e.1 == h && e.2.1 == r)).map (·.2.2)).getD 0
      | .mem a sz => finalMem S.img M (a + OFF) sz))
    (some outs, st)

/-- The outcome set at one platform. -/
def outsAt (S : STest) (P : BitVec 64 → Bool) (obs : List Key) (budget mcap : Nat) (st : SStat) :
    Option (List (List Nat)) × SStat := Id.run do
  match closure S P budget with
  | (none, ev) => return (none, { st with budget := true, events := st.events + ev })
  | (some (ts, sig, it), ev) =>
    let mut st := { st with events := st.events + ev, iters := max st.iters it,
                            oos := (st.oos ++ ts.flatMap stops).eraseDups }
    let mut seen : Std.HashSet (List (Int × List Nat × Nat × Nat)) := {}
    let mut outs : Std.HashSet (List Nat) := {}
    for ch in choices sig do
      let n := ch.foldl (fun a l => a + l.length) 0
      for M in arrange (n + 1) ch do
        let key := msgsKey M
        if seen.contains key then continue
        seen := seen.insert key
        st := { st with cands := st.cands + 1 }
        if mcap < st.cands then return (none, { st with budget := true })
        let (r, mr) := outcomesS S ts obs M
        st := { st with nodes := st.nodes + mr.nodes, miss := st.miss + mr.miss,
                        oos := (st.oos ++ mr.oos).eraseDups }
        match r with
        | none => pure ()
        | some os =>
          st := { st with valid := st.valid + 1 }
          for o in os do outs := outs.insert o
    return (some outs.toList, st)

/-- THE SAIL-LEVEL OUTCOME SET: the union over the reservation platforms on the SC addresses. -/
def sailOutcomes (S : STest) (obs : List Key) (budget mcap : Nat) : Option (List (List Nat)) × SStat := Id.run do
  let allT : BitVec 64 → Bool := fun _ => true
  let (r0, st0) := outsAt S allT obs budget mcap {}
  match r0 with
  | none => return (none, st0)
  | some o0 =>
    -- the SC addresses of the all-true trees (every SC path of any platform is one of them: at an address where
    -- `P` is false Sail fails the SC before its write, which the all-true tree has as the `.Err ()` answer)
    let A := match closure S allT budget with
      | (some (ts, _, _), _) => (ts.flatMap scAddrs).eraseDups
      | _ => []
    if A.isEmpty then return (some o0, { st0 with plats := 1 })
    let subsets := (List.range (2 ^ A.length)).map (fun m =>
      (List.range A.length).filterMap (fun j => if (m >>> j) % 2 == 1 then A[j]? else none))
    let mut outs : Std.HashSet (List Nat) := o0.foldl (fun s o => s.insert o) {}
    let mut st := { st0 with plats := 1 }
    for tset in subsets do
      if tset.length == A.length then continue    -- the all-true platform, done
      let P : BitVec 64 → Bool := fun pa => tset.contains (paZ pa)
      let (r, st') := outsAt S P obs budget mcap st
      st := { st' with plats := st.plats + 1 }
      match r with
      | none => return (none, st)
      | some os => for o in os do outs := outs.insert o
    let diff := outs.size != (o0.eraseDups).length
    return (some outs.toList, { st with platDiff := diff })

end Weak.Prom.SailLit
