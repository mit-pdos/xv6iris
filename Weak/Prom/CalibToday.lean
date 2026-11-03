/-
Weak/Prom: **TODAY's machine on litmus programs at label level** (S0-P parts (2)/(6), calibration E0; plan rev 7
§1A "Calibration": "the harness runs on today's machine and emission, with no seeding").

TODAY's machine is `Weak/WeakPromise.lean` `wpstep` (states `Weak.Wstate`, messages `Weak.Wmsg`, labels
`Weak.Wlabel`); TODAY's emission is `Weak/WeakEvInst.lean` `pnodeStep`.  This file is MachLitmus.lean's design
(promises-first normal form, per-hart message-list closure, arrangements, per-hart DFS, outcome product) with the
machine half replaced by today's arms and the program half by today's emission's label streams.  Nothing in
Weak/WeakPromise.lean, Weak/WeakMem.lean or Weak/WeakEvInst.lean is changed; only their definitions are used.

## The label streams (today's emission, `pnodeStep`, on the Sail events of each litmus instruction)

The announce is `annLabel` = `LInstr` (WeakEvInst: "D3-2: it is the instruction start"), the boundary `.pure` is
`LInstr` again; `nextPC := PC + 4` before the execute is `LCtrl (erwSrcs …) []` = `LCtrl []` (no register read
yet, FC-4) and is the identity (`ctrlPost ws 0`), so it is omitted.  Register writes are `erwOf (depsOfIb bits)
ibRds r`: the decoded destination gets `erwSrcs dec rds` (the `DLdRes` flag of the decoded list, then every
register READ so far: DEC-7).  For the litmus ISA the GPRs read are the instruction's operands; the CSRs Sail also
reads (`mstatus`, the PMP CSRs, `DecoderCheck.cal_SR11_dec7`) have view 0 in a litmus program (no CSR is ever
written), so they are omitted.

| instruction | today's labels |
|---|---|
| `op rd, rs1[, rs2]` | `LInstr`, `LRegW rd [rs1, rs2]`, `LInstr` |
| `l* rd, off(rs1)` | `LInstr`, `LLoad false false a tvs []` (D-8: no address source), `LRegW rd [DLdRes, rs1]`, `LInstr` |
| `s* rs2, off(rs1)` | `LInstr`, `LStore false a data [rs1] [rs2]`, `LInstr` |
| `lr rd, (rs1)` | `LInstr`, `LExLoad aq a tvs []`, `LRegW rd [DLdRes, rs1]`, `LInstr` |
| `sc rd, rs2, (rs1)`, `P a` | `LInstr`, `LExStore rl a data [rs1] [rs2]` (the write's `akSync`: `rl`), `LRegW rd [DLdRes, rs2, rs1]` (rd := 0), `LInstr` |
| `sc …`, `¬ P a` | `LInstr`, `LRegW rd [DLdRes, rs2, rs1]` (rd := 1: Sail fails before any memory event), `LInstr` |
| `amo rd, rs2, (rs1)` | `LInstr`, `LExLoad aq a tvs [rs1]`, `LExStore rl a data [rs1] [rs2]`, `LRegW rd [DLdRes, rs2, rs1]`, `LInstr` |
| `fence p,s` | `LInstr`, `LFence pr pw sr sw`, `LInstr` |
| `fence.tso` | `LInstr`, `LFence r,r` (`ebarNow`), `LFence rw,w` (`ebarPark`), `LInstr` |
| `fence.i` | `LInstr`, `LFence false false false false`, `LInstr` |
| `b<c> rs1, rs2` | `LInstr`, then `LCtrl [rs1, rs2]` ONLY IF TAKEN (FC-4), `LInstr` |
| `j`, `nop` | `LInstr`, `LInstr` |
| `csrr rd` (untracked CSR: `ORnone`) | `LInstr`, `LSilent` for the `rd` write (SR-19: stale view), `LInstr` |

The SC write's other answer, the memory-blind retry (`LSilent`, same node), never completes and is dropped.  The
reservation predicate `P` (`xv6_resv_matches`) is one value per address per run, shared by every hart (as
MachSail.lean); the outcome set is the union over the SC addresses' `2^|A|` platforms.  Zalasr `l*.aq`/`s*.rl` have
no Sail form (no access kind) and are out of scope here (`oos`).

## Completeness of the explorer (argument, not proved; milestone 1's for v2)

Promises-first is exact for today's machine: every arm except `WPPromise` reads the log only below views or
reservation timestamps (`readable`'s window `(t, vpre ⊔ coh]`, `fulfilOkD`'s EXT, `exclOkTs`'s `(t, ts - 1]`,
`adShapedb` at the reservation's timestamps; `lat` is `false` on every Sail label), and reads the promise set
only through the fulfil membership.  The candidate final memories come from free runs over a value domain
(`Mach.sigmaAll`), iterated to a fixpoint: a message's data views include its data sources' views, a load's result
view includes its timestamp (or the `vpre` of a forwarded own store) and, through F5', its address registers' views,
so every message's value is computed from answers below its timestamp.  The explorer is a CALIBRATION tool: a wrong
"unreachable" would only add a false rediscovery, so every rediscovered row is also explained by hand (the premise
that blocks it) in PROGRESS-S0rest.md.
-/
import Weak.Prom.MachLitmus
import Weak.WeakPromise

namespace Weak.Prom.Today

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc Wstate Wmsg WmClass Wresv wsInit logByte readableb loadPostRunD storePostRunD
  exloadPostRunD fencePost regwPost ctrlPost instrPost loadVpreD fulfilVpreD exclOkTsb adShapedb)
open Weak.Prom
open Weak.Prom.Mach (Key Dom sigmaAll arrange choices msgsKey finalMem regsOf testImg toBytes ofBytes srcR aligned)
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext)

/-! ## 1. Messages -/

def clsOf : PClass → WmClass
  | .plain => .WCplain
  | .rel => .WCrel
  | _ => .WCexcl

def wmsgOf (m : PMsg) : Wmsg := ⟨m.pa, m.data, m.tid, clsOf m.cls⟩

/-! ## 2. Today's arms as successor functions -/

/-- Every per-byte read run admissible under `readOkD` at pre-view `vpre` (brute force over timestamps). -/
def readRuns (img : Image) (log : List Wmsg) (ws : Wstate) (vpre : Nat) (base : Int) (sz : Nat) :
    List (List (Nat × BitVec 8)) :=
  let opts := (List.range sz).map (fun k : Nat =>
    let a := base + (k : Int)
    (List.range (log.length + 1)).filterMap (fun t =>
      match logByte img log t a with
      | some v => if readableb img log ws vpre a t then some (t, v) else none
      | none => none))
  let rec prod : List (List (Nat × BitVec 8)) → List (List (Nat × BitVec 8))
    | [] => [[]]
    | os :: rest => (prod rest).flatMap (fun tl => os.map (· :: tl))
  prod opts

/-- `fulfilOkD` as a Bool. -/
def fulfilOkB (ws : Wstate) (rl : Bool) (base : Int) (n ts vd : Nat) : Bool :=
  (List.range n).all (fun j => decide (Weak.coh ws (base + (j : Int)) < ts)) && decide (fulfilVpreD ws rl vd < ts)

/-- The fulfil timestamps of an own promise holding exactly `⟨base, data, some i, _⟩` (any class: `WPFulfil` and
`WPExStore` take the class `k` from the log). -/
def ownTs (log : List Wmsg) (i : Nat) (prom : GSet Nat) (base : Int) (data : List (BitVec 8)) : List Nat :=
  (List.range' 1 log.length).filter (fun ts =>
    prom.contains ts &&
    (match log[ts - 1]? with
     | some m => m.wmPa == base && m.wmData == data && m.wmTid == some i
     | none => false))

/-- `WPLoad` (lat = false). -/
def succLoad (img : Image) (log : List Wmsg) (ws : Wstate) (aq : Bool) (base : Int) (sz : Nat) (asrc : List Dsrc) :
    List (List (Nat × BitVec 8) × Wstate) :=
  let va := Weak.srcsView ws asrc
  (readRuns img log ws (loadVpreD ws aq va) base sz).map (fun tvs =>
    (tvs, loadPostRunD ws aq va base (tvs.map Prod.fst)))

/-- `WPExLoad` (`readOk`: the exclusive read at the PLAIN pre-view, D-2r). -/
def succExLoad (img : Image) (log : List Wmsg) (ws : Wstate) (aq : Bool) (base : Int) (sz : Nat)
    (asrc : List Dsrc) : List (List (Nat × BitVec 8) × Wstate) :=
  (readRuns img log ws (loadVpreD ws aq 0) base sz).map (fun tvs =>
    (tvs, exloadPostRunD ws aq (Weak.srcsView ws asrc) base (tvs.map Prod.fst)))

/-- `WPFulfil`. -/
def succStore (log : List Wmsg) (i : Nat) (prom : GSet Nat) (ws : Wstate) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) : List (Nat × Wstate × GSet Nat) :=
  let va := Weak.srcsView ws asrc
  let vd := Weak.srcsView ws vsrc
  ((ownTs log i prom base data).filter (fun ts => fulfilOkB ws rl base data.length ts (max va vd))).map (fun ts =>
    (ts, storePostRunD ws rl va vd base data.length ts, prom \ {ts}))

/-- `WPExStore` (the reservation, `exclOkTs`, and the walker gate `adShapedb` in the pre-view). -/
def succExStore (img : Image) (log : List Wmsg) (i : Nat) (prom : GSet Nat) (ws : Wstate) (rl : Bool)
    (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) : List (Nat × Wstate × GSet Nat) :=
  match ws.wRes with
  | none => []
  | some R =>
    if R.rvBase != base || R.rvTs.length != data.length then [] else
    let va := Weak.srcsView ws asrc
    let vd := Weak.srcsView ws vsrc
    let gate := if adShapedb img log base R.rvTs data then max ws.wVrOld ws.wVwOld else 0
    ((ownTs log i prom base data).filter (fun ts =>
        exclOkTsb log i base R.rvTs ts &&
        fulfilOkB ws rl base data.length ts (max (max va vd) (max R.rvView gate)))).map (fun ts =>
      (ts, storePostRunD ws rl va vd base data.length ts, prom \ {ts}))

/-! ## 3. A hart under today's machine -/

structure TH where
  pc : Nat
  regs : List Nat
  ws : Wstate
  prom : GSet Nat

def TH.rd (h : TH) (r : Nat) : Nat := if r = 0 then 0 else (h.regs[r]?).getD 0
def TH.wr (h : TH) (r v : Nat) : TH := if r = 0 then h else { h with regs := h.regs.set r (v % two64) }

structure Env where
  img : Image
  log : List Wmsg
  i : Nat
  P : Int → Bool

/-- `LRegW rd srcs` (`WPRegW`, x0 never written). -/
def regW (h : TH) (rd : Nat) (srcs : List Dsrc) : TH :=
  if rd = 0 then h else { h with ws := regwPost h.ws rd (Weak.srcsView h.ws srcs) }

def instr (h : TH) : TH := { h with ws := instrPost h.ws }
def ctrl (h : TH) (srcs : List Dsrc) : TH := { h with ws := ctrlPost h.ws (Weak.srcsView h.ws srcs) }
def fence (h : TH) (pr pw sr sw : Bool) : TH := { h with ws := Weak.fencePost h.ws pr pw sr sw }

inductive StepR where
  | next (hs : List TH)
  | oos (why : String)

def done (h : TH) (pc : Nat) : TH := { instr h with pc := pc }

/-- ONE INSTRUCTION under today's machine and emission (all successors), after the announce `LInstr`. -/
def stepT (E : Env) (n : Nat) (h0 : TH) : Instr → StepR
  | ins =>
  let h := instr h0
  match ins with
  | .alui op rd rs1 imm => .next [done (regW (h.wr rd (aluOp op (h.rd rs1) imm)) rd (srcR rs1)) (h.pc + 1)]
  | .alu op rd rs1 rs2 =>
      .next [done (regW (h.wr rd (aluOp op (h.rd rs1) (h.rd rs2))) rd (srcR rs1 ++ srcR rs2)) (h.pc + 1)]
  | .load sz sgn rd rs1 off =>
      let a := (h.rd rs1 + off) % two64
      if !aligned a sz then .oos "misaligned" else
      .next ((succLoad E.img E.log h.ws false a sz []).map (fun (tvs, ws') =>
        let raw := ofBytes (tvs.map Prod.snd)
        let h1 := { h with ws := ws' }
        done (regW (h1.wr rd (if sgn then sext sz raw else raw)) rd (.DLdRes :: srcR rs1)) (h.pc + 1)))
  | .store sz rs2 rs1 off =>
      let a := (h.rd rs1 + off) % two64
      if !aligned a sz then .oos "misaligned" else
      .next ((succStore E.log E.i h.prom h.ws false a (toBytes (h.rd rs2) sz) (srcR rs1) (srcR rs2)).map
        (fun (_, ws', pr') => done { h with ws := ws', prom := pr' } (h.pc + 1)))
  | .lr sz aq _ rd rs1 =>
      let a := h.rd rs1
      if !aligned a sz then .oos "misaligned" else
      .next ((succExLoad E.img E.log h.ws aq a sz []).map (fun (tvs, ws') =>
        let h1 := { h with ws := ws' }
        done (regW (h1.wr rd (sext sz (ofBytes (tvs.map Prod.snd)))) rd (.DLdRes :: srcR rs1)) (h.pc + 1)))
  | .sc sz _ rl rd rs2 rs1 =>
      let a := h.rd rs1
      if !aligned a sz then .oos "misaligned" else
      let srcs := .DLdRes :: (srcR rs2 ++ srcR rs1)
      if E.P (a : Int) then
        .next ((succExStore E.img E.log E.i h.prom h.ws rl a (toBytes (h.rd rs2) sz) (srcR rs1) (srcR rs2)).map
          (fun (_, ws', pr') => done (regW ({ h with ws := ws', prom := pr' }.wr rd 0) rd srcs) (h.pc + 1)))
      else .next [done (regW (h.wr rd 1) rd srcs) (h.pc + 1)]
  | .amo op sz aq rl rd rs2 rs1 =>
      let a := h.rd rs1
      if !aligned a sz then .oos "misaligned" else
      let b := h.rd rs2 % 2 ^ (8 * sz)
      .next ((succExLoad E.img E.log h.ws aq a sz (srcR rs1)).flatMap (fun (tvs, ws1) =>
        let data := toBytes (amoOp op sz (ofBytes (tvs.map Prod.snd)) b) sz
        (succExStore E.img E.log E.i h.prom ws1 rl a data (srcR rs1) (srcR rs2)).map (fun (_, ws2, pr') =>
          let h2 := { h with ws := ws2, prom := pr' }
          done (regW (h2.wr rd (sext sz (ofBytes (tvs.map Prod.snd)))) rd (.DLdRes :: (srcR rs2 ++ srcR rs1)))
            (h.pc + 1))))
  | .fence f => .next [done (fence h f.pr f.pw f.sr f.sw) (h.pc + 1)]
  | .fenceTso => .next [done (fence (fence h true false true false) true true false true) (h.pc + 1)]
  | .fencei => .next [done h (h.pc + 1)]
  | .br c rs1 rs2 tgt =>
      if tgt ≤ h.pc ∨ n < tgt then .next [] else
      if brEval c (h.rd rs1) (h.rd rs2) then .next [done (ctrl h (srcR rs1 ++ srcR rs2)) tgt]
      else .next [done h (h.pc + 1)]
  | .jmp tgt => if tgt ≤ h.pc ∨ n < tgt then .next [] else .next [done h tgt]
  | .csrr rd v => .next [done (h.wr rd v) (h.pc + 1)]   -- `LSilent`: the view of `rd` is STALE (SR-19)
  | .nop => .next [done h (h.pc + 1)]
  | .loadAq .. | .storeRl .. => .oos "Zalasr (no Sail access kind)"
  | .loadAqPc .. | .storeRlPc .. => .oos "RCpc"

structure Res where
  fin : List TH
  oos : List String
  nodes : Nat

def runT (E : Env) (prog : List Instr) : Nat → TH → Res
  | 0, _ => ⟨[], ["fuel"], 1⟩
  | fuel + 1, h =>
    if h.pc = prog.length then ⟨[h], [], 1⟩ else
    match prog[h.pc]? with
    | none => ⟨[], [], 1⟩
    | some ins =>
      match stepT E prog.length h ins with
      | .oos why => ⟨[], [why], 1⟩
      | .next hs => hs.foldl (fun acc h' =>
          let r := runT E prog fuel h'
          ⟨acc.fin ++ r.fin, acc.oos ++ r.oos, acc.nodes + r.nodes⟩) ⟨[], [], 1⟩

/-- The promise set of agent `i` in promises-first normal form. -/
def promsOf (log : List Wmsg) (i : Nat) : GSet Nat :=
  (List.range log.length).foldl (fun acc k =>
    match log[k]? with
    | some m => if m.wmTid == some i then {k + 1} ∪ acc else acc
    | none => acc) ∅

def promDone (log : List Wmsg) (prom : GSet Nat) : Bool :=
  (List.range' 1 log.length).all (fun t => !prom.contains t)

def hartRuns (T : Test) (P : Int → Bool) (M : List PMsg) (i : Nat) : Res :=
  let log := M.map wmsgOf
  let E : Env := ⟨testImg T, log, i, P⟩
  let h0 : TH := { pc := 0, regs := (List.range 32).map (fun r => ((((T.regs0[i]?).getD []).lookup r).getD 0) % two64),
                   ws := wsInit, prom := promsOf log i }
  let r := runT E (T.prog i) ((T.prog i).length + 1) h0
  { r with fin := r.fin.filter (fun h => promDone log h.prom) }

/-- The outcomes for one final memory. -/
def outcomesT (T : Test) (P : Int → Bool) (obs : List Key) (M : List PMsg) (st : Nat × List String) :
    Option (List (List Nat)) × Nat × List String :=
  let img := testImg T
  let rec harts : Nat → Nat × List String → Option (List (List (Nat × Nat × Nat))) × Nat × List String
    | 0, st => (some [[]], st)
    | k + 1, st =>
      let i := T.harts.length - (k + 1)
      let r := hartRuns T P M i
      let st := (st.1 + r.nodes, st.2 ++ r.oos)
      if r.fin.isEmpty then (none, st) else
      let proj := (r.fin.map (fun h => (regsOf obs i).map (fun rr => (i, rr, h.rd rr)))).eraseDups
      match harts k st with
      | (none, st) => (none, st)
      | (some rest, st) => (some (proj.flatMap (fun p => rest.map (p ++ ·))), st)
  match harts T.harts.length st with
  | (none, st) => (none, st)
  | (some rows, st) =>
    (some (rows.map (fun row => obs.map (fun k => match k with
      | .reg h r => ((row.find? (fun e => e.1 == h && e.2.1 == r)).map (·.2.2)).getD 0
      | .mem a sz => finalMem img M a sz))), st)

/-- The SC addresses of a test's free runs (the platforms range over them). -/
def scAddrsOf (sig : List (List (List PMsg))) : List Int :=
  ((sig.flatMap (fun s => s.flatten)).filter (fun m => m.cls == .excl)).map (·.pa) |>.eraseDups

structure TStat where
  cands : Nat := 0
  valid : Nat := 0
  plats : Nat := 0
  oos : List String := []
  budget : Bool := false

/-- TODAY's OUTCOME SET (union over the reservation platforms). -/
def todayOutcomes (T : Test) (obs : List Key) (budget mcap : Nat) (plat : Option Bool := none) :
    List (List Nat) × TStat := Id.run do
  match sigmaAll T budget with
  | none => return ([], { budget := true })
  | some (sig, _) =>
    -- every address an SC of the test can target (as the message addresses of SC/AMO writes; an SC that never
    -- writes in any free run only needs `P = false`, which every platform with that address absent gives)
    let A := scAddrsOf sig
    let plats := match plat with
      | some true => [A]
      | some false => [[]]
      | none => (List.range (2 ^ A.length)).map (fun m =>
          (List.range A.length).filterMap (fun j => if (m >>> j) % 2 == 1 then A[j]? else none))
    let mut outs : List (List Nat) := []
    let mut st : TStat := {}
    for tset in plats do
      let P : Int → Bool := fun a => tset.contains a
      st := { st with plats := st.plats + 1 }
      let mut seen : List (List (Int × List Nat × Nat × Nat)) := []
      for ch in choices sig do
        let n := ch.foldl (fun a l => a + l.length) 0
        for M in arrange (n + 1) ch do
          let key := msgsKey M
          if seen.contains key then continue
          seen := seen ++ [key]
          st := { st with cands := st.cands + 1 }
          if mcap < st.cands then return ([], { st with budget := true })
          let (r, (_, oo)) := outcomesT T P obs M (0, [])
          st := { st with oos := (st.oos ++ oo).eraseDups }
          match r with
          | none => pure ()
          | some os =>
            st := { st with valid := st.valid + 1 }
            for o in os do if !outs.contains o then outs := outs ++ [o]
    return (outs, st)

end Weak.Prom.Today
