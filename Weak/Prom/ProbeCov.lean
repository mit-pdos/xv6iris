/-
Weak/Prom: **G3 branch logging** (S0 exit, (E3) (a); plan rev 7 §1A G3 "Coverage is measured, not assumed … the
certified explorer logs which premise branch each step took, and (E3) checks that every branch of every G3 conjunct
was taken on some run").

The explorer (`MachExplore.succ`, proved sound; `MachSail*.runT*`) is not changed: a LOGGING TWIN runs beside it.
At every step the explorer considers — every template at every reachable hart state of every run of every probe —
the twin evaluates, on every RAW candidate (the explorer's read candidates plus the uniform timestamp vectors; every
timestamp of the log for a write), each PREMISE of the `memStep` arm and each `if`/`match`/`∨` BRANCH inside the
Machine definitions the arm unfolds to, and records which values it took.  The guard IDs are Table C's
(`TableCv2.tableCv2`, which `#tableCx_check` keeps equal to the rows extracted from `memStep`): the report lists
every C-A premise row and every C-A branch row with the branch values seen, and flags any row the twin does not log
(a missing evaluator) and any evaluator whose ID is not a row.

Run (label level: `ProbeRun` families through the litmus front end; Sail level: through `MachSail`/`MachSailX`):
  `lake env lean --run Weak/Prom/ProbeCov.lean <families,comma-separated> <shard> <shards> [nosail] [nolabel]`
prints `COV <id> T F` lines (one per guard and value seen) for merging; `report` merges files.
-/
import Weak.Prom.TableCv2
import Weak.Prom.MachSailX

namespace Weak.Prom.Cov

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.SailLit Weak.Prom.SailLitX
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext)
open PLabel

/-- Coverage: per guard ID, (seen true, seen false). -/
abbrev Cov := Std.HashMap String (Bool × Bool)

def mark (c : Cov) (id : String) (b : Bool) : Cov :=
  let (t, f) := c.getD id (false, false)
  c.insert id (t || b, f || !b)

def marks (c : Cov) (l : List (String × Bool)) : Cov := l.foldl (fun c (i, b) => mark c i b) c

/-! ## 1. The guard evaluators (IDs = Table C rows) -/

def srcG (srcs : List Dsrc) : List (String × Bool) :=
  srcs.map (fun s => match s with
    | .DReg _ => ("C-A.br.dsrcView.m1.DReg", true)
    | .DLdRes => ("C-A.br.dsrcView.m1.DLdRes", true))

/-- The per-byte branches of `loadOk` / `memByte` / `fwdView` on one candidate. -/
def byteG (img : Image) (log : List PMsg) (ws : PState) (vpre : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    List (String × Bool) :=
  let nfm := nonFwdMax ws base tvs
  (List.range tvs.length).flatMap (fun k =>
    let a : Int := base + (k : Int)
    let t := ((tvs[k]?).map Prod.fst).getD 0
    let mb : List (String × Bool) :=
      if t = 0 then [("C-A.br.memByte.m1.0", true)]
      else [("C-A.br.memByte.m1.succ", true)] ++
        (match log[t - 1]? with
         | some m => [("C-A.br.byteAt.if1", decide (m.pa ≤ a))]
         | none => [])
    let fw : List (String × Bool) :=
      match get? ws.wFwd a with
      | some (tf, _) => [("C-A.br.fwdHit.m1.some(mk)", true), ("C-A.br.fwdView.m1.some(mk)", true),
                         ("C-A.br.fwdView.if2", decide (t = tf))]
      | none => [("C-A.br.fwdHit.m1.none", true), ("C-A.br.fwdView.m1.none", true)]
    let fh := fwdHit ws a t
    let fl := max (if fh then vpre else max vpre nfm) (coh ws a)
    -- `writesIn`'s window `(t, fl]` evaluates `byteAt` (its `m.pa ≤ a`) on every entry
    let win : List (String × Bool) := (List.range' (t + 1) (fl - t)).filterMap (fun t' =>
      (log[t' - 1]?).map (fun m => ("C-A.br.byteAt.if1", decide (m.pa ≤ a))))
    mb ++ fw ++ win ++ [("C-A.br.loadOk.if2", fh), ("C-A.br.nonFwdMax.if1", fh),
      ("C-A.br.loadOk.or1.1", !writesInB log a t fl),
      ("C-A.br.loadOk.or1.2", invalReadB log a t (max vpre (coh ws a)))])

/-- Raw read candidates: the explorer's, the uniform timestamp vectors, and (small reads) the brute product. -/
def rawReads (img : Image) (log : List PMsg) (ws : PState) (vpre : Nat) (base : Int) (sz : Nat) :
    List (List (Nat × BitVec 8)) :=
  let addrs := (List.range sz).map (fun k : Nat => base + (k : Int))
  let uni := (List.range (log.length + 1)).filterMap (fun t =>
    addrs.mapM (fun a => (memByte img log t a).map (fun v => (t, v))))
  let brute := if sz ≤ 2 then (prodOpts (addrs.map (bruteOpts img log))).map (·.1) else []
  (readCands img log ws vpre base sz ++ uni ++ brute).eraseDups

/-- A load-like read (`load`, `lr`, `amoLd`, the read of `rmw`): its premise `p` (= `loadOk`) and the branches. -/
def readG (img : Image) (log : List PMsg) (ws : PState) (pid : String) (aq rl : Bool) (base : Int) (sz : Nat)
    (asrc : List Dsrc) : List (String × Bool) :=
  let vpre := ldPre ws aq rl (srcsView ws asrc)
  srcG asrc ++ [("C-A.br.ldPre.if1", aq), ("C-A.br.ldPre.if2", rl), ("C-A.br.loadByte.if1", aq),
    ("C-A.br.loadByte.if2", aq), ("C-A.br.loadRun.if1", rl)] ++
  (rawReads img log ws vpre base sz).flatMap (fun tvs =>
    (pid, loadOkB img log ws vpre base tvs) :: byteG img log ws vpre base tvs)

def stBitsG (aq rl : Bool) : List (String × Bool) :=
  [("C-A.br.stClass.if1", rl), ("C-A.br.stPre.if1", rl), ("C-A.br.stPreA.if1", aq), ("C-A.br.acqPost.if1", aq),
   ("C-A.br.acqPost.if2", aq), ("C-A.br.storeRun.if1", rl)]

/-- `memStep.store` premises p1–p4 at every timestamp. -/
def storeG (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) (aq rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) : List (String × Bool) :=
  let pre := stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc)
  srcG (asrc ++ vsrc) ++ stBitsG aq rl ++
  (List.range' 1 log.length).flatMap (fun ts =>
    [("C-A.store.p1", promHas prom ts), ("C-A.store.p2", log[ts - 1]? == some ⟨base, data, some i, stClass rl⟩),
     ("C-A.store.p3", cohBelowB ws base data.length ts), ("C-A.store.p4", decide (pre < ts))])

/-- `memStep.sc` premises p1–p7. -/
def scG (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) (aq rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) : List (String × Bool) :=
  srcG (asrc ++ vsrc) ++ stBitsG aq rl ++
  match ws.wRes with
  | none => [("C-A.sc.p1", false)]
  | some R =>
    let pre := max (stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc)) R.rvView
    ("C-A.sc.p1", true) :: (List.range' 1 log.length).flatMap (fun ts =>
      [("C-A.sc.p2", promHas prom ts), ("C-A.sc.p3", log[ts - 1]? == some ⟨base, data, some i, .excl⟩),
       ("C-A.sc.p4", exclOkB log i R.rvBase R.rvTs ts), ("C-A.sc.p5", R.rvTs.all (fun t => decide (t < ts))),
       ("C-A.sc.p6", cohBelowB ws base data.length ts), ("C-A.sc.p7", decide (pre < ts))])

/-- `memStep.rmw` premises p1–p7 (label level only). -/
def rmwG (img : Image) (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) (aq rl : Bool) (base : Int)
    (sz : Nat) (f : List (BitVec 8) → List (BitVec 8)) (asrc vsrc : List Dsrc) : List (String × Bool) :=
  let va := srcsView ws asrc
  let vd := srcsView ws vsrc
  let vpre := ldPre ws aq false va
  srcG (asrc ++ vsrc) ++ [("C-A.br.amoPost.if1", aq), ("C-A.br.amoPost.if2", aq), ("C-A.br.storeRun.if1", rl)] ++
  (rawReads img log ws vpre base sz).flatMap (fun tvs =>
    let ok := loadOkB img log ws vpre base tvs
    let data := f (tvs.map Prod.snd)
    let ws1 := loadRun ws aq false va base tvs
    [("C-A.rmw.p4", ok), ("C-A.rmw.p1", tvs.length == data.length)] ++ byteG img log ws vpre base tvs ++
    (if !ok then [] else (List.range' 1 log.length).flatMap (fun ts =>
      [("C-A.rmw.p2", promHas prom ts), ("C-A.rmw.p3", log[ts - 1]? == some ⟨base, data, some i, .excl⟩),
       ("C-A.rmw.p5", exclOkB log i base (tvs.map Prod.fst) ts),
       ("C-A.rmw.p6", cohBelowB ws1 base data.length ts), ("C-A.rmw.p7", decide (stPre ws1 rl va vd < ts))])))

/-- `memStep.amoSt` premises p1–p8 (Sail level). -/
def amoStG (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) : List (String × Bool) :=
  srcG (asrc ++ vsrc) ++ [("C-A.br.storeRun.if1", rl)] ++
  match ws.wRmw with
  | none => [("C-A.amoSt.p1", false)]
  | some R =>
    let pre := stPre ws rl (srcsView ws asrc) (srcsView ws vsrc)
    [("C-A.amoSt.p1", true), ("C-A.amoSt.p2", R.rmBase == base), ("C-A.amoSt.p3", R.rmTs.length == data.length),
     ("C-A.br.amoPost.if1", R.rmAq), ("C-A.br.amoPost.if2", R.rmAq)] ++
    (List.range' 1 log.length).flatMap (fun ts =>
      [("C-A.amoSt.p4", promHas prom ts), ("C-A.amoSt.p5", log[ts - 1]? == some ⟨base, data, some i, .excl⟩),
       ("C-A.amoSt.p6", exclOkB log i base R.rmTs ts), ("C-A.amoSt.p7", cohBelowB ws base data.length ts),
       ("C-A.amoSt.p8", decide (pre < ts))])

/-- `memStep.fetch` premise p1 and the fetch-view branches (Sail level). -/
def fetchG (img : Image) (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) (base : Int) (sz : Nat) :
    List (String × Bool) :=
  let addrs := (List.range sz).map (fun k : Nat => base + (k : Int))
  let cands := (List.range (log.length + 1)).filterMap (fun t =>
    addrs.mapM (fun a => (memByte img log t a).map (fun v => (t, v))))
  cands.flatMap (fun tvs =>
    ("C-A.fetch.p1", bytesAllB (fun a t v => (memByte img log t a == some v) && !writesInB log a t ws.wIfl) base tvs) ::
    tvs.flatMap (fun (t, _) =>
      [("C-A.br.fetchView.if1", ownDone log i prom t)] ++
      (match log[t - 1]? with
       | some _ => [("C-A.br.ownDone.m1.some", true)]
       | none => [("C-A.br.ownDone.m1.none", true)])))

/-- `memStep.cmo` premises p1–p4 (Sail level). -/
def cmoG (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) (k : CmoKind) (base : Int) (len : Nat)
    (asrc : List Dsrc) : List (String × Bool) :=
  srcG asrc ++ (List.range' 1 log.length).flatMap (fun ts =>
    [("C-A.cmo.p1", promHas prom ts), ("C-A.cmo.p2", log[ts - 1]? == some ⟨base, [], some i, .cmo k len⟩),
     ("C-A.cmo.p3", cohBelowB ws base len ts), ("C-A.cmo.p4", decide (stPre ws false (srcsView ws asrc) 0 < ts))])

/-- The answer-free labels' branches. -/
def fixG (l : PLabel) : List (String × Bool) :=
  match l with
  | LFence pr pw sr sw => [("C-A.br.fencePost.if1", pr), ("C-A.br.fencePost.if2", pw), ("C-A.br.fencePost.if3", sr),
                           ("C-A.br.fencePost.if4", sw)]
  | LRegW _ srcs => srcG srcs
  | LCtrl srcs => srcG srcs
  | _ => []

/-- Every template of the label level. -/
def tmplG (img : Image) (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) : Tmpl → List (String × Bool)
  | .fix l => fixG l
  | .ld aq rl base sz asrc => readG img log ws "C-A.load.p1" aq rl base sz asrc
  | .lr aq rl base sz asrc => readG img log ws "C-A.lr.p1" aq rl base sz asrc
  | .st aq rl base data asrc vsrc => storeG log i prom ws aq rl base data asrc vsrc
  | .sc aq rl base data asrc vsrc => scG log i prom ws aq rl base data asrc vsrc
  | .rmw aq rl base sz f asrc vsrc => rmwG img log i prom ws aq rl base sz f asrc vsrc

/-! ## 2. The label-level twin (MachLitmus.stepM / runM, with the logger at every template) -/

abbrev CM := StateM Cov

def thenTC (E : Env) (h : MH) (t : Tmpl) (k : Succ → MH → CM (List MH)) : CM (List MH) := do
  modify (marks · (tmplG E.img E.log E.i h.prom h.ws t))
  let mut out := []
  for s in succ E.img E.log E.i h.prom h.ws t do
    out := out ++ (← k s { h with ws := s.ws, prom := s.prom, tr := (s.l, s.ots) :: h.tr })
  return out

def fixesC (E : Env) : MH → List PLabel → Nat → CM (List MH)
  | h, [], pc' => return [{ h with pc := pc' }]
  | h, l :: ls, pc' => thenTC E h (.fix l) (fun _ h' => fixesC E h' ls pc')

/-- `MachLitmus.stepM`, with `thenTC`/`fixesC` (`none`: out of scope). -/
def stepMC (E : Env) (n : Nat) (h : MH) : Instr → CM (Option (List MH))
  | .alui op rd rs1 imm =>
      some <$> fixesC E (h.wr rd (aluOp op (h.rd rs1) imm)) (regWL rd (srcR rs1) ++ [LInstr]) (h.pc + 1)
  | .alu op rd rs1 rs2 =>
      some <$> fixesC E (h.wr rd (aluOp op (h.rd rs1) (h.rd rs2))) (regWL rd (srcR rs1 ++ srcR rs2) ++ [LInstr])
        (h.pc + 1)
  | .load sz sgn rd rs1 off => do
      let a := (h.rd rs1 + off) % two64
      if !aligned a sz then return none
      some <$> thenTC E h (.ld false false a sz (srcR rs1)) (fun s h1 =>
        let raw := ofBytes ((readsOf s.l).map Prod.snd)
        fixesC E (h1.wr rd (if sgn then sext sz raw else raw)) (regWL rd [.DLdRes] ++ [LInstr]) (h.pc + 1))
  | .store sz rs2 rs1 off => do
      let a := (h.rd rs1 + off) % two64
      if !aligned a sz then return none
      some <$> thenTC E h (.st false false a (toBytes (h.rd rs2) sz) (srcR rs1) (srcR rs2)) (fun _ h1 =>
        fixesC E h1 [LInstr] (h.pc + 1))
  | .loadAq sz rl rd rs1 => do
      let a := h.rd rs1
      if !aligned a sz then return none
      some <$> thenTC E h (.ld true rl a sz (srcR rs1)) (fun s h1 =>
        fixesC E (h1.wr rd (sext sz (ofBytes ((readsOf s.l).map Prod.snd)))) (regWL rd [.DLdRes] ++ [LInstr])
          (h.pc + 1))
  | .storeRl sz aq rs2 rs1 => do
      let a := h.rd rs1
      if !aligned a sz then return none
      some <$> thenTC E h (.st aq true a (toBytes (h.rd rs2) sz) (srcR rs1) (srcR rs2)) (fun _ h1 =>
        fixesC E h1 [LInstr] (h.pc + 1))
  | .loadAqPc .. => return none
  | .storeRlPc .. => return none
  | .lr sz aq rl rd rs1 => do
      let a := h.rd rs1
      if !aligned a sz then return none
      some <$> thenTC E h (.lr aq (aq && rl) a sz (srcR rs1)) (fun s h1 =>
        fixesC E (h1.wr rd (sext sz (ofBytes ((readsOf s.l).map Prod.snd)))) (regWL rd [.DLdRes] ++ [LInstr])
          (h.pc + 1))
  | .sc sz aq rl rd rs2 rs1 => do
      let a := h.rd rs1
      if !aligned a sz then return none
      let ok ← thenTC E h (.sc (aq && rl) rl a (toBytes (h.rd rs2) sz) (srcR rs1) (srcR rs2)) (fun _ h1 =>
        fixesC E (h1.wr rd 0) (regWL rd [.DLdRes] ++ [LExFail, LInstr]) (h.pc + 1))
      let ko ← fixesC E (h.wr rd 1) ([LExFail] ++ regWL rd [] ++ [LExFail, LInstr]) (h.pc + 1)
      return some (ok ++ ko)
  | .amo op sz aq rl rd rs2 rs1 => do
      let a := h.rd rs1
      if !aligned a sz then return none
      let b := h.rd rs2 % 2 ^ (8 * sz)
      let f := fun (bs : List (BitVec 8)) => toBytes (amoOp op sz (ofBytes bs) b) sz
      some <$> thenTC E h (.rmw aq rl a sz f (srcR rs1) (srcR rs2)) (fun s h1 =>
        fixesC E (h1.wr rd (sext sz (ofBytes ((readsOf s.l).map Prod.snd)))) (regWL rd [.DLdRes] ++ [LInstr])
          (h.pc + 1))
  | .fence f => some <$> fixesC E h [LFence f.pr f.pw f.sr f.sw, LInstr] (h.pc + 1)
  | .fenceTso => some <$> fixesC E h [LFence true false true true, LFence false true false true, LInstr] (h.pc + 1)
  | .br c rs1 rs2 tgt =>
      if tgt ≤ h.pc ∨ n < tgt then return some [] else
      some <$> fixesC E h [LCtrl (srcR rs1 ++ srcR rs2), LInstr]
        (if brEval c (h.rd rs1) (h.rd rs2) then tgt else h.pc + 1)
  | .jmp tgt => if tgt ≤ h.pc ∨ n < tgt then return some [] else some <$> fixesC E h [LInstr] tgt
  | .csrr rd v => some <$> fixesC E (h.wr rd v) (regWL rd [] ++ [LInstr]) (h.pc + 1)
  | .fencei => some <$> fixesC E h [LFenceI, LInstr] (h.pc + 1)
  | .nop => some <$> fixesC E h [LInstr] (h.pc + 1)

partial def runMC (E : Env) (prog : List Instr) (h : MH) : CM Unit := do
  if h.pc = prog.length then return
  match prog[h.pc]? with
  | none => return
  | some ins =>
    match ← stepMC E prog.length h ins with
    | none => return
    | some hs => for h' in hs do runMC E prog h'

/-- The label-level coverage of a test: every hart against every candidate final memory (as `machOutcomes`). -/
def labelCov (T : Test) (budget mcap : Nat) : Cov × Bool := Id.run do
  match sigmaAll T budget with
  | none => return ({}, false)
  | some (sig, _) =>
    let mut seen : Std.HashSet (List (Int × List Nat × Nat × Nat)) := {}
    let mut cov : Cov := {}
    let mut cands := 0
    for ch in choices sig do
      let n := ch.foldl (fun a l => a + l.length) 0
      for M in arrange (n + 1) ch do
        let key := msgsKey M
        if seen.contains key then continue
        seen := seen.insert key
        cands := cands + 1
        if mcap < cands then return (cov, false)
        for i in List.range T.harts.length do
          let E : Env := ⟨testImg T, M, i⟩
          let ((), c') := (runMC E (T.prog i) (mhInit T M i)).run cov
          cov := c'
        -- the promise / state arms (structural in the promises-first normal form)
        if !M.isEmpty then cov := marks cov [("C-A.pm.promise.p1", true), ("C-A.pm.promise.p2", true),
          ("C-A.pm.promise.p3", true)]
        cov := marks cov [("C-A.pm.state.p1", true), ("C-A.pm.state.p2", true), ("C-A.pm.state.p3", true)]
    return (cov, true)

/-! ## 3. The Sail-level twin (`runTX` with the logger) -/

partial def toTX : STree → TX
  | .done regs => .done regs
  | .stop w => .stop w
  | .lab l t => .lab l (toTX t)
  | .rd k base sz kids => .rd (.base k) base sz (kids.map (fun (b, t) => (b, toTX t)))
  | .wr k base data ok ko => .wr k base data (toTX ok) (ko.map toTX)

def rdG (img : Image) (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) : RdK → Int → Nat → List (String × Bool)
  | .ld aq rl asrc, base, sz => readG img log ws "C-A.load.p1" aq rl base sz asrc
  | .lr aq rl asrc, base, sz => readG img log ws "C-A.lr.p1" aq rl base sz asrc
  | .amo aq asrc, base, sz => readG img log ws "C-A.amoLd.p1" aq false base sz asrc
  | .fetch, base, sz => fetchG img log i prom ws base sz

def wrG (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) : WrK → Int → List (BitVec 8) → List (String × Bool)
  | .st aq rl asrc vsrc, base, data => storeG log i prom ws aq rl base data asrc vsrc
  | .sc aq rl asrc vsrc, base, data => scG log i prom ws aq rl base data asrc vsrc
  | .amo rl asrc vsrc, base, data => amoStG log i prom ws rl base data asrc vsrc

partial def runTXC (img : Image) (log : List PMsg) (i : Nat) (t : TX) (ws : PState) (prom : GSet Nat) : CM Unit := do
  match t with
  | .done _ | .stop _ => return
  | .lab l t' =>
    modify (marks · (fixG l))
    match fixPost ws l with
    | some ws' => runTXC img log i t' ws' prom
    | none => return
  | .rd (.dev _) _ _ kids => for (_, t') in kids do runTXC img log i t' ws prom
  | .rd (.base k) base sz kids =>
    modify (marks · (rdG img log i prom ws k base sz))
    for s in rdSuccs img log i prom ws k base sz do
      let vals := ((labelReads s.l).map (fun p => p.2.map Prod.snd)).getD []
      match kids.lookup vals with
      | some t' => runTXC img log i t' s.ws s.prom
      | none => pure ()
  | .wr k base data ok ko =>
    modify (marks · (wrG log i prom ws k base data))
    for s in wrSuccs img log i prom ws k base data do runTXC img log i ok s.ws s.prom
    match ko with
    | some t' => runTXC img log i t' { ws with wRes := none } prom
    | none => pure ()
  | .cmo k base len asrc t' =>
    modify (marks · (cmoG log i prom ws k base len asrc))
    for s in succCmo log i prom ws k base len asrc do runTXC img log i t' s.ws s.prom
  | .alt kids => for t' in kids do runTXC img log i t' ws prom

/-- The Sail-level coverage over the candidate final memories of the trees `ts` (one platform). -/
def sailCov (img : Image) (ts : List TX) (sig : List (List (List PMsg))) (mcap : Nat) : Cov := Id.run do
  let mut seen : Std.HashSet (List (Int × List Nat × Nat × Nat)) := {}
  let mut cov : Cov := {}
  let mut cands := 0
  for ch in choices sig do
    let n := ch.foldl (fun a l => a + l.length) 0
    for M in arrange (n + 1) ch do
      let key := msgsKey M
      if seen.contains key then continue
      seen := seen.insert key
      cands := cands + 1
      if mcap < cands then return cov
      for i in List.range ts.length do
        let ((), c') := (runTXC img M i ((ts[i]?).getD default) psInit (promsOf M i)).run cov
        cov := c'
  return cov

/-! ## 4. Families, runs, report -/

def merge (a b : Cov) : Cov := b.fold (fun acc k (t, f) => let (t', f') := acc.getD k (false, false); acc.insert k (t || t', f || f')) a

/-- The guard rows of Table C: the C-A premise rows and the C-A branch rows. -/
def guardRows : List String :=
  Weak.Prom.TC.tableCv2.filterMap (fun (id, _, _) =>
    if id.startsWith "C-A.br." then some id
    else if id.startsWith "C-A." && ((id.splitOn ".").drop 2).any (fun seg =>
        seg.length ≥ 2 && seg.startsWith "p" && (seg.drop 1).all Char.isDigit) then some id
    else none)

/-- A row needs both values (premises, `if`, `∨` disjuncts) or just to be taken (a `match` arm). -/
def needsBoth (id : String) : Bool := !id.startsWith "C-A.pm." && !((id.splitOn ".").any (fun s => s.length ≥ 2 && s.startsWith "m" && (s.drop 1).all Char.isDigit))

def locsC : List Nat := [0x1000, 0x2000, 0x3000, 0x4000, 0x5000, 0x6000, 0x7000]

def main (args : List String) : IO UInt32 := do
  if args.head? == some "report" then
    -- merge `COV id T F` lines from the files
    let mut cov : Cov := {}
    for f in args.drop 1 do
      for ln in (← IO.FS.lines f) do
        match ln.splitOn " " with
        | ["COV", id, t, fl] => cov := merge cov (Std.HashMap.insert ({} : Cov) id (t == "1", fl == "1"))
        | _ => pure ()
    let rows := guardRows
    let mut full := 0
    let mut part := 0
    for id in rows do
      let (t, f) := cov.getD id (false, false)
      let ok := if needsBoth id then t && f else t
      if ok then full := full + 1 else part := part + 1
      IO.println s!"{if ok then "OK  " else "OPEN"} {id} T={if t then 1 else 0} F={if f then 1 else 0}{if needsBoth id then "" else " (arm)"}"
    for (id, _) in cov.toList do
      if !rows.contains id then IO.println s!"UNKNOWN-ID {id} (logged, not a Table C row)"
    IO.println s!"guard rows: {rows.length}; covered {full}; open {part}"
    return 0
  let fams := (args.getD 0 "ROW").splitOn ","
  let shard := (args.getD 1 "0").toNat!
  let shards := (args.getD 2 "1").toNat!
  let nosail := args.contains "nosail"
  let nolabel := args.contains "nolabel"
  let mut cov : Cov := {}
  let mut idx := 0
  for fam in fams do
    if fam == "G5x" then
      for p in Weak.Prom.Probe.g5xProbes do
        idx := idx + 1
        if (idx - 1) % shards != shard then continue
        let zeros := (List.range 31).map (fun k => (k + 1, 0))
        let T' := { p.T with regs0 := (List.range p.T.harts.length).map (fun h => zeros ++ ((p.T.regs0[h]?).getD [])) }
        match prepareX T' locsC bootX with
        | .error _ => pure ()
        | .ok S =>
          match closureX S (fun _ => true) 200000 with
          | (some (ts, sig, _), _) => cov := merge cov (sailCov S.img ts sig 200000)
          | _ => pure ()
      continue
    for p in Weak.Prom.Probe.family fam do
      idx := idx + 1
      if (idx - 1) % shards != shard then continue
      if !nolabel then
        let (c, _) := labelCov p.T 200000 200000
        cov := merge cov c
      if !nosail then
        let zeros := (List.range 31).map (fun k => (k + 1, 0))
        match SailLit.prepare { p.T with regs0 := (List.range p.T.harts.length).map (fun h => zeros ++ ((p.T.regs0[h]?).getD [])) }
            locsC bootX with
        | .error _ => pure ()
        | .ok S =>
          let P : BitVec 64 → Bool := fun _ => p.plat.getD true
          match closure S P 200000 with
          | (some (ts, sig, _), _) => cov := merge cov (sailCov S.img (ts.map toTX) sig 200000)
          | _ => pure ()
  for (id, (t, f)) in cov.toList do
    IO.println s!"COV {id} {if t then 1 else 0} {if f then 1 else 0}"
  return 0

end Weak.Prom.Cov

def main (args : List String) : IO UInt32 := Weak.Prom.Cov.main args
