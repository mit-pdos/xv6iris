/-
Weak/Prom: **machine v2 through Sail on the EXTENDED programs** (S0 exit, (E3) (b)): the Sail-level runner of
`MachSail.lean`, with the emission arms that `MachSail.sNext` stops at transcribed from `Weak/Prom/Emit.lean`:

* a DECOMPOSABLE plain RAM read or write (`splittable`: a Sail piece of a misaligned access narrower than the
  instruction, or the `cbo.zero` block write) is answered in contiguous chunks, each its own `LLoad`/`LStore`
  (`ramRead`/`ramWrite`'s `racc`/`woff`); the chunk sizes are a nondeterministic choice (`altE`).  For a 64-byte
  `cbo.zero` write only the compositions `RefX.cboZeroComps` are explored (the same family as the reference side:
  an under-approximation of both, see `RefX`);
* an MMIO access to an I/O address with no device (`devDecode = none`): any answer (from `RefX.ioDom`), any write
  accepted, label `LDev` ([OWN.P1], Emit.lean `hnodeStep`); an address WITH a device stops the run (no device state
  here);
* the end of a failed `amocas`: the optional write-back of the old value (`bndStep`'s second disjunct: `LAmoSt false
  b old asrc []`, atomic with the read through the `wRmw` slot), or not;
* the end of a Zicbom instruction: the mandatory `LCmo k (cboBase rs w) cboLen (rs1)` (`bndStep`'s third disjunct),
  fulfilled by the machine's `cmo` arm (`succCmo`: the `memStep.cmo` premises).

Everything else is `MachSail.sNext`'s arm, verbatim.  The assembler adds `cbo.zero`/`cbo.inval`/`cbo.clean`/
`cbo.flush` (MISC-MEM, funct3 010, imm 4/0/1/2) and `amocas.w/d` (AMO, funct5 00101).
-/
import Weak.Prom.MachSail
import Weak.Prom.RefX

namespace Weak.Prom.SailLitX

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Weak (Image Dsrc depsCtrl depsAddr depsVsrc eregNum ebarPark ibOfBvn paZ)
open Weak.Prom
open Weak.Prom.Mach
open Weak.Prom.SailLit
open Weak.Prom.RefX (XI XTest)
open Weak.Prom.Ref (Instr Test two64)
open PLabel

/-! ## 1. The assembler -/

def asmX (locs : List Nat) (addrOf : Nat → Nat) (pc : Nat) : XI → Except String (List Nat)
  | .i ins => asmInstr locs addrOf pc ins
  | .ldM sz sgn rd rs1 off => asmInstr locs addrOf pc (.load sz sgn rd rs1 off)
  | .stM sz rs2 rs1 off => asmInstr locs addrOf pc (.store sz rs2 rs1 off)
  | .cboZero rs1 => .ok [iType 4 rs1 2 0 0x0F]
  | .cbo k rs1 => .ok [iType (match k with | .inval => 0 | .clean => 1 | .flush => 2) rs1 2 0 0x0F]
  | .amocas sz aq rl rd rs2 rs1 => do
    let f3 ← szF3 sz
    pure [rType ((5 <<< 2) ||| (b2n aq <<< 1) ||| b2n rl) rs2 rs1 f3 rd 0x2F]

def nWordsX (locs : List Nat) (i : XI) : Nat :=
  match asmX locs (fun _ => 0) 0 i with
  | .ok ws => ws.length
  | .error _ => 1

def asmProgX (locs : List Nat) (h : Nat) (prog : List XI) : Except String (List Nat × Nat) := do
  let sizes := prog.map (nWordsX locs)
  let starts := (sizes.foldl (fun (acc : List Nat × Nat) s => (acc.1 ++ [acc.2], acc.2 + 4 * s)) ([], codeBase h))
  let addrOf := fun (k : Nat) => (starts.1[k]?).getD starts.2
  let words ← (List.range prog.length).foldlM (fun (acc : List Nat) k => do
    let i := (prog[k]?).getD (.i .nop)
    let ws ← asmX locs addrOf (addrOf k) i
    pure (acc ++ ws)) []
  pure (words, starts.2)

/-! ## 2. The emission, executably, with the extended arms -/

inductive RdKX where
  | base (k : RdK)
  /-- an MMIO read with no device: any answer, label `LDev .rd` -/
  | dev (asrc : List Dsrc)

inductive EvX where
  | lab (l : PLabel) (h : SH)
  | rd (k : RdKX) (base : Int) (sz : Nat) (cont : List (BitVec 8) → SH)
  | wr (k : WrK) (base : Int) (data : List (BitVec 8)) (ok : SH) (ko : Option SH)
  | cmo (k : CmoKind) (base : Int) (len : Nat) (asrc : List Dsrc) (h : SH)
  | alt (es : List EvX)
  | done
  | stop (why : String)

instance : Inhabited EvX := ⟨.done⟩

/-- The chunk sizes allowed next, `off` bytes of `n` answered (all, or the `cbo.zero` family). -/
def chunkSizes (n off : Nat) : List Nat :=
  if n = RefX.blk then
    (RefX.cboZeroComps.filterMap (fun pcs =>
      let os := RefX.offsets pcs
      match (pcs.zip os).find? (fun (_, o) => o == off) with
      | some (p, _) => some p
      | none => none)).eraseDups
  else (List.range (n - off)).map (· + 1)

/-- ONE EVENT (`MachSail.sNext`, plus the arms above). -/
partial def sNextX (P : BitVec 64 → Bool) (endPC : BitVec 64) (h : SH) : EvX :=
  match h.fn with
  | some (pr, pw, sr, sw) => .lab (LFence pr pw sr sw) { h with fn := none }
  | none =>
  match h.m with
  | .pure _ =>
    if isSC h.ix.bits && !h.ix.trapped && !h.ix.scEnd then
      .lab LExFail { h with ix := { h.ix with scEnd := true } }
    else if h.ix.trapped then .stop "trap"
    else
    -- [OWN.P1] the optional write-back of a failed amocas (zacas.adoc:159–161)
    match h.ix.amoRd with
    | some (b, old) =>
      if isAmocas h.ix.bits && !h.ix.amoWr && !h.ix.wbDone then
        let h1 : SH := { h with ix := { h.ix with wbDone := true } }
        .alt [.wr (.amo false (depsAddr (v2Roles h.ix.bits)) []) b old h1 none, sNextX P endPC h1]
      else bndRest P endPC h
    | none => bndRest P endPC h
  | .impure (.error _) _ => .stop "sail-error"
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k =>
      match csrCapture h.ix r with
      | some n => .lab (LRegW csrOldKey [.DReg n]) { h with m := k (h.rs.get r), ix := { h.ix with csrOld := true } }
      | none => .lab LSilent { h with m := k (h.rs.get r) }
    | .regWrite r v, k =>
      if isReg r .mcause || isReg r .scause then .stop "trap" else
      let h' : SH := { h with m := k PUnit.unit, rs := h.rs.insert r v }
      if isReg r .nextPC then .lab (LCtrl (depsCtrl (v2Roles h.ix.bits))) h'
      else match eregNum r with
        | some num => .lab (LRegW num (regSrcs h.ix.bits h.ix.scOk num)) h'
        | none => .lab LSilent h'
    | .memRead n _ req, k =>
      let asrc := depsAddr (v2Roles h.ix.bits)
      let pa := paZ req.pa
      if devAddr req.pa then
        if (devDecode req.pa).isSome then .stop "device" else
        .rd (.dev asrc) pa n (fun bs => { h with m := k (.Ok (bvOfBytes n bs, none)) })
      else
      let ak := req.access_kind
      if isTtw ak then .stop "ttw" else
      if akIfetch ak then
        .rd (.base .fetch) pa n (fun bs => { h with m := k (.Ok (bvOfBytes n bs, none)) })
      else if akExcl ak then
        if isLR h.ix.bits then
          .rd (.base (.lr (akAcq ak) (akStrong ak) asrc)) pa n (fun bs => { h with m := k (.Ok (bvOfBytes n bs, none)) })
        else
          .rd (.base (.amo (akAcq ak) asrc)) pa n (fun bs =>
            { h with m := k (.Ok (bvOfBytes n bs, none)), ix := { h.ix with amoRd := some (pa, bs) } })
      else if splittable h.ix.bits n then
        let off := h.ix.racc.length
        .alt ((chunkSizes n off).map (fun c =>
          .rd (.base (.ld (akAcq ak) (akStrong ak) asrc)) (pa + off) c (fun bs =>
            let acc := h.ix.racc ++ bs.map (fun b => (0, b))
            if acc.length = n then
              { h with m := k (.Ok (bvOfBytes n (acc.map Prod.snd), none)), ix := { h.ix with racc := [] } }
            else { h with ix := { h.ix with racc := acc } })))
      else .rd (.base (.ld (akAcq ak) (akStrong ak) asrc)) pa n (fun bs => { h with m := k (.Ok (bvOfBytes n bs, none)) })
    | .memWrite n _ req, k =>
      match req.value with
      | none => .stop "write-no-value"
      | some v =>
        let ak := req.access_kind
        let bs := Weak.WeakInterpProj.wbytes n v
        let asrc := depsAddr (v2Roles h.ix.bits)
        let vsrc := depsVsrc (v2Roles h.ix.bits)
        let pa := paZ req.pa
        if devAddr req.pa then
          if (devDecode req.pa).isSome then .stop "device" else
          .lab (LDev .wr pa bs asrc vsrc) { h with m := k (.Ok (some true)) }
        else
        if n = 0 then .stop "empty-write" else
        if akExcl ak then
          if isSC h.ix.bits then
            .wr (.sc (akStrong ak) (akRel ak) asrc vsrc) pa bs
              { h with m := k (.Ok (some true)), ix := { h.ix with scOk := true } }
              (some { h with m := k (.Err ()) })
          else
            .wr (.amo (akAcq ak) asrc vsrc) pa bs
              { h with m := k (.Ok (some true)), ix := { h.ix with amoWr := true } } none
        else if splittable h.ix.bits n then
          let off := h.ix.woff
          .alt ((chunkSizes n off).map (fun c =>
            let h' : SH := if off + c = n then { h with m := k (.Ok (some true)), ix := { h.ix with woff := 0 } }
              else { h with ix := { h.ix with woff := off + c } }
            .wr (.st (akStrong ak) (akRel ak) asrc vsrc) (pa + off) ((bs.drop off).take c) h' none))
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
where
  /-- the rest of the boundary: the mandatory Zicbom operation, then `LInstr` / done. -/
  bndRest (P : BitVec 64 → Bool) (endPC : BitVec 64) (h : SH) : EvX :=
    match cboKind h.ix.bits, h.ix.bits with
    | some k, some w =>
      if !h.ix.cmoDone then
        .cmo k (cboBase (Vtest.XRegs.file h.rs) w) cboLen (dsrcOfRs1 w) { h with ix := { h.ix with cmoDone := true } }
      else if h.rs.get .PC == endPC then .done
      else .lab LInstr { h with m := riscvStepP P false, ix := ixNone }
    | _, _ =>
      if h.rs.get .PC == endPC then .done
      else .lab LInstr { h with m := riscvStepP P false, ix := ixNone }

partial def sNextXNS (P : BitVec 64 → Bool) (endPC : BitVec 64) (h : SH) (n : Nat) : EvX × Nat :=
  match sNextX P endPC h with
  | .lab LSilent h' => sNextXNS P endPC h' (n + 1)
  | e => (e, n)

/-! ## 3. The program tree -/

inductive TX where
  | done (regs : Array Nat)
  | stop (why : String)
  | lab (l : PLabel) (t : TX)
  | rd (k : RdKX) (base : Int) (sz : Nat) (kids : List (List (BitVec 8) × TX))
  | wr (k : WrK) (base : Int) (data : List (BitVec 8)) (ok : TX) (ko : Option TX)
  | cmo (k : CmoKind) (base : Int) (len : Nat) (asrc : List Dsrc) (t : TX)
  | alt (kids : List TX)

instance : Inhabited TX := ⟨.stop "default"⟩

/-- The answers of an MMIO read: the bytes of each `RefX.ioDom` value. -/
def devAns (sz : Nat) : List (List (BitVec 8)) := RefX.ioDom.map (fun v => toBytes v sz)

mutual
partial def buildX (c : BCfg) (h : SH) (ninstr : Nat) : StateM BSt TX := do
  let (e, n) := sNextXNS c.P c.endPC h 0
  modify fun s => { s with nodes := s.nodes + 1, events := s.events + n + 1 }
  if (← get).nodes > c.budget then
    modify fun s => { s with over := true }
    return .stop "budget"
  buildEv c h e ninstr

partial def buildEv (c : BCfg) (h : SH) (e : EvX) (ninstr : Nat) : StateM BSt TX := do
  match e with
  | .lab LInstr h' =>
    if ninstr ≥ c.maxInstr then return .stop "fuel"
    return .lab LInstr (← buildX c h' (ninstr + 1))
  | .lab l h' => return .lab l (← buildX c h' ninstr)
  | .rd k base sz cont =>
    let answers := match k with
      | .dev _ => devAns sz
      | .base _ => c.ans base sz
    let kids ← answers.mapM (fun bs => do return (bs, ← buildX c (cont bs) ninstr))
    return .rd k base sz kids
  | .wr k base data ok ko =>
    let t1 ← buildX c ok ninstr
    match ko with
    | some h2 => return .wr k base data t1 (some (← buildX c h2 ninstr))
    | none => return .wr k base data t1 none
  | .cmo k base len asrc h' => return .cmo k base len asrc (← buildX c h' ninstr)
  | .alt es => return .alt (← es.mapM (fun e' => buildEv c h e' ninstr))
  | .done => return .done (gprsOf h.rs)
  | .stop why => return .stop why
end

partial def msgListsX (i : Nat) : TX → List (List PMsg)
  | .done _ => [[]]
  | .stop why => if why == "sail-error" then [[]] else []   -- MachFix-havoc
  | .lab _ t => msgListsX i t
  | .rd _ _ _ kids => (kids.flatMap (fun p => msgListsX i p.2)).eraseDups
  | .wr k base data ok ko =>
    ((msgListsX i ok).map (⟨base, data, some i, wrCls k⟩ :: ·) ++
      (match ko with | some t => msgListsX i t | none => [])).eraseDups
  | .cmo k base len _ t => (msgListsX i t).map (⟨base, [], some i, .cmo k len⟩ :: ·)
  | .alt kids => (kids.flatMap (msgListsX i)).eraseDups

partial def scAddrsX : TX → List Int
  | .done _ | .stop _ => []
  | .lab _ t => scAddrsX t
  | .rd _ _ _ kids => (kids.flatMap (fun p => scAddrsX p.2)).eraseDups
  | .wr k base _ ok ko =>
    ((match k with | .sc .. => [base] | _ => []) ++ scAddrsX ok ++
      (match ko with | some t => scAddrsX t | none => [])).eraseDups
  | .cmo _ _ _ _ t => scAddrsX t
  | .alt kids => (kids.flatMap scAddrsX).eraseDups

partial def stopsX : TX → List String
  | .done _ => []
  | .stop w => [w]
  | .lab _ t => stopsX t
  | .rd _ _ _ kids => (kids.flatMap (fun p => stopsX p.2)).eraseDups
  | .wr _ _ _ ok ko => (stopsX ok ++ (match ko with | some t => stopsX t | none => [])).eraseDups
  | .cmo _ _ _ _ t => stopsX t
  | .alt kids => (kids.flatMap stopsX).eraseDups

/-- `memStep.cmo`: fulfil an own cache-block-operation message (COH on the block, EXT at the plain store pre-view). -/
def succCmo (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) (k : CmoKind) (base : Int) (len : Nat)
    (asrc : List Dsrc) : List Succ :=
  let va := srcsView ws asrc
  (List.range (log.length + 1)).filterMap (fun ts =>
    if promHas prom ts && log[ts - 1]? == some ⟨base, [], some i, .cmo k len⟩ && cohBelowB ws base len ts &&
        decide (stPre ws false va 0 < ts) then
      some ⟨LCmo k base len asrc, some ts, cmoPost ws va base len ts, prom \ {ts}⟩
    else none)

/-- Walk the tree against `M`. -/
partial def runTX (img : Image) (log : List PMsg) (i : Nat) (t : TX) (ws : PState) (prom : GSet Nat) : MR :=
  match t with
  | .done regs => if promDone log prom then { fin := [regs], nodes := 1 } else { nodes := 1 }
  -- MachFix-havoc, HavocProm [OWN.P10] (as MachSail.lean `runT`)
  | .stop why => { oos := [why], nodes := 1, herr := why == "sail-error" }
  | .lab l t' =>
    match fixPost ws l with
    | some ws' => let r := runTX img log i t' ws' prom; { r with nodes := r.nodes + 1 }
    | none => { oos := ["label needs answers"], nodes := 1 }
  | .rd (.dev _) _ _ kids =>
    -- `memStep.dev`: no premise, no effect
    kids.foldl (fun acc (_, t') => acc.add (runTX img log i t' ws prom)) { nodes := 1 }
  | .rd (.base k) base sz kids =>
    (rdSuccs img log i prom ws k base sz).foldl (fun acc s =>
      let vals := ((labelReads s.l).map (fun p => p.2.map Prod.snd)).getD []
      match kids.lookup vals with
      | some t' => acc.add (runTX img log i t' s.ws s.prom)
      | none => acc.add { miss := 1 }) { nodes := 1 }
  | .wr k base data ok ko =>
    let r1 := (wrSuccs img log i prom ws k base data).foldl (fun acc s =>
      acc.add (runTX img log i ok s.ws s.prom)) { nodes := 1 }
    match ko with
    | some t' => r1.add (runTX img log i t' { ws with wRes := none } prom)
    | none => r1
  | .cmo k base len asrc t' =>
    (succCmo log i prom ws k base len asrc).foldl (fun acc s => acc.add (runTX img log i t' s.ws s.prom)) { nodes := 1 }
  | .alt kids => kids.foldl (fun acc t' => acc.add (runTX img log i t' ws prom)) { nodes := 1 }

/-! ## 4. A test through Sail -/

structure STestX where
  T : XTest
  locs : List Nat
  img : Image
  harts : List (SH × BitVec 64 × Nat)

def storeInstrsX (T : XTest) : Nat :=
  T.harts.foldl (fun acc p => acc + (p.filter (fun i => match i with
    | .i (.store ..) | .i (.sc ..) | .i (.amo ..) | .stM .. | .cboZero .. | .cbo .. | .amocas .. => true
    | _ => false)).length) 0

def prepareX (T : XTest) (locs : List Nat) (boot : Nat → Vtest.XRegs) : Except String STestX := do
  let progs ← (List.range T.harts.length).mapM (fun h => do
    let (ws, e) ← asmProgX locs h ((T.harts[h]?).getD [])
    pure (h, ws, e))
  let img := mkImg T.base (progs.map (fun (h, ws, _) => (codeBase h, ws)))
  let harts := progs.map (fun (h, ws, e) =>
    let x0 := (boot h).insert .PC (BitVec.ofNat 64 (codeBase h))
    let x := (((T.regs0[h]?).getD []).foldl (fun x (r, v) => setGpr x r (BitVec.ofNat 64 (reloc locs v))) x0)
    ((⟨.pure (), x, none, ixNone⟩ : SH), BitVec.ofNat 64 e, ws.length + 4))
  pure ⟨T, locs, img, harts⟩

def treesX (S : STestX) (P : BitVec 64 → Bool) (d : Dom) (budget : Nat) : Option (List TX) × Nat :=
  S.harts.foldl (fun (acc : Option (List TX) × Nat) (h, e, mi) =>
    match acc.1 with
    | none => acc
    | some ts =>
      let c : BCfg := ⟨P, e, fun base sz => domRuns S.img d base sz, mi, budget⟩
      let (t, st) := (buildX c h 0).run {}
      (if st.over then none else some (ts ++ [t]), acc.2 + st.events)) (some [], 0)

def closureX (S : STestX) (P : BitVec 64 → Bool) (budget : Nat) :
    Option (List TX × List (List (List PMsg)) × Nat) × Nat :=
  let K := storeInstrsX S.T
  let rec go : Nat → Dom → Nat → Nat → Option (List TX × List (List (List PMsg)) × Nat) × Nat
    | 0, _, _, ev => (none, ev)
    | fuel + 1, d, it, ev =>
      match treesX S P d budget with
      | (none, ev') => (none, ev + ev')
      | (some ts, ev') =>
        let sig := (List.range ts.length).map (fun i => msgListsX i ((ts[i]?).getD default))
        let d' := domOf S.img (sig.flatMap (fun s => s.flatten))
        if domSize d' == domSize d || K ≤ it then
          if domSize d' == domSize d then (some (ts, sig, it + 1), ev + ev') else
          match treesX S P d' budget with
          | (none, ev'') => (none, ev + ev' + ev'')
          | (some ts', ev'') => (some (ts', sig, it + 1), ev + ev' + ev'')
        else go fuel d' (it + 1) (ev + ev')
  go (K + 2) [] 0 0

def outcomesSX (S : STestX) (ts : List TX) (obs : List Key) (M : List PMsg) : Option (List (List Nat)) × MR :=
  let rec harts : Nat → MR → Option (List (List (Nat × Nat × Nat))) × MR
    | 0, st => (some [[]], st)
    | k + 1, st =>
      let i := ts.length - (k + 1)
      let r := runTX S.img M i ((ts[i]?).getD default) psInit (promsOf M i)
      let st := { st with oos := (st.oos ++ r.oos).eraseDups, miss := st.miss + r.miss, nodes := st.nodes + r.nodes,
                          herr := st.herr || r.herr }
      if r.fin.isEmpty && !r.herr then (none, st) else   -- MachFix-havoc
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

/-- The outcome set at one reservation platform (the G5x probes have no SC: one platform). -/
def outsAtX (S : STestX) (P : BitVec 64 → Bool) (obs : List Key) (budget mcap : Nat) :
    Option (List (List Nat)) × SStat := Id.run do
  let mut st : SStat := {}
  match closureX S P budget with
  | (none, ev) => return (none, { st with budget := true, events := ev })
  | (some (ts, sig, it), ev) =>
    st := { st with events := ev, iters := it, oos := ts.flatMap stopsX |>.eraseDups, plats := 1 }
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
        let (r, mr) := outcomesSX S ts obs M
        st := { st with nodes := st.nodes + mr.nodes, miss := st.miss + mr.miss,
                        oos := (st.oos ++ mr.oos).eraseDups }
        match r with
        | none => pure ()
        | some os =>
          st := { st with valid := st.valid + 1, havoc := st.havoc || mr.herr }   -- MachFix-havoc
          for o in os do outs := outs.insert o
    return (some outs.toList, st)

end Weak.Prom.SailLitX
