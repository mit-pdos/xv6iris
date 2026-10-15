/-
Weak: **W11-F [OWN.102], (ii) increment 2 — EVERY MESSAGE OF A REALIZED LOG WRITES RAM**, and
`readAt`'s `inRam` clause.  Lean-only, no Rocq twin.

* `CapF10.hartFoot` / `CapF10.diskFoot` — a store label (`LStore`/`LExStore`/`LRmw`) of a hart comes
  from a non-device `memWrite` node; of the disk agent, from `DWriteDev`'s RAM-checked store;
* `CapF10.stepLogRam` — at a W4-realized pf configuration (`SimRel`, reachable from power-on, the step
  adjacent), a step keeps `CapF9.logRam`: the hart's footprint is RAM by `ramOfSafe` (the MachCSL
  hart thread is reducible, `HypsC.safe`; no foreign reservation, `notOthers`); the disk's by its
  program's own check;
* `CapF10.runLogRam` — along every W4 run record from a related configuration (`simRun`'s induction);
* `CapF10.loadReadAtRam` — `CapF8.loadReadAtParts` plus `inRam pa 1`.

Spec: FAITHFUL (proof organisation).  Names: `CapF10.*`.
-/
import Weak.CapF9
import Weak.CapF8

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open LeanRV64D
open Wlabel
open TsoShadow PfStepTsoView
open MachOfPf

/-- The store labels, at footprint `base` / `data`. -/
def CapF10.isSt (l : Wlabel) (base : Int) (data : List (BitVec 8)) : Prop :=
  (∃ rl a v, l = LStore rl base data a v) ∨ (∃ rl a v, l = LExStore rl base data a v) ∨
  (∃ aq rl tvs a v, l = LRmw aq rl base tvs data a v)

/-- A hart's store label comes from a non-device `memWrite` node. -/
theorem CapF10.hartFoot (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6)
    (d' : Efab) (base : Int) (data : List (BitVec 8))
    (hst : pstepEv (.PHart cpu m rs fn ib) d l p' d') (hl : CapF10.isSt l base data) :
    ∃ n va req k, m = .impure (.ok (.memWrite n va req)) k ∧ devAddr req.pa = false ∧
      base = paZ req.pa ∧ data.length = n := by
  cases p' with
  | PDisk _ => exact hst.elim
  | PHart cpu' m' rs' fn' ib' =>
  obtain ⟨-, ors, oib, obar, -, -, hh⟩ := hst
  rcases hh with ⟨hn, -⟩ | ⟨_, _, _, -, hld, _⟩
  · unfold pstepNode at hn
    cases fn with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      obtain ⟨hlf, -⟩ := hn
      rcases hl with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> exact nomatch hlf
    | none =>
      rcases hl with ⟨rl, a, v, rfl⟩ | ⟨rl, a, v, rfl⟩ | ⟨aq, rl, tvs, a, v, rfl⟩
      · obtain ⟨n, va, req, k, rfl, hdev, w, -, -, -, hb, hd, -⟩ :=
          CapF9.pnodeStoreInv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn
        exact ⟨n, va, req, k, rfl, hdev, hb, by rw [hd]; exact wbytesLength n w⟩
      · obtain ⟨n, va, req, k, rfl, hdev, w, -, -, -, -, hb, hd, -⟩ :=
          SilPf.pnodeExStoreInv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn
        exact ⟨n, va, req, k, rfl, hdev, hb, by rw [hd]; exact wbytesLength n w⟩
      · exact (CapF9.pnodeRmwFalse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn).elim
  · rcases hl with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> exact nomatch hld

/-- The disk agent's store label is a RAM-checked `DWriteDev` store. -/
theorem CapF10.diskFoot (dp : Option (DM Dres)) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab)
    (base : Int) (data : List (BitVec 8)) (hst : pstepEv (.PDisk dp) d l p' d')
    (hl : CapF10.isSt l base data) : ∃ pa : PAddr, base = paZ pa ∧ ramBytes pa data.length := by
  cases p' with
  | PHart _ _ _ _ _ => exact hst.elim
  | PDisk dp' =>
  rcases hl with ⟨rl, a, v, rfl⟩ | ⟨rl, a, v, rfl⟩ | ⟨aq, rl, tvs, a, v, rfl⟩
  · exact CapF9.pstepDiskStore _ _ _ _ _ _ _ _ _ hst
  · exfalso
    rcases hst with ⟨h, -⟩ | ⟨-, h, -⟩
    · rcases WeakEvInst.pdiskProgLabel _ _ _ _ _ h with h | ⟨_, _, _, h⟩ | h | ⟨_, _, h⟩ | h <;>
        exact nomatch h
    · exact nomatch h
  · exfalso
    rcases hst with ⟨h, -⟩ | ⟨-, h, -⟩
    · rcases WeakEvInst.pdiskProgLabel _ _ _ _ _ h with h | ⟨_, _, _, h⟩ | h | ⟨_, _, h⟩ | h <;>
        exact nomatch h
    · exact nomatch h

section real
variable {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
  {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
  {g0 : GState} {c0 : Wpcfg Pexv6 Efab}

/-- **The footprint of a realized agent's store is RAM** (header). -/
theorem CapF10.agentFoot (hH : HypsC fok fcutT g0 c0) {c : Wpcfg Pexv6 Efab}
    {st rest : List (Nat × Wlabel)} {t : List Expr} {g : GState} {n : Nat} {κ : List Obs}
    (hR : SimRel c st t g) (hreach : MRun n ([Expr.power], g0) κ (t, g)) (i : Nat) (l : Wlabel)
    (hadj : pairAdjacent (st ++ (i, l) :: rest)) (ag : Wpagent Pexv6) (hlk : c.pcAgs[i]? = some ag)
    (p' : Pexv6) (d' : Efab) (hst : pstepEv ag.paSt c.pcDev l p' d') (base : Int)
    (data : List (BitVec 8)) (hl : CapF10.isSt l base data) :
    ∃ pa : PAddr, base = paZ pa ∧ ramBytes pa data.length := by
  obtain ⟨H, vs, dp, dws, dpr, ht, hlen, hharts, hdisk, -⟩ := hR.pool
  by_cases hi : i < NCPU
  · let cpu : CPU := ⟨i, hi⟩
    obtain ⟨fn, ib, ws, pr, hlkc, -⟩ := hharts cpu
    have e : ag = ⟨.PHart cpu (H cpu) (g.m.regs cpu) fn ib, ws, pr⟩ := by
      have : c.pcAgs[cpu.val]? = some ag := hlk
      rw [hlkc] at this; exact (Option.some.inj this).symm
    subst e
    obtain ⟨n0, va, req, k, hm, hdev, hb, hd⟩ :=
      CapF10.hartFoot cpu _ _ _ _ _ l p' d' base data hst hl
    have hred := hH.safe n κ t g hreach _
      (List.mem_of_getElem? (by rw [ht]; exact poolHart H c.pcDev vs cpu))
    rw [hm] at hred
    have hadj' : pairAdjacent (st ++ (hartAgent cpu, l) :: rest) := hadj
    obtain ⟨-, hrbW⟩ := ramOfSafe hred ⟨hR.pow, hR.gen⟩ (notOthers hR.mem hadj')
    exact ⟨req.pa, hb, by rw [hd]; exact hrbW n0 va req rfl hdev⟩
  · have hiN : i = NCPU := by
      have := lookup_lt_Some hlk
      omega
    subst hiN
    rw [hdisk] at hlk
    obtain rfl := (Option.some.inj hlk).symm
    exact CapF10.diskFoot dp _ l p' d' base data hst hl

/-- **One step keeps the log RAM-only** (header). -/
theorem CapF10.stepLogRam (hH : HypsC fok fcutT g0 c0) {c c' : Wpcfg Pexv6 Efab}
    {st rest : List (Nat × Wlabel)} {t : List Expr} {g : GState} {n : Nat} {κ : List Obs}
    (hR : SimRel c st t g) (hreach : MRun n ([Expr.power], g0) κ (t, g)) (i : Nat) (l : Wlabel)
    (hs : wpPfStep pstepEv pclsEv i l c c') (hadj : pairAdjacent (st ++ (i, l) :: rest))
    (hlog : CapF9.logRam c.pcLog) : CapF9.logRam c'.pcLog := by
  cases hs with
  | PFStore _ ag rl base data asrc vsrc k st' d' hlk hst _ _ =>
    obtain ⟨pa, rfl, hram⟩ := CapF10.agentFoot hH hR hreach i _ hadj ag hlk st' d' hst base data
      (Or.inl ⟨rl, asrc, vsrc, rfl⟩)
    exact CapF9.logRamSnoc _ _ hlog (CapF9.msgRamOf pa data _ k hram)
  | PFRmw _ ag aq rl base tvs data asrc vsrc k st' d' hlk hst _ _ _ _ _ =>
    obtain ⟨pa, rfl, hram⟩ := CapF10.agentFoot hH hR hreach i _ hadj ag hlk st' d' hst base data
      (Or.inr (Or.inr ⟨aq, rl, tvs, asrc, vsrc, rfl⟩))
    exact CapF9.logRamSnoc _ _ hlog (CapF9.msgRamOf pa data _ k hram)
  | PFExStore _ ag rl base data asrc vsrc k _ st' d' hlk hst _ _ _ _ _ _ =>
    obtain ⟨pa, rfl, hram⟩ := CapF10.agentFoot hH hR hreach i _ hadj ag hlk st' d' hst base data
      (Or.inr (Or.inl ⟨rl, asrc, vsrc, rfl⟩))
    exact CapF9.logRamSnoc _ _ hlog (CapF9.msgRamOf pa data _ k hram)
  | PFSilent => exact hlog
  | PFLoad => exact hlog
  | PFFence => exact hlog
  | PFDev => exact hlog
  | PFRegW => exact hlog
  | PFCtrl => exact hlog
  | PFInstr => exact hlog
  | PFExLoad => exact hlog
  | PFIFetch => exact hlog

/-- **Along a run record, the log stays RAM-only** (header; `simRun`'s induction). -/
theorem CapF10.runLogRam (hH : HypsC fok fcutT g0 c0) :
    ∀ {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab},
      contRC fok fcutT c st r cN →
      ∀ {t : List Expr} {g : GState} {n : Nat} {κ : List Obs},
        SimRel c st t g → MRun n ([Expr.power], g0) κ (t, g) →
        pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c → pairAdjacent (st ++ recLabels r) →
        CapF9.logRam c.pcLog → CapF9.logRam cN.pcLog := by
  intro c st r cN h
  induction h with
  | nil c st => intro _ _ _ _ _ _ _ _ hl; exact hl
  | cons c c' st i l k r cN hs hf hfT hcf hk hr ih =>
    intro t g n κ hR hreach hrun hadj hlog
    have hadj' : pairAdjacent (st ++ (i, l) :: recLabels r) := by
      simpa [recLabels] using hadj
    have hlog' := CapF10.stepLogRam hH hR hreach i l hs hadj' hlog
    obtain ⟨m1, t1, g1, -, hm1, hR1⟩ := simStep hH hR hreach hrun hs hf hfT hcf hk hadj'
      (fun aq base tvs asrc hl => by subst hl; exact exclAhead fok hs hr hadj')
    exact ih hR1 (mrunTrans hreach hm1) (pfRunST.snoc c c' st i l hrun hs hf hfT)
      (by simpa using hadj') hlog'

end real

/-- `paZ` is injective. -/
theorem CapF10.paZInj (pa pa' : PAddr) (h : paZ pa = paZ pa') : pa = pa' := by
  unfold paZ at h
  exact BitVec.eq_of_toNat_eq (by omega)

/-- **`readAt`'s floor, export, `rmem`, message AND `inRam` clauses at a realized candidate load**
(header). -/
theorem CapF10.loadReadAtRam (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool)
    (hP : srvwmoXv6M2Premises σ0 c pst dv itvOf fiOf)
    (g0 : GState) (hg0 : g0.gen = 0) (hp0 : g0.pow = false) (hgd : σ0.wgdev = g0.m.devs.reset)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk)
    (k : Nat) (s : Estep) (hs : (candExec c).exTr[k]? = some s) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (hl : s.esLb = .LLoad aq base ts vs) (j p au' : Nat)
    (hj : ts[j]? = some (p + 1))
    (hsrc : shSrc (shadowRun cohSrc s.esAg ((candExec c).exTr.take k)).1 (p + 1) = some (au', p + 1))
    (hne : au' ≠ s.esAg) (cpu : CPU) (hcpu : hartAgent cpu = s.esAg) (pa : PAddr)
    (hpa : paZ pa = accAddr base j) :
    ∃ (cf : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (t' : List Expr) (g : GState) (m : Wmsg),
      CapF1.realAt g0 cf st t' g ∧ cf.pcLog = elog (candExec c) (k + 1) ∧
      (g.m.hr cpu).coh pa = p + 1 ∧ cf.pcLog[p]? = some m ∧ (msgByte m (paZ pa)).isSome ∧
      inRam pa 1 := by
  obtain ⟨cf, st, t', g, m, hreal, hlog, hcoh, hm, hmb⟩ :=
    CapF8.loadReadAtParts σ0 c pst dv itvOf fiOf hP g0 hg0 hp0 hgd hfs k s hs aq base ts vs hl j p
      au' hj hsrc hne cpu hcpu pa hpa
  refine ⟨cf, st, t', g, m, hreal, hlog, hcoh, hm, hmb, ?_⟩
  -- the log of the M2 prefix run at `k + 1` is RAM-only (re-realize that run with its record)
  obtain ⟨hb, -, -, hcons, himg, hpst, hdv, hprog, -, -, hi0, hf0⟩ := hP
  obtain ⟨hwf, -, heximg⟩ := srvwmoRealizable c hcons
  have hk : k + 1 ≤ (candExec c).exTr.length := lookup_lt_Some hs
  obtain ⟨cf2, st2, hrun, hadj, -, -, hm2, -, -⟩ :=
    execPrefixPfRunProgF pstepEv pclsEv _ cohSrc pst dv (candExec c) itvOf fiOf (k + 1)
      pclsEvEqr hwf hprog hi0 hf0 hk
  rw [heximg, himg, hpst, hdv] at hrun
  have hH := PfRunUnpinned.m2Hyps σ0 hb g0 hg0 hp0 hfs sailCycleOrder_holds
  obtain ⟨r, hr, hl'⟩ := contROfRun _ hrun
  have hboot := powerOnRun g0 σ0 g0.m.devs hb hg0 hp0 rfl
  have hR0 := simRelBoot σ0 g0.m.devs hb hgd
  have hram := CapF10.runLogRam hH hr hR0 hboot pfRunST.nil (by simpa [hl'] using hadj)
    CapF9.logRamNil
  have hlogeq : cf2.pcLog = cf.pcLog := by rw [hlog, ← hm2.2.1]; rfl
  rw [hlogeq] at hram
  obtain ⟨pa', he, hin⟩ := hram m (List.mem_of_getElem? hm) _ hmb
  rw [← CapF10.paZInj pa' pa he]
  exact hin

end Weak
