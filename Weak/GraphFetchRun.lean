/-
Weak: **W5d-G G6-3 (= W11 (iii)), layer L3 — the realization route and the cycle iteration at the
UNPINNED shaped supply** (plan `notes/weak-allocproc-plan.md` rev 51, §C top "W5d-G G6 — LAUNCH
PLAN [rev 50]", paragraph "G6-3 = W11 (iii)", layer L3).  Lean-only, no Rocq twin.

  §1  **`RunDataZ`** — `RunData`'s twin (`WeakRvwmoGlue.lean:275-283`, whose `rdProg` is "deviation
      5: at the pinned program LTS"): `rdProg` is M2's conjunct `execProgOk'STC pstepEv pclsEv
      fokTriv cohSrc (fcutEM2 cohSrc (candExec c) itvOf fiOf)` for SOME `itvOf`/`fiOf` with M2's
      boot values (the free functions of `srvwmoXv6M2Premises`, existential here).
  §2  **`hullRunZ`** (`hullRun`/`hullRunIO`'s twin): a `racyDIO`-acyclic hull of a core graph
      that CARRIES the Zifencei bundle (a hypothesis, as `hullRunIO` takes the hull's bundle) runs:
      under the guards `trDevOrdered` and `candDiskLat` (`GraphFetchBlocks` deviation 3) a `RunDataZ`
      at the fabric `fab ∘ dcnt GF'` of the normalized hull, the trace `linCand`, the hull's rows;
      `hullRunOfKillIOZ`: under `cycleKillIOZ` every proper hull carrying the bundle runs.
  §3  `cstOkZ`/`segStepZ`/`segsRunZ` (`WeakRvwmoCert4` §4's twins: the threaded state's supply is
      M2's conjunct) with `segsRunZOk`/`segsRunZStart`/`segsRunZPrefix`.

**Deviations.**  (1) FILE PLACEMENT (`GraphFetchBlocks` deviation 1).  (2) `RunDataZ.rdProg` existentially
quantifies M2's `itvOf`/`fiOf` (M2 keeps them as free parameters [R30.1]; a run datum names
none).  (3) The guards `trDevOrdered`/`candDiskLat` (the pinned `hullRun` has neither: its bundle is
quiescent; `hullRunIO` discharges the first on the anchored trace, where G5's cut supply is not
proved).  `runErased`'s twin (the M2 replay into the MachCSL run, `srvwmoXv6M2Core`) is NOT here:
it is W11-F's composition.

Lean-only helpers are file-qualified (`GraphFetchRun.*`).
-/
import Weak.GraphFetchLinInd

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The run datum -/

/-- `RunData` at the UNPINNED shaped supply (M2's conjunct). -/
structure RunDataZ (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (c : Cand)
    (pst : Nat → List Pexv6) (dv : Nat → Efab) : Prop where
  rdCons : srvwmoConsistent c
  rdImg : c.cdImg = G.gxImg
  rdPst0 : pst 0 = (List.range' 0 N).map boot
  rdDv0 : dv 0 = d0
  rdSca : candScaT cohSrc c
  /-- M2's conjunct, at some `itvOf`/`fiOf` with M2's boot values. -/
  rdProg : ∃ (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool),
    (∀ i, itvOf 0 i = 0) ∧ (∀ i, fiOf 0 i = false) ∧
    execProgOk'STC pstepEv pclsEv PfRunUnpinned.fokTriv cohSrc
      (PfRunUnpinned.fcutEM2 cohSrc (candExec c) itvOf fiOf) pst dv (candExec c)

/-- A run datum forgets to the shaped conformance at the trivial clause (M1's shape, unpinned). -/
theorem RunDataZ.progST {boot : Nat → Pexv6} {d0 : Efab} {N : Nat} {G : Gexec} {c : Cand}
    {pst : Nat → List Pexv6} {dv : Nat → Efab} (h : RunDataZ boot d0 N G c pst dv) :
    execProgOk'ST pstepEv pclsEv PfRunUnpinned.fokTriv cohSrc pst dv (candExec c) := by
  obtain ⟨_, _, hp⟩ := h.rdProg
  exact execProgOk'STCForget _ _ _ _ _ _ _ _ hp.2.2

/-! # 2. The realization route -/

/-- **`hullRunZ`** (`hullRunIO`'s twin at the unpinned shaped supply). -/
theorem hullRunZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (cs : List Nat) (N : Nat) :
    rvwmoCoreD GF.gfGd →
    hullOk GF.gfGd.gdG cs →
    GraphFabConf.gfexecConfZF boot d0 fab (gfHull GF cs) →
    (∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      (gfHull GF cs).gfGd.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetchBlocks.emFenceCyc em ∧ GraphFetchBlocks.emNoDangle em) →
    (∀ x, ¬ tc (racyDIO (gfHull GF cs)) x x) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (pi : Nat → Nat) (GF' : Gfexec),
      GF'.gfDev = (gfHull GF cs).gfDev ∧
      (∀ i, ((linCand GF'.gfGd.gdG).cdTr.filter (fun s => decide (s.esAg = i))).map
          (fun s => s.esLb) = (((gxHull GF.gfGd.gdG cs).gxProg[i]?).getD []).map (lblRen pi)) ∧
      (trDevOrdered GF' (linCand GF'.gfGd.gdG) → candDiskLat (linCand GF'.gfGd.gdG) →
        ∃ pst : Nat → List Pexv6,
          RunDataZ boot d0 N GF.gfGd.gdG (linCand GF'.gfGd.gdG) pst
            (fun k => fab (dcnt GF' (linCand GF'.gfGd.gdG).cdTr k))) := by
  intro hcore hok hconf hprem hacy hN
  have hNh : (gfHull GF cs).gfGd.gdG.gxProg.length ≤ N := by
    have := gxhNharts GF.gfGd.gdG cs
    change (gxHull GF.gfGd.gdG cs).gxProg.length ≤ N
    omega
  obtain ⟨pi, GF', -, hdev, -, -, hsr, himg, hrow, hscaT, hsup⟩ :=
    topoSupplyZ boot d0 fab (gfHull GF cs) N (hullCoreD GF.gfGd cs hcore hok) hacy hconf hprem hNh
  refine ⟨pi, GF', hdev, hrow, fun hord hdl => ?_⟩
  obtain ⟨pst, lsOf, hpst0, hd0, hi0, hf0, hprg⟩ := hsup hord
  exact ⟨pst, ⟨hsr, himg.trans (gxhImg _ _), hpst0, hd0, hscaT,
    ⟨_, _, hi0, hf0, GraphFetchBlocks.stcOfSC _ _ _ _ _ _ _ _ hprg hscaT hdl⟩⟩⟩

/-- **`cycleKillIOZ` THROUGH `hullRunZ`**: under the kill, every proper hull of a conformant graph
that carries the Zifencei bundle runs (its acyclicity is the induction's, `t2linIOZ` on the
hull). -/
theorem hullRunOfKillIOZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (cs : List Nat) (N : Nat) :
    cycleKillIOZ boot d0 fab GF.gfGd.gdG.gxImg →
    rvwmoMinusDepsConsistent GF.gfGd →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF →
    properCutF GF cs →
    GraphFabConf.gfexecConfZF boot d0 fab (gfHull GF cs) →
    (∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      (gfHull GF cs).gfGd.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetchBlocks.emFenceCyc em ∧ GraphFetchBlocks.emNoDangle em) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (pi : Nat → Nat) (GF' : Gfexec),
      GF'.gfDev = (gfHull GF cs).gfDev ∧
      (∀ i, ((linCand GF'.gfGd.gdG).cdTr.filter (fun s => decide (s.esAg = i))).map
          (fun s => s.esLb) = (((gxHull GF.gfGd.gdG cs).gxProg[i]?).getD []).map (lblRen pi)) ∧
      (trDevOrdered GF' (linCand GF'.gfGd.gdG) → candDiskLat (linCand GF'.gfGd.gdG) →
        ∃ pst : Nat → List Pexv6,
          RunDataZ boot d0 N GF.gfGd.gdG (linCand GF'.gfGd.gdG) pst
            (fun k => fab (dcnt GF' (linCand GF'.gfGd.gdG).cdTr k))) := by
  intro hk hc hres hdr hwio hpc hconf hprem hN
  obtain ⟨hc', hres', hdr', hwio'⟩ := GraphFetchLinInd.hullPremisesZ GF cs hc hres hdr hwio hpc
  exact hullRunZ boot d0 fab GF cs N hc (properCutOk _ _ hpc.1) hconf hprem
    (t2linIOZ boot d0 fab _ hk (gfHull GF cs) rfl hc' hconf hres' hdr' hwio') hN

/-! # 3. The cycle iteration at the unpinned supply -/

/-- `cstOk`'s twin: the threaded candidate is supplied by M2's conjunct. -/
def cstOkZ (d0 : Efab) (St : CycState) : Prop :=
  srvwmoConsistent St.cstC ∧
  (∃ (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool),
    (∀ i, itvOf 0 i = 0) ∧ (∀ i, fiOf 0 i = false) ∧
    execProgOk'STC pstepEv pclsEv PfRunUnpinned.fokTriv cohSrc
      (PfRunUnpinned.fcutEM2 cohSrc (candExec St.cstC) itvOf fiOf) St.cstPst St.cstDv
      (candExec St.cstC)) ∧
  St.cstDv (cdEnd St.cstC) = d0

/-- `segStep`'s twin. -/
def segStepZ (d0 : Efab) (o : Segout) (St St' : CycState) : Prop :=
  cstOkZ d0 St ∧
  cstOkZ d0 St' ∧
  o.soOff = cdEnd St.cstC ∧
  St'.cstC.cdTr = St.cstC.cdTr ++ o.soTr ∧
  (∀ s, s ∈ o.soTr → s.esAg = o.soHart) ∧
  List.Forall₂ lblReidxW o.soRow (o.soTr.map (fun s => s.esLb))

/-- THE WALK at the unpinned supply (`segsRun`'s twin). -/
inductive segsRunZ (d0 : Efab) : List Segout → CycState → CycState → Prop where
  | segsDone (St : CycState) : cstOkZ d0 St → segsRunZ d0 [] St St
  | segsMore (o : Segout) (l : List Segout) (St St' St'' : CycState) :
      segStepZ d0 o St St' → segsRunZ d0 l St' St'' → segsRunZ d0 (o :: l) St St''

theorem segsRunZOk (d0 : Efab) (l : List Segout) (St St' : CycState) :
    segsRunZ d0 l St St' → cstOkZ d0 St' := by
  intro h
  induction h with
  | segsDone _ hs => exact hs
  | segsMore _ _ _ _ _ _ _ ih => exact ih

theorem segsRunZStart (d0 : Efab) (l : List Segout) (St St' : CycState) :
    segsRunZ d0 l St St' → cstOkZ d0 St := by
  intro h
  cases h with
  | segsDone _ hs => exact hs
  | segsMore _ _ _ _ _ hst _ => exact hst.1

theorem segsRunZPrefix (d0 : Efab) (l : List Segout) (St St' : CycState) :
    segsRunZ d0 l St St' → ∃ ext, St'.cstC.cdTr = St.cstC.cdTr ++ ext := by
  intro h
  induction h with
  | segsDone _ _ => exact ⟨[], by rw [List.append_nil]⟩
  | segsMore o _ St St' St'' hst _ ih =>
    obtain ⟨ext, he⟩ := ih
    exact ⟨o.soTr ++ ext, by rw [he, hst.2.2.2.1, List.append_assoc]⟩

/-- A run datum whose fabric ends at `d0` is a valid threaded state. -/
theorem GraphFetchRun.cstOkZOfRunDataZ (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec)
    (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab) :
    RunDataZ boot d0 N G c pst dv → dv (cdEnd c) = d0 → cstOkZ d0 ⟨c, pst, dv⟩ :=
  fun h he => ⟨h.rdCons, h.rdProg, he⟩

/-! # 4. The erased run (L4 enabler: `runErased`'s twin) -/

/-- A shadow-threaded, cut-carrying run is a run of the promise-free machine. -/
theorem GraphFetchRun.pfRunSTCRtc {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass)
    (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) (stamp : CohStamp)
    (fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (c c' : Wpcfg P D) (st : List (Nat × Wlabel)) :
    pfRunSTC pstep pcls fok stamp fcutT c st c' → rtc (wpPfRun pstep pcls) c c' := by
  intro h
  induction h with
  | nil => exact rtc_refl _
  | snoc c1 c2 st i l _ hs _ _ _ ih => exact rtc_r ih ⟨i, l, hs⟩

section run

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **`runErasedZ`** (`runErased`'s twin, `WeakRvwmoGlue.lean:313`): a `RunDataZ` at the booted
state is an erased run of the event pool ending at the candidate's log — through M2's replay
`execWfPfRunProgF` (unpinned, cut-carrying), not `execWfPfRunPin`.  The fetch-view premise is
`runErased`'s, unchanged (W11-F replaces it). -/
theorem runErasedZ (gen : Nat) (σ0 : WGState) (boot : Nat → Pexv6) (d0 : Efab) (N : Nat)
    (G : Gexec) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab) :
    freshEra gen σ0 →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    G.gxImg = imgZ σ0.wgimg →
    RunDataZ boot d0 N G c pst dv →
    ∃ (t2 : List EExpr) (σ2 : WGState),
      (epowerFork gen, σ0) -·->ₜₚ* (t2, σ2) ∧
      σ2.wglog = cdLog c c.cdTr.length := by
  rintro ⟨hgen, hpow, hgen0, hlog, hws⟩ hcov hb1 hb2 hb3 ⟨hcons, himg, hpst0, hdv0, -, hprog⟩
  obtain ⟨itvOf, fiOf, hi0, hf0, hprg⟩ := hprog
  have hlive : ethreadLive σ0 gen := ⟨hpow, by rw [hgen0, hgen]⟩
  obtain ⟨hwf, -, heximg⟩ := srvwmoRealizable c hcons
  obtain ⟨cf, st, hrunS, -, -, -, hm, -, -⟩ :=
    execWfPfRunProgF pstepEv pclsEv _ cohSrc pst dv (candExec c) itvOf fiOf pclsEvEqr hwf hprg
      hi0 hf0
  have hrun := GraphFetchRun.pfRunSTCRtc _ _ _ _ _ _ _ _ hrunS
  rw [heximg, himg, hb3, hpst0, hb1, hdv0, hb2, ← ecfgOfInit gen σ0 hlog hws] at hrun
  obtain ⟨P', σ', hr, heq⟩ := wpPfRtcEpfRtc (epInit gen) σ0 cf hlive hcov hrun
  refine ⟨epoolList P', σ', ?_, ?_⟩
  · have he := epfRtcErased (epInit gen, σ0) (P', σ') hr
    rw [show (epInit gen, σ0).1 = epInit gen from rfl, epoolListInit] at he
    exact he
  · obtain ⟨-, hlg, -⟩ := hm
    rw [← ecfgOfLog P' σ', heq, ← hlg, candExTr]
    exact candElog c c.cdTr.length (Nat.le_refl _)

end run

end Weak
