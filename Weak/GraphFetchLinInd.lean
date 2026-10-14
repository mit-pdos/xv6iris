/-
Weak: **W5d-G G6-3 (= W11 (iii)), layer L2 — T2-LIN's corollary at the UNPINNED shaped supply**
(plan `notes/weak-allocproc-plan.md` rev 51, §C top "W5d-G G6 — LAUNCH PLAN [rev 50]", paragraph
"G6-3 = W11 (iii)", layer L2).  Lean-only, no Rocq twin.

The pinned corollaries `t2linSupply` (`WeakRvwmoLinInd`), `t2linSupplyF` (`WeakRvwmoFabInd`),
`t2linRealizeIO` (`WeakRvwmoKillIO`) and `CatLin.t2linSupplyC` (`CatLinChain`) compose a KILL
obligation, the strong induction on the event count over causal hulls (`t2linAux*`), and the
pinned supply.  Their Zifencei twins here compose the same induction with `topoSupplyZ`
(`Weak/GraphFetchBlocks.lean`):

  §1  `cycleKillIOZ` (the `cycleKillIO` twin over the Zifencei bundle `GraphFabConf.gfexecConfZF`),
      `t2linAuxIOZ`, `t2linIOZ`, **`t2linSupplyFZ`** (`t2linRealizeIO`/`t2linSupplyF`'s twin: the
      whole graph's normalized rule-14 linearization supplied by M2's shaped conjunct);
  §2  `CatLin.cycleKillCZ`, `CatLin.t2linAuxCZ`, **`CatLin.t2linSupplyCZ`** (the cat twin);
  §3  **`t2linSupplyZ`** — the composition over `xv6ConfSForget` (the tagged Zifencei bundle of
      G6-2): an `xv6ConfS` graph under the kill is supplied by M2's conjunct.

**THE HULL GUARD (deviation 1; the plan's XL risk R1, §B(4)(iii)).**  The pinned induction passes
its bundle to every proper hull (`gfexecConfHull`): the pinned fetch clause `emFetchImg` is a
property of the emission alone.  The Zifencei clause `emZifencei` is NOT: (Z1)–(Z3) read the
graph's writes, write indices and gmo, and a `properCut` (`hullOk`: rf-closed, no fetch
closure) may cut a kept fetch's source write — e.g. the fetch of a `fence.i` whose only own later
memory events are cut (`fetchEdge`'s E1 arm targets memory events only, `gmem`), so no fragment
edge keeps the source; the hull then renames the tag to itself (`hren`) and (Z1) fails.  So
"every proper hull of a Zifencei bundle is a Zifencei bundle" is FALSE in general and is NOT
assumed.  Instead the kill's induction hypothesis is GUARDED: `cycleKillIOZ` hands the kill
acyclicity of every proper hull ON WHICH THE ZIFENCEI BUNDLE HOLDS.  The induction then needs no
hull stability, the corollaries are fully proved from the kill, and R1 moves INTO the kill
obligation (W11-F): it must certify its cuts' Zifencei bundles (e.g. by choosing fetch-source-
closed cuts and proving stability for those).  Spec: proof organisation — RVWMO/riscv.cat/
Zifencei/PMAs are silent on how a proof cuts a graph; FAITHFUL, no trusted text.

**Deviations from the plan text.**  (1) The hull guard (above).  (2) FILE PLACEMENT: a NEW leaf
(`topoSupplyZ` sits above `LinInd`/`FabInd`/`CatLinChain`, `GraphFetchBlocks` deviation 1).
(3) The `WeakRvwmoFabInd` twin is the `racyDIO` one (`t2linRealizeIO`'s shape, `cycleKillIO`'s
premise set): G5's supply needs `racyDIO`-acyclicity, and `racyF` (FabInd's) does not give it.
(4) There is no quiescent Zifencei bundle (`gdexecQconf`'s clause is the pinned one); the
`WeakRvwmoLinInd` twin `t2linSupplyZ` is the composition over `xv6ConfSForget` (§3), the bundle the
plan names.  (5) (P2) of `GraphFetchBlocks` is a premise of every corollary ((P1) retired by [OWN.86]).

Lean-only helpers are file-qualified (`GraphFetchLinInd.*`).
-/
import Weak.GraphFetchBlocks
import Weak.CatLinHull

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The `racyDIO` chain -/

/-- **THE KILL OBLIGATION at the Zifencei bundle** (`cycleKillIO`'s twin, GUARDED induction
hypothesis — deviation 1): at a conformant graph every proper hull of which that carries the
Zifencei bundle is already `racyDIO`-acyclic, there is no `racyDIO` cycle. -/
def cycleKillIOZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) : Prop :=
  ∀ GF : Gfexec,
    GF.gfGd.gdG.gxImg = im →
    rvwmoMinusDepsConsistent GF.gfGd →
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF →
    (∀ cs, properCutF GF cs → GraphFabConf.gfexecConfZF boot d0 fab (gfHull GF cs) →
      ∀ x, ¬ tc (racyDIO (gfHull GF cs)) x x) →
    ∀ x, tc (racyDIO GF) x x → False

/-- The bundle-free premises of the kill pass to a proper hull (`WeakRvwmoKillIO.hullPremises`
without the pinned bundle). -/
theorem GraphFetchLinInd.hullPremisesZ (GF : Gfexec) (cs : List Nat) :
    rvwmoMinusDepsConsistent GF.gfGd →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF → properCutF GF cs →
    rvwmoMinusDepsConsistent (gfHull GF cs).gfGd ∧
    ioResidueGmo (gfHull GF cs) ∧ gdiskRead14 (gfHull GF cs).gfGd.gdG ∧
    gfDevWIo (gfHull GF cs) := by
  intro hc hres hdr hwio hpc
  have hok : hullOk GF.gfGd.gdG cs := properCutOk _ _ hpc.1
  have hnd := hc.1.1.1
  exact ⟨hullDepsConsistent _ cs hc hok, ioResidueGmoHull GF cs hnd hpc.2 hres,
    gdiskRead14Hull GF.gfGd.gdG cs hnd hdr, gfDevWIoHull GF cs hwio⟩

/-- THE INDUCTION (`t2linAuxIO`'s mirror; the guard is discharged by the hull's own bundle). -/
theorem t2linAuxIOZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) :
    cycleKillIOZ boot d0 fab im →
    ∀ (n : Nat) (GF : Gfexec),
      (gevs' GF.gfGd.gdG).length ≤ n →
      GF.gfGd.gdG.gxImg = im →
      rvwmoMinusDepsConsistent GF.gfGd → GraphFabConf.gfexecConfZF boot d0 fab GF →
      ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF →
      ∀ x, ¬ tc (racyDIO GF) x x := by
  intro hk n
  induction n with
  | zero =>
    intro GF hlen him hc hconf hres hdr hwio x hcyc
    refine hk GF him hc hconf hres hdr hwio ?_ x hcyc
    intro cs hpc _ y _
    have := gfHullEventsLt GF cs hpc
    omega
  | succ n ih =>
    intro GF hlen him hc hconf hres hdr hwio x hcyc
    refine hk GF him hc hconf hres hdr hwio ?_ x hcyc
    intro cs hpc hconf'
    obtain ⟨hc', hres', hdr', hwio'⟩ :=
      GraphFetchLinInd.hullPremisesZ GF cs hc hres hdr hwio hpc
    refine ih (gfHull GF cs) ?_ him hc' hconf' hres' hdr' hwio'
    have := gfHullEventsLt GF cs hpc
    omega

theorem t2linIOZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) :
    cycleKillIOZ boot d0 fab im →
    ∀ GF : Gfexec,
      GF.gfGd.gdG.gxImg = im →
      rvwmoMinusDepsConsistent GF.gfGd → GraphFabConf.gfexecConfZF boot d0 fab GF →
      ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF →
      ∀ x, ¬ tc (racyDIO GF) x x :=
  fun hk GF => t2linAuxIOZ boot d0 fab im hk (gevs' GF.gfGd.gdG).length GF (Nat.le_refl _)

/-- **THE COROLLARY at the unpinned shaped supply** (`t2linRealizeIO`/`t2linSupplyF`'s twin):
under the kill, a conformant Zifencei graph whose emissions satisfy (P2) normalizes to `GF'`
whose rule-14 linearization is consistent, `candScaT`, and — under the guard `trDevOrdered` — is
supplied by M2's shaped conjunct `execProgOk'SC … (fcutEM2 cohSrc E itvOfL fiOfL)` with M2's
boot values. -/
theorem t2linSupplyFZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (N : Nat) :
    cycleKillIOZ boot d0 fab GF.gfGd.gdG.gxImg →
    rvwmoMinusDepsConsistent GF.gfGd → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF →
    (∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      GF.gfGd.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetchBlocks.emNoDangle em) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (pi : Nat → Nat) (GF' : Gfexec),
      rowsRel pi GF.gfGd.gdG GF'.gfGd.gdG ∧ GF'.gfDev = GF.gfDev ∧
      srvwmoConsistent (linCand GF'.gfGd.gdG) ∧
      (linCand GF'.gfGd.gdG).cdImg = GF.gfGd.gdG.gxImg ∧
      candScaT cohSrc (linCand GF'.gfGd.gdG) ∧
      (trDevOrdered GF' (linCand GF'.gfGd.gdG) →
        ∃ (pst : Nat → List Pexv6) (lsOf : Nat → List Wlabel),
          pst 0 = (List.range' 0 N).map boot ∧
          fab (dcnt GF' (linCand GF'.gfGd.gdG).cdTr 0) = d0 ∧
          (∀ i, GraphFetchSupply.itvOfL cohSrc (candExec (linCand GF'.gfGd.gdG)) lsOf 0 i = 0) ∧
          (∀ i, GraphFetchSupply.fiOfL (candExec (linCand GF'.gfGd.gdG)).exTr lsOf 0 i = false) ∧
          execProgOk'SC pstepEv pclsEv PfRunUnpinned.fokTriv
            (PfRunUnpinned.fcutEM2 cohSrc (candExec (linCand GF'.gfGd.gdG))
              (GraphFetchSupply.itvOfL cohSrc (candExec (linCand GF'.gfGd.gdG)) lsOf)
              (GraphFetchSupply.fiOfL (candExec (linCand GF'.gfGd.gdG)).exTr lsOf))
            pst (fun k => fab (dcnt GF' (linCand GF'.gfGd.gdG).cdTr k))
            (candExec (linCand GF'.gfGd.gdG))) := by
  intro hk hc hconf hres hdr hwio hprem hN
  obtain ⟨pi, GF', hrr, hdev, -, -, hsr, himg, -, hscaT, hsup⟩ :=
    topoSupplyZ boot d0 fab GF N hc (t2linIOZ boot d0 fab _ hk GF rfl hc hconf hres hdr hwio) hconf
      hprem hN
  exact ⟨pi, GF', hrr, hdev, hsr, himg, hscaT, hsup⟩

/-! # 2. The cat chain -/

namespace CatLin

/-- The cat kill obligation at the Zifencei bundle (`cycleKillC`'s twin over the fabric bundle;
the guarded induction hypothesis, deviation 1). -/
def cycleKillCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im →
    rvwmoCatAD GF.gfGd ad →
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    (∀ cs, properCutF GF cs → GraphFabConf.gfexecConfZF boot d0 fab (gfHull GF cs) →
      ∀ x, ¬ tc (racyDIO (gfHull GF cs)) x x) →
    ∀ x, tc (racyDIO GF) x x → False

theorem t2linAuxCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) :
    cycleKillCZ boot d0 fab im →
    ∀ (n : Nat) (GF : Gfexec) (ad : List (Geid × Geid)),
      (gevs' GF.gfGd.gdG).length ≤ n →
      GF.gfGd.gdG.gxImg = im →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
      ∀ x, ¬ tc (racyDIO GF) x x := by
  intro hk n
  induction n with
  | zero =>
    intro GF ad hlen him hc hconf hres hdr x hcyc
    refine hk GF ad him hc hconf hres hdr ?_ x hcyc
    intro cs hpc _ y _
    have := gfHullEventsLt GF cs hpc
    omega
  | succ n ih =>
    intro GF ad hlen him hc hconf hres hdr x hcyc
    refine hk GF ad him hc hconf hres hdr ?_ x hcyc
    intro cs hpc hconf'
    have hnd := hc.1.1
    refine ih (gfHull GF cs) (adCut cs ad) ?_ him
      (hullCatAD GF.gfGd ad cs hc (properCutOk _ _ hpc.1)) hconf'
      (ioResidueGmoHull GF cs hnd hpc.2 hres) (gdiskRead14Hull GF.gfGd.gdG cs hnd hdr)
    have := gfHullEventsLt GF cs hpc
    omega

theorem t2linOfCycleKillCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) :
    cycleKillCZ boot d0 fab im →
    ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
      GF.gfGd.gdG.gxImg = im →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
      ∀ x, ¬ tc (racyDIO GF) x x :=
  fun hk GF ad => t2linAuxCZ boot d0 fab im hk (gevs' GF.gfGd.gdG).length GF ad (Nat.le_refl _)

/-- **THE CAT COROLLARY at the unpinned shaped supply** (`t2linSupplyC`'s twin). -/
theorem t2linSupplyCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (ad : List (Geid × Geid)) (N : Nat) :
    cycleKillCZ boot d0 fab GF.gfGd.gdG.gxImg →
    rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    (∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      GF.gfGd.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetchBlocks.emNoDangle em) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (pi : Nat → Nat) (GF' : Gfexec),
      rowsRel pi GF.gfGd.gdG GF'.gfGd.gdG ∧ GF'.gfDev = GF.gfDev ∧
      srvwmoConsistent (linCand GF'.gfGd.gdG) ∧
      (linCand GF'.gfGd.gdG).cdImg = GF.gfGd.gdG.gxImg ∧
      candScaT cohSrc (linCand GF'.gfGd.gdG) ∧
      (trDevOrdered GF' (linCand GF'.gfGd.gdG) →
        ∃ (pst : Nat → List Pexv6) (lsOf : Nat → List Wlabel),
          pst 0 = (List.range' 0 N).map boot ∧
          fab (dcnt GF' (linCand GF'.gfGd.gdG).cdTr 0) = d0 ∧
          (∀ i, GraphFetchSupply.itvOfL cohSrc (candExec (linCand GF'.gfGd.gdG)) lsOf 0 i = 0) ∧
          (∀ i, GraphFetchSupply.fiOfL (candExec (linCand GF'.gfGd.gdG)).exTr lsOf 0 i = false) ∧
          execProgOk'SC pstepEv pclsEv PfRunUnpinned.fokTriv
            (PfRunUnpinned.fcutEM2 cohSrc (candExec (linCand GF'.gfGd.gdG))
              (GraphFetchSupply.itvOfL cohSrc (candExec (linCand GF'.gfGd.gdG)) lsOf)
              (GraphFetchSupply.fiOfL (candExec (linCand GF'.gfGd.gdG)).exTr lsOf))
            pst (fun k => fab (dcnt GF' (linCand GF'.gfGd.gdG).cdTr k))
            (candExec (linCand GF'.gfGd.gdG))) := by
  intro hk hc hconf hres hdr hprem hN
  obtain ⟨pi, GF', hrr, hdev, -, -, hsr, himg, -, hscaT, hsup⟩ :=
    topoSupplyZ boot d0 fab GF N (catADCore _ _ hc)
      (t2linOfCycleKillCZ boot d0 fab _ hk GF ad rfl hc hconf hres hdr) hconf hprem hN
  exact ⟨pi, GF', hrr, hdev, hsr, himg, hscaT, hsup⟩

end CatLin

/-! # 3. Over `xv6ConfSForget` -/

/-- **`t2linSupplyZ` — THE COROLLARY OVER THE TAGGED ZIFENCEI BUNDLE** (`xv6ConfS`, G6-2): under the
kill at every fabric trace, an `xv6ConfS` graph whose untagged projection `forgetF GT` is RVWMO⁻,
carries the I/O residue facts and whose emissions satisfy (P2) is supplied — at some fabric
trace `fab` of its bundle — by M2's shaped conjunct (`t2linSupplyFZ` on `forgetF GT`). -/
theorem t2linSupplyZ (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GT : GfexecT)
    (N : Nat) :
    (∀ fab, cycleKillIOZ boot d0 fab im) →
    xv6ConfS boot d0 im nh GT →
    rvwmoMinusDepsConsistent (forgetF GT).gfGd →
    ioResidueGmo (forgetF GT) → gdiskRead14 (forgetF GT).gfGd.gdG → gfDevWIo (forgetF GT) →
    (∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      (forgetF GT).gfGd.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetchBlocks.emNoDangle em) →
    nh ≤ N →
    ∃ (fab : Nat → Efab) (pi : Nat → Nat) (GF' : Gfexec),
      (forgetF GT).gfGd.gdG.gxImg = im ∧
      rowsRel pi (forgetF GT).gfGd.gdG GF'.gfGd.gdG ∧ GF'.gfDev = GT.gfDev ∧
      srvwmoConsistent (linCand GF'.gfGd.gdG) ∧
      (linCand GF'.gfGd.gdG).cdImg = im ∧
      candScaT cohSrc (linCand GF'.gfGd.gdG) ∧
      (trDevOrdered GF' (linCand GF'.gfGd.gdG) →
        ∃ (pst : Nat → List Pexv6) (lsOf : Nat → List Wlabel),
          pst 0 = (List.range' 0 N).map boot ∧
          fab (dcnt GF' (linCand GF'.gfGd.gdG).cdTr 0) = d0 ∧
          (∀ i, GraphFetchSupply.itvOfL cohSrc (candExec (linCand GF'.gfGd.gdG)) lsOf 0 i = 0) ∧
          (∀ i, GraphFetchSupply.fiOfL (candExec (linCand GF'.gfGd.gdG)).exTr lsOf 0 i = false) ∧
          execProgOk'SC pstepEv pclsEv PfRunUnpinned.fokTriv
            (PfRunUnpinned.fcutEM2 cohSrc (candExec (linCand GF'.gfGd.gdG))
              (GraphFetchSupply.itvOfL cohSrc (candExec (linCand GF'.gfGd.gdG)) lsOf)
              (GraphFetchSupply.fiOfL (candExec (linCand GF'.gfGd.gdG)).exTr lsOf))
            pst (fun k => fab (dcnt GF' (linCand GF'.gfGd.gdG).cdTr k))
            (candExec (linCand GF'.gfGd.gdG))) := by
  intro hk hconf hc hres hdr hwio hprem hN
  obtain ⟨himg, hnh, fab, -, hzf⟩ := xv6ConfSForget boot d0 im nh GT hconf
  obtain ⟨pi, GF', hrr, hdev, hsr, himg', hscaT, hsup⟩ :=
    t2linSupplyFZ boot d0 fab (forgetF GT) N (himg ▸ hk fab) hc hzf hres hdr hwio hprem (by omega)
  exact ⟨fab, pi, GF', himg, hrr, hdev, hsr, himg'.trans himg, hscaT, hsup⟩

end Weak
