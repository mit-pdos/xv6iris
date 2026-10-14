/-
Weak: **W5d-G G6-3b (3) [OWN.75] — the UNPINNED shaped supply on ONE trace, guard-free**
(plan `notes/weak-allocproc-plan.md` rev 52, §C top "W5d-G G6 — LAUNCH PLAN [rev 50]", paragraph
"G6-3 = W11 (iii)"; the G6-3 report's open question 3, option (a), FAITHFUL).  Lean-only.

G6-3's `topoSupplyZ` (`Weak/GraphFetchBlocks.lean`) and its consumers (`t2linSupplyFZ`,
`CatLin.t2linSupplyCZ`, `t2linSupplyZ`, `hullRunZ`, `hullRunOfKillIOZ`) supplied M2's conjunct on
the write-anchored trace `linCand` under two GUARDS, `trDevOrdered` and `candDiskLat` (both
theorems only of the (L)-anchored trace `linCandIO`).  With G5's cut chain re-proved on anchored
traces (`Weak/GraphFetchAnc.lean`) everything is now ONE trace, `linCandIO` of the normalized graph:

  §1  **`topoSupplyZIO`** — `topoSupplyZ`'s twin on `linCandIO`, with NO guard: consistency, rows,
      `candScaT` (`linCandScaTMinusA`), `candDiskLat` (`linCandDiskLatMinus`), `trDevOrdered`
      (`trDevOrderedOfPtraceIO`, from `gfDevWIo`) and M2's conjunct `execProgOk'STC … fcutEM2 …`
      (M2's text verbatim) with M2's boot values, all PROVED;
  §2  the guard-free consumers: `t2linSupplyFZIO`, `CatLin.t2linSupplyCZIO`, `t2linSupplyZIO`
      (the kill corollaries), `hullRunZIO`, `hullRunOfKillIOZIO` (a `RunDataZ` outright).

What W11-F consumes: these (§2) in place of G6-3's guarded statements; the premises are G6-3's
minus the guards, plus `gfDevWIo` where the guarded twin lacked it (the cat corollary).

**Note on (P1) (RETIRED, [OWN.86]).**  G6-3b found G6-3's (P1) (`emFenceCyc`, a cycle label inside
every `LFence false×4` block) FALSE on Sail emissions: the PLIC wire write (`pstepPlic`,
`WeakEvInst.lean`, a disjunct of `pstepHart`) may land between a `fence.i`'s announce and its
`Barrier_RISCV_i`, leaving the fence's block empty, while MachCSL's `fiArm` still raises `itv`
there.  The owner restated G1's `emFenceI` with the EMISSION-WIDE latest own cycle label
(Q-P1-FENCEI (b′); FAITHFUL on Sail, `GraphFetchSail.fenceISiteIff`); the supply's arm is that
label (`GraphFetchSupply.siteOfArm`), so the premise is gone (`PROGRESS-P1b.md`).

Spec marks.  No new trusted text (FAITHFUL).  Lean-only helpers are file-qualified
(`GraphFetchAncSupply.*`).
-/
import Weak.GraphFetchAnc

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. THE SUPPLY on the (L) trace -/

/-- A fabric member of a bundle is a labelled event (`WeakRvwmoLin2.devLbl` over the Zifencei
bundle, through a row renaming). -/
theorem GraphFetchAncSupply.devLblRen (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (GF : Gfexec) (pi : Nat → Nat) (G' : Gexec) :
    GraphFabConf.gfexecConfZF boot d0 fab GF → rowsRel pi GF.gfGd.gdG G' →
    ∀ e, e ∈ GF.gfDev → (gxLbl G' e).isSome = true := by
  intro hconf hrr e he
  obtain ⟨n, hn⟩ := elem_of_list_lookup_1 he
  obtain ⟨i, k⟩ := e
  obtain ⟨row, hrow, hlt⟩ := hconf.2.2.1 n i k hn
  rw [rowsRelLbl pi _ _ _ hrr, Option.isSome_map]
  simp only [gxLbl, hrow, Option.bind_some]
  exact lookup_lt_is_Some_2 hlt

/-- **`topoSupplyZIO` — THE UNPINNED, SHAPED SUPPLY ON ONE TRACE** (`topoSupplyZT`'s twin on
`linCandIO`, guard-free): a `racyDIO`-acyclic core graph whose Zifencei fabric bundle holds, whose
fabric members are writes / I/O events (`gfDevWIo`) and whose rows' emissions satisfy (P2)
normalizes to `GF'` (same fabric) with the residue and the disk-read anchors, whose (L) trace
`linCandIO` is consistent, carries the rows, is `candScaT` and `candDiskLat`, visits the fabric in
order, and is supplied by M2's conjunct `execProgOk'STC pstepEv pclsEv fokTriv cohSrc
(fcutEM2 cohSrc E itvOf fiOf)` along `fab ∘ dcnt GF'` with M2's boot values. -/
theorem topoSupplyZIO (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec) (N : Nat) :
    rvwmoCoreD GF.gfGd →
    (∀ x, ¬ tc (racyDIO GF) x x) →
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    gfDevWIo GF →
    (∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      GF.gfGd.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetchBlocks.emNoDangle em) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (pi : Nat → Nat) (GF' : Gfexec),
      rowsRel pi GF.gfGd.gdG GF'.gfGd.gdG ∧
      GF'.gfDev = GF.gfDev ∧
      rvwmoMinusDepsConsistent GF'.gfGd ∧
      grule14 GF'.gfGd.gdG ∧
      ioResidueGmo GF' ∧ gdiskRead14 GF'.gfGd.gdG ∧
      srvwmoConsistent (linCandIO GF'.gfGd.gdG) ∧
      (linCandIO GF'.gfGd.gdG).cdImg = GF.gfGd.gdG.gxImg ∧
      (∀ i, ((linCandIO GF'.gfGd.gdG).cdTr.filter (fun s => decide (s.esAg = i))).map
          (fun s => s.esLb) = ((GF.gfGd.gdG.gxProg[i]?).getD []).map (lblRen pi)) ∧
      candScaT cohSrc (linCandIO GF'.gfGd.gdG) ∧
      candDiskLat (linCandIO GF'.gfGd.gdG) ∧
      trDevOrdered GF' (linCandIO GF'.gfGd.gdG) ∧
      ∃ (pst : Nat → List Pexv6) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool),
        pst 0 = (List.range' 0 N).map boot ∧
        fab (dcnt GF' (linCandIO GF'.gfGd.gdG).cdTr 0) = d0 ∧
        execProgOk'STC pstepEv pclsEv PfRunUnpinned.fokTriv cohSrc
          (PfRunUnpinned.fcutEM2 cohSrc (candExec (linCandIO GF'.gfGd.gdG)) itvOf fiOf) pst
          (fun k => fab (dcnt GF' (linCandIO GF'.gfGd.gdG).cdTr k))
          (candExec (linCandIO GF'.gfGd.gdG)) ∧
        (∀ i, itvOf 0 i = 0) ∧ (∀ i, fiOf 0 i = false) := by
  intro hcore hacy hconf hwio hprem hN
  have hconf0 := hconf
  obtain ⟨h0, hnd, -, hc⟩ := hconf
  -- the bundle's emissions, chosen
  have hch : ∀ i, i < GF.gfGd.gdG.gxProg.length →
      ∃ a : Hemission × (Nat → Efab) × (Nat → Efab) × (Nat → Bool), ∀ row,
        GF.gfGd.gdG.gxProg[i]? = some row →
        hartConff i row (boot i) a.2.1 a.2.2.1 a.2.2.2 a.1 ∧
        (∀ k : Nat, k < row.length →
          ((i, k) ∈ GF.gfDev ↔ (gisIo GF.gfGd.gdG (i, k) = true ∨ a.2.1 k ≠ a.2.2.1 k ∨
            a.2.2.2 k = true))) ∧
        (∀ (k n : Nat), GF.gfDev[n]? = some (i, k) → a.2.1 k = fab n ∧ a.2.2.1 k = fab (n + 1)) ∧
        (emZifencei GF.gfGd.gdG i a.1 ∧ GraphFetch.emFetchIn GF.gfGd i a.1) := by
    intro i hi
    obtain ⟨row, hrow⟩ : ∃ row, GF.gfGd.gdG.gxProg[i]? = some row :=
      someOfIsSome (lookup_lt_is_Some_2 hi)
    obtain ⟨em, dvi, dvo, tq, hem, hiff, hpin, hfz, -⟩ := hc i row hrow
    refine ⟨(em, dvi, dvo, tq), fun row' hrow' => ?_⟩
    rw [hrow, Option.some.injEq] at hrow'
    subst hrow'
    exact ⟨hem, hiff, hpin, hfz⟩
  obtain ⟨E, hE⟩ := natBoundedChoice
    ((⟨[], boot 0⟩ : Hemission), fun _ => d0, fun _ => d0, fun _ => false) _ _ hch
  let emF : Nat → Hemission := fun i =>
    if i < GF.gfGd.gdG.gxProg.length then (E i).1 else ⟨[], boot i⟩
  have hrowOf : ∀ i, i < GF.gfGd.gdG.gxProg.length → ∃ row, GF.gfGd.gdG.gxProg[i]? = some row :=
    fun i hi => someOfIsSome (lookup_lt_is_Some_2 hi)
  have hin : ∀ i, GraphFetch.emFetchIn GF.gfGd i (emF i) := by
    intro i
    by_cases hi : i < GF.gfGd.gdG.gxProg.length
    · obtain ⟨row, hrow⟩ := hrowOf i hi
      simp only [emF, if_pos hi]
      exact (hE i hi row hrow).2.2.2.2
    · simp only [emF, if_neg hi]
      exact GraphFetchBlocks.emptyFetchIn _ _ _
  have hz : ∀ i, GraphFetch.emZif GF.gfGd.gdG i (emF i) := by
    intro i
    by_cases hi : i < GF.gfGd.gdG.gxProg.length
    · obtain ⟨row, hrow⟩ := hrowOf i hi
      simp only [emF, if_pos hi]
      exact (hE i hi row hrow).2.2.2.1
    · simp only [emF, if_neg hi]
      exact GraphFetchBlocks.emptyZif _ _ _
  obtain ⟨GD', pi, hc', h14, hrr, -, -, -, hres', hdr', hsup⟩ :=
    GraphFetchAnc.normalizeFetchSupplyIO GF emF hcore hacy hin hz
  let GF' : Gfexec := ⟨GD', GF.gfDev⟩
  have hwf : gwf GD'.gdG := hc'.1.1
  have hok : ancOk GD'.gdG (gisAnc GD'.gdG) := ancOkIO GF' h14 hres' hdr'
  have hprog : ∀ i : Nat, GD'.gdG.gxProg[i]? =
      (GF.gfGd.gdG.gxProg[i]?).map (fun row : List Lbl => row.map (lblRen pi)) := by
    intro i
    rw [hrr.2.1, List.getElem?_map]
  obtain ⟨hsr, -, hrowL, -⟩ := rule14LinearizationIO GF' hc'.1 h14 hres' hdr'
  -- the per-hart block data at the normalized graph
  have hblkData : ∀ i, i < N → ∃ a : (Nat → Pexv6) × (Nat → List Wlabel), a.1 0 = boot i ∧
      ∀ n lb, ((GD'.gdG.gxProg[i]?).getD [])[n]? = some lb →
        GraphFetch.emBlockF GD'.gdG (emRen pi (emF i)) i n a.2 ∧
        (∀ m, GF.gfDev[m]? = some (i, n) →
          GraphFetchBlocks.hblkS (fab m) (fab (m + 1)) (rowWs ((GD'.gdG.gxProg[i]?).getD []) n) lb
            (a.2 n) (a.1 n) (a.1 (n + 1))) ∧
        ((i, n) ∉ GF.gfDev → ∀ d,
          GraphFetchBlocks.hblkS d d (rowWs ((GD'.gdG.gxProg[i]?).getD []) n) lb (a.2 n) (a.1 n)
            (a.1 (n + 1))) := by
    intro i hiN
    by_cases hi : i < GF.gfGd.gdG.gxProg.length
    · obtain ⟨row, hrow0⟩ := hrowOf i hi
      obtain ⟨hem, hiff, hpin, -⟩ := hE i hi row hrow0
      have hemF : emF i = (E i).1 := by simp only [emF, if_pos hi]
      have hndg := hprem i row (E i).1 _ _ _ hrow0 hem
      have hrowG : GD'.gdG.gxProg[i]? = some (row.map (lblRen pi)) := by
        rw [hprog, hrow0]; rfl
      obtain ⟨f, g, hf0, hf⟩ := GraphFetchBlocks.rowBlocks GD'.gdG i (row.map (lblRen pi)) (boot i)
        _ _ _ (emRen pi (E i).1) GF.gfDev fab (hartConffRen pi i row (boot i) _ _ _ _ hem)
        (GraphFetchBlocks.emNoDangleRen pi _ hndg)
        (fun n hn hnin => by
          cases htq : (E i).2.2.2 n with
          | false => rfl
          | true =>
            rw [List.length_map] at hn
            exact absurd ((hiff n hn).2 (Or.inr (Or.inr htq))) hnin)
        hpin
        (fun n lb hn => by
          unfold glbl gxLbl
          rw [hrowG]
          simp [hn])
      refine ⟨(f, g), hf0, fun n lb hn => ?_⟩
      rw [hrowG] at hn ⊢
      rw [hemF]
      exact hf n lb hn
    · refine ⟨(fun _ => boot i, fun _ => []), rfl, fun n lb hn => ?_⟩
      have hnone : GF.gfGd.gdG.gxProg[i]? = none := List.getElem?_eq_none (by omega)
      rw [hprog, hnone] at hn
      simp at hn
  obtain ⟨Fx, hFx⟩ := natBoundedChoice ((fun _ => boot 0), (fun _ => [])) _ N hblkData
  let lsOf : Nat → List Wlabel := fun K =>
    match (linCandIO GD'.gdG).cdTr[K]? with
    | some s => (Fx s.esAg).2 (tcnt s.esAg ((linCandIO GD'.gdG).cdTr.take K))
    | none => []
  have hlsOf : ∀ K s, (linCandIO GD'.gdG).cdTr[K]? = some s →
      lsOf K = (Fx s.esAg).2 (tcnt s.esAg ((linCandIO GD'.gdG).cdTr.take K)) := by
    intro K s hs
    simp only [lsOf, hs]
  have hblkF : ∀ K i k, (glinEidsIO GD'.gdG)[K]? = some (i, k) →
      lsOf K = (Fx i).2 k ∧ GraphFetch.emBlockF GD'.gdG (emRen pi (emF i)) i k (Fx i).2 := by
    intro K i k he
    have hs := linTrALookup GD'.gdG (gisAnc GD'.gdG) K (i, k) he
    have hcnt : tcnt i ((linCandIO GD'.gdG).cdTr.take K) = k :=
      GraphFetchAnc.ownCountA GD'.gdG (gisAnc GD'.gdG) hwf hok K (i, k) he
    have hl := GraphFetchBlocks.rowLbl GD'.gdG i k _
      (linALbl GD'.gdG (gisAnc GD'.gdG) hwf hok K (i, k) he)
    have hiN : i < N := by
      by_cases h : i < GD'.gdG.gxProg.length
      · have := rowsRelNharts pi _ _ hrr
        omega
      · have hnone : GD'.gdG.gxProg[i]? = none := List.getElem?_eq_none (by omega)
        rw [hnone] at hl
        simp at hl
    refine ⟨?_, ((hFx i hiN).2 k _ hl).1⟩
    rw [hlsOf K _ hs]
    simp only [glinStep] at hcnt ⊢
    rw [hcnt]
  obtain ⟨hi0, hf0', hcut⟩ := hsup lsOf (fun i => (Fx i).2) hblkF
  have hscaT := linCandScaTMinusA GD'.gdG (gisAnc GD'.gdG) hc'.1 hok
  have hdl : candDiskLat (linCandIO GD'.gdG) := linCandDiskLatMinus GF' hc'.1 h14 hres' hdr'
  have hwio' : gfDevWIo GF' := gfDevWIoRen pi GF GF' hrr rfl hwio
  have hord : trDevOrdered GF' (linCandIO GD'.gdG) :=
    trDevOrderedOfPtraceIO GF' (glinEidsIO GD'.gdG) (glinIOPtraceExtIO GF' hc'.1 h14 hres' hdr') hnd
      (GraphFetchAncSupply.devLblRen boot d0 fab GF pi GD'.gdG hconf0 hrr)
      (gfDevGmoOfRes GF' hres' hwio') hwio'
  have hrowsIO : ∀ i, ((linCandIO GD'.gdG).cdTr.filter (fun s => decide (s.esAg = i))).map
      (fun s => s.esLb) = (GD'.gdG.gxProg[i]?).getD [] := hrowL
  obtain ⟨pst, hpst0, hprg⟩ := GraphFetchBlocks.supplyOfFconfZ (linCandIO GD'.gdG) boot fab
    GF' (fun i => (GD'.gdG.gxProg[i]?).getD []) N Fx _ hrowsIO
    (fun i hi => by
      rw [List.getElem?_eq_none (by have := rowsRelNharts pi _ _ hrr; omega)]; rfl)
    (fun i hi => ⟨(hFx i hi).1, fun n lb hn => ⟨((hFx i hi).2 n lb hn).2.1, ((hFx i hi).2 n lb hn).2.2⟩⟩)
    hord
    (fun k s hs => by rw [← hlsOf k s hs]; exact hcut k s hs)
    (fun k s hs aq base ts vs hlb => scaOkTSca _ _ _ _ _ _ (hscaT k s hs aq base ts vs hlb))
  refine ⟨pi, GF', hrr, rfl, hc', h14, hres', hdr', hsr, ?_, fun i => ?_, hscaT, hdl, hord,
    pst, _, _, hpst0, h0, GraphFetchBlocks.stcOfSC _ _ _ _ _ _ _ _ hprg hscaT hdl, hi0, hf0'⟩
  · exact rowsRelImg pi _ _ hrr
  · rw [hrowsIO i, hprog]
    cases GF.gfGd.gdG.gxProg[i]? <;> rfl

/-! # 2. The guard-free consumers -/

/-- **`t2linSupplyFZ` on one trace** (guard-free): under the kill, a conformant Zifencei graph
with `gfDevWIo` whose emissions satisfy (P2) is supplied on `linCandIO` of its
normalization by M2's conjunct, with `candDiskLat` and `trDevOrdered` proved. -/
theorem t2linSupplyFZIO (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
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
      srvwmoConsistent (linCandIO GF'.gfGd.gdG) ∧
      (linCandIO GF'.gfGd.gdG).cdImg = GF.gfGd.gdG.gxImg ∧
      candScaT cohSrc (linCandIO GF'.gfGd.gdG) ∧ candDiskLat (linCandIO GF'.gfGd.gdG) ∧
      trDevOrdered GF' (linCandIO GF'.gfGd.gdG) ∧
      ∃ (pst : Nat → List Pexv6) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool),
        pst 0 = (List.range' 0 N).map boot ∧
        fab (dcnt GF' (linCandIO GF'.gfGd.gdG).cdTr 0) = d0 ∧
        execProgOk'STC pstepEv pclsEv PfRunUnpinned.fokTriv cohSrc
          (PfRunUnpinned.fcutEM2 cohSrc (candExec (linCandIO GF'.gfGd.gdG)) itvOf fiOf) pst
          (fun k => fab (dcnt GF' (linCandIO GF'.gfGd.gdG).cdTr k))
          (candExec (linCandIO GF'.gfGd.gdG)) ∧
        (∀ i, itvOf 0 i = 0) ∧ (∀ i, fiOf 0 i = false) := by
  intro hk hc hconf hres hdr hwio hprem hN
  obtain ⟨pi, GF', hrr, hdev, -, -, -, -, hsr, himg, -, hscaT, hdl, hord, hsup⟩ :=
    topoSupplyZIO boot d0 fab GF N hc (t2linIOZ boot d0 fab _ hk GF rfl hc hconf hres hdr hwio)
      hconf hwio hprem hN
  exact ⟨pi, GF', hrr, hdev, hsr, himg, hscaT, hdl, hord, hsup⟩

/-- **The cat corollary on one trace** (`CatLin.t2linSupplyCZ`'s guard-free twin; `gfDevWIo` is
the new premise `trDevOrdered` needs). -/
theorem CatLin.t2linSupplyCZIO (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (ad : List (Geid × Geid)) (N : Nat) :
    CatLin.cycleKillCZ boot d0 fab GF.gfGd.gdG.gxImg →
    CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF →
    (∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      GF.gfGd.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetchBlocks.emNoDangle em) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (pi : Nat → Nat) (GF' : Gfexec),
      rowsRel pi GF.gfGd.gdG GF'.gfGd.gdG ∧ GF'.gfDev = GF.gfDev ∧
      srvwmoConsistent (linCandIO GF'.gfGd.gdG) ∧
      (linCandIO GF'.gfGd.gdG).cdImg = GF.gfGd.gdG.gxImg ∧
      candScaT cohSrc (linCandIO GF'.gfGd.gdG) ∧ candDiskLat (linCandIO GF'.gfGd.gdG) ∧
      trDevOrdered GF' (linCandIO GF'.gfGd.gdG) ∧
      ∃ (pst : Nat → List Pexv6) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool),
        pst 0 = (List.range' 0 N).map boot ∧
        fab (dcnt GF' (linCandIO GF'.gfGd.gdG).cdTr 0) = d0 ∧
        execProgOk'STC pstepEv pclsEv PfRunUnpinned.fokTriv cohSrc
          (PfRunUnpinned.fcutEM2 cohSrc (candExec (linCandIO GF'.gfGd.gdG)) itvOf fiOf) pst
          (fun k => fab (dcnt GF' (linCandIO GF'.gfGd.gdG).cdTr k))
          (candExec (linCandIO GF'.gfGd.gdG)) ∧
        (∀ i, itvOf 0 i = 0) ∧ (∀ i, fiOf 0 i = false) := by
  intro hk hc hconf hres hdr hwio hprem hN
  obtain ⟨pi, GF', hrr, hdev, -, -, -, -, hsr, himg, -, hscaT, hdl, hord, hsup⟩ :=
    topoSupplyZIO boot d0 fab GF N (CatLin.catADCore _ _ hc)
      (CatLin.t2linOfCycleKillCZ boot d0 fab _ hk GF ad rfl hc hconf hres hdr) hconf hwio hprem hN
  exact ⟨pi, GF', hrr, hdev, hsr, himg, hscaT, hdl, hord, hsup⟩

/-- **`t2linSupplyZ` on one trace** (guard-free): over the tagged Zifencei bundle `xv6ConfS`. -/
theorem t2linSupplyZIO (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GT : GfexecT)
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
      srvwmoConsistent (linCandIO GF'.gfGd.gdG) ∧
      (linCandIO GF'.gfGd.gdG).cdImg = im ∧
      candScaT cohSrc (linCandIO GF'.gfGd.gdG) ∧ candDiskLat (linCandIO GF'.gfGd.gdG) ∧
      trDevOrdered GF' (linCandIO GF'.gfGd.gdG) ∧
      ∃ (pst : Nat → List Pexv6) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool),
        pst 0 = (List.range' 0 N).map boot ∧
        fab (dcnt GF' (linCandIO GF'.gfGd.gdG).cdTr 0) = d0 ∧
        execProgOk'STC pstepEv pclsEv PfRunUnpinned.fokTriv cohSrc
          (PfRunUnpinned.fcutEM2 cohSrc (candExec (linCandIO GF'.gfGd.gdG)) itvOf fiOf) pst
          (fun k => fab (dcnt GF' (linCandIO GF'.gfGd.gdG).cdTr k))
          (candExec (linCandIO GF'.gfGd.gdG)) ∧
        (∀ i, itvOf 0 i = 0) ∧ (∀ i, fiOf 0 i = false) := by
  intro hk hconf hc hres hdr hwio hprem hN
  obtain ⟨himg, hnh, fab, -, hzf⟩ := xv6ConfSForget boot d0 im nh GT hconf
  obtain ⟨pi, GF', hrr, hdev, hsr, himg', hscaT, hdl, hord, hsup⟩ :=
    t2linSupplyFZIO boot d0 fab (forgetF GT) N (himg ▸ hk fab) hc hzf hres hdr hwio hprem
      (by omega)
  exact ⟨fab, pi, GF', himg, hrr, hdev, hsr, himg'.trans himg, hscaT, hdl, hord, hsup⟩

/-- **`hullRunZ` on one trace** (guard-free): a `racyDIO`-acyclic hull carrying the Zifencei bundle
runs — a `RunDataZ` outright, on the normalized hull's `linCandIO`, with `trDevOrdered`. -/
theorem hullRunZIO (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (cs : List Nat) (N : Nat) :
    rvwmoCoreD GF.gfGd →
    hullOk GF.gfGd.gdG cs →
    GraphFabConf.gfexecConfZF boot d0 fab (gfHull GF cs) →
    gfDevWIo GF →
    (∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      (gfHull GF cs).gfGd.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetchBlocks.emNoDangle em) →
    (∀ x, ¬ tc (racyDIO (gfHull GF cs)) x x) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (c : Cand) (pst : Nat → List Pexv6) (pi : Nat → Nat) (GF' : Gfexec),
      RunDataZ boot d0 N GF.gfGd.gdG c pst (fun k => fab (dcnt GF' c.cdTr k)) ∧
      c = linCandIO GF'.gfGd.gdG ∧
      GF'.gfDev = (gfHull GF cs).gfDev ∧
      candDiskLat c ∧ trDevOrdered GF' c ∧
      (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) =
        (((gxHull GF.gfGd.gdG cs).gxProg[i]?).getD []).map (lblRen pi)) := by
  intro hcore hok hconf hwio hprem hacy hN
  have hNh : (gfHull GF cs).gfGd.gdG.gxProg.length ≤ N := by
    have := gxhNharts GF.gfGd.gdG cs
    change (gxHull GF.gfGd.gdG cs).gxProg.length ≤ N
    omega
  obtain ⟨pi, GF', -, hdev, -, -, -, -, hsr, himg, hrow, hscaT, hdl, hord, pst, itvOf, fiOf,
      hpst0, hd0, hprg, hi0, hf0⟩ :=
    topoSupplyZIO boot d0 fab (gfHull GF cs) N (hullCoreD GF.gfGd cs hcore hok) hacy hconf
      (gfDevWIoHull GF cs hwio) hprem hNh
  exact ⟨linCandIO GF'.gfGd.gdG, pst, pi, GF',
    ⟨hsr, himg.trans (gxhImg _ _), hpst0, hd0, hscaT, ⟨itvOf, fiOf, hi0, hf0, hprg⟩⟩,
    rfl, hdev, hdl, hord, hrow⟩

/-- **`hullRunOfKillIOZ` on one trace** (guard-free). -/
theorem hullRunOfKillIOZIO (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (cs : List Nat) (N : Nat) :
    cycleKillIOZ boot d0 fab GF.gfGd.gdG.gxImg →
    rvwmoMinusDepsConsistent GF.gfGd →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF →
    properCutF GF cs →
    GraphFabConf.gfexecConfZF boot d0 fab (gfHull GF cs) →
    (∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      (gfHull GF cs).gfGd.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetchBlocks.emNoDangle em) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (c : Cand) (pst : Nat → List Pexv6) (pi : Nat → Nat) (GF' : Gfexec),
      RunDataZ boot d0 N GF.gfGd.gdG c pst (fun k => fab (dcnt GF' c.cdTr k)) ∧
      c = linCandIO GF'.gfGd.gdG ∧
      GF'.gfDev = (gfHull GF cs).gfDev ∧
      candDiskLat c ∧ trDevOrdered GF' c ∧
      (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) =
        (((gxHull GF.gfGd.gdG cs).gxProg[i]?).getD []).map (lblRen pi)) := by
  intro hk hc hres hdr hwio hpc hconf hprem hN
  obtain ⟨hc', hres', hdr', hwio'⟩ := GraphFetchLinInd.hullPremisesZ GF cs hc hres hdr hwio hpc
  exact hullRunZIO boot d0 fab GF cs N hc (properCutOk _ _ hpc.1) hconf hwio hprem
    (t2linIOZ boot d0 fab _ hk (gfHull GF cs) rfl hc' hconf hres' hdr' hwio') hN

end Weak
