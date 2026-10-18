/-
Weak: **W11-F A12 (plan rev 53 REMAINING WORK row 6i) — `fetchProv` at the TAGGED graph**.  Lean-only,
no Rocq twin.  `PROGRESS-W11F-6i6m.md`.

G7's NAMED interface `fetchProv GD` (`Weak/G7Fetch.lean`, "every stored fetch pair is a `gzFetch`
item's edge") is NOT a consequence of the bundle: `xv6ConfS` (`gfexecConfZT`) states only
`GraphFetch.emFetchIn` — "F_em ⊆ gtFetch" — and nothing else (the cat model, `ioResidueGmo`,
`gdiskRead14`, `gfDevWIo`) reads the fragment, so a bundle of the theorem's quantifier may store
EXTRA pairs; nor does it survive `gdHull` (the hull keeps a pair iff both ENDS are kept, so an E2/E3
edge of a DROPPED fetch item whose source write is dropped stays, with no `gzFetch` item at the hull).
This file therefore never proves it at an arbitrary class graph; it proves it at the TRIMMED graph:

  §1  `CapFetchProv.provPair boot G p` — `p` is an edge of a ROW emission's fetch item (a `hartConff`
      witness of the row, `emZif`, `emFetchEdge`); `CapFetchProv.provAll boot GD` — every stored pair
      is one; **`CapFetchProv.fetchProvOfAll`** : `provAll → fetchProv`.
  §2  `CapFetchProv.trimF boot GF` — the same graph, deps and fabric, the fragment FILTERED by
      `provPair` (classical).  The fragment is proof data (riscv.cat has no fetch), so every class
      predicate but the fetch arm is unchanged (definitionally); `confTrim` (the Zifencei bundle
      passes: the witnesses' edges are provenant), **`provAllTrim`** (provenance at EVERY trimmed
      graph — at `trimF (forgetF GT)` and at every trimmed hull, nothing transported), and
      `racyDIOTrim` (the trimmed arm is a sub-relation).
  §3  the TRIMMED class kill **`CatLin.cycleKillCZT`** (`cycleKillCZC` with the class hypothesis
      `provAll` and the induction hypothesis over the trimmed hulls), its induction
      `CapFetchProv.t2linAuxCZT`, and the supply **`CapFetchProv.t2linSupplyCZT`** (the conclusion of
      `CatLin.t2linSupplyCZIO` for the UNTRIMMED graph, via `topoSupplyZIO` at `trimF GF`) with its
      tagged form **`CapFetchProv.t2linSupplyCZTtagged`** at `forgetF GT` (`xv6ConfS` + the tagged cat
      consistency).
  §4  **`CapFetchProv.g7FetchCertP`** — G7's fetch-entry certificate at a provenant graph, with the
      replay / after-direction premises asked ONLY at row-emission fetch items (G7's `hrep`/`hlate`
      quantify over every `gzFetch` item, which a fake item — any contributor set, a slot past the
      row's end — satisfies).

Retimes: not needed — the kill (and so the fetch-entry certificate) is stated at the class graph,
the normalization comes after it (`topoSupplyZIO`).

Spec (FIRST): RVWMO / riscv.cat have no fetch events; the fragment is the proof's record of the
Zifencei reading's edges (`gzFetch`, the trusted item, unchanged).  Trimming it changes no model text
and no conclusion (the trimmed graph has the same rows, gmo, deps and fabric): FAITHFUL.
Lean-only helpers are file-qualified (`CapFetchProv.*`).
-/
import Weak.G7Fetch
import Weak.GraphFetchHullZ

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. Provenance -/

/-- `p` is a fetch edge of a ROW emission's fetch item: a `hartConff` witness of row `i` whose fetch
items satisfy the Zifencei item (`emZif`). -/
def CapFetchProv.provPair (boot : Nat → Pexv6) (G : Gexec) (p : Geid × Geid) : Prop :=
  ∃ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
    G.gxProg[i]? = some row ∧ hartConff i row (boot i) dvi dvo tq em ∧
    GraphFetch.emZif G i em ∧ GraphFetch.emFetchEdge G i em p.1 p.2

/-- Every stored pair is a row emission's fetch edge. -/
def CapFetchProv.provAll (boot : Nat → Pexv6) (GD : Gdexec) : Prop :=
  ∀ x y, (x, y) ∈ GD.gdFetch → CapFetchProv.provPair boot GD.gdG (x, y)

/-- **`fetchProv` from row provenance.** -/
theorem CapFetchProv.fetchProvOfAll (boot : Nat → Pexv6) (GD : Gdexec) :
    CapFetchProv.provAll boot GD → fetchProv GD := by
  intro h
  refine fetchProvOfEm GD (fun x y hxy => ?_)
  obtain ⟨i, -, em, -, -, -, -, -, hz, he⟩ := h x y hxy
  exact ⟨i, em, hz, he⟩

/-! # 2. The trimmed graph -/

/-- The fragment filtered to the provenant pairs. -/
noncomputable def CapFetchProv.trimD (boot : Nat → Pexv6) (GD : Gdexec) : Gdexec :=
  ⟨GD.gdG, GD.gdDeps,
   GD.gdFetch.filter (fun p => @decide (CapFetchProv.provPair boot GD.gdG p) (Classical.propDecidable _))⟩

/-- The trimmed fabric bundle: same graph, deps and fabric. -/
noncomputable def CapFetchProv.trimF (boot : Nat → Pexv6) (GF : Gfexec) : Gfexec :=
  ⟨CapFetchProv.trimD boot GF.gfGd, GF.gfDev⟩

theorem CapFetchProv.memTrim (boot : Nat → Pexv6) (GD : Gdexec) (p : Geid × Geid) :
    p ∈ (CapFetchProv.trimD boot GD).gdFetch ↔
      p ∈ GD.gdFetch ∧ CapFetchProv.provPair boot GD.gdG p := by
  simp [CapFetchProv.trimD, List.mem_filter]

theorem CapFetchProv.trimG (boot : Nat → Pexv6) (GF : Gfexec) :
    (CapFetchProv.trimF boot GF).gfGd.gdG = GF.gfGd.gdG := rfl

theorem CapFetchProv.trimDeps (boot : Nat → Pexv6) (GF : Gfexec) :
    (CapFetchProv.trimF boot GF).gfGd.gdDeps = GF.gfGd.gdDeps := rfl

theorem CapFetchProv.trimDev (boot : Nat → Pexv6) (GF : Gfexec) :
    (CapFetchProv.trimF boot GF).gfDev = GF.gfDev := rfl

/-- **PROVENANCE AT EVERY TRIMMED GRAPH.** -/
theorem CapFetchProv.provAllTrim (boot : Nat → Pexv6) (GF : Gfexec) :
    CapFetchProv.provAll boot (CapFetchProv.trimF boot GF).gfGd :=
  fun x y h => ((CapFetchProv.memTrim boot GF.gfGd (x, y)).1 h).2

/-- … hence G7's interface there. -/
theorem CapFetchProv.fetchProvTrim (boot : Nat → Pexv6) (GF : Gfexec) :
    fetchProv (CapFetchProv.trimF boot GF).gfGd :=
  CapFetchProv.fetchProvOfAll boot _ (CapFetchProv.provAllTrim boot GF)

/-- The Zifencei bundle passes to the trimmed graph (the witnesses' edges are provenant). -/
theorem CapFetchProv.confTrim (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec) :
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    GraphFabConf.gfexecConfZF boot d0 fab (CapFetchProv.trimF boot GF) := by
  rintro ⟨h0, hnd, hbnd, hrows⟩
  refine ⟨h0, hnd, hbnd, fun i row hrow => ?_⟩
  obtain ⟨em, dvi, dvo, tq, hem, hiff, hpin, ⟨hz, hin⟩, hdep⟩ := hrows i row hrow
  refine ⟨em, dvi, dvo, tq, hem, hiff, hpin, ⟨hz, fun x y he => ?_⟩, hdep⟩
  exact (CapFetchProv.memTrim boot GF.gfGd (x, y)).2
    ⟨hin x y he, i, row, em, dvi, dvo, tq, hrow, hem, hz, he⟩

theorem CapFetchProv.catADTrim (boot : Nat → Pexv6) (GF : Gfexec) (ad : List (Geid × Geid)) :
    CatLin.rvwmoCatAD GF.gfGd ad → CatLin.rvwmoCatAD (CapFetchProv.trimF boot GF).gfGd ad :=
  fun h => h

theorem CapFetchProv.resTrim (boot : Nat → Pexv6) (GF : Gfexec) :
    ioResidueGmo GF → ioResidueGmo (CapFetchProv.trimF boot GF) :=
  fun h => h

theorem CapFetchProv.wioTrim (boot : Nat → Pexv6) (GF : Gfexec) :
    gfDevWIo GF → gfDevWIo (CapFetchProv.trimF boot GF) :=
  fun h => h

/-- The trimmed `racyDIO` is a sub-relation. -/
theorem CapFetchProv.racyDIOTrim (boot : Nat → Pexv6) (GF : Gfexec) (x y : Geid) :
    racyDIO (CapFetchProv.trimF boot GF) x y → racyDIO GF x y := by
  rintro (h | h | h | h | ⟨hm, h1, h2, h3⟩)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨((CapFetchProv.memTrim boot GF.gfGd (x, y)).1 hm).1, h1, h2, h3⟩)))

/-! # 3. The trimmed class kill, its induction and the supply -/

namespace CatLin

/-- **THE TRIMMED CLASS KILL** (`cycleKillCZC` at the provenant class): at a conformant Zifencei
graph whose stored fragment is provenant, every TRIMMED proper hull of which, cut in the class, is
already `racyDIO`-acyclic, there is no `racyDIO` cycle. -/
def cycleKillCZT (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im →
    rvwmoCatAD GF.gfGd ad →
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    CapFetchProv.provAll boot GF.gfGd →
    (∀ cs, properCutF GF cs → GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs →
      ∀ x, ¬ tc (racyDIO (CapFetchProv.trimF boot (gfHull GF cs))) x x) →
    ∀ x, tc (racyDIO GF) x x → False

end CatLin

/-- THE INDUCTION (`CatLin.t2linAuxCZ`'s mirror over the trimmed hulls). -/
theorem CapFetchProv.t2linAuxCZT (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) :
    CatLin.cycleKillCZT boot d0 fab im →
    ∀ (n : Nat) (GF : Gfexec) (ad : List (Geid × Geid)),
      (gevs' GF.gfGd.gdG).length ≤ n →
      GF.gfGd.gdG.gxImg = im →
      CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → CapFetchProv.provAll boot GF.gfGd →
      ∀ x, ¬ tc (racyDIO GF) x x := by
  intro hk n
  induction n with
  | zero =>
    intro GF ad hlen him hc hconf hres hdr hprov x hcyc
    refine hk GF ad him hc hconf hres hdr hprov ?_ x hcyc
    intro cs hpc _ y _
    have := gfHullEventsLt GF cs hpc
    omega
  | succ n ih =>
    intro GF ad hlen him hc hconf hres hdr hprov x hcyc
    refine hk GF ad him hc hconf hres hdr hprov ?_ x hcyc
    intro cs hpc hcl
    have hcore := CatLin.catADCore _ _ hc
    have hnd := hc.1.1
    have hconfH := GraphFetchHullZ.gfexecConfZFHull boot d0 fab GF cs hcore.1 hcore.2.1
      (properCutOk _ _ hpc.1) hpc.2 hconf hcl
    refine ih (CapFetchProv.trimF boot (gfHull GF cs)) (CatLin.adCut cs ad) ?_ him
      (CatLin.hullCatAD GF.gfGd ad cs hc (properCutOk _ _ hpc.1))
      (CapFetchProv.confTrim boot d0 fab _ hconfH)
      (ioResidueGmoHull GF cs hnd hpc.2 hres) (gdiskRead14Hull GF.gfGd.gdG cs hnd hdr)
      (CapFetchProv.provAllTrim boot _)
    have := gfHullEventsLt GF cs hpc
    show (gevs' (gfHull GF cs).gfGd.gdG).length ≤ n
    omega

/-- **ACYCLICITY AT THE TRIMMED GRAPH** of any class graph. -/
theorem CapFetchProv.acycT (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (ad : List (Geid × Geid)) :
    CatLin.cycleKillCZT boot d0 fab GF.gfGd.gdG.gxImg →
    CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ∀ x, ¬ tc (racyDIO (CapFetchProv.trimF boot GF)) x x :=
  fun hk hc hconf hres hdr =>
    CapFetchProv.t2linAuxCZT boot d0 fab _ hk _ (CapFetchProv.trimF boot GF) ad (Nat.le_refl _) rfl
      hc (CapFetchProv.confTrim boot d0 fab GF hconf) hres hdr (CapFetchProv.provAllTrim boot GF)

/-- **THE SUPPLY FROM THE TRIMMED KILL** — `CatLin.t2linSupplyCZIO`'s conclusion for the class graph
`GF` itself (the trimmed graph has the same rows, gmo, deps and fabric). -/
theorem CapFetchProv.t2linSupplyCZT (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (ad : List (Geid × Geid)) (N : Nat) :
    CatLin.cycleKillCZT boot d0 fab GF.gfGd.gdG.gxImg →
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
    topoSupplyZIO boot d0 fab (CapFetchProv.trimF boot GF) N (CatLin.catADCore _ _ hc)
      (CapFetchProv.acycT boot d0 fab GF ad hk hc hconf hres hdr)
      (CapFetchProv.confTrim boot d0 fab GF hconf) hwio hprem hN
  exact ⟨pi, GF', hrr, hdev, hsr, himg, hscaT, hdl, hord, hsup⟩

/-- **… at the TAGGED bundle** (`t2linSupplyZIO`'s shape, cat form): the published `xv6ConfS` and
the tagged cat consistency at `forgetF GT`. -/
theorem CapFetchProv.t2linSupplyCZTtagged (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GT : GfexecT) (N : Nat) :
    (∀ fab, CatLin.cycleKillCZT boot d0 fab im) →
    xv6ConfS boot d0 im nh GT →
    rvwmoCatConsistentT GT.gfGd →
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
  intro hk hconf hcat hres hdr hwio hprem hN
  obtain ⟨himg, hnh, fab, -, hzf⟩ := xv6ConfSForget boot d0 im nh GT hconf
  obtain ⟨pi, GF', hrr, hdev, hsr, himg', hscaT, hdl, hord, hsup⟩ :=
    CapFetchProv.t2linSupplyCZT boot d0 fab (forgetF GT) (gtAd GT.gfGd.gtG GT.gfGd.gtDeps) N
      (himg ▸ hk fab) (CatLin.catADOfCatT GT.gfGd hcat) hzf hres hdr hwio hprem (by omega)
  exact ⟨fab, pi, GF', himg, hrr, hdev, hsr, himg'.trans himg, hscaT, hdl, hord, hsup⟩

/-- The tagged instance of the provenance: at `trimF boot (forgetF GT)` (same graph as `forgetF GT`)
the bundle holds and G7's `fetchProv` holds. -/
theorem CapFetchProv.fetchProvTagged (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GT : GfexecT) :
    xv6ConfS boot d0 im nh GT →
    (CapFetchProv.trimF boot (forgetF GT)).gfGd.gdG = (forgetF GT).gfGd.gdG ∧
    (∃ fab, GraphFabConf.gfexecConfZF boot d0 fab (CapFetchProv.trimF boot (forgetF GT))) ∧
    CapFetchProv.provAll boot (CapFetchProv.trimF boot (forgetF GT)).gfGd ∧
    fetchProv (CapFetchProv.trimF boot (forgetF GT)).gfGd := by
  intro hconf
  obtain ⟨-, -, fab, -, hzf⟩ := xv6ConfSForget boot d0 im nh GT hconf
  exact ⟨rfl, ⟨fab, CapFetchProv.confTrim boot d0 fab _ hzf⟩, CapFetchProv.provAllTrim boot _,
    CapFetchProv.fetchProvTrim boot _⟩

/-! # 4. The fetch-entry certificate at a provenant graph -/

/-- **`g7FetchCert` at a provenant graph**: the replay state and the after-direction asked only at
the fetch items of ROW emissions (`hartConff` witnesses with `emZif`), at their real slots with the
emission's contributors. -/
theorem CapFetchProv.g7FetchCertP (boot : Nat → Pexv6) (GD : Gdexec) (ad : List (Geid × Geid))
    (X : Geid → Geid → Prop) (prev : Geid) (s : Seg) (hc : CatLin.rvwmoCatAD GD ad)
    (hx : gfetchE GD prev s.sgEntry) (hprov : CapFetchProv.provAll boot GD)
    (hrep : ∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool)
      (n : Nat) (base : Int) (tvs : List (Nat × BitVec 8)),
      GD.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetch.emZif GD.gdG i em → em.emItems[n]? = some (Wlabel.LIFetch base tvs, none) →
      fetchReplayOk GD.gdG i (GraphFetchSpike.emSlot em.emItems n) base tvs)
    (hlate : ∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool)
      (n : Nat) (base : Int) (tvs : List (Nat × BitVec 8)),
      GD.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetch.emZif GD.gdG i em → em.emItems[n]? = some (Wlabel.LIFetch base tvs, none) →
      fetchLateChained GD (GraphFetch.emContrib GD.gdG em i (GraphFetchSpike.emSlot em.emItems n)) i
        (GraphFetchSpike.emSlot em.emItems n) base tvs)
    (hrun : CatLin.segRunC GD s) (hm : gmem GD.gdG s.sgExit) : CatLin.CertC GD.gdG X prev s := by
  obtain ⟨i, row, em, dvi, dvo, tq, hrow, hem, hzem, n, base, tvs, hn, he⟩ := hprov _ _ hx.1
  have hz := hzem n base tvs hn
  rcases G7Fetch.fetchEdgeCases _ _ i _ base tvs _ _ he with h1 | h23
  · exact g7E1Chained GD ad X _ i _ base tvs prev s hc hz h1 hrun hm
  · by_cases hcut : gwix GD.gdG s.sgEntry ≤ gfcut GD.gdG i (GraphFetchSpike.emSlot em.emItems n)
    · exact (g7EarlyRefuted GD.gdG _ i _ base tvs prev s.sgEntry
        (hrep i row em dvi dvo tq n base tvs hrow hem hzem hn) h23 hcut).elim
    · exact chainHypsCertC GD ad X prev s hc
        (hlate i row em dvi dvo tq n base tvs hrow hem hzem hn prev s.sgEntry s h23 (by omega) rfl
          hrun)

end Weak
