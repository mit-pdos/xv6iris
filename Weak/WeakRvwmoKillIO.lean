/-
Weak: **W13 (K) — the kill and the normalization over the I/O-extended racy relation**
(plan `notes/weak-allocproc-plan.md` §C W13 (K), §C top "SECOND LAUNCH SET"; Lean-only, no Rocq
twin).

  §1  THE RELATION.  `racyDIO GF := racyD ∪ ioResidue ∪ gmo|IO ∪` the `gdiskRead14` pairs
      (`racyDX GF.gfGd (ioExtra GF)`, `WeakRvwmoAcyc`): `ioExtra` = the residue (R1)–(R3)
      (`GraphFabResidue`, (R3)'s fabric arm over `gmem` members since W13 (R3′)), `gmoIo` (the
      memory order among I/O events) and `gdiskRd` (a non-I/O memory access po-before a disk-row
      RAM read — G3-Q (a″), W13 (L)'s anchor class).  Decidable (`racyDIODec`).
  §2  EVERY EXTRA ARM IS GMO-FORWARD in the ORIGINAL graph under the trusted item and the
      disk-read premise (`ioExtraGmo`) — "(T) directly"; endpoints are memory events
      (`ioExtraGmem`).
  §3  TRANSPORT along a re-timing (`rowsRel`): the classifiers and `ioResidue` are blind to the
      read renaming (`ioResidueRen`), and along a hull: the residue / `gdiskRead14` / `gfDevWIo`
      of a `dclosed` hull follow from the graph's (`ioResidueGmoHull`, `gdiskRead14Hull`,
      `gfDevWIoHull`).
  §4  THE NORMALIZATION.  `normalizeOfAcyclicIO`: a `racyDIO`-acyclic core graph re-times
      (`WeakRvwmoTopo.normalizeOfAcyclicX`) to an RVWMO⁻ + rule-14 graph that KEEPS the
      residue (`ioResidueGmo`), the I/O events' relative positions (`gmoIo`) and the disk-read
      anchors (`gdiskRead14`) — exactly the premises of W13 (L)'s `fconfTraceRealizeIO`, which
      it therefore SUPPLIES (`gdiskRead14` via `racyDIO`, plan §C top).  `fconfRealizeIO`: the
      normalized graph's anchored rank trace `glinEidsIO` realizes it along the fabric
      (a corollary of `rule14LinearizationIO`).
  §5  THE KILL INTERFACE AND THE ROUTE.  `cycleKillIO` (the `cycleKill`/`cycleKillF` mirror over
      `racyDIO`, at the bundle `gfexecConfIO` with the residue, `gdiskRead14` and `gfDevWIo`);
      the induction `t2linAuxIO`/`t2linIO` (hulls keep every premise); `hullRunIO` — Glue's
      `hullRun` at the fabric (`RunData` with the fabric trace `fab ∘ dcnt`); `hullRunOfKillIO`
      — `cycleKillIO` THROUGH `hullRunIO` (every proper hull of a conformant graph runs);
      `t2linRealizeIO` — the whole graph runs.
  §6  THE ARMS.  `ioCross := gcrossE ∪ ioExtra` (every extra arm, same-row or not, joins the
      CROSS order: all are gmo-forward); `racyDIOSplit`, `cycleSegmentsIO` (a `racyDIO` cycle is
      a raw chain over `ioCross`, `CatLin.cycleSegmentsX`), `cycleKillIOC` (the cat kill at
      `X := ioCross ⊇ gmo|IO`, `CatLin.cycleKillArmsX`) — RVWMO⁻ graphs enter through
      `CatLin.catADOfMinus`; `ioEntryRelGmo` (an I/O entry of a critical section is gmo-before
      the release, residue (R2) — the second premise of `WeakRvwmoKillArms.csChainedMem`).
  §7  `ioSegPinned` (Claim L-IO of the census, plan §C W13 R5): a segment run THROUGH an I/O
      event is pinned — `entry <gmo exit` — under its two checks: (i)
      `WeakRvwmoKillIO.noReadEdgeOutsideGmo` (no same-row edge INTO a non-write outside gmo),
      PROVED for the RVWMO⁻ chain's `rsame` (`rsameNoReadEdge`); (ii) the lock-word discipline —
      see the docstring of `ioSegPinned`.
  §8  NON-VACUITY: `w13fIoRacyDIOAcyclic` (the re-encoded `w13f`, a NON-EMPTY fabric, is
      `racyDIO`-acyclic — `normalizeOfAcyclicIO` applies) and `w13fIoRevRacyDIOCycle` (with the
      fabric order reversed against gmo, `racyDIO` has a two-cycle: the relation bites).

**Deviations from the plan text.**  (1) FILES: `racyDIO` cannot live at `WeakRvwmoAcyc.lean:200`
(its arms name `Gfexec`/`ioResidue`, downstream of `Acyc`): `Acyc` gains the parametric
`racyDX`, `Topo` the parametric `topoExistsX`/`normalizeOfAcyclicX`, and the I/O instance is this
NEW leaf (`hullRun`'s fabric twin `hullRunIO` is here too, not in `Glue`, which stays the
constant-fabric chain).  (2) `WeakRvwmoHull.gdHull` is UNCHANGED: it already keeps the cut rows'
I/O events (labels are cut, not filtered by kind) and `gfHull` already filters `gfDev`; the hull
facts the kill needs are §3 here.  (3) The same-row residue arms (R1)/(R2)/(R2′)/(R3)-same-row and
the disk-read pairs go into the CROSS order `ioCross`, not into the segment relation: they are all
gmo-forward, so the raw chain composes in gmo unchanged (plan: "KillArms' chain composes in
`gmoLt` AS TODAY") and `CatLin`'s kit is reused as is.  (4) The induction is stated over RVWMO⁻
(`cycleKill`/`cycleKillF`'s model): `gfexecConfHull` (`WeakRvwmoFabInd`, not this item's file)
takes `gfexecConsistent`, which a cat graph lacks; `hullRunIO`/`fconfRealizeIO` themselves take
only the core `rvwmoCoreD` and the hull's conformance, so a cat induction needs only that hull
fact.

**Spec standing.**  No new trusted text: `racyDIO` is a proof device (an acyclicity premise), its
extra arms are the trusted residue (`ioResidueGmo`, §A(6)), the order gmo already has on I/O
events, and the NAMED (not trusted) premise `gdiskRead14`.
-/
import Weak.WeakRvwmoLin2
import Weak.CatLin
import Weak.WeakRvwmoGlue

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! # 1. THE RELATION -/

/-- gmo restricted to I/O events ("gmo|IO"). -/
def gmoIo (G : Gexec) (x y : Geid) : Prop :=
  gisIo G x = true ∧ gisIo G y = true ∧ gmoLt G x y

/-- The disk-read anchor pairs (`gdiskRead14`'s antecedent): a non-I/O memory access po-before a
disk-row RAM read. -/
def gdiskRd (G : Gexec) (e a : Geid) : Prop :=
  WeakRvwmoGraph.gpo G e a ∧ gmem G e ∧ gisIo G e = false ∧ gisR G a = true ∧ a.1 = NCPU

/-- THE EXTRA ARMS: the residue, gmo|IO, the disk-read pairs. -/
def ioExtra (GF : Gfexec) (x y : Geid) : Prop :=
  ioResidue GF x y ∨ gmoIo GF.gfGd.gdG x y ∨ gdiskRd GF.gfGd.gdG x y

/-- **`racyDIO := racyD ∪ ioResidue ∪ gmo|IO ∪` the `gdiskRead14` pairs.** -/
def racyDIO (GF : Gfexec) (x y : Geid) : Prop :=
  racyDX GF.gfGd (ioExtra GF) x y

instance WeakRvwmoKillIO.gfBeforeDec (GF : Gfexec) (x y : Geid) : Decidable (gfBefore GF x y) :=
  decidable_of_iff (∃ i ∈ List.range GF.gfDev.length, ∃ j ∈ List.range GF.gfDev.length,
      GF.gfDev[i]? = some x ∧ GF.gfDev[j]? = some y ∧ i < j)
    ⟨fun ⟨i, _, j, _, h⟩ => ⟨i, j, h⟩,
     fun ⟨i, j, hi, hj, hij⟩ => ⟨i, List.mem_range.2 (lookup_lt_Some hi), j,
       List.mem_range.2 (lookup_lt_Some hj), hi, hj, hij⟩⟩

instance WeakRvwmoKillIO.ioResidueDec (GF : Gfexec) (x y : Geid) :
    Decidable (ioResidue GF x y) := by
  unfold ioResidue; infer_instance

instance gmoIoDec (G : Gexec) (x y : Geid) : Decidable (gmoIo G x y) := by
  unfold gmoIo; infer_instance

instance gdiskRdDec (G : Gexec) (x y : Geid) : Decidable (gdiskRd G x y) := by
  unfold gdiskRd; infer_instance

instance ioExtraDec (GF : Gfexec) (x y : Geid) : Decidable (ioExtra GF x y) := by
  unfold ioExtra; infer_instance

instance racyDIODec (GF : Gfexec) (x y : Geid) : Decidable (racyDIO GF x y) := by
  unfold racyDIO racyDX; infer_instance

/-- `racyD` is inside `racyDIO`. -/
theorem racyDIOOfRacyD (GF : Gfexec) (x y : Geid) : racyD GF.gfGd x y → racyDIO GF x y :=
  Or.inl

/-! # 2. Endpoints and gmo-forwardness -/

/-- (Lean-only) a RAM read is a memory event. -/
theorem WeakRvwmoKillIO.gisRGmem (G : Gexec) (e : Geid) : gisR G e = true → gmem G e := by
  unfold gisR
  rcases h : gxLbl G e with _ | l
  · simp
  · intro hr
    exact ⟨l, h, by unfold lbIsMem; simp [hr]⟩

theorem ioExtraGmem (GF : Gfexec) (x y : Geid) :
    ioExtra GF x y → gmem GF.gfGd.gdG x ∧ gmem GF.gfGd.gdG y := by
  rintro ((⟨-, hm, -, hy⟩ | ⟨-, hx, hy⟩ | ⟨-, hx, hy, -⟩ | ⟨hx, hy, -⟩ | ⟨hx, hy, -⟩) |
    ⟨hx, hy, -⟩ | ⟨-, hm, -, hr, -⟩)
  · exact ⟨hm, GraphFabResidue.gisIoGmem _ _ hy⟩
  · exact ⟨GraphFabResidue.gisIoGmem _ _ hx, WeakRvwmoAcyc.gisWGmem _ _ hy⟩
  · exact ⟨GraphFabResidue.gisIoGmem _ _ hx, WeakRvwmoKillIO.gisRGmem _ _ hy⟩
  · exact ⟨GraphFabResidue.gisIoGmem _ _ hx, GraphFabResidue.gisIoGmem _ _ hy⟩
  · exact ⟨hx, hy⟩
  · exact ⟨GraphFabResidue.gisIoGmem _ _ hx, GraphFabResidue.gisIoGmem _ _ hy⟩
  · exact ⟨hm, WeakRvwmoKillIO.gisRGmem _ _ hr⟩

/-- Every extra arm is gmo-forward: the residue by the trusted item, gmo|IO by definition, the
disk-read pairs by `gdiskRead14`. -/
theorem ioExtraGmo (GF : Gfexec) :
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ∀ x y, ioExtra GF x y → gmoLt GF.gfGd.gdG x y := by
  rintro hres hdr x y (h | ⟨-, -, h⟩ | ⟨hp, hm, hio, hr, hn⟩)
  · exact hres x y h
  · exact h
  · exact hdr x y hp hm hio hr hn

/-! # 3. Transport -/

/-! ## 3.1 Along a re-timing (`rowsRel`) -/

theorem WeakRvwmoKillIO.lblRenIsIo (π : Nat → Nat) (l : Lbl) : lbIsIo (lblRen π l) = lbIsIo l := by
  cases l <;> rfl

theorem WeakRvwmoKillIO.rowsRelGisIo (π : Nat → Nat) (G G' : Gexec) (e : Geid) :
    rowsRel π G G' → gisIo G' e = gisIo G e := by
  intro hr
  unfold gisIo
  rw [rowsRelLbl π G G' e hr]
  cases gxLbl G e with
  | none => rfl
  | some l => simp [WeakRvwmoKillIO.lblRenIsIo]

theorem WeakRvwmoKillIO.rowsRelGisR (π : Nat → Nat) (G G' : Gexec) (e : Geid) :
    rowsRel π G G' → gisR G' e = gisR G e := by
  intro hr
  unfold gisR
  rw [rowsRelLbl π G G' e hr]
  cases gxLbl G e with
  | none => rfl
  | some l => simp [lblRenIsR]

/-- The residue is blind to the read renaming (same fabric list). -/
theorem ioResidueRen (π : Nat → Nat) (GF GF' : Gfexec) :
    rowsRel π GF.gfGd.gdG GF'.gfGd.gdG → GF'.gfDev = GF.gfDev →
    ∀ x y, ioResidue GF' x y ↔ ioResidue GF x y := by
  intro hr hdev x y
  have h1 : ∀ a b, WeakRvwmoGraph.gpo GF'.gfGd.gdG a b ↔ WeakRvwmoGraph.gpo GF.gfGd.gdG a b :=
    fun a b => rowsRelGpo π _ _ a b hr
  have h2 : ∀ a, gmem GF'.gfGd.gdG a ↔ gmem GF.gfGd.gdG a := fun a => rowsRelGmem π _ _ a hr
  have h3 : ∀ a, gisIo GF'.gfGd.gdG a = gisIo GF.gfGd.gdG a :=
    fun a => WeakRvwmoKillIO.rowsRelGisIo π _ _ a hr
  have h4 : ∀ a, gisW GF'.gfGd.gdG a = gisW GF.gfGd.gdG a := fun a => rowsRelGisW π _ _ a hr
  have h5 : ∀ a, gisR GF'.gfGd.gdG a = gisR GF.gfGd.gdG a :=
    fun a => WeakRvwmoKillIO.rowsRelGisR π _ _ a hr
  have h6 : ∀ a b, gfBefore GF' a b ↔ gfBefore GF a b := fun a b => by
    unfold gfBefore; rw [hdev]
  simp only [ioResidue, h1, h2, h3, h4, h5, h6]

theorem gfDevWIoRen (π : Nat → Nat) (GF GF' : Gfexec) :
    rowsRel π GF.gfGd.gdG GF'.gfGd.gdG → GF'.gfDev = GF.gfDev → gfDevWIo GF → gfDevWIo GF' := by
  intro hr hdev hwio e he
  rw [hdev] at he
  have := hwio e he
  unfold gisWIo at this ⊢
  rw [rowsRelGisW π _ _ e hr, WeakRvwmoKillIO.rowsRelGisIo π _ _ e hr]
  exact this

/-! ## 3.2 Along a hull -/

theorem WeakRvwmoKillIO.gxhGisIo (G : Gexec) (cs : List Nat) (e : Geid) :
    gisIo (gxHull G cs) e = (gcut cs e && gisIo G e) := by
  unfold gisIo
  rw [gxhLbl]
  cases hc : gcut cs e
  · simp
  · cases gxLbl G e with
    | none => simp
    | some l => simp [WeakRvwmoKillIO.lblRenIsIo]

theorem WeakRvwmoKillIO.gxhGisR (G : Gexec) (cs : List Nat) (e : Geid) :
    gisR (gxHull G cs) e = (gcut cs e && gisR G e) := by
  unfold gisR
  rw [gxhLbl]
  cases hc : gcut cs e
  · simp
  · cases gxLbl G e with
    | none => simp
    | some l => simp [lblRenIsR]

/-- (Lean-only) a hull po edge is a po edge between two KEPT events. -/
theorem WeakRvwmoKillIO.gxhGpoCut (G : Gexec) (cs : List Nat) (x y : Geid) :
    WeakRvwmoGraph.gpo (gxHull G cs) x y →
    WeakRvwmoGraph.gpo G x y ∧ gcut cs x = true ∧ gcut cs y = true := by
  intro h
  obtain ⟨hpo, hcy⟩ := (gxhGpo G cs x y).1 h
  exact ⟨hpo, gcutPoDown cs x y hpo.1 hpo.2.1 hcy, hcy⟩

/-- The hull's fabric order is the graph's, on kept members (`dclosed`: a prefix). -/
theorem WeakRvwmoKillIO.gfHullBefore (GF : Gfexec) (cs : List Nat) (x y : Geid) :
    dclosed cs GF.gfDev → gfBefore (gfHull GF cs) x y →
    gfBefore GF x y ∧ gcut cs x = true ∧ gcut cs y = true := by
  rintro hdc ⟨i, j, hi, hj, hij⟩
  exact ⟨⟨i, j, gfHullDevLookup GF cs i x hdc hi, gfHullDevLookup GF cs j y hdc hj, hij⟩,
    gfHullDevCut GF cs i x hi, gfHullDevCut GF cs j y hj⟩

/-- A hull residue edge is a graph residue edge between kept events. -/
theorem ioResidueHull (GF : Gfexec) (cs : List Nat) (x y : Geid) :
    dclosed cs GF.gfDev → ioResidue (gfHull GF cs) x y →
    ioResidue GF x y ∧ gcut cs x = true ∧ gcut cs y = true := by
  intro hdc hr
  have hio : ∀ e, gisIo (gfHull GF cs).gfGd.gdG e = (gcut cs e && gisIo GF.gfGd.gdG e) :=
    WeakRvwmoKillIO.gxhGisIo GF.gfGd.gdG cs
  have hR : ∀ e, gisR (gfHull GF cs).gfGd.gdG e = (gcut cs e && gisR GF.gfGd.gdG e) :=
    WeakRvwmoKillIO.gxhGisR GF.gfGd.gdG cs
  have hW : ∀ e, gisW (gfHull GF cs).gfGd.gdG e = (gcut cs e && gisW GF.gfGd.gdG e) := by
    intro e
    show gisW (gxHull GF.gfGd.gdG cs) e = _
    rw [gxhGisW]
    cases gcut cs e <;> rfl
  rcases hr with ⟨hp, hm, hx, hy⟩ | ⟨hp, hx, hy⟩ | ⟨hp, hx, hy, hn⟩ | ⟨hx, hy, hp⟩ | ⟨hx, hy, hb⟩
  · obtain ⟨hp, hcx, hcy⟩ := WeakRvwmoKillIO.gxhGpoCut _ cs x y hp
    obtain ⟨-, hm⟩ := (gxhGmem _ cs x).1 hm
    rw [hio, hcx, Bool.true_and] at hx
    rw [hio, hcy, Bool.true_and] at hy
    exact ⟨Or.inl ⟨hp, hm, hx, hy⟩, hcx, hcy⟩
  · obtain ⟨hp, hcx, hcy⟩ := WeakRvwmoKillIO.gxhGpoCut _ cs x y hp
    rw [hio, hcx, Bool.true_and] at hx
    rw [hW, hcy, Bool.true_and] at hy
    exact ⟨Or.inr (Or.inl ⟨hp, hx, hy⟩), hcx, hcy⟩
  · obtain ⟨hp, hcx, hcy⟩ := WeakRvwmoKillIO.gxhGpoCut _ cs x y hp
    rw [hio, hcx, Bool.true_and] at hx
    rw [hR, hcy, Bool.true_and] at hy
    exact ⟨Or.inr (Or.inr (Or.inl ⟨hp, hx, hy, hn⟩)), hcx, hcy⟩
  · obtain ⟨hp, hcx, hcy⟩ := WeakRvwmoKillIO.gxhGpoCut _ cs x y hp
    rw [hio, hcx, Bool.true_and] at hx
    rw [hio, hcy, Bool.true_and] at hy
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨hx, hy, hp⟩))), hcx, hcy⟩
  · obtain ⟨hb, hcx, hcy⟩ := WeakRvwmoKillIO.gfHullBefore GF cs x y hdc hb
    obtain ⟨-, hx⟩ := (gxhGmem _ cs x).1 hx
    obtain ⟨-, hy⟩ := (gxhGmem _ cs y).1 hy
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨hx, hy, hb⟩))), hcx, hcy⟩

/-- THE TRUSTED ITEM RESTRICTS TO A `dclosed` HULL. -/
theorem ioResidueGmoHull (GF : Gfexec) (cs : List Nat) :
    GF.gfGd.gdG.gxGmo.Nodup → dclosed cs GF.gfDev → ioResidueGmo GF →
    ioResidueGmo (gfHull GF cs) := by
  intro hnd hdc hres x y hr
  obtain ⟨hr, hcx, hcy⟩ := ioResidueHull GF cs x y hdc hr
  exact (gxhGmoLt GF.gfGd.gdG cs x y hnd).2 ⟨hcx, hcy, hres x y hr⟩

theorem gdiskRead14Hull (G : Gexec) (cs : List Nat) :
    G.gxGmo.Nodup → gdiskRead14 G → gdiskRead14 (gxHull G cs) := by
  intro hnd hdr e a hp hm hio hr hn
  obtain ⟨hp, hce, hca⟩ := WeakRvwmoKillIO.gxhGpoCut G cs e a hp
  obtain ⟨-, hm⟩ := (gxhGmem G cs e).1 hm
  rw [WeakRvwmoKillIO.gxhGisIo, hce, Bool.true_and] at hio
  rw [WeakRvwmoKillIO.gxhGisR, hca, Bool.true_and] at hr
  exact (gxhGmoLt G cs e a hnd).2 ⟨hce, hca, hdr e a hp hm hio hr hn⟩

theorem gfDevWIoHull (GF : Gfexec) (cs : List Nat) : gfDevWIo GF → gfDevWIo (gfHull GF cs) := by
  intro hwio e he
  obtain ⟨he, hc⟩ := List.mem_filter.1 he
  have h := hwio e he
  show (gisW (gxHull GF.gfGd.gdG cs) e || gisIo (gxHull GF.gfGd.gdG cs) e) = true
  rw [gxhGisW, WeakRvwmoKillIO.gxhGisIo, hc]
  exact h

/-! # 4. THE NORMALIZATION -/

/-- **`normalizeOfAcyclic` over `racyDIO`**: the re-timed graph is RVWMO⁻ + rule 14 (+ the cat
arms, [R21.2]) AND keeps the residue, the I/O events' relative positions and the disk-read
anchors. -/
theorem normalizeOfAcyclicIO (GF : Gfexec) :
    rvwmoCoreD GF.gfGd →
    (∀ x, ¬ tc (racyDIO GF) x x) →
    ∃ (GD' : Gdexec) (pi : Nat → Nat),
      rvwmoMinusDepsConsistent GD' ∧
      grule14 GD'.gdG ∧
      rowsRel pi GF.gfGd.gdG GD'.gdG ∧
      GD'.gdDeps = GF.gfGd.gdDeps ∧
      wperm pi GF.gfGd.gdG GD'.gdG ∧
      gppoCat6Gmo GD'.gdG ∧
      ioResidueGmo ⟨GD', GF.gfDev⟩ ∧
      gdiskRead14 GD'.gdG ∧
      (∀ x y, gmoIo GF.gfGd.gdG x y → gmoIo GD'.gdG x y) := by
  intro hcore hacy
  have hXm : ∀ x y, ioExtra GF x y → x ∈ GF.gfGd.gdG.gxGmo ∧ y ∈ GF.gfGd.gdG.gxGmo := by
    intro x y h
    obtain ⟨hx, hy⟩ := ioExtraGmem GF x y h
    exact ⟨gwfMemGmo _ x hcore.1 hx, gwfMemGmo _ y hcore.1 hy⟩
  obtain ⟨GD', pi, hc', h14, hrr, hdeps, hw, h6, hX⟩ :=
    normalizeOfAcyclicX GF.gfGd (ioExtra GF) hcore hXm (fun x y => racyDIODec GF x y) hacy
  have hio : ∀ a, gisIo GD'.gdG a = gisIo GF.gfGd.gdG a :=
    fun a => WeakRvwmoKillIO.rowsRelGisIo pi _ _ a hrr
  refine ⟨GD', pi, hc', h14, hrr, hdeps, hw, h6, ?_, ?_, ?_⟩
  · intro x y hr
    exact hX x y (Or.inl ((ioResidueRen pi GF ⟨GD', GF.gfDev⟩ hrr rfl x y).1 hr))
  · intro e a hp hm hie hr hn
    refine hX e a (Or.inr (Or.inr ⟨(rowsRelGpo pi _ _ e a hrr).1 hp, (rowsRelGmem pi _ _ e hrr).1 hm,
      ?_, ?_, hn⟩))
    · rw [← hio]; exact hie
    · rw [← WeakRvwmoKillIO.rowsRelGisR pi _ _ a hrr]; exact hr
  · rintro x y ⟨hx, hy, hmo⟩
    exact ⟨by rw [hio]; exact hx, by rw [hio]; exact hy, hX x y (Or.inr (Or.inl ⟨hx, hy, hmo⟩))⟩

/-- **THE NORMALIZED GRAPH'S (L) TRACE REALIZES IT** (a corollary of `rule14LinearizationIO`
through `fconfTraceRealizeIO`): a `racyDIO`-acyclic conformant core graph is re-timed to `GF'`
(same rows up to the read renaming, same fabric, conformant) whose anchored rank trace
`glinEidsIO` is a consistent candidate, visits the fabric in order and is SUPPLIED along it. -/
theorem fconfRealizeIO (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (N : Nat) :
    rvwmoCoreD GF.gfGd →
    gfexecConfIO boot d0 fab GF →
    gfDevWIo GF →
    (∀ x, ¬ tc (racyDIO GF) x x) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (pi : Nat → Nat) (GF' : Gfexec),
      rowsRel pi GF.gfGd.gdG GF'.gfGd.gdG ∧
      GF'.gfDev = GF.gfDev ∧
      gfexecConfIO boot d0 fab GF' ∧
      ioResidueGmo GF' ∧
      gdiskRead14 GF'.gfGd.gdG ∧
      srvwmoConsistent (linCandIO GF'.gfGd.gdG) ∧
      (linCandIO GF'.gfGd.gdG).cdImg = GF.gfGd.gdG.gxImg ∧
      (∀ i, List.map (fun s => s.esLb)
          (List.filter (fun s => decide (s.esAg = i)) (linCandIO GF'.gfGd.gdG).cdTr) =
            ((GF.gfGd.gdG.gxProg[i]?).getD []).map (lblRen pi)) ∧
      trDevOrdered GF' (linCandIO GF'.gfGd.gdG) ∧
      ∃ pst : Nat → List Pexv6,
        pst 0 = (List.range' 0 N).map boot ∧
        fab (dcnt GF' (linCandIO GF'.gfGd.gdG).cdTr 0) = d0 ∧
        execProgOk' (pstepPin (linCandIO GF'.gfGd.gdG).cdImg pstepEv) pclsEv pst
          (fun k => fab (dcnt GF' (linCandIO GF'.gfGd.gdG).cdTr k))
          (candExec (linCandIO GF'.gfGd.gdG)) := by
  intro hcore hconf hwio hacy hN
  obtain ⟨GD', pi, hc', h14, hrr, hdeps, -, -, hres', hdr', -⟩ :=
    normalizeOfAcyclicIO GF hcore hacy
  let GF' : Gfexec := ⟨GD', GF.gfDev⟩
  have hconf' : gfexecConfIO boot d0 fab GF' := gfexecConfRen pi boot d0 fab GF GF' hrr hdeps rfl hconf
  have hwio' : gfDevWIo GF' := gfDevWIoRen pi GF GF' hrr rfl hwio
  have hN' : GF'.gfGd.gdG.gxProg.length ≤ N := by
    show GD'.gdG.gxProg.length ≤ N
    rw [rowsRelNharts pi _ _ hrr]; exact hN
  obtain ⟨hsr, himg, hrow, -, hord, pst, hpst0, hf0, hprg⟩ :=
    fconfTraceRealizeIO boot d0 fab GF' N hc'.1 h14 hres' hdr' hconf' hwio' hN'
  have himg' : (linCandIO GF'.gfGd.gdG).cdImg = GF.gfGd.gdG.gxImg := by
    rw [himg]; exact rowsRelImg pi _ _ hrr
  refine ⟨pi, GF', hrr, rfl, hconf', hres', hdr', hsr, himg', ?_, hord, pst, hpst0, hf0, ?_⟩
  · intro i
    rw [hrow i]
    show (GD'.gdG.gxProg[i]?).getD [] = _
    rw [hrr.2.1, List.getElem?_map]
    cases GF.gfGd.gdG.gxProg[i]? <;> rfl
  · exact hprg

/-! # 5. THE KILL INTERFACE AND THE ROUTE -/

/-- The `cycleKill`/`cycleKillF` obligation over `racyDIO`: at a conformant RVWMO⁻ graph with the
residue, the disk-read anchors and `gfDevWIo`, EVERY PROPER HULL OF WHICH IS `racyDIO`-acyclic,
there is no `racyDIO` cycle. -/
def cycleKillIO (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) : Prop :=
  ∀ GF : Gfexec,
    rvwmoMinusDepsConsistent GF.gfGd →
    gfexecConfIO boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF →
    (∀ cs, properCutF GF cs → ∀ x, ¬ tc (racyDIO (gfHull GF cs)) x x) →
    ∀ x, tc (racyDIO GF) x x → False

/-- (Lean-only) the bundle's model arm `gfexecConsistent`, DERIVED: the fabric steps are gmo-forward
by the residue's fabric arm on write/I/O members. -/
theorem WeakRvwmoKillIO.gfexecConsistentOfRes (GF : Gfexec) :
    rvwmoMinusDepsConsistent GF.gfGd → ioResidueGmo GF → gfDevWIo GF → gfexecConsistent GF :=
  fun hc hres hwio => ⟨hc, fun a b hadj =>
    gfDevGmoOfRes GF hres hwio a b (GraphFabResidue.gdevAdjGfBefore GF a b hadj)⟩

/-- Every premise of the kill passes to a proper hull. -/
theorem WeakRvwmoKillIO.hullPremises (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (GF : Gfexec) (cs : List Nat) :
    rvwmoMinusDepsConsistent GF.gfGd → gfexecConfIO boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF → properCutF GF cs →
    rvwmoMinusDepsConsistent (gfHull GF cs).gfGd ∧ gfexecConfIO boot d0 fab (gfHull GF cs) ∧
    ioResidueGmo (gfHull GF cs) ∧ gdiskRead14 (gfHull GF cs).gfGd.gdG ∧
    gfDevWIo (gfHull GF cs) := by
  intro hc hconf hres hdr hwio hpc
  have hok : hullOk GF.gfGd.gdG cs := properCutOk _ _ hpc.1
  have hnd := hc.1.1.1
  exact ⟨hullDepsConsistent _ cs hc hok,
    gfexecConfHull boot d0 fab GF cs (WeakRvwmoKillIO.gfexecConsistentOfRes GF hc hres hwio)
      hpc.2 hok hconf,
    ioResidueGmoHull GF cs hnd hpc.2 hres, gdiskRead14Hull GF.gfGd.gdG cs hnd hdr,
    gfDevWIoHull GF cs hwio⟩

/-- THE INDUCTION (the `t2linAuxF` mirror). -/
theorem t2linAuxIO (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) :
    cycleKillIO boot d0 fab →
    ∀ (n : Nat) (GF : Gfexec),
      (gevs' GF.gfGd.gdG).length ≤ n →
      rvwmoMinusDepsConsistent GF.gfGd → gfexecConfIO boot d0 fab GF →
      ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF →
      ∀ x, ¬ tc (racyDIO GF) x x := by
  intro hk n
  induction n with
  | zero =>
    intro GF hlen hc hconf hres hdr hwio x hcyc
    refine hk GF hc hconf hres hdr hwio ?_ x hcyc
    intro cs hpc y _
    have := gfHullEventsLt GF cs hpc
    omega
  | succ n ih =>
    intro GF hlen hc hconf hres hdr hwio x hcyc
    refine hk GF hc hconf hres hdr hwio ?_ x hcyc
    intro cs hpc
    obtain ⟨hc', hconf', hres', hdr', hwio'⟩ :=
      WeakRvwmoKillIO.hullPremises boot d0 fab GF cs hc hconf hres hdr hwio hpc
    refine ih (gfHull GF cs) ?_ hc' hconf' hres' hdr' hwio'
    have := gfHullEventsLt GF cs hpc
    omega

theorem t2linIO (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) :
    cycleKillIO boot d0 fab →
    ∀ GF : Gfexec,
      rvwmoMinusDepsConsistent GF.gfGd → gfexecConfIO boot d0 fab GF →
      ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF →
      ∀ x, ¬ tc (racyDIO GF) x x :=
  fun hk GF => t2linAuxIO boot d0 fab hk (gevs' GF.gfGd.gdG).length GF (Nat.le_refl _)

/-- **`hullRun` AT THE FABRIC**: a `racyDIO`-acyclic hull of a conformant core graph RUNS — a
`RunData` (Glue §4) at the fabric trace `fab ∘ dcnt GF'` of the normalized hull bundle `GF'`,
whose trace is the (L) candidate `linCandIO`, with the hull's rows (read-renamed). -/
theorem hullRunIO (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (cs : List Nat) (N : Nat) :
    rvwmoCoreD GF.gfGd →
    hullOk GF.gfGd.gdG cs →
    gfexecConfIO boot d0 fab (gfHull GF cs) →
    gfDevWIo GF →
    (∀ x, ¬ tc (racyDIO (gfHull GF cs)) x x) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (c : Cand) (pst : Nat → List Pexv6) (pi : Nat → Nat) (GF' : Gfexec),
      RunData boot d0 N GF.gfGd.gdG c pst (fun k => fab (dcnt GF' c.cdTr k)) ∧
      c = linCandIO GF'.gfGd.gdG ∧
      GF'.gfDev = (gfHull GF cs).gfDev ∧
      gfexecConfIO boot d0 fab GF' ∧
      trDevOrdered GF' c ∧
      (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) =
        (((gxHull GF.gfGd.gdG cs).gxProg[i]?).getD []).map (lblRen pi)) := by
  intro hcore hok hconf hwio hacy hN
  have hNh : (gfHull GF cs).gfGd.gdG.gxProg.length ≤ N := by
    have := gxhNharts GF.gfGd.gdG cs
    change (gxHull GF.gfGd.gdG cs).gxProg.length ≤ N
    omega
  obtain ⟨pi, GF', -, hdev, hconf', -, -, hsr, himg, hrow, hord, pst, hpst0, hf0, hprg⟩ :=
    fconfRealizeIO boot d0 fab (gfHull GF cs) N (hullCoreD GF.gfGd cs hcore hok) hconf
      (gfDevWIoHull GF cs hwio) hacy hNh
  exact ⟨linCandIO GF'.gfGd.gdG, pst, pi, GF', ⟨hsr, himg.trans (gxhImg _ _), hpst0, hf0, hprg⟩,
    rfl, hdev, hconf', hord, hrow⟩

/-- **`cycleKillIO` THROUGH `hullRunIO`**: under the kill, every proper hull of a conformant
graph runs (its acyclicity is the induction's, `t2linIO` on the hull). -/
theorem hullRunOfKillIO (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (cs : List Nat) (N : Nat) :
    cycleKillIO boot d0 fab →
    rvwmoMinusDepsConsistent GF.gfGd → gfexecConfIO boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF →
    properCutF GF cs →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (c : Cand) (pst : Nat → List Pexv6) (pi : Nat → Nat) (GF' : Gfexec),
      RunData boot d0 N GF.gfGd.gdG c pst (fun k => fab (dcnt GF' c.cdTr k)) ∧
      c = linCandIO GF'.gfGd.gdG ∧
      GF'.gfDev = (gfHull GF cs).gfDev ∧
      gfexecConfIO boot d0 fab GF' ∧
      trDevOrdered GF' c ∧
      (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) =
        (((gxHull GF.gfGd.gdG cs).gxProg[i]?).getD []).map (lblRen pi)) := by
  intro hk hc hconf hres hdr hwio hpc hN
  obtain ⟨hc', hconf', hres', hdr', hwio'⟩ :=
    WeakRvwmoKillIO.hullPremises boot d0 fab GF cs hc hconf hres hdr hwio hpc
  exact hullRunIO boot d0 fab GF cs N hc (properCutOk _ _ hpc.1) hconf' hwio
    (t2linIO boot d0 fab hk (gfHull GF cs) hc' hconf' hres' hdr' hwio') hN

/-- THE COROLLARY: under the kill, the whole conformant graph is realized along the fabric. -/
theorem t2linRealizeIO (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (N : Nat) :
    cycleKillIO boot d0 fab →
    rvwmoMinusDepsConsistent GF.gfGd → gfexecConfIO boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (pi : Nat → Nat) (GF' : Gfexec),
      rowsRel pi GF.gfGd.gdG GF'.gfGd.gdG ∧ GF'.gfDev = GF.gfDev ∧
      srvwmoConsistent (linCandIO GF'.gfGd.gdG) ∧
      trDevOrdered GF' (linCandIO GF'.gfGd.gdG) ∧
      ∃ pst : Nat → List Pexv6,
        pst 0 = (List.range' 0 N).map boot ∧
        execProgOk' (pstepPin (linCandIO GF'.gfGd.gdG).cdImg pstepEv) pclsEv pst
          (fun k => fab (dcnt GF' (linCandIO GF'.gfGd.gdG).cdTr k))
          (candExec (linCandIO GF'.gfGd.gdG)) := by
  intro hk hc hconf hres hdr hwio hN
  obtain ⟨pi, GF', hrr, hdev, -, -, -, hsr, -, -, hord, pst, hpst0, -, hprg⟩ :=
    fconfRealizeIO boot d0 fab GF N hc hconf hwio
      (t2linIO boot d0 fab hk GF hc hconf hres hdr hwio) hN
  exact ⟨pi, GF', hrr, hdev, hsr, hord, pst, hpst0, hprg⟩

/-! # 6. THE ARMS: the decomposition and the kill at `X := ioCross` -/

/-- The cross order of the I/O chain: rfe ∪ co ∪ fr, and every extra arm. -/
def ioCross (GF : Gfexec) (x y : Geid) : Prop :=
  CatLin.gcrossE GF.gfGd.gdG x y ∨ ioExtra GF x y

theorem racyDIOSplit (GF : Gfexec) (x y : Geid) :
    racyDIO GF x y → CatLin.rsameC GF.gfGd x y ∨ ioCross GF x y := by
  rintro (h | h)
  · rcases CatLin.racyDSplitC _ _ _ h with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · exact .inr (.inr h)

/-- The cross order is gmo-forward ("(T) directly"). -/
theorem ioCrossGmo (GF : Gfexec) :
    gwf GF.gfGd.gdG → gloadValue GF.gfGd.gdG → ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ∀ x y, ioCross GF x y → gmoLt GF.gfGd.gdG x y := by
  rintro hwf hlv hres hdr x y (h | h)
  · exact CatLin.gcrossEGmo _ x y hwf hlv h
  · exact ioExtraGmo GF hres hdr x y h

/-- A `racyDIO` cycle is a nonempty raw chain with `ioCross` entries. -/
theorem cycleSegmentsIO (GF : Gfexec) (ad : List (Geid × Geid)) (x : Geid) :
    CatLin.rvwmoCatAD GF.gfGd ad → tc (racyDIO GF) x x →
    ∃ z ss, ss ≠ [] ∧ CatLin.rawChainC GF.gfGd (ioCross GF) z z ss :=
  CatLin.cycleSegmentsX GF.gfGd ad (racyDIO GF) (ioCross GF) (racyDIOSplit GF) x

/-- **`cycleKillIOC`**: the cat composition kill at `X := ioCross` (⊇ gmo|IO). -/
theorem cycleKillIOC (GF : Gfexec) (ad : List (Geid × Geid)) (x : Geid) (ss : List Seg) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → CatLin.chainC GF.gfGd.gdG (ioCross GF) x x ss → False :=
  fun hc hres hdr => CatLin.cycleKillArmsX GF.gfGd.gdG (ioCross GF) x ss
    (ioCrossGmo GF hc.1 hc.2.2.1 hres hdr)

/-- An I/O entry inside a critical section is gmo-before the section's release store — residue
arm (R2); the `gmoLt entry REL` premise of `WeakRvwmoKillArms.csChainedMem`. -/
theorem ioEntryRelGmo (GF : Gfexec) (entry REL : Geid) :
    ioResidueGmo GF → gisIo GF.gfGd.gdG entry = true →
    WeakRvwmoGraph.gpo GF.gfGd.gdG entry REL → gisW GF.gfGd.gdG REL = true →
    gmoLt GF.gfGd.gdG entry REL :=
  fun hres hio hpo hw => hres entry REL (Or.inr (Or.inl ⟨hpo, hio, hw⟩))

/-! # 7. `ioSegPinned`: a run through an I/O event is a composite pin -/

/-- CHECK (i) of `ioSegPinned` (plan §C W13 R5): no same-row edge INTO a non-write lies outside
gmo. -/
def WeakRvwmoKillIO.noReadEdgeOutsideGmo (G : Gexec) (S : Geid → Geid → Prop) : Prop :=
  ∀ u v, S u v → gisW G v = false → gmoLt G u v

/-- (Lean-only) a po-forward relation's closure is po. -/
theorem WeakRvwmoKillIO.tcGpo (G : Gexec) (S : Geid → Geid → Prop) (a b : Geid) :
    (∀ u v, S u v → WeakRvwmoGraph.gpo G u v) → tc S a b → WeakRvwmoGraph.gpo G a b := by
  intro hpo h
  induction h with
  | single h => exact hpo _ _ h
  | tail _ h ih => exact gpoTrans G _ _ _ ih (hpo _ _ h)

/-- **Claim L-IO as a lemma** (census `notes/W13-io-census.md`; plan §C W13 R5): a segment run
`entry →⁺ x →* exit` of a po-forward same-row relation `S` through an I/O event `x` has
`entry <gmo exit` — the entry by (R1)/(R3) (a memory event po-before `x`), every later event by
(R2) (writes) or check (i) (everything else, from an event already gmo-after `x`).

The plan's TWO CHECKS: **(i)** `noReadEdgeOutsideGmo` — a HYPOTHESIS here, PROVED for the RVWMO⁻
chain's same-row relation (`rsameNoReadEdge`); it is FALSE for the cat chain's `CatLin.rsameC`,
whose rfi arm forwards a read from a po-earlier write without gmo (the plan's refined cat
invariant "gmo-after `x`, or forwarded from a write gmo-after `x`", closed except at a
`PR∧SR∧¬PW` fence, is NOT built here).  **(ii)** the `lk->cpu` discipline (`lockWordDiscAt`,
`Xv6/AccessDiscipline.lean`; [rev 28]) is NOT a precondition of this graph lemma — its proof uses
only (R1)–(R3) and check (i); (ii) is the precondition of the CERTIFICATES of the window's racy
lock-layer reads (C1/C2), which go through the lock-layer route (W11 (i)), and a machine-state
predicate has no graph-tier statement to put here. -/
theorem ioSegPinned (GF : Gfexec) (S : Geid → Geid → Prop) (x entry exit : Geid) :
    ioResidueGmo GF →
    (∀ u v, S u v → WeakRvwmoGraph.gpo GF.gfGd.gdG u v) →
    WeakRvwmoKillIO.noReadEdgeOutsideGmo GF.gfGd.gdG S →
    gisIo GF.gfGd.gdG x = true → gmem GF.gfGd.gdG entry →
    tc S entry x → rtc S x exit →
    gmoLt GF.gfGd.gdG entry exit := by
  intro hres hpo hchk hio hm hex hxe
  have hpoe : WeakRvwmoGraph.gpo GF.gfGd.gdG entry x := WeakRvwmoKillIO.tcGpo _ S _ _ hpo hex
  have hen : gmoLt GF.gfGd.gdG entry x := by
    cases he : gisIo GF.gfGd.gdG entry with
    | false => exact hres entry x (Or.inl ⟨hpoe, hm, he, hio⟩)
    | true => exact hres entry x (Or.inr (Or.inr (Or.inr (Or.inl ⟨he, hio, hpoe⟩))))
  have key : ∀ v, rtc S x v →
      v = x ∨ (WeakRvwmoGraph.gpo GF.gfGd.gdG x v ∧ gmoLt GF.gfGd.gdG x v) := by
    refine rtc_ind_r _ x (Or.inl rfl) ?_
    intro u v _ huv ih
    have hxv : WeakRvwmoGraph.gpo GF.gfGd.gdG x v := by
      rcases ih with rfl | ⟨hxu, -⟩
      · exact hpo _ _ huv
      · exact gpoTrans _ _ _ _ hxu (hpo _ _ huv)
    refine Or.inr ⟨hxv, ?_⟩
    cases hw : gisW GF.gfGd.gdG v with
    | true => exact hres x v (Or.inr (Or.inl ⟨hxv, hio, hw⟩))
    | false =>
      have huv' := hchk u v huv hw
      rcases ih with rfl | ⟨-, hxu⟩
      · exact huv'
      · exact gmoLtTrans _ _ _ _ hxu huv'
  rcases key exit hxe with rfl | ⟨-, hxe'⟩
  · exact hen
  · exact gmoLtTrans _ _ _ _ hen hxe'

/-- The RVWMO⁻ chain's same-row relation is po-forward. -/
theorem WeakRvwmoKillIO.rsameGpo (GD : Gdexec) :
    gdepsWf GD.gdG GD.gdDeps → ∀ u v, rsame GD u v → WeakRvwmoGraph.gpo GD.gdG u v := by
  rintro hwf u v (h | h | h)
  · exact h.1
  · obtain ⟨h1, h2⟩ := gppoPoLt _ u v h
    obtain ⟨hm1, hm2⟩ := gppoGmem _ u v h
    exact ⟨h1, h2, GraphFabResidue.gmemSome _ _ hm1, GraphFabResidue.gmemSome _ _ hm2⟩
  · obtain ⟨h1, h2, ⟨l1, hl1, -⟩, ⟨l2, hl2, -⟩⟩ := hwf (u, v) h
    exact ⟨h1, h2, by simp [hl1], by simp [hl2]⟩

/-- **CHECK (i), PROVED for the RVWMO⁻ chain**: `gpow` only targets writes; `gppo` and the
dependency edges are gmo-forward. -/
theorem rsameNoReadEdge (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD → WeakRvwmoKillIO.noReadEdgeOutsideGmo GD.gdG (rsame GD) := by
  rintro ⟨hc, -, hdg⟩ u v (h | h | h) hw
  · rw [h.2.2] at hw; cases hw
  · exact hc.2.1 u v h
  · exact hdg (u, v) h

/-- `ioSegPinned` at the RVWMO⁻ chain's segment relation: both checks of the graph tier
discharged. -/
theorem ioSegPinnedMinus (GF : Gfexec) (x entry exit : Geid) :
    rvwmoMinusDepsConsistent GF.gfGd → ioResidueGmo GF →
    gisIo GF.gfGd.gdG x = true → gmem GF.gfGd.gdG entry →
    tc (rsame GF.gfGd) entry x → rtc (rsame GF.gfGd) x exit →
    gmoLt GF.gfGd.gdG entry exit :=
  fun hc hres => ioSegPinned GF (rsame GF.gfGd) x entry exit hres
    (WeakRvwmoKillIO.rsameGpo GF.gfGd hc.2.1) (rsameNoReadEdge GF.gfGd hc)

/-! # 8. Non-vacuity -/

/-- On a graph that is ALREADY RVWMO⁻ + rule 14 with the residue and the disk-read anchors,
every `racyDIO` edge is gmo-forward, so `racyDIO` is acyclic. -/
theorem racyDIOAcyclicOfRule14 (GF : Gfexec) :
    rvwmoMinusDepsConsistent GF.gfGd → grule14 GF.gfGd.gdG → ioResidueGmo GF →
    gdiskRead14 GF.gfGd.gdG → ∀ x, ¬ tc (racyDIO GF) x x := by
  intro hc h14 hres hdr x hcyc
  have step : ∀ a b, racyDIO GF a b → gmoLt GF.gfGd.gdG a b := by
    rintro a b (h | h)
    · exact rdGmo _ a b hc h14 h
    · exact ioExtraGmo GF hres hdr a b h
  have key : ∀ a b, tc (racyDIO GF) a b → gmoLt GF.gfGd.gdG a b := by
    intro a b h
    induction h with
    | single h => exact step _ _ h
    | tail _ h ih => exact gmoLtTrans _ _ _ _ ih (step _ _ h)
  exact gmoLtIrrefl _ x (key x x hcyc)

/-- The re-encoded `w13f` (`GraphFabResidue`, a NON-EMPTY fabric): `racyDIO` is acyclic, so
`normalizeOfAcyclicIO` applies there. -/
theorem w13fIoRacyDIOAcyclic : ∀ x, ¬ tc (racyDIO w13fIo) x x :=
  racyDIOAcyclicOfRule14 w13fIo
    ⟨w13fIoConsistent, fun p hp => by simp [w13fIo] at hp, fun p hp => by simp [w13fIo] at hp⟩
    w13fIoRule14 w13fIoResidueOk w13fIoDiskRead14

/-- …and `racyDIO` BITES: with the fabric order REVERSED against gmo, the fabric arm and gmo|IO
form a two-cycle (so acyclicity of `racyDIO` excludes a fabric order that disagrees with the
memory order of the I/O events). -/
theorem w13fIoRevRacyDIOCycle : tc (racyDIO ⟨⟨w13fIoG, []⟩, [(1, 0), (0, 0)]⟩) (0, 0) (0, 0) := by
  have hmo : gmoLt w13fIoG (0, 0) (1, 0) := by unfold gmoLt; decide +kernel
  refine tc_l (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hmo⟩))) (tc_once ?_)
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨GraphFabResidue.gisIoGmem _ _ rfl, GraphFabResidue.gisIoGmem _ _ rfl,
      ⟨0, 1, rfl, rfl, by omega⟩⟩)))))

end Weak
