/-
Weak: **W12 (3) — `hullCatAD`: the hull of a cat-consistent graph is cat-consistent** (plan
`notes/weak-allocproc-plan.md` §C W12 (3); D25 (a) [OWN.5]).

Lean-only, no Rocq twin.  `WeakRvwmoHull.hullConsistent` re-done for `CatLin.rvwmoCatAD`: the
hull `gdHull GD cs` of an rf-closed cut keeps every conjunct, with rule 12 over the CUT's
addr/data sublist `ad.filter (both endpoints kept)`.

  §1  Arm transport, hull → `G`, one lemma per riscv.cat arm (`hullGppo1` … `hullGrcsc`), and
      the rf transport `hullGrfAt` / `hullGrf` — the only place the cut's rf-closure (`hullOk`)
      and `G`'s load value are spent: a kept read's renamed timestamp `hren t` names, in the hull,
      exactly the write `t` names in `G` (`hrenWat` on the rf-closed source).
  §2  `hullCat6`: every `gppoCat6` edge of the hull is one of `G` between kept events.
  §3  `hullCatAD`.

**What the spike's risk note feared, and why it does not arise.**  `notes/W12-spike.md` listed
"`hren` injective on the cut's sources" for rule 2's `t1 ≠ t2`.  The transport runs hull → `G`,
so rule 2 needs only `hren t1 ≠ hren t2 → t1 ≠ t2` (congruence), and rules 3/12 need only that
`gwriteAt (hull) (hren t)` is `gwriteAt G t` on an rf-closed source (`hrenWat`).  No injectivity.
-/
import Weak.CatLin
import Weak.WeakRvwmoHull

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace CatLin

/-! # 1. Arm transport, hull → `G` -/

theorem hullGaccesses (G : Gexec) (cs : List Nat) (e : Geid) (a : Int) :
    gaccesses (gxHull G cs) e a → gaccesses G e a := by
  rintro (⟨v, h⟩ | ⟨t, v, h⟩)
  · exact .inl ⟨v, ((gxhWrb G cs e a v).1 h).2⟩
  · obtain ⟨-, t0, h0, -⟩ := gxhRdbInv G cs e a t v h
    exact .inr ⟨t0, v, h0⟩

theorem hullGpo (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    WeakRvwmoGraph.gpo (gxHull G cs) e1 e2 →
    WeakRvwmoGraph.gpo G e1 e2 ∧ gcut cs e1 = true ∧ gcut cs e2 = true := by
  intro h
  obtain ⟨hpo, hc2⟩ := (gxhGpo G cs e1 e2).1 h
  exact ⟨hpo, gcutPoDown cs e1 e2 hpo.1 hpo.2.1 hc2, hc2⟩

/-- The rf transport: a hull read's source is its `G` source (load value + rf-closure). -/
theorem hullGrfAt (G : Gexec) (cs : List Nat) (a : Int) (w r : Geid) :
    gloadValue G → hullOk G cs → grfAt (gxHull G cs) a w r →
    grfAt G a w r ∧ gcut cs w = true ∧ gcut cs r = true := by
  rintro hlv hok ⟨t', v, hrd', hat'⟩
  obtain ⟨hcr, t, hrd, rfl⟩ := gxhRdbInv G cs r a t' v hrd'
  cases t with
  | zero => simp [hrenZero, gwriteAt] at hat'
  | succ i =>
    obtain ⟨w0, hwat, -, -⟩ :=
      gloadSrcElim G (i + 1) a v r (Nat.succ_pos i) (hlv r a (i + 1) v hrd).1
    have hcw := hullOkRf G cs r a (i + 1) v w0 hok hcr hrd hwat
    have hw' := hrenWat G cs (i + 1) w0 hwat hcw
    rw [hw', Option.some.injEq] at hat'
    subst hat'
    exact ⟨⟨i + 1, v, hrd, hwat⟩, hcw, hcr⟩

theorem hullGrf (G : Gexec) (cs : List Nat) (w r : Geid) :
    gloadValue G → hullOk G cs → WeakRvwmoAcyc.grf (gxHull G cs) w r →
    WeakRvwmoAcyc.grf G w r ∧ gcut cs w = true ∧ gcut cs r = true := by
  rintro hlv hok ⟨a, t, v, hrd, hat⟩
  obtain ⟨h, hcw, hcr⟩ := hullGrfAt G cs a w r hlv hok ⟨t, v, hrd, hat⟩
  exact ⟨grfAtGrf G a w r h, hcw, hcr⟩

theorem hullGppo1 (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    gppo1 (gxHull G cs) e1 e2 → gppo1 G e1 e2 := by
  rintro ⟨hpo, a, h1, v, h2⟩
  exact ⟨(hullGpo G cs e1 e2 hpo).1, a, hullGaccesses G cs e1 a h1, v,
    ((gxhWrb G cs e2 a v).1 h2).2⟩

/-- Rule 2: the renamed sources differ only if the sources do; a `G`-write po-between two kept
events is kept, so the hull's "no write po-between" covers it. -/
theorem hullGppo2 (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    gppo2 (gxHull G cs) e1 e2 → gppo2 G e1 e2 := by
  rintro ⟨hpo, a, t1', v1, t2', v2, h1, h2, hne, hno⟩
  obtain ⟨hpoG, hc1, hc2⟩ := hullGpo G cs e1 e2 hpo
  obtain ⟨-, t1, h1G, rfl⟩ := gxhRdbInv G cs e1 a t1' v1 h1
  obtain ⟨-, t2, h2G, rfl⟩ := gxhRdbInv G cs e2 a t2' v2 h2
  refine ⟨hpoG, a, t1, v1, t2, v2, h1G, h2G, fun heq => hne (by rw [heq]), ?_⟩
  intro w v hw hpo1 hpo2
  have hcw : gcut cs w = true := gcutPoDown cs w e2 hpo2.1 hpo2.2.1 hc2
  exact hno w v ((gxhWrb G cs w a v).2 ⟨hcw, hw⟩) ((gxhGpo G cs e1 w).2 ⟨hpo1, hcw⟩)
    ((gxhGpo G cs w e2).2 ⟨hpo2, hc2⟩)

theorem lblRenIsRmw (π : Nat → Nat) (l : Lbl) : lbIsRmw (lblRen π l) = lbIsRmw l := by
  simp only [lbIsRmw, lblRenIsR, lblRenIsW]

theorem lblRenRcsc (π : Nat → Nat) (l : Lbl) : lbRcsc (lblRen π l) = lbRcsc l := by
  simp only [lbRcsc, lblRenAq, lblRenRl]

theorem hullGppo3 (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    gloadValue G → hullOk G cs → gppo3 (gxHull G cs) e1 e2 → gppo3 G e1 e2 := by
  rintro hlv hok ⟨hpo, hrmw, a, hrf⟩
  exact ⟨(hullGpo G cs e1 e2 hpo).1, ((gxhGlblIs G cs e1 lbIsRmw lblRenIsRmw).1 hrmw).2, a,
    (hullGrfAt G cs a e1 e2 hlv hok hrf).1⟩

theorem hullGfence (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    gfenceCovers (gxHull G cs) e1 e2 → gfenceCovers G e1 e2 := by
  rintro ⟨pr, pw, sr, sw, ⟨hag, hlt, kf, hk3, hk4, hlf⟩, hk1, hk2⟩
  have hl' := (rowsRelFence _ _ _ _ pr pw sr sw (hullRowsRel G cs)).1 hlf
  have hl := (gxrLblSome G cs 0 _ _ hl').2
  refine ⟨pr, pw, sr, sw, ⟨hag, hlt, kf, hk3, hk4, hl⟩, ?_, ?_⟩
  · rcases hk1 with ⟨h, hb⟩ | ⟨h, hb⟩
    · exact .inl ⟨((gxhGlblIs G cs e1 lbIsR lblRenIsR).1 h).2, hb⟩
    · exact .inr ⟨((gxhGlblIs G cs e1 lbIsW lblRenIsW).1 h).2, hb⟩
  · rcases hk2 with ⟨h, hb⟩ | ⟨h, hb⟩
    · exact .inl ⟨((gxhGlblIs G cs e2 lbIsR lblRenIsR).1 h).2, hb⟩
    · exact .inr ⟨((gxhGlblIs G cs e2 lbIsW lblRenIsW).1 h).2, hb⟩

theorem hullGacqPo (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    gacqPo (gxHull G cs) e1 e2 → gacqPo G e1 e2 := by
  rintro ⟨hpo, h1, h2, h3⟩
  exact ⟨(hullGpo G cs e1 e2 hpo).1, ((gxhGlblIs G cs e1 lbIsR lblRenIsR).1 h1).2,
    ((gxhGlblIs G cs e1 lbAq lblRenAq).1 h2).2, ((gxhGmem G cs e2).1 h3).2⟩

theorem hullGrcsc (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    grcsc (gxHull G cs) e1 e2 → grcsc G e1 e2 := by
  rintro ⟨hpo, h1, h2⟩
  exact ⟨(hullGpo G cs e1 e2 hpo).1, ((gxhGlblIs G cs e1 lbRcsc lblRenRcsc).1 h1).2,
    ((gxhGlblIs G cs e2 lbRcsc lblRenRcsc).1 h2).2⟩

/-! # 2. The six arms -/

theorem hullCat6 (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    gloadValue G → hullOk G cs → gppoCat6 (gxHull G cs) e1 e2 →
    gppoCat6 G e1 e2 ∧ gcut cs e1 = true ∧ gcut cs e2 = true := by
  intro hlv hok h
  obtain ⟨-, hc1, hc2⟩ := hullGpo G cs e1 e2 (gppoCat6Gpo _ e1 e2 h)
  refine ⟨?_, hc1, hc2⟩
  rcases h with h | h | h | h | h | h
  · exact .inl (hullGppo1 G cs e1 e2 h)
  · exact .inr (.inl (hullGppo2 G cs e1 e2 h))
  · exact .inr (.inr (.inl (hullGppo3 G cs e1 e2 hlv hok h)))
  · exact .inr (.inr (.inr (.inl (hullGfence G cs e1 e2 h))))
  · exact .inr (.inr (.inr (.inr (.inl (hullGacqPo G cs e1 e2 h)))))
  · exact .inr (.inr (.inr (.inr (.inr (hullGrcsc G cs e1 e2 h)))))

/-! # 3. THE HULL LEMMA -/

/-- The cut's addr/data sublist: rule 12's domain in the hull. -/
def adCut (cs : List Nat) (ad : List (Geid × Geid)) : List (Geid × Geid) :=
  ad.filter (fun p : Geid × Geid => gcut cs p.1 && gcut cs p.2)

theorem adCutElem (cs : List Nat) (ad : List (Geid × Geid)) (p : Geid × Geid) :
    p ∈ adCut cs ad ↔ p ∈ ad ∧ gcut cs p.1 = true ∧ gcut cs p.2 = true := by
  simp [adCut, List.mem_filter]

/-- **W12 (3) THE HULL LEMMA.** -/
theorem hullCatAD (GD : Gdexec) (ad : List (Geid × Geid)) (cs : List Nat) :
    rvwmoCatAD GD ad → hullOk GD.gdG cs → rvwmoCatAD (gdHull GD cs) (adCut cs ad) := by
  rintro ⟨hwf, h6, hlv, hat, hdw, hdg, had, h12⟩ hok
  have hnd := hwf.1
  obtain ⟨hwf', hlv', hat'⟩ := WeakRvwmoHull.hullCoreG GD.gdG cs hwf hlv hat hok
  obtain ⟨-, -, -, hdw'⟩ := hullCoreD GD cs ⟨hwf, hlv, hat, hdw⟩ hok
  refine ⟨hwf', ?_, hlv', hat', hdw', ?_, ?_, ?_⟩
  · -- the six arms
    intro e1 e2 h
    obtain ⟨hG, hc1, hc2⟩ := hullCat6 GD.gdG cs e1 e2 hlv hok h
    exact (gxhGmoLt GD.gdG cs e1 e2 hnd).2 ⟨hc1, hc2, h6 e1 e2 hG⟩
  · -- the dependency fragment's gmo
    intro p hp
    obtain ⟨hp, hc1, hc2⟩ := (gdHullDeps GD cs p).1 hp
    exact (gxhGmoLt GD.gdG cs p.1 p.2 hnd).2 ⟨hc1, hc2, hdg p hp⟩
  · -- the sublist
    intro p hp
    obtain ⟨hp, hc1, hc2⟩ := (adCutElem cs ad p).1 hp
    exact (gdHullDeps GD cs p).2 ⟨had p hp, hc1, hc2⟩
  · -- rule 12
    rintro a b ⟨hag, m, hm, hrf⟩
    obtain ⟨hm, hca, -⟩ := (adCutElem cs ad (a, m)).1 hm
    obtain ⟨hrfG, -, hcb⟩ := hullGrf GD.gdG cs m b hlv hok hrf
    exact (gxhGmoLt GD.gdG cs a b hnd).2 ⟨hca, hcb, h12 a b ⟨hag, m, hm, hrfG⟩⟩

end CatLin

end Weak
