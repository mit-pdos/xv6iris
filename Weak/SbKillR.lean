/-
Weak: **the S-R `DomAt` lift, increment I-5 (1/2) — `SbKillR`, THE KILL FROM THE S-R WALK** (ruling
[OWN.150]; `PROGRESS-DomAt.md` §0.2).  Lean-only, no Rocq twin.  A leaf: nothing registered imports this
file.

**Spec, stated first.**  The kill (`CatLin.cycleKillCZT`) needs, at every class graph, a FINISHED member of
the twin agreeing with GF (`SbKill.certSupplyP`).  This file supplies it from the S-R walk (`SbOrdR.walkRunR`,
`memberOfCatR`) instead of the top-read walk: the same consumer shape, with the S-R per-state interfaces
(`stateIfcCZR`: row H3′ `HeadOrdW` and the min-rule exempt value `ExValMin`) in place of `HeadOrdRd` and
`ExValTop`, and the census `NoAqLd` beside the image facts.  `HeadOrdW` follows from the per-head STATIC
WRITE HOP (`SbHeadHop.WrHop`, rules 11 / 4) and (R1) alone (`headOrdWOf`) — no (A2) read window.

  §1  **`SbOrdR.headOrdWOf`**: `HeadOrdW` from `WrHop` at every blocked head, (R1), `gfDevWIo`.
  §2  the consumer forms: `walkHypCZR`, `stateIfcCZR`, **`certSupplyOfWalkR`**, **`cycleKillOfWalkR`**,
      `cycleKillAllR` (`SbDevSt`'s `DevStOrd` discharge kept).

Spec: FAITHFUL (proof organisation).  Lean-only helpers `SbOrdR.*`, `SbKillR.*`.
-/
import Weak.SbWalkR
import Weak.SbDevSt
import Weak.SbHeadHop

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl SbWalk SbAgree SbReplay SbOrd

/-! # 1. Row H3′ from the static write hop -/

/-- **ROW H3′ FROM THE STATIC WRITE HOP**: if every blocked non-exempt plain-load head has `WrHop`
(rules 11 / 4 at its site), it is gmo-before every later write (that hop) and every later fabric member
(a write, or an I/O event: (R1)). -/
theorem SbOrdR.headOrdWOf (G : Gexec) (X : Geid → Prop) (dev : List Geid) (w : WS) (hc : CatH G)
    (hr1 : ∀ s m, WeakRvwmoGraph.gpo G s m → gmem G s → gisIo G s = false → gisIo G m = true →
      gmoLt G s m)
    (hwio2 : ∀ d, d ∈ dev → gisWIo G d = true)
    (hA1 : ∀ x base ts vs, gxLbl G (hd w x) = some (LLoad false base ts vs) → ¬ X (hd w x) →
      ¬ SbOrdR.srGate G w x false base ts vs → SbHeadHop.WrHop G (hd w x)) :
    SbOrdR.HeadOrdW G X dev w := by
  intro x base ts vs hl hX hns m hm hmx hlt hwo
  obtain ⟨lm, hlm, hmm⟩ := gwfGmoMem G m hc.wf hm
  have hpo : WeakRvwmoGraph.gpo G (hd w x) m :=
    SbHeadHop.gpoOfLbl G _ m _ lm hl hlm (by unfold hd; exact hmx.symm) hlt
  have hwr : gisW G m = true → gmoLt G (hd w x) m := fun h => hA1 x base ts vs hl hX hns m hpo h
  rcases hwo with hd' | hW
  · have hwi := hwio2 m hd'
    unfold gisWIo at hwi
    simp only [Bool.or_eq_true] at hwi
    rcases hwi with h | h
    · exact hwr h
    · exact hr1 _ m hpo ⟨_, hl, by simp [lbIsMem, lbIsR]⟩ (by unfold gisIo; rw [hl]; rfl) h
  · exact hwr hW

/-! # 2. The consumer forms -/

/-- **THE S-R WALK'S CLASS-LEVEL INPUTS (NAMED)**: `SbDevSt.walkHypCZD`'s (the image facts, exempt reads are
plain loads, the image defined at read bytes) and the census `NoAqLd` (finding F-DomAt-1). -/
def SbKillR.walkHypCZR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) : Prop :=
  SbDevSt.walkHypCZD boot d0 fab im Xof ∧
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    SbOrdR.NoAqLd GF.gfGd.gdG

/-- **THE S-R PER-STATE INTERFACES (NAMED)**: row H3′ (`HeadOrdW`) and the min-rule exempt value
(`ExValMin`) at every reachable GATED S-R candidate. -/
def SbKillR.stateIfcCZR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF →
    ∀ c, validW SbPol.epoch c → SbOrdR.gatedWR GF.gfGd.gdG (Xof GF) GF.gfDev c → c.img = im →
      SbOrdR.PInvR GF.gfGd.gdG.gxProg.length im GF.gfGd.gdG (Xof GF) GF.gfDev (cur c) →
      SbOrdR.HeadOrdW GF.gfGd.gdG (Xof GF) GF.gfDev (cur c) ∧ SbOrdR.ExValMin GF.gfGd.gdG (Xof GF) (cur c)

/-- **THE SUPPLY FROM THE S-R WALK** (`DevStOrd` discharged as in `SbDevSt.certSupplyOfWalkPD`). -/
theorem SbKillR.certSupplyOfWalkR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : CatLin.gfDevWIoCZ boot d0 fab im) (hdf : SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : SbKillR.walkHypCZR boot d0 fab im Xof) (hS : SbKillR.stateIfcCZR boot d0 fab im Xof) :
    SbKill.certSupplyP boot d0 fab im Xof := by
  intro GF ad him hc hconf hres
  obtain ⟨hI, hDS, hex, hdef⟩ :=
    SbDevSt.walkHypAt boot d0 fab im Xof hdb hwio hdf hW.1 GF ad him hc hconf hres
  have hWH : WalkHyp GF GF.gfGd.gdG.gxProg.length im (Xof GF) :=
    { cat := ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
      io := hres
      wio := hwio GF ad him hc hconf
      imgF := hI
      devSt := hDS
      hart := LockFacts3.hartDevIo boot d0 fab GF hconf hbt
      len := rfl
      imgEq := him
      ex := hex
      def' := hdef }
  obtain ⟨c, hcimg, hv, hdr, hgwf, hlog, hlat, hagX, -⟩ :=
    SbOrdR.memberOfCatR GF _ im (Xof GF) hWH (hW.2 GF ad him hc hconf) (fun c hv hg hci hP =>
      let h := hS GF ad him hc hconf hres c hv hg hci hP
      ⟨h.1, h.2⟩)
  exact ⟨c, hcimg.trans him.symm, hv, hdr, hgwf, hlog, hlat, hagX⟩

/-- **… the kill** (`SbKill.cycleKillCoreP` from the S-R supply). -/
theorem SbKillR.cycleKillOfWalkR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : CatLin.gfDevWIoCZ boot d0 fab im) (hdf : SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : SbKillR.walkHypCZR boot d0 fab im Xof) (hS : SbKillR.stateIfcCZR boot d0 fab im Xof)
    (hM : SbKill.memberRunCZ boot d0 fab im Xof P)
    (hl2 : SbKill.l2ClaimP boot d0 fab im Xof P Bad) (hnB : ¬ Bad) :
    CatLin.cycleKillCZT boot d0 fab im :=
  SbKill.cycleKillCoreP boot d0 fab im Xof P Bad
    (SbKillR.certSupplyOfWalkR boot d0 fab im Xof hbt hdb hwio hdf hW hS) hM hl2 hnB

/-- **THE SHAPE `CapFetchProv.t2linSupplyCZTtagged` CONSUMES**, from the S-R walk. -/
theorem SbKillR.cycleKillAllR (boot : Nat → Pexv6) (d0 : Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : ∀ fab, CatLin.gfDevWIoCZ boot d0 fab im) (hdf : ∀ fab, SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : ∀ fab, SbKillR.walkHypCZR boot d0 fab im Xof) (hS : ∀ fab, SbKillR.stateIfcCZR boot d0 fab im Xof)
    (hM : ∀ fab, SbKill.memberRunCZ boot d0 fab im Xof P)
    (hl2 : ∀ fab, SbKill.l2ClaimP boot d0 fab im Xof P Bad) (hnB : ¬ Bad) :
    ∀ fab, CatLin.cycleKillCZT boot d0 fab im :=
  fun fab => SbKillR.cycleKillOfWalkR boot d0 fab im Xof P Bad hbt hdb (hwio fab) (hdf fab) (hW fab)
    (hS fab) (hM fab) (hl2 fab) hnB

end Weak
