/-
Weak: **allocproc route P, row P-W6 — THE KILL'S NAMED RUN FACTS OVER GATED S-R MEMBERS** (coordinator decision
(2) of the P-W6b prompt, APPROVED: the restatement of `SbKill.memberRunCZ` / `SbKill.l2ClaimP` over GATED R-walk
members; `PROGRESS-PW6.md` design check).  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports
this file.

**Why.**  The capstone kill `SbKillR.cycleKillAllR` takes its named run facts (`SbKill.memberRunCZ`: `protRegZB`,
`lockRealB`, `csIssue`; `SbKill.l2ClaimP`) at EVERY `SbKill.finishedP` candidate — valid, drained, agreeing with
GF — but it only ever USES them at the member `SbKillR.certSupplyOfWalkR` supplies, a FINISHED GATED S-R walk.
P-W6's realization (MachCSL runs the walk) exists only for gated members: it needs the S-R gate at every item
(`SbOrdR.gatedWR`: the [OWN.151] device unit, the [OWN.152] I/O gate, `landR`'s GF write order), the walk
invariant at every prefix (`SbOrdR.PInvR`: `IssueCo`'s census `SbIssueCoR.issueCoOfCustodyR` reads it at every
issue), finding F-PW6-1.  So the named premises are restated over

  `finishedR GF X c := finishedP GF X c ∧ gatedWR G X dev c ∧ ∀ k ≤ |c|, PInvR (stAt c k)`,

which is WEAKER (asked at fewer candidates: `memberRunCZOfP`, `l2ClaimOfP`), and the kill is unchanged
(`cycleKillCoreR` is `SbKill.cycleKillCoreP`'s argument at the supplied member).

  §1  `pinvAll` (the walk invariant at every prefix) and **`walkRunRP`** (`SbOrdR.walkRunR` carrying it).
  §2  `finishedR`, `certSupplyR`, `memberRunCZR`, `l2ClaimPR`; the weakening lemmas.
  §3  **`cycleKillCoreR`**, **`certSupplyOfWalkRG`**, `cycleKillOfWalkRG`, **`cycleKillAllRG`** — the shape
      `CapFetchProv.t2linSupplyCZTtagged` consumes, with the restated premises.

Spec: FAITHFUL (proof organisation; the restated premises are WEAKER).  Lean-only helpers `SbKillRG.*`.
-/
import Weak.SbKillR

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl SbWalk SbAgree SbReplay SbOrd

namespace SbKillRG

/-! # 1. The walk invariant at every prefix -/

/-- **THE S-R WALK INVARIANT AT EVERY PREFIX STATE** of the candidate. -/
def pinvAll (N : Nat) (img : Image) (G : Gexec) (X : Geid → Prop) (dev : List Geid) (c : CandW) : Prop :=
  ∀ k, k ≤ c.its.length → SbOrdR.PInvR N img G X dev (stAt c k)

theorem pinvAllNil (N : Nat) (img : Image) (G : Gexec) (hwf : gwf G) (X : Geid → Prop) (dev : List Geid) :
    pinvAll N img G X dev ⟨img, []⟩ := by
  intro k hk
  have hk0 : k = 0 := by simp at hk; omega
  subst hk0
  exact SbOrdR.pinvInitR N img G hwf X dev

theorem pinvAllSnoc {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} (c : CandW)
    (it : Item) (h : pinvAll N img G X dev c) (h' : SbOrdR.PInvR N img G X dev (cur (snocC c it))) :
    pinvAll N img G X dev (snocC c it) := by
  intro k hk
  have hlen : (snocC c it).its.length = c.its.length + 1 := by simp [snocC]
  by_cases hle : k ≤ c.its.length
  · rw [stAtSnoc c it k hle]; exact h k hle
  · have hk : k = (snocC c it).its.length := by omega
    subst hk
    exact h'

theorem pinvAllCur {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} (c : CandW)
    (h : pinvAll N img G X dev c) : SbOrdR.PInvR N img G X dev (cur c) := h _ (Nat.le_refl _)

theorem nonFinalRG {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}
    (hP : SbOrdR.PInvR N img G X dev w)
    (hfin : ¬ ((∀ x, x < N → (w.rows x).length = (G.gxProg.getD x []).length) ∧ drained w)) :
    (∃ x, x < N ∧ (w.rows x).length < (G.gxProg.getD x []).length) ∨ (∃ i, w.pend i ≠ []) := by
  by_cases h1 : ∀ x, x < N → (w.rows x).length = (G.gxProg.getD x []).length
  · have h2 : ¬ drained w := fun h => hfin ⟨h1, h⟩
    obtain ⟨i, hi⟩ : ∃ i, w.pend i ≠ [] :=
      Classical.byContradiction (fun hn => h2 (fun i => Classical.byContradiction (fun h => hn ⟨i, h⟩)))
    exact .inr ⟨i, hi⟩
  · obtain ⟨x, hx, hne⟩ : ∃ x, x < N ∧ (w.rows x).length ≠ (G.gxProg.getD x []).length :=
      Classical.byContradiction (fun hn => h1 (fun x hx =>
        Classical.byContradiction (fun h => hn ⟨x, hx, h⟩)))
    exact .inl ⟨x, hx, by have := hP.len x; omega⟩

/-- **`walkRunRP` — THE S-R WALK RUNS TO COMPLETION, its invariant at EVERY prefix** (`SbOrdR.walkRunR`). -/
theorem walkRunRP (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop)
    (hW : WalkHyp GF N img X) (hNA : SbOrdR.NoAqLd GF.gfGd.gdG)
    (hS : ∀ c, validW SbPol.epoch c → SbOrdR.gatedWR GF.gfGd.gdG X GF.gfDev c → c.img = img →
      SbOrdR.PInvR N img GF.gfGd.gdG X GF.gfDev (cur c) → SbOrdR.StateIfcR GF.gfGd.gdG X GF.gfDev c) :
    ∃ c, c.img = img ∧ validW SbPol.epoch c ∧ pinvAll N img GF.gfGd.gdG X GF.gfDev c ∧
      (∀ x, x < N → ((cur c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
      drained (cur c) ∧ SbOrdR.gatedWR GF.gfGd.gdG X GF.gfDev c := by
  suffices H : ∀ n c, validW SbPol.epoch c → SbOrdR.gatedWR GF.gfGd.gdG X GF.gfDev c → c.img = img →
      pinvAll N img GF.gfGd.gdG X GF.gfDev c → work N GF.gfGd.gdG (cur c) ≤ n →
      ∃ c', c'.img = img ∧ validW SbPol.epoch c' ∧ pinvAll N img GF.gfGd.gdG X GF.gfDev c' ∧
        (∀ x, x < N → ((cur c').rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur c') ∧ SbOrdR.gatedWR GF.gfGd.gdG X GF.gfDev c' by
    exact H _ ⟨img, []⟩ (fun k it h => by simp at h) (SbOrdR.gatedNilR _ X _ img) rfl
      (pinvAllNil N img _ hW.cat.wf X _) (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro c hv hg hc hA hw
    have hP := pinvAllCur c hA
    by_cases hfin : (∀ x, x < N → ((cur c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur c)
    · exact ⟨c, hc, hv, hA, hfin.1, hfin.2, hg⟩
    · exfalso
      obtain ⟨T, hT, he⟩ := SbOrdR.noStuckR GF N img X (cur c) hW.cat hW.io hW.wio hW.imgF hNA hW.len hP
        hW.devSt hW.devFab hW.hart (hS c hv hg hc hP).head (nonFinalRG hP hfin)
      subst hc
      obtain ⟨it, -, -, hlt, -⟩ := SbOrdR.walkStepR GF N X c hW hv hP (hS c hv hg rfl hP).exv T hT he
      omega
  | succ n ih =>
    intro c hv hg hc hA hw
    have hP := pinvAllCur c hA
    by_cases hfin : (∀ x, x < N → ((cur c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur c)
    · exact ⟨c, hc, hv, hA, hfin.1, hfin.2, hg⟩
    · obtain ⟨T, hT, he⟩ := SbOrdR.noStuckR GF N img X (cur c) hW.cat hW.io hW.wio hW.imgF hNA hW.len hP
        hW.devSt hW.devFab hW.hart (hS c hv hg hc hP).head (nonFinalRG hP hfin)
      subst hc
      obtain ⟨it, hv', hP', hlt, hit⟩ := SbOrdR.walkStepR GF N X c hW hv hP (hS c hv hg rfl hP).exv T hT he
      exact ih (snocC c it) hv' (SbOrdR.gatedSnocR _ X _ c it hg (by rw [hit]; exact he)) rfl
        (pinvAllSnoc c it hA hP') (by omega)

/-! # 2. Gated finished members and the restated named premises -/

/-- **A FINISHED GATED S-R MEMBER** of `GF`: `SbKill.finishedP`, the S-R gate at every item, the S-R walk
invariant at every prefix. -/
def finishedR (GF : Gfexec) (X : Geid → Prop) (c : CandW) : Prop :=
  SbKill.finishedP GF X c ∧ SbOrdR.gatedWR GF.gfGd.gdG X GF.gfDev c ∧
  pinvAll GF.gfGd.gdG.gxProg.length c.img GF.gfGd.gdG X GF.gfDev c

theorem finishedROfP (GF : Gfexec) (X : Geid → Prop) (c : CandW) : finishedR GF X c → SbKill.finishedP GF X c :=
  fun h => h.1

/-- **(G-3) at gated S-R members**: a finished gated member for every class graph. -/
def certSupplyR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → ∃ c, finishedR GF (Xof GF) c

/-- **`SbKill.memberRunCZ` RESTATED OVER GATED S-R MEMBERS (NAMED; P-W5/P-W6/6j)**. -/
def memberRunCZR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : CandW),
    GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    finishedR GF (Xof GF) c →
    SbKill.protRegZB P im (logP c) ∧
    SbKill.lockRealB (memberP GF.gfGd.gdG.gxProg.length c) (logP c) P ∧
    ∀ b n0, SbKill.csIssue P GF.gfGd.gdG (memberP GF.gfGd.gdG.gxProg.length c) (logP c) b n0

/-- **`SbKill.l2ClaimP` RESTATED OVER GATED S-R MEMBERS (NAMED; W11-F, row 6n)**. -/
def l2ClaimPR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : CandW),
    GF.gfGd.gdG.gxImg = im → GraphFabConf.gfexecConfZF boot d0 fab GF →
    CapFetchProv.provAll boot GF.gfGd →
    finishedR GF (Xof GF) c →
    SbKill.l2ClaimAtP GF ad (memberP GF.gfGd.gdG.gxProg.length c) P Bad

/-- The restated run facts are WEAKER than the old ones. -/
theorem memberRunCZOfP (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (h : SbKill.memberRunCZ boot d0 fab im Xof P) :
    memberRunCZR boot d0 fab im Xof P :=
  fun GF ad c him hc hconf hfin => h GF ad c him hc hconf hfin.1

/-- The restated L2′ claim is WEAKER than the old one. -/
theorem l2ClaimOfP (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop)
    (h : SbKill.l2ClaimP boot d0 fab im Xof P Bad) : l2ClaimPR boot d0 fab im Xof P Bad :=
  fun GF ad c him hconf hprov hfin => h GF ad c him hconf hprov hfin.1

/-! # 3. The kill over gated members -/

/-- **`cycleKillCoreR` — THE TRIMMED CLASS KILL FROM GATED S-R MEMBERS** (`SbKill.cycleKillCoreP`'s argument at
the supplied member). -/
theorem cycleKillCoreR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop)
    (hsup : certSupplyR boot d0 fab im Xof)
    (hM : memberRunCZR boot d0 fab im Xof P)
    (hl2 : l2ClaimPR boot d0 fab im Xof P Bad) (hnB : ¬ Bad) :
    CatLin.cycleKillCZT boot d0 fab im := by
  intro GF ad him hc hconf hres hdr hprov _ x hcyc
  obtain ⟨z, ss, hne, hch⟩ := cycleSegmentsIO GF ad x hc hcyc
  obtain ⟨c, hfinR⟩ := hsup GF ad him hc hconf hres
  obtain ⟨hpr, hreal, hiss⟩ := hM GF ad c him hc hconf hfinR
  obtain ⟨-, -, -, hwfR, hlog, hlat, hagX⟩ := hfinR.1
  have himR : (memberP GF.gfGd.gdG.gxProg.length c).gxImg = im := hagX.1.trans him
  have hprR : SbKill.protRegZB P (memberP GF.gfGd.gdG.gxProg.length c).gxImg (logP c) := by
    rw [himR]; exact hpr
  have hcl := hl2 GF ad c him hconf hprov hfinR (logP c) z ss hc hlog hprR hne hch
  exact cycleKillIOC GF ad z ss hc hres hdr hne
    (SbKill.rawChainChainP GF ad _ (Xof GF) P (logP c) Bad ss hc hres hdr hwfR hagX hlat
      (SbKill.acqAqLogOfRealX _ _ (Xof GF) _ P hagX hwfR hlog hreal)
      (SbKill.relCoversLogOfRealX _ _ (Xof GF) _ P hagX hwfR hreal) hiss hlog hprR hnB
      hcl z z ss (fun _ h => h) hch)

/-- **THE GATED SUPPLY FROM THE S-R WALK** (`SbKillR.certSupplyOfWalkR`, the member also gated and carrying
`PInvR` at every prefix: `walkRunRP`). -/
theorem certSupplyOfWalkRG (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : CatLin.gfDevWIoCZ boot d0 fab im) (hdf : SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : SbKillR.walkHypCZR boot d0 fab im Xof) (hS : SbKillR.stateIfcCZR boot d0 fab im Xof) :
    certSupplyR boot d0 fab im Xof := by
  intro GF ad him hc hconf hres
  obtain ⟨hI, hDS, hDF, hex, hdef⟩ :=
    SbDevSt.walkHypAt boot d0 fab im Xof hdb hwio hdf hW.1 GF ad him hc hconf hres
  have hWH : WalkHyp GF GF.gfGd.gdG.gxProg.length im (Xof GF) :=
    { cat := ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
      io := hres
      wio := hwio GF ad him hc hconf
      imgF := hI
      devSt := hDS
      devFab := hDF
      hart := LockFacts3.hartDevIo boot d0 fab GF hconf hbt
      len := rfl
      imgEq := him
      ex := hex
      def' := hdef }
  obtain ⟨c, hcimg, hv, hA, hfin, hdr, hg⟩ :=
    walkRunRP GF _ im (Xof GF) hWH (hW.2 GF ad him hc hconf) (fun c hv hg hci hP =>
      let h := hS GF ad him hc hconf hres c hv hg hci hP
      ⟨h.1, h.2⟩)
  have hPc : SbOrdR.PInvR GF.gfGd.gdG.gxProg.length c.img GF.gfGd.gdG (Xof GF) GF.gfDev (cur c) := by
    rw [hcimg]; exact pinvAllCur c hA
  obtain ⟨hgwf, hlog, hlat, hagX, -⟩ :=
    SbOrdR.memberOfRunR SbPol.epoch _ _ (Xof GF) _ c hv hWH.cat.wf (hWH.imgEq.trans hcimg.symm) rfl hPc hfin hdr
  exact ⟨c, ⟨hcimg.trans him.symm, hv, hdr, hgwf, hlog, hlat, hagX⟩, hg, by rw [hcimg]; exact hA⟩

/-- **… the kill** from the S-R walk, with the restated (gated) run facts. -/
theorem cycleKillOfWalkRG (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : CatLin.gfDevWIoCZ boot d0 fab im) (hdf : SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : SbKillR.walkHypCZR boot d0 fab im Xof) (hS : SbKillR.stateIfcCZR boot d0 fab im Xof)
    (hM : memberRunCZR boot d0 fab im Xof P)
    (hl2 : l2ClaimPR boot d0 fab im Xof P Bad) (hnB : ¬ Bad) :
    CatLin.cycleKillCZT boot d0 fab im :=
  cycleKillCoreR boot d0 fab im Xof P Bad
    (certSupplyOfWalkRG boot d0 fab im Xof hbt hdb hwio hdf hW hS) hM hl2 hnB

/-- **THE SHAPE `CapFetchProv.t2linSupplyCZTtagged` CONSUMES**, from the S-R walk with the restated premises
(`SbKillR.cycleKillAllR` with `memberRunCZR` / `l2ClaimPR` in place of `memberRunCZ` / `l2ClaimP`). -/
theorem cycleKillAllRG (boot : Nat → Pexv6) (d0 : Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : ∀ fab, CatLin.gfDevWIoCZ boot d0 fab im) (hdf : ∀ fab, SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : ∀ fab, SbKillR.walkHypCZR boot d0 fab im Xof) (hS : ∀ fab, SbKillR.stateIfcCZR boot d0 fab im Xof)
    (hM : ∀ fab, memberRunCZR boot d0 fab im Xof P)
    (hl2 : ∀ fab, l2ClaimPR boot d0 fab im Xof P Bad) (hnB : ¬ Bad) :
    ∀ fab, CatLin.cycleKillCZT boot d0 fab im :=
  fun fab => cycleKillOfWalkRG boot d0 fab im Xof P Bad hbt hdb (hwio fab) (hdf fab) (hW fab)
    (hS fab) (hM fab) (hl2 fab) hnB

#print axioms Weak.SbKillRG.cycleKillAllRG

end SbKillRG

end Weak
