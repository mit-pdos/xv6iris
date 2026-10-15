/-
Weak: **W10 F1 [OWN.94] (N2′), increment 3 — the classification, supply and kill at PROTOCOL lock co**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

`GraphFetchN2` §4–§5 restated over `CertZ14.agreeRP2` (protocol lock co; `GraphFetchN2` untouched):
`CatLin.csHypsR2` (`csHypsR` + the section's release non-plain), `csHypsCertCR2` (through
`CatLin.csChainedT2`, the export's `wlpAt` threaded from `protReg`), `l2ClaimAtCZR2`/`l2ClaimCZR2`,
`certSupplyCZR2`, the two xv6 lock facts `acqAqCZ2`/`relCoversCZ2` (the same per-byte facts, at the
protocol agreement), `rawChainChainCZR2`, and **`CatLin.cycleKillOfL2CZRC2`** (the class kill, ending
at the unchanged `cycleKillIOC GF`).

Spec: FAITHFUL (proof organisation).
-/
import Weak.CertZ14

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

namespace CatLin

/-- `csHypsR` with the section's release NON-PLAIN (xv6: `release` is `fence rw,w; sw zero`,
the store stamped `WCrel` — `RelSiteProv.relPcWCrel`; not an AMO). -/
def csHypsR2 (GD : Gdexec) (GR : Gexec) (P : Int → Int → Prop) (log : List Wmsg) (prev : Geid)
    (s : Seg) : Prop :=
  ∃ (b a : Int) (ACQ REL : Geid),
    P a b ∧ lockWordByte log b ∧ (∃ v, gwritesByte GD.gdG prev a v) ∧
    gcls GD.gdG prev .WCplain ∧ gwix GR prev ≤ log.length ∧
    (∀ v, ¬ gwritesByte GD.gdG prev b v) ∧
    lockAcq GD.gdG b ACQ ∧ acqRow GD.gdG b ACQ ∧ glblIs GD.gdG ACQ lbAq ∧
    gwix GR ACQ ≤ log.length ∧
    lockCs GD.gdG b ACQ REL ∧ CertZ14.np GD.gdG REL ∧ WeakRvwmoGraph.gpo GD.gdG ACQ s.sgEntry ∧
    gfenceCovers GD.gdG s.sgEntry REL ∧
    WeakRvwmoGraph.gpo GD.gdG ACQ s.sgExit ∧ gmem GD.gdG s.sgExit ∧ ACQ.1 ≠ prev.1 ∧
    (∀ n0 r0, wprotAt log a b n0 r0 → r0 < gwix GR prev ∧ n0 < gwix GR ACQ)

theorem csHypsCertCR2 (GD : Gdexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (GR : Gexec) (P : Int → Int → Prop) (log : List Wmsg) (prev : Geid) (s : Seg) :
    rvwmoCatAD GD ad → (∀ x y, X x y → gmoLt GD.gdG x y) →
    gwf GR → CertZ14.agreeW2 GD.gdG GR (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    acqAqLog GD.gdG GR log P → relCoversLog GD.gdG GR log P →
    logOf GR log → protReg P log →
    csHypsR2 GD GR P log prev s → X prev s.sgEntry →
    CertC GD.gdG X prev s := by
  rintro hc hX hwfR hag hrowR hAQ hRC hlog hpr
    ⟨b, a, ACQ, REL, hP, hlwb, hwa, hcl, hlew, hnob, hacq, hrow, haq, hleA, hcs, hnpR, hpoe, hfen,
      hpox, hmx, hhart, hside⟩ hx
  obtain ⟨n0, r0, h, hprot, hat, halt⟩ := hpr a b hP
  obtain ⟨hr0, hn0A⟩ := hside n0 r0 hprot
  have hL : GraphFetchN2.lockBytes P b := ⟨a, hP⟩
  exact .CSchained (csChainedT2 GD ad GR (GraphFetchN2.lockBytes P) log b a n0 r0 h prev
    s.sgEntry s.sgExit ACQ REL hc hwfR hag hrowR hL (hAQ a b n0 r0 h hP hprot hat halt)
    (hRC a b n0 r0 h hP hprot hat halt) hlog hlwb halt hat hrow
    hprot hwa hcl hr0 hlew hnob hacq haq hn0A hleA hcs hnpR hpoe hfen (hX _ _ hx) hpox hmx hhart)

def l2ClaimAtCZR2 (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (P : Int → Int → Prop)
    (Bad : Prop) : Prop :=
  ∀ (log : List Wmsg) (z : Geid) (ss : List Seg),
    rvwmoCatAD GF.gfGd ad →
    logOf GR log →
    protReg P log →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ (prev : Geid) (s : Seg),
      s ∈ ss → ioCross GF prev s.sgEntry → segRunC GF.gfGd s →
      segPinC GF.gfGd ad s ∨ csHypsR2 GF.gfGd GR P log prev s ∨ Bad

/-- **THE L2′ CLAIM AT EVERY PROTOCOL-AGREEING MEMBER** (W11-F's obligation). -/
def l2ClaimCZR2 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) (Bad : Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (pi : Nat → Nat),
    GF.gfGd.gdG.gxImg = im → GraphFabConf.gfexecConfZF boot d0 fab GF →
    gwf GR → CertZ14.agreeRP2 GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    l2ClaimAtCZR2 GF ad GR P Bad

def certSupplyCZR2 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (cs : List Nat) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    properCutF GF cs → GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs →
    GraphFabConf.gfexecConfZF boot d0 fab (gfHull GF cs) →
    GraphFetchBlocks.emPremOk boot (gfHull GF cs).gfGd.gdG →
    (∀ x, ¬ tc (racyDIO (gfHull GF cs)) x x) →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab) (GR : Gexec) (pi : Nat → Nat),
      RunDataZ boot d0 N GF.gfGd.gdG c pst dv ∧
      logOf GR (cdLog c c.cdTr.length) ∧ gwf GR ∧
      CertZ14.agreeRP2 GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) ∧ gwrowGmo GR

/-- `acqAqCZ` at the protocol agreement (the same per-byte fact). -/
def acqAqCZ2 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (pi : Nat → Nat) (log : List Wmsg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    gwf GR → CertZ14.agreeRP2 GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    logOf GR log → protReg P log →
    acqAqLog GF.gfGd.gdG GR log P

/-- `relCoversCZ` at the protocol agreement (the same per-byte fact). -/
def relCoversCZ2 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (pi : Nat → Nat) (log : List Wmsg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    gwf GR → CertZ14.agreeRP2 GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    logOf GR log → protReg P log →
    relCoversLog GF.gfGd.gdG GR log P

theorem rawChainChainCZR2 (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (pi : Nat → Nat)
    (P : Int → Int → Prop) (log : List Wmsg) (Bad : Prop) (ss : List Seg) :
    rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    gwf GR → CertZ14.agreeRP2 GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    acqAqLog GF.gfGd.gdG GR log P → relCoversLog GF.gfGd.gdG GR log P →
    logOf GR log → protReg P log → ¬ Bad →
    (∀ prev s, s ∈ ss → ioCross GF prev s.sgEntry → segRunC GF.gfGd s →
       segPinC GF.gfGd ad s ∨ csHypsR2 GF.gfGd GR P log prev s ∨ Bad) →
    ∀ (x y : Geid) (ss' : List Seg),
      ss' ⊆ ss → rawChainC GF.gfGd (ioCross GF) x y ss' →
      chainC GF.gfGd.gdG (ioCross GF) x y ss' := by
  intro hc hres hdr hwfR hagR hrowR hAQ hRC hlog hpr hnB hcl x y ss'
  have hX : ∀ x y, ioCross GF x y → gmoLt GF.gfGd.gdG x y :=
    ioCrossGmo GF hc.1 hc.2.2.1 hres hdr
  have hag := CertZ14.agreeW2OfRP2 _ _ _ _ hagR
  induction ss' generalizing x with
  | nil => intro _ hch; exact hch
  | cons s ss' ih =>
    intro hsub hch
    obtain ⟨hx, hrun, hrest⟩ := hch
    have hs : s ∈ ss := hsub (by simp)
    have hsub' : ss' ⊆ ss := by
      intro t ht
      exact hsub (List.mem_cons_of_mem s ht)
    show CertC GF.gfGd.gdG (ioCross GF) x s ∧ chainC GF.gfGd.gdG (ioCross GF) s.sgExit y ss'
    refine ⟨?_, ih _ hsub' hrest⟩
    rcases hcl x s hs hx hrun with hp | hcs | hb
    · exact segPinCCert GF.gfGd ad _ x s hc hx hp
    · exact csHypsCertCR2 GF.gfGd ad _ GR P log x s hc hX hwfR hag hrowR hAQ hRC hlog hpr hcs hx
    · exact absurd hb hnB

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **`cycleKillOfL2CZRC2`** — the class kill at PROTOCOL lock co. -/
theorem cycleKillOfL2CZRC2 (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    cutSupplyCZC boot d0 fab (imgZ σ0.wgimg) →
    certSupplyCZR2 boot d0 fab (imgZ σ0.wgimg) N P →
    acqAqCZ2 boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ2 boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR2 boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) := by
  intro hfr hb1 hb2 hwp hwpp hcov hcut hcert hAQ hRC hl2
  intro GF ad him hc hconf hres hdr hIH x hcyc
  obtain ⟨z, ss, hne, hch⟩ := cycleSegmentsIO GF ad x hc hcyc
  obtain ⟨cs, hcutok, hdc, hcl, hprem⟩ := hcut GF ad z ss him hc hconf hne hch
  have hcore := catADCore _ _ hc
  have hconfH :=
    GraphFetchHullZ.gfexecConfZFHull boot d0 fab GF cs hcore.1 hcore.2.1 hcutok.1 hdc hconf hcl
  have hpc := GraphFetchKill.properCutFOfCut GF cs hcutok hdc
  have hacyH := hIH cs hpc hcl
  obtain ⟨c, pst, dv, GR, pi, hrd, hlog, hwfR, hagR, hrowR⟩ :=
    hcert GF ad cs z ss him hc hconf hres hdr hpc hcl hconfH hprem hacyH hne hch
  obtain ⟨t2, σ2, hrtc, hlgeq⟩ :=
    runErasedZ gen σ0 boot d0 N GF.gfGd.gdG c pst dv hfr hcov hb1 hb2 him hrd
  have hpr : protReg P (cdLog c c.cdTr.length) := by
    rw [← hlgeq]
    exact protRegOfRun hlc GF0 gen σ0 D hD Nm P t2 σ2 hfr hwpp hrtc
  have hnB : ¬ badRun gen σ0 := noBadRun hlc GF0 gen σ0 D hD hfr hwp
  exact cycleKillIOC GF ad z ss hc hres hdr hne
    (rawChainChainCZR2 GF ad GR pi P (cdLog c c.cdTr.length) (badRun gen σ0) ss hc hres hdr hwfR
      hagR hrowR (hAQ GF ad GR pi _ him hc hconf hwfR hagR hrowR hlog hpr)
      (hRC GF ad GR pi _ him hc hconf hwfR hagR hrowR hlog hpr) hlog hpr hnB
      (hl2 GF ad GR pi him hconf hwfR hagR hrowR (cdLog c c.cdTr.length) z ss hc hlog hpr hne
        hch) z z ss (fun _ h => h) hch)

end glue

end CatLin

end Weak
