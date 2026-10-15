/-
Weak: **W10 F1 [OWN.94] (N2′), decision (A), step 2 — classification, supply and kill UP TO FAILED
ACQUIRES** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

`CertZ19` restated over the padded agreement `CertZ24.agreeRP4`: `CatLin.csHypsR4` (`csHypsR4` + the
section's acquire and the plain write are no failed acquires), `csHypsCertCR4` (through
`CatLin.csChainedT4`), `l2ClaimAtCZR4`/`l2ClaimCZR4`, `certSupplyCZR4` (the PADDED member),
`acqAqCZ4`/`relCoversCZ4`, `rawChainChainCZR4`, and **`CatLin.cycleKillOfL2CZRC4`**.

Spec: FAITHFUL (proof organisation).
-/
import Weak.CertZ24

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

namespace CatLin

/-- `csHypsR2` with the section's acquire and the plain write NO failed acquires (xv6: a successful
`amoswap.w.aq`; a plain store reads nothing). -/
def csHypsR4 (GD : Gdexec) (GR : Gexec) (P : Int → Int → Prop) (log : List Wmsg) (prev : Geid)
    (s : Seg) : Prop :=
  csHypsR2 GD GR P log prev s ∧
  ∀ (b a : Int) (ACQ : Geid), P a b → acqRow GD.gdG b ACQ →
    CertZ24.nf GD.gdG (GraphFetchN2.lockBytes P) ACQ ∧ CertZ24.nf GD.gdG (GraphFetchN2.lockBytes P) prev

theorem csHypsCertCR4 (GD : Gdexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (GR : Gexec) (P : Int → Int → Prop) (log : List Wmsg) (prev : Geid) (s : Seg) :
    rvwmoCatAD GD ad → (∀ x y, X x y → gmoLt GD.gdG x y) →
    gwf GR → CertZ24.agreeW4 GD.gdG GR (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    CertZ18.rmwLatest GR log →
    acqAqLog GD.gdG GR log P → relCoversLog GD.gdG GR log P →
    logOf GR log → CertZ18.protRegZ P GR.gxImg log →
    csHypsR4 GD GR P log prev s → X prev s.sgEntry →
    CertC GD.gdG X prev s := by
  rintro hc hX hwfR hag hrowR hlat hAQ hRC hlog hpr
    ⟨⟨b, a, ACQ, REL, hP, hlwb, hwa, hcl, hlew, hnob, hacq, hrow, haq, hleA, hcs, hnpR, hpoe, hfen,
      hpox, hmx, hhart, hside⟩, hnf⟩ hx
  obtain ⟨hnfA, hnfw⟩ := hnf b a ACQ hP hrow
  obtain ⟨n0, r0, h, hprot, hat, halt, hz⟩ := hpr a b hP
  obtain ⟨hr0, hn0A⟩ := hside n0 r0 hprot
  have hL : GraphFetchN2.lockBytes P b := ⟨a, hP⟩
  exact .CSchained (csChainedT4 GD ad GR (GraphFetchN2.lockBytes P) log b a n0 r0 h prev
    s.sgEntry s.sgExit ACQ REL hc hwfR hag hrowR hL hlat hz (hAQ a b n0 r0 h hP hprot hat halt)
    (hRC a b n0 r0 h hP hprot hat halt) hlog hlwb halt hat hrow hnfA hnfw
    hprot hwa hcl hr0 hlew hnob hacq haq hn0A hleA hcs hnpR hpoe hfen (hX _ _ hx) hpox hmx hhart)

def l2ClaimAtCZR4 (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (P : Int → Int → Prop)
    (Bad : Prop) : Prop :=
  ∀ (log : List Wmsg) (z : Geid) (ss : List Seg),
    rvwmoCatAD GF.gfGd ad →
    logOf GR log →
    CertZ18.protRegZ P GR.gxImg log →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ (prev : Geid) (s : Seg),
      s ∈ ss → ioCross GF prev s.sgEntry → segRunC GF.gfGd s →
      segPinC GF.gfGd ad s ∨ csHypsR4 GF.gfGd GR P log prev s ∨ Bad

/-- **THE L2′ CLAIM AT EVERY SUCCESSFUL-PROTOCOL-AGREEING MEMBER** (W11-F's obligation). -/
def l2ClaimCZR4 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) (Bad : Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (pi : Nat → Nat),
    GF.gfGd.gdG.gxImg = im → GraphFabConf.gfexecConfZF boot d0 fab GF →
    gwf GR → CertZ24.agreeRP4 GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    l2ClaimAtCZR4 GF ad GR P Bad

/-- (G-3) at a member agreeing at successful-protocol co, with its RMW atomicity. -/
def certSupplyCZR4 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
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
      CertZ24.agreeRP4 GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) ∧ gwrowGmo GR ∧
      CertZ18.rmwLatest GR (cdLog c c.cdTr.length)

/-- `acqAqCZ2` at the successful-protocol agreement (the same per-byte fact). -/
def acqAqCZ4 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (pi : Nat → Nat) (log : List Wmsg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    gwf GR → CertZ24.agreeRP4 GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    logOf GR log → CertZ18.protRegZ P GR.gxImg log →
    acqAqLog GF.gfGd.gdG GR log P

/-- `relCoversCZ2` at the successful-protocol agreement (the same per-byte fact). -/
def relCoversCZ4 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (pi : Nat → Nat) (log : List Wmsg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    gwf GR → CertZ24.agreeRP4 GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    logOf GR log → CertZ18.protRegZ P GR.gxImg log →
    relCoversLog GF.gfGd.gdG GR log P

theorem rawChainChainCZR4 (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (pi : Nat → Nat)
    (P : Int → Int → Prop) (log : List Wmsg) (Bad : Prop) (ss : List Seg) :
    rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    gwf GR → CertZ24.agreeRP4 GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    CertZ18.rmwLatest GR log →
    acqAqLog GF.gfGd.gdG GR log P → relCoversLog GF.gfGd.gdG GR log P →
    logOf GR log → CertZ18.protRegZ P GR.gxImg log → ¬ Bad →
    (∀ prev s, s ∈ ss → ioCross GF prev s.sgEntry → segRunC GF.gfGd s →
       segPinC GF.gfGd ad s ∨ csHypsR4 GF.gfGd GR P log prev s ∨ Bad) →
    ∀ (x y : Geid) (ss' : List Seg),
      ss' ⊆ ss → rawChainC GF.gfGd (ioCross GF) x y ss' →
      chainC GF.gfGd.gdG (ioCross GF) x y ss' := by
  intro hc hres hdr hwfR hagR hrowR hlat hAQ hRC hlog hpr hnB hcl x y ss'
  have hX : ∀ x y, ioCross GF x y → gmoLt GF.gfGd.gdG x y :=
    ioCrossGmo GF hc.1 hc.2.2.1 hres hdr
  have hag := CertZ24.agreeW4OfRP4 _ _ _ _ hagR
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
    · exact csHypsCertCR4 GF.gfGd ad _ GR P log x s hc hX hwfR hag hrowR hlat hAQ hRC hlog hpr hcs
        hx
    · exact absurd hb hnB

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **`cycleKillOfL2CZRC4`** — the class kill at SUCCESSFUL-PROTOCOL lock co. -/
theorem cycleKillOfL2CZRC4 (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    regZeroRun gen σ0 P →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    cutSupplyCZC boot d0 fab (imgZ σ0.wgimg) →
    certSupplyCZR4 boot d0 fab (imgZ σ0.wgimg) N P →
    acqAqCZ4 boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ4 boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR4 boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) := by
  intro hfr hb1 hb2 hwp hrz hcov hcut hcert hAQ hRC hl2
  intro GF ad him hc hconf hres hdr hIH x hcyc
  obtain ⟨z, ss, hne, hch⟩ := cycleSegmentsIO GF ad x hc hcyc
  obtain ⟨cs, hcutok, hdc, hcl, hprem⟩ := hcut GF ad z ss him hc hconf hne hch
  have hcore := catADCore _ _ hc
  have hconfH :=
    GraphFetchHullZ.gfexecConfZFHull boot d0 fab GF cs hcore.1 hcore.2.1 hcutok.1 hdc hconf hcl
  have hpc := GraphFetchKill.properCutFOfCut GF cs hcutok hdc
  have hacyH := hIH cs hpc hcl
  obtain ⟨c, pst, dv, GR, pi, hrd, hlog, hwfR, hagR, hrowR, hlat⟩ :=
    hcert GF ad cs z ss him hc hconf hres hdr hpc hcl hconfH hprem hacyH hne hch
  obtain ⟨t2, σ2, hrtc, hlgeq⟩ :=
    runErasedZ gen σ0 boot d0 N GF.gfGd.gdG c pst dv hfr hcov hb1 hb2 him hrd
  have hpr : CertZ18.protRegZ P GR.gxImg (cdLog c c.cdTr.length) := by
    rw [← hlgeq, hagR.1, him]
    exact hrz t2 σ2 hrtc
  have hnB : ¬ badRun gen σ0 := noBadRun hlc GF0 gen σ0 D hD hfr hwp
  exact cycleKillIOC GF ad z ss hc hres hdr hne
    (rawChainChainCZR4 GF ad GR pi P (cdLog c c.cdTr.length) (badRun gen σ0) ss hc hres hdr hwfR
      hagR hrowR hlat (hAQ GF ad GR pi _ him hc hconf hwfR hagR hrowR hlog hpr)
      (hRC GF ad GR pi _ him hc hconf hwfR hagR hrowR hlog hpr) hlog hpr hnB
      (hl2 GF ad GR pi him hconf hwfR hagR hrowR (cdLog c c.cdTr.length) z ss hc hlog hpr hne
        hch) z z ss (fun _ h => h) hch)

end glue

end CatLin

end Weak
