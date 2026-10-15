/-
Weak: **(c) [OWN.100], increment 5b — the class kill at the REALIZED twin member** (`PROGRESS-W10N2p.md`).
Lean-only, no Rocq twin.

`CertZ25`'s kill (`CatLin.cycleKillOfL2CZRC4`) restated over the silent twin:
  * the cert supply returns a TWIN run datum (`SilAgree.RunDataS`) and the silent agreement
    (`SilAgree.agreeRPS`) at the realized member `SilAgree.memberS N c`; the member's gwf / gwrowGmo /
    logOf / rmwLatest are PROVED (`SilAgree.memberFacts`), no longer supplied;
  * the lock facts `acqAqS` / `relCoversS` and the L2′ claim `l2ClaimS` are quantified over REALIZED
    members only — a twin candidate with its run datum from the boot states — not over every graph
    agreeing with `GF` (W11-F inventory A8/B6/B3: false/circular there, provable at a realized member);
  * the weak-WP tier at the TWIN machine: `SilKill.wpPackageS`, `SilKill.badRunS` + `noBadRunS`
    (`SilEpf.pfViolationFreeS`), `SilKill.regZeroRunS` (over the twin thread pool), the fetch-view
    coverage over `SilEpf.epfRunS`.
**`SilKill.cycleKillOfL2S`** concludes the registered `cycleKillCZC`.

Spec: FAITHFUL.
-/
import Weak.SilAgree

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

namespace CatLin

/-- `rawChainChainCZR4` at CertZ24's `agreeW4` (the only agreement fact it uses). -/
theorem SilKill.rawChainChainW4 (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec)
    (P : Int → Int → Prop) (log : List Wmsg) (Bad : Prop) (ss : List Seg) :
    rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    gwf GR → CertZ24.agreeW4 GF.gfGd.gdG GR (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    CertZ18.rmwLatest GR log →
    acqAqLog GF.gfGd.gdG GR log P → relCoversLog GF.gfGd.gdG GR log P →
    logOf GR log → CertZ18.protRegZ P GR.gxImg log → ¬ Bad →
    (∀ prev s, s ∈ ss → ioCross GF prev s.sgEntry → segRunC GF.gfGd s →
       segPinC GF.gfGd ad s ∨ csHypsR4 GF.gfGd GR P log prev s ∨ Bad) →
    ∀ (x y : Geid) (ss' : List Seg),
      ss' ⊆ ss → rawChainC GF.gfGd (ioCross GF) x y ss' →
      chainC GF.gfGd.gdG (ioCross GF) x y ss' := by
  intro hc hres hdr hwfR hag hrowR hlat hAQ hRC hlog hpr hnB hcl x y ss'
  have hX : ∀ x y, ioCross GF x y → gmoLt GF.gfGd.gdG x y :=
    ioCrossGmo GF hc.1 hc.2.2.1 hres hdr
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

/-- **THE L2′ CLAIM AT EVERY REALIZED MEMBER** (W11-F's obligation). -/
def SilKill.l2ClaimS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) (Bad : Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : SilCand.CandS) (pst : Nat → List Pexv6)
    (dv : Nat → Efab) (pi : Nat → Nat),
    GF.gfGd.gdG.gxImg = im → GraphFabConf.gfexecConfZF boot d0 fab GF →
    SilAgree.RunDataS boot d0 N GF.gfGd.gdG c pst dv →
    SilAgree.agreeRPS GF.gfGd.gdG (SilAgree.memberS N c) pi (GraphFetchN2.lockBytes P) →
    l2ClaimAtCZR4 GF ad (SilAgree.memberS N c) P Bad

/-- (G-3) at the twin: a twin run datum and the silent agreement at its realized member. -/
def SilKill.certSupplyS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (cs : List Nat) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    properCutF GF cs → GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs →
    GraphFabConf.gfexecConfZF boot d0 fab (gfHull GF cs) →
    GraphFetchBlocks.emPremOk boot (gfHull GF cs).gfGd.gdG →
    (∀ x, ¬ tc (racyDIO (gfHull GF cs)) x x) →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ (c : SilCand.CandS) (pst : Nat → List Pexv6) (dv : Nat → Efab) (pi : Nat → Nat),
      SilAgree.RunDataS boot d0 N GF.gfGd.gdG c pst dv ∧
      SilAgree.agreeRPS GF.gfGd.gdG (SilAgree.memberS N c) pi (GraphFetchN2.lockBytes P)

/-- `acqAqCZ4` at the REALIZED members only. -/
def SilKill.acqAqS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : SilCand.CandS) (pst : Nat → List Pexv6)
    (dv : Nat → Efab) (pi : Nat → Nat),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    SilAgree.RunDataS boot d0 N GF.gfGd.gdG c pst dv →
    SilAgree.agreeRPS GF.gfGd.gdG (SilAgree.memberS N c) pi (GraphFetchN2.lockBytes P) →
    CertZ18.protRegZ P (SilAgree.memberS N c).gxImg (SilAgree.logS c) →
    acqAqLog GF.gfGd.gdG (SilAgree.memberS N c) (SilAgree.logS c) P

/-- `relCoversCZ4` at the REALIZED members only. -/
def SilKill.relCoversS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : SilCand.CandS) (pst : Nat → List Pexv6)
    (dv : Nat → Efab) (pi : Nat → Nat),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    SilAgree.RunDataS boot d0 N GF.gfGd.gdG c pst dv →
    SilAgree.agreeRPS GF.gfGd.gdG (SilAgree.memberS N c) pi (GraphFetchN2.lockBytes P) →
    CertZ18.protRegZ P (SilAgree.memberS N c).gxImg (SilAgree.logS c) →
    relCoversLog GF.gfGd.gdG (SilAgree.memberS N c) (SilAgree.logS c) P

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- The WP package at the TWIN logic (`wpPackage` with `epowerForkS` / `ewpTrivS`). -/
def SilKill.wpPackageS (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) : Prop :=
  ∀ [MachGS hlc GF] [WeakGS GF],
    (([∗list] cc ∈ cpus, [∗list] r ∈ D cc, regPointsTo cc r (DFrac.own 1) (σ0.wgregs cc r)) ∗
      bigSepM (M := GMapF PAddr) (fun a b => wlatPointsto (paZ a) (DFrac.own 1) 0 b) σ0.wgimg ∗
      ([∗list] cc ∈ cpus, hartView cc) ∗
      wlogLb [] ∗
      ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (σ0.wgdev.st d)))
    ⊢@{IProp GF} |={⊤}=>
      ([∗list] e ∈ SilLang.epowerForkS gen, SilLang.ewpTrivS (hlc := hlc) (GF := GF) ⊤ e)

/-- φ at the twin machine: the BAD arm. -/
def SilKill.badRunS (gen : Nat) (σ0 : WGState) : Prop :=
  ∃ ρ, rtc SilEpf.epfRunS (epInit gen, σ0) ρ ∧ violationHart clsOf pubOf nDisk (ecfgOf ρ.1 ρ.2)

theorem SilKill.noBadRunS (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup) :
    freshEra gen σ0 → SilKill.wpPackageS hlc GF gen σ0 D → ¬ SilKill.badRunS gen σ0 := by
  rintro ⟨hgen, hpow, hgen0, hlog, hws⟩ hwp ⟨ρ, hr, hv⟩
  exact SilEpf.pfViolationFreeS (hlc := hlc) (GF := GF) gen σ0 D hD hpow hgen0 hlog hws hwp ρ hr hv

/-- `regZeroRun` over the TWIN thread pool. -/
def SilKill.regZeroRunS (gen : Nat) (σ0 : WGState) (P : Int → Int → Prop) : Prop :=
  ∀ (t2 : List SilLang.EExprS) (σ2 : WGState), (SilLang.epowerForkS gen, σ0) -·->ₜₚ* (t2, σ2) →
    CertZ18.protRegZ P (imgZ σ0.wgimg) σ2.wglog

/-- **`cycleKillOfL2S`** — the class kill at the REALIZED twin member. -/
theorem SilKill.cycleKillOfL2S (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    SilKill.wpPackageS hlc GF0 gen σ0 D →
    SilKill.regZeroRunS gen σ0 P →
    (∀ ρ, rtc SilEpf.epfRunS (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    cutSupplyCZC boot d0 fab (imgZ σ0.wgimg) →
    SilKill.certSupplyS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.acqAqS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.relCoversS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
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
  obtain ⟨c, pst, dv, pi, hrd, hagR⟩ :=
    hcert GF ad cs z ss him hc hconf hres hdr hpc hcl hconfH hprem hacyH hne hch
  obtain ⟨hwfR, hrowR, hlog, hlat, himgR⟩ := SilAgree.memberFacts hrd
  obtain ⟨t2, σ2, hrtc, hlgeq⟩ :=
    SilAgree.runErasedS gen σ0 boot d0 N GF.gfGd.gdG c pst dv hfr hcov hb1 hb2 him hrd
  have hpr : CertZ18.protRegZ P (SilAgree.memberS N c).gxImg (SilAgree.logS c) := by
    rw [← hlgeq, himgR, him]
    exact hrz t2 σ2 hrtc
  have hnB : ¬ SilKill.badRunS gen σ0 := SilKill.noBadRunS hlc GF0 gen σ0 D hD hfr hwp
  exact cycleKillIOC GF ad z ss hc hres hdr hne
    (SilKill.rawChainChainW4 GF ad (SilAgree.memberS N c) P (SilAgree.logS c) (SilKill.badRunS gen σ0)
      ss hc hres hdr hwfR (SilAgree.agreeW4OfRPS _ _ _ _ hagR) hrowR hlat
      (hAQ GF ad c pst dv pi him hc hconf hrd hagR hpr)
      (hRC GF ad c pst dv pi him hc hconf hrd hagR hpr) hlog hpr hnB
      (hl2 GF ad c pst dv pi him hconf hrd hagR (SilAgree.logS c) z ss hc hlog hpr hne hch)
      z z ss (fun _ h => h) hch)

end glue

end CatLin

end Weak
