/-
Weak: **(c) [OWN.100] — the silent-AMO twin's kill re-routed to the TRIMMED class kill**
(`PROGRESS-W10N2p.md`; coordinator's provisional ruling after `Weak/CapFetchProv.lean`).  Lean-only, no
Rocq twin.

`fetchProv` is false at an untrimmed class graph (`xv6ConfS` only bounds the rows' fetch edges by
`gtFetch`, so a quantified graph may store junk pairs) and is not hull-stable, so the class kill
`CatLin.cycleKillCZC` is likely false as quantified.  `Weak/CapFetchProv.lean` gives the trimmed
route: `CatLin.cycleKillCZT` (class hypothesis `CapFetchProv.provAll`, induction hypothesis over the
TRIMMED hulls `CapFetchProv.trimF boot (gfHull GF cs)`), consumed by `CapFetchProv.t2linSupplyCZT` /
`t2linSupplyCZTtagged`.  This file restates the twin's kill so that it concludes `cycleKillCZT`:

  §1  **`SilKillT.certSupplyS`** (`SilKill.certSupplyS` with the hull acyclicity read at the TRIMMED
      hull) and its discharge from the twin walk **`SilKillT.certSupplyOfWalkS`**
      (`SilWalk.certOfWalkS`; the walk reads no hull premise); **`SilKillT.l2ClaimS`**
      (`SilKill.l2ClaimS` with `CapFetchProv.provAll boot GF.gfGd` as an extra hypothesis — the
      provenance G7's `g7FetchCertP` needs at a fetch-arm segment entry), `SilKillT.l2ClaimOfS`;
  §2  the common core `SilKillT.cycleKillCore` (the twin's footprint `protRegZ` at the realized log as
      one run-wise premise), and **`SilKillT.cycleKillOfL2S`** (`SilKill.cycleKillOfL2S`'s twin, the
      run fact `regZeroRunS`);
  §3  the kill′ consumers: `SilKillT.cycleKillOfL2CloseS` (`SilClose.cycleKillOfL2`),
      **`SilKillT.cycleKillS`** / `SilKillT.cycleKillDiscS` (`SilClose.cycleKillS` /
      `cycleKillDiscS`), **`SilKillT.cycleKillZS`** / `SilKillT.cycleKillDiscZS`
      (`SilRegZero.cycleKillZS` / `cycleKillDiscZS`: one `wpPackageProtZS` for the footprint).
      `SilClose.cycleKillCZS` / `SilRegZero.cycleKillCZZS` (⇒ `cycleKillCZ`, the untrimmed supply's
      guarded input) have no trimmed counterpart: `CapFetchProv.t2linSupplyCZT` takes `cycleKillCZT`
      itself.

The lock facts `SilKill.acqAqS` / `SilKill.relCoversS`, the cut supply and the WP tier are unchanged
(they do not read the fragment).

Spec: FAITHFUL (proof organisation: the trimmed graph has the same rows, gmo, deps and fabric; the
fragment is proof data, riscv.cat has no fetch).
-/
import Weak.SilRegZero
import Weak.CapFetchProv

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

namespace CatLin

/-! # 1. The trimmed cert supply and L2′ claim -/

/-- **(G-3) at the twin, TRIMMED**: `SilKill.certSupplyS` with the hull's acyclicity read at the
trimmed hull (what `cycleKillCZT`'s induction hypothesis gives). -/
def SilKillT.certSupplyS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (cs : List Nat) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    properCutF GF cs → GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs →
    GraphFabConf.gfexecConfZF boot d0 fab (gfHull GF cs) →
    GraphFetchBlocks.emPremOk boot (gfHull GF cs).gfGd.gdG →
    (∀ x, ¬ tc (racyDIO (CapFetchProv.trimF boot (gfHull GF cs))) x x) →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ (c : SilCand.CandS) (pst : Nat → List Pexv6) (dv : Nat → Efab) (pi : Nat → Nat),
      SilAgree.RunDataS boot d0 N GF.gfGd.gdG c pst dv ∧
      SilAgree.agreeRPS GF.gfGd.gdG (SilAgree.memberS N c) pi (GraphFetchN2.lockBytes P)

/-- **(G-3) TRIMMED, FROM THE FREE TWIN WALK** (the walk reads no hull premise). -/
theorem SilKillT.certSupplyOfWalkS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) :
    SilWalk.walkSupplyS boot d0 fab im N P → SilKillT.certSupplyS boot d0 fab im N P :=
  fun hws GF ad _ z ss him hc hconf hres hdr _ _ _ _ _ hne hch =>
    SilWalk.certOfWalkS boot d0 fab im N P hws GF ad z ss him hc hconf hres hdr hne hch

/-- **THE L2′ CLAIM AT EVERY REALIZED MEMBER OF A PROVENANT CLASS GRAPH** (W11-F's obligation on the
trimmed route): `SilKill.l2ClaimS` with the stored fetch fragment provenant (`CapFetchProv.provAll`). -/
def SilKillT.l2ClaimS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) (Bad : Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : SilCand.CandS) (pst : Nat → List Pexv6)
    (dv : Nat → Efab) (pi : Nat → Nat),
    GF.gfGd.gdG.gxImg = im → GraphFabConf.gfexecConfZF boot d0 fab GF →
    CapFetchProv.provAll boot GF.gfGd →
    SilAgree.RunDataS boot d0 N GF.gfGd.gdG c pst dv →
    SilAgree.agreeRPS GF.gfGd.gdG (SilAgree.memberS N c) pi (GraphFetchN2.lockBytes P) →
    l2ClaimAtCZR4 GF ad (SilAgree.memberS N c) P Bad

/-- The untrimmed claim gives the trimmed one. -/
theorem SilKillT.l2ClaimOfS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) (Bad : Prop) :
    SilKill.l2ClaimS boot d0 fab im N P Bad → SilKillT.l2ClaimS boot d0 fab im N P Bad :=
  fun h GF ad c pst dv pi him hconf _ => h GF ad c pst dv pi him hconf

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-! # 2. The core and `cycleKillOfL2S` -/

/-- **THE TRIMMED TWIN KILL, CORE**: `cycleKillCZT` from the twin's run facts, with the footprint
`protRegZ` at the realized log as one run-wise premise (`hprF`) and the bad arm refuted (`hnB`). -/
theorem SilKillT.cycleKillCore (gen : Nat) (σ0 : WGState) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    ¬ SilKill.badRunS gen σ0 →
    (∀ ρ, rtc SilEpf.epfRunS (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : SilCand.CandS) (pst : Nat → List Pexv6)
      (dv : Nat → Efab) (pi : Nat → Nat) (t2 : List SilLang.EExprS) (σ2 : WGState),
      GF.gfGd.gdG.gxImg = imgZ σ0.wgimg → rvwmoCatAD GF.gfGd ad →
      GraphFabConf.gfexecConfZF boot d0 fab GF →
      SilAgree.RunDataS boot d0 N GF.gfGd.gdG c pst dv →
      SilAgree.agreeRPS GF.gfGd.gdG (SilAgree.memberS N c) pi (GraphFetchN2.lockBytes P) →
      (SilLang.epowerForkS gen, σ0) -·->ₜₚ* (t2, σ2) → σ2.wglog = SilAgree.logS c →
      CertZ18.protRegZ P (imgZ σ0.wgimg) (SilAgree.logS c)) →
    cutSupplyCZC boot d0 fab (imgZ σ0.wgimg) →
    SilKillT.certSupplyS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.acqAqS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.relCoversS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKillT.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZT boot d0 fab (imgZ σ0.wgimg) := by
  intro hfr hb1 hb2 hnB hcov hprF hcut hcert hAQ hRC hl2
  intro GF ad him hc hconf hres hdr hprov hIH x hcyc
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
    rw [himgR, him]
    exact hprF GF ad c pst dv pi t2 σ2 him hc hconf hrd hagR hrtc hlgeq
  exact cycleKillIOC GF ad z ss hc hres hdr hne
    (SilKill.rawChainChainW4 GF ad (SilAgree.memberS N c) P (SilAgree.logS c) (SilKill.badRunS gen σ0)
      ss hc hres hdr hwfR (SilAgree.agreeW4OfRPS _ _ _ _ hagR) hrowR hlat
      (hAQ GF ad c pst dv pi him hc hconf hrd hagR hpr)
      (hRC GF ad c pst dv pi him hc hconf hrd hagR hpr) hlog hpr hnB
      (hl2 GF ad c pst dv pi him hconf hprov hrd hagR (SilAgree.logS c) z ss hc hlog hpr hne hch)
      z z ss (fun _ h => h) hch)

/-- **`cycleKillOfL2S`, TRIMMED** — `SilKill.cycleKillOfL2S` concluding `cycleKillCZT`. -/
theorem SilKillT.cycleKillOfL2S (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
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
    SilKillT.certSupplyS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.acqAqS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.relCoversS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKillT.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZT boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hrz hcov hcut hcert hAQ hRC hl2 =>
    SilKillT.cycleKillCore gen σ0 P boot d0 fab N hfr hb1 hb2
      (SilKill.noBadRunS hlc GF0 gen σ0 D hD hfr hwp) hcov
      (fun _ _ _ _ _ _ t2 σ2 _ _ _ _ _ hrtc hlg => by rw [← hlg]; exact hrz t2 σ2 hrtc)
      hcut hcert hAQ hRC hl2

/-! # 3. kill′, trimmed -/

/-- `SilClose.cycleKillOfL2`, TRIMMED: the footprint from `adequacyProtS` and `regZeroS`. -/
theorem SilKillT.cycleKillOfL2CloseS (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    SilKill.wpPackageS hlc GF0 gen σ0 D →
    (∀ a base, P a base → SilClose.wpPackageProtS hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc SilEpf.epfRunS (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    cutSupplyCZC boot d0 fab (imgZ σ0.wgimg) →
    SilKillT.certSupplyS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.acqAqS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.relCoversS boot d0 fab (imgZ σ0.wgimg) N P →
    SilClose.regZeroS gen σ0 boot d0 fab N P →
    SilKillT.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZT boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hcut hcert hAQ hRC hrz hl2 =>
    SilKillT.cycleKillCore gen σ0 P boot d0 fab N hfr hb1 hb2
      (SilKill.noBadRunS hlc GF0 gen σ0 D hD hfr hwp) hcov
      (fun GF ad c pst dv pi t2 σ2 him hc hconf hrd hagR hrtc hlg =>
        hrz GF ad c pst dv pi t2 σ2 him hc hconf hrd hagR hrtc hlg
          (by rw [← hlg]; exact SilClose.protRegOfRunS hlc GF0 gen σ0 D hD Nm P t2 σ2 hfr hwpp hrtc))
      hcut hcert hAQ hRC hl2

/-- **`cycleKillS`, TRIMMED** — `SilClose.cycleKillS` (kill′: the twin WP packages, the fetch view,
(harts ≤ N ∧ P2), the walk order with NF2c, the twin step supply, the lock facts, zero-at-registration
and the TRIMMED L2′ claim) concluding `cycleKillCZT`. -/
theorem SilKillT.cycleKillS (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    SilKill.wpPackageS hlc GF0 gen σ0 D →
    (∀ a base, P a base → SilClose.wpPackageProtS hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc SilEpf.epfRunS (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    orderSupplyCZ3 boot d0 fab (imgZ σ0.wgimg) P →
    SilClose.oneByteS boot d0 fab (imgZ σ0.wgimg) P →
    SilOrd.stepSupplyS boot d0 fab (imgZ σ0.wgimg) P →
    SilKill.acqAqS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.relCoversS boot d0 fab (imgZ σ0.wgimg) N P →
    SilClose.regZeroS gen σ0 boot d0 fab N P →
    SilKillT.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZT boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpre hordS h1b hstep hAQ hRC hrz hl2 =>
    SilKillT.cycleKillOfL2CloseS hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov
      (cutSupplyOfCycleCZC boot d0 fab _)
      (SilKillT.certSupplyOfWalkS boot d0 fab _ N P
        (SilOrd.walkSupplyOfOrdStepS boot d0 fab _ N P hpre hordS
          (SilClose.spNfOfOneByte boot d0 fab _ P h1b) hstep))
      hAQ hRC hrz hl2

/-- `SilClose.cycleKillDiscS`, TRIMMED (the order derived: `lockDiscCZ3` + `gfDevWIoCZ`). -/
theorem SilKillT.cycleKillDiscS (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    SilKill.wpPackageS hlc GF0 gen σ0 D →
    (∀ a base, P a base → SilClose.wpPackageProtS hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc SilEpf.epfRunS (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    lockDiscCZ3 boot d0 fab (imgZ σ0.wgimg) P →
    gfDevWIoCZ boot d0 fab (imgZ σ0.wgimg) →
    SilOrd.stepSupplyS boot d0 fab (imgZ σ0.wgimg) P →
    SilKill.acqAqS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.relCoversS boot d0 fab (imgZ σ0.wgimg) N P →
    SilClose.regZeroS gen σ0 boot d0 fab N P →
    SilKillT.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZT boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpre hdisc hwio hstep hAQ hRC hrz hl2 =>
    SilKillT.cycleKillS hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov hpre
      (orderSupplyOfDisc3 boot d0 fab _ P hdisc hwio)
      (SilClose.oneByteOfDisc3 boot d0 fab _ P hdisc) hstep hAQ hRC hrz hl2

/-- **`cycleKillZS`, TRIMMED** — `SilRegZero.cycleKillZS` (one `wpPackageProtZS` in place of
`wpPackageProtS` + `regZeroS`) concluding `cycleKillCZT`. -/
theorem SilKillT.cycleKillZS (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    SilKill.wpPackageS hlc GF0 gen σ0 D →
    (∀ a base, P a base → SilRegZero.wpPackageProtZS hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc SilEpf.epfRunS (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    orderSupplyCZ3 boot d0 fab (imgZ σ0.wgimg) P →
    SilClose.oneByteS boot d0 fab (imgZ σ0.wgimg) P →
    SilOrd.stepSupplyS boot d0 fab (imgZ σ0.wgimg) P →
    SilKill.acqAqS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.relCoversS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKillT.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZT boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpz hcov hpre hordS h1b hstep hAQ hRC hl2 =>
    SilKillT.cycleKillS hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp
      (fun a base hP => SilRegZero.wpPackageProtOfZ hlc GF0 gen σ0 D (Nm a base) a base
        (hwpz a base hP))
      hcov hpre hordS h1b hstep hAQ hRC
      (SilRegZero.regZeroOfZ hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hwpz) hl2

/-- `SilRegZero.cycleKillDiscZS`, TRIMMED (the order derived, the zero in the package). -/
theorem SilKillT.cycleKillDiscZS (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    SilKill.wpPackageS hlc GF0 gen σ0 D →
    (∀ a base, P a base → SilRegZero.wpPackageProtZS hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc SilEpf.epfRunS (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    lockDiscCZ3 boot d0 fab (imgZ σ0.wgimg) P →
    gfDevWIoCZ boot d0 fab (imgZ σ0.wgimg) →
    SilOrd.stepSupplyS boot d0 fab (imgZ σ0.wgimg) P →
    SilKill.acqAqS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.relCoversS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKillT.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZT boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpz hcov hpre hdisc hwio hstep hAQ hRC hl2 =>
    SilKillT.cycleKillZS hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpz hcov hpre
      (orderSupplyOfDisc3 boot d0 fab _ P hdisc hwio)
      (SilClose.oneByteOfDisc3 boot d0 fab _ P hdisc) hstep hAQ hRC hl2

end glue

end CatLin

end Weak
