/-
Weak: **(c) [OWN.100], increment 6 — kill′: the twin's kill closed as the consumer W11-F assembles**
(`PROGRESS-W10N2p.md`; plan rev 53 REMAINING WORK row 3).  Lean-only, no Rocq twin.

`SilOrd.cycleKillOfOrdStepS` restated so that every premise is either fed by the twin's adequacy exports
or is one of the REMAINING WORK row-6 facts:

  §1  `SilOrd.spNfS` DISCHARGED: **`SilClose.oneByteS`** (NF2c — a non-plain write touches at most one
      lock byte; the third conjunct of `lockDisc3`, row 6l) gives it (`SilClose.spNfOfOneByte`), and so
      does `lockDiscCZ3` (`SilClose.spNfOfDisc3`);
  §2  the protected-byte footprint FROM THE TWIN'S EXPORT: `SilClose.wpPackageProtS` (`wpPackageProt` at
      the twin language) and **`SilClose.protRegOfRunS`** (`protReg` along every twin run, by
      `SilLang.adequacyProtS`); the zero-at-registration half alone stays named —
      **`SilClose.regZeroS`** (row 6k), at the REALIZED twin member's log and GIVEN `protReg` there;
  §3  **`CatLin.SilClose.cycleKillS`** (kill′: twin WP packages → `pfViolationFreeS` / `adequacyProtS`,
      the fetch view, (harts ≤ N ∧ P2), `orderSupplyCZ3` + `oneByteS`, `stepSupplyS`, `acqAqS` /
      `relCoversS`, `regZeroS`, `l2ClaimS`) ⇒ the registered `cycleKillCZC`;
      `CatLin.SilClose.cycleKillDiscS` (the order DERIVED: `lockDiscCZ3` + `gfDevWIoCZ`, the registered
      CertZ31 shape) and `CatLin.SilClose.cycleKillCZS` (⇒ `cycleKillCZ`, `t2linSupplyCZIO`'s input).

Spec: FAITHFUL (proof organisation; the named facts' truth in `PROGRESS-W10N2p.md`).
-/
import Weak.SilOrd

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

namespace CatLin

/-! # 1. `spNfS` from NF2c -/

/-- **NF2c at the class** (`lockDisc3`'s third conjunct): a non-plain write touches at most one lock
byte.  xv6: the non-plain writes are `amoswap.w` (4 aligned bytes) and the walker's 8-byte PTE A/D
write-backs; lock words are ≥ 24 bytes apart (`struct spinlock`). -/
def SilClose.oneByteS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ∀ b b' e v v', GraphFetchN2.lockBytes P b → GraphFetchN2.lockBytes P b' →
      gwritesByte GF.gfGd.gdG e b v → gwritesByte GF.gfGd.gdG e b' v' → CertZ14.np GF.gfGd.gdG e →
      b = b'

theorem SilClose.spNfOfOneByte (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) :
    SilClose.oneByteS boot d0 fab im P → SilOrd.spNfS boot d0 fab im P := by
  intro h1 GF ad him hc hconf b e v hb hw hsp ⟨b', hb', hfa⟩
  obtain ⟨v', hw', -⟩ := hfa.1
  have hbb := h1 GF ad him hc hconf b b' e v v' hb hb' hw hw' hsp.1
  subst hbb
  exact hsp.2 hfa

theorem SilClose.oneByteOfDisc3 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) :
    lockDiscCZ3 boot d0 fab im P → SilClose.oneByteS boot d0 fab im P :=
  fun hld GF ad him hc hconf => (hld GF ad him hc hconf).2.2.1

theorem SilClose.spNfOfDisc3 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) :
    lockDiscCZ3 boot d0 fab im P → SilOrd.spNfS boot d0 fab im P :=
  fun hld => SilClose.spNfOfOneByte boot d0 fab im P (SilClose.oneByteOfDisc3 boot d0 fab im P hld)

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-! # 2. The footprint from the twin's export -/

/-- `wpPackageProt` at the TWIN logic (`epowerForkS` / `ewpTrivS`). -/
def SilClose.wpPackageProtS (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (Nm : Namespace) (a base : Int) : Prop :=
  ∀ [MachGS hlc GF] [WeakGS GF],
    (([∗list] cc ∈ cpus, [∗list] r ∈ D cc, regPointsTo cc r (DFrac.own 1) (σ0.wgregs cc r)) ∗
      bigSepM (M := GMapF PAddr) (fun a0 b => wlatPointsto (paZ a0) (DFrac.own 1) 0 b)
        σ0.wgimg ∗
      ([∗list] cc ∈ cpus, hartView cc) ∗
      wlogLb [] ∗
      ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (σ0.wgdev.st d)))
    ⊢@{IProp GF} |={⊤}=>
      (wprotRegd (hlc := hlc) Nm a base ∗
        [∗list] e ∈ SilLang.epowerForkS gen, SilLang.ewpTrivS (hlc := hlc) (GF := GF) ⊤ e)

/-- **`protRegOfRun` at the twin**: from the twin WP packages with the registration ghost, every twin
run's log carries the protection / lock-word / alternation witnesses (`SilLang.adequacyProtS`). -/
theorem SilClose.protRegOfRunS (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (t2 : List SilLang.EExprS) (σ2 : WGState) :
    freshEra gen σ0 →
    (∀ a base, P a base → SilClose.wpPackageProtS hlc GF gen σ0 D (Nm a base) a base) →
    (SilLang.epowerForkS gen, σ0) -·->ₜₚ* (t2, σ2) →
    protReg P σ2.wglog := by
  rintro ⟨-, hpow, hgen0, hlog, hws⟩ hwp hrtc a base hP
  obtain ⟨-, n0, r0, h, hpr, hat, halt⟩ :=
    SilLang.adequacyProtS (hlc := hlc) (GF := GF) gen σ0 D hD (Nm a base) a base hpow hgen0 hlog
      hws (hwp a base hP) t2 σ2 hrtc
  exact ⟨n0, r0, h, hpr, hat, halt⟩

/-- **THE ZERO-AT-REGISTRATION FACT AT THE REALIZED TWIN LOG** (row 6k; `CertZ18.regZeroAt`): at a
realized twin member whose twin run from power-on ends at its log, given the export's `protReg` there,
the witnesses can be chosen with each lock byte FREE at its registration point. -/
def SilClose.regZeroS (gen : Nat) (σ0 : WGState) (boot : Nat → Pexv6) (d0 : Efab)
    (fab : Nat → Efab) (N : Nat) (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : SilCand.CandS) (pst : Nat → List Pexv6)
    (dv : Nat → Efab) (pi : Nat → Nat) (t2 : List SilLang.EExprS) (σ2 : WGState),
    GF.gfGd.gdG.gxImg = imgZ σ0.wgimg → rvwmoCatAD GF.gfGd ad →
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    SilAgree.RunDataS boot d0 N GF.gfGd.gdG c pst dv →
    SilAgree.agreeRPS GF.gfGd.gdG (SilAgree.memberS N c) pi (GraphFetchN2.lockBytes P) →
    (SilLang.epowerForkS gen, σ0) -·->ₜₚ* (t2, σ2) → σ2.wglog = SilAgree.logS c →
    protReg P (SilAgree.logS c) →
    CertZ18.protRegZ P (imgZ σ0.wgimg) (SilAgree.logS c)

/-! # 3. kill′ -/

/-- `SilKill.cycleKillOfL2S` with the footprint from `adequacyProtS` and `regZeroS` in place of the
run fact `regZeroRunS`. -/
theorem SilClose.cycleKillOfL2 (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
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
    SilKill.certSupplyS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.acqAqS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.relCoversS boot d0 fab (imgZ σ0.wgimg) N P →
    SilClose.regZeroS gen σ0 boot d0 fab N P →
    SilKill.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) := by
  intro hfr hb1 hb2 hwp hwpp hcov hcut hcert hAQ hRC hrz hl2
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
  have hpr0 : protReg P (SilAgree.logS c) := by
    rw [← hlgeq]
    exact SilClose.protRegOfRunS hlc GF0 gen σ0 D hD Nm P t2 σ2 hfr hwpp hrtc
  have hpr : CertZ18.protRegZ P (SilAgree.memberS N c).gxImg (SilAgree.logS c) := by
    rw [himgR, him]
    exact hrz GF ad c pst dv pi t2 σ2 him hc hconf hrd hagR hrtc hlgeq hpr0
  have hnB : ¬ SilKill.badRunS gen σ0 := SilKill.noBadRunS hlc GF0 gen σ0 D hD hfr hwp
  exact cycleKillIOC GF ad z ss hc hres hdr hne
    (SilKill.rawChainChainW4 GF ad (SilAgree.memberS N c) P (SilAgree.logS c) (SilKill.badRunS gen σ0)
      ss hc hres hdr hwfR (SilAgree.agreeW4OfRPS _ _ _ _ hagR) hrowR hlat
      (hAQ GF ad c pst dv pi him hc hconf hrd hagR hpr)
      (hRC GF ad c pst dv pi him hc hconf hrd hagR hpr) hlog hpr hnB
      (hl2 GF ad c pst dv pi him hconf hrd hagR (SilAgree.logS c) z ss hc hlog hpr hne hch)
      z z ss (fun _ h => h) hch)

/-- **`cycleKillS` — kill′, THE TWIN'S KILL CLOSED**: the twin WP packages (fed to `pfViolationFreeS`
and `adequacyProtS`), the fetch view, (harts ≤ N ∧ P2), the walk ORDER (input) with NF2c, the twin STEP
supply, the lock facts / zero-at-registration / L2′ claim at REALIZED twin members. -/
theorem SilClose.cycleKillS (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
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
    SilKill.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpre hordS h1b hstep hAQ hRC hrz hl2 =>
    SilClose.cycleKillOfL2 hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov
      (cutSupplyOfCycleCZC boot d0 fab _)
      (SilWalk.certSupplyOfWalkS boot d0 fab _ N P
        (SilOrd.walkSupplyOfOrdStepS boot d0 fab _ N P hpre hordS
          (SilClose.spNfOfOneByte boot d0 fab _ P h1b) hstep))
      hAQ hRC hrz hl2

/-- kill′ with the order DERIVED (`orderSupplyOfDisc3`: the lock discipline + `gfDevWIoCZ`, the shape
of the registered `cycleKillOfOrdStepCZRC4`). -/
theorem SilClose.cycleKillDiscS (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
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
    SilKill.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpre hdisc hwio hstep hAQ hRC hrz hl2 =>
    SilClose.cycleKillS hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov hpre
      (orderSupplyOfDisc3 boot d0 fab _ P hdisc hwio)
      (SilClose.oneByteOfDisc3 boot d0 fab _ P hdisc) hstep hAQ hRC hrz hl2

/-- kill′ at `cycleKillCZ` (the input of `CatLin.t2linSupplyCZIO`). -/
theorem SilClose.cycleKillCZS (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
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
    SilKill.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZ boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpre hordS h1b hstep hAQ hRC hrz hl2 =>
    cycleKillCZOfC boot d0 fab _
      (SilClose.cycleKillS hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov hpre
        hordS h1b hstep hAQ hRC hrz hl2)

end glue

end CatLin

end Weak
