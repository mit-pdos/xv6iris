/-
Weak: **(c) [OWN.100], row 6k — zero at registration carried by the twin's REGISTRATION GHOST**
(`PROGRESS-W10N2p.md`; plan rev 53 REMAINING WORK row 6k, option (A), coordinator's provisional
ruling 2026-10-18).  Lean-only, no Rocq twin.

`CatLin.SilClose.regZeroS` ("a lock byte is zero at its registration point", at a realized twin log,
given `protReg` there) is NOT derivable from `protReg` plus the access-discipline export: the
registration point `n0` is the WP proof's ghost choice and carries no value (`wlockRegister`
registers from `WClean`), and no twin realization relates `logS c` to a MachCSL state (see
`PROGRESS-W10N2p.md`, row 6k).  This file records the zero where it is KNOWN — at the registration:

  §1  **`SilRegZero.wprotRegdZ img N a base`** — `wprotRegd` whose invariant body also holds a log
      snapshot `wlogLb L0` with `|L0| = n0` and `CertZ18.regZeroAt img L0 base n0` (the fact reads
      `log.take n0` only, so it is stable under every later append); `wprotRegdOfZ` (it implies
      `wprotRegd`); the establishment facts for the WP proof (row 6j), at the mint after
      `initlock`'s `sw zero`: `regZeroOfLatestVal` / `regZeroOfElem` (the registering hart's
      `wlatElem base _ t lockFree` gives `regZeroAt` at `n0 = |log|`) with `wlogSnapshot`;
  §2  the export **`SilRegZero.wprotRegdZExport`** and the twin adequacy
      **`SilRegZero.adequacyProtZS`** (`protRegZ`'s four clauses at the run's end), the package
      **`SilRegZero.wpPackageProtZS`** (⇒ `SilClose.wpPackageProtS`, `wpPackageProtOfZ`),
      **`SilRegZero.protRegZOfRunS`** and **`SilRegZero.regZeroOfZ`** (⇒ `SilClose.regZeroS`);
  §3  the kill′ Z-variants beside `SilClose`'s (kept intact for option (B)):
      **`CatLin.SilRegZero.cycleKillZS`** / `cycleKillDiscZS` / `cycleKillCZZS` — one
      `wpPackageProtZS` in place of `wpPackageProtS` + `regZeroS`.

Spec: FAITHFUL (proof organisation: `regZeroAt` is a program fact about xv6's registration sites —
a lock is registered right after `initlock`'s `lk->locked = 0`; RVWMO/riscv.cat/Sail are silent).
-/
import Weak.SilClose

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

namespace CatLin

/-! # 0. Pure facts -/

/-- `regZeroAt` reads only `log.take n0`: it moves from a snapshot `L0` of length `n0` to any log
extending it. -/
theorem SilRegZero.regZeroPrefix (img : Image) (L0 log : List Wmsg) (b : Int) (n0 : Nat) :
    L0.length = n0 → L0 <+: log → CertZ18.regZeroAt img L0 b n0 → CertZ18.regZeroAt img log b n0 := by
  intro hl hp hz
  have h1 : log.take n0 = L0 := by
    rw [← hl]; exact (List.prefix_iff_eq_take.1 hp).symm
  have h2 : L0.take n0 = L0 := List.take_of_length_le (Nat.le_of_eq hl)
  unfold CertZ18.regZeroAt at hz ⊢
  rw [h1]
  rwa [h2] at hz

/-- **THE ESTABLISHMENT, pure**: if the byte's latest write is a `lockFree` byte, the byte is zero
at the registration point `n0 = |log|`. -/
theorem SilRegZero.regZeroOfLatestVal (img : Image) (log : List Wmsg) (b : Int) (t : Nat) :
    latestVal img log b t lockFree → CertZ18.regZeroAt img log b log.length := by
  intro h t' ht'
  have hk : log.take log.length = log := List.take_of_length_le (Nat.le_refl _)
  rw [hk] at ht' ⊢
  have := latestUnique img log b t' t ht' (latestValLatest img log b t lockFree h)
  subst this
  exact h.1

section ghost

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-! # 1. The registration ghost with the zero -/

section res

variable {GF : BundledGFunctors} [WeakGS GF]

/-- **THE ESTABLISHMENT, at the mint** (row 6j's obligation at each registration): the registering
hart's element of the lock byte, holding `lockFree` (right after `initlock`'s `sw zero`), gives
`regZeroAt` at `n0 = |log|`; `wlogSnapshot` supplies the matching `wlogLb log`. -/
theorem SilRegZero.regZeroOfElem (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (b : Int)
    (dq : DFrac) (t : Nat) :
    wlatInterp (GF := GF) img log ∗ wlatElem b dq t lockFree ⊢
      ⌜CertZ18.regZeroAt (imgZ img) log b log.length⌝ := by
  iintro H
  ihave %h := wlatLookupElem img log b dq t lockFree $$ H
  ipureintro
  exact SilRegZero.regZeroOfLatestVal _ log b t h

end res

section interp

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- **`wprotRegd` WITH THE ZERO**: the invariant body also holds a snapshot `L0` of the log at the
registration point (`|L0| = n0`) at which the lock byte is free. -/
def SilRegZero.wprotRegdZ (img : Image) (N : Namespace) (a base : Int) : IProp GF :=
  iprop(∃ I : IProp GF, Iris.inv N I ∗
    □ (I -∗ ∃ (γ : GName) (n0 r0 : Nat) (d : Option CPU) (h : Option Nat) (L0 : List Wmsg),
      wprotSt a γ base n0 r0 d ∗ wlockSt base base n0 h ∗ wlogLb L0 ∗
      ⌜L0.length = n0 ∧ CertZ18.regZeroAt img L0 base n0⌝ ∗
      (wprotSt a γ base n0 r0 d -∗ wlockSt base base n0 h -∗ I)))

instance SilRegZero.wprotRegdZ_persistent (img : Image) (N : Namespace) (a base : Int) :
    Persistent (SilRegZero.wprotRegdZ (hlc := hlc) (GF := GF) img N a base) := by
  unfold SilRegZero.wprotRegdZ; infer_instance

/-- The zero is extra: `wprotRegdZ` implies `wprotRegd`. -/
theorem SilRegZero.wprotRegdOfZ (img : Image) (N : Namespace) (a base : Int) :
    SilRegZero.wprotRegdZ (hlc := hlc) (GF := GF) img N a base ⊢
      wprotRegd (hlc := hlc) (GF := GF) N a base := by
  unfold SilRegZero.wprotRegdZ wprotRegd
  iintro ⟨%I, #Hinv, #Hacc⟩
  iexists I
  isplit
  · iexact Hinv
  · imodintro
    iintro HI
    icases Hacc $$ HI with ⟨%γ, %n0, %r0, %d, %h, %L0, Hpr, Hlk, -, -, Hback⟩
    iexists γ, n0, r0, d, h
    iframe Hpr Hlk Hback

/-- The state interpretation's lattice and log authorities. -/
theorem SilRegZero.siLatLog (g : WGState) :
    weakStateInterp (hlc := hlc) (GF := GF) g ⊢ wlatInterp g.wgimg g.wglog ∗ wlogAuth g.wglog := by
  unfold weakStateInterp
  iintro ⟨-, -, -, -, -, -, Ha, Hl, -⟩
  isplitl [Hl]
  · iexact Hl
  · iexact Ha

/-! # 2. The export, the twin adequacy, the package -/

/-- **THE EXPORT WITH THE ZERO**: `wprotRegdExport`'s three clauses and `regZeroAt`, at one
registration point. -/
theorem SilRegZero.wprotRegdZExport (img : Image) (N : Namespace) (E : CoPset) (g : WGState)
    (a base : Int) :
    ↑N ⊆ E →
    weakStateInterp (hlc := hlc) (GF := GF) g ∗ SilRegZero.wprotRegdZ (hlc := hlc) img N a base ⊢
      |={E}=> ⌜∃ (n0 r0 : Nat) (h : Option Nat),
        wprotAt g.wglog a base n0 r0 ∧ wlpAt g.wglog base base n0 ∧ wlpAlt g.wglog base n0 h ∧
        CertZ18.regZeroAt img g.wglog base n0⌝ := by
  intro hN
  iintro ⟨Hsi, #Hreg⟩
  ihave H2 := SilRegZero.siLatLog g $$ Hsi
  icases H2 with ⟨Hlat, Hla⟩
  unfold SilRegZero.wprotRegdZ
  icases Hreg with ⟨%I, #Hinv, #Hacc⟩
  iinv Hinv with HI Hclose
  ihave HQ : ▷ (∃ (γ : GName) (n0 r0 : Nat) (d : Option CPU) (h : Option Nat) (L0 : List Wmsg),
      wprotSt (GF := GF) a γ base n0 r0 d ∗ wlockSt base base n0 h ∗ wlogLb L0 ∗
      ⌜L0.length = n0 ∧ CertZ18.regZeroAt img L0 base n0⌝ ∗
      (wprotSt a γ base n0 r0 d -∗ wlockSt base base n0 h -∗ I)) $$ [HI]
  · imodintro
    iapply Hacc $$ HI
  icases later_exists.mpr $$ HQ with ⟨%γ, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%n0, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%r0, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%d, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%h, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%L0, HQ⟩
  icases later_sep.mp $$ HQ with ⟨>Hpr, HQ⟩
  icases later_sep.mp $$ HQ with ⟨>Hlk, HQ⟩
  icases later_sep.mp $$ HQ with ⟨>Hlb, HQ⟩
  icases later_sep.mp $$ HQ with ⟨>Hz, Hback⟩
  icases Hz with %hz
  ihave %hpre := wlogValid g.wglog L0 $$ [Hla Hlb]
  · iframe Hla Hlb
  ihave %hpa := wprotAtOfProt g.wgimg g.wglog a γ base n0 r0 d $$ [Hlat Hpr]
  · iframe Hlat Hpr
  ihave %hlp := wlpAtOfLock g.wgimg g.wglog base base n0 h $$ [Hlat Hlk]
  · iframe Hlat Hlk
  ihave %halt := wlpAltOfLock g.wgimg g.wglog base base n0 h $$ [Hlat Hlk]
  · iframe Hlat Hlk
  imod Hclose $$ [Hpr Hlk Hback]
  · imodintro
    iapply Hback $$ Hpr Hlk
  imodintro
  ipureintro
  exact ⟨n0, r0, h, hpa, hlp, halt,
    SilRegZero.regZeroPrefix img L0 g.wglog base n0 hz.1 hpre hz.2⟩

end interp

section adequacy

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- **`adequacyProtS` WITH THE ZERO**: from a twin WP package carrying `wprotRegdZ`, every twin run's
log satisfies `protRegZ`'s four clauses at the byte. -/
theorem SilRegZero.adequacyProtZS [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (g : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup) (img : Image)
    (N : Namespace) (a base : Int)
    (Hpow : g.wgpow = true) (Hgen0 : g.wggen = 0) (Hlog : g.wglog = [])
    (Hws : ∀ c : CPU, g.wgws c = wsInit)
    (Hwp : ∀ [MachGS hlc GF] [WeakGS GF],
      (([∗list] c ∈ cpus, [∗list] r ∈ D c, regPointsTo c r (DFrac.own 1) (g.wgregs c r)) ∗
        bigSepM (M := GMapF PAddr) (fun a0 b => wlatPointsto (paZ a0) (DFrac.own 1) 0 b)
          g.wgimg ∗
        ([∗list] c ∈ cpus, hartView c) ∗
        wlogLb [] ∗
        ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (g.wgdev.st d)))
      ⊢@{IProp GF} |={⊤}=>
        (SilRegZero.wprotRegdZ (hlc := hlc) img N a base ∗
          [∗list] e ∈ SilLang.epowerForkS gen, SilLang.ewpTrivS (hlc := hlc) (GF := GF) ⊤ e))
    (t2 : List SilLang.EExprS) (g2 : WGState)
    (hrtc : (SilLang.epowerForkS gen, g) -·->ₜₚ* (t2, g2)) :
    ∃ (n0 r0 : Nat) (h : Option Nat),
      wprotAt g2.wglog a base n0 r0 ∧ wlpAt g2.wglog base base n0 ∧ wlpAlt g2.wglog base n0 h ∧
      CertZ18.regZeroAt img g2.wglog base n0 := by
  refine SilLang.adequacyCoreS (hlc := hlc) (GF := GF) gen g D hD Hpow Hgen0 Hlog Hws
    (fun _ _ => SilRegZero.wprotRegdZ (hlc := hlc) img N a base) Hwp t2 g2 _ ?_ hrtc
  intro HR HW _
  exact SilRegZero.wprotRegdZExport img N ⊤ g2 a base CoPset.subseteq_top

end adequacy

/-- **THE TWIN WP PACKAGE WITH THE ZERO** (row 6j's obligation): `SilClose.wpPackageProtS` with
`wprotRegdZ` at the boot image. -/
def SilRegZero.wpPackageProtZS (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (Nm : Namespace)
    (a base : Int) : Prop :=
  ∀ [MachGS hlc GF] [WeakGS GF],
    (([∗list] cc ∈ cpus, [∗list] r ∈ D cc, regPointsTo cc r (DFrac.own 1) (σ0.wgregs cc r)) ∗
      bigSepM (M := GMapF PAddr) (fun a0 b => wlatPointsto (paZ a0) (DFrac.own 1) 0 b)
        σ0.wgimg ∗
      ([∗list] cc ∈ cpus, hartView cc) ∗
      wlogLb [] ∗
      ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (σ0.wgdev.st d)))
    ⊢@{IProp GF} |={⊤}=>
      (SilRegZero.wprotRegdZ (hlc := hlc) (imgZ σ0.wgimg) Nm a base ∗
        [∗list] e ∈ SilLang.epowerForkS gen, SilLang.ewpTrivS (hlc := hlc) (GF := GF) ⊤ e)

/-- The package with the zero is a package. -/
theorem SilRegZero.wpPackageProtOfZ (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (Nm : Namespace)
    (a base : Int) :
    SilRegZero.wpPackageProtZS hlc GF gen σ0 D Nm a base →
    SilClose.wpPackageProtS hlc GF gen σ0 D Nm a base := by
  intro hz HR HW
  refine Entails.trans hz ?_
  iintro H
  imod H with ⟨HZ, Hl⟩
  imodintro
  isplitl [HZ]
  · iapply SilRegZero.wprotRegdOfZ (hlc := hlc) (GF := GF) (imgZ σ0.wgimg) Nm a base
    iexact HZ
  · iexact Hl

/-- **`protRegZ` along every twin run**, from the packages with the zero. -/
theorem SilRegZero.protRegZOfRunS (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (t2 : List SilLang.EExprS) (σ2 : WGState) :
    freshEra gen σ0 →
    (∀ a base, P a base → SilRegZero.wpPackageProtZS hlc GF gen σ0 D (Nm a base) a base) →
    (SilLang.epowerForkS gen, σ0) -·->ₜₚ* (t2, σ2) →
    CertZ18.protRegZ P (imgZ σ0.wgimg) σ2.wglog := by
  rintro ⟨-, hpow, hgen0, hlog, hws⟩ hwp hrtc a base hP
  exact SilRegZero.adequacyProtZS (hlc := hlc) (GF := GF) gen σ0 D hD (imgZ σ0.wgimg) (Nm a base)
    a base hpow hgen0 hlog hws (hwp a base hP) t2 σ2 hrtc

/-- **ROW 6k DISCHARGED from the packages with the zero**: `SilClose.regZeroS`. -/
theorem SilRegZero.regZeroOfZ (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (∀ a base, P a base → SilRegZero.wpPackageProtZS hlc GF0 gen σ0 D (Nm a base) a base) →
    SilClose.regZeroS gen σ0 boot d0 fab N P := by
  intro hfr hwpz _ _ c _ _ _ t2 σ2 _ _ _ _ _ hrtc hlg _
  rw [← hlg]
  exact SilRegZero.protRegZOfRunS hlc GF0 gen σ0 D hD Nm P t2 σ2 hfr hwpz hrtc

/-! # 3. kill′ with the zero in the package -/

/-- **`cycleKillZS`** — `SilClose.cycleKillS` with ONE `wpPackageProtZS` in place of
`wpPackageProtS` + `regZeroS`. SUPERSEDED by the trimmed route (`Weak/SilKillT.lean`,
`SilKillT.cycleKillZS`): concludes the untrimmed `cycleKillCZC`, likely false as quantified
(`fetchProv` fails at an untrimmed class graph, `Weak/CapFetchProv.lean`). -/
theorem SilRegZero.cycleKillZS (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
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
    SilKill.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpz hcov hpre hordS h1b hstep hAQ hRC hl2 =>
    SilClose.cycleKillS hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp
      (fun a base hP => SilRegZero.wpPackageProtOfZ hlc GF0 gen σ0 D (Nm a base) a base
        (hwpz a base hP))
      hcov hpre hordS h1b hstep hAQ hRC
      (SilRegZero.regZeroOfZ hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hwpz) hl2

/-- `SilClose.cycleKillDiscS` (the order derived) with the zero in the package. SUPERSEDED by the
trimmed route (`Weak/SilKillT.lean`, `SilKillT.cycleKillDiscZS`): concludes the untrimmed
`cycleKillCZC`, likely false as quantified (`fetchProv` fails at an untrimmed class graph,
`Weak/CapFetchProv.lean`). -/
theorem SilRegZero.cycleKillDiscZS (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
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
    SilKill.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpz hcov hpre hdisc hwio hstep hAQ hRC hl2 =>
    SilClose.cycleKillDiscS hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp
      (fun a base hP => SilRegZero.wpPackageProtOfZ hlc GF0 gen σ0 D (Nm a base) a base
        (hwpz a base hP))
      hcov hpre hdisc hwio hstep hAQ hRC
      (SilRegZero.regZeroOfZ hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hwpz) hl2

/-- `SilClose.cycleKillCZS` (⇒ `cycleKillCZ`, `t2linSupplyCZIO`'s input) with the zero in the
package. SUPERSEDED by the trimmed route (`Weak/SilKillT.lean`, `SilKillT.cycleKillZS`;
`CapFetchProv.t2linSupplyCZT` takes `cycleKillCZT` directly): rests on the untrimmed `cycleKillCZC`,
likely false as quantified (`fetchProv` fails at an untrimmed class graph,
`Weak/CapFetchProv.lean`). -/
theorem SilRegZero.cycleKillCZZS (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
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
    SilKill.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZ boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpz hcov hpre hordS h1b hstep hAQ hRC hl2 =>
    cycleKillCZOfC boot d0 fab _
      (SilRegZero.cycleKillZS hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpz hcov
        hpre hordS h1b hstep hAQ hRC hl2)

end ghost

end CatLin

end Weak
