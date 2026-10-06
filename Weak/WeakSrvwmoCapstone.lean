/-
Weak: **THE TIER-1 FINAL THEOREM** (A4): adequacy ∘ T1.

Rocq: `iris/WeakSrvwmoCapstone.v` @ xxvzwolszwmp (1cc222280).

## The Rocq header, in substance

    [WP package]  ⇒  (adequacy over the pf event language)
                  ∘  [T1: sRVWMO ⊆ pf, program-carrying]
                  =  xv6 is safe on every hart of every machine implementing sRVWMO.

`xv6SrvwmoSafe` says: EVERY sRVWMO-consistent execution whose trace the xv6 event programs can
emit (`execProgOk'` — T1's conformance interface, with the administrative STAR and the exclusive
PAIR arm) is REALIZED by a run of the promise-free event language from the booted initial state,
ending at the same log and the same per-agent program states; and — the adequacy half,
candidate-independent — every reachable configuration of that language is violation-free and
every thread of every reachable erased configuration is reducible.  The realization runs at
`WeakPromiseBridge.cfgMatchd` (image and LOG equal, per-agent `Wstate`s `wsEqr`-related).  The
other half of the characterization is T2 (`WeakEvInst.t2Ev`).  Premise ledger: (a) four machine
facts about a booted σ0; (b) THE WP PACKAGE, verbatim `WeakEvAdequacy.weakEvPfViolationFree`'s;
(c) `srvwmoConsistent`, the boot image, the initial program states / fabric, and the
conformance supply `execProgOk'`.  `pclsEqr pclsEv` is not a premise (`WeakEvCapstone.pclsEvEqr`).
No `mainPremises`, no robustness package, no retag.

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below).  `pa_st <$> pc_ags c` ↦
   `c.pcAgs.map Wpagent.paSt`; `img_z` ↦ `imgZ`; `erased_step` rtc ↦ `-·->ₜₚ*`;
   `reducible e σ` ↦ `Reducible (e, σ)`.  `Σ`, `riscvGpreS`, `weakGpreS` ↦ `hlc`, `GF`,
   `MachGpreS`, `WeakGpreS`; `D : CPU → gset register` ↦ `D : CPU → List Register` with `hD`
   (WeakEvAdequacy deviations 2, 3); the WP package is `weakEvPfViolationFree`'s verbatim
   (device fragments as `[∗list] d ∈ DevId.all, devFragAt …`).
2. THE FABRIC (WeakEvCapstone deviation 8): `dv : Nat → Efab` and `pst : Nat → List Pexv6`;
   the premise `dv 0 = dev_state σ0` becomes `dv 0 = efInit σ0.wgdev` (every residual device
   program at `.pure ()`).
3. O2 — THE FETCH-VIEW PREMISE (WeakEvCapstone deviation 2, Lean-only): the ⇒ language lift
   `wpPfRtcEpfRtc` needs `efetchItvOk` at every `epfRun`-reachable state, so the capstone CARRIES
   premise (b') `∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2` (dischargeable by
   `WeakEvCapstone.efetchItvOkRunOfUnwritten` from "no reachable log writes a fetched byte";
   nothing here proves the kernel text unwritten).  Only the T1 conjunct uses it.
4. O2 — THE FETCH-INERTNESS GATE (WeakAxRealize deviation 4): Lean's `lblRealizes` has the fifth
   conjunct `lbFetchInert`, so hypothesis (c)'s `execProgOk'` is (for a realizing `LIFetch`
   step only) STRONGER than Rocq's: such a step must be `wsEqr`-inert as a load at the axiomatic
   `Wstate`.  It is CARRIED inside `execProgOk'` (no general discharge: `loadPostRun` moves
   `coh`/`wVrOld`).  It IS discharged for a supply whose single realizing steps are not fetches:
   the Lean-only `execProgOkNf'` (the 4 Rocq gates plus `lbNoFetch`; the pair arm is unchanged —
   `lblRealizesPair` has no fetch gate), `execProgOkNf'Ok`, and the corollary
   `xv6SrvwmoSafeNoFetch`.
5. PROOFS: the Rocq script, with `cfgMatchd`'s log conjunct and `candElog` as in Rocq.

**Rocq → Lean name map.**  `xv6_srvwmo_safe` ↦ `xv6SrvwmoSafe`.  Lean-only (file-qualified):
`WeakSrvwmoCapstone.lbFetchInertOfNoFetch`, `WeakSrvwmoCapstone.lblRealizesOfNoFetch`,
`WeakSrvwmoCapstone.execProgOkNf'`, `WeakSrvwmoCapstone.execProgOkNf'Ok`,
`WeakSrvwmoCapstone.xv6SrvwmoSafeNoFetch`.

**Not ported:** nothing (the Rocq `Print Assumptions` audit comment is not a declaration).
-/
import Weak.WeakEvCapstone
import Weak.WeakAxRealize
import Weak.WeakAxiomatic3

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! ## Lean-only: discharging the fetch gate off the fetch (deviation 4) -/

theorem WeakSrvwmoCapstone.lbFetchInertOfNoFetch (σ : Mstate) (i : Nat) (l : Wlabel) :
    lbNoFetch l → lbFetchInert σ i l := by
  intro h
  cases l <;> first | exact trivial | exact absurd h id

theorem WeakSrvwmoCapstone.lblRealizesOfNoFetch {P : Type}
    (pcls : P → Wlabel → Wstate → WmClass) (p : P) (σ : Mstate) (i : Nat) (lb : Lbl)
    (l : Wlabel) :
    lbNobarex l → latFree l → lbRfoldfree l → projLbl (pcls p l (σ.msWs i)) l = some lb →
    lbNoFetch l → lblRealizes pcls p σ i lb l :=
  fun h1 h2 h3 h4 h5 => ⟨h1, h2, h3, h4, WeakSrvwmoCapstone.lbFetchInertOfNoFetch σ i l h5⟩

/-- `execProgOk'` with the single realizing step gated by Rocq's four conjuncts and `lbNoFetch`
(Lean-only, deviation 4). -/
def WeakSrvwmoCapstone.execProgOkNf' {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    Prop :=
  ∀ (k : Nat) (s : Estep), E.exTr[k]? = some s →
    ∃ (p pa : P) (da : D) (p' : P),
      (pst k)[s.esAg]? = some p ∧
      pst (k + 1) = (pst k).set s.esAg p' ∧
      admStar pstep true p (dv k) pa da ∧
      ((∃ l, (lbNobarex l ∧ latFree l ∧ lbRfoldfree l ∧
                projLbl (pcls pa l ((stt E k).msWs s.esAg)) l = some s.esLb ∧ lbNoFetch l) ∧
              pstep pa da l p' (dv (k + 1)))
       ∨ (∃ (pm : P) (dm : D) (pm2 : P) (dm2 : D) (l1 l2 : Wlabel),
            lblRealizesPair pcls pa pm2 (stt E k) s.esAg s.esLb l1 l2 ∧
            pstep pa da l1 pm dm ∧
            admStar pstep false pm dm pm2 dm2 ∧
            pstep pm2 dm2 l2 p' (dv (k + 1))))

theorem WeakSrvwmoCapstone.execProgOkNf'Ok {P D : Type}
    (pstep : P → D → Wlabel → P → D → Prop) (pcls : P → Wlabel → Wstate → WmClass)
    (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    WeakSrvwmoCapstone.execProgOkNf' pstep pcls pst dv E → execProgOk' pstep pcls pst dv E := by
  intro h k s hs
  obtain ⟨p, pa, da, p', hp, hn, hst, hsup⟩ := h k s hs
  refine ⟨p, pa, da, p', hp, hn, hst, ?_⟩
  rcases hsup with ⟨l, ⟨h1, h2, h3, h4, h5⟩, hps⟩ | hpair
  · exact .inl ⟨l, WeakSrvwmoCapstone.lblRealizesOfNoFetch pcls pa _ _ _ l h1 h2 h3 h4 h5, hps⟩
  · exact .inr hpair

/-! ## THE TIER-1 CAPSTONE -/

section capstone

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- Rocq `xv6_srvwmo_safe`.  Ledger: (a) the booted-σ0 facts; (b) THE WP PACKAGE; (b') THE
FETCH-VIEW PREMISE (deviation 3); (c) the sRVWMO side, with the fetch gate inside `execProgOk'`
(deviation 4). -/
theorem xv6SrvwmoSafe [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (cd : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (Hgen : gen = 0)
    (Hpow : σ0.wgpow = true) (Hgen0 : σ0.wggen = 0) (Hlog : σ0.wglog = [])
    (Hws : ∀ cc : CPU, σ0.wgws cc = wsInit) :
    -- (b) THE WP PACKAGE
    (∀ [MachGS hlc GF] [WeakGS GF],
      (([∗list] cc ∈ cpus, [∗list] r ∈ D cc, regPointsTo cc r (DFrac.own 1) (σ0.wgregs cc r)) ∗
        bigSepM (M := GMapF PAddr) (fun a b => wlatPointsto (paZ a) (DFrac.own 1) 0 b) σ0.wgimg ∗
        ([∗list] cc ∈ cpus, hartView cc) ∗
        wlogLb [] ∗
        ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (σ0.wgdev.st d)))
      ⊢@{IProp GF} |={⊤}=> ([∗list] e ∈ epowerFork gen, ewpTriv (hlc := hlc) (GF := GF) ⊤ e)) →
    -- (b') THE FETCH-VIEW PREMISE (deviation 3)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    -- (c) THE MODEL SIDE
    srvwmoConsistent cd →
    cd.cdImg = imgZ σ0.wgimg →
    pst 0 = epsInit σ0 →
    dv 0 = efInit σ0.wgdev →
    execProgOk' pstepEv pclsEv pst dv (candExec cd) →
    -- T1 ∘ the language lift
    (∃ P' σ',
      rtc epfRun (epInit gen, σ0) (P', σ') ∧
      σ'.wglog = cdLog cd cd.cdTr.length ∧
      (ecfgOf P' σ').pcAgs.map Wpagent.paSt = pst cd.cdTr.length) ∧
    -- ADEQUACY: violation-freedom ...
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → ¬ violationHart clsOf pubOf nDisk (ecfgOf ρ.1 ρ.2)) ∧
    -- ... and reducibility
    (∀ (t2 : List EExpr) (σ2 : WGState) (e2 : EExpr),
      (epowerFork gen, σ0) -·->ₜₚ* (t2, σ2) → e2 ∈ t2 → Reducible (e2, σ2)) := by
  intro Hwp Hcov Hcons Himg Hpst0 Hdv0 Hprog
  have hlive : ethreadLive σ0 gen := ⟨Hpow, by rw [Hgen0, Hgen]⟩
  refine ⟨?_, ?_, ?_⟩
  · -- T1: realizability, program-carried, then lifted to the language
    obtain ⟨hwf, -, heximg⟩ := srvwmoRealizable cd Hcons
    obtain ⟨c, hrun, hpg, -, hm⟩ :=
      execWfPfRunProg pstepEv pclsEv pst dv (candExec cd) pclsEvEqr hwf Hprog
    rw [heximg, Himg, Hpst0, Hdv0, ← ecfgOfInit gen σ0 Hlog Hws] at hrun
    obtain ⟨P', σ', hr, heq⟩ := wpPfRtcEpfRtc (epInit gen) σ0 c hlive Hcov hrun
    refine ⟨P', σ', hr, ?_, ?_⟩
    · obtain ⟨-, hlg, -⟩ := hm
      rw [← ecfgOfLog P' σ', heq, ← hlg, candExTr]
      exact candElog cd cd.cdTr.length (Nat.le_refl _)
    · rw [heq, hpg, candExTr]
  · intro ρ hρ
    exact weakEvPfViolationFree (hlc := hlc) (GF := GF) gen σ0 D hD Hgen Hpow Hgen0 Hlog Hws Hwp
      ρ hρ
  · intro t2 σ2 e2 hrtc he2
    exact weakEvAdequacyReducible (hlc := hlc) (GF := GF) gen σ0 D hD Hgen Hpow Hgen0 Hlog Hws
      Hwp t2 σ2 e2 hrtc he2

/-- Lean-only (deviation 4): the capstone for a NO-FETCH supply — the fetch gate discharged. -/
theorem WeakSrvwmoCapstone.xv6SrvwmoSafeNoFetch [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (cd : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (Hgen : gen = 0)
    (Hpow : σ0.wgpow = true) (Hgen0 : σ0.wggen = 0) (Hlog : σ0.wglog = [])
    (Hws : ∀ cc : CPU, σ0.wgws cc = wsInit) :
    (∀ [MachGS hlc GF] [WeakGS GF],
      (([∗list] cc ∈ cpus, [∗list] r ∈ D cc, regPointsTo cc r (DFrac.own 1) (σ0.wgregs cc r)) ∗
        bigSepM (M := GMapF PAddr) (fun a b => wlatPointsto (paZ a) (DFrac.own 1) 0 b) σ0.wgimg ∗
        ([∗list] cc ∈ cpus, hartView cc) ∗
        wlogLb [] ∗
        ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (σ0.wgdev.st d)))
      ⊢@{IProp GF} |={⊤}=> ([∗list] e ∈ epowerFork gen, ewpTriv (hlc := hlc) (GF := GF) ⊤ e)) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    srvwmoConsistent cd →
    cd.cdImg = imgZ σ0.wgimg →
    pst 0 = epsInit σ0 →
    dv 0 = efInit σ0.wgdev →
    WeakSrvwmoCapstone.execProgOkNf' pstepEv pclsEv pst dv (candExec cd) →
    (∃ P' σ',
      rtc epfRun (epInit gen, σ0) (P', σ') ∧
      σ'.wglog = cdLog cd cd.cdTr.length ∧
      (ecfgOf P' σ').pcAgs.map Wpagent.paSt = pst cd.cdTr.length) ∧
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → ¬ violationHart clsOf pubOf nDisk (ecfgOf ρ.1 ρ.2)) ∧
    (∀ (t2 : List EExpr) (σ2 : WGState) (e2 : EExpr),
      (epowerFork gen, σ0) -·->ₜₚ* (t2, σ2) → e2 ∈ t2 → Reducible (e2, σ2)) :=
  fun Hwp Hcov Hcons Himg Hpst0 Hdv0 Hprog =>
    xv6SrvwmoSafe (hlc := hlc) (GF := GF) gen σ0 D hD cd pst dv Hgen Hpow Hgen0 Hlog Hws Hwp Hcov
      Hcons Himg Hpst0 Hdv0
      (WeakSrvwmoCapstone.execProgOkNf'Ok pstepEv pclsEv pst dv (candExec cd) Hprog)

end capstone

end Weak
