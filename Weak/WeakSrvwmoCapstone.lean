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
conformance supply `execProgOk'` at the boot-image-pinned LTS (deviation 4).  `pclsEqr pclsEv` is not a premise (`WeakEvCapstone.pclsEvEqr`).
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
4. O2 Stage C — THE FETCH PIN (WeakAxRealize deviation 4): fetches are ADMINISTRATIVE labels
   (no row item; `lblRealizes` has Rocq's 4 conjuncts — the Stage-B gate `lbFetchInert`/`lbNoFetch`
   and the Lean-only no-fetch corollaries of this file are DELETED).  The graph tier's fetch oracle
   (a fetch answers the boot image at timestamp 0, Rocq `AStepFetch`/`fetch_answers`) becomes the
   pin on the program LTS: hypothesis (c) is `execProgOk' (pstepPin (imgZ σ0.wgimg) pstepEv) …`
   (Rocq: `execProgOk' pstepEv …`), i.e. every supplied step's fetch label is pinned to the boot
   image.  The replay is `WeakAxRealize.execWfPfRunProg` at the pinned LTS (discharging
   `pstepPinned` by `pstepPinPinned`; the administrative stars through `admStarPf`), projected to
   the unpinned `wpPfRun pstepEv` by `wpPfRunPinSub`.  The conclusions are Rocq's.
5. PROOFS: the Rocq script, with `cfgMatchd`'s log conjunct and `candElog` as in Rocq.

**Rocq → Lean name map.**  `xv6_srvwmo_safe` ↦ `xv6SrvwmoSafe`.  No Lean-only declarations.

**Not ported:** nothing (the Rocq `Print Assumptions` audit comment is not a declaration).
-/
import Weak.WeakEvCapstone
import Weak.WeakAxRealize
import Weak.WeakAxiomatic3

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! ## THE TIER-1 CAPSTONE -/

section capstone

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- Rocq `xv6_srvwmo_safe`.  Ledger: (a) the booted-σ0 facts; (b) THE WP PACKAGE; (b') THE
FETCH-VIEW PREMISE (deviation 3); (c) the sRVWMO side, the supply at the boot-image-pinned LTS (deviation 4). -/
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
    execProgOk' (pstepPin (imgZ σ0.wgimg) pstepEv) pclsEv pst dv (candExec cd) →
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
    have hpin : pstepPinned (exImg (candExec cd)) (pstepPin (imgZ σ0.wgimg) pstepEv) := by
      rw [heximg, Himg]; exact pstepPinPinned _ _
    obtain ⟨c, hrun, hpg, -, hm⟩ :=
      execWfPfRunProg (pstepPin (imgZ σ0.wgimg) pstepEv) pclsEv pst dv (candExec cd) pclsEvEqr
        hpin hwf Hprog
    have hrun := wpPfRunPinSub _ pstepEv pclsEv _ _ hrun
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

end capstone

end Weak
