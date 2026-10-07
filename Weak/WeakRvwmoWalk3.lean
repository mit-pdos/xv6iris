/-
Weak: **R-2: THE CERTIFICATION WALK, part 3 — the capstone shape, restated** (Rocq §5; §1–§4
are `WeakRvwmoWalk`, §4.5–§4.6 `WeakRvwmoWalkb`).

Rocq: `iris/WeakRvwmoWalk.v` @ xxvzwolszwmp (split at its section boundaries; this part imports
`Weak.WeakRvwmoWalk` and `Weak.WeakRvwmoCapstone`).

## The Rocq header, in substance

`WeakRvwmoGlue2`'s theorems and `WeakRvwmoCapstone`'s capstone take (R-2) as the opaque
`walkSupply`.  `WeakRvwmoWalk` §2–§4 replace it by the per-state certification policy
(`walkSupplyOfPolicy`), so the same statements hold with (R-2) spelled out: `cycleKillOfL2''''`,
`t2linOfL2'''` and `xv6RvwmoSafeModuloWalk`.  The capstone file is not edited: these are
corollaries.  §6 (the `Print Assumptions` audit) and §7 (the ledger) are Rocq commands/comments.

## Deviations from Rocq

1. NAMES / VOCABULARY as `WeakRvwmoGlue2` deviations 1-3 and `WeakRvwmoCapstone` deviation 1
   (explicit `hlc GF` with `[MachGpreS hlc GF] [WeakGpreS GF]`, `D : CPU → List Register` with
   `hD : ∀ c, (D c).Nodup`; `d0 = wgdev σ0` ↦ `d0 = efInit σ0.wgdev`; at the canonical tie
   `wgdev σ0` ↦ `efInit σ0.wgdev`).
2. CARRIED PREMISE (O2 / Stage C: the only fetch premise left; not discharged here):
   THE FETCH-VIEW PREMISE `∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2`
   (`WeakRvwmoGlue2` deviation 4, owner Q4): all three theorems, placed right after the WP
   package premises (as `cycleKillOfL2''`/`t2linOfL2''`/`xv6RvwmoSafeModulo`).  Stage B's
   whole-graph `WeakRvwmoCapstone.t2linFetchInert` premise of `xv6RvwmoSafeModuloWalk` is
   DELETED (with `WeakRvwmoCapstone`'s), and `walkPolicy` carries nothing fetch-specific.

**Rocq → Lean name map.**  `cycle_kill_of_l2''''` `cycleKillOfL2''''`, `t2lin_of_l2'''`
`t2linOfL2'''`, `xv6_rvwmo_safe_modulo_walk` `xv6RvwmoSafeModuloWalk`.

**File-qualified names:** none (no name of this part is in `notes/weak-port-dupnames.json`; no
Lean-only helpers).

**Dropped:** none (§5: Rocq 3 declarations; Lean 3).
-/
import Weak.WeakRvwmoWalk
import Weak.WeakRvwmoCapstone

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

section walkCapstone

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-! # 5. THE CAPSTONE SHAPE, RESTATED -/

/-- Rocq `cycle_kill_of_l2''''` (deviations 1-2). -/
theorem cycleKillOfL2'''' (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    l2Claim boot d0 (imgZ σ0.wgimg) N P (badRun gen σ0) →
    -- (R-2), spelled out: the certification walk's per-state policy
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD →
       gdexecQconf boot d0 (imgZ σ0.wgimg) N GD →
       walkPolicy boot d0 N GD.gdG) →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    -- THE FETCH-VIEW PREMISE (deviation 2)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    cycleKill boot d0 (imgZ σ0.wgimg) N :=
  fun hfr hb1 hb2 hl2 hpol hwp hwpp hcov =>
    cycleKillOfL2'' hlc GF gen σ0 D hD Nm P boot d0 N hfr hb1 hb2 hl2
      (walkSupplyOfPolicy boot d0 _ N N hpol) hwp hwpp hcov

/-- Rocq `t2lin_of_l2'''` (deviations 1-2). -/
theorem t2linOfL2''' (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    l2Claim boot d0 (imgZ σ0.wgimg) N P (badRun gen σ0) →
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD →
       gdexecQconf boot d0 (imgZ σ0.wgimg) N GD →
       walkPolicy boot d0 N GD.gdG) →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    ∀ GD : Gdexec,
      rvwmoMinusDepsConsistent GD →
      gdexecQconf boot d0 (imgZ σ0.wgimg) N GD →
      ∀ x, ¬ tc (racyD GD) x x :=
  fun hfr hb1 hb2 hl2 hpol hwp hwpp hcov =>
    t2linOfL2'' hlc GF gen σ0 D hD Nm P boot d0 N hfr hb1 hb2 hl2
      (walkSupplyOfPolicy boot d0 _ N N hpol) hwp hwpp hcov

/-- Rocq `xv6_rvwmo_safe_modulo_walk` (deviations 1-2): THE CAPSTONE, with (R-2) replaced by the
walk's policy. -/
theorem xv6RvwmoSafeModuloWalk (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop) :
    freshEra gen σ0 →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    -- THE FETCH-VIEW PREMISE (deviation 2)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    -- (R-1)
    l2Claim (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) P (badRun gen σ0) →
    -- (R-2), as the walk's per-state policy
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD →
       gdexecQconf (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GD →
       walkPolicy (xboot σ0) (efInit σ0.wgdev) (xN σ0) GD.gdG) →
    ∀ GD : Gdexec,
      rvwmoMinusDepsConsistent GD →
      gdexecQconf (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GD →
      (∀ x, ¬ tc (racyD GD) x x) ∧
      (∃ (c : Cand) (pst : Nat → List Pexv6) (P' : Epool) (σ' : WGState),
        srvwmoConsistent c ∧
        c.cdImg = imgZ σ0.wgimg ∧
        pst 0 = epsInit σ0 ∧
        execProgOk' pstepEv pclsEv pst (fun _ => efInit σ0.wgdev) (candExec c) ∧
        rtc epfRun (epInit gen, σ0) (P', σ') ∧
        σ'.wglog = cdLog c c.cdTr.length ∧
        (ecfgOf P' σ').pcAgs.map Wpagent.paSt = pst c.cdTr.length) ∧
      (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → ¬ violationHart clsOf pubOf nDisk (ecfgOf ρ.1 ρ.2)) ∧
      (∀ (t2 : List EExpr) (σ2 : WGState) (e2 : EExpr),
        (epowerFork gen, σ0) -·->ₜₚ* (t2, σ2) → e2 ∈ t2 → Reducible (e2, σ2)) :=
  fun hfr hwp hwpp hcov hl2 hpol =>
    xv6RvwmoSafeModulo hlc GF gen σ0 D hD Nm P hfr hwp hwpp hcov hl2
      (walkSupplyOfPolicy _ _ _ _ _ hpol)

end walkCapstone

end Weak
