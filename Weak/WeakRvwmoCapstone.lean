/-
Weak: **THE TIER-2 CAPSTONE, MODULO THE RESIDUE** (B3, route B).

Rocq: `iris/WeakRvwmoCapstone.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Take the booted xv6 machine state σ0 (a FRESH ERA) and the EWP package the kernel proofs supply.
Then EVERY graph `GD` that is RVWMO⁻(+deps)-consistent and CONFORMANT to the xv6 image at the
booted boot states (`gdexecQconf boot d0 (imgZ σ0.wgimg) N`) is `racyD`-ACYCLIC, is REALIZED by a
promise-free run of the event language from `(epInit gen, σ0)` whose final log is the realizing
candidate's own log, and — candidate-independently — every reachable configuration is
violation-free and every thread of every reachable configuration is reducible.  That is
`xv6SrvwmoSafe`'s conclusion, reached from a GRAPH rather than a hand-supplied sRVWMO candidate.

The chain: T2-LIN (`t2linOfL2''`, whose step `cycleKill` is `cycleKillOfL2''`) → TOPO
(`topoSupply` via `racyDDec`) → T2-1c (`rule14Linearization`) → T1 + adequacy (`xv6SrvwmoSafe`).
The two RESIDUAL hypotheses, quoted from `WeakRvwmoGlue2.t2linOfL2''`: (R-1) `l2Claim` — L2′
proper, the project's remaining content; (R-2) `walkSupply` — the certification walk.

  §1  THE BOOT TIE at the canonical `xboot σ0` / `xN σ0` (`xbootSeq`).
  §2  `xv6RvwmoSafeModuloGen` (arbitrary boot tie) and `xv6RvwmoSafeModulo` (canonical).
  §3  `xv6RvwmoSafeModuloF`: the full (moving-fabric) bundle from the REVISED axiom
      `gfexecConsistent'` (Rocq TODO (F-a)/(F-b): no derivation from `l2Claim` there).
  §4  NON-VACUITY of the model-side premises at `mpwd` / `mpwd'` (graph side only).

§5 (the `Print Assumptions` audit) is Rocq commands.  A LEAF.

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below); `seq 0 N` ↦ `List.range' 0 N`; `f <$> l` ↦
   `l.map f`; `default d (l !! i)` ↦ `(l[i]?).getD d`; `PDisk None` ↦ `.PDisk none`;
   `Σ`/`riscvGpreS`/`weakGpreS` ↦ explicit `hlc GF` with `[MachGpreS hlc GF] [WeakGpreS GF]`;
   `D : CPU → List Register` with `hD : ∀ c, (D c).Nodup` (WeakRvwmoGlue deviation 3); the
   Rocq graph-bundle variable `GF : gfexec` of §3 is `GX : Gfexec` (`GF` names the functors).
   `rtc erased_step` ↦ `-·->ₜₚ*`, `reducible e σ` ↦ `Reducible (e, σ)`, `pa_st <$> pc_ags` ↦
   `.pcAgs.map Wpagent.paSt` (WeakSrvwmoCapstone deviation 1).
2. THE BOOT DEVICE STATE (WeakRvwmoGlue2 deviation 2): Rocq's `d0 = wgdev σ0` is
   `d0 = efInit σ0.wgdev`; at the canonical tie `d0 := efInit σ0.wgdev` (Rocq `wgdev σ0`), and
   the conclusions' fabric `λ _, wgdev σ0` is `fun _ => efInit σ0.wgdev`; §3's `dv 0 = wgdev σ0`
   is `dv 0 = efInit σ0.wgdev`.
3. O2 — THE FETCH-VIEW PREMISE, CARRIED (WeakRvwmoGlue2 deviation 4 / WeakSrvwmoCapstone
   deviation 3, owner Q4): all three safety theorems take
   `∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2`, placed right after the WP package
   premises (as in `t2linOfL2''`).
4. O2 Stage C — THE PINNED PROGRAM LTS (spec item 16; WeakRvwmoLinInd / WeakRvwmoLin2 /
   WeakSrvwmoCapstone).  The fetch is an administrative label of the graph tier, so there is no
   fetch-inertness obligation: `t2linSupply` and `fconfTraceRealize` return the process supply
   unconditionally, at the PINNED LTS `pstepPin img pstepEv` (`img` the graph's image, equal to
   `imgZ σ0.wgimg` by `gdexecQconfImg` / the image premise).  The capstones hand that supply to
   `xv6SrvwmoSafe` (which lifts through `execWfPfRunProg` / `wpPfRunPinSub`), and state the
   Rocq conclusion `execProgOk' pstepEv …` via the Lean-only
   `WeakRvwmoCapstone.execProgOkPinSub` (the pinned LTS is a sub-LTS).  The provisional (Q5)
   Lean-only premises `t2linFetchInert` / `fconfFetchInert` and the helper `t2linSupplyRows`
   are DELETED; the only fetch premise left is the efetchItvOk fetch-view premise (deviation 3,
   Q4).  Conclusions are Rocq's.
5. PROOFS: Rocq's scripts.  `defaultLookupSeq` by `List.ext_getElem`.
6. W-DISK (`WeakRvwmoFab` deviation 4): `xv6RvwmoSafeModuloF`'s statement is UNCHANGED; its
   proof discharges `fconfTraceRealize`'s new quiet-boot hypothesis from the boot tie
   `(List.range' 0 N).map boot = epsInit σ0` by the Lean-only `WeakRvwmoCapstone.epsInitQuiet`
   (the boot pool's harts, and the disk at `.PDisk none`).

**Rocq → Lean name map.**  `default_lookup_seq` `defaultLookupSeq`, `xboot` `xboot`, `xN` `xN`,
`xboot_seq` `xbootSeq`, `xv6_rvwmo_safe_modulo_gen` `xv6RvwmoSafeModuloGen`,
`xv6_rvwmo_safe_modulo` `xv6RvwmoSafeModulo`, `xv6_rvwmo_safe_modulo_F` `xv6RvwmoSafeModuloF`,
`model_premises_nonvacuous` `modelPremisesNonvacuous`, `model_premises_nonvacuous'`
`modelPremisesNonvacuous'`.
Lean-only (file-qualified): `WeakRvwmoCapstone.execProgOkPinSub`, `WeakRvwmoCapstone.epsInitQuiet`.

**File-qualified Rocq names:** none (no name of this file is in `notes/weak-port-dupnames.json`).

**Dropped:** none (Rocq 9 declarations; Lean 11 = 9 + the 2 Lean-only).
-/
import Weak.WeakRvwmoGlue2
import Weak.WeakSrvwmoCapstone
import Weak.WeakRvwmoLinInd
import Weak.WeakRvwmoLin2
import Weak.WeakRvwmoConfWit2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! # 1. THE BOOT TIE, discharged at the canonical `boot` -/

theorem defaultLookupSeq {A : Type} (d : A) (l : List A) :
    (List.range' 0 l.length).map (fun i => (l[i]?).getD d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

/-- The canonical boot function of a booted state. -/
def xboot (σ0 : WGState) : Nat → Pexv6 :=
  fun i => ((epsInit σ0)[i]?).getD (.PDisk none)

/-- The canonical hart count of a booted state. -/
def xN (σ0 : WGState) : Nat := (epsInit σ0).length

theorem xbootSeq (σ0 : WGState) : (List.range' 0 (xN σ0)).map (xboot σ0) = epsInit σ0 :=
  defaultLookupSeq (.PDisk none) (epsInit σ0)

/-! # 2. THE TIER-2 CAPSTONE, MODULO `l2Claim` AND `walkSupply` -/

/-! ## 2.0 Lean-only: the pinned LTS is a sub-LTS of `execProgOk'` (deviation 4) -/

/-- (Lean-only, deviation 4) A program-carried execution at the pinned LTS is one at the LTS. -/
theorem WeakRvwmoCapstone.execProgOkPinSub {P D : Type} (img : Image)
    (pstep : P → D → Wlabel → P → D → Prop) (pcls : P → Wlabel → Wstate → WmClass)
    (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    execProgOk' (pstepPin img pstep) pcls pst dv E → execProgOk' pstep pcls pst dv E := by
  intro h k s hk
  have hsub : ∀ (instr : Bool) (p : P) (d : D) (p' : P) (d' : D),
      admStar (pstepPin img pstep) instr p d p' d' → admStar pstep instr p d p' d' :=
    fun _ _ _ _ _ => rtc_subrel (fun _ _ ⟨l, ha, hs⟩ => ⟨l, ha, hs.1⟩)
  obtain ⟨p, pa, da, p', h1, h2, h3, h4⟩ := h k s hk
  refine ⟨p, pa, da, p', h1, h2, hsub _ _ _ _ _ h3, ?_⟩
  rcases h4 with ⟨l, hr, hs⟩ | ⟨pm, dm, pm2, dm2, l1, l2, hr, hs1, hst, hs2⟩
  · exact .inl ⟨l, hr, hs.1⟩
  · exact .inr ⟨pm, dm, pm2, dm2, l1, l2, hr, hs1.1, hsub _ _ _ _ _ hst, hs2.1⟩

section capstone

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-! ## 2.1 The workhorse, at an arbitrary boot tie -/

/-- Rocq `xv6_rvwmo_safe_modulo_gen` (deviations 1-4). -/
theorem xv6RvwmoSafeModuloGen (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) :
    -- (a) the fresh era, and the boot tie
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    -- (b) THE WP PACKAGE, in its two flavours
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    -- THE FETCH-VIEW PREMISE (deviation 3)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    -- (R-1) THE L2′ PER-SITE CLAIM
    l2Claim boot d0 (imgZ σ0.wgimg) N P (badRun gen σ0) →
    -- (R-2) THE CERTIFICATION WALK
    walkSupply boot d0 (imgZ σ0.wgimg) N N →
    -- (c) THE MODEL SIDE
    ∀ GD : Gdexec,
      rvwmoMinusDepsConsistent GD →
      gdexecQconf boot d0 (imgZ σ0.wgimg) N GD →
      -- T2-LIN
      (∀ x, ¬ tc (racyD GD) x x) ∧
      -- T2-1c ∘ T1 ∘ the language lift
      (∃ (c : Cand) (pst : Nat → List Pexv6) (P' : Epool) (σ' : WGState),
        srvwmoConsistent c ∧
        c.cdImg = imgZ σ0.wgimg ∧
        pst 0 = epsInit σ0 ∧
        execProgOk' pstepEv pclsEv pst (fun _ => d0) (candExec c) ∧
        rtc epfRun (epInit gen, σ0) (P', σ') ∧
        σ'.wglog = cdLog c c.cdTr.length ∧
        (ecfgOf P' σ').pcAgs.map Wpagent.paSt = pst c.cdTr.length) ∧
      -- ADEQUACY, candidate-independent
      (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → ¬ violationHart clsOf pubOf nDisk (ecfgOf ρ.1 ρ.2)) ∧
      (∀ (t2 : List EExpr) (σ2 : WGState) (e2 : EExpr),
        (epowerFork gen, σ0) -·->ₜₚ* (t2, σ2) → e2 ∈ t2 → Reducible (e2, σ2)) := by
  intro hfr hb1 hb2 hwp hwpp hcov hl2 hwalk GD hcons hq
  obtain ⟨hgen, hpow, hgen0, hlog, hws⟩ := hfr
  have hfr' : freshEra gen σ0 := ⟨hgen, hpow, hgen0, hlog, hws⟩
  -- the cycle-kill step, and T2-LIN itself
  have hk := cycleKillOfL2'' hlc GF gen σ0 D hD Nm P boot d0 N hfr' hb1 hb2 hl2 hwalk hwp hwpp hcov
  have hacy : ∀ x, ¬ tc (racyD GD) x x := t2linOfCycleKill boot d0 _ N hk GD hcons hq
  -- topo ∘ T2-1c: the sRVWMO candidate, at the pinned LTS (deviation 4)
  have hN := gdexecQconfNharts _ _ _ _ _ hq
  obtain ⟨c, pst, hsr, himg, hpst0, hprog⟩ := t2linSupply boot d0 _ N GD N hk hcons hq hN
  have himg' : c.cdImg = imgZ σ0.wgimg := by rw [himg, gdexecQconfImg _ _ _ _ _ hq]
  have hpst0' : pst 0 = epsInit σ0 := by rw [hpst0, hb1]
  rw [himg'] at hprog
  -- T1 ∘ adequacy
  obtain ⟨hreal, hvf, hred⟩ :=
    xv6SrvwmoSafe (hlc := hlc) (GF := GF) gen σ0 D hD c pst (fun _ => d0) hgen hpow hgen0 hlog
      hws hwp hcov hsr himg' hpst0' hb2 hprog
  obtain ⟨P', σ', hr, hlg, hpg⟩ := hreal
  exact ⟨hacy, ⟨c, pst, P', σ', hsr, himg', hpst0',
    WeakRvwmoCapstone.execProgOkPinSub _ _ _ _ _ _ hprog, hr, hlg, hpg⟩, hvf, hred⟩

/-! ## 2.2 THE CAPSTONE, at the canonical boot tie -/

/-- Rocq `xv6_rvwmo_safe_modulo` (deviations 1-4). -/
theorem xv6RvwmoSafeModulo (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop) :
    freshEra gen σ0 →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    -- THE FETCH-VIEW PREMISE (deviation 3)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    l2Claim (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) P (badRun gen σ0) →
    walkSupply (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) (xN σ0) →
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
  fun hfr hwp hwpp hcov hl2 hwalk =>
    xv6RvwmoSafeModuloGen hlc GF gen σ0 D hD Nm P (xboot σ0) (efInit σ0.wgdev) (xN σ0) hfr
      (xbootSeq σ0) rfl hwp hwpp hcov hl2 hwalk

end capstone

/-! # 3. THE FULL-BUNDLE VARIANT (a MOVING fabric) -/

section capstoneF

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- (Lean-only, W-DISK) The boot pool is QUIET: its harts, and the disk between bursts. -/
theorem WeakRvwmoCapstone.epsInitQuiet (σ : WGState) (p : Pexv6) (hp : p ∈ epsInit σ) :
    devQuiet p := by
  simp only [epsInit, List.mem_append, List.mem_map, List.mem_singleton] at hp
  rcases hp with ⟨c, _, rfl⟩ | rfl <;> trivial

/-- Rocq `xv6_rvwmo_safe_modulo_F` (deviations 1-4). -/
theorem xv6RvwmoSafeModuloF (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) (GX : Gfexec) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF gen σ0 D →
    -- THE FETCH-VIEW PREMISE (deviation 3)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    -- the model side: the REVISED axiom and the fabric conformance bundle
    gfexecConsistent' GX →
    gfexecConf boot d0 fab GX →
    GX.gfGd.gdG.gxImg = imgZ σ0.wgimg →
    GX.gfGd.gdG.gxProg.length ≤ N →
    (∃ (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab) (P' : Epool) (σ' : WGState),
      srvwmoConsistent c ∧
      c.cdImg = imgZ σ0.wgimg ∧
      pst 0 = epsInit σ0 ∧
      dv 0 = efInit σ0.wgdev ∧
      execProgOk' pstepEv pclsEv pst dv (candExec c) ∧
      rtc epfRun (epInit gen, σ0) (P', σ') ∧
      σ'.wglog = cdLog c c.cdTr.length ∧
      (ecfgOf P' σ').pcAgs.map Wpagent.paSt = pst c.cdTr.length) ∧
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → ¬ violationHart clsOf pubOf nDisk (ecfgOf ρ.1 ρ.2)) ∧
    (∀ (t2 : List EExpr) (σ2 : WGState) (e2 : EExpr),
      (epowerFork gen, σ0) -·->ₜₚ* (t2, σ2) → e2 ∈ t2 → Reducible (e2, σ2)) := by
  intro hfr hb1 hb2 hwp hcov hc' hconf himg hN
  obtain ⟨hgen, hpow, hgen0, hlog, hws⟩ := hfr
  -- W-DISK: the boot pool is quiet (`devQuiet`, `WeakRvwmoFab` deviation 4)
  have hquiet : ∀ i, i < N → devQuiet (boot i) := fun i hi =>
    WeakRvwmoCapstone.epsInitQuiet σ0 (boot i)
      (by rw [← hb1]; exact List.mem_map.2 ⟨i, by simp [List.mem_range'_1, hi], rfl⟩)
  obtain ⟨L, hsr, hcimg, _, _, pst, hp0, hd0, hok⟩ :=
    fconfTraceRealize boot d0 fab GX N hc' hconf hN hquiet
  rw [himg] at hok
  have himg' : (candOf GX.gfGd.gdG L).cdImg = imgZ σ0.wgimg := by rw [hcimg, himg]
  have hpst0 : pst 0 = epsInit σ0 := by rw [hp0, hb1]
  have hdv0 : (fun k => fab (dcnt GX (candOf GX.gfGd.gdG L).cdTr k)) 0 = efInit σ0.wgdev := by
    rw [← hb2]; exact hd0
  obtain ⟨hreal, hvf, hred⟩ :=
    xv6SrvwmoSafe (hlc := hlc) (GF := GF) gen σ0 D hD (candOf GX.gfGd.gdG L) pst
      (fun k => fab (dcnt GX (candOf GX.gfGd.gdG L).cdTr k)) hgen hpow hgen0 hlog hws hwp hcov
      hsr himg' hpst0 hdv0 hok
  obtain ⟨P', σ', hr, hlg, hpg⟩ := hreal
  exact ⟨⟨candOf GX.gfGd.gdG L, pst, fun k => fab (dcnt GX (candOf GX.gfGd.gdG L).cdTr k), P',
    σ', hsr, himg', hpst0, hdv0, WeakRvwmoCapstone.execProgOkPinSub _ _ _ _ _ _ hok, hr, hlg, hpg⟩,
    hvf, hred⟩

end capstoneF

/-! # 4. NON-VACUITY OF THE MODEL-SIDE PREMISES (graph side only, at the MP witness) -/

theorem modelPremisesNonvacuous (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (ib0 ib1 : Ibch)
    (d0 : Efab) :
    rvwmoMinusDepsConsistent mpwd ∧
    gdexecQconf (mpBoot cpu0 cpu1 rs0 rs1 ib0 ib1) d0 mpImg 2 mpwd :=
  ⟨mpwDepsConsistent, mpwQconf cpu0 cpu1 rs0 rs1 ib0 ib1 d0⟩

/-- The early-read variant (the load sees the era image). -/
theorem modelPremisesNonvacuous' (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (ib0 ib1 : Ibch)
    (d0 : Efab) :
    rvwmoMinusDepsConsistent mpwd' ∧
    gdexecQconf (mpBoot cpu0 cpu1 rs0 rs1 ib0 ib1) d0 mpImg 2 mpwd' :=
  ⟨mpw'DepsConsistent, mpw'Qconf cpu0 cpu1 rs0 rs1 ib0 ib1 d0⟩

end Weak
