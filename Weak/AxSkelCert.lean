/-
Weak: **VACUITY CERTIFICATES for the skeleton `AxSkel`** — two EXISTING end-to-end results
re-derived as INSTANCES of `AwpPackage` + `xv6RvwmoSafeAxCore` / `xv6RvwmoSafeAxK1` /
`xv6RvwmoSafeAxSkel`.

Rocq: `iris/AxSkelCert.v` @ xxvzwolszwmp.

## What this file proves (the Rocq header, in substance)

§0 `tierAWpdcOfClosed`: a plain `tierAWpd` lifts to the checkpointed `tierAWpdc` at any
step-closed pure checkpoint (`AxWpcAdeq.wpdWpdcInv`); `hart0IsStepClosed`: "if this is hart 0
then it runs on `cpu`" is step-closed at every agent.

§1 EPILOGUE (`epiSkelReload`): `AxAllHarts.epiReloadSound3AllHarts` — EXACT same statement —
through a package at the protocol instance `apEpi a b` (names `GName`, state `Unit`, interp
`epiObInterp`, init `epiInit3 a b`), policy `epiPol`, graph class the singleton `{GD}`, the
NON-TRIVIAL checkpoint "hart 0 is `cpu`" (`hartIs`, lifted by `tierAWpdcOfClosed`), `pkQ :=
True`.  Bonus conclusion: the checkpoint at hart 0's end state (`epiSkelChk`).  K1 is NOT
derivable here: the instance carries no ledger.

§2 MESSAGE PASSING (`mprSkelNoViolation`): `mprNoViolation` — EXACT same statement
`¬ gdviolationHart 2 AxTokLedgerMp.mpr` — through a package at the LEDGER instance `apMpr`
(`obStInterpL ocMpr 2 baseMpr`, names `GName × GName`, init `initMpr`), policy `mpPol`, graph
class `{mpr}`, checkpoint `hartIs cpu0` on every hart, `pkQ := ledgerPkQ ocMpr 2`; K1 via
`awpK1Ledger` and `xv6RvwmoSafeAxK1`.  `mprSkelShape`: the FULL skeleton `xv6RvwmoSafeAxSkel`
applied — every premise discharged except the OWED `K2Owed`/`K3Owed` pass-throughs.
Both certificates use ALL 8 harts (idle harts 2..7 via `wpdIdle`).

KEY FINDING (Rocq, recorded in AxSkel's header): the two instances need DIFFERENT protocol
instances and policies, so the package is parametric in both.

## Deviations from Rocq

1. O2 STAGE C: the package field `pk_T` is gone (AxSkel deviation 1), so `pk_T := T` / `Tf` are
   not supplied and `tierAWpdcOfClosed` has no `T`.  §1's premises are
   `AxAllHarts.epiReloadSound3AllHarts`'s Lean forms (its deviation 6): no `T`, no
   `Hnw_sd`/`Hnw_ld`/`Hntext`; `fetchImgOk GD 0 0`/`0 1`, `storeRowOk GD 0 0`, `sdWriteOk GD 0 0
   a`, `loadRowOk GD 0 1`, `ldspOwnOk GD 0 1 (0,0)`, length 2, `Hlob_gmo (0,0) (0,1)`; the
   conclusion of `epiSkelReload` is `graphValue GD (0, 1) = some sdData` (Rocq `(0,3)`).
2. SECTION `EpiCert`: Rocq's `Context` is replaced by explicit arguments; each declaration takes
   only the parameters/hypotheses it uses (Rocq's section closing does the same), in Rocq's
   context order.  `epiSkelReload`'s argument list is exactly `epiReloadSound3AllHarts`'s
   (checked by `epiSameStatement`).  Rocq's `Local Existing Instance epi_pol` ↦ `epiPol` passed
   explicitly.
3. INSTANCES: Rocq's `invGS_gen`/`axannotGS` arguments are explicit or local instances as
   AxSkel's package fields require; `tierAWpdcOfClosed` takes them as instance arguments.
4. `init_regstate` ↦ `zeroRegs` (as AxTokLedgerMp); `fin_to_nat c` ↦ `c.val`; `S (S i)` ↦
   `k + 2`.  `epiIdle'` takes Lean's `Hidle` (`2 ≤ i ∧ i < NCPU`).
5. Rocq's `Local Definition epi_same_statement` / `mpr_same_statement` (type ascriptions) are
   theorems whose type is `type_of%` of the original (zero proof content).
6. `Print Assumptions` lines not ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `tierA_wpdc_of_closed` `tierAWpdcOfClosed`, `hart0_is_step_closed`
`hart0IsStepClosed`, `AP_epi` `apEpi`, `epi_s00` `epiS00`, `epi_s0` `epiS0`, `epi_sNf` `epiSNf`,
`epi_nf` `epiNf`, `epi_idle'` `epiIdle'`, `epi_framed` `epiFramed`, `epi_s0_hart0` `epiS0Hart0`,
`epi_pkg` `epiPkg`, `epi_pkg_run` `epiPkgRun`, `epi_skel_reload` `epiSkelReload`,
`epi_skel_chk` `epiSkelChk`, `AP_mpr` `apMpr`, `mpr_sN'` `mprSN'`, `mpr_n'` `mprN'`,
`mpr_grow_idle` `mprGrowIdle`, `mpr_s0_hart` `mprS0Hart`, `mpr_wpd_plain` `mprWpdPlain`,
`mpr_pkg` `mprPkg`, `mpr_pkg_run` `mprPkgRun`, `mpr_pkg_k1` `mprPkgK1`,
`mpr_skel_no_violation` `mprSkelNoViolation`, `mpr_skel_shape` `mprSkelShape`,
`epi_same_statement` `epiSameStatement`, `mpr_same_statement` `mprSameStatement`.  None is in
the duplicated-name table.  Lean-only (file-qualified): `AxSkelCert.mprInitIdle`.

**Dropped:** nothing (Rocq 27 definitions/lemmas, Lean 27 + 1 Lean-only helper).
-/
import Weak.AxSkel
import Weak.AxTokLedgerMp

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 0. Lifting a plain `tierAWpd` to the checkpointed `tierAWpdc` -/

theorem tierAWpdcOfClosed {GF : BundledGFunctors.{0,0,0}} [InvGS_gen .hasNoLC GF]
    [AxannotGS GF] (GD : Gdexec) (pol : Axpol) (N st : Type)
    (interp : N → Gdexec → st → GSet Geid → IProp GF) (nm : N)
    (P : Agent → Athread → Prop) (i : Agent) (Hcl : stepClosed P i)
    (s : Athread) (HP : P i s) (Φ : Athread → IProp GF) :
    @tierAWpd GF .hasNoLC _ _ pol GD N st interp nm s .MaybeStuck i Φ ⊢
      @tierAWpdc GF .hasNoLC _ _ pol GD N st interp nm (fun j s => iprop(⌜P j s⌝)) s
        .MaybeStuck i Φ := by
  unfold tierAWpdc tierAWpd
  exact @wpdWpdcInv .hasNoLC GF _ (axGAc GD N st interp nm) pol P i Hcl .MaybeStuck s Φ HP

/-- "if this is hart 0 then it runs on `cpu`" — step-closed at every agent. -/
theorem hart0IsStepClosed (cpu : CPU) (i : Agent) :
    stepClosed (fun j s => j = 0 → hartIs cpu s) i := by
  obtain ⟨Hrd, Hpg, Hwi⟩ := hartIsStepClosed cpu i
  refine ⟨?_, ?_, ?_⟩
  · intro row s id K v Hst Hlen HP Hi
    exact Hrd row s id K v Hst Hlen (HP Hi)
  · intro row s l s' Hst HP Hi
    exact Hpg row s l s' Hst (HP Hi)
  · intro s s' Hst HP Hi
    exact Hwi s s' Hst (HP Hi)

/-! # 1. THE EPILOGUE INSTANCE (prot_inv protocol) -/

def apEpi (a b : Int) : Aprot epiGF := ⟨GName, Unit, epiObInterp, epiInit3 a b⟩

noncomputable def epiS00 (cpu : CPU) : Athread :=
  ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩

noncomputable def epiS0 (cpu : CPU) (s0_1 : Athread) (i : Agent) : Athread :=
  match i with
  | 0 => epiS00 cpu
  | 1 => s0_1
  | _ + 2 => epiS00 cpu

noncomputable def epiSNf (cpu : CPU) (sN sN1 : Athread) (i : Agent) : Athread :=
  match i with
  | 0 => sN
  | 1 => sN1
  | _ + 2 => epiS00 cpu

def epiNf (n n1 : Nat) (i : Agent) : Nat :=
  match i with
  | 0 => n
  | 1 => n1
  | _ + 2 => 0

theorem epiIdle' (GD : Gdexec) (Hidle : ∀ i, 2 ≤ i ∧ i < NCPU → AxOpsem.grow GD i = []) :
    ∀ i, i + 2 ∈ allHarts → AxOpsem.grow GD (i + 2) = [] := by
  intro i Hi
  exact Hidle _ ⟨Nat.le_add_left 2 i, (elemOfAllHarts _).1 Hi⟩

/-- The plain per-hart WPds (AxAllHarts' `Hwpf`, verbatim). -/
theorem epiFramed (GD : Gdexec) (cpu : CPU) (a b : Int)
    (Hidle : ∀ i, 2 ≤ i ∧ i < NCPU → AxOpsem.grow GD i = [])
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD 0).length = 2)
    (s0_1 : Athread)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) :
    @framedWpd epiGF epiPol GD GName Unit epiObInterp (epiInit3 a b) allHarts
      (epiS0 cpu s0_1) (epiPost2 GD) := by
  intro _ _ nm i Hi
  match i, Hi with
  | 0, _ =>
    exact AxAllHarts.epiHart0Framed GD cpu a b Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld
      Hlen nm
  | 1, _ => exact AxAllHarts.epiHart1Framed GD a b s0_1 Hwp1 nm
  | k + 2, Hi =>
    have Hle : (AxOpsem.grow GD (k + 2)).length ≤ 0 := by
      rw [epiIdle' GD Hidle k Hi]; exact .refl
    have h := @wpdIdle epiGF .hasNoLC _ epiPol GD GName Unit epiObInterp nm _ (k + 2) 0 Hle
      (.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone)
    have h' : ⊢ @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm
        (epiS0 cpu s0_1 (k + 2)) .MaybeStuck (k + 2)
        (fun s => iprop(⌜epiPost2 GD (k + 2) s⌝)) := by
      unfold tierAWpd at h
      unfold tierAWpd
      exact h.trans (@wpdMono .hasNoLC epiGF _ (axGA2 GD GName Unit epiObInterp nm) epiPol
        _ _ _ _ _ (fun _ => pure_intro (fun h => absurd h (Nat.succ_ne_zero _))))
    iintro _
    ihave H := h'
    iexact H

theorem epiS0Hart0 (cpu : CPU) (s0_1 : Athread) (i : Agent) :
    i = 0 → hartIs cpu (epiS0 cpu s0_1 i) := by
  intro h
  subst h
  exact hartIsAThread cpu _ _ _ _ 0

/-- THE PACKAGE. -/
noncomputable def epiPkg (GD : Gdexec) (cpu : CPU) (a b : Int)
    (Hdisj : slotsDisjoint a b)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1)
    (Hidle : ∀ i, 2 ≤ i ∧ i < NCPU → AxOpsem.grow GD i = [])
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD 0).length = 2)
    (Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1))
    (s0_1 : Athread)
    (Hk1 : s0_1.atK = 0)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) :
    AwpPackage (apEpi a b) epiPol where
  pkGraphs := fun GD' => GD' = GD
  pkS0 := epiS0 cpu s0_1
  pkPost := epiPost2
  pkCk := fun _ _ _ j s => iprop(⌜j = 0 → hartIs cpu s⌝)
  pkChkp := fun j s => j = 0 → hartIs cpu s
  pkQ := fun _ => True
  pkPolWf := epiAxpolWf
  pkAgents := by
    intro GD' hGD e He
    subst hGD
    rw [elemOfAllHarts]
    rcases Hharts e He with h | h <;> rw [h] <;> decide
  pkK0 := by
    intro i _
    match i with
    | 0 => rfl
    | 1 => exact Hk1
    | _ + 2 => rfl
  pkHchkp := fun _ _ _ _ _ => .rfl
  pkWp := by
    intro GD' hGD Hinv Hann nm i Hi
    subst hGD
    have hf := epiFramed GD' cpu a b Hidle Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hlen s0_1
      Hwp1
    unfold framedWpd at hf
    exact (hf nm i Hi).trans (wand_mono .rfl
      (tierAWpdcOfClosed GD' epiPol GName Unit epiObInterp nm
        (fun j s => j = 0 → hartIs cpu s) i (hart0IsStepClosed cpu i)
        (epiS0 cpu s0_1 i) (epiS0Hart0 cpu s0_1 i) _))
  pkAlloc := by
    intro GD' hGD
    subst hGD
    exact epiHobAlloc3All a b Hdisj GD'
  pkSPolGmo := by
    intro GD' Hc hGD
    subst hGD
    exact (AxAllHarts.epiPolGmo GD' Hc Hlob_gmo).1
  pkLobpGmo := by
    intro GD' Hc hGD
    subst hGD
    exact (AxAllHarts.epiPolGmo GD' Hc Hlob_gmo).2
  pkReadback := fun _ _ _ _ _ => pure_intro trivial

theorem epiPkgRun (GD : Gdexec) (cpu : CPU) (a b : Int)
    (Hdisj : slotsDisjoint a b)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1)
    (Hidle : ∀ i, 2 ≤ i ∧ i < NCPU → AxOpsem.grow GD i = [])
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD 0).length = 2)
    (Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1))
    (sN : Athread) (n : Nat)
    (Hrun : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (Hend : sN.atK = (AxOpsem.grow GD 0).length)
    (s0_1 sN1 : Athread) (n1 : Nat)
    (Hk1 : s0_1.atK = 0)
    (Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm 1) n1 s0_1 sN1)
    (Hend1 : sN1.atK = (AxOpsem.grow GD 1).length)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) :
    pkRun (epiPkg GD cpu a b Hdisj Hharts Hidle Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hlen
      Hlob_gmo s0_1 Hk1 Hwp1) GD (epiSNf cpu sN sN1) (epiNf n n1) := by
  refine ⟨?_, ?_⟩
  · intro Hann nm i Hi
    match i with
    | 0 => exact Hrun Hann nm
    | 1 => exact Hrun1 Hann nm
    | _ + 2 => exact nsteps_O _
  · intro i Hi
    match i, Hi with
    | 0, _ => exact Hend
    | 1, _ => exact Hend1
    | k + 2, Hi => rw [epiIdle' GD Hidle k Hi]; rfl

/-- `AxAllHarts.epiReloadSound3AllHarts`, EXACT statement, through the skeleton core. -/
theorem epiSkelReload (GD : Gdexec) (cpu : CPU) (a b : Int)
    (Hdisj : slotsDisjoint a b)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1)
    (Hidle : ∀ i, 2 ≤ i ∧ i < NCPU → AxOpsem.grow GD i = [])
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD 0).length = 2)
    (Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1))
    (sN : Athread) (n : Nat)
    (Hrun : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (Hend : sN.atK = (AxOpsem.grow GD 0).length)
    (s0_1 sN1 : Athread) (n1 : Nat)
    (Hk1 : s0_1.atK = 0)
    (Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm 1) n1 s0_1 sN1)
    (Hend1 : sN1.atK = (AxOpsem.grow GD 1).length)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) :
    graphValue GD (0, 1) = some sdData := by
  obtain ⟨Hall, -⟩ := xv6RvwmoSafeAxCore (apEpi a b) epiPol
    (epiPkg GD cpu a b Hdisj Hharts Hidle Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hlen
      Hlob_gmo s0_1 Hk1 Hwp1) GD Hcons rfl (epiSNf cpu sN sN1) (epiNf n n1)
    (epiPkgRun GD cpu a b Hdisj Hharts Hidle Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hlen
      Hlob_gmo sN n Hrun Hend s0_1 sN1 n1 Hk1 Hrun1 Hend1 Hwp1)
  have Hp := (Hall ⟨0, by decide⟩).1
  exact Hp rfl (by show sN.atK = 2; rw [Hend, Hlen])

/-- Bonus: the (non-trivial) checkpoint at hart 0's end state. -/
theorem epiSkelChk (GD : Gdexec) (cpu : CPU) (a b : Int)
    (Hdisj : slotsDisjoint a b)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1)
    (Hidle : ∀ i, 2 ≤ i ∧ i < NCPU → AxOpsem.grow GD i = [])
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD 0).length = 2)
    (Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1))
    (sN : Athread) (n : Nat)
    (Hrun : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (Hend : sN.atK = (AxOpsem.grow GD 0).length)
    (s0_1 sN1 : Athread) (n1 : Nat)
    (Hk1 : s0_1.atK = 0)
    (Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm 1) n1 s0_1 sN1)
    (Hend1 : sN1.atK = (AxOpsem.grow GD 1).length)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) :
    hartIs cpu sN := by
  obtain ⟨Hall, -⟩ := xv6RvwmoSafeAxCore (apEpi a b) epiPol
    (epiPkg GD cpu a b Hdisj Hharts Hidle Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hlen
      Hlob_gmo s0_1 Hk1 Hwp1) GD Hcons rfl (epiSNf cpu sN sN1) (epiNf n n1)
    (epiPkgRun GD cpu a b Hdisj Hharts Hidle Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hlen
      Hlob_gmo sN n Hrun Hend s0_1 sN1 n1 Hk1 Hrun1 Hend1 Hwp1)
  exact (Hall ⟨0, by decide⟩).2 rfl

/-! # 2. THE MESSAGE-PASSING INSTANCE (ledger protocol) -/

def apMpr : Aprot mprGF :=
  ⟨GName × GName, Unit, obStInterpL ocMpr 2 baseMpr, initMpr⟩

def mprSN' (i : Agent) : Athread :=
  match i with
  | 0 => mprSN 0
  | 1 => mprSN 1
  | _ + 2 => mprS0 i

def mprN' (i : Agent) : Nat :=
  match i with
  | 0 => mprN 0
  | 1 => mprN 1
  | _ + 2 => 0

theorem mprGrowIdle (i : Agent) : AxOpsem.grow AxTokLedgerMp.mpr (i + 2) = [] := rfl

theorem mprS0Hart (i : Agent) : hartIs cpu0 (mprS0 i) := by
  match i with
  | 0 => exact hartIsAThread cpu0 _ _ _ _ 0
  | _ + 1 => exact hartIsAThread cpu0 _ _ _ _ 0

/-- The plain per-hart WPds at the ledger instance. -/
theorem mprWpdPlain (Hinv : InvGS_gen .hasNoLC mprGF) (Hann : AxannotGS mprGF)
    (nm : GName × GName) (i : Agent) :
    ⊢ initMpr nm i -∗
      @tierAWpd mprGF .hasNoLC Hinv Hann mpPol AxTokLedgerMp.mpr (GName × GName) Unit
        (obStInterpL ocMpr 2 baseMpr) nm (mprS0 i) .MaybeStuck i (fun _ => iprop(⌜True⌝)) := by
  obtain ⟨γ1, γ2⟩ := nm
  match i with
  | 0 =>
    rw [AxTokLedgerMp.mprS0At0]
    iintro H
    icases (AxTokLedgerMp.initMpr0 _).1 $$ H with ⟨%Heq, Ht⟩
    simp only at Heq
    subst Heq
    iapply (wpdH0_0 (hlc := .hasNoLC) (GF := mprGF) γ1 cpu0) $$ Ht %zeroRegs
  | 1 =>
    rw [AxTokLedgerMp.mprS0At1]
    iintro H
    icases (AxTokLedgerMp.initMpr1 _).1 $$ H with ⟨%Heq, -⟩
    simp only at Heq
    subst Heq
    iapply (wpdH1_0 (hlc := .hasNoLC) (GF := mprGF) γ1 cpu0) $$ %zeroRegs
  | k + 2 =>
    iintro -
    have Hle : (AxOpsem.grow AxTokLedgerMp.mpr (k + 2)).length ≤ 0 := by
      rw [mprGrowIdle]; exact .refl
    have h := @wpdIdle mprGF .hasNoLC Hinv mpPol AxTokLedgerMp.mpr (GName × GName) Unit
      (obStInterpL ocMpr 2 baseMpr) (γ1, γ2) Hann (k + 2) 0 Hle (hp cpu0 h1M0 zeroRegs)
    have h' : ⊢ @tierAWpd mprGF .hasNoLC Hinv Hann mpPol AxTokLedgerMp.mpr (GName × GName) Unit
        (obStInterpL ocMpr 2 baseMpr) (γ1, γ2) (mprS0 (k + 2)) .MaybeStuck (k + 2)
        (fun _ => iprop(⌜True⌝)) := h
    ihave H := h'
    iexact H

/-- Lean-only: idle harts' initial resources at a diagonal name pair. -/
theorem AxSkelCert.mprInitIdle (γ : GName) :
    ⊢@{IProp mprGF} [∗list] i ∈ List.range' 2 6, initMpr (γ, γ) i := by
  refine BigSepL.bigSepL_intro fun k x hx => ?_
  have hm := List.mem_of_getElem? hx
  rw [List.mem_range'_1] at hm
  obtain ⟨j, rfl⟩ : ∃ j, x = j + 2 := ⟨x - 2, (Nat.sub_add_cancel hm.1).symm⟩
  show ⊢ iprop(⌜(γ, γ).1 = (γ, γ).2⌝ ∗ True)
  istart
  isplitr
  · ipureintro
    rfl
  · itrivial

/-- THE PACKAGE. -/
def mprPkg : AwpPackage apMpr mpPol where
  pkGraphs := fun GD => GD = AxTokLedgerMp.mpr
  pkS0 := mprS0
  pkPost := fun _ _ _ => True
  pkCk := fun _ _ _ _ s => iprop(⌜hartIs cpu0 s⌝)
  pkChkp := fun _ s => hartIs cpu0 s
  pkQ := ledgerPkQ ocMpr 2
  pkPolWf := by
    intro GD i k e h
    exact absurd h notElemOfEmpty
  pkAgents := by
    intro GD hGD e He
    subst hGD
    rw [mprGmo] at He
    rw [elemOfAllHarts]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at He
    rcases He with rfl | rfl | rfl | rfl <;> decide
  pkK0 := by
    intro i _
    cases i <;> rfl
  pkHchkp := fun _ _ _ _ _ => .rfl
  pkWp := by
    intro GD hGD Hinv Hann nm i _
    subst hGD
    exact (mprWpdPlain Hinv Hann nm i).trans (wand_mono .rfl
      (tierAWpdcOfClosed AxTokLedgerMp.mpr mpPol (GName × GName) Unit
        (obStInterpL ocMpr 2 baseMpr) nm (fun _ s => hartIs cpu0 s) i
        (hartIsStepClosed cpu0 i) (mprS0 i) (mprS0Hart i) _))
  pkAlloc := by
    intro GD hGD
    subst hGD
    show ⊢ |==> ∃ (nm : GName × GName) (σ0 : Unit),
      obStInterpL ocMpr 2 baseMpr nm AxTokLedgerMp.mpr σ0 ∅ ∗ [∗list] i ∈ allHarts, initMpr nm i
    istart
    have HA := ledgerAlloc (GF := mprGF) lMpr0
    unfold lMpr0 at HA
    imod HA with ⟨%γ, Ha, Hf⟩
    have Hnone : get? ({[xa := Holder.held 0]} : Ledger) ya = none := by decide +kernel
    icases (BigSepM.bigSepM_insert (Φ := fun a h => tokFrag (GF := mprGF) γ a h)
      (x := Holder.held 0) Hnone).1 $$ Hf with ⟨Hy, Hf⟩
    ihave Hx := BigSepM.bigSepM_singleton.1 $$ Hf
    imodintro
    iexists (γ, γ), ()
    isplitl [Ha]
    · unfold obStInterpL
      rw [AxTokLedgerMp.baseMprEmpty]
      isplitr
      · itrivial
      · iapply ledgerInvInit ocMpr 2 γ AxTokLedgerMp.mpr
        iexact Ha
    · rw [show allHarts = [0, 1] ++ List.range' 2 6 from rfl]
      iapply BigSepL.bigSepL_append.2
      isplitl [Hx Hy]
      · iapply (AxTokLedgerMp.bigSepLPair 0 1 _).2
        isplitl [Hx Hy]
        · iapply (AxTokLedgerMp.initMpr0 _).2
          unfold tokAt
          isplitr
          · ipureintro
            rfl
          · isplitl [Hx]
            · iexact Hx
            · iexact Hy
        · iapply (AxTokLedgerMp.initMpr1 _).2
          isplitr
          · ipureintro
            rfl
          · itrivial
      · ihave Hid := AxSkelCert.mprInitIdle γ
        iexact Hid
  pkSPolGmo := by
    intro GD _ hGD e e' He'
    subst hGD
    exact gmoPrefixGmoLt' _ mprWf e e' ((elemOfListToSet (S := GSet Geid)).1 He')
  pkLobpGmo := by
    intro GD _ _ e e' He'
    exact absurd He' notElemOfEmpty
  pkReadback := fun GD Hc _ nm σ => ledgerReadback ocMpr 2 baseMpr GD Hc nm σ

theorem mprPkgRun : pkRun mprPkg AxTokLedgerMp.mpr mprSN' mprN' := by
  refine ⟨?_, ?_⟩
  · intro _ _ i _
    match i with
    | 0 => exact h0Run cpu0 zeroRegs
    | 1 => exact h1Run cpu0 zeroRegs
    | _ + 2 => exact nsteps_O _
  · intro i _
    match i with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl

theorem mprPkgK1 : awpK1 2 mprPkg :=
  awpK1Ledger 2 mprPkg ocMpr (fun _ HQ => HQ) (fun GD _ hGD => by
    subst hGD
    exact mprPlainWritesOC)

/-- `AxTokLedgerMp.mprNoViolation`, EXACT statement, through the skeleton's K1 route. -/
theorem mprSkelNoViolation : ¬ gdviolationHart 2 AxTokLedgerMp.mpr :=
  xv6RvwmoSafeAxK1 apMpr mpPol mprPkg 2 mprPkgK1 AxTokLedgerMp.mpr AxTokLedgerMp.mprCat rfl
    mprSN' mprN' mprPkgRun

/-- The FULL skeleton at `mpr`: every premise discharged except the OWED K2/K3 pass-throughs. -/
theorem mprSkelShape (eraBoot : Gdexec → Gdexec → Prop) (crashInv : Gdexec → Prop)
    (HK2 : ∀ GD, rvwmoCatConsistent GD → mprPkg.pkGraphs GD → K2Owed mprPkg GD)
    (HK3 : K3Owed mprPkg eraBoot crashInv) :
    ¬ gdviolationHart 2 AxTokLedgerMp.mpr ∧
    (∀ c : CPU, hartIs cpu0 (mprSN' c.val)) ∧
    ledgerPkQ ocMpr 2 AxTokLedgerMp.mpr ∧
    K2Owed mprPkg AxTokLedgerMp.mpr ∧ K3Owed mprPkg eraBoot crashInv := by
  obtain ⟨Hv, Hall, HQ, H2, H3⟩ := xv6RvwmoSafeAxSkel apMpr mpPol mprPkg 2 mprPkgK1 eraBoot
    crashInv HK2 HK3 AxTokLedgerMp.mpr AxTokLedgerMp.mprCat rfl mprSN' mprN' mprPkgRun
  exact ⟨Hv, fun c => (Hall c).2, HQ, H2, H3⟩

/-! MECHANICAL STATEMENT MATCH: each certificate's closed type IS the original theorem's type. -/

theorem epiSameStatement : type_of% @epiReloadSound3AllHarts := @epiSkelReload

theorem mprSameStatement : type_of% mprNoViolation := mprSkelNoViolation

end Weak
