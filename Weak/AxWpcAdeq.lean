/-
Weak: **`wpcAdequacy` for the LB/AxSL stack** — the CHECKPOINTED `WPd` and its Tier-A adequacy.

Rocq: `iris/AxWpcAdeq.v` @ xxvzwolszwmp.

## The Rocq header, in substance

"wpc" is NOT a Perennial crash WP.  `AxWp.wpc` (`AxWp2` §6, `wpPreChk`/`wpc`) is the port of
AxSL's `low/weakestpre_chk.v`: the CHECKPOINTED WP, which at every non-terminated state
additionally carries `postLifting (chk i) i s` (a per-hart state predicate, trivial off the
instruction boundary by `chkMidInstr`) in an `∧` with the step obligation.  Its adequacy (AxSL
`adequacy_chk.v`) says: at the end state of ANY (partial) execution graph the checkpoint holds.
Phase-1 composition and phase 2 exist for the DEMONIC-READ `WPd` (`AxWpD`), not for `wp`
(`tierAAdequacyAnnGmo` / `tierAAdequacyAnnRun`); this file transfers them.

§1 `wpdc` — the checkpointed `WPd`: `wpPreChk` with `wp`'s step replaced by `wpdPreStepDef`
(reads pinned to the graph value, clause (d) = post at row end).  The checkpoint `ck` is an
explicit parameter (not the `AxirisGChk` class: Tier A builds its `AxirisG` instance INSIDE the
adequacy, per ghost name, so the checkpoint is a family over that instance).
§2 `wpdcWpd` (forget checkpoints), `wpdWpdc` (trivial checkpoint), and the KEY `wpdcWpdChk`: a
`wpdc` IS a `WPd` whose row-end postcondition is `psiCk ck i Φ` — clause (d) is fed from the
`∧`'s checkpoint half; so the EXISTING Tier-A adequacy delivers the checkpoint.
§2b `stepClosed`/`wpdWpdcInv`: a pure per-hart predicate closed under the three WPd step shapes
lifts any `WPd` to a `wpdc`; `hartIs` (the hart's cpu identity) is one (`hartIsStepClosed`).
HONESTY (Rocq): such a pure checkpoint is also derivable from the run by induction, so §5
certifies that the checkpointed PREMISE is dischargeable on a real client, not that the
checkpoint carries information the run does not.
§3 `wpdcWpc`: under `AxirisGChk` with `ck = chk`, `wpdc` entails `AxWp.wpc`.
§3b `chkBd`/`axirisGChkBd`/`chkBdPure`/`wpdcWpcBd`: the checkpoint CLASS built from a pure
BOUNDARY predicate (trivial mid-instruction).
§4 `wpcAdequacyAnnRun` / `wpcAdequacyAnnGmo`: Tier-A adequacy with checkpointed per-hart
premises; conclusion `post i (sN i) ∧ chkp i (sN i)`.  `wpcAdequacyAnnGmoTriv`: at
`ck := True` it is exactly `tierAAdequacyAnnGmo`.
§5 `epiReloadSoundChk`: `AxEpiAdeq.epiReloadSound` re-derived through §4 with the non-trivial
checkpoint `hartIs cpu`.

SCOPE (Rocq): the checkpoint is delivered at the END state of `GD` (every hart consumed its
row); `GD` is arbitrary, so an intermediate boundary is the instance at a prefix graph (not
constructed here).  No crash/era content.

## Deviations from Rocq

1. NAMES / SHAPES (as `AxWpD`): camelCase (map below); `Psi_ck` ↦ `psiCk` (as `AxAdequacyChk`'s
   `psiChk`); `A -∗ B` premises ↦ `⊢ A -∗ B`; `WPd s @ st; i {{ Φ }}` ↦ `wpd st i s Φ`;
   `WPc …` ↦ `wpc st i s Φ`; `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for an arbitrary `hlc`
   in §1–§3 and in `tierAWpdc` (as `AxWpD`/`tierAWpd`); §4's `Hwp`/`ck`/`Hchkp` at `.hasNoLC`.
2. SEALS: `wpdc` is a plain `fixpoint` (`wpdc_def`/`wpdc_aux`/`wpdc_eq` have no counterpart, as
   `AxWpD` deviation 3).  `wpdcPreContractive` is a global instance.  Lean-only
   `AxWpcAdeq.wpdcUnfoldStep` (the unfolding at a hart state; harts never terminate).
3. O2 STAGE C / OWNER Q8 (`AxOpsem`, `AxWpD` deviation 5): `AxOpsem.astepProg` has no `T`/`img`,
   so `stepClosed`'s program clause quantifies over `row` only (Rocq `row T img`); the step
   case's clause (b) carries the image pin `⌜WeakAxRealize.fetchPin …⌝`, which every proof here
   threads through unchanged.  §4: Rocq's section `T` is gone (`axGA2`/`tierAAstep`/`tierAWpd`
   have none, `AxTierA2` deviation 2).
4. INSTANCES: Rocq's `Local Instance AxGAc` ↦ the reducible def `axGAc GD N obSt0 obStInterp0 nm`
   named in `tierAWpdc`; Rocq's section `GD T N ob_st0 ob_st_interp0 init` (and `nm` for
   `tierA_wpdc*`) ↦ explicit arguments in that order (as `tierAWpd`).  Rocq's
   `Local Existing Instance axirisGChk_bd` ↦ `axirisGChkBd I` passed explicitly (`chkBdPure`,
   `wpdcWpcBd`).  §3b's `chkBd`/`chkBdMidInstr`/`axirisGChkBd`/`chkBdPure` need no `InvGS`/`AxirisG`/`Axpol`
   (Rocq's section context, unused) and take none.  `hartsPremiseMono` takes no `InvGS` (unused
   in Rocq).  The `ck`/`Hchkp`/`Hwp` families bind the instances as `∀ [InvGS_gen .hasNoLC GF]
   [AxannotGS GF]` (as `tierAAdequacyAnnGmo`'s `Hwp`).  §4 is at
   `GF : BundledGFunctors.{0,0,0}` (as `AxTierA3`).
5. §5 (as `AxEpiAdeq.epiReloadSound`, its deviation 1): positions `fetchImgOk GD 0 0`,
   `storeRowOk GD 0 0`, `sdWriteOk GD 0 0 a`, `fetchImgOk GD 0 1`, `loadRowOk GD 0 1`,
   `ldspOwnOk GD 0 1 (0,0)`, length 2, `gmoLt (0,0) (0,1)`, conclusion `graphValue GD (0, 1)`
   (Rocq `… 0 0`, `0 1`, `0 1`, `0 2`, `0 3`, `0 3 (0,1)`, 4, `(0,1) (0,3)`, `(0,3)`);
   `T`, `Hnw_sd`, `Hnw_ld`, `Hntext` DROPPED; Rocq's `Local Existing Instance epi_pol` ↦
   `epiPol` passed explicitly; `Hrun` as `epiReloadSound`'s (deviation 7 there).

**Rocq → Lean name map.**  §1 `wpdc_pre` `wpdcPre`, `wpdc_pre_contractive`
`wpdcPreContractive`, `wpdc(_def)` `wpdc`, `wpdc_unfold` `wpdcUnfold`, `Psi_ck` `psiCk`.
§2 `wpdc_wpd` `wpdcWpd`, `wpd_wpdc` `wpdWpdc`, `post_lifting_Psi_ck` `postLiftingPsiCk`,
`wpdc_wpd_chk` `wpdcWpdChk`, `Psi_ck_pure` `psiCkPure`.  §2b `step_closed` `stepClosed`,
`wpd_wpdc_inv` `wpdWpdcInv`, `hart_is` `hartIs`, `hart_is_AThread` `hartIsAThread`,
`pstep_prog_hart_is` `pstepProgHartIs`, `pstep_wire_hart_is` `pstepWireHartIs`,
`hart_is_step_closed` `hartIsStepClosed`.  §3 `wpdc_wpc` `wpdcWpc`.  §3b `chk_bd` `chkBd`,
`chk_bd_mid_instr` `chkBdMidInstr`, `axirisGChk_bd` `axirisGChkBd`, `chk_bd_pure` `chkBdPure`,
`wpdc_wpc_bd` `wpdcWpcBd`.  §4 `AxGAc` `axGAc`, `tierA_wpdc` `tierAWpdc`, `tierA_wpdc_wpd`
`tierAWpdcWpd`, `tierA_wpdc_wpd_chk` `tierAWpdcWpdChk`, `harts_premise_mono`
`hartsPremiseMono`, `wpc_adequacy_ann_run` `wpcAdequacyAnnRun`, `wpc_adequacy_ann_gmo`
`wpcAdequacyAnnGmo`, `wpc_adequacy_ann_gmo_triv` `wpcAdequacyAnnGmoTriv`.  §5
`epi_reload_sound_chk` `epiReloadSoundChk`.  None is in the duplicated-name table.  Lean-only
(file-qualified): `AxWpcAdeq.wpdcUnfoldStep`.

**Dropped:** nothing (Rocq 35 definitions/lemmas/instances incl. `wpdc_def`/`wpdc_aux`/
`wpdc_eq`; Lean 32 — `wpdc_def` and `wpdc` are one `wpdc` — + 1 Lean-only helper).  **Not ported:** `wpdc_aux`/`wpdc_eq` (seal, deviation 2) and the
`Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxTierA4
import Weak.AxAdequacyChk
import Weak.AxEpiAdeq

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. `wpdc` — the checkpointed `WPd` -/

section wpdcDef
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (ck : Agent → Athread → IProp GF)

/-- Rocq `wpdc_pre`: `wpPreChk` with the `WPd` step case. -/
def wpdcPre (st : Stuckness) (i : Agent) (wpdc : Athread → (Athread → IProp GF) → IProp GF) :
    Athread → (Athread → IProp GF) → IProp GF :=
  fun s Φ =>
    if isTerminated s then postLifting Φ i s
    else iprop(postLifting (ck i) i s ∧
      (progressObl st i s ∧ wpdMPreStepDef rvwmoCatConsistent i wpdc s Φ))

instance wpdcPreContractive (st : Stuckness) (i : Agent) :
    OFE.Contractive (wpdcPre (GF := GF) ck st i) where
  distLater_dist {n wpd wpd'} Hwpd := by
    intro s Φ
    unfold wpdcPre
    simp only [isTerminated, Bool.false_eq_true, ↓reduceIte]
    refine BI.and_ne.ne .rfl (BI.and_ne.ne .rfl ?_)
    exact AxWpD.wpdMPreStepDefDist rvwmoCatConsistent i wpd wpd' s Φ n
      (fun m hm s' => Hwpd m hm s' Φ)

/-- Rocq `wpdc`: the fixpoint of `wpdcPre`. -/
def wpdc (st : Stuckness) (i : Agent) : Athread → (Athread → IProp GF) → IProp GF :=
  fixpoint (wpdcPre (GF := GF) ck st i)

theorem wpdcUnfold (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpdc ck st i s Φ ⊣⊢ wpdcPre ck st i (wpdc ck st i) s Φ :=
  BI.equiv_iff.1 <| OFE.eq_dist_2 <|
    fun _n => (fixpoint_unfold (f := (wpdcPre (GF := GF) ck st i).toContractiveHom)).dist s Φ

/-- Lean-only: the unfolding at a hart state (harts never terminate). -/
theorem AxWpcAdeq.wpdcUnfoldStep (st : Stuckness) (i : Agent) (s : Athread)
    (Φ : Athread → IProp GF) :
    wpdc ck st i s Φ ⊣⊢ iprop(postLifting (ck i) i s ∧
      (progressObl st i s ∧ wpdMPreStepDef rvwmoCatConsistent i (wpdc ck st i) s Φ)) := by
  refine (wpdcUnfold ck st i s Φ).trans ?_
  unfold wpdcPre
  simp only [isTerminated, Bool.false_eq_true, ↓reduceIte]
  exact .rfl

end wpdcDef

/-- `psiChk`'s twin at an explicit checkpoint family. -/
def psiCk {GF : BundledGFunctors} (ck : Agent → Athread → IProp GF) (i : Agent)
    (Φ : Athread → IProp GF) : Athread → IProp GF :=
  fun s => if isTerminated s then Φ s else ck i s

/-! # 2. Structural lemmas -/

section wpdcLaws
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (ck : Agent → Athread → IProp GF)

/-- Forgetting the checkpoints (twin of `AxWp.wpcWp`). -/
theorem wpdcWpd (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpdc ck st i s Φ ⊢ wpd st i s Φ := by
  have h : ⊢ ∀ s (Φ : Athread → IProp GF),
      wpdc ck st i s Φ -∗ wpdM rvwmoCatConsistent st i s Φ := by
    iloeb as IH
    iintro %s %Φ H
    rw [(AxWpcAdeq.wpdcUnfoldStep ck st i s Φ).to_eq,
      (AxWpD.wpdMUnfoldStep rvwmoCatConsistent st i s Φ).to_eq]
    isplit
    · icases H with ⟨-, H, -⟩
      iexact H
    · icases H with ⟨-, -, H⟩
      iapply wpdMPreStepDefMono $$ [] H
      isplit
      · inext
        iintro %s' H'
        iapply IH $$ %s' %Φ H'
      · iintro %k Hk
        imodintro
        iexact Hk
  iintro H
  iapply h $$ %s %Φ H

/-- A trivial checkpoint makes every `WPd` a `wpdc` (twin of `AxWp.wpWpc`). -/
theorem wpdWpdc (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF)
    (Hck : ∀ s', iprop(True) ⊢ ck i s') :
    wpd st i s Φ ⊢ wpdc ck st i s Φ := by
  have h : ⊢ ∀ s (Φ : Athread → IProp GF),
      wpdM rvwmoCatConsistent st i s Φ -∗ wpdc ck st i s Φ := by
    iloeb as IH
    iintro %s %Φ H
    rw [(AxWpcAdeq.wpdcUnfoldStep ck st i s Φ).to_eq,
      (AxWpD.wpdMUnfoldStep rvwmoCatConsistent st i s Φ).to_eq]
    isplit
    · iapply (postLiftingTrue (ck i) i s (Hck s))
    isplit
    · icases H with ⟨H, -⟩
      iexact H
    · icases H with ⟨-, H⟩
      iapply wpdMPreStepDefMono $$ [] H
      isplit
      · inext
        iintro %s' H'
        iapply IH $$ %s' %Φ H'
      · iintro %k Hk
        imodintro
        iexact Hk
  iintro H
  iapply h $$ %s %Φ H

theorem postLiftingPsiCk (i : Agent) (Φ : Athread → IProp GF) (s : Athread) :
    (if isTerminated s then postLifting Φ i s else postLifting (ck i) i s)
      = postLifting (psiCk ck i Φ) i s := by
  simp only [isTerminated, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- THE KEY LEMMA.  A `wpdc` is a `WPd` whose row-end postcondition is the checkpoint (or `Φ`
at a terminated state): clause (d) is discharged by the `∧`'s CHECKPOINT half, clauses (a)–(c)
by the step half (continuations by Löb). -/
theorem wpdcWpdChk (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpdc ck st i s Φ ⊢ wpd st i s (psiCk ck i Φ) := by
  have hpl : ∀ s, postLifting (ck i) i s = postLifting (psiCk ck i Φ) i s := fun s => by
    have h := postLiftingPsiCk ck i Φ s
    simp only [isTerminated, Bool.false_eq_true, ↓reduceIte] at h
    exact h
  have h : ⊢ ∀ s, wpdc ck st i s Φ -∗ wpdM rvwmoCatConsistent st i s (psiCk ck i Φ) := by
    iloeb as IH
    iintro %s H
    rw [(AxWpcAdeq.wpdcUnfoldStep ck st i s Φ).to_eq,
      (AxWpD.wpdMUnfoldStep rvwmoCatConsistent st i s (psiCk ck i Φ)).to_eq]
    isplit
    · icases H with ⟨-, H, -⟩
      iexact H
    unfold wpdMPreStepDef
    iintro %GD %ls Hpre
    isplit
    · icases H with ⟨-, -, H⟩
      ihave H := H $$ %GD %ls Hpre
      icases H with ⟨H, -⟩
      iintro %id %K %Hstep
      ihave H := H $$ %id %K %Hstep
      by_cases hadv : aidentAdvRd id = 1
      · simp only [hadv, ↓reduceIte]
        iintro %v %Hv %Hlen
        ihave H := H $$ %v %Hv %Hlen
        iapply wpEvStepMono $$ [] H
        inext
        iintro %_ Hw
        iapply IH $$ %(K v) Hw
      · simp only [hadv, ↓reduceIte]
        iintro %v %Hv %Hlen
        ihave H := H $$ %v %Hv %Hlen
        iapply wpSkipStepMono $$ [] H
        inext
        iintro Hw
        iapply IH $$ %(K v) Hw
    isplit
    · icases H with ⟨-, -, H⟩
      ihave H := H $$ %GD %ls Hpre
      icases H with ⟨-, H, -⟩
      iintro %l %s' %Hstep %Hpin
      ihave H := H $$ %l %s' %Hstep %Hpin
      cases wlWdata l with
      | some data =>
        iapply wpEvStepMono $$ [] H
        inext
        iintro %_ Hw
        iapply IH $$ %s' Hw
      | none =>
        iapply wpSkipStepMono $$ [] H
        inext
        iintro Hw
        iapply IH $$ %s' Hw
    isplit
    · icases H with ⟨-, -, H⟩
      ihave H := H $$ %GD %ls Hpre
      icases H with ⟨-, -, H, -⟩
      iintro %s' %Hstep
      ihave H := H $$ %s' %Hstep
      iapply wpSkipStepMono $$ [] H
      inext
      iintro Hw
      iapply IH $$ %s' Hw
    · icases H with ⟨H, -⟩
      iintro %_
      rw [← hpl s]
      iexact H
  iintro H
  iapply h $$ %s H

/-- `psiCk` at a pure postcondition is pure, given a pure reading of the checkpoint (twin of
`AxAdequacyChk.psiChkPure`). -/
theorem psiCkPure {GF : BundledGFunctors} (ck : Agent → Athread → IProp GF) (chkp : Agent → Athread → Prop) (Hchkp : ∀ i s, ck i s ⊢ iprop(⌜chkp i s⌝))
    (i : Agent) (Φp : Athread → Prop) (s : Athread) :
    psiCk ck i (fun v => iprop(⌜Φp v⌝)) s ⊢
      iprop(⌜if isTerminated s then Φp s else chkp i s⌝) := by
  unfold psiCk
  simp only [isTerminated, Bool.false_eq_true, ↓reduceIte]
  exact Hchkp i s

end wpdcLaws

/-! # 2b. Discharging the checkpoint premise: step-closed pure checkpoints -/

/-- A pure per-hart predicate closed under the three step shapes a `WPd` quantifies over (read
continuation, program step, PLIC wire — rows arbitrary). -/
def stepClosed (P : Agent → Athread → Prop) (i : Agent) : Prop :=
  (∀ (row : List Lbl) (s : Athread) (id : AidentT) (K : List (BitVec 8) → Athread)
      (v : List (BitVec 8)),
      areadStep row s id K → v.length = aidentN id → P i s → P i (K v)) ∧
  (∀ (row : List Lbl) (s : Athread) (l : Wlabel) (s' : Athread),
      AxOpsem.astepProg row s l s' → P i s → P i s') ∧
  (∀ s s', awire s s' → P i s → P i s')

section wpdcInv
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdWpdcInv (P : Agent → Athread → Prop) (i : Agent) (Hcl : stepClosed P i)
    (st : Stuckness) (s : Athread) (Φ : Athread → IProp GF) (HP : P i s) :
    wpd st i s Φ ⊢ wpdc (fun j s => iprop(⌜P j s⌝)) st i s Φ := by
  obtain ⟨Hrd, Hpg, Hwi⟩ := Hcl
  have h : ⊢ ∀ s, iprop(⌜P i s⌝) -∗ wpdM rvwmoCatConsistent st i s Φ -∗
      wpdc (fun j s => iprop(⌜P j s⌝)) st i s Φ := by
    iloeb as IH
    iintro %s %HP H
    rw [(AxWpcAdeq.wpdcUnfoldStep (fun j s => iprop(⌜P j s⌝)) st i s Φ).to_eq,
      (AxWpD.wpdMUnfoldStep rvwmoCatConsistent st i s Φ).to_eq]
    isplit
    · iapply (postLiftingTrue (fun s => iprop(⌜P i s⌝)) i s (pure_intro HP))
    isplit
    · icases H with ⟨H, -⟩
      iexact H
    icases H with ⟨-, H⟩
    unfold wpdMPreStepDef
    iintro %GD %ls Hpre
    ihave H := H $$ %GD %ls Hpre
    isplit
    · icases H with ⟨H, -⟩
      iintro %id %K %Hstep
      ihave H := H $$ %id %K %Hstep
      by_cases hadv : aidentAdvRd id = 1
      · simp only [hadv, ↓reduceIte]
        iintro %v %Hv %Hlen
        ihave H := H $$ %v %Hv %Hlen
        iapply wpEvStepMono $$ [] H
        inext
        iintro %_ Hw
        iapply IH $$ %(K v) %(Hrd _ _ _ _ _ Hstep Hlen HP) Hw
      · simp only [hadv, ↓reduceIte]
        iintro %v %Hv %Hlen
        ihave H := H $$ %v %Hv %Hlen
        iapply wpSkipStepMono $$ [] H
        inext
        iintro Hw
        iapply IH $$ %(K v) %(Hrd _ _ _ _ _ Hstep Hlen HP) Hw
    isplit
    · icases H with ⟨-, H, -⟩
      iintro %l %s' %Hstep %Hpin
      ihave H := H $$ %l %s' %Hstep %Hpin
      cases wlWdata l with
      | some data =>
        iapply wpEvStepMono $$ [] H
        inext
        iintro %_ Hw
        iapply IH $$ %s' %(Hpg _ _ _ _ Hstep HP) Hw
      | none =>
        iapply wpSkipStepMono $$ [] H
        inext
        iintro Hw
        iapply IH $$ %s' %(Hpg _ _ _ _ Hstep HP) Hw
    isplit
    · icases H with ⟨-, -, H, -⟩
      iintro %s' %Hstep
      ihave H := H $$ %s' %Hstep
      iapply wpSkipStepMono $$ [] H
      inext
      iintro Hw
      iapply IH $$ %s' %(Hwi _ _ Hstep HP) Hw
    · icases H with ⟨-, -, -, H⟩
      iexact H
  iintro H
  iapply h $$ %s %HP H

end wpdcInv

/-- The hart's IDENTITY: the simplest non-trivial checkpoint, used by §5. -/
def hartIs (cpu : CPU) (s : Athread) : Prop :=
  ∃ m rs fn ib, s.atP = .PHart cpu m rs fn ib

theorem hartIsAThread (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (k : Nat) :
    hartIs cpu ⟨.PHart cpu m rs fn ib, k⟩ :=
  ⟨m, rs, fn, ib, rfl⟩

theorem pstepProgHartIs (cpu : CPU) (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6)
    (d' : Efab) :
    pstepProg p d l p' d' → (∃ m rs fn ib, p = .PHart cpu m rs fn ib) →
    ∃ m rs fn ib, p' = .PHart cpu m rs fn ib := by
  rintro Hst ⟨m, rs, fn, ib, rfl⟩
  cases p' with
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, -⟩ := Hst
    exact ⟨m', rs', fn', ib', rfl⟩
  | PDisk _ => exact (Hst : False).elim

theorem pstepWireHartIs (cpu : CPU) (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6)
    (d' : Efab) :
    pstepWire p d l p' d' → (∃ m rs fn ib, p = .PHart cpu m rs fn ib) →
    ∃ m rs fn ib, p' = .PHart cpu m rs fn ib := by
  rintro Hst ⟨m, rs, fn, ib, rfl⟩
  cases p' with
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, -⟩ := Hst
    exact ⟨m', rs', fn', ib', rfl⟩
  | PDisk _ => exact (Hst : False).elim

theorem hartIsStepClosed (cpu : CPU) (i : Agent) : stepClosed (fun _ s => hartIs cpu s) i := by
  refine ⟨?_, ?_, ?_⟩
  · rintro row s id K v ⟨lb, -, -, -, Hk⟩ Hlen Hs
    obtain ⟨l, d, d', -, -, Hst, -⟩ := Hk v Hlen
    exact pstepProgHartIs cpu _ _ _ _ _ Hst Hs
  · intro row s l s' Hst Hs
    obtain ⟨d, d', Hp⟩ := astepProgPstep row s l s' Hst
    exact pstepProgHartIs cpu _ _ _ _ _ Hp Hs
  · rintro s s' ⟨-, d, d', Hw⟩ Hs
    exact pstepWireHartIs cpu _ _ _ _ _ Hw Hs

/-! # 3. `wpdc` entails the repo's `wpc` at `ck = chk` -/

section wpdcWpcSec
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
  [AxirisGChk GF]

/-- `AxWpD.wpdWp`'s script plus the checkpoint conjunct, copied verbatim: `wpdc` is a
strengthening of `wpc`. -/
theorem wpdcWpc (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpdc AxirisGChk.chk st i s Φ ⊢ wpc st i s Φ := by
  have h : ⊢ ∀ s (Φ : Athread → IProp GF), wpdc AxirisGChk.chk st i s Φ -∗ wpc st i s Φ := by
    iloeb as IH
    iintro %s %Φ H
    rw [(AxWpcAdeq.wpdcUnfoldStep AxirisGChk.chk st i s Φ).to_eq,
      (AxWp.wpcUnfoldStep st i s Φ).to_eq]
    isplit
    · icases H with ⟨H, -⟩
      iexact H
    isplit
    · icases H with ⟨-, H, -⟩
      iexact H
    icases H with ⟨-, -, H⟩
    unfold wpdMPreStepDef wpPreStepDef
    iintro %GD %ls ⟨%Hc, #Hg, Hl⟩
    ihave H := H $$ %GD %ls [Hl]
    · isplitr
      · ipureintro
        exact Hc
      isplitr
      · iexact Hg
      iexact Hl
    isplit
    · icases H with ⟨H, -⟩
      iintro %id %K %Hstep
      ihave H := H $$ %id %K %Hstep
      by_cases hadv : aidentAdvRd id = 1
      · simp only [hadv, ↓reduceIte]
        obtain ⟨v0, Hgv, Hlenimp⟩ := areadStepGraphValue GD i s id K Hstep
        have Hlen0 := Hlenimp hadv
        ihave H := H $$ %v0 %Hgv %Hlen0
        unfold wpEvStep
        iintro %na Hpg
        imod H $$ %na Hpg with H
        imodintro
        inext
        imod H with ⟨%a, %R, %nu, %nuu, %ls', -, Hsplit, Hfe, Hna, Hloc, Hc⟩
        imodintro
        iexists v0, R, nu, nuu, ls'
        isplitr
        · ipureintro
          exact Hlen0
        iframe Hsplit Hfe Hna Hloc
        iapply IH $$ %(K v0) %Φ Hc
      · simp only [hadv, ↓reduceIte]
        iintro %v %Hv %Hlen
        ihave H := H $$ %v %Hv %Hlen
        iapply wpSkipStepMono $$ [] H
        inext
        iintro Hc
        iapply IH $$ %(K v) %Φ Hc
    isplit
    · icases H with ⟨-, H, -⟩
      iintro %l %s' %Hstep %Hpin
      ihave H := H $$ %l %s' %Hstep %Hpin
      cases wlWdata l with
      | some data =>
        iapply wpEvStepMono $$ [] H
        inext
        iintro %_ Hc
        iapply IH $$ %s' %Φ Hc
      | none =>
        iapply wpSkipStepMono $$ [] H
        inext
        iintro Hc
        iapply IH $$ %s' %Φ Hc
    · icases H with ⟨-, -, H, -⟩
      iintro %s' %Hstep
      ihave H := H $$ %s' %Hstep
      iapply wpSkipStepMono $$ [] H
      inext
      iintro Hc
      iapply IH $$ %s' %Φ Hc
  iintro H
  iapply h $$ %s %Φ H

end wpdcWpcSec

/-! # 3b. The checkpoint CLASS from a pure BOUNDARY predicate -/

section chkOfBoundary
variable {GF : BundledGFunctors} (I : Agent → Athread → Prop)

/-- Rocq `chk_bd`: `I` demanded only at instruction boundaries. -/
def chkBd : Agent → Athread → IProp GF :=
  fun i s => iprop(⌜AxWp.atBoundary s → I i s⌝)

theorem chkBdMidInstr (i : Agent) (s : Athread) :
    ¬ AxWp.atBoundary s → iprop(True) ⊢ chkBd (GF := GF) I i s := by
  intro Hb
  unfold chkBd
  exact pure_intro (fun Hbd => absurd Hbd Hb)

/-- Rocq `axirisGChk_bd` (a named def; Rocq's `Local Existing Instance` is not replicated). -/
@[reducible] def axirisGChkBd : AxirisGChk GF :=
  { chk := chkBd I, chkMidInstr := chkBdMidInstr I }

theorem chkBdPure : @chkPure GF (axirisGChkBd I) (fun i s => AxWp.atBoundary s → I i s) :=
  fun _ _ => .rfl

theorem wpdcWpcBd {hlc : HasLC} [InvGS_gen hlc GF] [AxirisG GF] [Axpol] (st : Stuckness)
    (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpdc (chkBd I) st i s Φ ⊢ @wpc hlc GF _ _ _ (axirisGChkBd I) st i s Φ :=
  @wpdcWpc hlc GF _ _ _ (axirisGChkBd I) st i s Φ

end chkOfBoundary

/-! # 4. `wpcAdequacy`: Tier-A adequacy with checkpointed premises -/

section WpcAdeq
variable {GF : BundledGFunctors.{0,0,0}}

/-- Rocq `Local Instance AxGAc` (a named reducible def). -/
@[reducible] def axGAc [AxannotGS GF] (GD : Gdexec) (N obSt0 : Type)
    (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) : AxirisG GF :=
  axGA2 GD N obSt0 obStInterp0 nm

/-- Rocq `tierA_wpdc`: `tierAWpd`'s checkpointed twin at `nm`. -/
def tierAWpdc {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] [Axpol] (GD : Gdexec)
    (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N)
    (ck : Agent → Athread → IProp GF) (s : Athread) (st : Stuckness) (i : Agent)
    (Φ : Athread → IProp GF) : IProp GF :=
  @wpdc hlc GF _ (axGAc GD N obSt0 obStInterp0 nm) _ ck st i s Φ

theorem tierAWpdcWpd {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] [Axpol] (GD : Gdexec)
    (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N)
    (ck : Agent → Athread → IProp GF) (s : Athread) (st : Stuckness) (i : Agent)
    (Φ : Athread → IProp GF) :
    tierAWpdc GD N obSt0 obStInterp0 nm ck s st i Φ ⊢
      tierAWpd GD N obSt0 obStInterp0 nm s st i Φ := by
  unfold tierAWpdc tierAWpd
  exact @wpdcWpd hlc GF _ (axGAc GD N obSt0 obStInterp0 nm) _ ck st i s Φ

theorem tierAWpdcWpdChk {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] [Axpol] (GD : Gdexec)
    (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N)
    (ck : Agent → Athread → IProp GF) (chkp : Agent → Athread → Prop)
    (Hchkp : ∀ i s, ck i s ⊢ iprop(⌜chkp i s⌝))
    (s : Athread) (st : Stuckness) (i : Agent) (Φp : Athread → Prop) :
    tierAWpdc GD N obSt0 obStInterp0 nm ck s st i (fun s => iprop(⌜Φp s⌝)) ⊢
      tierAWpd GD N obSt0 obStInterp0 nm s st i
        (fun s => iprop(⌜if isTerminated s then Φp s else chkp i s⌝)) := by
  unfold tierAWpdc tierAWpd
  refine (@wpdcWpdChk hlc GF _ (axGAc GD N obSt0 obStInterp0 nm) _ ck st i s _).trans ?_
  exact @wpdMono hlc GF _ (axGAc GD N obSt0 obStInterp0 nm) _ st i s _ _
    (fun k => psiCkPure ck chkp Hchkp i Φp k)

/-- Transport of a whole-harts premise along a per-hart entailment. -/
theorem hartsPremiseMono {GF : BundledGFunctors} (harts : List Agent)
    (A B C : Agent → IProp GF) (HBC : ∀ i, B i ⊢ C i)
    (Hprem : ⊢ ([∗list] i ∈ harts, A i) -∗ [∗list] i ∈ harts, B i) :
    ⊢ ([∗list] i ∈ harts, A i) -∗ [∗list] i ∈ harts, C i :=
  entails_wand ((wand_entails Hprem).trans
    (BigSepL.bigSepL_mono_of_forall (fun {_ x} => HBC x)))

/-- THE THEOREM (`wpc_adequacy`, arbitrary completed scheduler run): `tierAAdequacyAnnRun`'s
premises with the per-hart premise CHECKPOINTED; every hart's end state satisfies the
postcondition AND the checkpoint. -/
theorem wpcAdequacyAnnRun [InvGpreS GF] [AxannotG GF] [Axpol]
    (GD : Gdexec) (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N → Agent → IProp GF)
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (harts : List Agent) (Hnd : harts.Nodup)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ harts)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N) i, i ∈ harts →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (ck : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF], N → Agent → Athread → IProp GF)
    (chkp : Agent → Athread → Prop)
    (Hchkp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N) i s,
      ck nm i s ⊢ iprop(⌜chkp i s⌝))
    (Hwp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpdc GD N obSt0 obStInterp0 nm (ck nm) (s0 i) .MaybeStuck i
            (fun s => iprop(⌜post i s⌝)))
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (Hsched : ∃ sst : Sstate, rtc (schedStep GD.gdG) sst0 sst ∧
      sst.sN = GD.gdG.gxGmo.length ∧ sst.sD = ∅ ∧ axpolWfL GD sst.sProc) :
    ∀ i, i ∈ harts → post i (sN i) ∧ chkp i (sN i) := by
  intro i Hi
  refine ⟨?_, ?_⟩
  · refine tierAAdequacyAnnRun GD N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts s0 sN n
      Hrun Hk0 Hend post ?_ HobAlloc Hsched i Hi
    intro _ _ nm
    exact hartsPremiseMono harts _ _ _
      (fun j => tierAWpdcWpd GD N obSt0 obStInterp0 nm (ck nm) (s0 j) .MaybeStuck j
        (fun s => iprop(⌜post j s⌝))) (Hwp nm)
  · have Hp2 := tierAAdequacyAnnRun GD N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts s0
      sN n Hrun Hk0 Hend (fun j s => if isTerminated s then post j s else chkp j s)
      (fun nm => hartsPremiseMono harts _ _ _
        (fun j => tierAWpdcWpdChk GD N obSt0 obStInterp0 nm (ck nm) chkp (Hchkp nm) (s0 j)
          .MaybeStuck j (post j)) (Hwp nm))
      HobAlloc Hsched i Hi
    simpa only [isTerminated, Bool.false_eq_true, ↓reduceIte] using Hp2

/-- Same, over the gate-free run with gmo-bounded policies (`tierAAdequacyAnnGmo`'s
premises). -/
theorem wpcAdequacyAnnGmo [InvGpreS GF] [AxannotG GF] [Axpol]
    (GD : Gdexec) (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N → Agent → IProp GF)
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (harts : List Agent) (Hnd : harts.Nodup)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ harts)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N) i, i ∈ harts →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (ck : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF], N → Agent → Athread → IProp GF)
    (chkp : Agent → Athread → Prop)
    (Hchkp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N) i s,
      ck nm i s ⊢ iprop(⌜chkp i s⌝))
    (Hwp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpdc GD N obSt0 obStInterp0 nm (ck nm) (s0 i) .MaybeStuck i
            (fun s => iprop(⌜post i s⌝)))
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (HsPolGmo : ∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e)
    (HlobpGmo : ∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e) :
    ∀ i, i ∈ harts → post i (sN i) ∧ chkp i (sN i) := by
  intro i Hi
  refine ⟨?_, ?_⟩
  · refine tierAAdequacyAnnGmo GD N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts s0 sN n
      Hrun Hk0 Hend post ?_ HobAlloc HsPolGmo HlobpGmo i Hi
    intro _ _ nm
    exact hartsPremiseMono harts _ _ _
      (fun j => tierAWpdcWpd GD N obSt0 obStInterp0 nm (ck nm) (s0 j) .MaybeStuck j
        (fun s => iprop(⌜post j s⌝))) (Hwp nm)
  · have Hp2 := tierAAdequacyAnnGmo GD N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts s0
      sN n Hrun Hk0 Hend (fun j s => if isTerminated s then post j s else chkp j s)
      (fun nm => hartsPremiseMono harts _ _ _
        (fun j => tierAWpdcWpdChk GD N obSt0 obStInterp0 nm (ck nm) chkp (Hchkp nm) (s0 j)
          .MaybeStuck j (post j)) (Hwp nm))
      HobAlloc HsPolGmo HlobpGmo i Hi
    simpa only [isTerminated, Bool.false_eq_true, ↓reduceIte] using Hp2

/-- SANITY (the checkpoint-free instance): at `ck := True` the checkpointed premise follows from
the plain Tier-A premise (`wpdWpdc`), so `wpcAdequacyAnnGmo` specializes to exactly
`tierAAdequacyAnnGmo`. -/
theorem wpcAdequacyAnnGmoTriv [InvGpreS GF] [AxannotG GF] [Axpol]
    (GD : Gdexec) (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N → Agent → IProp GF)
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (harts : List Agent) (Hnd : harts.Nodup)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ harts)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N) i, i ∈ harts →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpd GD N obSt0 obStInterp0 nm (s0 i) .MaybeStuck i (fun s => iprop(⌜post i s⌝)))
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (HsPolGmo : ∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e)
    (HlobpGmo : ∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e) :
    ∀ i, i ∈ harts → post i (sN i) := by
  intro i Hi
  refine (wpcAdequacyAnnGmo GD N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts s0 sN n Hrun
    Hk0 Hend post (fun _ _ _ => iprop(True)) (fun _ _ => True)
    (fun _ _ _ => pure_intro trivial) ?_ HobAlloc HsPolGmo HlobpGmo i Hi).1
  intro _ _ nm
  refine hartsPremiseMono harts _ _ _ (fun j => ?_) (Hwp nm)
  unfold tierAWpdc tierAWpd
  exact @wpdWpdc .hasNoLC GF _ (axGAc GD N obSt0 obStInterp0 nm) _ (fun _ _ => iprop(True))
    .MaybeStuck j (s0 j) (fun s => iprop(⌜post j s⌝)) (fun _ => .rfl)

end WpcAdeq

/-! # 5. SATISFIABILITY of the checkpointed premise on a REAL client -/

/-- `AxEpiAdeq.epiReloadSound` re-derived through `wpcAdequacyAnnGmo` with the NON-TRIVIAL
checkpoint `hartIs cpu`: the same premises, and the end state is still hart `cpu`. -/
theorem epiReloadSoundChk (GD : Gdexec) (cpu : CPU) (a : Int)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0)
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
    (Hend : sN.atK = (AxOpsem.grow GD 0).length) :
    graphValue GD (0, 1) = some sdData ∧ hartIs cpu sN := by
  have Hharts' : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ [0] := by
    intro e He
    rw [Hharts e He]
    exact List.mem_singleton.2 rfl
  have Hs_pol : ∀ e e', e' ∈ Axpol.sPol (self := epiPol) GD e → gmoLt GD.gdG e' e :=
    fun e e' he' => gmoPrefixGmoLt _ Hcons.1 e e' (elemOfListToSet.1 he')
  have Hlobp : ∀ e e', e' ∈ Axpol.lobp (self := epiPol) GD e → gmoLt GD.gdG e' e := by
    intro e e' he'
    change e' ∈ epiLobp GD e at he'
    unfold epiLobp at he'
    split at he'
    · rename_i heq
      subst heq
      have h1 := elemOfSingleton.1 (elemOfIntersection.1 he').1
      subst h1
      exact Hlob_gmo
    · exact absurd he' notElemOfEmpty
  have Hwp : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ ([∗list] i ∈ [0], epiInit a nm i) -∗
        [∗list] i ∈ [0],
          @tierAWpdc epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm
            (fun _ s => iprop(⌜hartIs cpu s⌝))
            ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ .MaybeStuck i
            (fun s => iprop(⌜epiPost GD i s⌝)) := by
    intro _ _ nm
    iintro Hi
    ihave Hi := BigSepL.bigSepL_singleton.1 $$ Hi
    ihave Hi := (AxEpiAdeq.epiInit0 a nm).1 $$ Hi
    iapply BigSepL.bigSepL_singleton.2
    unfold tierAWpdc
    iapply (@wpdWpdcInv .hasNoLC epiGF _ (axGAc GD GName Unit epiObInterp nm) epiPol
      (fun _ s => hartIs cpu s) 0 (hartIsStepClosed cpu 0) .MaybeStuck
      ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ _
      (hartIsAThread cpu _ _ _ _ 0))
    iapply (wpdEpiGa2 (pol := epiPol) GD nm cpu ibNone a Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld
      Hok_ld Hlen) $$ Hi
  have Hfin := @wpcAdequacyAnnGmo epiGF _ _ epiPol GD GName Unit epiObInterp (epiInit a)
    epiAxpolWf Hcons [0] (by decide) Hharts'
    (fun _ => ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩) (fun _ => sN)
    (fun _ => n)
    (fun Hann nm i Hi => by rw [List.mem_singleton.1 Hi]; exact Hrun Hann nm)
    (fun _ _ => rfl)
    (fun i Hi => by rw [List.mem_singleton.1 Hi]; exact Hend)
    (epiPost GD) (fun _ _ s => iprop(⌜hartIs cpu s⌝)) (fun _ s => hartIs cpu s)
    (fun _ _ _ => .rfl) Hwp (epiHobAlloc a GD) Hs_pol Hlobp 0 (List.mem_singleton.2 rfl)
  exact ⟨Hfin.1 (by rw [Hend, Hlen]), Hfin.2⟩

end Weak
