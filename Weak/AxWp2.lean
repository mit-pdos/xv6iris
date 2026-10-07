/-
Weak: **TIED ANNOTATIONS AND THE BASE WEAKEST PRECONDITION**, part 2 of 2 (AxSL tier):
the weakest precondition `AxWp.wp` (port of AxSL `low/weakestpre.v`), the checkpointed `wpc`
(`low/weakestpre_chk.v`) and the non-vacuity skeleton.

Rocq: `iris/AxWp.v` @ xxvzwolszwmp, §§5–7 (§§1–4 in `Weak/AxWp.lean`).

The Rocq header and ALL deviations are in `Weak/AxWp.lean`'s header (one Rocq file, split at
the §4/§5 boundary for size).  In short: plain `fixpoint`s, no seals, no notations (`AxWp.wp
st i s Φ` for `WP s @ st; i {{ Φ }}`, `wpc st i s Φ` for `WPc …`); `[InvGS_gen hlc GF]` for any
`hlc`; map unions `PartialMap.union`; `Proper` instances as theorems; the skeleton names
`skelAxirisG γg Φp` explicitly; the L0 fetch oracle (`ax_text`, `T`, `gx_img`) is gone (O2
Stage C, `Weak/AxWp.lean` deviation 10).

**Rocq → Lean name map.**  §5: `post_lifting` `postLifting`, `post_lifting_interp_mod`
`postLiftingInterpMod`, `post_lifting_strong_mono` `postLiftingStrongMono`, `post_lifting_True`
`postLiftingTrue`, `flow_eq_dyn(_def)` `flowEqDyn`, `flow_eq_dyn_mono` `flowEqDynMono`,
`flow_eq_dyn_frame` `flowEqDynFrame`, `flow_eq_dyn_pol_mono` `flowEqDynPolMono`,
`flow_eq_dyn_ne` `flowEqDynNe`, `progress_obl` `progressObl`, `progress_obl_maybestuck`
`progressOblMaybestuck`, `progress_obl_bupd` `progressOblBupd`, `progress_obl_iupd`
`progressOblIupd`, `progress_obl_of_pure` `progressOblOfPure`, `wp_ev_step` `wpEvStep`,
`wp_skip_step` `wpSkipStep`, `wp_ev_step_mono/bupd/iupd` `wpEvStepMono/Bupd/Iupd`,
`wp_skip_step_mono/bupd/iupd` `wpSkipStepMono/Bupd/Iupd`, `wp_pre_step_def` `wpPreStepDef`,
`wp_pre_step_def_mono/bupd/iupd` `wpPreStepDefMono/Bupd/Iupd`, `wp_pre` `wpPre`,
`wp_pre_contractive` `wpPreContractive`, `wp(_def)` `AxWp.wp`, `wp_unfold'` `wpUnfold'`,
`wp_stuck_mono` `wpStuckMono`, `wp_stuck_weaken` `wpStuckWeaken`, `wp_unfold` `wpUnfold`,
`wp_unfold_step` `wpUnfoldStep`, `wp_ne` `wpNe`, `wp_proper` `wpProper`, `wp_terminated'`
`wpTerminated'`, `wp_terminated_inv'` `wpTerminatedInv'`, `wp_strong_mono` `wpStrongMono`,
`bupd_wp` `bupdWp`, `iupd_wp` `iupdWp`, `wp_bupd` `wpBupd`, `wp_step_bupd` `wpStepBupd`,
`wp_mono` `wpMono`, `wp_mono'` `wpMono'`, `wp_flip_mono'` `wpFlipMono'`, `wp_frame_l/r`
`wpFrameL/R`, `wp_frame_step_l/r` `wpFrameStepL/R`, `wp_wand` `wpWand`, `wp_wand_l/r`
`wpWandL/R`, `wp_frame_wand_l` `wpFrameWandL`, `wp_progress_intro` `wpProgressIntro`,
`frame_wp` `frameWp`, `elim_modal_bupd_wp` `elimModalBupdWp`, `elim_modal_iupd_wp`
`elimModalIupdWp`, `add_modal_bupd_wp` `addModalBupdWp`.  §6: `wp_pre_chk` `wpPreChk`,
`wp_pre_chk_contractive` `wpPreChkContractive`, `wpc(_def)` `wpc`, `chk_obl` `chkObl`,
`chk_obl_triv` `chkOblTriv`, `chk_obl_mid_instr` `chkOblMidInstr`, `wpc_unfold'`
`wpcUnfold'`, `wpc_stuck_mono` `wpcStuckMono`, `wpc_stuck_weaken` `wpcStuckWeaken`,
`wpc_unfold` `wpcUnfold`, `wpc_post_or` `wpcPostOr`, `wpc_chk` `wpcChk`, `wpc_ne` `wpcNe`,
`wpc_proper` `wpcProper`, `wpc_terminated'` `wpcTerminated'`, `wpc_terminated_inv'`
`wpcTerminatedInv'`, `wpc_strong_mono` `wpcStrongMono`, `wpc_wp` `wpcWp`, `wp_wpc` `wpWpc`,
`bupd_wpc` `bupdWpc`, `iupd_wpc` `iupdWpc`, `wpc_bupd` `wpcBupd`, `wpc_step_bupd`
`wpcStepBupd`, `wpc_mono` `wpcMono`, `wpc_mono'` `wpcMono'`, `wpc_frame_l/r` `wpcFrameL/R`,
`wpc_wand` `wpcWand`, `wpc_frame_wand_l` `wpcFrameWandL`, `frame_wpc` `frameWpc`,
`elim_modal_bupd_wpc` `elimModalBupdWpc`, `elim_modal_iupd_wpc` `elimModalIupdWpc`.
§7: `axgraphG`/`AxGraphG` `AxgraphG` (`axgraph_inG` `axgraphInG`), `graph_agree` `graphAgree`,
`graph_agree_persistent` `graphAgreePersistent`, `graph_agree_agree` `graphAgreeAgree`,
`graph_agree_alloc` `graphAgreeAlloc`, `prot_interp` `protInterp`, `skel_axirisG`
`skelAxirisG`, `skel_annot_split` `skelAnnotSplit`, `skel_annot_merge` `skelAnnotMerge`,
`annot_alloc_at_progress` `annotAllocAtProgress`, `prot_interp_insert` `protInterpInsert`,
`flow_eq_dyn_triv` `flowEqDynTriv`, `skel_wp_skip_step_of_psi` `skelWpSkipStepOfPsi`.
Lean-only (file-qualified): `AxWp.wpEvStepDist`, `AxWp.wpSkipStepDist`,
`AxWp.wpPreStepDefDist`, `AxWp.wpcUnfoldStep`.

**Not ported:** `axgraphΣ`/`subG_axgraphΣ` (no gFunctor lists) and the §8 `Print Assumptions`.
-/
import Weak.AxWp

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 5. The weakest precondition (port of AxSL `low/weakestpre.v`) -/

section wpDef
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The postcondition under the hart's own annotations. -/
def postLifting (Φ : Athread → IProp GF) (i : Agent) (s : Athread) : IProp GF :=
  iprop(∀ na, AxirisG.annotInterp na ==∗ AxirisG.annotInterp na ∗
    (([∗map] e ↦ R ∈ na, if e.1 = i then R else iprop(True)) -∗ ▷ |==> Φ s))

theorem postLiftingInterpMod (Φ : Athread → IProp GF) (i : Agent) (s : Athread) :
    interpMod (postLifting Φ i s) ⊢ postLifting Φ i s := by
  unfold interpMod postLifting
  iintro H %na Hna
  imod H $$ %na Hna with ⟨H, Hna⟩
  iapply H $$ %na Hna

theorem postLiftingStrongMono (Φ Ψ : Athread → IProp GF) (i : Agent) (s : Athread) :
    ⊢ postLifting Φ i s -∗ (∀ k, Φ k ==∗ Ψ k) -∗ postLifting Ψ i s := by
  unfold postLifting
  iintro H HΦ %na Hannot
  imod H $$ %na Hannot with ⟨Hannot, H⟩
  imodintro
  iframe Hannot
  iintro HP
  ihave H := H $$ HP
  inext
  imod H
  iapply HΦ $$ H

theorem postLiftingTrue (Φ : Athread → IProp GF) (i : Agent) (s : Athread) :
    (iprop(True) ⊢ Φ s) → ⊢ postLifting Φ i s := by
  intro HΦ
  unfold postLifting
  iintro %na Hna
  imodintro
  iframe Hna
  iintro _
  inext
  imodintro
  iapply HΦ
  itrivial

/-- THE FLOW EQUATION at event `e`, parametric in the handout `sOb0` (design deviation 1: a
SUPERSET requirement `sOb0 ⊆ sOb`). -/
def flowEqDyn (GD : Gdexec) (e : Geid) (sOb0 : GSet Geid) (flowIn : Mea GF) (R : IProp GF) :
    IProp GF :=
  iprop(∀ (σ : AxirisG.obSt GF) (sOb : GSet Geid),
    ⌜sOb0 ⊆ sOb⌝ -∗ ⌜e ∉ sOb⌝ -∗
    AxirisG.obStInterp GD σ sOb -∗ ([∗map] Rin ∈ flowIn, Rin) ={⊤,∅}=∗ ▷ |={∅,⊤}=>
    ∃ σ', AxirisG.obStInterp GD σ' (({e} : GSet Geid) ∪ sOb) ∗ R)

theorem flowEqDynMono (GD : Gdexec) (e : Geid) (sOb0 : GSet Geid) (flowIn : Mea GF)
    (R1 R2 : IProp GF) :
    ⊢ ▷ (R1 -∗ R2) -∗ flowEqDyn GD e sOb0 flowIn R1 -∗ flowEqDyn GD e sOb0 flowIn R2 := by
  unfold flowEqDyn
  iintro Himpl H %σ %sOb %Hsub %Hnin Hob Rin
  imod H $$ %σ %sOb %Hsub %Hnin Hob Rin with H
  imodintro
  inext
  imod H with ⟨%σ', Hob, HR⟩
  imodintro
  iexists σ'
  iframe Hob
  iapply Himpl $$ HR

theorem flowEqDynFrame (GD : Gdexec) (e : Geid) (sOb0 : GSet Geid) (flowIn : Mea GF)
    (R R' : IProp GF) :
    ⊢ ▷ R' -∗ flowEqDyn GD e sOb0 flowIn R -∗ flowEqDyn GD e sOb0 flowIn iprop(R' ∗ R) := by
  unfold flowEqDyn
  iintro HR' H %σ %sOb %Hsub %Hnin Hob Rin
  imod H $$ %σ %sOb %Hsub %Hnin Hob Rin with H
  imodintro
  inext
  imod H with ⟨%σ', Hob, HR⟩
  imodintro
  iexists σ'
  iframe Hob HR' HR

/-- A smaller handout requirement is a stronger flow equation. -/
theorem flowEqDynPolMono (GD : Gdexec) (e : Geid) (sob1 sob2 : GSet Geid) (flowIn : Mea GF)
    (R : IProp GF) :
    sob1 ⊆ sob2 → flowEqDyn GD e sob1 flowIn R ⊢ flowEqDyn GD e sob2 flowIn R := by
  intro Hsub
  unfold flowEqDyn
  iintro H %σ %sOb %Hsub' %Hnin Hob Rin
  iapply H $$ %σ %sOb %(fun x hx => Hsub' x (Hsub x hx)) %Hnin Hob Rin

theorem flowEqDynNe (GD : Gdexec) (e : Geid) (sOb0 : GSet Geid) (flowIn : Mea GF) :
    OFE.NonExpansive (flowEqDyn (GF := GF) GD e sOb0 flowIn) where
  ne {n R1 R2} h := by
    unfold flowEqDyn
    refine BI.forall_ne (fun σ => ?_)
    refine BI.forall_ne (fun sOb => ?_)
    refine BI.wand_ne.ne .rfl ?_
    refine BI.wand_ne.ne .rfl ?_
    refine BI.wand_ne.ne .rfl ?_
    refine BI.wand_ne.ne .rfl ?_
    refine BIFUpdate.ne.ne ?_
    refine BI.later_ne.ne ?_
    refine BIFUpdate.ne.ne ?_
    refine BI.exists_ne (fun σ' => ?_)
    exact BI.sep_ne.ne .rfl h

/-- THE PROGRESS OBLIGATION: at `NotStuck` the hart's own step is enabled in some row
extension. -/
def progressObl (st : Stuckness) (i : Agent) (s : Athread) : IProp GF :=
  match st with
  | .MaybeStuck => iprop(True)
  | .NotStuck =>
    iprop(∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
      ⌜rvwmoCatConsistent GD⌝ ∗ □ AxirisG.gconstInterp GD ∗ AxirisG.localInterp GD i s.atK ls -∗
      interpMod iprop(⌜reducibleGd GD i s⌝))

theorem progressOblMaybestuck (i : Agent) (s : Athread) :
    progressObl (GF := GF) .MaybeStuck i s ⊣⊢ iprop(True) := .rfl

theorem progressOblBupd (st : Stuckness) (i : Agent) (s : Athread) :
    iprop(|==> progressObl (GF := GF) st i s) ⊢ progressObl st i s := by
  cases st with
  | NotStuck =>
    unfold progressObl
    iintro H %GD %ls Hpre
    imod H
    iapply H $$ %GD %ls Hpre
  | MaybeStuck =>
    unfold progressObl
    iintro _
    itrivial

theorem progressOblIupd (st : Stuckness) (i : Agent) (s : Athread) :
    interpMod (progressObl (GF := GF) st i s) ⊢ progressObl st i s := by
  cases st with
  | NotStuck =>
    unfold progressObl
    iintro H %GD %ls Hpre
    imod H
    iapply H $$ %GD %ls Hpre
  | MaybeStuck =>
    unfold progressObl
    iintro _
    itrivial

theorem progressOblOfPure (st : Stuckness) (i : Agent) (s : Athread) :
    (∀ GD, reducibleGd GD i s) → ⊢ progressObl (GF := GF) st i s := by
  intro Hred
  cases st with
  | NotStuck =>
    unfold progressObl
    iintro %GD %ls _
    iapply interpModIntro
    ipureintro
    exact Hred GD
  | MaybeStuck =>
    unfold progressObl
    itrivial

/-- THE EVENT STEP at `(i, k)`. -/
def wpEvStep {A : Type} (GD : Gdexec) (i : Agent) (k : Nat) (ok val : A → Prop) (k' : A → Nat)
    (Ψ : A → IProp GF) : IProp GF :=
  iprop(∀ na, naAtProgress GD i k na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
    ∃ (a : A) (R : IProp GF) (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
      ⌜ok a⌝ ∗
      naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) naUsed iprop(R ∗ ⌜val a⌝) ∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) ∗
      AxirisG.localInterp GD i (k' a) ls' ∗
      Ψ a)

/-- THE SKIP STEP: no event, the annotations untouched. -/
def wpSkipStep (GD : Gdexec) (i : Agent) (k' : Nat) (Ψ : IProp GF) : IProp GF :=
  iprop(∀ na, AxirisG.annotInterp na -∗ |==> ▷ |==>
    ∃ ls' : AxirisG.logTsT GF, AxirisG.annotInterp na ∗ AxirisG.localInterp GD i k' ls' ∗ Ψ)

/-! ## 5.1 The structural laws of the two step shapes, proved once -/

theorem wpEvStepMono {A : Type} (GD : Gdexec) (i : Agent) (k : Nat) (ok val : A → Prop)
    (k' : A → Nat) (Ψ Ψ' : A → IProp GF) :
    ⊢ ▷ (∀ a, Ψ a -∗ Ψ' a) -∗ wpEvStep GD i k ok val k' Ψ -∗ wpEvStep GD i k ok val k' Ψ' := by
  unfold wpEvStep
  iintro HΨ H %na Hna
  imod H $$ %na Hna with H
  imodintro
  inext
  imod H with ⟨%a, %R, %nu, %nuu, %ls', Hok, Hsplit, Hfe, Hna, Hloc, HΨa⟩
  imodintro
  iexists a, R, nu, nuu, ls'
  iframe Hok Hsplit Hfe Hna Hloc
  iapply HΨ $$ HΨa

theorem wpSkipStepMono (GD : Gdexec) (i : Agent) (k' : Nat) (Ψ Ψ' : IProp GF) :
    ⊢ ▷ (Ψ -∗ Ψ') -∗ wpSkipStep GD i k' Ψ -∗ wpSkipStep GD i k' Ψ' := by
  unfold wpSkipStep
  iintro HΨ H %na Hna
  imod H $$ %na Hna with H
  imodintro
  inext
  imod H with ⟨%ls', Hna, Hloc, HΨa⟩
  imodintro
  iexists ls'
  iframe Hna Hloc
  iapply HΨ $$ HΨa

theorem wpEvStepBupd {A : Type} (GD : Gdexec) (i : Agent) (k : Nat) (ok val : A → Prop)
    (k' : A → Nat) (Ψ : A → IProp GF) :
    iprop(|==> wpEvStep GD i k ok val k' Ψ) ⊢ wpEvStep GD i k ok val k' Ψ := by
  unfold wpEvStep
  iintro H %na Hna
  imod H
  iapply H $$ %na Hna

theorem wpSkipStepBupd (GD : Gdexec) (i : Agent) (k' : Nat) (Ψ : IProp GF) :
    iprop(|==> wpSkipStep GD i k' Ψ) ⊢ wpSkipStep GD i k' Ψ := by
  unfold wpSkipStep
  iintro H %na Hna
  imod H
  iapply H $$ %na Hna

theorem wpEvStepIupd {A : Type} (GD : Gdexec) (i : Agent) (k : Nat) (ok val : A → Prop)
    (k' : A → Nat) (Ψ : A → IProp GF) :
    interpMod (wpEvStep GD i k ok val k' Ψ) ⊢ wpEvStep GD i k ok val k' Ψ := by
  unfold wpEvStep interpMod
  iintro H %na ⟨Hpg, Hna⟩
  imod H $$ %na Hna with ⟨H, Hna⟩
  iapply H $$ %na [$Hpg $Hna]

theorem wpSkipStepIupd (GD : Gdexec) (i : Agent) (k' : Nat) (Ψ : IProp GF) :
    interpMod (wpSkipStep GD i k' Ψ) ⊢ wpSkipStep GD i k' Ψ := by
  unfold wpSkipStep interpMod
  iintro H %na Hna
  imod H $$ %na Hna with ⟨H, Hna⟩
  iapply H $$ %na Hna

/-! ## 5.2 The step case -/

/-- THE STEP CASE: (a) the read, angelic in the value, the RMW's read half pinned; (b) every
other program step, demonic, a write validates its data; (c) the PLIC wire. -/
def wpPreStepDef (i : Agent) (wp : Athread → (Athread → IProp GF) → IProp GF) (s : Athread)
    (Φ : Athread → IProp GF) : IProp GF :=
  iprop(∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
    ⌜rvwmoCatConsistent GD⌝ ∗ □ AxirisG.gconstInterp GD ∗ AxirisG.localInterp GD i s.atK ls -∗
    (∀ (id : AidentT) (K : List (BitVec 8) → Athread),
       ⌜areadStep (AxOpsem.grow GD i) s id K⌝ -∗
       if aidentAdvRd id = 1 then
         wpEvStep GD i s.atK
           (fun v => v.length = aidentN id) (fun v => graphValue GD (i, s.atK) = some v)
           (fun v => (K v).atK) (fun v => wp (K v) Φ)
       else
         ∀ v, ⌜graphValue GD (i, s.atK) = some v⌝ -∗ ⌜v.length = aidentN id⌝ -∗
           wpSkipStep GD i (K v).atK (wp (K v) Φ)) ∧
    (∀ (l : Wlabel) (s' : Athread),
       ⌜AxOpsem.astepProg (AxOpsem.grow GD i) s l s'⌝ -∗
       ⌜WeakAxRealize.fetchPin GD.gdG.gxImg l⌝ -∗
       match wlWdata l with
       | some data =>
           wpEvStep GD i s.atK
             (fun _ : Unit => True) (fun _ => graphData GD (i, s.atK) = some data)
             (fun _ => s'.atK) (fun _ => wp s' Φ)
       | none => wpSkipStep GD i s'.atK (wp s' Φ)) ∧
    (∀ s', ⌜awire s s'⌝ -∗ wpSkipStep GD i s'.atK (wp s' Φ)))

/-- The step case is monotone in the continuation, under a later. -/
theorem wpPreStepDefMono (i : Agent) (wp1 wp2 : Athread → (Athread → IProp GF) → IProp GF)
    (s : Athread) (Φ1 Φ2 : Athread → IProp GF) :
    ⊢ ▷ (∀ s', wp1 s' Φ1 -∗ wp2 s' Φ2) -∗ wpPreStepDef i wp1 s Φ1 -∗ wpPreStepDef i wp2 s Φ2 := by
  unfold wpPreStepDef
  iintro Hmono H %GD %ls Hpre
  ihave H := H $$ %GD %ls Hpre
  isplit
  · icases H with ⟨H, -⟩
    iintro %id %K %Hstep
    ihave H := H $$ %id %K %Hstep
    by_cases hadv : aidentAdvRd id = 1
    · simp only [hadv, ↓reduceIte]
      iapply wpEvStepMono $$ [Hmono] H
      inext
      iintro %v Hw
      iapply Hmono $$ Hw
    · simp only [hadv, ↓reduceIte]
      iintro %v %Hv %Hlen
      ihave H := H $$ %v %Hv %Hlen
      iapply wpSkipStepMono $$ [Hmono] H
      inext
      iintro Hw
      iapply Hmono $$ Hw
  isplit
  · icases H with ⟨-, H, -⟩
    iintro %l %s' %Hstep %Hpin
    ihave H := H $$ %l %s' %Hstep %Hpin
    cases wlWdata l with
    | some data =>
      iapply wpEvStepMono $$ [Hmono] H
      inext
      iintro %_ Hw
      iapply Hmono $$ Hw
    | none =>
      iapply wpSkipStepMono $$ [Hmono] H
      inext
      iintro Hw
      iapply Hmono $$ Hw
  · icases H with ⟨-, -, H⟩
    iintro %s' %Hstep
    ihave H := H $$ %s' %Hstep
    iapply wpSkipStepMono $$ [Hmono] H
    inext
    iintro Hw
    iapply Hmono $$ Hw

theorem wpPreStepDefBupd (i : Agent) (wp : Athread → (Athread → IProp GF) → IProp GF)
    (s : Athread) (Φ : Athread → IProp GF) :
    iprop(|==> wpPreStepDef i wp s Φ) ⊢ wpPreStepDef i wp s Φ := by
  unfold wpPreStepDef
  iintro H %GD %ls Hpre
  isplit
  · iintro %id %K %Hstep
    by_cases hadv : aidentAdvRd id = 1
    · simp only [hadv, ↓reduceIte]
      iapply wpEvStepBupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨H, -⟩
      ihave H := H $$ %id %K %Hstep
      simp only [hadv, ↓reduceIte]
      iexact H
    · simp only [hadv, ↓reduceIte]
      iintro %v %Hv %Hlen
      iapply wpSkipStepBupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨H, -⟩
      ihave H := H $$ %id %K %Hstep
      simp only [hadv, ↓reduceIte]
      iapply H $$ %v %Hv %Hlen
  isplit
  · iintro %l %s' %Hstep %Hpin
    cases hl : wlWdata l with
    | some data =>
      iapply wpEvStepBupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨-, H, -⟩
      ihave H := H $$ %l %s' %Hstep %Hpin
      rw [hl]
      iexact H
    | none =>
      iapply wpSkipStepBupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨-, H, -⟩
      ihave H := H $$ %l %s' %Hstep %Hpin
      rw [hl]
      iexact H
  · iintro %s' %Hstep
    iapply wpSkipStepBupd
    imod H
    imodintro
    icases H $$ %GD %ls Hpre with ⟨-, -, H⟩
    iapply H $$ %s' %Hstep

theorem wpPreStepDefIupd (i : Agent) (wp : Athread → (Athread → IProp GF) → IProp GF)
    (s : Athread) (Φ : Athread → IProp GF) :
    interpMod (wpPreStepDef i wp s Φ) ⊢ wpPreStepDef i wp s Φ := by
  unfold wpPreStepDef
  iintro H %GD %ls Hpre
  isplit
  · iintro %id %K %Hstep
    by_cases hadv : aidentAdvRd id = 1
    · simp only [hadv, ↓reduceIte]
      iapply wpEvStepIupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨H, -⟩
      ihave H := H $$ %id %K %Hstep
      simp only [hadv, ↓reduceIte]
      iexact H
    · simp only [hadv, ↓reduceIte]
      iintro %v %Hv %Hlen
      iapply wpSkipStepIupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨H, -⟩
      ihave H := H $$ %id %K %Hstep
      simp only [hadv, ↓reduceIte]
      iapply H $$ %v %Hv %Hlen
  isplit
  · iintro %l %s' %Hstep %Hpin
    cases hl : wlWdata l with
    | some data =>
      iapply wpEvStepIupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨-, H, -⟩
      ihave H := H $$ %l %s' %Hstep %Hpin
      rw [hl]
      iexact H
    | none =>
      iapply wpSkipStepIupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨-, H, -⟩
      ihave H := H $$ %l %s' %Hstep %Hpin
      rw [hl]
      iexact H
  · iintro %s' %Hstep
    iapply wpSkipStepIupd
    imod H
    imodintro
    icases H $$ %GD %ls Hpre with ⟨-, -, H⟩
    iapply H $$ %s' %Hstep

/-! ## 5.3 `wpPre` and the fixpoint -/

theorem AxWp.wpEvStepDist {A : Type} (GD : Gdexec) (i : Agent) (k : Nat) (ok val : A → Prop)
    (k' : A → Nat) (Ψ Ψ' : A → IProp GF) (n : Nat) (h : ∀ m, m < n → ∀ a, Ψ a ≡{m}≡ Ψ' a) :
    wpEvStep GD i k ok val k' Ψ ≡{n}≡ wpEvStep GD i k ok val k' Ψ' := by
  unfold wpEvStep
  refine BI.forall_ne (fun na => ?_)
  refine BI.wand_ne.ne .rfl ?_
  refine (BIUpdate.bupd_ne).ne ?_
  refine OFE.Contractive.distLater_dist (f := BIBase.later) (fun m hm => ?_)
  refine (BIUpdate.bupd_ne).ne ?_
  refine BI.exists_ne (fun a => ?_)
  refine BI.exists_ne (fun R => ?_)
  refine BI.exists_ne (fun nu => ?_)
  refine BI.exists_ne (fun nuu => ?_)
  refine BI.exists_ne (fun ls' => ?_)
  refine BI.sep_ne.ne .rfl ?_
  refine BI.sep_ne.ne .rfl ?_
  refine BI.sep_ne.ne .rfl ?_
  refine BI.sep_ne.ne .rfl ?_
  refine BI.sep_ne.ne .rfl ?_
  exact h m hm a

theorem AxWp.wpSkipStepDist (GD : Gdexec) (i : Agent) (k' : Nat) (Ψ Ψ' : IProp GF) (n : Nat)
    (h : ∀ m, m < n → Ψ ≡{m}≡ Ψ') :
    wpSkipStep GD i k' Ψ ≡{n}≡ wpSkipStep GD i k' Ψ' := by
  unfold wpSkipStep
  refine BI.forall_ne (fun na => ?_)
  refine BI.wand_ne.ne .rfl ?_
  refine (BIUpdate.bupd_ne).ne ?_
  refine OFE.Contractive.distLater_dist (f := BIBase.later) (fun m hm => ?_)
  refine (BIUpdate.bupd_ne).ne ?_
  refine BI.exists_ne (fun ls' => ?_)
  refine BI.sep_ne.ne .rfl ?_
  refine BI.sep_ne.ne .rfl ?_
  exact h m hm

theorem AxWp.wpPreStepDefDist (i : Agent) (wp1 wp2 : Athread → (Athread → IProp GF) → IProp GF)
    (s : Athread) (Φ1 Φ2 : Athread → IProp GF) (n : Nat)
    (h : ∀ m, m < n → ∀ s', wp1 s' Φ1 ≡{m}≡ wp2 s' Φ2) :
    wpPreStepDef i wp1 s Φ1 ≡{n}≡ wpPreStepDef i wp2 s Φ2 := by
  unfold wpPreStepDef
  refine BI.forall_ne (fun GD => ?_)
  refine BI.forall_ne (fun ls => ?_)
  refine BI.wand_ne.ne .rfl ?_
  refine BI.and_ne.ne ?_ (BI.and_ne.ne ?_ ?_)
  · refine BI.forall_ne (fun id => ?_)
    refine BI.forall_ne (fun K => ?_)
    refine BI.wand_ne.ne .rfl ?_
    split
    · exact AxWp.wpEvStepDist _ _ _ _ _ _ _ _ n (fun m hm v => h m hm (K v))
    · refine BI.forall_ne (fun v => ?_)
      refine BI.wand_ne.ne .rfl ?_
      refine BI.wand_ne.ne .rfl ?_
      exact AxWp.wpSkipStepDist _ _ _ _ _ n (fun m hm => h m hm (K v))
  · refine BI.forall_ne (fun l => ?_)
    refine BI.forall_ne (fun s' => ?_)
    refine BI.wand_ne.ne .rfl ?_
    refine BI.wand_ne.ne .rfl ?_
    split
    · exact AxWp.wpEvStepDist _ _ _ _ _ _ _ _ n (fun m hm _ => h m hm s')
    · exact AxWp.wpSkipStepDist _ _ _ _ _ n (fun m hm => h m hm s')
  · refine BI.forall_ne (fun s' => ?_)
    refine BI.wand_ne.ne .rfl ?_
    exact AxWp.wpSkipStepDist _ _ _ _ _ n (fun m hm => h m hm s')

/-- Rocq `wp_pre`. -/
def wpPre (st : Stuckness) (i : Agent) (wp : Athread → (Athread → IProp GF) → IProp GF) :
    Athread → (Athread → IProp GF) → IProp GF :=
  fun s Φ =>
    if isTerminated s then postLifting Φ i s
    else iprop(progressObl st i s ∧ wpPreStepDef i wp s Φ)

instance wpPreContractive (st : Stuckness) (i : Agent) :
    OFE.Contractive (wpPre (GF := GF) st i) where
  distLater_dist {n wp wp'} Hwp := by
    intro s Φ
    unfold wpPre
    simp only [isTerminated, Bool.false_eq_true, ↓reduceIte]
    refine BI.and_ne.ne .rfl ?_
    exact AxWp.wpPreStepDefDist i wp wp' s Φ Φ n (fun m hm s' => Hwp m hm s' Φ)

/-- Rocq `wp` (duplicated name: file-qualified): the fixpoint of `wpPre`. -/
def AxWp.wp (st : Stuckness) (i : Agent) : Athread → (Athread → IProp GF) → IProp GF :=
  fixpoint (wpPre (GF := GF) st i)

end wpDef

section wp
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpUnfold' (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    AxWp.wp st i s Φ ⊣⊢ wpPre st i (AxWp.wp st i) s Φ :=
  BI.equiv_iff.1 <| OFE.eq_dist_2 <|
    fun _n => (fixpoint_unfold (f := (wpPre (GF := GF) st i).toContractiveHom)).dist s Φ

/-- The unfolding at a hart state: harts never terminate. -/
theorem wpUnfoldStep (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    AxWp.wp st i s Φ ⊣⊢ iprop(progressObl st i s ∧ wpPreStepDef i (AxWp.wp st i) s Φ) := by
  refine (wpUnfold' st i s Φ).trans ?_
  unfold wpPre
  simp only [isTerminated, Bool.false_eq_true, ↓reduceIte]
  exact .rfl

/-- A `NotStuck` wp is stronger than a `MaybeStuck` one. -/
theorem wpStuckMono (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    AxWp.wp .NotStuck i s Φ ⊢ AxWp.wp .MaybeStuck i s Φ := by
  have h : ⊢ ∀ s Φ, AxWp.wp (GF := GF) .NotStuck i s Φ -∗ AxWp.wp .MaybeStuck i s Φ := by
    iloeb as IH
    iintro %s %Φ H
    rw [(wpUnfoldStep .NotStuck i s Φ).to_eq, (wpUnfoldStep .MaybeStuck i s Φ).to_eq]
    isplit
    · unfold progressObl
      itrivial
    · icases H with ⟨-, H⟩
      iapply wpPreStepDefMono $$ [] H
      inext
      iintro %s' H'
      iapply IH $$ %s' %Φ H'
  iintro H
  iapply h $$ %s %Φ H

theorem wpStuckWeaken (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    AxWp.wp st i s Φ ⊢ AxWp.wp .MaybeStuck i s Φ := by
  cases st with
  | NotStuck => exact wpStuckMono i s Φ
  | MaybeStuck => exact .rfl

theorem wpUnfold (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    AxWp.wp st i s Φ ⊣⊢ wpPre st i (AxWp.wp st i) s Φ := wpUnfold' st i s Φ

instance wpNe (st : Stuckness) (i : Agent) (s : Athread) :
    OFE.NonExpansive (AxWp.wp (GF := GF) st i s) where
  ne {n Φ1 Φ2} HΦ := by
    induction n using Nat.strongRecOn generalizing s Φ1 Φ2 with
    | ind n IH =>
      rw [(wpUnfoldStep st i s Φ1).to_eq, (wpUnfoldStep st i s Φ2).to_eq]
      refine BI.and_ne.ne .rfl ?_
      exact AxWp.wpPreStepDefDist i _ _ s Φ1 Φ2 n
        (fun m hm s' => IH m hm s' (OFE.dist_lt HΦ hm))

theorem wpTerminated' (st : Stuckness) (i : Agent) (Φ : Athread → IProp GF) (s : Athread) :
    isTerminated s = true → postLifting Φ i s ⊢ AxWp.wp st i s Φ := by
  intro Hs
  simp [isTerminated] at Hs

theorem wpTerminatedInv' (st : Stuckness) (i : Agent) (Φ : Athread → IProp GF) (s : Athread) :
    isTerminated s = true → AxWp.wp st i s Φ ⊢ postLifting Φ i s := by
  intro Hs
  simp [isTerminated] at Hs

theorem wpStrongMono (st : Stuckness) (i : Agent) (s : Athread) (Φ Ψ : Athread → IProp GF) :
    ⊢ AxWp.wp st i s Φ -∗ (∀ k, Φ k ==∗ Ψ k) -∗ AxWp.wp st i s Ψ := by
  have h : ⊢ ∀ s (Φ Ψ : Athread → IProp GF),
      AxWp.wp st i s Φ -∗ (∀ k, Φ k ==∗ Ψ k) -∗ AxWp.wp st i s Ψ := by
    iloeb as IH
    iintro %s %Φ %Ψ H HΦ
    rw [(wpUnfoldStep st i s Φ).to_eq, (wpUnfoldStep st i s Ψ).to_eq]
    isplit
    · icases H with ⟨H, -⟩
      iexact H
    · icases H with ⟨-, H⟩
      iapply wpPreStepDefMono $$ [HΦ] H
      inext
      iintro %s' H'
      iapply IH $$ %s' %Φ %Ψ H' HΦ
  iintro H HΦ
  iapply h $$ %s %Φ %Ψ H HΦ

theorem bupdWp (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    iprop(|==> AxWp.wp st i s Φ) ⊢ AxWp.wp st i s Φ := by
  rw [(wpUnfoldStep st i s Φ).to_eq]
  iintro H
  isplit
  · iapply progressOblBupd
    imod H
    imodintro
    icases H with ⟨H, -⟩
    iexact H
  · iapply wpPreStepDefBupd
    imod H
    imodintro
    icases H with ⟨-, H⟩
    iexact H

theorem iupdWp (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    interpMod (AxWp.wp st i s Φ) ⊢ AxWp.wp st i s Φ := by
  rw [(wpUnfoldStep st i s Φ).to_eq]
  iintro H
  isplit
  · iapply progressOblIupd
    iapply interpModMono $$ [] H
    iintro ⟨H, -⟩
    iexact H
  · iapply wpPreStepDefIupd
    iapply interpModMono $$ [] H
    iintro ⟨-, H⟩
    iexact H

theorem wpBupd (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    AxWp.wp st i s (fun k => iprop(|==> Φ k)) ⊢ AxWp.wp st i s Φ := by
  iintro H
  iapply wpStrongMono $$ H
  iintro %k H
  iexact H

theorem wpStepBupd (st : Stuckness) (i : Agent) (s : Athread) (P : IProp GF)
    (Φ : Athread → IProp GF) :
    ⊢ (|==> P) -∗ AxWp.wp st i s (fun k => iprop(P ==∗ Φ k)) -∗ AxWp.wp st i s Φ := by
  iintro HP H
  iapply wpStrongMono $$ H
  iintro %k H
  imod HP
  iapply H $$ HP

/-! ## 5.4 Derived rules -/

theorem wpMono (st : Stuckness) (i : Agent) (s : Athread) (Φ Ψ : Athread → IProp GF)
    (HΦ : ∀ k, Φ k ⊢ Ψ k) : AxWp.wp st i s Φ ⊢ AxWp.wp st i s Ψ := by
  iintro H
  iapply wpStrongMono $$ H
  iintro %v H
  imodintro
  iapply HΦ v
  iexact H

/-- Rocq `wp_mono'` (a `Proper` instance; a theorem here). -/
theorem wpMono' (st : Stuckness) (i : Agent) (s : Athread) (Φ Φ' : Athread → IProp GF)
    (h : ∀ k, Φ k ⊢ Φ' k) : AxWp.wp st i s Φ ⊢ AxWp.wp st i s Φ' := wpMono st i s Φ Φ' h

/-- Rocq `wp_flip_mono'`. -/
theorem wpFlipMono' (st : Stuckness) (i : Agent) (s : Athread) (Φ Φ' : Athread → IProp GF)
    (h : ∀ k, Φ' k ⊢ Φ k) : AxWp.wp st i s Φ' ⊢ AxWp.wp st i s Φ := wpMono st i s Φ' Φ h

/-- Rocq `wp_proper`. -/
theorem wpProper (st : Stuckness) (i : Agent) (s : Athread) (Φ Φ' : Athread → IProp GF)
    (h : ∀ k, Φ k ⊣⊢ Φ' k) : AxWp.wp st i s Φ ⊣⊢ AxWp.wp st i s Φ' :=
  ⟨wpMono st i s Φ Φ' (fun k => (h k).1), wpMono st i s Φ' Φ (fun k => (h k).2)⟩

theorem wpFrameL (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF)
    (R : IProp GF) : R ∗ AxWp.wp st i s Φ ⊢ AxWp.wp st i s (fun k => iprop(R ∗ Φ k)) := by
  iintro ⟨HR, H⟩
  iapply wpStrongMono $$ H
  iintro %k H
  imodintro
  iframe HR H

theorem wpFrameR (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF)
    (R : IProp GF) : AxWp.wp st i s Φ ∗ R ⊢ AxWp.wp st i s (fun k => iprop(Φ k ∗ R)) := by
  iintro ⟨H, HR⟩
  iapply wpStrongMono $$ H
  iintro %k H
  imodintro
  iframe HR H

theorem wpFrameStepL (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF)
    (R : IProp GF) :
    iprop(|==> R) ∗ AxWp.wp st i s Φ ⊢ AxWp.wp st i s (fun k => iprop(R ∗ Φ k)) := by
  iintro ⟨Hu, H⟩
  iapply wpStrongMono $$ H
  iintro %k H
  imod Hu
  imodintro
  iframe Hu H

theorem wpFrameStepR (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF)
    (R : IProp GF) :
    AxWp.wp st i s Φ ∗ iprop(|==> R) ⊢ AxWp.wp st i s (fun k => iprop(Φ k ∗ R)) := by
  iintro ⟨H, Hu⟩
  iapply wpStrongMono $$ H
  iintro %k H
  imod Hu
  imodintro
  iframe Hu H

theorem wpWand (st : Stuckness) (i : Agent) (s : Athread) (Φ Ψ : Athread → IProp GF) :
    ⊢ AxWp.wp st i s Φ -∗ (∀ k, Φ k -∗ Ψ k) -∗ AxWp.wp st i s Ψ := by
  iintro Hwp H
  iapply wpStrongMono $$ Hwp
  iintro %k Hk
  imodintro
  iapply H $$ Hk

theorem wpWandL (st : Stuckness) (i : Agent) (s : Athread) (Φ Ψ : Athread → IProp GF) :
    iprop(∀ v, Φ v -∗ Ψ v) ∗ AxWp.wp st i s Φ ⊢ AxWp.wp st i s Ψ := by
  iintro ⟨H, Hwp⟩
  iapply wpWand $$ Hwp H

theorem wpWandR (st : Stuckness) (i : Agent) (s : Athread) (Φ Ψ : Athread → IProp GF) :
    AxWp.wp st i s Φ ∗ iprop(∀ v, Φ v -∗ Ψ v) ⊢ AxWp.wp st i s Ψ := by
  iintro ⟨Hwp, H⟩
  iapply wpWand $$ Hwp H

theorem wpFrameWandL (st : Stuckness) (i : Agent) (s : Athread) (Q : IProp GF)
    (Φ : Athread → IProp GF) :
    ⊢ Q ∗ AxWp.wp st i s (fun v => iprop(Q -∗ Φ v)) -∗ AxWp.wp st i s Φ := by
  iintro ⟨HQ, HWP⟩
  iapply wpWand $$ HWP
  iintro %v HΦ
  iapply HΦ $$ HQ

/-- Discharging the progress obligation from a graph-uniform fact. -/
theorem wpProgressIntro (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    (∀ GD, reducibleGd GD i s) →
    wpPreStepDef i (AxWp.wp st i) s Φ ⊢ AxWp.wp st i s Φ := by
  intro Hred
  rw [(wpUnfoldStep st i s Φ).to_eq]
  iintro H
  isplit
  · iapply progressOblOfPure st i s Hred
  · iexact H

end wp

section wpProofmode
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

instance frameWp (st : Stuckness) (p : Bool) (i : Agent) (s : Athread) (R : IProp GF)
    (Φ Ψ : Athread → IProp GF) [h : ∀ k, Frame p R (Φ k) (Ψ k)] :
    Frame p R (AxWp.wp st i s Φ) (AxWp.wp st i s Ψ) where
  frame := by
    refine (wpFrameL st i s Ψ iprop(□?p R)).trans ?_
    exact wpMono st i s _ _ (fun k => (h k).frame)

instance elimModalBupdWp (st : Stuckness) {io : InOut} (p : Bool) (i : Agent) (s : Athread)
    (P : IProp GF) (Φ : Athread → IProp GF) :
    ElimModal True p io false iprop(|==> P) P (AxWp.wp st i s Φ) (AxWp.wp st i s Φ) where
  elim_modal := by
    iintro %_ ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply bupdWp
    imod H
    imodintro
    iapply G $$ H

instance elimModalIupdWp (st : Stuckness) {io : InOut} (p : Bool) (i : Agent) (s : Athread)
    (P : IProp GF) (Φ : Athread → IProp GF) :
    ElimModal True p io false (interpMod P) P (AxWp.wp st i s Φ) (AxWp.wp st i s Φ) where
  elim_modal := by
    iintro %_ ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply iupdWp
    iapply interpModMono P (AxWp.wp st i s Φ) $$ G H

instance addModalBupdWp (st : Stuckness) (i : Agent) (s : Athread) (P : IProp GF)
    (Φ : Athread → IProp GF) : AddModal iprop(|==> P) P (AxWp.wp st i s Φ) where
  add_modal := by
    iintro ⟨H1, H2⟩
    iapply bupdWp
    imod H1
    imodintro
    iapply H2 $$ H1

end wpProofmode

/-! # 6. The checkpointed WP (port of AxSL `low/weakestpre_chk.v`) -/

section wpcDef
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
  [AxirisGChk GF]

/-- Rocq `wp_pre_chk`. -/
def wpPreChk (st : Stuckness) (i : Agent) (wp : Athread → (Athread → IProp GF) → IProp GF) :
    Athread → (Athread → IProp GF) → IProp GF :=
  fun s Φ =>
    if isTerminated s then postLifting Φ i s
    else iprop(postLifting (AxirisGChk.chk i) i s ∧ (progressObl st i s ∧ wpPreStepDef i wp s Φ))

instance wpPreChkContractive (st : Stuckness) (i : Agent) :
    OFE.Contractive (wpPreChk (GF := GF) st i) where
  distLater_dist {n wp wp'} Hwp := by
    intro s Φ
    unfold wpPreChk
    simp only [isTerminated, Bool.false_eq_true, ↓reduceIte]
    refine BI.and_ne.ne .rfl (BI.and_ne.ne .rfl ?_)
    exact AxWp.wpPreStepDefDist i wp wp' s Φ Φ n (fun m hm s' => Hwp m hm s' Φ)

/-- Rocq `wpc`: the checkpointed fixpoint. -/
def wpc (st : Stuckness) (i : Agent) : Athread → (Athread → IProp GF) → IProp GF :=
  fixpoint (wpPreChk (GF := GF) st i)

/-- The checkpoint obligation. -/
def chkObl (i : Agent) (s : Athread) : IProp GF :=
  if isTerminated s then iprop(True) else postLifting (AxirisGChk.chk i) i s

theorem chkOblTriv (i : Agent) (s : Athread) :
    (iprop(True) ⊢ AxirisGChk.chk (GF := GF) i s) → ⊢ chkObl (GF := GF) i s := by
  intro Hchk
  unfold chkObl
  simp only [isTerminated, Bool.false_eq_true, ↓reduceIte]
  exact postLiftingTrue _ i s Hchk

theorem chkOblMidInstr (i : Agent) (s : Athread) :
    ¬ AxWp.atBoundary s → ⊢ chkObl (GF := GF) i s := fun Hb =>
  chkOblTriv i s (AxirisGChk.chkMidInstr i s Hb)

end wpcDef

section wpc
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
  [AxirisGChk GF]

theorem wpcUnfold' (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpc st i s Φ ⊣⊢ wpPreChk st i (wpc st i) s Φ :=
  BI.equiv_iff.1 <| OFE.eq_dist_2 <|
    fun _n => (fixpoint_unfold (f := (wpPreChk (GF := GF) st i).toContractiveHom)).dist s Φ

/-- Lean-only (file-qualified): the unfolding at a hart state. -/
theorem AxWp.wpcUnfoldStep (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpc st i s Φ ⊣⊢ iprop(postLifting (AxirisGChk.chk i) i s ∧
      (progressObl st i s ∧ wpPreStepDef i (wpc st i) s Φ)) := by
  refine (wpcUnfold' st i s Φ).trans ?_
  unfold wpPreChk
  simp only [isTerminated, Bool.false_eq_true, ↓reduceIte]
  exact .rfl

theorem wpcStuckMono (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpc .NotStuck i s Φ ⊢ wpc .MaybeStuck i s Φ := by
  have h : ⊢ ∀ s Φ, wpc (GF := GF) .NotStuck i s Φ -∗ wpc .MaybeStuck i s Φ := by
    iloeb as IH
    iintro %s %Φ H
    rw [(AxWp.wpcUnfoldStep .NotStuck i s Φ).to_eq, (AxWp.wpcUnfoldStep .MaybeStuck i s Φ).to_eq]
    isplit
    · icases H with ⟨H, -⟩
      iexact H
    · isplit
      · unfold progressObl
        itrivial
      · icases H with ⟨-, -, H⟩
        iapply wpPreStepDefMono $$ [] H
        inext
        iintro %s' H'
        iapply IH $$ %s' %Φ H'
  iintro H
  iapply h $$ %s %Φ H

theorem wpcStuckWeaken (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpc st i s Φ ⊢ wpc .MaybeStuck i s Φ := by
  cases st with
  | NotStuck => exact wpcStuckMono i s Φ
  | MaybeStuck => exact .rfl

theorem wpcUnfold (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpc st i s Φ ⊣⊢ wpPreChk st i (wpc st i) s Φ := wpcUnfold' st i s Φ

/-- At any state, a `wpc` gives the postcondition (terminated) or the checkpoint (otherwise)
under the annotations. -/
theorem wpcPostOr (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpc st i s Φ ⊢
      if isTerminated s then postLifting Φ i s else postLifting (AxirisGChk.chk i) i s := by
  refine (AxWp.wpcUnfoldStep st i s Φ).1.trans ?_
  simp only [isTerminated, Bool.false_eq_true, ↓reduceIte]
  exact and_elim_l

theorem wpcChk (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpc st i s Φ ⊢ postLifting (AxirisGChk.chk i) i s := by
  refine (wpcPostOr st i s Φ).trans ?_
  simp only [isTerminated, Bool.false_eq_true, ↓reduceIte]
  exact .rfl

instance wpcNe (st : Stuckness) (i : Agent) (s : Athread) :
    OFE.NonExpansive (wpc (GF := GF) st i s) where
  ne {n Φ1 Φ2} HΦ := by
    induction n using Nat.strongRecOn generalizing s Φ1 Φ2 with
    | ind n IH =>
      rw [(AxWp.wpcUnfoldStep st i s Φ1).to_eq, (AxWp.wpcUnfoldStep st i s Φ2).to_eq]
      refine BI.and_ne.ne .rfl (BI.and_ne.ne .rfl ?_)
      exact AxWp.wpPreStepDefDist i _ _ s Φ1 Φ2 n
        (fun m hm s' => IH m hm s' (OFE.dist_lt HΦ hm))

theorem wpcTerminated' (st : Stuckness) (i : Agent) (Φ : Athread → IProp GF) (s : Athread) :
    isTerminated s = true → postLifting Φ i s ⊢ wpc st i s Φ := by
  intro Hs
  simp [isTerminated] at Hs

theorem wpcTerminatedInv' (st : Stuckness) (i : Agent) (Φ : Athread → IProp GF) (s : Athread) :
    isTerminated s = true → wpc st i s Φ ⊢ postLifting Φ i s := by
  intro Hs
  simp [isTerminated] at Hs

theorem wpcStrongMono (st : Stuckness) (i : Agent) (s : Athread) (Φ Ψ : Athread → IProp GF) :
    ⊢ wpc st i s Φ -∗ (∀ k, Φ k ==∗ Ψ k) -∗ wpc st i s Ψ := by
  have h : ⊢ ∀ s (Φ Ψ : Athread → IProp GF),
      wpc st i s Φ -∗ (∀ k, Φ k ==∗ Ψ k) -∗ wpc st i s Ψ := by
    iloeb as IH
    iintro %s %Φ %Ψ H HΦ
    rw [(AxWp.wpcUnfoldStep st i s Φ).to_eq, (AxWp.wpcUnfoldStep st i s Ψ).to_eq]
    isplit
    · icases H with ⟨H, -⟩
      iexact H
    · isplit
      · icases H with ⟨-, H, -⟩
        iexact H
      · icases H with ⟨-, -, H⟩
        iapply wpPreStepDefMono $$ [HΦ] H
        inext
        iintro %s' H'
        iapply IH $$ %s' %Φ %Ψ H' HΦ
  iintro H HΦ
  iapply h $$ %s %Φ %Ψ H HΦ

/-- Forgetting the checkpoints. -/
theorem wpcWp (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpc st i s Φ ⊢ AxWp.wp st i s Φ := by
  have h : ⊢ ∀ s (Φ : Athread → IProp GF), wpc st i s Φ -∗ AxWp.wp st i s Φ := by
    iloeb as IH
    iintro %s %Φ H
    rw [(AxWp.wpcUnfoldStep st i s Φ).to_eq, (wpUnfoldStep st i s Φ).to_eq]
    isplit
    · icases H with ⟨-, H, -⟩
      iexact H
    · icases H with ⟨-, -, H⟩
      iapply wpPreStepDefMono $$ [] H
      inext
      iintro %s' H'
      iapply IH $$ %s' %Φ H'
  iintro H
  iapply h $$ %s %Φ H

/-- Converse: with a trivial checkpoint a `wp` already is a `wpc`. -/
theorem wpWpc (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    (∀ s', iprop(True) ⊢ AxirisGChk.chk (GF := GF) i s') →
    AxWp.wp st i s Φ ⊢ wpc st i s Φ := by
  intro Hchk
  have h : ⊢ ∀ s (Φ : Athread → IProp GF), AxWp.wp st i s Φ -∗ wpc st i s Φ := by
    iloeb as IH
    iintro %s %Φ H
    rw [(AxWp.wpcUnfoldStep st i s Φ).to_eq, (wpUnfoldStep st i s Φ).to_eq]
    isplit
    · iapply postLiftingTrue _ i s (Hchk s)
    · isplit
      · icases H with ⟨H, -⟩
        iexact H
      · icases H with ⟨-, H⟩
        iapply wpPreStepDefMono $$ [] H
        inext
        iintro %s' H'
        iapply IH $$ %s' %Φ H'
  iintro H
  iapply h $$ %s %Φ H

theorem bupdWpc (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    iprop(|==> wpc st i s Φ) ⊢ wpc st i s Φ := by
  rw [(AxWp.wpcUnfoldStep st i s Φ).to_eq]
  iintro H
  isplit
  · iapply postLiftingInterpMod
    iapply interpModBupd
    imod H
    imodintro
    iapply interpModIntro
    icases H with ⟨H, -⟩
    iexact H
  isplit
  · iapply progressOblBupd
    imod H
    imodintro
    icases H with ⟨-, H, -⟩
    iexact H
  · iapply wpPreStepDefBupd
    imod H
    imodintro
    icases H with ⟨-, -, H⟩
    iexact H

theorem iupdWpc (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    interpMod (wpc st i s Φ) ⊢ wpc st i s Φ := by
  rw [(AxWp.wpcUnfoldStep st i s Φ).to_eq]
  iintro H
  isplit
  · iapply postLiftingInterpMod
    iapply interpModMono $$ [] H
    iintro ⟨H, -⟩
    iexact H
  isplit
  · iapply progressOblIupd
    iapply interpModMono $$ [] H
    iintro ⟨-, H, -⟩
    iexact H
  · iapply wpPreStepDefIupd
    iapply interpModMono $$ [] H
    iintro ⟨-, -, H⟩
    iexact H

theorem wpcBupd (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpc st i s (fun k => iprop(|==> Φ k)) ⊢ wpc st i s Φ := by
  iintro H
  iapply wpcStrongMono $$ H
  iintro %k H
  iexact H

theorem wpcStepBupd (st : Stuckness) (i : Agent) (s : Athread) (P : IProp GF)
    (Φ : Athread → IProp GF) :
    ⊢ (|==> P) -∗ wpc st i s (fun k => iprop(P ==∗ Φ k)) -∗ wpc st i s Φ := by
  iintro HP H
  iapply wpcStrongMono $$ H
  iintro %k H
  imod HP
  iapply H $$ HP

theorem wpcMono (st : Stuckness) (i : Agent) (s : Athread) (Φ Ψ : Athread → IProp GF)
    (HΦ : ∀ k, Φ k ⊢ Ψ k) : wpc st i s Φ ⊢ wpc st i s Ψ := by
  iintro H
  iapply wpcStrongMono $$ H
  iintro %v H
  imodintro
  iapply HΦ v
  iexact H

/-- Rocq `wpc_mono'` (a `Proper` instance; a theorem here). -/
theorem wpcMono' (st : Stuckness) (i : Agent) (s : Athread) (Φ Φ' : Athread → IProp GF)
    (h : ∀ k, Φ k ⊢ Φ' k) : wpc st i s Φ ⊢ wpc st i s Φ' := wpcMono st i s Φ Φ' h

/-- Rocq `wpc_proper`. -/
theorem wpcProper (st : Stuckness) (i : Agent) (s : Athread) (Φ Φ' : Athread → IProp GF)
    (h : ∀ k, Φ k ⊣⊢ Φ' k) : wpc st i s Φ ⊣⊢ wpc st i s Φ' :=
  ⟨wpcMono st i s Φ Φ' (fun k => (h k).1), wpcMono st i s Φ' Φ (fun k => (h k).2)⟩

theorem wpcFrameL (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF)
    (R : IProp GF) : R ∗ wpc st i s Φ ⊢ wpc st i s (fun k => iprop(R ∗ Φ k)) := by
  iintro ⟨HR, H⟩
  iapply wpcStrongMono $$ H
  iintro %k H
  imodintro
  iframe HR H

theorem wpcFrameR (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF)
    (R : IProp GF) : wpc st i s Φ ∗ R ⊢ wpc st i s (fun k => iprop(Φ k ∗ R)) := by
  iintro ⟨H, HR⟩
  iapply wpcStrongMono $$ H
  iintro %k H
  imodintro
  iframe HR H

theorem wpcWand (st : Stuckness) (i : Agent) (s : Athread) (Φ Ψ : Athread → IProp GF) :
    ⊢ wpc st i s Φ -∗ (∀ k, Φ k -∗ Ψ k) -∗ wpc st i s Ψ := by
  iintro Hwp H
  iapply wpcStrongMono $$ Hwp
  iintro %k Hk
  imodintro
  iapply H $$ Hk

theorem wpcFrameWandL (st : Stuckness) (i : Agent) (s : Athread) (Q : IProp GF)
    (Φ : Athread → IProp GF) :
    ⊢ Q ∗ wpc st i s (fun v => iprop(Q -∗ Φ v)) -∗ wpc st i s Φ := by
  iintro ⟨HQ, HWP⟩
  iapply wpcWand $$ HWP
  iintro %v HΦ
  iapply HΦ $$ HQ

instance frameWpc (st : Stuckness) (p : Bool) (i : Agent) (s : Athread) (R : IProp GF)
    (Φ Ψ : Athread → IProp GF) [h : ∀ k, Frame p R (Φ k) (Ψ k)] :
    Frame p R (wpc st i s Φ) (wpc st i s Ψ) where
  frame := by
    refine (wpcFrameL st i s Ψ iprop(□?p R)).trans ?_
    exact wpcMono st i s _ _ (fun k => (h k).frame)

instance elimModalBupdWpc (st : Stuckness) {io : InOut} (p : Bool) (i : Agent) (s : Athread)
    (P : IProp GF) (Φ : Athread → IProp GF) :
    ElimModal True p io false iprop(|==> P) P (wpc st i s Φ) (wpc st i s Φ) where
  elim_modal := by
    iintro %_ ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply bupdWpc
    imod H
    imodintro
    iapply G $$ H

instance elimModalIupdWpc (st : Stuckness) {io : InOut} (p : Bool) (i : Agent) (s : Athread)
    (P : IProp GF) (Φ : Athread → IProp GF) :
    ElimModal True p io false (interpMod P) P (wpc st i s Φ) (wpc st i s Φ) where
  elim_modal := by
    iintro %_ ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply iupdWpc
    iapply interpModMono P (wpc st i s Φ) $$ G H

end wpc

/-! # 7. Non-vacuity: the instantiation skeleton -/

class AxgraphG (GF : BundledGFunctors) where
  axgraphInG : ElemG GF (constOF (Agree (DiscreteO Gdexec)))

attribute [reducible, instance] AxgraphG.axgraphInG

section graphAgree
variable {GF : BundledGFunctors} [AxgraphG GF]

def graphAgree (γg : GName) (GD : Gdexec) : IProp GF :=
  iOwn (E := AxgraphG.axgraphInG) γg (toAgree (DiscreteO.mk GD))

instance graphAgreePersistent (γg : GName) (GD : Gdexec) :
    Persistent (graphAgree (GF := GF) γg GD) := by
  unfold graphAgree; infer_instance

theorem graphAgreeAgree (γg : GName) (GD GD' : Gdexec) :
    ⊢ graphAgree (GF := GF) γg GD -∗ graphAgree γg GD' -∗ ⌜GD = GD'⌝ := by
  unfold graphAgree
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %hv
  ipureintro
  have h := toAgree_op_valid_iff_eq.mp hv
  exact congrArg DiscreteO.car h

theorem graphAgreeAlloc (GD : Gdexec) : ⊢ |==> ∃ γg, graphAgree (GF := GF) γg GD := by
  unfold graphAgree
  exact iOwn_alloc (E := AxgraphG.axgraphInG) _ Agree.toAgree_valid

end graphAgree

section skeleton
variable {GF : BundledGFunctors} [AxannotGS GF] [AxgraphG GF] (γg : GName)
  (Φp : Gdexec → Geid → IProp GF)

def protInterp (GD : Gdexec) (_ : Unit) (s : GSet Geid) : IProp GF :=
  iprop([∗set] e ∈ s, Φp GD e)

/-- The interface class at the REAL annotation resource of §2. -/
@[reducible] def skelAxirisG : AxirisG GF where
  annotInterp := AxAnnot.annotInterp
  gconstInterp := graphAgree γg
  obSt := Unit
  obStInterp := protInterp Φp
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

/-- The annotation laws, at the class's interpretation. -/
theorem skelAnnotSplit (e : Geid) (P Q : IProp GF) :
    ⊢ AxAnnot.annotOwn e iprop(P ∗ Q) -∗
      ∀ na, AxirisG.annotInterp (self := skelAxirisG γg Φp) na ==∗
        (AxAnnot.annotOwn e P ∗ AxAnnot.annotOwn e Q) ∗
        AxirisG.annotInterp (self := skelAxirisG γg Φp) na :=
  annotSplit e P Q

theorem skelAnnotMerge (e : Geid) (P Q : IProp GF) :
    ⊢ AxAnnot.annotOwn e P -∗ AxAnnot.annotOwn e Q -∗
      ∀ na, AxirisG.annotInterp (self := skelAxirisG γg Φp) na ==∗
        AxAnnot.annotOwn e iprop(P ∗ Q) ∗ AxirisG.annotInterp (self := skelAxirisG γg Φp) na :=
  annotMerge e P Q

/-- Allocation at the current position: the position is not yet annotated. -/
theorem annotAllocAtProgress (GD : Gdexec) (i : Agent) (k : Nat) (na : Mea GF) (P : IProp GF) :
    ⊢ naAtProgress GD i k na ∗ AxirisG.annotInterp (self := skelAxirisG γg Φp) na ==∗
      AxirisG.annotInterp (self := skelAxirisG γg Φp) (insert na (i, k) P) ∗
      AxAnnot.annotOwn (i, k) P := by
  iintro ⟨Hpg, Hna⟩
  ihave %Hnin := naAtProgressNotElemOf GD i k na $$ Hpg
  iapply annotAlloc na (i, k) P Hnin
  iexact Hna

/-- The protocol interpretation splits off a fresh event. -/
theorem protInterpInsert (GD : Gdexec) (σ : Unit) (e : Geid) (s : GSet Geid) :
    e ∉ s →
    AxirisG.obStInterp (self := skelAxirisG γg Φp) GD σ (({e} : GSet Geid) ∪ s) ⊣⊢
      Φp GD e ∗ AxirisG.obStInterp (self := skelAxirisG γg Φp) GD σ s := by
  intro Hnin
  show protInterp Φp GD σ (({e} : GSet Geid) ∪ s) ⊣⊢ Φp GD e ∗ protInterp Φp GD σ s
  unfold protInterp
  have hdisj : ({e} : GSet Geid) ## s := by
    rw [elemOfDisjoint]
    intro x hx hx'
    rw [elemOfSingleton.1 hx] at hx'
    exact Hnin hx'
  refine (BigSepS.bigSepS_union hdisj).trans ?_
  exact BI.sep_congr BigSepS.bigSepS_singleton .rfl

/-- A flow equation with no incoming flow and no protocol content to deposit: `R := True` at
any event. -/
theorem flowEqDynTriv {hlc : HasLC} [InvGS_gen hlc GF] (GD : Gdexec) (e : Geid)
    (s0 : GSet Geid) :
    (⊢ Φp GD e) →
    ⊢ @flowEqDyn hlc GF _ (skelAxirisG γg Φp) GD e s0 ∅ iprop(True) := by
  intro HΦ
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob _
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl
  · iapply (protInterpInsert γg Φp GD σ e sOb Hnin).2
    iframe Hob
    iapply HΦ
  · itrivial

/-- `wpSkipStep` closes from `Ψ` alone, under this concrete instance (the Rocq gotcha: the
goal's later is introduced by `later_intro`, not `inext`, so the context is not touched). -/
theorem skelWpSkipStepOfPsi (GD : Gdexec) (i : Agent) (k' : Nat) (Ψ : IProp GF) :
    Ψ ⊢ @wpSkipStep GF (skelAxirisG γg Φp) GD i k' Ψ := by
  unfold wpSkipStep
  iintro HΨ %na Hna
  imodintro
  iapply BI.later_intro
  imodintro
  iexists ()
  iframe Hna HΨ
  show ⊢ iprop(True)
  itrivial

end skeleton

end Weak
