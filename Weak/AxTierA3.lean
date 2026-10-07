/-
Weak: **`tierAAdequacyAnnGmo` / `tierAAdequacyAnnDev2`** — `AxTierA2.tierAAdequacyAnn` with its
scheduler-policy premises WEAKENED from "`sPol`/`lobp` ⊆ `gobCatFlow`-predecessors" to
"`sPol`/`lobp` ⊆ GMO-predecessors" (and, as a corollary, to deviation-2's `flowDev2`).

Rocq: `iris/AxTierA3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Phase 2 consumes the policy premises only through `axpolWfL GD sst.sProc` ("every handed-out
predecessor is PROCESSED before `e`"), which is all `adequacyOrdL` needs.  Tier A runs a
GATE-FREE schedule (`sst.sEverD = ∅`), so `schedCorrect`'s fourth clause
(`¬ D e1 → gmoLt e1 e2 → ltIn proc e1 e2`) orders EVERY gmo-earlier event first; hence any
gmo-predecessor handout satisfies `axpolWfL` (§2 `gatefreeAxpolWfProc`).  (For a deferring run
this would fail.)  §1 the flow relations (`flowDev2` = gob flow edges ∪ same-hart same-byte
po-earlier gmo-earlier edges) and the sanity implications; §3 `schedProcAdequatePol` =
`schedProcAdequate` with `axpolWfL` as premise; §4 the core / wrapper copies of AxTierA2's with
only the phase-2 call replaced, and the two corollaries.

## Deviations from Rocq

1. NAMES: camelCase (map below); no name of this file is in `notes/weak-port-dupnames.json`;
   no Lean-only helpers.  Vocabulary as AxTierA2 (deviation 1).
2. O2 STAGE C (as AxTierA2 deviation 2): the section parameter `T` is gone; `tierAAstep GD nm i`
   and `tierAWpd GD N obSt0 obStInterp0 nm …` are AxTierA2's.
3. `AxGA3` (a Rocq `Local Instance` := `AxGA2 … nm`) is `axGA3`, a `@[reducible] def` equal to
   `axGA2`; the core installs it with `letI` (AxTierA2 deviation 3).
4. `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` in §3/§4's core (as AxTierA2
   deviation 4); the wrappers' soundness runs at `.hasNoLC` and their `Hwp` quantifies
   `[InvGS_gen .hasNoLC GF]`.  Wand chains are `⊢ A -∗ B -∗ …`.
5. AxSchedGD's Lean `schedProcAdequate` threads an (unconsumed) `Hdefer`; `schedProcAdequatePol`
   has none, exactly as Rocq.

**Rocq → Lean name map.**  `flow_dev2` `flowDev2`, `gob_cat_flow_dev2` `gobCatFlowDev2`,
`flow_dev2_gmo` `flowDev2Gmo`, `pol_sub_flow_to_dev2` `polSubFlowToDev2`, `pol_sub_dev2_to_gmo`
`polSubDev2ToGmo`, `gatefree_axpol_wf_proc` `gatefreeAxpolWfProc`, `sched_proc_adequate_pol`
`schedProcAdequatePol`, `AxGA3` `axGA3`, `tierA_adequacy_ann_core_gmo` `tierAAdequacyAnnCoreGmo`,
`tierA_adequacy_ann_gmo` `tierAAdequacyAnnGmo`, `tierA_adequacy_ann_dev2` `tierAAdequacyAnnDev2`,
`tierA_adequacy_ann_from_dev2` `tierAAdequacyAnnFromDev2`.

**Dropped:** only the three `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxTierA2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. The flow relations -/

/-- Deviation 2: the gob flow edges, plus same-hart same-byte po-earlier edges that are ALSO
gmo-earlier. -/
def flowDev2 (GD : Gdexec) (e' e : Geid) : Prop :=
  gobCatFlow GD e' e ∨ (gpoloc GD.gdG e' e ∧ gmoLt GD.gdG e' e)

theorem gobCatFlowDev2 (GD : Gdexec) (e' e : Geid) : gobCatFlow GD e' e → flowDev2 GD e' e :=
  .inl

theorem flowDev2Gmo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (e' e : Geid) :
    flowDev2 GD e' e → gmoLt GD.gdG e' e := by
  rintro (Hf | ⟨_, Hlt⟩)
  · exact obCatSubGmo GD e' e Hcons (gobCatFlowSub GD e' e Hf)
  · exact Hlt

/-- SANITY: AxTierA2's premises imply the new ones. -/
theorem polSubFlowToDev2 [Axpol] (GD : Gdexec)
    (HsPolSub : ∀ e e', e' ∈ Axpol.sPol GD e → gobCatFlow GD e' e)
    (HlobpSub : ∀ e e', e' ∈ Axpol.lobp GD e → gobCatFlow GD e' e) :
    (∀ e e', e' ∈ Axpol.sPol GD e → flowDev2 GD e' e) ∧
    (∀ e e', e' ∈ Axpol.lobp GD e → flowDev2 GD e' e) :=
  ⟨fun e e' He => gobCatFlowDev2 GD e' e (HsPolSub e e' He),
   fun e e' He => gobCatFlowDev2 GD e' e (HlobpSub e e' He)⟩

theorem polSubDev2ToGmo [Axpol] (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (HsPolSub : ∀ e e', e' ∈ Axpol.sPol GD e → flowDev2 GD e' e)
    (HlobpSub : ∀ e e', e' ∈ Axpol.lobp GD e → flowDev2 GD e' e) :
    (∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e) ∧
    (∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e) :=
  ⟨fun e e' He => flowDev2Gmo GD Hcons e' e (HsPolSub e e' He),
   fun e e' He => flowDev2Gmo GD Hcons e' e (HlobpSub e e' He)⟩

/-! # 2. The consumed property, discharged from gmo on a gate-free run -/

theorem gatefreeAxpolWfProc [Axpol] (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hgatefree : st.sEverD = ∅)
    (HsPolGmo : ∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e)
    (HlobpGmo : ∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e) :
    axpolWfL GD st.sProc := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  obtain ⟨_, HndP, _, Hord, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  have Hgmo : ∀ n e e', st.sProc[n]? = some e → gmoLt GD.gdG e' e →
      e' ∈ takeL st.sProc n := by
    intro n e e' Hn Hlt
    refine ltInTakeL _ n e e' HndP Hn (Hord e' e ?_ Hlt)
    intro Hin
    rw [Hgatefree] at Hin
    exact notElemOfEmpty Hin
  intro n e Hn
  exact ⟨fun e' He' => Hgmo n e e' Hn (HsPolGmo e e' He'),
    fun e' He' => Hgmo n e e' Hn (HlobpGmo e e' He')⟩

/-! # 3. `schedProcAdequate` with the consumed property as its premise -/

section ProcAdequatePol
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem schedProcAdequatePol (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hpol : axpolWfL GD st.sProc)
    (na : Mea GF) (ea : Sra GF)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList st.sProc : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ordEaTodoL GD ea na st.sProc 0 -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[st.sProc.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList st.sProc) ∗
          [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  obtain ⟨Hmemiff, HndP, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  have Hperm : st.sProc.Perm GD.gdG.gxGmo := NoDup_Permutation HndP HGw.1 Hmemiff
  exact adequacyOrdL GD Hcons st.sProc Hperm Hpol na ea HdomEq Hdom HeaLob σ0

end ProcAdequatePol

/-! # 4. The generalized Tier A adequacy -/

section fixed
variable {GF : BundledGFunctors.{0,0,0}}

/-- Rocq `AxGA3` (a local instance): `axGA2` at `nm`. -/
@[reducible] def axGA3 [AxannotGS GF] (GD : Gdexec) (N obSt0 : Type)
    (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) : AxirisG GF :=
  axGA2 GD N obSt0 obStInterp0 nm

theorem tierAAdequacyAnnCoreGmo {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] [Axpol]
    (GD : Gdexec) (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N → Agent → IProp GF) (nm : N)
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (harts : List Agent) (Hnd : harts.Nodup)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ i, i ∈ harts → nsteps (astepAnyNfGv GD i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp : ⊢ ([∗list] i ∈ harts, init nm i) -∗
      [∗list] i ∈ harts,
        tierAWpd GD N obSt0 obStInterp0 nm (s0 i) .MaybeStuck i (fun s => iprop(⌜post i s⌝)))
    (sst : Sstate) (HrunSched : rtc (schedStep GD.gdG) sst0 sst)
    (Hfull : sst.sN = GD.gdG.gxGmo.length) (Hdone : sst.sD = ∅)
    (Hgatefree : sst.sEverD = ∅)
    (HsPolGmo : ∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e)
    (HlobpGmo : ∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e)
    (Hcov : (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) :
        GSet Geid) = LawfulSet.ofList sst.sProc)
    (σ0 : obSt0) (i : Agent) (Hi : i ∈ harts) :
    ⊢ AxAnnot.annotInterp (∅ : Mea GF) -∗ obStInterp0 nm GD σ0 ∅ -∗
      ([∗list] i ∈ harts, init nm i) -∗
      |={⊤}[∅]▷=>^[(harts.map n).sum + (1 + (sst.sProc.length + 1))] ⌜post i (sN i)⌝ := by
  letI axG : AxirisG GF := axGA3 GD N obSt0 obStInterp0 nm
  have Hgc : ⊢ AxirisG.gconstInterp GD := axGA2Gconst GD N obSt0 obStInterp0 nm
  have Hloc : ∀ j : Agent, ⊢ ∃ ls, AxirisG.localInterp (GF := GF) GD j 0 ls := fun _ => by
    iexists ()
    show ⊢ iprop(True)
    itrivial
  have Hbig0 : ([∗list] j ∈ harts,
        tierAWpd GD N obSt0 obStInterp0 nm (s0 j) .MaybeStuck j (fun s => iprop(⌜post j s⌝))) ⊢
      [∗list] j ∈ harts, (∃ ls, AxirisG.localInterp (GF := GF) GD j 0 ls) ∗
        wpd .MaybeStuck j (s0 j) (fun s => iprop(⌜post j s⌝)) :=
    BigSepL.bigSepL_mono_of_forall fun {_ j} => AxTierA2.wpdWithLocal GD j _ (Hloc j)
  have Hphase1 := wpdHartsNsteps (GF := GF) GD Hwf Hcons .MaybeStuck harts Hnd s0 sN n Hrun Hk0
    (fun j s => (iprop(⌜post j s⌝) : IProp GF))
  have HI := invRtc GD.gdG (schedHGwf GD Hcons) (schedHCat6gmo GD Hcons) sst HrunSched
  have Hndp := HI.invNodup
  have Hfmap : (harts.map fun j => eidsBefore GD j (sN j).atK) =
      harts.map fun j => eidsBefore GD j (AxOpsem.grow GD j).length :=
    List.map_congr_left fun j Hj => by rw [Hend j Hj]
  have Hpol := gatefreeAxpolWfProc GD Hcons sst HrunSched Hfull Hdone Hgatefree HsPolGmo HlobpGmo
  have Hpost := fun ls : AxirisG.logTsT GF => wpdPostAtRowEnd (GF := GF) .MaybeStuck i (sN i)
    (fun s => (iprop(⌜post i s⌝) : IProp GF)) GD ls (Hend i Hi) Hcons
  iintro Hannot0 Hob0 Hinit
  ihave HWPall := Hwp $$ Hinit
  ihave Hbig := Hbig0 $$ HWPall
  ihave #Hg := Hgc
  ihave Hp1 := Hphase1 $$ Hannot0 Hg Hbig
  ihave Hp1 := wpdStepsNStepFupdN _ _ $$ Hp1
  iapply step_fupdN_add.2
  iapply step_fupdN_wand $$ Hp1
  iintro H
  rw [show 1 + (sst.sProc.length + 1) = (sst.sProc.length + 1) + 1 by omega,
    AxTierA2.stepFupdNSucc]
  imod H with ⟨%na, %ea, %Hdomna, Hannot, Hea, Hbig2⟩
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  ihave Hhart := (BigSepL.bigSepL_mem Hi) $$ Hbig2
  icases Hhart with ⟨⟨%lsi, Hloci⟩, HWPi⟩
  ihave Hpl := Hpost lsi $$ Hg Hloci HWPi
  have Hdomeq : (FiniteMap.dom_set na : GSet Geid) = LawfulSet.ofList sst.sProc := by
    rw [Hdomna, Hfmap]
    exact Hcov
  ihave Hconn := (ordEaTodoLOfEaLocalWf GD ea na sst.sProc Hndp Hdomeq.symm) $$ Hea
  icases Hconn with ⟨%Hdom_eq2, %Hea_lob2, Htodo⟩
  have Hdom_sub : (LawfulSet.ofList sst.sProc : GSet Geid) ⊆ FiniteMap.dom_set na := by
    rw [Hdomeq]
  ihave Hphase2 := (schedProcAdequatePol GD Hcons sst HrunSched Hfull Hdone Hpol na ea
    Hdom_eq2 Hdom_sub Hea_lob2 σ0) $$ Htodo Hob0
  iapply step_fupdN_add.2
  iapply step_fupdN_wand $$ Hphase2
  iintro ⟨%σ, -, Hrbag⟩
  rw [← Hdomeq] at *
  ihave HRi := (AxTierA2.bagToHart na i) $$ Hrbag
  rw [AxTierA2.stepFupdNSucc, AxTierA2.stepFupdNZero]
  iunfold postLifting at Hpl
  imod Hpl $$ %na Hannot with ⟨-, Hwand⟩
  ihave HΦ := Hwand $$ HRi
  iapply step_fupd_fupd.2
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  imod HΦ with %Hp
  imodintro
  ipureintro
  exact Hp

end fixed

section wrapper
variable {GF : BundledGFunctors.{0,0,0}}

/-- The Prop-level wrapper, premises bounded by GMO (not gob). -/
theorem tierAAdequacyAnnGmo [InvGpreS GF] [AxannotG GF] [Axpol]
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
  obtain ⟨sst, HrunSched, Hproc, Hfull, Hdone, Hgatefree⟩ := schedGatefreeRun GD
  have Hcov : (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) :
      GSet Geid) = LawfulSet.ofList sst.sProc := by
    rw [Hproc]
    exact eidsBeforeCov GD harts (schedHGwf GD Hcons) Hharts
  intro i Hi
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := .hasNoLC)
    (1 + ((harts.map n).sum + (1 + (sst.sProc.length + 1)))) 0 (fun Hinv => ?_)
  rw [show 1 + ((harts.map n).sum + (1 + (sst.sProc.length + 1))) =
      ((harts.map n).sum + (1 + (sst.sProc.length + 1))) + 1 by omega,
    AxTierA2.stepFupdNSucc]
  iintro _
  imod (annotInterpAlloc (GF := GF)) with ⟨%γ, Hannot0⟩
  imod HobAlloc with ⟨%nm, %σ0, Hob0, Hinit⟩
  ihave Hcore := (@tierAAdequacyAnnCoreGmo GF .hasNoLC Hinv { axannotName := γ } _ GD N obSt0
    obStInterp0 init nm Hwf Hcons harts Hnd s0 sN n
    (fun j Hj => Hrun { axannotName := γ } nm j Hj) Hk0 Hend post
    (@Hwp Hinv { axannotName := γ } nm)
    sst HrunSched Hfull Hdone Hgatefree HsPolGmo HlobpGmo Hcov σ0 i Hi) $$ Hannot0 Hob0 Hinit
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  iexact Hcore

/-- THE TARGET: premises weakened to deviation-2's `flowDev2`. -/
theorem tierAAdequacyAnnDev2 [InvGpreS GF] [AxannotG GF] [Axpol]
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
    (HsPolSub : ∀ e e', e' ∈ Axpol.sPol GD e → flowDev2 GD e' e)
    (HlobpSub : ∀ e e', e' ∈ Axpol.lobp GD e → flowDev2 GD e' e) :
    ∀ i, i ∈ harts → post i (sN i) :=
  have H := polSubDev2ToGmo GD Hcons HsPolSub HlobpSub
  tierAAdequacyAnnGmo GD N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts s0 sN n Hrun Hk0
    Hend post Hwp HobAlloc H.1 H.2

/-- `AxTierA2.tierAAdequacyAnn` re-derived from the new theorem. -/
theorem tierAAdequacyAnnFromDev2 [InvGpreS GF] [AxannotG GF] [Axpol]
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
    (HsPolSub : ∀ e e', e' ∈ Axpol.sPol GD e → gobCatFlow GD e' e)
    (HlobpSub : ∀ e e', e' ∈ Axpol.lobp GD e → gobCatFlow GD e' e) :
    ∀ i, i ∈ harts → post i (sN i) :=
  have H := polSubFlowToDev2 GD HsPolSub HlobpSub
  tierAAdequacyAnnDev2 GD N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts s0 sN n Hrun Hk0
    Hend post Hwp HobAlloc H.1 H.2

end wrapper

end Weak
