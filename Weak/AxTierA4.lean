/-
Weak: **Tier A adequacy over an ARBITRARY completed scheduler run** (`tierAAdequacyAnnCoreRun` /
`tierAAdequacyAnnRun`), the "gated" policy lemma `schedAxpolWfProcGated`, and the
store-forwarding OBSTRUCTION of the current scheduler (`schedNoFwd` / `fwdPolUnrealizable`).

Rocq: `iris/AxTierA4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

VERDICT: THE RUN RESTRICTION IS IRRELEVANT; THE REAL RESTRICTION IS ON POLICIES.  (1) Phase 2
needs exactly ONE completed run `st` with `axpolWfL GD st.sProc` (the only policy fact
`adequacyOrdL` consumes; `schedProcAdequatePol`); nothing in the client's obligations mentions a
run, so `tierAAdequacyAnnRun` takes "some completed run satisfies `axpolWfL`" as its only
scheduler premise.  (2) The gate-free run always exists (`schedGatefreeRun`) and satisfies
`axpolWfL` iff every handout is gmo-earlier; hence `tierAAdequacyAnnGmo` (re-derived here as
`tierAAdequacyAnnGmoOfRun`) already holds for every `GD`.  (3) The gated premise
`polGated GD e' e := (gmoLt e' e ∧ ¬ gplainR e') ∨ flowDev2 GD e' e` is STRONGER than
gmo-boundedness (`polGatedGmo`), so `tierAAdequacyAnnGated` is a strict weakening of the gmo
theorem (proved both ways).  Its genuine content is `schedAxpolWfProcGated`: EVERY completed run
satisfies `axpolWfL` for gated policies (only plain reads are ever deferred — `invEverDR` — so a
non-plain-read gmo-predecessor is ordered first by `invOrdFresh`; the `flowDev2` arm is
AxSchedSH's).  (4) A deferring run is needed ONLY for policies handing out a gmo-LATER event.
Store forwarding (the reload `e` a read, its handout `e'` a po-earlier same-hart WRITE with
`gmoLt e e'`) is UNREALIZABLE by the current scheduler on ANY run: `schedNoFwd` and
`fwdPolUnrealizable`.  OPEN ITEM for AxSchedFwd: relax `stepCommit`'s `Hclear` (see the Rocq
header).  EPILOGUE NOTE (Rocq, unchanged): `AxLdspWpd.ldspOwnOk`'s prefix handout violates
`polGated` but satisfies the gmo premise, so the epilogue is fine under `tierAAdequacyAnnGmo`.

## Deviations from Rocq

1. NAMES: camelCase (map below); no name of this file is in `notes/weak-port-dupnames.json`; no
   Lean-only helpers.  Vocabulary as AxTierA2/AxTierA3/AxSchedSH.
2. O2 STAGE C (as AxTierA2/A3): the section parameter `T` is gone.
3. `AxGA4` (a Rocq `Local Instance` := `AxGA2 … nm`) is `axGA4`, a `@[reducible] def` equal to
   `axGA2`; the core installs it with `letI` (as AxTierA3's `axGA3`).
4. `tierAAdequacyAnnCoreRun` is stated for `[InvGS_gen hlc GF]`, any `hlc` (Rocq: `HasNoLc`),
   as AxTierA3's core; the wrappers' soundness runs at `.hasNoLC` and their `Hwp` quantifies
   `[InvGS_gen .hasNoLC GF]`.  Wand chains are `⊢ A -∗ B -∗ …`.  The core's proof follows
   AxTierA3's (the Rocq big_sepM steps are `AxTierA2.bagToHart`).
5. The Rocq section `NoFwd` (context `G Hgwf Hcat6gmo`) is unfolded: `InvNFStep`, `schedOrdNf`,
   `schedNoFwd` take `G Hgwf Hcat6gmo` explicitly; `InvNF` takes `G` only.

**Rocq → Lean name map.**  `gplain_r` `gplainR`, `gw_not_plain_r` `gwNotPlainR`, `pol_gated`
`polGated`, `pol_gated_gmo` `polGatedGmo`, `sched_axpol_wf_proc_gated` `schedAxpolWfProcGated`,
`InvNF` `InvNF`, `InvNF_step` `InvNFStep`, `sched_ord_nf` `schedOrdNf`, `sched_no_fwd`
`schedNoFwd`, `fwd_pol_unrealizable` `fwdPolUnrealizable`, `AxGA4` `axGA4`,
`tierA_adequacy_ann_core_run` `tierAAdequacyAnnCoreRun`, `tierA_adequacy_ann_run`
`tierAAdequacyAnnRun`, `tierA_adequacy_ann_gated` `tierAAdequacyAnnGated`,
`tierA_adequacy_ann_gmo_of_run` `tierAAdequacyAnnGmoOfRun`, `tierA_adequacy_ann_gated_of_gmo`
`tierAAdequacyAnnGatedOfGmo`.

**Dropped:** only the six `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxTierA3
import Weak.AxSchedSH

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. Plain reads (exactly the deferrable events) and the gated premise -/

def gplainR (G : Gexec) (e : Geid) : Prop :=
  ∃ l, gxLbl G e = some l ∧ lbIsR l = true ∧ lbIsW l = false

theorem gwNotPlainR (G : Gexec) (e : Geid) : glblIs G e lbIsW → ¬ gplainR G e := by
  rintro ⟨l, Hl, Hw⟩ ⟨l', Hl', _, Hw'⟩
  rw [Hl] at Hl'
  cases Hl'
  rw [Hw] at Hw'
  cases Hw'

def polGated (GD : Gdexec) (e' e : Geid) : Prop :=
  (gmoLt GD.gdG e' e ∧ ¬ gplainR GD.gdG e') ∨ flowDev2 GD e' e

theorem polGatedGmo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (e' e : Geid) :
    polGated GD e' e → gmoLt GD.gdG e' e := by
  rintro (⟨H, _⟩ | H)
  · exact H
  · exact flowDev2Gmo GD Hcons e' e H

/-! # 2. The policy lemma: ANY completed run -/

theorem schedAxpolWfProcGated [Axpol] (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (HsPolOk : ∀ e e', e' ∈ Axpol.sPol GD e → polGated GD e' e)
    (HlobpOk : ∀ e e', e' ∈ Axpol.lobp GD e → polGated GD e' e) :
    axpolWfL GD st.sProc := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  have HI := invRtc GD.gdG HGw HC6 st Hrun
  have HI2 := Inv2Rtc GD Hcons st Hrun
  obtain ⟨Hmem, HndP, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  have Hg : ∀ n e e', st.sProc[n]? = some e → polGated GD e' e →
      e' ∈ takeL st.sProc n := by
    intro n e e' Hn Hf
    refine ltInTakeL st.sProc n e e' HndP Hn ?_
    rcases Hf with ⟨Hlt, Hnp⟩ | Hf | ⟨Hpl, Hlt⟩
    · have HnD : e' ∉ st.sEverD := fun HeD => Hnp (HI.invEverDR e' HeD)
      obtain ⟨Hg1, _, Hpos⟩ := Hlt
      exact HI.invOrdFresh e' e ((Hmem e').2 Hg1) (elem_of_list_lookup_2 Hn) HnD Hpos
    · exact gobCatFlowOrd GD Hcons st HI HI2 Hmem e' e Hf
    · exact schedOrdShFull GD.gdG HGw HC6 st Hrun Hfull Hdone e' e Hpl.1 Hlt
  intro n e Hn
  exact ⟨fun e' He' => Hg n e e' Hn (HsPolOk e e' He'),
    fun e' He' => Hg n e e' Hn (HlobpOk e e' He')⟩

/-! # 3. The store-forwarding obstruction -/

/-- Same hart, gmo-earlier, the later one never deferred ⇒ processed in gmo order. -/
def InvNF (G : Gexec) (st : Sstate) : Prop :=
  ∀ e1 e2, e1.1 = e2.1 → gmoLt G e1 e2 → e2 ∈ st.sProc → e2 ∉ st.sEverD →
    ltIn st.sProc e1 e2

theorem InvNFStep (G : Gexec) (Hgwf : gwf G) (Hcat6gmo : gppoCat6Gmo G) (st st' : Sstate) :
    AxSched.Inv G st → InvNF G st → schedStep G st st' → InvNF G st' := by
  intro HI HInf Hstep
  cases Hstep with
  | stepCommit n D everD proc e He Hclear =>
    have Hpart : ∀ x, x ∈ visited G n ↔ x ∈ proc ∨ x ∈ AxSched.domG D := HI.invPart
    obtain ⟨Hfp, _⟩ := freshAt G Hgwf Hcat6gmo _ HI e He
    have Hnd' : (proc ++ [e]).Nodup := by
      refine NoDup_app.2 ⟨HI.invNodup, fun x hx hx' => ?_, NoDup_singleton⟩
      rw [List.mem_singleton] at hx'
      rw [hx'] at hx
      exact Hfp hx
    intro e1 e2 Hh Hlt He2 HnD
    change e2 ∈ proc ++ [e] at He2
    change e2 ∉ everD at HnD
    change ltIn (proc ++ [e]) e1 e2
    rcases List.mem_append.1 He2 with He2 | He2
    · exact ltInAppL G Hgwf Hcat6gmo proc [e] e1 e2 Hnd' (HInf e1 e2 Hh Hlt He2 HnD)
    · rw [List.mem_singleton] at He2
      subst He2
      have He1v : e1 ∈ visited G n := by
        obtain ⟨Hg1, _, Hpos⟩ := Hlt
        rw [gposOfLookup G n e2 Hgwf.1 He] at Hpos
        exact (elemOfVisited G Hgwf Hcat6gmo n e1).2
          (elem_of_take.2 ⟨gpos G e1, gposElemLookup G e1 Hg1, Hpos⟩)
      rcases (Hpart e1).1 He1v with He1p | He1D
      · exact ltInAppLast G Hgwf Hcat6gmo proc e1 e2 Hnd' He1p
      · exact absurd Hh (Hclear e1 He1D)
  | stepDefer n D everD proc e He Hr HgateOK =>
    intro e1 e2 Hh Hlt He2 HnD
    change e2 ∈ proc at He2
    change e2 ∉ ({e} ∪ everD : GSet Geid) at HnD
    change ltIn proc e1 e2
    exact HInf e1 e2 Hh Hlt He2 (fun h => HnD (elemOfUnion.2 (.inr h)))
  | stepFlush n D everD proc r m HD Hfirst =>
    have Hr0dom : r ∈ AxSched.domG D := AxSched.memDomG.2 (by rw [HD]; rfl)
    have Hr0notp : r ∉ proc := fun h => HI.invDisj r h Hr0dom
    have Hnd' : (proc ++ [r]).Nodup := by
      refine NoDup_app.2 ⟨HI.invNodup, fun x hx hx' => ?_, NoDup_singleton⟩
      rw [List.mem_singleton] at hx'
      rw [hx'] at hx
      exact Hr0notp hx
    intro e1 e2 Hh Hlt He2 HnD
    change e2 ∈ proc ++ [r] at He2
    change e2 ∉ everD at HnD
    change ltIn (proc ++ [r]) e1 e2
    rcases List.mem_append.1 He2 with He2 | He2
    · exact ltInAppL G Hgwf Hcat6gmo proc [r] e1 e2 Hnd' (HInf e1 e2 Hh Hlt He2 HnD)
    · rw [List.mem_singleton] at He2
      subst He2
      exact absurd (elemOfSubseteq.1 HI.invDEverD e2 Hr0dom) HnD

theorem schedOrdNf (G : Gexec) (Hgwf : gwf G) (Hcat6gmo : gppoCat6Gmo G) (st : Sstate) :
    rtc (schedStep G) sst0 st → InvNF G st := by
  intro h
  refine rtc_ind_r (fun st => InvNF G st) sst0 ?_
    (fun y z Hrun Hstep IH =>
      InvNFStep G Hgwf Hcat6gmo y z (invRtc G Hgwf Hcat6gmo y Hrun) IH Hstep) st h
  intro e1 e2 _ _ Hin
  exact absurd Hin List.not_mem_nil

/-- On a completed run, a same-hart gmo-LATER non-plain-read (e.g. a write) is processed AFTER
`e1`. -/
theorem schedNoFwd (G : Gexec) (Hgwf : gwf G) (Hcat6gmo : gppoCat6Gmo G) (st : Sstate)
    (Hrun : rtc (schedStep G) sst0 st)
    (Hfull : st.sN = G.gxGmo.length) (Hdone : st.sD = ∅) (e1 e2 : Geid) :
    e1.1 = e2.1 → gmoLt G e1 e2 → ¬ gplainR G e2 → ltIn st.sProc e1 e2 := by
  intro Hh Hlt Hnp
  obtain ⟨Hmem, _⟩ := schedCorrect G Hgwf Hcat6gmo st Hrun Hfull Hdone
  have HI := invRtc G Hgwf Hcat6gmo st Hrun
  exact schedOrdNf G Hgwf Hcat6gmo st Hrun e1 e2 Hh Hlt ((Hmem e2).2 Hlt.2.1)
    (fun HeD => Hnp (HI.invEverDR e2 HeD))

/-- A forwarding handout (same hart, the handed-out `e'` gmo-AFTER `e` and not a plain read)
makes `axpolWfL` FALSE for every completed run. -/
theorem fwdPolUnrealizable [Axpol] (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (e e' : Geid) (Hh : e.1 = e'.1) (Hlt : gmoLt GD.gdG e e')
    (Hnp : ¬ gplainR GD.gdG e')
    (Hin : e' ∈ Axpol.sPol GD e ∨ e' ∈ Axpol.lobp GD e) :
    ¬ axpolWfL GD st.sProc := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  obtain ⟨Hmem, HndP, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  obtain ⟨_, _, Hlpos⟩ := schedNoFwd GD.gdG HGw HC6 st Hrun Hfull Hdone e e' Hh Hlt Hnp
  obtain ⟨n, Hn, Hlposn⟩ := lposLookup st.sProc e ((Hmem e).2 Hlt.1)
  intro Hwf
  obtain ⟨Hs, Hl⟩ := Hwf n e Hn
  have Htk : e' ∈ takeL st.sProc n := by
    rcases Hin with Hx | Hx
    · exact elemOfSubseteq.1 Hs e' Hx
    · exact elemOfSubseteq.1 Hl e' Hx
  unfold takeL at Htk
  obtain ⟨i, Hi, Hilt⟩ := elem_of_take.1 (elemOfListToSet.1 Htk)
  rw [Hlposn, lposOfLookup _ i e' HndP Hi] at Hlpos
  omega

/-! # 4. Tier A adequacy over an arbitrary completed run -/

section fixed
variable {GF : BundledGFunctors.{0,0,0}}

/-- Rocq `AxGA4` (a local instance): `axGA2` at `nm`. -/
@[reducible] def axGA4 [AxannotGS GF] (GD : Gdexec) (N obSt0 : Type)
    (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) : AxirisG GF :=
  axGA2 GD N obSt0 obStInterp0 nm

/-- `tierAAdequacyAnnCoreGmo` with `Hgatefree`/`HsPolGmo`/`HlobpGmo` replaced by the consumed
property `Hpol` of THIS run. -/
theorem tierAAdequacyAnnCoreRun {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] [Axpol]
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
    (Hpol : axpolWfL GD sst.sProc)
    (Hcov : (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) :
        GSet Geid) = LawfulSet.ofList sst.sProc)
    (σ0 : obSt0) (i : Agent) (Hi : i ∈ harts) :
    ⊢ AxAnnot.annotInterp (∅ : Mea GF) -∗ obStInterp0 nm GD σ0 ∅ -∗
      ([∗list] i ∈ harts, init nm i) -∗
      |={⊤}[∅]▷=>^[(harts.map n).sum + (1 + (sst.sProc.length + 1))] ⌜post i (sN i)⌝ := by
  letI axG : AxirisG GF := axGA4 GD N obSt0 obStInterp0 nm
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

/-- The Prop-level wrapper: the ONLY scheduler premise is that SOME completed run processes every
handout before its recipient. -/
theorem tierAAdequacyAnnRun [InvGpreS GF] [AxannotG GF] [Axpol]
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
    (Hsched : ∃ sst : Sstate, rtc (schedStep GD.gdG) sst0 sst ∧
      sst.sN = GD.gdG.gxGmo.length ∧ sst.sD = ∅ ∧ axpolWfL GD sst.sProc) :
    ∀ i, i ∈ harts → post i (sN i) := by
  obtain ⟨sst, HrunSched, Hfull, Hdone, Hpol⟩ := Hsched
  have Hcov : (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) :
      GSet Geid) = LawfulSet.ofList sst.sProc := by
    rw [eidsBeforeCov GD harts (schedHGwf GD Hcons) Hharts]
    obtain ⟨Hmem, _⟩ := schedCorrect GD.gdG (schedHGwf GD Hcons) (schedHCat6gmo GD Hcons)
      sst HrunSched Hfull Hdone
    rw [setEq]
    intro x
    rw [elemOfListToSet, elemOfListToSet]
    exact (Hmem x).symm
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
  ihave Hcore := (@tierAAdequacyAnnCoreRun GF .hasNoLC Hinv { axannotName := γ } _ GD N obSt0
    obStInterp0 init nm Hwf Hcons harts Hnd s0 sN n
    (fun j Hj => Hrun { axannotName := γ } nm j Hj) Hk0 Hend post
    (@Hwp Hinv { axannotName := γ } nm)
    sst HrunSched Hfull Hdone Hpol Hcov σ0 i Hi) $$ Hannot0 Hob0 Hinit
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  iexact Hcore

/-- The requested theorem: gated policies.  Any completed run would do
(`schedAxpolWfProcGated`); the gate-free one is used for existence. -/
theorem tierAAdequacyAnnGated [InvGpreS GF] [AxannotG GF] [Axpol]
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
    (HsPolOk : ∀ e e', e' ∈ Axpol.sPol GD e → polGated GD e' e)
    (HlobpOk : ∀ e e', e' ∈ Axpol.lobp GD e → polGated GD e' e) :
    ∀ i, i ∈ harts → post i (sN i) := by
  apply tierAAdequacyAnnRun GD N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts s0 sN n Hrun
    Hk0 Hend post Hwp HobAlloc
  obtain ⟨sst, Hr, _, Hf, Hd, _⟩ := schedGatefreeRun GD
  exact ⟨sst, Hr, Hf, Hd, schedAxpolWfProcGated GD Hcons sst Hr Hf Hd HsPolOk HlobpOk⟩

/-- `tierAAdequacyAnnGmo` re-derived from the arbitrary-run theorem (the gate-free run +
`gatefreeAxpolWfProc`). -/
theorem tierAAdequacyAnnGmoOfRun [InvGpreS GF] [AxannotG GF] [Axpol]
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
  apply tierAAdequacyAnnRun GD N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts s0 sN n Hrun
    Hk0 Hend post Hwp HobAlloc
  obtain ⟨sst, Hr, _, Hf, Hd, Hg⟩ := schedGatefreeRun GD
  exact ⟨sst, Hr, Hf, Hd, gatefreeAxpolWfProc GD Hcons sst Hr Hf Hd Hg HsPolGmo HlobpGmo⟩

/-- The converse direction of strength: the gated theorem is a corollary of the gmo one
(gated ⊆ gmo). -/
theorem tierAAdequacyAnnGatedOfGmo [InvGpreS GF] [AxannotG GF] [Axpol]
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
    (HsPolOk : ∀ e e', e' ∈ Axpol.sPol GD e → polGated GD e' e)
    (HlobpOk : ∀ e e', e' ∈ Axpol.lobp GD e → polGated GD e' e) :
    ∀ i, i ∈ harts → post i (sN i) :=
  tierAAdequacyAnnGmo GD N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts s0 sN n Hrun Hk0
    Hend post Hwp HobAlloc
    (fun e e' H => polGatedGmo GD Hcons e' e (HsPolOk e e' H))
    (fun e e' H => polGatedGmo GD Hcons e' e (HlobpOk e e' H))

end wrapper

end Weak
