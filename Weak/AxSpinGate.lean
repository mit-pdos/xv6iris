/-
Weak: Phase 3a of the spinlock plan -- the GATED tier-A adequacy over a TAGGED graph
(`GdexecT`), with the tagged ctrl gate map `gsrcT`.

Rocq: `iris/AxSpinGate.v` @ xxvzwolszwmp.

## The Rocq header, in substance

WHY A PORT.  `AxDefer5.tierAAdequacyAnnGate` works over an untagged `GD : Gdexec` with
`rvwmoCatConsistent GD` and a gate map satisfying `AxDefer2.gateReal`, whose third conjunct asks
every gated WRITE to carry the dependency edge in `GD.gdDeps`.  The spinlock theorems live over
a TAGGED graph `GT : GdexecT` with the model `AxDeps.rvwmoCatConsistentT GT`; the only untagged
view with a cat model is `gtAdGd GT` (`AxDeps.catTAd`), which DROPS the ctrl edges, so the
untagged third conjunct is false for every real ctrl gate there (`twGateRealUntaggedFails`); and
`forget GT` (which keeps them) has no cat model in general (`AxDeps.twNotCatForget`).

WHAT IS PROVED.
- §1 `gateSrcPo` (conjuncts 1-2 of `gateReal`: sources are po-earlier reads), `gateReal'` (+ the
  write conjunct as a gmo FACT, exactly what `gateW'` consumes), `gateRealReal'` (the old notion
  implies the new).  `gateSrcPoGmo`: "labelled => in gxGmo" comes from `gwf` alone.
  `LcanonOkGate'`: `AxDefer5.LcanonOkGate` from `gwf` + `gateSrcPo` + `gateMono` (the rank
  lemmas `canonGate`/`canonPol` REUSED).  `dev2DS'`: `AxDefer3.dev2DS` from `gateReal'` (`gateW'`
  is the only changed leaf; `flowStep`/`flowGmo` REUSED).  `gateReal'WritesNotDeferred`: under
  `Lcanon` every write has `gkey w = gpos w` and `goff w = 0` (the HELD_NZ lemma).
- §2 The tagged gate map `gsrcT GT e = {r | ∃ w, ((r,w),DTctrl) ∈ gtDeps GT ∧ (w = e ∨ gpo w e) ∧
  r a RAM read}` (`gsrcTSpec`; the RAM-read filter is W13 (F-dep) (0c): `gtdepsWf` admits I/O-load
  sources, the gate keeps RAM reads only, and the registered roots keep their text),
  `ctrlClosed GT` (the plan's Hctrl_closed), `gsrcTMono` (no premise),
  `gsrcTSrcPo` (from `gtdepsWf` alone), `gsrcTReal'` (from `rvwmoCatConsistentT` +
  `ctrlClosed`), `writesNotDeferredT`.
- §3 `tierAAdequacyAnnGateT`: `AxDefer5.tierAAdequacyAnnGate` at `GD := gtAdGd GT`, `Hcons :=
  catTAd GT HconsT`, `gsrc := gsrcT GT`, by instantiating `AxDefer5.tierAAdequacyAnnL` at
  `LcanonOkGate'`.  Graph premise: `rvwmoCatConsistentT GT` ONLY (FINDING 1).
  `tierAAdequacyAnnDev2GateT`: the dev-2 corollary (+ `ctrlClosed GT`).
- §4 Sanity (kernel computation): `AxDeps.tw` and `twc` (= tw + a SECOND store after the branch,
  with its closing ctrl edge): cat_t, ctrlClosed, gsrcT nonempty at a gated write; `twcOpen`
  (the closing edge missing) is cat_t-consistent but NOT ctrlClosed.  `twLcanon`: the reload
  (1,2) IS deferred.

FINDINGS (Rocq).  1. `LcanonOkGate` (hence the gated adequacy) uses ONLY conjuncts 1-2 of
`gateReal`; the write conjunct is consumed only by the dev-2 corollary.  2. "labelled => in
gxGmo" for gate sources is `gwf`.  3. `gateReal'` from HconsT + Hctrl_closed; writes never
deferred.

## Deviations from Rocq

1. Vocabulary as AxDeps/AxDefer3/AxDefer5: `omap` ↦ `List.filterMap`, `list_to_set` ↦
   `LawfulSet.ofList`, `forallb` ↦ `List.all`, `bool_decide` ↦ `decide`, `implb a b` ↦
   `!a || b`, `≡ₚ` ↦ `List.Perm`; tagged deps are right-nested `((r, w), tg)` (AxDeps dev. 2);
   `vm_compute` ↦ `decide +kernel`.
2. O2 STAGE C: the section parameter `T` is gone (as AxDefer5 deviation 2): `tierAAstep GD nm i`
   and `tierAWpd GD N obSt0 obStInterp0 nm …`.  Section `Context`s are explicit arguments in
   AxDefer5's order; `[Axpol]` is an instance argument; `GF` at universe 0.
3. `flowGate'` inducts on the library `tc`, which splits at the LAST step (as `AxDefer3.flowGate`).
4. The `dev2'` section's `Context`s are explicit arguments (`GD Hcons gsrc Hreal Hmono`, each
   lemma taking only those its Rocq `Proof using` names).
5. `twLcanon`: `List.mergeSort` does not reduce in the kernel, so it is proved as
   `AxDefer3.LcanonGdefer` (rank injectivity + sortedness decided, `List.Perm.eq_of_pairwise`).
   Lean-only helper `AxSpinGate.twListPerm` (the target list is a permutation of the gmo).
6. The `Local Notation`s `B0`/`B1` are `b0`/`b1`; `Ltac vmr'` is `decide +kernel`.

**Rocq → Lean name map.**  `gpo_trans_sg` `gpoTransSg`, `gate_src_po` `gateSrcPo`, `gate_real'`
`gateReal'`, `gate_real'_src_po` `gateReal'SrcPo`, `gate_real_src_po` `gateRealSrcPo`,
`gate_real_real'` `gateRealReal'`, `gate_src_po_gmo` `gateSrcPoGmo`, `Lcanon_ok_gate'`
`LcanonOkGate'`, `gate_w'` `gateW'`, `flow_gate'` `flowGate'`, `dev2_DS'` `dev2DS'`,
`gate_real'_writes_not_deferred` `gateReal'WritesNotDeferred`, `gsrc_t` `gsrcT`, `gsrc_t_spec`
`gsrcTSpec`, `ctrl_closed` `ctrlClosed`, `gsrc_t_mono` `gsrcTMono`, `gsrc_t_src` `gsrcTSrc`,
`gsrc_t_src_po` `gsrcTSrcPo`, `gsrc_t_real'` `gsrcTReal'`, `writes_not_deferred_t`
`writesNotDeferredT`, `tierA_adequacy_ann_gate_t` `tierAAdequacyAnnGateT`,
`tierA_adequacy_ann_dev2_gate_t` `tierAAdequacyAnnDev2GateT`, `ctrl_closed_b`
`AxSpinGate.ctrlClosedB` (duplicated name), `ctrl_closed_b_sound` `ctrlClosedBSound`,
`tw_ctrl_closed` `twCtrlClosed`, `tw_gsrc_nonempty` `twGsrcNonempty`, `tw_Lcanon` `twLcanon`,
`tw_gate_real_untagged_fails` `twGateRealUntaggedFails`, `tw_untagged_views_fail`
`twUntaggedViewsFail`, `twc_prog` `twcProg`, `twc_gmo` `twcGmo`, `twc` `twc`, `twc_open`
`twcOpen`, `twc_cat_t` `twcCatT`, `twc_ctrl_closed` `twcCtrlClosed`, `twc_gsrc_nonempty`
`twcGsrcNonempty`, `twc_gate_w` `twcGateW`, `twc_open_cat_t` `twcOpenCatT`,
`twc_open_not_closed` `twcOpenNotClosed`.  Lean-only: `AxSpinGate.twListPerm`.

**Dropped:** only the §5 `Check`/`Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxDefer5
import Weak.AxDeps

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open AxDefer2
open Dtag

theorem gpoTransSg (G : Gexec) (e1 e2 e3 : Geid) :
    WeakRvwmoGraph.gpo G e1 e2 → WeakRvwmoGraph.gpo G e2 e3 → WeakRvwmoGraph.gpo G e1 e3 := by
  rintro ⟨H1, H2, H3, _⟩ ⟨H4, H5, _, H6⟩
  exact ⟨H1.trans H4, by omega, H3, H6⟩

/-! # 1. The gate notions, untied from `gdDeps` -/

/-- Conjuncts 1-2 of `AxDefer2.gateReal`: sources are po-earlier reads. -/
def gateSrcPo (GD : Gdexec) (gsrc : Geid → GSet Geid) : Prop :=
  ∀ e r, r ∈ gsrc e → WeakRvwmoGraph.gpo GD.gdG r e ∧ glblIs GD.gdG r lbIsR

/-- `gateReal` with the write conjunct as a gmo fact. -/
def gateReal' (GD : Gdexec) (gsrc : Geid → GSet Geid) : Prop :=
  ∀ e r, r ∈ gsrc e →
    WeakRvwmoGraph.gpo GD.gdG r e ∧ glblIs GD.gdG r lbIsR ∧
    (glblIs GD.gdG e lbIsW → gmoLt GD.gdG r e)

theorem gateReal'SrcPo (GD : Gdexec) (gsrc : Geid → GSet Geid) :
    gateReal' GD gsrc → gateSrcPo GD gsrc :=
  fun H e r Hr => ⟨(H e r Hr).1, (H e r Hr).2.1⟩

theorem gateRealSrcPo (GD : Gdexec) (gsrc : Geid → GSet Geid) :
    gateReal GD gsrc → gateSrcPo GD gsrc :=
  fun H e r Hr => ⟨(H e r Hr).1, (H e r Hr).2.1⟩

/-- The old notion implies the new one (`gdepsGmo` turns the edge into gmo). -/
theorem gateRealReal' (GD : Gdexec) (gsrc : Geid → GSet Geid) :
    rvwmoCatConsistent GD → gateReal GD gsrc → gateReal' GD gsrc := by
  intro Hcons H e r Hr
  obtain ⟨H1, H2, H3⟩ := H e r Hr
  exact ⟨H1, H2, fun Hw => Hcons.2.2.2.2.2 (r, e) (H3 Hw)⟩

/-- "labelled => in gxGmo": `gwf` gives it. -/
theorem gateSrcPoGmo (GD : Gdexec) (gsrc : Geid → GSet Geid) : gwf GD.gdG → gateSrcPo GD gsrc →
    ∀ e r, r ∈ gsrc e → r ∈ GD.gdG.gxGmo := by
  intro Hwf Hreal e r Hr
  exact gwfMemGmo _ _ Hwf (WeakRvwmoGraph.glblIsRGmem _ _ (Hreal e r Hr).2)

/-- `AxDefer5.LcanonOkGate`, from `gwf` and conjuncts 1-2 only. -/
theorem LcanonOkGate' [Axpol] (GD : Gdexec) (Hwfg : gwf GD.gdG)
    (gsrc : Geid → GSet Geid) (Hreal : gateSrcPo GD gsrc) (Hmono : gateMono GD gsrc)
    (Hok : ∀ e e', e' ∈ Axpol.sPol GD e ∪ Axpol.lobp GD e →
      polDS GD.gdG gsrc e' e ∨ e' ∈ gsrc e) :
    (Lcanon GD gsrc).Perm GD.gdG.gxGmo ∧ gsrcBefore (Lcanon GD gsrc) gsrc ∧
    axpolWfL GD (Lcanon GD gsrc) := by
  have Hnd := Hwfg.1
  have Hsg := gateSrcPoGmo GD gsrc Hwfg Hreal
  have Hpo : ∀ e r, r ∈ gsrc e → WeakRvwmoGraph.gpo GD.gdG r e := fun e r Hr => (Hreal e r Hr).1
  apply orderOfRank GD Hnd
  · intro e r He Hr
    exact ⟨Hsg e r Hr, canonGate GD.gdG gsrc Hnd Hpo Hmono Hsg e r He Hr⟩
  · intro e e' He Hin
    rcases Hok e e' Hin with Hds | Hg
    · exact ⟨Hds.1.1, canonPol GD.gdG gsrc Hnd Hpo Hsg e e' Hds⟩
    · exact ⟨Hsg e e' Hg, canonGate GD.gdG gsrc Hnd Hpo Hmono Hsg e e' He Hg⟩

/-! ## 1.1 Dev-2 handouts are deferral-safe, from `gateReal'` -/

/-- THE ONLY CHANGED LEAF: rule 11 as a gmo fact. -/
theorem gateW' (GD : Gdexec) (gsrc : Geid → GSet Geid) (Hreal : gateReal' GD gsrc) (w r : Geid) :
    r ∈ gsrc w → gisW GD.gdG w = true → gmoLt GD.gdG r w :=
  fun Hr Hw => (Hreal w r Hr).2.2 (AxDeps.gisWGlbl _ w Hw)

theorem flowGate' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (gsrc : Geid → GSet Geid)
    (Hreal : gateReal' GD gsrc) (Hmono : gateMono GD gsrc) (x e : Geid) :
    gobCatFlow GD x e →
    ∀ s, s ∈ gsrc x → gmoLt GD.gdG s e ∨ (s ∈ gsrc e ∧ WeakRvwmoGraph.gpo GD.gdG x e) := by
  intro Hf
  induction Hf with
  | single H =>
    rename_i y
    have Hxe := flowGmo GD Hcons _ _ (tc_once H)
    intro s Hs
    rcases flowStep GD Hcons x y H with Hw | Hpo | ⟨m, Hxm, Hmw, Hmy⟩
    · exact .inl (gmoLtTrans _ _ _ _ (gateW' GD gsrc Hreal x s Hs Hw) Hxe)
    · exact .inr ⟨Hmono x y Hpo s Hs, Hpo⟩
    · exact .inl (gmoLtTrans _ _ _ _ (gateW' GD gsrc Hreal m s (Hmono x m Hxm s Hs) Hmw) Hmy)
  | tail Hrest H IH =>
    rename_i u y
    have Huy := flowGmo GD Hcons _ _ (tc_once H)
    intro s Hs
    rcases IH s Hs with Hl | ⟨Hin, Hxu⟩
    · exact .inl (gmoLtTrans _ _ _ _ Hl Huy)
    · rcases flowStep GD Hcons u y H with Hw | Hpo | ⟨m, Hum, Hmw, Hmy⟩
      · exact .inl (gmoLtTrans _ _ _ _ (gateW' GD gsrc Hreal u s Hin Hw) Huy)
      · exact .inr ⟨Hmono u y Hpo s Hin, gpoTransSg _ _ _ _ Hxu Hpo⟩
      · exact .inl (gmoLtTrans _ _ _ _
          (gateW' GD gsrc Hreal m s (Hmono u m Hum s Hin) Hmw) Hmy)

theorem dev2DS' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (gsrc : Geid → GSet Geid)
    (Hreal : gateReal' GD gsrc) (Hmono : gateMono GD gsrc) (e' e : Geid) :
    flowDev2 GD e' e → polDS GD.gdG gsrc e' e := by
  intro Hf
  refine ⟨flowDev2Gmo GD Hcons e' e Hf, fun s Hs => ?_⟩
  rcases Hf with Hf | ⟨⟨Hpo, _⟩, _⟩
  · exact flowGate' GD Hcons gsrc Hreal Hmono e' e Hf s Hs
  · exact .inr ⟨Hmono e' e Hpo s Hs, Hpo⟩

/-! ## 1.2 Writes are never deferred under `Lcanon` -/

theorem gateReal'WritesNotDeferred (GD : Gdexec) (gsrc : Geid → GSet Geid)
    (Hreal : gateReal' GD gsrc) (w : Geid) :
    glblIs GD.gdG w lbIsW →
    gkey GD.gdG gsrc w = gpos GD.gdG w ∧ goff GD.gdG gsrc w = 0 := by
  intro Hw
  have Hk : gkey GD.gdG gsrc w = gpos GD.gdG w := by
    apply Nat.le_antisymm _ (gkeyGeSelf _ _ _)
    apply gkeyLe _ _ _ _ (Nat.le_refl _)
    intro r Hr
    obtain ⟨_, _, h⟩ := (Hreal w r Hr).2.2 Hw
    omega
  refine ⟨Hk, ?_⟩
  unfold goff
  rw [Hk, if_neg (Nat.lt_irrefl _)]

/-! # 2. The tagged gate map -/

/-- The tagged gate map: the RAM-READ sources of the ctrl edges into `e` or a po-earlier write
(W13 (F-dep) (0c) [R38.1]: an I/O-load source is filtered out, so the gate's sources stay RAM
reads under the I/O-admitting `gtdepsWf`). -/
def gsrcT (GT : GdexecT) (e : Geid) : GSet Geid :=
  LawfulSet.ofList (GT.gtDeps.filterMap (fun d : Tdep =>
    if decide (d.2 = DTctrl) && gisRd GT.gtG d.1.1 && (decide (d.1.2 = e) || gpoB GT.gtG d.1.2 e)
    then some d.1.1 else none))

theorem gsrcTSpec (GT : GdexecT) (e r : Geid) :
    r ∈ gsrcT GT e ↔ ∃ w, ((r, w), DTctrl) ∈ GT.gtDeps ∧ (w = e ∨ WeakRvwmoGraph.gpo GT.gtG w e) ∧
      gisRd GT.gtG r = true := by
  rw [gsrcT, elemOfListToSet, List.mem_filterMap]
  constructor
  · rintro ⟨⟨⟨r', w⟩, tg⟩, Hin, Hf⟩
    simp only at Hf
    split at Hf
    · next Hb =>
      cases Hf
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, gpoBSpec] at Hb
      obtain ⟨⟨rfl, Hr⟩, Hwe⟩ := Hb
      exact ⟨w, Hin, Hwe, Hr⟩
    · cases Hf
  · rintro ⟨w, Hin, Hwe, Hr⟩
    refine ⟨((r, w), DTctrl), Hin, ?_⟩
    have Hb : (decide (DTctrl = DTctrl) && gisRd GT.gtG r && (decide (w = e) || gpoB GT.gtG w e))
        = true := by
      simp only [decide_true, Bool.true_and, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        gpoBSpec]
      exact ⟨Hr, Hwe⟩
    show (if (decide (DTctrl = DTctrl) && gisRd GT.gtG r && (decide (w = e) || gpoB GT.gtG w e))
      = true then some r else none) = some r
    rw [if_pos Hb]

/-- The plan's Hctrl_closed, verbatim. -/
def ctrlClosed (GT : GdexecT) : Prop :=
  ∀ r w e, ((r, w), DTctrl) ∈ GT.gtDeps → WeakRvwmoGraph.gpo GT.gtG w e →
    glblIs GT.gtG e lbIsW → ((r, e), DTctrl) ∈ GT.gtDeps

/-- gateMono: po-transitivity, no premise. -/
theorem gsrcTMono (GT : GdexecT) : gateMono (gtAdGd GT) (gsrcT GT) := by
  intro e1 e2 H12 r Hr
  rw [gsrcTSpec] at Hr ⊢
  obtain ⟨w, Hin, Hwe, Hrd⟩ := Hr
  refine ⟨w, Hin, .inr ?_, Hrd⟩
  rcases Hwe with rfl | Hpo
  · exact H12
  · exact gpoTransSg _ _ _ _ Hpo H12

theorem gsrcTSrc (GT : GdexecT) (Hdw : gtdepsWf GT.gtG GT.gtDeps) (e r : Geid) :
    r ∈ gsrcT GT e → ∃ w, ((r, w), DTctrl) ∈ GT.gtDeps ∧
      (w = e ∨ WeakRvwmoGraph.gpo GT.gtG w e) ∧
      WeakRvwmoGraph.gpo GT.gtG r w ∧ glblIs GT.gtG r lbIsR ∧ glblIs GT.gtG w lbIsWT := by
  intro Hr
  obtain ⟨w, Hin, Hwe, Hrd⟩ := (gsrcTSpec GT e r).1 Hr
  obtain ⟨H1, H2, H3, H4⟩ := Hdw _ Hin
  simp only [dtagW, if_true] at H1 H2 H3 H4
  obtain ⟨l, Hl, Hlr⟩ := AxDeps.gisRdGlbl _ _ Hrd
  obtain ⟨l', Hl', _⟩ := H4
  refine ⟨w, Hin, Hwe, ⟨H1, H2, by simp [Hl], by simp [Hl']⟩, ⟨l, Hl, Hlr⟩, ⟨l', Hl', ?_⟩⟩
  assumption

/-- Conjuncts 1-2 from `gtdepsWf` alone. -/
theorem gsrcTSrcPo (GT : GdexecT) (Hdw : gtdepsWf GT.gtG GT.gtDeps) :
    gateSrcPo (gtAdGd GT) (gsrcT GT) := by
  intro e r Hr
  obtain ⟨w, _, Hwe, Hrw, Hrd, _⟩ := gsrcTSrc GT Hdw e r Hr
  refine ⟨?_, Hrd⟩
  rcases Hwe with rfl | Hpo
  · exact Hrw
  · exact gpoTransSg _ _ _ _ Hrw Hpo

/-- gateReal' from the tagged model + Hctrl_closed. -/
theorem gsrcTReal' (GT : GdexecT) (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT) :
    gateReal' (gtAdGd GT) (gsrcT GT) := by
  obtain ⟨_, _, _, _, Hdw, Hdg⟩ := HconsT
  intro e r Hr
  obtain ⟨w, Hin, Hwe, Hrw, Hrd, _⟩ := gsrcTSrc GT Hdw e r Hr
  refine ⟨?_, Hrd, fun Hew => ?_⟩
  · rcases Hwe with rfl | Hpo
    · exact Hrw
    · exact gpoTransSg _ _ _ _ Hrw Hpo
  · rcases Hwe with rfl | Hpo
    · exact Hdg _ Hin
    · exact Hdg ((r, e), DTctrl) (Hcl r w e Hin Hpo Hew)

/-- HELD_NZ's lemma: writes are never deferred under `Lcanon` with `gsrcT`. -/
theorem writesNotDeferredT (GT : GdexecT) (HconsT : rvwmoCatConsistentT GT)
    (Hcl : ctrlClosed GT) (w : Geid) :
    glblIs GT.gtG w lbIsW →
    gkey GT.gtG (gsrcT GT) w = gpos GT.gtG w ∧ goff GT.gtG (gsrcT GT) w = 0 :=
  gateReal'WritesNotDeferred (gtAdGd GT) (gsrcT GT) (gsrcTReal' GT HconsT Hcl) w

/-! # 3. The tagged gated tier-A adequacy -/

section TierAGateT
variable {GF : BundledGFunctors.{0,0,0}}

/-- `AxDefer5.tierAAdequacyAnnGate` over a TAGGED graph: `GD := gtAdGd GT`,
`Hcons := catTAd GT HconsT`, `gsrc := gsrcT GT`.  Graph premise: `rvwmoCatConsistentT GT`
only (FINDING 1). -/
theorem tierAAdequacyAnnGateT [InvGpreS GF] [AxannotG GF] [Axpol]
    (GT : GdexecT) (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N → Agent → IProp GF)
    (Hwf : axpolWf) (HconsT : rvwmoCatConsistentT GT)
    (harts : List Agent) (Hnd : harts.Nodup)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ harts)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N) i, i ∈ harts →
      nsteps (tierAAstep (gtAdGd GT) nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow (gtAdGd GT) i).length)
    (post : Agent → Athread → Prop)
    (Hwp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpd (gtAdGd GT) N obSt0 obStInterp0 nm (s0 i) .MaybeStuck i
            (fun s => iprop(⌜post i s⌝)))
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm (gtAdGd GT) σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (Hok : ∀ e e', e' ∈ Axpol.sPol (gtAdGd GT) e ∪ Axpol.lobp (gtAdGd GT) e →
      polDS GT.gtG (gsrcT GT) e' e ∨ e' ∈ gsrcT GT e) :
    ∀ i, i ∈ harts → post i (sN i) := by
  have Hcons := catTAd GT HconsT
  obtain ⟨Hwfg, _, _, _, Hdw, _⟩ := HconsT
  have H := LcanonOkGate' (gtAdGd GT) Hwfg (gsrcT GT) (gsrcTSrcPo GT Hdw) (gsrcTMono GT) Hok
  exact tierAAdequacyAnnL (gtAdGd GT) N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts
    s0 sN n Hrun Hk0 Hend post Hwp HobAlloc (Lcanon (gtAdGd GT) (gsrcT GT)) H.1 H.2.2

/-- The dev-2 corollary: here `ctrlClosed` is load-bearing (`gateW'`). -/
theorem tierAAdequacyAnnDev2GateT [InvGpreS GF] [AxannotG GF] [Axpol]
    (GT : GdexecT) (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N → Agent → IProp GF)
    (Hwf : axpolWf) (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT)
    (harts : List Agent) (Hnd : harts.Nodup)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ harts)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N) i, i ∈ harts →
      nsteps (tierAAstep (gtAdGd GT) nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow (gtAdGd GT) i).length)
    (post : Agent → Athread → Prop)
    (Hwp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpd (gtAdGd GT) N obSt0 obStInterp0 nm (s0 i) .MaybeStuck i
            (fun s => iprop(⌜post i s⌝)))
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm (gtAdGd GT) σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (HsPol : ∀ e e', e' ∈ Axpol.sPol (gtAdGd GT) e →
      flowDev2 (gtAdGd GT) e' e ∨ e' ∈ gsrcT GT e)
    (Hlobp : ∀ e e', e' ∈ Axpol.lobp (gtAdGd GT) e → flowDev2 (gtAdGd GT) e' e) :
    ∀ i, i ∈ harts → post i (sN i) := by
  have Hcons := catTAd GT HconsT
  have Hreal := gsrcTReal' GT HconsT Hcl
  apply tierAAdequacyAnnGateT GT N obSt0 obStInterp0 init Hwf HconsT harts Hnd Hharts s0 sN n
    Hrun Hk0 Hend post Hwp HobAlloc
  intro e e' Hin
  rcases elemOfUnion.1 Hin with Hin | Hin
  · rcases HsPol e e' Hin with Hf | Hg
    · exact .inl (dev2DS' (gtAdGd GT) Hcons (gsrcT GT) Hreal (gsrcTMono GT) e' e Hf)
    · exact .inr Hg
  · exact .inl (dev2DS' (gtAdGd GT) Hcons (gsrcT GT) Hreal (gsrcTMono GT) e' e (Hlobp e e' Hin))

end TierAGateT

/-! # 4. Sanity: the premises are jointly satisfiable, the gate is non-trivial -/

/-- A decision procedure for `ctrlClosed` (sound under `gwf`). -/
def AxSpinGate.ctrlClosedB (GT : GdexecT) : Bool :=
  GT.gtDeps.all (fun d : Tdep =>
    !(decide (d.2 = DTctrl)) ||
      GT.gtG.gxGmo.all (fun e =>
        !(gpoB GT.gtG d.1.2 e && glblB GT.gtG e lbIsW) ||
          decide (((d.1.1, e), DTctrl) ∈ GT.gtDeps)))

theorem ctrlClosedBSound (GT : GdexecT) :
    gwf GT.gtG → AxSpinGate.ctrlClosedB GT = true → ctrlClosed GT := by
  intro Hwf H r w e Hin Hpo Hw
  have Hem : e ∈ GT.gtG.gxGmo := gwfMemGmo _ _ Hwf (WeakRvwmoGraph.glblIsWGmem _ _ Hw)
  rw [AxSpinGate.ctrlClosedB, List.all_eq_true] at H
  have h := H _ Hin
  simp only [decide_true, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  have h2 := h e Hem
  rw [(gpoBSpec _ _ _).2 Hpo, (glblBSpec _ _ _).2 Hw] at h2
  simpa using h2

/-- `AxDeps.tw` (AxDeps §5.1): H1 = R z (1,0); W x (1,1) ctrl-dep on (1,0); R x (1,2)
forwarded from (1,1), gmo-FIRST. -/
theorem twCtrlClosed : ctrlClosed AxDeps.tw :=
  ctrlClosedBSound _ twCatT.1 (by decide +kernel)

theorem twGsrcNonempty : ((1, 0) : Geid) ∈ gsrcT AxDeps.tw (1, 1) :=
  (gsrcTSpec _ _ _).2 ⟨(1, 1), by decide +kernel, .inl rfl, by decide +kernel⟩

/-- Lean-only: the target order is a permutation of `AxDeps.tw`'s gmo. -/
theorem AxSpinGate.twListPerm :
    ([(1, 0), (1, 2), (1, 1), (0, 0), (0, 1)] : List Geid).Perm (gtAdGd AxDeps.tw).gdG.gxGmo := by
  decide +kernel

/-- The reload IS deferred: processed after its gate source, before the spill it is forwarded
from. -/
theorem twLcanon :
    Lcanon (gtAdGd AxDeps.tw) (gsrcT AxDeps.tw) = [(1, 0), (1, 2), (1, 1), (0, 0), (0, 1)] := by
  have Hinj : ∀ a, a ∈ ([(1, 0), (1, 2), (1, 1), (0, 0), (0, 1)] : List Geid) →
      ∀ b, b ∈ ([(1, 0), (1, 2), (1, 1), (0, 0), (0, 1)] : List Geid) →
      AxDefer3.grank (gtAdGd AxDeps.tw).gdG (gsrcT AxDeps.tw) a =
        AxDefer3.grank (gtAdGd AxDeps.tw).gdG (gsrcT AxDeps.tw) b → a = b := by
    decide +kernel
  have Hsorted : List.Pairwise
      (fun a b => decide (rankLe (AxDefer3.grank (gtAdGd AxDeps.tw).gdG (gsrcT AxDeps.tw)) a b)
        = true) ([(1, 0), (1, 2), (1, 1), (0, 0), (0, 1)] : List Geid) := by
    decide +kernel
  refine List.Perm.eq_of_pairwise (fun a b ha hb hab hba => ?_)
    (AxDefer3.rankSortSorted _ _) Hsorted
    ((rankSortPerm _ _).trans AxSpinGate.twListPerm.symm)
  have ha' := ((rankSortPerm _ _).trans AxSpinGate.twListPerm.symm).mem_iff.1 ha
  have h1 := of_decide_eq_true hab
  have h2 := of_decide_eq_true hba
  unfold rankLe at h1 h2
  exact Hinj a ha' b hb (by omega)

/-- The untagged `gateReal` FAILS at the ad-projection for `gsrcT`: the ctrl edge is not in
`(gtAdGd GT).gdDeps`. -/
theorem twGateRealUntaggedFails : ¬ gateReal (gtAdGd AxDeps.tw) (gsrcT AxDeps.tw) := by
  intro H
  obtain ⟨_, _, H3⟩ := H _ _ twGsrcNonempty
  have Hw : glblIs (gtAdGd AxDeps.tw).gdG (1, 1) lbIsW := (glblBSpec _ _ _).1 (by decide +kernel)
  have h := H3 Hw
  have Hn : (gtAdGd AxDeps.tw).gdDeps = [] := by decide +kernel
  unfold gdepsRel at h
  rw [Hn] at h
  cases h

/-- ... and `forget AxDeps.tw` has no cat model (`AxDeps.twNotCatForget`), so neither untagged
view carries the gated route on `tw`. -/
theorem twUntaggedViewsFail :
    rvwmoCatConsistentT AxDeps.tw ∧ ctrlClosed AxDeps.tw ∧
    ¬ rvwmoCatConsistent (forget AxDeps.tw) ∧ ¬ gateReal (gtAdGd AxDeps.tw) (gsrcT AxDeps.tw) :=
  ⟨twCatT, twCtrlClosed, twNotCatForget, twGateRealUntaggedFails⟩

/-- `twc`: `tw` plus a SECOND store after the branch, W y (1,3), with the closing ctrl edge
(1,0)→(1,3); `twcOpen` omits that edge. -/
def twcProg : List (List Lbl) :=
  [[Lbl.LLoad false 0 [1] [b1],
    Lbl.LLoad false 1 [0] [b0]],
   [Lbl.LLoad false 2 [0] [b0],
    Lbl.LStore false 0 [b1] .WCplain,
    Lbl.LLoad false 0 [1] [b1],
    Lbl.LStore false 1 [b1] .WCplain]]

def twcGmo : List Geid :=
  [(1, 2), (1, 0), (1, 1), (0, 0), (0, 1), (1, 3)]

def twc : GdexecT :=
  mkgt twcProg twcGmo (twDeps ++ [(((1, 0), (1, 3)), DTctrl)])

def twcOpen : GdexecT := mkgt twcProg twcGmo twDeps

theorem twcCatT : rvwmoCatConsistentT twc :=
  catTConsistentBSound _ (by decide +kernel)

theorem twcCtrlClosed : ctrlClosed twc :=
  ctrlClosedBSound _ twcCatT.1 (by decide +kernel)

theorem twcGsrcNonempty : ((1, 0) : Geid) ∈ gsrcT twc (1, 3) :=
  (gsrcTSpec _ _ _).2 ⟨(1, 1), by decide +kernel, .inr ((gpoBSpec _ _ _).1 (by decide +kernel)),
    by decide +kernel⟩

/-- The gate fact on the SECOND store, through the closure edge. -/
theorem twcGateW : gmoLt twc.gtG (1, 0) (1, 3) :=
  (gsrcTReal' twc twcCatT twcCtrlClosed _ _ twcGsrcNonempty).2.2
    ((glblBSpec _ _ _).1 (by decide +kernel))

theorem twcOpenCatT : rvwmoCatConsistentT twcOpen :=
  catTConsistentBSound _ (by decide +kernel)

theorem twcOpenNotClosed : ¬ ctrlClosed twcOpen := by
  intro H
  have Hin := H (1, 0) (1, 1) (1, 3) (by decide +kernel)
    ((gpoBSpec _ _ _).1 (by decide +kernel)) ((glblBSpec _ _ _).1 (by decide +kernel))
  have Hf : (((1, 0), (1, 3)), DTctrl) ∉ twcOpen.gtDeps := by decide +kernel
  exact Hf Hin

end Weak
