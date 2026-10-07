/-
Weak: **`AxAdequacy`'s phase-2 gmo-order induction, GENERALIZED to an arbitrary
predecessor-closed processing list `L`** (AxSL tier; LB/AxSL ctrl-gate scheduler).

Rocq: `iris/AxAdequacyL.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxAdequacy.adequacyOrd`'s machinery is hardwired to `gxGmo`; wiring `AxSched`'s
`AxTieProc.isProcOrder` output into it needs `ordEaTodo`/`axpolWfGmo`'s analogues restated
over an ARBITRARY list.  This file does that restatement, PARAMETRIC in `L`, reusing
`AxAdequacy.ordPending`/`ordPendingExtract` verbatim (they never mention the list) and
`AxTieProc.lpos`/`lposLookup`/`lposOfLookup` as the position function.

  §1 `takeL` (the `L`-prefix as a set) and its combinatorics.
  §2 `axpolWfL`, `ordEaTodoL`, and the induction `adequacyOrdAuxL(Wf)`/`adequacyOrdL(Wf)`.
  §3 predecessor-closedness `LPredClosed`; the gob_cat-predecessor handout policy discharges
     `axpolWfL` from it (`axpolWfLOfPredClosed`); `gxGmo` satisfies it (`LPredClosedGmo`), so
     `AxAdequacy.adequacyOrd` is recovered as an instance (`adequacyOrdViaL`).
  §4 (prose only) THE FINDING: `AxTieProc.isProcOrder` does NOT entail `LPredClosed GD proc` — a
     deferred read's `gobCat` successor that is a non-write (riscv.cat rule 2, a later same-hart
     same-byte read) or a cross-hart `gfr` target has no ordering guarantee.  UPDATE: `AxSched`
     now carries `inv_ord_ppo`/`sched_ord_ppo`; §5/§6 show that is what the weakened closure
     needs for the same-hart half, and the cross-hart `gfr` half needs nothing (a plain read
     deposits emp).
  §5 PART (B): `gobrCatFlow`/`gobCatFlow` drop exactly the `gfr` edges sourced at a PLAIN read
     (`gisW = false`; an RMW-sourced `gfr` is kept since an RMW deposits like a store);
     `LPredClosedFlow` is the weakened closure, `axpolWfLOfPredClosedFlow` its discharge.
  §6 (prose only) PART (C) status: write-sourced and `gppo_cat6`/RMW-`gfr` arms discharged by
     `AxSched.inv_ord_fresh`/`sched_ord_ppo`; the rule-12/`gdepsRel` arms OPEN (need a
     `Gdexec`-aware twin of `inv_ord_ppo`).

## Deviations from Rocq

1. Representation as `AxAdequacy` deviation 1: `list_to_set` ↦ `LawfulSet.ofList`, `take`/`drop`
   ↦ `List.take`/`List.drop`, `from_option id emp` ↦ `AxWp.fromOption (fun P => P) iprop(emp)`,
   `dom` ↦ `FiniteMap.dom_set`, `L ≡ₚ l` ↦ `L.Perm l`, `|={⊤}[∅]▷=>^n` ↦ `|={⊤}[∅]▷=>^[n]`,
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`; wand chains stated `⊢ A -∗ B -∗ C`.
2. Rocq's `adequacy_ord_aux_L`/`adequacy_ord_L` are `Definition`s (the `_wf` lemma at
   `proj1 Hcons`); here they are theorems with the same statements.  The induction on
   `k = length L - n` is the Lean-only `AxAdequacyL.ordAuxK` (as `AxAdequacy.ordAuxK`).
3. Lean-only helper: `AxAdequacyL.ordAuxK`.  No premise is carried beyond Rocq's own.
4. The WP step clause (`AxWp2.wpPreStepDef`) is never introduced or eliminated here: phase 2
   only consumes `flowEqEa`/`flowEqDyn`, so the pending Q8 `fetchPin` rework does not touch
   this file.

**Rocq → Lean name map.**  `take_L` `takeL`, `take_L_0` `takeL0`, `take_L_full` `takeLFull`,
`take_L_snoc` `takeLSnoc`, `lt_in_take_L` `ltInTakeL`, `axpol_wf_L` `axpolWfL`,
`lob_succ_not_in_take_L` `lobSuccNotInTakeL`, `ord_ea_todo_L` `ordEaTodoL`, `ord_ea_todo_L_cons`
`ordEaTodoLCons`, `adequacy_ord_aux_L_wf` `adequacyOrdAuxLWf`, `adequacy_ord_aux_L`
`adequacyOrdAuxL`, `adequacy_ord_L_wf` `adequacyOrdLWf`, `adequacy_ord_L` `adequacyOrdL`,
`L_pred_closed` `LPredClosed`, `axpol_wf_L_of_pred_closed` `axpolWfLOfPredClosed`,
`L_pred_closed_gmo` `LPredClosedGmo`, `adequacy_ord_via_L` `adequacyOrdViaL`, `gobr_cat_flow`
`gobrCatFlow`, `gob_cat_flow` `gobCatFlow`, `gobr_cat_flow_sub` `gobrCatFlowSub`,
`gob_cat_flow_sub` `gobCatFlowSub`, `L_pred_closed_flow` `LPredClosedFlow`,
`L_pred_closed_to_flow` `LPredClosedToFlow`, `L_pred_closed_gmo_flow` `LPredClosedGmoFlow`,
`axpol_wf_L_of_pred_closed_flow` `axpolWfLOfPredClosedFlow`.

**Dropped:** only the §7 `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxAdequacy
import Weak.AxTieProc
import Weak.AxSched

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. `takeL`: the prefix-as-a-set over an arbitrary list -/

def takeL (L : List Geid) (n : Nat) : GSet Geid := LawfulSet.ofList (L.take n)

theorem takeL0 (L : List Geid) : takeL L 0 = ∅ := by
  unfold takeL
  rw [List.take_zero]
  exact listToSetNil

theorem takeLFull (L : List Geid) : takeL L L.length = (LawfulSet.ofList L : GSet Geid) := by
  unfold takeL
  rw [List.take_length]

theorem takeLSnoc (L : List Geid) (n : Nat) (e : Geid) :
    L[n]? = some e → takeL L (n + 1) = ({e} : GSet Geid) ∪ takeL L n := by
  intro hn
  unfold takeL
  rw [List.take_add_one, hn, listToSetApp]
  rw [setEq]
  intro x
  simp only [elemOfUnion, elemOfListToSet, elemOfSingleton, Option.toList_some,
    List.mem_singleton]
  exact Or.comm

/-- An event's `ltIn`-predecessor sits inside the take-prefix at the other event's position. -/
theorem ltInTakeL (L : List Geid) (n : Nat) (e e' : Geid) :
    L.Nodup → L[n]? = some e → ltIn L e' e → e' ∈ takeL L n := by
  rintro hnd hn ⟨he', _, hlt⟩
  obtain ⟨i, hi, heq⟩ := lposLookup L e' he'
  rw [heq, lposOfLookup L n e hnd hn] at hlt
  unfold takeL
  rw [elemOfListToSet]
  exact AxAdequacy.memTakeOfLookup hi hlt

/-! # 2. `axpolWfL`, `ordEaTodoL`, and the induction -/

section polL
variable [Axpol]

/-- THE INDUCTION HYPOTHESIS over an arbitrary `L`. -/
def axpolWfL (GD : Gdexec) (L : List Geid) : Prop :=
  ∀ n e, L[n]? = some e → Axpol.sPol GD e ⊆ takeL L n ∧ Axpol.lobp GD e ⊆ takeL L n

/-- No lob′-successor of an event at `L`-position `n` sits in the `L`-prefix at `n`. -/
theorem lobSuccNotInTakeL (GD : Gdexec) (L : List Geid)
    (HpermSub : ∀ e, e ∈ GD.gdG.gxGmo → e ∈ L)
    (Hpol : axpolWfL GD L) (n : Nat) (e : Geid)
    (He : L[n]? = some e) (Hnd : L.Nodup) :
    ∀ eOut, eOut ∈ lobSuccOf GD e → eOut ∉ takeL L n := by
  intro eOut hsucc hcon
  obtain ⟨hlob, hgmo⟩ := (elemOfLobSuccOf GD e eOut).1 hsucc
  obtain ⟨m, hm, _⟩ := lposLookup L eOut (HpermSub eOut hgmo)
  have h1 := (Hpol m eOut hm).2 e hlob
  unfold takeL at h1 hcon
  rw [elemOfListToSet] at h1 hcon
  obtain ⟨j, hj, hjl⟩ := AxAdequacy.memTake h1
  have e1 := NoDup_lookup Hnd hjl He
  obtain ⟨j', hj', hjl'⟩ := AxAdequacy.memTake hcon
  have e2 := NoDup_lookup Hnd hjl' hm
  omega

section ordL
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF]

/-- THE WALK, over an arbitrary `L`. -/
def ordEaTodoL (GD : Gdexec) (ea : Sra GF) (na : Mea GF) (L : List Geid) (n : Nat) : IProp GF :=
  iprop([∗list] e0 ∈ L.drop n,
    AxWp.fromOption (fun R0 => AxWp.fromOption
        (fun flowIn => flowEqEa GD e0 (Axpol.sPol GD e0) flowIn ea R0) iprop(emp) (get? ea e0))
      iprop(emp) (get? na e0))

theorem ordEaTodoLCons (GD : Gdexec) (ea : Sra GF) (na : Mea GF) (L : List Geid) (n : Nat)
    (e : Geid) :
    L[n]? = some e →
    ordEaTodoL GD ea na L n ⊣⊢
    iprop(AxWp.fromOption (fun R0 => AxWp.fromOption
          (fun flowIn => flowEqEa GD e (Axpol.sPol GD e) flowIn ea R0) iprop(emp) (get? ea e))
        iprop(emp) (get? na e)
      ∗ ordEaTodoL GD ea na L (n + 1)) := by
  intro hn
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hn
  have hd : L.drop n = e :: L.drop (n + 1) := by
    rw [List.drop_eq_getElem_cons hlt, hget]
  unfold ordEaTodoL
  rw [hd]
  exact BigSepL.bigSepL_cons

/-- Lean-only: `adequacyOrdAuxLWf`'s induction, on `k = length L - n`. -/
theorem AxAdequacyL.ordAuxK (GD : Gdexec) (Hcons : gwf GD.gdG)
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo)
    (Hpol : axpolWfL GD L) (na : Mea GF) (ea : Sra GF)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList L : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0) :
    ∀ k n, k = L.length - n → n ≤ L.length →
    ⊢ ordEaTodoL GD ea na L n -∗
      (∃ (σ : AxirisG.obSt GF), AxirisG.obStInterp GD σ (takeL L n) ∗
        ([∗set] e0 ∈ takeL L n, AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ∗
        ([∗set] e0 ∈ takeL L n, ordPending GD ea (takeL L n) e0)) -∗
      |={⊤}[∅]▷=>^[k]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList L) ∗
          [∗set] e0 ∈ (LawfulSet.ofList L : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) := by
  have Hnd : L.Nodup := Hperm.nodup_iff.2 Hcons.1
  have HpermSub : ∀ x, x ∈ GD.gdG.gxGmo → x ∈ L := fun x hx => Hperm.mem_iff.2 hx
  intro k
  induction k with
  | zero =>
    intro n hk hn
    have hn' : n = L.length := by omega
    subst hn'
    rw [AxAdequacy.stepFupdNZero, takeLFull]
    iintro _ ⟨%σ, Hob, Hbag, -⟩
    iexists σ
    isplitl [Hob]
    · iexact Hob
    · iexact Hbag
  | succ k IHk =>
    intro n hk hn
    have Hnlt : n < L.length := by omega
    obtain ⟨e, He⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 Hnlt)
    have HeL : e ∈ L := elem_of_list_lookup_2 He
    have HeGmo : e ∈ GD.gdG.gxGmo := Hperm.mem_iff.1 HeL
    obtain ⟨Re, HnaE⟩ := Option.isSome_iff_exists.1
      (elemOfDom.1 (Hdom e (elemOfListToSet.2 HeL)))
    have HeDom : e ∈ (FiniteMap.dom_set ea : GSet Geid) := by
      rw [HdomEq]
      exact elemOfDom2 HnaE
    obtain ⟨flowIn, HeaE⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 HeDom)
    have Henin : e ∉ takeL L n := by
      intro hin
      unfold takeL at hin
      rw [elemOfListToSet] at hin
      obtain ⟨j, hj, hjl⟩ := AxAdequacy.memTake hin
      have := NoDup_lookup Hnd hjl He
      omega
    have Hsub := HeaLob e flowIn HeaE
    obtain ⟨HspolP, HlobP⟩ := Hpol n e He
    have Hself : e ∉ lobSuccOf GD e := fun h =>
      Henin (HlobP e ((elemOfLobSuccOf GD e e).1 h).1)
    have Hnosucc := lobSuccNotInTakeL GD L HpermSub Hpol n e He Hnd
    have hs : lobSuccOf GD e \ (({e} : GSet Geid) ∪ takeL L n) = lobSuccOf GD e := by
      rw [setEq]
      intro x
      simp only [elemOfDifference, elemOfUnion, elemOfSingleton]
      constructor
      · exact fun h => h.1
      · intro hx
        refine ⟨hx, fun h => h.elim (fun h' => Hself (h' ▸ hx)) (Hnosucc x hx)⟩
    rw [AxAdequacy.stepFupdNSucc]
    iintro Htodo ⟨%σ, Hob, Hbag, Hpend⟩
    icases (ordEaTodoLCons GD ea na L n e He).1 $$ Htodo with ⟨Hhd, Htodo⟩
    isimp only [HnaE, HeaE, AxWp.fromOption] at Hhd
    ihave ⟨Hflow, Hpend⟩ :=
      ordPendingExtract GD ea (takeL L n) e flowIn HeGmo Henin HeaE Hsub HlobP $$ Hpend
    iunfold flowEqEa, flowEqDyn at Hhd
    imod Hhd $$ %σ %(takeL L n) %HspolP %Henin Hob Hflow with Hhd
    imodintro
    inext
    imod Hhd with ⟨%σ', Hob', HRe, Hdep⟩
    imodintro
    iapply (IHk (n + 1) (by omega) Hnlt) $$ Htodo
    iexists σ'
    rw [takeLSnoc L n e He]
    isplitl [Hob']
    · iexact Hob'
    isplitl [HRe Hbag]
    · iapply (AxAdequacy.bigSepSSingleUnion _ (takeL L n) e Henin).2
      isplitl [HRe]
      · isimp only [HnaE, AxWp.fromOption]
        iexact HRe
      · iexact Hbag
    · iapply (AxAdequacy.bigSepSSingleUnion _ (takeL L n) e Henin).2
      isplitl [Hdep]
      · iunfold ordPending
        rw [hs]
        iexact Hdep
      · iexact Hpend

/-- THE INDUCTION, over `L` (only `gwf` of the model is used). -/
theorem adequacyOrdAuxLWf (GD : Gdexec) (Hcons : gwf GD.gdG)
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo)
    (Hpol : axpolWfL GD L) (na : Mea GF) (ea : Sra GF)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList L : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0) :
    ∀ n, n ≤ L.length →
    ⊢ ordEaTodoL GD ea na L n -∗
      (∃ (σ : AxirisG.obSt GF), AxirisG.obStInterp GD σ (takeL L n) ∗
        ([∗set] e0 ∈ takeL L n, AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ∗
        ([∗set] e0 ∈ takeL L n, ordPending GD ea (takeL L n) e0)) -∗
      |={⊤}[∅]▷=>^[L.length - n]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList L) ∗
          [∗set] e0 ∈ (LawfulSet.ofList L : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) :=
  fun n hn => AxAdequacyL.ordAuxK GD Hcons L Hperm Hpol na ea HdomEq Hdom HeaLob _ n rfl hn

/-- Rocq's `Definition adequacy_ord_aux_L := adequacy_ord_aux_L_wf GD (proj1 Hcons)`. -/
theorem adequacyOrdAuxL (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo)
    (Hpol : axpolWfL GD L) (na : Mea GF) (ea : Sra GF)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList L : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0) :
    ∀ n, n ≤ L.length →
    ⊢ ordEaTodoL GD ea na L n -∗
      (∃ (σ : AxirisG.obSt GF), AxirisG.obStInterp GD σ (takeL L n) ∗
        ([∗set] e0 ∈ takeL L n, AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ∗
        ([∗set] e0 ∈ takeL L n, ordPending GD ea (takeL L n) e0)) -∗
      |={⊤}[∅]▷=>^[L.length - n]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList L) ∗
          [∗set] e0 ∈ (LawfulSet.ofList L : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) :=
  adequacyOrdAuxLWf GD Hcons.1 L Hperm Hpol na ea HdomEq Hdom HeaLob

/-- THE WRAPPER, at full `L` coverage. -/
theorem adequacyOrdLWf (GD : Gdexec) (Hcons : gwf GD.gdG)
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo)
    (Hpol : axpolWfL GD L) (na : Mea GF) (ea : Sra GF)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList L : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ordEaTodoL GD ea na L 0 -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[L.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList L) ∗
          [∗set] e0 ∈ (LawfulSet.ofList L : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) := by
  have h := adequacyOrdAuxLWf GD Hcons L Hperm Hpol na ea HdomEq Hdom HeaLob 0 (Nat.zero_le _)
  rw [Nat.sub_zero, takeL0] at h
  iintro Htodo Hob
  iapply h $$ Htodo
  iexists σ0
  isplitl [Hob]
  · iexact Hob
  isplitl
  · iapply BigSepS.bigSepS_empty.2
    itrivial
  · iapply BigSepS.bigSepS_empty.2
    itrivial

/-- Rocq's `Definition adequacy_ord_L := adequacy_ord_L_wf GD (proj1 Hcons)`. -/
theorem adequacyOrdL (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo)
    (Hpol : axpolWfL GD L) (na : Mea GF) (ea : Sra GF)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList L : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ordEaTodoL GD ea na L 0 -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[L.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList L) ∗
          [∗set] e0 ∈ (LawfulSet.ofList L : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) :=
  adequacyOrdLWf GD Hcons.1 L Hperm Hpol na ea HdomEq Hdom HeaLob σ0

end ordL
end polL

/-! # 3. Predecessor-closedness, and `gxGmo` as an instance -/

/-- Every `gobCat` predecessor of `e` sits before `e`'s own position in `L`. -/
def LPredClosed (GD : Gdexec) (L : List Geid) : Prop :=
  ∀ n e, L[n]? = some e → ∀ e', gobCat GD e' e → e' ∈ takeL L n

/-- The natural gob_cat-predecessor handout policy discharges `axpolWfL` from `LPredClosed`. -/
theorem axpolWfLOfPredClosed [Axpol] (GD : Gdexec) (L : List Geid)
    (HsPolSub : ∀ e e', e' ∈ Axpol.sPol GD e → gobCat GD e' e)
    (HlobpSub : ∀ e e', e' ∈ Axpol.lobp GD e → gobCat GD e' e)
    (Hpc : LPredClosed GD L) :
    axpolWfL GD L := by
  intro n e hn
  exact ⟨fun e' he' => Hpc n e hn e' (HsPolSub e e' he'),
    fun e' he' => Hpc n e hn e' (HlobpSub e e' he')⟩

/-- `gxGmo` satisfies `LPredClosed` (`takeL gxGmo n` is `gmoTake GD n` by definition). -/
theorem LPredClosedGmo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) :
    LPredClosed GD GD.gdG.gxGmo :=
  fun n e hn e' hob => gobCatPredSubGmoTake GD Hcons n e hn e' hob

section polLGmo
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- `AxAdequacy.adequacyOrd` recovered as the `L := gxGmo` instance of `adequacyOrdL`. -/
theorem adequacyOrdViaL (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (Hpol : axpolWfGmo GD) (na : Mea GF) (ea : Sra GF)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ordEaTodo GD ea na 0 -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[GD.gdG.gxGmo.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList GD.gdG.gxGmo) ∗
          [∗set] e0 ∈ (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) :=
  adequacyOrdL GD Hcons GD.gdG.gxGmo (List.Perm.refl _) Hpol na ea HdomEq Hdom HeaLob σ0

end polLGmo

/-! # 4. (prose, header) THE FINDING: `isProcOrder` does not entail `LPredClosed`. -/

/-! # 5. PART (B): `LPredClosedFlow` — dropping resource-free edges -/

def gobrCatFlow (GD : Gdexec) (x y : Geid) : Prop :=
  gppoCat GD x y ∨ gdepsRel GD x y ∨ grfe GD.gdG x y ∨
  gco GD.gdG x y ∨ (gfr GD.gdG x y ∧ gisW GD.gdG x = true)

def gobCatFlow (GD : Gdexec) (x y : Geid) : Prop := tc (gobrCatFlow GD) x y

theorem gobrCatFlowSub (GD : Gdexec) (x y : Geid) : gobrCatFlow GD x y → gobrCat GD x y := by
  rintro (h | h | h | h | ⟨h, _⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr h)))

theorem gobCatFlowSub (GD : Gdexec) (x y : Geid) : gobCatFlow GD x y → gobCat GD x y := by
  intro h
  induction h with
  | single h => exact gobCatStep GD _ _ (gobrCatFlowSub GD _ _ h)
  | tail _ h ih => exact gobCatTrans GD _ _ _ ih (gobCatStep GD _ _ (gobrCatFlowSub GD _ _ h))

/-- THE WEAKENED PREDECESSOR-CLOSURE. -/
def LPredClosedFlow (GD : Gdexec) (L : List Geid) : Prop :=
  ∀ n e, L[n]? = some e → ∀ e', gobCatFlow GD e' e → e' ∈ takeL L n

theorem LPredClosedToFlow (GD : Gdexec) (L : List Geid) :
    LPredClosed GD L → LPredClosedFlow GD L :=
  fun Hpc n e hn e' hf => Hpc n e hn e' (gobCatFlowSub GD e' e hf)

theorem LPredClosedGmoFlow (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) :
    LPredClosedFlow GD GD.gdG.gxGmo :=
  LPredClosedToFlow GD _ (LPredClosedGmo GD Hcons)

theorem axpolWfLOfPredClosedFlow [Axpol] (GD : Gdexec) (L : List Geid)
    (HsPolSub : ∀ e e', e' ∈ Axpol.sPol GD e → gobCatFlow GD e' e)
    (HlobpSub : ∀ e e', e' ∈ Axpol.lobp GD e → gobCatFlow GD e' e)
    (Hpc : LPredClosedFlow GD L) :
    axpolWfL GD L := by
  intro n e hn
  exact ⟨fun e' he' => Hpc n e hn e' (HsPolSub e e' he'),
    fun e' he' => Hpc n e hn e' (HlobpSub e e' he')⟩

/-! # 6. (prose, header) PART (C): the scheduler against `LPredClosedFlow` — status. -/

end Weak
