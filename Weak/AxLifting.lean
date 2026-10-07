/-
Weak: **LIFTING — threading the tied annotations through a run** (AxSL tier).

Rocq: `iris/AxLifting.v` @ xxvzwolszwmp.

## The Rocq header, in substance

LB via an AxSL-style base logic (design §1-L1, §0.5 "The step case").  Port of the
edge-annotation core of AxSL's `low/lifting.v` (`flow_eq_ea`, `ea_local_wf` and its per-step
update) over `AxWp`'s `wp` and `AxOpsem`'s `astepAny`/`astepProg`/`areadStep`/`awire`.

DELIVERED: `flowEqEa`, `eaLocalWf` (§2), the per-step update `eaLocalWfEvStep` built from the
induction `eaLocalWfUsedPart` (AxSL's `sswp_step` minus the WP unfolding, which `AxWp2`'s
`wpEvStep`/`wpSkipStep` already supply — design deviation 6), and two pure facts about
`AxOpsem.astepProg`'s row-position advance (`astepProgWdataSk`, `astepProgNodataK`).  Not
delivered in Rocq either: `wp_step`/`sswp_step` proper, `wp_steps*`, `wp_not_stuck`, the `wpc`
twins.

THE SHAPE.  `wpEvStep`/`wpSkipStep` deliver, for ONE step, the existential AxSL's `sswp_step`
derives (the annotation `R`, the `naUsed`/`naUnused` split, the new local state).  This file adds
the EDGE-ANNOTATION bookkeeping: `flowEqEa` wraps `flowEqDyn` with the deposit a node's own flow
equation owes its local-flow (lob′) successors (`lobSuccOf`, recovered from `gxGmo` since `lobp`
gives only predecessors); `eaLocalWf` threads this deposit map (AxSL's `sra`) across a step.  The
only per-step invariant is `dom ea = dom na` plus the per-node WF bound (AxSL's `na_full` dropped,
design deviation 3).

PARAMETRICITY LAW BEYOND `Axpol`: `axpolWf` — lob′-predecessors of an event are same-hart,
strictly earlier memory events (`lobp GD (i,k) ⊆ eidsBefore GD i k`), passed explicitly.

## Deviations from Rocq

1. NAMES: camelCase (map below); Rocq's notation `sra Σ` is the abbrev `Sra GF`.  Representation
   as `AxWp` deviation 2: `m1 ∪ m2` on maps ↦ `PartialMap.union`, `m1 ∖ m2` ↦
   `PartialMap.difference`, `dom` ↦ `FiniteMap.dom_set … : GSet Geid`, `from_option id emp` ↦
   `AxWp.fromOption (fun P => P) iprop(emp)`, `list_to_set (filter …)` ↦ `LawfulSet.ofList
   (List.filter …)`.  `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (as AxWp
   deviation 6).  Wand chains `A -∗ B -∗ C` are stated `⊢ A -∗ B -∗ C` (AxWp deviation 7).
2. O2 STAGE C (`notes/weak-port-o2-stageC.md` §D, "opax lifting") — THE HEADER FINDING CLOSES.
   There is no `AStepFetch`: a fetch is an `AStepAdmin` step at `lbAdmin true (LIFetch ..)`
   (AxOpsem deviation 2), handled by `wpSkipStep` with `atK` unchanged, like every other
   administrative label.  So Rocq's `wlabel_is_fetch` (the label filter its multi-step lemmas
   were to use to exclude the `AStepFetch` arm, and that `AxAdequacy`'s `astep_any_nf` uses) is
   DROPPED, and later files drop the fetch exclusion; `astepProgWdataSk`/`astepProgNodataK`
   lose Rocq's `T`/`img` oracle parameters and the fetch case of their proofs.  The remaining
   three-arm dispatch of the finding (read / write-or-fence-or-admin / wire) is unchanged.
3. Lean-only helpers (file-qualified): `AxLifting.depAt` (one summand of `eaDeposit`, so the
   lookups can be rewritten by name) with `AxLifting.depAtNone`/`depAtSomeNone`/`depAtSomeSome`;
   the `GMapF` lookup/dom helpers `AxLifting.lkUnionSingle`/`lkUnionSingleNe`/`lkUnionL`/
   `lkUnionR`/`lkDiff`/`domUnionG`; `AxLifting.flowEqEaDepMono` (a `flowEqEa` is monotone in
   its deposit) and `AxLifting.stepKey` (the per-key step of `eaLocalWfUsedPart`'s induction).

**Rocq → Lean name map.**  `sra` `Sra`, `lob_succ_of` `lobSuccOf`, `elem_of_lob_succ_of`
`elemOfLobSuccOf`, `axpol_wf` `axpolWf`, `axpol_wf_pred` `axpolWfPred`, `lob_succ_of_future`
`lobSuccOfFuture`, `lobp_sub_dom` `lobpSubDom`, `lob_succ_not_elem_of_dom`
`lobSuccNotElemOfDom`, `ea_deposit` `eaDeposit`, `ea_deposit_emp` `eaDepositEmp`,
`ea_deposit_ins_miss` `eaDepositInsMiss`, `ea_deposit_ins_hit` `eaDepositInsHit`,
`ea_deposit_delete_fresh` `eaDepositDeleteFresh`, `flow_eq_ea` `flowEqEa`,
`flow_eq_ea_of_flow_eq_dyn` `flowEqEaOfFlowEqDyn`, `ea_local_wf` `eaLocalWf`,
`ea_local_wf_fe_upgrade_miss` `eaLocalWfFeUpgradeMiss`, `ea_local_wf_used_part`
`eaLocalWfUsedPart`, `ea_local_wf_ev_step` `eaLocalWfEvStep`, `astep_prog_wdata_Sk`
`astepProgWdataSk`, `astep_prog_nodata_k` `astepProgNodataK`.

**Dropped:** `wlabel_is_fetch` (deviation 2); the §4 `Print Assumptions` block (the lint's axiom
check covers it).
-/
import Weak.AxWp2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. The lob-successor set, and the well-formedness law -/

/-- Rocq notation `sra Σ`: the edge-annotation (deposit) map. -/
abbrev Sra (GF : BundledGFunctors) := GMapF Geid (Mea GF)

section lobSucc
variable [Axpol]

/-- The successor direction of `lobp`, by a filter over the graph's memory events. -/
def lobSuccOf (GD : Gdexec) (e : Geid) : GSet Geid :=
  LawfulSet.ofList (GD.gdG.gxGmo.filter (fun e' => decide (e ∈ Axpol.lobp GD e')))

theorem elemOfLobSuccOf (GD : Gdexec) (e e' : Geid) :
    e' ∈ lobSuccOf GD e ↔ e ∈ Axpol.lobp GD e' ∧ e' ∈ GD.gdG.gxGmo := by
  unfold lobSuccOf
  rw [elemOfListToSet]
  simp only [List.mem_filter, decide_eq_true_eq]
  exact And.comm

/-- THE PARAMETRICITY LAW: lob′-predecessors are same-hart, strictly earlier memory events. -/
def axpolWf : Prop := ∀ GD i k, Axpol.lobp GD (i, k) ⊆ eidsBefore GD i k

theorem axpolWfPred (Hwf : axpolWf) (GD : Gdexec) (i k : Nat) (e' : Geid) :
    e' ∈ Axpol.lobp GD (i, k) → e'.1 = i ∧ e'.2 < k := by
  intro He'
  have h := (elemOfEidsBefore GD i k e').1 (Hwf GD i k e' He')
  exact ⟨h.1, h.2.1⟩

/-- A lob-successor of `(i,k)` is strictly later on the same hart. -/
theorem lobSuccOfFuture (Hwf : axpolWf) (GD : Gdexec) (i k : Nat) (eOut : Geid) :
    eOut ∈ lobSuccOf GD (i, k) → eOut.1 = i ∧ k < eOut.2 := by
  intro h
  obtain ⟨i', k'⟩ := eOut
  have hin := ((elemOfLobSuccOf GD (i, k) (i', k')).1 h).1
  have h2 := axpolWfPred Hwf GD i' k' (i, k) hin
  exact ⟨h2.1.symm, h2.2⟩

/-- Every lob-predecessor of the position about to be stepped is already in the domain. -/
theorem lobpSubDom (Hwf : axpolWf) (GD : Gdexec) (i k : Nat) (na : GSet Geid) :
    FiniteSet.filter (fun e : Geid => decide (e.1 = i)) na = eidsBefore GD i k →
    Axpol.lobp GD (i, k) ⊆ na := by
  intro Hna e' He'
  have h := Hwf GD i k e' He'
  rw [← Hna] at h
  exact (elemOfFilter.1 h).2

/-- No lob-successor of the position about to be stepped is in the domain yet. -/
theorem lobSuccNotElemOfDom (Hwf : axpolWf) (GD : Gdexec) (i k : Nat) (na : GSet Geid)
    (eOut : Geid) :
    FiniteSet.filter (fun e : Geid => decide (e.1 = i)) na = eidsBefore GD i k →
    eOut ∈ lobSuccOf GD (i, k) → eOut ∉ na := by
  intro Hna Hout Hin
  obtain ⟨hi, hk⟩ := lobSuccOfFuture Hwf GD i k eOut Hout
  have Hf : eOut ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i)) na :=
    elemOfFilter.2 ⟨by simp [hi], Hin⟩
  rw [Hna, elemOfEidsBefore] at Hf
  omega

end lobSucc

/-! ### Lean-only map helpers (file-qualified) -/

section mapHelpers
variable {V : Type _}

theorem AxLifting.lkUnionSingle (m : GMapF Geid V) (i : Geid) (x : V) :
    get? (PartialMap.union ({[i := x]} : GMapF Geid V) m) i = some x :=
  lookupUnionSomeL (M := GMapF Geid) lookupSingleton

theorem AxLifting.lkUnionSingleNe (m : GMapF Geid V) (i j : Geid) (x : V) (h : i ≠ j) :
    get? (PartialMap.union ({[i := x]} : GMapF Geid V) m) j = get? m j :=
  lookupUnionR (M := GMapF Geid) (lookupSingletonNe h)

theorem AxLifting.lkUnionL (m1 m2 : GMapF Geid V) (j : Geid) (x : V) (h : get? m1 j = some x) :
    get? (PartialMap.union m1 m2) j = some x :=
  lookupUnionSomeL (M := GMapF Geid) h

theorem AxLifting.lkUnionR (m1 m2 : GMapF Geid V) (j : Geid) (h : get? m1 j = none) :
    get? (PartialMap.union m1 m2) j = get? m2 j :=
  lookupUnionR (M := GMapF Geid) h

theorem AxLifting.lkDiff (m1 m2 : GMapF Geid V) (j : Geid) :
    get? (PartialMap.difference m1 m2) j = if (get? m2 j).isSome then none else get? m1 j :=
  lookupDifference (M := GMapF Geid)

theorem AxLifting.domUnionG (m1 m2 : GMapF Geid V) :
    (FiniteMap.dom_set (PartialMap.union m1 m2) : GSet Geid) =
      FiniteMap.dom_set m1 ∪ FiniteMap.dom_set m2 :=
  domUnion (M := GMapF Geid)

end mapHelpers

/-! # 2. The edge-annotation map `eaLocalWf` -/

section ea
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- Lean-only: one summand of the deposit — the piece `eOut`'s own `naUsed` earmarked for `e`. -/
def AxLifting.depAt (ea : Sra GF) (e eOut : Geid) : IProp GF :=
  AxWp.fromOption (fun gm => AxWp.fromOption (fun P => P) iprop(emp) (get? gm e)) iprop(emp)
    (get? ea eOut)

theorem AxLifting.depAtNone (ea : Sra GF) (e eOut : Geid) (h : get? ea eOut = none) :
    AxLifting.depAt ea e eOut = iprop(emp) := by
  unfold AxLifting.depAt; rw [h]; rfl

theorem AxLifting.depAtSomeNone (ea : Sra GF) (e eOut : Geid) (gm : Mea GF)
    (h : get? ea eOut = some gm) (h2 : get? gm e = none) :
    AxLifting.depAt ea e eOut = iprop(emp) := by
  unfold AxLifting.depAt; rw [h]; simp only [AxWp.fromOption]; rw [h2]

theorem AxLifting.depAtSomeSome (ea : Sra GF) (e eOut : Geid) (gm : Mea GF) (gv : IProp GF)
    (h : get? ea eOut = some gm) (h2 : get? gm e = some gv) :
    AxLifting.depAt ea e eOut = gv := by
  unfold AxLifting.depAt; rw [h]; simp only [AxWp.fromOption]; rw [h2]

/-- The deposit a node's own flow equation owes its lob′-successors. -/
def eaDeposit (ea : Sra GF) (S : GSet Geid) (e : Geid) : IProp GF :=
  iprop([∗set] eOut ∈ S, AxLifting.depAt ea e eOut)

theorem eaDepositEmp (ea : Sra GF) (S : GSet Geid) (e : Geid) :
    (∀ eOut, eOut ∈ S → get? ea eOut = none) → ⊢ eaDeposit ea S e := by
  intro Hout
  unfold eaDeposit
  refine BigSepS.bigSepS_emp.2.trans (BigSepS.bigSepS_mono fun {eOut} hin => ?_)
  rw [AxLifting.depAtNone ea e eOut (Hout eOut hin)]

/-- Inserting a fresh key whose bag has nothing for `e` leaves the deposit unchanged. -/
theorem eaDepositInsMiss (ea : Sra GF) (e' : Geid) (gm0 : Mea GF) (S : GSet Geid) (e : Geid) :
    get? ea e' = none → get? gm0 e = none →
    eaDeposit ea S e ⊢ eaDeposit (PartialMap.union {[e' := gm0]} ea) S e := by
  intro Hfresh Hgm
  unfold eaDeposit
  refine BigSepS.bigSepS_mono fun {eOut} _ => ?_
  by_cases hne : eOut = e'
  · subst hne
    rw [AxLifting.depAtNone ea e eOut Hfresh,
      AxLifting.depAtSomeNone _ e eOut gm0 (AxLifting.lkUnionSingle ea eOut gm0) Hgm]
  · have h : AxLifting.depAt (PartialMap.union {[e' := gm0]} ea) e eOut = AxLifting.depAt ea e eOut := by
      unfold AxLifting.depAt; rw [AxLifting.lkUnionSingleNe ea e' eOut gm0 (Ne.symm hne)]
    rw [h]

/-- Inserting a fresh key whose bag has `e` (value `gv`) grows the deposit by that piece. -/
theorem eaDepositInsHit (ea : Sra GF) (e' : Geid) (gm0 : Mea GF) (S : GSet Geid) (e : Geid)
    (gv : IProp GF) :
    get? ea e' = none → e' ∈ S → get? gm0 e = some gv →
    eaDeposit (PartialMap.union {[e' := gm0]} ea) S e ⊣⊢ iprop(gv ∗ eaDeposit ea (S \ {e'}) e) := by
  intro Hfresh Hin Hgv
  unfold eaDeposit
  have h := BigSepS.bigSepS_delete (Φ := fun eOut =>
    AxLifting.depAt (PartialMap.union {[e' := gm0]} ea) e eOut) Hin
  rw [AxLifting.depAtSomeSome _ e e' gm0 gv (AxLifting.lkUnionSingle ea e' gm0) Hgv] at h
  refine h.trans (sep_congr .rfl (BiEntails.of_eq (BigSepS.bigSepS_eq fun {eOut} hin' => ?_)))
  have hne : eOut ≠ e' := fun h' => (elemOfDifference.1 hin').2 (elemOfSingleton.2 h')
  unfold AxLifting.depAt
  rw [AxLifting.lkUnionSingleNe ea e' eOut gm0 (Ne.symm hne)]

/-- Removing a not-yet-annotated `e'` from the successor set does not change the deposit. -/
theorem eaDepositDeleteFresh (ea : Sra GF) (S : GSet Geid) (e' e : Geid) :
    get? ea e' = none → eaDeposit ea (S \ {e'}) e ⊣⊢ eaDeposit ea S e := by
  intro Hfresh
  unfold eaDeposit
  by_cases Hin : e' ∈ S
  · have h := BigSepS.bigSepS_delete (Φ := fun eOut => AxLifting.depAt ea e eOut) Hin
    rw [AxLifting.depAtNone ea e e' Hfresh] at h
    exact (h.trans emp_sep).symm
  · have hS : S \ {e'} = S := by
      rw [setEq]
      intro x
      rw [elemOfDifference, elemOfSingleton]
      constructor
      · exact fun h => h.1
      · intro hx
        exact ⟨hx, fun h => Hin (h ▸ hx)⟩
    rw [hS]
    exact ⟨.rfl, .rfl⟩

/-- `flowEqDyn`, with the conclusion carrying the deposit owed to `e`'s lob′-successors. -/
def flowEqEa (GD : Gdexec) (e : Geid) (sOb0 : GSet Geid) (flowIn : Mea GF) (ea : Sra GF)
    (R : IProp GF) : IProp GF :=
  flowEqDyn GD e sOb0 flowIn iprop(R ∗ eaDeposit ea (lobSuccOf GD e) e)

/-- Lean-only: a `flowEqEa` is monotone in its deposit. -/
theorem AxLifting.flowEqEaDepMono (GD : Gdexec) (e : Geid) (sOb0 : GSet Geid) (flowIn : Mea GF)
    (ea ea' : Sra GF) (R : IProp GF)
    (h : eaDeposit ea (lobSuccOf GD e) e ⊢ eaDeposit ea' (lobSuccOf GD e) e) :
    flowEqEa GD e sOb0 flowIn ea R ⊢ flowEqEa GD e sOb0 flowIn ea' R := by
  unfold flowEqEa
  iintro H
  ihave Hw : ▷ (R ∗ eaDeposit ea (lobSuccOf GD e) e -∗ R ∗ eaDeposit ea' (lobSuccOf GD e) e) $$ []
  · inext
    iintro ⟨HR, Hd⟩
    isplitl [HR]
    · iexact HR
    · iapply h
      iexact Hd
  iapply flowEqDynMono GD e sOb0 flowIn _ _ $$ Hw H

theorem flowEqEaOfFlowEqDyn (GD : Gdexec) (e : Geid) (sOb0 : GSet Geid) (flowIn : Mea GF)
    (ea : Sra GF) (R : IProp GF) :
    (∀ eOut, eOut ∈ lobSuccOf GD e → get? ea eOut = none) →
    ⊢ flowEqDyn GD e sOb0 flowIn R -∗ flowEqEa GD e sOb0 flowIn ea R := by
  intro Hout
  unfold flowEqEa
  iintro FE
  ihave Hw : ▷ (R -∗ R ∗ eaDeposit ea (lobSuccOf GD e) e) $$ []
  · inext
    iintro HR
    isplitl [HR]
    · iexact HR
    · iapply eaDepositEmp ea (lobSuccOf GD e) e Hout
  iapply flowEqDynMono GD e sOb0 flowIn _ _ $$ Hw FE

/-- AxSL's edge-annotation domain invariant. -/
def eaLocalWf (GD : Gdexec) (ea : Sra GF) (na : Mea GF) : IProp GF :=
  iprop(⌜(FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na⌝ ∗
    ([∗map] e ↦ gm ∈ ea, ⌜(FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e⌝) ∗
    ([∗map] e ↦ R ∈ na,
      AxWp.fromOption (fun flowIn => flowEqEa GD e (Axpol.sPol GD e) flowIn ea R) iprop(emp)
        (get? ea e)))

/-- Upgrading an `Hea_fe`-shaped big-op from `ea` to `{[e:=NAU]} ∪ ea` when every key misses
`NAU`. -/
theorem eaLocalWfFeUpgradeMiss (GD : Gdexec) (e : Geid) (ea : Sra GF) (NAU : Mea GF)
    (m : Mea GF) :
    get? ea e = none → e ∉ (FiniteMap.dom_set m : GSet Geid) →
    (∀ e0, e0 ∈ (FiniteMap.dom_set m : GSet Geid) → get? NAU e0 = none) →
    ([∗map] e0 ↦ R0 ∈ m,
      AxWp.fromOption (fun fi => flowEqEa GD e0 (Axpol.sPol GD e0) fi ea R0) iprop(emp)
        (get? ea e0)) ⊢
    ([∗map] e0 ↦ R0 ∈ m,
      AxWp.fromOption (fun fi => flowEqEa GD e0 (Axpol.sPol GD e0) fi
          (PartialMap.union {[e := NAU]} ea) R0) iprop(emp)
        (get? (PartialMap.union {[e := NAU]} ea) e0)) := by
  intro Hea Hnin Hmiss
  refine BigSepM.bigSepM_mono fun {e0 R0} hlk => ?_
  have hne : e ≠ e0 := fun h => Hnin (h ▸ elemOfDom2 hlk)
  rw [AxLifting.lkUnionSingleNe ea e e0 NAU hne]
  cases hea0 : get? ea e0 with
  | none =>
    simp only [AxWp.fromOption]
    exact .rfl
  | some fi0 =>
    simp only [AxWp.fromOption]
    exact AxLifting.flowEqEaDepMono GD e0 _ fi0 ea _ R0
      (eaDepositInsMiss ea e NAU _ e0 Hea (Hmiss e0 (elemOfDom2 hlk)))

/-- Lean-only: the per-key step of `eaLocalWfUsedPart`'s induction (Rocq's inner bullet). -/
theorem AxLifting.stepKey (GD : Gdexec) (e e0 : Geid) (na : Mea GF) (ea : Sra GF)
    (NAU : Mea GF) (R0 Pu0 Puu0 : IProp GF)
    (hR0 : get? na e0 = some R0) (hNAU : get? NAU e0 = some Pu0) (hea : get? ea e = none)
    (hlsc : e ∈ lobSuccOf GD e0) :
    ⊢ ▷ □ (AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) -∗ Pu0 ∗ Puu0) -∗
      AxWp.fromOption (fun fi => flowEqEa GD e0 (Axpol.sPol GD e0) fi ea R0) iprop(emp)
        (get? ea e0) -∗
      AxWp.fromOption (fun fi => flowEqEa GD e0 (Axpol.sPol GD e0) fi
          (PartialMap.union {[e := NAU]} ea) Puu0) iprop(emp) (get? ea e0) := by
  rw [hR0]
  cases hea0 : get? ea e0 with
  | none =>
    simp only [AxWp.fromOption]
    iintro _ H
    iexact H
  | some fi0 =>
    simp only [AxWp.fromOption]
    unfold flowEqEa
    iintro #Hstep Hfe
    ihave Hw : ▷ (R0 ∗ eaDeposit ea (lobSuccOf GD e0) e0 -∗
        Puu0 ∗ eaDeposit (PartialMap.union {[e := NAU]} ea) (lobSuccOf GD e0) e0) $$ []
    · inext
      iintro ⟨HR0, Hdep⟩
      ihave ⟨HPu0, HPuu0⟩ := Hstep $$ HR0
      isplitl [HPuu0]
      · iexact HPuu0
      · iapply (eaDepositInsHit ea e NAU (lobSuccOf GD e0) e0 Pu0 hea hlsc hNAU).2
        isplitl [HPu0]
        · iexact HPu0
        · iapply (eaDepositDeleteFresh ea (lobSuccOf GD e0) e e0 hea).2
          iexact Hdep
    iapply flowEqDynMono GD e0 (Axpol.sPol GD e0) fi0 _ _ $$ Hw Hfe

/-- The heart of `sswp_step`'s edge-annotation update (AxSL's induction on `na_unused`).
`NAU` is the full final `naUsed` of the step; `naUsed`/`naUnused` the slice still being
processed. -/
theorem eaLocalWfUsedPart (Hwf : axpolWf) (GD : Gdexec) (e : Geid) (na : Mea GF) (ea : Sra GF)
    (NAU : Mea GF) :
    (FiniteMap.dom_set NAU : GSet Geid) ⊆ Axpol.lobp GD e →
    (FiniteMap.dom_set NAU : GSet Geid) ⊆ FiniteMap.dom_set na →
    e ∉ (FiniteMap.dom_set na : GSet Geid) → get? ea e = none →
    e ∈ GD.gdG.gxGmo →
    ∀ (naUsed naUnused : Mea GF),
    naUsed ⊆ NAU →
    (FiniteMap.dom_set naUsed : GSet Geid) = FiniteMap.dom_set naUnused →
    ⊢ ([∗map] e0 ↦ Pu0;Puu0 ∈ naUsed;naUnused,
        ▷ □ (AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) -∗ Pu0 ∗ Puu0)) -∗
      ([∗map] e0 ↦ R0 ∈ PartialMap.difference na (PartialMap.difference NAU naUsed),
        AxWp.fromOption (fun fi => flowEqEa GD e0 (Axpol.sPol GD e0) fi ea R0) iprop(emp)
          (get? ea e0)) -∗
      ([∗map] e0 ↦ Puu0 ∈ naUnused,
        AxWp.fromOption (fun fi => flowEqEa GD e0 (Axpol.sPol GD e0) fi
            (PartialMap.union {[e := NAU]} ea) Puu0) iprop(emp) (get? ea e0)) ∗
      ([∗map] e0 ↦ R0 ∈ PartialMap.difference na NAU,
        AxWp.fromOption (fun fi => flowEqEa GD e0 (Axpol.sPol GD e0) fi
            (PartialMap.union {[e := NAU]} ea) R0) iprop(emp)
          (get? (PartialMap.union {[e := NAU]} ea) e0)) := by
  intro Hlob HdomNa Hnin HeaE Hgmo naUsed
  induction naUsed using mapInd with
  | hemp =>
    intro naUnused _ Hdom
    have h0 : PartialMap.difference NAU (∅ : Mea GF) = NAU := mapDifferenceEmpty (M := GMapF Geid)
    rw [h0]
    have hnu : naUnused = ∅ := by
      apply domEmptyInv (S := GSet Geid)
      rw [← Hdom]
      exact domEmpty (M := GMapF Geid)
    subst hnu
    have hnin' : e ∉ (FiniteMap.dom_set (PartialMap.difference na NAU) : GSet Geid) := by
      intro h
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 h)
      exact Hnin (elemOfDom2 ((lookupDifferenceSome (M := GMapF Geid)).1 hx).1)
    have hmiss : ∀ e0, e0 ∈ (FiniteMap.dom_set (PartialMap.difference na NAU) : GSet Geid) →
        get? NAU e0 = none := by
      intro e0 h
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 h)
      exact ((lookupDifferenceSome (M := GMapF Geid)).1 hx).2
    iintro _ Hrest
    isplitr
    · iapply BigSepM.bigSepM_empty.2
      itrivial
    · iapply eaLocalWfFeUpgradeMiss GD e ea NAU (PartialMap.difference na NAU) HeaE hnin' hmiss
      iexact Hrest
  | hins e0 Pu0 naUsed' hnin0 IH =>
    intro naUnused Hsub Hdom
    have hPu0 : get? (insert naUsed' e0 Pu0) e0 = some Pu0 := lookupInsert
    have hin0 : e0 ∈ (FiniteMap.dom_set naUnused : GSet Geid) := Hdom ▸ elemOfDom2 hPu0
    obtain ⟨Puu0, hPuu0⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 hin0)
    have Hsub' : naUsed' ⊆ NAU := fun j x h => Hsub j x (insertSubseteq hnin0 j x h)
    have hNAU0 : get? NAU e0 = some Pu0 := Hsub e0 Pu0 hPu0
    obtain ⟨R0, hR0⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 (HdomNa e0 (elemOfDom2 hNAU0)))
    have hrest0 : get? (PartialMap.difference na
        (PartialMap.difference NAU (insert naUsed' e0 Pu0))) e0 = some R0 := by
      rw [AxLifting.lkDiff, AxLifting.lkDiff, hPu0]
      simp [hR0]
    have hrestDel : delete (PartialMap.difference na
        (PartialMap.difference NAU (insert naUsed' e0 Pu0))) e0 =
        PartialMap.difference na (PartialMap.difference NAU naUsed') := by
      refine mapEq (M := GMapF Geid) fun j => ?_
      by_cases hj : j = e0
      · subst hj
        rw [lookupDelete, AxLifting.lkDiff, AxLifting.lkDiff, hnin0, hNAU0]
        simp
      · rw [lookupDeleteNe (Ne.symm hj), AxLifting.lkDiff, AxLifting.lkDiff, AxLifting.lkDiff,
          AxLifting.lkDiff, lookupInsertNe (Ne.symm hj)]
    have hdom' : (FiniteMap.dom_set naUsed' : GSet Geid) =
        FiniteMap.dom_set (delete naUnused e0) := by
      rw [setEq]
      intro x
      have hx := (setEq.1 Hdom) x
      rw [elemOfDom, elemOfDom] at hx ⊢
      by_cases hj : x = e0
      · subst hj
        rw [hnin0, lookupDelete]
      · rw [lookupDeleteNe (Ne.symm hj)]
        rw [lookupInsertNe (Ne.symm hj)] at hx
        exact hx
    have hlsc : e ∈ lobSuccOf GD e0 :=
      (elemOfLobSuccOf GD e0 e).2 ⟨Hlob e0 (elemOfDom2 hNAU0), Hgmo⟩
    have IH' := IH (delete naUnused e0) Hsub' hdom'
    rw [← hrestDel] at IH'
    rw [← insertDelete (M := GMapF Geid) hPuu0]
    iintro Hpaired Hrest
    icases (BigSepM2.bigSepM2_insert (M := GMapF Geid) hnin0 lookupDelete).1 $$ Hpaired
      with ⟨Hstep, Hpaired⟩
    icases (BigSepM.bigSepM_delete hrest0).1 $$ Hrest with ⟨Hfe0, Hrest⟩
    ihave ⟨HIH1, HIH2⟩ := IH' $$ Hpaired Hrest
    isplitl [Hstep Hfe0 HIH1]
    · iapply (BigSepM.bigSepM_insert (M := GMapF Geid) lookupDelete).2
      isplitl [Hstep Hfe0]
      · iapply AxLifting.stepKey GD e e0 na ea NAU R0 Pu0 Puu0 hR0 hNAU0 HeaE hlsc $$ Hstep Hfe0
      · iexact HIH1
    · iexact HIH2

/-- `sswp_step`'s edge-annotation update: `eaLocalWf` for the old `(ea, na)` and what
`wpEvStep` hands back at `(i,k)` give `eaLocalWf` for the new pair. -/
theorem eaLocalWfEvStep (Hwf : axpolWf) (GD : Gdexec) (i k : Nat) (na : Mea GF) (ea : Sra GF)
    (naUsed naUnused : Mea GF) (R : IProp GF) :
    gwf GD.gdG → gmemB GD.gdG (i, k) = true →
    FiniteSet.filter (fun e0 : Geid => decide (e0.1 = i)) (FiniteMap.dom_set na : GSet Geid) =
      eidsBefore GD i k →
    ⊢ naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused -∗
      eaLocalWf GD ea na -∗
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) naUsed R -∗
      eaLocalWf GD (PartialMap.union {[(i, k) := naUsed]} ea)
        (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) := by
  intro Hgwf Hmem Hna
  have Hgmo : (i, k) ∈ GD.gdG.gxGmo := by
    refine (Hgwf.2.1 (i, k)).2 ?_
    unfold gmemB at Hmem
    cases hl : gxLbl GD.gdG (i, k) with
    | none => rw [hl] at Hmem; cases Hmem
    | some l => rw [hl] at Hmem; exact ⟨l, hl, Hmem⟩
  have HlobDom := lobpSubDom Hwf GD i k _ Hna
  have HcurNin : (i, k) ∉ (FiniteMap.dom_set na : GSet Geid) := by
    intro Hin
    have Hf : (i, k) ∈ FiniteSet.filter (fun e0 : Geid => decide (e0.1 = i))
        (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hin⟩
    rw [Hna, elemOfEidsBefore] at Hf
    exact Nat.lt_irrefl _ Hf.2.1
  have HnaE : get? na (i, k) = none := notElemOfDom.1 HcurNin
  iintro #Hsplit Hwf FE
  ihave %Hd := naSplittingWfDom (Axpol.lobp GD (i, k)) na naUsed naUnused $$ Hsplit
  obtain ⟨HnauSub, HnauDomEq⟩ := Hd
  have HnauSubNa : (FiniteMap.dom_set naUsed : GSet Geid) ⊆ FiniteMap.dom_set na :=
    fun x hx => HlobDom x (HnauSub x hx)
  iunfold eaLocalWf at Hwf
  icases Hwf with ⟨%HeaDomEq, HeaLobWf, HeaFe⟩
  have HeaE : get? ea (i, k) = none := by
    apply (notElemOfDom (S := GSet Geid)).1
    rw [HeaDomEq]
    exact HcurNin
  have HnuE : get? naUnused (i, k) = none := by
    apply (notElemOfDom (S := GSet Geid)).1
    rw [← HnauDomEq]
    exact fun h => HcurNin (HnauSubNa _ h)
  have hea'e := AxLifting.lkUnionSingle ea (i, k) naUsed
  have hna'eq : PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na =
      insert (PartialMap.union naUnused na) (i, k) R := by
    rw [insertUnionSingletonL (M := GMapF Geid)]
    exact (mapUnionAssoc (M := GMapF Geid)).symm
  have hnone : get? (PartialMap.union naUnused na) (i, k) = none := by
    rw [AxLifting.lkUnionR _ _ _ HnuE]
    exact HnaE
  have hea'ins : PartialMap.union {[(i, k) := naUsed]} ea = insert ea (i, k) naUsed :=
    (insertUnionSingletonL (M := GMapF Geid)).symm
  have hout : ∀ eOut, eOut ∈ lobSuccOf GD (i, k) →
      get? (PartialMap.union {[(i, k) := naUsed]} ea) eOut = none := by
    intro eOut hout
    obtain ⟨hi, hk⟩ := lobSuccOfFuture Hwf GD i k eOut hout
    have hne : (i, k) ≠ eOut := fun h => by subst h; exact Nat.lt_irrefl _ hk
    rw [AxLifting.lkUnionSingleNe ea (i, k) eOut naUsed hne]
    cases hx : get? ea eOut with
    | none => rfl
    | some x =>
      exfalso
      have h1 : eOut ∈ (FiniteMap.dom_set na : GSet Geid) := by
        rw [← HeaDomEq]; exact elemOfDom2 hx
      have h2 : eOut ∈ FiniteSet.filter (fun e0 : Geid => decide (e0.1 = i))
          (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp [hi], h1⟩
      rw [Hna, elemOfEidsBefore] at h2
      omega
  have hnaEq : PartialMap.union naUnused na =
      PartialMap.union naUnused (PartialMap.difference na naUsed) := by
    refine mapEq (M := GMapF Geid) fun j => ?_
    cases hj : get? naUnused j with
    | some x => rw [AxLifting.lkUnionL _ _ _ x hj, AxLifting.lkUnionL _ _ _ x hj]
    | none =>
      rw [AxLifting.lkUnionR _ _ _ hj, AxLifting.lkUnionR _ _ _ hj, AxLifting.lkDiff]
      have hj' : get? naUsed j = none := by
        apply (notElemOfDom (S := GSet Geid)).1
        rw [HnauDomEq]
        exact (notElemOfDom (S := GSet Geid)).2 hj
      rw [hj']
      rfl
  have hdisj : naUnused ##ₘ PartialMap.difference na naUsed := by
    refine (mapDisjointSpec (M := GMapF Geid)).2 fun j x y h1 h2 => ?_
    have h2' := ((lookupDifferenceSome (M := GMapF Geid)).1 h2).2
    have : j ∈ (FiniteMap.dom_set naUsed : GSet Geid) := by
      rw [HnauDomEq]; exact elemOfDom2 h1
    rw [elemOfDom, h2'] at this
    cases this
  have hdiff : PartialMap.difference na (PartialMap.difference naUsed naUsed) = na := by
    have h1 : PartialMap.difference naUsed naUsed = (∅ : Mea GF) :=
      mapDifferenceDiag (M := GMapF Geid)
    rw [h1]
    exact mapDifferenceEmpty (M := GMapF Geid)
  unfold eaLocalWf
  isplitr
  · ipureintro
    rw [AxLifting.domUnionG, AxLifting.domUnionG, AxLifting.domUnionG, domSingleton,
      domSingleton, HeaDomEq, ← HnauDomEq]
    rw [setEq]
    intro x
    simp only [elemOfUnion]
    constructor
    · rintro (h | h)
      · exact .inl (.inl h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inl h
      · exact .inr (HnauSubNa x h)
      · exact .inr h
  isplitl [HeaLobWf]
  · rw [hea'ins]
    iapply (BigSepM.bigSepM_insert HeaE).2
    isplitr
    · ipureintro
      exact HnauSub
    · iexact HeaLobWf
  · rw [hna'eq]
    iapply (BigSepM.bigSepM_insert hnone).2
    isplitl [FE]
    · rw [hea'e]
      simp only [AxWp.fromOption]
      iapply flowEqEaOfFlowEqDyn GD (i, k) _ naUsed _ R hout
      iexact FE
    · rw [hnaEq]
      iapply (BigSepM.bigSepM_union (M := GMapF Geid) hdisj).2
      iunfold naSplittingWf at Hsplit
      icases Hsplit with ⟨-, #Hpaired⟩
      have H := eaLocalWfUsedPart Hwf GD (i, k) na ea naUsed HnauSub HnauSubNa HcurNin HeaE Hgmo
        naUsed naUnused (fun _ _ h => h) HnauDomEq
      rw [hdiff] at H
      ihave ⟨H1, H2⟩ := H $$ Hpaired HeaFe
      isplitl [H1]
      · iapply BigSepM.bigSepM_mono ?_ $$ H1
        intro e0 v hlk
        have hne : (i, k) ≠ e0 := fun h => by
          subst h
          rw [HnuE] at hlk
          cases hlk
        rw [AxLifting.lkUnionSingleNe ea (i, k) e0 naUsed hne]
      · iexact H2

end ea

/-! # 3. The single step: row-position facts of `AxOpsem.astepProg` -/

/-- A write-shaped instance label always consumes its row position. -/
theorem astepProgWdataSk (row : List Lbl) (s : Athread) (l : Wlabel) (s' : Athread)
    (data : List (BitVec 8)) :
    AxOpsem.astepProg row s l s' → wlWdata l = some data → s'.atK = s.atK + 1 := by
  intro h hwd
  cases h with
  | AStepAdmin p k d l p' d' ha hs =>
    cases l <;> simp [lbAdmin, wlWdata] at ha hwd
  | AStepWrite => rfl
  | AStepFence p k d l lb p' d' hrow hs1 hid hs =>
    cases l <;> simp [wlFence, wlWdata] at hs1 hwd

theorem astepProgNodataK (row : List Lbl) (s : Athread) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row s l s' → wlWdata l = none →
    s'.atK = s.atK ∨ s'.atK = s.atK + 1 := by
  intro h _
  rcases astepProgK row s l s' h with h1 | ⟨h1, _⟩
  · exact .inl h1
  · exact .inr h1

end Weak
