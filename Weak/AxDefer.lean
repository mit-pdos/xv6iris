/-
Weak: **constraint F — adequacy with DEFERRED reads (the ctrl gate), phase 2** (AxSL tier).

Rocq: `iris/AxDefer.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Tier-A adequacy is proved for WPds WITHOUT a gate: `AxWpD.wpd` has no `LCtrl` arm handing the
continuation a fact, so a kernel branch on a loaded value can only be verified for EVERY value.
The design's gate (`AxGateWp`) lets the continuation assume the PURE facts `φ r` of the
annotations of the gate's sources `r`; this file states and proves the PHASE-2 half of the
missing adequacy and pins what policy/instance must satisfy.

  (A) gate facts are used by later flow equations / the row-end post; no new WPd arm.
  (B) phase 1 yields the todo list `ordEaTodoG`: `e`'s flow equation guarded by
      `gateOk gsrc φ e` (`gsrc e` = sources of every gate po-before `e`).
  (C) PHASE 2 (`adequacyOrdG`, §1): over ANY processing order `L` (a permutation of `gxGmo`)
      with `axpolWfL GD L` and `gsrcBefore L gsrc`, the walk closes AND every gate fact holds.
      `L := gxGmo` recovers the gate-free route whenever every gate source is gmo-before what
      it gates (§2 `gsrcBeforeGmo`); this holds for ACQUIRE-read sources (`gsrcAqGmo`).
  (D) a gate on a PLAIN load can have a po-later read `d` gmo-BEFORE the source `r` (deferred
      read); a policy handing `d` (transitively) to `r` makes (C)'s two order premises jointly
      unsatisfiable (`noOrderPrefixPol`, `noOrderCycle`).  Not a proof artifact (AxDefer2).
  (E) instance rules must hold for processed sets that are not gmo prefixes (AxDefer2/4).

  §1  `gateOk`, `gsrcBefore`, `ordEaTodoG`(`Cons`), `gateSrcPure`, `bagGateOk`,
      `adequacyOrdAuxG`, `adequacyOrdG`.
  §2  `gsrcBeforeGmo`, `gsrcAqGmo`, `gsrcBeforeAq`, `adequacyOrdGAq`, `noOrderCycle`,
      `noOrderPrefixPol`.

## Deviations from Rocq

1. Representation as `AxAdequacyL` deviation 1 (`list_to_set` ↦ `LawfulSet.ofList`, `take_L` ↦
   `takeL`, `from_option id emp` ↦ `AxWp.fromOption (fun P => P) iprop(emp)`, `dom` ↦
   `FiniteMap.dom_set`, `≡ₚ` ↦ `List.Perm`, `|={⊤}[∅]▷=>^n` ↦ `|={⊤}[∅]▷=>^[n]`,
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`); wand chains `⊢ A -∗ B -∗ C`.
2. `bagGateOk`'s pure extraction is classical (case on `gateOk`; a failing source's
   annotation entails `False`) instead of Rocq's `persistent_and_sep_1` + `iIntros (r Hr)`
   (IProp has no `BIPureForall`); same statement.
3. The induction on `k = length L - n` is the Lean-only `AxDefer.ordAuxK` (as
   `AxAdequacyL.ordAuxK`); Lean-only helpers `AxDefer.ordAuxK`, `AxDefer.bagGateOkAll`
   (the gate facts of every event of `L` from the full bag, used by `adequacyOrdG`'s
   post) and `AxDefer.stepFupdNMono` (monotonicity of `|={⊤}[∅]▷=>^[n]`).
4. Rocq's `gpo` is Lean's `WeakRvwmoGraph.gpo`; `gwf_gmo_mem` is `gwf`'s second conjunct.
5. The WP step clause (`AxWp2.wpPreStepDef`) is never introduced or eliminated here: phase 2
   only consumes `flowEqEa`/`flowEqDyn` (via the `ordEaTodoG` todo list), so the pending Q8
   fetch-pin rework does not touch this file.

**Rocq → Lean name map.**  `gate_ok` `gateOk`, `gsrc_before` `gsrcBefore`, `ord_ea_todo_G`
`ordEaTodoG`, `ord_ea_todo_G_cons` `ordEaTodoGCons`, `gate_src_pure` `gateSrcPure`,
`bag_gate_ok` `bagGateOk`, `adequacy_ord_aux_G` `adequacyOrdAuxG`, `adequacy_ord_G`
`adequacyOrdG`, `gsrc_before_gmo` `gsrcBeforeGmo`, `gsrc_aq_gmo` `gsrcAqGmo`,
`gsrc_before_aq` `gsrcBeforeAq`, `adequacy_ord_G_aq` `adequacyOrdGAq`, `no_order_cycle`
`noOrderCycle`, `no_order_prefix_pol` `noOrderPrefixPol`.

**Dropped:** only the `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxAdequacyL
import Weak.AxBridge

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. Gated phase 2 -/

/-- `gsrc e`: the sources of every gate po-before `e`; `φ r`: the pure fact of `r`'s annotation. -/
def gateOk (gsrc : Geid → GSet Geid) (φ : Geid → Prop) (e : Geid) : Prop :=
  ∀ r, r ∈ gsrc e → φ r

/-- Every gate source is processed before every event it gates. -/
def gsrcBefore (L : List Geid) (gsrc : Geid → GSet Geid) : Prop :=
  ∀ n e, L[n]? = some e → gsrc e ⊆ takeL L n

/-- Lean-only: monotonicity of the iterated step-update. -/
theorem AxDefer.stepFupdNMono {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] {n : Nat} {P Q : IProp GF} (h : P ⊢ Q) :
    iprop(|={⊤}[∅]▷=>^[n] P) ⊢ iprop(|={⊤}[∅]▷=>^[n] Q) :=
  sep_emp.2.trans ((sep_mono step_fupdN_wand (wand_intro (emp_sep.1.trans h))).trans wand_elim_left)

section gated
variable [Axpol]
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF]

/-- The phase-1 output of a gated WPd: `e`'s flow equation may assume the gate facts. -/
def ordEaTodoG (GD : Gdexec) (gsrc : Geid → GSet Geid) (φ : Geid → Prop)
    (ea : Sra GF) (na : Mea GF) (L : List Geid) (n : Nat) : IProp GF :=
  iprop([∗list] e0 ∈ L.drop n,
    AxWp.fromOption (fun R0 => AxWp.fromOption
        (fun flowIn => iprop(⌜gateOk gsrc φ e0⌝ -∗ flowEqEa GD e0 (Axpol.sPol GD e0) flowIn ea R0))
        iprop(emp) (get? ea e0))
      iprop(emp) (get? na e0))

theorem ordEaTodoGCons (GD : Gdexec) (gsrc : Geid → GSet Geid) (φ : Geid → Prop)
    (ea : Sra GF) (na : Mea GF) (L : List Geid) (n : Nat) (e : Geid) :
    L[n]? = some e →
    ordEaTodoG GD gsrc φ ea na L n ⊣⊢
    iprop(AxWp.fromOption (fun R0 => AxWp.fromOption
          (fun flowIn => iprop(⌜gateOk gsrc φ e⌝ -∗ flowEqEa GD e (Axpol.sPol GD e) flowIn ea R0))
          iprop(emp) (get? ea e))
        iprop(emp) (get? na e)
      ∗ ordEaTodoG GD gsrc φ ea na L (n + 1)) := by
  intro hn
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hn
  have hd : L.drop n = e :: L.drop (n + 1) := by
    rw [List.drop_eq_getElem_cons hlt, hget]
  unfold ordEaTodoG
  rw [hd]
  exact BigSepL.bigSepL_cons

/-- A gate source's annotation ENTAILS its pure fact. -/
def gateSrcPure (na : Mea GF) (gsrc : Geid → GSet Geid) (φ : Geid → Prop) : Prop :=
  ∀ e r, r ∈ gsrc e → ∃ R, get? na r = some R ∧ (R ⊢ iprop(⌜φ r⌝))

/-- The validated bag yields the gate facts of any event whose sources are all in it —
without consuming the bag. -/
theorem bagGateOk (S : GSet Geid) (na : Mea GF) (gsrc : Geid → GSet Geid) (φ : Geid → Prop)
    (e : Geid) (Hpure : gateSrcPure na gsrc φ) (Hsub : gsrc e ⊆ S) :
    ([∗set] e0 ∈ S, AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ⊢
    iprop(⌜gateOk gsrc φ e⌝ ∗
      [∗set] e0 ∈ S, AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) := by
  by_cases h : gateOk gsrc φ e
  · exact emp_sep.2.trans (sep_mono (pure_intro h) .rfl)
  · have hex : ∃ r, r ∈ gsrc e ∧ ¬ φ r :=
      Classical.byContradiction fun hne =>
        h (fun r hr => Classical.byContradiction fun hn => hne ⟨r, hr, hn⟩)
    obtain ⟨r, hr, hn⟩ := hex
    obtain ⟨R, hR, hRφ⟩ := Hpure e r hr
    refine (BigSepS.bigSepS_delete (Hsub r hr)).1.trans ?_
    refine sep_elim_left.trans ?_
    rw [hR]
    exact hRφ.trans (pure_elim' fun hφ => absurd hφ hn)

/-- Lean-only: the gate facts of every event of `L`, from the full bag. -/
theorem AxDefer.bagGateOkAll (L : List Geid) (na : Mea GF) (gsrc : Geid → GSet Geid)
    (φ : Geid → Prop) (Hbefore : gsrcBefore L gsrc) (Hpure : gateSrcPure na gsrc φ) :
    ([∗set] e0 ∈ (LawfulSet.ofList L : GSet Geid),
        AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ⊢
    iprop(⌜∀ e, e ∈ L → gateOk gsrc φ e⌝ ∗
      [∗set] e0 ∈ (LawfulSet.ofList L : GSet Geid),
        AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) := by
  by_cases h : ∀ e, e ∈ L → gateOk gsrc φ e
  · exact emp_sep.2.trans (sep_mono (pure_intro h) .rfl)
  · have hex : ∃ e, e ∈ L ∧ ¬ gateOk gsrc φ e :=
      Classical.byContradiction fun hne =>
        h (fun e he => Classical.byContradiction fun hn => hne ⟨e, he, hn⟩)
    obtain ⟨e, he, hn⟩ := hex
    obtain ⟨n, hnl⟩ := elem_of_list_lookup_1 he
    have Hsub : gsrc e ⊆ (LawfulSet.ofList L : GSet Geid) := by
      intro r hr
      have hin := Hbefore n e hnl r hr
      unfold takeL at hin
      rw [elemOfListToSet] at hin ⊢
      exact List.mem_of_mem_take hin
    refine (bagGateOk _ na gsrc φ e Hpure Hsub).trans ?_
    refine sep_elim_left.trans ?_
    exact pure_elim' fun hφ => absurd hφ hn

/-- Lean-only: `adequacyOrdAuxG`'s induction, on `k = length L - n`. -/
theorem AxDefer.ordAuxK (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo)
    (Hpol : axpolWfL GD L)
    (gsrc : Geid → GSet Geid) (φ : Geid → Prop)
    (Hbefore : gsrcBefore L gsrc)
    (na : Mea GF) (ea : Sra GF)
    (Hpure : gateSrcPure na gsrc φ)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList L : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0) :
    ∀ k n, k = L.length - n → n ≤ L.length →
    ⊢ ordEaTodoG GD gsrc φ ea na L n -∗
      (∃ (σ : AxirisG.obSt GF), AxirisG.obStInterp GD σ (takeL L n) ∗
        ([∗set] e0 ∈ takeL L n, AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ∗
        ([∗set] e0 ∈ takeL L n, ordPending GD ea (takeL L n) e0)) -∗
      |={⊤}[∅]▷=>^[k]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList L) ∗
          [∗set] e0 ∈ (LawfulSet.ofList L : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) := by
  have Hnd : L.Nodup := Hperm.nodup_iff.2 Hcons.1.1
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
    have Hgate := bagGateOk (takeL L n) na gsrc φ e Hpure (Hbefore n e He)
    rw [AxAdequacy.stepFupdNSucc]
    iintro Htodo ⟨%σ, Hob, Hbag, Hpend⟩
    icases (ordEaTodoGCons GD gsrc φ ea na L n e He).1 $$ Htodo with ⟨Hhd, Htodo⟩
    isimp only [HnaE, HeaE, AxWp.fromOption] at Hhd
    -- THE GATE: the head's sources are already validated.
    ihave ⟨%Hg, Hbag⟩ := Hgate $$ Hbag
    ispecialize Hhd $$ %Hg
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

/-- THE INDUCTION — `adequacyOrdAuxL` with the head's gate facts extracted from the bag. -/
theorem adequacyOrdAuxG (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo)
    (Hpol : axpolWfL GD L)
    (gsrc : Geid → GSet Geid) (φ : Geid → Prop)
    (Hbefore : gsrcBefore L gsrc)
    (na : Mea GF) (ea : Sra GF)
    (Hpure : gateSrcPure na gsrc φ)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList L : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0) :
    ∀ n, n ≤ L.length →
    ⊢ ordEaTodoG GD gsrc φ ea na L n -∗
      (∃ (σ : AxirisG.obSt GF), AxirisG.obStInterp GD σ (takeL L n) ∗
        ([∗set] e0 ∈ takeL L n, AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ∗
        ([∗set] e0 ∈ takeL L n, ordPending GD ea (takeL L n) e0)) -∗
      |={⊤}[∅]▷=>^[L.length - n]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList L) ∗
          [∗set] e0 ∈ (LawfulSet.ofList L : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) :=
  fun n hn => AxDefer.ordAuxK GD Hcons L Hperm Hpol gsrc φ Hbefore na ea Hpure HdomEq Hdom
    HeaLob _ n rfl hn

/-- THE WRAPPER: the walk closes over `L`, and EVERY gate fact holds (item (A)). -/
theorem adequacyOrdG (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo)
    (Hpol : axpolWfL GD L)
    (gsrc : Geid → GSet Geid) (φ : Geid → Prop)
    (Hbefore : gsrcBefore L gsrc)
    (na : Mea GF) (ea : Sra GF)
    (Hpure : gateSrcPure na gsrc φ)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList L : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ordEaTodoG GD gsrc φ ea na L 0 -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[L.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList L) ∗
          ([∗set] e0 ∈ (LawfulSet.ofList L : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ∗
          ⌜∀ e, e ∈ L → gateOk gsrc φ e⌝ := by
  have h := adequacyOrdAuxG GD Hcons L Hperm Hpol gsrc φ Hbefore na ea Hpure HdomEq Hdom HeaLob
    0 (Nat.zero_le _)
  rw [Nat.sub_zero, takeL0] at h
  have hall := AxDefer.bagGateOkAll L na gsrc φ Hbefore Hpure
  have hpost :
      iprop(∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList L) ∗
          [∗set] e0 ∈ (LawfulSet.ofList L : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ⊢
      iprop(∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList L) ∗
          ([∗set] e0 ∈ (LawfulSet.ofList L : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ∗
          ⌜∀ e, e ∈ L → gateOk gsrc φ e⌝) := by
    iintro ⟨%σ, Hob, Hbag⟩
    ihave ⟨%Hall, Hbag⟩ := hall $$ Hbag
    iexists σ
    isplitl [Hob]
    · iexact Hob
    isplitl [Hbag]
    · iexact Hbag
    · ipureintro
      exact Hall
  iintro Htodo Hob
  iapply (AxDefer.stepFupdNMono (n := L.length) hpost)
  iapply h $$ Htodo
  iexists σ0
  isplitl [Hob]
  · iexact Hob
  isplitl
  · iapply BigSepS.bigSepS_empty.2
    itrivial
  · iapply BigSepS.bigSepS_empty.2
    itrivial

end gated

/-! # 2. Which orders exist -/

/-- Gate-free case: every source gmo-before what it gates ⇒ `gxGmo` itself works. -/
theorem gsrcBeforeGmo (G : Gexec) (gsrc : Geid → GSet Geid) :
    G.gxGmo.Nodup →
    (∀ e r, e ∈ G.gxGmo → r ∈ gsrc e → gmoLt G r e) →
    gsrcBefore G.gxGmo gsrc := by
  intro hnd hlt n e hn r hr
  have he : e ∈ G.gxGmo := elem_of_list_lookup_2 hn
  obtain ⟨hr', _, hpos⟩ := hlt e r he hr
  rw [gposOfLookup G n e hnd hn] at hpos
  unfold takeL
  rw [elemOfListToSet]
  exact AxAdequacy.memTakeOfLookup (gposElemLookup G r hr') hpos

/-- THE ACQUIRE-LOOP SHAPE: acquire-read sources po-before what they gate are gmo-before it
(riscv.cat rule 5, `gacqPo`) — no read is ever deferred. -/
theorem gsrcAqGmo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (gsrc : Geid → GSet Geid) :
    (∀ e r, r ∈ gsrc e → WeakRvwmoGraph.gpo GD.gdG r e ∧ glblIs GD.gdG r lbIsR ∧
                         glblIs GD.gdG r lbAq) →
    ∀ e r, e ∈ GD.gdG.gxGmo → r ∈ gsrc e → gmoLt GD.gdG r e := by
  intro Haq e r He Hr
  obtain ⟨Hpo, Hrd, Hacq⟩ := Haq e r Hr
  exact Hcons.2.1 r e (.inl (.inr (.inr (.inr (.inr (.inl
    ⟨Hpo, Hrd, Hacq, (Hcons.1.2.1 e).1 He⟩))))))

theorem gsrcBeforeAq (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (gsrc : Geid → GSet Geid) :
    (∀ e r, r ∈ gsrc e → WeakRvwmoGraph.gpo GD.gdG r e ∧ glblIs GD.gdG r lbIsR ∧
                         glblIs GD.gdG r lbAq) →
    gsrcBefore GD.gdG.gxGmo gsrc :=
  fun Haq => gsrcBeforeGmo GD.gdG gsrc Hcons.1.1 (gsrcAqGmo GD Hcons gsrc Haq)

section gatedAq
variable [Axpol]
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF]

/-- For acquire-sourced gates, gated phase 2 runs over `gxGmo` with ANY gmo-bounded policy. -/
theorem adequacyOrdGAq (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (HsPolGmo : ∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e)
    (HlobpGmo : ∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e)
    (gsrc : Geid → GSet Geid) (φ : Geid → Prop)
    (Haq : ∀ e r, r ∈ gsrc e → WeakRvwmoGraph.gpo GD.gdG r e ∧ glblIs GD.gdG r lbIsR ∧
                             glblIs GD.gdG r lbAq)
    (na : Mea GF) (ea : Sra GF)
    (Hpure : gateSrcPure na gsrc φ)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ordEaTodoG GD gsrc φ ea na GD.gdG.gxGmo 0 -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[GD.gdG.gxGmo.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList GD.gdG.gxGmo) ∗
          ([∗set] e0 ∈ (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ∗
          ⌜∀ e, e ∈ GD.gdG.gxGmo → gateOk gsrc φ e⌝ := by
  have Hnd := Hcons.1.1
  have Hpol : axpolWfL GD GD.gdG.gxGmo := by
    intro n e hn
    exact ⟨fun e' he' => gmoLtTake GD n e e' Hnd hn (HsPolGmo e e' he'),
      fun e' he' => gmoLtTake GD n e e' Hnd hn (HlobpGmo e e' he')⟩
  exact adequacyOrdG GD Hcons _ (List.Perm.refl _) Hpol gsrc φ
    (gsrcBeforeAq GD Hcons gsrc Haq) na ea Hpure HdomEq Hdom HeaLob σ0

end gatedAq

/-- THE OBSTRUCTION: a deferred read `d` (gated by `r`) handed to `r` makes the two order
premises jointly unsatisfiable, for EVERY order. -/
theorem noOrderCycle [Axpol] (GD : Gdexec) (L : List Geid) (gsrc : Geid → GSet Geid)
    (d r : Geid) :
    L.Nodup → d ∈ L → r ∈ L → r ∈ gsrc d → d ∈ Axpol.sPol GD r →
    ¬ (gsrcBefore L gsrc ∧ axpolWfL GD L) := by
  rintro Hnd Hd Hr Hrd Hdr ⟨Hbef, Hpol⟩
  obtain ⟨nd, Hnd'⟩ := elem_of_list_lookup_1 Hd
  obtain ⟨nr, Hnr⟩ := elem_of_list_lookup_1 Hr
  have H1 := Hbef nd d Hnd' r Hrd
  have H2 := (Hpol nr r Hnr).1 d Hdr
  unfold takeL at H1 H2
  rw [elemOfListToSet] at H1 H2
  obtain ⟨i, hi, hil⟩ := AxAdequacy.memTake H1
  obtain ⟨j, hj, hjl⟩ := AxAdequacy.memTake H2
  have e1 := NoDup_lookup Hnd hil Hnr
  have e2 := NoDup_lookup Hnd hjl Hnd'
  omega

theorem noOrderPrefixPol [Axpol] (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo) (gsrc : Geid → GSet Geid)
    (Hpref : ∀ e, e ∈ GD.gdG.gxGmo →
       (LawfulSet.ofList (gmoPrefix GD.gdG e) : GSet Geid) ⊆ Axpol.sPol GD e)
    (d r : Geid) :
    r ∈ gsrc d → gmoLt GD.gdG d r →
    ¬ (gsrcBefore L gsrc ∧ axpolWfL GD L) := by
  intro Hrd Hlt
  obtain ⟨Hd, Hr, Hpos⟩ := Hlt
  refine noOrderCycle GD L gsrc d r (Hperm.nodup_iff.2 Hcons.1.1) (Hperm.mem_iff.2 Hd)
    (Hperm.mem_iff.2 Hr) Hrd ?_
  exact Hpref r Hr d (elemOfListToSet.2 ((gmoPrefixSpec GD.gdG r d Hcons.1 Hr).2 ⟨Hd, Hr, Hpos⟩))

end Weak
