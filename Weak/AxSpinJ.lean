/-
Weak: Phase 3 of the spinlock plan, JOINT step [R3.3] -- `tierAAdequacyAnnGateJointT`, the
tagged gated tier-A adequacy (`AxSpinGate.tierAAdequacyAnnGateT`, same premises) with iProp
per-hart posts `Φ : Agent → Athread → IProp GF` and a JOINT final step
  `Hjoint : ∀ Hinv Hann nm, ⊢ ([∗list] i ∈ harts, Φ Hinv Hann nm i (sN i)) ==∗ ⌜P⌝`
concluding `P`.

Rocq: `iris/AxSpinJ.v` @ xxvzwolszwmp.

## The Rocq header, in substance

The ghost names `nm` and the annotation name are allocated INSIDE the soundness proof
(`HobAlloc`, `annotInterpAlloc`), exactly as in `AxDefer5.tierAAdequacyAnnLM`; `Hjoint`/`Hwp`
are quantified over them only because they are chosen there.

HOW.  `tierAAdequacyAnnCoreJointLM` is `AxDefer5.tierAAdequacyAnnCoreLM` with the final step
changed (the phases are REUSED unchanged: `wpdHartsNstepsM` (phase 1, all harts, one shared
`na`), `wpdMPostAtRowEnd` (now for EVERY hart, not one), `ordEaTodoLOfEaLocalWf` +
`adequacyOrdLWf` (phase 2)).  The validated bag `[∗map] e ↦ R ∈ na, R` is SPLIT per hart
(`bagSplitHarts`: every key's hart is in `harts`, `harts.Nodup`), and each hart's `postLifting`
(consumes only its own slice and hands `annotInterp na` back) is applied IN TURN
(`postLiftingsJoint`); the collected `▷ |==> [∗list] Φ i (sN i)` then feeds `Hjoint` inside the
final `|==>`.  `tierAAdequacyAnnJointLM`/`L`: the Prop wrappers (model-generic / riscv.cat);
`tierAAdequacyAnnGateJointT`: the tagged gated instance (via `AxSpinGate.LcanonOkGate'`, as
`tierAAdequacyAnnGateT`).  REGRESSION CHECK: `tierAAdequacyAnnGateTOfJoint` re-derives
`tierAAdequacyAnnGateT`'s EXACT statement from the joint theorem (`Φ i s := ⌜post i s⌝`,
`P := ∀ i ∈ harts, post i (sN i)`).

## Deviations from Rocq

1. Vocabulary as AxDefer5/AxSpinGate: `≡ₚ` ↦ `List.Perm`, `list_to_set` ↦ `LawfulSet.ofList`,
   `|={⊤}[∅]▷=>^n` ↦ `|={⊤}[∅]▷=>^[n]`, `bool_decide (e.1 = i)` ↦ `if e.1 = i` (as
   `postLifting`), wand chains `⊢ A -∗ B -∗ C`.
2. O2 STAGE C (as AxDefer5 deviation 2): the section parameter `T` is gone; `tierAAstep GD nm i`
   and `tierAWpd`/`tierAWpdM GD N obSt0 obStInterp0 nm …`.
3. `AxGJ` (a Rocq `Local Instance` := `AxGA2 … nm`) is installed with `letI` at
   AxDefer5's `axGA5` (= `axGA2`); no new def.
4. The core is stated for `[InvGS_gen hlc GF]`, any `hlc` (Rocq: `HasNoLc`); the wrappers'
   soundness runs at `.hasNoLC` (as AxDefer5).  `postLiftingsJoint` needs no `InvGS` (Rocq's
   section context has one; `postLifting` does not use it).
5. Section `Context`s are explicit arguments in AxDefer5's order (`GD N obSt0 obStInterp0 init`,
   then `nm`, then `M [GModel M]`; §3: `GT …`); `[Axpol]` is an instance argument.  Rocq's
   `Φ : invGS_gen HasNoLc Σ → axannotGS Σ → N → …` is the same explicit function type; `Hwp`
   and `Hjoint` bind the instances as `∀ [Hinv : …] [Hann : …]`.
6. `sepOneHart`/`bagSplitHarts` are stated for any `GF` (Rocq: any `Σ`); `bagSplitHarts`'s
   domain premise is over `FiniteMap.dom_set na`.

**Rocq → Lean name map.**  `sep_one_hart` `sepOneHart`, `bag_split_harts` `bagSplitHarts`,
`post_liftings_joint` `postLiftingsJoint`, `tierA_adequacy_ann_core_joint_LM`
`tierAAdequacyAnnCoreJointLM`, `tierA_adequacy_ann_joint_LM` `tierAAdequacyAnnJointLM`,
`tierA_adequacy_ann_joint_L` `tierAAdequacyAnnJointL`, `tierA_adequacy_ann_gate_joint_t`
`tierAAdequacyAnnGateJointT`, `tierA_adequacy_ann_gate_t_of_joint`
`tierAAdequacyAnnGateTOfJoint`.  No name of this file is in `notes/weak-port-dupnames.json`.
Lean-only: `AxSpinJ.bagToMap` (the validated bag over `dom na` in map form, as
`AxTierA2.bagToHart`).

**Dropped:** only the §4 `Check`/`Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpinGate

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open AxDefer2

/-! # 1. Splitting the bag per hart; applying every hart's post_lifting -/

section split
variable {GF : BundledGFunctors}

theorem sepOneHart (R : IProp GF) (x : Agent) (harts : List Agent) :
    harts.Nodup → x ∈ harts →
    R ⊢ [∗list] i ∈ harts, if x = i then R else iprop(True) := by
  induction harts with
  | nil => intro _ Hx; exact absurd Hx List.not_mem_nil
  | cons a l IH =>
    intro Hnd Hx
    obtain ⟨Ha, Hnd⟩ := List.nodup_cons.1 Hnd
    refine Entails.trans ?_ BigSepL.bigSepL_cons.2
    by_cases Hxa : x = a
    · subst Hxa
      rw [if_pos rfl]
      refine sep_emp.2.trans (sep_mono_right (BigSepL.bigSepL_intro fun k y Hy => ?_))
      rw [if_neg (fun (h : x = y) => Ha (h ▸ List.mem_of_getElem? Hy))]
      exact true_intro
    · rw [if_neg Hxa]
      have Hx' : x ∈ l := by
        rcases List.mem_cons.1 Hx with h | h
        · exact absurd h Hxa
        · exact h
      exact (IH Hnd Hx').trans (emp_sep.2.trans (sep_mono_left true_intro))

theorem bagSplitHarts (na : Mea GF) (harts : List Agent) :
    harts.Nodup → (∀ e, e ∈ (FiniteMap.dom_set na : GSet Geid) → e.1 ∈ harts) →
    ([∗map] e ↦ R ∈ na, R) ⊢
      [∗list] i ∈ harts, ([∗map] e ↦ R ∈ na, if e.1 = i then R else iprop(True)) := by
  intro Hnd Hdom
  refine (BigSepM.bigSepM_mono fun {e R} hlk =>
    sepOneHart R e.1 harts Hnd (Hdom e (elemOfDom2 hlk))).trans ?_
  exact (BigSepL.bigSepL_comm_map
    (fun _ i (e : Geid) R => iprop(if e.1 = i then R else iprop(True))) harts na).2

/-- Lean-only: the validated bag over `dom na`, in map form. -/
theorem AxSpinJ.bagToMap (na : Mea GF) :
    ([∗set] e0 ∈ (FiniteMap.dom_set na : GSet Geid),
        AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ⊢
      [∗map] e ↦ R ∈ na, R := by
  refine (BigSepM.bigSepM_dom (S := GSet Geid) (m := na)
    (Φ := fun e0 => AxWp.fromOption (fun P => P) iprop(emp) (get? na e0))).2.trans ?_
  refine BigSepM.bigSepM_mono fun {k v} hlk => ?_
  rw [hlk]
  exact .rfl

end split

section jointLift
variable {GF : BundledGFunctors} [AxirisG GF] [Axpol]

theorem postLiftingsJoint (na : Mea GF) (harts : List Agent)
    (Φ : Agent → Athread → IProp GF) (sN : Agent → Athread) :
    ⊢ AxirisG.annotInterp na -∗ ([∗list] i ∈ harts, postLifting (Φ i) i (sN i)) -∗
      ([∗list] i ∈ harts, [∗map] e ↦ R ∈ na, if e.1 = i then R else iprop(True)) -∗
      |==> (AxirisG.annotInterp na ∗ ▷ |==> [∗list] i ∈ harts, Φ i (sN i)) := by
  induction harts with
  | nil =>
    iintro Hna _ _
    imodintro
    isplitl [Hna]
    · iexact Hna
    · inext
      imodintro
      iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      iempintro
  | cons j l IH =>
    iintro Hna Hpls Hbs
    ihave Hpls := (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hpls
    ihave Hbs := (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hbs
    icases Hpls with ⟨Hpl, Hpls⟩
    icases Hbs with ⟨Hb, Hbs⟩
    iunfold postLifting at Hpl
    imod Hpl $$ %na Hna with ⟨Hna, Hw⟩
    ihave HIH := IH $$ Hna Hpls Hbs
    imod HIH with ⟨Hna, HR⟩
    imodintro
    isplitl [Hna]
    · iexact Hna
    · ihave Hw := Hw $$ Hb
      inext
      imod Hw
      imod HR
      imodintro
      iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      isplitl [Hw]
      · iexact Hw
      · iexact HR

end jointLift

/-! # 2. The joint core and its Prop wrappers -/

section fixed
variable {GF : BundledGFunctors.{0,0,0}}

theorem tierAAdequacyAnnCoreJointLM {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] [Axpol]
    (GD : Gdexec) (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N → Agent → IProp GF) (nm : N) (M : Gdexec → Prop) [GModel M]
    (Hwf : axpolWf) (Hcons : M GD)
    (harts : List Agent) (Hnd : harts.Nodup)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ i, i ∈ harts → nsteps (astepAnyNfGv GD i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
    (Φ : Agent → Athread → IProp GF)
    (Hwp : ⊢ ([∗list] i ∈ harts, init nm i) -∗
      [∗list] i ∈ harts, tierAWpdM GD N obSt0 obStInterp0 nm M (s0 i) .MaybeStuck i (Φ i))
    (P : Prop)
    (Hjoint : ⊢ ([∗list] i ∈ harts, Φ i (sN i)) ==∗ ⌜P⌝)
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo) (Hpol : axpolWfL GD L)
    (Hcov : (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) :
        GSet Geid) = LawfulSet.ofList L)
    (σ0 : obSt0) :
    ⊢ AxAnnot.annotInterp (∅ : Mea GF) -∗ obStInterp0 nm GD σ0 ∅ -∗
      ([∗list] i ∈ harts, init nm i) -∗
      |={⊤}[∅]▷=>^[(harts.map n).sum + (1 + (L.length + 1))] ⌜P⌝ := by
  letI axG : AxirisG GF := axGA5 GD N obSt0 obStInterp0 nm
  have Hgc : ⊢ AxirisG.gconstInterp GD := axGA2Gconst GD N obSt0 obStInterp0 nm
  have Hloc : ∀ j : Agent, ⊢ ∃ ls, AxirisG.localInterp (GF := GF) GD j 0 ls := fun _ => by
    iexists ()
    show ⊢ iprop(True)
    itrivial
  have Hbig0 : ([∗list] j ∈ harts,
        tierAWpdM GD N obSt0 obStInterp0 nm M (s0 j) .MaybeStuck j (Φ j)) ⊢
      [∗list] j ∈ harts, (∃ ls, AxirisG.localInterp (GF := GF) GD j 0 ls) ∗
        wpdM M .MaybeStuck j (s0 j) (Φ j) :=
    BigSepL.bigSepL_mono_of_forall fun {_ j} => AxTierA2.wpdWithLocal GD j _ (Hloc j)
  have Hphase1 := wpdHartsNstepsM (GF := GF) M GD Hwf Hcons .MaybeStuck harts Hnd s0 sN n Hrun
    Hk0 Φ
  have Hndp : L.Nodup := Hperm.nodup_iff.2 (gmGwf GD Hcons).1
  have Hfmap : (harts.map fun j => eidsBefore GD j (sN j).atK) =
      harts.map fun j => eidsBefore GD j (AxOpsem.grow GD j).length :=
    List.map_congr_left fun j Hj => by rw [Hend j Hj]
  -- EVERY hart's post_lifting, at its row end
  have Hpost : ∀ (k : Nat) (j : Agent), harts[k]? = some j →
      ((∃ ls', AxirisG.localInterp (GF := GF) GD j (sN j).atK ls') ∗
        wpdM M .MaybeStuck j (sN j) (Φ j)) ⊢ postLifting (Φ j) j (sN j) := by
    intro k j Hk
    iintro ⟨⟨%ls, Hlocj⟩, HWPj⟩
    ihave #Hg := Hgc
    ihave Hpl := (wpdMPostAtRowEnd (GF := GF) M .MaybeStuck j (sN j) (Φ j) GD ls
      (Hend j (List.mem_of_getElem? Hk)) Hcons) $$ Hg Hlocj HWPj
    iexact Hpl
  iintro Hannot0 Hob0 Hinit
  ihave HWPall := Hwp $$ Hinit
  ihave Hbig := Hbig0 $$ HWPall
  ihave #Hg := Hgc
  ihave Hp1 := Hphase1 $$ Hannot0 Hg Hbig
  ihave Hp1 := wpdStepsNStepFupdN _ _ $$ Hp1
  iapply step_fupdN_add.2
  iapply step_fupdN_wand $$ Hp1
  iintro H
  rw [show 1 + (L.length + 1) = (L.length + 1) + 1 by omega, AxTierA2.stepFupdNSucc]
  imod H with ⟨%na, %ea, %Hdomna, Hannot, Hea, Hbig2⟩
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  ihave Hpls := (BigSepL.bigSepL_mono fun {k j} Hk => Hpost k j Hk) $$ Hbig2
  have Hdomeq : (FiniteMap.dom_set na : GSet Geid) = LawfulSet.ofList L := by
    rw [Hdomna, Hfmap]
    exact Hcov
  have Hkeys : ∀ e, e ∈ (FiniteMap.dom_set na : GSet Geid) → e.1 ∈ harts := by
    intro e He
    rw [Hdomna] at He
    obtain ⟨X, HX, He⟩ := elemOfUnionList.1 He
    obtain ⟨j, Hj, rfl⟩ := List.mem_map.1 HX
    obtain ⟨Heq, _, _⟩ := (elemOfEidsBefore GD j _ e).1 He
    rw [Heq]
    exact Hj
  ihave Hconn := (ordEaTodoLOfEaLocalWf GD ea na L Hndp Hdomeq.symm) $$ Hea
  icases Hconn with ⟨%Hdom_eq2, %Hea_lob2, Htodo⟩
  have Hdom_sub : (LawfulSet.ofList L : GSet Geid) ⊆ FiniteMap.dom_set na := by
    rw [Hdomeq]
  ihave Hphase2 := (adequacyOrdLWf GD (gmGwf GD Hcons) L Hperm Hpol na ea
    Hdom_eq2 Hdom_sub Hea_lob2 σ0) $$ Htodo Hob0
  iapply step_fupdN_add.2
  iapply step_fupdN_wand $$ Hphase2
  iintro ⟨%σ, -, Hrbag⟩
  rw [← Hdomeq] at *
  ihave HRmap := (AxSpinJ.bagToMap na) $$ Hrbag
  -- THE SPLIT, then each hart's post_lifting in turn
  ihave Hbags := (bagSplitHarts na harts Hnd Hkeys) $$ HRmap
  rw [AxTierA2.stepFupdNSucc, AxTierA2.stepFupdNZero]
  ihave Hjl := (postLiftingsJoint na harts Φ sN) $$ Hannot Hpls Hbags
  imod Hjl with ⟨-, HΦ⟩
  iapply step_fupd_fupd.2
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  imod HΦ
  ihave HP := Hjoint $$ HΦ
  imod HP with %Hp
  imodintro
  ipureintro
  exact Hp

end fixed

section wrapper
variable {GF : BundledGFunctors.{0,0,0}}

/-- The Prop-level JOINT wrapper over any order processing handouts first: the names are
allocated inside, `Hwp`/`Hjoint` are discharged at them. -/
theorem tierAAdequacyAnnJointLM [InvGpreS GF] [AxannotG GF] [Axpol]
    (GD : Gdexec) (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N → Agent → IProp GF) (M : Gdexec → Prop) [GModel M]
    (Hwf : axpolWf) (Hcons : M GD)
    (harts : List Agent) (Hnd : harts.Nodup)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ harts)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N) i, i ∈ harts →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
    (Φ : InvGS_gen .hasNoLC GF → AxannotGS GF → N → Agent → Athread → IProp GF)
    (Hwp : ∀ [Hinv : InvGS_gen .hasNoLC GF] [Hann : AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpdM GD N obSt0 obStInterp0 nm M (s0 i) .MaybeStuck i (Φ Hinv Hann nm i))
    (P : Prop)
    (Hjoint : ∀ [Hinv : InvGS_gen .hasNoLC GF] [Hann : AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, Φ Hinv Hann nm i (sN i)) ==∗ ⌜P⌝)
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo) (Hpol : axpolWfL GD L) :
    P := by
  have Hcov : (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) :
      GSet Geid) = LawfulSet.ofList L := by
    rw [eidsBeforeCov GD harts (gmGwf GD Hcons) Hharts, setEq]
    intro x
    rw [elemOfListToSet, elemOfListToSet]
    exact Hperm.mem_iff.symm
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := .hasNoLC)
    (1 + ((harts.map n).sum + (1 + (L.length + 1)))) 0 (fun Hinv => ?_)
  rw [show 1 + ((harts.map n).sum + (1 + (L.length + 1))) =
      ((harts.map n).sum + (1 + (L.length + 1))) + 1 by omega,
    AxTierA2.stepFupdNSucc]
  iintro _
  imod (annotInterpAlloc (GF := GF)) with ⟨%γ, Hannot0⟩
  imod HobAlloc with ⟨%nm, %σ0, Hob0, Hinit⟩
  ihave Hcore := (@tierAAdequacyAnnCoreJointLM GF .hasNoLC Hinv { axannotName := γ } _ GD N
    obSt0 obStInterp0 init nm M _ Hwf Hcons harts Hnd s0 sN n
    (fun j Hj => Hrun { axannotName := γ } nm j Hj) Hk0 Hend (Φ Hinv { axannotName := γ } nm)
    (@Hwp Hinv { axannotName := γ } nm) P (@Hjoint Hinv { axannotName := γ } nm)
    L Hperm Hpol Hcov σ0) $$ Hannot0 Hob0 Hinit
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  iexact Hcore

/-- riscv.cat instance (`tierAWpd` posts). -/
theorem tierAAdequacyAnnJointL [InvGpreS GF] [AxannotG GF] [Axpol]
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
    (Φ : InvGS_gen .hasNoLC GF → AxannotGS GF → N → Agent → Athread → IProp GF)
    (Hwp : ∀ [Hinv : InvGS_gen .hasNoLC GF] [Hann : AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpd GD N obSt0 obStInterp0 nm (s0 i) .MaybeStuck i (Φ Hinv Hann nm i))
    (P : Prop)
    (Hjoint : ∀ [Hinv : InvGS_gen .hasNoLC GF] [Hann : AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, Φ Hinv Hann nm i (sN i)) ==∗ ⌜P⌝)
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo) (Hpol : axpolWfL GD L) :
    P :=
  tierAAdequacyAnnJointLM GD N obSt0 obStInterp0 init rvwmoCatConsistent Hwf Hcons harts Hnd
    Hharts s0 sN n Hrun Hk0 Hend Φ Hwp P Hjoint HobAlloc L Hperm Hpol

end wrapper

/-! # 3. THE TAGGED GATED JOINT ADEQUACY -/

section gateJoint
variable {GF : BundledGFunctors.{0,0,0}}

/-- `AxSpinGate.tierAAdequacyAnnGateT`'s premises, iProp posts, a JOINT final step. -/
theorem tierAAdequacyAnnGateJointT [InvGpreS GF] [AxannotG GF] [Axpol]
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
    (Φ : InvGS_gen .hasNoLC GF → AxannotGS GF → N → Agent → Athread → IProp GF)
    (Hwp : ∀ [Hinv : InvGS_gen .hasNoLC GF] [Hann : AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpd (gtAdGd GT) N obSt0 obStInterp0 nm (s0 i) .MaybeStuck i (Φ Hinv Hann nm i))
    (P : Prop)
    (Hjoint : ∀ [Hinv : InvGS_gen .hasNoLC GF] [Hann : AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, Φ Hinv Hann nm i (sN i)) ==∗ ⌜P⌝)
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm (gtAdGd GT) σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (Hok : ∀ e e', e' ∈ Axpol.sPol (gtAdGd GT) e ∪ Axpol.lobp (gtAdGd GT) e →
      polDS GT.gtG (gsrcT GT) e' e ∨ e' ∈ gsrcT GT e) :
    P := by
  have Hcons := catTAd GT HconsT
  obtain ⟨Hwfg, _, _, _, Hdw, _⟩ := HconsT
  have H := LcanonOkGate' (gtAdGd GT) Hwfg (gsrcT GT) (gsrcTSrcPo GT Hdw) (gsrcTMono GT) Hok
  exact tierAAdequacyAnnJointL (gtAdGd GT) N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts
    s0 sN n Hrun Hk0 Hend Φ Hwp P Hjoint HobAlloc (Lcanon (gtAdGd GT) (gsrcT GT)) H.1 H.2.2

/-- REGRESSION CHECK: `AxSpinGate.tierAAdequacyAnnGateT`'s exact statement, as a corollary of
the joint theorem. -/
theorem tierAAdequacyAnnGateTOfJoint [InvGpreS GF] [AxannotG GF] [Axpol]
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
  refine tierAAdequacyAnnGateJointT GT N obSt0 obStInterp0 init Hwf HconsT harts Hnd Hharts
    s0 sN n Hrun Hk0 Hend (fun _ _ _ i s => iprop(⌜post i s⌝)) (fun nm => Hwp nm)
    (∀ i, i ∈ harts → post i (sN i)) (fun nm => ?_) HobAlloc Hok
  iintro H
  imodintro
  ihave %Hall := (BigSepL.bigSepL_pure (PROP := IProp GF)
    (φ := fun _ i => post i (sN i)) (l := harts)).1 $$ H
  ipureintro
  intro i Hi
  obtain ⟨k, Hk⟩ := List.mem_iff_getElem?.1 Hi
  exact Hall k i Hk

end gateJoint

end Weak
