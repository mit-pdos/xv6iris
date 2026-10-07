/-
Weak: **`tierAAdequacyAnn`, the non-trivial Tier A adequacy theorem** — `Φ` receives each hart's
REAL validated annotations (AxSL tier).

Rocq: `iris/AxTierA2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§0 derives two scheduler premises outright: `schedGatefreeRun` is an explicit all-`stepCommit`
walk of the whole scheduler over `gxGmo` (no event is ever deferred, so `sD` stays `∅` and
`stepCommit`'s `Hclear` is vacuous), and `eidsBeforeCov` shows that the union of every hart's full
row of memory events is the whole of `gxGmo`, given `gwf` and that every memory event's hart is
run.  §1 `axGA2` is the `AxirisG` record at the REAL annotation ghost map (`AxAnnot.annotInterp`),
`gconstInterp GD0 := ⌜GD0 = GD⌝`, and a caller-supplied protocol state `obSt0` /
`obStInterp0 nm` at a caller-chosen protocol ghost NAME `nm : N` (allocated inside the same bupd
as the initial protocol state and the per-hart `init nm i` resources).  `tierAWpd`/`tierAWpdM`/
`tierAAstep` re-export `wpd`/`wpdM`/`astepAnyNfGv` at a given `nm`.  §2 `tierAAdequacyAnnCore`:
phase 1 (`wpdHartsNsteps`, all harts through one shared `na`), the per-hart `postLifting` at row
end (`wpdPostAtRowEnd`), phase 2 (`ordEaTodoLOfEaLocalWf` then `schedProcAdequate`, whose
validated bag is converted to map form and fed into `postLifting` at the run's REAL `na`).  §3
`tierAAdequacyAnn` is the Prop-level wrapper: per hart, it allocates a fresh annotation name and a
fresh `nm`/`σ0`/init bundle inside the soundness continuation.

CERTIFICATE NOTE (as Rocq): `gconstInterp` pins `GD`, so instantiating these theorems at a
concrete graph literal proves nothing about the model; a real client states them for an abstract
`GD`.

## Deviations from Rocq

1. NAMES: camelCase (map below); no name of this file is in `notes/weak-port-dupnames.json`.
   `sum_list (n <$> harts)` ↦ `(harts.map n).sum`, `⋃ (f <$> l)` ↦ `unionList (l.map f)`,
   `list_to_set` ↦ `LawfulSet.ofList`, `dom` ↦ `FiniteMap.dom_set … : GSet Geid`, `NoDup` ↦
   `List.Nodup`, `grow GD i` ↦ `AxOpsem.grow GD i`, `MaybeStuck` ↦ `.MaybeStuck`,
   `|={⊤}[∅]▷=>^n` ↦ `|={⊤}[∅]▷=>^[n]`.
2. O2 STAGE C: `AxirisG` has no `ax_text` field, so the section parameter `T` (and `axGA2`'s
   `ax_text := T`) is gone; `astepAnyNfGv` carries the boot-image pin itself (Q8).  Consequently
   `tierAAstep GD nm i` no longer depends on the annotation instance; `Hrun` still quantifies an
   `AxannotGS GF` (as Rocq) and `nm`.
3. `AxGA2` is a Rocq `Global Instance` over a section-bound `nm`; Lean has no lexical instance
   over a non-class argument, so `axGA2 GD N obSt0 obStInterp0 nm` is a `@[reducible] def` (as
   AxWp2's `skelAxirisG`), named explicitly where used (`tierAWpd`, the core's `letI`).  Its
   `[AxannotGS GF]` is an instance argument; `GF : BundledGFunctors.{0,0,0}` (AxWp deviation 3).
4. `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` in §1/§2 (as AxWpDSteps); §3's
   soundness runs at `.hasNoLC` (`step_fupdN_soundness_close (hlc := .hasNoLC)`), and its `Hwp`
   quantifies `[InvGS_gen .hasNoLC GF]`.
5. `tierAAdequacyAnnCore`'s `Hwp` is stated with `tierAWpd` (convertible to Rocq's `WPd` under
   `AxGA2 nm`, by definition); the wand chain is `⊢ A -∗ B -∗ C -∗ …` (AxWp deviation 7).
6. PROOF ROUTE (not statements): the `(∃ ls, localInterp …) ∗ WPd` big list is built pointwise
   (`bigSepL_mono`), and the bag-to-hart-map conversion is the Lean-only helper
   `AxTierA2.bagToHart`.

**Rocq → Lean name map.**  `sched_gatefree_run` `schedGatefreeRun`, `eids_before_cov`
`eidsBeforeCov`, `AxGA2` `axGA2`, `AxGA2_gconst` `axGA2Gconst`, `tierA_wpd` `tierAWpd`,
`tierA_wpdM` `tierAWpdM`, `tierA_astep` `tierAAstep`, `tierA_adequacy_ann_core`
`tierAAdequacyAnnCore`, `tierA_adequacy_ann` `tierAAdequacyAnn`.  Lean-only:
`AxTierA2.bagToHart`, `AxTierA2.wpdWithLocal`, `AxTierA2.stepFupdNSucc`/`stepFupdNZero`.

**Dropped:** only the two `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxWpDHarts
import Weak.AxSchedGD

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 0. Scheduler-premise derivations -/

/-- An explicit all-`stepCommit` run of the whole scheduler over `gxGmo`, never deferring. -/
theorem schedGatefreeRun (GD : Gdexec) :
    ∃ sst : Sstate,
      rtc (schedStep GD.gdG) sst0 sst ∧
      sst.sProc = GD.gdG.gxGmo ∧
      sst.sN = GD.gdG.gxGmo.length ∧
      sst.sD = ∅ ∧ sst.sEverD = ∅ := by
  have Hgen : ∀ j, j ≤ GD.gdG.gxGmo.length →
      rtc (schedStep GD.gdG) sst0 ⟨j, ∅, ∅, GD.gdG.gxGmo.take j⟩ := by
    intro j
    induction j with
    | zero => intro _; exact rtc_refl _
    | succ j IH =>
      intro Hle
      have Hjlt : j < GD.gdG.gxGmo.length := by omega
      have He : GD.gdG.gxGmo[j]? = some (GD.gdG.gxGmo[j]'Hjlt) := List.getElem?_eq_getElem Hjlt
      have Hstep := schedStep.stepCommit (G := GD.gdG) j ∅ ∅ (GD.gdG.gxGmo.take j) _ He
        (fun r Hr => by
          exfalso
          have Hr' : r ∈ (FiniteMap.dom_set (∅ : GMapF Geid Nat) : GSet Geid) := Hr
          rw [domEmpty] at Hr'
          exact notElemOfEmpty Hr')
      have Htake : GD.gdG.gxGmo.take (j + 1) = GD.gdG.gxGmo.take j ++ [GD.gdG.gxGmo[j]'Hjlt] := by
        rw [List.take_add_one, He]
        rfl
      rw [Htake]
      exact rtc_r (IH (by omega)) Hstep
  refine ⟨⟨GD.gdG.gxGmo.length, ∅, ∅, GD.gdG.gxGmo⟩, ?_, rfl, rfl, rfl, rfl⟩
  have Hrun := Hgen GD.gdG.gxGmo.length (Nat.le_refl _)
  rw [List.take_length] at Hrun
  exact Hrun

/-- `Hcov`'s content: the union of every hart's own full-row memory events is the whole of
`gxGmo`, given `gwf` and that every memory event's hart is among `harts`. -/
theorem eidsBeforeCov (GD : Gdexec) (harts : List Agent) (Hwf : gwf GD.gdG)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ harts) :
    (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) : GSet Geid) =
      LawfulSet.ofList GD.gdG.gxGmo := by
  rw [setEq]
  intro e
  rw [elemOfUnionList, elemOfListToSet]
  constructor
  · rintro ⟨X, HX, He⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 HX
    obtain ⟨_, _, Hmem⟩ := (elemOfEidsBefore GD i _ e).1 He
    apply gwfMemGmo GD.gdG e Hwf
    unfold gmemB at Hmem
    cases Hl : gxLbl GD.gdG e with
    | none => rw [Hl] at Hmem; exact absurd Hmem Bool.false_ne_true
    | some l => rw [Hl] at Hmem; exact ⟨l, Hl, Hmem⟩
  · intro Hin
    obtain ⟨l, Hl, Hm⟩ := gwfGmoMem GD.gdG e Hwf Hin
    obtain ⟨ei, ek⟩ := e
    have Hsome : progressIsValidG GD.gdG ei ek := by
      unfold progressIsValidG
      rw [Hl]
      rfl
    have Hlt := (progressIsValidGrowG GD.gdG ei ek).1 Hsome
    refine ⟨eidsBefore GD ei (AxOpsem.grow GD ei).length,
      List.mem_map.2 ⟨ei, Hharts _ Hin, rfl⟩, (elemOfEidsBefore GD ei _ _).2 ⟨rfl, Hlt, ?_⟩⟩
    unfold gmemB
    rw [Hl]
    exact Hm

/-! # 1. `axGA2`: the `AxirisG` record at the real annotation map and a protocol name -/

section fixed
variable {GF : BundledGFunctors.{0,0,0}}

/-- Rocq `AxGA2`: the real ghost-map annotation law, the cheap graph pin, the caller's protocol
state at name `nm`, trivial local state. -/
@[reducible] def axGA2 [AxannotGS GF] (GD : Gdexec) (N obSt0 : Type)
    (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) : AxirisG GF where
  annotInterp := AxAnnot.annotInterp
  gconstInterp := fun GD0 => iprop(⌜GD0 = GD⌝)
  obSt := obSt0
  obStInterp := obStInterp0 nm
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

theorem axGA2Gconst [AxannotGS GF] (GD : Gdexec) (N obSt0 : Type)
    (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) :
    ⊢ AxirisG.gconstInterp (self := axGA2 GD N obSt0 obStInterp0 nm) GD := by
  show ⊢ iprop(⌜GD = GD⌝)
  ipureintro
  rfl

/-- Rocq `tierA_wpd`: `WPd` at `axGA2 … nm`. -/
def tierAWpd {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] [Axpol] (GD : Gdexec)
    (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N)
    (s : Athread) (st : Stuckness) (i : Agent) (Φ : Athread → IProp GF) : IProp GF :=
  @wpd hlc GF _ (axGA2 GD N obSt0 obStInterp0 nm) _ st i s Φ

/-- Rocq `tierA_wpdM`: the same over a graph model `M`. -/
def tierAWpdM {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] [Axpol] (GD : Gdexec)
    (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N)
    (M : Gdexec → Prop) (s : Athread) (st : Stuckness) (i : Agent)
    (Φ : Athread → IProp GF) : IProp GF :=
  @wpdM hlc GF _ (axGA2 GD N obSt0 obStInterp0 nm) _ M st i s Φ

/-- Rocq `tierA_astep` (Stage C: independent of the annotation instance and of `nm`). -/
def tierAAstep (GD : Gdexec) {N : Type} (_nm : N) (i : Agent) : Athread → Athread → Prop :=
  astepAnyNfGv GD i

/-! # 2. `tierAAdequacyAnnCore`: the iProp-level composition -/

/-- Lean-only: `AxAdequacy.stepFupdNSucc` without its section's `AxirisG` instance. -/
theorem AxTierA2.stepFupdNSucc {hlc : HasLC} [InvGS_gen hlc GF] (n : Nat) (P : IProp GF) :
    iprop(|={⊤}[∅]▷=>^[n + 1] P) = iprop(|={⊤}[∅]▷=> |={⊤}[∅]▷=>^[n] P) := rfl

/-- Lean-only: `AxAdequacy.stepFupdNZero` without its section's `AxirisG` instance. -/
theorem AxTierA2.stepFupdNZero {hlc : HasLC} [InvGS_gen hlc GF] (P : IProp GF) :
    iprop(|={⊤}[∅]▷=>^[0] P) = P := rfl

/-- Lean-only: the validated bag over `dom na`, restricted to hart `i`, in `postLifting`'s map
form. -/
theorem AxTierA2.bagToHart (na : Mea GF) (i : Agent) :
    ([∗set] e0 ∈ (FiniteMap.dom_set na : GSet Geid),
        AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ⊢
      [∗map] e ↦ R ∈ na, if e.1 = i then R else iprop(True) := by
  refine (BigSepM.bigSepM_dom (S := GSet Geid) (m := na)
    (Φ := fun e0 => AxWp.fromOption (fun P => P) iprop(emp) (get? na e0))).2.trans ?_
  refine BigSepM.bigSepM_mono fun {k v} hlk => ?_
  rw [hlk]
  simp only [AxWp.fromOption]
  split
  · exact .rfl
  · exact true_intro

/-- Lean-only: a `WPd` with the (trivial) local interpretation alongside. -/
theorem AxTierA2.wpdWithLocal [AxirisG GF] (GD : Gdexec) (j : Agent) (W : IProp GF)
    (Hloc : ⊢ ∃ ls, AxirisG.localInterp (GF := GF) GD j 0 ls) :
    W ⊢ iprop((∃ ls, AxirisG.localInterp (GF := GF) GD j 0 ls) ∗ W) := by
  iintro H
  isplitr
  · iapply Hloc
  · iexact H

theorem tierAAdequacyAnnCore {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] [Axpol]
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
    (HsPolSub : ∀ e e', e' ∈ Axpol.sPol GD e → gobCatFlow GD e' e)
    (HlobpSub : ∀ e e', e' ∈ Axpol.lobp GD e → gobCatFlow GD e' e)
    (Hcov : (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) :
        GSet Geid) = LawfulSet.ofList sst.sProc)
    (σ0 : obSt0) (i : Agent) (Hi : i ∈ harts) :
    ⊢ AxAnnot.annotInterp (∅ : Mea GF) -∗ obStInterp0 nm GD σ0 ∅ -∗
      ([∗list] i ∈ harts, init nm i) -∗
      |={⊤}[∅]▷=>^[(harts.map n).sum + (1 + (sst.sProc.length + 1))] ⌜post i (sN i)⌝ := by
  letI axG : AxirisG GF := axGA2 GD N obSt0 obStInterp0 nm
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
  have Hdefer : ∀ r, deferredSnapAvail GD sst.sEverD r := by
    intro r Hr
    rw [Hgatefree] at Hr
    exact absurd Hr notElemOfEmpty
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
  ihave Hphase2 := (schedProcAdequate GD Hcons sst HrunSched Hfull Hdone HsPolSub HlobpSub na ea
    Hdom_eq2 Hdom_sub Hea_lob2 Hdefer σ0) $$ Htodo Hob0
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

/-! # 3. `tierAAdequacyAnn`: the Prop-level wrapper -/

section wrapper
variable {GF : BundledGFunctors.{0,0,0}}

theorem tierAAdequacyAnn [InvGpreS GF] [AxannotG GF] [Axpol]
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
  ihave Hcore := (@tierAAdequacyAnnCore GF .hasNoLC Hinv { axannotName := γ } _ GD N obSt0
    obStInterp0 init nm Hwf Hcons harts Hnd s0 sN n
    (fun j Hj => Hrun { axannotName := γ } nm j Hj) Hk0 Hend post
    (@Hwp Hinv { axannotName := γ } nm)
    sst HrunSched Hfull Hdone Hgatefree HsPolSub HlobpSub Hcov σ0 i Hi) $$ Hannot0 Hob0 Hinit
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  iexact Hcore

end wrapper

end Weak
