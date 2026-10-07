/-
Weak: **constraint F at TIER A** — Prop-level adequacy (all harts' WPds, real annotations,
readback) over an ARBITRARY processing order (`tierAAdequacyAnnL`), and its instance at the
canonical deferring order `AxDefer3.Lcanon`: `tierAAdequacyAnnGate` — handouts may be
deferral-safe (`polDS`, ⊇ every `flowDev2` edge) OR a GATE SOURCE of the recipient, even one
gmo-LATER than it (a deferred read handed its gate's source).  No scheduler run, no
`Hgatefree` (AxSL tier).

Rocq: `iris/AxDefer5.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE GATE AS A HANDOUT.  `wpd` has no `LCtrl` arm, and needs none: a flow equation of a gated
event `e` may assume its gate sources `r ∈ gsrc e` are VALIDATED by putting them in
`sPol GD e`; an instance whose `obStInterp` records the pure facts of validated sources then
hands those facts to `e`'s flow equation — exactly the guarded form of `AxDefer.ordEaTodoG`.
Such handouts are gmo-BACKWARD at a deferred read, so the gmo-bounded routes
(AxTierA3/AxTierA4) cannot take them; ranks can (`AxDefer3.canonGate`).  The row-end post reads
the source annotation directly (`postLifting`).  `tierAAdequacyAnnCoreL` is
`AxTierA4.tierAAdequacyAnnCoreRun`'s proof with the scheduler run replaced by `L` (phase 2 =
`adequacyOrdLWf` directly).  §2: the deferral-safe PREFIX policy `polSafeS` is deferral-safe
for every graph (`polSafeDS`); `PGate` (safe prefix + gate sources) is admissible on
`AxDefer2.gdefer` (`PGateOk`) and hands the deferred read its gmo-later gate source
(`PGateBackward`); the refuted ledger policy `PRef` is not admissible (`PRefNotOk`).

## Deviations from Rocq

1. Vocabulary as AxTierA2/AxTierA3/AxDefer3 (`≡ₚ` ↦ `List.Perm`, `list_to_set` ↦
   `LawfulSet.ofList`, `|={⊤}[∅]▷=>^n` ↦ `|={⊤}[∅]▷=>^[n]`, wand chains `⊢ A -∗ B -∗ C`).
2. O2 STAGE C (as AxTierA2 deviation 2): the section parameter `T` is gone; `tierAAstep GD nm i`
   and `tierAWpd`/`tierAWpdM GD N obSt0 obStInterp0 nm …` are AxTierA2's.
3. `AxGA5` (a Rocq `Local Instance` := `AxGA2 … nm`) is `axGA5`, a `@[reducible] def` equal to
   `axGA2`; the core installs it with `letI` (as AxTierA3's `axGA3`).
4. The cores are stated for `[InvGS_gen hlc GF]`, any `hlc` (Rocq: `HasNoLc`); the wrappers'
   soundness runs at `.hasNoLC` and their `Hwp` quantifies `[InvGS_gen .hasNoLC GF]` (as
   AxTierA3/A4).  The Rocq big_sepM steps are `AxTierA2.bagToHart`.
5. Section `Context`s are explicit arguments (order: `GD N obSt0 obStInterp0 init`, then `nm`,
   then `M [GModel M]`); `[Axpol]` is an instance argument.  Rocq's `Definition
   tierA_adequacy_ann_core_L := …` is a theorem with the instantiated statement.
6. `P_gate` is `@[reducible] def PGate : Axpol` (not an instance); its lemmas name it
   explicitly (`@Axpol.sPol PGate …`), as AxDefer2's `PRef`.

**Rocq → Lean name map.**  `Lcanon_ok_gate` `LcanonOkGate`, `AxGA5` `axGA5`,
`tierA_adequacy_ann_core_LM` `tierAAdequacyAnnCoreLM`, `tierA_adequacy_ann_core_L`
`tierAAdequacyAnnCoreL`, `tierA_adequacy_ann_LM` `tierAAdequacyAnnLM`,
`tierA_adequacy_ann_gmoM` `tierAAdequacyAnnGmoM`, `tierA_adequacy_ann_L` `tierAAdequacyAnnL`,
`tierA_adequacy_ann_gate` `tierAAdequacyAnnGate`, `tierA_adequacy_ann_dev2_gate`
`tierAAdequacyAnnDev2Gate`, `pol_safe_DS` `polSafeDS`, `P_gate` `PGate`, `P_gate_ok`
`PGateOk`, `P_gate_backward` `PGateBackward`, `P_ref_not_ok` `PRefNotOk`.  No name of this file
is in `notes/weak-port-dupnames.json`; no Lean-only helpers.

**Dropped:** only the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxDefer3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open AxDefer2

/-- Ranks also order gate-source handouts. -/
theorem LcanonOkGate [Axpol] (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (gsrc : Geid → GSet Geid) (Hreal : gateReal GD gsrc) (Hmono : gateMono GD gsrc)
    (Hok : ∀ e e', e' ∈ Axpol.sPol GD e ∪ Axpol.lobp GD e →
      polDS GD.gdG gsrc e' e ∨ e' ∈ gsrc e) :
    (Lcanon GD gsrc).Perm GD.gdG.gxGmo ∧ gsrcBefore (Lcanon GD gsrc) gsrc ∧
    axpolWfL GD (Lcanon GD gsrc) := by
  have Hnd := Hcons.1.1
  have Hsg := gateRealSrcGmo GD gsrc Hcons Hreal
  have Hpo : ∀ e r, r ∈ gsrc e → WeakRvwmoGraph.gpo GD.gdG r e := fun e r Hr => (Hreal e r Hr).1
  apply orderOfRank GD Hnd
  · intro e r He Hr
    exact ⟨Hsg e r Hr, canonGate GD.gdG gsrc Hnd Hpo Hmono Hsg e r He Hr⟩
  · intro e e' He Hin
    rcases Hok e e' Hin with Hds | Hg
    · exact ⟨Hds.1.1, canonPol GD.gdG gsrc Hnd Hpo Hsg e e' Hds⟩
    · exact ⟨Hsg e e' Hg, canonGate GD.gdG gsrc Hnd Hpo Hmono Hsg e e' He Hg⟩

/-! # 1. Tier A adequacy over an arbitrary processing order -/

section fixed
variable {GF : BundledGFunctors.{0,0,0}}

/-- Rocq `AxGA5` (a local instance): `axGA2` at `nm`. -/
@[reducible] def axGA5 [AxannotGS GF] (GD : Gdexec) (N obSt0 : Type)
    (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) : AxirisG GF :=
  axGA2 GD N obSt0 obStInterp0 nm

/-- MODEL-GENERIC (`GModel`): phase 1 runs `wpdM M`; phase 2 (`adequacyOrdLWf`) needs only
`gmWf`. -/
theorem tierAAdequacyAnnCoreLM {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] [Axpol]
    (GD : Gdexec) (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N → Agent → IProp GF) (nm : N) (M : Gdexec → Prop) [GModel M]
    (Hwf : axpolWf) (Hcons : M GD)
    (harts : List Agent) (Hnd : harts.Nodup)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ i, i ∈ harts → nsteps (astepAnyNfGv GD i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp : ⊢ ([∗list] i ∈ harts, init nm i) -∗
      [∗list] i ∈ harts,
        tierAWpdM GD N obSt0 obStInterp0 nm M (s0 i) .MaybeStuck i (fun s => iprop(⌜post i s⌝)))
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo) (Hpol : axpolWfL GD L)
    (Hcov : (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) :
        GSet Geid) = LawfulSet.ofList L)
    (σ0 : obSt0) (i : Agent) (Hi : i ∈ harts) :
    ⊢ AxAnnot.annotInterp (∅ : Mea GF) -∗ obStInterp0 nm GD σ0 ∅ -∗
      ([∗list] i ∈ harts, init nm i) -∗
      |={⊤}[∅]▷=>^[(harts.map n).sum + (1 + (L.length + 1))] ⌜post i (sN i)⌝ := by
  letI axG : AxirisG GF := axGA5 GD N obSt0 obStInterp0 nm
  have Hgc : ⊢ AxirisG.gconstInterp GD := axGA2Gconst GD N obSt0 obStInterp0 nm
  have Hloc : ∀ j : Agent, ⊢ ∃ ls, AxirisG.localInterp (GF := GF) GD j 0 ls := fun _ => by
    iexists ()
    show ⊢ iprop(True)
    itrivial
  have Hbig0 : ([∗list] j ∈ harts,
        tierAWpdM GD N obSt0 obStInterp0 nm M (s0 j) .MaybeStuck j
          (fun s => iprop(⌜post j s⌝))) ⊢
      [∗list] j ∈ harts, (∃ ls, AxirisG.localInterp (GF := GF) GD j 0 ls) ∗
        wpdM M .MaybeStuck j (s0 j) (fun s => iprop(⌜post j s⌝)) :=
    BigSepL.bigSepL_mono_of_forall fun {_ j} => AxTierA2.wpdWithLocal GD j _ (Hloc j)
  have Hphase1 := wpdHartsNstepsM (GF := GF) M GD Hwf Hcons .MaybeStuck harts Hnd s0 sN n Hrun
    Hk0 (fun j s => (iprop(⌜post j s⌝) : IProp GF))
  have Hndp : L.Nodup := Hperm.nodup_iff.2 (gmGwf GD Hcons).1
  have Hfmap : (harts.map fun j => eidsBefore GD j (sN j).atK) =
      harts.map fun j => eidsBefore GD j (AxOpsem.grow GD j).length :=
    List.map_congr_left fun j Hj => by rw [Hend j Hj]
  have Hpost := fun ls : AxirisG.logTsT GF => wpdMPostAtRowEnd (GF := GF) M .MaybeStuck i (sN i)
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
  rw [show 1 + (L.length + 1) = (L.length + 1) + 1 by omega, AxTierA2.stepFupdNSucc]
  imod H with ⟨%na, %ea, %Hdomna, Hannot, Hea, Hbig2⟩
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  ihave Hhart := (BigSepL.bigSepL_mem Hi) $$ Hbig2
  icases Hhart with ⟨⟨%lsi, Hloci⟩, HWPi⟩
  ihave Hpl := Hpost lsi $$ Hg Hloci HWPi
  have Hdomeq : (FiniteMap.dom_set na : GSet Geid) = LawfulSet.ofList L := by
    rw [Hdomna, Hfmap]
    exact Hcov
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

/-- The riscv.cat instance under the old name. -/
theorem tierAAdequacyAnnCoreL {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] [Axpol]
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
        tierAWpdM GD N obSt0 obStInterp0 nm rvwmoCatConsistent (s0 i) .MaybeStuck i
          (fun s => iprop(⌜post i s⌝)))
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo) (Hpol : axpolWfL GD L)
    (Hcov : (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) :
        GSet Geid) = LawfulSet.ofList L)
    (σ0 : obSt0) (i : Agent) (Hi : i ∈ harts) :
    ⊢ AxAnnot.annotInterp (∅ : Mea GF) -∗ obStInterp0 nm GD σ0 ∅ -∗
      ([∗list] i ∈ harts, init nm i) -∗
      |={⊤}[∅]▷=>^[(harts.map n).sum + (1 + (L.length + 1))] ⌜post i (sN i)⌝ :=
  tierAAdequacyAnnCoreLM GD N obSt0 obStInterp0 init nm rvwmoCatConsistent Hwf Hcons harts Hnd
    s0 sN n Hrun Hk0 Hend post Hwp L Hperm Hpol Hcov σ0 i Hi

end fixed

section wrapper
variable {GF : BundledGFunctors.{0,0,0}}

/-- The Prop-level wrapper over ANY order processing handouts first — MODEL-GENERIC (only
`gmWf` of `M` is used). -/
theorem tierAAdequacyAnnLM [InvGpreS GF] [AxannotG GF] [Axpol]
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
    (post : Agent → Athread → Prop)
    (Hwp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpdM GD N obSt0 obStInterp0 nm M (s0 i) .MaybeStuck i
            (fun s => iprop(⌜post i s⌝)))
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo) (Hpol : axpolWfL GD L) :
    ∀ i, i ∈ harts → post i (sN i) := by
  have Hcov : (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) :
      GSet Geid) = LawfulSet.ofList L := by
    rw [eidsBeforeCov GD harts (gmGwf GD Hcons) Hharts, setEq]
    intro x
    rw [elemOfListToSet, elemOfListToSet]
    exact Hperm.mem_iff.symm
  intro i Hi
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := .hasNoLC)
    (1 + ((harts.map n).sum + (1 + (L.length + 1)))) 0 (fun Hinv => ?_)
  rw [show 1 + ((harts.map n).sum + (1 + (L.length + 1))) =
      ((harts.map n).sum + (1 + (L.length + 1))) + 1 by omega,
    AxTierA2.stepFupdNSucc]
  iintro _
  imod (annotInterpAlloc (GF := GF)) with ⟨%γ, Hannot0⟩
  imod HobAlloc with ⟨%nm, %σ0, Hob0, Hinit⟩
  ihave Hcore := (@tierAAdequacyAnnCoreLM GF .hasNoLC Hinv { axannotName := γ } _ GD N obSt0
    obStInterp0 init nm M _ Hwf Hcons harts Hnd s0 sN n
    (fun j Hj => Hrun { axannotName := γ } nm j Hj) Hk0 Hend post
    (@Hwp Hinv { axannotName := γ } nm)
    L Hperm Hpol Hcov σ0 i Hi) $$ Hannot0 Hob0 Hinit
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  iexact Hcore

/-- The gmo-bounded route (the `AxTierA3.tierAAdequacyAnnGmo` premise shape), MODEL-GENERIC:
`L := gxGmo`; no scheduler run. -/
theorem tierAAdequacyAnnGmoM [InvGpreS GF] [AxannotG GF] [Axpol]
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
    (post : Agent → Athread → Prop)
    (Hwp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpdM GD N obSt0 obStInterp0 nm M (s0 i) .MaybeStuck i
            (fun s => iprop(⌜post i s⌝)))
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (HsPolGmo : ∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e)
    (HlobpGmo : ∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e) :
    ∀ i, i ∈ harts → post i (sN i) := by
  have Hndg := (gmGwf GD Hcons).1
  refine tierAAdequacyAnnLM GD N obSt0 obStInterp0 init M Hwf Hcons harts Hnd Hharts s0 sN n
    Hrun Hk0 Hend post Hwp HobAlloc GD.gdG.gxGmo (List.Perm.refl _) ?_
  intro k e Hk
  exact ⟨fun e' He' => gmoLtTake GD k e e' Hndg Hk (HsPolGmo e e' He'),
    fun e' He' => gmoLtTake GD k e e' Hndg Hk (HlobpGmo e e' He')⟩

/-- The Prop-level wrapper over ANY order processing handouts first. -/
theorem tierAAdequacyAnnL [InvGpreS GF] [AxannotG GF] [Axpol]
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
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo) (Hpol : axpolWfL GD L) :
    ∀ i, i ∈ harts → post i (sN i) :=
  tierAAdequacyAnnLM GD N obSt0 obStInterp0 init rvwmoCatConsistent Hwf Hcons harts Hnd Hharts
    s0 sN n Hrun Hk0 Hend post Hwp HobAlloc L Hperm Hpol

/-- CONSTRAINT F, TIER A: deferral-safe (⊇ dev-2) handouts plus GATE-SOURCE handouts
(gmo-backward at deferred reads), over `Lcanon`. -/
theorem tierAAdequacyAnnGate [InvGpreS GF] [AxannotG GF] [Axpol]
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
    (gsrc : Geid → GSet Geid) (Hreal : gateReal GD gsrc) (Hmono : gateMono GD gsrc)
    (Hok : ∀ e e', e' ∈ Axpol.sPol GD e ∪ Axpol.lobp GD e →
      polDS GD.gdG gsrc e' e ∨ e' ∈ gsrc e) :
    ∀ i, i ∈ harts → post i (sN i) :=
  have H := LcanonOkGate GD Hcons gsrc Hreal Hmono Hok
  tierAAdequacyAnnL GD N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts s0 sN n Hrun Hk0
    Hend post Hwp HobAlloc (Lcanon GD gsrc) H.1 H.2.2

/-- Same, with the dev-2 handouts named directly. -/
theorem tierAAdequacyAnnDev2Gate [InvGpreS GF] [AxannotG GF] [Axpol]
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
    (gsrc : Geid → GSet Geid) (Hreal : gateReal GD gsrc) (Hmono : gateMono GD gsrc)
    (HsPol : ∀ e e', e' ∈ Axpol.sPol GD e → flowDev2 GD e' e ∨ e' ∈ gsrc e)
    (Hlobp : ∀ e e', e' ∈ Axpol.lobp GD e → flowDev2 GD e' e) :
    ∀ i, i ∈ harts → post i (sN i) := by
  apply tierAAdequacyAnnGate GD N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts s0 sN n Hrun
    Hk0 Hend post Hwp HobAlloc gsrc Hreal Hmono
  intro e e' Hin
  rcases elemOfUnion.1 Hin with Hin | Hin
  · rcases HsPol e e' Hin with Hf | Hg
    · exact .inl (dev2DS GD Hcons gsrc Hreal Hmono e' e Hf)
    · exact .inr Hg
  · exact .inl (dev2DS GD Hcons gsrc Hreal Hmono e' e (Hlobp e e' Hin))

end wrapper

/-! # 2. Policies: the safe prefix, and the gate handout, on `gdefer` -/

/-- The deferral-safe PREFIX policy is deferral-safe for EVERY graph. -/
theorem polSafeDS (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (gsrc : Geid → GSet Geid)
    (e e' : Geid) : e' ∈ polSafeS gsrc GD e → polDS GD.gdG gsrc e' e := by
  intro H
  unfold polSafeS at H
  rw [elemOfListToSet, List.mem_filter] at H
  obtain ⟨Hin, Hall⟩ := H
  refine ⟨gmoPrefixLt _ Hcons.1 e e' Hin, fun s Hs => .inl ?_⟩
  apply (gmoLtBSpec _ _ _).1
  rw [List.all_eq_true] at Hall
  exact Hall s (elemOfElements.2 Hs)

/-- Safe prefix + gate-source handouts. -/
@[reducible] def PGate : Axpol where
  sPol := fun GD e => polSafeS gsrcD GD e ∪ gsrcD e
  lobp := fun _ _ => ∅

theorem PGateOk : ∀ e e', e' ∈ @Axpol.sPol PGate gdefer e ∪ @Axpol.lobp PGate gdefer e →
    polDS gdefer.gdG gsrcD e' e ∨ e' ∈ gsrcD e := by
  intro e e' Hin
  rcases elemOfUnion.1 Hin with Hin | Hin
  · rcases elemOfUnion.1 Hin with Hin | Hin
    · exact .inl (polSafeDS gdefer gdeferCat gsrcD e e' Hin)
    · exact .inr Hin
  · exact absurd Hin notElemOfEmpty

/-- The deferred read IS handed its gate's source, which is gmo-LATER: outside every
gmo-bounded route (AxTierA3/AxTierA4). -/
theorem PGateBackward : rE ∈ @Axpol.sPol PGate gdefer dE ∧ ¬ gmoLt gdefer.gdG rE dE := by
  refine ⟨elemOfUnionR ((gsrcDSpec _ _).2 ⟨.inl rfl, rfl⟩), fun Hlt => ?_⟩
  have Hlt' := gdeferDeferred
  obtain ⟨_, _, H1⟩ := Hlt
  obtain ⟨_, _, H2⟩ := Hlt'
  omega

/-- The refuted ledger policy is NOT admissible here: it hands the deferred read to its own
gate source. -/
theorem PRefNotOk : ¬ (∀ e e', e' ∈ @Axpol.sPol PRef gdefer e ∪ @Axpol.lobp PRef gdefer e →
    polDS gdefer.gdG gsrcD e' e ∨ e' ∈ gsrcD e) := by
  intro H
  have Hin : dE ∈ @Axpol.sPol PRef gdefer rE ∪ @Axpol.lobp PRef gdefer rE := by
    apply elemOfUnionL
    show dE ∈ (LawfulSet.ofList (gmoPrefix gdefer.gdG rE) : GSet Geid)
    have Hp : gmoPrefix gdefer.gdG rE = [dE, wxE, wfE] := by decide +kernel
    rw [Hp, elemOfListToSet]
    exact List.mem_cons_self
  rcases H rE dE Hin with ⟨_, Hds⟩ | Hg
  · rcases Hds rE ((gsrcDSpec _ _).2 ⟨.inl rfl, rfl⟩) with Hlt | ⟨Hr, _⟩
    · exact gmoLtIrrefl _ _ Hlt
    · obtain ⟨h, _⟩ := (gsrcDSpec _ _).1 Hr
      rcases h with h | h <;> exact absurd h (by decide)
  · obtain ⟨h, _⟩ := (gsrcDSpec _ _).1 Hg
    rcases h with h | h <;> exact absurd h (by decide)

end Weak
