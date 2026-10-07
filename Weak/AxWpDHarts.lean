/-
Weak: **`WPd` THREADED ACROSS ALL HARTS OF A RUN** (AxSL tier; design §7.A, milestone A4), plus
the `eaLocalWf` → `ordEaTodoL` connector feeding `AxAdequacyL.adequacyOrdL` off the run's output.

Rocq: `iris/AxWpDHarts.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§0: hart-indexed `filter` helpers, and `wpdStepsNBind`, the Kleisli composition of `wpdStepsN`
(built from `wpdStepsNMono` and the flattening `wpdStepsNFlatten`).
§1: `wpdHartsNstepsGenM` runs a whole LIST of harts SEQUENTIALLY through the one shared
`annotInterp` (never unioning per-hart maps): hart `i`'s run only touches events whose first
component is `i` (`AxWpDSteps` §1.5), so the next hart `j ≠ i` starts its own `wpdNstepsM` run from
the first hart's output map.  The induction is over the hart list, from an arbitrary `(na0, ea0)`
whose slice for every hart still to run is empty (`Hna0`); `wpdHartsNstepsM` is the `∅` instance.
§2: `ordEaTodoLOfEaLocalWf`: `eaLocalWf`'s per-node big conjunction over `na` is, pointwise,
`ordEaTodoL`'s body over any duplicate-free list `L` enumerating `dom na`.

## Deviations from Rocq

1. NAMES: camelCase (map below).  `dom` ↦ `FiniteMap.dom_set … : GSet Geid`, `filter` ↦
   `FiniteSet.filter (fun e => decide …)`, `⋃` ↦ `MachCSL.unionList`, `sum_list (n <$> l)` ↦
   `(l.map n).sum`, `NoDup` ↦ `List.Nodup`, `list_to_set` ↦ `LawfulSet.ofList`.
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (as AxWpDSteps).  Wand chains are
   stated `⊢ A -∗ B -∗ …` (AxWp deviation 7).
2. O2 STAGE C: nothing fetch-specific here; the hart steps are `AxWpDSteps.astepAnyNfGv` (whose
   program arm carries the boot-image pin, Q8).
3. The old-name `Definition`s (`wpd_harts_nsteps_gen`, `wpd_harts_nsteps`) are theorems with their
   statements spelled out at `rvwmoCatConsistent` (via the `wpd` abbrev), as in AxWpDSteps.

**Rocq → Lean name map.**  `filter_hart_eq_of_neq` `filterHartEqOfNeq`,
`filter_hart_eids_before_neq` `filterHartEidsBeforeNeq`, `wpd_stepsN_flatten` `wpdStepsNFlatten`,
`wpd_stepsN_bind` `wpdStepsNBind`, `ea_local_wf_empty` `eaLocalWfEmpty`, `wpd_harts_nsteps_genM`
`wpdHartsNstepsGenM`, `wpd_harts_nstepsM` `wpdHartsNstepsM`, `wpd_harts_nsteps_gen`
`wpdHartsNstepsGen`, `wpd_harts_nsteps` `wpdHartsNsteps`, `ord_ea_todo_L_of_ea_local_wf`
`ordEaTodoLOfEaLocalWf`.

**Dropped:** only the §3 `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxWpDSteps
import Weak.AxAdequacyL

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 0. Small pure helpers, and `wpdStepsN`'s Kleisli composition -/

/-- Filtering to hart `j` after filtering OUT hart `i ≠ j` is filtering to `j` directly. -/
theorem filterHartEqOfNeq (i j : Agent) (X : GSet Geid) :
    j ≠ i →
    FiniteSet.filter (fun e : Geid => decide (e.1 = j))
        (FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) X) =
      FiniteSet.filter (fun e : Geid => decide (e.1 = j)) X := by
  intro Hne
  rw [setEq]
  intro e
  simp only [elemOfFilter, decide_eq_true_eq]
  constructor
  · rintro ⟨hj, _, hx⟩
    exact ⟨hj, hx⟩
  · rintro ⟨hj, hx⟩
    exact ⟨hj, fun h => Hne (hj.symm.trans h), hx⟩

/-- `eidsBefore GD i k` holds only hart-`i` events: its slice for another hart is empty. -/
theorem filterHartEidsBeforeNeq (GD : Gdexec) (i j : Agent) (k : Nat) :
    j ≠ i → FiniteSet.filter (fun e : Geid => decide (e.1 = j)) (eidsBefore GD i k) = ∅ := by
  intro Hne
  rw [setEq]
  intro e
  simp only [elemOfFilter, decide_eq_true_eq, elemOfEidsBefore, elemOfEmpty, iff_false]
  rintro ⟨hj, hi, _⟩
  exact Hne (hj.symm.trans hi)

section wpdStepsNBind
variable {GF : BundledGFunctors}

/-- `n1` rounds around a payload of `n2` more rounds collapse to `n1 + n2` rounds. -/
theorem wpdStepsNFlatten (n1 n2 : Nat) (P : IProp GF) :
    wpdStepsN n1 (wpdStepsN n2 P) ⊢ wpdStepsN (n1 + n2) P := by
  induction n1 with
  | zero =>
    rw [Nat.zero_add]
    exact AxWpDSteps.bupdWpdStepsN n2 P
  | succ n1 ih =>
    rw [Nat.add_right_comm]
    show iprop(|==> ▷ wpdStepsN n1 (wpdStepsN n2 P)) ⊢ iprop(|==> ▷ wpdStepsN (n1 + n2) P)
    iintro H
    imod H
    imodintro
    inext
    iapply ih $$ H

/-- THE COMBINATOR: `n1` steps to `P`, then `n2` more from whatever `P` hands over. -/
theorem wpdStepsNBind (n1 n2 : Nat) (P Q : IProp GF) :
    ⊢ wpdStepsN n1 P -∗ (P -∗ wpdStepsN n2 Q) -∗ wpdStepsN (n1 + n2) Q := by
  iintro H HPQ
  ihave H := wpdStepsNMono n1 P (wpdStepsN n2 Q) $$ HPQ H
  iapply wpdStepsNFlatten n1 n2 Q $$ H

end wpdStepsNBind

/-! # 1. `wpdHartsNsteps`: a whole hart list, sequentially, through one `annotInterp` -/

section wpdHarts
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem eaLocalWfEmpty (GD : Gdexec) : ⊢ eaLocalWf GD (∅ : Sra GF) (∅ : Mea GF) := by
  iunfold eaLocalWf
  isplitr
  · ipureintro
    rw [domEmpty, domEmpty]
  isplitr
  · iapply BigSepM.bigSepM_empty.2
    itrivial
  · iapply BigSepM.bigSepM_empty.2
    itrivial

variable (M : Gdexec → Prop) [GModel M]

/-- THE GENERALIZED FORM: from an arbitrary `(na0, ea0)` of which every hart still to run owns an
EMPTY slice (`Hna0`). -/
theorem wpdHartsNstepsGenM (GD : Gdexec) (Hwf : axpolWf) (Hcons : M GD) (st : Stuckness)
    (harts : List Agent) (Hnd : harts.Nodup) (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ i, i ∈ harts → nsteps (astepAnyNfGv GD i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Φ : Agent → Athread → IProp GF) (na0 : Mea GF) (ea0 : Sra GF)
    (Hna0 : ∀ i, i ∈ harts →
      FiniteSet.filter (fun e : Geid => decide (e.1 = i)) (FiniteMap.dom_set na0 : GSet Geid) =
        eidsBefore GD i 0) :
    ⊢ AxirisG.annotInterp na0 -∗ eaLocalWf GD ea0 na0 -∗ □ AxirisG.gconstInterp GD -∗
      ([∗list] i ∈ harts,
        (∃ ls, AxirisG.localInterp GD i 0 ls) ∗ wpdM M st i (s0 i) (Φ i)) -∗
      wpdStepsN (harts.map n).sum iprop(∃ (na : Mea GF) (ea : Sra GF),
        ⌜(FiniteMap.dom_set na : GSet Geid) = (FiniteMap.dom_set na0 : GSet Geid) ∪
          unionList (harts.map fun i => eidsBefore GD i (sN i).atK)⌝ ∗
        AxirisG.annotInterp na ∗ eaLocalWf GD ea na ∗
        [∗list] i ∈ harts,
          (∃ ls', AxirisG.localInterp GD i (sN i).atK ls') ∗ wpdM M st i (sN i) (Φ i)) := by
  induction harts generalizing na0 ea0 with
  | nil =>
    simp only [List.map_nil, List.sum_nil, unionListNil, wpdStepsN]
    iintro Hannot Hea #_ _
    imodintro
    iexists na0, ea0
    isplitr
    · ipureintro
      exact unionEmptyR.symm
    isplitl [Hannot]
    · iexact Hannot
    isplitl [Hea]
    · iexact Hea
    · iapply BigSepL.bigSepL_nil.2
      itrivial
  | cons i harts' ih =>
    obtain ⟨Hi_nin, Hnd'⟩ := List.nodup_cons.1 Hnd
    have Hhere : i ∈ i :: harts' := List.mem_cons.2 (.inl rfl)
    have Hrun_i := Hrun i Hhere
    have Hk0_i := Hk0 i Hhere
    have Hna0_i := Hna0 i Hhere
    have Hrun' : ∀ j, j ∈ harts' → nsteps (astepAnyNfGv GD j) (n j) (s0 j) (sN j) :=
      fun j hj => Hrun j (List.mem_cons_of_mem i hj)
    have Hk0' : ∀ j, j ∈ harts' → (s0 j).atK = 0 :=
      fun j hj => Hk0 j (List.mem_cons_of_mem i hj)
    simp only [List.map_cons, List.sum_cons, unionListCons]
    iintro Hannot Hea #Hgconst Hbig
    ihave Hbig := BigSepL.bigSepL_cons.1 $$ Hbig
    icases Hbig with ⟨⟨⟨%ls, Hloc⟩, HWP⟩, Htail⟩
    ihave Hnap : naAtProgress GD i (s0 i).atK na0 $$ []
    · iunfold naAtProgress
      ipureintro
      rw [Hk0_i]
      exact Hna0_i
    ihave Hloc' : AxirisG.localInterp GD i (s0 i).atK ls $$ [Hloc]
    · rw [Hk0_i]
      iexact Hloc
    ihave Hi := wpdNstepsM M GD Hwf Hcons i st (n i) (s0 i) (sN i) Hrun_i na0 ea0 ls (Φ i)
      $$ Hnap Hannot Hea Hloc' Hgconst HWP
    iapply wpdStepsNBind (n i) (harts'.map n).sum $$ Hi [Htail]
    iintro ⟨%na1, %ea1, %ls1, -, %Hdom1, Hannot1, Hea1, Hloc1, HWP1⟩
    have Hna1 : ∀ j, j ∈ harts' →
        FiniteSet.filter (fun e : Geid => decide (e.1 = j)) (FiniteMap.dom_set na1 : GSet Geid) =
          eidsBefore GD j 0 := by
      intro j hj
      have Hjni : j ≠ i := fun h => Hi_nin (h ▸ hj)
      rw [Hdom1, filterUnion, filterHartEqOfNeq i j _ Hjni,
        filterHartEidsBeforeNeq GD i j _ Hjni, unionEmptyR]
      exact Hna0 j (List.mem_cons_of_mem i hj)
    ihave Hrec := ih Hnd' Hrun' Hk0' na1 ea1 Hna1 $$ Hannot1 Hea1 Hgconst Htail
    iapply wpdStepsNMono $$ [Hloc1 HWP1] Hrec
    iintro ⟨%na, %ea, %Hdomf, Hannotf, Heaf, Htailf⟩
    iexists na, ea
    isplitr
    · ipureintro
      have Hpin := naDomPinRefl i (FiniteMap.dom_set na0 : GSet Geid) GD 0 Hna0_i
      rw [eidsBefore0, unionEmptyR] at Hpin
      rw [Hdomf, Hdom1, ← Hpin]
      exact unionAssoc.symm
    isplitl [Hannotf]
    · iexact Hannotf
    isplitl [Heaf]
    · iexact Heaf
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hloc1 HWP1]
    · isplitl [Hloc1]
      · iexists ls1
        iexact Hloc1
      · iexact HWP1
    · iexact Htailf

/-- THE TASK'S OWN FORM: every hart starts from the same `annotInterp ∅`. -/
theorem wpdHartsNstepsM (GD : Gdexec) (Hwf : axpolWf) (Hcons : M GD) (st : Stuckness)
    (harts : List Agent) (Hnd : harts.Nodup) (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ i, i ∈ harts → nsteps (astepAnyNfGv GD i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Φ : Agent → Athread → IProp GF) :
    ⊢ AxirisG.annotInterp (∅ : Mea GF) -∗ □ AxirisG.gconstInterp GD -∗
      ([∗list] i ∈ harts,
        (∃ ls, AxirisG.localInterp GD i 0 ls) ∗ wpdM M st i (s0 i) (Φ i)) -∗
      wpdStepsN (harts.map n).sum iprop(∃ (na : Mea GF) (ea : Sra GF),
        ⌜(FiniteMap.dom_set na : GSet Geid) =
          unionList (harts.map fun i => eidsBefore GD i (sN i).atK)⌝ ∗
        AxirisG.annotInterp na ∗ eaLocalWf GD ea na ∗
        [∗list] i ∈ harts,
          (∃ ls', AxirisG.localInterp GD i (sN i).atK ls') ∗ wpdM M st i (sN i) (Φ i)) := by
  have Hna0 : ∀ i, i ∈ harts →
      FiniteSet.filter (fun e : Geid => decide (e.1 = i))
          (FiniteMap.dom_set (∅ : Mea GF) : GSet Geid) = eidsBefore GD i 0 := by
    intro i _
    rw [domEmpty, filterEmpty, eidsBefore0]
  iintro Hannot #Hgconst H
  ihave Hea0 := eaLocalWfEmpty (GF := GF) GD
  ihave H := wpdHartsNstepsGenM M GD Hwf Hcons st harts Hnd s0 sN n Hrun Hk0 Φ ∅ ∅ Hna0
    $$ Hannot Hea0 Hgconst H
  iapply wpdStepsNMono $$ [] H
  iintro ⟨%na, %ea, %Hdom, Hannot', Hea', Htail⟩
  iexists na, ea
  isplitr
  · ipureintro
    rw [domEmpty, unionEmptyL] at Hdom
    exact Hdom
  isplitl [Hannot']
  · iexact Hannot'
  isplitl [Hea']
  · iexact Hea'
  · iexact Htail

end wpdHarts

section wpdCatHarts
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- Rocq `wpd_harts_nsteps_gen` (the riscv.cat instance). -/
theorem wpdHartsNstepsGen (GD : Gdexec) (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (st : Stuckness) (harts : List Agent) (Hnd : harts.Nodup) (s0 sN : Agent → Athread)
    (n : Agent → Nat)
    (Hrun : ∀ i, i ∈ harts → nsteps (astepAnyNfGv GD i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Φ : Agent → Athread → IProp GF) (na0 : Mea GF) (ea0 : Sra GF)
    (Hna0 : ∀ i, i ∈ harts →
      FiniteSet.filter (fun e : Geid => decide (e.1 = i)) (FiniteMap.dom_set na0 : GSet Geid) =
        eidsBefore GD i 0) :
    ⊢ AxirisG.annotInterp na0 -∗ eaLocalWf GD ea0 na0 -∗ □ AxirisG.gconstInterp GD -∗
      ([∗list] i ∈ harts,
        (∃ ls, AxirisG.localInterp GD i 0 ls) ∗ wpd st i (s0 i) (Φ i)) -∗
      wpdStepsN (harts.map n).sum iprop(∃ (na : Mea GF) (ea : Sra GF),
        ⌜(FiniteMap.dom_set na : GSet Geid) = (FiniteMap.dom_set na0 : GSet Geid) ∪
          unionList (harts.map fun i => eidsBefore GD i (sN i).atK)⌝ ∗
        AxirisG.annotInterp na ∗ eaLocalWf GD ea na ∗
        [∗list] i ∈ harts,
          (∃ ls', AxirisG.localInterp GD i (sN i).atK ls') ∗ wpd st i (sN i) (Φ i)) :=
  wpdHartsNstepsGenM rvwmoCatConsistent GD Hwf Hcons st harts Hnd s0 sN n Hrun Hk0 Φ na0 ea0 Hna0

/-- Rocq `wpd_harts_nsteps` (the riscv.cat instance). -/
theorem wpdHartsNsteps (GD : Gdexec) (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (st : Stuckness) (harts : List Agent) (Hnd : harts.Nodup) (s0 sN : Agent → Athread)
    (n : Agent → Nat)
    (Hrun : ∀ i, i ∈ harts → nsteps (astepAnyNfGv GD i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Φ : Agent → Athread → IProp GF) :
    ⊢ AxirisG.annotInterp (∅ : Mea GF) -∗ □ AxirisG.gconstInterp GD -∗
      ([∗list] i ∈ harts,
        (∃ ls, AxirisG.localInterp GD i 0 ls) ∗ wpd st i (s0 i) (Φ i)) -∗
      wpdStepsN (harts.map n).sum iprop(∃ (na : Mea GF) (ea : Sra GF),
        ⌜(FiniteMap.dom_set na : GSet Geid) =
          unionList (harts.map fun i => eidsBefore GD i (sN i).atK)⌝ ∗
        AxirisG.annotInterp na ∗ eaLocalWf GD ea na ∗
        [∗list] i ∈ harts,
          (∃ ls', AxirisG.localInterp GD i (sN i).atK ls') ∗ wpd st i (sN i) (Φ i)) :=
  wpdHartsNstepsM rvwmoCatConsistent GD Hwf Hcons st harts Hnd s0 sN n Hrun Hk0 Φ

end wpdCatHarts

/-! # 2. `ordEaTodoL` from `eaLocalWf` -/

section ordEaTodoLConn
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem ordEaTodoLOfEaLocalWf (GD : Gdexec) (ea : Sra GF) (na : Mea GF) (L : List Geid)
    (Hnd : L.Nodup) (Hdom : (LawfulSet.ofList L : GSet Geid) = FiniteMap.dom_set na) :
    eaLocalWf GD ea na ⊢
      iprop(⌜(FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na⌝ ∗
        ⌜∀ e gm, get? ea e = some gm →
          (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e⌝ ∗
        ordEaTodoL GD ea na L 0) := by
  have h1 : ([∗map] e ↦ R ∈ na,
      AxWp.fromOption (fun flowIn => flowEqEa GD e (Axpol.sPol GD e) flowIn ea R) iprop(emp)
        (get? ea e)) ⊢
      [∗map] e ↦ _R ∈ na, AxWp.fromOption (fun R0 => AxWp.fromOption
          (fun flowIn => flowEqEa GD e (Axpol.sPol GD e) flowIn ea R0) iprop(emp) (get? ea e))
        iprop(emp) (get? na e) :=
    BigSepM.bigSepM_mono fun {k v} hlk => by
      rw [hlk]
      exact .rfl
  have h2 := (BigSepM.bigSepM_dom (S := GSet Geid) (m := na)
    (Φ := fun e => AxWp.fromOption (fun R0 => AxWp.fromOption
          (fun flowIn => flowEqEa GD e (Axpol.sPol GD e) flowIn ea R0) iprop(emp) (get? ea e))
        iprop(emp) (get? na e))).1
  rw [← Hdom] at h2
  have h3 := (BigSepS.bigSepS_of_list (S := GSet Geid) (l := L)
    (Φ := fun e => AxWp.fromOption (fun R0 => AxWp.fromOption
          (fun flowIn => flowEqEa GD e (Axpol.sPol GD e) flowIn ea R0) iprop(emp) (get? ea e))
        iprop(emp) (get? na e)) Hnd).1
  iunfold eaLocalWf
  iintro ⟨%Hdom_ea, Hlob, Hbig⟩
  ihave %Hlob := BigSepM.bigSepM_pure.1 $$ Hlob
  isplitr
  · ipureintro
    exact Hdom_ea
  isplitr
  · ipureintro
    exact Hlob
  unfold ordEaTodoL
  rw [List.drop_zero]
  iapply (h1.trans (h2.trans h3)) $$ Hbig

end ordEaTodoLConn

end Weak
