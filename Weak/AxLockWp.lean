/-
Weak: **THE LOCK'S WP-LEVEL RULES** (AxSL tier, LB/AxSL lock slice) over `Weak.AxProtLock`'s
ghost protocol: `wpAmoswapAq` (the acquire RMW's WRITE half) and `wpReleaseStore` (the release
store), each with the flow equation it discharges (`flowEqAmoswapAq`, `flowEqRelease`).

Rocq: `iris/AxLockWp.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Mirror of `AxProtGate`'s `wp_read_owned_tok` template (a WP rule whose flow obligation is
discharged from resources) for the lock's two events.

* THE READ HALF of the fused RMW needs no rule: for `IRmw`, `aidentAdvRd id = 0`, so
  `wpPreStepDef`'s read case is the pure-guarded `∀ v, ⌜graphValue GD e = some v⌝ -∗ …` arm,
  which posts no flow equation; given the graph fact that the acquire reads 0 the `∀ v`
  specializes by `Option.some.inj`.  No lemma is built for it.
* THE WRITE HALF flows through `wpEvStep`/`flowEqDyn` at the SAME row position `(i, k)`;
  `flowEqAmoswapAq` discharges it via `protInvLockRmwStep`, depositing the pure fact
  `⌜gwritesByte GD.gdG w_rel L b0⌝` into `na`.
* THE `obSt` BRIDGE is an assumed capability of the concrete instance: `Hob_eq` relates
  `AxirisG.obStInterp` to the full `protInvLock`, the claimed domain `D` recovered from the
  abstract state through the getter/constructor pair `ob_D`/`mk_ob` (`Hmk_ob`).
* FINDING: the re-tied token minted by `protInvLockRmwStep` inside the flow proof is sealed in
  the flow equation's existential and is DROPPED there (affine BI); the copy handed to the
  continuation is an ordinary PREMISE of `wpAmoswapAq` (the acquiring thread's own token).
  `wpReleaseStore` CONSUMES the releasing thread's token.

**Fetches.** Nothing here depends on instruction fetches being graph read events: the file
speaks of the RMW's write event and the release store (`gwritesByte` over graph labels, `Lbl`
has no fetch constructor) and of `wpEvStep`'s write shape only.

## Deviations from Rocq

1. NAMES: camelCase (map below).  Lean-only helpers, file-qualified: `AxLockWp.annotInsertEq`
   (Rocq's inline `right_id_L … ∪; insert_union_singleton_l` rewrite) and
   `AxLockWp.naSplittingWfEmpty` (Rocq's inline `na_splitting_wf` at `∅ ∅`).
2. SECTION CONTEXT: Rocq's `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (as
   `AxWp` deviation 6); `axlogG Σ hent` ↦ `[AxlogG GF Hent]`, `ax_lockG Σ` ↦ `[AxLockG GF]`.
   Rocq's section variables `γ γc L x ob_D mk_ob Hmk_ob Hob_eq` (all used, `Proof using All`)
   are the explicit leading arguments of every lemma, in that order.
3. VOCABULARY (as `AxWp`/`AxProtLock`): `S k` ↦ `k + 1`; `gd_g GD` ↦ `GD.gdG`; `Some` ↦ `some`;
   `<[(i,k) := P]> na` ↦ `insert na (i, k) P`; `∅ : mea Σ` ↦ `(∅ : Mea GF)`; `tt` ↦ `()`;
   `WeakLitmus.b0/b1` ↦ `b0`/`b1`; `Z` ↦ `Int`; `agent` ↦ `Agent`.
4. STATEMENT SHAPES: Rocq's wand chains `A -∗ B -∗ C` are `⊢ A -∗ B -∗ C` (as `AxWp`
   deviation 7); pure premises and the `⊢`-closed `Hnalloc` stay `→`.

**Rocq → Lean name map.**  `flow_eq_release` `flowEqRelease`, `wp_release_store`
`wpReleaseStore`, `flow_eq_amoswap_aq` `flowEqAmoswapAq`, `wp_amoswap_aq` `wpAmoswapAq`.

**Not ported:** the `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxWp2
import Weak.AxProtLock

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-- Lean-only: the annotation map after an event with empty `naUnused` is the insert. -/
theorem AxLockWp.annotInsertEq {GF : BundledGFunctors} (na : Mea GF) (e : Geid) (R : IProp GF) :
    PartialMap.union (PartialMap.union {[e := R]} (∅ : Mea GF)) na = insert na e R := by
  have h1 : PartialMap.union ({[e := R]} : Mea GF) (∅ : Mea GF) = {[e := R]} :=
    mapUnionEmptyR (M := GMapF Geid)
  rw [h1]
  exact (insertUnionSingletonL (M := GMapF Geid)).symm

section lockWp

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
  [AxlogG GF Hent] [AxLockG GF]

/-- Lean-only: the empty splitting is well formed. -/
theorem AxLockWp.naSplittingWfEmpty (sLob : GSet Geid) (na : Mea GF) :
    ⊢ naSplittingWf sLob na (∅ : Mea GF) (∅ : Mea GF) := by
  unfold naSplittingWf
  isplitr
  · ipureintro
    rw [domEmpty]
    exact LawfulSet.empty_subset
  · iapply (BigSepM2.bigSepM2_empty _).2
    itrivial

/-! # 1. `wpReleaseStore` — the release event's write step -/

theorem flowEqRelease (γ γc : GName) (L x : Int)
    (ob_D : AxirisG.obSt GF → GSet Geid) (mk_ob : GSet Geid → AxirisG.obSt GF)
    (_Hmk_ob : ∀ D, ob_D (mk_ob D) = D)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInvLock L x γ γc GD s (ob_D σ))
    (GD : Gdexec) (i : Agent) (k : Nat) (e_last : Geid) (Hh H_L : List Hent)
    (Hcons : rvwmoCatConsistent GD)
    (Hwb : gwritesByte GD.gdG (i, k) L b0)
    (Hsingle : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' → a' = L)
    (Hgob : gobCat GD e_last (i, k))
    (Hval : graphData GD (i, k) = some [b0]) :
    ⊢ histAuth γ L 1 H_L -∗ tokTie GD γ x Hh {[e_last := (1 : Qp)]} -∗
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) (∅ : Mea GF)
        iprop(⌜gwritesByte GD.gdG (i, k) L b0⌝ ∗ ⌜graphData GD (i, k) = some [b0]⌝) := by
  unfold flowEqDyn
  iintro HaL Htie %σ %sOb %_Hsub %Hnin Hob _
  ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
  imod protInvLockReleaseStep L x γ γc GD sOb (ob_D σ) (i, k) e_last Hh H_L Hcons Hnin Hwb
    Hsingle Hgob $$ [$Hob $HaL $Htie] with Hinv'
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl [Hinv']
  · iapply (Hob_eq GD σ (({(i, k)} : GSet Geid) ∪ sOb)).2
    iexact Hinv'
  · isplitr
    · ipureintro
      exact Hwb
    · ipureintro
      exact Hval

theorem wpReleaseStore (γ γc : GName) (L x : Int)
    (ob_D : AxirisG.obSt GF → GSet Geid) (mk_ob : GSet Geid → AxirisG.obSt GF)
    (Hmk_ob : ∀ D, ob_D (mk_ob D) = D)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInvLock L x γ γc GD s (ob_D σ))
    (GD : Gdexec) (i : Agent) (k : Nat) (ls' : AxirisG.logTsT GF)
    (e_last : Geid) (Hh H_L : List Hent) (Ψ : Unit → IProp GF)
    (Hcons : rvwmoCatConsistent GD)
    (Hwb : gwritesByte GD.gdG (i, k) L b0)
    (Hsingle : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' → a' = L)
    (Hgob : gobCat GD e_last (i, k))
    (Hval : graphData GD (i, k) = some [b0])
    (Hnalloc : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
       AxirisG.annotInterp (insert na (i, k) iprop(⌜gwritesByte GD.gdG (i, k) L b0⌝))) :
    ⊢ histAuth γ L 1 H_L -∗
      tokTie GD γ x Hh {[e_last := (1 : Qp)]} -∗
      AxirisG.localInterp GD i (k + 1) ls' -∗
      Ψ () -∗
      wpEvStep GD i k (fun _ : Unit => True) (fun _ : Unit => graphData GD (i, k) = some [b0])
        (fun _ => k + 1) Ψ := by
  have Hn' : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union
        {[(i, k) := iprop(⌜gwritesByte GD.gdG (i, k) L b0⌝)]} (∅ : Mea GF)) na) := by
    simp only [AxLockWp.annotInsertEq]
    exact Hnalloc
  iintro HaL Htie Hloc HΨ
  ihave Hfeq := flowEqRelease γ γc L x ob_D mk_ob Hmk_ob Hob_eq GD i k e_last Hh H_L Hcons Hwb
    Hsingle Hgob Hval $$ HaL Htie
  unfold wpEvStep
  iintro %na Hpg
  ihave Hn := Hn'
  imod Hn $$ %na Hpg with Hna'
  imodintro
  inext
  imodintro
  iexists (), iprop(⌜gwritesByte GD.gdG (i, k) L b0⌝), (∅ : Mea GF), (∅ : Mea GF), ls'
  isplitr
  · ipureintro
    trivial
  isplitr
  · iapply AxLockWp.naSplittingWfEmpty
  iframe Hfeq Hna' Hloc HΨ

/-! # 2. `wpAmoswapAq` — the acquire RMW's write half -/

theorem flowEqAmoswapAq (γ γc : GName) (L x : Int)
    (ob_D : AxirisG.obSt GF → GSet Geid) (mk_ob : GSet Geid → AxirisG.obSt GF)
    (Hmk_ob : ∀ D, ob_D (mk_ob D) = D)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInvLock L x γ γc GD s (ob_D σ))
    (GD : Gdexec) (i : Agent) (k : Nat) (w_rel : Geid) (H_L : List Hent)
    (Hcons : rvwmoCatConsistent GD)
    (Hpol : w_rel ∈ Axpol.sPol GD (i, k))
    (Hunclaimed : ∀ σ : AxirisG.obSt GF, w_rel ∉ ob_D σ)
    (Hwb0 : gwritesByte GD.gdG w_rel L b0)
    (Hwb1 : gwritesByte GD.gdG (i, k) L b1)
    (Hsingle : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' → a' = L)
    (Hgob : gobCat GD w_rel (i, k))
    (Hval : graphData GD (i, k) = some [b1]) :
    ⊢ histAuth γ L 1 H_L -∗
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) (∅ : Mea GF)
        iprop(⌜gwritesByte GD.gdG w_rel L b0⌝ ∗ ⌜graphData GD (i, k) = some [b1]⌝) := by
  unfold flowEqDyn
  iintro HaL %σ %sOb %Hsub %Hnin Hob _
  ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
  have Hin : w_rel ∈ sOb := Hsub w_rel Hpol
  imod protInvLockRmwStep L x γ γc GD sOb (ob_D σ) w_rel (i, k) H_L Hcons Hin Hnin
    (Hunclaimed σ) Hwb0 Hwb1 Hsingle Hgob $$ [$Hob $HaL] with ⟨Hinv', %Hpure, -⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists (mk_ob (({w_rel} : GSet Geid) ∪ ob_D σ))
  isplitl [Hinv']
  · iapply (Hob_eq GD (mk_ob (({w_rel} : GSet Geid) ∪ ob_D σ))
      (({(i, k)} : GSet Geid) ∪ sOb)).2
    rw [Hmk_ob]
    iexact Hinv'
  · isplitr
    · ipureintro
      exact Hpure
    · ipureintro
      exact Hval

theorem wpAmoswapAq (γ γc : GName) (L x : Int)
    (ob_D : AxirisG.obSt GF → GSet Geid) (mk_ob : GSet Geid → AxirisG.obSt GF)
    (Hmk_ob : ∀ D, ob_D (mk_ob D) = D)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInvLock L x γ γc GD s (ob_D σ))
    (GD : Gdexec) (i : Agent) (k : Nat) (ls' : AxirisG.logTsT GF)
    (w_rel : Geid) (H_L Ht : List Hent) (Ψ : Unit → IProp GF)
    (Hcons : rvwmoCatConsistent GD)
    (Hpol : w_rel ∈ Axpol.sPol GD (i, k))
    (Hunclaimed : ∀ σ : AxirisG.obSt GF, w_rel ∉ ob_D σ)
    (Hwb0 : gwritesByte GD.gdG w_rel L b0)
    (Hwb1 : gwritesByte GD.gdG (i, k) L b1)
    (Hsingle : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' → a' = L)
    (Hgob : gobCat GD w_rel (i, k))
    (Hval : graphData GD (i, k) = some [b1])
    (Hnalloc : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
       AxirisG.annotInterp (insert na (i, k) iprop(⌜gwritesByte GD.gdG w_rel L b0⌝))) :
    ⊢ histAuth γ L 1 H_L -∗
      tokTie GD γ x Ht {[(i, k) := (1 : Qp)]} -∗
      AxirisG.localInterp GD i (k + 1) ls' -∗
      (tokTie GD γ x Ht {[(i, k) := (1 : Qp)]} -∗ Ψ ()) -∗
      wpEvStep GD i k (fun _ : Unit => True) (fun _ : Unit => graphData GD (i, k) = some [b1])
        (fun _ => k + 1) Ψ := by
  have Hn' : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union
        {[(i, k) := iprop(⌜gwritesByte GD.gdG w_rel L b0⌝)]} (∅ : Mea GF)) na) := by
    simp only [AxLockWp.annotInsertEq]
    exact Hnalloc
  iintro HaL Htie Hloc Hcont
  ihave Hfeq := flowEqAmoswapAq γ γc L x ob_D mk_ob Hmk_ob Hob_eq GD i k w_rel H_L Hcons Hpol
    Hunclaimed Hwb0 Hwb1 Hsingle Hgob Hval $$ HaL
  unfold wpEvStep
  iintro %na Hpg
  ihave Hn := Hn'
  imod Hn $$ %na Hpg with Hna'
  imodintro
  inext
  imodintro
  iexists (), iprop(⌜gwritesByte GD.gdG w_rel L b0⌝), (∅ : Mea GF), (∅ : Mea GF), ls'
  isplitr
  · ipureintro
    trivial
  isplitr
  · iapply AxLockWp.naSplittingWfEmpty
  iframe Hfeq Hna' Hloc
  iapply Hcont $$ Htie

end lockWp

end Weak
