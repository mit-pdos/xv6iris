/-
Weak: **THE LOCK HANDOFF TOKEN ALONG `lob`** (AxSL tier): the acquire RMW's write half deposits
the MIXED annotation `⌜w_rel writes b0⌝ ∗ tokTie …` at its OWN `na` slot instead of taking the
token as a WP premise; a later `lob`-after read claims it through `flowIn`.

Rocq: `iris/AxLockWp2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxLockWp.wp_amoswap_aq` took the re-tied `tokTie` as a PREMISE, because a mixed annotation at
the acquire's `na` slot was believed to break `AxGateAdeq.na_pure_global`; `AxGateAdeq2` shows
the purity extraction only needs an ENTAILMENT, so the mixed slot is sound.  §1:
`flowEqAmoswapAqLob` (the acquire's flow equation, via `protInvLockRmwStep`) and the full WP rule
`wpAmoswapAqLob`: the acquire posts `R_acq := ⌜gwritesByte w_rel L b0⌝ ∗ (∃ H, tokTie GD γ x H
{[acq := 1]})` at its own slot (an empty `naUsed`/`naUnused` split; the annotation map after the
event is `insert na (i, k) R_acq`, supplied by the caller's `Hnalloc`) and hands NOTHING
token-shaped to its continuation — SMELL TEST: no premise of `wpAmoswapAqLob` mentions `tokTie`
(only `Hnalloc`'s conclusion, the deposit).  §2: `protInvLockReadStep` (a read may always join
the validated set) and `flowEqLockReadLob`: the read `r_x`, `lob`-after the acquire, pulls the
token out of its `flowIn` bag through a thin wand and concludes as `AxLockOwn.lockReadOwn`.
§3: the PRIMED versions over `protInvLock'` (`protInvLockRmwStep'`), depositing `tokTie GD γ x Hh
{[(i, k) := 1]}` with NO existential; the `obSt`/`hm` bridge is passed as explicit arguments.

**Fetches.** Nothing here depends on instruction fetches being graph read events: the file
speaks of `gwritesByte`/`greadsByte`/`gobCat`/`gacqPo` over graph labels (`Lbl` has no fetch
constructor) and of `wpEvStep`/`flowEqDyn` generically.

## Deviations from Rocq

1. NAMES: camelCase (map below); none of the Rocq names is duplicated.  Lean-only helper,
   file-qualified: `AxLockWp2.unionSingletonEmpty` (Rocq's inline `right_id_L ∅ (∪)` +
   `insert_union_singleton_l` rewrite).
2. VOCABULARY (as `AxProtLock` deviation 2 and `AxWp` deviation 2): `{[e]} ∪ s` ↦ `({e} : GSet
   Geid) ∪ s`; `<[e := R]> na` ↦ `insert na e R`; map unions ↦ `PartialMap.union`; `gd_g GD` ↦
   `GD.gdG`; `H.*1` ↦ `H.map Prod.fst`; `last H` ↦ `H.getLast?`; `gpo` ↦ `WeakRvwmoGraph.gpo`;
   `WeakLitmus.b0/b1` ↦ `b0`/`b1`; `S k` ↦ `k + 1`; `Z` ↦ `Int`; `bv 8` ↦ `BitVec 8`;
   `gmap geid (list hent)` ↦ `GMapF Geid (List Hent)`, `hm !! e` ↦ `get? hm e`.
3. `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (as `AxWp` deviation 6).
4. SECTION VARIABLES: §§1–2's `Context (γ γc) (L x) (ob_D mk_ob Hmk_ob Hob_eq)` are explicit
   leading arguments of every §1–2 lemma (as after Rocq's section close), in that order;
   `protInvLockReadStep` takes only `L x γ γc` of them (it uses no bridge).  §3 takes them
   explicitly already in Rocq.
5. STATEMENT SHAPES (as `AxWp` deviation 7): `A -∗ B` ↦ `A ⊢ B`; `A -∗ B -∗ C (-∗ D)` ↦
   `⊢ A -∗ B -∗ C (-∗ D)`; pure premises `→`; `Hnalloc` stays a `⊢`-closed premise.

**Rocq → Lean name map.**  `flow_eq_amoswap_aq_lob` `flowEqAmoswapAqLob`, `wp_amoswap_aq_lob`
`wpAmoswapAqLob`, `prot_inv_lock_read_step` `protInvLockReadStep`, `flow_eq_lock_read_lob`
`flowEqLockReadLob`, `flow_eq_amoswap_aq_lob'` `flowEqAmoswapAqLob'`, `wp_amoswap_aq_lob'`
`wpAmoswapAqLob'`.

**Not ported:** the `Print Assumptions` audits (the lint's axiom check covers them).
-/
import Weak.AxWp2
import Weak.AxReadAll
import Weak.AxProtLock
import Weak.AxLockOwn

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-- Lean-only: the annotation map after a single-annotation event with an empty split. -/
theorem AxLockWp2.unionSingletonEmpty {GF : BundledGFunctors} (na : Mea GF) (e : Geid)
    (R : IProp GF) :
    PartialMap.union (PartialMap.union {[e := R]} (∅ : Mea GF)) na = insert na e R := by
  have h1 : PartialMap.union ({[e := R]} : Mea GF) (∅ : Mea GF) = {[e := R]} :=
    mapUnionEmptyR (M := GMapF Geid)
  rw [h1]
  exact (insertUnionSingletonL (M := GMapF Geid)).symm

/-! # 1. `wpAmoswapAqLob` — the acquire RMW's write half, depositing the mixed annotation -/

section lockWp2

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF] [Axpol]
  [AxlogG GF Hent] [AxLockG GF]

theorem flowEqAmoswapAqLob (γ γc : GName) (L x : Int)
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
    histAuth (GF := GF) γ L 1 H_L ⊢
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) ∅
        iprop((⌜gwritesByte GD.gdG w_rel L b0⌝ ∗
            (∃ H, tokTie GD γ x H {[(i, k) := (1 : Qp)]})) ∗
          ⌜graphData GD (i, k) = some [b1]⌝) := by
  unfold flowEqDyn
  iintro HaL %σ %sOb %Hsub %Hnin Hob -
  ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
  have hin : w_rel ∈ sOb := Hsub _ Hpol
  imod protInvLockRmwStep L x γ γc GD sOb (ob_D σ) w_rel (i, k) H_L Hcons hin Hnin
      (Hunclaimed σ) Hwb0 Hwb1 Hsingle Hgob $$ [$Hob $HaL] with ⟨Hinv', %Hpure, Htie⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists mk_ob (({w_rel} : GSet Geid) ∪ ob_D σ)
  isplitl [Hinv']
  · iapply (Hob_eq GD (mk_ob (({w_rel} : GSet Geid) ∪ ob_D σ))
      (({(i, k)} : GSet Geid) ∪ sOb)).2
    rw [Hmk_ob]
    iexact Hinv'
  · isplitl [Htie]
    · isplitl []
      · ipureintro
        exact Hpure
      · iexact Htie
    · ipureintro
      exact Hval

/-- THE FULL WP RULE: no `tokTie` premise, nothing token-shaped handed to `Ψ` — the token
travels solely inside the deposited `na` slot. -/
theorem wpAmoswapAqLob (γ γc : GName) (L x : Int)
    (ob_D : AxirisG.obSt GF → GSet Geid) (mk_ob : GSet Geid → AxirisG.obSt GF)
    (Hmk_ob : ∀ D, ob_D (mk_ob D) = D)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInvLock L x γ γc GD s (ob_D σ))
    (GD : Gdexec) (i : Agent) (k : Nat) (ls' : AxirisG.logTsT GF) (w_rel : Geid)
    (H_L : List Hent) (Ψ : Unit → IProp GF)
    (Hcons : rvwmoCatConsistent GD)
    (Hpol : w_rel ∈ Axpol.sPol GD (i, k))
    (Hunclaimed : ∀ σ : AxirisG.obSt GF, w_rel ∉ ob_D σ)
    (Hwb0 : gwritesByte GD.gdG w_rel L b0)
    (Hwb1 : gwritesByte GD.gdG (i, k) L b1)
    (Hsingle : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' → a' = L)
    (Hgob : gobCat GD w_rel (i, k))
    (Hval : graphData GD (i, k) = some [b1])
    (Hnalloc : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (insert na (i, k)
        iprop(⌜gwritesByte GD.gdG w_rel L b0⌝ ∗
          (∃ H, tokTie GD γ x H {[(i, k) := (1 : Qp)]})))) :
    ⊢ histAuth γ L 1 H_L -∗ AxirisG.localInterp GD i (k + 1) ls' -∗ Ψ () -∗
      wpEvStep GD i k (fun _ : Unit => True) (fun _ : Unit => graphData GD (i, k) = some [b1])
        (fun _ => k + 1) Ψ := by
  iintro HaL Hloc HΨ
  ihave Hfeq := flowEqAmoswapAqLob γ γc L x ob_D mk_ob Hmk_ob Hob_eq GD i k w_rel H_L Hcons
    Hpol Hunclaimed Hwb0 Hwb1 Hsingle Hgob Hval $$ HaL
  unfold wpEvStep
  iintro %na Hpg
  ihave Hn := Hnalloc
  imod Hn $$ %na Hpg with Hna'
  imodintro
  inext
  imodintro
  iexists (), iprop(⌜gwritesByte GD.gdG w_rel L b0⌝ ∗
    (∃ H, tokTie GD γ x H {[(i, k) := (1 : Qp)]})), ∅, ∅, ls'
  isplitr
  · ipureintro
    trivial
  isplitr
  · unfold naSplittingWf
    isplitl []
    · ipureintro
      rw [domEmpty]
      exact LawfulSet.empty_subset
    · iapply (BigSepM2.bigSepM2_empty _).2
      itrivial
  iframe Hfeq
  rw [AxLockWp2.unionSingletonEmpty]
  iframe Hna' Hloc HΨ

/-! # 2. `flowEqLockReadLob` — the read `r_x` claims the token via `flowIn` -/

/-- A read event may always join `protInvLock`'s validated set (`ΦLock` is vacuous at a
non-write). -/
theorem protInvLockReadStep (L x : Int) (γ γc : GName) (r : Geid) (s D : GSet Geid)
    (GD : Gdexec) :
    r ∉ s → gisW GD.gdG r = false →
    protInvLock (GF := GF) L x γ γc GD s D ⊢
      protInvLock L x γ γc GD (({r} : GSet Geid) ∪ s) D := by
  intro hnin hr
  iintro Hinv
  icases (protInvLockUnfold L x γ γc GD s D).1 $$ Hinv with ⟨Hc, Hpo, Hlocks⟩
  iapply (protInvLockUnfold L x γ γc GD (({r} : GSet Geid) ∪ s) D).2
  isplitl [Hc]
  · iexact Hc
  isplitl [Hpo]
  · iapply protInvReadStep γ GD s r hnin hr
    iexact Hpo
  iapply (AxProtLock.bigSepSUnionSingleton (Φ := ΦLock L x γ γc GD) hnin).2
  isplitl []
  · iapply AxProtLock.ΦLockVacuous L x γ γc GD r
    intro hbad
    have hisw := AxProt.gwritesByteGisW _ _ _ _ hbad
    rw [hisw] at hr
    cases hr
  · iexact Hlocks

theorem flowEqLockReadLob (γ γc : GName) (L x : Int)
    (ob_D : AxirisG.obSt GF → GSet Geid) (mk_ob : GSet Geid → AxirisG.obSt GF)
    (_Hmk_ob : ∀ D, ob_D (mk_ob D) = D)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInvLock L x γ γc GD s (ob_D σ))
    (GD : Gdexec) (acq r_x : Geid) (Hh : List Hent) (w_x : Geid) (vx : BitVec 8)
    (s_ob0 : GSet Geid) (flowIn : Mea GF)
    (Hcons : rvwmoCatConsistent GD)
    (Hnw : gisW GD.gdG r_x = false)
    (Hwr : ∀ p, p ∈ Hh → gwritesByte GD.gdG p.1 x p.2)
    (Hch : chainWith (gmoLt GD.gdG) (Hh.map Prod.fst))
    (Hown : ∀ w v, gwritesByte GD.gdG w x v → WeakRvwmoGraph.gpo GD.gdG w r_x →
      w ∈ Hh.map Prod.fst)
    (Hlast : Hh.getLast? = some (w_x, vx))
    (Hacq : gacqPo GD.gdG acq r_x)
    (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v) :
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ tokTie GD γ x Hh {[acq := (1 : Qp)]}) -∗
      (∀ w v, ⌜gwritesByte GD.gdG w x v⌝ -∗ ⌜gmoLt GD.gdG w r_x⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ x H') -∗
      flowEqDyn GD r_x s_ob0 flowIn
        iprop(⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝) := by
  iintro Hflowin Hsn
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Htie := Hflowin $$ Hflow
  ihave %Hres := lockReadOwn GD γ x Hh w_x acq r_x vx Hcons Hwr Hch Hown Hlast Hacq Hrd
    $$ [$Htie $Hsn]
  ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
  ihave Hob' := protInvLockReadStep L x γ γc r_x sOb (ob_D σ) GD Hnin Hnw $$ Hob
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl [Hob']
  · iapply (Hob_eq GD σ (({r_x} : GSet Geid) ∪ sOb)).2
    iexact Hob'
  · ipureintro
    exact Hres

/-! # 3. The primed acquire: `tokTie` at the recorded history, no existential -/

theorem flowEqAmoswapAqLob' (γ γc : GName) (L x : Int)
    (ob_D : AxirisG.obSt GF → GSet Geid) (ob_hm : AxirisG.obSt GF → GMapF Geid (List Hent))
    (mk_ob' : GSet Geid → GMapF Geid (List Hent) → AxirisG.obSt GF)
    (Hmk_ob'_D : ∀ D hm, ob_D (mk_ob' D hm) = D)
    (Hmk_ob'_hm : ∀ D hm, ob_hm (mk_ob' D hm) = hm)
    (Hob_eq' : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInvLock' L x γ γc GD s (ob_D σ) (ob_hm σ))
    (GD : Gdexec) (i : Agent) (k : Nat) (w_rel : Geid) (Hh H_L : List Hent)
    (Hcons : rvwmoCatConsistent GD)
    (Hpol : w_rel ∈ Axpol.sPol GD (i, k))
    (Hunclaimed : ∀ σ : AxirisG.obSt GF, w_rel ∉ ob_D σ)
    (Hhm : ∀ σ : AxirisG.obSt GF, get? (ob_hm σ) w_rel = some Hh)
    (Hwb0 : gwritesByte GD.gdG w_rel L b0)
    (Hwb1 : gwritesByte GD.gdG (i, k) L b1)
    (Hsingle : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' → a' = L)
    (Hgob : gobCat GD w_rel (i, k))
    (Hval : graphData GD (i, k) = some [b1])
    (Hne : Hh ≠ []) :
    histAuth (GF := GF) γ L 1 H_L ⊢
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) ∅
        iprop((⌜gwritesByte GD.gdG w_rel L b0⌝ ∗ tokTie GD γ x Hh {[(i, k) := (1 : Qp)]}) ∗
          ⌜graphData GD (i, k) = some [b1]⌝) := by
  unfold flowEqDyn
  iintro HaL %σ %sOb %Hsub %Hnin Hob -
  ihave Hob := (Hob_eq' GD σ sOb).1 $$ Hob
  have hin : w_rel ∈ sOb := Hsub _ Hpol
  imod protInvLockRmwStep' L x γ γc GD sOb (ob_D σ) (ob_hm σ) w_rel (i, k) Hh H_L Hcons hin
      Hnin (Hunclaimed σ) (Hhm σ) Hwb0 Hwb1 Hsingle Hgob Hne $$ [$Hob $HaL]
    with ⟨Hinv', %Hpure, Htie⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists mk_ob' (({w_rel} : GSet Geid) ∪ ob_D σ) (ob_hm σ)
  isplitl [Hinv']
  · iapply (Hob_eq' GD (mk_ob' (({w_rel} : GSet Geid) ∪ ob_D σ) (ob_hm σ))
      (({(i, k)} : GSet Geid) ∪ sOb)).2
    rw [Hmk_ob'_D, Hmk_ob'_hm]
    iexact Hinv'
  · isplitl [Htie]
    · isplitl []
      · ipureintro
        exact Hpure
      · iexact Htie
    · ipureintro
      exact Hval

/-- THE FULL WP RULE, primed: the deposited slot's `tokTie` has NO `∃ H`. -/
theorem wpAmoswapAqLob' (γ γc : GName) (L x : Int)
    (ob_D : AxirisG.obSt GF → GSet Geid) (ob_hm : AxirisG.obSt GF → GMapF Geid (List Hent))
    (mk_ob' : GSet Geid → GMapF Geid (List Hent) → AxirisG.obSt GF)
    (Hmk_ob'_D : ∀ D hm, ob_D (mk_ob' D hm) = D)
    (Hmk_ob'_hm : ∀ D hm, ob_hm (mk_ob' D hm) = hm)
    (Hob_eq' : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInvLock' L x γ γc GD s (ob_D σ) (ob_hm σ))
    (GD : Gdexec) (i : Agent) (k : Nat) (ls' : AxirisG.logTsT GF) (w_rel : Geid)
    (Hh H_L : List Hent) (Ψ : Unit → IProp GF)
    (Hcons : rvwmoCatConsistent GD)
    (Hpol : w_rel ∈ Axpol.sPol GD (i, k))
    (Hunclaimed : ∀ σ : AxirisG.obSt GF, w_rel ∉ ob_D σ)
    (Hhm : ∀ σ : AxirisG.obSt GF, get? (ob_hm σ) w_rel = some Hh)
    (Hwb0 : gwritesByte GD.gdG w_rel L b0)
    (Hwb1 : gwritesByte GD.gdG (i, k) L b1)
    (Hsingle : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' → a' = L)
    (Hgob : gobCat GD w_rel (i, k))
    (Hval : graphData GD (i, k) = some [b1])
    (Hne : Hh ≠ [])
    (Hnalloc : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (insert na (i, k)
        iprop(⌜gwritesByte GD.gdG w_rel L b0⌝ ∗ tokTie GD γ x Hh {[(i, k) := (1 : Qp)]}))) :
    ⊢ histAuth γ L 1 H_L -∗ AxirisG.localInterp GD i (k + 1) ls' -∗ Ψ () -∗
      wpEvStep GD i k (fun _ : Unit => True) (fun _ : Unit => graphData GD (i, k) = some [b1])
        (fun _ => k + 1) Ψ := by
  iintro HaL Hloc HΨ
  ihave Hfeq := flowEqAmoswapAqLob' γ γc L x ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
    GD i k w_rel Hh H_L Hcons Hpol Hunclaimed Hhm Hwb0 Hwb1 Hsingle Hgob Hval Hne $$ HaL
  unfold wpEvStep
  iintro %na Hpg
  ihave Hn := Hnalloc
  imod Hn $$ %na Hpg with Hna'
  imodintro
  inext
  imodintro
  iexists (), iprop(⌜gwritesByte GD.gdG w_rel L b0⌝ ∗
    tokTie GD γ x Hh {[(i, k) := (1 : Qp)]}), ∅, ∅, ls'
  isplitr
  · ipureintro
    trivial
  isplitr
  · unfold naSplittingWf
    isplitl []
    · ipureintro
      rw [domEmpty]
      exact LawfulSet.empty_subset
    · iapply (BigSepM2.bigSepM2_empty _).2
      itrivial
  iframe Hfeq
  rw [AxLockWp2.unionSingletonEmpty]
  iframe Hna' Hloc HΨ

end lockWp2

end Weak
