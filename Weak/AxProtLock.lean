/-
Weak: **THE LOCK-PROTOCOL SLOT** (AxSL tier), ADDITIVE over `Weak.AxProt`'s `protInv`: an
exclusive per-byte token handed release→acquire through a new `ΦLock` conjunct, plus
`tokRetieOb` (re-tying `AxToken.tokTie` along ANY `gobCat` edge).

Rocq: `iris/AxProtLock.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-lb-axsl.md` §7.R "Protocol instance" / tracker G3.
`AxProt` is untouched; this file only ADDS `protInvLock`/`ΦLock` alongside it, composing with
`protInv` via `bigSepS_sep` (`protInvLockUnfold`).

1. `tokRetieOb`: `tieBase` only needs `gmoLt (writer of last H) e` to transport (`tieLob`), and a
   `gobCat` edge IS a `gmoLt` edge under `rvwmoCatConsistent` (`obCatSubGmo`).  `tok`'s own
   resource (`tokSingleton`) is `histAuth` under a PHANTOM key, so re-tying is: pop via
   `tokSingleton`, retie the pure fact, repush at the new key.  No new ghost state.
   `xTok` (the empty-history arm): a lock holder's token is EITHER `tokTie` OR, when the history
   is still `[]`, the bare full `histAuth`; `xTokRetieOb` re-ties it.
2. THE EXCLUSIVE "CLAIMED" TOKEN needs real ghost state (a pure "`∃ acq, grfAt w acq`" would be
   vacuous once the graph is fixed): an AUTH/disjoint-set ticket over `Geid` (the recipe of
   `AxWp`'s `axannotSetG`, over `GName` there) with an explicit growing domain `D` threaded
   alongside the validated set `s` — hence `protInvLock`'s extra `D` argument.  `claimedDom` is
   the consistency check `protInvLockRmwStep`'s refutation uses; `w_rel ∉ D` (gatomicity's
   corollary) is an ordinary hypothesis there, parallel to `protInvWriteStep`'s `w ∉ s`.
3. THE PURE-ANNOTATION CAVEAT: `protInvLockRmwStep` keeps the pure fact and the `tokTie` as
   SEPARATE conjuncts of its conclusion (only the pure fact may cross a gate; the token travels
   as an ordinary WP resource).
3.3 THE PRIMED, HISTORY-INDEXED VERSION: `protInvLock' … hm` records, at each validated release
   write, the exact history `Hh` its token was re-tied to; the rmw step returns the token at the
   SAME `Hh` (`get? hm w_rel = some Hh` a hypothesis), no existential.

Left undone in Rocq (and so here): `Φ_flag`, a `flowEqDyn` wrapper, a non-vacuity witness.

**Fetches.** Nothing here depends on instruction fetches: the file speaks of `gwritesByte`/
`gobCat`/`gmoLt` over graph labels (`Lbl` has no fetch constructor) and of the history ghost.

## Deviations from Rocq

1. NAMES: camelCase (map below).  Duplicated Rocq name, file-qualified: `AxProtLock.claimed`
   (also in AxSpinProt).  Lean-only helpers, file-qualified: `AxProtLock.bigSepSUnionSingleton`
   (the `{e} ∪ s` form of `bigSepS_insert`), `AxProtLock.ΦLockOpen`/`ΦLockLeft`/`ΦLockRight`/
   `ΦLockVacuous` and `AxProtLock.ΦLock'Open`/`ΦLock'Left`/`ΦLock'Right`/`ΦLock'Vacuous` (the
   introduction/elimination forms of the pure-antecedent wands, used instead of unfolding inside
   proof mode).
2. VOCABULARY (as `AxProt` deviation 2): `{[e]} ∪ s` ↦ `({e} : GSet Geid) ∪ s`; `gmap geid (list
   hent)` ↦ `GMapF Geid (List Hent)`; `hm !! e` ↦ `get? hm e`; `<[w := Hh]> hm` ↦
   `insert hm w Hh`; `default [] o` ↦ `o.getD []`; `H.*1` ↦ `H.map Prod.fst`; `gd_g GD` ↦
   `GD.gdG`; `WeakLitmus.b0/b1` ↦ `b0`/`b1`; `Z` ↦ `Int`.
3. CAMERAS: `claimedUR` (a Rocq notation for `gset_disjUR geid`) ↦ `ClaimedUR :=
   DisjointLeibnizSet (GSet Geid)`; `ax_lockG Σ` ↦ the class `AxLockG GF` (field `axLockInG :
   ElemG GF (constOF (Auth ClaimedUR))`); `ax_lockΣ`/`subG_ax_lockG` have no counterpart
   (iris-lean has no `gFunctors` lists, as `AxWp` deviation 3).
4. STATEMENT SHAPES (as `AxProt` deviation 4): `P -∗ Q` ↦ `P ⊢ Q`; `P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`;
   `P -∗ Q ==∗ R` ↦ `P ∗ Q ⊢ |==> R`; pure premises stay `→`.  The pure-antecedent wands inside
   `ΦLock`/`ΦLock'` stay wands `⌜φ⌝ -∗ P` (they need not be persistent).
5. SECTION VARIABLES: Rocq's `(L x : Z)` are the explicit leading arguments of `ΦLock`,
   `protInvLock`, `ΦLock'`, `protInvLock'` and every §3 lemma (as after Rocq's section).

**Rocq → Lean name map.**  `tok_retie_ob` `tokRetieOb`, `x_tok` `xTok`, `tok_tie_x_tok`
`tokTieXTok`, `x_tok_retie_ob` `xTokRetieOb`, `claimedUR` `ClaimedUR`, `ax_lockG`/`AxLockG`
`AxLockG` (`ax_lock_inG` `axLockInG`), `ax_lockΣ`/`subG_ax_lockG` (none), `claimed_auth`
`claimedAuth`, `claimed` `AxProtLock.claimed`, `claimed_timeless` `claimed_timeless`,
`claimed_alloc` `claimedAlloc`, `claimed_dom` `claimedDom`, `Φ_lock` `ΦLock`, `prot_inv_lock`
`protInvLock`, `prot_inv_lock_unfold` `protInvLockUnfold`, `prot_inv_lock_release_step`
`protInvLockReleaseStep`, `prot_inv_lock_rmw_step` `protInvLockRmwStep`, `Φ_lock'` `ΦLock'`,
`prot_inv_lock'` `protInvLock'`, `prot_inv_lock_unfold'` `protInvLockUnfold'`,
`big_sepS_lock_insert_ne` `bigSepSLockInsertNe`, `prot_inv_lock_release_step'`
`protInvLockReleaseStep'`, `prot_inv_lock_rmw_step'` `protInvLockRmwStep'`.

**Not ported:** the §4 `Print Assumptions` audit (the lint's axiom check covers it).
-/
import Weak.AxProt
import Weak.AxToken
import Weak.AxGraphCat
import Weak.WeakLitmus
import MachCSL.StdppMap
import MachCSL.StdppSet
import Iris.Algebra.LeibnizSet
import Iris.Algebra.Auth
import Iris.ProofMode

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. `tokRetieOb` — re-tying `tokTie` along any `gobCat` edge -/

section retie

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem tokRetieOb (GD : Gdexec) (γ : GName) (a : Int) (H : List Hent) (w_x acq : Geid) :
    rvwmoCatConsistent GD →
    gobCat GD w_x acq →
    tokTie (GF := GF) GD γ a H {[w_x := (1 : Qp)]} ⊢ tokTie GD γ a H {[acq := (1 : Qp)]} := by
  intro hcons hgob
  unfold tokTie
  iintro ⟨T, %htie⟩
  have htiew : tieBase GD.gdG (H.map Prod.fst) w_x :=
    htie w_x (by rw [domSingleton, elemOfSingleton])
  have htieacq : tieBase GD.gdG (H.map Prod.fst) acq :=
    tieLob GD.gdG _ w_x acq htiew (obCatSubGmo GD w_x acq hcons hgob)
  isplitl [T]
  · iapply (tokSingleton γ a H acq 1).2
    iapply (tokSingleton γ a H w_x 1).1
    iexact T
  · ipureintro
    intro e he
    rw [domSingleton, elemOfSingleton] at he
    subst he
    exact htieacq

/-- THE EMPTY-HISTORY ARM: the ordinary `tokTie`, or (history still `[]`) the bare full
`histAuth`. -/
def xTok (GD : Gdexec) (γ : GName) (a : Int) (H : List Hent) (e : Geid) : IProp GF :=
  iprop(tokTie GD γ a H {[e := (1 : Qp)]} ∨ (⌜H = []⌝ ∗ histAuth γ a 1 H))

theorem tokTieXTok (GD : Gdexec) (γ : GName) (a : Int) (H : List Hent) (e : Geid) :
    tokTie (GF := GF) GD γ a H {[e := (1 : Qp)]} ⊢ xTok GD γ a H e := by
  unfold xTok
  iintro H
  ileft
  iexact H

/-- `xTok`'s re-tying along a `gobCat` edge (the raw arm passes through unchanged). -/
theorem xTokRetieOb (GD : Gdexec) (γ : GName) (a : Int) (H : List Hent) (w_x acq : Geid) :
    rvwmoCatConsistent GD →
    gobCat GD w_x acq →
    xTok (GF := GF) GD γ a H w_x ⊢ xTok GD γ a H acq := by
  intro hcons hgob
  unfold xTok
  iintro (Htie | ⟨%Heq, Ha⟩)
  · ileft
    iapply tokRetieOb GD γ a H w_x acq hcons hgob
    iexact Htie
  · iright
    isplitl []
    · ipureintro
      exact Heq
    · iexact Ha

end retie

/-! # 2. THE "CLAIMED" EXCLUSIVE TOKEN — a disjoint-set ticket over `Geid` -/

/-- Rocq `claimedUR := gset_disjUR geid`. -/
abbrev ClaimedUR := DisjointLeibnizSet (GSet Geid)

class AxLockG (GF : BundledGFunctors) where
  axLockInG : ElemG GF (constOF (Auth ClaimedUR))

attribute [reducible, instance] AxLockG.axLockInG

section claimed

variable {GF : BundledGFunctors} [AxLockG GF]

/-- `D`: the release writes whose token has already been handed to their acquiring RMW. -/
def claimedAuth (γc : GName) (D : GSet Geid) : IProp GF :=
  iOwn (E := AxLockG.axLockInG) γc (● (DisjointLeibnizSet.valid D))

def AxProtLock.claimed (γc : GName) (w : Geid) : IProp GF :=
  iOwn (E := AxLockG.axLockInG) γc (◯ (DisjointLeibnizSet.valid ({w} : GSet Geid)))

instance claimed_timeless (γc : GName) (w : Geid) :
    Timeless (AxProtLock.claimed (GF := GF) γc w) := by
  unfold AxProtLock.claimed; infer_instance

theorem claimedAlloc (γc : GName) (D : GSet Geid) (w : Geid) :
    w ∉ D →
    claimedAuth (GF := GF) γc D ⊢
      |==> (claimedAuth γc (({w} : GSet Geid) ∪ D) ∗ AxProtLock.claimed γc w) := by
  intro hnin
  have hdisj : ({w} : GSet Geid) ## D := by
    rw [elemOfDisjoint]
    intro y hy hy'
    rw [elemOfSingleton.1 hy] at hy'
    exact hnin hy'
  have hupd : (● (DisjointLeibnizSet.valid D) : Auth ClaimedUR) ~~>
      (● (DisjointLeibnizSet.valid (({w} : GSet Geid) ∪ D))) •
        ◯ (DisjointLeibnizSet.valid ({w} : GSet Geid)) :=
    Auth.auth_update_alloc (DisjointLeibnizSet.localUpdate_alloc_empty_of_disj _ _ hdisj)
  unfold claimedAuth AxProtLock.claimed
  iintro Ha
  imod iOwn_update hupd $$ Ha with Ha
  icases iOwn_op.1 $$ Ha with ⟨Ha, Hc⟩
  imodintro
  isplitl [Ha]
  · iexact Ha
  · iexact Hc

/-- The refutation lemma: the authority and a fragment force membership. -/
theorem claimedDom (γc : GName) (D : GSet Geid) (w : Geid) :
    claimedAuth (GF := GF) γc D ∗ AxProtLock.claimed γc w ⊢ ⌜w ∈ D⌝ := by
  unfold claimedAuth AxProtLock.claimed
  iintro ⟨Ha, Hc⟩
  icases iOwn_cmraValid_op $$ [$Ha $Hc] with %hv
  ipureintro
  have h := (Auth.auth_both_valid_discrete.mp hv).1
  have h2 := DisjointLeibnizSet.included_iff_subset.mp h
  exact h2 w (elemOfSingleton.2 rfl)

end claimed

/-! # 3. `ΦLock` / `protInvLock` — the lock slot, additive to `protInv`

`L` is the lock word's address, `x` the protected variable's (explicit leading arguments). -/

section lock

variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF] (L x : Int)

/-- Lean-only: the `{e} ∪ s` form of `bigSepS_insert`. -/
theorem AxProtLock.bigSepSUnionSingleton {Φ : Geid → IProp GF} {s : GSet Geid} {e : Geid}
    (h : e ∉ s) : ([∗set] y ∈ ({e} : GSet Geid) ∪ s, Φ y) ⊣⊢ Φ e ∗ [∗set] y ∈ s, Φ y := by
  have hdisj : ({e} : GSet Geid) ## s := by
    rw [elemOfDisjoint]
    intro y hy hy'
    rw [elemOfSingleton.1 hy] at hy'
    exact h hy'
  exact (BigSepS.bigSepS_union hdisj).trans (BI.sep_congr BigSepS.bigSepS_singleton .rfl)

/-- The lock's per-event protocol content: at a write of `0` to `L` (a release), EITHER the
byte-`x` token is still live (tied at this event) OR it has already been claimed. -/
def ΦLock (γ γc : GName) (GD : Gdexec) (e : Geid) : IProp GF :=
  iprop(⌜gwritesByte GD.gdG e L b0⌝ -∗
    ((∃ H, tokTie GD γ x H {[e := (1 : Qp)]}) ∨ AxProtLock.claimed γc e))

def protInvLock (γ γc : GName) (GD : Gdexec) (s D : GSet Geid) : IProp GF :=
  iprop(claimedAuth γc D ∗ [∗set] e ∈ s, (ΦpOwn γ GD e ∗ ΦLock L x γ γc GD e))

theorem protInvLockUnfold (γ γc : GName) (GD : Gdexec) (s D : GSet Geid) :
    protInvLock (GF := GF) L x γ γc GD s D ⊣⊢
      claimedAuth γc D ∗ protInv γ GD s ∗ [∗set] e ∈ s, ΦLock L x γ γc GD e := by
  unfold protInvLock protInv
  exact BI.sep_congr .rfl BigSepS.bigSepS_sep

/-- Lean-only: opening `ΦLock` at a release write. -/
theorem AxProtLock.ΦLockOpen (γ γc : GName) (GD : Gdexec) (e : Geid) :
    gwritesByte GD.gdG e L b0 →
    ΦLock (GF := GF) L x γ γc GD e ⊢
      (∃ H, tokTie GD γ x H {[e := (1 : Qp)]}) ∨ AxProtLock.claimed γc e := by
  intro hwb
  unfold ΦLock
  iintro H
  iapply H
  ipureintro
  exact hwb

/-- Lean-only: the live arm of `ΦLock`. -/
theorem AxProtLock.ΦLockLeft (γ γc : GName) (GD : Gdexec) (e : Geid) (H : List Hent) :
    tokTie (GF := GF) GD γ x H {[e := (1 : Qp)]} ⊢ ΦLock L x γ γc GD e := by
  unfold ΦLock
  iintro Ht %_
  ileft
  iexists H
  iexact Ht

/-- Lean-only: the claimed arm of `ΦLock`. -/
theorem AxProtLock.ΦLockRight (γ γc : GName) (GD : Gdexec) (e : Geid) :
    AxProtLock.claimed (GF := GF) γc e ⊢ ΦLock L x γ γc GD e := by
  unfold ΦLock
  iintro Hc %_
  iright
  iexact Hc

/-- Lean-only: `ΦLock` at an event that is not a release write. -/
theorem AxProtLock.ΦLockVacuous (γ γc : GName) (GD : Gdexec) (e : Geid) :
    ¬ gwritesByte GD.gdG e L b0 → ⊢ ΦLock (GF := GF) L x γ γc GD e := by
  intro hn
  unfold ΦLock
  iintro %hb
  exact (hn hb).elim

/-! ## 3.1 THE RELEASE STEP -/

theorem protInvLockReleaseStep (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (w_rel e_last : Geid) (Hh H_L : List Hent) :
    rvwmoCatConsistent GD →
    w_rel ∉ s →
    gwritesByte GD.gdG w_rel L b0 →
    (∀ a' v', gwritesByte GD.gdG w_rel a' v' → a' = L) →
    gobCat GD e_last w_rel →
    protInvLock (GF := GF) L x γ γc GD s D ∗ histAuth γ L 1 H_L ∗
      tokTie GD γ x Hh {[e_last := (1 : Qp)]} ⊢
    |==> protInvLock L x γ γc GD (({w_rel} : GSet Geid) ∪ s) D := by
  intro hcons hnin hwb hsingle hgob
  iintro ⟨Hinv, HaL, Htie⟩
  icases (protInvLockUnfold L x γ γc GD s D).1 $$ Hinv with ⟨Hc, Hpo, Hlocks⟩
  imod protInvWriteStep γ GD s w_rel L b0 H_L hnin hwb hsingle $$ [$Hpo $HaL] with ⟨Hpo', -⟩
  ihave Htie' := tokRetieOb GD γ x Hh e_last w_rel hcons hgob $$ Htie
  imodintro
  iapply (protInvLockUnfold L x γ γc GD (({w_rel} : GSet Geid) ∪ s) D).2
  isplitl [Hc]
  · iexact Hc
  isplitl [Hpo']
  · iexact Hpo'
  iapply (AxProtLock.bigSepSUnionSingleton (Φ := ΦLock L x γ γc GD) hnin).2
  isplitl [Htie']
  · iapply AxProtLock.ΦLockLeft L x γ γc GD w_rel Hh
    iexact Htie'
  · iexact Hlocks

/-! ## 3.2 THE ACQUIRE RMW STEP (pure fact and token as SEPARATE conjuncts) -/

theorem protInvLockRmwStep (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (w_rel acq : Geid) (H_L : List Hent) :
    rvwmoCatConsistent GD →
    w_rel ∈ s → acq ∉ s → w_rel ∉ D →
    gwritesByte GD.gdG w_rel L b0 →
    gwritesByte GD.gdG acq L b1 →
    (∀ a' v', gwritesByte GD.gdG acq a' v' → a' = L) →
    gobCat GD w_rel acq →
    protInvLock (GF := GF) L x γ γc GD s D ∗ histAuth γ L 1 H_L ⊢
    |==> (protInvLock L x γ γc GD (({acq} : GSet Geid) ∪ s) (({w_rel} : GSet Geid) ∪ D) ∗
      ⌜gwritesByte GD.gdG w_rel L b0⌝ ∗
      (∃ H, tokTie GD γ x H {[acq := (1 : Qp)]})) := by
  intro hcons hin hnacq hninD hwb0 hwb1 hsingle hgob
  iintro ⟨Hinv, HaL⟩
  icases (protInvLockUnfold L x γ γc GD s D).1 $$ Hinv with ⟨Hc, Hpo, Hlocks⟩
  icases (BigSepS.bigSepS_delete (Φ := ΦLock L x γ γc GD) hin).1 $$ Hlocks with ⟨Hw, Hrest⟩
  icases AxProtLock.ΦLockOpen L x γ γc GD w_rel hwb0 $$ Hw with (⟨%Hh, Htie⟩ | Hcl)
  · imod protInvWriteStep γ GD s acq L b1 H_L hnacq hwb1 hsingle $$ [$Hpo $HaL]
      with ⟨Hpo', -⟩
    imod claimedAlloc γc D w_rel hninD $$ Hc with ⟨Hc', Hcl⟩
    ihave Htie' := tokRetieOb GD γ x Hh w_rel acq hcons hgob $$ Htie
    imodintro
    isplitl [Hc' Hpo' Hcl Hrest]
    · iapply (protInvLockUnfold L x γ γc GD (({acq} : GSet Geid) ∪ s)
        (({w_rel} : GSet Geid) ∪ D)).2
      isplitl [Hc']
      · iexact Hc'
      isplitl [Hpo']
      · iexact Hpo'
      iapply (AxProtLock.bigSepSUnionSingleton (Φ := ΦLock L x γ γc GD) hnacq).2
      isplitl []
      · iapply AxProtLock.ΦLockVacuous L x γ γc GD acq
          (fun hbad => b0NeB1 (gwritesByteDet _ _ _ _ _ hbad hwb1))
      · iapply (BigSepS.bigSepS_delete (Φ := ΦLock L x γ γc GD) hin).2
        isplitl [Hcl]
        · iapply AxProtLock.ΦLockRight L x γ γc GD w_rel
          iexact Hcl
        · iexact Hrest
    · isplitl []
      · ipureintro
        exact hwb0
      · iexists Hh
        iexact Htie'
  · ihave %hinD := claimedDom γc D w_rel $$ [$Hc $Hcl]
    exact (hninD hinD).elim

/-! ## 3.3 THE PRIMED, HISTORY-INDEXED VERSION -/

def ΦLock' (γ γc : GName) (GD : Gdexec) (e : Geid) (H : List Hent) : IProp GF :=
  iprop(⌜gwritesByte GD.gdG e L b0⌝ -∗ (xTok GD γ x H e ∨ AxProtLock.claimed γc e))

def protInvLock' (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) : IProp GF :=
  iprop(claimedAuth γc D ∗
    [∗set] e ∈ s, (ΦpOwn γ GD e ∗ ΦLock' L x γ γc GD e ((get? hm e).getD [])))

theorem protInvLockUnfold' (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) :
    protInvLock' (GF := GF) L x γ γc GD s D hm ⊣⊢
      claimedAuth γc D ∗ protInv γ GD s ∗
      [∗set] e ∈ s, ΦLock' L x γ γc GD e ((get? hm e).getD []) := by
  unfold protInvLock' protInv
  exact BI.sep_congr .rfl BigSepS.bigSepS_sep

/-- Bookkeeping: `hm` can be updated at any key OUTSIDE `s`. -/
theorem bigSepSLockInsertNe (γ γc : GName) (GD : Gdexec) (s : GSet Geid)
    (hm : GMapF Geid (List Hent)) (w_rel : Geid) (Hh : List Hent) :
    w_rel ∉ s →
    ([∗set] e ∈ s, ΦLock' (GF := GF) L x γ γc GD e ((get? hm e).getD [])) ⊣⊢
    ([∗set] e ∈ s, ΦLock' L x γ γc GD e ((get? (insert hm w_rel Hh) e).getD [])) := by
  intro hnin
  refine BiEntails.of_eq (BigSepS.bigSepS_eq fun {e} he => ?_)
  have hne : w_rel ≠ e := fun h => hnin (h ▸ he)
  rw [lookupInsertNe hne]

/-- Lean-only: opening `ΦLock'` at a release write (with `xTok` unfolded). -/
theorem AxProtLock.ΦLock'Open (γ γc : GName) (GD : Gdexec) (e : Geid) (H Hh : List Hent) :
    H = Hh → gwritesByte GD.gdG e L b0 →
    ΦLock' (GF := GF) L x γ γc GD e H ⊢
      (tokTie GD γ x Hh {[e := (1 : Qp)]} ∨ (⌜Hh = []⌝ ∗ histAuth γ x 1 Hh)) ∨
        AxProtLock.claimed γc e := by
  intro hH hwb
  subst hH
  unfold ΦLock' xTok
  iintro Hl
  iapply Hl
  ipureintro
  exact hwb

/-- Lean-only: the live arm of `ΦLock'`. -/
theorem AxProtLock.ΦLock'Left (γ γc : GName) (GD : Gdexec) (e : Geid) (H : List Hent) :
    xTok (GF := GF) GD γ x H e ⊢ ΦLock' L x γ γc GD e H := by
  unfold ΦLock'
  iintro Ht %_
  ileft
  iexact Ht

/-- Lean-only: the claimed arm of `ΦLock'`. -/
theorem AxProtLock.ΦLock'Right (γ γc : GName) (GD : Gdexec) (e : Geid) (H : List Hent) :
    AxProtLock.claimed (GF := GF) γc e ⊢ ΦLock' L x γ γc GD e H := by
  unfold ΦLock'
  iintro Hc %_
  iright
  iexact Hc

/-- Lean-only: `ΦLock'` at an event that is not a release write. -/
theorem AxProtLock.ΦLock'Vacuous (γ γc : GName) (GD : Gdexec) (e : Geid) (H : List Hent) :
    ¬ gwritesByte GD.gdG e L b0 → ⊢ ΦLock' (GF := GF) L x γ γc GD e H := by
  intro hn
  unfold ΦLock'
  iintro %hb
  exact (hn hb).elim

/-- The RELEASE step, primed: additionally records `Hh` in `hm` at `w_rel`. -/
theorem protInvLockReleaseStep' (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (w_rel e_last : Geid) (Hh H_L : List Hent) :
    rvwmoCatConsistent GD →
    w_rel ∉ s →
    gwritesByte GD.gdG w_rel L b0 →
    (∀ a' v', gwritesByte GD.gdG w_rel a' v' → a' = L) →
    gobCat GD e_last w_rel →
    protInvLock' (GF := GF) L x γ γc GD s D hm ∗ histAuth γ L 1 H_L ∗
      tokTie GD γ x Hh {[e_last := (1 : Qp)]} ⊢
    |==> protInvLock' L x γ γc GD (({w_rel} : GSet Geid) ∪ s) D (insert hm w_rel Hh) := by
  intro hcons hnin hwb hsingle hgob
  iintro ⟨Hinv, HaL, Htie⟩
  icases (protInvLockUnfold' L x γ γc GD s D hm).1 $$ Hinv with ⟨Hc, Hpo, Hlocks⟩
  imod protInvWriteStep γ GD s w_rel L b0 H_L hnin hwb hsingle $$ [$Hpo $HaL] with ⟨Hpo', -⟩
  ihave Htie' := tokRetieOb GD γ x Hh e_last w_rel hcons hgob $$ Htie
  imodintro
  iapply (protInvLockUnfold' L x γ γc GD (({w_rel} : GSet Geid) ∪ s) D (insert hm w_rel Hh)).2
  isplitl [Hc]
  · iexact Hc
  isplitl [Hpo']
  · iexact Hpo'
  iapply (AxProtLock.bigSepSUnionSingleton
    (Φ := fun e => ΦLock' L x γ γc GD e ((get? (insert hm w_rel Hh) e).getD [])) hnin).2
  isplitl [Htie']
  · rw [lookupInsert, Option.getD_some]
    iapply AxProtLock.ΦLock'Left L x γ γc GD w_rel Hh
    iapply tokTieXTok
    iexact Htie'
  · iapply (bigSepSLockInsertNe L x γ γc GD s hm w_rel Hh hnin).1
    iexact Hlocks

/-- The ACQUIRE RMW step, primed: the SAME `Hh` the release step recorded comes back out. -/
theorem protInvLockRmwStep' (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (w_rel acq : Geid) (Hh H_L : List Hent) :
    rvwmoCatConsistent GD →
    w_rel ∈ s → acq ∉ s → w_rel ∉ D →
    get? hm w_rel = some Hh →
    gwritesByte GD.gdG w_rel L b0 →
    gwritesByte GD.gdG acq L b1 →
    (∀ a' v', gwritesByte GD.gdG acq a' v' → a' = L) →
    gobCat GD w_rel acq →
    Hh ≠ [] →
    protInvLock' (GF := GF) L x γ γc GD s D hm ∗ histAuth γ L 1 H_L ⊢
    |==> (protInvLock' L x γ γc GD (({acq} : GSet Geid) ∪ s) (({w_rel} : GSet Geid) ∪ D) hm ∗
      ⌜gwritesByte GD.gdG w_rel L b0⌝ ∗
      tokTie GD γ x Hh {[acq := (1 : Qp)]}) := by
  intro hcons hin hnacq hninD hhm hwb0 hwb1 hsingle hgob hne
  have hHh : (get? hm w_rel).getD [] = Hh := by rw [hhm]; rfl
  iintro ⟨Hinv, HaL⟩
  icases (protInvLockUnfold' L x γ γc GD s D hm).1 $$ Hinv with ⟨Hc, Hpo, Hlocks⟩
  icases (BigSepS.bigSepS_delete
    (Φ := fun e => ΦLock' L x γ γc GD e ((get? hm e).getD [])) hin).1 $$ Hlocks
    with ⟨Hw, Hrest⟩
  icases AxProtLock.ΦLock'Open L x γ γc GD w_rel _ Hh hHh hwb0 $$ Hw
    with ((Htie | ⟨%Heq, -⟩) | Hcl)
  · imod protInvWriteStep γ GD s acq L b1 H_L hnacq hwb1 hsingle $$ [$Hpo $HaL]
      with ⟨Hpo', -⟩
    imod claimedAlloc γc D w_rel hninD $$ Hc with ⟨Hc', Hcl⟩
    ihave Htie' := tokRetieOb GD γ x Hh w_rel acq hcons hgob $$ Htie
    imodintro
    isplitl [Hc' Hpo' Hcl Hrest]
    · iapply (protInvLockUnfold' L x γ γc GD (({acq} : GSet Geid) ∪ s)
        (({w_rel} : GSet Geid) ∪ D) hm).2
      isplitl [Hc']
      · iexact Hc'
      isplitl [Hpo']
      · iexact Hpo'
      iapply (AxProtLock.bigSepSUnionSingleton
        (Φ := fun e => ΦLock' L x γ γc GD e ((get? hm e).getD [])) hnacq).2
      isplitl []
      · iapply AxProtLock.ΦLock'Vacuous L x γ γc GD acq _
          (fun hbad => b0NeB1 (gwritesByteDet _ _ _ _ _ hbad hwb1))
      · iapply (BigSepS.bigSepS_delete
          (Φ := fun e => ΦLock' L x γ γc GD e ((get? hm e).getD [])) hin).2
        isplitl [Hcl]
        · iapply AxProtLock.ΦLock'Right L x γ γc GD w_rel _
          iexact Hcl
        · iexact Hrest
    · isplitl []
      · ipureintro
        exact hwb0
      · iexact Htie'
  · exact (hne Heq).elim
  · ihave %hinD := claimedDom γc D w_rel $$ [$Hc $Hcl]
    exact (hninD hinD).elim

end lock

end Weak
