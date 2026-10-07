/-
Weak: **THE LOCK CLIENT'S MUTEX SLOT** (AxSL tier; LB/AxSL lock slice, G1 commission, design
§7.L): `ΦLock''`/`AxLockMutex.protInvLock''` (`AxProtLock.ΦLock'`/`protInvLock'` extended
ADDITIVELY with the pure holder fact), its two extended step lemmas, the per-write extraction
lemma, and `lockClientVerified`.

Rocq: `iris/AxLockMutex.v` @ xxvzwolszwmp.

## The Rocq header, in substance

(1) `lockClientVerified GD L x` states, EXISTENTIALLY over the client's own `ea`/`na`
annotation: the two `Axpol`-closure side conditions `adequacyOrdL` needs (`HsPolSub`/
`HlobpSub`, discharging `axpolWfL GD gxGmo` via `axpolWfLOfPredClosed` + `LPredClosedGmo`),
the ordinary `ordEaTodoL` domain side conditions (`HdomEq`/`Hdom`/`HeaLob`), and, for every
`γ`/`γc`, the WAND CHAIN with the initial resources as ANTECEDENTS concluding `ordEaTodoL` AT
THE FIXED instance `axLockMutexG` (`obStInterp := AxLockMutex.protInvLock''`).

(2) `ΦLock''`'s left disjunct is `tokTie … ∗ ⌜glblIs Acq lbAq⌝ ∗ ⌜gpo Acq e⌝`, `Acq` a new
explicit argument threaded through a SECOND map `am : GMapF Geid Geid`, release-keyed as `hm`.
The release step takes `Acq`'s two pure facts as ordinary hypotheses and records `Acq` at
`w_rel` in `am`; the rmw step's deposit at the fresh acquire carries `⌜glblIs acq lbAq⌝`
reflexively (`hm`/`am` unchanged across it).

(3) The per-write extraction: `lockMutexExcludesRacingWrite` (while the token rests unclaimed
at `w_rel`, no other writer can present `histAuth γ x 1` — `ownedWriteExcluded`), and
`lockMutexDiscOfRmw` chains `protInvLockRmwStep''`'s returned `⌜glblIs acq lbAq⌝` directly
into `AxLockN.xwIsCsWrite` for a named write `w` (`lockMutexDiscWrite`) — the smell test:
drop that conjunct and the corollary no longer type-checks.

REMAINDER (stated, not built, as in Rocq): the fully universal "every `x`-write is a CS
write" claim (`lock_mutex_disc`) needs an inductive invariant over the client's in-flight
fraction (invisible to `obStInterp`); `lock_mutex_value` is correspondingly not built.

**Ghost state.** No allocation here: `lockMutexVerifiedWp` takes the two empty `histAuth`s
(name `γ`, `AxlogG GF Hent`) and `claimedAuth γc ∅` (`AxLockG GF`) as wand antecedents; the
caller allocates them (e.g. `AxLockAdeq2.lockInitialAlloc`).

**Fetches / Q8.** No fetch content (graph labels only; the WP step clause is never used).

## Deviations from Rocq

1. NAMES: camelCase (map below).  Duplicated Rocq names, file-qualified:
   `AxLockMutex.protInvLock''`, `AxLockMutex.protInvLockUnfold''` (also in AxProtLock2).
   Lean-only helpers, file-qualified: `AxLockMutex.ΦLock''Open`/`ΦLock''Left`/`ΦLock''Right`/
   `ΦLock''Vacuous` (intro/elim forms of the pure-antecedent wand, as AxProtLock deviation 1).
2. VOCABULARY as `AxProtLock` deviation 2; `gmap geid geid` ↦ `GMapF Geid Geid`, `default e
   (am !! e)` ↦ `(get? am e).getD e`, `gpo` ↦ `WeakRvwmoGraph.gpo`, `dom` ↦
   `FiniteMap.dom_set`, `list_to_set` ↦ `LawfulSet.ofList`, `s_pol`/`lobp` ↦
   `Axpol.sPol`/`Axpol.lobp`, `sra Σ`/`mea Σ` ↦ `Sra GF`/`Mea GF`.
3. STATEMENT SHAPES as `AxProtLock` deviation 4 (`P -∗ Q ==∗ R` ↦ `P ∗ Q ⊢ |==> R`,
   `P -∗ Q -∗ False` ↦ `P ∗ Q ⊢ False`); the wand chain of `lockMutexVerifiedWp` stays
   `⊢ A -∗ B -∗ C -∗ D`.
4. SECTION VARIABLES `(L x : Z)` are explicit leading arguments; each lemma takes those its
   statement mentions (`lockMutexDiscWrite` takes only `L`; Rocq's `Proof using All` adds `x`).
5. INSTANCE: Rocq's `Local Instance AxLockMutex_G` is the `@[reducible] def axLockMutexG L x γ
   γc`, passed explicitly (`@ordEaTodoL _ .hasNoLC GF Hinv (axLockMutexG L x γ γc) …`); its
   ob-state product is right-nested (`GSet Geid × GMapF Geid (List Hent) × GMapF Geid Geid`,
   Rocq `σ.1.1/σ.1.2/σ.2` ↦ `σ.1/σ.2.1/σ.2.2`); no `ax_text` field (Stage C).  The Rocq
   section's `axpol` is a `[Axpol]` binder.

**Rocq → Lean name map.**  `Φ_lock''` `ΦLock''`, `prot_inv_lock''` `AxLockMutex.protInvLock''`,
`prot_inv_lock_unfold''` `AxLockMutex.protInvLockUnfold''`, `big_sepS_lockpp_insert_ne`
`bigSepSLockppInsertNe`, `prot_inv_lock_release_step''` `protInvLockReleaseStep''`,
`prot_inv_lock_rmw_step''` `protInvLockRmwStep''`, `lock_mutex_excludes_racing_write`
`lockMutexExcludesRacingWrite`, `lock_mutex_disc_write` `lockMutexDiscWrite`,
`lock_mutex_disc_of_rmw` `lockMutexDiscOfRmw`, `AxLockMutex_G` `axLockMutexG`,
`lock_mutex_verified_wp` `lockMutexVerifiedWp`, `lock_client_verified` `lockClientVerified`.

**Dropped:** nothing.
-/
import Weak.AxProtLock
import Weak.AxLockRace
import Weak.AxLockN
import Weak.AxAdequacyL
import MachCSL.StdppMap
import MachCSL.StdppSet

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. `ΦLock''` / `protInvLock''` — `ΦLock'` plus the pure holder fact -/

section LockMutexProto

variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF] (L x : Int)

def ΦLock'' (γ γc : GName) (GD : Gdexec) (e : Geid) (H : List Hent) (Acq : Geid) :
    IProp GF :=
  iprop(⌜gwritesByte GD.gdG e L b0⌝ -∗
    ((tokTie GD γ x H {[e := (1 : Qp)]} ∗
        ⌜glblIs GD.gdG Acq lbAq⌝ ∗ ⌜WeakRvwmoGraph.gpo GD.gdG Acq e⌝)
      ∨ AxProtLock.claimed γc e))

def AxLockMutex.protInvLock'' (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (am : GMapF Geid Geid) : IProp GF :=
  iprop(claimedAuth γc D ∗
    [∗set] e ∈ s, (ΦpOwn γ GD e ∗
      ΦLock'' L x γ γc GD e ((get? hm e).getD []) ((get? am e).getD e)))

theorem AxLockMutex.protInvLockUnfold'' (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (am : GMapF Geid Geid) :
    AxLockMutex.protInvLock'' (GF := GF) L x γ γc GD s D hm am ⊣⊢
      claimedAuth γc D ∗ protInv γ GD s ∗
      [∗set] e ∈ s, ΦLock'' L x γ γc GD e ((get? hm e).getD []) ((get? am e).getD e) := by
  unfold AxLockMutex.protInvLock'' protInv
  exact BI.sep_congr .rfl BigSepS.bigSepS_sep

/-- Bookkeeping: BOTH `hm` and `am` can be updated at the same key OUTSIDE `s`. -/
theorem bigSepSLockppInsertNe (γ γc : GName) (GD : Gdexec) (s : GSet Geid)
    (hm : GMapF Geid (List Hent)) (am : GMapF Geid Geid)
    (w_rel : Geid) (Hh : List Hent) (Acq : Geid) :
    w_rel ∉ s →
    ([∗set] e ∈ s, ΦLock'' (GF := GF) L x γ γc GD e ((get? hm e).getD []) ((get? am e).getD e))
    ⊣⊢
    ([∗set] e ∈ s, ΦLock'' L x γ γc GD e ((get? (insert hm w_rel Hh) e).getD [])
                      ((get? (insert am w_rel Acq) e).getD e)) := by
  intro hnin
  refine BiEntails.of_eq (BigSepS.bigSepS_eq fun {e} he => ?_)
  have hne : w_rel ≠ e := fun h => hnin (h ▸ he)
  rw [lookupInsertNe hne, lookupInsertNe hne]

/-- Lean-only: opening `ΦLock''` at a release write. -/
theorem AxLockMutex.ΦLock''Open (γ γc : GName) (GD : Gdexec) (e : Geid) (H Hh : List Hent)
    (Acq : Geid) :
    H = Hh → gwritesByte GD.gdG e L b0 →
    ΦLock'' (GF := GF) L x γ γc GD e H Acq ⊢
      (tokTie GD γ x Hh {[e := (1 : Qp)]} ∗
          ⌜glblIs GD.gdG Acq lbAq⌝ ∗ ⌜WeakRvwmoGraph.gpo GD.gdG Acq e⌝) ∨
        AxProtLock.claimed γc e := by
  intro hH hwb
  subst hH
  unfold ΦLock''
  iintro Hl
  iapply Hl
  ipureintro
  exact hwb

/-- Lean-only: the live arm of `ΦLock''`. -/
theorem AxLockMutex.ΦLock''Left (γ γc : GName) (GD : Gdexec) (e : Geid) (H : List Hent)
    (Acq : Geid) :
    glblIs GD.gdG Acq lbAq → WeakRvwmoGraph.gpo GD.gdG Acq e →
    tokTie (GF := GF) GD γ x H {[e := (1 : Qp)]} ⊢ ΦLock'' L x γ γc GD e H Acq := by
  intro haq hpo
  unfold ΦLock''
  iintro Ht %_
  ileft
  isplitl [Ht]
  · iexact Ht
  isplitl []
  · ipureintro
    exact haq
  · ipureintro
    exact hpo

/-- Lean-only: the claimed arm of `ΦLock''`. -/
theorem AxLockMutex.ΦLock''Right (γ γc : GName) (GD : Gdexec) (e : Geid) (H : List Hent)
    (Acq : Geid) :
    AxProtLock.claimed (GF := GF) γc e ⊢ ΦLock'' L x γ γc GD e H Acq := by
  unfold ΦLock''
  iintro Hc %_
  iright
  iexact Hc

/-- Lean-only: `ΦLock''` at an event that is not a release write. -/
theorem AxLockMutex.ΦLock''Vacuous (γ γc : GName) (GD : Gdexec) (e : Geid) (H : List Hent)
    (Acq : Geid) :
    ¬ gwritesByte GD.gdG e L b0 → ⊢ ΦLock'' (GF := GF) L x γ γc GD e H Acq := by
  intro hn
  unfold ΦLock''
  iintro %hb
  exact (hn hb).elim

/-- THE RELEASE STEP, extended: `protInvLockReleaseStep'`'s premises plus `Acq`'s two pure
facts, recorded at `w_rel` in `am`. -/
theorem protInvLockReleaseStep'' (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (am : GMapF Geid Geid)
    (w_rel e_last Acq : Geid) (Hh H_L : List Hent) :
    rvwmoCatConsistent GD →
    w_rel ∉ s →
    gwritesByte GD.gdG w_rel L b0 →
    (∀ a' v', gwritesByte GD.gdG w_rel a' v' → a' = L) →
    gobCat GD e_last w_rel →
    glblIs GD.gdG Acq lbAq → WeakRvwmoGraph.gpo GD.gdG Acq w_rel →
    AxLockMutex.protInvLock'' (GF := GF) L x γ γc GD s D hm am ∗ histAuth γ L 1 H_L ∗
      tokTie GD γ x Hh {[e_last := (1 : Qp)]} ⊢
    |==> AxLockMutex.protInvLock'' L x γ γc GD (({w_rel} : GSet Geid) ∪ s) D
      (insert hm w_rel Hh) (insert am w_rel Acq) := by
  intro hcons hnin hwb hsingle hgob haq hpo
  iintro ⟨Hinv, HaL, Htie⟩
  icases (AxLockMutex.protInvLockUnfold'' L x γ γc GD s D hm am).1 $$ Hinv
    with ⟨Hc, Hpo, Hlocks⟩
  imod protInvWriteStep γ GD s w_rel L b0 H_L hnin hwb hsingle $$ [$Hpo $HaL] with ⟨Hpo', -⟩
  ihave Htie' := tokRetieOb GD γ x Hh e_last w_rel hcons hgob $$ Htie
  imodintro
  iapply (AxLockMutex.protInvLockUnfold'' L x γ γc GD (({w_rel} : GSet Geid) ∪ s) D
    (insert hm w_rel Hh) (insert am w_rel Acq)).2
  isplitl [Hc]
  · iexact Hc
  isplitl [Hpo']
  · iexact Hpo'
  iapply (AxProtLock.bigSepSUnionSingleton
    (Φ := fun e => ΦLock'' L x γ γc GD e ((get? (insert hm w_rel Hh) e).getD [])
      ((get? (insert am w_rel Acq) e).getD e)) hnin).2
  isplitl [Htie']
  · rw [lookupInsert, lookupInsert, Option.getD_some, Option.getD_some]
    iapply AxLockMutex.ΦLock''Left L x γ γc GD w_rel Hh Acq haq hpo
    iexact Htie'
  · iapply (bigSepSLockppInsertNe L x γ γc GD s hm am w_rel Hh Acq hnin).1
    iexact Hlocks

/-- THE RMW STEP, extended: the deposit at the fresh acquire carries `⌜glblIs acq lbAq⌝`
(the acquire is its own witness); `hm`/`am` unchanged. -/
theorem protInvLockRmwStep'' (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (am : GMapF Geid Geid)
    (w_rel acq : Geid) (Hh H_L : List Hent) :
    rvwmoCatConsistent GD →
    w_rel ∈ s → acq ∉ s → w_rel ∉ D →
    get? hm w_rel = some Hh →
    gwritesByte GD.gdG w_rel L b0 →
    gwritesByte GD.gdG acq L b1 →
    (∀ a' v', gwritesByte GD.gdG acq a' v' → a' = L) →
    gobCat GD w_rel acq →
    glblIs GD.gdG acq lbAq →
    AxLockMutex.protInvLock'' (GF := GF) L x γ γc GD s D hm am ∗ histAuth γ L 1 H_L ⊢
    |==> (AxLockMutex.protInvLock'' L x γ γc GD (({acq} : GSet Geid) ∪ s)
        (({w_rel} : GSet Geid) ∪ D) hm am ∗
      ⌜gwritesByte GD.gdG w_rel L b0⌝ ∗
      tokTie GD γ x Hh {[acq := (1 : Qp)]} ∗
      ⌜glblIs GD.gdG acq lbAq⌝) := by
  intro hcons hin hnacq hninD hhm hwb0 hwb1 hsingle hgob haq
  have hHh : (get? hm w_rel).getD [] = Hh := by rw [hhm]; rfl
  iintro ⟨Hinv, HaL⟩
  icases (AxLockMutex.protInvLockUnfold'' L x γ γc GD s D hm am).1 $$ Hinv
    with ⟨Hc, Hpo, Hlocks⟩
  icases (BigSepS.bigSepS_delete
    (Φ := fun e => ΦLock'' L x γ γc GD e ((get? hm e).getD []) ((get? am e).getD e)) hin).1
    $$ Hlocks with ⟨Hw, Hrest⟩
  icases AxLockMutex.ΦLock''Open L x γ γc GD w_rel _ Hh _ hHh hwb0 $$ Hw
    with (⟨Htie, -, -⟩ | Hcl)
  · imod protInvWriteStep γ GD s acq L b1 H_L hnacq hwb1 hsingle $$ [$Hpo $HaL]
      with ⟨Hpo', -⟩
    imod claimedAlloc γc D w_rel hninD $$ Hc with ⟨Hc', Hcl⟩
    ihave Htie' := tokRetieOb GD γ x Hh w_rel acq hcons hgob $$ Htie
    imodintro
    isplitl [Hc' Hpo' Hcl Hrest]
    · iapply (AxLockMutex.protInvLockUnfold'' L x γ γc GD (({acq} : GSet Geid) ∪ s)
        (({w_rel} : GSet Geid) ∪ D) hm am).2
      isplitl [Hc']
      · iexact Hc'
      isplitl [Hpo']
      · iexact Hpo'
      iapply (AxProtLock.bigSepSUnionSingleton
        (Φ := fun e => ΦLock'' L x γ γc GD e ((get? hm e).getD []) ((get? am e).getD e))
        hnacq).2
      isplitl []
      · iapply AxLockMutex.ΦLock''Vacuous L x γ γc GD acq _ _
          (fun hbad => b0NeB1 (gwritesByteDet _ _ _ _ _ hbad hwb1))
      · iapply (BigSepS.bigSepS_delete
          (Φ := fun e => ΦLock'' L x γ γc GD e ((get? hm e).getD []) ((get? am e).getD e))
          hin).2
        isplitl [Hcl]
        · iapply AxLockMutex.ΦLock''Right L x γ γc GD w_rel _ _
          iexact Hcl
        · iexact Hrest
    · isplitl []
      · ipureintro
        exact hwb0
      isplitl [Htie']
      · iexact Htie'
      · ipureintro
        exact haq
  · ihave %hinD := claimedDom γc D w_rel $$ [$Hc $Hcl]
    exact (hninD hinD).elim

/-! ## 1b. THE PER-WRITE EXTRACTION LEMMA -/

/-- THE SMELL-TEST STEP: while `x`'s token rests unclaimed at `w_rel`, no other writer can
present `histAuth γ x 1` (`ownedWriteExcluded`). -/
theorem lockMutexExcludesRacingWrite (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (am : GMapF Geid Geid)
    (w_rel : Geid) (Hh Hl_c : List Hent) :
    w_rel ∈ s → w_rel ∉ D → get? hm w_rel = some Hh →
    gwritesByte GD.gdG w_rel L b0 →
    AxLockMutex.protInvLock'' (GF := GF) L x γ γc GD s D hm am ∗ histAuth γ x 1 Hl_c ⊢
      False := by
  intro hin hninD hhm hwb0
  have hHh : (get? hm w_rel).getD [] = Hh := by rw [hhm]; rfl
  iintro ⟨Hinv, Hauth⟩
  icases (AxLockMutex.protInvLockUnfold'' L x γ γc GD s D hm am).1 $$ Hinv
    with ⟨Hc, -, Hlocks⟩
  icases (BigSepS.bigSepS_delete
    (Φ := fun e => ΦLock'' L x γ γc GD e ((get? hm e).getD []) ((get? am e).getD e)) hin).1
    $$ Hlocks with ⟨Hw, -⟩
  icases AxLockMutex.ΦLock''Open L x γ γc GD w_rel _ Hh _ hHh hwb0 $$ Hw
    with (⟨Htie, -, -⟩ | Hcl)
  · iapply ownedWriteExcluded GD γ x Hh w_rel Hl_c
    isplitl [Htie]
    · iexact Htie
    · iexact Hauth
  · ihave %hinD := claimedDom γc D w_rel $$ [$Hc $Hcl]
    exact (hninD hinD).elim

/-- THE ACQUIRE-HALF OF `xwIsCsWrite`, repackaged from ordinary graph hypotheses. -/
theorem lockMutexDiscWrite (GD : Gdexec) (acq rel w : Geid) :
    glblIs GD.gdG acq lbAq →
    lockCs GD.gdG L acq rel →
    WeakRvwmoGraph.gpo GD.gdG acq w →
    gppoCat GD w rel →
    AxLockN.xwIsCsWrite GD L w :=
  fun haq hcs hpo hcov => ⟨acq, rel, hcs, haq, hpo, hcov⟩

/-- THE COMBINED COROLLARY: `protInvLockRmwStep''`'s own extracted `⌜glblIs acq lbAq⌝`
feeds `lockMutexDiscWrite` directly. -/
theorem lockMutexDiscOfRmw (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (am : GMapF Geid Geid)
    (w_rel acq rel w : Geid) (Hh H_L : List Hent) :
    rvwmoCatConsistent GD →
    w_rel ∈ s → acq ∉ s → w_rel ∉ D →
    get? hm w_rel = some Hh →
    gwritesByte GD.gdG w_rel L b0 →
    gwritesByte GD.gdG acq L b1 →
    (∀ a' v', gwritesByte GD.gdG acq a' v' → a' = L) →
    gobCat GD w_rel acq →
    glblIs GD.gdG acq lbAq →
    lockCs GD.gdG L acq rel → WeakRvwmoGraph.gpo GD.gdG acq w → gppoCat GD w rel →
    AxLockMutex.protInvLock'' (GF := GF) L x γ γc GD s D hm am ∗ histAuth γ L 1 H_L ⊢
    |==> (AxLockMutex.protInvLock'' L x γ γc GD (({acq} : GSet Geid) ∪ s)
        (({w_rel} : GSet Geid) ∪ D) hm am ∗
      tokTie GD γ x Hh {[acq := (1 : Qp)]} ∗ ⌜AxLockN.xwIsCsWrite GD L w⌝) := by
  intro hcons hin hnacq hninD hhm hwb0 hwb1 hsingle hgob haq hcs hpo hcov
  iintro ⟨Hinv, HaL⟩
  imod protInvLockRmwStep'' L x γ γc GD s D hm am w_rel acq Hh H_L hcons hin hnacq hninD hhm
      hwb0 hwb1 hsingle hgob haq $$ [$Hinv $HaL] with ⟨Hinv', -, Htie, %haq'⟩
  imodintro
  isplitl [Hinv']
  · iexact Hinv'
  isplitl [Htie]
  · iexact Htie
  · ipureintro
    exact lockMutexDiscWrite L GD acq rel w haq' hcs hpo hcov

end LockMutexProto

/-! # 2. THE FIXED INSTANCE, and `lockClientVerified` -/

section LockMutexWp

variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF]

/-- THE FIXED `AxirisG` RECORD (Rocq `AxLockMutex_G`): `obStInterp := protInvLock''`. -/
@[reducible] def axLockMutexG (L x : Int) (γ γc : GName) : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := GSet Geid × GMapF Geid (List Hent) × GMapF Geid Geid
  obStInterp := fun GD0 σ s => AxLockMutex.protInvLock'' L x γ γc GD0 s σ.1 σ.2.1 σ.2.2
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

variable [Axpol]

/-- THE WAND CHAIN at fixed `γ`/`γc`, client-chosen `ea`/`na`. -/
def lockMutexVerifiedWp (L x : Int) (γ γc : GName) (GD : Gdexec) (ea : Sra GF) (na : Mea GF) :
    Prop :=
  ∀ (Hinv : InvGS_gen .hasNoLC GF),
    ⊢ histAuth γ L 1 ([] : List Hent) -∗ histAuth γ x 1 ([] : List Hent) -∗
      claimedAuth γc (∅ : GSet Geid) -∗
      @ordEaTodoL _ .hasNoLC GF Hinv (axLockMutexG L x γ γc) GD ea na GD.gdG.gxGmo 0

/-- `lockClientVerified GD L x`, per design §7.L: the client chooses `ea`/`na`; the side
conditions are `adequacyOrdL`'s; the verification is the wand chain at the fixed instance, for
every `γ`/`γc`. -/
def lockClientVerified (GD : Gdexec) (L x : Int) : Prop :=
  ∃ (ea : GName → GName → Sra GF) (na : GName → GName → Mea GF),
    (∀ e e', e' ∈ Axpol.sPol GD e → gobCat GD e' e) ∧
    (∀ e e', e' ∈ Axpol.lobp GD e → gobCat GD e' e) ∧
    (∀ γ γc, (FiniteMap.dom_set (ea γ γc) : GSet Geid) = FiniteMap.dom_set (na γ γc)) ∧
    (∀ γ γc, (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid) ⊆ FiniteMap.dom_set (na γ γc)) ∧
    (∀ γ γc, ∀ e0 gm, get? (ea γ γc) e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0) ∧
    (∀ γ γc, lockMutexVerifiedWp L x γ γc GD (ea γ γc) (na γ γc))

end LockMutexWp

end Weak
