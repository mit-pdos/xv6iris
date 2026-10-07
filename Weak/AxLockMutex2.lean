/-
Weak: **THE LOCK CLIENT'S MUTEX SLOT, FOLLOW-UP** (AxSL tier; G1 commission follow-up,
design §7.L): the token carrying its own critical-section witness (`tokcs`) and its three flow
steps, the GENESIS slot `protInvLockG` (x's initial fraction folded into the fixed instance's
ob-state interpretation behind a boolean flag), the restated wand chain
`lockMutexVerifiedWp''` and `lockClientVerified''`.

Rocq: `iris/AxLockMutex2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

(A) INITIAL RESOURCE. `AxLockMutex.lockMutexVerifiedWp` hands the client a bare
`histAuth γ x 1 []`; the client's closures could route it into any x-write, so the universal
"every x-write is a CS write" claim could never be proved. Fix: x's initial fraction is never
handed out; it lives inside the fixed instance's `obStInterp` as a third, boolean-gated
component (`protInvLockG`, initial flag `false`), and the ONLY way to extract it is
`protInvLockRmwStepGenesis`, which demands a genuine acquire (`glblIs acq lbAq`).

(B) THE TOKEN CARRIES ITS OWN DISCIPLINE. `tokcs` is `tokTie` plus the pure fact "this event
is a genuine acquire, or a genuine CS write" (`AxLockN.xwIsCsWrite`). Three flow steps:
acquire (`protInvLockRmwStepCs`, repackaging `protInvLockRmwStep''`), write inside a CS
(`tokcsStepWrite`: the witness is re-derived fresh via `lockMutexDiscWrite`), release
(`protInvLockReleaseStepCs`, repackaging `protInvLockReleaseStep''`).

(C) `lock_mutex_disc''` — NOT BUILT (as in Rocq). The universal claim needs a strengthened
induction hypothesis threading "wherever (γ, x)'s exclusive fraction is, it carries tokcs's
witness" through `adequacyOrdAuxL`'s own recursion. SEPARATE FINDING (Rocq, unfixed there and
here): `claimedAuth γc ∅` is both a wand antecedent of `lockMutexVerifiedWp''` and a conjunct
of `obStInterp GD σ0 ∅` (via `protInvLock''`) — the same double-spend shape (A) fixes for x;
the fix would fold it into σ0 too and drop it from the antecedents.

**Ghost state.** No allocation here (as AxLockMutex: the caller allocates `γ`, `γc`).

**Fetches / Q8.** No fetch content.

## Deviations from Rocq

1. NAMES: camelCase (map below). No Rocq name of this file is duplicated; no Lean-only helpers.
2. VOCABULARY and STATEMENT SHAPES as `AxLockMutex` deviations 2/3 (`P -∗ Q ==∗ R` ↦
   `P ∗ Q ⊢ |==> R`; `P -∗ Q -∗ R ==∗ S` ↦ `P ∗ Q ∗ R ⊢ |==> S`); `bv 8` ↦ `BitVec 8`; the
   wand chain of `lockMutexVerifiedWp''` stays `⊢ A -∗ B -∗ C`.
3. SECTION VARIABLES `(L x : Int)` are explicit leading arguments of every declaration
   (Rocq `Proof using All`); `tokcs` and the step lemmas take both.
4. INSTANCE: Rocq's `Local Instance AxLockMutex2_G` is the `@[reducible] def axLockMutex2G L x
   γ γc`, passed explicitly; its ob-state product is right-nested
   (`GSet Geid × GMapF Geid (List Hent) × GMapF Geid Geid × Bool`; Rocq
   `σ.1.1.1/σ.1.1.2/σ.1.2/σ.2` ↦ `σ.1/σ.2.1/σ.2.2.1/σ.2.2.2`); no `ax_text` field (Stage C).

**Rocq → Lean name map.** `tokcs` `tokcs`, `prot_inv_lock_rmw_step_cs` `protInvLockRmwStepCs`,
`tokcs_step_write` `tokcsStepWrite`, `prot_inv_lock_release_step_cs`
`protInvLockReleaseStepCs`, `prot_inv_lock_g` `protInvLockG`, `prot_inv_lock_rmw_step_genesis`
`protInvLockRmwStepGenesis`, `AxLockMutex2_G` `axLockMutex2G`, `lock_mutex_verified_wp''`
`lockMutexVerifiedWp''`, `lock_client_verified''` `lockClientVerified''`.

**Dropped:** nothing.
-/
import Weak.AxLockMutex

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. `tokcs` (item B) and the three flow steps -/

section TokCSAndGenesis

variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF] (L x : Int)

/-- The token with its own CS witness: the holder is the acquire itself, or a CS write. -/
def tokcs (γ : GName) (GD : Gdexec) (H : List Hent) (e : Geid) : IProp GF :=
  iprop(tokTie GD γ x H {[e := (1 : Qp)]} ∗
    ⌜glblIs GD.gdG e lbAq ∨ AxLockN.xwIsCsWrite GD L e⌝)

/-- ACQUIRE: slot → token-with-CS-fact. -/
theorem protInvLockRmwStepCs (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
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
      tokcs L x γ GD Hh acq) := by
  intro hcons hin hnacq hninD hhm hwb0 hwb1 hsingle hgob haq
  iintro ⟨Hinv, HaL⟩
  imod protInvLockRmwStep'' L x γ γc GD s D hm am w_rel acq Hh H_L hcons hin hnacq hninD hhm
      hwb0 hwb1 hsingle hgob haq $$ [$Hinv $HaL] with ⟨Hinv', -, Htie, -⟩
  imodintro
  isplitl [Hinv']
  · iexact Hinv'
  unfold tokcs
  isplitl [Htie]
  · iexact Htie
  · ipureintro
    exact Or.inl haq

/-- WRITE INSIDE A CS: token → token, the output witness re-derived fresh. -/
theorem tokcsStepWrite (γ : GName) (GD : Gdexec) (s : GSet Geid) (H : List Hent)
    (e_prev w acq rel : Geid) (v : BitVec 8) :
    w ∉ s →
    gwritesByte GD.gdG w x v →
    (∀ a' v', gwritesByte GD.gdG w a' v' → a' = x) →
    glblIs GD.gdG acq lbAq → lockCs GD.gdG L acq rel →
    WeakRvwmoGraph.gpo GD.gdG acq w → gppoCat GD w rel →
    protInv (GF := GF) γ GD s ∗ tokcs L x γ GD H e_prev ⊢
    |==> (protInv γ GD (({w} : GSet Geid) ∪ s) ∗ tokcs L x γ GD (H ++ [(w, v)]) w) := by
  intro hnin hwb hsingle haq hcs hpo hcov
  iintro ⟨Hp, Htie⟩
  unfold tokcs
  icases Htie with ⟨Ht, -⟩
  ihave Htok := tokTieTok GD γ x H {[e_prev := (1 : Qp)]} $$ Ht
  ihave Hauth := (tokSingleton γ x H e_prev 1).1 $$ Htok
  imod protInvWriteStep γ GD s w x v H hnin hwb hsingle $$ [$Hp $Hauth] with ⟨Hp', Htie'⟩
  imodintro
  isplitl [Hp']
  · iexact Hp'
  isplitl [Htie']
  · iexact Htie'
  · ipureintro
    exact Or.inr (lockMutexDiscWrite L GD acq rel w haq hcs hpo hcov)

/-- RELEASE: token → slot (the token's pure disjunct is discarded). -/
theorem protInvLockReleaseStepCs (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (am : GMapF Geid Geid)
    (w_rel e_last Acq : Geid) (Hh H_L : List Hent) :
    rvwmoCatConsistent GD → w_rel ∉ s →
    gwritesByte GD.gdG w_rel L b0 →
    (∀ a' v', gwritesByte GD.gdG w_rel a' v' → a' = L) →
    gobCat GD e_last w_rel →
    glblIs GD.gdG Acq lbAq → WeakRvwmoGraph.gpo GD.gdG Acq w_rel →
    AxLockMutex.protInvLock'' (GF := GF) L x γ γc GD s D hm am ∗ histAuth γ L 1 H_L ∗
      tokcs L x γ GD Hh e_last ⊢
    |==> AxLockMutex.protInvLock'' L x γ γc GD (({w_rel} : GSet Geid) ∪ s) D
      (insert hm w_rel Hh) (insert am w_rel Acq) := by
  intro hcons hnin hwb hsingle hgob haq hpo
  iintro ⟨Hinv, HaL, Htie⟩
  unfold tokcs
  icases Htie with ⟨Htie, -⟩
  iapply protInvLockReleaseStep'' L x γ γc GD s D hm am w_rel e_last Acq Hh H_L
    hcons hnin hwb hsingle hgob haq hpo
  isplitl [Hinv]
  · iexact Hinv
  isplitl [HaL]
  · iexact HaL
  · iexact Htie

/-! ## 1b. THE GENESIS SLOT (item A) -/

/-- `gcl = false`: x's initial, untied `histAuth` still rests here; `gcl = true`: handed out
(only by `protInvLockRmwStepGenesis`). -/
def protInvLockG (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (am : GMapF Geid Geid) (gcl : Bool) : IProp GF :=
  iprop(AxLockMutex.protInvLock'' L x γ γc GD s D hm am ∗
    (if gcl then iprop(emp) else histAuth γ x 1 ([] : List Hent)))

/-- THE FIRST ACQUIRE: draws x's fraction from the genesis flag. -/
theorem protInvLockRmwStepGenesis (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (am : GMapF Geid Geid) (acq : Geid) (H_L : List Hent) :
    acq ∉ s →
    gwritesByte GD.gdG acq L b1 →
    (∀ a' v', gwritesByte GD.gdG acq a' v' → a' = L) →
    glblIs GD.gdG acq lbAq →
    protInvLockG (GF := GF) L x γ γc GD s D hm am false ∗ histAuth γ L 1 H_L ⊢
    |==> (protInvLockG L x γ γc GD (({acq} : GSet Geid) ∪ s) D hm am true ∗
      histAuth γ x 1 ([] : List Hent)) := by
  intro hnacq hwb hsingle _haq
  unfold protInvLockG
  simp only [Bool.false_eq_true, ↓reduceIte]
  iintro ⟨⟨Hpl, Hx⟩, HaL⟩
  icases (AxLockMutex.protInvLockUnfold'' L x γ γc GD s D hm am).1 $$ Hpl
    with ⟨Hc, Hpo0, Hlocks⟩
  imod protInvWriteStep γ GD s acq L b1 H_L hnacq hwb hsingle $$ [$Hpo0 $HaL] with ⟨Hpo0', -⟩
  imodintro
  isplitl [Hc Hpo0' Hlocks]
  · isplitl [Hc Hpo0' Hlocks]
    · iapply (AxLockMutex.protInvLockUnfold'' L x γ γc GD (({acq} : GSet Geid) ∪ s) D hm am).2
      isplitl [Hc]
      · iexact Hc
      isplitl [Hpo0']
      · iexact Hpo0'
      iapply (AxProtLock.bigSepSUnionSingleton
        (Φ := fun e => ΦLock'' L x γ γc GD e ((get? hm e).getD []) ((get? am e).getD e))
        hnacq).2
      isplitl []
      · iapply AxLockMutex.ΦLock''Vacuous L x γ γc GD acq _ _
          (fun hbad => b0NeB1 (gwritesByteDet _ _ _ _ _ hbad hwb))
      · iexact Hlocks
    · iempintro
  · iexact Hx

end TokCSAndGenesis

/-! # 2. THE FIXED INSTANCE, and `lockClientVerified''` -/

section LockMutexWp2

variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF]

/-- THE FIXED `AxirisG` RECORD (Rocq `AxLockMutex2_G`): `obStInterp := protInvLockG`. -/
@[reducible] def axLockMutex2G (L x : Int) (γ γc : GName) : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := GSet Geid × GMapF Geid (List Hent) × GMapF Geid Geid × Bool
  obStInterp := fun GD0 σ s => protInvLockG L x γ γc GD0 s σ.1 σ.2.1 σ.2.2.1 σ.2.2.2
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

variable [Axpol]

/-- THE WAND CHAIN, (A)'s fix: x's fraction is no longer among the antecedents. -/
def lockMutexVerifiedWp'' (L x : Int) (γ γc : GName) (GD : Gdexec) (ea : Sra GF)
    (na : Mea GF) : Prop :=
  ∀ (Hinv : InvGS_gen .hasNoLC GF),
    ⊢ histAuth γ L 1 ([] : List Hent) -∗ claimedAuth γc (∅ : GSet Geid) -∗
      @ordEaTodoL _ .hasNoLC GF Hinv (axLockMutex2G L x γ γc) GD ea na GD.gdG.gxGmo 0

/-- `lockClientVerified` with only its wand chain restated per (A). -/
def lockClientVerified'' (GD : Gdexec) (L x : Int) : Prop :=
  ∃ (ea : GName → GName → Sra GF) (na : GName → GName → Mea GF),
    (∀ e e', e' ∈ Axpol.sPol GD e → gobCat GD e' e) ∧
    (∀ e e', e' ∈ Axpol.lobp GD e → gobCat GD e' e) ∧
    (∀ γ γc, (FiniteMap.dom_set (ea γ γc) : GSet Geid) = FiniteMap.dom_set (na γ γc)) ∧
    (∀ γ γc, (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid) ⊆ FiniteMap.dom_set (na γ γc)) ∧
    (∀ γ γc, ∀ e0 gm, get? (ea γ γc) e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0) ∧
    (∀ γ γc, lockMutexVerifiedWp'' L x γ γc GD (ea γ γc) (na γ γc))

end LockMutexWp2

end Weak
