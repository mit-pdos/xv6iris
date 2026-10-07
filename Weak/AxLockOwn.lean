/-
Weak: **THE OWNERSHIP ROUTE for a lock handoff read** (AxSL tier): `lockReadOwn`.

Rocq: `iris/AxLockOwn.v` @ xxvzwolszwmp.

Rocq header, in substance (design `claude-notes/design/weak-memory-lb-axsl.md` §7.R, tracker
G3).  Companion to `Weak.AxLockGraph`'s PURE route (`lockHandoffGraph`, which assumes the LOCK
DISCIPLINE "`w_x` is gmo-maximal among writes to `x`") and AxProtLock's protocol slot (which
hands the acquiring RMW a re-tied `tokTie` for `x`).  Here B's read `r_x` (po-after its own
`.aq` acquire `acq`) gets its graph value pinned by the TOKEN alone.

  §1  `lockAcqForcesCaseI` (pure: the `.aq` tie po-before `r_x` is gmo-before it, so
      `ownedReadRule`'s case (i) holds with witness `acq`); `lockReadOwn` (the ownership
      route over `tokTie GD γ x H {[acq := 1]}`); `lockReadOwnGenesis` (the first-ever
      acquire: an EMPTY `histAuth` forces the read to take the era-initial image, via
      `histSnapAfterLast`).
  §2  THE TWO ROUTES AGREE: `lockDisciplineOwn` (in a gmo-chained list every member is the
      last or gmo-before it), `lockDisciplineFromOwnership` (full coverage gives
      `lockHandoffGraph`'s discipline), `lockReadPureAgrees`.

  Smell test (Rocq header): dropping the `tokTie` premise breaks the proof twice — the
  `tieBase` fact for `acq` lives only inside `tokTie`, and `ownedReadGhost` needs the ghost
  resource to rule out an untracked interfering write.

  No statement depends on instruction fetches (graph vocabulary `gwritesByte`/`greadsByte`/
  `gmoLt`/`gpo`/`gacqPo` and the history ghost only; `Lbl` has no fetch constructor).

**Deviations from Rocq.**

1. NAMES: camelCase (map below).  None of the names is in `notes/weak-port-dupnames.json`; no
   Lean-only helpers.  Dependencies' duplicates referred to qualified (`WeakRvwmoGraph.gpo`,
   `WeakRvwmoAcyc.grf`).
2. VOCABULARY (as `AxToken` deviation 2): `last l` ↦ `l.getLast?`; `H.*1` ↦ `H.map Prod.fst`;
   `dom S` ↦ `(FiniteMap.dom_set S : GSet Geid)`; `gmap geid Qp` ↦ `GMapF Geid Qp`; `gd_g GD` ↦
   `GD.gdG`; `gx_img G x` ↦ `G.gxImg x`; `Z` ↦ `Int`; `bv 8` ↦ `BitVec 8`.
3. CAMERAS / SHAPES (as `AxToken` deviations 3-4): `axlogG Σ hent` ↦ `[AxlogG GF Hent]`;
   `P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`; pure premises stay `→`.
4. PROOF of `lockAcqForcesCaseI`: direct (the acquire is its own witness through ppo rule 5)
   instead of `tieCases` over `elements (dom S)` + `tieAcqCase`; statement unchanged.

**Rocq → Lean name map.**  `lock_acq_forces_case_i` `lockAcqForcesCaseI`, `lock_read_own`
`lockReadOwn`, `lock_read_own_genesis` `lockReadOwnGenesis`, `lock_discipline_own`
`lockDisciplineOwn`, `lock_discipline_from_ownership` `lockDisciplineFromOwnership`,
`lock_read_pure_agrees` `lockReadPureAgrees`.

**Not ported:** the §3 `Print Assumptions` audit (the lint's axiom check covers it).
-/
import Weak.AxToken
import Weak.AxLockGraph
import Weak.AxGhost
import Weak.AxGraphCat
import Weak.AxGraph
import Weak.WeakRvwmoGraph
import MachCSL.StdppMap
import MachCSL.StdppSet
import Iris.ProofMode

namespace Weak

open Iris Iris.BI Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! ## 1. `lockReadOwn` — the ownership route -/

/-- THE ACQUIRE FORCES CASE (i), pure: the `.aq` tie `acq` is po-before `r_x` (ppo rule 5),
hence gmo-before it. -/
theorem lockAcqForcesCaseI (GD : Gdexec) (acq r_x : Geid) :
    gppoCatGmo GD → gacqPo GD.gdG acq r_x →
    ∃ e, e ∈ (FiniteMap.dom_set ({[acq := (1 : Qp)]} : GMapF Geid Qp) : GSet Geid) ∧
      gmoLt GD.gdG e r_x := by
  intro hppo hacq
  refine ⟨acq, ?_, ?_⟩
  · rw [domSingleton, elemOfSingleton]
  · exact Classical.byContradiction fun hn =>
      tieAcqCase GD [acq] acq r_x hppo (elem_of_cons.2 (Or.inl rfl)) hacq
        (fun e he => by
          rcases elem_of_cons.1 he with rfl | h
          · exact hn
          · exact absurd h List.not_mem_nil)

section lockReadOwn

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- THE OWNERSHIP ROUTE: `lockHandoffGraph`'s conclusion without the lock discipline, from
B's post-acquire `tokTie` and the coverage wand. -/
theorem lockReadOwn (GD : Gdexec) (γ : GName) (x : Int) (H : List Hent) (w_x acq r_x : Geid)
    (vx : BitVec 8) :
    rvwmoCatConsistent GD →
    (∀ p, p ∈ H → gwritesByte GD.gdG p.1 x p.2) →
    chainWith (gmoLt GD.gdG) (H.map Prod.fst) →
    (∀ w v, gwritesByte GD.gdG w x v → WeakRvwmoGraph.gpo GD.gdG w r_x →
      w ∈ H.map Prod.fst) →
    H.getLast? = some (w_x, vx) →
    gacqPo GD.gdG acq r_x →
    (∃ t v, greadsByte GD.gdG r_x x t v) →
    tokTie (GF := GF) GD γ x H {[acq := (1 : Qp)]} ∗
      (∀ w v, ⌜gwritesByte GD.gdG w x v⌝ -∗ ⌜gmoLt GD.gdG w r_x⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ x H') ⊢
    ⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝ := by
  intro hcons hwr hch hown hlast hacq hrd
  exact ownedReadRule GD x r_x γ H {[acq := (1 : Qp)]} w_x vx hcons hwr hch hown hlast hrd
    (Or.inl (lockAcqForcesCaseI GD acq r_x hcons.2.1 hacq))

/-- THE GENESIS OWNERSHIP ROUTE: from a RAW, EMPTY `histAuth` (first-ever acquire), `r_x`
read the era-initial image — an external rf-source would carry a snapshot mentioning it,
contradicting the empty auth. -/
theorem lockReadOwnGenesis (GD : Gdexec) (γ : GName) (x : Int) (r_x : Geid) (t : Nat)
    (v : BitVec 8) :
    rvwmoCatConsistent GD →
    (∀ w v', gwritesByte GD.gdG w x v' → w.1 = r_x.1 → False) →
    greadsByte GD.gdG r_x x t v →
    histAuth (GF := GF) γ x 1 [] ∗
      (∀ w v', ⌜gwritesByte GD.gdG w x v'⌝ -∗ ⌜grfe GD.gdG w r_x⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ x H') ⊢
    ⌜t = 0 ∧ GD.gdG.gxImg x = some v⌝ := by
  intro hcons hnpo hrd
  have hcase := (hcons.2.2.1 r_x x t v hrd).1
  cases t with
  | zero =>
    iintro -
    ipureintro
    exact ⟨rfl, hcase⟩
  | succ j =>
    obtain ⟨w0, hat0, hwb0, -⟩ := hcase
    have hext : w0.1 ≠ r_x.1 := fun heq => hnpo w0 v hwb0 heq
    have hgrfe : grfe GD.gdG w0 r_x := ⟨⟨x, j + 1, v, hrd, hat0⟩, hext⟩
    iintro ⟨Hauth, Hsn⟩
    ispecialize Hsn $$ %w0 %v %hwb0 %hgrfe
    icases Hsn with ⟨%H', %hin, Hsnap⟩
    iexfalso
    iapply histSnapAfterLast γ x 1 [] H' w0 hin (by simp)
    isplitl [Hauth]
    · iexact Hauth
    · iexact Hsnap

end lockReadOwn

/-! ## 2. THE TWO ROUTES AGREE -/

/-- In an `gmoLt`-chained list, every member is the last or gmo-before it. -/
theorem lockDisciplineOwn (G : Gexec) (Hl : List Geid) (w_x : Geid) :
    chainWith (gmoLt G) Hl →
    Hl.getLast? = some w_x →
    ∀ w, w ∈ Hl → w = w_x ∨ gmoLt G w w_x := by
  intro hch hlast w hin
  obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hin
  rw [List.getLast?_eq_getElem?] at hlast
  by_cases hne : i = Hl.length - 1
  · left
    subst hne
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hlast
    rw [← hiw, hlast]
  · right
    have hlt : i < Hl.length - 1 := by omega
    exact chainWithGmo G (gmoLt G) Hl i (Hl.length - 1) w w_x (fun _ _ h => h) hch
      (by rw [List.getElem?_eq_getElem hi, hiw]) hlast hlt

/-- ... at a byte-`x` history: full coverage gives `lockHandoffGraph`'s discipline. -/
theorem lockDisciplineFromOwnership (GD : Gdexec) (x : Int) (H : List Hent) (w_x : Geid)
    (vx : BitVec 8) :
    chainWith (gmoLt GD.gdG) (H.map Prod.fst) →
    H.getLast? = some (w_x, vx) →
    (∀ w vw, gwritesByte GD.gdG w x vw → w ∈ H.map Prod.fst) →
    ∀ w vw, gwritesByte GD.gdG w x vw → w = w_x ∨ gmoLt GD.gdG w w_x :=
  fun hch hlast hcov w vw hwb =>
    lockDisciplineOwn GD.gdG _ w_x hch (hentLastFst H w_x vx hlast) w (hcov w vw hwb)

/-- THE AGREEMENT COROLLARY: under full coverage the PURE route reaches the same conclusion. -/
theorem lockReadPureAgrees (GD : Gdexec) (x : Int) (w_x r_x w_rel acq : Geid) (vx v : BitVec 8)
    (t : Nat) (H : List Hent) :
    rvwmoCatConsistent GD →
    gwritesByte GD.gdG w_x x vx →
    gppoCat GD w_x w_rel →
    grfe GD.gdG w_rel acq →
    glblIs GD.gdG acq lbIsR →
    glblIs GD.gdG acq lbAq →
    WeakRvwmoGraph.gpo GD.gdG acq r_x →
    greadsByte GD.gdG r_x x t v →
    chainWith (gmoLt GD.gdG) (H.map Prod.fst) →
    H.getLast? = some (w_x, vx) →
    (∀ w vw, gwritesByte GD.gdG w x vw → w ∈ H.map Prod.fst) →
    WeakRvwmoAcyc.grf GD.gdG w_x r_x ∧ v = vx :=
  fun hcons hwx hrel hrf hacqR hacqAq hacqPo hrd hch hlast hcov =>
    lockHandoffGraph GD x w_x r_x w_rel acq vx v t hcons hwx hrel hrf hacqR hacqAq hacqPo hrd
      (lockDisciplineFromOwnership GD x H w_x vx hch hlast hcov)

end Weak
