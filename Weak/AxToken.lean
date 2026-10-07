/-
Weak: **THE L2 OWNED POINTS-TO** (AxSL tier): the fraction-multiset token, the tie invariant,
and the read/write rules.

Rocq: `iris/AxToken.v` @ xxvzwolszwmp.

Rocq header (in substance; design `claude-notes/design/weak-memory-lb-axsl.md` §1-L2 "The
token", "Write rule", "Read rule", "Epochs", §0.5 item 3).  Built on `Weak.AxGhost`'s per-byte
history ghost (`histAuth`/`histSnap`, the validation lemma `ownedReadGhost`) and
`Weak.AxGraphCat`'s pure GMO vocabulary; §7 touches `Weak.AxWp`'s tied annotation.

  §1  THE SURFACE points-to: `ownedFrac γ a q v` (a bare fractional piece of byte `a`'s
      history, agreeing on the last-written value `v`) and `owned γ a v := ownedFrac γ a 1 v`.
  §2  THE TOKEN: the GLOBAL ghost-level device `tok γ a H S` — a `GMapF Geid Qp` of who holds
      which fraction; `tokSplit`/`tokMerge` move a piece between two events PAIRWISE (no global
      "fractions sum to 1" bookkeeping), `tokAgree`, `tokSingleton`, `tokAlloc`.
  §3  THE TIE INVARIANT in GMO form: `tieBase` (a CORRECTED form of the commissioned
      `tie_inv`-only formula, which is false at the fresh-write moment: `w` would have to be
      gmo/po-before itself), the transports `tieLob`/`tieWrite`/`tieAcq`/`tieDeposit`, and the
      Iris-level `tokTie`.  Only the GMO half of `tie_inv`'s disjunction is kept (the PO branch
      belongs to case (ii)'s own forwarding argument).
  §4  THE READ RULE: `ownedReadRuleFwd` (case (ii), pure, `ownForwardCat'`) and
      `ownedReadRule` (both cases, over `tokTie`, through `ownedReadGhost`).
  §5  THE WRITE RULE: `ownedWriteRule` (full fraction; deposit a snapshot) and
      `ownedWriteRuleCovers`; `tokTieAfterWrite` (§3) re-establishes the invariant.
  §6  NON-VACUITY: `fwdDemoWriteThenRead` on `AxGraphWit`'s `fwd`, and on `AxGraphWit.rel` the
      counterexample to tokenless reads (`relStaleNoGhostCoverage`,
      `relReownerOwnedReadRule`).
  §7  THE TIED FORM over `AxAnnot.annotOwn` (Rocq `e ↦ₐ P`): `tokTied`, `tokTiedAlloc`.
      Redemption (`flowEqDyn`/`naSplittingWf`) is NOT reproved (as in Rocq).

  LEFT UNDONE in Rocq (and so here): `Φ_lock`/`Φ_flag`, the `alive(lock)` fraction, the epoch
  ghost's wiring into `tok`, full soundness against `wpPre`.

  No statement depends on instruction fetches (the file speaks of `gwritesByte`/`greadsByte`/
  `gmoLt`/`gpo` and the ghost only).

**Deviations from Rocq.**

1. NAMES: camelCase (map below).  None of the names is in `notes/weak-port-dupnames.json`; no
   Lean-only helpers except `AxToken.histJoinAgree` (file-qualified; the join of two fractions
   whose histories agree, used by `ownedFrac_fractional`).
2. VOCABULARY (`AxGhost` deviation 2): `last l` ↦ `l.getLast?`; `H.*1` ↦ `H.map Prod.fst`;
   `S !! e` ↦ `get? S e`; `dom S` ↦ `(FiniteMap.dom_set S : GSet Geid)`; `<[e := q]> S` ↦
   `insert S e q`; `delete e S` ↦ `delete S e`; `gmap geid Qp` ↦ `GMapF Geid Qp`; `gd_g GD` ↦
   `GD.gdG`; `gpo` ↦ `WeakRvwmoGraph.gpo`; `WeakLitmus.b1/b2` ↦ `b1`/`b2`; `bv 8` ↦ `BitVec 8`.
3. CAMERAS (`AxGhost` deviation 3): `axlogG Σ hent` ↦ `[AxlogG GF Hent]`; `axannotGS Σ` ↦
   `[AxannotGS GF]` (`AxAnnot.annotOwn e P` for `e ↦ₐ P`, `annotAlloc` for `annot_alloc`).
4. STATEMENT SHAPES (`AxGhost` deviation 4): `P -∗ Q` is `P ⊢ Q`, `P -∗ Q -∗ R` is
   `P ∗ Q ⊢ R`, `P ==∗ Q` is `P ⊢ |==> Q`, `-∗ False` is `⊢ False`; `tok_tied_alloc` keeps
   `annotAlloc`'s shape `⊢ P ==∗ Q`.  Pure premises stay `→`.
5. `Fractional`/`AsFractional` are iris-lean's classes (`AsFractional` takes `InOut` modes).
6. PROOFS: `fwd_demo_write_then_read`'s `vm_compute`/`vmr` steps are `decide +kernel` on the
   boolean twins (`gpoBSpec`/`gwbBSpec`/`grbBSpec`/`gmoLtBSpec`), as `AxGraphWit.fwdOwnForward`.

**Rocq → Lean name map.**  `owned_frac` `ownedFrac`, `owned` `owned`, `owned_frac_timeless`
`ownedFrac_timeless`, `owned_frac_fractional` `ownedFrac_fractional`,
`owned_frac_as_fractional` `ownedFrac_as_fractional`, `owned_frac_agree` `ownedFracAgree`,
`owned_frac_snap` `ownedFracSnap`; `tok` `tok`, `tok_empty` `tokEmpty`, `tok_singleton`
`tokSingleton`, `tok_alloc` `tokAlloc`, `tok_agree` `tokAgree`, `tok_snap` `tokSnap`,
`tok_split` `tokSplit`, `tok_merge` `tokMerge`; `hent_last_fst` `hentLastFst`, `tie_base`
`tieBase`, `tie_inv_gmo_tie_base` `tieInvGmoTieBase`, `tie_lob` `tieLob`, `tie_write`
`tieWrite`, `tie_acq` `tieAcq`, `tie_deposit_pre` `tieDepositPre`, `tie_deposit` `tieDeposit`,
`tie_base_visible` `tieBaseVisible`, `tok_tie` `tokTie`, `tok_tie_tok` `tokTieTok`,
`tok_tie_after_write` `tokTieAfterWrite`; `owned_read_rule_fwd` `ownedReadRuleFwd`,
`owned_read_rule` `ownedReadRule`; `owned_write_rule` `ownedWriteRule`,
`owned_write_rule_covers` `ownedWriteRuleCovers`; `fwd_demo_write_then_read`
`fwdDemoWriteThenRead`, `rel_stale_no_ghost_coverage` `relStaleNoGhostCoverage`,
`rel_reowner_owned_read_rule` `relReownerOwnedReadRule`; `tok_tied` `tokTied`,
`tok_tied_alloc` `tokTiedAlloc`.

**Not ported:** the §8 `Print Assumptions` audit (the lint's axiom check covers it).

**Statements checked** (diffed against Rocq by hand): all; the changed spellings are the
deviations above.
-/
import Weak.AxGhost
import Weak.AxWp
import Weak.AxGraphWit
import Weak.AxGraphCat
import Weak.AxGraphDec
import Weak.AxGraph
import Weak.WeakRvwmoGraph
import MachCSL.StdppMap
import MachCSL.StdppSet
import Iris.BI.BigOp.BigSepMap
import Iris.BI.BigOp.BigSepSet
import Iris.BI.Lib.Fractional
import Iris.ProofMode

namespace Weak

open Iris Iris.BI Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! ## 1. THE SURFACE POINTS-TO -/

section surface

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- A bare fractional piece of byte `a`'s history, agreeing with every other piece on the
LAST-WRITTEN value (the writer is existential). -/
def ownedFrac (γ : GName) (a : Int) (q : Qp) (v : BitVec 8) : IProp GF :=
  iprop(∃ H : List Hent, histAuth γ a q H ∗ ⌜∃ e, H.getLast? = some (e, v)⌝)

def owned (γ : GName) (a : Int) (v : BitVec 8) : IProp GF := ownedFrac γ a 1 v

instance ownedFrac_timeless (γ : GName) (a : Int) (q : Qp) (v : BitVec 8) :
    Timeless (ownedFrac (GF := GF) γ a q v) := by
  unfold ownedFrac; infer_instance

/-- Lean-only (file-qualified): two fractions join, their histories agreeing. -/
theorem AxToken.histJoinAgree (γ : GName) (a : Int) (q1 q2 : Qp) (H1 H2 : List Hent) :
    histAuth (GF := GF) γ a q1 H1 ∗ histAuth γ a q2 H2 ⊢ histAuth γ a (q1 + q2) H1 :=
  BI.pure_elim _ ((histAgree γ a q1 q2 H1 H2).trans (BI.pure_mono And.left))
    (fun h => by subst h; exact histJoin γ a q1 q2 H1)

instance ownedFrac_fractional (γ : GName) (a : Int) (v : BitVec 8) :
    Fractional (fun q => ownedFrac (GF := GF) γ a q v) where
  fractional q1 q2 := by
    show ownedFrac γ a (q1 + q2) v ⊣⊢ ownedFrac γ a q1 v ∗ ownedFrac γ a q2 v
    unfold ownedFrac
    constructor
    · iintro ⟨%H, Ha, %He⟩
      icases histSplit γ a q1 q2 H $$ Ha with ⟨Ha1, Ha2⟩
      isplitl [Ha1]
      · iexists H
        isplitl [Ha1]
        · iexact Ha1
        · ipureintro; exact He
      · iexists H
        isplitl [Ha2]
        · iexact Ha2
        · ipureintro; exact He
    · iintro ⟨⟨%H1, Ha1, %He1⟩, ⟨%H2, Ha2, %He2⟩⟩
      iexists H1
      isplitl [Ha1 Ha2]
      · iapply AxToken.histJoinAgree γ a q1 q2 H1 H2
        isplitl [Ha1]
        · iexact Ha1
        · iexact Ha2
      · ipureintro; exact He1

instance ownedFrac_as_fractional (γ : GName) (a : Int) (q : Qp) (v : BitVec 8)
    {ioΦ ioq : Iris.ProofMode.InOut} :
    AsFractional (ownedFrac (GF := GF) γ a q v) ioΦ (fun q => ownedFrac γ a q v) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := inferInstance

/-- Two pieces agree on the last-written value. -/
theorem ownedFracAgree (γ : GName) (a : Int) (q1 q2 : Qp) (v1 v2 : BitVec 8) :
    ownedFrac (GF := GF) γ a q1 v1 ∗ ownedFrac γ a q2 v2 ⊢ ⌜v1 = v2⌝ := by
  unfold ownedFrac
  iintro ⟨⟨%H1, Ha1, %He1⟩, ⟨%H2, Ha2, %He2⟩⟩
  icases histAgree γ a q1 q2 H1 H2 $$ [$Ha1 $Ha2] with %hag
  ipureintro
  obtain ⟨rfl, _⟩ := hag
  obtain ⟨e1, he1⟩ := He1
  obtain ⟨e2, he2⟩ := He2
  rw [he1, Option.some.injEq, Prod.mk.injEq] at he2
  exact he2.2

/-- A persistent snapshot of the underlying history. -/
theorem ownedFracSnap (γ : GName) (a : Int) (q : Qp) (v : BitVec 8) :
    ownedFrac (GF := GF) γ a q v ⊢
      ∃ H : List Hent, histSnap γ a H ∗ ⌜∃ e, H.getLast? = some (e, v)⌝ := by
  unfold ownedFrac
  iintro ⟨%H, Ha, %He⟩
  ihave #Hs := histSnapGet γ a q H $$ Ha
  iexists H
  isplitl []
  · iexact Hs
  · ipureintro; exact He

end surface

/-! ## 2. THE TOKEN: the GLOBAL, GHOST-LEVEL fraction-multiset device

`S : GMapF Geid Qp` maps each current holder to its fraction.  NO "sum = 1" side condition:
`tokSplit`/`tokMerge` are PAIRWISE, local `Qp` arithmetic. -/

section token

variable {GF : BundledGFunctors} [AxlogG GF Hent]

def tok (γ : GName) (a : Int) (H : List Hent) (S : GMapF Geid Qp) : IProp GF :=
  iprop([∗map] _e ↦ q ∈ S, histAuth γ a q H)

theorem tokEmpty (γ : GName) (a : Int) (H : List Hent) :
    ⊢ tok (GF := GF) γ a H (∅ : GMapF Geid Qp) := by
  unfold tok
  exact BigSepM.bigSepM_empty.2

theorem tokSingleton (γ : GName) (a : Int) (H : List Hent) (w : Geid) (q : Qp) :
    tok (GF := GF) γ a H {[w := q]} ⊣⊢ histAuth γ a q H := by
  unfold tok
  exact BigSepM.bigSepM_singleton

/-- Allocate a fresh token: one arrival event, the empty history. -/
theorem tokAlloc (X : GSet Int) (w0 : Geid) :
    ⊢@{IProp GF} |==> ∃ γ, [∗set] a ∈ X, tok γ a [] {[w0 := (1 : Qp)]} := by
  imod histAlloc (GF := GF) X ([] : List Hent) with ⟨%γ, H⟩
  imodintro
  iexists γ
  iapply BigSepS.bigSepS_mono (fun {a} _ => (tokSingleton (GF := GF) γ a [] w0 1).2) $$ H

/-- Two token instances on the SAME `(γ, a)` agree on `H`. -/
theorem tokAgree (γ : GName) (a : Int) (H1 : List Hent) (S1 : GMapF Geid Qp) (H2 : List Hent)
    (S2 : GMapF Geid Qp) (e1 : Geid) (q1 : Qp) (e2 : Geid) (q2 : Qp) :
    get? S1 e1 = some q1 → get? S2 e2 = some q2 →
    tok (GF := GF) γ a H1 S1 ∗ tok γ a H2 S2 ⊢ ⌜H1 = H2⌝ := by
  intro he1 he2
  unfold tok
  iintro ⟨T1, T2⟩
  icases (BigSepM.bigSepM_delete he1).1 $$ T1 with ⟨Ha1, -⟩
  icases (BigSepM.bigSepM_delete he2).1 $$ T2 with ⟨Ha2, -⟩
  icases histAgree γ a q1 q2 H1 H2 $$ [$Ha1 $Ha2] with %hag
  ipureintro
  exact hag.1

/-- A persistent snapshot of the shared history, keeping the token. -/
theorem tokSnap (γ : GName) (a : Int) (H : List Hent) (S : GMapF Geid Qp) (e : Geid) (q : Qp) :
    get? S e = some q → tok (GF := GF) γ a H S ⊢ tok γ a H S ∗ histSnap γ a H := by
  intro he
  unfold tok
  iintro T
  icases (BigSepM.bigSepM_lookup_acc he).1 $$ T with ⟨Ha, Hclose⟩
  ihave #Hs := histSnapGet γ a q H $$ Ha
  isplitl [Ha Hclose]
  · iapply Hclose
    iexact Ha
  · iexact Hs

/-- PULL a piece `q2` of `e`'s fraction into a fresh event `e'`; both retain theirs. -/
theorem tokSplit (γ : GName) (a : Int) (H : List Hent) (S : GMapF Geid Qp) (e : Geid)
    (q1 q2 : Qp) (e' : Geid) :
    get? S e = some (q1 + q2) → e' ∉ (FiniteMap.dom_set S : GSet Geid) → e ≠ e' →
    tok (GF := GF) γ a H S ⊢ tok γ a H (insert (insert (delete S e) e' q2) e q1) := by
  intro he hout hne
  have hn1 : get? (delete S e) e' = none := by
    rw [lookupDeleteNe hne]; exact notElemOfDom1 hout
  have hn2 : get? (insert (delete S e) e' q2) e = none := by
    rw [lookupInsertNe (Ne.symm hne)]; exact lookupDelete
  unfold tok
  iintro T
  icases (BigSepM.bigSepM_delete he).1 $$ T with ⟨Ha, T⟩
  icases histSplit γ a q1 q2 H $$ Ha with ⟨Ha1, Ha2⟩
  iapply (BigSepM.bigSepM_insert hn2).2
  isplitl [Ha1]
  · iexact Ha1
  · iapply (BigSepM.bigSepM_insert hn1).2
    isplitl [Ha2]
    · iexact Ha2
    · iexact T

/-- The inverse: combine `e`'s and `e'`'s fractions back into `e`, dropping `e'`. -/
theorem tokMerge (γ : GName) (a : Int) (H : List Hent) (S : GMapF Geid Qp) (e e' : Geid)
    (q1 q2 : Qp) :
    e ≠ e' → get? S e = some q1 → get? S e' = some q2 →
    tok (GF := GF) γ a H S ⊢ tok γ a H (insert (delete S e') e (q1 + q2)) := by
  intro hne he he'
  have hde : get? (delete S e') e = some q1 := by rw [lookupDeleteNe (Ne.symm hne)]; exact he
  unfold tok
  iintro T
  icases (BigSepM.bigSepM_delete he').1 $$ T with ⟨Ha2, T⟩
  icases (BigSepM.bigSepM_delete hde).1 $$ T with ⟨Ha1, T⟩
  iapply BigSepM.bigSepM_insert_delete.2
  isplitl [Ha1 Ha2]
  · iapply histJoin γ a q1 q2 H
    isplitl [Ha1]
    · iexact Ha1
    · iexact Ha2
  · iexact T

end token

/-! ## 3. THE TIE INVARIANT, in GMO form -/

/-- `H.map Prod.fst`'s last entry is the writer named by `H`'s own last entry. -/
theorem hentLastFst (H : List Hent) (wl : Geid) (vl : BitVec 8) :
    H.getLast? = some (wl, vl) → (H.map Prod.fst).getLast? = some wl := by
  intro hl
  obtain ⟨H0, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  simp

/-- Only the GMO half of `tie_inv`'s disjunction, plus the fresh-tie case. -/
def tieBase (G : Gexec) (Hl : List Geid) (e : Geid) : Prop :=
  Hl.getLast? = some e ∨ ∃ wl, Hl.getLast? = some wl ∧ gmoLt G wl e

/-- `tie_inv`'s GMO branch is a `tieBase` fact. -/
theorem tieInvGmoTieBase (G : Gexec) (Hl : List Geid) (e wl : Geid) :
    Hl.getLast? = some wl → gmoLt G wl e → tieBase G Hl e :=
  fun h1 h2 => Or.inr ⟨wl, h1, h2⟩

/-- THE LOB TRANSPORT. -/
theorem tieLob (G : Gexec) (Hl : List Geid) (e e' : Geid) :
    tieBase G Hl e → gmoLt G e e' → tieBase G Hl e' := by
  rintro (heq | ⟨wl, hlast, hmo⟩) hmo'
  · exact Or.inr ⟨e, heq, hmo'⟩
  · exact Or.inr ⟨wl, hlast, gmoLtTrans G _ _ _ hmo hmo'⟩

/-- THE WRITE: re-tying at `w` trivially satisfies `tieBase`. -/
theorem tieWrite (G : Gexec) (H : List Hent) (w : Geid) (v : BitVec 8) :
    tieBase G ((H ++ [(w, v)]).map Prod.fst) w :=
  Or.inl (hentLastFst (H ++ [(w, v)]) w v (by simp))

/-- THE ACQUIRE. -/
theorem tieAcq (G : Gexec) (Hl : List Geid) (acq wl : Geid) :
    Hl.getLast? = some wl → gmoLt G wl acq → tieBase G Hl acq :=
  fun h1 h2 => Or.inr ⟨wl, h1, h2⟩

/-- THE DEPOSIT precondition: `last H` gmo-before the release write `R`. -/
def tieDepositPre (G : Gexec) (H : List Geid) (R : Geid) : Prop :=
  ∃ wl, H.getLast? = some wl ∧ gmoLt G wl R

theorem tieDeposit (G : Gexec) (H : List Geid) (R acq : Geid) :
    tieDepositPre G H R → gmoLt G R acq → tieBase G H acq := by
  rintro ⟨wl, hlast, hmo⟩ hmo'
  exact Or.inr ⟨wl, hlast, gmoLtTrans G _ _ _ hmo hmo'⟩

/-- THE VISIBILITY COROLLARY the read rule consumes (cross-hart capable). -/
theorem tieBaseVisible (G : Gexec) (Hl : List Geid) (e r : Geid) :
    tieBase G Hl e → gmoLt G e r → ∃ wl, Hl.getLast? = some wl ∧ gvisible G wl r := by
  rintro (heq | ⟨wl, hlast, hmo⟩) hmor
  · exact ⟨e, heq, Or.inl hmor⟩
  · exact ⟨wl, hlast, Or.inl (gmoLtTrans G _ _ _ hmo hmor)⟩

section tokTie

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- THE IRIS-LEVEL INVARIANT: a token with the pure tie fact at every current holder. -/
def tokTie (GD : Gdexec) (γ : GName) (a : Int) (H : List Hent) (S : GMapF Geid Qp) :
    IProp GF :=
  iprop(tok γ a H S ∗
    ⌜∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → tieBase GD.gdG (H.map Prod.fst) e⌝)

theorem tokTieTok (GD : Gdexec) (γ : GName) (a : Int) (H : List Hent) (S : GMapF Geid Qp) :
    tokTie (GF := GF) GD γ a H S ⊢ tok γ a H S := by
  unfold tokTie
  iintro ⟨T, -⟩
  iexact T

/-- THE WRITE re-establishes the invariant at the re-tied singleton. -/
theorem tokTieAfterWrite (GD : Gdexec) (γ : GName) (a : Int) (H : List Hent) (w : Geid)
    (v : BitVec 8) :
    histAuth (GF := GF) γ a 1 H ⊢ |==> tokTie GD γ a (H ++ [(w, v)]) {[w := (1 : Qp)]} := by
  iintro Ha
  imod histAppend γ a H (w, v) $$ Ha with Ha
  imodintro
  unfold tokTie
  isplitl [Ha]
  · iapply (tokSingleton γ a (H ++ [(w, v)]) w 1).2
    iexact Ha
  · ipureintro
    intro e he
    rw [domSingleton, elemOfSingleton] at he
    subst he
    exact tieWrite GD.gdG H e v

end tokTie

/-! ## 4. THE READ RULE -/

/-- CASE (ii), PURE: the hart's own forwarded write `wl` IS the rf-source. -/
theorem ownedReadRuleFwd (GD : Gdexec) (a : Int) (r wl : Geid) (vl : BitVec 8) (t : Nat)
    (vr : BitVec 8) :
    rvwmoCatConsistent GD →
    WeakRvwmoGraph.gpo GD.gdG wl r → gwritesByte GD.gdG wl a vl →
    greadsByte GD.gdG r a t vr →
    ¬ gmoLt GD.gdG wl r →
    (∀ w' v', gwritesByte GD.gdG w' a v' →
      WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' r → False) →
    grfAt GD.gdG a wl r ∧ ∀ t' v', greadsByte GD.gdG r a t' v' → v' = vl := by
  intro hcons hpo hwb hrd hnmo hnoint
  obtain ⟨hrf, rfl⟩ := ownForwardCat' GD a wl r vl t vr hcons hpo hwb hrd hnmo hnoint
  exact ⟨hrf, fun t' v' hrd' => (greadsByteDet _ _ _ _ _ _ _ hrd' hrd).2⟩

section readRule

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- THE FULL READ RULE, over `tokTie`: (i) a tie gmo-before `r` gives visibility of
`last H` and `ownedReadGhost` validates; (ii) every tie gmo-after `r`: pure forwarding. -/
theorem ownedReadRule (GD : Gdexec) (a : Int) (r : Geid) (γ : GName) (H : List Hent)
    (S : GMapF Geid Qp) (wl : Geid) (vl : BitVec 8) :
    rvwmoCatConsistent GD →
    (∀ p, p ∈ H → gwritesByte GD.gdG p.1 a p.2) →
    chainWith (gmoLt GD.gdG) (H.map Prod.fst) →
    (∀ w v, gwritesByte GD.gdG w a v → WeakRvwmoGraph.gpo GD.gdG w r → w ∈ H.map Prod.fst) →
    H.getLast? = some (wl, vl) →
    (∃ t v, greadsByte GD.gdG r a t v) →
    ((∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e r)
     ∨
     (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
      (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e r) ∧
      WeakRvwmoGraph.gpo GD.gdG wl r ∧
      (∀ w' v', gwritesByte GD.gdG w' a v' →
        WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' r → False))) →
    tokTie (GF := GF) GD γ a H S ∗
      (∀ w v, ⌜gwritesByte GD.gdG w a v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ a H') ⊢
    ⌜grfAt GD.gdG a wl r ∧ ∀ t v, greadsByte GD.gdG r a t v → v = vl⌝ := by
  intro hcons hwr hch hown hlast hrd hcase
  rcases hcase with ⟨e, he, hmo⟩ | ⟨hwin, hall, hpowl, hnoint⟩
  · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (elemOfDom.mp he)
    unfold tokTie tok
    iintro ⟨⟨T, %htie⟩, Hsn⟩
    icases (BigSepM.bigSepM_delete hq).1 $$ T with ⟨Ha, -⟩
    obtain ⟨wl', hlast', hvis⟩ := tieBaseVisible GD.gdG (H.map Prod.fst) e r (htie e he) hmo
    have hwl : wl' = wl := by
      rw [hentLastFst H wl vl hlast, Option.some.injEq] at hlast'
      exact hlast'.symm
    subst hwl
    iapply ownedReadGhost GD a r γ q H wl' vl hcons hwr hch hown hlast hvis hrd
    isplitl [Ha]
    · iexact Ha
    · iexact Hsn
  · iintro -
    ipureintro
    obtain ⟨t, vr, hrd⟩ := hrd
    have hwb : gwritesByte GD.gdG wl a vl := by
      apply hwr (wl, vl)
      obtain ⟨H0, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
      simp
    exact ownedReadRuleFwd GD a r wl vl t vr hcons hpowl hwb hrd (hall wl hwin) hnoint

end readRule

/-! ## 5. THE WRITE RULE

A write `w` to `a` with the FULL fraction: `H' := H ++ [(w, v)]`, deposit `histSnap γ a H'`
(the `Φ_own` protocol content); re-tie at `w` (`tokTieAfterWrite`, §3). -/

section writeRule

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem ownedWriteRule (γ : GName) (a : Int) (H : List Hent) (w : Geid) (v : BitVec 8) :
    histAuth (GF := GF) γ a 1 H ⊢
      |==> (histAuth γ a 1 (H ++ [(w, v)]) ∗ histSnap γ a (H ++ [(w, v)])) := by
  iintro Ha
  imod histAppend γ a H (w, v) $$ Ha with Ha
  ihave #Hs := histSnapGet γ a 1 (H ++ [(w, v)]) $$ Ha
  imodintro
  isplitl [Ha]
  · iexact Ha
  · iexact Hs

/-- The deposited snapshot covers `w` itself. -/
theorem ownedWriteRuleCovers (γ : GName) (a : Int) (H : List Hent) (w : Geid) (v : BitVec 8) :
    histSnap (GF := GF) γ a (H ++ [(w, v)]) ⊢ ⌜w ∈ (H ++ [(w, v)]).map Prod.fst⌝ := by
  iintro -
  ipureintro
  exact histSnapLastIn _ w v (by simp)

end writeRule

/-! ## 6. NON-VACUITY

§6.1 allocates a history and drives ONE write + ONE read on `fwd` through §4/§5's rules
(case (ii), forwarding).  §6.2 is the counterexample to tokenless reads on `AxGraphWit.rel`:
(a) the ORIGINAL owner's stale piece cannot supply `ownedReadRule`'s ghost coverage; (b) a
holder of the RE-OWNER's history validates, recovering `relRf`'s verdict. -/

section nonvacuity

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-! ### 6.1 `fwd`: allocate, write, forward-read -/

theorem fwdDemoWriteThenRead :
    ⊢@{IProp GF} |==> ∃ γ, histAuth γ 0 1 [((0, 0), b1)] ∗
      ⌜grfAt fwd.gdG 0 (0, 0) (0, 1) ∧
        ∀ t v, greadsByte fwd.gdG (0, 1) 0 t v → v = b1⌝ := by
  have hpure : grfAt fwd.gdG 0 (0, 0) (0, 1) ∧
      ∀ t v, greadsByte fwd.gdG (0, 1) 0 t v → v = b1 := by
    refine ownedReadRuleFwd fwd 0 (0, 1) (0, 0) b1 3 b1 AxGraphWit.fwdCat
      ((gpoBSpec _ _ _).1 (by decide +kernel))
      ((gwbBSpec _ _ _ _).1 (by decide +kernel))
      ((grbBSpec _ _ _ _ _).1 (by decide +kernel)) ?_ ?_
    · intro h
      have h' := (gmoLtBSpec _ _ _).2 h
      have hf : gmoLtB fwd.gdG (0, 0) (0, 1) = false := by decide +kernel
      rw [hf] at h'
      cases h'
    · rintro w' v' _ ⟨_, hlt, _⟩ ⟨_, hlt', _⟩
      dsimp only at hlt hlt'
      omega
  have hw := fun γ => ownedWriteRule (GF := GF) γ 0 [] (0, 0) b1
  simp only [List.nil_append] at hw
  imod histAlloc (GF := GF) ({0} : GSet Int) ([] : List Hent) with ⟨%γ, H⟩
  ihave H := BigSepS.bigSepS_singleton.1 $$ H
  imod hw γ $$ H with ⟨H, -⟩
  imodintro
  iexists γ
  isplitl [H]
  · iexact H
  · ipureintro
    exact hpure

/-! ### 6.2 `rel`: the counterexample to tokenless reads -/

/-- (a) THE ORIGINAL OWNER'S STALE PIECE HAS NO VALIDATING TOKEN. -/
theorem relStaleNoGhostCoverage (γ : GName) (q : Qp) :
    histAuth (GF := GF) γ 0 q [((0, 0), b1)] ∗
      (∀ w v, ⌜gwritesByte AxGraphWit.rel.gdG w 0 v⌝ -∗
        ⌜gmoLt AxGraphWit.rel.gdG w (0, 3)⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ 0 H') ⊢ iprop(False) := by
  iintro ⟨Ha, Hsn⟩
  icases Hsn $$ %(1, 1) %b2 %relNeedsW11.1 %relNeedsW11.2.1 with ⟨%H', %hin, Hs⟩
  iapply relStaleToken γ q H' hin
  isplitl [Ha]
  · iexact Ha
  · iexact Hs

/-- (b) A HOLDER OF THE RE-OWNER'S HISTORY VALIDATES: rf-source `(1,1)`, value `b2`. -/
theorem relReownerOwnedReadRule (γ : GName) (q : Qp) :
    histAuth (GF := GF) γ 0 q Hrel ⊢
      ⌜grfAt AxGraphWit.rel.gdG 0 (1, 1) (0, 3) ∧
        ∀ t v, greadsByte AxGraphWit.rel.gdG (0, 3) 0 t v → v = b2⌝ := by
  iintro Ha
  ihave #Hs := histSnapGet γ 0 q Hrel $$ Ha
  iapply relValidated γ q
  isplitl [Ha]
  · iexact Ha
  · iexact Hs

end nonvacuity

/-! ## 7. THE TIED FORM, over `AxAnnot.annotOwn` (Rocq `e ↦ₐ P`)

A piece deposited AT event `e` for a lob-successor to redeem is `annotOwn e (histAuth γ a q H)`;
allocation is FREE (`annotAlloc` does not ask for the content).  Redemption is `AxWp`'s
`flowEqDyn`/`naSplittingWf` machinery, NOT reproved here. -/

section tied

variable {GF : BundledGFunctors} [AxannotGS GF] [AxlogG GF Hent]

def tokTied (γ : GName) (a : Int) (H : List Hent) (e : Geid) (q : Qp) : IProp GF :=
  AxAnnot.annotOwn e (histAuth γ a q H)

theorem tokTiedAlloc (na : Mea GF) (γ : GName) (a : Int) (H : List Hent) (e : Geid) (q : Qp) :
    e ∉ (FiniteMap.dom_set na : GSet Geid) →
    ⊢ AxAnnot.annotInterp na ==∗
      AxAnnot.annotInterp (insert na e (histAuth γ a q H)) ∗ tokTied γ a H e q :=
  annotAlloc na e _

end tied

end Weak
