/-
Weak: **THE L2 GHOST ALGEBRA** (AxSL tier): per-byte histories, class/epoch logs, and the
Iris-level VALIDATION lemma of the owned-read rule.

Rocq: `iris/AxGhost.v` @ xxvzwolszwmp.

Rocq header (in substance; design `claude-notes/design/weak-memory-lb-axsl.md` §1-L2 "The
token", "Read rule", "Epochs", §0.5 item 3, Track C of §2).  IRIS, NO MEMORY MODEL — except in
§4, where the validation lemma sits on `AxGraphCat.ownedReadCatSnoc`, and in §5.3, where it is
exercised on `AxGraphWit.rel`.

  §1  ONE generic per-byte MONOTONE LOG (`logAuth γ a q L`, fractional, fractions AGREE on `L`,
      growth needs the full fraction; `logSnap γ a L'`, persistent, a PREFIX of the auth).  One
      ghost name serves every byte: the camera is `GMapF Int (MonoList (DiscreteO A))`, so a
      byte's log is the singleton `{[a := ●ML{q} L]}`.  Both L2 ghosts below are INSTANCES of
      this one library.
  §2  THE HISTORY ghost `hist*` := the log at `Geid × BitVec 8` and THE KEY REFUTATION
      `histSnapAfterLast`: a snapshot cannot mention a write the auth does not.
  §3  THE CLASS/EPOCH ghost `cls*` := the log at `Wclass × Option Geid`, where THE EPOCH IS THE
      INDEX: `clsAuth γ a q c ep b` says the log has length `ep + 1` and entry `ep` is `(c, b)`;
      `clsSnap γ a c ep b` says entry `ep` IS `(c, b)` in the auth — epoch `ep` EXISTED (past or
      current).  Exactly what a snapshot proves: `clsSnapLookup`; the two consumable readings
      `clsSnapLe`.  A snapshot of a PAST epoch says NOTHING about the current class.
  §4  THE VALIDATION LEMMA `ownedReadGhost`: the L2 read rule's core.  The gmo-coverage
      hypothesis of `ownedReadCatCov` is DISCHARGED from ghost state — for every same-byte write
      gmo-before the read, a `histSnap` mentioning it — through `histSnapIn`; the own-po-earlier
      coverage, the chain-ness of `H`, and "the last entry is visible" stay PURE hypotheses.
  §5  NON-VACUITY: `histDemo`/`histDemoRogue`, the class demo, and the `rel` witness
      (`relNeedsW11`, `relStaleToken`, `relValidated`).

Notes on the commissioned statements (Rocq header): (1) the agreement lemmas also return
`q1 + q2 ≤ 1`; (2) `ownedReadGhost`'s snapshot hypothesis is the `∀`-wand "a snapshot mentioning
`w`" (membership is all the proof needs; the `last`-form deposit implies it,
`histSnapLastIn`); (3) CHAIN-NESS of `H` (gmo-chained; the proof derives the `obCatChain` the cat
lemma needs, since a gmo-increasing same-byte history is co-chained), "every entry writes byte
`a`", "own po-earlier writes ∈ H" and `gvisible (last H) r` are pure hypotheses; (4) the epoch
ghost's "change bumps ep" is `clsChange`.  LEFT UNDONE in Rocq (and so here): the `alive(lock)`
fraction token, `owned_read_epoch`, per-byte non-uniform initial logs.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase convention (name map below); the inductive `wclass` is `Wclass`,
   its constructors keep their Rocq spelling.  The notations `hent`/`cent` are the
   abbreviations `Hent`/`Cent`; `axlogR` stays a NOTATION, `AxlogR` (an applied abbreviation
   would mis-unify as `?M ?V`, the `MachCSL.GMapF` pitfall).
2. VOCABULARY (`WeakGhost` deviation 2): `l !! i` ↦ `l[i]?`; `last l` ↦ `l.getLast?`; `H.*1` ↦
   `H.map Prod.fst`; `S ep` ↦ `ep + 1`; `prefix_of` ↦ `<+:`; `gset Z` ↦ `GSet Int`;
   `bv 8` ↦ `BitVec 8`; `gd_g GD` ↦ `GD.gdG`; `WeakLitmus.b1/b2` (`B1`/`B2`) ↦ `b1`/`b2`.
3. CAMERAS (the `WeakGhost` deviation 7 / `WeakViewMono` deviation 2 precedent): iris-lean has no
   `gFunctors` lists and no `subG`; `axlogG Σ A` is the class `AxlogG GF A` whose field
   `axlogInG : ElemG GF (AxlogRF A)` (with `AxlogRF A := constOF (AxlogR A)`) is Rocq's `inG`.
   `axlogR A := gmapUR Z (mono_listR (leibnizO A))` is `GMapF Int (MonoList (DiscreteO A))`
   (iris-lean's `Heap.instStoreUCMRA`); `●ML{#q} L` is `MonoList.auth (DFrac.own q) (L.map
   DiscreteO.mk)` (the `MonoList.auth_own` spelling of iris-lean's own BI library).
4. STATEMENT SHAPES (`WeakGhost` deviation 9): `P -∗ Q` is `P ⊢ Q`, `P -∗ Q -∗ R` is
   `P ∗ Q ⊢ R`, `P ==∗ Q` is `P ⊢ |==> Q`, `-∗ False` is `⊢ False`.  Pure premises stay `→`.
   `owned_read_ghost`'s two wands (the auth, then the coverage) are `auth ∗ coverage ⊢ ⌜…⌝`.
5. `wclass_eq_dec` is `deriving DecidableEq`.  The `Fractional`/`AsFractional` instances are
   iris-lean's classes (`AsFractional` takes the `InOut` modes `ioΦ ioq`).
6. PROOFS (not statements): `rel_writes0` decides "every event of `rel` that writes byte 0 is
   (0,0) or (1,1)" over `gevents` by `decide +kernel` instead of computing the event list and
   case-splitting; `hist_demo` appends through `logUpdate` at the literal target lists (the
   `[] ++ [x]` spellings `hist_append` produces are not syntactically the goal's); `log_alloc`
   names the `constOF` functor instance of iris-lean's `bigOpS_iOwn_entail` explicitly (its
   `URFunctorContractive` search otherwise finds the gmap-functor instance); every Rocq `vm_compute` is `decide +kernel` on the boolean twin
   (`gwbBSpec`/`gmoLtBSpec`/`grbBSpec`/`gwaBSpec`), the `WeakDeps` recipe.

**Rocq → Lean name map.**  `axlogR`→`AxlogR` (+ `AxlogRF`), `axlogG`/`AxLogG`/`axlog_inG`→
`AxlogG`/`AxlogG.mk`/`AxlogG.axlogInG`, `log_auth/snap`→`logAuth/Snap`,
`log_snap_persistent`→`logSnap_persistent`, `log_auth_timeless`→`logAuth_timeless`,
`log_snap_timeless`→`logSnap_timeless`, `log_alloc/valid/agree/auth_op`→`logAlloc/Valid/Agree/
AuthOp`, `log_auth_fractional`→`logAuth_fractional`, `log_auth_as_fractional`→
`logAuth_as_fractional`, `log_snap_get/mono/prefix/elem/lookup`→`logSnapGet/Mono/Prefix/Elem/
Lookup`, `log_update/append`→`logUpdate/Append`; `hent`→`Hent`, `hist_snap_last_in`→
`histSnapLastIn`, `hist_auth/snap`→`histAuth/Snap`, `hist_snap_persistent`→
`histSnap_persistent`, `hist_auth_timeless`→`histAuth_timeless`, `hist_snap_timeless`→
`histSnap_timeless`, `hist_auth_fractional`→`histAuth_fractional`, `hist_auth_as_fractional`→
`histAuth_as_fractional`, `hist_alloc/agree/split/join`→`histAlloc/Agree/Split/Join`,
`hist_snap_get/prefix`→`histSnapGet/Prefix`, `hist_append`→`histAppend`, `hist_snap_in`→
`histSnapIn`, `hist_snap_after_last`→`histSnapAfterLast`; `wclass`→`Wclass` (constructors
`Wclass.CLown/CLro/CLlock/CLflag`), `cent`→`Cent`, `cls_log/auth/snap`→`clsLog/Auth/Snap`,
`cls_snap_persistent`→`clsSnap_persistent`, `cls_auth_timeless`→`clsAuth_timeless`,
`cls_snap_timeless`→`clsSnap_timeless`, `cls_alloc/agree/auth_op`→`clsAlloc/Agree/AuthOp`,
`cls_auth_fractional`→`clsAuth_fractional`, `cls_auth_as_fractional`→`clsAuth_as_fractional`,
`cls_snap_get/lookup/le`→`clsSnapGet/Lookup/Le`, `cls_change`→`clsChange`;
`owned_read_ghost`→`ownedReadGhost`; `Hdemo`→`Hdemo`, `hist_demo(_rogue/_prefix)`→
`histDemo(Rogue/Prefix)`, `cls_demo(_stale/_future)`→`clsDemo(Stale/Future)`, `Hrel`→`Hrel`,
`rel_writes0`→`relWrites0`, `rel_needs_w11`→`relNeedsW11`, `rel_stale_token`→`relStaleToken`,
`rel_validated`→`relValidated`.  (None of these names is in `notes/weak-port-dupnames.json`.)

**Not ported:** `axlogΣ`, `subG_axlogG` (deviation 3: no `gFunctors` lists / `subG` in
iris-lean; no Lean weak file builds a Σ list), `wclass_eq_dec` (deviation 5), the §6
`Print Assumptions` audit (the lint bans `sorry`/`axiom`).

**Statements checked** (diffed against Rocq by hand): all; the changed spellings are the
deviations above.
-/
import Weak.AxGraphWit
import Weak.AxGraphCat
import Weak.AxGraphDec
import Weak.AxGraph
import Weak.WeakRvwmoGraph
import Weak.WeakRvwmoLock
import Weak.WeakRvwmoAcyc
import Weak.WeakLitmus
import MachCSL.StdppMap
import MachCSL.StdppSet
import MachCSL.QpLemmas
import Iris.Algebra.Heap
import Iris.Algebra.Lib.MonoList
import Iris.BI.Lib.MonoList
import Iris.BI.Lib.Fractional
import Iris.BI.BigOp.BigSepSet
import Iris.Instances.IProp
import Iris.ProofMode

namespace Weak

open Iris Iris.BI Iris.Std MachCSL MachCSL.Stdpp

/-! ## 1. The generic per-byte monotone log -/

/-- ONE ghost name for ALL bytes: a finite map from the byte address to a `MonoList`.  A
byte's log is a singleton of that map (Rocq notation `axlogR A`; a NOTATION here too, since an
applied abbreviation `AxlogR A` would unify as `?M ?V` with `M := AxlogR`, `V := A`, the
`MachCSL.GMapF` pitfall). -/
notation "AxlogR " A:max => GMapF Int (MonoList (DiscreteO A))

/-- The functor of `AxlogR` (deviation 3). -/
abbrev AxlogRF (A : Type) : COFE.OFunctorPre := constOF (AxlogR A)

class AxlogG (GF : BundledGFunctors) (A : Type) where
  axlogInG : ElemG GF (AxlogRF A)

attribute [reducible, instance] AxlogG.axlogInG

section log

variable {GF : BundledGFunctors} {A : Type} [AxlogG GF A]

/-- The authority on byte `a`'s log, at fraction `q`. -/
def logAuth (γ : GName) (a : Int) (q : Qp) (L : List A) : IProp GF :=
  iOwn (F := AxlogRF A) γ
    (PartialMap.singleton a (MonoList.auth (DFrac.own q) (L.map DiscreteO.mk)) : AxlogR A)

/-- A snapshot: a prefix of the auth, persistent. -/
def logSnap (γ : GName) (a : Int) (L : List A) : IProp GF :=
  iOwn (F := AxlogRF A) γ (PartialMap.singleton a (MonoList.lb (L.map DiscreteO.mk)) : AxlogR A)

instance logSnap_persistent (γ : GName) (a : Int) (L : List A) :
    Persistent (logSnap (GF := GF) γ a L) := by
  unfold logSnap; infer_instance

instance logAuth_timeless (γ : GName) (a : Int) (q : Qp) (L : List A) :
    Timeless (logAuth (GF := GF) γ a q L) := by
  unfold logAuth; infer_instance

instance logSnap_timeless (γ : GName) (a : Int) (L : List A) :
    Timeless (logSnap (GF := GF) γ a L) := by
  unfold logSnap; infer_instance

open Iris.Algebra in
/-- ALLOCATION: every byte of a finite set gets the full authority on the same initial log
`L0` (per-byte seeds: one `logAppend` each). -/
theorem logAlloc (X : GSet Int) (L0 : List A) :
    ⊢@{IProp GF} |==> ∃ γ, [∗set] a ∈ X, logAuth γ a 1 L0 := by
  have hv : ✓ ([^ CMRA.op set] k ∈ X,
      (PartialMap.singleton k (MonoList.auth (DFrac.own 1) (L0.map DiscreteO.mk)) : AxlogR A)) := by
    rw [Heap.bigOpS_ofSet]
    intro k
    by_cases hk : k ∈ X
    · rw [LawfulFiniteMap.get?_ofSet_of_mem hk]
      exact MonoList.auth_valid _
    · rw [LawfulFiniteMap.get?_ofSet_of_not_mem hk]
      trivial
  refine (iOwn_alloc (F := AxlogRF A) _ hv).trans (bupd_mono (exists_mono fun γ => ?_))
  unfold logAuth
  exact @bigOpS_iOwn_entail GF (AxlogRF A) OFunctor.constOF_URFunctorContractive AxlogG.axlogInG _ _ _ γ
    (fun k => (PartialMap.singleton k (MonoList.auth (DFrac.own 1) (L0.map DiscreteO.mk)) :
      AxlogR A)) X

/-- A fraction is valid. -/
theorem logValid (γ : GName) (a : Int) (q : Qp) (L : List A) :
    logAuth (GF := GF) γ a q L ⊢ ⌜q ≤ 1⌝ := by
  unfold logAuth
  iintro H
  icases iOwn_cmraValid $$ H with %hv
  ipureintro
  exact (MonoList.auth_dfrac_valid _ _).mp (Heap.singleton_valid_iff.mp hv)

/-- FRACTIONS AGREE on the log. -/
theorem logAgree (γ : GName) (a : Int) (q1 q2 : Qp) (L1 L2 : List A) :
    logAuth (GF := GF) γ a q1 L1 ∗ logAuth γ a q2 L2 ⊢ ⌜L1 = L2 ∧ q1 + q2 ≤ 1⌝ := by
  unfold logAuth
  iintro ⟨H1, H2⟩
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %hv
  ipureintro
  rw [Heap.singleton_op_singleton, Heap.singleton_valid_iff] at hv
  obtain ⟨hdq, hl⟩ := (MonoList.auth_dfrac_op_valid _ _ _ _).mp hv
  exact ⟨MonoList.map_mk_inj hl, hdq⟩

/-- SPLIT / JOIN. -/
theorem logAuthOp (γ : GName) (a : Int) (q1 q2 : Qp) (L : List A) :
    logAuth (GF := GF) γ a (q1 + q2) L ⊣⊢ logAuth γ a q1 L ∗ logAuth γ a q2 L := by
  unfold logAuth
  have h : (MonoList.auth (DFrac.own (q1 + q2)) (L.map DiscreteO.mk)) =
      MonoList.auth (DFrac.own q1) (L.map DiscreteO.mk) •
        MonoList.auth (DFrac.own q2) (L.map DiscreteO.mk) :=
    MonoList.auth_dfrac_op (DFrac.own q1) (DFrac.own q2) _
  rw [h, ← Heap.singleton_op_singleton]
  exact iOwn_op

instance logAuth_fractional (γ : GName) (a : Int) (L : List A) :
    Fractional (fun q => logAuth (GF := GF) γ a q L) where
  fractional p q := logAuthOp γ a p q L

instance logAuth_as_fractional (γ : GName) (a : Int) (q : Qp) (L : List A) {ioΦ ioq : Iris.ProofMode.InOut} :
    AsFractional (logAuth (GF := GF) γ a q L) ioΦ (fun q => logAuth γ a q L) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := inferInstance

/-- Taking a snapshot. -/
theorem logSnapGet (γ : GName) (a : Int) (q : Qp) (L : List A) :
    logAuth (GF := GF) γ a q L ⊢ logSnap γ a L := by
  unfold logAuth logSnap
  exact iOwn_mono (Heap.singleton_inc_singleton_mono (MonoList.included _ _))

/-- A snapshot weakens to any of its prefixes. -/
theorem logSnapMono (γ : GName) (a : Int) (L L' : List A) (h : L' <+: L) :
    logSnap (GF := GF) γ a L ⊢ logSnap γ a L' := by
  unfold logSnap
  exact iOwn_mono (Heap.singleton_inc_singleton_mono (MonoList.lb_mono (h.map _)))

/-- THE PREFIX FACT: a snapshot is a prefix of any fraction's log. -/
theorem logSnapPrefix (γ : GName) (a : Int) (q : Qp) (L L' : List A) :
    logAuth (GF := GF) γ a q L ∗ logSnap γ a L' ⊢ ⌜L' <+: L⌝ := by
  unfold logAuth logSnap
  iintro ⟨H1, H2⟩
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %hv
  ipureintro
  rw [Heap.singleton_op_singleton, Heap.singleton_valid_iff] at hv
  exact MonoList.map_mk_prefix ((MonoList.both_dfrac_valid _ _ _).mp hv).2

/-- ... hence membership and positions transfer from the snapshot to the auth. -/
theorem logSnapElem (γ : GName) (a : Int) (q : Qp) (L L' : List A) (x : A) (hx : x ∈ L') :
    logAuth (GF := GF) γ a q L ∗ logSnap γ a L' ⊢ ⌜x ∈ L⌝ := by
  refine (logSnapPrefix γ a q L L').trans ?_
  iintro %h
  ipureintro
  exact h.subset hx

theorem logSnapLookup (γ : GName) (a : Int) (q : Qp) (L L' : List A) (i : Nat) (x : A)
    (hx : L'[i]? = some x) :
    logAuth (GF := GF) γ a q L ∗ logSnap γ a L' ⊢ ⌜L[i]? = some x⌝ := by
  refine (logSnapPrefix γ a q L L').trans ?_
  iintro %h
  ipureintro
  exact MonoList.prefix_getElem? h hx

/-- GROWTH needs the full fraction. -/
theorem logUpdate (γ : GName) (a : Int) (L L' : List A) (h : L <+: L') :
    logAuth (GF := GF) γ a 1 L ⊢ |==> logAuth γ a 1 L' := by
  unfold logAuth
  exact iOwn_update (Heap.singleton_update (MonoList.update _ (h.map _)))

theorem logAppend (γ : GName) (a : Int) (L : List A) (x : A) :
    logAuth (GF := GF) γ a 1 L ⊢ |==> logAuth γ a 1 (L ++ [x]) :=
  logUpdate γ a L (L ++ [x]) (List.prefix_append L [x])

end log

/-! ## 2. THE HISTORY ghost: the log at `Geid × BitVec 8` -/

/-- A history entry: the write event and the byte it wrote (Rocq notation `hent`). -/
abbrev Hent : Type := Geid × BitVec 8

/-- The `Φ_own`-deposit form of a snapshot (`last H_w = (w, v)`) yields the membership
`ownedReadGhost` consumes.  PURE. -/
theorem histSnapLastIn (H' : List Hent) (w : Geid) (v : BitVec 8) :
    H'.getLast? = some (w, v) → w ∈ H'.map Prod.fst := by
  intro hl
  obtain ⟨H0, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  simp

section hist

variable {GF : BundledGFunctors} [AxlogG GF Hent]

def histAuth (γ : GName) (a : Int) (q : Qp) (H : List Hent) : IProp GF := logAuth γ a q H
def histSnap (γ : GName) (a : Int) (H : List Hent) : IProp GF := logSnap γ a H

instance histSnap_persistent (γ : GName) (a : Int) (H : List Hent) :
    Persistent (histSnap (GF := GF) γ a H) := by
  unfold histSnap; infer_instance

instance histAuth_timeless (γ : GName) (a : Int) (q : Qp) (H : List Hent) :
    Timeless (histAuth (GF := GF) γ a q H) := by
  unfold histAuth; infer_instance

instance histSnap_timeless (γ : GName) (a : Int) (H : List Hent) :
    Timeless (histSnap (GF := GF) γ a H) := by
  unfold histSnap; infer_instance

instance histAuth_fractional (γ : GName) (a : Int) (H : List Hent) :
    Fractional (fun q => histAuth (GF := GF) γ a q H) where
  fractional p q := logAuthOp γ a p q H

instance histAuth_as_fractional (γ : GName) (a : Int) (q : Qp) (H : List Hent)
    {ioΦ ioq : Iris.ProofMode.InOut} :
    AsFractional (histAuth (GF := GF) γ a q H) ioΦ (fun q => histAuth γ a q H) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := inferInstance

theorem histAlloc (X : GSet Int) (H0 : List Hent) :
    ⊢@{IProp GF} |==> ∃ γ, [∗set] a ∈ X, histAuth γ a 1 H0 :=
  logAlloc X H0

theorem histAgree (γ : GName) (a : Int) (q1 q2 : Qp) (H1 H2 : List Hent) :
    histAuth (GF := GF) γ a q1 H1 ∗ histAuth γ a q2 H2 ⊢ ⌜H1 = H2 ∧ q1 + q2 ≤ 1⌝ :=
  logAgree γ a q1 q2 H1 H2

theorem histSplit (γ : GName) (a : Int) (q1 q2 : Qp) (H : List Hent) :
    histAuth (GF := GF) γ a (q1 + q2) H ⊢ histAuth γ a q1 H ∗ histAuth γ a q2 H :=
  (logAuthOp γ a q1 q2 H).1

theorem histJoin (γ : GName) (a : Int) (q1 q2 : Qp) (H : List Hent) :
    histAuth (GF := GF) γ a q1 H ∗ histAuth γ a q2 H ⊢ histAuth γ a (q1 + q2) H :=
  (logAuthOp γ a q1 q2 H).2

theorem histSnapGet (γ : GName) (a : Int) (q : Qp) (H : List Hent) :
    histAuth (GF := GF) γ a q H ⊢ histSnap γ a H :=
  logSnapGet γ a q H

theorem histSnapPrefix (γ : GName) (a : Int) (q : Qp) (H H' : List Hent) :
    histAuth (GF := GF) γ a q H ∗ histSnap γ a H' ⊢ ⌜H' <+: H⌝ :=
  logSnapPrefix γ a q H H'

theorem histAppend (γ : GName) (a : Int) (H : List Hent) (x : Hent) :
    histAuth (GF := GF) γ a 1 H ⊢ |==> histAuth γ a 1 (H ++ [x]) :=
  logAppend γ a H x

/-- A write mentioned by a snapshot is in the auth's history. -/
theorem histSnapIn (γ : GName) (a : Int) (q : Qp) (H H' : List Hent) (w : Geid)
    (hw : w ∈ H'.map Prod.fst) :
    histAuth (GF := GF) γ a q H ∗ histSnap γ a H' ⊢ ⌜w ∈ H.map Prod.fst⌝ := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
  refine (logSnapElem γ a q H H' p hp).trans ?_
  iintro %h
  ipureintro
  exact List.mem_map_of_mem h

/-- THE KEY REFUTATION: a snapshot cannot mention a write the auth does not — growth needs the
full fraction, so no other party can have appended `w` while this fraction is out. -/
theorem histSnapAfterLast (γ : GName) (a : Int) (q : Qp) (H H' : List Hent) (w : Geid)
    (hw : w ∈ H'.map Prod.fst) (hnw : w ∉ H.map Prod.fst) :
    histAuth (GF := GF) γ a q H ∗ histSnap γ a H' ⊢ iprop(False) := by
  refine (histSnapIn γ a q H H' w hw).trans ?_
  iintro %h
  exact absurd h hnw

end hist

/-! ## 3. THE CLASS/EPOCH ghost: the log at `Wclass × Option Geid`

The epoch IS the index of the log: entry `ep` is `(class of epoch ep, boundary event that
opened it)`; epoch 0 (boot) has boundary `none`. -/

inductive Wclass where
  | CLown
  | CLro
  | CLlock
  | CLflag
  deriving DecidableEq

/-- Rocq notation `cent`. -/
abbrev Cent : Type := Wclass × Option Geid

section cls

variable {GF : BundledGFunctors} [AxlogG GF Cent]

/-- The whole epoch log (the primitive); ... -/
def clsLog (γ : GName) (a : Int) (q : Qp) (L : List Cent) : IProp GF := logAuth γ a q L

/-- ... its CURRENT view: class `c`, epoch `ep`, boundary `b`; ... -/
def clsAuth (γ : GName) (a : Int) (q : Qp) (c : Wclass) (ep : Nat) (b : Option Geid) :
    IProp GF :=
  iprop(∃ L, clsLog γ a q L ∗ ⌜L.length = ep + 1 ∧ L[ep]? = some (c, b)⌝)

/-- ... and a snapshot of SOME epoch, past or current. -/
def clsSnap (γ : GName) (a : Int) (c : Wclass) (ep : Nat) (b : Option Geid) : IProp GF :=
  iprop(∃ L', logSnap γ a L' ∗ ⌜L'[ep]? = some (c, b)⌝)

instance clsSnap_persistent (γ : GName) (a : Int) (c : Wclass) (ep : Nat) (b : Option Geid) :
    Persistent (clsSnap (GF := GF) γ a c ep b) := by
  unfold clsSnap; infer_instance

instance clsAuth_timeless (γ : GName) (a : Int) (q : Qp) (c : Wclass) (ep : Nat)
    (b : Option Geid) : Timeless (clsAuth (GF := GF) γ a q c ep b) := by
  unfold clsAuth clsLog; infer_instance

instance clsSnap_timeless (γ : GName) (a : Int) (c : Wclass) (ep : Nat) (b : Option Geid) :
    Timeless (clsSnap (GF := GF) γ a c ep b) := by
  unfold clsSnap; infer_instance

theorem clsAlloc (X : GSet Int) (c0 : Wclass) :
    ⊢@{IProp GF} |==> ∃ γ, [∗set] a ∈ X, clsAuth γ a 1 c0 0 none := by
  have hm : ∀ (γ : GName) (a : Int),
      logAuth (GF := GF) γ a 1 [((c0, none) : Cent)] ⊢ clsAuth γ a 1 c0 0 none := by
    intro γ a
    unfold clsAuth clsLog
    iintro H
    iexists [((c0, none) : Cent)]
    isplitl [H]
    · iexact H
    · ipureintro
      exact ⟨rfl, rfl⟩
  imod logAlloc (GF := GF) X [((c0, none) : Cent)] with ⟨%γ, H⟩
  imodintro
  iexists γ
  iapply BigSepS.bigSepS_mono_of_forall (fun a => hm γ a)
  iexact H

/-- Fractions agree on (class, epoch, boundary). -/
theorem clsAgree (γ : GName) (a : Int) (q1 q2 : Qp) (c : Wclass) (ep : Nat) (b : Option Geid)
    (c' : Wclass) (ep' : Nat) (b' : Option Geid) :
    clsAuth (GF := GF) γ a q1 c ep b ∗ clsAuth γ a q2 c' ep' b' ⊢ ⌜c = c' ∧ ep = ep' ∧ b = b'⌝ := by
  unfold clsAuth clsLog
  iintro ⟨⟨%L1, H1, %h1⟩, ⟨%L2, H2, %h2⟩⟩
  icases logAgree γ a q1 q2 L1 L2 $$ [$H1 $H2] with %⟨hL, -⟩
  ipureintro
  subst hL
  have hep : ep = ep' := by omega
  subst hep
  rw [h1.2] at h2
  cases h2.2
  exact ⟨rfl, rfl, rfl⟩

theorem clsAuthOp (γ : GName) (a : Int) (q1 q2 : Qp) (c : Wclass) (ep : Nat) (b : Option Geid) :
    clsAuth (GF := GF) γ a (q1 + q2) c ep b ⊣⊢ clsAuth γ a q1 c ep b ∗ clsAuth γ a q2 c ep b := by
  unfold clsAuth clsLog
  constructor
  · iintro ⟨%L, H, %hL⟩
    icases (logAuthOp γ a q1 q2 L).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists L
      isplitl [H1]
      · iexact H1
      · ipureintro; exact hL
    · iexists L
      isplitl [H2]
      · iexact H2
      · ipureintro; exact hL
  · iintro ⟨⟨%L1, H1, %hL1⟩, ⟨%L2, H2, %hL2⟩⟩
    icases (BI.and_intro (logAgree γ a q1 q2 L1 L2) .rfl) $$ [$H1 $H2] with ⟨%hL, H1, H2⟩
    obtain ⟨hL, -⟩ := hL
    subst hL
    iexists L1
    isplitl [H1 H2]
    · iapply (logAuthOp γ a q1 q2 L1).2
      isplitl [H1]
      · iexact H1
      · iexact H2
    · ipureintro; exact hL1

instance clsAuth_fractional (γ : GName) (a : Int) (c : Wclass) (ep : Nat) (b : Option Geid) :
    Fractional (fun q => clsAuth (GF := GF) γ a q c ep b) where
  fractional p q := clsAuthOp γ a p q c ep b

instance clsAuth_as_fractional (γ : GName) (a : Int) (q : Qp) (c : Wclass) (ep : Nat)
    (b : Option Geid) {ioΦ ioq : Iris.ProofMode.InOut} :
    AsFractional (clsAuth (GF := GF) γ a q c ep b) ioΦ (fun q => clsAuth γ a q c ep b) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := inferInstance

theorem clsSnapGet (γ : GName) (a : Int) (q : Qp) (c : Wclass) (ep : Nat) (b : Option Geid) :
    clsAuth (GF := GF) γ a q c ep b ⊢ clsSnap γ a c ep b := by
  unfold clsAuth clsSnap clsLog
  iintro ⟨%L, H, %⟨_, he⟩⟩
  ihave Hs := logSnapGet γ a q L $$ H
  iexists L
  isplitl [Hs]
  · iexact Hs
  · ipureintro; exact he

/-- EXACTLY WHAT A SNAPSHOT PROVES: the auth's log has `(c', b')` at index `ep'` — epoch `ep'`
existed with that class and boundary. -/
theorem clsSnapLookup (γ : GName) (a : Int) (q : Qp) (L : List Cent) (c' : Wclass) (ep' : Nat)
    (b' : Option Geid) :
    clsLog (GF := GF) γ a q L ∗ clsSnap γ a c' ep' b' ⊢ ⌜L[ep']? = some (c', b')⌝ := by
  unfold clsSnap clsLog
  iintro ⟨H, ⟨%L', Hs, %he⟩⟩
  icases logSnapLookup γ a q L L' ep' (c', b') he $$ [$H $Hs] with %h
  ipureintro
  exact h

/-- The two consumable readings: a snapshot is of a PAST OR CURRENT epoch, and at the current
epoch it agrees.  A snapshot of a past epoch says nothing about the CURRENT class. -/
theorem clsSnapLe (γ : GName) (a : Int) (q : Qp) (c : Wclass) (ep : Nat) (b : Option Geid)
    (c' : Wclass) (ep' : Nat) (b' : Option Geid) :
    clsAuth (GF := GF) γ a q c ep b ∗ clsSnap γ a c' ep' b' ⊢
      ⌜ep' ≤ ep ∧ (ep' = ep → c' = c ∧ b' = b)⌝ := by
  unfold clsAuth
  iintro ⟨⟨%L, H, %⟨hl, he⟩⟩, Hs⟩
  icases clsSnapLookup γ a q L c' ep' b' $$ [$H $Hs] with %he'
  ipureintro
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp he'
  refine ⟨by omega, fun heq => ?_⟩
  subst heq
  rw [he] at he'
  cases he'
  exact ⟨rfl, rfl⟩

/-- A CLASS CHANGE: full fraction, bumps the epoch, records the boundary event `b'` of the new
epoch. -/
theorem clsChange (γ : GName) (a : Int) (c : Wclass) (ep : Nat) (b : Option Geid) (c' : Wclass)
    (b' : Option Geid) :
    clsAuth (GF := GF) γ a 1 c ep b ⊢ |==> clsAuth γ a 1 c' (ep + 1) b' := by
  unfold clsAuth clsLog
  iintro ⟨%L, H, %⟨hl, _⟩⟩
  imod logAppend γ a L ((c', b') : Cent) $$ H with H
  imodintro
  iexists L ++ [((c', b') : Cent)]
  isplitl [H]
  · iexact H
  · ipureintro
    refine ⟨by simp [hl], ?_⟩
    rw [List.getElem?_append_right (by omega), hl]
    simp

end cls

/-! ## 4. THE VALIDATION LEMMA (the L2 read rule's core)

A read `r` of byte `a` by a hart holding ANY fraction of the byte's history `H` (a
write-validated, gmo-chained record of same-byte writes whose last entry is visible to `r`).
The gmo-coverage hypothesis of `AxGraphCat.ownedReadCatCov` — every same-byte write gmo-before
`r` is in `H` — is discharged from GHOST STATE: the base logic supplies, for each such write
`w`, a snapshot mentioning `w` (the `Φ_own` content of `w`'s protocol slot, readable because
`w` is in the gmo-prefix); `histSnapIn` puts `w` into `H`.  Then `r`'s rf-source is the last
entry of `H` and the value read is the value it wrote.

Everything about the GRAPH is a pure hypothesis; everything about OTHER harts' writes comes
through the ghost. -/

section validation

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem ownedReadGhost (GD : Gdexec) (a : Int) (r : Geid) (γ : GName) (q : Qp)
    (H : List Hent) (wl : Geid) (vl : BitVec 8) :
    rvwmoCatConsistent GD →
    -- `H` records writes to byte `a` with the bytes they wrote
    (∀ p, p ∈ H → gwritesByte GD.gdG p.1 a p.2) →
    -- ... GMO-chained (the design's token invariant; weaker than `obCatChain`: a same-byte
    -- history that is merely gmo-increasing is automatically CO-chained, which is what the
    -- proof derives to reach `ownedReadCatSnoc`'s `obCatChain`)
    chainWith (gmoLt GD.gdG) (H.map Prod.fst) →
    -- ... containing the hart's own po-earlier same-byte writes (rule 1)
    (∀ w v, gwritesByte GD.gdG w a v → WeakRvwmoGraph.gpo GD.gdG w r → w ∈ H.map Prod.fst) →
    -- ... whose last entry is visible to `r`
    H.getLast? = some (wl, vl) →
    gvisible GD.gdG wl r →
    -- `r` reads byte `a`
    (∃ t v, greadsByte GD.gdG r a t v) →
    histAuth (GF := GF) γ a q H ∗
      -- THE GHOST COVERAGE: a snapshot for every same-byte write gmo-before `r`
      (∀ w v, ⌜gwritesByte GD.gdG w a v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ a H') ⊢
    ⌜grfAt GD.gdG a wl r ∧ ∀ t v, greadsByte GD.gdG r a t v → v = vl⌝ := by
  intro hcons hwr hch hown hlast hvis hrd
  iintro ⟨Hauth, Hsn⟩
  -- the gmo-coverage, from the ghost
  ihave %hcov : ⌜∀ w v, gwritesByte GD.gdG w a v → gmoLt GD.gdG w r → w ∈ H.map Prod.fst⌝ $$
      [Hauth Hsn]
  · iapply BI.pure_forall.2
    iintro %w
    iapply BI.pure_forall.2
    iintro %v
    iapply BI.pure_wand.1
    iintro %hw
    iapply BI.pure_wand.1
    iintro %hmo
    icases Hsn $$ %w %v %hw %hmo with ⟨%H', %hin, Hs⟩
    icases histSnapIn γ a q H H' w hin $$ [$Hauth $Hs] with %h
    ipureintro
    exact h
  ipureintro
  have ⟨hwf, _, hlv, _⟩ := hcons
  obtain ⟨H0, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  have hfst : (H0 ++ [(wl, vl)]).map Prod.fst = H0.map Prod.fst ++ [wl] := by simp
  rw [hfst] at hch hown hcov
  have hwr' : ∀ w, w ∈ H0.map Prod.fst ++ [wl] → ∃ v, gwritesByte GD.gdG w a v := by
    intro w hw
    rw [← hfst] at hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    exact ⟨p.2, hwr p hp⟩
  -- `hch` is only gmo-chained; derive the `obCatChain` `ownedReadCatSnoc` needs from it — a
  -- gmo-chained same-byte history is co-chained, and `gco` is one of `gobrCat`'s own arms.
  have hobch : obCatChain GD (H0.map Prod.fst ++ [wl]) := by
    intro i w1 w2 hi1 hi2
    have hpos := hch i w1 w2 hi1 hi2
    obtain ⟨v1, hwb1⟩ := hwr' w1 (List.mem_of_getElem? hi1)
    obtain ⟨v2, hwb2⟩ := hwr' w2 (List.mem_of_getElem? hi2)
    apply gobCatStep
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, v1, v2, hwb1, hwb2, ?_⟩)))
    exact (gwixGposLt GD.gdG w1 w2 hwf.1 (gwritesByteGwrites _ _ _ _ hwf hwb1)
      (gwritesByteGwrites _ _ _ _ hwf hwb2)).2 hpos.2.2
  have hwl : gwritesByte GD.gdG wl a vl := hwr (wl, vl) (by simp)
  have hrf : grfAt GD.gdG a wl r := by
    refine ownedReadCatSnoc GD (H0.map Prod.fst) wl a r hcons hwr' hobch ?_ hvis hrd
    rintro w v hwb (hmo | hpo)
    · exact hcov w v hwb hmo
    · exact hown w v hwb hpo
  exact ⟨hrf, fun t v hrdv => grfAtValue _ _ _ _ _ _ _ hlv hrf hrdv hwl⟩

end validation

/-! ## 5. NON-VACUITY -/

/-! ### 5.1 The history ghost on a concrete run

Hart 0 allocates byte 0's history, writes twice ((0,0) then (0,1)), takes a snapshot in
between.  A snapshot naming hart 1's write (1,0) — which never appended — is refuted against
ANY fraction. -/

def Hdemo : List Hent := [((0, 0), b1), ((0, 1), b2)]

section histDemo

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem histDemo :
    ⊢@{IProp GF} |==> ∃ γ, histAuth γ 0 1 Hdemo ∗ histSnap γ 0 [((0, 0), b1)] := by
  unfold histAuth histSnap
  imod logAlloc (GF := GF) ({0} : GSet Int) ([] : List Hent) with ⟨%γ, H⟩
  ihave H := BigSepS.bigSepS_singleton.1 $$ H
  imod logUpdate γ 0 ([] : List Hent) [((0, 0), b1)] (List.nil_prefix) $$ H with H
  ihave #Hs := logSnapGet γ 0 1 _ $$ H
  imod logUpdate γ 0 [((0, 0), b1)] Hdemo ⟨[((0, 1), b2)], rfl⟩ $$ H with H
  imodintro
  iexists γ
  isplitl [H]
  · iexact H
  · iexact Hs

theorem histDemoRogue (γ : GName) (q : Qp) (H' : List Hent) (hin : (1, 0) ∈ H'.map Prod.fst) :
    histAuth (GF := GF) γ 0 q Hdemo ∗ histSnap γ 0 H' ⊢ iprop(False) :=
  histSnapAfterLast γ 0 q Hdemo H' (1, 0) hin (by decide)

/-- ... while the honest snapshot is a prefix, as it should be. -/
theorem histDemoPrefix (γ : GName) (q : Qp) :
    histAuth (GF := GF) γ 0 q Hdemo ∗ histSnap γ 0 [((0, 0), b1)] ⊢
      ⌜[((0, 0), b1)] <+: Hdemo⌝ :=
  histSnapPrefix γ 0 q Hdemo _

end histDemo

/-! ### 5.2 The class/epoch ghost: a class change and a stale snapshot -/

section clsDemo

variable {GF : BundledGFunctors} [AxlogG GF Cent]

/-- Byte 0 boots `CLown`; a snapshot of epoch 0 is taken; the class changes to `CLlock` at
boundary write `(0,5)`.  The old snapshot still proves "epoch 0 was `CLown`" and is NOT of the
current epoch. -/
theorem clsDemo :
    ⊢@{IProp GF} |==> ∃ γ, clsAuth γ 0 1 .CLlock 1 (some (0, 5)) ∗ clsSnap γ 0 .CLown 0 none := by
  imod clsAlloc (GF := GF) ({0} : GSet Int) .CLown with ⟨%γ, H⟩
  ihave H := BigSepS.bigSepS_singleton.1 $$ H
  ihave #Hs := clsSnapGet γ 0 1 .CLown 0 none $$ H
  imod clsChange γ 0 .CLown 0 none .CLlock (some (0, 5)) $$ H with H
  imodintro
  iexists γ
  isplitl [H]
  · iexact H
  · iexact Hs

theorem clsDemoStale (γ : GName) (q : Qp) :
    clsAuth (GF := GF) γ 0 q .CLlock 1 (some (0, 5)) ∗ clsSnap γ 0 .CLown 0 none ⊢
      ⌜0 ≤ 1 ∧ (0 = 1 → Wclass.CLown = .CLlock ∧ (none : Option Geid) = some (0, 5))⌝ :=
  clsSnapLe γ 0 q .CLlock 1 (some (0, 5)) .CLown 0 none

/-- A snapshot claiming a FUTURE epoch is refuted. -/
theorem clsDemoFuture (γ : GName) (q : Qp) (c : Wclass) (b : Option Geid) :
    clsAuth (GF := GF) γ 0 q .CLlock 1 (some (0, 5)) ∗ clsSnap γ 0 c 2 b ⊢ iprop(False) := by
  refine (clsSnapLe γ 0 q .CLlock 1 (some (0, 5)) c 2 b).trans ?_
  iintro %⟨hle, _⟩
  exact absurd hle (by decide)

end clsDemo

/-! ### 5.3 The validation lemma on `AxGraphWit.rel` (release-then-read)

    H0: W a=1 (0,0); fence rw,w (0,1); W lock=0 (0,2); R a (0,3).
    H1: RMW.aq lock (1,0); W a=2 (1,1).
    gmo = [W0a; W0lock; RMW1; W1a; R0a]; R0a reads W1a (`relRf`).

THE STORY.  Hart 0 wrote byte 0 and holds its history `[((0,0),b1)]`.  It releases the lock;
hart 1 acquires, RE-OWNS byte 0 and writes (1,1).  Under the design, hart 1's write needs the
FULL token (growth needs `q = 1`), so the token moved through the lock protocol and hart 0 has
NO fraction left; its plain read (0,3) is racy.

- `relNeedsW11`: byte 0's write (1,1) is gmo-before (0,3), so the validation lemma's coverage
  hypothesis at (0,3) DEMANDS a snapshot naming (1,1).
- `relStaleToken`: were hart 0 still holding a fraction at its pre-release history, no such
  snapshot could exist — so the lemma cannot be invoked with the stale token, and there is no
  ghost route to the FALSE conclusion `grfAt 0 (0,0) (0,3)` (`relRf`).
- `relValidated`: a holder of a fraction at the RE-OWNER's history `[((0,0),b1); ((1,1),b2)]`
  validates (0,3) through the lemma, and the verdict is `relRf`'s: rf-source (1,1), value `b2`.
  In `rel` itself no hart holds that fraction at (0,3) (no acquire on hart 0's path), which is
  exactly the design's "token at the re-owner" requirement. -/

def Hrel : List Hent := [((0, 0), b1), ((1, 1), b2)]

/-- Every write to byte 0 in `rel` is (0,0) or (1,1) — computed over the event list. -/
theorem relWrites0 (w : Geid) (v : BitVec 8) :
    gwritesByte AxGraphWit.rel.gdG w 0 v → w = (0, 0) ∨ w = (1, 1) := by
  intro hw
  have he := gwritesByteGevents _ _ _ _ hw
  have ha : gwaB AxGraphWit.rel.gdG w 0 = true := (gwaBSpec _ _ _).2 ⟨v, hw⟩
  have key : ∀ e ∈ gevents AxGraphWit.rel.gdG, gwaB AxGraphWit.rel.gdG e 0 = true →
      e = (0, 0) ∨ e = (1, 1) := by decide +kernel
  exact key w he ha

/-- The coverage hypothesis at (0,3) names hart 1's write. -/
theorem relNeedsW11 :
    gwritesByte AxGraphWit.rel.gdG (1, 1) 0 b2 ∧
    gmoLt AxGraphWit.rel.gdG (1, 1) (0, 3) ∧
    (1, 1) ∉ ([((0, 0), b1)] : List Hent).map Prod.fst :=
  ⟨(gwbBSpec _ _ _ _).1 (by decide +kernel), (gmoLtBSpec _ _ _).1 (by decide +kernel),
    by decide⟩

section relDemo

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- A fraction at the PRE-RELEASE history refutes any snapshot the coverage hypothesis at
(0,3) could supply. -/
theorem relStaleToken (γ : GName) (q : Qp) (H' : List Hent) (hin : (1, 1) ∈ H'.map Prod.fst) :
    histAuth (GF := GF) γ 0 q [((0, 0), b1)] ∗ histSnap γ 0 H' ⊢ iprop(False) :=
  histSnapAfterLast γ 0 q _ H' (1, 1) hin relNeedsW11.2.2

/-- With the re-owner's history, the lemma yields `relRf`'s verdict. -/
theorem relValidated (γ : GName) (q : Qp) :
    histAuth (GF := GF) γ 0 q Hrel ∗ histSnap γ 0 Hrel ⊢
      ⌜grfAt AxGraphWit.rel.gdG 0 (1, 1) (0, 3) ∧
        ∀ t v, greadsByte AxGraphWit.rel.gdG (0, 3) 0 t v → v = b2⌝ := by
  have hwr : ∀ p, p ∈ Hrel → gwritesByte AxGraphWit.rel.gdG p.1 0 p.2 := by
    intro p hp
    simp only [Hrel, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact (gwbBSpec _ _ _ _).1 (by decide +kernel)
  -- GMO-chained only — the single step (0,0) -> (1,1) is gmo-before, which is all
  -- `ownedReadGhost` asks of the chain hypothesis.
  have hch : chainWith (gmoLt AxGraphWit.rel.gdG) (Hrel.map Prod.fst) := by
    intro i w1 w2 h1 h2
    rcases i with _ | _ | i
    · have e1 : w1 = (0, 0) := by simpa [Hrel] using h1.symm
      have e2 : w2 = (1, 1) := by simpa [Hrel] using h2.symm
      subst e1 e2
      exact (gmoLtBSpec _ _ _).1 (by decide +kernel)
    · simp [Hrel] at h2
    · simp [Hrel] at h1
  have hown : ∀ w v, gwritesByte AxGraphWit.rel.gdG w 0 v →
      WeakRvwmoGraph.gpo AxGraphWit.rel.gdG w (0, 3) → w ∈ Hrel.map Prod.fst := by
    intro w v hw hpo
    rcases relWrites0 w v hw with rfl | rfl
    · simp [Hrel]
    · exact absurd hpo.1 (by decide)
  have hvis : gvisible AxGraphWit.rel.gdG (1, 1) (0, 3) :=
    Or.inl ((gmoLtBSpec _ _ _).1 (by decide +kernel))
  have hrd : ∃ t v, greadsByte AxGraphWit.rel.gdG (0, 3) 0 t v :=
    ⟨4, b2, (grbBSpec _ _ _ _ _).1 (by decide +kernel)⟩
  iintro ⟨Ha, #Hs⟩
  iapply ownedReadGhost AxGraphWit.rel 0 (0, 3) γ q Hrel (1, 1) b2 relCat hwr hch hown rfl hvis
    hrd
  isplitl [Ha]
  · iexact Ha
  · iintro %w %v %hw %hmo
    iexists Hrel
    isplit
    · ipureintro
      rcases relWrites0 w v hw with rfl | rfl <;> simp [Hrel]
    · iexact Hs

end relDemo

end Weak
