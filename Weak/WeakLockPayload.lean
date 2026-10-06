/-
Weak: **a WORKED lock payload** — a list of items, each owning memory, nested three
definitions deep, mixed with pure facts and ghost state, written as a `VProp` with the
ordinary `[∗list]`; the boundary lemmas (`tableAcquire`/`tableRelease`), the DERIVED
decomposition through `cobj` (`itemObj`/`itemsObj`/`tableObj`), the frozen form the invariant
sees (`tablePub`), and the round trip (`tableRoundTrip`).

Rocq: `iris/WeakLockPayload.v` @ xxvzwolszwmp.

Rocq header (in substance).  THE QUESTION: does writing a real payload as a `vProp` cost
anything — in particular, does `big_sepL` need redefining, or the payload reshaping?  THE
ANSWER, checked rather than asserted: no.  `[∗list]` is generic over any `BI`, and `VProp` is
one, so the combinators and their lemma library apply unchanged; iris ships
`monPred_at_big_sepL` (here `MonPred.monPred_at_big_sepL`).  The diff from the SC twin is the
type ascription and the arrow (`↦ₘ` ↦ `↦w`); genuine `IProp`s gain `⎡ ⎤` (`G` below stands for
any of them).  The decomposition lemmas are DERIVED from `WeakCtx`'s structural laws only; a
client does not normally need them (the boundary lemmas apply to the whole payload), but they
make "no per-definition transport lemma" checkable.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase convention (name map below).  None of this file's names is in
   `notes/weak-port-dupnames.json`.
2. STATEMENT SHAPES (the `WeakCtx` deviation 2 convention): Rocq `P -∗ Q -∗ R` is `P ∗ Q ⊢ R`;
   `monPred_at R V` is `R.monPred_at V`; `view_scl` is `viewScl`; `DfracOwn 1` is `DFrac.own 1`.
3. `Context {!riscvGS Σ, !weakGS Σ}`: the SC instance is dropped (nothing here uses it), the
   ghost state is `[WeakGS GF]`; `` `{CID : CpuId} `` is dropped (nothing here uses it; Lean has
   no `CpuId` class, `WeakGhost` deviation 12).
4. `Record item := Item { it_a : Z; it_v : bv 8 }` is `structure Item` with fields `itA : Int`,
   `itV : BitVec 8` (constructor `Item.mk`).
5. `NoDup (it_a <$> l)` is `(l.map Item.itA).Nodup`.

**Rocq → Lean name map.**  `item`→`Item`, `Item`→`Item.mk`, `it_a`→`Item.itA`,
`it_v`→`Item.itV`, `item_inv`→`itemInv`, `items_inv`→`itemsInv`, `table_inv`→`tableInv`,
`table_acquire`→`tableAcquire`, `table_release`→`tableRelease`, `item_obj`→`itemObj`,
`items_obj`→`itemsObj`, `table_obj`→`tableObj`, `table_pub`→`tablePub`,
`table_round_trip`→`tableRoundTrip`.

**Not ported:** nothing.
-/
import Weak.WeakCtx
import Weak.WeakPtPub
import Weak.WeakVProp
import MachCSL.MonPredExtra

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp

/-- One entry of the protected structure: an address and the byte it holds. -/
structure Item where
  itA : Int
  itV : BitVec 8

section payload

variable {GF : BundledGFunctors} [WeakGS GF]
variable (ξ : CtxId)
variable (G : IProp GF)

/-! ## 1. The payload, written the way the SC one would be -/

/-- Level 1: one item — a pure well-formedness fact next to the memory. -/
def itemInv (x : Item) : VProp GF :=
  iprop(⌜0 < x.itA⌝ ∗ x.itA ↦w x.itV)

/-- Level 2: the list — an ordinary `[∗list]`, at `VProp`, with no redefinition anywhere. -/
def itemsInv (l : List Item) : VProp GF :=
  iprop([∗list] x ∈ l, itemInv x)

/-- Level 3: the whole thing — a global pure invariant, ghost state already an `IProp`, and
the list. -/
def tableInv (l : List Item) : VProp GF :=
  iprop(⌜(l.map Item.itA).Nodup⌝ ∗ ⎡G⎤ ∗ itemsInv l)

/-! ## 2. THE BOUNDARY — what a lock spec actually applies.  Both are the generic lemma at
`R := tableInv G l`; neither mentions the list, the nesting, or a byte. -/

theorem tableAcquire (V : View) (T : Nat) (l : List Item) (hT : ∀ a, T ≤ flr V a) :
    ctxAuth (GF := GF) ξ V ∗ (tableInv G l).monPred_at (viewScl T) ⊢
      ctxAuth ξ V ∗ cobj ξ (tableInv G l) :=
  cobjAcquire ξ V T _ hT

theorem tableRelease (V : View) (T : Nat) (l : List Item) (hT : ∀ a, flr V a ≤ T) :
    ctxAuth (GF := GF) ξ V ∗ cobj ξ (tableInv G l) ⊢
      ctxAuth ξ V ∗ (tableInv G l).monPred_at (viewScl T) :=
  cobjRelease ξ V T _ hT

/-! ## 3. The decomposition, DERIVED from `WeakCtx`'s structural laws. -/

theorem itemObj (x : Item) :
    cobj ξ (itemInv (GF := GF) x) ⊣⊢ iprop(⌜0 < x.itA⌝ ∗ cobj ξ (x.itA ↦w x.itV)) :=
  (cobjSep ξ _ _).trans (sep_congr (cobjPure ξ _) .rfl)

theorem itemsObj (l : List Item) :
    cobj ξ (itemsInv (GF := GF) l) ⊣⊢
      iprop([∗list] x ∈ l, ⌜0 < x.itA⌝ ∗ cobj ξ (x.itA ↦w x.itV)) :=
  (cobjBigSepL ξ l (fun _ x => itemInv x)).trans
    ⟨BigSepL.bigSepL_mono_of_forall (@fun _ x => (itemObj ξ x).mp),
     BigSepL.bigSepL_mono_of_forall (@fun _ x => (itemObj ξ x).mpr)⟩

theorem tableObj (l : List Item) :
    cobj ξ (tableInv G l) ⊣⊢
      iprop(⌜(l.map Item.itA).Nodup⌝ ∗ G ∗
        [∗list] x ∈ l, ⌜0 < x.itA⌝ ∗ cobj ξ (x.itA ↦w x.itV)) :=
  (cobjSep ξ _ _).trans
    (sep_congr (cobjPure ξ _) ((cobjSep ξ _ _).trans (sep_congr (cobjEmbed ξ G) (itemsObj ξ l))))

/-- The same payload as the INVARIANT sees it: per byte `wptPub T`, hart-free and absolute. -/
theorem tablePub (T : Nat) (l : List Item) :
    (tableInv G l).monPred_at (viewScl T) ⊣⊢
      iprop(⌜(l.map Item.itA).Nodup⌝ ∗ G ∗
        [∗list] x ∈ l, ⌜0 < x.itA⌝ ∗ wptPub (GF := GF) T x.itA (DFrac.own 1) x.itV) := by
  unfold tableInv itemsInv
  exact sep_congr .rfl (sep_congr .rfl
    ((monPred_at_big_sepL (viewScl T) (fun _ x => itemInv x) l).trans
      ⟨BigSepL.bigSepL_mono_of_forall (@fun _ x =>
          (sep_congr .rfl (wptPubFrozen T x.itA (DFrac.own 1) x.itV)).mp),
       BigSepL.bigSepL_mono_of_forall (@fun _ x =>
          (sep_congr .rfl (wptPubFrozen T x.itA (DFrac.own 1) x.itV)).mpr)⟩))

/-! ## 4. The round trip, on this payload: the structure goes in objectively and comes back
objectively; the two weak-memory side conditions are the lock's business. -/

theorem tableRoundTrip (V : View) (T : Nat) (l : List Item)
    (hT : ∀ a, flr V a ≤ T) (hacq : ∀ a, T ≤ flr V a) :
    ctxAuth (GF := GF) ξ V ∗ cobj ξ (tableInv G l) ⊢
      ctxAuth ξ V ∗ cobj ξ (tableInv G l) :=
  (tableRelease ξ G V T l hT).trans (tableAcquire ξ G V T l hacq)

end payload

end Weak
