/-
**THE CARRIER ROWS EVERY CLIENT OF THE BLOCK LAYER HOLDS**, and the ERA'S
MINT, ported from Rocq `FsBlocks.v`'s `FsMint` section plus the two
allocation lemmas at the end of its `FsBytes` section (`byte_map_grow`,
`fs_bytes_alloc`, `fs_alloc`).

**THE ROWS.**  The home set is BOUND in `Xv6.fsBytesRow` because no consumer
needs to name it: holding a block's byte run IS being a home block
(`Xv6.fsblock_home_open`), and the byte map's AUTH -- of which there is
exactly one -- is inside the invariant, so two invariants at `Xv6.fsbN`
over one `γfs.bytes` cannot disagree about it.  What a consumer needs is
only that SOME such invariant exists, which is what the row says.

`Xv6.fsBytesAny` is the row a RUNTIME reader needs: the row plus the SEAL.
It is what `Xv6.logCtx` carries, so every client of the log layer gets it
for free and not one crossing site above the WAL changed.  (The bitmap's
and the inode region's own invariants are minted at PowerOn, BEFORE
recovery has run, so they will carry only `Xv6.fsBytesRow`; their crossings
take `Xv6.excSealed` explicitly and their callers read it off `logCtx`.)

Deviations: sets are lists (the port's standing log-layer deviation), and
Rocq's `fs_alloc` also names back the two abstract-state gnames
(`fs_link` / `fs_top`) which this port's `Xv6.FsNames` does not carry --
see `Xv6/FsBlocks.lean`.
-/
import Xv6.FsBytesInv

namespace Xv6

open Iris Iris.BI Iris.ProofMode Std MachCSL
open Iris.Std Iris.Std.PartialMap

set_option linter.unusedSectionVars false

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [FsBlocksG GF]

/-! ## The rows -/

/-- THE ROW AT A NAMED HOME SET.  `Xv` is bound: it is the invariant's own
bookkeeping for the recovery window and no consumer above the WAL names
it. -/
def fsBytesAt (γ : FsNames) (homeL : List Nat) : IProp GF :=
  iprop(∃ Xv : Nat → List (BitVec 8), fsBytesInv γ.bytes γ.cache γ.exc homeL Xv)

instance fsBytesAt_persistent (γ : FsNames) (homeL : List Nat) :
    Persistent (fsBytesAt (GF := GF) γ homeL) := by unfold fsBytesAt; infer_instance

theorem fsBytesAt_of (γ : FsNames) (homeL : List Nat) (Xv : Nat → List (BitVec 8)) :
    fsBytesInv (GF := GF) γ.bytes γ.cache γ.exc homeL Xv ⊢ fsBytesAt γ homeL := by
  unfold fsBytesAt; iintro H; iexists Xv; iexact H

/-- THE ROW ITSELF, minted at PowerOn: it says only that SOME byte-view
invariant over `γ` exists. -/
def fsBytesRow (γ : FsNames) : IProp GF :=
  iprop(∃ homeL : List Nat, fsBytesAt γ homeL)

instance fsBytesRow_persistent (γ : FsNames) :
    Persistent (fsBytesRow (GF := GF) γ) := by unfold fsBytesRow; infer_instance

/-- ...AND THE ROW A RUNTIME READER NEEDS: the row plus the SEAL. -/
def fsBytesAny (γ : FsNames) : IProp GF := iprop(fsBytesRow γ ∗ excSealed γ.exc)

instance fsBytesAny_persistent (γ : FsNames) :
    Persistent (fsBytesAny (GF := GF) γ) := by unfold fsBytesAny; infer_instance

/-- ...and the same pair at a NAMED home set. -/
def fsBytesAnyAt (γ : FsNames) (homeL : List Nat) : IProp GF :=
  iprop(fsBytesAt γ homeL ∗ excSealed γ.exc)

instance fsBytesAnyAt_persistent (γ : FsNames) (homeL : List Nat) :
    Persistent (fsBytesAnyAt (GF := GF) γ homeL) := by
  unfold fsBytesAnyAt; infer_instance

theorem fsBytesAny_row (γ : FsNames) : fsBytesAny (GF := GF) γ ⊢ fsBytesRow γ := by
  unfold fsBytesAny; iintro ⟨H, -⟩; iexact H

theorem fsBytesAny_seal (γ : FsNames) : fsBytesAny (GF := GF) γ ⊢ excSealed γ.exc := by
  unfold fsBytesAny; iintro ⟨-, H⟩; iexact H

theorem fsBytesAny_of (γ : FsNames) :
    fsBytesRow (GF := GF) γ ⊢ excSealed γ.exc -∗ fsBytesAny γ := by
  unfold fsBytesAny; iintro H1 H2; iframe H1 H2

theorem fsBytesAnyAt_at (γ : FsNames) (homeL : List Nat) :
    fsBytesAnyAt (GF := GF) γ homeL ⊢ fsBytesAt γ homeL := by
  unfold fsBytesAnyAt; iintro ⟨H, -⟩; iexact H

theorem fsBytesAnyAt_seal (γ : FsNames) (homeL : List Nat) :
    fsBytesAnyAt (GF := GF) γ homeL ⊢ excSealed γ.exc := by
  unfold fsBytesAnyAt; iintro ⟨-, H⟩; iexact H

theorem fsBytesAnyAt_any (γ : FsNames) (homeL : List Nat) :
    fsBytesAnyAt (GF := GF) γ homeL ⊢ fsBytesAny γ := by
  unfold fsBytesAnyAt fsBytesAny fsBytesRow
  iintro ⟨H1, H2⟩
  isplitl [H1]
  · iexists homeL; iexact H1
  · iexact H2

theorem fsBytesAnyAt_of (γ : FsNames) (homeL : List Nat) :
    fsBytesAt (GF := GF) γ homeL ⊢ excSealed γ.exc -∗ fsBytesAnyAt γ homeL := by
  unfold fsBytesAnyAt; iintro H1 H2; iframe H1 H2

/-! ## The bread client's crossing, AT THE ROW

What used to be an auth-free half/half entailment (`Xv6.fsChalf_mclean_agree`)
is this fupd.  The `_q` form is `readi`'s tie between the buffer `bread`
handed it and the bytes its own inode block map names, and it is an
AGREEMENT, so a read-locker holding a QUARTER of the run runs it exactly as
a full owner does. -/

theorem fsBytes_agree_any_q (E : CoPset) (γ : FsNames) (dq : DFrac) (b : Nat)
    (bs bsm : List (BitVec 8)) (hE : (↑logN : CoPset) ⊆ E) :
    fsBytesAny (GF := GF) γ -∗ fsblockQ γ.bytes dq b bs -∗
      (γ.cache ↪◯MAP[b]{DFrac.own (1 : Qp).half} bsm) -∗
      |={E}=> (⌜bsm = bs⌝ ∗ fsblockQ γ.bytes dq b bs ∗
        (γ.cache ↪◯MAP[b]{DFrac.own (1 : Qp).half} bsm)) := by
  unfold fsBytesAny fsBytesRow fsBytesAt
  iintro ⟨⟨%homeL, %Xv, #Hinv⟩, #Hseal⟩ Hfb Hm
  iapply fsBytesQ_agree E γ.bytes γ.cache γ.exc dq homeL Xv b bs bsm hE $$ Hinv Hseal Hfb Hm

theorem fsBytes_agree_any (E : CoPset) (γ : FsNames) (b : Nat)
    (bs bsm : List (BitVec 8)) (hE : (↑logN : CoPset) ⊆ E) :
    fsBytesAny (GF := GF) γ -∗ fsblock γ.bytes b bs -∗
      (γ.cache ↪◯MAP[b]{DFrac.own (1 : Qp).half} bsm) -∗
      |={E}=> (⌜bsm = bs⌝ ∗ fsblock γ.bytes b bs ∗
        (γ.cache ↪◯MAP[b]{DFrac.own (1 : Qp).half} bsm)) := by
  rw [fsblock_1]
  exact fsBytes_agree_any_q E γ (DFrac.own 1) b bs bsm hE

/-- **THE DROP-IN FOR `Xv6.fsCache_update` AT A HOME BLOCK** (Rocq's
`fsblock_update`, read at the row `Xv6.logCtx` carries).  The shape is
`fsCache_update`'s with `fsChalf` replaced by `fsblock`, `|==>` by
`|={E}=>`, and the persistent row added -- which is why the call sites are
one-line edits. -/
theorem fsblock_update_any (E : CoPset) (γ : FsNames) (L : BlockMap) (b : Nat)
    (bs bsNew bs' : List (BitVec 8)) (hE : (↑logN : CoPset) ⊆ E)
    (hlnew : bsNew.length = BSIZE) :
    fsBytesAny (GF := GF) γ -∗ fsCacheAuth γ L -∗ fsblock γ.bytes b bs -∗
      (γ.cache ↪◯MAP[b]{DFrac.own (1 : Qp).half} bs') -∗
      |={E}=> (⌜bs' = bs ∧ PartialMap.get? L b = some bs⌝ ∗
        fsCacheAuth γ (PartialMap.insert L b bsNew) ∗ fsblock γ.bytes b bsNew ∗
        (γ.cache ↪◯MAP[b]{DFrac.own (1 : Qp).half} bsNew)) := by
  unfold fsBytesAny fsBytesRow fsBytesAt fsCacheAuth
  iintro ⟨⟨%homeL, %Xv, #Hinv⟩, #Hseal⟩ Ha Hfb Hm
  iapply fsblock_update E γ.bytes γ.cache γ.exc homeL Xv L b bs bsNew bs' hE hlnew
    $$ Hinv Hseal Ha Hfb Hm

/-- **THE RECOVERING INSTALL'S GHOST STEP**, at `Xv6.fsCacheAuth` (Rocq's
`fsblock_install_exc`).  Needs NO byte run: the byte view was minted at the
committed view, so it already reads the logged value at `b`; what moves is
the CACHE map, from the crashed bytes to `Xv b` -- exactly what the home
`bwrite` just put on the disk. -/
theorem fsblock_install_exc_at (E : CoPset) (γ : FsNames) (homeL : List Nat)
    (Xv : Nat → List (BitVec 8)) (L : BlockMap) (X : List Nat) (b : Nat)
    (bsm : List (BitVec 8)) (hE : (↑logN : CoPset) ⊆ E) (hb : b ∈ X)
    (hlen : (Xv b).length = BSIZE) :
    fsBytesInv (GF := GF) γ.bytes γ.cache γ.exc homeL Xv -∗ excOwn γ.exc X -∗
      fsCacheAuth γ L -∗ (γ.cache ↪◯MAP[b]{DFrac.own (1 : Qp).half} bsm) -∗
      |={E}=> (⌜PartialMap.get? L b = some bsm⌝ ∗ excOwn γ.exc (excDel X b) ∗
        fsCacheAuth γ (PartialMap.insert L b (Xv b)) ∗
        (γ.cache ↪◯MAP[b]{DFrac.own (1 : Qp).half} (Xv b))) := by
  unfold fsCacheAuth
  iintro #Hinv Hxo Ha Hm
  iapply fsblock_install_exc E γ.bytes γ.cache γ.exc homeL Xv L X b bsm hE hb hlen
    $$ Hinv Hxo Ha Hm

/-- ...and the home-block reading, at the row. -/
theorem fsblock_home_any (E : CoPset) (γ : FsNames) (homeL : List Nat) (b : Nat)
    (bs : List (BitVec 8)) (hE : (↑logN : CoPset) ⊆ E) :
    fsBytesAt (GF := GF) γ homeL -∗ fsblock γ.bytes b bs -∗
      |={E}=> (⌜b ∈ homeL⌝ ∗ fsblock γ.bytes b bs) := by
  unfold fsBytesAt
  iintro ⟨%Xv, #Hinv⟩ Hfb
  iapply fsblock_home_open E γ.bytes γ.cache γ.exc homeL Xv b bs hE $$ Hinv Hfb

end

end Xv6
