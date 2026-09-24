/-
The two BLOCK-LEVEL authorities the write-ahead log freezes, ported from
the part of Rocq `FsBlocks.v` that `LogInv.v` names: the LOGGED VIEW
(`fs_cache`, the logical content of every covered block, with a client
HALF per block) and the PINNED SET (`fs_dirty`, one boolean per covered
block, likewise in halves).

**READ THIS BEFORE USING IT: the tie to the buffer cache is MISSING, and
cannot be added from outside the bio layer.**  In Rocq the client view the
bio layer is parametric over carries two hooks, `bio_view.bv_clean` and
`bv_dirty`, and a buffer's travelling payload (`BioInv.buf_pay`) IS
`bv_clean bs` -- which is what makes a `bread` of block `b` hand the
caller a proposition about `fs_cache`'s value at `b`, and what makes the
committer's authority a FREEZE on what every buffer holds.  This port's
`Xv6.BioView` is `gd`/`dev`/`cov` only, and `Xv6.bufPay` is the disk
image fragment `Xv6.diskBlock` at the buffer's own bytes: see the note in
`Xv6/BioPool.lean` ("Rocq's `bio_locked` carries the log layer's opaque
payload ... This port has no log layer, so the payload IS the disk
fragment").  Consequently the authorities below are HONEST GHOST STATE --
they are allocated, split, agreed and updated exactly as Rocq's are, and
nothing false is assumed anywhere -- but nothing in this port relates
them to what a buffer or the disk actually holds.  Re-establishing the
tie means extending `BioView`/`bufPay` with the two payload hooks and
re-proving the five bio functions; it is out of reach of a file that may
not touch the bio layer, and it is the single largest residual of the log
port.

Not ported from `FsBlocks.v`: the BYTE view (`fs_bytes`, `bytes_tie`,
`bytes_dom`, `fs_bytes_inv`, `exc_own`/`exc_sealed`) -- that layer belongs
to the file system ABOVE the log (it is what `readi`/`writei` read), it has
no client in this port, and `LogInv`'s only use of it is to park a row for
the file system's own crossings.
-/
import Xv6.LogDefs

namespace Xv6

open Iris Iris.BI Iris.ProofMode Std MachCSL

set_option linter.unusedSectionVars false

/-- Rocq's `fs_names`, the two members the WAL uses. -/
structure FsNames where
  /-- the logged view: block ↦ its logical content -/
  cache : GName
  /-- the pinned set: block ↦ "the log holds a pin on this block" -/
  dirty : GName

/-- The ghost libraries the block view needs (the `fsLogG` members
`LogInv` names). -/
class FsBlocksG (GF : BundledGFunctors) where
  [gmCache : GhostMapG GF Nat (List (BitVec 8)) RegMapF]
  [gmDirty : GhostMapG GF Nat Bool RegMapF]

attribute [reducible, instance] FsBlocksG.gmCache FsBlocksG.gmDirty

section
variable {GF : BundledGFunctors} [FsBlocksG GF]

/-- **The logged view's authority** (Rocq's `ghost_map_auth (fs_cache γfs) 1 L`):
the freeze-by-auth that makes `log_write` and the committer the only
writers of the logged view. -/
def fsCacheAuth (γfs : FsNames) (L : BlockMap) : IProp GF := γfs.cache ↪●MAP L

/-- **A block's CLIENT half** (Rocq's `fs_chalf`): the log is its own
client for the header block and the `LOGBLOCKS` slots; every home block's
half belongs to the file system above.

AT FRACTION ONE, not one half.  Rocq's other half is the one a BUFFER's
travelling payload carries (`bio_view.bv_clean`), and this port's buffer
payload carries the disk image fragment instead (see the file header), so
there is no second half to hold: the client owns the element whole.  That
is also what makes the ghost update below possible at all -- a half
cannot be written. -/
def fsChalf (γfs : FsNames) (b : Nat) (bs : List (BitVec 8)) : IProp GF :=
  γfs.cache ↪◯MAP[b] bs

/-- **The pinned set's authority.** -/
def fsDirtyAuth (γfs : FsNames) (D : RegMapF Bool) : IProp GF := γfs.dirty ↪●MAP D

/-- **A block's pin half**: in Rocq the log side holds one and the
buffer's payload the other; here, for `fsChalf`'s reason, the log side
holds the element whole. -/
def fsDirtyHalf (γfs : FsNames) (b : Nat) (v : Bool) : IProp GF :=
  γfs.dirty ↪◯MAP[b] v

instance fsCacheAuth_timeless (γfs : FsNames) (L : BlockMap) :
    Timeless (fsCacheAuth (GF := GF) γfs L) := by unfold fsCacheAuth; infer_instance
instance fsChalf_timeless (γfs : FsNames) (b : Nat) (bs : List (BitVec 8)) :
    Timeless (fsChalf (GF := GF) γfs b bs) := by unfold fsChalf; infer_instance
instance fsDirtyAuth_timeless (γfs : FsNames) (D : RegMapF Bool) :
    Timeless (fsDirtyAuth (GF := GF) γfs D) := by unfold fsDirtyAuth; infer_instance
instance fsDirtyHalf_timeless (γfs : FsNames) (b : Nat) (v : Bool) :
    Timeless (fsDirtyHalf (GF := GF) γfs b v) := by unfold fsDirtyHalf; infer_instance

/-! ## The four steps a WAL proof takes -/

/-- A client half is what the authority says it is. -/
theorem fsCache_lookup (γfs : FsNames) (L : BlockMap) (b : Nat) (bs : List (BitVec 8)) :
    fsCacheAuth (GF := GF) γfs L ⊢ fsChalf γfs b bs -∗
      ⌜PartialMap.get? L b = some bs⌝ := by
  unfold fsCacheAuth fsChalf
  iintro H1 H2
  ihave %h := ghost_map_lookup $$ H1 H2
  ipureintro
  exact h

/-- ...and the same for a pin. -/
theorem fsDirty_lookup (γfs : FsNames) (D : RegMapF Bool) (b : Nat) (v : Bool) :
    fsDirtyAuth (GF := GF) γfs D ⊢ fsDirtyHalf γfs b v -∗
      ⌜PartialMap.get? D b = some v⌝ := by
  unfold fsDirtyAuth fsDirtyHalf
  iintro H1 H2
  ihave %h := ghost_map_lookup $$ H1 H2
  ipureintro
  exact h

/-- **The logged view's one move**: the authority and the block's OWN
client half go to a new content together (Rocq's `fs_chalf_update`). -/
theorem fsCache_update (γfs : FsNames) (L : BlockMap) (b : Nat) (bs bs' : List (BitVec 8)) :
    fsCacheAuth (GF := GF) γfs L ⊢ fsChalf γfs b bs -∗
      |==> (fsCacheAuth γfs (PartialMap.insert L b bs') ∗ fsChalf γfs b bs') := by
  unfold fsCacheAuth fsChalf
  iintro H1 H2
  imod (ghost_map_update (γ := γfs.cache) (m := L) (k := b) (v := bs) bs') $$ H1 H2 with ⟨Ha, He⟩
  imodintro
  iframe Ha He

/-- **A pin's flip**: the element and the authority move together. -/
theorem fsDirty_update (γfs : FsNames) (D : RegMapF Bool) (b : Nat) (v v' : Bool) :
    fsDirtyAuth (GF := GF) γfs D ⊢ fsDirtyHalf γfs b v -∗
      |==> (fsDirtyAuth γfs (PartialMap.insert D b v') ∗ fsDirtyHalf γfs b v') := by
  unfold fsDirtyAuth fsDirtyHalf
  iintro H1 H2
  imod (ghost_map_update (γ := γfs.dirty) (m := D) (k := b) (v := v) v') $$ H1 H2 with ⟨Ha, He⟩
  imodintro
  iframe Ha He

/-- The genesis bundle: both authorities born empty. -/
def fsFreeTok (γfs : FsNames) : IProp GF :=
  iprop(fsCacheAuth γfs ∅ ∗ fsDirtyAuth γfs ∅)

theorem fsGhostAlloc : ⊢ |==> (∃ γfs : FsNames, fsFreeTok (GF := GF) γfs) := by
  imod (ghost_map_alloc_empty (GF := GF) (K := Nat) (V := List (BitVec 8)) (H := RegMapF))
    with ⟨%γc, Hc⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Bool) (H := RegMapF)) with ⟨%γd, Hd⟩
  imodintro
  iexists ⟨γc, γd⟩
  unfold fsFreeTok fsCacheAuth fsDirtyAuth
  iframe Hc Hd

end

end Xv6
