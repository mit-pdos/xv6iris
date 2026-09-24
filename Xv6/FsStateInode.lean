/-
**ONE INODE'S ABSTRACT VALUE, AS READINGS OF THE NODE RECORD.**  The
SUBSET of Rocq `FsStateInode.v` (`/shared/xv6rocq/iris/FsStateInode.v`,
2097 lines) that the inode region needs: the node's scalar readings, the
flat file-byte view, and the BARE node with its lemmas.

Design of record: the Rocq tree's `claude-notes/design/fs-state.md` §2;
stage 2a of `claude-notes/projects/durable-disk.md`.

    n = { fnRec ; fnEnt ; fnBlk }

`fnRec` is the 64-byte on-disk record, `fnEnt` the indirect block's entry
array, and `fnBlk` maps a SLOT INDEX to that slot's block contents.  The
abstract byte-sequence is a READING, not the ownership: `fnFileBytes n` is
a function of `n`.

**LOCAL REASONING** (fs-state.md §0), Rocq's rule kept verbatim: every
clause here mentions ONE inode.  Links to other inodes are carried as
tokens, never as an equation.

## WHAT IS PORTED

`fnType`, `fnSize`, `fnNlink`, `fnNaddr`, `fnIndb`, `fnData`, `fnOrphan`,
`fnFileBytes`, `fnBare` and `fnBare`'s lemmas (`fnBare_wf`, `fnBare_indb`,
`fnBare_naddr`, `fnBare_orphan`), plus `fnZero` / `fnBare_zero`.

## WHAT IS DEFERRED, AND WHY (report for the wave)

Everything below needs the DIRECTORY vocabulary, which this port does not
have yet: `dir_nrec` / `T_DIR_z` live in Rocq `DirView.v` (wave 0c-3) and
`dir_view` / `dir_names_unique` / `fname` / `DOT` / `DOTDOT` /
`file_bytes` live in Rocq `FsTree.v`, which is in NO wave of 0c.  None of
it can be stated, let alone proved, before those land:

* `fn_is_dir`, `fn_nrec`, `dir_entries` and their lemmas
  (`fn_bare_nrec`, `dir_entries_bare`, `dir_entries_zero`,
  `dir_entries_write`, `dir_entries_fresh`);
* **`inode_local` (the 16-clause record) and `inode_local_bare`**, which
  the brief asked for: five of its clauses (`inl_dir_size`,
  `inl_dir_uniq`, `inl_dir_dot`, `inl_dir_dotdot`, and `inl_type`'s three
  type constants) are stated over exactly that vocabulary, so the RECORD
  cannot be written down.  Weakening it -- dropping the directory clauses
  -- would silently change the theorem every consumer reads off it, which
  the wave's rules forbid.  With it go `inode_local_data_owned`,
  `inode_local_beyond_size` and `node_dir_local` (whose `dir_ok` /
  `dir_dots_ix` / `dir_orphan_clean` are literally `DirView.v`'s).
  `InodeRegion.v` (wave 0c-2) consumes `inode_local`,
  `inode_local_bare` and `inl_type` in `inode_local_free_node` alone;
  that one lemma, and this record, should land with 0c-3's `DirView`.
* the whole of Rocq's §3-§9 (`Section RecOwned`, `Section InodeOwned`:
  `inode_dat`, `ent_toks`, `ent_tokenless`, `inode_owned`, the token
  moves) -- they are stated over `FsStateLink.v`'s link algebra and the
  era's top map, neither of which exists in this port
  (`Xv6/FsBytesGamma.lean` deviation 1 records that `FsViewNames` has no
  `γlink` / `γtop`).

## DEVIATIONS

1. **`fileBytes` IS HOISTED FROM Rocq `FsTree.v`** (`file_bytes`, with its
   `file_bytes_lookup`).  `fn_file_bytes` is one line over it and the
   brief puts `fn_file_bytes` in this batch; FsTree.v is in no wave of 0c.
   It is two lines over the port's existing `Xv6.fileByte`
   (`Xv6/InodeDefs.lean`).  When `FsTree` lands, delete these two and
   import them.
2. **`FS_NDIRECT` / `FS_NINDIRECT` / `FS_MAXFILE` ARE
   `Xv6.NDIRECT` / `NINDIRECT` / `MAXFILE`.**  Rocq duplicates the three
   in `FsImg.v` because that file is iris-free on purpose; this port
   collects every `fs.h` constant in `Xv6/FsGeom.lean` and there is
   nothing to duplicate.
3. **EVERYTHING IS `Nat`**, following `Xv6/FsGeom.lean`: Rocq's
   `fn_type` / `fn_size` / `fn_naddr` / `fn_indb` are `Z` readings of a
   `bv`, here they are `.toNat`.  `fn_nlink` is already `Z.to_nat` in
   Rocq.  Every `0 <= _` side condition vanishes.
4. **`fn_blk` IS A `RegMapF`** (`Xv6/FsNode.lean` deviation 1), so
   `fn_blk n !! k` is `PartialMap.get? n.fnBlk k` and stdpp's `default`
   is `Option.getD`.
5. `fn_orphan` is a `Bool` as in Rocq (`bool_decide`), spelled `decide`.
-/
import Xv6.FsNode
import Xv6.InodeDefs
import Xv6.FsGeom

namespace Xv6

open Iris.Std MachCSL

/-! ## 1.  The node's readings -/

/-- Rocq's `fn_type`. -/
def fnType (n : FsNode) : Nat := n.fnRec.diType.toNat

/-- Rocq's `fn_size`. -/
def fnSize (n : FsNode) : Nat := n.fnRec.diSize.toNat

/-- Rocq's `fn_nlink`. -/
def fnNlink (n : FsNode) : Nat := n.fnRec.diNlink.toNat

/-- The block number of slot `k`: direct out of the record, indirect out of
the entry array (Rocq's `fn_naddr`). -/
def fnNaddr (n : FsNode) (k : Nat) : Nat :=
  if k < NDIRECT then n.fnRec.diAddrs[k]!.toNat else n.fnEnt[k - NDIRECT]!.toNat

/-- The indirect block itself; `0` = none (Rocq's `fn_indb`). -/
def fnIndb (n : FsNode) : Nat := n.fnRec.diAddrs[NDIRECT]!.toNat

/-- The `data` function the tree's readings are stated over (Rocq's
`fn_data`).  Slots the node does not own read as zeroes -- which is only
ever consulted below the size, where `inl_covers` says the slot IS
owned. -/
def fnData (n : FsNode) : Nat → List (BitVec 8) :=
  fun k => (PartialMap.get? n.fnBlk k).getD (List.replicate BSIZE 0)

/-! ## The flat file view (deviation 1) -/

/-- A file's content: the first `n` bytes of its data (Rocq
`FsTree.file_bytes`). -/
def fileBytes (data : Nat → List (BitVec 8)) (n : Nat) : List (BitVec 8) :=
  (List.range n).map (fileByte data)

/-- ...and its total lookup, below the size, IS `fileByte` (Rocq
`FsTree.file_bytes_lookup`). -/
theorem fileBytes_lookup (data : Nat → List (BitVec 8)) (sz k : Nat) (hk : k < sz) :
    (fileBytes data sz)[k]! = fileByte data k := by
  have hlen : (fileBytes data sz).length = sz := by
    unfold fileBytes; rw [List.length_map, List.length_range]
  have h : (fileBytes data sz)[k]? = some (fileByte data k) := by
    unfold fileBytes
    rw [List.getElem?_map, List.getElem?_range hk]
    rfl
  exact getElem!_of_getElem? h

/-- Rocq's `fn_file_bytes`. -/
def fnFileBytes (n : FsNode) : List (BitVec 8) := fileBytes (fnData n) (fnSize n)

/-- An ORPHAN is a node at `nlink = 0`: its `".."` entry is TOKENLESS, the
parent having taken that token back at the unlink (fs-state.md §2).  This
kernel's "grey" record (Rocq's `fn_orphan`). -/
def fnOrphan (n : FsNode) : Bool := decide (fnNlink n = 0)

/-! ## 2a.  The BARE node

A node with no blocks, no indirect block, size 0 and nlink 0.  THREE of
this kernel's records are bare, and they are the same shape, so this is ONE
definition and not three (Rocq's own list):

* the FREE record (`diType = 0`) the mkfs image is full of;
* the CLAIM BOX `ialloc` installs (the zero record with the type halfword
  set);
* the CORPSE `itrunc` then `iput` leave (blocks and size already cleared,
  still typed until `iput` clears the type). -/

/-- Rocq's `fn_bare`.  `13` is `NDIRECT + 1`, spelled as `dinodeWf` spells
it. -/
def fnBare (n : FsNode) : Prop :=
  n.fnRec.diAddrs = List.replicate 13 0
  ∧ n.fnEnt = List.replicate NINDIRECT 0
  ∧ n.fnBlk = ∅
  ∧ fnSize n = 0
  ∧ fnNlink n = 0

theorem replicate_getElem! {α : Type _} [Inhabited α] (n : Nat) (a : α) (k : Nat)
    (hk : k < n) : (List.replicate n a)[k]! = a :=
  getElem!_of_getElem? (by rw [List.getElem?_replicate, if_pos hk])

theorem fnBare_wf (n : FsNode) (h : fnBare n) : dinodeWf n.fnRec := by
  obtain ⟨ha, _, _, _, _⟩ := h
  unfold dinodeWf
  rw [ha, List.length_replicate]

theorem fnBare_indb (n : FsNode) (h : fnBare n) : fnIndb n = 0 := by
  obtain ⟨ha, _, _, _, _⟩ := h
  unfold fnIndb
  rw [ha, replicate_getElem! 13 (0 : BitVec 32) NDIRECT (by decide)]
  rfl

theorem fnBare_naddr (n : FsNode) (k : Nat) (h : fnBare n) (hk : k < MAXFILE) :
    fnNaddr n k = 0 := by
  obtain ⟨ha, he, _, _, _⟩ := h
  unfold fnNaddr
  split
  · rename_i hd
    rw [ha, replicate_getElem! 13 (0 : BitVec 32) k (by unfold NDIRECT at hd; omega)]
    rfl
  · rename_i hd
    rw [he, replicate_getElem! NINDIRECT (0 : BitVec 32) (k - NDIRECT)
      (by unfold MAXFILE NDIRECT NINDIRECT at *; omega)]
    rfl

theorem fnBare_orphan (n : FsNode) (h : fnBare n) : fnOrphan n = true := by
  obtain ⟨_, _, _, _, hnl⟩ := h
  unfold fnOrphan
  rw [hnl]
  rfl

/-- The all-zero record: the mkfs image's free inode, and the node the boot
allocation starts every inum at (Rocq's `fn_zero`). -/
def fnZero : FsNode :=
  ⟨⟨0, 0, 0, 0, 0, List.replicate 13 0⟩, List.replicate NINDIRECT 0, ∅⟩

theorem fnBare_zero : fnBare fnZero := by
  unfold fnBare fnZero
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · decide
  · decide

end Xv6
