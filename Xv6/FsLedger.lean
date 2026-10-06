/-
**THE ERA'S FS-EVENT LEDGER: THE RESOURCE, THE TIE TO THE TYPED ROWS, THE
RECEIPTS** (NI M3 private files, lane FS-1; design of record
`claude-notes/projects/noninterference.md`, "M3 private files design
(2026-10-05)", findings F2/F3/F4/F7/F8, rulings FS-R2/R3/R5).

The commits hand their receipts to the CLIENT's piece, and the generic
dispatcher passes trivial pieces, so no kernel-owned record says what any fs
call saw (F2).  This is that record: ONE mono-list of `NiFs.Fev` per era, at
the era's own name `FsNames.fev`, whose authority `InodeRegionInv.ftopBody`
holds beside the kernel's half of the top map, TIED to it:

    fevTie h I  :=  fevRows h = ftopRows I

-- the fold of the history IS the raw map read through `ftopRow` on TYPED
records (orphans at nlink 0 included, so a read through an fd of an unlinked
file reads a row the view no longer has; F3).  Every move of the map appends
the corresponding event at its own instant (the fire lemmas, iput's free,
ilock's claim fill), with the actor; the observations append theirs; the
receipts (`fsEvRcpt`) are lower bounds ending in the round's own event, its
POSITION the prefix's length (FS-R3).

`fsFullRcpt` (lane FS-0's name) is now the receipt of an exhaustion verdict.

What the NI roots name of this is `NiFs` alone (F8): this module is never in
a statement's cone.

## Deviations from the design text

1. THE NAME IS THE ERA'S `FsNames.fev`, NOT A `WchG` NAME (the brief's
   `WchG.wfsName`): the receipts ride open's and mkdir's RECEIPTS
   (`SpecSysOpen.openReceiptCreate`, `SpecSysMkdir.mkdirArms`), which the U
   tier states in sections with no `WchG` instance; the allocator's ledger
   `fsReadyKmem.pend` is keyed the same way (an `Fscfg` name).  The camera
   is `Xv6G.mlFevG` (as `Xv6G.mlKevG`).  `NiEvid.niNamesHere`'s seventh entry
   is `fscFs.fev`.
2. (NI M3 private files FS-2a′) **THE TRACKED OFFSETS.**  `ftopLed` also
   holds a QUARTER of every parked file's offset shadow at the fold's
   offset (`fevShares`, over `NiFs.fevPk`), keeps the recorded offsets the
   fold's (`NiFs.fevOffWf`) and the tracked shadows distinct, and keeps a
   MIRROR of the ledger at the `Icfg` name `icfgFev` (the descriptor rows
   cannot name the `Fscfg` ledger: `FdTable.foffRow`'s parked arm carries a
   mirror lower bound naming the install, `fevPkWit`).  Neutral appends
   (`ftopLed_step`, `fevNeutral`) leave the shares; a parked install mints
   one from the whole fresh shadow (`ftopLed_pkOpen`); a parked read or
   write moves the three shares together and records the agreed offset
   (`ftopLed_pkAdv`).  Every lower bound is well-formed (`ftopLed_lb_wf`).
-/
import Xv6.NiFs
import Xv6.FsAbsDefs
import Xv6.FsBlocks
import Xv6.UartTrace
import Xv6.OffGv
import Xv6.IcacheRefDefs

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL

/-! ## §1 The tie, pure -/

/-- an abstract node in the ledger's vocabulary -/
def fnodeOf : Absnode → Fnode
  | .AFile bs => .file bs
  | .ADir m => .dir m
  | .ADev a b => .dev a b

theorem fnodeOf_inj {a b : Absnode} (h : fnodeOf a = fnodeOf b) : a = b := by
  cases a <;> cases b <;> simp_all [fnodeOf]

/-- **THE TYPED ROW** a record reads as: none at a FREE record (type 0), else
its abstract node and its count -- at ANY count (an unlinked-but-open file,
a claim box) -/
def ftopRow (n : FsNode) : Option (Fnode × Nat) :=
  if fnType n = 0 then none else some (fnodeOf (absNode n), fnNlink n)

/-- the raw map's typed rows -/
def ftopRows (I : RegMapF FsNode) : Frows :=
  fun i => (PartialMap.get? I i).bind ftopRow

/-- **THE TIE** -/
def fevTie (h : List Fev) (I : RegMapF FsNode) : Prop := fevRows h = ftopRows I

theorem ftopRow_typed (n : FsNode) (hnz : fnType n ≠ 0) :
    ftopRow n = some (fnodeOf (absRow n).anNode, (absRow n).anNlink) := by
  unfold ftopRow; rw [if_neg hnz]; rfl

theorem ftopRow_free (n : FsNode) (hz : fnType n = 0) : ftopRow n = none := by
  unfold ftopRow; rw [if_pos hz]

/-- equal typed rows read as equal views (what a `_same` retag owes the
application) -/
theorem absOf_of_ftopRow {n n' : FsNode} (h : ftopRow n = ftopRow n') : absOf n = absOf n' := by
  unfold ftopRow at h
  unfold absOf absRow
  by_cases hz : fnType n = 0 <;> by_cases hz' : fnType n' = 0 <;> simp_all
  obtain ⟨h1, h2⟩ := h
  have := fnodeOf_inj h1
  simp_all

/-- a directory retag at the same type, count and entries keeps its typed
row (`absOf_dir_same`'s twin, at the ledger's grain) -/
theorem ftopRow_dir_same (n n' : FsNode) (hd : fnIsDir n = true) (hty : fnType n = fnType n')
    (hnl : fnNlink n = fnNlink n') (he : dirEntries n = dirEntries n') :
    ftopRow n = ftopRow n' := by
  have hd' : fnIsDir n' = true := by unfold fnIsDir at hd ⊢; rw [← hty]; exact hd
  unfold ftopRow absNode
  rw [hty, hnl, if_pos hd, if_pos hd', he]

theorem ftopRows_insert (I : RegMapF FsNode) (i : Nat) (n : FsNode) :
    ftopRows (PartialMap.insert I i n) = frowsSet (ftopRows I) i (ftopRow n) := by
  funext j
  unfold ftopRows frowsSet
  rw [LawfulPartialMap.get?_insert]
  by_cases hj : i = j
  · rw [if_pos hj, if_pos hj.symm]; rfl
  · rw [if_neg hj, if_neg (Ne.symm hj)]

theorem ftopRows_get (I : RegMapF FsNode) (i : Nat) (n : FsNode) (hi : PartialMap.get? I i = some n) :
    ftopRows I i = ftopRow n := by
  unfold ftopRows; rw [hi]; rfl

theorem frowsSet_self (s : Frows) (i : Nat) : frowsSet s i (s i) = s := by
  funext j; unfold frowsSet; split
  · next h => rw [h]
  · rfl

/-- an observation keeps the tie -/
theorem fevTie_obs {h : List Fev} {I : RegMapF FsNode} (e : Fev) (he : fevObs e) (ht : fevTie h I) :
    fevTie (h ++ [e]) I := by
  unfold fevTie at *; rw [fevRows_obs h e he]; exact ht

/-- **A ONE-ROW MOVE KEEPS THE TIE** when its events take the fold's row `i`
from the record's row to the new record's, and nothing else -/
theorem fevTie_move {h : List Fev} {I : RegMapF FsNode} (i : Nat) (n' : FsNode) (evs : List Fev)
    (ht : fevTie h I)
    (hrows : fevRows (h ++ evs) = frowsSet (fevRows h) i (ftopRow n')) :
    fevTie (h ++ evs) (PartialMap.insert I i n') := by
  unfold fevTie at *
  rw [hrows, ht, ftopRows_insert]

/-- the fold's row of a tied map -/
theorem fevTie_row {h : List Fev} {I : RegMapF FsNode} (i : Nat) (n : FsNode) (ht : fevTie h I)
    (hi : PartialMap.get? I i = some n) : fevRows h i = ftopRow n := by
  unfold fevTie at ht; rw [ht, ftopRows_get I i n hi]

/-! ### One event's effect on the rows -/

theorem fevRows_claim (h : List Fev) (a : BitVec 64) (i : Nat) (n : Fnode) :
    fevRows (h ++ [.claim a i n]) = frowsSet (fevRows h) i (some (n, 0)) := by
  rw [fevRows_snoc]; rfl

theorem fevRows_arm (h : List Fev) (a : BitVec 64) (i : Nat) (n : Fnode) :
    fevRows (h ++ [.arm a i n]) = frowsSet (fevRows h) i (some (n, 1)) := by
  rw [fevRows_snoc]; rfl

theorem fevRows_ent (h : List Fev) (a : BitVec 64) (d : Nat) (nm : List (BitVec 8)) (t : Option Nat) :
    fevRows (h ++ [.ent a d nm t]) = frowsSet (fevRows h) d (frowEnt nm t (fevRows h d)) := by
  rw [fevRows_snoc]; rfl

theorem fevRows_nlink (h : List Fev) (a : BitVec 64) (i nl : Nat) :
    fevRows (h ++ [.nlink a i nl]) = frowsSet (fevRows h) i (frowNlink nl (fevRows h i)) := by
  rw [fevRows_snoc]; rfl

theorem fevRows_write (h : List Fev) (a : BitVec 64) (i : Nat) (γo : GName) (hd : Bool) (off : Nat)
    (bs : List (BitVec 8)) (r : Nat) :
    fevRows (h ++ [.write a i γo hd off bs r]) = frowsSet (fevRows h) i (frowWrite off bs (fevRows h i)) := by
  rw [fevRows_snoc]; rfl

/-- (NI M3 FS-2a′) an install and a read move no row, at either mode -/
theorem fevTie_open {h : List Fev} {I : RegMapF FsNode} (a : BitVec 64) (i : Nat) (γo : GName) (hd : Bool)
    (po : Option Nat) (ht : fevTie h I) : fevTie (h ++ [.open a i γo hd po]) I := by
  unfold fevTie at *; rw [fevRows_snoc]; exact ht

theorem fevTie_read {h : List Fev} {I : RegMapF FsNode} (a : BitVec 64) (i : Nat) (γo : GName) (hd : Bool)
    (off d : Nat) (ht : fevTie h I) : fevTie (h ++ [.read a i γo hd off d]) I := by
  unfold fevTie at *; rw [fevRows_snoc]; exact ht

theorem fevRows_trunc (h : List Fev) (a : BitVec 64) (i : Nat) :
    fevRows (h ++ [.trunc a i]) = frowsSet (fevRows h) i (frowTrunc (fevRows h i)) := by
  rw [fevRows_snoc]; rfl

theorem fevRows_free (h : List Fev) (a : BitVec 64) (i : Nat) :
    fevRows (h ++ [.free a i]) = frowsSet (fevRows h) i none := by
  rw [fevRows_snoc]; rfl

theorem frowsSet_twice (s : Frows) (i : Nat) (v w : Option (Fnode × Nat)) :
    frowsSet (frowsSet s i v) i w = frowsSet s i w := by
  funext j; unfold frowsSet; split <;> rfl

theorem frowsSet_get (s : Frows) (i : Nat) (v : Option (Fnode × Nat)) : frowsSet s i v i = v := by
  unfold frowsSet; rw [if_pos rfl]

/-! ### The moves, one lemma per shape (what each fire appends) -/

section Moves
variable {h : List Fev} {I : RegMapF FsNode} {i : Nat} {n n' : FsNode} (a : BitVec 64)

theorem ftopRow_absRow (n : FsNode) (hnz : fnType n ≠ 0) (c : Absnode) (nl : Nat)
    (habs : absRow n = ⟨c, nl⟩) : ftopRow n = some (fnodeOf c, nl) := by
  rw [ftopRow_typed n hnz, habs]

/-- a chunk written at `off` -/
theorem fevTie_write (γo : GName) (hd : Bool) (off : Nat) (bs bs0 : List (BitVec 8)) (nl r : Nat)
    (ht : fevTie h I) (hi : PartialMap.get? I i = some n)
    (hnz : fnType n ≠ 0) (habs : absRow n = ⟨.AFile bs0, nl⟩)
    (hnz' : fnType n' ≠ 0) (habs' : absRow n' = ⟨.AFile (blkSplice off bs bs0), nl⟩) :
    fevTie (h ++ [.write a i γo hd off bs r]) (PartialMap.insert I i n') := by
  apply fevTie_move i n' _ ht
  rw [fevRows_write, fevTie_row i n ht hi, ftopRow_absRow n hnz _ _ habs,
    ftopRow_absRow n' hnz' _ _ habs']
  rfl

/-- O_TRUNC's itrunc -/
theorem fevTie_trunc (bs0 : List (BitVec 8)) (nl : Nat)
    (ht : fevTie h I) (hi : PartialMap.get? I i = some n)
    (hnz : fnType n ≠ 0) (habs : absRow n = ⟨.AFile bs0, nl⟩)
    (hnz' : fnType n' ≠ 0) (habs' : absRow n' = ⟨.AFile [], nl⟩) :
    fevTie (h ++ [.trunc a i]) (PartialMap.insert I i n') := by
  apply fevTie_move i n' _ ht
  rw [fevRows_trunc, fevTie_row i n ht hi, ftopRow_absRow n hnz _ _ habs,
    ftopRow_absRow n' hnz' _ _ habs']
  rfl

/-- a link-count leg -/
theorem fevTie_nlink (c : Absnode) (nl nl' : Nat)
    (ht : fevTie h I) (hi : PartialMap.get? I i = some n)
    (hnz : fnType n ≠ 0) (habs : absRow n = ⟨c, nl⟩)
    (hnz' : fnType n' ≠ 0) (habs' : absRow n' = ⟨c, nl'⟩) :
    fevTie (h ++ [.nlink a i nl']) (PartialMap.insert I i n') := by
  apply fevTie_move i n' _ ht
  rw [fevRows_nlink, fevTie_row i n ht hi, ftopRow_absRow n hnz _ _ habs,
    ftopRow_absRow n' hnz' _ _ habs']
  rfl

/-- an entry set or removed, the directory's count unchanged -/
theorem fevTie_ent (nm : List (BitVec 8)) (t : Option Nat) (m : Std.ExtTreeMap Fname Nat compare)
    (nl : Nat) (ht : fevTie h I) (hi : PartialMap.get? I i = some n)
    (hnz : fnType n ≠ 0) (habs : absRow n = ⟨.ADir m, nl⟩)
    (hnz' : fnType n' ≠ 0) (habs' : absRow n' = ⟨.ADir (fentSet m nm t), nl⟩) :
    fevTie (h ++ [.ent a i nm t]) (PartialMap.insert I i n') := by
  apply fevTie_move i n' _ ht
  rw [fevRows_ent, fevTie_row i n ht hi, ftopRow_absRow n hnz _ _ habs,
    ftopRow_absRow n' hnz' _ _ habs']
  rfl

/-- an entry move AND a link-count leg on the same directory (create's
parent leg at a directory child, unlink's at a directory) -/
theorem fevTie_entNlink (nm : List (BitVec 8)) (t : Option Nat) (m : Std.ExtTreeMap Fname Nat compare)
    (nl nl' : Nat) (ht : fevTie h I) (hi : PartialMap.get? I i = some n)
    (hnz : fnType n ≠ 0) (habs : absRow n = ⟨.ADir m, nl⟩)
    (hnz' : fnType n' ≠ 0) (habs' : absRow n' = ⟨.ADir (fentSet m nm t), nl'⟩) :
    fevTie (h ++ [.ent a i nm t, .nlink a i nl']) (PartialMap.insert I i n') := by
  apply fevTie_move i n' _ ht
  have e : h ++ [Fev.ent a i nm t, Fev.nlink a i nl'] = (h ++ [.ent a i nm t]) ++ [.nlink a i nl'] := by
    simp
  rw [e, fevRows_nlink, fevRows_ent, fevTie_row i n ht hi, ftopRow_absRow n hnz _ _ habs,
    ftopRow_absRow n' hnz' _ _ habs', frowsSet_get, frowsSet_twice]
  rfl

/-- create's arm: the child appears at count 1 -/
theorem fevTie_arm (c : Absnode) (ht : fevTie h I) (hnz' : fnType n' ≠ 0)
    (habs' : absRow n' = ⟨c, 1⟩) :
    fevTie (h ++ [.arm a i (fnodeOf c)]) (PartialMap.insert I i n') := by
  apply fevTie_move i n' _ ht
  rw [fevRows_arm, ftopRow_absRow n' hnz' _ _ habs']

/-- two entries set on one directory (a fresh directory's dots) -/
theorem fevTie_ent2 (nm1 nm2 : List (BitVec 8)) (t1 t2 : Option Nat)
    (m : Std.ExtTreeMap Fname Nat compare) (nl : Nat)
    (ht : fevTie h I) (hi : PartialMap.get? I i = some n)
    (hnz : fnType n ≠ 0) (habs : absRow n = ⟨.ADir m, nl⟩)
    (hnz' : fnType n' ≠ 0) (habs' : absRow n' = ⟨.ADir (fentSet (fentSet m nm1 t1) nm2 t2), nl⟩) :
    fevTie (h ++ [.ent a i nm1 t1, .ent a i nm2 t2]) (PartialMap.insert I i n') := by
  apply fevTie_move i n' _ ht
  have e : h ++ [Fev.ent a i nm1 t1, Fev.ent a i nm2 t2] = (h ++ [.ent a i nm1 t1]) ++ [.ent a i nm2 t2] := by
    simp
  rw [e, fevRows_ent, fevRows_ent, fevTie_row i n ht hi, ftopRow_absRow n hnz _ _ habs,
    ftopRow_absRow n' hnz' _ _ habs', frowsSet_get, frowsSet_twice]
  rfl

end Moves

/-! ## §2 The resource -/

section Res
variable {GF : BundledGFunctors} [Xv6G GF] [OffboxG GF]

/-- the ledger's authority (it lives in `InodeRegionInv.ftopBody`) -/
def fsLedAuth (γfs : FsNames) (h : List Fev) : IProp GF := γfs.fev ↪●ML h

/-- a persistent lower bound of the ledger -/
def fsLedLb (γfs : FsNames) (h : List Fev) : IProp GF := γfs.fev ↪◯ML h

instance fsLedLb_persistent (γfs : FsNames) (h : List Fev) : Persistent (fsLedLb (GF := GF) γfs h) := by
  unfold fsLedLb; infer_instance

instance fsLedAuth_timeless (γfs : FsNames) (h : List Fev) : Timeless (fsLedAuth (GF := GF) γfs h) := by
  unfold fsLedAuth; infer_instance

/-- **THE RECEIPT**: event `e` sits in the ledger at position `|h|`, after
the prefix `h` (whose fold is what `e` observed or moved from). -/
def fsEvRcpt (γfs : FsNames) (h : List Fev) (e : Fev) : IProp GF := fsLedLb γfs (h ++ [e])

instance fsEvRcpt_persistent (γfs : FsNames) (h : List Fev) (e : Fev) :
    Persistent (fsEvRcpt (GF := GF) γfs h e) := by
  unfold fsEvRcpt; infer_instance

/-- **AN OBSERVATION's RECEIPT**: event `e` at a position whose prefix's fold
read, at row `i`, the record `n` the observer held (the tie at that
instant). -/
def fsObsRcpt (γfs : FsNames) (e : Fev) (i : Nat) (n : FsNode) : IProp GF :=
  iprop(∃ h : List Fev, ⌜fevRows h i = ftopRow n⌝ ∗ fsEvRcpt γfs h e)

instance fsObsRcpt_persistent (γfs : FsNames) (e : Fev) (i : Nat) (n : FsNode) :
    Persistent (fsObsRcpt (GF := GF) γfs e i n) := by
  unfold fsObsRcpt; infer_instance

/-- **A MOVE's RECEIPT**: the move's events `evs` at a position whose
prefix's fold read, at the moved row `i`, the record `n` it moved from. -/
def fsMoveRcpt (γfs : FsNames) (evs : List Fev) (i : Nat) (n : FsNode) : IProp GF :=
  iprop(∃ h : List Fev, ⌜fevRows h i = ftopRow n⌝ ∗ fsLedLb γfs (h ++ evs))

instance fsMoveRcpt_persistent (γfs : FsNames) (evs : List Fev) (i : Nat) (n : FsNode) :
    Persistent (fsMoveRcpt (GF := GF) γfs evs i n) := by
  unfold fsMoveRcpt; infer_instance

/-- (FS-1) the observation's receipt at the ABSTRACT row a client spec names
(`Anode`, what the fs posts speak of): the event lands at a prefix whose
fold holds the row `a` at `i` -/
def fsObsAt (γfs : FsNames) (e : Fev) (i : Nat) (a : Anode) : IProp GF :=
  iprop(∃ h, ⌜fevRows h i = some (fnodeOf a.anNode, a.anNlink)⌝ ∗ fsEvRcpt γfs h e)

instance fsObsAt_persistent (γfs : FsNames) (e : Fev) (i : Nat) (a : Anode) :
    Persistent (fsObsAt (GF := GF) γfs e i a) := by
  unfold fsObsAt; infer_instance

/-- (NI M3 private files FS-2a′) **AN OBSERVATION's RECEIPT WITH A FACT ON ITS
PREFIX**: `fsObsRcpt` whose prefix also satisfies `Φ` -- a parked read's
receipt names its offset as the prefix's fold offset (`off = fevOff h γo`) -/
def fsObsRcptP (γfs : FsNames) (e : Fev) (i : Nat) (n : FsNode) (Φ : List Fev → Prop) : IProp GF :=
  iprop(∃ h : List Fev, ⌜fevRows h i = ftopRow n ∧ Φ h⌝ ∗ fsEvRcpt γfs h e)

instance fsObsRcptP_persistent (γfs : FsNames) (e : Fev) (i : Nat) (n : FsNode) (Φ : List Fev → Prop) :
    Persistent (fsObsRcptP (GF := GF) γfs e i n Φ) := by
  unfold fsObsRcptP; infer_instance

/-- ...at the abstract row -/
def fsObsAtP (γfs : FsNames) (e : Fev) (i : Nat) (a : Anode) (Φ : List Fev → Prop) : IProp GF :=
  iprop(∃ h, ⌜fevRows h i = some (fnodeOf a.anNode, a.anNlink) ∧ Φ h⌝ ∗ fsEvRcpt γfs h e)

instance fsObsAtP_persistent (γfs : FsNames) (e : Fev) (i : Nat) (a : Anode) (Φ : List Fev → Prop) :
    Persistent (fsObsAtP (GF := GF) γfs e i a Φ) := by
  unfold fsObsAtP; infer_instance

theorem fsObsRcptP_at (γfs : FsNames) (e : Fev) (i : Nat) (n : FsNode) (Φ : List Fev → Prop)
    (hnz : fnType n ≠ 0) :
    fsObsRcptP (GF := GF) γfs e i n Φ ⊢ fsObsAtP γfs e i (absRow n) Φ := by
  unfold fsObsRcptP fsObsAtP
  iintro ⟨%h, %⟨hr, hΦ⟩, Hr⟩
  iexists h
  iframe Hr
  ipureintro; refine ⟨?_, hΦ⟩; rw [hr, ftopRow_typed n hnz]

/-- a fact-free receipt carries the trivial fact -/
theorem fsObsRcptP_of (γfs : FsNames) (e : Fev) (i : Nat) (n : FsNode) (Φ : List Fev → Prop)
    (hΦ : ∀ h, Φ h) : fsObsRcpt (GF := GF) γfs e i n ⊢ fsObsRcptP γfs e i n Φ := by
  unfold fsObsRcpt fsObsRcptP
  iintro ⟨%h, %hr, Hr⟩
  iexists h
  iframe Hr
  ipureintro; exact ⟨hr, hΦ h⟩

theorem fsObsRcpt_at (γfs : FsNames) (e : Fev) (i : Nat) (n : FsNode) (hnz : fnType n ≠ 0) :
    fsObsRcpt (GF := GF) γfs e i n ⊢ fsObsAt γfs e i (absRow n) := by
  unfold fsObsRcpt fsObsAt
  iintro ⟨%h, %hr, Hr⟩
  iexists h
  iframe Hr
  ipureintro; rw [hr, ftopRow_typed n hnz]

/-- **THE EXHAUSTION RECEIPT** (lane FS-0's name, anchored): actor `act`
found table `why` full, at a position of the era's ledger. -/
def fsFullRcpt (γfs : FsNames) (act : BitVec 64) (why : FsFull) : IProp GF :=
  iprop(∃ h : List Fev, fsEvRcpt γfs h (.full act why))

instance fsFullRcpt_persistent (γfs : FsNames) (act : BitVec 64) (why : FsFull) :
    Persistent (fsFullRcpt (GF := GF) γfs act why) := by
  unfold fsFullRcpt; infer_instance

/-- **THE APPEND**: the authority grows by `evs`, the new prefix's lower
bound out. -/
theorem fsLed_append (γfs : FsNames) (h evs : List Fev) :
    fsLedAuth (GF := GF) γfs h ⊢ |==> (fsLedAuth γfs (h ++ evs) ∗ fsLedLb γfs (h ++ evs)) := by
  unfold fsLedAuth fsLedLb
  iintro Ha
  iapply (MonoList.auth_own_update_app γfs.fev evs) $$ Ha

/-- a lower bound of a longer ledger is a lower bound of every prefix -/
theorem fsLedLb_prefix (γfs : FsNames) {h h' : List Fev} (hp : h <+: h') :
    fsLedLb (GF := GF) γfs h' ⊢ fsLedLb γfs h := by
  unfold fsLedLb
  iintro H
  iapply (MonoList.lb_own_le (GF := GF) γfs.fev h hp) $$ H

/-- a receipt inside a longer append's lower bound -/
theorem fsEvRcpt_of_lb (γfs : FsNames) (h t : List Fev) (e : Fev) :
    fsLedLb (GF := GF) γfs (h ++ e :: t) ⊢ fsEvRcpt γfs h e := by
  unfold fsEvRcpt
  apply fsLedLb_prefix
  exact ⟨t, by simp⟩

/-! ### The tracked offsets' shares (NI M3 private files FS-2a′)

A PARKED file's offset shadow is split ½ kernel (its off box) / ¼ user (the
row's invariant, `OffGv.offUserInv`) / ¼ LEDGER: the ledger holds, for every
shadow a parked install opened (`NiFs.fevPk`), a quarter at the FOLD's
offset.  So the fire that appends a parked `read`/`write` -- holding the
kernel's half at the real offset, inside the ledger's opening -- finds the
real offset EQUAL to the fold's (agreement), records it, and moves all three
shares to the advanced offset (`OffGv.offUserInv_move`): the recorded
offsets ARE the fold's (`NiFs.fevOffWf`, kept as the ledger's invariant).
The quarter is minted by the install (`ftopLed_pkOpen`, from the WHOLE
fresh shadow, which also refutes a second install of one shadow) and never
returned: after the last close the box is gone and nothing moves it.

The membership a fire needs (`γo ∈ fevPk h`) is witnessed by a lower bound
of the ledger's MIRROR at the `Icfg` name `icfgFev` (`fevPkWit`, carried by
the parked descriptor row `FdTable.foffRow`), which the ledger authority
keeps equal to the ledger. -/

/-- the ledger's quarters of the tracked shadows, at the fold's offsets -/
def fevShares (h : List Fev) : IProp GF :=
  [∗list] γ ∈ fevPk h, offGv γ (1 : Qp).half.half ((fevOff h γ : Nat) : Int)

instance fevShares_timeless (h : List Fev) : Timeless (fevShares (GF := GF) h) := by
  unfold fevShares; infer_instance

/-- **THE REGISTRATION WITNESS**: shadow `γo` was opened by a parked install
(a lower bound of the ledger's mirror naming it) -/
def fevPkWit [Icfg] (γo : GName) : IProp GF :=
  iprop(∃ L : List Fev, (icfgFev ↪◯ML L) ∗ ⌜γo ∈ fevPk L⌝)

instance fevPkWit_persistent [Icfg] (γo : GName) : Persistent (fevPkWit (GF := GF) γo) := by
  unfold fevPkWit; infer_instance

theorem fevPk_prefix_mem {L h : List Fev} (hp : L <+: h) {γo : GName} (hm : γo ∈ fevPk L) :
    γo ∈ fevPk h := by
  obtain ⟨t, rfl⟩ := hp
  unfold fevPk at hm ⊢
  rw [List.filterMap_append]
  exact List.mem_append_left _ hm

theorem fevPk_neutrals (h evs : List Fev) (hn : evs.all fevNeutral = true) :
    fevPk (h ++ evs) = fevPk h := by
  induction evs generalizing h with
  | nil => simp
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hn
    rw [show h ++ e :: es = (h ++ [e]) ++ es by simp, ih _ hn.2, fevPk_neutral h e hn.1]

theorem fevOff_neutrals (h evs : List Fev) (hn : evs.all fevNeutral = true) (γ : GName) :
    fevOff (h ++ evs) γ = fevOff h γ := by
  induction evs generalizing h with
  | nil => simp
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hn
    rw [show h ++ e :: es = (h ++ [e]) ++ es by simp, ih _ hn.2, fevOff_neutral h e hn.1]

theorem fevOffWf_neutrals (h evs : List Fev) (hn : evs.all fevNeutral = true) (hw : fevOffWf h) :
    fevOffWf (h ++ evs) := by
  induction evs generalizing h with
  | nil => simpa using hw
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hn
    rw [show h ++ e :: es = (h ++ [e]) ++ es by simp]
    exact ih _ hn.2 ((fevOffWf_snoc h e).2 ⟨hw, fevOffOk_neutral h e hn.1⟩)

/-- a neutral block leaves the shares as they are -/
theorem fevShares_neutrals (h evs : List Fev) (hn : evs.all fevNeutral = true) :
    fevShares (GF := GF) h ⊢ fevShares (h ++ evs) := by
  unfold fevShares
  rw [fevPk_neutrals h evs hn]
  refine BigSepL.bigSepL_mono fun {_ γ} _ => ?_
  rw [fevOff_neutrals h evs hn γ]

/-- **ONE SHARE OUT, ANOTHER VALUE BACK**: over a duplicate-free list, the
quarter at `γo` comes out at `f γo`, and the list goes back at `g`, which
agrees with `f` everywhere else -/
theorem fevShares_upd (L : List GName) (f g : GName → Nat) (γo : GName) (hm : γo ∈ L) (hnd : L.Nodup)
    (hfg : ∀ γ, γ ≠ γo → f γ = g γ) :
    ([∗list] γ ∈ L, offGv (GF := GF) γ (1 : Qp).half.half ((f γ : Nat) : Int)) ⊢
      offGv γo (1 : Qp).half.half ((f γo : Nat) : Int) ∗
      (offGv γo (1 : Qp).half.half ((g γo : Nat) : Int) -∗
        [∗list] γ ∈ L, offGv γ (1 : Qp).half.half ((g γ : Nat) : Int)) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  have hilt : i < L.length := (List.getElem?_eq_some_iff.mp hi).1
  have hne : ∀ {k : Nat} {γ : GName}, L[k]? = some γ → k ≠ i → γ ≠ γo := by
    intro k γ hk hki heq
    subst heq
    exact hki ((List.getElem?_inj hilt hnd).mp (hi.trans hk.symm)).symm
  refine (BigSepL.bigSepL_delete_cond hi).1.trans (sep_mono_right ?_)
  iintro Hrest Hg
  iapply (BigSepL.bigSepL_delete_cond hi).2
  iframe Hg
  iapply (BigSepL.bigSepL_mono (fun {k γ} hk => ?_)) $$ Hrest
  by_cases hki : k = i
  · rw [if_pos hki, if_pos hki]
  · rw [if_neg hki, if_neg hki, hfg γ (hne hk hki)]

/-- the ledger's quarter at `γo` refutes a WHOLE shadow at `γo` -/
theorem fevShares_whole (h : List Fev) (γo : GName) (z : Int) (hm : γo ∈ fevPk h) :
    ⊢@{IProp GF} fevShares h -∗ offGv γo 1 z -∗ False := by
  unfold fevShares
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  iintro Hs Hw
  icases (BigSepL.bigSepL_lookup_acc hi).1 $$ Hs with ⟨Hq, -⟩
  iapply offGv_whole_excl γo _ z _ $$ Hw Hq

/-- (NI M3 private files FS-1, FS-2a′) **THE LEDGER BESIDE THE MAP**: the
era's fs-event history, whose fold is the map's typed rows; (FS-2a′) its
MIRROR at `icfgFev`, kept equal to it; the recorded offsets ARE the fold's
(`fevOffWf`); and the ledger's quarter of every tracked shadow, at the
fold's offset. -/
def ftopLed [Icfg] (γfs : FsNames) (I : RegMapF FsNode) : IProp GF :=
  iprop(∃ h : List Fev, fsLedAuth γfs h ∗ (icfgFev ↪●ML h) ∗
    ⌜fevTie h I ∧ fevOffWf h ∧ (fevPk h).Nodup⌝ ∗ fevShares h)

instance ftopLed_timeless [Icfg] (γfs : FsNames) (I : RegMapF FsNode) : Timeless (ftopLed (GF := GF) γfs I) := by
  unfold ftopLed fsLedAuth; infer_instance

/-- **THE ERA's FIRST EVENT**: the empty ledger and its empty mirror take the
era's recovered rows (`ftopAlloc`) -/
theorem ftopLed_boot [Icfg] (γfs : FsNames) (I : RegMapF FsNode) :
    ⊢@{IProp GF} fsLedAuth γfs [] -∗ (icfgFev ↪●ML ([] : List Fev)) ==∗ ftopLed γfs I := by
  iintro Ha Hm
  imod fsLed_append γfs [] [.boot (ftopRows I)] $$ Ha with ⟨Ha, -⟩
  imod (MonoList.auth_own_update_app icfgFev [.boot (ftopRows I)]) $$ Hm with ⟨Hm, -⟩
  imodintro
  unfold ftopLed
  iexists [] ++ [.boot (ftopRows I)]
  iframe Ha Hm
  isplitr
  · ipureintro
    refine ⟨?_, (fevOffWf_snoc [] _).2 ⟨fevOffWf_nil, trivial⟩, by simp [fevPk, fevPkOf]⟩
    unfold fevTie fevRows fevRun; rfl
  · unfold fevShares
    simp only [List.nil_append, fevPk, List.filterMap_cons, fevPkOf, List.filterMap_nil]
    iapply BigSepL.bigSepL_nil.2
    iempintro

/-- **THE STEP**: a map move whose events keep the tie appends them -- at
NEUTRAL events (no parked install, read or write: those move the shares,
`ftopLed_pkOpen` / `ftopLed_pkAdv`); the receipt is the prefix the events
followed and the lower bound past them. -/
theorem ftopLed_step [Icfg] (γfs : FsNames) (I I' : RegMapF FsNode) (evs : List Fev)
    (hneu : evs.all fevNeutral = true)
    (hstep : ∀ h, fevTie h I → fevTie (h ++ evs) I') :
    ftopLed (GF := GF) γfs I ⊢ |==> (ftopLed γfs I' ∗ ∃ h : List Fev, ⌜fevTie h I⌝ ∗ fsLedLb γfs (h ++ evs)) := by
  unfold ftopLed
  iintro ⟨%h, Ha, Hm, %⟨ht, hw, hnd⟩, Hs⟩
  imod fsLed_append γfs h evs $$ Ha with ⟨Ha, #Hlb⟩
  imod (MonoList.auth_own_update_app icfgFev evs) $$ Hm with ⟨Hm, -⟩
  ihave Hs := fevShares_neutrals h evs hneu $$ Hs
  imodintro
  isplitl [Ha Hm Hs]
  · iexists h ++ evs
    iframe Ha Hm Hs
    ipureintro
    exact ⟨hstep h ht, fevOffWf_neutrals h evs hneu hw, by rw [fevPk_neutrals h evs hneu]; exact hnd⟩
  · iexists h
    iframe Hlb
    ipureintro; exact ht

/-- (NI M3 FS-2b) the empty lower bound -/
theorem fsLedLb_nil (γfs : FsNames) : ⊢@{IProp GF} |==> fsLedLb γfs [] := by
  unfold fsLedLb
  exact MonoList.lb_own_nil γfs.fev

/-- (NI M3 FS-2b) a lower bound is a prefix of the authority -/
theorem fsLedAuth_lb_valid (γfs : FsNames) (h L : List Fev) :
    ⊢@{IProp GF} fsLedAuth γfs h -∗ fsLedLb γfs L -∗ ⌜L <+: h⌝ := by
  unfold fsLedAuth fsLedLb
  iintro Ha HL
  ihave %hv := MonoList.auth_lb_own_valid (GF := GF) γfs.fev (DFrac.own 1) h L $$ Ha HL
  ipureintro; exact hv.2

/-- (NI M3 FS-2a′) **EVERY LOWER BOUND OF THE LEDGER IS WELL-FORMED**: the
recorded offsets of any prefix a receipt names are the fold's
(`fevOffWf` is prefix-closed) -/
theorem ftopLed_lb_wf [Icfg] (γfs : FsNames) (I : RegMapF FsNode) (L : List Fev) :
    ⊢@{IProp GF} fsLedLb γfs L -∗ ftopLed γfs I -∗ ⌜fevOffWf L⌝ ∗ ftopLed γfs I := by
  iintro #HL Hl
  unfold ftopLed
  icases Hl with ⟨%h, Ha, Hm, %⟨ht, hw, hnd⟩, Hs⟩
  ihave %hv := fsLedAuth_lb_valid γfs h L $$ Ha HL
  isplitr
  · ipureintro; exact fevOffWf_prefix hv hw
  iexists h
  iframe Ha Hm Hs
  ipureintro; exact ⟨ht, hw, hnd⟩

/-- (NI M3 FS-2b) **AN OBSERVATION APPENDED AFTER A LOWER BOUND THE CALLER
HOLDS**: the authority is checked against `L` (`MonoList.auth_lb_own_valid`),
so the event lands past it -- what makes a back-pointer into `L` point
strictly earlier. -/
theorem ftopLed_obsAfter [Icfg] (γfs : FsNames) (I : RegMapF FsNode) (e : Fev) (he : fevObs e) (L : List Fev) :
    ⊢@{IProp GF} fsLedLb γfs L -∗ ftopLed γfs I ==∗
      ftopLed γfs I ∗ ∃ h : List Fev, ⌜fevTie h I ∧ L <+: h⌝ ∗ fsLedLb γfs (h ++ [e]) := by
  iintro #HL Hl
  unfold ftopLed
  icases Hl with ⟨%h, Ha, Hm, %⟨ht, hw, hnd⟩, Hs⟩
  ihave %hv := fsLedAuth_lb_valid γfs h L $$ Ha HL
  have hn : [e].all fevNeutral = true := by simp [fevNeutral_obs e he]
  imod fsLed_append γfs h [e] $$ Ha with ⟨Ha, #Hlb⟩
  imod (MonoList.auth_own_update_app icfgFev [e]) $$ Hm with ⟨Hm, -⟩
  ihave Hs := fevShares_neutrals h [e] hn $$ Hs
  imodintro
  isplitl [Ha Hm Hs]
  · iexists h ++ [e]
    iframe Ha Hm Hs
    ipureintro
    exact ⟨fevTie_obs e he ht, fevOffWf_neutrals h [e] hn hw, by rw [fevPk_neutrals h [e] hn]; exact hnd⟩
  · iexists h
    iframe Hlb
    ipureintro; exact ⟨ht, hv⟩

/-- an observation appended -/
theorem ftopLed_obs [Icfg] (γfs : FsNames) (I : RegMapF FsNode) (e : Fev) (he : fevObs e) :
    ftopLed (GF := GF) γfs I ⊢ |==> (ftopLed γfs I ∗ ∃ h : List Fev, ⌜fevTie h I⌝ ∗ fsEvRcpt γfs h e) := by
  iintro Hl
  imod ftopLed_step γfs I I [e] (by simp [fevNeutral_obs e he]) (fun h ht => fevTie_obs e he ht) $$ Hl
    with ⟨Hl, Hr⟩
  imodintro
  iframe Hl
  unfold fsEvRcpt
  iexact Hr

/-- an observation at row `i`, the record the observer holds -/
theorem ftopLed_obsAt [Icfg] (γfs : FsNames) (I : RegMapF FsNode) (e : Fev) (he : fevObs e) (i : Nat)
    (n : FsNode) (hi : PartialMap.get? I i = some n) :
    ftopLed (GF := GF) γfs I ⊢ |==> (ftopLed γfs I ∗ fsObsRcpt γfs e i n) := by
  iintro Hl
  imod ftopLed_obs γfs I e he $$ Hl with ⟨Hl, ⟨%h, %ht, #Hr⟩⟩
  imodintro
  iframe Hl
  unfold fsObsRcpt
  iexists h
  iframe Hr
  ipureintro; exact fevTie_row i n ht hi

/-- a move at row `i` from record `n`, its receipt out -/
theorem ftopLed_moveAt [Icfg] (γfs : FsNames) (I : RegMapF FsNode) (i : Nat) (n n' : FsNode) (evs : List Fev)
    (hi : PartialMap.get? I i = some n) (hneu : evs.all fevNeutral = true)
    (hstep : ∀ h, fevTie h I → fevTie (h ++ evs) (PartialMap.insert I i n')) :
    ftopLed (GF := GF) γfs I ⊢
      |==> (ftopLed γfs (PartialMap.insert I i n') ∗ fsMoveRcpt γfs evs i n) := by
  iintro Hl
  imod ftopLed_step γfs I _ evs hneu hstep $$ Hl with ⟨Hl, ⟨%h, %ht, #Hr⟩⟩
  imodintro
  iframe Hl
  unfold fsMoveRcpt
  iexists h
  iframe Hr
  ipureintro; exact fevTie_row i n ht hi

/-- (NI M3 private files FS-2e) **A MOVE's RECEIPT PAST A BOUND THE MOVER
HELD**: `fsMoveRcpt` whose prefix extends `L` (the authority checked against
`L` at the move's instant) -- what orders a syscall's own events -/
def fsMoveRcptAfter (γfs : FsNames) (L : List Fev) (evs : List Fev) (i : Nat) (n : FsNode) : IProp GF :=
  iprop(∃ h : List Fev, ⌜L <+: h ∧ fevRows h i = ftopRow n⌝ ∗ fsLedLb γfs (h ++ evs))

instance fsMoveRcptAfter_persistent (γfs : FsNames) (L evs : List Fev) (i : Nat) (n : FsNode) :
    Persistent (fsMoveRcptAfter (GF := GF) γfs L evs i n) := by
  unfold fsMoveRcptAfter; infer_instance

/-- (NI M3 private files FS-2e) a move at row `i` APPENDED PAST a lower bound
the caller holds -/
theorem ftopLed_moveAtAfter [Icfg] (γfs : FsNames) (I : RegMapF FsNode) (i : Nat) (n n' : FsNode)
    (evs : List Fev) (L : List Fev)
    (hi : PartialMap.get? I i = some n) (hneu : evs.all fevNeutral = true)
    (hstep : ∀ h, fevTie h I → fevTie (h ++ evs) (PartialMap.insert I i n')) :
    ⊢@{IProp GF} fsLedLb γfs L -∗ ftopLed γfs I ==∗
      ftopLed γfs (PartialMap.insert I i n') ∗ fsMoveRcptAfter γfs L evs i n := by
  iintro #HL Hl
  unfold ftopLed
  icases Hl with ⟨%h, Ha, Hm, %⟨ht, hw, hnd⟩, Hs⟩
  ihave %hv := fsLedAuth_lb_valid γfs h L $$ Ha HL
  imod fsLed_append γfs h evs $$ Ha with ⟨Ha, #Hlb⟩
  imod (MonoList.auth_own_update_app icfgFev evs) $$ Hm with ⟨Hm, -⟩
  ihave Hs := fevShares_neutrals h evs hneu $$ Hs
  imodintro
  isplitl [Ha Hm Hs]
  · iexists h ++ evs
    iframe Ha Hm Hs
    ipureintro
    exact ⟨hstep h ht, fevOffWf_neutrals h evs hneu hw, by rw [fevPk_neutrals h evs hneu]; exact hnd⟩
  · unfold fsMoveRcptAfter
    iexists h
    iframe Hlb
    ipureintro; exact ⟨hv, fevTie_row i n ht hi⟩

/-- (NI M3 private files FS-2e) **A VERDICT PAST A POSITION**: `full act why`
at a position at least `lo` -/
def fsFullAfter (γfs : FsNames) (act : BitVec 64) (why : FsFull) (lo : Nat) : IProp GF :=
  iprop(∃ h : List Fev, ⌜lo ≤ h.length⌝ ∗ fsEvRcpt γfs h (.full act why))

instance fsFullAfter_persistent (γfs : FsNames) (act : BitVec 64) (why : FsFull) (lo : Nat) :
    Persistent (fsFullAfter (GF := GF) γfs act why lo) := by
  unfold fsFullAfter; infer_instance

theorem fsFullAfter_rcpt (γfs : FsNames) (act : BitVec 64) (why : FsFull) (lo : Nat) :
    fsFullAfter (GF := GF) γfs act why lo ⊢ fsFullRcpt γfs act why := by
  unfold fsFullAfter fsFullRcpt
  iintro ⟨%h, -, Hr⟩
  iexists h; iexact Hr

/-- (NI M3 private files FS-2e) an exhaustion verdict appended past a lower
bound the caller holds -/
theorem ftopLed_fullAfter [Icfg] (γfs : FsNames) (I : RegMapF FsNode) (act : BitVec 64) (why : FsFull)
    (L : List Fev) :
    ⊢@{IProp GF} fsLedLb γfs L -∗ ftopLed γfs I ==∗ ftopLed γfs I ∗ fsFullAfter γfs act why L.length := by
  iintro #HL Hl
  imod ftopLed_obsAfter γfs I (.full act why) trivial L $$ HL Hl with ⟨Hl, ⟨%h, %⟨-, hv⟩, #Hr⟩⟩
  imodintro
  iframe Hl
  unfold fsFullAfter fsEvRcpt
  iexists h
  iframe Hr
  ipureintro; exact hv.length_le

/-- an exhaustion verdict recorded at its instant -/
theorem ftopLed_full [Icfg] (γfs : FsNames) (I : RegMapF FsNode) (act : BitVec 64) (why : FsFull) :
    ftopLed (GF := GF) γfs I ⊢ |==> (ftopLed γfs I ∗ fsFullRcpt γfs act why) := by
  iintro Hl
  imod ftopLed_obs γfs I (.full act why) trivial $$ Hl with ⟨Hl, ⟨%h, -, #Hr⟩⟩
  imodintro
  iframe Hl
  unfold fsFullRcpt
  iexists h
  iexact Hr

/-- (NI M3 FS-2a′) **THE PARKED INSTALL**: a parked open's install appended
after a lower bound the caller holds, the WHOLE fresh shadow at offset 0 in
hand (which refutes a second install of one shadow: the ledger would hold a
quarter of it).  The ledger keeps a quarter; the kernel's half and the
row's quarter come back, with the registration witness. -/
theorem ftopLed_pkOpen [Icfg] (γfs : FsNames) (I : RegMapF FsNode) (a : BitVec 64) (i : Nat)
    (γo : GName) (po : Option Nat) (L : List Fev) :
    ⊢@{IProp GF} fsLedLb γfs L -∗ offGv γo 1 0 -∗ ftopLed γfs I ==∗
      ftopLed γfs I ∗ offGv γo (1 : Qp).half 0 ∗ offGv γo (1 : Qp).half.half 0 ∗ fevPkWit γo ∗
      ∃ h : List Fev, ⌜fevTie h I ∧ L <+: h⌝ ∗ fsLedLb γfs (h ++ [.open a i γo false po]) := by
  iintro #HL Hw Hl
  unfold ftopLed
  icases Hl with ⟨%h, Ha, Hm, %⟨ht, hw, hnd⟩, Hs⟩
  ihave %hv := fsLedAuth_lb_valid γfs h L $$ Ha HL
  by_cases hm : γo ∈ fevPk h
  · iexfalso
    iapply fevShares_whole h γo 0 hm $$ Hs Hw
  icases (offGv_whole3 γo 0).1 $$ Hw with ⟨Hk, Hq, Hu⟩
  have hpk : fevPk (h ++ [.open a i γo false po]) = fevPk h ++ [γo] := by
    rw [fevPk_snoc]; rfl
  imod fsLed_append γfs h [.open a i γo false po] $$ Ha with ⟨Ha, #Hlb⟩
  imod (MonoList.auth_own_update_app icfgFev [.open a i γo false po]) $$ Hm with ⟨Hm, #Hmb⟩
  imodintro
  iframe Hk Hu
  isplitl [Ha Hm Hs Hq]
  · iexists h ++ [.open a i γo false po]
    iframe Ha Hm
    isplitr
    · ipureintro
      refine ⟨fevTie_open a i γo false po ht, (fevOffWf_snoc h _).2 ⟨hw, trivial⟩, ?_⟩
      rw [hpk, List.nodup_append]
      exact ⟨hnd, by simp, fun x hx y hy => by
        simp at hy; subst hy; intro e; subst e; exact hm hx⟩
    · unfold fevShares
      rw [hpk]
      iapply BigSepL.bigSepL_snoc.2
      isplitl [Hs]
      · iapply (BigSepL.bigSepL_mono (fun {k γ} hk => ?_)) $$ Hs
        have hne : γ ≠ γo := fun e => hm (e ▸ List.mem_of_getElem? hk)
        rw [fevOff_pkOpen, if_neg hne]
      · rw [fevOff_pkOpen, if_pos rfl]
        iexact Hq
  isplitr
  · unfold fevPkWit
    iexists h ++ [.open a i γo false po]
    iframe Hmb
    ipureintro; rw [hpk]; simp
  iexists h
  iframe Hlb
  ipureintro; exact ⟨ht, hv⟩

/-- (NI M3 FS-2a′) **THE PARKED ADVANCE**: a parked read or write of `γo`
at the offset `off` the kernel's half holds, advancing it by `d` -- inside
the ledger's opening, the registration witness finds the ledger's quarter,
which AGREES with the kernel's half (`off` is the fold's offset); the event
is appended, and all three shares (the kernel's half, the ledger's quarter,
the row's quarter in its invariant) move to `off + d`. -/
theorem ftopLed_pkAdvAfter [Icfg] {hlc : HasLC} [MachGS hlc GF] (E : CoPset) (hE : (↑foffN : CoPset) ⊆ E)
    (γfs : FsNames) (I I' : RegMapF FsNode) (γo : GName) (off d : Nat) (e : Fev)
    (hpk : fevPkOf e = none)
    (hoff : ∀ h γ, fevOff (h ++ [e]) γ = if γ = γo then off + d else fevOff h γ)
    (hok : ∀ h, off = fevOff h γo → fevOffOk h e)
    (hstep : ∀ h, fevTie h I → fevTie (h ++ [e]) I') (L : List Fev) :
    ⊢@{IProp GF} fsLedLb γfs L -∗ fevPkWit γo -∗ offUserInv (hlc := hlc) γo -∗ offGv γo (1 : Qp).half (off : Int) -∗
      ftopLed γfs I ={E}=∗
      ftopLed γfs I' ∗ offGv γo (1 : Qp).half ((off + d : Nat) : Int) ∗
      ∃ h : List Fev, ⌜fevTie h I ∧ off = fevOff h γo ∧ L <+: h⌝ ∗ fsLedLb γfs (h ++ [e]) := by
  iintro #HL #Hwit #Hinv Hk Hl
  unfold ftopLed
  icases Hl with ⟨%h, Ha, Hm, %⟨ht, hw, hnd⟩, Hs⟩
  ihave %hvL := fsLedAuth_lb_valid γfs h L $$ Ha HL
  unfold fevPkWit
  icases Hwit with ⟨%L, #HmL, %hmL⟩
  ihave %hv := MonoList.auth_lb_own_valid (GF := GF) icfgFev (DFrac.own 1) h L $$ Hm HmL
  have hm : γo ∈ fevPk h := fevPk_prefix_mem hv.2 hmL
  have hpk' : fevPk (h ++ [e]) = fevPk h := by rw [fevPk_snoc, hpk]; simp
  unfold fevShares
  icases fevShares_upd (fevPk h) (fevOff h) (fevOff (h ++ [e])) γo hm hnd
    (fun γ hne => by rw [hoff, if_neg hne]) $$ Hs with ⟨Hq, Hback⟩
  imod offUserInv_move E γo (off : Int) ((fevOff h γo : Nat) : Int) ((off + d : Nat) : Int) hE $$
    Hinv Hk Hq with ⟨%heq, Hk, Hq⟩
  have hoff0 : off = fevOff h γo := by exact_mod_cast heq.symm
  imod fsLed_append γfs h [e] $$ Ha with ⟨Ha, #Hlb⟩
  imod (MonoList.auth_own_update_app icfgFev [e]) $$ Hm with ⟨Hm, -⟩
  imodintro
  iframe Hk
  isplitl [Ha Hm Hq Hback]
  · iexists h ++ [e]
    iframe Ha Hm
    isplitr
    · ipureintro
      exact ⟨hstep h ht, (fevOffWf_snoc h e).2 ⟨hw, hok h hoff0⟩, by rw [hpk']; exact hnd⟩
    · rw [hpk']
      iapply Hback
      rw [hoff, if_pos rfl]
      iexact Hq
  iexists h
  iframe Hlb
  ipureintro; exact ⟨ht, hoff0, hvL⟩

/-- (NI M3 FS-2a′) **THE PARKED ADVANCE**, with no bound (`ftopLed_pkAdvAfter`
at the empty one) -/
theorem ftopLed_pkAdv [Icfg] {hlc : HasLC} [MachGS hlc GF] (E : CoPset) (hE : (↑foffN : CoPset) ⊆ E)
    (γfs : FsNames) (I I' : RegMapF FsNode) (γo : GName) (off d : Nat) (e : Fev)
    (hpk : fevPkOf e = none)
    (hoff : ∀ h γ, fevOff (h ++ [e]) γ = if γ = γo then off + d else fevOff h γ)
    (hok : ∀ h, off = fevOff h γo → fevOffOk h e)
    (hstep : ∀ h, fevTie h I → fevTie (h ++ [e]) I') :
    ⊢@{IProp GF} fevPkWit γo -∗ offUserInv (hlc := hlc) γo -∗ offGv γo (1 : Qp).half (off : Int) -∗
      ftopLed γfs I ={E}=∗
      ftopLed γfs I' ∗ offGv γo (1 : Qp).half ((off + d : Nat) : Int) ∗
      ∃ h : List Fev, ⌜fevTie h I ∧ off = fevOff h γo⌝ ∗ fsLedLb γfs (h ++ [e]) := by
  iintro #Hwit #Hinv Hk Hl
  imod fsLedLb_nil γfs with #H0
  imod ftopLed_pkAdvAfter E hE γfs I I' γo off d e hpk hoff hok hstep [] $$ H0 Hwit Hinv Hk Hl
    with ⟨Hl, Hk, ⟨%h, %⟨ht, ho, -⟩, #Hr⟩⟩
  imodintro
  iframe Hl Hk
  iexists h
  iframe Hr
  ipureintro; exact ⟨ht, ho⟩

/-- (NI M3 FS-2a′) a parked READ: the advance's three facts -/
theorem fevPkRead_facts (a : BitVec 64) (i : Nat) (γo : GName) (off d : Nat) :
    fevPkOf (.read a i γo false off d) = none ∧
    (∀ h γ, fevOff (h ++ [.read a i γo false off d]) γ = if γ = γo then off + d else fevOff h γ) ∧
    (∀ h, off = fevOff h γo → fevOffOk h (.read a i γo false off d)) :=
  ⟨rfl, fun h γ => fevOff_pkRead h a i γo off d γ, fun _ h => h⟩

/-- (NI M3 FS-2a′) a parked CHUNK: the advance's three facts -/
theorem fevPkWrite_facts (a : BitVec 64) (i : Nat) (γo : GName) (off : Nat) (bs : List (BitVec 8)) (r : Nat) :
    fevPkOf (.write a i γo false off bs r) = none ∧
    (∀ h γ, fevOff (h ++ [.write a i γo false off bs r]) γ = if γ = γo then off + r else fevOff h γ) ∧
    (∀ h, off = fevOff h γo → fevOffOk h (.write a i γo false off bs r)) :=
  ⟨rfl, fun h γ => fevOff_pkWrite h a i γo off bs r γ, fun _ h => h⟩

/-- a move whose typed row is unchanged appends nothing -/
theorem fevTie_same {h : List Fev} {I : RegMapF FsNode} (i : Nat) (n n' : FsNode)
    (hi : PartialMap.get? I i = some n) (hrow : ftopRow n = ftopRow n') (ht : fevTie h I) :
    fevTie h (PartialMap.insert I i n') := by
  have h1 := fevTie_move (evs := []) i n' ht (by
    rw [List.append_nil, ← hrow, ← fevTie_row i n ht hi, frowsSet_self])
  simpa using h1


/-! ### The receipts the syscall posts carry (FS-1's relay)

A post names only the events: `fsLedAt γfs evs` is "the block `evs` sits
contiguously in the era's ledger", the shape every relay uses (a move's
legs, a chunk, an observation). -/

def fsLedAt (γfs : FsNames) (evs : List Fev) : IProp GF :=
  iprop(∃ h : List Fev, fsLedLb γfs (h ++ evs))

instance fsLedAt_persistent (γfs : FsNames) (evs : List Fev) :
    Persistent (fsLedAt (GF := GF) γfs evs) := by
  unfold fsLedAt; infer_instance

/-- (NI M3 private files FS-2e) **AN EVENT AT A POSITION**: `e` is the
ledger's event at index `q` -/
def fsLedPos (γfs : FsNames) (q : Nat) (e : Fev) : IProp GF :=
  iprop(∃ h : List Fev, ⌜h.length = q⌝ ∗ fsLedLb γfs (h ++ [e]))

instance fsLedPos_persistent (γfs : FsNames) (q : Nat) (e : Fev) :
    Persistent (fsLedPos (GF := GF) γfs q e) := by
  unfold fsLedPos; infer_instance

theorem fsMoveRcpt_at (γfs : FsNames) (evs : List Fev) (i : Nat) (n : FsNode) :
    fsMoveRcpt (GF := GF) γfs evs i n ⊢ fsLedAt γfs evs := by
  unfold fsMoveRcpt fsLedAt
  iintro ⟨%h, -, Hr⟩
  iexists h; iexact Hr

theorem fsObsRcpt_at' (γfs : FsNames) (e : Fev) (i : Nat) (n : FsNode) :
    fsObsRcpt (GF := GF) γfs e i n ⊢ fsLedAt γfs [e] := by
  unfold fsObsRcpt fsLedAt fsEvRcpt
  iintro ⟨%h, -, Hr⟩
  iexists h; iexact Hr

theorem fsEvRcpt_at (γfs : FsNames) (h : List Fev) (e : Fev) :
    fsEvRcpt (GF := GF) γfs h e ⊢ fsLedAt γfs [e] := by
  unfold fsEvRcpt fsLedAt
  iintro Hr
  iexists h; iexact Hr

/-- a write event's advance (`0` for every other event) -/
def fevWriteR : Fev → Nat
  | .write _ _ _ _ _ _ r => r
  | _ => 0

/-- the chunks' total advance (FS-2e: the chunks are POSITIONED, `(q, e)`) -/
def fwSum (cs : List (Nat × Fev)) : Nat := (cs.map (fun c => fevWriteR c.2)).sum

theorem fwSum_append (cs cs' : List (Nat × Fev)) : fwSum (cs ++ cs') = fwSum cs + fwSum cs' := by
  unfold fwSum; simp

/-- (NI M3 private files FS-1) the arm event of `i` by `act`, in the era's ledger -/
def creArmRcpt (γfs : FsNames) (act : BitVec 64) (i : Nat) : IProp GF :=
  iprop(∃ n : Fnode, fsLedAt γfs [.arm act i n])

instance creArmRcpt_persistent (γfs : FsNames) (act : BitVec 64) (i : Nat) :
    Persistent (creArmRcpt (GF := GF) γfs act i) := by
  unfold creArmRcpt; infer_instance

/-- (NI M3 private files FS-1, FS-2e) **THE PARENT LEG BY `act`, AFTER THE
ARM**: the entry `nm ↦ i` set in `d` and `d`'s count, one block in the era's
ledger, past the made child's arm `arm act i n` (the leg fired past the arm's
lower bound) -/
def creParentRcpt (γfs : FsNames) (act : BitVec 64) (nm : List (BitVec 8)) (i : Nat) : IProp GF :=
  iprop(∃ (n : Fnode) (h h' : List Fev) (d nl : Nat), ⌜h ++ [.arm act i n] <+: h'⌝ ∗
    fsLedLb γfs (h ++ [.arm act i n]) ∗ fsLedLb γfs (h' ++ [.ent act d nm (some i), .nlink act d nl]))

instance creParentRcpt_persistent (γfs : FsNames) (act : BitVec 64) (nm : List (BitVec 8)) (i : Nat) :
    Persistent (creParentRcpt (GF := GF) γfs act nm i) := by
  unfold creParentRcpt; infer_instance

/-- (FS-2e) the leg's receipt from the arm's and the leg fire's past it -/
theorem creParentRcpt_of (γfs : FsNames) (act : BitVec 64) (nm : List (BitVec 8)) (i d nl : Nat)
    (n : Fnode) (h : List Fev) (np : FsNode) :
    fsLedLb (GF := GF) γfs (h ++ [.arm act i n]) ⊢
      fsMoveRcptAfter γfs (h ++ [.arm act i n]) [.ent act d nm (some i), .nlink act d nl] d np -∗
      creParentRcpt γfs act nm i := by
  unfold fsMoveRcptAfter creParentRcpt
  iintro #Ha ⟨%h', %⟨hv, -⟩, #Hl⟩
  iexists n, h, h', d, nl
  iframe Ha Hl
  ipureintro; exact hv

/-- (NI M3 private files FS-2b′, FS-2e) a FOUND node's lookup hop by `act`
of the name `nm`, at a position whose prefix's fold reads the parent `d` as
a directory naming `nm ↦ i` (the observation's receipt, the found entry read
off it) -/
def creFoundRcpt (γfs : FsNames) (act : BitVec 64) (nm : List (BitVec 8)) (i : Nat) : IProp GF :=
  iprop(∃ (h : List Fev) (d : Nat) (e : Std.ExtTreeMap (List (BitVec 8)) Nat compare) (nl : Nat),
    ⌜fevRows h d = some (.dir e, nl) ∧ e[nm]? = some i⌝ ∗ fsLedLb γfs (h ++ [.hop act d nm none]))

instance creFoundRcpt_persistent (γfs : FsNames) (act : BitVec 64) (nm : List (BitVec 8)) (i : Nat) :
    Persistent (creFoundRcpt (GF := GF) γfs act nm i) := by
  unfold creFoundRcpt; infer_instance

/-- a directory's lookup observation, its entry read: the found receipt -/
theorem fsObsRcpt_found (γfs : FsNames) (act : BitVec 64) (d i : Nat) (nm : List (BitVec 8))
    (n : FsNode) (hd : fnIsDir n = true) (hnm : (dirEntries n)[nm]? = some i) :
    fsObsRcpt (GF := GF) γfs (.hop act d nm none) d n ⊢ creFoundRcpt γfs act nm i := by
  unfold fsObsRcpt fsEvRcpt creFoundRcpt
  iintro ⟨%h, %hr, #Hr⟩
  iexists h, d, dirEntries n, fnNlink n
  iframe Hr
  ipureintro
  refine ⟨?_, hnm⟩
  rw [hr, ftopRow_typed n (fnIsDir_typed n hd), absRow_dir_eq n hd]
  rfl

/-- (NI M3 private files FS-1, FS-2e) **CREATE'S LEDGER RECEIPT** on a
success, at the entry name `nm`: a MADE child's arm and, after it, its
parent leg filing `nm`; or a FOUND node's lookup hop of `nm` (FS-2b′: at its
parent's entry). -/
def creOkRcpt (γfs : FsNames) (act : BitVec 64) (made : Bool) (nm : List (BitVec 8)) (i : Nat) : IProp GF :=
  iprop((⌜made = true⌝ ∗ creParentRcpt γfs act nm i) ∨
    (⌜made = false⌝ ∗ creFoundRcpt γfs act nm i))

instance creOkRcpt_persistent (γfs : FsNames) (act : BitVec 64) (made : Bool) (nm : List (BitVec 8))
    (i : Nat) : Persistent (creOkRcpt (GF := GF) γfs act made nm i) := by
  unfold creOkRcpt; infer_instance

/-- (NI M3 private files FS-2e) **CREATE'S EVENTS INSIDE A PREFIX**: a made
child's arm by `act`, then its parent leg filing `nm ↦ i`; or a found node's
lookup of `nm`, at a prefix whose fold names `nm ↦ i` in the parent -- all
of it inside `H` -/
def creOkIn (act : BitVec 64) (made : Bool) (nm : List (BitVec 8)) (i : Nat) (H : List Fev) : Prop :=
  if made then
    ∃ (n : Fnode) (h h' : List Fev) (d nl : Nat),
      h ++ [.arm act i n] <+: h' ∧ h' ++ [.ent act d nm (some i), .nlink act d nl] <+: H
  else
    ∃ (h : List Fev) (d : Nat) (e : Std.ExtTreeMap (List (BitVec 8)) Nat compare) (nl : Nat),
      fevRows h d = some (.dir e, nl) ∧ e[nm]? = some i ∧ h ++ [.hop act d nm none] <+: H

theorem creOkIn_mono {act : BitVec 64} {made : Bool} {nm : List (BitVec 8)} {i : Nat} {H H' : List Fev}
    (hp : H <+: H') (h : creOkIn act made nm i H) : creOkIn act made nm i H' := by
  unfold creOkIn at h ⊢
  cases made with
  | true =>
    simp only [if_true] at h ⊢
    obtain ⟨n, h1, h2, d, nl, ha, hb⟩ := h
    exact ⟨n, h1, h2, d, nl, ha, hb.trans hp⟩
  | false =>
    simp only [Bool.false_eq_true, if_false] at h ⊢
    obtain ⟨h1, d, e, nl, hr, he, hb⟩ := h
    exact ⟨h1, d, e, nl, hr, he, hb.trans hp⟩

/-- (NI M3 private files FS-2b′) **WHAT FIXED create's INODE**, in the
ledger: a made child's arm, or a found node's hop at its parent's entry
(`fevOpenFixed`'s O_CREATE side; the walk's start and names unread); (FS-2e)
read at a lower bound that holds ALL of create's events (a made child's
ENDS IN ITS PARENT LEG), so what lands past it lands past the whole create -/
theorem creOkRcpt_fixed (γfs : FsNames) (act : BitVec 64) (made : Bool) (nm : List (BitVec 8)) (i : Nat)
    (rt s0 : Nat) (es : List (List (BitVec 8))) :
    creOkRcpt (GF := GF) γfs act made nm i ⊢
      ∃ (H : List Fev) (p : Nat), fsLedLb γfs H ∗
        ⌜fevOpenFixed H act rt s0 es true i (some p) = true ∧ creOkIn act made nm i H⌝ := by
  unfold creOkRcpt creParentRcpt creFoundRcpt
  iintro (⟨%hm, ⟨%n, %h, %h', %d, %nl, %hv, -, #Hl⟩⟩ | ⟨%hm, ⟨%h, %d, %e, %nl, %⟨hr, hnm⟩, #Hh⟩⟩)
  · iexists h' ++ [.ent act d nm (some i), .nlink act d nl], h.length
    iframe Hl
    ipureintro
    have h0 : fevOpenFixed (h ++ [.arm act i n]) act rt s0 es true i (some h.length) = true := by
      simp [fevOpenFixed]
    refine ⟨fevOpenFixed_mono (hv.trans (List.prefix_append _ _)) h0, ?_⟩
    subst hm
    exact ⟨n, h, h', d, nl, hv, List.prefix_refl _⟩
  · iexists h ++ [.hop act d nm none], h.length
    iframe Hh
    ipureintro
    refine ⟨by simp [fevOpenFixed, List.take_left' rfl, hr, hnm], ?_⟩
    subst hm
    exact ⟨h, d, e, nl, hr, hnm, List.prefix_refl _⟩

/-- (NI M3 private files FS-1) unlink's parent leg by `act`: the entry
removed from `d` and `d`'s count, one block -/
def unlParentRcpt (γfs : FsNames) (act : BitVec 64) : IProp GF :=
  iprop(∃ (d : Nat) (nm : List (BitVec 8)) (nl : Nat),
    fsLedAt γfs [.ent act d nm none, .nlink act d nl])

instance unlParentRcpt_persistent (γfs : FsNames) (act : BitVec 64) :
    Persistent (unlParentRcpt (GF := GF) γfs act) := by
  unfold unlParentRcpt; infer_instance

/-- (NI M3 private files FS-1) **UNLINK'S LEDGER RECEIPT**, relayed to the
post: a `0` answer names the parent leg and the target's count by `act` -/
def unlinkRcptAt (γfs : FsNames) (act : BitVec 64) (r : BitVec 64) : IProp GF :=
  iprop(⌜r ≠ 0#64⌝ ∨ unlParentRcpt γfs act ∗
    ∃ (t nl : Nat), fsLedAt γfs [.nlink act t nl])

instance unlinkRcptAt_persistent (γfs : FsNames) (act r : BitVec 64) :
    Persistent (unlinkRcptAt (GF := GF) γfs act r) := by
  unfold unlinkRcptAt; infer_instance

theorem unlinkRcptAt_m1 (γfs : FsNames) (act r : BitVec 64) (h : r ≠ 0#64) :
    ⊢@{IProp GF} unlinkRcptAt γfs act r := by
  unfold unlinkRcptAt; ileft; ipureintro; exact h

end Res

end Xv6
