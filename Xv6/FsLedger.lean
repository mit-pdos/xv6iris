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
-/
import Xv6.NiFs
import Xv6.FsAbsDefs
import Xv6.FsBlocks
import Xv6.UartTrace

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

theorem fevRows_write (h : List Fev) (a : BitVec 64) (i : Nat) (γo : GName) (off : Nat)
    (bs : List (BitVec 8)) (r : Nat) :
    fevRows (h ++ [.write a i γo off bs r]) = frowsSet (fevRows h) i (frowWrite off bs (fevRows h i)) := by
  rw [fevRows_snoc]; rfl

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
theorem fevTie_write (γo : GName) (off : Nat) (bs bs0 : List (BitVec 8)) (nl r : Nat)
    (ht : fevTie h I) (hi : PartialMap.get? I i = some n)
    (hnz : fnType n ≠ 0) (habs : absRow n = ⟨.AFile bs0, nl⟩)
    (hnz' : fnType n' ≠ 0) (habs' : absRow n' = ⟨.AFile (blkSplice off bs bs0), nl⟩) :
    fevTie (h ++ [.write a i γo off bs r]) (PartialMap.insert I i n') := by
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
variable {GF : BundledGFunctors} [Xv6G GF]

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

/-- (NI M3 private files FS-1) **THE LEDGER BESIDE THE MAP**: the era's
fs-event history, whose fold is the map's typed rows. -/
def ftopLed (γfs : FsNames) (I : RegMapF FsNode) : IProp GF :=
  iprop(∃ h : List Fev, fsLedAuth γfs h ∗ ⌜fevTie h I⌝)

instance ftopLed_timeless (γfs : FsNames) (I : RegMapF FsNode) : Timeless (ftopLed (GF := GF) γfs I) := by
  unfold ftopLed; infer_instance

/-- **THE STEP**: a map move whose events keep the tie appends them; the
receipt is the prefix the events followed and the lower bound past them. -/
theorem ftopLed_step (γfs : FsNames) (I I' : RegMapF FsNode) (evs : List Fev)
    (hstep : ∀ h, fevTie h I → fevTie (h ++ evs) I') :
    ftopLed (GF := GF) γfs I ⊢ |==> (ftopLed γfs I' ∗ ∃ h : List Fev, ⌜fevTie h I⌝ ∗ fsLedLb γfs (h ++ evs)) := by
  unfold ftopLed
  iintro ⟨%h, Ha, %ht⟩
  imod fsLed_append γfs h evs $$ Ha with ⟨Ha, #Hlb⟩
  imodintro
  isplitl [Ha]
  · iexists h ++ evs
    iframe Ha
    ipureintro; exact hstep h ht
  · iexists h
    iframe Hlb
    ipureintro; exact ht

/-- an observation appended -/
theorem ftopLed_obs (γfs : FsNames) (I : RegMapF FsNode) (e : Fev) (he : fevObs e) :
    ftopLed (GF := GF) γfs I ⊢ |==> (ftopLed γfs I ∗ ∃ h : List Fev, ⌜fevTie h I⌝ ∗ fsEvRcpt γfs h e) := by
  iintro Hl
  imod ftopLed_step γfs I I [e] (fun h ht => fevTie_obs e he ht) $$ Hl with ⟨Hl, Hr⟩
  imodintro
  iframe Hl
  unfold fsEvRcpt
  iexact Hr

/-- an observation at row `i`, the record the observer holds -/
theorem ftopLed_obsAt (γfs : FsNames) (I : RegMapF FsNode) (e : Fev) (he : fevObs e) (i : Nat)
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
theorem ftopLed_moveAt (γfs : FsNames) (I : RegMapF FsNode) (i : Nat) (n n' : FsNode) (evs : List Fev)
    (hi : PartialMap.get? I i = some n)
    (hstep : ∀ h, fevTie h I → fevTie (h ++ evs) (PartialMap.insert I i n')) :
    ftopLed (GF := GF) γfs I ⊢
      |==> (ftopLed γfs (PartialMap.insert I i n') ∗ fsMoveRcpt γfs evs i n) := by
  iintro Hl
  imod ftopLed_step γfs I _ evs hstep $$ Hl with ⟨Hl, ⟨%h, %ht, #Hr⟩⟩
  imodintro
  iframe Hl
  unfold fsMoveRcpt
  iexists h
  iframe Hr
  ipureintro; exact fevTie_row i n ht hi

/-- an exhaustion verdict recorded at its instant -/
theorem ftopLed_full (γfs : FsNames) (I : RegMapF FsNode) (act : BitVec 64) (why : FsFull) :
    ftopLed (GF := GF) γfs I ⊢ |==> (ftopLed γfs I ∗ fsFullRcpt γfs act why) := by
  iintro Hl
  imod ftopLed_obs γfs I (.full act why) trivial $$ Hl with ⟨Hl, ⟨%h, -, #Hr⟩⟩
  imodintro
  iframe Hl
  unfold fsFullRcpt
  iexists h
  iexact Hr

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
  | .write _ _ _ _ _ r => r
  | _ => 0

/-- the chunks' total advance -/
def fwSum (cs : List Fev) : Nat := (cs.map fevWriteR).sum

theorem fwSum_append (cs cs' : List Fev) : fwSum (cs ++ cs') = fwSum cs + fwSum cs' := by
  unfold fwSum; simp

/-- **A WRITE'S CHUNKS**: one block per chunk that moved the row, each a
`write act i γo off bs r` at its own position (filewrite unlocks between
chunks, so they need not be adjacent). -/
def fwChunks (γfs : FsNames) (act : BitVec 64) (i : Nat) (γo : GName) : List Fev → IProp GF
  | [] => iprop(emp)
  | e :: cs => iprop(⌜∃ off bs r, e = Fev.write act i γo off bs r⌝ ∗ fsLedAt γfs [e] ∗
      fwChunks γfs act i γo cs)

instance fwChunks_persistent (γfs : FsNames) (act : BitVec 64) (i : Nat) (γo : GName) (cs : List Fev) :
    Persistent (fwChunks (GF := GF) γfs act i γo cs) := by
  induction cs with
  | nil => unfold fwChunks; infer_instance
  | cons e cs ih => unfold fwChunks; infer_instance

theorem fwChunks_nil (γfs : FsNames) (act : BitVec 64) (i : Nat) (γo : GName) :
    ⊢@{IProp GF} fwChunks γfs act i γo [] := by
  unfold fwChunks; iempintro

theorem fwChunks_app (γfs : FsNames) (act : BitVec 64) (i : Nat) (γo : GName) (cs cs' : List Fev) :
    fwChunks (GF := GF) γfs act i γo cs ⊢ fwChunks γfs act i γo cs' -∗ fwChunks γfs act i γo (cs ++ cs') := by
  induction cs with
  | nil => rw [List.nil_append]; iintro - H; iexact H
  | cons e cs ih =>
    rw [List.cons_append, fwChunks.eq_2, fwChunks.eq_2]
    iintro ⟨%he, #Hr, H1⟩ H2
    isplitl []
    · ipureintro; exact he
    isplitl []
    · iexact Hr
    iapply ih $$ H1 H2

theorem fwChunks_one (γfs : FsNames) (act : BitVec 64) (i : Nat) (γo : GName) (off : Nat)
    (bs : List (BitVec 8)) (r : Nat) (n : FsNode) :
    fsMoveRcpt (GF := GF) γfs [Fev.write act i γo off bs r] i n ⊢
      fwChunks γfs act i γo [Fev.write act i γo off bs r] := by
  iintro #Hr
  ihave #Hr2 := fsMoveRcpt_at $$ Hr
  unfold fwChunks fwChunks
  isplitl []
  · ipureintro; exact ⟨off, bs, r, rfl⟩
  isplitl []
  · iexact Hr2
  · iempintro

/-- (NI M3 private files FS-1) the arm event of `i` by `act`, in the era's ledger -/
def creArmRcpt (γfs : FsNames) (act : BitVec 64) (i : Nat) : IProp GF :=
  iprop(∃ n : Fnode, fsLedAt γfs [.arm act i n])

instance creArmRcpt_persistent (γfs : FsNames) (act : BitVec 64) (i : Nat) :
    Persistent (creArmRcpt (GF := GF) γfs act i) := by
  unfold creArmRcpt; infer_instance

/-- (NI M3 private files FS-1) the parent leg by `act`: the entry `nm ↦ i`
set in `d` and `d`'s count, one block in the era's ledger -/
def creParentRcpt (γfs : FsNames) (act : BitVec 64) (i : Nat) : IProp GF :=
  iprop(∃ (d : Nat) (nm : List (BitVec 8)) (nl : Nat),
    fsLedAt γfs [.ent act d nm (some i), .nlink act d nl])

instance creParentRcpt_persistent (γfs : FsNames) (act : BitVec 64) (i : Nat) :
    Persistent (creParentRcpt (GF := GF) γfs act i) := by
  unfold creParentRcpt; infer_instance

/-- (NI M3 private files FS-1) **CREATE'S LEDGER RECEIPT** on a success: a
MADE child's arm and parent leg, or a FOUND node's lookup hop. -/
def creOkRcpt (γfs : FsNames) (act : BitVec 64) (made : Bool) (i : Nat) : IProp GF :=
  iprop((⌜made = true⌝ ∗ creArmRcpt γfs act i ∗ creParentRcpt γfs act i) ∨
    (⌜made = false⌝ ∗ ∃ (d : Nat) (nm : List (BitVec 8)), fsLedAt γfs [.hop act d nm]))

instance creOkRcpt_persistent (γfs : FsNames) (act : BitVec 64) (made : Bool) (i : Nat) :
    Persistent (creOkRcpt (GF := GF) γfs act made i) := by
  unfold creOkRcpt; infer_instance

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
