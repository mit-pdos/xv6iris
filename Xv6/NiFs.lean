/-
**THE FILE SYSTEM's NI VOCABULARY, PURE** (NI M3 private files; design of
record `claude-notes/projects/noninterference.md`, "M3 private files design
(2026-10-05)", findings F3/F4/F7/F8, rulings FS-R2/R3/R5).

* `FsFull` (lane FS-0): the three global fs tables a call can find
  exhausted -- the out-of-resources VERDICTS the design records AS GIVEN
  (FS-R3): no row can compute them, so the kernel's word is carried.
* `Fnode` / `Frows` / `Fev` and the fold `fevRun` (lane FS-1): one era's
  file system as a HISTORY.  The kernel appends one event per abstract move
  at the move's own instant (the fire lemmas, `FsLedger`), so the fold of
  the history IS the era's typed rows (the tie, `FsLedger.fevTie`); the
  observations (a read, a hop, an install, a stat) carry only what names
  them, and a row computes its answer from the fold of the prefix before
  them (`fevReadBytes`, `fevHop`).
* The footprints (`FsFoot`, `fevOn`, `fevPrivate`, `fevClosed` and the two
  footprint lemmas) are FS-4's, and land with it.

F8: this module is self-contained and pure (no ghost state, no kernel
definition: it imports Lean's `Std` map and Iris's `GName` alone), so that
the NI roots' trusted base grows by it alone when `UsysDet.UIota` names it.

## Deviations from the design text (each forced; FS-1's note lists them)

1. `Fnode.dir` holds the entry map as `Std.ExtTreeMap` (the view's own map,
   `FsAbsDefs.Absnode.ADir`), not an association list: the tie is then an
   EQUATION of rows (`fevRows h = ftopRows I`) and a hop is the map's
   lookup, which is `dirlookup`'s first match.
2. `Fev.write` carries the chunk's OFFSET and the count `r` the offset
   advanced by: the row's move IS the delta `deltaWrite i off bs` (FS-R3,
   moves at the delta level), and a short chunk's landed run can be longer
   than its count (writei's disturbed tail, `FsAbsWriteFire.wrfLanded`), so
   neither is a function of the other.  The fold's offset for `γo` is the
   chunk's end, `off + r`.  `Fev.read`'s `n` is the count the read advanced
   the offset by (its answer's length).
3. `Fev.claim` (new): ialloc's claim box made visible at ilock's fill (a
   typed record at nlink 0, its node the record's), so that the fold is the
   typed rows EXACTLY.  The design kept the claim out of the history; then
   a claimed-but-unarmed inode is a typed row the fold does not have, and
   no row of the fold can tell such a box from an empty unlinked file (the
   bare record is not a function of the abstract row).  It carries what the
   arm event would have: the inum (carried, F6) and the record's type.
4. (NI M3 FS-2a, the coordinator's ruling (C) of 2026-10-06) `Fev.read`
   carries the REAL offset `off` the read used, as `write` does, and the
   fold sets `off + n`: the offset is RECORDED AS GIVEN (R3's status for
   the inode number), because the fold's own offset is not yet tied to the
   real `f->off` (FS-2a′ ties it; FS-4 derives the recorded offsets).  The
   read row reads the cited prefix's last event (`fevReadOut`,
   `fevReadDir`), so no row reads `UIota.fpos`.
5. (NI M3 FS-2a) `FsFull.max`: writei's refusal at the file's size cap
   from the offset, recorded as a verdict like the three exhaustions.
-/
import Std.Data.ExtTreeMap
import Iris.Algebra.IProp

namespace Xv6

open Iris

/-- (NI M3 FS-0) the three global fs tables a call can find exhausted. -/
inductive FsFull where
  /-- the inode table: `ialloc` scanned every dinode and found none free -/
  | inodes
  /-- the free-block bitmap: `balloc` found no clear bit below `sb.size` -/
  | blocks
  /-- the open-file table: `filealloc` found all `NFILE` entries in use -/
  | files
  /-- (NI M3 FS-2a) the FILE's size cap: writei refused the chunk at its
  offset (`off > size` or past `MAXFILE * BSIZE`) -- a per-file verdict, not
  a table, recorded AS GIVEN like the three exhaustions (it reads the offset,
  which the ledger records as given until FS-2a′ ties it to the fold) -/
  | max
  deriving DecidableEq, Repr

/-! ## §1 The rows and the events -/

/-- the node a row reads (`FsAbsDefs.Absnode` over this module's own
vocabulary): a file's bytes, a directory's entry map (`"."` and `".."`
included), a device's major and minor -/
inductive Fnode where
  | file (bs : List (BitVec 8))
  | dir (ents : Std.ExtTreeMap (List (BitVec 8)) Nat compare)
  | dev (ma mi : Nat)

/-- the TYPED rows, orphans (nlink 0, still referenced) and claim boxes
included: inum ↦ (node, link count) -/
abbrev Frows := Nat → Option (Fnode × Nat)

/-- **ONE FS EVENT OF AN ERA.**  MOVES carry their delta; OBSERVATIONS carry
only what names them (their answer is computed from the fold of the prefix
before them); the inode number, the offset shadow's name `γo` and the
exhaustion verdicts are CARRIED (declassified, F6). -/
inductive Fev where
  /-- the era's recovered rows -/
  | boot (s : Frows)
  /-- ialloc's claim box made visible at ilock's fill (nlink 0) -/
  | claim (act : BitVec 64) (i : Nat) (n : Fnode)
  /-- create's child appears at nlink 1 (`i` CARRIED) -/
  | arm (act : BitVec 64) (i : Nat) (n : Fnode)
  /-- an entry set (`some t`) or removed (`none`) -/
  | ent (act : BitVec 64) (d : Nat) (nm : List (BitVec 8)) (t : Option Nat)
  /-- a link-count leg: the count becomes `nl` -/
  | nlink (act : BitVec 64) (i : Nat) (nl : Nat)
  /-- one chunk, spliced in at `off`; `γo`'s offset ends at `off + r` -/
  | write (act : BitVec 64) (i : Nat) (γo : GName) (off : Nat) (bs : List (BitVec 8)) (r : Nat)
  /-- O_TRUNC's itrunc -/
  | trunc (act : BitVec 64) (i : Nat)
  /-- iput's last-reference free -/
  | free (act : BitVec 64) (i : Nat)
  /-- a lookup of `nm` in `d`, at its instant -/
  | hop (act : BitVec 64) (d : Nat) (nm : List (BitVec 8))
  /-- an fd installed on `i` (`γo` CARRIED); its offset 0 -/
  | open (act : BitVec 64) (i : Nat) (γo : GName)
  /-- `n` bytes read from `γo`'s offset `off` (the count the read advanced it
  by); (NI M3 FS-2a, ruling (C)) `off` is the REAL offset the read used,
  recorded AS GIVEN, as `write` records its own -/
  | read (act : BitVec 64) (i : Nat) (γo : GName) (off n : Nat)
  /-- a stat of `i` -/
  | stat (act : BitVec 64) (i : Nat)
  /-- an exhaustion verdict (CARRIED) -/
  | full (act : BitVec 64) (why : FsFull)

/-! ## §2 The fold -/

/-- one row set -/
def frowsSet (s : Frows) (i : Nat) (v : Option (Fnode × Nat)) : Frows :=
  fun j => if j = i then v else s j

/-- the write's splice (`FsBytes.blkSplice`, restated: this module names no
kernel definition) -/
def fsplice (off : Nat) (sub bs : List (BitVec 8)) : List (BitVec 8) :=
  bs.take off ++ (sub ++ bs.drop (off + sub.length))

/-- an entry set or removed -/
def fentSet (m : Std.ExtTreeMap (List (BitVec 8)) Nat compare) (nm : List (BitVec 8)) :
    Option Nat → Std.ExtTreeMap (List (BitVec 8)) Nat compare
  | some t => m.insert nm t
  | none => m.erase nm

/-- one offset set -/
def foffSet (o : GName → Nat) (γo : GName) (v : Nat) : GName → Nat :=
  fun g => if g = γo then v else o g

/-- a link-count leg on one row -/
def frowNlink (nl : Nat) : Option (Fnode × Nat) → Option (Fnode × Nat)
  | some (n, _) => some (n, nl)
  | none => none

/-- an entry move on one row (a directory's) -/
def frowEnt (nm : List (BitVec 8)) (t : Option Nat) : Option (Fnode × Nat) → Option (Fnode × Nat)
  | some (.dir m, nl) => some (.dir (fentSet m nm t), nl)
  | x => x

/-- a chunk on one row (a file's) -/
def frowWrite (off : Nat) (bs : List (BitVec 8)) : Option (Fnode × Nat) → Option (Fnode × Nat)
  | some (.file c, nl) => some (.file (fsplice off bs c), nl)
  | x => x

/-- a truncation on one row (a file's) -/
def frowTrunc : Option (Fnode × Nat) → Option (Fnode × Nat)
  | some (.file _, nl) => some (.file [], nl)
  | x => x

/-- **ONE STEP OF THE FOLD**: the rows and every struct file's offset. -/
def fevStep (st : Frows × (GName → Nat)) : Fev → Frows × (GName → Nat)
  | .boot s => (s, fun _ => 0)
  | .claim _ i n => (frowsSet st.1 i (some (n, 0)), st.2)
  | .arm _ i n => (frowsSet st.1 i (some (n, 1)), st.2)
  | .ent _ d nm t => (frowsSet st.1 d (frowEnt nm t (st.1 d)), st.2)
  | .nlink _ i nl => (frowsSet st.1 i (frowNlink nl (st.1 i)), st.2)
  | .write _ i γo off bs r => (frowsSet st.1 i (frowWrite off bs (st.1 i)), foffSet st.2 γo (off + r))
  | .trunc _ i => (frowsSet st.1 i (frowTrunc (st.1 i)), st.2)
  | .free _ i => (frowsSet st.1 i none, st.2)
  | .open _ _ γo => (st.1, foffSet st.2 γo 0)
  | .read _ _ γo off n => (st.1, foffSet st.2 γo (off + n))
  | .hop _ _ _ => st
  | .stat _ _ => st
  | .full _ _ => st

/-- **THE FOLD**: the rows and every struct file's offset after `h` (from
nothing: an era's history starts with its `boot`). -/
def fevRun (h : List Fev) : Frows × (GName → Nat) :=
  h.foldl fevStep (fun _ => none, fun _ => 0)

def fevRows (h : List Fev) : Frows := (fevRun h).1

def fevOff (h : List Fev) (γo : GName) : Nat := (fevRun h).2 γo

/-- a file row's bytes (`[]` at any other row) -/
def fevContent (h : List Fev) (i : Nat) : List (BitVec 8) :=
  match fevRows h i with
  | some (.file bs, _) => bs
  | _ => []

/-- **A READ's ANSWER**: at most `n` bytes from `γo`'s offset -/
def fevReadBytes (h : List Fev) (i : Nat) (γo : GName) (n : Nat) : List (BitVec 8) :=
  ((fevContent h i).drop (fevOff h γo)).take n

/-- **A HOP's ANSWER**: `..` at the walker's root is the root (chroot's
rule), else the directory's entry -/
def fevHop (h : List Fev) (rt d : Nat) (nm : List (BitVec 8)) : Option Nat :=
  if nm = [46#8, 46#8] ∧ d = rt then some d else
    match fevRows h d with
    | some (.dir es, _) => es[nm]?
    | _ => none

/-- **A STAT's FIELDS** at a FILE row: (type `T_FILE` = 2, the count, the
size); `none` at a directory or device row (a directory's raw size and a
device's size are not in the view: FS-R4 keeps them outside the class) -/
def fevStatOf (h : List Fev) (i : Nat) : Option (Nat × Nat × Nat) :=
  match fevRows h i with
  | some (.file bs, nl) => some (2, nl, bs.length)
  | _ => none

/-! ### The cited read (NI M3 FS-2a, ruling (C))

A read row cites the prefix ENDING IN its own `read` event (the fork row's
pattern: the decisive event closes the cited prefix), so the reading is a
function of the cited list alone.  The bytes are the file row's content in
the fold of the prefix BEFORE the event, from the event's RECORDED offset
(not the fold's `fevOff`: FS-2a′ ties the two), at most `n`. -/

/-- the row is a file in `h`'s fold -/
def fevIsFile (h : List Fev) (i : Nat) : Bool :=
  match fevRows h i with
  | some (.file _, _) => true
  | _ => false

/-- **THE CITED READ's ROW IS NOT A FILE** (a directory, or anything else
the view does not hold the bytes of): the class's `fdir` reading -/
def fevReadDir (h : List Fev) : Bool :=
  match h.getLast? with
  | some (.read _ i _ _ _) => !fevIsFile h.dropLast i
  | _ => false

/-- **THE CITED READ's BYTES**: at most `n` bytes of the file row from the
read's recorded offset, in the fold before it (`[]` when the cited prefix
does not end in a read) -/
def fevReadOut (h : List Fev) (n : Nat) : List (BitVec 8) :=
  match h.getLast? with
  | some (.read _ i _ off _) => ((fevContent h.dropLast i).drop off).take n
  | _ => []

/-- **THE CITED VERDICT**: the cited prefix ends in an out-of-resources
verdict of actor `a` (write's `-1`, recorded as given) -/
def fevFullBy (h : List Fev) (a : BitVec 64) : Bool :=
  match h.getLast? with
  | some (.full a' _) => a' == a
  | _ => false

theorem fevReadDir_snoc (h : List Fev) (act : BitVec 64) (i : Nat) (γo : GName) (off d : Nat) :
    fevReadDir (h ++ [.read act i γo off d]) = !fevIsFile h i := by
  unfold fevReadDir; simp

theorem fevReadOut_snoc (h : List Fev) (act : BitVec 64) (i : Nat) (γo : GName) (off d n : Nat) :
    fevReadOut (h ++ [.read act i γo off d]) n = ((fevContent h i).drop off).take n := by
  unfold fevReadOut; simp

theorem fevFullBy_snoc (h : List Fev) (a : BitVec 64) (why : FsFull) :
    fevFullBy (h ++ [.full a why]) a = true := by
  unfold fevFullBy; simp

/-! ### The fold's algebra -/

theorem fevRun_append (h h' : List Fev) : fevRun (h ++ h') = h'.foldl fevStep (fevRun h) := by
  unfold fevRun; rw [List.foldl_append]

theorem fevRun_snoc (h : List Fev) (e : Fev) : fevRun (h ++ [e]) = fevStep (fevRun h) e := by
  rw [fevRun_append]; rfl

/-- an OBSERVATION moves no row -/
def fevObs : Fev → Prop
  | .hop _ _ _ | .open _ _ _ | .read _ _ _ _ _ | .stat _ _ | .full _ _ => True
  | _ => False

theorem fevRows_obs (h : List Fev) (e : Fev) (he : fevObs e) : fevRows (h ++ [e]) = fevRows h := by
  unfold fevRows; rw [fevRun_snoc]
  cases e <;> first | rfl | exact absurd he id

theorem fevRows_snoc (h : List Fev) (e : Fev) : fevRows (h ++ [e]) = (fevStep (fevRun h) e).1 := by
  unfold fevRows; rw [fevRun_snoc]

/-- prefix monotonicity: a prefix's fold is the fold of the prefix -/
theorem fevRun_prefix {h h' : List Fev} (hp : h <+: h') :
    ∃ t, h' = h ++ t ∧ fevRun h' = t.foldl fevStep (fevRun h) := by
  obtain ⟨t, rfl⟩ := hp
  exact ⟨t, rfl, fevRun_append h t⟩

end Xv6
