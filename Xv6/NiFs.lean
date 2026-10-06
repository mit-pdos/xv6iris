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
* The footprints (`FsFoot`, `fevMoves`, `fevOn`, `fevClosed` and the two
  footprint lemmas `fevReadBytes_on`/`fevHop_on`, §3) land in FS-2d for
  FS-4, which reads them.

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
   fold sets `off + n`.  (NI M3 FS-2a′) The fold's offset is now TIED to
   the real `f->off` at every parked read and write (`fevOffWf`, the
   ledger's invariant, kept by the fs ledger's quarter share of the
   shadow), so the read row reads the FOLD's offset (`fevReadOut`,
   `fevReadBytes`); `read`/`write`/`open` carry the descriptor's mode
   `held`, and the fold's offsets ignore the held ones (a held
   descriptor's offset is the client's own).  The read row reads the cited
   prefix's last event (`fevReadOut`, `fevReadDir`), so no row reads
   `UIota.fpos`.
5. (NI M3 FS-2a) `FsFull.max`: writei's refusal at the file's size cap
   from the offset, recorded as a verdict like the three exhaustions.
6. (NI M3 FS-2d, X2) `fevLookAt`/`fevOpenFixed` take the path's ELEMENTS
   `es` and check the followed walk's lookup NAMES against them
   (`(fevChain H po).map Prod.snd = es`), not only their count: a walk of
   the right length over other names no longer reads as the key's path.
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
  /-- one chunk, spliced in at `off`; `γo`'s offset ends at `off + r`.  (NI M3
  FS-2a′) `held`: the descriptor's offset is the client's own (`OffMode.held`),
  so the ledger does not track it and the fold's offsets ignore the chunk -/
  | write (act : BitVec 64) (i : Nat) (γo : GName) (held : Bool) (off : Nat) (bs : List (BitVec 8))
      (r : Nat)
  /-- O_TRUNC's itrunc -/
  | trunc (act : BitVec 64) (i : Nat)
  /-- iput's last-reference free -/
  | free (act : BitVec 64) (i : Nat)
  /-- a lookup of `nm` in `d`, at its instant; (NI M3 FS-2b) `prev` is the ledger
  position of the previous lookup of the SAME walk (`none` at a walk's first, and
  at a lookup no walk follows) -- a back-pointer, ledger bookkeeping -/
  | hop (act : BitVec 64) (d : Nat) (nm : List (BitVec 8)) (prev : Option Nat)
  /-- an fd installed on `i` (`γo` CARRIED); its offset 0.  (NI M3 FS-2b′) An
  observation AT `i`'s row (the install runs under the open's lock on `i`, the
  type test's lock): `held` the descriptor's offset mode (`OffMode.held`,
  CARRIED like `γo`), `prev` the position of the event that fixed `i` -- the
  walk's last lookup (a plain open), create's arm or create's lookup (O_CREATE).
  (NI M3 FS-2a′) `held` is ALSO set at a DEVICE install: a device descriptor
  has no offset shadow, so the ledger tracks none (`fevPk`); only a PARKED
  inode install (`held = false`) starts a tracked offset, at 0 -/
  | open (act : BitVec 64) (i : Nat) (γo : GName) (held : Bool) (prev : Option Nat)
  /-- `n` bytes read from `γo`'s offset `off` (the count the read advanced it
  by); (NI M3 FS-2a, ruling (C)) `off` is the REAL offset the read used,
  recorded AS GIVEN, as `write` records its own.  (NI M3 FS-2a′) At a PARKED
  descriptor (`held = false`) the recorded offset IS the fold's (`fevOffWf`,
  the ledger's invariant); at a HELD one it is the client's own and the fold's
  offsets ignore the read -/
  | read (act : BitVec 64) (i : Nat) (γo : GName) (held : Bool) (off n : Nat)
  /-- a stat of `i` -/
  | stat (act : BitVec 64) (i : Nat)
  /-- an exhaustion verdict (CARRIED) -/
  | full (act : BitVec 64) (why : FsFull)
  /-- (NI M3 FS-2b) a walk's TYPE TEST: an observation of `i`'s row at its
  instant (chdir's and open's), `prev` the position of the walk's last lookup -/
  | look (act : BitVec 64) (i : Nat) (prev : Option Nat)

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
  | .write _ i γo held off bs r =>
    (frowsSet st.1 i (frowWrite off bs (st.1 i)), if held then st.2 else foffSet st.2 γo (off + r))
  | .trunc _ i => (frowsSet st.1 i (frowTrunc (st.1 i)), st.2)
  | .free _ i => (frowsSet st.1 i none, st.2)
  | .open _ _ γo held _ => (st.1, if held then st.2 else foffSet st.2 γo 0)
  | .read _ _ γo held off n => (st.1, if held then st.2 else foffSet st.2 γo (off + n))
  | .hop _ _ _ _ => st
  | .look _ _ _ => st
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
  | some (.read _ i _ _ _ _) => !fevIsFile h.dropLast i
  | _ => false

/-- **THE CITED READ's BYTES**: at most `n` bytes of the file row from the
FOLD's offset for the read's shadow, in the fold before it (`fevReadBytes`;
`[]` when the cited prefix does not end in a read).  (NI M3 FS-2a′) DERIVED,
not recorded: at a parked read the recorded offset IS the fold's
(`fevOffWf`, the ledger's invariant; the read's receipt carries it,
`SpecFileread.freadRcptAt`), so the row no longer reads the carried one. -/
def fevReadOut (h : List Fev) (n : Nat) : List (BitVec 8) :=
  match h.getLast? with
  | some (.read _ i γo _ _ _) => fevReadBytes h.dropLast i γo n
  | _ => []

/-- **THE CITED VERDICT**: the cited prefix ends in an out-of-resources
verdict of actor `a` (write's `-1`, recorded as given) -/
def fevFullBy (h : List Fev) (a : BitVec 64) : Bool :=
  match h.getLast? with
  | some (.full a' _) => a' == a
  | _ => false

theorem fevReadDir_snoc (h : List Fev) (act : BitVec 64) (i : Nat) (γo : GName) (hd : Bool) (off d : Nat) :
    fevReadDir (h ++ [.read act i γo hd off d]) = !fevIsFile h i := by
  unfold fevReadDir; simp

theorem fevReadOut_snoc (h : List Fev) (act : BitVec 64) (i : Nat) (γo : GName) (hd : Bool) (off d n : Nat) :
    fevReadOut (h ++ [.read act i γo hd off d]) n = fevReadBytes h i γo n := by
  unfold fevReadOut; simp

/-- ...at the recorded offset, where it is the fold's -/
theorem fevReadOut_snoc_at (h : List Fev) (act : BitVec 64) (i : Nat) (γo : GName) (hd : Bool) (off d n : Nat)
    (hoff : off = fevOff h γo) :
    fevReadOut (h ++ [.read act i γo hd off d]) n = ((fevContent h i).drop off).take n := by
  rw [fevReadOut_snoc, hoff]; rfl

theorem fevFullBy_snoc (h : List Fev) (a : BitVec 64) (why : FsFull) :
    fevFullBy (h ++ [.full a why]) a = true := by
  unfold fevFullBy; simp

/-! ### The fold's algebra -/

theorem fevRun_append (h h' : List Fev) : fevRun (h ++ h') = h'.foldl fevStep (fevRun h) := by
  unfold fevRun; rw [List.foldl_append]

theorem fevRun_snoc (h : List Fev) (e : Fev) : fevRun (h ++ [e]) = fevStep (fevRun h) e := by
  rw [fevRun_append]; rfl

/-- an OBSERVATION moves no row -- and (NI M3 FS-2a′) no TRACKED offset: a
PARKED install or read is not one (it moves the ledger's offset share,
`FsLedger.ftopLed_pk*`) -/
def fevObs : Fev → Prop
  | .hop _ _ _ _ | .stat _ _ | .full _ _ | .look _ _ _ => True
  | .open _ _ _ held _ => held = true
  | .read _ _ _ held _ _ => held = true
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

/-! ### The tracked offsets (NI M3 FS-2a′)

The ledger TRACKS the offset of every struct file a PARKED inode install
opened (`fevPk`: the install `open _ _ γo false _`): it holds a quarter of
that file's offset shadow at the fold's value (`FsLedger.ftopLed`), so a
fire at a parked descriptor finds the real offset EQUAL to the fold's at the
instant it appends its `read`/`write`.  That is `fevOffWf`, the ledger's
invariant: every parked read's and write's RECORDED offset is the fold's
offset of the prefix before it.  A HELD descriptor's offset (and a device's,
which has none) is the client's own datum: its events carry `held = true`,
the fold's offsets ignore them, and `fevOffWf` says nothing of them. -/

/-- the struct file a PARKED install starts tracking -/
def fevPkOf : Fev → Option GName
  | .open _ _ γo false _ => some γo
  | _ => none

/-- **THE TRACKED OFFSETS**: the shadows of the parked installs, in order -/
def fevPk (h : List Fev) : List GName := h.filterMap fevPkOf

theorem fevPk_snoc (h : List Fev) (e : Fev) : fevPk (h ++ [e]) = fevPk h ++ (fevPkOf e).toList := by
  unfold fevPk
  rw [List.filterMap_append]
  cases hx : fevPkOf e <;> simp [hx]

/-- an event that moves no tracked offset and starts none: everything but a
parked install, read or write -- and the era's `boot` (which resets every
offset; it is only ever the era's first event) -/
def fevNeutral : Fev → Bool
  | .boot _ => false
  | .open _ _ _ false _ => false
  | .read _ _ _ false _ _ => false
  | .write _ _ _ false _ _ _ => false
  | _ => true

theorem fevNeutral_obs (e : Fev) (he : fevObs e) : fevNeutral e = true := by
  cases e with
  | «open» a i γo held po =>
    cases held
    · exact absurd he (by simp [fevObs])
    · rfl
  | read a i γo held off n =>
    cases held
    · exact absurd he (by simp [fevObs])
    · rfl
  | write => exact absurd he id
  | boot => exact absurd he id
  | _ => rfl

theorem fevPk_neutral (h : List Fev) (e : Fev) (hn : fevNeutral e = true) : fevPk (h ++ [e]) = fevPk h := by
  rw [fevPk_snoc]
  have : fevPkOf e = none := by
    cases e with
    | «open» a i γo held po => cases held <;> simp_all [fevNeutral, fevPkOf]
    | _ => rfl
  rw [this]; simp

theorem fevOff_neutral (h : List Fev) (e : Fev) (hn : fevNeutral e = true) (γ : GName) :
    fevOff (h ++ [e]) γ = fevOff h γ := by
  unfold fevOff; rw [fevRun_snoc]
  cases e with
  | «open» a i γo held po => cases held <;> simp_all [fevNeutral, fevStep]
  | read a i γo held off n => cases held <;> simp_all [fevNeutral, fevStep]
  | write a i γo held off bs r => cases held <;> simp_all [fevNeutral, fevStep]
  | boot => simp [fevNeutral] at hn
  | _ => rfl

/-- a parked install starts its offset at 0 -/
theorem fevOff_pkOpen (h : List Fev) (a : BitVec 64) (i : Nat) (γo : GName) (po : Option Nat) (γ : GName) :
    fevOff (h ++ [.open a i γo false po]) γ = if γ = γo then 0 else fevOff h γ := by
  unfold fevOff; rw [fevRun_snoc]; simp [fevStep, foffSet]

/-- a parked read advances its offset from the recorded one -/
theorem fevOff_pkRead (h : List Fev) (a : BitVec 64) (i : Nat) (γo : GName) (off n : Nat) (γ : GName) :
    fevOff (h ++ [.read a i γo false off n]) γ = if γ = γo then off + n else fevOff h γ := by
  unfold fevOff; rw [fevRun_snoc]; simp [fevStep, foffSet]

/-- a parked chunk advances its offset from the recorded one -/
theorem fevOff_pkWrite (h : List Fev) (a : BitVec 64) (i : Nat) (γo : GName) (off : Nat)
    (bs : List (BitVec 8)) (r : Nat) (γ : GName) :
    fevOff (h ++ [.write a i γo false off bs r]) γ = if γ = γo then off + r else fevOff h γ := by
  unfold fevOff; rw [fevRun_snoc]; simp [fevStep, foffSet]

/-- **ONE EVENT's OFFSET CONDITION**: a parked read or write recorded the
offset the fold held for its shadow -/
def fevOffOk (h : List Fev) : Fev → Prop
  | .read _ _ γo false off _ => off = fevOff h γo
  | .write _ _ γo false off _ _ => off = fevOff h γo
  | _ => True

/-- **THE RECORDED OFFSETS ARE THE FOLD's** (the ledger's invariant,
`FsLedger.ftopLed`): every parked read's and write's carried offset is the
fold's offset of the prefix before it -/
def fevOffWf (h : List Fev) : Prop := ∀ (k : Nat) (e : Fev), h[k]? = some e → fevOffOk (h.take k) e

theorem fevOffOk_neutral (h : List Fev) (e : Fev) (hn : fevNeutral e = true) : fevOffOk h e := by
  cases e with
  | read a i γo held off n => cases held <;> simp_all [fevNeutral, fevOffOk]
  | write a i γo held off bs r => cases held <;> simp_all [fevNeutral, fevOffOk]
  | _ => trivial

theorem fevOffWf_nil : fevOffWf [] := fun _ _ h => by simp at h

theorem fevOffWf_snoc (h : List Fev) (e : Fev) : fevOffWf (h ++ [e]) ↔ fevOffWf h ∧ fevOffOk h e := by
  constructor
  · intro hw
    refine ⟨fun k e' hk => ?_, ?_⟩
    · have hlt : k < h.length := (List.getElem?_eq_some_iff.mp hk).1
      have h1 := hw k e' (by rw [List.getElem?_append_left hlt]; exact hk)
      rwa [List.take_append_of_le_length (Nat.le_of_lt hlt)] at h1
    · have h1 := hw h.length e (by simp)
      rwa [List.take_left' rfl] at h1
  · rintro ⟨hw, he⟩ k e' hk
    by_cases hlt : k < h.length
    · rw [List.getElem?_append_left hlt] at hk
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact hw k e' hk
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hk
      have hk0 : k - h.length = 0 := by
        cases hx : k - h.length with
        | zero => rfl
        | succ m => rw [hx] at hk; simp at hk
      have hkk : k = h.length := by omega
      subst hkk
      rw [hk0] at hk
      simp at hk
      subst hk
      rw [List.take_left' rfl]
      exact he

/-- every prefix of a well-formed ledger is well-formed -/
theorem fevOffWf_prefix {h h' : List Fev} (hp : h' <+: h) (hw : fevOffWf h) : fevOffWf h' := by
  obtain ⟨t, rfl⟩ := hp
  intro k e hk
  have hlt : k < h'.length := (List.getElem?_eq_some_iff.mp hk).1
  have h1 := hw k e (by rw [List.getElem?_append_left hlt]; exact hk)
  rwa [List.take_append_of_le_length (Nat.le_of_lt hlt)] at h1

/-! ### The walk's lookups, followed (NI M3 FS-2b)

A path walk's lookups are NOT contiguous in the ledger (the walk releases
each directory's lock before the next element), so each `hop` records the
position of the previous lookup of its walk, and a walk's decisive event
(chdir's and open's type test, `look`) records the position of its last.
The rows follow the pointers inside the cited prefix -- positions are
bookkeeping, every answer is a fold (`fevHop`) of the prefix before the
lookup at its own position.  A pointer that is not strictly earlier stops
the chain (the fires only ever record earlier ones). -/

/-- the lookups of the walk whose LAST lookup sits at position `p` of `H`,
in walk order: their positions and names -/
def fevChainAt (H : List Fev) (p : Nat) : List (Nat × List (BitVec 8)) :=
  match H[p]? with
  | some (.hop _ _ nm (some q)) => if _h : q < p then fevChainAt H q ++ [(p, nm)] else [(p, nm)]
  | some (.hop _ _ nm none) => [(p, nm)]
  | _ => []
termination_by p

/-- ...from an optional last position (`none`: a walk that made no lookup) -/
def fevChain (H : List Fev) : Option Nat → List (Nat × List (BitVec 8))
  | none => []
  | some p => fevChainAt H p

/-- **THE WALK's RESOLUTION**: from the start `s0`, each lookup answered by
the fold of the prefix before it (`fevHop` at the walker's root `rt`) -/
def fevWalk (H : List Fev) (rt s0 : Nat) (cs : List (Nat × List (BitVec 8))) : Option Nat :=
  cs.foldl (fun acc x => acc.bind fun cur => fevHop (H.take x.1) rt cur x.2) (some s0)

/-- **THE CITED TYPE TEST** (chdir's and open's decisive event): the cited
prefix ends in actor `a`'s `look a i po`, whose walk -- the lookups followed
from `po` -- looked up exactly the names `es` (NI M3 FS-2d, X2: the hop NAMES
are the path's elements, not only their count) and resolved from `s0` to
`i`; its reading is `i` and `i`'s row in the fold before the observation
(`none` otherwise) -/
def fevLookAt (H : List Fev) (a : BitVec 64) (rt s0 : Nat) (es : List (List (BitVec 8))) :
    Option (Nat × Option (Fnode × Nat)) :=
  match H.getLast? with
  | some (.look a' i po) =>
    if a' = a ∧ (fevChain H po).map Prod.snd = es ∧ fevWalk H rt s0 (fevChain H po) = some i then
      some (i, fevRows H.dropLast i)
    else none
  | _ => none

/-- **THE CITED PARENT LEG** (mkdir's decisive event, NI M3 FS-2b): the cited
prefix ends in actor `a`'s entry set and the parent's count leg, one block -/
def fevLegBy (H : List Fev) (a : BitVec 64) : Bool :=
  match H.reverse with
  | .nlink a1 d1 _ :: .ent a2 d2 _ (some _) :: _ => a1 == a && a2 == a && d1 == d2
  | _ => false

theorem fevChainAt_eq (H : List Fev) (p : Nat) :
    fevChainAt H p = match H[p]? with
      | some (.hop _ _ nm (some q)) => if q < p then fevChainAt H q ++ [(p, nm)] else [(p, nm)]
      | some (.hop _ _ nm none) => [(p, nm)]
      | _ => [] := by
  rw [fevChainAt]
  split <;> rfl

/-- every position on a chain is at most its last -/
theorem fevChainAt_le (H : List Fev) : ∀ (p : Nat), ∀ x ∈ fevChainAt H p, x.1 ≤ p := by
  intro p
  refine Nat.strongRecOn p ?_
  intro p ih
  · intro x hx
    rw [fevChainAt_eq] at hx
    split at hx
    · split at hx
      · rename_i q _ hq
        rcases List.mem_append.mp hx with h | h
        · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (ih q hq x h) hq)
        · simp at h; rw [h]; exact Nat.le_refl _
      · simp at hx; rw [hx]; exact Nat.le_refl _
    · simp at hx; rw [hx]; exact Nat.le_refl _
    · simp at hx

/-- a chain read in a longer ledger is the chain read in the shorter one -/
theorem fevChainAt_prefix {H H' : List Fev} (hp : H <+: H') :
    ∀ (p : Nat), p < H.length → fevChainAt H' p = fevChainAt H p := by
  intro p
  refine Nat.strongRecOn p ?_
  intro p ih
  · intro hlt
    have hg : H'[p]? = H[p]? := by
      obtain ⟨t, rfl⟩ := hp
      rw [List.getElem?_append_left hlt]
    rw [fevChainAt_eq, fevChainAt_eq H, hg]
    split
    · split
      · rename_i q _ hq
        rw [ih q hq (Nat.lt_trans hq hlt)]
      · rfl
    · rfl
    · rfl

theorem fevWalk_append (H : List Fev) (rt s0 : Nat) (cs : List (Nat × List (BitVec 8))) (x : Nat × List (BitVec 8)) :
    fevWalk H rt s0 (cs ++ [x]) = (fevWalk H rt s0 cs).bind fun cur => fevHop (H.take x.1) rt cur x.2 := by
  unfold fevWalk; rw [List.foldl_append]; rfl

/-- a walk read in a longer ledger at positions inside the shorter one -/
theorem fevWalk_prefix {H H' : List Fev} (hp : H <+: H') (rt s0 : Nat) :
    ∀ (cs : List (Nat × List (BitVec 8))), (∀ x ∈ cs, x.1 ≤ H.length) →
      fevWalk H' rt s0 cs = fevWalk H rt s0 cs := by
  intro cs hc
  unfold fevWalk
  generalize (some s0 : Option Nat) = acc
  induction cs generalizing acc with
  | nil => rfl
  | cons x cs ih =>
    simp only [List.foldl_cons]
    have hx := hc x (List.mem_cons_self ..)
    have ht : H'.take x.1 = H.take x.1 := by
      obtain ⟨t, rfl⟩ := hp
      rw [List.take_append_of_le_length hx]
    rw [ht]
    exact ih (fun y hy => hc y (List.mem_cons_of_mem _ hy)) _

/-- **THE WALK SO FAR** (what the wrapped cursor carries): the lookups
followed from `po` in `H` name `es` and resolve from `s0` to `d` -/
def fevWalkIs (H : List Fev) (rt s0 : Nat) (po : Option Nat) (es : List (List (BitVec 8))) (d : Nat) : Prop :=
  (∀ q, po = some q → q < H.length) ∧ (fevChain H po).map Prod.snd = es ∧
    fevWalk H rt s0 (fevChain H po) = some d

theorem fevWalkIs_nil (H : List Fev) (rt s0 : Nat) : fevWalkIs H rt s0 none [] s0 :=
  ⟨(fun _ h => nomatch h), rfl, rfl⟩

theorem fevChain_le (H : List Fev) (po : Option Nat) (hpo : ∀ q, po = some q → q < H.length) :
    ∀ x ∈ fevChain H po, x.1 < H.length := by
  intro x hx
  cases po with
  | none => simp [fevChain] at hx
  | some p => exact Nat.lt_of_le_of_lt (fevChainAt_le H p x hx) (hpo p rfl)

theorem fevChain_prefix {H H' : List Fev} (hp : H <+: H') (po : Option Nat)
    (hpo : ∀ q, po = some q → q < H.length) : fevChain H' po = fevChain H po := by
  cases po with
  | none => rfl
  | some p => exact fevChainAt_prefix hp p (hpo p rfl)

/-- the walk so far survives the ledger's growth -/
theorem fevWalkIs_mono {H H' : List Fev} (hp : H <+: H') {rt s0 : Nat} {po : Option Nat}
    {es : List (List (BitVec 8))} {d : Nat} (hw : fevWalkIs H rt s0 po es d) : fevWalkIs H' rt s0 po es d := by
  obtain ⟨hpo, hes, hd⟩ := hw
  have hlen : H.length ≤ H'.length := hp.length_le
  refine ⟨fun q hq => Nat.lt_of_lt_of_le (hpo q hq) hlen, ?_, ?_⟩
  · rw [fevChain_prefix hp po hpo]; exact hes
  · rw [fevChain_prefix hp po hpo, fevWalk_prefix hp rt s0 _ (fun x hx => Nat.le_of_lt (fevChain_le H po hpo x hx))]
    exact hd

/-- **ONE MORE LOOKUP**: at a ledger `h` past the walk's, the lookup of `nm`
in the walk's directory `d` appended with the back-pointer `po`, answered
`c` by the fold of `h` -/
theorem fevWalkIs_hop {H h : List Fev} (hp : H <+: h) {rt s0 : Nat} {po : Option Nat}
    {es : List (List (BitVec 8))} {d c : Nat} (hw : fevWalkIs H rt s0 po es d) (a : BitVec 64)
    (nm : List (BitVec 8)) (hc : fevHop h rt d nm = some c) :
    fevWalkIs (h ++ [.hop a d nm po]) rt s0 (some h.length) (es ++ [nm]) c := by
  have hw' := fevWalkIs_mono (H' := h ++ [.hop a d nm po]) (hp.trans (List.prefix_append _ _)) hw
  obtain ⟨hpo', hes', hd'⟩ := hw'
  have hpo : ∀ q, po = some q → q < h.length := fun q hq => Nat.lt_of_lt_of_le (hw.1 q hq) hp.length_le
  have hch : fevChain (h ++ [.hop a d nm po]) (some h.length) =
      fevChain (h ++ [.hop a d nm po]) po ++ [(h.length, nm)] := by
    show fevChainAt _ _ = _
    rw [fevChainAt_eq]
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
    cases po with
    | none => rfl
    | some q => simp only [fevChain, if_pos (hpo q rfl)]
  refine ⟨fun q hq => by cases hq; simp, ?_, ?_⟩
  · rw [hch, List.map_append, hes']; rfl
  · rw [hch, fevWalk_append, hd']
    simp only [Option.bind_some, List.take_left' rfl]
    exact hc

/-- **THE TYPE TEST CITED**: the walk so far, observed at `i` -/
theorem fevLookAt_snoc {H h : List Fev} (hp : H <+: h) {rt s0 : Nat} {po : Option Nat}
    {es : List (List (BitVec 8))} {i : Nat} (hw : fevWalkIs H rt s0 po es i) (a : BitVec 64) :
    fevLookAt (h ++ [.look a i po]) a rt s0 es = some (i, fevRows h i) := by
  obtain ⟨hpo, hes, hd⟩ := fevWalkIs_mono (H' := h ++ [.look a i po]) (hp.trans (List.prefix_append _ _)) hw
  have hl : (h ++ [Fev.look a i po]).getLast? = some (.look a i po) := by simp
  unfold fevLookAt
  rw [hl]
  dsimp only
  rw [if_pos ⟨rfl, hes, hd⟩, List.dropLast_concat]

theorem fevLegBy_snoc (h : List Fev) (a : BitVec 64) (d : Nat) (nm : List (BitVec 8)) (i nl : Nat) :
    fevLegBy (h ++ [.ent a d nm (some i), .nlink a d nl]) a = true := by
  unfold fevLegBy; simp

/-! ### open's install, cited (NI M3 FS-2b′)

open's decisive event is its INSTALL, appended at the opened inode's row
under the lock that also held the type test, so the fold before it holds the
row the test read.  Its back-pointer reaches what fixed the inode: the walk's
last lookup (a plain open: the walk, followed, resolved to it), create's
`arm` (O_CREATE, made: the inode number recorded as given) or create's
lookup in the parent (O_CREATE, found: the parent recorded as given in the
lookup event, the entry the fold's). -/

/-- **WHAT FIXED THE INODE**, at the install's back-pointer `po` (NI M3
FS-2d, X2: a plain open's walk looked up exactly the names `es`) -/
def fevOpenFixed (H : List Fev) (a : BitVec 64) (rt s0 : Nat) (es : List (List (BitVec 8))) (create : Bool)
    (i : Nat) (po : Option Nat) : Bool :=
  if create then
    match po with
    | some p =>
      decide (p < H.length) &&
        (match H[p]? with
         | some (.arm a' i' _) => a' == a && i' == i
         | some (.hop a' d nm none) =>
           a' == a &&
             (match fevRows (H.take p) d with
              | some (.dir e, _) => e[nm]? == some i
              | _ => false)
         | _ => false)
    | none => false
  else
    (match po with
     | some q => decide (q < H.length)
     | none => true) && (fevChain H po).map Prod.snd == es && fevWalk H rt s0 (fevChain H po) == some i

/-- what fixed the inode survives the ledger's growth -/
theorem fevOpenFixed_mono {H H' : List Fev} (hp : H <+: H') {a : BitVec 64} {rt s0 : Nat}
    {es : List (List (BitVec 8))} {create : Bool} {i : Nat} {po : Option Nat}
    (h : fevOpenFixed H a rt s0 es create i po = true) :
    fevOpenFixed H' a rt s0 es create i po = true := by
  unfold fevOpenFixed at h ⊢
  cases create with
  | true =>
    simp only [if_true] at h ⊢
    cases po with
    | none => exact h
    | some p =>
      dsimp only at h ⊢
      rw [Bool.and_eq_true] at h
      obtain ⟨hlt, hc⟩ := h
      have hlt' : p < H.length := of_decide_eq_true hlt
      have hg : H'[p]? = H[p]? := by
        obtain ⟨t, rfl⟩ := hp; rw [List.getElem?_append_left hlt']
      have ht : H'.take p = H.take p := by
        obtain ⟨t, rfl⟩ := hp; rw [List.take_append_of_le_length (Nat.le_of_lt hlt')]
      rw [hg, ht, Bool.and_eq_true]
      exact ⟨decide_eq_true (Nat.lt_of_lt_of_le hlt' hp.length_le), hc⟩
  | false =>
    simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, beq_iff_eq] at h ⊢
    obtain ⟨⟨hpo, hm⟩, hi⟩ := h
    have hpo' : ∀ q, po = some q → q < H.length := by
      intro q hq; subst hq; exact of_decide_eq_true hpo
    have hw := fevWalkIs_mono (es := (fevChain H po).map Prod.snd) (d := i) hp ⟨hpo', rfl, hi⟩
    obtain ⟨hpo'', hes', hi'⟩ := hw
    refine ⟨⟨?_, ?_⟩, hi'⟩
    · cases po with
      | none => rfl
      | some q => exact decide_eq_true (hpo'' q rfl)
    · rw [hes', hm]

/-- a plain walk so far IS what fixed its inode -/
theorem fevOpenFixed_walk {H : List Fev} {rt s0 : Nat} {po : Option Nat} {es : List (List (BitVec 8))}
    {d : Nat} (a : BitVec 64) (hw : fevWalkIs H rt s0 po es d) :
    fevOpenFixed H a rt s0 es false d po = true := by
  obtain ⟨hpo, hes, hd⟩ := hw
  unfold fevOpenFixed
  simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨?_, hes⟩, hd⟩
  cases po with
  | none => rfl
  | some q => exact decide_eq_true (hpo q rfl)

/-! ## §3 The footprints (NI M3 FS-2d, for FS-4)

FS-4's private-footprint theorem restricts an era's history to the events
that MOVE a footprint `S` (`fevOn`): inode rows, single directory entries
`(d, nm)` and struct-file offsets.  When `S` is CLOSED (every entry of `S`
lives in a directory of `S`, `fevClosed`), the restriction keeps every
reading a class row makes inside `S`: the read's bytes (`fevReadBytes_on`)
and a lookup's answer (`fevHop_on`), by one fold-agreement lemma
(`fstAg_fevRun`: the fold of `h` and the fold of `fevOn S h` agree on `S`).
A hop's answer reads names and `S`-rows only, so the back-pointer positions
are bookkeeping under the restriction.  (The coordinator's prototype of
2026-10-06, verbatim.) -/

/-- **A FOOTPRINT**: the inode rows, the directory entries and the struct
files' offsets an incarnation's rows read -/
structure FsFoot where
  ino : Nat → Prop
  ent : Nat → List (BitVec 8) → Prop
  off : GName → Prop

/-- the event MOVES the footprint -/
def fevMoves (S : FsFoot) : Fev → Prop
  | .boot _ => True
  | .claim _ i _ | .arm _ i _ | .nlink _ i _ | .trunc _ i | .free _ i => S.ino i
  | .ent _ d nm _ => S.ent d nm
  | .write _ i γo held _ _ _ => S.ino i ∨ (held = false ∧ S.off γo)
  | .open _ _ γo held _ | .read _ _ γo held _ _ => held = false ∧ S.off γo
  | _ => False

/-- closed: an entry of S lives in a directory of S -/
def fevClosed (S : FsFoot) : Prop := ∀ d nm, S.ent d nm → S.ino d

noncomputable def fevOn (S : FsFoot) (h : List Fev) : List Fev :=
  open Classical in h.filter fun e => decide (fevMoves S e)

/-- two rows agree on S at inode `i` -/
def frowAg (S : FsFoot) (i : Nat) : Option (Fnode × Nat) → Option (Fnode × Nat) → Prop
  | some (.file a, n), some (.file b, n') => a = b ∧ n = n'
  | some (.dev a b, n), some (.dev a' b', n') => a = a' ∧ b = b' ∧ n = n'
  | some (.dir m, n), some (.dir m', n') => (∀ nm, S.ent i nm → m[nm]? = m'[nm]?) ∧ n = n'
  | none, none => True
  | _, _ => False

def fstAg (S : FsFoot) (s t : Frows × (GName → Nat)) : Prop :=
  (∀ i, S.ino i → frowAg S i (s.1 i) (t.1 i)) ∧ ∀ γ, S.off γ → s.2 γ = t.2 γ

theorem frowAg_refl (S : FsFoot) (i : Nat) : ∀ r, frowAg S i r r
  | some (.file _, _) => ⟨rfl, rfl⟩
  | some (.dev _ _, _) => ⟨rfl, rfl, rfl⟩
  | some (.dir _, _) => ⟨fun _ _ => rfl, rfl⟩
  | none => trivial

/-- a non-move keeps the S-view of the left state -/
theorem fstAg_skip (S : FsFoot) (hc : fevClosed S) (s t : Frows × (GName → Nat)) (e : Fev)
    (hm : ¬ fevMoves S e) (ha : fstAg S s t) : fstAg S (fevStep s e) t := by
  obtain ⟨hr, ho⟩ := ha
  cases e with
  | boot => exact absurd trivial hm
  | claim a i n | arm a i n | nlink a i nl | trunc a i | free a i =>
    refine ⟨fun j hj => ?_, ho⟩
    have : j ≠ i := fun h => hm (h ▸ hj)
    simpa [fevStep, frowsSet, this] using hr j hj
  | ent a d nm tg =>
    refine ⟨fun j hj => ?_, ho⟩
    by_cases hjd : j = d
    · subst hjd
      have := hr j hj
      simp only [fevStep, frowsSet, if_true]
      revert this
      cases hs : s.1 j with
      | none => intro h; exact h
      | some p =>
        obtain ⟨nd, nl⟩ := p
        cases nd with
        | dir m =>
          intro h
          cases ht : t.1 j with
          | none => rw [ht] at h; exact h.elim
          | some q =>
            obtain ⟨nd', nl'⟩ := q
            rw [ht] at h
            cases nd' with
            | dir m' =>
              refine ⟨fun x hx => ?_, h.2⟩
              have hne : nm ≠ x := fun he => hm (he ▸ hx)
              cases tg <;> simp [fentSet, Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase,
                hne, h.1 x hx]
            | _ => exact h.elim
        | _ => intro h; exact h
    · simpa [fevStep, frowsSet, hjd] using hr j hj
  | write a i γo held off bs r =>
    simp only [fevMoves, not_or, not_and] at hm
    refine ⟨fun j hj => ?_, fun γ hγ => ?_⟩
    · have : j ≠ i := fun h => hm.1 (h ▸ hj)
      simpa [fevStep, frowsSet, this] using hr j hj
    · cases held
      · have : γ ≠ γo := fun h => hm.2 rfl (h ▸ hγ)
        simpa [fevStep, foffSet, this] using ho γ hγ
      · simpa [fevStep] using ho γ hγ
  | «open» a i γo held po =>
    simp only [fevMoves, not_and] at hm
    refine ⟨fun j hj => by simpa [fevStep] using hr j hj, fun γ hγ => ?_⟩
    cases held
    · have : γ ≠ γo := fun h => hm rfl (h ▸ hγ)
      simpa [fevStep, foffSet, this] using ho γ hγ
    · simpa [fevStep] using ho γ hγ
  | read a i γo held off n =>
    simp only [fevMoves, not_and] at hm
    refine ⟨fun j hj => by simpa [fevStep] using hr j hj, fun γ hγ => ?_⟩
    cases held
    · have : γ ≠ γo := fun h => hm rfl (h ▸ hγ)
      simpa [fevStep, foffSet, this] using ho γ hγ
    · simpa [fevStep] using ho γ hγ
  | hop | look | stat | full => exact ⟨hr, ho⟩

/-- a move applied to both keeps agreement -/
theorem fstAg_both (S : FsFoot) (hc : fevClosed S) (s t : Frows × (GName → Nat)) (e : Fev)
    (ha : fstAg S s t) : fstAg S (fevStep s e) (fevStep t e) := by
  obtain ⟨hr, ho⟩ := ha
  have hoff : ∀ (o o' : GName → Nat) γo v, (∀ γ, S.off γ → o γ = o' γ) →
      ∀ γ, S.off γ → foffSet o γo v γ = foffSet o' γo v γ := by
    intro o o' γo v h γ hγ; unfold foffSet; split <;> simp_all
  have hset : ∀ (i : Nat) (v v' : Option (Fnode × Nat)), (S.ino i → frowAg S i v v') →
      ∀ j, S.ino j → frowAg S j (frowsSet s.1 i v j) (frowsSet t.1 i v' j) := by
    intro i v v' hv j hj; unfold frowsSet
    by_cases hji : j = i
    · subst hji; simp only [if_true]; exact hv hj
    · simp only [hji, if_false]; exact hr j hj
  cases e with
  | boot sb => exact ⟨fun j _ => frowAg_refl S j _, fun _ _ => rfl⟩
  | claim a i n | arm a i n | free a i =>
    exact ⟨hset _ _ _ (fun _ => frowAg_refl S _ _), ho⟩
  | nlink a i nl =>
    refine ⟨hset _ _ _ (fun hi => ?_), ho⟩
    have := hr i hi
    revert this
    cases s.1 i with
    | none => cases t.1 i with
      | none => intro _; trivial
      | some _ => intro h; exact h.elim
    | some p => cases t.1 i with
      | none => intro h; obtain ⟨nd, _⟩ := p; cases nd <;> exact h.elim
      | some q =>
        obtain ⟨nd, _⟩ := p; obtain ⟨nd', _⟩ := q
        cases nd <;> cases nd' <;> simp_all [frowAg, frowNlink]
  | trunc a i =>
    refine ⟨hset _ _ _ (fun hi => ?_), ho⟩
    have := hr i hi
    revert this
    cases s.1 i with
    | none => cases t.1 i with
      | none => intro _; trivial
      | some _ => intro h; exact h.elim
    | some p => cases t.1 i with
      | none => intro h; obtain ⟨nd, _⟩ := p; cases nd <;> exact h.elim
      | some q =>
        obtain ⟨nd, _⟩ := p; obtain ⟨nd', _⟩ := q
        cases nd <;> cases nd' <;> simp_all [frowAg, frowTrunc]
  | write a i γo held off bs r =>
    refine ⟨hset _ _ _ (fun hi => ?_), ?_⟩
    · have := hr i hi
      revert this
      cases s.1 i with
      | none => cases t.1 i with
        | none => intro _; trivial
        | some _ => intro h; exact h.elim
      | some p => cases t.1 i with
        | none => intro h; obtain ⟨nd, _⟩ := p; cases nd <;> exact h.elim
        | some q =>
          obtain ⟨nd, _⟩ := p; obtain ⟨nd', _⟩ := q
          cases nd <;> cases nd' <;> simp_all [frowAg, frowWrite]
    · cases held
      · exact hoff _ _ _ _ ho
      · exact ho
  | ent a d nm tg =>
    refine ⟨hset _ _ _ (fun hi => ?_), ho⟩
    have := hr d hi
    revert this
    cases s.1 d with
    | none => cases t.1 d with
      | none => intro _; trivial
      | some _ => intro h; exact h.elim
    | some p => cases t.1 d with
      | none => intro h; obtain ⟨nd, _⟩ := p; cases nd <;> exact h.elim
      | some q =>
        obtain ⟨nd, _⟩ := p; obtain ⟨nd', _⟩ := q
        cases nd <;> cases nd' <;> simp only [frowAg, frowEnt] <;> try (intro h; exact h)
        rename_i m m'
        intro h
        refine ⟨fun x hx => ?_, h.2⟩
        cases tg <;> simp only [fentSet, Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase] <;>
          split <;> simp_all
  | «open» a i γo held po =>
    refine ⟨hr, ?_⟩
    cases held
    · exact hoff _ _ _ _ ho
    · exact ho
  | read a i γo held off n =>
    refine ⟨hr, ?_⟩
    cases held
    · exact hoff _ _ _ _ ho
    · exact ho
  | hop | look | stat | full => exact ⟨hr, ho⟩

theorem fstAg_run (S : FsFoot) (hc : fevClosed S) :
    ∀ (h : List Fev) (s t : Frows × (GName → Nat)), fstAg S s t →
      fstAg S (h.foldl fevStep s) ((fevOn S h).foldl fevStep t) := by
  intro h
  induction h with
  | nil => intro s t ha; exact ha
  | cons e h ih =>
    intro s t ha
    classical
    unfold fevOn
    by_cases hm : fevMoves S e
    · rw [List.filter_cons_of_pos (by simpa using hm)]
      exact ih _ _ (fstAg_both S hc s t e ha)
    · rw [List.filter_cons_of_neg (by simpa using hm)]
      exact ih _ _ (fstAg_skip S hc s t e hm ha)

theorem fstAg_fevRun (S : FsFoot) (hc : fevClosed S) (h : List Fev) :
    fstAg S (fevRun h) (fevRun (fevOn S h)) :=
  fstAg_run S hc h _ _ ⟨fun j _ => frowAg_refl S j _, fun _ _ => rfl⟩

theorem fevReadBytes_on {S : FsFoot} {h : List Fev} {i : Nat} {γo : GName} (n : Nat) (hc : fevClosed S)
    (hi : S.ino i) (ho : S.off γo) :
    fevReadBytes h i γo n = fevReadBytes (fevOn S h) i γo n := by
  obtain ⟨hr, hoo⟩ := fstAg_fevRun S hc h
  have hrow := hr i hi
  have hcont : fevContent h i = fevContent (fevOn S h) i := by
    unfold fevContent fevRows
    revert hrow
    cases (fevRun h).1 i with
    | none => cases (fevRun (fevOn S h)).1 i with
      | none => intro _; rfl
      | some _ => intro h; exact h.elim
    | some p => cases (fevRun (fevOn S h)).1 i with
      | none => intro h; obtain ⟨nd, _⟩ := p; cases nd <;> exact h.elim
      | some q =>
        obtain ⟨nd, _⟩ := p; obtain ⟨nd', _⟩ := q
        cases nd <;> cases nd' <;> simp_all [frowAg]
  unfold fevReadBytes fevOff
  rw [hcont, hoo γo ho]

theorem fevHop_on {S : FsFoot} {h : List Fev} {d : Nat} {nm : List (BitVec 8)} (rt : Nat) (hc : fevClosed S)
    (he : S.ent d nm) : fevHop h rt d nm = fevHop (fevOn S h) rt d nm := by
  obtain ⟨hr, -⟩ := fstAg_fevRun S hc h
  have hrow := hr d (hc d nm he)
  unfold fevHop fevRows
  split
  · rfl
  · revert hrow
    cases (fevRun h).1 d with
    | none => cases (fevRun (fevOn S h)).1 d with
      | none => intro _; rfl
      | some _ => intro h; exact h.elim
    | some p => cases (fevRun (fevOn S h)).1 d with
      | none => intro h; obtain ⟨nd, _⟩ := p; cases nd <;> exact h.elim
      | some q =>
        obtain ⟨nd, _⟩ := p; obtain ⟨nd', _⟩ := q
        cases nd <;> cases nd' <;> simp_all [frowAg]

end Xv6
