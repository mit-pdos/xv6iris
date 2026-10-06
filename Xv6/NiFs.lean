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
  /-- a lookup of `nm` in `d`, at its instant; (NI M3 FS-2b) `prev` is the ledger
  position of the previous lookup of the SAME walk (`none` at a walk's first, and
  at a lookup no walk follows) -- a back-pointer, ledger bookkeeping -/
  | hop (act : BitVec 64) (d : Nat) (nm : List (BitVec 8)) (prev : Option Nat)
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
  | .write _ i γo off bs r => (frowsSet st.1 i (frowWrite off bs (st.1 i)), foffSet st.2 γo (off + r))
  | .trunc _ i => (frowsSet st.1 i (frowTrunc (st.1 i)), st.2)
  | .free _ i => (frowsSet st.1 i none, st.2)
  | .open _ _ γo => (st.1, foffSet st.2 γo 0)
  | .read _ _ γo off n => (st.1, foffSet st.2 γo (off + n))
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
  | .hop _ _ _ _ | .open _ _ _ | .read _ _ _ _ _ | .stat _ _ | .full _ _ | .look _ _ _ => True
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
from `po` -- made `m` lookups and resolved from `s0` to `i`; its reading is
`i` and `i`'s row in the fold before the observation (`none` otherwise) -/
def fevLookAt (H : List Fev) (a : BitVec 64) (rt s0 m : Nat) : Option (Nat × Option (Fnode × Nat)) :=
  match H.getLast? with
  | some (.look a' i po) =>
    if a' = a ∧ (fevChain H po).length = m ∧ fevWalk H rt s0 (fevChain H po) = some i then
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
    fevLookAt (h ++ [.look a i po]) a rt s0 es.length = some (i, fevRows h i) := by
  obtain ⟨hpo, hes, hd⟩ := fevWalkIs_mono (H' := h ++ [.look a i po]) (hp.trans (List.prefix_append _ _)) hw
  have hl : (h ++ [Fev.look a i po]).getLast? = some (.look a i po) := by simp
  unfold fevLookAt
  rw [hl]
  dsimp only
  rw [if_pos ⟨rfl, by rw [← hes, List.length_map], hd⟩, List.dropLast_concat]

theorem fevLegBy_snoc (h : List Fev) (a : BitVec 64) (d : Nat) (nm : List (BitVec 8)) (i nl : Nat) :
    fevLegBy (h ++ [.ent a d nm (some i), .nlink a d nl]) a = true := by
  unfold fevLegBy; simp

end Xv6
