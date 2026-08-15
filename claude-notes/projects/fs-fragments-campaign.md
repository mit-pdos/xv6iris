# The fragment campaign — worklist

The design of record is [`../design/fs-fragments.md`](../design/fs-fragments.md);
rulings **R1–R12** there bind this campaign and are not restated here. This
file is the LEDGER: what has landed, what each increment actually cost, what
diverged from the design's sketches, and what is left.

## Slate

| stage | what lands | files | gate | state |
|---|---|---|---|---|
| **F1a** | the pure tree type, `dir_view` (first-match), `dir_names_unique`, `node_rep`, `node_rep_inj`, `path_at` | `FsTree.v` (new) | none | **LANDED** |
| **F1b** | `fnode`/`fedges`/`fslice`/`fs_rep` as a reading over `dinode_at` + `inode_blocks` + `dir_links`; the frame law; the `".."` fact | `FsRep.v` (new) | F1a | **LANDED** |
| **F1.5b** | the edge-DELETE constructor | `DirLinks.v` (additive) | none | **LANDED** |
| **F1.5c** | (L5), `fdetached`, the mint, the option-indexed read at ilock, the axiom deletes | IcacheRef, InodeRegion, IcacheBoot, SpecIalloc, SpecIlock + 9, ProofCreate | **F1.5d** | NOT STARTED — **do not start** (R7) |
| **F1.5d** | `ireg_free_au`'s `c = None` | SpecIget + 4 sites, SpecIupdate, ProofIput | §20.17.5's residue + C′ (**the root clause is landed** — see below) | NOT STARTED |
| **F2** | path resolution as a logically-atomic triple (R8 — NOT a re-derivation of namex's post) | `FsLookup.v` (new) | F1b | **LANDED** |

`F1a`, `F1b` and `F1.5b` are the unconditional slate: purely additive, no
landed contract and no landed proof moved.

## What landed

### F1a — `iris/FsTree.v`

Pure, resource-free, `DirView.v`'s placement and style. Requires
`DirView` + `PathElems` (and, through `DirView`, `InodeInv` for `file_byte`).
`Print Assumptions` on every headline lemma: **closed under the global
context** — no axiom, not even functional extensionality.

The shape, per R1/R2:

- `fname := list (bv 8)` — definitionally `DirentEnc.bname 14`'s result and
  `PathElems.path_elems`'s element type, so paths need no coercion and no new
  datatype.
- `fsnode = NFile (list (bv 8)) | NDir (gmap fname Z)`;
  `fstree = MkTree { fs_nodes : gmap Z fsnode; fs_root : Z }`.
- `dir_view` is first-match-wins, via an `nrec`-FREE filter `dir_wins data k`
  ("live, and no earlier record carries this name"). **`dir_view_lookup` is
  the abstraction theorem**: `dir_view data nrec !! s` is exactly the inum of
  `dir_first data nrec s`, at every name. Everything else is read off it.
- `dir_names_unique` is the invariant; `dir_view_live` is "under it the view
  is the exact ANY-match map", and `dir_view_zero` is the unlink delta
  (`dir_view data' nrec = delete (dir_bname data k0) (dir_view data nrec)`),
  which is FALSE without the invariant — the unmasking argument.
- `node_rep` / `node_of` / `node_rep_node_of` / `node_rep_inj`; `path_at` as
  one `foldl` over `path_step`; `path_chain` for `fslice`; `fs_wf` and
  `fs_dirs_acyclic` as separate derived predicates.

### F1b — `iris/FsRep.v`

`fnode`, `fedges`, `fslice`, `fs_rep`, the frame law, `fnode_excl`, and the
`".."`-location lemma. Requires `InodeRegion` + `DirLinks` + `FsTree`.
`Print Assumptions` on every lemma: **closed under the global context** —
the standing six were not needed either.

R3 holds by construction: no new ghost name, no new authority, no invariant.
Every clause is a client-held fragment that already exists —
`InodeRegion.dinode_at` + `InodeInv.inode_blocks` for the node, and
`DirLinks.dir_links` VERBATIM for the edges (`fedges` is a name, not a
resource).

**The headline pair, §20.17.4's owed fact.** `fnode_dotdot` turns
`ents !! ".." = Some dp` into the RECORD INDEX `dirlookup` stops at — live,
naming `dp` — and `fedges_acc` hands out that index's `dir_link_at`. Between
them, S7's grey conversion can finally say WHICH `ilink dp` it converts,
which the model had no fact for: `dir_link_at` is keyed by record index and
is name-blind, and nothing places `".."` at index 1. The tree names the
record instead of positioning it, and `dir_view_lookup` turns the name back
into the index.

`fslice` is `fs_rep` restricted to `path_nodes t i p`; `fmap_rep_split` (the
filter/complement carve) is what makes it a SLICE rather than a second
predicate, and the whole frame law is `big_sepM_union` — free, exactly as
§2(iv) promised.

### F1.5b — `iris/DirLinks.v`, additive only

`dir_link_at_zeroed` / `dir_link_at_unlink` / `dir_links_unlink`: zeroing a
live non-self record's slot collapses its ticket and RELEASES one `ilink`,
`dir_links_dirlink`'s exact inverse. 137 lines, zero deletions, nothing
existing in the file touched. `Print Assumptions` on all three: **closed
under the global context**.

**Why it was owed.** Insert had a full resource story here
(`dir_link_at_dirlink` and its two siblings); delete had only the refcount
half — `InodeRegion.ireg_write_unlink` is the kernel's one nlink-LOWERING
region write, it CONSUMES an `ilink` as it lowers, and it has no caller
because nothing on the DirLinks side ever released the ticket out of a
zeroed record. These three close the asymmetry.

`dir_link_at_unlink` takes a LIVE-HOME premise, and that is not a
convenience: a grey record's target already has `di_nlink = 0`, there is no
count to lower, and the conversion S7 performs there is §20.17.4's different
move. Zero consumers today (sys_unlink has only `CodeSysUnlink.v`).

### The ROOT clause — `iris/InodeRegion.v`, `IcacheBoot.v`, `IregLinkNz.v`

R9's third owed item, and one of F1.5d's three gate planks. No new file, no
new ghost, no new premise on any of the six movers, no obligation threaded
to any caller. `Print Assumptions` on all seventeen touched/new lemmas —
the movers included — is **closed under the global context**.

**THE STATEMENT DIVERGES FROM §20.4's CHARTER, and the arithmetic is why.**
The charter is `ireg_body` gaining `⌜di_nlink (m !!! ROOTINO) ≥ 1⌝`. That
form is **not preservable**, and `ireg_write_unlink` is where it dies: the
kernel's one nlink-LOWERING region write knows `di_nlink dn = di_nlink dn' +
1` and, from the `ilink` it spends, `1 ≤ w`; at the root it must produce
`1 ≤ di_nlink dn'`, i.e. `2 ≤ di_nlink dn`, and the clause offers `1 ≤
di_nlink dn`. Nothing on the mover closes that gap honestly — the mover
cannot see that xv6 never unlinks the root, and the walk that can
(`sys_unlink` refusing `"."`/`".."`) is three contracts away.

What IS preservable is **(L1) made strict at the root**:

```coq
Definition ireg_root : Z := 1.
Definition ireg_root_ok (z : Z) (d : dinode) (w : nat) : Prop :=
  z = ireg_root -> (w < Z.to_nat (bv_unsigned (di_nlink d)))%nat.
```

— a conjunct of `ireg_slot`, beside `⌜ireg_link_ok d w⌝`. The charter's
statement is its one-line projection (`ireg_root_ok_alive`), so §20.4's
consumer gets exactly what it was promised.

**The root's slack is structural, not a coincidence of reachability.**
`dir_links` files one ledger unit per live NON-SELF record, so the root's
own `"."` and `".."` (both naming the root) are filed by nobody, while
every subdirectory's `".."` is filed against the root and is paid for by
create's `dp->nlink++`. The root's count is therefore permanently one more
than the number of records that can ever name it — the entry it does not
have in a parent. Strictness is the ledger carrying that one, so the mover
needs no premise.

**Two homes were forced, not chosen.** The clause CANNOT live in
`ireg_body`: strictness names `w`, which lives at the slot and nowhere else,
and a body-level clause over `m` would face the identical `ireg_write_unlink`
gap with less to work with. And it is a SEPARATE conjunct rather than a
fourth conjunct of `ireg_link_ok`, because that predicate is read by
projection all over the tree (`proj1 Hlok`, `ireg_link_ok_short`,
IregLinkNz's `destruct Hlok as [Hle _]`) — the recorded "adding a conjunct
to a Prop breaks every proj2" trap, dodged rather than paid for.

Mover by mover, all six free or refuted:

| mover | how the clause survives |
|---|---|
| `ireg_write_au` | `di_nlink_stable`'s first conjunct is an EQUALITY and `w` does not move — `ireg_root_ok_stable`, one rewrite |
| `ireg_write_link` | `w -> S w` and `nlink -> nlink + 1` in ONE ghost step; strict is monotone under a simultaneous bump (`ireg_root_ok_bump`) |
| `ireg_write_unlink` | the same step downwards (`ireg_root_ok_drop`) — the mover the chartered form could not survive, and it takes NO new premise |
| `ireg_claim_au` | **refuted**: the caller's buffer shows `di_type = 0`, (L3) forces `di_nlink = 0`, and `w < 0` is absurd. **ialloc can never claim the root** |
| `ireg_free_au` | **refuted** by the same two steps from its own `di_nlink dn = 0` (iput's `ip->nlink == 0` guard). **iput can never free the root** |
| `ireg_withdraw` | record, count and authority all unchanged |

**Licence (f)'s refutation** (§3.6's table row) lands in two forms:
`ireg_root_ok_ne` (pure — a record with `di_nlink = 0` is not the root,
which is a claim box by `fresh_shape_nlink` and iput's flush by its own
guard) and `InodeRegion.ireg_root_ne`, the mask-preserving accessor for a
caller holding `dinode_at γi inum dn` with `nlink dn = 0`. It gives back
`⌜bv_unsigned inum ≠ ireg_root⌝` and the fragment untouched.
`IregLinkNz.ireg_root_ROOTINO : bv_unsigned ROOTINO = ireg_root` is the
one-`reflexivity` bridge to `InodeInv.ROOTINO` — the region states the inum
as a `Z` literal for `ireg_link_ok`'s 32767's reason, so that a file 350
dependents deep does not acquire the in-core inode geometry for one
constant.

**The boot obligation** rides in `ireg_alloc`'s existing ∀-over-decodings
premise slot (its arity does not move), guarded by `z ∈ region_inums nib`
like its two neighbours, hence vacuous at `nib = 0`:

```coq
Definition image_root_alive (dss : list (list dinode)) (nib : nat) : Prop :=
  forall z : Z, z ∈ region_inums nib -> z = ireg_root ->
    1 <= bv_unsigned (di_nlink (image_dinode dss z)).
```

At boot the ledger is EMPTY, so the strict clause *is* §20.4's chartered one
verbatim (`ireg_root_ok_zero`) — one computational image obligation, true of
every mkfs image (mkfs's `ialloc` writes `nlink = 1` into the root and the
`"."`/`".."` it appends are self-records no `dir_links` unit is filed
against). `ireg_alloc` has no caller yet, so the third conjunct costs
nothing downstream.

### The `".."` INDEX BRIDGE — `iris/DirView.v`, `iris/DirLinks.v`

§20.17.4's owed fact: `dir_dots_ix self dn data` says a live directory's record 1 is
the live `".."`, and `DirLinks.dir_links_dotdot_out` borrows that index's
`dir_link_at` out of `dir_links` and returns it, so S7's `dp->nlink--` can
finally name the `ilink dp` it converts. `Print Assumptions` on both, and on
every discharge: **closed under the global context.**

**THE GUARD IS `T_DIR` *AND* `di_nlink <> 0`, AND THE TYPE GUARD ALONE IS
FALSE OF A REACHABLE PARKED STATE.** This is the correction the payload pass
found by road-testing the clause against create, and it is the difference
between a fact about directories and a fact a PAYLOAD can carry. create's
mkdir arm reaches `fail:` from three `bltz`es (`ProofCreate.v`, +0x10a /
+0x11e / +0x130) and re-parks the child's `ic_loaded` at every one of them;
at the first two the child IS a directory whose `".."` was never written —
the `"."` link fell short, or the `".."` link did — so a type-guarded clause
is not vacuous there, **it is false**, and no walk discharge exists. What
closes all three is the `sh zero,74(s3)` at +0x146: `ip->nlink = 0` is stored
BEFORE the re-park, so what the walk rebuilds is an ORPHAN and
`dir_dots_ix_orphan` closes it in one line at every entry, **with no
premise threaded to `cr_fail_mkdir_body`**. The rule the road test leaves
behind: **a payload conjunct is only as strong as the WORST state any walk
re-parks that payload in, and create's failure arms park directories that no
sane filesystem contains.**

**IT COUNTS ITS OWN RECORDS, WHICH IS WHAT MAKES THE PRESERVATION
SELF-SUPPLYING.** `dir_dots_ix_dirlink` has to know the write window is not
index 1, i.e. `dir_slot data nrec <> 1`: below `nrec` the slot is free
(`dir_slot_free`) while index 1 is live, and AT `nrec` the slot IS `nrec` —
which differs from 1 only because the clause carries `2 <= nrec`. Stated as a
premise on the lemma instead, that fact **has no supplier**:
nothing in any walk pins a parent directory's size, so every dirlink caller
would have to assume a directory it never measured has two records. Carrying
the count costs one `dir_nrec_mono` step per dirlink — the size only grows —
and closes the gap for every caller at once. `dir_links_dotdot_out`'s
`1 < dir_nrec` premise became a projection and is gone.

The discharge set is `dir_ok`'s four plus the one the guard adds:
`_not_dir`, `_free`, `_orphan` (new), `_eq` and `_dirlink`. Every field the
clause names is one a RECONSTRUCTING caller knows of its own `dn'`, which is
what the `dir_links_live` -> write -> `dir_links_of_ilink` round trip
demands. **`_eq` takes nlink as an IMPLICATION and size as a BOUND, not as
equalities**, and that is not generality for its own sake: create's
`dp->nlink++` at +0x134 re-parks the PARENT at
`cr_setf dp3 _ _ (di_nlink dp3 + 1)` (`ProofCreate.v`:8226-8234), a live
directory whose count moved, and the premise there is closed from create's
own `dp->nlink != 0` guard — `nlink + 1 <> 0` does NOT imply `nlink <> 0`,
so an equality-shaped congruence has no caller at the one site that needs
it.

**The two clauses partition the directory case.** `dir_dots_ix` is the
`nlink <> 0` half; the strong-`isdirempty` clause (`nlink = 0`, live records
are exactly `"."` and `".."`) is the other, and neither weakens the other.
That is why they ride beside each other in the payload rather than being one
predicate.

### F2 — `iris/FsLookup.v`

R8's increment: ONE `dirlookup` under ONE lock, read at the tree, lifted
CALLER-SIDE out of the landed `SpecDirlookup.wp_dirlookup_sconf`. Purely
additive — `SpecDirlookup` does not move (R10, §20.18 ruling 1) and `FsRep`'s
consumer set is unchanged (it had none). Requires `FsTree` + `FsRep` +
`SpecDirlookup`.

#### THE ATOMIC UPDATE OVER THE DIRECTORY'S OWN NODE IS UNSTATABLE, AND THAT IS A THEOREM

**RATIFIED (coordinator) as R8's IMPLEMENTATION FORM.** The house AU idiom
(`wp_log_write_au`, `ireg_write_au`) surrenders the caller's fragment through
a fupd fired at ONE ghost step, so the fragment need never sit in the caller's
hands across the call. It does not apply to a directory node, and it is
REFUTED BY THE TREE'S OWN LOCK PLACEMENT, twice over:

- `dirlookup`'s `readi` loop consumes `inode_blocks` from entry to return and
  the call SLEEPS, so the bytes half cannot arrive at one point and leave at
  another — a mask-changing fupd cannot be held open across a `WP Loop` step;
- the record half cannot travel either: the caller ALREADY holds `dinode_at`
  out of `ic_loaded`, so a second copy arriving through a client invariant
  meets `dinode_at_excl`.

So the node fragment is pinned in the caller's hands for the whole call — **by
the lock, which is exactly what makes the call atomic in the first place.**
This is §1.4's theorem (`fnode i n` is holdable only while `i` is locked)
meeting its FIRST CONCRETE INSTANCE, and it is why the linearization point is
not a ghost step to be chosen but the entire locked interval, during which the
node cannot move. R8's "logically atomic" therefore has exactly two pieces of
formal content and no third:

> **(LP1)** the triple's pre and post name the SAME `ents`, so the answer read
> out of the bytes IS the answer at the linearization point; and
> **(LP2)** the triple claims NOTHING about any other node — a client that
> wants a GLOBAL tree fact opens its own AMBIENT tree at that one instant.

Anyone who proposes surrendering `fnode` through a fupd at a `dirlookup`,
`readi` or `writei` boundary reads this first: the obstruction is the lock
discipline, not the spec's shape, so no restatement escapes it.

#### The lifting DISCHARGES a premise rather than adding one

`di_type dn = T_DIR` — the premise that refutes `panic("dirlookup not DIR")` —
falls out of `node_rep`'s NDir case (`node_rep_T_DIR`). What the triple still
takes is byte-level well-formedness the tree layer deliberately does not carry
(`inode_ok`, `dir_ok`) and that a caller holds beside the fragment in
`ic_loaded`.

#### What landed, by part

- `node_lookup_first` — the whole of F2's pure content in ONE equation: under
  `node_rep (NDir ents) dn data`, `ents !! s` IS the record inum of
  `dir_first data (dnrec dn) s`. Both arms (`node_lookup_found` /
  `node_lookup_none`) and both converses are read off it. It is
  `FsTree.dir_view_lookup` at a NODE rather than at a byte view.
- `fdir` — `fnode` with `dn`/`bm`/`data` NAMED. `fnode` hides them
  existentially, which is right for a tree statement and wrong at a call
  boundary: dirlookup's bundle (`inode_meta ip dn`, `inode_map γfs ip bm`)
  names them and nothing would tie the two together otherwise.
  `fdir_fnode` / `fnode_fdir` repack in both directions.
- `wp_dirlookup_tree_body` + `Module FsLookupTree (DL : DIRLOOKUP)` — the
  triple. Three differences from the landed body and no others: the type
  premise is gone, `inode_blocks` becomes `fdir` in pre and post, and each arm
  carries the tree answer BESIDE the byte one. The record index `k` survives
  deliberately: sys_unlink names the offset `16k` with it and iget's reference
  is at that record's inum.
- `dl_au` / `dl_au_fire` / `dl_au_found` / `dl_au_miss` — (LP2) made
  operational. The client's fupd surrenders `fs_rep t` for the tree WITHOUT
  the locked directory (`fs_nodes t !! dpi = None` — the hole is FORCED by
  `dinode_at_excl`, not a convenience) and takes it straight back, paying its
  own receipt at `tree_ent (tree_ins t dpi (NDir ents)) dpi s`. It is a SHAPE
  a client may choose, not a resource this file allocates (R3).

#### `dir_view_write` is `dir_view_zero`'s missing twin, and F3 needs both

F1a landed the tree delta of an UNLINK; this is the tree delta of a DIRLINK —
writing name `s` at inum `z` into a free slot inserts exactly that binding and
moves nothing else, and, like its twin, it is FALSE without `dir_names_unique`
on the way in. ONE clause covers both of dirlink's arms: `dir_written_at`
(stated over `DirView.dir_win_agree`, so a byte-range postcondition converts
with `dir_win_agree_below`) plus separate `nrec`/`nrec'` counts, so the APPEND
arm (`k0 = nrec`, count grows) and the REUSE arm (`k0 < nrec` at a free
record) are one lemma rather than two. `node_rep_insert` / `node_rep_delete`
lift them to a node, and `dir_first_after_write` / `dir_first_after_zero` are
the OPERATIONAL forms — what the NEXT scan does: it finds the written record
at exactly the slot dirlink used (uniqueness pins it to `k0`, which is what
lets a caller name the offset), and it misses the zeroed name.

#### §20.17.4's owed `".."` fact — **CLOSED**, both halves joined

`node_dots_first` / `node_dots_index` / `fdir_dots_index` compose the PAYLOAD
half (`DirView.dir_dots_ix self dn data`: a LIVE directory's record 0 is a
live `"."` naming `self` and its record 1 is a live `".."`) with the TREE half
(`ents !! ".." = Some dp`, a conjunct of `fnode`) and conclude they are the
SAME NUMBER: `dp = bv_unsigned (dir_inum data 1)`, with `dir_first data nrec
".." = Some 1`. Neither half can state the other — "the parent" is a relation
between two inodes and a conjunct on ONE payload cannot say it, while
`dir_link_at` is keyed by record INDEX and is name-blind. Feed that number to
`DirLinks.dir_links_dotdot_out` and the `ilink dp` S7 must convert is in hand.
`Print Assumptions` on all five: **closed under the global context.**

**`dir_names_unique` IS WHAT JOINS THEM**, and this is the third place R2's
amendment pays for itself: under the invariant any-match is first-match, so
the live `".."` at index 1 is the ONLY live `".."`. Worth seeing exactly how
the index-0 collision dies — **by UNIQUENESS, not by `dot_name <> dotdot_name`**:
record 0 is a live `"."`, so if it also matched `".."` the invariant would
force `0 = 1`. The composition never needs a name disequality.

**THE CLAUSE'S GROWTH ALL PAID OUT HERE.** The payload pass gave
`dir_dots_ix` a `"."` half, a `di_nlink <> 0` guard and a `self` parameter on
its way into the escrow payloads. Three consequences at the tree, all
favourable:

- `2 <= dir_nrec (di_size dn)` is no longer a PREMISE this layer takes — it is
  a PROJECTION of the clause, so the composition is self-supplying where the
  earlier sketch made every caller carry the record count;
- the record-0 facts come free, so the `"."` edge is readable at the tree too
  (`ents !! DOT = Some self`) — the self-loop the ledger deliberately files no
  `dir_links` unit against, now visible as an ordinary entry — and `self <> 0`
  falls out of `dir_dots_ix_self`;
- **the fragment is indexed at `self`, and that is the coupling**: the tree's
  node key and the payload's `self` are the same number precisely because
  record 0's `"."` names the node's own inum. It costs no arity anywhere,
  because both payloads have the inum in hand.

The `di_nlink <> 0` guard travels as a premise and is not a burden: every
caller in the S7 walk holds it already (create's guard at `sysfile.c:262`,
namex's at `fs.c:693`), and an ORPHANED directory is the complement clause's
business. `fdir_dots_index` also discharges `dir_links_dotdot_out`'s own
`bv_unsigned (dir_inum data 1) <> self` premise **at the tree**, from
`dp <> self` — "the parent is not the child" is a statement the tree can make
and the bytes cannot. `DOT_dot_name` / `DOTDOT_dotdot_name` bridge the tree
layer's `mword` spelling of the two names to the record view's `bv` one.

#### A tactic trap worth keeping

`FsTree.v` does not import the proofmode and `FsLookup.v` does, so its
`rewrite` is **ssreflect's** — `rewrite lem by tac` is REJECTED (BvShift.v's
note) even though the identical line compiles one file down. Side conditions
go to `//` with the hypothesis already in context. `rewrite <- lem` is fine.

## Divergences from the verification report's sketches

The report (fs-fragments.md §1–§6) was written against the tree three merges
back. These differ at the code level; none moves a ruling.

1. **`node_rep` is a FUNCTION, and that is what makes `node_rep_inj`
   cheap.** The report calls `node_rep_inj` "F1's one real proof obligation"
   by analogy with `diblk_bytes_inj`, which is a genuine injectivity proof
   over an encoding. Here bytes -> tree is one-directional by construction
   (§1.2), so the sharp statement is `node_rep_node_of` — any node
   representing `(dn, data)` IS `node_of dn data` — and injectivity is its
   two-line corollary. The obligation is real and it is discharged; it is
   just smaller than the analogy suggested, because the relation was stated
   in the direction the design demands.

2. **`dinode_at` is keyed by `bv 32`, not `Z`.**
   `InodeRegion.dinode_at (γi : gname) (inum : bv 32) (dn : dinode)`
   (`iris/InodeRegion.v:560`) wraps a `ghost_map Z dinode` element at
   `bv_unsigned inum`. R1's reason 1 still holds — the map underneath IS
   `Z`-keyed — but the fragment's own signature is not, so `FsRep.inum_of`
   is `Z_to_bv 32` and `FsTree.fs_inums_ok` carries `0 <= i < 2 ^ 32` to make
   it round-trip (`inum_of_unsigned`). §2(i)'s `inum_of` was a placeholder;
   this is what it has to be.

3. **`inode_blocks` takes a `blkmap`, and `fnode` does NOT couple it to
   `dn`.** `InodeInv.inode_blocks γfs bm data` (`iris/InodeInv.v:790`) is one
   `blk_res` per file index of `bm`; the coupling to `di_addrs` lives in
   `InodeLock.inode_ok cov logstart dn bm data`, which would put `cov` and
   `logstart` on every `fnode` for a fact this layer never reads. `fnode`
   existentially quantifies `bm` and states no `inode_ok`; a caller that
   wants the coupling still has it in the escrow payload it carved the
   `fnode` out of.

4. **`fnode` has no `Timeless` instance.** `inode_blocks`'s own instance
   lives in `IcacheEscrow.v:234`, ABOVE `FsRep.v`. Requiring the escrow to
   get it would enlarge the cone for a property nothing needs — R3 forbids
   the invariant that would be its only consumer. A file above IcacheEscrow
   can declare it in one line.

5. **`node_rep`'s NFile case demands a NONZERO type.** The report's fsnode
   has two constructors and says nothing about free inodes. A type-0 record
   would otherwise represent `NFile []`, i.e. the tree would silently contain
   free inodes and `fs_rep` would stop being a statement about the file
   system. `node_rep_alloc` is the resulting one-liner, and it is what
   `fnode` hands a caller that needs allocatedness.

## How the gates were run, and the trap in them

Compiles are mirror-only. Two things about that are worth keeping:

- **The mirror's `.vo` tree can be bulk-touched by a coordinator sync, and
  then `make` validates NOTHING while reporting success.** A whole-tree
  rsync plus a `touch` of every `.vo` leaves each `.vo` newer than each
  `.v`; `make` says "Nothing to be done for 'real-all'" with zero compile
  lines, which is indistinguishable at a glance from a real green cone. The
  tell is `ls --time-style=full-iso`: identical timestamps to the NANOSECOND
  across unrelated files. The fix — reverse transitive closure out of
  `.CoqMakefile.d`, `rm` those `.vo`, rebuild — is now a durable-notes rule.
- **A LIVE SIBLING LANE UNDER YOUR CONE MAKES THE SHARED MIRROR UNGATEABLE,
  AND THE FIX IS A LANE TREE, NOT A SMALLER GATE.** `DirView.v`'s cone is
  **400** files; the file layer's is **387**, and 387 of those 400 are the
  same files — because `FileInvDefs.v` sits under `ProcInv.v`, so a lane
  editing the file layer owns almost everything below any fs change. With
  its sources dirty in the shared mirror, `make` in that tree compiles ITS
  in-flight work: a red that is not yours, or a green built from code nobody
  committed. `cp -a` the mirror to a private lane tree (`/shared/xv6iris-frag`,
  the bump lane's precedent), `git checkout --` the OTHER lane's dirty paths
  **in the copy only**, confirm `git status --porcelain` lists exactly your
  own files, then `rm` the cone and build there. Copying the `.vo` tree along
  is what keeps it to one cone instead of a from-scratch build.
- **`DirLinks.v`'s cone is 142 files**, and the only two that consume the
  ticket lemmas at all are `ProofCreate.v` and `ProofSysLink.v`
  (`SpecDirlink.v` and `SpecSysLink.v` name them in prose only). Both are in
  the cone and both must recompile unchanged; that is F1.5b's whole gate,
  and it passed: 143 files, `EXIT=0`, zero `Error` lines, with
  `ProofCreate.v` and `ProofSysLink.v` the last two to finish.

## Owed, and where it lives

Carried forward from R9; none of it is F1a/F1b/F1.5b's to discharge.

- `isdirempty`'s invariant — S7's brief, as a PREREQUISITE of
  `create_fresh_ty`'s retirement, not a local convenience.
- `SpecIget`'s licence enumeration (C′), or fs-icache §20.17.7's kernel fix.

## THE PAYLOAD-CONJUNCT PASS — LANDED, and what the road test changed

`DirView.dir_dots_ix` rides beside `dir_ok` in `IcacheEscrow.ipool_alloc` and
`ic_loaded`. What landed is NOT the clause the design charted, and the two
differences were both forced by walks, not chosen.

**IT PINS BOTH DOT RECORDS, AND THE `"."` HALF IS THE ONLY SUPPLIER OF THE
PARENT'S INUM.** The charted clause was the `".."` index alone. Its
establishment — create's `dirlink(ip, "..", dp->inum)` — must show record 1
is LIVE, which is `dp->inum <> 0`, and **nothing in the tree supplies that**:
`IcacheRef.inode_held` (`IcacheRef.v`:1458-1462) keeps only
`bv_unsigned inum < 16 * icfg_nib`, and namex hands back an entry POINTER, so
`SpecDirlookup`'s own `0 < bv_unsigned inum` (`SpecDirlookup.v`:672) is
dropped at the boundary. Strengthening `inode_held` was the obvious fix and
is out of reach: `p->cwd`'s `inode_held` would owe the same fact, which means
a `ProcInv` invariant and a 316-file cone. So the clause carries `self`
(both payloads have the inum in hand, so it costs no arity anywhere) and says
a live directory's record 0 is a live `"."` naming ITSELF —
`dir_dots_ix_self` then reads `dp->inum <> 0` off the PARENT's own payload,
which create is already holding. **The rule: when an establishment needs a
fact about ANOTHER object, look for a payload clause that object already
carries before threading a premise up through a contract.**

**THE GUARD IS `T_DIR` AND `nlink <> 0`, AND THE COUNT IS A CONJUNCT.** Both
recorded in `DirView.v`'s header: the type-only guard is FALSE at two of
`cr_fail_mkdir_body`'s three entries, and `2 <= dir_nrec` as a premise has no
supplier, so it is carried. `dir_dots_ix_dirlink` therefore takes no count
premise and no caller has to measure a directory it never read.

### What it cost, per site

| site | discharge |
|---|---|
| every peel/re-park that moves nothing (`ProofNamex` ×4, `ProofSysChdir` ×2, `ProofKexecA` ×3, `ProofKexecB2`/`B3`, `ProofFileread` ×2, `ProofFilestat`, `ProofIput` ×2, `ProofSysOpen`, `ProofSysLink` ×3, `ProofCreate` ×4) | transfer — one name in the destruct, one `iSplitR` in the rebuild |
| `ProofIlock`'s fill | transfer out of `ipool_alloc`'s allocated arm |
| `ProofIlock`'s CLAIM BOX | `dir_dots_ix_orphan` off `fresh_shape_nlink` |
| `ProofFilewrite`, `ProofSysOpenParts`' O_TRUNC, `ProofSysLink`'s `ip->nlink++`, create's non-dir child | `dir_dots_ix_not_dir` |
| `ProofSysLinkTails`' `ip->nlink--` | `sl_setnl_ddix`, the congruence at a moved count |
| create's parent, across its own `dirlink` (×3) | `dir_dots_ix_dirlink` |
| create's parent at `dp->nlink++` | `dir_dots_ix_eq`, nlink as an implication closed from create's guard |
| create's three `fail:` entries | `dir_dots_ix_orphan` — ONE line, because `sh zero,74(s3)` precedes the re-park |
| **create's `dirlink(ip,"..")`** | **the establishment** — `cr_dotdot_record` + `cr_dot_record` + `dir_dots_ix_self` at the parent |
| boot | threaded, zero obligation (`IcacheBoot`) |

### THE ATTEMPTED FOLD OF THE COMPLEMENT CLAUSE — REVERTED, and where it stops

The strong-isdirempty clause (`dir_orphan_clean`: a `T_DIR` record at
`nlink = 0` has every live record's name in `{".", ".."}`) was folded into
this sweep to pay the arity once. **It does not close, and the obstruction is
one site: `sys_link`'s `bad:` tail.** The clause is trivial everywhere else —
vacuous at every live directory, `not_dir` at every file, `size_zero` at the
claim box and the truncated corpse, a transfer at every peel — but
`ProofSysLinkTails`' `ip->nlink--` re-parks a record that its OWN `ilock`
produced, so the record is an existential and the walk cannot say it is not a
directory. The natural fix (pass the caller's `ity_shot` and agree the types)
**fails at the generation**: the call sites re-introduce the generation
existentially (`inode_shr_gen_intro`), so no shot at the tail's `gy` exists to
agree with. `dir_dots_ix` is no help — it speaks only above `nlink <> 0`, and
the site is exactly the drop to zero.

So the complement clause needs its own design step before it can ride in the
payload, and it is about `sys_link`'s tail alone. Its **definition and five
discharges are landed in `DirView.v`** (`dir_dots_only`, `dir_orphan_clean`,
`_not_dir`, `_free`, `_live`, `_size_zero`, `_of_only`, `dir_dots_only_of`,
`dir_dots_only_dirlink`), so the design step has its vocabulary and the
arity sweep is the only part that must be paid twice.

## THE PAYLOAD SWEEP'S SITE COUNT, and the two traps in measuring it

**A `∗`-conjunct in `ic_loaded` costs ~45 sites, not the six the constructor
lemmas suggest**, because every hand-rolled destruct and rebuild moves too.
Raw `rewrite /ic_loaded` (or `/ipool_shape`) sites, per file: `ProofSysLink`
6, `IcacheEscrow` 5, `ProofNamex` 4, `ProofKexecA` 3, `ProofFileread` 3,
`ProofCreate` 3, `SpecKexecB2` 2, `ProofSysChdir` 2, `ProofIlock` 2,
`ProofFilewrite` 2, `ProofFilestat` 2, `IcacheBoot` 2, `ProofSysLinkTails` 1,
`ProofIput` 1 — plus ~15 `ic_mk_loaded` / `kxc_load_peel` / `kxc_load_seal`
applications that each gain an argument.

Two ways that count comes out wrong:

- **ANONYMOUS POSITIONAL DESTRUCTS DO NOT MENTION THE PREDICATE AT ALL.**
  `IcacheEscrow.ic_payload_size` opens the payload as
  `"(_ & _ & _ & _ & Hmeta & _)"` through `rewrite /ic_payload`, so it
  matches no grep for `ic_loaded` and fails only at `Qed`-time with an
  `iExact` mismatch naming an unrelated hypothesis. Grep for the underscore
  runs too.
- **A SPEC THAT RE-EXPORTS THE PAYLOAD'S PIECES DOES NOT HAVE TO RE-EXPORT
  THE NEW ONE.** `ProofSysOpenParts.so_loaded_open` names the conjunct in its
  intro pattern and drops it; its caller's pattern must NOT gain a name.
  Getting this backwards produces `iExistDestruct: cannot destruct` at the
  CALLER, which reads like a payload error and is a lemma-statement one.

**Folding a SECOND clause into the same sweep is worth it when it closes**
(the arity is paid once), and the fold is cheap to attempt and cheap to
revert — but revert it with a script that removes whole `iSplitR; [...|].`
blocks, not lines: a line-wise revert leaves dangling `iSplitR;` heads that
surface as *"Syntax error: ']' expected after [for_each_goal]"* far from the
edit, and a `replace(...,'',1)` on a fragment that occurs several times in a
file will take out the wrong one.

## Standing constraints (do not violate, do not re-propose)

- **(L6) `c <> None -> inreg` MUST NEVER BE STATED** (R5). It discharges the
  free in two lines and collapses the design into §20.16.3 verbatim.
- No whole-tree authority, no new gname, no new invariant (R3).
- The ledger dimension (`dl`/`crz` credit) stays OUTSIDE the algebra (R12);
  only F3's syscall boundary can hide it.
- No new `Axiom` or `Parameter` anywhere — §4.1's twice-instantiate audit
  must stay clean. F1a and F1b introduce none.
- `g` (the grey colour) is a discriminator NOWHERE (§4.2(c), foreclosed
  permanently by §20.18 ruling 2).

## F1.5b's FIRST-CONSUMER VERDICT (S7-unlink's road test)

**The constructor's SHAPE fits; its PREMISE SET does not.**  `sys_unlink`
is F1.5b's designated first consumer and it stopped before writing a
contract, on two facts the algebra cannot supply.  The full record is in
[`fs-sysfile.md`](fs-sysfile.md), "S7-unlink — STOPPED"; what belongs here
is what it asks of the campaign.

### What fitted, verbatim

`dir_links_unlink`'s statement is the walk's sequencing exactly:
`memset(&de,0,16)` then `writei(dp,0,&de,off,16)` delivers the range
clause as written (`2 <= tot <= 16`, `de_inum d = bv_0 16`, the type /
nlink / size trio unmoved), `dirlookup`'s found arm supplies `k0` and its
liveness (`SpecDirlookup.v:270`, `dir_first data nrec s = Some k0`), and
the released `ilink` is precisely what `SpecIupdate.wp_iupdate_unlink`
consumes one instruction group later.  `dir_link_at_zeroed` and
`IregLinkNz.dir_links_nlink_drop` compose with no glue at all.  **Nothing
in the constructor needs restating for the walk's shape.**

### AMENDMENT (1) IS NOT NEEDED — the home-live premise comes from the
### STRONG isdirempty invariant, which the KERNEL FIX makes true

`dir_link_at_unlink` / `dir_links_unlink` take the HOME-LIVE premise
`bv_unsigned (di_nlink dn) <> 0`, and the landed sources of that fact are
all kernel `nlink == 0` guards walked in the same critical section —
create's at `sysfile.c:262` (→ `ProofCreate.v:7914`), namex's at
`fs.c:693` (→ `ProofNamex.v:3315`).  `sys_unlink` has no such guard and
the walker's does not cross its `iunlock`/re-`ilock` window, so the
premise has to come from the invariant instead:

> an orphaned directory holds only dot records; `sys_unlink`'s two
> `namecmp` refusals say the matched record is not a dot record; so the
> home is not orphaned.

That derivation is sound **only once the invariant is true**, which is
what the kernel fix below buys.  A weaker route — putting the record's
NAME into `dir_link_at`'s grey disjunct, so the `namecmp` refusals refute
grey directly — was proposed and is **SUPERSEDED: do not pursue it.**  It
bought only `sys_unlink`'s own zeroing and left §20.6's itrunc row open,
whereas the strong invariant discharges both.  fs-icache.md §20.17.4
sharpening (b)'s name-blindness therefore STANDS.

### AMENDMENT ASKED FOR (2): the `".."`-location fact needs a SUPPLIER,
### not just a reading

The T_DIR arm's `dp->nlink--` needs an `ilink dp`, whose only home is
`ip`'s `".."` record — fs-icache.md §20.17.4's "S7's blocker", still open.
`FsRep.fnode_dotdot` is the right READING but not a supplier: `fnode` is a
derived predicate over client-held fragments (R3) and no payload hands one
out, so nothing bridges "`ents ip !! ".."` is `dp`" to "record `k` of
`ip`'s data names `dp`".  §20.17.4's own prescription — a payload conjunct
beside `dir_links`, established at create's `dirlink(ip, "..", dp->inum)`
— is what is missing, and it is the same conjunct amendment (1) wants for
the grey clause.  **Both blockers close in one place.**

### THE isdirempty INVARIANT, stated — F1.5d's PLANK, and true of the
### FIXED binary

R9 registers it as a prerequisite of `create_fresh_ty`'s retirement.  The
statement, over `DirView`'s record vocabulary, is

```
  bv_unsigned (di_type dn) = T_DIR_z -> bv_unsigned (di_nlink dn) = 0 ->
    forall k, (k < dir_nrec (bv_unsigned (di_size dn)))%nat ->
      dir_live data k ->
        dir_bname data k = bname 14 "." \/ dir_bname data k = bname 14 ".."
```

as a payload conjunct riding beside `dir_links` in `ic_loaded` /
`ipool_alloc` — i.e. **an orphaned directory's live records are exactly
`"."` and `".."`**.  It carries three loads at once: §20.6's itrunc-row
obligation, §20.17.5's residue closure, and — the thing that was not
noticed until S7 road-tested it — **`sys_unlink`'s own INPUT premise**,
since a live non-dot record under it forces `di_nlink dp <> 0`, which is
`dir_links_unlink`'s home-live premise.

It was FALSE of the binary and `sys_link` was why: `nameiparent(new, name)`
→ `ilock(dp)` → `dirlink(dp, name, ip->inum)` with **no `dp->nlink == 0`
re-check** (contrast create's at `sysfile.c:262`).  namex's guard fires
under the WALKER's lock and sys_link re-locks afterwards, so a concurrent
`rmdir dp` in that window appends a non-dot record to an orphaned
directory — a real leak, and in the model a stranded `ilink`, which is
precisely what §20.6's itrunc row calls "a blocker on a reachable step".

**RULED real, KERNEL FIX TAKEN, AND LANDED.**  `XV6_REV` is `f60ff58`:
create's guard verbatim, routed to `bad:`, seven lines of C and five
instructions.  So the clause above is a property of the pinned binary and
needs no weakening, and the walk that has to preserve it is proven against
the image that enforces it (`sys_link`'s ARM E2, `ProofSysLinkTails.sl_tail_e2`).
What still gates F1.5d is finding 2 alone — §20.17.4's `".."`-location
fact.  See [`../kernel-defects.md`](../kernel-defects.md) and
[`../xv6-bump-playbook.md`](../xv6-bump-playbook.md).
