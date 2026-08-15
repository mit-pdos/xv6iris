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
| **F2** | path resolution as a logically-atomic triple (R8 — NOT a re-derivation of namex's post) | — | F1b | NOT STARTED |

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
- **`DirLinks.v`'s cone is 142 files**, and the only two that consume the
  ticket lemmas at all are `ProofCreate.v` and `ProofSysLink.v`
  (`SpecDirlink.v` and `SpecSysLink.v` name them in prose only). Both are in
  the cone and both must recompile unchanged; that is F1.5b's whole gate,
  and it passed: 143 files, `EXIT=0`, zero `Error` lines, with
  `ProofCreate.v` and `ProofSysLink.v` the last two to finish.

## Owed, and where it lives

Carried forward from R9; none of it is F1a/F1b/F1.5b's to discharge.

- the ROOT clause `di_nlink ROOTINO >= 1` in `ireg_body` — §20.4 chartered
  it, never landed; licence (f)'s refutation needs it.
- `isdirempty`'s invariant — S7's brief, as a PREREQUISITE of
  `create_fresh_ty`'s retirement, not a local convenience.
- `SpecIget`'s licence enumeration (C′), or fs-icache §20.17.7's kernel fix.

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

### AMENDMENT ASKED FOR (1): the grey disjunct must carry the NAME

`dir_link_at_unlink` / `dir_links_unlink` take the HOME-LIVE premise
`bv_unsigned (di_nlink dn) <> 0`, and **sys_unlink cannot supply it.**
Every landed consumer of `dir_link_at_live` gets that premise from a
kernel `nlink == 0` guard walked in the same critical section — create's
at `sysfile.c:262` (→ `ProofCreate.v:7914`), namex's at `fs.c:693` (→
`ProofNamex.v:3315`) — and **sys_unlink has no such guard**; the walker's
guard does not cross its `iunlock`/re-`ilock` window.

What sys_unlink DOES hold is the two `namecmp` refusals, i.e. the matched
record's name is neither `"."` nor `".."`.  A grey ticket is only ever
§20.8's orphaned `".."`.  So the amendment is one pure conjunct inside
`dir_link_at`'s grey disjunct — *the record's name is* `".."` — and
`dir_links_unlink`'s home-live premise then becomes
`dir_bname data k0 <> bname 14 ".."`, which the walk discharges from
`SpecNamecmp`'s iff.

This reverses fs-icache.md §20.17.4 sharpening (b), which chose
name-blindness on the grounds that it is "strictly better than the
ruling's step 5 needs".  It is strictly WORSE for the first consumer, and
§20.17.5's shelter (iii) — refuted for `dirlink`, because `skipelem` will
hand it `".."` — **holds for `sys_unlink`**, whose guards are explicit.
The clause is preservable by inspection: nothing landed produces a grey in
a `dir_links` at all (boot mints `g = 0`; `link_grey_of_link` has no
caller), the only future producer is S7's own conversion at `ip`'s `".."`,
and every existing constructor's range clause already gives the
name-agreement the untouched records need.

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

### THE isdirempty INVARIANT, stated — and REFUTED as an invariant of the
### landed binary

R9 registers it as a prerequisite of `create_fresh_ty`'s retirement.  The
statement it wants is, over `DirView`'s record vocabulary,

```
  bv_unsigned (di_type dn) = T_DIR_z -> bv_unsigned (di_nlink dn) = 0 ->
    forall k, (k < dir_nrec (bv_unsigned (di_size dn)))%nat ->
      dir_live data k ->
        dir_bname data k = bname 14 "." \/ dir_bname data k = bname 14 ".."
```

as a payload conjunct riding beside `dir_links` in `ic_loaded` /
`ipool_alloc` — i.e. **an orphaned directory's live records are exactly
`"."` and `".."`** — which is §20.6's itrunc-row obligation and §20.17.5's
residue closure in one clause.

**It also turns out to be sys_unlink's own INPUT premise**, not merely its
output obligation: under it, a live record whose name is neither dot
forces `di_nlink dp <> 0`, which is amendment (1)'s premise by another
route.

**But it is FALSE of the landed kernel, and `sys_link` is why.**
`sys_link` does `nameiparent(new, name)` → `ilock(dp)` → `dirlink(dp,
name, ip->inum)` with **no `dp->nlink == 0` re-check** (`sysfile.c`'s
sys_link; contrast create's at `:262`).  namex's guard fires under the
WALKER's lock and sys_link re-locks afterwards, so a concurrent `rmdir dp`
in that window lets sys_link append a non-dot record to an orphaned
directory.  The consequence is a real leak, and it is exactly the shape
§20.6's itrunc row calls "a blocker on a reachable step": `dp` is later
freed by `iput` → `itrunc`, which discards the record WITHOUT decrementing
`ip->nlink`, so `ip` is never freed and its `ilink` is stranded.

So F1.5d's gate needs a ruling: either the kernel gains sys_link's missing
guard (the same one-line shape `117c0e7` gave create and `fs.c:693` gave
namex — this is a kernel-defect candidate, filed in
[`../kernel-defects.md`](../kernel-defects.md)), or the invariant is
weakened to something sys_link's unguarded `dirlink` preserves.
**Amendment (1)'s name-carrying grey clause is such a weakening** — it is
preserved by sys_link (the record sys_link appends carries an `ilink`, not
a grey) and it is all sys_unlink's own zeroing needs.  It does NOT
discharge §20.6's itrunc row, which genuinely wants the full statement
above.
