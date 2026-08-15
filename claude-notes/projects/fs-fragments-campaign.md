# The fragment campaign — worklist

The design of record is [`../design/fs-fragments.md`](../design/fs-fragments.md);
rulings **R1–R12** there bind this campaign and are not restated here. This
file is the LEDGER: what has landed, what each increment actually cost, what
diverged from the design's sketches, and what is left.

## Slate

| stage | what lands | files | gate | state |
|---|---|---|---|---|
| **F1a** | the pure tree type, `dir_view` (first-match), `dir_names_unique`, `node_rep`, `node_rep_inj`, `path_at` | `FsTree.v` (new) | none | **LANDED** |
| **F1b** | `fnode`/`fedges`/`fslice`/`fs_rep` as a reading over `dinode_at` + `inode_blocks` + `dir_links`; the frame law; the `".."` fact | `FsRep.v` (new) | F1a | IN FLIGHT |
| **F1.5b** | the edge-DELETE constructor | `DirLinks.v` (additive) | none | QUEUED |
| **F1.5c** | (L5), `fdetached`, the mint, the option-indexed read at ilock, the axiom deletes | IcacheRef, InodeRegion, IcacheBoot, SpecIalloc, SpecIlock + 9, ProofCreate | **F1.5d** | NOT STARTED — **do not start** (R7) |
| **F1.5d** | `ireg_free_au`'s `c = None` | SpecIget + 4 sites, SpecIupdate, ProofIput | §20.17.5's residue + the unlanded root clause + C′ | NOT STARTED |
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

2. **`node_rep`'s NFile case demands a NONZERO type.** The report's fsnode
   has two constructors and says nothing about free inodes. A type-0 record
   would otherwise represent `NFile []`, i.e. the tree would silently contain
   free inodes and `fs_rep` would stop being a statement about the file
   system. `node_rep_alloc` is the resulting one-liner, and it is what
   `fnode` hands a caller that needs allocatedness.

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
