# fs-namei — the directory & path campaign (fs.c's remaining 11)

OPENED 2026-08-11, immediately after the Plan-B share trial completed.
The campaign closes fs.c: ialloc, iunlockput, ireclaim, fsinit, stati,
namecmp, dirlookup, dirlink, namex (skipelem INLINED into it — no
symbol), namei, nameiparent. Prerequisite state: the share vocabulary
(design/fs-icache.md §14.6–§14.10) — reader contracts are stated over
`inode_shr`, which is the whole reason C8 preceded this.

## Decode: STAGED (scratch gen4), lands with the first campaign commit

11 manifest rows (namex at width 3 — 318 bytes, skipelem inlined);
sibling Code files byte-identical; all 32 shards pure additions. The
usual near-full rebuild lands with it.

## The design layers (the §-pass, in progress)

1. **`DirentEnc.v`** — LANDED (N1). The fourth byte vocabulary, mirroring
   DinodeEnc's law set (lengths, cons, per-record and per-byte lookup,
   insert-same/other, the `_t` total-lookup twins, zero/replicate, and
   the §12.3 injectivity family `dirent_bytes_inj`/`dirblk_bytes_inj`).
   Geometry VERIFIED off the decode, not fs.h: `&de = s0-96`,
   `&de.name = s0-94` ⇒ inum@0 (2 bytes, read `lhu`), name@2, stride 16
   (`li s3,16` feeds readi's `n` AND `off += 16`), DIRSIZ 14
   (`namecmp+0x08 li a2,14`), 64 per block. A FREE slot is
   `de.inum == 0` (`de_free`).
   THE NAME MODEL is `cut_nul` (list) / `bname n f` (naming function) —
   the prefix before the first NUL, capped at n. dirlink calls
   **strncpy** (`dirlink+0x78`), so a stored name IS NUL-padded
   (`name_pad`, `de_padded`) and canonical equality determines the bytes
   (`de_name_faithful`) — that is what makes a `name -> inum` view of a
   directory well defined. But namex's own buffer is NOT padded, so the
   bridge is stated without any padding hypothesis: `nc_zero_iff` says
   "namecmp returned 0" ⟺ `bname 14 f = bname 14 g`, over `nc_stop` /
   `nc_run` (SpecStrncmp's two `strncmp_res` arms transcribed, minus the
   returned word — SpecStrncmp is iris-heavy and cannot be imported by a
   pure leaf). The one step left to the namecmp proof: `mword_of_int
   (bv_unsigned (f k) - bv_unsigned (g k)) = 0 -> f k = g k`.
2. **The path grammar** — LANDED (N1) as `PathElems.v`: `skipelem`,
   `path_elems` (fuel + `path_elems_unfold`, the only law consumers
   use), `skipelem_decr` (the loop measure), the corner cases, and the
   `nameiparent_of` (all-but-last + last) split. Read off namex's
   INLINED loop: the element is `take 14` of the scan but the REST
   resumes after the FULL element (`skipelem_split` is the master law);
   the rest also has its leading separators skipped, because skipelem's
   TRAILING `while (*path=='/')` at namex+0xa4 runs before namex+0xc8's
   `nameiparent && *path == 0` test — so "no elements left" is literally
   "the rest is []" for a normalised rest (`path_elems_nil_norm`).
   Two things the WP proof must expect: namex+0xf8–0x102 re-tests
   `*path` for `'/'` and NUL and branches to a `len = 0` block that is
   DEAD (both tests were just decided at +0xe8/+0xf6), and the short
   branch writes `name[len] = 0` while the `len >= 14` branch writes no
   terminator at all — `bname_of_buf` / `skipelem_name_view` cover both
   with one canonical view.
3. **Directory-inode contracts** — dirlookup/dirlink read and write
   the directory's DATA blocks THROUGH readi/writei's proven contracts
   (xv6's own loops call readi/writei per 16-byte record with kernel
   destinations) — so the campaign stacks on the inode layer, not on
   bread. The directory's content as a pure `gmap name inum` view
   derived from the data function `data : nat -> list (bv 8)` the
   bundle carries — a DIRECTORY-typed refinement of inode_ok's data,
   minted by ilock's postcondition when di_type = T_DIR (a new pure
   layer, not a new resource).
4. **ialloc + the image-wf tie** — ialloc scans dinode blocks via
   bread (NOT through the icache) and claims a type-0 slot via
   dinode_at + wp_log_write_au (iupdate's AU seam, already landed);
   the pool's free shape (§13.3) is exactly what it consumes, and
   its output feeds iget. This is also where ipool_alloc's
   allocated-shape premise earns its discharge for the REAL image
   (the recorded image-wf effort) — scope stage-0 whether that lands
   here or stays a threaded premise.
5. **Locking discipline** — namex's loop does ilock(dp); dirlookup;
   iunlockput(dp) — iunlockput composes two proven contracts (32
   bytes, jal iunlock; jal iput — likely the campaign's cheapest
   proof). The share-vs-reference question at each step: namex HOLDS a
   reference to the current dir (from iget/namei's caller) and its
   dirlookup returns the CHILD's reference via iget. State stage-0:
   which of the 11 take shares, which references.

## Stages (per the established loop; each ends merged + gated)

- **N0** (coordinator): land the staged decode; finish this design
  pass (§-work above); stage-0 scope per function.
- **N1** (agent): DONE — `DirentEnc.v` + `PathElems.v` (both pure
  leaves, no `Admitted`, no new assumptions). See layers 1–2 above for
  what they provide and for the two decode findings that constrain N4.
- **N2**: stati (46B, trivial — inode_meta → stat struct copy),
  iunlockput (32B, two jals), namecmp (22B, a jal to strncmp).
  Warm-up proofs validating the layers.
- **N3**: dirlookup (172B: the readi-per-record scan; iget's scan-loop
  recipe + readi's contract) + dirlink (170B: the free-slot scan +
  writei append; the two-armed postcondition — found/appended).
- **N4**: namex (318B, width 3 — the campaign's boss: the inlined
  skipelem loop over the path grammar, ilock/dirlookup/iunlockput
  per element, the parent-vs-target split) + namei/nameiparent
  (26B wrappers).
- **N5**: ialloc (188B) + ireclaim (200B) + fsinit (112B) — the
  allocation/boot half; ireclaim is fsinit's single-threaded orphan
  sweep (the C7 notes flagged it as the pool's initial-contents
  authority).

After N5: fs.c is 24/24 and the campaign's exit gate is the shutdown
(user-standing instruction).
