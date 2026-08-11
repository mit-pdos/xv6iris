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

1. **`DirentEnc.v`** — the FOURTH byte vocabulary (after BlockWords'
   words, DinodeEnc's records, BitmapEnc's bits): `dirent := {de_inum :
   bv 16; de_name : 14 bytes NUL-padded}`, 16 bytes, 64 per block;
   `dirent_bytes`/`dirblk_bytes` mirroring diblk's laws (lookup,
   insert-same/other, length, and the §12.3-style injectivity the
   region taught us to provide up front). The NAME model: reuse
   ByteBuf's `bb_cstr`/`bb_nonul` vocabulary (strncmp/safestrcpy's
   layer) rather than inventing a second string model — namecmp IS
   strncmp at DIRSIZ and its proven contract should compose directly.
2. **The path grammar** — namex's loop needs a pure model of
   skipelem's decomposition (path → element list, the PrintkFmt
   precedent: a pure model of what the loop consumes is what makes the
   contract statable). Slashes, empty elements, DIRSIZ truncation,
   the trailing-name vs parent split (namei vs nameiparent).
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
- **N1** (agent): DirentEnc.v + the path grammar (pure layers, no
  instructions — IcacheBoot's precedent says budget ~100 lines of
  surprise-free grinding each, but the path grammar's corner cases
  deserve adversarial review).
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
