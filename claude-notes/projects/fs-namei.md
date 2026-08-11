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
3. **Directory-inode contracts** — DESIGNED (coordinator, pre-N3).
   dirlookup/dirlink read and write the directory's DATA blocks THROUGH
   readi/writei's proven contracts (xv6's own loops call readi/writei
   per 16-byte record with kernel destinations) — the campaign stacks
   on the inode layer, not on bread.

   **The record view (pure, over `InodeInv.file_byte data`):**
   - `dir_inum data k : bv 16` — the k-th record's inum halfword,
     assembled little-endian from `file_byte data (16k)` and `(16k+1)`
     (DinodeEnc.half_bytes's inverse direction; state it so
     `dirent_bytes_inum` connects it to an encoded record).
   - `dir_name data k : nat -> bv 8 := fun j => file_byte data (16k+2+j)`
     — the name bytes as a FUNCTION (namecmp's g), canonicalised by
     `bname 14`.
   - `dir_live data k := dir_inum data k ≠ 0`; `dir_match data k s :=
     dir_live ∧ bname 14 (dir_name data k) = s`.
   - `dir_first data nrec s : option nat` — the LEAST k < nrec with
     `dir_match` (dirlookup returns the first hit; nothing proven
     forbids duplicate names, so first-match is the honest semantics).
     nrec = size/16.
   - **SCOPE RULING: no `gmap name inum` view this campaign.** namex
     only needs dir_first's two arms; the gmap refinement (which needs
     a no-duplicates directory invariant nobody has minted) belongs to
     the sysfile/end-to-end effort. Recorded as a future frontier.

   **dirlookup's contract (172B):** premises — `di_type dn = T_DIR`
   (panic "dirlookup not DIR" refuted by premise, same pattern as
   ilock's holder arms), **`16 | bv_unsigned (di_size dn)`** (the
   directory-size granularity invariant: under it every loop readi has
   off+16 ≤ size, so kernel-arm readi returns EXACTLY 16 and panic
   "dirlookup read" is dead — mkfs and dirlink both only ever grow
   directories by whole records), plus readi's own threading
   (bm_covers, size ≤ MAXFILE*BSIZE, log_geom/blkmap_wf) and iget's
   (pool shape / live panic arm, icache invariant, budget-free).
   Resources: the holder's locked-dir bundle (i_dev, i_inum,
   inode_meta, inode_map, inode_blocks — readi's verbatim), the
   caller's 14-byte name buffer (any dfrac, handed back), the de
   scratch is dirlookup's own stack, `poff` two-armed (null ⇒ emp,
   else a 4-byte cell). Postcondition arms:
   - FOUND: `dir_first data nrec s = Some k`, a0 = iget's nonzero
     return for `(dev, dir_inum data k)` with its `inode_ref` (iget's
     postcondition verbatim), poff (if non-null) holds 16k.
   - NOT FOUND: `dir_first data nrec s = None`, a0 = 0, everything
     returned unchanged.
   The dir bundle comes back untouched either way (readi modifies
   nothing; iget touches only icache state).

   **dirlink's contract (170B):** runs INSIDE a transaction (its
   writei can allocate via bmap → log_write), so it threads writei's
   log resources verbatim, plus dirlookup's premises and iput's
   (found-arm iputs the child). Postcondition arms:
   - FOUND (name present): a0 = -1, directory data UNCHANGED, the
     iget'd child reference already respent by iput (net zero icache
     resources — thread iput's budget interval).
   - APPENDED: a0 = 0, the record written at slot k0 = the first free
     slot (`dir_first`-style least k with ¬dir_live, else nrec), via
     writei's postcondition: data' agrees with data off [16k0,16k0+16)
     and holds `dirent_bytes (de_of_name inum s)` there — dirlink
     strncpy-pads, so the stored record IS `name_pad` (DirentEnc's
     `de_of_name`/`de_padded` are exactly this). If k0 = nrec, size
     grows to size+16 (writei's size-update arm) — premise
     `size + 16 ≤ MAXFILE*BSIZE` kills panic("dirlink") the same way
     granularity kills the read panic.
   Also needs the caller's name buffer wf: `length s ≤ 14`, nonul
   (namex's skipelem output satisfies both — `skipelem_elem_wf`).
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
   bytes, jal iunlock; jal iput). LANDED (N2), and it WAS the cheapest
   proof — but the composition is not free: iunlock returns a SHARE and
   iput spends a REFERENCE, so the caller must also hand over the SHORT
   PARENT it kept back when it carved ilock's share. See "N2's ledger"
   below. The share-vs-reference question at each step: namex HOLDS a
   reference to the current dir (from iget/namei's caller) and its
   dirlookup returns the CHILD's reference via iget. State stage-0:
   which of the 11 take shares, which references.

## Stages (per the established loop; each ends merged + gated)

- **N0** (coordinator): land the staged decode; finish this design
  pass (§-work above); stage-0 scope per function.
- **N1** (agent): DONE — `DirentEnc.v` + `PathElems.v` (both pure
  leaves, no `Admitted`, no new assumptions). See layers 1–2 above for
  what they provide and for the two decode findings that constrain N4.
- **N2**: DONE — stati, iunlockput and namecmp are all PROVEN, LINKED and
  sealed; `Print Assumptions` on each of the three linked modules gives the
  5 platform axioms + funext and nothing else. See "N2's ledger" below for
  the exact names N3/N4 consume.
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

## N2's ledger — what N3/N4 consume

Nine new files, no existing file touched: `Spec`/`Proof`/`Link` for each of
stati, namecmp, iunlockput, in that `_CoqProject` order.  Module types
`STATI` / `NAMECMP` / `IUNLOCKPUT`; functor arguments `StatiProof` (none),
`NamecmpProof (SC : STRNCMP)`, `IunlockputProof (IU : IUNLOCK) (IP : IPUT)`;
linked modules `Stati` / `Namecmp` / `Iunlockput`.

**`SpecNamecmp.wp_namecmp_sconf_body mm f g K dq1 dq2 b p`** — the resource
half is SpecStrncmp's verbatim at n = 14 (two `[∗ list] j ∈ seq 0 14,
pa_add (mm !!! a0/a1) j ↦ₘ{dq} f/g j`, handed back), and the result half is
the ONE fact dirlookup wants:

    ⌜mr !!! a0 = (mword_of_int 0 : mword 64) <-> bname 14 f = bname 14 g⌝

`K_namecmp = 4`.  No `cpu_own`, no `procs_inv`, no parking premise — namecmp
neither sleeps nor locks.  N3 pairs the right-hand side with
`DirentEnc.namecmp_bridge` to read it as `bname 14 f = de_name_str d`.
The proof file also exports two pure lemmas N3 may want directly:
`ProofNamecmp.nc_byte_of_zero` (the owed arithmetic step: a 64-bit word
holding the difference of two BYTES is zero only when the bytes are equal)
and `ProofNamecmp.nc_res_iff` (`strncmp_res f g 14 res -> (res = 0 <->
bname 14 f = bname 14 g)`).  N1's prediction was exact: that one step was
the entire gap, and `SpecStrncmp.strncmp_stop` turned out to be
`DirentEnc.nc_stop` verbatim once `bb_nonul` and `NUL` are unfolded
(`nc_stop_of_strncmp` is `exact (fun H => H)`).

**`SpecStati.wp_stati_sconf_body mm ip st dev inum dn dev0 ino0 ty0 nl0 sz0
K dqd dqn b p`** — `K_stati = 2`, no `cpu_own`, no parking premise, and
`ip` is an ARBITRARY pointer (stati does no slot arithmetic and has no panic
to refute).  It takes `i_dev ip ↦₄{dqd} dev`, `i_inum ip ↦₄{dqn} inum` and
`InodeInv.inode_meta ip dn` — i.e. exactly what a holder destructs out of
`IcacheEscrow.ic_loaded`, at SpecIlock's own existential `dn` — plus the
caller's buffer, and hands all four back.

  **struct stat's geometry is NEW VOCABULARY this file introduces**, read
  off stati's own five stores rather than off `stat.h`:
  `SpecStati.st_dev`@0, `st_ino`@4, `st_type`@8, `st_nlink`@10,
  `st_size`@16, bundled as

      SpecStati.stat_at st dev ino ty nl sz
        = st_dev ↦₄ dev ∗ st_ino ↦₄ ino ∗ st_type ↦₂ ty
          ∗ st_nlink ↦₂ nl ∗ st_size ↦₈ sz

  BYTES 12..15 ARE DELIBERATELY NOT IN THE BUNDLE — they are the alignment
  hole before the 8-byte size and stati never writes them, so a caller that
  has to `copyout` the whole 24-byte struct owns them separately.  That is
  the thing to know before writing `filestat`/`sys_fstat`.

  The postcondition is `stat_at st dev inum (di_type dn) (di_nlink dn)
  (zero_extend' 64 (di_size dn))`.  ONLY `size` carries an extension: four
  of the five pairs load and store at the same width, so the load's
  extension is undone by the store's truncation, but `lwu a5,76(a0)` feeds
  an 8-byte `sd`, so `st->size` is the ZERO-extension of `ip->size`.  N1's
  is_unsigned warning was worth having — the flag is `false` (lh/lw) on the
  first four loads and `true` (lwu) only on the fifth, and getting it
  backwards there would have produced a false contract.  `ProofStati` proves
  one reusable lemma on the way: `trunc16_sext64 : trunc16 (sign_extend' 64
  w) = w`, the width-2 twin of `RiscvExtras.trunc32_sext64` (it belongs
  beside `WpSmodeHalf.trunc16`; left in the proof file so nothing below it
  needs rebuilding).

**`SpecIunlockput.wp_iunlockput_sconf_body`** — `K_iunlockput = 64`
(= `K_iput + 4`).  Every premise and every resource is one of the two
callees'; the budget clause is iput's verbatim (`iput_units <= n` in, the
spend-at-most interval out), and so is the whole postcondition: one
`iref_slot`, `used' ⊆ used`, and NOTHING inode-shaped.

  **THE SEAM, and the one thing a caller must supply beyond the two
  callees' unions.**  SpecIunlock v3 hands back a SHARE (`inode_shr k s dev
  inum`); SpecIput spends a canonical REFERENCE (`inode_ref k q dev inum`).
  They do not compose on their own — that is §14.6(1) working as designed.
  What closes the gap is the parent the caller retained when it carved the
  share off for ilock, so the precondition carries, beside iunlock's
  `ic_deposit cn k (DepShr s dev inum)` bundle:

      IcacheRef.inode_ref_short k (qi + s)%Qp qi dev inum

  and the proof fires `IcacheRef.inode_ref_gather` at the instruction
  between the two `jal`s, producing `inode_ref k (qi + s) dev inum` for
  iput.  **N4's namex must therefore carve rather than lend**: before
  `ilock(dp)` it splits its reference with `inode_ref_carve` /
  `inode_ref_shed`, passes the share to ilock, keeps the short parent, and
  hands BOTH the deposit descriptor and the short parent to iunlockput.
  After the call it holds no inode resource for `dp` at all.  (`qi` and `s`
  are free parameters, so `inode_ref_shed`'s `q/2 + q/2` shape instantiates
  it with no arithmetic.)

  No new lemma was needed anywhere in the icache layer for this — the seam
  is exactly the carve/gather pair that already existed.

### Build evidence (EC2 mirror, git-synced at 2cee9490)

Each of the nine compiled standalone, exit 0, against the mirror's full
`.vo` tree.  `tools/lemma_diff.py --ref HEAD` reports no `GONE` and no
`ADMITTED`; its three `NEWAXIOM` lines are the three `Module Type` seal
`Parameter`s (`wp_stati_sconf`, `wp_namecmp_sconf`,
`wp_iunlockput_sconf`), which every `Spec<F>.v` in the tree has and which
the matching `Proof<F>.v` discharges — the tool flags a `Parameter`
regardless of whether it sits in a `Module Type`.
