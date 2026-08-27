# fs-syscall-specs — the campaign worklist

STATUS: OPENED 2026-08-27 (user: rank 4's finding first, then get going),
after the durable-disk adequacy theorem became TRUE (`Himg` deleted,
lane H complete; that campaign's only open lane is F — receipts).
Design of record: [`../design/fs-syscall-specs.md`](../design/fs-syscall-specs.md)
(v2 + the 2026-08-25 impact note; the v3 refinement is lanes S0/A here).
Related: `durable-disk.md` (its lane D is handed HERE; its lane F gates
lane Y below), `namei-pinned-lookup.md` (paused; its port is lane P).

Working rules (inherited): all builds on the EC2 mirror; Opus for proof
lanes, Fable for design (user's split); R10 byte-stability — landed
contracts never move, new specs are parallel forms; merge to main at
each green gate, never push campaign branches (the user pushes).

## Input to the simplification campaign's rank 4 (consumer side)

Rank 4 asks: keep the `dview`/`fview` ghosts and the pinned-lookup
island for this project's port, or delete.  The island is TWO different
things, and the answer differs:

1. **The live substrate — KEEP for now, and let THIS campaign retire it
   if its carrier ruling makes it redundant.**  `DirViewG.v`'s
   `dview`/`fview` ghosts (threaded through the payloads at every
   mutation), `DirViewLend.v`, and the ghost-trace namex spec
   (`SpecNamexTr`/`ProofNamexTr`/`LinkNameiTr`).  The spec doc's §3
   path-resolution primitive IS the ghost trace, and §2's carrier
   (`nview`) is either dview-extended or a `γtop` reading — that choice
   was lane S0's question (§9 Q1 of the doc) and IS NOW RULED
   (2026-08-27, doc v3): the carrier is a reading of `γtop`'s
   `top_frag_q`, so the dview column retires HERE — lane A item (iii),
   hop seam first, column second.  Deleting the ghosts before the hop
   seam moves would still re-pay N-1; the sequencing stands.
2. **The seven off-build pinned files — DELETE-OK, with one statement
   salvaged.**  `NameiInitPinned.v`, `LinkNameiPinned.v`,
   `SpecKexecPinned.v`, `ProofKexecPinnedA/­.v`, `LinkKexecPinned.v` are
   era-0 image-content instances whose premises (`dv_pin` minted by
   `fs_cfg_alloc`) no longer exist — that lemma is deleted; the port
   re-derives the two pins from era-0 snapshot facts (lane P below), not
   from these proofs.  Git history and the notes keep the statements.
   `DirViewPin.v`'s generic pinned walk (client holds fragments along
   the path ⇒ namei returns THE inum) is the doc's §3 `path_at`
   corollary one level down: copy its STATEMENT into lane A's brief (or
   keep the one file off-build as the seed); the rest can go.

## The lanes

- [x] **S0 — the carrier ruling + doc v3.**  DONE 2026-08-27, on the
  user's ruling "we can change the design to match better the kernel
  specs": the carrier is a READING of `γtop`'s `top_frag_q` (no new
  map; agreement/split/mover-discipline all landed), `aview` quotients
  via `abs_of` INSIDE the carrier definition (kernel side never sees
  `anode`), `state av` is a reading of `fs_view`'s authority, and the
  batch bound left the carrier for persistent `dur_at` certificates
  (doc §5 principle 3 v3).  `dview` retires inside this campaign, hop
  seam first — see lane A.  Q4 answered earlier (epoch pointer); Q5
  stays option (a).  Residual: owner reads v3.
- [ ] **D — the durability readings (UNGATED; the first proof lane).**
  `mknod_durable` and siblings, as PER-NODE PERSISTENCE instances off
  what the durable campaign left: `FsCrash.fs_commit_receipt` (line
  2187), `FsDurSnap.P_dur_tie`/`P_dur_node_of_slot`/
  `snap_dir_entry_of_first`, `SystemAdequacy.fs_boot_pure`.  Definition
  of done: after the batch containing a mknod's transaction commits, the
  current snapshot's table at `inum` is the created node and the
  parent's entries contain `(name ↦ inum)` — stated once in the doc's §5
  vocabulary, proven by reading; unlink and write's siblings follow the
  same shape.  This is durable-disk lane D's content, subsumed.
- [ ] **A — the abstract state and carriers (S0 done; ready).**  Four
  pieces, all readings: (i) `abs_of : fs_node → anode` + the carrier
  `i ↦ₐ{q} a := ∃ n, top_frag_q _ q i n ∗ ⌜abs_of n = a⌝` + the
  `state av` accessor off `fs_view`; (ii) `path_at` off the ghost trace
  (the salvaged `DirViewPin` statement over the new carrier); (iii) THE
  DVIEW RETIREMENT: re-fire `nx_hop` off the payload's `top_frag`
  (`dv_lookup_found` restated over `dir_entries`), then take the
  `dv_*` column off the payloads — hop seam FIRST, column second (the
  reverse re-pays N-1); (iv) price the offset seam for the fd row (the
  one datum with no ghost — lives in `fcontent` behind `file_ref`).
- [ ] **W — the first increment's AU specs (after A).**  mknod →
  unlink → write, in that order (§9 Q6: spike-adjacent first, hardest
  in-memory arm second, per-chunk honesty third).  open/read/close/
  fstat/chdir after, mechanical.  NOTE (2026-08-27): the fd-state ghost
  landed upstream (`FdSlots.fd_frags` beside `ut_own`; `fdstate` =
  open-or-closed + `fdtype`, two-halves algebra, commits 28d707dc +
  3199a1b6; `FdInode` carries its INUM as of d1411776, riding on
  `file_ref`'s index) — the descriptor arms of these specs speak THAT
  carrier and can tie fd → inum → the §2 abstract node directly; the
  campaign does not mint its own fd ghost.
- [ ] **P — the /init pin port (after D; independent of S0).**  Era 0's
  exec-of-`/init` re-derived on the spec abstract state from era-0
  snapshot facts (era 0's snapshot IS the mkfs image: `fs_boot_pure` +
  `FsImgCheck.fsimg_init_path`/`fsimg_root_type`), replacing the
  disabled `dv_pin`/`fv_pin` route.  Done when the boot chain's
  commented pin consumers could be re-enabled against it (whether to
  re-enable is the owner's call).
- [ ] **Y — sys_sync (gated on durable lane F).**  The `flushed`
  receipt (persistent snapshot certificate copy, plan 4⁹.3) + the
  `wp_sys_sync` parallel form (R10), per doc §5 principle 2's derivation
  chain — items (ii) and (iii); item (i) is DONE (the commit concludes
  something real).

Sizing: D is spike-sized — the readings exist, the work is assembly and
statement.  S0 is one design session.  A and W are the campaign's bulk.
P is contained (two pins).  Y is small once F lands.
