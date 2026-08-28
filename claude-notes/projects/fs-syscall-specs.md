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
- [x] **D — the durability readings.**  DONE 2026-08-28 (Opus lane,
  `iris/FsDurSyscall.v`, 654 lines, zero axioms): `mknod_durable` (+
  its §7 non-vacuity witness), `unlink_durable`/`unlink_durable_freed`,
  `write_durable`(`_block`), over pure persistent certificates
  `snap_holds D` / `dur_sb D sb` / `dur_node D i n` and the determinism
  theorem `snap_node_det` (snap_ok pins the state per-inum against `D`
  — discharging durable-fs-plan §8's asserted claim).  Producers:
  `snap_holds_of_boot_pure` (reaches every reachable state) and
  `fs_commit_snap_holds` off `fs_commit_receipt`.
  AS-LANDED NOTES: two of the brief's three FsDurSnap lemma names had
  been deleted at S2 (plan told the spike to restate; it did — the
  certificates are restated from `snap_ok` directly).  Certificates are
  batch-free until durable lane F lands `flushed`; then `dur_at b i a`
  = `flushed b ∗ ⌜dur_node D_b i n⌝` with nothing here moving.
  GAPS RECORDED FOR LATER LANES: (1) **`FsCollectAll.fs_collect_mint`
  discards `S = col_state sb sbb I used`** — the one tie from a
  client's `top_frag` to the committed snapshot; lane W's AU specs will
  want it, and the fix is a one-conjunct strengthening of a landed
  contract (R10 — OWNER'S CALL, queued as decision item below).
  (2) `fss_used` is NOT determined by `D` above bit `BSIZE*8`; free-
  block durability must be stated within `[0, sb_size)`.  (3)
  `sk_regdom` only covers `[0, 16*(ninodes/16+1))`, so determinism is
  per-inum; no whole-map equality exists.  (4) mirror one-file compile
  line: `coqc -R . xv6iris -R ../model-xv6iris Riscv -R ../kernel-rocq
  Kernel -R ../user-rocq User -w -notation-overridden File.v` (the
  `-arg` rows of _CoqProject are coq_makefile flags, not coqc's).
- [ ] **DECISION (owner) — the γtop↔snapshot tie for lane W.**
  ORIGINAL FORM MOOT (2026-08-28): EV-Y retired `fs_collect_mint` and
  the destructive collection; the commit now COLLECTS
  `fs_state (fs_gamma_L γfs) (DfracOwn (3/4)) S` reversibly out of the
  invariants at quiescence and hands it to `FsDurXfer.fs_state_xfer_tok`
  — the S it transports is assembled FROM the live legs, so the tie
  lane W wants may now be READABLE at the collection boundary rather
  than needing any contract strengthened.  Re-derive the ask when lane
  W starts (probe: can a spec-layer lemma at the quiescent point relate
  the transported S's `fss_inodes` to the ftop authority's map?); only
  if not does an R10 question come back to the owner.
  ALSO NOTED: upstream ruled the simplification order (1d8c8901) —
  **rank 4 is PARKED and the pinned-/init files stay untouched**, which
  is consistent with v3's plan (this campaign retires dview itself,
  hop seam first).
- [~] **A — the abstract state and carriers.**  Items (i)+(ii) DONE
  2026-08-28 (Opus lane, `iris/FsAbs.v`, 699 lines, zero axioms):
  `absnode`/`anode`/`abs_of` off the landed readings; `nview(_dq)` =
  `top_frag_q`'s `abs_of` reading with agreement / split (⊣⊢, both
  directions) / fractional / timeless; `astate Γ av` with
  `fs_view_astate : fs_view Γ ⊣⊢ ∃ av, astate Γ av` (Q3 as an
  EQUIVALENCE, no new invariant) and `astate_nview` (held share reads
  the authority's row); `apath_at` (NAMED so — `FsTree.path_at` is in
  the cone; `apath_at_tree` proves they are one function, inheriting
  FsTree §7's algebra); `arun` (the visited-inum walk, total + converse
  forms); the DirViewPin statement restated as `ax_hop`/`ax_hops_from`
  (= `nx_hop`/`nx_hops_from` with the lent fragment ABSTRACTED —
  machine-checked `reflexivity` receipts quoted in the header) and the
  pinned-walk package `apn_walk`, with NO divergence arm (a
  `top_frag_q` share is not a cancellable lend — the v3 stability
  story cashed out).
  AS-LANDED GOTCHAS: `aview` must stay a NOTATION (a Definition splits
  the `lookup` elaboration and `abs_tree_ent` stops closing); no
  `T_DEVICE_z : Z` exists (ADev is the else arm; sharpen `abs_of_dev`
  if one lands); `apn_pins` is Typeclasses Opaque — consumers
  `Require Import FsAbs` directly.
  REMAINING: (iii) THE DVIEW RETIREMENT — the one gate on
  instantiating `apn_walk` against `wp_namei_tr`.  Suggested seam
  (from the lane): `dv_half d dq ents ∗ top_frag_q Γ dq' d n ⊢
  ⌜ents = dir_entries n⌝`, proved ONCE where both live in the payload
  (escrow/region); then `lend_agrees Γ dv_half` is immediate and
  `apn_hop`/`apn_walk` apply UNCHANGED at `F := dv_half`.  Hop seam
  first, `dv_*` column off the payloads second.  (iv) the offset seam
  for the fd row; plus the §2 leftovers (`root_is` — `FsImg.ROOTINO`
  is reachable from FsAbs — and the fd/cwd carrier readings).
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
