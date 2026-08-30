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
  REMAINING: (iii) THE DVIEW RETIREMENT — DONE 2026-08-30, see the
  record at the end of this item; (iv) the offset seam for the fd row;
  plus the §2 leftovers.
  [history of (iii), kept because it is why the era walk exists:] the one
  gate on instantiating `apn_walk` against `wp_namei_tr`.  Suggested seam
  (from the lane): `dv_half d dq ents ∗ top_frag_q Γ dq' d n ⊢
  ⌜ents = dir_entries n⌝`, proved ONCE where both live in the payload
  (escrow/region); then `lend_agrees Γ dv_half` is immediate and
  `apn_hop`/`apn_walk` apply UNCHANGED at `F := dv_half`.  Hop seam
  first, `dv_*` column off the payloads second.  (iv) the offset seam
  for the fd row; plus the §2 leftovers (`root_is` — `FsImg.ROOTINO`
  is reachable from FsAbs — and the fd/cwd carrier readings).
  ITEM (iii) ATTEMPTED 2026-08-28 (Opus lane, `iris/FsAbsSeam.v`, zero
  axioms, EC2-green) AND IT DOES NOT CLOSE AS SCHEDULED.  Three findings,
  all machine-checked:
  1. **The tie is real, pure, and already landed.**  Every payload arm
     (`ic_loaded` via `ic_loaded_flat_body`, `ic_rd_arm`, `ipool_alloc`)
     carries `dv_ride z (dv_of dn data)` and `top_frag … (era_node dn bm
     data)` side by side, and `FsStateEra.dir_entries_era_node` already
     says the two readings are ONE function.  `FsAbsSeam.dv_of_dir_entries`
     / `abs_of_era_dir` / `dv_top_seam` are the seam, at ANY pair of shares.
  2. **`lend_agrees` is the wrong law.**  It asks the lend to prove the
     pinned node is a DIRECTORY, which no arm can: `dv_half` rides a file
     too.  `FsAbs.lend_reads` (directory-ness supplied by `arun` instead)
     is what a payload discharges, and FsAbs §4a' re-proves the package at
     it (`apn_hop_rd`/`apn_hops_rd`/`apn_walk_rd`, statements of the
     landed trio untouched).
  3. **THE ACTUAL BLOCKER: no client can hold `nview` while the walk
     runs.**  `ic_loaded` and `ipool_alloc` hold the era leg at
     `DfracOwn 1`, i.e. `top_frag` WHOLE, so `apn_pin` against a live inum
     is REFUTED (`ic_loaded_nview_excl`, `ipool_alloc_nview_excl`,
     `apn_pin_loaded_excl`).  The only producer of a client share in the
     tree is a read-locking `ilock`'s quarter (`inode_rd_era_nview`), and
     namex's `ilock` takes the WRITE arm — so at the fire instant not even
     the read arm's 3/4 residue is in the escrow to open.  `nx_hop` (R10-
     frozen) passes only `dv_half` through the caller's fupd, so a client
     hop learns nothing about γtop.  Where a share IS legitimately
     outstanding the whole thing composes: `dv_lend_arm_reads` discharges
     `lend_reads` for a concrete lend and `apn_walk_arm` is the package
     fired at it.
  WHAT (iii) NEEDS NEXT — an OWNER decision, because both routes are
  payload-side: (a) `ic_loaded`/`ipool_alloc` carry the leg at 3/4 with a
  client quarter outstanding — but a share blocks every `ireg_top_retag`,
  so that lend must be CANCELLABLE, which is the `DirViewLend` machinery
  the column was to retire and the divergence arm v3 ruled out; or (b) a
  second walk that lends the era fragment beside the contents (a new
  Spec/Proof/Link triple over ProofNamexTr's 4990 lines).  Until one is
  taken, the `dv_*` column CANNOT retire and the pinned walk over `nview`
  is instantiable only against a read-locked directory.
  **RULED (user, 2026-08-28): OPTION (b).**  Cross-syscall stability is
  the tree layer's exclusivity fact, not an in-logic cancellable share;
  the campaign builds the era-fragment walk — new parallel
  Spec/Proof/Link beside the frozen trio, per-hop lend = the era leg
  (`lend_reads` is the law it discharges; `apn_walk_rd` applies
  unchanged).  The `dv_*` column retires when the new walk replaces the
  dv-firing one as the consumed form.  This is now lane A-iii's work
  item, Opus-sized (the proof follows ProofNamexTr's structure).
  **(b) LANDED, NAMEI SIDE, 2026-08-28** (Opus lane; ten new files, all
  EC2-green, zero `Admitted`, and the era cone's `Print Assumptions` is
  BYTE-IDENTICAL to `LinkNameiTr`'s — `resv_matches`, `resv_is_valid`,
  funext).  Files and what each seals:
  - `FsAbsPins.v` — the PIN-RETURNING package (owner ruling, relayed
    mid-lane): `apr_pins` is the client's WHOLE bundle carried through
    every hop (`big_sepL_lookup_acc`: read the k-th pin, put it straight
    back) instead of `apn_pins`'s shrinking `drop k`.  `apr_P_final`
    returns the shares beside the answer; `apr_P_pins` returns them at
    any death index.  `apr_pins_is_apn_pins` is a `reflexivity` receipt
    that it IS the landed accumulator at hop 0.  A NEW LEAF rather than
    an append to `FsAbs.v` for one mechanical reason: the mirror forbids
    touching a tracked file.  Fuse the two when `FsAbs.v` is next edited.
  - `FsAbsEra.v` — THE LEND.  `elend Γ d dq ents := ∃ n, top_frag_q Γ dq
    d n ∗ ⌜fn_is_dir n = true ∧ dir_entries n = ents⌝`.  Node
    existential (`ax_hop`'s `F` signature is frozen), but the fire SPLITS
    the walk's element (lend ½, keep ½) so agreement pins the returned
    node — that is why the fire does not lend `DfracOwn 1`.
    Directory-ness IS carried (the walk has already run its
    `ip->type == T_DIR` test), so this lend discharges the STRONG law
    `lend_agrees`, not just `lend_reads`.  `elend_astate` is what it is
    all for: read the parent's row off the AUTHORITY at the hop instant,
    no client share needed.  Also: `ex_hop`/`ex_hops_from` (= `ax_hop`
    /`ax_hops_from` at `elend`, by `reflexivity`), the two fire lemmas,
    `apn_walk_era` and `apr_walk_era`.
  - `SpecNamexEra.v` / `ProofNamexEra.v` / `LinkNamexEra.v` and
    `SpecNameiEra.v` / `ProofNameiEra.v` / `LinkNameiEra.v` — the
    parallel walk.  `ProofNamexEra` is `ProofNamexTr` with 300 diff lines
    out of 4990, ~130 of them header: split `Hfview` into `Hfv Htop` once
    before the `found` case split, fire off `Htop` instead of `Hdview`,
    re-frame `Hfv Htop`, and read `Htyd` as `Htydz : bv_unsigned (di_type
    dnl) = T_DIR_z`.  `Hdview` is never touched.  1m57s to compile, so no
    split was needed.  TRANSITIONAL BY DESIGN — the retirement step
    deletes the dv-firing original once consumers move.
  - `FsAbsEraMknod.v` — lane W's two fire points, DISCHARGED IN ADVANCE:
    `era_dlookup_fire` (its prover's `dlookup_commit` consumed at an era
    hop, lend and state both returned) and `era_acre_fire` (`acre_commit`
    phase 1, with `cre_pre`'s ROW conjunct coming from the lend and the
    other two from the caller), plus `mknod_walk_pre_era` /
    `mknod_walk_dead_era`, the era twins of lane W's walk predicates.
  AS-LANDED FINDINGS:
  1. **The pinned walk is still VACUOUS for a live inum, and a second
     walk was never going to change that.**  The walk's custody is the
     WHOLE element (namex's `ilock` takes the write arm), so
     `FsAbsSeam`'s finding 3 stands: a client holding any `nview` share
     of a directory on the chain is refuted.  `apn_walk_era` /
     `apr_walk_era` are theorems and compose, but the NON-VACUOUS
     consumption route is `elend_astate` — the hop reads the authority's
     row, which needs no client share.  A non-vacuous pin waits for the
     tree layer's exclusivity fact, as the ruling itself says.
  2. **`lend_agrees` turned out to be the right law after all** — for
     THIS lend.  `FsAbsSeam` had to weaken to `lend_reads` because
     `dv_half` rides a file too; the era fragment carries the type, so
     `FsAbs` section 4 and section 4a' both instantiate.
  **THE NAMEIPARENT WALK LANDED, 2026-08-28** (Opus lane; eight new files,
  all EC2-green, zero `Admitted`, and `Print Assumptions` on the whole cone
  is BYTE-IDENTICAL to `LinkNamexEra`'s — `resv_matches`, `resv_is_valid`,
  funext).  Files and what each seals:
  - `FsAbsNpar.v` — THE PARENT-PREFIX VOCABULARY.  `np_elems pl :=
    removelast (path_elems pl)`, which is `SpecSysMknodAU.mknod_parent_elems`
    definitionally; `ep_hop`/`ep_hops_from` = `FsAbs.ax_hop`/`ax_hops_from`
    at `FsAbsEra.elend` over that shorter list, by `reflexivity`; the peel
    `ep_hops_cons`; and `np_dead`, the death arm.  A leaf, not an append to
    `FsAbsEra.v`, for the mirror's reason (it forbids touching a tracked
    file) — fuse when `FsAbsEra.v` is next edited.
  - `SpecNparEra.v` / `ProofNparEra.v` / `LinkNparEra.v` — namex at the
    nameiparent side, `a1 <> 0`, absolute paths.  Plus
    `SpecNparWrapEra.v` / `ProofNparWrapEra.v` / `LinkNparWrapEra.v` —
    nameiparent's own contract over it, so a create-side caller never
    reaches past the wrapper.
  - `FsAbsNparMknod.v` — THE ACCEPTANCE TEST, discharged:
    `np_pre_of_mknod` (lane W's `mknod_walk_pre_era` one-shot fired at the
    fetched path and at `ROOTINO`, supplying the contract's two trace
    premises) and `np_dead_to_mknod`.
  AS-LANDED FINDINGS:
  1. **The trace premise HAD to be the parent prefix, not the full family
     with the last hop unfired.**  The earlier sketch (success arm =
     `P (L−1) iL` beside an UNFIRED last hop over `path_elems pl`) is
     UNSUPPLIABLE: producing that extra hop is a real fupd obligation and
     lane W's caller has no directory to discharge it against.  Over
     `removelast (path_elems pl)` the discharge is `reflexivity`, because
     that list IS `mknod_parent_elems`.
  2. **The frozen `⌜k < L⌝` death shape cannot express two REACHABLE
     nameiparent deaths**, and `np_dead` splits the bound accordingly.
     LEFT (`k <= length ps`): namex runs the type test (+0x54) and the
     nlink guard (+0x7a) at EVERY level including the PARENT's own, and
     "nameiparent of /" (+0x140's iput) is the same shape at `k = 0` with
     an empty family.  RIGHT (`k < length ps`): a dirlookup miss can only
     happen strictly inside the prefix, because dirlookup is reached only
     after the walk has decided the element is not the last one.
  3. **`mknod_walk_dead_era` does NOT cover the walk's failures**, and
     `np_dead_to_mknod` is honest about it: at `k = length ps` the walk
     hands back `P (length ps) d`, which is `mknod_post_fail`'s THIRD fold
     arm (`∃ d, P Lp d ∗ acre_commit ∗ (… ∨ dlookup_commit)`) and not
     `mknod_walk_dead_era`.  mknod's post is dischargeable as it stands;
     the predicate alone is not the whole story.
  4. **The `destruct npar` splits were PINNED, not eliminated.**  Deriving
     from `ProofNamex.v` (not from `ProofNamexEra`, per the sizing below)
     and opening with `pose (npar := true); assert (Hnpe : npar = true);
     clearbody npar` keeps all three case splits and their bullets exactly
     as landed; each namei branch closes with `discriminate Hnpe`.  Total
     new proof content: three nameiparent facts (`Hklep`, `Hkltp`/`Hdropp`,
     and the `es0`-nonempty invariant conjunct) and the two exits' trace
     rows.  133 s to compile, so no split was needed.
  5. **+0x140 needed a NEW INVARIANT CONJUNCT.**  On the namei side that
     exit is the success return; here it is "nameiparent of /", and the
     failure arm is indexed by the parent prefix — so the proof must know
     `es0 = []` there.  Carried as a second conjunct INSIDE the existing
     `⌜path_elems pl = es0 ++ …⌝` premise ("a level that consumed an
     element leaves another one behind"), so no call site's `[%]` count and
     no bullet list moved.
  6. **`lia` fails inside this file's proofmode context on a goal with NAT
     SUBTRACTION** — measured, on `n <= n + S m - 1`, "Cannot find
     witness", while the same goal closes instantly at the top level.  This
     is the reason `ProofNamex` has its `nx_wi_*` family; the two index
     bounds are hoisted the same way (`np_removelast_len_ge` / `_gt`).
  7. **Understating a `Context` binder list is still a 255 GB memory
     bomb** (durable-notes' rule, hit once here on `SpecNparEra`'s
     `inode_held_ty_at` section: 420 s and an OOM kill, against 3 s with
     `SpecNameiTr.NameiTrDefs`'s list).
  **THE RELATIVE START: DONE 2026-08-28** (Opus lane, two commits, both
  green on the mirror with the whole tree rebuilt, zero admits).  New leaf
  `iris/FsAbsStart.v`: `ex_start` / `ep_start`, the trace DEFERRED IN THE
  START INUM —
  `∀ r, ⌜pl !! 0 = Some SLASH -> r = ROOTINO⌝ ={⊤}=∗ P 0 r ∗ hops 0`,
  over the full family and over the parent prefix — plus the two head
  lemmas (`bview_head_slash`, `..._intro`) and the receipts
  `ex_start_of_pair` / `ep_start_of_pair` (the landed absolute pair BUILDS
  the deferred form, so nothing weakened).  All four era contracts and
  `SpecCreateAU` drop `pfun 0 = SLASH` and trade their two trace premises
  for that one.  AS-LANDED FINDINGS:
  1. **Q-c was not a gap in the cwd's reading.**  The blocker on record
     was that no landed predicate exposes `p->cwd`'s inum.  The CALLER
     never needs it: idup's postcondition hands the WALK a package whose
     own existential witness is the slot's inum, so the proof opens it
     (into `SpecNameiTr.inode_held_at`, the era loop invariant's own
     currency) and fires the caller's one shot there.  No `cwd_ref_at`
     was written, none is needed, and `ProcInv.v` was not touched.
  2. **Extending the era proofs in place beat re-deriving from
     `ProofNamex`** and the reason is structural: the myproc/idup arm is
     npar-agnostic (it sits before the `a1` test), so it splices into
     both era proofs unchanged, while re-deriving would have meant redoing
     the era adaptation (the fire point) and the npar one (parent-prefix
     index arithmetic).  288 lines spliced per proof; exactly TWO changes
     at the join (build the starting reference at its inum; fire the
     deferred trace, at ROOTINO on the absolute arm and at idup's inum on
     the relative one, where the tie is refuted by `bview_head_slash`
     rather than used).  The absolute arms are otherwise line for line
     what they were.  Compile: `ProofNamexEra` 177 s, `ProofNparEra`
     149 s, both first try.
  3. **The fire is `iApply fupd_wp; iMod …; iModIntro`** at the
     instruction boundary before the loop entry — the same idiom the hop
     fire uses 2000 lines up, so no new proofmode machinery.
  4. **The consumer side needed no invention**: `ep_start γfs P Pmiss pl`
     at a FIXED `pl` IS `FsAbsEraMknod.mknod_walk_pre_era` at that `pl`
     (same quantifier, same tie, same family), so
     `FsAbsNparMknod.np_start_of_mknod` is one `iMod` and
     `np_rootino_agree`.  The one-shot now travels DOWN unfired instead of
     being fired at ROOTINO in the syscall.
  **ITEM (iii) IS DONE — THE DVIEW RETIREMENT LANDED 2026-08-30** (Opus
  lane, three staged green commits, whole tree green after each, zero
  `Admitted`).  The `dview`/`fview` ghosts, their lend, their camera and
  their two gnames are OUT OF THE TREE; `git grep` for the column's names
  returns prose and tombstones only (plus the unrelated `LogDefs.dv_of_D`).
  Stages, in the order that keeps each one green:
  1. **The dv-FIRING STATEMENTS leave the build first.**  `SpecNamexTr`,
     `ProofNamexTr`, `ProofNameiTr`, `LinkNamexTr`, `LinkNameiTr` are
     off-build with their source intact and a `_CoqProject` tombstone (the
     pinned-files precedent; R10 — not one statement edited).  MEASURED, not
     assumed: their `.vo`s were deleted and a full `make` rebuilt NOTHING
     and stayed green.
     TWO FILES COULD NOT FOLLOW THE GHOST OUT and are trimmed in place with
     tombstones, because the honest reverse-dependency closure says
     off-building them takes 94 files including `SystemAdequacy`:
     `SpecNameiTr` (its `inode_held_at` is the ERA cone's own vocabulary —
     `SpecNameiEra`/`SpecNamexEra`/`SpecNparEra`/`SpecNparWrapEra` state
     their pins in it, and `NameiTrDefs`'s binder list is quoted by half the
     cone) keeps that and loses `nx_hop`/`nx_hops_from`/`wp_namei_tr_body`/
     `NAMEI_TR`/the canonical cursor; `SpecSysMknodAU` (this campaign's own
     file, twenty-five consumers of its §1–2a vocabulary) loses everything
     stated over `ax_hops_from dv_half` — `mknod_walk_pre`, `_dead`, the AU
     bundle, the three arm predicates, the frame, both bodies and
     `SYSMKNOD_AU`, none of which had an on-build consumer (the sealed form
     is `SpecSysMknodAUEra`'s `SYSMKNOD_AU_ERA`).
  2. **The column comes off the payloads**, and the movers with it.  A
     re-pack's dv step was always SUBSUMED by the `ireg_top_retag` beside it
     (the retag moves the fragment; the fragment's `dir_entries` /
     `fn_file_bytes` ARE what the two ghosts read off the same record and
     bytes), so `dv_set_rt`/`fv_set_rt`/`dvw_set_rt` and the size-preserving
     casts are deleted at ~30 call sites with every conclusion standing.
     37 files, −1085 lines net.  `FsAbsSeam` keeps its one surviving result
     as `dir_entries_era_ok`; the kexec header oracle is handed the ERA LEG
     alone (it was always the half that answered the pinned verdict).
  3. **The homes, the camera and the gnames.**  `DirViewG.v` and
     `DirViewLend.v` DELETED; `dviewUR`/`fviewUR`, `icache_dviewG`/
     `icache_fviewG` and their two `GFunctor` rows out of `Xv6Cameras`;
     `icfg_dview`/`icfg_fview` out of `MkIcfg` (two gnames shorter), with
     `icfg_alloc`'s two map arguments, their validity premises, their
     `own_alloc`s and their output conjuncts, and the two boot maps and
     `_valid` lemmas in `IcacheRef`.  Exactly upstream's rank-6 shape
     (52d2e407c, "xv6Sigma loses a functor"): the audited theorem now holds
     at a SMALLER functor list and `SystemAdequacy.v` / `SystemAssumptions.v`
     are byte-identical.
  AS-LANDED FINDINGS:
  1. **An over-long `iDestruct` pattern SPLITS a fractional resource instead
     of failing.**  Deleting two conjuncts from `ireg_registry` /
     `ic_loaded` left `EscrowDeposit` and four accessor lemmas with one name
     too many, and iris quietly cut `ghost_map_auth γ 1` (and `top_frag`)
     into halves — the error then surfaces one tactic LATER, as
     "cannot instantiate … with (… {#1/2} …)".  Read such a message as
     "your pattern is one name too long", not as a resource that went
     missing.
  2. **The last payload name was load-bearing prose.**  `ic_loaded`'s final
     conjunct bound `fv_ride ∗ top_frag` as ONE hypothesis at ~40 sites (the
     2b-inode-3 flip's whole dividend); with the ride gone it binds the
     fragment alone, so the sweep is a RENAME (`Hfview` → `Htopl`/`Htop`)
     and not a re-plumbing.
  3. **Nothing on the build ever READ the column** except the frozen Tr
     fire — verified by grepping every consumer of `dv_agree`/`dv_ride_excl`/
     the lend kit before touching a payload.  That is what made the sweep
     mechanical: every other site was a re-pack.
- [~] **W — the first increment's AU specs.**  mknod STATEMENT DONE
  2026-08-28 (Fable lane, `iris/SpecSysMknodAU.v`, 856 lines, green,
  zero admits — a statement file; the proof is a later Opus lane):
  `delta_create` (type-parameterized, `acre_bump` fuses mkdir's
  parent bump) with its row algebra and the `create_made` bridge
  `abs_of_create_dev`; `acre_commit` (TWO-PHASE, shaped for
  `ftop_astate_acc`: lend pre-state, then lend the delta applied, one
  ftopN critical section) and `dlookup_commit` (read-only sibling,
  reusable by unlink/open); trace via `ax_hop dv_half` over
  `mknod_parent_elems`; arms replace `⌜sys_mknod_ret⌝` in a frame
  copying SpecSysMknod's premises verbatim (R10 parallel form).
  DELIBERATE DEVIATIONS from doc §4 (recorded in the header):
  `∃ i ∉ dom av` UNSTATABLE over the landed astate (the authority rows
  the whole region) — replaced by the minted-orphan observation; the
  path is EXISTENTIAL (kernel contracts say nothing about user bytes);
  the stable corollary pins the CHAIN, never the parent (a held parent
  share would make the success retag impossible), and is partially
  vacuous until the (b) walk lands.
  PROVER OWES: the two fire points (dirlookup via `ftop_astate_ro`,
  dirlink's two phases around the parent-row `ghost_map_update` +
  `inode_local` give-back); the written-record `dir_entries` bridge; a
  nameiparent-side trace walk (NONE LANDED — fold into the (b) walk);
  the halfword `major` tie.  OWNER QUESTIONS (header): two-instant
  freshness (observe the mint) at the cost of a rollback-honest FAIL
  arm?; mask floor `∅` ok?; pin-returning refinement scheduled with
  the tree layer or waits for a cross-syscall pin producer?
  Gotchas: `FsImg` must be `Require`d not `Import`ed at syscall
  altitude; stdpp `last` = `list_basics.last` in this import mix.
  **THE ret-0 ESCAPE IS RETIRED 2026-08-28** (Opus lane, same session as
  the relative start above, strengthened IN PLACE — statement and seal in
  one commit, as those two files are the campaign's own with no external
  consumers).  `SpecCreateAU` now takes `FsAbsStart.ep_start` and has no
  absolute-path premise, so `ProofSysMknodAU` calls ONE create contract
  for every fetched string: the `destruct` on the first byte and the
  300-line landed-create branch under it are DELETED, and
  `mknod_arms_era`'s ret-0 arm is `mknod_post_ok_era` alone.  A `ret = 0`
  is a receipt unconditionally, which is what makes the theorem say
  anything about init: `mknod("console", …)` instantiates with
  `pl !! 0 ≠ Some SLASH`, the walk starts at `idup(p->cwd)` and `P 0`
  fires at the cwd's own inum — ROOTINO for init, but the contract never
  has to know that.  `mknod_post_fail_era` KEEPS its "whole bundle back"
  disjunct: that one is the argstr failure and is honest.
  WRITE STATEMENT DONE 2026-08-28 (Fable lane, `iris/SpecSysWriteAU.v`,
  810 lines, green): `delta_write` reuses `FsBlocks.blk_splice` (the
  splice IS the landed one; `delta_write_chain` = a chained run is one
  delta of the concatenation); per-chunk two-phase commits, bundle
  bounded by `wchunks n = ⌈n/FW_MAX⌉` (a COUNT of instants, boundaries
  existential); per-chunk offsets EXISTENTIAL (f->off moves unlocked on
  a shared struct file — chaining offsets is not a truth of the
  concurrent kernel); arms are TWO (n or −1 — the doc sketch's
  "partial ret" corrected: filewrite answers nothing between); fd side
  = the landed `fd_st` fragment, returned unchanged; stable corollary
  sealed with an UN-KEYED escape disjunct (no observable keys it) and
  the usual vacuity caveat.  OWNER QUESTIONS (header): wchunks
  exposure vs a stream commit; keep the sealed stable form or wait for
  exclusivity; sharper −1 tie?; lane A(iv) offset seam is now
  CONSUMER-MOTIVATED (first consumer = this contract).
  **THE WRITE AU PROVER LANE, 2026-08-29** (Opus lane; six new files, all
  EC2-green, zero `Admitted`).  The syscall shell and the corollary are
  SEALED; the chunk loop is the one open piece and its design is now
  discharged rather than sketched.  Files:
  - `iris/FsAbsWriteFire.v` — the per-chunk fire.  `awrite_commit_at`
    (authority-shaped, two-phase), `wrf_awrite_fire` (fused with the
    `ireg_top_retag` filewrite performs between writei's return and its
    `iunlock` — ProofFilewrite.v:2285, and that ONE line is the whole
    seam), the splice bridge `wrf_write_row` /
    `wrf_file_bytes_splice` (writei's range clause + `wi_dinode`'s
    `max` size IS `blk_splice`), and the instant-count arithmetic
    (`wri_count_lt`/`_step`/`_done`).  `Print Assumptions`: **Closed
    under the global context** — no axiom, not even funext.
  - `iris/SpecSysWriteAUEra.v` — `SYSWRITE_AU_ERA` (+ `_STABLE`), which
    is `SpecSysWriteAU` with ONE substitution.
    `wp_sys_write_au_frame` is REUSED VERBATIM (unlike
    `SpecSysMknodAU`'s, whose continuation the ustate sweep made
    unprovable: write does not move the image, so no `M'` binder
    arises), and so are `wri_receipts`/`wri_receipts_chained`.
  - `iris/SpecFilewriteAU.v` — `FILEWRITE_AU`, plus the loop's carried
    state `fw_au_raw` and its four moves (`_init`, `_take`, `_ok`,
    `_fail`, `_nofile`).
  - `iris/ProofSysWriteAU.v` — SEALS `SYSWRITE_AU_ERA` over
    `FILEWRITE_AU`; ProofSysWrite's walk instruction for instruction,
    15 s, first try.
  - `iris/ProofSysWriteAUStable.v` — `SYSWRITE_AU_ERA -> …_STABLE`, 14
    lines, lands in the escape disjunct at `off0 := 0`.
  AS-LANDED FINDINGS:
  1. **The astate-shaped commit is not dischargeable — again.**
     `FsAbsMknodFire`'s first finding repeats verbatim at the write
     delta: `abs_view` is not injective, so a client's fupd may return
     an authority at a map with the right READING and no `inode_local`,
     and `ftop_body` cannot be closed.  R10 keeps `SpecSysWriteAU`
     byte-identical; the era form carries the `_at` pair.
  2. **The peel sys_open needed is NOT needed here, and the short chunk
     must not fire.**  Open shares one `bs0` across an existential
     reseal; write's chunks each RE-LOCK, so the pre-row phase 1 sees is
     read off the same `top_frag` the fire retags, inside one critical
     section — the payload travels sealed.  And writei's DISTURBED tail
     (`dist`, up to one block, visible whenever the file was already
     longer) is not the splice, so a short chunk carries no receipt; it
     costs nothing, because `tot = n -> dist = 0` and the loop breaks on
     `r <> n1`, so every chunk that continues the loop is full and clean
     and the one that ends it is simply absent from `bss`.  That is the
     slack the fail arm's "total < n" leaves.
  3. **OWNER QUESTION 1 (new, and it gates the arm shape):
     `wri_pre`'s "the row is an `AFile`" is NOT derivable at filewrite's
     inode arm.**  The fd payload's entire type witness is
     `FileInvDefs.inode_pay`'s `⌜wr = true -> ty <> T_DIR_z⌝` — a
     DIRECTORY is excluded and nothing else — and `inode_pay` does not
     even take the descriptor's `fc_type` as a parameter.  So a
     T_DEVICE inode behind an FD_INODE descriptor is not refutable.  It
     is unreachable in xv6 (sys_open writes `FD_DEVICE` exactly when
     `ip->type == T_DEVICE`) and closing it is a one-conjunct
     strengthening at `FileInvDefs.file_payload`'s inode arm
     (`fc_type Cf = FD_INODE -> bv_unsigned ty = T_FILE_z`), discharged
     where that very test is — an R10 edit to a landed file that
     ripples through the file layer, hence the OWNER's.  Until then
     `write_arms_at` carries a THIRD arm: on such a row `abs_node`
     reads `ADev major minor`, fields writei never moves, so the
     abstract view does not move at all and every chunk's `delta_write`
     is the IDENTITY (which is what its totality was for); the arm
     delivers the fired PREFIX, refunds the rest, and says nothing
     about totals.  If the owner rules, the arm, the loop's `clean`
     flag and that whole branch go away together.

  **OWNER QUESTION 1 IS RULED AND PAID — 2026-08-29 (`file_payload`
  strengthening lane, whole tree green, zero `Admitted`).**  The
  FD_INODE payload arm now carries the fact; the write and read lanes can
  refute the device row without touching their contracts.
  - **THE CONJUNCT.**  `FileInvDefs.inode_pay` gained a PARAMETER
    (`fdty : mword 32`, sitting between `v` and `wr` exactly as the
    struct's own field order reads) and one conjunct, LAST inside the
    existing `∃ ty` block and beside the wr-guard it shares that `ty`
    with:
    `⌜fdty = FD_INODE -> bv_unsigned ty <> FsImg.T_DEVICE_z⌝`.
    Unconditional in `wr` — which is the ruling — and conditional on the
    FD's own type word, because ONE payload serves both typed arms and on
    the FD_DEVICE arm the claim is FALSE (the parked inode is precisely a
    device there).  `file_core` passes `fc_type C`, exactly as it already
    passed `fc_wbool C`.  It is `T_FILE_z` OR `T_DIR_z` by exclusion, not
    `= T_FILE_z` as the question guessed: an O_RDONLY *directory* fd is a
    legal FD_INODE file and read needs it to stay one.
  - **THE POSITION, and the banking's precedent applied.**  Inside the
    `∃ ty` block rather than after it, because the two facts must be
    about the SAME `ty`; last within it, so every opener that takes the
    block whole (`inode_pay_split`, `_cancel`, `file_core_split`,
    `file_payload_split`) is untouched — only the three sites that open
    the block moved.  The `T_DEVICE_z` is `FsImg`'s, QUALIFIED and not
    restated: FsImg is already in `FileInvDefs`'s cone through `FsCfg`
    (`FileInvDefs <- FsCfg <- IcacheEscrow <- FsState <- FsImg`), so the
    constant costs no import — `ProofSysOpenAUStores` spells it the same
    way.
  - **THE PAY SITES.**  `inode_pay_alloc` takes a second premise, and the
    ONE installer in the tree pays it: `ProofSysOpenParts.so_publish`
    (sys_open's publication, and the only `inode_pay_alloc` call there
    is).  It is free there — the `lh a4,68(s1); c.li a5,3; beq` at +0x76
    is the test that decides which type word the store writes — so two
    one-line lemmas discharge it: `so_tdev_zne` (the fall-through's
    register disequality read at Z level, `so_tdir_zne`'s sibling one
    constant over) and `so_dev_vac` (the taken arm's vacuity, FD_DEVICE
    ≠ FD_INODE).  filealloc/pipealloc install FD_NONE/FD_PIPE and never
    reach the arm; kfork/filedup/kexit copy through
    `file_payload_split`, so the conjunct rides along untouched.
  - **BROKEN SITES: 21 edits across 9 files** (the estimate was the
    banking's ~13; the banking itself measured 14 across 5).  The arity
    change bites only where `inode_pay` is *named* or its `∃ ty` block
    *opened*: `SpecFilestat` 2 (carve open + rebuild), `SpecFileread` 2
    (same; the grown output is a third, deliberate, edit),
    `ProofFileclose` 2 (the last closer's `iAssert` + `inode_pay_cancel`
    argument lists), `ProofFileread` 1 and `ProofFilewrite` 1 (one carve
    pattern each), `ProofSysOpenParts` 1 (`so_publish`, plus the two new
    branch lemmas), `ProofSysOpen` 7 (`so_tail_pub` and `so_stores`
    signatures, 3 tail calls, 2 store calls), `ProofSysOpenAUPub` 1,
    `ProofSysOpenAUStores` 4 (the derivation + 3 tail calls).  Every
    other consumer goes through `file_pay`/`file_ref` and did not move:
    filedup, kfork, kexit and sys_pipe carry the payload opaquely.
  - **THE AU LANE OWED NOTHING NEW.**  `so_stores_au` already carries
    `Htd` (`di_type = T_DEVICE_z -> tyw = FD_DEVICE`, forced by the AU's
    `t`), so the premise is its contrapositive, derived in four lines.
    Only the LANDED `so_stores` needed a new premise, because its store
    block ties the type word to nothing.
  - **THE EXPOSURE.**  `SpecFileread.fileread_pay_carve` — the one lemma
    both lanes already call — gained a fifth pure output,
    `⌜fc_type Cf = FD_INODE -> bv_unsigned ty <> FsImg.T_DEVICE_z⌝`,
    beside the `fc_wbool` one it grew for filewrite.  It has to be the
    carve and cannot be a `file_pay_st`-level lemma: the fact is keyed on
    the payload's generation `fp_ig`, which is ∃-bound in `file_pay_st`,
    so a caller's own `ity_shot` cannot be tied to it from outside.  A
    consumer joins the carve's `ity_shot g ty` to ilock's copy with
    `IcacheRef.ity_shot_agree` and reads `di_type dn <> T_DEVICE_z`.
    `FileInvDefs.inode_pay_not_dev` states the same at the invariant's
    own altitude (payload + a shot at its generation ⊢ the pure
    disequality; pure conclusion, so it costs the payload nothing).
  - **WHAT THE FOLLOW-ON LANES MAY NOW DO** (untouched here, R10 and
    their business): `SpecSysWriteAUEra`'s third arm
    (`write_post_nofile_at`) and the `clean` flag of the chunk loop can
    both go; `SpecSysReadAU`'s owner question 2 can sharpen
    `ard_ret_tie`'s wildcard to `ADir`.  Neither contract was edited.
  REMAINING — **`ProofFilewriteAU.v`, the chunk loop, and nothing else.**
  ProofFilewrite.v compiles in 44 s, so the copy is affordable; the
  design is fixed by `fw_au_raw`.  `fw_loop` gains three ordinary
  binders (`t : Z`, `p : nat`, `clean : bool`), one premise
  (`clean = true -> t = iz /\ iz = FW_MAX * Z.of_nat p`) and one wand
  (`fw_au_raw Γfs i n Φw t p`); the fire replaces line 2285's
  `ireg_top_retag`, keyed on `di_type dnl = T_FILE_z` AND on
  `rz = c` (both known there — writei has returned); the three exits
  are `fw_au_raw_ok` at `iz + c = n`, `fw_au_raw_fail` at the
  short-write break, `fw_au_raw_nofile` when `clean = false`; the back
  edge passes `iz + c`, `S p`, `clean` and re-proves the tie from
  `c = FW_MAX` (which holds because the chunk was not the last).  The
  capstone's non-inode arms are dead by the `st = FdOpen rb true
  (FdInode i)` premise.

  **THE CHUNK LOOP IS PROVEN — 2026-08-29 (FILEWRITE-AU lane, Opus; four
  new files, whole set EC2-green, zero `Admitted`).**
  `SYSWRITE_AU_ERA` AND `SYSWRITE_AU_ERA_STABLE` ARE UNCONDITIONAL
  THEOREMS.  `ProofFilewriteAU.v` (4.3 k lines, 57 s) seals `FILEWRITE_AU`;
  `LinkFilewriteAU.v` / `LinkSysWriteAU.v` / `LinkSysWriteAUStable.v`
  instantiate the three functors against real callee proofs.
  `Print Assumptions` on `SysWriteAU.wp_sys_write_au_era`, on
  `SysWriteStable.wp_sys_write_au_era_stable` and on
  `FilewriteAU.wp_filewrite_au` is the SAME THREE-LINE SET —
  `resv_matches`, `resv_is_valid`, funext — i.e. `LinkNameiEra`'s, and
  **`LinkConsolewrite`'s Axiom is NOT in it**: `LinkSysWrite`'s cone carries
  it, this one does not, because the AU premise refutes the device arm
  instead of walking it.
  - **THE FUNCTOR HAS FIVE PARAMETERS, NOT EIGHT.**  `st = FdOpen rb true
    (FdInode i)` plus `fdstate_ok` pins `f->writable = 1` and
    `f->type = FD_INODE`, so the `beq a5,x0` at +0x04, the FD_PIPE compare
    at +0x20, the FD_DEVICE compare at +0x26 and the `panic` else-arm are
    each refuted in three lines.  ~1050 lines of the landed walk (the
    pipewrite block, the whole devsw dispatch, the panic block) simply do
    not appear, and Pipewrite / Consolewrite / PANIC leave the parameter
    list with them.
  - **THE DEVICE ARM IS DEAD AND SO IS THE THIRD ARM.**  The owner's
    `file_payload` strengthening is consumed exactly where the design said:
    `di_type dnl = T_FILE_z` is now derivable at the fire from four facts
    joined at ilock — `inode_rec_local`'s four-way enumeration,
    `InodeLock.inode_ok`'s `type <> 0`, the carve's fourth output (not a
    directory, on a writable fd) and its FIFTH (not a device, on an
    FD_INODE fd).  `write_post_nofile_at`, `fw_au_raw_nofile` and
    `write_arms_at`/`write_stable_arms_at`'s third disjunct are DELETED;
    `ProofSysWriteAUStable`'s destructuring loses one bullet and
    `ProofSysWriteAU` needed no edit at all (it frames the arms opaquely).
  - **THE EOF-GUARD FINDING IS RULED AND PAID — 2026-08-29**
    (`SpecWritei` output-growth lane, whole tree green, zero `Admitted`).
    The gap was that `SpecWritei`'s success arm did not expose
    `off <= ip->size`: the fire needs `wri_pre`'s `off <= length bs0`, and
    without it the new file is `bs0 ++ junk ++ wrote` and NOT
    `blk_splice off wrote bs0`, so the delta is WRONG, not merely
    unprovable.  Only the `-1` arm recorded the guard the code tests, so a
    success past EOF was spec-permitted and code-impossible.
    - **THE CONJUNCT AND ITS POSITION.**
      `Z.of_nat off <= bv_unsigned (di_size dn)` — the literal negation of
      the `-1` arm's first reason, at the PRE-write record — placed SECOND
      in the writing arm, immediately after the `a0 = tot` equation, which
      is where the `-1` arm states its own copy.  Against durable-notes'
      new-conjunct-LAST rule, and deliberately: that rule buys its saving
      from intro patterns whose LAST name absorbs the remainder, and every
      one of this arm's four consumers writes a full-width `&`-chain and
      USES its last name (`dn0' = dn'`) in a `subst`.  LAST and SECOND
      therefore cost the same one line per site, and durable-notes' own
      mirror rule for a PURE conjunct ("put it SECOND, after the fact every
      producer already has") and the contract's local convention both point
      at SECOND.
    - **PROOF COST: FREE, as estimated, but not FREE-STANDING.**  No new
      proof obligation anywhere — `ProofWritei`'s `wp_writei_gen` already
      names the fall-through of the `+0x02 bltu` as `Hbig`, in exactly this
      spelling.  What it cost is a RELAY: the arm is built in one place
      (`wi_join`'s `right; split_and!`), so the fact travels
      `wp_writei_gen → wi_loop → wi_size → wi_join` as one new premise on
      each (3 signatures, 7 call sites, all positional).  `wi_ret` needed
      only its restated premise; both `-1` exits are `left` and did not
      move.  5,073 lines re-elaborate with no tactic change, and
      `ProofFilewriteAU` measures 62 s against the 57 s it landed at — the
      whole collapse is inside the noise.  The cone below `SpecWritei` is
      186 files, so budget a near-whole-tree rebuild for any edit to it,
      comment-only ones included.
    - **THREE CALLERS, FIVE SITES, ONE LINE EACH.**  `ProofFilewrite` (1),
      `ProofSysUnlink` (2), `ProofDirlink` (1), plus the campaign's own
      `ProofFilewriteAU` (1).  Four take an extra `_` in the writing arm's
      pattern; dirlink's took the arm WHOLE (`left; exact Hgood`) and
      became `(Hg0 & _ & Hgrest)` / `conj Hg0 Hgrest`.
    - **THE DIVIDEND, and it is the whole of the containment.**
      `SpecSysWriteAUEra.write_arms_at` / `write_stable_arms_at`: the fail
      arm's return value is the exact `-1` again (the
      `\/ (r = n /\ 0 <= n)` widening deleted).  `SpecFilewriteAU`'s loop
      invariant is `t = iz` again (`0 <= t <= iz` deleted).
      `ProofFilewriteAU`'s fire is keyed on `rz = c` ALONE; the second key
      conjunct is now a READING off `Hjoin`'s `0 < rz ->` guard, which
      gained a third component beside `rz = tot` and the `wi_dinode`
      equation.  The carried disjunction's non-firing branch records
      `rz <> c` (free from the `decide`), which is what makes the exhausted
      exit unconditional: `Hcrz : rz = c` refutes it, so `tf = t + c = n`
      and the `destruct (decide (tf = n))` with its fail branch is gone.
      `ProofSysWriteAU`, `ProofSysWriteAUStable` and the three Links needed
      NO edit — the syscall layer frames the arms opaquely, and the stable
      corollary's `by iPureIntro` closes the narrowed pure goal unchanged.
  - **TWO MORE PARALLEL FORMS, both `R10`-clean copies.**
    `fwau_tail` is `ProofFilewriteParts.fw_tail` with its post KEYED on the
    compare the block performs — `(iz = nz /\ rv = nz) \/ (iz <> nz /\
    rv = -1)` instead of `rv = -1 \/ (iz = nz /\ rv = nz)`.  The landed
    disjunction is enough for `filewrite_ret` but NOT for an armed post: at
    the exhausted exit it still permits `-1`, the one value the ok arm
    cannot carry.  Both branches prove the sharper form for free.
    `fwau_pay_carve` is `SpecFileread.fileread_pay_carve` with
    `fdstate_ok inum Cf st` as a SIXTH output: the carve and
    `file_pay_st_ok` bind the payload's `inum` under two separate
    existentials, so `i = bv_unsigned inum` — which the receipts need, since
    the fire retags at the inum and the contract indexes by `i` — is not
    otherwise derivable.  Both read off the same `pn`.
  - **`fw_test`'s post is one conjunct wider** (`c = nz - iz \/ c =
    FW_MAX`, free at both exits): the back edge needs it to re-prove
    `t = FW_MAX * p`, because a chunk that leaves `i < n` IS the cap.
  - **THE FIRE, as landed.**  One `iAssert` in place of the
    `ireg_top_retag`, keyed on `rz = c /\ off <= size`; on the key
    `fw_au_raw_take` peels the chunk's commit, `wrf_write_row` builds the
    splice row (writei's range clause at `dist = 0`, `wi_dinode`'s `max`
    size) and `wrf_awrite_fire` fires it inside the one `ftopN` section;
    off the key the landed retag runs unchanged.  Both branches deliver
    `∃ tf pf, ⌜(tf = t /\ pf = p) \/ (tf = t + c /\ pf = S p /\ rz = c)⌝ ∗
    fw_au_raw … tf pf`, which is what lets the ~370 lines from the retag to
    the exits stay single-copy.
  - **`Hjoin` grew one conjunct** — `0 < rz -> rz = tot /\ dn' = wi_dinode
    dnl bm' off tot` — because the landed join threw the record away (the
    retag does not look inside it) and the fire needs the splice.

  **READ IS CLOSED END TO END — 2026-08-30 (READ WALK PROVER lane, Opus;
  six new files, whole set EC2-green, zero `Admitted`).**
  BOTH Parameters of `SpecSysReadAUAt.SYSREAD_AU_AT` are sealed, and
  `LinkSysReadAU.v` makes them unconditional theorems.  `Print Assumptions`
  on `SysReadAU.wp_sys_read_au_at` AND on
  `SysReadAU.wp_sys_read_au_at_stable` is the SAME THREE-LINE SET the whole
  campaign carries — `resv_matches`, `resv_is_valid`, funext — and
  **`LinkConsoleread`'s Axiom is NOT in it**: `LinkSysRead`'s cone carries
  it, this one does not.  Files, with measured compile times:
  - `iris/SpecFilereadAU.v` (189 lines, 3 s) — `FILEREAD_AU`.
    `SpecFileread.wp_fileread_sconf_body` verbatim with three edits: the
    premise `st = FdOpen true wb (FdInode i)`, the resource
    `aread_commit_at Γfs ∅ i Φr`, and `read_arms Γfs i n Φr r` in place of
    `⌜fileread_ret n r⌝`.  The user-memory WINDOW survives verbatim — the
    syscall shell above still needs it to rebuild `proc_priv`.
  - `iris/ProofFilereadAU.v` (2.0 k lines, 33 s) — the walk.
  - `iris/ProofSysReadAU.v` (1.0 k lines, 16 s) — the syscall shell,
    `ProofSysWriteAU`'s four deltas verbatim (the object code is the same
    twenty-five instructions).
  - `iris/ProofSysReadAUStable.v` (148 lines, 3 s) — the corollary AND the
    seal.
  - `iris/LinkFilereadAU.v`, `iris/LinkSysReadAU.v`.
  - **THE FUNCTOR HAS THREE PARAMETERS, NOT SIX.**  `fdstate_ok` against
    the premise pins `f->readable = 1` and `f->type = FD_INODE`, so the
    `c.beqz a5` at +0x0e, the FD_PIPE compare at +0x24, the FD_DEVICE
    compare at +0x2a and the `panic` else-arm are each refuted in three to
    five lines.  ~980 lines of the landed walk (the readable -1 block, the
    piperead block, the whole devsw dispatch, the panic block) do not
    appear, and Piperead / Consoleread / PANIC leave the parameter list
    with them — which is where the axiom goes.  ONE arm the write lane
    could refute survives here: the fork's SIGN GUARD at +0x1a is a test on
    a trapframe word and is walked, which is the only reason read has a
    fail arm with an UNSPENT commit.  It lands in `read_post_fail`'s left
    disjunct through `aread_commit_at_weaken` (the frozen arms are stated
    over the astate-shaped commit; that weakening is what the `_at` file
    was built to supply).
  - **THE FIRE IS AN INSERTION, NOT A SUBSTITUTION, and that is the whole
    structural difference from the write lane.**  A read retags nothing, so
    there is no `ireg_top_retag` to fuse into: `arf_read_fire` stands on its
    own, immediately after the `f->off` CHECKOUT and before the four
    argument moves, taking the payload's own `top_frag` QUARTER — the one
    `FsStateEra.inode_rd_era_era_node_to` hands out at the read-arm shed —
    and giving it straight back.  `ard_pre`'s three conjuncts are exactly
    what is in hand at that boundary and nowhere earlier: the row (the fire
    proves it itself off the fragment), the offset cap (`FileOff.off_wf`,
    just produced by the checkout) and the size cap (`arf_size_ok_era` over
    the loaded record's `Hszb`, the premise readi is about to be handed).
    Every LATER boundary in the window would do equally well — that is THE
    ONE INSTANT, and it is the reason the ~700 lines from the fire to the
    two exits stay single-copy with no carried disjunction (contrast
    `fw_au_raw`, which the write loop needs because its instants recur).
  - **THE FOUR ARMS, and where each lands.**  `+0x1a` n < 0 →
    `read_post_fail` LEFT (the refund).  readi's copyout fault →
    `read_post_fail` RIGHT, the FIRED receipt: the lock window happened and
    the source value was observed even though the copy died.  readi's count
    at `r = 0` (the `blez` skips the advance) and at `r > 0` → both
    `read_post_ok`, at the same exact tie.  The `blez` diamond does NOT
    separate the fault from the zero return — both take the branch — so
    `Hrdret` is destructed a SECOND time inside the skip arm; keeping
    `Hcase`'s right disjunct three-wide (`a0 = tot /\ 0 < tot /\ tot =
    rd_clamp …`) is what lets the advance arm avoid re-deriving readi's
    equation from a value comparison.
  - **THE RETURN TIE IS TWO LINES AND A CASE SPLIT** (`frau_ret_tie`):
    `arf_count_bridge_era` on the file row, `fr_clamp_le` on the other two.
    THE DIRECTORY ROW STAYS BOUNDS-ONLY — the premise does not exclude it
    (xv6 keeps T_DIR under FD_INODE, `ls` reads directories through
    `read()`) — and the DEVICE row folds into the SAME wildcard arm.  So
    the payload's fifth carve output, which the write lane spends to kill
    its third arm, is NOT needed here at all: read's contract weakens toward
    the caller on both non-file rows and never has to tell them apart.
    `SpecSysReadAU`'s owner question 2 (sharpen the wildcard to `ADir`) is
    therefore still open, still R10-clean, and now provably cheap — the
    fifth output is already in `frau_pay_carve`'s hand.
  - **`frau_pay_carve` IS `fwau_pay_carve`, COPIED.**  Both AU lanes need
    `fdstate_ok inum Cf st` as a sixth carve output for the same reason (the
    carve and `file_pay_st_ok` bind `inum` under separate existentials, so
    `i = bv_unsigned inum` is not otherwise derivable), neither may edit
    `SpecFileread` (R10), and requiring the write lane's copy from the read
    lane would drag its whole cone in.  The copy is deliberate; retiring
    BOTH into `FileInvDefs` is one edit when the tree next takes a
    bottom-of-tree rebuild, and it belongs with the other five S4' items
    `SpecFileread`'s header already lists.
  - **THE SEAL HAD TO BE SPLIT DIFFERENTLY FROM WRITE'S.**
    `SYSWRITE_AU_ERA` and `..._ERA_STABLE` are two module types with one
    field each, so `ProofSysWriteAUStable` is a pure functor over the AU
    module.  `SYSREAD_AU_AT` carries BOTH Parameters, so one module has to
    contain both proofs: `ProofSysReadAU` exports the walk UNSEALED as
    `SysReadAUWalk`, and `ProofSysReadAUStable` `Include`s an application of
    it, adds the corollary beside it and applies the seal once.  R10 keeps
    `SpecSysReadAUAt.v` byte-identical; only where the seal sits moved.
  - **THE STABLE DERIVATION IS THREE MOVES AND NO ESCAPE ARM.**
    Instantiate the AU at `arf_pin_recv Γ i q (MkAnode (AFile bs0) nl) Φr`;
    build its commit with `arf_pin_compose` (the client's `nview` is spent
    ONCE, on the way in, and rides inside every receipt after);
    `arf_stable_of_arms` collapses the arms, and the body's `0 <= n` premise
    is what refutes the guard arm — whose refund would otherwise strand the
    wrapped share inside the returned closure.  Write's ok arm had to take
    an UN-KEYED escape disjunct at `off0 := 0` because chaining one chunk's
    offset to the next is not a truth of the concurrent kernel; read has ONE
    instant, so there is nothing to chain and nothing to escape into, and
    both arms land at the client's own value.  The landed
    `arf_stable_of_arms` measured Qed trap (cut at the disjunction, never
    one two-arm entailment) held: the derivation is 3 s.
  - **THE VACUITY CAVEAT IS UNCHANGED AND STILL ONE-SIDED.**  A client
    `nview` share against a live inum is refuted by today's whole-element
    payload custody (`FsAbsSeam`'s finding 3), so the stable form is vacuous
    until the tree layer's exclusivity fact exists.  Unlike write's, it needs
    no re-cut then: a read fires no retag, so the same sealed statement
    becomes non-vacuous as it stands.
  - **REUSE, MEASURED.**  `ProofFileread`'s pure prefix (`fr_maxfile_bsize`,
    `fr_K6`, the five stack projections, `fr_clamp_le`, `fr_ret_of_readi`,
    …) and `ProofSysRead`'s four address lemmas are TOP-LEVEL in their
    files, so both AU walks reuse them by `Require` and copy none of them —
    `ProofSysWriteAU`'s precedent, applied on both storeys.
    `ProofFilereadParts`'s `fr_pro` / `fr_epi` take an abstract continuation
    and never mention fileread's post, so they are reused as they stand.
    That is the sys_open lane's rule holding for a fourth syscall: only the
    blocks that fire a commit or mint the armed post are re-derived.
  **OPEN'S PLAIN ARM IS PROVEN** (Opus lane): `SpecSysOpenAUPlain.v` seals
  `SYSOPEN_AU_PLAIN` — `SpecSysOpenAU.wp_sys_open_au_plain_body` byte for
  byte, the O_CREATE parameter split off — and `LinkSysOpenAU.v`
  instantiates the functor against real callee proofs, with
  `Print Assumptions` BYTE-IDENTICAL to `LinkNameiEra`'s (`resv_matches`,
  `resv_is_valid`, funext).  Ten new files, ~6200 lines, zero `Admitted`.
  WHAT MADE IT AFFORDABLE, and it is the rule for the remaining syscalls:
  **the landed failure tails and parts layer are RESOURCE-GENERIC and were
  reused verbatim.**  `ProofSysOpenTails`'s seven tails take an abstract
  `wp_next` continuation, not `sys_open_post`, so an AU walk frames its
  residue through them untouched; only the blocks that (a) fire a commit or
  (b) mint the success post had to be re-derived — the entry, the walk, the
  join, the alloc, the stores and the publication.  Check this before
  sizing unlink/read/close: if a syscall's tails are equally generic, its
  AU proof is the same five blocks.
  THREE AS-LANDED FINDINGS:
  1. **The observed-row tie is a DATA tie, and it forces the payload to
     travel PEELED.**  The FILE arm shares one `bs0` between the terminal
     observation (fired at `ilock`, because every post-walk failure must
     deliver a fired receipt) and the O_TRUNC receipt (fired at the retag,
     far below).  `IcacheEscrow.ic_loaded` binds its `data` EXISTENTIALLY,
     so a peel-reseal-repeel in between yields two unrelated witnesses and
     two `fn_file_bytes` terms.  `ProofSysOpenAUParts.so_flat` is
     `ic_loaded_flat_body` with `data` exposed; the blocks below the fire
     carry it and close it back only where a failure tail's `iunlockput`
     wants the sealed form.
  2. **The trunc commit CANNOT be split across the retag.**  Phase 2 needs
     the authority AT the delta, and any other row may move between the
     retag and a later phase-2 — so the fire is FUSED with the retag it
     replaces (`FsAbsOpenFire.opf_atrunc_fire` in `mkf_acre_fire`'s mold).
     Same premise as `ireg_top_retag`, same payout, plus the receipt.
  3. **The success post is a STRENGTHENING of an existing output, not new
     work.**  `so_publish` already computes the typed `stpub`; the AU
     publication only opens the bundle with `fd_frags_acc` instead of
     `fd_frags_any_acc` so the row survives, and reads `stpub`'s shape off
     `fdstate_ok_inj`.
  REMAINING ON OPEN: **the O_CREATE arm**, which is the expensive half and
  is NOT a variant of the above — it needs a create-AU carrying
  `ty = T_FILE`, and `SpecCreateAU` is T_DEVICE-PINNED BY CONSTRUCTION (its
  header, difference (2): the pin refutes the mkdir half and the found-arm
  type inspection, −3,900 lines).  So the arm costs a general-`ty` or
  T_FILE-twin `ProofCreateAU` (7,121 lines) before any sys_open work
  starts; size it as a lane of its own.  **DONE 2026-08-29 — that lane is
  W-F below (`SpecCreateAUF` / `ProofCreateAUF` / `LinkCreateAUF`, the
  twin), and the bridge into these arms is `SpecCreateAUFOpen`.**  What is
  left on the O_CREATE arm is sys_open's own walk at that contract.  When
  it lands, delete `SpecSysOpenAUPlain.v` and seal `SYSOPEN_AU` whole.
  REMAINING: ~~unlink AU (wants the npar walk's contract shape)~~ **DONE
  2026-08-30, see W-U below**, then read/close/fstat/chdir, mechanical.
  NOTE (2026-08-27): the fd-state ghost
  landed upstream (`FdSlots.fd_frags` beside `ut_own`; `fdstate` =
  open-or-closed + `fdtype`, two-halves algebra, commits 28d707dc +
  3199a1b6; `FdInode` carries its INUM as of d1411776, riding on
  `file_ref`'s index) — the descriptor arms of these specs speak THAT
  carrier and can tie fd → inum → the §2 abstract node directly; the
  campaign does not mint its own fd ghost.
- [x] **W-F — the T_FILE CREATE CARRY (the O_CREATE arm's prerequisite).**
  DONE 2026-08-29 (Opus lane).  Shape chosen: **the T_FILE TWIN**, not a
  general-`ty` form — the general form's extra cost is not a statement
  change (`SpecSysMknodAU.delta_create` is already type-parameterized and
  `acre_bump` already handles the dir case) but the ~3,900 lines of mkdir
  walk `ProofCreateAU` deletes, plus that arm's two extra abstract
  obligations (the parent's nlink bump and the "."/".." content that makes
  the child's row an `ADir`), and no consumer on this list wants them.
  FIVE NEW FILES, all EC2-green, zero `Admitted`, R10 clean (`SpecCreate`,
  `SpecCreateAU`, `SpecSysOpenAU`, `ProofCreate`, `ProofCreateAU`,
  `FsAbsMknodFire` all byte-identical; only `iris/_CoqProject` moved):
  - `FsAbsCreateFire.v` (245 ln, 2.9 s) — **FIRE 2 at a NON-DIRECTORY
    child.**  `mkf_acre_fire` is device-pinned only through
    `SpecSysMknodAU.delta_create_dev`, whose proof uses nothing about a
    device but that it is not an `ADir` (that is what zeroes `acre_bump`
    and what `cre_pre_ne` needs).  So: `caf_delta_create_nondir`,
    `caf_acre_fire` (any non-`ADir` `c`), `caf_acre_fire_file`, and the
    row reading `caf_child_file` (`create_made T_FILE _ _` reads as
    `AFile []` at nlink 1 — size zero, so `file_bytes _ 0 = []`).
  - `SpecCreateAUF.v` (409 ln) — `wp_create_auf_body`: `SpecCreateAU`'s
    body at `ty = T_FILE`, the commit at `AFile []`, and the success
    payout **keyed on `made`** (`cauf_ok`), because `ok = true` no longer
    forces it.  `cauf_fail` is `cau_fail` at the file child.  Projections
    `cauf_ok_fresh` / `cauf_ok_exists` for the consumer.
  - `ProofCreateAUF.v` (7,398 ln, 1 m 50 s) — `ProofCreateAU` with ARM
    F-OK restored verbatim from `ProofCreate` (+0x5c..+0x70, the
    `lhu`/`addiw`/`slli`/`srli`/`bltu` type span and F-BAD's second entry,
    ~250 ln) and the `ty <> T_FILE` bullet refuted instead.  The mkdir
    refutation at +0xca is UNCHANGED (`T_FILE <> T_DIR`).  The one
    structural change beyond the arm: FIRE 1's receipt is no longer folded
    into `cau_fail` one line after the fire — it now has TWO possible
    consumers (F-BAD folds it into `cauf_fail`, F-OK hands it out as
    `cauf_ok`'s `made = false` arm), so `HFex`/`HPpar`/`Hacre` ride down
    the +0x4a..+0x6c walk and are assembled at each leaf.
  - `LinkCreateAUF.v` — the same seven real callee proofs as
    `LinkCreateAU`.  `Print Assumptions CreateAUF.wp_create_auf` = **3**:
    the two platform axioms (`resv_matches`, `resv_is_valid`) + funext.
    Identical to `LinkCreateAU`'s cone.
  - `SpecCreateAUFOpen.v` (185 ln) — the bridge INTO `SpecSysOpenAU`
    (which does not move).  `cauf_fail_to_open` is the WHOLE failure fold
    (`cauf_fail`'s three alternatives are `open_post_fail_create`'s inner
    three arm for arm; arm (a) is unreachable from a create that returned
    0, by construction).  The success side is a FRAMING, not a fold —
    `open_post_ok_create`'s two disjuncts each end in `open_fd_ok`, which
    create never sees — so `cauf_ok_shape` records the correspondence
    over the parts create DOES own.
  WHAT IS LEFT ON THE O_CREATE ARM: sys_open's own walk of
  `create(path, T_FILE, 0, 0)` at this contract, its terminal
  `opf_open_fire` on the returned locked child (whose `AFile`/`ADev` split
  is paid by this post's `di_type dn = T_FILE \/ di_type dn = T_DEVICE`
  through `opf_era_file_row` / `opf_era_dev_row`), and the
  `delta_trunc_nil` refund on the FRESH arm.  The carry itself is done.
  LATER CONSOLIDATION, recorded so it is not rediscovered: the three
  create walks (`ProofCreate`, `ProofCreateAU`, `ProofCreateAUF`) collapse
  into ONE non-directory-generic AU walk (`ty <> T_DIR`, both sides of the
  `bne s2,2` proven, the child's row a premise `abs_of (era_node
  (create_made ty mj mn) _ _) = MkAnode c 1`), which `caf_acre_fire`
  already supports.  That is a refactor, not new mathematics.
- [x] **W-U — THE UNLINK AU, the last mutating-syscall lane.**  DONE
  2026-08-30 (Opus lane).  `SpecSysUnlinkAU.SYSUNLINK_AU` is SEALED and
  `LinkSysUnlinkAU` makes it unconditional; assumption set = `resv_matches`,
  `resv_is_valid`, `functional_extensionality_dep`, i.e. `LinkNamexEra`'s,
  with NOTHING new entering the cone.  EIGHT NEW FILES, all EC2-green, zero
  `Admitted`, R10 clean (`SpecSysUnlinkAU`, `SpecSysUnlink`, `ProofSysUnlink`,
  `ProofSysUnlinkParts`, `ProofSysUnlinkTails`, `FsAbsMknodFire`,
  `SpecNparWrapEra` all byte-identical; only `iris/_CoqProject` moved):
  - `FsAbsUnlinkFire.v` (5.7 s) — THE FIRE LEAF, the one-per-syscall
    precedent of `FsAbsMknodFire` / `FsAbsOpenFire` / `FsAbsWriteFire`.  The
    four fires and the four bridges.  `uf_uent_fire` (instant 1) replaces
    the parent-row `ireg_top_retag` and reads a SECOND, read-only fragment
    beside it — `unl_pre`'s last three conjuncts are about `ip`, whose lock
    the walk has held since W3, and that borrowed row is what lets the pair
    be read as one delta later (`delta_unlink_split`).  `uf_utgt_fire` is
    instant 2.  `uf_dmiss_fire` is the fired miss; `uf_dex_fire` fires the
    REUSED `dlookup_commit_at` at the isdirempty refusal holding BOTH
    fragments, so one `av` carries all four of arm (iii-c)'s conjuncts.
  - `ProofSysUnlinkAUParts.v` + `ProofSysUnlinkAUW1/W2/W3/W5F/W5D.v` +
    `ProofSysUnlinkAU.v` (the seal) + `LinkSysUnlinkAU.v`.
  AS-LANDED FINDINGS:
  1. **THE AU PROOF OF A SYSCALL IS ITS LANDED PROOF, BLOCK FOR BLOCK.**
     The five blocks are copy-adapts and the diff per block is ~40 lines out
     of 700–2200; the instruction-level script is untouched.  Three files
     are reused VERBATIM and each has a reason: `ProofSysUnlinkParts` (no
     contract in it), `ProofSysUnlinkTails` (**every exit block** — the
     tails conclude ABSTRACTLY, so the AU caller supplies a continuation
     that pays `unlink_arms` at −1 and not one line of them moves), and
     `ProofSysUnlink` itself for its top-level pure layer.  That last is a
     whole-function proof taken as a dependency, which the house rule
     forbids for ANOTHER function; this is the same function's second
     contract, the case the rule does not cover.  **Budget the next AU lane
     at its landed walk's line count, not at a re-proof.**
  2. **ONE FIRE LEMMA SERVES BOTH W5 ARMS**, and the reason is that `dec` is
     `unl_dec` of the TARGET's row, read off the target's own fragment: 0 on
     the FILE arm (so the parent's count does not move and `unl_pre`'s
     dots-only conjunct is vacuous), 1 on the DIR arm, where W5-DIR's single
     post-`iupdate(dp)` retag makes the fire cover entry-delete and count
     together.
  3. **THE ONE STRENGTHENING TAKEN OVER A LANDED BLOCK** is `su_w4_exitE_au`,
     which carries the isdirempty loop's NON-EMPTY WITNESS (`exists k,
     2 <= k < dir_nrec /\ dir_live`).  The landed exit threw it away and arm
     (iii-c) is precisely the report that it happened — it cannot be
     re-derived downstream, because the loop's index is gone.  `k < dir_nrec`
     comes from the FULL-READ fact `su_clamp16_in` already leaves
     (`su_nrec_lt`).  No statement of `SpecSysUnlinkAU` moved.
  4. **The `uptd_ext` / `uptd_ext_sz` seam.**  The AU contract's inlined
     return continuation reports the descriptor growth as `uptd_ext` where
     the landed closer's — and therefore every block's — is the stronger
     `uptd_ext_sz`.  `ProcPtOwn.uptd_ext_sz_ext` closes it ONCE at the top
     of the seal rather than at each of the eight exits.
  5. **`lia` does not identify convertible-but-not-syntactically-equal
     atoms**, and the DIR arm's parent-count premise (`A = A + 1 - 1` on two
     spellings of the stored halfword) is where it bites.  The landed walk
     hits the same wall at its own `HdWnd` site; the route is one
     `Z.add_simpl_r` rewrite and `reflexivity`.
  OWNER QUESTIONS 1–4 in `SpecSysUnlinkAU`'s header are ANSWERED BY
  CONSTRUCTION as the statement proposed them: the two-instant surface is
  realizable and realized (Q1); ret 0 does NOT fire the found observation,
  and `unl_pre`-at-instant-1 was enough at every consumer inside the walk
  (Q2); the dot refusal stayed PURE and needed no parent observation (Q3);
  the mask floor ∅ never bound (Q4).
- [x] **P — the /init pin port (after D; independent of S0).**  DONE
  2026-08-28 (Opus lane, `iris/FsInitPin.v`, 505 lines, EC2-green in
  **5.5 s**, zero `Admitted`, and `Print Assumptions` on all three
  theorems is **EMPTY** — only Rocq's own `PrimInt63`/`PrimString`
  primitives, so the pins carry NO logical axiom, not even funext).
  NOTHING WAS RE-ENABLED: the boot chain is untouched and no file
  requires this one (it is an `FsImgCheck` consumer, hence a leaf).
  THE ERA-0 PREMISE, in its exact landed spelling:
  `SystemAdequacy.fsimg_snap_ok : snap_ok (img_state fsimg_P fsimg_sb
  fsimg_nib) (fs_restrict fsimg_P (fs_home_set fsimg_cov (sb_logstart
  fsimg_sb)))` — unchanged by durable-disk BT-3, which this file is
  stated against.  That map is named `era0_D`.
  THE TWO PINS, both ROUTE (b) (pure in `era0_D`, quantified over EVERY
  `S` with `snap_ok S era0_D`, hence eternal for era 0 and persistent
  for free):
  - `era0_init_path_pin S : snap_ok S era0_D -> apath_at (abs_view
    (fss_inodes S)) ROOTINO init_path = Some INIT_INO` (`INIT_INO := 7`,
    `init_path := [fname_init]`);
  - `era0_init_content_pin S : snap_ok S era0_D -> abs_view (fss_inodes
    S) !! INIT_INO = Some (MkAnode (AFile init_bytes) 1)` with
    `init_bytes := ElfUser.init_elf` (= `SpecKexecPinned.init_bytes`,
    `fv_of init_dn init_data`, by `init_bytes_elf`).
  Plus `era0_root_row`, `era0_dur_root`/`era0_dur_init` (the `dur_node`
  certificates), and `era0_init_arun : arun (abs_view (fss_inodes S))
  ROOTINO init_path [ROOTINO; INIT_INO]` — **exactly the premise
  `FsAbsPins.apr_walk` takes**, which is the composition point with lane
  A(iii)'s live walk.  ROUTE (a) is section 6: `astate_era0_init_path`
  and `nview_era0_init` (a client share of inum 7 IS /init's bytes, via
  `astate_nview`), for a consumer holding the founded authority.
  WHY THE SNAPSHOT STATE IS THE PLACE TO STAND: the snapshot mint
  reaches `FsState.fs_boot_alloc_root_slack` AT `fss_inodes S`, so the
  founded `astate` is `abs_view (fss_inodes S)` on the nose.
  GAP (transport, not a missing lemma): nothing at `boot_shared_alloc`'s
  altitude says THIS era's `D` is the image's — `S` and the snapshot
  arrive as parameters, era-generic.  Post-BT-3 the producer of the pins'
  premise is `FsDurSnap.fs_snap_read_ok_keep` (non-destructive) off the
  epoch the mint takes; what is still owed at era 0 is
  `fs_recovery_det` + `fsimg_snap_ok` identifying that epoch's map with
  `era0_D`.  BT-3 also removed the `Rb` slot as a delivery channel (`Rb`
  is now named at `FsCrash.P_fs_lend`).

  **GAP (1) CLOSED 2026-08-29** — `iris/FsInitPinBoot.v`, EC2-green in
  **3.2 s**, zero `Admitted`, and `Print Assumptions` on all thirteen
  artifacts is EMPTY (only Rocq's `PrimInt63`/`PrimString` primitives, so
  the transport carries no logical axiom either).  A SECOND LEAF, not an
  appendix to `FsInitPin`: its import cone is `FsInitPin`'s own — every
  module it requires, `FsInitPin` already requires — so hygiene forced
  nothing and the split is on ALTITUDE (a fact about a boot's premises,
  which computes nothing, beside a fact about a gmap, which computes the
  image), keeping `FsInitPin`'s landed text and empty audit untouched.
  THE ERA-0 PREMISE at the boot altitude, exact landed spelling: there is
  no era COUNTER there and cannot be one (`xv6_boot_era` runs at every
  power-on and knows only `FsCrash.P_fs_project`'s reading of its disk),
  so era 0 is an equation about the DISK — the one hypothesis
  `SystemAdequacy.xv6_power_adequacy_xv6Σ` takes,
  `Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk`, read at the
  block view as `FsCrash.fs_blocks dk = FsImgDisk.fsimg_P` — plus
  `cov = fsimg_cov` (the crash predicate fixes `cov` for the whole
  execution).  The LOG START is NOT assumed: `sk_sbok`→`FsImg.sbo_logstart`
  pins the era's at 2 and `FsImgCheck.fsimg_sb_logstart` checks the image's
  at 2 (`era0_logstart` — this is `xv6_boot_era`'s own `Hlseq`).
  TWO ROUTES, because the boot uses both:
  - (A) off the mint's own bundle `FsCfgBoot.fs_boot_snap_wf` —
    `era0_boot_map : … → fs_restrict Pb (fs_home_set cov (sb_logstart sb))
    = era0_D`, hence `era0_boot_snap_ok : … → snap_ok S era0_D` and
    `era0_boot_pins : … → era0_pins (abs_view (fss_inodes S))`.  The step
    is bundle conjunct (6) (`Pb` = raw disk off the header write set) plus
    `era0_hdr_wset : hdr_wset fsimg_P (sb_logstart fsimg_sb) = ∅`, off
    `FsImgCheck.fsimg_wf_log_clean` — mkfs leaves a clean log.
  - (B) off the crash predicate's epoch — `era0_recovery_D : fs_recovery
    fsimg_P D fsimg_cov (sb_logstart fsimg_sb) → D = era0_D` (by
    `fs_recovery_clean` at the same clean log), its converse
    `era0_recovery`, `era0_lend_D` (`fs_recovery_det` + the disk equation:
    the lent epoch's map IS `era0_D`), and `era0_recovery_pins`.
  `era0_pins av` is the three conclusions as one `Prop` (path pin, content
  pin, and the `arun` walk `[ROOTINO; INIT_INO]`).
  CRASH-BEFORE-/init, and it was free: `era0_reboot_pins` — `fs_recovery`
  is a function of the PHYSICAL disk, so "nothing committed" is spelled as
  "the re-boot's disk still carries the image's bytes", and
  `fs_recovery_det` gives `D' = D = era0_D` and the same pins.  None of the
  recovery cone is dragged in: what PROVES an uncommitted era leaves the
  durable extent alone is the WAL's own argument, consumed here as the
  hypothesis.
  RESOURCE FORMS: `fs_snap_era0_pins` (off the lent epoch, snapshot handed
  back — `fs_snap_read_ok_keep` composed with the pins, premise
  `era0_dblk_full` discharged here) and, at the founded authority,
  `astate_era0_boot_pins` / `nview_era0_boot_init` — `FsInitPin` §6 with
  its `snap_ok` premise replaced by the boot's bundle, so a consumer
  (ProofForkret's pinned-kexec gate) owes only the era-0 disk equation.
  MEASURED GOTCHA, and it is about the LEAF RULE, not about `set_solver`:
  one `set_solver` closing `b ∉ ∅` — with `b ∈ fs_home_set fsimg_cov …` in
  the CONTEXT, `fsimg_cov` being a 1,999-element `list_to_set` literal —
  took the file from **3.2 s to 3 m 49 s**.  The reason is that
  `FastSetSolver`'s override is a `Tactic Notation` and therefore needs
  IMPORT: the chain that carries it (`BitmapEnc` `Require Export`s it) is
  broken by every intermediate that only `Require Import`s, so in an
  `FsImgCheck`-consumer leaf `set_solver` is UPSTREAM's, and
  optimization.md's "set_solver at capstone altitude is now fine" does not
  apply.  Either `Require Import FastSetSolver` or, as here, close the goal
  by hand (`exact (not_elem_of_empty b)`) and keep the cone unchanged.
  MEASURED GOTCHA, recorded in optimization.md and in the file's §3
  header: `injection`/`exact` against an equation carrying the
  35,976-byte `init_elf` literal DOES NOT FINISH (>15 min, both
  spellings) — conversion unfolds `FsTree.file_bytes`, which is
  quadratic in the file size.  Prove `Some (NFile b) = Some (NFile b')
  -> b = b'` AT VARIABLES and close the instance by transitivity through
  `node_at`.  That one change took the file from >15 min to 5.5 s.
- [x] **Y — sys_sync.  DONE 2026-08-29 (banking landed, contract PROVED).**
  The `flushed` receipt (persistent snapshot certificate copy, plan 4⁹.3)
  + the `wp_sys_sync` parallel form (R10), per doc §5 principle 2's
  derivation chain — items (i), (ii) and (iii) all closed.

  **THE BANKING (owner-ruled 2026-08-28, executed 2026-08-29).**  The
  receipt now has a client-reachable producer and `SYS_SYNC_FLUSH` has an
  implementing functor.  Whole tree green on the mirror; ZERO `Admitted`;
  no arity moved (`log_ctx`, `wp_end_op`, `log_names` all stand) and no
  landed contract statement moved (`SpecSysSync.v` byte-identical,
  `SpecSysSyncFlush`'s Module Type byte-identical, `ProofSyscall` arm 22
  untouched).

  - **THE CONJUNCT.**  `LogInv.log_flushed_bank γ e := ∃ b D,
    log_epoch_lb γ e ∗ flushed b D ∗ ⌜snap_holds D⌝` — the lane's prepared
    definition verbatim — added to `LogInv.log_res` as the LAST conjunct
    BEFORE the `if cmt` arm, not after it.  That is the position `log_res`'s
    own comment already argues for (the arm is what every opener
    destructures further, so a conjunct after it costs each of them a
    restructuring rather than one name in a pattern), and it is what keeps
    `ProofSysSync`'s three cell-accessors intact: their pattern ends at
    `%Hcap` and closes with `iExact "Hrest"`, so the bank rides inside
    `Hrest`.  Verified against every site, not assumed.
  - **THE ONE STRUCTURAL COST, and it was not in the estimate: the receipt
    had to MOVE DOWN.**  `FsFlushed.v` is a leaf over `FsDurSyscall`, whose
    cone contains `SystemAdequacy` and therefore the whole proof tree,
    `LogInv` included — so a conjunct of `log_res` could not be *stated*
    over it.  §§1–2 moved verbatim into a new `iris/FsFlushedCore.v`, a leaf
    over `FsCrash` + `FsDurSnap` (`FsCrash`'s cone is 48 files and does not
    contain `LogInv`; `FsDurSnap` was already in `LogInv`'s cone through
    `LogSnapLaw`).  `FsFlushed.v` re-exports it and keeps §3 `dur_at`
    unchanged, so no importer moved.  `snap_holds` moved one line under
    `snap_ok` in `FsDurSnap` for the same reason (4 referencing files;
    `FsDurSyscall` re-exports).  `LogInv` gains `!fsCrashG Σ` — an `xv6G`
    member, exactly the precedent its own section header records for
    `fsLinkG`/`fsTopG` — so no consumer of `log_ctx` gained a binder.
    **`SpecSysSyncFlush` was retargeted to `FsFlushedCore`/`FsDurSnap` too,
    and that is what made the contract provable at all**: stated over
    `FsFlushed` it sat above `ProofSysSync`.
  - **THE PRODUCER SIDE (`FsCrash`).**  `P_fs_bank` (the record's own
    receipt + `snap_holds`, non-destructive), `fs_bank := ∃ D,
    fs_receipt_any D ∗ ⌜snap_holds D⌝`, and `fs_rec_permit_bank : fs_rec_permit
    … Q -∗ fs_rec_permit … (Q ∗ fs_bank)` — a premise-free strengthening
    available at ANY WAL write, because the permit already has the record
    open at the post-write image.  Only `fs_clear_keep_seq_permit` uses it
    (two lines, one per sector order); `fs_commit_L_seq_permit` is
    unchanged.
  - **THE TWO DEPOSITS, both at a counter SET.**  `ProofEndOp.eo_tail` (new
    `fs_bank` premise, banked in the same breath as `log_epoch_bump`) with
    the copy taken at the commit's LAST write — the preserving CLEAR after
    the install, so it is that batch's own durable state on either sector
    order; and `ProofInitlog`'s seal at genesis (E = 1), off the same clear,
    which is the one write `initlog` makes and is why the bank is never
    empty.  `end_op`'s empty-log path (no commit body, but `ncommit` still
    increments) recycles the invariant's own copy through
    `log_flushed_bank_recycle` — the literal truth there, nothing was made
    durable because nothing needed to be.
  - **BROKEN SITES: 14 measured, 14 actual** — ProofBeginOp 4 (3 rebuilds +
    the one site that restates `log_res`'s body verbatim), ProofEndOp 5,
    ProofLogWrite 3, ProofInitlog 1, ProofSysSync 0 (both its openers and
    its rebuild survived, as predicted).  Every one was `& #Hbank &` in the
    pattern and one `iSplitR; [iExact "Hbank"|]` in the rebuild.
  - **THE PAYOFF, PROVED.**  `LogInv.log_res_flushed` /
    `SpecSysSyncFlush.flushed_sync_of_res`: with the "log" lock held and the
    caller's `log_epoch_lb γ e`, `log_res` yields `flushed_sync γ e` and
    closes UNCHANGED (everything handed out is persistent).  That is item
    (iii) in one lemma.  And the FULL SEAL closed:
    `ProofSysSync.SysSyncProof` now implements `SYS_SYNC_FLUSH` and
    `LinkSysSync` derives the landed `SYS_SYNC` from it through the already-
    proved `SysSyncFlushWeaken`, so R10's "the postcondition only grows"
    stayed a theorem rather than becoming an edit.
  - **THE SECOND DEBT TURNED OUT NOT TO BIND, and this is the finding worth
    keeping.**  The `ncommit`↔epoch tie is still absent — `log_res` binds
    the cell existentially, the wait loop carries no `nc` binder, the back
    edge is still a raw case split — and the contract does not need it.  The
    post asks for a bank at some `e' ≥ e`, not for a strict increase, so the
    receipt can be minted ONCE at the FIRST acquire and ride the
    intuitionistic context through the guard, the Löb-closed loop and out at
    the tail.  The walk is the landed one instruction for instruction.  The
    tie would only be needed by a contract claiming the WAIT ended at a
    later batch — which §5's own argument says would be unprovable on the
    fast path and would make no consumer stronger.

  <details><summary>as landed 2026-08-28 (the machinery, before the
  banking)</summary>

  **AS LANDED 2026-08-28 — the machinery, the composition and the
  contract; what is left is ONE OWNER DECISION and the wait loop.**  Two
  new leaf files, both green on the mirror, every artifact `Closed under
  the global context`, nothing else in the tree touched:

  - **`iris/FsFlushed.v` — the receipt.**  `flushed_at γs b D :=
    ∃ l, ⌜length l = b⌝ ∗ fs_hist_lb (fcn_hist γs) (l ++ [D])`, and the
    client-facing `flushed b D` with `γs` closed under
    `fs_receipt_any`'s three seam equations.  **NO NEW GHOST, NO NEW
    INVARIANT, NO ARITY MOVED.**  The finding that decided the shape:
    *there is no numeric durable-epoch pointer in the tree and there
    cannot cheaply be one* — the epoch is `FsDurSnap.P_dur`, whose gname
    family is existential and which is indexed BY THE COMMITTED MAP
    ALONE; a commit drops it and allocates a fresh one
    (`dsnap_step_xfer`), so nothing of an epoch survives to be compared.
    What does survive is the crash record's mono-list `fcn_hist`, and it
    is already a commit counter with its values attached: the index IS
    `length l`, which `fs_receipt` merely existentially closes.  So the
    "commit counter for the receipt `ProofEndOp.v:1783` drops" is not a
    new counter at all — it is a projection of the receipt the committer
    already holds.  Proven: persistence, `flushed_at_agree` (one bound,
    one disk — from `mono_list_lb_op_valid_L`, no authority needed),
    `flushed_at_earlier` (monotone, and the earlier map is the history's
    own entry), `P_fs_flushed_lookup` (a receipt's index is its POSITION
    in the record's history — `P_fs_receipt_committed` sharpened), and
    the producer `P_fs_flushed_now`: whenever the crash predicate is
    open it hands out its current commit's receipt plus `snap_holds`,
    non-destructively.
  - **the composition (same file, §3), the acceptance test.**  `dur_at b
    D i n := flushed b D ∗ ⌜snap_holds D⌝ ∗ ⌜FsDurSyscall.dur_node D i
    n⌝` — the worklist's promised shape, with NOTHING in FsDurSyscall
    moving.  Mint (`dur_at_of_rec`, off the bytes a transaction left in
    the inum's slot; `dur_at_of_snap`), read (`dur_at_node`), agreement
    (`dur_at_agree`), the cross-node conjunction at one bound
    (`dur_at_pair` — doc §5's "two carriers, same b"), the end-to-end
    `dur_at_of_crash` from `P_fs` alone, and a non-vacuity witness.
  - **`iris/SpecSysSyncFlush.v` — the R10 parallel contract.**
    `SpecSysSync.v` is byte-identical.  The new body is the landed one
    plus `log_epoch_lb γ e` in (the caller's invocation-time batch
    witness — free, `sync_witness_0`) and `flushed_sync γ e` out.
    `SysSyncFlushWeaken : SYS_SYNC_FLUSH -> SYS_SYNC` is PROVED, so
    "the postcondition only grows" is now a theorem and arm 22 of the
    dispatcher keeps its contract.  `flushed_sync_of_bank` discharges
    BOTH arms of the fast/slow case split at once.
  - **THE OWNER DECISION, and it is the only thing between this and a
    proof.**  The receipt has no producer a client can reach:
    `P_fs_flushed_now` needs the crash predicate OPEN, which is the
    commit's fupd and nothing else — sys_sync writes no disk block.  The
    committer must BANK the receipt it currently drops, as one conjunct
    of `LogInv.log_res` (`SpecSysSyncFlush.log_flushed_bank`, spelled
    there as a type-checked definition), deposited at the same
    re-deposit that runs `log_epoch_bump`.  Measured cost: it changes NO
    arity (`log_ctx`, `wp_end_op`, `log_names` all stand) but it
    re-elaborates `LogInv.v` and hence the whole tree, and it breaks
    ~14 positional sites in `ProofBeginOp` (4, one of which restates
    `log_res`'s body verbatim), `ProofEndOp` (5), `ProofLogWrite` (3),
    `ProofInitlog` (1); `ProofSysSync`'s own three openers survive
    (they close with `iExact "Hrest"`).
  - **THE SECOND DEBT, smaller, and only the SLOW path needs it.**
    `log_res` binds the `log.ncommit` cell existentially and says
    nothing about its value, so `ProofSysSync`'s wait loop carries no
    `nc` binder and its back edge is a raw case split.  Proving that the
    WAIT ends at a later batch needs the cell tied to `ln_ep`
    (`⌜uint nc = Z.of_nat E⌝` or its off-by-one) and the loop invariant
    restated over the tie.  The fast path needs neither.
  - **Why the post is not `S e`.**  On the fast path no commit occurs,
    and a caller whose witness was taken in the current batch finds the
    log empty exactly when that batch is empty; demanding `S e` would
    make the contract unprovable there without making any consumer
    stronger.  The receipt is what consumers use.  (This turned out to be
    the load-bearing decision: it is exactly why the banking's seal did not
    need the wait loop's counter tie.)

  </details>

- [x] **FILEWRITE-CONS — the console-write syscall seal, CLOSED.**  DONE
  2026-08-29 (Opus lane; three new files, all EC2-green at 523cc4e8, zero
  `Admitted`, and the audit is **THE STANDING THREE and nothing else** —
  `xv6iris_extras.resv_matches`, `xv6iris_extras.resv_is_valid`,
  `functional_extensionality_dep` — machine-checked on both
  `FilewriteCons.wp_filewrite_cons` and
  `SysWriteConsAU.wp_sys_write_cons_au`).  init.c's printf path is proved
  end to end: `write(1, buf, n)` on the descriptor `mknod("console",1,1)`
  installed returns `SpecSysWriteConsAU.write_cons_arms`, i.e. the count IS
  the UART's accepted-byte receipt (or filewrite's own sign guard's −1).
  - `iris/ProofFilewriteCons.v` (~940 lines) — SEALS
    `SpecFilewriteCons.FILEWRITE_CONS`.  A copy-adapt of
    `ProofFilewrite.v`'s walk at `st = FdOpen rb true (FdDevice ma)`,
    `ma = CONSOLE`.  **THE WHOLE DIFF IS SUBTRACTION: five branches the
    landed walk PROVES are here REFUTED from the premises**, before the
    branch instruction is applied — +0x04 the `f->writable == 0` early
    return (`fdstate_ok` ties the byte the `lbu` read to the state's mode
    bit); +0x28 FD_PIPE and +0x2e the FD_INODE/panic fall (`fdstate_ok`
    pins `fc_type Cf = FD_DEVICE`, which is why the FD_INODE loop,
    `SpecPanic` and seven of the landed functor's eight arguments leave the
    file); +0x70 the out-of-range major's −1 (`CONSOLE` is 1, the test is
    `9 < major`); +0x82 the null-`devsw`-slot −1 (the contract's
    `fwn_wp fn ma = consolewrite` makes `filewrite_dev_env`'s honest
    disjunction one-sided; `Hwp` is never consulted).  What survives is the
    sign guard at +0x1c/+0x20 — the NEG arm, and the only −1 this contract
    admits — and the call.
  - THE LOCATED WALK'S CALL LANDS AT THE `c.jalr a5` AT **+0x86** (the
    `c.li a0,1` at +0x84 is unchanged): `ConsolewriteLoc` in place of the
    landed `Consolewrite`, same binders in the same order plus `tr0` and
    the seed `uart_sent fsc_uart tr0` in, `cons_sent_cnt fsc_uart tr0 r`
    out.  The FD_DEVICE arm relays `r` untouched, so at the exit the three
    bridge lemmas at the bottom of `SpecFilewriteCons.v` do the whole
    count-to-arms step in ONE line —
    `write_cons_arms_of_cnt fsc_uart tr0 n r Hn0 Hrn` — with `Hn0` the sign
    guard's fall-through and `Hrn` the callee's own range fact after
    `Z.max 0 n` collapses at `0 <= n`.  (`wcons_ok_of_cnt` /
    `wcons_short_of_cnt` are consumed inside it; the walk never needs to
    know which of `r = n` / `r < n` it got.)
  - `iris/LinkFilewriteCons.v` / `iris/LinkSysWriteConsAU.v` — the
    instances.  `FilewriteConsProof` takes ONE argument where
    `FilewriteProof` takes eight; `SysWriteConsAUProof` gets the landed
    `Argaddr`/`Argint`/`Argfd` plus it.
  - AS-LANDED NOTES.  (1) `FilewriteProof` is sealed with `: FILEWRITE`, so
    its four `Local Lemma` environment bridges are unreachable —
    `fw_dev_in`/`fw_dev_in_back` are restated keyed on the MAJOR (this
    contract names it) and `fw_env_dev`/`fw_env_out_dev` shrink to
    `intros ->; iIntros "$"`, because a pinned `st` makes
    `filewrite_env`'s match iota-reduce.  Seven pure preamble facts
    (`fw_K12`, `fw_av_cons`, `fw_n_range`, `fw_uint_moi`,
    `fw_major_range`, `fw_bltu9_false`, `fw_ret_pc_cons`) are restated as
    `fwc_*` rather than imported — the tree does not `Require Import` a
    proof file, and the alternative is a 4,400-line dependency for 20
    lines.  (2) The `uptd_ext_sz` continuation forms were already migrated
    into both contracts by the coordinator; nothing here moved them.
    (3) `SpecFilewriteCons.v` is BYTE-IDENTICAL (R10): its shape had
    already been validated by the syscall seal above it, and it needed no
    edit to be provable.

- [ ] **INIT — the init.c program theorem (three stages; scoped
  2026-08-29 after upstream's echo landed the Uk pattern).**
  STAGE 1 (bare tier, echo's mold, launchable): `UkInit.v` — init's
  text as U-mode continuations over key facts (`init_text_sub M`,
  X-page, stack budget; no uk_args); preamble syscalls are QUIET rows;
  the argv-for-exec stores via UkStore; TWO in-lane verifications that
  are the only possible blockers: do `usys_mem_ok` rows exist for
  SYS_fork/SYS_exec/SYS_wait (echo exercised only write/sync/exit —
  if absent, stop at the loop head and report: small upstream rows),
  and the forever-loop's round/iLöb discipline (the one structural
  novelty vs echo's bounded inductions; J's scheduler rounds are the
  expected precedent).
  STAGE 2 (functional preamble — fds 0-2 = console): OUR sealed AU
  receipts (mknod/open/dup) under the ecall ∀ via the Φ REFINEMENT
  PARKED in user-wp-slot's design (UkEcho's header names it; this
  stage is its first real consumer — CROSS-CAMPAIGN ASK, raised
  here: the receipts are ready on our side).
  STAGE 3 (the child runs sh): J's `cond_entry_slot` mint consumes
  `SpecKexecPin.Q_pin` (seam drawn in that file's header); needs the
  pinned-exec PROVER (ELF-header step; owner Qs: oracle widening,
  image-hole sweep timing) and, for the segments, the image-hole
  widening.
  Dependency truth: stage 1 blocks on nothing of ours; stage 2 on
  upstream's Φ; stage 3 on our exec prover + two owner rulings.
  STAGE 1 AS-LANDED (2026-08-29, `iris/UkInit.v`, 1520 lines, audit =
  the standing three): start→main through the WHOLE preamble proven —
  both open arms, the mknod repair arm, both dups — stopping at the
  printf call (0x32); the complete syscall-stub surface proven
  independently (quiet ×3, exit, FORK = a separating conjunction —
  parent AND child continuations owed, exec = the −1 arm only with
  success being stage 3's mint, wait, jr).  Q1: ALL rows exist (wait
  is syscall 3; fork is uexec_ret_F's own arm, not usys_mem_ok's).
  Q2: the unbounded-loop discipline is UkBranch's `_later` leaves —
  no J machinery needed.  Q3 (UNASKED, THE BLOCKER — CROSS-CAMPAIGN
  ASK #2, beside the Φ refinement): `usys_window 3`'s row at
  wait((int*)0) permits M' to differ over [0,d) — init's own TEXT —
  so the loop invariant cannot re-establish; code-impossible (the C
  guards addr != 0).  Minimal fix in SpecSyscall.sysc_mem_ok /
  UsysMemOk.usys_mem_ok's window arm: a `decide (arg = 0)` null
  disjunct with M' = M; weakens no caller; kernel discharge = the
  existing short-circuit.  UPSTREAM'S CONTRACT — their call.
  Remaining for a full stage 1: the printf walk (~280 instructions,
  the old tier's 2925-line file) and, after the wait fix, the loop
  closure via the proven `_later` shape.  Scoping corrections: no
  argv stores (static global in .data); no uk_args (verified).
  STAGE 1 COMPLETE (2026-08-30, `iris/UkInitPrintf.v` 3249 lines +
  `iris/UkInitLoop.v` 1020 lines, audit = the standing three, zero
  `Admitted`).  The printf walk landed as printf → vprintf → putc →
  write (write is a fourth QUIET-row instantiation of
  `wp_kinit_qstub`), and the ~180-instruction %-conversion tree is
  REFUTED, not proved: vprintf's percent-pending register `s3` is
  written only at 0x538 and 0x538 is reached only on a percent byte,
  which init's literal has none of, so 0x516 and 0x53c..0x794 (212
  instructions) are unreachable for this call — decided by
  `uki_lit_ok`, one `vm_compute` per literal.  The scan is a bounded
  Rocq induction (echo's strlen mold), NOT an iLöb.  The loop walk
  closed BOTH heads (0x32 and 0x44) under ONE iLöb over their
  conjunction (`∧`, so both branch arms may use all of it), one
  `_later` leaf per cycle; fork's BOTH continuations paid, exec's −1
  arm consumed, and the three printf+exit arms stated once
  (`wp_kinit_die`).  `uki_loop_head` is DISCHARGED; what is left of
  stage 1 is the single Prop `uki_wait_ok` — Q3's blocker, restated
  minimally as "a window written at address 0 leaves `init_text_sub`
  and `init_data_sub` standing".  It is FALSE of the row as written
  (it quantifies over every `d`), so `wp_kinit_start_full` and the two
  lemmas above it are TODAY VACUOUS and say so in their header;
  everything below them is unconditional.  Upstream's fix makes the
  closure `intros M d bs Ht Hd; split; assumption` — one lemma, no new
  induction.  One deliberate change to `UkInit.v` (R10 waived by the
  lane brief): `uki_loop_head` now carries `init_data_sub` beside
  `init_text_sub`, and the two entry theorems a frame-above-image
  inequality, because vprintf LOADS the .rodata literal's bytes.

- [ ] **SH — the sh.c program theorem on the urun engine (six stages;
  opened 2026-08-30).  Upstream owns the INIT port; this lane owns sh.**

  **STAGE 0 — THE INVENTORY, and the two corrections it forces.**

  (a) *There is already a COMPLETE first-generation sh program proof, and
  it is ON-BUILD.*  Not three files — **eleven**: `UProofShLib` (2107),
  `ShMem` (1814), `ShHeap` (4061), `ShLex` (5651), `ShIo` (3692),
  `ShInput` (158), `ShParse` (8996), `ShCmd` (3676), `ShTop` (1017),
  `ShMain` (1952), `ShEcho` (122) — ~33k lines, plus `UCodeSh.v` (10148)
  and the two statement files `USpecSh.v` / `USpecShParse.v`.  It closes
  end to end: `wp_sh_execs_echo` (`UProofShEcho.v`) says the shell, run on
  the input `echo Hello world!\n`, reaches an `exec` naming `echo` with
  argv `["echo";"Hello";"world!"]`.  Thirty functions covered, zero
  `Admitted`, zero `Axiom`; the only two `Hypothesis`es
  (`UProofShMain.Hparsecmd`, `UProofShCmd.Hparseline`) are cross-lane
  section hypotheses that `UProofShEcho.v` §1 discharges by application.
  Design of record: `claude-notes/completed/user-sh.md`.
  **So this lane is a PORT, not a first proof** — and R10 says the eleven
  files and their statements do not move.

  (b) *`ShLib`/`ShMem`/`ShHeap` are NOT tier-neutral pure layers.*  They
  are old-interface walks: measured by declaration, the engine fraction is
  **91.6% / 80.9% / 92.0%** and the pure remainder is 9 / 19 / 20 tiny
  shims (`bv8_zero`, `uM_bytes_4_of_8`, `heap_leaf`, register indices…).
  The genuinely portable material in the stack is elsewhere: all of
  `UProofShInput.v` (100% pure) and ~2 700 lines spread over the PURE
  columns of ShParse (735), ShLex (615), ShCmd (411), ShIo (309), ShMem
  (254) — plus **both `USpec*` files in full**, which hold every sh
  contract statement and were among the 18 rows that survived the last
  engine swap with zero edits.  `USpecShParse.sh_tokens`,
  `USpecSh.sh_exec_below`, `sh_skipws`/`sh_toklen`, `ustr_find`,
  `sh_gets_taken` and the `SH_*` address constants are the modelling work
  worth harvesting verbatim.  What does *not* port is the shape: every
  contract is `… -∗ WP (Loop …)` in CPS over `UmodeIo.xv6_io_protocol`,
  whose eleven `Io*` arms are **assumptions about the kernel** (fork never
  fails, open returns ≥3, exec never returns, sbrk never grows `pt`,
  `wait` only at a null status, `write` forgets what it wrote).  The port's
  content job is replacing each such conjunct with the real
  `UsysMemOk.usys_mem_ok` row — per arm, not a rewrite.

  (c) *The syscall-row coverage sh needs* (`UsysMemOk.usys_mem_ok`,
  c27e0e839; kernel twin `SpecSyscall.sysc_mem_ok`, bridge
  `UsysMemOkSpec.v`; no axiom, no `Admitted` anywhere in them):

  | row | # | exists? | what it gives sh |
  |---|---|---|---|
  | open | 15 | quiet | `M'=M, π'=π, sz'=sz` — **stage 1 uses it** |
  | close | 21 | quiet | ditto — **stage 1 uses it** |
  | exit | 2 | dedicated arm in `UexecRet.uexec_ret_F` = `emp` | **stage 1 uses it** |
  | write | 16 | quiet | echo already consumes it |
  | chdir | 9 | quiet | `cd` builtin, stage 2 |
  | dup | 10 | quiet | PIPE arm, stage 5 |
  | read | 5 | **window**: `∃ d ≤ max 0 (arg2), M' = umem_wr M arg1 d bs` | `gets`, stage 2 |
  | wait | 3 | **window**: `∃ d ≤ 4`, **plus** `arg0 = 0 → d = 0` (9dc84f919) | `wait(0)`, stage 2 |
  | pipe | 4 | **window**: `∃ d ≤ 8` at arg0, **no null guard** | PIPE arm, stage 5 |
  | fork | 1 | dedicated arm: a **separating conjunction** — parent AND child continuations owed | `fork1`, stage 4 |
  | exec | 7 | user side = the **−1 arm only** (`r = −1`, image intact); success has no row by design | `execcmd`, stage 6 |

  Every row sh needs EXISTS.  **What is missing is the consumer side**:
  `UkRunSys.v` has exactly two ecall leaves, `wp_uk_ecall_quiet` and
  `wp_uk_ecall_exit`, and its own header says the WINDOW row and the SBRK
  row are "not yet built".  There is no `wp_uk_ecall_fork` either.  Those
  three leaves are stage 2/3/4's first task — see the asks below.

  (d) *Assets that plug in unchanged.*  `FsShPin.v` (sh at inode 13,
  `sh_bytes = ElfUser.sh_elf`, 58 312 bytes — matching `ShElfRaw`
  exactly); the sealed syscall AU theorems (sh's KERNEL-side story is
  done; this lane is the USER-side walk); `UexecCond.cond_entry_slot`, to
  which adding sh is literally one more `destruct (decide (sh_gate W))`
  once the walk is unconditional.  The parked `UkInit*.v` files are the
  molds for the shapes stage 4 needs (fork's two continuations, the dying
  arms, the double-headed loop iLöb) but are stale against the current
  engine — read them, do not import them.

  **STAGE 1 AS LANDED (2026-08-30; `iris/UCodeShK.v` 2104 lines,
  `iris/UkRunBr.v` 110, `iris/UkSh.v` 640; audit = the standing three
  (`resv_matches`, `resv_is_valid`, funext), zero `Admitted`).**
  start → main's prologue → main's CONSOLE PREAMBLE, closed, stopping at
  the command loop's head 0x914.
  * **The catalog had to be regenerated, and could not reuse the name.**
    `UCodeSh.v` emits `uinstr` facts (page-table indexed) and the urun
    leaves take `UserHeap.uinstr_is` (a separation-logic resource naming
    no page table).  `tools/gen_ucode.py` already emits the new form, but
    its `--prog` flag — the one that would let a second catalog over the
    same dump avoid colliding with the first — was **broken**: five emit
    sites spelled the dump maps `<M>Instrs.<prog>_bytes` instead of
    `<M>Instrs.<prefix>_bytes`.  Fixed here (5 lines, plus the geometry
    scalars, which read `<prog>Entry` and silently printed 0).
    `tools/ucode_shk.txt` is the new pc spec and grows per stage.
  * **Compile-time finding: the catalog does not scale to all of sh.**
    91 instructions cost **3 m 20 s**; `ucode_sh.txt`'s 1032 would be
    ~11× that, far past the per-file budget.  The catalog must be SPLIT
    per stage (or per function group) before the parser lands.
  * **Two engine leaves were missing, and both are UkRunLeaf's.**
    `wp_uk_btype0` — the base branch against x0 (`bltz`/`bgez`/…): the
    value of x0 is not readable off the register file, so `wp_uk_btype`'s
    premise is undischargeable, and echo/sync never hit it.
    `wp_uk_btype_later` — every leaf in `UkRunLeaf.v` is later-FREE, which
    is right for a bounded Rocq induction (echo's two scans) and leaves an
    UNBOUNDED loop unprovable, since an `iLöb` hypothesis is `□ ▷ …`.
    Both are six-line re-threads of leaves `UkBranch.v` already has; they
    are in `UkRunBr.v` only because UkRunLeaf.v is not this lane's file.
  * **The first unbounded loop on urun, and its invariant is EMPTY.**
    `while ((fd = open("console", O_RDWR)) >= 0) if (fd >= 3) { close(fd);
    break; }` — 0x900..0x910, back edge `bge s1,a0,0x900` at 0x90c.  One
    `iLöb`; the two branches are taken on the ABSTRACT `uv_btaken …`
    boolean and case-split, so the walk never computes what fd the kernel
    returned and carries nothing round the cycle but `urun … 0x900 n`
    itself.  90 lines, not 900.  **This is the shape stage 2 should try
    first on the command loop**, whose real invariant is the buffer's.
  * `wp_ksh_qstub` states usys.S's whole stub shape (`c.li a7,n; ecall;
    c.jr ra`) once, at any quiet-row number; open and close are two-line
    instances and stage 2's chdir/dup/write are three more.
  * The single Prop `ush_cmd_head` — "0x914 is safe at ANY register file"
    — is the stage boundary.  ∀-over-`m` is honest: main never returns, so
    the eight words its prologue spilled are dropped here and no epilogue
    pc is reachable, and 0x914..0x926 rewrites every register the loop
    reads.  Everything below it in the file is unconditional.

  **THE PLAN (stages 2–6).**
  * **STAGE 2 — the command loop's head, and the READ window.**  `getcmd`
    (0x0, 29 instrs) → `write(2,"$ ",2)` (quiet) + `memset` (0xa5c, 16) +
    `gets` (0xaaa, 50) → `read(0,&c,1)`, plus main's blank-line arm
    (`while (*cmd==' '||*cmd=='\t') cmd++;  if (*cmd=='\n') continue;`) and
    the outer `while (getcmd(...) >= 0)` back edge to 0x938 — a second
    iLöb, at the head that matters.  Discharges `ush_cmd_head`.
    **Blocked on one leaf**: `wp_uk_ecall_window`, the read row's consumer.
    Its statement is forced — the caller hands over `ubytes γd a k f` for
    the buffer it named in a1 with `k ≥ count`, and gets back
    `∃ d ≤ count, ubytes γd a k g` with `g` agreeing with `f` above `d`;
    the re-assembly primitive already exists and is
    `UserHeap.uheap_store_run`.  ASK below.
  * **STAGE 3 — the allocator.**  `malloc` (0x118c, 91) → `morecore` →
    `sbrk` (0xc52, 10) → `sys_sbrk` (0xd0e), and `free` (0x1106, 46).  The
    first call is the only one the old stack proved (`freep == 0`), and
    that scoping carries.  **Blocked on `wp_uk_ecall_sbrk`**, the second
    unbuilt row — and this one moves `π` and `sz`, so it is strictly
    harder than the window.  `USpecSh`'s `sh_nunits`, `SH_FREEP`,
    `SH_BASE` and `UProofShMem`'s `heap_leaf`/`data_leaf` port.
  * **STAGE 4 — the parser's recursion.**  `parsecmd` (0x86e) →
    `parseline` (0x6e2) → `parsepipe` (0x682) → `parseexec` (0x590) →
    `parseredirs` (0x4ac), over `peek` (0x448) / `gettoken` (0x310) /
    `strchr` (0xa82) / `nulterminate` (0x7ee).  ~500 instructions, the
    lane's bulk.  The recursion is bounded by the input LINE, and
    `USpecShParse.sh_tokens` is already the right induction — it is
    defined in the exact shape `parseexec`'s arg loop runs, so the loop
    invariant is one constructor.  Harvest `USpecShParse.v` verbatim; the
    three-level shared postcondition (`wp_sh_parse_body entry budget`,
    instantiated at parseexec/parsepipe/parseline) is the economy to keep.
    `nulterminate`'s jump table is the one novelty (a computed control
    transfer) and the old `UProofShCmd.nt_mem` model ports.
    Catalog: split it — see the compile-time finding.
  * **STAGE 5 — `runcmd`'s tree walk.**  0x8e, 102 instructions, five arms
    off the 0x1398 jump table.  EXEC needs the exec −1 arm plus, for
    success, the pinned-exec prover (lane X's `SpecKexecPin.Q_pin`) —
    that is the same seam init's stage 3 sits on.  LIST and BACK need
    `fork`'s TWO continuations (`uexec_ret_F`'s separating conjunction —
    a `wp_uk_ecall_fork` leaf, third unbuilt).  REDIR needs open/close
    (have them).  PIPE needs `pipe`'s window row + `dup` (quiet) — and
    note the pipe row has **no null guard**, unlike wait's; if `p` can be
    argued non-null from the code the row still permits a write at 0, so
    this may become a fourth upstream contract ask.  `fork1`'s
    `panic("fork")` arm and every `fprintf` diagnostic are REFUTABLE the
    way UkInitPrintf refuted init's %-tree, or scoped out the way
    `ucode_sh.txt` scoped them out; decide once, at the top.
  * **STAGE 6 — the top theorem, stated honestly.**  The first-generation
    statement is the target shape and the ceiling: `wp_sh_execs_echo` says
    *on one fixed input*, the shell reaches `exec` naming the right path
    and argv.  It is fixed-input for a recorded reason — parametric in the
    input it is not merely unproven but not a theorem, because nothing
    bounds the loop.  The honest urun form is therefore **per accepted
    command line**: "given `ustdin`-equivalent ownership of a line the
    lexer accepts, sh's next `exec` names the tokens of that line" — one
    line, then the loop's iLöb re-enters at the head.  Functional content
    rides the same Φ-refinement seam as init's stage 2 (UkEcho's header
    names it) unless the entry chain's gate provides more.  Only when the
    walk is unconditional does sh join `UexecCond.cond_entry_slot`: one
    `destruct (decide (sh_gate W))` plus a `UShKernel.sh_uexec_slot` built
    from `uslot_of_urun` at sh's stack budget (the old tier measured the
    deepest chain at 560 bytes, i.e. 70 words) — and sh needs NO
    `uk_args_c` (it takes no argv), so its gate is sync's six conditions
    at sh's text and entry pc, not echo's nine.

  **ASKS (relay, in priority order).**
  1. **`wp_uk_ecall_window` in `UkRunSys.v`** — blocks stage 2 and every
     stage above it, and blocks upstream's init port at exactly the same
     place (`wait((int*)0)`).  Owner question: ours or upstream's?  The
     row and the re-assembly lemma both exist; this is the leaf.
  2. **`wp_uk_ecall_fork`** (the two-continuation arm) and
     **`wp_uk_ecall_sbrk`** — stages 3–5.
  3. **Relocate `UkRunBr.v`'s two leaves into `UkRunLeaf.v`.**
  4. **`pipe`'s row has no null guard** while `wait`'s now does — the
     same defect 9dc84f919 fixed, one row over.  Upstream's contract.
  5. **The eleven first-generation `UProofSh*.v` files.**  Precedent says
     the old proofs are DELETED when a program is ported (4f088971f did
     exactly that for sync).  That is 33k green lines and a closed
     theorem; deleting them is a coordinator/owner call, not this lane's.
     Until it is made, both catalogs stay on-build and the port carries
     the `shk_` prefix.

## RULING BRIEFS (drafted 2026-08-30, coordinator; each is a yes/no)

- [ ] **RULING A — the copyin content seam.**  THE GAP: `either_copyin`'s
  success arm binds the copied bytes existentially, so write's receipts
  say "SOME bytes of the right length landed" and console-write's say
  "length and order" — never "MY bytes."  THE ASK: an output equation on
  the success arm tying the copied run to the USER SOURCE bytes at the
  instant's `M` (the vocabulary exists post-M-threading: copyinstr's
  same-M contracts are the precedent).  THE COST, honestly: it is a
  `SpecWritei`-class ripple — the equation must relay
  either_copyin → writei → filewrite → the syscall arms (and the
  console chain separately), i.e. one output conjunct each on two or
  three landed contracts with their proofs re-elaborated; the write
  precedent measured that class at zero proof content + a relay through
  3 signatures + a handful of caller sites, but writei's is the tree's
  big proof, so budget a full lane.  THE PAYOFF: "printf printed MY
  bytes" and write's content-pinned receipts, in one ruling — the last
  honesty gap in the write family.  RECOMMEND: YES, as a lane when the
  current pair lands.
- [ ] **RULING B — the A(iv) offset carrier.**  THE GAP: `f->off` lives
  behind `file_pay`'s existential, so write/read receipts carry
  per-instant existential offsets and dup's same-description fact stops
  at the array cell.  THE OPTIONS: (a) a two-halves offset ghost keyed
  on the struct-file SLOT (per description, shared by dup'd fds — the
  `fdstate` two-halves pattern at the ftable: auth beside `file_ref`,
  optional client half; movers = the two `f->off` advances in
  fileread/filewrite), the d1411776 precedent one field further; (b)
  status quo (existential offsets; single-threaded consumers re-derive
  positions from their own receipts' lengths — workable, forever
  slightly dishonest about sequencing).  THE COST of (a): one new
  two-halves ghost + threading at exactly two mover sites + the
  carve/settle plumbing — the fd-state landing's scale (~30 files
  touched upstream when fdstate landed).  CONSUMERS WAITING: write,
  read, dup, and any future lseek.  RECOMMEND: (a) YES but AFTER
  ruling A's lane (they touch the same file-layer proofs; sequencing
  them avoids a double re-elaboration).

Sizing: D is spike-sized — the readings exist, the work is assembly and
statement.  S0 is one design session.  A and W are the campaign's bulk.
P is contained (two pins).  Y is CLOSED (2026-08-29): machinery, contract,
banking and seal.


---

## Lane X (PINNED-EXEC PROVER) — landed 2026-08-30, with ONE owner question

Files: `iris/ProofKexecPinTrace.v`, `ProofKexecPinA.v`, `ProofKexecPin.v`,
`LinkKexecPin.v`; plus the seam widening inside `ProofKexecA.v` /
`ProofKexec.v`.  `SpecKexec.v`, `KexecOkQ.v` and `SpecKexecPin.v` are
byte-identical (R10) — the widening lives entirely below the seal.

**What is proven.**  `SpecKexecPin` §8's (1), (2), (3) and (5).  The paying
site is `kxc_cd`'s `Q (kxq_entry ef)`, discharged by `Q_pin_of_hdr` at
`HD := Some (kxp_ef pb)`, `XCH := ⌜False⌝`; the other thirty-one relays
carry the `Q` opaquely and needed no restatement (verified by the first
compile).  Phase A is copied (`kxc_a1p` / `kxc_phaseAp`) because the landed
one calls the *traceless* namei; every other block is the landed one,
instantiated.  Audit: the platform's `resv` pair plus funext.  Zero
`Admitted`.

**The oracle seam (§8 (2)), measured.**  Route (a) — widen ProofKexecA's
oracle premise to carry the payload's era leg (`top_frag`) and its
`inode_ok` beside the `fv_ride` — is **+64/−21 lines across two files** and
one full-tree `make` (green).  Route (b), a pinned `kxc_a2` copy, is
**~920 lines** duplicated (`kxc_a2` + `kxc_a2_exit1`) and forces a parallel
`kxc_phaseA` regardless.  (a) taken.  The ride alone genuinely cannot answer
a pinned verdict: the fv ghost has no tie to γ-top outside the payload, and
the era leg is what lets the abstract row be read off the authority.

**THE OWNER QUESTION (§8 (3)'s premise, not its proof).**
`kxp_view_pin` re-reads `kxp_pins` at every instant, and `kxp_pins` pins the
two ENDPOINTS.  On a path of two or more elements that is not enough, and
the contract's sentence is **false**, not merely unproven: between hop *k*
and hop *k+1* a writer may re-point the root's `"a"` at a fresh directory
whose `"b"` is the pinned inum and leave the stale `d`'s `"b"` pointing at
junk — every instant still satisfies `kxp_pins`, and the walk answers junk.
No cursor definable from `kxp_pins` rules this out (the invariant a hop can
carry forward must hold at *every* pin-satisfying view, and "d is the k-th
inum" does not).

*The repair is one conjunct and it is already written upstream.*  What pins
a walk is the CHAIN at a fixed `ds` — `FsAbs.arun av ROOTINO ps ds` — and
`FsInitPinBoot.era0_pins` and `FsShPin.era0_sh_pins` BOTH carry exactly that
conjunct today; `SpecKexecPin` §5a discards it (`intros (Hp & Hc & _)`).  So:
give `kx_pin` a `kxp_chain` field (or `kxp_pins` a third conjunct) and both
era-0 instances discharge it for free.

**Nothing is blocked meanwhile.**  `ProofKexecPin.wp_kexec_pinned_run` proves
the body at the honest premise (`kxp_run_pin`, the drop-in the statement lane
can lift verbatim), and `wp_kexec_pinned_1hop` derives `SpecKexecPin`'s OWN
body — the Module Type's sentence, quoted — for every one-element path.
`init_path = ["init"]` and `sh_path = ["sh"]`, so /init and sh are covered
and Milestone J's `cond_entry_slot` mint can consume `Q_pin` today.
`KEXEC_PIN` itself is left UNSEALED deliberately: sealing it would require
proving the multi-hop arm, which is false.

## Lane C (CONSOLE TRACE CONNECTION) — landed 2026-08-30, with ONE upstream ask

Files: `iris/UartAccepted.v` (pure leaf, beside `ObsTrace.v`),
`iris/UartSentResidue.v` (Iris, above `UartSentLoc`),
`iris/SystemUartAccepted.v` (the export, above `SystemAdequacy`).  Nothing
of `claude-notes/projects/uart-trace.md`'s phases 1–4 was touched (R10):
all three files are new leaves.

**THE TIE (`UartAccepted.run_out_accepted`).**  For every run of the machine
from a powered-off, never-booted state,

```
obs_wire (open_seg κs)  `sublist_of`  uart_acc (duart (gdev g2))
```

— every `ObsUartOut` byte of the current power cycle is a byte the kernel
ACCEPTED into the UART, in order, and nothing else is on the wire.
`uart_acc` is exactly the list `WpUart.uart_sent` / `UartSentLoc.
uart_sent_from` are lower bounds of, so this is the sentence that turns a
console receipt into a statement about what the host saw.

It is PURE — no Iris, no ledger.  The carrier is a new device invariant,
`out_wire_ok u := u_wire u ⊑ u_out u`, proved a step invariant of
`prim_step` in the shape of `ObsTrace.prim_step_obs_wf`
(`prim_step_gout_wire_ok`, conditioned on `gpow` and re-established at
PowerOn from `boot_facts`' `duart = uart0_state`).  Sublist and not prefix
because a byte can be accepted and never sent: LOOP diverts it to this
UART's own receiver, an FCR clear drops the tx FIFO, and a power loss ends
the cycle.  The statement is about a REACHED STATE, so it holds at every
point of every run (every prefix of an `nsteps` is an `nsteps`) — which is
how the completed cycles are covered, each while it was the open one.

**THE EXPORT (`SystemUartAccepted.xv6_out_accepted_xv6Σ`).**  At the real
image: adequacy's reducibility, `ObsTrace.obs_wf κs g2`, and the tie, about
one run.  `xv6_out_accepted_from_xv6Σ` is the LOCATED reading: given a
receipt's pure residue at the reached state (`tr0` a prefix of `uart_acc`,
`bs` a sublist of `drop |tr0| uart_acc`), the cycle's output splits as
`w1 ++ w2` with `w1 ⊑ tr0` and `w2 ⊑ drop |tr0| uart_acc` — the same window
`bs` lives in.  Read for a printf: nothing the host sees after the printf's
starting point can be a byte that was not accepted after that point, and
outputs cannot outrun the acceptance order.  SAFETY ONLY (uart-trace.md
ruling 5): it does NOT say the printf's bytes appeared.

**Audit.**  `run_out_accepted` is on the platform's `resv` pair and NOTHING
ELSE (two axioms) -- no funext, no Rocq primitives: it is a theorem about
the semantics.  `uart_sent_from_acc` / `uart_sent_from_obs` are closed under
the global context (zero).  `xv6_out_accepted_xv6Σ` and
`xv6_out_accepted_from_xv6Σ` inherit the system theorem's standing set --
the `resv` pair, funext and the ten Rocq primitives, thirteen in all -- and
add nothing to it.  Zero `Admitted`; every file compiles in under three
seconds on the mirror.

**THE IRIS-TO-PURE STEP (`UartSentResidue.uart_sent_from_acc`).**
`uart_sent_from γu tr0 bs` agreed against `WpUart.uart_sent_auth γu u` IS
that residue; `uart_sent_from_obs` is the whole composition at one device
state, given the wire tie and `out_wire_ok`.  Both green.

**THE ASK (relay; it is uart-trace.md's open "identification gate" in its
UART instance — not a new item).**  To fire `uart_sent_from_obs` at a trace
EVENT, so that a receipt is exported without assuming its residue, the
ledger's per-event wands need two things they are not given:

1. **Era identity.**  `SystemAdequacy.xv6_power_adequacy_gen`'s permit
   premise is `forall γ : uart_names, ⊢ obs_inv -∗ uart_obs_permit γ`, and
   `xv6_trace_adequacy`'s `Htx`/`Hrx` likewise quantify over an arbitrary
   `γ`.  A client's `R` therefore cannot know the `γ` it is handed is the
   era's, and no ghost comparison recovers it (the wand holds `uart_ghosts
   γ u'`, the ledger would hold a lower bound at some `γ0`; nothing relates
   them).  The fix is the trace-side twin of `Hswap`'s `Rb dk`: the boot
   deposits the era's `γu` (a persistent registration) where the ledger can
   see it, and the permit premise is taken at the registered `γ`.
2. **The device invariant at the event.**  The wands get `⌜trace_shape h
   true⌝` and the wire tie but nothing about `u_out`.  The cheapest fix is a
   FOURTH conjunct on `ObsTrace.obs_wf` — `gpow g = true -> out_wire_ok
   (duart (gdev g))` — whose preservation proof is already green here
   (`UartAccepted.prim_step_gout_wire_ok`); `wp_uart_step` then hands it
   over beside the tie.

Neither is needed by what landed: the pure route proves the acceptance
content of the trace outright, and the ledger is only the vehicle for the
LOCATED, era-attached form.  Recorded here rather than in uart-trace.md so
the plan's own "Open" list is not duplicated.
