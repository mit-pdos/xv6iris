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
  REMAINING: unlink AU (wants the npar walk's contract shape), then
  open/read/close/fstat/chdir, mechanical.  NOTE (2026-08-27): the fd-state ghost
  landed upstream (`FdSlots.fd_frags` beside `ut_own`; `fdstate` =
  open-or-closed + `fdtype`, two-halves algebra, commits 28d707dc +
  3199a1b6; `FdInode` carries its INUM as of d1411776, riding on
  `file_ref`'s index) — the descriptor arms of these specs speak THAT
  carrier and can tie fd → inum → the §2 abstract node directly; the
  campaign does not mint its own fd ghost.
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
  MEASURED GOTCHA, recorded in optimization.md and in the file's §3
  header: `injection`/`exact` against an equation carrying the
  35,976-byte `init_elf` literal DOES NOT FINISH (>15 min, both
  spellings) — conversion unfolds `FsTree.file_bytes`, which is
  quadratic in the file size.  Prove `Some (NFile b) = Some (NFile b')
  -> b = b'` AT VARIABLES and close the instance by transitivity through
  `node_at`.  That one change took the file from >15 min to 5.5 s.
- [ ] **Y — sys_sync (gated on durable lane F).**  The `flushed`
  receipt (persistent snapshot certificate copy, plan 4⁹.3) + the
  `wp_sys_sync` parallel form (R10), per doc §5 principle 2's derivation
  chain — items (ii) and (iii); item (i) is DONE (the commit concludes
  something real).

Sizing: D is spike-sized — the readings exist, the work is assembly and
statement.  S0 is one design session.  A and W are the campaign's bulk.
P is contained (two pins).  Y is small once F lands.
