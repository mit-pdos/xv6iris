# Design: the FS block layer — the logged view, bio's client interface, log.c

STATUS: DESIGN, nothing landed. Worklist: [`../projects/fs-log.md`](../projects/fs-log.md).
Base layers this sits on: [`../completed/bio.md`](../completed/bio.md) (the
physical buffer cache — this design is the "bio_cell / coherent client view"
that file deferred), [`../completed/virtio-disk.md`](../completed/virtio-disk.md)
(the driver; **unchanged** by stages 1–3 below), and
[`crash.md`](crash.md) / [`../projects/crash.md`](../projects/crash.md) M5b
(the crash invariant `Pc` and the write-permit seam that stage 4 instantiates
as `P_fs`).

## The three states, and which function moves which

For the FS's block range (`fs_covered bno := 1 <= bno < FSSIZE`; block 0 is
deliberately excluded — binit leaves all 30 buffers with blockno 0, so 0 must
never be a client block), there are three block-content maps:

- **P — the physical disk** (`disk_block γd bno bs` fragments over `γdur`,
  the fixed-layer durable auth of M5). Home blocks + the log area
  (`logstart .. logstart+LOGBLOCKS`, header at `logstart`) + sb. Moves at
  every `bwrite` (DMA completion).
- **D — the durable / committed state**: what recovery would produce from P
  right now (home blocks, overlaid by the on-disk log iff the on-disk header
  says n > 0). **Strongly consistent**: changes ATOMICALLY at exactly one
  instant — `write_head`'s disk write when lh.n > 0 (the commit point) — and
  jumps from one committed state to the next. D is the crash-side state:
  stage 4 puts its auth inside `P_fs` (the `riscv_crash_pred` instance).
- **L — the logged / latest state** (NEW ghost, `γL`): D overlaid with every
  `log_write` of the current, still-open batch. This is what `bread` returns
  and `log_write` updates. Volatile (dies at crash — correct: uncommitted
  writes must vanish), and **not required to be FS-consistent mid-batch**:
  between a `begin_op` and the batch's last `end_op`, L is just bytes.

Plus the **cache overlay invariant** tying L to the machine:

- bno cached in buffer k, parked, clean: cache bytes = L(bno) = home disk
  content.
- bno cached, parked, dirty (logged, uncommitted or uninstalled): cache
  bytes = L(bno); home disk content stale; the buffer is PINNED (a `bref`
  exists), so it cannot be evicted.
- bno cached, checked out (sleeplock held): the holder owes brelse a
  consistent content (below).
- bno uncached: home disk content = L(bno). (Uncached ⇒ clean: every
  log_write pins its buffer, and bunpin happens only in install_trans after
  the home bwrite, so refcnt = 0 implies installed.)

## Why the bio specs must be revised (not just layered over)

1. **The mystery disjunct is unfixable from outside.** bread's post gives
   existential `bs_out` on a valid hit; only an invariant on the ESCROW's
   parked arm can tie a hit's bytes to anything, and the escrow is bio's.
2. **The caller-supplied exclusive `disk_block` is wrong.** Two concurrent
   `bread`s of the same block are legal and real (two `balloc`s scanning the
   same bitmap block; xv6 serializes them only on the buffer sleeplock
   itself), but two callers cannot both present the exclusive fragment. The
   fragment has to live INSIDE the bio machinery.
3. **Eviction/fill happen inside bread.** The overlay invariant's uncached
   arm is broken and re-established at bget's recycle and at the fill —
   both interior to bread — so the resources moving between "uncached pool"
   and "escrow" must be routed by bread's own proof.

## The ghost state

- **`γL : ghost_map Z (list (bv 8))`** — the logged view L. THE AUTH LIVES
  IN `log_res` (the log spinlock's resource, cmt=false arm). Each covered
  block's elem is split ½/½:
  - `fsblock bno bs := bno ↪[γL]{#½} bs` — the CLIENT half. Held by the
    layer above (inode/bitmap owners; for the log area, the header block and
    the sb: by the log layer itself, inside `log_res`). This is the
    FS-facing points-to for logical block content.
  - the MACHINERY half rides inside the bio layer (pool → escrow → handle),
    as the payload `Ψ` below. Two ½s agree with no auth in sight — that is
    bread's postcondition. Updating needs auth + both halves — that is what
    makes `log_write` (under log.lock) and the committer (who checks the
    auth out) THE ONLY writers of L. A client holding both halves still
    cannot move L: no auth. This freeze-by-auth is load-bearing: during
    commit the committer owns the auth outright, so L is frozen and
    "log slot i contains L(W[i])" survives from write_log to install_trans
    with no extra ghost.
- **`γown : ghost_map Z unit`** — the EXCLUSIVE per-block ownership token,
  `blk_own γ b := b ↪[fs_own γ] tt` (`FsBlocks.v`). `fsblock` cannot play
  this role: it is a HALF, so two owners each holding a half of one key is
  perfectly consistent (machine-checked — the two halves `iCombine` into a
  valid full element, no contradiction). A FULL-fraction element is
  incompatible with itself, which gives `blk_own_excl` and hence
  **`blk_own_ne : blk_own γ b1 -∗ blk_own γ b2 -∗ ⌜b1 ≠ b2⌝`** — the fact
  the inode layer's block-map injectivity (`blkmap_wf`, `fs-inode.md`)
  rests on. **No auth exists yet, and none is needed**: exclusivity of the
  elements is an auth-free property. The authority over this map belongs
  to the bitmap/free-block invariant (`balloc`, still assumed), which is
  where "block `b`'s token is in the free pool" will be stated;
  `fs_alloc` therefore drops the auth it allocates and mints one token per
  covered block into the per-block bundle, and `fs_boot_bundle` hands the
  whole `[∗ set] b ∈ cov, blk_own γfs b` to the boot client. Note the
  consequence of having no auth: a dropped token is dropped forever —
  nothing can re-mint it.
- **`γdirty : ghost_map Z bool`** — per covered block, is it in the current
  pinned write set (logged-uncommitted-or-uninstalled)? Auth + one ½ in
  `log_res` (the ½ recording W-membership); the other ½ rides with the
  machinery L-half. Flipped false→true by log_write (auth + handle half +
  log_res half all present under log.lock), true→false by install_trans at
  bunpin time.
- **The bio payloads** (bio stays FS-agnostic; these are the log layer's
  instantiation of bio's two opaque parameters):

      Ψc bno bs := bno ↪[γL]{#½} bs ∗ bno ↪[γdirty]{#½} false   (* clean *)
      Ψd bno bs := bno ↪[γL]{#½} bs ∗ bno ↪[γdirty]{#½} true    (* dirty *)

  **The payloads must be TIMELESS, and `bio_view` demands the proofs as
  record fields** (`bv_clean_tl`/`bv_dirty_tl`): they ride the escrow,
  whose every open happens inside a store's atomic update with no step
  left to absorb a `▷` — the same constraint that shaped `disk_inv`
  (projects/crash.md M5b). An arbitrary-iProp payload breaks every
  opener, and on the checkout path the withdrawn bundle IS the payload,
  so no opener-local workaround exists. No real client is constrained:
  "bs is the logical content" is ghost state (the log instance is two
  ghost_map halves).

- **Pin witnesses**: no new ghost — the existing Arc `bref` from BioInv. The
  dirty escrow arm HOLDS the bref that log_write's bpin minted; the refcnt
  auth (`M !! k = None`) is what refutes the dirty arm at eviction, locally
  in the bio proof.
- **The reservation ledger** (`γops`, FdSlots/bslots-style counting units,
  in `log_res`): `log_unit` (one prospective lh.n slot) and `op_tok u` (an
  active operation holding u unused units). Invariant in log_res:
  `lh_n + total_outstanding_units <= LOGBLOCKS` and
  `#active_ops = outstanding-cell`.

## The bio rework (Ψ-parametric; bio never reads Ψ)

`bio_ctx` (and bio_init) gains parameters: `γd`, the covered predicate, and
the two OPAQUE payloads `Ψc Ψd : mword 32 -> Z -> list (bv 8) -> iProp`
(dev, bno, bytes). Bio moves them around; only holders convert Ψc ↔ Ψd
(with log-layer ghosts, in their own hands — bio needs no client view-shifts
and no ghost laws about Ψ).

- **The uncached pool rides in `bcache_res`** (every cached/uncached
  transition is under bcache.lock):

      pool := [∗ bno ∈ covered ∖ img(bnos)] ∃ bs, disk_block γd bno bs ∗ Ψc dev bno bs

  where `img(bnos)` is the blocknos of ALL 30 slots, valid or not. TWO new
  pure conjuncts in bcache_res: (i) injectivity of `bnos` restricted to
  covered blocks (two slots never cache the same covered block;
  established at recycle from the miss scan's exit ties; initial state
  fine — all slots pin block 0, uncovered); (ii) the DEV PIN — a slot
  claiming a covered blockno is on the view's device
  (`⌜∀ k < NBUF, uint (bnos k) ∈ bv_cov V → devs k = bv_dev V⌝`). The dev
  pin is forced: the forward scan's per-slot exit tie is the negation of
  the code's `&&` (dev ≠ OR bno ≠), and upgrading it to the miss fact
  `∀ j, bnos j ≠ B` needs exactly this; the payload's own dev pin is
  unreachable mid-scan because a checked-out arm carries no payload — the
  vs_data record-the-value rule again. For the same reason `buf_mid`'s dev
  cell is pinned AT `bv_dev V` rather than existential (the recycler
  holds no fraction across the window and could never re-derive the
  value at the valid store).
- **The escrow arms restructure** (A2, the checked-out arm, is unchanged):

      A-invalid (vld = 0, covered bno):
        bytes arbitrary ∗ ∃ bs, disk_block γd bno bs ∗ Ψc dev bno bs
      A-valid (vld = 1, covered bno):
        ∃ bs bsd, bytes bs ∗ disk_block γd bno bsd ∗
          ( (Ψc dev bno bs ∗ ⌜bsd = bs⌝)         (* clean: disk agrees *)
          ∨ (Ψd dev bno bs ∗ ∃ q, bref k q dev bno) )  (* dirty: pinned *)

  (Uncovered bno — only block 0 in practice: arms carry no disk_block/Ψ,
  and bread's spec simply requires ⌜covered bno⌝.)
  **The A-invalid arm holding the fragment is the fill-race fix**: the
  recycler deposits the pool arm INTO the escrow at the blockno-rewrite
  (c)-swap rather than carrying it, because a hit thread that arrived after
  the rewrite can win the sleeplock race and become the filler — whichever
  thread sees valid = 0 at the tail withdraws the fragment at its checkout
  and does the disk read. (With caller-supplied disk_blocks this
  interleaving was unprovable; see "why revised" #2.)
- **A THIRD ARM (A3, mid-recycle) is forced by the store order.** The
  recycle block stores dev, then blockno, then valid := 0 — so between the
  blockno store and the valid store the blockno cell names the NEW block
  while the valid cell is stale, and no cell↔payload coupling can hold.
  The window gets its own arm: cells only, decoupled from any payload,
  with (i) the dev cell FULL — the recycler joins the bcache-retained half
  in — which is what every other opener refutes A3 by (a checkout holds a
  bref's dev fraction; a park holds the full valid cell; the free-open
  holds the bcache dev half), and (ii) a per-buffer exclusive **recycle
  token `bmid k`** (a `lock_tok_excl`, `bn_mid` in `bio_names`) that
  normally parks inside A1/A2 and sits in the recycler's hand during the
  window — which is what lets the RECYCLER refute A1/A2 when it reopens at
  the valid store, since by then it holds no cell fraction of its own.
  The pool exchange (withdraw the new block's bundle, deposit the evicted
  one) happens once, at the blockno store, because that is the instant the
  `bnos` function — which the pool's domain subtracts — changes.
  (`BioInv.v`: `buf_mid`, `escrow_open_mid`, `escrow_close_mid`,
  `bio_pool_recycle`, `buf_pay_evict`.)
- **The handle** replaces bio_locked:

      bio_held bn k pidv dev bno (bs : bytes) (bsd : disk) (st : Clean bsl | Dirty bsl) :=
        ⌜k < NBUF⌝ ∗ sleeplocked ∗ sl_pid ↦₄ pidv ∗ b_valid ↦₄ 1 ∗
        b_dev ↦₄{½} dev ∗ buf_own (bpa k) bno 0 bs ∗ disk_block γd bno bsd ∗
        match st with
        | Clean bsl => Ψc dev bno bsl ∗ ⌜bsd = bsl⌝
        | Dirty bsl => Ψd dev bno bsl ∗ ∃ q, bref k q dev bno
        end
      bio_locked … bs bsd st := bio_held … bs bsd st ∗ ⌜st_index st = bs⌝

  A holder who edits bytes has `bio_held bs_new bsd (Clean bs_old)` — NOT
  bio_locked — and cannot brelse until log_write re-indexes Ψ. That is
  exactly the requested brelse obligation, enforced by shape.

## The revised bio specs (deltas only; fabric threading as today)

- **bread(dev, bno)**: pre `bslot ∗ ⌜covered bno⌝` (+ fabric; **no
  disk_block, no content argument**). Post:
  `∃ k bs bsd st, bio_locked bn k pidv dev bno bs bsd st` — bytes = the
  Ψ-index = L(bno). The caller learns bs by agreeing its own
  `fsblock bno bs₀` against the handle's L-half. No mystery disjunct.
- **bwrite(b)**: pre `bio_hold0 … bs bsd` — the PAYLOAD-LESS handle —
  post `bio_hold0 … bs bs` (disk now equals bytes). NOT bio_locked, and
  the reason is a real discovery (found at write_head's proof): a
  content-changing write necessarily has logical ≠ disk on one side of
  the call whatever the order of the ghost update and the write, so the
  clean payload's ⌜bsd = bsl⌝ tie cannot appear in bwrite's pre or post.
  The caller splits the handle (`bio_held_split`), holds the payload
  aside across the call, and re-pairs after: write_head does its γL
  update AFTER the write (exactly when the clean tie holds again);
  install_trans's dirty payload never mentions the disk value at all.
  Stage 4 adds the crash-permit premise here (see below); stages 1–3
  keep rw's identity permit.
- **brelse(b)**: pre `bio_locked … bs bsd st` (consistency is internal to
  the definition); post `bslot`. Parks the arm back.
- **bpin/bunpin**: statements essentially as today (bslot ⇄ bref); they get
  re-proven over the new arms. bunpin's caller (install_trans) extracts the
  bref from its Dirty handle after bwrite established bsd = bs, flips
  Ψd→Ψc (log ghosts, under the committer's auth), and feeds the bref in.
- Sanity: bwrite/brelse's holdingsleep panic arms stay dead as today.

## log.c: the lock invariant and the function specs

`log_res` (the "log" spinlock's resource):

    ∃ (out : nat) (cmt : bool) (nc : nat),
      outstanding-cell ↦ out ∗ committing-cell ↦ cmt ∗ ncommit ↦ nc ∗
      dev/start cells (frozen after initlog) ∗
      ops_auth: #active op_toks = out ∗ sleep-channel bookkeeping ∗
      if cmt then emp else log_batch

    log_batch :=  (* everything the committer checks out *)
      ∃ (n : nat) (W : list Z),
        lh.n-cell ↦ n ∗ lh.block[] cells ↦ W (++ junk) ∗ ⌜n = length W⌝ ∗
        ghost_map_auth γL ∗ ghost_map_auth γdirty ∗
        units_invariant: n + outstanding_units <= LOGBLOCKS ∗
        [∗ bno covered] bno ↪[γdirty]{#½} (bool_decide (bno ∈ W)) ∗
        ⌜NoDup W ∧ ∀ b ∈ W, covered ∧ home-range⌝ ∗
        fsblock (log header) _ ∗ [∗ i < LOGBLOCKS] fsblock (logstart+1+i) _
        (* client halves of the log region — the log IS their client *)

Transitions mirror the code exactly: `end_op`'s last-out path sets cmt := 1
under the lock and TAKES `log_batch` out linearly; commit runs with it (no
locks — matching the code); re-acquires, deposits, cmt := 0.

- **begin_op()**: sleep loop (iLöb over the SLEEP interface, precedent
  acquiresleep/piperead). Post: `op_tok MAXOPBLOCKS`. The mint is legal
  exactly when the code's guard passes:
  `n + (out+1)*MAXOPBLOCKS <= LOGBLOCKS` and outstanding units are
  ≤ out·MAXOPBLOCKS, so the invariant survives. This IS the meaning of the
  guard.
- **log_write(b)**: pre
  `op_tok (S u) ∗ bio_held … bs_new bsd (Clean bs_old) ∗ fsblock bno bs_old ∗ ⌜home-range bno⌝`
  (or Dirty bs_old for the re-log case); post
  `op_tok u ∗ bio_locked … bs_new bsd (Dirty bs_new) ∗ fsblock bno bs_new`.
  Under log.lock: γL update (auth + both halves in hand); new-block case
  (i = lh.n): bpin's bref → the Dirty slot, γdirty flip, n++, unit burned
  into the invariant; absorption case (bno ∈ W): no bpin (already Dirty —
  its bref is in the handle), unit simply burned (the sum shrinks; fine —
  the unit is always consumed, callers reason with MAXOPBLOCKS worst case
  exactly like the C code does). Dead panics: "too big a transaction" —
  a unit in hand ⇒ n < LOGBLOCKS; "outside of trans" — op_tok vs ops_auth
  ⇒ out ≥ 1.
- **end_op()**: pre `op_tok u` (+ sleep/wakeup fabric); post emp. Fast
  path: out--, burn token+units, wakeup. Commit path (out' = 0): flip cmt,
  take log_batch, release, run commit, re-acquire, ncommit++, wakeup,
  deposit. Dead panic: op_tok ⇒ out ≥ 1 at entry ⇒ cmt = 0 (invariant:
  cmt → out = 0, maintained because begin_op sleeps on cmt).
- **commit internals** (Local specs over the checked-out log_batch; all
  callers of bread/bwrite here use the revised specs):
  - write_log: per tail i — bread(log block), bread(W[i]) → bytes =
    L(W[i]) (frozen: committer holds the auth), memmove, γL-update of the
    log-area block to that value (auth + its own client half + handle
    half), bwrite, brelse ×2. After: log area's L = physical log area
    contents = the batch's home values.
  - write_head: bread(header), write n + W into bytes, γL-update, bwrite,
    brelse. When n > 0 this is THE COMMIT POINT (stage 4: D := L over W;
    stages 1–3: nothing extra).
  - install_trans(recovering=0): per tail — bread both; the home handle
    arrives Dirty with bytes already = L(W[i]) (frozen), so the memmove
    rewrites equal content; bwrite (home disk := L); extract bref, flip
    Ψd→Ψc + γdirty→false; bunpin; brelse ×2. Then lh.n := 0, W := [],
    which RESTORES the big-op's all-false form and frees units.
- **initlog / recovery**: staged. Stages 1–3 give initlog a clean-image
  precondition (⌜on-disk header n = 0⌝ — true after mkfs) and construct
  log_res + bio_init's pool inputs from the boot-side disk_block mint (the
  recorded-open mkfs-image mint, projects/crash.md). Real recovery
  (install from a committed on-disk log) is stage 4 — it is the consumer
  of `P_fs`'s crash-receipt.
- **sys_sync**: deferred with stage 4 (its spec is a durability receipt:
  needs D-side client views).

## Stage 4 — the crash side (recorded now, built with recovery)

What `P_fs` is FOR: `∃ D, dur_auth γD D ∗ Pcontent D ∗ tie(P, D)` where
`tie` says recovery(P) = D. Every physical write's permit
(`▷P_fs ==∗ ▷P_fs`, spent at the DMA completion — the M5b seam) must
re-establish the tie: log-area writes at on-disk n = 0 don't change
recovery; write_head with n > 0 moves D atomically to L|W (the committer's
receipts — the frozen γL facts for W and the log area — are what prove it);
install writes rewrite home blocks to their logged values (recovery
unchanged); the final write_head clears. Mid-batch L-inconsistency never
matters: D only ever jumps between batch boundaries, where outstanding = 0.
FS-level consistency of D (`Pcontent`) stays PARAMETRIC in the log layer;
when the FS layer above wants it, each op's end_op can carry a composable
"my delta preserves Pcontent" wand — xv6's ops are serializable under
their inode/bitmap locks, so the batch composes them.

### The stage-4 architecture (PROPOSED, to pin down before any code)

The two forks recorded earlier are resolved by one load-bearing finding
plus one dissolution; the whole shape follows.

**The finding that forces everything: client-visible disk fragments
cannot live at the fixed `γdur`.** Today bio's pool/escrow/handles hold
FULL fs-range `disk_block` fragments of the fixed durable auth. At the
first crash those strand in the dead era's invariants forever —
`ghost_map` cannot re-mint an existing key, and "auth-side forgetting"
does not typecheck (delete needs the elem, which is exactly what is
stranded). Fractional splits (a ½ standing in `P_fs`) merely leak ½ per
crash. So the CURRENT stage-1–3 volatile design cannot boot twice; any
resolution must make the stranded pieces RE-CREATABLE, i.e.:

1. **Per-era client disk ghosts — LANDED (Phase A).** Each boot allocates
   a fresh era image ghost (auth + full fragments, minted at the current
   disk content); bio's `bv_gd` points at the ERA ghost; a crash abandons
   it wholesale — nothing to reclaim, next boot mints fresh. What landed
   (see `design/crash.md`, "The disk image ghost"):
   - `riscvEraGS.era_disk_name`; the typing class stays fixed-layer
     (`riscvF_diskGS`, the unique instance source). The fixed
     `riscv_disk_name` gname is GONE — there is no auth-only fixed map at
     all, because nothing needs one: `state_interp` ties the ERA map to
     the machine's own `v_disk`, and the REAL disk is what carries content
     across the crash.
   - `state_interp`'s image conjunct moved INSIDE the `gpow` live branch
     (it is `era_interp`'s fourth conjunct, `disk_dur_interp E g`), so
     when the power is off there is no image conjunct at all.
   - `wp_power_loop`'s PowerOn arm is THE BOOT MINT: `DiskImg.disk_img_alloc`
     allocates the fresh map at the preserved `v_disk`, and `power_boot_res`
     hands the client `disk_img_bytes (era_disk_name HE) 0
     (disk_read (v_disk (g'.(gdev).(dvirtio))) 0 ndisk)` — total exclusive
     ownership of bytes `[0, ndisk)`, every boot including the first. The
     range is a PARAMETER (`ndisk`, threaded like `nproc`);
     `SystemAdequacy.XV6_DISK_BYTES = 2000 * 1024` is the xv6 value, so no
     FS constant appears below that file. `BootShared.boot_shared_alloc`
     re-exports the mint as `disk_bytes γv 0 (disk_read … 0 ndisk)`, which
     is where the bio pool will take it from.
   - The seam equation is now `dn_img γd = disk_img_name` (the ambient
     era's gname); `disk_ghosts_alloc` still CONSTRUCTS `dn_img` at it and
     exports the equation, `wp_disk_loop` still takes it as a premise, and
     `virtio_proto_step` is unchanged in shape.
   - The recorded "mkfs-image mint" future work dissolves into the boot
     mint; `disk_bytes_mint` (at `disk_names`) has no caller left.
2. **Permits are LOGICALLY-ATOMIC client view shifts, transported by
   M5b's option (a)** (decided with the user; an earlier tag-enumeration
   draft is recorded below as rejected). bwrite's crash-facing contract
   is the textbook logatom disk write: the CALLER supplies a fupd
   `▷P_fs ==∗ ▷P_fs ∗ Q`, curried over its own ghosts, applied at the
   DMA completion (the linearization point); `Q` is the caller's receipt
   ("this transaction committed", durable fragments, the receipt
   lower-bound) and returns to it after the write. The timeless-slot
   blocker is solved exactly as M5b recorded: a SECOND, non-timeless era
   invariant holds the in-flight permits — per pending write, either the
   client's fupd identified by a saved proposition at a gname the
   timeless slot stores (pure, so it rides `disk_inv` fine), or the
   `done(Q)` arm after the completion consumed it. Deposit works under
   the `▷` (`▷B ∗ P ⊢ ▷(B ∗ P)`); the completion strips via
   `wp_disk_step`'s existing between-legs `iNext`; the enqueuer collects
   `▷Q` post-wake where it has steps (and Q is usually timeless ghost
   state anyway). The MECHANICAL disk-tracking update (the record's P
   moving to P[o := bs]) stays with the completion itself — it has the
   write's identity from the slot and the state_interp tie — so the
   client fupd is stated against the FS-meaning part of the record with
   the write identity as a premise. Consequences: the four WAL write
   kinds (log-fill / commit(n,W) / install / clear) exist NOWHERE as a
   type — they are four call sites in the log proofs, each proving its
   own fupd with its own local knowledge; nothing FS-shaped appears
   below the log layer; and the design does not lean on xv6's commit
   serialization, so it would survive a concurrent-commit log.
3. **`P_fs` is a generation-swappable escrow over a PURE record.**
   Record = (P restricted to the fs range, D, the receipts list), with
   `⌜recovery(P) = D⌝`-class conjuncts. Arms: at-rest, or checked out by
   generation g — the arm holds g's one-shot FS BOOT TOKEN (a fresh
   era-bundle exclusive; a later generation swaps in ITS token using the
   recorded pure picture — abandonment, not revocation, exactly the
   crash-layer's own pattern). The tie between the record's P and the
   REAL disk is a fixed-layer `ghost_var` ½/½ against `state_interp`'s
   disk conjunct — both fixed, nothing strands. Adding the state_interp
   conjunct follows M5's fourth-conjunct recipe.
   - **THE TIE HALF CANNOT LIVE INSIDE `riscv_crash_pred`** (found in
     phase C1, and it corrects the earlier "both halves are in hand at a
     completion" reading). The completion is the only mover of the tie,
     and its channel to the crash side is `crash_inv`, whose body was the
     OPAQUE `iProp` field `riscv_crash_pred`: opening `crashN` yields
     that proposition, not its innards, so a half parked inside `P_fs`
     is unreachable to the mechanical update — and at `Pc := True` it
     does not exist at all, which makes the conjunct unmaintainable.
     **LANDED FIX (phase C2a): index the crash predicate by the DISK
     IMAGE.** `riscv_crash_pred : (Z -> bv 8) -> iProp Σ` with
     `crash_inv := inv crashN (∃ dk, disk_tie dk ∗ riscv_crash_pred dk)`,
     and `state_interp`'s new FIXED conjunct `fs_tie_interp g :=
     disk_tie (v_disk (dvirtio (gdev g)))`. The half is a SIBLING of the
     client's predicate — allocatable at the trivial `Pc`, mechanically
     movable by the completion (`ghost_var` is timeless, so the `∃dk`
     strips inside the existing `crashN` opening), and exactly the tie
     `P_fs` needs, because `P_fs` becomes a PREDICATE ON `dk` and owns no
     tie ghost at all.
   - **THE INDEX IS THE RAW BYTE FUNCTION, NOT THE BLOCK MAP.** Two
     reasons, both load-bearing: `state_interp` lives below every FS
     constant (BSIZE, the fs range), and — decisively — the completion
     would otherwise owe a SECTOR-EVENNESS fact (`vs_sector_off` is
     `sector * 512`, and only the driver knows its sectors are even).
     At the raw index the completion's obligation is literally
     `VirtioModel.disk_write`, and the block view (`FsCrash.fs_blocks`,
     with `fs_blocks_write_eq`/`_ne` as its teeth) is a pure re-indexing
     the FS layer applies on top.
   - **A WRITE'S PERMIT IS NOT FREE, AND THAT IS THE HONEST CONTENT.**
     The permit is indexed by the request's own write identity —
     `disk_write_permit (w : disk_wr) Q := ∀ dk, ▷ Pc dk ==∗
     ▷ Pc (wr_apply w dk) ∗ Q` with `disk_wr := option (Z * list (bv 8))`
     (`None` = a read). `wr_apply None` is the identity ON THE NOSE, so a
     READ's permit stays provable for an ARBITRARY `Pc` and the whole
     read stack (bread and above) is untouched. A WRITE moves the index,
     so no `Pc`-generic proof exists: an earlier claim that the trivial
     write permit survives the reshape was WRONG. Each of the four WAL
     write kinds therefore proves its OWN fupd against `P_fs`
     (`FsCrash.fs_logfill_permit` / `_commit_permit` / `_install_permit` /
     `_clear_permit`); there is no bridge lemma and no `Pc`-generic write
     permit in the tree.
   - **THE PERMIT'S INDEX IS PINNED TO THE REQUEST BY THE SLOT.** The
     permit-channel token gains the `disk_wr` as part of its ghost-map
     value, and `VirtioProto.slot_pend_res` holds it AT `vs_wr sl` —
     the slot's own write identity (`VirtioQueue.vs_wr`, with
     `vslot_post_wr` as the completion's discharge). So nothing in
     PermInv knows anything about virtio, and nothing in virtio knows
     anything about the crash predicate.
   - Consequence for adequacy: `HPc : ⊢ Pc` cannot survive — a crash
     predicate that OWNS ghosts is never provable from nothing. The
     interface becomes "the client builds `Pc` from the ghosts adequacy
     allocated", i.e. `FsCrash.P_fs_alloc`'s shape.
4. **Recovery** = initlog's real spec: swap the `P_fs` arm with the
   era's boot token; the recovery writes are tagged install/clear
   transitions; the final record has the header cleared and D unchanged.
   - **THE SWAP IS A PREREQUISITE FOR THE WRITE FUPDS, NOT A FOLLOW-ON**
     (found in phase C2b). A crash permit is a STATELESS view shift: it
     runs at the DMA completion, inside the disk thread, on whatever the
     caller curried at enqueue. So every fact a WAL write's fupd needs
     about the PHYSICAL log region — "the on-disk header is clean"
     (write_log's slot fills), "the physical log slots hold the logged
     values" (write_head's commit), "the on-disk header is the (n, W) I
     just wrote" (install_trans's home writes) — has to be knowledge the
     ERA holds continuously. It cannot live in `P_fs` as a ghost equation
     against `γL`: `γL` is per-era and dies at a crash while `P_fs` is
     fixed-layer. It cannot be re-derived at each `bwrite` either: bio
     owns every covered block's `disk_block` (the log region is inside
     `cov`), and the pool/escrow arms that DO tie physical to logical
     (`pool_blk`'s shared `bs`, the clean arm's `⌜bsd = bs⌝`) are parked
     under `bcache.lock`. The CHECKED-OUT arm is precisely the place for
     that era-side custody, so recovery's swap has to land first.
   The stage-2 clean-image spec becomes the n = 0 corollary.
   - **AN ERA LEARNS THE ON-DISK HEADER ONLY BY HAVING WRITTEN IT, AND THAT
     CAPS WHAT RECOVERY CAN CLAIM** (phase D2). A crash permit is a
     stateless view shift over a UNIVERSALLY QUANTIFIED image `dk`, and the
     only channel from the image into client-visible knowledge is the
     custody arm's `log_mirror_ok M (fs_blocks dk) ls`. A swap installs
     `M := mirror_of (fs_blocks dk) ls` — true, but at an image the client
     cannot name, so the picture it hands back is OPAQUE (`Q` is fixed at
     permit-creation time and cannot mention `dk`). The steady state is
     fine: `fs_commit_permit` writes the header, so its `Q` names the
     picture from the BYTES IT WROTE. Recovery only READS the header, and a
     read's permit carries no data (`disk_wr = option (Z * list (bv 8))` —
     `None` for a read). Consequences, all forced:
     - recovery's `install_trans` writes CANNOT be `fs_install_permit`s
       (which need `Ws !! i = Some b` for the DECODED on-disk header);
     - they are `FsCrash.fs_recover_permit`s instead — RE-BASING writes,
       which set `fr_D` to whatever the post-write image recovers to
       (always available: `fs_recovery` is a total function of the image,
       `fs_recovery_total`) and extend the history by it. Sound, and
       nothing later cashes the difference: every earlier receipt stays
       valid because the history only grows, and the post-recovery state is
       pinned by the FINAL header write anyway;
     - what is NOT provable this way is the WAL's COMPLETENESS claim ("what
       recovery leaves behind IS the last committed state"). Safety —
       `P_fs` stays well formed across every recovery write, custody is
       this era's, `log_ctx` comes out — is unaffected.
     **The fix, when completeness is wanted, is a read-data-indexed permit**:
     make a READ's `Q` a FUNCTION of the delivered bytes (`Q (disk_read dk
     off len)`), so the header bread's own permit can hand back
     `log_mirror_at (hdr_dec bs)` at the bytes `bread` returns. That is a
     machine-layer interface change of the same size as phase C2b — saved
     PREDICATES rather than saved props in `PermInv`, a read-data equation
     at `WpUart`'s completion (the analogue of `vslot_post_wr`), the permit
     premise on `SpecVirtioDiskRw`/`SpecBread`, and a trivial instance at
     every existing bread caller. It is the only known way to close the gap:
     tying a client-held `disk_block` fragment to `dk` instead would need
     the era image AUTH inside the stateless fupd, and that lives in
     `state_interp`.
   - **THE SWAP CANNOT BE A PLAIN GHOST STEP outside a write's permit**, which
     is why "swap first, then install with full knowledge" is not on the
     table. Retiring the incumbent arm needs `c <= S gen_id` — "no later era
     has swapped" — and the only source of that bound is the STARTED-
     GENERATIONS AUTH (`fs_arm_le` against the arm's `gen_started`). That auth
     lives in `state_interp` and reaches a client only through
     `wp_disk_step`'s callback, i.e. only inside a permit's fupd. A client
     holds `gen_started gen_id`, a LOWER bound, which is the wrong direction.
     (Opening `crashN` directly would give the record but not the auth.)
   - **THE RECOVERY-SIDE PERMIT FAMILY IS UNIFORM IN `n`, AND HAS TO BE.**
     `SpecInstallTrans` takes its per-entry permits as a `□`-generator over
     one threaded resource, so the entry that performs the swap cannot have
     a different contract from the rest. `FsCrash.fs_era_custody` is the
     disjunction that makes it uniform — `log_mirror_full` (the boot mint,
     no custody taken yet) `∨` `log_mirror_any ∗ swap_lb (S gen_id)`
     (custody taken, picture unrecorded) — and `fs_recover_permit` consumes
     and re-establishes it, swapping on first use. `fs_boot_head_permit`
     closes the boot the same way for initlog's final `write_head`: at
     `n = 0` no install ran and it IS `fs_swap_permit`; at `n > 0` the first
     install already swapped and it is `fs_clear_permit` carrying the swap
     receipt through. Both land `log_mirror_at (0, []) ∗ swap_lb (S gen_id)`,
     which is what keeps initlog's postcondition — hence `log_ctx` — free of
     `n`.
5. **sys_sync** = a persistent receipt: the record carries a fixed
   mono-list of committed D's; commit appends; sys_sync's post is a
   lower-bound receipt that the caller's pre-call writes are durable.
   - **WHAT A RECEIPT CAN HONESTLY NAME** (phase D2's analysis, not built).
     `fs_commit_permit`'s `Q` today is `∃ D, fs_receipt_any D` with `D`
     unnamed, because the new durable state is
     `fs_install (fs_blocks dk) ls Ws (fs_restrict (fs_blocks dk) home)` and
     the committer holds no picture of the HOME side of the physical disk.
     But it does not need one: the only part of `D` a client cares about is
     the part the batch WROTE, and `fs_install_hit` computes exactly that
     from the physical LOG SLOTS — which the mirror already records
     (`log_mirror.lm_slots`, and `log_mirror_ok` pins it to
     `P (log_slot_bno ls i)` for `i < LOGBLOCKS`). So the minimal addition
     is to stop throwing that field away at the era side: give
     `LogInv.log_mirror_at` a second index, a PARTIAL slot record
     `sl : nat -> option (list (bv 8))`, which `fs_logfill_permit` EXTENDS
     one slot per write and `fs_commit_permit` READS. `log_mirror_clean` is
     then its `(0, []) / (fun _ => None)` instance, so `log_batch` — and
     every statement above `LogInv.v` — is textually unchanged. With it the
     commit receipt becomes the honest, useful one:
     `∃ D, fs_receipt_any D ∗ ⌜∀ i b, Ws !! i = Some b -> D !! b = Some (Lw i)⌝`
     — "the state I committed has MY blocks at MY contents".
   - **NO RECEIPT ESCAPES TO ANY CALLER TODAY**, which is why sys_sync cannot
     yet state anything about durability at all: `ProofEndOp` HOLDS the
     commit's `∃ D, fs_receipt_any D` (it is what `fs_commit_permit`'s `Q`
     hands back) and drops it, and `SpecEndOp`'s post does not mention it.
     **And it must NOT simply be exported there**: `do_commit` is decided at
     run time (only the last op out commits), so an end_op post carrying the
     receipt would be a DISJUNCTION the caller cannot resolve — i.e. `True`.
     That is precisely why sys_sync exists, and why the receipt has to be
     DEPOSITED into `log_res` keyed by the commit counter rather than returned
     to whoever happened to be last.
   - **sys_sync ITSELF NEEDS A COMMIT COUNTER, NOT A NEW GHOST FAMILY.** Its
     loop is `n := ncommit + 1; while (ncommit < n) sleep(&log)`, so the
     `l_ncommit` cell — today an arbitrary `mword` in `log_res` — has to
     become a faithful `nat` with a `mono_nat` auth beside it, and the
     committer (end_op) deposits its receipt into `log_res` as it bumps the
     counter. sys_sync then reads the counter at entry and returns the
     receipt of the first commit that follows. Note the barrier's real
     shape: the fast path (`committing == 0 && outstanding == 0`) returns
     the LAST commit's receipt, and that is the strong case — nothing is in
     flight, so the durable state IS the current logical one.
   - **WHAT sys_sync CANNOT SAY, and why it is not a defect.** "The caller's
     own writes are durable" is not a log-layer statement: two ops in one
     batch may write the same block, so a caller's content claim is
     genuinely stale after another op's `log_write`, and what is durable is
     the batch's FINAL content. Composing the receipt above with the FS
     layer's own per-op knowledge is where that gets closed — the same place
     `Pcontent` lives (item 6).
6. **FS-level consistency stays parametric** (the record carries raw
   maps; `Pcontent D` and the per-op composable wands remain the future
   fs.c layer's business), and the torn-write knob stays off
   (request-atomic writes, crash.md's recorded modeling choice).

Cost inventory (all contained): the era image ghost + boot mint seam
(DiskPtsto/VirtioProto/boot bundle); the γdur auth-only sweep (rw's
`disk_block` re-keyed to the era gname — one seam equation today, so
mostly mechanical); the permit→tag reshape at `virtio_proto_step` /
`wp_disk_loop`; the state_interp `ghost_var` conjunct; `P_fs` + the boot
token; bwrite's spec gains the tag argument (threaded to rw); initlog's
recovery spec/proof; sys_sync.

## Decision record (rejected shapes)

- **A committer-side contract must witness HOME-block content through the
  auth it holds (`ghost_map_lookup` + a pure `L !! bno = Some …` premise),
  never through a client `fsblock`**: home blocks' client halves are with
  the FS callers by construction (log_write hands them back; log_batch
  holds only the log region's own), so a committer spec demanding one is
  unsatisfiable at its only real call site — and compiles anyway, because
  the n = 0 caller discharges it vacuously. Found twice while proving
  stage 3 (install_trans's per-entry home half; the same shape was
  avoided in write_head by keeping it d-generic).

- **Client view-shifts as bio parameters** (load/evict fill in fs_inv):
  rejected — once the pool and the disk_block ride inside bio, every
  Ψ-move is plain resource shuffling in bio's own proofs; a pure opaque
  payload suffices and no fancy update interface leaks into the bio specs.
- **A separate namespace invariant for the uncached pool**: rejected —
  every pool transition is under bcache.lock anyway; putting the pool in
  bcache_res avoids a second mask and the fs_inv↔bcache_res coupling
  ghost.
- **`ghost_var` per block for L** (machinery ½ / client ½, no auth):
  rejected — a holder with both halves could update L without log_write,
  and then nothing freezes L during commit; the commit-to-install content
  tie dies. The ghost_map auth IN log_res is precisely the freeze.
- **The dirty pin-witness in log_res instead of the escrow arm**:
  rejected — eviction's refutation must be LOCAL to the bio proof (the
  refcnt auth vs the arm's bref); bio cannot see log_res. Conversely the
  install-side needs the bref too, and it gets it from the handle it
  checked out — one bref serves both because it travels with the arm.
- **Caller-supplied `disk_block` kept in bread's pre**: rejected (see
  "why revised" — concurrency and the fill race both break it).
- **log_write returning the unit on absorption**: rejected — callers
  cannot predict absorption, a conditional resource poisons every caller
  proof, and always-consume matches the C code's own MAXOPBLOCKS
  worst-case accounting.
- **Crash permits as PURE TRANSITION TAGS in the timeless slots**
  (enumerating the WAL's four write kinds as data the completion
  case-splits on): rejected in favour of the logatom permit above. It
  worked around the timeless-slot blocker that option (a)'s permit
  invariant already solves properly, it pushed an FS-shaped enumeration
  deep into the device stack, and it leaned on xv6's commit
  serialization for tag-freshness — three costs the client-fupd shape
  simply doesn't have.
