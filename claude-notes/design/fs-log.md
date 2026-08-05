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
- **bwrite(b)**: pre `bio_locked … bs bsd st`; post
  `bio_locked … bs bs st'` — disk now equals bytes (st' = st, with the
  Clean tie now at bs; for Dirty the caller sees ⌜bsd' = bs⌝ directly and
  can later flip Dirty→Clean at bunpin). Stage 4 adds the crash-permit
  premise here (see below); stages 1–3 keep rw's identity permit.
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

Known open forks, discovered while designing (do not start stage 4 without
settling these):

1. **The permit needs the write's identity.** A bare `▷P_fs ==∗ ▷P_fs`
   cannot update a shadow-of-P ghost per write. The enqueuer knows (o, bs)
   at enqueue and can curry them into the permit it deposits, but the M5b
   blocker stands: an iProp permit cannot ride the timeless `disk_inv`.
   Candidates remain M5b's (a) second non-timeless permit invariant with a
   timeless skeleton, or (b) `P_fs` closed under in-flight writes with a
   pure pending-set. Also likely: the permit type widens so the completing
   write's `disk_block` fragment passes THROUGH the permit (P_fs holding a
   fraction of fs-range disk_blocks), which touches `virtio_proto_step`'s
   hand-off type.
2. **The era boundary strands the FS ghosts.** Bio's pool/escrow
   `disk_block` fragments, log_res's γL/γdirty auths and halves — all die
   with the era at a crash. Recovery in the next generation needs fresh
   ones. The recorded option (b) "auth-side key forgetting"
   (projects/crash.md, stranded-fragment decision) DOES NOT TYPECHECK as
   stated: `ghost_map_delete` needs the elem, and the elems are exactly
   what is stranded. Viable shapes: per-era FS ghosts (γL/γdirty freshly
   allocated each boot — natural, they are volatile state) plus a
   crash-SPANNING hand-off through `P_fs` itself, shaped as an escrow
   whose checked-out arm RECORDS the pure picture (the vs_data rule) so
   the next generation can re-check-out with its own one-shot boot token
   and rebuild the volatile layer from recorded data + re-minted
   fragments. The base `γdur` fragments need the same treatment (they are
   fixed-layer; whether P_fs holds a standing fraction of them, or the FS
   range is never minted at the base and P_fs tracks content in its own
   shadow, is part of fork 1's resolution).

## Decision record (rejected shapes)

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
