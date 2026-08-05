# Project: the FS block layer — logged view + log.c

Design: [`../design/fs-log.md`](../design/fs-log.md) — read it first. This
file is the worklist.

## Status (2026-08-05)

**STAGE 1 IS COMPLETE**: the Ψ-parametric bio layer is reworked and all
six functions re-proven and linked (bio.c 6/6, axiom footprint unchanged,
`Print Assumptions Bread.wp_bread_sconf` = the 5 `rv64d` hooks + funext).
Three interface facts were discovered DURING the re-proofs and folded back
into the design (all recorded in design/fs-log.md): the payloads must be
Timeless (bio_view carries the proofs as fields); `bcache_scan` needs the
DEV-PIN pure conjunct (the scan's && exit tie alone cannot yield the miss
fact); `buf_mid`'s dev cell is pinned AT `bv_dev V` (the recycler holds no
fraction across the window). Reusable proof vocabulary now in
ProofBreadParts.v: `bfun_upd` (named one-slot function update — inline
lambdas make every lemma unify against a different beta-redex),
`bcache_scan_incr`/`bcache_scan_recycle` (the open-scan forms with the new
conjuncts threaded), `bd_pay_retarget`, and the three asymmetric (c)-swaps
`escrow_recyc_{dev,bno,valid}`. ProofBread.v's forward scan now
ACCUMULATES its negative exit tie (`∀ i ∈ done, ¬(devs i = dev ∧ bnos i =
bno)`) — the old proof discarded it; the miss fact needs it.

Reference material: [`../completed/bio.md`](../completed/bio.md) (the
physical bio layer this reworks — instruction maps, escrow swap lemmas,
proof-agent notes all still apply), log.c disassembly to be catalogued the
usual way (Code*.v; check KernelRvcDecode/KernelBaseDecode first per the
decode-dedup rule).

## Stage 1 — the bio rework (Ψ-parametric escrow + pool)

- [x] `FsBlocks.v` (new): `fsLogG`/`fs_names` (`γL`/`γdirty`); `fsblock`;
      `fs_mclean`/`fs_mdirty` (the two payloads); `fs_view` (the bio_view
      instantiation); fsblock↔payload agreement, the auth-gated update and
      dirty-flip, `fs_alloc`. The range predicates over the superblock
      constants are stage 2 (`bv_cov` is just a `gset Z` here).
- [x] BioInv.v: `bio_view` (bv_gd/bv_dev/bv_cov/bv_clean/bv_dirty)
      parameter threaded everywhere; the THREE escrow arms (buf_parked with
      `buf_pay` + `bmid`, buf_chain + `bmid`, buf_mid) — the A3 window and
      the `bmid` recycle token are a design addition forced by the recycle
      block's store order, see the design doc; swaps restated
      (checkout/park/open_free + new open_mid/close_mid/buf_pay_evict);
      new `bio_held`/`bio_locked`; `bio_init` takes the covered pool bundle
      and `0 ∉ bv_cov`.
- [x] The pool big-op + covered-bnos injectivity inside `bcache_scan`
      (BioInv.v; BcacheInv.v needed NO change), with `bcache_cached`
      membership spec and the one-shot `bio_pool_recycle` exchange lemma.
- [x] The five Spec files revised per the design (bread loses the
      disk_block/bs_disk arguments and gains the covered/device premises;
      bwrite/brelse over the new bio_locked with interior disk fragment;
      bpin/bunpin only re-based).
- [x] Re-prove: bpin, bunpin, bwrite, brelse, bread — all six linked,
      bio.c 6/6. bwrite grew the Local `bio_pay_reindex` (the one case
      split on d, factored so the whole-function proof never destructs
      it); brelse parks via the assembled `buf_pay` + `case_decide`.
- [x] bio_init's inputs: the client pool bundle `[∗ set] b ∈ bv_cov V,
      pool_blk V b` + `0 ∉ bv_cov V` premise (the actual mkfs-image mint
      at adequacy remains recorded future work in projects/crash.md).
- [x] `lemma_diff.py` + `spec_vacuity.py` CLEAN; `proof_coverage.py
      --check` rc=0; full build green (checkpoint commit).

## Stage 2 — LogInv + the log.c specs (COMPLETE)

- [x] `LogInv.v`: geometry (struct log @ KernelSyms.log: spinlock@0/24B,
      start@24, outstanding@28, committing@32, dev@36, ncommit@40,
      lh.n@44, lh.block[]@48); the LEDGER as a ghost map op-id →
      remaining budget (a flat units counter is NOT inductive at end_op —
      the per-op structure is what closes it), `log_op`, the three
      transitions + guard arithmetic (`log_reserve_ok`) + `op_sum`
      theory; `log_batch` (both FsBlocks auths = the freeze, the dirty
      halves over cov recording W's membership, the log-region client
      halves, the lh cells at (n, W), and THE SLOT POOL
      `bslots bn ((LOGBLOCKS − n) + 2)` — one unit per free slot + the
      committer's two in-flight breads; pool + n invariant is what makes
      log_write's bslot refund UNCONDITIONAL and lets install's bunpins
      deposit their freed units instead of end_op dropping them);
      `log_res` (cmt=true → batch checked out, out = 0); `log_ctx`; and
      `log_frozen` (the frozen dev/start cells alone — what write_head
      and install_trans take, because initlog calls both BEFORE the lock
      can be sealed); `hdr_n` (only the header's n field — the full
      (n, W) encoding is deliberately stage 4).
- [x] Code files (all six compile; structure headers carry frames,
      offsets, loops, calls, panics): CodeWriteHead, CodeInstallTrans,
      CodeInitlog, CodeBeginOp, CodeEndOp, CodeLogWrite. read_head +
      recover_from_log inlined into initlog; write_log + commit into
      end_op; initlog's "too big logheader" panic is compile-time dead
      and ABSENT from the image. write_head/install_trans kept real
      symbols → real Spec/Link treatment (not Local contracts).
- [x] Spec files, all six, spec_vacuity/coverage clean; K values:
      log_write 18, begin_op 26, write_head 44, install_trans 50,
      initlog 56, end_op 58. Notables: log_write takes `bio_held` (bytes
      already edited, pay still at bsl) + fsblock + log_op (S u) and
      returns the re-indexed DIRTY `bio_locked` + fsblock at the new
      bytes + log_op u + the unconditional bslot; install_trans takes
      per-entry BOTH fsblock halves (home + log copy, same content — the
      memmove content-preservation needs the copy's) + the dirty halves
      at true, returns them at false, `recovering = false ∨ n = 0` for
      stage 2; initlog is the clean-image form (`hdr_n = 0`) and stocks
      the pool (pre `bslots bn 34`, post `bslots bn 2` + ∃γ log_ctx).
- [ ] sys_sync: deferred to stage 4 (needs durability receipts).

Note for ProofLogWrite (from the spec round): the append path must peel
the refunded unit out of the batch's pool AT THE `lh.n++` store — the
pool's index is `(LOGBLOCKS − n) + 2` and only the n++ re-establishes it.

## Stage 3 — the log.c proofs

- [ ] log_write (no sleeps; log.lock critical section; the γL/γdirty/bpin
      choreography).
- [ ] begin_op (sleep loop over SLEEP; precedent: acquiresleep's retry
      iLöb).
- [ ] end_op + commit (the batch checkout across release; write_log /
      write_head / install_trans loops are fuel inductions over the
      revised bread/bwrite specs; memmove via the proven spec — note
      memmove's contract is non-overlapping-by-separation, two buffers'
      byte ranges are separate conjuncts, fine here).
- [ ] initlog (boot wiring: builds log_res; called under fsinit? — check
      the actual call chain in this kernel's main/forkret path when
      wiring).

## Stage 4 — the crash instantiation (DO NOT START until the two forks in
## the design doc's stage-4 section are settled)

- [ ] Settle fork 1 (permit identity/currying; the M5b timelessness
      blocker) and fork 2 (era-boundary hand-off of the FS ghosts; note
      the recorded option (b) auth-side forgetting does not typecheck —
      ghost_map_delete needs the elems).
- [ ] `P_fs` definition; adequacy client passes it as Pc; the mkfs-image
      mint threaded into the boot bundle.
- [ ] bwrite gains the permit premise; write_head's commit permit does
      D := L|W; install/write_log permits are recovery-neutral.
- [ ] recover_from_log / install_trans(recovering=1) against the crash
      receipt; initlog's clean-image precondition replaced by the real
      one.
- [ ] sys_sync spec + proof (durability receipt).
