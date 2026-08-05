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

## Stage 2 — LogInv + the log.c specs

- [ ] `LogInv.v`: `log_res` / `log_batch` per the design; the ops/units
      counting ghost (mirror FdSlots); `op_tok`; the cmt→out=0 tie;
      lemmas: mint (begin_op's guard arithmetic), burn-unit-grow,
      burn-unit-absorb, batch checkout/deposit.
- [ ] Decode/Code files for log.c (initlog, begin_op, end_op, log_write,
      and the static write_log/write_head/install_trans/read_head/
      recover_from_log/commit — check which got inlined; gcc may have
      folded commit into end_op etc. Look at KernelInstrs.v first).
- [ ] Spec files: SpecBeginOp, SpecEndOp, SpecLogWrite, SpecInitlog
      (clean-image precondition ⌜on-disk header n = 0⌝ for now).
      Commit internals as Local contracts inside the proof, not public
      specs (they are static and only end_op/initlog call them).
- [ ] sys_sync: deferred to stage 4 (needs durability receipts).

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
