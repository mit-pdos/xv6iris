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

## Cleanup queue (post-stage-3; none blocks anything)

- [ ] Promote the four missing WP leaves now proved locally TWICE or
      needed broadly: `wp_addw4_s_sconf` (base 3-operand addw — Local in
      BOTH ProofInstallTrans and ProofEndOp, the promotion trigger) to
      WpSconfAlu.v; `wp_bgtz_{fall,taken}_s_sconf` (BLT with rs1 = x0 —
      only the rs2 = x0 bltz twin exists) and `wp_blt_taken_s_sconf`
      (the general two-register BLT taken arm; every loop back edge of
      this shape needs it) to WpSconfBtype.v. All four route through
      WpSconfBtype's Local exec lemmas by qualified name — copy-paste
      promotions.
- [ ] The byte↔word bridge vocabulary is now duplicated: ProofWriteHead's
      `wh_align4`/`wh_word_acc`/byte-list bridges and ProofInitlog's
      `il_*` near-copies. Promote to a shared home (ByteBuf.v or
      InstrBytes.v) when a third consumer appears.
- [ ] The decode-dedup sweep flagged by the log.c Code files: the words
      duplicated WITHIN the six new files (0x060a, 0x0711, 0x0791,
      0x962a, 0x4314, 0x00c05f63, 0xfec79ce3, 0x509c, 0x2585, 0x0a91,
      0x000aa583, 0x018a2583, 0x024a2503, 0x02ca2783) and the
      cross-file candidates listed in each Code header.
- [ ] `wp_next_shift` (WpSconfVc) subsumes the bespoke `*_cont` +
      `*_cont_shift` pairs — ProofWriteHead's could be retired the next
      time that file is touched (ProofInitlog already uses the direct
      form).

## Stage 3 — the log.c proofs (COMPLETE: log.c 6/7 fns, 91.0% of bytes;
## only sys_sync remains, deferred to stage 4)

- [x] log_write (ProofLogWrite: the two closing wands built once after
      acquire and carried as an ∧ keyed on ⌜bno ∈ W⌝ / ⌜∉⌝ — NO case
      split on d in the whole-function proof; both duplicated slot-store
      blocks feed one shared tail at +0x66).
- [x] begin_op (ProofBeginOp: iLöb retry loop, the W-form guard
      arithmetic as mword-free lemmas, l_cmt's `if cmt` cell making both
      branch conditions a destruct).
- [x] write_head + the ProofBwrite adaptation to bio_hold0 (ProofWriteHead:
      d0-generic payload handling; the γL update AFTER the bwrite is when
      the clean tie re-holds; the wh_* byte↔word window vocabulary).
- [x] install_trans (ProofInstallTrans: home content witnessed through
      the committer's auth — it_pay_bs_auth — after the spec fix; the
      dirty flip at bunpin; per-entry fuel induction with the write set
      split at the cursor).
- [x] end_op + commit (ProofEndOp, 4471 lines: six blocks each with its
      own CID binder; the batch checkout across release; the copy loop's
      log-region client halves split at the cursor; the pool arithmetic
      exact end-to-end).
- [x] initlog (ProofInitlog: clean-image form — the header-copy loop is
      dead; delayed lock seal with the ∀R wand; word4_pointsto_persist →
      log_frozen; assembles log_batch 0 / log_res inline).

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
