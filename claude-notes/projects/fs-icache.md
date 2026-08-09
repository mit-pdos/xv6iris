# fs-icache — worklist: the inode region, the escrow, and iget/iput

Design: [`design/fs-icache.md`](../design/fs-icache.md) — read §10 (the
per-entry escrow + pool), §11 (the inode region / `dinode_at`), and §12
(why §11.4's checkout died, and the fupd-shaped `SpecLogWrite` premise
that replaced it) before touching anything here. The definitional layers
are `iris/IcacheInv.v` (landed earlier) and `iris/InodeRegion.v` (landed
2026-08-09, axiom-free).

State of fs.c: 11/24 functions; `iput` is the only assumed function in
kexit's cone; `iget` is unproven (its `CodeIget.v` was generated once and
REVERTED — regenerating rewrites the shared `KernelDecode*.v` shards; use
the full-generator-into-scratch recipe in durable-notes, never `--only`).

## Strategy

Cycle 1 is additive and lands on main. Cycles 2–3 change five landed
contracts and their proofs together — do them on a short-lived branch
(precedent: `park-to-lock`), keeping main green, and merge each cycle
only when the whole tree builds. Definitions/specs are orchestrator
(Fable) work; whole-function proof reworks go to Opus subagents with the
recipes below.

## C1 — the region + log_write's AU form (DONE, committed bc377b06)

- [x] `InodeRegion.v`: `dinode_at`, the one-armed region invariant
      (`ireg_inv`), `ireg_read`, `ireg_write_au`, `diblk_bytes_inj`.
- [x] `SpecLogWrite.v`: `wp_log_write_au_body` + the `wp_log_write_au`
      parameter in `Module Type LOG_WRITE`.
- [x] `ProofLogWrite.v`: main lemma retargeted to the AU form (the
      receipt abstracted as a new opaque `Fb` binder beside `Bud` on
      `lw_cont`/`lw_res` and the block lemmas — their proofs untouched;
      the ghost step at ~2082 opens with `iApply fupd_wp`, the tree's
      idiom, cf. ProofInitlog.v:664); `wp_log_write_gen` derived from it
      at `Efs := ⊤`; `wp_log_write_sconf` unchanged.
- [x] Full build green (EC2 -j30, 0 Errors, lemma_diff clean).

## C2 — iupdate onto `dinode_at` (DONE 2026-08-09, six files, clean
## remote build 906 .vo / 0 errors, lemma_diff clean vs bc377b06)

Findings worth keeping (the recipes below were followed and worked;
deltas from them):

- **`SpecWritei`'s region record is TWO-armed**: writei's `-1` early
  return (`off > size` / `off+n > MAXFILE*BSIZE`) never reaches iupdate,
  so the continuation's existential is `dn0'` with `dn0' = dn0` on the
  error arm and `dn0' = dn'` on the flush arm. An unconditional
  `dinode_at γi inum dn'` postcondition is UNPROVABLE — remember this
  shape for every future contract over a function whose flush is
  conditional (iput's truncate arm will meet it too).
- **No opaque receipt binder was needed in ProofIupdate** (unlike C1's
  `Fb` in ProofLogWrite): the receipt is the concrete
  `dinode_at γi inum dn`, so the interior continuation bundle names it
  directly. The binder trick is only for universally-quantified Φ.
- **`ProofIupdate.iu_held_L`** (lines ~160–186) is the extract/restore
  pair for the payload's machinery `fs_L` half over both polarities —
  `ProofLogWrite.lw_pay_split` is sealed inside its module and NOT
  reusable. C3's ilock read needs the same move: use `iu_held_L` as the
  model (or lift it somewhere shared).
- `ProofItrunc` keeps its interior `Hrange` hypothesis verbatim: the
  main lemma re-derives it from `cov_below` via
  `IcacheInv.blkmap_slot_inrange` in three lines; the five inner lemmas
  and the bfree call sites are untouched. Cheaper than threading the new
  premise down.
- `SpecItrunc`'s length premise was ALREADY narrowed to `i < MAXFILE`
  in the landed file — design §6(ii)'s "necessary narrowing" note
  described its own past. Only the range premise (i) actually moved.

Original plan (kept for the record):

**SpecIupdate v2** (the statement delta, worked out):
- drop the `(ds : list dinode)` parameter and the `diblk_wf ds` premise —
  `ds` becomes proof-internal, learned at bread time via `ireg_read`;
- add `(γi : gname) (nib : nat)` and a `(dn0 : dinode)` parameter (the
  stale on-disk record — it need not equal the in-memory `dn`);
- add premise `bv_unsigned inum < 16 * Z.of_nat nib`;
- swap resource `fsblock γfs (IBLOCK inum inodestart) (diblk_bytes ds)`
  for `ireg_inv γi γfs inodestart nib ∗ dinode_at γi inum dn0`;
- postcondition's fsblock line becomes `dinode_at γi inum dn`.

**ProofIupdate rework recipe** (the three touch points, from reading the
landed proof):
1. `iu_held_content` at ~line 983 (learning `bs = diblk_bytes ds` from
   the caller's fsblock against the handle) is replaced by `ireg_read`:
   extract the machinery half `(uint bno) ↪[fs_L γfs]{#½} bsl` from the
   handle's `bio_pay` (BOTH polarities carry it — clean is `fs_mclean`,
   dirty is `fs_mdirty ∗ ∃q bref`), fire `ireg_read`, restore. Its pure
   output (`∃ ds, diblk_wf ds ∧ bsl = diblk_bytes ds ∧ ds !!! islot inum
   = dn0`) replaces today's `Hbs0` + the `diblk_wf ds` premise.
2. The `LW.wp_log_write_sconf` call at ~line 277 becomes
   `LW.wp_log_write_au` with `Efs := ⊤ ∖ ↑iregN`, `Φfsb := dinode_at γi
   inum dn`, discharging the AU premise with `ireg_write_au` (whose
   `dinode_wf dn` premise is derivable: `di_addrs dn = bm_cells bm` +
   `length (bm_dir bm) = NDIRECT` give `length (di_addrs dn) = 13`).
3. The postcondition assembly hands back `dinode_at` where it handed
   `Hfsb`.

**Same-stroke spec swaps** (they thread the block down to iupdate):
`SpecItrunc` (fsblock premise at :275, post at :312 — becomes
`dinode_at γi inum (di_trunc dn)`) and `SpecWritei` (premise :350, post
:431 at its flushed record) — swap for `ireg_inv + dinode_at` exactly
as above; narrow `SpecItrunc`'s unbounded length premise to
`i < MAXFILE` and swap its owed per-slot range hypothesis for
`cov_below cov size` while in there (design §6 — ProofItrunc then
derives the per-slot facts via `IcacheInv.blkmap_slot_inrange`). Both
have landed proofs (`ProofItrunc` 2798, `ProofWritei` 4004) — each
repairs at its `wp_iupdate_sconf` call site (ProofItrunc.v:316,
ProofWritei.v:833) and threads `γi/nib/dn0` up into its own statement.

**NOT C2: `SpecFileread`.** Its fsblock (:326/:349, inside the
`frn_*` FD_INODE environment) feeds its ILOCK call, not iupdate — it
swaps with SpecIlock in C3, and `ProofFileread` repairs there.

## C3 — the per-entry escrow, the pool, and ilock/iunlock (branch)

Design §10 stands, EXCEPT §12.5: the escrow is probably TWO-armed
(parked / checked out) — the mid arm's job evaporates because iget's four
stores hit four different homes in the landed architecture. Verify
against the image first (§12.5 has the obligation), then build two-armed.
The work: the escrow over `i_valid` + the sleeplock payload (the entry's
sleeplock keeps only the checkout token, and the SLEEPLOCK credential
makes this escrow statable where the region's was not); the uncached
pool inside `itable_res` carrying, per uncached inum, `dinode_at + 
ind_res + inode_blocks + inode_ok`; InodeLock C1 (unloaded arm owns
nothing; two-state shadow `option (dinode * blkmap)`) and C2; SpecIlock/
SpecIunlock v2 (swap the unsatisfiable `i_ref ↦{dqr}` premise for
`itable_inv + iref_tok` (§4), add the escrow share, take `dinode_at`
instead of the block+`ds !!! islot inum = dn` premise — which DISAPPEARS,
§11.3). Then the `il_load` half of `ProofIlock.v` (1930 lines) re-proves
against the new seam (Opus; the instruction-level work is untouched —
only where the block resources come from moves).

## C4–C6 — idup ripple check, iget, iput

- C4: `idup` never touches dinode blocks or the sleeplock payload —
  expect zero ripple; verify by build.
- C5: regenerate `CodeIget.v` (FULL generator into a scratch dir, copy
  out, verify byte-identical siblings + addition-only shard diffs, add
  the manifest row), then `SpecIget`/`ProofIget`: the scan
  (`ientry_step`/`ientry_sentinel`), `iref_alloc_step`, the recycle
  window (escrow mid arm), and the pool hand-off of the recycled inum's
  bundle.
- C6: `SpecIput`/`ProofIput`: REF-1 (`iref_lookup`), both close steps,
  the escrow opening for the two lock-free loads, the truncate arm.
  Retires `LinkIput.v`'s axiom and the last fs-side assumption in
  kexit's cone.

## C7 — the boot wiring (`ireg_alloc` + pool stocking)

IN SCOPE (user-confirmed 2026-08-09), after C6. One seam, two halves:

- `ireg_alloc`: from the boot-time `fsblock` big-op over the inode
  blocks (out of `FsBoot.fs_alloc`'s partition), build the initial
  region map and mint every `dinode_at`, allocating `ireg_inv`. The
  caller must exhibit `dss : list (list dinode)` with `Forall diblk_wf`
  and the image bytes AT `diblk_bytes` of them — i.e. a pure decode of
  the mkfs image's inode blocks; that existence layer is part of this
  cycle. Stated as owed in `InodeRegion.v`'s header.
- Pool stocking: `itable_res`'s uncached-inum bundles (`dinode_at +
  ind_res + inode_blocks + inode_ok`) come from the same partition, at
  iinit's `newlock` — which is what lets iinit link into main. Read
  `ireclaim` before designing the initial contents (it is fsinit's
  single-threaded orphan sweep, the one caller that can establish them).

## Deferred / owed
- The `fsblock`-carries-its-length fold (design §6(ii), better home) —
  whoever next touches `FsBlocks.v`.
- `FileInv.inode_ref`/`ProcInv.cwd_ref` placeholders → `IcacheInv.inode_ref`
  via an `icacheG`-carried gname (design §3's recorded choice).
