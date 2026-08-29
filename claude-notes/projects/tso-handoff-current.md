# TSO port: LIVE HANDOFF CHECKPOINT (2026-08-28, evening session #2)

This file is the resumption point for a FRESH agent taking over the TSO
port coordination.  It is updated at green boundaries; trust the newest
git commit of it on branch `tso`.  Read `claude-notes/README.md`,
`durable-notes.md`, `remote-build-gcp.md` (note the leaked-rocqworker
gotcha at the end AND the new `--pull`/`--delete` gotcha below), then
`projects/tso-port.md` rulings §0.23′–§0.40′, then `tso-machine-flip.md`
A6.119–A6.120, then this file.  The A6-series (`tso-machine-flip.md`),
K-series (`tso-kpt-lane.md`), and intr notes (`tso-intr-lane.md`) are the
measured record; `main-tso-readiness.md` is the separate main-side handoff.

## The trees (all durable now)

1. **PRIMARY fliptree**: `/shared/xv6iris-3-fliptree` (durable; the old
   tmpfs tree under `/tmp/claude-0/…/861bc642…/scratchpad/fliptree` is a
   stale r37 copy and can be ignored).  Remote build dir on the VM:
   `/mnt/rocq/trees/_shared_xv6iris-3-fliptree` (cloned from the lock
   lane's warm tree; incremental).  Durable mirror
   `/shared/xv6iris-3-fliptree-backup` (rsync'd at green boundaries).
   GitHub: branch `tso-flip`, snapshot `820ae4406` = r39 (A6.121; r38 was
   `619c23287`) (snapshots via the
   temp-index recipe; `ZZchain.sh <File>…` at the tree root rechecks files
   locally in order against pulled `.vo`).
   Build driver: `ZZbuild.sh` at the tree root (the intr lane's, log names
   suffixed `.aux` -- see the gotcha).  **Last certified: r41 (CLEAN round), 1183 .vo of 1298, red roots 8, zero admits (A6.124: the avail-index word is on the ledger -- lease split + payload half; `ProofVirtioDiskRwD`, `RwE`, `RwDSeam` GREEN; the new red root is `ProofVirtioDiskRwF:365`, the pin-return crossing, characterized and sized in A6.124).**  Snapshot `6168b7303` = r41; **r42 = `61fb20680`** (A6.125 step 1, the `TsoCtx` half-ctx-cell bricks, root change only: 1183/1298, same 8 roots); **r43 = `6304d4c92`** (A6.125 step 2: `VirtioProto`'s hole is the whole control set at ½, publish takes a PIN OFFER and returns the memory half -- A6.125's step-2 entry; 1183/1298, same 8 roots).
2. **KPT tree**: `/shared/xv6iris-3-kpttree` — FROZEN mid-K15d, unchanged
   this session EXCEPT one mirrored hunk: `iris/SmodeCorePt.v`'s
   `word_pointsto_wpay_mint_c` gained the trailing own-message fragment
   conjunct (A6.120 §6) so the eventual merge is a no-op there.  Everything
   in the previous checkpoint about it still holds (certified r34, K15d
   remainder, merge list).
3. **INTR tree**: `/shared/xv6iris-3-intrtree` — PARKED clean, unchanged.

Main repo `/shared/xv6iris-3` (branch `tso`): notes only.

## NEW GOTCHA (2026-08-28): `run-on-gcp --pull <file>` pushes first, with `--delete`

Every `run-on-gcp` invocation without `--no-sync` rsyncs the local tree to
the VM with `--delete`; a remote-only file (a build log written on the VM)
that matches no `ROCQ_EXCLUDES` pattern is DELETED by the next sync -- and
`--pull <file> <cmd>` syncs before it pulls, so it deletes the very file it
was asked to fetch.  Measured: a whole round's log lost.  Rule: write remote
logs under an excluded name (`*.aux` -- `ZZbuild.sh` now writes
`ZZ-iris.log.aux` / `ZZbuild.out.aux`) and read them with
`run-on-gcp --no-sync bash -c 'grep … ZZbuild.out.aux'`.

## Round-launch gotchas (2026-08-29, A6.124; cost ~40 min once)

The wrapper is `/shared/xv6iris-3/gcp-rocq/run-on-gcp` (not in the fliptree;
run it with the fliptree as `$PWD`).  rsync DROPS `ZZbuild.sh`'s exec bit --
launch as `bash ./ZZbuild.sh`.  A detached `nohup`/`setsid` launch dies with
the ssh session; launch under tmux:
`run-on-gcp bash -c 'D=$PWD; tmux kill-session -t zz 2>/dev/null; rm -f ZZbuild.out.aux; tmux new-session -d -s zz "cd $D && bash ./ZZbuild.sh > ZZbuild.out.aux 2>&1"'`
and poll `run-on-gcp --no-sync bash -c 'grep -q DONE ZZbuild.out.aux'` (a
warm round is ~5–10 min).  `GREEN=` counts stale `.vo`s of files whose
recompile FAILED (the old `.vo` survives), so read the red ROOTS from
`grep -n -B4 "^Error" ZZ-iris.log.aux | grep 'File "'` and certify with a
clean round.  Fast loop for one file: `run-on-gcp --pull-vo true` then
`./ZZchain.sh <File>` (both `ZZ*.sh` need `chmod +x` locally after a restore).

## Lane states and queues

**LOCK LANE** (this session's; a fresh agent resumes from the tree + notes):
**r38 GREEN BOUNDARY.**  A6.119 §8's two acquire-side items are CLOSED
(A6.120): (1) `ProofRelease`'s cancel path — `WpLock.lock_finisher` is
two-part (prelude at entry, body at the store); (2) `ProofAcquire`'s
pre-AMO floor — `lk_floor`'s right arm is now the ctx tower's own dirty
witness (`TsoCtx.ctx_wrote`), cashed on either arm by `WpLock.lk_floor_vis`,
so the notheld read takes the plain `lock_openable`, `lock_openable_c` is
retired in place, and **the old queue's item (5) (`lock_openable_c` through
`SpecAcquire`'s ~40 callers) and its ~160-file sweep are CANCELLED**.  The
AMO leaf exports the parked record with its floor (`lock_pay_won`) and
acquire absorbs by `TsoCtxAbsorbLb.ctx_absorb_lb`.  `ProofPipeclose`'s
residue (`pipe_bytes_page_own` on the ctx word) re-cut.  Twelve files
touched, all this lane's, plus the mirrored `SmodeCorePt` hunk (A6.120 §6).

**A6.121 (r39): the M3 λ-conversion is DONE for `ticks_res`, `cons_res`,
`disk_res`** (explicit-context twins `*_at` with real `CtxMorph` proofs,
`CtxMorphTac.v`'s driver, 197 sites renamed, zero consumer proof edits).
`proc_lock_res` (44 sites) waits for §0.27′ (its slots hold `▷ proc_ctx`);
`wait_res` (38 sites) unmeasured.

**A6.124 (r41): the virtio AVAIL side is DONE** -- `VirtioProto`'s lease
has a hole at the index word and holds its cells at ½ (`dma_own_x`,
`avail_lease_half`); the payload's ½ with exposed stamps + `lk_floor`s is
`DiskAvail.avail_half` (new file, `disk_res`/`vdrw_body`'s LAST conjunct,
`CtxMorph` via `lk_floor_morph`); the holder reads with its own half
(`avail_half_read_ok`, no invariant for the value), the publisher joins,
stores through `wp_store_s_sconf_au_dat`, registers (`ctx_wrote_register`)
and re-splits.  `ProofVirtioDiskRwD` + `RwE` + `RwDSeam` green.

**Next queue (lock lane), in order:**
1. **The slot cells on the ledger (the pin-return crossing; A6.124's
   surfaced item).**  `ProofVirtioDiskRwF:365`: the payoff's formatted
   descriptor/info cells come back SEALED and `↦₂/↦₄/↦₈` are ctx words;
   the forget-with-floor is not reversible on the dirty arm (a `ctx_wrote`
   witness is discarded, `ctx_phys_pointsto_def`'s dirty arm is the FULL
   element).  Recommended shape (a): the avail unit's pattern for
   `disk_slot`'s cells -- lease ½ sealed, payload ½ exposed + `lk_floor`,
   RwD's formatting stores through `_au_dat` with one obligation per width
   (`vdrwd_avail_store_ok`'s shape), `VdrwdPinBuild` splits instead of
   forgetting, RwF §1's bridges deleted.  Sized in A6.124.  **Steps 1–2 of
   the (b′) plan are LANDED (r42, r43); next is step 4 (RwD's pin builder
   keeps `ts ½ + arm` per cell -- `keep_map` -- and rebuilds
   `ctx_phys_pointsto_h` from `pin_back`), then 3 (`flight_res`/`parked_res`
   carry the ctx halves), 5-OUT, 6.**  **RE-MEASURED
   in A6.125: build shape (b′) "half ctx cells" instead** -- the ctx side
   keeps ½ + its arm (`TsoCtx.ctx_phys_pointsto_h`, transports exactly like
   the full cell because `ctx_morph_pointsto` drops the dirty fragment),
   the lease keeps ½ sealed under a generalized hole (`avail_idx_dom ∪
   pins_dom`); RwC's 17 formatting stores are untouched.  Six steps and
   their order are in A6.125.  Greens RwF's §1 and the OUT withdraw; the
   IN buffer (device-written) still needs item 2's instrument, so RwF is
   green only with both.  `LinkVirtioDiskRw` also waits on `LinkSleep` ← §0.27′.
2. **FOR THE OWNER (A6.122 §3): the virtio USED index needs a MONOTONE-CELL
   instrument** (a third `ts_pay` arm: since `B`, one author, non-decreasing
   values) — the pin cannot carry a stale reader's lower bound, measured
   against every re-floor placement.  Σ-level; wants a §0.x′ ruling before
   anyone builds it.  `ProofVirtioDiskIntr` stays red until then.
3. **§0.27′ → `ProofSwtch`** (`:157` still names the retired
   `hart_view_lb_any`; the parked record now arrives at the winner with
   `ctx_parked`), together with `proc_lock_res`'s λ-conversion (the `▷`
   in its slots is this ruling's business).
4. `ProofKernelvec:1704` (§0.39′), then `ProofForkretPark` re-measure
   (post-§0.27′).
Then the KPT lane's K15d tail + `ProofMain:996`, and the merge.

**KPT LANE** (killed; resumable as a fresh lane on the KPT tree):
remainder = K15d steps 1–5 (verbatim in tso-kpt-lane.md), then `ProofMain`.
At merge, `SmodeCorePt.v` already carries A6.120's hunk in both trees.

**INTR LANE** (parked): resumes AFTER the λ-conversion lands.

## The three-case gate (§0.25′) at checkpoint

Case 1 (spinlock): **the lock tier is green end to end** — `WpSconfLock`,
`ProofHolding`, `ProofAcquire`, `ProofRelease`, `ProofPipeclose`, and every
lock consumer the compiler reaches; the only lock-tier text still unreached
is behind the eight reds above (virtio, swtch, kernelvec, main, the U-mode
pair).  Case 2 (first/park): unchanged — `ProofSwtch` behind §0.27′,
`ProofForkretPark` re-measure after.  Case 3 (started): K15d's tail then
`ProofMain`.  **RED ROOTS 8 (r41)**: ProofForkretPark:298, ProofKernelvec:1704,
ProofMain:996, ProofSwtch:157, ProofVirtioDiskIntr:1166, ProofVirtioDiskRwF:365
(new; queue item 1), UptWalkPt:679*, UserMemPt:427*
(* = deliberately red, §0.37′ — do not fix).  `ProofVirtioDiskRwD` is
green (A6.124).

## Merge topology (when lanes finish)

Unchanged from the previous checkpoint: copy the KPT lane's 15 files + the
intr lane's `SpecDevintr.v` into the primary fliptree, rebuild, certify a
clean round (rm .vo), refresh the mirror, snapshot to `tso-flip`.  Cautions:
(a) verify no stray KPT edits to `IntrDefs`/`UsertrapRes`/`TsoCtx`; (b)
re-run the destructuring-pattern audit near changed definitions; (c) NEW:
`TsoCtx.own_context_def` is unfolded in `KptCtxTravel.v` (3 sites) and
`CtxPinMint.v` (1) — A6.120 did NOT change the token's definition (only
added lemmas beside it), so those are safe, but re-check on merge.
(d) A6.121 renamed `<{ disk_res … }>` sites in 89 files; the KPT lane's 15
files are not among them (none names the four payloads), but `_CoqProject`
gained `CtxMorphTac.v` after `TsoCtx.v` — merge that line.

## Coordinator duties (what this session's coordinator did; do the same)

- Commit lane notes to `tso` at every report; push.
- Snapshot the primary tree to `tso-flip` at green boundaries via the
  temp-index recipe (GIT_INDEX_FILE + `git --work-tree=<tree> add -A -f .`
  + drop blobs >40MB — iris/.lia.cache is 222MB — `commit-tree -p <prev>`,
  `update-ref refs/heads/tso-flip`, push).  Pull the VM's `.vo` first so
  the snapshot and the mirror carry a build that matches the sources.
- rsync the mirror at green boundaries.
- Route cross-lane needs; never let a lane edit a foreign file (the ONE
  exception this session, A6.120 §6, was mirrored into the other tree the
  same minute and recorded).
- Owner-ruling protocol: characterize + surface; record rulings as
  §0.x′ in tso-port.md; refutations recorded in place.
- Process law: measure before designing; grep for the law before
  building it; sentinel-backed numbers only; the stale-.vo trap (a local
  recheck past a changed root needs the VM's `.vo` pulled first, and even
  then only the files whose deps are all fresh); hoist every side condition
  out of `ltac:` application position (A6.119/A6.120 — it bit three times
  this session); the rocqworker hygiene mandate.

## Open owner items at checkpoint

**ONE for ruling: A6.122 §3 — the monotone-cell ledger instrument the
virtio used-index read needs (a Σ-level `ts_pay` arm).**  For the owner's
veto (A6.120): the creator's arm
of `lk_floor` is now spelled as the ctx tower's dirty-map witness rather
than a bare log position — the composition of §0.38′ (received-or-wrote)
and §0.36′(a) (the author rides its own write), and the reason the ~40-caller
threading was never needed.  Deferred: §0.37′ (U-mode pair, waits on main's
user-mode rework).  Future decisions: ProofForkretPark re-measurement
(post-§0.27′); the adequacy tail; the C-leg cutover gate (§0.23′/0.25′);
the main-side slices run by a separate agent off main-tso-readiness.md.
