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
   GitHub: branch `tso-flip` (snapshots via the temp-index recipe).
   Build driver: `ZZbuild.sh` at the tree root (the intr lane's, log names
   suffixed `.aux` -- see the gotcha).  **Last certified: r38, 1178/1296, RED 8, zero admits (A6.120).**
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

**Next queue (lock lane), in order:**
1. **DMA AU leaf + the virtio pair** (A6.95: ready — datum `phys_word2`,
   claims from `kmap_static_claims`, agent-generic gates).  Both virtio
   files fail on the same pre-flip residue: `ProofVirtioDiskRwD:686` /
   `ProofVirtioDiskIntr:1165` want `wordw_pointsto 2 … -∗ wordw_claim 2 …`
   and hold `word2_pointsto` — the M4-shaped store leaf for the 2-byte
   queue words.
2. **The M3 λ-conversion** of the four payloads (`proc_lock_res` /
   `disk_res` / `ticks_res` / `cons_res`) + the `TsoCtx` freshpack lemma
   (statement in tso-intr-lane.md) — the gate for §0.27′ AND the intr lane.
   Note for it: a payload carrying a nested `is_lock` now transports its
   floor on BOTH arms for free (`ctx_floor_dom`, `ctx_dom_wrote_floor`), so
   a `CtxMorph` instance for `is_lock` is provable without any absorb
   capability — A6.116 §3's question is moot.
3. **§0.27′ → `ProofSwtch`** (`:157` still names the retired
   `hart_view_lb_any`; the parked record now arrives at the winner with
   `ctx_parked` — §0.27′'s prerequisite, per A6.119).
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
`ProofMain`.  **RED 8**: ProofForkretPark, ProofKernelvec, ProofMain,
ProofSwtch, ProofVirtioDiskIntr, ProofVirtioDiskRwD, UptWalkPt*, UserMemPt*
(* = deliberately red, §0.37′ — do not fix).

## Merge topology (when lanes finish)

Unchanged from the previous checkpoint: copy the KPT lane's 15 files + the
intr lane's `SpecDevintr.v` into the primary fliptree, rebuild, certify a
clean round (rm .vo), refresh the mirror, snapshot to `tso-flip`.  Cautions:
(a) verify no stray KPT edits to `IntrDefs`/`UsertrapRes`/`TsoCtx`; (b)
re-run the destructuring-pattern audit near changed definitions; (c) NEW:
`TsoCtx.own_context_def` is unfolded in `KptCtxTravel.v` (3 sites) and
`CtxPinMint.v` (1) — A6.120 did NOT change the token's definition (only
added lemmas beside it), so those are safe, but re-check on merge.

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

None pending ruling.  **For the owner's veto (A6.120):** the creator's arm
of `lk_floor` is now spelled as the ctx tower's dirty-map witness rather
than a bare log position — the composition of §0.38′ (received-or-wrote)
and §0.36′(a) (the author rides its own write), and the reason the ~40-caller
threading was never needed.  Deferred: §0.37′ (U-mode pair, waits on main's
user-mode rework).  Future decisions: ProofForkretPark re-measurement
(post-§0.27′); the adequacy tail; the C-leg cutover gate (§0.23′/0.25′);
the main-side slices run by a separate agent off main-tso-readiness.md.
