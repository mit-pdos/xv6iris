# TSO port: LIVE HANDOFF CHECKPOINT (2026-08-28, credits-limited session)

This file is the resumption point for a FRESH agent taking over the TSO
port coordination.  It is updated at green boundaries; trust the newest
git commit of it on branch `tso`.  Read `claude-notes/README.md`,
`durable-notes.md`, `remote-build-gcp.md` (note the NEW leaked-rocqworker
gotcha at the end), then `projects/tso-port.md` rulings §0.23′–§0.40′,
then this file.  The A6-series (`tso-machine-flip.md`), K-series
(`tso-kpt-lane.md`), and intr notes (`tso-intr-lane.md`) are the measured
record; `main-tso-readiness.md` is the separate main-side handoff (its
own agent, its own credits — not this resumption's job).

## The three trees (all /shared or durable; all baseline-certified)

1. **PRIMARY fliptree** (lock lane's): `/tmp/claude-0/-shared-xv6iris-3/
   861bc642-1d31-482b-8fd8-39183ee1abdd/scratchpad/fliptree` — WARNING:
   tmpfs, session-scoped.  Durable mirror `/shared/xv6iris-3-fliptree-backup`
   (rsync'd at every green boundary; verify freshness vs the snapshots).
   GitHub: branch `tso-flip`, snapshot commits through `9b288a06c`+
   (check `git log origin/tso-flip`).  Last certified: r27, 1100/1296,
   RED 9.  The lock lane has UNCOMMITTED work past r27 inside
   `WpSconfLock` (the indivisible closing unit) — if the lane died, its
   tree state is the mirror/snapshot plus whatever WpSconfLock.v edits
   survive in the tmpfs tree; the unit is re-derivable from A6.111–A6.118
   (all committed).
2. **KPT tree**: `/shared/xv6iris-3-kpttree` — FROZEN mid-K15d (lane
   killed for orphaned rocqworkers, not for its work).  Certified r34:
   1102/1340, RED 9, all four openers off the invariant's tree.
   UNCERTIFIED edits past r34: `kpt_body`'s tree-drop is already written
   (KptShare.v — verified present), opener threading partially done,
   `ProofMain` untouched.  Remainder = K15d steps as written in
   tso-kpt-lane.md (K15d list), then ProofMain:996 + ProofMainSecondary.
   Cumulative merge list (all lane-owned, disjoint from lock lane):
   PhysSeen.v + KptCtxTravel.v (new), PtTree, HartSKpt, KptShare,
   SRegime, ProofKvminithart, KptTree, Pt2Walk, TransPt, UserFetchCert,
   UptTree, SmodeCorePt, WpSconfSfence, _CoqProject.
   Remote build dir: `_shared_xv6iris-3-kpttree` on the VM (green build
   of r34-adjacent state; incremental resume).
3. **INTR tree**: `/shared/xv6iris-3-intrtree` — PARKED clean.  Only
   `iris/SpecDevintr.v` modified (additive CapsFresh section) +
   scratch ZZintrbuild.sh.  Fresh .vo pulled (local probes valid HERE
   only).  Blocked on the M3 λ-conversion (in the lock lane's queue).
   Remote dir `_shared_xv6iris-3-intrtree`.

Main repo `/shared/xv6iris-3` (branch `tso`): notes only; everything
committed and pushed.  The tso branch = the M-leg, fully green, 1331
files — do not confuse with the fliptree.

## Lane states and queues

**LOCK LANE** (running at checkpoint time; agent context in this
session only — a fresh agent CANNOT resume it, only re-derive):
inside WpSconfLock's indivisible unit.  DONE (r29 certified for the
TsoCtx/WpLock halves; the WpSconfLock pieces compile in-file): the
∃-form window swap (ledger_read_racy_ok/_word_ok/lkcpu_read_not_mine
take [∗list] j, ∃tj — the ts-function spelling was the outlier),
lk_cpu_cell_ex_pay + lk_own_ok_some, and BOTH READS — notheld
(lock_cell_read_notheld → wp_ld_lkcpu_notheld_gen → the _s_sconf leaf
on lock_openable_c, A6.92's refuted premise retired in place) and the
holder read.  Design note: an existential crossing an atomic update
must be pinned outside it or carried whole through it — hand the whole
lock_body through Res (the A6.109 lo-hoist one level up).  The unit then went THROUGH the cpu-store family and into the word-pin
redesign (A6.92's refutation reached lock_body via the AMO's failing
branch): the authorship arm is OUT of lock_body, the word carries
lock_word_pin (value-set {1}, pin instrument — pin for
same-value-many-writers vs TsWin for distinct-values-per-writer), the
ghost lockUR went PRODUCT (state x acquire-position; lock_pos_agree the
tie; arities preserved), ledger_pin_drop is the retraction (release =
retract-then-store), and locked/locked_pre carry
∃B, lock_frag_at γ _ B ∗ ctx_floor cur_ctx B (§0.34′ realized on the
ξ-axis; boundary note rewritten at the definition).  ALL certified
through r34 + WpLock/WpLockAt green after.  REMAINING (itemised, no
design left).  DONE SINCE: the mint+export (uncoupled from CtxPinMint
— hart_view_lb_get at T:=0, "the acquirer's own view IS the
position"), BOTH READS (holder via ledger_read_pin_bytes_ok —
§0.35′(iv) case 2 DISCHARGED; the nonzero fact travels inside Res
beside the pin — the AU rule's fourth manifestation), and
lock_take/lock_give at the new arities.  REMAINING (all wiring,
instruments in hand): (1) release retract-then-store at
WpSconfLock:874 (lock_word_pin_drop then the free-word gate,
replacing lock_word_ex_forget); (2) spinner preservation on the
failing AMO branch (ledger_store_win_pin_ok, premise from rget=1);
(3) the failing-branch close; (4) the WpSconfLock/WpLockAt re-cut
tail + the 69-file sweep as arity verification + sentinel + A6.119.  Then (5) the
SpecAcquire threading and (6) close + cone sweep as before.
Then: (5) lock_openable_c threading through SpecAcquire's ~40 callers;
(6) close WpSconfLock + sweep the cone (~160 files); DMA AU leaf +
virtio pair (A6.95: ready, datum phys_word2, claims from
kmap_static_claims, agent-generic gates); M3 λ-CONVERSION of the four
payloads (proc_lock_res/disk_res/ticks_res/cons_res — gate for §0.27′
AND the intr lane; measured surface in tso-intr-lane.md) + the TsoCtx
freshpack lemma (statement in tso-intr-lane.md); §0.27′ → ProofSwtch.
Everything through A6.118 is committed; the unit's remaining content is
fully specified by A6.111–A6.118.

**KPT LANE** (killed; resumable as a fresh lane on the KPT tree):
remainder = K15d steps 1–5 (verbatim in tso-kpt-lane.md, including the
one further deferred-cone statement change covered by the K14 exit-(2)
exception).  Then goalpost 3 closes.

**INTR LANE** (parked): resumes AFTER the λ-conversion lands; its
far-side pieces (CapsFresh, the arity-preserving contract spelling) are
in its tree + notes.  §0.39′ + the identity finding: tso-intr-lane.md.

## The three-case gate (§0.25′) at checkpoint

Case 1 (spinlock): design complete (§0.35′/§0.38′ + A6.110–118), ~70%
of leaves Qed, the closing unit in flight.  Case 2 (first/park): heart
Qed, ProofForkret green; ProofSwtch behind §0.27′ (behind the lock
queue); ProofForkretPark = re-measure AFTER §0.27′ (may have become
mechanical — the buy/carry/cash machinery postdates its
characterization).  Case 3 (started): one-to-two boundaries out —
K15d's tail then ProofMain.  RED 9 everywhere:
ProofForkretPark, ProofKernelvec, ProofMain, ProofSwtch,
ProofVirtioDiskIntr, ProofVirtioDiskRwD, UptWalkPt*, UserMemPt*,
WpSconfLock  (* = deliberately red, §0.37′ — do not fix).

## Merge topology (when lanes finish)

All three lanes' file sets are DISJOINT by contract (ownership lists in
the lane prompts, reproduced in the notes).  Merge = copy the KPT
lane's 15 files + the intr lane's SpecDevintr.v into the primary
fliptree, rebuild, certify a clean round (rm .vo), refresh the mirror,
snapshot to tso-flip.  Two shared-boundary cautions: (a) the KPT lane's
IntrDefs/UsertrapRes/TsoCtx needs were all resolved WITHOUT editing
those files — verify no stray edits before merging; (b) after merging,
re-run the destructuring-pattern audit near changed definitions (K15's
finding: greenness after a definition change is not evidence a call
site was reviewed).

## Coordinator duties (what this session's coordinator did; do the same)

- Commit lane notes to `tso` at every report; push.
- Snapshot the primary tree to `tso-flip` at green boundaries via the
  temp-index recipe (GIT_INDEX_FILE + git --work-tree add -A + drop
  blobs >40MB — iris/.lia.cache is 222MB — commit-tree -p <prev>).
- rsync the mirror at green boundaries.
- Route cross-lane needs; never let a lane edit a foreign file.
- Owner-ruling protocol: characterize + surface; record rulings as
  §0.x′ in tso-port.md; refutations recorded in place.
- Process law: measure before designing; grep for the law before
  building it; sentinel-backed numbers only; the stale-.vo trap; the
  rocqworker hygiene mandate (remote-build-gcp.md tail).

## Open owner items at checkpoint

None pending ruling.  Deferred: §0.37′ (U-mode pair, waits on main's
user-mode rework).  Future decisions: ProofForkretPark re-measurement
(post-§0.27′); the adequacy tail; the C-leg cutover gate (§0.23′/0.25′:
main moves once, after the gate); the main-side slices run by a separate
agent off main-tso-readiness.md.
