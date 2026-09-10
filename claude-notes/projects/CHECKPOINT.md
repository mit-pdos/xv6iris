# CHECKPOINT (2026-09-10) — resume here

Written by the coordinator session that ran PID-ROW → PINNED-EXEC → EXEC-CHANNEL →
EXEC-ARGS → STD-LEDGER → ARM-c (1a) → WX-KEY → WX-FORK, while WX-RES phase 2 was
running.  Design of record and every landed note: `projects/app-echo.md` (read
"WAIT-EXIT — DESIGN OF RECORD" and the LANDED notes above it, newest first).
Briefs (the exact instructions each lane agent ran on) and the WX-RES phase-1 WIP
patch: `projects/wx-briefs/`.

## State of main at this checkpoint
- origin/main = local HEAD (`51f7ae907`, a notes commit) is GREEN: full VM build,
  `make audit-only` = the thirteen assumptions, `tools/lemma_diff.py` clean.
- Landed today: WX-KEY (`987f79afd`), WX-FORK (`901f9aba5`, rebased over a
  nightly dead-import sweep `086c81b9f`).

## State of the WORKING TREE at this checkpoint (2026-09-10, later)
- The tree is DIRTY with WX-RES phase-2 WIP: 23 modified iris/*.v (backup
  `wx-briefs/wxres-p2.patch`, apply with `git apply` onto `51f7ae907`/`e90eacb4c`
  if the tree was cleaned).  Build `wxres6`: COMPILED=1010, EXIT=2, FOUR red roots
  (`ProofKforkB5.v:~320`, `ProofUserinit.v:~809`, `ProofSyscall.v:~1743`,
  `ProofUsertrapSys.v:~291`).  Everything else in the lane is landed and green (see
  `wx-briefs/brief-wx-row-res-finish.md` "STATE").
- WX-RES stopped on a STRUCTURAL blocker: kfork seals the child's residue at its
  first `release(&np->lock)` before it takes `wait_lock`, so it cannot install the
  child's children row; main cannot name init's slot either.  RULED (P): rows are
  per-slot, born at boot by `wait_res_alloc` (NPROC rows), riding the DORMANT block
  exactly as the descriptor ghost does; allocproc hands the row out and writes its
  name into `pv_chg`; freeproc returns it; `children_own_install/_del` die.  That is
  lane WX-ROW, folded with the WX-RES finish into ONE brief:
  `wx-briefs/brief-wx-row-res-finish.md`.  An agent may have been launched on it.

## WX-ROW phase 1 (later still): rulings given for phase 2
- Tree: the WX-RES WIP plus the dispatcher relay landed green (`ProofSyscall`,
  `ProofUsertrapSys`, `ProofUsertrap`); TWO red roots (`ProofKforkB5.v:~320`,
  `ProofUserinit.v:~809`).  Backup `wx-briefs/wxrow-p1.patch`.
- RULED: the children map's name becomes CANONICAL (class-carried `wch_name` on
  `Xv6Cameras.wchG`, minted in the boot fupd beside `fd_slots_alloc`/`bslots_alloc`;
  the `fdslot_name`/`pav_name`/`bioslot_name` precedent) so `ProcDefs` can name the
  row and `γc` disappears from `wait_res_at`/`ch_frag`/`un_ch`/`park_globals` (a
  deleting sweep).  The row RIDES the dormant block on the `kstack_free`/`bslots 3`
  mold (enters at `proc_dormant_seal`, leaves at `proc_dormant_unused`): `∅` at
  UNUSED, `∃ S` at ZOMBIE this lane (kwait resets the zombie's row to `∅` under
  `wait_lock` before `freeproc`; WX-EXIT tightens to `∅`).  `wait_res_alloc` moves
  BEFORE `procs_inv_alloc` in ProofMain and yields the NPROC rows for the per-slot
  assembly; `children_own_install` stays (the boot primitive), `children_own_del`
  dies.  Phase 2 = that sweep + the two parks + kfork's parent `children_own_upd`.

## LATEST (2026-09-10, final checkpoint of this session)
- WX-ROW + WX-RES FINISH phase 2 was RUNNING when this session ended (fresh Opus
  agent, go-ahead with the rulings above).  The working tree is DIRTY with its
  in-flight edits; a snapshot taken at this checkpoint is
  `wx-briefs/wxrow-p2-inflight.patch` (the agent kept editing after it -- the tree
  itself is authoritative; the patch is a fallback).  The agent's own backups are in
  the old session's scratchpad and may be gone.
- If you find the tree dirty: do NOT assume it is green.  Back it up, build once
  (`./gcp-rocq/vmbuild.sh xv6iris-2 <log>`), read the red list, then either gate/
  commit (if green: `make audit-only` = the thirteen, `lemma_diff` justified GONEs
  `children_wf`, `children_own_del`, retyped sealed Parameters) or hand a fresh
  agent a continuation of `wx-briefs/brief-wx-row-res-finish.md` carrying the phase-2
  rulings verbatim from the section above ("WX-ROW phase 1 … rulings").
- If you find the tree clean at a commit AFTER `d129bba6e` whose message names
  WX-ROW/WX-RES: it landed; continue with WX-EXIT (`wx-briefs/brief-wx-exit.md`,
  re-anchor file:line first: `ch_frag` now has no `γc` and carries the slot address).
- Owner's clarification this session: the "discarded half" of the generation ghost is
  Iris `DfracDiscarded` (a permanent read-only share), accepted as designed.

## LATEST+1 (2026-09-10, successor session, Fable coordinator)
- Found the tree DIRTY (284 iris files, the in-flight phase-2 sweep, slightly ahead
  of the old snapshot); backed it up and refreshed `wx-briefs/wxrow-p2-inflight.patch`
  to it.  Built once (`wxrow7`): COMPILED=720, EXIT=2, ONE error --
  `ProcInv.v:2748` `proc_priv_to_dormant_zombie` (the ZOMBIE block now carries the
  row, the lemma takes none in); everything above ProcInv SKIPPED, so the red list
  above it is unknown.  Grep showed the row still absent from kfork B5's park and
  parent move, userinit's park, kwait's reap reset, and kexit's ZOMBIE park.
- Wrote the continuation brief `wx-briefs/brief-wx-row-res-finish-2.md` (rulings
  restated; R1 kexit's row premise through SpecKexit/SpecSysExit/the dispatcher's
  exit arm; R2 userinit; R3 kfork child row + parent `children_own_upd` at +0xd4 with
  the moved row returned through `kfk_b5`'s continuation; R4 kwait's reset; R5 the
  rest of the red list) and launched a fresh Opus agent on it.
- If you find this session gone and the tree dirty: same rule as above -- back up,
  build once, read the red list, then gate/commit or relaunch on
  `brief-wx-row-res-finish-2.md` with the red list appended.

## HOW TO RESUME
1. `git status --porcelain` in /shared/xv6iris-2.
   - CLEAN tree at/after `51f7ae907`: WX-RES either landed (check `git log`) or
     was never applied.  If not landed: launch a fresh Opus agent on
     `wx-briefs/brief-wx-res.md` (both phases; apply the rulings above), then
     gate/commit/push (procedure below), then WX-EXIT (`brief-wx-exit.md`).
   - DIRTY tree with WX-RES/WX-ROW WIP: back it up (`git diff -- iris/ >
     <backup>.patch`), build it once (`./gcp-rocq/vmbuild.sh xv6iris-2 <log>`),
     read the red list, and hand a fresh Opus agent
     `wx-briefs/brief-wx-row-res-finish.md` (or a continuation of it: state + red
     files + "do not revert"), the way `brief-wx-fork-finish.md` did.  If the WIP
     is exactly `wxres-p2.patch`, that brief applies as written.
2. Gate before any commit: zero `Error`/`EXIT=0`; VM `make audit-only` = EXACTLY
   the thirteen; `tools/lemma_diff.py` clean; `git diff --cached` empty; nothing
   outside iris/ modified.  Commit iris with `git add -A -- iris/`, notes by path;
   `git fetch`; if origin moved, `git rebase -X theirs origin/main`, rebuild, re-audit;
   push.  Never stash/reset/add -A (except `-- iris/`)/commit -a/amend.
3. Then, in order: WX-EXIT (`brief-wx-exit.md`, drafted against the WX-RES landing
   -- re-anchor file:line first) → WX-INV (carry `children_inv` + orphans in
   `wait_res_at`, binding `ps` and `m`) → WX-WAIT (kwait returns the escrow with
   `⌜γ' ∈ uvis_ch⌝` and pid uniqueness; init's `wp_kinit_wait`) → WX-PID (pid
   uniqueness in `PidLock.nextpid_res_at`) → ARM-c (1b) (echo discharges
   `Hinit_boot`; needs the taint) → L7.
4. Standing rulings (owner): one spec per syscall; no persistent promises across the
   ecall seam; resources are real (cwd, children) never piggybacked; no GAP premises
   (a child program's entry premise must have a discharger in the parent);
   PLIC-claim-is-the-lock; kernel defects go to `kernel-defects.md`; wait/exit =
   escrow tokens by generation, every process tracked, `uvis_ch` as the completeness
   device (see the design of record).  Subagents never commit/stage/edit claude-notes.
