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

## What was RUNNING when this was written
- WX-RES phase 2 (agent on the coordinator's session; brief
  `wx-briefs/brief-wx-res.md` + the phase-2 go-ahead rulings recorded in
  app-echo.md's order line and below).  Its phase-1 tree is `wx-briefs/wxres-p1.patch`
  (11 modified iris files, green statements, 8 red proof roots).  Phase-2 rulings:
  `park_cap` keeps `∀ sts cs`; `usertrap_res_bare_fd_open` keeps `cs` fixed and
  `ProofUserretClosed.Rut_at` gains the `cs` index; option (C) for the invariant
  (`ch_frag γc γ0 pa S`, the slot address in the map's value; `children_inv`
  STATED, NOT carried -- WX-INV carries it); the two row installs (kfork's child
  row under `wait_lock` + `upd_chg`; main hands init's row `ch_frag γc γ0 pa_init ∅`
  to userinit as a `SpecUserinit` premise); `ut_fork_out := ufork_ans (sfork_pay f)
  r cs cs'` + `ut_ch_kept`; kfork moves the parent's row (`children_own_upd`).

## HOW TO RESUME
1. `git status --porcelain` in /shared/xv6iris-2.
   - CLEAN tree at/after `51f7ae907`: WX-RES either landed (check `git log`) or
     was never applied.  If not landed: launch a fresh Opus agent on
     `wx-briefs/brief-wx-res.md` (both phases; apply the rulings above), then
     gate/commit/push (procedure below), then WX-EXIT (`brief-wx-exit.md`).
   - DIRTY tree with WX-RES WIP (iris/UsertrapRes.v, SpecUsertrap.v, WaitInv.v,
     ParkCap.v, SpecKfork.v, SpecSyscall.v, SpecUservec.v, SpecUserretClosed.v,
     SpecForkret.v, SpecForkretParkPaid.v, Proof* …): the agent was killed mid
     phase 2.  Back the tree up (`git diff -- iris/ > <backup>.patch`), build it
     once (`./gcp-rocq/vmbuild.sh xv6iris-2 <log>`), read the red list, and hand a
     fresh agent a continuation brief (state + red files + the rulings above +
     "do not revert"), the way `brief-wx-fork-finish.md` did.
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
