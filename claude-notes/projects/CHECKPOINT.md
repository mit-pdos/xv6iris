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

## State of main (2026-09-10, latest)
- Landed 2026-09-10/11, newest first: WX-INV `5b228fcad`, WX-GEN `d4a70aa12`, WX-EXIT
  `3f10fc4fa`, WX-RES + WX-ROW `96de38269`, WX-FORK, WX-KEY.  Notes in `app-echo.md` ("… LANDED").
- WX-INV LANDED: `5b228fcad` (25 files; gated pre-rebase on VM build `wxinv24`,
  audit = the thirteen, lemma_diff clean), then REBASED over the XV6_REV bump
  `92e0b0415` (panic loses its printk calls; the image relayouts; `panic_env` is
  `emp`).  The post-rebase full VM rebuild (`run-on-gcp --proofs -k`) + audit is
  the gate before the push; the relayout residue check (`RELAYOUT_OLD_REV=92e0b0415^
  tools/relayout_batch.py --residue --allow-shape=CodePanic.v`) shows nothing
  stale in the lane's files.  Note: `app-echo.md` "WX-INV LANDED".
- NEXT: WX-WAIT (`wx-briefs/brief-wx-wait.md`, re-anchored at this landing), then
  ARM-c (1b), L7.  If found dirty with no agent alive: back up, build once, read the
  red list, relaunch on a continuation brief.
- Standing rulings from the lanes (WX-EXIT/WX-INV build on them): rows per slot
  born at boot; the map's and the orphans' names canonical on `wchG`; ZOMBIE row
  at `∅`; the escrow keyed at the stored status via the xstate half-cell; the run
  keeps `Q (-1)` and every trap deposits it; the exit payload is a family field;
  `park_cap`'s `∀ cs` stays; `children_inv` stated not carried; the "discarded
  half" of the generation ghost is Iris `DfracDiscarded`, accepted as designed.

## HOW TO RESUME
1. `git status --porcelain` in /shared/xv6iris-2.
   - CLEAN tree at/after `96de38269`: continue with the NEXT lane above (launch a
     fresh Opus agent on its brief, two phases, stop-and-report after phase 1).
   - DIRTY tree with a lane's WIP: back it up (`git diff -- iris/ > <backup>.patch`),
     build it once (`./gcp-rocq/vmbuild.sh xv6iris-2 <log>`), read the red list,
     and hand a fresh Opus agent a continuation brief (state + red files + rulings
     + "do not revert"), the way `brief-wx-row-res-finish-2.md` did.
2. Gate before any commit: zero `Error`/`EXIT=0`; VM `make audit-only` = EXACTLY
   the thirteen; `tools/lemma_diff.py` clean; `git diff --cached` empty; nothing
   outside iris/ modified.  Commit iris with `git add -A -- iris/`, notes by path;
   `git fetch`; if origin moved, `git rebase -X theirs origin/main`, rebuild, re-audit;
   push.  Never stash/reset/add -A (except `-- iris/`)/commit -a/amend.
3. Then, in order: WX-EXIT → WX-GEN → WX-INV → WX-WAIT (see the design section
   named above) → ARM-c (1b) (echo discharges `Hinit_boot`; needs the taint) → L7.
4. Standing rulings (owner): one spec per syscall; no persistent promises across the
   ecall seam; resources are real (cwd, children) never piggybacked; no GAP premises
   (a child program's entry premise must have a discharger in the parent);
   PLIC-claim-is-the-lock; kernel defects go to `kernel-defects.md`; wait/exit =
   escrow tokens by generation, every process tracked, `uvis_ch` as the completeness
   device (see the design of record).  Subagents never commit/stage/edit claude-notes.
