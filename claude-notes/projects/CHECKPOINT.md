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
- Landed 2026-09-10/11, newest first: WX-WAIT `f3f77bb51`, WX-INV `5b228fcad`, WX-GEN `d4a70aa12`, WX-EXIT
  `3f10fc4fa`, WX-RES + WX-ROW `96de38269`, WX-FORK, WX-KEY.  Notes in `app-echo.md` ("… LANDED").
- WX-WAIT LANDED: `f3f77bb51` (15 files; VM build `wxwait4` EXIT=0, audit = the
  thirteen, lemma_diff = one justified GONE).  Note: `app-echo.md` "WX-WAIT LANDED".
  Tree CLEAN.  The WAIT-EXIT design of record is now fully landed (WX-KEY, WX-FORK,
  WX-RES+ROW, WX-EXIT, WX-GEN, WX-INV, WX-WAIT); every payload is `fun _ => True`
  until L7 puts the console-input resource in.
- THE REMAINING ARC: `app-echo.md` "THE REMAINING ARC TO xv6_app_adequacy FOR
  ECHO — DESIGN".  E1 ECHO-PRED LANDED (2026-09-11; note "E1 ECHO-PRED LANDED").
  Order corrected: E3 RECEIPT LEAF + reader token → E4 SH-ECHO → E2 INIT-BOOT →
  E5 L7.  E3's design is RULED (owner, 2026-09-11: option (i) -- the trace property is
  "wait for the $ prompt, type each character after its echo"; fallback: fix the
  kernel's console overflow with UART flow control).  CONS-CURSOR (the kernel
  half, `wx-briefs/brief-cons-cursor.md`): phase 1 landed as statements (13 reds);
  its agent died to a login expiry; a SECOND agent runs `brief-cons-cursor-
  finish.md` (tree DIRTY on purpose, snapshot `conscur-inflight.patch`) under
  the LEASE ruling (`app-echo.md` CONS-CURSOR RULINGS (5): the console arm takes
  the token unconditionally through a fupd-shaped accessor; the generic slot's
  supply gains the accessor; the lease itself is SH-LINE's); then SH-LINE (R5 + sh's gets under the receipt) → E4 SH-ECHO →
  E2 INIT-BOOT → E5 (the discipline automaton, `good_out`, the identification
  gate, `Hphi`).
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
