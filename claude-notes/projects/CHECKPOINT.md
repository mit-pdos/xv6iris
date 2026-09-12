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
  Order: E3 (CONS-CURSOR kernel half + SH-LINE program half) → E4 SH-ECHO →
  E2 INIT-BOOT → E5 L7.  E3's discipline is RULED (owner: "wait for the $
  prompt, type each character after its echo"; fallback: fix the kernel's console
  overflow with UART flow control).  CONS-CURSOR LANDED: `40e97689f` (48 files;
  VM build `conscur35` EXIT=0, audit = the thirteen, lemma_diff = ten justified
  GONEs, vtest unaffected); note `app-echo.md` "CONS-CURSOR LANDED", rulings
  (1)-(7) above it (the lease; the one-arm `cons_acc`; the window under the dirty
  disjunction).  Tree CLEAN at the landing.
- PID-KEY LANDED (2026-09-11; 58 files; VM build `pidkey56` EXIT=0, audit = the
  thirteen, lemma_diff clean).  Note: `app-echo.md` "PID-KEY LANDED".  Tree CLEAN.
- CONS-ROUTE LANDED (2026-09-11; 24 files; VM build `consroute10` EXIT=0, audit =
  the thirteen, lemma_diff clean).  Notes: `app-echo.md` "SH-LINE RULING",
  "CONS-ROUTE LANDED".  Tree CLEAN.
- SH-LINE phase 1 LANDED (additive: `UserConsole.v`, `UConsLine.v`, `ukn_const`; VM
  build `shline4` EXIT=0, audit = the thirteen, lemma_diff clean) and found two
  more kernel seams, RULED in `app-echo.md` "SH-LINE PHASE 1 LANDED + TWO MORE
  KERNEL SEAMS RULED": EXEC-PAY LANDED (21 files; VM build
  `execpay5` EXIT=0, audit = the thirteen, lemma_diff clean; note "EXEC-PAY
  LANDED") → OPEN-PIN phase 1 found the image has NO console node (init's mknod makes it)
  and that open/mknod bundles cannot name their path; `PinnedObs` (the factoring)
  LANDED; both fixes RULED with the owner (`app-echo.md` "OPEN-PIN FINDINGS"):
  PATH-ARGS LANDED (21 files + `ArgPath.v`; VM build `pathargs8` EXIT=0, audit =
  the thirteen, lemma_diff clean; note "PATH-ARGS LANDED") → OPEN-PIN phase 1 LANDED (the linear two-state claim with the
  mono_list flag, FsConsPin, PinnedOpen, UInitCons statements, the open leaf;
  note "OPEN-PIN PHASE 1 LANDED + FINDINGS") → SPEC-TIGHTEN LANDED (19 files; VM build
  `tighten7` EXIT=0, audit = the thirteen, lemma_diff clean; note "SPEC-TIGHTEN
  LANDED") → OPEN-PIN phase 2 MILESTONE LANDED (2026-09-12; 20 files; VM build
  `openpin54` EXIT=0, audit = the thirteen, lemma_diff = one justified GONE;
  the create leg spends the arm's permit; the console KEY; init's mknod bundle
  PROVED; the first open pinned as a MISS; note "OPEN-PIN PHASE 2 MILESTONE
  LANDED") → OPEN-PIN phase 3 LANDED (2026-09-12; 7 files + `UInitFd.v`; VM build
  `openpin68` EXIT=0, audit = the thirteen, lemma_diff = one justified GONE; the
  three receipt-keeping leaves, init's console calls as leaf bodies, one head
  from the second open to the fork; see the commit message) → OPEN-PIN phase 4 LANDED (2026-09-12; `UInitConsK.v`; VM build
  `openpin80` EXIT=0, audit = the thirteen, lemma_diff clean) -- OPEN-PIN COMPLETE
  (note "OPEN-PIN COMPLETE"; E2 owes init's entry the key, the record equation,
  app_inv, init_cons_leaves and the entry-ledger fact) → SH-LINE phase 2
  (`wx-briefs/brief-sh-line-2.md`; phase 1 GREEN 2026-09-12, build `shline14`,
  6 u-tier files +477/-46, no kernel diff; phase-2 GO-AHEAD given with these
  accepted deviations: `UkFork.wp_uk_ecall_fork` takes a child lend `Rc`
  (Forkable cannot carry a ghost_var); `wp_uk_ecall_read_recv_body` restated at
  the TRAPPING key (the defect was a0 = the return value, not `uvis_M`);
  `UkRun.udepwf_std` (the read supplier told the ledger, as `udepwf_at` is told
  the cwd); `UkRun.urun_gen` (the taint's generic continuation from a run --
  drops everything the run holds); `ukn_triv` stays in sh's CHILD-side files
  (`UkShRun/Diag/Parse*/Malloc`, whose payload IS trivial after
  `wp_uk_ecall_fork_any`), parent side moves to `ukn_const`; init's token premise
  is `UserConsole.ucons_reader cn 0` at the narrow class, held as
  `UConsLine.uinit_tok cn T` on the restart head) → BLOCKER 2026-09-12 (note "SH-LINE PHASE 2 -- THE
  SWALLOWED BYTE"): consoleread's `dc = d+1` arm; the ^D face is fixed by a
  kernel lane, the copyout-fault face RULED: the lazy flag on the key (LAZY-FLAG). Pipeline meanwhile: SH-LINE 2a
  LANDED (`69e38c9f0`, build `shline37`; the payload half blocked by a SECOND
  seam: the generic slot exists only at the trivial payload -- note "SECOND SEAM
  FOUND") → GENERIC-PAY LANDED (2026-09-12, build `gpay28`; note "GENERIC-PAY
  LANDED") → CONS-SWALLOW (`wx-briefs/brief-cons-swallow.md`, kernel lane, fresh
  agent, LAUNCHED 2026-09-12)
  (`wx-briefs/brief-cons-swallow.md`, kernel lane, option-independent) → SH-LINE
  2b → LAZY-FLAG (RULED 2026-09-12: `uvis_lazy : bool`, false at exec, set only
  by sbrklazy; note "THE OWNER'S RULING ON THE FORK") → E4 → E2 → E5
  → SH-LINE phase 2 → E4 → E2 → E5.
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

PRE-MORTEM REVIEW (2026-09-12): `projects/review-echo-plan-2026-09-12.md`, sixteen
findings; the coordinator verified 1 (udep = □ app_sup = the taint; init's slot
takes it), 2 (eight harts print after `started`), 3 (Htx/Hrx at an arbitrary
γ), 9 (sh re-opens the console until fd >= 3), 11 (`ushd_clw_text_ty`
assumed in UkShFork). Awaiting the owner's rulings on the batch before the
pipeline order changes; CONS-SWALLOW continues.

PARALLEL LANES (2026-09-12).  Sibling checkouts `/shared/xv6iris-2-tlw` (lane
TEXT-LW, branch `lane/text-lw`) and `/shared/xv6iris-2-sup` (lane SUPPLY-SPLIT,
branch `lane/supply-split`), each with its own remote tree seeded by `cp -a`
of `_shared_xv6iris-2` on the VM (then one incremental build back to HEAD;
USE DISTINCT LOG NAMES PER TREE -- `/tmp/<log>.log` is shared).  Landing: the
lane commits on its branch; the coordinator gates in the sibling, then
`git fetch /shared/xv6iris-2-<l> lane/<x>` + rebase/merge onto main in the
main checkout, rebuild, re-gate, push.  E5 design proposal written (note "E5 --
THE OUTPUT SIDE: DESIGN PROPOSAL"); awaiting the owner on O3 (rate discipline
(b)) and O5 (allocation failure (i)).  Main-tree pipeline unchanged:
CONS-SWALLOW (phase 2 running) → LAZY-FLAG → DISC-RATE → TX-TAG → TX-RECEIPT
+ ECHO-RECEIPT → APP-IFACE → write leaf + cones → SH-LINE 2b → E4 → E2 → E5.

LANES RUNNING (2026-09-12, later): main tree CONS-SWALLOW phase 2; siblings
SUPPLY-SPLIT phase 2 (`-sup`, rulings (a)-(f) in the note "SUPPLY-SPLIT PHASE
1"), TEXT-LW phase 1 (`-tlw`), DISC-RATE phase 1 (`-disc`, brief
`brief-disc-rate.md`; O3/O5 RULED: wait for the harts; failure outputs valid).
Landing order when green: CONS-SWALLOW (main) → fetch the sibling branches one
at a time (rebase on main, rebuild, re-gate) → LAZY-FLAG in main.
