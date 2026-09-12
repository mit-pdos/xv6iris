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

LANES (2026-09-12, later): CONS-SWALLOW LANDED on main (note "CONS-SWALLOW
LANDED"); main is free for LAZY-FLAG (`brief-lazy-flag.md`) after a verify
build of the merged HEAD; siblings
SUPPLY-SPLIT phase 2 (`-sup`, rulings (a)-(f) in the note "SUPPLY-SPLIT PHASE
1"), TEXT-LW LANDED on main (2026-09-12), DISC-RATE phase 1 (`-disc`, brief
`brief-disc-rate.md`; O3/O5 RULED: wait for the harts; failure outputs valid).
Landing order when green: CONS-SWALLOW (main) → fetch the sibling branches one
at a time (rebase on main, rebuild, re-gate) → LAZY-FLAG in main.

TX-TAG LAUNCHED (2026-09-12) in the freed sibling `/shared/xv6iris-2-tlw` on
`lane/tx-tag` from `2c0d32048` (brief `brief-tx-tag.md`; scope = the UART/
console/printk layer + boot; the filewrite/row-16 relay is the next lane
TX-RECEIPT).  Main: verify build `mainverify1` of the merged HEAD GREEN (audit = the
thirteen); LAZY-FLAG LAUNCHED in main (2026-09-12, brief `brief-lazy-flag.md`,
based on `ed3d61934`).  Four lanes in flight: LAZY-FLAG (main), SUPPLY-SPLIT p2
(`-sup`), DISC-RATE LANDED on main (2026-09-12; `-disc` is free), TX-TAG p1 (`-tlw`).

TX-TAG phase 1 green (2026-09-12); phase 2 go-ahead given (pinned echo post;
printk-site list requested).  RULED: TX-RECEIPT = per-pid transmit token; the K
side = printk ledger in pr_res + PRINTK-FMT + printk-site enumeration (note
"TX-TAG PHASE 1").  `-disc` sibling free: APP-IFACE phase 1 (statement diff
only, for the owner's review) next there.

APP-IFACE phase 1 LAUNCHED (2026-09-12) in `-disc` on `lane/app-iface` from
`5cd2ae7e0` (brief `brief-app-iface.md`): the three trusted-statement changes
(app_boot; the rx-tag equation in Hinit_boot; the era token for Htx/Hrx) as a
DIFF for the owner's review -- no commit, no phase 2 without the owner.  In
flight: LAZY-FLAG p1 (main), SUPPLY-SPLIT p2 (`-sup`), TX-TAG p2 (`-tlw`),
APP-IFACE p1 (`-disc`).

SUPPLY-SPLIT phase 2 GREEN on `lane/supply-split` (`d2708e5b7`); LANDING DEFERRED
behind LAZY-FLAG (shared tier files).  SH-OPEN LAUNCHED (2026-09-12) in `-sup` on
`lane/sh-open` off `lane/supply-split` (brief `brief-sh-open.md`).  In flight:
LAZY-FLAG p1 continued in the STORED form (main; the computed refinement is
withdrawn), TX-TAG p2 (`-tlw`), APP-IFACE p1 (`-disc`), SH-OPEN p1 (`-sup`).
Landing order: LAZY-FLAG (main) → SUPPLY-SPLIT (rebase) → SH-OPEN → TX-TAG →
APP-IFACE after the owner's review.

APP-IFACE: the owner approved the statement diff (2026-09-12); phase 2 running
in `-disc`.  TX-TAG phase 2 gains the rider: `uart_col_ok`'s LOOP-off clause
`u_wire u = u_out u`.

APP-IFACE LANDED on main (2026-09-12).  `-disc` free → E2 INIT-BOOT next there,
on a base = main + `lane/supply-split` (merged locally; supply-split itself
still lands on main after LAZY-FLAG).

REBASE-SUPPLY-SPLIT LAUNCHED (2026-09-12) in `-disc` (brief
`brief-rebase-supply-split.md`): `lane/supply-split` → `lane/supply-split-r1` on
current main (three conflicts with TEXT-LW in UkShDiag/UkShFork/UkShMain).
E2 INIT-BOOT brief written (`brief-init-boot.md`); launches in `-disc` on
`lane/supply-split-r1` when the rebase is green.  In flight: LAZY-FLAG p1
(stored form, main), TX-TAG p2 + LOOP-off rider (`-tlw`), SH-OPEN p1 (`-sup`),
REBASE-SUPPLY-SPLIT (`-disc`).

LAZY-FLAG CORE LANDED on main (`05d689c1b`); the stored form is banked as
`wx-briefs/lazy-flag-stored.patch`; LAZY-FLAG-2 LAUNCHED in main (fresh agent,
brief `brief-lazy-flag-2.md`: close the patch, sbrk's block-level arm, exec's
domain row in `kexec_built`, the read-leaf refutation).  In flight: LAZY-FLAG-2
(main), TX-TAG p2 (`-tlw`), SH-OPEN p1 (`-sup`), REBASE-SUPPLY-SPLIT (`-disc`,
then E2 INIT-BOOT there).

REBASE-SUPPLY-SPLIT DONE (2026-09-12): `lane/supply-split-r1` = `69543d942` in
`-disc`, green (build `rebase10`, audit = the thirteen; three conflict
resolutions kept both edits).  LANDING on main still deferred: LAZY-FLAG-2 has
30 files dirty in main, four overlapping (UInitSh, UexecExecInst, UexecSG,
UkRun) -- after LAZY-FLAG-2 lands, rebase r1 once more, then land, then rebase
SH-OPEN (which is on the OLD supply-split d2708e5b7) onto it.  E2 INIT-BOOT
LAUNCHED in `-disc` on `lane/init-boot` = r1 (brief `brief-init-boot.md`).  In
flight: LAZY-FLAG-2 p1 (main), TX-TAG p2 (`-tlw`), SH-OPEN p1 (`-sup`), E2 p1
(`-disc`).

TX-TAG LANDED on main (2026-09-12).  `-tlw` free → TX-RECEIPT (per-pid
transmit token; exact receipts) next there.

TX-RECEIPT LAUNCHED (2026-09-12) in `-tlw` on `lane/tx-receipt` from main
`3159c77d5` (brief `brief-tx-receipt.md`: the per-pid transmit token, exact
console-write receipts, the relay to row 16, the U-tier write leaf; phase 1
PROPOSES the key component `uvis_tx` for the coordinator's ruling).  In flight:
LAZY-FLAG-2 p1 (main), SH-OPEN p1 (`-sup`), E2 p1 (`-disc`), TX-RECEIPT p1
(`-tlw`).

SH-OPEN phase 1 green-but-one-file (2026-09-12); phase 2 go-ahead given with
rulings (A) `cons_never` sealed-absent state → E2; (B) the cwd row on
`exec_slot_pre`'s wands → LAZY-FLAG-2 (note "SH-OPEN PHASE 1 + TWO RULINGS").

SH-OPEN phase 2 committed on `lane/sh-open` (`ba3249c96`), one seam red until
LAZY-FLAG-2's cwd row; lands after supply-split-r1.  `-sup` idle → the K-side
ledger lane (PRINTK-LEDGER) next there, on main.

PRINTK-LEDGER LAUNCHED (2026-09-12) in `-sup` on `lane/printk-ledger` from main
`b0cc198c6` (brief `brief-printk-ledger.md`: the K ledger under pr.lock, rendered
messages pinned, `kernel_msgs`).  RULED (O5'): kernel diagnostics reachable from our processes' syscalls are
ADMITTED in the output claim (recovering tail / ireclaim / ialloc / balloc
templates; the boot's ten exact); the trap-side two are not ours (note "O5'
RULED").  In flight: LAZY-FLAG-2 p1 (main), E2 p1 (`-disc`), TX-RECEIPT p1
(`-tlw`), PRINTK-LEDGER p1 (`-sup`); `lane/sh-open` and `lane/supply-split-r1`
wait to land.

E2 phase 1 green (2026-09-12); phase 2 go-ahead with rulings (d)(e)(h)(i) (note
"E2 INIT-BOOT PHASE 1 + RULINGS"); E2 will be red at the cwd seam until
LAZY-FLAG-2 lands.

TX-RECEIPT phase 1: design blocker at the mint (pid reuse) RULED (pid_reg slice
in the UART invariant); `uvis_tx` key component ruled; PAUSED at a milestone
commit until LAZY-FLAG-2 lands (shared sweep).  `-tlw` to host E4 SH-ECHO on
`lane/supply-split-r1` meanwhile.

TX-RECEIPT milestone committed (`6ac4b8626` on `lane/tx-receipt`, red only at
ProofFilewrite:4675 pending the block conjunct); the agent stands by for a ping
after LAZY-FLAG-2 lands.  `-tlw` switched to `lane/supply-split-r1`; E4 SH-ECHO
launching there (brief `brief-sh-echo.md`).

LAZY-FLAG-2 phase 1 DONE (2026-09-12; 60 dirty files in main; banked as
`wx-briefs/lazy-flag-stored-2.patch`; K4 is a ROW -- `um_covered` survives to
`kexec_built`); LAZY-FLAG-3 (fresh agent, `brief-lazy-flag-3.md`) finishes the
ten reds and gates IN THE SAME DIRTY TREE.  Waiting on it: SUPPLY-SPLIT-r1,
SH-OPEN, TX-RECEIPT (resume by ping), E2's cwd seam.

E4 phase 1 green (2026-09-12; `lane/sh-echo` = `5b4c88ef8`); phase 2 go-ahead
(the big item: `echo_slot_of_kexec`); E2 told to hand sh the one `echo_fs_pure`
law.  In flight: LAZY-FLAG-3 (main), E2 p2 (`-disc`), PRINTK-LEDGER p1 (`-sup`),
E4 p2 (`-tlw`).

PRINTK-LEDGER phase 1 (2026-09-12); phase 2 go-ahead (note "PRINTK-LEDGER PHASE
1").  LANDING ORDER for the UART-side branches after LAZY-FLAG-3: supply-split-r1
→ sh-open → tx-receipt (resumed) → printk-ledger (both extend the THR leaf and
`uart_tagsE` by juxtaposition).

PRINTK-LEDGER STAGED (2026-09-12): A (ledger threading, cs existential, green) → B
(printint digits) → C (printk's pinned post, 23 lemmas) → D (the tie with
`k_push_ok`; hart lines); each its own commit on `lane/printk-ledger`; a fresh
agent continues where context runs out.

PRINTK-LEDGER agent out of context before milestone A's commit (2026-09-12);
PRINTK-LEDGER-2 (fresh, `brief-printk-ledger-2.md`) continues on the dirty
`lane/printk-ledger` in `-sup`.  NOTE: the VM is saturated (five trees building;
load 22-40) -- builds queue.

OWNER (2026-09-12): printk's contract takes a caller-supplied FUPD that appends
the message to the ledger at the commit under pr.lock (note "OWNER'S RULING ON
PRINTK'S CONTRACT"); PRINTK-LEDGER-2 told before its A commit.
CLARIFIED: the APPLICATION owns the era's output ledger authority; printk's Ψ
comes from `printk_env` (an abstract era appender minted at boot) for kernel
sites; `pr_res` holds no authority.

E4 phase 2 GREEN on `lane/sh-echo` (`e01a8d9df`); phase 3 (echo's exec entry
geometry, the two hanging walks, the cwd threading) to a fresh agent in `-tlw`
(`brief-sh-echo-3.md`).

LAZY-FLAG LANDED on main (2026-09-12; 78 files; build `lazy59`).  Next in main:
REBASE-CHAIN (`brief-rebase-chain.md`): supply-split-r1 → r2 onto main, sh-open →
sh-open-r2 on top (its cwd seam closes); then the coordinator fast-forwards main
to sh-open-r2; then TX-RECEIPT resumes (rebase onto main) in the next free
checkout; E2 (`-disc`, on r1) rebases onto the new main at its end.

SUPPLY-SPLIT + SH-OPEN LANDED on main (2026-09-12; main = `6f959f529` + notes).
TX-RECEIPT resumes IN MAIN (rebase `lane/tx-receipt` from `-tlw` onto main; then
the pid_reg slice, the block conjunct, `uvis_tx`, row 16, the write leaf).  E2
rebases onto main at its end.  In flight: TX-RECEIPT (main), E2 p2 (`-disc`),
PRINTK-LEDGER-2 A (`-sup`), E4 p3 (`-tlw`).

TX-RECEIPT resumed in main (rebase clean, `9de28358a`); the pid_reg SLICE is
unbuildable (wchG layering) → RULED the DOMAIN SHADOW (`tx_dom` halves in the
UART invariant and the pid lock's payload); R1 proceeds.

OWNER'S REDESIGN (2026-09-12): tagless raw-byte theorem; ONE invariant with an
application-fixed pure predicate over (rx history, accepted bytes); EVERY UART
output opens it via a caller-supplied fupd; the sublist/prefix receipts and the
tags are retired.  TX-RECEIPT CANCELLED (branch = history).  PRINTK-LEDGER-2
redirected: revert the ledger, keep rendering (milestones B/C).  New lane
OUT-FUPD (brief being written) runs in main.

OUT-FUPD LAUNCHED in main (2026-09-12, `brief-out-fupd.md`; phase 1 = the
application-fixed output predicate in the UART invariant, the store's fupd, the
writers' contracts, the retirement list, WITH a trusted-statement diff for the
owner).  TX-RECEIPT agent stopped (branch `lane/tx-receipt` = history).  In
flight: OUT-FUPD p1 (main), E2 p2 (`-disc`), PRINTK-LEDGER-2 → rendering B/C
(`-sup`), E4 p3 (`-tlw`).  COORDINATOR RULE: check `git branch --show-current` =
main before any notes commit in the main checkout (two notes commits went onto
lane/tx-receipt while an agent had it checked out; both cherry-picked to main).

TWO UARTS (owner's plan, 2026-09-12): kernel messages on their own UART; the
theorem is about the console UART only.  PRINTK-LEDGER-2 STOPPED; OUT-FUPD
narrowed to the console UART (printk untouched).  Pending the owner: who
changes the Rocq machine model; roles/addresses.  Then DISC-SIMPLIFY (drop D0,
the shuffle, kernel_msgs).

2026-09-12 (late): OUT-FUPD PAUSED (banking its diff; design to be reported as
text; main restored clean); UNTAG (`brief-untag.md`: remove TX-TAG's labels,
keep the LOOP-off rider and the pinned consputc/echo posts) launches in main as
soon as OUT-FUPD confirms the clean tree -- BEFORE the owner's dual-UART agent
touches the UART layer; SH-LINE 2b LAUNCHED in `-sup` (`brief-sh-line-2b.md`);
PRINTK-RENDER parked (`lane/printk-ledger`, pure files; the printint-digits WIP
banked as `wx-briefs/printint-digits-wip.patch`).  In flight: E2 p2 (`-disc`),
E4 p3 (`-tlw`), SH-LINE 2b p1 (`-sup`); OUT-FUPD pausing (main).
