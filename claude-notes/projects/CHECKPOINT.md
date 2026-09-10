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
- WX-RES + WX-ROW LANDED: `96de38269` (iris, 288 files), gated on the VM (build
  `wxrow13` EXIT=0, `make audit-only` = the thirteen, `lemma_diff` = the three
  justified GONEs `children_wf`/`children_own_del`/`children_own_install`).  The
  as-landed note is in `app-echo.md` ("WX-RES + WX-ROW LANDED").  Tree CLEAN.
- Rulings that shaped it (kept here because WX-EXIT/WX-INV build on them): the map's
  name is canonical (`Xv6Cameras.wch_name`); rows are per-slot, born at boot, riding
  the dormant block (`∅` at UNUSED, `∃ S` at ZOMBIE -- WX-EXIT tightens to `∅` and
  deletes kwait's reset); kexit parks its own row into the ZOMBIE block; `park_cap`'s
  `∀ cs` stays; `children_inv` stated not carried.  The "discarded half" of the
  generation ghost is Iris `DfracDiscarded`, accepted as designed.
- WX-EXIT LAUNCHED (2026-09-10; fresh Opus agent, phase 1 then stop-and-report).  Its
  brief's last section "RE-ANCHORED AFTER THE WX-RES + WX-ROW LANDING" carries the
  corrections (ZOMBIE tightens to `∅`, kwait's reset dies, orphans canonical-named
  beside the map, the children move is kexit's).  Owner's standing instruction: keep
  going through checkpoints -- land, note, launch the next lane, no pausing to ask.
- NEXT after it (REVISED, design in app-echo.md "WX-GEN / WX-INV / WX-WAIT — DESIGN"):
  WX-GEN (`wx-briefs/brief-wx-gen.md`, written; launch when WX-EXIT lands -- same
  files) → WX-INV → WX-WAIT → ARM-c (1b) → L7.  WX-PID is absorbed into WX-GEN
  (pid uniqueness IS the `pid_reg` ghost map's agreement).  Original WX-EXIT re-anchoring note: it
  was drafted against a pre-landing tree -- `ch_frag` has no `γc` and carries the
  slot address; `children_own_del` is GONE (X3 must empty the dying process's row
  with `children_own_upd` to `∅` and move `S` to the orphans, then park the row at
  `∅`, which is what lets ZOMBIE tighten); `SpecKexit.wp_kexit_sconf_body` already
  takes the dying process's row at `cs` (R1 of the finish-2 brief), so X3's "the
  residue in hand" is kexit's contract, not reparent's.

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
