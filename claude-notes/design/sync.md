# Design: `sync` in the union -- a completed sync pins what the next boot sees

§1-§2 LANDED (xv6 `d66e41c`); §3-§5 PROPOSAL (the worklist is
[`../projects/sync.md`](../projects/sync.md)).  Builds on
[`union.md`](union.md) (the model `ulm`, the round, the top theorem),
[`app-file.md`](app-file.md) (the deed, the durable copy, honest limit 2,
§6's commit receipt), [`applications.md`](applications.md) §3 (the durable
instance and the transport) and `fs-syscall-specs.md` §5 (the SNAPSHOT /
BOUND / PER-NODE principles `sys_sync` was specified against).

## 0. The target

A new line shape `sync` (the image's `/sync`: `sync(); exit(0)`, prints
nothing).  The claim, at the transcript:

- without a sync, the next boot sees any state f passed through since this
  era's boot, including the intermediate states of a round -- the create or
  truncate committed before echo's writes (`Some []`), a chunk subset -- and
  the round in flight at the crash;
- after a sync round whose prompt appeared, the next boot sees the state at
  the sync or a state a LATER round passed through: `echo a > f; echo b >
  f; sync; <power cut>; cat f` prints `b` and nothing else.

Two NEGATIVE demos carry the claim (the vacuity rule): that transcript with
`cat f` printing `a` is refuted; and, within one era, `echo a > f; echo b >
f; cat f` printing `a` is refuted (§1 -- the landed model admits it).

## 1. Why no line may have a silent alternative

The top theorem is `∃ cs` (one alternative per line) with the transcript a
prefix of the session.  An admissible alternative that prints the bare
prompt and moves nothing lets the theorem read "the command did not run"
into any transcript where the command prints nothing on success -- `echo …
> f` (`RFRan`, cont `u_prompt`) and `sync`.  So `echo a > f; echo b > f;
cat f` printing `a` would be admitted, and a completed `sync` could not
raise the floor of §5.

Until xv6 `d66e41c` such an alternative was HONEST: sh parses in the child
(`sh.c`, `runcmd(parsecmd(cmd))`), the constructors used `malloc`'s result
unchecked, `malloc` returns NULL when `sbrk`'s `kalloc` fails, the store to
NULL faults, `usertrap` reports on the KERNEL UART (not the theorem's) and
kills the child, and sh prints `$ ` after `wait`.  `d66e41c` (owner's
change, "sh: panic when out of memory") adds `cmdalloc`: `malloc`,
`panic("out of memory")` on NULL, `memset`.  The death now PRINTS `out of
memory\n` on fd 2 (checked in QEMU with a memory hog).  Every other child
death is visible or unreachable: exec and fork failure print, `argv[0] ==
0` and `cmd == 0` cannot happen at a non-empty admissible line, `kill` has
no caller in the union (the taint covers it), a verified program faults
nowhere, and a BLANK line re-prompts in sh's parent with no fork -- under
the discipline only as the taint's arm (an admissible line never starts
with a newline, `UkSh.ush_uline_head_nonnl`).

## 2. The model: an out-of-memory alternative, no silent one

- **`FileDisc.ROom`** (code 18), shared by every forked line shape --
  echo, redirect, cat, seccomp, sync, and the pipelines as `UR ROom`
  (`UnionDisc.uok`'s one cross arm): cont `alt_oom = "out of memory\n$ "`,
  step the identity (the parse precedes the redirect's open), not a panic,
  free.  It is the one "the command did not run" outcome the console shows.
- **No file line has a silent alternative.**  Pipelines keep `PLRun []` in
  the shell's always-admitted three (`PipesDisc.plsafe`): an empty pipeline
  output is real (`cat f | cat` at an empty `f`), and taking it out of
  `plsafe` reaches the N-stage layer (`PipesView.pv_ok`,
  `PipeOutNEv.pwc_blkV_file_empty`) -- an open cleanup, not a hole.
- **The hook** `LineModelLinks.lmh_noc : lm_line M -> option nat`, its laws
  under `Some`; the pad of an in-flight line (`GenOutPure.lm_alts_pad`)
  uses `lmh_exf`; the decider's canonical re-resolution
  (`UnionDecU.u_canon_name`) uses `uoom`.
- **The proofs name the true alternative** wherever the silent one used to
  be filed:
  - the constructors' NULL arm is `cmdalloc` -> `panic`; the parse walks
    take it as the continuation `UkShEcho.ushp_oom` (built from a
    diagnostic law by `ushp_oom_of_diag`), and the child -- holding its
    lend AND its fd ledger, since panic writes fd 2 -- prints, files `ROom`
    at the block's first byte and exits paying `Wc I 0`
    (`UkShDiag.wp_kshd_oom_paid`; `UShURoundDefs.uHoom` for echo and the
    pipeline's node 0, `UShURound.uoom_law_deed` for cat and the redirect,
    whose children open the deed before the parse);
  - no child returns its lend untouched: `UkShFork.ushf_wq I := Wc I 0`,
    and no law converts `Wc I 3` to `Wc I 0`;
  - the fork's re-entry has no whole-lend row (`ushf_fans`: the parent
    arm's `r ≠ -1` refutes it);
  - a block whose first byte is the prompt files the block's OWN
    alternative (`uWcf0_of_pre_line_id`: `cat f` at an empty `f`, `RCRan`).
- **The negative demo**: `UnionDiscDec.demo_no_silent` -- for every
  well-formed boot state, `echo a > a.txt; echo b > a.txt; cat a.txt`
  printing `a` is not a good output of the union model (`lm_good_out
  ulmG`, what `union_phi` promises per cycle).

## 3. The sync line

- **Model** (`FileDisc`/`UnionDisc`): `LSync`, bytes `sync\n`; alternatives
  RAN (`$ `, f unchanged), EXEC-FAILED (`exec sync failed\n$ `), and the
  fork panic `RCFork`.  All state-free, so all free.  `line_file LSync =
  None`.
- **The round**: an EXEC line with no redirect -- `uHchild_*`'s echo/cat
  shape at `argv = ["sync"]`; the child execs `/sync` on the image
  (pinned like `/cat`: `FsImg` already tracks the raw), whose entry at the
  union registry is `UkSync`'s program at a payload that pays PEND at RAN
  once `sys_sync` has returned.  The deed is not lent (sync touches no
  file); the payload is where §5's durability evidence will ride.
- **Admission**: `adm_u` admits `LSync`; the decider (`UnionDecU`) gains
  the line's three candidates.

## 4. What the kernel gives, and what it does not (the durability link)

`SpecSysSync.wp_sys_sync_sconf` returns `flushed_sync γ e := ∃ e' ≥ e,
log_flushed_bank γ e'`, and `log_flushed_bank γ E := ∃ b D, log_epoch_lb γ
E ∗ flushed b D ∗ ⌜snap_holds D⌝`.  The three conjuncts are INDEPENDENT:
the receipt says "some committed file-system state exists" (true at
genesis) and nothing ties `D` to the caller's state; "D is the state as of
batch E" is asserted in the header comment, not carried.  `FsFlushed.dur_at`
(the per-node reading) was never built, and the dispatcher's arm 22 drops
the receipt at `sync_witness_0`.  What IS there: a receipt's `D` is in the
committed history and recovery lands on its last element
(`FsCrash.P_fs_receipt_committed`).

So SY3 owes: (K1) a receipt that says `D` contains every delta linearized
before the call (the bank's pairing made a statement at its two deposits,
`ProofEndOp.eo_tail` and `ProofInitlog`'s seal); (K2) arm 22 carrying it to
the U tier; (K3) the application's durable copy tied to it, so the running
claim learns at sync's return that the crash slot's copy was made from a
state at or after the sync point.  Two shapes for K3, undecided: a commit
receipt (the commit law passes its batch index to the transport;
app-file.md §6's plan, which would also give `write` a receipt), or a
durable REGISTER (the transport also receives the OLD durable copy, which
`fs_rec_permit`'s guest already carries, so one ghost value split between
the running claim and the durable copy is updated at each commit).

## 5. The crash semantics (the model's boot relation)

`fadm_boot` ("any subsequence of any earlier redirect line, or absent")
becomes a relation between CONSECUTIVE cycles.  Per round, `rmid s l a`:
the states the round passes through (for `RFRan sel` from `s`: `s`, `Some
[]` at f, and the chunk subsets at f); for the round in flight at the cut,
the union over its admissible alternatives.  The FLOOR of a cycle is its
last `sync` round whose block's first byte is ON THE WIRE (observational:
the pad of §2 may name a "ran" alternative for a round in flight, and must
not raise the floor), or the cycle's start.  Then

    boot_{k+1} ∈ {state before the floor round} ∪ ⋃_{rounds i ≥ floor} rmid(round i).

The unsynced half (floor = the cycle's start) is provable WITHOUT §4: the
durable copy's typed witness becomes a lower bound of the era's f-state
TRAJECTORY whose last element is the content, in place of the line-list
lower bound.  The synced half is §4's.

## 6. Honest limits

- Limit 1 of app-file.md stands: the state at the sync is a chunk SUBSET of
  its redirect line (a write can fail invisibly at a full disk).
- Safety only: `sys_sync` may block forever under a continuous operation
  stream; then no prompt appears and the floor does not move.
- In reality this kernel commits at the last `end_op`, and sh serialises
  rounds, so a completed `echo b > f` is durable without a sync; the model
  cannot see it because `write` carries no receipt (app-file.md §6).
