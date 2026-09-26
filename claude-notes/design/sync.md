# Design: `sync` in the union -- a completed sync pins what the next boot sees

PROPOSAL (owner's direction; the worklist is
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

## 1. The silent alternative is a hole at the TRACE level

The top theorem is `∃ cs` (one alternative per line) with the transcript a
prefix of the session.  A line whose admissible set contains an alternative
printing the bare prompt and moving nothing lets the theorem read "the
command did not run" into any transcript where the command prints nothing
on success.  Today every file line has one (`REcho 2`, `RFSilent`,
`RCSilent`), and `echo … > f` prints nothing on success (`RFRan sel`, cont
`u_prompt`) -- so `echo a > f; echo b > f; cat f` printing `a` is ADMITTED
(`echo b > f` read as `RFSilent`).  A silent `sync` would leave the floor of
§5 unraised the same way.  So the silent alternative leaves the MODEL, not
just the proofs.

**A real execution DOES reach it: the child's out-of-memory death in
`parsecmd`.**  sh parses in the CHILD (`sh.c:172`, `runcmd(parsecmd(cmd))`);
`parsecmd`'s constructors `malloc` and `memset` the result unchecked
(`sh.c:206-207`, …); `malloc` returns NULL when `sbrk` fails
(`umalloc.c:54-56`, `growproc`'s `kalloc` can fail), the store to NULL
faults, and `usertrap` prints on the KERNEL UART (not the theorem's) and
kills.  sh then prints `$ ` after `wait`, ignoring the status.  So "the
command did not run and the console shows only the prompt" is an HONEST
outcome at every forked line (`UkShMalloc.v`'s header: no caller can wish
the NULL away), and the proofs' left payload arm (`Wc I 3`, "died at the
null store") is exactly it.  Consequences: the within-era `echo a > f; echo
b > f; cat f` -> `a` is admitted HONESTLY (the second child may die before
its open), and a silent `/sync` cannot be told apart from a sync that never
ran.  The other deaths are visible or unreachable: `argv[0] == 0`
(`sh.c:77`) and `cmd == 0` (`:68`) at a non-empty line, exec and fork
failure print, `kill` has no caller in the union (the taint covers it), and
a verified program faults nowhere.  A BLANK line re-prompts in the parent
(`sh.c:164`) with no fork; the proofs file it at the silent echo
alternative of the parser's fallback line `LEcho []`.

RULED (owner, 2026-09-26): option (b) -- sh checks `malloc`.  Upstream
`d66e41c` ("sh: panic when out of memory") adds `cmdalloc(n)`: `malloc`,
`panic("out of memory")` on NULL, `memset`; the five constructors call it.
So the out-of-memory death PRINTS `out of memory\n` on fd 2 and exits the
child, and sh prints `$ `.  Checked in QEMU with a memory hog: the pinned
sh printed nothing (the kill message went to the kernel UART) and sync never
ran; `d66e41c` prints the diagnostic.

## 2. The model after `d66e41c`: an out-of-memory alternative, no silent one

- **`ROom`**, one alternative shared by every forked line shape (echo,
  redirect, cat, seccomp, sync, and the pipelines through `UR ROom`): cont
  `out of memory\n$ `, step the identity (the parse precedes the redirect's
  open), not a panic, state-free, hence free.  It is the only honest
  "the command did not run" outcome that the console can show.
- **The silent alternatives leave**: `REcho 2`, `RFSilent`, `RCSilent`
  (echo, redirect, cat, and seccomp's), and `sync` never has one.  ONE
  exception, a proof artefact with no trace meaning: a BLANK line is
  handled in sh's parent with no fork (`sh.c:164`), and the proofs file it
  at the parser's fallback line `LEcho []`, which no admissible input
  parses to; `REcho 2` stays admissible THERE ONLY.  Pipelines keep `PLRun
  []` (a pipeline that prints nothing is a real outcome, `cat f | cat` at an
  empty `f`).
- **The hook**: `lmh_noc` becomes optional (`Some` at pipelines and at
  `LEcho []`); the PAD (`GenOutPure.lm_alts_pad`, the in-flight line's
  entry) moves to `lmh_exf`, which already has the three properties it
  needs (admissible, free, not a panic); `UnionDecU.u_canon_name` needs a
  pad output that does not merge (to check).
- **The proofs, and who knows the true alternative**:
  - the constructors' NULL arm (formerly the fault at the null store,
    `UkSh.wp_ksh_memset_null`) is now `cmdalloc` -> `panic`: the CHILD,
    holding the lend (`Wc I 3`), prints `out of memory\n`, files `ROom` at
    its first byte, and exits paying `Wc I 0` -- the exec-failed diagnostic's
    shape (`ush_execfail_law`), at the panic walk (`UkShDiag`);
  - so no child returns the lend untouched: `ushf_wq`'s left arm has no
    producer and goes, and with it `uHwbl_f`'s payload use;
  - the fork re-entry's whole-lend row is refuted inside
    `wp_kshf_fork_core` (its `r <> -1` is discarded there today);
  - `uWcf0_of_pre_line_id`'s prompt-first arm files PEND at the block's own
    alternative (`lm_aprs I a`; `cat f` at an empty `f`, `RCRan`);
  - `gprompt_dollar`'s settled arm is dead at the union; `gwc_line_of_blk0`
    is reached only under the taint (`uHcltaint` instead).

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
