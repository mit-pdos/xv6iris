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

**No real execution reaches it.**  sh prints the next `$ ` after `wait`,
ignoring the status, so the question is which child deaths print nothing on
the console: `argv[0] == 0` (`sh.c:77`) and `cmd == 0` (`:68`) are
unreachable at a non-empty admissible line; exec failure and fork failure
print; a kill needs a `kill` caller (none in the union; the taint covers
it); an unexpected trap prints on the KERNEL UART (not the theorem's) and
kills, but a verified program faults nowhere and exec allocates the stack
eagerly (`exec.c:91`), so the lazy-`vmfault` OOM kill is unreachable.  The
silent alternative is proof convenience (RULING HOLD-POS) standing on an
unreachable `sh.c` branch.

## 2. Removing it: every silent filing becomes the round's TRUE alternative

The model: `ralt_ok` drops `REcho 2`, `RFSilent`, `RCSilent` from the echo,
redirect and cat lines; `LSync` never has one.  Pipelines keep `PLRun []`
(a pipeline that printed nothing is a real outcome, e.g. `cat f | cat` at
an empty `f`); `LSecc` keeps its silent round (the seccomp round is
terminal, design `seccomp.md` §2).  THE PRINCIPLE: wherever a proof filed
the silent alternative because the filer did not know what the child did,
some process DID know, and the proof is re-routed to it.

**The hook splits** (`LineModelLinks.lm_hooks`).  `lmh_noc` served two
unrelated needs:

- the PAD (`GenOutPure.lm_alts_pad`: the in-flight line's entry when the
  stage's list runs one short) needs only admissible, free, not a panic --
  `lmh_pad : lm_line -> nat`, total (the redirect's `RFExec`, sync's
  ran-alternative, the cat's `RCExec`, echo's `REcho 1`);
- the SILENT FILING needs `cont = u_prompt` -- `lmh_sil : lm_line -> option
  nat`, `Some` only where the model has a silent round (pipelines, seccomp).

A pad entry never reaches the wire (its block has not started), so the pad
choosing a "ran" alternative says nothing -- which is why §5's floor is
OBSERVATIONAL (§5).

**The four fallbacks, and their replacements:**

- (A) `UShURoundDefs.uWcf0_of_pre_line_id`, the prompt-first-byte arm: the
  block credential it destructs already names its alternative `a` (with
  `lm_apr I a`), and a prompt-first block has `cont a = u_prompt` (the
  derivation is in `uWcf0_of_posts_alt`); file PEND at `a` itself.  This is
  `cat f` at an empty `f` (`RCRan`), today filed as `RCSilent`.
- (B) `uHwbl_f : Wcf I 3 -∗ Wcf I 0`, "PEND at the silent alternative",
  spent by `UkShFork.wp_kshf_fork_at` at two sites: (i) the re-entry's
  "lend came back whole" row, which `fork1`'s panic makes unreachable --
  refute it at the re-entry (the answer is not -1 there) rather than
  convert; (ii) a child's exit payload `ushf_wq I := Wc I 3 ∨ Wc I 0` at
  its LEFT arm, the child that returned the lend untouched.  Every child
  of a line with no silent round pays the RIGHT arm, converting at its own
  alternative (`uHwbl_f_at a`, the law restated at an alternative the
  child names, with `cont a = u_prompt` and a step the deed can pay):
  sync's exit pays PEND at its ran-alternative after `sys_sync` returns.
  Whether the left arm can then leave `ushf_wq` for good, or stays for the
  pipeline/seccomp children, is SY1's first finding.
- (C) `GenLinksLine.gprompt_dollar`'s settled arm and (D)
  `gwc_line_of_blk0` / `LineModelLinks`' `lm_ab_noc`/`lm_apr_noc` block:
  generic laws where the prompt writer holds only an owed credential.  They
  take `lmh_sil l = Some a` as a premise (the models that have one) or the
  alternative as a parameter from a holder that knows it (the deed's PEND
  at the union).

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
