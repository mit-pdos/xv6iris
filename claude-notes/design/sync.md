# Design: `sync` in the union -- a completed sync pins what the next boot sees

§1-§3 LANDED (§1-§2 at xv6 `d66e41c`, §3 lane SY2); §4-§5 PROPOSAL (the worklist is
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

- **Model.**  `FileDisc.LSync` (bytes `sync\n`, words `[cmd_sync]`,
  `line_file LSync = None`) is ADDITIVE like `LSecc`: `parse_line` never
  answers it, `UnionDisc.uline_of_u` reads it through `FileDisc.sync_parse`
  after the seccomp parser, `uline_nopipe` excludes it, and the union
  admits it outright (`UnionDisc.usync_ok`, `ubody_ok`'s fourth disjunct).
  `ralt_ok LSync` admits four: `RSyncRan` (code 19; `u_prompt`, the
  identity -- /sync ran, it prints nothing), `RSyncExec` (20;
  `alt_execsync`, `exec sync failed\n$ `), `RCFork` and `ROom`.  All free,
  none terminal.  Hooks (`UnionDiscDec.ulm_hooks_sync`): pan `RCFork`, exf
  `RSyncExec`, noc `None`.  The decider's candidates are
  `FileDiscDec.ralt_fix_cands LSync`.  Demos (`UnionDiscDec` §6):
  `demo_sync_parse`, `demo_sync_ran`, `demo_sync_execfail`,
  `demo_sync_ok`/`demo_sync_cat` (`echo hi > a.txt; sync; cat a.txt` prints
  `hi`); NEGATIVE `demo_sync_only` (the four and nothing else, at every
  state), `demo_sync_neg`, `demo_sync_neg_x`.
- **The program.**  `UkSync.wp_ksync_start` runs at a status-independent
  payload, handed `P` and `sync_pay P (ukn_pay N (-1))`, which `main`
  spends AFTER `sync()` returned -- SY3's durability receipt is a second
  premise of `sync_pay`.  `UShSync` is `UShSecc`'s geometry at /sync;
  `UkSyncEntry.sync_image_entry` takes any lend `P`, any status-independent
  payload `Q` and `□ sync_pay P (Q (-1))`.  /sync is the seventh pin of the
  fixed part (`FsSyncPin`, inum 22, in `FileFsPure.file_fs_pure`; every
  write/unarm lemma threads `i <> SYNC_INO`), resolved by
  `UShExecPin.sh_sync_pin_resolves`/`sh_sync_slot`.
- **The round** (`UShURound.uHchild_sync`): an EXEC line with no redirect,
  every alternative the identity, so the lend `Wcu I 3` goes to /sync
  whole and `usync_ran_pay` pays PEND at `RSyncRan` (the deed PRE -> PEND,
  the block owed whole; sh files RAN at its `$`, as for `RFRan sel`).  The
  exec failure (`usync_execfail_law`) and the out-of-memory death
  (`uHoom`) are the record's blocks beside the deed as found.  Dispatched
  at `LSync` by `UkShPipeForkTwin.wp_kshm_body_pipe_nc` in
  `ushq_body_law_union`; `UShUPipes.sh_round_holds_union_closed` takes
  `sh_sync_slot`, which `UInitUnionBoot` builds from the fixed part.

## 4. The durability link (RULED, owner 2026-09-27; revised after two reviews)

**Why an action at the sync is needed.**  In `echo a > f; echo b > f;
sync; <cut>`, `echo b`'s last `end_op` commits synchronously, `sync` finds
the log quiescent, and nothing commits after: the crash slot keeps the copy
minted during `echo b`, whose witness still admits `a`.  So the sync must
strengthen the DURABLE copy, and the boot must use it without ordering
copies (lower bounds carry no time).  The kernel's old receipt
(`flushed_sync`, three independent conjuncts) said nothing about the
caller's state, and the dispatcher's arm 22 dropped it.

### 4.1 Vocabulary

- σ: the running abstract state (the file system's authoritative map,
  `fs_top`), agreed with the application invariant's half.  σ_d: the
  durable (committed) state.  `I_app`: the application invariant; its body
  holds the running claim `A`.  `CI`: the crash invariant (`crash_inv`,
  `RiscvPtsto.v`), holding the snapshot beside the opaque application
  GUEST `G gt` (`AppDur.app_dur_raw`: `∃ r I, ghost_map_auth gt (1/2) I ∗ A
  r (abs_view I)` -- an iProp with exclusive parts at fresh names).  The
  ledger `I_obs` survives crashes and owns the typed-line list.
- Sync RECORDS (the pure model, §5 and `UnionAdm.v` on branch `sync3-m`):
  `srec := (p, S)` -- `S` the user-file state at the sync, `p` the sync
  line's global position + 1; `srec0 = (0, ∅)`; `uadm ls r s` the states
  admissible after record `r` given lines `ls`; `srec_le ls r r'` the
  preorder along which `uadm` SHRINKS (`uadm_shrink`,
  `uadm_shrink_chain`); `uadm_ustep`: a round of a line at position ≥ p
  stays inside.

### 4.2 The ghost state

**The sync list `γs`** (per era): a `mono_list` of sync records with
FRACTIONAL authority, `●{q} Ls` (`iris.base_logic.lib.mono_list`:
`mono_list_auth_own γs q Ls`, fragments `mono_list_lb_own γs Ls`).  Laws
used: halves agree; `●{q} Ls ∗ ◯⊒Ls' ⊢ Ls' ⊑ Ls`; with total `1`, append.
Invariant of every list: consecutive records rise (`srec_le` over the line
list), so the last record gives the SMALLEST admissible set.
Shares, at all times:

    durable  ●{½} Ls   in the current durable copy (the guest in CI)
    running  ●{¼} Ls   in the running claim (I_app)
    S        ●{¼} Ls   opaque application token held by the LOG
                       invariant's non-committing arm while no commit is in
                       flight; in the committer's hand from a real commit's
                       collection to its tail

Both claims' witnesses: `state(σ) ∈ uadm ls (last Ls)` (`srec0` when `Ls =
[]`), with `◯⊒ls` a lower bound on the ledger's line list.

**The helping slot `H`** (in the log invariant, both arms): `∃ m,
ghost_map_auth γH 1 m ∗ [∗ map] w ↦ st ∈ m, (Pending w Fs ∗ Fs | Done w Q ∗
Q)`, entries tagged by `saved_prop`s so the depositor recognises its own.

### 4.3 The operations

1. **An ordinary file step** (echo's write): `I_app` moves σ and the deed;
   the new state is a round's state after the last record (`uadm_ustep`),
   so the witness holds at the same `Ls`.  `CI` untouched.
2. **A real commit** (`end_op` with `outstanding = 0`; the collection runs
   at quiescence, the header write later on the disk thread).  The
   collection (`FsCollectAll.fs_collect_dur`) takes `S` from the log
   invariant (it holds the checked-out `log_res`) and agrees it with the
   running `¼`; it builds the MERGE WAND (`FsDurSnap.dur_merge`, landed by
   K2 as `∀ gt_o, ▷ G gt_o ==∗ ▷ G gt`) extended to carry `S`:

       dur_merge' G T gt := (∀ gt_o, ▷ G gt_o ==∗ ▷ G gt ∗ ▷ T) ∧ T

   The header-write permit (`FsCrash.fs_commit_L_sector0_rec`, mask ∅,
   inside the DMA completion) applies the left arm: `S` agrees with the old
   copy's `½` (so the list the new copy's witness was proved at is the old
   copy's), the `½` moves into the new copy, and `▷ T` comes back in the
   permit's `Q` (timeless, stripped by the permit's own update).  The
   EMPTY-LOG path (`n = 0`, no header write; `ProofEndOp.v` ~5133-5170)
   takes the right arm.  The commit's TAIL (`eo_tail`) re-deposits `S` into
   the log invariant.  WHY `S`: the collection holds the running claim but
   not the old copy, the permit holds the old copy but not the running
   claim (and not the log invariant: the lock may be held by another hart
   during `commit()`), so a share must travel from the collection to the
   header write to pin the list and block any append in between; the fast
   path knows `S` is home because it holds the log invariant's IDLE arm.
3. **The GHOST COMMIT `GC(Fss)`** -- a commit with no disk write, run with
   `log.lock` held, `outstanding = 0` and `committing = 0` (or by the
   committer at its tail, where the same holds):
   a. the hart lifting lemma lends the era's custody token `start_auth`
      (today lent only to the DMA completion, `RiscvExec.wp_disk_step`);
   b. open `CI` at `⊤`; K1's `LogQuiet.P_fs_rec_quiet_acc` gives the
      snapshot `P_dur_at gt_o D` and a closer at any name over the same
      map; `LogQuiet.log_res_quiet_acc` lends the bundle the commit law
      consumes; `log_quiet_committed`: the committed map is the logged
      view;
   c. run the HOOKED commit law at `⊤ ∖ ↑crashN ∖ ↑fsbN`: the collection
      (the one place where the running claim and the fresh guest meet at
      one map -- `HSI` in `fs_collect_dur`), the merge applied at once to
      the old guest, then each `Fs ∈ Fss` fired INSIDE the collection with
      the running claim and the new guest at the same map;
   d. close `CI` with the new pair (same committed map), return the loan.
   Nothing changes on disk.  `Fs` has: the new guest's `½`, the running
   `¼` (it opens `I_app`), `S` -- full authority.
4. **`sys_sync(Fs)`**, generic in the caller's `Q`, with `Fs : ∀ gt I, G⁰
   gt I ∗ T ∗ R I ={E}=∗ G⁰ gt I ∗ T ∗ R I ∗ Q` (`G⁰ gt I` the guest
   unpacked at map `I`, `R I` the running claim at `I`):
   - FAST branch (`!committing && outstanding == 0` at the acquire,
     `ProofSysSync.v` ~1500): `GC([Fs])`, return `Q`.
   - SLOW branch: allocate `w`, deposit `Pending w Fs` in `H`, remember
     `n0 = ncommit`, sleep (the C is UNCHANGED).  The committer's `eo_tail`
     (after a real or an empty-log commit) runs `GC(all Pending)`, flips
     each to `Done w Q`, then bumps `ncommit` and wakes.  `sys_sync` wakes
     with `ncommit > n0`, finds `Done w Q`, removes it, returns `Q`.
     Correct because a waiter depositing while `committing = 1` does so
     after that commit's collection, so the FIRST `eo_tail` after the
     deposit is the one that moves `ncommit` past `n0` and lands a state
     covering every change before the call; commits are serialised.
5. **The union's `Fs`**: with full authority, append the record `r =
   (p, state(σ))` (p from sh's lower bound `◯⊒ls'` INCLUDING the sync
   line, carried in by the payload -- the running claim's own lower bound
   cannot contain it, no file step runs after the line is typed); rewrite
   both witnesses to `uadm ls' r` (the state is `r.2` itself: `uadm_self`);
   the chain rises because the running state was in `uadm ls (last Ls)`.
   `Q := ◯⊒(Ls ++ [r]) ∗ ⌜r = (p, state)⌝`.
6. **Back to sh**: `/sync`'s exit payload (`UkSync.sync_pay`) carries `Q`
   through `wait()`; sh files the record on the ledger at the sync round's
   prompt (the model's `usync_last`, §5).
7. **Crash and boot**: the running claim and its `¼` die; `S` dies with
   the log.  `CI`'s copy has `●{½} Ls` and `state ∈ uadm ls (last Ls)`; the
   ledger's fragment `◯⊒Ls_m` (ending in the last completed record) gives
   `Ls_m ⊑ Ls`, so the last completed record is in `Ls` and, the chain
   rising, `state ∈ uadm ls (last Ls) ⊆ uadm ls r_m` -- the model's boot
   relation.  The new era allocates a FRESH `γs` with all three shares AT
   `Ls`; the ledger's floor is RE-STATED as a fragment of the new era's
   `γs` (the counter is per era), and the durable copy must be re-based to
   the new era's `γs` before the new era can crash (see the plan's risk
   R4).

### 4.4 What is NOT done, and why

- No C change (a quiescence loop in `sys_sync` was proposed and rejected:
  the helping slot keeps the current, correct code).
- No change to the disk write permit (a fancy-update permit is sound and
  needs no device-model change, but the running = durable tie exists only
  inside a collection, the log invariant is unreachable at the DMA instant,
  and the empty-log commit has no header write -- so the header write is
  never the firing point).
- No log-invariant fact "quiescent ⇒ σ = σ_d" (the three invariants share
  no ghost state; the empty-log path re-quiesces with an old snapshot):
  the ghost commit makes the durable copy from the running claim instead.

## 5. The crash semantics (the model's boot relation)

`fadm_boot` ("absent, or states admissible given every earlier line")
becomes, per cycle, `Adm(lines before the cut, m)` with m the number of
`sync` rounds of ALL previous cycles whose prompt is ON THE WIRE (the pad
of an in-flight line may name the RAN alternative and must not count).
Per round the states a redirect round passes through are the model's
intermediate states (the truncate's `[]`, the chunk subsets).  Two
negative demos carry it: within an era, `echo a > f; echo b > f; cat f` ->
`a` refuted (landed, `UnionDiscDec.demo_no_silent`); across a cut, `echo a
> f; echo b > f; sync; <cut>; cat f` -> `a` refuted.  Without any sync the
relation is the landed one (k = 0).

## 6. Honest limits

- Limit 1 of app-file.md stands: the state at the sync is a chunk SUBSET of
  its redirect line (a write can fail invisibly at a full disk).
- Safety only: `sys_sync` may block forever under a continuous operation
  stream; then no prompt appears and the floor does not move.
- In reality this kernel commits at the last `end_op`, and sh serialises
  rounds, so a completed `echo b > f` is durable without a sync; the model
  cannot see it because `write` carries no receipt (app-file.md §6).

## 7. Rejected

- **A quiescence loop in `sys_sync`'s C** (fire only at a quiescent
  point): works, but the current C is correct; helping (§4.3 item 4) keeps it.
- **Firing `Fs` at the header write** (with a fancy-update permit): the
  tie running = durable is not a resource there, the log invariant is
  unreachable at the DMA instant, and empty-log commits have no header
  write.
- **A log conjunct "quiescent ⇒ running = durable"**: not maintainable
  (SY3-K1's finding); the ghost commit replaces it.

- **Commit POSITIONS** (the commit told its index in the committed
  history, the durable copy carrying it, the boot comparing it with the
  sync's index): works, but puts a disk-log ordering into the WAL's
  interface and the application; the counter-in-the-copy (§4) needs no
  order of copies at all.
- **A persistent "shrinking set" fact alone**: `Adm(ls, k)` shrinks in k,
  but an old copy carries a small k and the boot needs the large one;
  fragments bound the count from the wrong side.  The fix is to put the
  counter's AUTHORITY in the durable copy (§4).
- **A counter authority in the ledger**: the copy's fragment is then
  bounded ABOVE by the completed syncs -- the wrong direction.
- **A durable register without the merge**: the transport never sees the
  old copy; the commit's merge (§4 step 2) is what makes the register
  idea work.
