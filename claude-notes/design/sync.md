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

## 4. The durability link (RULED, owner 2026-09-27)

**What the kernel gave before.** `SpecSysSync.wp_sys_sync_sconf` returned
`flushed_sync γ e := ∃ e' ≥ e, log_flushed_bank γ e'` with `LogInv.
log_flushed_bank γ E := ∃ b D, log_epoch_lb γ E ∗ flushed b D ∗ ⌜snap_holds
D⌝` -- three INDEPENDENT conjuncts: "some committed file system exists",
nothing about the caller's state; the dispatcher's arm 22 dropped it.

**Why nothing weaker than an action at the sync instant works.** In
`echo a > f; echo b > f; sync; <cut>`, `echo b`'s last `end_op` commits
synchronously, `sync` takes the fast path, and nothing commits after: the
crash slot keeps the copy minted during `echo b`, whose witness admits `a`.
Some resource must strengthen the durable copy AT THE SYNC, and the boot
must be able to use it without ordering copies (lower bounds carry no
time; comparing two of them says nothing about which is newer).

**Notation.**  σ: the running abstract state (the file system's
authoritative `●σ`); σ_d: the durable state (what recovery yields; the
committed map); `I_app`: the application invariant holding the running
claim `A(σ)`; `CI`: the crash invariant `∃ σ_d, disk recovers to σ_d ∗
D(σ_d)` with `D` the application's durable claim (`AppDur.app_dur_raw`,
an iProp, exclusive parts at fresh names); `I_obs`: the ledger, crash-
surviving, owner of the typed-line list `●L`.

**The ghost state.**  Per era, a monotone counter γ_k with FRACTIONAL
authority `●{q} k` and persistent fragments `◯≥j`:
`●{½}k ∗ ●{½}k' ⊢ k = k'`; `●{q}k ∗ ◯≥j ⊢ j ≤ k`; `●{1}k ==∗ ●{1}(k+1) ∗
◯≥(k+1)`.  The typed-line list gains `sync` entries (appended by the
ledger's rx wand like redirect lines).  `Adm(ls, k)`: for k = 0 the
landed admissible set; for k ≥ 1, {the state at the k-th `sync` entry of
ls} ∪ {states of redirect rounds after that entry} -- the sets SHRINK in
k, so `Adm(ls, k) ⊆ Adm(ls, m)` for m ≤ k.

    A(σ) := … ∗ ◯⊒ls ∗ ●{½} k ∗ ⌜state(σ) ∈ Adm(ls, k)⌝     (running, in I_app)
    D(σ) := … ∗ ◯⊒ls ∗ ●{½} k ∗ ⌜state(σ) ∈ Adm(ls, k)⌝     (durable, in CI)

The counter's two halves are split between the running claim and the
durable copy: neither moves k alone, and whoever holds both knows they
agree.  The authority TRAVELS WITH THE CURRENT DURABLE COPY.

**The operations.**

1. **An ordinary file step** (echo's write): `I_app` moves σ and the
   deed; the new state is a round's state after the last `sync` entry, so
   `Adm(ls, k)` holds at the same k.  `CI` is untouched.
2. **Commit** (at the header write, `outstanding = 0`): the commit law
   today collects `A(σ)` at quiescence, runs the persistent transport
   `app_xfer_raw` (`□ ∀ r av, ▷ A r av ==∗ ▷ A r av ∗ ∃ r', ▷ A r' av`)
   and DROPS the old durable guest unread (`FsDurSnap.dsnap_step_xfer`).
   It becomes a MERGE: a second persistent application-supplied law,
   proved once per application,

       □ ∀ …, ▷ D_old ∗ ▷ A(σ) ==∗ ▷ A(σ) ∗ ▷ D(σ)

   which moves the counter's half from the old copy to the new one (the
   halves agree on k) and gives the new copy the running witness.  The
   WAL stays application-agnostic: the law is over the opaque guest `G`.
   Applications with nothing to carry prove it from the transport.
3. **`sys_sync(Fs)`**, generic in the caller's `Q`:

       Fs : ∀ σ, ⌜σ is running = durable⌝ ∗ ▷ G(σ) ={E}=∗ ▷ G(σ) ∗ Q

   The kernel fires `Fs` EXACTLY ONCE, at an instant between the call and
   the return where σ = σ_d, and returns `Q`.  FAST PATH (`!committing &&
   outstanding == 0` at the acquire of `log.lock`): the instant is the
   acquire; the equality is a new log-invariant conjunct, "quiescent ⇒ σ =
   σ_d", which needs EVERY change to σ to happen inside a transaction;
   `sys_sync` opens `CI` for this ghost-only step (the first opener of the
   crash invariant that is not a disk write).  SLOW PATH: `sys_sync`
   deposits `Fs` in the log invariant and sleeps; the committer fires every
   pending `Fs` right after the merge of step 2 (σ = σ_d there by
   construction: the commit captured σ with nothing outstanding and
   `begin_op` blocks while committing); the deposit is consumed, and
   `sys_sync` collects `Q` when it wakes.
   At the union, `Fs` opens `I_app`, bumps k with both halves, rewrites
   both witnesses to `Adm(ls', k+1)` (ls' contains this `sync` entry;
   true because the state IS the state at this sync, and σ = σ_d says the
   durable one is the same), and yields `Q := ∃ k, ◯≥k ∗ ◯⊒ls'`.
4. **Back to sh**: `/sync`'s exit payload (`UkSync.sync_pay`) carries `Q`
   through `wait()`; sh files it on the ledger's record of the round when
   it prints the prompt.  The ledger holds `◯≥m` for the m-th completed
   sync.
5. **Crash and boot**: the running claim and its half are lost; `CI`
   holds `D(σ_d)` with `●{½} k`.  Validity gives `m ≤ k`, so `state(σ_d)
   ∈ Adm(ls, k) ⊆ Adm(ls, m)`: the state at the last completed sync or a
   later round's -- the model's boot relation (§5).  The new era allocates
   a fresh counter with both halves AT THE COPY'S k, so the count (and the
   `sync` entries it numbers) runs across eras and a floor survives an era
   with no sync of its own.

**Kernel/WAL obligations.** (K1) the quiescent conjunct and the
in-transaction-only property of every running-state mover; (K2) the
commit's merge in place of the drop (`dsnap_step_xfer`, `fs_rec_permit`,
the commit law); (K3) `sys_sync`'s new contract with `Fs`: the fast-path
open of `CI` (masks unverified) and the slow-path deposit fired by the
committer; (K4) the dispatcher's arm 22 carrying `Fs`/`Q` to the user tier.

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

**As built (lane SY3-M, pure; `UnionAdm.v`, `UnionOutPure.v`,
`UnionAdmDemo.v`).**
- The line list is EVERY complete line (`ulines_of h`, `uline_of_u` of
  each body, cycle by cycle); a line's position is its global round index.
  The rx wand appends `uline_of_u b` at the newline completing `b`; the
  landed redirect list is its projection (`ulines_of_echof`).
- A sync RECORD `(p, S)`: `S` the files at the sync, `p` the sync line's
  position + 1; `srec0 = (0, ∅)`.  `uadm ls (p, S) s`: per name, `s !! N =
  S !! N`, or a chunk subset of a redirect at `N` in `drop p ls`.  At
  `srec0` it is `fadm_boot` (`uadm_srec0`).  `srec_le ls r r'` (`r.1 <=
  r'.1` and `uadm ls r r'.2`) is a preorder; `uadm_shrink`,
  `uadm_shrink_chain` (the counter form), `uadm_mono` (appending lines),
  `uadm_ustep` (a round of a line at a position >= p stays inside).
- The state at the sync is NOT a function of the lines (an open failure
  keeps the old content, visible only on the console), so the record is
  read off the cycle's RESOLUTION: `lm_good_sync s seg o` is `lm_good_out`
  with `o = usync_last ps cs s I w`, the last round of line `sync` resolved
  to `RSyncRan` whose whole block is on the wire (the pad never counts).
  On the machine the record is minted by `Fs` (it knows σ); the counter
  numbers the fires and the ledger files, at the prompt, the record of
  the latest completed sync.
- `union_phi`: `∃ W : list (fstate * option srec)`, cycle 0 boots `∅`,
  cycle `k+1` boots in `uadm (ulines_before h (S k)) (ulast_before h (snd
  <$> W) (S k))` -- the last completed sync of the earlier cycles, at its
  global position -- and `Forall2 (λ w seg, lm_good_sync w.1 seg w.2)`.
  The discipline (`lm_disc`) and its decider are untouched.
- Demos: `demo_sync_cut` (b after the cut, admitted), `demo_sync_cut_neg`
  (a after the cut, refuted at every `W`), `demo_nosync_cut` (no sync: a
  admitted), `demo_sync_inflight` (sync's prompt not out: a admitted).

## 6. Honest limits

- Limit 1 of app-file.md stands: the state at the sync is a chunk SUBSET of
  its redirect line (a write can fail invisibly at a full disk).
- Safety only: `sys_sync` may block forever under a continuous operation
  stream; then no prompt appears and the floor does not move.
- In reality this kernel commits at the last `end_op`, and sh serialises
  rounds, so a completed `echo b > f` is durable without a sync; the model
  cannot see it because `write` carries no receipt (app-file.md §6).

## 7. Rejected

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
