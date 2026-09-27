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

**Where the WAL names the application's two opaque things** (ruled at the
K3 cut, 2026-09-27).  The token `S` sits in the log invariant and the
waiters' hooks sit in the log invariant's helping slot, so both have a
TYPE the WAL must be able to write and the application must be able to
match, at one place both can name.  That place is the machine's fixed
ghost record: `RiscvPtsto.riscvFixedGS` gains two client slots beside
`riscv_crash_pred`,

    riscv_sync_tok  : nat -> iProp Σ            (* the token, per era   *)
    riscv_sync_hook : nat -> iProp Σ -> iProp Σ  (* the hook family, per era *)

filled by adequacy from two parameters stated at the same raw gnames as
`Pc` (`Tk`, `Hk`: functions of the four gnames and the fixed part `c`) and
delivered to every boot by the record-shape equation (`boot_fixedGS`), so
no era-side equation is needed.  The WAL writes `T := riscv_sync_tok
gen_id` and a waiter's hook as `riscv_sync_hook gen_id Q`; the application
supplies, at the era mint, a persistent RUNNER (`AppInv.app_sync_run`)
that fires `riscv_sync_hook gen_id Q` on the guest, the running claim and
the token at one map -- that is the only place the family's meaning is
used.  Every landed application takes `Tk := fun _ => True`, `Hk := fun _ Q
=> Q`, and the runner is `iFrame`.  REJECTED on the way: a `saved_prop`
per opaque index in `log_names` -- agreement costs a later, and a hook is
a wand fired inside a fupd, which cannot absorb it; parametrising
`log_res` (an arity change in ~370 files); a class ambient in the WAL's
cone.

**The helping slot `H`** (in `log_res`, both arms; `LogHelp.v`): a
`ghost_map` at the new `log_names` field `ln_help`, keys the waiters'
ids, values `(γw, n0)` -- the waiter's escrow gname and the `ncommit`
word it read at its deposit.  Per entry, an ESCROW invariant at `helpN
.@ w` over a `mono_nat` at `γw` with three arms,

    esc Q γw := (Q ∗ ◯ 1)  ∨  ●{½} 0  ∨  ● 1          (◯ = mono_nat_lb_own,
                                                        ● = mono_nat_auth_own)

and the entry's state in the slot

    Pending:  riscv_sync_hook gen_id Q ∗ ●{½} 0 ∗ ⌜n0 = nc⌝ ∗ ⌜cmt = true ∨ out ≠ 0⌝
    Done:     ● 1

`nc`, `cmt`, `out` are `log_res`'s own cells.  A waiter allocates `γw` at
`0`, puts one half into the escrow (middle arm) and one into its `Pending`
entry, and keeps the full fragment `w ↪[ln_help γ] (γw, n0)` and the
escrow's handle at its own `Q`.  The committer's FLIP, holding the entry's
half and the `Q` the ghost commit produced, opens the escrow: the first
arm is refuted (`◯ 1` against an authority at `0`), the third by the
fractions, the middle yields the other half; it joins, bumps the counter
to `1`, leaves `Q ∗ ◯ 1` in the escrow and `● 1` in the `Done` entry.  The
waiter's COLLECT, at `ncommit ≠ n0`, finds its entry `Done` (the `Pending`
arm says `n0 = nc`), deletes it, and with `● 1` opens the escrow: the two
token arms are refuted by the fractions, the first yields `▷ Q`, and the
escrow closes in its terminal third arm.  No `saved_prop`: the escrow
pins `Q` to `w`, every token arm is timeless, and the one `▷` (on `Q`) is
stripped by the waiter's next instruction.  The two pure clauses are what
the two readers need: a fast-path `sys_sync` (`cmt = false`, `out = 0`)
knows every entry is `Done`, so it flips nothing.

As built (`LogHelp.v`): `log_help γ nc out cmt := ∃ m, ghost_map_auth
(ln_help γ) 1 m ∗ [∗ map] w ↦ e ∈ m, log_help_entry nc out cmt w e`, the
entry being the `∃ Q, inv (helpN .@ w) (esc Q e.1) ∗ (Pending ∨ Done)`
above.  Four lemmas: `log_help_deposit` (at `cmt = true ∨ out ≠ 0`; a
fresh `w ∉ dom m`), `log_help_extract` (every Pending hook out, and a
return wand `∀ nc' out' cmt', ([∗ list] Q ∈ Qs, Q) ={⊤}=∗ log_help γ nc'
out' cmt'` -- the flip, `esc_flip`, per Pending entry), `log_help_collect`
(`n0 ≠ nc`), `log_help_cells` (the writers that keep `nc`); genesis is
`log_help_empty`.  The waiter reads the escrow through ITS OWN handle: the
entry's `Q` is existential and never compared with the waiter's, since
the full authority `● 1` out of the Done entry refutes the escrow's two
token arms whichever invariant it is read through.

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

       dur_merge G T gt := (∀ gt_o, ▷ G gt_o ==∗ ▷ G gt ∗ T) ∧ T

   (`T` NOT under a later on the way out: the wand captures the token
   itself and returns it; the old copy's share is agreed with it UNDER
   the old copy's later -- `▷ ●{½}Ls_o ∗ ●{¼}Ls ⊢ ▷ ⌜Ls_o = Ls⌝` -- and
   moved into the new copy's later.)  The header-write permit
   (`FsCrash.fs_commit_L_sector0_rec`, mask ∅, inside the DMA completion)
   applies the left arm and returns `T` in the permit's `Q`, which rides
   the write's receipt to the commit's tail.  The EMPTY-LOG path (`n = 0`,
   no header write; `ProofEndOp.v` ~5133-5170) takes the right arm.  The
   commit's TAIL (`eo_tail`) re-deposits `S` into the log invariant.  WHY
   `S`: the collection holds the running claim but not the old copy, the
   permit holds the old copy but not the running claim (and not the log
   invariant: the lock may be held by another hart during `commit()`), so
   a share must travel from the collection to the header write to pin the
   list and block any append in between; the fast path knows `S` is home
   because it holds the log invariant's IDLE arm.
3. **The GHOST COMMIT `GC(Qs)`** (`LogGhostCommit.log_ghost_commit`) -- a
   commit with no disk write, run with `log.lock` held and the batch
   quiescent (the fast path: `outstanding = 0`, `committing = 0`; the
   committer's tail: the checked-out batch at `n = 0`), at ANY point of a
   kernel proof (it is a `mWP e -∗ mWP e` rule):
   a. CUSTODY.  `HartCustody.wp_start_auth_fupd`: for any expression of
      this generation, a client fupd at `⊤` runs against `state_interp`'s
      `start_auth (start_count g)` with `⌜start_count g = gen_id + 1⌝`
      WITHOUT taking a step -- `wp_unfold` once, the live/dead case split
      of `RiscvExec.wp_hart_step` (dead: `wp_dead`), the hook, the same
      `state_interp` handed to the continuation's own unfolding.  No
      instruction leaf changes; the instruction chain (`swp_loop` →
      `swp_tick_wrap_ex` → … → `wp_hart_step`) is untouched.
      `wp_crash_fupd` opens `crash_inv` at `⊤` inside it: the second
      opener of the crash invariant beside the DMA completion.
   b. open `CI` at `⊤`; the seam at the parked law's `G` turns the slot
      into the record and the old guest `▷ G gt_o` (the record is
      timeless, so it comes out of the invariant's later); K1's
      `LogQuiet.P_fs_rec_quiet_acc` gives the snapshot `P_dur_at gt_o D`
      and a closer at any name over the same map; `log_quiet_committed`:
      the committed map is the logged view.  The quiescent bundle
      `log_quiet` comes from K1's `log_res_quiet_acc` (fast path) or from
      the tail's checked-out batch (`log_state_quiet_acc`).
   c. open `fsbN` (as `ProofEndOp.eo_snap_law_of_auth` does) and run the
      HOOKED LAW parked in `log_ctx` at `⊤ ∖ ↑crashN ∖ ↑fsbN`
      (`LogSnapLaw.snap_law_ghost`): it takes the old guest, `T` and the
      hooks `[∗ list] Q ∈ Qs, riscv_sync_hook gen_id Q`, runs the
      collection (the one place the running claim and the fresh guest half
      meet at one map -- `HSI` in `fs_collect_dur`), applies the merge to
      the old guest INSIDE the collection, fires every hook there through
      `app_sync_run` (guest half at `gt`, the new guest's claim, the
      running claim, `T`, all at map `I`), and returns `∃ gt, P_dur_at gt
      D ∗ ▷ G gt ∗ T ∗ [∗ list] Q ∈ Qs, Q`.  (The law returns the guest
      rather than a pair because the merge must be applied where the
      running claim is in hand, and the hooks after it.)
   d. close `CI` with the new pair at the same committed map, return the
      loan.  Nothing changes on disk.
4. **`sys_sync(oQ)`**, `oQ : option (iProp Σ)` (the dispatcher's arm 22
   passes `None`; `/sync` passes `Some Q`), premise `hook_opt gen_id oQ`,
   post `Q_opt oQ`:
   - FAST branch (`!committing && outstanding == 0` at the acquire,
     `ProofSysSync.v` ~1500): `GC([Q])`, return `Q`.
   - SLOW branch: allocate `w` and `γw`, allocate the escrow at `Q`,
     deposit `Pending` in `H` at `n0 = ncommit`, sleep (the C is
     UNCHANGED).  The committer's `eo_tail` (after a real or an empty-log
     commit; `committing` still reads 1, the lock held) extracts every
     `Pending` hook (`LogHelp.log_help_extract`) and runs `GC(all)` BEFORE
     the `committing := 0` store; the `Q`s ride in the committer's hand
     through the stores, `ncommit++` and `wakeup` (all under the lock), and
     the re-deposit feeds them to the extract's wand, which fills each
     escrow and flips every entry to `Done` at the NEW cells -- no waiter
     can observe the slot in between.  `sys_sync` wakes with `ncommit ≠
     n0`, so its entry is `Done` (`log_help_collect`): it deletes the
     entry, takes the token, opens its escrow and leaves with `▷ Q`,
     stripped at the next instruction.  Correct because a waiter
     depositing while `committing = 1` does so after that commit's
     collection, so the FIRST `eo_tail` after the deposit is the one that
     moves `ncommit` past `n0` and lands a state covering every change
     before the call; commits are serialised.
5. **The union's `Fs`** (SY3-A instantiates `Hk`): with full authority,
   append the record `r = (p, state(σ))` (p from sh's lower bound `◯⊒ls'`
   INCLUDING the sync line, carried in by the payload -- the running
   claim's own lower bound cannot contain it, no file step runs after the
   line is typed); rewrite both witnesses to `uadm ls' r` (the state is
   `r.2` itself: `uadm_self`); the chain rises because the running state
   was in `uadm ls (last Ls)`.  `Q := ◯⊒(Ls ++ [r]) ∗ ⌜r = (p, state)⌝`.
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
   R4).  The token's birth is the era mint's: `LogDefs.log_ghost_alloc`
   takes `riscv_sync_tok gen_id` and puts it in `log_free_tok`, which is
   what `initlog` seals into the first `log_res`.

### 4.5 The application side (RULED at the SY3-A cut, 2026-09-27)

What the kernel side (K3, K4) fixed: the WAL names an opaque token
`riscv_sync_tok k` and hook family `riscv_sync_hook k Q` (§4.2); the merge
`dur_merge G T` moves the old copy into the new one with the token; the
ghost commit fires hooks inside the collection through the runner
`app_sync_run_raw A T Hk`; `sys_sync` and `/sync` carry `oQ : option
(iProp Σ)`.  Four facts about the union's side drive the rest (all
verified in the tree): only PERSISTENT facts travel from `/init` to the
ledger (the first-drain path is `fturn_file` → `f0_bl` → the console claim
→ `udrain_ret`); the ledger's PowerOn step (`Hobs`) and the crash slot's
swap (`Hswap`) are two separate invariant openings, so no hook ever holds
the durable copy and the ledger together; the ledger's per-era maps
(`f0_map`, `pera_map`, `pin_map`) are filled at the on-arm with fresh
persistent registrations; and the installed iris has no `mono_list`
wrapper (the tree writes `own γ (●ML{#q} l)` with the algebra's lemmas).

**Names.**  The fixed part `union_gn` gains two gnames born at
`al_birth` into `Cl c`, hence into the LEDGER: `ugn_reg` -- the sync
registry, a `ghost_map nat gname` from era to that era's sync-list gname,
auth in `union_led`, fragments `k ↪□ γs` persistent -- and `ugn_cm` -- the
COMMIT-ERA counter, a `mono_nat` whose full authority travels with the
durable copy and the parked running claim (below), born in era 0's turn.
`file_names` gains `fn_sync : gname` (the era's sync list).  The token
and the hook family, as the fixed record's closed terms over `c` and `k`:

    Tk c k   := ∃ γs Ls, k ↪[ugn_reg c]□ γs ∗ ●{¼}_{γs} Ls
    Hk c k Q := ∀ gt I r r', ghost_map_auth gt ½ I -∗ ▷ file_pred c r' (abs_view I)
                 -∗ ▷ file_pred c r (abs_view I) -∗ Tk c k ={∅}=∗ (the same four) ∗ Q

**The sync part of the claim** (`file_pred c r av` gains a conjunct
`sync_claim c r av`, two arms each for the two instances):

    durable, BASED:    ∃ k γs Ls, k ↪□ γs ∗ ●{½}_{γs} Ls ∗ ● ugn_cm k ∗ gen_started k
                       ∗ ◯⊒ls ∗ ⌜chain ls Ls⌝ ∗ ⌜fcontent av ∈ uadm ls (last Ls)⌝
    durable, UNBASED:  ◯⊒ls ∗ ⌜fcontent av ∈ uadm ls r⌝ (pure, at the record it was left at)
    running, PARKED:   gen_id ↪□ γs ∗ ●{¼} Ls ∗ ●{½} Ls ∗ ● ugn_cm k' ∗ gen_started k' ∗ witness
    running, COMMITTED: gen_id ↪□ γs ∗ ●{¼} Ls ∗ mono_nat_lb ugn_cm gen_id ∗ witness

(`chain ls Ls`: consecutive records rise, `srec_le`; the running arms are
at the era's `fn_sync r = γs`.)  The copy is UNBASED from PowerOn to the
era's first commit and BASED at the current era from then on; the running
claim is PARKED (it holds the era's durable half) until the first commit
and COMMITTED after.  WHY THE COUNTER: the merge must know that a based
copy is THIS era's, and the boot must know that no later era than the
copy's completed a sync; neither is a ghost fact without it.  With it both
are: a based copy holds `● ugn_cm k` and `gen_started k`, a committed
running claim holds `◯ ugn_cm gen_id`, and the WAL lends `start_auth n`
with `n = gen_id + 1` into the merge (`dur_merge` gains the loan; the
permit and the ghost commit both hold it), so `gen_id ≤ k ≤ gen_id`.

**The merge** (`al_merge`, the union's own, no longer derived from the
transport): PARKED + any copy: drop the old copy's sync part, base the new
copy with the parked half, bump the counter to `gen_id` (the loan gives
`k' ≤ gen_id`), mint `◯ ugn_cm gen_id`, the running claim becomes
COMMITTED.  COMMITTED + BASED at `k`: the counter pins `k = gen_id`, the
registry pins `γs`, the token agrees the lists, the half moves.
COMMITTED + UNBASED: refuted (`◯ gen_id` against a counter the transport
took away -- see PowerOn -- cannot exist: the unbased arm holds no counter
while the committed arm's bound came off the copy's authority; the case is
closed by the counter's absence, i.e. the unbased copy is only ever met by
a parked claim).  The token is returned on both arms; the merge sets the
new copy's witness from the running claim's.

**The hook** (`Hk` above, the union's `Fs`): the guest is based (the
hooked law applied the merge first), so guest ½ + running ¼ + token ¼ is
the full authority; append `r = (length ls', fcontent av)` with `ls'` sh's
lower bound including the sync line; rewrite both witnesses to `uadm ls'
r` (`uadm_self`, the chain rises by the running witness); `Q := ◯⊒_{γs}
(Ls ++ [r]) ∗ ◯ ugn_cm gen_id ∗ ⌜r = (length ls', fcontent av)⌝`.

**PowerOn** (`al_xfer`, the transport at `Hswap`; the slot keeps its
`r`, `I`, `gt`): a BASED copy is UNBASED in place -- its `k ↪□ γs`,
`●{½} Ls`, `● ugn_cm k`, `gen_started k` and its pure facts move into the
boot resource `B r'` (under the later, all timeless); an unbased copy
hands over its pure facts only.  **The ledger's on-arm** (`union_led_pow`,
era `k+1`): allocates `γs_{k+1}` with full authority at `[]`, registers
`k+1 ↪□ γs_{k+1}`, and yields into the era's turn (`union_turn`, a new
conjunct): the full authority, the registration, its per-era FLOOR map
(persistent: for every era `j`, `◯⊒_{γs_j} F_j` with `F_j`'s last record
the last completed sync as of era `j`, and `◯ ugn_cm j'` for the era `j'`
of the last completed sync), and at era 0 the counter `● ugn_cm 0`.
**The founding law** (`al_found`, a new `App` field replacing K3-2's
`HTk`; runs at `xv6_boot_era` with `Tn` and `B r'`): from the copy's
`● ugn_cm k'` and the floors' `◯ ugn_cm j'`, `j' ≤ k'`; the floor `F_{k'}`
against `●{½}_{γs_{k'}} Ls_c` gives `F_{k'} ⊑ Ls_c`, so the global last
record is in `Ls_c` and `s0 ∈ uadm ls (last Ls_c) ⊆ uadm ls r_m`
(`uadm_shrink_chain`); update `γs_{k+1}`'s list to `Ls_c`, split ½ (parked)
+ ¼ (running) + ¼ (the token `Tk c (k+1)`), drop the dead era's half,
found the running claim PARKED with the counter, and hand `/init` (through
the turn's remainder) the persistent `◯⊒_{γs_{k+1}} Ls_c` and the pure boot
fact, which `/init` files with `f0_bl` and the ledger reads at the first
drain: the era's floor `F_{k+1} := Ls_c`, and the model's boot relation
`s0 ∈ uadm (ulines_before h (S k)) r_m`.  Era 0: `Happ_init`'s copy is
unbased at `srec0`; the founding takes the counter from the turn.

**The ledger** (`union_led`): the line list becomes the FULL list
(`UnionAdm.ulines_of`, every complete line; sh's `flw` and `f_typed` read
the redirect lines through `omap echof_ws`, `ulines_of_echof`); the floor
map above; `union_phi_res` over `sync3-m`'s `W : list (fstate * option
srec)`; at a sync round's prompt sh files `Q` (persistent) and the ledger
extends the era's floor and matches `r` with the model's `usync_last`.

**sh's round**: `usync_exec_sup` at `Some Q` with the hook resource
`riscv_sync_hook gen_id Q` PROVED by sh from `Hk c gen_id Q` through a
persistent seam `□ ∀ Q, Hk c gen_id Q -∗ riscv_sync_hook gen_id Q` minted
at the boot era from the record-shape equation and carried in
`union_links`; the hook's body uses sh's lend (the deed's state `s`, the
tie `f_ok av s`, `◯⊒ls'` from `flw` over the full list).

**Adequacy**: the `App` record gains `al_merge`, `al_found`, `al_sync_run`
and the values `al_tk`/`al_hk`; `SystemAdequacy.xv6_power_adequacy_gen`
takes them in place of K3-2/K3-3's `HTk`/`HHk`/`Htok`/`Happ_sync_run`;
every landed application takes the trivial values.  No machine change
except `dur_merge`'s started-auth loan (WAL level).

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
