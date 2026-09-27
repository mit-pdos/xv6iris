# Worklist: `sync` in the union

Design: [`../design/sync.md`](../design/sync.md).  Order is the owner's:
the silent alternative goes first (it is the prerequisite for any negative
demo, and it closes the landed within-era hole), then the line, then the
durability link.

## Rules

- Every landing keeps `UInitUnion.union_adequacy_closed` closed and the
  three audits at the baseline (system 13, tree 13, union 14); whole-tree
  gate on the VM before every landing; commit and push to `main` at green
  checkpoints (owner, 2026-09-26).
- One lane at a time.

## SY1 -- DONE: xv6 d66e41c, no silent alternative (design §1-§2)

Open cleanups it left, none blocking:
- pipelines' `PLRun []` still in `PipesDisc.plsafe` (reaches the N-stage
  layer: `PipesView.pv_ok`, `PipeOutNEv.pwc_blkV_file_empty`);
- `LineModelLinks.lm_ab_noc`/`lm_apr_noc`/`lm_ab_noc_len` have no users;
- the user-tier LOAD/STORE leaves carry an in-page premise redundant with
  alignment (`WpUmodeLoad`, `UkLoad`, `UkLoadText`, `UkStore`,
  `WpUmodeStore`) -- the fetch clause's twin, which the owner had removed
  from `uinstr`; ask before touching;
- `UInitTreeBoot.v`'s header cites a lemma `tree_cc_wb_conj8_is_turn_to_taint`
  that does not exist.

## SY2 -- DONE: the `sync` line (design §3)

## SY3 -- the durability link (design §4-§5; RULED 2026-09-27, revised)

### State (update this block as lanes land)

- ON MAIN: SY3-K1 (`LogInv.log_res` gains `⌜out = 0 -> n = 0⌝`; new
  `iris/LogQuiet.v`: `log_quiet_committed`, `log_quiet`,
  `log_res_quiet_acc`, `P_fs_rec_quiet_acc`) and SY3-K2 (the commit MERGES
  the old durable guest: `FsDurSnap.dur_merge`/`dur_pair`/
  `dsnap_step_merge`, `AppInv.app_merge_raw`/`app_merge_raw_of_xfer`,
  `AppDur.app_dur_raw_merge`; every application derives the merge from its
  transport at `SystemAdequacy`'s call of `xv6_boot_era` (`Happ_merge`)).
  Merged at `966c6d815`; whole tree green, audits 13/13/14.
- ON BRANCH `sync3-m` (worktree `/shared/xv6iris-3m`, `855896fb8`, based on
  `2bbb6fdf5`; NOT on main because the ledger above it is red until SY3-A):
  the pure model -- `iris/UnionAdm.v` (line list `ulines_of`, records
  `srec`, `uadm`, `srec_le`, the shrink lemmas, `usync_last`,
  `lm_good_sync`), `iris/UnionOutPure.v` (the new `union_phi` over `W :
  list (fstate * option srec)` and its four ledger step lemmas),
  `iris/UnionAdmDemo.v` (the four demos, including the NEGATIVE
  `demo_sync_cut_neg`), and design §5 "as built".  First red file:
  `UnionOut.v` line ~572 (`union_phi_res`).
- NOT STARTED: K3 (helping + ghost commit + `S` + the hooked law + the
  custody lemma + `sys_sync`'s contract), K4 (the dispatcher's arm 22 and
  `/sync`'s payload), A (the application side and the ledger).

### Rules for every lane

- Read `CLAUDE.md`, `claude-notes/durable-notes.md` (Guiding principle,
  Orchestration, Build, Staleness, Shared-checkout discipline, The dev
  loop, Contracts and resources, Shaping a change so the sweep is small,
  The adequacy-print baseline), `claude-notes/remote-build-gcp.md`, and
  design `sync.md` §4-§5 in full before editing.
- Builds only on the GCP VM: `gcp-rocq/vmbuild.sh <tree> <log>` from the
  checkout's root (it syncs, deletes the dirty files' artifacts, builds
  `iris/` with `-k`; log `/tmp/<log>.log` on the VM; if the tool's timeout
  would kill it, run a detached copy of what the script does);
  `gcp-rocq/run-on-gcp --check Foo.v` for statement-only checks; a new
  worktree's remote tree needs one `gcp-rocq/run-on-gcp --proofs -k` first
  (~1 hour).  Never a local tree build; never a top-level `make` on the VM
  except the audit targets `audit-all-only` and `audit-tree-only` (no dump
  prerequisites).  The cones are large (`LogInv` ~370 files, `FsCrash`/
  `FsDurSnap` more): batch edits, one build per tree at a time.
- Git: branch per lane from current `origin/main`; commit by explicit
  path; never `git stash`/`reset`/`add -A`/`commit -a`/`--amend`; never
  `pkill`.  Landing: merge `origin/main` into the lane branch, build the
  merge on the VM, then `git push origin <branch>:main` (fast-forward
  only).  Commit messages end with the attribution line the harness
  specifies.
- Green means: whole tree (`run-on-gcp --proofs -k`, no plain `Error` in
  the log, `make -n` in `iris/` compiles nothing), audits system 13 / tree
  13 / union 14 textually equal to the baseline, `UInitUnion.
  union_adequacy_closed`'s STATEMENT unchanged unless the lane is SY3-A
  (whose end state changes `union_phi`'s body, by design).  No `Admitted`,
  no `Axiom`, no weakened contract.
- If a statement below is unprovable or the design is wrong, STOP and
  report to the owner with specifics; do not bend a contract.

### Lane SY3-K3 -- the ghost commit, `S`, helping, `sys_sync(Fs)` (kernel/WAL)

Goal: `sys_sync`'s contract becomes "fires the caller's `Fs` exactly once
at a ghost commit, returns `Q`" (design §4.3 items 2-4), proved for both
branches of the UNCHANGED C (`kernel/log.c` `sys_sync`).

Steps, in dependency order (each can be a commit; the tree must stay
green at each landing):
1. **The custody lemma.**  A variant of `RiscvExec.wp_hart_step`
   (`RiscvExec.v` ~751) that lends `start_auth (start_count g)` with
   `⌜n = gen_id + 1⌝` from `power_interp` (`RiscvPtsto.v` ~2813) into the
   client's `={⊤,∅}=∗` prefix and takes it back -- exactly what
   `wp_disk_step` (~1227) lends the DMA completion.  Then a kernel-level
   leaf that, at one instruction, opens `crash_inv` at `⊤` and runs a
   caller's update on `▷ riscv_crash_pred` with `start_auth` in hand.
   Check the crash invariant's single-opener rule (`RiscvPtsto.v` ~904-910)
   and document the new opener there.
2. **The opaque token `T` and the `∧ T` merge.**  Parametrise the WAL's
   guest interface by an opaque `T : iProp` (like `G`): `log_res`'s
   non-committing arm holds `T`; `LogQuiet.log_res_quiet_acc` lends it
   with the quiet bundle; `dur_merge` becomes `dur_merge' G T gt :=
   (∀ gt_o, ▷ G gt_o ==∗ ▷ G gt ∗ ▷ T) ∧ T`; the collection takes `T` from
   the checked-out `log_res` into the pair; `fs_commit_L_sector0_rec`'s
   `Q` (`FsCrash.v` ~3053) returns `▷ T`; the empty-log arm of `end_op`
   (`ProofEndOp.v` ~5133-5170) takes the right arm; `eo_tail` re-deposits.
   Every landed application instantiates `T := True` (no behaviour change)
   -- derive it generically, as K2 derived the merge from the transport.
3. **The hooked commit law.**  A second parked closure in `log_ctx` beside
   `snap_law_at` (`LogSnapLaw.v` ~99), same shape plus a HOOK `Φ` fired
   inside `fs_collect_dur` (`FsCollectAll.v` ~1800; the merge is applied
   at ~1898; `HSI` at ~1873) right after the merge, with the running claim
   and the new guest at the same map, at mask `⊤ ∖ ↑crashN ∖ ↑fsbN`.  Built
   by the same code as `fs_snap_law_build` (~1953).  Then `GC` as a
   lemma: design §4.3 item 3, a-d, using K1's `LogQuiet` accessors (the
   byte authority by opening `fsbN` as `ProofEndOp.eo_snap_law_of_auth`
   ~836-880 does, in a `⊤ ∖ ↑crashN` variant).
4. **The helping slot `H`** in `log_res` (both arms), with `saved_prop`
   tags; `eo_tail` (`ProofEndOp.v`, the re-acquire before `committing :=
   0`, `ncommit++`, `wakeup`) runs `GC(all Pending)` and flips them to
   `Done` BEFORE bumping `ncommit`.  Check (and prove) the premises of
   `LogQuiet` hold at that point on both the real and the empty-log path.
5. **`sys_sync`'s new contract** (`SpecSysSync.v`: the module type
   `SYS_SYNC`; `ProofSysSync.v`; `LinkSysSync.v`): generic in the caller's
   `T`/`G`-level `Fs` and `Q` (design §4.3 item 4); fast branch
   (`ProofSysSync.v` ~1500): `GC([Fs])`; slow branch: deposit, sleep until
   `ncommit > n0`, collect `Done`.  Keep the receipt-free callers compiling
   by instantiating `Fs` trivially (`Q := True`) where `sys_sync` is called
   today (`ProofSyscall.v` ~5813-5826, arm 22).  The old `flushed_sync`
   post may be deleted if nothing else uses it (grep first).
Acceptance: green (as above); `SpecSysSync`'s header rewritten to the new
contract; a paragraph in `design/fs-log.md` and `design/crash.md` (the new
crash-invariant opener) stating the new facts.
Risks: (R1) the masks at the hart step: `crashN` opened at `⊤`, then the
hooked law at `⊤ ∖ crashN ∖ fsbN` -- verify `appN`, `ftopN`, `iregN`,
`bitmapN`, `sbN`, `ipoolN`, `icEscN` are disjoint from both; (R2) `eo_tail`
must hold, after the commit, everything `LogQuiet`'s accessors need (the
reviewer believes `eo_open_to_batch … (fun _ => []) ∅ M0 HM0hdr HM0row`
at `ProofEndOp.v` ~5155 is it -- verify); (R3) `Fs`'s later: the guest is
under `▷`; unpack it the way `AppDur.app_dur_raw_merge` does.

### Lane SY3-K4 -- arm 22 and `/sync` (after K3)

- The syscall dispatcher's arm 22 (`ProofSyscall.v` ~5813) passes the
  user-tier caller's `Fs` in and its `Q` out, instead of the trivial
  instantiation; the user-tier row for syscall 22 (find it next to the
  other rows in `UexecExecInst.v` / the `xv6_sbundle`; `SpecSysSync` is
  its kernel contract) states it; `UkRunSys` gets the ecall leaf for
  `sync` with `Fs`/`Q` (model on the other ecall leaves there).
- `UkSync.v`: `sync_pay P R := P -∗ R` gains the receipt: the program
  calls `sync()` with the `Fs` its ENTRY was given and pays its exit with
  `Q`; `UkSyncEntry.sync_image_entry` (the union's entry for `/sync`) and
  `UShURound.usync_ran_pay`/`uHchild_sync` thread `Fs` in (from sh's
  round: it needs sh's `◯⊒ls'` including the sync line, and the round's
  position) and `Q` out (to the ledger via sh's prompt).  Keep `Fs`
  ABSTRACT at this lane (a parameter of the entry/child law), so K4 lands
  green before SY3-A instantiates it.

### Lane SY3-A -- the application side and the ledger (after K3, K4; merges `sync3-m`)

1. Merge branch `sync3-m` (the pure model) into the lane branch first.
2. The typed-line list: the ledger's authoritative list (`AppFile.fl_auth`
   / `fl_lb`, `AppFile.v` ~184-193, over `fwline`s) becomes (or gains) the
   full line list `UnionAdm.ulines_of` (every complete line, the sync line
   included; decision recorded in sync.md §5 "as built"); the rx wand
   appends `uline_of_u b` at the newline completing `b`.
3. The claims: the union's running claim (`AppFile.f_state`/`f_typed`,
   `AppFile.v` ~668, `file_pred` ~788) gains the running `●{¼} Ls`, `◯⊒ls`
   and the witness `state ∈ uadm ls (last Ls)`; the durable copy (the same
   predicate at fresh names, via the transport/merge) carries `●{½} Ls`;
   `T := ●{¼} Ls` is the union's token.  Provide the union's MERGE law
   (not derived from the transport any more: it moves the `½` and checks
   `T` against it) -- this needs an App-record field for the merge (today
   `Happ_merge` is derived from `al_xfer` in `SystemAdequacy`; add
   `al_merge` or widen `al_xfer`), and `T`'s birth in the era mint.
4. The union's `Fs` (design §4.3 item 5) and its instantiation in sh's
   sync round; `Q` filed at the prompt.
5. The ledger (`UnionOut.v` and above): the new `union_phi` body from
   `sync3-m` -- `union_phi_res`, the per-cycle record filed at the sync
   prompt, the boot comparison (design §4.3 item 7) at the era's first
   drain (where `f0_typed` is filed today, app-file.md §4.3).
6. Risk (R4), decide early: the durable copy must be RE-BASED to the new
   era's `γs` before the new era can crash (if the new era crashes before
   its first commit, `CI` still holds the previous era's copy with the
   previous `γs`).  Check whether the boot's genesis write
   (`ProofInitlog`'s seal, the recovery's header clear) runs the commit law
   / merge; if not, add a merge there or re-base at the PowerOn arm
   (`FsCrash.P_fs_swap`, `SystemAdequacy` ~1476-1492).  The ledger's floor
   likewise moves to the new era's `γs` at the boot (the era's first
   drain).
Acceptance: green; `union_adequacy_closed` restated only through
`union_phi`'s new body (from `sync3-m`); `demo_sync_cut_neg` is the
theorem's negative witness; design §4-§5 updated to "as built";
`sync3-m` deleted after the merge.
