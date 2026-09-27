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

## SY3 -- the durability link (design §4-§5, RULED 2026-09-27)

Lanes run in parallel where their files are disjoint; each lands on main
green (whole tree, audits 13/13/14) or stays on its branch.

- [ ] **SY3-K1** (kernel/WAL, riskiest; branch `sync3-k1`): the log-invariant
  conjunct "quiescent (`outstanding = 0 && !committing`) ⇒ running state =
  committed durable state", established by the commit and by genesis,
  preserved by every step; this needs EVERY change to the running
  authoritative state (`fs_top`'s movers, InodeRegion's `ireg_top_*`) to
  happen inside a transaction -- audit, prove, or report the counter-example.
- [ ] **SY3-K2** (WAL; branch `sync3-k2`): the commit's MERGE -- the old
  durable guest passed to a persistent application-supplied law `□ ∀ …, ▷
  G_old ∗ ▷ A ==∗ ▷ A ∗ ▷ G_new` in place of the drop (`dsnap_step_xfer`,
  `fs_rec_permit`, `LogSnapLaw`, `FsCollectAll`, `AppInv`/`AppDur`,
  `SystemAdequacy`'s slot); every landed application instantiates it from
  its transport (no behaviour change).
- [ ] **SY3-M** (pure model; branch `sync3-m`): `sync` entries in the line
  list, `Adm(ls, k)` with the shrink lemma, the boot relation over all
  earlier cycles' completed syncs (observational: prompt on the wire), the
  decider, the negative demo across a cut.
- [ ] **SY3-K3** (after K1, K2): `sys_sync`'s contract with `Fs` (fast path:
  fire at the acquire, opening the crash invariant; slow path: deposit,
  fired by the committer after the merge).
- [ ] **SY3-K4**: the dispatcher's arm 22 carrying `Fs`/`Q`; `UkSync`'s
  payload carrying `Q`.
- [ ] **SY3-A** (after M, K2, K4): the counter halves in the running and
  durable claims, the union's merge law and `Fs`, the floor on the ledger,
  the boot's comparison, `union_phi` at the new boot relation.
