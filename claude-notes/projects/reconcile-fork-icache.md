# Reconciling the fork: local icache line (C1–C7) × origin's kfork line

Two sessions diverged at 30aa4741 (design §13.7, 2026-08-09) and both
shipped: LOCAL proved iget/iput/the five-arm escrow/boot and retired
the emp placeholders (kexit/fileclose/iput audit to platform+funext);
ORIGIN proved kfork/sys_fork, moved `NFILE` to `FdSlots` (breaking the
IrefSlots→FileInv cycle their way), canonicalized the reference
authority's gname (`irefNameG`, ~145 files of arity drops), changed the
Arc algebra to `natR` with count-0 SHARES, and designed (code-free) a
proportional-share cwd/file payload. Full recon map: the 2026-08-10
session's divergence report (both sides' inventories, the collision
list C1–C8).

RULING (2026-08-10): **local is the base.** Origin→local is bounded;
local→origin re-proves ~7000 lines behind an unsolved design question.

## The stages (one branch + commit each, EC2-validated)

- **T1** — free merges: 394f6126 (sconf/mie), 5f56f2d4 (CSR b-pins),
  07a80127 (wp_next_at), 3217149b (ops_ok), ac6200b8 (dead-import
  sweep, re-audit against our tree), _CoqProject/manifest unions,
  KernelDecode02 both-lemmas, the SpecSched/Sleep/Acquiresleep
  both-hunks resolutions, and the NOTES merges (keep ours; interleave
  their step-10/cwd-ref notes as their own sections).
- **T2** — `NFILE` → `FdSlots.v` (2e634258): keep OUR `IcacheRef.v`
  cut; `InodeRef.v` becomes a thin re-export or dies.
- **T3** — fold `irefNameG` into `icfg` + the arity drop (`itable_inv`,
  `iref_tok`, `itable_half`, `inode_ref`, `is_itable2`; `ic_names`
  loses `icn_ref`). Pure rename over every proven fs file; lands alone;
  makes origin's ~145 fast-forward files real.
- **T4** — the kfork/sys_fork cone onto OUR `cwd_ref`: `SpecKfork`
  gains `pv_cwd Vp <> 0` (honest — xv6's fork has no null test);
  ProofKforkB4's two sites use `cwd_ref_held`/`cwd_ref_of_held`; keep
  their `proc_priv_nocwd`/`proc_priv_split_cwd` (definition-agnostic)
  and `proc_dormant`'s `iref_slots (1 + IREFSPARE)` supply routing
  (better than ours); our `dev` arg at B4's one `is_itable2` site.
  SEMANTIC-MERGE FILES needing care: FileInv (icacheG must live in ONE
  file = IcacheRef), SystemAdequacy (xv6Σ arities), InodeLock (their
  import sweep × our inode_sized).
- **T5 — DEFERRED, its own design cycle**: the `natR` count-0-share
  algebra (b4902e13, ~500 lines already written) transplanted onto
  IcacheRef/IcacheInv; escrow + ProofIget retype mechanically; the ONE
  hard piece is ProofIput:924/:1387 — REF-1's `n = 1 → q = qt`
  direction dies under shares, so `SpecIput` needs a
  no-outstanding-share witness (origin's proportional accounting is
  the sketch). Third shape worth weighing then: cinv-as-parking +
  share-beside (`inode_pay := cinv … ∗ cinv_own q ∗ iref_shr_at v
  (q·Q_slot)`), which keeps ProofFileclose's arm and deletes their
  off_body step.
- **C8, recorded**: BOTH sides' SpecIlock/SpecFileread take a whole
  reference where a share belongs (three fds reading one file ⟹
  ip->ref == 3 today). Blocked on T5's vocabulary AND on the escrow's
  OUT arm (which holds a tok the two_lookup refutations need — a
  share-holding ilock has nothing to deposit). Genuine open design.
