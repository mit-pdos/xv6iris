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

## What actually landed (2026-08-10, branch `reconcile-fork`)

One merge commit, `git merge origin/main` with the conflicts resolved
inside it, so origin's 28-commit kfork line is a real ancestor of main.

- **T1** — done as planned. The four interrupt/CSR/`wp_next_at`/`ops_ok`
  commits, the dead-import sweep, the `_CoqProject`/manifest unions and
  the `KernelDecode02`/`SpecSched`/`SpecSleep`/`SpecAcquiresleep`
  both-hunks resolutions all fast-forwarded or merged clean. NOTES kept
  ours as base with their sections interleaved; `design/fs-icache.md`'s
  conflicting section keeps our §13.8–13.13 content and folds their
  canonical-gname paragraph in (it is now true of the tree).
- **T2** — done. `NFILE` lives in `FdSlots.v`; `IrefSlots` requires
  `FdSlots`; `IREFSLOTS = NPROC*(1 + IREFSPARE) + NFILE`. `IcacheRef.v`
  keeps our cut and is the ONLY home of `icacheG`/`icacheΣ`/`icfg`.
  **`InodeRef.v` survives as a thin re-export** of `IrefSlots` +
  `IcacheRef` (plus `ientry_nonzero`), which is the minimum-churn choice:
  ~20 of their files `Require Import InodeRef` only to get the reference
  vocabulary and the slot supply in scope at once. `iref_at` /
  `iref_shr_at` are NOT re-provided — `iref_at` had exactly two consumers
  (`ProcInv.cwd_ref`, `ProofKforkB4`) and both now use `inode_held`.
- **T3** — done, and folded the way the ruling said: `IcacheRef.icfg`
  carries the canonical authority gname (`icfg_iref` ≡ their
  `iref_name`), and `itable_half` / `iref_tok` / `inode_ref` /
  `itable_inv` / `itable_body` / `itable_res` / `is_itable` all lost
  their `γ` argument, as did every lemma over them. `ic_names` lost
  `icn_ref`, so `ic_names_alloc` no longer takes or returns a gname, and
  the pure bridging premises (`icn_ref cn = icfg_iref` in `SpecFileclose`
  and `ProofKexit`) are gone.
  - **The one thing the ruling did not anticipate**: `icfg` is AMBIENT
    (a superclass field of `FileInv.fileG`, fixed before the boot fupd),
    whereas their `irefNameG` was minted inside `boot_shared_alloc` and
    left existentially. Under the fold, a boot-time mint would produce a
    SECOND `icfg`, unrelated to the one the file table's payload is
    stated over. So `iref_name_alloc` and its `BootShared` call site are
    gone; `IcacheRef.icfg_alloc` is the allocator (kept, so the premise
    is demonstrably satisfiable), and `IcacheBoot.icache_boot` now TAKES
    `own icfg_iref (● ∅)` instead of allocating it. Tying the ambient
    `icfg` to a boot-minted authority is the remaining half of the boot
    wiring, and it is the same not-done-ness their side had (their
    `iref_name_alloc` discarded what it minted).
  - Their `!irefNameG Σ` Context binders (~25 files) were DELETED rather
    than translated: `fileG` already carries `icacheG` + `icfg`, and
    binding both is the two-instance-paths trap. Where `fileG` is absent
    (the i-cone spec/proof files) the binder is `ICFG : icfg` beside
    `!icacheG Σ`.
- **T4** — done. The kfork/sys_fork cone ported onto our `cwd_ref`:
  `SpecKfork` and `SpecSysFork` gained `pv_cwd Vp <> 0` (threaded through
  `ProofKforkMain.kfork_arm3` to `ProofKforkB4.kfk_b4`); B4's cwd destruct
  goes through `cwd_ref_held` and `inode_held`, so the DEVICE is not
  existential (it is `icfg_dev`) and the inum bound comes out with it;
  `kfk_child_cwd` rebuilds the child's arm with `cwd_ref_of_held`. B4's
  `is_itable2` call sites (and the cone's, seven files) gained our `dev`
  argument as `icfg_dev` — no new spec parameter was needed, because
  §13.11's single-device pin makes the itable's device and the
  reference's the same thing. Kept their `proc_priv_nocwd` /
  `proc_priv_split_cwd` / accessors, their `proc_dormant`
  `iref_slots (1 + IREFSPARE)` routing and their `SpecAllocproc`; our
  `proc_priv_intro`'s `pv_cwd V = 0` premise was dropped in favour of
  their `cwd_ref (pv_cwd V)` argument (strictly more general under the
  two-armed definition, and `ProofAllocproc` now uses
  `proc_priv_nocwd_intro` anyway).
- **T5** — still deferred. `positiveR` stayed. The one place their `natR`
  retype leaked in through a theirs-only file was
  `IrefSlots.iref_slots_no_overflow`, restated at `nat`; it is back at
  `positive` with a pointer to T5 at the site. Verified by grep that no
  file in the kfork/sys_fork cone consumes `iref_shr_at` / `inode_shr` /
  count-0 shares.
