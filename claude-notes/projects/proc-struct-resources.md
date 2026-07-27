# Project: `struct proc` resources

Design: [`design/proc-struct.md`](../design/proc-struct.md) — read it first; it
has the field-by-field sharing analysis, the two-boolean invariant shape, and
the evidence for every offset. This file is only the worklist.

## Done

- [x] `ProcGeom.v`: all 15 field addresses (`p_killed`/`p_xstate`/`p_parent`/
      `p_kstack`/`p_sz`/`p_pagetable`/`p_trapframe`/`p_ofile`/`p_cwd`/`p_name`),
      `NOFILE`/`PNAMELEN`/`ofile_stride`, the codes `UNUSED`/`USED`/`ZOMBIE`,
      and `inv_dormant` + its six `vm_compute` facts.
- [x] `ProcInv.v`: `pprivate` (+ `upd_ofile`/`upd_sz`/`upd_cwd`),
      `proc_fields`, `pname_cells`, `ofile_cells`, `ofile_slot`, `proc_ofiles`,
      `cwd_ref`, `proc_priv`, `proc_priv_pid` / `proc_priv_ofile` /
      `proc_priv_pid_agree`, `proc_dormant`, `proc_dormant_to_priv`,
      `is_kstack`.
- [x] `sys_getpid` proven whole-function over `proc_priv`
      (`SpecSysGetpid.v` / `ProofSysGetpid.v` / `LinkSysGetpid.v`).

## Next

- [x] **S1 — the `proc_lock_res` swap** (done). `SchedCtx.v` gained
      `proc_pub` (killed + xstate + the invariant's permanent half of the pid
      cell, existentially bundled so growing the invariant costs each caller
      one opaque conjunct instead of three spec parameters), `proc_slots` (the
      two flat guards), and `proc_slots_recast`. `proc_held` grew by
      `proc_pub`. Fallout was 4 files and ~15 lines: ProofYield, ProofSleep,
      ProofSched, ProofWakeup. `proc_lock_res_wakeup` now *is*
      `proc_slots_recast`, which deleted wakeup's `needs_ctx`-rewrite dance.
      `proc_dormant` ended up NOT indexed by `pid` either — the invariant's own
      half is always resident and two halves of a points-to agree for free — so
      `proc_slots` is a function of `st` alone and `proc_slots_recast` holds in
      both directions within a guard class.
- [x] **S2 — retiring the ad-hoc pid threading: NOT NEEDED, and would be
      wrong.** The claim in the first draft of the design note was mistaken.
      `SpecAcquiresleep` / `SpecHoldingsleep` take `p_pid pj ↦₄{dq} pidv` at a
      *universally quantified* `dq`, so they already compose with `proc_priv`
      unchanged at `dq := DfracOwn (1/4)` (checked: `proc_priv_pid`'s
      conclusion is literally their premise at that instantiation). Rewriting
      them to take `proc_priv` would add a `fileG`/`γf` dependency to the
      sleeplock layer purely to read a pid — a strictly worse interface. The
      bare fraction is both the weaker premise and the honest one.

- [x] **S3a — `argraw` PROVEN, `argint` linked** (done). The tree's first proof
      over a **computed indirect jump**: gcc compiles the switch to a `.rodata`
      jump table at `0x80007758`, whose six self-relative entries are read out
      of `kernel_data`, added back to the table base, and entered with
      `c.jr a5`. Both functions are axiom-clean; `proof_coverage` reports them
      `proven`. `ProofArgraw.v` costs **95 s / 2.5 GB**.

      **Getting there took two failed shapes, and the reason is the lesson.**

      1. *Six arms inlined in the capstone*: compiles, but **30 min / 74 GB**.
         `coqc -time` put 81 s in the single `destruct i` on the Iris goal, and
         Coq retains all six arms' proof terms until `Qed` (measured 8 GB at
         4 min, 16.6 GB at 7.5 min, climbing linearly).
      2. *One arm over a SYMBOLIC index*: no `destruct` on the WP goal at
         all — and still 14 GB at 7 min, climbing. With `k` symbolic every
         address becomes `mword_of_int (AR + ar_case_off k)` instead of a
         literal, so the WP leaves must unify open `Z` expressions against the
         `instr` facts through Sail's dependently-typed bitvectors. One
         blowup traded for another.
      3. **What works: six separately-`Qed`'d arms + a dispatch that splits
         BEFORE introducing anything.** Concrete indices keep every address a
         closed term (cheap unification); each `Qed` releases that arm's proof
         term (peak = one arm, not six); and the dispatch

             destruct k as [|[|[|[|[|[|k']]]]]];
               [ apply ar_arm0 | ... | apply ar_arm5 | ].

         is cheap *because the goal is still a closed implication* — no Iris
         context exists yet to duplicate per branch. The shared statement is a
         `Definition ar_arm_body`, which is the same `wp_*_sconf_body` idiom
         the spec files already use.

      **Rule of thumb this yields:** never `destruct` inside an Iris proof
      whose context carries the register-map chain. Push the split either
      *down* into small pure/`instr` helper lemmas (`ar_i_tf`, `ar_i_ld`,
      `ar_jump_tgt`, `ar_arg_addr`, `ar_ld_after_case`, `ar_i_cj`,
      `ar_cj_tgt`) or *up* above `iIntros`. A stray `destruct k` left inside
      `ar_join` was enough to OOM 125 GB on its own.

      Other facts worth keeping:

      * **`wp_cret_s_sconf` is not a "return" rule** — it is general over its
        register, so it IS the `jr rs` rule. The indirect jump needed no new
        leaf.
      * **The `i < NARG` precondition replaces `panic_wp`**: it discharges
        `bltu a5,s1,panic` via `wp_bltu_fall_s_sconf`.
      * The trapframe word is read through **`ProcInv.tf_word_to_mem`** —
        `tf_page` is physical, the `c.ld` is a VA-tier load, and a kalloc
        page's bytes are statically claimed `KP_rw`, so the crossing costs
        only the persistent `kmap_static_claims` plus `page_valid`.
      * **`kernel_data` byte facts do NOT close by `vm_compute; reflexivity`**
        — the two `bv 8` literals differ in their proof component. Use
        `vm_compute; f_equal; apply bv_eq; reflexivity`.
      * `ar_table_word`'s 24 map lookups are ~67 s of the file's 95 s (each
        `vm_compute` renormalises the 18k-entry `list_to_map`). Batching them
        into one `vm_compute` would be the next win if it matters.
      * Stack budget is cumulative: argraw `14 <= av`, argint `18 <= av`.
      * One instruction word (`addi a4,a4,52`) came from the STALE
        `kernel.asm`; `KernelInstrs` has `addi a4,a4,38`. Read words from
        `KernelInstrs.v`, never the `.asm`.

- [ ] **S3b — `sys_pause`.** Needs S3a first (it opens with `argint(0,&n)`),
      and is materially bigger than anything above: `acquire(&tickslock)`,
      a `while (ticks - ticks0 < n)` loop whose body is
      `killed(myproc())` + `sleep(&ticks,&tickslock)`, and `release`. So it
      needs (i) `killed()` specified and proven — which S1 just enabled, since
      `p_killed` now lives in `proc_pub` at the top level of `proc_lock_res`;
      (ii) an iLöb loop over the proven `SLEEP` interface, the same shape as
      `acquiresleep`'s sleep-retry loop (`ProofAcquiresleep.v`, 824 lines) —
      that file is the template; (iii) `TicksInv`'s tick cell, already used by
      `sys_uptime`. Budget it like acquiresleep, not like sys_getpid.

- [ ] **S3 — `p_ofile` loop lemmas.** `fdalloc` scans the array, so it needs a
      successor lemma and injectivity on `fd < NOFILE`, in the style of
      `ProcGeom.proc_addr_succ` / `p_context_proc_addr_inj`. (`ArrCursor.acur`
      does NOT apply — it takes a `Z` base; see the design note.)
- [ ] **S4 — the next syscalls.** `sys_dup` (exercises `proc_priv_ofile` +
      `filedup`), `sys_sbrk` (the unlocked `p->sz` write that is the whole
      reason the private block cannot be fractionally shared), `sys_close`
      (surrenders a `file_ref`).
- [ ] **S5 — `cwd_ref`.** Currently `emp`, a deliberate hole with `file_ref`'s
      shape. Needs an inode model (per-slot fractional auth over `itable`)
      that does not exist yet. Fill it and no caller restates.

## Gotchas hit

- **Do not `set` an index abbreviation you will later feed to `congruence`.**
  `set (s0_idx := mword_of_int 8)` makes the `upd_ne` side goal read
  `Regidx r <> Regidx s0_idx`, and `congruence` will not unfold the local
  definition — the componentwise `callee_saved` block fails with "congruence
  failed". Write the literal. (`ProofHoldingsleep.v` already does; `ProofCpuid.v`
  gets away with `set` only because it never needs `congruence` on them.)
- **`kernel.asm` in `xv6-riscv/kernel/` is stale** relative to
  `kernel-rocq/KernelInstrs.v` — symbols are shifted by 0xe. `KernelInstrs.v` +
  `KernelSyms.v` are the authority the proofs build against; read instruction
  words out of `KernelInstrs.v`, not the `.asm`.
- stdpp here is `length_insert` / `length_replicate`, not `insert_length` /
  `replicate_length`.
