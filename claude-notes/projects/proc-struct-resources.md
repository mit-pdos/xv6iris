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

- [ ] **S1 — the `proc_lock_res` swap** (`SchedCtx.v`). Add `proc_slots pa st
      pid` (the two flat guards) and `proc_slots_recast`; grow the
      always-resident row with `killed`/`xstate`/the `pid` half; grow
      `proc_held` to match. Re-prove the downstream users: `ProofYield`,
      `ProofSched`, `ProofSleep`, `ProofWakeup(Parts)`. `proc_lock_res_wakeup`
      becomes a corollary of `proc_slots_recast`. Nothing in `ProcInv.v`
      changes.
- [ ] **S2 — retire the ad-hoc pid threading.** `SpecAcquiresleep.v` /
      `SpecHoldingsleep.v` / `SpecSleep.v` currently thread
      `p_pid pj ↦₄{dq} pidv` through pre- and postcondition with `dq` as a spec
      parameter. Replace with `proc_priv` + `proc_priv_pid`; `dq` disappears.
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
