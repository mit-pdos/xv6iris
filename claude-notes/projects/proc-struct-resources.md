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

- [ ] **S3a — `argraw`, and linking `argint`.** `argint` is proven over the
      `ARGRAW` module type but `LinkArgint.v` is empty until argraw is proven.
      Everything needed has been checked to exist; this is writing, not
      research. The derived facts:

      * argraw @ `0x8000271a`, 30 instructions. 32-byte ra/s0/s1 frame,
        byte-identical to sys_uptime's / argint's, so reuse those decodes.
      * gcc compiles the switch to a **`.rodata` jump table** at `0x80007758`
        (inside `kernel_data`, verified present). The six self-relative
        4-byte entries and their targets, extracted from `KernelData.v`:

        | n | entry | target | = argraw+ |
        |---|---|---|---|
        | 0 | `0xffffafea` | `0x80002742` | `+0x28` |
        | 1 | `0xffffaff8` | `0x80002750` | `+0x36` |
        | 2 | `0xffffaffe` | `0x80002756` | `+0x3c` |
        | 3 | `0xffffb004` | `0x8000275c` | `+0x42` |
        | 4 | `0xffffb00a` | `0x80002762` | `+0x48` |
        | 5 | `0xffffb010` | `0x80002768` | `+0x4e` |

      * Fresh decodes (all validated with a decoder cross-checked against
        `sldec_lw_locked` / `sgdec_lw_a0_procpid` / `aidec_sw_a0_ip` /
        `aidec_mv_s1_a1` / `cdec_8082`):
        `+0x0a 0x84aa` C_MV s1,a0 · `+0x0c 0x9deff0ef` jal myproc (imm21
        2093534) · `+0x10 0x4795` C_LI 5,a5 · `+0x12 0x0497e163` BLTU a5,s1
        → `+0x54` · `+0x16 0x048a` C_SLLI 2,s1 · `+0x18 0x00005717` auipc
        a4,0x5 · `+0x1c 0x03470713` addi a4,a4,52 · `+0x20 0x94ba` C_ADD
        s1,a4 · `+0x22 0x409c` C_LW 0(s1)→a5 (shared `sldec_lw_locked`) ·
        `+0x24 0x97ba` C_ADD a5,a4 · `+0x26 0x8782` C_JR a5 ·
        `0x6d3c` C_LD 88(a0)→a5 (imm field 11) · the six
        `C_LD <112+8i>(a5)→a0` words `0x7ba8/0x7fa8/0x63c8/0x67c8/0x6bc8/0x6fc8`
        (imm fields 14..19) · the five `c.j` words
        `0xbfcd/0xb7f5/0xb7dd/0xb7c5/0xbfe9`, ALL targeting `+0x2c`.
      * **No new WP rule is needed.** `wp_cret_s_sconf` is already general
        over the register, so it IS the indirect-jump rule for `c.jr a5`.
        `wp_bltu_fall_s_sconf` (WpSconfBtype.v) is the not-taken branch —
        and the spec's `i < NARG` precondition is what discharges it, so
        argraw needs NO `panic_wp` hypothesis. `kernel_data_window`'s output
        is literally `word4_pointsto`'s definition at `DfracDiscarded`, so
        the table read needs only an alignment fact. A `kernel_data` lookup
        proves by `vm_compute` in well under a second (measured) despite the
        18k-entry map, so the table read is cheap.
      * Shape: case-split on `i` into six concrete branches right after the
        `c.add s1,s1,a4`; prove the shared epilogue at `+0x2c` ONCE as a
        local lemma over an arbitrary arrival map (the `wp_ci_tail` pattern
        from `ProofClockintr`, see design/kernel-proofs.md), since all six
        arms re-join there.

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
