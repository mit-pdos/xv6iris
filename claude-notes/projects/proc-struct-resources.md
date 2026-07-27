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

- [ ] **S3a — `argraw`, and linking `argint`. PARKED, with a working proof
      that is too expensive to commit.** A complete six-arm proof was written
      and it *does* compile — but at ~30 min and a **74 GB** peak, so it was not
      committed. Kept at `scratchpad/ProofArgraw.6arm.v` in the session that
      wrote it; everything below is what a rewrite needs.

      **Why it is expensive, measured.** With one arm the file is 98 s / 2.3 GB,
      and `coqc -time` attributes **81 s to the single `destruct i`** on the
      capstone's Iris goal. Two things compound:
      * `destruct` on the big goal re-typechecks the dependently-typed Sail
        bitvector context once per branch (`subrange_vec_dec _ (log2_xlen-1) 0`
        has a *Z-computation* in its type). `clearbody` on the register-map
        chain, `clear`ing the unused i-facts, and restricting `try lia` to the
        one impossible branch each bought ~0 — it is the `destruct` itself.
      * Coq retains **all six arms' proof terms until `Qed`** — measured 8 GB at
        4 min, 16.6 GB at 7.5 min, climbing linearly to the 74 GB peak.

      **The fix (designed, not yet written): prove the arm ONCE over a symbolic
      index.** Add `ar_case_off`/`ar_ld_off : nat -> Z` for the per-case PCs,
      then push the only six-way `destruct`s down into *small* helper lemmas —
      `ar_i_tf` / `ar_i_ld` (dispatch the two `instr` facts to `ari_28`/`ari_36`/…),
      `ar_jump_tgt` (the table entry really lands on the case body),
      `ar_arg_addr` (the `112+8k` displacement; note the C_LD imm field is
      exactly `14+k`), and `ar_join` (case 0 falls through, 1..5 take a `c.j`;
      a plain continuation may be fed to `wp_cj_s_sconf`'s `▷` slot since
      `P ⊢ ▷ P`). The capstone then needs **no `destruct` at all** — one
      `ar_arm` application with `i` symbolic.

      **The rest, still valid.** Jump table @ `0x80007758` in `kernel_data`:

        | n | entry | target | = argraw+ |
        |---|---|---|---|
        | 0 | `0xffffafea` | `0x80002742` | `+0x28` |
        | 1 | `0xffffaff8` | `0x80002750` | `+0x36` |
        | 2 | `0xffffaffe` | `0x80002756` | `+0x3c` |
        | 3 | `0xffffb004` | `0x8000275c` | `+0x42` |
        | 4 | `0xffffb00a` | `0x80002762` | `+0x48` |
        | 5 | `0xffffb010` | `0x80002768` | `+0x4e` |

      * **`wp_cret_s_sconf` is not a "return" rule** — it is already general
        over its register, so it IS the `jr rs` rule. The indirect jump needs
        no new leaf.
      * **The `i < NARG` precondition replaces `panic_wp`**: it discharges
        `bltu a5,s1,panic` via `wp_bltu_fall_s_sconf`, so argraw carries no
        panic hypothesis.
      * **`kernel_data` byte facts do NOT close by `vm_compute; reflexivity`** —
        the two `bv 8` literals differ in their proof component. Use
        `vm_compute; f_equal; apply bv_eq; reflexivity`.
      * `unfold NARG in Hi` before any `destruct i`, or `lia` cannot kill the
        out-of-range branch.
      * Stack budget is cumulative: argraw needs `14 <= av` (4 frame slots +
        myproc's 10), argint `18 <= av`. **Both spec bounds are now corrected
        in-tree**; the originally committed 12/16 were unprovable.
      * One instruction word (`addi a4,a4,52`) was taken from the STALE
        `kernel.asm`; `KernelInstrs` has `addi a4,a4,38`. Same table base, but
        the decode failed. Read words from `KernelInstrs.v`, never the `.asm`.

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
