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
- [x] `sys_close` proven whole-function (`WpSysCloseDecode.v` /
      `SpecSysClose.v` / `ProofSysClose.v`), over the specs of `argfd`,
      `myproc` and `fileclose`. It is the first proof in which a `file_ref`
      LEAVES a process: `proc_priv_ofile` borrows the descriptor, the store
      nulls it, `fileclose` consumes the reference and returns the `fd_slot`
      that the now-empty descriptor needs. NOT LINKED: `argfd` has a spec but
      no proof, and `fileclose`'s proof needs `pipeclose`/`begin_op`/`iput`
      first, so no `LinkSysClose.v` exists yet and `proof_coverage.py` still
      reads `sys_close` as unproven. See "What sys_close needed" below.

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
      `proven`. `ProofArgraw.v` costs **21 s / 1.0 GB** (was 95 s / 2.5 GB —
      see the `ar_table_word` bullet below).

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
      * **`ar_table_word` was 73.6 s of the file's 93.8 s, and it was the
        inline-`ltac:` trap, NOT the map** (fixed 2026-07-27; the earlier note
        here blamed "24 map lookups renormalising the 18k-entry
        `list_to_map`" and that was measurably wrong — 24 separate
        `vm_compute` lookups total **0.152 s**, because the VM compiles
        `kernel_data` to bytecode once per process). The real cost was six
        `iApply (kernel_data_window … ltac:(intros j Hj; destruct j …) …)`
        under a six-way `destruct i` ON the Iris goal: the proofmode
        re-elaborates each spliced `ltac:` without the `Qed` vm-seal, ~12 s a
        site — the same pathology as the `kernel_data_string` witnesses.
        Hoisting the byte premise into a pure `ar_tbl_bytes` lemma over a
        SYMBOLIC `i` and passing it by name kills the `destruct i` and leaves
        ONE `iApply`: region **73.6 s → 0.2 s**, file **93.8 s → 21.0 s**,
        RSS **2.49 GB → 0.99 GB**, `LinkArgraw`/`LinkArgint` still build and
        `Print Assumptions Argraw.wp_argraw_sconf` is still clean (Sail
        primitives + funext only). Full account in optimization.md.
      * **What is left in the 21 s is FLAT** — no sentence over 0.63 s; ~10 s
        of tactic time and ~10 s of async `Qed` spread over the six arms and
        `ar_tail`. The six arms are byte-identical modulo the index literal,
        so collapsing them into one symbolic-`k` arm is the only remaining
        structural win (~5/6 of the arm cost). Shape 2 above rejected exactly
        that at 14 GB — but it was measured WITH the inline-`ltac:` premises
        in place and BEFORE the regfile-as-function migration, so that verdict
        is no longer evidence. Re-measure before believing it; the symbolic-`k`
        helpers (`ar_i_tf`/`ar_i_ld`/`ar_jump_tgt`/`ar_arg_addr`/`ar_i_cj`/
        `ar_cj_tgt`/`ar_ld_after_case`) are already in place.
      * Stack budget is cumulative: argraw `14 <= av`, argint `18 <= av`.
      * One instruction word (`addi a4,a4,52`) came from the STALE
        `kernel.asm`; `KernelInstrs` has `addi a4,a4,38`. Read words from
        `KernelInstrs.v`, never the `.asm`.

- [x] **`killed` PROVEN** — the first consumer of the invariant's
      always-resident row. `p_killed` lives in `SchedCtx.proc_pub`, at the top
      level of `proc_lock_res`, so the read is: open the lock, destruct ONE
      existential, `c.lw a5,40(s1)`, reassemble. It never learns the process's
      state and never touches either `proc_slots` guard — which is exactly what
      S1's flat row was for. Nineteen instructions, a 32-byte ra/s0/s1/s2 frame
      with all four slots used (no gap); `p` parks in s1 across acquire and the
      value in s2 across release. `panic_wp` is threaded because the reworked
      `acquire` takes it.
- [ ] **S3b — `sys_pause`.** All callees are now proven: `argint` ✓ `acquire` ✓
      `myproc` ✓ `sleep` ✓ `release` ✓ `killed` ✓. What remains is sys_pause's
      own shape — `acquire(&tickslock)`, then a `while (ticks - ticks0 < n)`
      loop whose body is `killed(myproc())` + `sleep(&ticks,&tickslock)`, then
      `release`. That needs an iLöb loop over the proven `SLEEP` interface; the
      template is `ProofAcquiresleep.v`'s sleep-retry loop (824 lines), and
      `TicksInv`'s tick cell is already used by `sys_uptime`. Budget it like
      acquiresleep, not like sys_getpid.
- [ ] **S3 — `p_ofile` loop lemmas.** `fdalloc` scans the array, so it needs a
      successor lemma and injectivity on `fd < NOFILE`, in the style of
      `ProcGeom.proc_addr_succ` / `p_context_proc_addr_inj`. (`ArrCursor.acur`
      does NOT apply — it takes a `Z` base; see the design note.)
- [ ] **S4 — the next syscalls.** `sys_dup` (exercises `proc_priv_ofile` +
      `filedup`) and `sys_sbrk` (the unlocked `p->sz` write that is the whole
      reason the private block cannot be fractionally shared). `sys_close` is
      done; `sys_read`/`sys_write`/`sys_fstat` are the other `argfd` callers
      and are cheap once `argfd` itself is proven — but note they pass a NULL
      out-parameter (`sys_read` passes `pf = 0`), which `SpecArgfd`'s
      both-non-null shape does not cover, so they want a second interface or
      a `pf`-optional generalization of this one.

- [x] **S4a — `argfd` proven** (`WpArgfdDecode.v` / `ProofArgfd.v`), over
      `ARGINT` + `MYPROC`, 33 instructions. Like sys_close it is NOT linked:
      `ARGINT` has no implementation while `argraw` is parked (S3a), so there
      is no `LinkArgint.v` and hence no `LinkArgfd.v`. Three things worth
      reusing:
      * **THREE arms join at the epilogue** (+0x46) — the success fall-through
        and two `c.li a0,-1; c.j` tails — so `af_tail` is applied three times.
        Factor the epilogue the moment a function has more than one `return`.
      * **The fused range test.** gcc compiles `fd < 0 || fd >= NOFILE` into
        the single UNSIGNED `bltu a5,a4` against 15: a negative fd
        sign-extends to ~2^64 and fails the same compare. `af_bltu_in` /
        `af_bltu_out` are that argument over `bv_signed` of the loaded `int`;
        the C-level disjunction never has to be split.
      * **The `int` out-parameter round trip.** The local is reloaded with an
        `lw` (sign-extending) and stored through the caller's pointer with an
        `sw` (truncating); `RiscvExtras.trunc32_sext64` says that composition
        is the identity, so the caller's cell holds exactly argint's
        `trunc32 v`.
      Both `c.beqz` null tests are DEAD under this contract — the spec's two
      disequality premises discharge their fall-through — which is what makes
      the both-non-null shape cheap. `sys_read`'s `pf = 0` call site is NOT
      covered and wants a second interface (see S4).

      Note what the specs do NOT thread: since the trapframe page moved
      inside `proc_priv` (`tf_page (ud_tfp (pv_upt V)) (pv_tf V)`), neither
      `SpecArgfd` nor `SpecSysClose` takes a separate argument resource —
      only the pure fact `pv_tf V !! tf_arg_idx i = Some v` saying which word
      the argument is. `ProcInv.proc_priv_tf` hands the pointer fraction and
      the page out TOGETHER, which is necessary: `proc_priv_trapframe`'s wand
      swallows the `proc_priv` the page is still inside, so the pair has to be
      one accessor.
- [ ] **S5 — `cwd_ref`.** Currently `emp`, a deliberate hole with `file_ref`'s
      shape. Needs an inode model (per-slot fractional auth over `itable`)
      that does not exist yet. Fill it and no caller restates.

## The unlinked chain: what is left after `argraw`

**`argraw` is no longer the blocker — `fileclose` is the only one left.**
S3a landed `LinkArgraw.v` and `LinkArgint.v`, both of which build, and
`Print Assumptions Argraw.wp_argraw_sconf` shows only Sail primitives +
functional extensionality. Current state:

```
sys_close  --proof over-->  ARGFD, MYPROC, FILECLOSE
argfd      --proof over-->  ARGINT, MYPROC     (no LinkArgfd yet: needs FILECLOSE's sibling)
argint     --LINKED-->      real (LinkArgint.v)
argraw     --LINKED-->      real (LinkArgraw.v)
fileclose  --no proof-->    needs pipeclose / begin_op / iput / end_op
myproc     --LINKED-->      real
```

So the sys_close/argfd cone is ONE `fileclose` proof away from being linked
end to end; nothing else is missing.

**Reading the tree: `.vo` staleness will lie to you about this.** A checkout
whose `.vo`s predate the "move `tf_page` to the VA tier" merge makes
`ProofArgraw.v` fail at arm 0's `iExact "Hw"` with `a_tf_word … ↦ₚ₈ v` — the
OLD physical-tier `tf_page_word`, not a real breakage. Check `.v -nt .vo`
across `iris/` and `make` the dependency cone before concluding a proof is
broken (durable-notes.md's stale-`.vo` trap; this one cost a full
misdiagnosis).

## What `sys_close` needed (reusable)

Four pieces of infrastructure landed with it; none is sys_close-specific.

- **A 4-byte C local at the UPPER HALF of a frame slot.** `int fd` lives at
  `s0-20`, so `&fd` is a `↦₄` view of a cell the stack hands out as `↦₈`.
  `InstrBytes.word_pointsto_split4` / `word_pointsto_join4` (with
  `word_lo`/`word_hi`/`word_of_words`, all spelled through
  `RiscvModelBytes.assemble_bytes`) are that split, at any dfrac. Every
  syscall that takes the address of an `int` local will want them.
- **"The out-parameter is not null" is DISCHARGED, not assumed.** argfd
  null-checks `pfd`/`pf`, so its spec takes two disequalities — and a caller
  passing a stack local can prove them: `StackOwn.stack_own_sp_bounds` reads
  `8 <= uint sp < 2^38 + 8` straight out of the ambient capability's own
  stack carve (every owned address is canonical, so an sp below 8 would put
  the next slot at ~2^64), and `stack_off_nonzero` lifts that to any
  non-negative offset from it. This is the durable answer to the
  "caller obligation the caller cannot discharge" smell.
- **`p->ofile[fd]` at a SYMBOLIC fd.** `slli a5,3 / addi a5,208 / add a0,a0,a5`
  is `ProcGeom.p_ofile p fd` by definition once the shift is done over a
  symbolic `z` (`ProofSysClose.sc_slli3`, the `slli13` shape from
  ProofProcMapstacks). Do NOT case on the sixteen descriptors — that is the
  argraw mistake (S3a) in miniature.
- **A branch that JOINS.** The `blt` failure arm lands on the same `c.mv
  a0,a5` the success arm falls through to, so the epilogue is one lemma
  (`ProofSysClose.sc_tail`) parameterized by the value the arm left in a5,
  not two copies of five instructions plus a 14-conjunct `callee_saved`
  block. Look for this shape in any `if (...) return -1;` function.

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
