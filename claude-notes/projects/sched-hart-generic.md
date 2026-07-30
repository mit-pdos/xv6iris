# Project: hart-generic p_sched (G5, part 2)

GOAL: make `SchedCtx.procs_inv` ONE hart-independent proposition, so the
`started` payload can carry it and every secondary hart's `scheduler()` can
consume it. Companion to [`kpt-share.md`](kpt-share.md) (G5 part 1); the two
are independent sweeps over disjoint files. Approved 2026-07-30.

## The problem

The proc-lock resource of a parked proc stores the RESUMPTION CONTRACT
(`p_sched`, the 4-place chain payload from `completed/scheduler.md`): "if a
scheduler swtches into my saved context, execution continues safely and
eventually swtches back into THAT scheduler's context cell, releasing my
lock on the way". Today that payload is stated at the AMBIENT hart —
`p_sched` carries `⌜tpv = cid_word⌝` and `⌜c = a_cpu_ctx cid_word⌝`, the
section-level `CpuId` instance. So `procs_inv` elaborated at hart 0 and at
hart 1 are DIFFERENT propositions over the same 64 locks, and neither can
be the payload the other needs. This is an artifact of the single-hart
proof era, not of the code: real xv6 lets any hart's scheduler pick up any
RUNNABLE proc, and `swtch` does not even save `tp` — the resumed thread
inherits the resuming hart's.

## The fix, AS REFINED BY THE SEAM SURVEY (the naive ∀h does NOT close)

First checkpoint (`c890e7f`): `p_sched (h : CPU) …` / `proc_held (i :
CPU) …` re-indexed by the hart they are ABOUT (pure re-spelling,
`sched_vc` applies at `cpu_id`, zero proof rework).

The approved final shape is an ADMISSIBILITY-INDEXED fixpoint, forced by
four seams the naive ∀h missed:

- **S1 — the SIE ghost γ is per-hart** (one γ's fractions are fully
  consumed by one hart's sconf/intr_inv/sie_arm/intr_count), so the
  resume wand quantifies `∀ h γ`, and `procs_inv Φ γs` LOSES γ — it must,
  to ride the single `started_inv` payload. The crossing DELIVERS
  `intr_handler_avail γ_new` (resumer and resumed are on the same hart at
  the swtch instant, so the resumer's γ is the one the resumed gets).
- **S2 — `trap_csrs` are per-hart cells held ACROSS parks** (yield/sleep
  take acquire's `trap_csrs_pay` and spend it at their release, entirely
  inside the function), so hart-h's trap CSRs ride the payload — and the
  balanced exchange needs **`eb = true` as a parking precondition**
  (honest: user processes' kernel threads park with intena saved true;
  the scheduler holds the CSRs in both eb arms).
- **S3 — cpu contexts are PINNED, proc contexts migrate.** The scheduler
  re-derives its per-cpu addresses from saved callee-saved registers (s4
  = `a_cpu_proc` of ITS hart), so a uniform ∀h resume wand is unprovable
  for it — and unnecessary (`cpus[h].context` is only ever resumed from
  hart h's own tp). Hence `A : option (CPU * gname)` on
  `valid_context`: `None` = resumable anywhere (proc contexts, what
  `procs_inv` stores), `Some (h,γ)` = pinned (each hart's `sched_vc`).
- **S4 — `callee_saved` includes tp**, which genuinely changes across a
  migrating park: sched/yield/sleep and every contract above a potential
  park weaken to a no-tp `callee_saved` form + `⌜mf !!! x4 =
  cid_word_of h⌝` (wrapper recipe keeps the strong form for
  non-sleepers).
- **S5 — the sleeper cone is bigger than first listed**: uartwrite,
  the virtio_disk_rw tower (~8.5k lines) and bwrite also park.
  allocproc is a no-op today (raw ctx_cells only; the proc_ctx deposit
  is future work). wakeup confirmed unaffected. ~24k proof lines in the
  cone.

The validated mechanics: `iApply (lem (CID := h) …)` works (bare iApply
resolves the section instance); extract each parking proof's post-resume
half as its OWN section lemma applied once at `(CID := h)` — one seam per
proof instead of thousands of leaf edits. `stack_own`/`ctx_cells` are
`Arch.pa` memory, already hart-independent — the parked stack re-attaches
at h for free.

## Blast radius (the sweep's checklist)

- `SchedCtx.v`: `sched_vc` / `proc_ctx` / `p_sched` / `proc_lock_res` /
  `procs_inv` — the ∀h binder and the re-indexed conjuncts. `procs_inv`
  becomes hart-independent (and stays persistent).
- The crossing's two sides: `sched`/`yield` (producer: the deposited
  continuation must be proven ∀h) and `scheduler()` (consumer: instantiate
  at its own hart; its own re-deposit of the scheduler context is the
  mirror obligation).
- The `SLEEP` / `SLEEP_GEN` interface: its continuation premise becomes
  ∀h, so every sleeper's post-sleep proof re-threads its tp-dependent
  steps (acquire/release → push_off/pop_off → mycpu) through the
  quantified hart: `acquiresleep`, `piperead`, `pipewrite`, `sys_pause`.
- `allocproc`: deposits the FIRST context (the forkret continuation) —
  same ∀h form.
- `wakeup` does not cross (it only flips state under the lock) — expect
  little or no change.
- `procs_inv_alloc` (SpecProcinit) and `SpecMain`'s wand/`SpecScheduler`'s
  precondition follow the new statement.

## Interaction with main-boot

After this sweep + kpt-share, the `started` payload P grows `kpt_inv` and
the (now hart-generic) `procs_inv`, and `wp_main_secondary_sconf` becomes
statable: spin loop (iLöb over lw/sext.w/beqz), `▷ P` stripped at the
fence by `wp_fence_gen_later_s_sconf`, printk("hart %d starting") from
P's `printk_env`, kvminithart (kpt-share's hart-generic contract),
trapinithart, plicinithart, `jal scheduler` at the join.
