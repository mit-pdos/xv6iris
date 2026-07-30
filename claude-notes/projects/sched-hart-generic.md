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

## The fix: quantify the resuming hart INSIDE the stored payload

The stored continuation becomes, schematically,

```
∀ h : CPU, ⟨resumption resources at h⟩ -∗ WP (LoopE h) {{ … }}
```

with the resumption resources exactly what the crossing hands over today,
re-indexed by `h` instead of the ambient instance: the register map with
`tp = cid_word_of h`, hart-h's scheduler-context cell
(`a_cpu_ctx (cid_word_of h)`), hart-h's `cpu_own` pieces, the c->proc
cursor. This is statable because EVERY lemma in the tree is already
∀-quantified over `CpuId` at the top (Section Context): `WP (LoopE h)` for
a variable `h` is the lemma instantiated at `CID := h`. The work is moving
the hart from the section context into the payload's binder at the two
seams (park and resume) and making the post-swtch halves of the parking
proofs draw their tp/mycpu facts FROM THE PAYLOAD rather than from the
ambient instance — the code cooperates (xv6 re-derives `mycpu()` from `tp`
after every resumption; the proofs' facts all flow through the register
map).

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
