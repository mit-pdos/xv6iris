# Project: prove `kerneltrap()`

Replacing the last big assumed kernel contract on the interrupt path.
`kerneltrap` is one of the four sanctioned assumed callees
(`design/execution-model.md`); today `SpecKerneltrap.v` states a round-trip
"it returns, preserving everything" contract and `LinkKerneltrap.v` supplies it
with an `Axiom`.  This file is the design and the worklist for discharging it.

Read [`design/interrupts.md`](../design/interrupts.md) first — the `sconf` /
`sie_cap_gpr` / `intr_handler_spec` vocabulary below is all defined there.

## The function

```c
void kerneltrap() {
  int which_dev = 0;
  uint64 sepc = r_sepc(); uint64 sstatus = r_sstatus(); uint64 scause = r_scause();
  if ((sstatus & SSTATUS_SPP) == 0) panic("kerneltrap: not from supervisor mode");
  if (intr_get() != 0)              panic("kerneltrap: interrupts enabled");
  if ((which_dev = devintr()) == 0) {
    printk("scause=0x%lx sepc=0x%lx stval=0x%lx\n", scause, r_sepc(), r_stval());
    panic("kerneltrap");
  }
  if (which_dev == 2 && myproc() != 0) yield();
  w_sepc(sepc); w_sstatus(sstatus);
}
```

`@ KernelSyms.kerneltrap = 0x80002696`, 40 instructions, 146 bytes, a 6-slot
(48-byte) frame saving ra/s0/s1/s2/s3.  Callees: `devintr` (proven), `myproc`
(proven), `yield` (proven), `panic` ×3 (proven) — and `printk`-general, which
is assumed but sits on a DEAD arm (next section).

### ALL THREE PANIC ARMS ARE REFUTED FROM THE PRECONDITION

kerneltrap is called from ONE place — kernelvec, i.e. a taken S-mode
interrupt — and the contract is stated at exactly that call site rather than
for an arbitrary caller.  That is what makes the three panic arms DEAD, and
it is a better contract than the alternative in every way, so it is the
design:

| arm | refuted by |
| --- | --- |
| `panic("kerneltrap: not from supervisor mode")` | the caller's half of the SPP ghost mirror, at `'b"1"` — the trap came from S-mode, which `trap_ms` in the handler contract already says. Carrying that fact to the check is what `spp_hlf` exists for (below) |
| `panic("kerneltrap: interrupts enabled")` | the live SIE bit is the ambient arm index, and the handler runs at `b = false` (the trap cleared SIE). `IntrDefs.sie_arm_half_agree` reads it off the index at either arm, no case split |
| `printk(...)` + `panic("kerneltrap")` | `scause` is threaded at a PINNED value with `devintr_ret sc ≠ 0`, i.e. the cause is one of the two `devintr` recognises |

**The payoff is the axiom ledger.**  Closing an arm with `panic_wp_any`
instead would have been easy, but the `printk` arm would then pull
printk-general into the cone — so proving kerneltrap would trade one
sanctioned axiom for another.  With the premises above the cone is
`devintr` + `myproc` + `yield` + `panic`, all proven: **`kerneltrap_returns`
goes away and nothing takes its place.**

Two consequences for the shape:

- **The SPP/SPIE facts reach the check through `sret_bits`, the ghost
  mirror** — NOT through any flavour of the bundle.  The precondition threads
  the PLAIN `sie_cap_gpr` plus `sret_bits '1' '1'`; the postcondition is then
  ABSOLUTE (`SPP = 1`, `SPIE = 1`, `SIE = 0` outright) rather than relative to
  an entry mstatus, because the final `csrw sstatus` writes back the saved
  word.  No entry mstatus is named anywhere in the contract.  The
  mstatus-exposing flavour appears only on the OUTPUT side, and only because
  `sret` is what reads those bits.  `wp_csrr_sstatus_s_sconf` now hands back
  `sconf_at ms` (it already named the mstatus it read, so exposing it costs
  nothing), and `sconf_at_sret` turns the travelling half into the fact.
- **The engine now owes the scause fact.**  `wp_exec_step_intr`'s σ-callback
  hands out only `exec (dispatchInterrupt Supervisor) σ = Some (None, σ)`; the
  trap-TAKING arm computes `s_dispatch mip meip seip mie mdv ms = Some (i, Supervisor)`
  and throws `i` away.  It has to expose it, and relate it to the word the
  trap writes into `scause`, so kernelvec can discharge `devintr_ret sc ≠ 0`.

### DONE: the SPP arm, and the ghost mirror that refutes it

Of the three refutations the table promises, two were cheap and one was not.

- **interrupts-enabled: FREE.**  `wp_csrr_sstatus_s_sconf` already hands the
  caller `⌜_get_Mstatus_SIE ms0 = sie_bit b⌝` for the very `ms0` whose S-view
  it read, and a handler runs at `b = false`.
- **scause: cheap.**  Pin `mie` in `sconf` (next section) and expose the taken
  cause out of the engine.
- **SPP: needed a new mechanism, now built.**  `_get_Mstatus_SPP ms_e = 'b"1"`
  is a fact about the mstatus at kerneltrap's *entry*, but the check runs FOUR
  instructions later, and **every one of those round-trips `sconf` through
  `wp_instr_s_sconf`, whose `∃ ms` destroys the identity of the mstatus**.
  `sie_cap_gpr_at` does not rescue it: it is an accessor, so closing it to
  feed the funnel spends the closer and an arbitrary `ms` comes back.  The
  information is destroyed by the existential, not mislaid — which is why an
  `_at` variant of the sstatus READ leaf would not have helped either.

**The fix, landed:** `spp_hlf`, a ghost mirror of mstatus.SPP threaded
independently of the register package, exactly as SIE already is.  See
[`design/interrupts.md`](../design/interrupts.md) for the full write-up.  The
short version: two halves, one tied inside `sconf` to `_get_Mstatus_SPP ms`
and one travelling in `trap_csrs` — existential in `sie_arm true`, pinned in
the hands of interrupts-off code.  Four things fell out of the discipline
rather than being designed in: `intr_config` must NOT carry a tie (a trap and
its sret move the bit, so the funnel re-ties both halves after the engine);
push_off/pop_off need no ghost movement at all (the SIE mask misses bit 8);
`csrw sstatus` is the one leaf that moves SPP and is vacuous at `b = true`;
and the tie is first established at the M→S bridge, the only moment outside
an mstatus-writing leaf when both halves are in hand.

Fallout was five thin layers (3 → 7 → 2 → 1 → 1 files), almost all
ride-through sites in proofs that never touch mstatus.

### RESOLVED: what makes the scause premise dischargeable — pin `mie`, not `mip`

`devintr` recognises S-external (9) and S-timer (5) and nothing else, so the
premise `devintr_ret sc ≠ 0` is only as good as the argument that no OTHER
cause can be delivered to S-mode.  The first guess is that this needs an
`mip.SSIP = 0` invariant (S-software, cause 1, is not recognised).  **It does
not.**  The dispatch set is

```coq
s_pending mip meip seip mie mdv = and_vec (s_mip_bits mip meip seip) (and_vec mie mdv)
```

— it is masked by `mie`, and in THIS kernel `mie` never has any bit but 5 and
9 set:

- `w_sie` is called exactly ONCE in the whole kernel, `start.c:33`:
  `w_sie(r_sie() | SIE_SEIE | SIE_STIE)` — bits 9 and 5 only. **This revision
  does not set `SIE_SSIE`** (`riscv.h` does not even define it), so cause 1 is
  never ENABLED, whatever `mip.SSIP` holds.
- `w_mie` is never called at all, and `mie` is 0 at reset, so `mie = 0x220`
  from `start()` onward, forever.
- `mideleg = 0xffff` (`start.c:32`) delegates bits 0-15, so masking by
  `mideleg` removes nothing; the restriction comes entirely from `mie`.

So `s_pending ⊆ {bit 5, bit 9}`, `findPendingInterrupt` can only return
S-timer or S-external, and the scause the trap writes is `SCAUSE_STIMER` or
`SCAUSE_SEXT` — exactly `devintr`'s two.

**What has to change is `sconf`'s `mie` conjunct.**  Today it carries only
`and_vec mie_v (not_vec mdv0) = zeros' 64` ("nothing is M-destined"), with
`mie` itself existential.  It needs the value PINNED, exactly as the menvcfg
conjunct already pins `menvcfg0 = MENVCFG_S` and for exactly the same reason:
a boot-established constant that no later instruction touches.  Either
`mie_v = MIE_S` (the literal `0x220`) or the weaker
`and_vec mie_v (not_vec S_INTR_MASK) = zeros' 64`; prefer the literal, since
it is what `start()` provably leaves and it makes the dispatch computation a
`vm_compute`.

That is a small, bounded change to one conjunct plus whatever establishes it
in the boot chain — NOT a new machine-state invariant, and `clock_inv`'s
fully-existential `mip` can stay as it is.

## STATUS: **kerneltrap() IS PROVEN.**

`Kerneltrap.wp_kerneltrap_sconf` is a theorem.  `Print Assumptions` on it
gives exactly

    5 rv64d platform axioms + functional_extensionality_dep
      + LinkConsoleintr.Consoleintr.wp_consoleintr_sconf

and nothing else.  **No `wp_printk_gen_sconf`** — the panic-arm work paid off
— and **no `kerneltrap_returns`**.  consoleintr is inherited through
devintr → uartintr and is one of the four sanctioned assumed contracts; the
proof introduces no assumption of its own.

Files: `CodeKerneltrap.v` (40 decode facts, generated),
`ProofKerneltrapParts.v` (835 lines), `ProofKerneltrap.v` (444 lines, the
functor over DEVINTR/MYPROC/YIELD), `LinkKerneltrap.v`.

**What is NOT done, and it is the only thing left:** `ProofKernelvec.v` still
runs against `KERNELTRAP_RETURNS`, whose `Axiom` `LinkKerneltrap.v` still
supplies as `KerneltrapRet`.  That assumption is no longer about whether
kerneltrap works — it is about the SHAPE of the handler contract, i.e. step
10 below.  Nothing else stands between the two.

### The proof's shape

- `kt_pro` — prologue (6-slot frame, five saves, frame pointer), the three CSR
  reads, and both panic tests, each provably falling through.
- `kt_epi` — the epilogue, at +0x36 in the MIDDLE of the function, so THREE
  paths reach it and it is proved once over an arbitrary arrival map.
- The functor — the four call sites and two genuine branches: the timer test
  (`devintr_ret sc` is 1 or 2, so a real split) and "no current proc".
- `PANIC` and `PRINTK` are **not functor parameters**, because no arm reaches
  either.  The axiom ledger is structural, not incidental.

### Three things worth keeping

- **State the postcondition ABSOLUTELY.**  `wp_csrw_sstatus_s_sconf` hands
  back `sie_cap_gpr_at msf`, but the five reloads and the sp pop go through
  the ordinary funnel and lose `msf` again.  The epilogue therefore re-derives
  SPP/SPIE at the end from the `sret_bits` mirror and SIE from the arm index.
  A relative fact (`= SPP of the entry mstatus`) would not have survived; an
  absolute one (`= 'b"1"`) does.
- **Never leave `_` for a frame word at a block boundary.**  The gap slot's
  value left as an evar cost **141 seconds** per `iExact` and then failed;
  naming it once, up front, took the file's slowest step to 1.2 s.  This is
  the "a failing tactic in a whole-function WP looks like a hang" rule with a
  specific cause.
- **`subst p` picks the WRONG equation.**  In the yield arm both `Hpj :
  proc_addr j = p` and myproc's `Hmpa0 : mmp !!! a0 = p` define `p`, and
  `subst` took the latter.  Bridge with explicit `iEval (rewrite -Hpj)`.

## The mstatus-exposing bundle (`sconf_at` / `sie_cap_gpr_at`)

`kerneltrap`'s last instruction is `csrw sstatus,s1`, restoring the sstatus it
read at entry, and **kernelvec's `sret` needs to know what that did**: it reads
SPP (to return to S-mode) and SPIE (to restore SIE).  `sconf` quantifies
mstatus EXISTENTIALLY, so neither the leaf's postcondition nor kerneltrap's
can say anything about those fields.

The fix is an mstatus-PINNED variant of the bundle — `sconf_at ms`,
`sie_cap_gpr_at ms m n b p` — with `sconf ⊣⊢ ∃ ms, sconf_at ms`.  **It is
needed only at the two boundaries, not throughout**: kerneltrap threads the
plain `sie_cap_gpr` through its whole body (loads, stores, branches, the four
calls) and switches to the `_at` flavour only on the OUTPUT side of the final
`csrw sstatus` and of its own contract.  Do NOT give every leaf an `_at`
twin — that is exactly the cross-product the guiding principle forbids.

The entry mstatus does NOT need threading: the value written is held in a
REGISTER (s1) across the whole body, so the register-file tracking already
carries it, and the leaf relates the post-mstatus's fields to the WRITTEN
WORD, not to some earlier state.

Leaf shape:

```coq
wp_csrw_sstatus_s_sconf (wval : mword 64) :
  rget m rs1 = wval ->
  (* wval's S-visible fields agree with sconf_ms_facts — true because wval
     was read from an mstatus that satisfied them *)
  <sstatus_ok wval> ->
  (* the write must not MOVE SIE: at b = false, restoring the entry sstatus
     (SIE already 0) is SIE-neutral, so no ghost moves at all.  A write that
     did move it would need all three ghost pieces — that is csrci/csrsi's
     business, not this leaf's. *)
  _get_Sstatus_SIE wval = sie_bit b ->
  sie_cap_gpr m n b p -∗ pc_is pc -∗ instr ... -∗
  wp_next b p (fun CID =>
    ∀ msf, ⌜ sconf_ms_facts msf ⌝ -∗
           ⌜ _get_Mstatus_SIE  msf = _get_Sstatus_SIE  wval ⌝ -∗
           ⌜ _get_Mstatus_SPP  msf = _get_Sstatus_SPP  wval ⌝ -∗
           ⌜ _get_Mstatus_SPIE msf = _get_Sstatus_SPIE wval ⌝ -∗
           sie_cap_gpr_at msf m n b p -∗ pc_is (pc+4) -∗ WP ...) -∗ WP ...
```

**`WpSieFlipBits.flip_core` already proves the hard half** — for any `W` whose
S-fields mirror `ms`, `legalize_sstatus_val ms W` has the prescribed SIE and
still satisfies `sconf_ms_facts`.  It is currently `Local`; drop that (a
`Local Lemma` is invisible to every other file — see `durable-notes.md`) and
add SPP/SPIE rows to the ladder (`lift_SPP`/`lift_SPIE` at L3,
`mstatus_legalized_SPP`/`_SPIE` at L4 in `WpGprCsrwC.v`).

## What kerneltrap needs that the current `intr_handler_spec` does NOT hand over

This is the real blocker, and it is the other half of
`completed/explicit-cpuid.md`'s **STAGE 2** ("gated on kerneltrap actually
being proved").  Today `intr_handler_spec` gives the handler only registers,
config cells, and `intr_frame`; kernelvec gets away with it because the
kerneltrap axiom does nothing.  A real kerneltrap needs:

1. **The trap-scratch CSRs** (`scause`, `stval`, and `sepc` at a pinned value).
   They live in `sie_arm true` at the interrupted instruction and must be
   handed to the handler and taken back.
2. **`cpu_hart 0 ? p`** — this hart's `cpus[cid]` cells plus the counting
   token.  Also in `sie_arm true`.  devintr's whole cone (acquire/push_off)
   touches `c->noff`.
3. **A deeper stack carve.**  `kv_frame_slots = 32` covers kernelvec's own
   frame only.  It must cover the whole trap path: kernelvec (32) + kerneltrap
   (6) + max(devintr = 40, myproc, yield's cone).  Changing that constant
   re-tunes every `K ≤ n` premise in the tree — budget for it.
4. **The persistent device/proc credentials** — `devintr_caps`, `procs_inv`,
   `scheds_inv`, `panic_wp_any`, `kernel_text`.  All persistent, so they can be
   closed over at `intr_inv` allocation exactly as `hw_config`/`minstret_inv`/
   `kernel_text` already are in `kernelvec_handler_spec`; they never need to
   appear in the handler contract's footprint.
5. **`own_ctx (p_context pj)` + `park_hlf j true` when `p ≠ 0`** — exclusive,
   per-thread, needed by `yield`.  They belong in `sie_arm true` under a
   disjunction keyed on `p = zero_reg`, which is exactly the shape
   `wp_next`'s second escape hatch ("no current proc ⇒ same hart") already
   assumes.
6. **Hart migration.**  `yield` parks and resumes elsewhere, so the handler's
   continuation is at a NEW hart and `wp_exec_step_intr`'s `iLöb` has to be
   hart-generic.  This is Stage 2 verbatim, including its cut: canonical
   per-hart ghost names `sie_name : CPU -> gname` mirroring `strans_name`, plus
   a persistent `□ ∀ c, ∃ h, intr_inv (CID:=c) h`.

Also: `intr_handler_spec`'s post should stop pinning mstatus to
`sret_ms5 (trap_ms elp ms)` and instead re-establish `sconf` with SIE = '1'.
The engine does not need mstatus back exactly — the interrupted code owns it
existentially inside `sconf` — and pinning it is not provable of a real
handler, whose push_off/pop_off pairs leave `legalize_sstatus_val`-shaped
mstatus values rather than the literal original.

## DONE: `SpecYield`/`SpecSched` are now `forall eb`

They used to pin `eb = true`, which made both contracts unusable from
kerneltrap.  Derivation of why, from both sides:

- *From the C*: the trap cleared SIE, so `push_off` inside `yield`'s
  `acquire(&p->lock)` records `intena = intr_get() = 0`.  `sched` saves and
  restores that across the `swtch`; the matching `release` pops to noff 0 with
  `intena == false` and does NOT `intr_on()`.  kerneltrap therefore returns
  with interrupts still off, and kernelvec's `sret` is what re-enables them
  from SPIE.  Correct xv6 behaviour, not a bug.
- *From the ghosts*: at level 0 `intr_count 0 eb` is the eighth at
  `sie_bit eb` and `sie_arm b` holds the complementary eighth at `sie_bit b`;
  `ghost_var` agreement forces `b = eb` (`CpuOwn.cpu_own_eb_agree`).  Inside
  the handler the live SIE bit is '0', so `eb = false`.
- `SpecSched.v`'s comment "A parked kernel thread always got here from
  interrupts-enabled code, so this costs nothing" was the assumption that
  fails: a thread parked from `kerneltrap` got there from a TRAP.  Nobody had
  hit it because `wp_yield_sconf` had **zero consumers** — kerneltrap is its
  first.

### What the generalization turned out to be

**`sched` needed no proof change at all.**  Its `eb = true` premise was
introduced by `intros` and never used: the trap CSRs were already threaded
explicitly rather than taken out of the SIE arm, the post-swtch intena
restore and ghost retune already ran at both values
(`intr_count_retune_on`/`_off`), and the `intr_handler_avail` in its
postcondition comes from the DISPATCH payload — the scheduler that resumes
the thread always runs with interrupts on — not from the parking thread's own
entry stash.  Deleting the premise and the dead `intros` name was the whole
change (plus dropping one `eq_refl` at each of the three call sites).

**`yield` collapsed from two indices to one.**  `eb` and the resource index
`b` were separate binders that `cpu_own_eb_agree` already forced equal at
level 0, so the second only ever admitted vacuous instances; the contract now
carries one `eb` and threads it through every leaf.

**Two things had to be added, and both are about per-hart resources.**

- `IntrDefs.trap_csrs_ext eb := if eb then emp else trap_csrs`, the
  complement of `trap_csrs_pay 0 eb`, with
  `trap_csrs_ext_split : trap_csrs_pay 0 eb ∗ trap_csrs_ext eb ⊣⊢ trap_csrs`.
  `sched`'s crossing demands the whole set unconditionally, and
  sepc/scause/stval are PER-HART registers, so a parking function cannot
  frame them — it must hand them over and take the resuming hart's back.  At
  `eb = true` yield's own acquire produces them by dismantling the enabled
  arm and the caller brings `emp`; at `eb = false` there is no arm and the
  caller brings the set.  Exactly one of the two is `emp`.
- `IntrDefs.trap_csrs_ext_transport`, the twin of `cpu_own_transport` and
  needed for the same reason: the lent set is hart-indexed, so it cannot be
  framed around a step that may move the hart.  It transports by the same two
  halves — at `eb = true` the proposition is literally `emp` and mentions no
  hart; at `eb = false` no trap was taken, so `wp_next`'s conditional
  equality pins the hart.  **A hart-indexed resource that survives a possible
  migration needs a transport lemma, not a frame** — this is the second
  instance of that shape, and the pattern is worth reaching for directly.

**And `wp_next_chain` had to stop assuming one index.**  A PARKING function's
own `wp_next` index is the literal `true`, while the leaves it ran carry its
caller's `eb`, so the goal and the chain facts are disjunctions with
different left components and a plain `specialize` does not typecheck.  The
tactic now falls back to keeping the RIGHT disjunct (the left one,
`true = false`, is absurd) and re-injecting it at whatever index each chain
fact carries.  At a matching index the old path still fires.

### The crossing index is now the literal `true`

`wp_next b pj` became `wp_next true pj`, matching `sched`.  This is a
correctness fix, not bookkeeping: at `eb = false` the old form collapsed via
`wp_next_off` to "yield returns on the hart that called it", which is false —
yield parks, and a `swtch` moves the hart with interrupts off, so it has
nothing to do with SIE.  It was invisible only because the contract had no
consumers and its `eb = true` instance made `b` true.

## Worklist

1. ~~`CodeKerneltrap.v` + manifest + shards~~ **done**.
2. ~~The five CSR leaves~~ **done**.
3. ~~`sconf_at`, `sie_arm_half_agree`, the SPP/SPIE ladder rows, `flip_core`
   exported and widened~~ **done**.
4. ~~The SPP+SPIE ghost mirror (`sret_bits`)~~ **done**.
5. ~~The `eb` generalization of `SpecYield`/`SpecSched`~~ **done**.
6. ~~`SpecKerneltrap.v` on the house-spec shape~~ **done**.
7. ~~`ProofKerneltrapParts.v` + `ProofKerneltrap.v` + `LinkKerneltrap.v`~~
   **done — kerneltrap is proven.**
8. ~~Grow `kv_frame_slots` 32 -> 78 to cover the whole trap path~~ **done**
   (kernelvec's 32-slot frame + `kerneltrap_stack` = 46; `kt_carve_fits`
   ties the two so they cannot drift).  `kernelvec_handler_spec` now splits
   the carve, keeps the top 32 for its own save windows, and frames the
   lower 46 across as the callee budget.  Everything else absorbed it
   symbolically; `boot_stack_slots K_main` went 86 -> 132 slots (1056 bytes,
   still inside `_entry`'s 4096-byte slice).

9. **THE OPEN FORK — where preemption's resources live.**  See the section
   below.  This is what the old notes deferred as "should be made against
   kerneltrap's real contract, not guessed"; the contract now exists, so the
   question is answerable, and it is bigger than a wiring change.

10. **The `intr_handler_spec` upgrade + `ProofKernelvec.v` rewiring**
   (explicit-cpuid Stage 2).  The handler contract must start
   handing the handler the trap CSRs, `cpu_hart`, the `sret_bits` mirror at
   `('b"1", 'b"1")`, a deep enough `kv_frame_slots`, the persistent device/proc
   credentials, `kt_proc_res`, and a hart-generic Loeb.  It also owes the two
   facts kerneltrap takes as premises: pin `mie` in `sconf` (see RESOLVED
   above) and expose the taken cause out of `wp_exec_step_intr`'s trap arm.
   When it lands, delete `KERNELTRAP_RETURNS`, `KerneltrapRet`, `kv_cell` and
   `kt_clobbered`; nothing else refers to them.

## THE OPEN FORK: where preemption's resources live

`kerneltrap` PREEMPTS.  On a timer interrupt with a current process it calls
`yield`, which parks the interrupted thread — and parking needs that thread's
`own_ctx (p_context p)` and `park_hlf j true`.

**Today those are ordinary frames** held by whichever function happened to be
interrupted, so they are *unreachable* from the handler: a frame lives outside
the handler's WP.  For the trap to park the thread they have to be reachable,
and there are only two places they can be.

Measured footprint of each:

- **(A) Move them into `sie_arm true`**, beside `cpu_hart 0 true p`, with
  surrender/reclaim plumbing at the SIE flips (`csrci` hands them to the code,
  `csrsi` takes them back) — the same shape `cpu_cells_pay` already has.
  Cost: **35 `Spec*.v` and 31 `Proof*.v` files** thread `own_ctx`/`park_hlf`
  today (essentially the whole blocking half of the kernel: sleep, the log,
  bio, the pipe and file layers, kexit/kwait).  Every one of them would gain
  the pay/reclaim conjunct.  `own_ctx`/`ctx_cells` also have to move below
  `IntrDefs` first — cheap, they depend only on `↦₈` — because `SwtchCtx`
  currently imports `IntrDefs`, not the other way round.
- **(B) Put the current thread's park resources in a per-hart INVARIANT**, so
  the handler OPENS them rather than being handed them.  `SchedCtx.scheds_inv`
  already does exactly this for one half of the park bit, per hart, which is
  why this looks like the natural extension.  Cost is concentrated in
  `SchedCtx.v` + the handler contract instead of spread over 66 files —
  but it is a real design change to the parked-scheduler protocol, not a
  mechanical sweep, and it has to keep `own_ctx`'s exclusivity honest.

**Recommendation: investigate (B) before committing to (A).**  (A) is the
brute-force answer and its cost is now measured rather than guessed; (B) is
plausibly an order of magnitude smaller and follows a protocol the tree
already has.  Either way this is the last thing between the proven
`kerneltrap` and deleting `KERNELTRAP_RETURNS`.
