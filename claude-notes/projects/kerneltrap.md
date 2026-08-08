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

## STATUS

**Step 1 (decode layer) — DONE.**  `iris/CodeKerneltrap.v` (40 `kti_<off>`
facts) generated by `tools/gen_code.py`, manifest row
`["CodeKerneltrap.v","kerneltrap","kti_",2]`, 122 lines added across 16
`KernelDecode*.v` shards, `_CoqProject` updated.  Full tree green;
regeneration is idempotent.

**Step 2 (CSR leaves) — DONE, all five.**  In `WpSconfCsr.v`, with the
privilege-free read halves in `WpGprCsrrB.v`:

- `wp_csrr_ro_s_sconf` — **THE read-only S-CSR leaf, stated once.**  sepc /
  scause / stval are the same instruction at three CSR numbers, so the leaf
  abstracts over the number (via an exec-layer premise) and over how the
  architectural read transforms the cell (`f`: identity for scause/stval,
  `mepc_val` for sepc, whose read runs `align_pc`).  The three instances are
  five lines each; the previously-cloned `wp_csrr_scause_s_sconf` is now one
  of them.  `rg` is a `register_bitvector_64`, not a `register`, so the cell's
  value type is definitionally `mword 64`; the `register_beq rg nextPC = false`
  premise is what migrates the lookup across the nextPC bump and is a
  `vm_compute` at every instance.
- `wp_csrr_sepc_s_sconf`, `wp_csrr_stval_s_sconf`, `wp_csrr_scause_s_sconf`.
- `wp_csrw_sepc_s_sconf` — the `sepc` cell threaded explicitly (same reason as
  stvec's: at `b = false` nothing in the ambient bundle owns it).  The written
  word does NOT land verbatim — sepc legalizes through `mepc_val` (bit 0
  cleared), so the post carries the wrapper, like satp/stimecmp and unlike
  stvec.
- `wp_csrw_sstatus_s_sconf` — the S-status RESTORE, and the one leaf whose
  postcondition exposes mstatus (`sie_cap_gpr_at msf`), because SPP/SPIE are
  its entire content.  The written word is taken as `sstatus_read ms0` for a
  well-formed source `ms0` rather than as an abstract word plus a field
  predicate: that is the only way the instruction is ever used, and it makes
  `flip_core`'s four field premises derivable inside the leaf.  Premise
  `_get_Mstatus_SIE ms0 = sie_bit b` — **the write must not MOVE SIE**; one
  that did would have to move all three ghost pieces and re-seal the interrupt
  invariant, which is the csrci/csrsi leaves' job.  At the trap-handler use
  the premise is free.
- Shared: `exec_check_CSR_result_read_extS` (the Ext_S accessibility check
  once, over the CSR number; sepc/scause/stval each contribute four
  `vm_compute`s).  sepc's privilege-free write chain sits in `WpSconfCsr.v`
  rather than `WpGprCsrwB.v` on purpose — its legalizer is mepc's, in
  `WpGprCsrwA`, and importing A into B for one CSR with no M-mode consumer
  would invert the A/B layering.

**Step 3 (the bundle + ladder work the sstatus write needed) — DONE.**

- `IntrDefs.v`: `sconf_msown` / `sconf_at` / `sie_cap_gpr_at` plus
  `sconf_at_close` / `_open` / `_facts` and `sie_cap_gpr_at_close` / `_open`.
  Written as an ACCESSOR (payload + a wand taking a replacement triple back to
  `sconf`), so `sconf` itself is untouched — no second copy of its body to
  keep in sync, and every existing destructuring still works.
- `IntrDefs.sie_arm_half_agree` — the live SIE bit is the arm index, at either
  index and with no case split at the call site.  This is what refutes the
  "interrupts enabled" panic.
- `WpGprCsrwC.v`: the SPP and SPIE getter rows (`qSPP_u*`, `qSPIE_u*`) and
  `mstatus_legalized_SPP` / `_SPIE`.  Short next to MPRV's or SXL's because
  the chains stop at the field's own setter.
- `WpSieFlipBits.v`: `lift_SPP` / `lift_SPIE`, and `flip_core` is no longer
  `Local` and now also concludes SPP/SPIE.  It was always the reusable
  statement, not an internal step — the two SIE flips are its
  `W = sstatus_write_val ...` instances and `csrw sstatus` is the other
  consumer.



**Step 8 (the spec) — DONE.**  `SpecKerneltrap.v` now holds TWO interfaces,
and the arrangement is deliberate and temporary:

- `KERNELTRAP` — the real house-spec contract, `wp_kerneltrap_sconf_body`.
  `sie_cap_gpr_at ms_e` in with `⌜_get_Mstatus_SPP ms_e = 'b"1"⌝`,
  `sie_cap_gpr_at ms_f` out with SPP/SPIE/SIE pinned to `ms_e`'s;
  `cpu_own 0 false p C false`; `sepc`/`scause`/`stval` threaded explicitly
  with `⌜devintr_ret sc ≠ 0⌝` and `⌜ret_pc ep = ep⌝`; `devintr_caps` +
  `scheds_inv` persistent; `kt_proc_res p` (the yield arm's `own_ctx` +
  `park_hlf`, under a `p = zero_reg` disjunction — the same test the C makes
  and the same one `wp_next`'s second escape hatch uses); and `wp_next true p`
  on the crossing.  `kerneltrap_stack = 46` = its own 6 slots + devintr's 40.
  Post gives sepc back at `ep` but scause/stval only existentially: those are
  the RESUMING hart's cells.
- `KERNELTRAP_RETURNS` — the legacy assumed round-trip contract, renamed from
  `KERNELTRAP`.  `LinkKerneltrap.v` still supplies it with an `Axiom` and
  `ProofKernelvec.v` is still a functor over it.  **Delete it, `kv_cell`,
  `kt_clobbered` and the axiom the day step 10 lands** — nothing else refers
  to them.  Two interfaces for one function is not the end state; the reason
  it is tolerable now is that the new contract cannot be CONSUMED until the
  engine changes, and the old one cannot be deleted until it is.

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

## Worklist, in dependency order

1. ~~`CodeKerneltrap.v` + manifest + shards + `_CoqProject`~~ **done**.
2. ~~The five CSR leaves~~ **done**.
3. ~~`sconf_at` / `sie_cap_gpr_at`, `sie_arm_half_agree`, the SPP/SPIE ladder
   rows, `flip_core` exported and widened~~ **done**.
4. Pin `mie` in `sconf`'s mie conjunct (see the RESOLVED section) and
   establish it in the boot chain.
5. Expose the taken cause out of `wp_exec_step_intr`'s trap arm and relate it
   to the `scause` the trap writes; with `mie` pinned, "the cause is 5 or 9"
   is a `vm_compute` on the dispatch set.
6. ~~The SPP ghost mirror~~ **done** (see the section above).  Note for
   anyone tempted: an `_at` variant of `wp_csrr_sstatus_s_sconf` does NOT
   help and should not be attempted — the funnel's `∃ ms` is what loses the
   pinning, not the leaf.
7. ~~The `eb` generalization of `SpecYield`/`ProofYield`/`SpecSched`/`ProofSched`~~
   **done** (see the section above).
8. ~~`SpecKerneltrap.v` on the house-spec shape~~ **done**.
9. `ProofKerneltrap.v` + `LinkKerneltrap.v` — the `Axiom` goes away and
   **nothing replaces it** (see the panic-arm table).
10. The `intr_handler_spec` upgrade + `ProofKernelvec.v` rewiring — i.e.
    explicit-cpuid **Stage 2**.  Until this lands, kerneltrap is proven but
    not yet CONNECTED.

Steps 4-9 deliver the function proof; 10 is what retires the axiom.
