# tools/vtest -- differential tests of the device semantics against QEMU

The question these tests answer is one-directional:

> is what the real hardware did an execution our model ALLOWS?

so a test only has to EXHIBIT one model execution matching what QEMU produced.
That is a computation, not a proof: no WP, no invariants, no Iris.  A test is
a `vm_cast_no_check`d equation between a projection of the model's reached
state and a literal captured from QEMU.  Nothing here is restricted to what
the xv6 driver's proofs assume -- a test may program the queue illegally, and
the only question is whether the model has a run that matches.

## Layout

    abi.h              THE ABI: regions, result layout, done handshake  (read first)
    vtest.S            prologue/epilogue every test image uses
    tests/<area>_<name>.S   one test program (a `vtest:` directive in it
                            carries the repeat count and backend configs)
    vtest.py           builds the image, runs QEMU, captures, generates Rocq
    ../../vtest-rocq/  the model side: harness + one .v per test

## Naming

A test is `<area>_<name>`, and the Rocq side is the same in CamelCase:
`tests/disk_rw.S` -> `vtest-rocq/DiskRw.v` + the generated `DiskRwGen.v`,
whose definitions are `disk_rw_text`, `disk_rw_qemu_result`, ...  Areas:

| area | what it is about |
|------|------------------|
| `core` | the CPU and ordinary memory: instruction semantics, the loaded image, the declared regions.  The plumbing test lives here. |
| `disk` | the virtio-mmio block device (`VirtioModel.v`) |
| `uart` | the 16550 (`DevModel.v`'s UART half) |
| `plic` | the interrupt controller ITSELF -- arbitration, priorities, thresholds, several sources |
| `pt` | Sv39 translation: the walk, the TLB, page faults, and the A/D write-back.  S-mode, `start_pt`. |
| `conc` | shared memory between harts.  Uses `vtest-rocq/VConc.v` and `smp=` rather than the single-hart harness. |

**The area is what the test is ABOUT, not everything it touches.**
`disk_intr` drives the PLIC and reads `mip`, but it exists to check the
DISK's interrupt path, so it is a `disk` test.  A `plic_` test would be one
whose subject is the controller -- two sources competing, a threshold that
masks one, a claim while another is pending.

## Running

    make vtest         regenerate from QEMU (needs qemu-system-riscv64 + the
                       riscv64 toolchain), then check the model against it
    make vtest-check   check the model against the CHECKED-IN captures only
                       (no QEMU, no toolchain) -- this is what CI runs

`vtest-check` is deliberately outside `make proofs`: a red test must not break
the proof build.  It needs only the ~20-file dependency cone of `RiscvExec` +
`DevModel`, not all of `iris/`.

## Observation channels

1. **The RESULT region** (`abi.h`).  QEMU side: read out of guest physical
   memory over QMP `xp`.  Model side: read out of `gmem`.  The whole 4 KB is
   compared, untouched zeros included -- nothing is trimmed, so a difference
   cannot hide in the tail.
2. **The disk image**.  QEMU side: byte-diff the raw `-drive` file after the
   process exits, reported per 512-byte sector.  Model side: `disk_read` over
   `v_disk`.  This is the channel that sees what a write request actually did.

The serial console is deliberately NOT a channel: printing a result costs
~10 instructions per character, and the model executes every one of them.
an early hex-printing version was 1600 instructions / 23 s; the same
observations through memory are ~40 instructions / 2 s.

## Rules a test program must obey

They come from the ABI and from what the model is:

- Only the regions in `abi.h` are mapped.  Anything else is a STUCK model.
- No dependence on `a1`/`a2`.  a0 (hartid) agrees, but the model writes a1 to
  a hardcoded `0x1000` that is not the DTB address (finding 18) and never
  writes a2 at all.
- No LR/SC: `exec` treats the reservation outcomes as stuck.
- `-smp 1`.  The model has 8 harts, but a schedule that only ever steps hart 0
  is a legal execution, so this costs nothing.
- **A bad FETCH is a TRAP LOOP, not `VStuck`.**  `mtvec` is 0 at power-on, so
  an illegal instruction sends the pc to 0, where the fetch at an undeclared
  address raises an access fault that traps back to 0 -- forever.  The status
  is `VBudget`, and the way to tell it from a small budget is to pin the pc at
  two different step counts (`CoreRegsFpr.v` does).  `VStuck` is for DATA
  accesses the model refuses.
- **The clock never ticks.**  The harness always steps `riscv_step false`, so
  `mcycle`/`cycle`/`time` are frozen while `minstret` DOES advance -- which is
  the control showing the freeze is about the clock and not about counters in
  general.  Consequence: no vtest image can observe elapsed time, so this
  suite cannot reach the timer-interrupt path at all, and `mip.MTIP` can only
  ever appear as power-on garbage.
- **QEMU's `-kernel` boot contract** passes a0 = hartid, a1 = the DTB pointer,
  AND a2 = `0x1028` (virt's reset ROM leaves a pointer to the `fw_dynamic`
  info struct there).  The model's chain writes a0 and a1 and nothing else;
  a2 is admitted as a witness.  See finding 18 for a1.
- **Do not write FCR bit 0 in a test that receives.**  Flipping FIFO-enable
  flushes the receive path, and the host's first byte is already in QEMU's
  holding register before the guest's first instruction runs -- an FCR
  FIFO-enable at the top of the program silently eats byte 1 (measured: reads
  `0x42` first, 8 runs of 8).  Relatedly, with the FIFOs off QEMU delivers one
  character at a time and re-offers the next only after RHR is read, so any
  "LSR bit 0 immediately after a read" field is a race against the host rather
  than a fact about the device; order plus a spin before each read
  establishes the same property deterministically.
- **A `pt_` program must pin `menvcfg.ADUE` explicitly, before `satp`.**
  Power-on ADUE DIFFERS (finding 20): clear in the model, set on the machine.
  So a page table written the natural way (`V|R|W|X`, no A/D) needs an A/D
  update on its first access, which FAULTS in the model and SUCCEEDS on QEMU
  -- and that makes an unrelated translation test diverge in a way that looks
  like a walk bug.  Set or clear bit 61 deliberately in every `pt_` program;
  Svadu is the natural default, being what `start()` gives xv6.  QEMU does
  accept the CLEAR (verified -- ADUE is WARL, so this was not a given), so the
  Svade arm is testable on hardware too.
- **Use `lla`, never `la`, to materialise an address.**  `la` assembles to a
  GOT load; the GOT is outside `.text` and the image is built with
  `objcopy -j .text`, so it is not in the image at all.  The model then reads
  an undeclared address and goes STUCK -- which looks exactly like a genuine
  "the model does not decode this" finding.  Whenever a test reports `VStuck`,
  check `stuck_pc` against
  `riscv64-linux-gnu-objdump -d tools/vtest/build/<name>.elf` and confirm the
  instruction it names is the access you meant to test.
- The QEMU command line is fixed by `vtest.py`, and
  `-global virtio-mmio.force-legacy=false` is part of it: without that flag
  QEMU presents a LEGACY virtio-mmio device (Version reads 1, not 2) and every
  register test disagrees for the wrong reason.

## QEMU quirks that look like findings

- **The virt PLIC is built with `num-priorities = 7` and silently ignores any
  priority or threshold write above 7.** A probe using threshold 9 looks
  exactly like "the threshold does not mask".  Keep every value <= 7.
- **QEMU's `sifive_plic_write` does not recompute the context notification on
  an ENABLE write**, so it lags by one register access.  `plic_mask.S`
  re-writes the threshold with its existing value right after the enable write
  to force the recompute; that write is a no-op on the model side.
- QEMU defaults to LEGACY virtio-mmio (Version reads 1);
  `-global virtio-mmio.force-legacy=false` is in the fixed command line.
- A QEMU process that outlives its test holds the disk image's write lock, and
  the next run dies with "Failed to get write lock"; the runner quits it in a
  `finally`.

## Recording a divergence

A test compares field by field, so a known divergence does not have to make
the build red.  The convention is to pin the value on BOTH sides:

```coq
Lemma t2_rw_model_diverging : ... = t2_model_diverging.   (* [8; 0; 512; 512] *)
Lemma t2_rw_qemu_diverging  : ... = t2_qemu_diverging.    (* [1024; 25684; 1; 513] *)
Lemma t2_rw_really_diverges : t2_model_diverging <> t2_qemu_diverging.
```

with a comment classifying it.  This is green today and the model-side
equation goes RED the day someone changes the model there -- which is exactly
when the test file should be revisited, and is the property a comment alone
would not give.

## Findings so far

Classified as *incompleteness* (the model is stricter than the hardware, so
some real driver has no model execution -- cannot make a proof wrong, but
limits what can be verified) or *defect* (the model produces a value the
hardware never produces, so a proof that depends on it is about a device that
does not exist).

| # | what | model | QEMU | kind | found by |
|---|------|-------|------|------|----------|
| 1 | `QueueNumMax`, and `QueueNum` writes | 8, only {1,2,4,8} accepted | 1024 | incompleteness | `disk_rw`, `disk_ident_qnum` |
| 2 | offered / negotiated features | `FLUSH\|CONFIG_WCE`, negotiates 0 | `0x30006e54`, negotiates `0x6454` | incompleteness | `disk_rw` |
| 3 | `DeviceFeaturesSel` (0x14), `DriverFeaturesSel` (0x24) | not decoded -- the store is STUCK | writable; the high feature word is `0x101`, and a full 1.x negotiation acking `VERSION_1` reaches Status 11 | incompleteness | `disk_ident_featsel`, `disk_ident_drvfsel` |
| 4 | **`used.ring[i].len`** | `vr_len` (the data descriptor's length) in both directions | 1 for a write, 513 for a read | **defect** | `disk_rw`, `disk_order` |
| 5 | **completion ORDER of two in-flight requests** | publication order ONLY | either order | **unsoundness** | `disk_order` |
| 6 | UART MCR (4), MSR (6), SCRATCH (7): read as 0, writes discarded | `0` / `0` / `0` | `3` / `0xb0` / `0x5a` | incompleteness | `uart_regs` |
| 7 | UART ISR bits 7:6 (FIFOs-enabled) hardcoded set | `0xc1` at reset | `0x01` until FCR enables the FIFOs | incompleteness | `uart_regs` |
| 8 | UART THRE interrupt modelled as a LEVEL, not latched | second ISR read still `0xc2` | second read `0xc1` -- the read cleared it | incompleteness | `uart_regs` |
| 9 | the UART window decodes width 1 only | a 4-byte read is STUCK | returns `0x00000008` (the bus narrows to register 4) | incompleteness | `uart_width` |
| 10 | **PLIC claim ignores the context THRESHOLD** | returns the masked source and clears its pending bit | returns `0`, the source stays pending | **unsoundness** (and a defect) | `plic_thresh` |
| 11 | PLIC M-context registers (enable 0x2000, threshold 0x200000, claim 0x200004) not decoded | STUCK at the first M access | services all three | incompleteness | `plic_mctx` |
| 13 | virtio CONFIG SPACE: capacity (0x100) and ConfigGeneration (0x0fc) | not decoded -- STUCK | capacity **128 sectors**, exactly the backing file | incompleteness | `disk_ident_cap`, `disk_ident_confgen` |
| 14 | virtio `QueueReset` (0x0c0) and the SHM registers (0x0ac..) | not decoded -- STUCK | `QueueReset` 0; `SHMLen` all-ones | incompleteness | `disk_ident_qreset`, `disk_ident_shmsel` |
| 15 | sub-word access anywhere in the virtio window (1- and 2-byte, read and write) | not decoded -- STUCK | reads give 0; a 1-byte Status write is a NO-OP | incompleteness | `disk_ident_rd1/rd2/wr1` |
| 16 | a per-queue write with `QueueSel` /= 0, and `QueueNotify` /= 0 | REFUSED -- STUCK | both ignored | incompleteness | `disk_ident_qsel`, `disk_ident_notify` |
| 17 | a descriptor chain that is not exactly THREE descriptors | the device STALLS (`virtio_stalled`); only `DevStepDiskWild` covers it | served normally -- 512 bytes written, status 0 | incompleteness in practice | `disk_chain` |
| 18 | **`a1` at entry** -- the device-tree pointer | `0x1000`, a HARDCODED constant in `rv64d.v`'s `init_boot_requirements` | the real DTB address (`0x87e00000`), which moves with `-m` and the image | **defect** (boot contract) | `core_regs_gpr` |
| 19 | `misa` bit 7 (H), and `mideleg` as its consequence | H absent; `mideleg` 0 | H present; `mideleg` `0x1444` (VSSIP/VSTIP/VSEIP/SGEIP, hardwired when H is implemented) | incompleteness | `core_regs_mcsr` |
| 20 | `menvcfg` bit 61 (ADUE) at POWER-ON | `0` (Svade), so an access needing A/D FAULTS | `0x2000...` (Svadu), so hardware writes the bit back | incompleteness, and a FALSE board assumption | `core_regs_mcsr`, `pt_ad` |
| 26 | **the model's TLB is DIRECT-MAPPED (64 entries, `tlb_hash` = the low 6 bits of the VPN)** | at a colliding VPN the entry is evicted by the very next fetch, so a PTE rewritten WITHOUT `sfence.vma` is re-walked and the NEW mapping is used | keeps the stale entry | unsound direction, but see below | `pt_tlb` |
| 21 | `misa` advertises F and D but the model has NO F/D instructions | `fsd` takes an illegal-instruction trap (`mcause` 2, `mtval` = the encoding) | executes | incompleteness + internal inconsistency | `core_regs_fpr` |
| 22 | CSRs the model implements that QEMU's default virt CPU REFUSES: `mseccfg`, `mstateen0`, `sstateen0`, `scountovf`, `mcyclecfg`, `minstretcfg`, `ssp` | implemented, read successfully | illegal instruction | **model is WIDER -- needs a ruling**, see below | `core_regs_mcsr` |
| 23 | RHR read on an EMPTY receive FIFO | `0` | the LAST byte received -- the holding register is not cleared by a read nor by an FCR clear, only the DR FLAG is | incompleteness | `uart_rx` |
| 24 | **THE MEMORY MODEL: the model is sequentially consistent** | one shared `gmem`, a store is global the instant it retires -- (0,0) unreachable | store-buffering gives **(0,0) in a few percent of runs**, which RVWMO permits | **UNSOUNDNESS** | `conc_sb` |
| 25 | `sc.w` does not evaluate | `vm_compute` does not return (110 s+), so a test containing one cannot be COMPILED | executes | incompleteness (harness-blocking) | `conc_amo` |
| 12 | PLIC source 0's priority register not decoded (`plic_read`/`plic_write` gate on `0 <? off`), and `plic_nsrc` is 32 where the board has 96 | STUCK | offset 0 is read-only zero; source 32 is a real register | incompleteness | `plic_prio0` |

Finding 4 is the one worth acting on.  The spec defines the used element's
`len` as the number of bytes written into the DEVICE-WRITABLE part of the
chain -- the status byte alone for a write request, the data buffer plus the
status byte for a read.  `VirtioModel.virtio_used_writes` writes the data
descriptor's length regardless of direction, which is a value no real device
produces.  Nothing in the tree has noticed because xv6's driver ignores the
field.  The fix needs the request TYPE at that point, so it is local; what
makes it a decision rather than a drive-by edit is that VirtioModel.v's
reverse-dependency closure is 1286 files.

**Finding 5 is the serious one.**  `disk_order` publishes two write requests in
one batch -- eight sectors at 100 and one sector at 5 -- and records which
descriptor id lands in which used-ring slot.  QEMU produces BOTH orders:

| `-drive` options | in order | reordered |
|---|---|---|
| `cache=writeback` (the default) | 19/25 | **6/25** |
| `cache=writeback,aio=threads` | 20/25 | **5/25** |
| `cache=none,aio=threads` | 3/25 | **22/25** |
| `cache=none,aio=native` | 0/25 | **25/25** |

The model has no execution for the second.  `virtio_req_step` reads the chain
at position `v_seen` and hands back a state whose `v_seen` is one greater, so
the served order IS the publication order and no schedule can change it --
`DiskOrder.model_serves_head_only` states exactly that, off the model rather
than off this test.

This is the other direction from findings 1--3: not the model being stricter
than the hardware (which limits what can be verified but cannot make a proof
wrong), but the hardware having a behaviour the model has no transition for,
so a theorem proved against the model does not cover the machine it claims
to.  And it is live in xv6: `virtio_disk_rw` sleeps with its request
outstanding so up to `NUM` = 8 can be in flight, and `virtio_disk_intr` reads
each used element's ID and wakes `disk.info[id]` precisely because
completions need not come back in order -- under this model that code is only
ever exercised on the in-order case.

The fix is not local, which is why `DiskOrder.v` §4 only records it: the device
would have to serve any published-but-unserved position rather than `v_seen`
alone, so `v_seen : bv 16` becomes a set, `virtio_pending` and the completion
gate move with it, and `VirtioQueue`'s slot protocol and the DMA lease's
reachable-window argument (`virtio_queue_ok`'s `S`, closed under advancing by
one until it reaches `ai`) are stated against exactly the assumption this
breaks.

### Finding 10 is the second one with no model execution

`plic_cand` is `pending && enabled && (0 < priority)` and never mentions the
threshold; the threshold appears in `plic_eip` alone.  So **the model's
notification and its own claim disagree with each other**: a source masked by
the threshold raises no notification, yet `plic_claim` hands it back and
clears its pending bit.  QEMU returns 0 and leaves the source pending, so
lowering the threshold later re-exposes it.

Like finding 5, this is not merely a wrong value: `plic_read`'s claim arm is a
pure function of `plic_state`, so no schedule can produce QEMU's answer.

It is not live in xv6 -- `plicinithart` writes threshold 0 -- **but
`PlicPlan.v` deliberately leaves the per-hart threshold completely free**, so
the device invariant admits exactly the states where the two disagree.

The fix is three tokens and makes the two halves agree by construction: move
the threshold conjunct from `plic_eip` into `plic_cand` (where it subsumes
`0 < priority`), leaving `plic_eip := existsb (plic_cand p h) plic_srcs`.

### One divergence where the MODEL is right

`plic_level` shows the model re-forwarding a still-asserted level source after
`plic_complete`, where QEMU does not: QEMU's PLIC takes pending off the RISING
edge only.  A level gateway that re-forwards is the spec-faithful behaviour --
it is why a driver acknowledges the DEVICE before completing at the PLIC -- so
no model change is wanted.  The model does have a matching execution (`SLatch`
is never forced), but `VSched.settle` is eager and takes every enabled arm, so
this test cannot exhibit it.  Exhibiting it needs a `run_until` variant
parameterised by the device policy; until then it is recorded, not reproduced.

### Finding 17, and why the wild arm earns its keep

`chain_at` requires exactly three descriptors, so a 4-descriptor
scatter-gather chain leaves the device `virtio_stalled` and it never
completes -- `run_status` reads `VBudget`, and `disk_chain` confirms
`virtio_stalled = true` after 700 instructions, so it is a real stall and not
a small budget.

But this is **incompleteness in practice, not unsoundness**, and the
difference is the whole point of the "model UB as anything, never as nothing"
rule: `DevStepDiskWild` is enabled *exactly when* `virtio_stalled` holds, so
the model's transition relation genuinely does contain QEMU's behaviour --
the device may write anything anywhere, which includes writing what QEMU
wrote.  What the model does not contain is anything a driver PROOF could use.
`DiskChain.v` states both halves off the model (`model_refuses_longer_chains`,
`model_stalled_leaves_only_wild`) rather than off the test.

Exhibiting it would need a hand-written schedule interleaving ~550 `SCpu`
steps around one `SDiskWild` carrying ~530 (address, byte) pairs built
mechanically from the capture; `DiskChain.v` section 5 records what that takes.

### A correction to finding 4

`disk_err` runs the UNSUPP and FLUSH paths, where the model reports `used.len`
= 512 and QEMU reports 513 -- but the **spec** says 1 on both, since neither
path writes the data buffer.  So on these paths QEMU is not spec-conforming
either, and finding 4's fix must be stated against the SPEC (bytes actually
written into the device-writable part of the chain), not against QEMU's value.

### Finding 24 is the largest one the suite has found

`conc_sb` is the store-buffering litmus test -- `hart 0: X=1; a=Y` alongside
`hart 1: Y=1; b=X` -- and QEMU produces **(a,b) = (0,0)**, which no
sequentially consistent machine can.  Measured 55 times in 1200 runs (4.6%)
by the agent, and independently re-confirmed at 4 in 200.  It is not a
truncated run: in the (0,0) captures **X and Y are both 1**, so both stores
landed and both loads still returned 0 (`conc_sb_both_stores_happened`).

QEMU is RIGHT.  RVWMO permits a store to be reordered past a later load, the
litmus program has no fence between them, and QEMU on an x86 host exposes the
host's TSO.  It is the MODEL that is wrong.

And it is not a granularity gap that a finer schedule would close.  `VConc`
has one `gmem`; `ghart` hands it to a hart and `gput` makes that hart's memory
THE memory, so no store can wait anywhere -- `ConcSb.v` states this off the
model (`model_hart_sees_the_one_memory`, `model_store_is_immediately_global`)
and enumerates all six interleavings of the two two-instruction sequences,
none of which gives (0,0).  Per-node interleaving would not help either.

**This is live in xv6.**  `acquire`/`release` carry `__sync_synchronize()`
precisely because the hardware reorders a store past a later load -- and under
this model those fences are unobservable, so nothing in the development can
tell a correct one from a missing one.

The model reproduces the three SC outcomes, whole result region each, lined up
with the capture order (`conc_sb_model_admits_every_sc_outcome`).

### Finding 26 is a different shape from the other three

`pt_tlb` rewrites a level-0 leaf without `sfence.vma` and reads again, at two
VAs chosen to land in different TLB sets.  At **set 7 both machines keep the
stale entry** -- that is the control.  At **set 0 QEMU keeps it and the model
has already re-walked**, 20 runs of 20.

The cause is exact: `tlb` is a `vec (option TLB_Entry) 64` and `tlb_hash` is
literally the low `num_tlb_entries_exp = 6` bits of the VPN, so the TLB is
DIRECT-MAPPED -- and every fetch in a vtest image is at VPN `0x80000` with
every result store at `0x80100`, both `= 0 (mod 64)`, so a set-0 entry is
evicted by the next instruction.

Unlike findings 5, 10 and 24 the model is not missing a FREEDOM -- set 7 shows
it can keep a stale entry.  It has a smaller, less associative TLB, and both
are legal implementations.  The risk is directional rather than structural: a
theorem over this model can conclude "the access after a PTE write uses the
new mapping" where the real machine uses the old one.  Only software that
omits `sfence.vma` is exposed, and nothing in xv6 is -- but the model hands
such a program the favourable answer instead of refusing it.

A fix is not more capacity: any deterministic finite TLB collides somewhere.
It would have to make eviction NONDETERMINISTIC -- the `DevStepDiskWild`
over-approximation shape applied to `translate`.  Recorded, not proposed.

### The A/D write-back IS executable, and why `sc.w` is not

`pt_adu` runs two write-backs under `vm_compute` at ordinary cost -- no hang,
no `VStuck`, no `internal_error`.  The `sc.w` non-termination of finding 25
does not reach this path, and the reason is structural: `execute_STORECON`
goes through the opaque platform axioms `match_reservation`/
`cancel_reservation`, which `exec` cannot step, whereas
`write_pte_conditional` is `mem_write_value_priv ... con = true` -- an
ordinary `Interface.MemWrite` outcome.  `exec` answers it `inl None` and
`write_ram` maps that to `true`.

**Consequence worth knowing: the conditional write ALWAYS succeeds under
`exec`, so the `Ok false -> internal_error` arm of `update_and_write_pte` is
unreachable by this interpreter.**  Not a defect -- the limit of what a test
in this suite can probe.

### OPEN DECISION (finding 22): which machine is the model claiming to be?

Every other row is the model being NARROWER than the hardware.  Finding 22 is
the reverse: the model implements CSRs that QEMU's default rv64 virt CPU
answers with an illegal-instruction trap.  Under this suite's premise --
QEMU-virt is the reference hardware -- the hardware's TRAP then has no model
execution, which is the unsound direction.

But it may not be a bug at all: it may just mean the model is configured for a
different machine than `-cpu rv64` gives us (`sail-config-rv64d.json` decides
which extensions exist).  The same axis produces finding 19 in the opposite
direction -- QEMU has H and the model does not.

**This needs a decision that is not the suite's to make: WHICH machine is the
model claiming to be?**  If it is QEMU's virt board, findings 19 and 22 are
both real gaps and the config should be reconciled.  If it is a machine with a
different extension set, the QEMU command line should be pinned to match
(e.g. `-cpu rv64,h=false,smstateen=on`) and both rows become configuration
notes rather than findings.  Until that is settled they are recorded, not
classified.

### Finding 21, and what it costs

`model-xv6iris/sail-modules.txt` includes `FD_core` -- the registers, `fcsr`,
and the CSR plumbing -- but no F/D INSTRUCTION modules, so the decoder has no
floating-point instructions at all while `misa` bits 3 and 5 promise them.
`fsd ft0,8(s11)` takes an illegal-instruction trap with `mstatus.FS` correctly
set to Initial first, so FS is not the cause.  The fix is a one-liner either
way: add the modules, or set F/D `supported: false` in the config so `misa`
stops promising them.

### Making a race actually race (the TB warm-up trap)

QEMU's FIRST execution of a basic block costs thousands of guest instructions'
worth of wall time in `tb_gen_code`, so a plain rendezvous does not make two
harts overlap -- whichever is still in the translator loses before it starts.
Measured: a 16-round lost-update loop came out at 32 in **60 runs of 60**, and
2048 rounds each was still 0 lost in 25 runs.

The fix, used by all three racing tests: a **two-pass structure**.  Both harts
run the whole hot path once on PRIVATE words, leaving every block in QEMU's
shared TB cache, then rendezvous, then race.  With that, two rounds each is
enough.  `conc_sb` additionally gives the harts delay loops of different
lengths to trim hart 0's systematic head start, which raised (0,0) from 1.3%
to 4.6% of runs.

Only store->load reordering appears on an x86-64 host, which is what TSO under
MTTCG can expose.  Message-passing and load-buffering tests would be
guaranteed single-outcome here and are worth adding only if this suite is ever
run on an aarch64 host.

### Capturing a nondeterministic test

Because QEMU has more than one legal execution here, `disk_order` is captured as
a SET.  A `vtest:` directive in the `.S` names the repeat count and the
backend configurations to union over:

```
/* vtest: repeat=20 drives=cache=writeback;cache=none,aio=threads */
```

No single configuration reliably shows both orders, so a test about
nondeterminism names the ones that between them exhibit its executions;
without that, `make vtest-gen` is itself flaky.  The generated file then
carries `<name>_qemu_results : list (list Z)` alongside the single
`<name>_qemu_result`.

## What the suite has CONFIRMED

Positive results are worth recording too -- each is a way the model could
have been wrong and is not.

- **The request protocol** (`disk_rw`): both status bytes, both used-ring ids, the
  used index, the interrupt status, and the 512 bytes DMA'd in each
  direction.
- **The disk image** (`disk_rw`, `disk_order`, `disk_intr`): QEMU has flushed a completed write to the
  backing file by the time its process exits, so the raw-file diff is a sound
  channel -- and the model's `v_disk` agrees with it byte for byte, including
  on a multi-sector (8-sector) request.
- **The UART transmit path end to end** (`uart_tx`, `uart_dlab`, `uart_regs`):
  `uart_write` at offset 0 -> `uart_tx_pop` -> `uart_acc` is exactly the byte
  sequence the host received, in order, nothing lost or duplicated; `uart_lsr`
  is `0x60` with the FIFO empty at every point either machine can be asked,
  including one instruction after a THR store, and LSR reads are pure.
- **The DLAB divisor-latch aliasing** (`uart_dlab`), which is what the whole
  `un_dlab` ghost in `design/device.md` exists for: LCR bit 7's polarity,
  offset 0 aliasing to DLL and offset 1 to DLM, IER unaffected by a DLM
  store, the aliasing not sticky, and a byte written to offset 0 with DLAB
  set NOT reaching the wire.
- **PLIC arbitration, both clauses** (`plic_arb` + `plic_tie`): with the disk
  at priority 3 and the UART at 7 the claim returns the HIGHER id 10 over the
  pending, enabled id 1 -- ids are scanned in order, so only the priority
  comparison explains it -- and the same program with equal priorities
  reverses the order to 1-then-10.  The pair pins both clauses of
  `plic_better`; either alone is passed by a half-wrong implementation, and
  QEMU breaks ties the same way.
- **The rest of the controller** (`plic_thresh`, `plic_mask`, `plic_level`):
  the threshold gates the NOTIFICATION strictly and in both directions (equal
  is masked, and the pin follows down and back up); the enable bit is not the
  gateway (a disabled source still latches, is not claimable, and becomes
  claimable when the bit is set later with no new device edge); a claim clears
  that source's pending bit and no other and marks it claimed, and neither
  source re-latches while claimed; `plic_complete` touches `p_claimed` only;
  claiming with nothing pending returns 0 and disturbs nothing; the pending
  word carries two bits (`0x402`), which `plic_pending_word`'s fold had never
  been exercised past one; and pending is sticky across the source going quiet.
- **The two-device interrupt fabric**: the UART raises PLIC source 10 with no
  serial input at all (IER bit 1, empty FIFO), and `dev_irq_level`'s
  two-source dispatch agrees with the machine.
- **The UART raises BOTH interrupts, all the way into `mip`** (`uart_irq_tx`,
  `uart_irq_rx`): IER bit clear -> nothing pending; bit set -> the line goes
  high -> the gateway latches source **10** -> the wire sets `mip` bit 9; the
  ISR names the cause (2 = THRE, 4 = rx available); the S-context claim hands
  back 10; the condition removed and completed -> pending and SEIP clear.
  Identical on both machines at every step of both chains.  This is the first
  test to raise source 10 at all, so it is the first evidence that the UART is
  wired to the controller AND to the right source.  It also BOUNDS finding 8:
  after QEMU's ISR read drops the line, QEMU still reports source 10 pending
  and SEIP set, because the gateway holds a forwarded request until it is
  claimed -- and `plic_latch` does the same -- so the model's level treatment
  of THRE costs no extra PLIC-visible interrupt on this path.  Only the
  TRANSMIT condition has the wrong edge; the receive interrupt is a level on
  real hardware too.
- **The virtio RESET command** (`disk_ident`), never exercised before: Status
  -> 0, `QueueReady` -> 0 without the driver clearing it, ISR -> 0, and the
  offered features untouched.  `virtio_reset` keeping only `v_disk` is what
  the hardware does.
- **The error paths** (`disk_err`): an unrecognised request type is an ANSWER,
  not a silence -- status 2 (UNSUPP) and a used-ring slot, with zero data
  movement on both channels and the disk unchanged; and a `FLUSH` from a
  driver that DECLINED `VIRTIO_BLK_F_FLUSH` still completes OK on QEMU, so the
  model's unconditional recognition of type 4 is faithful.  The ISR is a bit
  and not a count: still 1 after three completions.
- **Per-queue READS at a queue that does not exist** (`disk_ident`): both
  answer 0.  A driver may LOOK at queue 1; it may not TOUCH it.
- **The whole S-mode CSR file, the whole PMP file, and the whole HPM file**
  (`core_regs_scsr`, `core_regs_pmp`, `core_regs_hpm`) agree byte for byte
  over the entire result region.  None is vacuous: `sstatus` is derived
  through the model's `lower_mstatus` window onto the board-written `mstatus`;
  `satp = 0` is what makes "translation is off until `start()` turns it on"
  true OF THE MACHINE; and `ArchReset.v` says pmpcfg is explicitly NOT a board
  obligation -- the spec's own `reset_pmp` establishes `pmp_all_off` over
  arbitrary garbage -- so those sixteen zero entries are produced by the
  model's reset CODE, and this is the check that the code's answer is the
  machine's answer.  The HPM test also exercises a permission path: an M-mode
  read of the UNPRIVILEGED alias with `mcounteren = 0` must succeed, because
  `mcounteren` gates S and U and not M, and the model does not wrongly refuse.
- **`mstatus = 0xA00000000`** (`core_regs_mcsr`): `ArchReset.board_regs`'
  power-on obligation for mstatus -- SXL = UXL = 2 and everything else clear,
  the part `reset_sys` does NOT establish -- is a true statement about this
  board.
- **`mip` and `tselect` are WITNESSED, not findings** (`core_regs_mcsr`): the
  model admits QEMU's values from a legal power-on file.  `tselect` is the
  instructive one -- `read_CSR 0x7A0` returns `not_vec tselect`, the
  architecture's "no trigger selectable" stub, so the default's all-ones
  readback is just `init_regstate`'s zero complemented; preset the register to
  all-ones and the read gives QEMU's 0.  This is exactly the case a raw diff
  would have mis-reported as a divergence.
- **The UART receive datapath** (`uart_rx`), ten of eleven observations
  exact: bytes come out IN ORDER (`u_rx` really is a FIFO -- a LIFO or a
  one-deep register gives a different answer here); RHR pops EXACTLY one byte
  per read, established without a race by reading three of a four-byte queue
  and finding the fourth still there; LSR bit 0 tracks the FIFO across the
  whole sequence and is not sticky in either direction; and FCR bit 1 clears
  the receive FIFO -- a live `uart_write` arm no test had touched on the rx
  side, and what `uartinit` writes at boot.
- **Instruction-granularity interleaving** (`conc_lost`): a lost-update race
  produces exactly three outcomes (4, 2 and 3 over two rounds) and the model
  has a schedule for each, floor included.  It also pins that the UNSCHEDULED
  round-robin run is the maximally-colliding one, which is the concrete reason
  a race test must NAME its interleaving rather than let the harness pick.
- **Sub-word store granularity under concurrent access** (`conc_byte`): two
  harts holding a loaded byte while the other stores an adjacent byte of the
  same word, three rounds, nothing lost -- the same shape that DOES lose an
  update in `conc_lost` when the byte is shared.
- **`amoadd.w`** (`conc_amo`) computes the right read-modify-write and both
  machines answer 8.  The atomicity claim is deliberately weak and the file
  says so: `CCpu` is instruction-granular, so no schedule here could split an
  AMO in the first place.
- **S-mode with paging on, end to end** (`pt_ident`): the PMP TOR grant that
  S-mode cannot run without, the `satp` write and `sfence.vma`, `mret` to
  Supervisor, a level-2 leaf taking 30 offset bits, and FETCH through
  translation as well as load and store.
- **The A/D write-back arm against real hardware** (`pt_adu`), for the first
  time -- both the A case and the D case, checked by reading the PTE word back
  out of the page-table page: `0x07 -> 0x47` and `0x47 -> 0xC7`, upper 54 bits
  identical, i.e. the write-back rewrote exactly the flag bits to the same
  word the hardware wrote.  And **the Svade arm** (`pt_ade`): the model
  refuses exactly where the hardware refuses, and writes nothing.
- **The fault matrix** (`pt_fault`): five refusals and one grant, with
  `scause`, `sepc` AND `stval` identical in all five.  `stval` carries the
  faulting VIRTUAL address including the sub-page byte offset -- a model
  reporting the page-aligned VA, the PA, or the PTE address would fail here --
  and the instruction-fetch case attributes `sepc` to the unmapped VA itself,
  not to the `jalr`.  `sstatus.SUM` gates the identical U-page load in both
  directions on both machines.
- **The walk really descends** (`pt_levels`): a three-level walk to a 4 KB
  leaf, and a level-1 megapage whose 21-bit offset is checked by a store 1 MB
  in landing where it should.
- **Two checks a translation model could quietly have omitted and did not**:
  the reserved leaf encoding R=0/W=1 (`pt_resv`) and the misaligned superpage
  (`pt_super`).  Each has a control mapping built from the same PPN that
  works, so the fault is attributable to the CHECK and not to the table.
- **`medeleg` bits 12/13/15**: the M-mode backstop never fired in any of the
  nine images, and `sfence.vma` flushes totally on both machines.
- **The whole interrupt path** (`disk_intr`): the device raising its line, the PLIC
  gateway latching source 1, the wire driving hart 0's `sig_seip` (visible in
  `mip`), the S-context claim returning the source and clearing pending, the
  device acknowledgement dropping the line, and the PLIC complete clearing
  the claim.  All twelve observations identical.  In particular the model's
  deliberate PROPAGATION DELAY -- the gateway latch and the wire are separate
  steps, not side effects of the completing MMIO write -- is faithful: the
  test spins on the pending bit rather than reading it once, so it would
  still pass if the delay were longer and would fail if the model had quietly
  made the pin synchronous.
