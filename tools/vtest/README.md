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
    vtest_status.py    which tests passed, per area (CI's reporter)
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
                       (no QEMU, no toolchain), stopping at the first red test
    make vtest-check-ci  the same captures, but compile EVERY test (-k) and
                       report the per-test result -- this is what CI runs,
                       on every push

`vtest-check` is deliberately outside `make proofs`: a red test must not break
the proof build.  It needs only the ~20-file dependency cone of `RiscvExec` +
`DevModel`, not all of `iris/`.

### What CI does with a red test

`.github/workflows/ci.yml` runs `vtest-check-ci` after the proof build --
against the CHECKED-IN captures, so **CI never runs QEMU** and never looks for
new hardware behaviours; it re-checks that the executions already recorded
from real hardware are still executions the model ADMITS.

**Every test must pass, and a red one fails the job.**  There is no list of
expected reds and no need for one: a known divergence is pinned on BOTH sides
and proved unequal (see [Recording a divergence](#recording-a-divergence)), so
it is green today and goes red exactly when the model moves.  All 56 pass, the
eleven open findings included -- the findings are theorems about the
disagreement, not failures.

What the step adds over a plain `vtest-check` is the REPORT: all 56 are
compiled (`-k`) before the verdict, so one red test does not hide the rest, and
`tools/vtest/vtest_status.py` writes the per-area table with each failure's
Rocq error into the run's step summary.  Its header has the rest, including why
a passing test is judged by its `.vo` and why the target deletes them first.

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
  flushes the receive path -- on BOTH machines now, `uart_write` offset 2
  implements it -- and the host's first byte is already in QEMU's holding
  register before the guest's first instruction runs, so an FCR FIFO-enable
  at the top of the program silently eats byte 1 (measured: reads `0x42`
  first, 8 runs of 8).  The model cannot reproduce the RACE, only the flush,
  which is why this is a rule for the test rather than a finding.  Relatedly, with the FIFOs off QEMU delivers one
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

Fifteen of these have been FIXED rather than recorded -- the whole UART
register file, its interrupt-status semantics and its bus decode; the PLIC's
threshold, its M contexts and its source count; and the virtio disk's register
decode, its queue sizes and its used-ring reporting.  They are in
[Findings fixed](#findings-fixed) below, with what the fix was and which test
now passes because of it; they are kept because the point of this table is the
register of what differential testing FOUND, not only of what is still open.

Classified as *incompleteness* (the model is stricter than the hardware, so
some real driver has no model execution -- cannot make a proof wrong, but
limits what can be verified) or *defect* (the model produces a value the
hardware never produces, so a proof that depends on it is about a device that
does not exist).

| # | what | model | QEMU | kind | found by |
|---|------|-------|------|------|----------|
| 2 | offered / negotiated features | `FLUSH\|CONFIG_WCE`, negotiates 0 | `0x30006e54`, negotiates `0x6454` | incompleteness | `disk_rw` |
| 17 | a descriptor chain that is not exactly THREE descriptors | the device STALLS (`virtio_stalled`); only `DevStepDiskWild` covers it | served normally -- 512 bytes written, status 0 | incompleteness in practice | `disk_chain` |
| 18 | **`a1` at entry** -- the device-tree pointer | `0x1000`, a HARDCODED constant in `rv64d.v`'s `init_boot_requirements` | the real DTB address (`0x87e00000`), which moves with `-m` and the image | **defect** (boot contract) | `core_regs_gpr` |
| 19 | `misa` bit 7 (H), and `mideleg` as its consequence | H absent; `mideleg` 0 | H present; `mideleg` `0x1444` (VSSIP/VSTIP/VSEIP/SGEIP, hardwired when H is implemented) | incompleteness | `core_regs_mcsr` |
| 20 | `menvcfg` bit 61 (ADUE) at POWER-ON | `0` (Svade), so an access needing A/D FAULTS | `0x2000...` (Svadu), so hardware writes the bit back | incompleteness, and a FALSE board assumption | `core_regs_mcsr`, `pt_ad` |
| 26 | **the model's TLB is DIRECT-MAPPED (64 entries, `tlb_hash` = the low 6 bits of the VPN)** | at a colliding VPN the entry is evicted by the very next fetch, so a PTE rewritten WITHOUT `sfence.vma` is re-walked and the NEW mapping is used | keeps the stale entry | unsound direction, but see below | `pt_tlb` |
| 21 | `misa` advertises F and D but the model has NO F/D instructions | `fsd` takes an illegal-instruction trap (`mcause` 2, `mtval` = the encoding) | executes | incompleteness + internal inconsistency | `core_regs_fpr` |
| 22 | CSRs the model implements that QEMU's default virt CPU REFUSES: `mseccfg`, `mstateen0`, `sstateen0`, `scountovf`, `mcyclecfg`, `minstretcfg`, `ssp` | implemented, read successfully | illegal instruction | **model is WIDER -- needs a ruling**, see below | `core_regs_mcsr` |
| 24 | **THE MEMORY MODEL: the model is sequentially consistent** | one shared `gmem`, a store is global the instant it retires -- (0,0) unreachable | store-buffering gives **(0,0) in a few percent of runs**, which RVWMO permits | **UNSOUNDNESS** | `conc_sb` |
| 25 | `sc.w` does not evaluate | `vm_compute` does not return (110 s+), so a test containing one cannot be COMPILED | executes | **out of scope: LR/SC is not supported** | `conc_amo` |

<a id="findings-fixed"></a>
## Findings fixed

**These are findings, not deleted rows.**  Each was a real difference between
the model and the machine and each is now a passing test rather than a pinned
divergence, but the register of what differential testing FOUND is the point
of this file, so they keep their numbers, their values and their original
classification.  All five were in the 16550 and they went together: half of
them are one modelling shortcut seen from different sides.

| # | what | the model USED to say | the machine -- and the model now | kind it was | pinned by |
|---|------|------------------------|-----------------------------------|-------------|-----------|
| 6 | UART MCR (4), MSR (6), SCRATCH (7) | `0` / `0` / `0`, and writes discarded | `3` / `0xb0` / `0x5a`: five bits of MCR **including LOOPBACK**, the port's modem inputs (MCR's outputs under LOOP), and a byte of storage | incompleteness | `uart_regs`, `uart_loop` |
| 7 | UART ISR bits 7:6 (FIFOs-enabled) | hardcoded set: `0xc1` at reset | `0x01` until FCR bit 0 enables the FIFOs, `0xc1` after | incompleteness | `uart_regs`, `uart_irq_tx`, `uart_irq_rx` |
| 8 | UART THRE interrupt: LEVEL or LATCH | a level -- the second ISR read still `0xc2` | second read `0xc1`: the read cleared it.  The latch `u_thri` arms when the transmitter falls idle, when an FCR write clears the tx FIFO, or when IER bit 1 is written while it is already idle | incompleteness | `uart_regs`, `uart_irq_tx` |
| 9 | UART access WIDTH | width 1 only -- a 4-byte read was STUCK | `0x00000008`: the bus NARROWS to the one byte register the address names (zero-extended out, low byte in), at 2, 4 and 8 bytes, and does NOT gather registers into a word | incompleteness | `uart_width` |
| 23 | RHR read on an EMPTY receive FIFO | `0` | the LAST byte received: the holding register is cleared neither by a read nor by an FCR clear, only the DR FLAG is -- and with the FIFOs ENABLED the machine answers `0`, which is the FIFO's output stage | incompleteness | `uart_rx`, `uart_dlab` |
| 10 | **PLIC claim ignores the context THRESHOLD** | the masked source's id, and its pending bit cleared | `0`, and the source STAYS pending.  The threshold now lives in `plic_cand`, which `plic_eip` and `plic_best` both read | **unsoundness** (and a defect) | `plic_thresh` |
| 11 | PLIC M-context registers (enable 0x2000, threshold 0x200000, claim 0x200004) | not decoded -- STUCK at the first M access | all three serviced: the PLIC is indexed by CONTEXT (`plic_nctx`, `plic_mctx`/`plic_sctx`), both halves of every hart's pair, and each context drives its own pin | incompleteness | `plic_mctx` |
| 12 | PLIC source 0's priority register, and `plic_nsrc` = 32 against the board's 96 | STUCK at both bounds | offset 0 is read-only zero (source 0 does not exist); 96 sources, so the enable and pending bitmaps are three words each | incompleteness | `plic_prio0` |
| 1 | `QueueNumMax`, and `QueueNum` writes | 8, and only {1,2,4,8} accepted | **1024**, and any power of two up to it.  An illegal size is still refused, which is deliberate | incompleteness | `disk_rw`, `disk_ident_qnum` |
| 3 | `DeviceFeaturesSel` (0x14), `DriverFeaturesSel` (0x24) | not decoded -- STUCK, so no feature bit above 31 could be read OR acked | both are real registers; word 1 carries `VIRTIO_F_VERSION_1`, the ack lands in the word the selector names, and a full 1.x negotiation reaches Status 11 | incompleteness | `disk_ident_featsel`, `disk_ident_drvfsel` |
| 4 | **`used.ring[i].len`** | `vr_len` -- the data descriptor's length -- in every direction | the device-WRITABLE part of the chain: 1 for a write, 513 for a read, and 513 for an unrecognised type on a read-shaped chain.  The discriminator is the descriptor's WRITE flag, not the request type | **defect** | `disk_rw`, `disk_order`, `disk_err` |
| 13 | virtio CONFIG SPACE: capacity (0x100), ConfigGeneration (0x0fc) | not decoded -- STUCK | the capacity is a field of the device state (`v_cap`), set by whoever attaches the image and kept across a reset; generation 0 | incompleteness | `disk_ident_cap`, `disk_ident_confgen` |
| 14 | virtio `QueueReset` (0x0c0) and the SHM registers (0x0ac..) | not decoded -- STUCK | `QueueReset` reads 0 (this device does not offer `RING_RESET`); every SHM region reads all-ones, which is how the transport says a region does not exist | incompleteness | `disk_ident_qreset`, `disk_ident_shmsel` |
| 15 | sub-word access anywhere in the virtio window | not decoded -- STUCK | the transport is 32-bit: a 1- or 2-byte read reaches no register and answers 0, and a narrow write is dropped | incompleteness | `disk_ident_rd1/rd2/wr1` |
| 16 | a per-queue write with `QueueSel` /= 0, and `QueueNotify` /= 0 | REFUSED -- STUCK | both accepted and ignored.  What kept the queue geometry legal was never the refusal but `virtio_live`'s own conditions | incompleteness | `disk_ident_qsel`, `disk_ident_notify` |
| 5 | **the completion ORDER of two in-flight requests** | publication order ONLY -- `virtio_req_step` read the chain at `v_seen` and handed back `v_seen + 1`, so no schedule could reorder | EITHER order, and the model now has both: the device POPS available-ring entries in order (`virtio_pop_step`, `v_inflight` = the popped heads) and completes ANY in-flight head (`virtio_req_step` takes the head), `VSched` picks which, and `DiskOrder.v` exhibits the two executions against the two captures.  The Iris driver proofs are ported to it (design/virtio-driver.md) | **UNSOUNDNESS**, RESOLVED | `disk_order` |

**Finding 10 was the serious one of the PLIC three**, and the only PLIC
finding that was not mere incompleteness: the threshold appeared in `plic_eip`
alone, so the model's NOTIFICATION and its CLAIM disagreed -- a source could be
invisible to a context and still be what that context's claim register handed
back, with its pending bit cleared on the way out.  The fix is not a special
case in the claim but a move: the threshold went into `plic_cand`, the one
predicate that says what a context can see, and `plic_eip` became
`existsb (plic_cand p c)` while `plic_best` folds the same thing.  The two
cannot disagree now because they are the same question asked twice ("is there
one?" versus "which one?"), which `PlicThresh.v` states off the model as well
as off the program.  It also subsumed the old `0 <? p_prio` guard -- a
priority-0 source cannot exceed a threshold of 0 -- so the model got smaller.

**Findings 11 and 12 were one change**: the PLIC stopped being indexed by hart.
It has CONTEXTS, the board wires two to each hart (M then S), and every
per-context register family -- enable bitmap, threshold, claim/complete -- is
now decoded for all of them, with `dev_meip` beside `dev_seip` and a second
wire arm in `RiscvLang.plic_step` so that an M context's notification reaches
its pin rather than being computed and dropped.  Decoding the registers while
leaving the pin unmodelled would have been the same half-fix as a
stored-but-inert control bit.  The source count went with it: 96 sources means
three enable words per context and three pending words, which is what makes
source 32's priority register (`plic_prio0` +20) a register at all.

**Finding 4 is the one that had to be got right rather than merely made.**
Two rules both explain "1 for a write, 513 for a read": key off the request
TYPE, or key off the data descriptor's WRITE flag.  `disk_err` is what
separates them -- an unrecognised type and a FLUSH, both published through a
read-shaped chain, where the device writes no data at all.  The spec's wording
("bytes WRITTEN into the device-writable part") says 1; the hardware says 513,
because what a real device reports is the writable SEGMENT and not the
transfer.  Keying off the type would have passed `disk_rw` and produced 1
there -- a value the machine does not produce, which is finding 4 itself moved
from the read path to the error paths.  So `vreq_used_len` reads `vr_wr`, the
flag the parser takes off the descriptor.

**Findings 3, 13, 14, 15 and 16 were all the same shape**: an access the
hardware answers and the model had no transition for, so a driver that made it
had no model execution.  Nothing about them was subtle once each register's
meaning was pinned; what they cost was reach, and the two that had real
drivers behind them are 15 (a narrow read of a status byte) and 16 (a driver
that touches a queue this device does not have).  Finding 13 needed one piece
of modelling rather than decode: `v_disk` is a total function, so the medium
has no edge of its own and the CAPACITY had to become a field of the device
state, set by the machine that attaches the image.

**Finding 6 was the load-bearing one of the UART five, and not because of the values.**  MCR
bit 4 is LOOPBACK, so a readable MCR that ignored bit 4 would have been worse
than the register that read as zero: a driver's self-test would have put its
byte on the WIRE, which is a thing the hardware never does -- turning an
incompleteness into a defect.  Making the register real meant making the mode
real.  `uart_tx_pop` has two arms, and `uart_state` carries `u_wire` (what
left on SOUT -- the console-observable trace, and what `VTest.serial_of`
compares) beside `u_out` (what the TRANSMITTER finished with, loopback
included), so that the transmitter-token argument in `WpUart.v`, stated on
`u_out ++ u_tx`, is untouched by where the byte went.  `uart_loop` checks the
whole of it against the machine, serial channel included: the loopbacked byte
comes back on RHR and the host sees only the byte sent after LOOP was cleared.

**What these fixes deliberately did NOT change**, each for the same reason --
the safe direction is the model producing MORE interrupts and accepting MORE
input than the machine, never fewer:

- the RECEIVE interrupt is a level on the hardware too, so `uart_rx_int` is
  what it always was (`uart_irq_rx` is the evidence);
- the ISR's receive condition triggers at ONE byte rather than at FCR's
  trigger level.  Modelling the trigger level without the character TIMEOUT
  interrupt would err toward FEWER interrupts, and one byte is the level xv6
  and every test here select anyway (FCR bits 7:6 clear);
- the model's rx FIFO is 16 deep in both FIFO modes, where the hardware has a
  one-byte holding register with the FIFOs off.  The model accepts more host
  input than the machine offers, and `uart_rx_push` REFUSES when full, which
  is the flow control QEMU's front end applies rather than an overrun.

Finding 4 is the one worth acting on.  The spec defines the used element's
`len` as the number of bytes written into the DEVICE-WRITABLE part of the
chain -- the status byte alone for a write request, the data buffer plus the
status byte for a read.  `VirtioModel.virtio_used_writes` writes the data
descriptor's length regardless of direction, which is a value no real device
produces.  Nothing in the tree has noticed because xv6's driver ignores the
field.  The fix needs the request TYPE at that point, so it is local; what
makes it a decision rather than a drive-by edit is that VirtioModel.v's
reverse-dependency closure is 1286 files.

**Finding 5 was the serious one, and it is RESOLVED.**  `disk_order`
publishes two write requests in one batch -- eight sectors at 100 and one
sector at 5 -- and records which descriptor id lands in which used-ring slot.
QEMU produces BOTH orders:

| `-drive` options | in order | reordered |
|---|---|---|
| `cache=writeback` (the default) | 19/25 | **6/25** |
| `cache=writeback,aio=threads` | 20/25 | **5/25** |
| `cache=none,aio=threads` | 3/25 | **22/25** |
| `cache=none,aio=native` | 0/25 | **25/25** |

The model used to have no execution for the second: `virtio_req_step` read
the chain at position `v_seen` and handed back `v_seen + 1`, so the served
order WAS the publication order.  That was the other direction from findings
1--3 -- the hardware having a behaviour the model had no transition for, so a
theorem proved against the model did not cover the machine -- and it was
live in xv6: `virtio_disk_intr` reads each used element's ID and wakes
`disk.info[id]` precisely because completions need not come back in order.

What the model does now (VirtioModel.v section 5b): the device POPS
available-ring entries strictly in order (`virtio_pop_step`; `v_seen` is the
pop index and `v_inflight` the set of popped, uncompleted descriptor HEADS)
and CAPTURES/COMPLETES any in-flight head (`virtio_capture_step` /
`virtio_req_step` take the head).  `VSched`'s eager schedules differ only
in which in-flight head they pick (`lowest_head` / `highest_head`), and
`DiskOrder.v` proves the model admits both captured orders
(`disk_order_admits_inorder`, `disk_order_admits_reordered`,
`disk_order_model_has_both`) plus the general facts `model_pops_in_order`
and `model_completes_any_inflight_head`.  The Iris side followed: the keyed
protocol serves any position (`vp_srv`, `vp_lo`, `vp_uix`), and the driver
proofs (`virtio_disk_rw`, `virtio_disk_intr`) are stated over a
per-descriptor receipt keyed by head -- claude-notes/design/virtio-driver.md
and claude-notes/completed/virtio-finding5-driver-port.md.

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

**IT IS FIXED IN THE DEVICE MODEL, AND THE DRIVER PORT IS IN PROGRESS.**  A
step now takes the available-ring position it answers as a parameter; the
device state carries a watermark plus the set of positions served out of turn,
and `v_taken` names the position whose payload is latched rather than being a
flag.  `DiskOrder.v` proves both of QEMU's captures are model executions --
same program, same start state, two schedules that differ only in which
outstanding request the device picks up.  The Iris driver proof is being
ported to the new protocol; `claude-notes/projects/device-conformance.md`
records exactly what is green, what is in progress, and the two design pieces
that remain.

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
  `uart_write` at offset 0 -> `uart_tx_pop` -> `u_wire` is exactly the byte
  sequence the host received, in order, nothing lost or duplicated; `uart_lsr`
  is `0x60` with the FIFO empty at every point either machine can be asked,
  including one instruction after a THR store, and LSR reads are pure.
- **The whole UART register file, read and written** (`uart_regs`,
  `uart_width`, `uart_loop`): all eight offsets, at all four access widths,
  in both directions -- see [Findings fixed](#findings-fixed), since every one
  of those rows is now a confirmation.  The two worth naming on their own are
  LOOPBACK (`uart_loop`: the transmitted byte comes back on RHR, the modem
  outputs come back on the modem inputs pin for pin, and the host sees
  nothing of it -- the serial channel is what proves the last part) and the
  ISR's LATCH (`uart_regs`, `uart_irq_tx`: two reads in a row differ, and the
  latch is armed by the IER write itself, so a transmitter that is already
  idle when the interrupt is enabled still interrupts).
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
  wired to the controller AND to the right source.  It also pins the GATEWAY against the ISR read: on
  both machines the read drops the UART's line and source 10 stays pending
  with SEIP still set, because the gateway holds a forwarded request until it
  is claimed -- `plic_latch` does the same.
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
- **The UART receive datapath** (`uart_rx`), every observation exact: bytes come out IN ORDER (`u_rx` really is a FIFO -- a LIFO or a
  one-deep register gives a different answer here); RHR pops EXACTLY one byte
  per read, established without a race by reading three of a four-byte queue
  and finding the fourth still there; LSR bit 0 tracks the FIFO across the
  whole sequence and is not sticky in either direction; and FCR bit 1 clears
  the receive FIFO -- a live `uart_write` arm no test had touched on the rx
  side, and what `uartinit` writes at boot -- while leaving the receive
  HOLDING register alone, which is what a read with DR clear hands back.
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
