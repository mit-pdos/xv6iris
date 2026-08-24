# Project: device conformance — the semantics, differentially tested against QEMU

## STATUS (2026-08-23)

The plumbing is LANDED and green (`make vtest`, ~33 s, four tests).  What it
has produced so far is **five divergences from real hardware, one of them an
unsoundness**, and three positive confirmations.  Nothing here changes the
model: this effort's output is a register of findings plus the machinery that
keeps producing them.

- `tools/vtest/` — the ABI, the test programs, the QEMU runner/generator.
  **Read [`tools/vtest/README.md`](../../tools/vtest/README.md) first**; it
  carries the naming scheme, the observation channels, the rules a test
  program must obey, and the FINDINGS TABLE (the authority — this file
  summarises, that file is maintained).
- `vtest-rocq/` — the model side: `VSched.v` (the executable device
  schedule), `VTest.v` (the harness), one `.v` per test.

**What is NOT done, in the order it is worth doing, is §5.**

## 1. What a test claims, and why it is cheap

The question is one-directional:

> is what the real hardware did an execution our model ALLOWS?

so a test only has to EXHIBIT one model execution matching what QEMU
produced.  Exhibiting one is a COMPUTATION, so **there is no WP, no invariant
and no Iris in `vtest-rocq/`** — a test is a `vm_cast_no_check`d equation
between a projection of the model's reached state and a literal captured from
QEMU.  This is what makes the effort affordable: measured ~8 ms per
instruction, and a whole 628-instruction disk round trip is ~20 s
kernel-checked.

It also means a test is **not restricted to what the driver proofs assume**.
No DMA lease, no `virtio_proto`, no `dev_inv`.  A test may configure the queue
illegally; the only question is whether the model has a run that matches.

## 2. Architecture, in one pass

- **One binary runs on both machines.** A bare-metal M-mode image linked at
  `0x80000000`, assembled from `tools/vtest/tests/<area>_<name>.S`.
- **Two observation channels**, and the serial console is deliberately not
  one of them (printing a result costs ~10 instructions per character and the
  model executes every one; the same observations through memory are ~40× 
  cheaper):
  1. the RESULT region, read from QEMU over QMP `xp` (4 KB in ~2 ms;
     `pmemsave` mis-parses its filename argument in QEMU 10.2) and from the
     model out of `gmem`;
  2. the DISK IMAGE, byte-diffed per 512-byte sector against the raw `-drive`
     file after the process exits, and read from the model through
     `disk_read` over `v_disk`.
- **The declared-regions rule is load-bearing.** The model's memory is a
  FINITE `gmap`, so an access outside the regions of `abi.h` is STUCK.  That
  is a feature: on QEMU such an access silently reads a zero and the
  difference would go unnoticed.
- **The schedule is the witness.** `VSched.sitem` has one constructor per arm
  of `uart_step`/`disk_step`/`plic_step` plus the CPU, and `sapply` computes
  the successor.  `settle` is the eager default (every enabled device action
  after every instruction); a test that is ABOUT interleaving writes an
  explicit `sitem` list, which then documents what the test is about.
- **Nondeterministic tests are captured as a SET.** A `vtest:` directive in
  the `.S` names a repeat count and the backend configurations to union over.
  Necessary, not cosmetic: no single `-drive` configuration reliably shows
  both completion orders, so without it `make vtest-gen` is itself flaky.

Build targets: `make vtest-deps` (the ~14-file cone this needs — NOT all of
`iris/`), `make vtest-gen` (re-run QEMU), `make vtest-check` (model against
the checked-in captures; no QEMU, no toolchain — the CI target).
Deliberately outside `make proofs`: a red device test is a finding, and must
not break the proof build.

## 3. The findings

Full table with values in `tools/vtest/README.md`.  Classified as
*incompleteness* (the model is stricter than the hardware — limits which
drivers can be verified, cannot make a proof wrong) or worse.

| # | what | kind |
|---|------|------|
| 1 | `QueueNumMax` is 8 and `QueueNum` accepts only {1,2,4,8}; QEMU offers 1024 | incompleteness |
| 2 | the device offers only `FLUSH\|CONFIG_WCE`, so negotiation lands on 0 where QEMU lands on `0x6454` | incompleteness |
| 3 | `DeviceFeaturesSel` (0x14) / `DriverFeaturesSel` (0x24) are not decoded — the store is STUCK, so `VIRTIO_F_VERSION_1` can neither be read nor acked | incompleteness |
| 4 | `used.ring[i].len` is the DATA descriptor's length in both directions; the spec and QEMU say 1 for a write, 513 for a read | **defect** |
| 5 | **completion ORDER: the model serves the available ring strictly at `v_seen`, so the used ring can only come out in publication order; QEMU produces either order** | **UNSOUNDNESS** |

### Finding 5 is the one that matters

`disk_order` publishes two write requests in one batch — eight sectors at 100
and one at 5 — and records which descriptor id lands in which used slot.  QEMU
gives both orders, and how often depends only on the backend (6/25 reordered
with the default `cache=writeback`, 25/25 with `cache=none,aio=native`).

The model has no execution for the reordered one, and that is a fact about
the device, not about the test's schedule: `DiskOrder.model_serves_head_only`
proves `virtio_req_step` reads the chain at `v_seen` and returns a state whose
`v_seen` is one greater, so the served order IS the publication order and no
`sitem` list can change it.

**It is live in xv6, not hypothetical.** `virtio_disk_rw` sleeps with its
request outstanding, so up to `NUM` = 8 can be in flight; and
`virtio_disk_intr` walks the used ring reading each element's ID and waking
`disk.info[id]` — written that way precisely because completions need not come
back in order.  Under this model that code is only ever exercised on the
in-order case, so the reason it reads the id at all is never tested by the
proof.

**The fix is not local**, which is why it is recorded rather than made.  The
device would have to serve any published-but-unserved position rather than
`v_seen` alone: `v_seen : bv 16` becomes a set of outstanding positions,
`virtio_pending` and the completion gate move with it, and `VirtioQueue`'s
slot protocol and the DMA lease's reachable-window argument
(`virtio_queue_ok`'s `S`, closed under advancing by one until it reaches
`ai`) are stated against exactly the assumption this breaks.  See
[`completed/virtio-disk.md`](../completed/virtio-disk.md) and
[`design/virtio-driver.md`](../design/virtio-driver.md).

Finding 4's fix IS local — `virtio_used_writes` needs the request type to
choose between `1` and `vr_len r + 1` — but it still moves a definition in
`VirtioModel.v`, whose reverse-dependency closure is **1286 files** (942 of
them built at the time of writing).  Both fixes want to be made together, once.

## 4. What the suite has CONFIRMED

Positive results are worth as much, and each is a way the model could have
been wrong and is not.

- **The request protocol** (`disk_rw`): both status bytes, both used-ring
  ids, the used index, the interrupt status, the 512 bytes DMA'd in each
  direction.
- **The disk image** (`disk_rw`, `disk_order`, `disk_intr`): the model's
  `v_disk` agrees byte for byte, including on a multi-sector request.  QEMU
  has flushed a completed write to the backing file by process exit, so the
  raw-file diff is a sound channel.
- **The whole interrupt path** (`disk_intr`): line raised, gateway latched,
  wire onto `sig_seip` (visible in `mip`), S-context claim, device ack, PLIC
  complete.  All twelve observations identical.  In particular the model's
  deliberate PROPAGATION DELAY — the latch and the wire are separate steps,
  not side effects of the completing MMIO write — is faithful: the test spins
  on the pending bit rather than reading it once, so it would still pass if
  the delay were longer and would FAIL if the model had made the pin
  synchronous.

## 5. WHAT IS LEFT, in the order it is worth doing

1. **`disk_ident` — the stuck matrix.** The cheapest remaining findings, and
   the one place the register set is systematically wrong rather than
   incidentally.  Config space at offset `0x100` is not decoded, so **a
   driver that asks the disk its capacity gets a STUCK machine**; likewise
   `ConfigGeneration`, `QueueReset`, `SHMSel`, 1- and 2-byte accesses to the
   window, `QueueNum` outside {1,2,4,8}, `QueueSel` /= 0.  Each stuck point is
   a driver the system cannot describe; the test turns that from a comment
   into a scoreboard.  Finding 3 has no landed test yet and belongs here.

2. **`disk_err` — the error paths.** An unrecognised request type must
   complete with `UNSUPP` (2) and no transfer; a `VIRTIO_BLK_T_FLUSH` (4)
   with the cache empty must complete OK.  Neither has ever been run.

3. **`disk_chain` — chains that are not exactly three descriptors.** The
   model serves only the 3-descriptor shape; anything else leaves it
   `virtio_stalled`, which ENABLES `DevStepDiskWild` — the model may then
   write anything anywhere.  So the model can match QEMU here, but only
   through the wild arm, with the write set taken from the capture.  Worth
   doing because it is the one test that demonstrates the "model UB as
   anything, never as nothing" design actually paying off.

4. **`uart_*`** — the 16550 half of `DevModel.v`: the transmit FIFO and its
   depth-16 drop-when-full behaviour, `LSR`/`THRE`, the `FCR` FIFO clear,
   the `DLAB` divisor-latch aliasing of offset 0 (which the ghost design in
   [`design/device.md`](../design/device.md) leans on), and the rx path.
   `VSched` already has `SUartTx`/`SUartRx`.

5. **`plic_*`** — the controller as SUBJECT rather than as the disk's
   plumbing: two sources competing, priorities, a threshold that masks one,
   a claim while another is pending, `plic_complete` of a source that was
   never claimed.  `disk_intr` only ever exercises one source at priority 1
   with threshold 0.

6. **`core_*`** — the CPU and shared memory: the RAM path at each width,
   misaligned accesses, and (once more than one hart is scheduled) the
   reservation/self-loop arms of `mnode_step`, which no test reaches because
   `exec` treats the reservation outcomes as stuck.  Note the current
   harness always steps `riscv_step false`, so nothing exercises the clock
   tick — `disk_intr` has to mask `mip` down to `SEIP` for exactly that
   reason.

7. **THE SOUNDNESS BRIDGE (`EStep.v` + `sapply_sound`).** Until this lands, a
   green test is a fact about the model as `exec` and `VSched`'s step
   functions compute it — which does exercise `DevModel`/`VirtioModel`
   directly, since `exec` calls them itself — and NOT yet a fact about
   `RiscvLang.prim_step`.  Two pieces:
   - `enode : M unit -> mstate -> option (M unit * mstate)` with
     `enode_sound : enode m s = Some (m',s') -> mstep1 (m,s) (m',s')`.  This
     is precisely the converse [`HartBlock.v`](../../iris/HartBlock.v)'s
     header defers to "the language's own functional interpreter (the
     reflective stepper)", so it retires a stated gap in the tree.
   - `sapply_sound` — one small lemma per `prim_step` arm, each a two-line
     constructor application.  `VSched.view_of_ok` already discharges
     `DevStepDisk`'s existential bus view.
   With both, every test is restated as
   `∃ ts g, rtc erased_step (init, g0) (ts, g) ∧ obs g = qemu_obs`
   without changing a single test.

8. **Fixes 4 and 5**, together, once someone is willing to spend the 1286-file
   rebuild.

## 6. Measured costs and traps

- **Building the byte map dominates a test, not running it.** Every declared
  byte is a `gmap` insert on a 64-bit key.  `core_smoke` is 29 instructions:
  24,696 declared bytes took 20 s, 8,264 takes 8 s.  Declare the regions you
  use and no more (`start` vs `start_dma`).
- `vm_cast_no_check`, never `vm_compute; reflexivity` — the latter evaluates
  twice.  Measured 23 s versus 44 s on the same test.
- **`native_compute` is not usable on this development.**  Measured, then
  abandoned: `rocq native-precompile` handles the Sail model
  (`rv64d_types` 131 s / 5.8 GB, `rv64d` 50 s) but the two kinds of file this
  tree is MADE of both defeat it — the literal image dumps (`KernelInstrs`:
  `ocamlopt` still running after 10 minutes) and the `vm_compute`d concrete
  states (`ColdBoot`: 350 s and 16.7 GB, then a stack overflow).  `ColdBoot`
  is not optional; the harness's initial register file IS `cold_regs`.
- `objcopy -O binary` pads from address 0 and produces a 2 GB file for an
  image linked at `0x80000000`; use `-j .text`.
- QEMU defaults to LEGACY virtio-mmio (Version reads 1).
  `-global virtio-mmio.force-legacy=false` is part of the fixed command line.
- A QEMU process that outlives its test holds the disk image's write lock and
  the next run dies with "Failed to get write lock"; the runner quits it in a
  `finally`.
