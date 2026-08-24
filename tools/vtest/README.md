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
- No dependence on `a0`/`a1`.  QEMU's `-kernel` passes hartid and a device-tree
  pointer; the model's reset register file does not.
- No LR/SC: `exec` treats the reservation outcomes as stuck.
- `-smp 1`.  The model has 8 harts, but a schedule that only ever steps hart 0
  is a legal execution, so this costs nothing.
- The QEMU command line is fixed by `vtest.py`, and
  `-global virtio-mmio.force-legacy=false` is part of it: without that flag
  QEMU presents a LEGACY virtio-mmio device (Version reads 1, not 2) and every
  register test disagrees for the wrong reason.

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
| 1 | `QueueNumMax`, and `QueueNum` writes | 8, only {1,2,4,8} accepted | 1024 | incompleteness | `disk_rw` |
| 2 | offered / negotiated features | `FLUSH\|CONFIG_WCE`, negotiates 0 | `0x30006e54`, negotiates `0x6454` | incompleteness | `disk_rw` |
| 3 | `DeviceFeaturesSel` (0x14), `DriverFeaturesSel` (0x24) | not decoded -- the store is STUCK | writable | incompleteness | not yet covered |
| 4 | **`used.ring[i].len`** | `vr_len` (the data descriptor's length) in both directions | 1 for a write, 513 for a read | **defect** | `disk_rw`, `disk_order` |
| 5 | **completion ORDER of two in-flight requests** | publication order ONLY | either order | **unsoundness** | `disk_order` |

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
