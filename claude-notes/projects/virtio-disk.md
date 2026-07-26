# Project: the virtio disk device (VirtioModel.v / WpVirtio.v)

The device model behind `kernel/virtio_disk.c`. The MACHINE side is done and
proven: the disk exists as a third device on the fabric, it runs as part of the
device execution context, its DMA is modelled honestly, and `wp_dev_loop`
discharges the DMA step. What is left is the DRIVER side.

Read [`design/device.md`](../design/device.md) first — it describes the device
fabric this plugs into.

## What exists (done, in-tree, green)

- **`VirtioModel.v`** (iris-free) — the pure device: `virtio_cfg`/`virtio_state`,
  the 32-bit MMIO register decode (`virtio_read`/`virtio_write` + the
  `vio_readable`/`vio_writable` totality lemmas), the virtqueue reader
  (`read_desc`/`read_avail_idx`/`read_avail_ring`/`read_req`), the autonomous
  request step (`virtio_req_step` → `virtio_complete`), the byte-addressed disk
  image (`disk_read`/`disk_write`), the interrupt line (`virtio_irq`), and the
  DMA-footprint obligation `virtio_dma_ok` with its preservation kit.
- **`DevModel.v`** — `dev_state` carries `dvirtio`; `in_virtio` routes
  `[0x1000_1000, 0x1000_2000)` 4-byte accesses; `plic_latch` is now
  per-SOURCE and `dev_irq_level` says which device drives which source
  (UART = 10, disk = 1).
- **`RiscvLang.v`** — `dev_step` carries the byte memory and has a
  `DevStepDisk` constructor; the `DevLoop` branch of `prim_step` writes the
  memory back.
- **`RiscvExec.v`** — `wp_dev_step` hands the device thread `gen_heap_interp`
  instead of framing it.
- **`WpVirtio.v`** — the `virtio_auth`/`virtio_frag` halves, the DMA lease
  (`dma_own`/`virtio_lease`) with `dma_agree`/`dma_update`, and the device-thread
  rule `virtio_lease_step`.
- **`WpUart.v`** — `dev_inv_body` carries the virtio half, its lease and
  `virtio_isr_ok`; `wp_dev_loop` proves the DMA case.
- **`RiscvAdequacy.v`** — the virtio ghost is allocated and `riscv_device_adequacy`
  takes `virtio_live (v_cfg …) = false` (the queue is not live when the
  invariant is born, so the initial lease is empty) and
  `virtio_isr_ok (dvirtio …)`.

`virtio_isr_ok` is the disk's analogue of `plic_ok`: the interrupt-status
register holds only the two bits the spec defines. It rides in `dev_inv_body`,
is preserved by a completion (`virtio_req_step_isr_ok`), and is exactly what
makes `virtio_disk_intr`'s `0x3` acknowledgement provably drop the line
(`virtio_ack_clears`). Every device half in `dev_inv_body` now carries the pure
invariant its driver needs, which is the pattern to follow for a new device.

**§8 of `VirtioModel.v` is a CHECK on the model, not infrastructure.** It runs
xv6's own register sequence against it: `virtio_ident_reads` (the four identity
reads plus QUEUE_NUM_MAX pass the driver's checks), `virtio_reset_not_ready`,
`virtio_status_readback` (the FEATURES_OK re-read), and
`virtio_init_seq`/`virtio_init_seq_post`/`virtio_init_post_live` — the whole
`virtio_disk_init` write sequence is accepted and lands, by `reflexivity`, on a
concrete configuration the device will serve requests from. That is the cheap
way to catch a wrong offset or a mis-ordered status bit; extend it whenever the
modelled register set changes.

## The DMA-lease design (read this before touching the invariant)

The disk is the only BUS MASTER in the model, and that is the one thing that
makes it structurally different from the UART and the PLIC. Its step
*overwrites bytes of the harts' memory*, so at the Iris level the device thread
must OWN what it overwrites. The whole design follows from that:

- `virtio_lease v` (WpVirtio.v) is an existentially-quantified set of physical
  bytes `dma_own dma` plus a distinguished CONTROL sub-map `ctl ⊆ dma` (the
  descriptor table and the available ring — the bytes the device reads to
  decide *where* to write), plus the pure obligation
  `virtio_dma_ok (v_cfg v) ctl (dom dma)`.
- `virtio_dma_ok c ctl D` reads: *whatever the rest of memory says, and at any
  value of the dynamic device state, a step from configuration `c` writes only
  inside `D`, and never over `ctl`.* Both conjuncts are load-bearing:
  - `dom w ⊆ D` is what lets the device thread update the byte memory at all;
  - `dom w ## dom ctl` is what keeps the control region PINNED, which is in
    turn what makes the footprint a function of the configuration. Without it
    the obligation would not survive its own step.
- The obligation is stated over `virtio_cfg` — the driver-written half of the
  device state — and an autonomous step provably preserves it
  (`virtio_req_step_cfg` → `virtio_dma_ok_step`). So `virtio_lease_step` hands
  the lease back with **nothing re-proved**: the device thread never reasons
  about descriptor contents.
- The flip side, and the whole point: **only a driver's MMIO write can
  invalidate the lease**, and re-establishing it there is exactly the real
  obligation "the descriptors I published point into memory I have handed to
  the device". That is where the work is, and it is deliberately pushed there.
  `virtio_lease_cfg` + `virtio_write_cfg_stable` say the two steady-state
  writes (QUEUE_NOTIFY, INTERRUPT_ACK) are free.

The alternative designs were considered and rejected: quantifying
`virtio_dma_ok` over all memories makes the footprint unbounded (a descriptor
could say anything), and restricting `virtio_req_step` itself to a leased
region would be a modelling assumption that hides a real class of driver bug.

## Modelling choices, and why each is SAFE

Each of these ADDS device behaviours or is neutral, so a driver proof can only
get harder, never unsound. They are also all documented at the definitions.

- QUEUE_NOTIFY is a no-op: the device polls the available ring itself, so it
  may take a request as soon as it is published, before the notify store.
- A request completes ATOMICALLY (data + status + used element + used index in
  one transition). The index bump is what a driver waits on and is ordered last
  either way.
- DMA is not restricted to bytes already present in the byte memory; the lease
  is what bounds the device's reach.
- A malformed queue simply does not step. That costs LIVENESS only (a driver
  that builds a bad chain waits forever) and adds no unreachable state. It is
  the one deliberate weakness: a driver bug of that shape would not be caught.

## Remaining work (the driver side), in dependency order

1. **S-mode width-4 virtio MMIO leaves.** The virtio registers are all 32-bit,
   so this is the PLIC's shape, not the UART's byte shape: reuse the width-4
   S-mode device store/load infrastructure from the plic-init effort
   (`WpPlic.v`/`WpPlicExec.v`, see [`plic-init-spec.md`](plic-init-spec.md))
   with the address window swapped, plus the `kvmmake` virtio mapping
   (`virtio_vpn`/`virtio_ppn`, already in `KvmMap.v` — the kernel PT maps this
   page, so there is no tlb-invariant switch, exactly as for the UART; see
   `WpUartPutcSyncFull.v`).
2. **`virtio_disk_init`.** Run it against the RAW `virtio_frag`, pre-invariant,
   the way `wp_uartinit_sconf` runs against the raw `uart_frag` — it does a
   device RESET, and it is also where the queue becomes live, which is where the
   lease must be established. Note it calls `kalloc` three times and `memset`;
   the queue pages it allocates are what it must hand into the lease.
3. **The lease-transfer protocol on the driver side.** `virtio_disk_rw` gives
   the device a buffer (`b->data`, inside the static `bcache`) and takes it back
   at completion; `virtio_disk_intr` reads the used ring. Expect the used-ring
   page and the descriptor/avail pages to stay leased for the machine's whole
   life, and only the per-request buffer + status byte to move.
4. **`virtio_disk_intr`.** Needs the completion side of the interrupt chain
   (`virtio_irq → plic_latch … virtio_irq_id → plic_eip → s_dispatch_seip_fires`),
   which is the same pure chain WpUart.v already has for the UART — the latch is
   now per-source, so it should generalize rather than clone.
5. **A disk-contents spec.** Nothing yet says what a block device *is* from the
   file system's point of view. `disk_read_write` (VirtioModel.v) is the only
   fact so far. The natural statement is a `sector ↦ bytes` resource over
   `v_disk`, minted alongside the lease.
