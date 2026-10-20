# Weak-memory bugs in xv6 (found by the RVWMO allocproc effort)

Owner request 2026-10-20 ([OWN.127]): keep a list of the weak-memory bugs found in xv6. Each entry: where, what
RVWMO (riscv.cat) + the RISC-V PMAs allow, why it matters, the fix, and how the theorem treats it.

## 1. `virtio_disk_init`: queue zeroing not ordered before the device goes live (REAL under RVWMO; not benign)

* **Where.** `kernel/virtio_disk.c`, `virtio_disk_init`: `memset(disk.desc, 0, PGSIZE)`, `memset(disk.avail, 0,
  PGSIZE)`, `memset(disk.used, 0, PGSIZE)` (image `virtio_disk_init+0xf0/+0x102/+0x10c`), then the MMIO stores
  `QUEUE_READY = 1` (`+0x14a`) and `STATUS |= DRIVER_OK` (`+0x170`) — with no fence in between (and none since
  `kalloc`'s junk fill `memset(5)`, which follows its `release`).
* **What RVWMO + PMAs allow.** A RAM store and a later MMIO store of the same hart are not ordered without a fence
  with `w` in the predecessor and `o` in the successor set (`fence w,o`, or `fence iorw,iorw` = `__sync_synchronize()`).
  So the device may observe `DRIVER_OK` while the zeroing stores are still in hart 0's store buffer.
* **Why it matters.** The pages come from `kalloc` (junk-filled). A virtio device that polls the avail ring once the
  queue is live (the virtio spec permits polling) can read the pre-zeroing `avail->idx` (e.g. `0x0505`), see it
  differ from its own last-seen index 0, and pop a garbage descriptor chain → a DMA to/from junk addresses.
  Not observable on QEMU (TCG executes harts sequentially; virtio-mmio processes only on `QUEUE_NOTIFY`, and xv6
  fences before every notify). Linux's `writel` / `virtio_wmb` contain exactly the missing barrier.
* **Fix (not applied).** `__sync_synchronize();` after the three `memset`s (before `QUEUE_READY`/`DRIVER_OK`).
* **In the theorem.** [OWN.127]: kernel unchanged; a NAMED header assumption scoped to this code path only ("hart 0's
  three zeroing `memset`s in `virtio_disk_init` have landed before the device's first DMA read after `DRIVER_OK`").
  Found 2026-10-20 by the route-P switch worker (finding F-11.5, `../xv6iris-weak-w1/PROGRESS-W11F.md` §11).
  Previously masked at the execution-graph level by the trusted ordering arm (R1) of `ioResidueGmo`
  ("a RAM access po-before an I/O event is gmo-before it", STRONGER than RVWMO + PMAs).

## 2. Benign data races (C11 UB, harmless on RISC-V; proved harmless in the theorem)

Recorded in `claude-notes/kernel-defects.md` ("Benign but load-bearing"):
* (a) `acquire` → `holding()` reads `lk->locked` / `lk->cpu` without the lock (`holding+0x0`, `holding+0x12`) — the
  `holding+0x12` read is an exempt read in the replay ([OWN.124], REVISIT-flagged).
* (b) `ilock` / `iunlock` read `ip->ref` without `itable.lock` (`ilock+0xe`, `iunlock+0x1c`) — exempt reads [OWN.112].
