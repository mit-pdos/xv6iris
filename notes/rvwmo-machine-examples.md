# RVWMO vs. the proof machine: reference examples

Concrete hart-level examples of places where the proof machine `MachCSL` and RVWMO disagree. Each one is recorded
so that it can be pointed to by name from rulings, plans and theorem documentation.

---

## EX-FENCEI-1: `fence.i` on the return to user mode is not a data fence (recorded 2026-10-21)

**One line.** In xv6's return to user mode, RVWMO + Zifencei let the user's first data load be satisfied *before* the
kernel's last trapframe store becomes visible to other harts. `MachCSL` forbids this today, because its `fence.i` drains
the hart's store buffer; [OWN.143] (2026-10-21) makes `fence.i` non-draining, which will remove the difference.

### The xv6 code (hart A)

| step | source | what it does |
|---|---|---|
| 1 | `kernel/trap.c:124` (`usertrapret`) | `p->trapframe->kernel_hartid = r_tp();`: a plain `sd` to the trapframe page |
| 2 | `kernel/trap.c` (rest of `usertrapret`) | `w_sstatus`, `w_sepc`, jump to the trampoline: CSR writes, no memory fence |
| 3 | `kernel/trampoline.S:107` (`userret`), image `0x8000609c` (`Xv6/KernelImage.lean:17614-17615`) | `fence.i` |
| 4 | `kernel/trampoline.S:110-112` | `sfence.vma; csrw satp; sfence.vma`: page-table fences, which do not order explicit loads and stores |
| 5 | rest of `userret` | restores user registers from the trapframe (own-hart loads), then `sret` |
| 6 | first user instruction | `ld y`: a data load of a word `y` that hart B is writing |

Hart B, concurrently: `sd y` and then a load of hart A's trapframe word (or any chain that makes B observe step 1).

### What the spec says

* **Zifencei.** `fence.i` makes the hart's earlier stores visible to its own *later instruction fetches*. It says nothing
  about data loads, and nothing about other harts.
* **RVWMO / riscv.cat.** There is no `fence.i` event at all, so `fence.i` contributes no preserved-program-order edge
  between step 1 (a store) and step 6 (a load).
* **Privileged spec.** `sfence.vma` orders only the hart's implicit page-table accesses, not explicit loads and stores.
  `sret` and the CSR writes are not memory fences.
* **Consequence.** The store→load pair (step 1, step 6) is unordered. RVWMO allows the classic store-buffering ("SB")
  outcome: hart A's load of `y` reads the old value while hart B's load still misses hart A's trapframe store. In
  store-buffer terms, step 1 is still sitting in hart A's buffer when step 6 executes.

### What the machine does

* `MachCSL/TsoMem.lean:863` `fenceDrainsSb`: a `fence.i` (`fenceIfetch`) must find the hart's store buffer EMPTY.
* `MachCSL/Lang.lean:1395` (barrier arm of `evStep`): `fenceDrainsSb b = true → σ.sb cpu = []`.
* So in `MachCSL` step 1 has always landed before step 6, and the outcome above is impossible.
* The machine is **STRONGER** than RVWMO here (today; see the ruling below).
* `notes/weak-allocproc-routeP-design.md:161` (the Zifencei row) used to mark the drain FAITHFUL. Corrected 2026-10-21
  (`notes/rvwmo-spec-audit.md` §4 item 1) to "STRONGER today; being aligned to Zifencei per [OWN.143]".

### Why it matters

* **Bridge obligation.** The bridge must show that every RVWMO execution of the image is a `MachCSL` run. Every machine
  strengthening is therefore a proof obligation: show it excludes no execution of this binary.
* **Where it bit.** Finding **F-6h-3 (i)** (2026-10-21, row 6h): a certificate for the own-hart user-fetch case needed
  "the stores before `fence.i` are ordered before a later own event". That holds in `MachCSL` but not in RVWMO.
* **Ruling [OWN.139].** Owner ruling (t3): prove faithfully, inside the graph, that no such cycle closes in xv6
  (≈ 2–4k, after P-W6). There is no scope premise and no stronger `fence.i` rule.
* **Fetch never forwards.** A related strengthening is that the fetch does not read the hart's own pending stores
  (`MachCSL/Lang.lean:1370-1372`, ifetch arm, reads landed memory only). Together with the drain, it underlies **F-6m-1**
  (`FetchProg`, row 6m).
* **RULED [OWN.143]: align now** (2026-10-21, Q-AUDIT-2 in `notes/rvwmo-spec-audit.md` §5; supersedes the Q-A2-2
  default of `~/dev/weak-orch/weakmach/proposal-A3.md` §7). `MachCSL`'s `fence.i` becomes NON-DRAINING, and its fetch
  view rises past everything already visible to the hart: `itv := max itv (max tv (max rv pub))`. That is faithful to
  Zifencei, and also closes the converse gap: today `itv` ignores the read watermark `rv` (`MachCSL/Lang.lean:193-200`),
  so a foreign code store the hart has merely loaded need not be fetched (WEAKER than Zifencei). The drain's consumers
  (`FetchProg` row 6m, F-6m-1, the P-W6 fetch marker, the [OWN.139] (t3) scope) are re-proved on the MachCSL serial lane.
* **Why xv6 is still fine.** Nothing in xv6 relies on this ordering for correctness. The trapframe's `kernel_hartid`
  is read back only by hart A itself (own-hart forwarding) or through later lock hand-offs. The gap is in what the
  *machine* admits, not in the code. **This is NOT an xv6 bug.**

---

## EX-IO-1: the fenced NOTIFY shape — a `fence iorw,iorw` the model cannot see (recorded 2026-10-21)

**One line.** xv6 orders its virtio descriptor stores before the device doorbell with `fence iorw,iorw`, exactly as
RVWMO requires. The graph model cannot see the fence's i/o bits, because Sail drops them at decode
(`notes/sail-gaps.md` SAIL-GAP-1). Only the trusted arm (R1) of `ioResidueGmo` makes the device see the descriptors.
Source: `notes/rvwmo-spec-audit.md` §2 row 7, §4 items 2 and 10.

### The xv6 code (hart A, `virtio_disk_rw`; image offsets from `notes/W10-P0a-wfence.md:118-119`)

| step | image | what it does |
|---|---|---|
| 1 | before `virtio_disk_rw+0x186` | plain RAM stores of the three descriptors and the avail-ring slot |
| 2 | `virtio_disk_rw+0x186` | `fence iorw,iorw` (`__sync_synchronize()`) |
| 3 | `virtio_disk_rw+0x192` (`0x80005c86`) | `sh` of `avail->idx`: a plain RAM store |
| 4 | `virtio_disk_rw+0x196` | `fence iorw,iorw` |
| 5 | `virtio_disk_rw+0x19e` (`0x80005c92`) | `sw zero, QUEUE_NOTIFY`: an MMIO store (an I/O output) |
| 6 | the disk device (row `NCPU`) | after the NOTIFY, reads the avail ring and the descriptors (DMA reads of RAM) |

### What the spec says

* **FENCE.** A fence with `w` in its predecessor set and `o` in its successor set orders the earlier RAM stores before
  the later device output. The FENCE prose adds that no device may observe the successor before the predecessor
  (from memory, verify). So the device must see the new descriptors and the new `avail->idx`.
* **PMAs.** Strongly ordered I/O regions order I/O accesses against other I/O accesses only, never against RAM.
* **riscv.cat.** It has no I/O events. The i/o bits have no formal counterpart.

### What the tree does

* **Sail.** `fence iorw,iorw` decodes as `fence rw,rw` (`InstsEnd.lean:18299-18314`). The fence orders the RAM stores
  among themselves, but orders nothing against the NOTIFY.
* **Graph model.** `gfenceCovers` (`Weak/WeakRvwmoGraph.lean:235-239`) needs a RAM read or write at both ends, and an
  `LIo` event is neither. So the graph has no edge from steps 1/3 to step 5. A graph in which the device reads STALE
  descriptors is therefore consistent for the model without (R1): **WEAKER** than the spec.
* **(R1).** "A RAM access po-before an I/O event of the same hart is gmo-before it" (`Weak/GraphFabResidue.lean:116-143`)
  orders steps 1/3 before step 5, so the stale-read graph is excluded. That is **STRONGER** than the spec (every MMIO
  access acts as a one-way fence; true of QEMU-TCG), and here it happens to supply what the real fence gives.
* **MachCSL.** A machine fence with `pw ∧ sr` (which `rw,rw` has) DRAINS the store buffer
  (`notes/weak-allocproc-routeP-design.md` §1 row 4). So in the MACHINE the descriptors have landed before the NOTIFY.
  The replay's `DiskDesc` argument (`drainLanded`, design §3.4) uses this drain.

### Why it matters

* **A4 (drop (R1) after the capstone).** Without (R1), a stale-read graph would be in the quantifier, and the replay
  would get stuck on it. The hart's fence waits for the stores to land. The landing gate waits for the device's stale
  read to be replayed. The device read waits for the NOTIFY by (R3). Verify against `Weak/SbOrd.lean:796,1059`.
* **Ruling [OWN.142].** Keep (R1) until the capstone. After it, revisit with a read-only NOTIFY-shape spike and with
  option (b) of Q-AUDIT-1: recover the fence bits from the instruction word and add a FAITHFUL fence-with-i/o-bits rule.
* **xv6 bug #1** (`notes/xv6-weak-memory-bugs.md`). The same blind spot means that bug #1's fix (a fence before
  `DRIVER_OK`) cannot be checked by the present model.
* **Why xv6 is fine here.** xv6 has the right fence. The gap is in what the model can SEE, not in the code.
  **This is NOT an xv6 bug.**

---

## EX-TRAP-1: a PLIC pin delivery acts as a one-way store fence (recorded 2026-10-21)

**One line.** RVWMO makes trap entry no memory-ordering point. The graph model files a PLIC pin delivery as an I/O
event in the receiving hart's row, so (R1) orders EVERY earlier RAM store of that hart before the delivery. That is
**STRONGER** than the ISA. Source: `notes/rvwmo-spec-audit.md` §2 row 8.

### The shape (hart A)

| step | where | what it does |
|---|---|---|
| 1 | any kernel code | a plain RAM store `sd x` |
| 2 | PLIC → hart A | the external interrupt is delivered (`pstepPlic`). It is an `LIo .dev` event in hart A's row (D49 (a), [OWN.17]) |
| 3 | `kernelvec` / `uservec`, then `devintr` | the trap entry (register saves), then the claim `plic_claim` (an MMIO load, `0x80005886`) |
| 4 | the handler | MMIO accesses to the UART or virtio, then `plic_complete` |

### What the spec says

* **ISA.** Traps and interrupts are not memory-ordering points. Precise exceptions order the trap after the earlier
  instructions *retire*, not after their stores become visible. Step 1 may still be in hart A's store buffer when the
  handler's MMIO accesses (steps 3–4) reach the device.
* **RVWMO / PMAs.** Both are silent on where an interrupt delivery sits in the global memory order.

### What the tree does

* **Graph model.** The delivery is an I/O-class event in hart A's row under (R1)/(R2)
  (`Weak/GraphFabResidue.lean:116-143`; plan §B(11), "EVERY RAM store po-before a PLIC pin delivery"). So step 1 is
  gmo-before step 2, which is gmo-before the claim. The (F5) arm orders pre-trap LOADS only. The STORE coupling comes
  from (R1). **STRONGER** than the ISA.
* **MachCSL.** `takeException` / `returnException` are memory no-ops (`MachCSL/Lang.lean:1400-1401`), and traps do not
  drain the store buffer (`notes/weak-allocproc-routeP-design.md` §1, the "interrupts, traps" row). **FAITHFUL.**

### Why it matters

* **What a reader may conclude.** Inside the model, handler code may assume that all pre-trap stores of its hart are
  visible to its MMIO accesses. That holds on QEMU, but the ISA does not promise it. xv6's handlers do not rely on it:
  their shared data goes through locks.
* **Rulings.** [OWN.142] keeps (R1), and so this strengthening, until the capstone. It is to be revisited together
  with EX-IO-1.
* **Related record [OWN.145] (s-a).** `spinFenceNext` needs "no interrupt at `main+0x18`". It gets this from a
  proof-only per-hart "interrupts off" ghost record (set and cleared at `csrw sstatus`, trap entry and `sret`). That
  record says WHEN a delivery can happen. It adds no memory ordering, and so does not depend on this example's
  strengthening.
* **This is NOT an xv6 bug.**
