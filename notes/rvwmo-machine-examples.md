# RVWMO vs. the proof machine: reference examples

Concrete hart-level examples of places where the proof machine `MachCSL` and RVWMO disagree. Each one is recorded
so that it can be pointed to by name from rulings, plans and theorem documentation.

---

## EX-FENCEI-1: `fence.i` on the return to user mode is not a data fence (recorded 2026-10-21)

**One line.** In xv6's return to user mode, RVWMO + Zifencei let the user's first data load be satisfied *before* the
kernel's last trapframe store becomes visible to other harts. `MachCSL` forbids this, because its `fence.i` drains the
hart's store buffer.

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
* The machine is **STRONGER** than RVWMO here.
* `notes/weak-allocproc-routeP-design.md:161` (the Zifencei row) treats the drain as faithful. That label is WRONG and is
  to be corrected.

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
* **Pending decision Q-A2-2** (weakMachCSL advisory loop, `~/dev/weak-orch/weakmach/proposal-A3.md` §7): keep the drain
  as a documented strengthening, make `fence.i` non-draining now (faithful to Zifencei), or decide at the P-W6 spike.
* **Why xv6 is still fine.** Nothing in xv6 relies on this ordering for correctness. The trapframe's `kernel_hartid`
  is read back only by hart A itself (own-hart forwarding) or through later lock hand-offs. The gap is in what the
  *machine* admits, not in the code. **This is NOT an xv6 bug.**
