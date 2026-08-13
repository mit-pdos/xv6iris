# claude-notes — xv6iris development notes

Durable, forward-looking guidance for the Rocq/Iris proofs under `iris/`
(weakest-precondition proofs for a RISC-V rv64 xv6 kernel). Split into small,
topic-scoped files so an agent can read only what its task needs.

**Read [`durable-notes.md`](durable-notes.md) first** for any work under `iris/`
— the guiding principle, build instructions, and cross-cutting gotchas. Then
open the design file(s) for the subsystem you are touching, and — only if you
are working on that effort — the relevant `projects/` file.

This index is a POINTER LIST, not a summary. One or two lines per file; the
content lives in the file. Keep it that way, and see "Maintaining these notes"
in `durable-notes.md` for what belongs where and what gets deleted.

## Top level

- **[`durable-notes.md`](durable-notes.md)** — the always-relevant core: the
  guiding principle (clean specs over rework), how to maintain these notes,
  build/opam instructions, the proof-coverage report, proofmode & bitvector
  gotchas, reusable recipes, and durable spec-design preferences.
- **[`optimization.md`](optimization.md)** — proof performance: the diagnostics,
  the rules that keep a proof fast, and the negative results so nobody re-runs
  them. Apply the rules when writing new proofs, not after.
- **[`xv6-bump-playbook.md`](xv6-bump-playbook.md)** — moving to a new upstream
  `XV6_REV`: the mechanical steps and their silent no-ops, how to CLASSIFY a
  change before touching a proof, the two relayout tools, the categories of
  breakage, and the finishing checks. Read before any bump.
- **[`kernel-defects.md`](kernel-defects.md)** — how to tell a defect in the xv6
  SOURCE from a problem in a spec, plus the register of open ones (currently
  empty) and the provably dead code.

## `design/` — how each part of the project is built

- **[`execution-model.md`](design/execution-model.md)** — the Sail model & WP
  exec stack, the clock tick, the minstret invariant, the register file, memory
  points-to & dfrac, config bundles, fetch geometry, the concrete-state decode
  bridge.
- **[`code-organization.md`](design/code-organization.md)** — where a function's
  decode facts live vs. its WP leaf lemmas, import discipline, lemma-altitude
  rules, specific-vs-generic leaves.
- **[`spec-modules.md`](design/spec-modules.md)** — function specs as module
  types: the `SpecF`/sealed-functor/`LinkF` shape that keeps a function proof off
  its callees' proofs, so the build does not serialize along the call graph.
- **[`smode-and-vcgen.md`](design/smode-and-vcgen.md)** — the S-mode config
  convention, recovering a concrete register map from a VCgen block.
- **[`interrupts.md`](design/interrupts.md)** — interrupt dispatch: the
  keystones, the interrupt invariant + absorbing step engine, the SIE-agnostic
  bundle, the interrupt-stack file layout.
- **[`multi-cpu.md`](design/multi-cpu.md)** — the ambient-hart multi-CPU model.
- **[`adequacy.md`](design/adequacy.md)** — whole-system adequacy.
- **[`crash.md`](design/crash.md)** — power, crashes and generations: the ghost
  power thread, generation-indexed loop expressions, the fixed/era `riscvGS`
  split, the crash-spanning disk invariant.
- **[`device.md`](design/device.md)** — the memory-mapped device model (16550
  UART + PLIC + virtio-mmio disk), the device ghosts, the bus-master/DMA-lease
  story, the S-mode instruction-level UART access layer.
- **[`virtio-driver.md`](design/virtio-driver.md)** — the virtio driver's
  concurrent-request protocol, DMA handoff and disk points-to.
- **[`tlb-translation.md`](design/tlb-translation.md)** — the kvmmake-faithful
  all-4KB kernel page table, TLB/page-walk/translation, userret/trampoline/user
  page table, the `CommonWalk.v` walk technique.
- **[`kernel-proofs.md`](design/kernel-proofs.md)** — kernel-side proof
  architecture: swtch/contexts, proc locks/wakeup, loop shapes, whole-function
  WP specs, spinlocks, kernel data-structure layout.
- **[`proc-struct.md`](design/proc-struct.md)** — `struct proc`: the verified
  geometry of all 15 fields, the five sharing disciplines the code actually uses
  (not the three `proc.h` claims), and the two resources — the state-keyed lock
  invariant any CPU can peek at, and the exclusive private bundle.
- **[`file-table.md`](design/file-table.md)** — the open-file table: `struct
  file`'s geometry, the reference-count algebra tying `f->ref` to fractional
  ownership of the immutable fields, the `ftable.lock` invariant, and `f->off`.
- **[`pipe.md`](design/pipe.md)** — pipes: geometry, the well-formedness
  predicate, the two-ended fractional reference algebra, `PageFields.v` (carving
  a kalloc'd page into typed struct fields — reusable), and page reclamation.
- **[`fs-log.md`](design/fs-log.md)** — the FS block layer: the three
  block-content states, the `γL` logged-view ghost and its commit discipline,
  the Ψ-parametric bio escrow, the bread/bwrite/brelse contracts, `log_res` and
  the begin_op/end_op/log_write specs, and the stage-4 crash plan.
- **[`fs-inode.md`](design/fs-inode.md)** — the inode layer: `struct inode`'s
  geometry read off `bmap`'s instructions, the pure `blkmap` model, the two
  resources (`inode_map`, `inode_blocks`) and why `balloc`'s fresh block is
  DEPOSITED, `BlockWords.v`, and the SPEND-AT-MOST budget rule.
- **[`fs-icache.md`](design/fs-icache.md)** — the inode CACHE (`itable`,
  `iget`/`idup`/`iput`), the chokepoint under most of `sysfile.c`: the itable's
  geometry, the Arc reference algebra, why the `ref` words live in an invariant,
  the REF-1 exclusivity theorem, the escrow/pool arms, and the share-generation
  algebra. Sections are §-numbered and cited from the live fs-sysfile worklist.
- **[`fs-bitmap.md`](design/fs-bitmap.md)** — the block bitmap: the
  bits-in-a-block vocabulary, the `bitmap_res` resource and the FREE POOL, why
  the pool token's exclusivity makes the alloc/free handshake sound, `bfree`'s
  contract, and the single-bitmap-block simplification.

## `projects/` — ongoing worklists & plans (one per effort)

- **[`fs-sysfile.md`](projects/fs-sysfile.md)** — the syscall-layer campaign
  (file.c's last 2 + sysfile.c's 11). **Live and actively appended to.**
- **[`fs-icache.md`](projects/fs-icache.md)** — the inode-cache implementation
  effort (design in [`design/fs-icache.md`](design/fs-icache.md)): the staged
  cycle plan, the branch-per-cycle strategy, the owed boot wiring.
- **[`fs-inode.md`](projects/fs-inode.md)** — the inode layer above the block
  layer, heading for `writei`/`readi`; keeps the deferred bitmap-invariant
  question `balloc` waits on and the owed decode-word dedup sweep.
- **[`fs-log.md`](projects/fs-log.md)** — the FS block layer, STAGE 4 (the crash
  instantiation) only. Left: initlog's real recovery spec, sys_sync, the boot
  composition, and the phase-D2 finding that caps what recovery can CLAIM.
- **[`proc-struct-resources.md`](projects/proc-struct-resources.md)** — the
  `struct proc` resource split: what has landed and what is next (the remaining
  syscalls, and `cwd_ref`). **Read `kwait` before writing any loop that can
  RETURN from inside itself.**
- **[`cwd-ref.md`](projects/cwd-ref.md)** — filling the `ProcInv.cwd_ref` hole:
  the target shape (no null arm), the measured layering fix, why the itable
  gname must be canonical, and the ordering behind kfork.
- **[`proc-pagetable-ownership.md`](projects/proc-pagetable-ownership.md)** —
  the process page table's OWNERSHIP side (`proc_pt`): the footprint derived
  from `um`, the physical-tier decision, the `page_own ⇄ udata_own` bridges.
  The CONSTRUCTION side is [`completed/proc-pagetable.md`](completed/proc-pagetable.md).
- **[`kexec.md`](projects/kexec.md)** — `kexec()`, the largest function in the
  tree, where the FS, the page-table builder and `struct proc` meet. Opens with
  a CHECKPOINT and ends with an ordered worklist. **Read it for the copyout
  story**, the most transferable thing this project produced.
- **[`main-boot.md`](projects/main-boot.md)** — `main()`, both arms proven: the
  `started` one-shot escrow, the deposit as a □-wand, the hart-generic init
  chain. Remaining: the whole-system adequacy composition.
- **[`uservec.md`](projects/uservec.md)** — uservec, proven (trampoline.S is
  100 % covered): the boundary specs, the TVM/TSR mstatus-pin extension, the
  proof's file split. Remaining: the whole-trap-loop Löb theorem.
- **[`panic.md`](projects/panic.md)** — `panic()`, proven: the contract the two
  printk calls force, the Löb self-jump, and the one thing left — splicing it
  into the 169 files that still thread `PanicStub.v`'s placeholder credential.
- **[`printk.md`](projects/printk.md)** — the formatted-output cone, all proven
  and linked: `pk_held`, `PrintkFmt.v`, the fuel inductions, the loop-assembly
  architecture. Only the general (non-panic) path remains.
- **[`console.md`](projects/console.md)** — console.c: consolewrite (proven,
  axiom-clean), consoleread (specified, proof owed) and consoleintr; the
  `cons` module's own state in `ConsoleInv.v` and why its resource is
  deliberately unconstrained.
- **[`uart-driver.md`](projects/uart-driver.md)** — the interrupt-driven UART
  driver; uart.c is 4/4 functions. Read it for the transmit path's shape and for
  the rotated-loop / nested-iLöb / `uart_sent_sub` techniques. Remaining:
  consolewrite, consoleread, consoleintr, and the boot `newlock`.
- **[`eb-generic-sweep.md`](projects/eb-generic-sweep.md)** — making the sleep
  cone callable with interrupts OFF, which is what `usertrap` needs to reach
  `kexit`: the index-free restatement, what moves with a crossing and what must
  not, and the remaining worklist in dependency order.
- **[`user-verified.md`](projects/user-verified.md)** — VERIFIED user-mode
  execution (the Umode tier): the `uv_cap` capability, the concrete-image memory
  layer, the interrupt-absorbing step engine, and the sync program's proofs.

## `completed/` — finished projects, archived for reference

Kept for their durable design notes, gotchas and reusable recipes; `ls` them.
**Nobody reads these for current guidance**, so they are the one place a
narrative may survive, and they are not maintained — a statement in one was
true when it was written and may not be now. When a project is fully finished —
no remaining work and no cleanup — move its file here rather than deleting it,
and lift any broadly-applicable lesson up into the design or durable notes
first.

Two are worth reading even if you never touch their subject, because they are
about failure modes that COMPILE: `explicit-cpuid.md` with its porting guide
(an interface sweep across every WP statement in the tree, carrying a
scoreboard of six contracts that were stated falsely and compiled anyway), and
`fs-namei.md`'s close-out (what the fs.c contracts THREAD rather than
discharge — which is what `sysfile.c` and the boot client inherit).
