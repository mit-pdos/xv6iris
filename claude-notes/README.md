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
- **[`remote-build-gcp.md`](remote-build-gcp.md)** — building on the GCP VM:
  the two scripts, daily use, pulling `.vo` back for a local single-file
  recheck, preemption and cost, and the two things that silently break (the
  VM's Ubuntu must match, and the opam switch must be byte-identical).
- **[`kernel-defects.md`](kernel-defects.md)** — how to tell a defect in the xv6
  SOURCE from a problem in a spec, the register of open ones, and the provably
  dead code.  The newest entry -- `read(fd, buf, -1)` delivering the rest of
  the file -- is FIXED UPSTREAM, and is why `XV6_REV` is at `31f115a`.

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
- **[`main-cycle-port.md`](design/main-cycle-port.md)** — the expression-resident
  Sail monad: `HartE gen cpu m` steps one monad NODE per language step, so a
  page walk, a TLB write-back, a fetch and a data access of one instruction can
  interleave with other harts. The placement rule, the fused-AMO window, the
  proof interface that keeps step granularity out of proof granularity, and the
  phasing (the tree is red across the port — read §6 before starting).
- **[`adequacy.md`](design/adequacy.md)** — whole-system adequacy, and the TRACE INVARIANT hook `Hphi`: how a pure consequence of any Iris invariant is exported to every state of the CSL-free execution, which conjunct of `state_interp` each kind of fact comes from, and what `wp_strong_adequacy` still leaves on the table.
- **[`fs-state.md`](design/fs-state.md)** — DESIGN OF RECORD for the
  durable-disk project: the view record `Γ`, byte-level ownership on both
  the durable and logged sides, `inode_owned`/`dir_owned`/`free_bitmap`/
  `fs_state` as nested predicates with link TOKENS and no whole-state pure
  clauses, "in flight, not inconsistent", the debt, the log's FS-agnostic
  interface, and what it supersedes.
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
- **[`elf.md`](design/elf.md)** — ELF file semantics: the file-side
  `ElfFile.v` layer vs `ElfEnc.v`'s code-side readers, the PrimString import
  vehicle for whole binaries, the kernel-dump consistency theorem
  (`ElfKernel.v`), the measured vm_compute rules (`List.rev` is quadratic),
  and the exec() connection plan.
- **[`fs-img.md`](design/fs-img.md)** — the mkfs disk image in Rocq: the pure
  on-disk FS semantics (`FsImg.v`), the literal image import, the `fsimg_wf`
  durable-state check, the /init-/sh-/echo-/sync-are-the-tracked-raws
  theorems, the adequacy discharge (nothing about the FS is assumed any
  more), and the measured 2 MB vm_compute traps.
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
  bits-in-a-block vocabulary, the `bitmap_res` resource and the FREE POOL,
  **`bitmap_inv`** (the persistent invariant that owns them, and the
  `wp_log_write_au` suppliers balloc/bfree touch it through), why the pool
  token's exclusivity makes the alloc/free handshake sound, and the
  single-bitmap-block simplification.
- **[`fs-friendly.md`](design/fs-friendly.md)** — the friendly, client-facing
  file-system layer above the syscall proofs: what a caller should be able to
  say, and the staging that gets there.
- **[`fs-fragments.md`](design/fs-fragments.md)** — the fragment algebra and
  the tree layer, the DESIGN OF RECORD for F1/F1.5: rulings R1–R12 (including
  the standing constraint that (L6) must NEVER be stated) over a verification
  report against the landed tree.

## `projects/` — ongoing worklists & plans (one per effort)

Six remain open; each file's top banner says precisely what is left (the
first five were audited against the tree 2026-08-22):

- **[`durable-disk.md`](projects/durable-disk.md)** — xv6 correctness
  across crashes INCLUDING FS consistency, under RULING 3 (2026-08-23):
  the file system as nested SL predicates at two views (`design/fs-state.md`),
  the log's contract first (custody at birth, row (b), byte-keyed `fs_L`,
  the parked payload and two AUs), then the predicates, then a `sys_mknod`
  spike.  Stages A/B/D/H0 stand; everything FS-side is still a
  placeholder.  The byte-view attempt is archived in
  `completed/durable-disk-byteview.md`.
- **[`fs-log.md`](projects/fs-log.md)** — the FS block layer, STAGE 4 (the
  crash instantiation): real `n > 0` recovery in `initlog`/`install_trans`
  (today both carry a clean-image premise), `sys_sync`'s empty
  postcondition, and the phase-D2 read-data-indexed-permit decision. The
  boot composition's wiring is done; it inherits the clean-image premise.
- **[`sp-migration.md`](projects/sp-migration.md)** — owning memory at a
  NON-IDENTITY kernel va: the settled design (ktier-indexed `↦ₘ[kt]`,
  `kpt_on` witness, `KtierLe` inference) and the KSTACK campaign are
  LANDED (K4 via `ParkCap.v`); what is NEXT is the `instr` ktier sweep
  (~330 statement-identical files) and the uservec/userret trampoline-fetch
  project that consumes `TrampText.tramp_text_mint`.
- **[`instr-subgoal-sweep.md`](projects/instr-subgoal-sweep.md)** — the
  performance discipline that replaced posing instruction facts: close the
  leaf's `instr` premise as a `[]` subgoal from `kernel_text` instead. Measured
  −46 % wall / −61 % `Qed` / −69 % proof term on the reference conversion. The
  file is the mechanical recipe, the traps, and the scoreboard for the
  remaining 214 files.
- **[`device-conformance.md`](projects/device-conformance.md)** — the
  device semantics differentially tested against QEMU: one bare-metal image
  run on both machines, the model side EXHIBITING one execution by
  `vm_compute` (no WP, no Iris, ~8 ms/instruction).  Landed and green
  (`make vtest`); it has already found FIVE divergences, one of them an
  UNSOUNDNESS — the model serves the virtqueue strictly in publication order
  and real hardware does not, which is exactly what `virtio_disk_intr` reads
  the used element's id for.  §5 is the worklist, and §7 of it is the
  `prim_step` soundness bridge that `HartBlock.v`'s header already defers to.
- **[`namei-pinned-lookup.md`](projects/namei-pinned-lookup.md)** — a
  ghost-state spec for WHICH inode `namei` returns: N-1 through N-5.2B
  (kexec loads `/init` at its entry) are landed; M2 (`dvrt`, the pin through
  the trap seam) and stage C (threading `proc_ptm` through kexec) are gated
  on the owner's call. §10 is the long-run tree-level direction.

## `completed/` — finished projects, archived for reference

`durable-disk-byteview.md` (2026-08-23) is NOT a finished project: it is
the superseded byte-view worklist of the live durable-disk effort, kept
for its two surveys' findings; `projects/durable-disk.md` is current.

Kept for their durable design notes, gotchas and reusable recipes; `ls` them.
**Nobody reads these for current guidance**, so they are the one place a
narrative may survive, and they are not maintained — a statement in one was
true when it was written and may not be now. When a project is fully finished —
no remaining work and no cleanup — move its file here rather than deleting it,
and lift any broadly-applicable lesson up into the design or durable notes
first.

- **[`async-disk.md`](completed/async-disk.md)** — the disk has a VOLATILE
  write-back cache by default (the device offers FLUSH|CONFIG_WCE; capture /
  drain-any-order / gated completion; a power cycle drops the cache). xv6
  declines FLUSH, and `virtio_proto_writethrough` (no axioms) is the proof
  that its writes are durable at completion — the disk assumption became a
  theorem about the driver. §4 records what a FLUSH-negotiating driver owes.
- **[`sector-atomic-disk.md`](completed/sector-atomic-disk.md)** — disk
  writes are SECTOR-atomic (512 B); a block (1024 B) lands one sector per
  device step in ANY order; the commit is atomic because the 124-byte log
  header sits in sector 0. The machine permit became ONE sequential permit
  per request (`RiscvPtsto.sperm`); §6 records why independent per-sector
  permits cannot work (one mirror half, two permits, device-chosen order).

`panic.md` is the one to open before proving any arm that ends in a `jal
panic` — `forkret`'s `if (first)` is the only such arm left. It carries the arm
recipe, its six traps, and the rule for deriving a `.rodata` message address
instead of copying one.

Two are worth reading even if you never touch their subject, because they are
about failure modes that COMPILE: `explicit-cpuid.md` with its porting guide
(an interface sweep across every WP statement in the tree, carrying a
scoreboard of six contracts that were stated falsely and compiled anyway), and
`fs-namei.md`'s close-out (what the fs.c contracts THREAD rather than
discharge — which is what `sysfile.c` and the boot client inherit).

`lock-set.md` is the third, and the one to read BEFORE adding a lock or
changing where one sits: it carries the audit of every simultaneous lock pair
in xv6 and the installed rank table. The one thing it left behind —
`ProofIput.iput_acquiresleep_order_ADMITTED`, a FALSE axiom that made
everything downstream of `iput` vacuous — is GONE; how, and why no ranking
could ever have licensed that edge, is in
[`completed/iput-acquiresleep.md`](completed/iput-acquiresleep.md).

Twelve arrived on 2026-08-22. `forkret-park.md` is the LAST assumed Link,
retired — read it for why the trap loop's two "gap" premises were
unsatisfiable and became residue-carried facts (§4), and why the park had
to become a guarded-fixpoint RESOURCE (`iris/ParkCap.v`) rather than a
functor argument (§6, a module cycle). With it, eleven projects whose work
had finished: `forkret-boot-arm.md` (forkret's `if (first)` arm),
`syscall-dispatch.md` (all 22 entries wired, the dispatcher's `Axiom` and
the tree's last `Admitted` gone — read it for why `syscall_env` is
`fs_ready` plus the ties, and the read/write count story), `main-boot.md`
(`main()` proven, both callee axioms retired), `fs-cfg-boot.md` (the
era-fupd allocation of `icfg`/`fscfg`, the `_at` constructor discipline,
the boot kits — **read R5 before assuming `valid = 0` means the ghost
state says nothing**), `main-cycle-port.md` and `user-tier-port.md` (the
per-node port, complete and merged; `user-tier-port.md` §14.4 is the
fetch-geometry package), and the Umode tier's four programs —
`user-verified.md` (`sync`, the tier's vocabulary), `user-echo.md` (the
stack as a budget, `uM_only`), `user-sh.md` (scoping a program by its
input, the I/O protocol), `user-init.md` (the non-terminating loop) — all
verified and back in the build since the tier's revival (`e8459afe`).
`iget-licence.md`'s three non-blocking leftovers are in
[`design/code-organization.md`](design/code-organization.md) under
"Cleanups inherited from finished projects", beside `main-boot.md`'s.

Seven more followed the same day after a tree audit of every remaining
project (each carries a top banner saying what was verified and which of
its own claims were stale): `cwd-ref.md` (the reference is `inode_held`;
the file-table half landed as `inode_pay`, not as designed),
`fs-icache.md` (read §10–§12 of the design; the "iref_slot leak" it owes
is not a leak), `fs-inode.md`, `iclaim-ledger.md` (its STATUS header says
"nothing built" — §5⁗″/§6‴ are the truth), `fs-fragments-campaign.md`
(the ledger of the fragment slate; F3 was stopped by ruling),
`proc-struct-resources.md` (**read `kwait` before writing any loop that
can RETURN from inside itself**), and `proc-pagetable-ownership.md` (only
file-organization refactors left). Their refactor/comment leftovers are
in `design/code-organization.md`'s "Cleanups inherited from finished
projects".

Seven arrived on 2026-08-20, when their work finished: `kexec.md` (the largest
function in the tree, and the home of **the copyout story** — the most
transferable thing that project produced), `fs-sysfile.md` (the syscall-layer
campaign that took `sysfile.c` to 16/16 and retired the tree's last stub
`Axiom`; its successor, the DISPATCHER, is
[`completed/syscall-dispatch.md`](completed/syscall-dispatch.md)), `uservec.md` (uservec proven and the whole-trap-loop Löb theorem
built on top of it), `console.md` and `uart-driver.md` (console.c 5/5, uart.c
4/4, both cones axiom-clean), `kvminithart-tlb-lane.md` (the TLB lane's root,
closed), and `iput-acquiresleep.md`. The two cleanups those files were still
carrying were lifted into
[`design/code-organization.md`](design/code-organization.md) first, under
"Cleanups inherited from finished projects", so they did not go into the
archive with them.
