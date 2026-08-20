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
- **[`main-cycle-port.md`](design/main-cycle-port.md)** — the expression-resident
  Sail monad: `HartE gen cpu m` steps one monad NODE per language step, so a
  page walk, a TLB write-back, a fetch and a data access of one instruction can
  interleave with other harts. The placement rule, the fused-AMO window, the
  proof interface that keeps step granularity out of proof granularity, and the
  phasing (the tree is red across the port — read §6 before starting).
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
- **[`fs-friendly.md`](design/fs-friendly.md)** — the friendly, client-facing
  file-system layer above the syscall proofs: what a caller should be able to
  say, and the staging that gets there.
- **[`fs-fragments.md`](design/fs-fragments.md)** — the fragment algebra and
  the tree layer, the DESIGN OF RECORD for F1/F1.5: rulings R1–R12 (including
  the standing constraint that (L6) must NEVER be stated) over a verification
  report against the landed tree.

## `projects/` — ongoing worklists & plans (one per effort)

- **[`main-cycle-port.md`](projects/main-cycle-port.md)** — the expression-resident
  monad port (design in [`design/main-cycle-port.md`](design/main-cycle-port.md)).
- **[`user-tier-port.md`](projects/user-tier-port.md)** — the user tier's port onto
  per-node semantics (sub-plan of the above: `swp_hmrun_of_exec` + `goodmb` twins).
  **Done on branch `hart-node-port`**: `ProofUser.wp_user_exec_closed` is proven
  per-node, so the temporary user-exec axiom is discharged and
  `iris/UserExecAxiom.v` is gone. Read it for the §14.4 fetch-geometry package
  (width-generic read certificates, the six va geometries, the split-fetch
  shells) and the `goodmb` discipline. The one scope decision it still records
  is §P8: the specific-binary Umode tier (`sync`/`echo`/`sh`/`init`) is
  descoped from the build.
- **[`fs-fragments-campaign.md`](projects/fs-fragments-campaign.md)** — the
  fragment campaign's ledger (design in
  [`design/fs-fragments.md`](design/fs-fragments.md)): the staged slate, what
  each increment cost, where the landed tree diverged from the report's
  sketches, and the standing constraints.
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
- **[`sp-migration.md`](projects/sp-migration.md)** — owning memory at a
  NON-IDENTITY kernel va (the gate on the process kernel stack): the four
  dead ends, and THE SETTLED DESIGN — a ktier-indexed `↦ₘ[kt]` datum, a
  persistent per-hart `kpt_on` witness carried by a ktier-indexed `sie_cap`,
  tier-preserving `KtierLe`-inferred leaf rules, ambient `CurKtier` notation,
  and lock payloads at explicit tiers.
- **[`proc-pagetable-ownership.md`](projects/proc-pagetable-ownership.md)** —
  the process page table's OWNERSHIP side (`proc_pt`): the footprint derived
  from `um`, the physical-tier decision, the `page_own ⇄ umem_own` bridges,
  and **the address-space view** — `user_pt_inv P M` now EXPOSES the abstract
  state of a user-mode process (`M`, its memory keyed by user virtual
  address), why that forces no aliasing, and what is left to thread it into
  the kernel-side proofs. The CONSTRUCTION side is
  [`completed/proc-pagetable.md`](completed/proc-pagetable.md).
- **[`main-boot.md`](projects/main-boot.md)** — `main()`, both arms proven: the
  `started` one-shot escrow, the deposit as a □-wand, the hart-generic init
  chain. **§G3 is now `userinit`'s own record** — proven AND linked, with the
  axiom moved down to `namei`'s root corner
  (`SpecNameiRootBoot`/`LinkNameiRootBoot`), the row-by-row table of what
  main can and cannot pay, and the ruling that the cache's configuration
  must NOT be pinned by threading a premise. Remaining: that boot wiring,
  and (§G2) retiring `LinkPrintkGen.v`'s `Axiom`.
- **[`user-verified.md`](projects/user-verified.md)** — VERIFIED user-mode
  execution (the Umode tier): the `uv_cap` capability, the concrete-image memory
  layer, the interrupt-absorbing step engine, and the sync program's proofs.
  (DESCOPED from the hart-node-port build — see the ruling in
  [`user-tier-port.md`](projects/user-tier-port.md).)
- **[`user-echo.md`](projects/user-echo.md)** — the Umode tier's SECOND
  program, `echo`: the first with loops, memory reads, an argv area and a
  syscall with a real precondition. Read it for the pieces that grew to carry
  it — the stack as a splittable BUDGET, `uM_only` as the image
  postcondition of a call, the `mword_of_int` calculus, and the one generic
  branch leaf that replaces an op cross-product. (DESCOPED from the
  hart-node-port build — see the ruling in
  [`user-tier-port.md`](projects/user-tier-port.md).)
- **[`user-sh.md`](projects/user-sh.md)** — the Umode tier's THIRD program,
  `sh` on one fixed input: the design of record for scoping a program by its
  input, the `xv6_io_protocol` at I/O depth, and the code-catalog generator.
  (DESCOPED from the hart-node-port build — see the ruling in
  [`user-tier-port.md`](projects/user-tier-port.md).)
- **[`user-init.md`](projects/user-init.md)** — the Umode tier's FOURTH
  program, `init`: the first that NEVER TERMINATES (two nested `iLöb` loops
  and the `▷`-exposing branch leaves that close them), the first whose
  theorem assumes nothing about what the kernel returns (every branch of
  every syscall test is proved), and the first verified xv6 `printf`.
  (DESCOPED from the hart-node-port build — see the ruling in
  [`user-tier-port.md`](projects/user-tier-port.md).)

- **[`iclaim-ledger.md`](projects/iclaim-ledger.md)** — the iclaim ledger
  increment's own worklist (design in [`design/fs-icache.md`](design/fs-icache.md)):
  the escrow's await arm, the freeze mirror, and the as-built record of what
  each increment deviated on.
- **[`iget-licence.md`](projects/iget-licence.md)** — the iget licence
  increment (C′-lite), LANDED at `35bc973b`, with the three non-blocking
  things it left: row 14's shape question, `IgetLic.v`'s fold-back into
  `InodeRegion`/`DirLinks`, and the `SpanL`/`GreyL` deletes.
## `completed/` — finished projects, archived for reference

Kept for their durable design notes, gotchas and reusable recipes; `ls` them.
**Nobody reads these for current guidance**, so they are the one place a
narrative may survive, and they are not maintained — a statement in one was
true when it was written and may not be now. When a project is fully finished —
no remaining work and no cleanup — move its file here rather than deleting it,
and lift any broadly-applicable lesson up into the design or durable notes
first.

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

Seven arrived on 2026-08-20, when their work finished: `kexec.md` (the largest
function in the tree, and the home of **the copyout story** — the most
transferable thing that project produced), `fs-sysfile.md` (the syscall-layer
campaign that took `sysfile.c` to 16/16 and retired the tree's last stub
`Axiom`), `uservec.md` (uservec proven and the whole-trap-loop Löb theorem
built on top of it), `console.md` and `uart-driver.md` (console.c 5/5, uart.c
4/4, both cones axiom-clean), `kvminithart-tlb-lane.md` (the TLB lane's root,
closed), and `iput-acquiresleep.md`. The two cleanups those files were still
carrying were lifted into
[`design/code-organization.md`](design/code-organization.md) first, under
"Cleanups inherited from finished projects", so they did not go into the
archive with them.
