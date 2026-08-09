# claude-notes — xv6iris development notes

Durable, forward-looking guidance for the Rocq/Iris proofs under `iris/`
(weakest-precondition proofs for a RISC-V rv64 xv6 kernel). Split into small,
topic-scoped files so an agent can read only what its task needs — the design
of a subsystem, or one project's worklist — without wading through unrelated
in-flight worklists.

**Read [`durable-notes.md`](durable-notes.md) first** for any work under `iris/`
(the guiding principle, build instructions, and cross-cutting gotchas). Then
open the design file(s) for the subsystem you are touching, and — only if you
are working on that effort — the relevant `projects/` file.

## Layout

- **[`durable-notes.md`](durable-notes.md)** — the always-relevant core: guiding
  principle (clean specs over rework), how to maintain these notes, build /
  opam / profiling instructions, the `tools/proof_coverage.py` coverage report,
  proofmode & bitvector gotchas, and durable spec-design preferences.
- **[`optimization.md`](optimization.md)** — proof performance rules: the
  performance pitfalls and the tactics/patterns that fix them (apply proactively
  when writing new proofs).
- **[`kernel-defects.md`](kernel-defects.md)** — bugs found in the xv6 SOURCE
  by the verification, as opposed to gaps in the proofs. An entry there means
  the C code is wrong and the stuck proof is the symptom. Currently one open
  defect (D1: `writei` releases a partially-modified buffer without logging
  it, so the buffer cache can diverge from the committed state), plus a list
  of near-misses and provably dead code so the same ground is not re-covered.
  Read the note at the top before proposing to fix any of them: the image is
  pinned by `XV6_REV`, so editing `xv6-riscv/` moves every symbol address.

### `design/` — how each part of the project is built

- **[`execution-model.md`](design/execution-model.md)** — the Sail model & WP
  exec stack (`run`/`exec`, `wp_exec_step` layering), the clock tick, the
  minstret invariant, the register file, memory points-to & dfrac, config
  bundles (`hw_config`/`mmode_config`/`smode_config`), fetch geometry, and the
  fast concrete-state decode bridge.
- **[`code-organization.md`](design/code-organization.md)** — where a function's
  decode/`instr` facts live (`Code<F>.v`) and where WP leaf lemmas live
  (`Wp<Mode><Family>.v`), import discipline, lemma-altitude rules, and
  specific-vs-generic leaf lemmas.
- **[`smode-and-vcgen.md`](design/smode-and-vcgen.md)** — the S-mode config
  convention (`_scfg` wrappers, SIE ghost), recovering a concrete register map
  from a VCgen block, and straight-line VCgen blocks.
- **[`interrupts.md`](design/interrupts.md)** — interrupt dispatch: the
  keystones, the interrupt invariant + absorbing step engine, the SIE-agnostic
  v2 bundle (`sconf`/`sie_cap`), and the interrupt-stack file layout.
- **[`multi-cpu.md`](design/multi-cpu.md)** — the ambient-hart multi-CPU model.
- **[`adequacy.md`](design/adequacy.md)** — whole-system adequacy
  (`RiscvAdequacy.v`).
- **[`crash.md`](design/crash.md)** — power, crashes, and generations: the
  ghost power thread (PowerOff bumps the generation, PowerOn resets +
  forks the new generation's threads), generation-indexed loop
  expressions with corpse arms, the fixed/era `riscvGS` split, the
  crash-spanning iProp disk invariant (`crash_inv`), and the decision
  record of the rejected designs.
- **[`device.md`](design/device.md)** — the memory-mapped device model (16550
  UART + PLIC + virtio-mmio disk), `DevModel.v`/`VirtioModel.v`/`WpUart.v`/
  `WpVirtio.v`, the device ghosts, the bus-master/DMA-lease story, and the
  S-mode instruction-level UART access layer.
- **[`tlb-translation.md`](design/tlb-translation.md)** — the kvmmake-faithful
  all-4KB kernel page table, TLB/page-walk/translation, userret / trampoline /
  user page table, and the `CommonWalk.v` page-table-walk proof technique.
- **[`spec-modules.md`](design/spec-modules.md)** — function specs as module
  types: the `SpecF.v` / sealed-functor / `LinkF.v` shape that keeps a function
  proof off its callees' proofs, so the build does not serialize along the
  kernel call graph.
- **[`fs-log.md`](design/fs-log.md)** — the FS block layer (DESIGN, nothing
  landed): the three block-content states (physical / durable / logged), the
  `γL` logged-view ghost with its freeze-by-auth commit discipline, the
  Ψ-parametric rework of the bio escrow (the coherent client view that
  retires bread's mystery disjunct), the revised bread/bwrite/brelse
  contracts, the `log_res` invariant and begin_op/end_op/log_write specs,
  and the stage-4 `P_fs` plan with its two recorded open forks.
- **[`fs-inode.md`](design/fs-inode.md)** — the inode layer: `struct
  inode`'s geometry read off `bmap`'s own instructions (and the
  sleeplock alignment hole that puts `addrs` at +80, not +76), the pure
  `blkmap` model with `bm_slot` unifying the coverage and injectivity
  clauses, the two resources (`inode_map` for the map, `inode_blocks` for
  the data) and why `balloc`'s fresh block is DEPOSITED rather than
  returned, `BlockWords.v`'s word-in-a-block vocabulary, and the
  SPEND-AT-MOST budget rule — why any function above the log that does not
  take `log.lock` can only promise to spend at most N units, never exactly N.
- **[`fs-icache.md`](design/fs-icache.md)** — the inode CACHE (`itable`,
  `iget`/`idup`/`iput`), the chokepoint under most of `sysfile.c`: the
  itable's geometry read off iget's own scan (24-byte lock, 136-byte
  stride, and a loop bound that IS the next symbol's address), the Arc
  reference algebra reused from `file-table.md`, why the `ref` WORDS must
  live in an Iris invariant rather than in `itable.lock` (and why
  `SpecIlock`'s `i_ref` premise is therefore unsatisfiable as written),
  the REF-1 exclusivity theorem behind xv6's "`ip->ref == 1` means no
  other process can have `ip` locked" — what part of it is free from the
  algebra, what part needs a bio-style escrow, and what part needs no
  theorem at all — and **where `itrunc`'s two owed premises belong**: the
  block-range one is a pure `cov`-vs-`size` geometry premise (NOT a
  `blkmap_wf` or `ilock` invariant, correcting `fs-inode.md`'s guess),
  the BSIZE one an `inode_ok` conjunct, better folded into `fsblock`.
  Definitional layer landed in `iris/IcacheInv.v`.
- **[`fs-bitmap.md`](design/fs-bitmap.md)** — the block bitmap: the
  bits-in-a-block vocabulary (`BitmapEnc.v`, the third after `BlockWords`'
  words and `DinodeEnc`'s records), the `bitmap_res` resource and the FREE
  POOL that parks a free block's `fsblock` half and its exclusive
  `blk_own` token (`BitmapInv.v`), why that token's exclusivity is what
  makes the alloc/free handshake sound AND what refutes `bfree`'s
  `panic("freeing free block")`, `bfree`'s contract, the single-bitmap-block
  simplification (`FSSIZE = 2000 < BPB`), and the recorded finding that the
  existing `Module Type BALLOC` is UNPROVABLE as written — with the minimal
  delta and its ripple into `bmap`/`writei`.
- **[`virtio-driver.md`](design/virtio-driver.md)** — the virtio driver's
  own design notes.
- **[`file-table.md`](design/file-table.md)** — the open-file table: `struct
  file`'s geometry, the reference-count algebra (`auth (gmap nat (frac *
  positive))`) that ties `f->ref` to fractional ownership of the immutable
  fields, the "holding a reference" predicate, the `ftable.lock` invariant, how
  the fd-sharing patterns come out, and the staged plan for `f->off`.
- **[`pipe.md`](design/pipe.md)** — pipes: `struct pipe`'s geometry, the
  well-formedness predicate (`is_pipe` = `is_lock` over a `pipe_res` owning
  every other byte of the page), the two-ended fractional reference algebra
  that mirrors `readopen`/`writeopen`, `PageFields.v` (carving a kalloc'd page
  into typed struct fields — reusable for any page-backed object), the
  `pipealloc` spec and proof, and the page-reclamation problem that
  `pipeclose` must solve first.
- **[`proc-struct.md`](design/proc-struct.md)** — `struct proc`: the verified
  geometry of all 15 fields, the five sharing disciplines the code actually
  uses (not the three `proc.h` claims), and the resources — the state-keyed
  lock invariant any CPU can peek at (`proc_pub` + the two flat `proc_slots`
  guards), and `proc_priv`, the exclusive private bundle
  (`sz`/`pagetable`/`trapframe`/`ofile`/`cwd`) that rides alongside
  `cur_proc p` and carries a `FileInv.file_ref` per open fd.
- **[`kernel-proofs.md`](design/kernel-proofs.md)** — kernel-side proof
  architecture (swtch/contexts, proc locks/wakeup, loop shapes), whole-function
  WP specs (`callee_saved`/`stack_own`), spinlocks (`WpLock.v`), and the kernel
  data-structure layout.

### `projects/` — ongoing worklists & plans (one per effort)

- **[`fs-icache.md`](projects/fs-icache.md)** — the inode cache
  IMPLEMENTATION effort (the design lives in
  [`design/fs-icache.md`](design/fs-icache.md), §10–§12): the staged
  cycle plan — C1 the inode region (`InodeRegion.v`, landed) +
  `SpecLogWrite`'s atomic-update premise, C2 iupdate onto `dinode_at`
  (with the worked SpecIupdate v2 delta and the three-touch-point
  ProofIupdate recipe), C3 the per-entry escrow/pool + the InodeLock
  restructure + ProofIlock's `il_load` re-proof, then iget/iput. Keeps
  the branch-per-cycle strategy and the owed boot-wiring list.
- **[`fs-log.md`](projects/fs-log.md)** — the FS block layer, STAGE 4 (the
  crash instantiation) only; stages 1–3 are finished and archived in
  [`completed/fs-log-bio-and-logc.md`](completed/fs-log-bio-and-logc.md).
  log.c is 6/7 proven, `xv6_fs_adequacy` carries `P_fs` in the crash slot,
  and all four steady-state WAL writes prove real durability fupds. Left:
  initlog's real (n > 0) recovery spec, sys_sync, and the boot composition —
  plus the phase-D2 finding that caps what recovery can CLAIM (an era learns
  the on-disk header only by having written it, so closing the gap needs
  read-data-indexed permits). Design in
  [`design/fs-log.md`](design/fs-log.md).
- **[`fs-inode.md`](projects/fs-inode.md)** — the inode layer above the
  block layer, heading for `writei`/`readi`. Stage 1 (the layer under
  `bmap`) has LANDED: `BlockWords.v`, `InodeInv.v`, the assumed
  `SpecBalloc.v`, `SpecBmap.v`, and `CodeBmap.v`'s 70 instruction facts —
  definitions and contracts only, so fs.c is still 1/24. Next is
  `ProofBmap.v`/`LinkBmap.v` (the `s4`-saved-only-on-the-indirect-path
  quirk is the thing to plan for), then `iupdate`, then `writei`. Keeps the
  deferred bitmap-invariant question that `balloc` waits on, and the owed
  decode-word dedup sweep. Design in
  [`design/fs-inode.md`](design/fs-inode.md).
- **[`proc-struct-resources.md`](projects/proc-struct-resources.md)** — the
  `struct proc` resource split: what has landed (`ProcInv.v`, `procinit`,
  `argraw`/`argint`/`argaddr`, `argfd`, the whole `p->killed` cone
  (`killed`/`setkilled`/`kkill`/`sys_kill`), `sys_getpid`, `sys_close`,
  `sys_pause`, `fetchaddr`, `fdalloc`, `kwait` + `sys_wait`,
  **`kexit` + `sys_exit`**) and what is
  next (the remaining syscalls, and `cwd_ref`). `kwait` is the
  entry to read before writing any loop that can RETURN from inside itself:
  the function exit is one linear resource the inner loop takes as a premise
  and hands back to its own exit, what the exit still wants back rides
  through as an abstract frame rather than inside a closure, a parking
  loop's carried continuation is anchored at the TURN's hart (a `wp_next`
  re-anchors only forward), and `cpu_own` is the one bundle no leaf
  re-anchors. Keeps the measured account of why
  `argraw`'s six-arm proof cost 74 GB, sys_pause's path-dependent-frame
  recipe, — from fetchaddr, the first function spanning the `proc_priv`
  and bare-cell tiers — the `proc_priv_copy` accessor and the x0-as-source
  (`snez`/`negw`) recipe, and, from fdalloc, the fuel-induction descriptor
  scan and why the loop's continuation must be a premise of the loop
  statement rather than a resource in its context.  **`allocproc` is proven,
  linked and AXIOM-FREE** (allocpid with it) -- the one PRODUCER of
  `proc_priv`, and where the user page table's construction and ownership
  sides meet -- but counted-only; the
  worklist spells out the exact chain that makes it work in `kfork`'s
  uncounted regime (uvmcreate -> proc_pagetable -> freeproc), plus
  `proc_priv_owe`, the payload-deficit predicate `sys_dup` needs.
- **[`cwd-ref.md`](projects/cwd-ref.md)** — filling the `ProcInv.cwd_ref`
  hole (S5 of the above, promoted to its own file). `cwd_ref` is still `emp`
  while `SpecIdup.v` is now stated over the REAL inode cache, so the tree is
  inconsistent about the hole and `kfork` has to carry five icache premises
  no caller can discharge. Has the target shape (NO null arm, so
  `cwd_ref v ⊢ ⌜v ≠ 0⌝` and a live process's non-null cwd is a free
  projection of `proc_priv` that no `proc_slots_recast` ever re-establishes;
  the fraction existential, because fork halves it; and a
  `proc_priv_nocwd` split for the construction window between allocproc's
  return and kfork's `sd a0,336(s4)`, which is the only place a LIVE process
  has a null cwd), the
  measured layering fix (the `IrefSlots -> FileInv` cycle is one edge wide
  and exists for `NFILE`; factor the reference out of the invariant into a
  new low `InodeRef.v`), why the itable gname must be CANONICAL rather than
  threaded, the routing (S4b again, for iref slots), and the ordering —
  **after** kfork lands, with kfork's contract simplification as the
  acceptance test.
- **[`main-boot.md`](projects/main-boot.md)** — `main()`. BOTH ARMS ARE
  PROVEN (main.c 178/178 bytes; axiom footprint = printk-general + userinit
  + kerneltrap): `CodeMain.v`, `StartedInv.v` (the `started` flag as a
  one-shot escrow with a PERSISTENT payload), `SpecMain.v` (deposit as a
  □-wand main applies at the `started = 1` store), `ProofMain.v` (six
  bare-`WP Loop` call-group lemmas; no `callee_saved` threading — main
  never returns), and the SECONDARY arm `SpecMainSecondary.v` (the
  concrete deposit package `main_deposit`) / `ProofMainSecondary.v`
  (the started spin loop + the ▷-stripping fence + the hart-generic
  init-hart chain into scheduler). The file keeps the resolved-blocker
  record (G1's time-0 device invariants, G2/G3 assumed interfaces, G4's
  later-stripping fence leaf, G5's three sweeps), the callee-by-callee
  resource inventory, the assemblies main performs, and what remains:
  the whole-system adequacy composition.
- **[`proc-pagetable-ownership.md`](projects/proc-pagetable-ownership.md)** —
  the process page table's OWNERSHIP side (`ProcPtOwn.v`): `proc_pt`, one
  predicate for a valid parked user table — trampoline + trapframe + the pages
  it OWNS — the footprint derived from `um` (retiring `uptd`'s `ud_data`
  field), the physical-tier decision, the `page_own ⇄ udata_own` bridges, and
  the worklist for folding `UserPtTree.user_pt_inv` onto it. The CONSTRUCTION
  side is [`completed/proc-pagetable.md`](completed/proc-pagetable.md); they
  meet at `ProcPtOwn.proc_pt_intro_ppt`.
- **[`uservec.md`](projects/uservec.md)** — uservec (the user-mode trap
  handler), PROVEN — trampoline.S is 100% covered: the boundary specs
  (SpecUserret/SpecUservec/SpecUsertrap, the userret→user-exec dovetail
  `UserretUser.v`), the TVM/TSR mstatus-pin extension, the proof's file
  split (catalog / store+CSR leaves / reverse pt2 switch / chain) with its
  reusable lessons, and the remaining work: prove usertrap(), then the
  whole-trap-loop Löb theorem that discharges `stvec_handler_wp`.
- **[`kerneltrap.md`](projects/kerneltrap.md)** — **`kerneltrap()` IS
  PROVEN.** `Print Assumptions` gives the 5 platform axioms + funext +
  consoleintr (inherited through devintr/uartintr) and nothing else: no
  printk-general, no `kerneltrap_returns`. All three panic arms are refuted
  from the contract's premises, which is what keeps printk out. Records the
  SPP/SPIE ghost mirror (`sret_bits`) on the trap-payload discipline, the
  `eb` generalization of `SpecYield`/`SpecSched` it forced, and three durable
  lessons (state postconditions absolutely; never leave an `_` for a frame
  word at a block boundary — it cost 141 s per `iExact`; `subst p` picks the
  wrong equation when two hypotheses define `p`). ONE thing remains: the
  `intr_handler_spec` upgrade that rewires `ProofKernelvec` off the legacy
  `KERNELTRAP_RETURNS` axiom (= explicit-cpuid Stage 2).
- **[`printk.md`](projects/printk.md)** — the formatted-output cone (printk →
  printint → consputc → uartputc_sync), ALL PROVEN and linked on the PANIC
  path (`panicking ≠ 0`, so no lock and no `intr_count` anywhere in it).
  Keeps the rejoining-arms epilogue shape, `StackBytes.v`'s frame-resident
  char array, the fuel inductions (printint's digit loop, printk's format
  loop), `PrintkFmt.v` — the pure model of which varargs a format string
  consumes, which is what makes printk's variadic precondition statable —
  and the loop-assembly architecture (one-turn lemma at 0x86 with its two
  futures as an `∧`-conjunction). Only the general (non-panic) path remains,
  blocked on uartputc_sync's.
- **[`user-verified.md`](projects/user-verified.md)** — VERIFIED user-mode
  execution (the Umode tier): the `uv_cap` capability (the sie-cap analog
  carrying the kernel's interrupt + syscall trap services as assumed
  round-trip contracts), the concrete-image memory layer (`umem`/`uinstr`
  over user VAs), the interrupt-absorbing step engine with hart-switching
  continuations, the Umode leaf WPs, and the sync program's function proofs
  (start/main + the sync/exit ecall stubs).
- **[`uart-driver.md`](projects/uart-driver.md)** — the interrupt-driven UART
  driver: uartwrite, uartintr and uartgetc, all proven (uart.c 4/4). The
  `tx_lock` invariant (`UartTxInv.v`) whose implication "`tx_busy == 0` ⟹
  everything accepted has been transmitted" is what licenses uartwrite's THR
  store with no THRE poll and what uartintr's THRE arm re-establishes — the two
  functions meet there and nowhere else. Also: why the transmitter token has to
  live in that lock (and the resulting tension with uartputc_sync's caller-held
  token), the `uart_sent_sub` SUBLIST output claim a driver that sleeps between
  bytes can honestly make, the ghost-free UART read leaf (`uart_read_stable`)
  that lets the rx drain run outside the critical section, and how to state a
  `static` helper that gcc INLINED away (uartgetc has no symbol). consoleintr
  is the cone's one assumption. Remaining: consolewrite, consoleintr, devintr,
  boot wiring.


### `completed/` — finished projects, archived for reference

- **[`crash.md`](completed/crash.md)** — the completed crash/power-cycling
  layer through M6. `SystemAdequacy.xv6_power_adequacy` proves reducibility
  across arbitrary power cycles, hart scheduling, and device steps; the FS
  durability instantiation and torn-write model are separate future work.
- **[`park-to-lock.md`](completed/park-to-lock.md)** — the global
  parked-scheduler invariant `scheds_inv`, deleted. The parked `scheduler()`
  record moved into the running proc's own `p->lock` (`SchedCtx.run_slot`),
  paid for by the HART TAG — the per-proc `ghost_var CPU` naming the hart a
  RUNNING proc runs on, and the only thing that can collapse the slot's `∃ h`
  (the `cpus[h].proc` cell cannot: it is keyed on a hart, the tag on a proc).
  `cpus[h].proc` is consequently NOT split — the whole cell sits in
  `IntrDefs.cpu_cells` and the scheduler's two stores to it are plain stores.
  Keeps the finding that closed `kerneltrap.md`'s open fork (when a resource
  seems to need threading somewhere unreachable, check whether the taker
  already holds a lock on the thing it is about) and the two syntactic wrecks
  a ~260-site premise sweep left that grepping for the deleted NAMES cannot
  find. Design in [`design/proc-struct.md`](design/proc-struct.md).
- **[`sail-model-bump.md`](completed/sail-model-bump.md)** — the sail-riscv
  model bump: the model now comes from the `zeldovich/sail-riscv` FORK (pinned
  by `SAIL_RISCV_REV`), whose delta is the ATOMIC PTE A/D-bit update, and whose
  tip carried 58 upstream commits along with it. The headline finding: the bump
  moved the misaligned split in TWO directions at once — `vmem_*_addr` now
  splits only across a PAGE boundary (at most two ways, one translation each)
  while the MAG/alignment split moved DOWN into `checked_mem_*`, under a single
  translation and with no fault of its own — so the iris-level work is per PAGE,
  not per chunk. Keeps the peel recipes and their traps, the physical split kit
  (`MemAccessGen`'s N-chunk loops and width-generic RAM leaves, `UserMemMis`'s
  chunk-plan derivation), the two platform conjuncts `pma_allows_all` had to
  gain (misaligned-exceptions None, reservability ≠ RsrvNone) and why, and FOUR
  findings worth reading before any interface sweep of this kind: a 30-minute
  "hang" that was a mis-stated `∀`-premise (and that `coqc -time` localises in
  two minutes); why pinning a platform field beat threading a disjunction
  through five altitudes; how a WEAKENED upstream `assert` made a dead branch
  live (the shadow-stack PTE, and the `forall s` argument that kills it again);
  and `pmaCheck`'s Atomic arm compiling to a match on the op.
- **[`explicit-cpuid.md`](completed/explicit-cpuid.md)** — the ambient `CpuId`
  removed from every WP statement, so a step's continuation is about the hart
  execution RESUMES on rather than the one it started on. `wp_next` and its two
  escape hatches (interrupts off; no current proc), the SIE-arm index `b`, tp
  pinned to the hart (`HartTp.v`), the canonical per-hart SIE ghost, `cpu_own`
  riding the enabled arm, and the parked-scheduler record made hart-free so it
  stopped being carried across migrations (that project put it in a global
  invariant `scheds_inv`; `completed/park-to-lock.md` has since moved it into
  the running proc's own `p->lock` and deleted the invariant). Keeps the
  scoreboard of SIX contracts that were stated falsely and compiled anyway (and
  what each got wrong), the 25 surprises, and the retrospective on why this
  should have been six expand/contract cycles rather than one big-bang branch.
  **STAGE 2 REMAINS and is future work**: making the migration real in the
  engines (`intr_handler_spec`'s continuation, `WpIntrInv`'s `iLöb`) is gated
  on `kerneltrap` actually being proved — see the file's last section, and the
  explicit obligation `wp_next`'s second hatch places on it.
- **[`explicit-cpuid-porting-guide.md`](completed/explicit-cpuid-porting-guide.md)** —
  the mechanical per-file recipe for that sweep. Still worth reading before any
  interface sweep of this kind: most of it is about failure modes that COMPILE
  (a vacuous contract, a wrong-hart read, a dropped conjunct, a non-terminating
  `iSpecialize` one leaf after the mistake).
- **[`sched-hart-generic.md`](completed/sched-hart-generic.md)** — G5 part 2:
  the parked-proc resumption contract (`p_sched`) quantifies the RESUMING hart
  inside the payload instead of pinning the ambient `cid_word`, so
  `procs_inv Φ γs` is one hart-independent proposition the `started` payload
  can carry. All EIGHT sleepers (acquiresleep, sys_pause, piperead, pipewrite,
  uartwrite, virtio_disk_rw, bread, bwrite) were re-proven against the new
  contracts; no `Axiom` of this project remains. Keeps the extraction recipe
  (`CID` as a lemma binder outside the fixing section), the collapsed-`wp_next`
  port recipe, WHICH joins actually need anchoring, the resolved
  `trap_csrs_pay`-across-a-park blocker, and the failure modes that compile
  (`Typeclasses Opaque cpu_own`, per-hart `cid_word` facts, per-hart `instr`).
- **[`kpt-share.md`](completed/kpt-share.md)** — G5 part 1: the kernel page
  table SHARED across harts, so `kvminithart` has ONE hart-generic contract
  (consumes only the persistent `kpt_inv root` + the `↦₈□` root cell; the
  publication — persist root, `kvm_M_mint`, `kpt_inv_alloc` — is a boot-hart
  assembly in ProofMain's kvm group). Keeps why a fraction cannot work, the
  one-shot-agreement `kpt_lb` ghost over the A/D-canonical tree (leaf-only
  canonicalisation is load-bearing for soundness), the mask-carrying
  `sr_absorb` call form, `kpt_inv_snapshot` (any tree serves an
  empty-TLB re-entry), and the satp-window follow-up (the userret/uservec
  island keeps the exclusive `tlb_inv_pt`).
- **[`bare-inv-generic.md`](completed/bare-inv-generic.md)** — G5 part 3:
  the Bare translation arm made PER-HART (`bare_inv` holds only this hart's
  satp/PMP cells; the global `kmap_auth kmap_M0` became a boot token routed
  adequacy → main → kvminithart). The `s_regime` fields `sr_adm`/`sr_adm_id`,
  why a claim's admissibility can never be *refuted* per-hart, and the move
  that kept the premise out of every leaf statement: `↦ₘ`/`↦ₓ` carry the
  identity `pa_of ppn va = va`. Also the consequence to know before touching
  kernel stacks — a kstack byte is not a `↦ₘ`, and the way in is a
  KPT-regime leaf family.

Projects with no outstanding steps, tasks, or cleanup. Kept (not deleted) for
their durable design notes, gotchas, and reusable recipes.

- **[`fileclose.md`](completed/fileclose.md)** — `fileclose`, PROVEN and
  LINKED, and with it the four functions that were waiting on it: pipealloc,
  sys_close, sys_pipe and kexit are all linked now too. Keeps the payload
  link's design (a `file_ref` carries the pipe end / inode reference it
  names, so the last closer has a whole `pipe_ref` to hand `pipeclose`), the
  TYPE-INDEXED callee environment that keeps pipealloc from being made to
  own a file system, the `ProcInv.proc_priv_pid_ofile` accessor kexit's loop
  needed, and two gotchas worth reading before any block lemma with a branch
  in it: `vm_compute` on a jump target that is still open does not come back,
  and a lazily-spilled callee-saved register makes `callee_saved` a PREMISE
  of the epilogue rather than a consequence of its loads. Design in
  [`design/file-table.md`](design/file-table.md).
- **[`kexit.md`](completed/kexit.md)** — `kexit()`, the process-lifetime
  cone's other half, PROVEN and LINKED. Keeps the protocol change it needed:
  parking at ZOMBIE is a different kind of park, because a zombie's private
  block cannot ride the parked closure — wait()/freeproc, running on another
  process, must find the user page table in `p->lock` — so the crossing
  carries the block MINUS its context cells and the reclaiming scheduler puts
  the two back together, FORGETTING the zombie's record down to its cells
  rather than claiming it resumable. Also `SpecIput.v` (the cone's one
  assumption), the diverging-contract shape, why having no epilogue keeps the
  frame out of the loop, and the `proc_priv_pid_ofile` accessor its fd loop
  needed once fileclose's file-system arm wanted a pid cell out of the very
  block the loop walks.
- **[`sys-pipe.md`](completed/sys-pipe.md)** — sys_pipe, PROVEN and LINKED:
  the syscall where the file/proc model has to balance — two `fd_slot`s in,
  two out on all four exits, which is what forced filealloc's and pipealloc's
  failure arms to start returning their units. Keeps `SpecFdalloc.v`'s
  `fd_frees` pure layer (what makes two successive fdalloc calls compose), the
  two shared-block lemmas, and what the contract deliberately does not say.
- **[`bio.md`](completed/bio.md)** — the buffer cache: the settled ownership
  design (the per-buffer content ESCROW — a namespace invariant with a
  parked arm and a checked-out arm — over a sleeplock that protects only a
  checkout token; the Arc-algebra refcount with real dev/blockno cell
  fractions; the finite `bslot` supply that makes the unchecked refcnt++
  provable), why the two obvious models fail, `BufOwn.v`'s ½-blockno
  `buf_own`, the five function contracts, and the worklist (binit was
  already proven; bget is inlined into bread).
- **[`fs-log-bio-and-logc.md`](completed/fs-log-bio-and-logc.md)** — stages
  1–3 of the FS block layer: the Ψ-parametric bio rework (the three escrow
  arms, the uncached pool, the three interface facts the re-proofs turned up,
  and `ProofBreadParts.v`'s reusable vocabulary), `LogInv.v` + the six log.c
  specs (the reservation LEDGER and why a flat counter is not inductive; the
  batch's slot pool), and their whole-function proofs. Stage 4 (the crash
  instantiation) is still in flight — see
  [`projects/fs-log.md`](projects/fs-log.md).
- **[`virtio-disk.md`](completed/virtio-disk.md)** — the virtio disk device,
  end to end: the machine side (`VirtioModel.v`/`WpVirtio.v`, the DMA lease,
  `wp_dev_loop`), the whole driver side (`virtio_disk_init`/`_rw`/`_intr` +
  `free_desc`, `virtio_disk.c` 4/4), and the boot seam
  (`DiskBoot.disk_res_boot` → main's disk-lock `newlock`, so what leaves `main`
  is `is_lock … (disk_res …)` ∗ `disk_geom`). Keeps the DMA-lease design and
  the rule it came from — model undefined device behaviour as "anything", never
  as "nothing", or a driver satisfies its obligation vacuously — plus the
  modelling choices and why each is safe. What it deliberately does not say is
  what a block device IS to the file system; that spec is its own effort.
- **[`virtio-disk-rw.md`](completed/virtio-disk-rw.md)** — the record of the
  headline driver proof `virtio_disk_rw`: the phase map (P1..P6), the seam each
  phase hands the next, the one protocol-spec change P6 forced (`vs_data` for
  READ requests — an invariant that takes an exclusive ghost fragment across a
  sleep must RECORD its value), and ~30 gotchas already paid for.
- **[`scheduler.md`](completed/scheduler.md)** — scheduler(), the per-CPU
  dispatch loop, PROVEN: the tree's first DIVERGING whole-function spec (no
  continuation; proof_coverage.py learned the shape), the 4-place
  chain-payload refactor (the crossing's c->proc index made visible to
  `p_sched`, which is what lets the resumed scheduler identify the parking
  proc with its scan cursor — its release needs exactly that lock), the
  level-0 SIE flip leaves for the inlined intr_on/intr_off, the eb/trap_csrs
  accounting (a dispatch round legitimately re-enables interrupts mid-scan;
  `found = 0 → SIE off` is what makes the wfi provable at SIE=0), the wfi
  stutter-loop leaf (`WpSmodeWfi.v` — the model wakes on `mip & mie ≠ 0`,
  no SIE gate, TW dead), and the three-□-loop proof structure.
- **[`pt-teardown-copy.md`](completed/pt-teardown-copy.md)** — freewalk / uvmfree /
  uvmcopy / uvmclear: the page-table TEARDOWN path, fork's address-space COPY
  and exec's guard-page edit — **vm.c is 20/20 functions and 100 % of its
  bytes**. Keeps the two invariant changes they forced — `PtTree.pt_node_claim`
  now records that a page-table node's page is a kalloc page (so no contract
  had to grow a conjunct), and `BarePt.v`'s single `otf` axis, which states
  the parked user table with OR without its trampoline/trapframe leaves and
  lets uvmunmap be proved once and **sealed twice** — plus freewalk's
  recursion recipe (a named `Prop` contract + hand-staged strong induction,
  which is what makes a recursive function's proof splittable),
  `uvm_perm_ok_of_leaf` (why uvmcopy's contract can ask the caller nothing
  about the permission it copies), and the A/D subtlety that made the first
  draft of uvmcopy's postcondition false.
- **[`growproc.md`](completed/growproc.md)** — growproc AND sys_sbrk, proven and linked,
  and the **`p->sz` ⇄ user-map coherence invariant** it forced: `um_below`
  and the tightened size bound inside `proc_priv`, the `uptd_ext_sz`
  relation copyin/copyout now hand back (a bare `uptd_ext` cannot rebuild
  the block), the uvm* range premises relaxed to `<= uvm_maxsz` because the
  old ones were undischargeable by their only caller, and the GUARD on
  `uvmd_np` that makes `sbrk(-1)`'s wrapped `sz + n` say the truth. Also the
  one-`iAssert`-EXIT shape for a function whose shared blocks want the same
  linear resource. sys_sbrk's LAZY path is the argument for why `um_below`
  is an inequality rather than an equality — it raises `p->sz` and maps
  nothing.
- **[`uvm-alloc-unmap.md`](completed/uvm-alloc-unmap.md)** — uvmunmap /
  uvmdealloc / uvmalloc, all three proven and linked: growing and shrinking a
  process's address space at the `proc_pt` altitude. Keeps the `um_inj`
  (no-aliasing) strengthening of `proc_pt_wf` and why OWNERSHIP, not a caller
  premise, re-establishes it; the perm-generic leaf layer (`uvm_pte` /
  `uvm_perm_ok` + the four instances) that a runtime `xperm` forced; the run
  vocabulary (`um_del_run` / `vpn_run` / `uptd_del_run`) and
  `um_del_run_restore`, the law that makes uvmalloc's failure arm give back
  exactly the descriptor it was handed; and the measured finding that a
  helper-relocation sweep over cheap `lia`/`rvc_oneshot` helpers is
  compile-time NEUTRAL — structural payoff only, unlike the copy-inout sweep.
- **[`string-args.md`](completed/string-args.md)** — the string-argument cone
  (argstr → argraw + fetchstr → myproc + copyinstr + strlen), all four proven
  and linked: `ByteBuf`'s `bb_nonul`/`bb_cstr` vocabulary (a NUL-terminated
  string as a property of the buffer's NAMING FUNCTION, which is what makes
  copyinstr's and strlen's contracts compose with nothing in between), why a
  CONTENTS postcondition forbids the `bb_join3` chunk-split copyin uses and
  wants `bb_byte_acc` instead, copyinstr's two nested loops (the outer counter
  recovered from two POINTERS, the inner cursor indexed off the chunk base,
  fuel-outside/`nat`-inside induction, the dead `beqz`), strlen's off-by-one
  cursor and its `subw` pointer-difference return, and argstr's INLINED
  argaddr. The consumers (`sys_open`, `sys_exec`, …) are the syscall worklist
  in [`proc-struct-resources.md`](projects/proc-struct-resources.md), not this
  cone.
- **[`pipe-rw.md`](completed/pipe-rw.md)** — piperead / pipewrite, both proven
  and linked: the queue-coupling conjunct in `pipe_res`, the SLEEP_GEN
  generalization (sleeping on a cancellable lock — the sleeper's own reference
  keeps the object alive through sched), the interrupt-level generalization it
  forced through the vmfault/copyin/copyout and walk/mappages chains, the
  iLöb + fuel loop structures, and the shrink-wrapped-epilogue and
  `∧`-conjoined-exit gotchas both proofs hit.
- **[`either-copy.md`](completed/either-copy.md)** — either_copyout /
  either_copyin, both proven and linked: the pair whose destination (resp.
  source) is a USER or a KERNEL pointer depending on a run-time flag, which is
  what forced the flag into the contract as a ghost boolean and made the
  precondition, the postcondition and two numeric premises `if user then …
  else …` — including why `proc_priv` is required only on the user arm and why
  the kernel arm's length bound is the tighter one (`sext.w`). Also: `ec_epi`,
  the epilogue of a block gcc emitted TWICE proved once and instantiated at
  both addresses, and a decode-word + load-shape dedup sweep (14 private
  copies of 6 words, plus 5 copies of 3 load-shape lemmas, retired).
- **[`copy-inout.md`](completed/copy-inout.md)** — copyin / copyout (+ the
  `walkaddr` callee), all three proven: the kernel↔user byte-copy pair at the
  `proc_pt` altitude, so both PRESERVE the user-page-table invariant and hand
  back a descriptor EXTENDING the one they were given (`uptd_ext`).  Keeps the
  per-page accessor (`proc_pt_page_acc`, the `↦ₚ ⇄ ↦ₘ` move a memmove through
  a user page needs), `ByteBuf.v`'s buffer algebra, why the contracts
  deliberately say nothing about the bytes that crossed, the walkaddr PTE2PA
  high-bit correction, copyout's un-null-checked `walk` result, the fuel-not-
  count loop induction, and the cleanup sweep's measured payoff.
- **[`vmfault.md`](completed/vmfault.md)** — vmfault + ismapped (+ the no-alloc
  walk spec), all proven: the lazy-allocation page-fault handler, stated at the
  `proc_pt` altitude so it PRESERVES the valid-user-page-table invariant.
  Keeps the `upt_tree_spec` blocks0 strengthening, the `pt_rep0 ⇄
  upt_tree_spec` bridge (`upt_ad_view`) that dovetails the runtime
  mappages/walk specs with the user-table invariant, the shrink-wrapped
  five-arm epilogue-join recipe, and the MAXVA vpn-bound correction
  (tf_vpn = 2^26−2, not 2^27−2).
- **[`lock-cancel-pipeclose.md`](completed/lock-cancel-pipeclose.md)** — making
  a lock's storage reclaimable (`lock_openable` with the credential quantified
  inside the accessor, `lock_finisher`, release proved once and instantiated
  twice) and proving `pipeclose`, which frees a pipe's page. Keeps the argument
  for why `cinv` cannot lock a multiply-owned object, and the join structure a
  whole-function proof with rejoining arms needs.
- **[`rwx-kmap.md`](completed/rwx-kmap.md)** — the R/W/X-accurate kernel page
  table and the kernel mapping model: one claim ghost for identity AND
  non-identity mappings, VA-based `↦ₘ`/`↦ₓ` (a store to kernel text is
  unprovable), the physical tier `↦ₚ` and the boot switch. (Its
  `page_own_kstack` capstone is superseded — `↦ₘ` carries the identity
  conjunct now, see `completed/bare-inv-generic.md`.) The live design is in
  [`design/tlb-translation.md`](design/tlb-translation.md); the archive keeps
  the decision record, including the two cleanups deliberately NOT done (the
  heap-domain invariant, and slot-generic `intr_frame`).
- **[`kvm-spec.md`](completed/kvm-spec.md)** — the kvminit / kvmmake / kvmmap /
  mappages / walk proofs (`KvmSpec.v`), all sealed and linked: the counted-kalloc
  tier (`avail_sub`, the additive `∃g` growth form), the `pt_rep0` zero-stop-word
  map view, the `kvm_map` literal + `kvm_bridge`, and the large-pure-map
  proof-engineering landmines.
- **[`yield-sched.md`](completed/yield-sched.md)** — yield/sched/myproc specs and
  proofs (S1–S9 complete): the sconf-tier swtch port, the global scheduler-chain predicate
  `P_sched`, the ▷-guarded proc-lock context slot, and the `cur_proc` resource.
- **[`memmove.md`](completed/memmove.md)** — memmove, proven for non-overlapping
  ranges, where the non-overlap hypothesis is carried by SEPARATION (the two
  buffers as separate conjuncts) rather than a pure side condition, so the
  source's descending-copy arm closes by contradiction and is never even
  decoded. Also: `ByteCursor.v` (the shared byte-loop arithmetic) and the
  register-map rewrite gotchas the proof turned up.
- **[`proc-pagetable.md`](completed/proc-pagetable.md)** — proc_pagetable +
  uvmcreate: the user page table's CONSTRUCTION side (the execution side is
  UptTree/userret). `ProcPt.v`'s `ppt_bridge` carries the built table to
  `upt_tree_spec`; counted-budget-only, so both error tails (uvmfree /
  uvmunmap, unverified) are dead.
- **[`sleeplock.md`](completed/sleeplock.md)** — the sleeplock subsystem, all
  four functions proven (initsleeplock / acquiresleep / releasesleep /
  holdingsleep): the `is_sleeplock`/`sl_res` lock abstraction over the inner
  spinlock, the holder-carried pid cell, and acquiresleep's sleep-retry iLöb
  loop over the proven `SLEEP` interface.
- **[`sie-cap-avail.md`](completed/sie-cap-avail.md)** — folded the free stack
  into the sie capability with an avail parameter (avail = slots available to kernel code); sp
  push/pop specs (`wp_caddi{,16}sp_{push,pop}_s_sconf`), the sp-aware VCgen
  executor, and the whole function tier (mycpu … kvmmap, plus the kinit cone)
  ported off the separate deep-`stack_own` conjunct. Full clean build green.
- **[`plic-init-spec.md`](completed/plic-init-spec.md)** — plicinit /
  plicinithart / plic_claim / plic_complete specs & proofs (+ cpuid, + the
  width-4 PLIC S-mode device-access infrastructure, both directions); plic.c is
  4/4. Keeps the reason no function here owns PLIC state — the gateway latches
  whenever an irq line is up, so the fragment can never sit raw in a CPU's
  precondition, not even during boot-time init on hart 0 — and the universal
  obligation that follows (`∀ p, plic_ok p → …`), which is why `plic_ok` has to
  be weak and per-hart-local: a hart preserves it from its OWN two writes,
  knowing nothing about the others. `WpPlic.v`'s two width-4 store leaves differ
  only in which invariant they open (`plic_inv` vs the `dev_inv` bundle).
- **[`kinit-cone.md`](completed/kinit-cone.md)** — the kinit cone (kinit →
  initlock + freerange, over kfree), all proved axiom-clean over sconf. The
  page-count token is threaded through to kinit's postcondition; the caller
  supplies the pages precondition.
- **[`spec-module-migration.md`](completed/spec-module-migration.md)** — all 19
  whole-function proofs moved onto the spec / sealed-functor / link shape; no
  function proof depends on another function's proof any more. The recipe lives
  in [`design/spec-modules.md`](design/spec-modules.md).
- **[`user-mode-ptree-port.md`](completed/user-mode-ptree-port.md)** — porting
  user-mode execution onto the ptree page-table layer (UserPt → `utlb_inv_pt`);
  the port and its cleanup are done. The execution-side story is finished in
  [`user-mode-exec-v2.md`](completed/user-mode-exec-v2.md).
- **[`user-mode-exec-v2.md`](completed/user-mode-exec-v2.md)** — arbitrary
  user-mode execution (v2: `UserPt.v` / `UserExec.v`). `wp_user_exec_closed` is
  the complete WP with no totality hypotheses; the userret → `user_inv` bridge is
  built. Only the kernel-side uservec proof (E-uservec, which would discharge the
  assumed `stvec_handler_wp`) is left, and it is not user-mode-execution work.
- **[`regfile-migration.md`](completed/regfile-migration.md)** — the register
  file is a function `regfile := regidx → mword 64` (`RegFile.v`), not a `gmap`;
  whole tree on it (~30× on funnel lookups). Keeps the `RegFile` interface, the
  `rf_upd` transparency / async-`Qed` hazard (always discharge with
  `reg_lookup`), when to prefer the lemma-based `peel_reg` instead, and what to
  do in a new file that threads register maps.
- **[`interrupt-sweep.md`](completed/interrupt-sweep.md)** — made every S-mode
  execution lemma SIE-agnostic; all S-mode whole-function proofs are over `sconf`
  on the sie-cap-avail interface. Keeps the `sconf`/`sie_cap`/`intr_count`
  architecture, the avail-param push/pop conventions, and the reusable recipes.
  Two consumer-side items are PARKED there with no owner: the boot wiring that
  would drive the sconf layer (`main`; `trapinithart` and the `csrw stvec` leaf
  it needed are done) and wiring `wp_vc_block_s_sconf` into the whole-function
  proofs.

When a project is fully finished — no remaining work and no cleanup — move its
file from `projects/` to `completed/` (rather than deleting it), so its durable
lessons stay available. See "Maintaining these notes" in `durable-notes.md`.
