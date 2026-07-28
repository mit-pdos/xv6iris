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

### `design/` — how each part of the project is built

- **[`execution-model.md`](design/execution-model.md)** — the Sail model & WP
  exec stack (`run`/`exec`, `wp_exec_step` layering), the clock tick, the
  minstret invariant, the register file, memory points-to & dfrac, config
  bundles (`hw_config`/`mmode_config`/`smode_config`), fetch geometry, and the
  fast concrete-state decode bridge.
- **[`code-organization.md`](design/code-organization.md)** — where WP leaf
  lemmas live (`Wp<Mode><Family>.v`), import discipline, lemma-altitude rules,
  and specific-vs-generic leaf lemmas.
- **[`smode-and-vcgen.md`](design/smode-and-vcgen.md)** — the S-mode config
  convention (`_scfg` wrappers, SIE ghost), recovering a concrete register map
  from a VCgen block, and straight-line VCgen blocks.
- **[`interrupts.md`](design/interrupts.md)** — interrupt dispatch: the
  keystones, the interrupt invariant + absorbing step engine, the SIE-agnostic
  v2 bundle (`sconf`/`sie_cap`), and the interrupt-stack file layout.
- **[`multi-cpu.md`](design/multi-cpu.md)** — the ambient-hart multi-CPU model.
- **[`adequacy.md`](design/adequacy.md)** — whole-system adequacy
  (`RiscvAdequacy.v`).
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

- **[`proc-struct-resources.md`](projects/proc-struct-resources.md)** — the
  `struct proc` resource split: what has landed (`ProcInv.v`, `procinit`,
  `argraw`/`argint`/`argaddr`, `argfd`, `killed`, `sys_getpid`, `sys_close`,
  `sys_pause`, `fetchaddr`, `fdalloc`) and what is next (the remaining
  syscalls, and `cwd_ref`). Keeps the measured account of why
  `argraw`'s six-arm proof cost 74 GB, sys_pause's path-dependent-frame
  recipe, — from fetchaddr, the first function spanning the `proc_priv`
  and bare-cell tiers — the `proc_priv_copy` accessor and the x0-as-source
  (`snez`/`negw`) recipe, and, from fdalloc, the fuel-induction descriptor
  scan and why the loop's continuation must be a premise of the loop
  statement rather than a resource in its context.  Its worklist now leads
  with `proc_priv_owe`, the payload-deficit predicate `sys_dup` needs.
- **[`plic-init-spec.md`](projects/plic-init-spec.md)** — plicinit / plicinithart
  specs & proofs (+ cpuid, + the width-4 PLIC S-mode device-store infrastructure).
- **[`proc-pagetable-ownership.md`](projects/proc-pagetable-ownership.md)** —
  the process page table's OWNERSHIP side (`ProcPtOwn.v`): `proc_pt`, one
  predicate for a valid parked user table — trampoline + trapframe + the pages
  it OWNS — the footprint derived from `um` (retiring `uptd`'s `ud_data`
  field), the physical-tier decision, the `page_own ⇄ udata_own` bridges, and
  the worklist for folding `UserPtTree.user_pt_inv` onto it. The CONSTRUCTION
  side is [`completed/proc-pagetable.md`](completed/proc-pagetable.md); they
  meet at `ProcPtOwn.proc_pt_intro_ppt`.
- **[`lock-cancel-pipeclose.md`](completed/lock-cancel-pipeclose.md)** — moved
  to `completed/`.
- **[`uservec.md`](projects/uservec.md)** — uservec (the user-mode trap
  handler), PROVEN — trampoline.S is 100% covered: the boundary specs
  (SpecUserret/SpecUservec/SpecUsertrap, the userret→user-exec dovetail
  `UserretUser.v`), the TVM/TSR mstatus-pin extension, the proof's file
  split (catalog / store+CSR leaves / reverse pt2 switch / chain) with its
  reusable lessons, and the remaining work: prove usertrap(), then the
  whole-trap-loop Löb theorem that discharges `stvec_handler_wp`.
- **[`printk.md`](projects/printk.md)** — the formatted-output cone (printk →
  printint → consputc → uartputc_sync), verified on the PANIC path
  (`panicking ≠ 0`, so no lock and no `intr_count` anywhere in it): consputc and
  printint are proven — with the rejoining-arms epilogue shape, `StackBytes.v`'s
  frame-resident char array, and the fuel induction that bounds printint's
  digit loop inside `buf[20]` — and printk is specified, including
  `PrintkFmt.v`, the pure model of which varargs a format string consumes,
  which is what makes printk's variadic precondition statable.
- **[`sys-pipe.md`](projects/sys-pipe.md)** — sys_pipe, PROVEN (unlinked): the
  syscall where the file/proc model has to balance — two `fd_slot`s in, two out
  on all four exits, which is what forced filealloc's and pipealloc's failure
  arms to start returning their units. Keeps `SpecFdalloc.v`'s `fd_frees` pure
  layer (what makes two successive fdalloc calls compose), the two
  shared-block lemmas, what the contract deliberately does not say, and the
  remaining work (proving argaddr and fdalloc).
- **[`virtio-disk.md`](projects/virtio-disk.md)** — the virtio disk device: the
  machine side (`VirtioModel.v`/`WpVirtio.v`, the DMA lease, `wp_dev_loop`) is
  done; the driver side (`virtio_disk_init`/`_rw`/`_intr`, the width-4 S-mode
  MMIO leaves, the lease-transfer protocol) is the remaining work.

### `completed/` — finished projects, archived for reference

Projects with no outstanding steps, tasks, or cleanup. Kept (not deleted) for
their durable design notes, gotchas, and reusable recipes.

- **[`pipe-rw.md`](completed/pipe-rw.md)** — piperead / pipewrite, both proven
  and linked: the queue-coupling conjunct in `pipe_res`, the SLEEP_GEN
  generalization (sleeping on a cancellable lock — the sleeper's own reference
  keeps the object alive through sched), the interrupt-level generalization it
  forced through the vmfault/copyin/copyout and walk/mappages chains, the
  iLöb + fuel loop structures, and the shrink-wrapped-epilogue and
  `∧`-conjoined-exit gotchas both proofs hit.
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
  unprovable), the physical tier `↦ₚ`, the boot switch, and
  `page_own_kstack`. The live design is in
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
