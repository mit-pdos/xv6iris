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
  statement rather than a resource in its context.  **`allocproc` is proven,
  linked and AXIOM-FREE** (allocpid with it) -- the one PRODUCER of
  `proc_priv`, and where the user page table's construction and ownership
  sides meet -- but counted-only; the
  worklist spells out the exact chain that makes it work in `kfork`'s
  uncounted regime (uvmcreate -> proc_pagetable -> freeproc), plus
  `proc_priv_owe`, the payload-deficit predicate `sys_dup` needs.
- **[`main-boot.md`](projects/main-boot.md)** — `main()`. The BOOT ARM IS
  PROVEN (main.c 178/178 bytes; axiom footprint = printk-general + userinit
  + kerneltrap): `WpMainDecode.v`, `StartedInv.v` (the `started` flag as a
  one-shot escrow with a PERSISTENT payload), `SpecMain.v` (deposit as a
  □-wand main applies at the `started = 1` store), `ProofMain.v` (six
  bare-`WP Loop` call-group lemmas; no `callee_saved` threading — main
  never returns). The file keeps the resolved-blocker record (G1's
  time-0 device invariants + init-under-invariant rework, G2/G3 assumed
  interfaces, G4's later-stripping fence leaf), the callee-by-callee
  resource inventory, the assemblies main performs, and what remains:
  the secondary arm (G5 — see [`kpt-share.md`](projects/kpt-share.md))
  and the whole-system adequacy composition.
- **[`kpt-share.md`](projects/kpt-share.md)** — sharing the kernel page
  table across harts (G5 part 1) so `kvminithart` gets ONE hart-generic
  contract: the `kpt_inv` invariant over the mutating tree, the
  A/D-monotone `kpt_lb` ghost + `tlb_ok_pt_ad_mono`, the mask-carrying
  `sr_absorb`, per-CPU `strans_name` — and the sequencing through
  hart-generic `p_sched`, `wp_main_secondary_sconf`, and the all-harts
  `_entry`→`start`→`main` adequacy.
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
- **[`sys-pipe.md`](projects/sys-pipe.md)** — sys_pipe, PROVEN (unlinked): the
  syscall where the file/proc model has to balance — two `fd_slot`s in, two out
  on all four exits, which is what forced filealloc's and pipealloc's failure
  arms to start returning their units. Keeps `SpecFdalloc.v`'s `fd_frees` pure
  layer (what makes two successive fdalloc calls compose), the two
  shared-block lemmas, what the contract deliberately does not say, and the one
  thing standing between sys_pipe and a `LinkSysPipe.v`: `fileclose`, its only
  callee without a proof.
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

- **[`virtio-disk.md`](projects/virtio-disk.md)** — the virtio disk device: the
  machine side (`VirtioModel.v`/`WpVirtio.v`, the DMA lease, `wp_dev_loop`) and
  the whole driver side (`virtio_disk_init`/`_rw`/`_intr` + `free_desc`, all
  proven and linked, `virtio_disk.c` 4/4) are done; the boot wiring that ties
  init's post-state to the contracts `_rw`/`_intr` consume is what remains.
- **[`virtio-disk-rw.md`](projects/virtio-disk-rw.md)** — the record of the
  headline driver proof `virtio_disk_rw` (DONE): the phase map (P1..P6), the
  seam each phase hands the next, the one protocol-spec change P6 forced
  (`vs_data` for READ requests), and ~30 gotchas already paid for.

### `completed/` — finished projects, archived for reference

Projects with no outstanding steps, tasks, or cleanup. Kept (not deleted) for
their durable design notes, gotchas, and reusable recipes.

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
- **[`plic-init-spec.md`](completed/plic-init-spec.md)** — plicinit /
  plicinithart / plic_claim / plic_complete specs & proofs (+ cpuid, + the
  width-4 PLIC S-mode device-access infrastructure, both directions); plic.c is
  4/4. Keeps the establish-vs-preserve split — plicinit runs alone on hart 0 and
  can establish a property of the PLIC, plicinithart runs on every hart and can
  only open `dev_inv` and preserve one — which is why `WpPlic.v` has two width-4
  store leaves. Its consumer-side items (`riscv_device_adequacy`'s `plic_ok`,
  and re-proving plicinit over the accessor leaves) are parked in
  [`main-boot.md`](projects/main-boot.md).
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
