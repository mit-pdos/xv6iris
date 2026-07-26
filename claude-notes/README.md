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
- **[`kernel-proofs.md`](design/kernel-proofs.md)** — kernel-side proof
  architecture (swtch/contexts, proc locks/wakeup, loop shapes), whole-function
  WP specs (`callee_saved`/`stack_own`), spinlocks (`WpLock.v`), and the kernel
  data-structure layout.

### `projects/` — ongoing worklists & plans (one per effort)

- **[`rwx-kmap.md`](projects/rwx-kmap.md)** — uniform-claims model and RAM-bounds cleanup complete (2026-07-24); stage 6 (boot switch) remains:
  R/W/X-accurate kernel PT (text RX / data RW), the code points-to `↦ₓ`
  inside `instr`, the monotone kernel-mapping claim ghost for non-identity
  mappings, and `mem_pointsto`/`node_kdata` generalization to `addr_is_ram`.
- **[`kvm-spec.md`](projects/kvm-spec.md)** — the kvminit / kvmmake / kvmmap /
  mappages / walk proofs (`KvmSpec.v`).
- **[`plic-init-spec.md`](projects/plic-init-spec.md)** — plicinit / plicinithart
  specs & proofs (+ cpuid, + the width-4 PLIC S-mode device-store infrastructure).
- **[`virtio-disk.md`](projects/virtio-disk.md)** — the virtio disk device: the
  machine side (`VirtioModel.v`/`WpVirtio.v`, the DMA lease, `wp_dev_loop`) is
  done; the driver side (`virtio_disk_init`/`_rw`/`_intr`, the width-4 S-mode
  MMIO leaves, the lease-transfer protocol) is the remaining work.

### `completed/` — finished projects, archived for reference

Projects with no outstanding steps, tasks, or cleanup. Kept (not deleted) for
their durable design notes, gotchas, and reusable recipes.

- **[`yield-sched.md`](completed/yield-sched.md)** — yield/sched/myproc specs and
  proofs (S1–S9 complete): the sconf-tier swtch port, the global scheduler-chain predicate
  `P_sched`, the ▷-guarded proc-lock context slot, and the `cur_proc` resource.
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
  would drive the sconf layer (`main`→`trapinithart`) and wiring
  `wp_vc_block_s_sconf` into the whole-function proofs.

When a project is fully finished — no remaining work and no cleanup — move its
file from `projects/` to `completed/` (rather than deleting it), so its durable
lessons stay available. See "Maintaining these notes" in `durable-notes.md`.
