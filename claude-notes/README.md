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
  opam / profiling instructions, proofmode & bitvector gotchas, and durable
  spec-design preferences.
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
  UART + PLIC), `DevModel.v`/`WpUart.v`, the four device ghosts, and the
  S-mode instruction-level UART access layer.
- **[`tlb-translation.md`](design/tlb-translation.md)** — the kvmmake-faithful
  all-4KB kernel page table, TLB/page-walk/translation, userret / trampoline /
  user page table, and the `CommonWalk.v` page-table-walk proof technique.
- **[`kernel-proofs.md`](design/kernel-proofs.md)** — kernel-side proof
  architecture (swtch/contexts, proc locks/wakeup, loop shapes), whole-function
  WP specs (`callee_saved`/`stack_own`), spinlocks (`WpLock.v`), and the kernel
  data-structure layout.

### `projects/` — ongoing worklists & plans (one per effort)

- **[`interrupt-sweep.md`](projects/interrupt-sweep.md)** — making every S-mode
  execution lemma SIE-agnostic (the interrupt sweep).
- **[`kinit-cone.md`](projects/kinit-cone.md)** — the kinit cone (kinit →
  initlock + freerange, over kfree).
- **[`kvm-spec.md`](projects/kvm-spec.md)** — the kvminit / kvmmake / kvmmap /
  mappages / walk proofs (`KvmSpec.v`).
- **[`user-mode-ptree-port.md`](projects/user-mode-ptree-port.md)** — porting
  user-mode execution onto the ptree page-table layer (UserPt → `utlb_inv_pt`).
- **[`user-mode-exec-v2.md`](projects/user-mode-exec-v2.md)** — arbitrary
  user-mode execution (v2: `UserPt.v` / `UserExec.v`).

When a project lands, delete its file here after lifting any durable lessons
into `durable-notes.md` or the relevant `design/` file (see "Maintaining these
notes" in `durable-notes.md`).
