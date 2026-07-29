# Project: main() — the boot function and the `started` handover

GOAL: specify and prove `main()` (kernel/main.c, `0x80000e7e .. 0x80000f2f`,
50 instructions), over the *specs* of its eighteen callees, with an invariant on
the `started` flag carrying the boot hart's initialisation to the other harts.

This is the consumer end of the boot wiring parked in
[`../completed/interrupt-sweep.md`](../completed/interrupt-sweep.md) ("item 8"):
`ENTRY.wp_entry_boot` stops at `<main>` and `SPEC*`/`Link*` exist for almost
every callee, but nothing yet DRIVES them.

## Status

**Landed (both compile, both in `_CoqProject`, full build green):**

- **`WpMainDecode.v`** — the complete decode layer, 50/50 instructions
  (`mni_00` … `mni_b0`) plus the 5 compressed and 30 base decode facts they
  consume. Nothing about main's decode is left to do.
- **`StartedInv.v`** — the `started` invariant and its three accessors
  (`started_inv_alloc`, `started_inv_load_au`, `started_inv_store_au`), shaped
  to plug straight into `wp_load_s_sconf_au` / `wp_store_s_sconf_au`
  (WpSconfMem.v) at width 4.
- **`SpecMain.v`** — the BOOT-HART contract (`wp_main_boot_sconf` +
  `Module Type MAIN`), precondition factored into `main_locks_raw` /
  `main_globals_raw` / `main_devices_raw` / `main_hart_raw`. NOTE: the
  `main_devices_raw` conjunct and the "main is what allocates the device
  invariant" comment are known-wrong pending G1's rework (see below) — the
  rest of the statement is settled.
- **`SpecPrintkGen.v` / `LinkPrintkGen.v`** and **`SpecUserinit.v` /
  `LinkUserinit.v`** — the two assumed-callee interfaces (G2, G3 below,
  both marked LANDED with their design decisions).
- **`wp_fence_gen_later_s_sconf`** (WpSconfCtl.v, G4) and
  **`procs_inv_alloc`** (SpecProcinit.v §ProcinitProcsInv — NOT SchedCtx.v:
  SchedCtx cannot import SpecProcinit, that would be a cycle). The alloc
  needed **`WpLock.newlock_delayed`** (`==∗ ∃ γ, ∀ R, R ={E}=∗ is_lock γ lk
  s R` — name first, resource later), because each proc lock's
  `proc_lock_res` mentions ALL 64 gnames through `p_sched`, so `newlock`'s
  pick-γ-and-demand-R-together shape is circular over the list. That lemma
  is the reusable tool for allocating any FAMILY of locks whose resources
  reference each other's names.

**NOT landed: `ProofMain.v` / `LinkMain.v`.** main is *not* proven. What
still blocks the boot arm is G1 alone (its rework also revises `SpecMain`'s
device conjuncts); the secondary arm additionally waits on G5. The
inventory main's precondition has to carry is §"Resource inventory", traced
callee by callee.

## The function

`main` is TWO arms joined at the tail, and it NEVER RETURNS — no epilogue, no
`jalr ra`. Its spec is therefore DIVERGING, like `scheduler`'s (`… -∗ WP Loop
{{Φ}}`, no continuation; `tools/proof_coverage.py` already knows that shape).
Offsets are what the proof's pc chain steps through:

```
  0x00..0x06  the standard 16-byte / 2-slot frame push
  0x08        jal cpuid
  0x0c..0x10  auipc a4 / addi a4          -> a4 = &started
  0x14        beqz a0, +0x2e              -- cpuid()==0 ? boot arm : secondary
  --- secondary arm -------------------------------------------------------
  0x16..0x1a  lw a5,0(a4) / sext.w a5 / beqz a5,-4     while (started == 0) ;
  0x1c        fence rw,rw                 __atomic_thread_fence(SEQ_CST)
  0x20..0x2e  printk("hart %d starting\n", cpuid())
  0x32..0x3a  kvminithart / trapinithart / plicinithart
  0x3e        jal scheduler               -- THE JOIN, and main's exit
  --- boot arm ------------------------------------------------------------
  0x42..0x9e  consoleinit printkinit printk×3 kinit kvminit kvminithart
              procinit trapinit trapinithart plicinit plicinithart binit
              iinit fileinit virtio_disk_init userinit
  0xa2        fence rw,rw
  0xa6..0xac  li a5,1 / auipc a4 / sw a5,778(a4)       started = 1
  0xb0        j 0x3e                      -- back to the join
```

Note `a4` is materialized ONCE at 0x0c/0x10 and reused by the spin loop, and
RE-materialized at 0xa8 for the store; the boot arm's `beqz` at 0x14 is the
only place `cpuid()`'s first result is used.

Two contracts, not one: `wp_main_boot_sconf` (`fin_to_nat cpu_id = 0`, entered
with the whole boot supply) and `wp_main_secondary_sconf` (`≠ 0`, entered with
only this hart's own resources plus the invariant). One spec with a disjunctive
precondition was considered and rejected — the two arms share four
instructions and nothing else, and each contract reads as its own sentence.

## The `started` invariant (landed, `StartedInv.v`)

```coq
started_body P := ∃ v : mword 32, started_addr ↦₄ v ∗ (⌜v = started_clear⌝ ∨ P)
started_inv  P := inv startedN (started_body P)
```

A one-shot escrow keyed on the word: while the word is 0 the invariant promises
nothing; once nonzero it carries `P`, the boot hart's deposit. Reading a
nonzero word yields `P`; writing the word costs `P`. That is the C code's
happens-before spelled in separation logic, and the two `fence rw,rw`s are its
machine-level counterpart (no-ops in the model —
`WpSconfCtl.wp_fence_gen_s_sconf` serves both).

Four things about this design are load-bearing:

- **`P` must be PERSISTENT** (every lemma takes `Persistent P`). Up to
  `NCPU - 1` harts read the flag and each wants the payload, and the invariant
  is re-closed unchanged after every read. No escrow/ticket machinery is needed
  *because* of this: with `P` persistent the reader hands the same disjunct back
  in, so the one-shot flag is the whole protocol.
- **What crosses is exactly the persistent part.** A hart's own satp / tlb /
  stvec cells, its stack carve, its `cpu_own`, its `trap_csrs` never cross —
  each hart gets those from its own `_entry` → `start`. What crosses is the
  console/PLIC/disk device invariant, the `pr` lock, the proc locks, the
  kernel-mapping claims: all persistent.
- **The invariant is allocated by the CLIENT, not by main** (`started_inv_alloc`
  is `↦₄ 0 ={E}=∗ started_inv P`, and every hart enters main already holding
  it). It has to be: a secondary hart can reach its first `lw` before hart 0
  has executed a single instruction.
- **The reader gets `▷ P`, not `P`** — see G4 below.

`started_inv_load_au` / `started_inv_store_au` take the OUTER mask `Eo` as a
parameter with the single premise `↑startedN ⊆ Eo`, rather than spelling
`⊤ ∖ ↑minstretN`. That is what keeps `StartedInv.v` below the minstret
invariant (it requires `↦₄` + `inv` + `KernelSyms` and nothing else), so a
future `SpecMain.v` can require it without dragging in a WP layer. The consumer
instantiates `Eo := ⊤ ∖ ↑minstretN`, which is what both AU leaves want.

Also in `StartedInv.v`: `Timeless` instances for `mem_pointsto` and
`word4_pointsto`. Typeclass search does not unfold either `Definition`, so a
`>` intro pattern on the invariant's cell fails with *"iMod: cannot eliminate
modality"* on a hypothesis that visibly IS timeless. Both are one `rewrite`
away. They are `Local` here only to keep the change off `RiscvPtsto.v`; **fold
them into `RiscvPtsto.v` at the next touch of that file** and delete them here.

## Blockers

Ordered by what has to happen first. G1–G3 block the boot arm; G4–G5 additionally
block the secondary arm.

### G1 — `dev_inv` bundles the disk with the UART, but printk runs 12 calls before `virtio_disk_init`

`WpUart.dev_inv_body` is `∃ u p v, uart_frag u ∗ plic_frag p ∗ virtio_frag v ∗
uart_ghosts ∗ virtio_proto ∗ ⌜plic_ok p⌝ ∗ ⌜virtio_isr_ok v⌝` — ONE invariant
over all three device fragments. main cannot establish it where it is first
needed:

- `printk` (0x52) and `plicinithart` (0x8a) both take `dev_inv γd γv`;
- `virtio_disk_init` (0x9a) takes the RAW `virtio_frag v0` and says so
  explicitly in its header ("no `dev_inv`, because this function resets the
  device and programs its queue").

So the disk fragment must still be raw at 0x9a while the invariant must already
exist at 0x52.

**The first-draft fix ("split the invariant; allocate each half when its
device is initialized") does NOT work, and neither does today's raw-frag init
tier.** The device thread (`wp_dev_loop`) is a top-level thread of the whole
system from step 0, and EVERY autonomous device step must update the
ghost-var pair behind `dev_interp`: the lifting rule hands the thread the
auth half, and the user half IS the fragment. A UART rx byte can arrive at
step 0 (nothing gates it), so `uart_frag` must be reachable through an
invariant at every step of the execution — and the same holds for
`plic_frag` (the gateway latch fires whenever an irq line is up) and
`virtio_frag` (the thread must REFUTE `DevStepDiskWild` at every step, which
only `virtio_proto` can do). **No device fragment can ever sit raw in a
CPU's precondition while the system runs.** Consequences: the raw-frag
contracts of `consoleinit`/`uartinit`, `plicinit`, and `virtio_disk_init`
are incompatible with the final wiring; so are `SpecMain.main_devices_raw`
and its "main is what allocates the invariant" comment; today's
`riscv_device_adequacy` only escapes because its thread pool is the device
alone and its initial-state hypotheses (`Hdlab`, `Hvlive`) quietly assume a
machine that xv6's own init code would un-assume.

**The workable fix: the device invariant(s) exist from time 0 (allocated in
adequacy, before any thread runs), and the three init functions are proven
UNDER them, keeping their determinism through per-device side ghosts:**

- **disk** — `virtio_proto` is ALREADY keyed on `virtio_live (v_cfg v)` (the
  not-live arm is trivial; `disk_ghosts_alloc` works from any not-live
  state), so the invariant is allocatable at power-on. Extend the not-live
  arm with a config-tracking half (`ghost_var γc ½ (v_cfg v)`); the boot
  chain holds the other half, so `virtio_disk_init` keeps deterministic
  knowledge of the config it programs across its MMIO writes (the device
  never touches `v_cfg`, so device steps preserve it). The `QUEUE_READY <- 1`
  write is where the arm flips and the DMA lease is paid in; the retired
  ghost halves come back to the driver. `_rw`/`_intr` are unaffected except
  for spec re-pointing (they already run in the live arm).
- **uart** — stop freezing DLAB inside `uart_ghosts_alloc`: return the raw
  `dfrac_agree` half instead, let the boot chain thread it through
  `uartinit`'s baud-latch dance and FREEZE it after the final LCR write
  (dlab=false), which is when `uart_dlab_off` is minted. The FCR
  FIFO-clear write is verifiable under the invariant because the boot chain
  holds `uart_tx_own γ []`, which pins `uart_acc = []`, hence `u_tx = []`,
  hence the clear does not shrink the accepted trace (adequacy hypothesis:
  power-on FIFOs empty — honest). All other uartinit writes are
  config-only and ghost-stable. `uartinit`/`consoleinit` re-proven over
  accessor-form leaves (the raw-frag store leaf `wp_sb_uart_frag_s_sconf`
  gets an invariant-opening sibling).
- **plic** — `plicinit`/`plicinithart` re-proven over accessor leaves; their
  writes (priorities, one hart's S-context enable word) preserve `plic_ok`;
  no extra ghost (nothing reads config back, and no consumer yet needs
  "the priorities are set").

The SPLIT (UART+PLIC invariant vs. disk invariant) is now an interface-
hygiene choice, not a correctness need — still worth doing while every
consumer is being touched anyway (printk should not drag `disk_names`).
Consumers to re-point: `SpecPrintk`, `SpecPrintkGen`, `SpecPlicinithart`,
`SpecConsputc`, `SpecUartwrite`, `SpecUartintr`, `SpecVirtioDiskRw`,
`SpecVirtioDiskIntr`, `SpecConsoleintr`, and the `WpPlic`/`WpVirtioDev`/
`WpUart` leaves that open it.

**Staging so main is not blocked on the proof rework:** state the new
invariant-form `Spec*` for the four init functions and AXIOMATIZE the
reworked ones (assumed-callee shape, like G2/G3); `ProofMain` proceeds over
the interfaces, and each raw-frag proof is then re-worked to discharge its
axiom on its own schedule. `SpecMain` changes with this: `main_devices_raw`
is replaced by the persistent invariant(s) plus the boot hart's tokens
(`uart_tx_own γ []`, the unfrozen dlab half, the virtio config half).

STATUS: direction approved; the DECOUPLING is landed (`7d9bf8f`): three
device threads (`UartLoop`/`DiskLoop`/`PlicLoop`) with pairwise-decoupled
step relations (each device latches its OWN interrupt into the PLIC), the
three invariants `uart_inv γ` / `plic_inv` / `disk_inv γd` (sub-namespaces
of `devN`), and `dev_inv` retained as the compatibility bundle so no
consumer spec changed — see [`../design/device.md`](../design/device.md).
Remaining: the init-under-invariant rework (dlab unfreeze, virtio cfg
tracker, new init specs, adequacy, SpecMain revision) per worklist item 2.

### G2 — printk's only proven contract is the PANIC path

`SpecPrintk.wp_printk_sconf_body` carries `eq_vec (sign_extend' 64 pv) zero_reg
= false` — i.e. `panicking ≠ 0`. All four of main's calls are on the GENERAL
path (`panicking == 0`), where printk takes `pr.lock`, so the proven spec does
not apply. See [`printk.md`](printk.md): "Only the general (non-panic) path
remains, blocked on uartputc_sync's."

**LANDED: `SpecPrintkGen.v` + `LinkPrintkGen.v`** in the assumed-callee
shape (`Module Type` + `Axiom` in the link, as for `KERNELTRAP` —
[`../design/spec-modules.md`](../design/spec-modules.md)), so main's proof is a
functor over it and proving printk-general later replaces exactly one file. The
interface is PERSISTENT-heavy (`printk_env` is proved `Persistent`), so it
crosses `started_inv` for free:

```coq
printk_env γpr γd γv := is_lock γpr pr_lock "pr" (pr_res γd) ∗
                        uart_dlab_off γd ∗ dev_inv γd γv ∗ printk_flags_inv
pr_res γd            := ∃ l, uart_tx_own γd l ∗ uart_sent γd l
```
One deliberate deviation from this note's first draft, which said `R = emp`
("the lock only serializes output"): **the `pr` lock protects the transmitter
token.** A general-path printk transmits bytes, so its future proof needs
transmit rights from somewhere that a SECONDARY hart can also pay — and the
persistent `is_lock` is the only such place (the caller-held-token shape of
the panic path is unpayable post-boot, and `R = emp` would have axiomatized
an interface with no transmit-rights story at all). Consequence for main:
the boot hart pays `pr_res` (the `uart_tx_own γ []` + `uart_sent γ []` it
gets from the uart ghost allocation) into the lock when it builds
`printk_env` after `printkinit`. Note the standing tension with uartwrite,
whose proof keeps the token in `tx_lock`'s invariant
([`uart-driver.md`](uart-driver.md)) — the two homes cannot both link into
one system; reconciling them is the printk-general/console project's
problem, and whichever home wins, this axiom file is the one that changes.

The general contract does NOT require `panicking = 0` (that would force a
fraction of the cell into every caller and forbid `panic` from writing it);
the two flag cells live in their own invariant `printk_flags_inv` inside
`printk_env`. The spec also threads `cpu_own` net-zero and the tp premise
(the general path acquires `pr.lock`), and its post is minimal:
`callee_saved` + ra restored, no `a0` claim, no output claim.

### G3 — `userinit()` has no spec

**LANDED: `SpecUserinit.v` + `LinkUserinit.v`**, same assumed-callee shape:
the weakest interface main can pay — `sie_cap_gpr`, `cpu_own γ 0 …` net-zero,
`kernel_text`/`kernel_data`, `panic_wp`, `procs_inv`, `kalloc_env` (consumed
by `userinit_pages := 8`, provisional), the `initproc` cell (back
existentially). `K_userinit := 50` is provisional — namei's true depth is
unknown; adjusting either constant, or adding the FS-side resources namei's
real proof will demand, replaces exactly this one file plus its Axiom.
(Typeclass note: the context deliberately drops `SpecMain`'s `!fileG Σ` —
nothing in the statement needs it.)

### G4 — the payload arrives under a `▷` and nothing on the loop-exit path strips it

Opening any invariant yields its body under a later, and `P` is persistent but
NOT timeless (it is a conjunction of `inv`-based facts), so the secondary hart
gets `▷ P`. The later must be stripped at a program step, and only
*control-transfer* leaves expose one: `wp_cbeqz_taken_s_sconf` /
`wp_cbnez_taken_s_sconf` (WpSconfBtype.v), `wp_cj_s_sconf` (WpSconfCtl.v),
`wp_wfi_*` (WpSmodeWfi.v). The spin loop EXITS through the FALL-THROUGH of
`beqz a5` at 0x1a, and every leaf the secondary arm then runs — the fence at
0x1c, `jal cpuid` at 0x20, `c.mv`, `auipc`, `addi`, `jal printk` — applies its
continuation without a later. (The loop-BACK edge does expose one, which is why
the iLöb recursion itself is fine.)

**LANDED: `wp_fence_gen_later_s_sconf` (WpSconfCtl.v)** — the existing fence
leaf's statement with the continuation under `▷` (WRAPPER RECIPE: new name,
existing lemma untouched, zero call-site churn); the proof is the original
plus one `iNext` inside `wp_instr_s_sconf`'s post-step callback. This is
also the semantically right place — `fence rw,rw` IS the acquire barrier, so
"the fence is where `▷ P` becomes `P`" is the reading the secondary arm's
proof will use.

### G5 — the per-hart resources the secondary arm needs are globally unique

Two independent instances, both about resources that are per-hart in the
hardware but global in the model's ghost state:

- **`kvminithart`'s contract consumes the kernel page table exclusively.** Its
  precondition takes `ptree_own 2 (DfracOwn 1) t` and
  `kernel_pagetable ↦₈ root_b`, and folds them into `tlb_inv_pt` (KptTree.v),
  which also holds `kmap_auth M` at fraction 1. Every hart runs
  `kvminithart()`, so with 8 harts this is unsatisfiable. `kernel_pagetable ↦₈`
  is read-only after `kvminit` and can become `↦₈□`; `kmap_auth` is
  `ghost_map_auth kmap_name 1 M` over an `M` that never changes after boot and
  can become a fraction. `ptree_own` is the hard one: the model's page walk
  writes A/D bits back (`sr_absorb` returns `gen_heap_interp σ'.(mem)` and
  `tlb_inv_pt`'s `t` is existential), so the tree is genuinely mutated and a
  fraction will not do — it has to live in an Iris invariant, which means
  `s_regime.sr_absorb`'s plain `==∗` has to become mask-carrying, which touches
  every S-mode leaf and engine. That is a project of its own.
- **`SchedCtx.procs_inv` is hart-indexed.** `proc_lock_res` → `proc_slots` →
  `proc_ctx` → `p_sched`, and `p_sched` asserts `⌜tpv = cid_word⌝` and
  `⌜c = a_cpu_ctx cid_word⌝` — the AMBIENT hart. So hart 0's `procs_inv` and
  hart 1's are different propositions over the same 64 locks, and neither can be
  the payload the other needs. Making the proc protocol hart-generic (the
  parking hart's identity as a *value* in the lock resource rather than the
  ambient `cid_word`) is prior to any multi-hart `scheduler`, never mind main.

Also worth recording: `strans_name : gname` in `riscvGS` is GLOBAL (5 use sites:
`RiscvPtsto.v:122`, `IntrDefs.v:444,452`, `RiscvAdequacy.v:241,242`), so
`strans_bit` — half of which rides in every hart's `sie_cap_gpr` via
`strans_inv` — admits at most two holders. Making it `CPU -> gname` is a
5-line change and is right (satp and tlb are per-hart), but it unblocks nothing
on its own while G5's `ptree_own` stands.

## Resource inventory (traced; this is what `SpecMain.v` transcribes)

Ambient, both arms: `sie_cap_gpr γ m K`, `pc_is (mword_of_int KernelSyms.main)`,
`kernel_text`, `kernel_data`, `panic_wp`, `m !!! Regidx (mword_of_int 4) =
cid_word` (the tp/cid convention every callee in the kalloc cone requires), and
`started_inv P`.

`K`: main's own frame is 2 slots and its deepest callee is `kvminit` (50);
`printk` wants 38, `kinit` 22, `virtio_disk_init` `K_virtio_disk_init` = 18,
`procinit` 10, `binit`/`iinit` 12, `consoleinit` 6, `plicinithart` 4. And
`scheduler` needs `20 ≤ av` at the frame depth main calls it from. So
`K_main = 52`.

`cpu_own γ 0 false p0 cpu_ctx_free` threads the whole way: `kinit`, `kvminit`,
`virtio_disk_init` each take `cpu_own γ 0 eb pp C` net-zero, and `scheduler`
consumes it at exactly the boot shape.

Boot arm, the raw global inventory (each spinlock as
`SpecProcinit.lk_raw`, which bundles the three cells `lk ↦₄ _`,
`lock_name_field lk ↦₈ _`, `lk_cpu lk ↦₈ _`):

| callee | consumes | produces |
|---|---|---|
| `consoleinit` | `lk_raw cons`, `lk_raw tx_lock`, `devsw_console_{read,write} ↦₈`, `uart_frag u0` | both locks `lk_fresh`, devsw slots set, `uart_frag (uartinit_post u0)` |
| `printkinit` | `lk_raw pr` | `lk_fresh pr "pr"` |
| `printk` ×3 | `printk_env` (G2), format string `↦ₛ{dq}` | — |
| `kinit` | `lk_raw kmem`, `kmem+24 ↦₈ 0`, `[∗list] p ∈ ps, page_own p` + `prun phystop s1entry ps` | `is_kmem γl γk`, `kalloc_avail γk (Some (length ps))` |
| `kvminit` | `kernel_pagetable ↦₈ kpt0`, `kalloc_env γa on tp` | `ptree_own 2 1 t`, root written, `pt_rep0 t (kvm_map_full pas)`, `kvm_pas_ok pas`, 64 `page_own` kstacks, budget `avail_sub on K_kvmmake` |
| `kvminithart` | `strans_bit bare`, `tlb ↦ᵣ tlbvec0`, the table + root | `strans_bit kpt`, `∃v, stvec ↦ᵣ v`, `kmap_at tramp_vpn`, 64 `kmap_at (kstack_vpn i)` |
| `procinit` | `lk_raw pid_lock`, `lk_raw wait_lock`, 64 × `proc_raw`, `fd_slots (NPROC*(NOFILE+FDSPARE))` | both `lk_fresh`, 64 × `proc_ready` |
| `trapinit` | `lk_raw tickslock` | `lk_fresh tickslock "time"` |
| `trapinithart` | `stvec ↦ᵣ tv0` | `stvec ↦ᵣ kernelvec` |
| `plicinit` | `plic_frag p` | `plic_frag (plicinit_plic p)` |
| `plicinithart` | device invariant (G1) | — |
| `binit` | `lk_raw bcache`, `NBUF × sl_raw (buf_lock (bnode k))`, `NBUF × blink_raw`, `blink_raw bhead` | `lk_fresh`, `NBUF × sl_fresh "buffer"`, `bcache_lru bhead (blist 0 NBUF)` |
| `iinit` | `lk_raw itable`, `NINODE × sl_raw (inode_lock i)` | `lk_fresh`, `NINODE × sl_fresh "inode"` |
| `fileinit` | `lk_raw ftable` | `lk_fresh ftable "ftable"` |
| `virtio_disk_init` | `lk_raw disk_lock`, `disk_{desc,avail,used} ↦₈`, 8 × `disk_free+j ↦ₘ`, `virtio_frag v0`, `kalloc_env` with ≥3 pages | `vdi_post` |
| `userinit` | G3 | — |
| `scheduler` | `procs_inv γ Φ γs`, `cpu_own γ 0 false p0 cpu_ctx_free`, `trap_csrs`, `intr_handler_avail γ` | never returns |

Three assemblies main itself owes, none of them a callee call:

1. **`kalloc_env γa on tp` from `is_kmem` + `kalloc_avail`** (`KvmSpec.v:118`),
   between `kinit` and `kvminit`.
2. **`procs_inv γ Φ γs` from the 64 `proc_ready`s** — DONE:
   `SpecProcinit.procs_inv_alloc` (§ProcinitProcsInv), consuming per proc
   `proc_ready i` + the two public cells procinit does not touch, over
   `WpLock.newlock_delayed` (see Status).
3. **`intr_handler_avail γ` via `intr_inv_alloc_off`** (`IntrDefs.v:356`), from
   `trapinithart`'s `stvec ↦ᵣ kernelvec` plus the SIE ghost's spare quarter —
   this is step 3 of interrupt-sweep's item 8, and main is its only caller.
   Note the boot arm calls `trapinithart` at 0x82 and `scheduler` at 0x3e, so
   the allocation sits between them; the SECOND `kvminithart` call at 0x76 is
   the one that dissolves the Bare arm (the call at 0x32 is the secondary arm's).

Secondary arm: `started_inv P` + this hart's own `strans_bit bare`, `tlb ↦ᵣ`,
`stvec` (via kvminithart), `cpu_own`, `trap_csrs` — and `P` must supply the
device invariant, `printk_env`, the kernel table (G5), and `procs_inv` (G5).

## Worklist

1. ~~G2 + G3 + G4 + `procs_inv_alloc` + the Timeless fold + the
   `0330000f`/`creg_c*` decode dedup~~ — DONE (commits `a1cafcf`, `81aa9ea`);
   see Status.
2. **G1**: the invariant-from-time-0 rework described above — the WpUart.v
   invariant restructure (+ optional split), the `uart_ghosts_alloc` DLAB
   unfreeze, the virtio not-live cfg tracker, the new invariant-form init
   specs (axiomatized where the proof rework is deferred), the adequacy
   allocation, and the `SpecMain` device-precondition revision.
3. **`SpecMain.v` revision + `ProofMain.v`** — after G1: replace
   `main_devices_raw` with the invariant(s) + boot-hart tokens, and switch
   the payload to the wand shape — main's boot contract takes
   `□ (∀ γd γv γs …, <init output> -∗ P)` and applies it at the store, so
   main's proof never has to know what the secondaries want. Then
   `ProofMain.v` as a functor over the eighteen callee interfaces, and the
   one-line `LinkMain.v`.
4. **G5** — its own project, and prior to any multi-hart claim: the mask-carrying
   `sr_absorb` (so the kernel page table can be shared), `kmap_auth` at a
   fraction, `kernel_pagetable ↦₈□`, `strans_name : CPU -> gname`, and a
   hart-generic `p_sched`. Only then `wp_main_secondary_sconf`.
5. Adequacy: `started_inv_alloc` goes inside `riscv_system_adequacy`'s
   `={⊤}=∗`, beside the device-ghost allocation
   ([`../design/adequacy.md`](../design/adequacy.md)).
