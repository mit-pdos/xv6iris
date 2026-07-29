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

**NOT landed: `SpecMain.v` / `ProofMain.v` / `LinkMain.v`.** main is *not*
proven and its contract is deliberately not frozen yet. Five gaps block it, and
every one of them is in a CALLEE's contract or in a shared abstraction, not in
main; freezing a `SpecMain.v` against contracts that must change first would be
building on a shape we already know is wrong (see the guiding principle in
`durable-notes.md`). The gaps and their fixes are §"Blockers" below; the
inventory main's precondition has to carry is §"Resource inventory", already
traced callee by callee, so `SpecMain.v` is a transcription job once the
blockers clear.

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
exist at 0x52. **Fix: split the device invariant** — a UART+PLIC invariant
allocatable right after `consoleinit`/`plicinit`, and a separate disk invariant
allocated by `virtio_disk_init` itself out of the raw fragment. That is the
honest factoring anyway: the three devices share nothing but the `dev_interp`
conjunct of `state_interp`, and the code initializes them at three different
times. Consumers to re-point: `SpecPrintk`, `SpecPrintkinit`?, `SpecPlicinithart`,
`SpecConsputc`, `SpecUartwrite`, `SpecUartintr`, `SpecVirtioDiskRw`,
`SpecVirtioDiskIntr`, `SpecConsoleintr`, and the `WpPlic`/`WpVirtioDev`/`WpUart`
leaves that open it.

### G2 — printk's only proven contract is the PANIC path

`SpecPrintk.wp_printk_sconf_body` carries `eq_vec (sign_extend' 64 pv) zero_reg
= false` — i.e. `panicking ≠ 0`. All four of main's calls are on the GENERAL
path (`panicking == 0`), where printk takes `pr.lock`, so the proven spec does
not apply. See [`printk.md`](printk.md): "Only the general (non-panic) path
remains, blocked on uartputc_sync's."

**Fix (short term): `SpecPrintkGen.v` + `LinkPrintkGen.v`** in the assumed-callee
shape (`Module Type` + `Axiom` in the link, as for `KERNELTRAP` —
[`../design/spec-modules.md`](../design/spec-modules.md)), so main's proof is a
functor over it and proving printk-general later replaces exactly one file. Keep
the interface PERSISTENT-heavy so it crosses `started_inv` for free:

```coq
printk_env γd γv γpr := is_lock γpr pr_lock "pr" emp ∗ <device invariant> ∗ <panic-flag inv>
```
`pr` is `static struct { struct spinlock lock; } pr;` — the lock protects
NOTHING (`R = emp`); it only serializes output. And do NOT thread the
`panicking`/`panicked` cells: printk works whichever way the flag reads, so the
general contract should not require `panicking = 0` at all (requiring it forces
a fraction of the cell into every caller and forbids `panic` from writing it).
Put the two flags in their own invariant inside `printk_env`.

### G3 — `userinit()` has no spec

No `SpecUserinit.v`. Same fix as G2: state the interface (the weakest thing main
can pay — `sie_cap_gpr`, `cpu_own γ 0 …`, `kernel_text`/`kernel_data`,
`panic_wp`, `procs_inv`, `kalloc_env`, the `initproc` cell) and axiomatize it in
`LinkUserinit.v`.

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

**Fix: one later-exposing leaf, at the fence.** `wp_fence_gen_s_sconf`'s proof
already sits inside `wp_instr_s_sconf`'s post-step callback, where an `iNext` is
available (compare `wp_cbeqz_taken_s_sconf`, which does exactly that); a
`wp_fence_gen_later_s_sconf` whose continuation is `▷ (sie_cap_gpr … -∗ …)` is
that proof plus one `iNext`. Put it in `WpSconfCtl.v` (WRAPPER RECIPE: new name,
existing lemma untouched, zero call-site churn). This is also the semantically
right place — `fence rw,rw` IS the acquire barrier, so "the fence is where
`▷ P` becomes `P`" is the reading you want in the proof. Cost: recompiling
`WpSconfCtl.v` and everything above it, so batch it with any other central-file
edit (G1, and the `Timeless` instances above).

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
2. **`procs_inv γ Φ γs` from the 64 `proc_ready`s** — 64 `lock_alloc`s plus
   persisting each `p->kstack` into `is_kstack`. Worth a helper
   (`procs_inv_alloc`) in `SchedCtx.v` rather than 64 lines in `ProofMain.v`.
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

1. **G2 + G3**: `SpecPrintkGen.v` / `LinkPrintkGen.v` and `SpecUserinit.v` /
   `LinkUserinit.v` — assumed-callee shape. Cheap, unblocks the boot arm's two
   remaining holes. Add all four to `_CoqProject`.
2. **G1**: split `dev_inv`. Batch with the `Timeless` instances (into
   `RiscvPtsto.v`), the `mndb_0330000f` / `mnd_cr{2,6,7}` decode dedup (into
   `KernelBaseDecode.v` / `KernelRvcDecode.v` — `fence rw,rw` is now proved
   privately in both `WpVirtioDiskIntrDecode.v` and `WpMainDecode.v`), and
   G4's `wp_fence_gen_later_s_sconf` (into `WpSconfCtl.v`), since all four
   touch files with big cones.
3. `procs_inv_alloc` in `SchedCtx.v`.
4. **`SpecMain.v`** — `wp_main_boot_sconf` from the table above, diverging, with
   the payload handled as a parameter: main's boot contract takes
   `□ (∀ γd γv γs …, <init output> -∗ P)` and applies it at the store, so main's
   proof never has to know what the secondaries want. Then `ProofMain.v` as a
   functor over the eighteen callee interfaces, and the one-line `LinkMain.v`.
   Spell the entry pc as `let pcE : mword 64 := mword_of_int KernelSyms.main in`
   so `tools/proof_coverage.py` sees the symbol.
5. **G5** — its own project, and prior to any multi-hart claim: the mask-carrying
   `sr_absorb` (so the kernel page table can be shared), `kmap_auth` at a
   fraction, `kernel_pagetable ↦₈□`, `strans_name : CPU -> gname`, and a
   hart-generic `p_sched`. Only then `wp_main_secondary_sconf`.
6. Adequacy: `started_inv_alloc` goes inside `riscv_system_adequacy`'s
   `={⊤}=∗`, beside the device-ghost allocation
   ([`../design/adequacy.md`](../design/adequacy.md)).
