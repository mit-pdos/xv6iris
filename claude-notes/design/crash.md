# Design: power, crashes, and generations

The crash/power layer: the machine may lose power at any cycle, discarding
memory, registers and all device state except the disk image, and reboot at
`_entry`. Verified INSIDE the logic (stock Iris, no Perennial fork): a ghost
"power thread" owns both boot and crash, each boot runs in a fresh
GENERATION with fresh ghost names, and one crash-spanning invariant owns the
disk's persistent contents as an arbitrary iProp. Existing crash-free WPs
are untouched by construction — crash reasoning never appears in any leaf,
engine, or whole-function statement.

**STATUS: COMPLETE through M6.** The layer is built and CLOSED: the system
theorem `SystemAdequacy.xv6_power_adequacy` says that a machine starting
powered off at generation 0 is never stuck under any interleaving of power
cycles, hart steps and device steps, over the real kernel image and all eight
harts. Its hypotheses are exactly `ggen = 0` and `gpow = false`; its axiom
footprint is the 5 `rv64d.*` platform axioms + `functional_extensionality_dep`
+ the four sanctioned assumed kernel contracts (printk-general, kerneltrap,
userinit, panic). What is left is future work rather than layer work: the crash
predicate `Pc` is instantiated at `True` and the FS layer's `P_fs` is what will
give it content, and the torn-write knob is still open. Worklist (with the
per-milestone record):
[`../projects/crash.md`](../projects/crash.md).

## The semantics (RiscvLang.v)

- `gstate` gains `ggen : nat` (the current generation) and `gpow : bool`.
- The four loop expressions are INDEXED BY GENERATION (`LoopE gen c`,
  `UartLoopE gen`, `DiskLoopE gen`, `PlicLoopE gen`). Real arms are gated
  on `gpow = true ∧ ggen = gen`; each expression also has a CORPSE arm — a
  self-loop with no state change — enabled on the complement. A dead
  generation's thread can only take the corpse step, and handling the
  corpse step needs no resources: that is the whole trick. Thread identity
  is SYNTACTIC, which is what lets an old generation be abandoned rather
  than revoked (one thread can never revoke another's resources in Iris).
- `PowerLoopE` — the ghost thread, the ONLY member of the initial pool:
  - **PowerOff** (enabled at `gpow = true`): `gpow := false` AND
    `ggen := ggen + 1`. Power loss kills the running generation instantly,
    so "gen is dead" is simply `ggen > gen` — one mono-nat lower bound,
    stable forever. During an off-window, `ggen` names the generation
    about to boot, which has no threads yet.
  - **PowerOn** (enabled at `gpow = false`): `gpow := true` (ggen
    unchanged), machine reset to `g' ∈ boot_shape` with `v_disk` PRESERVED
    (the only crash-surviving state), and FORKS the new generation's
    threads (`LoopE ggen c` for each hart + the three device loops) via
    `prim_step`'s `efs`. First boot and every reboot are this same arm.
  - The gating makes the alternation total: no stutter arm, never stuck.
- `boot_shape` (RiscvLang.v, pure): the kernel image reloaded and .bss
  zeroed over an ALL-PRESENT RAM (the loader/firmware, modeled here as
  `boot_byte` over the ELF's own byte maps), the fifteen per-hart reset
  registers of `reset_regs` (PC = nextPC = 0x80000000, M-mode, mhartid =
  the hart index, the M-mode config registers, all-OFF PMP, mie/mideleg
  clear), the devices reset (`virtio_reset` keeps `v_disk`; UART/PLIC at
  their power-on states) — and the rest of the registers arbitrary,
  because that is what a boot proof quantifies over. `boot_facts` is the
  same fact set minus the two equalities that relate the new machine to
  the dead one: it is what the power thread hands the boot client. The
  canonical machine that has the shape, and the witness that PowerOn can
  always step, are `boot_gstate` / `boot_shape_boot_gstate` in
  PowerBoot.v.
  - **`reset_regs`' VALUES ARE PROVEN, not transcribed.**
    `ColdBoot.reset_regs_cold_boot` runs the Sail model's own cold-boot
    chain (`sail_model_init`; the board's reset vector and hart id;
    `init_model ""`; `init_boot_requirements`) with `RiscvExec.exec` and
    proves `reset_regs` of the register file it produces, so a model
    regeneration that changes a reset value breaks the build. EXACTLY ONE
    conjunct is still an explicit `register_set` patch and it is the whole
    residue: `pma_regions`, the one-region idealization. (misa used to be a
    second patch — the model's config enabled B and V, so its cold boot
    left `0x800000000034112F`. Fixed at the config, not the constant, and
    `cold_boot_misa` is the tie.) What the patch is measured AGAINST is now
    compiled too: `ColdBoot.pma_model_table` is the model's real
    three-region table, extracted by evaluating the model, with
    `cold_boot_pma` proving it is the register's value — so the
    table IS the model's own (`cold_boot_pma`), so no `register_set` patch
    remains at all. `init_model`'s `assert (config_is_valid tt)` is
    SATISFIED (`cold_boot_config_valid`), which is why the chain can be
    anchored there at all; at the idealized table the same check computes
    to false.
    The chain's one uninterpretable step — `cancel_reservation`, an
    `Axiom` of the model — is lifted to a parameter whose elision is
    itself checked by `reflexivity`. `reset_regs` is a COLD-boot
    description; a warm-reset arm would need its own, weaker, fact set.
    Still open, and recorded in projects/crash.md: the ∃-garbage anchoring
    (`reset()` alone over arbitrary power-on state), which waits on
    symbolic peeling because forcing any register field of the reset's
    result over an OPEN register file does not compute.
  - **THE TOWER'S PMA OBLIGATION IS PER ADDRESS CLASS.** The platform's
    table (`RiscvLang.pma_boot`, the model's own) has three regions — boot
    ROM `[0x1000, +0x1000)` IOMemory read-only, MMIO band
    `[0x2000000, +0x10000000)` IOMemory R/W, DRAM
    `[0x80000000, +0x8000000)` MainMemory R/W/X with AMOCASQ and PTE
    access — with HOLES between them, so no obligation quantified over all
    addresses can hold of it. `RiscvFetchExec.pma_allows_all` is therefore
    indexed by a class (`pma_class = PmaRam | PmaIo`; a `∀`, not a
    conjunction, so `repeat split` in a config-bundle proof cannot take it
    apart): `pma_allows_ram` asks R/W/X, both PTE permissions, and — stated
    as what a consumer consumes rather than as a support LEVEL —
    `∀ op n, n ≤ 16 → pma_allows_atomic_op … op n = true`, i.e. every AMO
    the decoder can produce, over `pma_ram_access` (the DRAM range, which
    is EXACTLY `RiscvPtsto.addr_is_ram`'s); `pma_allows_io` asks R/W only
    over `pma_io_access` (the band, `mmio_base`/`mmio_size`). Each class carries
    the END bound as well as the base bound, because `range_subset`
    compares the access's end against the region's — and every applier
    already owns it (the chunk lemmas return the last byte's
    `addr_is_ram`; `PtTree.pt_slot_mem` carries both ends of a PTE slot).
- The corpse arm is a SELF-LOOP, not a retire-to-value: reaching a value
  would force `Φ dead_val` through every leaf lemma in the tree; the
  self-loop keeps the dead branch Φ-generic. Deliberate consequence:
  not-stuck is vacuous for corpses (they accumulate in the pool,
  schedulable but inert); every real step of a live generation still
  carries the full WP obligation.
- Initial configuration: pool `[PowerLoopE]`, `gpow = false`, `ggen = 0`,
  `g0` arbitrary except the client's `P_fs (v_disk g0)` (mkfs's
  obligation). The top-level theorem has that ONE hypothesis.

## Generations in the logic

- `riscvGS` splits into a FIXED layer (invGS, the `γgen` mono-nat, the
  generation→era registry, the disk-image ghost's CLASS, `crash_inv`'s
  ghosts) and an ERA layer (heap gname, register auths, device ghost-vars,
  sie/strans/park/kpt names, the disk-image gname `era_disk_name`). PowerOn allocates a fresh era record, so
  every memory/register reference of a boot is independent of the previous
  boot's. The composite class keeps the name `riscvGS` and its field
  accessors, so mid-tree files are textually unchanged.
- The generation is AMBIENT via `Class GenId := { gen_id : nat }`, a
  Context binder alongside `CpuId`; `Notation Loop := (LoopE gen_id
  cpu_id)`. Gen must NOT be a `CpuId` field: parking/`wp_next` contracts
  quantify their continuations over the RESUMING CpuId, and that
  quantifier must range over harts of the SAME generation — a parked
  proc's payload is era resources and dies with its generation (correct:
  a crashed machine's run state is gone).
- `state_interp` = fixed conjuncts (mono-nat auth of `ggen`; the registry
  gen ↦ era with the pure shape `dom(registry) = [0, ggen) ∪ (if gpow
  then {ggen} else ∅)`) ∗ (when `gpow`: the current era's interp
  QUADRUPLE — registers, heap, devices, and the era's disk-image tie
  `disk_img_auth (era_disk_name E) (v_disk (dvirtio (gdev g)))`).  When the
  power is off there is no image conjunct at all: the era, and its image
  map, are gone.
- **Base lifting rules are the only re-proved WP layer** (`wp_exec_step`
  tower roots + the three device lifting rules). Each reads `(ggen, gpow)`
  off `state_interp` and four-way splits against the caller's `gen`:
  - `ggen > gen` → mint `dead gen := mono_nat_lb γgen (gen+1)`, drop the
    caller's resources (affine), `iApply wp_dead`.
  - `ggen = gen ∧ gpow` → the old proof verbatim (only real arms enabled,
    so the caller's continuation covers every step).
  - `ggen = gen ∧ ¬gpow` → REFUTED: the caller's era registration says
    `gen ∈ dom(registry)`, the registry shape says otherwise. (This state
    is semantically unreachable while a gen-thread exists — threads of a
    generation are forked only at its PowerOn — but base rules must
    refute it in-logic, and the registry shape is what does it.)
  - `ggen < gen` → refuted by the birth bound.
- `wp_dead : dead gen ⊢ WP (LoopE gen c) {{Φ}}` — a short Löb loop, no
  other resources, arbitrary Φ; stable because `ggen` is monotone.
- The birth certificate `mono_nat_lb γgen gen` and the era registration
  ride INSIDE that era's `minstret_inv` (allocated per era at PowerOn,
  already threaded by every WP in the tree): zero statement churn.
- `wp_power_loop`: Löb over the two arms. PowerOff: drop the era innards
  of `state_interp` — INCLUDING the era's disk-image auth — bump the auth,
  re-establish the off form. PowerOn:
  `gen_heap_init` over the reset memory, fresh register/device auths (the
  virtio auth at the PRESERVED `v_disk`), a FRESH image map minted at that
  preserved content whose full fragments go to the client
  (`DiskImg.disk_img_alloc`; see the image section below),
  allocate the era invariants,
  register the era, then discharge the fork obligations with the client's
  JOINT boot entailment — the same shape as the old adequacy hypothesis
  (`∀` era instance, `∀ g' ∈ boot_shape`, initial resources `={⊤}=∗` the
  per-thread WPs), now consumed in exactly one place. Neither arm ever
  opens `crash_inv`.
- Adequacy shrinks to: allocate the fixed layer, hand the pool
  `wp_power_loop`. The era-0-vs-era-k distinction does not exist.

## The disk image ghost: PER-ERA, re-minted at every boot

The disk itself is the one machine component a power cycle preserves; its
GHOST mirror deliberately is not.

- **Nothing linear may be parked in an era invariant and still be needed
  after a crash**: Iris invariants are never deallocated, so a resource
  inside a dead era's invariant is unreachable forever. The image auth
  therefore cannot live in `virtio_proto`/`disk_inv` *and* be the thing
  clients hold fragments of. It does not live in the FIXED layer either
  (that was M5's shape, and it does not survive contact with the FS
  layer): a fixed map's stranded fragments can never be re-minted —
  `ghost_map` cannot re-create an existing key, and auth-side forgetting
  needs the element, which is exactly what is stranded — so a system whose
  bio/log layers hold image fragments could not boot twice.
- **The shape: one image map PER ERA** (`riscvEraGS.era_disk_name`; the
  typing class `diskImgG` stays fixed-layer, `riscvFixedGS.riscvF_diskGS`,
  and is the UNIQUE source of that `ghost_mapG Σ Z (bv 8)` instance).
  `state_interp`'s live branch holds `disk_img_auth (era_disk_name E)
  (v_disk …)`; PowerOff drops it with the era (nothing is owed — the map's
  only reader was that era's own disk thread); PowerOn allocates a FRESH
  map at the disk's preserved content and hands the client its FULL
  fragments (`DiskImg.disk_img_alloc`, delivered in `power_boot_res` as
  `disk_img_bytes (era_disk_name HE) 0 (disk_read (v_disk …) 0 ndisk)`).
  So every boot — the first one included — starts with total ownership of
  a whole disk's worth of ghost bytes, and a crash abandons the previous
  era's wholesale. `DiskPtsto.disk_names.dn_img` is CONSTRUCTED at the
  ambient era's gname (`RiscvPtsto.disk_img_name`), so every client
  spelling `disk_bytes γ …` / `disk_block γ …` is unchanged.
- The era-level `virtio_proto` keeps the queue/slot/claim
  protocol — which SHOULD die at a crash: in-flight requests vanish with
  the device reset, and sleepers holding receipts are dead anyway.
- `crash_inv := inv crashN riscv_crash_pred`, where `riscv_crash_pred` is
  a FIELD of `riscvFixedGS` of type `iProp Σ` — the client fixes it at
  adequacy (the `Pc` parameter). Intended instance: "the durable image
  satisfies `P_fs`", over `disk_bytes` fragments plus whatever abstract FS
  state, commit-history mono-lists and persistent durability receipts the
  FS keeps. Carrying it as a FIELD rather than a parameter is what keeps
  `P_fs` out of every `dev_inv`-adjacent signature — nothing between
  RiscvPtsto and the disk thread names it. Allocated once, in adequacy,
  and handed to every boot (`power_boot_res`), so all generations share
  it; it spans power cycles because neither power arm touches `v_disk` and
  neither opens the invariant.  Note the asymmetry that makes the whole
  design work: what spans a crash is the CRASH PREDICATE (an iProp over
  whatever ghost state the client chooses), never the image map — the
  image ghost is per-era and re-minted, and `P_fs`'s own state has to be
  fixed-layer or re-derivable, which is what recovery is for.
  - **A FIELD OF TYPE `iProp Σ` IS OPAQUE TO EVERY OPENER, and that
    decides what may be parked inside it.** `crash_inv`'s body used to be
    the field itself, so the disk thread's completion — the one opener —
    got the proposition, never its innards. Anything the MACHINE layer
    has to move at a completion (the FS tie's other half: a
    `ghost_var` ½ mirroring `v_disk`) therefore cannot be a conjunct of
    the client's `Pc`; it has to be a SIBLING of it in the invariant
    body, which means indexing the field by the value being tied. That
    is now the shape (fs-log stage 4 phase C2a):
    `riscv_crash_pred : (Z -> bv 8) -> iProp Σ` and
    `crash_inv := inv crashN (∃ dk, disk_tie dk ∗ riscv_crash_pred dk)`,
    against `state_interp`'s new FIXED conjunct `fs_tie_interp`. The
    corollary for adequacy is that `HPc : ⊢ Pc` becomes
    `⊢ |==> Pc (v_disk …)` — a crash predicate that OWNS ghosts is never
    provable from nothing — and that a WRITE's permit is no longer free
    (`design/fs-log.md`, stage-4 item 3).
  - **The stranded-fragment question is CLOSED by the per-era map**: a
    sleeper's `disk_bytes` fragments sit in the per-era `disk_inv`, so a
    crash abandons them together with the auth that remembers their keys.
    Nothing is lost, because the next boot's map is brand new.
- `v_disk` changes in exactly ONE place (the device thread's DMA
  completion of an OUT slot, `vslot_post`), so that step carries the only
  crash obligation in the whole kernel: `wp_disk_loop` opens `crash_inv`,
  `permN` and `disk_inv` together (disjoint namespaces) at that instant,
  does the MECHANICAL update of the FS tie's two halves (it is the only
  holder of both), and spends a WRITE PERMIT —
  `disk_write_permit (w : disk_wr) Q := ∀ dk, ▷ riscv_crash_pred dk ==∗
  ▷ riscv_crash_pred (wr_apply w dk) ∗ Q`, transported by `PermInv` and
  INDEXED by the completing slot's own write identity (`VirtioQueue.vs_wr`,
  pinned to the request by `VirtioProto.slot_pend_res`) — to re-establish
  `P_fs`. A BASIC update suffices, with no mask annotation: a serialized
  writer (xv6's log) needs nothing conditional. Disk reads cost nothing
  (`w = None`, and `wr_apply None` is the identity ON THE NOSE, which is
  what keeps every read caller's statement unchanged).
  - **Where the permit comes FROM is still open.** The intended source is
    the enqueuer (`virtio_disk_rw`'s caller), per the recorded vs_data
    rule, but the `vslot` cannot hold it: `disk_inv_body` must be
    `Timeless` (the MMIO accessors open it with no step left to absorb a
    `▷`), and no iProp can pass through a timeless invariant. The two
    candidate channels — a second, non-timeless era invariant with a
    timeless ghost skeleton, or a `P_fs` closed under in-flight writes so
    that no per-slot deposit is needed — are written up in
    `../projects/crash.md` (M5b). Until one lands, the completion mints
    the identity permit, so nothing in the kernel yet owes anything. In-era
  kernel code has NO crash conditions anywhere — no wpc, no per-function
  crash specs; the write-ahead-log discipline lands entirely on the
  enqueue permit.

## Decision record (rejected shapes, and why)

- **Per-thread crash `prim_step` absorbed by a WP engine** (the
  MinstretInv / interrupt-engine pattern): not even statable — a crash
  resets every hart's PC and all memory underneath frags OTHER threads
  own, and one thread cannot revoke another's resources. Interrupts can be
  absorbed because they ROUND-TRIP; crashes don't.
- **Meta-level crash relation between adequacy applications**
  (Argosy-style pure carrier; induction over eras, `wp_strong_adequacy`
  extraction of a pure disk predicate at every reachable state): sound and
  much cheaper, but the crash boundary can then only carry a PURE
  predicate/abstract state — no iProp invariant, no in-logic durability
  receipts. Kept as the fallback if the in-logic design proves too heavy.
- **Rebirth slots** (the power thread deposits fresh boot bundles that
  stale derivations claim at their next step): workable but heavy — needs
  era tokens smuggled into `pc_is`, a claim protocol, a `crash_cap`
  capability threaded to dodge the state_interp/wp definitional
  circularity, and later-credit accounting. Generation-indexed
  expressions + FORK delete all of it: dead threads are abandoned, not
  revived, and new WPs flow through the fork's `efs` natively.
- **Even/odd phase counter** unifying (ggen, gpow) in the semantics:
  rejected as annoying; PowerOff-bumps-ggen gives the same monotone death
  certificate with two honest fields.
- **gen inside CpuId**: rejected — cross-hart resumption quantifiers would
  range over generations, which is nonsense (see above).
- **Corpse retire-to-value**: rejected — forces `Φ dead_val` through every
  leaf lemma.

## Recorded modeling choices

- Disk writes are REQUEST-ATOMIC across a crash (xv6's own assumption;
  BSIZE = 1024 = 2 virtio sectors). Sector-granularity tearing of
  in-flight requests would be a one-line knob in the PowerOff arm, at the
  price of `P_fs` closed under tearing — which xv6's log does NOT satisfy;
  turning it on would surface a real xv6 assumption, not a proof artifact.
- PowerOn models the loader/firmware: kernel image reloaded, bss zeroed,
  registers per SpecEntry.v's reset state. Warm-boot memory retention is
  deliberately NOT modeled (memory is havocked).
- mtime/CLINT reset to arbitrary values (`clock_inv` is value-agnostic, so
  nothing anywhere cares).
- The pool accumulates corpse threads across power cycles; they are
  schedulable but inert, and the adequacy statement is unaffected.
