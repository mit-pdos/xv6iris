# durable-disk — the crash predicate owns the disk; P_fs as the cross-era loop invariant

Design of record: [`../design/crash.md`](../design/crash.md), "The durable
disk: ONE fixed gname, owned by the crash predicate" (ruled 2026-08-22).
Read it first; this file is the worklist. It subsumes the "honest
restatement" paragraphs in [`fs-log.md`](fs-log.md)'s banner, whose items
(1)/(3) (initlog's real recovery) become stage D here.

## Why (one paragraph)

`xv6_power_adequacy` is vacuous: its (d2b) premise `fs_boot_image_eras` is a
∀ over every `boot_facts` state and `boot_facts` leaves the disk free, so a
zero disk refutes it. The premise existed because a booting era has no way
to tie the crash invariant's `dk` to its own disk (the `disk_tie` halves
sit in the invariant body and in `state_interp`). The ruling removes the
tie by construction: the durable disk is one fixed gname whose auth the
machine layer holds at `v_disk` and whose fragments `P_fs` owns; no mortal
owner ever holds a durable fragment; the theorem assumes only
`v_disk g = fsimg_dk` at era 0.

## Stages

**A. Machine layer (`RiscvPtsto`/`RiscvExec`/`RiscvAdequacy`/`DiskImg`).**
`riscvFixedGS` gains `γdisk`; `state_interp` holds `● v_disk` at it (fixed
conjunct, both power arms preserve it); `riscv_crash_pred : iProp Σ` (no
`dk` index); `crash_inv := inv crashN riscv_crash_pred`; delete
`disk_tie`, `fs_tie_interp`, `era_disk_name`'s re-mint and
`power_boot_res`'s whole-disk fragment row. The write rule at DMA completion
opens `crashN`, applies the permit (now a view shift over
`riscv_crash_pred` beside the `γdisk` auth/frag update), closes. Add the
READ rule's permit (phase D2): at completion the client's view shift sees
the auth-agreed bytes. `HPc` becomes `⊢ |==> Pc` from `● fsimg_dk`'s
fragments (era 0 only). `Hboot` keeps `boot_facts g'` and nothing about the
disk.

**B. `FsCrash.P_fs`.** Owns the `◯` fragments of `γdisk` (the whole disk);
`fs_rec_wf` restated over them; carries mkfs's geometry (superblock parse)
as pure content. `fs_crash_seam` becomes an equation on the field again
(no `dk`). The five permits restated; `fs_recovery` unchanged.

**C. Bio/log/boot consumers — no durable ownership anywhere.** `BioInv`'s
`disk_block` in `bv_clean`/pool, `FsBlocks.fsblock`/`fs_L`, `FsBoot`'s byte
mint, `BootShared`'s disk rows, `SpecBread`/`SpecBwrite`/`ProofWriteHead`'s
fragment arguments: each becomes a per-era IN-MEMORY ghost whose relation
to the durable state is established at the DMA completion through the
read/write permits. `fs_cfg_alloc` mints `fscfg`/`icfg` off `P_fs`'s pure
content in the boot fupd; `Himg` and `fs_boot_image_eras` deleted;
`FsAdequacyImg` keeps only `v_disk g = fsimg_dk` and proves `P_fs` of it.

**D. The dirty-log boot (was fs-log (1)/(3)).** `SpecInitlog` drops
`hdr_n bs_hdr = 0` and consumes the read permit's knowledge; `ProofInitlog`'s
copy loop goes live; `SpecInstallTrans` loses `recovering = false ∨ n = 0`
and proves the recovering arm. Only then is the boot obligation dischargeable
on every `P_fs` disk and the theorem true.

Order: A → B → C → D. A and B are machine/crash-layer and FS-agnostic; C is
the wide sweep (24 files hold disk fragments today: `FsBoot` 22 sites,
`BootShared` 5, `BioInv` 5, the virtio proofs, `SpecBread`/`SpecBwrite`);
D is the proof debt that was always there.
