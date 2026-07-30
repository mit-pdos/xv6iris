# Project: sharing the kernel page table across harts (G5, part 1)

GOAL: make `kvminithart` callable on EVERY hart, so `wp_main_secondary_sconf`
becomes statable. This is the first half of main-boot's G5; the second half
(hart-generic `p_sched`/`procs_inv`) is an independent sweep.

## Why a fraction cannot work

`KptTree.tlb_inv_pt root_ppn` bundles per-hart register cells (`satp ↦ᵣ`,
`tlb ↦ᵣ`, `pmp_config`) with the GLOBAL `ptree_own 2 (DfracOwn 1) t` +
`kmap_auth M` (t, M existential). The tree genuinely MUTATES: the model's
page walk writes A/D bits back (`SRegime.sr_absorb` returns
`gen_heap_interp σ'.(mem)`), and a memory write needs full ownership of the
written bytes. Presetting A/D at construction would dodge the writeback but
means changing the C source (mappages sets V|perm only) and regenerating the
image — off the table.

## The design

1. **`kpt_inv` — the shared-table invariant** (new, namespace `kptN`):
   ```
   kpt_inv root := inv kptN (∃ t M, ptree_own 2 1 t ∗ kpt_ad_auth t ∗
                              kmap_auth M ∗ ⌜kpt_tree_spec_gen root M t⌝)
   ```
   persistent, allocatable once out of kvminit's exclusive post.
   `kmap_auth` stays inside (the `kmap_at` agreement happens inside the
   absorb, where the invariant is open — no fractional auth needed).

2. **`kpt_ad_auth`/`kpt_lb` — an A/D-monotone lower-bound ghost on the
   tree.** Order: `ptree_ad_le t t'` = same structure, every PTE's non-A/D
   content equal, A/D bits ⊆ (the walk's `pte_set_ad` only ORs bits, so
   every writeback is `ad_le`-increasing). Auth rides in `kpt_inv`; the
   persistent `kpt_lb t0` is what a hart's TLB coherence is stated against.

3. **The per-hart residue of `tlb_inv_pt`**: satp cell + satp facts +
   `tlb ↦ᵣ tlbvec` + `∃ t0, ⌜tlb_ok_pt 0 t0 tlbvec⌝ ∗ kpt_lb t0` +
   `pmp_config root` + `kpt_inv root`. Needs the preservation lemma
   **`tlb_ok_pt_ad_mono`**: `ptree_ad_le t0 t → tlb_ok_pt asid t0 v →
   tlb_ok_pt asid t v`-ish (a cached entry was filled AFTER its walk set
   A/D, so monotone growth cannot invalidate it — verify against
   `tlb_ok_pt`'s actual clauses; if an entry can cache a PTE whose A/D the
   tree later grows, state the mono lemma at whatever granularity holds).

4. **`sr_absorb` becomes mask-carrying.** The record field gains a mask:
   `∀ E, ↑kptN ⊆ E → … sr_inv ={E}=∗ …`. Every call site (grep: ~15 sites
   in SmodeCorePt / WpSmodePtMem / WpSconfLock / ProofUart / WpPlic + the
   engines that plumb it) supplies its ambient mask + `solve_ndisj`; every
   ambient mask in the tree is `⊤ ∖ ↑minstretN` or narrower BY OTHER
   namespaces (devN sub-spaces), so `↑kptN ⊆ E` discharges everywhere —
   nobody else ever opens `kptN`. The strans_regime INSTANCE's absorb
   proof is the real rework: open `kpt_inv`, `tlb_ok_pt_ad_mono` off the
   hart's `kpt_lb`, do the writeback against the invariant's `ptree_own`,
   bump `kpt_ad_auth`, mint the new `kpt_lb`, close.

5. **`kvminithart` gets ONE hart-generic contract**: consumes `kpt_inv
   root` (persistent) + this hart's own `strans_bit bare` / `tlb ↦ᵣ` /
   satp / pmp cells; no exclusive tree anywhere. MAIN's boot arm gains an
   assembly between kvminit and kvminithart: allocate `kpt_inv` from
   kvminit's post (`ptree_own` + `kmap_auth` + spec fact) and persist
   `kernel_pagetable ↦₈□`. The secondary arm receives `kpt_inv` through
   the `started` payload P (persistent ✓).

6. **`strans_name : CPU -> gname`** (the 5-line change, 5 use sites:
   RiscvPtsto.v:122, IntrDefs.v:444,452, RiscvAdequacy.v:241,242) rides in
   this sweep — satp/tlb are per-hart, so their transit ghost must be too.

## Sequencing (after the boot-bridge agent lands)

1. This project (one central sweep: SRegime + KptTree + the kpt ghost +
   call-site mask plumbing + kvminithart respec/reproof + main's new
   assembly — ProofMain's kvm group changes).
2. Hart-generic `p_sched`/`procs_inv` (separate sweep, SchedCtx + scheduler
   + yield/sleep consumers: the parking hart's identity becomes a VALUE in
   the lock resource instead of the ambient `cid_word`).
3. `SpecMainSecondary`/`ProofMainSecondary`: the spin loop (iLöb over
   lw/sext.w/beqz), `wp_fence_gen_later_s_sconf` strips the `▷ P`,
   printk("hart %d starting") out of P's `printk_env`, kvminithart (new
   contract) / trapinithart / plicinithart, scheduler with the
   hart-generic `procs_inv` from P + this hart's own cpu_own/trap_csrs.
   The deposit wand in SpecMain grows what secondaries consume:
   `kpt_inv root` and the hart-generic `procs_inv`.
4. The whole-system adequacy with `cs = all harts`: hart 0 via
   ENTRY ∘ boot-bridge ∘ MAIN-boot, harts ≠ 0 via
   ENTRY ∘ boot-bridge ∘ MAIN-secondary; the image carve + `started_inv`
   allocation + P instantiation inside the `={⊤}=∗`.
