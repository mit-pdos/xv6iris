# Project: R/W/X-accurate kernel PT, code points-to, and non-identity mappings

STATUS: DESIGN CHECKPOINT — proposed and once-reviewed in outline; NOT started.
The design below is UPDATED for the two refactors that landed after the
original proposal (the `sie_cap_gpr` ambient bundle and the Bare-regime
translation slot — see design/interrupts.md); several pieces got strictly
easier because of them.  Open decision points at the bottom need sign-off
before implementation.

## Goal

Replace the "DRAM uniformly RWX" deviation (KptPt.v header) with the real
kvmmake shape: kernel text `[KERNBASE, etext)` mapped R|X, data
`[etext, PHYSTOP)` R|W, devices R|W — plus the NON-IDENTITY mappings xv6
actually has: TRAMPOLINE (already a static tree clause), per-proc kernel
stacks (dynamic pas), and (user-PT side) TRAPFRAME.  Introduce a CODE
points-to beside the data points-to; both assert OWNERSHIP of the physical
bytes plus a statement about the va's mapping under the current regime.
Constraints fixed by review: the data points-to surface (`↦ₘ` notation,
`mem_ram`, every existing spec/proof) stays unchanged; the new code
points-to lives INSIDE `instr_bytes`, and `instr`'s statement is unchanged.

## Verified ground facts (re-verify only if the image regenerates)

- `KernelSyms.etext = 0x80007000` (page-aligned; 7 text pages incl. the
  trampoline page at ppn 0x80006).  Model RAM = [0x80000000, 0x88000000).
- `KernelInstrs.kernel_bytes` spans 0x80000000..0x8000611f — entirely below
  etext.  ✓ every instruction byte is a text-region byte.
- **`KernelData.kernel_data` has 5332 bytes BELOW etext** (0x8000541e..
  0x80006fff — inter-function padding + the trampoline page's tail).  No
  current proof consumes them (all `kernel_data_string` uses are ≥
  0x80007000: "uart" @0x80007030, "kmem" @0x80007040, pr/ftable/time names).
- Adequacy (RiscvAdequacy.v ~l.203-241) mints `↦ₘ` for every byte of
  `g.(gmem)` — the init split at etext happens there.
- The planned `kvm_map` (this file's sibling kvm-spec.md, item (b)) already
  uses split perms: text perm 10 (R|X), data perm 6 (R|W) — no spec
  loosening needed in the kvm chain.

## The design

### 1. Permission classes + region split (KptPt.v, iris-free)

- `Inductive kperm := KP_rx | KP_rw.`  `kperm_flags`: 0xCB / 0xC7 (A/D-preset
  bases; the §12 `_ad` layer generalizes verbatim, `PTE_TEXT_ad` new).
  `kperm_allows`: fetch → KP_rx; load → either (BOTH bases grant R — this is
  what keeps every load path's key unchanged); store/AMO → KP_rw.
- `kpt_text_vpn` = [0x80000, 0x80007), `kpt_data_vpn` = [0x80007, 0x88000),
  `kpt_dev_vpn` unchanged.  `kpt_lflags` region-keyed.  Hardcode
  `text_end := 0x80007000` next to ram_base/ram_size in RiscvPtsto (cross-
  check `= KernelSyms.etext` by vm_compute higher up) — keeps the base
  memory layer off the kernel dump.
- Check lemmas per (class, access), same vm_compute dispatch:
  `kpt_check_fetch` gains a text-vpn premise, `kpt_check_store/amo` a
  data/dev-vpn premise, `kpt_check_load` passes on both.  Ripples into the
  `kpt_variant_*` corollaries (KptTree §1-§2).

### 2. The claim facade `kmap_at` (new file KMap.v)

```
Class kmapGS Σ := { kmap_inG :: ghost_mapG Σ (mword 27) (mword 44 * kperm);
                    kmap_name : gname }.        (* CpuId-style gname class *)
Definition kmap_static (vpn : mword 27) (pc : kperm) : Prop :=
  (kpt_text_vpn vpn ∧ pc = KP_rx) ∨
  ((kpt_data_vpn vpn ∨ kpt_dev_vpn vpn) ∧ pc = KP_rw).
Definition kmap_at (vpn : mword 27) (ppn : mword 44) (pc : kperm) : iProp :=
  ⌜kmap_static vpn pc ∧ ppn = kpt_leaf_ppn vpn⌝ ∨ vpn ↪[kmap_name]□ (ppn, pc).
```
Persistent, timeless, duplicable — "under the current AND ALL FUTURE kernel
translation regimes, vpn maps to ppn with at least pc".  HYBRID (recommended
over all-in-ghost): the static identity regions ride the pure arm (honored
by BOTH regimes by construction — Bare is identity-everything, KPT's region
clauses grant exactly these); the ghost map holds ONLY dynamic entries
(kstacks; extensible).  Avoids a ~49k-entry initial gmap and keeps the
points-to definitions ghost-free (no kmapGS in the base files).
Monotonicity = ghost_map elems persisted, never deleted; the Bare→KPT
switch is the single point where outstanding claims are re-honored, which
is why text claims are RX-ONLY even though Bare would allow RWX.
IMPORTANT: static claims are IDENTITY-ONLY.  The trampoline mapping is NOT
a claim (a non-identity pure fact would be usable under Bare — unsound);
it stays the dedicated static clause in the tree spec, consumed by the
ktramp/userret engines exactly as today.

### 3. Where the ghost auth lives — NOW EASY (the slot exists)

`strans_inv` is already `(bare_inv ∗ stvec) ∨ (∃root, tlb_inv_pt root)`:
- KPT arm: `tlb_inv_pt` gains `∃ M, ghost_map_auth kmap_name 1 M` and the
  tree spec becomes `kpt_tree_spec_gen root M t`:
    pt_base ∧ (static regions → A/D-variants of region leaves)
    ∧ (tramp clause, unchanged) 
    ∧ (∀ vpn↦(ppn,pc) ∈ M: dyn-range vpn ∧ RAM ppn ∧ maps A/D-variant of
       mk_pte ppn (kperm_flags pc))
    ∧ (∀ vpn ∉ static ∪ {tramp} ∪ dom M: blocks).
  `dom M ⊆` the kstack va range ∪ {tramp?no} — keep constrained for future
  fault lemmas.
- Bare arm: `bare_inv` gains `ghost_map_auth kmap_name 1 ∅` — ghost claims
  are REFUTABLE under Bare (lookup in ∅), static claims are identity, so
  `bare_absorb` stays provable.  Once any kstack fragment is persisted the
  Bare arm can never be re-established: Bare→KPT one-way, no extra ghost.
- The kvminithart switch lemma (kvm-spec.md item 3): dissolve Bare arm,
  build tlb_inv_pt from `pt_rep0 t kvm_map` (which will now have the split
  perms + kstack entries), insert+persist the 64 kstack claims, hand out
  `[∗ list] i, kmap_at (kstack_vpn i) (stk i) KP_rw` + the stvec cell.

### 4. Points-to layer (RiscvPtsto.v — ghost-free changes)

- `addr_is_text a := ram_base ≤ a < text_end`;
  `addr_is_kdata a := text_end ≤ a < ram_base + ram_size`.
- CODE: `text_pointsto a dq b := pointsto a dq b ∗ ⌜addr_is_text a⌝`
  (notations `↦ₓ{dq}`/`↦ₓ□`; `code_ram` analogue of `mem_ram`).  The RX
  claim for identity text is derivable via the static arm — not stored.
- DATA: `mem_pointsto a dq v := pointsto a dq v ∗ ⌜addr_is_kdata a⌝`
  (RECOMMENDED: unconditional strengthening; `mem_ram` still holds since
  kdata ⊂ ram).  Requires re-scoping `kernel_data` to ≥ etext (drop the
  5332 unused sub-etext bytes, or expose them as `↦ₓ□`).  FALLBACK if
  sub-etext data loads ever materialize: the dq-conditional conjunct
  (`match dq with DfracDiscarded => True | _ => addr_is_kdata a end`) —
  survives split/combine/persist; keeps read-only image data anywhere.
- GENERAL (non-identity) forms for kstack/future use:
  `vmem_pointsto va pa dq b := pointsto pa dq b ∗ ⌜addr_is_ram pa⌝ ∗
   ⌜page-offsets agree⌝ ∗ kmap_at (vpn va) (ppn pa) KP_rw` (and a vcode
  analogue).  `a ↦ₘ v ⊢ vmem_pointsto a a v`.  Only NEW proofs (kstack
  demonstrator) use these; sp-migration onto KSTACK vas is a separate later
  project — this project builds the machinery + a width-8 leaf demonstrator.
- `kernel_text` and `instr_bytes`' footprint switch `↦ₘ□ → ↦ₓ□`; `instr`
  statement unchanged; `fetch_from_instr_bytes` (M-mode, no perm check)
  re-proves off `addr_is_text ⊆ addr_is_ram`; KernelText's `mk_rvc/mk_base`
  tactic interfaces unchanged.  Adequacy init splits at etext (below →
  persist to `↦ₓ□`; above → own `↦ₘ`).

### 5. Absorption re-keying (the only engine-tier change)

The `s_regime` record's `sr_absorb` key changes from the blanket
`addr_is_ram va` to claim + class:
```
sr_absorb : ∀ acc va ppn pc σ, s_acc_ok acc → kperm_allows pc acc → …reg facts… →
  ⊢ kmap_at (svpn_of va) ppn pc -∗ reg_interp -∗ gen_heap -∗ sr_inv ==∗
    ∃ σ', ⌜translateAddr va acc = Ok (Physaddr (ppn ++ pageoff va), …)⌝ ∗ … ∗ sr_inv
```
(output pa = the claim's ppn; identity in the static arms).  Instances:
- `kpt_absorb`: ghost arm via auth agreement + `kpt_tree_spec_gen`'s M
  clause; static arm via the region clauses.  The O1/O2/O3 total case
  analysis (`kpt_translateAddr_cases`) is leaf-word-generic and survives;
  only the flag-byte dispatch becomes class-indexed.
- `bare_absorb`: static → pa=va identity translate; ghost → refuted (∅).
- `strans_regime` dispatch: unchanged shape.
- LOADS: `kperm_allows pc (Load Data)` holds for both classes, so identity
  load leaves keep deriving their claim from `addr_is_ram` (region-decide
  → static arm) — NO leaf signature changes.  STORES/AMO extract
  `addr_is_kdata` from their own (own-fraction) `↦ₘ` — one proof line per
  store leaf.  FETCH: the fetch engine (`s_regime_fetch`) derives the RX
  claim from the chunk's own `↦ₓ□` bytes (per-chunk for straddles).
  `sr_absorb_dev` unchanged (dev region's flag byte was already 0xC7).
- Soundness win: stores to text become UNPROVABLE.

### 6. TRAPFRAME (open question, again)

In xv6, TRAPFRAME is a USER-PT mapping (kernel C code reaches the trapframe
through the identity data mapping; only trampoline code uses the va, under
the user table — already handled by `upt_tree_spec`'s `pte_tf`).  Proposal:
kernel-PT ghost covers kstacks (+ future) only; TRAPFRAME stays in the upt
layer.  If a kernel-PT trapframe deviation is wanted instead, the ghost
handles it exactly like kstacks.  NEEDS SIGN-OFF.

## Open decision points (carry to review)

1. TRAPFRAME scope (above).
2. Hybrid claims (recommended) vs all-in-ghost (uniform but 49k-entry init).
3. `kernel_data` re-scope to ≥ etext (recommended) vs dq-conditional
   `mem_pointsto` conjunct.
4. `kperm` two-class enum (recommended; matches the two real flag bytes) vs
   {R,W,X} record.
5. Kstack claims minted at the kvminithart switch; sp-migration deferred.

## Staging (each phase builds green independently)

1. KptPt region split + per-class check/update lemmas + kpt_variant ripple.
2. KMap.v (kperm, kmapGS, kmap_at, static-intro/agree/insert lemmas).
3. RiscvPtsto: addr_is_text/kdata, ↦ₓ, mem_pointsto conjunct, vmem/vcode;
   audit `↦ₘ` construction sites (grep `rewrite /mem_pointsto`); re-scope
   kernel_data (KernelDataInv + dump tooling if needed).
4. KernelText/InstrBytes/adequacy: ↦ₓ□ image + init split.
5. KptTree/IntrDefs-strans/engines: kpt_tree_spec_gen + auth in both slot
   arms, re-keyed absorption instances + strans_regime dispatch, fetch
   engine; store/AMO leaf one-liners.
6. Switch lemma + kstack claims + vmem width-8 leaf demonstrator
   (dovetails with kvm-spec.md items 2-3, which this project's tree-spec
   revision unblocks — the "boot introduction" there IS this switch lemma).

## Interactions to keep in mind

- The sconf tier is regime-blind through `strans_regime` — the re-keying
  in §5 is invisible to whole-function specs (they thread `sie_cap_gpr`
  only).  Only the record fields, the two instances, the dispatch, and the
  engines change; leaf statements keep their shapes.
- The pt2 switch window (TransPt) references `kpt_tree_spec` — becomes
  `kpt_tree_spec_gen` with the SAME M across the window (auth rides in
  `pt_frame`/the pt2 invariant).
- `intr_frame` carries `tlb_inv_pt root` — gains the auth silently (it is
  inside tlb_inv_pt); nothing at the interrupt tier changes.
- tlb_ok_pt / the TLB layer is untouched (entries are "some vpn the tree
  maps" — generalizing the tree spec suffices).
