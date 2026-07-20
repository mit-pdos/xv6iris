# Project: kvminit / kvmmake / kvmmap / mappages / walk proofs (KvmSpec.v)


The five spec statements are CHECKED IN as compiled iProp definitions in
KvmSpec.v — read its header first: it fixes the design (edited-table vs
ambient-regime separation; the `pt_rep t m` map view; walk's
`ptree_same_rep` + `ptree_level0` post; mappages' k-of-n prefix post; the
`panic_wp` absorption of kvmmap's failure arm).  Remaining work, in order:

1. **THE TRANSLATION-REGIME PARAMETERIZATION (decided — no leaf
   duplication).**  The S-mode leaf layer's contact with translation is
   NARROW: every leaf threads `tlb_inv_pt root_ppn` as an opaque resource,
   the step engines discharge the FETCH through
   `tlb_inv_pt_translateAddr_fetch`, and the data leaves run their
   data-side translation through `tlb_inv_pt_translateAddr_load/_store`
   (/the AMO instantiation) inside the engine callback.  Nothing else in
   any leaf mentions the MMU.  So: define ONE interface and make the layer
   generic over it (`SRegime.v`):
     `Record s_regime := { sr_inv : iProp; sr_fetch; sr_load; sr_store;
        sr_amo }` — each `sr_<acc>` an absorption entailment in the EXACT
     shape of TrampStepPt's `Habs` (the proven pattern): for a va with
     `addr_is_ram va` + the standard reg facts,
     `reg_interp ∗ gen_heap ∗ sr_inv ==∗ ∃ σ', ⌜translate = Ok (va
     identity)⌝ ∗ ⌜mdev unchanged⌝ ∗ ⌜sregs same-or-one-tlb-write⌝ ∗
     ⌜the access-class PMP facts at σ'⌝ ∗ interps ∗ sr_inv`.
   Instances:
     - `kpt_regime root_ppn`: `sr_inv := tlb_inv_pt root_ppn`, fields =
       the four EXISTING absorption wrappers, η-expanded with the PMP
       facts peeled-and-resealed (exactly what `ktramp_fetch_habs`
       already does; ~zero new proof).
     - `bare_regime`: `sr_inv := ∃ satp0, satp ↦ᵣ satp0 ∗ ⌜Mode(satp0) =
       Bare⌝ ∗ pmp_config r` (BareMode.v).  The fields are TRIVIAL:
       `translateAddr` at Bare short-circuits to the identity before
       touching the TLB — one new pure reduction
       (`exec_translateAddr_bare`, the S-mode analog of UserTranslate
       §1's mode dispatch, at `satpMode_of_bits = Bare`), σ' = σ, left
       sregs disjunct always; the PMP facts come off `pmp_config`.
   The leaves keep both SPEC CLEANLINESS and generality: a generic leaf
   states `sr_inv R` where it stated `tlb_inv_pt root_ppn` (the
   `root_ppn` parameter disappears from generic statements — it was only
   the invariant's index), and its proof changes only the absorption call
   to the record field.  MIGRATION (additive at every step, `make proofs`
   green per commit; coordinates with the interrupt sweep by never
   renaming what its files reference):
     a. SRegime.v (record + kpt_regime) and BareMode.v (bare_inv +
        bare_regime).  Sanity-check the record-of-entailments encoding
        compiles cleanly; fallback is TrampStepPt's Section-Variables
        style (Variable R-pieces), same content.
     b. SmodeCorePt: generalize the unified fetch + the two step engines
        over `R : s_regime` (new Section); the OLD names
        (`wp_instr_s_tlbinv_pt`, `wp_instr_s_config_tlbinv_pt`,
        `tlb_inv_pt_fetch`) become Definitions instantiating
        `kpt_regime` — zero downstream churn, sweep unaffected.
     b''. STATUS UPDATE (2026-07-18e): the DATA side of stage (c) is DONE —
        sr_transform (the third regime field: the pointer-masking
        effective-address transform is the identity at pmlen 0 in EITHER
        mode; mode-generic exec_transform_effective_address_mode), every
        vmem tower (widths 8/4/1 + AMO) takes the transform outcome as
        the premise Htea instead of satp0/Sv39 hypotheses, and ALL data
        leaves are regime-generic with kpt_regime restatement wrappers
        under the old names: wp_{cld,csd}_s_r (Leaves), wp_{ld,sd,clw,lw,
        csw,sw,sb}_s_r (Mem), wp_{sd_zero,clw_lockinv(+_locked),
        sw_zero_lockinv,amoswap_lockinv}_..._r (Lock — regime binder Rg
        there; R is the lock's resource).  The sconf files' tower call
        sites discharge Htea inline from their own satp facts (interface
        unchanged).  REMAINING in stage (c): the NON-memory files
        WpSmodePtAlu/Btype/Ctl — pure renames now (statements swap
        tlb_inv_pt->sr_inv R, engine calls already generic; use the
        validated wrapper recipe), plus WpSmodePtMemWrap's _scfg
        wrappers.  Then stage (d), the kalloc-cone flip.
     b'''. STAGE (c) COMPLETE (2026-07-18f): the non-memory files
        (Alu 34 / Btype 30 / Ctl 16 / MemWrap 13 lemmas) converted
        wholesale (pattern: every `Lemma <x>_pt (root_ppn : mword 44)`
        becomes `<x>_r (R : s_regime)` + a kpt_regime restatement
        wrapper) — all four compiled first try; the ENTIRE WpSmodePt
        leaf layer is now regime-generic.  ONLY stage (d) remains
        before the Bare boot path opens: flip the kalloc cone's
        whole-function statements (memset_page, mycpu,
        push_off/pop_off(+Csr/Mem), holding, acquire(+Top), release,
        kalloc) from `tlb_inv_pt root_ppn` to `sr_inv R` — bodies
        change only leaf names `_pt`->`_r` applied at R — keeping
        old-name kpt instances for the unconverted callers (kfree,
        wakeup, ...).
     b'. STATUS: (a) and (b) are DONE (SRegime.v; SmodeCorePt.v now proves
        the generic `s_regime_fetch` / `wp_instr_s_regime` /
        `wp_instr_s_config_regime`, with the old names as restatement
        Lemmas at `kpt_regime` closed by `exact` — conversion through the
        record projection; full build green, zero downstream churn).  The
        generic fetch proof got SHORTER: `sr_absorb`'s `pmp_grant_facts`
        conjunct replaced every open-peel-reseal block and the
        L1pmp*/L2pmp* backwards transports.
     c. Leaf sweep (script-assisted, file-by-file like previous sweeps):
        WpSmodePtLeaves/Alu/Ctl/Btype/Mem/MemWrap/Lock generalize over R;
        old names re-instantiated at `kpt_regime` so every current
        consumer compiles untouched.  Wrapper recipe (validated on the
        engines): the generic lemma gets the new name; the old name is a
        RESTATEMENT Lemma (verbatim original statement) closed by `exact
        (<generic> (kpt_regime root_ppn) <explicit binders>)` — never a
        Definition (implicit `dq` would become positional and churn every
        call site).  TWO REAL TECHNICAL POINTS found scoping the sweep,
        both in the DATA leaves: (i) they peel the satp VALUE from
        `tlb_inv_pt` and feed `Lsatp_pc`/`Hmode : Mode=Sv39` to the vmem
        towers — an opaque `sr_inv` cannot be peeled, and Bare has a
        different mode value.  The towers need those premises only to
        drive `get_transformed_data_addr` (the pointer-masking effective-
        address transform, which reads the satp mode but is the IDENTITY
        whenever PMM is Disabled): generalize the towers to take the
        transform's exec OUTCOME as a hypothesis (`Hgta : exec
        (get_transformed_data_addr …) s = Some (ea, s)`), tower-style like
        the translate outcome — then prove two tiny dischargers, Sv39 and
        Bare, of that fact from PMM-off (mode-independent conclusion).
        (ii) the post-translate PMP/PMA facts at `s_tr` currently come
        from the same peel + `Hprestr` transports — they now come straight
        from `sr_absorb`'s `pmp_grant_facts` at s_tr (same simplification
        as the engines); the `matching_pma_region`/PMA-readable facts come
        from `Hpma_all` at σ + `pt_regs_preserved` transport, unchanged.  (WpSmodePtUart stays kpt-specific
        for now — its DEV absorption needs kpt-shaped premises; add dev
        fields to the record only when a Bare device access is actually
        needed, i.e. when proving panic/printf rather than axiomatizing
        `panic_wp`.)
     d. Flip the kalloc cone to regime-generic statements (`sr_inv R`
        replaces `tlb_inv_pt root_ppn`; mechanical rename + leaf-name
        swaps): memset_page, mycpu, push_off/pop_off(+Csr/Mem), holding,
        acquire, release, kalloc — again keeping old-name kpt instances
        for existing callers (kfree, wakeup, …, which can migrate
        lazily).  KvmSpec.v's `Variable SINV` becomes
        `Variable R : s_regime` (`SINV := sr_inv R`).
   ORTHOGONALITY NOTE for the interrupt sweep: regime (what translation
   invariant fetches go through) and SIE-agnosticism (the sconf bundle)
   are independent axes; the sweep's v2 engines should eventually take a
   regime argument the same way, and TrampStepPt's Variable-INV engine is
   a candidate to re-express as an `s_regime` whose fields are keyed on
   the trampoline va instead of `addr_is_ram` — both are follow-ups, not
   blockers.
   BOOT NOTE: the Bare→Sv39 switch at kvminithart needs NO pt2-style
   window — Bare execution never fills the TLB, kvminithart's first
   sfence zeroes it anyway, so after the `csrw satp` the proof builds
   `tlb_inv_pt` directly from `pt_rep t kvm_map` + `tlb_ok_pt_empty`,
   and the second sfence is an ordinary Sv39 step.
2. **DONE — the pure construction layer + its Iris side (PtBuild.v).**
   THE xv6 SHAPE STRENGTHENING: `ptree_blocks` demands only model-
   invalidity (`pte_invalid`), but xv6's walk tests the V BIT alone — a
   V=1 reserved-encoding stop word would make the C code descend
   garbage.  PtBuild therefore works on `ptree_blocks0` (stop word =
   LITERAL ZERO), `pt_rep0`, `ptree_same_rep0` (bridges
   `pte_invalid_zero` / `ptree_blocks0_blocks` / `pt_rep0_rep`; KvmSpec
   states everything on the 0-forms, and walk_spec carries a
   `⌜pt_rep0 t m⌝` premise — without it a V=1 slot need not have an
   owned kid and the descend is unprovable).  Contents: §1 pt_rep0/
   same_rep0/level0/`ptree_maps_level0`/`mappages_pte`/`vpn_at`/
   `pt_insert_run`; §2 `pt_empty_node` (+`ptree_blocks0_empty`/
   `pt_rep0_empty`); §3 `ptree_set_leaf0_maps_self` (needs only the
   level0 path, not a classified old leaf), `ptree_set_leaf0_blocks_
   other`, `pt_rep0_insert` (the keystone: classified leaf through
   walk's slot = one map insert); §4 grafting — ext transports
   (`ptree_maps_ext`/`_ext1`, `ptree_blocks0_ext`/`_ext1`: a vpn's walk
   facts depend only on its own path), `pt_ptr_pte b := mk_pte b
   PTE_PTR` (+valid/ptr/`u_next_base` = b), `pt_graft2`/`pt_graft1`
   (+`pt_graft1_kid`) with projection laws, `ptree_level0_intro`,
   `pt_graft1_level0` (after the L1 graft the path reaches L0 with a
   ZERO slot), `pt_graft2_same_rep0`/`pt_graft1_same_rep0`; §5 Iris —
   `zero_page_to_node` (4096 ↦ₘ-zero bytes at ppn b's page ⇒
   `ptree_own lvl` of `pt_empty_node b`, any level; via
   `big_sepL_seq_chunk` + `word_pointsto_intro` + Pt4kWalk's new
   `page_base_unsigned`/`pa_add_page_slot` address facts),
   `pt_kids_own_ins` (insert a child under a kid-free index),
   `ptree_own_slot2_ro`/`slot1_ro` (walk's descend reads),
   `ptree_own_graft2`/`_graft1` (slot cell out; closing wand takes the
   rewritten pointer-PTE cell + the zeroed child), and
   `ptree_own_level0_upd` (mappages' remap-check read + leaf store).
3. **wp_walk** (DONE, all four paths Qed; WpWalk.v registered in
   _CoqProject, full build green).  Architecture: WpWalkInstr.v holds
   the complete 47-instruction decode catalog (wdec_*/wi_*); WpWalk.v
   holds three Qed-sealed chunks — `wp_walk_epilogue` (+0x52..ret),
   `wp_walk_tail` (+0x46..+0x50: a0 := L0 slot addr, then epilogue),
   `wp_walk_alloc` (+0x72..+0x94: beqz-s6 fall, kalloc, null-exit via
   epilogue with a0=0, else memset + `zero_page_to_node` + graft-cell
   sd + c.j rejoin; parameterized over cellA/old word/child level and
   a close wand ∀ b, cellA ↦₈ pt_ptr_pte b -∗ ptree_own clvl 1
   (pt_empty_node b) -∗ ptree_own 2 1 (tG b); the SUCCESS continuation
   receives the walk-spec continuation BACK as a wand premise so the
   one linear Hcont threads through both exits) — and `wp_walk_r`
   (walk_spec shape: premises a1=1M-aligned root a0, a2=1, va<2^38,
   pt_rep0 t m; post = callee_saved + kalloc_env + ptree_own t' with
   `ptree_same_rep0 t t'` + a0=0 ∨ level0-slot-addr payload) with four
   paths: mapped descend/descend, arm 3 (descend/descend to zero L0),
   arm 2 (descend + graft1 alloc), arm 1 (graft2 alloc + loop iter 2
   on the grafted tree + graft1-on-t2 alloc; same_rep0 by trans of
   pt_graft2_same_rep0/pt_graft1_same_rep0; payload pt_graft1_level0).
   Axioms of wp_walk_r = the 6 standard model stubs only.  Proof-
   engineering notes that carry forward: instr wi_* facts are
   persistent (reusable across loop iterations); repeat ne-peels
   delta-see through set-vars (overshoot ⇒ continue inline:
   insert-hit, more peels, add_vec_zero_l, reflexivity); register
   facts across kalloc/alloc-chunk boundaries hop via the transport
   fact (Htrans c is_cs_idx-guarded) then peel the pre-call chain.
4. **wp_mappages** (DONE, Qed; WpMappages.v + WpMappagesInstr.v registered;
   full build green, axioms = the 6 standard model stubs).  Architecture:
   WpMappagesInstr.v = the 56-instruction decode catalog (mdec_*/mi_*).
   WpMappages.v = `mappages_sp_cancel`, a Qed-sealed `wp_mappages_epilogue`
   (+0x9c..+0xb0: the 9 cldsp restores + addi16sp + ret, both exits funnel
   here with a0 decided), a fuel-inducted `wp_mappages_loop` (induction on
   the REMAINING page count `rem`, NOT npages — invariant carries k+rem=npages,
   the register-file column facts, `pt_base tk = pt_base t`, and `pt_rep0 tk
   (pt_insert_run m vpn0 ppn0 perm k)`; each iteration calls `wp_walk_r`,
   recovers callee-saved regs via `callee_saved_lookup`, reads the L0 slot
   pinned to zero by `pt_rep0_level0_zero` + `pt_insert_run_lookup_None`,
   collapses srli/slli/or/ori to `mappages_pte` via the §8 bridges,
   stores through `ptree_own_level0_upd` + `pt_rep0_insert`, then either
   funnels to the epilogue (walk-null → −1 at k<npages; last page → 0 at
   k=npages) or steps s1 by PGSIZE and recurses on IH), and `wp_mappages_r`
   (the prologue: 10-slot frame, the three entry checks falling by the
   aligned/nonzero premises via `mappages_align_probe`/`mappages_size_nonzero`,
   loop-state setup `s2 := last-page va` via `mappages_s2_val`, then the loop)
   + `mappages_spec_holds : ⊢ mappages_spec`.  KvmSpec's mappages/kvmmap
   specs now premise `mappages_perm_ok perm` and the pa-run bound
   `uint pa + npages*4096 < 2^56`.  PtBuild §8 holds all the pure bridges.
5. **wp_kvmmap** (DONE, Qed; WpKvmmap.v registered, full build green,
   axioms = 6 standard model stubs; panic_wp is a proper HYPOTHESIS, not a
   global axiom).  Thin wrapper: 2-slot frame, three c.mv swapping mappages's
   size/pa args (a2↔a3 via a5), jal mappages (wp_mappages_r at the swapped
   map P6, whose va/pa/vpn0/ppn0 coincide with kvmmap's via HP6a1/HP6a3),
   then the beqz on a0: FALL (k=npages, a0=0) → the 2-slot epilogue → post
   with the full run; TAKEN (k<npages, a0=-1) → the panic arm (auipc/addi/
   jal panic) → `panic_wp` absorbs it.  Frame decodes reuse KernelRvcDecode's
   shared mdec_ccc..cf0 templates; only the 3 c.mv, the c.bnez, and the two
   base jals are decoded locally.  callee_saved mm mr recovered from
   callee_saved P6 mr since P6 = mm off the callee-saved set (only a2/a3/a5
   clobbered).  `kvmmap_spec_holds : ⊢ kvmmap_spec`.
6. **wp_kvmmake / wp_proc_mapstacks / wp_kvminit** (NOT STARTED; walk +
   mappages + kvmmap all DONE and green as the building blocks).  This is
   a large, design-heavy NEW LAYER, not an incremental proof.  Full design
   checkpoint (2026-07-19) so the next session starts from the design, not
   from scratch:

   **(a) Constants to add** (most do NOT exist yet — only UART0/plic_base
   in DevModel, TRAMPOLINE in TrampPt, etext/proc in KernelSyms, NPROC in
   WpWakeup).  From xv6-riscv/kernel/memlayout.h + riscv.h:
     - KERNBASE = 0x80000000, PHYSTOP = KERNBASE + 128*1024*1024 = 0x88000000
     - UART0 = 0x10000000, VIRTIO0 = 0x10001000, PLIC = 0x0c000000
     - MAXVA = 1 << (9+9+9+12-1) = 0x4000000000; TRAMPOLINE = MAXVA - PGSIZE
       = 0x3FFFFFF000 (already in TrampPt.v)
     - KSTACK(p) = TRAMPOLINE - (p+1)*2*PGSIZE  (guard page below each stack)
     - proc array base = KernelSyms.proc = 0x80012778; sizeof(struct proc)
       needed for the p++ stride (read from the +0x78 addi in the
       proc_mapstacks loop: 0x168 = 360 bytes — CONFIRM against the dump).
     - PTE flag values: perm passed to kvmmap is WITHOUT V (mappages ORs V
       in): R|W = 2|4 = 6, R|X = 2|8 = 10.

   **(b) The [kvm_map] gmap literal** (kernel/vm.c kvmmake order; each
   region is a [pt_insert_run] applied to the accumulator so the six
   kvmmap posts chain DEFINITIONALLY -- the k-th kvmmap's post
   [pt_insert_run m_prev vpn0_k ppn0_k perm_k npages_k] becomes the next
   call's precondition [pt_rep0 t m_k]):
     1. UART0    va=pa=0x10000000, 1 page,      perm 6   (R|W)
     2. VIRTIO0  va=pa=0x10001000, 1 page,      perm 6
     3. PLIC     va=pa=0x0c000000, 0x4000000 B = 16384 pages, perm 6
     4. text     va=pa=KERNBASE,   (etext-KERNBASE)=0x7000 = 7 pages, perm 10 (R|X)
     5. data     va=pa=etext,      (PHYSTOP-etext)=0x7FF9000 = 31977 pages, perm 6
     6. tramp    va=TRAMPOLINE, pa=trampoline (the phys page), 1 page, perm 10
     then proc_mapstacks: 64 KSTACK(i) pages -> kalloc-chosen pas, perm 6.
   NB the PLIC (16384) and data (31977) runs are BIG: mappages_spec's
   premises [uint va + npages*4096 <= 2^38] and [uint pa + npages*4096 <
   2^56] must hold -- check: PLIC pa 0x0c000000 + 16384*4096 = 0x10000000
   ok; data va 0x80007000 + 31977*4096 = 0x88000000 = 2^31+... < 2^38 ok,
   pa same < 2^56 ok.  So the existing bounds SUFFICE -- no spec loosening.
   Also each region's start is page-aligned by construction (all the
   constants are multiples of 0x1000) so [subrange va 11 0 = 0] discharges
   by vm_compute, and [mappages_perm_ok 6]/[mappages_perm_ok 10] are two
   fixed lemmas provable once (pte_valid/leaf/no_napot/pbmt0 of
   mk_pte 0 (6|1) and mk_pte 0 (10|1) -- all vm_compute on the flag byte).
   NO-REMAP obligation ([forall i<npages, m_k !! vpn_at vpn0_k i = None]):
   the regions are DISJOINT in va (devices < 0x10002000, PLIC region
   0x0c.., text/data 0x8.., tramp at MAXVA, stacks just below tramp) so
   each region's vpns are unmapped in the accumulator -- prove a disjointness
   lemma per region (vpn ranges don't overlap) feeding pt_insert_run_lookup
   -style reasoning; this is the main NEW pure-arithmetic burden.

   **(c) Spec signatures to add to KvmSpec.v** (currently only sketched in
   comments there):
     - [proc_mapstacks_spec]: args kpgtbl=a0, tree t repr m, the 64 KSTACK
       vpns unmapped, kalloc_env, panic_wp; post = ∃ (pas : nat -> mword 44),
       tree t' repr (m + {KSTACK i -> mk_pte (pas i) 6 | i<64}), pt_base
       preserved, kalloc_env restored.  Existential pas as a FUNCTION
       nat->pa (not a list) keeps the induction clean.  Fuel = remaining
       proc count, invariant carries the pas chosen so far (partial function
       / accumulator map).  Structurally = mappages' loop but the per-iter
       body is kalloc (env threading, null->panic) + kvmmap (needs panic_wp,
       aligned page from kalloc, KSTACK(i) aligned+unmapped+bounded).
     - [kvmmake_spec]: NO incoming tree (it kallocs the root itself); pre =
       kalloc_env with ENOUGH free pages (root + all intermediate PT nodes
       for the six regions + 64 stacks + 64 stack pages -- the kalloc_env
       must guarantee non-failure OR the spec's post is the ret=0/partial
       disjunction like mappages; SIMPLEST: require panic_wp and make every
       kalloc-null go to panic, so the post is unconditional full kvm_map).
       Post: ret(a0) = root pa, ptree_own 2 1 t with pt_rep0 t kvm_map (for
       the existential stack pas), + the root is a FRESH page.  Stack depth:
       kvmmake frame is 4 slots (ra,s0,s1,s2 at +0x00 c.addi16sp -32... check:
       +0x00 0x1101 = c.addi16sp -32? decode) -- but it CALLS mappages/walk
       which need 32; so n must be >= 32 + kvmmake's own frame.
     - [kvminit_spec]: kvmmake then [sd a0, kernel_pagetable]; needs the
       kernel_pagetable global cell.  Post: kernel_pagetable points at the
       kvm_map root.
   Get Nickolai's sign-off on the kvm_map shape + the "panic on any
   kalloc-null" simplification BEFORE building the proofs (spec-design
   preferences: constant depth bounds, no ad-hoc arg coupling).

   **(d) Decode catalogs** (mechanical but ~90 + ~44 instrs; reuse
   KernelRvcDecode's shared frame templates mdec_ccc..cf0 for the standard
   frames, like WpKvmmap did): WpProcMapstacksInstr.v (frame 0x715d = 80-byte
   =11 slots, the KSTACK arith auipc/lui/addi/mul-by-stride/sub, kalloc+kvmmap
   jals, the p<&proc[64] bne loop) and WpKvmmakeInstr.v (kalloc+memset+6*
   {auipc/lui/addi arg setup + kvmmap jal} + proc_mapstacks jal).  Generate
   programmatically as in WpMappagesInstr; the JAL residues = (target - pc)
   mod 2^21 (confirmed formula from walk/mappages/kvmmap).  WATCH the base
   ASTs for lui/mul/sub -- probe with the vm_compute-on-decode trick only if
   rvc_oneshot/decode_bridge_ms rejects a guessed AST (each miss = a full
   ~minute compile, so get the immediates right up front from the dump).

   **(e) Proof order**: proc_mapstacks FIRST (self-contained, unblocks
   kvmmake), then kvmmake (root kalloc + memset + zero_page_to_node at level
   2 + the six chained kvmmap calls + the proc_mapstacks call), then kvminit
   (kvmmake + one sd).  Each funnels through a sealed epilogue like the
   mappages/kvmmap ones.  The six kvmmap calls each want callee_saved
   recovery + the accumulator-tree transport (t_k repr m_k) between calls --
   the a0/a1/.. arg-register reloads between calls are the per-call auipc/lui
   /addi sequences already in the dump.
7. **Boot introduction** (separate, later): kvminithart establishes
   `tlb_inv_pt` from `pt_rep t kvm_map` — at which point `kpt_tree_spec`
   must be REVISED to the true per-region flags (text RX / data RW /
   devices RW; the KptPt uniform-RWX deviation dies), rippling into the
   `kpt_variant_check_*` dispatch (fetches only from text, stores only to
   data — the `addr_is_ram`-keyed wrappers become region-keyed).

