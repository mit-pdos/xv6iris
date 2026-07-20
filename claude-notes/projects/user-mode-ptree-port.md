# Project: porting user-mode execution onto the ptree page-table layer (UserPt → utlb_inv_pt)


**STATUS (2026-07-18e): stages 1–7 DONE and green; stage 8 done at width 8.**
Where things landed (the stage descriptions below remain the design rationale):

- *Stage 1*: the deep core (PtTreeAdue §5 front + KptTree §5–§6
  miss_core/cases/own) is privilege-generic (`p` parameter; cur_privilege /
  effectivePrivilege / `translationMode p = Sv39` are premises).  S wrappers
  instantiate `p := Supervisor` + `exec_translationMode_S_sv39` — signatures
  unchanged.  UptTree's absorption wrapper takes the mode dispatch as a
  CALLBACK premise (`Htmk` — satp lives inside the invariant).
- *Stage 2*: subsumed — no separate U front; `exec_translationMode_U_sv39`
  (UserTranslate §1, the only surviving part of that file) is the U
  instantiation.
- *Stages 3–5* live in **UserPtTree.v**: `uleaf_ok`/`uleaf_denied`/`u_acc`/
  `upt_acc_wf` (per-leaf ∀-variant classification; tramp/tf DENIED for every
  user access), the `uptd` record + `user_pt_inv` bundle
  (= `utlb_inv_pt ∗ udata_own ∗ ⌜udata_cov⌝ ∗ ⌜upt_acc_wf⌝`), the Ok
  absorption instance `utlb_inv_pt_translateAddr_u`, the pmp-fact borrow
  `utlb_inv_pt_pmp_facts`, and the THREE fault wrappers
  `utlb_inv_pt_translateAddr_u_{noncanon,unmapped,denied}` (Err, σ
  unchanged, invariant borrowed).  Their exec substrate: PtTree gained
  `ptree_maps_blocks_excl`, `ptree_own_blocked_mem`,
  `exec_translate_pt_denied`, `exec_translate_TLB_hit_denied_pt`,
  `tlb_ok_pt_lookup_blocked` (the unmapped-never-resident keystone);
  PtTreeAdue §5 gained the Err + non-canonical fronts.
- *Stage 6*: **UserFetchPt.v** — `user_pt_fetch_instr` (4-aligned fetch over
  the bundle, absorbed-outcome shape, no A/D-preset premises) +
  `udata_fetch_word`/`udata_fetch_mem_read`, and §4 `user_pt_fetch_fault`:
  the ONE fetch-fault composer over the flavor predicate
  `u_fetch_fault_flavor` (non-canonical / unmapped / fetch-denied) —
  `F_Error (E_Fetch_Page_Fault, pc)`, σ unchanged, bundle borrowed; the
  odd-pc align fault stays PT-free (`exec_fetch_align_fault`).  The
  2-ALIGNED (split) geometry is DONE on the success side: UserFetch §6
  holds the premise-shaped privilege-blind reductions
  (`exec_fetch_rvc_2` / `exec_fetch_base_2` /
  `exec_fetch_fault_2_{first,second}` -- the high halfword translates
  INDEPENDENTLY at pc+2, possibly another page), and
  `user_pt_fetch_instr_2` (UserFetchPt §5) composes them over the bundle
  with TWO sequential absorptions; its conclusion has the same if-isRVC
  shape as the 4-aligned composer (via UserBits' `subrange16_zext32` /
  `subrange16_concat16` bridges), with the sregs shape reported as the
  non-tlb lookup-transport property.  The 2-aligned FAULT composers are
  DONE too (UserFetchPt §6): `user_pt_fetch_fault_2_first` (flavor at pc,
  σ unchanged, bundle borrowed) and `user_pt_fetch_fault_2_second`
  (flavor at pc+2; ONE absorbed move; the conclusion is the inherent
  RVC-success / page-fault disjunction since the low halfword's bits are
  existential).  THE FETCH STORY IS NOW TOTAL over all pc alignments:
  odd -> align fault; 2-aligned -> rvc / base / fault composers;
  4-aligned -> user_pt_fetch_instr / user_pt_fetch_fault.  The fault
  flavor is now ACCESS-GENERIC (`u_fault_flavor acc` + the combined
  dispatch `utlb_inv_pt_translateAddr_u_fault`, UserPtTree §5b;
  `u_fetch_fault_flavor` is its fetch instance) -- the DATA-fault story
  for the memory arms is this one lemma at Load Data / Store Data / the
  AMO accs, with `exec_effectivePrivilege_mprv0` +
  `exec_is_shadow_stack_u_acc` as the acc-specific ingredients and the
  three translationException premises each a cbn-discharge.
- *Stage 7*: `user_inv` and the whole obligation chain (UserExec / UserTrap /
  UserStep / UserStepFull / UserCompute / UserArms) close over `pt : uptd`
  and `user_pt_inv pt`.  UserPt.v DELETED; UserTranslate slimmed to §1;
  UserFetch §6 and UserMem's upt Iris layer deleted.
- *Stage 8*: **UserMemPt.v** — width-8 LOAD/STORE end-to-end: U-mode PMP
  R/W grants, `exec_{checked_mem_read,mem_read_data}_8_U`,
  `exec_{checked_mem_write,mem_write_value}_8_U`, the ghost side
  (`udata_read_word_8`, `udata_own_upd` list-inductive window update +
  `udata_own_store_8`), and the composers `user_pt_load_data_8` /
  `user_pt_store_data_8` (translate absorbed + physical access + bundle
  re-established; a store just re-picks the existential byte map).
  The development is WIDTH-GENERIC: §5's Section closes over the access
  width `k` (premises `0 < k <= 8`, `(k | 4096)`, `uint (to_bits 64 k) = k`)
  plus the two width-TYPED plain-RAM bricks as parameters (`Hread_plain` /
  `Hwrite_plain` -- the only places the dependent `mword (8*k)` resists
  abstraction, because of the `cast_N` inside `sail_mem_read`); §6 derives
  the four RV64 width instances `user_pt_{load,store}_data_{8,4,2,1}` in a
  few lines each from the concrete bricks (read_2/4 RiscvFetchExec, read_8
  WpLoad, write_8 WpMmodeLeafBase, read_1/write_1/2/4 local clones).
  Supporting generics: `off_bound_div`/`pa_aligned_div`/
  `nth_byte_assemble_len`/`bytes_list_of_lookups` (UserBits.v),
  `u_walk_pa_window_div`, width-generic pma checks, `udata_read_word_g`/
  `udata_own_store_g`.  AMO is DONE at MemAmo4's kernel scope (width 4, AMOSWAP): UserMemPt §7
  adds the U-mode R∧W PMP grant (`exec_pmpCheck_user_grant_amo`) and the
  composer `user_pt_amo_data_4` -- ONE absorbed translation serving both
  sides, returning the old value plus a ∀-value PURE write fact at the
  moved state (the arm computes the stored value and absorbs the write
  with `udata_own_store_4`); MemAmo4's mem-level chain was already
  privilege-generic.  MemAmo4 §1 is now OP-GENERIC (the four chain lemmas +
  `exec_pmaCheck_ram_amo_4` + `exec_effectivePrivilege_amo_nm` take an
  `op : amoop`; the pma proof `destruct op`s the or-pattern the
  Data/ShadowStack arms compile to, effectivePrivilege uses
  `andb_false_r` instead of cbn so op stays abstract; NB WpAmo defines
  its OWN same-named AMOSWAP-specialized copies and does not import
  MemAmo4, so it is untouched).  `user_pt_amo_data_4` passes AMOSWAP;
  other ops are now a bare instantiation.
- **THE vmem_read_addr / vmem_write_addr LAYER (UserMemAccess.v)** -- the
  LOAD/STORE/LR/SC access layer just below execute_*, where instruction
  alignment and the LR/SC reservation live.  DONE and green:
  * the RESERVATION platform-effect axioms `exec_load_reservation` /
    `exec_cancel_reservation` (the opaque monadic reservation ops leave the
    modeled sregs/mem/mdev unchanged -- reservation state is not in mstate;
    extends the reservation platform-axiom family, assuming nothing about a
    particular reservation content since match_reservation stays opaque);
  * `exec_vmem_read_addr_aligned_8` (premise-shaped, res-generic: LOAD
    res=false AND LR res=true both route through it; the res
    load_reservation side effect discharged by the axiom) + the LOAD
    composer `user_pt_vmem_read_addr_load_8` over user_pt_load_data_8;
  * `exec_vmem_write_addr_aligned_store_8` (the write loop through the
    SC-assert bind0 and the store branch) + `user_pt_vmem_write_addr_store_8`;
  * the misaligned-fault exec bricks `exec_memory_exception` (a memory
    fault ExecutionResult is Trap(priv, sync_exc, pc)) and
    `exec_plat_misaligned_lrsc` (the platform delivers AccessFault for a
    misaligned reservation access).
  STILL OPEN (the memory tail, in rough order):
  1. DONE -- the MISALIGNED LR/SC fault reductions
     (`exec_vmem_read_addr_misaligned_lr` -> E_Load_Access_Fault,
     `exec_vmem_write_addr_misaligned_sc` -> E_SAMO_Access_Fault), width-
     generic, state unchanged.  The reduction recipe that finally worked:
     make plat_misaligned_exception / memory_exception Opaque so
     `cbn [Riscv.rv64d.not negb]` takes the fault branch without evaluating
     plat's computable body; the fault block is `bind (bind0 FAULT split)
     loop`, so PEEL outer-to-inner with execR_bind / execR_bind0 /
     execR_liftR (a `repeat (peel_b0 || peel_b || peel_l)`), rewrite
     exec_plat_misaligned_lrsc, cbn match to select the AccessFault arm,
     a SECOND peel round for the memory_exception bind, rewrite
     exec_memory_exception, then execR_early_ret (early_return short-
     circuits inl through the enclosing binds).  The earlier blocker was
     applying execR_liftR_seq before peeling the enclosing binds -- the
     fault block is nested, not at the execR head.  Former blocker text
     kept below for reference.  BLOCKER (historical): reducing
     the model's align guard `(if not is_aligned then FAULT else returnR tt)
     >> split >>= loop` inside catch_early_return.  Findings:
     `rewrite Hnal` DOES fire (guard becomes `if not false`), but the guard
     is a `bind0`-sequenced block `bind (bind0 FAULT_BLOCK split) loop`
     where FAULT_BLOCK = `liftR plat_misaligned_exception >>= (match ... =>
     memory_exception >>= early_return)`.  cbn evaluates
     plat_misaligned_exception's computable body (making it opaque via
     `Local Opaque plat_misaligned_exception memory_exception` fixes that),
     but the folded `execR_liftR_seq`/`execR_bind` lemmas then fail to
     re-match because the `Defs.bind`/`Defs.liftR`/`Defs.bind0` combinators
     have been unfolded by cbn -- and making THOSE opaque stops cbn from
     collapsing the bind0 chain to expose FAULT_BLOCK.  The fix is a small
     dedicated reduction lemma for `execR (bind0 FAULT_BLOCK rest) s` where
     FAULT_BLOCK early-returns inl (its execR = inl propagates through the
     enclosing binds regardless of rest), proven at the RAW execR level
     rather than via the folded combinator lemmas; then the two misaligned
     lemmas are `exec_catch_early_return` + that reduction.
  2. SC control-flow -- DONE.  `exec_vmem_write_addr_sc` (width-generic,
     premise-shaped): the aligned StoreConditional loop with the opaque
     `match_reservation (bits_of_physaddr paddr)` destructed -- true =>
     the write lands (Ok true), false => reservation lost, no write, access
     still granted (Ok false), both re-establishing the invariant.
     REMAINING for SC: discharge its physical premises (mem_write_ea /
     mem_write_value with the reserved write_kind, and phys_access_check)
     -- see the reservability note below.
  3. LR (LoadReserved res=true): the vmem_read_addr reduction is DONE
     (`exec_vmem_read_addr_aligned` is res-generic, handles the
     load_reservation side effect via the axiom).  REMAINING: the physical
     read chain at User for the reserved read_kind (MemAmo4's
     `run_read_ram_resacq_4_pin` is the width-4 reserved read primitive to
     clone) -- see the reservability note.
     RESERVABILITY NOTE (LR/SC physical discharge): `pma_allows_all`
     guarantees executable/readable/writable/atomic_support=AMOSwap but
     NOT `PMA_reservability` -- and the LR/SC pma arms check
     `reservability <> RsrvNone`.  So on RAM, LR/SC either RETIRE (if the
     PMA reservability is set) or take an ACCESS FAULT (if RsrvNone) --
     BOTH safe for totality.  DECISION MADE (per the user): route (b), the
     retire-or-fault DISJUNCTION, no bundle change.  DONE END-TO-END for
     BOTH LR and SC at the vmem level (UserMemAccess §5a-k, all green) --
     §5a-d below, plus §5e the LR mem_read wrap, §5f the aligned vmem
     FAULT path (translate Ok but mem_read Err -> memory_exception Trap,
     width-generic), §5g `exec_vmem_read_addr_lr_disj` (the
     instruction-facing LR disjunction: retire [exists value] or delegated
     E_Load_Access_Fault Trap, a case-split combining the res-generic
     retire lemma and §5f); §5h `exec_checked_mem_write_sc_4/_8` (the SC
     write mirror of §5d -- conditional write LANDS when reservable else
     E_SAMO fault; adds `exec_write_ram_cond_8`, whose value-projection
     needs an extra `cbn [Mem_write_request_value]`+`iMon_bind` vs width-4),
     §5i the SC mem_write_value wrap, §5j `exec_vmem_write_addr_sc_fault`
     (reservability=None -> BOTH match_reservation branches fault to
     E_SAMO Trap; complements the granted `exec_vmem_write_addr_sc`), §5k
     `exec_vmem_write_addr_sc_disj` (the instruction-facing SC disjunction:
     retire [Ok of match_reservation, write lands iff reservation valid] or
     E_SAMO Trap).  All width-generic where the layer allows; the
     per-width bricks are widths 4 and 8 (LR.W/LR.D, SC.W/SC.D).  The IRIS
     BUNDLE COMPOSERS ARE ALSO DONE (§6a/§6b, widths 4/8, all green):
     `user_pt_vmem_read_addr_lr_4/_8` and `user_pt_vmem_write_addr_sc_4/_8`
     thread the reserved translate through the utlb_inv_pt_translateAddr_u
     absorption + udata_own and expose the instruction-facing disjunction,
     re-establishing utlb_inv_pt + udata_own; same shape as §2's aligned
     LOAD/STORE composers.  SC's composer cases on the opaque
     match_reservation for the CONDITIONAL ghost write (udata_own_store_g
     fires only on the mr=true retire sub-case; mr=false retires without
     writing, RsrvNone faults).  So LR/SC is COMPLETE from atom to
     invariant.  (UserMemAccess now Require Imports SmodeCore / UserBits /
     WpMmodeLeafBase for ram_fetch_pmp / pa_aligned_div / within_htif_
     writable_false, which UserMemPt does not re-export.)
     §5 PHYSICAL PIECES DONE (UserMemAccess §5a-d, all green):
       - §5a `exec_read_ram_resv_4/_8`: the reserved-RAM read atoms.
         read_ram is AK-agnostic for RAM, so these clone the plain read
         atoms verbatim; the reserved read_kind only swaps AV_plain ->
         AV_exclusive.  (The earlier "No primitive equality" blocker was
         the UNUSED AK_arch strong-acquire variant, not the plain reserved
         kind that LR/SC-with-default-flags actually use.)
       - §5b `exec_pmaCheck_ram_lr_g` / `_sc_g`: the reserved pma arm
         `andb R/W (reservability<>RsrvNone)` reduced to a single `if` on
         reservability -- <>None allows (None), =None yields the delegated
         E_Load/E_SAMO access fault.  THE branch point of the disjunction.
       - §5c `exec_pmpCheck_user_grant_lr` / `_sc`: pmpCheckRWX treats
         LoadReserved/StoreConditional exactly as Load/Store, so verbatim
         load/store grants with the access swapped.  (Only compiles in the
         full import context -- a minimal probe misses the reduction
         setup that makes cbn resolve the foreach guard; add such lemmas
         directly to the real file, not a probe.)
       - §5d `exec_checked_mem_read_lr_4/_8`: the LR retire-or-fault
         disjunction at the checked_mem_read layer -- one `if` on the
         unpinned reservability gives Ok(bytes) [retire] or
         Err E_Load_Access_Fault [fault].  Composes §5a+§5b+§5c.
     (§5e-k + §6a/§6b above completed the entire LR/SC stack, atom to
     invariant; NOTHING remains for LR/SC.)
  4. AMO EXECUTE reduction (execute_AMO): its own pre-translation alignment
     check (misaligned -> E_SAMO_Access_Fault via GlobalMisalignedExceptions_
     amo = AccessFault), then translate + mem_write_ea + mem_read +
     mem_write_value + the result computation (per-op, AMOCAS special-cased)
     + wX; the mem-level facts are `user_pt_amo_data_4`.  This is
     execute-level (borders the assembly).
  5. DONE -- the vmem LOAD/STORE composers are WIDTH-GENERIC:
     exec_vmem_read_addr_aligned / exec_vmem_write_addr_aligned_store and
     user_pt_vmem_{read_addr_load,write_addr_store} take the width k (+ the
     two width-typed plain-RAM bricks, like UserMemPt SS5), with the RV64
     width instances user_pt_vmem_{read_addr_load,write_addr_store}_{8,4,2,1}
     the trivial derivations.  The STORE composer threads the model's own
     subrange write-value (udata_own absorbs it, contents existential), so
     no per-width subrange-identity is needed.
  6. plain LOAD/STORE MISALIGNED split (n>1) -- DONE at the exec level
     (UserMemAccess §4a-c, all green).  plat_misaligned_access.load_store
     = None, so a misaligned plain load/store does NOT fault -- the model
     splits it into n = width/2^ctz aligned sub-accesses, each translated
     independently, via an `untilMT` loop with a CONSTANT measure.  REQUIRED
     for totality over arbitrary user code (whether xv6 itself misaligns is
     irrelevant -- the classification must handle every decodable access).
     Pieces:
       - §4a the generic untilMT' loop reductions: `execR_untilMT'_last`
         (cond true -> return), `_step` (cond false -> recurse at limit-1;
         both via destructing the `Acc (Zwf 0)` witness -- axiom-free, no
         proof-irrelevance), `_chain` (compose N iterations by induction).
         The CONSTANT measure means untilMT' starts at limit n and just
         decrements once per chunk; termination is driven by the `finished`
         flag reached exactly at the last chunk.
       - §4b `exec_vmem_read_addr_misaligned_split` (general N): the loop
         state `split_var k = (data_seq k, k=?N, offset)` with `data_seq`
         the running byte-assembly; `split_body_step` reduces ONE iteration
         (translate+read+update_subrange) generically in k; `split_loop`
         composes N via `_chain`; the top lemma glues the align-guard
         (`exec_plat_misaligned_loadstore_none`: plat delivers None for a
         plain load/store, so the guard returns tt -- no fault) and the
         split.  Premise-shaped over per-chunk translate+read facts.  res=
         false only (the split never fires for LR, which access-faults on
         misalign).
       - §4c `exec_vmem_write_addr_misaligned_split` (general N): same shape
         with loop var `(finished, offset, write_success)`; `ws_seq`
         accumulates `andb` of the per-chunk store outcomes; each chunk
         threads the post-translate state `stt k` then mem_write_ea +
         mem_write_value; the write-value is the model's own subrange slice.
     Reduction gotchas kept: the `if false ... else returnR tt` (res
     substituted) is convertible to `returnR tt`, so write it directly in
     the body definition (the dependent-if hits a notation-scope parse
     error in this file's import context); the CONSTANT-measure `untilMT`
     needs `set`/`clearbody`/`rewrite` to reduce `measure (v 0)` to n
     without breaking the Acc-dependent type; the initial loop var
     `(zeros', false, 0)` must be `replace`d with `split_var 0` (the
     `Nat.eqb 0 N` flag is not definitionally false for abstract N).
     BUNDLE COMPOSERS DONE (UserMemAccess §7/§8, all green): the N-fold
     absorption is `split_load_fold` (§7) / `split_store_fold` (§8) -- an
     induction on the chunk count that loops user_pt_load_data_g /
     user_pt_store_data_g at width [bytes] and the chunk address, threading
     the invariant + udata + a `config_ok` predicate across all N
     absorptions (config preserved per absorption via config_ok_pres;
     STORE additionally threads per-chunk ghost writes -- two-level state
     sttS/sstS = post-translate/post-write).  The per-chunk state is a
     deterministic fixpoint over exec ([sst]/[sstS]); [spa] the closed-form
     paddr; the LOAD value [sval] is the exec output, the STORE value the
     model's subrange slice of the full store data (matched to §4c's
     internal wv via an Hwvdef hypothesis).  The top composers
     user_pt_vmem_read_addr_misaligned_split_load /
     user_pt_vmem_write_addr_misaligned_split_store feed the collected
     per-chunk facts to §4b/§4c, reducing the misaligned plain LOAD/STORE
     to Ok over utlb_inv_pt + udata_own.  Within-page coverage: the caller
     supplies um !! svpn_of (chunk k) = Some w for every chunk (§7/§8 fix
     one leaf w; a straddling access that maps two pages would take the
     per-chunk-vpn generalization -- not needed for the within-page case).
     This is §6's SINGLE-absorption pattern generalized to N.  THE USER
     MEMORY LAYER IS NOW WIRED END-TO-END TO THE USER INVARIANT (aligned
     LOAD/STORE §2, LR/SC §5-§6, and the misaligned split §4/§7/§8).
- NEXT after that: wire the fault wrappers into `fetch_fault_obligation` /
  the memory-trap arms, then the UserClassify assembly (see the HANDOFF
  CHECKPOINT's item A), then the concrete-witness stage (a real process
  table satisfying `upt_tree_spec`/`upt_acc_wf` — meets KvmSpec.v).
- Post-deletion sweep now unblocked: UserPt was the last consumer of
  several KptPt P_kpt iris-side instances and SmodePte's `tlb_consistent`
  — verify and delete.

GOAL: replace UserPt.v's `upt` record (`u_root`/`u_slots`/`u_map`/`u_data` +
`upt_wf` + `upt_inv`) with the ptree layer, so arbitrary U-mode execution runs
over **`utlb_inv_pt uroot tfp um` (UptTree.v) ∗ a separate data-page resource**,
with the Svadu A/D write-back ABSORBED by the invariant (the current U-mode
chain assumes A/D preset in every user leaf — "update_PTE_Bits = None always";
that assumption is DROPPED by this port, exactly as it was on the kernel side).
The S-mode side is fully done and is the template throughout: the generic
absorption core (KptTree.v §5-§6: `ptree_translate_miss_core` /
`ptree_translateAddr_cases` / `ptree_translateAddr_own`), its kernel/user
S-mode instances, the pt2 switch window (TransPt.v), and the userret proof
(UserretAllPt.v).  This port also UNBLOCKS the deferred U-mode memory arms
(LOAD/STORE/AMO) and the fetch-fault payload wiring, which were parked
"waiting for the Svadu/ADUE page-table rework" — the ptree layer IS that
rework.

### Target architecture

- The user bundle becomes `user_pt_inv uroot tfp um data :=
  utlb_inv_pt uroot tfp um ∗ upt_data_own data ∗ ⌜upt_data_cov um data⌝`
  (names indicative).  KEEP the old `upt_data_own : gset Arch.pa → iProp`
  shape (flat pa-set, existential byte contents) — owning "one page per
  mapped vpn" instead is an ALIASING TRAP (two vpns may map one ppn; a gset
  dedups).  The coverage fact says every mapped leaf's output page
  (`PPN_of_PTE w` ++ offset) lands in `data`; it replaces `upt_data_cov` on
  the old record.  PT-slot ownership, satp/tlb cells, `tlb_ok_pt`, spec and
  `pmp_config uroot` all live inside `utlb_inv_pt` already — nothing else
  rides outside.
- Translation outcomes at User, per access at a va (the ONE caller-facing
  trichotomy, mirroring the old UserTranslate GOAL comment):
  - **Ok** — `um !! svpn = Some w` and w's flag byte passes the check at
    User for this access: pa = leaf page + offset, and the state moves in
    one of the ABSORBED ways (unchanged hit / TLB fill / Svadu A/D
    write-back into the owned tree) — the invariant re-establishes, callers
    never see hit-vs-miss or the write-back.
  - **Err (page fault, σ unchanged)** — non-canonical va, unmapped vpn
    (`ptree_blocks`), flag byte denies the access, or the vpn is
    `tramp_vpn`/`tf_vpn` (mapped U=0 ⇒ denied at User).
- uservec's return page-table switch reuses TransPt's pt2 window with the
  roles swapped (`Sp := upt_tree_spec uroot tfp um`,
  `Sc := kpt_tree_spec kroot`); `wp_userret_pt`'s post already hands back
  `pt_frame (kpt_tree_spec kroot)` for exactly this.

### Stage plan (each stage compiles + commits green on its own)

1. **Privilege-generalize the DEEP core** (KptTree.v §5-§6).  Add a Section
   `Context (p : Privilege)` to `KptTranslate`/`KptTranslateAddr`/
   `PtTranslateOwn` and replace the literal `Supervisor` in
   `ptree_translate_miss_core`, `ptree_translateAddr_cases`,
   `ptree_translateAddr_own` (the `pte_check_ok acc Supervisor …` premises,
   the `translate … Supervisor …` calls, the `effectivePrivilege` /
   `is_shadow_stack` facts → at `p`).  The underlying CommonWalk core and
   PtTreeAdue's hit/miss/write-back lemmas are ALREADY privilege-generic;
   this is mechanical.  Keep every existing kernel/S-mode wrapper unchanged
   by instantiating `p := Supervisor` — zero downstream churn.  Do NOT try
   to abstract `exec_translateAddr_pt_front` over privilege (next stage).
2. **The User translateAddr FRONT.**  The S front
   (`exec_translateAddr_pt_front`, PtTreeAdue.v) reads
   `cur_privilege = Supervisor` + `mstatus.SXL`; the U front has genuinely
   different register reads (cur_priv = User, effectivePrivilege at MPRV=0,
   the satp-mode dispatch of UserTranslate §1).  CLONE a small
   `exec_translateAddr_pt_front_u` from UserTranslate §1's pure bricks
   (`exec_get_satp_39` / `exec_satp_mode_width_39` / `exec_assert_vmem431` /
   `exec_translationMode_U_sv39` — all live, reuse verbatim) composing any
   ∀-mxr/do_sum `translate` outcome, mirroring the S front's statement.
3. **Per-leaf flag dispatch.**  `upt_map_wf` currently records only the
   STRUCTURAL classification (valid/leaf/no-napot/pbmt0 variants).  Add the
   permission story: a pure dichotomy lemma family "for a structurally-wf
   leaf w and each access type at User (mxr abstract, ∀-quantified as
   usual): `pte_check_ok acc User mxr do_sum (pte_set_ad w a d)` for all
   a/d, OR check_PTE_permission returns denied" — by case analysis on the
   flag byte (`check_PTE_permission` ignores A/D entirely, so the dichotomy
   is a fact about w alone; push through variants with the PtAdBits laws,
   mirroring `kpt_variant_check_{fetch,load,store}`).  Options: strengthen
   `upt_map_wf` to classify the flag byte into a closed set (simplest,
   matches how KptPt §12 dispatches), or prove the dichotomy for an
   arbitrary flag byte (more general; the old UserPt "worklist item 2" shape).
   Also needed: `pte_check_ok acc User … (pte_set_ad pte_tramp a d)` and
   `(pte_tf tfp)` are DENIED (U=0) — concrete vm_compute facts.
4. **U-mode Ok absorption instances** (extend UptTree.v or a new file):
   `utlb_inv_pt_translateAddr_u` (+ `_fetch/_load/_store` instances) =
   stage-1's generalized `ptree_translateAddr_own` at `p := User` + stage-2's
   front + stage-3's check facts, opened/resealed against `utlb_inv_pt`
   exactly like the existing S-mode instances (`_tramp_fetch`/`_tf_load`/
   `_tf_store` in UptTree.v are the worked examples — same peel of satp/tlb/
   pmp facts, same spec-preservation via `upt_tree_spec_set_leaf`).  The
   output-pa premise (`Hout`) is the leaf-page form: derive
   `pa = zero_extend' 64 (concat_vec (PPN-of-w) offset)` and record the
   data-coverage corollary (pa ∈ data) from the bundle's coverage fact.
5. **The FAULT head** (new exec layer + Iris wrapper).  Pieces:
   (a) blocked-vpn walk fault: `exec_translate_pt_blocks` (PtTree.v, done at
   `translate` level) + the U front's Err propagation (UserTranslate's
   `exec_translateAddr_fetch_u_noncanonical` / `exec_translateAddr_fetch_u_fault`
   heads are live and reusable);
   (b) denied-walk fault: clone the blocks lemma with CommonWalk
   UserWalkFault's no-permission piece (walk reads the leaf, check fails →
   `PTW_No_Permission`, NO fill, NO write-back);
   (c) HIT-denied fault: a resident `u_walk_entry` A/D-VARIANT of a mapped
   vpn whose check fails at User (restate UserTranslate's
   `exec_translate_TLB_hit_denied_u` on uwe-shaped entries; the entry's
   leaf is `pte_set_ad w a d` — absorb with `pte_set_ad_absorb`).  VERIFY
   THE MODEL ORDER first: on a hit, `check_PTE_permission` runs BEFORE
   `update_PTE_Bits`, so a denied hit never write-backs and the fault
   leaves σ unchanged — if the order were reversed the statement changes;
   (d) the soundness keystone, from `tlb_ok_pt`: an UNMAPPED vpn is never
   TLB-resident (resident ⇒ some mapped vpn's entry; same-slot foreign
   entries are rejected by `uwe_match_other`) — spell this as its own
   lemma; it is what makes the fault case analysis total.
   Then ONE Iris wrapper `utlb_inv_pt_translateAddr_u_fault`: Err, σ
   unchanged, invariant handed back whole.
6. **Rebuild the fetch interface.**  `upt_fetch_instr` (UserFetch §6) and
   its word/mem-read layers move onto the new bundle: bytes come from
   `upt_data_own` at the leaf-page pa; the four fetch-geometry compositors
   in PtFetchGen.v (`exec_fetch_{F_Base_4,F_Base_2,RVC_4,RVC_2}_S_gen_pa`)
   take the translate outcome AS A PREMISE, so they are privilege-blind —
   reuse them verbatim at U (despite the `_S_` in the name), feeding the
   PMP X-grant facts from UserMem's U-mode grant.  A SPLIT fetch translates
   each half independently — each half may independently fill or
   write-back; thread `pt_regs_preserved`-style transport as the S engines
   do (SmodeCorePt is the worked example).
7. **Flip the User chain, file by file** (mechanical once 1-6 are in):
   UserExec (`user_inv` bundles the new user_pt_inv), UserTranslate (the
   trichotomy wrappers), UserFetch, UserMem, then the PT-blind threaders
   UserStep / UserStepFull / UserArms / UserCompute (they touch the PT only
   through the fetch/translate interfaces and the bundle name), UserTrap
   (PT-free, unchanged).  UserCsr / UserExecFacts / UserBits / DecodeSetU
   are PT-free — untouched.
8. **Then build the deferred pieces on top**: the U-mode data-memory arms
   (LOAD/STORE/AMO/LR/SC against `upt_data_own`, width-generic — a user
   STORE re-establishes the bundle trivially since contents are
   existential), and the fetch-fault flavor payload wiring.

### Tricky cases / gotchas for this port

- **The A/D-preset assumption is gone, so `upt_tlb_ok`-style EXACT-entry
  reasoning dies with it**: resident entries are now A/D VARIANTS
  (`tlb_ok_pt` / `tlb_cache_of`); anything that pattern-matched a concrete
  `um_tlb_ent` must switch to variant reasoning (`pte_set_ad_absorb`
  collapses variant-of-variant; `uwe_match_self` holds for any global bit).
- **A U-mode access can dirty the page table**: the write-back arm writes
  the provenance L0 slot through `ptree_own_path_upd` + `word_pointsto_write`
  and refreshes the TLB slot — memory changes MID-FETCH on a split fetch,
  and a "read-only" user load can change σ.  Every U-mode step lemma must
  carry the absorbed-outcome shape (`σ' = σ ∨ tlb register_set ∨ the
  MState-with-write-bytes form), not σ'=σ.
- **mxr/do_sum**: the model computes them as concrete mstatus expressions
  right before `translate` — keep the ∀-mxr/do_sum quantification in every
  check hypothesis and `match goal` to capture the concrete forms (same
  gotcha as the S-mode data leaves).  `user_mstatus_ok` pins MXR=0/MPRV=0;
  SUM is irrelevant at effective-User.
- **tramp/tf entries CAN be TLB-resident when U-mode runs**: the S-phase
  uservec/userret fetches cache them.  A user access to those vas takes the
  HIT-denied path (stage 5c), not the walk-denied path — this is the
  realistic hit-denied case, don't skip it.
- **asid is 0 everywhere** (`mword_of_int 0`); user vas below TRAPFRAME are
  canonical-low, tramp/tf vas canonical-high — both pass the canonicality
  check; only genuinely non-canonical vas take the early fault.
- **Do not confuse `wp_instr_u_pt` (TrampStepPt.v)** — that is the S-MODE
  step engine over the user TABLE (the userret/uservec trampoline phase),
  not a U-mode engine.  The U-mode engine is the UserStep/UserStepFull
  obligation machinery, which is PT-agnostic above the fetch interface.
- `pmp_config`'s root index is phantom (`pmp_config_reindex` converts by
  `iExact`); the U bundle keeps `pmp_config uroot`.
- PT slots and data pages are separately owned under one gen_heap —
  separation gives PT/data disjointness for free, and the write-back's
  slot write composes with a user store's data write without any aliasing
  side condition.

### What to DELETE once superseded (the old user-mode PT machinery)

Delete only at the END of stage 7, after the flip is green — until then the
old and new layers coexist:

- **UserPt.v — the whole file**: the `upt` record + `umap_ent`/`umap_ent_wf`
  + `upt_wf` (`upt_map_spec`/`upt_unmapped_spec`/`upt_data_cov`),
  `um_tlb_ent`, `upt_tlb_ok`(+`_empty`/`_fill`), `upt_satp_ok`,
  `upt_slots_own`, `upt_inv`(+intro/open), and the slot-read layer
  (`upt_slot_read_pte`, `upt_read_walk_ptes`, `upt_unmapped_walk_fault`,
  `upt_denied_walk_fault`) — replaced by `ptree_own`/`ptree_maps`/
  `ptree_blocks` + `ptree_own_path_mem` + `pt_read_pte_slot` + `tlb_ok_pt`
  + `utlb_inv_pt`.  RELOCATE first: `upt_data_own` (+ its access lemmas)
  and the old `upte_check_ok`/`upte_check_denied` dichotomy content (dies
  as stated, but its flag-byte case analysis is the seed for stage 3).
- **UserTranslate.v — the upt-keyed parts**: the Iris wrappers
  (`upt_translateAddr_fetch_{unmapped,denied,denied_full,needs_update_full}`)
  and the `umap_ent`-keyed walk/hit lemmas
  (`exec_translateAddr_fetch_u_walk`/`_walk_nomatch`/`_hit`/`_hit_denied`,
  `exec_translate_hit_{ok,denied}_u`, `um_tlb_ent_match_self`).  KEEP the
  pure §1 mode-dispatch bricks and the Err-propagation heads
  (`exec_translateAddr_fetch_u_noncanonical`/`_u_fault`) — stages 2 and 5
  reuse them.
- **There is NO needs-update fault arm to port**: the Svade needs-update
  fault chain was already deleted tree-wide as dead+false (ADUE is pinned
  1); under the ptree absorption an A/D-insufficient access takes the
  write-back path.  If any residual needs-update spelling surfaces, delete
  it rather than porting it.
- **UserMem.v / UserFetch.v**: the `upt_*` fetch layers (`upt_fetch_word` /
  `upt_fetch_mem_read` in UserMem.v, `upt_fetch_instr` in UserFetch.v) are
  REBUILT (stage 6); the pure fault layers and the U-mode PMP grant stay.
- After UserPt.v is gone, also sweep the now-dead residue flagged in the
  deletion-status bullet: KptPt's P_kpt/_ad IRIS-side instances and
  SmodePte's `tlb_consistent` — but KEEP KptPt §12's `_ad` CLASSIFICATION
  lemmas (they are the live A/D-variance bridge KptTree consumes), and note
  UserPt is currently the last consumer of several of them.
- WpIntrCore's commented-out U-side region (§5b/§6 porting stock) can be
  retired once the flipped chain covers its intent.

