(* WpSmodePtLeaves.v -- the S-mode LEAF layer over the generalized
   page-table-tree invariant [tlb_inv_pt] (KptTree.v / SmodeCorePt.v).

   The migration pattern for every existing S-mode leaf (all three
   kinds), demonstrated end to end:

   - NON-MEMORY (gpr-write) leaves: the generic engines
     [wp_gpr_write_s_config_pt]/[_base_pt] are clones of
     WpSmodeLeafBase's over [wp_instr_s_config_tlbinv_pt] -- SIMPLER
     than the originals (the invariant is threaded whole; there is no
     satp/tlb/pte/pmp reseal plumbing).  Per-instruction leaves
     ([wp_addi_s_pt], [wp_cli_s_pt]) are verbatim wrappers.

   - LOAD leaves ([wp_cld_s_pt]): the data-side translation goes
     through the absorption theorem [tlb_inv_pt_translateAddr_load]
     (a [==∗] inside the engine's σ-callback).  Compared with
     [wp_cld_s], ALL the legacy geometry premises (canonicality, vpn
     definition, identity, megapage masks) disappear -- the absorption
     theorem derives identity translation from [addr_is_ram] alone,
     which comes from the owned data bytes.  The instruction towers
     are re-proved STATE-GENERIC ([ExecLoadGSwalkPt]): the translate
     output state is an abstract [s'] (the write-back may have changed
     memory), with the data bytes given AT [s'] (the Iris layer reads
     them off [gen_heap_interp s']).

   - STORE leaves ([wp_csd_s_pt]): same shape; the store's memory
     write runs at the translate output state.

   Migrating any remaining leaf is the same mechanical recipe:
   swap the engine, delete the geometry premises, run the data
   translate through the absorption theorem, and use the
   state-generic tower.                                                  *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpGpr RegFile MinstretInv InstrBytes WpMmodeLeafBase WpMmodeSwpBase.
Require Import SmodeCore WpSmodeGpr.
Require Import UserBits.
Require Import SmodeCorePt SRegime WpSmodePtFetch.
Require Import HartLift HartSpan HartSwp HartSMem WpSmodePtEngine.
Require Import KptShare KptGoodb.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import MemAccessGen.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

(* Opts back out of [RiscvPtsto]'s [word_pointsto] seal: the leaf walk takes page-table words apart byte by byte.
   Local, so nothing above this file inherits the transparency. *)
Local Typeclasses Transparent word_pointsto.

Section WpSmodePtGprEngine.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* The generic RVC (2-byte) gpr-write engine over [tlb_inv_pt].         *)
  (* ------------------------------------------------------------------- *)
  (* THE FORCED PREMISE CHANGE (the sweep's standing one): the [exec] fact
     is unusable per node, so the instruction arrives as a [swp] OBLIGATION
     -- verbatim what [WpMmodeSwpBase]'s node shapes conclude.  Everything
     else, including the [sr_inv R] surface, is unchanged. *)
  Lemma wp_gpr_write_s_config_regime (R : s_regime)
      (pc : mword 64) (rd : mword 5) (base : instruction) (wval : mword 64)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (gen_cert -∗ gpr_file m -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   gpr_file (<[Regidx rd := regval_into_reg wval]> m))) -∗
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true base -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0)
      "Hex #Hhw #Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc Hfile Hinstr
       Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iApply (wp_instr_s_config_folded R pc true base mstatus0 mie_v mdv0 menvcfg0
              mie_v menvcfg0
              (fun npc ms1 mdv1 => (⌜npc = add_vec_int pc 2⌝ ∗
                 ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗
                 gpr_file (<[Regidx rd := regval_into_reg wval]> m))%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc Hinstr
                    [Hex Hfile] [Hcont]").
    - (* the instruction: the SLOT is framed across the walk, folded *)
      iIntros "Hpriv Hms Hmie Hmdl Hmenv Hslot Hclk HPC HnPC Hresv".
      iDestruct ("Hex" with "Hcert Hfile") as "Hexx".
      iApply (swp_mono with "[Hpriv Hms Hmie Hmdl Hmenv Hslot
                              Hclk HPC HnPC Hresv] [Hexx]");
        [| iExact "Hexx" ].
      iIntros (e) "(-> & Hfile)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hslot Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists mstatus0, mdv0, (add_vec_int pc 2).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iExact "Hfile".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc (-> & -> & -> & Hfile)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc Hfile").
  Qed.

End WpSmodePtGprEngine.

(* ===================================================================== *)
(* Exemplar NON-MEMORY leaves (verbatim clones of WpSmodeItype's, with    *)
(* [tlb_inv_pt] threaded).                                                *)
(* ===================================================================== *)
Section WpSmodePtItype.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.





End WpSmodePtItype.

(* ===================================================================== *)
(* STATE-GENERIC load towers: the [RWSwalk]/[RWgSwalk]/[ExecLoadGSwalk]   *)
(* clones with the translate output state ABSTRACT (the pt data           *)
(* translation may have written A/D back, so [s'] is not a tlb-only       *)
(* variant and the data bytes are given AT [s'']).                        *)
(* ===================================================================== *)

Section RWSwalkPt.
Variable a : mword 64.
Variable v : mword (8*8).
Variable region : PMA_Region.
Variable s s' : mstate.
Variable pa : mword 64.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Variable md : SATPMode.
Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
Hypothesis Htr : exec (translateAddr (Virtaddr a) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_addr_8_S_walk_pt :
  exec (vmem_read_addr (Virtaddr a) 8 (Load Data) false false false) s
    = Some (Ok v, s').
Proof.
  assert (Heff : exec (effectivePrivilege (Load Data) (register_lookup mstatus s.(sregs))
                         (register_lookup cur_privilege s.(sregs))) s = Some (Supervisor, s)).
  { rewrite Hcps. apply exec_effectivePrivilege_load_S. exact Hmprvs. }
  apply (exec_vmem_read_addr_aligned_load 8 a pa v Supervisor md s s'
           ltac:(right; right; right; reflexivity) Halign Heff Htm).
  apply (exec_translate_and_read_value_g 8 a pa PBMT_PMA v s s' s' Htr).
  exact (exec_mem_read_load_S PBMT_PMA pa region v (register_lookup mstatus s'.(sregs)) s'
           HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes eq_refl Hmprv' Hcp').
Qed.
End RWSwalkPt.

Section RWgSwalkPt.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable v : mword (8*8).
Variable region : PMA_Region.
Variable s s' : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Variable pa : mword 64.
Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s
                  = Some (Virtaddr ea, s).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Variable md : SATPMode.
Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_8_gpr_S_walk_pt :
  exec (vmem_read (Regidx rs1) offset 8 (Load Data) false false false) s = Some (Ok v, s').
Proof.
  unfold vmem_read. rewrite exec_catch_early_return.
  assert (Ha8ea : a8 = ea) by (unfold a8; rewrite subrange_id; apply sign_extend'_id).
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 8 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ Htea).
    rewrite Ha8ea. apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_read_addr_8_S_walk_pt a8 v region s s' pa Halign Hcp' Hmprv'
             md Hcps Hmprvs Htm Htr HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
  reflexivity.
Qed.
End RWgSwalkPt.

Section ExecLoadGSwalkPt.
Variable rs1 rd : mword 5.
Variable imm : mword 12.
Variable v : mword (8*8).
Variable region : PMA_Region.
Variable s s' : mstate.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Variable pa : mword 64.
Hypothesis Hrd : uint rd <> 0.
Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s
                  = Some (Virtaddr ea, s).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Variable md : SATPMode.
Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_execute_LOAD_8_gpr_S_walk_pt :
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s
    = Some (RETIRE_SUCCESS,
            set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false v))).
Proof.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 8).
  unfold execute_LOAD.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_read_8_gpr_S_walk_pt rs1 offset v region s s' pa Htea Halign
       md Hcps Hmprvs Htm Htr Hcp' Hmprv' HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
  cbn match.
  assert (Hw : exec (wX_bits (Regidx rd) (extend_value false v)) s'
               = Some (tt, set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value false v)))).
  { rewrite (exec_wX_bits_gpr rd (extend_value false v) s').
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnM.
Qed.
End ExecLoadGSwalkPt.

(* ===================================================================== *)
(* Exemplar LOAD leaf over [tlb_inv_pt]: c.ld rd, imm(rs1) from a RAM     *)
(* address.  Compared with [wp_cld_s]: the seven geometry premises are    *)
(* GONE (identity translation falls out of [addr_is_ram] inside the      *)
(* absorption theorem), and there is NO hit/walk case split -- the       *)
(* translate output state is abstract and one state-generic tower       *)
(* serves every arm (hit, fill, and the Svadu A/D write-back).           *)
(* ===================================================================== *)
Section WpSmodePtLoad.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ==================================================================== *)
  (* THE TIER-INDEXED FORM (sp-migration phase D, design §4).  [kt'] is the *)
  (* DATUM's tier and [kt] the accessing hart's; [KtierLe kt' kt] is the    *)
  (* whole access condition, and [sr_ktier_wit R kt] (persistent, [emp] at  *)
  (* KT0) is what the hart must show for it.  TIER-PRESERVING: the datum    *)
  (* comes back at [kt'], so a KT0 fact stays KT0 through any number of     *)
  (* accesses and a re-deposit into a KT0-stated invariant needs no         *)
  (* strengthening.  [wp_cld_s_r] below is the kt := kt' := KT0 corollary   *)
  (* -- character-identical to its pre-phase-D statement, so no consumer    *)
  (* sees the generalization.                                              *)
  (* ==================================================================== *)
  Lemma wp_cld_s_r_t (R : s_regime) (kt kt' : ktier) `{!KtierLe kt' kt}
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (v : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    sr_ktier_wit R kt -∗
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    pa ↦₈[kt']{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈[kt']{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea a8 pa Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    (* the three [let]s collapse: the engine spells the address as the term,
       and a local definition is not syntactically it *)
    unfold pa, a8, ea in *. clear pa a8 ea.
    iIntros "#Hwit #Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr
              (Virtaddr (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))) 8
              = true) by exact Hpalign4.
    pose proof (off_bound_div
                  (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 8
                  ltac:(lia) ltac:(exists 512; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA &
        %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0.
    (* THE WORD'S OWN CLAIM: byte 0 carries the ppn, the canonicality, the
       RAM-ness of the translated base and the tier pin -- everything the
       engine needs BEFORE it runs, and none of it needs the heap. *)
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes")
      as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc (KTR := kt') with "Hb0")
      as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0
             (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    assert (Hev : extend_value (n := 8 * 8) false v = v)
      by (unfold extend_value; apply sign_extend'_id).
    iApply (wp_instr_s_config_folded R pc true
              (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 => (⌜npc = add_vec_int pc 2⌝ ∗
                 ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗
                 gpr_file (<[Regidx rd := regval_into_reg v]> m) ∗
                 (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                   ↦₈[kt']{ dqm } v)%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr
                    [Hfile Hbytes] [Hcont]").
    - iIntros "Hpriv Hms Hmie Hmdl Hmenv Hslot Hclk HPC HnPC Hresv".
      (* THE SLOT STAYS FOLDED.  [sda_slot_acc_R] is the one place the two
         translation arms are told apart: it hands out an ABSTRACT write set
         with its frames, the residue, and the arm's translation SIDE
         CONDITION already discharged -- the one thing a regime-generic leaf
         cannot produce for itself ([sr_swp_side_ok] demands [tlb ∈ Drw], and
         the Bare arm's write set is empty). *)
      iDestruct (sda_slot_acc_R R dq mstatus0 menvcfg0 pmar0
                   Hmenvval0 HSXL HMPRV (pma_all_ram Hpma_all)
                   with "Hms Hpriv Hmenv Hpma Hhtif Hmisa Hslot")
        as (SD satp0 pcfg paddr tv')
           "(%Hdisj & %Hsub & %Hsok & %Hpok & %Hside & Hrw & Hro & HRes &
             Hclose)".
      destruct Hpok as (HA & Hord & HX & HW & HR & Hcov).
      iDestruct "Hresv" as (rr) "Hfrag".
      change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
        with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 8).
      iApply (swp_mono with "[Hmie Hmdl Hclk HPC HnPC Hclose] [-]").
      2:{ iApply (swp_execute_LOAD_ram_S8 SD sda_Dro (sda_Df dq)
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                    imm rs1 rd false m (pa_of ppn (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))) pmar0 pcfg paddr v
                    ((add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                       ↦₈[kt']{ dqm } v)%I (sr_swp_res R) rr
                    (sr_swp_mode R satp0)
                    Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                    (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_htif _ _ _ _ _ _ _)
                    (sda_rs_pma _ _ _ _ _ _ _) (sda_rs_pcfg _ _ _ _ _ _ _)
                    (sda_rs_paddr _ _ _ _ _ _ _)
                    ltac:(rewrite sda_rs_mst; exact HMXR)
                    ltac:(rewrite sda_rs_menv; exact Hpmm)
                    ltac:(rewrite sda_rs_mst; exact HSXL)
                    (hval_transform_effective_address_S_mode
                       (SD ∪ sda_Dro) SD
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                       (Load Data) (sr_swp_mode R satp0)
                       (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                       (sda_rs_priv _ _ _ _ _ _ _)
                       ltac:(rewrite sda_rs_mst;
                             exact (effectivePrivilege_mprv0 (Load Data) _
                                      Supervisor HMPRV))
                       eq_refl eq_refl eq_refl
                       ltac:(rewrite sda_rs_mst; exact HMXR)
                       ltac:(rewrite sda_rs_menv; exact Hpmm)
                       ltac:(rewrite sda_rs_mst; exact HSXL)
                       ltac:(rewrite sda_rs_satp;
                             exact (sr_swp_mode_ok R satp0 Hsok)))
                    (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (sr_swp_mode R satp0) (sda_in_mst_D SD) (sda_in_satp_D SD)
                       ltac:(rewrite sda_rs_mst; exact HSXL)
                       ltac:(rewrite sda_rs_satp;
                             exact (sr_swp_mode_ok R satp0 Hsok)))
                    ltac:(rewrite sda_rs_mst;
                          exact (effectivePrivilege_mprv0 (Load Data) _
                                   Supervisor HMPRV))
                    HA Hord HR Hcov (pma_all_ram Hpma_all) Hkd0
                    Halign4
                    (pa_aligned_div ppn
                       (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 8
                       ltac:(lia) ltac:(exists 512; lia) Halign4)
                    Hrd
                    with "Hcert Hfrag HRes Hfile Hrw Hro [] [Hbytes]").
          - (* THE DATA TRANSLATION, the regime's own *)
            iIntros "Hfrag HRes Hrw Hro".
            iApply (sda_translate_D R SD kt kt' dq (Load Data) KP_rw mstatus0
                      menvcfg0 satp0 pmar0 pcfg paddr tv'
                      (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn rr
                      (or_intror (or_introl eq_refl)) I Hmenvval0 HSXL HMPRV
                      Hsok
                      ltac:(unfold pmp_ent0_ok; split_and!; assumption)
                      (pma_all_ram Hpma_all) Hcan Hid Hdisj
                      (Hside (Load Data) KP_rw
                         (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn
                         tv' (or_intror (or_introl eq_refl)))
                      with "Hwit Hk Hcert Hfrag HRes Hrw Hro").
          - (* THE RAM OBLIGATION, off the word the leaf owns *)
            iIntros (sigma) "Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iDestruct (s_mem_chunk (KTR := kt') sigma
                         (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                         (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                         0 8 8 (nth_byte v)
                         ppn dqm ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff
                         Hcan with "Hmem Hk Hbytes") as %(Hbf & _ & _ & _).
            iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver|].
            iModIntro. iSplitR.
            { iPureIntro. intros j Hj. apply Hbf. exact Hj. }
            iNext. iMod "Hclose" as "_". iModIntro.
            iFrame "Hreg Hmem Hdev".
            rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iIntros (e) "(-> & Hfile & Hland)".
      iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & Hany & Hword)".
      (* the landing file back onto the tower, at ITS OWN tlb value *)
      iAssert (∃ tv2 : type_of_register tlb,
                 hreg_frame (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)
                   SD ∗
                 hreg_frame_ro (sda_Df dq)
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
                 sr_swp_res_at R satp0 tv2)%I
        with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
      { destruct Hshape as [-> | (tvx & ->)].
        - iExists tv'. iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree R
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))
                 sda_rs_satp sda_rs_tlb) in "HRes". iExact "HRes".
        - iExists tvx.
          iDestruct (sda_rw_ext_D SD _ _ Hsub (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hrw") as "Hrw".
          iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hro") as "Hro".
          iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree R
                   (register_set tlb tvx
                      (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))
                 register_lookup_set) in "HRes".
          rewrite irrelevant_register_set; [| vm_compute; reflexivity].
          rewrite sda_rs_satp. iExact "HRes". }
      iAssert (sr_swp_res R
                 (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2))
        with "[HRes]" as "HRes".
      { rewrite -(sr_swp_res_agree R
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)).
        rewrite sda_rs_satp sda_rs_tlb. iExact "HRes". }
      (* the slot re-seals itself, at the landing tlb value *)
      iDestruct ("Hclose" $! tv2 with "Hrw Hro HRes")
        as "(Hms & Hpriv & Hmenv & _ & _ & _ & Hslot)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hslot Hclk".
      iSplitR "Hany"; [| iExact "Hany"].
      iExists mstatus0, mdv0, (add_vec_int pc 2).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      rewrite Hev. iFrame "Hfile Hword".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc
         (-> & -> & -> & Hfile & Hword)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile
                            Hword").
  Qed.

  (* THE KT0/KT0 COROLLARY -- the pre-phase-D statement, character for
     character (the ambient [↦₈{dqm}] is at the KT0 default, which is
     convertible with the explicit [KT0] above), so every consumer is
     byte-identical.  The witness is [emp] and is discharged here. *)
  Lemma wp_cld_s_r (R : s_regime)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (v : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea a8 pa Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iPoseProof (sr_ktier_wit_KT0 R) as "#Hwit".
    iApply (wp_cld_s_r_t R KT0 KT0 pc rd rs1 imm m v mstatus0 mie_v mdv0 menvcfg0
              (dq := dq) (dqm := dqm)
              Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 with "Hwit").
  Qed.


End WpSmodePtLoad.

(* ===================================================================== *)
(* STATE-GENERIC store towers (the [SWSwalk]/[VWgSwalk]/[ExecStoreGSwalk] *)
(* clones): the write lands on the ABSTRACT translate output state's      *)
(* memory ([write_bytes s'.(mem) ...]).                                   *)
(* ===================================================================== *)

Section SWSwalkPt.
Variable a : mword 64.
Variable data : mword (8*8).
Variable region : PMA_Region.
Variable s s' : mstate.
Variable pa : mword 64.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Variable md : SATPMode.
Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
Hypothesis Htr : exec (translateAddr (Virtaddr a) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_vmem_write_addr_8_S_walk_pt :
  exec (vmem_write_addr (Virtaddr a) 8 data (Store Data) false false false) s
    = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa 8 data) s'.(mdev)).
Proof.
  assert (Heff : exec (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs))
                         (register_lookup cur_privilege s.(sregs))) s = Some (Supervisor, s)).
  { rewrite Hcps. apply exec_effectivePrivilege_store_S. exact Hmprvs. }
  assert (Hea : exec (mem_write_ea (Physaddr pa) 8 (Store Data) PBMT_PMA false false false) s'
                = Some (Ok tt, s')).
  { apply (exec_mem_write_ea_g 8 pa (Store Data) PBMT_PMA Supervisor s').
    - rewrite Hcp. apply exec_effectivePrivilege_store_S. exact Hmprv.
    - unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_store_g 8 pa PBMT_PMA region s' Hmatch Hpalign Hwrite)).
      cbn match. apply exec_returnM.
    - exact (exec_pmpCheck_supervisor_grant_store pa 8 s' HA Hord Hrange HW). }
  assert (Hwv : exec (mem_write_value (Physaddr pa) 8
                        (autocast (T := mword) (subrange_vec_dec data (8*8-1) 0))
                        (Store Data) PBMT_PMA false false false) s'
                = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa 8 data) s'.(mdev))).
  { rewrite (subrange_full_gen_cast (8 * 8) data ltac:(lia)).
    exact (exec_mem_write_value_8_S PBMT_PMA pa region data
             (register_lookup mstatus s'.(sregs)) s'
             HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hcp). }
  exact (exec_vmem_write_addr_aligned_store 8 a pa data Supervisor md s s'
           (MState s'.(sregs) (write_bytes s'.(mem) pa 8 data) s'.(mdev))
           ltac:(right; right; right; reflexivity) Halign Heff Htm Htr Hea Hwv).
Qed.
End SWSwalkPt.

Section VWgSwalkPt.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable data : mword (8*8).
Variable region : PMA_Region.
Variable s s' : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Variable pa : mword 64.
Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s
                  = Some (Virtaddr ea, s).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Variable md : SATPMode.
Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_vmem_write_8_gpr_S_walk_pt :
  exec (vmem_write (Regidx rs1) offset 8 data (Store Data) false false false) s
    = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa 8 data) s'.(mdev)).
Proof.
  unfold vmem_write. rewrite exec_catch_early_return.
  assert (Ha8ea : a8 = ea) by (unfold a8; rewrite subrange_id; apply sign_extend'_id).
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 8 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ Htea).
    rewrite Ha8ea. apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_write_addr_8_S_walk_pt a8 data region s s' pa Halign Hcp' Hmprv'
             md Hcps Hmprvs Htm Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
  reflexivity.
Qed.
End VWgSwalkPt.

Section ExecStoreGSwalkPt.
Variable rs2 rs1 : mword 5.
Variable imm : mword 12.
Variable region : PMA_Region.
Variable s s' : mstate.
Let offset := sign_extend' 64 imm.
Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Variable pa : mword 64.
Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s
                  = Some (Virtaddr ea, s).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Variable md : SATPMode.
Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_execute_STORE_8_gpr_S_walk_pt :
  exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s
    = Some (RETIRE_SUCCESS, MState s'.(sregs) (write_bytes s'.(mem) pa 8 vrs2) s'.(mdev)).
Proof.
  change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
    with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
  unfold execute_STORE.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_write_8_gpr_S_walk_pt rs1 offset _ region s s' pa Htea Halign
       md Hcps Hmprvs Htm Htr Hcp' Hmprv' HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
  cbn match.
  rewrite (exec_returnM _ _).
  rewrite autocast_subrange_id.
  reflexivity.
Qed.
End ExecStoreGSwalkPt.

(* ===================================================================== *)
(* Exemplar STORE leaf over [tlb_inv_pt]: c.sd rs2, imm(rs1) to a RAM     *)
(* address.  Same shape as the load: no geometry premises, no hit/walk    *)
(* case split; the data write lands on the abstract translate output      *)
(* state and the leaf's own byte window absorbs it via                    *)
(* [word_pointsto_write].                                                 *)
(* ===================================================================== *)
(* the STORE engine's data premise at width 8: the model truncates the source
   GPR to the width, and at 8 that is the identity.  As a standalone equation
   because [rewrite] cannot reach under [autocast]'s dependent index inside a
   term-position [ltac:]. *)
Lemma store_data8 (w : SailStdpp.Values.mword 64) :
  autocast (T := mword) (subrange_vec_dec w (Z.sub (Z.mul 8 8) 1) 0) = w.
Proof.
  change (Z.sub (Z.mul 8 8) 1) with 63%Z.
  rewrite RiscvExtras.subrange_full_64. apply autocast_id.
Qed.

Section WpSmodePtStore.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE TIER-INDEXED FORM -- see [wp_cld_s_r_t]'s note for the shape.  The
     STORE is tier-preserving in the same sense: the window is written and
     handed back at its own tier [kt'] (the re-mint inside
     [SmodeCorePt.s_win_write] re-uses the pin it destructured). *)
  Lemma wp_csd_s_r_t (R : s_regime) (kt kt' : ktier) `{!KtierLe kt' kt}
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (vold : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    sr_ktier_wit R kt -∗
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    pa ↦₈[kt'] vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₈[kt'] (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea a8 pa HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    unfold pa, a8, ea in *. clear pa a8 ea.
    iIntros "#Hwit #Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (word_pointsto_aligned_p (KTR := kt') with "Hbytes")
      as %Hpalign4.
    assert (Halign4 : is_aligned_vaddr
              (Virtaddr (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))) 8
              = true) by exact Hpalign4.
    pose proof (off_bound_div
                  (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 8
                  ltac:(lia) ltac:(exists 512; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA &
        %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0.
    (* the window's own claim, off byte 0, then the word refolded *)
    iDestruct (word_pointsto_bytes (KTR := kt') with "Hbytes") as "Hbytes".
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes")
      as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc (KTR := kt') with "Hb0")
      as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0
             (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    iDestruct (word_pointsto_intro (KTR := kt') _ _ _ Hpalign4 with "Hbytes")
      as "Hword".
    iApply (wp_instr_s_config_folded R pc true
              (STORE (imm, Regidx rs2, Regidx rs1, 8))
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 => (⌜npc = add_vec_int pc 2⌝ ∗
                 ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗ gpr_file m ∗
                 (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                   ↦₈[kt'] (m !!! Regidx rs2))%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr
                    [Hfile Hword] [Hcont]").
    - iIntros "Hpriv Hms Hmie Hmdl Hmenv Hslot Hclk HPC HnPC Hresv".
      (* THE SLOT STAYS FOLDED.  [sda_slot_acc_R] is the one place the two
         translation arms are told apart: it hands out an ABSTRACT write set
         with its frames, the residue, and the arm's translation SIDE
         CONDITION already discharged -- the one thing a regime-generic leaf
         cannot produce for itself ([sr_swp_side_ok] demands [tlb ∈ Drw], and
         the Bare arm's write set is empty). *)
      iDestruct (sda_slot_acc_R R dq mstatus0 menvcfg0 pmar0
                   Hmenvval0 HSXL HMPRV (pma_all_ram Hpma_all)
                   with "Hms Hpriv Hmenv Hpma Hhtif Hmisa Hslot")
        as (SD satp0 pcfg paddr tv')
           "(%Hdisj & %Hsub & %Hsok & %Hpok & %Hside & Hrw & Hro & HRes &
             Hclose)".
      destruct Hpok as (HA & Hord & HX & HW & HR & Hcov).
      iDestruct "Hresv" as (rr) "Hfrag".
      change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
        with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
      iApply (swp_mono with "[Hmie Hmdl Hclk HPC HnPC Hclose] [-]").
      2:{ iApply (swp_execute_STORE_ram_S8 SD sda_Dro (sda_Df dq)
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                    imm rs2 rs1 m
                    (pa_of ppn (add_vec (m !!! Regidx rs1)
                                  (sign_extend' 64 imm)))
                    (m !!! Regidx rs2) pmar0 pcfg paddr
                    ((add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                       ↦₈[kt'] (m !!! Regidx rs2))%I (sr_swp_res R) rr
                    (sr_swp_mode R satp0)
                    (store_data8 (m !!! Regidx rs2))
                    Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                    (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_pma _ _ _ _ _ _ _)
                    (sda_rs_pcfg _ _ _ _ _ _ _) (sda_rs_paddr _ _ _ _ _ _ _)
                    (sda_rs_htif _ _ _ _ _ _ _)
                    ltac:(rewrite sda_rs_mst; exact HMXR)
                    ltac:(rewrite sda_rs_menv; exact Hpmm)
                    ltac:(rewrite sda_rs_mst; exact HSXL)
                    (hval_transform_effective_address_S_mode
                       (SD ∪ sda_Dro) SD
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                       (Store Data) (sr_swp_mode R satp0)
                       (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                       (sda_rs_priv _ _ _ _ _ _ _)
                       ltac:(rewrite sda_rs_mst;
                             exact (effectivePrivilege_mprv0 (Store Data) _
                                      Supervisor HMPRV))
                       eq_refl eq_refl eq_refl
                       ltac:(rewrite sda_rs_mst; exact HMXR)
                       ltac:(rewrite sda_rs_menv; exact Hpmm)
                       ltac:(rewrite sda_rs_mst; exact HSXL)
                       ltac:(rewrite sda_rs_satp;
                             exact (sr_swp_mode_ok R satp0 Hsok)))
                    (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (sr_swp_mode R satp0) (sda_in_mst_D SD) (sda_in_satp_D SD)
                       ltac:(rewrite sda_rs_mst; exact HSXL)
                       ltac:(rewrite sda_rs_satp;
                             exact (sr_swp_mode_ok R satp0 Hsok)))
                    ltac:(rewrite sda_rs_mst;
                          exact (effectivePrivilege_mprv0 (Store Data) _
                                   Supervisor HMPRV))
                    HA Hord HW Hcov (pma_all_ram Hpma_all) Hkd0
                    Halign4
                    (pa_aligned_div ppn
                       (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 8
                       ltac:(lia) ltac:(exists 512; lia) Halign4)
                    with "Hcert Hfrag HRes Hfile Hrw Hro [] [Hword]").
          - iIntros "Hfrag HRes Hrw Hro".
            iApply (sda_translate_D R SD kt kt' dq (Store Data) KP_rw mstatus0
                      menvcfg0 satp0 pmar0 pcfg paddr tv'
                      (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn rr
                      (or_intror (or_intror (or_introl eq_refl))) eq_refl
                      Hmenvval0
                      HSXL HMPRV Hsok
                      ltac:(unfold pmp_ent0_ok; split_and!; assumption)
                      (pma_all_ram Hpma_all) Hcan Hid Hdisj
                      (Hside (Store Data) KP_rw
                         (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn
                         tv' (or_intror (or_intror (or_introl eq_refl))))
                      with "Hwit Hk Hcert Hfrag HRes Hrw Hro").
          - iIntros (sigma) "Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iMod (word_pointsto_write_c (KTR := kt') sigma.(mem)
                    (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn
                    vold (m !!! Regidx rs2) Hcan Hoff
                    with "Hk Hmem Hword") as "[Hmem Hword]".
            iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver|].
            iModIntro. iNext. iMod "Hclose" as "_". iModIntro.
            iFrame "Hreg Hmem Hdev Hword". }
      iIntros (e) "(-> & Hfile & Hland)".
      iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & Hword & Hfrag)".
      iAssert (∃ tv2 : type_of_register tlb,
                 hreg_frame (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)
                   SD ∗
                 hreg_frame_ro (sda_Df dq)
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
                 sr_swp_res_at R satp0 tv2)%I
        with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
      { destruct Hshape as [-> | (tvx & ->)].
        - iExists tv'. iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree R
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))
                 sda_rs_satp sda_rs_tlb) in "HRes". iExact "HRes".
        - iExists tvx.
          iDestruct (sda_rw_ext_D SD _ _ Hsub (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hrw") as "Hrw".
          iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hro") as "Hro".
          iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree R
                   (register_set tlb tvx
                      (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))
                 register_lookup_set) in "HRes".
          rewrite irrelevant_register_set; [| vm_compute; reflexivity].
          rewrite sda_rs_satp. iExact "HRes". }
      iAssert (sr_swp_res R
                 (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2))
        with "[HRes]" as "HRes".
      { rewrite -(sr_swp_res_agree R
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)).
        rewrite sda_rs_satp sda_rs_tlb. iExact "HRes". }
      (* the slot re-seals itself, at the landing tlb value *)
      iDestruct ("Hclose" $! tv2 with "Hrw Hro HRes")
        as "(Hms & Hpriv & Hmenv & _ & _ & _ & Hslot)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hslot Hclk".
      iSplitR "Hfrag"; [| by iApply resv_any_intro].
      iExists mstatus0, mdv0, (add_vec_int pc 2).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iFrame "Hfile Hword".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc
         (-> & -> & -> & Hfile & Hword)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile
                            Hword").
  Qed.

  (* THE KT0/KT0 COROLLARY -- statement character-identical to the
     pre-phase-D one; the [emp] witness is discharged here. *)
  Lemma wp_csd_s_r (R : s_regime)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (vold : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea a8 pa HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iPoseProof (sr_ktier_wit_KT0 R) as "#Hwit".
    iApply (wp_csd_s_r_t R KT0 KT0 pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0
              (dq := dq)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 with "Hwit").
  Qed.


End WpSmodePtStore.

(* the PC-reading 4-byte gpr-write engine (auipc), over [tlb_inv_pt] *)
Section WpSmodePtGprEnginePc.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


End WpSmodePtGprEnginePc.

(* γ-form gpr-write leaves relocated from WpSmodeGpr.v (rvc engine,
   c.addi16sp, jal rd) over [tlb_inv_pt] via [wp_instr_s_tlbinv_pt]. *)
Section WpSmodePtGprGamma.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [hw_config] is [smode_config]'s first (persistent) conjunct; a leaf on
     the bundle needs it to pay the fetch translation. *)
  Lemma smode_config_hw (γ : gname) (dq : dfrac) :
    smode_config γ dq -∗ hw_config ∗ smode_config γ dq.
  Proof.
    rewrite /smode_config. iIntros "[#Hhw H]".
    iSplitR; [iExact "Hhw"|]. iSplitR; [iExact "Hhw"|]. iExact "H".
  Qed.

  (* the FORCED premise change again: the instruction is a [swp] obligation.
     [wp_caddi16sp_gpr_s_r] / [_pt] below, which ARE consumed outside this
     file, keep their statements byte for byte. *)
  Lemma wp_rvc_gpr_write_s_r (R : s_regime) (γ : gname)
      (pc : mword 64) (rd : mword 5)
      (base : instruction) (wval : mword 64)
      (m : regfile)
      (q : Qp) :
    (gen_cert -∗ gpr_file m -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   gpr_file (<[Regidx rd := regval_into_reg wval]> m))) -∗
    smode_config γ (DfracOwn q) -∗
    sr_inv R -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true base -∗
    ( smode_config γ (DfracOwn q) -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hex Hsm Hinv Hpc Hfile Hinstr Hcont".
    (* UNBUNDLE rather than ride a [smode_config]-shaped wrapper: such a
       wrapper's fetch obligation does not forward mstatus.MPRV, which the
       fetch producer needs, and [smode_config] carries it.  So this is the
       folded engine above, with the bundle taken apart here and rebuilt at
       the seam. *)
    iDestruct (smode_config_unbundle with "Hsm")
      as "(#Hhw & #Hminv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0)
      "(Hmstatus & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmiec & Hmdlc & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0)
      "(Hmenvc & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval)".
    iApply (wp_gpr_write_s_config_regime R pc rd base wval m mstatus0 mie_v
              mdv0 menvcfg0 (dq := DfracOwn q)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval
              with "Hex Hhw Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hinv
                    Hpc Hfile Hinstr [Hcont Hsie]").
    iIntros "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hinv Hpc Hfile".
    iApply ("Hcont" with
              "[Hhs Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc] Hinv Hpc Hfile").
    iApply (smode_config_rebuild γ (DfracOwn q) mstatus0 mie_v mdv0 menvcfg0
              HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval
              with "Hhw Hminv Hhs Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc").
  Qed.


  Lemma wp_caddi16sp_gpr_s_r (R : s_regime) (γ : gname)
      (pc : mword 64) (imm6 : mword 6)
      (m : regfile)
      (q : Qp) :
    smode_config γ (DfracOwn q) -∗
    sr_inv R -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) -∗
    ( smode_config γ (DfracOwn q) -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6)))]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hsm Hinv Hpc Hfile Hinstr Hcont".
    assert (Hsp : uint csp_rs1 <> 0) by (vm_compute; discriminate).
    iApply (wp_rvc_gpr_write_s_r R γ pc csp_rs1
              (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI))
              (add_vec (m !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi16sp_imm imm6)))
              m q with "[] Hsm Hinv Hpc Hfile Hinstr Hcont").
    iIntros "#Hcert Hf".
    change sp with (Regidx csp_rs1).
    iApply (swp_execute_rw csp_rs1 csp_rs1 m
              (execute (ITYPE (caddi16sp_imm imm6, Regidx csp_rs1,
                               Regidx csp_rs1, ADDI)))
              RETIRE_SUCCESS
              (fun a => add_vec a (sign_extend' 64 (caddi16sp_imm imm6)))
              eq_refl Hsp with "Hcert Hf").
  Qed.

  Lemma wp_caddi16sp_gpr_s_pt (root_ppn : mword 44) (γ : gname)
      (pc : mword 64) (imm6 : mword 6)
      (m : regfile)
      (q : Qp) :
    smode_config γ (DfracOwn q) -∗
    tlb_res_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) -∗
    ( smode_config γ (DfracOwn q) -∗
      tlb_res_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6)))]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
    Proof.
    exact (wp_caddi16sp_gpr_s_r (kpt_share_regime root_ppn) γ pc imm6 m q).
  Qed.



End WpSmodePtGprGamma.
