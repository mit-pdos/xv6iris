(* WpPopOffVc.v -- pop_off() re-proved with the S-mode VCgen (VcGenS.v),
   including the function it calls (mycpu(), via WpMycpuVc.wp_mycpu_vc).

   Same statement as WpPopOff.wp_pop_off.  The straight-line runs are VCgen
   blocks (one [vm_compute]d symbolic execution + one [iApply wp_vc_block_s]
   each):

     - the PROLOGUE  +0x00..+0x06 (c.addi sp,-16; sd ra,8(sp); sd s0,0(sp);
       addi s0,sp,16) -- literally the same [mycpu_prologue] program as
       mycpu's, run at pop_off's pc ([popoff_prologue_run]);
     - the EPILOGUE  +0x28..+0x2c (ld ra,8(sp); ld s0,0(sp); c.addi sp,16),
       shared by BOTH bnez outcomes -- the same [mycpu_epilogue] program,
       run at pop_off's pc ([popoff_epilogue_run]) and applied once per
       branch.

   The call [jal mycpu] reuses the WpPushOffTop call-composite pattern with
   [wp_mycpu_vc] as the callee (so mycpu's straight-line runs are ALSO VCgen
   blocks), and the value-computing middle (csrr sstatus / c.andi / the
   three branches / c.lw / c.addiw / c.sw / csrsi-skip) keeps the existing
   per-instruction leaves -- branch conditions and 32-bit sign-extension
   live outside the VCgen's symbolic domain by design. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc WpGprLoad.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpSpinNew WpKernelvecNew WpPushOff.
Require Import WpPushOffMem WpPushOffCsr WpMycpu WpPushOffTop WpMemsetInstr WpHolding.
Require Import WpRvcBridge WpPopOff.
Require Import VcGen VcGenS WpMycpuVc.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* pop_off's prologue/epilogue are the SAME instruction sequences as
   mycpu's ([mycpu_prologue]/[mycpu_epilogue] from WpMycpuVc), just at
   pop_off's addresses: two fresh one-line runs. *)
Lemma popoff_prologue_run :
  vc_block_s (VSt KernelSyms.pop_off vregs_init mycpu_pro_heap0) mycpu_prologue
  = Some (VSt (KernelSyms.pop_off + 8) mycpu_pro_regs1 mycpu_pro_heap1).
Proof. vm_compute. reflexivity. Qed.

Lemma popoff_epilogue_run :
  vc_block_s (VSt (KernelSyms.pop_off + 0x28) vregs_init mycpu_epi_heap) mycpu_epilogue
  = Some (VSt (KernelSyms.pop_off + 0x2e) mycpu_epi_regs1 mycpu_epi_heap).
Proof. vm_compute. reflexivity. Qed.

Section WpPopOffVc.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation PP := KernelSyms.pop_off.

  Lemma popoff_prologue_instrs :
    kernel_text -∗ block_instrs_s PP mycpu_prologue.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s mycpu_prologue vop_s_ast].
    replace (PP + 2 + 2) with (PP + 4) by lia.
    replace (PP + 4 + 2) with (PP + 6) by lia.
    iSplitR; [by iApply ppi_00|].
    iSplitR; [by iApply ppi_02|].
    iSplitR; [by iApply ppi_04|].
    iSplitR.
    { assert (Hcreg : creg2reg_idx (Cregidx (mword_of_int 0 : mword 3))
                      = Regidx (mword_of_int 8 : mword 5))
        by (vm_compute; reflexivity).
      rewrite -Hcreg. by iApply ppi_06. }
    done.
  Qed.

  Lemma popoff_epilogue_instrs :
    kernel_text -∗ block_instrs_s (PP + 0x28) mycpu_epilogue.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s mycpu_epilogue vop_s_ast].
    replace (PP + 0x28 + 2) with (PP + 0x2a) by lia.
    replace (PP + 0x2a + 2) with (PP + 0x2c) by lia.
    iSplitR; [by iApply ppi_28|].
    iSplitR; [by iApply ppi_2a|].
    iSplitR; [by iApply ppi_2c|].
    done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the call composite (jal + the whole mycpu): the WpPushOffTop proof,  *)
  (* verbatim, with wp_mycpu_vc as the callee.                            *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_call_mycpu_vc (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (P : mword 64) (jimm : mword 21)
      (m : gmap regidx (mword 64))
      (raold s0old : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) :
    let ra_idx : mword 5 := mword_of_int 1 in
    let tp_idx : mword 5 := mword_of_int 4 in
    let s0_idx : mword 5 := mword_of_int 8 in
    let a0_idx : mword 5 := mword_of_int 10 in
    let a5_idx : mword 5 := mword_of_int 15 in
    let m0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> m in
    let pcE := mword_of_int KernelSyms.mycpu in
    let imm_entry : mword 6 := mword_of_int 48 in
    let sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry)) in
    let ra0 := m0 !!! Regidx ra_idx in
    let s00 := m0 !!! Regidx s0_idx in
    let ea_ra := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let pa_ra := ea_ra in
    let ea_s0 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let pa_s0 := ea_s0 in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    add_vec P (sign_extend' 64 jimm) = pcE ->
    po_mycpu_geom pmpcfg0 pmpaddr00 ->
    eq_vec (access_vec_dec pcE 0) ('b"0") = true ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is P -∗ gpr_file m -∗
    instr P false (JAL (jimm, Regidx (mword_of_int 1 : mword 5))) -∗
    pa_ra ↦₈ raold -∗
    pa_s0 ↦₈ s0old -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
      mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗ gpr_file (po_mycpu_out P m) -∗
      pa_ra ↦₈ ra0 -∗
      pa_s0 ↦₈ s00 -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ra_idx tp_idx s0_idx a0_idx a5_idx m0 pcE imm_entry sp' ra0 s00
      ea_ra pa_ra ea_s0 pa_s0 ret_tgt
      HN Htarget Hmyg Halign_tgt
      HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
      Hpmpp Hpteregion Hal0 HW HR Hramcov.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv #Htext Hpc Hfile Hjal Hbra Hbs0 Hcont".
    iDestruct (kv_cfg_split mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 HSIE HMPRV HSXL Hmm HPBMTE
                 with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
      as "(Hsm & Hpca & Hpaa & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpcb & Hpab)".
    iApply (wp_jal_gpr_s2 root_ppn E Φ P (mword_of_int 1) jimm m pmpcfg0 pmpaddr00 region_pte (1/2)%Qp
              HN Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              ltac:(rewrite Htarget; exact Halign_tgt)
              with "Hhw Hsm Hpca Hpaa Htlbinv Hpc Hfile Hjal [-]").
    iIntros "Hsm Hpca Hpaa Htlbinv Hpc Hfile".
    iEval (rewrite Htarget) in "Hpc".
    iDestruct (kv_cfg_recombine mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                 with "Hsm Hpca Hpaa Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpcb Hpab")
      as "(Hhs & Hpriv & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
    iApply (wp_mycpu_vc root_ppn E Φ m0 raold s0old mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
              Hmyg
              Hpmpp Hpteregion Hal0 HW HR Hramcov
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile Hbra Hbs0 Hcont").
  Qed.

  (* ==================================================================== *)
  (* wp_pop_off, re-proved.  Statement identical to WpPopOff.wp_pop_off.   *)
  (* ==================================================================== *)
  Lemma wp_pop_off_vc (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (svpn_noff svpn_int : mword 27)
      (noffv intenav : mword 32)
      (vp8 vp0 vfra vfs0 : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dqi : dfrac} :
    let pcE : mword 64 := mword_of_int PP in
    let spd := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) in
    let a_p8 := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a_p0 := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let mc_sp := add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) in
    let a_fra := add_vec mc_sp (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a_fs0 := add_vec mc_sp (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let a0v := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
    let a_noff := add_vec a0v (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a_int := add_vec a0v (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    let nv1 := sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0) in
    let storeval := (autocast (T := mword) (subrange_vec_dec nv1 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    po_mycpu_geom pmpcfg0 pmpaddr00 ->
    po_slot_geom root_ppn pmpaddr00 svpn_noff a_noff 4 ->
    po_slot_geom root_ppn pmpaddr00 svpn_int a_int 4 ->
    neq_vec (and_vec (sstatus_read mstatus0) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false ->
    zopz0zKzJ_s zero_reg (sign_extend' 64 noffv) = false ->
    eq_vec (sign_extend' 64 intenav) zero_reg = true ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    a_p8 ↦₈ vp8 -∗
    a_p0 ↦₈ vp0 -∗
    a_fra ↦₈ vfra -∗
    a_fs0 ↦₈ vfs0 -∗
    ([∗ list] j ∈ seq 0 4, (pa_add a_noff j) ↦ₘ nth_byte noffv j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add a_int j) ↦ₘ{ dqi } nth_byte intenav j) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
      mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      (∃ mf, gpr_file mf ∗
        ⌜ mf !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5) /\
          mf !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5) /\
          mf !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5) /\
          mf !!! Regidx csp_rs1 = m !!! Regidx csp_rs1 /\
          mf !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5) /\
          mf !!! Regidx (mword_of_int 10 : mword 5) = a0v ⌝) -∗
      ([∗ list] j ∈ seq 0 4, (pa_add a_noff j) ↦ₘ nth_byte storeval j) -∗
      ([∗ list] j ∈ seq 0 4, (pa_add a_int j) ↦ₘ{ dqi } nth_byte intenav j) -∗
      (∃ (w8 w0 wra ws0 : bv 64),
        a_p8 ↦₈ w8 ∗
        a_p0 ↦₈ w0 ∗
        a_fra ↦₈ wra ∗
        a_fs0 ↦₈ ws0) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pcE spd a_p8 a_p0 mc_sp a_fra a_fs0 a0v a_noff a_int nv1 storeval ret_tgt
      HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe Hpmpp Hpteregion HW HR Hramcov
      Hmyg Hg_noff Hg_int Hsst2 Hnoffpos Hint Hal0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             #Htext Hpc Hfile Hp8 Hp0 Hfra Hfs0 Hnoff Hint Hcont".
    iPoseProof (ppi_08 with "Htext") as "Hi08".
    iPoseProof (ppi_0c with "Htext") as "Hi0c".
    iPoseProof (ppi_10 with "Htext") as "Hi10".
    iPoseProof (ppi_12 with "Htext") as "Hi12".
    iPoseProof (ppi_14 with "Htext") as "Hi14".
    iPoseProof (ppi_16 with "Htext") as "Hi16".
    iPoseProof (ppi_1a with "Htext") as "Hi1a".
    iPoseProof (ppi_1c with "Htext") as "Hi1c".
    iPoseProof (ppi_1e with "Htext") as "Hi1e".
    iPoseProof (ppi_20 with "Htext") as "Hi20".
    iPoseProof (ppi_22 with "Htext") as "Hi22".
    iPoseProof (ppi_2e with "Htext") as "Hi2e".
    assert (Hcsp2 : Regidx (mword_of_int 2 : mword 5) = Regidx csp_rs1)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    (* ------------------------------------------------------------------ *)
    (* PROLOGUE +0x00..+0x06: one VCgen block.                              *)
    (* ------------------------------------------------------------------ *)
    iDestruct (gpr_file_dom with "Hfile") as "[%Hdom0 Hfile]".
    iDestruct (gpr_file_x0 m (mword_of_int 0) ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx00 Hfile]".
    set (ρA := fun k : nat =>
           if (k <? 32)%nat
           then m !!! Regidx (mword_of_int (Z.of_nat k) : mword 5)
           else if Nat.eqb k 33 then (vp8 : mword 64) else (vp0 : mword 64)).
    assert (HdenA : vregs_den ρA vregs_init = m).
    { apply (vregs_den_init_agree _ _ Hdom0 Hx00). intros k Hk.
      unfold ρA. rewrite (proj2 (Nat.ltb_lt k 32) Hk). reflexivity. }
    assert (Hara : sval_den ρA (SX 2 (wrap64 (-8))) = a_p8).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2.
      unfold a_p8, spd. rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (Has0 : sval_den ρA (SX 2 (wrap64 (-16))) = a_p0).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2.
      unfold a_p0, spd. rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (Hv33 : sval_den ρA (SX 33 0) = (vp8 : mword 64)).
    { cbn [sval_den].
      replace (ρA 33%nat) with (vp8 : mword 64) by (unfold ρA; reflexivity).
      change (add_vec (vp8 : mword 64) (mword_of_int 0))
        with (add_vec_int (vp8 : mword 64) 0).
      apply avi0. }
    assert (Hv34 : sval_den ρA (SX 34 0) = (vp0 : mword 64)).
    { cbn [sval_den].
      replace (ρA 34%nat) with (vp0 : mword 64) by (unfold ρA; reflexivity).
      change (add_vec (vp0 : mword 64) (mword_of_int 0))
        with (add_vec_int (vp0 : mword 64) 0).
      apply avi0. }
    iDestruct (popoff_prologue_instrs with "Htext") as "Hbi".
    iEval (rewrite -HdenA) in "Hfile".
    iApply (wp_vc_block_s root_ppn mycpu_prologue E Φ
              (VSt PP vregs_init mycpu_pro_heap0)
              (VSt (PP + 8) mycpu_pro_regs1 mycpu_pro_heap1)
              ρA mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
              HW HR popoff_prologue_run
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
                    Hpc Hfile Hbi [Hp8 Hp0]").
    { rewrite /vheap_own. cbn [vheap]. rewrite /mycpu_pro_heap0.
      rewrite big_sepL_cons big_sepL_cons big_sepL_nil.
      cbn [fst snd]. rewrite Hara Has0 Hv33 Hv34.
      iFrame "Hp8 Hp0". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hheap".
    (* seam out: denote the symbolic post-state as P2 (the hand-proof's map) *)
    set (P1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    assert (HspP1 : P1 !!! Regidx csp_rs1 = spd)
      by (rewrite /P1; apply lookup_total_insert).
    set (P2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (P1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> P1).
    assert (Hspv : sval_den ρA (SX 2 (wrap64 (-16)))
                   = add_vec (m !!! Regidx csp_rs1)
                             (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2. f_equal;
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hs0v : sval_den ρA (SX 2 0)
                   = add_vec (P1 !!! Regidx csp_rs1)
                             (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2 HspP1. unfold spd. rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (HmP2 : vregs_den ρA mycpu_pro_regs1 = P2).
    { unfold mycpu_pro_regs1.
      rewrite -vregs_den_insert -vregs_den_insert HdenA.
      rewrite Hspv Hs0v.
      unfold P2, P1, regval_into_reg. reflexivity. }
    iEval (rewrite HmP2) in "Hfile".
    assert (Hvra1 : sval_den ρA (SX 1 0) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { cbn [sval_den].
      replace (ρA 1%nat) with (m !!! Regidx (mword_of_int 1 : mword 5))
        by (unfold ρA; reflexivity).
      change (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (mword_of_int 0))
        with (add_vec_int (m !!! Regidx (mword_of_int 1 : mword 5)) 0).
      apply avi0. }
    assert (Hvs81 : sval_den ρA (SX 8 0) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { cbn [sval_den].
      replace (ρA 8%nat) with (m !!! Regidx (mword_of_int 8 : mword 5))
        by (unfold ρA; reflexivity).
      change (add_vec (m !!! Regidx (mword_of_int 8 : mword 5)) (mword_of_int 0))
        with (add_vec_int (m !!! Regidx (mword_of_int 8 : mword 5)) 0).
      apply avi0. }
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /mycpu_pro_heap1;
           rewrite big_sepL_cons big_sepL_cons big_sepL_nil; cbn [fst snd];
           rewrite Hara Has0 Hvra1 Hvs81) in "Hheap".
    iDestruct "Hheap" as "(Hp8 & Hp0 & _)".
    iEval (cbn [vpc]) in "Hpc".
    replace (PP + 8) with (PP + 0x08) by lia.
    (* +0x08 jal ra,mycpu; the whole mycpu() -- via the VCgen-based callee *)
    assert (HspP2 : P2 !!! Regidx csp_rs1 = spd).
    { rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact HspP1. }
    assert (HspP2r : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PP + 0x08) : mword 64) 4)]> P2) !!! Regidx csp_rs1 = spd)
      by (rewrite lookup_total_insert_ne; [ exact HspP2 | vm_compute; discriminate ]).
    iApply (wp_call_mycpu_vc root_ppn E Φ (mword_of_int (PP + 0x08)) (mword_of_int 0xc94 : mword 21) P2 vfra vfs0
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN ltac:(apply bv_eq; vm_compute; reflexivity) Hmyg
              ltac:(vm_compute; reflexivity)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
              Hpmpp Hpteregion
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              HW HR Hramcov
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile Hi08 [Hfra] [Hfs0] [-]").
    { iEval (rewrite HspP2r). iExact "Hfra". }
    { iEval (rewrite HspP2r). iExact "Hfs0". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hfra Hfs0".
    iEval (rewrite HspP2r) in "Hfra". iEval (rewrite HspP2r) in "Hfs0".
    iEval (rewrite lookup_total_insert) in "Hpc".
    assert (Hpc0c : update_vec_dec (add_vec (add_vec_int (mword_of_int (PP + 0x08) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (PP + 0x0c) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    set (C := po_mycpu_out (mword_of_int (PP + 0x08)) P2).
    (* +0x0c csrr a5,sstatus *)
    iApply (wp_csrr_sstatus_s root_ppn E Φ (mword_of_int (PP + 0x0c)) (mword_of_int 15) C
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (P3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read mstatus0)]> C).
    assert (Hpp10 : add_vec_int (mword_of_int (PP + 0x0c) : mword 64) 4 = mword_of_int (PP + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.andi a5,2 *)
    iApply (wp_candi_s root_ppn E Φ (mword_of_int (PP + 0x10)) (mword_of_int 15) (mword_of_int 2 : mword 6)
              P3 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi10 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (P4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (P3 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> P3).
    assert (Ha5P3 : P3 !!! Regidx (mword_of_int 15 : mword 5) = sstatus_read mstatus0)
      by (rewrite /P3; apply lookup_total_insert).
    assert (Hpp12 : add_vec_int (mword_of_int (PP + 0x10) : mword 64) 2 = mword_of_int (PP + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.bnez a5 NOT taken (SIE = 0) *)
    assert (Ha5P4 : P4 !!! Regidx (mword_of_int 15 : mword 5)
                    = and_vec (sstatus_read mstatus0) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))).
    { rewrite /P4. rewrite lookup_total_insert. rewrite Ha5P3. reflexivity. }
    iApply (wp_cbnez_fall_s root_ppn E Φ (mword_of_int (PP + 0x12)) (mword_of_int 15) (Cregidx (mword_of_int 7)) (mword_of_int 15)
              P4 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5P4; exact Hsst2)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    assert (Hpp14 : add_vec_int (mword_of_int (PP + 0x12) : mword 64) 2 = mword_of_int (PP + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.lw a5,120(a0): a5 := sext64 noffv *)
    assert (Ha0C : C !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /C po_mycpu_out_a0.
      rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Ha0P4 : P4 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Ha0C. }
    assert (HAnoff4 : add_vec (P4 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 120 : mword 12)) = a_noff)
      by (rewrite Ha0P4; reflexivity).
    pose proof Hg_noff as (Ncanon & Nvpn & Nident & Nmask & Nvpn2 & Nmvpn & Nmppn & Nrange & Nalign & Npalign).
    iApply (wp_clw_s root_ppn E Φ (mword_of_int (PP + 0x14)) (mword_of_int 15) (mword_of_int 10)
              (mword_of_int 120) svpn_noff P4 noffv mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              ltac:(rewrite HAnoff4; exact Ncanon) ltac:(rewrite HAnoff4; exact Nvpn) ltac:(rewrite HAnoff4; exact Nident)
              Nmask Nvpn2 Nmvpn Nmppn Hpmpp Hpteregion ltac:(rewrite HAnoff4; exact Nrange) HR
              ltac:(rewrite HAnoff4; exact Nalign) ltac:(rewrite HAnoff4; exact Npalign)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi14 [Hnoff] [-]").
    { iEval (rewrite HAnoff4). iExact "Hnoff". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hnoff".
    iEval (rewrite HAnoff4) in "Hnoff".
    set (P5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noffv)]> P4).
    assert (Hpp16 : add_vec_int (mword_of_int (PP + 0x14) : mword 64) 2 = mword_of_int (PP + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 blez a5 NOT taken (noff >= 1) *)
    assert (Ha5P5 : P5 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 noffv)
      by (rewrite /P5; apply lookup_total_insert).
    iApply (wp_bge_x0_fall_s root_ppn E Φ (mword_of_int (PP + 0x16)) (mword_of_int 0x26 : mword 13) (mword_of_int 15)
              P5 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5P5; exact Hnoffpos)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    assert (Hpp1a : add_vec_int (mword_of_int (PP + 0x16) : mword 64) 4 = mword_of_int (PP + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.addiw a5,-1 *)
    iApply (wp_caddiw_s root_ppn E Φ (mword_of_int (PP + 0x1a)) (mword_of_int 15) (mword_of_int 63 : mword 6)
              P5 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (P6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (P5 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> P5).
    assert (Ha5P6 : P6 !!! Regidx (mword_of_int 15 : mword 5) = nv1).
    { rewrite /P6. rewrite lookup_total_insert. rewrite Ha5P5. reflexivity. }
    assert (Hpp1c : add_vec_int (mword_of_int (PP + 0x1a) : mword 64) 2 = mword_of_int (PP + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.sw a5,120(a0): noff := noff-1 *)
    assert (Ha0P6 : P6 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Ha0P4. }
    assert (HAnoff6 : add_vec (P6 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 120 : mword 12)) = a_noff)
      by (rewrite Ha0P6; reflexivity).
    iApply (wp_csw_s root_ppn E Φ (mword_of_int (PP + 0x1c)) (mword_of_int 15) (mword_of_int 10)
              (mword_of_int 120) svpn_noff P6 noffv mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              ltac:(rewrite HAnoff6; exact Ncanon) ltac:(rewrite HAnoff6; exact Nvpn) ltac:(rewrite HAnoff6; exact Nident)
              Nmask Nvpn2 Nmvpn Nmppn Hpmpp Hpteregion ltac:(rewrite HAnoff6; exact Nrange) HW
              ltac:(rewrite HAnoff6; exact Nalign) ltac:(rewrite HAnoff6; exact Npalign)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1c [Hnoff] [-]").
    { iEval (rewrite HAnoff6). iExact "Hnoff". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hnoff".
    iEval (rewrite HAnoff6 Ha5P6) in "Hnoff".
    assert (Hpp1e : add_vec_int (mword_of_int (PP + 0x1c) : mword 64) 2 = mword_of_int (PP + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* the shared VCgen EPILOGUE (both bnez outcomes land on it): factored
       here as a local Iris abbreviation applied in each branch. *)
    (* +0x1e c.bnez a5: both outcomes (noff-1 <> 0 / = 0) *)
    destruct (neq_vec nv1 zero_reg) eqn:Hnz.
    - (* taken: skip the intena check, straight to the epilogue at +0x28 *)
      iApply (wp_cbnez_taken_s_zca root_ppn E Φ (mword_of_int (PP + 0x1e)) (mword_of_int 5) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                P6 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5P6; exact Hnz)
                ltac:(vm_compute; reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      assert (Hpc28 : add_vec (mword_of_int (PP + 0x1e) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0"))))
                      = mword_of_int (PP + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc28) in "Hpc".
      (* ---- VCgen epilogue from P6 ---- *)
      assert (HspC : C !!! Regidx csp_rs1 = spd).
      { rewrite /C po_mycpu_out_csp. exact HspP2. }
      assert (HspP6 : P6 !!! Regidx csp_rs1 = spd).
      { rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact HspC. }
      iDestruct (gpr_file_dom with "Hfile") as "[%HdomM Hfile]".
      iDestruct (gpr_file_x0 P6 (mword_of_int 0) ltac:(vm_compute; reflexivity)
                   with "Hfile") as "[%Hx0M Hfile]".
      set (ρC := fun k : nat =>
             if (k <? 32)%nat
             then P6 !!! Regidx (mword_of_int (Z.of_nat k) : mword 5)
             else if Nat.eqb k 33
                  then m !!! Regidx (mword_of_int 1 : mword 5)
                  else m !!! Regidx (mword_of_int 8 : mword 5)).
      assert (HdenC : vregs_den ρC vregs_init = P6).
      { apply (vregs_den_init_agree _ _ HdomM Hx0M). intros k Hk.
        unfold ρC. rewrite (proj2 (Nat.ltb_lt k 32) Hk). reflexivity. }
      assert (HspC2 : ρC 2%nat = spd).
      { replace (ρC 2%nat) with (P6 !!! Regidx (mword_of_int 2 : mword 5))
          by (unfold ρC; reflexivity).
        rewrite Hcsp2. exact HspP6. }
      assert (HaraC : sval_den ρC (SX 2 8) = a_p8).
      { cbn [sval_den]. rewrite HspC2. unfold a_p8. f_equal;
        apply bv_eq; vm_compute; reflexivity. }
      assert (Has0C : sval_den ρC (SX 2 0) = a_p0).
      { cbn [sval_den]. rewrite HspC2. unfold a_p0. f_equal;
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hv33C : sval_den ρC (SX 33 0) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { cbn [sval_den].
        replace (ρC 33%nat) with (m !!! Regidx (mword_of_int 1 : mword 5))
          by (unfold ρC; reflexivity).
        change (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (mword_of_int 0))
          with (add_vec_int (m !!! Regidx (mword_of_int 1 : mword 5)) 0).
        apply avi0. }
      assert (Hv34C : sval_den ρC (SX 34 0) = m !!! Regidx (mword_of_int 8 : mword 5)).
      { cbn [sval_den].
        replace (ρC 34%nat) with (m !!! Regidx (mword_of_int 8 : mword 5))
          by (unfold ρC; reflexivity).
        change (add_vec (m !!! Regidx (mword_of_int 8 : mword 5)) (mword_of_int 0))
          with (add_vec_int (m !!! Regidx (mword_of_int 8 : mword 5)) 0).
        apply avi0. }
      iEval (rewrite -HdenC) in "Hfile".
      iDestruct (popoff_epilogue_instrs with "Htext") as "Hbi2".
      iApply (wp_vc_block_s root_ppn mycpu_epilogue E Φ
                (VSt (PP + 0x28) vregs_init mycpu_epi_heap)
                (VSt (PP + 0x2e) mycpu_epi_regs1 mycpu_epi_heap)
                ρC mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
                (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
                HW HR popoff_epilogue_run
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
                      Hpc Hfile Hbi2 [Hp8 Hp0]").
      { rewrite /vheap_own. cbn [vheap]. rewrite /mycpu_epi_heap.
        rewrite big_sepL_cons big_sepL_cons big_sepL_nil.
        cbn [fst snd]. rewrite HaraC Has0C Hv33C Hv34C.
        iFrame "Hp8 Hp0". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hheap".
      (* seam out *)
      assert (Hsp16C : sval_den ρC (SX 2 16) = add_vec spd (mword_of_int 16)).
      { cbn [sval_den]. rewrite HspC2. reflexivity. }
      set (Qf := <[Regidx csp_rs1 := add_vec spd (mword_of_int 16)]>
                   (<[Regidx (mword_of_int 8 : mword 5) := m !!! Regidx (mword_of_int 8 : mword 5)]>
                      (<[Regidx (mword_of_int 1 : mword 5) := m !!! Regidx (mword_of_int 1 : mword 5)]> P6))).
      assert (HmQf : vregs_den ρC mycpu_epi_regs1 = Qf).
      { unfold mycpu_epi_regs1.
        rewrite -vregs_den_insert -vregs_den_insert -vregs_den_insert HdenC.
        rewrite Hv33C Hv34C Hsp16C. reflexivity. }
      iEval (rewrite HmQf) in "Hfile".
      iEval (rewrite /vheap_own; cbn [vheap]; rewrite /mycpu_epi_heap;
             rewrite big_sepL_cons big_sepL_cons big_sepL_nil; cbn [fst snd];
             rewrite HaraC Has0C Hv33C Hv34C) in "Hheap".
      iDestruct "Hheap" as "(Hp8 & Hp0 & _)".
      assert (HraQf : Qf !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /Qf. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        apply lookup_total_insert. }
      (* +0x2e c.ret *)
      iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (PP + 0x2e)) (mword_of_int 1) Qf
                mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate) Hlpe
                ltac:(rewrite HraQf; exact Hal0)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      iEval (rewrite HraQf) in "Hpc".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc [Hfile] Hnoff Hint [Hp8 Hp0 Hfra Hfs0]").
      { iExists Qf. iFrame "Hfile". iPureIntro.
        split; [exact HraQf|]. split; [|split; [|split; [|split]]].
        - rewrite /Qf. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          apply lookup_total_insert.
        - rewrite /Qf. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_s1.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - rewrite /Qf. rewrite lookup_total_insert.
          rewrite /spd po_addv_assoc.
          replace (add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
                           (mword_of_int 16 : mword 64))
            with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
          apply kv_addv_zero.
        - rewrite /Qf. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_tp.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - rewrite /Qf. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          exact Ha0P6.
      }
      iExists _, _, _, _. iFrame "Hp8 Hp0 Hfra Hfs0".
    - (* fall: noff-1 = 0, read intena (= 0), c.beqz taken to +0x28 *)
      iApply (wp_cbnez_fall_s root_ppn E Φ (mword_of_int (PP + 0x1e)) (mword_of_int 5) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                P6 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5P6; exact Hnz)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      assert (Hpp20 : add_vec_int (mword_of_int (PP + 0x1e) : mword 64) 2 = mword_of_int (PP + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      (* +0x20 c.lw a5,124(a0): a5 := sext64 intenav *)
      assert (HAint6 : add_vec (P6 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 124 : mword 12)) = a_int)
        by (rewrite Ha0P6; reflexivity).
      pose proof Hg_int as (Icanon & Ivpn & Iident & Imask & Ivpn2 & Imvpn & Imppn & Irange & Ialign & Ipalign).
      iApply (wp_clw_s root_ppn E Φ (mword_of_int (PP + 0x20)) (mword_of_int 15) (mword_of_int 10)
                (mword_of_int 124) svpn_int P6 intenav mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
                (dq:=DfracOwn 1) (dqm:=dqi)
                HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
                ltac:(rewrite HAint6; exact Icanon) ltac:(rewrite HAint6; exact Ivpn) ltac:(rewrite HAint6; exact Iident)
                Imask Ivpn2 Imvpn Imppn Hpmpp Hpteregion ltac:(rewrite HAint6; exact Irange) HR
                ltac:(rewrite HAint6; exact Ialign) ltac:(rewrite HAint6; exact Ipalign)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi20 [Hint] [-]").
      { iEval (rewrite HAint6). iExact "Hint". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hint".
      iEval (rewrite HAint6) in "Hint".
      set (P7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 intenav)]> P6).
      assert (Ha5P7 : P7 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 intenav)
        by (rewrite /P7; apply lookup_total_insert).
      assert (Hpp22 : add_vec_int (mword_of_int (PP + 0x20) : mword 64) 2 = mword_of_int (PP + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* +0x22 c.beqz a5 TAKEN (intena = 0) *)
      iApply (wp_cbeqz_taken_s_zca root_ppn E Φ (mword_of_int (PP + 0x22)) (mword_of_int 3) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                P7 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5P7; exact Hint)
                ltac:(vm_compute; reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi22 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      assert (Hpc28 : add_vec (mword_of_int (PP + 0x22) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                      = mword_of_int (PP + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc28) in "Hpc".
      (* ---- VCgen epilogue from P7 ---- *)
      assert (HspC : C !!! Regidx csp_rs1 = spd).
      { rewrite /C po_mycpu_out_csp. exact HspP2. }
      assert (HspP7 : P7 !!! Regidx csp_rs1 = spd).
      { rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact HspC. }
      iDestruct (gpr_file_dom with "Hfile") as "[%HdomM Hfile]".
      iDestruct (gpr_file_x0 P7 (mword_of_int 0) ltac:(vm_compute; reflexivity)
                   with "Hfile") as "[%Hx0M Hfile]".
      set (ρC := fun k : nat =>
             if (k <? 32)%nat
             then P7 !!! Regidx (mword_of_int (Z.of_nat k) : mword 5)
             else if Nat.eqb k 33
                  then m !!! Regidx (mword_of_int 1 : mword 5)
                  else m !!! Regidx (mword_of_int 8 : mword 5)).
      assert (HdenC : vregs_den ρC vregs_init = P7).
      { apply (vregs_den_init_agree _ _ HdomM Hx0M). intros k Hk.
        unfold ρC. rewrite (proj2 (Nat.ltb_lt k 32) Hk). reflexivity. }
      assert (HspC2 : ρC 2%nat = spd).
      { replace (ρC 2%nat) with (P7 !!! Regidx (mword_of_int 2 : mword 5))
          by (unfold ρC; reflexivity).
        rewrite Hcsp2. exact HspP7. }
      assert (HaraC : sval_den ρC (SX 2 8) = a_p8).
      { cbn [sval_den]. rewrite HspC2. unfold a_p8. f_equal;
        apply bv_eq; vm_compute; reflexivity. }
      assert (Has0C : sval_den ρC (SX 2 0) = a_p0).
      { cbn [sval_den]. rewrite HspC2. unfold a_p0. f_equal;
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hv33C : sval_den ρC (SX 33 0) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { cbn [sval_den].
        replace (ρC 33%nat) with (m !!! Regidx (mword_of_int 1 : mword 5))
          by (unfold ρC; reflexivity).
        change (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (mword_of_int 0))
          with (add_vec_int (m !!! Regidx (mword_of_int 1 : mword 5)) 0).
        apply avi0. }
      assert (Hv34C : sval_den ρC (SX 34 0) = m !!! Regidx (mword_of_int 8 : mword 5)).
      { cbn [sval_den].
        replace (ρC 34%nat) with (m !!! Regidx (mword_of_int 8 : mword 5))
          by (unfold ρC; reflexivity).
        change (add_vec (m !!! Regidx (mword_of_int 8 : mword 5)) (mword_of_int 0))
          with (add_vec_int (m !!! Regidx (mword_of_int 8 : mword 5)) 0).
        apply avi0. }
      iEval (rewrite -HdenC) in "Hfile".
      iDestruct (popoff_epilogue_instrs with "Htext") as "Hbi2".
      iApply (wp_vc_block_s root_ppn mycpu_epilogue E Φ
                (VSt (PP + 0x28) vregs_init mycpu_epi_heap)
                (VSt (PP + 0x2e) mycpu_epi_regs1 mycpu_epi_heap)
                ρC mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
                (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
                HW HR popoff_epilogue_run
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
                      Hpc Hfile Hbi2 [Hp8 Hp0]").
      { rewrite /vheap_own. cbn [vheap]. rewrite /mycpu_epi_heap.
        rewrite big_sepL_cons big_sepL_cons big_sepL_nil.
        cbn [fst snd]. rewrite HaraC Has0C Hv33C Hv34C.
        iFrame "Hp8 Hp0". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hheap".
      assert (Hsp16C : sval_den ρC (SX 2 16) = add_vec spd (mword_of_int 16)).
      { cbn [sval_den]. rewrite HspC2. reflexivity. }
      set (Qf := <[Regidx csp_rs1 := add_vec spd (mword_of_int 16)]>
                   (<[Regidx (mword_of_int 8 : mword 5) := m !!! Regidx (mword_of_int 8 : mword 5)]>
                      (<[Regidx (mword_of_int 1 : mword 5) := m !!! Regidx (mword_of_int 1 : mword 5)]> P7))).
      assert (HmQf : vregs_den ρC mycpu_epi_regs1 = Qf).
      { unfold mycpu_epi_regs1.
        rewrite -vregs_den_insert -vregs_den_insert -vregs_den_insert HdenC.
        rewrite Hv33C Hv34C Hsp16C. reflexivity. }
      iEval (rewrite HmQf) in "Hfile".
      iEval (rewrite /vheap_own; cbn [vheap]; rewrite /mycpu_epi_heap;
             rewrite big_sepL_cons big_sepL_cons big_sepL_nil; cbn [fst snd];
             rewrite HaraC Has0C Hv33C Hv34C) in "Hheap".
      iDestruct "Hheap" as "(Hp8 & Hp0 & _)".
      assert (HraQf : Qf !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /Qf. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        apply lookup_total_insert. }
      (* +0x2e c.ret *)
      iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (PP + 0x2e)) (mword_of_int 1) Qf
                mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate) Hlpe
                ltac:(rewrite HraQf; exact Hal0)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      iEval (rewrite HraQf) in "Hpc".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc [Hfile] Hnoff Hint [Hp8 Hp0 Hfra Hfs0]").
      { iExists Qf. iFrame "Hfile". iPureIntro.
        split; [exact HraQf|]. split; [|split; [|split; [|split]]].
        - rewrite /Qf. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          apply lookup_total_insert.
        - rewrite /Qf. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_s1.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - rewrite /Qf. rewrite lookup_total_insert.
          rewrite /spd po_addv_assoc.
          replace (add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
                           (mword_of_int 16 : mword 64))
            with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
          apply kv_addv_zero.
        - rewrite /Qf. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_tp.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - rewrite /Qf. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          exact Ha0P6.
      }
      iExists _, _, _, _. iFrame "Hp8 Hp0 Hfra Hfs0".
  Qed.

End WpPopOffVc.
