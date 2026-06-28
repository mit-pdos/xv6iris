(* 2-aligned-fetch variants of the ALU WPs needed by the start()/timerinit chain
   (addi/ori land at addr%4=2 PCs).  Leaf file: imports the WP files, imported by
   nothing, so it can be edited while other WP files compile.  Each _2 variant is
   the 4-aligned wp with fetch_from_pts_minstret -> _2 and the wp_step_jal-style
   alignment+halfword hyps + the misa resource; the forward lemma is reused. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry WpGpr WpGprAddi WpGprLogic WpGprLui.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

Section WpAlu2.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma wp_addi_gpr_2 (pc : mword 64) (w : mword 32) (rs1 rd : mword 5) (imm : mword 12)
      (m : gmap register_bitvector_64 (mword 64)) (va vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rs1 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some va ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j)) ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, ADDI), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (add_vec va (sign_extend' 64 imm))]> m) -∗
        reg_pointsto misa dqc misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hr1 Hrd Hm1 Hmd Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
             Hconcat Haddr Hlo Hhi HmisaC HmisaS Hdec Hb1 HmIE Help)
      "#Hinv Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_addi_val rs1 imm (s_pci s pc b1) = add_vec va (sign_extend' 64 imm))
      by (apply (gpr_addi_val_file s pc b1 rs1 imm va Hr1 Lrs1)).
    iEval (rewrite <- Lmisa) in "Hmisa".
    iDestruct (fetch_from_pts_minstret_2 pc w regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
                 Hconcat Haddr Hlo Hhi ltac:(rewrite Lmisa; exact HmisaC)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFci s pc b1 rs1 rd imm (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFi_eq s pc b1 rs1 rd imm (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_addi_gpr s pc b1 w rs1 rd imm Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iEval (rewrite Lmisa) in "Hmisa".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_addi_val rs1 imm (s_pci s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec va (sign_extend' 64 imm))) with "Hrdc") as "Hfile".
    unfold sFci, base_upd_i. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.

  Lemma wp_ori_gpr_2 (pc : mword 64) (w : mword 32) (rs1 rd : mword 5) (imm : mword 12)
      (m : gmap register_bitvector_64 (mword 64)) (va vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rs1 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some va ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j)) ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, ORI), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (or_vec va (sign_extend' 64 imm))]> m) -∗
        reg_pointsto misa dqc misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hr1 Hrd Hm1 Hmd Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
             Hconcat Haddr Hlo Hhi HmisaC HmisaS Hdec Hb1 HmIE Help)
      "#Hinv Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_ori_val rs1 imm (s_pcori s pc b1) = or_vec va (sign_extend' 64 imm))
      by (apply (gpr_ori_val_file s pc b1 rs1 imm va Hr1 Lrs1)).
    iEval (rewrite <- Lmisa) in "Hmisa".
    iDestruct (fetch_from_pts_minstret_2 pc w regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
                 Hconcat Haddr Hlo Hhi ltac:(rewrite Lmisa; exact HmisaC)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcori s pc b1 rs1 rd imm (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFori_eq s pc b1 rs1 rd imm (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_ori_gpr s pc b1 w rs1 rd imm Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iEval (rewrite Lmisa) in "Hmisa".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_ori_val rs1 imm (s_pcori s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (or_vec va (sign_extend' 64 imm))) with "Hrdc") as "Hfile".
    unfold sFcori, base_upd_ori. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.

  Lemma wp_lui_gpr_2 (pc : mword 64) (w : mword 32) (rd : mword 5) (imm : mword 20)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j)) ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (UTYPE (imm, Regidx rd, LUI), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (luival imm)]> m) -∗
        reg_pointsto misa dqc misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hmd Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
             Hconcat Haddr Hlo Hhi HmisaC HmisaS Hdec Hb1 HmIE Help)
      "#Hinv Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iEval (rewrite <- Lmisa) in "Hmisa".
    iDestruct (fetch_from_pts_minstret_2 pc w regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
                 Hconcat Haddr Hlo Hhi ltac:(rewrite Lmisa; exact HmisaC)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcl s pc b1 rd imm (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFl_eq s pc b1 rd imm (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_lui_gpr s pc b1 w rd imm Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iEval (rewrite Lmisa) in "Hmisa".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (luival imm)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg (luival imm)) with "Hrdc") as "Hfile".
    unfold sFcl, base_upd_l. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.

End WpAlu2.
