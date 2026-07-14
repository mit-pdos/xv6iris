(* WpUserCtrlU.v -- the COMBINED (hit+miss) control-flow USTEP arms.
   The 32-bit JAL/JALR/BTYPE arms riding the combined fetch engine
   [WpUserComputeMiss.wp_instr_u]: they carry NO fetch-hit precondition
   (only [upt_tlb_ok] + [spec!!vpn]) and re-establish over the FILLED TLB.
   (* original header follows *)
   WpUserCtrl.v -- the control-flow USTEP arms (JAL/JALR/BTYPE, base and compressed).
   Split from the monolithic WpUserExec.v; all lemmas close over the
   single parameter bundle [uctx] (see WpUserBase).                      *)
(* WpUserExec.v -- the user-execution theorem: the loop frames and the
   Löb skeleton.

   [user_frame] is the loop invariant P of [wp_user_loop]: an ARBITRARY
   user machine -- existential GPRs, pc, trap CSRs, TLB (consistent with
   the page-table spec) -- over the loop-constant configuration (the
   [user_cfg] cells, the page-table ownership [upt_inv], the persistent
   user code bytes, and the writable user data bytes).

   [user_trap_frame] is Tr: the same machine handed to the kernel
   re-entry continuation -- Supervisor privilege, pc at stvec's direct
   base, trap CSRs written (existential here; refined per-cause by the
   USTEP cases that produce it).

   [wp_user_exec] is the Löb capstone: one USTEP obligation -- a single
   machine step from [user_frame] re-establishes [user_frame] (retire)
   or produces [user_trap_frame] (trap), with both continuations under a
   later -- runs arbitrary user code forever.  The USTEP obligation is
   discharged case by case in the companion files (fetch trichotomy x
   decode totality x execute families); the proven instances so far are
   the wp_user_ecall / wp_user_fetch_pagefault vertical slices.        *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv InstrBytes WpGpr.
Require Import WpDecodeBridge.
Require Import UmodeFetch UmodeEcall.
Require Import UptInv WpMmodeJal WpMemsetS WpGprStore.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.
Require Import WpUserComputeMiss.

Section WpUserCtrlU.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (U : uctx).

  Local Notation stvec_v := (WpUserBase.stvec_v U).
  Local Notation mie_v := (WpUserBase.mie_v U).
  Local Notation midl_v := (WpUserBase.midl_v U).
  Local Notation medl_v := (WpUserBase.medl_v U).
  Local Notation mip_v := (WpUserBase.mip_v U).
  Local Notation meip := (WpUserBase.meip U).
  Local Notation seip := (WpUserBase.seip U).
  Local Notation satp0 := (WpUserBase.satp0 U).
  Local Notation root := (WpUserBase.root U).
  Local Notation slots := (WpUserBase.slots U).
  Local Notation spec := (WpUserBase.spec U).
  Local Notation pmpcfg0 := (WpUserBase.pmpcfg0 U).
  Local Notation pmpaddr00 := (WpUserBase.pmpaddr00 U).
  Local Notation code := (WpUserBase.code U).
  Local Notation data := (WpUserBase.data U).
  Local Notation dq := (WpUserBase.dq U).
  Local Notation dqc := (WpUserBase.dqc U).
  Local Notation Hmm := (WpUserBase.Hmm U).
  Local Notation Hs0 := (WpUserBase.Hs0 U).
  Local Notation Hsatpmode := (WpUserBase.Hsatpmode U).
  Local Notation Hasid := (WpUserBase.Hasid U).
  Local Notation Hroot := (WpUserBase.Hroot U).
  Local Notation Htvd := (WpUserBase.Htvd U).
  Local Notation Hdel_ecall := (WpUserBase.Hdel_ecall U).
  Local Notation Hdel_fetchpf := (WpUserBase.Hdel_fetchpf U).
  Local Notation Hdel_loadpf := (WpUserBase.Hdel_loadpf U).
  Local Notation Hdel_samopf := (WpUserBase.Hdel_samopf U).
  Local Notation Hdel_illegal := (WpUserBase.Hdel_illegal U).
  Local Notation Hdel_break := (WpUserBase.Hdel_break U).
  Local Notation HpmpA := (WpUserBase.HpmpA U).
  Local Notation Hpmp_ord := (WpUserBase.Hpmp_ord U).
  Local Notation HpmpX := (WpUserBase.HpmpX U).
  Local Notation HpmpR := (WpUserBase.HpmpR U).
  Local Notation HpmpW := (WpUserBase.HpmpW U).
  Local Notation Hpmp_cov := (WpUserBase.Hpmp_cov U).
  Local Notation Hpter := (WpUserBase.Hpter U).
  Local Notation Hspec := (WpUserBase.Hspec U).
  Local Notation user_cfg := (WpUserBase.user_cfg U).
  Local Notation user_code := (WpUserBase.user_code U).
  Local Notation user_data := (WpUserBase.user_data U).
  Local Notation user_frame := (WpUserBase.user_frame U).
  Local Notation wp_instr_u_hit := (WpUserBase.wp_instr_u_hit U).
  Local Notation wp_instr_c_hit := (WpUserBase.wp_instr_c_hit U).
  Local Notation wp_instr_u := (WpUserComputeMiss.wp_instr_u U).



  (* ---- combined (hit+miss) arm: ustep_jal_u ---- *)
  Lemma ustep_jal
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 21) (rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (JAL (imm, Regidx rd), s0)) ->
    uint rd <> 0 ->
    (* target alignment (the non-RVC check form of exec_execute_JAL_gpr) *)
    eq_vec (access_vec_dec (add_vec va (sign_extend' 64 imm)) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (add_vec va (sign_extend' 64 imm)) 1) = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon Hvpn_def Hpaal
           HnotRVC Hdec Hrd Hal0 Hal1.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (JAL (imm, Regidx rd)) = false)
      by reflexivity.
    iApply (wp_instr_u va vpn ie w (JAL (imm, Regidx rd))
              ms_v tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hupt Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 4)).
    assert (HpcX : register_lookup PC s1.(sregs) = va).
    { unfold s1, set_reg; cbn [sregs]. tmig. exact Hpceq. }
    assert (HnpcX : register_lookup nextPC s1.(sregs) = add_vec_int va 4).
    { unfold s1, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    (* the execute writes nextPC := target, then rd := va + 4 *)
    iMod (reg_update _ nextPC _ (add_vec va (sign_extend' 64 imm))
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int va 4))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec_int va 4)) with "[Hrdc]")
      as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg s1 nextPC (add_vec va (sign_extend' 64 imm)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec_int va 4))).
    iSplitR.
    { iPureIntro.
      pose proof (exec_execute_JAL_gpr imm rd s1 Hrd) as HE.
      rewrite HpcX in HE.
      specialize (HE Hal0 Hal1).
      rewrite HnpcX in HE.
      change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hupt' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg s1 nextPC (add_vec va (sign_extend' 64 imm)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec_int va 4))).(sregs)
             = add_vec va (sign_extend' 64 imm)).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec va (sign_extend' 64 imm)),
            (<[Regidx rd := regval_into_reg (add_vec_int va 4)]> g), (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))).
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt' Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact (upt_tlb_ok_fill spec tlbvec vpn ie Hsome Hok) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ---- combined (hit+miss) arm: ustep_jalr_u ---- *)
  Lemma ustep_jalr
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 12) (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (JALR (imm, Regidx rs1, Regidx rd), s0)) ->
    uint rd <> 0 ->
    (* target alignment, in terms of the FRAME's rs1 value *)
    eq_vec (access_vec_dec (jalr_target (g !!! Regidx rs1) imm) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (jalr_target (g !!! Regidx rs1) imm) 1) = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon Hvpn_def Hpaal
           HnotRVC Hdec Hrd Hal0 Hal1.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (JALR (imm, Regidx rs1, Regidx rd)) = false)
      by reflexivity.
    iApply (wp_instr_u va vpn ie w (JALR (imm, Regidx rs1, Regidx rd))
              ms_v tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hupt Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 4)).
    assert (HnpcX : register_lookup nextPC s1.(sregs) = add_vec_int va 4).
    { unfold s1, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    (* rs1's value at the execute state is the frame's *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1) s1 with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Hjb : jbase rs1 s1 = g !!! Regidx rs1).
    { unfold jbase. rewrite Hrv. reflexivity. }
    (* the Zicfilp probe at the execute state (agreement survives the
       nextPC tick -- nextPC is outside the decode read set) *)
    pose proof (exec_cE_zicfilp_false_u s1
                  (agree_u_set_nextPC σ (add_vec_int va 4) Hag)) as HZ.
    (* the execute writes nextPC := target, then rd := va + 4 *)
    iMod (reg_update _ nextPC _ (jalr_target (g !!! Regidx rs1) imm)
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int va 4))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec_int va 4)) with "[Hrdc]")
      as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg s1 nextPC (jalr_target (g !!! Regidx rs1) imm))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec_int va 4))).
    iSplitR.
    { iPureIntro.
      pose proof (exec_execute_JALR_gpr imm rs1 rd s1 Hrd) as HE.
      rewrite Hjb in HE.
      specialize (HE HZ Hal0 Hal1).
      rewrite HnpcX in HE.
      change (execute (JALR (imm, Regidx rs1, Regidx rd)))
        with (execute_JALR imm (Regidx rs1) (Regidx rd)).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hupt' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg s1 nextPC (jalr_target (g !!! Regidx rs1) imm))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec_int va 4))).(sregs)
             = jalr_target (g !!! Regidx rs1) imm).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (jalr_target (g !!! Regidx rs1) imm),
            (<[Regidx rd := regval_into_reg (add_vec_int va 4)]> g), (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))).
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt' Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact (upt_tlb_ok_fill spec tlbvec vpn ie Hsome Hok) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ---- combined (hit+miss) arm: ustep_branch_fall_u ---- *)
  Lemma ustep_branch_fall_u (op : bop) (c : mword 64 -> mword 64 -> bool)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 13) (rs2 rs1 : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall (imm' : mword 13) (rs2' rs1' : mword 5) s,
       c (rvv rs1' s) (rvv rs2' s) = false ->
       exec (execute (BTYPE (imm', Regidx rs2', Regidx rs1', op))) s
         = Some (RETIRE_SUCCESS, s)) ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (BTYPE (imm, Regidx rs2, Regidx rs1, op), s0)) ->
    (* the branch is NOT taken, in frame terms *)
    c (g !!! Regidx rs1) (g !!! Regidx rs2) = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_f Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hcmp.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (BTYPE (imm, Regidx rs2, Regidx rs1, op))
                       = false) by reflexivity.
    iApply (wp_instr_u va vpn ie w (BTYPE (imm, Regidx rs2, Regidx rs1, op))
              ms_v tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hupt Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1) s1 with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2) s1 with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iModIntro.
    iExists s1.
    iSplitR.
    { iPureIntro.
      apply (Hexec_f imm rs2 rs1 s1).
      unfold rvv. rewrite Hrv1 Hrv2. exact Hcmp. }
    iSplitL "Hreg Hmem".
    { unfold s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hupt' Hcfg'".
    assert (Lnpc : register_lookup nextPC s1.(sregs) = add_vec_int va 4).
    { unfold s1, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4), g, (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))).
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt' Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact (upt_tlb_ok_fill spec tlbvec vpn ie Hsome Hok) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR; [iPureIntro; exact Hdom |].
    iExact "Hfmap".
  Qed.


  (* ---- combined (hit+miss) arm: ustep_branch_taken_u ---- *)
  Lemma ustep_branch_taken_u (op : bop) (c : mword 64 -> mword 64 -> bool)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 13) (rs2 rs1 : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall (imm' : mword 13) (rs2' rs1' : mword 5) s,
       c (rvv rs1' s) (rvv rs2' s) = true ->
       eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs))
                 (sign_extend' 64 imm')) 0) ('b"0") = true ->
       bit_to_bool (access_vec_dec (add_vec (register_lookup PC s.(sregs))
                 (sign_extend' 64 imm')) 1) = false ->
       exec (execute (BTYPE (imm', Regidx rs2', Regidx rs1', op))) s
         = Some (RETIRE_SUCCESS,
                 set_reg s nextPC (add_vec (register_lookup PC s.(sregs))
                                     (sign_extend' 64 imm')))) ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (BTYPE (imm, Regidx rs2, Regidx rs1, op), s0)) ->
    (* the branch IS taken, in frame terms; target aligned (non-RVC form) *)
    c (g !!! Regidx rs1) (g !!! Regidx rs2) = true ->
    eq_vec (access_vec_dec (add_vec va (sign_extend' 64 imm)) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (add_vec va (sign_extend' 64 imm)) 1) = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_t Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hcmp Hal0 Hal1.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (BTYPE (imm, Regidx rs2, Regidx rs1, op))
                       = false) by reflexivity.
    iApply (wp_instr_u va vpn ie w (BTYPE (imm, Regidx rs2, Regidx rs1, op))
              ms_v tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hupt Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 4)).
    assert (HpcX : register_lookup PC s1.(sregs) = va).
    { unfold s1, set_reg; cbn [sregs]. tmig. exact Hpceq. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1) s1 with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2) s1 with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    (* the taken execute writes nextPC := target *)
    iMod (reg_update _ nextPC _ (add_vec va (sign_extend' 64 imm))
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s1 nextPC (add_vec va (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_t imm rs2 rs1 s1) as HE.
      rewrite HpcX in HE.
      apply HE; [ | exact Hal0 | exact Hal1 ].
      unfold rvv. rewrite Hrv1 Hrv2. exact Hcmp. }
    iSplitL "Hreg Hmem".
    { unfold s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hupt' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s1 nextPC (add_vec va (sign_extend' 64 imm))).(sregs)
             = add_vec va (sign_extend' 64 imm)).
    { unfold set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec va (sign_extend' 64 imm)), g, (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))).
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt' Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact (upt_tlb_ok_fill spec tlbvec vpn ie Hsome Hok) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR; [iPureIntro; exact Hdom |].
    iExact "Hfmap".
  Qed.

End WpUserCtrlU.
