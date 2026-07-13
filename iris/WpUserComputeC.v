(* WpUserComputeC.v -- the compressed retiring compute USTEP arms.
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
Require Import UptInv.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.

Section WpUserComputeC.
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
  Local Notation wp_instr_c_hit := (WpUserBase.wp_instr_c_hit U).
  Local Notation wp_instr_c_hit_direct := (WpUserBase.wp_instr_c_hit_direct U).


  (* ------------------------------------------------------------------ *)
  (* The GENERIC COMPRESSED ITYPE retire case: any compressed instruction *)
  (* whose execute expands (ExecuteAs) to an ITYPE compute -- C_ADDI,     *)
  (* C_LI, C_ANDI, C_ADDI16SP, C_ADDI4SPN, and every future Zcb ANDI/XORI *)
  (* expansion ride this one arm; only the pure expansion fact differs.   *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_c_itype (op : iop) (f : mword 64 -> mword 12 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (h : mword 16) (ii : instruction)
      (imm : mword 12) (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the op's register-generic execute fact (about the BASE expansion) *)
    (forall (rs1' rd' : mword 5) (imm' : mword 12) s,
       exec (execute (ITYPE (imm', Regidx rs1', Regidx rd', op))) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd') 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                      (regval_into_reg
                         (f (if Z.eqb (uint rs1') 0 then zero_reg
                             else register_lookup
                                    (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                            imm')))) ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (* decode: h is this compressed instruction *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
    (* the pure expansion to the base ITYPE *)
    (forall s : mstate, exec (execute ii) s
       = Some (ExecuteAs (ITYPE (imm, Regidx rs1, Regidx rd, op)), s)) ->
    uint rd <> 0 ->
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
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
           Hvpn_def Hmode HisRVC Hdec Hexp Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_c_hit va vpn ie h ii (ITYPE (imm, Regidx rs1, Regidx rd, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 2)) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (f (g !!! Regidx rs1) imm))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (f (g !!! Regidx rs1) imm))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 2))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) imm))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs1 rd imm (set_reg σ nextPC (add_vec_int va 2))) as HE.
      rewrite Hrv in HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 2))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) imm))).(sregs)
             = add_vec_int va 2).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) imm)]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  Lemma ustep_c_rtype (op : rop) (f : mword 64 -> mword 64 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (rs2 rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the op's register-generic execute fact (nonzero-rd form) *)
    (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
       exec (execute (RTYPE (Regidx rs2', Regidx rs1', Regidx rd', op))) s
       = Some (RETIRE_SUCCESS,
               set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                 (regval_into_reg
                    (f (if Z.eqb (uint rs1') 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                       (if Z.eqb (uint rs2') 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))) ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (* decode: h is a compressed RTYPE op expansion *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
    (* the pure expansion to the base instruction *)
    (forall s : mstate, exec (execute ii) s
       = Some (ExecuteAs (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op)), s)) ->
    uint rd <> 0 ->
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
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon Hvpn_def
           Hmode HisRVC Hdec Hexp Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_c_hit va vpn ie h ii (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 2)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int va 2)) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 2))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs2 rs1 rd (set_reg σ nextPC (add_vec_int va 2)) Hrd) as HE.
      rewrite Hrv1 in HE. rewrite Hrv2 in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 2))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).(sregs)
             = add_vec_int va 2).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2))]> g),
            tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  Lemma ustep_c_utype (op : uop) (V : mword 20 -> mstate -> mword 64) (v : mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (imm : mword 20) (rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall (rd' : mword 5) (imm' : mword 20) s,
       exec (execute (UTYPE (imm', Regidx rd', op))) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd') 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                      (regval_into_reg (V imm' s)))) ->
    (forall s', register_lookup PC s'.(sregs) = va -> V imm s' = v) ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
    (* the pure expansion to the base instruction *)
    (forall s : mstate, exec (execute ii) s
       = Some (ExecuteAs (UTYPE (imm, Regidx rd, op)), s)) ->
    uint rd <> 0 ->
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
    intros HN Hexec_op HV Hok Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon Hvpn_def
           Hmode HisRVC Hdec Hexp Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_c_hit va vpn ie h ii (UTYPE (imm, Regidx rd, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* PC is untouched by the nextPC tick, so [V] evaluates to [v] *)
    assert (HpcX : register_lookup PC
              (set_reg σ nextPC (add_vec_int va 2)).(sregs) = va).
    { unfold set_reg; cbn [sregs]. tmig. exact Hpceq. }
    pose proof (HV (set_reg σ nextPC (add_vec_int va 2)) HpcX) as Hv.
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg v) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 2))
               (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rd imm (set_reg σ nextPC (add_vec_int va 2))) as HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hv in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 2))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v)).(sregs)
             = add_vec_int va 2).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg v]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  Lemma ustep_c_shiftiop (op : sop) (f : mword 64 -> mword 6 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (shamt : mword 6) (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall (rs1' rd' : mword 5) (shamt' : mword 6) s,
       exec (execute (SHIFTIOP (shamt', Regidx rs1', Regidx rd', op))) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd') 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                      (regval_into_reg
                         (f (if Z.eqb (uint rs1') 0 then zero_reg
                             else register_lookup
                                    (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                            shamt')))) ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
    (* the pure expansion to the base instruction *)
    (forall s : mstate, exec (execute ii) s
       = Some (ExecuteAs (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op)), s)) ->
    uint rd <> 0 ->
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
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon Hvpn_def
           Hmode HisRVC Hdec Hexp Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_c_hit va vpn ie h ii (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 2)) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (f (g !!! Regidx rs1) shamt))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (f (g !!! Regidx rs1) shamt))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 2))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) shamt))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs1 rd shamt (set_reg σ nextPC (add_vec_int va 2))) as HE.
      rewrite Hrv in HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 2))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) shamt))).(sregs)
             = add_vec_int va 2).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) shamt)]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  Lemma ustep_c_compute1 (mk : mword 5 -> mword 5 -> instruction)
      (F : mword 64 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall (rs1' rd' : mword 5) s,
       exec (execute (mk rs1' rd')) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd') 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                      (regval_into_reg
                         (F (if Z.eqb (uint rs1') 0 then zero_reg
                             else register_lookup
                                    (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs)))))) ->
    is_lpad_instruction (mk rs1 rd) = false ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
    (* the pure expansion to the base instruction *)
    (forall s : mstate, exec (execute ii) s
       = Some (ExecuteAs (mk rs1 rd), s)) ->
    uint rd <> 0 ->
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
    intros HN Hexec_op Hnlpad Hok Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
           Hvpn_def Hmode HisRVC Hdec Hexp Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_c_hit va vpn ie h ii (mk rs1 rd)
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 2)) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (F (g !!! Regidx rs1)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (F (g !!! Regidx rs1)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 2))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (F (g !!! Regidx rs1)))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs1 rd (set_reg σ nextPC (add_vec_int va 2))) as HE.
      rewrite Hrv in HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 2))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (F (g !!! Regidx rs1)))).(sregs)
             = add_vec_int va 2).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg (F (g !!! Regidx rs1))]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ------------------------------------------------------------------ *)
  (* ------------------------------------------------------------------ *)
  (* The COMPRESSED NOP-like retire case: any compressed instruction      *)
  (* whose execute retires with the state untouched and no ExecuteAs hop  *)
  (* -- C_NOP, C_NTL, ZCMOP ride this arm.                                *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_c_nop (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall s, exec (execute ii) s = Some (RETIRE_SUCCESS, s)) ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
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
    intros HN Hexec_nop Hok Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon Hvpn_def
           Hmode HisRVC Hdec.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_c_hit_direct va vpn ie h ii
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 2)).
    iModIntro.
    iExists s1.
    iSplitR; [iPureIntro; exact (Hexec_nop s1) |].
    iSplitL "Hreg Hmem".
    { unfold s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC s1.(sregs) = add_vec_int va 2).
    { unfold s1, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2), g, tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hgpr Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iFrame "Hpc' Hnpc".
  Qed.


  Lemma ustep_c_rtypew (op : ropw) (f : mword 64 -> mword 64 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (rs2 rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the op's register-generic execute fact (nonzero-rd form) *)
    (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
       exec (execute (RTYPEW (Regidx rs2', Regidx rs1', Regidx rd', op))) s
       = Some (RETIRE_SUCCESS,
               set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                 (regval_into_reg
                    (f (if Z.eqb (uint rs1') 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                       (if Z.eqb (uint rs2') 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))) ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (* decode: h is a compressed RTYPE op expansion *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
    (* the pure expansion to the base instruction *)
    (forall s : mstate, exec (execute ii) s
       = Some (ExecuteAs (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op)), s)) ->
    uint rd <> 0 ->
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
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon Hvpn_def
           Hmode HisRVC Hdec Hexp Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_c_hit va vpn ie h ii (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 2)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int va 2)) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 2))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs2 rs1 rd (set_reg σ nextPC (add_vec_int va 2)) Hrd) as HE.
      rewrite Hrv1 in HE. rewrite Hrv2 in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 2))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).(sregs)
             = add_vec_int va 2).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2))]> g),
            tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  Lemma ustep_c_mul (mulop : mul_op) (f : mword 64 -> mword 64 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (rs2 rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the op's register-generic execute fact (nonzero-rd form) *)
    (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
       exec (execute (MUL (Regidx rs2', Regidx rs1', Regidx rd', mulop))) s
       = Some (RETIRE_SUCCESS,
               set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                 (regval_into_reg
                    (f (if Z.eqb (uint rs1') 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                       (if Z.eqb (uint rs2') 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))) ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (* decode: h is a compressed RTYPE op expansion *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
    (* the pure expansion to the base instruction *)
    (forall s : mstate, exec (execute ii) s
       = Some (ExecuteAs (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop)), s)) ->
    uint rd <> 0 ->
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
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon Hvpn_def
           Hmode HisRVC Hdec Hexp Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_c_hit va vpn ie h ii (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 2)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int va 2)) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 2))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs2 rs1 rd (set_reg σ nextPC (add_vec_int va 2)) Hrd) as HE.
      rewrite Hrv1 in HE. rewrite Hrv2 in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 2))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).(sregs)
             = add_vec_int va 2).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2))]> g),
            tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  Lemma ustep_c_rtype2 (mk2 : mword 5 -> mword 5 -> mword 5 -> instruction) (f : mword 64 -> mword 64 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (rs2 rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the op's register-generic execute fact (nonzero-rd form) *)
    (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
       exec (execute (mk2 rs2' rs1' rd')) s
       = Some (RETIRE_SUCCESS,
               set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                 (regval_into_reg
                    (f (if Z.eqb (uint rs1') 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                       (if Z.eqb (uint rs2') 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))) ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (* decode: h is a compressed RTYPE op expansion *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
    (* the pure expansion to the base instruction *)
    (forall s : mstate, exec (execute ii) s
       = Some (ExecuteAs (mk2 rs2 rs1 rd), s)) ->
    uint rd <> 0 ->
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
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon Hvpn_def
           Hmode HisRVC Hdec Hexp Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_c_hit va vpn ie h ii (mk2 rs2 rs1 rd)
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 2)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int va 2)) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 2))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs2 rs1 rd (set_reg σ nextPC (add_vec_int va 2)) Hrd) as HE.
      rewrite Hrv1 in HE. rewrite Hrv2 in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 2))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).(sregs)
             = add_vec_int va 2).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2))]> g),
            tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ------------------------------------------------------------------ *)
  (* The DIRECT compressed single-source compute: the compressed          *)
  (* instruction runs its rX/wX chain itself (C_NOT, C_ZEXT_B) -- no      *)
  (* ExecuteAs hop, so the execute fact is about ii at the FIXED rs1/rd.  *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_c_compute1_direct
      (F : mword 64 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall s,
       exec (execute ii) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd) 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                      (regval_into_reg
                         (F (if Z.eqb (uint rs1) 0 then zero_reg
                             else register_lookup
                                    (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))))) ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
    uint rd <> 0 ->
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
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
           Hvpn_def Hmode HisRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_c_hit_direct va vpn ie h ii
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 2)) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (F (g !!! Regidx rs1)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (F (g !!! Regidx rs1)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 2))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (F (g !!! Regidx rs1)))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op (set_reg σ nextPC (add_vec_int va 2))) as HE.
      rewrite Hrv in HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 2))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (F (g !!! Regidx rs1)))).(sregs)
             = add_vec_int va 2).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg (F (g !!! Regidx rs1))]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


End WpUserComputeC.
