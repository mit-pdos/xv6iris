(* WpUserCompute.v -- the 32-bit retiring compute USTEP arms.
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
Require Import UptInv WpAuipc WpMmodeShiftiop.
Require Import WpMmodeLeafBase.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.

Section WpUserCompute.
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
  Local Notation user_step_obligation := (WpUserBase.user_step_obligation U).
  Local Notation wp_instr_u_hit := (WpUserBase.wp_instr_u_hit U).


  (* ------------------------------------------------------------------ *)
  (* USTEP case: ADDI (rd <> x0) -- the FIRST RETIRING instruction case.  *)
  (* Rides [wp_instr_u_hit]; the machine steps and RE-ESTABLISHES the     *)
  (* user frame: rd updated in the gpr file, pc advanced by 4, everything *)
  (* else unchanged.  The template for every integer compute family.      *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_addi
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 12) (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
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
    (* decode: w is this ADDI *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, ADDI), s0)) ->
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
    intros HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal
           HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
                       = false) by reflexivity.
    iApply (wp_instr_u_hit va vpn ie w (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    (* completeness gives the (total) lookups for rs1 and rd *)
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    (* tick nextPC first, so we read rs1 against the execute state *)
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* read the rs1 entry (x0 or a real register) -> the ADDI value *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Hav : gpr_addi_val rs1 imm (set_reg σ nextPC (add_vec_int va 4))
                  = add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)).
    { unfold gpr_addi_val. rewrite Hrv. reflexivity. }
    (* write rd (rd <> 0, so its entry is the real register points-to) *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))).
    iSplitR.
    { iPureIntro.
      rewrite (exec_execute_ITYPE_ADDI_gpr rs1 rd imm (set_reg σ nextPC (add_vec_int va 4))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hav. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    (* continuation: rebuild the user frame at pc+4 with rd updated *)
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec (g !!! Regidx rs1)
                   (sign_extend' 64 imm)))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg (add_vec (g !!! Regidx rs1)
                              (sign_extend' 64 imm))]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ------------------------------------------------------------------ *)
  (* The GENERIC ITYPE retire case: any immediate-compute op whose        *)
  (* execute writes rd := f(rs1-value, imm) and retires.  Instantiated    *)
  (* by the per-op [exec_execute_ITYPE_*_gpr] lemmas (ADDI / ORI / ANDI / *)
  (* XORI / ...), so each op needs NO further Iris proof.                 *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_itype (op : iop) (f : mword 64 -> mword 12 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 12) (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the op's register-generic execute fact *)
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
    (* decode: w is this ITYPE op *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, op), s0)) ->
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
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (ITYPE (imm, Regidx rs1, Regidx rd, op))
                       = false) by (destruct op; reflexivity).
    iApply (wp_instr_u_hit va vpn ie w (ITYPE (imm, Regidx rs1, Regidx rd, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv.
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
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) imm))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs1 rd imm (set_reg σ nextPC (add_vec_int va 4))) as HE.
      rewrite Hrv in HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) imm))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) imm)]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* the four proven immediate-compute ops, as direct instantiations *)
  Definition ustep_ori := fun va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_itype ORI (fun v i => or_vec v (sign_extend' 64 i))
      va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs1' rd' imm' s => exec_execute_ITYPE_ORI_gpr rs1' rd' imm' s).

  Definition ustep_andi := fun va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_itype ANDI (fun v i => and_vec v (sign_extend' 64 i))
      va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs1' rd' imm' s => exec_execute_ITYPE_ANDI_gpr rs1' rd' imm' s).

  Definition ustep_xori := fun va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_itype XORI (fun v i => xor_vec v (sign_extend' 64 i))
      va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs1' rd' imm' s => exec_execute_ITYPE_XORI_gpr rs1' rd' imm' s).

  Definition ustep_addi' := fun va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_itype ADDI (fun v i => add_vec v (sign_extend' 64 i))
      va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs1' rd' imm' s => exec_execute_ITYPE_ADDI_gpr rs1' rd' imm' s).


  (* ------------------------------------------------------------------ *)
  (* The GENERIC RTYPE retire case: any register-register op whose        *)
  (* execute writes rd := f(rs1-value, rs2-value) and retires.            *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_rtype (op : rop) (f : mword 64 -> mword 64 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
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
    (* decode: w is this RTYPE op *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op), s0)) ->
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
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op))
                       = false) by (destruct op; reflexivity).
    iApply (wp_instr_u_hit va vpn ie w (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr2c") as %Hrv2.
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
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs2 rs1 rd (set_reg σ nextPC (add_vec_int va 4)) Hrd) as HE.
      rewrite Hrv1 in HE. rewrite Hrv2 in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
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


  (* ADD's if-form execute fact, in the nonzero-rd shape the generic wants *)
  Lemma exec_execute_RTYPE_ADD_gpr_nz (rs2 rs1 rd : mword 5) s :
    uint rd <> 0 ->
    exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (gpr_rd_val rs2 rs1 s))).
  Proof.
    intro Hrd.
    pose proof (exec_execute_RTYPE_ADD_gpr rs2 rs1 rd s) as H.
    replace (Z.eqb (uint rd) 0) with false in H
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    exact H.
  Qed.


  (* the four proven register-register ops, as direct instantiations *)
  Definition ustep_add := fun va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_rtype ADD (fun v1 v2 => add_vec v1 v2)
      va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs2' rs1' rd' s Hrd => exec_execute_RTYPE_ADD_gpr_nz rs2' rs1' rd' s Hrd).

  Definition ustep_or := fun va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_rtype OR (fun v1 v2 => or_vec v1 v2)
      va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs2' rs1' rd' s Hrd => exec_execute_RTYPE_OR_gpr rs2' rs1' rd' s Hrd).

  Definition ustep_and := fun va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_rtype AND (fun v1 v2 => and_vec v1 v2)
      va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs2' rs1' rd' s Hrd => exec_execute_RTYPE_AND_gpr rs2' rs1' rd' s Hrd).

  Definition ustep_xor := fun va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_rtype XOR (fun v1 v2 => xor_vec v1 v2)
      va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs2' rs1' rd' s Hrd => exec_execute_RTYPE_XOR_gpr rs2' rs1' rd' s Hrd).


  (* ------------------------------------------------------------------ *)
  (* The GENERIC UTYPE retire case (LUI / AUIPC): no source register; the *)
  (* written value [V imm s] may read the pc (AUIPC), pinned to [v] by    *)
  (* the [HV] agreement hypothesis at any state whose PC is [va].         *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_utype (op : uop) (V : mword 20 -> mstate -> mword 64) (v : mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
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
       exec (ext_decode w) s0 = Some (UTYPE (imm, Regidx rd, op), s0)) ->
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
    intros HN Hexec_op HV Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (UTYPE (imm, Regidx rd, op)) = false)
      by reflexivity.
    iApply (wp_instr_u_hit va vpn ie w (UTYPE (imm, Regidx rd, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* PC is untouched by the nextPC tick, so [V] evaluates to [v] *)
    assert (HpcX : register_lookup PC
              (set_reg σ nextPC (add_vec_int va 4)).(sregs) = va).
    { unfold set_reg; cbn [sregs]. tmig. exact Hpceq. }
    pose proof (HV (set_reg σ nextPC (add_vec_int va 4)) HpcX) as Hv.
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg v) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rd imm (set_reg σ nextPC (add_vec_int va 4))) as HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hv in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v)).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg v]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* LUI: the value is imm-only *)
  Definition ustep_lui := fun va vpn ie w imm rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_utype LUI (fun imm' _ => luival imm') (luival imm)
      va vpn ie w imm rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rd' imm' s => exec_execute_UTYPE_LUI_gpr rd' imm' s)
      (fun s' _ => eq_refl).

  (* AUIPC: the value reads the pc *)
  Definition ustep_auipc := fun va vpn ie w imm rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_utype AUIPC (fun imm' s => add_vec (register_lookup PC s.(sregs)) (auipc_off imm'))
      (add_vec va (auipc_off imm))
      va vpn ie w imm rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rd' imm' s => exec_execute_UTYPE_AUIPC_gpr rd' imm' s)
      (fun s' Hpc => f_equal (fun x => add_vec x (auipc_off imm)) Hpc).


  (* ------------------------------------------------------------------ *)
  (* The GENERIC SHIFTIOP retire case (SLLI / SRLI): rd := f(rs1, shamt). *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_shiftiop (op : sop) (f : mword 64 -> mword 6 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
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
       exec (ext_decode w) s0 = Some (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op), s0)) ->
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
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op))
                       = false) by reflexivity.
    iApply (wp_instr_u_hit va vpn ie w (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv.
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
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) shamt))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs1 rd shamt (set_reg σ nextPC (add_vec_int va 4))) as HE.
      rewrite Hrv in HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) shamt))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) shamt)]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  Definition ustep_slli := fun va vpn ie w shamt rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_shiftiop SLLI (fun v sh => shift_bits_left v (subrange_vec_dec sh (Z.sub log2_xlen 1) 0))
      va vpn ie w shamt rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs1' rd' shamt' s => exec_execute_SHIFTIOP_SLLI_gpr rs1' rd' shamt' s).

  Definition ustep_srli := fun va vpn ie w shamt rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_shiftiop SRLI (fun v sh => shift_bits_right v (subrange_vec_dec sh (Z.sub log2_xlen 1) 0))
      va vpn ie w shamt rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs1' rd' shamt' s => exec_execute_SHIFTIOP_SRLI_gpr rs1' rd' shamt' s).


  (* ------------------------------------------------------------------ *)
  (* The STATE-PRESERVING retire case: any instruction whose execute      *)
  (* retires without touching the machine state -- every compute op with  *)
  (* rd = x0 (their _gpr execute lemmas reduce to Some (RETIRE, s)),      *)
  (* fences, hints.  Repacks at va + 4 with everything unchanged.         *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_nop (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall s, exec (execute ii) s = Some (RETIRE_SUCCESS, s)) ->
    is_lpad_instruction ii = false ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
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
       exec (ext_decode w) s0 = Some (ii, s0)) ->
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
    intros HN Hexec_nop Hnlpad Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_u_hit va vpn ie w ii
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 4)).
    iModIntro.
    iExists s1.
    iSplitR; [iPureIntro; exact (Hexec_nop s1) |].
    iSplitL "Hreg Hmem".
    { unfold s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC s1.(sregs) = add_vec_int va 4).
    { unfold s1, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4), g, tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hgpr Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iFrame "Hpc' Hnpc".
  Qed.


  (* rd = x0 adapters: every if-form _gpr execute lemma reduces to the
     state-preserving shape when rd = x0 *)
  Lemma exec_execute_ITYPE_x0 (op : iop) (imm : mword 12) (rs1 rd : mword 5) :
    uint rd = 0 ->
    (forall s', exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, op))) s'
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd) 0 then s'
               else set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                      (regval_into_reg (gpr_addi_val rs1 imm s')))) ->
    forall s, exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, op))) s
      = Some (RETIRE_SUCCESS, s).
  Proof.
    intros Hrd0 HE s.
    rewrite (HE s).
    replace (Z.eqb (uint rd) 0) with true by (symmetry; apply Z.eqb_eq; exact Hrd0).
    reflexivity.
  Qed.


  (* SUB's if-form fact in the nonzero-rd shape (like ADD's) *)
  Lemma exec_execute_RTYPE_SUB_gpr_nz (rs2 rs1 rd : mword 5) s :
    uint rd <> 0 ->
    exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (gpr_sub_val rs2 rs1 s))).
  Proof.
    intro Hrd.
    pose proof (exec_execute_RTYPE_SUB_gpr rs2 rs1 rd s) as H.
    replace (Z.eqb (uint rd) 0) with false in H
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    exact H.
  Qed.


  Definition ustep_sub := fun va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_rtype SUB (fun v1 v2 => sub_vec v1 v2)
      va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs2' rs1' rd' s Hrd => exec_execute_RTYPE_SUB_gpr_nz rs2' rs1' rd' s Hrd).

  Definition ustep_sltiu := fun va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_itype SLTIU (fun v i => zero_extend' 64 (bool_to_bit (zopz0zI_u v (sign_extend' 64 i))))
      va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs1' rd' imm' s => exec_execute_ITYPE_SLTIU_gpr rs1' rd' imm' s).


  (* ------------------------------------------------------------------ *)
  (* The INSTRUCTION-GENERIC single-source retire case: rd := F(rs1),     *)
  (* pc += 4, for ANY AST term [mk rs1 rd] with a state-preserving-read   *)
  (* execute fact.  Covers ADDIW and every W-form without a new clone.    *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_compute1 (mk : mword 5 -> mword 5 -> instruction)
      (F : mword 64 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
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
       exec (ext_decode w) s0 = Some (mk rs1 rd, s0)) ->
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
    intros HN Hexec_op Hnlpad Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_u_hit va vpn ie w (mk rs1 rd)
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv.
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
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (F (g !!! Regidx rs1)))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs1 rd (set_reg σ nextPC (add_vec_int va 4))) as HE.
      rewrite Hrv in HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (F (g !!! Regidx rs1)))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg (F (g !!! Regidx rs1))]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ADDIW rides the instruction-generic single-source case *)
  Definition ustep_addiw := fun (imm : mword 12) va vpn ie w rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_compute1 (fun rs1' rd' => ADDIW (imm, Regidx rs1', Regidx rd'))
      (fun v => sign_extend' 64 (subrange_vec_dec (add_vec v (sign_extend' 64 imm)) 31 0))
      va vpn ie w rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs1' rd' s => exec_execute_ADDIW_gpr rs1' rd' imm s)
      eq_refl.


  (* THE USTEP ASSEMBLY (v1).  [ustep_case] classifies one frame state    *)
  (* (pc, gprs, TLB, mstatus) into one of the PROVEN arms -- each         *)
  (* disjunct is exactly the pure premise bundle of one ustep lemma.      *)
  (* [user_step_holds] discharges [user_step_obligation] from it: the     *)
  (* Löb obligation's case tree, dispatching retire arms to the P         *)
  (* continuation and trap arms to Tr.  Extending coverage = adding a     *)
  (* disjunct here + its arm above; the classification hypothesis plays   *)
  (* the role the decode-totality hypothesis was always designed to       *)
  (* play, now composed with the per-page classification.                 *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_rtypew (op : ropw) (f : mword 64 -> mword 64 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
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
    (* decode: w is this RTYPE op *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op), s0)) ->
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
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op))
                       = false) by (destruct op; reflexivity).
    iApply (wp_instr_u_hit va vpn ie w (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr2c") as %Hrv2.
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
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs2 rs1 rd (set_reg σ nextPC (add_vec_int va 4)) Hrd) as HE.
      rewrite Hrv1 in HE. rewrite Hrv2 in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
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


  Lemma ustep_mul (mulop : mul_op) (f : mword 64 -> mword 64 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
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
    (* decode: w is this RTYPE op *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop), s0)) ->
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
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop))
                       = false) by reflexivity.
    iApply (wp_instr_u_hit va vpn ie w (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr2c") as %Hrv2.
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
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs2 rs1 rd (set_reg σ nextPC (add_vec_int va 4)) Hrd) as HE.
      rewrite Hrv1 in HE. rewrite Hrv2 in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
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


  Lemma ustep_rtype2 (mk2 : mword 5 -> mword 5 -> mword 5 -> instruction) (f : mword 64 -> mword 64 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
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
    is_lpad_instruction (mk2 rs2 rs1 rd) = false ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
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
    (* decode: w is this RTYPE op *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (mk2 rs2 rs1 rd, s0)) ->
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
    intros HN Hexec_op Hnlpad Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_u_hit va vpn ie w (mk2 rs2 rs1 rd)
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr2c") as %Hrv2.
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
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs2 rs1 rd (set_reg σ nextPC (add_vec_int va 4)) Hrd) as HE.
      rewrite Hrv1 in HE. rewrite Hrv2 in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
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


End WpUserCompute.
