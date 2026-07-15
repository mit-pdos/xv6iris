(* WpUserMemC.v -- the COMPRESSED memory USTEP arms: C_LD/C_LDSP and
   C_SD/C_SDSP expand (ExecuteAs) to width-8 LOAD/STORE, so these are
   the c-transforms of the WpUserMem arms riding wp_instr_c_hit.
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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpGpr.
Require Import SmodeCore WpIntrCore WpDecodeBridge.
Require Import UmodeFetch UmodeEcall.
Require Import UptInv UmodeData WpGprStore.
Require Import UmodeWalk WpUserComputeMiss.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.
Require Import WpUserFetchCMiss.

Section WpUserMemC.
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
  Local Notation wp_instr_c_hit_data := (WpUserBase.wp_instr_c_hit_data U).
  Local Notation wp_instr_c_data := (WpUserFetchCMiss.wp_instr_c_data U).


  (* ------------------------------------------------------------------ *)
  (* USTEP case: LD (8-byte load, rd <> x0) from a CODE page: the data    *)
  (* address hits the TLB at its walk entry (R permission, A set), and    *)
  (* the loaded dword's bytes live in the persistent code image.          *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_c_ld_code
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs1 rd : mword 5) (v : mword 64)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
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
       = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, false, 8)), s)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 8 = true ->
    (forall j : nat, (j < 8)%nat ->
       code !! pa_add paD j = Some (nth_byte v j)) ->
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
    intros eaF paD HN Hok Hvec Hchk0 HupdN Hpbmt0 HSXL HMPRV HMXR Hcanon
           Hvpn_def Hmode HisRVC Hdec Hexp Hrd HsomeD HvecD HchkD HupdD
           HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hcwd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_c_hit va vpn ie h ii (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg [Hmem Hdev]]".
    destruct Hpins as (Lpriv0 & Lms0 & Lsatp0 & Ltlb0 & Lpmpc0 & Lpmpa0).
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1) s1 with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    set (eaS := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s1.(sregs))
                        (sign_extend' 64 imm)).
    assert (Hea : eaS = eaF) by (unfold eaS, eaF; rewrite Hrv; reflexivity).
    set (paS := u_pa (upt_entry vpnD ieD) eaS vpnD).
    assert (Hpa : paS = paD)
      by (unfold paS, paD; rewrite Hea; reflexivity).
    (* ---- machine-state pins at s1 ---- *)
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa0.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma0.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif0.
    assert (Lpriv1 : register_lookup cur_privilege s1.(sregs) = User)
      by (unfold s1; lk; exact Lpriv0).
    assert (Lms1 : register_lookup mstatus s1.(sregs) = ms_v)
      by (unfold s1; lk; exact Lms0).
    assert (Lsatp1 : register_lookup satp s1.(sregs) = satp0)
      by (unfold s1; lk; exact Lsatp0).
    assert (Ltlb1 : register_lookup tlb s1.(sregs) = tlbvec)
      by (unfold s1; lk; exact Ltlb0).
    assert (Lpmpc1 : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
      by (unfold s1; lk; exact Lpmpc0).
    assert (Lpmpa1 : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
      by (unfold s1; lk; exact Lpmpa0).
    (* the persistent-cell reads above ran AFTER the nextPC tick, so they
       are already s1 facts *)
    assert (Lmisa1 : register_lookup misa s1.(sregs) = misa0) by exact Lmisa0.
    assert (Lpma1 : register_lookup pma_regions s1.(sregs) = pmar0) by exact Lpma0.
    assert (Lhtif1 : register_lookup htif_tohost_base s1.(sregs) = None) by exact Lhtif0.
    assert (HES1 : exec (currentlyEnabled Ext_S) s1 = Some (true, s1)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa1.
      rewrite Hmisa_val0 in HmisaS. rewrite Hmisa_val0. exact HmisaS. }
    assert (Lsenv1 : register_lookup senvcfg s1.(sregs) = mword_of_int 0).
    { unfold s1; lk.
      rewrite (Hag (R_bitvector_64 senvcfg) ltac:(vm_compute; reflexivity)).
      vm_compute; reflexivity. }
    assert (Lmenv1 : register_lookup menvcfg s1.(sregs) = MENVCFG_S).
    { unfold s1; lk.
      rewrite (Hag (R_bitvector_64 menvcfg) ltac:(vm_compute; reflexivity)).
      vm_compute; reflexivity. }
    (* ---- the data-entry leaf facts at Load Data ---- *)
    assert (HchkD' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (Load Data) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpnD ieD)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpnD ieD))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact HchkD. }
    assert (HupdD' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpnD ieD)) (Load Data)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdD. }
    assert (HpbmtD' : forall s0, exec (tlb_get_pbmt (upt_entry vpnD ieD)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpnD ieD s0 HpbmtD). }
    (* ---- the physical-side facts at the (frame-form) pa ---- *)
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add paD j) = Some (nth_byte v j)⌝)%I as %HbfD.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcwd j ltac:(lia)) with "Hcode") as "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram paD⌝)%I as %HramD.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcwd 0%nat ltac:(lia)) with "Hcode") as "Hb0".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add paD 7)⌝)%I as %HramD7.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcwd 7%nat ltac:(lia)) with "Hcode") as "Hb7".
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    pose proof (addr_is_ram_not_in_clint _ HramD) as HncD.
    pose proof (addr_is_ram_not_in_sig _ HramD) as HnsD.
    destruct (Hpma_all paD 8) as (regionD & HpmamD & _ & HreadD & _ & _).
    assert (HrangeD : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
              (uint paD) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite Lpmpa1.
      exact (ram_fetch_pmp paD (vec_access_dec pmpaddr00 0) 8 7
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramD HramD7 Hpmp_cov). }
    (* ---- the LOAD execute fact at s1 ---- *)
    assert (HE : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s1
             = Some (RETIRE_SUCCESS,
                     set_reg s1 (R_bitvector_64 (gpr_of_Z (uint rd)))
                       (regval_into_reg (extend_value false
                          (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v))))).
    { apply (exec_execute_LOAD_8_U (upt_entry vpnD ieD) vpnD rs1
               (sign_extend' 64 imm) v regionD s1
               HchkD' HupdD' HpbmtD' (upt_entry_match vpnD ieD)
               Lpriv1
               ltac:(rewrite Lms1; exact HSXL)
               ltac:(rewrite Lms1; exact HMPRV)
               ltac:(rewrite Lms1; exact HMXR)
               HES1 Lsenv1 Lmenv1
               ltac:(rewrite Lsatp1; exact Hsatpmode)
               ltac:(rewrite Lsatp1; exact Hasid)
               ltac:(rewrite Ltlb1; exact HvecD)
               ltac:(fold eaS; rewrite Hea; exact HalignD)
               ltac:(fold eaS; rewrite Hea; exact HcanonD)
               ltac:(fold eaS; rewrite Hea; exact Hvpn_defD)
               ltac:(rewrite Lpmpc1; exact HpmpA)
               ltac:(rewrite Lpmpa1; exact Hpmp_ord)
               ltac:(fold eaS paS; rewrite Hpa; exact HrangeD)
               ltac:(rewrite Lpmpc1; exact HpmpR)
               ltac:(fold eaS paS; rewrite Hpa Lpma1; exact HpmamD)
               ltac:(fold eaS paS; rewrite Hpa; exact HpaalD)
               HreadD
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_clint_false paD 8 s1 HncD ltac:(lia)))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_sig_false paD 8 s1 HnsD ltac:(lia)))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_htif_false paD 8 s1 Lhtif1))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (addr_is_ram_not_dev _ HramD))
               ltac:(fold eaS paS; rewrite Hpa; exact HbfD)
               rd imm Hrd eq_refl). }
    rewrite data2_id in HE.
    (* ---- ghost rd write ---- *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (extend_value false v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (extend_value false v))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s1 (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (extend_value false v))).
    iSplitR; [iPureIntro; exact HE |].
    iSplitL "Hreg Hmem Hdev".
    { unfold s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s1 (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (extend_value false v))).(sregs)
             = add_vec_int va 2).
    { unfold s1, set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg (extend_value false v)]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  Lemma ustep_c_ld_data
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs1 rd : mword 5) (v : mword 64)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (dm : gmap Arch.pa (bv 8))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
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
       = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, false, 8)), s)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 8 = true ->
    dom dm = data ->
    (forall j : nat, (j < 8)%nat ->
       dm !! pa_add paD j = Some (nth_byte v j)) ->
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
    ([∗ map] a ↦ b ∈ dm, a ↦ₘ b) -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hok Hvec Hchk0 HupdN Hpbmt0 HSXL HMPRV HMXR Hcanon
           Hvpn_def Hmode HisRVC Hdec Hexp Hrd HsomeD HvecD HchkD HupdD
           HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hdomdm Hcwd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdm Hcfg Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_c_hit va vpn ie h ii (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg [Hmem Hdev]]".
    destruct Hpins as (Lpriv0 & Lms0 & Lsatp0 & Ltlb0 & Lpmpc0 & Lpmpa0).
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1) s1 with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    set (eaS := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s1.(sregs))
                        (sign_extend' 64 imm)).
    assert (Hea : eaS = eaF) by (unfold eaS, eaF; rewrite Hrv; reflexivity).
    set (paS := u_pa (upt_entry vpnD ieD) eaS vpnD).
    assert (Hpa : paS = paD)
      by (unfold paS, paD; rewrite Hea; reflexivity).
    (* ---- machine-state pins at s1 ---- *)
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa0.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma0.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif0.
    assert (Lpriv1 : register_lookup cur_privilege s1.(sregs) = User)
      by (unfold s1; lk; exact Lpriv0).
    assert (Lms1 : register_lookup mstatus s1.(sregs) = ms_v)
      by (unfold s1; lk; exact Lms0).
    assert (Lsatp1 : register_lookup satp s1.(sregs) = satp0)
      by (unfold s1; lk; exact Lsatp0).
    assert (Ltlb1 : register_lookup tlb s1.(sregs) = tlbvec)
      by (unfold s1; lk; exact Ltlb0).
    assert (Lpmpc1 : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
      by (unfold s1; lk; exact Lpmpc0).
    assert (Lpmpa1 : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
      by (unfold s1; lk; exact Lpmpa0).
    (* the persistent-cell reads above ran AFTER the nextPC tick, so they
       are already s1 facts *)
    assert (Lmisa1 : register_lookup misa s1.(sregs) = misa0) by exact Lmisa0.
    assert (Lpma1 : register_lookup pma_regions s1.(sregs) = pmar0) by exact Lpma0.
    assert (Lhtif1 : register_lookup htif_tohost_base s1.(sregs) = None) by exact Lhtif0.
    assert (HES1 : exec (currentlyEnabled Ext_S) s1 = Some (true, s1)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa1.
      rewrite Hmisa_val0 in HmisaS. rewrite Hmisa_val0. exact HmisaS. }
    assert (Lsenv1 : register_lookup senvcfg s1.(sregs) = mword_of_int 0).
    { unfold s1; lk.
      rewrite (Hag (R_bitvector_64 senvcfg) ltac:(vm_compute; reflexivity)).
      vm_compute; reflexivity. }
    assert (Lmenv1 : register_lookup menvcfg s1.(sregs) = MENVCFG_S).
    { unfold s1; lk.
      rewrite (Hag (R_bitvector_64 menvcfg) ltac:(vm_compute; reflexivity)).
      vm_compute; reflexivity. }
    (* ---- the data-entry leaf facts at Load Data ---- *)
    assert (HchkD' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (Load Data) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpnD ieD)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpnD ieD))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact HchkD. }
    assert (HupdD' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpnD ieD)) (Load Data)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdD. }
    assert (HpbmtD' : forall s0, exec (tlb_get_pbmt (upt_entry vpnD ieD)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpnD ieD s0 HpbmtD). }
    (* ---- the physical-side facts at the (frame-form) pa ---- *)
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add paD j) = Some (nth_byte v j)⌝)%I as %HbfD.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd j ltac:(lia)) with "Hdm")
        as "[Hbj _]".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram paD⌝)%I as %HramD.
    { iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd 0%nat ltac:(lia)) with "Hdm")
        as "[Hb0 _]".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add paD 7)⌝)%I as %HramD7.
    { iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd 7%nat ltac:(lia)) with "Hdm")
        as "[Hb7 _]".
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    pose proof (addr_is_ram_not_in_clint _ HramD) as HncD.
    pose proof (addr_is_ram_not_in_sig _ HramD) as HnsD.
    destruct (Hpma_all paD 8) as (regionD & HpmamD & _ & HreadD & _ & _).
    assert (HrangeD : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
              (uint paD) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite Lpmpa1.
      exact (ram_fetch_pmp paD (vec_access_dec pmpaddr00 0) 8 7
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramD HramD7 Hpmp_cov). }
    (* ---- the LOAD execute fact at s1 ---- *)
    assert (HE : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s1
             = Some (RETIRE_SUCCESS,
                     set_reg s1 (R_bitvector_64 (gpr_of_Z (uint rd)))
                       (regval_into_reg (extend_value false
                          (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v))))).
    { apply (exec_execute_LOAD_8_U (upt_entry vpnD ieD) vpnD rs1
               (sign_extend' 64 imm) v regionD s1
               HchkD' HupdD' HpbmtD' (upt_entry_match vpnD ieD)
               Lpriv1
               ltac:(rewrite Lms1; exact HSXL)
               ltac:(rewrite Lms1; exact HMPRV)
               ltac:(rewrite Lms1; exact HMXR)
               HES1 Lsenv1 Lmenv1
               ltac:(rewrite Lsatp1; exact Hsatpmode)
               ltac:(rewrite Lsatp1; exact Hasid)
               ltac:(rewrite Ltlb1; exact HvecD)
               ltac:(fold eaS; rewrite Hea; exact HalignD)
               ltac:(fold eaS; rewrite Hea; exact HcanonD)
               ltac:(fold eaS; rewrite Hea; exact Hvpn_defD)
               ltac:(rewrite Lpmpc1; exact HpmpA)
               ltac:(rewrite Lpmpa1; exact Hpmp_ord)
               ltac:(fold eaS paS; rewrite Hpa; exact HrangeD)
               ltac:(rewrite Lpmpc1; exact HpmpR)
               ltac:(fold eaS paS; rewrite Hpa Lpma1; exact HpmamD)
               ltac:(fold eaS paS; rewrite Hpa; exact HpaalD)
               HreadD
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_clint_false paD 8 s1 HncD ltac:(lia)))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_sig_false paD 8 s1 HnsD ltac:(lia)))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_htif_false paD 8 s1 Lhtif1))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (addr_is_ram_not_dev _ HramD))
               ltac:(fold eaS paS; rewrite Hpa; exact HbfD)
               rd imm Hrd eq_refl). }
    rewrite data2_id in HE.
    (* ---- ghost rd write ---- *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (extend_value false v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (extend_value false v))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s1 (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (extend_value false v))).
    iSplitR; [iPureIntro; exact HE |].
    iSplitL "Hreg Hmem Hdev".
    { unfold s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s1 (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (extend_value false v))).(sregs)
             = add_vec_int va 2).
    { unfold s1, set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg (extend_value false v)]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitL "Hfmap".
    { iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap". }
    rewrite /user_data. iExists dm. iSplitR; [iPureIntro; exact Hdomdm |].
    iExact "Hdm".
  Qed.

  Lemma ustep_c_sd
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs2 rs1 : mword 5) (vold : mword 64)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    let vNew := (g !!! Regidx rs2) in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
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
       = Some (ExecuteAs (STORE (imm, Regidx rs2, Regidx rs1, 8)), s)) ->
    spec !! vpnD = Some ieD ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 8 = true ->
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
    (* the target window's OLD bytes, owned *)
    ([∗ list] j ∈ seq 0 8, (pa_add paD j) ↦ₘ nth_byte vold j) -∗
    (* rebuilding [user_data] from the NEW window *)
    (([∗ list] j ∈ seq 0 8, (pa_add paD j) ↦ₘ nth_byte vNew j) -∗ user_data) -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD vNew HN Hok Hvec Hchk0 HupdN Hpbmt0 HSXL HMPRV HMXR
           Hcanon Hvpn_def Hmode HisRVC Hdec Hexp HsomeD HvecD HchkD HupdD
           HpbmtD HalignD HcanonD Hvpn_defD HpaalD.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hwin Hrestore Hcfg Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_c_hit va vpn ie h ii (STORE (imm, Regidx rs2, Regidx rs1, 8))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag Hpins) "[Hreg [Hmem Hdev]]".
    destruct Hpins as (Lpriv0 & Lms0 & Lsatp0 & Ltlb0 & Lpmpc0 & Lpmpa0).
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1) s1 with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2) s1 with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    set (eaS := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s1.(sregs))
                        (sign_extend' 64 imm)).
    assert (Hea : eaS = eaF) by (unfold eaS, eaF; rewrite Hrv1; reflexivity).
    set (paS := u_pa (upt_entry vpnD ieD) eaS vpnD).
    assert (Hpa : paS = paD)
      by (unfold paS, paD; rewrite Hea; reflexivity).
    (* ---- machine-state pins at s1 ---- *)
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa0.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma0.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif0.
    assert (Lpriv1 : register_lookup cur_privilege s1.(sregs) = User)
      by (unfold s1; lk; exact Lpriv0).
    assert (Lms1 : register_lookup mstatus s1.(sregs) = ms_v)
      by (unfold s1; lk; exact Lms0).
    assert (Lsatp1 : register_lookup satp s1.(sregs) = satp0)
      by (unfold s1; lk; exact Lsatp0).
    assert (Ltlb1 : register_lookup tlb s1.(sregs) = tlbvec)
      by (unfold s1; lk; exact Ltlb0).
    assert (Lpmpc1 : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
      by (unfold s1; lk; exact Lpmpc0).
    assert (Lpmpa1 : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
      by (unfold s1; lk; exact Lpmpa0).
    assert (HES1 : exec (currentlyEnabled Ext_S) s1 = Some (true, s1)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa0.
      rewrite Hmisa_val0 in HmisaS. rewrite Hmisa_val0. exact HmisaS. }
    assert (Lsenv1 : register_lookup senvcfg s1.(sregs) = mword_of_int 0).
    { unfold s1; lk.
      rewrite (Hag (R_bitvector_64 senvcfg) ltac:(vm_compute; reflexivity)).
      vm_compute; reflexivity. }
    assert (Lmenv1 : register_lookup menvcfg s1.(sregs) = MENVCFG_S).
    { unfold s1; lk.
      rewrite (Hag (R_bitvector_64 menvcfg) ltac:(vm_compute; reflexivity)).
      vm_compute; reflexivity. }
    (* ---- the data-entry leaf facts at Store Data ---- *)
    assert (HchkD' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (Store Data) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpnD ieD)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpnD ieD))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact HchkD. }
    assert (HupdD' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpnD ieD)) (Store Data)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdD. }
    assert (HpbmtD' : forall s0, exec (tlb_get_pbmt (upt_entry vpnD ieD)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpnD ieD s0 HpbmtD). }
    (* ---- RAM-ness of the target window ---- *)
    iAssert (⌜addr_is_ram paD⌝)%I as %HramD.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hwin") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add paD 7)⌝)%I as %HramD7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hwin") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    pose proof (addr_is_ram_not_in_clint _ HramD) as HncD.
    pose proof (addr_is_ram_not_in_sig _ HramD) as HnsD.
    destruct (Hpma_all paD 8) as (regionD & HpmamD & _ & _ & HwriteD & _).
    assert (HrangeD : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
              (uint paD) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite Lpmpa1.
      exact (ram_fetch_pmp paD (vec_access_dec pmpaddr00 0) 8 7
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramD HramD7 Hpmp_cov). }
    (* ---- the STORE execute fact at s1 ---- *)
    assert (HE : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s1
             = Some (RETIRE_SUCCESS,
                     MState s1.(sregs) (write_bytes s1.(mem) paD 8 vNew) s1.(mdev))).
    { pose proof (exec_execute_STORE_8_U (upt_entry vpnD ieD) vpnD rs2 rs1 imm
               regionD s1
               HchkD' HupdD' HpbmtD' (upt_entry_match vpnD ieD)
               Lpriv1
               ltac:(rewrite Lms1; exact HSXL)
               ltac:(rewrite Lms1; exact HMPRV)
               ltac:(rewrite Lms1; exact HMXR)
               HES1 Lsenv1 Lmenv1
               ltac:(rewrite Lsatp1; exact Hsatpmode)
               ltac:(rewrite Lsatp1; exact Hasid)
               ltac:(rewrite Ltlb1; exact HvecD)
               ltac:(fold eaS; rewrite Hea; exact HalignD)
               ltac:(fold eaS; rewrite Hea; exact HcanonD)
               ltac:(fold eaS; rewrite Hea; exact Hvpn_defD)
               ltac:(rewrite Lpmpc1; exact HpmpA)
               ltac:(rewrite Lpmpa1; exact Hpmp_ord)
               ltac:(fold eaS paS; rewrite Hpa; exact HrangeD)
               ltac:(rewrite Lpmpc1; exact HpmpW)
               ltac:(fold eaS paS; rewrite Hpa Lpma0; exact HpmamD)
               ltac:(fold eaS paS; rewrite Hpa; exact HpaalD)
               HwriteD
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_clint_false paD 8 s1 HncD ltac:(lia)))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_sig_false paD 8 s1 HnsD ltac:(lia)))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_htif_writable_false paD 8 s1 Lhtif0))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (addr_is_ram_not_dev _ HramD))) as HE0.
      fold eaS paS in HE0. rewrite Hpa in HE0. rewrite Hrv2 in HE0.
      exact HE0. }
    (* ---- ghost window update in lock-step with write_bytes ---- *)
    iMod (upd_window_8 σ.(mem) paD vNew vold with "Hmem Hwin") as "[Hmem Hwin]".
    iModIntro.
    iExists (MState s1.(sregs) (write_bytes s1.(mem) paD 8 vNew) s1.(mdev)).
    iSplitR; [iPureIntro; exact HE |].
    iSplitL "Hreg Hmem Hdev".
    { rewrite /mstate_interp. cbn [sregs mem mdev].
      unfold s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (MState s1.(sregs) (write_bytes s1.(mem) paD 8 vNew) s1.(mdev)).(sregs)
             = add_vec_int va 2).
    { cbn [sregs]. unfold s1, set_reg; cbn [sregs].
      rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2), g, tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitL "Hfmap"; [iSplitR; [iPureIntro; exact Hdom |]; iExact "Hfmap" |].
    iApply "Hrestore". iExact "Hwin".
  Qed.

  Lemma ustep_c_ld_data_miss
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs1 rd : mword 5) (v : mword 64)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (dm : gmap Arch.pa (bv 8))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
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
       = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, false, 8)), s)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    (* the DATA slot is EMPTY -> the translate walks and fills *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = None ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 8 = true ->
    dom dm = data ->
    (forall j : nat, (j < 8)%nat ->
       dm !! pa_add paD j = Some (nth_byte v j)) ->
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
    ([∗ map] a ↦ b ∈ dm, a ↦ₘ b) -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hok Hvec Hchk0 HupdN Hpbmt0 HSXL HMPRV HMXR Hcanon
           Hvpn_def Hmode HisRVC Hdec Hexp Hrd HsomeD HvecD HchkD HupdD
           HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hdomdm Hcwd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdm Hcfg Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_c_hit_data va vpn ie h ii (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hupt Hcfg").
    iIntros (σ Hpceq Hag Hpins) "Htlbc Hupt [Hreg [Hmem Hdev]]".
    destruct Hpins as (Lpriv0 & Lms0 & Lsatp0 & Ltlb0 & Lpmpc0 & Lpmpa0).
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1) s1 with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    set (eaS := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s1.(sregs))
                        (sign_extend' 64 imm)).
    assert (Hea : eaS = eaF) by (unfold eaS, eaF; rewrite Hrv; reflexivity).
    (* ---- machine-state pins at s1 ---- *)
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa0.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma0.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif0.
    assert (Lpriv1 : register_lookup cur_privilege s1.(sregs) = User)
      by (unfold s1; lk; exact Lpriv0).
    assert (Lms1 : register_lookup mstatus s1.(sregs) = ms_v)
      by (unfold s1; lk; exact Lms0).
    assert (Lsatp1 : register_lookup satp s1.(sregs) = satp0)
      by (unfold s1; lk; exact Lsatp0).
    assert (Ltlb1 : register_lookup tlb s1.(sregs) = tlbvec)
      by (unfold s1; lk; exact Ltlb0).
    assert (Lpmpc1 : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
      by (unfold s1; lk; exact Lpmpc0).
    assert (Lpmpa1 : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
      by (unfold s1; lk; exact Lpmpa0).
    assert (Lmisa1 : register_lookup misa s1.(sregs) = MISA_C)
      by (rewrite Lmisa0; exact Hmisa_val0).
    assert (Lpma1 : register_lookup pma_regions s1.(sregs) = pmar0) by exact Lpma0.
    assert (Lhtif1 : register_lookup htif_tohost_base s1.(sregs) = None) by exact Lhtif0.
    assert (HES1 : exec (currentlyEnabled Ext_S) s1 = Some (true, s1)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa1.
      rewrite Hmisa_val0 in HmisaS. exact HmisaS. }
    assert (Lsenv1 : register_lookup senvcfg s1.(sregs) = mword_of_int 0).
    { unfold s1; lk.
      rewrite (Hag (R_bitvector_64 senvcfg) ltac:(vm_compute; reflexivity)).
      vm_compute; reflexivity. }
    assert (Lmenv1 : register_lookup menvcfg s1.(sregs) = MENVCFG_S).
    { unfold s1; lk.
      rewrite (Hag (R_bitvector_64 menvcfg) ltac:(vm_compute; reflexivity)).
      vm_compute; reflexivity. }
    (* ---- read the DATA PTEs off the owned slots at s1 ---- *)
    iDestruct (upt_walk_read_ptes root slots spec vpnD ieD s1 HsomeD
                 ltac:(rewrite Lpmpc1; exact HpmpA)
                 ltac:(rewrite Lpmpa1; exact Hpmp_ord)
                 ltac:(rewrite Lpmpc1; exact HpmpR)
                 ltac:(rewrite Lpmpa1; exact Hpmp_cov)
                 Hpter
                 with "Hhw [$Hreg $Hmem $Hdev] Hupt")
      as %(Hrd2 & Hrd1 & Hrd0 & _).
    destruct (Hspec vpnD ieD HsomeD) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0D).
    (* ---- physical-side facts about paD, at the PRE state s1 ---- *)
    set (paS := u_walk_pa (uw_pte0 ieD) eaS).
    assert (Hpa : paS = paD)
      by (unfold paS; rewrite Hea; symmetry; exact (u_pa_upt_entry_walk vpnD ieD eaF)).
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               s1.(mem) !! (pa_add paD j) = Some (nth_byte v j)⌝)%I as %HbfD.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd j ltac:(lia)) with "Hdm")
        as "[Hbj _]".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro.
      unfold s1, set_reg; cbn [mem]. exact Hmj. }
    iAssert (⌜addr_is_ram paD⌝)%I as %HramD.
    { iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd 0%nat ltac:(lia)) with "Hdm")
        as "[Hb0 _]".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add paD 7)⌝)%I as %HramD7.
    { iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd 7%nat ltac:(lia)) with "Hdm")
        as "[Hb7 _]".
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    destruct (Hpma_all paD 8) as (regionD & HpmamD & _ & HreadD & _ & _).
    assert (HrangeD : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
              (uint paD) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite Lpmpa1.
      exact (ram_fetch_pmp paD (vec_access_dec pmpaddr00 0) 8 7
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramD HramD7 Hpmp_cov). }
    set (tlbvecD := vec_update_dec (register_lookup tlb s1.(sregs)) (tlb_hash (__id 39) vpnD)
                      (Some (u_walk_entry vpnD (uw_pte2 ieD) (uw_pte1 ieD) (uw_pte0 ieD)
                               (mword_of_int 0)))).
    set (s' := set_reg s1 tlb tlbvecD).
    (* ---- ghost tlb fill s1 -> s' ---- *)
    iMod (reg_update _ tlb _ tlbvecD with "Hreg Htlbc") as "[Hreg Htlbc]".
    (* ---- the LOAD execute fact at s1 (walk form, translate built inside) ---- *)
    assert (HE : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s1
             = Some (RETIRE_SUCCESS,
                     set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                       (regval_into_reg (extend_value false
                          (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v))))).
    { apply (exec_execute_LOAD_8_U_walk vpnD root rs1 rd imm
               (uw_pte2 ieD) (uw_pte1 ieD) (uw_pte0 ieD) v regionD s1 satp0
               Hrd
               H2i H2nl H1i H1nl H0i H0nl HchkD H0N
               Lmisa1 Lpriv1
               ltac:(rewrite Lms1; exact HSXL)
               ltac:(rewrite Lms1; exact HMPRV)
               ltac:(rewrite Lms1; exact HMXR)
               Lsatp1 Hsatpmode Hasid Hroot Lsenv1 Lmenv1 HES1
               ltac:(rewrite Ltlb1; exact HvecD) HupdD
               Hrd2 Hrd1 Hrd0
               ltac:(fold eaS; rewrite Hea; exact HcanonD)
               ltac:(fold eaS; rewrite Hea; exact Hvpn_defD)
               ltac:(fold eaS; rewrite Hea; exact HalignD)
               ltac:(rewrite Lpmpc1; exact HpmpA)
               ltac:(rewrite Lpmpa1; exact Hpmp_ord)
               ltac:(fold eaS paS; rewrite Hpa; exact HrangeD)
               ltac:(rewrite Lpmpc1; exact HpmpR)
               ltac:(fold eaS paS; rewrite Hpa Lpma1; exact HpmamD)
               ltac:(fold eaS paS; rewrite Hpa; exact HpaalD)
               HreadD
               ltac:(fold eaS paS; rewrite Hpa; exact HramD)
               Lhtif1
               ltac:(fold eaS paS; rewrite Hpa; exact HbfD)). }
    rewrite data2_id in HE.
    (* ---- ghost rd write ---- *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (extend_value false v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (extend_value false v))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (extend_value false v))).
    iSplitR; [iPureIntro; exact HE |].
    iSplitL "Hreg Hmem Hdev".
    { unfold s', s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpriv' Hms' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (extend_value false v))).(sregs)
             = add_vec_int va 2).
    { unfold s', s1, set_reg; cbn [sregs].
      tmig. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg (extend_value false v)]> g), tlbvecD.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc Hupt Hcode Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro;
              exact (upt_tlb_ok_fill spec (register_lookup tlb s1.(sregs)) vpnD ieD HsomeD
                       ltac:(rewrite Ltlb1; exact Hok)) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitL "Hfmap".
    { iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap". }
    rewrite /user_data. iExists dm. iSplitR; [iPureIntro; exact Hdomdm |].
    iExact "Hdm".
  Qed.


  Lemma ustep_c_ld_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs1 rd : mword 5) (v : mword 64)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (dm : gmap Arch.pa (bv 8))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
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
       = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, false, 8)), s)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 8 = true ->
    dom dm = data ->
    (forall j : nat, (j < 8)%nat ->
       dm !! pa_add paD j = Some (nth_byte v j)) ->
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
    ([∗ map] a ↦ b ∈ dm, a ↦ₘ b) -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hok Hsome Hchk0 HupdN HSXL HMPRV HMXR Hcanon
           Hvpn_def Hmode HisRVC Hdec Hexp Hrd HsomeD HchkD HupdD
           HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hdomdm Hcwd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdm Hcfg Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_c_data va vpn ie h ii (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
              ms_v tlbvec E Φ HN Hok Hsome Hchk0 HupdN HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hupt Hcfg").
    iIntros (σ Hpceq Hag Hpins) "Htlbc Hupt [Hreg [Hmem Hdev]]".
    destruct Hpins as (Lpriv0 & Lms0 & Lsatp0 & Ltlb0 & Lpmpc0 & Lpmpa0).
    set (tlbvec_f := vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))) in *.
    assert (Hok_f : upt_tlb_ok spec tlbvec_f)
      by exact (upt_tlb_ok_fill spec tlbvec vpn ie Hsome Hok).
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1) s1 with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    set (eaS := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s1.(sregs))
                        (sign_extend' 64 imm)).
    assert (Hea : eaS = eaF) by (unfold eaS, eaF; rewrite Hrv; reflexivity).
    (* ---- machine-state pins at s1 ---- *)
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa0.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma0.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif0.
    assert (Lpriv1 : register_lookup cur_privilege s1.(sregs) = User)
      by (unfold s1; lk; exact Lpriv0).
    assert (Lms1 : register_lookup mstatus s1.(sregs) = ms_v)
      by (unfold s1; lk; exact Lms0).
    assert (Lsatp1 : register_lookup satp s1.(sregs) = satp0)
      by (unfold s1; lk; exact Lsatp0).
    assert (Ltlb1 : register_lookup tlb s1.(sregs) = tlbvec_f)
      by (unfold s1; lk; exact Ltlb0).
    assert (Lpmpc1 : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
      by (unfold s1; lk; exact Lpmpc0).
    assert (Lpmpa1 : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
      by (unfold s1; lk; exact Lpmpa0).
    assert (Lmisa1 : register_lookup misa s1.(sregs) = MISA_C)
      by (rewrite Lmisa0; exact Hmisa_val0).
    assert (Lpma1 : register_lookup pma_regions s1.(sregs) = pmar0) by exact Lpma0.
    assert (Lhtif1 : register_lookup htif_tohost_base s1.(sregs) = None) by exact Lhtif0.
    assert (HES1 : exec (currentlyEnabled Ext_S) s1 = Some (true, s1)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa1.
      rewrite Hmisa_val0 in HmisaS. exact HmisaS. }
    assert (Lsenv1 : register_lookup senvcfg s1.(sregs) = mword_of_int 0).
    { unfold s1; lk.
      rewrite (Hag (R_bitvector_64 senvcfg) ltac:(vm_compute; reflexivity)).
      vm_compute; reflexivity. }
    assert (Lmenv1 : register_lookup menvcfg s1.(sregs) = MENVCFG_S).
    { unfold s1; lk.
      rewrite (Hag (R_bitvector_64 menvcfg) ltac:(vm_compute; reflexivity)).
      vm_compute; reflexivity. }
    destruct (vec_access_dec tlbvec_f (tlb_hash (__id 39) vpnD)) as [entD|] eqn:HvaccD.
    { destruct (match_TLB_Entry entD (mword_of_int 0 : mword 16)
                  (sign_extend' (57 - 12) vpnD)) eqn:HmatchD.
      { (* data HIT *)
        destruct (Hok_f vpnD entD HvaccD) as (vpnD'' & iD & HspecD'' & _ & HentD).
        subst entD.
        pose proof (upt_entry_match_inj vpnD'' vpnD iD HmatchD) as HvvD. subst vpnD''.
        rewrite HsomeD in HspecD''. inversion HspecD''. subst iD.
        assert (HvecD_hit : vec_access_dec tlbvec_f (tlb_hash (__id 39) vpnD)
                            = Some (upt_entry vpnD ieD)) by exact HvaccD.
        set (paS := u_pa (upt_entry vpnD ieD) eaS vpnD).
        assert (Hpa : paS = paD)
          by (unfold paS, paD; rewrite Hea; reflexivity).
    (* ---- the data-entry leaf facts at Load Data ---- *)
    assert (HchkD' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (Load Data) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpnD ieD)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpnD ieD))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact HchkD. }
    assert (HupdD' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpnD ieD)) (Load Data)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdD. }
    assert (HpbmtD' : forall s0, exec (tlb_get_pbmt (upt_entry vpnD ieD)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpnD ieD s0 HpbmtD). }
    (* ---- the physical-side facts at the (frame-form) pa ---- *)
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add paD j) = Some (nth_byte v j)⌝)%I as %HbfD.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd j ltac:(lia)) with "Hdm")
        as "[Hbj _]".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram paD⌝)%I as %HramD.
    { iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd 0%nat ltac:(lia)) with "Hdm")
        as "[Hb0 _]".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add paD 7)⌝)%I as %HramD7.
    { iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd 7%nat ltac:(lia)) with "Hdm")
        as "[Hb7 _]".
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    pose proof (addr_is_ram_not_in_clint _ HramD) as HncD.
    pose proof (addr_is_ram_not_in_sig _ HramD) as HnsD.
    destruct (Hpma_all paD 8) as (regionD & HpmamD & _ & HreadD & _ & _).
    assert (HrangeD : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
              (uint paD) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite Lpmpa1.
      exact (ram_fetch_pmp paD (vec_access_dec pmpaddr00 0) 8 7
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramD HramD7 Hpmp_cov). }
    (* ---- the LOAD execute fact at s1 ---- *)
    assert (HE : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s1
             = Some (RETIRE_SUCCESS,
                     set_reg s1 (R_bitvector_64 (gpr_of_Z (uint rd)))
                       (regval_into_reg (extend_value false
                          (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v))))).
    { apply (exec_execute_LOAD_8_U (upt_entry vpnD ieD) vpnD rs1
               (sign_extend' 64 imm) v regionD s1
               HchkD' HupdD' HpbmtD' (upt_entry_match vpnD ieD)
               Lpriv1
               ltac:(rewrite Lms1; exact HSXL)
               ltac:(rewrite Lms1; exact HMPRV)
               ltac:(rewrite Lms1; exact HMXR)
               HES1 Lsenv1 Lmenv1
               ltac:(rewrite Lsatp1; exact Hsatpmode)
               ltac:(rewrite Lsatp1; exact Hasid)
               ltac:(rewrite Ltlb1; exact HvecD_hit)
               ltac:(fold eaS; rewrite Hea; exact HalignD)
               ltac:(fold eaS; rewrite Hea; exact HcanonD)
               ltac:(fold eaS; rewrite Hea; exact Hvpn_defD)
               ltac:(rewrite Lpmpc1; exact HpmpA)
               ltac:(rewrite Lpmpa1; exact Hpmp_ord)
               ltac:(fold eaS paS; rewrite Hpa; exact HrangeD)
               ltac:(rewrite Lpmpc1; exact HpmpR)
               ltac:(fold eaS paS; rewrite Hpa Lpma1; exact HpmamD)
               ltac:(fold eaS paS; rewrite Hpa; exact HpaalD)
               HreadD
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_clint_false paD 8 s1 HncD ltac:(lia)))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_sig_false paD 8 s1 HnsD ltac:(lia)))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_htif_false paD 8 s1 Lhtif1))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (addr_is_ram_not_dev _ HramD))
               ltac:(fold eaS paS; rewrite Hpa; exact HbfD)
               rd imm Hrd eq_refl). }
    rewrite data2_id in HE.
    (* ---- ghost rd write ---- *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (extend_value false v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (extend_value false v))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s1 (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (extend_value false v))).
    iSplitR; [iPureIntro; exact HE |].
    iSplitL "Hreg Hmem Hdev".
    { unfold s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpriv' Hms' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s1 (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (extend_value false v))).(sregs)
             = add_vec_int va 2).
    { unfold s1, set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg (extend_value false v)]> g), tlbvec_f.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc Hupt Hcode Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok_f |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitL "Hfmap".
    { iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap". }
    rewrite /user_data. iExists dm. iSplitR; [iPureIntro; exact Hdomdm |].
    iExact "Hdm".
      }
      { (* colliding data MISS *)
    (* ---- read the DATA PTEs off the owned slots at s1 ---- *)
    iDestruct (upt_walk_read_ptes root slots spec vpnD ieD s1 HsomeD
                 ltac:(rewrite Lpmpc1; exact HpmpA)
                 ltac:(rewrite Lpmpa1; exact Hpmp_ord)
                 ltac:(rewrite Lpmpc1; exact HpmpR)
                 ltac:(rewrite Lpmpa1; exact Hpmp_cov)
                 Hpter
                 with "Hhw [$Hreg $Hmem $Hdev] Hupt")
      as %(Hrd2 & Hrd1 & Hrd0 & _).
    destruct (Hspec vpnD ieD HsomeD) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0D).
    (* ---- physical-side facts about paD, at the PRE state s1 ---- *)
    set (paS := u_walk_pa (uw_pte0 ieD) eaS).
    assert (Hpa : paS = paD)
      by (unfold paS; rewrite Hea; symmetry; exact (u_pa_upt_entry_walk vpnD ieD eaF)).
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               s1.(mem) !! (pa_add paD j) = Some (nth_byte v j)⌝)%I as %HbfD.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd j ltac:(lia)) with "Hdm")
        as "[Hbj _]".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro.
      unfold s1, set_reg; cbn [mem]. exact Hmj. }
    iAssert (⌜addr_is_ram paD⌝)%I as %HramD.
    { iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd 0%nat ltac:(lia)) with "Hdm")
        as "[Hb0 _]".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add paD 7)⌝)%I as %HramD7.
    { iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd 7%nat ltac:(lia)) with "Hdm")
        as "[Hb7 _]".
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    destruct (Hpma_all paD 8) as (regionD & HpmamD & _ & HreadD & _ & _).
    assert (HrangeD : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
              (uint paD) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite Lpmpa1.
      exact (ram_fetch_pmp paD (vec_access_dec pmpaddr00 0) 8 7
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramD HramD7 Hpmp_cov). }
    set (tlbvecD := vec_update_dec (register_lookup tlb s1.(sregs)) (tlb_hash (__id 39) vpnD)
                      (Some (u_walk_entry vpnD (uw_pte2 ieD) (uw_pte1 ieD) (uw_pte0 ieD)
                               (mword_of_int 0)))).
    set (s' := set_reg s1 tlb tlbvecD).
    (* ---- ghost tlb fill s1 -> s' ---- *)
    iMod (reg_update _ tlb _ tlbvecD with "Hreg Htlbc") as "[Hreg Htlbc]".
    (* ---- the LOAD execute fact at s1 (walk form, translate built inside) ---- *)
    assert (HE : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s1
             = Some (RETIRE_SUCCESS,
                     set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                       (regval_into_reg (extend_value false
                          (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v))))).
    { apply (exec_execute_LOAD_8_U_walk_nomatch vpnD root entD rs1 rd imm
               (uw_pte2 ieD) (uw_pte1 ieD) (uw_pte0 ieD) v regionD s1 satp0
               Hrd
               H2i H2nl H1i H1nl H0i H0nl HchkD H0N
               Lmisa1 Lpriv1
               ltac:(rewrite Lms1; exact HSXL)
               ltac:(rewrite Lms1; exact HMPRV)
               ltac:(rewrite Lms1; exact HMXR)
               Lsatp1 Hsatpmode Hasid Hroot Lsenv1 Lmenv1 HES1
               ltac:(rewrite Ltlb1; exact HvaccD) HmatchD HupdD
               Hrd2 Hrd1 Hrd0
               ltac:(fold eaS; rewrite Hea; exact HcanonD)
               ltac:(fold eaS; rewrite Hea; exact Hvpn_defD)
               ltac:(fold eaS; rewrite Hea; exact HalignD)
               ltac:(rewrite Lpmpc1; exact HpmpA)
               ltac:(rewrite Lpmpa1; exact Hpmp_ord)
               ltac:(fold eaS paS; rewrite Hpa; exact HrangeD)
               ltac:(rewrite Lpmpc1; exact HpmpR)
               ltac:(fold eaS paS; rewrite Hpa Lpma1; exact HpmamD)
               ltac:(fold eaS paS; rewrite Hpa; exact HpaalD)
               HreadD
               ltac:(fold eaS paS; rewrite Hpa; exact HramD)
               Lhtif1
               ltac:(fold eaS paS; rewrite Hpa; exact HbfD)). }
    rewrite data2_id in HE.
    (* ---- ghost rd write ---- *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (extend_value false v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (extend_value false v))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (extend_value false v))).
    iSplitR; [iPureIntro; exact HE |].
    iSplitL "Hreg Hmem Hdev".
    { unfold s', s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpriv' Hms' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (extend_value false v))).(sregs)
             = add_vec_int va 2).
    { unfold s', s1, set_reg; cbn [sregs].
      tmig. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg (extend_value false v)]> g), tlbvecD.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc Hupt Hcode Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro;
              exact (upt_tlb_ok_fill spec (register_lookup tlb s1.(sregs)) vpnD ieD HsomeD
                       ltac:(rewrite Ltlb1; exact Hok_f)) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitL "Hfmap".
    { iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap". }
    rewrite /user_data. iExists dm. iSplitR; [iPureIntro; exact Hdomdm |].
    iExact "Hdm".
      }
    }
    { (* empty data MISS *)
    (* ---- read the DATA PTEs off the owned slots at s1 ---- *)
    iDestruct (upt_walk_read_ptes root slots spec vpnD ieD s1 HsomeD
                 ltac:(rewrite Lpmpc1; exact HpmpA)
                 ltac:(rewrite Lpmpa1; exact Hpmp_ord)
                 ltac:(rewrite Lpmpc1; exact HpmpR)
                 ltac:(rewrite Lpmpa1; exact Hpmp_cov)
                 Hpter
                 with "Hhw [$Hreg $Hmem $Hdev] Hupt")
      as %(Hrd2 & Hrd1 & Hrd0 & _).
    destruct (Hspec vpnD ieD HsomeD) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0D).
    (* ---- physical-side facts about paD, at the PRE state s1 ---- *)
    set (paS := u_walk_pa (uw_pte0 ieD) eaS).
    assert (Hpa : paS = paD)
      by (unfold paS; rewrite Hea; symmetry; exact (u_pa_upt_entry_walk vpnD ieD eaF)).
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               s1.(mem) !! (pa_add paD j) = Some (nth_byte v j)⌝)%I as %HbfD.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd j ltac:(lia)) with "Hdm")
        as "[Hbj _]".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro.
      unfold s1, set_reg; cbn [mem]. exact Hmj. }
    iAssert (⌜addr_is_ram paD⌝)%I as %HramD.
    { iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd 0%nat ltac:(lia)) with "Hdm")
        as "[Hb0 _]".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add paD 7)⌝)%I as %HramD7.
    { iDestruct (big_sepM_lookup_acc (fun a b => (a ↦ₘ b)%I) dm _ _ (Hcwd 7%nat ltac:(lia)) with "Hdm")
        as "[Hb7 _]".
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    destruct (Hpma_all paD 8) as (regionD & HpmamD & _ & HreadD & _ & _).
    assert (HrangeD : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
              (uint paD) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite Lpmpa1.
      exact (ram_fetch_pmp paD (vec_access_dec pmpaddr00 0) 8 7
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramD HramD7 Hpmp_cov). }
    set (tlbvecD := vec_update_dec (register_lookup tlb s1.(sregs)) (tlb_hash (__id 39) vpnD)
                      (Some (u_walk_entry vpnD (uw_pte2 ieD) (uw_pte1 ieD) (uw_pte0 ieD)
                               (mword_of_int 0)))).
    set (s' := set_reg s1 tlb tlbvecD).
    (* ---- ghost tlb fill s1 -> s' ---- *)
    iMod (reg_update _ tlb _ tlbvecD with "Hreg Htlbc") as "[Hreg Htlbc]".
    (* ---- the LOAD execute fact at s1 (walk form, translate built inside) ---- *)
    assert (HE : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s1
             = Some (RETIRE_SUCCESS,
                     set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                       (regval_into_reg (extend_value false
                          (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v))))).
    { apply (exec_execute_LOAD_8_U_walk vpnD root rs1 rd imm
               (uw_pte2 ieD) (uw_pte1 ieD) (uw_pte0 ieD) v regionD s1 satp0
               Hrd
               H2i H2nl H1i H1nl H0i H0nl HchkD H0N
               Lmisa1 Lpriv1
               ltac:(rewrite Lms1; exact HSXL)
               ltac:(rewrite Lms1; exact HMPRV)
               ltac:(rewrite Lms1; exact HMXR)
               Lsatp1 Hsatpmode Hasid Hroot Lsenv1 Lmenv1 HES1
               ltac:(rewrite Ltlb1; exact HvaccD) HupdD
               Hrd2 Hrd1 Hrd0
               ltac:(fold eaS; rewrite Hea; exact HcanonD)
               ltac:(fold eaS; rewrite Hea; exact Hvpn_defD)
               ltac:(fold eaS; rewrite Hea; exact HalignD)
               ltac:(rewrite Lpmpc1; exact HpmpA)
               ltac:(rewrite Lpmpa1; exact Hpmp_ord)
               ltac:(fold eaS paS; rewrite Hpa; exact HrangeD)
               ltac:(rewrite Lpmpc1; exact HpmpR)
               ltac:(fold eaS paS; rewrite Hpa Lpma1; exact HpmamD)
               ltac:(fold eaS paS; rewrite Hpa; exact HpaalD)
               HreadD
               ltac:(fold eaS paS; rewrite Hpa; exact HramD)
               Lhtif1
               ltac:(fold eaS paS; rewrite Hpa; exact HbfD)). }
    rewrite data2_id in HE.
    (* ---- ghost rd write ---- *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (extend_value false v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (extend_value false v))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (extend_value false v))).
    iSplitR; [iPureIntro; exact HE |].
    iSplitL "Hreg Hmem Hdev".
    { unfold s', s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpriv' Hms' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (extend_value false v))).(sregs)
             = add_vec_int va 2).
    { unfold s', s1, set_reg; cbn [sregs].
      tmig. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2),
            (<[Regidx rd := regval_into_reg (extend_value false v)]> g), tlbvecD.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc Hupt Hcode Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro;
              exact (upt_tlb_ok_fill spec (register_lookup tlb s1.(sregs)) vpnD ieD HsomeD
                       ltac:(rewrite Ltlb1; exact Hok_f)) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitL "Hfmap".
    { iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap". }
    rewrite /user_data. iExists dm. iSplitR; [iPureIntro; exact Hdomdm |].
    iExact "Hdm".
    }
  Qed.

  Lemma ustep_c_sd_miss
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs2 rs1 : mword 5) (vold : mword 64)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    let vNew := (g !!! Regidx rs2) in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
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
       = Some (ExecuteAs (STORE (imm, Regidx rs2, Regidx rs1, 8)), s)) ->
    spec !! vpnD = Some ieD ->
    (* the DATA slot is EMPTY -> the translate walks and fills *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = None ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 8 = true ->
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
    (* the target window's OLD bytes, owned *)
    ([∗ list] j ∈ seq 0 8, (pa_add paD j) ↦ₘ nth_byte vold j) -∗
    (* rebuilding [user_data] from the NEW window *)
    (([∗ list] j ∈ seq 0 8, (pa_add paD j) ↦ₘ nth_byte vNew j) -∗ user_data) -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD vNew HN Hok Hvec Hchk0 HupdN Hpbmt0 HSXL HMPRV HMXR
           Hcanon Hvpn_def Hmode HisRVC Hdec Hexp HsomeD HvecD HchkD HupdD
           HpbmtD HalignD HcanonD Hvpn_defD HpaalD.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hwin Hrestore Hcfg Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_c_hit_data va vpn ie h ii (STORE (imm, Regidx rs2, Regidx rs1, 8))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hupt Hcfg").
    iIntros (σ Hpceq Hag Hpins) "Htlbc Hupt [Hreg [Hmem Hdev]]".
    destruct Hpins as (Lpriv0 & Lms0 & Lsatp0 & Ltlb0 & Lpmpc0 & Lpmpa0).
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1) s1 with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2) s1 with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    set (eaS := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s1.(sregs))
                        (sign_extend' 64 imm)).
    assert (Hea : eaS = eaF) by (unfold eaS, eaF; rewrite Hrv1; reflexivity).
    (* ---- machine-state pins at s1 ---- *)
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa0.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma0.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif0.
    assert (Lpriv1 : register_lookup cur_privilege s1.(sregs) = User)
      by (unfold s1; lk; exact Lpriv0).
    assert (Lms1 : register_lookup mstatus s1.(sregs) = ms_v)
      by (unfold s1; lk; exact Lms0).
    assert (Lsatp1 : register_lookup satp s1.(sregs) = satp0)
      by (unfold s1; lk; exact Lsatp0).
    assert (Ltlb1 : register_lookup tlb s1.(sregs) = tlbvec)
      by (unfold s1; lk; exact Ltlb0).
    assert (Lpmpc1 : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
      by (unfold s1; lk; exact Lpmpc0).
    assert (Lpmpa1 : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
      by (unfold s1; lk; exact Lpmpa0).
    assert (Lmisa1 : register_lookup misa s1.(sregs) = MISA_C)
      by (rewrite Lmisa0; exact Hmisa_val0).
    assert (Lpma1 : register_lookup pma_regions s1.(sregs) = pmar0) by exact Lpma0.
    assert (Lhtif1 : register_lookup htif_tohost_base s1.(sregs) = None) by exact Lhtif0.
    assert (HES1 : exec (currentlyEnabled Ext_S) s1 = Some (true, s1)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa1.
      rewrite Hmisa_val0 in HmisaS. exact HmisaS. }
    assert (Lsenv1 : register_lookup senvcfg s1.(sregs) = mword_of_int 0).
    { unfold s1; lk.
      rewrite (Hag (R_bitvector_64 senvcfg) ltac:(vm_compute; reflexivity)).
      vm_compute; reflexivity. }
    assert (Lmenv1 : register_lookup menvcfg s1.(sregs) = MENVCFG_S).
    { unfold s1; lk.
      rewrite (Hag (R_bitvector_64 menvcfg) ltac:(vm_compute; reflexivity)).
      vm_compute; reflexivity. }
    (* ---- read the DATA PTEs off the owned slots at s1 ---- *)
    iDestruct (upt_walk_read_ptes root slots spec vpnD ieD s1 HsomeD
                 ltac:(rewrite Lpmpc1; exact HpmpA)
                 ltac:(rewrite Lpmpa1; exact Hpmp_ord)
                 ltac:(rewrite Lpmpc1; exact HpmpR)
                 ltac:(rewrite Lpmpa1; exact Hpmp_cov)
                 Hpter
                 with "Hhw [$Hreg $Hmem $Hdev] Hupt")
      as %(Hrd2 & Hrd1 & Hrd0 & _).
    destruct (Hspec vpnD ieD HsomeD) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0D).
    (* ---- physical-side facts about paD, at the PRE state s1 ---- *)
    set (paS := u_walk_pa (uw_pte0 ieD) eaS).
    assert (Hpa : paS = paD)
      by (unfold paS; rewrite Hea; symmetry; exact (u_pa_upt_entry_walk vpnD ieD eaF)).
    (* RAM-ness of the target window, from the owned window bytes *)
    iAssert (⌜addr_is_ram paD⌝)%I as %HramD.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hwin") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add paD 7)⌝)%I as %HramD7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hwin") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    destruct (Hpma_all paD 8) as (regionD & HpmamD & _ & _ & HwriteD & _).
    assert (HrangeD : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
              (uint paD) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite Lpmpa1.
      exact (ram_fetch_pmp paD (vec_access_dec pmpaddr00 0) 8 7
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramD HramD7 Hpmp_cov). }
    set (tlbvecD := vec_update_dec (register_lookup tlb s1.(sregs)) (tlb_hash (__id 39) vpnD)
                      (Some (u_walk_entry vpnD (uw_pte2 ieD) (uw_pte1 ieD) (uw_pte0 ieD)
                               (mword_of_int 0)))).
    set (s' := set_reg s1 tlb tlbvecD).
    (* ---- ghost tlb fill s1 -> s' ---- *)
    iMod (reg_update _ tlb _ tlbvecD with "Hreg Htlbc") as "[Hreg Htlbc]".
    (* ---- the STORE execute fact at s1 (walk form, translate built inside) ---- *)
    assert (HE : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s1
             = Some (RETIRE_SUCCESS,
                     MState s'.(sregs) (write_bytes s'.(mem) paD 8 vNew) s'.(mdev))).
    { pose proof (exec_execute_STORE_8_U_walk vpnD root rs2 rs1 imm
               (uw_pte2 ieD) (uw_pte1 ieD) (uw_pte0 ieD) regionD s1 satp0
               H2i H2nl H1i H1nl H0i H0nl HchkD H0N
               Lmisa1 Lpriv1
               ltac:(rewrite Lms1; exact HSXL)
               ltac:(rewrite Lms1; exact HMPRV)
               ltac:(rewrite Lms1; exact HMXR)
               Lsatp1 Hsatpmode Hasid Hroot Lsenv1 Lmenv1 HES1
               ltac:(rewrite Ltlb1; exact HvecD) HupdD
               Hrd2 Hrd1 Hrd0
               ltac:(fold eaS; rewrite Hea; exact HcanonD)
               ltac:(fold eaS; rewrite Hea; exact Hvpn_defD)
               ltac:(fold eaS; rewrite Hea; exact HalignD)
               ltac:(rewrite Lpmpc1; exact HpmpA)
               ltac:(rewrite Lpmpa1; exact Hpmp_ord)
               ltac:(fold eaS paS; rewrite Hpa; exact HrangeD)
               ltac:(rewrite Lpmpc1; exact HpmpW)
               ltac:(fold eaS paS; rewrite Hpa Lpma1; exact HpmamD)
               ltac:(fold eaS paS; rewrite Hpa; exact HpaalD)
               HwriteD
               ltac:(fold eaS paS; rewrite Hpa; exact HramD)
               Lhtif1) as HE0.
      fold eaS paS in HE0. rewrite Hpa in HE0. rewrite Hrv2 in HE0. exact HE0. }
    (* ---- ghost window update in lock-step with write_bytes ---- *)
    iMod (upd_window_8 σ.(mem) paD vNew vold with "Hmem Hwin") as "[Hmem Hwin]".
    iModIntro.
    iExists (MState s'.(sregs) (write_bytes s'.(mem) paD 8 vNew) s'.(mdev)).
    iSplitR; [iPureIntro; exact HE |].
    iSplitL "Hreg Hmem Hdev".
    { rewrite /mstate_interp. cbn [sregs mem mdev].
      unfold s', s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpriv' Hms' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (MState s'.(sregs) (write_bytes s'.(mem) paD 8 vNew) s'.(mdev)).(sregs)
             = add_vec_int va 2).
    { cbn [sregs]. unfold s', s1, set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2), g, tlbvecD.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc Hupt Hcode Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro;
              exact (upt_tlb_ok_fill spec (register_lookup tlb s1.(sregs)) vpnD ieD HsomeD
                       ltac:(rewrite Ltlb1; exact Hok)) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitL "Hfmap"; [iSplitR; [iPureIntro; exact Hdom |]; iExact "Hfmap" |].
    iApply "Hrestore". iExact "Hwin".
  Qed.


  Lemma ustep_c_sd_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16) (ii : instruction)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs2 rs1 : mword 5) (vold : mword 64)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    let vNew := (g !!! Regidx rs2) in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
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
       = Some (ExecuteAs (STORE (imm, Regidx rs2, Regidx rs1, 8)), s)) ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 8 = true ->
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
    (* the target window's OLD bytes, owned *)
    ([∗ list] j ∈ seq 0 8, (pa_add paD j) ↦ₘ nth_byte vold j) -∗
    (* rebuilding [user_data] from the NEW window *)
    (([∗ list] j ∈ seq 0 8, (pa_add paD j) ↦ₘ nth_byte vNew j) -∗ user_data) -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD vNew HN Hok Hsome Hchk0 HupdN HSXL HMPRV HMXR
           Hcanon Hvpn_def Hmode HisRVC Hdec Hexp HsomeD HchkD HupdD
           HpbmtD HalignD HcanonD Hvpn_defD HpaalD.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hwin Hrestore Hcfg Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_c_data va vpn ie h ii (STORE (imm, Regidx rs2, Regidx rs1, 8))
              ms_v tlbvec E Φ HN Hok Hsome Hchk0 HupdN HSXL Hcanon
              Hvpn_def Hmode HisRVC Hdec Hexp
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hupt Hcfg").
    iIntros (σ Hpceq Hag Hpins) "Htlbc Hupt [Hreg [Hmem Hdev]]".
    destruct Hpins as (Lpriv0 & Lms0 & Lsatp0 & Ltlb0 & Lpmpc0 & Lpmpa0).
    set (tlbvec_f := vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))) in *.
    assert (Hok_f : upt_tlb_ok spec tlbvec_f)
      by exact (upt_tlb_ok_fill spec tlbvec vpn ie Hsome Hok).
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1) s1 with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2) s1 with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    set (eaS := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s1.(sregs))
                        (sign_extend' 64 imm)).
    assert (Hea : eaS = eaF) by (unfold eaS, eaF; rewrite Hrv1; reflexivity).
    (* ---- machine-state pins at s1 ---- *)
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa0.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma0.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif0.
    assert (Lpriv1 : register_lookup cur_privilege s1.(sregs) = User)
      by (unfold s1; lk; exact Lpriv0).
    assert (Lms1 : register_lookup mstatus s1.(sregs) = ms_v)
      by (unfold s1; lk; exact Lms0).
    assert (Lsatp1 : register_lookup satp s1.(sregs) = satp0)
      by (unfold s1; lk; exact Lsatp0).
    assert (Ltlb1 : register_lookup tlb s1.(sregs) = tlbvec_f)
      by (unfold s1; lk; exact Ltlb0).
    assert (Lpmpc1 : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
      by (unfold s1; lk; exact Lpmpc0).
    assert (Lpmpa1 : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
      by (unfold s1; lk; exact Lpmpa0).
    assert (Lmisa1 : register_lookup misa s1.(sregs) = MISA_C)
      by (rewrite Lmisa0; exact Hmisa_val0).
    assert (Lpma1 : register_lookup pma_regions s1.(sregs) = pmar0) by exact Lpma0.
    assert (Lhtif1 : register_lookup htif_tohost_base s1.(sregs) = None) by exact Lhtif0.
    assert (HES1 : exec (currentlyEnabled Ext_S) s1 = Some (true, s1)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa1.
      rewrite Hmisa_val0 in HmisaS. exact HmisaS. }
    assert (Lsenv1 : register_lookup senvcfg s1.(sregs) = mword_of_int 0).
    { unfold s1; lk.
      rewrite (Hag (R_bitvector_64 senvcfg) ltac:(vm_compute; reflexivity)).
      vm_compute; reflexivity. }
    assert (Lmenv1 : register_lookup menvcfg s1.(sregs) = MENVCFG_S).
    { unfold s1; lk.
      rewrite (Hag (R_bitvector_64 menvcfg) ltac:(vm_compute; reflexivity)).
      vm_compute; reflexivity. }
    destruct (vec_access_dec tlbvec_f (tlb_hash (__id 39) vpnD)) as [entD|] eqn:HvaccD.
    { destruct (match_TLB_Entry entD (mword_of_int 0 : mword 16)
                  (sign_extend' (57 - 12) vpnD)) eqn:HmatchD.
      { (* data HIT *)
        destruct (Hok_f vpnD entD HvaccD) as (vpnD'' & iD & HspecD'' & _ & HentD).
        subst entD.
        pose proof (upt_entry_match_inj vpnD'' vpnD iD HmatchD) as HvvD. subst vpnD''.
        rewrite HsomeD in HspecD''. inversion HspecD''. subst iD.
        assert (HvecD_hit : vec_access_dec tlbvec_f (tlb_hash (__id 39) vpnD)
                            = Some (upt_entry vpnD ieD)) by exact HvaccD.
        set (paS := u_pa (upt_entry vpnD ieD) eaS vpnD).
        assert (Hpa : paS = paD)
          by (unfold paS, paD; rewrite Hea; reflexivity).
    (* ---- the data-entry leaf facts at Store Data ---- *)
    assert (HchkD' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (Store Data) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpnD ieD)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpnD ieD))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact HchkD. }
    assert (HupdD' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpnD ieD)) (Store Data)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdD. }
    assert (HpbmtD' : forall s0, exec (tlb_get_pbmt (upt_entry vpnD ieD)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpnD ieD s0 HpbmtD). }
    (* ---- RAM-ness of the target window ---- *)
    iAssert (⌜addr_is_ram paD⌝)%I as %HramD.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hwin") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add paD 7)⌝)%I as %HramD7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hwin") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    pose proof (addr_is_ram_not_in_clint _ HramD) as HncD.
    pose proof (addr_is_ram_not_in_sig _ HramD) as HnsD.
    destruct (Hpma_all paD 8) as (regionD & HpmamD & _ & _ & HwriteD & _).
    assert (HrangeD : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
              (uint paD) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite Lpmpa1.
      exact (ram_fetch_pmp paD (vec_access_dec pmpaddr00 0) 8 7
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramD HramD7 Hpmp_cov). }
    (* ---- the STORE execute fact at s1 ---- *)
    assert (HE : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s1
             = Some (RETIRE_SUCCESS,
                     MState s1.(sregs) (write_bytes s1.(mem) paD 8 vNew) s1.(mdev))).
    { pose proof (exec_execute_STORE_8_U (upt_entry vpnD ieD) vpnD rs2 rs1 imm
               regionD s1
               HchkD' HupdD' HpbmtD' (upt_entry_match vpnD ieD)
               Lpriv1
               ltac:(rewrite Lms1; exact HSXL)
               ltac:(rewrite Lms1; exact HMPRV)
               ltac:(rewrite Lms1; exact HMXR)
               HES1 Lsenv1 Lmenv1
               ltac:(rewrite Lsatp1; exact Hsatpmode)
               ltac:(rewrite Lsatp1; exact Hasid)
               ltac:(rewrite Ltlb1; exact HvecD_hit)
               ltac:(fold eaS; rewrite Hea; exact HalignD)
               ltac:(fold eaS; rewrite Hea; exact HcanonD)
               ltac:(fold eaS; rewrite Hea; exact Hvpn_defD)
               ltac:(rewrite Lpmpc1; exact HpmpA)
               ltac:(rewrite Lpmpa1; exact Hpmp_ord)
               ltac:(fold eaS paS; rewrite Hpa; exact HrangeD)
               ltac:(rewrite Lpmpc1; exact HpmpW)
               ltac:(fold eaS paS; rewrite Hpa Lpma0; exact HpmamD)
               ltac:(fold eaS paS; rewrite Hpa; exact HpaalD)
               HwriteD
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_clint_false paD 8 s1 HncD ltac:(lia)))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_sig_false paD 8 s1 HnsD ltac:(lia)))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (within_htif_writable_false paD 8 s1 Lhtif0))
               ltac:(fold eaS paS; rewrite Hpa;
                     exact (addr_is_ram_not_dev _ HramD))) as HE0.
      fold eaS paS in HE0. rewrite Hpa in HE0. rewrite Hrv2 in HE0.
      exact HE0. }
    (* ---- ghost window update in lock-step with write_bytes ---- *)
    iMod (upd_window_8 σ.(mem) paD vNew vold with "Hmem Hwin") as "[Hmem Hwin]".
    iModIntro.
    iExists (MState s1.(sregs) (write_bytes s1.(mem) paD 8 vNew) s1.(mdev)).
    iSplitR; [iPureIntro; exact HE |].
    iSplitL "Hreg Hmem Hdev".
    { rewrite /mstate_interp. cbn [sregs mem mdev].
      unfold s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpriv' Hms' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (MState s1.(sregs) (write_bytes s1.(mem) paD 8 vNew) s1.(mdev)).(sregs)
             = add_vec_int va 2).
    { cbn [sregs]. unfold s1, set_reg; cbn [sregs].
      rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2), g, tlbvec_f.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc Hupt Hcode Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok_f |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitL "Hfmap"; [iSplitR; [iPureIntro; exact Hdom |]; iExact "Hfmap" |].
    iApply "Hrestore". iExact "Hwin".
      }
      { (* colliding data MISS *)
    (* ---- read the DATA PTEs off the owned slots at s1 ---- *)
    iDestruct (upt_walk_read_ptes root slots spec vpnD ieD s1 HsomeD
                 ltac:(rewrite Lpmpc1; exact HpmpA)
                 ltac:(rewrite Lpmpa1; exact Hpmp_ord)
                 ltac:(rewrite Lpmpc1; exact HpmpR)
                 ltac:(rewrite Lpmpa1; exact Hpmp_cov)
                 Hpter
                 with "Hhw [$Hreg $Hmem $Hdev] Hupt")
      as %(Hrd2 & Hrd1 & Hrd0 & _).
    destruct (Hspec vpnD ieD HsomeD) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0D).
    (* ---- physical-side facts about paD, at the PRE state s1 ---- *)
    set (paS := u_walk_pa (uw_pte0 ieD) eaS).
    assert (Hpa : paS = paD)
      by (unfold paS; rewrite Hea; symmetry; exact (u_pa_upt_entry_walk vpnD ieD eaF)).
    (* RAM-ness of the target window, from the owned window bytes *)
    iAssert (⌜addr_is_ram paD⌝)%I as %HramD.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hwin") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add paD 7)⌝)%I as %HramD7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hwin") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    destruct (Hpma_all paD 8) as (regionD & HpmamD & _ & _ & HwriteD & _).
    assert (HrangeD : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
              (uint paD) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite Lpmpa1.
      exact (ram_fetch_pmp paD (vec_access_dec pmpaddr00 0) 8 7
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramD HramD7 Hpmp_cov). }
    set (tlbvecD := vec_update_dec (register_lookup tlb s1.(sregs)) (tlb_hash (__id 39) vpnD)
                      (Some (u_walk_entry vpnD (uw_pte2 ieD) (uw_pte1 ieD) (uw_pte0 ieD)
                               (mword_of_int 0)))).
    set (s' := set_reg s1 tlb tlbvecD).
    (* ---- ghost tlb fill s1 -> s' ---- *)
    iMod (reg_update _ tlb _ tlbvecD with "Hreg Htlbc") as "[Hreg Htlbc]".
    (* ---- the STORE execute fact at s1 (walk form, translate built inside) ---- *)
    assert (HE : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s1
             = Some (RETIRE_SUCCESS,
                     MState s'.(sregs) (write_bytes s'.(mem) paD 8 vNew) s'.(mdev))).
    { pose proof (exec_execute_STORE_8_U_walk_nomatch vpnD root entD rs2 rs1 imm
               (uw_pte2 ieD) (uw_pte1 ieD) (uw_pte0 ieD) regionD s1 satp0
               H2i H2nl H1i H1nl H0i H0nl HchkD H0N
               Lmisa1 Lpriv1
               ltac:(rewrite Lms1; exact HSXL)
               ltac:(rewrite Lms1; exact HMPRV)
               ltac:(rewrite Lms1; exact HMXR)
               Lsatp1 Hsatpmode Hasid Hroot Lsenv1 Lmenv1 HES1
               ltac:(rewrite Ltlb1; exact HvaccD) HmatchD HupdD
               Hrd2 Hrd1 Hrd0
               ltac:(fold eaS; rewrite Hea; exact HcanonD)
               ltac:(fold eaS; rewrite Hea; exact Hvpn_defD)
               ltac:(fold eaS; rewrite Hea; exact HalignD)
               ltac:(rewrite Lpmpc1; exact HpmpA)
               ltac:(rewrite Lpmpa1; exact Hpmp_ord)
               ltac:(fold eaS paS; rewrite Hpa; exact HrangeD)
               ltac:(rewrite Lpmpc1; exact HpmpW)
               ltac:(fold eaS paS; rewrite Hpa Lpma1; exact HpmamD)
               ltac:(fold eaS paS; rewrite Hpa; exact HpaalD)
               HwriteD
               ltac:(fold eaS paS; rewrite Hpa; exact HramD)
               Lhtif1) as HE0.
      fold eaS paS in HE0. rewrite Hpa in HE0. rewrite Hrv2 in HE0. exact HE0. }
    (* ---- ghost window update in lock-step with write_bytes ---- *)
    iMod (upd_window_8 σ.(mem) paD vNew vold with "Hmem Hwin") as "[Hmem Hwin]".
    iModIntro.
    iExists (MState s'.(sregs) (write_bytes s'.(mem) paD 8 vNew) s'.(mdev)).
    iSplitR; [iPureIntro; exact HE |].
    iSplitL "Hreg Hmem Hdev".
    { rewrite /mstate_interp. cbn [sregs mem mdev].
      unfold s', s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpriv' Hms' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (MState s'.(sregs) (write_bytes s'.(mem) paD 8 vNew) s'.(mdev)).(sregs)
             = add_vec_int va 2).
    { cbn [sregs]. unfold s', s1, set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2), g, tlbvecD.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc Hupt Hcode Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro;
              exact (upt_tlb_ok_fill spec (register_lookup tlb s1.(sregs)) vpnD ieD HsomeD
                       ltac:(rewrite Ltlb1; exact Hok_f)) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitL "Hfmap"; [iSplitR; [iPureIntro; exact Hdom |]; iExact "Hfmap" |].
    iApply "Hrestore". iExact "Hwin".
      }
    }
    { (* empty data MISS *)
    (* ---- read the DATA PTEs off the owned slots at s1 ---- *)
    iDestruct (upt_walk_read_ptes root slots spec vpnD ieD s1 HsomeD
                 ltac:(rewrite Lpmpc1; exact HpmpA)
                 ltac:(rewrite Lpmpa1; exact Hpmp_ord)
                 ltac:(rewrite Lpmpc1; exact HpmpR)
                 ltac:(rewrite Lpmpa1; exact Hpmp_cov)
                 Hpter
                 with "Hhw [$Hreg $Hmem $Hdev] Hupt")
      as %(Hrd2 & Hrd1 & Hrd0 & _).
    destruct (Hspec vpnD ieD HsomeD) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0D).
    (* ---- physical-side facts about paD, at the PRE state s1 ---- *)
    set (paS := u_walk_pa (uw_pte0 ieD) eaS).
    assert (Hpa : paS = paD)
      by (unfold paS; rewrite Hea; symmetry; exact (u_pa_upt_entry_walk vpnD ieD eaF)).
    (* RAM-ness of the target window, from the owned window bytes *)
    iAssert (⌜addr_is_ram paD⌝)%I as %HramD.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hwin") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add paD 7)⌝)%I as %HramD7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hwin") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    destruct (Hpma_all paD 8) as (regionD & HpmamD & _ & _ & HwriteD & _).
    assert (HrangeD : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
              (uint paD) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite Lpmpa1.
      exact (ram_fetch_pmp paD (vec_access_dec pmpaddr00 0) 8 7
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramD HramD7 Hpmp_cov). }
    set (tlbvecD := vec_update_dec (register_lookup tlb s1.(sregs)) (tlb_hash (__id 39) vpnD)
                      (Some (u_walk_entry vpnD (uw_pte2 ieD) (uw_pte1 ieD) (uw_pte0 ieD)
                               (mword_of_int 0)))).
    set (s' := set_reg s1 tlb tlbvecD).
    (* ---- ghost tlb fill s1 -> s' ---- *)
    iMod (reg_update _ tlb _ tlbvecD with "Hreg Htlbc") as "[Hreg Htlbc]".
    (* ---- the STORE execute fact at s1 (walk form, translate built inside) ---- *)
    assert (HE : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s1
             = Some (RETIRE_SUCCESS,
                     MState s'.(sregs) (write_bytes s'.(mem) paD 8 vNew) s'.(mdev))).
    { pose proof (exec_execute_STORE_8_U_walk vpnD root rs2 rs1 imm
               (uw_pte2 ieD) (uw_pte1 ieD) (uw_pte0 ieD) regionD s1 satp0
               H2i H2nl H1i H1nl H0i H0nl HchkD H0N
               Lmisa1 Lpriv1
               ltac:(rewrite Lms1; exact HSXL)
               ltac:(rewrite Lms1; exact HMPRV)
               ltac:(rewrite Lms1; exact HMXR)
               Lsatp1 Hsatpmode Hasid Hroot Lsenv1 Lmenv1 HES1
               ltac:(rewrite Ltlb1; exact HvaccD) HupdD
               Hrd2 Hrd1 Hrd0
               ltac:(fold eaS; rewrite Hea; exact HcanonD)
               ltac:(fold eaS; rewrite Hea; exact Hvpn_defD)
               ltac:(fold eaS; rewrite Hea; exact HalignD)
               ltac:(rewrite Lpmpc1; exact HpmpA)
               ltac:(rewrite Lpmpa1; exact Hpmp_ord)
               ltac:(fold eaS paS; rewrite Hpa; exact HrangeD)
               ltac:(rewrite Lpmpc1; exact HpmpW)
               ltac:(fold eaS paS; rewrite Hpa Lpma1; exact HpmamD)
               ltac:(fold eaS paS; rewrite Hpa; exact HpaalD)
               HwriteD
               ltac:(fold eaS paS; rewrite Hpa; exact HramD)
               Lhtif1) as HE0.
      fold eaS paS in HE0. rewrite Hpa in HE0. rewrite Hrv2 in HE0. exact HE0. }
    (* ---- ghost window update in lock-step with write_bytes ---- *)
    iMod (upd_window_8 σ.(mem) paD vNew vold with "Hmem Hwin") as "[Hmem Hwin]".
    iModIntro.
    iExists (MState s'.(sregs) (write_bytes s'.(mem) paD 8 vNew) s'.(mdev)).
    iSplitR; [iPureIntro; exact HE |].
    iSplitL "Hreg Hmem Hdev".
    { rewrite /mstate_interp. cbn [sregs mem mdev].
      unfold s', s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpriv' Hms' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (MState s'.(sregs) (write_bytes s'.(mem) paD 8 vNew) s'.(mdev)).(sregs)
             = add_vec_int va 2).
    { cbn [sregs]. unfold s', s1, set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 2), g, tlbvecD.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc Hupt Hcode Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro;
              exact (upt_tlb_ok_fill spec (register_lookup tlb s1.(sregs)) vpnD ieD HsomeD
                       ltac:(rewrite Ltlb1; exact Hok_f)) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitL "Hfmap"; [iSplitR; [iPureIntro; exact Hdom |]; iExact "Hfmap" |].
    iApply "Hrestore". iExact "Hwin".
    }
  Qed.


End WpUserMemC.
