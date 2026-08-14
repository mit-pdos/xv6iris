(* UservecExitPt.v -- the uservec PAGE-TABLE SWITCH back to the KERNEL
   table over the pt2 window (TransPt.v), plus the final jump into
   usertrap:

       sfence.vma x0,x0   @ uva 0x8e
       csrw satp, t1      @ uva 0x92   (t1 holds the KERNEL satp)
       sfence.vma x0,x0   @ uva 0x96
       c.jalr t0          @ uva 0x9a   (ra := uva 0x9c ; pc := t0 & ~1)

   This is the EXACT mirror of [wp_userret_entry_pt] (UserretEntryPt.v)
   with the two tables' roles swapped -- the same three-step window
   machinery -- extended with the compressed jalr.  The KERNEL side is
   SHARED throughout (KptShare.kpt_inv, TransPt.v's [_kcur] family):
   nothing about the kernel table is threaded in or out of this lemma's
   own premises/postcondition, only the ambient persistent [kpt_inv kroot].

     step 1 (USER invariant): the sfence flushes the TLB; the user
       invariant re-seals with [tlb_ok_pt_empty].
     step 2 (USER invariant): the csrw installs the kernel root; the
       user invariant DISSOLVES into the two-table window invariant
       [tlb_inv_pt2_kcur] ([tlb_inv_pt2_kcur_enter]) -- the kernel side
       comes from [kpt_inv] alone (a fresh snapshot, no ownership), every
       resident TLB entry is user-provenance.
     step 3 (window invariant): the fetch is absorbed by [tlb_inv_pt2_kcur]
       (the trampoline page is mapped by BOTH tables at the same pa; a
       kernel-provenance hit may Svadu-write-back through [kpt_inv],
       opened for the span of this one call); the sfence flushes the TLB
       and the window EXITS ([tlb_inv_pt2_kcur_exit]): the USER table
       parks as [pt_frame] and the kernel side folds back into
       [tlb_res_pt] -- nothing is resealed into an exclusive invariant.
     step 4 (SHARED kernel table): the compressed jalr links [ra] and
       jumps to [ret_pc t0], fetched through [tlb_res_pt] like any other
       ordinary kernel trampoline step.                                  *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile.
Require Import ExecCommon WpDecode WpGpr WpGprCsrwB.
Require Import SmodePte PtTree.
Require Import KMap KptExecMap.
Require Import KptTree UptTree.
Require Import TrampStepPt TransPt KptShare.
Require Import UserretDefs.
Require Import Riscv.rv64d_types Riscv.rv64d.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Local execute helpers for the compressed jalr (the LINKING form:       *)
(* rd = ra <> 0, so the JALR writes the link register).  The non-linking  *)
(* [exec_execute_JALR_ret_zca] lives in WpSmodePtCtl.v but is [Local].    *)
(* ===================================================================== *)

Local Lemma uve_cE_zicfilp_false_S s :
  register_lookup cur_privilege (sregs s) = Supervisor ->
  bool_bit_backwards (_get_MEnvcfg_LPE (register_lookup menvcfg s.(sregs))) = false ->
  exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s).
Proof.
  intros Hpriv Hlpe.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _
            (exec_rec_cE_Zicsr_any (currentlyEnabled_measure Ext_Zicfilp - 1) _ s
               ltac:(vm_compute; reflexivity))).
  cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicfilp s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  match goal with |- context[_rec_get_xLPE Supervisor _ ?acc] => destruct acc end.
  cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp - 1) 0) with true by (vm_compute; reflexivity).
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn match.
  rewrite Hlpe. apply exec_returnM.
Qed.

(* the LINKING jalr: rd <> 0, so [wX] stores the (already-ticked) nextPC
   into rd on top of the jump's nextPC write. *)
Local Lemma exec_execute_JALR_link_zca (imm : mword 12) (rs1 rdz : mword 5) s :
  uint rs1 <> 0 -> uint rdz <> 0 ->
  exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s) ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  eq_vec (access_vec_dec (update_vec_dec
     (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
              (sign_extend' 64 imm)) 0 ('b"0")) 0) ('b"0") = true ->
  exec (execute_JALR imm (Regidx rs1) (Regidx rdz)) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC (update_vec_dec
                     (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                              (sign_extend' 64 imm)) 0 ('b"0")))
                  (R_bitvector_64 (gpr_of_Z (uint rdz)))
                  (regval_into_reg (register_lookup nextPC s.(sregs)))).
Proof.
  intros Hrs1 Hrdz Hzic Hzca Halign.
  unfold execute_JALR.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.bind0 (update_elp_state (Regidx rs1)) (get_next_pc tt)) s
                 = Some (register_lookup nextPC s.(sregs), s))).
  2:{ rewrite (exec_bind0_Some _ _ _ _ _
                (_ : exec (update_elp_state (Regidx rs1)) s = Some (tt, s))).
      2:{ unfold update_elp_state. rewrite (exec_bind_Some _ _ _ _ _ Hzic). cbn match.
          apply exec_returnm. }
      unfold get_next_pc. exact (exec_read_reg nextPC s). }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _
            (exec_wX_bits_gpr rdz (register_lookup nextPC s.(sregs))
                (set_reg s nextPC (update_vec_dec
                   (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                            (sign_extend' 64 imm)) 0 ('b"0"))))).
  replace (Z.eqb (uint rdz) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrdz).
  cbn match. apply exec_returnm.
Qed.

Section UservecExitPt.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_uservec_exit_pt (kroot uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64))
      (m : regfile) (ksatp : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    (* S-mode config *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    eq_vec (_get_Mstatus_TVM mstatus0) ('b"1") = false ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    upt_map_wf um ->
    (* t1 holds the KERNEL satp value *)
    m !!! Regidx (mword_of_int 6) = ksatp ->
    _get_Satp64_Mode (Mk_Satp64 ksatp) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) ksatp : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) ksatp : mword 64)) = kroot ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    (* the trampoline claim: the KERNEL table maps the trampoline page, so
       the post-switch fetches go through it *)
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    utlb_inv_pt uroot tfp um -∗
    kpt_inv kroot -∗
    pc_is (uva 0x8e) -∗
    gpr_file m -∗
    instr (upa 0x8e) false ai_sfence -∗
    instr (upa 0x92) false (CSRReg (csr_satp, Regidx (mword_of_int 6 : mword 5), zreg, CSRRW)) -∗
    instr (upa 0x96) false ai_sfence -∗
    instr (upa 0x9a) true (JALR (zeros' 12, Regidx (mword_of_int 5 : mword 5), ra)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pt_frame (upt_tree_spec uroot tfp um) -∗
      (* STEP 4's own [tlb_res_pt kroot] -- KEPT, not [iClear]ed: a chained
         caller that goes on to userret's own entry switch needs it as
         ITS precondition (see SpecUserret.v's own header). *)
      tlb_res_pt kroot -∗
      pc_is (ret_pc (m !!! Regidx (mword_of_int 5))) -∗
      gpr_file (<[Regidx (mword_of_int 1) := regval_into_reg (uva 0x9c)]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL HTVM Hmm HPBMTE Hmenvval0 Hwf Ht1 HkMode Hkasid Hkppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv #Hclaim Hutlb #Hkinv [Hpc Hnpc]
             Hfmap Hi1 Hi2 Hi3 Hi4 Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    assert (Hva01 : add_vec_int (uva 0x8e) 4 = uva 0x92)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hva02 : add_vec_int (uva 0x92) 4 = uva 0x96)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hva03 : add_vec_int (uva 0x96) 4 = uva 0x9a)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hva04 : add_vec_int (uva 0x9a) 2 = uva 0x9c)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ============ STEP 1: sfence.vma under the USER invariant ========== *)
    iApply (wp_instr_u_pt uroot tfp um (uva 0x8e) (upa 0x8e) false ai_sfence
              mstatus0 mie_v mdv0 menvcfg0 dq
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hx4; first [ vm_compute in Hx4; discriminate | vm_compute; reflexivity ])
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hi1").
    iIntros (σ1 Hpceq1) "Hpriv Hms Hmie Hmdl Hmenv Hutlb Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv1.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms1.
    iMod (reg_update _ nextPC _ (uva 0x92) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc1 := set_reg σ1 nextPC (uva 0x92)).
    assert (Lpriv1p : register_lookup cur_privilege s_pc1.(sregs) = Supervisor)
      by (unfold s_pc1; tmig; exact Lpriv1).
    assert (Lms1p : register_lookup mstatus s_pc1.(sregs) = mstatus0)
      by (unfold s_pc1; tmig; exact Lms1).
    destruct (exec_execute_SFENCE_VMA_S s_pc1 Lpriv1p
                ltac:(rewrite Lms1p; exact HTVM)) as (tlbz1 & Hex1 & Hnone1).
    (* flush the user invariant's TLB cell and re-seal with the empty vector *)
    iDestruct "Hutlb" as (usatp1 tlbvec1 ut1)
      "(Hsatp & %HuMode1 & %Huasid1 & %Huppn1 & Htlb & %Hoku1 & %Hspecu1 & %Hwfu1 & %Hpmaw1 & Hut & Hpmp)".
    iMod (reg_update _ tlb _ tlbz1 with "Hreg Htlb") as "[Hreg Htlb]".
    iDestruct (utlb_inv_pt_intro uroot tfp um usatp1 tlbz1 ut1 HuMode1 Huasid1 Huppn1
                 (tlb_ok_pt_empty (mword_of_int 0) ut1 tlbz1
                    (fun vpn' => Hnone1 _ (tlb_hash_range vpn')))
                 Hspecu1 Hwfu1 Hpmaw1 with "Hsatp Htlb Hut Hpmp") as "Hutlb".
    iModIntro.
    iExists (set_reg s_pc1 tlb tlbz1).
    iSplitR.
    { iPureIntro. rewrite Hpceq1. rewrite Hva01. fold s_pc1.
      change ai_sfence with (SFENCE_VMA (zreg, zreg)). exact Hex1. }
    iSplitL "Hreg Hmem".
    { unfold s_pc1; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc".
    assert (Lnpc1 : register_lookup nextPC (set_reg s_pc1 tlb tlbz1).(sregs) = uva 0x92).
    { unfold s_pc1; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc1) in "Hpc".
    iNext.
    (* ============ STEP 2: csrw satp,t1 -- ENTER the window ============= *)
    iApply (wp_instr_u_pt uroot tfp um (uva 0x92) (upa 0x92) false
              (CSRReg (csr_satp, Regidx (mword_of_int 6 : mword 5), zreg, CSRRW))
              mstatus0 mie_v mdv0 menvcfg0 dq
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hx4; first [ vm_compute in Hx4; discriminate | vm_compute; reflexivity ])
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hi2").
    iIntros (σ2 Hpceq2) "Hpriv Hms Hmie Hmdl Hmenv Hutlb Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv2.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms2.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa2.
    iMod (reg_update _ nextPC _ (uva 0x96) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc2 := set_reg σ2 nextPC (uva 0x96)).
    assert (Lpriv2p : register_lookup cur_privilege s_pc2.(sregs) = Supervisor)
      by (unfold s_pc2; tmig; exact Lpriv2).
    assert (Lms2p : register_lookup mstatus s_pc2.(sregs) = mstatus0)
      by (unfold s_pc2; tmig; exact Lms2).
    assert (Lmisa2p : register_lookup misa s_pc2.(sregs) = misa0)
      by (unfold s_pc2; tmig; exact Lmisa2).
    (* t1's value at the executing state *)
    iDestruct (gpr_file_lookup_acc m (Regidx (mword_of_int 6 : mword 5)) with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value (mword_of_int 6) (m (Regidx (mword_of_int 6 : mword 5))) s_pc2
                 with "Hreg Hspc") as %Lva2.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    replace (Z.eqb (uint (mword_of_int 6 : mword 5)) 0) with false in Lva2
      by (vm_compute; reflexivity).
    rewrite -rf_lookup Ht1 in Lva2.
    pose proof (exec_execute_csrw_satp_S (mword_of_int 6) s_pc2
                  ltac:(vm_compute; lia) Lpriv2p
                  ltac:(rewrite Lms2p; exact HTVM)
                  ltac:(rewrite Lmisa2p; exact HmisaS)
                  ltac:(rewrite Lms2p; exact HSXL)) as Hex2.
    rewrite Lva2 in Hex2.
    rewrite (satp_legalized_sv39 (register_lookup satp s_pc2.(sregs)) ksatp HkMode) in Hex2.
    (* dissolve the USER invariant into the two-table window; the KERNEL
       side is now sourced from the ambient [kpt_inv], not a parked
       [kpt_frame] -- no [kmap_at_lookup] against a mapping auth needed
       here at all *)
    iDestruct "Hutlb" as (usatp2 tlbvec2 ut2)
      "(Hsatp & %HuMode2 & %Huasid2 & %Huppn2 & Htlb & %Hoku2 & %Hspecu2 & %Hwfu2 & %Hpmaw2 & Hut & Hpmp)".
    iMod (reg_update _ satp _ ksatp with "Hreg Hsatp") as "[Hreg Hsatp]".
    iMod (tlb_inv_pt2_kcur_enter kroot (upt_tree_spec uroot tfp um) (⊤ ∖ ↑minstretN)
             ksatp tlbvec2 ut2 ltac:(solve_ndisj) HkMode Hkasid Hkppn Hoku2 Hspecu2 Hpmaw2
             with "Hsatp Htlb Hut [Hpmp] Hkinv") as "Hpt2".
    { iApply (pmp_config_reindex uroot kroot with "Hpmp"). }
    iModIntro.
    iExists (set_reg s_pc2 satp ksatp).
    iSplitR.
    { iPureIntro. rewrite Hpceq2. rewrite Hva02. fold s_pc2. exact Hex2. }
    iSplitL "Hreg Hmem".
    { unfold s_pc2; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc".
    assert (Lnpc2 : register_lookup nextPC (set_reg s_pc2 satp ksatp).(sregs) = uva 0x96).
    { unfold s_pc2; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc2) in "Hpc".
    iNext.
    (* ============ STEP 3: sfence.vma -- EXIT into the kernel invariant = *)
    iApply (wp_instr_pt2_tramp_kcur kroot (upt_tree_spec uroot tfp um)
              (upt_pt2_tramp_spec uroot tfp um Hwf)
              (uva 0x96) (upa 0x96) false ai_sfence
              mstatus0 mie_v mdv0 menvcfg0 dq
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hx4; first [ vm_compute in Hx4; discriminate | vm_compute; reflexivity ])
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv [$Hclaim $Hpt2] Hpc Hi3").
    iIntros (σ3 Hpceq3) "Hpriv Hms Hmie Hmdl Hmenv Hpt2b Hsi".
    iDestruct "Hpt2b" as "[_ Hpt2]".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv3.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms3.
    iMod (reg_update _ nextPC _ (uva 0x9a) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc3 := set_reg σ3 nextPC (uva 0x9a)).
    assert (Lpriv3p : register_lookup cur_privilege s_pc3.(sregs) = Supervisor)
      by (unfold s_pc3; tmig; exact Lpriv3).
    assert (Lms3p : register_lookup mstatus s_pc3.(sregs) = mstatus0)
      by (unfold s_pc3; tmig; exact Lms3).
    destruct (exec_execute_SFENCE_VMA_S s_pc3 Lpriv3p
                ltac:(rewrite Lms3p; exact HTVM)) as (tlbz3 & Hex3 & Hnone3).
    (* exit the window: the user table parks; the kernel side hands back
       nothing but the persistent snapshot -- [kpt_inv] was never checked
       out, so there is nothing to reseal into the exclusive [tlb_inv_pt].
       Fold the empty-TLB fact straight into a fresh [tlb_res_pt] instead,
       which is what STEP 4's kernel trampoline step now runs against. *)
    iDestruct (tlb_inv_pt2_kcur_exit with "Hpt2") as (ksatp3 tlbvec3 tc0)
      "(Hsatp & %HkMode3 & %Hkasid3 & %Hkppn3 & Htlb & Hpmp & Hlb0 & Hkinv3 & Hufr)".
    iMod (reg_update _ tlb _ tlbz3 with "Hreg Htlb") as "[Hreg Htlb]".
    iDestruct (tlb_res_pt_intro kroot ksatp3 tlbz3 tc0 HkMode3 Hkasid3 Hkppn3
                 (tlb_ok_pt_empty (mword_of_int 0) tc0 tlbz3
                    (fun vpn' => Hnone3 _ (tlb_hash_range vpn')))
                 with "Hsatp Htlb Hlb0 Hpmp Hkinv3") as "Hkres".
    iModIntro.
    iExists (set_reg s_pc3 tlb tlbz3).
    iSplitR.
    { iPureIntro. rewrite Hpceq3. rewrite Hva03. fold s_pc3.
      change ai_sfence with (SFENCE_VMA (zreg, zreg)). exact Hex3. }
    iSplitL "Hreg Hmem".
    { unfold s_pc3; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc".
    assert (Lnpc3 : register_lookup nextPC (set_reg s_pc3 tlb tlbz3).(sregs) = uva 0x9a).
    { unfold s_pc3; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc3) in "Hpc".
    iNext.
    (* ============ STEP 4: c.jalr t0 under the SHARED kernel table ====== *)
    iApply (wp_instr_ktramp_pt_share kroot (uva 0x9a) (upa 0x9a) true
              (JALR (zeros' 12, Regidx (mword_of_int 5 : mword 5), ra))
              mstatus0 mie_v mdv0 menvcfg0 dq
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hx4; first [ vm_compute in Hx4; discriminate | vm_compute; reflexivity ])
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv [$Hclaim $Hkres] Hpc Hi4").
    iIntros (σ4 Hpceq4) "Hpriv Hms Hmie Hmdl Hmenv Hkres Hsi".
    iDestruct "Hkres" as "[_ Hkres]".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv4.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv4.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa4.
    iMod (reg_update _ nextPC _ (uva 0x9c) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc4 := set_reg σ4 nextPC (uva 0x9c)).
    assert (Lpriv4p : register_lookup cur_privilege s_pc4.(sregs) = Supervisor)
      by (unfold s_pc4; tmig; exact Lpriv4).
    assert (Lmenv4p : register_lookup menvcfg s_pc4.(sregs) = menvcfg0)
      by (unfold s_pc4; tmig; exact Lmenv4).
    assert (Lmisa4p : register_lookup misa s_pc4.(sregs) = misa0)
      by (unfold s_pc4; tmig; exact Lmisa4).
    assert (Lnpc4v : register_lookup nextPC s_pc4.(sregs) = uva 0x9c)
      by (unfold s_pc4; rewrite ?sregs_set_reg; rewrite register_lookup_set; reflexivity).
    assert (Hzic : exec (currentlyEnabled Ext_Zicfilp) s_pc4 = Some (false, s_pc4)).
    { apply uve_cE_zicfilp_false_S; [ exact Lpriv4p |].
      rewrite Lmenv4p Hmenvval0. vm_compute; reflexivity. }
    assert (Hzca : exec (currentlyEnabled Ext_Zca) s_pc4 = Some (true, s_pc4)).
    { apply exec_currentlyEnabled_Zca. rewrite Lmisa4p. exact HmisaC. }
    (* t0's value at the executing state *)
    iDestruct (gpr_file_lookup_acc m (Regidx (mword_of_int 5 : mword 5)) with "Hfmap") as "[Ht0 Hfb2]".
    iDestruct (gpr_pt_value (mword_of_int 5) (m (Regidx (mword_of_int 5 : mword 5))) s_pc4
                 with "Hreg Ht0") as %Lt0.
    iDestruct ("Hfb2" with "Ht0") as "Hfmap".
    replace (Z.eqb (uint (mword_of_int 5 : mword 5)) 0) with false in Lt0
      by (vm_compute; reflexivity).
    rewrite -rf_lookup in Lt0.
    set (tgt := ret_pc (m !!! Regidx (mword_of_int 5))).
    assert (Htgt : update_vec_dec (add_vec
              (register_lookup (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 5 : mword 5)))) s_pc4.(sregs))
              (sign_extend' 64 (zeros' 12))) 0 ('b"0") = tgt)
      by (rewrite Lt0; apply ret_pc_jalr).
    assert (Hra1 : ra = Regidx (mword_of_int 1 : mword 5))
      by (unfold ra; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Hrd1 : uint (mword_of_int 1 : mword 5) <> 0) by (vm_compute; lia).
    (* nextPC := tgt ; ra := uva 0x9c *)
    iMod (reg_update _ nextPC _ tgt with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (gpr_file_insert_acc m (Regidx (mword_of_int 1 : mword 5))
                 (regval_into_reg (uva 0x9c)) with "Hfmap") as "[Hrac Hfins]".
    rewrite (gpr_pt_nz (mword_of_int 1) _ Hrd1).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 1 : mword 5)))) _
            (regval_into_reg (uva 0x9c)) with "Hreg Hrac") as "[Hreg Hrac]".
    iDestruct ("Hfins" with "[Hrac]") as "Hfmap".
    { rewrite (gpr_pt_nz (mword_of_int 1) _ Hrd1). iExact "Hrac". }
    iModIntro.
    iExists (set_reg (set_reg s_pc4 nextPC tgt)
               (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 1 : mword 5))))
               (regval_into_reg (uva 0x9c))).
    iSplitR.
    { iPureIntro. rewrite Hpceq4. rewrite Hva04. fold s_pc4.
      rewrite Hra1.
      change (execute (JALR (zeros' 12, Regidx (mword_of_int 5 : mword 5),
                             Regidx (mword_of_int 1 : mword 5))))
        with (execute_JALR (zeros' 12) (Regidx (mword_of_int 5 : mword 5))
                (Regidx (mword_of_int 1 : mword 5))).
      rewrite -Lnpc4v. rewrite -Htgt.
      apply (exec_execute_JALR_link_zca (zeros' 12) (mword_of_int 5) (mword_of_int 1) s_pc4
               ltac:(vm_compute; lia) Hrd1 Hzic Hzca).
      rewrite Htgt. unfold tgt. apply ret_pc_aligned. }
    iSplitL "Hreg Hmem".
    { unfold s_pc4; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc".
    assert (Lnpc4 : register_lookup nextPC
              (set_reg (set_reg s_pc4 nextPC tgt)
                 (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 1 : mword 5))))
                 (regval_into_reg (uva 0x9c))).(sregs) = tgt).
    { cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc4) in "Hpc".
    iNext.
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hufr Hkres
                          [$Hpc $Hnpc] Hfmap").
  Qed.

End UservecExitPt.
