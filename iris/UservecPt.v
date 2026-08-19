(* UservecPt.v -- the uservec (trap-entry) instruction leaves over
   [utlb_inv_pt]: the STORE mirror of UserretPt.v's [wp_uld_pt], plus the
   two sscratch CSR leaves.

   uservec runs on the TRAMPOLINE page with the USER page table installed,
   so every instruction fetch goes through the user table's trampoline leaf
   (the [wp_instr_u_pt] engine of TrampStepPt.v) and every data access goes
   through the user table's TRAPFRAME leaf -- physical words [tfpa ↦ₚ₈].

   - [wp_usd_pt]   : sd rs2, imm(a0)      (the [wp_uld_pt] mirror)
   - [wp_ucsrw_sscratch_pt] : csrw sscratch, rs1
   - [wp_ucsrr_sscratch_pt] : csrr rd, sscratch

   The store leaf is [WpSmodePtMem.wp_sd_s_r_t]'s proof with
   [UptWalkPt.utf_translate] in place of the regime's data translation and
   the physical trapframe word in place of the claim-carrying one -- the
   mirror of UserretPt's [wp_uld_pt].  The two CSR leaves go through
   [HartSCsr]'s privilege-parametric CSR engines at [Supervisor]. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import ExecCommon WpGpr WpMmodeLeafBase.
Require Import WpGprCsrwCommon WpGprCsrrCommon.
Require Import SmodePte TrampPt.
Require Import SmodeCorePt WpSmodeGpr UptTree.
Require Import PtTree PtAdBits PtTreeAdue.
Require Import SRegime WpSmodePtLeaves WpSmodePtFetch.
Require Import HartLift HartSpan HartSpanChar HartSwp HartSFrame HartSMem.
Require Import WpSmodePtEngine HartSCsr KptGoodb WpDecodeBridge.
Require Import WpMmodeSwpBase WpMmodeCsrSwp WpMmodeJump.
Require Import TrampStepPt UptWalkPt.
Require Import UserretDefs UserretPt.
Require Import RegFile.
Require Import Riscv.rv64d_types Riscv.rv64d.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The S-mode effective-address transform for a STORE.                 *)
(*    (the [exec_transform_effective_address_load_S] twin -- the only     *)
(*    premise of WpSmodePtLeaves' pa-generic width-8 store tower that is  *)
(*    not already supplied by the absorption theorem.)                    *)
(* ===================================================================== *)

(* ===================================================================== *)
(* §2 The TRAPFRAME leaf passes the S-mode STORE permission check on any  *)
(*    A/D variant (PTE_TF = 0xC7 is R|W with U=0), and the user           *)
(*    invariant therefore absorbs a trapframe STORE translation.          *)
(*    (the [tf_variant_check_load]/[utlb_inv_pt_translateAddr_tf_load]    *)
(*    twins of UptTree.v §1/§4.)                                          *)
(* ===================================================================== *)

(* ===================================================================== *)
(* §3 [wp_usd_pt] -- sd rs2, imm(a0) inside uservec: instruction on the    *)
(*    TRAMPOLINE page, data through the user table's TRAPFRAME leaf.       *)
(*    Exactly [wp_uld_pt]'s signature with the load's [rd]/read swapped    *)
(*    for the store's [rs2]/write.                                         *)
(* ===================================================================== *)

Section WpUsdPt.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_usd_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (off immz : Z) (rs2 : mword 5) (is_rvc : bool)
      (m : regfile) (wold : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    let va := uva off in
    let pa := upa off in
    let imm : mword 12 := mword_of_int immz in
    let iva : mword 64 := mword_of_int (TRAPFRAME + immz) in
    let tfpa : mword 64 := zero_extend' 64 (concat_vec tfp
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr iva)) (Z.sub pagesize_bits 1) 0)) in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* GPR: a0 holds TRAPFRAME *)
    m !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME ->
    (* fetch va/pa geometry (vm_compute per instruction) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    svpn_of va = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    svpn_of (add_vec_int va 2) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr va) 4 ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pa 2)) 2 = true ->
    (is_aligned_vaddr (Virtaddr va) 4 = true -> is_aligned_paddr (Physaddr pa) 4 = true) ->
    (* data va geometry (vm_compute per instruction) *)
    add_vec (mword_of_int TRAPFRAME) (sign_extend' 64 imm) = iva ->
    neq_vec (bits_of_virtaddr (Virtaddr iva))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr iva)) (Z.sub 39 1) 0)) = false ->
    svpn_of iva = tf_vpn ->
    is_aligned_vaddr (Virtaddr iva) 8 = true ->
    bv_unsigned (subrange_vec_dec (bits_of_virtaddr (Virtaddr iva)) (Z.sub pagesize_bits 1) 0) `mod` 8 = 0 ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    utlb_inv_pt uroot tfp um -∗
    pc_is va -∗
    gpr_file m -∗
    instr pa is_rvc (STORE (imm, Regidx rs2, Regidx (mword_of_int 10), 8)) -∗
    tfpa ↦ₚ₈ wold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      utlb_inv_pt uroot tfp um -∗
      pc_is (add_vec_int va (if is_rvc then 2 else 4)) -∗
      gpr_file m -∗
      tfpa ↦ₚ₈ (m !!! Regidx rs2 : mword 64) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va pa imm iva tfpa HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Ha0
      Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al
      Heva Hcanond Hvpnd Halignd Hmod8.
    iIntros "#Hhw #Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb
             Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (phys_word_pointsto_ram with "Hbw") as %Hram_tf.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA &
        %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0.
    assert (Hea : add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                    (sign_extend' 64 imm) = iva)
      by (rewrite Ha0; exact Heva).
    assert (Hpalign8 : is_aligned_paddr (Physaddr tfpa) 8 = true)
      by exact (tfcat_aligned8 tfp _ Hmod8).
    iApply (wp_instr_u_pt uroot tfp um va pa is_rvc
              (STORE (imm, Regidx rs2, Regidx (mword_of_int 10), 8))
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 =>
                 (⌜npc = add_vec_int va (if is_rvc then 2 else 4)⌝ ∗
                  ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗ gpr_file m ∗
                  tfpa ↦ₚ₈ (m !!! Regidx rs2 : mword 64))%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr
                    [Hfile Hbw] [Hcont]").
    - iIntros (satp0 pcfg paddr tv') "%Hsok %Hpok
        Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
        Hresv".
      pose proof Hpok as (HA & Hord & HX & HW & HR & Hcov).
      iDestruct (sda_frames_in dq mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'
                   with "Htlbc Hms Hpriv Hmenv Hsatp Hpma Hpcfg Hpaddr Hhtif
                         Hmisa") as "[Hrw Hro]".
      iAssert (upt_res_pt uroot tfp um (register_lookup tlb (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))
        with "[HRes]" as "HRes".
      { rewrite sda_rs_tlb. iExact "HRes". }
      assert (Lmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))
                ('b"0") = true)
        by (rewrite sda_rs_mst; exact HMXR).
      assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM
                (register_lookup menvcfg (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))) = PMM_Disabled)
        by (rewrite sda_rs_menv; exact Hpmm).
      assert (Lsxl : _get_Mstatus_SXL (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')) = 'b"10")
        by (rewrite sda_rs_mst; exact HSXL).
      assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
                (register_lookup satp (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))) = Some Sv39)
        by (rewrite sda_rs_satp; exact (upt_swp_mode_ok uroot satp0 Hsok)).
      assert (Lep : effectivePrivilege (Store Data)
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')) Supervisor = returnM Supervisor)
        by (rewrite sda_rs_mst;
            exact (effectivePrivilege_mprv0 (Store Data) _ Supervisor HMPRV)).
      assert (Lalign : is_aligned_vaddr (Virtaddr
                (add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                   (sign_extend' 64 imm))) 8 = true)
        by (rewrite Hea; exact Halignd).
      assert (Lvpn : svpn_of (add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                       (sign_extend' 64 imm)) = tf_vpn)
        by (rewrite Hea; exact Hvpnd).
      assert (Lcanon : neq_vec (bits_of_virtaddr (Virtaddr
                (add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                   (sign_extend' 64 imm))))
                (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr
                   (add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                      (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false)
        by (rewrite Hea; exact Hcanond).
      assert (Lid : zero_extend' 64 (concat_vec tfp
                (subrange_vec_dec (bits_of_virtaddr (Virtaddr
                   (add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                      (sign_extend' 64 imm)))) (Z.sub pagesize_bits 1) 0)) = tfpa)
        by (rewrite Hea; reflexivity).
      iDestruct "Hresv" as (rr) "Hfrag".
      change (execute (STORE (imm, Regidx rs2, Regidx (mword_of_int 10), 8)))
        with (execute_STORE imm (Regidx rs2) (Regidx (mword_of_int 10)) 8).
      iApply (swp_mono with "[Hmie Hmdl Hclk HPC HnPC] [-]").
      2:{ iApply (swp_execute_STORE_ram_S8 sda_Drw sda_Dro (sda_Df dq) (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                    imm rs2 (mword_of_int 10) m tfpa (m !!! Regidx rs2)
                    pmar0 pcfg paddr
                    (tfpa ↦ₚ₈ (m !!! Regidx rs2 : mword 64))%I
                    (fun rs => upt_res_pt uroot tfp um (register_lookup tlb rs))
                    rr Sv39
                    (store_data8 (m !!! Regidx rs2))
                    sda_disj sda_in_mst sda_in_priv sda_in_menv sda_in_satp
                    sda_in_pma sda_in_pcfg sda_in_paddr sda_in_htif
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_pma _ _ _ _ _ _ _)
                    (sda_rs_pcfg _ _ _ _ _ _ _) (sda_rs_paddr _ _ _ _ _ _ _)
                    (sda_rs_htif _ _ _ _ _ _ _)
                    Lmxr Lpmm Lsxl
                    (hval_transform_effective_address_S_mode
                       (sda_Drw ∪ sda_Dro) sda_Drw (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                          (sign_extend' 64 imm))
                       (Store Data) Sv39
                       sda_in_mst sda_in_priv sda_in_menv sda_in_satp
                       (sda_rs_priv _ _ _ _ _ _ _)
                       Lep eq_refl eq_refl eq_refl Lmxr Lpmm Lsxl Lmd)
                    (hval_translationMode_S_mode (sda_Drw ∪ sda_Dro) sda_Drw
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv') Sv39 sda_in_mst sda_in_satp Lsxl Lmd)
                    Lep HA Hord HW Hcov (pma_all_ram Hpma_all) Hram_tf
                    Lalign Hpalign8
                    with "Hcert Hfrag HRes Hfile Hrw Hro [] [Hbw]").
          - iIntros "Hfrag HRes Hrw Hro".
            iApply (utf_translate (Store Data) sda_Drw sda_Dro (sda_Df dq) (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                      uroot tfp um
                      (add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                         (sign_extend' 64 imm))
                      tfpa satp0 mstatus0 pcfg paddr pmar0 rr
                      (or_intror eq_refl) sda_disj upt_Dr_in_sda upt_Dw_in_sda
                      (sda_rs_misa _ _ _ _ _ _ _)
                      ltac:(rewrite sda_rs_menv; exact Hmenvval0)
                      (sda_rs_htif _ _ _ _ _ _ _)
                      (sda_rs_priv _ _ _ _ _ _ _)
                      (sda_rs_mst _ _ _ _ _ _ _)
                      HSXL HMPRV
                      (sda_rs_satp _ _ _ _ _ _ _)
                      (sda_rs_pcfg _ _ _ _ _ _ _)
                      (sda_rs_paddr _ _ _ _ _ _ _)
                      (sda_rs_pma _ _ _ _ _ _ _)
                      Hsok Hpok Hpma_all Lvpn Lcanon Lid
                      with "Hcert Hfrag HRes Hrw Hro").
          - iIntros (sigma) "Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iMod (phys_word_pointsto_write sigma.(mem) tfpa wold
                    (m !!! Regidx rs2) with "Hmem Hbw") as "[Hmem Hbw]".
            iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver|].
            iModIntro. iNext. iMod "Hclose" as "_". iModIntro.
            iFrame "Hreg Hmem Hdev Hbw". }
      iIntros (e) "(-> & Hfile & Hland)".
      iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & Hword & Hfrag)".
      iAssert (∃ tv2 : type_of_register tlb,
                 hreg_frame (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)
                   sda_Drw ∗
                 hreg_frame_ro (sda_Df dq)
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
                 upt_res_pt uroot tfp um tv2)%I
        with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
      { destruct Hshape as [-> | (tvx & ->)].
        - iExists tv'. iFrame "Hrw Hro".
          iEval (rewrite sda_rs_tlb) in "HRes". iExact "HRes".
        - iExists tvx.
          iDestruct (sda_rw_ext _ _ (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hrw") as "Hrw".
          iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hro") as "Hro".
          iFrame "Hrw Hro".
          iEval (rewrite register_lookup_set) in "HRes". iExact "HRes". }
      iDestruct (sda_frames_out dq mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2
                   with "[$Hrw $Hro]")
        as "(Htlbc & Hms & Hpriv & Hmenv & Hsatp & _ & Hpcfg & Hpaddr & _ & _)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hsatp Hpcfg Hpaddr".
      iSplitL "Htlbc HRes". { iExists tv2. iFrame "Htlbc HRes". }
      iFrame "Hclk".
      iSplitR "Hfrag"; [| by iApply resv_any_intro].
      iExists mstatus0, mdv0, (add_vec_int va (if is_rvc then 2 else 4)).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iFrame "Hfile Hword".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc
         (-> & -> & -> & Hfile & Hword)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile
                            Hword").
  Qed.

End WpUsdPt.

(* ===================================================================== *)
(* §4 sscratch: the S-mode csrw/csrr execute reductions.                  *)
(*    sscratch (0x140) is Ext_S-gated ([is_CSR_accessible] reduces to     *)
(*    [currentlyEnabled Ext_S]) with NO TVM gate and NO legalization --   *)
(*    [write_CSR] writes the value verbatim and reads it straight back.   *)
(* ===================================================================== *)

Definition csr_sscratch : mword 12 := mword_of_int 0x140.

Lemma exec_is_CSR_accessible_sscratch_S (acc : CSRAccessType) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (is_CSR_accessible csr_sscratch Supervisor acc) s = Some (true, s).
Proof.
  intro HS.
  assert (Hred : is_CSR_accessible csr_sscratch Supervisor acc = currentlyEnabled Ext_S)
    by csr_dispatch_eq.
  rewrite Hred.
  rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity.
Qed.

Lemma exec_check_CSR_result_csrw_sscratch_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_sscratch Supervisor CSRWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS.
  apply exec_check_CSR_result_csrw_p. apply exec_check_CSR_csrw_p.
  - assert (H : check_CSR_priv csr_sscratch Supervisor = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - apply exec_is_CSR_accessible_sscratch_S. exact HS.
  - assert (H : stateen_allows_CSR_access csr_sscratch Supervisor CSRWrite = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_check_CSR_result_csrr_sscratch_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_sscratch Supervisor CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS.
  apply exec_check_CSR_result_read_p. apply exec_check_CSR_read_p.
  - assert (H : check_CSR_priv csr_sscratch Supervisor = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - apply exec_is_CSR_accessible_sscratch_S. exact HS.
  - assert (H : stateen_allows_CSR_access csr_sscratch Supervisor CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_write_CSR_sscratch (v : mword 64) s :
  exec (write_CSR csr_sscratch v) s = Some (Ok v, set_reg s sscratch v).
Proof.
  unfold write_CSR.
  skip_csr_false_clauses.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg sscratch v s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sscratch (set_reg s sscratch v))).
  rewrite register_lookup_set. apply exec_returnM.
Qed.

Lemma exec_read_CSR_sscratch s :
  exec (read_CSR csr_sscratch) s = Some (register_lookup sscratch s.(sregs), s).
Proof. drive_csr. exact (exec_read_reg sscratch s). Qed.

Lemma exec_csr_id_write_callback_sscratch (d : mword 64) s :
  exec (csr_id_write_callback csr_sscratch d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_sscratch d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_csr_id_read_callback_sscratch (d : mword 64) s :
  exec (csr_id_read_callback csr_sscratch d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_sscratch d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

(* the two node-level reductions the swp walk needs: [write_CSR]/[read_CSR]
   at the sscratch literal, driven through the model's if-chain. *)
Lemma write_CSR_sscratch_red (v : mword 64) :
  write_CSR csr_sscratch v
  = (Defs.bind0 (Defs.write_reg sscratch v)
       (Defs.bind (Defs.read_reg sscratch)
          (fun w : mword 64 => returnM (Ok w)))
     : M (result (mword 64) unit)).
Proof. unfold write_CSR, csr_sscratch. drive_csr_term. reflexivity. Qed.

Lemma read_CSR_sscratch_red :
  read_CSR csr_sscratch = (Defs.read_reg sscratch : M (mword 64)).
Proof. unfold csr_sscratch. drive_csr_term. reflexivity. Qed.

(* csrw sscratch,rs1 in S-mode: sscratch := rs1's value (no legalization). *)
Lemma exec_execute_csrw_sscratch_S (rs1 : mword 5) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute (CSRReg (csr_sscratch, Regidx rs1, zreg, CSRRW))) s
    = Some (RETIRE_SUCCESS,
            set_reg s sscratch
              (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))).
Proof.
  intros Hpriv HS.
  change (execute (CSRReg (csr_sscratch, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_sscratch (Regidx rs1) zreg CSRRW).
  apply (exec_execute_csrw_gpr_p Supervisor csr_sscratch rs1 s _
           (if Z.eqb (uint rs1) 0 then zero_reg
            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))).
  - exact Hpriv.
  - apply exec_check_CSR_result_csrw_sscratch_S. exact HS.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_sscratch.
  - apply exec_csr_id_write_callback_sscratch.
Qed.

(* csrr rd,sscratch (= csrrs rd,sscratch,x0) in S-mode. *)
Lemma exec_execute_csrr_sscratch_S (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute (CSRReg (csr_sscratch, zreg, Regidx rd, CSRRS))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (register_lookup sscratch s.(sregs)))).
Proof.
  intros Hrd Hpriv HS.
  change (execute (CSRReg (csr_sscratch, zreg, Regidx rd, CSRRS)))
    with (execute_CSRReg csr_sscratch zreg (Regidx rd) CSRRS).
  apply (csrr_read_step_p Supervisor csr_sscratch rd
           (register_lookup sscratch s.(sregs)) s _ Hpriv).
  - apply exec_check_CSR_result_csrr_sscratch_S. exact HS.
  - vm_compute; reflexivity.
  - apply exec_read_CSR_sscratch.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_sscratch.
  - rewrite (exec_wX_bits_gpr rd (register_lookup sscratch s.(sregs)) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ===================================================================== *)
(* §5 The two sscratch CSR leaves over the uservec trampoline engine.     *)
(*    Same shape as [wp_ualu_pt] (no data access), with the sscratch cell *)
(*    threaded as an extra resource.                                      *)
(* ===================================================================== *)

Section WpUCsrPt.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_ucsrw_sscratch_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (off : Z) (is_rvc : bool) (rs1 : mword 5)
      (m : regfile) (sscr0 : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    let va := uva off in
    let pa := upa off in
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch va/pa geometry (vm_compute per instruction) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    svpn_of va = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    svpn_of (add_vec_int va 2) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr va) 4 ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pa 2)) 2 = true ->
    (is_aligned_vaddr (Virtaddr va) 4 = true -> is_aligned_paddr (Physaddr pa) 4 = true) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sscratch ↦ᵣ sscr0 -∗
    utlb_inv_pt uroot tfp um -∗
    pc_is va -∗
    gpr_file m -∗
    instr pa is_rvc (CSRReg (csr_sscratch, Regidx rs1, zreg, CSRRW)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sscratch ↦ᵣ (m !!! Regidx rs1 : mword 64) -∗
      utlb_inv_pt uroot tfp um -∗
      pc_is (add_vec_int va (if is_rvc then 2 else 4)) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va pa HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
      Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al.
    assert (Hfresh : cw_fresh (R_bitvector_64 sscratch))
      by (split_and!; vm_compute; reflexivity).
    iIntros "#Hhw #Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb
             Hpc Hfile Hinstr Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA &
        %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0 mseccfg0.
    iApply (wp_instr_u_pt uroot tfp um va pa is_rvc
              (CSRReg (csr_sscratch, Regidx rs1, zreg, CSRRW))
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 =>
                 (⌜npc = add_vec_int va (if is_rvc then 2 else 4)⌝ ∗
                  ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗ gpr_file m ∗
                  sscratch ↦ᵣ (m !!! Regidx rs1 : mword 64))%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr
                    [Hfile Hsscr] [Hcont]").
    - iIntros (satp0 pcfg paddr tv') "%Hsok %Hpok
        Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
        Hresv".
      iDestruct (pw_frames_in Supervisor dq (R_bitvector_64 sscratch) sscr0
                   Hfresh with "Hsscr Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      change (execute (CSRReg (csr_sscratch, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_sscratch (Regidx rs1) zreg CSRRW).
      iApply (swp_mono with "[Hms Hmie Hmdl Hmenv Hclk Hsatp Hpcfg Hpaddr Htlbc
                              HRes Hresv HPC HnPC] [Hrw Hro Hfile]").
      2:{ iApply (swp_execute_CSRReg_w_p (cw_Drw (R_bitvector_64 sscratch))
                    cw_Dro (cw_Df dq)
                    (pw_rs Supervisor (R_bitvector_64 sscratch) sscr0)
                    (pw_rs Supervisor (R_bitvector_64 sscratch)
                       (m !!! Regidx rs1)) m csr_sscratch Supervisor rs1
                    (m !!! Regidx rs1)
                    (cw_disj _ Hfresh) (cw_in_priv _)
                    (pw_rs_priv Supervisor (R_bitvector_64 sscratch) sscr0
                       Hfresh)
                    ltac:(by vm_compute)
                    (hval_check_CSR_result_S _ _ _ csr_sscratch CSRWrite
                       (cw_in_priv _) (cw_in_sec _) (cw_in_misa _)
                       (pw_rs_priv Supervisor (R_bitvector_64 sscratch) sscr0
                          Hfresh)
                       (pw_rs_sec Supervisor (R_bitvector_64 sscratch) sscr0
                          Hfresh)
                       (pw_rs_misa Supervisor (R_bitvector_64 sscratch) sscr0
                          Hfresh)
                       ltac:(by vm_compute)
                       (exec_check_CSR_result_csrw_sscratch_S dstateS
                          ltac:(by vm_compute)))
                    ltac:(by vm_compute) ltac:(by vm_compute)
                    ltac:(by vm_compute)
                    with "Hcert Hfile Hrw Hro [ ]").
          iIntros "Hrw Hro". rewrite write_CSR_sscratch_red.
          iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
          { iApply (swp_write_reg_owned (cw_Drw (R_bitvector_64 sscratch))
                      cw_Dro (cw_Df dq) _ (R_bitvector_64 sscratch)
                      (m !!! Regidx rs1) (cw_disj _ Hfresh) (cw_w_r _)
                      with "Hcert Hrw Hro"). }
          iIntros (u) "[Hrw Hro]".
          pose proof (pw_set_agree Supervisor (R_bitvector_64 sscratch) sscr0
                        (m !!! Regidx rs1) Hfresh) as Hset.
          iDestruct (cw_rw_ext (R_bitvector_64 sscratch) _ _
                       (reg_agree_mono (cw_Drw (R_bitvector_64 sscratch) ∪ cw_Dro)
                          (cw_Drw (R_bitvector_64 sscratch)) _ _
                          ltac:(set_solver) Hset) with "Hrw") as "Hrw".
          iDestruct (cw_ro_ext dq _ _
                       (reg_agree_mono (cw_Drw (R_bitvector_64 sscratch) ∪ cw_Dro)
                          cw_Dro _ _ ltac:(set_solver) Hset)
                       with "Hro") as "Hro".
          iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
          { iApply (swp_read_reg_pinned (cw_Drw (R_bitvector_64 sscratch))
                      cw_Dro (cw_Df dq) _ (R_bitvector_64 sscratch)
                      (cw_disj _ Hfresh) (cw_in_r _) with "Hcert Hrw Hro"). }
          iIntros (w) "(-> & Hrw & Hro)". rewrite pw_rs_r.
          iApply swp_ret. iSplitR; [done|]. iFrame. }
      iIntros (e) "(-> & Hfile & Hrw & Hro)".
      iDestruct (pw_frames_out Supervisor dq (R_bitvector_64 sscratch)
                   (m !!! Regidx rs1) Hfresh with "[$Hrw $Hro]")
        as "(Hsscr & Hpriv & _ & _)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hsatp Hpcfg Hpaddr".
      iSplitL "Htlbc HRes". { iExists tv'. iFrame "Htlbc HRes". }
      iFrame "Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists mstatus0, mdv0, (add_vec_int va (if is_rvc then 2 else 4)).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iFrame "Hfile Hsscr".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc
         (-> & -> & -> & Hfile & Hsscr)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb Hpc
                            Hfile").
  Qed.

  Lemma wp_ucsrr_sscratch_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (off : Z) (is_rvc : bool) (rd : mword 5)
      (m : regfile) (sv : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq dqs : dfrac} :
    let va := uva off in
    let pa := upa off in
    uint rd <> 0 ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch va/pa geometry (vm_compute per instruction) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    svpn_of va = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    svpn_of (add_vec_int va 2) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr va) 4 ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pa 2)) 2 = true ->
    (is_aligned_vaddr (Virtaddr va) 4 = true -> is_aligned_paddr (Physaddr pa) 4 = true) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sscratch ↦ᵣ{ dqs } sv -∗
    utlb_inv_pt uroot tfp um -∗
    pc_is va -∗
    gpr_file m -∗
    instr pa is_rvc (CSRReg (csr_sscratch, zreg, Regidx rd, CSRRS)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sscratch ↦ᵣ{ dqs } sv -∗
      utlb_inv_pt uroot tfp um -∗
      pc_is (add_vec_int va (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg sv]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va pa Hrd HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
      Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al.
    assert (Hfresh : cw_fresh (R_bitvector_64 sscratch))
      by (split_and!; vm_compute; reflexivity).
    iIntros "#Hhw #Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb
             Hpc Hfile Hinstr Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA &
        %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0 mseccfg0.
    iApply (wp_instr_u_pt uroot tfp um va pa is_rvc
              (CSRReg (csr_sscratch, zreg, Regidx rd, CSRRS))
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 =>
                 (⌜npc = add_vec_int va (if is_rvc then 2 else 4)⌝ ∗
                  ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗
                  gpr_file (<[Regidx rd := regval_into_reg sv]> m) ∗
                  sscratch ↦ᵣ{ dqs } sv)%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr
                    [Hfile Hsscr] [Hcont]").
    - iIntros (satp0 pcfg paddr tv') "%Hsok %Hpok
        Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
        Hresv".
      iDestruct (pr_frames_in Supervisor dq dqs (R_bitvector_64 sscratch) sv
                   Hfresh with "Hsscr Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      change (execute (CSRReg (csr_sscratch, zreg, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_sscratch zreg (Regidx rd) CSRRS).
      iApply (swp_mono with "[Hms Hmie Hmdl Hmenv Hclk Hsatp Hpcfg Hpaddr Htlbc
                              HRes Hresv HPC HnPC] [Hrw Hro Hfile]").
      2:{ iApply (swp_execute_CSRReg_r_p ∅ (cr_Dro (R_bitvector_64 sscratch))
                    (cr_Df dq dqs (R_bitvector_64 sscratch))
                    (pw_rs Supervisor (R_bitvector_64 sscratch) sv) m
                    csr_sscratch Supervisor rd sv
                    ltac:(set_solver) (cr_in_priv _)
                    (pw_rs_priv Supervisor (R_bitvector_64 sscratch) sv Hfresh)
                    Hrd
                    ltac:(by vm_compute)
                    (hval_check_CSR_result_S _ _ _ csr_sscratch CSRRead
                       (cr_in_priv _) (cr_in_sec _) (cr_in_misa _)
                       (pw_rs_priv Supervisor (R_bitvector_64 sscratch) sv
                          Hfresh)
                       (pw_rs_sec Supervisor (R_bitvector_64 sscratch) sv
                          Hfresh)
                       (pw_rs_misa Supervisor (R_bitvector_64 sscratch) sv
                          Hfresh)
                       ltac:(by vm_compute)
                       (exec_check_CSR_result_csrr_sscratch_S dstateS
                          ltac:(by vm_compute)))
                    ltac:(by vm_compute) ltac:(by vm_compute)
                    ltac:(intro x; by vm_compute)
                    with "Hcert Hfile Hrw Hro [ ]").
          iIntros "Hrw Hro". rewrite read_CSR_sscratch_red.
          iApply (swp_mono with "[] [-]");
            [| iApply (swp_read_reg_pinned ∅
                         (cr_Dro (R_bitvector_64 sscratch))
                         (cr_Df dq dqs (R_bitvector_64 sscratch)) _
                         (R_bitvector_64 sscratch)
                         ltac:(set_solver) (cr_in_r _)
                         with "Hcert Hrw Hro") ].
          iIntros (w) "(-> & Hrw & Hro)". rewrite pw_rs_r. by iFrame. }
      iIntros (e) "(-> & Hfile & Hrw & Hro)".
      iDestruct (pr_frames_out Supervisor dq dqs (R_bitvector_64 sscratch) sv
                   Hfresh with "Hro") as "(Hsscr & Hpriv & _ & _)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hsatp Hpcfg Hpaddr".
      iSplitL "Htlbc HRes". { iExists tv'. iFrame "Htlbc HRes". }
      iFrame "Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists mstatus0, mdv0, (add_vec_int va (if is_rvc then 2 else 4)).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iFrame "Hfile Hsscr".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc
         (-> & -> & -> & Hfile & Hsscr)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb Hpc
                            Hfile").
  Qed.

End WpUCsrPt.
