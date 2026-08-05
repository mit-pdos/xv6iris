(* M-mode Load leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase. *)
Require Import WpMmodeLeafBase.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvExec RiscvFetchExec WpGpr RegFile InstrBytes RiscvModelBytes RiscvTryStep RiscvExtras SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Import Defs.
Import Defs.

(* from WpGprLoad.v *)
Section WpLdGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* reg_pointsto Fractional/AsFractional, reg_pointsto_agree, and
     mmode_config_split_half / mmode_config_combine_half now live in InstrBytes.v
     (next to mmode_config) -- shared by every memory / control-flow WP. *)

  (* [instr]/[mmode_config]-formulated register-generic 8-byte LOAD WP.  The
     caller supplies the loaded bytes ([pa..pa+7] ↦ₘ) and alignment facts; the
     config the load's translation / PMP checks read is recovered from the KEPT
     half of [mmode_config] + [hw_config].  [rs1<>0] (base) / [rd<>0] (dest). *)
  Lemma wp_ld_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5)
      (imm : mword 12) (m : regfile) (v : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) {dq : dfrac} :
    let offset := sign_extend' 64 imm in
    let ea := add_vec (m !!! Regidx rs1) offset in
    (* the 8-byte DATA access needs the stronger all-OFF form: an 8-byte
       window can partially overlap a TOR/NA4 boundary (partial match faults
       even in M-mode), so unlocked-ness alone does not suffice.  The fetch
       side uses [pmp_all_off_allows_all]. *)
    pmp_all_off pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    phys_word_pointsto ea dq v -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      phys_word_pointsto ea dq v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros offset ea Hpmp Hstat Hrd.
    iIntros "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbw Hcont".
    iDestruct (phys_word_pointsto_ram with "Hbw") as %Hram_ea.
    iDestruct (phys_word_pointsto_ram7 with "Hbw") as %Hram_ea7.
    iDestruct "Hbw" as "(%Halign & Hbytes)".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL & %HKF)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    destruct (pma_all_ram Hpma_all ea 8
               (pma_access_ram _ _ _ Hram_ea Hram_ea7 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl)) as (region & Hmatch & _ & Hread & _).
    iApply (wp_instr Φ pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) pmpcfg0
 (pmp_all_off_allows_all _ Hpmp) Hstat with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")   as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms_k")     as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hpmpc_k")   as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg")  as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpma")      as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")     as %Lhtif.
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rs1)) with "Hfmap") as "[Hr1c Hfb1]".
    iEval (rewrite -(rf_lookup m (Regidx rs1))) in "Hr1c".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) σ with "Hreg Hr1c") as %Lrs1v.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
              σ.(mem) !! (pa_add ea j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (phys_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram ea⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (phys_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
    (* base register at the execute state, uniform over rs1 (x0 -> zero_reg). *)
    assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                    = m !!! Regidx rs1).
    { rewrite -Lrs1v. destruct (Z.eqb (uint rs1) 0) eqn:Ez; [reflexivity |].
      unfold s_pc; gpr_trans; reflexivity. }
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsecp : register_lookup mseccfg s_pc.(sregs) = mseccfg0)
      by (unfold s_pc; tmig; exact Lsec).
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmap : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtifp : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    pose proof (within_clint_false ea 8 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false ea 8 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false ea 8 s_pc Lhtifp) as Hwh.
    (* [extend_value false] is the identity here (the value is already 64-bit). *)
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v) = v).
    { unfold extend_value. rewrite sign_extend'_id. apply data2_id. }
    (* [ea]/[pa] the model computes coincide with [ea] once the identity
       zero-extends / +0 are stripped; bridge each PMP/translation goal. *)
    assert (Ha8 : zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0) = ea).
    { rewrite Hbase. rewrite zero_extend'_id. rewrite subrange_id. reflexivity. }
    assert (Hpa : zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0)) (0 * 8)) = ea).
    { rewrite Hbase. rewrite !zero_extend'_id. rewrite subrange_id.
      change (0 * 8) with 0. rewrite avi0. reflexivity. }
    assert (Hexec_spc :
      exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s_pc
      = Some (RETIRE_SUCCESS,
              set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v))).
    { rewrite -Hev.
      apply (exec_execute_LOAD_8_gpr rs1 rd imm v region s_pc Hrd Lprivp).
      - rewrite Lmsp. exact HMPRV.
      - rewrite Lsecp. exact Hseccfg1.
      - rewrite Ha8. unfold is_aligned_vaddr. unfold is_aligned_paddr in Halign. exact Halign.
      - intro j. rewrite Lpmpcp. exact (proj1 (Hpmp j)).
      - rewrite Lpmap Hpa. exact Hmatch.
      - rewrite Hpa. exact Halign.
      - exact Hread.
      - rewrite Hpa. apply Hwc.
      - rewrite Hpa. apply Hws.
      - rewrite Hpa. apply Hwh.
      - rewrite Hpa. exact (addr_is_ram_not_dev _ Hrampa).
      - intros j Hj. rewrite Hpa. exact (Hbytesf j Hj). }
    iDestruct (big_sepM_insert_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rd)) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg v) with "Hreg Hrdc")
      as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]")
      as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iEval (rewrite -rf_to_gmap_upd) in "Hfmap".
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg v)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. exact Hexec_spc. }
    iSplitL "Hreg Hmem Hdev".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem Hdev". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v)).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV (conj HSXL HKF))). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iAssert (phys_word_pointsto ea dq v) with "[Hbytes]" as "Hbw".
    { rewrite /phys_word_pointsto. iFrame "Hbytes". iPureIntro. exact Halign. }
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hbw").
    iSplitR.
    { iPureIntro. intro r. rewrite rf_to_gmap_upd dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

End WpLdGpr.

(* from WpGprRvcTor.v (RvcTorEngines, load leaves) *)
Section MmodeLoadTor.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_ld_gpr_tor (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5)
      (imm : mword 12) (m : regfile) (v : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (q : Qp) {dq : dfrac} :
    let offset := sign_extend' 64 imm in
    let ea := add_vec (m !!! Regidx rs1) offset in
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    ea ↦ₚ₈{ dq } v -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ea ↦ₚ₈{ dq } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros offset ea Hpmp Hstat Htor Hrd.
    iIntros "Hmm Hpmpc Hpaddr [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct (phys_word_pointsto_ram with "Hbytes") as %Hram_ea.
    iDestruct (phys_word_pointsto_ram7 with "Hbytes") as %Hram_ea7.
    iDestruct "Hbytes" as "(%Halign & Hbytes)".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL & %HKF)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    destruct (pma_all_ram Hpma_all ea 8
               (pma_access_ram _ _ _ Hram_ea Hram_ea7 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl)) as (region & Hmatch & _ & Hread & _).
    iApply (wp_instr Φ pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) pmpcfg0
              Hpmp Hstat with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")   as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms_k")     as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hpmpc_k")   as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpaddr")    as %Lpaddr.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg")  as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpma")      as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")     as %Lhtif.
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rs1)) with "Hfmap") as "[Hr1c Hfb1]".
    iEval (rewrite -(rf_lookup m (Regidx rs1))) in "Hr1c".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) σ with "Hreg Hr1c") as %Lrs1v.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
              σ.(mem) !! (pa_add ea j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (phys_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram ea⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (phys_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
    assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                    = m !!! Regidx rs1).
    { rewrite -Lrs1v. destruct (Z.eqb (uint rs1) 0) eqn:Ez; [reflexivity |].
      unfold s_pc; gpr_trans; reflexivity. }
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsecp : register_lookup mseccfg s_pc.(sregs) = mseccfg0)
      by (unfold s_pc; tmig; exact Lsec).
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpaddrp : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddrs)
      by (unfold s_pc; tmig; exact Lpaddr).
    assert (Lpmap : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtifp : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    pose proof (within_clint_false ea 8 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false ea 8 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false ea 8 s_pc Lhtifp) as Hwh.
    (* THE pmpCheck fact at the ticked state, from the TOR-entry-0 predicate. *)
    assert (Hpmpchk_ea : exec (pmpCheck (Physaddr ea) 8 (Load Data) Machine) s_pc
                         = Some (None, s_pc)).
    { apply (exec_pmpCheck_machine_tor0 ea 8 (Load Data) s_pc).
      - rewrite Lpmpcp Lpaddrp. exact Htor.
      - intros ent. eexists. apply exec_returnM.
      - vm_compute; reflexivity. }
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v) = v).
    { unfold extend_value. rewrite sign_extend'_id. apply data2_id. }
    assert (Ha8 : zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0) = ea).
    { rewrite Hbase. rewrite zero_extend'_id. rewrite subrange_id. reflexivity. }
    assert (Hpa : zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0)) (0 * 8)) = ea).
    { rewrite Hbase. rewrite !zero_extend'_id. rewrite subrange_id.
      change (0 * 8) with 0. rewrite avi0. reflexivity. }
    assert (Hexec_spc :
      exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s_pc
      = Some (RETIRE_SUCCESS,
              set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v))).
    { rewrite -Hev.
      apply (exec_execute_LOAD_8_gpr_chk rs1 rd imm v region s_pc Hrd Lprivp).
      - rewrite Lmsp. exact HMPRV.
      - rewrite Lsecp. exact Hseccfg1.
      - rewrite Ha8. unfold is_aligned_vaddr. unfold is_aligned_paddr in Halign. exact Halign.
      - rewrite Hpa. exact Hpmpchk_ea.
      - rewrite Lpmap Hpa. exact Hmatch.
      - rewrite Hpa. exact Halign.
      - exact Hread.
      - rewrite Hpa. apply Hwc.
      - rewrite Hpa. apply Hws.
      - rewrite Hpa. apply Hwh.
      - rewrite Hpa. exact (addr_is_ram_not_dev _ Hrampa).
      - intros j Hj. rewrite Hpa. exact (Hbytesf j Hj). }
    iDestruct (big_sepM_insert_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rd)) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg v) with "Hreg Hrdc")
      as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]")
      as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iEval (rewrite -rf_to_gmap_upd) in "Hfmap".
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg v)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact Hexec_spc. }
    iSplitL "Hreg Hmem Hdev".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem Hdev". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v)).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV (conj HSXL HKF))). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iAssert (ea ↦ₚ₈{ dq } v)%I with "[Hbytes]" as "Hbw".
    { rewrite /phys_word_pointsto. iFrame "Hbytes". iPureIntro. exact Halign. }
    iApply ("Hcont" with "Hmm'' Hpmpc'' Hpaddr [$Hpc' $Hnpc] [Hfmap] Hbw").
    iSplitR.
    { iPureIntro. intro r. rewrite rf_to_gmap_upd dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  Lemma wp_cldsp_gpr_tor (Φ : mval -> iProp Σ) (pc : mword 64) (uimm : mword 6)
      (rd : mword 5) (m : regfile) (v : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (q : Qp) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 imm) in
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (imm, Regidx csp_rs1, Regidx rd, false, 8)) -∗
    ea ↦ₚ₈{ dq } v -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ea ↦ₚ₈{ dq } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros imm ea Hpmp Hstat Htor Hrd.
    iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hinstr Hbytes Hcont".
    iApply (wp_ld_gpr_tor Φ pc true csp_rs1 rd imm m v
              pmpcfg0 pmpaddrs q Hpmp Hstat Htor Hrd
              with "Hmm Hpmpc Hpaddr Hpc Hfile Hinstr Hbytes Hcont").
  Qed.

  (* ---- c.sdsp rs2, uimm(sp), TOR-aware ---- *)
End MmodeLoadTor.
