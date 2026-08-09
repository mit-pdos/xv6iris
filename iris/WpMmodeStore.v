(* M-mode Store leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase. *)
Require Import WpMmodeLeafBase.
Require Import RegFile.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvExec RiscvFetchExec WpGpr InstrBytes RiscvModelBytes RiscvTryStep RiscvExtras SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Import Defs.
Import Defs.

(* from WpGprStore.v *)
Section WpStoreGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* reg_pointsto fractional instances + mmode_config_split_half /
     mmode_config_combine_half now live in InstrBytes.v (shared). *)

  (* [instr]/[mmode_config]-formulated register-generic 8-byte STORE WP -- the
     write-dual of [wp_ld_gpr].  STORE reads TWO sources: rs1 (base address) and
     rs2 (data), each borrowed off [gpr_file] independently (so rs1 = rs2 is
     fine), and WRITES the 8 target bytes from their old contents [vold] to rs2's
     bytes.  The caller supplies the OLD (full-owned) target bytes and the store's
     alignment; the config the translation / PMP checks read is recovered from the
     KEPT half of [mmode_config] + [hw_config].  No register is written ([gpr_file]
     is handed back UNCHANGED). *)
  Lemma wp_store_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rs2 : mword 5)
      (imm : mword 12) (m : regfile) (vold : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    let offset := sign_extend' 64 imm in
    let ea := add_vec (m !!! Regidx rs1) offset in
    (* the 8-byte DATA access needs the stronger all-OFF form: an 8-byte
       window can partially overlap a TOR/NA4 boundary (partial match faults
       even in M-mode), so unlocked-ness alone does not suffice.  The fetch
       side uses [pmp_all_off_allows_all]. *)
    pmp_all_off pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ea ↦ₚ₈ vold -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file m -∗
      ea ↦ₚ₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros offset ea Hpmp Hstat.
    iIntros "Hmm Hpmpc [Hpc Hnpc] Hfile Hinstr Hbw Hcont".
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
               (pma_access_ram _ _ _ Hram_ea Hram_ea7 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl)) as (region & Hmatch & _ & _ & Hwrite & _).
    iApply (wp_instr Φ pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 8)) pmpcfg0
 (pmp_all_off_allows_all _ Hpmp) Hstat with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")   as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms_k")     as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hpmpc_k")   as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg")  as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpma")      as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")     as %Lhtif.
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
    (* read rs1 (base) -- borrow, read, return *)
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 _ s_pc with "Hreg Hr1c") as %Lrs1v.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    (* read rs2 (data) -- independent borrow; rs1 = rs2 is fine *)
    iDestruct (gpr_file_lookup_acc m (Regidx rs2) with "Hfile") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 _ s_pc with "Hreg Hr2c") as %Lrs2v.
    iDestruct ("Hfb2" with "Hr2c") as "Hfile".
    iAssert (⌜addr_is_ram ea⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (phys_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    (* base register at the execute state, uniform over rs1 (x0 -> zero_reg). *)
    assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                    = m !!! Regidx rs1)
      by exact Lrs1v.
    (* data register at the execute state, uniform over rs2 (x0 -> zero_reg). *)
    assert (Hdata : (if Z.eqb (uint rs2) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s_pc.(sregs))
                    = m !!! Regidx rs2)
      by exact Lrs2v.
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
    pose proof (within_htif_writable_false ea 8 s_pc Lhtifp) as Hwh.
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
    pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) ea 8 (m !!! Regidx rs2)) s_pc.(mdev)).
    assert (Hexec_spc :
      exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
      = Some (RETIRE_SUCCESS, s_x)).
    { rewrite (exec_execute_STORE_8_gpr rs2 rs1 imm region s_pc Lprivp
                ltac:(rewrite Lmsp; exact HMPRV) ltac:(rewrite Lsecp; exact Hseccfg1)
                ltac:(rewrite Ha8; unfold is_aligned_vaddr; unfold is_aligned_paddr in Halign; exact Halign)
                ltac:(intro j; rewrite Lpmpcp; exact (proj1 (Hpmp j)))
                ltac:(rewrite Lpmap Hpa; exact Hmatch) ltac:(rewrite Hpa; exact Halign)
                Hwrite ltac:(rewrite Hpa; apply Hwc) ltac:(rewrite Hpa; apply Hws)
                ltac:(rewrite Hpa; apply Hwh)
                ltac:(rewrite Hpa; exact (addr_is_ram_not_dev _ Hrampa))).
      subst s_x. rewrite Hpa Hdata. reflexivity. }
    (* write the 8 target bytes: from [vold] to rs2's value, updating the heap. *)
    iMod (upd_window_8 σ.(mem) ea (m !!! Regidx rs2) vold
            with "Hmem Hbytes") as "[Hmem Hbytes]".
    iModIntro.
    iExists s_x.
    iSplitR.
    { iPureIntro. rewrite Hpceq. exact Hexec_spc. }
    iSplitL "Hreg Hmem Hdev".
    { unfold s_x, s_pc; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem Hdev". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV (conj HSXL HKF))). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iAssert (ea ↦ₚ₈ (m !!! Regidx rs2))%I with "[Hbytes]" as "Hbw".
    { rewrite /phys_word_pointsto. iFrame "Hbytes". iPureIntro. exact Halign. }
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hfile Hbw").
  Qed.
End WpStoreGpr.

(* from WpGprRvcTor.v (RvcTorEngines, store leaves) *)
Section MmodeStoreTor.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_store_gpr_tor (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rs2 : mword 5)
      (imm : mword 12) (m : regfile) (vold : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (q : Qp) :
    let offset := sign_extend' 64 imm in
    let ea := add_vec (m !!! Regidx rs1) offset in
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ea ↦ₚ₈ vold -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file m -∗
      ea ↦ₚ₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros offset ea Hpmp Hstat Htor.
    iIntros "Hmm Hpmpc Hpaddr [Hpc Hnpc] Hfile Hinstr Hbytes Hcont".
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
               (pma_access_ram _ _ _ Hram_ea Hram_ea7 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl)) as (region & Hmatch & _ & _ & Hwrite & _).
    iApply (wp_instr Φ pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 8)) pmpcfg0
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
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 _ s_pc with "Hreg Hr1c") as %Lrs1v.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    iDestruct (gpr_file_lookup_acc m (Regidx rs2) with "Hfile") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 _ s_pc with "Hreg Hr2c") as %Lrs2v.
    iDestruct ("Hfb2" with "Hr2c") as "Hfile".
    iAssert (⌜addr_is_ram ea⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (phys_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                    = m !!! Regidx rs1)
      by exact Lrs1v.
    assert (Hdata : (if Z.eqb (uint rs2) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s_pc.(sregs))
                    = m !!! Regidx rs2)
      by exact Lrs2v.
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
    pose proof (within_htif_writable_false ea 8 s_pc Lhtifp) as Hwh.
    assert (Hpmpchk_ea : exec (pmpCheck (Physaddr ea) 8 (Store Data) Machine) s_pc
                         = Some (None, s_pc)).
    { apply (exec_pmpCheck_machine_tor0 ea 8 (Store Data) s_pc).
      - rewrite Lpmpcp Lpaddrp. exact Htor.
      - intros ent. eexists. apply exec_returnM.
      - vm_compute; reflexivity. }
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
    pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) ea 8 (m !!! Regidx rs2)) s_pc.(mdev)).
    assert (Hexec_spc :
      exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
      = Some (RETIRE_SUCCESS, s_x)).
    { rewrite (exec_execute_STORE_8_gpr_chk rs2 rs1 imm region s_pc Lprivp
                ltac:(rewrite Lmsp; exact HMPRV) ltac:(rewrite Lsecp; exact Hseccfg1)
                ltac:(rewrite Ha8; unfold is_aligned_vaddr; unfold is_aligned_paddr in Halign; exact Halign)
                ltac:(rewrite Hpa; exact Hpmpchk_ea)
                ltac:(rewrite Lpmap Hpa; exact Hmatch) ltac:(rewrite Hpa; exact Halign)
                Hwrite ltac:(rewrite Hpa; apply Hwc) ltac:(rewrite Hpa; apply Hws)
                ltac:(rewrite Hpa; apply Hwh)
                ltac:(rewrite Hpa; exact (addr_is_ram_not_dev _ Hrampa))).
      subst s_x. rewrite Hpa Hdata. reflexivity. }
    iMod (upd_window_8 σ.(mem) ea (m !!! Regidx rs2) vold
            with "Hmem Hbytes") as "[Hmem Hbytes]".
    iModIntro.
    iExists s_x.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact Hexec_spc. }
    iSplitL "Hreg Hmem Hdev".
    { unfold s_x, s_pc; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem Hdev". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV (conj HSXL HKF))). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iAssert (ea ↦ₚ₈ (m !!! Regidx rs2))%I with "[Hbytes]" as "Hbw".
    { rewrite /phys_word_pointsto. iFrame "Hbytes". iPureIntro. exact Halign. }
    iApply ("Hcont" with "Hmm'' Hpmpc'' Hpaddr [$Hpc' $Hnpc] Hfile Hbw").
  Qed.

  (* ---- c.ldsp rd, uimm(sp), TOR-aware ---- *)

  Lemma wp_csdsp_gpr_tor (Φ : mval -> iProp Σ) (pc : mword 64) (uimm : mword 6)
      (rs2 : mword 5) (m : regfile) (vold : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (q : Qp) :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 imm) in
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx csp_rs1, 8)) -∗
    ea ↦ₚ₈ vold -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      ea ↦ₚ₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros imm ea Hpmp Hstat Htor.
    iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hinstr Hbytes Hcont".
    iApply (wp_store_gpr_tor Φ pc true csp_rs1 rs2 imm m vold
              pmpcfg0 pmpaddrs q Hpmp Hstat Htor
              with "Hmm Hpmpc Hpaddr Hpc Hfile Hinstr Hbytes Hcont").
  Qed.

End MmodeStoreTor.
