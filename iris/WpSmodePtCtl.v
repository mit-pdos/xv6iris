(* S-mode control-flow / CSR / fence / sret leaf lemmas over the generalized
   page-table invariant [tlb_inv_pt] (ptree abstraction, Svadu/ADUE).
   Ports of the WpSmodeFence/Jal/Jalr/Csr/Sret leaves. *)
From Stdlib Require Import ZArith Lia List FunctionalExtensionality.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes WpDecode ExecCommon WpGpr WpGprCsrwCommon.
Require Import SRegime.
Require Import SmodeCore WpMmodeLeafBase.
Require Import WpSmodeSret MstatusBits.
Require Import KptTree SmodeCorePt.
Require Import RegFile.
Import Defs.

(* helper: exec_execute_JAL_gpr_zca *)
Local Lemma exec_execute_JAL_gpr_zca (imm : mword 21) (rd : mword 5) s :
  uint rd <> 0 ->
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (execute_JAL imm (Regidx rd)) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (register_lookup nextPC s.(sregs)))).
Proof.
  intros Hrd Halign Hzca.
  unfold execute_JAL, get_next_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
  cbn match.
  match goal with |- context[Defs.bind0 ?wx _] =>
    assert (Hwx : exec wx (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  = Some (tt, set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                                (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (register_lookup nextPC s.(sregs)))))
  end.
  { rewrite (exec_wX_bits_gpr rd (register_lookup nextPC s.(sregs)) _).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hwx).
  apply exec_returnm.
Qed.

(* ---- Local helpers copied from WpSmodeJalr.v ---- *)
Local Lemma exec_cE_zicfilp_false_S s :
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

(* helper: exec_jump_to_zca *)
Local Lemma exec_jump_to_zca (target : mword 64) s :
    eq_vec (access_vec_dec target 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (jump_to target) s = Some (RETIRE_SUCCESS, set_reg s nextPC target).
  Proof.
    intros Halign Hzca.
    unfold jump_to. rewrite exec_catch_early_return.
    change (ext_control_check_pc target) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ unfold Defs.bind0.
        erewrite execR_bind_Some.
        2:{ erewrite execR_bind_Some.
            2:{ apply execR_returnR_fwd. }
            rewrite execR_liftR. unfold assert_exp. rewrite Halign. cbn match.
            rewrite exec_returnm. reflexivity. }
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ (bit_to_bool (access_vec_dec target 1)) s).
        2:{ apply execR_returnR_fwd. }
        destruct (bit_to_bool (access_vec_dec target 1)).
        - cbv iota beta.
          rewrite (execR_bind_Some _ _ _ true s).
          2:{ rewrite execR_liftR. rewrite Hzca. reflexivity. }
          cbv iota beta. apply execR_returnR_fwd.
        - cbv iota beta. apply execR_returnR_fwd. }
    cbv iota beta.
    unfold Defs.bind0.
    rewrite (execR_bind_Some _ _ _ tt (set_reg s nextPC target)).
    2:{ rewrite execR_liftR. rewrite exec_set_next_pc. reflexivity. }
    rewrite (execR_returnR_fwd RETIRE_SUCCESS (set_reg s nextPC target)).
    reflexivity.
  Qed.

(* helper: exec_execute_JALR_ret_zca *)
Local Lemma exec_execute_JALR_ret_zca (imm : mword 12) (rs1 rdz : mword 5) s :
    uint rs1 <> 0 -> uint rdz = 0 ->
    exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s) ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    eq_vec (access_vec_dec (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0")) 0) ('b"0") = true ->
    exec (execute_JALR imm (Regidx rs1) (Regidx rdz)) s
    = Some (RETIRE_SUCCESS,
            set_reg s nextPC (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0"))).
  Proof.
    intros Hrs1 Hrdz Hzic Hzca Halign.
    unfold execute_JALR.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.bind0 (update_elp_state (Regidx rs1)) (get_next_pc tt)) s
                   = Some (register_lookup nextPC s.(sregs), s))).
    2:{ rewrite (exec_bind0_Some _ _ _ _ _
                  (_ : exec (update_elp_state (Regidx rs1)) s = Some (tt, s))).
        2:{ unfold update_elp_state. rewrite (exec_bind_Some _ _ _ _ _ Hzic). cbn match. apply exec_returnm. }
        unfold get_next_pc. exact (exec_read_reg nextPC s). }
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
    replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
    cbn match.
    rewrite (exec_bind0_Some _ _ _ _ _
              (exec_wX_bits_gpr rdz (register_lookup nextPC s.(sregs))
                  (set_reg s nextPC (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0"))))).
    rewrite Hrdz. cbn match. apply exec_returnm.
  Qed.


(* ---- Local helpers copied from WpSmodeCsr.v ---- *)

(* helper: exec_csr_id_write_callback_sstatus *)

(* helper: exec_hartSupports_H *)

(* helper: exec_hartSupports_Sv32 *)

(* helper: exec_have_nominal_privLevel *)

(* helper: exec_lowest_supported_privLevel *)

(* helper: exec_read_CSR_sstatus *)

(* helper: exec_virtual_memory_supported *)

(* helper: register_set_bv64_id *)

(* helper: exec_currentlyEnabled_H_false *)

(* helper: exec_legalize_mstatus *)

(* helper: exec_legalize_sstatus *)

(* helper: exec_write_CSR_sstatus *)

(* helper: exec_check_CSR_priv_sstatus_S *)

(* helper: exec_check_CSR_sstatus_S *)

(* helper: exec_check_CSR_result_sstatus_S *)

(* helper: exec_execute_csrr_sstatus *)

(* helper: exec_execute_csrrci_sstatus *)


(* pure FENCE helpers (relocated from the deleted WpSmodeFence.v) *)
Lemma exec_sail_barrier (b : Arch.barrier) s :
  exec (sail_barrier b) s = Some (tt, s).
Proof. reflexivity. Qed.

Lemma exec_is_fiom_active_S (menvcfg0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  exec (is_fiom_active tt) s
    = Some (eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1"), s).
Proof.
  intros Hcp Hmenv. unfold is_fiom_active.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)).
  rewrite Hmenv. apply exec_returnM.
Qed.


Lemma exec_execute_FENCE_rw_w (menvcfg0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
  exec (execute (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4,
                        Regidx (mword_of_int 0), Regidx (mword_of_int 0)))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intros Hcp Hmenv Hfiom.
  change (execute (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4,
                          Regidx (mword_of_int 0), Regidx (mword_of_int 0))))
    with (execute_FENCE (mword_of_int 0) (mword_of_int 3) (mword_of_int 1)
            (Regidx (mword_of_int 0)) (Regidx (mword_of_int 0))).
  unfold execute_FENCE.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_fiom_active_S menvcfg0 s Hcp Hmenv)).
  rewrite Hfiom.
  unfold effective_fence_set.
  cbn match beta zeta.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity)
  end.
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_sail_barrier _ s)).
  apply exec_returnM.
Qed.

Section WpSmodePtCtl.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* ---- from WpSmodeFence.v ---- *)





  (* ---- from WpSmodeJal.v ---- *)





  Lemma wp_jal_gpr_s_zca_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 21)
      (m : regfile)
      (q : Qp) :
    uint rd <> 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    smode_config γ (DfracOwn q) -∗
    sr_inv R -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (JAL (imm, Regidx rd)) -∗
    ( smode_config γ (DfracOwn q) -∗
      sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hal0)
      "Hsm Htlbinv [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    (* pull a persistent [hw_config] copy out of the bundle, keep the bundle *)
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinvz & Hhsz & Hprivz & Hmstz & Hmiebz & Hmenvbz)".
    iDestruct "Hmstz" as (mstatus0z) "(Hmsz & Hsiez & %HSIEz & %HMPRVz & %HSXLz & %HMXRz & %Hlegz)".
    iDestruct "Hmiebz" as (mie_vz mdv0z) "(Hmiez & Hmdlz & %Hmmz)".
    iDestruct "Hmenvbz" as (menvcfg0z) "(Hmenvz & %HPBMTEz & %Hpmmz & %Hlpez & %Hfiomz & %Hmenvval0z)".
    iDestruct (smode_config_rebuild γ (DfracOwn q) mstatus0z mie_vz mdv0z menvcfg0z
                 HSIEz HMPRVz HSXLz HMXRz Hlegz Hmmz HPBMTEz Hpmmz Hlpez Hfiomz Hmenvval0z
                 with "Hhw Hinvz Hhsz Hprivz Hmsz Hsiez Hmiez Hmdlz Hmenvz") as "Hsm".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_s_regime R γ Φ pc false (JAL (imm, Regidx rd))


              with "Hsm Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    pose proof (rf_to_gmap_lookup m (Regidx rd)) as Hmd.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (Hpcv : register_lookup PC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = pc).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    assert (Hlink : register_lookup nextPC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    assert (Lmisa1 : register_lookup misa (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = misa0).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm))
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int pc 4))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec_int pc 4))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                        nextPC (add_vec pc (sign_extend' 64 imm)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec_int pc 4))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
      rewrite (exec_execute_JAL_gpr_zca imm rd (set_reg σ nextPC (add_vec_int pc 4))
                 Hrd ltac:(rewrite Hpcv; exact Hal0)
                 (exec_currentlyEnabled_Zca (set_reg σ nextPC (add_vec_int pc 4)) ltac:(rewrite Lmisa1; exact HmisaC))).
      rewrite Hpcv. rewrite Hlink. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hsm' Htlbinv' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                         nextPC (add_vec pc (sign_extend' 64 imm)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec_int pc 4))).(sregs)
             = add_vec pc (sign_extend' 64 imm)).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hsm' Htlbinv' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. apply rf_to_gmap_dom. }
    iEval (rewrite -rf_to_gmap_upd) in "Hfmap". iExact "Hfmap".
  Qed.

  Lemma wp_jal_gpr_s_zca_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 21)
      (m : regfile)
      (q : Qp) :
    uint rd <> 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    smode_config γ (DfracOwn q) -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (JAL (imm, Regidx rd)) -∗
    ( smode_config γ (DfracOwn q) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_jal_gpr_s_zca_r (kpt_regime root_ppn) γ Φ pc rd imm m q).
  Qed.

  (* ---- from WpSmodeJalr.v ---- *)



  Lemma wp_cret_s_zca_r_later (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (ra : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let tgt := update_vec_dec (add_vec (m !!! Regidx ra) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint ra <> 0 ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    ( ▷ ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is tgt -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros tgt HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hra Hlpe Halign.
    iIntros "#Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & %HmisaC & _)".
    iApply (wp_instr_s_config_regime R Φ pc true (JALR (zeros' 12, Regidx ra, zreg))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    pose proof (rf_to_gmap_lookup m (Regidx ra)) as Hma.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfb]".
    iDestruct (gpr_pt_value ra (m (Regidx ra)) s_pc with "Hreg Hrac") as %Lra.
    iDestruct ("Hfb" with "Hrac") as "Hfmap".
    assert (Lra' : register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s_pc.(sregs) = m !!! Regidx ra).
    { pose proof Lra as H.
      replace (Z.eqb (uint ra) 0) with false in H by (symmetry; apply Z.eqb_neq; exact Hra).
      cbn match in H. exact H. }
    assert (Hpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (Hmenv_spc : register_lookup menvcfg s_pc.(sregs) = menvcfg0).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lmenv | vm_compute; reflexivity ]. }
    assert (Hzic : exec (currentlyEnabled Ext_Zicfilp) s_pc = Some (false, s_pc)).
    { apply exec_cE_zicfilp_false_S; [ exact Hpriv_spc | rewrite Hmenv_spc; exact Hlpe ]. }
    assert (Hmisa_spc : register_lookup misa s_pc.(sregs) = misa0).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (Hzca : exec (currentlyEnabled Ext_Zca) s_pc = Some (true, s_pc)).
    { apply exec_currentlyEnabled_Zca. rewrite Hmisa_spc. exact HmisaC. }
    iMod (reg_update _ nextPC _ tgt with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC tgt).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      change (execute (JALR (zeros' 12, Regidx ra, zreg)))
        with (execute_JALR (zeros' 12) (Regidx ra) zreg).
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htgt : update_vec_dec (add_vec
                (register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s_pc.(sregs))
                (sign_extend' 64 (zeros' 12))) 0 ('b"0") = tgt)
        by (rewrite Lra'; reflexivity).
      rewrite <- Htgt.
      apply (exec_execute_JALR_ret_zca (zeros' 12) ra (zero_extend' 5 ('b"00") : mword 5) s_pc
               Hra ltac:(vm_compute; reflexivity) Hzic Hzca).
      rewrite Htgt. exact Halign. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc nextPC tgt).(sregs) = tgt)
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  Lemma wp_cret_s_zca_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (ra : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let tgt := update_vec_dec (add_vec (m !!! Regidx ra) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint ra <> 0 ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is tgt -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros tgt HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hra Hlpe Halign.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    iApply (wp_cret_s_zca_r_later R Φ pc ra m mstatus0 mie_v mdv0 menvcfg0
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hra Hlpe Halign
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr [Hcont]").
    iNext. iExact "Hcont".
  Qed.



  (* ---- from WpSmodeCsr.v ---- *)









  (* ---- from WpSmodeSret.v ---- *)

  Lemma wp_sret_gpr_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 sepc0 : mword 64)
      (m : regfile)
      :
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch: page-table geometry (SRET is a 4-byte F_Base) *)
    (* the walk's PTE read *)
    (* SRET-specific premises *)
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    sret_newpriv mstatus0 = Supervisor ->
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    sr_inv R -∗
    sepc ↦ᵣ sepc0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (SRET tt) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ sret_ms5 mstatus0 -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      sr_inv R -∗
      sepc ↦ᵣ sepc0 -∗
      pc_is (sret_tgt sepc0) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 HTSR Hsup Hlpe0)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc
       [Hpc Hnpc] Hfile Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (mword1_not_lp elp0 Help_np) as Help0.
    assert (Hxlpe : forall sz : mstate,
              register_lookup menvcfg sz.(sregs) = menvcfg0 ->
              exec (get_xLPE (sret_newpriv mstatus0)) sz = Some (false, sz)).
    { intros sz Hm. rewrite Hsup. apply exec_get_xLPE_S. rewrite Hm. exact Hlpe0. }
    iApply (wp_instr_s_config_regime R Φ pc false (SRET tt)
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid    with "Hreg Hsepc") as %Lsepc.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Lelp.
    (* tick nextPC := pc+4 *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lsepc_pc : register_lookup sepc s_pc.(sregs) = sepc0)
      by (unfold s_pc; tmig; exact Lsepc).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    (* the SRET execute reduction at s_pc, with lpe = false *)
    pose proof (exec_execute_SRET_menv s_pc false menvcfg0
                  Lpriv_pc
                  ltac:(rewrite Lmisa_pc; exact HmisaS)
                  ltac:(rewrite Lms_pc; exact HTSR)
                  ltac:(rewrite Lmisa_pc; exact HmisaC)
                  Lmenv_pc
                  ltac:(intros sz Hm;
                        pose proof (Hxlpe sz Hm) as Hx;
                        unfold sret_newpriv, sret_ms2, sret_ms1 in Hx;
                        rewrite Lms_pc; exact Hx)) as HexecC0.
    pose (sX := set_reg (set_reg (set_reg (set_reg (set_reg
                  (set_reg (set_reg (set_reg s_pc mstatus (sret_ms1 mstatus0)) mstatus (sret_ms2 mstatus0))
                           cur_privilege Supervisor) mstatus (sret_ms3 mstatus0)) mstatus (sret_ms4 mstatus0))
                  mstatus (sret_ms5 mstatus0)) elp (landing_pad_bits_backwards NO_LP_EXPECTED))
                  nextPC (sret_tgt sepc0)).
    assert (HexecC : exec (execute (SRET tt)) s_pc = Some (RETIRE_SUCCESS, sX)).
    { rewrite HexecC0. unfold sX.
      rewrite !Lms_pc Lsepc_pc.
      unfold sret_newpriv, sret_ms2, sret_ms1 in Hsup.
      unfold sret_ms1, sret_ms2, sret_ms3, sret_ms4, sret_ms5, sret_tgt.
      rewrite Hsup. reflexivity. }
    (* mirror the physical set_regs on the ghost cells *)
    iMod (reg_update _ mstatus _ (sret_ms1 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms2 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ mstatus _ (sret_ms3 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms4 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms5 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    assert (Lelp_now : register_lookup elp
              (register_set mstatus (sret_ms5 mstatus0) (register_set mstatus (sret_ms4 mstatus0)
                (register_set mstatus (sret_ms3 mstatus0) (register_set cur_privilege Supervisor
                  (register_set mstatus (sret_ms2 mstatus0) (register_set mstatus (sret_ms1 mstatus0)
                    (register_set nextPC (add_vec_int pc 4) σ.(sregs))))))))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { repeat tmig. rewrite Lelp Help0. reflexivity. }
    iDestruct (reg_interp_set_same _ elp (landing_pad_bits_backwards NO_LP_EXPECTED)
                 Lelp_now with "Hreg") as "Hreg".
    iMod (reg_update _ nextPC _ (sret_tgt sepc0) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists sX.
    iSplitR.
    { iPureIntro. rewrite Hpceq. exact HexecC. }
    iSplitL "Hreg Hmem".
    { unfold sX, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc'".
    assert (Lnpc : register_lookup nextPC sX.(sregs) = sret_tgt sepc0)
      by (unfold sX, set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc
                          [$Hpc' $Hnpc] Hfile").
  Qed.

  Lemma wp_sret_gpr_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 sepc0 : mword 64)
      (m : regfile)
      :
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch: page-table geometry (SRET is a 4-byte F_Base) *)
    (* the walk's PTE read *)
    (* SRET-specific premises *)
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    sret_newpriv mstatus0 = Supervisor ->
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    sepc ↦ᵣ sepc0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (SRET tt) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ sret_ms5 mstatus0 -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      sepc ↦ᵣ sepc0 -∗
      pc_is (sret_tgt sepc0) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_sret_gpr_r (kpt_regime root_ppn) Φ pc mstatus0 mie_v mdv0 menvcfg0 sepc0 m).
  Qed.

End WpSmodePtCtl.
