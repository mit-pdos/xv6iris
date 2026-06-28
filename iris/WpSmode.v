(* WpSmode.v -- the first SUPERVISOR-mode instruction after start()'s MRET,
   PROVEN (no admits): wp_smode_caddi (c.addi sp at 0x80000e82 = <main>) and the
   full S-mode fetch/step infrastructure (translationMode/translateAddr/pmpCheck/
   getPendingSet/should_inc for Supervisor), then chained to wp_kernel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpGprAddi WpAdd WpGprMret WpGprMretWp WpStartText KernelBoot WpStartChain WpStart2 WpStart3.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

Section WpSmode.
  Context `{!riscvGS Σ}.

  Lemma exec_should_inc_S (mc : mword 32) (mcfg : mword 64) (priv : Privilege) s :
    register_lookup mcountinhibit s.(sregs) = mc ->
    register_lookup minstretcfg s.(sregs) = mcfg ->
    exec (should_inc_minstret priv) s
      = Some (andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                   (eq_vec (counter_priv_filter_bit mcfg priv) ('b"0")), s).
  Proof.
    intros Hmc Hmcfg. unfold should_inc_minstret.
    erewrite (exec_and_boolM_Some _ _ s (eq_vec (_get_Counterin_IR mc) ('b"0")) s).
    2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcountinhibit s)). rewrite Hmc. apply exec_returnm. }
    destruct (eq_vec (_get_Counterin_IR mc) ('b"0")) eqn:Ea; cbn [andb].
    - rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg minstretcfg s)). rewrite Hmcfg. apply exec_returnm.
    - reflexivity.
  Qed.

  Lemma exec_translationMode_S_bare (satp0 : mword 64) s :
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ->
    exec (translationMode Supervisor) s = Some (Bare, s).
  Proof.
    intros HSXL Hsatp Hmode.
    unfold translationMode.
    replace (generic_eq Supervisor Machine) with false by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_architecture_Supervisor s HSXL)).
    cbn match.
    change (xlen >=? 64) with true.
    match goal with |- exec (Defs.bind ?ARM _) s = _ =>
      assert (HARM : exec ARM s = Some (_get_Satp64_Mode (Mk_Satp64 satp0), s)) end.
    { assert (Hae : exec (Defs.assert_exp' true "sys/vmem.sail:254.25-254.26") s
                    = Some (eq_refl, s)).
      { unfold assert_exp'. cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hae).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
      rewrite Hsatp. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ HARM).
    rewrite Hmode.
    replace (satpMode_of_bits RV64 ('b"0000" : mword 4)) with (Some Bare)
      by (vm_compute; reflexivity).
    cbn match. apply exec_returnm.
  Qed.

  Lemma exec_translateAddr_identity_S (a satp0 : mword 64) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ->
    exec (translateAddr (Virtaddr a) (InstructionFetch tt)) s
      = Some (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))),
                  PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hcp HSXL Hsatp Hmode.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_bare satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_fetch s)).
    unfold Defs.bind0.
    replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
    rewrite execR_bind. cbn match. reflexivity.
  Qed.

  Lemma and_vec_zeros64_r (x : mword 64) : and_vec x (zeros' 64) = zeros' 64.
  Proof.
    cbv [and_vec word_binop with_word' with_word]. unfold MachineWord.MachineWord.and.
    apply bv_eq. rewrite bv_and_unsigned.
    assert (H0 : bv_unsigned (zeros' 64) = 0) by reflexivity. rewrite H0. apply Z.land_0_r.
  Qed.

  (* read_mip succeeds (any value) given the S-extension is enabled. *)
  Lemma exec_read_mip_some_S (s : mstate) :
    exec (currentlyEnabled Ext_S) s = Some (true, s) ->
    exists v, exec (read_mip IncludePlatformInterrupts) s = Some (v, s).
  Proof.
    intro HES.
    assert (Hext : exists ev, exec (external_interrupts_pending tt) s = Some (ev, s)).
    { unfold external_interrupts_pending.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sig_meip s)).
      rewrite (exec_bind_Some _ _ _ _ _ HES). cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sig_seip s)). eexists. apply exec_returnm. }
    destruct Hext as [ev Hext].
    unfold read_mip. cbn match. eexists.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mip s)).
    rewrite (exec_bind_Some _ _ _ _ _ Hext). apply exec_returnm.
  Qed.

  Lemma exec_getPendingSet_supervisor_none (s : mstate) (mie_v mideleg_v mstatus_v : mword 64) :
    exec (currentlyEnabled Ext_S) s = Some (true, s) ->
    register_lookup mie s.(sregs) = mie_v ->
    register_lookup mideleg s.(sregs) = mideleg_v ->
    register_lookup mstatus s.(sregs) = mstatus_v ->
    and_vec mie_v (not_vec mideleg_v) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus_v) ('b"1") = false ->
    exec (getPendingSet Supervisor) s = Some (None, s).
  Proof.
    intros HES Hmie Hmdl Hms Hand0 HSIE.
    destruct (exec_read_mip_some_S s HES) as [mipv Hmip].
    assert (Hguard : exec (or_boolM (currentlyEnabled Ext_S)
                       (bind (read_reg mideleg)
                          (fun w1 : mword 64 => returnM (eq_vec w1 (zeros' 64))))) s
                     = Some (true, s)).
    { rewrite (exec_or_boolM_Some _ _ _ _ _ HES). reflexivity. }
    assert (Hae : exec (Defs.assert_exp' true "sys/sys_control.sail:107.58-107.59") s
                  = Some (eq_refl, s)).
    { unfold assert_exp'. cbn match. apply exec_returnm. }
    assert (HmIEt : exec (or_boolM
              (and_boolM (returnM (generic_eq Supervisor Machine))
                 (bind (read_reg mstatus)
                    (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1")))))
              (returnM (orb (generic_eq Supervisor Supervisor) (generic_eq Supervisor User)))) s
                  = Some (true, s)).
    { assert (Hand : exec (and_boolM (returnM (generic_eq Supervisor Machine))
                       (bind (read_reg mstatus)
                          (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1"))))) s
                     = Some (false, s)).
      { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq Supervisor Machine) s)).
        change (generic_eq Supervisor Machine) with false. reflexivity. }
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
      change (orb (generic_eq Supervisor Supervisor) (generic_eq Supervisor User)) with true.
      apply exec_returnm. }
    assert (HsIEf : exec (or_boolM
              (and_boolM (returnM (generic_eq Supervisor Supervisor))
                 (bind (read_reg mstatus)
                    (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1")))))
              (returnM (generic_eq Supervisor User))) s
                  = Some (false, s)).
    { assert (Hand : exec (and_boolM (returnM (generic_eq Supervisor Supervisor))
                       (bind (read_reg mstatus)
                          (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1"))))) s
                     = Some (false, s)).
      { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq Supervisor Supervisor) s)).
        change (generic_eq Supervisor Supervisor) with true. cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
        rewrite Hms. rewrite HSIE.
        apply exec_returnm. }
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
      change (generic_eq Supervisor User) with false. apply exec_returnm. }
    unfold getPendingSet.
    rewrite (exec_bind_Some _ _ _ _ _ Hguard).
    rewrite (exec_bind_Some _ _ _ _ _ Hae).
    rewrite (exec_bind_Some _ _ _ _ _ Hmip).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
    rewrite (exec_bind_Some _ _ _ _ _ HmIEt).
    rewrite (exec_bind_Some _ _ _ _ _ HsIEf).
    rewrite Hmie.
    rewrite Hmdl.
    rewrite Hand0.
    rewrite and_vec_zeros64_r.
    assert (Hnq : neq_vec (zeros' 64 : mword 64) (zeros' 64) = false).
    { vm_compute. reflexivity. }
    rewrite Hnq.
    cbn [andb].
    apply exec_returnm.
  Qed.


  Lemma exec_dispatchInterrupt_none_S (s : mstate) :
    exec (getPendingSet Supervisor) s = Some (None, s) ->
    exec (dispatchInterrupt Supervisor) s = Some (None, s).
  Proof. intros Hgp. unfold dispatchInterrupt.
    rewrite (exec_bind_Some _ _ _ _ _ Hgp). cbn match. apply exec_returnm. Qed.

Section HartActiveRVC_gen.
  Context (priv : Privilege) (s s_x : mstate) (h : mword 16) (instr other : instruction)
          (pc : mword 64) (resf : ExecutionResult).

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = priv.
  Hypothesis Hdisp : exec (dispatchInterrupt priv) s = Some (None, s).
  Hypothesis Hfetch : exec (fetch tt) s = Some (F_RVC h, s).
  Hypothesis Hdec : exec (ext_decode_compressed h) s = Some (instr, s).
  Hypothesis Hlpad : eq_vec (register_lookup elp s.(sregs))
                            (landing_pad_bits_backwards LP_EXPECTED) = false.
  Hypothesis HpcF : register_lookup PC s.(sregs) = pc.
  Hypothesis Hzca : exec (currentlyEnabled Ext_Zca) s = Some (true, s).
  Let s_pc : mstate := set_reg s nextPC (add_vec_int pc 2).
  (* RVC instructions expand via [ExecuteAs] to a base instruction [other]. *)
  Hypothesis Hexec : exec (execute instr) s_pc = Some (ExecuteAs other, s_pc).
  Hypothesis Hexec2 : exec (execute other) s_pc = Some (resf, s_x).

  Lemma exec_hart_active_progress_RVC_gen :
    exec (run_hart_active 0) s
    = Some (Step_Execute (resf, zero_extend' 32 h), s_x).
  Proof using All.
    unfold run_hart_active.
    rewrite exec_catch_early_return.
    rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
    rewrite execR_bind execR_liftR Hdisp. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
    rewrite execR_liftR Hfetch. cbn match. cbn match.
    unfold ext_fetch_hook. cbn match. cbn beta iota.
    rewrite execR_bind execR_liftR Hdec. cbn match.
    unfold get_config_print_instr. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
    (* is_landing_pad_expected -> false (plain, no and_boolM in the RVC branch) *)
    rewrite execR_liftR exec_is_landing_pad Hlpad. cbn match.
    (* currentlyEnabled Ext_Zca -> true *)
    rewrite execR_bind execR_liftR Hzca. cbn match.
    (* read PC -> pc ; write nextPC (pc+2) ; execute instr -> ExecuteAs other *)
    rewrite execR_bind execR_liftR (exec_read_reg PC) HpcF. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_liftR (exec_write_reg nextPC). cbn match.
    fold s_pc. rewrite execR_liftR Hexec. cbn match. cbn match.
    (* w11 = ExecuteAs other -> liftR (execute other) -> resf, fed to Step_Execute *)
    rewrite execR_bind execR_liftR Hexec2. cbn match.
    rewrite execR_returnR. cbn match. reflexivity.
  Qed.

End HartActiveRVC_gen.

Section StepGen_gen.
  Context (priv : Privilege) (s s_exec : mstate) (iw : mword 32) (b : bool).
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = priv.
  Hypothesis Hsi   : exec (should_inc_minstret priv) s = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a = Some (Step_Execute (RETIRE_SUCCESS, iw), s_exec).
  Hypothesis Hhart_exec : register_lookup hart_state s_exec.(sregs) = HART_ACTIVE tt.
  Hypothesis Hmi_exec : register_lookup (R_bool minstret_increment) s_exec.(sregs) = b.
  Hypothesis Hrvfi : get_config_rvfi tt = false.
  Let s_tick : mstate := set_reg s_exec PC (register_lookup nextPC s_exec.(sregs)).
  Let s_final : mstate :=
    if b then set_reg s_tick minstret
                      (add_vec_int (register_lookup minstret s_tick.(sregs)) 1)
         else s_tick.

  Lemma exec_riscv_step_gen_gen : exec riscv_step s = Some (tt, s_final).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (false, s_final))).
    { reflexivity. }
    unfold try_step. cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    cbn beta. rewrite Hpriv.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)).
    cbn beta. rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    unfold RETIRE_SUCCESS. cbn beta iota.
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind_Some.
            2:{ apply exec_read_reg. }
            rewrite Hhart_exec. unfold Defs.assert_exp. cbn [hart_is_active].
            reflexivity. }
        apply exec_read_reg. }
    rewrite Hhart_exec. cbn beta iota.
    erewrite exec_bind0_Some.
    2:{ apply exec_tick_pc. }
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some.
        2:{ reflexivity. }
        cbn beta iota. apply (exec_read_reg minstret_increment). }
    rewrite Hrvfi.
    replace (register_lookup minstret_increment
               (set_reg s_exec PC (register_lookup nextPC s_exec.(sregs))).(sregs))
      with b.
    2:{ unfold set_reg; cbn [sregs].
        rewrite irrelevant_register_set;
          [ (exact Hmi_exec || (symmetry; exact Hmi_exec)) | reflexivity ]. }
    unfold s_final, s_tick.
    destruct b.
    - erewrite exec_bind0_Some.
      2:{ erewrite exec_bind0_Some.
          2:{ erewrite exec_bind_Some.
              2:{ apply (exec_read_reg minstret). }
              apply exec_write_reg. }
          cbn beta iota. reflexivity. }
      reflexivity.
    - erewrite exec_bind0_Some.
      2:{ erewrite exec_bind0_Some.
          2:{ cbn beta iota. reflexivity. }
          cbn beta iota. reflexivity. }
      reflexivity.
  Qed.
End StepGen_gen.

Section ForwardCaddiGpr_gen.
  Context (priv : Privilege) (s : mstate) (pc : mword 64) (b : bool) (w16 : mword 16) (rd : mword 5) (imm6 : mword 6).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC w16, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret priv) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hcdec : forall s0,
    eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w16) s0 = Some (C_ADDI (imm6, Regidx rd), s0).

  Definition sXa : mstate :=
    set_reg (s_pcl s pc b) (R_bitvector_64 (gpr_of_Z (uint rd)))
      (regval_into_reg (gpr_addi_val rd (sign_extend' 12 imm6) (s_pcl s pc b))).
  Definition sTa : mstate := set_reg sXa PC (register_lookup nextPC sXa.(sregs)).
  Definition sFa : mstate :=
    if b then set_reg sTa minstret (add_vec_int (register_lookup minstret sTa.(sregs)) 1)
         else sTa.

  Lemma forward_exec_caddi_gpr_gen :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = priv ->
    exec (dispatchInterrupt priv) (sAl s b) = Some (None, (sAl s b)) ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFa).
  Proof using All.
    intros Lpc Lpriv Hdisp Lhs LS Lelp Lmisa.
    assert (LpcA  : register_lookup PC (sAl s b).(sregs) = pc).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege (sAl s b).(sregs) = priv).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state (sAl s b).(sregs) = HART_ACTIVE tt).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAl s b).(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LS | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp (sAl s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa (sAl s b).(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt priv) (sAl s b) = Some (None, (sAl s b))) by exact Hdisp.
    assert (HfetchA : exec (fetch tt) (sAl s b) = Some (F_RVC w16, (sAl s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode_compressed w16) (sAl s b) = Some (C_ADDI (imm6, Regidx rd), (sAl s b)))
      by (apply Hcdec; exact LmisaA).
    assert (Hexec1 : exec (execute (C_ADDI (imm6, Regidx rd))) (s_pcl s pc b)
                   = Some (ExecuteAs (ITYPE (sign_extend' 12 imm6, Regidx rd, Regidx rd, ADDI)), (s_pcl s pc b)))
      by apply exec_execute_C_ADDI.
    assert (Hexec2 : exec (execute (ITYPE (sign_extend' 12 imm6, Regidx rd, Regidx rd, ADDI))) (s_pcl s pc b)
                   = Some (RETIRE_SUCCESS, sXa)).
    { rewrite (exec_execute_ITYPE_ADDI_gpr rd rd (sign_extend' 12 imm6) (s_pcl s pc b)).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd0).
      unfold sXa. reflexivity. }
    assert (Hzca : exec (currentlyEnabled Ext_Zca) (sAl s b) = Some (true, (sAl s b)))
      by (apply exec_currentlyEnabled_Zca; exact LmisaA).
    assert (Hha : exec (run_hart_active 0) (sAl s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w16), sXa)).
    { exact (exec_hart_active_progress_RVC_gen priv (sAl s b) sXa w16 (C_ADDI (imm6, Regidx rd))
               (ITYPE (sign_extend' 12 imm6, Regidx rd, Regidx rd, ADDI)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA LpcA Hzca Hexec1 Hexec2). }
    apply (exec_riscv_step_gen_gen priv s sXa (zero_extend' 32 w16) b).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXa, s_pcl, sAl; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXa, s_pcl, sAl; cbn zeta. trans_mi. trans_mi. rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCaddiGpr_gen.


  Lemma exec_pmpMatchAddr_TOR_match (addr width : mword 64) (ent : mword 8)
      (pmpaddr prev : mword 64) s :
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = TOR ->
    zopz0zKzJ_u prev pmpaddr = false ->
    pmpRangeMatch (Z.mul (uint prev) 4) (Z.mul (uint pmpaddr) 4) (uint addr) (uint width) = PMP_Match ->
    exec (pmpMatchAddr (Physaddr addr) width ent pmpaddr prev) s = Some (PMP_Match, s).
  Proof.
    intros HA Hord Hrange. unfold pmpMatchAddr. cbn zeta.
    rewrite HA. cbn match. rewrite Hord. rewrite Hrange. apply exec_returnm.
  Qed.


  Lemma exec_pmpReadAddrReg_val (n : Z) s :
    exec (pmpReadAddrReg n) s
      = Some (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) n, s).
  Proof.
    unfold pmpReadAddrReg. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpaddr_n s)). cbn beta.
    replace (andb (Z.geb sys_pmp_grain 2)
               (eq_vec (access_vec_dec (_get_Pmpcfg_ent_A
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) n)) 1) ('b"1")))
      with false by (vm_compute; reflexivity).
    replace (andb (Z.geb sys_pmp_grain 1)
               (eq_vec (access_vec_dec (_get_Pmpcfg_ent_A
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) n)) 1) ('b"0")))
      with false by (vm_compute; reflexivity).
    cbn match. apply exec_returnm.
  Qed.


  Lemma exec_pmpCheck_supervisor_grant (a : mword 64) (width : Z) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint a) (uint (to_bits 64 width)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    exec (pmpCheck (Physaddr a) width (InstructionFetch tt) Supervisor) s = Some (None, s).
  Proof.
    intros HA Hord Hrange HX.
    unfold pmpCheck. rewrite exec_catch_early_return.
    replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
    rewrite execR_bind0.
    match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
      assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s)) end.
    { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
      rewrite execR_bind.
      (* body 0: prev = zeros (Z.gtb 0 0 = false) *)
      rewrite execR_bind. rewrite execR_returnR. cbn match.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
                    (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                    (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                    (zeros' 64) s HA Hord Hrange)). cbn beta.
      cbn match.
      (* PMP_Match arm: or_boolM (pmpCheckRWX) (...) -> true *)
      unfold or_boolM.
      rewrite execR_bind.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                              (InstructionFetch tt)) s = Some (true, s))).
      2:{ unfold pmpCheckRWX. cbn match. rewrite HX. apply exec_returnm. }
      cbn match. rewrite execR_returnR. cbn beta.
      cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
      unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
    rewrite Hfe. cbn match. reflexivity.
  Qed.


  (* ---- S-mode fetch read path: mirror of the Machine lemmas, Supervisor +
     the granting PMP entry (replacing all-OFF + pmpCheck_machine_none). ---- *)
  Lemma exec_checked_mem_read_ram_2_S (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (w : bv 16) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 2)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2 = Some region ->
    is_aligned_paddr (Physaddr addr) 2 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
    exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    exec (checked_mem_read (InstructionFetch tt) pbmt Supervisor (Physaddr addr) 2 false false false false)
         s = Some (Ok (w, default_meta), s).
  Proof.
    intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes.
    unfold checked_mem_read.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
    2:{ unfold phys_access_check.
        rewrite (exec_bind_Some _ _ _ _ _
                   (exec_pmpCheck_supervisor_grant addr 2 s HA Hord Hrange HX)).
        cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_2 addr pbmt region s Hmatch Halign Hexec)).
        cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (within_mmio_readable (Physaddr addr) 2) s = Some (false, s))).
    2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
        rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
    2:{ unfold read_kind_of_flags. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_2 addr w s Hbytes)).
    apply exec_returnM.
  Qed.


  Lemma exec_mem_read_fetch_2_S (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (w : bv 16) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 2)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2 = Some region ->
    is_aligned_paddr (Physaddr addr) 2 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
    exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    exec (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 2 false false false)
         s = Some (Ok w, s).
  Proof.
    intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv.
    unfold mem_read.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
    rewrite Hpriv.
    unfold mem_read_priv.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (mem_read_priv_meta _ _ _ _ 2 _ _ _ _) s = Some (Ok (w, default_meta), s))).
    2:{ unfold mem_read_priv_meta. cbn [orb andb].
        rewrite (exec_bind_Some _ _ _ _ _
                  (_ : exec (checked_mem_read _ _ _ _ 2 _ _ _ _) s = Some (Ok (w, default_meta), s))).
        2:{ cbn match. apply exec_checked_mem_read_ram_2_S with (region := region); assumption. }
        cbn match. unfold mem_read_callback. apply exec_returnM. }
    cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
  Qed.


Section FetchBytes2_S.
  Context (pc satp0 : mword 64) (region : PMA_Region) (w : mword 16) (s : mstate).
  Let addr := fetch_pa pc.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hsmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 2)) = PMP_Match.
  Hypothesis HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 2 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j).

  Lemma exec_fetch_bytes_2_S :
    exec (fetch_bytes pc pc 2) s = Some (@FetchBytes_Success 2 w, s).
  Proof using All.
    unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr pc) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr addr, PBMT_PMA, init_ext_ptw)), s))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite (exec_translateAddr_identity_S pc satp0 s Hpriv HSXL Hsatp Hsmode).
        cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr addr, PBMT_PMA) s)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr addr) 2 false false false)) s
           = Some (inr (Ok w), s))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2_S PBMT_PMA addr region w s
                   HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.
End FetchBytes2_S.

Section FetchRVC2_S.
  Context (pc satp0 : mword 64) (region : PMA_Region) (w : mword 16) (s : mstate).
  Let addr := fetch_pa pc.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hsmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 2)) = PMP_Match.
  Hypothesis HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 2 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec pc 1) ('b"0") = true.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = false.
  Hypothesis HmisaC : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HisRVC : isRVC w = true.

  Lemma exec_fetch_RVC_2_S : exec (fetch tt) s = Some (F_RVC w, s).
  Proof using All.
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (pc, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite execR_liftR. rewrite (exec_currentlyEnabled_Zca s HmisaC). cbn match.
            apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _
      (exec_fetch_bytes_2_S pc satp0 region w s HpcPC Hpriv HSXL Hsatp Hsmode
         HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes)).
    cbv iota beta. rewrite HisRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.
End FetchRVC2_S.


  Lemma fetch_from_pts_minstret_RVC2_S
      (pc satp0 mstatus0 : mword 64) (w : mword 16) (region : PMA_Region)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (b : bool) (misa0 : mword 64) (s : mstate) {dq : dfrac} (dqc : dfrac) :
    matching_pma_region pmar0 (Physaddr (fetch_pa pc)) 2 = Some region ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (fetch_pa pc)) (uint (to_bits 64 2)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    isRVC w = true ->
    reg_interp s.(sregs) -∗ gen_heap_interp s.(mem) -∗
    PC ↦ᵣ pc -∗ cur_privilege ↦ᵣ Supervisor -∗ reg_pointsto misa dqc misa0 -∗
    (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗
    reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ⌜ exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC w, set_reg s (R_bool minstret_increment) b) ⌝.
  Proof.
    iIntros (Hmatch0 Hexec HSXL0 Hsmode HA0 Hord0 Hrange0 HX0 Halign Hbit0 Hbit1 Hvalign Hmisa HisRVC)
            "Hreg Hmem Hpc Hpriv Hmisa' Hms Hsatp Hpmpc Hpmpaddr Hpma Hhtif Hbytes".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hsatp")  as %Lsatp.
    iDestruct (reg_valid with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hpmpaddr") as %Lpmpaddr.
    iDestruct (reg_valid_dq with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")  as %Lhtif.
    iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
               s.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 2)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (fetch_pa pc)⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iPureIntro.
    unfold addr_is_ram in Hram. destruct Hram as [Hnc Hns].
    set (t := set_reg s (R_bool minstret_increment) b).
    assert (Ltpc : register_lookup PC t.(sregs) = pc).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (Ltpriv : register_lookup cur_privilege t.(sregs) = Supervisor).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (Ltmisa : register_lookup misa t.(sregs) = misa0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmisa | vm_compute; reflexivity]. }
    assert (Ltms : register_lookup mstatus t.(sregs) = mstatus0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lms | vm_compute; reflexivity]. }
    assert (Ltsatp : register_lookup satp t.(sregs) = satp0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lsatp | vm_compute; reflexivity]. }
    assert (Ltpmpc : register_lookup pmpcfg_n t.(sregs) = pmpcfg0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpc | vm_compute; reflexivity]. }
    assert (Ltpmpaddr : register_lookup pmpaddr_n t.(sregs) = pmpaddr00).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpaddr | vm_compute; reflexivity]. }
    assert (Ltpma : register_lookup pma_regions t.(sregs) = pmar0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpma | vm_compute; reflexivity]. }
    assert (Lthtif : register_lookup htif_tohost_base t.(sregs) = None).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhtif | vm_compute; reflexivity]. }
    assert (Ltmem : forall j : nat, (N.of_nat j < 2)%N ->
              t.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j))
      by (unfold t, set_reg; cbn [mem]; exact Hbytesf).
    assert (HSXL : _get_Mstatus_SXL (register_lookup mstatus t.(sregs)) = 'b"10")
      by (rewrite Ltms; exact HSXL0).
    assert (HA : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n t.(sregs)) 0)) = TOR)
      by (rewrite Ltpmpc; exact HA0).
    assert (Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n t.(sregs)) 0) = false)
      by (rewrite Ltpmpaddr; exact Hord0).
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n t.(sregs)) 0)) 4)
              (uint (fetch_pa pc)) (uint (to_bits 64 2)) = PMP_Match)
      by (rewrite Ltpmpaddr; exact Hrange0).
    assert (HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n t.(sregs)) 0)) ('b"1") = true)
      by (rewrite Ltpmpc; exact HX0).
    assert (Hmatch : matching_pma_region (register_lookup pma_regions t.(sregs))
              (Physaddr (fetch_pa pc)) 2 = Some region)
      by (rewrite Ltpma; exact Hmatch0).
    assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true)
      by (rewrite Ltmisa; exact Hmisa).
    exact (exec_fetch_RVC_2_S pc satp0 region w t Ltpc Ltpriv HSXL Ltsatp Hsmode
             HA Hord Hrange HX Hmatch Halign Hexec
             (within_clint_false (fetch_pa pc) 2 t Hnc ltac:(lia))
             (within_sig_false  (fetch_pa pc) 2 t Hns ltac:(lia))
             (within_htif_false (fetch_pa pc) 2 t Lthtif)
             Ltmem Hbit0 Hbit1 Hvalign HmisaC HisRVC).
  Qed.


  Lemma wp_smode_caddi (pc : mword 64) (w16 : mword 16) (rd : mword 5) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 mdv0 mstatus0 satp0 mie_v : mword 64)
      (b1 : bool) (npc0 mst0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (dqc : dfrac) (Phi : mval -> iProp Σ) :
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    pma_allows_all pmar0 ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (fetch_pa pc)) (uint (to_bits 64 2)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_ADDI (imm6, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) :=
                     regval_into_reg (add_vec vd (sign_extend' 64 (sign_extend' 12 imm6)))]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrd Hmd HsatpM HSXL Hpmaall HA0 Hord0 Hrange0 HX0 Halignf Hbit0f Hbit1f Hvalignf
             HisRVC HmisaC HmisaS Hdec Hb1 Hmie_mdl HSIE Help)
      "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")      as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")    as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")      as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")     as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")      as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")     as %Lmst.
    iDestruct (reg_valid with "Hreg Hsatp")    as %Lsatp.
    iDestruct (reg_valid with "Hreg Hmie")     as %Lmie.
    iDestruct (reg_valid with "Hreg Help'")    as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh")   as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")    as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'")   as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc1 Hfb]".
    iDestruct (reg_valid with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb" with "Hrdc1") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_S mc mcfg Supervisor s Lmc Lmcfg). }
    assert (Hav : gpr_addi_val rd (sign_extend' 12 imm6) (s_pcl s pc b1)
                  = add_vec vd (sign_extend' 64 (sign_extend' 12 imm6)))
      by (apply (gpr_addi_val_caddi_file s pc b1 rd imm6 vd Hrd Lrd)).
    iDestruct (fetch_from_pts_minstret_RVC2_S pc satp0 mstatus0 w16 region_f pmpcfg0 pmpaddr00 pmar0 b1 misa0 s dqc
                 Hmatchf Hexecf HSXL HsatpM HA0 Hord0 Hrange0 HX0 Halignf Hbit0f Hbit1f Hvalignf HmisaC HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hms Hsatp Hpmpc Hpmpaddr Hpma Hhtif Hibytes") as %Hfetch_at.
    assert (Hdisp : exec (dispatchInterrupt Supervisor) (sAl s b1) = Some (None, sAl s b1)).
    { apply exec_dispatchInterrupt_none_S.
      apply (exec_getPendingSet_supervisor_none (sAl s b1) mie_v mdv0 mstatus0).
      - rewrite (exec_currentlyEnabled_S (sAl s b1)).
        replace (register_lookup misa (sAl s b1).(sregs)) with misa0.
        2:{ unfold sAl, set_reg; cbn [sregs].
            rewrite irrelevant_register_set; [symmetry; exact Lmisa | vm_compute; reflexivity]. }
        rewrite HmisaS. reflexivity.
      - unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmie | vm_compute; reflexivity].
      - unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmdl | vm_compute; reflexivity].
      - unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lms | vm_compute; reflexivity].
      - exact Hmie_mdl.
      - exact HSIE. }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (WpRvc.sFca s pc b1 rd imm6 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (WpRvc.sFa_eq s pc b1 rd imm6 mst0 Lpc Lmst).
      apply (forward_exec_caddi_gpr_gen Supervisor s pc b1 w16 rd imm6 Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Hdisp Lhs).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HmisaC. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_addi_val rd (sign_extend' 12 imm6) (s_pcl s pc b1)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec vd (sign_extend' 64 (sign_extend' 12 imm6)))) with "Hrdc") as "Hfile".
    unfold WpRvc.sFca, WpRvc.base_upd_a. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes").
  Qed.

  (* ===================================================================== *)
  Lemma wp_kernel_smode1
      (v : bv 64) (sp0b mst0 mstatus0 : mword 64) (mi0 : bool) (elp0 : mword 1)
      (mc : mword 32) (mcfg : mword 64) (mseccfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (x1_0 x10_0 x11_0 mhartid0 misa0 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (menvcfg0 mtime0 stimecmp0 mepc0 satp0 medeleg0 mie0 : mword 64)
      (mcounteren0 : mword 32) (pmpaddr00 : type_of_register pmpaddr_n)
      (vs0b va4b va5b : mword 64)
      (vold_ra vold_s0 vti_ra vti_s0 : bv 64) (newpriv : Privilege) (lpe : bool)
      (* ---- first S-mode instruction (c.addi sp,sp,-16) ---- *)
      (rd : mword 5) (imm6 : mword 6) (b1s : bool)
      E (Φ : mval -> iProp Σ) :
      let bb     := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                         (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
      let sp1e   := regval_into_reg (add_vec kpc0 (auipc_off imm_auipc)) in
      let eal    := add_vec sp1e (sign_extend' 64 imm_ld) in
      let a8l    := zero_extend' 64 (subrange_vec_dec eal (xlen - 0 - 1) 0) in
      let pal    := zero_extend' 64 (add_vec_int a8l (0 * 8)) in
      let bumpe  := fun mm => if bb then add_vec_int mm 1 else mm in
      let mst1   := if bb then add_vec_int mst0 1 else mst0 in
      let x2ld   := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v)) in
      let x10l   := regval_into_reg luival in
      let x11c   := regval_into_reg mhartid0 in
      let x11a   := regval_into_reg (add_vec x11c (sign_extend' 64 (sign_extend' 12 imm_caddi))) in
      let x10m   := regval_into_reg (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                      (mulop_mul.(mul_op_signed_rs2)) x10l x11a (mulop_mul.(mul_op_result_part))) in
      let x2add  := regval_into_reg (add_vec x2ld x10m) in
      let x1j    := regval_into_reg (add_vec_int kpc7 4) in
      let m8     := bumpe (bumpe (bumpe (bumpe (bumpe (bumpe (bumpe mst1)))))) in
      let sp1  := add_vec x2add (sign_extend' 64 (sign_extend' 12 imm9)) in
      let imm_ra := zero_extend' 12 (concat_vec uimm10 ('b"000")) in
      let pa_ra  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0)) (0 * 8)) in
      let imm_s0 := zero_extend' 12 (concat_vec uimm11 ('b"000")) in
      let pa_s0  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0)) (0 * 8)) in
      let a8_ra  := zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0) in
      let a8_s0  := zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0) in
      let va5_c2 := regval_into_reg (subrange_vec_dec mstatus0 (Z.sub xlen 1) 0) in
      let va4_35 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw35)) in
      let va4_36 := add_vec va4_35 (sign_extend' 64 (subrange_vec_dec sw36 31 20)) in
      let va5_37 := and_vec va5_c2 va4_36 in
      let va4_38 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw38)) in
      let va4_39 := add_vec va4_38 (sign_extend' 64 (subrange_vec_dec sw39 31 20)) in
      let va5_40 := or_vec va5_37 va4_39 in
      let mstatus1 := mstatus_legalized mstatus0 va5_40 in
      let va5_42 := add_vec spc42 (auipc_off (subrange_vec_dec sw42 31 12)) in
      let va5_43 := add_vec va5_42 (sign_extend' 64 (subrange_vec_dec sw43 31 20)) in
      let va5_45 := cli_wval (scli_imm sw45) in
      let va5_47 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw47)) in
      let va5_48 := add_vec va5_47 (sign_extend' 64 (sign_extend' 12 (scli_imm sw48))) in
      let mdv0 := mideleg_legalized (zeros' 64) va5_48 in
      let va5_51 := lower_mie mie0 mdv0 in
      let va5_52 := or_vec va5_51 (sign_extend' 64 (subrange_vec_dec sw52 31 20)) in
      let va5_54 := cli_wval (scli_imm sw54) in
      let va5_55 := csrli_wval (scsrli_sh sw55) va5_54 in
      let va5_57 := cli_wval (scli_imm sw57) in
      let pmpcfg1 := pmpcfg0_finalvec va5_57 pmpcfg0 in
      let c6sp   := add_vec sp1 (sign_extend' 64 (sign_extend' 12 imm9)) in
      let tpa_ra := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0)) (0 * 8)) in
      let tpa_s0 := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0)) (0 * 8)) in
      let ta8_ra := zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0) in
      let ta8_s0 := zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0) in
      m !! x1 = Some x1_0 -> m !! x2 = Some sp0b ->
      m !! x10 = Some x10_0 -> m !! x11 = Some x11_0 ->
      m !! gpr_of_Z 8 = Some vs0b -> m !! gpr_of_Z 14 = Some va4b -> m !! gpr_of_Z 15 = Some va5b ->
      is_Some (m !! gpr_of_Z 4) ->
      pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
      eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
      eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
      eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
      pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
      is_aligned_vaddr (Virtaddr a8l) 8 = true -> is_aligned_paddr (Physaddr pal) 8 = true ->
      eq_vec (_get_Misa_C misa0) ('b"1") = true ->
      eq_vec (_get_Misa_M misa0) ('b"1") = true ->
      eq_vec (_get_Misa_S misa0) ('b"1") = true ->
      eq_vec (_get_Misa_U misa0) ('b"1") = true ->
      eq_vec (_get_Mstatus_MIE mstatus1) ('b"1") = false ->
      _get_Mstatus_SXL mstatus1 = 'b"10" ->
      is_aligned_vaddr (Virtaddr a8_ra) 8 = true -> is_aligned_paddr (Physaddr pa_ra) 8 = true ->
      is_aligned_vaddr (Virtaddr a8_s0) 8 = true -> is_aligned_paddr (Physaddr pa_s0) 8 = true ->
      eq_vec (_get_Mstatus_MPRV mstatus1) ('b"1") = false ->
      bool_bit_backwards (_get_Seccfg_MLPE mseccfg0) = false ->
      pmp_allows_all pmpcfg1 ->
      is_aligned_vaddr (Virtaddr ta8_ra) 8 = true -> is_aligned_paddr (Physaddr tpa_ra) 8 = true ->
      is_aligned_vaddr (Virtaddr ta8_s0) 8 = true -> is_aligned_paddr (Physaddr tpa_s0) 8 = true ->
      privLevel_bits_forwards (_get_Mstatus_MPP (cms2 mstatus1), ('b"0")) = returnM newpriv ->
      generic_neq newpriv Machine = true ->
      (forall sz, exec (get_xLPE newpriv) sz = Some (lpe, sz)) ->
      (* ---- facts about the post-MRET S-mode state (the remaining model work
         for the c.addi fetch; see wp_smode_caddi) ---- *)
      uint rd = 2 ->
      newpriv = Supervisor ->
      b1s = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                 (eq_vec (counter_priv_filter_bit mcfg newpriv) ('b"0")) ->
      _get_Satp64_Mode (Mk_Satp64 (satp_legalized satp0 va5_45)) = ('b"0000" : mword 4) ->
      _get_Mstatus_SXL (cms5 mstatus1) = 'b"10" ->
      eq_vec (_get_Mstatus_SIE (cms5 mstatus1)) ('b"1") = false ->
      and_vec (sie_new_mie mie0 mdv0 va5_52) (not_vec mdv0) = zeros' 64 ->
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg1 0)) = TOR ->
      zopz0zKzJ_u (zeros' 64) (vec_access_dec (pmp0_newaddr pmpcfg0 pmpaddr00 va5_55) 0) = false ->
      pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
        (Z.mul (uint (vec_access_dec (pmp0_newaddr pmpcfg0 pmpaddr00 va5_55) 0)) 4)
        (uint (fetch_pa (mword_of_int 0x80000e82 : mword 64))) (uint (to_bits 64 2)) = PMP_Match ->
      eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg1 0)) ('b"1") = true ->
      eq_vec (celpv lpe mstatus1) (landing_pad_bits_backwards LP_EXPECTED) = false ->
      (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
         exec (ext_decode_compressed (mword_of_int 0x1141 : mword 16)) s0
           = Some (C_ADDI (imm6, Regidx rd), s0)) ->
      PC ↦ᵣ kpc0 -∗ gpr_file m -∗
      mhartid ↦ᵣ mhartid0 -∗
      nextPC ↦ᵣ kpc0 -∗ (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
      cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
      (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
      elp ↦ᵣ elp0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗
      hw_config misa0 mseccfg0 mc mcfg pmar0 -∗
      ([∗ list] j ∈ seq 0 8, (pa_add pal j) ↦ₘ nth_byte v j) -∗
      menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
      mepc ↦ᵣ mepc0 -∗ satp ↦ᵣ satp0 -∗ medeleg ↦ᵣ medeleg0 -∗ mie ↦ᵣ mie0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗
      ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte vold_ra j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte vold_s0 j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add tpa_ra j) ↦ₘ nth_byte vti_ra j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add tpa_s0 j) ↦ₘ nth_byte vti_s0 j) -∗
      kernel_text -∗
      ▷ ( (∃ (mf' : gmap register_bitvector_64 (mword 64)) (mstf' : mword 64),
            PC ↦ᵣ add_vec_int (mword_of_int 0x80000e82) 2 ∗
            nextPC ↦ᵣ add_vec_int (mword_of_int 0x80000e82) 2 ∗
            gpr_file mf' ∗
            (R_bool minstret_increment) ↦ᵣ b1s ∗ minstret ↦ᵣ mstf' ∗
            cur_privilege ↦ᵣ Supervisor ∗ hart_state ↦ᵣ HART_ACTIVE tt ∗
            (R_bitvector_64 mideleg) ↦ᵣ mdv0 ∗ (R_bitvector_64 mstatus) ↦ᵣ cms5 mstatus1 ∗
            satp ↦ᵣ satp_legalized satp0 va5_45 ∗ mie ↦ᵣ sie_new_mie mie0 mdv0 va5_52 ∗
            elp ↦ᵣ celpv lpe mstatus1 ∗
            pmpcfg_n ↦ᵣ pmpcfg1 ∗ pmpaddr_n ↦ᵣ pmp0_newaddr pmpcfg0 pmpaddr00 va5_55)
          -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }} ) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros bb sp1e eal a8l pal bumpe mst1 x2ld x10l x11c x11a x10m x2add x1j m8
           sp1 imm_ra pa_ra imm_s0 pa_s0 a8_ra a8_s0 va5_c2 va4_35 va4_36 va5_37 va4_38 va4_39 va5_40 mstatus1
           va5_42 va5_43 va5_45 va5_47 va5_48 mdv0 va5_51 va5_52 va5_54 va5_55 va5_57 pmpcfg1
           c6sp tpa_ra tpa_s0 ta8_ra ta8_s0.
    intros Hm1 Hm2 Hm10 Hm11 Hm8 Hm14 Hm15 Hm4 Hpmaall Hpmpf HmIE Hlp HMPRV Hpmm Ha8l Hpall HmisaC HmisaM HmisaS HmisaU
           HmIE1 HSXL1 Hsa8ra Hspara Hsa8s0 Hspas0 HMPRV1 Hmlpe Hpmpf1 Hta8ra Htpara Hta8s0 Htpas0 Hnp Hnpm Hlpe
           Hrd2 Hnpsup Hb1s Hsatp_bare HSXL_s HSIE_s Hmie_mdl HA0 Hord0 Hrange0 HX0 Help_s Hdec.
    subst newpriv.
    iIntros "Hpc Hfile Hmh Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hpmpc #Hhw Hbytes
             Hmenv Hmcen Hmtime Hstc Hmepc Hsatp Hmede Hmie Hpmpaddr Hstkra Hstks0 Htra Htrs0 HK Hcont".
    iPoseProof "Hhw" as "#Hhwc". iDestruct "Hhwc" as "#(Hmisa & Hsec & Hmcinh & Hmcfg & Hpma & Hhtif & _ & _ & _ & _ & _)".
    (* ---- run the whole boot path up to and including the MRET ---- *)
    iApply (wp_kernel v sp0b mst0 mstatus0 mi0 elp0 mc mcfg mseccfg0 pmpcfg0 pmar0
              x1_0 x10_0 x11_0 mhartid0 misa0 m menvcfg0 mtime0 stimecmp0 mepc0 satp0 medeleg0 mie0
              mcounteren0 pmpaddr00 vs0b va4b va5b vold_ra vold_s0 vti_ra vti_s0 Supervisor lpe E Φ
              Hm1 Hm2 Hm10 Hm11 Hm8 Hm14 Hm15 Hm4 Hpmaall Hpmpf HmIE Hlp HMPRV Hpmm Ha8l Hpall
              HmisaC HmisaM HmisaS HmisaU HmIE1 HSXL1 Hsa8ra Hspara Hsa8s0 Hspas0 HMPRV1 Hmlpe Hpmpf1
              Hta8ra Htpara Hta8s0 Htpas0 Hnp Hnpm Hlpe
              with "Hpc Hfile Hmh Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hpmpc Hhw
                    Hbytes Hmenv Hmcen Hmtime Hstc Hmepc Hsatp Hmede Hmie Hpmpaddr Hstkra Hstks0 Htra Htrs0 HK").
    iNext.
    iDestruct 1 as (mf mstf)
      "(Hpc & Hnpc & Hfile & %Hsp & Hmh & Hmi & Hmst & Hpriv & %Hnpriv & Hhs & Hmdl & Hms & Hmepc &
        Hsatp & Help & Hpmpc & Hpmpaddr & Hmie & H)".
    (* PC = ctgt (mepc_val va5_43) = 0x80000e82 = <main> *)
    assert (Hpceq : ctgt (mepc_val va5_43) = (mword_of_int 0x80000e82 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpceq) in "Hpc". iEval (rewrite Hpceq) in "Hnpc".
    (* extract main's first-instruction window from the (persistent) kernel_text *)
    iAssert (kinstr_bytes (skinstr 1304)) as "#Kmain". { sg 1304. }
    assert (Hk_a : ki_addr (skinstr 1304) = 0x80000e82) by (vm_compute; reflexivity).
    assert (Hk_e : ki_enc (skinstr 1304) = 0x1141) by (vm_compute; reflexivity).
    assert (Hk_w : (2 <= ki_width (skinstr 1304) / 8)%nat) by (vm_compute; lia).
    iDestruct (kinstr_window16 (skinstr 1304) 0x80000e82 0x1141 Hk_a Hk_e Hk_w with "Kmain") as "#Wmain".
    destruct Hsp as [vd Hsp].
    (* ---- run the first Supervisor-mode instruction (c.addi sp,sp,-16) ---- *)
    iApply (wp_smode_caddi (mword_of_int 0x80000e82) (mword_of_int 0x1141 : mword 16) rd imm6
              mf vd misa0 mdv0 (cms5 mstatus1) (satp_legalized satp0 va5_45)
              (sie_new_mie mie0 mdv0 va5_52) b1s
              (mword_of_int 0x80000e82) mstf mc mcfg pmpcfg1 (pmp0_newaddr pmpcfg0 pmpaddr00 va5_55)
              pmar0 bb (celpv lpe mstatus1) E (dq := DfracDiscarded) DfracDiscarded Φ
              ltac:(rewrite Hrd2; discriminate)
              ltac:(rewrite Hrd2; exact Hsp)
              Hsatp_bare HSXL_s Hpmaall HA0 Hord0 Hrange0 HX0
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              HmisaC HmisaS Hdec Hb1s
              Hmie_mdl HSIE_s Help_s
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Hmie Help Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Wmain").
    iNext.
    iIntros "Hpc2 Hfile2 Hmisa2 Hnpc2 Hmi2 Hmst2 Hpriv2 Hhs2 Hmdl2 Hms2 Hsatp2 Hmie2 Help2 Hmcinh2 Hmcfg2 Hpmpc2 Hpmpaddr2 Hpma2 Hhtif2 _".
    iApply "Hcont".
    iExists _, _. iFrame.
  Qed.

End WpSmode.
