(* WpSconfCtl.v -- the SIE-AGNOSTIC control-flow leaf layer
   (interrupt-sweep stage 5): [sconf]+[sie_cap] twins of
   WpSmodePtCtl.v's fence / c.j / jal / c.ret leaves over the agnostic
   funnel [wp_instr_s_sconf].

   Spec cleanups made in this pass:
     - the config premises are gone as everywhere in the sweep;
     - [wp_cj_s_sconf] hands the step's later out: an unconditional
       backward jump is a loop back edge exactly like a taken branch
       (the `_pt` original absorbed it); jal/c.ret keep the later-free
       shape (call/return sites are straight-line);
     - jal carries the sweep's [rd <> csp_rs1] premise (link-register
       write); c.j and c.ret write no register, so [sconf]/[sie_cap]
       pass through (c.j untouched, c.ret opened only for the
       LPE/priv/misa side conditions).
   The csrr/csrrci-sstatus and sret leaves are NOT here: sret runs in
   kernelvec's SIE=0 body and the csr flips are stage 7.               *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes WpDecode WpLeafCommon WpGpr WpGprCsrwCommon.
Require Import SmodeCore.
Require Import KptTree WpSmodePtCtl.
Require Import WpMmodeLeafBase.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Import Defs.

(* ---- Local helpers (copies: the originals are Local in WpSmodePtCtl.v /
   WpSpinNew.v; [exec_execute_FENCE_rw_w] is exported and imported). ---- *)
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

Local Lemma exec_execute_JAL_zreg_zca (imm : mword 21) s :
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute_JAL imm zreg) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Halign Hzca.
    unfold execute_JAL, get_next_pc.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
    cbn match.
    unfold zreg.
    rewrite (exec_bind0_Some _ _ _ _ _
      (exec_wX_bits_gpr (zero_extend' 5 ('b"00")) (register_lookup nextPC s.(sregs))
         (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))))).
    apply exec_returnm.
  Qed.

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

Section WpSconfCtl.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* fence rw,w -- state-preserving; the config is opened only for the    *)
  (* priv/menvcfg side conditions.                                        *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_fence_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (m : gmap regidx (mword 64)) :
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4,
                           Regidx (mword_of_int 0), Regidx (mword_of_int 0))) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc false
              (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4,
                      Regidx (mword_of_int 0), Regidx (mword_of_int 0)))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hmenv") as %Lmenv.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_FENCE_rw_w menvcfg0 s_pc Lpriv_pc Lmenv_pc Hfiom). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' [Hpriv Hmsx Hmiex Hmenv] Hcap Htlbinv [$Hpc' $Hnpc] Hfile").
    iFrame "Hhw Hminv Hpriv Hmsx Hmiex".
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.j -- unconditional jump; a backward jump is a loop back edge, so   *)
  (* the continuation is UNDER A LATER (straight-line callers [iNext]).   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_cj_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (jimm : mword 21)
      (m : gmap regidx (mword 64)) :
    let tgt := add_vec pc (sign_extend' 64 jimm) in
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (JAL (jimm, zreg)) -∗
    ( ▷ ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
      pc_is tgt -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros tgt Hal0.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc true (JAL (jimm, zreg))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    assert (HzcaC : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
    assert (Halign_spc : eq_vec (access_vec_dec
              (add_vec (register_lookup PC s_pc.(sregs)) (sign_extend' 64 jimm)) 0) ('b"0") = true).
    { rewrite Hpcv. exact Hal0. }
    iMod (reg_update _ nextPC _ tgt with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC tgt).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc.
      change (execute (JAL (jimm, zreg))) with (execute_JAL jimm zreg).
      rewrite (exec_execute_JAL_zreg_zca jimm s_pc Halign_spc
                 (exec_currentlyEnabled_Zca s_pc HzcaC)).
      rewrite Hpcv. reflexivity. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc nextPC tgt).(sregs) = tgt)
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply ("Hcont" with "Hhs' [$Hhw $Hsc2] Hcap Htlbinv [$Hpc' $Hnpc] Hfile").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* jal rd -- link write + jump.                                         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_jal_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 21)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (JAL (imm, Regidx rd)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hal0) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc false (JAL (imm, Regidx rd))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
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
      change (if false then 2%Z else 4%Z) with 4%Z.
      change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
      rewrite (exec_execute_JAL_gpr_zca imm rd (set_reg σ nextPC (add_vec_int pc 4))
                 Hrd ltac:(rewrite Hpcv; exact Hal0)
                 (exec_currentlyEnabled_Zca (set_reg σ nextPC (add_vec_int pc 4)) ltac:(rewrite Lmisa1; exact HmisaC))).
      rewrite Hpcv. rewrite Hlink. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                         nextPC (add_vec pc (sign_extend' 64 imm)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec_int pc 4))).(sregs)
             = add_vec pc (sign_extend' 64 imm)).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m !!! Regidx csp_rs1)
      by (symmetry; apply lookup_total_insert_ne; exact Hspne).
    iDestruct (sie_cap_retarget γ root_ppn m
                 (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) Hsp with "Hcap") as "Hcap".
    iApply ("Hcont" with "Hhs' [$Hhw $Hsc2] Hcap Htlbinv [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.ret (jalr x0, 0(ra)) -- no register write; the bundle is opened    *)
  (* for the LPE/priv/misa side conditions and reassembled.               *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_cret_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (ra : mword 5)
      (m : gmap regidx (mword 64)) :
    let tgt := update_vec_dec (add_vec (m !!! Regidx ra) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    uint ra <> 0 ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
      pc_is tgt -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros tgt Hra Halign.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc true (JALR (zeros' 12, Regidx ra, zreg))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & %HmisaC & _)".
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hma : m !! Regidx ra = Some (m !!! Regidx ra))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfb]".
    iDestruct (gpr_pt_value ra (m !!! Regidx ra) s_pc with "Hreg Hrac") as %Lra.
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
    iApply ("Hcont" with "Hhs' [Hpriv Hmsx Hmiex Hmenv] Hcap Htlbinv [$Hpc' $Hnpc] [Hfmap]").
    { iFrame "Hhw Hminv Hpriv Hmsx Hmiex".
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

End WpSconfCtl.
