From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv WpGpr UserBits.
Require Import WpLeafCommon WpIntrCore SmodeCore.
Require Import UserPtTree UserExec UserStep UserTrap UserCompute UserArms UserFetch UserFetchPt UserStepExec UserExecProducer UserClassify.
Local Open Scope Z_scope.
Import Defs.

Section UserExecProducerU.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* 5-way BASE totality: decode w -> instr; execute (possibly one base
     ExecuteAs redirect, e.g. SINVAL_VMA) -> r with u_result_ok r. *)
  Definition base_exec_total_u (E : coPset) (σ : mstate) (va : mword 64)
      (g : gmap regidx (mword 64)) : iProp Σ :=
    (∀ (w : mword 32) (σf : mstate),
       ⌜post_fetch_cfg σf va (register_lookup (R_bool minstret_increment) σ.(sregs))⌝ -∗
       hw_config -∗
       mstate_interp (set_reg σf nextPC (add_vec_int va 4)) -∗
       gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
       |={E}=>
         ∃ (instr : instruction) (r : ExecutionResult) (s_x : mstate)
           (g' : gmap regidx (mword 64)) (va' : mword 64),
           ⌜exec (ext_decode w) σf = Some (instr, σf)⌝ ∗
           ⌜is_lpad_instruction instr = false⌝ ∗
           ⌜exec (execute instr) (set_reg σf nextPC (add_vec_int va 4)) = Some (r, s_x)
            \/ (exists other,
                  exec (execute instr) (set_reg σf nextPC (add_vec_int va 4))
                    = Some (ExecuteAs other, set_reg σf nextPC (add_vec_int va 4))
                  /\ exec (execute other) (set_reg σf nextPC (add_vec_int va 4)) = Some (r, s_x))⌝ ∗
           ⌜u_result_ok r⌝ ∗
           ⌜match r with ExecuteAs _ => False | _ => True end⌝ ∗
           ⌜register_lookup hart_state s_x.(sregs) = HART_ACTIVE tt⌝ ∗
           ⌜register_lookup (R_bool minstret_increment) s_x.(sregs)
              = register_lookup (R_bool minstret_increment) σ.(sregs)⌝ ∗
           ⌜register_lookup nextPC s_x.(sregs) = va'⌝ ∗
           mstate_interp s_x ∗ gpr_file g' ∗ nextPC ↦ᵣ va' ∗ user_pt_inv pt ∗ user_cfg C)%I.

  (* 5-way RVC totality: decode_compressed h -> instr; execute -> ExecuteAs
     other; execute other -> r with u_result_ok r. *)
  Definition rvc_exec_total_u (E : coPset) (σ : mstate) (va : mword 64)
      (g : gmap regidx (mword 64)) : iProp Σ :=
    (∀ (h : mword 16) (σf : mstate),
       ⌜post_fetch_cfg σf va (register_lookup (R_bool minstret_increment) σ.(sregs))⌝ -∗
       hw_config -∗
       mstate_interp (set_reg σf nextPC (add_vec_int va 2)) -∗
       gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
       |={E}=>
         ∃ (instr other : instruction) (r : ExecutionResult) (s_x : mstate)
           (g' : gmap regidx (mword 64)) (va' : mword 64),
           ⌜exec (ext_decode_compressed h) σf = Some (instr, σf)⌝ ∗
           ⌜exec (currentlyEnabled Ext_Zca) σf = Some (true, σf)⌝ ∗
           ⌜exec (execute instr) (set_reg σf nextPC (add_vec_int va 2))
              = Some (ExecuteAs other, set_reg σf nextPC (add_vec_int va 2))⌝ ∗
           ⌜exec (execute other) (set_reg σf nextPC (add_vec_int va 2)) = Some (r, s_x)⌝ ∗
           ⌜u_result_ok r⌝ ∗
           ⌜match r with ExecuteAs _ => False | _ => True end⌝ ∗
           ⌜register_lookup hart_state s_x.(sregs) = HART_ACTIVE tt⌝ ∗
           ⌜register_lookup (R_bool minstret_increment) s_x.(sregs)
              = register_lookup (R_bool minstret_increment) σ.(sregs)⌝ ∗
           ⌜register_lookup nextPC s_x.(sregs) = va'⌝ ∗
           mstate_interp s_x ∗ gpr_file g' ∗ nextPC ↦ᵣ va' ∗ user_pt_inv pt ∗ user_cfg C)%I.

  (* Lift a completed fetch to active_step_obligation (Step_Execute case). *)
  Lemma user_exec_step_from_fetch_u (E : coPset) (σ σf : mstate) (va : mword 64)
      (g : gmap regidx (mword 64)) (iw : mword 32) :
    register_lookup cur_privilege σ.(sregs) = User ->
    exec (dispatchInterrupt User) σ = Some (None, σ) ->
    register_lookup PC σ.(sregs) = va ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    eq_vec (register_lookup elp σ.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    (forall r : register, register_beq r tlb = false ->
       register_lookup r σf.(sregs) = register_lookup r σ.(sregs)) ->
    exec (fetch tt) σ
      = Some ((if isRVC (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0)
               then F_RVC (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0)
               else F_Base (autocast (T := mword) iw)), σf) ->
    hw_config -∗
    base_exec_total_u E σ va g -∗ rvc_exec_total_u E σ va g -∗
    mstate_interp σf -∗ gpr_file g -∗ nextPC ↦ᵣ va -∗ user_pt_inv pt -∗ user_cfg C -∗
    |={E}=>
      ∃ (st : Step) (s_x : mstate) (g' : gmap regidx (mword 64)) (va' : mword 64),
        ⌜exec (run_hart_active 0) σ = Some (st, s_x)⌝ ∗
        ⌜u_step_outcome st⌝ ∗
        ⌜register_lookup hart_state s_x.(sregs) = HART_ACTIVE tt⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs)
           = register_lookup (R_bool minstret_increment) σ.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = va'⌝ ∗
        mstate_interp s_x ∗ gpr_file g' ∗ nextPC ↦ᵣ va' ∗ user_pt_inv pt ∗ user_cfg C.
  Proof.
    intros Hcp Hdisp Lpc HSXL Hmenv Help Tr Hfetch.
    iIntros "#Hhw Htb Htr Hint2 Hgpr2 Hnpc2 Hupt2 Hcfg2".
    iDestruct "Hint2" as "(Hreg & Hgh & Hdev)".
    iDestruct "Hupt2" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    assert (Hcfgf : post_fetch_cfg σf va (register_lookup (R_bool minstret_increment) σ.(sregs))).
    { unfold post_fetch_cfg. repeat split.
      - rewrite (Tr PC ltac:(vm_compute; reflexivity)); exact Lpc.
      - rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp.
      - rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact HSXL.
      - rewrite (Tr menvcfg ltac:(vm_compute; reflexivity)); exact Hmenv.
      - apply Tr; vm_compute; reflexivity. }
    assert (LelpF : eq_vec (register_lookup elp σf.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite (Tr elp ltac:(vm_compute; reflexivity)); exact Help).
    assert (LpcF : register_lookup PC σf.(sregs) = va) by (rewrite (Tr PC ltac:(vm_compute; reflexivity)); exact Lpc).
    destruct (isRVC (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0)) eqn:Hrvc.
    - (* F_RVC *)
      iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc2") as "[Hreg Hnpc2]".
      iMod ("Htr" $! (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0) σf Hcfgf
              with "Hhw [Hreg Hgh Hdev] Hgpr2 Hnpc2 [Hutlb Hudata] Hcfg2")
        as (instr other r s_x g' va') "(%Hdec & %Hzca & %Hex1 & %Hex2 & %Hok & %Hnex & %Hhx & %Hmix & %Lnpcx & Hint & Hgpr & Hnpc & Hupt & Hcfg)".
      { unfold mstate_interp; cbn [sregs mem mdev]. iFrame "Hreg Hgh Hdev". }
      { iFrame "Hutlb Hudata". iPureIntro; split; assumption. }
      pose proof (exec_hart_active_progress_RVC_gen User σ σf s_x
                    (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0)
                    instr other va r Hcp Hdisp Hfetch Hdec LelpF LpcF Hzca Hex1 Hex2) as Hrun.
      iModIntro.
      iExists (Step_Execute (r, zero_extend' 32 (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0))), s_x, g', va'.
      iFrame "Hint Hgpr Hnpc Hupt Hcfg".
      iPureIntro. split; [exact Hrun|]. split; [| repeat split; assumption].
      left. eexists r, _. split; [reflexivity | exact Hok].
    - (* F_Base *)
      iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc2") as "[Hreg Hnpc2]".
      iMod ("Htb" $! (autocast (T := mword) iw) σf Hcfgf
              with "Hhw [Hreg Hgh Hdev] Hgpr2 Hnpc2 [Hutlb Hudata] Hcfg2")
        as (instr r s_x g' va') "(%Hdec & %Hlpad & %Hexd & %Hok & %Hnex & %Hhx & %Hmix & %Lnpcx & Hint & Hgpr & Hnpc & Hupt & Hcfg)".
      { unfold mstate_interp; cbn [sregs mem mdev]. iFrame "Hreg Hgh Hdev". }
      { iFrame "Hutlb Hudata". iPureIntro; split; assumption. }
      assert (Hrun : exec (run_hart_active 0) σ
                = Some (Step_Execute (r, zero_extend' 32 (autocast (T := mword) iw : mword 32)), s_x)).
      { destruct Hexd as [Hexd | (other & Hex1 & Hex2)].
        - exact (exec_hart_active_progress_base_gen User σ σf s_x
                   (autocast (T := mword) iw) instr va r Hcp Hdisp Hfetch Hdec LelpF Hlpad LpcF Hexd Hnex).
        - exact (exec_hart_active_progress_base_redirect_gen User σ σf s_x
                   (autocast (T := mword) iw) instr other va r Hcp Hdisp Hfetch Hdec LelpF Hlpad LpcF Hex1 Hex2). }
      iModIntro.
      iExists (Step_Execute (r, zero_extend' 32 (autocast (T := mword) iw : mword 32))), s_x, g', va'.
      iFrame "Hint Hgpr Hnpc Hupt Hcfg".
      iPureIntro. split; [exact Hrun|]. split; [| repeat split; assumption].
      left. eexists r, _. split; [reflexivity | exact Hok].
  Qed.

  (* The fetch-success producer for the unified obligation (4-aligned). *)
  Lemma user_exec_step_producer_u (E : coPset) (σ : mstate) (va : mword 64)
      (g : gmap regidx (mword 64)) (w_leaf : mword 64) :
    pt.(ud_um) !! svpn_of va = Some w_leaf ->
    uleaf_ok (InstructionFetch tt) w_leaf ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    eq_vec (register_lookup elp σ.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    hw_config -∗
    base_exec_total_u E σ va g -∗ rvc_exec_total_u E σ va g -∗
    active_step_obligation C pt E σ va g.
  Proof.
    intros Hum Hleaf Hal Hcanon Hmisa Hmenv Hhtif HSXL Hall Help.
    iIntros "#Hhw Htb Htr %Hpre Hint Hgpr Hnpc Hupt Hcfg".
    destruct Hpre as (Hdisp & Hcp & Lpc & Hmsok).
    iDestruct "Hint" as "(Hreg & Hgh & Hdev)".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    iMod (user_pt_fetch_instr pt.(ud_root) pt.(ud_tfp) pt.(ud_um) pt.(ud_data)
            w_leaf va σ Hum Hleaf Hcov Hal Lpc Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hall
            with "Hreg Hgh Hutlb Hudata")
      as (iw σf) "(%Hfetch & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σf.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne. destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iApply (user_exec_step_from_fetch_u E σ σf va g iw
              Hcp Hdisp Lpc HSXL Hmenv Help Tr Hfetch
              with "Hhw Htb Htr [Hreg Hgh Hdev] Hgpr Hnpc [Hutlb Hudata] Hcfg").
    - unfold mstate_interp; cbn [sregs mem mdev]. rewrite Hmdev. iFrame "Hreg Hgh Hdev".
    - unfold user_pt_inv. iFrame "Hutlb Hudata". iPureIntro; split; assumption.
  Qed.

End UserExecProducerU.
