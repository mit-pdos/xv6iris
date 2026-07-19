(* ===================================================================== *)
(* UserExecProducer.v -- the generic EXECUTE-STEP PRODUCER.               *)
(*                                                                        *)
(* Factors the common fetch -> decode -> progress-composer -> classify    *)
(* pipeline ONCE, so a classification proves only the per-family EXECUTE   *)
(* facts.  Given the two execute totalities (base = 4-byte via ext_decode; *)
(* RVC = 2-byte via ext_decode_compressed with the ExecuteAs expansion),   *)
(* [user_exec_step_producer] fetches over the user invariant               *)
(* ([user_pt_fetch_instr]), cases on isRVC, drives the matching progress   *)
(* composer ([exec_hart_active_progress_base_gen] / [_RVC_gen], both       *)
(* result-generic), and packages the result-parameterized                 *)
(* [exec_step_obligation] (UserStepExec) -- which [exec_step_branch] then   *)
(* turns into the step, dispatching retire-vs-trap on the runtime result.  *)
(* No family forks the arm; only the execute totalities vary, and each     *)
(* memory family's totality is discharged by the UserMemAccess composers.  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv WpGpr.
Require Import WpLeafCommon WpIntrCore.
Require Import SmodeCore.
Require Import UserPtTree UserExec UserStep UserTrap UserCompute UserArms UserFetch UserFetchPt UserStepExec.
Local Open Scope Z_scope.
Import Defs.

Section UserExecProducer.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* The post-fetch config facts an execute totality assumes. *)
  Definition post_fetch_cfg (σf : mstate) (va : mword 64) (miσ : bool) : Prop :=
    register_lookup PC σf.(sregs) = va /\
    register_lookup cur_privilege σf.(sregs) = User /\
    _get_Mstatus_SXL (register_lookup mstatus σf.(sregs)) = 'b"10" /\
    register_lookup menvcfg σf.(sregs) = MENVCFG_S /\
    register_lookup (R_bool minstret_increment) σf.(sregs) = miσ.

  (* BASE execute totality (4-byte, offset 4): decode w -> instr, execute it. *)
  Definition base_exec_total (E : coPset) (σ : mstate) (va : mword 64)
      (g : gmap regidx (mword 64)) : iProp Σ :=
    (∀ (w : mword 32) (σf : mstate),
       ⌜post_fetch_cfg σf va (register_lookup (R_bool minstret_increment) σ.(sregs))⌝ -∗
       mstate_interp (set_reg σf nextPC (add_vec_int va 4)) -∗
       gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
       |={E}=>
         ∃ (instr : instruction) (r : ExecutionResult) (s_x : mstate)
           (g' : gmap regidx (mword 64)) (va' : mword 64),
           ⌜exec (ext_decode w) σf = Some (instr, σf)⌝ ∗
           ⌜is_lpad_instruction instr = false⌝ ∗
           ⌜exec (execute instr) (set_reg σf nextPC (add_vec_int va 4)) = Some (r, s_x)⌝ ∗
           ⌜exec_step_result_ok r⌝ ∗
           ⌜match r with ExecuteAs _ => False | _ => True end⌝ ∗
           ⌜register_lookup hart_state s_x.(sregs) = HART_ACTIVE tt⌝ ∗
           ⌜register_lookup (R_bool minstret_increment) s_x.(sregs)
              = register_lookup (R_bool minstret_increment) σ.(sregs)⌝ ∗
           ⌜register_lookup nextPC s_x.(sregs) = va'⌝ ∗
           mstate_interp s_x ∗ gpr_file g' ∗ nextPC ↦ᵣ va' ∗
           user_pt_inv pt ∗ user_cfg C)%I.

  (* RVC execute totality (2-byte, offset 2): decode_compressed h -> instr,
     execute instr -> ExecuteAs other, execute the expansion [other]. *)
  Definition rvc_exec_total (E : coPset) (σ : mstate) (va : mword 64)
      (g : gmap regidx (mword 64)) : iProp Σ :=
    (∀ (h : mword 16) (σf : mstate),
       ⌜post_fetch_cfg σf va (register_lookup (R_bool minstret_increment) σ.(sregs))⌝ -∗
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
           ⌜exec_step_result_ok r⌝ ∗
           ⌜match r with ExecuteAs _ => False | _ => True end⌝ ∗
           ⌜register_lookup hart_state s_x.(sregs) = HART_ACTIVE tt⌝ ∗
           ⌜register_lookup (R_bool minstret_increment) s_x.(sregs)
              = register_lookup (R_bool minstret_increment) σ.(sregs)⌝ ∗
           ⌜register_lookup nextPC s_x.(sregs) = va'⌝ ∗
           mstate_interp s_x ∗ gpr_file g' ∗ nextPC ↦ᵣ va' ∗
           user_pt_inv pt ∗ user_cfg C)%I.

  Lemma user_exec_step_producer (E : coPset) (σ : mstate) (va : mword 64)
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
    base_exec_total E σ va g -∗
    rvc_exec_total E σ va g -∗
    exec_step_obligation C pt E σ va g.
  Proof.
    intros Hum Hleaf Hal Hcanon Hmisa Hmenv Hhtif HSXL Hall Help.
    iIntros "Htb Htr %Hpre Hint Hgpr Hnpc Hupt Hcfg".
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
      iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
      iMod ("Htr" $! (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0) σf Hcfgf
              with "[Hreg Hgh Hdev] Hgpr Hnpc [Hutlb Hudata] Hcfg")
        as (instr other r s_x g' va') "(%Hdec & %Hzca & %Hex1 & %Hex2 & %Hok & %Hnex & %Hhx & %Hmix & %Lnpcx & Hint & Hgpr & Hnpc & Hupt & Hcfg)".
      { unfold mstate_interp; cbn [sregs mem mdev]. rewrite Hmdev. iFrame "Hreg Hgh Hdev". }
      { iFrame "Hutlb Hudata". iPureIntro; split; assumption. }
      pose proof (exec_hart_active_progress_RVC_gen User σ σf s_x
                    (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0)
                    instr other va r Hcp Hdisp Hfetch Hdec LelpF LpcF Hzca Hex1 Hex2) as Hrun.
      iModIntro. iExists r, (zero_extend' 32 (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0)), s_x, g', va'.
      iFrame "Hint Hgpr Hnpc Hupt Hcfg".
      iPureIntro. repeat split; try assumption.
    - (* F_Base *)
      iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
      iMod ("Htb" $! (autocast (T := mword) iw) σf Hcfgf
              with "[Hreg Hgh Hdev] Hgpr Hnpc [Hutlb Hudata] Hcfg")
        as (instr r s_x g' va') "(%Hdec & %Hlpad & %Hex & %Hok & %Hnex & %Hhx & %Hmix & %Lnpcx & Hint & Hgpr & Hnpc & Hupt & Hcfg)".
      { unfold mstate_interp; cbn [sregs mem mdev]. rewrite Hmdev. iFrame "Hreg Hgh Hdev". }
      { iFrame "Hutlb Hudata". iPureIntro; split; assumption. }
      pose proof (exec_hart_active_progress_base_gen User σ σf s_x
                    (autocast (T := mword) iw) instr va r
                    Hcp Hdisp Hfetch Hdec LelpF Hlpad LpcF Hex Hnex) as Hrun.
      iModIntro. iExists r, (zero_extend' 32 (autocast (T := mword) iw : mword 32)), s_x, g', va'.
      iFrame "Hint Hgpr Hnpc Hupt Hcfg".
      iPureIntro. repeat split; try assumption.
  Qed.

  (* ===================================================================== *)
  (* The FETCH-FAULT half of the classification.  Where the success        *)
  (* producer needs a fetchable leaf (um !! svpn = Some w, uleaf_ok), these *)
  (* discharge [fetch_fault_obligation] from the UserFetchPt fault          *)
  (* composers: the fetch faults, [exec_run_hart_active_fetch_failure]      *)
  (* lifts it to [Step_Fetch_Failure], and (all these geometries leave the  *)
  (* state unchanged) the invariant re-frames trivially.  user_exc holds by *)
  (* reflexivity for both causes.  The 2-aligned SECOND-halfword fault is a *)
  (* disjunction (RVC success OR high-half fault, with a TLB-filled state)  *)
  (* and belongs with the split success producer (classification, item A);  *)
  (* it is not a single-outcome fault corollary.                            *)
  (* ===================================================================== *)

  (* Odd pc: E_Fetch_Addr_Align, before any translation, state unchanged. *)
  Lemma user_fetch_fault_producer_align (E : coPset) (σ : mstate) (va : mword 64) :
    neq_vec (access_vec_dec va 0) ('b"0") = true ->
    register_lookup hart_state σ.(sregs) = HART_ACTIVE tt ->
    ⊢ fetch_fault_obligation C pt E σ va.
  Proof.
    intros Hbit0 Hhart.
    iIntros "%Hpre Hint Hupt Hcfg".
    destruct Hpre as (Hdisp & Hcp & Lpc & Hmsok).
    pose proof (exec_fetch_align_fault σ va Lpc Hbit0) as Hfetch.
    pose proof (exec_run_hart_active_fetch_failure User σ σ va (E_Fetch_Addr_Align tt)
                  Hcp Hdisp Hfetch) as Hrun.
    iModIntro. iExists σ, (E_Fetch_Addr_Align tt), va.
    iFrame "Hint Hupt Hcfg". iPureIntro. repeat split; try assumption; reflexivity.
  Qed.

  (* 4-aligned pc whose walk faults (non-canonical / unmapped / denied all  *)
  (* collapse to E_Fetch_Page_Fault at the user tables), state unchanged.   *)
  Lemma user_fetch_fault_producer (E : coPset) (σ : mstate) (va : mword 64) :
    u_fetch_fault_flavor pt.(ud_tfp) pt.(ud_um) va ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    register_lookup hart_state σ.(sregs) = HART_ACTIVE tt ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    ⊢ fetch_fault_obligation C pt E σ va.
  Proof.
    intros Hflavor Hal Hhart Hhtif Hall.
    iIntros "%Hpre Hint Hupt Hcfg".
    destruct Hpre as (Hdisp & Hcp & Lpc & Hmsok).
    iDestruct "Hint" as "(Hreg & Hgh & Hdev)".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    iDestruct (user_pt_fetch_fault pt.(ud_root) pt.(ud_tfp) pt.(ud_um) va σ
                 Hflavor Hal Lpc Hhtif Hcp (proj1 Hmsok) Hall with "Hreg Hgh Hutlb") as %Hfetch.
    pose proof (exec_run_hart_active_fetch_failure User σ σ va (E_Fetch_Page_Fault tt)
                  Hcp Hdisp Hfetch) as Hrun.
    iModIntro. iExists σ, (E_Fetch_Page_Fault tt), va.
    iSplitR; [iPureIntro; exact Hrun|].
    iSplitR; [iPureIntro; reflexivity|].
    iSplitR; [iPureIntro; exact Hhart|].
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "Hreg Hgh Hdev"; [unfold mstate_interp; iFrame "Hreg Hgh Hdev"|].
    iSplitL "Hutlb Hudata"; [unfold user_pt_inv; iFrame "Hutlb Hudata"; iPureIntro; split; assumption|].
    iFrame "Hcfg".
  Qed.

  (* 2-aligned (not 4-aligned) pc whose LOW halfword's page faults: same    *)
  (* single-outcome E_Fetch_Page_Fault at va, state unchanged.              *)
  Lemma user_fetch_fault_producer_2_first (E : coPset) (σ : mstate) (va : mword 64) :
    u_fetch_fault_flavor pt.(ud_tfp) pt.(ud_um) va ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = false ->
    register_lookup hart_state σ.(sregs) = HART_ACTIVE tt ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    ⊢ fetch_fault_obligation C pt E σ va.
  Proof.
    intros Hflavor Hbit0 Hbit1 Hnal4 Hhart Hmisa Hhtif Hall.
    iIntros "%Hpre Hint Hupt Hcfg".
    destruct Hpre as (Hdisp & Hcp & Lpc & Hmsok).
    iDestruct "Hint" as "(Hreg & Hgh & Hdev)".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    iDestruct (user_pt_fetch_fault_2_first pt.(ud_root) pt.(ud_tfp) pt.(ud_um) va σ
                 Hflavor Hbit0 Hbit1 Hnal4 Lpc Hmisa Hhtif Hcp (proj1 Hmsok) Hall
                 with "Hreg Hgh Hutlb") as %Hfetch.
    pose proof (exec_run_hart_active_fetch_failure User σ σ va (E_Fetch_Page_Fault tt)
                  Hcp Hdisp Hfetch) as Hrun.
    iModIntro. iExists σ, (E_Fetch_Page_Fault tt), va.
    iSplitR; [iPureIntro; exact Hrun|].
    iSplitR; [iPureIntro; reflexivity|].
    iSplitR; [iPureIntro; exact Hhart|].
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "Hreg Hgh Hdev"; [unfold mstate_interp; iFrame "Hreg Hgh Hdev"|].
    iSplitL "Hutlb Hudata"; [unfold user_pt_inv; iFrame "Hutlb Hudata"; iPureIntro; split; assumption|].
    iFrame "Hcfg".
  Qed.

End UserExecProducer.
