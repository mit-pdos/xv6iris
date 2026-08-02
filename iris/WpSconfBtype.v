(* WpSconfBtype.v -- the SIE-AGNOSTIC branch leaf layer (interrupt-sweep
   stage 5): [sconf]+[sie_cap] twins of WpSmodePtBtype.v's leaves over
   the agnostic funnel [wp_instr_s_sconf].

   Branches write NO general register, so [sie_cap] passes through
   UNTOUCHED (no retarget, no rd premises); a FALL-THROUGH leaf does not
   even open the bundle.  Spec cleanups made in this pass:
     - EVERY taken leaf hands the step's later out (the RVC originals
       did; the base-width ones absorbed it) -- a taken branch is a loop
       back edge, and a uniform ▷-continuation is what lets any loop
       close against the packaged leaf (a straight-line caller weakens
       with [iNext] for free);
     - EVERY taken leaf goes through the Zca-legalized jump helper, so
       only bit-0 alignment of the target is demanded (the non-zca
       originals' [bit_to_bool (access_vec_dec tgt 1) = false] premise
       is gone);
     - the config premises are gone as everywhere in the sweep.        *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes ExecCommon WpGpr RegFile HartTp WpNext.
Require Import SmodeCore.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Import Defs.

(* ---- Local helpers (copies: WpSmodePtBtype's are Local) ---- *)
Local Definition rvv (r : mword 5) (s : mstate) : mword 64 :=
    if Z.eqb (uint r) 0 then zero_reg
    else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s.(sregs).

Local Lemma exec_BTYPE_cmp_BNE (rs2 rs1 : mword 5) s :
    exec (Defs.bind (rX_bits (Regidx rs1))
            (fun w2 => Defs.bind (rX_bits (Regidx rs2))
               (fun w3 => returnM (neq_vec w2 w3)))) s
      = Some (neq_vec (rvv rs1 s) (rvv rs2 s), s).
  Proof.
    unfold rvv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    apply exec_returnM.
  Qed.

Local Lemma exec_BTYPE_cmp_BEQ (rs2 rs1 : mword 5) s :
    exec (Defs.bind (rX_bits (Regidx rs1))
            (fun w2 => Defs.bind (rX_bits (Regidx rs2))
               (fun w3 => returnM (eq_vec w2 w3)))) s
      = Some (eq_vec (rvv rs1 s) (rvv rs2 s), s).
  Proof.
    unfold rvv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    apply exec_returnM.
  Qed.

Local Lemma exec_BTYPE_cmp_BGE (rs2 rs1 : mword 5) s :
  exec (Defs.bind (rX_bits (Regidx rs1))
          (fun w2 => Defs.bind (rX_bits (Regidx rs2))
             (fun w3 => returnM (zopz0zKzJ_s w2 w3)))) s
    = Some (zopz0zKzJ_s (rvv rs1 s) (rvv rs2 s), s).
Proof.
  unfold rvv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  apply exec_returnM.
Qed.

Local Lemma exec_execute_BTYPE_BEQ_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
    eq_vec (rvv rs1 s) (rvv rs2 s) = false ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))) s
      = Some (RETIRE_SUCCESS, s).
  Proof.
    intro Hfall.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BEQ rs2 rs1 s)).
    rewrite Hfall. apply exec_returnM.
  Qed.

Local Lemma exec_execute_BTYPE_BNE_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
    neq_vec (rvv rs1 s) (rvv rs2 s) = false ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))) s
      = Some (RETIRE_SUCCESS, s).
  Proof.
    intro Hfall.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BNE rs2 rs1 s)).
    rewrite Hfall. apply exec_returnM.
  Qed.

Local Lemma exec_execute_BTYPE_BGE_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
  zopz0zKzJ_s (rvv rs1 s) (rvv rs2 s) = false ->
  exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BGE))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intro Hfall.
  unfold execute. cbn match. unfold execute_BTYPE.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BGE rs2 rs1 s)).
  rewrite Hfall. apply exec_returnM.
Qed.

Local Lemma exec_BTYPE_cmp_BLTU (rs2 rs1 : mword 5) s :
  exec (Defs.bind (rX_bits (Regidx rs1))
          (fun w2 => Defs.bind (rX_bits (Regidx rs2))
             (fun w3 => returnM (zopz0zI_u w2 w3)))) s
    = Some (zopz0zI_u (rvv rs1 s) (rvv rs2 s), s).
Proof.
  unfold rvv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  apply exec_returnM.
Qed.

Local Lemma exec_execute_BTYPE_BLTU_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
  zopz0zI_u (rvv rs1 s) (rvv rs2 s) = false ->
  exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intro Hfall.
  unfold execute. cbn match. unfold execute_BTYPE.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BLTU rs2 rs1 s)).
  rewrite Hfall. apply exec_returnM.
Qed.

Local Lemma exec_BTYPE_cmp_BLT (rs2 rs1 : mword 5) s :
  exec (Defs.bind (rX_bits (Regidx rs1))
          (fun w2 => Defs.bind (rX_bits (Regidx rs2))
             (fun w3 => returnM (zopz0zI_s w2 w3)))) s
    = Some (zopz0zI_s (rvv rs1 s) (rvv rs2 s), s).
Proof.
  unfold rvv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  apply exec_returnM.
Qed.

Local Lemma exec_execute_BTYPE_BLT_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
  zopz0zI_s (rvv rs1 s) (rvv rs2 s) = false ->
  exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BLT))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intro Hfall.
  unfold execute. cbn match. unfold execute_BTYPE.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BLT rs2 rs1 s)).
  rewrite Hfall. apply exec_returnM.
Qed.

Local Lemma exec_BTYPE_cmp_BGEU (rs2 rs1 : mword 5) s :
  exec (Defs.bind (rX_bits (Regidx rs1))
          (fun w2 => Defs.bind (rX_bits (Regidx rs2))
             (fun w3 => returnM (zopz0zKzJ_u w2 w3)))) s
    = Some (zopz0zKzJ_u (rvv rs1 s) (rvv rs2 s), s).
Proof.
  unfold rvv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  apply exec_returnM.
Qed.

Local Lemma exec_execute_BTYPE_BGEU_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
  zopz0zKzJ_u (rvv rs1 s) (rvv rs2 s) = false ->
  exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intro Hfall.
  unfold execute. cbn match. unfold execute_BTYPE.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BGEU rs2 rs1 s)).
  rewrite Hfall. apply exec_returnM.
Qed.

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

Local Lemma exec_execute_BTYPE_BEQ_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    eq_vec (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BEQ rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.

Local Lemma exec_execute_BTYPE_BNE_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    neq_vec (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BNE rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.

Local Lemma exec_execute_BTYPE_BLTU_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    zopz0zI_u (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BLTU rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.

Local Lemma exec_execute_BTYPE_BLT_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    zopz0zI_s (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BLT))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BLT rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.

Local Lemma exec_execute_BTYPE_BGE_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    zopz0zKzJ_s (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BGE))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BGE rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.

Local Lemma exec_execute_BTYPE_BGEU_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    zopz0zKzJ_u (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BGEU rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.

Section WpSconfBtype.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  (* ------------------------------------------------------------------- *)
  (* FALL-THROUGH leaves: [sconf]/[sie_cap] pass through untouched.       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_beq_fall_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (rget m rs1) (rget m rs2) = false ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BEQ_fall. unfold rvv. rewrite Lva Lvb. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  Lemma wp_bne_fall_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (rget m rs1) (rget m rs2) = false ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BNE_fall. unfold rvv. rewrite Lva Lvb. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  Lemma wp_bltu_fall_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zI_u (rget m rs1) (rget m rs2) = false ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BLTU_fall. unfold rvv. rewrite Lva Lvb. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* BLT-fall, the SIGNED twin of [wp_bltu_fall_s_sconf] at two general
     registers (free_desc's `i >= NUM` bound check).  The x0-specialized
     [wp_blt_x0_fall_s_sconf] below is the same leaf against zero. *)
  Lemma wp_blt_fall_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zI_s (rget m rs1) (rget m rs2) = false ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BLT)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BLT))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BLT_fall. unfold rvv. rewrite Lva Lvb. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* BGEU-fall (the freerange loop exit: no more full pages fit). *)
  Lemma wp_bgeu_fall_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zKzJ_u (rget m rs1) (rget m rs2) = false ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BGEU_fall. unfold rvv. rewrite Lva Lvb. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* BLTU-taken (the freerange empty-page-list path skips the loop to the
     epilogue). *)
  Lemma wp_bltu_taken_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zI_u (rget m rs1) (rget m rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : zopz0zI_u (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact Hcmp).
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BLTU_taken_zca imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* BGEU-taken (the freerange loop back-edge: another full page still fits). *)
  Lemma wp_bgeu_taken_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zKzJ_u (rget m rs1) (rget m rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : zopz0zKzJ_u (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact Hcmp).
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BGEU_taken_zca imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* BGE-fall / BGE-taken over TWO general registers -- the SIGNED twin of
     the [bgeu] pair above (pipewrite's / piperead's [bge s2,s4] loop guard:
     the copy is done when the signed index reaches the signed count).  The
     [_x0_] forms below are the [rs1 = x0] specializations gcc emits for
     [blez]; neither covers a general rs1. *)
  Lemma wp_bge_fall_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zKzJ_s (rget m rs1) (rget m rs2) = false ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BGE)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BGE))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BGE_fall. unfold rvv. rewrite Lva Lvb. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  Lemma wp_bge_taken_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zKzJ_s (rget m rs1) (rget m rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BGE)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BGE))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : zopz0zKzJ_s (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact Hcmp).
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BGE_taken_zca imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  Lemma wp_bge_x0_fall_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs2 <> 0 ->
    zopz0zKzJ_s zero_reg (rget m rs2) = false ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BGE)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BGE))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BGE_fall. unfold rvv. rewrite Lvb.
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* BLT against x0 -- a [bltz rs1] error test (the -1 return of
     mappages / kvmmap).  x0 is not in the register file, so this is the
     x0-specialized twin of [wp_bltu_fall_s_sconf], as [wp_bge_x0_fall_s_sconf]
     is of [wp_bgeu_fall_s_sconf]. *)
  Lemma wp_blt_x0_fall_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    zopz0zI_s (rget m rs1) zero_reg = false ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BLT)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hcmp) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BLT))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BLT_fall. unfold rvv. rewrite Lva.
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* ...and its TAKEN twin: the [bltz rs1] error test that DID fire (the
     [argfd(...) < 0] arm of a syscall).  x0 is not in the register file, so
     this is the x0-specialized twin of [wp_bltu_taken_s_sconf]. *)
  Lemma wp_blt_x0_taken_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    zopz0zI_s (rget m rs1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BLT)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BLT))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : zopz0zI_s (rvv rs1 s_pc) (rvv (mword_of_int 0 : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact Hcmp. }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BLT_taken_zca imm (mword_of_int 0) rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* BGE against x0 in the rs2 slot -- the [bgez rs1] "did it succeed?"    *)
  (* test (sys_pipe's [copyout(...) >= 0]).  The MIRROR of the two         *)
  (* [wp_bge_x0_*] lemmas above, which put x0 in rs1 and so read [blez];   *)
  (* the operand order is the whole difference and neither can serve for   *)
  (* the other, so both pairs exist.                                       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_bgez_fall_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    zopz0zKzJ_s (rget m rs1) zero_reg = false ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BGE)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hcmp) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BGE))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BGE_fall. unfold rvv. rewrite Lva.
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  Lemma wp_bgez_taken_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    zopz0zKzJ_s (rget m rs1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BGE)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BGE))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : zopz0zKzJ_s (rvv rs1 s_pc) (rvv (mword_of_int 0 : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact Hcmp. }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BGE_taken_zca imm (mword_of_int 0) rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* BGE against x0 in the rs1 slot -- a [blez rs2] loop-guard (printint's
     [while (--i >= 0)]).  The taken twin of [wp_bge_x0_fall_s_sconf]. *)
  Lemma wp_bge_x0_taken_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs2 <> 0 ->
    zopz0zKzJ_s zero_reg (rget m rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BGE)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs2 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BGE))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : zopz0zKzJ_s (rvv (mword_of_int 0 : mword 5) s_pc) (rvv rs2 s_pc) = true).
      { unfold rvv. rewrite Lvb.
        replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact Hcmp. }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BGE_taken_zca imm rs2 (mword_of_int 0) s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  Lemma wp_cbeqz_fall_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    eq_vec (rget m rd1) zero_reg = false ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs Hrd1 Hcmp) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc true
              (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rd1) with "Hfile") as "[Hrac Hfb_rd1]".
    iDestruct (gpr_pt_value rd1 (tp_pin m (Regidx rd1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rd1" with "Hrac") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      apply exec_execute_BTYPE_BEQ_fall. unfold rvv.
      rewrite Lva.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  Lemma wp_cbnez_fall_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    neq_vec (rget m rd1) zero_reg = false ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs Hrd1 Hcmp) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc true
              (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rd1) with "Hfile") as "[Hrac Hfb_rd1]".
    iDestruct (gpr_pt_value rd1 (tp_pin m (Regidx rd1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rd1" with "Hrac") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      apply exec_execute_BTYPE_BNE_fall. unfold rvv.
      rewrite Lva.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* TAKEN leaves: the continuation is UNDER A LATER (the step's own),    *)
  (* so a loop's Löb IH can be discharged here; straight-line callers     *)
  (* weaken with [iNext].  All four go through the Zca jump helper, so    *)
  (* only bit-0 alignment of the target is demanded.                      *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_beq_taken_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (rget m rs1) (rget m rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : eq_vec (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact Hcmp).
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BEQ_taken_zca imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  Lemma wp_bne_taken_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (rget m rs1) (rget m rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : neq_vec (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact Hcmp).
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BNE_taken_zca imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  Lemma wp_cbeqz_taken_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    let imm : mword 13 := sign_extend' 13 (concat_vec imm8 ('b"0")) in
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    eq_vec (rget m rd1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc true (BTYPE (imm, zreg, creg2reg_idx rs, BEQ)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros imm.
    iIntros (Hrs Hrd1 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc true
              (BTYPE (imm, zreg, creg2reg_idx rs, BEQ))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rd1) with "Hfile") as "[Hrac Hfb_rd1]".
    iDestruct (gpr_pt_value rd1 (tp_pin m (Regidx rd1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rd1" with "Hrac") as "Hfile".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htk : eq_vec (rvv rd1 s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact Hcmp. }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BEQ_taken_zca imm (zero_extend' 5 ('b"00")) rd1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
                     (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
                   = add_vec pc (sign_extend' 64 imm))
      by (rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  Lemma wp_cbnez_taken_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    let imm : mword 13 := sign_extend' 13 (concat_vec imm8 ('b"0")) in
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    neq_vec (rget m rd1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc true (BTYPE (imm, zreg, creg2reg_idx rs, BNE)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros imm.
    iIntros (Hrs Hrd1 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc true
              (BTYPE (imm, zreg, creg2reg_idx rs, BNE))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rd1) with "Hfile") as "[Hrac Hfb_rd1]".
    iDestruct (gpr_pt_value rd1 (tp_pin m (Regidx rd1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rd1" with "Hrac") as "Hfile".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htk : neq_vec (rvv rd1 s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact Hcmp. }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BNE_taken_zca imm (zero_extend' 5 ('b"00")) rd1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
                     (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
                   = add_vec pc (sign_extend' 64 imm))
      by (rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.


  (* beqz (x0) TAKEN: the 4-byte twin of [wp_cbeqz_taken_s_sconf].  Only the
     instruction width differs -- the branch target's 2-alignment is what Zca
     licenses, and that is a fact about the TARGET, not about the size of the
     branch. *)
  Lemma wp_beqz_x0_taken_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    eq_vec (rget m rs1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, zreg, Regidx rs1, BEQ)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, zreg, Regidx rs1, BEQ))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htk : eq_vec (rvv rs1 s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact Hcmp. }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BEQ_taken_zca imm (zero_extend' 5 ('b"00")) rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
                     (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
                   = add_vec pc (sign_extend' 64 imm))
      by (rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* beqz (x0) fall-through -- moved here from ProofWalk.v. *)
  Lemma wp_beqz_x0_fall_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    eq_vec (rget m rs1) zero_reg = false ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, zreg, Regidx rs1, BEQ)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hcmp) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, zreg, Regidx rs1, BEQ))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap [%Hdom Hfmap] Hnpc [Hreg Hmem]".
    assert (Hma : rf_to_gmap (tp_pin m) !! Regidx rs1 = Some (tp_pin m !!! Regidx rs1))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rs1 (tp_pin m !!! Regidx rs1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      change zreg with (Regidx (mword_of_int 0 : mword 5)).
      apply exec_execute_BTYPE_BEQ_fall. unfold rvv. rewrite Lva.
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (gpr_file (tp_pin m)) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"]. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg'".
    iApply ("Hcont" $! cpu_id with "[] Hcg' [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* bnez (x0 as rs2), the uncompressed form -- the back-edge of printk's %p
     hex loop, whose counter is a full-width [addiw].  The [zreg] twins of
     [wp_bne_taken]/[wp_bne_fall]: with rs2 = x0 the model reads no second
     register, so the [uint rs2 <> 0] side condition of those cannot be met. *)
  Lemma wp_bnez_x0_taken_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    neq_vec (rget m rs1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, zreg, Regidx rs1, BNE)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, zreg, Regidx rs1, BNE))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htk : neq_vec (rvv rs1 s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact Hcmp. }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BNE_taken_zca imm (zero_extend' 5 ('b"00")) rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
                     (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
                   = add_vec pc (sign_extend' 64 imm))
      by (rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  Lemma wp_bnez_x0_fall_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    neq_vec (rget m rs1) zero_reg = false ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, zreg, Regidx rs1, BNE)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hcmp) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (BTYPE (imm, zreg, Regidx rs1, BNE))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap [%Hdom Hfmap] Hnpc [Hreg Hmem]".
    assert (Hma : rf_to_gmap (tp_pin m) !! Regidx rs1 = Some (tp_pin m !!! Regidx rs1))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rs1 (tp_pin m !!! Regidx rs1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      change zreg with (Regidx (mword_of_int 0 : mword 5)).
      apply exec_execute_BTYPE_BNE_fall. unfold rvv. rewrite Lva.
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (gpr_file (tp_pin m)) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"]. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg'".
    iApply ("Hcont" $! cpu_id with "[] Hcg' [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

End WpSconfBtype.
