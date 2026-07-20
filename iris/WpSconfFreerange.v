(* WpSconfFreerange.v -- the whole-function WP for xv6's freerange() over the
   SIE-agnostic sconf world.  freerange(pa_start, pa_end) rounds pa_start up to
   a page boundary and calls kfree() on every full page in
   [PGROUNDUP(pa_start), pa_end).  It is the hard loop of the kinit cone: a
   BOUNDED loop over kfree, proved by ordinary Coq fuel induction on the list of
   remaining pages (no iLoeb -- the packaged leaves strip the later).

   The loop threads: [sconf]/[sie_cap]/[intr_count] (net-zero -- kfree's
   acquire/release pair restores the level), the three per-CPU scratch cells
   (returned by the strengthened [wp_kfree_sconf]), a DEEP [stack_own] slice
   lent to kfree (kfree wants 14 below its sp), and a big-sep of [page_own] over
   the pages to be freed. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpLoad.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import SmodePte PtTreeAdue.
Require Import SmodeCore WpSmodeGpr.
Require Import KptTree SmodeCorePt WpSmodePtLeaves WpSmodePtMem.
Require Import StackOwn CalleeSaved.
Require Import KernelText.
Require Import WpMycpu WpLock.
Require Import KallocInv.
Require Import IntrDefs WpIntrInv WpSmodeIntr.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSconfWalk.
Require Import WpSconfKfree.
Require Import WpFreerangeDecode.
Require Import SRegime.
From Kernel Require KernelSyms.
Require Import RiscvExec RiscvTryStep RiscvFetchExec WpLeafCommon.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

(* ---- Model-level BTYPE facts for BLTU-taken and BGEU (fall/taken).  The
   BLTU-fall model lemma and its [wp_bltu_fall_s_sconf] leaf already live in
   WpSconfWalk; here we add the three siblings freerange's two branches need.
   [rvv] and the cmp-helper shape mirror WpSconfBtype/WpSconfWalk (Local). ---- *)
Local Definition rvv (r : mword 5) (s : mstate) : mword 64 :=
    if Z.eqb (uint r) 0 then zero_reg
    else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s.(sregs).

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

Section WpSconfFreerange.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.

  (* ================================================================= *)
  (*  §1  Missing branch / ALU leaves (freerange-local).                *)
  (* ================================================================= *)

  (* BLTU-taken (the empty-page-list path skips the loop to the epilogue). *)
  Lemma wp_bltu_taken_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : gmap regidx (mword 64)) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zI_u (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU)) -∗
    ( ▷ ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal0) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hma : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
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
    iApply ("Hcont" with "Hhs' [$Hhw $Hsc2] Hcap Htlbinv [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* BGEU-fall (the loop exit: no more full pages fit). *)
  Lemma wp_bgeu_fall_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : gmap regidx (mword 64)) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zKzJ_u (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc [Hreg Hmem]".
    assert (Hma : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BGEU_fall. unfold rvv. rewrite Lva Lvb. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hsc Hcap Htlbinv [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* BGEU-taken (the loop back-edge: another full page still fits). *)
  Lemma wp_bgeu_taken_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : gmap regidx (mword 64)) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zKzJ_u (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU)) -∗
    ( ▷ ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal0) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hma : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
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
    iApply ("Hcont" with "Hhs' [$Hhw $Hsc2] Hcap Htlbinv [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* c.and rd,rd,rs2 (register-register AND; the PGROUNDUP mask step). *)
  Lemma wp_cand_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, Regidx rd, Regidx rd, AND)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg
        (and_vec (m !!! Regidx rd) (m !!! Regidx rs2))]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (and_vec (m !!! Regidx rd) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rs2
              (RTYPE (Regidx rs2, Regidx rd, Regidx rd, AND))
              (and_vec (m !!! Regidx rd) (m !!! Regidx rs2))
              m Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    rewrite (exec_execute_RTYPE_AND_gpr rs2 rd rd s_pc Hrd).
    unfold gpr_and_val. rewrite Hva Hvb. reflexivity.
  Qed.

  (* ================================================================= *)
  (*  §2  The page-run predicate and freerange's whole-function WP.     *)
  (* ================================================================= *)
  Notation FR := KernelSyms.freerange.

  Definition PGSIZEv : mword 64 := mword_of_int 4096.
  Definition negPGSIZEv : mword 64 := mword_of_int (-4096).   (* the ~0xfff page mask *)

  (* [avail_inc] applied [k] times -- the page-count token after freeing [k]
     pages.  freerange starts at [Some 0] and ends at [Some (length ps)]. *)
  Fixpoint avail_inc_n (on : option nat) (k : nat) : option nat :=
    match k with O => on | S k' => avail_inc (avail_inc_n on k') end.

  Lemma avail_inc_n_comm (on : option nat) (k : nat) :
    avail_inc_n (avail_inc on) k = avail_inc (avail_inc_n on k).
  Proof. induction k as [|k IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma avail_inc_n_Some0 (k : nat) : avail_inc_n (Some 0%nat) k = Some k.
  Proof. induction k as [|k IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  (* [prun pa_end s1 ps]: [ps] is exactly the list of full pages to free when the
     loop register [s1] currently holds [p + PGSIZE].  The list terminates the
     moment [s1 >u pa_end] (no full page left); each entry is [s1 - PGSIZE],
     page-valid, and the residual [prun] threads [s1 += PGSIZE]. *)
  Fixpoint prun (pa_end s1 : mword 64) (ps : list (mword 64)) : Prop :=
    match ps with
    | [] => zopz0zI_u pa_end s1 = true
    | p :: rest =>
        zopz0zI_u pa_end s1 = false
        /\ p = add_vec s1 negPGSIZEv
        /\ page_valid p
        /\ prun pa_end (add_vec s1 PGSIZEv) rest
    end.

  (* [>=u] is the negation of [<u]: ties the bgeu back-edge to the bltu entry. *)
  Lemma zge_negb_zlt (a b : mword 64) : zopz0zKzJ_u a b = negb (zopz0zI_u a b).
  Proof.
    unfold zopz0zKzJ_u, zopz0zI_u.
    rewrite Z.geb_leb. rewrite Z.ltb_antisym. rewrite negb_involutive. reflexivity.
  Qed.

  (* freerange's epilogue (0x3e..0x46): restore ra/s0/s1, frame trade back (move_up
     6), ret.  Factored as a top-level lemma so its [intr_count γ root_ppn 0]
     premise pm-reduces on application (an iAssert's would stay folded and fail to
     unify with the caller's iota-reduced [intr_count] hypothesis). *)
  Lemma frepi (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m Me : gmap regidx (mword 64)) (K ncnt : nat) (a_noff a_int a_cpu : mword 64)
      (γk : gname * gname) (onf : option nat) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (6 <= K)%nat ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    Me !!! Regidx csp_rs1 = spr ->
    (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> csp_rs1 -> Me !!! Regidx c = m !!! Regidx c) ->
    kernel_text -∗
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap γ root_ppn Me -∗
    intr_count γ root_ppn ncnt -∗ tlb_inv_pt root_ppn -∗
    pc_is (mword_of_int (FR + 0x3e)) -∗ gpr_file Me -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5) : mword 64) -∗
    (pa_stk sp0 3) ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5) : mword 64) -∗
    (∃ v : mword 64, (pa_stk sp0 4) ↦₈ v) -∗
    (∃ v : mword 64, (pa_stk sp0 5) ↦₈ v) -∗
    (∃ v : mword 64, (pa_stk sp0 6) ↦₈ v) -∗
    stack_own (pa_stk spr kv_frame_slots) (K - 6) -∗
    a_noff ↦₄ (zeros' 32 : mword 32) -∗ (∃ iv : mword 32, a_int ↦₄ iv) -∗ a_cpu ↦₈ (zero_reg : mword 64) -∗
    kalloc_avail γk onf -∗
    ( ∀ mr,
      sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap γ root_ppn mr -∗
      intr_count γ root_ppn ncnt -∗ tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗ gpr_file mr -∗ ⌜ callee_saved m mr ⌝ -∗
      stack_own (pa_stk sp0 kv_frame_slots) K -∗
      a_noff ↦₄ (zeros' 32 : mword 32) -∗ (∃ iv : mword 32, a_int ↦₄ iv) -∗ a_cpu ↦₈ (zero_reg : mword 64) -∗
      kalloc_avail γk onf -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 spr ret_tgt HK6 Hretm HMesp HMecs.
    assert (Hspr6 : spr = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hdeepaddr : pa_stk (pa_stk sp0 kv_frame_slots) 6 = pa_stk spr kv_frame_slots).
    { rewrite Hspr6 !pa_stk_assoc. f_equal; lia. }
    iIntros "#Htext Hsc Hhs Hcap Hcnt Htlbinv Hpc Hfile Hs1c Hs2c Hs3c Hf4 Hf5 Hf6 HdeepE Hqnoff Hqint Hqcpu Havail Hcont".
    iPoseProof (fri_3e with "Htext") as "Hi3e".
    iPoseProof (fri_40 with "Htext") as "Hi40".
    iPoseProof (fri_42 with "Htext") as "Hi42".
    iPoseProof (fri_44 with "Htext") as "Hi44".
    iPoseProof (fri_46 with "Htext") as "Hi46".
    (* +0x3e c.ldsp ra,40(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x3e)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              Me (m !!! Regidx (mword_of_int 1 : mword 5)) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi3e [Hs1c] [-]").
    { iEval (rewrite HMesp Hb1). iExact "Hs1c". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hs1c".
    iEval (rewrite HMesp Hb1) in "Hs1c".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> Me).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1 lookup_total_insert_ne; [exact HMesp | vm_compute; discriminate]).
    assert (Hpp40 : add_vec_int (mword_of_int (FR + 0x3e) : mword 64) 2 = mword_of_int (FR + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    (* +0x40 c.ldsp s0,32(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x40)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              E1 (m !!! Regidx (mword_of_int 8 : mword 5)) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi40 [Hs2c] [-]").
    { iEval (rewrite HE1sp Hb2). iExact "Hs2c". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hs2c".
    iEval (rewrite HE1sp Hb2) in "Hs2c".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2 lookup_total_insert_ne; [exact HE1sp | vm_compute; discriminate]).
    assert (Hpp42 : add_vec_int (mword_of_int (FR + 0x40) : mword 64) 2 = mword_of_int (FR + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    (* +0x42 c.ldsp s1,24(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x42)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              E2 (m !!! Regidx (mword_of_int 9 : mword 5)) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi42 [Hs3c] [-]").
    { iEval (rewrite HE2sp Hb3). iExact "Hs3c". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hs3c".
    iEval (rewrite HE2sp Hb3) in "Hs3c".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spr) by (rewrite /E3 lookup_total_insert_ne; [exact HE2sp | vm_compute; discriminate]).
    assert (Hpp44 : add_vec_int (mword_of_int (FR + 0x42) : mword 64) 2 = mword_of_int (FR + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    (* +0x44 c.addi16sp sp,48 -- move_up 6 *)
    iDestruct "Hf4" as (v4) "Hs4c". iDestruct "Hf5" as (v5) "Hs5c". iDestruct "Hf6" as (v6) "Hs6c".
    set (E4 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E3).
    assert (HE4sp : E4 !!! Regidx csp_rs1 = sp0).
    { rewrite /E4 lookup_total_insert. rewrite HE3sp.
      unfold spr. rewrite pa_stk_off2.
      replace (mword_of_int (bv_wrap 64 (uint (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)) : mword 64) + uint (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)) : mword 64))) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      change (add_vec sp0 (mword_of_int 0)) with (add_vec_int sp0 0). apply avi0. }
    assert (Hup : E3 !!! Regidx csp_rs1 = pa_stk (E4 !!! Regidx csp_rs1) 6).
    { rewrite HE3sp HE4sp Hspr6. reflexivity. }
    iApply (wp_caddi16sp_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x44)) (mword_of_int 3 : mword 6) E3
              (stack_own (pa_stk sp0 kv_frame_slots) 6)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi44 [Hs1c Hs2c Hs3c Hs4c Hs5c Hs6c] [-]").
    { iIntros "Hcap".
      iAssert (stack_own (E4 !!! Regidx csp_rs1) 6) with "[Hs1c Hs2c Hs3c Hs4c Hs5c Hs6c]" as "Hframe".
      { rewrite HE4sp. rewrite stack_own_slots. cbn [seq].
        iSplitL "Hs1c"; [iExists _; iExact "Hs1c"|].
        iSplitL "Hs2c"; [iExists _; iExact "Hs2c"|].
        iSplitL "Hs3c"; [iExists _; iExact "Hs3c"|].
        iSplitL "Hs4c"; [iExists _; iExact "Hs4c"|].
        iSplitL "Hs5c"; [iExists _; iExact "Hs5c"|].
        iSplitL "Hs6c"; [iExists _; iExact "Hs6c"|].
        done. }
      iDestruct (sie_cap_move_up γ root_ppn E3 E4 6 Hup with "Hframe Hcap") as "[Hcap Hdeep6]".
      iEval (rewrite HE4sp) in "Hdeep6". iFrame "Hcap Hdeep6". }
    iIntros "Hhs Hsc Hcap Hdeep6 Htlbinv Hpc Hfile".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E3) with E4.
    assert (Hpp46 : add_vec_int (mword_of_int (FR + 0x44) : mword 64) 2 = mword_of_int (FR + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp46) in "Hpc".
    (* recombine deep-6 with the riding deep-(K-6) into the full deep-K *)
    iEval (rewrite -Hdeepaddr) in "HdeepE".
    iDestruct (stack_own_split_2 (pa_stk sp0 kv_frame_slots) 6 K ltac:(lia) with "[$Hdeep6 $HdeepE]") as "Hdeep".
    (* +0x46 c.ret *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /E3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /E2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /E1 lookup_total_insert; reflexivity. }
    assert (Hretaligned : eq_vec (access_vec_dec (update_vec_dec (add_vec (E4 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HE4ra; exact Hretm).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x46)) (mword_of_int 1 : mword 5) E4
              ltac:(vm_compute; discriminate) Hretaligned
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi46 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    assert (Hretf : update_vec_dec (add_vec (E4 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite HE4ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iApply ("Hcont" $! E4 with "Hsc Hhs Hcap Hcnt Htlbinv Hpc Hfile [%] Hdeep Hqnoff Hqint Hqcpu Havail").
    (* callee_saved m E4 *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 1 -> c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> csp_rs1 -> E4 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N1 N8 N9 Nsp.
      rewrite /E4 lookup_total_insert_ne; [| congruence].
      rewrite /E3 lookup_total_insert_ne; [| congruence].
      rewrite /E2 lookup_total_insert_ne; [| congruence].
      rewrite /E1 lookup_total_insert_ne; [| congruence].
      apply HMecs; assumption. }
    unfold callee_saved.
    split. { rewrite HE4sp. reflexivity. }
    split. { apply Hthread; vm_compute; first [reflexivity | discriminate]. }
    split. { rewrite /E4 lookup_total_insert_ne; [| vm_compute; discriminate].
             rewrite /E3 lookup_total_insert_ne; [| vm_compute; discriminate].
             rewrite /E2 lookup_total_insert; reflexivity. }
    split. { rewrite /E4 lookup_total_insert_ne; [| vm_compute; discriminate].
             rewrite /E3 lookup_total_insert; reflexivity. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

  Lemma wp_freerange_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γl : gname) (γk : gname * gname) (lk fl : mword 64)
      (m : gmap regidx (mword 64))
      (ps : list (mword 64)) (K ncnt : nat) :
    let pcE : mword 64 := mword_of_int FR in
    let pa_start := m !!! Regidx (mword_of_int 10 : mword 5) in
    let pa_end := m !!! Regidx (mword_of_int 11 : mword 5) in
    let sp0 := m !!! Regidx csp_rs1 in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
    let a_noff := add_vec cpuv (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a_int := add_vec cpuv (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    let a_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    let s1entry := add_vec (and_vec (add_vec pa_start (mword_of_int 4095 : mword 64)) negPGSIZEv) PGSIZEv in
    (20 <= K)%nat ->
    ncnt = 0%nat ->
    eq_vec (zero_reg : mword 64) cpuv = false ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    lk = mword_of_int KernelSyms.kmem ->
    fl = mword_of_int (KernelSyms.kmem + 24) ->
    prun pa_end s1entry ps ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    intr_count γ root_ppn ncnt -∗
    tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    is_lock γl lk (kmem_res γk fl) -∗
    ([∗ list] p ∈ ps, page_own p) -∗
    stack_own (pa_stk sp0 kv_frame_slots) K -∗
    a_noff ↦₄ (zeros' 32 : mword 32) -∗
    (∃ iv : mword 32, a_int ↦₄ iv) -∗
    a_cpu ↦₈ (zero_reg : mword 64) -∗
    kalloc_avail γk (Some 0%nat) -∗
    ( ∀ mr,
      sconf γ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap γ root_ppn mr -∗
      intr_count γ root_ppn ncnt -∗
      tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗ gpr_file mr -∗
      ⌜ callee_saved m mr ⌝ -∗
      stack_own (pa_stk sp0 kv_frame_slots) K -∗
      a_noff ↦₄ (zeros' 32 : mword 32) -∗
      (∃ iv : mword 32, a_int ↦₄ iv) -∗
      a_cpu ↦₈ (zero_reg : mword 64) -∗
      kalloc_avail γk (Some (length ps)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pcE pa_start pa_end sp0 ret_tgt cpuv a_noff a_int a_cpu s1entry
      HK Hncnt Hmycpu Hretm Hlk Hfl Hprun.
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    iIntros "Hsc Hhs Hcap Hcnt Htlbinv #Htext Hpc Hfile #Hkmem Hpages Hdeep Hqnoff Hqint Hqcpu Havail Hcont".
    assert (Hspr6 : spr = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* the six frame-slot address bridges (spr-relative store offset -> pa_stk sp0 k) *)
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hdeepaddr : pa_stk (pa_stk sp0 kv_frame_slots) 6 = pa_stk spr kv_frame_slots).
    { rewrite Hspr6 !pa_stk_assoc. f_equal; lia. }
    iPoseProof (fri_00 with "Htext") as "Hi00".
    iPoseProof (fri_02 with "Htext") as "Hi02".
    iPoseProof (fri_04 with "Htext") as "Hi04".
    iPoseProof (fri_06 with "Htext") as "Hi06".
    iPoseProof (fri_08 with "Htext") as "Hi08".
    iPoseProof (fri_0a with "Htext") as "Hi0a".
    iPoseProof (fri_0c with "Htext") as "Hi0c".
    iPoseProof (fri_10 with "Htext") as "Hi10".
    iPoseProof (fri_14 with "Htext") as "Hi14".
    iPoseProof (fri_16 with "Htext") as "Hi16".
    iPoseProof (fri_18 with "Htext") as "Hi18".
    iPoseProof (fri_1a with "Htext") as "Hi1a".
    iPoseProof (fri_1e with "Htext") as "Hi1e".
    iPoseProof (fri_20 with "Htext") as "Hi20".
    iPoseProof (fri_22 with "Htext") as "Hi22".
    iPoseProof (fri_24 with "Htext") as "Hi24".
    iPoseProof (fri_26 with "Htext") as "Hi26".
    iPoseProof (fri_28 with "Htext") as "Hi28".
    (* ===== PROLOGUE: 6-slot frame trade (move_down 6) + save ra/s0/s1 ===== *)
    iDestruct (stack_own_split_1 (pa_stk sp0 kv_frame_slots) 6 K ltac:(lia) with "Hdeep") as "[Hd6 Hdeep]".
    iEval (rewrite Hdeepaddr) in "Hdeep".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    assert (Hsp1 : R1 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /R1 lookup_total_insert. rewrite -Hspr6. reflexivity. }
    iApply (wp_caddi16sp_s_sconf γ root_ppn Φ pcE (mword_of_int 61 : mword 6) m (stack_own sp0 6)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi00 [Hd6] [-]").
    { iIntros "Hcap".
      iDestruct (sie_cap_move_down γ root_ppn m R1 6 Hsp1 with "Hd6 Hcap") as "[Hcap Hframe]".
      iFrame "Hcap Hframe". }
    iIntros "Hhs Hsc Hcap Hframe Htlbinv Hpc Hfile".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 lookup_total_insert; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (vra0) "Hra". iDestruct "S2" as (vs00) "Hs0".
    iDestruct "S3" as (vs10) "Hs1". iDestruct "S4" as (vs20) "Hslot4".
    iDestruct "S5" as (vs30) "Hslot5". iDestruct "S6" as (vs40) "Hslot6".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (FR + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,40(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x02)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              R1 vra0 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi02 [Hra] [-]").
    { iEval (rewrite HspR1 Hb1). iExact "Hra". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hra".
    iEval (rewrite HspR1 Hb1) in "Hra".
    assert (Hpp04 : add_vec_int (mword_of_int (FR + 0x02) : mword 64) 2 = mword_of_int (FR + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,32(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x04)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              R1 vs00 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi04 [Hs0] [-]").
    { iEval (rewrite HspR1 Hb2). iExact "Hs0". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hs0".
    iEval (rewrite HspR1 Hb2) in "Hs0".
    assert (Hpp06 : add_vec_int (mword_of_int (FR + 0x04) : mword 64) 2 = mword_of_int (FR + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,24(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x06)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              R1 vs10 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi06 [Hs1] [-]").
    { iEval (rewrite HspR1 Hb3). iExact "Hs1". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hs1".
    iEval (rewrite HspR1 Hb3) in "Hs1".
    (* the saved values are the ORIGINAL ra/s0/s1 (unchanged before these stores) *)
    assert (Hra_v : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0_v : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1_v : R1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hra_v) in "Hra". iEval (rewrite Hs0_v) in "Hs0". iEval (rewrite Hs1_v) in "Hs1".
    assert (Hpp08 : add_vec_int (mword_of_int (FR + 0x06) : mword 64) 2 = mword_of_int (FR + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) (mword_of_int 8 : mword 5)
              R1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (FR + 0x08) : mword 64) 2 = mword_of_int (FR + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* ===== PGROUNDUP (0x0a..0x18): compute s1entry, a5=PGSIZE, a4=negmask ===== *)
    (* +0x0a c.lui a5,0x1 : a5 := 0x1000 *)
    iApply (wp_clui_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x0a)) (mword_of_int 15 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6)) PGSIZEv
              R2 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(unfold PGSIZEv; vm_compute; reflexivity)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    set (R3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg PGSIZEv]> R2).
    assert (Hpp0c : add_vec_int (mword_of_int (FR + 0x0a) : mword 64) 2 = mword_of_int (FR + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    assert (HR3a5 : R3 !!! Regidx (mword_of_int 15 : mword 5) = PGSIZEv) by (rewrite /R3 lookup_total_insert; reflexivity).
    (* +0x0c addi a4,a5,-1 : a4 := 0xfff *)
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x0c)) (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 4095 : mword 12)
              R3 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    set (R4 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (R3 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 4095 : mword 12)))]> R3).
    assert (Hpp10 : add_vec_int (mword_of_int (FR + 0x0c) : mword 64) 4 = mword_of_int (FR + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    assert (HR4a0 : R4 !!! Regidx (mword_of_int 10 : mword 5) = pa_start).
    { rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR4a4 : R4 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 4095).
    { rewrite /R4 lookup_total_insert. rewrite HR3a5. unfold PGSIZEv. apply bv_eq; vm_compute; reflexivity. }
    (* +0x10 add s1,a0,a4 : s1 := pa_start + 0xfff *)
    iApply (wp_add_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x10)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 14 : mword 5)
              (add_vec pa_start (mword_of_int 4095 : mword 64)) R4
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HR4a0 HR4a4; reflexivity)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi10 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    set (R5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec pa_start (mword_of_int 4095 : mword 64))]> R4).
    assert (Hpp14 : add_vec_int (mword_of_int (FR + 0x10) : mword 64) 4 = mword_of_int (FR + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.lui a4,0xfffff : a4 := negmask *)
    iApply (wp_clui_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x14)) (mword_of_int 14 : mword 5) (sign_extend' 20 (mword_of_int 63 : mword 6)) negPGSIZEv
              R5 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(unfold negPGSIZEv; vm_compute; reflexivity)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi14 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    set (R6 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg negPGSIZEv]> R5).
    assert (Hpp16 : add_vec_int (mword_of_int (FR + 0x14) : mword 64) 2 = mword_of_int (FR + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    assert (HR6s1 : R6 !!! Regidx (mword_of_int 9 : mword 5) = add_vec pa_start (mword_of_int 4095 : mword 64)).
    { rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert; reflexivity. }
    assert (HR6a4 : R6 !!! Regidx (mword_of_int 14 : mword 5) = negPGSIZEv) by (rewrite /R6 lookup_total_insert; reflexivity).
    (* +0x16 c.and s1,s1,a4 : s1 := PGROUNDUP(pa_start) *)
    iApply (wp_cand_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x16)) (mword_of_int 9 : mword 5) (mword_of_int 14 : mword 5)
              R6 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    set (R7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (and_vec (R6 !!! Regidx (mword_of_int 9 : mword 5)) (R6 !!! Regidx (mword_of_int 14 : mword 5)))]> R6).
    assert (Hpp18 : add_vec_int (mword_of_int (FR + 0x16) : mword 64) 2 = mword_of_int (FR + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    assert (HR7s1 : R7 !!! Regidx (mword_of_int 9 : mword 5) = and_vec (add_vec pa_start (mword_of_int 4095 : mword 64)) negPGSIZEv).
    { rewrite /R7 lookup_total_insert. rewrite HR6s1 HR6a4. reflexivity. }
    assert (HR7a5 : R7 !!! Regidx (mword_of_int 15 : mword 5) = PGSIZEv).
    { rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate]. exact HR3a5. }
    (* +0x18 c.add s1,s1,a5 : s1 := s1entry = PGROUNDUP(pa_start) + PGSIZE *)
    iApply (wp_cadd_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x18)) (mword_of_int 9 : mword 5) (mword_of_int 15 : mword 5)
              R7 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi18 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    set (R8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (R7 !!! Regidx (mword_of_int 9 : mword 5)) (R7 !!! Regidx (mword_of_int 15 : mword 5)))]> R7).
    assert (Hpp1a : add_vec_int (mword_of_int (FR + 0x18) : mword 64) 2 = mword_of_int (FR + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    assert (HR8s1 : R8 !!! Regidx (mword_of_int 9 : mword 5) = s1entry).
    { rewrite /R8 lookup_total_insert. rewrite HR7s1 HR7a5. reflexivity. }
    assert (HR8a1 : R8 !!! Regidx (mword_of_int 11 : mword 5) = pa_end).
    { rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    (* register bookkeeping shared by both branches: sp/tp preserved, a4/a5, s2/s3/s4 orig *)
    assert (HR8sp : R8 !!! Regidx csp_rs1 = spr).
    { rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate]. exact HspR1. }
    (* a general "callee-saved-except-{s0,s1,sp} through R8" helper (used at the epilogue) *)
    assert (HR8cs : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> csp_rs1 -> R8 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 N9 Nsp.
      pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
      pose proof (is_cs_idx_true_neq (mword_of_int 15 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N15.
      rewrite /R8 lookup_total_insert_ne; [| congruence].
      rewrite /R7 lookup_total_insert_ne; [| congruence].
      rewrite /R6 lookup_total_insert_ne; [| congruence].
      rewrite /R5 lookup_total_insert_ne; [| congruence].
      rewrite /R4 lookup_total_insert_ne; [| congruence].
      rewrite /R3 lookup_total_insert_ne; [| congruence].
      rewrite /R2 lookup_total_insert_ne; [| congruence].
      rewrite /R1 lookup_total_insert_ne; [reflexivity | congruence]. }
    (* ===================================================================== *)
    (* +0x1a bltu a1,s1,+0x3e : split on whether any full page fits.          *)
    (* ===================================================================== *)
    destruct ps as [| p0 rest] eqn:Hpseq.
    - (* ---- SKIP: no full page fits; bltu TAKEN straight to the epilogue ---- *)
      simpl in Hprun.
      assert (Htgt3e : add_vec (mword_of_int (FR + 0x1a) : mword 64) (sign_extend' 64 (mword_of_int 36 : mword 13)) = mword_of_int (FR + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_bltu_taken_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x1a)) (mword_of_int 36 : mword 13) (mword_of_int 9 : mword 5) (mword_of_int 11 : mword 5)
                R8 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HR8a1 HR8s1; exact Hprun)
                ltac:(rewrite Htgt3e; vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi1a [-]").
      iNext. iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      iEval (rewrite Htgt3e) in "Hpc".
      iApply (frepi γ root_ppn Φ m R8 K ncnt a_noff a_int a_cpu γk (Some 0%nat) ltac:(lia) Hretm HR8sp HR8cs
                with "Htext Hsc Hhs Hcap Hcnt Htlbinv Hpc Hfile Hra Hs0 Hs1 [Hslot4] [Hslot5] [Hslot6] Hdeep Hqnoff Hqint Hqcpu Havail Hcont").
      { iExists vs20; iExact "Hslot4". }
      { iExists vs30; iExact "Hslot5". }
      { iExists vs40; iExact "Hslot6". }
    - (* ---- LOOP: at least one full page fits; enter the loop ---- *)
      destruct Hprun as (Hfits0 & Hp0eq & Hpv0 & Hprest0).
      iDestruct "Hqint" as (iv0) "Hqint".
      (* +0x1a bltu a1,s1 : falls through into the loop setup *)
      iApply (wp_bltu_fall_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x1a)) (mword_of_int 36 : mword 13) (mword_of_int 9 : mword 5) (mword_of_int 11 : mword 5)
                R8 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HR8a1 HR8s1; exact Hfits0)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi1a [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      assert (Hpp1e : add_vec_int (mword_of_int (FR + 0x1a) : mword 64) 4 = mword_of_int (FR + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      (* the saved s2/s3/s4 are the ORIGINAL callee values (untouched before 0x1e) *)
      assert (HR8s2 : R8 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)) by (apply HR8cs; vm_compute; first [reflexivity | discriminate]).
      assert (HR8s3 : R8 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)) by (apply HR8cs; vm_compute; first [reflexivity | discriminate]).
      assert (HR8s4 : R8 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5)) by (apply HR8cs; vm_compute; first [reflexivity | discriminate]).
      (* +0x1e c.sdsp s2,16(sp) *)
      iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x1e)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5)
                R8 vs20 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi1e [Hslot4] [-]").
      { iEval (rewrite HR8sp Hb4). iExact "Hslot4". }
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hslot4".
      iEval (rewrite HR8sp Hb4 HR8s2) in "Hslot4".
      assert (Hpp20 : add_vec_int (mword_of_int (FR + 0x1e) : mword 64) 2 = mword_of_int (FR + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      (* +0x20 c.sdsp s3,8(sp) *)
      iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x20)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
                R8 vs30 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi20 [Hslot5] [-]").
      { iEval (rewrite HR8sp Hb5). iExact "Hslot5". }
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hslot5".
      iEval (rewrite HR8sp Hb5 HR8s3) in "Hslot5".
      assert (Hpp22 : add_vec_int (mword_of_int (FR + 0x20) : mword 64) 2 = mword_of_int (FR + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* +0x22 c.sdsp s4,0(sp) *)
      iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x22)) (mword_of_int 0 : mword 6) (mword_of_int 20 : mword 5)
                R8 vs40 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi22 [Hslot6] [-]").
      { iEval (rewrite HR8sp Hb6). iExact "Hslot6". }
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hslot6".
      iEval (rewrite HR8sp Hb6 HR8s4) in "Hslot6".
      assert (Hpp24 : add_vec_int (mword_of_int (FR + 0x22) : mword 64) 2 = mword_of_int (FR + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      (* +0x24 c.mv s2,a1 : s2 := pa_end *)
      iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x24)) (mword_of_int 18 : mword 5) (mword_of_int 11 : mword 5)
                R8 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi24 [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (R9 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec zero_reg (R8 !!! Regidx (mword_of_int 11 : mword 5)))]> R8).
      assert (Hpp26 : add_vec_int (mword_of_int (FR + 0x24) : mword 64) 2 = mword_of_int (FR + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* +0x26 c.mv s4,a4 : s4 := negmask *)
      iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x26)) (mword_of_int 20 : mword 5) (mword_of_int 14 : mword 5)
                R9 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi26 [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (R10 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (add_vec zero_reg (R9 !!! Regidx (mword_of_int 14 : mword 5)))]> R9).
      assert (Hpp28 : add_vec_int (mword_of_int (FR + 0x26) : mword 64) 2 = mword_of_int (FR + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp28) in "Hpc".
      (* +0x28 c.mv s3,a5 : s3 := PGSIZE *)
      iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x28)) (mword_of_int 19 : mword 5) (mword_of_int 15 : mword 5)
                R10 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi28 [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (R11 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (add_vec zero_reg (R10 !!! Regidx (mword_of_int 15 : mword 5)))]> R10).
      assert (Hpp2a : add_vec_int (mword_of_int (FR + 0x28) : mword 64) 2 = mword_of_int (FR + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      (* register values entering the loop body *)
      assert (HR11s2 : R11 !!! Regidx (mword_of_int 18 : mword 5) = pa_end).
      { rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R9 lookup_total_insert. rewrite HR8a1. apply add_vec_zero_l. }
      assert (HR11s3 : R11 !!! Regidx (mword_of_int 19 : mword 5) = PGSIZEv).
      { rewrite /R11 lookup_total_insert.
        rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite HR7a5. apply add_vec_zero_l. }
      assert (HR11s4 : R11 !!! Regidx (mword_of_int 20 : mword 5) = negPGSIZEv).
      { rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R10 lookup_total_insert.
        rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite HR6a4. apply add_vec_zero_l. }
      assert (HR11sp : R11 !!! Regidx csp_rs1 = spr).
      { rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate]. exact HR8sp. }
      assert (HR11tp : R11 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
      { rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate]. apply HR8cs; vm_compute; first [reflexivity | discriminate]. }
      assert (HR11s1 : R11 !!! Regidx (mword_of_int 9 : mword 5) = s1entry).
      { rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate]. exact HR8s1. }
      (* the surviving callee-saved (tp + s5..s11) tracked across the loop *)
      assert (HR11cs : forall c : mword 5, is_cs_idx c = true ->
                c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> csp_rs1 ->
                c <> mword_of_int 18 -> c <> mword_of_int 19 -> c <> mword_of_int 20 ->
                R11 !!! Regidx c = m !!! Regidx c).
      { intros c Hc N8 N9 Nsp N18 N19 N20.
        rewrite /R11 lookup_total_insert_ne; [| congruence].
        rewrite /R10 lookup_total_insert_ne; [| congruence].
        rewrite /R9 lookup_total_insert_ne; [| congruence].
        apply HR8cs; assumption. }
      (* ================================================================= *)
      (* THE LOOP.  Fuel induction over the remaining page list.           *)
      (* ================================================================= *)
      iAssert (∀ (fuel : nat) (M : gmap regidx (mword 64)) (qs : list (mword 64)) (on : option nat),
        ⌜(length qs <= fuel)%nat⌝ -∗
        ⌜ M !!! Regidx (mword_of_int 18 : mword 5) = pa_end
          /\ M !!! Regidx (mword_of_int 19 : mword 5) = PGSIZEv
          /\ M !!! Regidx (mword_of_int 20 : mword 5) = negPGSIZEv
          /\ M !!! Regidx csp_rs1 = spr
          /\ M !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)
          /\ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> csp_rs1 -> c <> mword_of_int 18 -> c <> mword_of_int 19 -> c <> mword_of_int 20 -> M !!! Regidx c = m !!! Regidx c)
          /\ prun pa_end (M !!! Regidx (mword_of_int 9 : mword 5)) qs
          /\ qs <> []
          /\ avail_inc_n on (length qs) = Some (length (p0 :: rest)) ⌝ -∗
        sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap γ root_ppn M -∗
        intr_count γ root_ppn ncnt -∗ tlb_inv_pt root_ppn -∗
        pc_is (mword_of_int (FR + 0x2a)) -∗ gpr_file M -∗
        ([∗ list] p ∈ qs, page_own p) -∗
        stack_own (pa_stk spr kv_frame_slots) (K - 6) -∗
        a_noff ↦₄ (zeros' 32 : mword 32) -∗ (∃ iv : mword 32, a_int ↦₄ iv) -∗ a_cpu ↦₈ (zero_reg : mword 64) -∗
        kalloc_avail γk on -∗
        (pa_stk sp0 1) ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) -∗
        (pa_stk sp0 2) ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5) : mword 64) -∗
        (pa_stk sp0 3) ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5) : mword 64) -∗
        (pa_stk sp0 4) ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5) : mword 64) -∗
        (pa_stk sp0 5) ↦₈ (m !!! Regidx (mword_of_int 19 : mword 5) : mword 64) -∗
        (pa_stk sp0 6) ↦₈ (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64) -∗
        ( ∀ mr, sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap γ root_ppn mr -∗
          intr_count γ root_ppn ncnt -∗ tlb_inv_pt root_ppn -∗
          pc_is ret_tgt -∗ gpr_file mr -∗ ⌜ callee_saved m mr ⌝ -∗
          stack_own (pa_stk sp0 kv_frame_slots) K -∗
          a_noff ↦₄ (zeros' 32 : mword 32) -∗ (∃ iv : mword 32, a_int ↦₄ iv) -∗ a_cpu ↦₈ (zero_reg : mword 64) -∗
          kalloc_avail γk (Some (length (p0 :: rest))) -∗
          WP (Loop : expr riscv_lang) {{ Φ }}) -∗
        WP (Loop : expr riscv_lang) {{ Φ }})%I
        with "[]" as "Hloop".
      { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
        { iIntros (M qs on) "%Hlen %Hinv Hsc Hhs Hcap Hcnt Htlb Hpc Hfile Hpages Hdeepl Hqnoff Hqint Hqcpu Havail Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hcont".
          destruct Hinv as (_ & _ & _ & _ & _ & _ & _ & Hne & _).
          destruct qs; [contradiction | simpl in Hlen; lia]. }
        iIntros (M qs on) "%Hlen %Hinv Hsc Hhs Hcap Hcnt Htlb Hpc Hfile Hpages Hdeepl Hqnoff Hqint Hqcpu Havail Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hcont".
        destruct Hinv as (Hms2 & Hms3 & Hms4 & Hmsp & Hmtp & Hmcs & Hprunq & Hqne & Hcount).
        destruct qs as [| pc0 rest0]; [contradiction |].
        destruct Hprunq as (Hfitsq & Hpc0eqq & Hpvq & Hprestq).
        iDestruct "Hpages" as "[Hpage Hpages]".
        iPoseProof (fri_2a with "Htext") as "Hi2a".
        iPoseProof (fri_2e with "Htext") as "Hi2e".
        iPoseProof (fri_32 with "Htext") as "Hi32".
        iPoseProof (fri_34 with "Htext") as "Hi34".
        (* +0x2a add a0,s1,s4 : a0 := p = s1 - PGSIZE *)
        iApply (wp_add_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x2a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5)
                  (add_vec (M !!! Regidx (mword_of_int 9 : mword 5)) (M !!! Regidx (mword_of_int 20 : mword 5))) M
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(reflexivity)
                  with "Hsc Hhs Hcap Htlb Hpc Hfile Hi2a [-]").
        iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
        set (M1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (M !!! Regidx (mword_of_int 9 : mword 5)) (M !!! Regidx (mword_of_int 20 : mword 5)))]> M).
        assert (HM1a0 : M1 !!! Regidx (mword_of_int 10 : mword 5) = pc0).
        { rewrite /M1 lookup_total_insert. rewrite Hms4. rewrite -Hpc0eqq. reflexivity. }
        assert (Hpp2e : add_vec_int (mword_of_int (FR + 0x2a) : mword 64) 4 = mword_of_int (FR + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp2e) in "Hpc".
        (* +0x2e jal ra,kfree *)
        iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x2e)) (mword_of_int 1 : mword 5) (mword_of_int 2096998 : mword 21)
                  M1 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
                  with "Hsc Hhs Hcap Htlb Hpc Hfile Hi2e [-]").
        iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
        set (M2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (FR + 0x2e) : mword 64) 4)]> M1).
        assert (Htgtkf : add_vec (mword_of_int (FR + 0x2e) : mword 64) (sign_extend' 64 (mword_of_int 2096998 : mword 21)) = mword_of_int KernelSyms.kfree) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtkf) in "Hpc".
        assert (HM2a0 : M2 !!! Regidx (mword_of_int 10 : mword 5) = pc0).
        { rewrite /M2 lookup_total_insert_ne; [exact HM1a0 | vm_compute; discriminate]. }
        assert (HM2tp : M2 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
        { rewrite /M2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /M1 lookup_total_insert_ne; [exact Hmtp | vm_compute; discriminate]. }
        assert (HM2sp : M2 !!! Regidx csp_rs1 = spr).
        { rewrite /M2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /M1 lookup_total_insert_ne; [exact Hmsp | vm_compute; discriminate]. }
        assert (HM2ra : M2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (FR + 0x2e) : mword 64) 4) by (rewrite /M2; apply lookup_total_insert).
        (* ---- kfree(p) ---- *)
        iDestruct "Hqint" as (ivl) "Hqint".
        iApply (wp_kfree_sconf γ root_ppn Φ γl γk lk fl M2 zero_reg (zeros' 32) ivl on ncnt (K - 6)
                  ltac:(lia)
                  ltac:(rewrite HM2tp; exact Hmycpu)
                  ltac:(rewrite HM2ra; vm_compute; reflexivity)
                  Hlk Hfl
                  ltac:(split; intros _; [exact Hncnt | vm_compute; reflexivity])
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hsc Hhs Hcap Hcnt Htlb Htext Hpc Hfile Hkmem [Hpage] Havail [Hdeepl] [Hqnoff] [Hqint] [Hqcpu] [-]").
        { rewrite /kfree_pre. iSplitR; [iPureIntro; rewrite HM2a0; exact Hpvq | rewrite HM2a0; iExact "Hpage"]. }
        { iEval (rewrite HM2sp). iExact "Hdeepl". }
        { iEval (rewrite HM2tp). iExact "Hqnoff". }
        { iEval (rewrite HM2tp). iExact "Hqint". }
        { iExact "Hqcpu". }
        iIntros (mkf) "Hsc Hhs Hcap Hcnt Htlb Hpc Hfile %Hkfcs Havail Hdeepl Hqcpu Hqnoff Hqint".
        iEval (rewrite HM2sp) in "Hdeepl".
        iEval (rewrite HM2tp) in "Hqnoff".
        iEval (rewrite HM2tp) in "Hqint".
        (* kfree returned the noff cell at the release value; it is [zeros' 32]. *)
        (* kfree returned the noff cell at the release value; at noffv = [zeros' 32]
           it is [zeros' 32].  Compute the ISOLATED (closed) value -- vm_compute on
           the hypothesis itself would diverge on the symbolic per-cpu address. *)
        assert (Hnr : (autocast (T := mword) (subrange_vec_dec
            (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 (autocast (T := mword) (subrange_vec_dec
                (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 (zeros' 32))
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
                (Z.sub (Z.mul 4 8) 1) 0) : mword 32))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
            (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = (zeros' 32 : mword 32))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hnr) in "Hqnoff".
        assert (Hkfret : update_vec_dec (add_vec (M2 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (FR + 0x32)).
        { rewrite HM2ra. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hkfret) in "Hpc".
        pose proof Hkfcs as Hkfcs_full. unfold callee_saved in Hkfcs.
        destruct Hkfcs as (Hqsp & Hqtp & Hqs0 & Hqs1 & Hqs2 & Hqs3 & Hqs4 & Hqs5 & Hqs6 & Hqs7 & Hqs8 & Hqs9 & Hqs10 & Hqs11).
        (* +0x32 c.add s1,s1,s3 : s1 += PGSIZE *)
        iPoseProof (fri_32 with "Htext") as "Hi32'".
        iApply (wp_cadd_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 19 : mword 5)
                  mkf ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hsc Hhs Hcap Htlb Hpc Hfile Hi32 [-]").
        iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
        set (M3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (mkf !!! Regidx (mword_of_int 9 : mword 5)) (mkf !!! Regidx (mword_of_int 19 : mword 5)))]> mkf).
        assert (Hpp34 : add_vec_int (mword_of_int (FR + 0x32) : mword 64) 2 = mword_of_int (FR + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp34) in "Hpc".
        (* mkf preserves the loop registers (callee-saved through kfree) *)
        assert (Hkf_s1 : mkf !!! Regidx (mword_of_int 9 : mword 5) = M !!! Regidx (mword_of_int 9 : mword 5)).
        { rewrite Hqs1. rewrite /M2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /M1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
        assert (Hkf_s2 : mkf !!! Regidx (mword_of_int 18 : mword 5) = pa_end).
        { rewrite Hqs2. rewrite /M2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /M1 lookup_total_insert_ne; [exact Hms2 | vm_compute; discriminate]. }
        assert (Hkf_s3 : mkf !!! Regidx (mword_of_int 19 : mword 5) = PGSIZEv).
        { rewrite Hqs3. rewrite /M2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /M1 lookup_total_insert_ne; [exact Hms3 | vm_compute; discriminate]. }
        assert (Hkf_s4 : mkf !!! Regidx (mword_of_int 20 : mword 5) = negPGSIZEv).
        { rewrite Hqs4. rewrite /M2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /M1 lookup_total_insert_ne; [exact Hms4 | vm_compute; discriminate]. }
        assert (Hkf_sp : mkf !!! Regidx csp_rs1 = spr) by (rewrite Hqsp; exact HM2sp).
        assert (HM3s1 : M3 !!! Regidx (mword_of_int 9 : mword 5) = add_vec (M !!! Regidx (mword_of_int 9 : mword 5)) PGSIZEv).
        { rewrite /M3 lookup_total_insert. rewrite Hkf_s1 Hkf_s3. reflexivity. }
        assert (HM3s2 : M3 !!! Regidx (mword_of_int 18 : mword 5) = pa_end).
        { rewrite /M3 lookup_total_insert_ne; [exact Hkf_s2 | vm_compute; discriminate]. }
        assert (HM3s3 : M3 !!! Regidx (mword_of_int 19 : mword 5) = PGSIZEv).
        { rewrite /M3 lookup_total_insert_ne; [exact Hkf_s3 | vm_compute; discriminate]. }
        assert (HM3s4 : M3 !!! Regidx (mword_of_int 20 : mword 5) = negPGSIZEv).
        { rewrite /M3 lookup_total_insert_ne; [exact Hkf_s4 | vm_compute; discriminate]. }
        assert (HM3sp : M3 !!! Regidx csp_rs1 = spr).
        { rewrite /M3 lookup_total_insert_ne; [exact Hkf_sp | vm_compute; discriminate]. }
        assert (HM3tp : M3 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
        { rewrite /M3 lookup_total_insert_ne; [| vm_compute; discriminate]. rewrite Hqtp. exact HM2tp. }
        (* the tail callee-saved (tp + s5..s11) still equal m through this iteration *)
        assert (HM3cs : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> csp_rs1 -> c <> mword_of_int 18 -> c <> mword_of_int 19 -> c <> mword_of_int 20 -> M3 !!! Regidx c = m !!! Regidx c).
        { intros c Hc N8 N9 Nsp N18 N19 N20.
          pose proof (is_cs_idx_true_neq (mword_of_int 1 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Nra.
          pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na0.
          rewrite /M3 lookup_total_insert_ne; [| congruence].
          rewrite (callee_saved_lookup Hkfcs_full c Hc).
          rewrite /M2 lookup_total_insert_ne; [| congruence].
          rewrite /M1 lookup_total_insert_ne; [| congruence].
          apply Hmcs; assumption. }
        (* the bgeu test: s2 >=u s1  <->  another page still fits (rest nonempty) *)
        destruct rest0 as [| q0 rest0'].
        + (* rest empty: bgeu FALLS -> exit to 0x38, restore s2/s3/s4, then epilogue *)
          simpl in Hprestq.
          assert (Hbfall : zopz0zKzJ_u (M3 !!! Regidx (mword_of_int 18 : mword 5)) (M3 !!! Regidx (mword_of_int 9 : mword 5)) = false).
          { rewrite zge_negb_zlt. rewrite HM3s2 HM3s1. rewrite Hprestq. reflexivity. }
          iApply (wp_bgeu_fall_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x34)) (mword_of_int 8182 : mword 13) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5)
                    M3 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbfall
                    with "Hsc Hhs Hcap Htlb Hpc Hfile Hi34 [-]").
          iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
          assert (Hpp38 : add_vec_int (mword_of_int (FR + 0x34) : mword 64) 4 = mword_of_int (FR + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp38) in "Hpc".
          iPoseProof (fri_38 with "Htext") as "Hi38".
          iPoseProof (fri_3a with "Htext") as "Hi3a".
          iPoseProof (fri_3c with "Htext") as "Hi3c".
          (* +0x38 c.ldsp s2,16(sp) : restore s2 = m!!!18 *)
          iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x38)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5)
                    M3 (m !!! Regidx (mword_of_int 18 : mword 5)) (dqm:=DfracOwn 1)
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    with "Hsc Hhs Hcap Htlb Hpc Hfile Hi38 [Hc4] [-]").
          { iEval (rewrite HM3sp Hb4). iExact "Hc4". }
          iIntros "Hhs Hsc Hcap Htlb Hpc Hfile Hc4".
          iEval (rewrite HM3sp Hb4) in "Hc4".
          set (N1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> M3).
          assert (HN1sp : N1 !!! Regidx csp_rs1 = spr) by (rewrite /N1 lookup_total_insert_ne; [exact HM3sp | vm_compute; discriminate]).
          assert (Hpp3a : add_vec_int (mword_of_int (FR + 0x38) : mword 64) 2 = mword_of_int (FR + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp3a) in "Hpc".
          (* +0x3a c.ldsp s3,8(sp) : restore s3 = m!!!19 *)
          iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x3a)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
                    N1 (m !!! Regidx (mword_of_int 19 : mword 5)) (dqm:=DfracOwn 1)
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    with "Hsc Hhs Hcap Htlb Hpc Hfile Hi3a [Hc5] [-]").
          { iEval (rewrite HN1sp Hb5). iExact "Hc5". }
          iIntros "Hhs Hsc Hcap Htlb Hpc Hfile Hc5".
          iEval (rewrite HN1sp Hb5) in "Hc5".
          set (N2 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> N1).
          assert (HN2sp : N2 !!! Regidx csp_rs1 = spr) by (rewrite /N2 lookup_total_insert_ne; [exact HN1sp | vm_compute; discriminate]).
          assert (Hpp3c : add_vec_int (mword_of_int (FR + 0x3a) : mword 64) 2 = mword_of_int (FR + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp3c) in "Hpc".
          (* +0x3c c.ldsp s4,0(sp) : restore s4 = m!!!20 *)
          iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x3c)) (mword_of_int 0 : mword 6) (mword_of_int 20 : mword 5)
                    N2 (m !!! Regidx (mword_of_int 20 : mword 5)) (dqm:=DfracOwn 1)
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    with "Hsc Hhs Hcap Htlb Hpc Hfile Hi3c [Hc6] [-]").
          { iEval (rewrite HN2sp Hb6). iExact "Hc6". }
          iIntros "Hhs Hsc Hcap Htlb Hpc Hfile Hc6".
          iEval (rewrite HN2sp Hb6) in "Hc6".
          set (N3 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 20 : mword 5))]> N2).
          assert (HN3sp : N3 !!! Regidx csp_rs1 = spr) by (rewrite /N3 lookup_total_insert_ne; [exact HN2sp | vm_compute; discriminate]).
          assert (Hpp3e : add_vec_int (mword_of_int (FR + 0x3c) : mword 64) 2 = mword_of_int (FR + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp3e) in "Hpc".
          (* the restored map satisfies the epilogue's callee-saved-except side condition *)
          assert (HN3cs : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> csp_rs1 -> N3 !!! Regidx c = m !!! Regidx c).
          { intros c Hc N8 N9 Nsp.
            destruct (decide (c = mword_of_int 18)) as [->|Hn18].
            { rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
              rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
              rewrite /N1 lookup_total_insert; reflexivity. }
            destruct (decide (c = mword_of_int 19)) as [->|Hn19].
            { rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
              rewrite /N2 lookup_total_insert; reflexivity. }
            destruct (decide (c = mword_of_int 20)) as [->|Hn20].
            { rewrite /N3 lookup_total_insert; reflexivity. }
            rewrite /N3 lookup_total_insert_ne; [| congruence].
            rewrite /N2 lookup_total_insert_ne; [| congruence].
            rewrite /N1 lookup_total_insert_ne; [| congruence].
            apply HM3cs; assumption. }
          (* the token after the last free is [avail_inc on] = [Some (length ps)] *)
          simpl in Hcount.
          iEval (rewrite Hcount) in "Havail".
          iApply (frepi γ root_ppn Φ m N3 K ncnt a_noff a_int a_cpu γk (Some (length (p0 :: rest))) ltac:(lia)
                    Hretm HN3sp HN3cs
                    with "Htext Hsc Hhs Hcap Hcnt Htlb Hpc Hfile Hc1 Hc2 Hc3 [Hc4] [Hc5] [Hc6] Hdeepl Hqnoff Hqint Hqcpu Havail Hcont").
          { iExists _; iExact "Hc4". }
          { iExists _; iExact "Hc5". }
          { iExists _; iExact "Hc6". }
        + (* rest nonempty: bgeu TAKEN -> back-edge to 0x2a, recurse with rest0 *)
          assert (Hbtaken : zopz0zKzJ_u (M3 !!! Regidx (mword_of_int 18 : mword 5)) (M3 !!! Regidx (mword_of_int 9 : mword 5)) = true).
          { rewrite zge_negb_zlt. rewrite HM3s2 HM3s1.
            destruct Hprestq as (Hfitsq' & _ & _ & _). rewrite Hfitsq'. reflexivity. }
          assert (Htgt2a : add_vec (mword_of_int (FR + 0x34) : mword 64) (sign_extend' 64 (mword_of_int 8182 : mword 13)) = mword_of_int (FR + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
          iApply (wp_bgeu_taken_s_sconf γ root_ppn Φ (mword_of_int (FR + 0x34)) (mword_of_int 8182 : mword 13) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5)
                    M3 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbtaken
                    ltac:(rewrite Htgt2a; vm_compute; reflexivity)
                    with "Hsc Hhs Hcap Htlb Hpc Hfile Hi34 [-]").
          iNext. iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
          iEval (rewrite Htgt2a) in "Hpc".
          iApply ("IHf" $! M3 (q0 :: rest0') (avail_inc on) with "[] [] Hsc Hhs Hcap Hcnt Htlb Hpc Hfile Hpages Hdeepl Hqnoff Hqint Hqcpu Havail Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hcont").
          { iPureIntro. simpl in Hlen |- *. lia. }
          { iPureIntro. rewrite HM3s2 HM3s3 HM3s4 HM3sp HM3tp HM3s1.
            split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
            split; [reflexivity|]. split; [reflexivity|]. split; [exact HM3cs|].
            split; [exact Hprestq|]. split; [discriminate|].
            rewrite avail_inc_n_comm; exact Hcount. } }
      (* apply the loop at the entry (fuel = length of the page list) *)
      iApply ("Hloop" $! (length (p0 :: rest)) R11 (p0 :: rest) (Some 0%nat) with "[] [] Hsc Hhs Hcap Hcnt Htlbinv Hpc Hfile Hpages Hdeep Hqnoff [Hqint] Hqcpu Havail Hra Hs0 Hs1 Hslot4 Hslot5 Hslot6 Hcont").
      { iPureIntro. lia. }
      { iPureIntro. rewrite HR11s2 HR11s3 HR11s4 HR11sp HR11tp HR11s1.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [exact HR11cs|].
        split; [simpl; split; [exact Hfits0 | split; [exact Hp0eq | split; [exact Hpv0 | exact Hprest0]]]|].
        split; [discriminate|].
        rewrite avail_inc_n_Some0; reflexivity. }
      { iExists iv0; iExact "Hqint". }
  Qed.

End WpSconfFreerange.
