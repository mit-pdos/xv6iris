From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RegFile RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec WpGpr WpLeafCommon.
Require Import InstrBytes KernelText.
Require Import WpRvcBridge.
From iris.base_logic.lib Require Import invariants.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Section WpSpin.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* The [spin] symbol at 0x8000001a (just past _entry's [jal start]): a single
     compressed self-jump [c.j spin] = [0xa001], the halt loop each hart runs
     forever once start() returns.  It decodes to [C_J imm_spin] whose 11-bit
     immediate is all-zero (jump offset 0), so it targets its own PC. *)
  Definition pc_spin : mword 64 := mword_of_int KernelSyms.spin.
  Definition h_spin : mword 16 := mword_of_int 0xa001.
  Definition imm_spin : mword 11 :=
    concat_vec (concat_vec (concat_vec (concat_vec (concat_vec (concat_vec
      (concat_vec (subrange_vec_dec h_spin 12 12) (subrange_vec_dec h_spin 8 8))
      (subrange_vec_dec h_spin 10 9)) (subrange_vec_dec h_spin 6 6))
      (subrange_vec_dec h_spin 7 7)) (subrange_vec_dec h_spin 2 2))
      (subrange_vec_dec h_spin 11 11)) (subrange_vec_dec h_spin 5 3).
  (* C_J expands (ExecuteAs) to [JAL (jimm_spin, x0)]; jimm_spin = 0. *)
  Definition jimm_spin : mword 21 := sign_extend' 21 (concat_vec imm_spin ('b"0")).

  (* ---- decode: the compressed self-jump decodes to [C_J imm_spin] ---- *)
  Lemma decode_C_J s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed h_spin) s = Some (C_J imm_spin, s).
  Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

  (* ---- the two execute steps (C_J -> JAL x0 -> nextPC := PC) ---- *)
  Lemma exec_execute_C_J (imm : mword 11) s :
    exec (execute (C_J imm)) s
      = Some (ExecuteAs (JAL (sign_extend' 21 (concat_vec imm ('b"0")), zreg)), s).
  Proof. unfold execute. cbn match. unfold execute_C_J. apply exec_returnM. Qed.

  (* JAL to a 2-byte-aligned target with the C extension enabled: the
     misalignment check ([bit1] && not Zca) is false (port of
     WpKernelvecNew.kv_exec_jump_to_zca). *)
  Lemma sp_exec_jump_to_zca (target : mword 64) s :
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

  (* JAL with rd = x0 (as C_J expands to): no link write, so the resulting
     state is just [nextPC := target]. *)
  Lemma exec_execute_JAL_zreg_zca (imm : mword 21) s :
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
    rewrite (exec_bind_Some _ _ _ _ _ (sp_exec_jump_to_zca _ s Halign Hzca)).
    cbn match.
    unfold zreg.
    rewrite (exec_bind0_Some _ _ _ _ _
      (exec_wX_bits_gpr (zero_extend' 5 ('b"00")) (register_lookup nextPC s.(sregs))
         (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))))).
    apply exec_returnm.
  Qed.

  (* ---- the [instr] fact for the spin instruction, off the kernel text ---- *)
  Lemma spin_instr :
    kernel_text -∗ instr pc_spin true (JAL (jimm_spin, zreg)).
  Proof.
    mk_rvc KernelSyms.spin h_spin pc_spin (JAL (jimm_spin, zreg))
      decode_C_J exec_execute_C_J.
  Qed.

  (* ================================================================= *)
  (*  THE THEOREM: the spin loop runs forever (proved by iLöb).        *)
  (*                                                                   *)
  (*  There is NO postcondition continuation: [spin] never leaves the  *)
  (*  self-jump, so the only way to discharge [WP Loop] is coinductive *)
  (*  -- a Löb-induction hypothesis [IH : ▷ (resources -∗ WP Loop)].   *)
  (*  We take ONE fetch/decode/execute step of [c.j spin] with the     *)
  (*  ordinary leaf engine [wp_instr]; because [wp_instr]'s continuation *)
  (*  now lands on [▷ WP Loop] (it exposes the step's later instead of   *)
  (*  stripping it internally), that later strips [IH] and closes the    *)
  (*  loop back onto [pc_spin] with every resource unchanged.           *)
  (* ================================================================= *)
  Lemma wp_spin (Φ : mval -> iProp Σ) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc_spin -∗
    gpr_file m -∗
    kernel_text -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    assert (Hbit0 : eq_vec (access_vec_dec pc_spin 0) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (Htgt : add_vec pc_spin (sign_extend' 64 jimm_spin) = pc_spin)
      by (apply bv_eq; vm_compute; reflexivity).
    iIntros (Hpmp) "Hmm Hpmpc Hpc Hfile #Htext".
    (* pull the (persistent, constant) misa.C fact out once, so it survives Löb *)
    iDestruct "Hmm" as "(#Hhw & Hmmrest)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & %HmisaC & _)".
    iAssert (mmode_config (DfracOwn q)) with "[Hmmrest]" as "Hmm".
    { rewrite /mmode_config. iFrame "Hhw". iExact "Hmmrest". }
    (* Löb: assume the loop already runs from any resource snapshot at pc_spin *)
    iRevert "Hmm Hpmpc Hpc Hfile".
    iLöb as "IH".
    iIntros "Hmm Hpmpc Hpc Hfile".
    iPoseProof (spin_instr with "Htext") as "Hinstr".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    (* one leaf step of [c.j spin]; [wp_instr] hands back [▷ WP Loop] *)
    iApply (wp_instr Φ pc_spin true (JAL (jimm_spin, zreg)) pmpcfg0 Hpmp
              with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc_spin 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc_spin 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc_spin).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Hpceq | vm_compute; reflexivity]. }
    assert (HzcaC : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [rewrite Lmisa; exact HmisaC | vm_compute; reflexivity]. }
    assert (Halign_spc : eq_vec (access_vec_dec
              (add_vec (register_lookup PC s_pc.(sregs)) (sign_extend' 64 jimm_spin)) 0)
              ('b"0") = true).
    { rewrite Hpcv. rewrite Htgt. exact Hbit0. }
    assert (Hexec_spc :
      exec (execute (JAL (jimm_spin, zreg))) s_pc
      = Some (RETIRE_SUCCESS, set_reg s_pc nextPC pc_spin)).
    { change (execute (JAL (jimm_spin, zreg))) with (execute_JAL jimm_spin zreg).
      rewrite (exec_execute_JAL_zreg_zca jimm_spin s_pc Halign_spc
                 (exec_currentlyEnabled_Zca s_pc HzcaC)).
      rewrite Hpcv. rewrite Htgt. reflexivity. }
    iMod (reg_update _ nextPC _ pc_spin with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC pc_spin).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hexec_spc. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    (* continuation: PC (from wp_instr) = nextPC of s_exec = pc_spin; close the
       loop with the Löb hypothesis (its later is stripped by [wp_instr]'s). *)
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc nextPC pc_spin).(sregs) = pc_spin).
    { rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    (* strip [wp_instr]'s exposed later: it discharges [IH]'s. *)
    iNext.
    iApply ("IH" with "Hmm' Hpmpc' [$Hpc' $Hnpc] Hfile").
  Qed.

End WpSpin.
