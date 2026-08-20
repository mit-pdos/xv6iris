(* ProofSpin.v -- the proof of [spin]'s whole-function spec (SpecSpin.v), as a
   sealed module.  [spin] calls nothing, so SpinProof takes no functor
   arguments.

   The decode side lives here: [spin] is the single compressed self-jump
   [c.j spin] = [0xa001] at 0x8000001a.  It decodes to [C_J imm_spin] whose
   11-bit immediate is all-zero (jump offset 0), so it targets its own PC. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RegFile RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec WpGpr ExecCommon.
Require Import InstrBytes KernelText.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
Require Import HartSwp WpMmodeLeafBase WpMmodeJump.
Require Import WpRvcBridge.
From iris.base_logic.lib Require Import invariants.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpMmodeLeafBase.
Require Import SpecSpin.
Local Open Scope Z_scope.

Module SpinProof : SPIN.
Section ProofSpin.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

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

  (* JAL to a 2-byte-aligned target with the C extension enabled: the
     misalignment check ([bit1] && not Zca) is false (port of
     ProofKernelvec.kv_exec_jump_to_zca). *)
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
  Lemma wp_spin (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    wp_spin_body m pmpcfg0 q.
  Proof.
    cbv beta delta [wp_spin_body].
    assert (Hbit0 : eq_vec (access_vec_dec pc_spin 0) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (Htgt : add_vec pc_spin (sign_extend' 64 jimm_spin) = pc_spin)
      by (apply bv_eq; vm_compute; reflexivity).
    iIntros (Hpmp) "Hmm Hpmpc Hpc Hfile #Htext".
    assert (Hspin_static : forall j, (j < 4)%nat ->
              KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc_spin j)) KP_rx).
    { apply KptPt.instr_window_static. intros j Hj. unfold addr_is_text.
      destruct j as [|[|[|[|k]]]]; try lia;
        (split; [vm_compute; discriminate | vm_compute; reflexivity]). }
    (* Löb: assume the loop already runs from any resource snapshot at pc_spin *)
    iRevert "Hmm Hpmpc Hpc Hfile".
    iLöb as "IH".
    iIntros "Hmm Hpmpc Hpc Hfile".
    iPoseProof (spin_instr with "Htext") as "Hinstr".
    (* keep half the bundle: [jump_to] reads misa (persistent) and the leaf
       needs cur_privilege for [swp_execute_JAL_zreg]'s footprint *)
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & %Hmisaval & %Hsecval & _)".
    subst misa0 mseccfg0.
    iApply (wp_instr pc_spin pc_spin true (JAL (jimm_spin, zreg)) m m pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0)%I
              Hpmp Hspin_static
              with "Hmm_wp Hpmpc_wp Hpc Hfile Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k] [IH]").
    - iIntros "Hf HPC HnPC".
      change zreg with (Regidx cli_rs1).
      iApply (swp_mono with "[Hhs_k Hmst_k Hpmpc_k] [Hf HPC HnPC Hpriv_k]");
        [| iApply (swp_execute_JAL_zreg (DfracOwn (q/2)) jimm_spin cli_rs1 m
                     pc_spin (add_vec_int pc_spin 2)
                     ltac:(vm_compute; reflexivity)
                     ltac:(rewrite Htgt; exact Hbit0)
                     with "Hcert Hf HPC HnPC Hpriv_k Hmseccfg Hmisa") ].
      iIntros (e) "(-> & Hf & HPC & HnPC & Hpriv_k & _ & _)".
      rewrite Htgt.
      iSplitR; [done|]. iFrame "Hf HPC HnPC".
      iSplitL "Hhs_k Hpriv_k Hmst_k".
      { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
      iFrame "Hpmpc_k".
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' [Hmm_k' Hpmpc_k']".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("IH" with "Hmm'' Hpmpc'' Hpc' Hf'").
  Qed.

End ProofSpin.
End SpinProof.
