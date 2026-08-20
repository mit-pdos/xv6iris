(* WpMmodeJal.v -- the JAL family, stated on the new [instr] / [mmode_config]
   / [gpr_file] layer (cf. wp_auipc_gpr).  JAL has no source register: it
   writes rd := pc+4 (the return address) AND jumps, setting nextPC := the
   target [pc + sign_extend(imm)].  Unlike the straight-line templates
   (ADDI/AUIPC) this is a CONTROL-FLOW instruction: the continuation lands on
   [pc_is target], NOT [pc_is (pc+4)].  Built on [wp_instr]. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras ExecCommon WpGpr RegFile.
Require Import InstrBytes.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
Require Import HartSwp WpMmodeJump.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* register-generic JAL execute (reused verbatim from the old formulation --
   representation-independent): writes rd := link (the old nextPC), and sets
   nextPC := target [PC + sign_extend imm]. *)
Lemma exec_execute_JAL_gpr (imm : mword 21) (rd : mword 5) s :
  uint rd <> 0 ->
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  bit_to_bool (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 1) = false ->
  exec (execute_JAL imm (Regidx rd)) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (register_lookup nextPC s.(sregs)))).
Proof.
  intros Hrd Halign Hbit1.
  apply (exec_execute_JAL imm (Regidx rd) s _ Halign Hbit1).
  rewrite (exec_wX_bits_gpr rd (register_lookup nextPC s.(sregs))
             (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  reflexivity.
Qed.

Section WpJalGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [instr]/[mmode_config]-formulated register-generic JAL WP, built on
     [wp_instr] -- stated like [wp_auipc_gpr] (no source register) BUT it is a
     control-flow instruction:
       - it writes rd := pc+4 (the return/link address); and
       - it jumps, so the continuation's [pc_is] is the TARGET
         [add_vec pc (sign_extend' 64 imm)], not [pc+4].
     [wp_instr] runs [execute (JAL ..)] against the state where nextPC has
     already been ticked to [pc+4] (that ticked value becomes the link that JAL
     writes to rd); the JAL execute then overwrites nextPC with the target, so
     [wp_instr] hands the continuation [PC := target].  The two target-alignment
     side conditions ([bit0 = 0], [bit1 = false]) are JAL-specific (AUIPC has
     none). *)
  Lemma wp_jal_gpr (pc : mword 64) (rd : mword 5)
      (imm : mword 21) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    is_aligned_paddr (Physaddr (add_vec pc (sign_extend' 64 imm))) 4 = true ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (JAL (imm, Regidx rd)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd Halign) "Hmm Hpmpc Hpc Hf Hinstr Hcont".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & %Hmisaval & %Hsecval & _)".
    subst misa0 mseccfg0.
    (* the jump's own alignment side condition: bit 0 of a 4-aligned target *)
    assert (Hb0 : eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0)
                    ('b"0") = true).
    { destruct (align4_low_bits (add_vec pc (sign_extend' 64 imm)) Halign)
        as [H0 _].
      unfold neq_vec in H0. by apply negb_false_iff in H0. }
    iApply (wp_instr pc (add_vec pc (sign_extend' 64 imm)) false
              (JAL (imm, Regidx rd)) m
              (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0)%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hf Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iApply (swp_mono with "[Hhs_k Hmst_k Hpmpc_k] [Hf HPC HnPC Hpriv_k]");
        [| iApply (swp_execute_JAL (DfracOwn (q/2)) imm rd m pc
                     (add_vec_int pc 4) Hrd Hb0
                     with "Hcert Hf HPC HnPC Hpriv_k Hmseccfg Hmisa") ].
      iIntros (e) "(-> & Hf & HPC & HnPC & Hpriv_k & _ & _)".
      iSplitR; [done|]. iFrame "Hf HPC HnPC".
      iSplitL "Hhs_k Hpriv_k Hmst_k".
      { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
      iFrame "Hpmpc_k".
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' [Hmm_k' Hpmpc_k']".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf'").
  Qed.
End WpJalGpr.
