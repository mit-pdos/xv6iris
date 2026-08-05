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
  Lemma wp_jal_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
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
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hstat Hrd Halign) "Hmm Hpmpc [Hpc Hnpc] Hfmap Hinstr Hcont".
    destruct (aligned4_jump_bits _ Halign) as [Hal0 Hal1].
    iApply (wp_instr Φ pc false (JAL (imm, Regidx rd)) pmpcfg0
              Hpmp Hstat with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    (* tick nextPC to [pc+4]: this ticked value is the link JAL writes to rd,
       and JAL then overwrites nextPC with the jump target. *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* PC unchanged by the nextPC tick; still [pc] *)
    assert (Hpcv : register_lookup PC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = pc).
    { rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    (* the link value: [register_lookup nextPC (set_reg σ nextPC (pc+4)) = pc+4] *)
    assert (Hlink : register_lookup nextPC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = add_vec_int pc 4).
    { rewrite ?sregs_set_reg. rewrite register_lookup_set. reflexivity. }
    (* nextPC := target [add_vec pc (sign_extend' 64 imm)] (the JUMP) *)
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm))
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* write rd := link = pc+4 (rd <> 0, so its entry is the real points-to) *)
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg (add_vec_int pc 4))
                 with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int pc 4))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                        nextPC (add_vec pc (sign_extend' 64 imm)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec_int pc 4))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
      rewrite (exec_execute_JAL_gpr imm rd (set_reg σ nextPC (add_vec_int pc 4))
                 Hrd).
      - rewrite Hpcv. rewrite Hlink. reflexivity.
      - rewrite Hpcv. exact Hal0.
      - rewrite Hpcv. exact Hal1. }
    iSplitL "Hreg Hmem".
    { rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    (* continuation: PC (from wp_instr) is [register_lookup nextPC s_exec] = the
       target; own nextPC ↦ target too, giving [pc_is target]. *)
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                         nextPC (add_vec pc (sign_extend' 64 imm)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec_int pc 4))).(sregs)
             = add_vec pc (sign_extend' 64 imm)).
    { rewrite ?sregs_set_reg.
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] Hfmap").
  Qed.
End WpJalGpr.
