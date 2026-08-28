(* M-mode Utype leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase. *)
Require Import WpMmodeLeafBase.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvFetchExec WpGpr InstrBytes SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values RegFile.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
Require Import HartSwp WpMmodeSwpBase.   (* the [swp] execute catalogue *)
Require Import RiscvExtras.
Import Defs.
Import Defs.

(* from WpGprAuipc.v *)
Section WpAuipcGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [instr]/[mmode_config]-formulated register-generic AUIPC WP, built on
     [wp_instr] -- stated exactly like [wp_addi_gpr] but with no source
     register: the result is [pc + auipc_off imm].  [gpr_file] is indexed by
     [regidx] and complete, so no membership obligation; [rd <> 0] is kept
     (the write to x0 is a no-op). *)
  Lemma wp_auipc_gpr (pc : mword 64) (rd : mword 5)
      (imm : mword 20) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec pc (auipc_off imm))]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc Hpc Hf Hinstr Hcont".
    iDestruct (mmode_config_cert with "Hmm") as "[#Hcert Hmm]".
    iApply (wp_instr pc (add_vec_int pc 4) false
              (UTYPE (imm, Regidx rd, AUIPC)) m
              (<[Regidx rd := regval_into_reg (add_vec pc (auipc_off imm))]> m)
              pmpcfg0 emp%I Hpmp Hstat
              with "Hmm Hpmpc Hpc Hf Hinstr [] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iApply (swp_mono with "[HnPC] [Hf HPC]");
        [| iApply (swp_execute_pcw rd m
                     (execute (UTYPE (imm, Regidx rd, AUIPC)))
                     RETIRE_SUCCESS pc
                     (fun w => add_vec w (auipc_off imm)) eq_refl Hrd
                     with "Hcert Hf HPC") ].
      iIntros (e) "(-> & Hf & HPC)". iSplitR; [done|]. iFrame "Hf HPC HnPC".
    - iApply bi.later_intro. iIntros "Hmm Hpmpc Hpc Hf _".
      iApply ("Hcont" with "Hmm Hpmpc Hpc Hf").
  Qed.
End WpAuipcGpr.

(* from WpGprLui.v *)
Section WpLuiGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [instr]/[mmode_config]-formulated register-generic LUI WP, built on
     [wp_instr] -- stated exactly like [wp_auipc_gpr] but the written value is
     the ABSOLUTE [luival imm] (not PC-relative).  [gpr_file] is indexed by
     [regidx] and complete, so no membership obligation; [rd <> 0] is kept
     (the write to x0 is a no-op). *)
  Lemma wp_lui_gpr (pc : mword 64) (is_rvc : bool) (rd : mword 5)
      (imm : mword 20) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (UTYPE (imm, Regidx rd, LUI)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (luival imm)]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc Hpc Hf Hinstr Hcont".
    iDestruct (mmode_config_cert with "Hmm") as "[#Hcert Hmm]".
    iApply (wp_instr pc (add_vec_int pc (if is_rvc then 2 else 4)) is_rvc
              (UTYPE (imm, Regidx rd, LUI)) m
              (<[Regidx rd := regval_into_reg (luival imm)]> m)
              pmpcfg0 emp%I Hpmp Hstat
              with "Hmm Hpmpc Hpc Hf Hinstr [] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iApply (swp_mono with "[HPC HnPC] [Hf]");
        [| iApply (swp_execute_pure_w rd m (execute (UTYPE (imm, Regidx rd, LUI)))
               RETIRE_SUCCESS (luival imm) eq_refl Hrd with "Hcert Hf") ].
      iIntros (e) "[-> Hf]". iSplitR; [done|]. iFrame "Hf HPC HnPC".
    - iApply bi.later_intro. iIntros "Hmm Hpmpc Hpc Hf _".
      iApply ("Hcont" with "Hmm Hpmpc Hpc Hf").
  Qed.
End WpLuiGpr.
