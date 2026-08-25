(* M-mode Rtype leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvFetchExec WpGpr InstrBytes SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
Require Import HartSwp WpMmodeSwpBase.   (* the [swp] execute catalogue *)
Require Import RegFile.
Require Import TsoCtx.
Import Defs.
Import Defs.

(* from WpGprLogic.v *)
Section WpLogicRTypeGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context {dqc : dfrac}.

  Lemma wp_or_gpr (pc : mword 64) (is_rvc : bool) (rs2 rs1 rd : mword 5)
      (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (or_vec (m !!! Regidx rs1) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc Hpc Hf Hinstr Hcont".
    iDestruct (mmode_config_cert with "Hmm") as "[#Hcert Hmm]".
    iApply (wp_instr pc (add_vec_int pc (if is_rvc then 2 else 4)) is_rvc
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) m
              (<[Regidx rd := regval_into_reg
                   (or_vec (m !!! Regidx rs1) (m !!! Regidx rs2))]> m)
              pmpcfg0 emp%I Hpmp Hstat
              with "Hmm Hpmpc Hpc Hf Hinstr [] [Hcont]").
    - iIntros "Hf HPC HnPC".
      change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) OR).
      iApply (swp_mono with "[HPC HnPC] [Hf]");
        [| iApply (swp_execute_RTYPE_OR rs2 rs1 rd m Hrd with "Hcert Hf") ].
      iIntros (e) "[-> Hf]". iSplitR; [done|]. iFrame "Hf HPC HnPC".
    - iNext. iIntros "Hmm Hpmpc Hpc Hf _".
      iApply ("Hcont" with "Hmm Hpmpc Hpc Hf").
  Qed.

  Lemma wp_and_gpr (pc : mword 64) (is_rvc : bool) (rs2 rs1 rd : mword 5)
      (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (and_vec (m !!! Regidx rs1) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc Hpc Hf Hinstr Hcont".
    iDestruct (mmode_config_cert with "Hmm") as "[#Hcert Hmm]".
    iApply (wp_instr pc (add_vec_int pc (if is_rvc then 2 else 4)) is_rvc
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)) m
              (<[Regidx rd := regval_into_reg
                   (and_vec (m !!! Regidx rs1) (m !!! Regidx rs2))]> m)
              pmpcfg0 emp%I Hpmp Hstat
              with "Hmm Hpmpc Hpc Hf Hinstr [] [Hcont]").
    - iIntros "Hf HPC HnPC".
      change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) AND).
      iApply (swp_mono with "[HPC HnPC] [Hf]");
        [| iApply (swp_execute_RTYPE_AND rs2 rs1 rd m Hrd with "Hcert Hf") ].
      iIntros (e) "[-> Hf]". iSplitR; [done|]. iFrame "Hf HPC HnPC".
    - iNext. iIntros "Hmm Hpmpc Hpc Hf _".
      iApply ("Hcont" with "Hmm Hpmpc Hpc Hf").
  Qed.

  (* wp_add_gpr -- the RTYPE ADD member of the family (the ExecuteAs target of
     c.mv / c.add, hence [is_rvc]-generic like its siblings).  Uses WpGpr's
     [exec_execute_RTYPE_ADD_gpr] / [gpr_rd_val]. *)
  Lemma wp_add_gpr (pc : mword 64) (is_rvc : bool) (rs2 rs1 rd : mword 5)
      (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec (m !!! Regidx rs1) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc Hpc Hf Hinstr Hcont".
    iDestruct (mmode_config_cert with "Hmm") as "[#Hcert Hmm]".
    iApply (wp_instr pc (add_vec_int pc (if is_rvc then 2 else 4)) is_rvc
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) m
              (<[Regidx rd := regval_into_reg
                   (add_vec (m !!! Regidx rs1) (m !!! Regidx rs2))]> m)
              pmpcfg0 emp%I Hpmp Hstat
              with "Hmm Hpmpc Hpc Hf Hinstr [] [Hcont]").
    - iIntros "Hf HPC HnPC".
      change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
      iApply (swp_mono with "[HPC HnPC] [Hf]");
        [| iApply (swp_execute_RTYPE_ADD rs2 rs1 rd m Hrd with "Hcert Hf") ].
      iIntros (e) "[-> Hf]". iSplitR; [done|]. iFrame "Hf HPC HnPC".
    - iNext. iIntros "Hmm Hpmpc Hpc Hf _".
      iApply ("Hcont" with "Hmm Hpmpc Hpc Hf").
  Qed.

End WpLogicRTypeGpr.
