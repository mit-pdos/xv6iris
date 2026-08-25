(* M-mode Itype leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RegFile RiscvPtsto RiscvFetchExec WpGpr InstrBytes SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
Require Import HartSwp WpMmodeSwpBase.   (* the [swp] execute catalogue *)
Require Import TsoCtx.
Import Defs.
Import Defs.

(* from WpGprAddi.v *)
Section WpAddiGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context {dqc : dfrac}.

  (* [instr]/[mmode_config]-formulated register-generic ADDI WP, built on
     [wp_instr].  All the fetch/decode/config machinery is now packaged: the
     caller supplies [mmode_config] (ambient M-mode config, incl. the minstret
     invariant and the mstatus.MIE fact) and [instr pc false (ITYPE .. ADDI)]
     (the instruction at pc decodes to ADDI, 4-byte).  This lemma's only real
     work is the ADDI execute: read rs1 and rd off the [gpr_file], run the
     register-generic execute, and rebuild the file.  [wp_instr] discharges
     fetch / decode / dispatchInterrupt / minstret and hands [mmode_config]
     back to the continuation. *)
  Lemma wp_addi_gpr (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5)
      (imm : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc Hpc Hf Hinstr Hcont".
    iDestruct (mmode_config_cert with "Hmm") as "[#Hcert Hmm]".
    iApply (wp_instr pc (add_vec_int pc (if is_rvc then 2 else 4)) is_rvc
              (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) m
              (<[Regidx rd := regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))]> m)
              pmpcfg0 emp%I Hpmp Hstat
              with "Hmm Hpmpc Hpc Hf Hinstr [] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iApply (swp_mono with "[HPC HnPC] [Hf]");
        [| iApply (swp_execute_rw rs1 rd m (execute (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)))
               RETIRE_SUCCESS (fun a => add_vec a (sign_extend' 64 imm)) eq_refl Hrd with "Hcert Hf") ].
      iIntros (e) "[-> Hf]". iSplitR; [done|]. iFrame "Hf HPC HnPC".
    - iNext. iIntros "Hmm Hpmpc Hpc Hf _".
      iApply ("Hcont" with "Hmm Hpmpc Hpc Hf").
  Qed.
End WpAddiGpr.

(* from WpGprLogic.v *)
Section WpLogicITypeGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context {dqc : dfrac}.

  Lemma wp_ori_gpr (pc : mword 64) (rs1 rd : mword 5)
      (imm : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (or_vec (m !!! Regidx rs1) (sign_extend' 64 imm))]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc Hpc Hf Hinstr Hcont".
    iDestruct (mmode_config_cert with "Hmm") as "[#Hcert Hmm]".
    iApply (wp_instr pc (add_vec_int pc 4) false
              (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) m
              (<[Regidx rd := regval_into_reg (or_vec (m !!! Regidx rs1) (sign_extend' 64 imm))]> m)
              pmpcfg0 emp%I Hpmp Hstat
              with "Hmm Hpmpc Hpc Hf Hinstr [] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iApply (swp_mono with "[HPC HnPC] [Hf]");
        [| iApply (swp_execute_rw rs1 rd m (execute (ITYPE (imm, Regidx rs1, Regidx rd, ORI)))
               RETIRE_SUCCESS (fun a => or_vec a (sign_extend' 64 imm)) eq_refl Hrd with "Hcert Hf") ].
      iIntros (e) "[-> Hf]". iSplitR; [done|]. iFrame "Hf HPC HnPC".
    - iNext. iIntros "Hmm Hpmpc Hpc Hf _".
      iApply ("Hcont" with "Hmm Hpmpc Hpc Hf").
  Qed.


End WpLogicITypeGpr.
