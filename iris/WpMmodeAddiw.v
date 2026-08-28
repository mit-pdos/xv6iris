(* M-mode Addiw leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvFetchExec WpGpr RegFile InstrBytes SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
Require Import HartSwp WpMmodeSwpBase.   (* the [swp] execute catalogue *)
Import Defs.
Import Defs.

(* from WpGprAddi.v *)
Section WpAddiwGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Lemma wp_addiw_gpr (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5) (immv : mword 12)
      (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (ADDIW (immv, Regidx rs1, Regidx rd)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg (sign_extend' 64
          (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0))]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc Hpc Hf Hinstr Hcont".
    iDestruct (mmode_config_cert with "Hmm") as "[#Hcert Hmm]".
    iApply (wp_instr pc (add_vec_int pc (if is_rvc then 2 else 4)) is_rvc
              (ADDIW (immv, Regidx rs1, Regidx rd)) m
              (<[Regidx rd := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0))]> m)
              pmpcfg0 emp%I Hpmp Hstat
              with "Hmm Hpmpc Hpc Hf Hinstr [] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iApply (swp_mono with "[HPC HnPC] [Hf]");
        [| iApply (swp_execute_rw2 rs1 rd m (execute (ADDIW (immv, Regidx rs1, Regidx rd)))
               RETIRE_SUCCESS
               (fun a => sign_extend' 64 (subrange_vec_dec (add_vec a (sign_extend' 64 immv)) 31 0))
               eq_refl Hrd with "Hcert Hf") ].
      iIntros (e) "[-> Hf]". iSplitR; [done|]. iFrame "Hf HPC HnPC".
    - iApply bi.later_intro. iIntros "Hmm Hpmpc Hpc Hf _".
      iApply ("Hcont" with "Hmm Hpmpc Hpc Hf").
  Qed.

End WpAddiwGpr.
