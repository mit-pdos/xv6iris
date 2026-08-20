(* M-mode Jalr leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase. *)
Require Import WpMmodeLeafBase.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvFetchExec WpGpr RegFile InstrBytes RiscvExtras SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
Require Import HartSwp WpMmodeJump.
Import Defs.
Import Defs.

(* from WpGprJalr.v *)
Section WpJalrGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [instr]/[mmode_config]-formulated register-generic JALR WP, built on
     [wp_instr].  Like [wp_addi_gpr] it reads rs1 off the [gpr_file] and writes
     rd, but the write is the return address [pc+4] and the continuation's
     [pc_is] is the JUMP TARGET.  JALR's execute reads mseccfg.MLPE (for the
     Zicfilp check) and cur_privilege; these cells are held separately from
     [mmode_config] (which [wp_instr] takes) and handed back to the caller. *)
End WpJalrGpr.

(* from WpGprRvc.v *)
Section RvcRet.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [wp_cret_gpr] for a c.ret return target.  Under the C extension (misa.C,
     held by [mmode_config]'s [hw_config]) the model's jalr accepts a 2-aligned
     target, which [ret_pc] is by construction ([ret_pc_aligned]) -- so, unlike
     the 4-aligned leaf, this needs no alignment premise at all. *)
  Lemma wp_cret_gpr_zca (pc : mword 64) (ra : mword 5)
      (m : regfile) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint ra <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (ret_pc (m !!! Regidx ra)) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hra) "Hmm Hpmpc Hpc Hf Hinstr Hcont".
    (* keep HALF the config bundle: the jump's [update_elp_state] and
       [jump_to] read cur_privilege / mseccfg / misa, and wp_instr is about to
       take the bundle.  misa and mseccfg are PERSISTENT so they survive on
       their own; only cur_privilege needs the fraction split. *)
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & %Hmisaval & %Hsecval & _)".
    subst misa0 mseccfg0.
    iApply (wp_instr pc (ret_pc (m !!! Regidx ra)) true
              (JALR (zeros' 12, Regidx ra, zreg)) m m pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0)%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hf Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k] [Hcont]").
    - iIntros "Hf HPC HnPC".
      change zreg with (Regidx cli_rs1).
      iApply (swp_mono with "[HPC Hhs_k Hmst_k Hpmpc_k] [Hf HnPC Hpriv_k]");
        [| iApply (swp_execute_JALR_ret (DfracOwn (q/2)) ra cli_rs1 m
                     (add_vec_int pc 2) ltac:(vm_compute; reflexivity)
                     with "Hcert Hf HnPC Hpriv_k Hmseccfg Hmisa") ].
      iIntros (e) "(-> & Hf & HnPC & Hpriv_k & _ & _)".
      iSplitR; [done|]. iFrame "Hf HPC HnPC".
      iSplitL "Hhs_k Hpriv_k Hmst_k".
      { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
      iFrame "Hpmpc_k".
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' [Hmm_k' Hpmpc_k']".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf'").
  Qed.

End RvcRet.
