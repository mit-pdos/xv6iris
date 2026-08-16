(* HartMFetch.v -- the fetch path, one [swp] fact per model function.

   [fetch] is decomposed along its OWN structure: a [catch_early_return]
   region whose body binds [liftR sub] for each call it makes.  The walk is
   uniform and mechanical:

     - peel a call with [swp_use_cer{,2,3}] (the depth is how many
       MR-level binds sit between the [liftR] and the handler; matching is
       first-order, so the former is never guessed);
     - clear the glue with the REWRITE equations [mbind_ret], [mbind0_ret],
       [mliftR_ret], [mcer_ret] -- never with a cbn wide enough to unfold
       [Defs.bind], which re-spells the goal as [Interface.iMon_bind] and
       breaks every match downstream;
     - unfold [Defs.and_boolM] / [Defs.or_boolM] with [unfold], not [cbn]
       (cbn declines: unfolding them exposes no iota redex);
     - resolve each test from a premise by [rewrite].

   WHAT THE 4-ALIGNED M-MODE PATH ACTUALLY TOUCHES: five PC reads (the two
   feeding [ext_fetch_check_pc], the two misalignment bit tests, the
   4-alignment test) plus two more feeding [fetch_bytes].  [Ext_Zca] is
   never read -- with bit 1 clear the [and_boolM] short-circuits before it
   -- and [Ext_Ziccif] is a constant true from the config, no read at all.

   STILL OWED: [swp_fetch_bytes], which is [translateAddr] followed by
   [mem_read] (whose own chain is [mem_read_priv] -> [checked_mem_read],
   where [pmpCheck] -- HartMPmp -- and the memory event live). *)
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartEvents.
Local Open Scope Z_scope.

Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

(* [currentlyEnabled Ext_Ziccif] is a CONSTANT true (no read: hartSupports
   answers from the config) -- a pure conversion *)
Local Lemma mf_cE_Ziccif_eq_local : currentlyEnabled Ext_Ziccif = returnM true.
Proof. reflexivity. Qed.

Local Ltac mf_glue :=
  cbn beta iota zeta delta [get_config_rvfi ext_fetch_check_pc].

Section fetch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma swp_fetch (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pc : SailStdpp.Values.mword 64)
      (w : SailStdpp.Values.mword 32) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch_bytes pc pc 4)
         (fun r => ⌜r = @FetchBytes_Success 4 w⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_Base w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpc Hpc Hb0 Hb1 Hal Hrvc.
    iIntros "#Hcert Hrw Hro Hfb".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch. mf_glue.
    (* the two PC reads feeding ext_fetch_check_pc *)
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". mf_glue.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". mf_glue.
    rewrite mbind0_ret. unfold Defs.or_boolM.
    (* the misalignment test's bit-0 read *)
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta. rewrite Hb0.
    unfold Defs.and_boolM.
    (* the bit-1 read; with a 4-aligned PC it short-circuits before Zca *)
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta. rewrite Hb1.
    rewrite mbind_ret. cbn beta.
    (* the 4-alignment test; Ziccif is a constant true, no read *)
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta. rewrite Hal.
    rewrite mf_cE_Ziccif_eq_local /returnM mliftR_ret mbind_ret. cbn beta.
    (* the two PC reads feeding fetch_bytes *)
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    (* THE CALL *)
    iApply (swp_use_cer (fetch_bytes pc pc 4) _ _ C HC
              with "[Hrw Hro Hfb] [-]").
    { iApply ("Hfb" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite Hrvc mcer_ret.
    iApply ("Hcont" $! (F_Base w)). by iFrame.
  Qed.

End fetch.
