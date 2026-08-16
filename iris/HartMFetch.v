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

   THE OTHER TOOL, and the judgement the walk turns on: [hfrun] DOES NOT
   CARE about [catch_early_return].  It walks nodes, and the term structure
   reduces out of the way -- so any maximal stretch whose reads are all
   pinned and which contains NO memory event gets a two-line proof no
   matter how it is wrapped.  [translateAddr] at Bare is the case in point:
   the whole page-translation function, ten lines, 2 s.

   STILL OWED: [checked_mem_read], which is where [pmpCheck] (HartMPmp's
   fact) and the memory event live, under an [untilMT] misalignment loop
   that runs once for an aligned 4-byte fetch. *)
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartEvents HartMPmp.
Require Import RiscvExtras.
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

Local Ltac tr_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.returnR
     Defs.read_reg Defs.early_return Defs.throw Defs.and_boolM Defs.or_boolM
     andb orb negb not].

Local Ltac tr_read :=
  rewrite hfrun_read;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

(* the identity translation's address, at the spelling [translateAddr]'s
   Bare arm produces *)
Local Lemma zext_pc_id (x : SailStdpp.Values.mword 64) :
  zero_extend' 64 (bits_of_virtaddr (Virtaddr x)) = x.
Proof. exact (fetch_pa_id x). Qed.

Lemma hfrun_translateAddr_M (D Drw : gset register) (rs : regstate)
    (pc : SailStdpp.Values.mword 64) :
  (mstatus : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  register_lookup cur_privilege rs = Machine ->
  hfrun 8 D Drw rs (translateAddr (Virtaddr pc) (InstructionFetch tt))
  = Some (Values.Ok (Physaddr pc, PBMT_PMA, init_ext_ptw), rs).
Proof.
  intros HD1 HD2 Hpriv.
  unfold translateAddr. tr_cbn.
  tr_read. tr_cbn.
  tr_read. rewrite Hpriv. tr_cbn.
  unfold effectivePrivilege.
  change (Instances.generic_neq (InstructionFetch tt) (InstructionFetch tt))
    with false. tr_cbn.
  unfold translationMode.
  change (Instances.generic_eq Machine Machine) with true. tr_cbn.
  unfold is_shadow_stack_access. tr_cbn.
  change (Instances.generic_eq Bare Bare) with true. tr_cbn.
  rewrite zext_pc_id. apply hfrun_ret.
Qed.

Section fetch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma swp_translateAddr_M (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pc : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
      (fun r => ⌜r = Values.Ok (Physaddr pc, PBMT_PMA, init_ext_ptw)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    apply (swp_hfrun 8 Drw Dro Df rs rs _ _ Hdisj).
    exact (hfrun_translateAddr_M (Drw ∪ Dro) Drw rs pc HDmst HDpriv Hpriv).
  Qed.

  Lemma swp_mem_read_M (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : physaddr) (w : SailStdpp.Values.mword 32) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Machine pa 4
              false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    swp (mem_read (InstructionFetch tt) PBMT_PMA pa 4 false false false)
      (fun r => ⌜r = Values.Ok w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Hcmr".
    unfold mem_read.
    iApply (swp_bind_use (Defs.read_reg mstatus) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    unfold effectivePrivilege.
    change (Instances.generic_neq (InstructionFetch tt) (InstructionFetch tt))
      with false.
    cbn beta iota zeta delta [Defs.returnm returnM].
    rewrite mbind_ret.
    unfold mem_read_priv, mem_read_priv_meta.
    cbn beta iota.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I) _
              with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_bind_use _ _
                (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I) _
                with "[Hrw Hro Hcmr] [-]").
      - iApply ("Hcmr" with "Hrw Hro").
      - iIntros (v) "(-> & Hrw & Hro)". iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro)". iApply swp_ret.
    cbn [MemoryOpResult_drop_meta]. by iFrame.
  Qed.

  Lemma swp_fetch_bytes_M (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pc : SailStdpp.Values.mword 64)
      (w : SailStdpp.Values.mword 32) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Machine
              (Physaddr pc) 4 false false false false)
         (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                    hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I)) -∗
    swp (fetch_bytes pc pc 4)
      (fun r => ⌜r = @FetchBytes_Success 4 w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Hcmr".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch_bytes.
    cbn beta iota zeta delta [ext_fetch_check_pc].
    rewrite mbind0_ret.
    iApply (swp_use_cer (translateAddr (Virtaddr pc) (InstructionFetch tt))
              _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_translateAddr_M Drw Dro Df rs pc Hdisj HDmst HDpriv Hpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer
              (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pc) 4
                 false false false) _ _ C HC with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_mem_read_M Drw Dro Df rs (Physaddr pc) w Hdisj HDmst
                HDpriv Hpriv with "Hcert Hrw Hro Hcmr"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite autocast_id mcer_ret.
    iApply ("Hcont" $! (@FetchBytes_Success 4 w)). by iFrame.
  Qed.

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

  (* THE COMPOSITION: [fetch] with [fetch_bytes] filled in, leaving only
     [checked_mem_read] -- where [pmpCheck] and the memory event live -- as
     the obligation. *)
  Lemma swp_fetch_M (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pc : SailStdpp.Values.mword 64)
      (w : SailStdpp.Values.mword 32) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup cur_privilege rs = Machine ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Machine
              (Physaddr pc) 4 false false false false)
         (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                    hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_Base w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpc HDmst HDpriv Hpc Hpriv Hb0 Hb1 Hal Hrvc.
    iIntros "#Hcert Hrw Hro Hcmr".
    iApply (swp_fetch Drw Dro Df rs pc w Hdisj HDpc Hpc Hb0 Hb1 Hal Hrvc
              with "Hcert Hrw Hro [Hcmr]").
    iIntros "Hrw Hro".
    iApply (swp_fetch_bytes_M Drw Dro Df rs pc w Hdisj HDmst HDpriv Hpriv
              with "Hcert Hrw Hro Hcmr").
  Qed.

End fetch.
