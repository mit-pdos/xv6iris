(* ====================================================================== *)
(* WpSconfSfence.v -- SFENCE.VMA x0,x0 at Supervisor, per node.           *)
(*                                                                        *)
(* kvminithart is the only caller and it issues the instruction three      *)
(* times (+0x08 under Bare, +0x1c and +0x20 around the satp write).  Under *)
(* whole-cycle stepping ProofKvminithart ran those three as RAW steps --   *)
(* [wp_next_off_intro] then [reg_update] / [reg_valid] against the state   *)
(* interpretation by hand -- which per node there is no callback for.      *)
(* This is the converted leaf, and it is the last S-mode one.              *)
(*                                                                        *)
(* WHY IT IS NOT A NODE WALK.  Every other converted S-mode leaf is an     *)
(* [swp_execute_*] composer that follows the model's binds node by node    *)
(* ([WpSmodePtEngine.swp_execute_SRET_S] is the big one).  SFENCE.VMA      *)
(* cannot be: its [flush_TLB] is a SIXTY-FOUR ITERATION loop whose body    *)
(* reads [tlb], tests a slot whose contents are symbolic at a leaf, and    *)
(* conditionally writes [tlb] back.  So this leaf takes the other route    *)
(* the tree provides for exactly this shape --                             *)
(*                                                                        *)
(*    [HartMemRun.swp_hmrun_of_exec] at [mm := ∅], THE REGISTER-WRITING    *)
(*    ANALOGUE OF [hval_of_goodb] (HartMemRun's own header says so),       *)
(*                                                                        *)
(* which turns ONE [exec] fact plus ONE [goodmb] certificate into the      *)
(* whole [swp].  The [exec] fact already existed                           *)
(* ([UserretDefs.exec_execute_SFENCE_VMA_S]); the certificate is section 1 *)
(* below, and it is the same induction as [exec_flush_TLB_all]'s -- goodmb *)
(* recurses on the continuation applied to what the state holds, so the    *)
(* two walks have the same shape and the exec facts drive the goodmb one.  *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import RegFile.
Require Import InstrBytes WpGpr.
Require Import WpDecodeBridge.
Require Import HartSwp HartLift HartSpan HartSpanChar HartRegNode HartMemRun
        HartMemAsm.
Require Import UserretDefs.
Require Import SmodeCore HartTp WpNext KernelText.
Require Import IntrDefs WpIntrInv WpSmodeIntr.
(* the KPT arm's residue, for the second leaf below: [tlb_res_pt_open] /
   [_intro] (KptShare), [tlb_ok_pt_empty] (PtTree), [tlb_hash_range]
   (SmodePte).  [WpIntrInv] already requires all three, so no edge moves. *)
Require Import KptShare PtTree SmodePte.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(* 1. THE FOOTPRINT CERTIFICATE FOR THE FLUSH.                            *)
(* ====================================================================== *)

(* the certificate for the flush itself lives beside its exec fact, in
   [UserretDefs.flush_TLB_all_cert] / [execute_SFENCE_VMA_S_cert] -- one
   induction and one set of peels, not two. *)

Section SfenceFrames.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ==================================================================== *)
  (* 1. THE FRAME.  SFENCE.VMA x0,x0 reads cur_privilege and mstatus and   *)
  (* reads/writes tlb; nothing else.  [WpMmodeCsrSwp]'s [cw_*] family      *)
  (* cannot serve -- its read-only set is misa/mseccfg/cur_privilege and   *)
  (* has no mstatus -- so this is the same shape at this leaf's three      *)
  (* cells.                                                               *)
  (* ==================================================================== *)
  Definition sf_Drw : gset register := {[ (tlb : register) ]}.
  Definition sf_Dro : gset register :=
    {[ (cur_privilege : register); (mstatus : register) ]}.
  Definition sf_Df : register -> dfrac := fun _ => DfracOwn 1.
  Definition sf_Dr : register -> bool :=
    fun r => bool_decide (r ∈ sf_Drw ∪ sf_Dro).
  Definition sf_Dw : register -> bool := fun r => bool_decide (r ∈ sf_Drw).

  Definition sf_rs (ms : mword 64) (tv : type_of_register tlb) : regstate :=
    register_set tlb tv
      (register_set mstatus ms
         (register_set cur_privilege Supervisor init_regstate)).

  Lemma sf_disj : sf_Drw ## sf_Dro.
  Proof. rewrite /sf_Drw /sf_Dro. set_solver. Qed.

  Lemma sf_Dr_in : forall r, sf_Dr r = true -> r ∈ sf_Drw ∪ sf_Dro.
  Proof. intros r Hr. by apply bool_decide_eq_true_1 in Hr. Qed.

  Lemma sf_Dw_in : forall r, sf_Dw r = true -> r ∈ sf_Drw.
  Proof. intros r Hr. by apply bool_decide_eq_true_1 in Hr. Qed.

  Lemma sf_Dr_priv : sf_Dr (cur_privilege : register) = true.
  Proof. rewrite /sf_Dr /sf_Drw /sf_Dro. apply bool_decide_eq_true_2. set_solver. Qed.
  Lemma sf_Dr_ms : sf_Dr (mstatus : register) = true.
  Proof. rewrite /sf_Dr /sf_Drw /sf_Dro. apply bool_decide_eq_true_2. set_solver. Qed.
  Lemma sf_Dr_tlb : sf_Dr (tlb : register) = true.
  Proof. rewrite /sf_Dr /sf_Drw /sf_Dro. apply bool_decide_eq_true_2. set_solver. Qed.
  Lemma sf_Dw_tlb : sf_Dw (tlb : register) = true.
  Proof. rewrite /sf_Dw /sf_Drw. apply bool_decide_eq_true_2. set_solver. Qed.

  Lemma sf_rs_tlb (ms : mword 64) (tv : type_of_register tlb) :
    register_lookup tlb (sf_rs ms tv) = tv.
  Proof. apply register_lookup_set. Qed.

  Lemma sf_rs_ms (ms : mword 64) (tv : type_of_register tlb) :
    register_lookup mstatus (sf_rs ms tv) = ms.
  Proof.
    rewrite /sf_rs (irrelevant_register_set (R_bitvector_64 mstatus) tlb);
      [ apply register_lookup_set | vm_compute; reflexivity ].
  Qed.

  Lemma sf_rs_priv (ms : mword 64) (tv : type_of_register tlb) :
    register_lookup cur_privilege (sf_rs ms tv) = Supervisor.
  Proof.
    rewrite /sf_rs (irrelevant_register_set cur_privilege tlb);
      [| vm_compute; reflexivity ].
    rewrite (irrelevant_register_set cur_privilege (R_bitvector_64 mstatus));
      [ apply register_lookup_set | vm_compute; reflexivity ].
  Qed.

  Lemma sf_frames (ms : mword 64) (tv : type_of_register tlb) :
    (hreg_frame (sf_rs ms tv) sf_Drw ∗
     hreg_frame_ro sf_Df (sf_rs ms tv) sf_Dro : iProp Σ)
    ⊣⊢ (reg_pointsto tlb (DfracOwn 1) tv ∗
        reg_pointsto cur_privilege (DfracOwn 1) Supervisor ∗
        reg_pointsto mstatus (DfracOwn 1) ms).
  Proof.
    rewrite /hreg_frame /hreg_frame_ro /sf_Drw /sf_Dro.
    rewrite big_sepS_singleton.
    rewrite big_sepS_union; last set_solver.
    rewrite !big_sepS_singleton.
    rewrite sf_rs_tlb sf_rs_priv sf_rs_ms. rewrite /sf_Df.
    by rewrite !bi.sep_assoc.
  Qed.
  Lemma sf_frames_in (ms : mword 64) (tv : type_of_register tlb) :
    reg_pointsto tlb (DfracOwn 1) tv -∗
    reg_pointsto cur_privilege (DfracOwn 1) Supervisor -∗
    reg_pointsto mstatus (DfracOwn 1) ms -∗
    (hreg_frame (sf_rs ms tv) sf_Drw ∗
     hreg_frame_ro sf_Df (sf_rs ms tv) sf_Dro : iProp Σ).
  Proof. iIntros "H1 H2 H3". rewrite (sf_frames ms tv). iFrame. Qed.

  Lemma sf_frames_out (ms : mword 64) (tv : type_of_register tlb) :
    (hreg_frame (sf_rs ms tv) sf_Drw ∗
     hreg_frame_ro sf_Df (sf_rs ms tv) sf_Dro : iProp Σ) -∗
    (reg_pointsto tlb (DfracOwn 1) tv ∗
     reg_pointsto cur_privilege (DfracOwn 1) Supervisor ∗
     reg_pointsto mstatus (DfracOwn 1) ms).
  Proof. rewrite (sf_frames ms tv). iIntros "H". iExact "H". Qed.

  (* the flush's landing file, back in canonical form: the composer's [rs']
     only AGREES with the post state on the footprint, and the post state is
     [sf_rs] with [tlb] set twice. *)
  Lemma sf_rs_after (ms : mword 64) (tv0 tv : type_of_register tlb) :
    reg_agree_on (sf_Drw ∪ sf_Dro) (register_set tlb tv (sf_rs ms tv0))
      (sf_rs ms tv).
  Proof.
    intros r Hr. rewrite /sf_Drw /sf_Dro in Hr.
    apply elem_of_union in Hr as [Hr | Hr].
    - apply elem_of_singleton in Hr; subst r.
      rewrite register_lookup_set sf_rs_tlb. reflexivity.
    - apply elem_of_union in Hr as [Hr | Hr];
        apply elem_of_singleton in Hr; subst r.
      + rewrite (irrelevant_register_set cur_privilege tlb);
          [| vm_compute; reflexivity ].
        rewrite !sf_rs_priv. reflexivity.
      + rewrite (irrelevant_register_set (R_bitvector_64 mstatus) tlb);
          [| vm_compute; reflexivity ].
        rewrite !sf_rs_ms. reflexivity.
  Qed.
End SfenceFrames.

Section SfenceLeaf.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (kt : ktier) (p : mword 64).

  (* ==================================================================== *)
  (* 2. THE COMPOSER.  One [swp_hmrun_of_exec] at [mm := ∅] off the        *)
  (* reference state [MState rs ∅ dev0_state] -- the idiom                 *)
  (* [HartStepFull]'s waiting step uses, and the only one that can take a  *)
  (* sixty-four iteration register loop in one step.                       *)
  (* ==================================================================== *)
  (* THE FRAME-GENERIC FORM.  The certificate
     ([UserretDefs.execute_SFENCE_VMA_S_cert]) is already [Dr]/[Dw]-generic,
     so nothing about this composer is tied to [sf_*] -- and the trampoline
     tier needs it at ITS frame, whose read-only cells arrive at whatever
     fraction the step engine lends ([WpSmodePtEngine.sda_Df dq]) rather than
     at [sf_Df]'s [DfracOwn 1].  [swp_execute_SFENCE_VMA_S] is the instance;
     no statement moved. *)
  Lemma swp_execute_SFENCE_VMA_S_gen (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (tlb : register) ∈ Drw ->
    register_lookup cur_privilege rs = Supervisor ->
    eq_vec (_get_Mstatus_TVM (register_lookup mstatus rs)) ('b"1") = false ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
    swp (execute (SFENCE_VMA (zreg, zreg)))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
        ∃ (rs' : regstate) (tv : type_of_register tlb),
          ⌜reg_agree_on (Drw ∪ Dro) rs' (register_set tlb tv rs)⌝ ∗
          ⌜forall i, 0 <= i < 64 -> vec_access_dec tv i = None⌝ ∗
          hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro ∗
          resv_any cpu_id).
  Proof.
    intros Hdisj Hpriv_in Hms_in Htlb_in Hpriv HTVM.
    pose (Dr := fun r : register => bool_decide (r ∈ Drw ∪ Dro)).
    pose (Dw := fun r : register => bool_decide (r ∈ Drw)).
    assert (HDr_in : forall r, Dr r = true -> r ∈ Drw ∪ Dro)
      by (intros r Hr; by apply bool_decide_eq_true_1 in Hr).
    assert (HDw_in : forall r, Dw r = true -> r ∈ Drw)
      by (intros r Hr; by apply bool_decide_eq_true_1 in Hr).
    destruct (execute_SFENCE_VMA_S_cert Dr Dw (MState rs ∅ dev0_state)
                (bool_decide_eq_true_2 _ Hpriv_in)
                (bool_decide_eq_true_2 _ Hms_in)
                (bool_decide_eq_true_2 _ (elem_of_union_l _ _ _ Htlb_in))
                (bool_decide_eq_true_2 _ Htlb_in) Hpriv HTVM)
      as (tv & Hex & Hprop & Hgm).
    iIntros "#Hcert Hany Hrw Hro".
    (* [bytes_own ∅] is [emp], hence persistent: it lands in the □ context *)
    iAssert (bytes_own (∅ : gmap Arch.pa (bv 8))) with "[]" as "#Hemp";
      [ by rewrite /bytes_own big_sepM_empty |].
    iApply (swp_mono _ _ _ with "[] [-]"); last first.
    { iApply (swp_hmrun_of_exec Dr Dw Drw Dro Df
                (execute (SFENCE_VMA (zreg, zreg))) (MState rs ∅ dev0_state)
                _ _ rs ∅ Hdisj HDr_in HDw_in (reg_agree_refl _ _)
                (map_empty_subseteq _) (Hgm ∅) Hex
                with "Hcert Hany Hrw Hro Hemp"). }
    iIntros (v) "(-> & Hpost)".
    iDestruct "Hpost" as (rs' mm') "(%Hag & _ & _ & Hrw & Hro & _ & Hany)".
    iSplitR; [done|].
    iExists rs', tv. iFrame "Hrw Hro Hany".
    iSplitR; [| iPureIntro; exact Hprop].
    iPureIntro. exact Hag.
  Qed.

  Lemma swp_execute_SFENCE_VMA_S (rs : regstate) :
    register_lookup cur_privilege rs = Supervisor ->
    eq_vec (_get_Mstatus_TVM (register_lookup mstatus rs)) ('b"1") = false ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rs sf_Drw -∗ hreg_frame_ro sf_Df rs sf_Dro -∗
    swp (execute (SFENCE_VMA (zreg, zreg)))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
        ∃ (rs' : regstate) (tv : type_of_register tlb),
          ⌜reg_agree_on (sf_Drw ∪ sf_Dro) rs' (register_set tlb tv rs)⌝ ∗
          ⌜forall i, 0 <= i < 64 -> vec_access_dec tv i = None⌝ ∗
          hreg_frame rs' sf_Drw ∗ hreg_frame_ro sf_Df rs' sf_Dro ∗
          resv_any cpu_id).
  Proof.
    intros Hpriv HTVM.
    assert (Hp : (cur_privilege : register) ∈ sf_Drw ∪ sf_Dro)
      by (rewrite /sf_Drw /sf_Dro; set_solver).
    assert (Hm : (mstatus : register) ∈ sf_Drw ∪ sf_Dro)
      by (rewrite /sf_Drw /sf_Dro; set_solver).
    assert (Ht : (tlb : register) ∈ sf_Drw)
      by (rewrite /sf_Drw; set_solver).
    exact (swp_execute_SFENCE_VMA_S_gen sf_Drw sf_Dro sf_Df rs sf_disj
             Hp Hm Ht Hpriv HTVM).
  Qed.

  (* ==================================================================== *)
  (* 3. THE LEAF.  Statement in the shape every other converted S-mode      *)
  (* leaf has: the ambient bundle in and out, the ONE extra cell this       *)
  (* instruction touches threaded explicitly, and the flushed-ness of the   *)
  (* landing [tlb] as the only thing the caller learns.  TVM = 0 is NOT a   *)
  (* premise -- it is already one of [sconf]'s own mstatus facts.           *)
  (* ==================================================================== *)
  Lemma wp_sfence_vma_s_sconf (pc : mword 64) (m : regfile) (n : nat)
      (tv0 : type_of_register tlb) :
    sie_cap_gpr kt m n false p -∗
    tlb ↦ᵣ tv0 -∗
    pc_is pc -∗
    instr pc false (SFENCE_VMA (zreg, zreg)) -∗
    wp_next false p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n false p -∗
      (∃ tv : type_of_register tlb,
         ⌜forall i, 0 <= i < 64 -> vec_access_dec tv i = None⌝ ∗ tlb ↦ᵣ tv) -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Htlb Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n false false pc false
              (SFENCE_VMA (zreg, zreg))
              (fun (_ : CpuId) npc ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗ ⌜m' = m⌝ ∗ ⌜n' = n⌝ ∗
                 ∃ tv : type_of_register tlb,
                   ⌜forall i, 0 <= i < 64 -> vec_access_dec tv i = None⌝ ∗
                   tlb ↦ᵣ tv)%I
              with "Hcg Hpc Hinstr [Htlb Hcont]").
    iNext. iApply wp_next_off_intro. rewrite /sconf_step_obl.
    iSplitL "Htlb".
    - iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct (sconf_to_cells with "Hsc") as (ms0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
          Hmdl & Hmenv)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD &
                          HMPP & HTVM).
      iDestruct (sf_frames_in ms0 tv0 with "Htlb Hpriv Hms") as "[Hrw Hro]".
      iApply (swp_mono with "[Hcap Hfile HPC HnPC Hhalf Hspp Hmie Hmdl Hmenv] [Hrw Hro Hresv]");
        last first.
      { iApply (swp_execute_SFENCE_VMA_S (sf_rs ms0 tv0)
                  (sf_rs_priv ms0 tv0)
                  ltac:(rewrite sf_rs_ms; exact HTVM)
                  with "Hcert Hresv Hrw Hro"). }
      iIntros (e) "(-> & Hpost)".
      iDestruct "Hpost" as (rs' tv) "(%Hag & %Hflush & Hrw & Hro & Hresv)".
      iDestruct (hreg_frame_ext rs' (sf_rs ms0 tv) sf_Drw with "Hrw") as "Hrw";
        [ intros r Hr; rewrite (Hag r ltac:(set_solver));
          exact (sf_rs_after ms0 tv0 tv r ltac:(set_solver)) |].
      iDestruct (hreg_frame_ro_ext sf_Df rs' (sf_rs ms0 tv) sf_Dro with "Hro")
        as "Hro";
        [ intros r Hr; rewrite (Hag r ltac:(set_solver));
          exact (sf_rs_after ms0 tv0 tv r ltac:(set_solver)) |].
      iDestruct (sf_frames_out ms0 tv with "[$Hrw $Hro]") as "(Htlb & Hpriv & Hms)".
      iSplitR; [done|].
      iExists (add_vec_int pc 4), ms0, m, n.
      iFrame "HPC HnPC Hresv".
      iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
      { rewrite /sconf_at_priv. iExists mdv0.
        iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
        iPureIntro. split; [exact Hmsf | exact Hmm]. }
      iFrame "Hcap Hfile".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iExists tv. iSplitR; [iPureIntro; exact Hflush |]. iExact "Htlb".
    - iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & -> & Htlb)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      (* [wp_next]'s continuation leads with its own hart-identity premise *)
      iApply ("Hcont" $! cpu_id with "[%] Hcg' Htlb Hpc'"). done.
  Qed.

  (* THE LEAF INTERFACE IS CELLS, and deliberately so: the wrapper-shape
     convention (worklist "THE S-MODE WRAPPER SHAPES") is that a leaf
     receives the cells it may touch and returns them rewritten.  An earlier
     draft of this file also carried two arm-specific variants that borrowed
     the cell out of [sie_cap]'s translation slot and re-sealed it inside the
     step.  They are GONE, and the reason is worth keeping: [strans_inv]'s
     Bare arm is [bare_inv], which is EXISTENTIAL in the tlb value, so
     re-sealing there discards the flush -- and kvminithart's [csrw satp]
     consumes exactly that flush six instructions later
     ([tlb_res_pt_intro ... (tlb_ok_pt_empty ... Hnone1)]).  The cell stays
     in the caller's hand across the window for that reason. *)

  (* ==================================================================== *)
  (* 4. THE SAME INSTRUCTION AT THE KERNEL TABLE.                          *)
  (*                                                                      *)
  (* The leaf above threads the cell because kvminithart's FIRST sfence     *)
  (* has to remember its flush six instructions later.  Its SECOND does     *)
  (* not: by then the switch has re-sealed the translation slot at the KPT  *)
  (* arm, [KptShare.tlb_res_pt] owns the cell, and nothing downstream reads *)
  (* the flush -- so this variant BORROWS the cell out of the arm the       *)
  (* receipt pins, re-seals it at the flushed vector, and exposes nothing.  *)
  (* It is not the deleted Bare variant in disguise: the objection there    *)
  (* was that [bare_inv] is existential in the tlb value, and the KPT arm   *)
  (* is not -- [tlb_res_pt] carries the coherence, and [tlb_ok_pt_empty]    *)
  (* re-establishes it at the residue's OWN snapshot, so no invariant is    *)
  (* opened in the step.  Same borrow shape as                              *)
  (* [WpSconfCsr.wp_csrr_satp_kpt_s_sconf]; the receipt is free at the one  *)
  (* call site, being exactly what the switch produced.                     *)
  (* ==================================================================== *)
  Lemma wp_sfence_vma_kpt_s_sconf (pc : mword 64) (m : regfile) (n : nat) :
    sie_cap_gpr kt m n false p -∗
    kpt_on cpu_id -∗
    pc_is pc -∗
    instr pc false (SFENCE_VMA (zreg, zreg)) -∗
    wp_next false p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n false p -∗
      kpt_on cpu_id -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg #Hkptr Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n false false pc false
              (SFENCE_VMA (zreg, zreg))
              (fun (_ : CpuId) npc ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗ ⌜m' = m⌝ ∗ ⌜n' = n⌝)%I
              with "Hcg Hpc Hinstr [Hcont]").
    iNext. iApply wp_next_off_intro. rewrite /sconf_step_obl.
    iSplitR "Hcont".
    - iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      iDestruct (strans_inv_acc_kpt with "Hkptr Htr")
        as (root) "(Hres & Htrback)".
      iDestruct (tlb_res_pt_open with "Hres") as (ksatp tlbv)
        "(Hsatp & %HkMode & %Hkasid & %Hkppn & Htlbc & Hsnap & Hpmp & #Hkinv)".
      iDestruct "Hsnap" as (kt3) "(_ & #Hlb3)".
      iDestruct (sconf_to_cells with "Hsc") as (ms0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
          Hmdl & Hmenv)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD &
                          HMPP & HTVM).
      iDestruct (sf_frames_in ms0 tlbv with "Htlbc Hpriv Hms") as "[Hrw Hro]".
      iApply (swp_mono with
                "[Hstk Harm Hfile HPC HnPC Hhalf Hspp Hmie Hmdl Hmenv
                  Hsatp Hpmp Htrback] [Hrw Hro Hresv]");
        last first.
      { iApply (swp_execute_SFENCE_VMA_S (sf_rs ms0 tlbv)
                  (sf_rs_priv ms0 tlbv)
                  ltac:(rewrite sf_rs_ms; exact HTVM)
                  with "Hcert Hresv Hrw Hro"). }
      iIntros (e) "(-> & Hpost)".
      iDestruct "Hpost" as (rs' tv) "(%Hag & %Hflush & Hrw & Hro & Hresv)".
      iDestruct (hreg_frame_ext rs' (sf_rs ms0 tv) sf_Drw with "Hrw") as "Hrw";
        [ intros r Hr; rewrite (Hag r ltac:(set_solver));
          exact (sf_rs_after ms0 tlbv tv r ltac:(set_solver)) |].
      iDestruct (hreg_frame_ro_ext sf_Df rs' (sf_rs ms0 tv) sf_Dro with "Hro")
        as "Hro";
        [ intros r Hr; rewrite (Hag r ltac:(set_solver));
          exact (sf_rs_after ms0 tlbv tv r ltac:(set_solver)) |].
      iDestruct (sf_frames_out ms0 tv with "[$Hrw $Hro]")
        as "(Htlbc & Hpriv & Hms)".
      (* re-seal the arm at the flushed vector, at the residue's OWN
         snapshot -- an empty TLB is coherent with any tree. *)
      iDestruct (tlb_res_pt_intro root ksatp tv kt3 HkMode Hkasid Hkppn
                   (tlb_ok_pt_empty (mword_of_int 0) kt3 tv
                      (fun vpn' => Hflush _ (tlb_hash_range vpn')))
                   with "Hsatp Htlbc Hlb3 Hpmp Hkinv") as "Hres".
      iDestruct ("Htrback" with "Hres") as "Htr".
      iSplitR; [done|].
      iExists (add_vec_int pc 4), ms0, m, n.
      iFrame "HPC HnPC Hresv".
      iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
      { rewrite /sconf_at_priv. iExists mdv0.
        iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
        iPureIntro. split; [exact Hmsf | exact Hmm]. }
      iSplitL "Hstk Htr Harm". { iFrame "Hstk Htr Harm Hwit". }
      iFrame "Hfile". iSplitR; [done|]. iSplitR; [done|]. done.
    - iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & ->)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! cpu_id with "[%] Hcg' Hkptr Hpc'"). done.
  Qed.

End SfenceLeaf.
