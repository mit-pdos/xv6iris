From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpGpr.
Require Import MinstretInv InstrBytes.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* register-generic ADDI execute: reads rs1 + immediate, writes rd, via the
   file-generic rX/wX lemmas -- works for ANY rd/rs1. *)
Definition gpr_addi_val (rs1 : mword 5) (imm : mword 12) (s : mstate) : mword 64 :=
  add_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
          (sign_extend' 64 imm).

Lemma exec_execute_ITYPE_ADDI_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_addi_val rs1 imm s))).
Proof.
  unfold gpr_addi_val.
  eapply exec_execute_ITYPE_ADDI.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

Lemma gpr_addi_val_lookup (rs1 : mword 5) (imm : mword 12) (t : mstate) :
  uint rs1 <> 0 ->
  gpr_addi_val rs1 imm t
  = add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) t.(sregs))
            (sign_extend' 64 imm).
Proof.
  intros H1. unfold gpr_addi_val.
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  reflexivity.
Qed.

(* ADDIW: sign-extend the low 32 bits of (rs1 + imm).  An add-immediate variant,
   so it lives here rather than in WpGprShift.  Value inlined (like gpr_addi_val),
   so no dependency on WpGprShift's gpr_src. *)
Lemma exec_execute_ADDIW_base (imm : mword 12) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (sign_extend' 64 (subrange_vec_dec (add_vec a (sign_extend' 64 imm)) 31 0))) s
    = Some (tt, s') ->
  exec (execute (ADDIW (imm, rs1, rd))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (ADDIW (imm, rs1, rd))) with (execute_ADDIW imm rs1 rd).
  unfold execute_ADDIW. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ Ha).
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

Definition gpr_addiw_val (rs1 : mword 5) (imm : mword 12) (s : mstate) : mword 64 :=
  sign_extend' 64 (subrange_vec_dec
    (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
             (sign_extend' 64 imm)) 31 0).

Lemma exec_execute_ADDIW_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec (execute (ADDIW (imm, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_addiw_val rs1 imm s))).
Proof.
  unfold gpr_addiw_val.
  eapply exec_execute_ADDIW_base.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

(* exec-level register-generic ADDI step (32-bit, F_Base): one lemma, ANY rd/rs1. *)
Section ForwardAddiGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 rd : mword 5) (imm : mword 12).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, ADDI), s0).

  Definition sAi : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pci : mstate := set_reg sAi nextPC (add_vec_int pc 4).
  Definition sXi : mstate :=
    set_reg s_pci (R_bitvector_64 (gpr_of_Z (uint rd)))
      (regval_into_reg (gpr_addi_val rs1 imm s_pci)).
  Definition sTi : mstate := set_reg sXi PC (register_lookup nextPC sXi.(sregs)).
  Definition sFi : mstate :=
    if b then set_reg sTi minstret (add_vec_int (register_lookup minstret sTi.(sregs)) 1)
         else sTi.

End ForwardAddiGpr.


Section CleanAddiGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 rd : mword 5) (imm : mword 12) (mst0 : mword 64).
  Definition base_upd_i : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b)
                  nextPC (add_vec_int pc 4))
         (R_bitvector_64 (gpr_of_Z (uint rd)))
         (regval_into_reg (gpr_addi_val rs1 imm (s_pci s pc b))))
      PC (add_vec_int pc 4).
  Definition sFci : mstate :=
    if b then set_reg base_upd_i minstret (add_vec_int mst0 1) else base_upd_i.

End CleanAddiGpr.

(* ====================================================================== *)
(* The register-GENERIC addi WP: ONE lemma for `addi rd,rs1,imm`, ANY      *)
(* rd/rs1, with all GPRs held as the single [gpr_file] resource.           *)
(* ====================================================================== *)
Section WpAddiGpr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
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
  Lemma wp_addi_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5)
      (imm : mword 12) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
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
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr E Φ pc is_rvc (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) pmpcfg0
              HN Hpmp with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    (* completeness gives the (total) lookups for rs1 and rd *)
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    (* tick nextPC first, so we read rs1 against the execute state *)
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* read the rs1 entry (x0 or a real register) -> the ADDI value *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Hav : gpr_addi_val rs1 imm (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                  = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { unfold gpr_addi_val. rewrite Hrv. reflexivity. }
    (* write rd (rd <> 0, so its entry is the real register points-to) *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_ITYPE_ADDI_gpr rs1 rd imm (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hav. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    (* continuation: PC/nextPC are both pc+4; hand back mmode_config, pmpcfg,
       the reassembled [pc_is (pc+4)], and the updated file *)
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec (m !!! Regidx rs1)
                   (sign_extend' 64 imm)))).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.
End WpAddiGpr.

(* ADDIW WP -- moved here from WpGprShift (add-immediate variant). *)
Section WpAddiwGpr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Lemma wp_addiw_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5) (immv : mword 12)
      (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
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
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr E Φ pc is_rvc (ADDIW (immv, Regidx rs1, Regidx rd)) pmpcfg0
              HN Hpmp with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Hav : gpr_addiw_val rs1 immv (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                  = sign_extend' 64
                      (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)).
    { unfold gpr_addiw_val. rewrite Hrv. reflexivity. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (sign_extend' 64
               (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (sign_extend' 64
               (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (sign_extend' 64
                  (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_ADDIW_gpr rs1 rd immv (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hav. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (sign_extend' 64
                   (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)))).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold set_reg; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  Definition wp_sextw_x15_x15 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) :=
    wp_addiw_gpr E Φ pc false (mword_of_int 15) (mword_of_int 15) (mword_of_int 0).
  Definition wp_addiw_x5_x6 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (imm : mword 12) :=
    wp_addiw_gpr E Φ pc false (mword_of_int 6) (mword_of_int 5) imm.
End WpAddiwGpr.

(* Demonstration: ONE lemma [wp_addi_gpr] serves many (rd,rs1) pairs. *)
Section WpAddiGprDemo.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.
  Definition wp_addi_x5_x6 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (imm : mword 12) :=
    wp_addi_gpr E Φ pc false (mword_of_int 6) (mword_of_int 5) imm.   (* addi x5, x6, imm *)
  Definition wp_addi_x28_x1 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (imm : mword 12) :=
    wp_addi_gpr E Φ pc false (mword_of_int 1) (mword_of_int 28) imm.  (* addi x28, x1, imm *)
  Goal gpr_of_Z (uint (mword_of_int 6 : mword 5)) = x6
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 1 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpAddiGprDemo.
