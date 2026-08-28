From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec ExecCommon WpGpr.
Require Import RegFile.
Require Import InstrBytes.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
Local Open Scope Z_scope.
Require Import WpGprCsrrCommon.
Require Import WpMmodeCsrSwp.   (* swp_execute_CSRReg_csrr + the cr_* footprint *)
Require Import HartSwp HartSpan HartSpanChar WpDecodeBridge.

(* [read_CSR csr_csrr] IS the mhartid read -- the whole 4096-way dispatch
   collapses by conversion at a literal CSR number, which is why
   [ExecCommon.exec_read_CSR_csrr] is one [exact].  So the walker takes it
   with one node of fuel and no pruning tactic at all. *)
Lemma hfrun_read_CSR_csrr (D Drw : gset register) (rs : regstate) :
  (R_bitvector_64 mhartid : register) ∈ D ->
  hfrun 2 D Drw rs (read_CSR csr_csrr)
  = Some (register_lookup (R_bitvector_64 mhartid) rs, rs).
Proof.
  intros HD.
  change (read_CSR csr_csrr)
    with (Defs.read_reg (R_bitvector_64 mhartid) : M (mword 64)).
  cbn beta iota zeta delta [Defs.read_reg].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD). apply hfrun_ret.
Qed.

(* ====================================================================== *)
(* Register-generic CSR-read execute: csrr rd, mhartid (= csrrs rd,mhartid,x0).*)
(* The CSR read (mhartid) and the x0 source stay fixed; only the           *)
(* destination [rd] is generalized.  CSRRS with a zero source always yields  *)
(* access type CSRRead, independent of rd.                                   *)
(* ====================================================================== *)
Lemma exec_execute_CSRReg_gpr_aux (rd : mword 5) s s_w :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (wX_bits (Regidx rd) (register_lookup mhartid s.(sregs))) s = Some (tt, s_w) ->
  exec (execute_CSRReg csr_csrr zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS, s_w).
Proof.
  intros Hpriv Hwx.
  unfold execute_CSRReg.
  replace (csr_access_type CSRRS (generic_eq (Regidx rd) zreg)
             (generic_eq zreg zreg)) with CSRRead
    by (replace (generic_eq zreg zreg) with true by (vm_compute; reflexivity);
        symmetry; apply csr_access_type_CSRRS_true).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_x0 (zero_extend' 5 ('b"00")) s ltac:(vm_compute; reflexivity))).
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_result_csrr s)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  replace (not (ext_check_CSR csr_csrr Machine CSRRead)) with false
    by (vm_compute; reflexivity).
  replace (if generic_neq CSRRead CSRWrite then read_CSR csr_csrr else returnM (zeros' 64))
    with (read_CSR csr_csrr) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_csrr s)).
  match goal with |- exec (Defs.bind ?D ?K) s = _ =>
    replace D with (returnM (register_lookup mhartid s.(sregs)) : M (mword 64))
      by (vm_compute; reflexivity) end.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (register_lookup mhartid s.(sregs)) s)).
  replace (generic_eq CSRRead CSRRead) with true by reflexivity.
  rewrite (exec_bind0_Some _ _ _ _ _ (_ :
    exec (Defs.bind0 (csr_id_read_callback csr_csrr (register_lookup mhartid s.(sregs)))
            (wX_bits (Regidx rd) (register_lookup mhartid s.(sregs)))) s
      = Some (tt, s_w))).
  2:{ rewrite (exec_bind0_Some _ _ _ _ _
        (exec_csr_id_read_callback_csrr s (register_lookup mhartid s.(sregs)))).
      exact Hwx. }
  apply exec_returnM.
Qed.

Lemma exec_execute_CSRReg_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_csrr zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (register_lookup mhartid s.(sregs)))).
Proof.
  intros Hrd Hpriv.
  apply (exec_execute_CSRReg_gpr_aux rd s
           (set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (register_lookup mhartid s.(sregs)))) Hpriv).
  rewrite (exec_wX_bits_gpr rd (register_lookup mhartid s.(sregs)) s).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  reflexivity.
Qed.

(* mhartid is untouched by [set_reg _ nextPC _], so its value carries into the
   execute state unchanged. *)
Lemma mhartid_set_nextPC (s : mstate) (v : mword 64) :
  register_lookup mhartid (set_reg s nextPC v).(sregs)
  = register_lookup mhartid s.(sregs).
Proof.
  rewrite ?sregs_set_reg.
  rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ].
Qed.

(* ===== mstatus (0x300): machine CSR, accessible (vm), read = subrange ===== *)
Definition csr_mstatus : mword 12 := Ox"300".
Definition mstatus_rdval (s : mstate) : mword 64 :=
  subrange_vec_dec (register_lookup mstatus s.(sregs)) (Z.sub xlen 1) 0.

Lemma exec_read_CSR_mstatus s :
  exec (read_CSR csr_mstatus) s = Some (mstatus_rdval s, s).
Proof.
  unfold read_CSR, csr_mstatus, mstatus_rdval.
  replace (eq_vec (Ox"300" : mword 12) (Ox"301")) with false by (vm_compute; reflexivity).
  cbn match.
  replace (andb (Z.eqb xlen 64) (eq_vec (Ox"300" : mword 12) (Ox"300"))) with true
    by (vm_compute; reflexivity).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  apply exec_returnM.
Qed.

(* the walker's twin of [exec_read_CSR_mstatus]: the same two guard
   collapses, done at the TERM so both interpreters can use it.  Concluding at
   the RAW register value rather than the subrange (they are equal by
   [subrange64_id]) is what keeps the leaf statement free of the projection. *)
Lemma read_CSR_mstatus_red :
  read_CSR csr_mstatus
  = (Defs.bind (Defs.read_reg mstatus)
       (fun v : mword 64 => returnM (subrange_vec_dec v (Z.sub xlen 1) 0))
     : M (mword 64)).
Proof.
  unfold read_CSR, csr_mstatus.
  replace (eq_vec (Ox"300" : mword 12) (Ox"301")) with false
    by (vm_compute; reflexivity).
  cbn match.
  replace (andb (Z.eqb xlen 64) (eq_vec (Ox"300" : mword 12) (Ox"300")))
    with true by (vm_compute; reflexivity).
  cbn match. reflexivity.
Qed.

Lemma hfrun_read_CSR_mstatus (D Drw : gset register) (rs : regstate) :
  (R_bitvector_64 mstatus : register) ∈ D ->
  hfrun 3 D Drw rs (read_CSR csr_mstatus)
  = Some (register_lookup (R_bitvector_64 mstatus) rs, rs).
Proof.
  intros HD. rewrite read_CSR_mstatus_red.
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  cbn beta iota zeta delta [Defs.returnm returnM].
  rewrite hfrun_ret subrange64_id. reflexivity.
Qed.

Lemma exec_check_CSR_result_mstatus s :
  exec (check_CSR_result csr_mstatus Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  unfold check_CSR_result, csr_mstatus.
  assert (H : check_CSR (Ox"300") Machine CSRRead = returnM true) by (vm_compute; reflexivity).
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (check_CSR (Ox"300") Machine CSRRead) s = Some (true, s))).
  2:{ rewrite H. apply exec_returnm. }
  apply (exec_returnM (CSR_Check_OK tt) s).
Qed.

Lemma exec_csr_id_read_callback_mstatus s d :
  exec (csr_id_read_callback csr_mstatus d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_mstatus d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_mstatus_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_mstatus zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (mstatus_rdval s))).
Proof.
  intros Hrd Hpriv.
  apply (csrr_read_step csr_mstatus rd (mstatus_rdval s) s _ Hpriv).
  - apply exec_check_CSR_result_mstatus.
  - vm_compute; reflexivity.
  - apply exec_read_CSR_mstatus.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_mstatus.
  - rewrite (exec_wX_bits_gpr rd (mstatus_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

Lemma exec_read_CSR_mcounteren s :
  exec (read_CSR (Ox"306")) s
    = Some (zero_extend' 64 (register_lookup mcounteren s.(sregs)), s).
Proof. drive_csr. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren s)). apply exec_returnM. Qed.

Lemma read_CSR_mcounteren_red :
  read_CSR (Ox"306")
  = (Defs.bind (Defs.read_reg mcounteren)
       (fun v : mword 32 => returnM (zero_extend' 64 v)) : M (mword 64)).
Proof. drive_csr_term. reflexivity. Qed.

Lemma hfrun_read_CSR_mcounteren (D Drw : gset register) (rs : regstate) :
  (R_bitvector_32 mcounteren : register) ∈ D ->
  hfrun 3 D Drw rs (read_CSR (Ox"306"))
  = Some (zero_extend' 64 (register_lookup (R_bitvector_32 mcounteren) rs), rs).
Proof.
  intros HD. rewrite read_CSR_mcounteren_red.
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  cbn beta iota zeta delta [Defs.returnm returnM].
  apply hfrun_ret.
Qed.

(* ===== mcounteren (0x306): Ext_U-gated, read = zero_extend' 64 mcounteren ===== *)
Definition csr_mcounteren : mword 12 := Ox"306".
Definition mcounteren_rdval (s : mstate) : mword 64 :=
  zero_extend' 64 (register_lookup mcounteren s.(sregs)).

Lemma exec_check_CSR_result_mcounteren s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_mcounteren Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HU. apply exec_check_CSR_result_read. apply exec_check_CSR_read.
  - assert (H : check_CSR_priv csr_mcounteren Machine = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - assert (Hacceq : is_CSR_accessible csr_mcounteren Machine CSRRead = currentlyEnabled Ext_U)
      by csr_dispatch_eq.
    rewrite Hacceq. apply (exec_currentlyEnabled_U s HU).
  - assert (H : stateen_allows_CSR_access csr_mcounteren Machine CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_csr_id_read_callback_mcounteren s d :
  exec (csr_id_read_callback csr_mcounteren d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_mcounteren d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_mcounteren_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_mcounteren zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (mcounteren_rdval s))).
Proof.
  intros Hrd Hpriv HU.
  apply (csrr_read_step csr_mcounteren rd (mcounteren_rdval s) s _ Hpriv).
  - apply (exec_check_CSR_result_mcounteren s HU).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_mcounteren.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_mcounteren.
  - rewrite (exec_wX_bits_gpr rd (mcounteren_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

Lemma mstatus_rdval_set_nextPC (s : mstate) (v : mword 64) :
  mstatus_rdval (set_reg s nextPC v) = mstatus_rdval s.
Proof. unfold mstatus_rdval; rewrite ?sregs_set_reg.
  rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ]. Qed.
Lemma mcounteren_rdval_set_nextPC (s : mstate) (v : mword 64) :
  mcounteren_rdval (set_reg s nextPC v) = mcounteren_rdval s.
Proof. unfold mcounteren_rdval; rewrite ?sregs_set_reg.
  rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ]. Qed.

(* ====================================================================== *)
(* The register-GENERIC csrr WP for [csrr rd, mhartid], stated on the new    *)
(* [instr] / [mmode_config] / [gpr_file] layer (cf. [wp_auipc_gpr]).  Like    *)
(* AUIPC, csrr-mhartid has no GPR source: it writes rd := mhartid.  The value  *)
(* of mhartid is threaded through as its own register points-to premise         *)
(* [mhartid ↦ᵣ mhartid_in] (mhartid is not part of [mmode_config]); it is read  *)
(* and returned unchanged.  Built on [wp_instr]; reuses the representation-      *)
(* independent execute helper [exec_execute_CSRReg_gpr].                        *)
(* ====================================================================== *)
Section WpCsrrMhartidGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_csrr_mhartid_gpr (pc : mword 64) (rd : mword 5)
      (mhartid_in : mword 64) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mhartid ↦ᵣ mhartid_in -∗
    instr pc false (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg mhartid_in]> m) -∗
      mhartid ↦ᵣ mhartid_in -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc Hpc Hfmap Hmh Hinstr Hcont".
    assert (Hfresh : cw_fresh (R_bitvector_64 mhartid))
      by (rewrite /cw_fresh; split_and!; vm_compute; reflexivity).
    assert (Hchk : exec (check_CSR_result csr_csrr Machine CSRRead) dstateM
                   = Some (CSR_Check_OK tt, dstateM))
      by (vm_compute; reflexivity).
    (* keep half of [mmode_config]: the CSR legality check reads
       cur_privilege, and the wrapper has the other half *)
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & %Hmisaval & %Hsecval & _)".
    subst misa0 mseccfg0.
    iApply (wp_instr pc (add_vec_int pc 4) false
              (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS)) m
              (<[Regidx rd := regval_into_reg mhartid_in]> m) pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               mhartid ↦ᵣ mhartid_in)%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hfmap Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k Hmh] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iDestruct (cr_frames_in (DfracOwn (q/2)) (DfracOwn 1)
                   (R_bitvector_64 mhartid) mhartid_in Hfresh
                   with "Hmh Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hmst_k Hpmpc_k] [Hf Hrw Hro]");
        [| iApply (swp_execute_CSRReg_csrr ∅ (cr_Dro (R_bitvector_64 mhartid))
                     (cr_Df (DfracOwn (q/2)) (DfracOwn 1)
                        (R_bitvector_64 mhartid))
                     (cw_rs (R_bitvector_64 mhartid) mhartid_in) m
                     csr_csrr rd mhartid_in
                     (cr_disj (R_bitvector_64 mhartid))
                     (cr_in_priv (R_bitvector_64 mhartid))
                     (cw_rs_priv (R_bitvector_64 mhartid) mhartid_in Hfresh)
                     Hrd
                     ltac:(vm_compute; reflexivity)
                     (hval_check_CSR_result _ ∅ _ csr_csrr CSRRead
                        (cr_in_priv (R_bitvector_64 mhartid)) (cr_in_sec (R_bitvector_64 mhartid))
                        (cr_in_misa (R_bitvector_64 mhartid))
                        (cw_rs_priv (R_bitvector_64 mhartid) mhartid_in Hfresh)
                        (cw_rs_sec (R_bitvector_64 mhartid) mhartid_in Hfresh)
                        (cw_rs_misa (R_bitvector_64 mhartid) mhartid_in Hfresh)
                        ltac:(vm_compute; reflexivity) Hchk)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     ltac:(intros ?; vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro [Hcert]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (cr_frames_out (DfracOwn (q/2)) (DfracOwn 1)
                     (R_bitvector_64 mhartid) mhartid_in Hfresh with "Hro")
          as "(Hmh & Hpriv_k & _ & _)".
        iSplitR; [done|]. iFrame "Hf HPC HnPC".
        iSplitL "Hhs_k Hpriv_k Hmst_k".
        { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
        iFrame "Hpmpc_k Hmh".
      + (* the CSR read: [read_CSR csr_csrr] IS the mhartid read *)
        iIntros "Hrw Hro".
        iApply (swp_mono with "[] [-]");
          [| iApply (swp_hfrun 2 ∅ (cr_Dro (R_bitvector_64 mhartid))
                       (cr_Df (DfracOwn (q/2)) (DfracOwn 1)
                          (R_bitvector_64 mhartid))
                       (cw_rs (R_bitvector_64 mhartid) mhartid_in) _ _ _
                       (cr_disj (R_bitvector_64 mhartid))
                       (hfrun_read_CSR_csrr
                          (∅ ∪ cr_Dro (R_bitvector_64 mhartid)) ∅
                          (cw_rs (R_bitvector_64 mhartid) mhartid_in)
                          (cr_in_r (R_bitvector_64 mhartid)))
                       with "Hcert Hrw Hro") ].
        iIntros (x) "(-> & Hrw & Hro)".
        rewrite (cw_rs_r (R_bitvector_64 mhartid) mhartid_in).
        iSplitR; [done|]. iFrame.
    - iApply bi.later_intro. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hmh')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hmh'").
  Qed.
End WpCsrrMhartidGpr.
(* ====================================================================== *)
(* Register-generic csrr WPs for arbitrary readable CSRs (mstatus /          *)
(* mcounteren / menvcfg / sie / time), stated on the new                     *)
(* [instr] / [mmode_config] / [gpr_file] layer -- ported from the old        *)
(* WpGprCsrrAny.v.  Each is [csrr rd, csr] (= csrrs rd,csr,x0): no GPR        *)
(* source, writes rd := (CSR read value).  The read CSR cell(s) are threaded  *)
(* as extra register points-to premises (returned unchanged); cur_privilege   *)
(* = Machine (and, for the U/S-gated CSRs, the misa.U/misa.S bit) is          *)
(* recovered at the execute state from the [mmode_config] / [hw_config]        *)
(* split, exactly as in [wp_csrr_mhartid_gpr].  Built on [wp_instr]; each      *)
(* reuses the representation-independent [exec_execute_csrr_<csr>_gpr] helper. *)
(* ====================================================================== *)
Section WpCsrrGprA.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* mstatus (0x300): machine CSR, no extra gate. *)
  (* [dqm]-generic mstatus cell: mstatus lives INSIDE [mmode_config], so a
     chain can only ever hand this WP a FRACTION of the cell (the half it
     kept outside its working bundle to pin the value).  Only the value is
     read, so any fraction works. *)
  Lemma wp_csrr_mstatus_gpr (pc : mword 64) (rd : mword 5)
      (mstatus_in : mword 64) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) {dqm : dfrac} :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mstatus ↦ᵣ{dqm} mstatus_in -∗
    instr pc false (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg (mstatus_in)]> m) -∗
      mstatus ↦ᵣ{dqm} mstatus_in -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc Hpc Hfmap Hcsr Hinstr Hcont".
    assert (Hfresh : cw_fresh (R_bitvector_64 mstatus))
      by (rewrite /cw_fresh; split_and!; vm_compute; reflexivity).
    assert (Hchk : exec (check_CSR_result csr_mstatus Machine CSRRead) dstateM
                   = Some (CSR_Check_OK tt, dstateM))
      by (vm_compute; reflexivity).
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & %Hmisaval & %Hsecval & _)".
    subst misa0 mseccfg0.
    iApply (wp_instr pc (add_vec_int pc 4) false
              (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS)) m
              (<[Regidx rd := regval_into_reg mstatus_in]> m) pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               mstatus ↦ᵣ{dqm} mstatus_in)%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hfmap Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k Hcsr] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iDestruct (cr_frames_in (DfracOwn (q/2)) dqm
                   (R_bitvector_64 mstatus) mstatus_in Hfresh
                   with "Hcsr Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hmst_k Hpmpc_k] [Hf Hrw Hro]");
        [| iApply (swp_execute_CSRReg_csrr ∅ (cr_Dro (R_bitvector_64 mstatus))
                     (cr_Df (DfracOwn (q/2)) dqm (R_bitvector_64 mstatus))
                     (cw_rs (R_bitvector_64 mstatus) mstatus_in) m
                     csr_mstatus rd mstatus_in
                     (cr_disj (R_bitvector_64 mstatus))
                     (cr_in_priv (R_bitvector_64 mstatus))
                     (cw_rs_priv (R_bitvector_64 mstatus) mstatus_in Hfresh)
                     Hrd
                     ltac:(vm_compute; reflexivity)
                     (hval_check_CSR_result _ ∅ _ csr_mstatus CSRRead
                        (cr_in_priv (R_bitvector_64 mstatus)) (cr_in_sec (R_bitvector_64 mstatus))
                        (cr_in_misa (R_bitvector_64 mstatus))
                        (cw_rs_priv (R_bitvector_64 mstatus) mstatus_in Hfresh)
                        (cw_rs_sec (R_bitvector_64 mstatus) mstatus_in Hfresh)
                        (cw_rs_misa (R_bitvector_64 mstatus) mstatus_in Hfresh)
                        ltac:(vm_compute; reflexivity) Hchk)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     ltac:(intros ?; vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro [Hcert]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (cr_frames_out (DfracOwn (q/2)) dqm
                     (R_bitvector_64 mstatus) mstatus_in Hfresh with "Hro")
          as "(Hcsr & Hpriv_k & _ & _)".
        iSplitR; [done|]. iFrame "Hf HPC HnPC".
        iSplitL "Hhs_k Hpriv_k Hmst_k".
        { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
        iFrame "Hpmpc_k Hcsr".
      + iIntros "Hrw Hro".
        iApply (swp_mono with "[] [-]");
          [| iApply (swp_hfrun 3 ∅ (cr_Dro (R_bitvector_64 mstatus))
                       (cr_Df (DfracOwn (q/2)) dqm (R_bitvector_64 mstatus))
                       (cw_rs (R_bitvector_64 mstatus) mstatus_in) _ _ _
                       (cr_disj (R_bitvector_64 mstatus))
                       (hfrun_read_CSR_mstatus
                          (∅ ∪ cr_Dro (R_bitvector_64 mstatus)) ∅
                          (cw_rs (R_bitvector_64 mstatus) mstatus_in)
                          (cr_in_r (R_bitvector_64 mstatus)))
                       with "Hcert Hrw Hro") ].
        iIntros (x) "(-> & Hrw & Hro)".
        rewrite (cw_rs_r (R_bitvector_64 mstatus) mstatus_in).
        iSplitR; [done|]. iFrame.
    - iApply bi.later_intro. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hcsr')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hcsr'").
  Qed.

  (* mcounteren (0x306): Ext_U-gated; misa.U recovered from hw_config. *)
  Lemma wp_csrr_mcounteren_gpr (pc : mword 64) (rd : mword 5)
      (mcen_in : mword 32) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mcounteren ↦ᵣ mcen_in -∗
    instr pc false (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (zero_extend' 64 mcen_in)]> m) -∗
      mcounteren ↦ᵣ mcen_in -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc Hpc Hfmap Hcsr Hinstr Hcont".
    assert (Hfresh : cw_fresh (R_bitvector_32 mcounteren))
      by (rewrite /cw_fresh; split_and!; vm_compute; reflexivity).
    (* the Ext_U gate needs no premise here: the check is transported from the
       reference state, where misa IS [MISA_C] and misa.U is set -- the same
       pin [hw_config] carries. *)
    assert (Hchk : exec (check_CSR_result csr_mcounteren Machine CSRRead) dstateM
                   = Some (CSR_Check_OK tt, dstateM))
      by (vm_compute; reflexivity).
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & %Hmisaval & %Hsecval & _)".
    subst misa0 mseccfg0.
    iApply (wp_instr pc (add_vec_int pc 4) false
              (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS)) m
              (<[Regidx rd := regval_into_reg (zero_extend' 64 mcen_in)]> m)
              pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               mcounteren ↦ᵣ mcen_in)%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hfmap Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k Hcsr] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iDestruct (cr_frames_in (DfracOwn (q/2)) (DfracOwn 1)
                   (R_bitvector_32 mcounteren) mcen_in Hfresh
                   with "Hcsr Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hmst_k Hpmpc_k] [Hf Hrw Hro]");
        [| iApply (swp_execute_CSRReg_csrr ∅
                     (cr_Dro (R_bitvector_32 mcounteren))
                     (cr_Df (DfracOwn (q/2)) (DfracOwn 1)
                        (R_bitvector_32 mcounteren))
                     (cw_rs (R_bitvector_32 mcounteren) mcen_in) m
                     csr_mcounteren rd (zero_extend' 64 mcen_in)
                     (cr_disj (R_bitvector_32 mcounteren))
                     (cr_in_priv (R_bitvector_32 mcounteren))
                     (cw_rs_priv (R_bitvector_32 mcounteren) mcen_in Hfresh)
                     Hrd
                     ltac:(vm_compute; reflexivity)
                     (hval_check_CSR_result _ ∅ _ csr_mcounteren CSRRead
                        (cr_in_priv (R_bitvector_32 mcounteren)) (cr_in_sec (R_bitvector_32 mcounteren))
                        (cr_in_misa (R_bitvector_32 mcounteren))
                        (cw_rs_priv (R_bitvector_32 mcounteren) mcen_in Hfresh)
                        (cw_rs_sec (R_bitvector_32 mcounteren) mcen_in Hfresh)
                        (cw_rs_misa (R_bitvector_32 mcounteren) mcen_in Hfresh)
                        ltac:(vm_compute; reflexivity) Hchk)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     ltac:(intros ?; vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro [Hcert]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (cr_frames_out (DfracOwn (q/2)) (DfracOwn 1)
                     (R_bitvector_32 mcounteren) mcen_in Hfresh with "Hro")
          as "(Hcsr & Hpriv_k & _ & _)".
        iSplitR; [done|]. iFrame "Hf HPC HnPC".
        iSplitL "Hhs_k Hpriv_k Hmst_k".
        { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
        iFrame "Hpmpc_k Hcsr".
      + iIntros "Hrw Hro".
        iApply (swp_mono with "[] [-]");
          [| iApply (swp_hfrun 3 ∅ (cr_Dro (R_bitvector_32 mcounteren))
                       (cr_Df (DfracOwn (q/2)) (DfracOwn 1)
                          (R_bitvector_32 mcounteren))
                       (cw_rs (R_bitvector_32 mcounteren) mcen_in) _ _ _
                       (cr_disj (R_bitvector_32 mcounteren))
                       (hfrun_read_CSR_mcounteren
                          (∅ ∪ cr_Dro (R_bitvector_32 mcounteren)) ∅
                          (cw_rs (R_bitvector_32 mcounteren) mcen_in)
                          (cr_in_r (R_bitvector_32 mcounteren)))
                       with "Hcert Hrw Hro") ].
        iIntros (x) "(-> & Hrw & Hro)".
        rewrite (cw_rs_r (R_bitvector_32 mcounteren) mcen_in).
        iSplitR; [done|]. iFrame.
    - iApply bi.later_intro. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hcsr')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hcsr'").
  Qed.
End WpCsrrGprA.
