From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvExtras ExecCommon.
Require Import InstrBytes.
From iris.bi.lib Require Import fractional.
Local Open Scope Z_scope.

(* [subrange_vec_dec a (xlen-1) 0] extracts all 64 bits of a 64-bit word -- a
   noop (cf. subrange_id, but stated with the [Z.sub xlen 1] form the
   CSR reads use).  Lets the CSR-read WPs state the read value without the
   subrange. *)
Lemma subrange64_id (a : mword 64) : subrange_vec_dec a (Z.sub xlen 1) 0 = a.
Proof.
  apply bv_eq. unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (Z.sub xlen 1 - 0 + 1)) with 64%N.
  apply bv_wrap_bv_unsigned.
Qed.

Lemma csr_access_type_CSRRS_true (b : bool) : csr_access_type CSRRS b true = CSRRead.
Proof. destruct b; reflexivity. Qed.

(* ====================================================================== *)
(* Representation-independent CSR-read execute helpers, ported (verbatim in  *)
(* their pure content) from the old WpGprCsrrAny.v.  They reduce             *)
(* [execute_CSRReg csr x0 rd CSRRS] to a single [wX rd (read_CSR csr)] write, *)
(* per CSR (mstatus / mcounteren / menvcfg / sie / time).  The new-style WPs  *)
(* below feed these to [wp_instr]'s execute obligation.                       *)
(* ====================================================================== *)

(* Generic register-generic CSR-read step: csrr rd, csr  (= csrrs rd,csr,rs1z
   with rs1z = x0).  Parameterised over the CSR; the per-CSR facts
   (accessibility, read value, callback) are supplied as hypotheses.

   Privilege is a parameter for the same reason as in [exec_doCSR_csrw_p]:
   nothing on the read path inspects it beyond the [cur_privilege] read that
   the check_CSR_result premise already speaks about, so ONE lemma serves the
   Machine-mode boot leaves and the S-mode ones (time in WpSconfTimer). *)
Lemma csrr_read_step_p (p : Privilege) (csr : mword 12) (rd : mword 5) (readval : mword 64) (s s_w : mstate) :
  register_lookup cur_privilege s.(sregs) = p ->
  exec (check_CSR_result csr p CSRRead) s = Some (CSR_Check_OK tt, s) ->
  ext_check_CSR csr p CSRRead = true ->
  exec (read_CSR csr) s = Some (readval, s) ->
  eq_vec csr ((Ox"344") : mword 12) = false ->
  eq_vec csr ((Ox"144") : mword 12) = false ->
  exec (csr_id_read_callback csr readval) s = Some (tt, s) ->
  exec (wX_bits (Regidx rd) readval) s = Some (tt, s_w) ->
  exec (execute_CSRReg csr zreg (Regidx rd) CSRRS) s = Some (RETIRE_SUCCESS, s_w).
Proof.
  intros Hpriv Hchk Hext Hread H344 H144 Hcb Hwx.
  unfold execute_CSRReg.
  replace (generic_eq zreg zreg) with true by (vm_compute; reflexivity).
  rewrite csr_access_type_CSRRS_true.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_x0 (zero_extend' 5 ('b"00")) s ltac:(vm_compute; reflexivity))).
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ Hchk). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hext. cbn match.
  replace (if generic_neq CSRRead CSRWrite then read_CSR csr else returnM (zeros' 64))
    with (read_CSR csr) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hread).
  rewrite H344. rewrite H144. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM readval s)).
  replace (generic_eq CSRRead CSRRead) with true by reflexivity. cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _
    (_ : exec (Defs.bind0 (csr_id_read_callback csr readval) (wX_bits (Regidx rd) readval)) s
         = Some (tt, s_w))).
  2:{ rewrite (exec_bind0_Some _ _ _ _ _ Hcb). exact Hwx. }
  apply exec_returnM.
Qed.

Lemma csrr_read_step (csr : mword 12) (rd : mword 5) (readval : mword 64) (s s_w : mstate) :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (check_CSR_result csr Machine CSRRead) s = Some (CSR_Check_OK tt, s) ->
  ext_check_CSR csr Machine CSRRead = true ->
  exec (read_CSR csr) s = Some (readval, s) ->
  eq_vec csr ((Ox"344") : mword 12) = false ->
  eq_vec csr ((Ox"144") : mword 12) = false ->
  exec (csr_id_read_callback csr readval) s = Some (tt, s) ->
  exec (wX_bits (Regidx rd) readval) s = Some (tt, s_w) ->
  exec (execute_CSRReg csr zreg (Regidx rd) CSRRS) s = Some (RETIRE_SUCCESS, s_w).
Proof. apply (csrr_read_step_p Machine csr rd readval s s_w). Qed.

(* Walk the [read_CSR] dispatch; see WpGprCsrrAny provenance / build-perf note. *)
Ltac drive_csr :=
  unfold read_CSR;
  (* Batch-peel the leading false clauses (16 then 4 at a time) before the
     per-clause loop, mirroring [skip_csr_false_clauses]: the O(tail)-sized
     retyping that dominates the walk happens ~3x instead of ~90x.  The
     single-clause loop below still handles the residual clauses and the
     TRUE guard. *)
  repeat (erewrite exec_if_false_g16 by (vm_compute; reflexivity));
  repeat (erewrite exec_if_false_g4 by (vm_compute; reflexivity));
  repeat first
    [ erewrite exec_if_false_g by (vm_compute; reflexivity)
    | match goal with
      | |- context[if ?g then _ else _] =>
          let v := eval vm_compute in g in
          lazymatch v with
          | true  => replace g with true by (vm_compute; reflexivity)
          | false => replace g with false by (vm_compute; reflexivity)
          end
      end; cbn match ].

(* Gated check_CSR_result engine for CSRRead. *)
(* privilege-generic, for the same reason as [csrr_read_step_p]. *)
Lemma exec_check_CSR_read_p (p : Privilege) (csr : mword 12) s :
  exec (check_CSR_priv csr p) s = Some (true, s) ->
  check_CSR_access csr CSRRead = true ->
  exec (is_CSR_accessible csr p CSRRead) s = Some (true, s) ->
  exec (stateen_allows_CSR_access csr p CSRRead) s = Some (true, s) ->
  exec (check_CSR csr p CSRRead) s = Some (true, s).
Proof.
  intros Hpriv Hca Hacc Hst. unfold check_CSR.
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hpriv). cbn match.
  assert (HB : exec (returnM (check_CSR_access csr CSRRead) : M bool) s = Some (true, s))
    by (rewrite exec_returnm; rewrite Hca; reflexivity).
  rewrite (exec_and_boolM_Some _ _ _ _ _ HB). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hacc). cbn match.
  exact Hst.
Qed.

Lemma exec_check_CSR_read (csr : mword 12) s :
  exec (check_CSR_priv csr Machine) s = Some (true, s) ->
  check_CSR_access csr CSRRead = true ->
  exec (is_CSR_accessible csr Machine CSRRead) s = Some (true, s) ->
  exec (stateen_allows_CSR_access csr Machine CSRRead) s = Some (true, s) ->
  exec (check_CSR csr Machine CSRRead) s = Some (true, s).
Proof. apply (exec_check_CSR_read_p Machine csr s). Qed.

Lemma exec_check_CSR_result_read_p (p : Privilege) (csr : mword 12) s :
  exec (check_CSR csr p CSRRead) s = Some (true, s) ->
  exec (check_CSR_result csr p CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro Hcc. unfold check_CSR_result.
  rewrite (exec_bind_Some _ _ _ _ _ Hcc). cbn match. apply exec_returnm.
Qed.

Lemma exec_check_CSR_result_read (csr : mword 12) s :
  exec (check_CSR csr Machine CSRRead) s = Some (true, s) ->
  exec (check_CSR_result csr Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof. apply (exec_check_CSR_result_read_p Machine csr s). Qed.


(* Each CSR read value, and misa's U/S bits, are untouched by [set_reg _ nextPC _],
   so they carry into the execute state (set_reg σ nextPC (pc+4)) unchanged. *)
Lemma misa_set_nextPC (s : mstate) (v : mword 64) :
  register_lookup misa (set_reg s nextPC v).(sregs) = register_lookup misa s.(sregs).
Proof. rewrite ?sregs_set_reg.
  rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ]. Qed.

(* Shared Iris-level machinery for the csrr WPs (fractional reg points-to,
   mmode_config half-split/combine), moved out of Section WpCsrrMhartidGpr. *)
Section WpCsrrGprShared.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Global Instance reg_pointsto_fractional_csrr (r : register) (v : type_of_register r) :
    Fractional (fun q => reg_pointsto r (DfracOwn q) v).
  Proof. rewrite /reg_pointsto. apply _. Qed.
  Global Instance reg_pointsto_as_fractional_csrr (r : register) (q : Qp) (v : type_of_register r) :
    AsFractional (reg_pointsto r (DfracOwn q) v) (fun q => reg_pointsto r (DfracOwn q) v) q.
  Proof. rewrite /reg_pointsto. split; [done | apply _]. Qed.

  Lemma reg_pointsto_agree_csrr (r : register) (dq1 dq2 : dfrac) (v1 v2 : type_of_register r) :
    reg_pointsto r dq1 v1 -∗ reg_pointsto r dq2 v2 -∗ ⌜ v1 = v2 ⌝.
  Proof.
    rewrite /reg_pointsto. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
    iPureIntro. exact (Eqdep_dec.inj_pair2_eq_dec _ Decidable_eq_register _ r v1 v2 Heq).
  Qed.

  (* Split [mmode_config (DfracOwn q)] into two halves: one to hand to
     [wp_instr], the other kept to read [cur_privilege = Machine] at the
     execute state (the CSR read needs M-privilege).  Fraction-generic
     ([q := 1] recovers the original full-ownership version). *)
  Lemma mmode_config_split_half_csrr (q : Qp) :
    mmode_config (DfracOwn q) ⊢
      mmode_config (DfracOwn (q/2)) ∗ mmode_config (DfracOwn (q/2)).
  Proof.
    iIntros "(#Hhw & #Hinv & Hhs & Hpriv & Hmst)".
    iDestruct "Hmst" as (ms0) "(Hms & %HmIE & %HMPRV & %HSXL & %HKF)".
    iDestruct "Hhs" as "[Hhs1 Hhs2]".
    iDestruct "Hpriv" as "[Hpriv1 Hpriv2]".
    iDestruct "Hms" as "[Hms1 Hms2]".
    iSplitL "Hhs1 Hpriv1 Hms1".
    - iFrame "Hhw Hinv Hhs1 Hpriv1". iExists ms0. iFrame "Hms1 %".
    - iFrame "Hhw Hinv Hhs2 Hpriv2". iExists ms0. iFrame "Hms2 %".
  Qed.

  Lemma mmode_config_combine_half_csrr (q : Qp) :
    mmode_config (DfracOwn (q/2)) -∗ mmode_config (DfracOwn (q/2)) -∗
    mmode_config (DfracOwn q).
  Proof.
    iIntros "(#Hhw & #Hinv & Hhs1 & Hpriv1 & Hmst1) (_ & _ & Hhs2 & Hpriv2 & Hmst2)".
    iDestruct "Hmst1" as (ms0) "(Hms1 & %HmIE & %HMPRV & %HSXL & %HKF)".
    iDestruct "Hmst2" as (ms0') "(Hms2 & _ & _ & _)".
    iDestruct (reg_pointsto_agree_csrr with "Hms1 Hms2") as %<-.
    iCombine "Hhs1 Hhs2" as "Hhs".
    iCombine "Hpriv1 Hpriv2" as "Hpriv".
    iCombine "Hms1 Hms2" as "Hms".
    iFrame "Hhw Hinv Hhs Hpriv". iExists ms0. iFrame "Hms %".
  Qed.
End WpCsrrGprShared.
