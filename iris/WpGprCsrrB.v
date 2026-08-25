From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RegFile RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec ExecCommon WpGpr.
Require Import InstrBytes.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
Local Open Scope Z_scope.
Require Import WpGprCsrrCommon.
Require Import HartSwp HartLift HartRegNode HartSpan HartSpanChar HartGoodb
        WpDecodeBridge.
Require Import WpMmodeJump.     (* cw_Drw / cw_Dro *)
Require Import WpMmodeCsrSwp.   (* swp_execute_CSRReg_csrr + the cr_* footprint *)
Require Import TsoCtx.

Lemma exec_read_CSR_menvcfg s :
  exec (read_CSR (Ox"30A")) s
    = Some (subrange_vec_dec (register_lookup menvcfg s.(sregs)) (Z.sub xlen 1) 0, s).
Proof. drive_csr. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). apply exec_returnM. Qed.

Lemma exec_read_CSR_sie s :
  exec (read_CSR (Ox"104")) s
    = Some (lower_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs)), s).
Proof.
  drive_csr.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)). apply exec_returnM.
Qed.

Lemma exec_read_CSR_time s :
  exec (read_CSR (Ox"C01")) s
    = Some (subrange_vec_dec (register_lookup mtime s.(sregs)) (Z.sub xlen 1) 0, s).
Proof. drive_csr. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mtime s)). apply exec_returnM. Qed.

(* scause (0x142) reads the register straight out, with no subrange and no
   lowering -- it is an S-level CSR with no M-level counterpart to narrow. *)
Lemma exec_read_CSR_scause s :
  exec (read_CSR (Ox"142")) s = Some (register_lookup scause s.(sregs), s).
Proof. drive_csr. reflexivity. Qed.

(* the walker's twins of the [exec_read_CSR_*] facts above: the same cascade
   walk, done at the TERM so both interpreters can use it.  Each concludes at
   the value the leaf's statement names ([subrange64_id] for the two subrange
   reads), so no leaf carries the projection. *)
Lemma read_CSR_menvcfg_red :
  read_CSR (Ox"30A")
  = (Defs.bind (Defs.read_reg menvcfg)
       (fun v : mword 64 => returnM (subrange_vec_dec v (Z.sub xlen 1) 0))
     : M (mword 64)).
Proof. drive_csr_term. reflexivity. Qed.

Lemma hfrun_read_CSR_menvcfg (D Drw : gset register) (rs : regstate) :
  (R_bitvector_64 menvcfg : register) ∈ D ->
  hfrun 3 D Drw rs (read_CSR (Ox"30A"))
  = Some (register_lookup (R_bitvector_64 menvcfg) rs, rs).
Proof.
  intros HD. rewrite read_CSR_menvcfg_red.
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  cbn beta iota zeta delta [Defs.returnm returnM].
  rewrite hfrun_ret subrange64_id. reflexivity.
Qed.

Lemma read_CSR_sie_red :
  read_CSR (Ox"104")
  = (Defs.bind (Defs.read_reg mie)
       (fun v : mword 64 =>
          Defs.bind (Defs.read_reg mideleg)
            (fun d : mword 64 => returnM (lower_mie v d))) : M (mword 64)).
Proof. drive_csr_term. reflexivity. Qed.

Lemma hfrun_read_CSR_sie (D Drw : gset register) (rs : regstate) :
  (R_bitvector_64 mie : register) ∈ D ->
  (R_bitvector_64 mideleg : register) ∈ D ->
  hfrun 4 D Drw rs (read_CSR (Ox"104"))
  = Some (lower_mie (register_lookup (R_bitvector_64 mie) rs)
            (register_lookup (R_bitvector_64 mideleg) rs), rs).
Proof.
  intros HD1 HD2. rewrite read_CSR_sie_red.
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD1).
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD2).
  cbn beta iota zeta delta [Defs.returnm returnM].
  apply hfrun_ret.
Qed.


(* ---------------------------------------------------------------------- *)
(* sie reads TWO cells, so this ONE leaf carries its own five-cell read     *)
(* frame rather than a second named footprint family: [cr_*] generalized    *)
(* over the number of read cells would be a cross-product, and mie /        *)
(* mideleg is the only pair in the tree.                                    *)
(* ---------------------------------------------------------------------- *)
Definition sie_Dro : gset register :=
  {[ (R_bitvector_64 mideleg : register) ]} ∪ cr_Dro (R_bitvector_64 mie).

Definition sie_rs (mie_in mideleg_in : mword 64) : regstate :=
  register_set (R_bitvector_64 mideleg) mideleg_in
    (cw_rs (R_bitvector_64 mie) mie_in).

Definition sie_Df (dqp : dfrac) : register -> dfrac := fun r' =>
  if decide (r' = (misa : register)) then DfracDiscarded
  else if decide (r' = (mseccfg : register)) then DfracDiscarded
  else if decide (r' = (R_bitvector_64 mie : register)) then DfracOwn 1
  else if decide (r' = (R_bitvector_64 mideleg : register)) then DfracOwn 1
  else dqp.

Lemma sie_Df_misa dqp : sie_Df dqp misa = DfracDiscarded.
Proof. rewrite /sie_Df. repeat case_decide; congruence. Qed.
Lemma sie_Df_sec dqp : sie_Df dqp mseccfg = DfracDiscarded.
Proof. rewrite /sie_Df. repeat case_decide; congruence. Qed.
Lemma sie_Df_mie dqp : sie_Df dqp mie = DfracOwn 1.
Proof. rewrite /sie_Df. repeat case_decide; congruence. Qed.
Lemma sie_Df_mdl dqp : sie_Df dqp mideleg = DfracOwn 1.
Proof. rewrite /sie_Df. repeat case_decide; congruence. Qed.
Lemma sie_Df_priv dqp : sie_Df dqp cur_privilege = dqp.
Proof. rewrite /sie_Df. repeat case_decide; congruence. Qed.

Lemma sie_mie_fresh : cw_fresh (R_bitvector_64 mie).
Proof. rewrite /cw_fresh; split_and!; vm_compute; reflexivity. Qed.

Lemma sie_disj : (∅ : gset register) ## sie_Dro.
Proof. set_solver. Qed.
Lemma sie_in_mie : (R_bitvector_64 mie : register) ∈ (∅ : gset register) ∪ sie_Dro.
Proof. rewrite /sie_Dro /cr_Dro /cw_Drw. set_solver. Qed.
Lemma sie_in_mdl :
  (R_bitvector_64 mideleg : register) ∈ (∅ : gset register) ∪ sie_Dro.
Proof. rewrite /sie_Dro. set_solver. Qed.
Lemma sie_in_priv :
  (cur_privilege : register) ∈ (∅ : gset register) ∪ sie_Dro.
Proof. rewrite /sie_Dro /cr_Dro /cw_Dro. set_solver. Qed.
Lemma sie_in_sec : (mseccfg : register) ∈ (∅ : gset register) ∪ sie_Dro.
Proof. rewrite /sie_Dro /cr_Dro /cw_Dro. set_solver. Qed.
Lemma sie_in_misa : (misa : register) ∈ (∅ : gset register) ∪ sie_Dro.
Proof. rewrite /sie_Dro /cr_Dro /cw_Dro. set_solver. Qed.

Local Ltac sielk :=
  rewrite /sie_rs;
  etransitivity; [ apply irrelevant_register_set; vm_compute; reflexivity |].

Lemma sie_rs_mdl (mie_in mideleg_in : mword 64) :
  register_lookup (R_bitvector_64 mideleg) (sie_rs mie_in mideleg_in)
  = mideleg_in.
Proof. rewrite /sie_rs. apply register_lookup_set. Qed.
Lemma sie_rs_mie (mie_in mideleg_in : mword 64) :
  register_lookup (R_bitvector_64 mie) (sie_rs mie_in mideleg_in) = mie_in.
Proof. sielk. apply cw_rs_r. Qed.
Lemma sie_rs_priv (mie_in mideleg_in : mword 64) :
  register_lookup cur_privilege (sie_rs mie_in mideleg_in) = Machine.
Proof. sielk. apply (cw_rs_priv (R_bitvector_64 mie) mie_in sie_mie_fresh). Qed.
Lemma sie_rs_sec (mie_in mideleg_in : mword 64) :
  register_lookup mseccfg (sie_rs mie_in mideleg_in) = mword_of_int 0.
Proof. sielk. apply (cw_rs_sec (R_bitvector_64 mie) mie_in sie_mie_fresh). Qed.
Lemma sie_rs_misa (mie_in mideleg_in : mword 64) :
  register_lookup misa (sie_rs mie_in mideleg_in) = MISA_C.
Proof. sielk. apply (cw_rs_misa (R_bitvector_64 mie) mie_in sie_mie_fresh). Qed.

Section sieframes.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma sie_frames (dqp : dfrac) (mie_in mideleg_in : mword 64) :
    (hreg_frame_ro (sie_Df dqp) (sie_rs mie_in mideleg_in) sie_Dro : iProp Σ)
    ⊣⊢ (mideleg ↦ᵣ mideleg_in ∗ mie ↦ᵣ mie_in ∗
        reg_pointsto cur_privilege dqp Machine ∗
        reg_pointsto mseccfg DfracDiscarded (mword_of_int 0) ∗
        reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    rewrite /hreg_frame_ro /sie_Dro /cr_Dro /cw_Drw /cw_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite sie_rs_mdl sie_rs_mie sie_rs_priv sie_rs_sec sie_rs_misa.
    rewrite (sie_Df_mdl dqp) (sie_Df_mie dqp) (sie_Df_priv dqp)
      (sie_Df_sec dqp) (sie_Df_misa dqp).
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma sie_frames_in (dqp : dfrac) (mie_in mideleg_in : mword 64) :
    mie ↦ᵣ mie_in -∗ mideleg ↦ᵣ mideleg_in -∗
    reg_pointsto cur_privilege dqp Machine -∗
    reg_pointsto mseccfg DfracDiscarded (mword_of_int 0) -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    (hreg_frame (sie_rs mie_in mideleg_in) ∅ ∗
     hreg_frame_ro (sie_Df dqp) (sie_rs mie_in mideleg_in) sie_Dro : iProp Σ).
  Proof.
    iIntros "H1 H2 H3 H4 H5".
    iSplitR; [iApply hreg_frame_empty|].
    rewrite (sie_frames dqp mie_in mideleg_in). iFrame.
  Qed.

  Lemma sie_frames_out (dqp : dfrac) (mie_in mideleg_in : mword 64) :
    (hreg_frame_ro (sie_Df dqp) (sie_rs mie_in mideleg_in) sie_Dro : iProp Σ) -∗
    (mideleg ↦ᵣ mideleg_in ∗ mie ↦ᵣ mie_in ∗
     reg_pointsto cur_privilege dqp Machine ∗
     reg_pointsto mseccfg DfracDiscarded (mword_of_int 0) ∗
     reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    rewrite (sie_frames dqp mie_in mideleg_in). iIntros "H". iExact "H".
  Qed.
End sieframes.

(* ===== menvcfg (0x30A): Ext_U-gated, read = subrange of menvcfg ===== *)
Definition csr_menvcfg : mword 12 := Ox"30A".
Definition menvcfg_rdval (s : mstate) : mword 64 :=
  subrange_vec_dec (register_lookup menvcfg s.(sregs)) (Z.sub xlen 1) 0.

Lemma exec_check_CSR_result_menvcfg s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_menvcfg Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HU. apply exec_check_CSR_result_read. apply exec_check_CSR_read.
  - assert (H : check_CSR_priv csr_menvcfg Machine = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - (* menvcfg's gate is now Ext_U AND the xenvcfg-CSRs-exist config predicate *)
    assert (Hacceq : is_CSR_accessible csr_menvcfg Machine CSRRead
                     = Defs.and_boolM ((currentlyEnabled Ext_U) : M bool)
                                      (returnM xenvcfg_csrs_are_defined))
      by csr_dispatch_eq.
    rewrite Hacceq.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_U s HU)). cbn match.
    replace xenvcfg_csrs_are_defined with true by (vm_compute; reflexivity).
    apply exec_returnm.
  - assert (H : stateen_allows_CSR_access csr_menvcfg Machine CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_csr_id_read_callback_menvcfg s d :
  exec (csr_id_read_callback csr_menvcfg d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_menvcfg d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_menvcfg_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_menvcfg zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (menvcfg_rdval s))).
Proof.
  intros Hrd Hpriv HU.
  apply (csrr_read_step csr_menvcfg rd (menvcfg_rdval s) s _ Hpriv).
  - apply (exec_check_CSR_result_menvcfg s HU).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_menvcfg.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_menvcfg.
  - rewrite (exec_wX_bits_gpr rd (menvcfg_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ===== sie (0x104): Ext_S-gated, read = lower_mie mie mideleg (TWO regs) ===== *)
Definition csr_sie : mword 12 := Ox"104".
Definition sie_rdval (s : mstate) : mword 64 :=
  lower_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs)).

Lemma exec_check_CSR_result_sie s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_sie Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS. apply exec_check_CSR_result_read. apply exec_check_CSR_read.
  - assert (H : check_CSR_priv csr_sie Machine = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - assert (Hacceq : is_CSR_accessible csr_sie Machine CSRRead = currentlyEnabled Ext_S)
      by csr_dispatch_eq.
    rewrite Hacceq. rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity.
  - assert (H : stateen_allows_CSR_access csr_sie Machine CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_csr_id_read_callback_sie s d :
  exec (csr_id_read_callback csr_sie d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_sie d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_sie_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_sie zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sie_rdval s))).
Proof.
  intros Hrd Hpriv HS.
  apply (csrr_read_step csr_sie rd (sie_rdval s) s _ Hpriv).
  - apply (exec_check_CSR_result_sie s HS).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_sie.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_sie.
  - rewrite (exec_wX_bits_gpr rd (sie_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ===== time (0xC01): Ext_Zicntr-gated + counter_enabled 1 priv (Machine =>  *)
(* true unconditionally).  Read = subrange of mtime. ===== *)
Definition csr_time : mword 12 := Ox"C01".
Definition time_rdval (s : mstate) : mword 64 :=
  subrange_vec_dec (register_lookup mtime s.(sregs)) (Z.sub xlen 1) 0.

(* The [time] check reads the COUNTER-ENABLE cells and nothing else: at
   Machine privilege [feature_enabled_for_priv_bool] ignores the bits, so the
   whole four-level [check_CSR] collapses (by conversion, at a literal CSR
   number and privilege) to two reads and a [Ret].  No leaf owns mcounteren or
   scounteren, and it does not have to: the values are never used, so the
   route into [hval] is a ∀-peel of each read rather than the reference-state
   [goodb] transport -- which is why this lemma has no premises at all, just
   as [exec_check_CSR_result_time] has none. *)
Lemma check_CSR_result_time_red :
  check_CSR_result csr_time Machine CSRRead
  = Interface.Next (Interface.RegRead (R_bitvector_32 mcounteren) None)
      (fun _ : mword 32 =>
         Interface.Next (Interface.RegRead (R_bitvector_32 scounteren) None)
           (fun _ : mword 32 => Interface.Ret (CSR_Check_OK tt))).
Proof. reflexivity. Qed.

Section timecheck.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma hval_check_CSR_result_time (D Drw : gset register) (rs : regstate) :
    hval D Drw rs (check_CSR_result csr_time Machine CSRRead)
      (CSR_Check_OK tt) rs.
  Proof.
    rewrite check_CSR_result_time_red.
    apply (hval_read_any D Drw (R_bitvector_32 mcounteren));
      [cbn [hregread_at]; apply bool_decide_eq_true_2; reflexivity|].
    intros v1. rewrite hregread_resume_red.
    apply (hval_read_any D Drw (R_bitvector_32 scounteren));
      [cbn [hregread_at]; apply bool_decide_eq_true_2; reflexivity|].
    intros v2. rewrite hregread_resume_red.
    apply hval_ret.
  Qed.
End timecheck.

Lemma read_CSR_time_red :
  read_CSR (Ox"C01")
  = (Defs.bind (Defs.read_reg mtime)
       (fun v : mword 64 => returnM (subrange_vec_dec v (Z.sub xlen 1) 0))
     : M (mword 64)).
Proof. drive_csr_term. reflexivity. Qed.

Lemma exec_hartSupports_Zicntr s : exec (hartSupports Ext_Zicntr) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicntr) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_Zicntr s :
  exec (currentlyEnabled Ext_Zicntr) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicntr) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicntr s)). cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k ?acc] =>
    destruct acc; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
    replace (Z.geb k 0) with true by reflexivity; cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)); cbn match
  end.
  apply exec_hartSupports_Zicntr.
Qed.

Lemma exec_counter_enabled_machine (index : Z) s :
  exec (counter_enabled index Machine) s = Some (true, s).
Proof.
  unfold counter_enabled.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg scounteren s)).
  unfold feature_enabled_for_priv_bool.
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (feature_enabled_for_priv Machine _ _ _) s = Some (FEATURE_ENABLED, s))).
  2:{ unfold feature_enabled_for_priv. apply exec_returnM. }
  apply exec_returnM.
Qed.

Lemma exec_is_CSR_accessible_time s :
  exec (is_CSR_accessible csr_time Machine CSRRead) s = Some (true, s).
Proof.
  assert (Hred : is_CSR_accessible csr_time Machine CSRRead
                 = Defs.and_boolM (currentlyEnabled Ext_Zicntr) (counter_enabled 1 Machine))
    by csr_dispatch_eq.
  rewrite Hred.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Zicntr s)). cbn match.
  apply exec_counter_enabled_machine.
Qed.

Lemma exec_check_CSR_result_time s :
  exec (check_CSR_result csr_time Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  apply exec_check_CSR_result_read. apply exec_check_CSR_read.
  - assert (H : check_CSR_priv csr_time Machine = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - apply exec_is_CSR_accessible_time.
  - assert (H : stateen_allows_CSR_access csr_time Machine CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_csr_id_read_callback_time s d :
  exec (csr_id_read_callback csr_time d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_time d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_time_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_time zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (time_rdval s))).
Proof.
  intros Hrd Hpriv.
  apply (csrr_read_step csr_time rd (time_rdval s) s _ Hpriv).
  - apply (exec_check_CSR_result_time s).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_time.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_time.
  - rewrite (exec_wX_bits_gpr rd (time_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ===== scause (0x142): Ext_S-gated, read = the register itself.  The     *)
(* privilege-free half; the Supervisor accessibility check and the          *)
(* [execute] instance are next to their leaf, in WpSconfCsr.v. ===== *)
Definition csr_scause : mword 12 := Ox"142".

Lemma exec_csr_id_read_callback_scause s d :
  exec (csr_id_read_callback csr_scause d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_scause d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

(* ===== stval (0x143): the second of the three trap-scratch CSRs, and    *)
(* character-for-character scause's twin -- Ext_S-gated, read = the        *)
(* register itself, no subrange and no lowering. ===== *)
Definition csr_stval : mword 12 := Ox"143".

Lemma exec_read_CSR_stval s :
  exec (read_CSR (Ox"143")) s = Some (register_lookup stval s.(sregs), s).
Proof. drive_csr. reflexivity. Qed.

Lemma exec_csr_id_read_callback_stval s d :
  exec (csr_id_read_callback csr_stval d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_stval d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

(* ===== sepc (0x141): the third, and the one that is NOT its cell.  The   *)
(* read is [get_xepc Supervisor], which runs the raw word through          *)
(* [align_pc]; with Zca enabled -- misa.C = 1 on this platform, hence the  *)
(* premise -- that clears bit 0.  Every WRITE goes through [legalize_xepc],*)
(* which clears the same bit, so the cell can only ever hold an aligned    *)
(* word and the wrapper is the identity in practice; nothing here assumes  *)
(* that, and a caller who knows it collapses the wrapper itself.  The      *)
(* wrapper term is spelled out rather than named: it is definitionally     *)
(* [WpGprCsrwA.mepc_val], the legalizer shared with mepc, and introducing  *)
(* a second name for it here would be the duplication, not the fix. ===== *)
Definition csr_sepc : mword 12 := Ox"141".

Lemma exec_read_CSR_sepc s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (read_CSR (Ox"141")) s
    = Some (update_vec_dec (register_lookup sepc s.(sregs)) 0 ('b"0"), s).
Proof.
  intro HmisaC. drive_csr.
  unfold get_xepc. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sepc s)).
  unfold align_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Zca s HmisaC)).
  cbn zeta match. apply exec_returnM.
Qed.

Lemma exec_csr_id_read_callback_sepc s d :
  exec (csr_id_read_callback csr_sepc d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_sepc d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma menvcfg_rdval_set_nextPC (s : mstate) (v : mword 64) :
  menvcfg_rdval (set_reg s nextPC v) = menvcfg_rdval s.
Proof. unfold menvcfg_rdval; rewrite ?sregs_set_reg.
  rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ]. Qed.
Lemma sie_rdval_set_nextPC (s : mstate) (v : mword 64) :
  sie_rdval (set_reg s nextPC v) = sie_rdval s.
Proof. unfold sie_rdval; rewrite ?sregs_set_reg.
  do 2 (rewrite irrelevant_register_set; [| vm_compute; reflexivity]). reflexivity. Qed.

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
Section WpCsrrGprB.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* time (0xC01): Ext_Zicntr-gated, no misa premise needed (holds for any state).
     [mtime] lives in [clock_inv] and advances nondeterministically with the
     clock tick, so this leaf owns NO mtime cell and cannot pin the value the
     instruction reads: the continuation is ∀-quantified over the read value
     [tv].  (No clock_inv opening is needed either -- the exec witness reads
     mtime straight off the abstract step state σ.) *)
  Lemma wp_csrr_time_gpr (pc : mword 64) (rd : mword 5)
      (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (CSRReg (csr_time, zreg, Regidx rd, CSRRS)) -∗
    ( ∀ tv : mword 64,
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg tv]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc Hpc Hfmap Hinstr Hcont".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & %Hmisaval & %Hsecval & _)".
    subst misa0 mseccfg0.
    (* the post-GPR-file is not nameable here (mtime is unowned), so this is
       the ONE leaf on [wp_instr_ex] rather than [wp_instr]. *)
    iApply (wp_instr_ex pc (add_vec_int pc 4) false
              (CSRReg (csr_time, zreg, Regidx rd, CSRRS)) m pmpcfg0
              (fun mf => ∃ tv : mword 64,
                 ⌜mf = <[Regidx rd := regval_into_reg tv]> m⌝ ∗
                 mmode_config (DfracOwn (q/2)) ∗
                 pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0)%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hfmap Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iDestruct (cr0_frames_in (DfracOwn (q/2))
                   with "Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hmst_k Hpmpc_k] [Hf Hrw Hro]");
        [| iApply (swp_execute_CSRReg_csrr_gen ∅ cw_Dro
                     (cw_Df (DfracOwn (q/2))) cr0_rs m csr_time rd
                     (fun _ => emp)%I
                     cr0_disj cr0_in_priv cr0_rs_priv
                     Hrd
                     ltac:(vm_compute; reflexivity)
                     (hval_check_CSR_result_time _ ∅ cr0_rs)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     ltac:(intros ?; vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro [Hcert]") ].
      + iIntros (e) "(-> & H)".
        iDestruct "H" as (tv) "(_ & Hf & Hrw & Hro)".
        iDestruct (cr0_frames_out (DfracOwn (q/2)) with "Hro")
          as "(Hpriv_k & _ & _)".
        iSplitR; [done|]. iFrame "HPC HnPC".
        iExists (<[Regidx rd := regval_into_reg tv]> m). iFrame "Hf".
        iExists tv. iSplitR; [done|].
        iSplitL "Hhs_k Hpriv_k Hmst_k".
        { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
        iFrame "Hpmpc_k".
      + (* the mtime read: UNPINNED, so the value is whatever the machine has *)
        iIntros "Hrw Hro".
        rewrite read_CSR_time_red.
        iApply (swp_bind_use (Defs.read_reg (R_bitvector_64 mtime)) _
                  (fun _ : mword 64 =>
                     hreg_frame cr0_rs ∅ ∗
                     hreg_frame_ro (cw_Df (DfracOwn (q/2))) cr0_rs cw_Dro)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_read_reg_any (R_bitvector_64 mtime) with "Hcert").
          iIntros (v). iFrame. }
        iIntros (tv) "[Hrw Hro]". iApply swp_ret. iFrame.
    - iNext. iIntros (mf) "Hmm' Hpmpc' Hpc' Hf' H".
      iDestruct "H" as (tv) "(-> & Hmm_k' & Hpmpc_k')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" $! tv with "Hmm'' Hpmpc'' Hpc' Hf'").
  Qed.

  (* menvcfg (0x30A): Ext_U-gated; misa.U recovered from hw_config. *)
  Lemma wp_csrr_menvcfg_gpr (pc : mword 64) (rd : mword 5)
      (menvcfg_in : mword 64) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    menvcfg ↦ᵣ menvcfg_in -∗
    instr pc false (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg (menvcfg_in)]> m) -∗
      menvcfg ↦ᵣ menvcfg_in -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc Hpc Hfmap Hcsr Hinstr Hcont".
    assert (Hfresh : cw_fresh (R_bitvector_64 menvcfg))
      by (rewrite /cw_fresh; split_and!; vm_compute; reflexivity).
    assert (Hchk : exec (check_CSR_result csr_menvcfg Machine CSRRead) dstateM
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
              (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS)) m
              (<[Regidx rd := regval_into_reg menvcfg_in]> m) pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               menvcfg ↦ᵣ menvcfg_in)%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hfmap Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k Hcsr] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iDestruct (cr_frames_in (DfracOwn (q/2)) (DfracOwn 1)
                   (R_bitvector_64 menvcfg) menvcfg_in Hfresh
                   with "Hcsr Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hmst_k Hpmpc_k] [Hf Hrw Hro]");
        [| iApply (swp_execute_CSRReg_csrr ∅ (cr_Dro (R_bitvector_64 menvcfg))
                     (cr_Df (DfracOwn (q/2)) (DfracOwn 1)
                        (R_bitvector_64 menvcfg))
                     (cw_rs (R_bitvector_64 menvcfg) menvcfg_in) m
                     csr_menvcfg rd menvcfg_in
                     (cr_disj (R_bitvector_64 menvcfg))
                     (cr_in_priv (R_bitvector_64 menvcfg))
                     (cw_rs_priv (R_bitvector_64 menvcfg) menvcfg_in Hfresh)
                     Hrd
                     ltac:(vm_compute; reflexivity)
                     (hval_check_CSR_result _ ∅ _ csr_menvcfg CSRRead
                        (cr_in_priv (R_bitvector_64 menvcfg)) (cr_in_sec (R_bitvector_64 menvcfg))
                        (cr_in_misa (R_bitvector_64 menvcfg))
                        (cw_rs_priv (R_bitvector_64 menvcfg) menvcfg_in Hfresh)
                        (cw_rs_sec (R_bitvector_64 menvcfg) menvcfg_in Hfresh)
                        (cw_rs_misa (R_bitvector_64 menvcfg) menvcfg_in Hfresh)
                        ltac:(vm_compute; reflexivity) Hchk)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     ltac:(intros ?; vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro [Hcert]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (cr_frames_out (DfracOwn (q/2)) (DfracOwn 1)
                     (R_bitvector_64 menvcfg) menvcfg_in Hfresh with "Hro")
          as "(Hcsr & Hpriv_k & _ & _)".
        iSplitR; [done|]. iFrame "Hf HPC HnPC".
        iSplitL "Hhs_k Hpriv_k Hmst_k".
        { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
        iFrame "Hpmpc_k Hcsr".
      + iIntros "Hrw Hro".
        iApply (swp_mono with "[] [-]");
          [| iApply (swp_hfrun 3 ∅ (cr_Dro (R_bitvector_64 menvcfg))
                       (cr_Df (DfracOwn (q/2)) (DfracOwn 1)
                          (R_bitvector_64 menvcfg))
                       (cw_rs (R_bitvector_64 menvcfg) menvcfg_in) _ _ _
                       (cr_disj (R_bitvector_64 menvcfg))
                       (hfrun_read_CSR_menvcfg
                          (∅ ∪ cr_Dro (R_bitvector_64 menvcfg)) ∅
                          (cw_rs (R_bitvector_64 menvcfg) menvcfg_in)
                          (cr_in_r (R_bitvector_64 menvcfg)))
                       with "Hcert Hrw Hro") ].
        iIntros (x) "(-> & Hrw & Hro)".
        rewrite (cw_rs_r (R_bitvector_64 menvcfg) menvcfg_in).
        iSplitR; [done|]. iFrame.
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hcsr')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hcsr'").
  Qed.
  (* sie (0x104): Ext_S-gated; misa.S recovered from hw_config.  The read
     value is a VIEW over TWO registers ([lower_mie mie mideleg]), so both
     cells are threaded (returned unchanged). *)
  Lemma wp_csrr_sie_gpr (pc : mword 64) (rd : mword 5)
      (mie_in mideleg_in : mword 64) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mie ↦ᵣ mie_in -∗
    mideleg ↦ᵣ mideleg_in -∗
    instr pc false (CSRReg (csr_sie, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg (lower_mie mie_in mideleg_in)]> m) -∗
      mie ↦ᵣ mie_in -∗
      mideleg ↦ᵣ mideleg_in -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc Hpc Hfmap Hmie Hmdl Hinstr Hcont".
    assert (Hchk : exec (check_CSR_result csr_sie Machine CSRRead) dstateM
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
              (CSRReg (csr_sie, zreg, Regidx rd, CSRRS)) m
              (<[Regidx rd :=
                 regval_into_reg (lower_mie mie_in mideleg_in)]> m) pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               mie ↦ᵣ mie_in ∗ mideleg ↦ᵣ mideleg_in)%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hfmap Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k Hmie Hmdl] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iDestruct (sie_frames_in (DfracOwn (q/2)) mie_in mideleg_in
                   with "Hmie Hmdl Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hmst_k Hpmpc_k] [Hf Hrw Hro]");
        [| iApply (swp_execute_CSRReg_csrr ∅ sie_Dro
                     (sie_Df (DfracOwn (q/2)))
                     (sie_rs mie_in mideleg_in) m
                     csr_sie rd (lower_mie mie_in mideleg_in)
                     sie_disj sie_in_priv
                     (sie_rs_priv mie_in mideleg_in)
                     Hrd
                     ltac:(vm_compute; reflexivity)
                     (hval_check_CSR_result _ ∅ _ csr_sie CSRRead
                        sie_in_priv sie_in_sec sie_in_misa
                        (sie_rs_priv mie_in mideleg_in)
                        (sie_rs_sec mie_in mideleg_in)
                        (sie_rs_misa mie_in mideleg_in)
                        ltac:(vm_compute; reflexivity) Hchk)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     ltac:(intros ?; vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro [Hcert]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (sie_frames_out (DfracOwn (q/2)) mie_in mideleg_in
                     with "Hro") as "(Hmdl & Hmie & Hpriv_k & _ & _)".
        iSplitR; [done|]. iFrame "Hf HPC HnPC".
        iSplitL "Hhs_k Hpriv_k Hmst_k".
        { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
        iFrame "Hpmpc_k Hmie Hmdl".
      + iIntros "Hrw Hro".
        iApply (swp_mono with "[] [-]");
          [| iApply (swp_hfrun 4 ∅ sie_Dro (sie_Df (DfracOwn (q/2)))
                       (sie_rs mie_in mideleg_in) _ _ _ sie_disj
                       (hfrun_read_CSR_sie (∅ ∪ sie_Dro) ∅
                          (sie_rs mie_in mideleg_in) sie_in_mie sie_in_mdl)
                       with "Hcert Hrw Hro") ].
        iIntros (x) "(-> & Hrw & Hro)".
        rewrite (sie_rs_mie mie_in mideleg_in) (sie_rs_mdl mie_in mideleg_in).
        iSplitR; [done|]. iFrame.
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hmie' & Hmdl')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hmie' Hmdl'").
  Qed.

End WpCsrrGprB.
