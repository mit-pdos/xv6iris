(* WpPushOffCsr.v -- S-mode csrrci-on-sstatus (interrupt disable) instruction lemma
   
   [noff]/[intena] accesses.  Built by cloning wp_cldsp_gpr_s / wp_csdsp_gpr_s
   (WpSmodeGpr.v, 8-byte, sp-relative) with the base register generalized and
   the access width changed 8 -> 4. *)
From Stdlib Require Import ZArith FunctionalExtensionality.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.

Require Import WpGpr.
Require Import WpGprCsrwCommon WpGprCsrwA.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import ExecCommon.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(* csrrci a5,sstatus,2  (= csrrc a5,sstatus,imm5 with imm5<>0 -> CSRReadWrite)*)
(* at Supervisor, running with SIE ALREADY 0 (interrupt-disable idempotent).*)
(* ====================================================================== *)

Definition csr_sstatus : mword 12 := Ox"100".

(* RDVAL: the S-visible read of an mstatus value, as read_CSR(0x100) returns.
   [sstatus_read]/[sstatus_write_val]/[legalize_sstatus_val] now live low in
   WpGprCsrwCommon.v (reused by WpGprCsrwC's idempotence lemma). *)

(* ---- set a bitvector-64 register to the value it already holds = no-op ---- *)
Lemma register_set_bv64_id (r : register_bitvector_64) (rs : regstate) :
  register_set (R_bitvector_64 r) (register_lookup (R_bitvector_64 r) rs) rs = rs.
Proof.
  destruct rs. unfold register_set, register_lookup. cbn.
  f_equal. apply functional_extensionality. intro r'.
  destruct (register_bitvector_64_beq r' r) eqn:E.
  - apply register_bitvector_64_beq_iff in E. subst r'. reflexivity.
  - reflexivity.
Qed.

(* ---- Ext_H is not supported: hartSupports / currentlyEnabled reduce false ---- *)
Lemma exec_hartSupports_H s : exec (hartSupports Ext_H) s = Some (false, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_H) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_H_false s : exec (currentlyEnabled Ext_H) s = Some (false, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_H) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_H s)). reflexivity.
Qed.

(* ---- check_CSR path for sstatus at Supervisor / CSRReadWrite ---- *)
Lemma exec_check_CSR_priv_sstatus_S s :
  exec (check_CSR_priv csr_sstatus Supervisor) s = Some (true, s).
Proof.
  unfold check_CSR_priv.
  assert (Hp : exec (privLevel_to_CSR_privbits Supervisor) s = Some ('b"01" : mword 2, s)).
  { unfold privLevel_to_CSR_privbits.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_H_false s)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hp). rewrite exec_returnM.
  replace (zopz0zKzJ_u ('b"01" : mword 2) (csrPriv csr_sstatus)) with true
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma exec_check_CSR_sstatus_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR csr_sstatus Supervisor CSRReadWrite) s = Some (true, s).
Proof.
  intro HS. unfold check_CSR.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_check_CSR_priv_sstatus_S s)). cbn match.
  assert (HA : exec (returnM (check_CSR_access csr_sstatus CSRReadWrite) : M bool) s
               = Some (true, s)).
  { rewrite exec_returnM.
    replace (check_CSR_access csr_sstatus CSRReadWrite) with true by (vm_compute; reflexivity).
    reflexivity. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ HA). cbn match.
  assert (Hacc : exec (is_CSR_accessible csr_sstatus Supervisor CSRReadWrite) s = Some (true, s)).
  { unfold is_CSR_accessible. skip_csr_false_clauses.
    replace (eq_vec csr_sstatus (Ox"100")) with true by (vm_compute; reflexivity). cbn match.
    rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hacc). cbn match.
  unfold stateen_allows_CSR_access. cbn match. skip_csr_false_clauses.
  apply exec_returnM.
Qed.

Lemma exec_check_CSR_result_sstatus_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_sstatus Supervisor CSRReadWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS. unfold check_CSR_result.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_sstatus_S s HS)). cbn match.
  apply exec_returnM.
Qed.

(* ---- read_CSR / legalize / write_CSR for sstatus ---- *)
Lemma exec_read_CSR_sstatus s :
  exec (read_CSR csr_sstatus) s
    = Some (sstatus_read (register_lookup mstatus s.(sregs)), s).
Proof.
  unfold read_CSR. skip_csr_false_clauses.
  replace (eq_vec csr_sstatus (Ox"100")) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  unfold sstatus_read. apply exec_returnM.
Qed.

Lemma exec_legalize_sstatus (m v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (legalize_sstatus m v) s = Some (legalize_sstatus_val m v, s).
Proof.
  intros HS HU. unfold legalize_sstatus, legalize_sstatus_val.
  apply (exec_legalize_mstatus m (lift_sstatus m (Mk_Sstatus (zero_extend' 64 v))) s HS HU).
Qed.

Lemma exec_write_CSR_sstatus (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (write_CSR csr_sstatus v) s
    = Some (Ok (subrange_vec_dec
                  (lower_mstatus (legalize_sstatus_val (register_lookup mstatus s.(sregs)) v))
                  (Z.sub xlen 1) 0),
            set_reg s mstatus (legalize_sstatus_val (register_lookup mstatus s.(sregs)) v)).
Proof.
  intros HS HU. unfold write_CSR. skip_csr_false_clauses.
  replace (eq_vec csr_sstatus (Ox"100")) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_legalize_sstatus (register_lookup mstatus s.(sregs)) v s HS HU)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_sstatus (d : mword 64) s :
  exec (csr_id_write_callback csr_sstatus d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_sstatus d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

(* ---- the full csrrci-on-sstatus execute, with SIE-idempotence collapse ---- *)
Lemma exec_execute_csrrci_sstatus (imm5 rd : mword 5) (m : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec imm5 (zeros' 5) = false ->
  uint rd <> 0 ->
  legalize_sstatus_val m (sstatus_write_val m imm5) = m ->
  exec (execute (CSRImm (csr_sstatus, imm5, Regidx rd, CSRRC))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sstatus_read m))).
Proof.
  intros Hpriv Hm HS HU Himm Hrd Hcollapse.
  change (execute (CSRImm (csr_sstatus, imm5, Regidx rd, CSRRC)))
    with (execute_CSRImm csr_sstatus imm5 (Regidx rd) CSRRC).
  unfold execute_CSRImm.
  rewrite Himm.
  (* access_type = CSRReadWrite *)
  cbn match.
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_result_sstatus_S s HS)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  unfold ext_check_CSR. cbn match.
  replace (generic_neq CSRReadWrite CSRWrite) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_sstatus s)). rewrite Hm.
  replace (eq_vec csr_sstatus (Ox"344")) with false by (vm_compute; reflexivity).
  replace (eq_vec csr_sstatus (Ox"144")) with false by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (sstatus_read m) s)).
  replace (generic_eq CSRReadWrite CSRRead) with false by (vm_compute; reflexivity). cbn match.
  (* write path: write_val = and_vec read_val (not_vec (zext imm5)) = sstatus_write_val m imm5 *)
  assert (Hid : set_reg s mstatus m = s).
  { unfold set_reg. rewrite <- Hm.
    rewrite (register_set_bv64_id mstatus s.(sregs)).
    destruct s; reflexivity. }
  assert (Hwrite : exec (write_CSR csr_sstatus (sstatus_write_val m imm5)) s
                   = Some (Ok (subrange_vec_dec (lower_mstatus m) (Z.sub xlen 1) 0), s)).
  { rewrite (exec_write_CSR_sstatus (sstatus_write_val m imm5) s HS HU).
    rewrite Hm. rewrite Hcollapse. rewrite Hid. reflexivity. }
  change (and_vec (sstatus_read m) (not_vec (zero_extend' 64 imm5)))
    with (sstatus_write_val m imm5).
  rewrite (exec_bind_Some _ _ _ _ _ Hwrite). cbn beta match.
  (* [>>] is left-associative: (wX >> callback) >> returnM.  Peel inner first. *)
  assert (Hwc : exec (wX_bits (Regidx rd) (sstatus_read m) >>
                      csr_id_write_callback csr_sstatus
                        (subrange_vec_dec (lower_mstatus m) (Z.sub xlen 1) 0)) s
                = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sstatus_read m)))).
  { rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd (sstatus_read m) s)).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    apply (exec_csr_id_write_callback_sstatus
             (subrange_vec_dec (lower_mstatus m) (Z.sub xlen 1) 0) _). }
  rewrite (exec_bind0_Some _ _ _ _ _ Hwc).
  apply exec_returnM.
Qed.



Section WpPushOffCsr.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ---- csrrci rd,sstatus,imm5 at Supervisor, SIE already 0 (idempotent) ----
     4-byte instruction: PC advances +4; needs fetch geom at pc and pc+2.
     mstatus is UNCHANGED (the [Hcollapse] premise witnesses that legalizing the
     read-back S-status onto mstatus0 gives mstatus0 -- true because clearing an
     already-0 SIE is a no-op, so the write puts back exactly the S-bits read). *)

  (* [smode_config] view of the sstatus SIE-clear read (csrrci rd,sstatus,2):
     [mstatus] is PRESERVED -- the SIE-clear collapses because SIE=0, which is
     exactly the [legalize] fact the bundle already carries -- so the config
     round-trips through the bundle.  The value read into [rd] is exposed only
     through the ghost SIE flag: [sstatus_read ms] for SOME [ms] with SIE=0.
     The kernel reads/writes sstatus only to inspect/clear SIE, so that is all
     a caller ever needs (e.g. [po_storeval32_zero] uses only SIE=0). *)

End WpPushOffCsr.
