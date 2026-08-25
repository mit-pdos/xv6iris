From Stdlib Require Import ZArith FunctionalExtensionality.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec WpDecode ExecCommon WpGpr RegFile.
Require Import InstrBytes.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
Require Import HartSwp HartLift HartSpan HartSpanChar HartMCycle
        HartMFrame HartGoodb WpDecodeBridge WpMmodeJump WpMmodeCsrSwp.
Local Open Scope Z_scope.
Require Import WpGprCsrwCommon.
Require Import TsoCtx.

Definition csr_mcounteren : mword 12 := mword_of_int 0x306.

Lemma exec_write_CSR_mcounteren (v : mword 64) s :
  exec (write_CSR csr_mcounteren v) s
    = Some (Ok (zero_extend' 64 (legalize_mcounteren (register_lookup mcounteren s.(sregs)) v)),
            set_reg s mcounteren (legalize_mcounteren (register_lookup mcounteren s.(sregs)) v)).
Proof.
  unfold write_CSR.
  skip_csr_false_clauses.
  (* reached the 0x306 clause *)
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mcounteren _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_mcounteren (d : mword 64) s :
  exec (csr_id_write_callback csr_mcounteren d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_mcounteren d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_mcounteren (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (check_CSR_result csr_mcounteren Machine CSRWrite) s = Some (CSR_Check_OK tt, s) ->
  exec (execute_CSRReg csr_mcounteren (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s mcounteren
              (legalize_mcounteren (register_lookup mcounteren s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv Hchk.
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr csr_mcounteren rs1 s _
           (zero_extend' 64 (legalize_mcounteren (register_lookup mcounteren s.(sregs))
              (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))).
  - exact Hpriv.
  - exact Hchk.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_mcounteren.
  - apply exec_csr_id_write_callback_mcounteren.
Qed.

(* ---- medeleg 0x302 (Ext_S, pure legalize) end-to-end execute ---- *)
Definition csr_medeleg : mword 12 := mword_of_int 0x302.

Lemma exec_write_CSR_medeleg (v : mword 64) s :
  exec (write_CSR csr_medeleg v) s
    = Some (Ok (legalize_medeleg (register_lookup medeleg s.(sregs)) v),
            set_reg s medeleg (legalize_medeleg (register_lookup medeleg s.(sregs)) v)).
Proof.
  unfold write_CSR.
  skip_csr_false_clauses.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg medeleg s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg medeleg _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg medeleg _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

(* the [hfrun] twin of [exec_write_CSR_medeleg]: [write_CSR] at a CONCRETE csr
   is three nodes at that one register, so the walker takes it.  This is the
   only per-CSR work the swp route needs -- the legality check is
   goodb-transported and the callback is a pure equation. *)
Lemma hfrun_write_CSR_medeleg (D Drw : gset register) (rs : regstate)
    (v : mword 64) :
  (medeleg : register) ∈ D -> (medeleg : register) ∈ Drw ->
  hfrun 8 D Drw rs (write_CSR csr_medeleg v)
  = Some (Values.Ok (legalize_medeleg (register_lookup medeleg rs) v),
          register_set medeleg
            (legalize_medeleg (register_lookup medeleg rs) v) rs).
Proof.
  intros HD HW. unfold write_CSR. skip_csr_false_clauses.
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.write_reg Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.write_reg Defs.read_reg Defs.returnm returnM].
  rewrite hfrun_write (bool_decide_eq_true_2 _ HW).
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  rewrite register_lookup_set.
  apply hfrun_ret.
Qed.

Lemma hfrun_write_CSR_mcounteren (D Drw : gset register) (rs : regstate)
    (v : mword 64) :
  (mcounteren : register) ∈ D -> (mcounteren : register) ∈ Drw ->
  hfrun 8 D Drw rs (write_CSR csr_mcounteren v)
  = Some (Values.Ok (zero_extend' 64
                       (legalize_mcounteren (register_lookup mcounteren rs) v)),
          register_set mcounteren
            (legalize_mcounteren (register_lookup mcounteren rs) v) rs).
Proof.
  intros HD HW. unfold write_CSR. skip_csr_false_clauses.
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.write_reg Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.write_reg Defs.read_reg Defs.returnm returnM].
  rewrite hfrun_write (bool_decide_eq_true_2 _ HW).
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  rewrite register_lookup_set.
  apply hfrun_ret.
Qed.

Lemma exec_csr_id_write_callback_medeleg (d : mword 64) s :
  exec (csr_id_write_callback csr_medeleg d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_medeleg d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_medeleg (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_medeleg (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s medeleg
              (legalize_medeleg (register_lookup medeleg s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HS.
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr csr_medeleg rs1 s _
           (legalize_medeleg (register_lookup medeleg s.(sregs))
              ((if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))).
  
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_S csr_medeleg s HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | csr_dispatch_eq | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_medeleg.
  - apply exec_csr_id_write_callback_medeleg.
Qed.

(* discharge mcounteren's check_CSR via Ext_U for a fully-closed execute *)
Lemma exec_execute_csrw_mcounteren_full (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_mcounteren (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s mcounteren
              (legalize_mcounteren (register_lookup mcounteren s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HU. apply exec_execute_csrw_mcounteren; try assumption.
  apply (exec_check_CSR_result_csrw_U csr_mcounteren s HU);
    [ vm_compute; reflexivity | vm_compute; reflexivity | csr_dispatch_eq | vm_compute; reflexivity ].
Qed.

(* ---- forward_exec for csrw medeleg (exec riscv_step, generic rs1) ---- *)

(* ---- clean-form post-state for csrw medeleg (for the Iris WP layer) ---- *)


(* Demonstration: ONE engine serves many CSRs/source regs. *)

(* ====================================================================== *)
(* mcounteren (0x306, Ext_U, legalize_mcounteren) — full forward + wp.      *)
(* Reuses the CSR-agnostic sAcw/s_pccw/gpr_s_pccw from the medeleg block.   *)
(* ====================================================================== *)


(* ====================================================================== *)
(* mepc (0x341, _pure check, set_xepc → update_vec_dec v 0 := 'b0).         *)
(* ====================================================================== *)
Definition csr_mepc : mword 12 := mword_of_int 0x341.
Definition mepc_val (v : mword 64) : mword 64 := update_vec_dec v 0 ('b"0").

Lemma exec_legalize_xepc (v : mword 64) s :
  exec (legalize_xepc v) s = Some (mepc_val v, s).
Proof.
  unfold legalize_xepc, mepc_val.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_hartSupports_Zca s)).
  apply exec_returnM.
Qed.

(* [legalize_xepc] reads NO register ([hartSupports] is a platform constant),
   so mepc's whole write is one node and [hfrun] walks it -- no certificate
   needed, unlike menvcfg's. *)
Lemma hfrun_write_CSR_mepc (D Drw : gset register) (rs : regstate)
    (v : mword 64) :
  (mepc : register) ∈ Drw ->
  hfrun 8 D Drw rs (write_CSR csr_mepc v)
  = Some (Values.Ok (mepc_val v), register_set mepc (mepc_val v) rs).
Proof.
  intros HW. unfold write_CSR. skip_csr_false_clauses.
  unfold set_xepc, legalize_xepc, mepc_val, hartSupports.
  destruct (Defs.Zwf_guarded _).
  cbn beta iota zeta delta [_rec_hartSupports Defs.assert_exp' Defs.bind
    Defs.bind0 Interface.iMon_bind Defs.write_reg Defs.returnm returnM].
  rewrite hfrun_write (bool_decide_eq_true_2 _ HW).
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.returnm returnM].
  apply hfrun_ret.
Qed.

Lemma exec_write_CSR_mepc (v : mword 64) s :
  exec (write_CSR csr_mepc v) s = Some (Ok (mepc_val v), set_reg s mepc (mepc_val v)).
Proof.
  unfold write_CSR.
  skip_csr_false_clauses.
  assert (Hsx : exec (set_xepc Machine v) s = Some (mepc_val v, set_reg s mepc (mepc_val v))).
  { unfold set_xepc.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_legalize_xepc v s)). cbn match.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mepc (mepc_val v) s)).
    apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hsx).
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_mepc (d : mword 64) s :
  exec (csr_id_write_callback csr_mepc d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_mepc d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_mepc (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_mepc (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s mepc (mepc_val (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv.
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr csr_mepc rs1 s _
           (mepc_val ((if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))).
  
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_pure csr_mepc s);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_mepc.
  - apply exec_csr_id_write_callback_mepc.
Qed.


(* ===== mscratch (0x340): pure direct write, _pure check ===== *)

Lemma exec_hartSupports_Sv32 s : exec (hartSupports Ext_Sv32) s = Some (false, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sv32) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  replace (andb false (Z.eqb xlen 32)) with false by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_virtual_memory_supported s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (virtual_memory_supported tt) s = Some (true, s).
Proof.
  intro HS. unfold virtual_memory_supported. destruct (Defs.Zwf_guarded _).
  cbn [_rec_virtual_memory_supported]. unfold Defs.assert_exp'.
  replace (Z.geb 3 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  (* or_boolM (rec cE Sv32 2) (...) : reduce Sv32 -> false inline *)
  match goal with |- context[_rec_currentlyEnabled Ext_Sv32 ?k ?a] =>
    assert (H32 : exec (_rec_currentlyEnabled Ext_Sv32 k a) s = Some (false, s)) end.
  { match goal with |- exec (_rec_currentlyEnabled Ext_Sv32 ?k ?a) s = _ => destruct a end.
    cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
    replace (Z.geb (Z.sub 3 1) 0) with true by reflexivity. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sv32 s)). reflexivity. }
  rewrite (exec_or_boolM_Some _ _ _ _ _ H32). cbn match.
  (* or_boolM (rec cE Sv39 2) (...) : reduce Sv39 -> true inline *)
  match goal with |- context[_rec_currentlyEnabled Ext_Sv39 ?k ?a] =>
    assert (H39 : exec (_rec_currentlyEnabled Ext_Sv39 k a) s = Some (true, s)) end.
  { match goal with |- exec (_rec_currentlyEnabled Ext_Sv39 ?k ?a) s = _ => destruct a end.
    cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
    replace (Z.geb (Z.sub 3 1) 0) with true by reflexivity. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sv39 s)). cbn match.
    (* rec cE S at reclimit 1 inline *)
    match goal with |- context[_rec_currentlyEnabled Ext_S ?k ?a] =>
      assert (HSm : exec (_rec_currentlyEnabled Ext_S k a) s
                    = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"), s)) end.
    { match goal with |- exec (_rec_currentlyEnabled Ext_S ?k ?a) s = _ => destruct a end.
      cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
      replace (Z.geb (Z.sub (Z.sub 3 1) 1) 0) with true by reflexivity. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_S s)). cbn match.
      rewrite (exec_and_boolM_Some _ _ s
                 (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s).
      2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM. }
      destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:Hb.
      - match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k2 ?a2] =>
          exact (exec_rec_cE_Zicsr_any k2 a2 s ltac:(reflexivity)) end.
      - reflexivity. }
    rewrite HSm. rewrite HS. reflexivity. }
  rewrite (exec_or_boolM_Some _ _ _ _ _ H39). reflexivity.
Qed.

Lemma exec_lowest_supported_privLevel s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (lowest_supported_privLevel tt) s = Some (User, s).
Proof.
  intro HU. unfold lowest_supported_privLevel.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_U s HU)). cbn match.
  apply exec_returnM.
Qed.

Lemma exec_have_nominal_privLevel (priv : mword 2) s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (have_nominal_privLevel priv) s = Some (have_nom_val priv, s).
Proof.
  intros HU HS. unfold have_nominal_privLevel, have_nom_val.
  destruct (eq_vec priv ('b"00")) eqn:E0.
  - exact (exec_currentlyEnabled_U s HU).
  - destruct (eq_vec priv ('b"01")) eqn:E1.
    + rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity.
    + apply exec_returnM.
Qed.

Lemma exec_legalize_mstatus (o v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (legalize_mstatus o v) s = Some (mstatus_legalized o v, s).
Proof.
  intros HS HU. unfold legalize_mstatus, mstatus_legalized.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_hartSupports_Zicfilp s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_hartSupports_Zicfilp s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_U s HU)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_virtual_memory_supported s HS)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_U s HU)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_have_nominal_privLevel (_get_Mstatus_MPP (Mk_Mstatus v)) s HU HS)).
  match goal with |- exec (Defs.bind ?IF _) s = _ =>
    assert (Hw18 : exec IF s
                   = Some (if have_nom_val (_get_Mstatus_MPP (Mk_Mstatus v))
                           then _get_Mstatus_MPP (Mk_Mstatus v) else privLevel_to_bits User, s)) end.
  { destruct (have_nom_val (_get_Mstatus_MPP (Mk_Mstatus v))).
    - cbn match. apply exec_returnM.
    - cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_lowest_supported_privLevel s HU)).
      apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hw18). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  apply exec_returnM.
Qed.

Definition csr_mstatus : mword 12 := mword_of_int 0x300.

Lemma exec_write_CSR_mstatus (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (write_CSR csr_mstatus v) s
    = Some (Ok (mstatus_legalized (register_lookup mstatus s.(sregs)) v),
            set_reg s mstatus (mstatus_legalized (register_lookup mstatus s.(sregs)) v)).
Proof.
  intros HS HU. unfold write_CSR.
  skip_csr_false_clauses.
  (* reached the xlen=64 0x300 clause; expose its body *)
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_legalize_mstatus (register_lookup mstatus s.(sregs)) v s HS HU)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_mstatus (d : mword 64) s :
  exec (csr_id_write_callback csr_mstatus d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_mstatus d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_mstatus (rs1 : mword 5) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_mstatus (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s mstatus
              (mstatus_legalized (register_lookup mstatus s.(sregs))
                 (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hpriv HS HU.
  apply (exec_execute_csrw_gpr csr_mstatus rs1 s _
           (mstatus_legalized (register_lookup mstatus s.(sregs))
              (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_pure csr_mstatus s);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_mstatus; assumption.
  - apply exec_csr_id_write_callback_mstatus.
Qed.

(* ====================================================================== *)
(* mstatus (0x300, _pure check, MONADIC legalize_mstatus). WRITTEN mstatus  *)
(* = R_bitvector_64 mstatus MIE frame -> own once (pre MIE=false). mideleg  *)
(* stays a separate pending frame. legalize needs misa.S AND misa.U.        *)
(* ====================================================================== *)

(* ===================================================================== *)
(* pmpcfg0 (0x3a0): pmpWriteCfgReg foreach_ZM_up loop (8 iters, state-      *)
(* threading) writing one pmpcfg_n byte each. pmpWriteCfg is total         *)
(* (PMP_ClearPermissions). Keep results symbolic.                          *)
(* ===================================================================== *)
Definition pmpWriteCfg_val (cfg v : mword 8) : mword 8 :=
  if pmpLocked cfg then cfg
  else
    let c := Mk_Pmpcfg_ent (and_vec v (Ox"9F")) in
    let c := if andb (eq_vec (_get_Pmpcfg_ent_W c) ('b"1")) (eq_vec (_get_Pmpcfg_ent_R c) ('b"0"))
             then _update_Pmpcfg_ent_R
                    (_update_Pmpcfg_ent_W (_update_Pmpcfg_ent_X c ('b"0")) ('b"0")) ('b"0")
             else c in
    if (match pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A c) with
        | OFF => true | TOR => true
        | NA4 => andb true (Z.eqb sys_pmp_grain 0) | NAPOT => true end)
    then c else _update_Pmpcfg_ent_A c (pmpAddrMatchType_encdec_forwards OFF).

Lemma exec_pmpWriteCfg (cfg v : mword 8) s :
  exec (pmpWriteCfg cfg v) s = Some (pmpWriteCfg_val cfg v, s).
Proof.
  unfold pmpWriteCfg, pmpWriteCfg_val.
  destruct (pmpLocked cfg).
  - apply exec_returnM.
  - destruct (andb (eq_vec (_get_Pmpcfg_ent_W (Mk_Pmpcfg_ent (and_vec v (Ox"9F")))) ('b"1"))
                   (eq_vec (_get_Pmpcfg_ent_R (Mk_Pmpcfg_ent (and_vec v (Ox"9F")))) ('b"0"))).
    + rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). apply exec_returnM.
    + rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). apply exec_returnM.
Qed.

Definition pmp_cfg_step (v : mword 64) (s : mstate) (i : Z) : mstate :=
  set_reg s pmpcfg_n
    (vec_update_dec (register_lookup pmpcfg_n s.(sregs)) (Z.add (Z.mul 0 4) i)
       (pmpWriteCfg_val
          (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) (Z.add (Z.mul 0 4) i))
          (autocast (T := mword) (subrange_vec_dec v (Z.add (Z.mul 8 i) 7) (Z.mul 8 i))))).

Definition pmpcfg0_final (v : mword 64) (s : mstate) : mstate :=
  pmp_cfg_step v (pmp_cfg_step v (pmp_cfg_step v (pmp_cfg_step v
    (pmp_cfg_step v (pmp_cfg_step v (pmp_cfg_step v (pmp_cfg_step v s 0) 1) 2) 3) 4) 5) 6) 7.

Ltac do_cfg_step vv ii :=
  rewrite Defs.unroll_foreach_ZM_up'; [ | lia ];
  match goal with
  | |- exec (Defs.bind ?body0 _) ?si = _ =>
    let Hb := fresh "Hb" in
    assert (Hb : exec body0 si = Some (tt, pmp_cfg_step vv si ii));
    [ replace (Z.ltb (Z.add (Z.mul 0 4) ii) sys_pmp_usable_count) with true by (vm_compute; reflexivity);
      cbn match;
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n si));
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n si));
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpWriteCfg _ _ si));
      unfold pmp_cfg_step; apply exec_write_reg
    | rewrite (exec_bind_Some _ _ _ _ _ Hb) ]
  end.

Lemma exec_pmpWriteCfgReg_0 (v : mword 64) s :
  exec (pmpWriteCfgReg 0 v) s = Some (tt, pmpcfg0_final v s).
Proof.
  unfold pmpWriteCfgReg, Defs.assert_exp'.
  replace (Z.eqb (Z.rem 0 2) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  unfold Defs.foreach_ZM_up.
  do_cfg_step v 0. do_cfg_step v 1. do_cfg_step v 2. do_cfg_step v 3.
  do_cfg_step v 4. do_cfg_step v 5. do_cfg_step v 6. do_cfg_step v 7.
  cbn [Defs.foreach_ZM_up']. apply exec_returnM.
Qed.

Definition csr_pmpcfg0 : mword 12 := mword_of_int 0x3a0.

Definition pmpcfg0_readback (cfg : vec (mword 8) 64) : mword 64 :=
  concat_vec (vec_access_dec cfg (Z.add (Z.mul 0 4) 7))
   (concat_vec (vec_access_dec cfg (Z.add (Z.mul 0 4) 6))
    (concat_vec (vec_access_dec cfg (Z.add (Z.mul 0 4) 5))
     (concat_vec (vec_access_dec cfg (Z.add (Z.mul 0 4) 4))
      (concat_vec (vec_access_dec cfg (Z.add (Z.mul 0 4) 3))
       (concat_vec (vec_access_dec cfg (Z.add (Z.mul 0 4) 2))
        (concat_vec (vec_access_dec cfg (Z.add (Z.mul 0 4) 1))
         (vec_access_dec cfg (Z.add (Z.mul 0 4) 0)))))))).

Lemma exec_pmpReadCfgReg_0 s :
  exec (pmpReadCfgReg 0) s = Some (pmpcfg0_readback (register_lookup pmpcfg_n s.(sregs)), s).
Proof.
  unfold pmpReadCfgReg, Defs.assert_exp'.
  replace (Z.eqb (Z.rem 0 2) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  apply exec_returnM.
Qed.


Lemma exec_write_CSR_pmpcfg0 (v : mword 64) s :
  exec (write_CSR csr_pmpcfg0 v) s
    = Some (Ok (pmpcfg0_readback (register_lookup pmpcfg_n (pmpcfg0_final v s).(sregs))),
            pmpcfg0_final v s).
Proof.
  unfold write_CSR.
  skip_csr_false_clauses.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  cbn zeta.
  assert (Hidx : uint (subrange_vec_dec csr_pmpcfg0 3 0) = 0) by (vm_compute; reflexivity).
  rewrite !Hidx.
  assert (Hwr : exec (Defs.bind0 (pmpWriteCfgReg 0 v) (pmpReadCfgReg 0)) s
                = Some (pmpcfg0_readback (register_lookup pmpcfg_n (pmpcfg0_final v s).(sregs)),
                        pmpcfg0_final v s)).
  { rewrite (exec_bind0_Some _ _ _ _ _ (exec_pmpWriteCfgReg_0 v s)).
    exact (exec_pmpReadCfgReg_0 (pmpcfg0_final v s)). }
  rewrite (exec_bind_Some _ _ _ _ _ Hwr). apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_pmpcfg0 (d : mword 64) s :
  exec (csr_id_write_callback csr_pmpcfg0 d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_pmpcfg0 d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_pmpcfg0 (rs1 : mword 5) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_pmpcfg0 (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            pmpcfg0_final (if Z.eqb (uint rs1) 0 then zero_reg
                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) s).
Proof.
  intros Hpriv.
  apply (exec_execute_csrw_gpr csr_pmpcfg0 rs1 s _
           (pmpcfg0_readback (register_lookup pmpcfg_n
              (pmpcfg0_final (if Z.eqb (uint rs1) 0 then zero_reg
                              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) s).(sregs)))).
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_pure csr_pmpcfg0 s);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_pmpcfg0.
  - apply exec_csr_id_write_callback_pmpcfg0.
Qed.

(* ---- collapse the 8 nested set_reg pmpcfg_n into a single set_reg ---- *)
Lemma register_set_pmpcfg_n_overwrite (a b : type_of_register pmpcfg_n) (regs : regstate) :
  register_set pmpcfg_n b (register_set pmpcfg_n a regs) = register_set pmpcfg_n b regs.
Proof.
  destruct regs. unfold register_set. cbn.
  f_equal. apply functional_extensionality; intro x.
  destruct (register_vector_64_bitvector_8_beq x pmpcfg_n); reflexivity.
Qed.

Lemma set_reg_pmpcfg_n_overwrite (a b : type_of_register pmpcfg_n) (s : mstate) :
  set_reg (set_reg s pmpcfg_n a) pmpcfg_n b = set_reg s pmpcfg_n b.
Proof. unfold set_reg; cbn [sregs mem]. f_equal. apply register_set_pmpcfg_n_overwrite. Qed.

Definition pmpcfg0_vecupd (v : mword 64) (cfg : vec (mword 8) 64) (i : Z) : vec (mword 8) 64 :=
  vec_update_dec cfg (Z.add (Z.mul 0 4) i)
    (pmpWriteCfg_val (vec_access_dec cfg (Z.add (Z.mul 0 4) i))
       (autocast (T := mword) (subrange_vec_dec v (Z.add (Z.mul 8 i) 7) (Z.mul 8 i)))).


Lemma pmp_cfg_step_on_set (v : mword 64) (s : mstate) (X : vec (mword 8) 64) (i : Z) :
  pmp_cfg_step v (set_reg s pmpcfg_n X) i = set_reg s pmpcfg_n (pmpcfg0_vecupd v X i).
Proof.
  unfold pmp_cfg_step, pmpcfg0_vecupd.
  rewrite !register_lookup_set. rewrite set_reg_pmpcfg_n_overwrite. reflexivity.
Qed.


(* ---- pmpcfg0 forward/clean/wp: writes vec pmpcfg_n (= fetch frame) ---- *)


Lemma exec_hartSupports_Zicfiss s : exec (hartSupports Ext_Zicfiss) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicfiss) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zicboz s : exec (hartSupports Ext_Zicboz) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicboz) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zicbom s : exec (hartSupports Ext_Zicbom) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicbom) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_hartSupports_Smnpm s : exec (hartSupports Ext_Smnpm) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Smnpm) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  (* andb true (xlen==64) *)
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_hartSupports_Svadu s : exec (hartSupports Ext_Svadu) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Svadu) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_hartSupports_Svpbmt s : exec (hartSupports Ext_Svpbmt) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Svpbmt) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

(* currentlyEnabled for the simple extensions (body = hartSupports X) *)
Lemma exec_currentlyEnabled_Zicboz s : exec (currentlyEnabled Ext_Zicboz) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicboz) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Zicboz.
Qed.

Lemma exec_currentlyEnabled_Zicbom s : exec (currentlyEnabled Ext_Zicbom) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicbom) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Zicbom.
Qed.

Lemma exec_currentlyEnabled_Smnpm s : exec (currentlyEnabled Ext_Smnpm) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Smnpm) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Smnpm.
Qed.

Lemma exec_currentlyEnabled_Svadu s : exec (currentlyEnabled Ext_Svadu) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Svadu) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Svadu.
Qed.

(* reduce an inner `_rec_currentlyEnabled Ext_S k a` (concrete k) to misa.S
   (same as crush_rec_cE_S in WpGprCsrw, replicated here for the probe) *)
Ltac crush_inner_cE_S s :=
  match goal with |- context[_rec_currentlyEnabled Ext_S ?k ?a] =>
    let H := fresh "HSm" in
    assert (H : exec (_rec_currentlyEnabled Ext_S k a) s
                = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"), s));
    [ destruct a; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
      match goal with |- context[Z.geb ?kk 0] => replace (Z.geb kk 0) with true by reflexivity end;
      cbn match; rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)); cbn match;
      rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_S s)); cbn match;
      rewrite (exec_and_boolM_Some _ _ s
                 (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s);
      [ destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:?;
        [ match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k2 ?a2] =>
            exact (exec_rec_cE_Zicsr_any k2 a2 s ltac:(reflexivity)) end
        | reflexivity ]
      | rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)); apply exec_returnM ]
    | rewrite H ]
  end.

Lemma exec_currentlyEnabled_Svpbmt s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_Svpbmt) s = Some (true, s).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Svpbmt) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Svpbmt s)). cbn match.
  (* inner rec cE Sv39 at concrete reclimit *)
  match goal with |- context[_rec_currentlyEnabled Ext_Sv39 ?k ?a] =>
    destruct a end.
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  match goal with |- context[Z.geb ?kk 0] => replace (Z.geb kk 0) with true by reflexivity end.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sv39 s)). cbn match.
  crush_inner_cE_S s. rewrite HS. reflexivity.
Qed.

(* ===================================================================== *)
(* menvcfg (0x30A): legalize_menvcfg via the extension tower above       *)
(* ===================================================================== *)
Definition csr_menvcfg : mword 12 := mword_of_int 0x30a.

(* symbolic cbie legalization (pure: neq_vec test) *)
Definition menvcfg_cbie (v : mword 64) : mword 2 :=
  if neq_vec (_get_MEnvcfg_CBIE (Mk_MEnvcfg v)) ('b"10")
  then _get_MEnvcfg_CBIE (Mk_MEnvcfg v)
  else ('b"00").

Lemma exec_legalize_xenvcfg_cbie (cbie : mword 2) s :
  exec (legalize_xenvcfg_cbie cbie) s
    = Some (if neq_vec cbie ('b"10") then cbie else ('b"00"), s).
Proof.
  unfold legalize_xenvcfg_cbie.
  destruct (neq_vec cbie ('b"10")).
  - apply exec_returnM.
  - (* xenvcfg_cbie_reserved_behavior = Xenvcfg_ClearPermissions -> returnM 00 *)
    cbn match. apply exec_returnM.
Qed.

(* symbolic legalized menvcfg: all enabled extensions -> use v's field;
   STCE/PMM/ADUE/PBMTE per the legalize result. *)
Definition menvcfg_legalized (o v : mword 64) : mword 64 :=
  let v' := Mk_MEnvcfg v in
  _update_MEnvcfg_PBMTE
    (_update_MEnvcfg_ADUE
       (_update_MEnvcfg_PMM
          (_update_MEnvcfg_STCE
             (_update_MEnvcfg_CBIE
                (_update_MEnvcfg_CBCFE
                   (_update_MEnvcfg_CBZE
                      (_update_MEnvcfg_SSE
                         (_update_MEnvcfg_LPE
                            (_update_MEnvcfg_FIOM o
                               (if sys_enable_writable_fiom then _get_MEnvcfg_FIOM v' else ('b"0")))
                            (_get_MEnvcfg_LPE v'))
                         (_get_MEnvcfg_SSE v'))
                      (_get_MEnvcfg_CBZE v'))
                   (_get_MEnvcfg_CBCFE v'))
                (menvcfg_cbie v))
             (_get_MEnvcfg_STCE v'))
          (if andb true (is_supported_pmm PM_SMNPM (pmm_mode_backwards (_get_MEnvcfg_PMM v')))
           then _get_MEnvcfg_PMM v' else _get_MEnvcfg_PMM o))
       (_get_MEnvcfg_ADUE v'))
    (_get_MEnvcfg_PBMTE v').

Lemma exec_legalize_menvcfg (o v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (legalize_menvcfg o v) s = Some (menvcfg_legalized o v, s).
Proof.
  intro HS. unfold legalize_menvcfg, menvcfg_legalized, menvcfg_cbie.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_hartSupports_Zicfilp s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_hartSupports_Zicfiss s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Zicboz s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Zicbom s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Zicbom s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_legalize_xenvcfg_cbie (_get_MEnvcfg_CBIE (Mk_MEnvcfg v)) s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Sstc s)). cbn match.
  (* and_boolM (cE Smnpm) (returnM (is_supported_pmm ...)) *)
  match goal with |- context[Defs.and_boolM ?l ?r] =>
    assert (Hsm : exec (Defs.and_boolM l r) s
                  = Some (andb true (is_supported_pmm PM_SMNPM (pmm_mode_backwards (_get_MEnvcfg_PMM (Mk_MEnvcfg v)))), s)) end.
  { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Smnpm s)). cbn match.
    apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hsm). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svadu s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svpbmt s HS)). cbn match.
  apply exec_returnM.
Qed.

(* ====================================================================== *)
(* THE menvcfg WRITE.  Three separate obstacles, each with its own answer.  *)
(*                                                                        *)
(* (1) [write_CSR]'s ~90-way dispatch must be pruned in a PURE goal.  Doing *)
(*     it inside a [swp] goal meets the whole [envs_entails]: 23 GB, OOM at *)
(*     8 minutes.  Here it is milliseconds.                                 *)
(* (2) The surviving clause is READ OFF the pruned goal, not transcribed    *)
(*     from the model: it associates as [bind (bind0 write read) k].        *)
(* (3) [legalize_menvcfg]'s [goodb] certificate cannot be COMPUTED -- the   *)
(*     term carries symbolic o/v and vm_compute/cbv/lazy all diverge on the *)
(*     bitvector data even though goodb's answer cannot depend on it.  So it *)
(*     is ASSEMBLED along the binds with [WpDecodeBridge.goodb_bind]: every  *)
(*     sub-stretch ([currentlyEnabled X], [hartSupports X]) takes no         *)
(*     argument and IS data-free, and the symbolic value ends up only in a   *)
(*     [Ret], where goodb answers true without looking.                     *)
(* ====================================================================== *)
Ltac goodb_step :=
  first [ erewrite goodb_bind  by (vm_compute; reflexivity)
        | erewrite goodb_bind0 by (vm_compute; reflexivity) ].

(* THE SAME PEEL, APPLIED RATHER THAN REWRITTEN.  [goodb_bind] is an
   equation, so [erewrite] builds an [eq_ind_r] motive over the WHOLE
   remaining monadic tail at every step -- and once a continuation has been
   instantiated with symbolic bitvector data (the legalized CBIE field, in
   [goodb_legalize_menvcfg] below) that tail is large: Ltac profiling puts
   81.5 % of the 17.3 s LOCAL to the [erewrite], against 3 % in its
   [vm_compute] side conditions and 11 % in their [reflexivity].  The intro
   form has the same two side conditions and no motive: the proof term
   becomes a chain of applications, which is why it takes the [Qed] down with
   it.  (Only [goodb_legalize_menvcfg] uses these; the [goodb_step] sites in
   WpSconfCsr / WpGprCsrwC are ~1.4 s and are left alone -- optimization.md,
   "do this per file with a measurement, never as a sweep".) *)
Lemma goodb_bind_i (D : register -> bool) {X Y} (m : M X) (f : X -> M Y)
    (s : mstate) (x : X) :
  goodb D m s = true -> exec m s = Some (x, s) -> goodb D (f x) s = true ->
  goodb D (Defs.bind m f) s = true.
Proof.
  intros H1 H2 H3. rewrite (goodb_bind D m f s x H1 H2). exact H3.
Qed.

Lemma goodb_bind0_i (D : register -> bool) {Y} (m : M unit) (n : M Y)
    (s : mstate) :
  goodb D m s = true -> exec m s = Some (tt, s) -> goodb D n s = true ->
  goodb D (Defs.bind0 m n) s = true.
Proof.
  intros H1 H2 H3. rewrite (goodb_bind0 D m n s H1 H2). exact H3.
Qed.

Ltac goodb_stepi :=
  first [ eapply goodb_bind_i;
            [ vm_compute; reflexivity | vm_compute; reflexivity | ]
        | eapply goodb_bind0_i;
            [ vm_compute; reflexivity | vm_compute; reflexivity | ] ].

Lemma goodb_legalize_xenvcfg_cbie (x : mword 2) :
  goodb D_m (legalize_xenvcfg_cbie x) dstateM = true.
Proof.
  unfold legalize_xenvcfg_cbie.
  destruct (neq_vec x ('b"10")); [reflexivity|]. cbn match. reflexivity.
Qed.

Lemma goodb_legalize_menvcfg (o v : mword 64) :
  goodb D_m (legalize_menvcfg o v) dstateM = true.
Proof.
  unfold legalize_menvcfg.
  repeat goodb_step.
  cbn match.
  erewrite goodb_bind.
  3: apply exec_legalize_xenvcfg_cbie.
  2: apply goodb_legalize_xenvcfg_cbie.
  (* HIDE THE LEGALIZED FIELD BEHIND A VARIABLE BEFORE THE REMAINING BINDS.
     [exec_legalize_xenvcfg_cbie] instantiates the continuation's argument
     with a symbolic if-then-else over bitvector data, and from here on every
     [goodb_step] both copies it (each [erewrite] rebuilds the term) and hands
     it to a [vm_compute] side condition -- the very data this proof exists to
     avoid computing (see (3) in the header).  Opaque, the tail is 18.6 s of
     tactic and 18.0 s of [Qed] cheaper, and nothing below looks at the value:
     [goodb] answers [true] at the [Ret] without reading it. *)
  repeat goodb_stepi.
  reflexivity.
Qed.

Lemma if_false_t {X} (g : bool) (A B : X) : g = false -> (if g then A else B) = B.
Proof. intros ->. reflexivity. Qed.

Lemma write_CSR_menvcfg_red (v : mword 64) :
  write_CSR csr_menvcfg v
  = Defs.bind (Defs.read_reg menvcfg)
      (fun o : mword 64 =>
         Defs.bind (legalize_menvcfg o v)
           (fun c : mword 64 =>
              Defs.bind (Defs.bind0 (Defs.write_reg menvcfg c)
                           (Defs.read_reg menvcfg))
                (fun c2 : mword 64 => returnM (Ok c2)))).
Proof.
  unfold write_CSR.
  repeat (erewrite if_false_t by (vm_compute; reflexivity)).
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end.
  reflexivity.
Qed.

Lemma exec_write_CSR_menvcfg (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (write_CSR csr_menvcfg v) s
    = Some (Ok (menvcfg_legalized (register_lookup menvcfg s.(sregs)) v),
            set_reg s menvcfg (menvcfg_legalized (register_lookup menvcfg s.(sregs)) v)).
Proof.
  intro HS. unfold write_CSR.
  skip_csr_false_clauses.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_legalize_menvcfg (register_lookup menvcfg s.(sregs)) v s HS)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg menvcfg _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_menvcfg (d : mword 64) s :
  exec (csr_id_write_callback csr_menvcfg d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_menvcfg d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.


Lemma exec_execute_csrw_menvcfg (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_menvcfg (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s menvcfg
              (menvcfg_legalized (register_lookup menvcfg s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HS HU.
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr csr_menvcfg rs1 s _
           (menvcfg_legalized (register_lookup menvcfg s.(sregs))
              ((if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))).
  
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_U_and csr_menvcfg xenvcfg_csrs_are_defined s HU);
      [ vm_compute; reflexivity | vm_compute; reflexivity | csr_dispatch_eq
      | vm_compute; reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_menvcfg; assumption.
  - apply exec_csr_id_write_callback_menvcfg.
Qed.

(* ---- menvcfg forward/clean/wp: writes menvcfg; reads misa.S/.U, mstatus.MIE ---- *)

(* ====================================================================== *)
(* NEW-STYLE register-generic CSR-WRITE WPs (csrw csr, rs1 = csrrw x0,csr,rs1) *)
(* on the [instr] / [mmode_config] / [gpr_file] layer, built on [wp_instr]. *)
(* Dual of [wp_csrr_mhartid_gpr]: reads rs1 off the [gpr_file] and WRITES    *)
(* the CSR cell, which is threaded as an extra points-to premise (old value  *)
(* in, new/legalized value out).  Reuses the representation-independent      *)
(* execute helpers [exec_execute_csrw_*] verbatim.  A HALF of [mmode_config] *)
(* is kept to recover cur_privilege = Machine (and, where the execute        *)
(* legalizes with misa.S/misa.U or mstatus.SXL, those facts from hw_config / *)
(* the kept mstatus) at the execute state; the halves are recombined for the *)
(* continuation.                                                             *)
(* ====================================================================== *)



Section WpCsrwGprNewA.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* [legalize_menvcfg] reads ONLY misa, whose value hw_config pins, so it IS
     goodb-transportable -- with the certificate ASSEMBLED above rather than
     computed.  Note the contrast with [write_CSR csr_menvcfg] as a whole,
     which reads MENVCFG: the leaf's own variable.  goodb transport demands a
     reference-PINNED value for every read register, so the enclosing write can
     never go that route however the certificate is generalized -- which is why
     the menvcfg read is peeled at the frame and only the legalization is
     certified. *)
  Lemma hval_legalize_menvcfg (D Drw : gset register) (rs : regstate)
      (o v : mword 64) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup mseccfg rs = mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    hval D Drw rs (legalize_menvcfg o v) (menvcfg_legalized o v) rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm.
    exact (hval_of_goodb D_m D Drw _ dstateM rs (menvcfg_legalized o v)
             (dm_sub D HD1 HD2 HD3)
             (agree_m (MState rs ∅ dev0_state) Hp Hs Hm)
             (goodb_legalize_menvcfg o v)
             (exec_legalize_menvcfg o v dstateM
                ltac:(vm_compute; reflexivity))).
  Qed.

  Lemma swp_write_CSR_menvcfg (dq : dfrac) (menvcfg0 v : mword 64) :
    cw_fresh menvcfg ->
    gen_cert -∗
    (hreg_frame (cw_rs menvcfg menvcfg0) (cw_Drw menvcfg) -∗
     hreg_frame_ro (cw_Df dq) (cw_rs menvcfg menvcfg0) cw_Dro -∗
     swp (write_CSR csr_menvcfg v)
       (fun x => ⌜x = Ok (menvcfg_legalized menvcfg0 v)⌝ ∗
          hreg_frame (cw_rs menvcfg (menvcfg_legalized menvcfg0 v))
            (cw_Drw menvcfg) ∗
          hreg_frame_ro (cw_Df dq)
            (cw_rs menvcfg (menvcfg_legalized menvcfg0 v)) cw_Dro)).
  Proof.
    intros Hfresh. iIntros "#Hcert Hrw Hro".
    rewrite write_CSR_menvcfg_red.
    iApply (swp_bind_use (Defs.read_reg menvcfg) _
              (fun o => ⌜o = menvcfg0⌝ ∗
                 hreg_frame (cw_rs menvcfg menvcfg0) (cw_Drw menvcfg) ∗
                 hreg_frame_ro (cw_Df dq) (cw_rs menvcfg menvcfg0) cw_Dro)%I _
              with "[Hrw Hro] [-]").
    { iApply (swp_mono with "[] [-]");
        [| iApply (swp_read_reg_pinned (cw_Drw menvcfg) cw_Dro (cw_Df dq)
                     (cw_rs menvcfg menvcfg0) menvcfg (cw_disj menvcfg Hfresh)
                     (cw_in_r menvcfg) with "Hcert Hrw Hro") ].
      iIntros (o) "(-> & Hrw & Hro)".
      rewrite (cw_rs_r menvcfg menvcfg0). by iFrame. }
    iIntros (o) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (legalize_menvcfg menvcfg0 v) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_span (cw_Drw menvcfg) cw_Dro (cw_Df dq)
                (cw_rs menvcfg menvcfg0) (cw_rs menvcfg menvcfg0) _ _
                (cw_disj menvcfg Hfresh)
                (hval_legalize_menvcfg (cw_Drw menvcfg ∪ cw_Dro)
                   (cw_Drw menvcfg) (cw_rs menvcfg menvcfg0) menvcfg0 v
                   (cw_in_priv menvcfg) (cw_in_sec menvcfg)
                   (cw_in_misa menvcfg)
                   (cw_rs_priv menvcfg menvcfg0 Hfresh)
                   (cw_rs_sec menvcfg menvcfg0 Hfresh)
                   (cw_rs_misa menvcfg menvcfg0 Hfresh))
                with "Hcert Hrw Hro"). }
    iIntros (c) "(-> & Hrw & Hro)".
    iApply (swp_bind_use _ _
              (fun c2 => ⌜c2 = menvcfg_legalized menvcfg0 v⌝ ∗
                 hreg_frame (cw_rs menvcfg (menvcfg_legalized menvcfg0 v))
                   (cw_Drw menvcfg) ∗
                 hreg_frame_ro (cw_Df dq)
                   (cw_rs menvcfg (menvcfg_legalized menvcfg0 v)) cw_Dro)%I _
              with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => hreg_frame
                   (cw_rs menvcfg (menvcfg_legalized menvcfg0 v))
                   (cw_Drw menvcfg) ∗
                   hreg_frame_ro (cw_Df dq)
                     (cw_rs menvcfg (menvcfg_legalized menvcfg0 v)) cw_Dro)%I _
                with "[Hrw Hro] [-]").
      { iApply (swp_mono with "[] [-]");
          [| iApply (swp_write_reg_owned (cw_Drw menvcfg) cw_Dro (cw_Df dq)
                       (cw_rs menvcfg menvcfg0) menvcfg _
                       (cw_disj menvcfg Hfresh) (cw_w_r menvcfg)
                       with "Hcert Hrw Hro") ].
        iIntros (u) "[Hrw Hro]".
        iDestruct (cw_rw_ext menvcfg _ _
                     (reg_agree_l _ _ _ _
                        (cw_set_agree menvcfg menvcfg0 _ Hfresh)) with "Hrw")
          as "Hrw".
        iDestruct (cw_ro_ext dq _ _
                     (reg_agree_r _ _ _ _
                        (cw_set_agree menvcfg menvcfg0 _ Hfresh)) with "Hro")
          as "Hro".
        by iFrame. }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_mono with "[] [-]");
        [| iApply (swp_read_reg_pinned (cw_Drw menvcfg) cw_Dro (cw_Df dq)
                     (cw_rs menvcfg (menvcfg_legalized menvcfg0 v)) menvcfg
                     (cw_disj menvcfg Hfresh) (cw_in_r menvcfg)
                     with "Hcert Hrw Hro") ].
      iIntros (c2) "(-> & Hrw & Hro)".
      rewrite (cw_rs_r menvcfg (menvcfg_legalized menvcfg0 v)). by iFrame. }
    iIntros (c2) "(-> & Hrw & Hro)".
    iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.
  (* ---- medeleg (Ext_S, pure legalize) ---- *)
  Lemma wp_csrw_medeleg_gpr (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (medeleg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    medeleg ↦ᵣ medeleg0 -∗
    instr pc false (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      medeleg ↦ᵣ legalize_medeleg medeleg0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrs1) "Hmm Hpmpc Hpc Hf Hcsr Hinstr Hcont".
    assert (Hfresh : cw_fresh medeleg)
      by (rewrite /cw_fresh; split_and!; vm_compute; reflexivity).
    assert (Hchk : exec (check_CSR_result csr_medeleg Machine CSRWrite) dstateM
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
              (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW)) m m pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               medeleg ↦ᵣ legalize_medeleg medeleg0 (m !!! Regidx rs1))%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hf Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k Hcsr] [Hcont]").
    - iIntros "Hf HPC HnPC".
      (* the write obligation, stated at the NAMED post-file so nothing after
         it has to convert a [register_set] *)
      iAssert (hreg_frame (cw_rs medeleg medeleg0) (cw_Drw medeleg) -∗
               hreg_frame_ro (cw_Df (DfracOwn (q/2))) (cw_rs medeleg medeleg0)
                 cw_Dro -∗
               swp (write_CSR csr_medeleg (m !!! Regidx rs1))
                 (fun x => ⌜x = Values.Ok
                     (legalize_medeleg medeleg0 (m !!! Regidx rs1))⌝ ∗
                   hreg_frame (cw_rs medeleg
                     (legalize_medeleg medeleg0 (m !!! Regidx rs1)))
                     (cw_Drw medeleg) ∗
                   hreg_frame_ro (cw_Df (DfracOwn (q/2))) (cw_rs medeleg
                     (legalize_medeleg medeleg0 (m !!! Regidx rs1)))
                     cw_Dro))%I as "Hwr".
      { iIntros "Hrw Hro".
        iApply (swp_mono with "[] [-]");
          [| iApply (swp_hfrun 8 (cw_Drw medeleg) cw_Dro
                       (cw_Df (DfracOwn (q/2))) (cw_rs medeleg medeleg0) _ _ _
                       (cw_disj medeleg Hfresh)
                       (hfrun_write_CSR_medeleg (cw_Drw medeleg ∪ cw_Dro)
                          (cw_Drw medeleg) (cw_rs medeleg medeleg0)
                          (m !!! Regidx rs1) (cw_in_r medeleg)
                          (cw_w_r medeleg))
                       with "Hcert Hrw Hro") ].
        iIntros (x) "(-> & Hrw & Hro)".
        rewrite (cw_rs_r medeleg medeleg0).
        iDestruct (cw_rw_ext medeleg _ _
                     (reg_agree_l _ _ _ _
                        (cw_set_agree medeleg medeleg0 _ Hfresh))
                     with "Hrw") as "Hrw".
        iDestruct (cw_ro_ext (DfracOwn (q/2)) _ _
                     (reg_agree_r _ _ _ _
                        (cw_set_agree medeleg medeleg0 _ Hfresh))
                     with "Hro") as "Hro".
        iSplitR; [done|]. iFrame. }
      iDestruct (cw_frames_in (DfracOwn (q/2)) medeleg medeleg0 Hfresh
                   with "Hcsr Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hmst_k Hpmpc_k] [Hf Hrw Hro Hwr]");
        [| iApply (swp_execute_CSRReg_csrw (cw_Drw medeleg) cw_Dro
                     (cw_Df (DfracOwn (q/2))) (cw_rs medeleg medeleg0)
                     (cw_rs medeleg
                        (legalize_medeleg medeleg0 (m !!! Regidx rs1))) m
                     csr_medeleg rs1 _ (cw_disj medeleg Hfresh)
                     (cw_in_priv medeleg) (cw_in_sec medeleg)
                     (cw_in_misa medeleg)
                     (cw_rs_priv medeleg medeleg0 Hfresh)
                     (cw_rs_sec medeleg medeleg0 Hfresh)
                     (cw_rs_misa medeleg medeleg0 Hfresh)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     Hchk
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro Hwr") ].
      iIntros (e) "(-> & Hf & Hrw & Hro)".
      iDestruct (cw_frames_out (DfracOwn (q/2)) medeleg _ Hfresh
                   with "[$Hrw $Hro]") as "(Hcsr & Hpriv_k & _ & _)".
      iSplitR; [done|]. iFrame "Hf HPC HnPC".
      iSplitL "Hhs_k Hpriv_k Hmst_k".
      { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
      iFrame "Hpmpc_k Hcsr".
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hcsr')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hcsr'").
  Qed.

  (* ---- mcounteren ---- *)
  Lemma wp_csrw_mcounteren_gpr (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (mcounteren0 : type_of_register mcounteren)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mcounteren ↦ᵣ mcounteren0 -∗
    instr pc false (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      mcounteren ↦ᵣ legalize_mcounteren mcounteren0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrs1) "Hmm Hpmpc Hpc Hf Hcsr Hinstr Hcont".
    assert (Hfresh : cw_fresh mcounteren)
      by (rewrite /cw_fresh; split_and!; vm_compute; reflexivity).
    assert (Hchk : exec (check_CSR_result csr_mcounteren Machine CSRWrite) dstateM
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
              (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW)) m m pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               mcounteren ↦ᵣ legalize_mcounteren mcounteren0 (m !!! Regidx rs1))%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hf Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k Hcsr] [Hcont]").
    - iIntros "Hf HPC HnPC".
      (* the write obligation, stated at the NAMED post-file so nothing after
         it has to convert a [register_set] *)
      iAssert (hreg_frame (cw_rs mcounteren mcounteren0) (cw_Drw mcounteren) -∗
               hreg_frame_ro (cw_Df (DfracOwn (q/2))) (cw_rs mcounteren mcounteren0)
                 cw_Dro -∗
               swp (write_CSR csr_mcounteren (m !!! Regidx rs1))
                 (fun x => ⌜x = Values.Ok (zero_extend' 64
                     (legalize_mcounteren mcounteren0 (m !!! Regidx rs1)))⌝ ∗
                   hreg_frame (cw_rs mcounteren
                     (legalize_mcounteren mcounteren0 (m !!! Regidx rs1)))
                     (cw_Drw mcounteren) ∗
                   hreg_frame_ro (cw_Df (DfracOwn (q/2))) (cw_rs mcounteren
                     (legalize_mcounteren mcounteren0 (m !!! Regidx rs1)))
                     cw_Dro))%I as "Hwr".
      { iIntros "Hrw Hro".
        iApply (swp_mono with "[] [-]");
          [| iApply (swp_hfrun 8 (cw_Drw mcounteren) cw_Dro
                       (cw_Df (DfracOwn (q/2))) (cw_rs mcounteren mcounteren0) _ _ _
                       (cw_disj mcounteren Hfresh)
                       (hfrun_write_CSR_mcounteren (cw_Drw mcounteren ∪ cw_Dro)
                          (cw_Drw mcounteren) (cw_rs mcounteren mcounteren0)
                          (m !!! Regidx rs1) (cw_in_r mcounteren)
                          (cw_w_r mcounteren))
                       with "Hcert Hrw Hro") ].
        iIntros (x) "(-> & Hrw & Hro)".
        rewrite (cw_rs_r mcounteren mcounteren0).
        iDestruct (cw_rw_ext mcounteren _ _
                     (reg_agree_l _ _ _ _
                        (cw_set_agree mcounteren mcounteren0 _ Hfresh))
                     with "Hrw") as "Hrw".
        iDestruct (cw_ro_ext (DfracOwn (q/2)) _ _
                     (reg_agree_r _ _ _ _
                        (cw_set_agree mcounteren mcounteren0 _ Hfresh))
                     with "Hro") as "Hro".
        iSplitR; [done|]. iFrame. }
      iDestruct (cw_frames_in (DfracOwn (q/2)) mcounteren mcounteren0 Hfresh
                   with "Hcsr Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hmst_k Hpmpc_k] [Hf Hrw Hro Hwr]");
        [| iApply (swp_execute_CSRReg_csrw (cw_Drw mcounteren) cw_Dro
                     (cw_Df (DfracOwn (q/2))) (cw_rs mcounteren mcounteren0)
                     (cw_rs mcounteren
                        (legalize_mcounteren mcounteren0 (m !!! Regidx rs1))) m
                     csr_mcounteren rs1 _ (cw_disj mcounteren Hfresh)
                     (cw_in_priv mcounteren) (cw_in_sec mcounteren)
                     (cw_in_misa mcounteren)
                     (cw_rs_priv mcounteren mcounteren0 Hfresh)
                     (cw_rs_sec mcounteren mcounteren0 Hfresh)
                     (cw_rs_misa mcounteren mcounteren0 Hfresh)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     Hchk
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro Hwr") ].
      iIntros (e) "(-> & Hf & Hrw & Hro)".
      iDestruct (cw_frames_out (DfracOwn (q/2)) mcounteren _ Hfresh
                   with "[$Hrw $Hro]") as "(Hcsr & Hpriv_k & _ & _)".
      iSplitR; [done|]. iFrame "Hf HPC HnPC".
      iSplitL "Hhs_k Hpriv_k Hmst_k".
      { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
      iFrame "Hpmpc_k Hcsr".
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hcsr')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hcsr'").
  Qed.

  (* ---- menvcfg ---- *)
  Lemma wp_csrw_menvcfg_gpr (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (menvcfg0 : type_of_register menvcfg)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    instr pc false (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      menvcfg ↦ᵣ menvcfg_legalized menvcfg0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrs1) "Hmm Hpmpc Hpc Hf Hcsr Hinstr Hcont".
    assert (Hfresh : cw_fresh menvcfg)
      by (rewrite /cw_fresh; split_and!; vm_compute; reflexivity).
    assert (Hchk : exec (check_CSR_result csr_menvcfg Machine CSRWrite) dstateM
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
              (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW)) m m pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               menvcfg ↦ᵣ menvcfg_legalized menvcfg0 (m !!! Regidx rs1))%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hf Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k Hcsr] [Hcont]").
    - iIntros "Hf HPC HnPC".
      (* the write obligation, stated at the NAMED post-file so nothing after
         it has to convert a [register_set] *)
      iPoseProof (swp_write_CSR_menvcfg (DfracOwn (q/2)) menvcfg0
                    (m !!! Regidx rs1) Hfresh with "Hcert") as "Hwr".
      iDestruct (cw_frames_in (DfracOwn (q/2)) menvcfg menvcfg0 Hfresh
                   with "Hcsr Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hmst_k Hpmpc_k] [Hf Hrw Hro Hwr]");
        [| iApply (swp_execute_CSRReg_csrw (cw_Drw menvcfg) cw_Dro
                     (cw_Df (DfracOwn (q/2))) (cw_rs menvcfg menvcfg0)
                     (cw_rs menvcfg
                        (menvcfg_legalized menvcfg0 (m !!! Regidx rs1))) m
                     csr_menvcfg rs1 _ (cw_disj menvcfg Hfresh)
                     (cw_in_priv menvcfg) (cw_in_sec menvcfg)
                     (cw_in_misa menvcfg)
                     (cw_rs_priv menvcfg menvcfg0 Hfresh)
                     (cw_rs_sec menvcfg menvcfg0 Hfresh)
                     (cw_rs_misa menvcfg menvcfg0 Hfresh)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     Hchk
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro Hwr") ].
      iIntros (e) "(-> & Hf & Hrw & Hro)".
      iDestruct (cw_frames_out (DfracOwn (q/2)) menvcfg _ Hfresh
                   with "[$Hrw $Hro]") as "(Hcsr & Hpriv_k & _ & _)".
      iSplitR; [done|]. iFrame "Hf HPC HnPC".
      iSplitL "Hhs_k Hpriv_k Hmst_k".
      { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
      iFrame "Hpmpc_k Hcsr".
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hcsr')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hcsr'").
  Qed.

  (* ---- mepc ---- *)
  Lemma wp_csrw_mepc_gpr (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (mepc0 : type_of_register mepc)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mepc ↦ᵣ mepc0 -∗
    instr pc false (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      mepc ↦ᵣ mepc_val (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrs1) "Hmm Hpmpc Hpc Hf Hcsr Hinstr Hcont".
    assert (Hfresh : cw_fresh mepc)
      by (rewrite /cw_fresh; split_and!; vm_compute; reflexivity).
    assert (Hchk : exec (check_CSR_result csr_mepc Machine CSRWrite) dstateM
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
              (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW)) m m pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               mepc ↦ᵣ mepc_val (m !!! Regidx rs1))%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hf Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k Hcsr] [Hcont]").
    - iIntros "Hf HPC HnPC".
      (* the write obligation, stated at the NAMED post-file so nothing after
         it has to convert a [register_set] *)
      iAssert (hreg_frame (cw_rs mepc mepc0) (cw_Drw mepc) -∗
               hreg_frame_ro (cw_Df (DfracOwn (q/2))) (cw_rs mepc mepc0)
                 cw_Dro -∗
               swp (write_CSR csr_mepc (m !!! Regidx rs1))
                 (fun x => ⌜x = Values.Ok (mepc_val (m !!! Regidx rs1))⌝ ∗
                   hreg_frame (cw_rs mepc
                     (mepc_val (m !!! Regidx rs1)))
                     (cw_Drw mepc) ∗
                   hreg_frame_ro (cw_Df (DfracOwn (q/2))) (cw_rs mepc
                     (mepc_val (m !!! Regidx rs1)))
                     cw_Dro))%I as "Hwr".
      { iIntros "Hrw Hro".
        iApply (swp_mono with "[] [-]");
          [| iApply (swp_hfrun 8 (cw_Drw mepc) cw_Dro
                       (cw_Df (DfracOwn (q/2))) (cw_rs mepc mepc0) _ _ _
                       (cw_disj mepc Hfresh)
                       (hfrun_write_CSR_mepc (cw_Drw mepc ∪ cw_Dro)
                          (cw_Drw mepc) (cw_rs mepc mepc0)
                          (m !!! Regidx rs1) (cw_w_r mepc))
                       with "Hcert Hrw Hro") ].
        iIntros (x) "(-> & Hrw & Hro)".
        iDestruct (cw_rw_ext mepc _ _
                     (reg_agree_l _ _ _ _
                        (cw_set_agree mepc mepc0 _ Hfresh))
                     with "Hrw") as "Hrw".
        iDestruct (cw_ro_ext (DfracOwn (q/2)) _ _
                     (reg_agree_r _ _ _ _
                        (cw_set_agree mepc mepc0 _ Hfresh))
                     with "Hro") as "Hro".
        iSplitR; [done|]. iFrame. }
      iDestruct (cw_frames_in (DfracOwn (q/2)) mepc mepc0 Hfresh
                   with "Hcsr Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hmst_k Hpmpc_k] [Hf Hrw Hro Hwr]");
        [| iApply (swp_execute_CSRReg_csrw (cw_Drw mepc) cw_Dro
                     (cw_Df (DfracOwn (q/2))) (cw_rs mepc mepc0)
                     (cw_rs mepc
                        (mepc_val (m !!! Regidx rs1))) m
                     csr_mepc rs1 _ (cw_disj mepc Hfresh)
                     (cw_in_priv mepc) (cw_in_sec mepc)
                     (cw_in_misa mepc)
                     (cw_rs_priv mepc mepc0 Hfresh)
                     (cw_rs_sec mepc mepc0 Hfresh)
                     (cw_rs_misa mepc mepc0 Hfresh)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     Hchk
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro Hwr") ].
      iIntros (e) "(-> & Hf & Hrw & Hro)".
      iDestruct (cw_frames_out (DfracOwn (q/2)) mepc _ Hfresh
                   with "[$Hrw $Hro]") as "(Hcsr & Hpriv_k & _ & _)".
      iSplitR; [done|]. iFrame "Hf HPC HnPC".
      iSplitL "Hhs_k Hpriv_k Hmst_k".
      { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
      iFrame "Hpmpc_k Hcsr".
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hcsr')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hcsr'").
  Qed.

  (* ---- mscratch ---- *)

End WpCsrwGprNewA.
