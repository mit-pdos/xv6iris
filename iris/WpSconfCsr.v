(* WpSconfCsr.v -- the S-mode CSR leaves over [sconf]+[sie_cap]: the
   sstatus reads/flips, [wp_csrw_stvec_s_sconf] (the trap-vector
   install) and [wp_csrr_scause_s_sconf] (the trap-cause read).

   [wp_csrr_sstatus_s_sconf] (push_off's intr_get) works at EITHER SIE
   value (the arm INDEX [b] is a lemma parameter): the read needs no SIE
   side condition, and the continuation receives the capability
   DESTRUCTED into [sie_arm b] PAIRED with the pure fact that the read
   value's SIE bit matches that index (ghost agreement between the
   bundle's tied half and the capability quarter).  At [b = false] it
   holds the bare '0' quarter; at [b = true] it holds the quarter + the
   interrupt invariant + the trap CSRs + the stack bound -- exactly what
   the upcoming csrci flip leaf consumes or what pop_off's csrsi restore
   re-packs.

   The csrci/csrsi FLIP leaves themselves are NOT here yet: they need
   the SIE=1 characterization of
   [legalize_sstatus_val ms (sstatus_write_val ms 2)] (bit-preservation
   of the sconf_ms_facts set + SIE clearing), a WpGprCsrwC-style
   symbolic-mstatus effort -- see the stage-7 note in CLAUDE.md.        *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var ghost_map invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import RegFile.
Require Import InstrBytes WpGpr ExecCommon WpGprCsrwCommon WpGprCsrwB.
Require Import SmodeCore WpMmodeLeafBase.
(* [exec_execute_csrr_sstatus] is proved below -- it is the read-only csrr of
   ONE csr at ONE privilege, so it belongs with the S-mode csr leaves that use
   it (the WpSmodePtCtl copy is Local).  The csr-WRITE reduction chain
   (exec_write_CSR_sstatus & co.) is exported from WpPushOffCsr.v --
   relocate those down when the csr leaves get a shared base. *)
Require Import WpGprCsrrCommon WpGprCsrrB.
(* [mepc_val] -- the shared xepc legalizer (bit 0 cleared).  sepc's READ
   runs the same function via [align_pc], so the sepc leaves below name it
   rather than introducing a second copy. *)
Require Import WpGprCsrwA.
Require Import WpPushOffCsr WpSieFlipBits.
Require WpGprCsrwC.
Require Import StackOwn.
Require Import HartTp WpNext.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
(* [sr_ktier_wit]: the capability's tier witness, which this file's sstatus
   read has to carry ACROSS its σ-callback -- see the give-back below. *)
Require Import SRegime.
(* [tlb_res_pt_satp_acc]: the satp borrow the csrr-satp leaf takes out of the
   translation slot's KPT arm.  [IntrDefs] already names [tlb_res_pt], so this
   adds no edge to the require graph -- only the import. *)
Require Import KptShare.
Import Defs.

(* helper copy (Local in WpSmodePtCtl.v) *)
Local Definition csr_sstatus : mword 12 := Ox"100".

(* ===================================================================== *)
(* exec layer: read-only [csrr rd,sstatus] (CSRRS with rs1 = x0, so no     *)
(* write happens) at Supervisor.  Used by the sstatus read leaf below.     *)
(* ===================================================================== *)

Lemma exec_csr_id_read_callback_sstatus (d : mword 64) s :
  exec (csr_id_read_callback csr_sstatus d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_sstatus d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrr_sstatus (rd : mword 5) (m : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  uint rd <> 0 ->
  exec (execute (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sstatus_read m))).
Proof.
  intros Hpriv Hm HS Hrd.
  change (execute (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS)))
    with (execute_CSRReg csr_sstatus (Regidx (mword_of_int 0)) (Regidx rd) CSRRS).
  unfold execute_CSRReg.
  (* access_type = csr_access_type CSRRS _ true = CSRRead *)
  replace (generic_eq (Regidx (mword_of_int 0 : mword 5)) zreg) with true
    by (vm_compute; reflexivity).
  cbn zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr (mword_of_int 0) s)).
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_result_sstatus_S s HS)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  unfold ext_check_CSR. cbn match.
  replace (generic_neq (csr_access_type CSRRS (generic_eq (Regidx rd) zreg) true) CSRWrite)
    with true by (vm_compute; reflexivity).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_sstatus s)). rewrite Hm.
  replace (eq_vec csr_sstatus (Ox"344")) with false by (vm_compute; reflexivity).
  replace (eq_vec csr_sstatus (Ox"144")) with false by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (sstatus_read m) s)).
  replace (generic_eq (csr_access_type CSRRS (generic_eq (Regidx rd) zreg) true) CSRRead)
    with true by (vm_compute; reflexivity).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_csr_id_read_callback_sstatus (sstatus_read m) s)).
  assert (HwX : exec (wX_bits (Regidx rd) (sstatus_read m)) s
                = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sstatus_read m)))).
  { rewrite (exec_wX_bits_gpr rd _ s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ HwX).
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* exec layer: [csrr rd,scause] at Supervisor.  The privilege-free pieces  *)
(* ([exec_read_CSR_scause], the id read callback) live in WpGprCsrrB.v;    *)
(* scause is gated on Ext_S alone, exactly as stvec's write is.            *)
(* ===================================================================== *)

(* THE Ext_S ACCESSIBILITY CHECK, ONCE.  sepc / scause / stval are all
   plain S-level CSRs whose only gate is Ext_S, so what distinguishes them
   in the check is nothing at all: the four dispatch facts are closed and
   vm-computable per CSR, and the misa.S step is shared.  Stated over the
   CSR number so each of the three contributes four [vm_compute]s. *)
Lemma exec_check_CSR_result_read_extS (csr : mword 12) s :
  check_CSR_priv csr Supervisor = returnM true ->
  check_CSR_access csr CSRRead = true ->
  is_CSR_accessible csr Supervisor CSRRead = currentlyEnabled Ext_S ->
  stateen_allows_CSR_access csr Supervisor CSRRead = returnM true ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr Supervisor CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intros Hpriv Hacc Hred Hst HS.
  apply exec_check_CSR_result_read_p. apply exec_check_CSR_read_p.
  - rewrite Hpriv. apply exec_returnm.
  - exact Hacc.
  - rewrite Hred. rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity.
  - rewrite Hst. apply exec_returnm.
Qed.

Lemma exec_check_CSR_result_scause_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_scause Supervisor CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  apply exec_check_CSR_result_read_extS;
    [ vm_compute; reflexivity | vm_compute; reflexivity
    | csr_dispatch_eq | vm_compute; reflexivity ].
Qed.

Lemma exec_check_CSR_result_stval_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_stval Supervisor CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  apply exec_check_CSR_result_read_extS;
    [ vm_compute; reflexivity | vm_compute; reflexivity
    | csr_dispatch_eq | vm_compute; reflexivity ].
Qed.

Lemma exec_check_CSR_result_sepc_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_sepc Supervisor CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  apply exec_check_CSR_result_read_extS;
    [ vm_compute; reflexivity | vm_compute; reflexivity
    | csr_dispatch_eq | vm_compute; reflexivity ].
Qed.

Lemma exec_execute_csrr_scause_gpr_S (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_scause zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg (register_lookup scause s.(sregs)))).
Proof.
  intros Hrd Hpriv HS.
  apply (csrr_read_step_p Supervisor csr_scause rd
           (register_lookup scause s.(sregs)) s _ Hpriv).
  - apply (exec_check_CSR_result_scause_S s HS).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_scause.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_scause.
  - rewrite (exec_wX_bits_gpr rd (register_lookup scause s.(sregs)) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

Lemma exec_execute_csrr_stval_gpr_S (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_stval zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg (register_lookup stval s.(sregs)))).
Proof.
  intros Hrd Hpriv HS.
  apply (csrr_read_step_p Supervisor csr_stval rd
           (register_lookup stval s.(sregs)) s _ Hpriv).
  - apply (exec_check_CSR_result_stval_S s HS).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_stval.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_stval.
  - rewrite (exec_wX_bits_gpr rd (register_lookup stval s.(sregs)) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* sepc's read is the one that is not its cell: [align_pc] clears bit 0,
   so this needs misa.C as well and the value carries the wrapper. *)
Lemma exec_execute_csrr_sepc_gpr_S (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_sepc zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg
                       (mepc_val (register_lookup sepc s.(sregs))))).
Proof.
  intros Hrd Hpriv HS HC.
  apply (csrr_read_step_p Supervisor csr_sepc rd
           (mepc_val (register_lookup sepc s.(sregs))) s _ Hpriv).
  - apply (exec_check_CSR_result_sepc_S s HS).
  - vm_compute; reflexivity.
  - apply (exec_read_CSR_sepc s HC).
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_sepc.
  - rewrite (exec_wX_bits_gpr rd (mepc_val (register_lookup sepc s.(sregs))) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ===================================================================== *)
(* exec layer: [csrr rd,satp] at Supervisor -- THE ODD ONE OUT.           *)
(*                                                                        *)
(* Every other S-mode CSR read above is gated on Ext_S alone, which is    *)
(* why [exec_check_CSR_result_read_extS] serves all three of them with    *)
(* four [vm_compute]s each.  satp is gated on mstatus.TVM, which is not a *)
(* constant but a REGISTER READ -- [is_CSR_accessible 0x180 p acc] is     *)
(* [satp_accessible p], and at Supervisor that is                         *)
(* [read_reg mstatus >>= fun w => returnM (TVM w == 0)].  So the shared   *)
(* Ext_S route is not merely inconvenient here, its third premise         *)
(* ([is_CSR_accessible … = currentlyEnabled Ext_S]) is FALSE, and the     *)
(* check has to be assembled by hand.                                     *)
(*                                                                        *)
(* THE PIECES DO NOT ALL LIVE HERE.  The accessibility step is            *)
(* WpGprCsrwB's [exec_is_CSR_accessible_satp_S], written access-type      *)
(* generic precisely so this read and userret's write share it; and       *)
(* [csr_satp] is that file's definition.  Only the read-specific halves   *)
(* are below.  They are not in WpGprCsrrB.v with scause's and stval's --  *)
(* that file is deliberately privilege-free and does not (and should not) *)
(* import the csrw family that owns [csr_satp].                           *)
(*                                                                        *)
(* NOTE WHAT IS ABSENT FROM THE PREMISES: no misa.S, and no misa.C.       *)
(* satp's read touches neither -- unlike sepc, whose value runs through   *)
(* [align_pc] and so needs Zca.  The read is the cell, verbatim.          *)
(* ===================================================================== *)

Lemma exec_read_CSR_satp s :
  exec (read_CSR csr_satp) s = Some (register_lookup satp s.(sregs), s).
Proof. drive_csr. reflexivity. Qed.

Lemma exec_csr_id_read_callback_satp s d :
  exec (csr_id_read_callback csr_satp d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_satp d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_check_CSR_result_csrr_satp_S s :
  eq_vec (_get_Mstatus_TVM (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  exec (check_CSR_result csr_satp Supervisor CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HTVM.
  apply exec_check_CSR_result_read_p. apply exec_check_CSR_read_p.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - exact (exec_is_CSR_accessible_satp_S CSRRead s HTVM).
  - vm_compute (stateen_allows_CSR_access csr_satp Supervisor CSRRead).
    apply exec_returnM.
Qed.

Lemma exec_execute_csrr_satp_gpr_S (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Mstatus_TVM (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  exec (execute_CSRReg csr_satp zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg (register_lookup satp s.(sregs)))).
Proof.
  intros Hrd Hpriv HTVM.
  apply (csrr_read_step_p Supervisor csr_satp rd
           (register_lookup satp s.(sregs)) s _ Hpriv).
  - apply (exec_check_CSR_result_csrr_satp_S s HTVM).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_satp.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_satp.
  - rewrite (exec_wX_bits_gpr rd (register_lookup satp s.(sregs)) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ===================================================================== *)
(* exec layer: [csrw sstatus,rs1] at Supervisor -- the S-status RESTORE.  *)
(*                                                                        *)
(* The privilege-free chain (check_CSR_priv / read / legalize / write /   *)
(* the id write callback) is WpPushOffCsr.v's, built there for the csrci   *)
(* flip; what is new here is the CSRWrite accessibility check (csrci is a  *)
(* read-MODIFY-write, so it goes through CSRReadWrite) and the [execute]   *)
(* instance for the rd = x0 form, which does not read the CSR at all.      *)
(* ===================================================================== *)

Lemma exec_check_CSR_result_csrw_sstatus_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_sstatus Supervisor CSRWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS.
  apply exec_check_CSR_result_csrw_p. apply exec_check_CSR_csrw_p.
  - apply exec_check_CSR_priv_sstatus_S.
  - vm_compute; reflexivity.
  - assert (Hred : is_CSR_accessible csr_sstatus Supervisor CSRWrite
                   = currentlyEnabled Ext_S) by csr_dispatch_eq.
    rewrite Hred. rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity.
  - assert (H : stateen_allows_CSR_access csr_sstatus Supervisor CSRWrite = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrw_sstatus_S (rs1 : mword 5) (ms : mword 64) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  register_lookup mstatus s.(sregs) = ms ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute (CSRReg (csr_sstatus, Regidx rs1, zreg, CSRRW))) s
    = Some (RETIRE_SUCCESS,
            set_reg s mstatus
              (legalize_sstatus_val ms
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv Hms HS HU.
  change (execute (CSRReg (csr_sstatus, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_sstatus (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr_p Supervisor csr_sstatus rs1 s _
           (subrange_vec_dec
              (lower_mstatus
                 (legalize_sstatus_val ms
                    (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))
              (Z.sub xlen 1) 0)).
  - exact Hpriv.
  - apply exec_check_CSR_result_csrw_sstatus_S; assumption.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - rewrite (exec_write_CSR_sstatus _ s HS HU). rewrite Hms. reflexivity.
  - apply exec_csr_id_write_callback_sstatus.
Qed.

(* ===================================================================== *)
(* exec layer: [csrw sepc,rs1] at Supervisor.                             *)
(*                                                                        *)
(* Unlike stvec's, sepc's privilege-FREE half lives here rather than in    *)
(* WpGprCsrwB.v: the write runs [set_xepc Supervisor], whose legalizer     *)
(* ([exec_legalize_xepc] / [mepc_val]) is mepc's, i.e. in WpGprCsrwA --    *)
(* and importing A into B to reach it would invert the A/B layering for    *)
(* the sake of one CSR that has no M-mode consumer at all.  So the whole   *)
(* sepc chain sits next to its leaf.                                       *)
(*                                                                        *)
(* THE WRITTEN WORD IS LEGALIZED, and the postcondition says so            *)
(* ([mepc_val], bit 0 cleared) rather than pretending otherwise -- the     *)
(* same choice as satp/stimecmp, and the opposite of stvec, whose          *)
(* legalizer is provably the identity at this platform's parameters.  A    *)
(* caller writing back an aligned epc collapses the wrapper itself.        *)
(* ===================================================================== *)

Lemma exec_write_CSR_sepc (v : mword 64) s :
  exec (write_CSR csr_sepc v) s = Some (Ok (mepc_val v), set_reg s sepc (mepc_val v)).
Proof.
  unfold write_CSR. skip_csr_false_clauses.
  assert (Hsx : exec (set_xepc Supervisor v) s
                = Some (mepc_val v, set_reg s sepc (mepc_val v))).
  { unfold set_xepc.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_legalize_xepc v s)). cbn match.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg sepc (mepc_val v) s)).
    apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hsx).
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_sepc (d : mword 64) s :
  exec (csr_id_write_callback csr_sepc d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_sepc d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_check_CSR_result_csrw_sepc_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_sepc Supervisor CSRWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS.
  apply exec_check_CSR_result_csrw_p. apply exec_check_CSR_csrw_p.
  - assert (H : check_CSR_priv csr_sepc Supervisor = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - assert (Hred : is_CSR_accessible csr_sepc Supervisor CSRWrite
                   = currentlyEnabled Ext_S) by csr_dispatch_eq.
    rewrite Hred. rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity.
  - assert (H : stateen_allows_CSR_access csr_sepc Supervisor CSRWrite = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrw_sepc_S (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute (CSRReg (csr_sepc, Regidx rs1, zreg, CSRRW))) s
    = Some (RETIRE_SUCCESS,
            set_reg s sepc
              (mepc_val (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HS.
  change (execute (CSRReg (csr_sepc, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_sepc (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr_p Supervisor csr_sepc rs1 s _
           (mepc_val (if Z.eqb (uint rs1) 0 then zero_reg
                      else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
  - exact Hpriv.
  - apply exec_check_CSR_result_csrw_sepc_S; assumption.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_sepc.
  - apply exec_csr_id_write_callback_sepc.
Qed.

(* ===================================================================== *)
(* exec layer: [csrw stvec,rs1] at Supervisor.  The per-CSR pieces        *)
(* ([exec_write_CSR_stvec] & co.) are privilege-free and live in          *)
(* WpGprCsrwB.v; what is S-mode-specific is the accessibility check and   *)
(* the [execute] instance of the privilege-generic framework.            *)
(* ===================================================================== *)

(* stvec is an S-level CSR whose only accessibility gate is Ext_S. *)
Lemma exec_check_CSR_result_csrw_stvec_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_stvec Supervisor CSRWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS.
  apply exec_check_CSR_result_csrw_p. apply exec_check_CSR_csrw_p.
  - assert (H : check_CSR_priv csr_stvec Supervisor = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - assert (Hred : is_CSR_accessible csr_stvec Supervisor CSRWrite
                   = currentlyEnabled Ext_S) by csr_dispatch_eq.
    rewrite Hred. rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity.
  - assert (H : stateen_allows_CSR_access csr_stvec Supervisor CSRWrite = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrw_stvec_S (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  trapVectorMode_forwards
    (_get_Mtvec_Mode (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))
    <> TV_Reserved ->
  exec (execute (CSRReg (csr_stvec, Regidx rs1, zreg, CSRRW))) s
    = Some (RETIRE_SUCCESS,
            set_reg s stvec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))).
Proof.
  intros Hrs1 Hpriv HS Hm.
  change (execute (CSRReg (csr_stvec, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_stvec (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr_p Supervisor csr_stvec rs1 s _
           (if Z.eqb (uint rs1) 0 then zero_reg
            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))).
  - exact Hpriv.
  - apply exec_check_CSR_result_csrw_stvec_S; assumption.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_stvec.
    replace (Z.eqb (uint rs1) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrs1). exact Hm.
  - apply exec_csr_id_write_callback_stvec.
Qed.

(* THE TWO COMPANIONS OF [trap_csrs_pay] THE SIE-FLIP LEAVES NEED, one on
   each side of the flip.  Both exist because [sie_arm true p] owns the
   enabled arm's per-cpu bookkeeping ([cpu_hart 0 true p], IntrDefs.v) --
   i.e. BOTH eighths of the kernel-code SIE token: its own, and the one
   nested inside [intr_count 0 true].  So a caller at [b = true] can hold
   NEITHER; the flip leaves must consume the arm whole and hand back the
   pieces (and, in the other direction, take the pieces and build it).

   THEY LIVE OUTSIDE [Section WpSconfCsr] ON PURPOSE.  A constant defined
   INSIDE a section has that section's variables -- here [CID] -- applied
   automatically at every use in the same section, which silently BEATS the
   [fun (CID : CpuId) => ...] binder of a [wp_next] continuation: the leaf
   would then hand its payload back at the hart it started on rather than
   the one execution resumed on.  Defined out here they take [CID] as an
   ordinary instance argument, resolved -- like every [IntrDefs] resource
   in the same continuation -- to the bound hart. *)

(* ON THE WAY OUT (a csrci): the freed cells.  Indexed by [b], not by the
   level -- the cells come out exactly when there WAS an arm to dismantle.
   The count eighth is NOT here: it is accounted for by the leaf's
   [intr_count (S k) eb] postcondition, and handing out both would be
   handing out the same eighth at two different values. *)
Definition cpu_priv_pay `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId}
    (b : bool) (p : mword 64) : iProp Σ :=
  (if b then cpu_priv 0 true p ∅ else emp)%I.

Lemma cpu_priv_pay_on `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (px : mword 64) :
  cpu_priv_pay true px ⊣⊢ cpu_priv 0 true px ∅.
Proof. reflexivity. Qed.

Lemma cpu_priv_pay_off `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (px : mword 64) :
  cpu_priv_pay false px ⊣⊢ (emp : iProp Σ).
Proof. reflexivity. Qed.

(* ON THE WAY IN (a csrci again -- the counting token the leaf increments).
   At [b = false] the caller holds it beside its bundle and hands it over,
   exactly as before.  At [b = true] it is inside the arm, so what the
   caller supplies instead is the PURE fact its own [cpu_own _ _ _ _ true]
   carries ([CpuOwn.cpu_own_on]) -- which is what pins the leaf's [k]/[eb]
   there, the arm having baked them in as 0 / true. *)
Definition intr_count_pre `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (b : bool) (n : nat) (eb : bool) : iProp Σ :=
  (if b then ⌜ n = 0%nat /\ eb = true ⌝ else intr_count n eb)%I.

(* the two index-instances, so a proof never has to reduce the [if] by
   hand inside the proofmode. *)
Lemma intr_count_pre_on `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (n : nat) (eb : bool) :
  intr_count_pre true n eb -∗ ⌜ n = 0%nat /\ eb = true ⌝.
Proof. iIntros "H". iExact "H". Qed.

Lemma intr_count_pre_off `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (n : nat) (eb : bool) :
  intr_count_pre false n eb -∗ intr_count n eb.
Proof. iIntros "H". iExact "H". Qed.

Section WpSconfCsr.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  Lemma wp_csrr_sstatus_s_sconf
      (pc : mword 64) (rd : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      (* [sconf_at ms], not [sconf]: the leaf NAMES the mstatus it read, so
         handing back the mstatus-EXPOSING flavour costs nothing and is
         strictly more useful -- it is what lets a holder of the [sret_bits]
         travelling half turn it into a fact about SPP/SPIE at this very [ms]
         ([sconf_at_sret]).  [sconf_at_close] recovers the plain bundle in
         one line for callers that do not care. *)
      sconf_at ms -∗
      strans_inv -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (tp_pin (<[Regidx rd := regval_into_reg (sstatus_read ms)]> m)) -∗
      (* THE CARVE IS THE CAPABILITY'S, SO IT IS ARM-DEPENDENT.  This leaf
         takes the bundle at a GENERIC [b] and hands the stack conjunct back
         raw (the arm-bit fact and the arm travel separately, so the caller
         can re-fold), which means the size MUST be spelled [trap_res b + n]
         -- the same thing [IntrDefs.sie_cap] owns.  Spelled
         [kv_frame_slots + n] (what an arm-blind reserve made it) this
         statement is FALSE at [b = false]: the [destruct b] in the proof
         below shows that arm handing back a carve it never received. *)
      (* THE TIER WITNESS RIDES WITH THE PIECES, AND UNDER A GENERIC [kt] IT
         HAS TO.  This is the ONE leaf in the S-mode engines that takes the
         capability APART across the σ-callback (every other leaf hands
         [sie_cap_gpr] back folded), so it is the one place the fourth
         conjunct of [IntrDefs.sie_cap] could be lost -- and a caller that
         lost it could only close its re-fold by CONJURING a witness at a
         [kt] it knows nothing about.  It is persistent
         ([SRegime.sr_ktier_wit_persistent]), so carrying it costs the
         callback side nothing and the give-back is free. *)
      ( stack_own (KTR := kt) (<[Regidx rd := regval_into_reg (sstatus_read ms)]> m
                     !!! Regidx csp_rs1) (trap_res b + n) ∗
        ⌜ _get_Mstatus_SIE ms = sie_bit b ⌝ ∗
        sie_arm kt b p ∗
        sr_ktier_wit strans_regime kt ) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok) "Hcg Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    iApply (wp_instr_s_sconf m n b pc false
              (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    iDestruct (gpr_file_insert_acc (tp_pin m) (Regidx rd) (regval_into_reg (sstatus_read ms0)) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (sstatus_read ms0)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (sstatus_read ms0))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_csrr_sstatus rd ms0 s_pc
               Lpriv_spc Lms_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS) Hrd). }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (sstatus_read ms0))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : <[Regidx rd := regval_into_reg (sstatus_read ms0)]> m !!! Regidx csp_rs1
                  = m !!! Regidx csp_rs1)
      by (apply upd_ne; congruence).
    tp_refold Hrdtp "Hfmap".
    iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
    (* EVERY HART-INDEXED TERM WRITTEN FRESH NEEDS THE ANNOTATION, and that
       includes the ghost NAME: [sie_gname] is [sie_name cpu_id], so an
       unannotated occurrence names the ENTRY hart's ghost while [Hhalf] came
       from the callback at the rebound one. *)
    (* [Hwit] IS ALREADY AT THE REBOUND HART, so no [sie_ktier_wit_rebind] is
       needed: [wp_instr_s_sconf]'s σ-callback delivers the whole [sie_cap]
       at the hart it rebound to, and this witness was destructed out of
       THAT.  (WpSconfMem's leaves need the rebind because their witness is
       an explicit PREMISE, supplied at the caller's own hart.)  It is
       persistent, so it stays in the intuitionistic context and needs no
       mention in the selection below. *)
    iAssert ( ghost_var (sie_gname (CID := CID)) (1/2) (_get_Mstatus_SIE ms0) ∗
              ( stack_own (KTR := kt) (<[Regidx rd := regval_into_reg (sstatus_read ms0)]> m
                             !!! Regidx csp_rs1) (trap_res b + n) ∗
                ⌜ _get_Mstatus_SIE ms0 = sie_bit b ⌝ ∗
                sie_arm kt (CID := CID) b p ∗
                sr_ktier_wit (CID := CID) (strans_regime (CID := CID)) kt ) )%I
      with "[Hstk Harm Hhalf]" as "[Hhalf Hpair]".
    { destruct b.
      - iDestruct "Harm" as "(Hq1 & Hhx & Hkptr & Hsepcx & Hscausex & Hstvalx & Hsppc & Hcpu)".
        iDestruct (ghost_var_agree with "Hhalf Hq1") as %Hb.
        iFrame "Hhalf". iSplitL "Hstk". { rewrite Hsp. iExact "Hstk". }
        iSplitR. { iPureIntro. exact Hb. }
        iFrame "Hq1 Hhx Hkptr Hsepcx Hscausex Hstvalx Hsppc Hcpu Hwit".
      - iDestruct "Harm" as "Hq0".
        iDestruct (ghost_var_agree with "Hhalf Hq0") as %Hb.
        iFrame "Hhalf". iSplitL "Hstk". { rewrite Hsp. iExact "Hstk". }
        iSplitR. { iPureIntro. exact Hb. }
        iFrame "Hq0 Hwit". }
    iSpecialize ("Hcont" $! CID with "[]"); [iPureIntro; done|].
    iApply ("Hcont" $! ms0 with "[%] Hhs' [Hpriv Hms Hhalf Hspp Hmiex Hmenvx] Htr
                          [$Hpc' $Hnpc] [Hfmap] Hpair").
    { exact Hmsf. }
    { rewrite /sconf_at /sconf_msown.
      iSplitL "Hms Hhalf Hspp".
      { iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
      iIntros (ms') "(Hms' & Hhalf' & Hspp' & %Hmsf')".
      iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
      iExists ms'. iFrame "Hms' Hhalf' Hspp'". iPureIntro. exact Hmsf'. }
    iExact "Hfmap".
  Qed.


  (* ------------------------------------------------------------------- *)
  (* The GENERAL csrrci-on-sstatus execute (no idempotence collapse):     *)
  (* the write lands [legalize_sstatus_val m (sstatus_write_val m imm5)]  *)
  (* in mstatus, rd gets the OLD S-view.                                  *)
  (* ------------------------------------------------------------------- *)
  Local Lemma exec_execute_csrrci_sstatus_gen (imm5 rd : mword 5) (m : mword 64) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    register_lookup mstatus s.(sregs) = m ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec imm5 (zeros' 5) = false ->
    uint rd <> 0 ->
    exec (execute (CSRImm (csr_sstatus, imm5, Regidx rd, CSRRC))) s
      = Some (RETIRE_SUCCESS,
              set_reg (set_reg s mstatus (legalize_sstatus_val m (sstatus_write_val m imm5)))
                      (R_bitvector_64 (gpr_of_Z (uint rd)))
                      (regval_into_reg (sstatus_read m))).
  Proof.
    intros Hpriv Hm HS HU Himm Hrd.
    change (execute (CSRImm (csr_sstatus, imm5, Regidx rd, CSRRC)))
      with (execute_CSRImm csr_sstatus imm5 (Regidx rd) CSRRC).
    unfold execute_CSRImm.
    rewrite Himm.
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
    assert (Hwrite : exec (write_CSR csr_sstatus (sstatus_write_val m imm5)) s
                     = Some (Ok (subrange_vec_dec
                                   (lower_mstatus (legalize_sstatus_val m (sstatus_write_val m imm5)))
                                   (Z.sub xlen 1) 0),
                             set_reg s mstatus (legalize_sstatus_val m (sstatus_write_val m imm5)))).
    { rewrite (exec_write_CSR_sstatus (sstatus_write_val m imm5) s HS HU).
      rewrite Hm. reflexivity. }
    change (and_vec (sstatus_read m) (not_vec (zero_extend' 64 imm5)))
      with (sstatus_write_val m imm5).
    rewrite (exec_bind_Some _ _ _ _ _ Hwrite). cbn beta match.
    set (s1 := set_reg s mstatus (legalize_sstatus_val m (sstatus_write_val m imm5))).
    assert (Hwc : exec (wX_bits (Regidx rd) (sstatus_read m) >>
                        csr_id_write_callback csr_sstatus
                          (subrange_vec_dec
                             (lower_mstatus (legalize_sstatus_val m (sstatus_write_val m imm5)))
                             (Z.sub xlen 1) 0)) s1
                  = Some (tt, set_reg s1 (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (sstatus_read m)))).
    { rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd (sstatus_read m) s1)).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      apply (exec_csr_id_write_callback_sstatus _ _). }
    rewrite (exec_bind0_Some _ _ _ _ _ Hwc).
    apply exec_returnm.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* THE '1'->'0' FLIP: csrci sstatus, 2 (push_off's intr_off).           *)
  (*                                                                      *)
  (* The SIE=1 characterization of the write is PROVEN                    *)
  (* SIE=1 characterization of the legalized write (SIE cleared, the      *)
  (* sconf fact set preserved); it is taken as a premise so the ghost     *)
  (* choreography below is proven now and the bit lemma lands once,       *)
  (* later, in WpGprCsrwC style.  At SIE=0 it already follows from        *)
  (* [legalize_sie_clear_idem].                                           *)
  (*                                                                      *)
  (* Choreography ('1' arm): the funnel's σf-callback flips mstatus to    *)
  (* ms' by reg_update, reads the quarter out of [intr_res],              *)
  (* [sie_ghost_flip]s ALL THREE pieces to '0' (bundle half + capability  *)
  (* quarter + the [intr_res] quarter), re-forms [intr_res] at b := '0'   *)
  (* (the handler guard is vacuous), and hands the caller the freed       *)
  (* '1'-arm payload (the trap CSRs, [intr_res] among them, + the stack   *)
  (* bound).  The '0' arm is the idempotent write, ghosts untouched.      *)
  (* THIS USED TO OPEN [intrN] ACROSS THE STEP; there is no invariant any *)
  (* more, so there is no mask side condition either.                     *)
  (* ------------------------------------------------------------------- *)
(* ===================================================================== *)
(* THE ARM-FLIP SEAM AND ITS avail INDEX -- READ THIS BEFORE TOUCHING ANY  *)
(* OF THE FOUR csrci/csrsi LEAVES BELOW.                                   *)
(*                                                                        *)
(* [IntrDefs.sie_cap m av b p] owns [trap_res b + av] free stack slots     *)
(* below sp: [av] usable by kernel code plus an ARM-DEPENDENT trap reserve *)
(* ([kv_frame_slots] at [b = true], nothing at [b = false] -- see          *)
(* [IntrDefs.trap_res] for why an arm-blind reserve is unsatisfiable).     *)
(* These four leaves are the only instructions in the tree that MOVE THE   *)
(* ARM, so they are the only ones at which that reserve appears or         *)
(* disappears -- and stack slots are not persistent, so the total carve    *)
(* must be CONSERVED across each of them.  Hence the uniform rule:         *)
(*                                                                        *)
(*   a leaf moving the arm from [b0] to [b1] has                            *)
(*     PRE  index [trap_res b1 + n]   and   POST index [trap_res b0 + n].   *)
(*                                                                        *)
(* Both sides then carve [trap_res b0 + (trap_res b1 + n)] slots, i.e. the *)
(* stack conjunct is LITERALLY THE SAME PROPOSITION on the way in and on   *)
(* the way out -- a pure re-indexing, never a split, and never a           *)
(* [kv_frame_slots <= n] premise (which is what rejected alternative (a)   *)
(* at [IntrDefs.trap_res] would have cost).  Each direction collapses to   *)
(* the identity at the arm where nothing moves, because [trap_res false +  *)
(* n] is DEFINITIONALLY [n]:                                              *)
(*                                                                        *)
(*   DISABLING ([b1 = false]): pre [n] (verbatim what it always was),      *)
(*     post [trap_res b + n] -- the freed reserve becomes usable stack.    *)
(*     At [b = false] the post is [n] too, so nothing changes.             *)
(*   ENABLING ([b1 = true]): pre [trap_res true + n], post                 *)
(*     [trap_res b + n] -- re-enabling interrupts PAYS the reserve out of  *)
(*     the caller's budget.  At [b = true] (the idempotent write) pre and  *)
(*     post coincide and the carve rides through untouched.                *)
(*                                                                        *)
(* THE CONSEQUENCE FOR CALLERS IS NOT LOCAL, and that is the point: the    *)
(* window between a push_off/acquire and its matching pop_off/release runs *)
(* at [trap_res b + av], not [av].  Do not "fix" a caller by dropping the  *)
(* difference -- the reserve is exactly what funds the trap handler, and a  *)
(* pop_off that cannot re-establish it is unprovable.                      *)
(* ===================================================================== *)
  (* DISABLING: pre index [n], post index [trap_res b + n] -- the reserve the
     enabled arm was holding becomes usable stack.  See the seam header. *)
  Lemma wp_csrci_sstatus_s_sconf
      (pc : mword 64) (rd : mword 5) (k : nat) (eb : bool)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    intr_count_pre b k eb -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx rd, CSRRC)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      ⌜ k = 0%nat -> _get_Mstatus_SIE ms = sie_bit eb ⌝ -∗
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg (sstatus_read ms)]> m)
                  (trap_res b + n)%nat false p -∗
      intr_count (S k) eb -∗
      trap_csrs_pay kt k eb -∗
      cpu_claim_pay k eb p -∗
      cpu_priv_pay b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok) "Hcg Hcnt Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    iApply (wp_instr_s_sconf m n b pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx rd, CSRRC))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Himm2 : eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false)
      by (vm_compute; reflexivity).
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : <[Regidx rd := regval_into_reg (sstatus_read ms0)]> m !!! Regidx csp_rs1
                  = m !!! Regidx csp_rs1)
      by (apply upd_ne; congruence).
    iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
    destruct b.
    - (* ---- b = true: the real flip.  The caller holds NEITHER eighth here
           (both are in the arm); what it hands over is the pure fact, and
           the arm itself is dismantled for the rest. ---- *)
      iDestruct (intr_count_pre_on with "Hcnt") as %Hke.
      destruct Hke as [-> ->].
      iDestruct "Harm" as "(Hq1 & Hhx & Hkptr & Hsepcx & Hscausex & Hstvalx & Hsppc & Hclmx & (Hcells & Hc1))".
      iDestruct (ghost_var_agree with "Hhalf Hq1") as %Hb1.
      iDestruct (intr_count_get_on 0 true with "Hq1 Hc1") as "(_ & Hq1 & Hc1)".
      destruct (csrci_sie_flip ms0 Hmsf) as (Hsie' & Hspp' & Hspie' & Hmsf').
      set (ms1 := legalize_sstatus_val ms0 (sstatus_write_val ms0 (mword_of_int 2))).
      (* THE HANDLER RESOURCE: read the quarter out, flip, re-form at '0'.
         This was an [inv_acc] on [intrN] plus a re-seal; owning [intr_res]
         turns it into an accessor and a constructor, and the mask side
         condition ([solve_ndisj]) disappears with the invariant. *)
      iEval (rewrite /intr_res) in "Hhx".
      iDestruct "Hhx" as (handler vb) "(%Htvd & %Hsb & Hqi & Hstv & #Hspec)".
      iMod (sie_ghost_flip_off _ _ _ _ _ with "Hhalf Hq1 Hc1 Hqi") as "(Hhalf & Hq & Htok & Hqi)".
      iDestruct (intr_res_intro handler _ Htvd Hsb with "Hqi Hstv Hspec") as "Hintr".
      (* the machine write: mstatus := ms1, rd := old S-view *)
      iMod (reg_update _ mstatus _ ms1 with "Hreg Hms") as "[Hreg Hms]".
      iDestruct (gpr_file_insert_acc (tp_pin m) (Regidx rd) (regval_into_reg (sstatus_read ms0)) with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
              (regval_into_reg (sstatus_read ms0)) with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iModIntro.
      iExists (set_reg (set_reg s_pc mstatus ms1)
                 (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (sstatus_read ms0))).
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc.
        apply (exec_execute_csrrci_sstatus_gen (mword_of_int 2) rd ms0 s_pc
                 Lpriv_spc Lms_spc
                 ltac:(rewrite Lmisa_spc; exact HmisaS)
                 ltac:(rewrite Lmisa_spc; exact HmisaU)
                 Himm2 Hrd). }
      iSplitL "Hreg Hmem".
      { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg (set_reg s_pc mstatus ms1)
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (sstatus_read ms0))).(sregs)
               = add_vec_int pc 4).
      { unfold set_reg at 1; cbn [sregs]. tmig.
        unfold set_reg at 1; cbn [sregs]. tmig.
        unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iEval (rewrite -Hsie') in "Hhalf".
      (* SPP and SPIE are untouched by an SIE flip, so the tie only needs
         re-expressing at the new mstatus -- no ghost movement. *)
      iDestruct (sret_tie_congr ms0 ms1 Hspp' Hspie' with "Hspp") as "Hspp".
      tp_refold Hrdtp "Hfmap".
      iAssert (sie_cap kt (CID := CID) (<[Regidx rd := regval_into_reg (sstatus_read ms0)]> m)
                       (trap_res true + n)%nat false p)
        with "[Hstk Htr Hq]" as "Hcap".
      { iSplitL "Hstk". { rewrite Hsp. iExact "Hstk". }
        iFrame "Htr Hwit". iExact "Hq". }
      iAssert (sconf (CID := CID)) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenvx]" as "Hsc".
      { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
        iExists ms1. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf'. }
      iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
      iSpecialize ("Hcont" $! CID with "[]"); [iPureIntro; done|].
      iApply ("Hcont" $! ms0 with "[%] [%] Hcg
                            [Htok] [Hsepcx Hscausex Hstvalx Hsppc Hintr Hkptr] [Hclmx] [Hcells] [$Hpc' $Hnpc]").
      { exact Hmsf. }
      { intros _. cbn [sie_bit]. exact Hb1. }
      (* the level-S token is now JUST the eighth: the handler resource it
         used to carry goes out with the trap CSRs below, where the client
         needs it and where its matching pop_off takes it back. *)
      { iApply (intr_count_pack_S_on with "Htok"). }
      { iFrame "Hsepcx Hscausex Hstvalx Hsppc Hintr Hkptr". }
      { rewrite /cpu_claim_pay. iExact "Hclmx". }
      { rewrite /cpu_priv_pay. iExact "Hcells". }
    - (* ---- b = false: the idempotent write; ghosts untouched ---- *)
      (* THE GUARD COLLAPSES THE HARTS HERE, and this arm cannot do without
         it: at [b = false] the statement's [intr_count_pre] is a REAL
         per-hart resource, held at the ENTRY hart, and the post owes
         [intr_count (S k) eb] at the CALLBACK's.  Nothing transports a count
         between harts -- but the guard says there is nothing to transport,
         because an SIE-off step cannot migrate.  (The [b = true] arm needs
         no collapse: there [intr_count_pre] is a pure fact and every
         resource in the post comes out of the arm, which the callback
         already delivers at the rebound hart.) *)
      assert (Hcc : CID = CID0) by exact (Hs (or_introl eq_refl)).
      subst CID.
      iDestruct (intr_count_pre_off with "Hcnt") as "Hcnt".
      iDestruct "Harm" as "Hq0".
      iDestruct (ghost_var_agree with "Hhalf Hq0") as %Hb0.
      assert (Hcollapse : legalize_sstatus_val ms0 (sstatus_write_val ms0 (mword_of_int 2)) = ms0)
        by (apply WpGprCsrwC.legalize_sie_clear_idem; assumption).
      iDestruct (gpr_file_insert_acc (tp_pin m) (Regidx rd) (regval_into_reg (sstatus_read ms0)) with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
              (regval_into_reg (sstatus_read ms0)) with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iModIntro.
      iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (sstatus_read ms0))).
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc.
        apply (exec_execute_csrrci_sstatus (mword_of_int 2) rd ms0 s_pc
                 Lpriv_spc Lms_spc
                 ltac:(rewrite Lmisa_spc; exact HmisaS)
                 ltac:(rewrite Lmisa_spc; exact HmisaU)
                 Himm2 Hrd Hcollapse). }
      iSplitL "Hreg Hmem".
      { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (sstatus_read ms0))).(sregs)
               = add_vec_int pc 4).
      { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      tp_refold Hrdtp "Hfmap".
      iDestruct (intr_count_push_off k eb with "Hq0 Hcnt") as "(%Heb0 & Hq0 & Hcnt)".
      iAssert (sie_cap kt (CID := CID0) (<[Regidx rd := regval_into_reg (sstatus_read ms0)]> m)
                       (trap_res false + n)%nat false p)
        with "[Hstk Htr Hq0]" as "Hcap".
      { iSplitL "Hstk". { rewrite Hsp. iExact "Hstk". }
        iFrame "Htr Hwit". iExact "Hq0". }
      iAssert (sconf (CID := CID0)) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenvx]" as "Hsc".
      { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
        iExists ms0. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
      iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
      iSpecialize ("Hcont" $! CID0 with "[]"); [iPureIntro; done|].
      iApply ("Hcont" $! ms0 with "[%] [%] Hcg Hcnt [] [] [] [$Hpc' $Hnpc]").
      { exact Hmsf. }
      { intros Hk. rewrite (Heb0 Hk). cbn [sie_bit]. exact Hb0. }
      { destruct k; [rewrite (Heb0 eq_refl) |]; done. }
      { rewrite /cpu_claim_pay. destruct k; [rewrite (Heb0 eq_refl) |]; done. }
      { rewrite /cpu_priv_pay. done. }
  Qed.


  (* ------------------------------------------------------------------- *)
  (* THE '0'->'1' RESTORE: csrsi sstatus, 2 (pop_off's intr_on).           *)
  (* ------------------------------------------------------------------- *)

  (* two full cells for the same register cannot coexist (refutes the
     already-enabled branch of the restore: the caller's payload and a
     '1'-armed capability would both own sepc). *)
  Local Lemma reg_pointsto_excl (r : register) (v w : type_of_register r) :
    r ↦ᵣ v -∗ r ↦ᵣ w -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    exfalso. apply dfrac_valid_own_r in Hv.
    exact (irreflexivity (<)%Qp 1%Qp Hv).
  Qed.

  Local Lemma exec_execute_csrsi_sstatus_x0 (imm5 : mword 5) (m : mword 64) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    register_lookup mstatus s.(sregs) = m ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec imm5 (zeros' 5) = false ->
    exec (execute (CSRImm (csr_sstatus, imm5, Regidx (mword_of_int 0), CSRRS))) s
      = Some (RETIRE_SUCCESS,
              set_reg s mstatus (legalize_sstatus_val m (sstatus_write_set_val m imm5))).
  Proof.
    intros Hpriv Hm HS HU Himm.
    change (execute (CSRImm (csr_sstatus, imm5, Regidx (mword_of_int 0), CSRRS)))
      with (execute_CSRImm csr_sstatus imm5 (Regidx (mword_of_int 0)) CSRRS).
    unfold execute_CSRImm.
    rewrite Himm.
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
    assert (Hwrite : exec (write_CSR csr_sstatus (sstatus_write_set_val m imm5)) s
                     = Some (Ok (subrange_vec_dec
                                   (lower_mstatus (legalize_sstatus_val m (sstatus_write_set_val m imm5)))
                                   (Z.sub xlen 1) 0),
                             set_reg s mstatus (legalize_sstatus_val m (sstatus_write_set_val m imm5)))).
    { rewrite (exec_write_CSR_sstatus (sstatus_write_set_val m imm5) s HS HU).
      rewrite Hm. reflexivity. }
    change (or_vec (sstatus_read m) (zero_extend' 64 imm5))
      with (sstatus_write_set_val m imm5).
    rewrite (exec_bind_Some _ _ _ _ _ Hwrite). cbn beta match.
    set (s1 := set_reg s mstatus (legalize_sstatus_val m (sstatus_write_set_val m imm5))).
    assert (Hwc : exec (wX_bits (Regidx (mword_of_int 0)) (sstatus_read m) >>
                        csr_id_write_callback csr_sstatus
                          (subrange_vec_dec
                             (lower_mstatus (legalize_sstatus_val m (sstatus_write_set_val m imm5)))
                             (Z.sub xlen 1) 0)) s1
                  = Some (tt, s1)).
    { rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr (mword_of_int 0) (sstatus_read m) s1)).
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true by reflexivity.
      apply (exec_csr_id_write_callback_sstatus _ _). }
    rewrite (exec_bind0_Some _ _ _ _ _ Hwc).
    apply exec_returnm.
  Qed.

  (* pop_off's restore: consumes the saved payload to re-arm the
     capability.  The MIRROR of the csrci leaf above: the pieces go IN and
     the arm is rebuilt whole, so the caller supplies the CELLS
     ([cpu_cells 0 true p]) and the counting token at level 1, and gets NO
     [intr_count] back -- the eighth the flip produces goes straight into
     [sie_arm true p]'s nested [cpu_hart 0 true p], which is where the
     enabled arm keeps it.  (Asking the caller for a whole [cpu_hart 0 true
     p] would ask it for that eighth at '1' while its own bundle still pins
     it at '0'.)  The already-enabled branch of [sie_cap] is refuted by
     sepc-cell exclusivity (the payload and a '1' arm can't coexist). *)
  (* ENABLING: pre index [trap_res true + n], post index [trap_res b + n].
     Re-enabling interrupts must PAY the trap reserve, and the caller pays it
     out of the very slots its own push_off/csrci freed.  See the seam header
     above [wp_csrci_sstatus_s_sconf]. *)
  Lemma wp_csrsi_sstatus_x0_s_sconf
      (pc : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    sie_cap_gpr kt m (trap_res true + n)%nat b p -∗
    intr_count 1 true -∗
    trap_csrs kt -∗
    cpu_priv 0 true p ∅ -∗
    cpu_claim p -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      sie_cap_gpr kt m (trap_res b + n)%nat true p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Htok Hcsrs Hcells Hclm Hpc Hinstr Hcont".
    (* the handler resource arrives inside [trap_csrs] now, not as
       [intr_count 1 true]'s payload -- which is what lets the flip re-form it
       at the SAME installed vector (the old shape had the spec in a separate
       persistent premise, about an unrelated [h]). *)
    iDestruct "Hcsrs" as "(Hsepcx & Hscausex & Hstvalx & Hsppc & Hhx & Hkptr)".
    (* REFUTE THE ALREADY-ENABLED CASE ABOVE THE FUNNEL, NOT INSIDE IT.  The
       contradiction is between the payload's sepc cell and the '1' arm's, and
       a register cell is PER HART ([reg_pointsto] takes a [CpuId]): held here,
       both are the entry hart's and cannot coexist; held inside the callback,
       the arm arrives at the REBOUND hart, where two sepc cells for two
       different harts are no contradiction at all.  So the case split has to
       happen before the funnel is consumed -- and that pays twice, because the
       surviving arm is [b = false], where [wp_next_off_intro] retires the hart
       question outright. *)
    destruct b.
    { iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      iDestruct "Harm" as "(Hq1 & Hhx' & Hkptr' & Hsepcx' & Hscausex' & Hstvalx' & Hsppc' & Hclmx' & Hcells')".
      iDestruct "Hsepcx" as (v1) "Hsepc1".
      iDestruct "Hsepcx'" as (v2) "Hsepc2".
      iDestruct (reg_pointsto_excl sepc v1 v2 with "Hsepc1 Hsepc2") as %[]. }
    iApply (wp_instr_s_sconf m (trap_res true + n)%nat false pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS))
              with "Hcg Hpc Hinstr").
    iApply wp_next_off_intro.
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Himm2 : eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false)
      by (vm_compute; reflexivity).
    iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
    (* ---- the real restore: interrupts were off ---- *)
    destruct (csrsi_sie_flip ms0 Hmsf) as (Hsie' & Hspp' & Hspie' & Hmsf').
    set (ms1 := legalize_sstatus_val ms0 (sstatus_write_set_val ms0 (mword_of_int 2))).
    (* the quarter comes straight out of the resource the caller handed in;
       this used to be an [inv_acc] on [intrN] whose body supplied it. *)
    iEval (rewrite /intr_res) in "Hhx".
    iDestruct "Hhx" as (handler vb) "(%Htvd & %Hsb & Hqi & Hstv & #Hspec)".
    iMod (sie_ghost_flip_on _ _ _ _ _ with "Hhalf Harm Htok Hqi") as "(Hhalf & Hqcap & Hqcnt & Hqi)".
    iDestruct (intr_res_intro handler _ Htvd Hsb with "Hqi Hstv Hspec") as "Hintr".
    iMod (reg_update _ mstatus _ ms1 with "Hreg Hms") as "[Hreg Hms]".
    iModIntro.
    iExists (set_reg s_pc mstatus ms1).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_csrsi_sstatus_x0 (mword_of_int 2) ms0 s_pc
               Lpriv_spc Lms_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS)
               ltac:(rewrite Lmisa_spc; exact HmisaU)
               Himm2). }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc mstatus ms1).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iEval (rewrite -Hsie') in "Hhalf".
    (* SPP and SPIE are untouched by an SIE flip, so the tie only needs
       re-expressing at the new mstatus -- no ghost movement. *)
    iDestruct (sret_tie_congr ms0 ms1 Hspp' Hspie' with "Hspp") as "Hspp".
    (* the carve is IDENTICAL on both sides -- [trap_res false + (trap_res
       true + n)] going in, [trap_res true + (trap_res false + n)] coming
       out, both [kv_frame_slots + n] by conversion -- so [iExact] on the
       untouched [Hstk] closes it with no split and no arithmetic. *)
    iAssert (sie_cap kt m (trap_res false + n)%nat true p)
      with "[Hqcap Hqcnt Hintr Hkptr Hsepcx Hscausex Hstvalx Hsppc Hclm Hstk Htr Hcells]" as "Hcap".
    { iSplitL "Hstk". { iExact "Hstk". }
      iFrame "Htr Hwit".
      iFrame "Hqcap Hintr Hkptr Hsepcx Hscausex Hstvalx Hsppc Hclm".
      (* [cpu_hart 0 true p] -- the cells the caller handed in, plus the
         count eighth the flip just produced at '1'. *)
      iSplitL "Hcells"; [ iExact "Hcells" | iExact "Hqcnt" ]. }
    iAssert sconf with "[Hpriv Hms Hhalf Hspp Hmiex Hmenvx]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
      iExists ms1. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf'. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
    iDestruct (wp_next_here with "Hcont") as "Hcont".
    iApply ("Hcont" $! ms0 with "[%] Hcg [$Hpc' $Hnpc]").
    { exact Hmsf. }
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE LEVEL-0 FLIPS: scheduler()'s INLINED intr_on()/intr_off() at the  *)
  (* head of its dispatch loop.  Both instructions have rd = x0, and both  *)
  (* stay at noff level 0 -- they are NOT the push/pop pair (which moves    *)
  (* k -> S k / S k -> k and hands the trap CSRs to [trap_csrs_pay]), but  *)
  (* an unbalanced enable/disable of the loop's own interrupt window.      *)
  (* ------------------------------------------------------------------- *)

  (* the x0 twin of [exec_execute_csrrci_sstatus_gen]: [csrci sstatus,imm]
     with rd = x0.  The wX_bits write-back takes the x0 NO-OP path, so the
     only state change is mstatus := the legalized cleared write (no rd
     cell is touched, hence no [uint rd <> 0] premise and no gpr update in
     the leaves below). *)
  Local Lemma exec_execute_csrrci_sstatus_x0 (imm5 : mword 5) (m : mword 64) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    register_lookup mstatus s.(sregs) = m ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec imm5 (zeros' 5) = false ->
    exec (execute (CSRImm (csr_sstatus, imm5, Regidx (mword_of_int 0), CSRRC))) s
      = Some (RETIRE_SUCCESS,
              set_reg s mstatus (legalize_sstatus_val m (sstatus_write_val m imm5))).
  Proof.
    intros Hpriv Hm HS HU Himm.
    change (execute (CSRImm (csr_sstatus, imm5, Regidx (mword_of_int 0), CSRRC)))
      with (execute_CSRImm csr_sstatus imm5 (Regidx (mword_of_int 0)) CSRRC).
    unfold execute_CSRImm.
    rewrite Himm.
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
    assert (Hwrite : exec (write_CSR csr_sstatus (sstatus_write_val m imm5)) s
                     = Some (Ok (subrange_vec_dec
                                   (lower_mstatus (legalize_sstatus_val m (sstatus_write_val m imm5)))
                                   (Z.sub xlen 1) 0),
                             set_reg s mstatus (legalize_sstatus_val m (sstatus_write_val m imm5)))).
    { rewrite (exec_write_CSR_sstatus (sstatus_write_val m imm5) s HS HU).
      rewrite Hm. reflexivity. }
    change (and_vec (sstatus_read m) (not_vec (zero_extend' 64 imm5)))
      with (sstatus_write_val m imm5).
    rewrite (exec_bind_Some _ _ _ _ _ Hwrite). cbn beta match.
    set (s1 := set_reg s mstatus (legalize_sstatus_val m (sstatus_write_val m imm5))).
    assert (Hwc : exec (wX_bits (Regidx (mword_of_int 0)) (sstatus_read m) >>
                        csr_id_write_callback csr_sstatus
                          (subrange_vec_dec
                             (lower_mstatus (legalize_sstatus_val m (sstatus_write_val m imm5)))
                             (Z.sub xlen 1) 0)) s1
                  = Some (tt, s1)).
    { rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr (mword_of_int 0) (sstatus_read m) s1)).
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true by reflexivity.
      apply (exec_csr_id_write_callback_sstatus _ _). }
    rewrite (exec_bind0_Some _ _ _ _ _ Hwc).
    apply exec_returnm.
  Qed.

  (* intr_on() at level 0, from EITHER base state.
       eb = false: the real '0'->'1' flip.  [intr_count 0 false] is just
     the count eighth at '0', so together with the persistent
     handler resource -- which rides inside [trap_csrs] -- the pop_off
     restore leaf applies verbatim (same four-piece ghost choreography:
     bundle half + capability eighth + count eighth + the [intr_res] quarter,
     with the whole of [trap_csrs] moving INTO the arm's '1' branch).
       eb = true: SIE is ALREADY '1' (ghost agreement between the arm's own
     eighth and the mstatus-tied half), so the write is idempotent on the
     bit and NO ghost moves; the legalized write still changes mstatus's
     term, but [csrsi_sie_flip] says the new word again has SIE = '1' and
     again satisfies [sconf_ms_facts], which is all the bundle needs.  The
     capability's '1' arm (trap CSRs + per-cpu cells + invariant copy) rides
     through untouched, and every one of the caller's [if eb then emp else _]
     premises is [emp] -- at [eb = true] all of that is ALREADY in the arm,
     which is exactly why the counting token is one of them. *)
  (* ------------------------------------------------------------------- *)
  (* THE IDEMPOTENT SET AT AN ALREADY-ENABLED ARM -- AND IT IS            *)
  (* INDEX-GENERIC, WHICH IS THE WHOLE POINT.                             *)
  (*                                                                      *)
  (* [csrsi sstatus,2] with SIE already '1' writes the bit that is already *)
  (* set: the ghost state does not move (the arm's own eighth and the      *)
  (* mstatus-tied half already agree at '1'), the '1' arm rides through    *)
  (* untouched, and -- decisively -- THE STACK CONJUNCT IS NEVER TOUCHED.  *)
  (* So this leaf holds at an ARBITRARY index [n]: pre and post are the    *)
  (* SAME [sie_cap_gpr m n true p], with no [trap_res true + _] shape      *)
  (* demanded of it and no [kv_frame_slots <= n] premise.                  *)
  (*                                                                      *)
  (* WHY THAT MATTERS, AND WHY THIS IS A SEPARATE LEMMA.                   *)
  (* [wp_csrsi_sstatus_x0_enable_s_sconf] below is the arm-GENERIC enable, *)
  (* and its contract must be stated at pre index [trap_res true + n] --   *)
  (* at [eb = false] it is a real 0 -> 1 flip and the reserve has to come  *)
  (* out of the index.  Instantiated at [eb = true] that shape is still    *)
  (* sound but it is a REQUIREMENT: it forces the caller's index to be at  *)
  (* least [kv_frame_slots], on top of whatever the enabled arm is already *)
  (* holding in reserve.  scheduler()'s loop head is exactly that caller   *)
  (* -- its [intr_on] is reached with interrupts already on from the       *)
  (* second round onwards -- and paying there would make [SpecScheduler]   *)
  (* demand [2 * kv_frame_slots + 20], a factor-of-two reserve, which is   *)
  (* the pathology the arm-dependent carve exists to remove.  Splitting    *)
  (* the idempotent case out gives that caller a leaf that moves nothing:  *)
  (* ONE reserve, paid once, at the single real enable.                    *)
  (*                                                                      *)
  (* The arm-generic enable's [eb = true] branch IS this lemma at          *)
  (* [n := trap_res true + n], so nothing is restated: the proof below is  *)
  (* the one that used to sit inline there.                                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_csrsi_sstatus_x0_idem_s_sconf
      (pc : mword 64) (m : regfile) (n : nat) :
    sie_cap_gpr kt m n true p -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS)) -∗
    wp_next true p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      sie_cap_gpr kt m n true p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n true pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Himm2 : eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false)
      by (vm_compute; reflexivity).
    (* [Hcap : sie_cap m n true] already -- the arm rides through untouched;
       the only thing wanted from it is its own eighth, for the agreement
       that pins the live bit at '1'. *)
    iDestruct "Hcap" as "(Hstk & Htr & (Hq1 & Harest) & #Hwit)".
    iDestruct (ghost_var_agree with "Hhalf Hq1") as %Hb1.
    iAssert (sie_cap kt (CID := CID) m n true p) with "[Hstk Htr Hq1 Harest]" as "Hcap".
    { iFrame "Hstk Htr Hq1 Harest Hwit". }
    destruct (csrsi_sie_flip ms0 Hmsf) as (Hsie' & Hspp' & Hspie' & Hmsf').
    set (ms1 := legalize_sstatus_val ms0 (sstatus_write_set_val ms0 (mword_of_int 2))).
    iMod (reg_update _ mstatus _ ms1 with "Hreg Hms") as "[Hreg Hms]".
    iModIntro.
    iExists (set_reg s_pc mstatus ms1).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_csrsi_sstatus_x0 (mword_of_int 2) ms0 s_pc
               Lpriv_spc Lms_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS)
               ltac:(rewrite Lmisa_spc; exact HmisaU)
               Himm2). }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc mstatus ms1).(sregs)
                   = add_vec_int pc 4).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iEval (rewrite Hb1) in "Hhalf".
    iEval (rewrite -Hsie') in "Hhalf".
      (* SPP and SPIE are untouched by an SIE flip, so the tie only needs
         re-expressing at the new mstatus -- no ghost movement. *)
      iDestruct (sret_tie_congr ms0 ms1 Hspp' Hspie' with "Hspp") as "Hspp".
    iAssert (sconf (CID := CID)) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenvx]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
      iExists ms1. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf'. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
    iSpecialize ("Hcont" $! CID with "[]"); [iPureIntro; done|].
    iApply ("Hcont" $! ms0 with "[%] Hcg [$Hpc' $Hnpc]").
    { exact Hmsf. }
  Qed.

  (* ENABLING, so the same index discipline as [wp_csrsi_sstatus_x0_s_sconf]:
     pre [trap_res true + n], post [trap_res eb + n].  At [eb = true] the two
     coincide (the write is idempotent and the reserve rides through); at
     [eb = false] this delegates to that leaf at [b := false], whose pre/post
     indices are then literally these. *)
  Lemma wp_csrsi_sstatus_x0_enable_s_sconf
      (pc : mword 64) (eb : bool) (m : regfile) (n : nat) :
    sie_cap_gpr kt m (trap_res true + n)%nat eb p -∗
    (if eb then emp else intr_count 0 false) -∗
    (if eb then emp else trap_csrs kt) -∗
    (if eb then emp else cpu_priv 0 true p ∅) -∗
    cpu_claim_ext eb p -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS)) -∗
    wp_next eb p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      sie_cap_gpr kt m (trap_res eb + n)%nat true p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    destruct eb.
    2:{ (* ---- base state DISABLED: the real flip, via the restore leaf ---- *)
        iIntros "Hcg Hcnt Hcsrs Hcells Hclm Hpc Hinstr Hcont".
        iApply (wp_csrsi_sstatus_x0_s_sconf pc m n false
                  with "Hcg [Hcnt] Hcsrs Hcells Hclm Hpc Hinstr Hcont").
        iApply (intr_count_pack_S_on 0 with "Hcnt"). }
    (* ---- base state ENABLED: idempotent on SIE, ghosts stand still.  This
           IS [wp_csrsi_sstatus_x0_idem_s_sconf] at index [trap_res true + n];
           the reserve summand is inert here (nothing reads the index), which
           is precisely why that lemma can be stated without it. ---- *)
    iIntros "Hcg _ _ _ _ Hpc Hinstr Hcont".
    iApply (wp_csrsi_sstatus_x0_idem_s_sconf pc m (trap_res true + n)%nat
              with "Hcg Hpc Hinstr Hcont").
  Qed.

  (* intr_off() at level 0, FROM enabled: the '1'->'0' flip of
     [wp_csrci_sstatus_s_sconf] with rd = x0 and no level push.  Same
     choreography ([sie_ghost_flip_off] on all four pieces -- bundle half +
     capability eighth + count eighth + the [intr_res] quarter -- re-forming
     [intr_res] at the same installed vector), but the freed '1'-arm payload
     lands DIFFERENTLY: the trap CSRs go straight to the caller (level 0 with
     a now-disabled base owes them explicitly), [intr_res] RIDES OUT WITH
     THEM (it used to be a persistent [intr_inv] copy that could simply be
     dropped, because the caller kept its own [intr_handler_avail]; owned,
     there is exactly one and the caller must get it), and the count eighth
     comes back at [sie_bit false] -- i.e. [intr_count 0 false], not
     [intr_count 1 _].

     THE TWO EIGHTHS ARE NOT THE CALLER'S TO SUPPLY AT [b = true].  This
     leaf used to demand a separate [intr_count 0 true] BESIDE the bundle,
     and hand back [cpu_hart 0 true p] (which CONTAINS an [intr_count 0
     true]) beside an [intr_count 0 false] -- the same eighth at two
     values, which the comment on [cpu_priv_pay] above forbids.  Nobody
     could hold the premise: at [b = true] the arm owns BOTH eighths
     ([sie_arm]'s own plus the one inside [cpu_hart 0 true p]), and at
     [b = false] the last branch below refutes it outright, so the contract
     was vacuous at every index.  It now takes [intr_count_pre b 0 true]
     (the pure fact at the enabled arm, the token at the disabled one) and
     returns the freed cells as [cpu_priv_pay b p], exactly like its
     sibling [wp_csrci_sstatus_s_sconf]: the flip's second eighth is taken
     out of the arm's own [cpu_hart], not out of the caller. *)
  (* DISABLING, same index discipline as [wp_csrci_sstatus_s_sconf]: pre [n],
     post [trap_res b + n].  Reachable only at [b = true] (the [b = false] arm
     is refuted below), where the post index is [kv_frame_slots + n] -- the
     scheduler's inlined intr_off() freeing its own reserve. *)
  Lemma wp_csrci_sstatus_x0_s_sconf
      (pc : mword 64) (m : regfile) (n : nat) (b : bool) :
    sie_cap_gpr kt m n b p -∗
    intr_count_pre b 0 true -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRC)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      sie_cap_gpr kt m (trap_res b + n)%nat false p -∗
      intr_count 0 false -∗
      trap_csrs kt -∗
      (* THE RUNNING CLAIM, out of the arm along with the trap CSRs.  It used
         to be DROPPED here, which made this leaf lose a resource its
         push_off sibling [wp_csrci_sstatus_s_sconf] hands back (as
         [cpu_claim_pay k eb p]) -- sound, but it left every caller of
         [WpIntrOff.wp_intr_off_lvl0_s_sconf] unable to reassemble a bundle
         containing [cpu_claim].  usertrap is the first caller that notices:
         it reaches prepare_return at [b = true] on the syscall arm and its
         own boundary owes the claim back.  Unconditional rather than
         [cpu_claim_pay 0 true p] because this leaf's [b = false] arm is
         refuted above, so the arm always existed and always owned it. *)
      cpu_claim p -∗
      cpu_priv_pay b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hcnt Hpc Hinstr Hcont".
    (* REFUTE THE ALREADY-DISABLED CASE ABOVE THE FUNNEL: the count eighth at
       '1' contradicts the capability's '0' eighth, and both eighths are the
       ENTRY hart's while the caller still holds them.  Inside the callback the
       arm arrives at the REBOUND hart and two eighths of two different harts'
       ghosts agree about nothing. *)
    destruct b.
    2: { iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
         iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
         iDestruct (intr_count_pre_off with "Hcnt") as "Hcnt".
         iDestruct (ghost_var_agree with "Hcnt Harm") as %Hbad.
         exfalso. apply (f_equal (@bv_unsigned _)) in Hbad.
         vm_compute in Hbad. discriminate. }
    iApply (wp_instr_s_sconf m n true pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRC))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Himm2 : eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false)
      by (vm_compute; reflexivity).
    iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
    (* the only reachable arm: interrupts were ON ---- the flip is real, and
       both eighths are in the arm (its own, and the one inside [cpu_hart 0
       true p]), which the callback delivers at the rebound hart. *)
    iDestruct "Harm" as "(Hq1 & Hhx & Hkptr & Hsepcx & Hscausex & Hstvalx & Hsppc & Hclmx & (Hcells & Hc1))".
    iClear "Hcnt".
    iDestruct (intr_count_get_on 0 true with "Hq1 Hc1") as "(_ & Hq1 & Hcnt)".
    destruct (csrci_sie_flip ms0 Hmsf) as (Hsie' & Hspp' & Hspie' & Hmsf').
    set (ms1 := legalize_sstatus_val ms0 (sstatus_write_val ms0 (mword_of_int 2))).
    (* the handler resource: take the quarter out, flip, re-form.  This used
       to open [intrN] across the step and re-seal it. *)
    iEval (rewrite /intr_res) in "Hhx".
    iDestruct "Hhx" as (handler vb) "(%Htvd & %Hsb & Hqi & Hstv & #Hspec)".
    iMod (sie_ghost_flip_off _ _ _ _ _ with "Hhalf Hq1 Hcnt Hqi")
      as "(Hhalf & Hq & Htok & Hqi)".
    iDestruct (intr_res_intro handler _ Htvd Hsb with "Hqi Hstv Hspec") as "Hintr".
    iMod (reg_update _ mstatus _ ms1 with "Hreg Hms") as "[Hreg Hms]".
    iModIntro.
    iExists (set_reg s_pc mstatus ms1).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_csrrci_sstatus_x0 (mword_of_int 2) ms0 s_pc
               Lpriv_spc Lms_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS)
               ltac:(rewrite Lmisa_spc; exact HmisaU)
               Himm2). }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc mstatus ms1).(sregs)
                   = add_vec_int pc 4).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iEval (rewrite -Hsie') in "Hhalf".
    (* SPP and SPIE are untouched by an SIE flip, so the tie only needs
       re-expressing at the new mstatus -- no ghost movement. *)
    iDestruct (sret_tie_congr ms0 ms1 Hspp' Hspie' with "Hspp") as "Hspp".
    iAssert (sie_cap kt (CID := CID) m (trap_res true + n)%nat false p) with "[Hstk Htr Hq]" as "Hcap".
    { iSplitL "Hstk"; [iExact "Hstk" |].
      iFrame "Htr Hwit". iExact "Hq". }
    iAssert (sconf (CID := CID)) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenvx]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
      iExists ms1. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf'. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
    iSpecialize ("Hcont" $! CID with "[]"); [iPureIntro; done|].
    iApply ("Hcont" $! ms0 with "[%] Hcg [Htok]
                          [Hsepcx Hscausex Hstvalx Hsppc Hintr Hkptr] [Hclmx] [Hcells] [$Hpc' $Hnpc]").
    { exact Hmsf. }
    { iExact "Htok". }
    { iFrame "Hsepcx Hscausex Hstvalx Hsppc Hintr Hkptr". }
    { iExact "Hclmx". }
    { rewrite /cpu_priv_pay. iExact "Hcells". }
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE IDEMPOTENT CLEAR AT AN ALREADY-DISABLED ARM -- the exact mirror  *)
  (* of [wp_csrsi_sstatus_x0_idem_s_sconf] above.                          *)
  (*                                                                      *)
  (* [csrci sstatus,2] with SIE already '0' clears the bit that is already *)
  (* clear: the ghost state does not move (the disabled arm's eighth and   *)
  (* the mstatus-tied half already agree at '0'), the arm rides through     *)
  (* untouched, and the stack conjunct is never touched -- so pre and post *)
  (* are the SAME [sie_cap_gpr m n false p] at an ARBITRARY index [n],     *)
  (* with no reserve to move and nothing to pay out.                       *)
  (*                                                                      *)
  (* WHY IT IS NEEDED.  [wp_csrci_sstatus_x0_s_sconf] REFUTES its          *)
  (* [b = false] arm (its [intr_count_pre] premise is unsatisfiable there),*)
  (* so an intr_off() reached with interrupts ALREADY off had no leaf at    *)
  (* all.  prepare_return is exactly such a caller: usertrap reaches it     *)
  (* with SIE = 0 on the devintr / vmfault / unexpected-scause paths, and   *)
  (* only the syscall path (which does its own [csrsi] first) arrives       *)
  (* enabled.  [WpIntrOff.wp_intr_off_lvl0_s_sconf] is the index-generic    *)
  (* composite the two arms feed.                                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_csrci_sstatus_x0_idem_s_sconf
      (pc : mword 64) (m : regfile) (n : nat) :
    sie_cap_gpr kt m n false p -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRC)) -∗
    wp_next false p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      sie_cap_gpr kt m n false p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n false pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRC))
              with "Hcg Hpc Hinstr").
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Himm2 : eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false)
      by (vm_compute; reflexivity).
    (* the disabled arm IS its own eighth; the agreement pins the live bit
       at '0', which is what makes the write idempotent. *)
    iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
    iDestruct (ghost_var_agree with "Hhalf Harm") as %Hb0.
    iAssert (sie_cap kt (CID := CID) m n false p) with "[Hstk Htr Harm]" as "Hcap".
    { iFrame "Hstk Htr Harm Hwit". }
    destruct (csrci_sie_flip ms0 Hmsf) as (Hsie' & Hspp' & Hspie' & Hmsf').
    set (ms1 := legalize_sstatus_val ms0 (sstatus_write_val ms0 (mword_of_int 2))).
    iMod (reg_update _ mstatus _ ms1 with "Hreg Hms") as "[Hreg Hms]".
    iModIntro.
    iExists (set_reg s_pc mstatus ms1).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_csrrci_sstatus_x0 (mword_of_int 2) ms0 s_pc
               Lpriv_spc Lms_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS)
               ltac:(rewrite Lmisa_spc; exact HmisaU)
               Himm2). }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc mstatus ms1).(sregs)
                   = add_vec_int pc 4).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iEval (rewrite Hb0) in "Hhalf".
    iEval (rewrite -Hsie') in "Hhalf".
    iDestruct (sret_tie_congr ms0 ms1 Hspp' Hspie' with "Hspp") as "Hspp".
    iAssert (sconf (CID := CID)) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenvx]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
      iExists ms1. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf'. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
    iSpecialize ("Hcont" $! CID with "[]"); [iPureIntro; done|].
    iApply ("Hcont" $! ms0 with "[%] Hcg [$Hpc' $Hnpc]").
    { exact Hmsf. }
  Qed.

  (* ===================================================================== *)
  (* THE PINNED INDEX: WHY THE SEVEN LEAVES BELOW SAY [false] AND NOT [b].  *)
  (*                                                                        *)
  (* Every leaf from here to the end of the section threads a PER-HART       *)
  (* resource EXPLICITLY, beside the bundle: a trap-CSR cell ([stvec],       *)
  (* [sepc], [scause], [stval] -- each a single register of THIS hart), or   *)
  (* the travelling SPP/SPIE ghost half ([sret_bits], i.e.                   *)
  (* [era_sp{p,ie}_name cpu_id]).  Their postconditions live under           *)
  (* [wp_next _ p (fun CID => ...)], whose binder shadows the ambient [CID]  *)
  (* -- so every resource written inside the continuation is about the hart  *)
  (* execution RESUMES on, not the hart the instruction started on           *)
  (* (WpNext.v).                                                            *)
  (*                                                                        *)
  (* At [b = true] a trap can be taken AT THIS INSTRUCTION and the thread    *)
  (* resumed on a different hart.  A [b]-generic version of these leaves     *)
  (* would then read/write the ENTRY hart's CSR (that is the only cell the   *)
  (* premise could possibly be about -- it is the one the step executes on)  *)
  (* and hand it straight back as the RESUMING hart's.  So at [b = true]     *)
  (* these postconditions are FALSE, not merely unprovable: they equate two  *)
  (* different harts' state.  Nothing exploits that today only because a     *)
  (* trap currently returns on the hart it came from; it stops being an      *)
  (* accident and starts being a soundness hole the moment migration is      *)
  (* real.  Pinning the index at the literal [false] is therefore a          *)
  (* correction, not a restriction -- every call site was already at         *)
  (* [false] (ProofTrapinithart, ProofKerneltrapParts, ProofDevintr: the     *)
  (* trap-handler tier, which runs with interrupts off by construction).     *)
  (*                                                                        *)
  (* DO NOT "GENERALISE" THE INDEX BACK.  If you need one of these           *)
  (* instructions at [b = true], the missing piece is not a weaker index:    *)
  (* it is a statement that says which hart each cell belongs to, i.e. the   *)
  (* [sie_cap] enabled arm's own existentially-quantified trap CSRs, or a    *)
  (* payload transported across the crossing the way the csrci/csrsi flip    *)
  (* family does it.                                                        *)
  (*                                                                        *)
  (* The [wp_next false p (fun CID => ...)] WRAPPER STAYS.  It is not the    *)
  (* problem (at [false] it collapses by [wp_next_off]), and every call site *)
  (* discharges it with [iApply wp_next_off_intro], which needs the head to  *)
  (* still be [wp_next].                                                    *)
  (*                                                                        *)
  (* THIS DOES NOT APPLY TO THE SIE-FLIP FAMILY ABOVE                        *)
  (* ([wp_csrci_sstatus_s_sconf] & co.), which is legitimately [b]-generic:  *)
  (* the write that DISABLES interrupts is genuinely applied at [b = true]   *)
  (* on its input side (pinning it would make push_off unstatable), and it   *)
  (* handles the crossing through its [b]-guarded payloads                   *)
  (* ([intr_count_pre], [trap_csrs_pay], [cpu_claim_pay], [cpu_priv_pay]).  *)
  (* Nor to [wp_csrr_sstatus_s_sconf], which threads nothing extra (its      *)
  (* [hart_state] cell comes OUT of the bundle and returns INTO              *)
  (* [sie_cap_gpr_at]), nor to [WpSconfTimer]'s [wp_csrr_time_s_sconf],      *)
  (* which owns no cell at all.                                             *)
  (* ===================================================================== *)

  (* ---- csrw stvec,rs1 -- installs the trap vector.  The [stvec] cell is
     threaded EXPLICITLY: only the Bare arm of the translation slot owns it,
     so between kvminithart and trapinithart it rides client-side.  The
     written word lands VERBATIM; the one premise on it is that its MODE
     field is not the reserved encoding, which is exactly what
     [legalize_tvec] would otherwise silently rewrite.  Taking the value as
     an explicit [wval] (rather than leaving [m !!! Regidx rs1] in the
     post) keeps the stored term closed at the call site.

     THE INDEX IS THE LITERAL [false], not a parameter -- see [THE PINNED
     INDEX] above.  At [b = true] the post would hand [stvec ↦ᵣ wval] back
     as the RESUMING hart's stvec while the instruction wrote the ENTRY
     hart's, which is FALSE rather than unprovable. ---- *)
  Lemma wp_csrw_stvec_s_sconf
      (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (n : nat) (tv0 wval : mword 64) :
    uint rs1 <> 0 ->
    rget m rs1 = wval ->
    trapVectorMode_forwards (_get_Mtvec_Mode wval) <> TV_Reserved ->
    sie_cap_gpr kt m n false p -∗
    stvec ↦ᵣ tv0 -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_stvec, Regidx rs1, zreg, CSRRW)) -∗
    wp_next false p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n false p -∗
      stvec ↦ᵣ wval -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hwval Hmode) "Hcg Hstv Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n false pc false
              (CSRReg (csr_stvec, Regidx rs1, zreg, CSRRW))
              with "Hcg Hpc Hinstr").
    (* INTERRUPTS ARE OFF AT THIS LEAF, so the funnel's hart-generic obligation
       is discharged by [wp_next]'s OWN introduction rule at the ambient hart --
       the same [wp_next_off_intro] a b = false leaf already uses for its own
       conclusion.  Nothing is renamed and nothing is substituted: the body below
       is the pre-move proof VERBATIM. *)
    iApply wp_next_off_intro.
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & _ & %HmisaS & _)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hstv")  as %Lstv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    (* the rs1 value: the pinned gpr file has it in the step state *)
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hr1c Hfb]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hr1c") as %Lva.
    iDestruct ("Hfb" with "Hr1c") as "Hfile".
    assert (Lrs1 : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                   = wval).
    { rewrite -Hwval. unfold rget. rewrite rf_lookup. rewrite -Lva.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    iMod (reg_update _ stvec _ wval with "Hreg Hstv") as "[Hreg Hstv]".
    iModIntro.
    iExists (set_reg s_pc stvec wval).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      rewrite <- Lrs1.
      apply (exec_execute_csrw_stvec_S rs1 s_pc Hrs1 Lpriv_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS)).
      rewrite Lrs1. exact Hmode. }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc stvec wval).(sregs)
                   = add_vec_int pc 4).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hminv $Hpriv $Hmsx $Hmiex $Hmenvx] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg Hstv [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* ---- csrw sstatus,rs1 -- THE S-STATUS RESTORE, and the one leaf whose
     postcondition EXPOSES mstatus.

     THE WRITTEN WORD IS ABSTRACT, carrying the five field premises
     [flip_core] wants.  It was once taken as [sstatus_read ms0] for a
     well-formed source mstatus, on the grounds that a RESTORE (kerneltrap
     writing back the sstatus an earlier csrr saved) is the only way the
     instruction is used -- and that stopped being true at prepare_return,
     whose word is a read-modify-write:

         x = r_sstatus(); x &= ~SSTATUS_SPP; x |= SSTATUS_SPIE; w_sstatus(x);

     No mstatus [ms0] has [sstatus_read ms0 = x] for free there; proving one
     does means a whole-word identity over [lower_mstatus]'s nest of slice
     updates, where the five field facts are each three lines
     ([WpGprCsrwC]'s [bv_extract_and] / [bv_extract_or] block).  So the
     restore shape is now the COROLLARY [wp_csrw_sstatus_s_sconf] below,
     which discharges the five from [sconf_ms_facts ms0] exactly as this
     leaf's body used to.

     THE WRITE MUST NOT MOVE SIE -- premise [_get_Sstatus_SIE wval = sie_bit
     b].  A restore whose saved SIE differs from the live one would have to
     move all THREE ghost pieces and re-seal the interrupt invariant; that
     is what the csrci/csrsi flip leaves are for, and duplicating their
     choreography here would be the wrong shape.  At the trap-handler use
     the premise is free: the trap cleared SIE, nothing in the handler
     turned it back on, and the saved word was read after the clear.

     The post hands back [sie_cap_gpr_at msf] -- the mstatus-EXPOSING
     flavour (IntrDefs) -- because SPP and SPIE are the entire point: they
     are what kernelvec's [sret] reads.  Close it with
     [sie_cap_gpr_at_close] as soon as they have been recorded.

     THE INDEX IS THE LITERAL [false], not a parameter -- see [THE PINNED
     INDEX] above.  Here the crossing would corrupt a GHOST rather than a
     cell: [sret_bits] is [era_sp{p,ie}_name cpu_id], the travelling half of
     THIS hart's SPP/SPIE tie, and the post re-ties it at the [msf] this
     instruction installed.  At [b = true] that hands the entry hart's
     freshly-tied half back as the RESUMING hart's -- FALSE, not merely
     unprovable.  (At [b = true] the premise was in any case vacuous: the
     enabled arm owns the travelling half, so no caller could supply it --
     but a vacuous premise in front of a false conclusion is exactly the
     shape that survives a future refactor and then bites, which is why the
     index is pinned rather than left to the arm.)  The SIE premise reads
     [sie_bit false] for the same reason, and is what says the restore does
     not move SIE. ---- *)
  Lemma wp_csrw_sstatus_val_s_sconf
      (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (n : nat) (wval : mword 64) (vspp vspie : mword 1) :
    uint rs1 <> 0 ->
    rget m rs1 = wval ->
    _get_Sstatus_SIE wval = sie_bit false ->
    (* the four S-fields [sconf] PINS: the write must not disturb them, and
       since [sconf_ms_facts] fixes each to a constant the premise can be
       stated against that constant rather than against the live mstatus
       (which the caller cannot see). *)
    _get_Sstatus_MXR wval = ('b"0" : mword 1) ->
    _get_Sstatus_FS  wval = extStatus_map_forwards Off ->
    _get_Sstatus_VS  wval = extStatus_map_forwards Off ->
    _get_Sstatus_XS  wval = extStatus_map_forwards Off ->
    sie_cap_gpr kt m n false p -∗
    (* THE TRAVELLING SPP HALF.  This is the one instruction that MOVES SPP,
       so it needs both halves: the tie inside [sconf] and this one, which
       interrupts-off code holds (it rides in [trap_csrs]). *)
    sret_bits vspp vspie -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_sstatus, Regidx rs1, zreg, CSRRW)) -∗
    wp_next false p (fun (CID : CpuId) =>
      ∀ msf : mword 64,
      ⌜ _get_Mstatus_SIE  msf = sie_bit false ⌝ -∗
      ⌜ _get_Mstatus_SPP  msf = _get_Sstatus_SPP  wval ⌝ -∗
      ⌜ _get_Mstatus_SPIE msf = _get_Sstatus_SPIE wval ⌝ -∗
      sie_cap_gpr_at kt msf m n false p -∗
      sret_bits (_get_Mstatus_SPP msf) (_get_Mstatus_SPIE msf) -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hwval HWsie HWmxr0 HWfs0 HWvs0 HWxs0) "Hcg Hsppc Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n false pc false
              (CSRReg (csr_sstatus, Regidx rs1, zreg, CSRRW))
              with "Hcg Hpc Hinstr").
    (* INTERRUPTS ARE OFF AT THIS LEAF, so the funnel's hart-generic obligation
       is discharged by [wp_next]'s OWN introduction rule at the ambient hart --
       the same [wp_next_off_intro] a b = false leaf already uses for its own
       conclusion.  Nothing is renamed and nothing is substituted: the body below
       is the pre-move proof VERBATIM. *)
    iApply wp_next_off_intro.
    iIntros (sigma Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms) "(Hms & Hhalf & Hspp & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & _ & %HmisaS & %HmisaC & %HmisaU & _)".
    (* the live SIE bit is the arm index *)
    iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
    iDestruct (sie_arm_half_agree false p ms with "Hhalf Harm") as %Hsie_ms.
    (* the four field equalities [flip_core] wants: the premises pin [wval]'s
       side to a constant, [sconf_ms_facts] pins [ms]'s side to the same one. *)
    pose proof Hmsf as (_ & _ & HMXR & _ & HXS & HFS & HVS & _ & _ & _).
    apply eq_vec_true_iff in HMXR.
    assert (HWmxr : _get_Sstatus_MXR wval = _get_Mstatus_MXR ms)
      by (rewrite HWmxr0 HMXR; reflexivity).
    assert (HWfs : _get_Sstatus_FS wval = _get_Mstatus_FS ms)
      by (rewrite HWfs0 HFS; reflexivity).
    assert (HWvs : _get_Sstatus_VS wval = _get_Mstatus_VS ms)
      by (rewrite HWvs0 HVS; reflexivity).
    assert (HWxs : _get_Sstatus_XS wval = _get_Mstatus_XS ms)
      by (rewrite HWxs0 HXS; reflexivity).
    set (ms1 := legalize_sstatus_val ms wval).
    destruct (flip_core ms wval (sie_bit false)
                Hmsf HWsie HWmxr HWfs HWvs HWxs)
      as (Hf_sie & Hf_spp & Hf_spie & Hf_facts).
    fold ms1 in Hf_sie, Hf_spp, Hf_spie, Hf_facts.
    (* the ghost half does not move: both indices are [sie_bit false] *)
    assert (Hhalf_eq : _get_Mstatus_SIE ms1 = _get_Mstatus_SIE ms)
      by (rewrite Hf_sie Hsie_ms; reflexivity).
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg sigma nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hr1c Hfb]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hr1c") as %Lva.
    iDestruct ("Hfb" with "Hr1c") as "Hfile".
    assert (Lrs1 : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                   = wval).
    { rewrite -Hwval. unfold rget. rewrite rf_lookup. rewrite -Lva.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    iMod (reg_update _ mstatus _ ms1 with "Hreg Hms") as "[Hreg Hms]".
    (* re-tie SPP to the mstatus the write installs -- the only leaf that has
       to, and the only one holding both halves. *)
    iMod (sret_bits_update (_get_Mstatus_SPP ms) (_get_Mstatus_SPIE ms)
            vspp vspie (_get_Mstatus_SPP ms1) (_get_Mstatus_SPIE ms1)
            with "Hspp Hsppc") as "[Hspp Hsppc]".
    iModIntro.
    iExists (set_reg s_pc mstatus ms1).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      unfold ms1. rewrite <- Lrs1.
      apply (exec_execute_csrw_sstatus_S rs1 ms s_pc Hrs1 Lpriv_spc Lms_spc);
        rewrite Lmisa_spc; [ exact HmisaS | exact HmisaU ]. }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc mstatus ms1).(sregs)
                   = add_vec_int pc 4).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iEval (rewrite -Hhalf_eq) in "Hhalf".
    iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
    iApply ("Hcont" $! ms1 with "[%] [%] [%] [Hhs' Hpriv Hmiex Hmenvx Hms Hhalf Hspp Hstk Htr Harm Hfile] Hsppc [$Hpc' $Hnpc]").
    { exact Hf_sie. }
    { exact Hf_spp. }
    { exact Hf_spie. }
    rewrite /sie_cap_gpr_at /sconf_at /sconf_msown.
    iFrame "Hhs'".
    iSplitL "Hms Hhalf Hspp Hpriv Hmiex Hmenvx".
    { iSplitL "Hms Hhalf Hspp".
      { iFrame "Hms Hhalf Hspp". iPureIntro. exact Hf_facts. }
      iIntros (ms') "(Hms' & Hhalf' & Hspp' & %Hmsf')".
      iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
      iExists ms'. iFrame "Hms' Hhalf' Hspp'". iPureIntro. exact Hmsf'. }
    rewrite /sie_cap. iFrame "Hstk Htr Harm Hwit Hfile".
  Qed.

  (* ---- THE RESTORE SHAPE: the written word is one an earlier [csrr
     sstatus] read, so the five field premises above come from that mstatus'
     [sconf_ms_facts] and the S-view/M-view field agreement
     ([WpGprCsrwC.sX_lower]).  This is kerneltrap's [csrw sstatus,s1] and
     kernelvec's route to [sret]; the statement is unchanged from before the
     leaf above was generalized, so its call sites are untouched. ---- *)
  Lemma wp_csrw_sstatus_s_sconf
      (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (n : nat) (ms0 : mword 64) (vspp vspie : mword 1) :
    uint rs1 <> 0 ->
    rget m rs1 = sstatus_read ms0 ->
    sconf_ms_facts ms0 ->
    _get_Mstatus_SIE ms0 = sie_bit false ->
    sie_cap_gpr kt m n false p -∗
    sret_bits vspp vspie -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_sstatus, Regidx rs1, zreg, CSRRW)) -∗
    wp_next false p (fun (CID : CpuId) =>
      ∀ msf : mword 64,
      ⌜ _get_Mstatus_SIE  msf = _get_Mstatus_SIE  ms0 ⌝ -∗
      ⌜ _get_Mstatus_SPP  msf = _get_Mstatus_SPP  ms0 ⌝ -∗
      ⌜ _get_Mstatus_SPIE msf = _get_Mstatus_SPIE ms0 ⌝ -∗
      sie_cap_gpr_at kt msf m n false p -∗
      sret_bits (_get_Mstatus_SPP msf) (_get_Mstatus_SPIE msf) -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hwval Hms0f Hsie0) "Hcg Hsppc Hpc Hinstr Hcont".
    pose proof Hms0f as (_ & _ & HMXR0 & _ & HXS0 & HFS0 & HVS0 & _ & _ & _).
    apply eq_vec_true_iff in HMXR0.
    (* the S-view of a lowered mstatus agrees field by field with its M-view *)
    assert (HWsie : _get_Sstatus_SIE (sstatus_read ms0) = _get_Mstatus_SIE ms0)
      by (unfold sstatus_read; rewrite WpGprCsrwC.subrange_full; apply WpGprCsrwC.sSIE_lower).
    assert (HWspp : _get_Sstatus_SPP (sstatus_read ms0) = _get_Mstatus_SPP ms0)
      by (unfold sstatus_read; rewrite WpGprCsrwC.subrange_full; apply WpGprCsrwC.sSPP_lower).
    assert (HWspie : _get_Sstatus_SPIE (sstatus_read ms0) = _get_Mstatus_SPIE ms0)
      by (unfold sstatus_read; rewrite WpGprCsrwC.subrange_full; apply WpGprCsrwC.sSPIE_lower).
    iApply (wp_csrw_sstatus_val_s_sconf pc rs1 m n (sstatus_read ms0) vspp vspie
              Hrs1 Hwval
              ltac:(rewrite HWsie; exact Hsie0)
              ltac:(unfold sstatus_read; rewrite WpGprCsrwC.subrange_full
                      WpGprCsrwC.sMXR_lower; exact HMXR0)
              ltac:(unfold sstatus_read; rewrite WpGprCsrwC.subrange_full
                      WpGprCsrwC.sFS_lower; exact HFS0)
              ltac:(unfold sstatus_read; rewrite WpGprCsrwC.subrange_full
                      WpGprCsrwC.sVS_lower; exact HVS0)
              ltac:(unfold sstatus_read; rewrite WpGprCsrwC.subrange_full
                      WpGprCsrwC.sXS_lower; exact HXS0)
              with "Hcg Hsppc Hpc Hinstr [-]").
    iApply wp_next_off_intro.
    iIntros (msf) "%Hf_sie %Hf_spp %Hf_spie Hcgat Hsppc Hpc".
    iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
    iApply ("Hcont" $! msf with "[%] [%] [%] Hcgat Hsppc Hpc").
    - rewrite Hf_sie Hsie0. reflexivity.
    - rewrite Hf_spp HWspp. reflexivity.
    - rewrite Hf_spie HWspie. reflexivity.
  Qed.

  (* ---- csrw sepc,rs1 -- restores the trapped pc.  The [sepc] cell is
     threaded EXPLICITLY, exactly as stvec's is at [wp_csrw_stvec_s_sconf]
     and for the same reason: at [b = false] nothing in the ambient bundle
     owns it (the enabled arm's copy exists only at [b = true], and a
     handler running with interrupts off holds the trap CSRs itself).
     Unlike stvec's, the written word does NOT land verbatim: sepc's write
     legalizes through [mepc_val], so the post-value carries the wrapper --
     a caller writing back a 2-aligned epc collapses it.

     THE INDEX IS THE LITERAL [false], not a parameter -- see [THE PINNED
     INDEX] above.  At [b = true] the post would hand [sepc ↦ᵣ mepc_val
     wval] back as the RESUMING hart's sepc while the instruction wrote the
     ENTRY hart's, which is FALSE rather than unprovable -- and sepc is the
     worst cell to get wrong, since it is what the eventual [sret] jumps
     to. ---- *)
  Lemma wp_csrw_sepc_s_sconf
      (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (n : nat) (ep0 wval : mword 64) :
    uint rs1 <> 0 ->
    rget m rs1 = wval ->
    sie_cap_gpr kt m n false p -∗
    sepc ↦ᵣ ep0 -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_sepc, Regidx rs1, zreg, CSRRW)) -∗
    wp_next false p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n false p -∗
      sepc ↦ᵣ mepc_val wval -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hwval) "Hcg Hsepc Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n false pc false
              (CSRReg (csr_sepc, Regidx rs1, zreg, CSRRW))
              with "Hcg Hpc Hinstr").
    (* INTERRUPTS ARE OFF AT THIS LEAF, so the funnel's hart-generic obligation
       is discharged by [wp_next]'s OWN introduction rule at the ambient hart --
       the same [wp_next_off_intro] a b = false leaf already uses for its own
       conclusion.  Nothing is renamed and nothing is substituted: the body below
       is the pre-move proof VERBATIM. *)
    iApply wp_next_off_intro.
    iIntros (sigma Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & _ & %HmisaS & _)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hsepc") as %Lsepc.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg sigma nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hr1c Hfb]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hr1c") as %Lva.
    iDestruct ("Hfb" with "Hr1c") as "Hfile".
    assert (Lrs1 : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                   = wval).
    { rewrite -Hwval. unfold rget. rewrite rf_lookup. rewrite -Lva.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    iMod (reg_update _ sepc _ (mepc_val wval) with "Hreg Hsepc") as "[Hreg Hsepc]".
    iModIntro.
    iExists (set_reg s_pc sepc (mepc_val wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      rewrite <- Lrs1.
      apply (exec_execute_csrw_sepc_S rs1 s_pc Hrs1 Lpriv_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS)). }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc sepc (mepc_val wval)).(sregs)
                   = add_vec_int pc 4).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hminv $Hpriv $Hmsx $Hmiex $Hmenvx] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg Hsepc [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE READ-ONLY S-CSR LEAF, STATED ONCE.                                *)
  (*                                                                       *)
  (* sepc / scause / stval are the same instruction with three different   *)
  (* CSR numbers, and the WP-level plumbing (funnel, nextPC bump, gpr      *)
  (* insert, [sie_cap] retarget, rejoin) is character-for-character the    *)
  (* same for all three.  So the leaf abstracts over the two things that   *)
  (* actually vary -- the CSR number with its exec-layer fact, and how the *)
  (* architectural read transforms the cell ([f]: the identity for         *)
  (* scause/stval, bit-0 clearing for sepc, whose read runs [align_pc]) -- *)
  (* and each CSR contributes a five-line instance below.  Cloning the     *)
  (* proof three times is what this replaces.                              *)
  (*                                                                       *)
  (* THE CELL IS THREADED, AND AT A PINNED VALUE.  A trap-CSR read is the  *)
  (* kind of read whose RESULT a caller has to reason about -- devintr's   *)
  (* whole body is a three-way branch on scause, and kerneltrap saves sepc *)
  (* to restore it later -- so unlike [wp_csrr_time_s_sconf], whose value  *)
  (* is Forall-quantified because mtime is unowned, this leaf takes the    *)
  (* cell and hands the SAME word back in [rd].  The fraction is           *)
  (* arbitrary: reading pins the value and does not need the cell          *)
  (* exclusively, so a caller holding the cell under [IntrDefs.trap_csrs]  *)
  (* can lend a share.                                                     *)
  (*                                                                       *)
  (* [rg] is a [register_bitvector_64] rather than a [register] so that    *)
  (* the cell's value type is definitionally [mword 64]; [Hnpc_ne] is what *)
  (* migrates its lookup across the nextPC bump, and is a [vm_compute] at  *)
  (* every instance.                                                       *)
  (*                                                                       *)
  (* THE INDEX IS THE LITERAL [false], not a parameter -- see [THE PINNED   *)
  (* INDEX] above; pinning it HERE pins all three instances below with it.  *)
  (* The cell is threaded in AND back out, so at [b = true] the             *)
  (* [R_bitvector_64 rg ↦ᵣ{dq} v] in the post would be the RESUMING hart's  *)
  (* cell, while the read that pinned [v] -- and the [rd] value derived     *)
  (* from it, which is the whole point of the leaf -- happened on the ENTRY *)
  (* hart.  That is FALSE, not merely unprovable.  The arbitrary fraction   *)
  (* does not rescue it: a share of the wrong hart's cell is still the      *)
  (* wrong hart's cell.  (The [b]-generic form was in any case unusable at  *)
  (* the enabled arm: [sie_cap true] holds trap-CSR cells of its OWN under  *)
  (* existentials and this leaf never opens it, so a caller there had to be *)
  (* lending a share it got from somewhere else.)                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_csrr_ro_s_sconf
      (pc : mword 64) (csrn : mword 12) (rg : register_bitvector_64)
      (f : mword 64 -> mword 64) (rd : mword 5)
      (m : regfile) (n : nat) (dq : dfrac) (v : mword 64) :
    uint rd <> 0 ->
    rd_ok rd ->
    register_beq (R_bitvector_64 rg) nextPC = false ->
    (* THE FOURTH HYPOTHESIS IS THE mstatus FACT SET, not just the one bit
       satp's reader wants.  [sconf] already carries [sconf_ms_facts] under
       its mstatus existential -- this leaf simply stops throwing it away,
       and hands the obligation the whole bundle rather than a projection of
       it, so a future S-mode read gated on MXR/TSR/SXL costs nothing here.
       The three Ext_S-gated instances below ignore it with a [_]. *)
    ( forall s : mstate,
        register_lookup cur_privilege s.(sregs) = Supervisor ->
        eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
        eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
        sconf_ms_facts (register_lookup mstatus s.(sregs)) ->
        exec (execute (CSRReg (csrn, zreg, Regidx rd, CSRRS))) s
          = Some (RETIRE_SUCCESS,
                  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg
                       (f (register_lookup (R_bitvector_64 rg) s.(sregs))))) ) ->
    sie_cap_gpr kt m n false p -∗
    R_bitvector_64 rg ↦ᵣ{dq} v -∗
    pc_is pc -∗
    instr pc false (CSRReg (csrn, zreg, Regidx rd, CSRRS)) -∗
    wp_next false p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg (f v)]> m) n false p -∗
      R_bitvector_64 rg ↦ᵣ{dq} v -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok Hne Hexec) "Hcg Hcell Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    iApply (wp_instr_s_sconf m n false pc false
              (CSRReg (csrn, zreg, Regidx rd, CSRRS))
              with "Hcg Hpc Hinstr").
    (* INTERRUPTS ARE OFF AT THIS LEAF, so the funnel's hart-generic obligation
       is discharged by [wp_next]'s OWN introduction rule at the ambient hart --
       the same [wp_next_off_intro] a b = false leaf already uses for its own
       conclusion.  Nothing is renamed and nothing is substituted: the body below
       is the pre-move proof VERBATIM. *)
    iApply wp_next_off_intro.
    iIntros (sigma Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hsie & Hsret & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & _ & %HmisaS & %HmisaC & _)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hcell") as %Lcell.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg sigma nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lcell_spc : register_lookup (R_bitvector_64 rg) s_pc.(sregs) = v).
    { unfold s_pc. rewrite irrelevant_register_set; [ exact Lcell | exact Hne ]. }
    iDestruct (gpr_file_insert_acc (tp_pin m) (Regidx rd) (regval_into_reg (f v))
                 with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (f v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (f v))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite -Lcell_spc.
      apply (Hexec s_pc Lpriv_spc);
        [ rewrite Lmisa_spc; exact HmisaS
        | rewrite Lmisa_spc; exact HmisaC
        | rewrite Lms_spc;   exact Hmsf ]. }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (f v))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (f v)]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    tp_refold Hrdtp "Hfile".
    iDestruct (sie_cap_retarget m
                 (<[Regidx rd := regval_into_reg (f v)]> m) n false Hsp with "Hcap") as "Hcap".
    iDestruct (sie_cap_gpr_join with
      "Hhs' [$Hhw $Hminv $Hpriv Hms Hsie Hsret $Hmiex $Hmenvx] Hcap Hfile") as "Hcg".
    { iExists ms0. iFrame "Hms Hsie Hsret". iPureIntro. exact Hmsf. }
    iApply ("Hcont" $! cpu_id with "[] Hcg Hcell [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* ---- the three instances.  scause and stval read their cell verbatim;
     sepc's read runs [align_pc], so its value carries [mepc_val].

     ALL THREE INHERIT THE PINNED INDEX from [wp_csrr_ro_s_sconf] -- they
     could not be [b]-generic even if one wanted them to be, since the
     generic leaf they are five lines of is not.  See [THE PINNED INDEX]
     above: each threads one of THIS hart's trap-CSR cells in and back out,
     so at [b = true] the post would be about the resuming hart's cell while
     the read happened on the entry hart's, which is FALSE rather than
     unprovable. ---- *)

  Lemma wp_csrr_scause_s_sconf
      (pc : mword 64) (rd : mword 5)
      (m : regfile) (n : nat) (dq : dfrac) (sc : mword 64) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n false p -∗
    scause ↦ᵣ{dq} sc -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_scause, zreg, Regidx rd, CSRRS)) -∗
    wp_next false p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg sc]> m) n false p -∗
      scause ↦ᵣ{dq} sc -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok).
    iApply (wp_csrr_ro_s_sconf pc csr_scause scause (fun x => x) rd m n dq sc
              Hrd Hrdok ltac:(vm_compute; reflexivity)).
    intros s Hpriv HS _ _.
    exact (exec_execute_csrr_scause_gpr_S rd s Hrd Hpriv HS).
  Qed.

  (* stval: NO CALL SITE TODAY (kerneltrap's usermode arm will be the first).
     It is kept because it is the third five-line instance of a leaf that
     exists precisely to be instantiated three times, and because deleting
     it would leave the [f]-generic proof looking over-general.  Its index is
     pinned like its siblings' -- a future first caller will be in the
     trap-handler tier, i.e. at interrupts-off, exactly as the others are. *)
  Lemma wp_csrr_stval_s_sconf
      (pc : mword 64) (rd : mword 5)
      (m : regfile) (n : nat) (dq : dfrac) (tv : mword 64) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n false p -∗
    stval ↦ᵣ{dq} tv -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_stval, zreg, Regidx rd, CSRRS)) -∗
    wp_next false p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg tv]> m) n false p -∗
      stval ↦ᵣ{dq} tv -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok).
    iApply (wp_csrr_ro_s_sconf pc csr_stval stval (fun x => x) rd m n dq tv
              Hrd Hrdok ltac:(vm_compute; reflexivity)).
    intros s Hpriv HS _ _.
    exact (exec_execute_csrr_stval_gpr_S rd s Hrd Hpriv HS).
  Qed.

  (* sepc: the value that lands in [rd] is [mepc_val ep], not [ep].  A
     caller that knows its saved epc is 2-aligned (every write to the cell
     went through [legalize_xepc], and every trap writes an aligned pc)
     collapses the wrapper itself; the leaf does not assume it. *)
  Lemma wp_csrr_sepc_s_sconf
      (pc : mword 64) (rd : mword 5)
      (m : regfile) (n : nat) (dq : dfrac) (ep : mword 64) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n false p -∗
    sepc ↦ᵣ{dq} ep -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_sepc, zreg, Regidx rd, CSRRS)) -∗
    wp_next false p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg (mepc_val ep)]> m) n false p -∗
      sepc ↦ᵣ{dq} ep -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok).
    iApply (wp_csrr_ro_s_sconf pc csr_sepc sepc mepc_val rd m n dq ep
              Hrd Hrdok ltac:(vm_compute; reflexivity)).
    intros s Hpriv HS HC _.
    exact (exec_execute_csrr_sepc_gpr_S rd s Hrd Hpriv HS HC).
  Qed.

  (* ---- csrr rd,satp -- THE ONE RO READ THAT CANNOT BE AN INSTANCE OF
     [wp_csrr_ro_s_sconf], and the reason is ownership rather than decode.

     The three instances above thread a cell the ambient bundle does NOT
     hold: sepc / scause / stval belong to whoever is running with
     interrupts off.  satp is different -- [IntrDefs.strans_inv] owns it in
     BOTH arms ([SRegime.bare_inv] at Bare, [KptShare.tlb_res_pt] at KPT),
     and [strans_inv] is inside [sie_cap], inside [sie_cap_gpr].  So
     [sie_cap_gpr m n false p ∗ satp ↦ᵣ{dq} v] is not a premise set a caller
     can be short of; it is one NO caller can hold, and a leaf demanding it
     is vacuous however carefully it is proved.  (It was: this lemma had
     that shape until prepare_return tried to call it.)

     WHAT THE CALLER SUPPLIES INSTEAD IS THE KPT RECEIPT.  [kpt_on cpu_id]
     pins the arm at KPT and opens it
     ([IntrDefs.strans_inv_acc_kpt]); the cell comes out of the
     [tlb_res_pt] inside ([KptShare.tlb_res_pt_satp_acc]) and goes straight
     back, so the borrow never escapes this leaf and the bundle handed back
     is whole.  That also explains why the value is not a parameter: it is
     whatever the live kernel table's satp says, so it comes back
     EXISTENTIALLY, carrying the three [satp_rooted] facts the arm knows
     about it -- which is exactly what a reader of [kernel_satp] wants and
     strictly more than a bare points-to would give.

     The mstatus obligation the other three discard is used here: satp's
     accessibility is mstatus.TVM = 0 rather than Ext_S, and that bit is the
     last conjunct of [sconf_ms_facts], which [sconf] was already
     carrying. ---- *)
  Lemma wp_csrr_satp_kpt_s_sconf
      (pc : mword 64) (rd : mword 5) (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n false p -∗
    kpt_on cpu_id -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_satp, zreg, Regidx rd, CSRRS)) -∗
    wp_next false p (fun (CID : CpuId) =>
      ∀ (sp0 : mword 64) (root : mword 44),
      ⌜ _get_Satp64_Mode (Mk_Satp64 sp0) = ('b"1000" : mword 4) ⌝ -∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) sp0 : mword 64))
          = (mword_of_int 0 : mword 16) ⌝ -∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) sp0 : mword 64))
          = root ⌝ -∗
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg sp0]> m) n false p -∗
      kpt_on cpu_id -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok) "Hcg #Hkptr Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    iApply (wp_instr_s_sconf m n false pc false
              (CSRReg (csr_satp, zreg, Regidx rd, CSRRS))
              with "Hcg Hpc Hinstr").
    iApply wp_next_off_intro.
    iIntros (sigma Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    (* THE BORROW, taken inside: the receipt pins the arm, the arm's
       [tlb_res_pt] lends the cell, and both closures are held until the
       bundle is rebuilt below. *)
    iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
    iDestruct (strans_inv_acc_kpt with "Hkptr Htr") as (root) "(Htlb & Htrback)".
    iDestruct (tlb_res_pt_satp_acc with "Htlb")
      as (v) "(Hcell & %Hmode & %Hasid & %Hppn & Htlbback)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hsie & Hsret & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & _ & %HmisaS & %HmisaC & _)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hcell") as %Lcell.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg sigma nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lcell_spc : register_lookup satp s_pc.(sregs) = v).
    { unfold s_pc. rewrite irrelevant_register_set;
        [ exact Lcell | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_insert_acc (tp_pin m) (Regidx rd) (regval_into_reg v)
                 with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg v)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite -Lcell_spc.
      apply (exec_execute_csrr_satp_gpr_S rd s_pc Hrd Lpriv_spc).
      rewrite Lms_spc.
      destruct Hmsf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HTVM). exact HTVM. }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    (* GIVE THE CELL BACK, innermost closure first, and the bundle is whole
       again -- the borrow never leaves this proof. *)
    iDestruct ("Htlbback" with "Hcell") as "Htlb".
    iDestruct ("Htrback" with "Htlb") as "Htr".
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg v]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    tp_refold Hrdtp "Hfile".
    iDestruct (sie_cap_retarget m (<[Regidx rd := regval_into_reg v]> m) n false Hsp
                 with "[Hstk Htr Harm]") as "Hcap"; [rewrite /sie_cap; iFrame "Hstk Htr Harm Hwit"|].
    iDestruct (sie_cap_gpr_join with
      "Hhs' [$Hhw $Hminv $Hpriv Hms Hsie Hsret $Hmiex $Hmenvx] Hcap Hfile") as "Hcg".
    { iExists ms0. iFrame "Hms Hsie Hsret". iPureIntro. exact Hmsf. }
    iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
    iApply ("Hcont" $! v root with "[%] [%] [%] Hcg Hkptr [$Hpc' $Hnpc]").
    - exact Hmode.
    - exact Hasid.
    - exact Hppn.
  Qed.

End WpSconfCsr.
