(* ===================================================================== *)
(* THE PER-NODE PORT: THIS FILE IS DONE (2026-08-18).                     *)
(*                                                                        *)
(* All SIXTEEN leaves are converted to [WpSmodeIntr.sconf_step_obl] and    *)
(* run on [HartSCsr]'s privilege-generic CSR engines.  EVERY STATEMENT IS  *)
(* BYTE-IDENTICAL except [wp_csrr_ro_s_sconf]'s, whose whole-[execute]     *)
(* [exec] premise had to become an [swp] obligation -- an [exec] fact      *)
(* constrains the START state only, and a per-node walk may be interfered  *)
(* with between nodes, so nothing bridges the two.  That is the same       *)
(* forced change [WpSmodeIntr.wp_gpr_write_s_sconf] made; its three        *)
(* instances are untouched.                                               *)
(*                                                                        *)
(* THREE THINGS IN THE WRAPPER'S OBLIGATION ARE LOAD-BEARING HERE, and     *)
(* each was added for a leaf in this file:                                 *)
(*   - the SECOND arm index [b']: the four sstatus flips MOVE the SIE arm, *)
(*     and before it the flip could not be stated at all ([sconf]'s ghost  *)
(*     half at the new bit and [sie_arm true]'s quarter at the old one are *)
(*     contradictory, so the obligation's post was FALSE, not merely       *)
(*     unreachable);                                                       *)
(*   - the mstatus witness [ms']: [wp_csrr_sstatus_s_sconf] NAMES the word *)
(*     it read, so its [sconf_at ms] and the [sstatus_read ms] that landed *)
(*     in rd are about the same word by construction;                      *)
(*   - the rider's HART [R CID …]: the two csrci disable flips hand their  *)
(*     continuation the enabled arm's payload -- trap CSRs, count token,   *)
(*     running claim, per-cpu cells -- and every one of those is           *)
(*     hart-indexed, so a rider fixed at the entry hart cannot carry them. *)
(* ===================================================================== *)
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
(* the privilege-generic CSR swp engines and the frame kit at Supervisor *)
Require Import HartSCsr HartSwp HartMFrame HartLift HartSpan HartSpanChar
        HartMCycle HartRegNode HartGoodb
        WpDecodeBridge WpMmodeJump WpMmodeCsrSwp.
Require Import IntrDefs WpIntrInv WpSmodeIntr.
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

(* the CSRRead reading of the sstatus check: [exec_check_CSR_result_sstatus_S]
   (WpPushOffCsr) is the read-MODIFY-write one the flip leaves use.  sstatus
   is Ext_S-gated like scause/stval/sepc, so this is the shared route with
   four [vm_compute]s. *)
Lemma exec_check_CSR_result_csrr_sstatus_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_sstatus Supervisor CSRRead) s
    = Some (CSR_Check_OK tt, s).
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

(* ===================================================================== *)
(* THE TERM REDUCTIONS of the three trap-CSR reads.  [exec_read_CSR_*]     *)
(* above are the exec-side facts; these are the same cascade walk done at  *)
(* the TERM, which is what the per-node layer needs (an [exec] fact        *)
(* constrains the start state only).  Printed rather than guessed -- see   *)
(* the worklist's "PRINTING A MODEL TERM IS HOW YOU GET A _red LEMMA".     *)
(* ===================================================================== *)
Lemma read_CSR_scause_red :
  read_CSR csr_scause = (Defs.read_reg scause : M (mword 64)).
Proof. unfold csr_scause. drive_csr_term. reflexivity. Qed.

Lemma read_CSR_stval_red :
  read_CSR csr_stval = (Defs.read_reg stval : M (mword 64)).
Proof. unfold csr_stval. drive_csr_term. reflexivity. Qed.

Lemma read_CSR_satp_red :
  read_CSR csr_satp = (Defs.read_reg satp : M (mword 64)).
Proof. unfold csr_satp. drive_csr_term. reflexivity. Qed.

Lemma read_CSR_sepc_red :
  read_CSR csr_sepc
  = (Defs.bind (Defs.read_reg sepc) (fun v : mword 64 => align_pc v)
     : M (mword 64)).
Proof. unfold csr_sepc. drive_csr_term. unfold get_xepc. cbn match. reflexivity. Qed.

(* [align_pc] at a SYMBOLIC word: the only read is misa (through
   [currentlyEnabled Ext_Zca]), which the reference state pins, so the whole
   stretch rides the goodb certificate and the value is never inspected --
   which is why the certificate computes at all (goodb is not computable when
   CONTROL FLOW depends on symbolic data; here it does not). *)
Lemma hval_align_pc (D Drw : gset register) (rs : regstate) (w : mword 64) :
  (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
  (misa : register) ∈ D ->
  register_lookup cur_privilege rs = Supervisor ->
  register_lookup mseccfg rs = mword_of_int 0 ->
  register_lookup misa rs = MISA_C ->
  hval D Drw rs (align_pc w) (mepc_val w) rs.
Proof.
  intros HD1 HD2 HD3 Hp Hs Hm.
  apply (hval_of_goodb D_m D Drw _ dstateS rs (mepc_val w)
           (dm_sub D HD1 HD2 HD3) (agree_dm_S rs Hp Hs Hm)).
  - vm_compute. reflexivity.
  - unfold align_pc.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_currentlyEnabled_Zca dstateS
                  ltac:(vm_compute; reflexivity))).
    cbn zeta match. apply exec_returnM.
Qed.
(* ===================================================================== *)
(* THE TWO S-CSR WRITES, at the TERM.  Both dispatch clauses were PRINTED   *)
(* out of a pruned goal rather than hand-written -- see the worklist's      *)
(* note on getting the ASSOCIATION wrong.                                  *)
(* ===================================================================== *)
Lemma write_CSR_stvec_red (v : mword 64) :
  write_CSR csr_stvec v
  = (Defs.bind (set_stvec v) (fun w : mword 64 => returnM (Ok w))
     : M (result (mword 64) unit)).
Proof. unfold write_CSR, csr_stvec. drive_csr_term. reflexivity. Qed.

Lemma read_CSR_sstatus_red :
  read_CSR csr_sstatus
  = (Defs.bind (Defs.read_reg mstatus)
       (fun o : mword 64 => returnM (sstatus_read o)) : M (mword 64)).
Proof. unfold csr_sstatus. drive_csr_term. reflexivity. Qed.

(* the sstatus write: read mstatus, LEGALIZE (monadic, misa-gated), write it
   back, read it back.  This is the clause the M-mode mstatus write has
   ([WpGprCsrwC.write_CSR_mstatus_red]); the only difference is that the
   value handed to the legalizer is the S-view lift. *)
Lemma write_CSR_sstatus_red (v : mword 64) :
  write_CSR csr_sstatus v
  = (Defs.bind (Defs.read_reg mstatus)
       (fun o : mword 64 =>
          Defs.bind (legalize_sstatus o v)
            (fun c : mword 64 =>
               Defs.bind (Defs.bind0 (Defs.write_reg mstatus c)
                            (Defs.read_reg mstatus))
                 (fun c2 : mword 64 =>
                    returnM (Ok (subrange_vec_dec (lower_mstatus c2)
                                   (Z.sub xlen 1) 0)))))
     : M (result (mword 64) unit)).
Proof. unfold csr_sstatus. drive_csr_term. reflexivity. Qed.

Lemma write_CSR_sepc_red (v : mword 64) :
  write_CSR csr_sepc v
  = (Defs.bind (set_xepc Supervisor v) (fun w : mword 64 => returnM (Ok w))
     : M (result (mword 64) unit)).
Proof. unfold write_CSR, csr_sepc. drive_csr_term. reflexivity. Qed.

(* [HartSwp.mbind_ret] is keyed on [Interface.Ret]; the MODEL spells its
   returns [returnM], which is a [Definition] and so never matches
   syntactically.  Same equation, the model's own spelling. *)
Lemma mbind_returnM {A B : Type} (v : A) (f : A -> M B) :
  Defs.bind (returnM v) f = f v.
Proof. reflexivity. Qed.

Section SWrites.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [legalize_tvec] READS NOTHING -- it is a match on the written value's
     mode field over [returnM]s -- so its certificate needs no read set at
     all.  goodb is not COMPUTABLE here (the control flow is driven by the
     symbolic [v]), which is exactly the case the worklist says a plain
     [destruct] of the scrutinee closes: each arm is then concrete. *)
  Local Lemma hval_legalize_tvec_stvec (D Drw : gset register) (rs : regstate)
      (o v : mword 64) :
    trapVectorMode_forwards (_get_Mtvec_Mode v) <> TV_Reserved ->
    hval D Drw rs
      (legalize_tvec o v plat_stvec_direct_mode_supported 2
         plat_stvec_vectored_mode_supported
         plat_stvec_vectored_base_alignment_exp) v rs.
  Proof.
    intro Hm.
    apply (hval_of_goodb (fun _ => false) D Drw _ dstateS rs v
             ltac:(intros r Hr; discriminate)
             ltac:(intros r Hr; discriminate)).
    - unfold legalize_tvec.
      (* the scrutinee is spelled at [Mk_Mtvec v], so the case split has to be
         too -- and the third arm is the one [Hm] rules out. *)
      destruct (trapVectorMode_forwards (_get_Mtvec_Mode (Mk_Mtvec v)))
        eqn:Hmode;
        [ repeat first [ rewrite Hmode | rewrite mbind_returnM ]; reflexivity
        | repeat first [ rewrite Hmode | rewrite mbind_returnM ]; reflexivity
        | exfalso; apply Hm; exact Hmode ].
    - exact (exec_legalize_tvec_stvec o v dstateS Hm).
  Qed.

  (* [legalize_xepc] reads nothing either ([hartSupports] is a platform
     constant), and here the control flow does not touch the value, so the
     certificate simply computes. *)
  Local Lemma hval_legalize_xepc (D Drw : gset register) (rs : regstate)
      (v : mword 64) :
    hval D Drw rs (legalize_xepc v) (mepc_val v) rs.
  Proof.
    apply (hval_of_goodb (fun _ => false) D Drw _ dstateS rs (mepc_val v)
             ltac:(intros r Hr; discriminate)
             ltac:(intros r Hr; discriminate)).
    - vm_compute. reflexivity.
    - exact (exec_legalize_xepc v dstateS).
  Qed.

  (* the stvec write: read the old value, legalize (pure), write, read back *)
  Lemma swp_write_CSR_stvec_S (dq : dfrac) (tv0 v : mword 64) :
    trapVectorMode_forwards (_get_Mtvec_Mode v) <> TV_Reserved ->
    gen_cert -∗
    hreg_frame (pw_rs Supervisor (R_bitvector_64 stvec) tv0)
      (cw_Drw (R_bitvector_64 stvec)) -∗
    hreg_frame_ro (cw_Df dq) (pw_rs Supervisor (R_bitvector_64 stvec) tv0)
      cw_Dro -∗
    swp (write_CSR csr_stvec v)
      (fun x => ⌜x = Ok v⌝ ∗
         hreg_frame (pw_rs Supervisor (R_bitvector_64 stvec) v)
           (cw_Drw (R_bitvector_64 stvec)) ∗
         hreg_frame_ro (cw_Df dq) (pw_rs Supervisor (R_bitvector_64 stvec) v)
           cw_Dro).
  Proof.
    intros Hmode.
    assert (Hfresh : cw_fresh (R_bitvector_64 stvec))
      by (split_and!; vm_compute; reflexivity).
    iIntros "#Hcert Hrw Hro".
    rewrite write_CSR_stvec_red.
    iApply (swp_bind_use _ _
              (fun w : mword 64 => ⌜w = v⌝ ∗
                 hreg_frame (pw_rs Supervisor (R_bitvector_64 stvec) v)
                   (cw_Drw (R_bitvector_64 stvec)) ∗
                 hreg_frame_ro (cw_Df dq)
                   (pw_rs Supervisor (R_bitvector_64 stvec) v) cw_Dro)%I
              _ with "[Hrw Hro] [-]").
    { unfold set_stvec.
      (* 1. the old value *)
      iApply (swp_bind_use _ _
                (fun o : mword 64 => ⌜o = tv0⌝ ∗
                   hreg_frame (pw_rs Supervisor (R_bitvector_64 stvec) tv0)
                     (cw_Drw (R_bitvector_64 stvec)) ∗
                   hreg_frame_ro (cw_Df dq)
                     (pw_rs Supervisor (R_bitvector_64 stvec) tv0) cw_Dro)%I
                _ with "[Hrw Hro] [-]").
      { iApply (swp_mono with "[] [-]");
          [| iApply (swp_read_reg_pinned (cw_Drw (R_bitvector_64 stvec)) cw_Dro
                       (cw_Df dq) (pw_rs Supervisor (R_bitvector_64 stvec) tv0)
                       (R_bitvector_64 stvec) (cw_disj _ Hfresh) (cw_in_r _)
                       with "Hcert Hrw Hro") ].
        iIntros (o) "(-> & Hrw & Hro)".
        rewrite (pw_rs_r Supervisor (R_bitvector_64 stvec) tv0). by iFrame. }
      iIntros (o) "(-> & Hrw & Hro)".
      (* 2. the legalization: pure, so it rides the certificate *)
      iApply (swp_bind_use _ _
                (fun w : mword 64 => ⌜w = v⌝ ∗
                   hreg_frame (pw_rs Supervisor (R_bitvector_64 stvec) tv0)
                     (cw_Drw (R_bitvector_64 stvec)) ∗
                   hreg_frame_ro (cw_Df dq)
                     (pw_rs Supervisor (R_bitvector_64 stvec) tv0) cw_Dro)%I
                _ with "[Hrw Hro] [-]").
      { iApply (swp_span (cw_Drw (R_bitvector_64 stvec)) cw_Dro (cw_Df dq)
                  (pw_rs Supervisor (R_bitvector_64 stvec) tv0)
                  (pw_rs Supervisor (R_bitvector_64 stvec) tv0) _ v
                  (cw_disj _ Hfresh)
                  (hval_legalize_tvec_stvec _ _ _ tv0 v Hmode)
                  with "Hcert Hrw Hro"). }
      iIntros (w) "(-> & Hrw & Hro)".
      (* 3. the write, then the read-back *)
      iApply (swp_bind0_use _ _
                (fun _ =>
                   hreg_frame (pw_rs Supervisor (R_bitvector_64 stvec) v)
                     (cw_Drw (R_bitvector_64 stvec)) ∗
                   hreg_frame_ro (cw_Df dq)
                     (pw_rs Supervisor (R_bitvector_64 stvec) v) cw_Dro)%I
                _ with "[Hrw Hro] [-]").
      { iApply (swp_mono with "[] [-]");
          [| iApply (swp_write_reg_owned (cw_Drw (R_bitvector_64 stvec)) cw_Dro
                       (cw_Df dq) (pw_rs Supervisor (R_bitvector_64 stvec) tv0)
                       (R_bitvector_64 stvec) v (cw_disj _ Hfresh) (cw_w_r _)
                       with "Hcert Hrw Hro") ].
        iIntros (u) "[Hrw Hro]".
        iSplitL "Hrw".
        { iApply (cw_rw_ext (R_bitvector_64 stvec) _ _
                    (reg_agree_l _ _ _ _ (pw_set_agree Supervisor
                       (R_bitvector_64 stvec) tv0 v Hfresh)) with "Hrw"). }
        iApply (cw_ro_ext dq _ _
                  (reg_agree_r _ _ _ _ (pw_set_agree Supervisor
                     (R_bitvector_64 stvec) tv0 v Hfresh)) with "Hro"). }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_mono with "[] [-]");
        [| iApply (swp_read_reg_pinned (cw_Drw (R_bitvector_64 stvec)) cw_Dro
                     (cw_Df dq) (pw_rs Supervisor (R_bitvector_64 stvec) v)
                     (R_bitvector_64 stvec) (cw_disj _ Hfresh) (cw_in_r _)
                     with "Hcert Hrw Hro") ].
      iIntros (c) "(-> & Hrw & Hro)".
      rewrite (pw_rs_r Supervisor (R_bitvector_64 stvec) v). by iFrame. }
    iIntros (w) "(-> & Hrw & Hro)". iApply swp_ret. by iFrame.
  Qed.

  (* the sepc write: legalize (pure, bit 0 cleared), write, return *)
  Lemma swp_write_CSR_sepc_S (dq : dfrac) (ep0 v : mword 64) :
    gen_cert -∗
    hreg_frame (pw_rs Supervisor (R_bitvector_64 sepc) ep0)
      (cw_Drw (R_bitvector_64 sepc)) -∗
    hreg_frame_ro (cw_Df dq) (pw_rs Supervisor (R_bitvector_64 sepc) ep0)
      cw_Dro -∗
    swp (write_CSR csr_sepc v)
      (fun x => ⌜x = Ok (mepc_val v)⌝ ∗
         hreg_frame (pw_rs Supervisor (R_bitvector_64 sepc) (mepc_val v))
           (cw_Drw (R_bitvector_64 sepc)) ∗
         hreg_frame_ro (cw_Df dq)
           (pw_rs Supervisor (R_bitvector_64 sepc) (mepc_val v)) cw_Dro).
  Proof.
    assert (Hfresh : cw_fresh (R_bitvector_64 sepc))
      by (split_and!; vm_compute; reflexivity).
    iIntros "#Hcert Hrw Hro".
    rewrite write_CSR_sepc_red.
    iApply (swp_bind_use _ _
              (fun w : mword 64 => ⌜w = mepc_val v⌝ ∗
                 hreg_frame (pw_rs Supervisor (R_bitvector_64 sepc) (mepc_val v))
                   (cw_Drw (R_bitvector_64 sepc)) ∗
                 hreg_frame_ro (cw_Df dq)
                   (pw_rs Supervisor (R_bitvector_64 sepc) (mepc_val v))
                   cw_Dro)%I
              _ with "[Hrw Hro] [-]").
    { unfold set_xepc. cbn match.
      iApply (swp_bind_use _ _
                (fun t : mword 64 => ⌜t = mepc_val v⌝ ∗
                   hreg_frame (pw_rs Supervisor (R_bitvector_64 sepc) ep0)
                     (cw_Drw (R_bitvector_64 sepc)) ∗
                   hreg_frame_ro (cw_Df dq)
                     (pw_rs Supervisor (R_bitvector_64 sepc) ep0) cw_Dro)%I
                _ with "[Hrw Hro] [-]").
      { iApply (swp_span (cw_Drw (R_bitvector_64 sepc)) cw_Dro (cw_Df dq)
                  (pw_rs Supervisor (R_bitvector_64 sepc) ep0)
                  (pw_rs Supervisor (R_bitvector_64 sepc) ep0) _ (mepc_val v)
                  (cw_disj _ Hfresh) (hval_legalize_xepc _ _ _ v)
                  with "Hcert Hrw Hro"). }
      iIntros (t) "(-> & Hrw & Hro)".
      iApply (swp_bind0_use _ _
                (fun _ =>
                   hreg_frame (pw_rs Supervisor (R_bitvector_64 sepc)
                                 (mepc_val v)) (cw_Drw (R_bitvector_64 sepc)) ∗
                   hreg_frame_ro (cw_Df dq)
                     (pw_rs Supervisor (R_bitvector_64 sepc) (mepc_val v))
                     cw_Dro)%I
                _ with "[Hrw Hro] [-]").
      { iApply (swp_mono with "[] [-]");
          [| iApply (swp_write_reg_owned (cw_Drw (R_bitvector_64 sepc)) cw_Dro
                       (cw_Df dq) (pw_rs Supervisor (R_bitvector_64 sepc) ep0)
                       (R_bitvector_64 sepc) (mepc_val v) (cw_disj _ Hfresh)
                       (cw_w_r _) with "Hcert Hrw Hro") ].
        iIntros (u) "[Hrw Hro]".
        iSplitL "Hrw".
        { iApply (cw_rw_ext (R_bitvector_64 sepc) _ _
                    (reg_agree_l _ _ _ _ (pw_set_agree Supervisor
                       (R_bitvector_64 sepc) ep0 (mepc_val v) Hfresh))
                    with "Hrw"). }
        iApply (cw_ro_ext dq _ _
                  (reg_agree_r _ _ _ _ (pw_set_agree Supervisor
                     (R_bitvector_64 sepc) ep0 (mepc_val v) Hfresh))
                  with "Hro"). }
      iIntros (u) "[Hrw Hro]". iApply swp_ret. by iFrame. }
    iIntros (w) "(-> & Hrw & Hro)". iApply swp_ret. by iFrame.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* THE sstatus WRITE.  [legalize_sstatus o v] is [legalize_mstatus] at   *)
  (* the S-view lift, so it is READ-ONLY (misa only) and rides the goodb   *)
  (* certificate -- but NOT computably: it branches on the written value's *)
  (* MPP field through [have_nominal_privLevel].  Same shape                *)
  (* [WpGprCsrwC.goodb_legalize_mstatus] needed at Machine, re-run here at  *)
  (* the SUPERVISOR reference state (D_m contains cur_privilege, so the     *)
  (* M-mode certificate does not transport by [goodb_congr]).              *)
  (* ------------------------------------------------------------------ *)
  Local Lemma goodb_have_nominal_privLevel_S (pp : mword 2) :
    goodb D_m (have_nominal_privLevel pp) dstateS = true.
  Proof.
    unfold have_nominal_privLevel. cbn zeta.
    destruct (eq_vec pp ('b"00")); [cbn match; vm_compute; reflexivity|].
    cbn match.
    destruct (eq_vec pp ('b"01")); [cbn match; vm_compute; reflexivity|].
    cbn match. reflexivity.
  Qed.

  Local Lemma goodb_legalize_mstatus_S (o v : mword 64) :
    goodb D_m (legalize_mstatus o v) dstateS = true.
  Proof.
    unfold legalize_mstatus.
    repeat goodb_step.
    erewrite goodb_bind.
    3: apply (exec_have_nominal_privLevel (_get_Mstatus_MPP (Mk_Mstatus v))
                dstateS ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)).
    2: apply goodb_have_nominal_privLevel_S.
    destruct (have_nom_val (_get_Mstatus_MPP (Mk_Mstatus v)));
      cbn match; repeat goodb_step; reflexivity.
  Qed.

  Local Lemma hval_legalize_sstatus_S (D Drw : gset register) (rs : regstate)
      (o v : mword 64) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mseccfg rs = mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    hval D Drw rs (legalize_sstatus o v) (legalize_sstatus_val o v) rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm.
    apply (hval_of_goodb D_m D Drw _ dstateS rs (legalize_sstatus_val o v)
             (dm_sub D HD1 HD2 HD3) (agree_dm_S rs Hp Hs Hm)).
    - unfold legalize_sstatus. apply goodb_legalize_mstatus_S.
    - apply (exec_legalize_sstatus o v dstateS
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
  Qed.

  Lemma swp_write_CSR_sstatus_S (dq : dfrac) (ms0 v : mword 64) :
    gen_cert -∗
    hreg_frame (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
      (cw_Drw (R_bitvector_64 mstatus)) -∗
    hreg_frame_ro (cw_Df dq) (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
      cw_Dro -∗
    swp (write_CSR csr_sstatus v)
      (fun x => ⌜x = Ok (subrange_vec_dec
                           (lower_mstatus (legalize_sstatus_val ms0 v))
                           (Z.sub xlen 1) 0)⌝ ∗
         hreg_frame (pw_rs Supervisor (R_bitvector_64 mstatus)
                       (legalize_sstatus_val ms0 v))
           (cw_Drw (R_bitvector_64 mstatus)) ∗
         hreg_frame_ro (cw_Df dq)
           (pw_rs Supervisor (R_bitvector_64 mstatus)
              (legalize_sstatus_val ms0 v)) cw_Dro).
  Proof.
    assert (Hfresh : cw_fresh (R_bitvector_64 mstatus))
      by (split_and!; vm_compute; reflexivity).
    iIntros "#Hcert Hrw Hro".
    rewrite write_CSR_sstatus_red.
    (* 1. the old mstatus *)
    iApply (swp_bind_use _ _
              (fun o : mword 64 => ⌜o = ms0⌝ ∗
                 hreg_frame (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                   (cw_Drw (R_bitvector_64 mstatus)) ∗
                 hreg_frame_ro (cw_Df dq)
                   (pw_rs Supervisor (R_bitvector_64 mstatus) ms0) cw_Dro)%I
              _ with "[Hrw Hro] [-]").
    { iApply (swp_mono with "[] [-]");
        [| iApply (swp_read_reg_pinned (cw_Drw (R_bitvector_64 mstatus)) cw_Dro
                     (cw_Df dq) (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                     (R_bitvector_64 mstatus) (cw_disj _ Hfresh) (cw_in_r _)
                     with "Hcert Hrw Hro") ].
      iIntros (o) "(-> & Hrw & Hro)".
      rewrite (pw_rs_r Supervisor (R_bitvector_64 mstatus) ms0). by iFrame. }
    iIntros (o) "(-> & Hrw & Hro)".
    (* 2. the legalization, goodb-transported *)
    iApply (swp_bind_use _ _
              (fun c : mword 64 => ⌜c = legalize_sstatus_val ms0 v⌝ ∗
                 hreg_frame (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                   (cw_Drw (R_bitvector_64 mstatus)) ∗
                 hreg_frame_ro (cw_Df dq)
                   (pw_rs Supervisor (R_bitvector_64 mstatus) ms0) cw_Dro)%I
              _ with "[Hrw Hro] [-]").
    { iApply (swp_span (cw_Drw (R_bitvector_64 mstatus)) cw_Dro (cw_Df dq)
                (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                (pw_rs Supervisor (R_bitvector_64 mstatus) ms0) _
                (legalize_sstatus_val ms0 v) (cw_disj _ Hfresh)
                (hval_legalize_sstatus_S _ _ _ ms0 v (cw_in_priv _)
                   (cw_in_sec _) (cw_in_misa _)
                   (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                   (pw_rs_sec Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                   (pw_rs_misa Supervisor (R_bitvector_64 mstatus) ms0 Hfresh))
                with "Hcert Hrw Hro"). }
    iIntros (c) "(-> & Hrw & Hro)".
    (* 3. the write, then the read-back *)
    iApply (swp_bind_use _ _
              (fun c2 : mword 64 => ⌜c2 = legalize_sstatus_val ms0 v⌝ ∗
                 hreg_frame (pw_rs Supervisor (R_bitvector_64 mstatus)
                               (legalize_sstatus_val ms0 v))
                   (cw_Drw (R_bitvector_64 mstatus)) ∗
                 hreg_frame_ro (cw_Df dq)
                   (pw_rs Supervisor (R_bitvector_64 mstatus)
                      (legalize_sstatus_val ms0 v)) cw_Dro)%I
              _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ =>
                   hreg_frame (pw_rs Supervisor (R_bitvector_64 mstatus)
                                 (legalize_sstatus_val ms0 v))
                     (cw_Drw (R_bitvector_64 mstatus)) ∗
                   hreg_frame_ro (cw_Df dq)
                     (pw_rs Supervisor (R_bitvector_64 mstatus)
                        (legalize_sstatus_val ms0 v)) cw_Dro)%I
                _ with "[Hrw Hro] [-]").
      { iApply (swp_mono with "[] [-]");
          [| iApply (swp_write_reg_owned (cw_Drw (R_bitvector_64 mstatus))
                       cw_Dro (cw_Df dq)
                       (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                       (R_bitvector_64 mstatus) (legalize_sstatus_val ms0 v)
                       (cw_disj _ Hfresh) (cw_w_r _) with "Hcert Hrw Hro") ].
        iIntros (u) "[Hrw Hro]".
        iSplitL "Hrw".
        { iApply (cw_rw_ext (R_bitvector_64 mstatus) _ _
                    (reg_agree_l _ _ _ _ (pw_set_agree Supervisor
                       (R_bitvector_64 mstatus) ms0
                       (legalize_sstatus_val ms0 v) Hfresh)) with "Hrw"). }
        iApply (cw_ro_ext dq _ _
                  (reg_agree_r _ _ _ _ (pw_set_agree Supervisor
                     (R_bitvector_64 mstatus) ms0
                     (legalize_sstatus_val ms0 v) Hfresh)) with "Hro"). }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_mono with "[] [-]");
        [| iApply (swp_read_reg_pinned (cw_Drw (R_bitvector_64 mstatus)) cw_Dro
                     (cw_Df dq)
                     (pw_rs Supervisor (R_bitvector_64 mstatus)
                        (legalize_sstatus_val ms0 v))
                     (R_bitvector_64 mstatus) (cw_disj _ Hfresh) (cw_in_r _)
                     with "Hcert Hrw Hro") ].
      iIntros (c2) "(-> & Hrw & Hro)".
      rewrite (pw_rs_r Supervisor (R_bitvector_64 mstatus)
                 (legalize_sstatus_val ms0 v)). by iFrame. }
    iIntros (c2) "(-> & Hrw & Hro)". iApply swp_ret. by iFrame.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* satp's LEGALITY CHECK -- THE ONE THAT IS NOT [D_m].                   *)
  (*                                                                     *)
  (* [is_CSR_accessible 0x180 Supervisor acc] is [satp_accessible], i.e.  *)
  (* [read_reg mstatus >>= fun w => returnM (TVM w == 0)], so the check    *)
  (* reads mstatus and BRANCHES on the value.  Two consequences:           *)
  (*   - the read set is [D_ms], not [D_m], so mstatus must be in the      *)
  (*     leaf's read frame;                                               *)
  (*   - the certificate is not computable at a symbolic mstatus, so it is *)
  (*     ASSEMBLED at the accessibility step off the leaf's own TVM fact.  *)
  (* THE REFERENCE STATE IS THE CALLER'S OWN FILE, which makes             *)
  (* [hval_of_goodb]'s agreement premise [eq_refl] -- the trick that stops *)
  (* a value-dependent check from needing a concrete reference state at    *)
  (* all. *)
  (* ------------------------------------------------------------------ *)
  Definition D_ms (r : register) : bool :=
    D_m r || register_beq r (R_bitvector_64 mstatus).

  Lemma dms_sub (D : gset register) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D -> (mstatus : register) ∈ D ->
    forall r : register, D_ms r = true -> r ∈ D.
  Proof.
    intros H1 H2 H3 H4 r Hr. unfold D_ms in Hr.
    apply orb_prop in Hr as [Hr|Hr]; [ exact (dm_sub D H1 H2 H3 r Hr) |].
    apply register_beq_eq in Hr. subst r. exact H4.
  Qed.

  (* the three data-free conjuncts compute; the accessibility one is the
     mstatus read and is ASSEMBLED off the leaf's own TVM fact. *)
  Local Lemma goodb_check_CSR_satp_S (st : mstate) :
    eq_vec (_get_Mstatus_TVM (register_lookup mstatus st.(sregs))) ('b"1")
      = false ->
    goodb D_ms (check_CSR csr_satp Supervisor CSRRead) st = true.
  Proof.
    intro HTVM. unfold check_CSR, Defs.and_boolM.
    erewrite goodb_bind; [ | vm_compute; reflexivity | vm_compute; reflexivity ].
    cbn match.
    erewrite goodb_bind; [ | vm_compute; reflexivity | vm_compute; reflexivity ].
    cbn match.
    erewrite goodb_bind;
      [ | vm_compute; reflexivity
        | exact (exec_is_CSR_accessible_satp_S CSRRead st HTVM) ].
    cbn match.
    vm_compute; reflexivity.
  Qed.

  Local Lemma goodb_check_CSR_result_satp_S (st : mstate) :
    eq_vec (_get_Mstatus_TVM (register_lookup mstatus st.(sregs))) ('b"1")
      = false ->
    goodb D_ms (check_CSR_result csr_satp Supervisor CSRRead) st = true.
  Proof.
    intro HTVM. unfold check_CSR_result.
    erewrite goodb_bind;
      [ | exact (goodb_check_CSR_satp_S st HTVM)
        | apply exec_check_CSR_read_p;
          [ assert (H : check_CSR_priv csr_satp Supervisor = returnM true)
              by (vm_compute; reflexivity);
            rewrite H; apply exec_returnm
          | vm_compute; reflexivity
          | exact (exec_is_CSR_accessible_satp_S CSRRead st HTVM)
          | assert (H : stateen_allows_CSR_access csr_satp Supervisor CSRRead
                        = returnM true) by (vm_compute; reflexivity);
            rewrite H; apply exec_returnm ] ].
    cbn match. reflexivity.
  Qed.

  Local Lemma hval_check_CSR_result_satp_S (D Drw : gset register)
      (rs : regstate) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D -> (mstatus : register) ∈ D ->
    eq_vec (_get_Mstatus_TVM (register_lookup mstatus rs)) ('b"1") = false ->
    hval D Drw rs (check_CSR_result csr_satp Supervisor CSRRead)
      (CSR_Check_OK tt) rs.
  Proof.
    intros HD1 HD2 HD3 HD4 HTVM.
    apply (hval_of_goodb D_ms D Drw _ (MState rs ∅ dev0_state) rs
             (CSR_Check_OK tt) (dms_sub D HD1 HD2 HD3 HD4)
             (fun r _ => eq_refl)).
    - exact (goodb_check_CSR_result_satp_S (MState rs ∅ dev0_state) HTVM).
    - exact (exec_check_CSR_result_csrr_satp_S (MState rs ∅ dev0_state) HTVM).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE SATP LEGALITY CHECK ON THE WRITE SIDE.                            *)
  (*                                                                      *)
  (* [exec_is_CSR_accessible_satp_S] was written access-type generic        *)
  (* precisely so the read above and this write share it (see the header    *)
  (* note); these are the read's three lemmas at [CSRWrite], and only the   *)
  (* [check_CSR] chain differs, because the write path is the [and_boolM]   *)
  (* chain rather than [exec_check_CSR_read_p].                             *)
  (* ------------------------------------------------------------------- *)
  Local Lemma exec_check_CSR_satp_S_w (st : mstate) :
    eq_vec (_get_Mstatus_TVM (register_lookup mstatus st.(sregs))) ('b"1")
      = false ->
    exec (check_CSR csr_satp Supervisor CSRWrite) st = Some (true, st).
  Proof.
    intro HTVM. unfold check_CSR.
    assert (Hpriv : exec (check_CSR_priv csr_satp Supervisor) st
                    = Some (true, st)) by (vm_compute; reflexivity).
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hpriv). cbn match.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (HB : exec A st = Some (true, st)) end.
    { vm_compute (check_CSR_access _ _). apply exec_returnM. }
    rewrite (exec_and_boolM_Some _ _ _ _ _ HB). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _
               (exec_is_CSR_accessible_satp_S CSRWrite st HTVM)). cbn match.
    vm_compute (stateen_allows_CSR_access csr_satp Supervisor CSRWrite).
    apply exec_returnM.
  Qed.

  Local Lemma goodb_check_CSR_satp_S_w (st : mstate) :
    eq_vec (_get_Mstatus_TVM (register_lookup mstatus st.(sregs))) ('b"1")
      = false ->
    goodb D_ms (check_CSR csr_satp Supervisor CSRWrite) st = true.
  Proof.
    intro HTVM. unfold check_CSR, Defs.and_boolM.
    erewrite goodb_bind; [ | vm_compute; reflexivity | vm_compute; reflexivity ].
    cbn match.
    erewrite goodb_bind; [ | vm_compute; reflexivity | vm_compute; reflexivity ].
    cbn match.
    erewrite goodb_bind;
      [ | vm_compute; reflexivity
        | exact (exec_is_CSR_accessible_satp_S CSRWrite st HTVM) ].
    cbn match.
    vm_compute; reflexivity.
  Qed.

  Local Lemma goodb_check_CSR_result_satp_S_w (st : mstate) :
    eq_vec (_get_Mstatus_TVM (register_lookup mstatus st.(sregs))) ('b"1")
      = false ->
    goodb D_ms (check_CSR_result csr_satp Supervisor CSRWrite) st = true.
  Proof.
    intro HTVM. unfold check_CSR_result.
    erewrite goodb_bind;
      [ | exact (goodb_check_CSR_satp_S_w st HTVM)
        | exact (exec_check_CSR_satp_S_w st HTVM) ].
    cbn match. reflexivity.
  Qed.

  Local Lemma exec_check_CSR_result_satp_S_w (st : mstate) :
    eq_vec (_get_Mstatus_TVM (register_lookup mstatus st.(sregs))) ('b"1")
      = false ->
    exec (check_CSR_result csr_satp Supervisor CSRWrite) st
      = Some (CSR_Check_OK tt, st).
  Proof.
    intro HTVM. unfold check_CSR_result.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_satp_S_w st HTVM)).
    cbn match. apply exec_returnm.
  Qed.

  (* EXPORTED (the read twin above stays [Local]): satp's write check is the
     one CSR legality [HartSCsr.hval_check_CSR_result_S] cannot serve --
     [check_TVM_SATP] reads mstatus, which is not in [D_m] and whose value no
     reference state pins -- and the trampoline's own [csrw satp] leaves
     ([UserretEntryPt], [UservecExitPt]) need it at their frame. *)
  Lemma hval_check_CSR_result_satp_S_w (D Drw : gset register)
      (rs : regstate) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D -> (mstatus : register) ∈ D ->
    eq_vec (_get_Mstatus_TVM (register_lookup mstatus rs)) ('b"1") = false ->
    hval D Drw rs (check_CSR_result csr_satp Supervisor CSRWrite)
      (CSR_Check_OK tt) rs.
  Proof.
    intros HD1 HD2 HD3 HD4 HTVM.
    apply (hval_of_goodb D_ms D Drw _ (MState rs ∅ dev0_state) rs
             (CSR_Check_OK tt) (dms_sub D HD1 HD2 HD3 HD4)
             (fun r _ => eq_refl)).
    - exact (goodb_check_CSR_result_satp_S_w (MState rs ∅ dev0_state) HTVM).
    - exact (exec_check_CSR_result_satp_S_w (MState rs ∅ dev0_state) HTVM).
  Qed.

  (* [goodb] DOES read the state (its RegRead case indexes the continuation
     by what the register holds), so this is not [goodb_legalize_satp_rv64]
     re-used at another state -- it is the same script at the OTHER concrete
     reference state.  Both compute. *)
  Local Lemma goodb_legalize_satp_rv64_S (prev value : mword 64) :
    goodb D_m (legalize_satp RV64 prev value) dstateS = true.
  Proof.
    unfold legalize_satp. cbn zeta. rewrite satp_ppn_mask_id.
    destruct (satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64 value)))
      as [sv|]; [destruct sv|]; vm_compute; reflexivity.
  Qed.

  (* [legalize_satp]'s [hval] at Supervisor: [WpGprCsrwB.hval_legalize_satp_p]
     is the parameterised transport and this is its [dstateS] instance, exactly
     as [hval_legalize_satp] is its [dstateM] one. *)
  Local Lemma hval_legalize_satp_S (D Drw : gset register) (rs : regstate)
      (o v : mword 64) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mseccfg rs = Values.mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    hval D Drw rs (legalize_satp RV64 o v) (satp_legalized o v) rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm.
    exact (hval_legalize_satp_p D_m dstateS D Drw rs o v
             (dm_sub D HD1 HD2 HD3) (agree_dm_S rs Hp Hs Hm)
             (exec_legalize_satp_rv64 o v dstateS
                ltac:(vm_compute; reflexivity))
             (goodb_legalize_satp_rv64_S o v)).
  Qed.

  (* the [pw2] twin of [WpMmodeCsrSwp.cw2_set_agree] -- the only tower fact
     of that family HartSCsr's [pw2_*] block does not already carry.  It
     BELONGS there, beside [pw2_frames_in]/[pw2_frames_out]; it is here only
     to keep this change off [HartSCsr]'s cone, and should move at a
     fold-back. *)
  Local Lemma pw2_set_agree (pr : Privilege) (r : register)
      (v0 vnew : type_of_register r) (r2 : register)
      (v2 : type_of_register r2) :
    cw2_ok r r2 ->
    reg_agree_on (cw_Drw r ∪ cw2_Dro r2)
      (register_set r vnew (pw2_rs pr r v0 r2 v2)) (pw2_rs pr r vnew r2 v2).
  Proof.
    intros Hok. pose proof Hok as (Hfr & Hfr2 & Hne).
    pose proof Hfr as (H1 & H2 & H3).
    destruct (cw_fresh_ne r2 Hfr2) as (N1 & N2 & N3).
    intros q Hq. rewrite /cw_Drw /cw2_Dro /cw_Dro in Hq.
    repeat (apply elem_of_union in Hq as [Hq|Hq]);
      apply elem_of_singleton in Hq; subst q.
    - etransitivity; [apply register_lookup_set|].
      symmetry. apply (pw2_rs_r pr r vnew r2 v2 Hok).
    - etransitivity;
        [apply irrelevant_register_set;
         exact (register_beq_false r2 r (fun H => Hne (eq_sym H)))|].
      etransitivity; [apply (pw2_rs_r2 pr r v0 r2 v2)|].
      symmetry. apply (pw2_rs_r2 pr r vnew r2 v2).
    - etransitivity; [apply irrelevant_register_set; exact H3|].
      etransitivity; [apply (pw2_rs_priv pr r v0 r2 v2 Hok)|].
      symmetry. apply (pw2_rs_priv pr r vnew r2 v2 Hok).
    - etransitivity; [apply irrelevant_register_set; exact H2|].
      etransitivity; [apply (pw2_rs_sec pr r v0 r2 v2 Hok)|].
      symmetry. apply (pw2_rs_sec pr r vnew r2 v2 Hok).
    - etransitivity; [apply irrelevant_register_set; exact H1|].
      etransitivity; [apply (pw2_rs_misa pr r v0 r2 v2 Hok)|].
      symmetry. apply (pw2_rs_misa pr r vnew r2 v2 Hok).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE SATP WRITE AT SUPERVISOR.                                        *)
  (*                                                                      *)
  (* [WpGprCsrwB.swp_write_CSR_satp] is this at Machine, and the two differ *)
  (* in exactly two places: the reference tower is [HartSCsr.pw2_rs] at    *)
  (* [Supervisor] instead of [WpMmodeCsrSwp.cw2_rs] (which pins Machine),  *)
  (* and [legalize_satp]'s [hval] is transported off [dstateS] instead of  *)
  (* [dstateM].  The generic form cannot live beside the Machine one --    *)
  (* [pw2_*] is in [HartSCsr], which sits ABOVE [WpGprCsrwB] -- so the two  *)
  (* statements stand side by side, sharing                                *)
  (* [WpGprCsrwB.hval_legalize_satp_p], the parameterised transport.        *)
  (* ------------------------------------------------------------------- *)
  Lemma swp_write_CSR_satp_S (dq dq2 : dfrac) (satp0 ms0 v : mword 64) :
    cw2_ok satp mstatus ->
    _get_Mstatus_SXL ms0 = 'b"10" ->
    gen_cert -∗
    (hreg_frame (pw2_rs Supervisor satp satp0 mstatus ms0) (cw_Drw satp) -∗
     hreg_frame_ro (cw2_Df dq dq2 mstatus) (pw2_rs Supervisor satp satp0 mstatus ms0)
       (cw2_Dro mstatus) -∗
     swp (write_CSR csr_satp v)
       (fun x => ⌜x = Ok (satp_legalized satp0 v)⌝ ∗
          hreg_frame (pw2_rs Supervisor satp (satp_legalized satp0 v) mstatus ms0)
            (cw_Drw satp) ∗
          hreg_frame_ro (cw2_Df dq dq2 mstatus)
            (pw2_rs Supervisor satp (satp_legalized satp0 v) mstatus ms0)
            (cw2_Dro mstatus))).
  Proof.
    intros Hok HSXL. iIntros "#Hcert Hrw Hro".
    rewrite write_CSR_satp_red.
    (* 1. the architecture read, walked *)
    iApply (swp_bind_use (architecture Supervisor) _
              (fun a => ⌜a = RV64⌝ ∗
                 hreg_frame (pw2_rs Supervisor satp satp0 mstatus ms0) (cw_Drw satp) ∗
                 hreg_frame_ro (cw2_Df dq dq2 mstatus)
                   (pw2_rs Supervisor satp satp0 mstatus ms0) (cw2_Dro mstatus))%I _
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 4 (cw_Drw satp) (cw2_Dro mstatus)
                (cw2_Df dq dq2 mstatus) (pw2_rs Supervisor satp satp0 mstatus ms0) _ _ _
                (cw2_disj satp mstatus Hok)
                (hfrun_architecture_Supervisor
                   (cw_Drw satp ∪ cw2_Dro mstatus) (cw_Drw satp)
                   (pw2_rs Supervisor satp satp0 mstatus ms0)
                   (cw2_in_r2 satp mstatus)
                   ltac:(rewrite (pw2_rs_r2 Supervisor satp satp0 mstatus ms0);
                         exact HSXL))
                with "Hcert Hrw Hro"). }
    iIntros (a) "(-> & Hrw & Hro)".
    (* 2. the satp read, at the frame *)
    iApply (swp_bind_use (Defs.read_reg satp) _
              (fun o => ⌜o = satp0⌝ ∗
                 hreg_frame (pw2_rs Supervisor satp satp0 mstatus ms0) (cw_Drw satp) ∗
                 hreg_frame_ro (cw2_Df dq dq2 mstatus)
                   (pw2_rs Supervisor satp satp0 mstatus ms0) (cw2_Dro mstatus))%I _
              with "[Hrw Hro] [-]").
    { iApply (swp_mono with "[] [-]");
        [| iApply (swp_read_reg_pinned (cw_Drw satp) (cw2_Dro mstatus)
                     (cw2_Df dq dq2 mstatus) (pw2_rs Supervisor satp satp0 mstatus ms0)
                     satp (cw2_disj satp mstatus Hok)
                     (cw2_in_r satp mstatus) with "Hcert Hrw Hro") ].
      iIntros (o) "(-> & Hrw & Hro)".
      rewrite (pw2_rs_r Supervisor satp satp0 mstatus ms0 Hok). by iFrame. }
    iIntros (o) "(-> & Hrw & Hro)".
    (* 3. the legalization, goodb-transported *)
    iApply (swp_bind_use (legalize_satp RV64 satp0 v) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_span (cw_Drw satp) (cw2_Dro mstatus)
                (cw2_Df dq dq2 mstatus) (pw2_rs Supervisor satp satp0 mstatus ms0)
                (pw2_rs Supervisor satp satp0 mstatus ms0) _ _
                (cw2_disj satp mstatus Hok)
                (hval_legalize_satp_S (cw_Drw satp ∪ cw2_Dro mstatus)
                   (cw_Drw satp) (pw2_rs Supervisor satp satp0 mstatus ms0) satp0 v
                   (cw2_in_priv satp mstatus) (cw2_in_sec satp mstatus)
                   (cw2_in_misa satp mstatus)
                   (pw2_rs_priv Supervisor satp satp0 mstatus ms0 Hok)
                   (pw2_rs_sec Supervisor satp satp0 mstatus ms0 Hok)
                   (pw2_rs_misa Supervisor satp satp0 mstatus ms0 Hok))
                with "Hcert Hrw Hro"). }
    iIntros (c) "(-> & Hrw & Hro)".
    (* 4. the write and the readback *)
    iApply (swp_bind_use _ _
              (fun c2 => ⌜c2 = satp_legalized satp0 v⌝ ∗
                 hreg_frame (pw2_rs Supervisor satp (satp_legalized satp0 v) mstatus ms0)
                   (cw_Drw satp) ∗
                 hreg_frame_ro (cw2_Df dq dq2 mstatus)
                   (pw2_rs Supervisor satp (satp_legalized satp0 v) mstatus ms0)
                   (cw2_Dro mstatus))%I _
              with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => hreg_frame
                   (pw2_rs Supervisor satp (satp_legalized satp0 v) mstatus ms0)
                   (cw_Drw satp) ∗
                   hreg_frame_ro (cw2_Df dq dq2 mstatus)
                     (pw2_rs Supervisor satp (satp_legalized satp0 v) mstatus ms0)
                     (cw2_Dro mstatus))%I _
                with "[Hrw Hro] [-]").
      { iApply (swp_mono with "[] [-]");
          [| iApply (swp_write_reg_owned (cw_Drw satp) (cw2_Dro mstatus)
                       (cw2_Df dq dq2 mstatus)
                       (pw2_rs Supervisor satp satp0 mstatus ms0) satp _
                       (cw2_disj satp mstatus Hok) (cw2_w_r satp mstatus)
                       with "Hcert Hrw Hro") ].
        iIntros (u) "[Hrw Hro]".
        iDestruct (cw2_rw_ext satp _ _
                     (reg_agree_l _ _ _ _
                        (pw2_set_agree Supervisor satp satp0 _ mstatus ms0 Hok))
                     with "Hrw") as "Hrw".
        iDestruct (cw2_ro_ext dq dq2 mstatus _ _
                     (reg_agree_r _ _ _ _
                        (pw2_set_agree Supervisor satp satp0 _ mstatus ms0 Hok))
                     with "Hro") as "Hro".
        by iFrame. }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_mono with "[] [-]");
        [| iApply (swp_read_reg_pinned (cw_Drw satp) (cw2_Dro mstatus)
                     (cw2_Df dq dq2 mstatus)
                     (pw2_rs Supervisor satp (satp_legalized satp0 v) mstatus ms0) satp
                     (cw2_disj satp mstatus Hok) (cw2_in_r satp mstatus)
                     with "Hcert Hrw Hro") ].
      iIntros (c2) "(-> & Hrw & Hro)".
      rewrite (pw2_rs_r Supervisor satp (satp_legalized satp0 v) mstatus ms0 Hok).
      by iFrame. }
    iIntros (c2) "(-> & Hrw & Hro)".
    iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.
End SWrites.

Section WpSconfCsr.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.



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

  (* ENABLING, so the same index discipline as [wp_csrsi_sstatus_x0_s_sconf]:
     pre [trap_res true + n], post [trap_res eb + n].  At [eb = true] the two
     coincide (the write is idempotent and the reserve rides through); at
     [eb = false] this delegates to that leaf at [b := false], whose pre/post
     indices are then literally these. *)

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
    assert (Hfresh : cw_fresh (R_bitvector_64 stvec))
      by (split_and!; vm_compute; reflexivity).
    iApply (wp_instr_s_sconf m n false false pc false
              (CSRReg (csr_stvec, Regidx rs1, zreg, CSRRW))
              (fun (_ : CpuId) npc ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗ ⌜m' = m⌝ ∗ ⌜n' = n⌝ ∗
                 stvec ↦ᵣ wval)%I
              with "Hcg Hpc Hinstr [Hstv Hcont]").
    iNext. iApply wp_next_off_intro. rewrite /sconf_step_obl.
    iSplitL "Hstv".
    - iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct (sconf_to_cells with "Hsc") as (ms0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
          Hmdl & Hmenv)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
          %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0 mseccfg0.
      iDestruct (pw_frames_in Supervisor (DfracOwn 1) (R_bitvector_64 stvec) tv0
                   Hfresh with "Hstv Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      change (execute (CSRReg (csr_stvec, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_stvec (Regidx rs1) zreg CSRRW).
      iApply (swp_mono with
                "[Hms Hhalf Hspp Hmie Hmdl Hmenv Hcap HPC HnPC Hresv] [Hrw Hro Hfile]");
        [| iApply (swp_execute_CSRReg_w_p (cw_Drw (R_bitvector_64 stvec)) cw_Dro
                     (cw_Df (DfracOwn 1))
                     (pw_rs Supervisor (R_bitvector_64 stvec) tv0)
                     (pw_rs Supervisor (R_bitvector_64 stvec) wval)
                     (tp_pin m) csr_stvec Supervisor rs1 wval
                     (cw_disj _ Hfresh) (cw_in_priv _)
                     (pw_rs_priv Supervisor (R_bitvector_64 stvec) tv0 Hfresh)
                     ltac:(by vm_compute)
                     (hval_check_CSR_result_S _ _ _ csr_stvec CSRWrite
                        (cw_in_priv _) (cw_in_sec _) (cw_in_misa _)
                        (pw_rs_priv Supervisor (R_bitvector_64 stvec) tv0 Hfresh)
                        (pw_rs_sec Supervisor (R_bitvector_64 stvec) tv0 Hfresh)
                        (pw_rs_misa Supervisor (R_bitvector_64 stvec) tv0 Hfresh)
                        ltac:(by vm_compute)
                        (exec_check_CSR_result_csrw_stvec_S dstateS
                           ltac:(by vm_compute)))
                     ltac:(by vm_compute) ltac:(by vm_compute)
                     ltac:(by vm_compute)
                     with "Hcert Hfile Hrw Hro [ ]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (pw_frames_out Supervisor (DfracOwn 1) (R_bitvector_64 stvec)
                     wval Hfresh with "[$Hrw $Hro]") as "(Hstv & Hpriv & _ & _)".
        iSplitR; [done|].
        iExists (add_vec_int pc 4), ms0, m, n.
        iFrame "HPC HnPC Hresv".
        iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
        { rewrite /sconf_at_priv. iExists mdv0.
          iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
          iPureIntro. split; [exact Hmsf | exact Hmm]. }
        iFrame "Hcap Hf".
        iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iExact "Hstv".
      + iIntros "Hrw Hro".
        change (tp_pin m !!! Regidx rs1) with (rget m rs1). rewrite Hwval.
        iApply (swp_write_CSR_stvec_S (DfracOwn 1) tv0 wval Hmode
                  with "Hcert Hrw Hro").
    - iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & -> & Hstv)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! cpu_id with "[%] Hcg' Hstv Hpc'"). done.
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

  (* ---- THE RESTORE SHAPE: the written word is one an earlier [csrr
     sstatus] read, so the five field premises above come from that mstatus'
     [sconf_ms_facts] and the S-view/M-view field agreement
     ([WpGprCsrwC.sX_lower]).  This is kerneltrap's [csrw sstatus,s1] and
     kernelvec's route to [sret]; the statement is unchanged from before the
     leaf above was generalized, so its call sites are untouched. ---- *)

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
    assert (Hfresh : cw_fresh (R_bitvector_64 sepc))
      by (split_and!; vm_compute; reflexivity).
    iApply (wp_instr_s_sconf m n false false pc false
              (CSRReg (csr_sepc, Regidx rs1, zreg, CSRRW))
              (fun (_ : CpuId) npc ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗ ⌜m' = m⌝ ∗ ⌜n' = n⌝ ∗
                 sepc ↦ᵣ mepc_val wval)%I
              with "Hcg Hpc Hinstr [Hsepc Hcont]").
    iNext. iApply wp_next_off_intro. rewrite /sconf_step_obl.
    iSplitL "Hsepc".
    - iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct (sconf_to_cells with "Hsc") as (ms0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
          Hmdl & Hmenv)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
          %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0 mseccfg0.
      iDestruct (pw_frames_in Supervisor (DfracOwn 1) (R_bitvector_64 sepc) ep0
                   Hfresh with "Hsepc Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      change (execute (CSRReg (csr_sepc, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_sepc (Regidx rs1) zreg CSRRW).
      iApply (swp_mono with
                "[Hms Hhalf Hspp Hmie Hmdl Hmenv Hcap HPC HnPC Hresv] [Hrw Hro Hfile]");
        [| iApply (swp_execute_CSRReg_w_p (cw_Drw (R_bitvector_64 sepc)) cw_Dro
                     (cw_Df (DfracOwn 1))
                     (pw_rs Supervisor (R_bitvector_64 sepc) ep0)
                     (pw_rs Supervisor (R_bitvector_64 sepc) (mepc_val wval))
                     (tp_pin m) csr_sepc Supervisor rs1 (mepc_val wval)
                     (cw_disj _ Hfresh) (cw_in_priv _)
                     (pw_rs_priv Supervisor (R_bitvector_64 sepc) ep0 Hfresh)
                     ltac:(by vm_compute)
                     (hval_check_CSR_result_S _ _ _ csr_sepc CSRWrite
                        (cw_in_priv _) (cw_in_sec _) (cw_in_misa _)
                        (pw_rs_priv Supervisor (R_bitvector_64 sepc) ep0 Hfresh)
                        (pw_rs_sec Supervisor (R_bitvector_64 sepc) ep0 Hfresh)
                        (pw_rs_misa Supervisor (R_bitvector_64 sepc) ep0 Hfresh)
                        ltac:(by vm_compute)
                        (exec_check_CSR_result_csrw_sepc_S dstateS
                           ltac:(by vm_compute)))
                     ltac:(by vm_compute) ltac:(by vm_compute)
                     ltac:(by vm_compute)
                     with "Hcert Hfile Hrw Hro [ ]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (pw_frames_out Supervisor (DfracOwn 1) (R_bitvector_64 sepc)
                     (mepc_val wval) Hfresh with "[$Hrw $Hro]")
          as "(Hsepc & Hpriv & _ & _)".
        iSplitR; [done|].
        iExists (add_vec_int pc 4), ms0, m, n.
        iFrame "HPC HnPC Hresv".
        iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
        { rewrite /sconf_at_priv. iExists mdv0.
          iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
          iPureIntro. split; [exact Hmsf | exact Hmm]. }
        iFrame "Hcap Hf".
        iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iExact "Hsepc".
      + iIntros "Hrw Hro".
        change (tp_pin m !!! Regidx rs1) with (rget m rs1). rewrite Hwval.
        iApply (swp_write_CSR_sepc_S (DfracOwn 1) ep0 wval
                  with "Hcert Hrw Hro").
    - iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & -> & Hsepc)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! cpu_id with "[%] Hcg' Hsepc Hpc'"). done.
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
    (* THE CELL IS NONE OF THE THREE CONFIG PINS -- [vm_compute] at every
       instance.  It is what makes the four-cell footprint disjoint. *)
    cw_fresh (R_bitvector_64 rg) ->
    (* THE FOUR CHECK FACTS.  The legality check is READ-ONLY however deep,
       so it rides [HartGoodb.hval_of_goodb] off the Supervisor reference
       state -- [HartSCsr.hval_check_CSR_result_S], whose read set is [D_m]
       (measured: the stateen gate that would read menvcfg is off at
       MENVCFG_S, so the check reads the same three cells at Supervisor as at
       Machine).  Each instance discharges these by [vm_compute] plus the
       exec-layer fact it already had. *)
    ext_check_CSR csrn Supervisor CSRRead = true ->
    goodb D_m (check_CSR_result csrn Supervisor CSRRead) dstateS = true ->
    exec (check_CSR_result csrn Supervisor CSRRead) dstateS
      = Some (CSR_Check_OK tt, dstateS) ->
    eq_vec csrn (Ox"344") = false ->
    eq_vec csrn (Ox"144") = false ->
    (forall x, csr_id_read_callback csrn x = Defs.returnm tt) ->
    (* THE READ ITSELF, AS AN [swp] OBLIGATION -- the premise that replaces
       the old whole-[execute] [exec] fact, and it HAD to.  An [exec] fact
       quantifies over the START state only, while a per-node walk may be
       interfered with between nodes, so nothing bridges the two; the same
       change [WpSmodeIntr.wp_gpr_write_s_sconf] made.  It is stated
       FRAME-GENERICALLY so the instances below say nothing about which
       footprint the engine picks: all they need is that the cell and misa
       are pinned. *)
    ( ∀ (Drw Dro : gset register) (Df : register -> dfrac) (rs : regstate),
        ⌜ Drw ## Dro /\
          (R_bitvector_64 rg : register) ∈ Drw ∪ Dro /\
          (misa : register) ∈ Drw ∪ Dro /\
          (cur_privilege : register) ∈ Drw ∪ Dro /\
          (mseccfg : register) ∈ Drw ∪ Dro /\
          register_lookup (R_bitvector_64 rg) rs = v /\
          register_lookup misa rs = MISA_C /\
          register_lookup cur_privilege rs = Supervisor /\
          register_lookup mseccfg rs = mword_of_int 0 ⌝ -∗
        gen_cert -∗ hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
        swp (read_CSR csrn)
          (fun x => ⌜x = f v⌝ ∗ hreg_frame rs Drw ∗
                    hreg_frame_ro Df rs Dro) ) -∗
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
    iIntros (Hrd Hrdok Hne Hfresh Hext Hgb Hex H344 H144 Hcb)
            "Hrdcsr Hcg Hcell Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (f v)]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iApply (wp_instr_s_sconf m n false false pc false
              (CSRReg (csrn, zreg, Regidx rd, CSRRS))
              (fun (_ : CpuId) npc ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗
                 ⌜m' = <[Regidx rd := regval_into_reg (f v)]> m⌝ ∗
                 ⌜n' = n⌝ ∗ R_bitvector_64 rg ↦ᵣ{dq} v)%I
              with "Hcg Hpc Hinstr [Hrdcsr Hcell Hcont]").
    (* INTERRUPTS ARE OFF AT THIS LEAF, so the funnel's hart-generic callback
       is discharged at the ambient hart and nothing is renamed. *)
    iNext. iApply wp_next_off_intro. rewrite /sconf_step_obl.
    iSplitL "Hrdcsr Hcell".
    - (* ---- the instruction ---- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct (sconf_to_cells with "Hsc") as (ms0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hsie & Hsret & Hmie &
          Hmdl & Hmenv)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
          %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0 mseccfg0.
      iDestruct (pr_frames_in Supervisor (DfracOwn 1) dq (R_bitvector_64 rg) v
                   Hfresh with "Hcell Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      change (execute (CSRReg (csrn, zreg, Regidx rd, CSRRS)))
        with (execute_CSRReg csrn zreg (Regidx rd) CSRRS).
      iApply (swp_mono with
                "[Hms Hsie Hsret Hmie Hmdl Hmenv Hcap HPC HnPC Hresv]
                 [Hrw Hro Hfile Hrdcsr]");
        [| iApply (swp_execute_CSRReg_r_p ∅ (cr_Dro (R_bitvector_64 rg))
                     (cr_Df (DfracOwn 1) dq (R_bitvector_64 rg))
                     (pw_rs Supervisor (R_bitvector_64 rg) v) (tp_pin m)
                     csrn Supervisor rd (f v)
                     (cr_disj _) (cr_in_priv _)
                     (pw_rs_priv Supervisor (R_bitvector_64 rg) v Hfresh) Hrd Hext
                     (hval_check_CSR_result_S _ ∅ _ csrn CSRRead
                        (cr_in_priv _) (cr_in_sec _) (cr_in_misa _)
                        (pw_rs_priv Supervisor (R_bitvector_64 rg) v Hfresh)
                        (pw_rs_sec Supervisor (R_bitvector_64 rg) v Hfresh)
                        (pw_rs_misa Supervisor (R_bitvector_64 rg) v Hfresh) Hgb Hex)
                     H344 H144 Hcb with "Hcert Hfile Hrw Hro [Hrdcsr]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (pr_frames_out Supervisor (DfracOwn 1) dq
                     (R_bitvector_64 rg) v Hfresh with "Hro")
          as "(Hcell & Hpriv & _ & _)".
        iSplitR; [done|].
        iExists (add_vec_int pc 4), ms0,
                (<[Regidx rd := regval_into_reg (f v)]> m), n.
        iFrame "HPC HnPC Hresv".
        iSplitL "Hpriv Hms Hsie Hsret Hmie Hmdl Hmenv".
        { rewrite /sconf_at_priv. iExists mdv0.
          iFrame "Hhw Hminv Hpriv Hms Hsie Hsret Hmie Hmdl Hmenv".
          iPureIntro. split; [exact Hmsf | exact Hmm]. }
        iSplitL "Hcap".
        { iApply (sie_cap_retarget m
                    (<[Regidx rd := regval_into_reg (f v)]> m) n false Hsp
                    with "Hcap"). }
        iSplitL "Hf".
        { iEval (rewrite (tp_pin_upd m rd (regval_into_reg (f v)) Hrdtp))
            in "Hf". iExact "Hf". }
        iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iExact "Hcell".
      + iIntros "Hrw Hro".
        iApply ("Hrdcsr" $! ∅ (cr_Dro (R_bitvector_64 rg))
                  (cr_Df (DfracOwn 1) dq (R_bitvector_64 rg))
                  (pw_rs Supervisor (R_bitvector_64 rg) v)
                  with "[%] Hcert Hrw Hro").
        split_and!;
          [ apply cr_disj | apply cr_in_r | apply cr_in_misa
          | apply cr_in_priv | apply cr_in_sec
          | apply (pw_rs_r Supervisor (R_bitvector_64 rg) v)
          | apply (pw_rs_misa Supervisor (R_bitvector_64 rg) v Hfresh)
          | apply (pw_rs_priv Supervisor (R_bitvector_64 rg) v Hfresh)
          | apply (pw_rs_sec Supervisor (R_bitvector_64 rg) v Hfresh) ].
    - (* ---- the continuation ---- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & -> & Hcell)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! cpu_id with "[%] Hcg' Hcell Hpc'"). done.
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
    iIntros (Hrd Hrdok) "Hcg Hcell Hpc Hinstr Hcont".
    assert (Hfresh : cw_fresh (R_bitvector_64 scause))
      by (split_and!; vm_compute; reflexivity).
    iApply (wp_csrr_ro_s_sconf pc csr_scause scause (fun x => x) rd m n dq sc
              Hrd Hrdok ltac:(by vm_compute) Hfresh
              ltac:(by vm_compute)
              ltac:(by vm_compute)
              (exec_check_CSR_result_scause_S dstateS ltac:(by vm_compute))
              ltac:(by vm_compute) ltac:(by vm_compute)
              ltac:(intro; by vm_compute)
              with "[] Hcg Hcell Hpc Hinstr Hcont").
    iIntros (Drw Dro Df rs (Hd & Hin & _ & _ & _ & Hv & _)) "#Hcert Hrw Hro".
    rewrite read_CSR_scause_red.
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_read_reg_pinned Drw Dro Df rs (R_bitvector_64 scause)
                   Hd Hin with "Hcert Hrw Hro") ].
    iIntros (x) "(-> & Hrw & Hro)". rewrite Hv. by iFrame.
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
    iIntros (Hrd Hrdok) "Hcg Hcell Hpc Hinstr Hcont".
    assert (Hfresh : cw_fresh (R_bitvector_64 stval))
      by (split_and!; vm_compute; reflexivity).
    iApply (wp_csrr_ro_s_sconf pc csr_stval stval (fun x => x) rd m n dq tv
              Hrd Hrdok ltac:(by vm_compute) Hfresh
              ltac:(by vm_compute)
              ltac:(by vm_compute)
              (exec_check_CSR_result_stval_S dstateS ltac:(by vm_compute))
              ltac:(by vm_compute) ltac:(by vm_compute)
              ltac:(intro; by vm_compute)
              with "[] Hcg Hcell Hpc Hinstr Hcont").
    iIntros (Drw Dro Df rs (Hd & Hin & _ & _ & _ & Hv & _)) "#Hcert Hrw Hro".
    rewrite read_CSR_stval_red.
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_read_reg_pinned Drw Dro Df rs (R_bitvector_64 stval)
                   Hd Hin with "Hcert Hrw Hro") ].
    iIntros (x) "(-> & Hrw & Hro)". rewrite Hv. by iFrame.
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
    iIntros (Hrd Hrdok) "Hcg Hcell Hpc Hinstr Hcont".
    assert (Hfresh : cw_fresh (R_bitvector_64 sepc))
      by (split_and!; vm_compute; reflexivity).
    iApply (wp_csrr_ro_s_sconf pc csr_sepc sepc mepc_val rd m n dq ep
              Hrd Hrdok ltac:(by vm_compute) Hfresh
              ltac:(by vm_compute)
              ltac:(by vm_compute)
              (exec_check_CSR_result_sepc_S dstateS ltac:(by vm_compute))
              ltac:(by vm_compute) ltac:(by vm_compute)
              ltac:(intro; by vm_compute)
              with "[] Hcg Hcell Hpc Hinstr Hcont").
    (* sepc's read is NOT its cell: [align_pc] clears bit 0, so the stretch
       is the cell read followed by a misa-gated pure step.  The first is a
       pinned node, the second the goodb transport above. *)
    iIntros (Drw Dro Df rs (Hd & Hin & Hmi & Hpriv & Hsec & Hv & Hmisa & Hlpriv & Hlsec))
            "#Hcert Hrw Hro".
    rewrite read_CSR_sepc_red.
    iApply (swp_bind_use (Defs.read_reg (R_bitvector_64 sepc)) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs (R_bitvector_64 sepc)
                Hd Hin with "Hcert Hrw Hro"). }
    iIntros (x) "(-> & Hrw & Hro)". rewrite Hv.
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_span Drw Dro Df rs rs _ (mepc_val ep) Hd
                   (hval_align_pc (Drw ∪ Dro) Drw rs ep Hpriv Hsec Hmi
                      Hlpriv Hlsec Hmisa) with "Hcert Hrw Hro") ].
    iIntros (y) "(-> & Hrw & Hro)". by iFrame.
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
    assert (Hfresh : cw_fresh (R_bitvector_64 mstatus))
      by (split_and!; vm_compute; reflexivity).
    assert (Himm2 : eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false)
      by (vm_compute; reflexivity).
    iApply (wp_instr_s_sconf m n false false pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRC))
              (fun (_ : CpuId) npc ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗ ⌜m' = m⌝ ∗ ⌜n' = n⌝ ∗
                 ⌜∃ ms : mword 64, sconf_ms_facts ms⌝)%I
              with "Hcg Hpc Hinstr [Hcont]").
    iNext. iApply wp_next_off_intro. rewrite /sconf_step_obl.
    iSplitR "Hcont".
    - (* ---- the instruction: a read-MODIFY-write at x0 ---- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct (sconf_to_cells with "Hsc") as (ms0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
          Hmdl & Hmenv)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
          %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0 mseccfg0.
      (* the disabled arm IS its own eighth; the agreement pins the live SIE
         bit at '0', which is what makes this write idempotent on the ghost. *)
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      iDestruct (ghost_var_agree with "Hhalf Harm") as %Hb0.
      destruct (csrci_sie_flip ms0 Hmsf) as (Hsie' & Hspp' & Hspie' & Hmsf').
      iDestruct (pw_frames_in Supervisor (DfracOwn 1) (R_bitvector_64 mstatus)
                   ms0 Hfresh with "Hms Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      change (execute (CSRImm (csr_sstatus, mword_of_int 2,
                               Regidx (mword_of_int 0), CSRRC)))
        with (execute_CSRImm csr_sstatus (mword_of_int 2)
                (Regidx (mword_of_int 0)) CSRRC).
      iApply (swp_mono with
                "[Hstk Htr Harm Hhalf Hspp Hmie Hmdl Hmenv HPC HnPC Hresv]
                 [Hrw Hro Hfile]");
        [| iApply (swp_execute_CSRImm_rw_p (cw_Drw (R_bitvector_64 mstatus))
                     cw_Dro (cw_Df (DfracOwn 1))
                     (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                     (pw_rs Supervisor (R_bitvector_64 mstatus)
                        (legalize_sstatus_val ms0
                           (sstatus_write_val ms0 (mword_of_int 2))))
                     (tp_pin m) (tp_pin m) csr_sstatus Supervisor
                     (mword_of_int 2) (mword_of_int 0) CSRRC
                     (sstatus_read ms0) (sstatus_write_val ms0 (mword_of_int 2))
                     (subrange_vec_dec
                        (lower_mstatus (legalize_sstatus_val ms0
                           (sstatus_write_val ms0 (mword_of_int 2))))
                        (Z.sub xlen 1) 0)
                     (cw_disj _ Hfresh) (cw_in_priv _)
                     (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                     Himm2 ltac:(intros bb; reflexivity)
                     ltac:(by vm_compute)
                     (hval_check_CSR_result_S _ _ _ csr_sstatus CSRReadWrite
                        (cw_in_priv _) (cw_in_sec _) (cw_in_misa _)
                        (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        (pw_rs_sec Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        (pw_rs_misa Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        ltac:(by vm_compute)
                        (exec_check_CSR_result_sstatus_S dstateS
                           ltac:(by vm_compute)))
                     ltac:(by vm_compute) ltac:(by vm_compute)
                     eq_refl ltac:(by vm_compute)
                     with "Hcert Hfile Hrw Hro [] [] []") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (pw_frames_out Supervisor (DfracOwn 1) (R_bitvector_64 mstatus)
                     _ Hfresh with "[$Hrw $Hro]") as "(Hms & Hpriv & _ & _)".
        iEval (rewrite Hb0) in "Hhalf". iEval (rewrite -Hsie') in "Hhalf".
        (* SPP and SPIE are untouched by an SIE flip, so the tie only needs
           re-expressing at the new mstatus -- no ghost movement. *)
        iDestruct (sret_tie_congr ms0 _ Hspp' Hspie' with "Hspp") as "Hspp".
        iSplitR; [done|].
        iExists (add_vec_int pc 4),
                (legalize_sstatus_val ms0
                   (sstatus_write_val ms0 (mword_of_int 2))), m, n.
        iFrame "HPC HnPC Hresv".
        iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
        { rewrite /sconf_at_priv. iExists mdv0.
          iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
          iPureIntro. split; [exact Hmsf' | exact Hmm]. }
        iSplitL "Hstk Htr Harm". { iFrame "Hstk Htr Harm Hwit". }
        iFrame "Hf".
        iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
        iPureIntro. exists ms0. exact Hmsf.
      + (* the CSR read *)
        iIntros "Hrw Hro". rewrite read_CSR_sstatus_red.
        iApply (swp_bind_use _ _
                  (fun o : mword 64 => ⌜o = ms0⌝ ∗
                     hreg_frame (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                       (cw_Drw (R_bitvector_64 mstatus)) ∗
                     hreg_frame_ro (cw_Df (DfracOwn 1))
                       (pw_rs Supervisor (R_bitvector_64 mstatus) ms0) cw_Dro)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_mono with "[] [-]");
            [| iApply (swp_read_reg_pinned (cw_Drw (R_bitvector_64 mstatus))
                         cw_Dro (cw_Df (DfracOwn 1))
                         (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                         (R_bitvector_64 mstatus) (cw_disj _ Hfresh)
                         (cw_in_r _) with "Hcert Hrw Hro") ].
          iIntros (o) "(-> & Hrw & Hro)".
          rewrite (pw_rs_r Supervisor (R_bitvector_64 mstatus) ms0). by iFrame. }
        iIntros (o) "(-> & Hrw & Hro)". iApply swp_ret. by iFrame.
      + (* the CSR write *)
        iIntros "Hrw Hro".
        iApply (swp_write_CSR_sstatus_S (DfracOwn 1) ms0 _ with "Hcert Hrw Hro").
      + (* the rd write, at x0: a no-op *)
        iIntros "Hf". iApply (swp_wX_zero (mword_of_int 0) _ _
                                ltac:(by vm_compute) with "Hf").
    - (* ---- the continuation ---- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & -> & %Hex)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      destruct Hex as (ms & Hmsf).
      iSpecialize ("Hcont" $! cpu_id with "[%]"); [done|].
      iApply ("Hcont" $! ms with "[%] Hcg' Hpc'"). exact Hmsf.
  Qed.

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
    assert (Hfresh : cw_fresh (R_bitvector_64 mstatus))
      by (split_and!; vm_compute; reflexivity).
    assert (Himm2 : eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false)
      by (vm_compute; reflexivity).
    iApply (wp_instr_s_sconf m n true true pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS))
              (fun (_ : CpuId) npc ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗ ⌜m' = m⌝ ∗ ⌜n' = n⌝ ∗
                 ⌜∃ ms : mword 64, sconf_ms_facts ms⌝)%I
              with "Hcg Hpc Hinstr [Hcont]").
    iNext.
    (* FREE THE NAME [CID] FOR THE REBOUND HART: with interrupts enabled the
       instruction can be trapped and the thread resumed elsewhere, so every
       resource below is about the hart the callback binds. *)
    rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl.
    iSplitR "Hcont".
    - (* ---- the instruction: a read-MODIFY-write at x0 ---- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct (sconf_to_cells with "Hsc") as (ms0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
          Hmdl & Hmenv)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
          %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0 mseccfg0.
      (* the ENABLED arm rides through untouched; all that is wanted from it
         is its own eighth, for the agreement that pins the live bit at '1'. *)
      iDestruct "Hcap" as "(Hstk & Htr & (Hq1 & Harest) & #Hwit)".
      iDestruct (ghost_var_agree with "Hhalf Hq1") as %Hb1.
      destruct (csrsi_sie_flip ms0 Hmsf) as (Hsie' & Hspp' & Hspie' & Hmsf').
      iDestruct (pw_frames_in (CID := CID) Supervisor (DfracOwn 1)
                   (R_bitvector_64 mstatus) ms0 Hfresh
                   with "Hms Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      change (execute (CSRImm (csr_sstatus, mword_of_int 2,
                               Regidx (mword_of_int 0), CSRRS)))
        with (execute_CSRImm csr_sstatus (mword_of_int 2)
                (Regidx (mword_of_int 0)) CSRRS).
      iApply (swp_mono (CID := CID) with
                "[Hstk Htr Hq1 Harest Hhalf Hspp Hmie Hmdl Hmenv HPC HnPC Hresv]
                 [Hrw Hro Hfile]");
        [| iApply (swp_execute_CSRImm_rw_p (CID := CID)
                     (cw_Drw (R_bitvector_64 mstatus))
                     cw_Dro (cw_Df (DfracOwn 1))
                     (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                     (pw_rs Supervisor (R_bitvector_64 mstatus)
                        (legalize_sstatus_val ms0
                           (sstatus_write_set_val ms0 (mword_of_int 2))))
                     (tp_pin (CID := CID) m) (tp_pin (CID := CID) m)
                     csr_sstatus Supervisor
                     (mword_of_int 2) (mword_of_int 0) CSRRS
                     (sstatus_read ms0)
                     (sstatus_write_set_val ms0 (mword_of_int 2))
                     (subrange_vec_dec
                        (lower_mstatus (legalize_sstatus_val ms0
                           (sstatus_write_set_val ms0 (mword_of_int 2))))
                        (Z.sub xlen 1) 0)
                     (cw_disj _ Hfresh) (cw_in_priv _)
                     (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                     Himm2 ltac:(intros bb; reflexivity)
                     ltac:(by vm_compute)
                     (hval_check_CSR_result_S _ _ _ csr_sstatus CSRReadWrite
                        (cw_in_priv _) (cw_in_sec _) (cw_in_misa _)
                        (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        (pw_rs_sec Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        (pw_rs_misa Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        ltac:(by vm_compute)
                        (exec_check_CSR_result_sstatus_S dstateS
                           ltac:(by vm_compute)))
                     ltac:(by vm_compute) ltac:(by vm_compute)
                     eq_refl ltac:(by vm_compute)
                     with "Hcert Hfile Hrw Hro [] [] []") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (pw_frames_out (CID := CID) Supervisor (DfracOwn 1)
                     (R_bitvector_64 mstatus) _ Hfresh with "[$Hrw $Hro]")
          as "(Hms & Hpriv & _ & _)".
        iEval (rewrite Hb1) in "Hhalf". iEval (rewrite -Hsie') in "Hhalf".
        iDestruct (sret_tie_congr (CID := CID) ms0 _ Hspp' Hspie' with "Hspp")
          as "Hspp".
        iSplitR; [done|].
        iExists (add_vec_int pc 4),
                (legalize_sstatus_val ms0
                   (sstatus_write_set_val ms0 (mword_of_int 2))), m, n.
        iFrame "HPC HnPC Hresv".
        iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
        { rewrite /sconf_at_priv. iExists mdv0.
          iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
          iPureIntro. split; [exact Hmsf' | exact Hmm]. }
        iSplitL "Hstk Htr Hq1 Harest". { iFrame "Hstk Htr Hq1 Harest Hwit". }
        iFrame "Hf".
        iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
        iPureIntro. exists ms0. exact Hmsf.
      + (* the CSR read *)
        iIntros "Hrw Hro". rewrite read_CSR_sstatus_red.
        (* EVERY hand-written hart-indexed term takes the annotation here:
           after the rename there are two [CpuId]s in context and an
           unannotated [hreg_frame] resolves to the ENTRY hart's. *)
        iApply (swp_bind_use (CID := CID) _ _
                  (fun o : mword 64 => ⌜o = ms0⌝ ∗
                     hreg_frame (CID := CID)
                       (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                       (cw_Drw (R_bitvector_64 mstatus)) ∗
                     hreg_frame_ro (CID := CID) (cw_Df (DfracOwn 1))
                       (pw_rs Supervisor (R_bitvector_64 mstatus) ms0) cw_Dro)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_mono (CID := CID) with "[] [-]");
            [| iApply (swp_read_reg_pinned (CID := CID)
                         (cw_Drw (R_bitvector_64 mstatus))
                         cw_Dro (cw_Df (DfracOwn 1))
                         (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                         (R_bitvector_64 mstatus) (cw_disj _ Hfresh)
                         (cw_in_r _) with "Hcert Hrw Hro") ].
          iIntros (o) "(-> & Hrw & Hro)".
          rewrite (pw_rs_r Supervisor (R_bitvector_64 mstatus) ms0). by iFrame. }
        iIntros (o) "(-> & Hrw & Hro)". iApply (swp_ret (CID := CID)).
        by iFrame.
      + (* the CSR write *)
        iIntros "Hrw Hro".
        iApply (swp_write_CSR_sstatus_S (CID := CID) (DfracOwn 1) ms0 _
                  with "Hcert Hrw Hro").
      + (* the rd write, at x0: a no-op *)
        iIntros "Hf". iApply (swp_wX_zero (CID := CID) (mword_of_int 0) _ _
                                ltac:(by vm_compute) with "Hf").
    - (* ---- the continuation: the engine resumes on the hart [Hs] names ---- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & -> & %Hex)".
      iDestruct (sie_cap_gpr_at_close (CID := CID) with "Hcg'") as "Hcg'".
      destruct Hex as (ms & Hmsf).
      iSpecialize ("Hcont" $! CID with "[%]"); [exact Hs|].
      iApply ("Hcont" $! ms with "[%] Hcg' Hpc'"). exact Hmsf.
  Qed.

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
    iIntros (Hrs1 Hwval HWsie HWmxr0 HWfs0 HWvs0 HWxs0)
            "Hcg Hsppc Hpc Hinstr Hcont".
    assert (Hfresh : cw_fresh (R_bitvector_64 mstatus))
      by (split_and!; vm_compute; reflexivity).
    (* THE LEAF NAMES THE LANDING mstatus, which is exactly what the
       generalized obligation exists for: [sconf_at_priv ms'] goes back at
       the value the write installed, the continuation receives
       [sie_cap_gpr_at] at that same [ms'], and the three field facts ride
       the rider as pure side conditions. *)
    iApply (wp_instr_s_sconf m n false false pc false
              (CSRReg (csr_sstatus, Regidx rs1, zreg, CSRRW))
              (fun (_ : CpuId) npc ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗ ⌜m' = m⌝ ∗ ⌜n' = n⌝ ∗
                 ⌜_get_Mstatus_SIE  ms' = sie_bit false⌝ ∗
                 ⌜_get_Mstatus_SPP  ms' = _get_Sstatus_SPP  wval⌝ ∗
                 ⌜_get_Mstatus_SPIE ms' = _get_Sstatus_SPIE wval⌝ ∗
                 sret_bits (_get_Mstatus_SPP ms') (_get_Mstatus_SPIE ms'))%I
              with "Hcg Hpc Hinstr [Hsppc Hcont]").
    iNext. iApply wp_next_off_intro. rewrite /sconf_step_obl.
    iSplitL "Hsppc".
    - (* ---- the instruction ---- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct (sconf_to_cells with "Hsc") as (ms mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
          Hmdl & Hmenv)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
          %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0 mseccfg0.
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      iDestruct (sie_arm_half_agree false p ms with "Hhalf Harm") as %Hsie_ms.
      (* the four field equalities [flip_core] wants: the premises pin
         [wval]'s side to a constant, [sconf_ms_facts] pins [ms]'s side to
         the same one. *)
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
      destruct (flip_core ms wval (sie_bit false)
                  Hmsf HWsie HWmxr HWfs HWvs HWxs)
        as (Hf_sie & Hf_spp & Hf_spie & Hf_facts).
      (* the ghost half does not move: both indices are [sie_bit false] *)
      assert (Hhalf_eq : _get_Mstatus_SIE (legalize_sstatus_val ms wval)
                         = _get_Mstatus_SIE ms)
        by (rewrite Hf_sie Hsie_ms; reflexivity).
      iDestruct (pw_frames_in Supervisor (DfracOwn 1) (R_bitvector_64 mstatus)
                   ms Hfresh with "Hms Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      change (execute (CSRReg (csr_sstatus, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_sstatus (Regidx rs1) zreg CSRRW).
      (* the SPP tie MOVES here -- the only leaf in the tree where it does,
         and the only one holding both halves.  The update is a [bupd], and
         [HartSwp.swp_fupd_post] is what lets it happen in the swp's POST. *)
      iApply swp_fupd_post.
      iApply (swp_mono with
                "[Hstk Htr Harm Hhalf Hspp Hsppc Hmie Hmdl Hmenv HPC HnPC Hresv]
                 [Hrw Hro Hfile]");
        [| iApply (swp_execute_CSRReg_w_p (cw_Drw (R_bitvector_64 mstatus))
                     cw_Dro (cw_Df (DfracOwn 1))
                     (pw_rs Supervisor (R_bitvector_64 mstatus) ms)
                     (pw_rs Supervisor (R_bitvector_64 mstatus)
                        (legalize_sstatus_val ms wval))
                     (tp_pin m) csr_sstatus Supervisor rs1
                     (subrange_vec_dec
                        (lower_mstatus (legalize_sstatus_val ms wval))
                        (Z.sub xlen 1) 0)
                     (cw_disj _ Hfresh) (cw_in_priv _)
                     (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms Hfresh)
                     ltac:(by vm_compute)
                     (hval_check_CSR_result_S _ _ _ csr_sstatus CSRWrite
                        (cw_in_priv _) (cw_in_sec _) (cw_in_misa _)
                        (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms Hfresh)
                        (pw_rs_sec Supervisor (R_bitvector_64 mstatus) ms Hfresh)
                        (pw_rs_misa Supervisor (R_bitvector_64 mstatus) ms Hfresh)
                        ltac:(by vm_compute)
                        (exec_check_CSR_result_csrw_sstatus_S dstateS
                           ltac:(by vm_compute)))
                     ltac:(by vm_compute) ltac:(by vm_compute)
                     ltac:(by vm_compute)
                     with "Hcert Hfile Hrw Hro [Hcert]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (pw_frames_out Supervisor (DfracOwn 1) (R_bitvector_64 mstatus)
                     _ Hfresh with "[$Hrw $Hro]") as "(Hms & Hpriv & _ & _)".
        iMod (sret_bits_update (_get_Mstatus_SPP ms) (_get_Mstatus_SPIE ms)
                vspp vspie (_get_Mstatus_SPP (legalize_sstatus_val ms wval))
                (_get_Mstatus_SPIE (legalize_sstatus_val ms wval))
                with "Hspp Hsppc") as "[Hspp Hsppc]".
        iModIntro.
        iEval (rewrite -Hhalf_eq) in "Hhalf".
        iSplitR; [done|].
        iExists (add_vec_int pc 4), (legalize_sstatus_val ms wval), m, n.
        iFrame "HPC HnPC Hresv".
        iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
        { rewrite /sconf_at_priv. iExists mdv0.
          iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
          iPureIntro. split; [exact Hf_facts | exact Hmm]. }
        iSplitL "Hstk Htr Harm". { iFrame "Hstk Htr Harm Hwit". }
        iFrame "Hf".
        iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
        iSplitR; [iPureIntro; exact Hf_sie|].
        iSplitR; [iPureIntro; exact Hf_spp|].
        iSplitR; [iPureIntro; exact Hf_spie|].
        iExact "Hsppc".
      + iIntros "Hrw Hro".
        change (tp_pin m !!! Regidx rs1) with (rget m rs1). rewrite Hwval.
        iApply (swp_write_CSR_sstatus_S (DfracOwn 1) ms wval
                  with "Hcert Hrw Hro").
    - (* ---- the continuation: the wrapper delivers the mstatus-EXPOSING
           bundle at the very value the write installed, so this is a
           hand-through. ---- *)
      iIntros (npc ms' m' n')
        "Hcg' Hpc' (-> & -> & -> & %Hsie & %Hspp & %Hspie & Hsppc)".
      iSpecialize ("Hcont" $! cpu_id with "[%]"); [done|].
      iApply ("Hcont" $! ms' with "[%] [%] [%] Hcg' Hsppc Hpc'").
      { exact Hsie. }
      { exact Hspp. }
      { exact Hspie. }
  Qed.

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
    assert (Hfresh : cw_fresh (R_bitvector_64 mstatus))
      by (split_and!; vm_compute; reflexivity).
    iApply (wp_instr_s_sconf m n false false pc false
              (CSRReg (csr_satp, zreg, Regidx rd, CSRRS))
              (fun (_ : CpuId) npc ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗ ⌜n' = n⌝ ∗
                 ⌜∃ (sp0 : mword 64) (root : mword 44),
                    m' = <[Regidx rd := regval_into_reg sp0]> m /\
                    _get_Satp64_Mode (Mk_Satp64 sp0) = ('b"1000" : mword 4) /\
                    zero_extend' 16 (satp_to_asid (autocast (T := mword) sp0 : mword 64))
                      = (mword_of_int 0 : mword 16) /\
                    autocast (T := mword)
                      (satp_to_ppn (autocast (T := mword) sp0 : mword 64))
                      = root⌝)%I
              with "Hcg Hpc Hinstr [Hcont]").
    iNext. iApply wp_next_off_intro. rewrite /sconf_step_obl.
    iSplitR "Hcont".
    - (* ---- the instruction ---- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      (* THE BORROW, taken inside: the receipt pins the arm, the arm's
         [tlb_res_pt] lends the cell, and both closures are held until the
         bundle is rebuilt below.  The cell stays OUT of the read frame --
         it is read by [HartMFrame.swp_read_reg_cell], a one-cell node rule
         -- which is what keeps the frame the ordinary four-cell one. *)
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      iDestruct (strans_inv_acc_kpt with "Hkptr Htr") as (root) "(Htlb & Htrback)".
      iDestruct (tlb_res_pt_satp_acc with "Htlb")
        as (v) "(Hcell & %Hmode & %Hasid & %Hppn & Htlbback)".
      iDestruct (sconf_to_cells with "Hsc") as (ms0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hsie & Hsret & Hmie &
          Hmdl & Hmenv)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
          %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0 mseccfg0.
      pose proof Hmsf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HTVM).
      iDestruct (pr_frames_in Supervisor (DfracOwn 1) (DfracOwn 1)
                   (R_bitvector_64 mstatus) ms0 Hfresh
                   with "Hms Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      change (execute (CSRReg (csr_satp, zreg, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_satp zreg (Regidx rd) CSRRS).
      iApply (swp_mono with
                "[Hstk Harm Hsie Hsret Hmie Hmdl Hmenv Htrback Htlbback
                  HPC HnPC Hresv] [Hrw Hro Hfile Hcell]");
        [| iApply (swp_execute_CSRReg_r_gen_p ∅ (cr_Dro (R_bitvector_64 mstatus))
                     (cr_Df (DfracOwn 1) (DfracOwn 1) (R_bitvector_64 mstatus))
                     (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                     (tp_pin m) csr_satp Supervisor rd
                     (fun x => ⌜x = v⌝ ∗ (R_bitvector_64 satp) ↦ᵣ v)%I
                     (cr_disj _) (cr_in_priv _)
                     (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                     Hrd ltac:(by vm_compute)
                     (hval_check_CSR_result_satp_S
                        (∅ ∪ cr_Dro (R_bitvector_64 mstatus)) ∅
                        (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                        (cr_in_priv _) (cr_in_sec _) (cr_in_misa _) (cr_in_r _)
                        ltac:(rewrite (pw_rs_r Supervisor
                                         (R_bitvector_64 mstatus) ms0);
                              exact HTVM))
                     ltac:(by vm_compute) ltac:(by vm_compute)
                     ltac:(intro; by vm_compute)
                     with "Hcert Hfile Hrw Hro [Hcell]") ].
      + iIntros (e) "(-> & Hx)".
        iDestruct "Hx" as (x) "((-> & Hcelltmp) & Hf & Hrw & Hro)".
        iDestruct (pr_frames_out Supervisor (DfracOwn 1) (DfracOwn 1)
                     (R_bitvector_64 mstatus) ms0 Hfresh with "Hro")
          as "(Hms & Hpriv & _ & _)".
        (* GIVE THE CELL BACK, innermost closure first, and the bundle is
           whole again -- the borrow never leaves this proof. *)
        iSplitR; [done|].
        iExists (add_vec_int pc 4), ms0,
                (<[Regidx rd := regval_into_reg v]> m), n.
        iFrame "HPC HnPC Hresv".
        iSplitL "Hpriv Hms Hsie Hsret Hmie Hmdl Hmenv".
        { rewrite /sconf_at_priv. iExists mdv0.
          iFrame "Hhw Hminv Hpriv Hms Hsie Hsret Hmie Hmdl Hmenv".
          iPureIntro. split; [exact Hmsf | exact Hmm]. }
        assert (Hsp : m !!! Regidx csp_rs1
                      = <[Regidx rd := regval_into_reg v]> m !!! Regidx csp_rs1)
          by (symmetry; apply upd_ne; congruence).
        iSplitL "Hstk Harm Htlbback Htrback Hcelltmp".
        { iApply (sie_cap_retarget m (<[Regidx rd := regval_into_reg v]> m)
                    n false Hsp with "[Hstk Harm Htlbback Htrback Hcelltmp]").
          rewrite /sie_cap. iFrame "Hstk Harm Hwit".
          iApply "Htrback". iApply "Htlbback". iExact "Hcelltmp". }
        iSplitL "Hf".
        { iEval (rewrite (tp_pin_upd m rd (regval_into_reg v) Hrdtp)) in "Hf".
          iExact "Hf". }
        iSplitR; [done|]. iSplitR; [done|].
        iPureIntro. exists v, root. split_and!;
          [ reflexivity | exact Hmode | exact Hasid | exact Hppn ].
      + (* the satp read: the borrowed cell, at a one-cell node rule *)
        iIntros "Hrw Hro". rewrite read_CSR_satp_red.
        iApply (swp_mono with "[Hrw Hro] [Hcell]");
          [| iApply (swp_read_reg_cell (R_bitvector_64 satp) v
                       with "Hcert Hcell") ].
        iIntros (x) "[-> Hcell]". iFrame "Hrw Hro Hcell". done.
    - (* ---- the continuation ---- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & %Hex)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      destruct Hex as (sp0 & root & -> & Hmode & Hasid & Hppn).
      iSpecialize ("Hcont" $! cpu_id with "[%]"); [done|].
      iApply ("Hcont" $! sp0 root with "[%] [%] [%] Hcg' Hkptr Hpc'").
      { exact Hmode. }
      { exact Hasid. }
      { exact Hppn. }
  Qed.


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
    assert (Hfresh : cw_fresh (R_bitvector_64 mstatus))
      by (split_and!; vm_compute; reflexivity).
    assert (Himm2 : eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false)
      by (vm_compute; reflexivity).
    iDestruct "Hcsrs" as "(Hsepcx & Hscausex & Hstvalx & Hsppc & Hhx & Hkptr)".
    (* REFUTE THE ALREADY-ENABLED CASE ABOVE THE FUNNEL, NOT INSIDE IT.  The
       contradiction is between the payload's sepc cell and the '1' arm's, and
       a register cell is PER HART: held here, both are the entry hart's and
       cannot coexist; held inside the callback, the arm arrives at the
       REBOUND hart, where two sepc cells for two different harts are no
       contradiction at all.  That pays twice -- the surviving arm is
       [b = false], where [wp_next_off_intro] retires the hart question, and
       with it the rider's hart-indexing problem. *)
    destruct b.
    { iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      iDestruct "Harm" as "(Hq1 & Hhx' & Hkptr' & Hsepcx' & Hscausex' & Hstvalx' & Hsppc' & Hclmx' & Hcells')".
      iDestruct "Hsepcx" as (v1) "Hsepc1".
      iDestruct "Hsepcx'" as (v2) "Hsepc2".
      iDestruct (reg_pointsto_excl sepc v1 v2 with "Hsepc1 Hsepc2") as %[]. }
    (* THE ARM MOVES the other way: [false] in, [true] out. *)
    iApply (wp_instr_s_sconf m (trap_res true + n)%nat false true pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS))
              (fun (_ : CpuId) npc ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗ ⌜m' = m⌝ ∗
                 ⌜n' = (trap_res false + n)%nat⌝ ∗
                 ⌜∃ ms : mword 64, sconf_ms_facts ms⌝)%I
              with "Hcg Hpc Hinstr
                    [Htok Hhx Hkptr Hsepcx Hscausex Hstvalx Hsppc Hcells Hclm
                     Hcont]").
    iNext. iApply wp_next_off_intro. rewrite /sconf_step_obl.
    iSplitR "Hcont".
    - (* ---- the instruction, and the four-piece ghost flip ---- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct (sconf_to_cells with "Hsc") as (ms0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
          Hmdl & Hmenv)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
          %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0 mseccfg0.
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      destruct (csrsi_sie_flip ms0 Hmsf) as (Hsie' & Hspp' & Hspie' & Hmsf').
      (* the quarter comes straight out of the resource the caller handed in;
         this used to be an [inv_acc] on [intrN] whose body supplied it. *)
      iEval (rewrite /intr_res) in "Hhx".
      iDestruct "Hhx" as (handler vb) "(%Htvd & %Hsb & Hqi & Hstv & #Hspec)".
      iDestruct (pw_frames_in Supervisor (DfracOwn 1) (R_bitvector_64 mstatus)
                   ms0 Hfresh with "Hms Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      change (execute (CSRImm (csr_sstatus, mword_of_int 2,
                               Regidx (mword_of_int 0), CSRRS)))
        with (execute_CSRImm csr_sstatus (mword_of_int 2)
                (Regidx (mword_of_int 0)) CSRRS).
      iApply swp_fupd_post.
      iApply (swp_mono with
                "[Hstk Htr Harm Htok Hhalf Hspp Hqi Hstv Hkptr Hsepcx Hscausex
                  Hstvalx Hsppc Hclm Hcells Hmie Hmdl Hmenv HPC HnPC Hresv]
                 [Hrw Hro Hfile]");
        [| iApply (swp_execute_CSRImm_rw_p (cw_Drw (R_bitvector_64 mstatus))
                     cw_Dro (cw_Df (DfracOwn 1))
                     (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                     (pw_rs Supervisor (R_bitvector_64 mstatus)
                        (legalize_sstatus_val ms0
                           (sstatus_write_set_val ms0 (mword_of_int 2))))
                     (tp_pin m) (tp_pin m) csr_sstatus Supervisor
                     (mword_of_int 2) (mword_of_int 0) CSRRS
                     (sstatus_read ms0)
                     (sstatus_write_set_val ms0 (mword_of_int 2))
                     (subrange_vec_dec
                        (lower_mstatus (legalize_sstatus_val ms0
                           (sstatus_write_set_val ms0 (mword_of_int 2))))
                        (Z.sub xlen 1) 0)
                     (cw_disj _ Hfresh) (cw_in_priv _)
                     (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                     Himm2 ltac:(intros bb; reflexivity)
                     ltac:(by vm_compute)
                     (hval_check_CSR_result_S _ _ _ csr_sstatus CSRReadWrite
                        (cw_in_priv _) (cw_in_sec _) (cw_in_misa _)
                        (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        (pw_rs_sec Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        (pw_rs_misa Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        ltac:(by vm_compute)
                        (exec_check_CSR_result_sstatus_S dstateS
                           ltac:(by vm_compute)))
                     ltac:(by vm_compute) ltac:(by vm_compute)
                     eq_refl ltac:(by vm_compute)
                     with "Hcert Hfile Hrw Hro [] [] []") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (pw_frames_out Supervisor (DfracOwn 1) (R_bitvector_64 mstatus)
                     _ Hfresh with "[$Hrw $Hro]") as "(Hms & Hpriv & _ & _)".
        iMod (sie_ghost_flip_on _ _ _ _ _ with "Hhalf Harm Htok Hqi")
          as "(Hhalf & Hqcap & Hqcnt & Hqi)".
        iDestruct (intr_res_intro handler _ Htvd Hsb with "Hqi Hstv Hspec")
          as "Hintr".
        iEval (rewrite -Hsie') in "Hhalf".
        iDestruct (sret_tie_congr ms0 _ Hspp' Hspie' with "Hspp") as "Hspp".
        iModIntro.
        iSplitR; [done|].
        iExists (add_vec_int pc 4),
                (legalize_sstatus_val ms0
                   (sstatus_write_set_val ms0 (mword_of_int 2))), m,
                (trap_res false + n)%nat.
        iFrame "HPC HnPC Hresv".
        iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
        { rewrite /sconf_at_priv. iExists mdv0.
          iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
          iPureIntro. split; [exact Hmsf' | exact Hmm]. }
        (* the carve is IDENTICAL on both sides -- [trap_res false + (trap_res
           true + n)] going in, [trap_res true + (trap_res false + n)] coming
           out, both [kv_frame_slots + n] by conversion -- so [iExact] on the
           untouched [Hstk] closes it with no split and no arithmetic. *)
        iSplitL "Hqcap Hqcnt Hintr Hkptr Hsepcx Hscausex Hstvalx Hsppc Hclm
                 Hstk Htr Hcells".
        { iSplitL "Hstk". { iExact "Hstk". }
          iFrame "Htr Hwit".
          iFrame "Hqcap Hintr Hkptr Hsepcx Hscausex Hstvalx Hsppc Hclm".
          iSplitL "Hcells"; [ iExact "Hcells" | iExact "Hqcnt" ]. }
        iSplitL "Hf". { iExact "Hf". }
        iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
        iPureIntro. exists ms0. exact Hmsf.
      + (* the CSR read *)
        iIntros "Hrw Hro". rewrite read_CSR_sstatus_red.
        iApply (swp_bind_use _ _
                  (fun o : mword 64 => ⌜o = ms0⌝ ∗
                     hreg_frame (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                       (cw_Drw (R_bitvector_64 mstatus)) ∗
                     hreg_frame_ro (cw_Df (DfracOwn 1))
                       (pw_rs Supervisor (R_bitvector_64 mstatus) ms0) cw_Dro)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_mono with "[] [-]");
            [| iApply (swp_read_reg_pinned (cw_Drw (R_bitvector_64 mstatus))
                         cw_Dro (cw_Df (DfracOwn 1))
                         (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                         (R_bitvector_64 mstatus) (cw_disj _ Hfresh)
                         (cw_in_r _) with "Hcert Hrw Hro") ].
          iIntros (o) "(-> & Hrw & Hro)".
          rewrite (pw_rs_r Supervisor (R_bitvector_64 mstatus) ms0). by iFrame. }
        iIntros (o) "(-> & Hrw & Hro)". iApply swp_ret. by iFrame.
      + (* the CSR write *)
        iIntros "Hrw Hro".
        iApply (swp_write_CSR_sstatus_S (DfracOwn 1) ms0 _ with "Hcert Hrw Hro").
      + (* the rd write, at x0: a no-op *)
        iIntros "Hf". iApply (swp_wX_zero (mword_of_int 0) _ _
                                ltac:(by vm_compute) with "Hf").
    - (* ---- the continuation ---- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & -> & %Hex)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      destruct Hex as (ms & Hmsf).
      iDestruct (wp_next_here with "Hcont") as "Hcont".
      iApply ("Hcont" $! ms with "[%] Hcg' Hpc'"). exact Hmsf.
  Qed.

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
    assert (Hfresh : cw_fresh (R_bitvector_64 mstatus))
      by (split_and!; vm_compute; reflexivity).
    (* THE LEAF NAMES THE mstatus IT READ, which is what the generalized
       obligation exists for: [ms'] is the leaf's own choice, so the
       continuation's [sconf_at ms] and the [sstatus_read ms] that landed in
       rd are about the SAME word. *)
    iApply (wp_instr_s_sconf m n b b pc false
              (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS))
              (fun (_ : CpuId) npc ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗
                 ⌜m' = <[Regidx rd := regval_into_reg (sstatus_read ms')]> m⌝ ∗
                 ⌜n' = n⌝)%I
              with "Hcg Hpc Hinstr [Hcont]").
    iNext.
    (* FREE THE NAME [CID] FOR THE REBOUND HART: at [b = true] the read can be
       trapped and the thread resumed elsewhere, and every resource the
       continuation hands on is then about THAT hart. *)
    rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl.
    iSplitR "Hcont".
    - (* ---- the instruction ---- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct (sconf_to_cells (CID := CID) with "Hsc") as (ms0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
          Hmdl & Hmenv)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
          %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0 mseccfg0.
      assert (Hsp : m !!! Regidx csp_rs1
                    = <[Regidx rd := regval_into_reg (sstatus_read ms0)]> m
                        !!! Regidx csp_rs1)
        by (symmetry; apply upd_ne; congruence).
      iDestruct (pr_frames_in (CID := CID) Supervisor (DfracOwn 1) (DfracOwn 1)
                   (R_bitvector_64 mstatus) ms0 Hfresh
                   with "Hms Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      (* the model spells the x0 SOURCE as [Regidx (mword_of_int 0)]; the
         engine's is [zreg].  Same index, different literal -- so the bridge
         is [bv_eq], not [reflexivity] (the worklist's regidx-width trap). *)
      replace (Regidx (mword_of_int 0 : mword 5)) with zreg
        by (unfold zreg; f_equal; apply bv_eq; vm_compute; reflexivity).
      change (execute (CSRReg (csr_sstatus, zreg, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_sstatus zreg (Regidx rd) CSRRS).
      iApply (swp_mono (CID := CID) with
                "[Hcap Hmie Hmdl Hmenv Hhalf Hspp HPC HnPC Hresv]
                 [Hrw Hro Hfile]");
        [| iApply (swp_execute_CSRReg_r_p (CID := CID) ∅
                     (cr_Dro (R_bitvector_64 mstatus))
                     (cr_Df (DfracOwn 1) (DfracOwn 1) (R_bitvector_64 mstatus))
                     (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                     (tp_pin (CID := CID) m) csr_sstatus Supervisor rd
                     (sstatus_read ms0)
                     (cr_disj _) (cr_in_priv _)
                     (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                     Hrd ltac:(by vm_compute)
                     (hval_check_CSR_result_S _ _ _ csr_sstatus CSRRead
                        (cr_in_priv _) (cr_in_sec _) (cr_in_misa _)
                        (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        (pw_rs_sec Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        (pw_rs_misa Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        ltac:(by vm_compute)
                        (exec_check_CSR_result_csrr_sstatus_S dstateS
                           ltac:(by vm_compute)))
                     ltac:(by vm_compute) ltac:(by vm_compute)
                     ltac:(intro; by vm_compute)
                     with "Hcert Hfile Hrw Hro [Hcert]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (pr_frames_out (CID := CID) Supervisor (DfracOwn 1)
                     (DfracOwn 1) (R_bitvector_64 mstatus) ms0 Hfresh with "Hro")
          as "(Hms & Hpriv & _ & _)".
        iSplitR; [done|].
        iExists (add_vec_int pc 4), ms0,
                (<[Regidx rd := regval_into_reg (sstatus_read ms0)]> m), n.
        iFrame "HPC HnPC Hresv".
        iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
        { rewrite /sconf_at_priv. iExists mdv0.
          iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
          iPureIntro. split; [exact Hmsf | exact Hmm]. }
        iSplitL "Hcap".
        { iApply (sie_cap_retarget (CID := CID) m
                    (<[Regidx rd := regval_into_reg (sstatus_read ms0)]> m) n b
                    Hsp with "Hcap"). }
        iSplitL "Hf".
        { iEval (rewrite (tp_pin_upd (CID := CID) m rd
                            (regval_into_reg (sstatus_read ms0)) Hrdtp)) in "Hf".
          iExact "Hf". }
        iSplitR; [done|]. iSplitR; [done|]. done.
      + (* the sstatus read: the mstatus cell, pinned in the read frame *)
        iIntros "Hrw Hro". rewrite read_CSR_sstatus_red.
        iApply (swp_bind_use (CID := CID) _ _
                  (fun o : mword 64 => ⌜o = ms0⌝ ∗
                     hreg_frame (CID := CID)
                       (pw_rs Supervisor (R_bitvector_64 mstatus) ms0) ∅ ∗
                     hreg_frame_ro (CID := CID)
                       (cr_Df (DfracOwn 1) (DfracOwn 1) (R_bitvector_64 mstatus))
                       (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                       (cr_Dro (R_bitvector_64 mstatus)))%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_mono (CID := CID) with "[] [-]");
            [| iApply (swp_read_reg_pinned (CID := CID) ∅
                         (cr_Dro (R_bitvector_64 mstatus))
                         (cr_Df (DfracOwn 1) (DfracOwn 1)
                            (R_bitvector_64 mstatus))
                         (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                         (R_bitvector_64 mstatus) (cr_disj _)
                         (cr_in_r _) with "Hcert Hrw Hro") ].
          iIntros (o) "(-> & Hrw & Hro)".
          rewrite (pw_rs_r Supervisor (R_bitvector_64 mstatus) ms0). by iFrame. }
        iIntros (o) "(-> & Hrw & Hro)". iApply (swp_ret (CID := CID)).
        by iFrame.
    - (* ---- the continuation: the bundle arrives mstatus-EXPOSING at the
           very word the read returned, so the leaf's pieces come straight
           out of it. ---- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & ->)".
      iDestruct "Hcg'" as "(Hhs & Hscat & Hcap & Hfile)".
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      iDestruct "Hscat" as "[Hown Hcl]".
      iDestruct "Hown" as "(Hms & Hhalf & Htie & %Hmsf)".
      iDestruct (sie_arm_half_agree (CID := CID) b p ms' with "Hhalf Harm")
        as %Hb.
      iSpecialize ("Hcont" $! CID with "[%]"); [exact Hs|].
      iApply ("Hcont" $! ms' with "[%] Hhs [Hms Hhalf Htie Hcl] Htr Hpc' Hfile
                [Hstk Harm]").
      { exact Hmsf. }
      { rewrite /sconf_at. iSplitL "Hms Hhalf Htie".
        { rewrite /sconf_msown. iFrame "Hms Hhalf Htie". iPureIntro. exact Hmsf. }
        iExact "Hcl". }
      { iFrame "Hstk Harm Hwit". iPureIntro. exact Hb. }
  Qed.

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
    assert (Hfresh : cw_fresh (R_bitvector_64 mstatus))
      by (split_and!; vm_compute; reflexivity).
    assert (Himm2 : eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false)
      by (vm_compute; reflexivity).
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
    iClear "Hcnt".
    (* THE ARM MOVES ([true] in, [false] out) AND THE PAYLOAD IS HART-INDEXED,
       so the rider is taken at the callback's own hart -- both halves of the
       obligation's generalization are used here. *)
    iApply (wp_instr_s_sconf m n true false pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRC))
              (fun (CIDr : CpuId) npc ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗ ⌜m' = m⌝ ∗
                 ⌜n' = (trap_res true + n)%nat⌝ ∗
                 ⌜∃ ms : mword 64, sconf_ms_facts ms⌝ ∗
                 intr_count (CID := CIDr) 0 false ∗
                 trap_csrs (CID := CIDr) kt ∗ cpu_claim (CID := CIDr) p ∗
                 cpu_priv_pay (CID := CIDr) true p)%I
              with "Hcg Hpc Hinstr [Hcont]").
    iNext.
    rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl.
    iSplitR "Hcont".
    - (* ---- the instruction, and the four-piece ghost flip ---- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct (sconf_to_cells (CID := CID) with "Hsc") as (ms0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
          Hmdl & Hmenv)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
          %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0 mseccfg0.
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      (* the only reachable arm: interrupts were ON -- the flip is real, and
         both eighths are in the arm (its own, and the one inside
         [cpu_hart 0 true p]), which the callback delivers at the rebound
         hart. *)
      iDestruct "Harm" as "(Hq1 & Hhx & Hkptr & Hsepcx & Hscausex & Hstvalx &
                            Hsppc & Hclmx & (Hcells & Hc1))".
      iDestruct (intr_count_get_on 0 true with "Hq1 Hc1") as "(_ & Hq1 & Hcnt2)".
      destruct (csrci_sie_flip ms0 Hmsf) as (Hsie' & Hspp' & Hspie' & Hmsf').
      (* the handler resource: take the quarter out, flip, re-form.  This used
         to open [intrN] across the step and re-seal it. *)
      iEval (rewrite /intr_res) in "Hhx".
      iDestruct "Hhx" as (handler vb) "(%Htvd & %Hsb & Hqi & Hstv & #Hspec)".
      iDestruct (pw_frames_in (CID := CID) Supervisor (DfracOwn 1)
                   (R_bitvector_64 mstatus) ms0 Hfresh
                   with "Hms Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      change (execute (CSRImm (csr_sstatus, mword_of_int 2,
                               Regidx (mword_of_int 0), CSRRC)))
        with (execute_CSRImm csr_sstatus (mword_of_int 2)
                (Regidx (mword_of_int 0)) CSRRC).
      iApply (swp_fupd_post (CID := CID)).
      iApply (swp_mono (CID := CID) with
                "[Hstk Htr Hq1 Hhalf Hspp Hcnt2 Hqi Hstv Hkptr Hsepcx Hscausex
                  Hstvalx Hsppc Hclmx Hcells Hmie Hmdl Hmenv HPC HnPC Hresv]
                 [Hrw Hro Hfile]");
        [| iApply (swp_execute_CSRImm_rw_p (CID := CID)
                     (cw_Drw (R_bitvector_64 mstatus))
                     cw_Dro (cw_Df (DfracOwn 1))
                     (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                     (pw_rs Supervisor (R_bitvector_64 mstatus)
                        (legalize_sstatus_val ms0
                           (sstatus_write_val ms0 (mword_of_int 2))))
                     (tp_pin (CID := CID) m) (tp_pin (CID := CID) m)
                     csr_sstatus Supervisor
                     (mword_of_int 2) (mword_of_int 0) CSRRC
                     (sstatus_read ms0) (sstatus_write_val ms0 (mword_of_int 2))
                     (subrange_vec_dec
                        (lower_mstatus (legalize_sstatus_val ms0
                           (sstatus_write_val ms0 (mword_of_int 2))))
                        (Z.sub xlen 1) 0)
                     (cw_disj _ Hfresh) (cw_in_priv _)
                     (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                     Himm2 ltac:(intros bb; reflexivity)
                     ltac:(by vm_compute)
                     (hval_check_CSR_result_S _ _ _ csr_sstatus CSRReadWrite
                        (cw_in_priv _) (cw_in_sec _) (cw_in_misa _)
                        (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        (pw_rs_sec Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        (pw_rs_misa Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                        ltac:(by vm_compute)
                        (exec_check_CSR_result_sstatus_S dstateS
                           ltac:(by vm_compute)))
                     ltac:(by vm_compute) ltac:(by vm_compute)
                     eq_refl ltac:(by vm_compute)
                     with "Hcert Hfile Hrw Hro [] [] []") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (pw_frames_out (CID := CID) Supervisor (DfracOwn 1)
                     (R_bitvector_64 mstatus) _ Hfresh with "[$Hrw $Hro]")
          as "(Hms & Hpriv & _ & _)".
        iMod (sie_ghost_flip_off _ _ _ _ _ with "Hhalf Hq1 Hcnt2 Hqi")
          as "(Hhalf & Hq & Htok & Hqi)".
        iDestruct (intr_res_intro handler _ Htvd Hsb with "Hqi Hstv Hspec")
          as "Hintr".
        iEval (rewrite -Hsie') in "Hhalf".
        (* SPP and SPIE are untouched by an SIE flip, so the tie only needs
           re-expressing at the new mstatus -- no ghost movement. *)
        iDestruct (sret_tie_congr (CID := CID) ms0 _ Hspp' Hspie' with "Hspp")
          as "Hspp".
        iModIntro.
        iSplitR; [done|].
        iExists (add_vec_int pc 4),
                (legalize_sstatus_val ms0
                   (sstatus_write_val ms0 (mword_of_int 2))), m,
                (trap_res true + n)%nat.
        iFrame "HPC HnPC Hresv".
        iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
        { rewrite /sconf_at_priv. iExists mdv0.
          iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
          iPureIntro. split; [exact Hmsf' | exact Hmm]. }
        iSplitL "Hstk Htr Hq".
        { iSplitL "Hstk"; [iExact "Hstk"|].
          iFrame "Htr Hwit". iExact "Hq". }
        iSplitL "Hf". { iExact "Hf". }
        iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
        iSplitR. { iPureIntro. exists ms0. exact Hmsf. }
        iSplitL "Htok". { rewrite /intr_count /sie_bit. iExact "Htok". }
        iSplitL "Hsepcx Hscausex Hstvalx Hsppc Hintr Hkptr".
        { iFrame "Hsepcx Hscausex Hstvalx Hsppc Hintr Hkptr". }
        iSplitL "Hclmx". { iExact "Hclmx". }
        rewrite /cpu_priv_pay. iExact "Hcells".
      + (* the CSR read *)
        iIntros "Hrw Hro". rewrite read_CSR_sstatus_red.
        iApply (swp_bind_use (CID := CID) _ _
                  (fun o : mword 64 => ⌜o = ms0⌝ ∗
                     hreg_frame (CID := CID)
                       (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                       (cw_Drw (R_bitvector_64 mstatus)) ∗
                     hreg_frame_ro (CID := CID) (cw_Df (DfracOwn 1))
                       (pw_rs Supervisor (R_bitvector_64 mstatus) ms0) cw_Dro)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_mono (CID := CID) with "[] [-]");
            [| iApply (swp_read_reg_pinned (CID := CID)
                         (cw_Drw (R_bitvector_64 mstatus))
                         cw_Dro (cw_Df (DfracOwn 1))
                         (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                         (R_bitvector_64 mstatus) (cw_disj _ Hfresh)
                         (cw_in_r _) with "Hcert Hrw Hro") ].
          iIntros (o) "(-> & Hrw & Hro)".
          rewrite (pw_rs_r Supervisor (R_bitvector_64 mstatus) ms0). by iFrame. }
        iIntros (o) "(-> & Hrw & Hro)". iApply (swp_ret (CID := CID)).
        by iFrame.
      + (* the CSR write *)
        iIntros "Hrw Hro".
        iApply (swp_write_CSR_sstatus_S (CID := CID) (DfracOwn 1) ms0 _
                  with "Hcert Hrw Hro").
      + (* the rd write, at x0: a no-op *)
        iIntros "Hf". iApply (swp_wX_zero (CID := CID) (mword_of_int 0) _ _
                                ltac:(by vm_compute) with "Hf").
    - (* ---- the continuation ---- *)
      iIntros (npc ms' m' n')
        "Hcg' Hpc' (-> & -> & -> & %Hex & Hcnt & Htr & Hclm & Hcells)".
      iDestruct (sie_cap_gpr_at_close (CID := CID) with "Hcg'") as "Hcg'".
      destruct Hex as (ms & Hmsf).
      iSpecialize ("Hcont" $! CID with "[%]"); [exact Hs|].
      iApply ("Hcont" $! ms with "[%] Hcg' Hcnt Htr Hclm Hcells Hpc'").
      exact Hmsf.
  Qed.

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
    assert (Hfresh : cw_fresh (R_bitvector_64 mstatus))
      by (split_and!; vm_compute; reflexivity).
    assert (Himm2 : eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false)
      by (vm_compute; reflexivity).
    destruct b.
    - (* ================= b = true: the REAL flip ================= *)
      iDestruct (intr_count_pre_on with "Hcnt") as %Hke.
      destruct Hke as [-> ->].
      iApply (wp_instr_s_sconf m n true false pc false
                (CSRImm (csr_sstatus, mword_of_int 2, Regidx rd, CSRRC))
                (fun (CIDr : CpuId) npc ms' m' n' =>
                   ⌜npc = add_vec_int pc 4⌝ ∗
                   ⌜n' = (trap_res true + n)%nat⌝ ∗
                   (∃ ms : mword 64,
                      ⌜m' = <[Regidx rd := regval_into_reg (sstatus_read ms)]> m⌝ ∗
                      ⌜sconf_ms_facts ms⌝ ∗
                      ⌜0%nat = 0%nat -> _get_Mstatus_SIE ms = sie_bit true⌝) ∗
                   intr_count (CID := CIDr) 1 true ∗
                   trap_csrs_pay (CID := CIDr) kt 0 true ∗
                   cpu_claim_pay (CID := CIDr) 0 true p ∗
                   cpu_priv_pay (CID := CIDr) true p)%I
                with "Hcg Hpc Hinstr [Hcont]").
      iNext.
      rename CID into CID0.
      iIntros (CID Hs). rewrite /sconf_step_obl.
      iSplitR "Hcont".
      + iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
        iDestruct (sconf_to_cells (CID := CID) with "Hsc") as (ms0 mdv0)
          "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
            Hmdl & Hmenv)".
        iDestruct (hw_config_cert with "Hhw") as "#Hcert".
        iPoseProof "Hhw" as "#Hhwc".
        iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
          "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
            %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
            %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
        subst misa0 mseccfg0.
        assert (Hsp : m !!! Regidx csp_rs1
                      = <[Regidx rd := regval_into_reg (sstatus_read ms0)]> m
                          !!! Regidx csp_rs1)
          by (symmetry; apply upd_ne; congruence).
        iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
        iDestruct "Harm" as "(Hq1 & Hhx & Hkptr & Hsepcx & Hscausex & Hstvalx &
                              Hsppc & Hclmx & (Hcells & Hc1))".
        iDestruct (ghost_var_agree with "Hhalf Hq1") as %Hb1.
        iDestruct (intr_count_get_on 0 true with "Hq1 Hc1") as "(_ & Hq1 & Hcnt2)".
        destruct (csrci_sie_flip ms0 Hmsf) as (Hsie' & Hspp' & Hspie' & Hmsf').
        iEval (rewrite /intr_res) in "Hhx".
        iDestruct "Hhx" as (handler vb) "(%Htvd & %Hsb & Hqi & Hstv & #Hspec)".
        iDestruct (pw_frames_in (CID := CID) Supervisor (DfracOwn 1)
                     (R_bitvector_64 mstatus) ms0 Hfresh
                     with "Hms Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
        change (execute (CSRImm (csr_sstatus, mword_of_int 2,
                                 Regidx rd, CSRRC)))
          with (execute_CSRImm csr_sstatus (mword_of_int 2) (Regidx rd) CSRRC).
        iApply (swp_fupd_post (CID := CID)).
        iApply (swp_mono (CID := CID) with
                  "[Hstk Htr Hq1 Hhalf Hspp Hcnt2 Hqi Hstv Hkptr Hsepcx Hscausex
                    Hstvalx Hsppc Hclmx Hcells Hmie Hmdl Hmenv HPC HnPC Hresv]
                   [Hrw Hro Hfile]");
          [| iApply (swp_execute_CSRImm_rw_p (CID := CID)
                       (cw_Drw (R_bitvector_64 mstatus))
                       cw_Dro (cw_Df (DfracOwn 1))
                       (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                       (pw_rs Supervisor (R_bitvector_64 mstatus)
                          (legalize_sstatus_val ms0
                             (sstatus_write_val ms0 (mword_of_int 2))))
                       (tp_pin (CID := CID) m)
                       (<[Regidx rd := regval_into_reg (sstatus_read ms0)]>
                          (tp_pin (CID := CID) m))
                       csr_sstatus Supervisor
                       (mword_of_int 2) rd CSRRC
                       (sstatus_read ms0) (sstatus_write_val ms0 (mword_of_int 2))
                       (subrange_vec_dec
                          (lower_mstatus (legalize_sstatus_val ms0
                             (sstatus_write_val ms0 (mword_of_int 2))))
                          (Z.sub xlen 1) 0)
                       (cw_disj _ Hfresh) (cw_in_priv _)
                       (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                       Himm2 ltac:(intros bb; reflexivity)
                       ltac:(by vm_compute)
                       (hval_check_CSR_result_S _ _ _ csr_sstatus CSRReadWrite
                          (cw_in_priv _) (cw_in_sec _) (cw_in_misa _)
                          (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                          (pw_rs_sec Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                          (pw_rs_misa Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                          ltac:(by vm_compute)
                          (exec_check_CSR_result_sstatus_S dstateS
                             ltac:(by vm_compute)))
                       ltac:(by vm_compute) ltac:(by vm_compute)
                       eq_refl ltac:(by vm_compute)
                       with "Hcert Hfile Hrw Hro [] [] []") ].
        * iIntros (e) "(-> & Hf & Hrw & Hro)".
          iDestruct (pw_frames_out (CID := CID) Supervisor (DfracOwn 1)
                       (R_bitvector_64 mstatus) _ Hfresh with "[$Hrw $Hro]")
            as "(Hms & Hpriv & _ & _)".
          iMod (sie_ghost_flip_off _ _ _ _ _ with "Hhalf Hq1 Hcnt2 Hqi")
            as "(Hhalf & Hq & Htok & Hqi)".
          iDestruct (intr_res_intro handler _ Htvd Hsb with "Hqi Hstv Hspec")
            as "Hintr".
          iEval (rewrite -Hsie') in "Hhalf".
          iDestruct (sret_tie_congr (CID := CID) ms0 _ Hspp' Hspie' with "Hspp")
            as "Hspp".
          iModIntro.
          iSplitR; [done|].
          iExists (add_vec_int pc 4),
                  (legalize_sstatus_val ms0
                     (sstatus_write_val ms0 (mword_of_int 2))),
                  (<[Regidx rd := regval_into_reg (sstatus_read ms0)]> m),
                  (trap_res true + n)%nat.
          iFrame "HPC HnPC Hresv".
          iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
          { rewrite /sconf_at_priv. iExists mdv0.
            iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
            iPureIntro. split; [exact Hmsf' | exact Hmm]. }
          iSplitL "Hstk Htr Hq".
          { iSplitL "Hstk". { rewrite -Hsp. iExact "Hstk". }
            iFrame "Htr Hwit". iExact "Hq". }
          iSplitL "Hf".
          { iEval (rewrite (tp_pin_upd (CID := CID) m rd
                              (regval_into_reg (sstatus_read ms0)) Hrdtp)) in "Hf".
            iExact "Hf". }
          iSplitR; [done|]. iSplitR; [done|].
          iSplitR.
          { iPureIntro. exists ms0. split_and!;
              [ reflexivity | exact Hmsf | intros _; cbn [sie_bit]; exact Hb1 ]. }
          iSplitL "Htok". { iApply (intr_count_pack_S_on with "Htok"). }
          iSplitL "Hsepcx Hscausex Hstvalx Hsppc Hintr Hkptr".
          { iFrame "Hsepcx Hscausex Hstvalx Hsppc Hintr Hkptr". }
          iSplitL "Hclmx". { rewrite /cpu_claim_pay. iExact "Hclmx". }
          rewrite /cpu_priv_pay. iExact "Hcells".
        * iIntros "Hrw Hro". rewrite read_CSR_sstatus_red.
          iApply (swp_bind_use (CID := CID) _ _
                    (fun o : mword 64 => ⌜o = ms0⌝ ∗
                       hreg_frame (CID := CID)
                         (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                         (cw_Drw (R_bitvector_64 mstatus)) ∗
                       hreg_frame_ro (CID := CID) (cw_Df (DfracOwn 1))
                         (pw_rs Supervisor (R_bitvector_64 mstatus) ms0) cw_Dro)%I
                    _ with "[Hrw Hro] [-]").
          { iApply (swp_mono (CID := CID) with "[] [-]");
              [| iApply (swp_read_reg_pinned (CID := CID)
                           (cw_Drw (R_bitvector_64 mstatus))
                           cw_Dro (cw_Df (DfracOwn 1))
                           (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                           (R_bitvector_64 mstatus) (cw_disj _ Hfresh)
                           (cw_in_r _) with "Hcert Hrw Hro") ].
            iIntros (o) "(-> & Hrw & Hro)".
            rewrite (pw_rs_r Supervisor (R_bitvector_64 mstatus) ms0). by iFrame. }
          iIntros (o) "(-> & Hrw & Hro)". iApply (swp_ret (CID := CID)).
          by iFrame.
        * iIntros "Hrw Hro".
          iApply (swp_write_CSR_sstatus_S (CID := CID) (DfracOwn 1) ms0 _
                    with "Hcert Hrw Hro").
        * iIntros "Hf".
          iApply (swp_wX_file (CID := CID) rd (tp_pin (CID := CID) m)
                    (sstatus_read ms0) Hrd with "Hcert Hf").
      + iIntros (npc ms' m' n')
          "Hcg' Hpc' (-> & -> & %Hex & Hcnt & Htr & Hclm & Hcells)".
        iDestruct (sie_cap_gpr_at_close (CID := CID) with "Hcg'") as "Hcg'".
        destruct Hex as (ms & -> & Hmsf & Hsie).
        iSpecialize ("Hcont" $! CID with "[%]"); [exact Hs|].
        iApply ("Hcont" $! ms with "[%] [%] Hcg' Hcnt Htr Hclm Hcells Hpc'");
          [ exact Hmsf | exact Hsie ].
    - (* ================= b = false: the IDEMPOTENT write ================= *)
      iDestruct (intr_count_pre_off with "Hcnt") as "Hcnt".
      iApply (wp_instr_s_sconf m n false false pc false
                (CSRImm (csr_sstatus, mword_of_int 2, Regidx rd, CSRRC))
                (fun (CIDr : CpuId) npc ms' m' n' =>
                   ⌜npc = add_vec_int pc 4⌝ ∗
                   ⌜n' = (trap_res false + n)%nat⌝ ∗
                   (∃ ms : mword 64,
                      ⌜m' = <[Regidx rd := regval_into_reg (sstatus_read ms)]> m⌝ ∗
                      ⌜sconf_ms_facts ms⌝ ∗
                      ⌜k = 0%nat -> _get_Mstatus_SIE ms = sie_bit eb⌝) ∗
                   intr_count (CID := CIDr) (S k) eb ∗
                   trap_csrs_pay (CID := CIDr) kt k eb ∗
                   cpu_claim_pay (CID := CIDr) k eb p ∗
                   cpu_priv_pay (CID := CIDr) false p)%I
                with "Hcg Hpc Hinstr [Hcnt Hcont]").
      iNext. iApply wp_next_off_intro. rewrite /sconf_step_obl.
      iSplitR "Hcont".
      + iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
        iDestruct (sconf_to_cells with "Hsc") as (ms0 mdv0)
          "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
            Hmdl & Hmenv)".
        iDestruct (hw_config_cert with "Hhw") as "#Hcert".
        iPoseProof "Hhw" as "#Hhwc".
        iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
          "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
            %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
            %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
        subst misa0 mseccfg0.
        assert (Hsp : m !!! Regidx csp_rs1
                      = <[Regidx rd := regval_into_reg (sstatus_read ms0)]> m
                          !!! Regidx csp_rs1)
          by (symmetry; apply upd_ne; congruence).
        iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
        iDestruct (ghost_var_agree with "Hhalf Harm") as %Hb0.
        destruct (csrci_sie_flip ms0 Hmsf) as (Hsie' & Hspp' & Hspie' & Hmsf').
        iDestruct (intr_count_push_off k eb with "Harm Hcnt")
          as "(%Heb0 & Harm & Hcnt)".
        iDestruct (pw_frames_in Supervisor (DfracOwn 1)
                     (R_bitvector_64 mstatus) ms0 Hfresh
                     with "Hms Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
        change (execute (CSRImm (csr_sstatus, mword_of_int 2,
                                 Regidx rd, CSRRC)))
          with (execute_CSRImm csr_sstatus (mword_of_int 2) (Regidx rd) CSRRC).
        iApply (swp_mono with
                  "[Hstk Htr Harm Hcnt Hhalf Hspp Hmie Hmdl Hmenv HPC HnPC Hresv]
                   [Hrw Hro Hfile]");
          [| iApply (swp_execute_CSRImm_rw_p
                       (cw_Drw (R_bitvector_64 mstatus))
                       cw_Dro (cw_Df (DfracOwn 1))
                       (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                       (pw_rs Supervisor (R_bitvector_64 mstatus)
                          (legalize_sstatus_val ms0
                             (sstatus_write_val ms0 (mword_of_int 2))))
                       (tp_pin m)
                       (<[Regidx rd := regval_into_reg (sstatus_read ms0)]>
                          (tp_pin m))
                       csr_sstatus Supervisor
                       (mword_of_int 2) rd CSRRC
                       (sstatus_read ms0) (sstatus_write_val ms0 (mword_of_int 2))
                       (subrange_vec_dec
                          (lower_mstatus (legalize_sstatus_val ms0
                             (sstatus_write_val ms0 (mword_of_int 2))))
                          (Z.sub xlen 1) 0)
                       (cw_disj _ Hfresh) (cw_in_priv _)
                       (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                       Himm2 ltac:(intros bb; reflexivity)
                       ltac:(by vm_compute)
                       (hval_check_CSR_result_S _ _ _ csr_sstatus CSRReadWrite
                          (cw_in_priv _) (cw_in_sec _) (cw_in_misa _)
                          (pw_rs_priv Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                          (pw_rs_sec Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                          (pw_rs_misa Supervisor (R_bitvector_64 mstatus) ms0 Hfresh)
                          ltac:(by vm_compute)
                          (exec_check_CSR_result_sstatus_S dstateS
                             ltac:(by vm_compute)))
                       ltac:(by vm_compute) ltac:(by vm_compute)
                       eq_refl ltac:(by vm_compute)
                       with "Hcert Hfile Hrw Hro [] [] []") ].
        * iIntros (e) "(-> & Hf & Hrw & Hro)".
          iDestruct (pw_frames_out Supervisor (DfracOwn 1)
                       (R_bitvector_64 mstatus) _ Hfresh with "[$Hrw $Hro]")
            as "(Hms & Hpriv & _ & _)".
          iEval (rewrite Hb0) in "Hhalf". iEval (rewrite -Hsie') in "Hhalf".
          iDestruct (sret_tie_congr ms0 _ Hspp' Hspie' with "Hspp") as "Hspp".
          iSplitR; [done|].
          iExists (add_vec_int pc 4),
                  (legalize_sstatus_val ms0
                     (sstatus_write_val ms0 (mword_of_int 2))),
                  (<[Regidx rd := regval_into_reg (sstatus_read ms0)]> m),
                  (trap_res false + n)%nat.
          iFrame "HPC HnPC Hresv".
          iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
          { rewrite /sconf_at_priv. iExists mdv0.
            iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
            iPureIntro. split; [exact Hmsf' | exact Hmm]. }
          iSplitL "Hstk Htr Harm".
          { iSplitL "Hstk". { rewrite -Hsp. iExact "Hstk". }
            iFrame "Htr Hwit". iExact "Harm". }
          iSplitL "Hf".
          { iEval (rewrite (tp_pin_upd m rd
                              (regval_into_reg (sstatus_read ms0)) Hrdtp)) in "Hf".
            iExact "Hf". }
          iSplitR; [done|]. iSplitR; [done|].
          iSplitR.
          { iPureIntro. exists ms0. split_and!;
              [ reflexivity | exact Hmsf
              | intros Hk; rewrite (Heb0 Hk); cbn [sie_bit]; exact Hb0 ]. }
          iSplitL "Hcnt". { iExact "Hcnt". }
          iSplitR. { destruct k; [rewrite (Heb0 eq_refl) |]; done. }
          iSplitR. { rewrite /cpu_claim_pay.
                     destruct k; [rewrite (Heb0 eq_refl) |]; done. }
          rewrite /cpu_priv_pay. done.
        * iIntros "Hrw Hro". rewrite read_CSR_sstatus_red.
          iApply (swp_bind_use _ _
                    (fun o : mword 64 => ⌜o = ms0⌝ ∗
                       hreg_frame (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                         (cw_Drw (R_bitvector_64 mstatus)) ∗
                       hreg_frame_ro (cw_Df (DfracOwn 1))
                         (pw_rs Supervisor (R_bitvector_64 mstatus) ms0) cw_Dro)%I
                    _ with "[Hrw Hro] [-]").
          { iApply (swp_mono with "[] [-]");
              [| iApply (swp_read_reg_pinned
                           (cw_Drw (R_bitvector_64 mstatus))
                           cw_Dro (cw_Df (DfracOwn 1))
                           (pw_rs Supervisor (R_bitvector_64 mstatus) ms0)
                           (R_bitvector_64 mstatus) (cw_disj _ Hfresh)
                           (cw_in_r _) with "Hcert Hrw Hro") ].
            iIntros (o) "(-> & Hrw & Hro)".
            rewrite (pw_rs_r Supervisor (R_bitvector_64 mstatus) ms0). by iFrame. }
          iIntros (o) "(-> & Hrw & Hro)". iApply swp_ret. by iFrame.
        * iIntros "Hrw Hro".
          iApply (swp_write_CSR_sstatus_S (DfracOwn 1) ms0 _
                    with "Hcert Hrw Hro").
        * iIntros "Hf".
          iApply (swp_wX_file rd (tp_pin m) (sstatus_read ms0) Hrd
                    with "Hcert Hf").
      + iIntros (npc ms' m' n')
          "Hcg' Hpc' (-> & -> & %Hex & Hcnt & Htr & Hclm & Hcells)".
        iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
        destruct Hex as (ms & -> & Hmsf & Hsie).
        iSpecialize ("Hcont" $! cpu_id with "[%]"); [done|].
        iApply ("Hcont" $! ms with "[%] [%] Hcg' Hcnt Htr Hclm Hcells Hpc'");
          [ exact Hmsf | exact Hsie ].
  Qed.




End WpSconfCsr.
