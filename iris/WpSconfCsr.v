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
Require Import MinstretInv InstrBytes WpGpr ExecCommon WpGprCsrwCommon WpGprCsrwB.
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
Definition cpu_cells_pay `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId}
    (b : bool) (p : mword 64) : iProp Σ :=
  (if b then cpu_cells 0 true p else emp)%I.

Lemma cpu_cells_pay_on `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (px : mword 64) :
  cpu_cells_pay true px ⊣⊢ cpu_cells 0 true px.
Proof. reflexivity. Qed.

Lemma cpu_cells_pay_off `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (px : mword 64) :
  cpu_cells_pay false px ⊣⊢ (emp : iProp Σ).
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
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  Lemma wp_csrr_sstatus_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr m n b p -∗
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
      ( stack_own (<[Regidx rd := regval_into_reg (sstatus_read ms)]> m
                     !!! Regidx csp_rs1) (kv_frame_slots + n) ∗
        ⌜ _get_Mstatus_SIE ms = sie_bit b ⌝ ∗
        sie_arm b p ) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdok) "Hcg Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    iApply (wp_instr_s_sconf m n b Φ pc false
              (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
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
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iAssert ( ghost_var sie_gname (1/2) (_get_Mstatus_SIE ms0) ∗
              ( stack_own (<[Regidx rd := regval_into_reg (sstatus_read ms0)]> m
                             !!! Regidx csp_rs1) (kv_frame_slots + n) ∗
                ⌜ _get_Mstatus_SIE ms0 = sie_bit b ⌝ ∗
                sie_arm b p ) )%I
      with "[Hstk Harm Hhalf]" as "[Hhalf Hpair]".
    { destruct b.
      - iDestruct "Harm" as "(Hq1 & Hhx & Hsepcx & Hscausex & Hstvalx & Hsppc & Hcpu)".
        iDestruct (ghost_var_agree with "Hhalf Hq1") as %Hb.
        iFrame "Hhalf". iSplitL "Hstk". { rewrite Hsp. iExact "Hstk". }
        iSplitR. { iPureIntro. exact Hb. }
        iFrame "Hq1 Hhx Hsepcx Hscausex Hstvalx Hsppc Hcpu".
      - iDestruct "Harm" as "Hq0".
        iDestruct (ghost_var_agree with "Hhalf Hq0") as %Hb.
        iFrame "Hhalf". iSplitL "Hstk". { rewrite Hsp. iExact "Hstk". }
        iSplitR. { iPureIntro. exact Hb. }
        iExact "Hq0". }
    iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
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
  (* ms' by reg_update, opens intrN (closed at callback time in BOTH      *)
  (* arms; lockN-style disjointness from minstretN), [sie_ghost_flip]s    *)
  (* ALL THREE pieces to '0' (bundle half + capability quarter +          *)
  (* invariant quarter), reseals the invariant at b := '0' (the handler   *)
  (* guard is vacuous), and hands the caller the freed '1'-arm payload    *)
  (* (trap CSRs + stack bound + a persistent intr_inv copy).  The '0'     *)
  (* arm is the idempotent write, ghosts untouched.                       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_csrci_sstatus_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (k : nat) (eb : bool)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr m n b p -∗
    intr_count_pre b k eb -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx rd, CSRRC)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      ⌜ k = 0%nat -> _get_Mstatus_SIE ms = sie_bit eb ⌝ -∗
      sie_cap_gpr (<[Regidx rd := regval_into_reg (sstatus_read ms)]> m) n false p -∗
      intr_count (S k) eb -∗
      trap_csrs_pay k eb -∗
      cpu_cells_pay b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdok) "Hcg Hcnt Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    iApply (wp_instr_s_sconf m n b Φ pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx rd, CSRRC))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
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
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    destruct b.
    - (* ---- b = true: the real flip.  The caller holds NEITHER eighth here
           (both are in the arm); what it hands over is the pure fact, and
           the arm itself is dismantled for the rest. ---- *)
      iDestruct (intr_count_pre_on with "Hcnt") as %Hke.
      destruct Hke as [-> ->].
      iDestruct "Harm" as "(Hq1 & Hhx & Hsepcx & Hscausex & Hstvalx & Hsppc & (Hcells & Hc1))".
      iDestruct (ghost_var_agree with "Hhalf Hq1") as %Hb1.
      iDestruct (intr_count_get_on 0 true with "Hq1 Hc1") as "(_ & Hq1 & Hc1)".
      destruct (csrci_sie_flip ms0 Hmsf) as (Hsie' & Hspp' & Hspie' & Hmsf').
      set (ms1 := legalize_sstatus_val ms0 (sstatus_write_val ms0 (mword_of_int 2))).
      (* the trap-vector invariant: open it for the quarter, flip, reseal *)
      iDestruct "Hhx" as (handler) "#Hintr".
      iDestruct "Hintr" as "(%Htvd & %Hsb & #Hinv_i)".
      iMod (inv_acc (⊤ ∖ ↑minstretN) intrN with "Hinv_i") as "[Hbody Hclose]";
        [solve_ndisj|].
      iDestruct "Hbody" as (bq) "(>Hqi & >Hstv & #Hguard)".
      iDestruct (ghost_var_agree with "Hq1 Hqi") as %Hbq.
      iAssert (▷ intr_handler_spec handler)%I as "#Hspec".
      { iNext. iApply "Hguard". iPureIntro. symmetry. exact Hbq. }
      iMod (sie_ghost_flip_off _ _ _ _ _ with "Hhalf Hq1 Hc1 Hqi") as "(Hhalf & Hq & Htok & Hqi)".
      iMod ("Hclose" with "[Hqi Hstv]") as "_".
      { iNext. iExists ('b"0" : mword 1). iFrame "Hqi Hstv".
        iModIntro. iIntros "%Hb".
        exfalso. apply (f_equal (@bv_unsigned _)) in Hb.
        vm_compute in Hb. discriminate. }
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
      iAssert (sie_cap (<[Regidx rd := regval_into_reg (sstatus_read ms0)]> m) n false p)
        with "[Hstk Htr Hq]" as "Hcap".
      { iSplitL "Hstk". { rewrite Hsp. iExact "Hstk". }
        iFrame "Htr". iExact "Hq". }
      iAssert (sconf) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenvx]" as "Hsc".
      { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
        iExists ms1. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf'. }
      iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
      iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
      iApply ("Hcont" $! ms0 with "[%] [%] Hcg
                            [Htok] [Hsepcx Hscausex Hstvalx Hsppc] [Hcells] [$Hpc' $Hnpc]").
      { exact Hmsf. }
      { intros _. cbn [sie_bit]. exact Hb1. }
      { iApply (intr_count_pack_S_on with "Htok").
        iExists handler. iSplit; [| iExact "Hspec"].
        iSplit; [iPureIntro; exact Htvd |].
        iSplit; [iPureIntro; exact Hsb |]. iExact "Hinv_i". }
      { iFrame "Hsepcx Hscausex Hstvalx Hsppc". }
      { rewrite /cpu_cells_pay. iExact "Hcells". }
    - (* ---- b = false: the idempotent write; ghosts untouched ---- *)
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
      iAssert (sie_cap (<[Regidx rd := regval_into_reg (sstatus_read ms0)]> m) n false p)
        with "[Hstk Htr Hq0]" as "Hcap".
      { iSplitL "Hstk". { rewrite Hsp. iExact "Hstk". }
        iFrame "Htr". iExact "Hq0". }
      iAssert (sconf) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenvx]" as "Hsc".
      { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
        iExists ms0. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
      iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
      iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
      iApply ("Hcont" $! ms0 with "[%] [%] Hcg Hcnt [] [] [$Hpc' $Hnpc]").
      { exact Hmsf. }
      { intros Hk. rewrite (Heb0 Hk). cbn [sie_bit]. exact Hb0. }
      { destruct k; [rewrite (Heb0 eq_refl) |]; done. }
      { rewrite /cpu_cells_pay. done. }
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
  Lemma wp_csrsi_sstatus_x0_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    sie_cap_gpr m n b p -∗
    intr_count 1 true -∗
    trap_csrs -∗
    cpu_cells 0 true p -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      sie_cap_gpr m n true p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "Hcg Hcnt Hcsrs Hcells Hpc Hinstr Hcont".
    iDestruct "Hcnt" as "[Htok Hhx]".
    iDestruct "Hcsrs" as "(Hsepcx & Hscausex & Hstvalx & Hsppc)".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
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
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    destruct b.
    - (* ---- b = true: already enabled -- impossible.  The payload's sepc
           cell and the '1' arm's sepc cell cannot coexist. ---- *)
      iDestruct "Harm" as "(Hq1 & Hhx' & Hsepcx' & Hscausex' & Hstvalx' & Hcells')".
      iDestruct "Hsepcx" as (v1) "Hsepc1".
      iDestruct "Hsepcx'" as (v2) "Hsepc2".
      iDestruct (reg_pointsto_excl sepc v1 v2 with "Hsepc1 Hsepc2") as %[].
    - (* ---- b = false: the real restore ---- *)
      destruct (csrsi_sie_flip ms0 Hmsf) as (Hsie' & Hspp' & Hspie' & Hmsf').
      set (ms1 := legalize_sstatus_val ms0 (sstatus_write_set_val ms0 (mword_of_int 2))).
      iDestruct "Hhx" as (handler) "[#Hintr #Hspec]".
      iDestruct "Hintr" as "(%Htvd & %Hsb & #Hinv_i)".
      iMod (inv_acc (⊤ ∖ ↑minstretN) intrN with "Hinv_i") as "[Hbody Hclose]";
        [solve_ndisj|].
      iDestruct "Hbody" as (bq) "(>Hqi & >Hstv & _)".
      iMod (sie_ghost_flip_on _ _ _ _ _ with "Hhalf Harm Htok Hqi") as "(Hhalf & Hqcap & Hqcnt & Hqi)".
      iMod ("Hclose" with "[Hqi Hstv]") as "_".
      { iNext. iExists ('b"1" : mword 1). iFrame "Hqi Hstv".
        iModIntro. iIntros "%Hb". iExact "Hspec". }
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
      iAssert (sie_cap m n true p)
        with "[Hqcap Hqcnt Hsepcx Hscausex Hstvalx Hsppc Hstk Htr Hcells]" as "Hcap".
      { iSplitL "Hstk". { iExact "Hstk". }
        iFrame "Htr".
        iFrame "Hqcap Hsepcx Hscausex Hstvalx Hsppc".
        iSplitR "Hcells Hqcnt".
        { iExists handler. iSplit; [iPureIntro; exact Htvd |].
          iSplit; [iPureIntro; exact Hsb |]. iExact "Hinv_i". }
        (* [cpu_hart 0 true p] -- the cells the caller handed in, plus the
           count eighth the flip just produced at '1'. *)
        iSplitL "Hcells"; [ iExact "Hcells" | iExact "Hqcnt" ]. }
      iAssert (sconf) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenvx]" as "Hsc".
      { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
        iExists ms1. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf'. }
      iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
      iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
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
     [intr_handler_avail] it IS [intr_count 1 true] -- the pop_off
     restore leaf applies verbatim (same four-piece ghost choreography:
     bundle half + capability eighth + count eighth + invariant quarter,
     with [trap_csrs] moving INTO the arm's '1' branch alongside an
     [intr_inv] copy taken from the persistent parameter).
       eb = true: SIE is ALREADY '1' (ghost agreement between the arm's own
     eighth and the mstatus-tied half), so the write is idempotent on the
     bit and NO ghost moves; the legalized write still changes mstatus's
     term, but [csrsi_sie_flip] says the new word again has SIE = '1' and
     again satisfies [sconf_ms_facts], which is all the bundle needs.  The
     capability's '1' arm (trap CSRs + per-cpu cells + invariant copy) rides
     through untouched, and every one of the caller's [if eb then emp else _]
     premises is [emp] -- at [eb = true] all of that is ALREADY in the arm,
     which is exactly why the counting token is one of them. *)
  Lemma wp_csrsi_sstatus_x0_enable_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (eb : bool) (m : regfile) (n : nat) :
    sie_cap_gpr m n eb p -∗
    (if eb then emp else intr_count 0 false) -∗
    (if eb then emp else trap_csrs) -∗
    (if eb then emp else cpu_cells 0 true p) -∗
    intr_handler_avail -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS)) -∗
    wp_next eb p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      sie_cap_gpr m n true p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    destruct eb.
    2:{ (* ---- base state DISABLED: the real flip, via the restore leaf ---- *)
        iIntros "Hcg Hcnt Hcsrs Hcells #Havail Hpc Hinstr Hcont".
        iApply (wp_csrsi_sstatus_x0_s_sconf Φ pc m n false
                  with "Hcg [Hcnt] Hcsrs Hcells Hpc Hinstr Hcont").
        iApply (intr_count_pack_S_on 0 with "Hcnt Havail"). }
    (* ---- base state ENABLED: idempotent on SIE, ghosts stand still ---- *)
    iIntros "Hcg _ _ _ #Havail Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n true Φ pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
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
    iDestruct "Hcap" as "(Hstk & Htr & Hq1 & Harest)".
    iDestruct (ghost_var_agree with "Hhalf Hq1") as %Hb1.
    iAssert (sie_cap m n true p) with "[Hstk Htr Hq1 Harest]" as "Hcap".
    { iFrame "Hstk Htr Hq1 Harest". }
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
    iAssert (sconf) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenvx]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
      iExists ms1. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf'. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
    iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
    iApply ("Hcont" $! ms0 with "[%] Hcg [$Hpc' $Hnpc]").
    { exact Hmsf. }
  Qed.

  (* intr_off() at level 0, FROM enabled: the '1'->'0' flip of
     [wp_csrci_sstatus_s_sconf] with rd = x0 and no level push.  Same
     choreography (open intrN, [sie_ghost_flip_off] on all four pieces --
     bundle half + capability eighth + count eighth + invariant quarter --
     reseal at '0' where the handler guard is vacuous), but the freed '1'-arm
     payload lands DIFFERENTLY: the trap CSRs go straight to the caller
     (level 0 with a now-disabled base owes them explicitly), the [intr_inv]
     copy is simply dropped (it is persistent, and the caller keeps its own
     [intr_handler_avail]), and the count eighth comes back at
     [sie_bit false] -- i.e. [intr_count 0 false], not [intr_count 1 _].

     THE TWO EIGHTHS ARE NOT THE CALLER'S TO SUPPLY AT [b = true].  This
     leaf used to demand a separate [intr_count 0 true] BESIDE the bundle,
     and hand back [cpu_hart 0 true p] (which CONTAINS an [intr_count 0
     true]) beside an [intr_count 0 false] -- the same eighth at two
     values, which the comment on [cpu_cells_pay] above forbids.  Nobody
     could hold the premise: at [b = true] the arm owns BOTH eighths
     ([sie_arm]'s own plus the one inside [cpu_hart 0 true p]), and at
     [b = false] the last branch below refutes it outright, so the contract
     was vacuous at every index.  It now takes [intr_count_pre b 0 true]
     (the pure fact at the enabled arm, the token at the disabled one) and
     returns the freed cells as [cpu_cells_pay b p], exactly like its
     sibling [wp_csrci_sstatus_s_sconf]: the flip's second eighth is taken
     out of the arm's own [cpu_hart], not out of the caller. *)
  Lemma wp_csrci_sstatus_x0_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (m : regfile) (n : nat) (b : bool) :
    sie_cap_gpr m n b p -∗
    intr_count_pre b 0 true -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRC)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      sie_cap_gpr m n false p -∗
      intr_count 0 false -∗
      trap_csrs -∗
      cpu_cells_pay b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "Hcg Hcnt Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRC))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
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
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    destruct b.
    - (* ---- b = true: both eighths are in the arm -- its own, and the one
           inside [cpu_hart 0 true p].  Take the second out of THERE (the
           caller supplied only the pure fact) and do the real flip; the
           cells that are left are what the leaf hands back. ---- *)
      iDestruct "Harm" as "(Hq1 & Hhx & Hsepcx & Hscausex & Hstvalx & Hsppc & (Hcells & Hc1))".
      iClear "Hcnt".
      iDestruct (intr_count_get_on 0 true with "Hq1 Hc1") as "(_ & Hq1 & Hcnt)".
      destruct (csrci_sie_flip ms0 Hmsf) as (Hsie' & Hspp' & Hspie' & Hmsf').
      set (ms1 := legalize_sstatus_val ms0 (sstatus_write_val ms0 (mword_of_int 2))).
      (* the trap-vector invariant: open it for the quarter, flip, reseal *)
      iDestruct "Hhx" as (handler) "#Hintr".
      iDestruct "Hintr" as "(%Htvd & %Hsb & #Hinv_i)".
      iMod (inv_acc (⊤ ∖ ↑minstretN) intrN with "Hinv_i") as "[Hbody Hclose]";
        [solve_ndisj|].
      iDestruct "Hbody" as (bq) "(>Hqi & >Hstv & _)".
      iMod (sie_ghost_flip_off _ _ _ _ _ with "Hhalf Hq1 Hcnt Hqi")
        as "(Hhalf & Hq & Htok & Hqi)".
      iMod ("Hclose" with "[Hqi Hstv]") as "_".
      { iNext. iExists ('b"0" : mword 1). iFrame "Hqi Hstv".
        iModIntro. iIntros "%Hb".
        exfalso. apply (f_equal (@bv_unsigned _)) in Hb.
        vm_compute in Hb. discriminate. }
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
      iAssert (sie_cap m n false p) with "[Hstk Htr Hq]" as "Hcap".
      { iSplitL "Hstk"; [iExact "Hstk" |].
        iFrame "Htr". iExact "Hq". }
      iAssert (sconf) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenvx]" as "Hsc".
      { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
        iExists ms1. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf'. }
      iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
      iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
      iApply ("Hcont" $! ms0 with "[%] Hcg [Htok]
                            [Hsepcx Hscausex Hstvalx Hsppc] [Hcells] [$Hpc' $Hnpc]").
      { exact Hmsf. }
      { iExact "Htok". }
      { iFrame "Hsepcx Hscausex Hstvalx Hsppc". }
      { rewrite /cpu_cells_pay. iExact "Hcells". }
    - (* ---- b = false: impossible -- the count eighth at '1' contradicts
           the capability's '0' eighth ---- *)
      iDestruct (intr_count_pre_off with "Hcnt") as "Hcnt".
      iDestruct (ghost_var_agree with "Hcnt Harm") as %Hbad.
      exfalso. apply (f_equal (@bv_unsigned _)) in Hbad.
      vm_compute in Hbad. discriminate.
  Qed.

  (* ---- csrw stvec,rs1 -- installs the trap vector.  The [stvec] cell is
     threaded EXPLICITLY: only the Bare arm of the translation slot owns it,
     so between kvminithart and trapinithart it rides client-side.  The
     written word lands VERBATIM; the one premise on it is that its MODE
     field is not the reserved encoding, which is exactly what
     [legalize_tvec] would otherwise silently rewrite.  Taking the value as
     an explicit [wval] (rather than leaving [m !!! Regidx rs1] in the
     post) keeps the stored term closed at the call site. ---- *)
  Lemma wp_csrw_stvec_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) (tv0 wval : mword 64) :
    uint rs1 <> 0 ->
    rget m rs1 = wval ->
    trapVectorMode_forwards (_get_Mtvec_Mode wval) <> TV_Reserved ->
    sie_cap_gpr m n b p -∗
    stvec ↦ᵣ tv0 -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_stvec, Regidx rs1, zreg, CSRRW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      stvec ↦ᵣ wval -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hwval Hmode) "Hcg Hstv Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (CSRReg (csr_stvec, Regidx rs1, zreg, CSRRW))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & _)".
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

     The written word is taken as [sstatus_read ms0] for a well-formed
     source mstatus [ms0] rather than as an abstract word with a field
     predicate: that IS the only way the instruction is used (kerneltrap
     writes back the sstatus an earlier csrr saved), and it makes the four
     field premises [flip_core] wants derivable inside the leaf instead of
     inflicted on the caller.

     THE WRITE MUST NOT MOVE SIE -- premise [_get_Mstatus_SIE ms0 = sie_bit
     b].  A restore whose saved SIE differs from the live one would have to
     move all THREE ghost pieces and re-seal the interrupt invariant; that
     is what the csrci/csrsi flip leaves are for, and duplicating their
     choreography here would be the wrong shape.  At the trap-handler use
     the premise is free: the trap cleared SIE, nothing in the handler
     turned it back on, and the saved word was read after the clear.

     The post hands back [sie_cap_gpr_at msf] -- the mstatus-EXPOSING
     flavour (IntrDefs) -- because SPP and SPIE are the entire point: they
     are what kernelvec's [sret] reads.  Close it with
     [sie_cap_gpr_at_close] as soon as they have been recorded. ---- *)
  Lemma wp_csrw_sstatus_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) (ms0 : mword 64) (vspp vspie : mword 1) :
    uint rs1 <> 0 ->
    rget m rs1 = sstatus_read ms0 ->
    sconf_ms_facts ms0 ->
    _get_Mstatus_SIE ms0 = sie_bit b ->
    sie_cap_gpr m n b p -∗
    (* THE TRAVELLING SPP HALF.  This is the one instruction that MOVES SPP,
       so it needs both halves: the tie inside [sconf] and this one, which
       interrupts-off code holds (it rides in [trap_csrs]).  At [b = true]
       the enabled arm holds it instead and no caller can supply it -- the
       instance is then vacuous, which is right: SPP is not a value enabled
       code may pin. *)
    sret_bits vspp vspie -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_sstatus, Regidx rs1, zreg, CSRRW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ msf : mword 64,
      ⌜ _get_Mstatus_SIE  msf = _get_Mstatus_SIE  ms0 ⌝ -∗
      ⌜ _get_Mstatus_SPP  msf = _get_Mstatus_SPP  ms0 ⌝ -∗
      ⌜ _get_Mstatus_SPIE msf = _get_Mstatus_SPIE ms0 ⌝ -∗
      sie_cap_gpr_at msf m n b p -∗
      sret_bits (_get_Mstatus_SPP msf) (_get_Mstatus_SPIE msf) -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hwval Hms0f Hsie0) "Hcg Hsppc Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (CSRReg (csr_sstatus, Regidx rs1, zreg, CSRRW))
              with "Hcg Hpc Hinstr").
    iIntros (sigma Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms) "(Hms & Hhalf & Hspp & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & %HmisaC & %HmisaU & _)".
    (* the live SIE bit is the arm index *)
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct (sie_arm_half_agree b p ms with "Hhalf Harm") as %Hsie_ms.
    (* the four field equalities [flip_core] wants: both sides are the
       constants [sconf_ms_facts] pins, on [ms0] and on [ms] respectively. *)
    pose proof Hmsf  as (_ & _ & HMXR  & _ & HXS  & HFS  & HVS  & _ & _ & _).
    pose proof Hms0f as (_ & _ & HMXR0 & _ & HXS0 & HFS0 & HVS0 & _ & _ & _).
    apply eq_vec_true_iff in HMXR. apply eq_vec_true_iff in HMXR0.
    assert (HWsie : _get_Sstatus_SIE (sstatus_read ms0) = _get_Mstatus_SIE ms0)
      by (unfold sstatus_read; rewrite WpGprCsrwC.subrange_full; apply WpGprCsrwC.sSIE_lower).
    assert (HWspp : _get_Sstatus_SPP (sstatus_read ms0) = _get_Mstatus_SPP ms0)
      by (unfold sstatus_read; rewrite WpGprCsrwC.subrange_full; apply WpGprCsrwC.sSPP_lower).
    assert (HWspie : _get_Sstatus_SPIE (sstatus_read ms0) = _get_Mstatus_SPIE ms0)
      by (unfold sstatus_read; rewrite WpGprCsrwC.subrange_full; apply WpGprCsrwC.sSPIE_lower).
    assert (HWmxr : _get_Sstatus_MXR (sstatus_read ms0) = _get_Mstatus_MXR ms).
    { unfold sstatus_read; rewrite WpGprCsrwC.subrange_full; rewrite WpGprCsrwC.sMXR_lower.
      rewrite HMXR0 HMXR. reflexivity. }
    assert (HWfs : _get_Sstatus_FS (sstatus_read ms0) = _get_Mstatus_FS ms).
    { unfold sstatus_read; rewrite WpGprCsrwC.subrange_full; rewrite WpGprCsrwC.sFS_lower.
      rewrite HFS0 HFS. reflexivity. }
    assert (HWvs : _get_Sstatus_VS (sstatus_read ms0) = _get_Mstatus_VS ms).
    { unfold sstatus_read; rewrite WpGprCsrwC.subrange_full; rewrite WpGprCsrwC.sVS_lower.
      rewrite HVS0 HVS. reflexivity. }
    assert (HWxs : _get_Sstatus_XS (sstatus_read ms0) = _get_Mstatus_XS ms).
    { unfold sstatus_read; rewrite WpGprCsrwC.subrange_full; rewrite WpGprCsrwC.sXS_lower.
      rewrite HXS0 HXS. reflexivity. }
    set (ms1 := legalize_sstatus_val ms (sstatus_read ms0)).
    destruct (flip_core ms (sstatus_read ms0) (_get_Mstatus_SIE ms0)
                Hmsf HWsie HWmxr HWfs HWvs HWxs)
      as (Hf_sie & Hf_spp & Hf_spie & Hf_facts).
    fold ms1 in Hf_sie, Hf_spp, Hf_spie, Hf_facts.
    rewrite HWspp in Hf_spp. rewrite HWspie in Hf_spie.
    (* the ghost half does not move: both indices are [sie_bit b] *)
    assert (Hhalf_eq : _get_Mstatus_SIE ms1 = _get_Mstatus_SIE ms)
      by (rewrite Hf_sie Hsie0 Hsie_ms; reflexivity).
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
                   = sstatus_read ms0).
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
    rewrite /sie_cap. iFrame "Hstk Htr Harm Hfile".
  Qed.

  (* ---- csrw sepc,rs1 -- restores the trapped pc.  The [sepc] cell is
     threaded EXPLICITLY, exactly as stvec's is at [wp_csrw_stvec_s_sconf]
     and for the same reason: at [b = false] nothing in the ambient bundle
     owns it (the enabled arm's copy exists only at [b = true], and a
     handler running with interrupts off holds the trap CSRs itself).
     Unlike stvec's, the written word does NOT land verbatim: sepc's write
     legalizes through [mepc_val], so the post-value carries the wrapper --
     a caller writing back a 2-aligned epc collapses it. ---- *)
  Lemma wp_csrw_sepc_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) (ep0 wval : mword 64) :
    uint rs1 <> 0 ->
    rget m rs1 = wval ->
    sie_cap_gpr m n b p -∗
    sepc ↦ᵣ ep0 -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_sepc, Regidx rs1, zreg, CSRRW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      sepc ↦ᵣ mepc_val wval -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hwval) "Hcg Hsepc Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (CSRReg (csr_sepc, Regidx rs1, zreg, CSRRW))
              with "Hcg Hpc Hinstr").
    iIntros (sigma Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & _)".
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
  (* every instance.  Note [sie_cap] is untouched: at [b = true] its arm   *)
  (* holds trap-CSR cells of its OWN under existentials, and this leaf     *)
  (* never opens it -- so a caller at that arm must be lending a share it  *)
  (* got from somewhere else.                                              *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_csrr_ro_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (csrn : mword 12) (rg : register_bitvector_64)
      (f : mword 64 -> mword 64) (rd : mword 5)
      (m : regfile) (n : nat) (b : bool) (dq : dfrac) (v : mword 64) :
    uint rd <> 0 ->
    rd_ok rd ->
    register_beq (R_bitvector_64 rg) nextPC = false ->
    ( forall s : mstate,
        register_lookup cur_privilege s.(sregs) = Supervisor ->
        eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
        eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
        exec (execute (CSRReg (csrn, zreg, Regidx rd, CSRRS))) s
          = Some (RETIRE_SUCCESS,
                  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg
                       (f (register_lookup (R_bitvector_64 rg) s.(sregs))))) ) ->
    sie_cap_gpr m n b p -∗
    R_bitvector_64 rg ↦ᵣ{dq} v -∗
    pc_is pc -∗
    instr pc false (CSRReg (csrn, zreg, Regidx rd, CSRRS)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg (f v)]> m) n b p -∗
      R_bitvector_64 rg ↦ᵣ{dq} v -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdok Hne Hexec) "Hcg Hcell Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    iApply (wp_instr_s_sconf m n b Φ pc false
              (CSRReg (csrn, zreg, Regidx rd, CSRRS))
              with "Hcg Hpc Hinstr").
    iIntros (sigma Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hrest)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & %HmisaC & _)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hcell") as %Lcell.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg sigma nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
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
        rewrite Lmisa_spc; [ exact HmisaS | exact HmisaC ]. }
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
                 (<[Regidx rd := regval_into_reg (f v)]> m) n b Hsp with "Hcap") as "Hcap".
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hminv $Hpriv $Hrest] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg Hcell [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* ---- the three instances.  scause and stval read their cell verbatim;
     sepc's read runs [align_pc], so its value carries [mepc_val]. ---- *)

  Lemma wp_csrr_scause_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5)
      (m : regfile) (n : nat) (b : bool) (dq : dfrac) (sc : mword 64) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr m n b p -∗
    scause ↦ᵣ{dq} sc -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_scause, zreg, Regidx rd, CSRRS)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg sc]> m) n b p -∗
      scause ↦ᵣ{dq} sc -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdok).
    iApply (wp_csrr_ro_s_sconf Φ pc csr_scause scause (fun x => x) rd m n b dq sc
              Hrd Hrdok ltac:(vm_compute; reflexivity)).
    intros s Hpriv HS _.
    exact (exec_execute_csrr_scause_gpr_S rd s Hrd Hpriv HS).
  Qed.

  Lemma wp_csrr_stval_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5)
      (m : regfile) (n : nat) (b : bool) (dq : dfrac) (tv : mword 64) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr m n b p -∗
    stval ↦ᵣ{dq} tv -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_stval, zreg, Regidx rd, CSRRS)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg tv]> m) n b p -∗
      stval ↦ᵣ{dq} tv -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdok).
    iApply (wp_csrr_ro_s_sconf Φ pc csr_stval stval (fun x => x) rd m n b dq tv
              Hrd Hrdok ltac:(vm_compute; reflexivity)).
    intros s Hpriv HS _.
    exact (exec_execute_csrr_stval_gpr_S rd s Hrd Hpriv HS).
  Qed.

  (* sepc: the value that lands in [rd] is [mepc_val ep], not [ep].  A
     caller that knows its saved epc is 2-aligned (every write to the cell
     went through [legalize_xepc], and every trap writes an aligned pc)
     collapses the wrapper itself; the leaf does not assume it. *)
  Lemma wp_csrr_sepc_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5)
      (m : regfile) (n : nat) (b : bool) (dq : dfrac) (ep : mword 64) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr m n b p -∗
    sepc ↦ᵣ{dq} ep -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_sepc, zreg, Regidx rd, CSRRS)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg (mepc_val ep)]> m) n b p -∗
      sepc ↦ᵣ{dq} ep -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdok).
    iApply (wp_csrr_ro_s_sconf Φ pc csr_sepc sepc mepc_val rd m n b dq ep
              Hrd Hrdok ltac:(vm_compute; reflexivity)).
    intros s Hpriv HS HC.
    exact (exec_execute_csrr_sepc_gpr_S rd s Hrd Hpriv HS HC).
  Qed.

End WpSconfCsr.
