(* UmodeCsr.v -- U-mode CSR access to a PRIVILEGED CSR is illegal.

   A CSR instruction (CSRReg / CSRImm) naming a CSR whose privilege field
   (bits [9:8]) is above User traps to Illegal_Instruction whenever run in
   User mode: check_CSR's first conjunct check_CSR_priv fails (User's CSR
   privbits 0b00 are not >=u the CSR's), and and_boolM short-circuits, so
   doCSR returns Illegal without ever reading the CSR (no read_CSR
   dispatch, no register reads, no state change).  This is the safety
   statement that user code cannot touch privileged CSRs.  The execute
   facts feed the privilege-conditioned trap arm ustep_illegal_st. *)
From Stdlib Require Import ZArith Lia List Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep.
Require Import WpGpr.
Local Open Scope Z_scope.
Import Defs.

(* check_CSR_result for a User access to a CSR whose privilege field is above
   User: check_CSR_priv fails, and_boolM short-circuits check_CSR to false,
   and User is not a virtual privilege, so the result is CSR_Illegal.  The
   access type is irrelevant (the priv check does not consult it). *)
Lemma exec_check_CSR_result_illegal_u (csr : mword 12) (acc : CSRAccessType) s :
  zopz0zKzJ_u ('b"00" : mword 2) (csrPriv csr) = false ->
  exec (check_CSR_result csr User acc) s = Some (CSR_Illegal tt, s).
Proof.
  intro Hpriv.
  unfold check_CSR_result.
  assert (Hcc : exec (check_CSR csr User acc) s = Some (false, s)).
  { unfold check_CSR.
    assert (Hpr : exec (check_CSR_priv csr User) s = Some (false, s)).
    { unfold check_CSR_priv.
      rewrite (exec_bind_Some _ _ _ _ _
                 (_ : exec (privLevel_to_CSR_privbits User) s = Some ('b"00", s))).
      2:{ cbn. apply exec_returnm. }
      rewrite (exec_returnM _ s). rewrite Hpriv. reflexivity. }
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hpr). reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ Hcc). cbn match.
  match goal with
  | |- context [ Defs.bind (Defs.and_boolM ?l ?r) _ ] =>
      assert (Hab : exec (Defs.and_boolM l r) s = Some (false, s))
  end.
  { rewrite (exec_and_boolM_Some _ _ _ _ _
               (_ : exec (returnM (orb (generic_eq User VirtualSupervisor) (generic_eq User VirtualUser)) : M bool) s = Some (false, s))).
    - reflexivity.
    - replace (orb (generic_eq User VirtualSupervisor) (generic_eq User VirtualUser))
        with false by (vm_compute; reflexivity).
      apply exec_returnm. }
  rewrite (exec_bind_Some _ _ _ _ _ Hab). cbn match. apply exec_returnm.
Qed.

(* doCSR to a privileged CSR at User -> Illegal (state-preserving). *)
Lemma exec_doCSR_illegal_u (csr : mword 12) (v : mword 64) (rd : regidx) (op : csrop)
    (acc : CSRAccessType) s :
  register_lookup cur_privilege s.(sregs) = User ->
  zopz0zKzJ_u ('b"00" : mword 2) (csrPriv csr) = false ->
  exec (doCSR csr v rd op acc) s = Some (Illegal_Instruction tt, s).
Proof.
  intros Hcp Hpriv.
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_result_illegal_u csr acc s Hpriv)).
  cbn match. apply exec_returnM.
Qed.

(* CSRReg (csrrw/csrrs/csrrc) to a privileged CSR at User is illegal. *)
Lemma exec_execute_CSRReg_illegal_u (csr : mword 12) (rs1 rd : mword 5) (op : csrop) s :
  register_lookup cur_privilege s.(sregs) = User ->
  zopz0zKzJ_u ('b"00" : mword 2) (csrPriv csr) = false ->
  exec (execute (CSRReg (csr, Regidx rs1, Regidx rd, op))) s = Some (Illegal_Instruction tt, s).
Proof.
  intros Hcp Hpriv.
  change (execute (CSRReg (csr, Regidx rs1, Regidx rd, op)))
    with (execute_CSRReg csr (Regidx rs1) (Regidx rd) op).
  unfold execute_CSRReg. cbv zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  apply (exec_doCSR_illegal_u csr _ (Regidx rd) op _ s Hcp Hpriv).
Qed.

(* CSRImm (csrrwi/csrrsi/csrrci) to a privileged CSR at User is illegal. *)
Lemma exec_execute_CSRImm_illegal_u (csr : mword 12) (imm rd : mword 5) (op : csrop) s :
  register_lookup cur_privilege s.(sregs) = User ->
  zopz0zKzJ_u ('b"00" : mword 2) (csrPriv csr) = false ->
  exec (execute (CSRImm (csr, imm, Regidx rd, op))) s = Some (Illegal_Instruction tt, s).
Proof.
  intros Hcp Hpriv.
  change (execute (CSRImm (csr, imm, Regidx rd, op)))
    with (execute_CSRImm csr imm (Regidx rd) op).
  unfold execute_CSRImm. cbv zeta.
  apply (exec_doCSR_illegal_u csr _ (Regidx rd) op _ s Hcp Hpriv).
Qed.
