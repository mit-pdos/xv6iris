(* UserExecFacts.v -- pure U-mode [execute] facts for the trap-producing
   instruction families, feeding the classification's per-family
   obligations (UserArms.v):

     ECALL / EBREAK       -> [rv64d_types.Trap (User, make_sync_exception
                             e xv, pc)] with the state UNCHANGED -- these
                             feed [execute_trap_obligation] directly
                             (E_U_EnvCall's tval is None for any xv, so
                             the [make_sync_exception] spelling matches
                             execute_ECALL's literal record).
     MRET / SRET / WFI /
     the sfence family    -> [Illegal_Instruction tt] with the state
                             UNCHANGED (every privileged instruction is
                             illegal at User; WFI because
                             [plat_wfi_available_to_usermode = false]) --
                             these feed [illegal_obligation], whose step
                             shape delivers E_Illegal_Instr with the
                             INSTRUCTION BITS as tval
                             ([exec_riscv_step_execute_illegal],
                             UserTrap.v).  SINVAL_VMA is an [ExecuteAs]
                             redirection to SFENCE_VMA.

   All lemmas are stated at an ARBITRARY state with the two lookups the
   clauses read (cur_privilege = User, PC) -- no page-table or fetch
   machinery is involved.                                                 *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

Lemma exec_execute_ECALL_U (s : mstate) (va : mword 64) :
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup PC s.(sregs) = va ->
  exec (execute (ECALL tt)) s
    = Some (rv64d_types.Trap
              (User, make_sync_exception (E_U_EnvCall tt) (zeros' 64), va), s).
Proof.
  intros Hpriv Hpc.
  change (execute (ECALL tt)) with (execute_ECALL tt).
  unfold execute_ECALL.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite Hpriv. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (E_U_EnvCall tt) s)). cbn beta.
  cbv zeta.
  unfold trap.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)). cbn beta.
  rewrite Hpc.
  apply exec_returnm.
Qed.

Lemma exec_execute_EBREAK_U (s : mstate) (va : mword 64) :
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup PC s.(sregs) = va ->
  exec (execute (EBREAK tt)) s
    = Some (rv64d_types.Trap
              (User, make_sync_exception (E_Breakpoint Brk_Software) va, va), s).
Proof.
  intros Hpriv Hpc.
  change (execute (EBREAK tt)) with (execute_EBREAK tt).
  unfold execute_EBREAK.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)). cbn beta.
  rewrite Hpc.
  unfold trap.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)). cbn beta.
  rewrite Hpc.
  apply exec_returnm.
Qed.

Lemma exec_execute_MRET_U (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (execute (MRET tt)) s = Some (Illegal_Instruction tt, s).
Proof.
  intros Hpriv.
  change (execute (MRET tt)) with (execute_MRET tt).
  unfold execute_MRET.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite Hpriv.
  replace (generic_neq User Machine) with true by reflexivity. cbn match.
  apply exec_returnm.
Qed.

Lemma exec_execute_SRET_U (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (execute (SRET tt)) s = Some (Illegal_Instruction tt, s).
Proof.
  intros Hpriv.
  change (execute (SRET tt)) with (execute_SRET tt).
  unfold execute_SRET.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite Hpriv. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM true s)). cbn beta.
  cbn match.
  apply exec_returnm.
Qed.

Lemma exec_execute_WFI_U (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (execute (WFI tt)) s = Some (Illegal_Instruction tt, s).
Proof.
  intros Hpriv.
  change (execute (WFI tt)) with (execute_WFI tt).
  unfold execute_WFI.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite Hpriv. cbn match.
  apply exec_returnm.
Qed.

(* the sfence/sinval family: illegal at User.  SFENCE_VMA reads its two
   source registers (harmlessly, via the total [exec_rX_bits_gpr]) before
   the privilege check; the barrier sfences check privilege directly.
   SINVAL_VMA is a pure [ExecuteAs] REDIRECTION to SFENCE_VMA -- the
   classification composes it through the one-redirection path.           *)
Require Import WpGpr.

Lemma exec_execute_SFENCE_VMA_U (i1 i2 : mword 5) (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (execute (SFENCE_VMA (Regidx i1, Regidx i2))) s
    = Some (Illegal_Instruction tt, s).
Proof.
  intros Hpriv.
  change (execute (SFENCE_VMA (Regidx i1, Regidx i2)))
    with (execute_SFENCE_VMA (Regidx i1) (Regidx i2)).
  unfold execute_SFENCE_VMA.
  destruct (generic_neq (Regidx i1) zreg) eqn:E1;
  destruct (generic_neq (Regidx i2) zreg) eqn:E2.
  - erewrite exec_bind_Some.
    2:{ erewrite exec_bind_Some; [ apply exec_returnm | apply (exec_rX_bits_gpr i1 s) ]. }
    cbn beta.
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind_Some; [ apply exec_returnm | apply (exec_rX_bits_gpr i2 s) ]. }
    cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite Hpriv. cbn match.
    apply exec_returnm.
  - erewrite exec_bind_Some.
    2:{ erewrite exec_bind_Some; [ apply exec_returnm | apply (exec_rX_bits_gpr i1 s) ]. }
    cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (@None (mword 16)) s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite Hpriv. cbn match.
    apply exec_returnm.
  - rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (@None (mword 64)) s)). cbn beta.
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind_Some; [ apply exec_returnm | apply (exec_rX_bits_gpr i2 s) ]. }
    cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite Hpriv. cbn match.
    apply exec_returnm.
  - rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (@None (mword 64)) s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (@None (mword 16)) s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite Hpriv. cbn match.
    apply exec_returnm.
Qed.

Lemma exec_execute_SFENCE_W_INVAL_U (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (execute (SFENCE_W_INVAL tt)) s = Some (Illegal_Instruction tt, s).
Proof.
  intros Hpriv.
  change (execute (SFENCE_W_INVAL tt)) with (execute_SFENCE_W_INVAL tt).
  unfold execute_SFENCE_W_INVAL.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite Hpriv.
  replace (generic_eq User User) with true by reflexivity. cbn match.
  apply exec_returnm.
Qed.

Lemma exec_execute_SFENCE_INVAL_IR_U (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (execute (SFENCE_INVAL_IR tt)) s = Some (Illegal_Instruction tt, s).
Proof.
  intros Hpriv.
  change (execute (SFENCE_INVAL_IR tt)) with (execute_SFENCE_INVAL_IR tt).
  unfold execute_SFENCE_INVAL_IR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite Hpriv.
  replace (generic_eq User User) with true by reflexivity. cbn match.
  apply exec_returnm.
Qed.

Lemma exec_execute_SINVAL_VMA (rs1 rs2 : regidx) (s : mstate) :
  exec (execute (SINVAL_VMA (rs1, rs2))) s
    = Some (ExecuteAs (SFENCE_VMA (rs1, rs2)), s).
Proof. apply exec_returnm. Qed.

(* WRS: a PURE Enter_Wait outcome (user-executable; the enter-wait step
   shape parks the hart WAITING with no pc tick).                          *)
Lemma exec_execute_WRS (op : wrsop) (s : mstate) :
  exec (execute (WRS op)) s
    = Some (Enter_Wait (match op with
                        | WRS_STO => WAIT_WRS_STO
                        | WRS_NTO => WAIT_WRS_NTO
                        end), s).
Proof. destruct op; apply exec_returnm. Qed.
