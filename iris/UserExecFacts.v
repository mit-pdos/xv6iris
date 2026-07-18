(* UserExecFacts.v -- pure U-mode [execute] facts for the trap-producing
   instruction families, feeding the classification's per-family
   obligations (UserArms.v):

     ECALL / EBREAK       -> [rv64d_types.Trap (User, make_sync_exception
                             e xv, pc)] with the state UNCHANGED -- these
                             feed [execute_trap_obligation] directly
                             (E_U_EnvCall's tval is None for any xv, so
                             the [make_sync_exception] spelling matches
                             execute_ECALL's literal record).
     MRET / SRET / WFI    -> [Illegal_Instruction tt] with the state
                             UNCHANGED (every privileged instruction is
                             illegal at User; WFI because
                             [plat_wfi_available_to_usermode = false]) --
                             these feed [illegal_obligation], whose step
                             shape delivers E_Illegal_Instr with the
                             INSTRUCTION BITS as tval
                             ([exec_riscv_step_execute_illegal],
                             UserTrap.v).

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
