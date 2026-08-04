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
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
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

(* ===================================================================== *)
(* RETIRING compute-family TOTALITY facts: for EVERY operand assignment    *)
(* (including rd = x0), execute retires with a single (possibly vacuous)   *)
(* gpr write -- the shape [retire_obligation]'s dischargers need.  The     *)
(* written VALUE is existential: safety never tracks it.                   *)
(* [gpr_write_state] is [exec_wX_bits_gpr]'s post-state, packaged.         *)
(* ===================================================================== *)

Definition gpr_write_state (rd : mword 5) (v : mword 64) (s : mstate) : mstate :=
  if Z.eqb (uint rd) 0 then s
  else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) v.

Lemma exec_execute_ITYPE_total (imm : mword 12) (i1 ird : mword 5)
    (op : iop) (s : mstate) :
  exists v : mword 64,
    exec (execute (ITYPE (imm, Regidx i1, Regidx ird, op))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (ITYPE (imm, Regidx i1, Regidx ird, op)))
    with (execute_ITYPE imm (Regidx i1) (Regidx ird) op).
  unfold execute_ITYPE, gpr_write_state. cbv zeta.
  destruct op; eexists;
    (erewrite exec_bind_Some;
      [ | erewrite exec_bind_Some; [ apply exec_returnm | apply (exec_rX_bits_gpr i1 s) ] ]);
    cbn beta;
    (erewrite exec_bind0_Some;
      [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ]).
Qed.

Lemma exec_execute_RTYPE_total (i2 i1 ird : mword 5) (op : rop) (s : mstate) :
  exists v : mword 64,
    exec (execute (RTYPE (Regidx i2, Regidx i1, Regidx ird, op))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (RTYPE (Regidx i2, Regidx i1, Regidx ird, op)))
    with (execute_RTYPE (Regidx i2) (Regidx i1) (Regidx ird) op).
  unfold execute_RTYPE, gpr_write_state.
  destruct op; eexists;
    (erewrite exec_bind_Some;
      [ | erewrite exec_bind_Some;
          [ cbn beta;
            erewrite exec_bind_Some;
            [ apply exec_returnm | apply (exec_rX_bits_gpr i2 s) ]
          | apply (exec_rX_bits_gpr i1 s) ] ]);
    cbn beta;
    (erewrite exec_bind0_Some;
      [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ]).
Qed.

Lemma exec_execute_RTYPEW_total (i2 i1 ird : mword 5) (op : ropw) (s : mstate) :
  exists v : mword 64,
    exec (execute (RTYPEW (Regidx i2, Regidx i1, Regidx ird, op))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (RTYPEW (Regidx i2, Regidx i1, Regidx ird, op)))
    with (execute_RTYPEW (Regidx i2) (Regidx i1) (Regidx ird) op).
  unfold execute_RTYPEW, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i2 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_SHIFTIOP_total (shamt : mword 6) (i1 ird : mword 5)
    (op : sop) (s : mstate) :
  exists v : mword 64,
    exec (execute (SHIFTIOP (shamt, Regidx i1, Regidx ird, op))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (SHIFTIOP (shamt, Regidx i1, Regidx ird, op)))
    with (execute_SHIFTIOP shamt (Regidx i1) (Regidx ird) op).
  unfold execute_SHIFTIOP, gpr_write_state. cbv zeta.
  destruct op; eexists;
    (erewrite exec_bind_Some;
      [ | erewrite exec_bind_Some; [ apply exec_returnm | apply (exec_rX_bits_gpr i1 s) ] ]);
    cbn beta;
    (erewrite exec_bind0_Some;
      [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ]).
Qed.

Lemma exec_execute_SHIFTIWOP_total (shamt : mword 5) (i1 ird : mword 5)
    (op : sopw) (s : mstate) :
  exists v : mword 64,
    exec (execute (SHIFTIWOP (shamt, Regidx i1, Regidx ird, op))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (SHIFTIWOP (shamt, Regidx i1, Regidx ird, op)))
    with (execute_SHIFTIWOP shamt (Regidx i1) (Regidx ird) op).
  unfold execute_SHIFTIWOP, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_ADDIW_total (imm : mword 12) (i1 ird : mword 5) (s : mstate) :
  exists v : mword 64,
    exec (execute (ADDIW (imm, Regidx i1, Regidx ird))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (ADDIW (imm, Regidx i1, Regidx ird)))
    with (execute_ADDIW imm (Regidx i1) (Regidx ird)).
  unfold execute_ADDIW, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_MUL_total (i2 i1 ird : mword 5) (op : mul_op) (s : mstate) :
  exists v : mword 64,
    exec (execute (MUL (Regidx i2, Regidx i1, Regidx ird, op))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (MUL (Regidx i2, Regidx i1, Regidx ird, op)))
    with (execute_MUL (Regidx i2) (Regidx i1) (Regidx ird) op).
  unfold execute_MUL, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i2 s) ]. cbn beta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_MULW_total (i2 i1 ird : mword 5) (s : mstate) :
  exists v : mword 64,
    exec (execute (MULW (Regidx i2, Regidx i1, Regidx ird))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (MULW (Regidx i2, Regidx i1, Regidx ird)))
    with (execute_MULW (Regidx i2) (Regidx i1) (Regidx ird)).
  unfold execute_MULW, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i2 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_DIV_total (i2 i1 ird : mword 5) (u : bool) (s : mstate) :
  exists v : mword 64,
    exec (execute (DIV (Regidx i2, Regidx i1, Regidx ird, u))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (DIV (Regidx i2, Regidx i1, Regidx ird, u)))
    with (execute_DIV (Regidx i2) (Regidx i1) (Regidx ird) u).
  unfold execute_DIV, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i2 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_DIVW_total (i2 i1 ird : mword 5) (u : bool) (s : mstate) :
  exists v : mword 64,
    exec (execute (DIVW (Regidx i2, Regidx i1, Regidx ird, u))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (DIVW (Regidx i2, Regidx i1, Regidx ird, u)))
    with (execute_DIVW (Regidx i2) (Regidx i1) (Regidx ird) u).
  unfold execute_DIVW, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i2 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_REM_total (i2 i1 ird : mword 5) (u : bool) (s : mstate) :
  exists v : mword 64,
    exec (execute (REM (Regidx i2, Regidx i1, Regidx ird, u))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (REM (Regidx i2, Regidx i1, Regidx ird, u)))
    with (execute_REM (Regidx i2) (Regidx i1) (Regidx ird) u).
  unfold execute_REM, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i2 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_REMW_total (i2 i1 ird : mword 5) (u : bool) (s : mstate) :
  exists v : mword 64,
    exec (execute (REMW (Regidx i2, Regidx i1, Regidx ird, u))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (REMW (Regidx i2, Regidx i1, Regidx ird, u)))
    with (execute_REMW (Regidx i2) (Regidx i1) (Regidx ird) u).
  unfold execute_REMW, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i2 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

(* PAUSE / NTL: pure RETIRE_SUCCESS no-ops. *)
Lemma exec_execute_PAUSE (s : mstate) :
  exec (execute (PAUSE tt)) s = Some (RETIRE_SUCCESS, s).
Proof. apply exec_returnm. Qed.

Lemma exec_execute_UTYPE_total (imm : mword 20) (ird : mword 5)
    (op : uop) (s : mstate) :
  exists v : mword 64,
    exec (execute (UTYPE (imm, Regidx ird, op))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (UTYPE (imm, Regidx ird, op)))
    with (execute_UTYPE imm (Regidx ird) op).
  unfold execute_UTYPE, gpr_write_state. cbv zeta.
  destruct op; eexists.
  - (* LUI: pure *)
    erewrite exec_bind_Some; [ | apply exec_returnm ]. cbn beta.
    erewrite exec_bind0_Some;
      [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
  - (* AUIPC: reads PC *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind_Some; [ apply exec_returnm | ].
        unfold get_arch_pc. apply (exec_read_reg PC s). }
    cbn beta.
    erewrite exec_bind0_Some;
      [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

(* the fence family: state-preserving retires (a barrier is a no-op in the
   functional interpreter).  FENCE's pred/succ dispatch is a pure if-tree
   over the effective sets; at User [is_fiom_active] reads menvcfg and
   senvcfg (values irrelevant -- every branch is a barrier-or-nothing). *)
Local Lemma exec_sail_barrier' (b : Arch.barrier) s :
  exec (sail_barrier b) s = Some (tt, s).
Proof. reflexivity. Qed.

Lemma exec_execute_NTL (g : ntl_type) (s : mstate) :
  exec (execute (NTL g)) s = Some (RETIRE_SUCCESS, s).
Proof. apply exec_returnm. Qed.

Lemma exec_execute_FENCE_TSO_U (s : mstate) :
  exec (execute (FENCE_TSO tt)) s = Some (RETIRE_SUCCESS, s).
Proof.
  change (execute (FENCE_TSO tt)) with (execute_FENCE_TSO tt).
  unfold execute_FENCE_TSO.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_sail_barrier' _ s)).
  apply exec_returnm.
Qed.

Lemma exec_execute_FENCEI_U (imm : mword 12) (i1 ird : mword 5) (s : mstate) :
  exec (execute (FENCEI (imm, Regidx i1, Regidx ird))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  change (execute (FENCEI (imm, Regidx i1, Regidx ird)))
    with (execute_FENCEI imm (Regidx i1) (Regidx ird)).
  unfold execute_FENCEI.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_sail_barrier' _ s)).
  apply exec_returnm.
Qed.

Lemma exec_execute_FENCE_total_U (fm pred succ : mword 4) (i1 ird : mword 5)
    (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (execute (FENCE (fm, pred, succ, Regidx i1, Regidx ird))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intros Hpriv.
  change (execute (FENCE (fm, pred, succ, Regidx i1, Regidx ird)))
    with (execute_FENCE fm pred succ (Regidx i1) (Regidx ird)).
  unfold execute_FENCE.
  erewrite exec_bind_Some.
  2:{ unfold is_fiom_active.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
      rewrite Hpriv. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn beta.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg s)). cbn beta.
      apply exec_returnm. }
  cbn beta. cbv zeta.
  cbn match.
  erewrite exec_bind0_Some.
  2:{ repeat match goal with
             | |- exec (if ?b then _ else _) _ = _ => destruct b
             | |- exec (returnM (if ?b then _ else _)) _ = _ => destruct b
             end;
      first [ apply (exec_sail_barrier' _ s) | apply exec_returnm ]. }
  apply exec_returnm.
Qed.

(* ===================================================================== *)
(* CONTROL FLOW: JAL / JALR / BTYPE.  All three route through [jump_to];   *)
(* with C enabled ([currentlyEnabled Ext_Zca = true], from hw_config's     *)
(* misa pin) a 2-aligned target always succeeds.  The BIT-0 premise on     *)
(* JAL/BTYPE targets is a DECODER invariant (encdec appends '0' to the     *)
(* immediate; the fetched pc is 2-aligned) -- jump_to ASSERTS it (a false  *)
(* assert is stuck, not a trap), so the classification must discharge it   *)
(* from the planned decode-wf refinement of [decode_total_u_set].  JALR    *)
(* clears bit 0 explicitly, so it needs no such premise -- only the        *)
(* Zicfilp-off reduction for [update_elp_state].                           *)
(* ===================================================================== *)
Require Import ExecCommon WpIntrCore UserBits.

Lemma exec_execute_JAL_total (imm : mword 21) (ird : mword 5) (s : mstate) :
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  eq_vec (access_vec_dec
            (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0)
         ('b"0") = true ->
  exists v : mword 64,
    exec (execute (JAL (imm, Regidx ird))) s
      = Some (RETIRE_SUCCESS,
              gpr_write_state ird v
                (set_reg s nextPC
                   (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))).
Proof.
  intros Hzca Halign.
  change (execute (JAL (imm, Regidx ird))) with (execute_JAL imm (Regidx ird)).
  unfold execute_JAL, get_next_pc, gpr_write_state.
  eexists.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)). cbn beta.
  change RETIRE_SUCCESS with (Retire_Success tt). cbn match.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ _) ].
Qed.

Lemma exec_execute_JALR_total (imm : mword 12) (i1 ird : mword 5) (s : mstate) :
  exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s) ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exists (v tgt : mword 64),
    exec (execute (JALR (imm, Regidx i1, Regidx ird))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v (set_reg s nextPC tgt)).
Proof.
  intros Hzic Hzca.
  pose proof bit0_update0_64 as Hbit0.
  change (execute (JALR (imm, Regidx i1, Regidx ird)))
    with (execute_JALR imm (Regidx i1) (Regidx ird)).
  unfold execute_JALR, gpr_write_state.
  assert (Help : exec (update_elp_state (Regidx i1)) s = Some (tt, s)).
  { unfold update_elp_state. rewrite (exec_bind_Some _ _ _ _ _ Hzic).
    cbn match. apply exec_returnm. }
  assert (Hpre : exec (Defs.bind0 (update_elp_state (Regidx i1)) (get_next_pc tt)) s
                 = Some (register_lookup nextPC s.(sregs), s)).
  { rewrite (exec_bind0_Some _ _ _ _ _ Help).
    unfold get_next_pc. exact (exec_read_reg nextPC s). }
  do 2 eexists.
  rewrite (exec_bind_Some _ _ _ _ _ Hpre).
  cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr i1 s)). cbn beta. cbv zeta.
  erewrite exec_bind_Some.
  2:{ apply (exec_jump_to_zca _ s); [ apply Hbit0 | exact Hzca ]. }
  cbn beta.
  change RETIRE_SUCCESS with (Retire_Success tt). cbn match.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ _) ].
Qed.

Lemma exec_execute_BTYPE_total (imm : mword 13) (i2 i1 : mword 5)
    (op : bop) (s : mstate) :
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  eq_vec (access_vec_dec
            (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0)
         ('b"0") = true ->
  exists s' : mstate,
    exec (execute (BTYPE (imm, Regidx i2, Regidx i1, op))) s
      = Some (RETIRE_SUCCESS, s')
    /\ (s' = s \/
        s' = set_reg s nextPC
               (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
Proof.
  intros Hzca Halign.
  change (execute (BTYPE (imm, Regidx i2, Regidx i1, op)))
    with (execute_BTYPE imm (Regidx i2) (Regidx i1) op).
  unfold execute_BTYPE.
  destruct op;
    ((erewrite exec_bind_Some;
       [ | erewrite exec_bind_Some;
           [ cbn beta;
             erewrite exec_bind_Some;
             [ apply exec_returnm | apply (exec_rX_bits_gpr i2 s) ]
           | apply (exec_rX_bits_gpr i1 s) ] ]);
     cbn beta;
     (match goal with
      | |- context [ if ?C then _ else _ ] => destruct C
      end;
      [ (* taken: read PC, jump_to *)
        eexists; split;
        [ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)); cbn beta;
          apply (exec_jump_to_zca _ s Halign Hzca)
        | right; reflexivity ]
      | (* fall-through *)
        eexists; split; [ apply exec_returnm | left; reflexivity ] ])).
Qed.

(* ===================================================================== *)
(* The Zbb / Zbs-adjacent / Zicond / Zbc / Zimop retiring families.  Their *)
(* extension gates live at DECODE time (the decoder only produces these    *)
(* constructors when the extension is enabled), so the execute bodies are  *)
(* gate-free plain read/compute/write shapes.                              *)
(* ===================================================================== *)

Lemma exec_execute_ZBB_RTYPE_total (i2 i1 ird : mword 5) (op : brop_zbb) (s : mstate) :
  exists v : mword 64,
    exec (execute (ZBB_RTYPE (Regidx i2, Regidx i1, Regidx ird, op))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (ZBB_RTYPE (Regidx i2, Regidx i1, Regidx ird, op)))
    with (execute_ZBB_RTYPE (Regidx i2) (Regidx i1) (Regidx ird) op).
  unfold execute_ZBB_RTYPE, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i2 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_ZBB_RTYPEW_total (i2 i1 ird : mword 5) (op : bropw_zbb) (s : mstate) :
  exists v : mword 64,
    exec (execute (ZBB_RTYPEW (Regidx i2, Regidx i1, Regidx ird, op))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (ZBB_RTYPEW (Regidx i2, Regidx i1, Regidx ird, op)))
    with (execute_ZBB_RTYPEW (Regidx i2) (Regidx i1) (Regidx ird) op).
  unfold execute_ZBB_RTYPEW, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i2 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_CLMUL_total (i2 i1 ird : mword 5) (s : mstate) :
  exists v : mword 64,
    exec (execute (CLMUL (Regidx i2, Regidx i1, Regidx ird))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (CLMUL (Regidx i2, Regidx i1, Regidx ird)))
    with (execute_CLMUL (Regidx i2) (Regidx i1) (Regidx ird)).
  unfold execute_CLMUL, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i2 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_CLMULH_total (i2 i1 ird : mword 5) (s : mstate) :
  exists v : mword 64,
    exec (execute (CLMULH (Regidx i2, Regidx i1, Regidx ird))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (CLMULH (Regidx i2, Regidx i1, Regidx ird)))
    with (execute_CLMULH (Regidx i2) (Regidx i1) (Regidx ird)).
  unfold execute_CLMULH, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i2 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_CLMULR_total (i2 i1 ird : mword 5) (s : mstate) :
  exists v : mword 64,
    exec (execute (CLMULR (Regidx i2, Regidx i1, Regidx ird))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (CLMULR (Regidx i2, Regidx i1, Regidx ird)))
    with (execute_CLMULR (Regidx i2) (Regidx i1) (Regidx ird)).
  unfold execute_CLMULR, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i2 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_REV8_total (i1 ird : mword 5) (s : mstate) :
  exists v : mword 64,
    exec (execute (REV8 (Regidx i1, Regidx ird))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (REV8 (Regidx i1, Regidx ird)))
    with (execute_REV8 (Regidx i1) (Regidx ird)).
  unfold execute_REV8, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_RORI_total (shamt : mword 6) (i1 ird : mword 5) (s : mstate) :
  exists v : mword 64,
    exec (execute (RORI (shamt, Regidx i1, Regidx ird))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (RORI (shamt, Regidx i1, Regidx ird)))
    with (execute_RORI shamt (Regidx i1) (Regidx ird)).
  unfold execute_RORI, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_RORIW_total (shamt : mword 5) (i1 ird : mword 5) (s : mstate) :
  exists v : mword 64,
    exec (execute (RORIW (shamt, Regidx i1, Regidx ird))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (RORIW (shamt, Regidx i1, Regidx ird)))
    with (execute_RORIW shamt (Regidx i1) (Regidx ird)).
  unfold execute_RORIW, gpr_write_state.
  eexists.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i1 s) ]. cbn beta. cbv zeta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_ZIMOP_MOP_R_total (mop : mword 5) (i1 ird : mword 5) (s : mstate) :
  exists v : mword 64,
    exec (execute (ZIMOP_MOP_R (mop, Regidx i1, Regidx ird))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (ZIMOP_MOP_R (mop, Regidx i1, Regidx ird)))
    with (execute_ZIMOP_MOP_R mop (Regidx i1) (Regidx ird)).
  unfold execute_ZIMOP_MOP_R, gpr_write_state.
  eexists.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

Lemma exec_execute_ZIMOP_MOP_RR_total (mop : mword 3) (i2 i1 ird : mword 5) (s : mstate) :
  exists v : mword 64,
    exec (execute (ZIMOP_MOP_RR (mop, Regidx i2, Regidx i1, Regidx ird))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  change (execute (ZIMOP_MOP_RR (mop, Regidx i2, Regidx i1, Regidx ird)))
    with (execute_ZIMOP_MOP_RR mop (Regidx i2) (Regidx i1) (Regidx ird)).
  unfold execute_ZIMOP_MOP_RR, gpr_write_state.
  eexists.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr ird _ s) ].
Qed.

(* ZICOND: the write value depends on an abstract runtime condition;
   [exec_execute_ZICOND_RTYPE_gpr] (ZicondGpr.v) is already total and
   premise-free, so the totality form is a corollary. *)
Require Import ZicondGpr.

Lemma exec_execute_ZICOND_RTYPE_total (i2 i1 ird : mword 5)
    (op : zicondop) (s : mstate) :
  exists v : mword 64,
    exec (execute (ZICOND_RTYPE (Regidx i2, Regidx i1, Regidx ird, op))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v s).
Proof.
  eexists.
  change (execute (ZICOND_RTYPE (Regidx i2, Regidx i1, Regidx ird, op)))
    with (execute_ZICOND_RTYPE (Regidx i2) (Regidx i1) (Regidx ird) op).
  unfold gpr_write_state.
  apply exec_execute_ZICOND_RTYPE_gpr.
Qed.

(* ===================================================================== *)
(* The remaining compressed EXPANSION facts (decodable_c stragglers --    *)
(* WpMmodeLeafBase.v has the other ~20, operand-generic).  Each pure      *)
(* expansion is [returnM (ExecuteAs base)]; conversion unfolds the        *)
(* execute_C_* body and its lets, so [exec_returnm] closes them.          *)
(* C_NOT / C_ZEXT_B are DIRECT retires (monadic read/write, no            *)
(* redirection); C_NOP / C_NTL / ZCMOP / C_ILLEGAL are pure results.      *)
(* ===================================================================== *)

Lemma exec_execute_C_ADDW (rsd rs2 : cregidx) (s : mstate) :
  exec (execute (C_ADDW (rsd, rs2))) s
    = Some (ExecuteAs (RTYPEW (creg2reg_idx rs2, creg2reg_idx rsd,
                               creg2reg_idx rsd, ADDW)), s).
Proof. apply exec_returnm. Qed.

Lemma exec_execute_C_SUBW (rsd rs2 : cregidx) (s : mstate) :
  exec (execute (C_SUBW (rsd, rs2))) s
    = Some (ExecuteAs (RTYPEW (creg2reg_idx rs2, creg2reg_idx rsd,
                               creg2reg_idx rsd, SUBW)), s).
Proof. apply exec_returnm. Qed.

Lemma exec_execute_C_SUB (rsd rs2 : cregidx) (s : mstate) :
  exec (execute (C_SUB (rsd, rs2))) s
    = Some (ExecuteAs (RTYPE (creg2reg_idx rs2, creg2reg_idx rsd,
                              creg2reg_idx rsd, SUB)), s).
Proof. apply exec_returnm. Qed.

Lemma exec_execute_C_XOR (rsd rs2 : cregidx) (s : mstate) :
  exec (execute (C_XOR (rsd, rs2))) s
    = Some (ExecuteAs (RTYPE (creg2reg_idx rs2, creg2reg_idx rsd,
                              creg2reg_idx rsd, XOR)), s).
Proof. apply exec_returnm. Qed.

Lemma exec_execute_C_ANDI (imm : mword 6) (rsd : cregidx) (s : mstate) :
  exec (execute (C_ANDI (imm, rsd))) s
    = Some (ExecuteAs (ITYPE (sign_extend' 12 imm, creg2reg_idx rsd,
                              creg2reg_idx rsd, ANDI)), s).
Proof. apply exec_returnm. Qed.

Lemma exec_execute_C_SRAI (shamt : mword 6) (rsd : cregidx) (s : mstate) :
  exec (execute (C_SRAI (shamt, rsd))) s
    = Some (ExecuteAs (SHIFTIOP (shamt, creg2reg_idx rsd,
                                 creg2reg_idx rsd, SRAI)), s).
Proof. apply exec_returnm. Qed.

Lemma exec_execute_C_MUL (rsdc rsc2 : cregidx) (s : mstate) :
  exists mop,
    exec (execute (C_MUL (rsdc, rsc2))) s
      = Some (ExecuteAs (MUL (creg2reg_idx rsc2, creg2reg_idx rsdc,
                              creg2reg_idx rsdc, mop)), s).
Proof. eexists. apply exec_returnm. Qed.


Lemma exec_execute_C_EBREAK_U (s : mstate) :
  exec (execute (C_EBREAK tt)) s = Some (ExecuteAs (EBREAK tt), s).
Proof. apply exec_returnm. Qed.

Lemma exec_execute_C_ILLEGAL (w : mword 16) (s : mstate) :
  exec (execute (C_ILLEGAL w)) s = Some (Illegal_Instruction tt, s).
Proof. apply exec_returnm. Qed.

Lemma exec_execute_C_NOP (g : mword 6) (s : mstate) :
  exec (execute (C_NOP g)) s = Some (RETIRE_SUCCESS, s).
Proof. apply exec_returnm. Qed.

Lemma exec_execute_C_NTL (g : ntl_type) (s : mstate) :
  exec (execute (C_NTL g)) s = Some (RETIRE_SUCCESS, s).
Proof. apply exec_returnm. Qed.

Lemma exec_execute_ZCMOP (mop : mword 3) (s : mstate) :
  exec (execute (ZCMOP mop)) s = Some (RETIRE_SUCCESS, s).
Proof. apply exec_returnm. Qed.

(* the compressed memory expansions *)


(* C_NOT / C_ZEXT_B: DIRECT retires (read/write the same creg). *)
Lemma exec_execute_C_NOT_total (c : cregidx) (s : mstate) :
  exists (i : mword 5) (v : mword 64),
    creg2reg_idx c = Regidx i /\
    exec (execute (C_NOT c)) s = Some (RETIRE_SUCCESS, gpr_write_state i v s).
Proof.
  change (execute (C_NOT c)) with (execute_C_NOT c).
  unfold execute_C_NOT. cbv zeta.
  destruct (creg2reg_idx c) as [i] eqn:E.
  exists i. eexists. split; [ reflexivity | ].
  unfold gpr_write_state.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i s) ]. cbn beta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr i _ s) ].
Qed.

Lemma exec_execute_C_ZEXT_B_total (c : cregidx) (s : mstate) :
  exists (i : mword 5) (v : mword 64),
    creg2reg_idx c = Regidx i /\
    exec (execute (C_ZEXT_B c)) s = Some (RETIRE_SUCCESS, gpr_write_state i v s).
Proof.
  change (execute (C_ZEXT_B c)) with (execute_C_ZEXT_B c).
  unfold execute_C_ZEXT_B. cbv zeta.
  destruct (creg2reg_idx c) as [i] eqn:E.
  exists i. eexists. split; [ reflexivity | ].
  unfold gpr_write_state.
  erewrite exec_bind_Some; [ | apply (exec_rX_bits_gpr i s) ]. cbn beta.
  erewrite exec_bind0_Some;
    [ apply exec_returnm | apply (exec_wX_bits_gpr i _ s) ].
Qed.

(* ===================================================================== *)
(* Zicbom / Zicboz at User: ILLEGAL under the pinned configs.  MENVCFG_S  *)
(* has CBZE/CBCFE clear and CBIE = 00 (CBIE_ILLEGAL), so                  *)
(* [feature_enabled_for_priv] short-circuits on the machine-enable bit    *)
(* and [cbop_priv_check] returns CBOP_ILLEGAL from mCBIE alone; the       *)
(* senvcfg = 0 pin keeps [read_senvcfg]'s sCBIE decode off the reserved-  *)
(* encoding error.  (ZICBOP is NOT here: prefetch does a real             *)
(* translation -- ADUE-coupled.)                                          *)
(* ===================================================================== *)

Lemma exec_read_senvcfg_pinned (st : mstate) :
  register_lookup menvcfg st.(sregs) = MENVCFG_S ->
  register_lookup senvcfg st.(sregs) = (mword_of_int 0 : mword 64) ->
  exec (read_senvcfg tt) st
    = Some (_update_SEnvcfg_SSE (mword_of_int 0 : mword 64)
              (and_vec (_get_MEnvcfg_SSE MENVCFG_S)
                       (_get_SEnvcfg_SSE (mword_of_int 0 : mword 64))), st).
Proof.
  intros Hmenv Hsenv.
  unfold read_senvcfg.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg st)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg st)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg st)). cbn beta.
  rewrite Hmenv, Hsenv.
  apply exec_returnm.
Qed.

Lemma exec_feature_illegal_U (m s h : mword 1) (st : mstate) :
  eq_vec m ('b"1") = false ->
  exec (feature_enabled_for_priv User m s h) st = Some (FEATURE_ILLEGAL, st).
Proof.
  intro Hm.
  unfold feature_enabled_for_priv. cbn match.
  unfold and_boolM.
  erewrite exec_bind_Some.
  2:{ erewrite exec_bind_Some; [ | apply (exec_returnM (eq_vec m ('b"1")) st) ].
      cbn beta. rewrite Hm. cbn match. apply (exec_returnM false st). }
  cbn beta. cbv zeta. cbn match.
  apply exec_returnm.
Qed.

Lemma exec_execute_ZICBOZ_U (i1 : mword 5) (st : mstate) :
  register_lookup cur_privilege st.(sregs) = User ->
  register_lookup menvcfg st.(sregs) = MENVCFG_S ->
  register_lookup senvcfg st.(sregs) = (mword_of_int 0 : mword 64) ->
  exec (execute (ZICBOZ (Regidx i1))) st = Some (Illegal_Instruction tt, st).
Proof.
  intros Hpriv Hmenv Hsenv.
  change (execute (ZICBOZ (Regidx i1))) with (execute_ZICBOZ (Regidx i1)).
  unfold execute_ZICBOZ.
  rewrite exec_catch_early_return.
  rewrite execR_bind, execR_liftR, (exec_read_reg cur_privilege st), Hpriv. cbn match.
  assert (Hrdm : exec ((read_reg menvcfg) : M (mword 64)) st = Some (MENVCFG_S, st)).
  { etransitivity; [ exact (exec_read_reg menvcfg st) | rewrite Hmenv; reflexivity ]. }
  rewrite execR_bind, execR_liftR, Hrdm. cbn match.
  rewrite execR_bind, execR_liftR, (exec_read_senvcfg_pinned st Hmenv Hsenv). cbn match.
  rewrite execR_bind, execR_liftR.
  erewrite exec_feature_illegal_U. 2:{ vm_compute; reflexivity. }
  cbn match.
  rewrite execR_bind. rewrite execR_bind0.
  rewrite execR_early_return. cbn match.
  reflexivity.
Qed.

Lemma exec_execute_ZICBOM_U (op : cbop_zicbom) (i1 : mword 5) (st : mstate) :
  register_lookup cur_privilege st.(sregs) = User ->
  register_lookup menvcfg st.(sregs) = MENVCFG_S ->
  register_lookup senvcfg st.(sregs) = (mword_of_int 0 : mword 64) ->
  exec (currentlyEnabled Ext_S) st = Some (true, st) ->
  exec (execute (ZICBOM (op, Regidx i1))) st = Some (Illegal_Instruction tt, st).
Proof.
  intros Hpriv Hmenv Hsenv HES.
  change (execute (ZICBOM (op, Regidx i1))) with (execute_ZICBOM op (Regidx i1)).
  unfold execute_ZICBOM. cbv zeta.
  destruct op.
  - (* CBO_CLEAN: CBCFE gate *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege st)). cbn beta.
    rewrite Hpriv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg st)). cbn beta.
    rewrite Hmenv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_senvcfg_pinned st Hmenv Hsenv)). cbn beta.
    erewrite exec_bind_Some.
    2:{ apply exec_feature_illegal_U. vm_compute; reflexivity. }
    cbn beta. cbn match. apply exec_returnm.
  - (* CBO_FLUSH: CBCFE gate *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege st)). cbn beta.
    rewrite Hpriv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg st)). cbn beta.
    rewrite Hmenv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_senvcfg_pinned st Hmenv Hsenv)). cbn beta.
    erewrite exec_bind_Some.
    2:{ apply exec_feature_illegal_U. vm_compute; reflexivity. }
    cbn beta. cbn match. apply exec_returnm.
  - (* CBO_INVAL: cbop_priv_check, CBOP_ILLEGAL from mCBIE = 00 *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege st)). cbn beta.
    rewrite Hpriv.
    erewrite exec_bind_Some.
    2:{ unfold cbop_priv_check.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg st)). cbn beta.
        rewrite Hmenv.
        erewrite exec_bind_Some.
        2:{ unfold encdec_cbie_backwards. cbv zeta.
            replace (eq_vec (_get_MEnvcfg_CBIE MENVCFG_S) ('b"00")) with true
              by (vm_compute; reflexivity).
            cbn match. apply (exec_returnM CBIE_ILLEGAL st). }
        cbn beta.
        rewrite (exec_bind_Some _ _ _ _ _ HES). cbn beta. cbn match.
        erewrite exec_bind_Some.
        2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_senvcfg_pinned st Hmenv Hsenv)).
            cbn beta.
            unfold encdec_cbie_backwards. cbv zeta.
            match goal with
            | |- exec (if ?g then _ else _) _ = _ =>
                replace g with true by (vm_compute; reflexivity)
            end.
            cbn match. apply (exec_returnM CBIE_ILLEGAL st). }
        cbn beta. cbn match.
        apply (exec_returnM CBOP_ILLEGAL st). }
    cbn beta. cbn match.
    apply exec_returnm.
Qed.

(* SSAMOSWAP (Zicfiss shadow-stack swap): ILLEGAL at User under the pins --
   the xSSE gate reads senvcfg.SSE, which the [read_senvcfg] composite pins
   to 0 (menvcfg.SSE ∧ senvcfg.SSE with senvcfg = 0). *)
Lemma exec_execute_SSAMOSWAP_U (aq rl : bool) (i2 i1 ird : mword 5)
    (width : Z) (st : mstate) :
  register_lookup cur_privilege st.(sregs) = User ->
  register_lookup menvcfg st.(sregs) = MENVCFG_S ->
  register_lookup senvcfg st.(sregs) = (mword_of_int 0 : mword 64) ->
  exec (currentlyEnabled Ext_S) st = Some (true, st) ->
  exec (execute (SSAMOSWAP (aq, rl, Regidx i2, Regidx i1, width, Regidx ird))) st
    = Some (Illegal_Instruction tt, st).
Proof.
  intros Hpriv Hmenv Hsenv HES.
  change (execute (SSAMOSWAP (aq, rl, Regidx i2, Regidx i1, width, Regidx ird)))
    with (execute_SSAMOSWAP aq rl (Regidx i2) (Regidx i1) width (Regidx ird)).
  unfold execute_SSAMOSWAP.
  rewrite exec_catch_early_return.
  rewrite execR_bind, execR_liftR, (exec_read_reg cur_privilege st), Hpriv. cbn match.
  cbv beta iota.
  rewrite execR_bind0.
  rewrite execR_bind.
  unfold or_boolM.
  rewrite execR_bind.
  rewrite execR_bind, execR_liftR, HES. cbn match.
  rewrite execR_returnR. cbn [not negb]. cbn match.
  rewrite execR_bind, execR_liftR, (exec_read_senvcfg_pinned st Hmenv Hsenv). cbn match.
  rewrite execR_returnR. cbn match.
  match goal with
  | |- context [ if ?g then _ else _ ] =>
      replace g with true by (vm_compute; reflexivity)
  end.
  cbn match.
  rewrite execR_early_return. cbn match.
  reflexivity.
Qed.
