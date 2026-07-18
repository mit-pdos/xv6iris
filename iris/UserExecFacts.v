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
Require Import WpLeafCommon.

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
  (forall t : mword 64,
     eq_vec (access_vec_dec (update_vec_dec t 0 ('b"0")) 0) ('b"0") = true) ->
  exists (v tgt : mword 64),
    exec (execute (JALR (imm, Regidx i1, Regidx ird))) s
      = Some (RETIRE_SUCCESS, gpr_write_state ird v (set_reg s nextPC tgt)).
Proof.
  intros Hzic Hzca Hbit0.
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
