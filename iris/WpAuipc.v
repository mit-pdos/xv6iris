(* WpAuipc.v -- the AUIPC opcode: execute reduction, forward_exec_auipc, wp_step_auipc. *)
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.


Lemma exec_get_arch_pc s :
  exec (get_arch_pc tt) s = Some (register_lookup PC s.(sregs), s).
Proof. unfold get_arch_pc. exact (exec_read_reg PC s). Qed.

(* --- execute (UTYPE imm rd AUIPC): read PC, add imm<<12, write rd, retire. --- *)
Definition auipc_off (imm : mword 20) : mword 64 :=
  sign_extend' 64 (concat_vec imm (Ox"000")).

Lemma exec_execute_UTYPE_AUIPC (i : mword 5) (imm : mword 20) s :
  uint i = 2 ->
  exec (execute_UTYPE imm (Regidx i) AUIPC) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 x2)
            (regval_into_reg
               (add_vec (register_lookup PC s.(sregs)) (auipc_off imm)))).
Proof.
  intro Hi.
  unfold execute_UTYPE, auipc_off. cbn match.
  rewrite (exec_bind_Some _ _ _
             (add_vec (register_lookup PC s.(sregs))
                      (sign_extend' 64 (concat_vec imm (Ox"000")))) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_get_arch_pc s)). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_x2 i s _ Hi)). apply exec_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* forward_exec_auipc: thread the generic try_step wrapper + the generic    *)
(* run_hart_active progress engine around the AUIPC execute leaf.           *)
(* Hypotheses mirror forward_exec_final's: universally-quantified fetch /    *)
(* decode / should_inc facts + booting-Machine register conditions.         *)
(* ---------------------------------------------------------------------- *)

Section ForwardAUIPC.
  Context (s : mstate) (w : mword 32) (pc : mword 64) (imm : mword 20)
          (i : mword 5) (b : bool).

  Hypothesis Hi : uint i = 2.
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hdec_gen : forall s0 : mstate,
    register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (UTYPE (imm, Regidx i, AUIPC), s0).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).

  Definition sAa : mstate := set_reg s (R_bool minstret_increment) b.
  Definition sXa : mstate :=
    let s1 := set_reg sAa nextPC (add_vec_int pc 4) in
    set_reg s1 (R_bitvector_64 x2)
      (regval_into_reg (add_vec (register_lookup PC s1.(sregs)) (auipc_off imm))).
  Definition sTa : mstate := set_reg sXa PC (register_lookup nextPC sXa.(sregs)).
  Definition sFa : mstate :=
    if b then set_reg sTa minstret
                  (add_vec_int (register_lookup minstret sTa.(sregs)) 1)
         else sTa.


  (* clean-form post-state (concrete values). *)
  Variable mst0 : mword 64.
  Hypothesis Lmst_a : register_lookup minstret s.(sregs) = mst0.

  Definition base_upd_a : mstate :=
    set_reg (set_reg (set_reg (set_reg s (R_bool minstret_increment) b)
                              nextPC (add_vec_int pc 4))
                     (R_bitvector_64 x2) (regval_into_reg (add_vec pc (auipc_off imm))))
            PC (add_vec_int pc 4).
  Definition sFca : mstate :=
    if b then set_reg base_upd_a minstret (add_vec_int mst0 1)
         else base_upd_a.

  Ltac tmiss := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].


End ForwardAUIPC.

Section StepAUIPC.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.

  (* ---------------------------------------------------------------------- *)
  (* Single-step WP for `ld rd,imm(rs1)` (rs1=rd=x2), via wp_exec_step +     *)
  (* forward_exec_ld + sFl_eq, discharging Hexec_spc via exec_execute_LOAD_8.*)
  (* ---------------------------------------------------------------------- *)
End StepAUIPC.
