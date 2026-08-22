(* WpAuipc.v -- the AUIPC opcode: execute reduction, forward_exec_auipc, wp_step_auipc. *)
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.


Lemma exec_get_arch_pc s :
  exec (get_arch_pc tt) s = Some (register_lookup PC s.(sregs), s).
Proof. unfold get_arch_pc. exact (exec_read_reg PC s). Qed.

(* --- execute (UTYPE imm rd AUIPC): read PC, add imm<<12, write rd, retire. ---
   [auipc_off] itself is pure bit-shuffling and lives in RiscvExtras.v. *)

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



  (* clean-form post-state (concrete values). *)
  Variable mst0 : mword 64.
  Hypothesis Lmst_a : register_lookup minstret s.(sregs) = mst0.


  Ltac tmiss := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].


End ForwardAUIPC.

Section StepAUIPC.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {dqc : dfrac}.

  (* ---------------------------------------------------------------------- *)
  (* Single-step WP for `ld rd,imm(rs1)` (rs1=rd=x2), via wp_exec_step +     *)
  (* forward_exec_ld + sFl_eq, discharging Hexec_spc via exec_execute_LOAD_8.*)
  (* ---------------------------------------------------------------------- *)
End StepAUIPC.
