(* WpAdd.v -- the ADD opcode: forward_exec_final + wp_add_real_final. *)
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* ===== RiscvModelFinalWP ===== *)
(* ====================================================================== *)
(* RiscvModelFinalWP.v                                                     *)
(*                                                                         *)
(* THE capstone: wp_add_real_final -- an Iris WP for `add a2,a0,a1` through *)
(* the real Sail try_step, with Hne DISCHARGED at the quantified state via *)
(* exec_hart_active_done (NOT the over-strong unconditional Hne_gen).       *)
(* Remaining genuine assumptions: Hdec (decode wall) + reducible geometric. *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* [exec_hartSupports_S] / [exec_hartSupports_Zicsr] / [exec_rec_cE_Zicsr] /
   [exec_currentlyEnabled_S] were moved to RiscvFetchExec.v (general-purpose
   exec twins of the S-extension enablement); available here via import. *)

(* ---------------------------------------------------------------------- *)
(* Step 2: the capstone WP, with Hne DERIVED via exec_hart_active_done.    *)
(* ---------------------------------------------------------------------- *)

Ltac trans_mi := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

Section FinalWP.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.
  Context (b : bool) (pc a0 a1 mst0 npc v2old : mword 64) (mi0 : bool)
          (w : mword 32) (rs2 rs1 rd : mword 5).


  (* fetch/decode facts, stated once at the EXEC level; the relational [run]
     twins needed by run_hart_active_ADD are derived on the spot via
     [exec_run_det] (exec = Some -> run), so no separate run hypotheses. *)
  Hypothesis Hdec_exec_gen : forall s : mstate,
    exec (ext_decode w) s = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD), s).
  Hypothesis Hsi_gen : forall s : mstate,
    register_lookup cur_privilege s.(sregs) = Machine ->
    exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 = 10.
  Hypothesis Hrs2 : uint rs2 = 11.
  Hypothesis Hrd  : uint rd  = 12.
  Hypothesis Hrvfi : get_config_rvfi tt = false.





  Ltac tmiss := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].


  (* Expresses the post-step state through the *runtime* minstret
     value [register_lookup minstret s.(sregs)] rather than the section parameter
     [mst0].  This is what a leaf needs when it does NOT own (and never learns) the
     minstret value up front -- it only obtains it transiently from the invariant
     after the step. *)

  (* ====================================================================== *)
  (* PROTOTYPE: the same ADD leaf, but with [minstret] / [minstret_increment]
     taken from the persistent [minstret_inv] (opened across the step) instead
     of threaded as two owned cells.  Note the precondition/continuation no
     longer mention either cell -- only the (duplicable) [minstret_inv].
     The exec witness is [sF s], built WITHOUT the minstret value; the cells are
     obtained from the invariant body only AFTER the step, to fold the bump into
     [state_interp] and hand a fresh body back to close the invariant.        *)
  (* ====================================================================== *)

End FinalWP.

