(* ===================================================================== *)
(* ProofUser.v -- CLOSE the user-mode execution WP, and seal it behind     *)
(* [SpecUser.USER].                                                        *)
(*                                                                         *)
(* Instantiates the two execute totalities (base_exec_total_u_holds /      *)
(* rvc_exec_total_u_holds, UserTotalU.v) with the 19 PROVEN memory arms:    *)
(* the 6 base (LOAD/STORE from UserMemArmsBase, LOADRES/STORECON/AMO from   *)
(* UserMemArmsA, ZICBOP from UserMemClassifyAmo) and the 13 compressed      *)
(* (C_LW..C_SH, UserMemArmsC).  Both totalities are PURE now -- the port    *)
(* moved the whole classification below Iris -- so they hold               *)
(* UNCONDITIONALLY as Coq propositions, discharging wp_user_exec_full's     *)
(* Hbase/Hrvc into the final closed safety theorem [wp_user_exec_closed]:   *)
(* no totality hypotheses, axiom-clean beyond the 5 baseline platform       *)
(* stubs and the two reservation-term axioms.                              *)
(*                                                                         *)
(* This is the ONLY file where the user-mode interface meets the whole      *)
(* User*.v proof tower: [UserProof] is sealed by [USER], so a consumer      *)
(* requires SpecUser.v (cheap) and takes a [USER] functor argument rather   *)
(* than pulling the tower into its own build path.                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import UserPtTree UserExec UserClassifyAsm.
Require Import UserTotalU UserActiveClass.
Require Import UserMemArmsBase UserMemArmsC UserMemArmsA UserMemClassifyAmo.
Require Import SpecUser.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Module UserProof : USER.

Section ProofUser.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd).
  Context (Rut : uptd -> iProp Σ).

  (* The base execute totality, closed by instantiating the 6 base memory
     Variables with their proven arms.  PURE: no [C], no mask, no state. *)
  Lemma base_exec_total_u_closed (va : mword 64) (mi : bool) :
    base_exec_total_u pt va mi.
  Proof.
    apply (base_exec_total_u_holds pt
             (arm_LOAD_u pt) (arm_STORE_u pt) (arm_AMO_u pt)
             (arm_LOADRES_u pt) (arm_STORECON_u pt) (arm_ZICBOP_u pt)).
  Qed.

  (* The compressed execute totality, closed by instantiating the 13
     compressed memory Variables with their proven arms. *)
  Lemma rvc_exec_total_u_closed (va : mword 64) (mi : bool) :
    rvc_exec_total_u pt va mi.
  Proof.
    apply (rvc_exec_total_u_holds pt
             (arm_C_LW_u pt) (arm_C_LD_u pt) (arm_C_LWSP_u pt) (arm_C_LDSP_u pt)
             (arm_C_SW_u pt) (arm_C_SD_u pt) (arm_C_SWSP_u pt) (arm_C_SDSP_u pt)
             (arm_C_LBU_u pt) (arm_C_LH_u pt) (arm_C_LHU_u pt)
             (arm_C_SB_u pt) (arm_C_SH_u pt)).
  Qed.

  (* THE FINAL THEOREM: safety of arbitrary user-mode execution, with NO
     totality hypotheses -- the two totalities are now unconditional. *)
  Theorem wp_user_exec_closed :
    wp_user_exec_closed_body C pt Rut.
  Proof.
    cbv beta delta [wp_user_exec_closed_body].
    apply (wp_user_exec_full C pt Rut
             base_exec_total_u_closed rvc_exec_total_u_closed).
  Qed.

End ProofUser.

End UserProof.
