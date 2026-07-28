(* ===================================================================== *)
(* ProofUser.v -- CLOSE the user-mode execution WP, and seal it behind     *)
(* [SpecUser.USER].                                                        *)
(*                                                                         *)
(* Instantiates the two execute totalities (base_exec_total_u_holds /      *)
(* rvc_exec_total_u_holds, UserTotalU.v) with the 19 PROVEN memory arms     *)
(* (UserMemClassify.v): the 6 base (LOAD/STORE/AMO/LOADRES/STORECON/ZICBOP) *)
(* and the 13 compressed (C_LW..C_SH).  The two totalities then hold        *)
(* UNCONDITIONALLY, discharging wp_user_exec_full's Hbase/Hrvc into the     *)
(* final closed safety theorem [wp_user_exec_closed] -- no totality         *)
(* hypotheses, axiom-clean beyond the 5 baseline platform stubs.           *)
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
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import MinstretInv WireInv RegFile.
Require Import UserPtTree UserExec UserClassifyAsm.
Require Import UserTotalU UserMemClassify UserActiveClass.
Require Import SpecUser.
Local Open Scope Z_scope.
Import Defs.

Module UserProof : USER.

Section ProofUser.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* The base execute totality, closed by instantiating the 6 base memory
     Variables with their proven arms. *)
  Lemma base_exec_total_u_closed (E : coPset) (sigma : mstate) (va : mword 64)
      (g : regfile) :
    ⊢ base_exec_total_u C pt E sigma va g.
  Proof.
    apply (base_exec_total_u_holds C pt
             (arm_LOAD_u C pt) (arm_STORE_u C pt) (arm_AMO_u C pt)
             (arm_LOADRES_u C pt) (arm_STORECON_u C pt) (arm_ZICBOP_u C pt)).
  Qed.

  (* The compressed execute totality, closed by instantiating the 13
     compressed memory Variables with their proven arms. *)
  Lemma rvc_exec_total_u_closed (E : coPset) (sigma : mstate) (va : mword 64)
      (g : regfile) :
    ⊢ rvc_exec_total_u C pt E sigma va g.
  Proof.
    apply (rvc_exec_total_u_holds C pt
             (arm_C_LW_u C pt) (arm_C_LD_u C pt) (arm_C_LWSP_u C pt) (arm_C_LDSP_u C pt)
             (arm_C_SW_u C pt) (arm_C_SD_u C pt) (arm_C_SWSP_u C pt) (arm_C_SDSP_u C pt)
             (arm_C_LBU_u C pt) (arm_C_LH_u C pt) (arm_C_LHU_u C pt)
             (arm_C_SB_u C pt) (arm_C_SH_u C pt)).
  Qed.

  (* THE FINAL THEOREM: safety of arbitrary user-mode execution, with NO
     totality hypotheses -- the two totalities are now unconditional. *)
  Theorem wp_user_exec_closed (Φ : mval -> iProp Σ) :
    wp_user_exec_closed_body C pt Φ.
  Proof.
    cbv beta delta [wp_user_exec_closed_body].
    apply (wp_user_exec_full C pt Φ
             base_exec_total_u_closed rvc_exec_total_u_closed).
  Qed.

End ProofUser.

End UserProof.
