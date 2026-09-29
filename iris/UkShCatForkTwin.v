(* ===================================================================== *)
(*  UkShCatForkTwin.v -- THE [cat f] BODY AT THE WIDENED CREDENTIAL       *)
(*  (cut C9f1; design: claude-notes/design/union.md section 3,            *)
(*  'Dispatch').                                                           *)
(*                                                                        *)
(*  [UkShRedirBody.wp_kshm_body_cat] is the [cd] test's two instructions  *)
(*  in front of the fork, and its ONE fork call is a parameter            *)
(*  ([UkShRedirBody.kshf_fork_law], [wp_kshm_body_ca_with]).  This file   *)
(*  is that law at the pipe era's fork twin                               *)
(*  [UkShPipeForkTwin.wp_kshf_fork_pipe], whose credential need not be    *)
(*  timeless -- the union's widened credential is not.  The cat body      *)
(*  walk at it is [UkShShape.ushf_body_law_of_mod]'s [HeadCA] arm         *)
(*  (design/shape-modules.md); the per-shape wrappers that used to live   *)
(*  here went with the round's dispatch.                                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import UkRun.
Require Import UserFd.
Require Import UkShPipeForkTwin.
Require Import UkShRedirBody.
Require Import CtxIdDefs.
Require Import UexecSG.
Require Import Xv6Cameras.
Local Open Scope Z_scope.
Import Defs.

Section UkShCatForkTwin.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Context `{!uartGhostG Σ}.
  Context (γp : gname).
  Context (T : iProp Σ).
  Context `{HT : !Persistent T}.
  Context (Wc : list (bv 8) -> nat -> iProp Σ).
  Context (Wb : list (bv 8) -> iProp Σ).
  Context (Pm : list (bv 8) -> iProp Σ).
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  (* the pipe era's fork twin IS the fork law *)
  Lemma kshf_fork_law_pipe : UkShRedirBody.kshf_fork_law N γp T Wc Wb Pm.
  Proof using HT Hpay Hpsok_free.
    exact (UkShPipeForkTwin.wp_kshf_fork_pipe N γp T Wc Wb Pm Hpsok_free).
  Qed.


End UkShCatForkTwin.
