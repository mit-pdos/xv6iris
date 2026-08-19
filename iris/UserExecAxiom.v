(* ===================================================================== *)
(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
(* !!  UserExecAxiom.v -- A USER-RULED **TEMPORARY AXIOM** (2026-08-19) !! *)
(* !!  THIS FILE ASSUMES THE GENERAL-CASE USER-MODE SAFETY THEOREM.     !! *)
(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
(*                                                                         *)
(* WHAT THIS IS.  [SpecUser.USER] -- the public interface of arbitrary      *)
(* user-mode execution -- is PROVEN, in [ProofUser.v], on top of the whole  *)
(* ~24 kLOC User*.v tower.  That proof is NOT YET PORTED onto the per-node  *)
(* (expression-resident monad) semantics of branch `hart-node-port`, and    *)
(* [ProofUser.v] is the last red root of the port that has a lane still in  *)
(* flight.  To let the port LAND ON MAIN sooner rather than later, the      *)
(* project owner RULED (2026-08-19) that:                                   *)
(*                                                                         *)
(*   * the ProofUser stack is temporarily removed from the build            *)
(*     (its rows are commented out of iris/_CoqProject -- the files stay    *)
(*     ON DISK, untouched, and the pre-port proof is intact in git), and     *)
(*   * its ONE dependency -- the userret link files, where the trap loop    *)
(*     is closed against the general-case user WP -- is stated as an        *)
(*     AXIOM instead, namely the module below.                              *)
(*                                                                         *)
(* SO: EVERY THEOREM ABOVE LinkUserretClosed.v / LinkUserretUser.v NOW      *)
(* CARRIES THIS ASSUMPTION.  As of 2026-08-19 that is exactly five          *)
(* theorems -- LinkUserretClosed's [wp_userret_closed], LinkUserretUser's   *)
(* [wp_userret_user], and the three forkret links above them (LinkForkret,  *)
(* LinkForkretNF, LinkForkretParkPaid).  It does NOT reach LinkMain /       *)
(* BootChain / SystemAdequacy, which do not depend on the closed trap loop. *)
(* It is NOT a new mathematical assumption about the machine: the statement *)
(* is exactly the theorem [ProofUser.UserProof.wp_user_exec_closed] proves  *)
(* today, character for character (both are [USER]'s single Parameter, over *)
(* [SpecUser.wp_user_exec_closed_body]).  It is an assumption only about    *)
(* THE PORT, and it is scheduled to be discharged, not to be lived with.    *)
(*                                                                         *)
(* THE DISCHARGE IS IN FLIGHT.  claude-notes/projects/user-tier-port.md     *)
(* ("THE USER-EXEC AXIOM" section) is the lane; §5.5 is its success         *)
(* criterion, which is precisely "ProofUser.wp_user_exec_closed compiles".  *)
(*                                                                         *)
(* THE REVIVAL PROCEDURE, when that lane closes -- three steps, no proof    *)
(* work anywhere else in the tree:                                          *)
(*                                                                         *)
(*   1. UNCOMMENT the "USER-RULED TEMPORARY DESCOPE (2026-08-19)" block in  *)
(*      iris/_CoqProject (ProofUser.v, UserActiveClass.v), and DELETE the   *)
(*      UserExecAxiom.v row.                                                 *)
(*   2. In iris/LinkUserretClosed.v and iris/LinkUserretUser.v, put         *)
(*      [ProofUser] back in the Require line (in place of [UserExecAxiom])  *)
(*      and rename the functor argument                                      *)
(*      [UserProof_USER_RULED_TEMPORARY_AXIOM] back to [UserProof].         *)
(*      Nothing else in those two files moves.                              *)
(*   3. DELETE THIS FILE.                                                    *)
(*                                                                          *)
(* The check that step 3 really happened is `Print Assumptions` on          *)
(* SpecUserretClosed's theorem: this axiom must disappear from the          *)
(* assumption set, leaving only the documented platform baseline.           *)
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
Require Import UserPtTree UserExec.
Require Import SpecUser.
Local Open Scope Z_scope.
Import Defs.

(* The axiomatised stand-in for [ProofUser.UserProof].  Named to scream at
   every use site and in every `Print Assumptions` output.

   An [Axiom] INSIDE the module, not `Declare Module … : USER.` -- the short
   form works and Print Assumptions reports it, but tools/proof_coverage.py
   finds assumptions by scanning for the keyword and would silently drop it
   from the coverage report (claude-notes/design/spec-modules.md, "An ASSUMED
   callee").  The binder list is restated here, as that section requires; the
   STATEMENT itself still lives once, in SpecUser.wp_user_exec_closed_body. *)
Module UserProof_USER_RULED_TEMPORARY_AXIOM : USER.

  Axiom wp_user_exec_closed_USER_RULED_TEMPORARY_AXIOM :
    forall `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId}
      (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ),
      wp_user_exec_closed_body C pt Rut.

  Definition wp_user_exec_closed := @wp_user_exec_closed_USER_RULED_TEMPORARY_AXIOM.

End UserProof_USER_RULED_TEMPORARY_AXIOM.
