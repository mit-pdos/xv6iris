(* ===================================================================== *)
(* USyncKernel.v -- THE `sync` PROGRAM'S WHOLE-PROCESS WP AS A CONSTRUCTOR  *)
(* OF THE TRAPFRAME-KEYED SLOT: the ENTRY DEPOSIT, with NO assumption.      *)
(*                                                                         *)
(* See claude-notes/design/user-wp-slot.md (the step-2 layer, as re-cut on  *)
(* the user-mode-on-kernel engine) and claude-notes/design/uk-engine.md.    *)
(* [UkSync.wp_ksync_start] is sync's top-level theorem on the new engine:   *)
(* a U-mode continuation [ukc π M m start] from pure facts about the KEY   *)
(* alone -- the text present in the image, page 0 an X page of the         *)
(* permission map, a 32-byte writable stack budget below sp.  [uslot W] is  *)
(* that continuation at the key's state ([UexecRet.uslot_ukc]), so this     *)
(* file is the one-line identification.                                     *)
(*                                                                         *)
(* THE ENTRY CONDITIONS are the pure facts an INITIALIZER (exec, forkret's  *)
(* park) establishes when it writes the trapframe and loads the image,      *)
(* spelled against the SLOT's own vocabulary:                               *)
(*                                                                         *)
(*   Hentry  tf_resume_pc (uvis_tf W) = SyncSyms.start   -- the resume pc   *)
(*   Htext   uimg_sub SyncInstrs.sync_bytes (uvis_M W)   -- the image       *)
(*   Hx      uk_xpage (uvis_perm W) 0                    -- page 0 is X      *)
(*   Hst     uk_stack (uvis_perm W) (uvis_M W) sp 32     -- the stack budget *)
(*                                                                         *)
(* at [sp = tf_w (uvis_tf W) tf_sp_idx]; [wp_ksync_start]'s [Hsp] is        *)
(* DISCHARGED by [tf_resume_gpr_sp] -- the payoff of trapframe keying.      *)
(* Every one of the four is DECIDABLE (UexecCond.v decides them), and none  *)
(* mentions a table: the ∀-bound table inside the slot is met by the        *)
(* program through UserPerm.v's leaf-bit transfers.  The former            *)
(* [sync_entry_tbl] (a guard at EVERY [loop_ok] table, refuted by           *)
(* [UexecCond.sync_entry_tbl_refuted]) and the [uv_cap] assumption are     *)
(* gone: the kernel's own trap contract ([UexecRet.ukont]) is what the      *)
(* program's traps go through.                                             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import ProcGeom ProcDefs UserPtTree.
Require Import UserExec.
Require Import UmodeAbi.
Require Import UCodeSync.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UkStep UkSync.
Require User.SyncSyms User.SyncInstrs.
Local Open Scope Z_scope.
Import Defs.

Section USyncKernel.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  (* NO [Context {CID : CpuId}]: the slot binds the hart itself. *)

  Lemma sync_uexec_slot (W : uvis) :
    tf_resume_pc (uvis_tf W) = (mword_of_int SyncSyms.start : mword 64) ->
    uimg_sub SyncInstrs.sync_bytes (uvis_M W) ->
    uk_xpage (uvis_perm W) (mword_of_int 0) ->
    uk_stack (uvis_perm W) (uvis_M W) (tf_w (uvis_tf W) tf_sp_idx) 32 ->
    ⊢ uslot W.
  Proof.
    intros Hentry Htext Hx Hst.
    rewrite uslot_ukc Hentry.
    iApply (wp_ksync_start (uvis_perm W) (uvis_M W) (tf_resume_gpr0 (uvis_tf W))
              (tf_w (uvis_tf W) tf_sp_idx) Hx Htext
              (tf_resume_gpr_sp zero_rf (uvis_tf W)) Hst).
  Qed.

End USyncKernel.
