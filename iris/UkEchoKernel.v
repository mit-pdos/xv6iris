(* ===================================================================== *)
(* UkEchoKernel.v -- THE `echo` PROGRAM'S WHOLE-PROCESS WP AS A            *)
(* CONSTRUCTOR OF THE TRAPFRAME-KEYED SLOT: the ENTRY DEPOSIT, with NO     *)
(* assumption.  USyncKernel.v is the same file one program smaller.        *)
(*                                                                        *)
(* [UkEcho.wp_kecho_start] is echo's top-level theorem on the             *)
(* user-mode-on-kernel engine: a U-mode continuation [ukc π M m start]     *)
(* from pure facts about the KEY alone.  [uslot W] is that continuation    *)
(* at the key's state ([UexecRet.uslot_ukc]), so this file is the          *)
(* identification -- one [rewrite] and one [iApply].                       *)
(*                                                                        *)
(* THE ENTRY CONDITIONS are the pure facts an INITIALIZER (exec) is        *)
(* supposed to establish when it writes the trapframe and loads the        *)
(* image, spelled against the SLOT's own vocabulary:                       *)
(*                                                                        *)
(*   Hentry  tf_resume_pc (uvis_tf W) = EchoSyms.start   -- the resume pc  *)
(*   Htext   uimg_sub EchoInstrs.echo_bytes (uvis_M W)   -- the image      *)
(*   Hx      uk_xpage (uvis_perm W) 0                    -- page 0 is X    *)
(*   Hst     uk_stack (uvis_perm W) (uvis_M W) sp 96     -- the budget     *)
(*   Hargs   uk_args (uvis_perm W) (uvis_M W) av argc (uint sp) alen       *)
(*                                                       -- the argv area  *)
(*                                                                        *)
(* THE ARGUMENTS COME OFF THE TRAPFRAME, and that is the whole difference  *)
(* from sync.  [sp], [argc] and [av] are the words [tf_sp_idx],            *)
(* [tf_arg_idx 0] and [tf_arg_idx 1], read back out of [userret_gpr]'s     *)
(* insert tower by UexecSlot.v's three peel lemmas -- so [wp_kecho_start]'s *)
(* register premises are DISCHARGED rather than assumed, which is the      *)
(* payoff of keying the slot on the trapframe.  Every condition above is a *)
(* fact about the key, every one is DECIDABLE (UexecCond.v decides them),  *)
(* and none mentions a table: the ∀-bound table inside the slot is met by  *)
(* the program through UserPerm.v's leaf-bit transfers.                    *)
(*                                                                        *)
(* [alen] IS A PARAMETER HERE and is chosen at the gate.  UkAbi.v §3's     *)
(* [uk_args_c] is [uk_args] at the CANONICAL lengths (scan for the first   *)
(* NUL), and [uk_args_canon] says every instance of the parametric form    *)
(* implies the canonical one -- so a gate decides the canonical form and   *)
(* hands it here as the witness, losing nothing.                           *)
(*                                                                        *)
(* WHAT THIS DOES NOT CLAIM.  Safety, exactly as sync has it.  It does NOT *)
(* say echo's output bytes are its argv strings; see UkEcho.v's header for *)
(* why the contract has no place for that today and where the hook is.     *)
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
Require Import ProcGeom.
Require Import UmodeArith UmodeAbi.
Require Import UexecSlot UexecRet.
Require Import UkAbi UkEcho.
Require Import TsoCtx.   (* [CurCtx]: ambient, per the WpUmode*/Uk* precedent *)
Require User.EchoSyms User.EchoInstrs.
Local Open Scope Z_scope.
Import Defs.

Section UkEchoKernel.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.

  (* NO [Context {CID : CpuId}]: the slot binds the hart itself. *)

  Lemma echo_uexec_slot (W : uvis) (alen : Z -> Z) :
    tf_resume_pc (uvis_tf W) = (mword_of_int EchoSyms.start : mword 64) ->
    uimg_sub EchoInstrs.echo_bytes (uvis_M W) ->
    uk_xpage (uvis_perm W) (mword_of_int 0) ->
    uk_stack (uvis_perm W) (uvis_M W) (tf_w (uvis_tf W) tf_sp_idx) 96 ->
    uk_args (uvis_perm W) (uvis_M W)
      (uint (tf_w (uvis_tf W) (tf_arg_idx 1)))
      (uint (tf_w (uvis_tf W) (tf_arg_idx 0)))
      (uint (tf_w (uvis_tf W) tf_sp_idx)) alen ->
    ⊢ uslot W.
  Proof.
    intros Hentry Htext Hx Hst Hargs.
    rewrite uslot_ukc Hentry.
    iApply (wp_kecho_start (uvis_perm W) (uvis_M W) (tf_resume_gpr0 (uvis_tf W))
              (tf_w (uvis_tf W) tf_sp_idx)
              (uint (tf_w (uvis_tf W) (tf_arg_idx 0)))
              (uint (tf_w (uvis_tf W) (tf_arg_idx 1))) alen
              Hx Htext
              (tf_resume_gpr_sp zero_rf (uvis_tf W)) Hst
              ltac:(rewrite moi_of_uint;
                    exact (tf_resume_gpr_a0 zero_rf (uvis_tf W)))
              ltac:(rewrite moi_of_uint;
                    exact (tf_resume_gpr_a1 zero_rf (uvis_tf W)))
              Hargs).
  Qed.

End UkEchoKernel.
