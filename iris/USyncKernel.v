(* ===================================================================== *)
(* USyncKernel.v -- THE `sync` PROGRAM'S WHOLE-PROCESS WP AS A CONSTRUCTOR  *)
(* OF THE TRAPFRAME-KEYED SLOT: the ENTRY DEPOSIT.                         *)
(*                                                                         *)
(* See claude-notes/projects/user-wp-slot.md SS3 (step 2).  [UProofSync.   *)
(* wp_sync_start] is stated in the Umode tier's vocabulary ([uv_cap_gpr] +  *)
(* [pc_is]); the kernel's trap loop holds [uexec_slot V M].  This file is   *)
(* the one lemma that says those are THE SAME THEOREM at the right         *)
(* [(V, M)] pair -- i.e. that a verified program's WP is TYPE-COMPATIBLE   *)
(* with the residue's conjunct.  Nothing is plugged into the kernel loop    *)
(* here; that is step 3.                                                    *)
(*                                                                         *)
(* THE ENTRY CONDITIONS are the pure facts an INITIALIZER (exec, forkret's  *)
(* park) establishes when it writes the trapframe and loads the image, and  *)
(* they are spelled against the SLOT's own vocabulary -- [tf_resume_pc V0]  *)
(* and [tf_w V0 tf_sp_idx], not the Umode tier's [m]/[sp0].  They mirror    *)
(* [USpecSync.wp_sync_start_body]'s premise set exactly, one for one:       *)
(*                                                                         *)
(*   Hlay  sync_layout (pv_upt V0)                                          *)
(*   Htext uimg_sub SyncInstrs.sync_bytes M0                                *)
(*   Hsp   -- NOT a premise: it is DISCHARGED by [tf_resume_gpr_sp], which  *)
(*            is the whole point of keying the slot on the trapframe.       *)
(*   Hst   uv_stack (pv_upt V0) M0 (tf_w V0 tf_sp_idx) 32                   *)
(*                                                                         *)
(* plus the one condition that is about the slot rather than about sync's   *)
(* body: the resume pc IS the ELF entry, [tf_resume_pc V0 = SyncSyms.start].*)
(* [wp_sync_start_body] asks for no alignment fact on the entry pc (its     *)
(* first instruction's fetch fact comes from [sync_layout] through          *)
(* [sync_layout_fetch]), so none is carried.                                *)
(*                                                                         *)
(* [Rut (pv_upt V0)] AND THE PAIRED TRAP SEAM -- [> (user_trap_frame ...    *)
(* * uexec_wp -* WP Loop)], the premise that both hands the kernel the trap *)
(* frame and takes the NEXT WP back (MILESTONE G) -- ARE RECEIVED AND       *)
(* RETAINED UNUSED (Iris is affine, so they are simply left in the spatial  *)
(* context at the end).  That is not an oversight: with [uv_cap] still an   *)
(* ASSUMPTION, sync's traps are absorbed by the assumed round-trip          *)
(* contracts and the kernel loop is never re-entered on this path, so       *)
(* neither the kernel's re-entry premise nor its return channel has a       *)
(* consumer yet.  [uv_cap] is thereby visibly the ONE gap between this      *)
(* lemma and a real linkage.                                                *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import InstrBytes RegFile.
Require Import ProcGeom ProcDefs.
Require Import UserPtTree UserFrame UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeSyscall.
Require Import UCodeSync USpecSync UProofSync.
Require Import UexecWp UexecSlot UmodeKernelTie.
Require User.SyncSyms User.SyncInstrs.
Local Open Scope Z_scope.
Import Defs.

Section USyncKernel.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  (* NO [Context {CID : CpuId}]: the slot binds the hart itself (a process
     may resume on any hart), and [UProofSync.wp_sync_start] takes [CIDp]
     as an explicit leading binder for exactly the same reason. *)

  Lemma sync_uexec_slot (V0 : pprivate) (M0 : gmap Z (bv 8)) :
    tf_resume_pc V0 = (mword_of_int SyncSyms.start : mword 64) ->
    sync_layout (pv_upt V0) ->
    uimg_sub SyncInstrs.sync_bytes M0 ->
    uv_stack (pv_upt V0) M0 (tf_w V0 tf_sp_idx) 32 ->
    □ (∀ C : ucfg, ⌜loop_ok C (pv_upt V0)⌝ -∗
         uv_cap C (pv_upt V0) (xv6_sys_protocol C (pv_upt V0))) ⊢
    uexec_slot V0 M0.
  Proof.
    intros Hentry Hlay Htext Hst.
    iIntros "#Hcap".
    (* [Typeclasses Opaque uexec_slot] blocks [IntoForall]: unfold by hand. *)
    rewrite /uexec_slot.
    iIntros (h C Rut b ms_v sc_v stval_v sepc_v)
            "%Hlo %Hmso Hhw Hmi Hwi Hregs Hpt Hcfg Hrut Hhdl".
    (* the assumed trap capability, at THIS round's config *)
    iAssert (uv_cap C (pv_upt V0) (xv6_sys_protocol C (pv_upt V0)))
      as "#Hcap0".
    { iApply "Hcap". iPureIntro. exact Hlo. }
    (* cross the seam: the slot's spatial premises become the verified
       tier's threading bundle at the same concrete state *)
    iDestruct (uexec_state_uv_cap_gpr (CID := h) C (pv_upt V0)
                 (xv6_sys_protocol C (pv_upt V0)) M0 (tf_resume_gpr b V0)
                 ms_v sc_v stval_v sepc_v (tf_resume_pc V0) Hmso
                 with "Hcap0 Hhw Hmi Hwi Hregs Hpt Hcfg") as "(Hcg & Hpc)".
    iEval (rewrite Hentry) in "Hpc".
    (* [Hrut] and [Hhdl] stay in the spatial context, unused -- see header *)
    iApply (wp_sync_start C (pv_upt V0) h M0 (tf_resume_gpr b V0)
              (tf_w V0 tf_sp_idx) Hlay Htext (tf_resume_gpr_sp b V0) Hst
              with "Hcg Hpc").
  Qed.

End USyncKernel.
