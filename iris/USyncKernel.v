(* ===================================================================== *)
(* USyncKernel.v -- THE `sync` PROGRAM'S WHOLE-PROCESS WP AS A CONSTRUCTOR  *)
(* OF THE TRAPFRAME-KEYED SLOT: the ENTRY DEPOSIT.                         *)
(*                                                                         *)
(* See claude-notes/design/user-wp-slot.md (the step-2 layer).             *)
(* [UProofSync.wp_sync_start] is stated in the Umode tier's vocabulary      *)
(* ([uv_cap_gpr] + [pc_is]) at a FIXED table; the kernel's trap loop holds  *)
(* [uexec_slot W] at a user-visible key [W : uvis], the table forall-bound  *)
(* INSIDE.  This file is the one lemma that says those are THE SAME         *)
(* THEOREM at the right key -- i.e. that a verified program's WP is         *)
(* TYPE-COMPATIBLE with the residue's conjunct.  Nothing is plugged into    *)
(* the kernel loop here; that is step 3.                                    *)
(*                                                                         *)
(* THE ENTRY CONDITIONS are the pure facts an INITIALIZER (exec, forkret's  *)
(* park) establishes when it writes the trapframe and loads the image, and  *)
(* they are spelled against the SLOT's own vocabulary -- [tf_resume_pc]     *)
(* and [tf_w _ tf_sp_idx] over [uvis_tf], not the Umode tier's [m]/[sp0].   *)
(* They mirror [USpecSync.wp_sync_start_body]'s premise set one for one,   *)
(* SPLIT BY WHAT THEY MENTION:                                              *)
(*                                                                         *)
(*   Htext uimg_sub SyncInstrs.sync_bytes M        -- about the KEY alone   *)
(*   Hsp   -- NOT a premise: it is DISCHARGED by [tf_resume_gpr_sp], which  *)
(*            is the whole point of keying the slot on the trapframe.       *)
(*   Hlay  sync_layout P                           -- about the TABLE       *)
(*   Hst   uv_stack P M sp 32                      -- about the TABLE       *)
(*                                                                         *)
(* The two table-dependent ones cannot be premises of a lemma whose         *)
(* conclusion binds the table inside: they are GUARDED under that forall,   *)
(* as [sync_entry_tbl] -- for every [(C, P)] the loop may offer (i.e. with  *)
(* [loop_ok C P], the slot's own guard), the layout and the stack hold at   *)
(* [P].  It is a plain [Prop], not an iProp guard: both conjuncts are       *)
(* [Prop]s that [wp_sync_start] consumes as Rocq hypotheses, so a           *)
(* [⌜_⌝ -∗] wrapping would only be peeled again at the one use.  The        *)
(* assumed trap capability is guarded the same way, over [(C, P)].          *)
(*                                                                         *)
(* plus the one condition that is about the slot rather than about sync's   *)
(* body: the resume pc IS the ELF entry, [tf_resume_pc tf = SyncSyms.start].*)
(* [wp_sync_start_body] asks for no alignment fact on the entry pc (its     *)
(* first instruction's fetch fact comes from [sync_layout] through          *)
(* [sync_layout_fetch]), so none is carried.                                *)
(*                                                                         *)
(* [Rut P] AND THE PAIRED TRAP SEAM -- [> (user_trap_frame ... * uexec_wp   *)
(* -* WP Loop)], the premise that both hands the kernel the trap frame and  *)
(* takes the NEXT WP back (MILESTONE G) -- ARE RECEIVED AND RETAINED        *)
(* UNUSED (Iris is affine, so they are simply left in the spatial context   *)
(* at the end).  That is not an oversight: with [uv_cap] still an           *)
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
Require Import RiscvLang RiscvPtsto.
Require Import ProcGeom ProcDefs UserPtTree.
Require Import UserExec.
Require Import UmodeCap UmodeAbi UmodeSyscall.
Require Import UCodeSync UProofSync.
Require Import UexecWp UexecSlot UmodeKernelTie.
Require User.SyncSyms User.SyncInstrs.
Local Open Scope Z_scope.
Import Defs.

(* the table-dependent half of sync's entry conditions, guarded by the
   slot's own [loop_ok] so they are owed only at tables the loop can offer *)
Definition sync_entry_tbl (M : gmap Z (bv 8)) (sp : mword 64) : Prop :=
  forall (C : ucfg) (P : uptd), loop_ok C P ->
    sync_layout P /\ uv_stack P M sp 32.

Section USyncKernel.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  (* NO [Context {CID : CpuId}]: the slot binds the hart itself (a process
     may resume on any hart), and [UProofSync.wp_sync_start] takes [CIDp]
     as an explicit leading binder for exactly the same reason. *)

  Lemma sync_uexec_slot (W : uvis) :
    tf_resume_pc (uvis_tf W) = (mword_of_int SyncSyms.start : mword 64) ->
    uimg_sub SyncInstrs.sync_bytes (uvis_M W) ->
    sync_entry_tbl (uvis_M W) (tf_w (uvis_tf W) tf_sp_idx) ->
    □ (∀ (C : ucfg) (P : uptd), ⌜loop_ok C P⌝ -∗
         uv_cap C P (xv6_sys_protocol C P)) ⊢
    uexec_slot W.
  Proof.
    intros Hentry Htext Htbl.
    iIntros "#Hcap".
    (* [Typeclasses Opaque uexec_slot] blocks [IntoForall]: unfold by hand. *)
    rewrite /uexec_slot.
    iIntros (h C Rut P b ms_v sc_v stval_v sepc_v)
            "%Hlo %Hmso Hhw Hmi Hwi Hregs Hpt Hcfg Hrut Hhdl".
    destruct (Htbl C P Hlo) as [Hlay Hst].
    (* the assumed trap capability, at THIS round's config and table *)
    iAssert (uv_cap C P (xv6_sys_protocol C P)) as "#Hcap0".
    { iApply "Hcap". iPureIntro. exact Hlo. }
    (* cross the seam: the slot's spatial premises become the verified
       tier's threading bundle at the same concrete state *)
    iDestruct (uexec_state_uv_cap_gpr (CID := h) C P
                 (xv6_sys_protocol C P) (uvis_M W) (tf_resume_gpr b (uvis_tf W))
                 ms_v sc_v stval_v sepc_v (tf_resume_pc (uvis_tf W)) Hmso
                 with "Hcap0 Hhw Hmi Hwi Hregs Hpt Hcfg") as "(Hcg & Hpc)".
    iEval (rewrite Hentry) in "Hpc".
    (* [Hrut] and [Hhdl] stay in the spatial context, unused -- see header *)
    iApply (wp_sync_start C P h (uvis_M W) (tf_resume_gpr b (uvis_tf W))
              (tf_w (uvis_tf W) tf_sp_idx) Hlay Htext
              (tf_resume_gpr_sp b (uvis_tf W)) Hst
              with "Hcg Hpc").
    Unshelve. exact (TsoCtx.MkCtxId inhabitant inhabitant).
  Qed.

End USyncKernel.
