(* ===================================================================== *)
(* UkRunSysX.v -- THE ENRICHED EXEC ECALL LEAF: [UkRunSys.wp_uk_ecall_exec] *)
(* on [UexecRetExec.urun_x], where the process HANDS OVER the exec bundle.  *)
(*                                                                         *)
(* The plain leaf is on the plain contract: at an exec ecall the process   *)
(* owes the generic returning arm and nothing else, and only the failure   *)
(* case ever comes back ([UsysMemOk.usys_mem_ok_exec_row]).  Under the     *)
(* enriched contract the return at the trap-out key is                     *)
(* [uexec_ret_x_ecall_exec]:                                               *)
(*                                                                         *)
(*     xbundle uslot_x W  ∗  <the generic returning arm, at uslot_x>       *)
(*                                                                         *)
(* so this leaf takes ONE more premise -- the program supplies the bundle   *)
(* -- and handles the arm exactly as the plain leaf does.                   *)
(*                                                                         *)
(* THE KEY THE BUNDLE IS OWED AT is [uvis_of_run m pc M pm sz fdv]: the     *)
(* registers and pc the program knows, and the image, the permission map,  *)
(* the break and the descriptor view that [urun_x] HIDES.  The bundle reads *)
(* the key only through [uvis_M], argument 1 and [uvis_fd]                 *)
(* ([xbundle_cong]), so the premise quantifies the four hidden components   *)
(* and LENDS the program the heap and descriptor authorities while it       *)
(* builds the bundle: a program pins the bytes and the descriptors it holds *)
(* fragments of against them ([uheap_ubytes_at], [ufd_agree] -- pure       *)
(* conclusions, so both come straight back), and a program with a generic  *)
(* bundle in hand ignores them.  Neither can travel INTO the bundle: the    *)
(* failure arm re-closes [urun_x] out of both.                              *)
(*                                                                         *)
(* THE MACHINE STEP is UkStepGen's X-generic ecall driver at               *)
(* [(uexec_ret_x_F, uslot_x, fun _ => True)] -- [wp_uk_ecall_x] below is   *)
(* an [exact] of [UkStepGen.wp_uk_ecall'] at the two facts it asks for,     *)
(* the fixpoint unfolding ([uslot_x_unfold_gen]) and the transparent arm    *)
(* ([UexecRetExec.uexec_ret_x_transparent]).  [uslot_x] quantifies the     *)
(* TSO context inside its fixpoint exactly as [uslot] does, so the family's *)
(* context predicate is the plain [True].                                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import UsysMemOk UexecSlot UexecRet.
Require Import FdSlots.
Require Import ProcGeom.
Require Import UserPtTree UserExec.   (* [ucfg] *)
Require Import UexecWp.               (* [loop_ok] *)
Require Import UkStep.
Require Import UmodeArith.
Require Import UserHeap.
Require Import UserPerm.
Require Import UserBits.
Require Import RiscvExtras.
Require Import RiscvModelBytes.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.
From Stdlib Require Import ZArith Bool Lia List FunctionalExtensionality.
From iris.base_logic.lib Require Import invariants gen_heap.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import HartSwp HartLift HartSpan HartGoodb HartMemRun HartMCycle
        HartStepFull HartRunFull HartRunGen.
Require Import UserFrame.
Require Import UserExecFacts.
Require Import UsysMemOk.
Require Import UexecSlot UexecRet.
Require Import TsoCtx.
Local Open Scope Z_scope.
Require Import UkRun.
Require Import UkRunSys.       (* [usysno] *)
Require Import UserFd.
Require Import UmodeText.
Require Import UexecRetExec.   (* [uslot_x] / [uvb_x] / [urun_x]: REQUIRED
                                  DIRECTLY, both are [Typeclasses Opaque] *)
Require Import UkStepGen.      (* the X-generic engine *)
Require Import UkRunX.         (* [ukc_x] / [uslot_x_bump_run] / [urun_x_close_upd] *)

Section UkRunSysX.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId}.
  (* NO ambient [CurCtx]: the run binds its own, exactly as UkRun.v says *)
  Context `{XG : uexecXG Σ}.
  Context `{!ghost_varG Σ Z}.

  (* ------------------------------------------------------------------- *)
  (* SS1 THE MACHINE STEP, off the X-generic engine.                       *)
  (* ------------------------------------------------------------------- *)

  (* fact (i) at [uslot_x]: the fixpoint unfolding in the engine's shape,
     [UkStepGen.uslot_unfold_gen]'s proof -- [Q] is [True], so the one
     difference from [uslot_x_unfold] is a vacuous premise *)
  Lemma uslot_x_unfold_gen (W : uvis) :
    uslot_x W ⊣⊢
    ukc' uexec_ret_x_F uslot_x (fun _ : TsoCtx.CurCtx => Logic.True)
      (uvis_perm W) (uvis_M W) (uvis_sz W) (uvis_fd W) (uvis_cwd W)
      (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)).
  Proof.
    rewrite (uslot_x_unfold W) /ukc'.
    iSplit.
    - iIntros "H" (h xi C pt Rfd Rut HRut) "_ %Hlo %Hpm Hb".
      iApply ("H" $! h xi C pt Rfd Rut HRut with "[%] [%] Hb");
        [ exact Hlo | exact Hpm ].
    - iIntros "H" (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
      iApply ("H" $! h xi C pt Rfd Rut HRut with "[%] [%] [%] Hb");
        [ exact I | exact Hlo | exact Hpm ].
  Qed.

  (* [UkStep.wp_uk_ecall] with [uvb -> uvb_x] and [uexec_ret -> uexec_ret_x]:
     the engine at the enriched family *)
  Lemma wp_uk_ecall_x `{CID : CpuId} `{XI : CurCtx} (C : ucfg) (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
      (π : gmap (mword 27) uperm) (sz : Z)
      (Hlo : loop_ok C pt) (Hpm : perm_of (ud_um pt) sz = π)
      (HRut : forall pt' : uptd,
                ⊢ Rut pt' -∗ TsoCtx.own_context XI ∗
                             (TsoCtx.own_context XI -∗ Rut pt'))
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (fdv : list fdstate) (cw : Z) :
    uk_instr π M pc false (ECALL tt) ->
    (forall s : mstate,
       register_lookup cur_privilege s.(sregs) = User ->
       register_lookup (R_bitvector_64 PC) s.(sregs) = pc ->
       goodmb Du_r Du_w (execute (ECALL tt)) s ∅ = true) ->
    uvb_x C pt Rfd Rut sz π fdv cw M m pc -∗
    uexec_ret_x uecall_scause (uvis_of_run m pc M π sz fdv cw) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    exact (wp_uk_ecall' uexec_ret_x_F uslot_x (fun _ : TsoCtx.CurCtx => Logic.True)
             uslot_x_unfold_gen uexec_ret_x_transparent
             C pt Rfd Rut π sz Hlo Hpm HRut I M m pc fdv cw).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* SS2 THE LEAF.                                                        *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_exec_x (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    usysno m = USYS_exec ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun_x γt γd γs γfd h m pc avail -∗
    (* THE HAND-OVER (header): the bundle at this ecall's key, for whatever
       image, map, break and view the run hides, with the two authorities
       lent for the pure facts the program needs off them *)
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (cw : Z),
       uheap γt γd γs M pm -∗ ufd_auth γfd fdv -∗
       uheap γt γd γs M pm ∗ ufd_auth γfd fdv ∗
       xbundle uslot_x (uvis_of_run m pc M pm sz fdv cw)) -∗
    (* the failure return: -1, and not one byte moved *)
    (∀ h' : CpuId,
       urun_x γt γd γs γfd h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hal4.
    iIntros "#Hi Hrun Hbundle Hcont".
    rewrite /urun_x.
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw)
      "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x_x0 with "Hb") as "[%Hx0 Hb]".
    iDestruct ("Hbundle" $! M pm sz fdv cw with "Hheap Hufd")
      as "(Hheap & Hufd & Hx)".
    iApply (wp_uk_ecall_x C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv cw Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw)) = USYS_exec).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite (uexec_ret_x_ecall_exec _ _ eq_refl Hnum).
    rewrite Hnum.
    iSplitL "Hx"; [ iExact "Hx" | ].
    iIntros (r M' pm' sz' fdv' cw') "%Hok %Hfdok %Hpiperow %Hcwrow".
    destruct (usys_mem_ok_exec_row USYS_exec _ r _ _ _ _ _ _ eq_refl Hok)
      as [-> [-> [-> ->]]].
    cbn [uvis_M uvis_perm uvis_of_run].
    (* the row read, not dropped: exec is none of the four numbers that
       move [p->ofile[]], so the view -- and the authority -- is where the
       process resumes.  [refine] first, so the side goals are at the
       concrete number. *)
    assert (Hview : fdv' = fdv).
    { refine (usys_fd_ok_quiet _ _ _ _ _ _ _ _ _ Hfdok);
        vm_compute; discriminate. }
    subst fdv'.
    rewrite (uslot_x_bump_run m pc M M pm pm sz sz fdv fdv cw cw'
               (mword_of_int (-1) : mword 64) Hx0 Hal4).
    iApply (urun_x_close_upd _ _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate)
              with "Hheap Hstk Hufd").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' with "Hrun").
  Qed.

End UkRunSysX.
