(* ===================================================================== *)
(* UkRunSys.v -- the SYSCALL boundary, on [urun].                          *)
(*                                                                        *)
(* ECALL is the one instruction that is not a wrapper.  Every other leaf   *)
(* keeps the image inside [urun] untouched; a trap hands [user_ptm_inv]    *)
(* back to the kernel, which returns an image the program has to re-own.   *)
(* What it is allowed to have done is [usys_mem_ok]'s table, and the       *)
(* program pays for exactly the row its syscall is in.                     *)
(*                                                                        *)
(* THE QUIET ROW is the one settled here: sixteen syscalls that touch no   *)
(* user memory at all, so [M' = M] and the two heap authorities survive    *)
(* the trap unchanged -- the program keeps every points-to it held across  *)
(* the call, and only a0 moves.  That is what makes [write] framable.      *)
(*                                                                        *)
(* The WINDOW row (the kernel writes a caller-named buffer) and the SBRK   *)
(* row (the image grows or shrinks by pages while the break moves by       *)
(* bytes) are the remaining two, and both need the caller to hand over the *)
(* range the kernel is licensed to touch.  Not yet built.                  *)
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
Require Import UkStep.
Require Import UserHeap.
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
Require Import TsoCtx.   (* [CurCtx]: ambient, per the WpUmode* precedent *)
Local Open Scope Z_scope.
Require Import UkRun.

(* THE SYSCALL NUMBER, off the register file rather than off the trapframe:
   a program knows what it put in a7, and should not have to know that the
   key spells it [usys_num (tf_of m pc)]. *)
Definition usysno (m : regfile) : Z :=
  bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 17)) 31 0 : mword 32).

Section UkRunSys.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  (* ------------------------------------------------------------------- *)
  (* ecall, at a QUIET syscall.  The heap crosses the trap intact: the     *)
  (* kernel is licensed to change nothing about the image, so [urun] comes *)
  (* back at the same [M] and every points-to the program (or its caller)  *)
  (* was holding is still good.  a0 is the kernel's return value, about    *)
  (* which nothing is claimed.                                             *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_quiet (γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (n : Z) (avail : nat) :
    usysno m = n ->
    n <> USYS_exit -> n <> USYS_fork ->
    n <> USYS_exec -> n <> USYS_sbrk -> usys_window n = None ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs h m pc avail -∗
    (∀ (h' : CpuId) (r : mword 64),
       urun γt γd γs h' (<[Regidx (mword_of_int 10) := r]> m) (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hexit Hfork Hexec Hsbrk Hwin Hal4.
    iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rut pm sz Hlo Hpm M m pc Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz)) = n).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum. cbv zeta.
    destruct (decide (n = USYS_exit)) as [He | _]; [ exfalso; exact (Hexit He) | ].
    destruct (decide (n = USYS_fork)) as [He | _]; [ exfalso; exact (Hfork He) | ].
    iIntros (r M' pm' sz') "%Hok".
    destruct (usys_mem_ok_quiet n _ r _ _ _ _ _ _ Hexec Hsbrk Hwin Hok)
      as [-> [-> ->]].
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite (uslot_bump_run m pc M M pm pm sz sz r Hx0 Hal4).
    iApply (urun_close_upd _ _ _ _ _ m (mword_of_int 10) _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r with "Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ecall, at exit.  The process never comes back, so it owes NOTHING --  *)
  (* not even a continuation.  This is the only leaf with no successor.    *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_exit (γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    usysno m = USYS_exit ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs h m pc avail -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn. iIntros "#Hi Hrun".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkStep.wp_uk_ecall C pt Rut pm sz Hlo Hpm M m pc Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz)) = USYS_exit).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_exit = USYS_exit)) as [_ | Hne];
      [ done | exfalso; exact (Hne eq_refl) ].
  Qed.

End UkRunSys.
