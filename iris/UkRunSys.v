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
Require Import ProcGeom.   (* [tf_arg_idx] -- wait's row is based at a0 *)
Require Import UserPtTree. (* [umem_wr_write] / [umem_write_prefix] *)
Require Import UkStep.
Require Import UmodeArith.  (* [moi_add_l] / [uint_moi]: read's row addresses
                               through [add_vec_int], the heap through [Z] *)
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
    n <> USYS_exec -> n <> USYS_sbrk ->
    n <> USYS_wait -> n <> USYS_pipe -> n <> USYS_read -> n <> USYS_fstat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs h m pc avail -∗
    (∀ (h' : CpuId) (r : mword 64),
       urun γt γd γs h' (<[Regidx (mword_of_int 10) := r]> m) (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hexit Hfork Hexec Hsbrk H3 H4 H5 H8 Hal4.
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
    destruct (usys_mem_ok_quiet n _ r _ _ _ _ _ _ Hexec Hsbrk H3 H4 H5 H8 Hok)
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

  (* ------------------------------------------------------------------- *)
  (* ecall, at read -- THE FIRST SYSCALL IN THIS TIER THAT WRITES USER     *)
  (* MEMORY.                                                              *)
  (*                                                                      *)
  (* [UsysMemOk]'s read row says the kernel wrote SOME [d] bytes at        *)
  (* argument 1, no more than the count at argument 2, and left the        *)
  (* permission map and the break alone.  It does not say WHICH bytes, and *)
  (* it does not tie [d] to the return value -- so this leaf does not      *)
  (* either.  What it does say is the only thing a caller can use: hand in *)
  (* the whole count as a run you own, get the whole count back at SOME    *)
  (* contents.                                                            *)
  (*                                                                      *)
  (* OWNING THE WHOLE COUNT IS THE PREMISE, not a convenience.  The row    *)
  (* licenses a write anywhere in [buf .. buf+cnt), so a caller that owned *)
  (* less could not absorb it, and the heap would be left describing bytes *)
  (* the kernel had changed underneath it.                                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_read (γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (a : Z) (cnt : nat) (f : nat -> bv 8) (avail : nat) :
    usysno m = USYS_read ->
    m !!! Regidx (mword_of_int 11) = (mword_of_int a : mword 64) ->
    bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 12)) 31 0
               : mword 32) = Z.of_nat cnt ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    ubytes γd a cnt f -∗
    urun γt γd γs h m pc avail -∗
    (∀ (h' : CpuId) (r : mword 64) (g : nat -> bv 8),
       ubytes γd a cnt g -∗
       urun γt γd γs h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Ha1 Hcnt Hal4.
    iIntros "#Hi Hbs Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    (* the run is in the image, and does not wrap *)
    iDestruct (uheap_ubytes_img with "Hheap Hbs") as %Himg.
    iApply (UkStep.wp_uk_ecall C pt Rut pm sz Hlo Hpm M m pc Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz)) = USYS_read).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_read = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_read = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    iIntros (r M' pm' sz') "%Hok".
    (* unfold the row down to its read arm *)
    unfold usys_mem_ok in Hok.
    destruct (decide (USYS_read = USYS_exec)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_read = USYS_sbrk)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_read = USYS_wait)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_read = USYS_pipe)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_read = USYS_read)) as [_ | Hne];
      [ | exfalso; exact (Hne eq_refl) ].
    destruct Hok as [(d & bs & Hdle & HM') [-> ->]].
    (* the row's [d] is within the run the caller owns *)
    cbn [uvis_tf uvis_of_run] in Hdle, HM'.
    unfold usys_rdcount in Hdle. rewrite tf_of_arg2 in Hdle.
    rewrite Hcnt in Hdle.
    assert (Hdn : (d <= cnt)%nat) by lia.
    rewrite tf_of_arg1 Ha1 in HM'.
    (* ...so writing [d] of them is writing all [cnt], the tail unchanged *)
    (* the row addresses through [add_vec_int], the heap through [Z] --
       and they agree, because every owned address is below MAXVA *)
    assert (Hwrap : forall k : nat, (k < d)%nat ->
               uint (add_vec_int (mword_of_int a : mword 64) (Z.of_nat k))
               = (a + Z.of_nat k)%Z).
    { intros k Hk.
      destruct (proj2 (Himg 0%nat ltac:(lia))) as [Ha0 _].
      destruct (proj2 (Himg k ltac:(lia))) as [_ Hak].
      assert (Ha64 : 0 <= a < Z64) by (unfold Z64; lia).
      assert (Hak64 : 0 <= a + Z.of_nat k < Z64) by (unfold Z64; lia).
      unfold add_vec_int.
      rewrite moi_add_l (uint_moi a Ha64).
      exact (uint_moi (a + Z.of_nat k) Hak64). }
    rewrite (umem_wr_write M a d bs Hwrap) in HM'.
    rewrite (umem_write_prefix M a cnt d bs f Hdn
               ltac:(intros k Hk; exact (proj1 (Himg k Hk)))) in HM'.
    subst M'.
    (* the slot ends in a [WP], so it absorbs the heap's update -- which is
       the only place the update CAN run, the row being what says how far
       the image moved *)
    iApply uslot_bupd.
    iMod (uheap_store_run γt γd γs M pm a cnt f
            (fun k => if decide (k < d)%nat then bs k else f k)
            with "Hheap Hbs") as "[Hheap Hbs]".
    iModIntro.
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite (uslot_bump_run m pc M
               (umem_write M a cnt
                  (fun k => if decide (k < d)%nat then bs k else f k))
               pm pm sz sz r Hx0 Hal4).
    iApply (urun_close_upd _ _ _ _ _ m (mword_of_int 10) _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r _ with "Hbs Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* EXEC'S FAILURE ARM.  A successful exec never returns to this WP at all *)
  (* -- the new program's is minted by exec from the new trapframe and     *)
  (* image -- so the only arm that comes back is the failure, and the row  *)
  (* says so outright: -1, and not one byte moved.                         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_exec (γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    usysno m = USYS_exec ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hal4.
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
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz)) = USYS_exec).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_exec = USYS_exit)) as [He | _];
      [ exfalso; unfold USYS_exec, USYS_exit in He; discriminate He | ].
    destruct (decide (USYS_exec = USYS_fork)) as [He | _];
      [ exfalso; unfold USYS_exec, USYS_fork in He; discriminate He | ].
    iIntros (r M' pm' sz') "%Hok".
    destruct (usys_mem_ok_exec_row USYS_exec _ r _ _ _ _ _ _ eq_refl Hok)
      as [-> [-> [-> ->]]].
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite (uslot_bump_run m pc M M pm pm sz sz
               (mword_of_int (-1) : mword 64) Hx0 Hal4).
    iApply (urun_close_upd _ _ _ _ _ m (mword_of_int 10) _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' with "Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* WAIT AT A NULL STATUS POINTER.  The kernel's own [addr != 0] test     *)
  (* means nothing is copied out, so the heap the caller owns comes back   *)
  (* untouched and the leaf can hand the SAME run on -- exactly the quiet  *)
  (* row's shape.  This is the arm init and sh both take.                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_wait_null (γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    usysno m = USYS_wait ->
    uint (m !!! Regidx (mword_of_int 10)) = 0 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs h m pc avail -∗
    (∀ (h' : CpuId) (r : mword 64),
       urun γt γd γs h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hz Hal4.
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
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz)) = USYS_wait).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    assert (Ha0 : uint (uvis_tf (uvis_of_run m pc M pm sz) !!! tf_arg_idx 0) = 0).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_arg0. exact Hz. }
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_wait = USYS_exit)) as [He | _];
      [ exfalso; unfold USYS_wait, USYS_exit in He; discriminate He | ].
    destruct (decide (USYS_wait = USYS_fork)) as [He | _];
      [ exfalso; unfold USYS_wait, USYS_fork in He; discriminate He | ].
    iIntros (r M' pm' sz') "%Hok".
    destruct (usys_mem_ok_wait_null USYS_wait _ r _ _ _ _ _ _
                eq_refl Ha0 Hok) as [-> [-> ->]].
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite (uslot_bump_run m pc M M pm pm sz sz r Hx0 Hal4).
    iApply (urun_close_upd _ _ _ _ _ m (mword_of_int 10) _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r with "Hrun").
  Qed.

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
