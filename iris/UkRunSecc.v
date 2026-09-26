(* ===================================================================== *)
(* UkRunSecc.v -- THE ECALL LEAF AT seccomp(2), ROW 23.                   *)
(*                                                                        *)
(* Design: claude-notes/design/seccomp.md SS4 (the row) and the S3        *)
(* rulings (G1): [UkRun.urun] is keyed at the FULL mask, and row 23 is the *)
(* one row that moves the mask, so the leaf does not re-close a run.  Its  *)
(* continuation proves the process's SLOT at the resumed key instead --    *)
(* the key's mask the full mask ANDed with a0, its table the one the run   *)
(* trapped from, which the caller reads through its ledger's table view   *)
(* ([UserFd.utab]: [tab_le] of it, the S3 ruling G2).  A process that      *)
(* masks itself leaves the verified tier here: the seccomp program answers *)
(* the continuation out of the universe ([UexecSecc.useccomp_mint]).      *)
(*                                                                        *)
(* Stated at the full-mask run like every other leaf; the number is free   *)
(* ([UexecSG.free_num] 23), so the deposit is the free one.               *)
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
Require Import ProcDefs.   (* [secc_all] *)
Require Import UkStep.
Require Import UserHeap.
Require Import UserPerm.
Require Import CtxIdDefs.
Require Import ChildTok.
Require Import UserFrame UserExecFacts.
Require Import UkRun UkRunSys.
Require Import UserFd.
Require Import UexecSG.
Local Open Scope Z_scope.
Import Defs.

Section UkRunSecc.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Lemma wp_uk_ecall_seccomp (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (v : list fdstate) :
    usysno m = USYS_seccomp ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_seccomp -∗
    (* the program's half of its table view, read and dropped *)
    utab (ukn_fd N) v -∗
    (∀ W : uvis,
       ⌜uvis_secc W = and_vec secc_all (m !!! Regidx (mword_of_int 10))⌝ -∗
       ⌜tab_le (uvis_fd W) v⌝ -∗
       my_pay (uvis_gen W) (ukn_pay N) -∗
       uslot W) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4.
    iIntros "#Hi Hrun Hsb Htab Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (utab_agree with "Hufd Htab") as %Hle.
    iMod (udepw_mint N m pc _ M pm _ fdv cw gn cs pidv
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
                   = USYS_seccomp).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all))
                     = USYS_seccomp)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_seccomp = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate He | ].
    destruct (decide (USYS_seccomp = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate He | ].
    destruct (decide (USYS_seccomp = USYS_wait)) as [He | _];
      [ exfalso; vm_compute in He; discriminate He | ].
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow _".
    (* THE THREE ROWS THE CONTINUATION READS: the mask, the table, the
       generation *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    subst gn'.
    assert (Hview : fdv' = fdv).
    { refine (usys_fd_ok_quiet _ _ _ _ _ _ _ _ _ Hfdok);
        vm_compute; discriminate. }
    subst fdv'.
    unfold usys_secc_ok in Hscrow.
    destruct (decide (USYS_seccomp = USYS_seccomp)) as [_ | Hne];
      [ | exfalso; exact (Hne eq_refl) ].
    destruct Hscrow as [Hsc _].
    iApply "Hcont".
    - iPureIntro. cbn [uvis_secc bump bump_at]. rewrite Hsc.
      cbn [uvis_secc uvis_tf uvis_of_run]. rewrite tf_of_arg0. reflexivity.
    - iPureIntro. cbn [uvis_fd bump bump_at]. exact Hle.
    - cbn [uvis_gen bump bump_at]. iExact "Hmy".
  Qed.

End UkRunSecc.
