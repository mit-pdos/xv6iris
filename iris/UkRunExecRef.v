(* ===================================================================== *)
(* UkRunExecRef.v -- the exec leaf at a SUPPLIER-NAMED REFUND (lane M6b).  *)
(*                                                                        *)
(* [UkRunSys.wp_uk_ecall_exec_at_cwd] hands a FAILED exec's refund back   *)
(* as the record's own exit payload at the kill status                    *)
(* ([UkRun.udepw_at_ref]: the deposit carries [□ (sexec_refund f -∗       *)
(* ukn_pay N (-1))]).  That is the one shape a caller could exit on, and   *)
(* it is also the ONLY thing the refund can be: the payload family is the  *)
(* exec'd program's exit family, fixed by whoever reaps it.  /init's child *)
(* needs more than its exit on that arm -- it prints “init: exec sh        *)
(* failed” first, and the credential that pays those bytes went INTO the   *)
(* deposit with the lease and the position ([UkInit.init_exec_sup_pos]),  *)
(* so it has to come back OUT at its own shape, not folded into the exit   *)
(* family.  This file is the same leaf with the refund's consequence a     *)
(* parameter: [udepw_at_refR N m pc c R] is [udepw_at_ref] with            *)
(* [□ (sexec_refund f -∗ R)], and the leaf hands the caller [R].  The       *)
(* original is this at [R := ukn_pay N (-1)]; nothing below UkRunSys       *)
(* moves.  The proof is [wp_uk_ecall_exec_at_cwd]'s verbatim.              *)
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
Require Import FdSlots.      (* [fdstate] -- the key's descriptor view *)
Require Import UkStep.
Require Import UserHeap.
Require Import UserPerm.    (* [uperm] -- the row's permission-map argument *)
Require Import RiscvModelBytes. (* [nth_byte] -- pipe's two reported words *)
Require Import CtxIdDefs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
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
Local Open Scope Z_scope.
Require Import UkRun.
Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UserCwd.  (* [ucwd] -- the program's own half of its working
                            directory, which the exec leaf reads *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)


Require Import UkRunSys.  (* [usysno] -- the syscall number off a7 *)

Section UkRunExecRef.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  (* [UexecSG.sbundle_pay_ref] with the refund's consequence a parameter *)
  Definition sbundle_pay_refR (X : uvis -d> iPropO Σ) (Q : Z -> iProp Σ)
      (R : iProp Σ) (W : uvis) : iProp Σ :=
    (∃ f : sfam, ⌜sexit_pay f = Q⌝ ∗ □ (sexec_refund f -∗ R)
                 ∗ sbundle_at X USYS_exec f W)%I.

  (* ...and the original is it at the record's own exit payload *)
  Lemma sbundle_pay_ref_of_refR (X : uvis -d> iPropO Σ) (Q : Z -> iProp Σ)
      (W : uvis) :
    sbundle_pay_refR X Q (Q (-1)) W -∗ sbundle_pay_ref X Q W.
  Proof using .
    iIntros "H". iDestruct "H" as (f) "(%Hp & #Hrf & Hb)".
    rewrite /sbundle_pay_ref. iExists f. iSplitR; [ done | ].
    iSplitR; [ iExact "Hrf" | iExact "Hb" ].
  Qed.

  (* [UkRun.udepw_at_ref] with the refund's consequence a parameter *)
  Definition udepw_at_refR (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (c : Z) (R : iProp Σ) : iProp Σ :=
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (gn : gname) (cs : gset gname) (pidv : mword 32),
       my_pay gn (ukn_pay N) -∗
       (* ...and whether the key's table holds a pipe row, lent with them
          (design/pipe.md, "The exit path"): a pinned exec supply builds
          the new image's ENTRY, and an entry constructor asks for it.
          Persistent, so nothing comes back. *)
       urun_rows N fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       sbundle_pay_refR uslot (ukn_pay N) R
         (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all))%I.

  Lemma udepw_at_ref_of_refR (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (c : Z) :
    udepw_at_refR N m pc c (ukn_pay N (-1)) -∗ udepw_at_ref N m pc c.
  Proof using .
    rewrite /udepw_at_refR /udepw_at_ref.
    iIntros "Hd" (M pm sz fdv gn cs pidv) "Hmp #Hnpw Hh Hf".
    iDestruct ("Hd" $! M pm sz fdv gn cs pidv with "Hmp Hnpw Hh Hf")
      as "(Hh & Hf & Hb)".
    iFrame "Hh Hf". iApply (sbundle_pay_ref_of_refR with "Hb").
  Qed.

  Lemma wp_uk_ecall_exec_at_cwd_refR (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (c : Z) (R : iProp Σ) :
    usysno m = USYS_exec ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* the program's half of its working directory... *)
    UserCwd.ucwd (ukn_cwd N) c -∗
    (* ...and the deposit at every key whose cwd is that one inum, AT THE
       REFUND THE SUPPLIER NAMED: [udepw_at_refR] is [UkRun.udepw_at_ref]
       with the refund's consequence a parameter [R] instead of the
       record's own exit payload. *)
    udepw_at_refR N m pc c R -∗
    (∀ h' : CpuId,
       UserCwd.ucwd (ukn_cwd N) c -∗
       (* ...AND THE REFUND, as the supplier's wand reads it *)
       R -∗
       urun N h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4.
    iIntros "#Hi Hrun Hcwd Hsb Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    (* the whole point of the leaf: the key's cwd IS the one the caller's
       bundle is stated at *)
    iDestruct (ucwd_agree with "Hcwda Hcwd") as %->.
    iDestruct ("Hsb" $! M pm sz fdv gn cs pidv with "Hmy Hnpx Hheap Hufd")
      as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv c gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all) = USYS_exec).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)) = USYS_exec)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_exec = USYS_exit)) as [He | _];
      [ exfalso; unfold USYS_exec, USYS_exit in He; discriminate He | ].
    destruct (decide (USYS_exec = USYS_fork)) as [He | _];
      [ exfalso; unfold USYS_exec, USYS_fork in He; discriminate He | ].
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "(%Hfp & #Href & Hdepn)".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    (* THE POST AT exec IS THE REFUND (lane KILL-PAY, K4(a), R-A): it used
       to be [emp] and is a wand from "the answer was -1" now
       ([UexecSG.spost_at_exec]), which is exactly the branch this leaf is
       on -- a successful exec never resumes here. *)
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow Hsp".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    assert (Hcw : cw' = c)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N c cw' Hcw with "Hcwda") as "Hcwda".
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: no entry
       re-incarnates its caller, and this lane's children row is the
       identity at every number ([UsysMemOk] SS2e/SS2f).  Both are
       substituted rather than re-keyed -- the generation has no
       authority beside it, and the children authority is already at
       the set the process resumes at. *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    destruct (usys_mem_ok_exec_row USYS_exec _ r _ _ _ _ _ _ _ _ eq_refl Hok)
      as [-> [-> [-> ->]]].
    (* the refund, cashed at the answer this arm IS at, and turned into
       what the supplier's wand says it is worth *)
    iEval (rewrite spost_at_exec) in "Hsp".
    iDestruct ("Hsp" with "[//]") as "Hrf".
    iDestruct ("Href" with "Hrf") as "Hpayret".
    cbn [uvis_M uvis_perm uvis_of_run].
    assert (Hview : fdv' = fdv).
    { refine (usys_fd_ok_quiet _ _ _ _ _ _ _ _ _ Hfdok);
        vm_compute; discriminate. }
    subst fdv'.
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv c cw' gn gn cs cs pidv false false secc_all secc_all
               (mword_of_int (-1) : mword 64) Hx0 Hal4).
    iApply ukcq_ukc.
    iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' with "Hcwd Hpayret Hrun").
  Qed.

  (* ===================================================================== *)
  (* ...AND WITH THE RECORD'S IDENTITY AUTHORITIES LENT (lane EXEC-SEAM).   *)
  (* [SpecKexec.exec_slot_pre]'s two wands now pin the resumed key's       *)
  (* children set and pid to the exec'ing process's own ([uvis_ch W' =     *)
  (* cs], [uvis_pid W' = pidv]), and a supplier that wants to SAY what      *)
  (* those are -- init's, for the shell it starts: “no children yet, and    *)
  (* not <init>” -- has to read [cs] and [pidv] off the record's authority  *)
  (* for both ([UkRun.urun_ids]) against the program's own fragments       *)
  (* ([UserChildren.uch] / [upid]).  So this deposit lends the authority    *)
  (* beside the heap and the descriptor authority and takes it back; the    *)
  (* leaf below is [wp_uk_ecall_exec_at_cwd_refR]'s proof with one more     *)
  (* resource handed through, and [udepw_at_refR_ids_of_refR] is the        *)
  (* forgetful direction for a supplier that reads neither.                 *)
  (* ===================================================================== *)
  Definition udepw_at_refR_ids (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (c : Z) (R : iProp Σ) : iProp Σ :=
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (gn : gname) (cs : gset gname) (pidv : mword 32),
       my_pay gn (ukn_pay N) -∗
       (* ...and whether the key's table holds a pipe row, lent with them
          (design/pipe.md, "The exit path"): a pinned exec supply builds
          the new image's ENTRY, and an entry constructor asks for it.
          Persistent, so nothing comes back. *)
       urun_rows N fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       urun_ids N cs pidv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       urun_ids N cs pidv ∗
       sbundle_pay_refR uslot (ukn_pay N) R
         (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all))%I.

  Lemma udepw_at_refR_ids_of_refR (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (c : Z) (R : iProp Σ) :
    udepw_at_refR N m pc c R -∗ udepw_at_refR_ids N m pc c R.
  Proof using .
    rewrite /udepw_at_refR /udepw_at_refR_ids.
    iIntros "Hd" (M pm sz fdv gn cs pidv) "Hmp #Hnpw Hh Hf Hids".
    iDestruct ("Hd" $! M pm sz fdv gn cs pidv with "Hmp Hnpw Hh Hf")
      as "(Hh & Hf & Hb)".
    iFrame "Hh Hf Hids Hb".
  Qed.

  Lemma wp_uk_ecall_exec_at_cwd_refR_ids (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (c : Z) (R : iProp Σ) :
    usysno m = USYS_exec ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* the program's half of its working directory... *)
    UserCwd.ucwd (ukn_cwd N) c -∗
    (* ...and the deposit at every key whose cwd is that one inum, at the
       supplier-named refund AND WITH THE IDENTITY AUTHORITIES LENT
       ([udepw_at_refR_ids], lane EXEC-SEAM) *)
    udepw_at_refR_ids N m pc c R -∗
    (∀ h' : CpuId,
       UserCwd.ucwd (ukn_cwd N) c -∗
       (* ...AND THE REFUND, as the supplier's wand reads it *)
       R -∗
       urun N h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4.
    iIntros "#Hi Hrun Hcwd Hsb Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    (* the whole point of the leaf: the key's cwd IS the one the caller's
       bundle is stated at *)
    iDestruct (ucwd_agree with "Hcwda Hcwd") as %->.
    iDestruct ("Hsb" $! M pm sz fdv gn cs pidv with "Hmy Hnpx Hheap Hufd Hcha")
      as "(Hheap & Hufd & Hcha & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv c gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all) = USYS_exec).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)) = USYS_exec)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_exec = USYS_exit)) as [He | _];
      [ exfalso; unfold USYS_exec, USYS_exit in He; discriminate He | ].
    destruct (decide (USYS_exec = USYS_fork)) as [He | _];
      [ exfalso; unfold USYS_exec, USYS_fork in He; discriminate He | ].
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "(%Hfp & #Href & Hdepn)".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    (* THE POST AT exec IS THE REFUND (lane KILL-PAY, K4(a), R-A): it used
       to be [emp] and is a wand from "the answer was -1" now
       ([UexecSG.spost_at_exec]), which is exactly the branch this leaf is
       on -- a successful exec never resumes here. *)
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow Hsp".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    assert (Hcw : cw' = c)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N c cw' Hcw with "Hcwda") as "Hcwda".
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: no entry
       re-incarnates its caller, and this lane's children row is the
       identity at every number ([UsysMemOk] SS2e/SS2f).  Both are
       substituted rather than re-keyed -- the generation has no
       authority beside it, and the children authority is already at
       the set the process resumes at. *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    destruct (usys_mem_ok_exec_row USYS_exec _ r _ _ _ _ _ _ _ _ eq_refl Hok)
      as [-> [-> [-> ->]]].
    (* the refund, cashed at the answer this arm IS at, and turned into
       what the supplier's wand says it is worth *)
    iEval (rewrite spost_at_exec) in "Hsp".
    iDestruct ("Hsp" with "[//]") as "Hrf".
    iDestruct ("Href" with "Hrf") as "Hpayret".
    cbn [uvis_M uvis_perm uvis_of_run].
    assert (Hview : fdv' = fdv).
    { refine (usys_fd_ok_quiet _ _ _ _ _ _ _ _ _ Hfdok);
        vm_compute; discriminate. }
    subst fdv'.
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv c cw' gn gn cs cs pidv false false secc_all secc_all
               (mword_of_int (-1) : mword 64) Hx0 Hal4).
    iApply ukcq_ukc.
    iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' with "Hcwd Hpayret Hrun").
  Qed.


End UkRunExecRef.
