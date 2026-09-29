(* PipeReg.v -- THE REGISTRY: a pipe row's exit payment as a PERSISTENT
   handle, so a verified program may hold a pipe without the taint.

   Design of record: claude-notes/design/app-pipe.md SS2 ("A verified
   program holds a pipe: the REGISTRY replaces the taint"), which closes
   the two items claude-notes/completed/pipe-queue.md left under "Open,
   recorded".

   THE WALL IT REMOVES.  kexit closes every descriptor a dying process
   holds, so exit(2)'s bundle row is [SpecFileclose.fileclose_cpays] of the
   key's whole table -- and at a PIPE row that payment is
   [PipeQueue.pipe_cpay], a close LINK (buildable only by the holder of the
   pipe's exclusive queue fragment) or the TAINT.  Until now the only
   PERSISTENT way to answer was the taint, so a program that called pipe(2)
   gave up being verified-and-untainted ([UkRunSys.wp_uk_ecall_pipe] took
   [app_taint] as a premise).  Two things made the fragment itself
   unusable there: it is exclusive, while the exit row is a [∗ list] of
   INDEPENDENT payments (sh holds BOTH ends right after pipe(2), so two
   rows name one pipe), and it cannot cross exec.

   THE READING THAT PAYS.  What a run carries per row is not the fragment
   but a [□]-guarded payment at EITHER END -- the registry.  Being under a
   [□] it is buildable any number of times, which is exactly what two rows
   on one pipe, a dup'd row and a forked child's copy of the table all
   need; and holding one says nothing about where the fragment lives, which
   is the application's business (lane PIPE-PROTO puts it in a per-pipe
   invariant and derives the registry from the invariant's handle).

   WHERE IT IS SPENT: [UexecExecInst.xv6_sbundle_exit_regs] mints exit's
   bundle row from one instance of each row's registry, and
   [UexecSG.srow_reg] is the CLASS FIELD through which [UkRun.urun_nopipe]
   -- which lives below every pipe ghost -- names it.  See this lane's
   finding in claude-notes/projects/app-pipe.md for why the field exists.

   VACUITY, FIRST (durable-notes.md, "Vacuity").  [pipe_reg] must not be
   free, or the wall would have been an illusion and every exit row would
   be paid by nothing.  It is not free, and the argument is mechanised
   below as [pipe_reg_not_free]: firing a close link moves the pipe's
   AUTHORITY, and a link at the trivial payload gives nothing back, so a
   link conjured from [emp] would move the authority away from a fragment
   that did not move -- which [PipeQueue.pipe_queue_agree] refutes at any
   state whose flag the close actually clears.  The two real sources are
   therefore the ones named here ([pipe_reg_of_taint]) and in lane
   PIPE-PROTO ([pipe_reg_of_inv]).  What CANNOT be mechanised in Rocq is
   the statement "[⊢ pipe_reg γp] is not derivable" itself -- it is a
   meta-level claim about the logic, not a proposition of it -- so the
   refutation is stated at the one step the derivation would have to take.

   NOT TIMELESS, and deliberately so: [pipe_cpay] is a disjunction whose
   left arm is a fupd-producing wand, and no [□] makes that timeless.  No
   consumer of [UkRun.urun_nopipe] strips a later off it (this lane
   checked every site), so nothing asks for it. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import list gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From xv6iris Require Import StepIndex.
From transfinite.base_logic.lib Require Import own invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.       (* [riscvGS], [app_taint] *)
Require Import Xv6G.             (* the ONE ghost bundle: [xv6_pipe] is how
                                    [pipeG] is reached here, so that this
                                    file's terms elaborate at the same
                                    instance path as [SpecFileclose]'s *)
Require Import PipeNames.        (* [pipe_names] / [pn_queue] / [pipe_st] *)
Require Import PipeQueue.        (* [pipe_cpay] / [pipe_clink]; the taint is [app_taint] *)
Require Import FdSlots.          (* [fdstate] / [fdst_nopipe] *)
Require Import SpecFileclose.    (* [fileclose_cpay] / [fileclose_cpays] *)

Local Open Scope Z_scope.

Section PipeReg.
  (* THE CONTEXT IS [xv6G]'S AND NOTHING ELSE (durable-notes.md, "A section
     variable of a class type is a LOCAL INSTANCE"): a second [pipeG]
     beside the bundle would make every term here a different proposition
     from [SpecFileclose.fileclose_cpay]'s. *)
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* ===================================================================== *)
  (*  1.  THE REGISTRY                                                     *)
  (* ===================================================================== *)

  (* THE PIPE'S REGISTRATION: its close payment at EITHER END, forever.
     [emp] is the payload because kexit's row is at [emp] -- a dying
     process never resumes to be told anything ([SpecFileclose.
     fileclose_cpays]).  A registered pipe is one whose ends may be closed
     by anybody at any time without anybody owing anything. *)
  Definition pipe_reg (γp : pipe_names) : iProp Σ :=
    (□ (∀ w : bool, pipe_cpay (pn_queue γp) w emp))%I.

  Global Instance pipe_reg_persistent (γp : pipe_names) :
    Persistent (pipe_reg γp).
  Proof using . rewrite /pipe_reg. apply _. Qed.

  (* ...AND A TABLE ROW'S, which is the registry at a pipe row and nothing
     at all anywhere else.  The shape [FdSlots.fdst_nopipe] is the pure
     reading of ([pipe_row_reg_nopipe] below), one resource up. *)
  Definition pipe_row_reg (st : fdstate) : iProp Σ :=
    (match st with
     | FdOpen _ _ (FdPipe γp) => pipe_reg γp
     | _ => emp
     end)%I.

  Global Instance pipe_row_reg_persistent (st : fdstate) :
    Persistent (pipe_row_reg st).
  Proof using . rewrite /pipe_row_reg. destruct st as [| ? ? [| |]]; apply _. Qed.

  (* ===================================================================== *)
  (*  2.  THE VACUITY CHECK (design SS2, "VACUITY CHECK, written first")    *)
  (* ===================================================================== *)

  (* A CLOSE LINK AT THE TRIVIAL PAYLOAD IS NOT FREE, and this is the step
     a derivation from [emp] would have to take: fire it against the
     authority at a state whose flag the close clears, and the authority
     has moved while the fragment has not.  [pst_close true pst0] is
     [pst0] with [ps_wo := false], so the agreement refutes it.

     This is why [pipe_reg] is a real credential and not a decoration: the
     ONLY ways to hold one are the taint (below) and an invariant that owns
     the fragment (lane PIPE-PROTO). *)
  Lemma pipe_reg_not_free (γ : gname) :
    pipe_clink γ true emp -∗ pipe_qauth γ pst0 -∗ pipe_qfrag γ pst0 ={⊤}=∗ False.
  Proof using .
    rewrite /pipe_clink. iIntros "Hl Ha Hf".
    iMod ("Hl" $! pst0 with "Ha") as "[Ha _]".
    iDestruct (pipe_queue_agree with "Ha Hf") as %Heq.
    iModIntro. rewrite /pst_close /pst0 /= in Heq. discriminate Heq.
  Qed.

  (* ...and the positive half of the same exhibit: the fragment's holder
     buys ONE payment, at the cost of the fragment -- which is precisely
     why a program cannot carry the registry by holding the fragment, and
     why the registry is what a run carries. *)
  Lemma pipe_cpay_of_frag (γ : gname) (w : bool) (s : pipe_st) :
    pipe_qfrag γ s -∗ pipe_cpay γ w emp.
  Proof using .
    iIntros "Hf". rewrite /pipe_cpay. iLeft.
    iApply (pipe_clink_of_frag γ w emp s with "Hf").
    iIntros "_". by iModIntro.
  Qed.

  (* ===================================================================== *)
  (*  3.  THE TWO INTROS                                                   *)
  (* ===================================================================== *)

  (* THE TAINT STILL BUYS IT, so a caller that wants the old behaviour --
     an unverified program, or the generic-safety supply -- redeems with
     this and nothing changes for it ([PipeQueue.pipe_cpay_taint]). *)
  Lemma pipe_reg_of_taint (γp : pipe_names) :
    app_taint -∗ pipe_reg γp.
  Proof using .
    iIntros "#Ht". rewrite /pipe_reg. iIntros "!>" (w).
    iApply (pipe_cpay_taint (pn_queue γp) w emp). iExact "Ht".
  Qed.

  Lemma pipe_row_reg_of_taint (st : fdstate) :
    app_taint -∗ pipe_row_reg st.
  Proof using .
    iIntros "#Ht". rewrite /pipe_row_reg.
    destruct st as [| ? ? [| γp |]]; try done.
    iApply (pipe_reg_of_taint γp with "Ht").
  Qed.

  (* ...AND A ROW THAT IS NOT A PIPE REGISTERS ITSELF.  This is the law
     [UkRun.urun_nopipe_intro] runs on, and it is why a program that never
     calls pipe(2) pays nothing whatever (design/pipe.md). *)
  Lemma pipe_row_reg_nopipe (st : fdstate) :
    fdst_nopipe st -> ⊢ pipe_row_reg st.
  Proof using .
    intros Hnp. rewrite /pipe_row_reg.
    destruct st as [| ? ? [| γp |]]; [ done | done | exfalso; exact Hnp | done ].
  Qed.

  (* ===================================================================== *)
  (*  4.  WHAT IT PAYS: kexit's WHOLE ROW                                  *)
  (* ===================================================================== *)

  (* ONE INSTANCE OF EACH ROW'S [□], and that is the whole of exit's
     bundle row ([SpecFileclose.fileclose_cpays sts] is
     [[∗ list] st ∈ sts, fileclose_cpay st emp], and [fileclose_cpay] at a
     pipe row IS [pipe_cpay (pn_queue γp) w emp]).  The [∗ list] of
     INDEPENDENT payments that could not be paid from one exclusive
     fragment (completed/pipe-queue.md, "Open, recorded", second bullet)
     is paid here row by row. *)
  Lemma fileclose_cpay_of_reg (st : fdstate) :
    pipe_row_reg st -∗ fileclose_cpay st emp.
  Proof using .
    rewrite /pipe_row_reg /fileclose_cpay.
    destruct st as [| ? w [| γp |]]; try (by iIntros "_").
    iIntros "#Hr". iApply "Hr".
  Qed.

  (* ...AND THE SAME ROW AT A PAYLOAD THE REGISTRY CAN REACH.  close(21)'s
     bundle row is [fileclose_cpay st (cl_P f)] at the family the caller
     deposited at, and the POINT family's [cl_P] is [True]
     ([UexecExecInst.xfam_pt]) -- so a registered row pays its own close
     too, for a caller that reads nothing back from it.  What the registry
     CANNOT pay is a payload carrying a resource: the close link's fupd
     places [emp] and can therefore place only what [emp] entails.  This is
     what lets a pipe-holding program close its own ends
     ([UexecExecInst.xv6_sbundle_close_of_reg]); a caller that wants close's
     post has to hold something else. *)
  Lemma pipe_cpay_of_reg_true (γp : pipe_names) (w : bool) :
    pipe_reg γp -∗ pipe_cpay (pn_queue γp) w True.
  Proof using .
    iIntros "#Hr". rewrite /pipe_reg.
    iDestruct ("Hr" $! w) as "[Hl | #Ht]"; rewrite /pipe_cpay;
      [ iLeft | by iRight ].
    iApply (pipe_clink_mono (pn_queue γp) w emp True%I with "[] Hl").
    iIntros "_". done.
  Qed.

  Lemma fileclose_cpay_of_reg_true (st : fdstate) :
    pipe_row_reg st -∗ fileclose_cpay st True.
  Proof using .
    rewrite /pipe_row_reg /fileclose_cpay.
    destruct st as [| ? w [| γp |]]; try (by iIntros "_").
    iIntros "#Hr". iApply (pipe_cpay_of_reg_true γp w with "Hr").
  Qed.

  Lemma fileclose_cpays_of_regs (sts : list fdstate) :
    ([∗ list] st ∈ sts, pipe_row_reg st) -∗ fileclose_cpays sts.
  Proof using .
    rewrite /fileclose_cpays. iApply big_sepL_mono.
    iIntros (k st _) "H". iApply (fileclose_cpay_of_reg st with "H").
  Qed.

  (* ===================================================================== *)
  (*  5.  THE TABLE'S ROWS, as a big-op the run can carry                   *)
  (* ===================================================================== *)
  (* The four moves a syscall makes on a descriptor table, at the
     RESOURCE.  Every row is persistent, so a copy costs nothing and an
     overwritten row is simply dropped; the lemmas are stated here rather
     than in [UkRun] so that the induction is in one place and the engine's
     own steps ([UkRun.urun_nopipe_insert] and its three siblings) are one
     line each.  Stated at an ARBITRARY row predicate, because that is all
     the proofs use -- and because the class field the engine reads them
     through ([UexecSG.srow_reg]) is not this one. *)
  Lemma fd_rows_insert (R : fdstate -> iProp Σ) (l : list fdstate) (k : nat)
      (st : fdstate) :
    ([∗ list] s ∈ l, R s) -∗ R st -∗ ([∗ list] s ∈ <[k := st]> l, R s).
  Proof using .
    iInduction l as [| s l] "IH" forall (k); [ by iIntros "_ _" | ].
    destruct k as [| k]; cbn [list_insert].
    - iIntros "[_ Ht] Hst". iFrame "Hst Ht".
    - iIntros "[Hh Ht] Hst". iFrame "Hh".
      iApply ("IH" with "Ht Hst").
  Qed.

  Lemma fd_rows_lookup (R : fdstate -> iProp Σ) (l : list fdstate) (k : nat)
      (st : fdstate) :
    (forall s : fdstate, Persistent (R s)) ->
    l !! k = Some st -> ([∗ list] s ∈ l, R s) -∗ R st.
  Proof using .
    intros Hpers Hk. iIntros "H".
    iDestruct (big_sepL_lookup_acc (fun _ s => R s) l k st Hk with "H")
      as "[#Hst _]".
    iExact "Hst".
  Qed.

End PipeReg.
