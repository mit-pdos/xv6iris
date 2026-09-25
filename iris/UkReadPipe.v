(* ===================================================================== *)
(* UkReadPipe.v -- THE PIPE ARM OF THE GENERIC READ LEAF.                  *)
(*                                                                        *)
(* design/user-read.md section 3's PIPE row, on RD-4's shape: supplier ->  *)
(* content post -> leaf, the walk taken from                               *)
(* [UkRunSys.wp_uk_ecall_read_at] (the ONE read walk, parametric in the    *)
(* descriptor resource [D] and the pure reading [K] of the key's table)    *)
(* and the deposit an instance of [UkRunSys.udepwf_K].                     *)
(*                                                                        *)
(* THE BYTE QUEUE LANDED, and with it everything this file's first version *)
(* recorded as owed (design/pipe.md, "The byte queue").  A pipe now        *)
(* carries a fifth ghost name, [PipeNames.pn_queue], over an [excl_auth]   *)
(* of [PipeNames.pipe_st] -- every byte ever written, the read pointer and *)
(* the two open flags -- whose AUTHORITY sits in [pi->lock]'s payload      *)
(* coupled to the ring ([PipeInvDefs.pipe_qres]) and whose EXACT FRAGMENT  *)
(* [sys_pipe] hands the creating process.  So:                             *)
(*                                                                        *)
(*  - THE PAYMENT IS NO LONGER [emp].  [SpecFileread.fileread_in] at       *)
(*    [FdOpen true _ (FdPipe γp)] is the caller's payload BESIDE           *)
(*    [PipeQueue.pipe_rpay]: a per-byte READ CHAIN at the caller's own     *)
(*    cursor over what it dequeues, with an OBSERVATION node fired where   *)
(*    the ring runs dry -- or the taint.  [udepwf_st_read_pipe] takes it   *)
(*    as it stands; building it out of the fragment                        *)
(*    ([PipeQueue.pipe_rlink_of_frag] / [pipe_olink_of_frag]) is the       *)
(*    holder's business, not this file's.                                  *)
(*  - AND THE POST TELLS SOMETHING.  [fileread_extra_core]'s pipe arm is   *)
(*    [PipeQueue.pipe_rpost_img]: the chain at the bytes actually          *)
(*    dequeued, those bytes read back out of the RESUME IMAGE (which the   *)
(*    walk's own two pure rows turn into a statement about the caller's    *)
(*    buffer function), and the STOP's reason -- request met, ring         *)
(*    observed empty, copy-out fault, or the reader's kill shot.  EOF is   *)
(*    then a fact about the ghost state and not an owed row: the empty     *)
(*    stop at nothing delivered carries [ps_wo s = false]                  *)
(*    ([PipeQueue.pipe_rstop]'s second arm).                               *)
(*                                                                        *)
(* WHAT IS STILL NOT SAID, and it is the same gap as before: the           *)
(* COUNT/WINDOW JOIN.  The walk hands out a window length [d] (the bytes   *)
(* [UsysMemOk.usys_mem_ok] says the call wrote) and the post hands out a   *)
(* return value [r]; at the INODE arm [FsAbsReadFire.read_post_ok] ties    *)
(* them and at the CONSOLE arm [SpecFileread.console_receipt] does.  At a  *)
(* pipe the post's own [pipe_rstop] ties [r] to the delivered count, but   *)
(* nothing ties either to the WALK's [d], so a program still cannot        *)
(* conclude that its buffer above [r] is unchanged.  That is a kernel-side *)
(* row, not a U-tier one; the continuation below hands [d] and [r] over    *)
(* separately and claims no equation between them.                         *)
(*                                                                        *)
(* [uread_pipe_ans] survives unchanged: it is [PipeInvDefs.pipe_rw_ret] at *)
(* the caller's own [nat] count, and -1 is NOT refuted here (a pipe read   *)
(* really does answer -1 when the reader is killed asleep, or when the     *)
(* very first copy-out faults).                                            *)
(*                                                                        *)
(* ON [UkReadFile]: this file takes two ARM-INDEPENDENT names from         *)
(* [UkReadRows.v] -- [udepwf_st] (the STATE-fixed deposit, which is        *)
(* [UkRunSys.udepwf_K] at the handle reading) and [ufd_key_agree] (that    *)
(* reading, taken where both halves are in one hand).                      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.             (* [fdstate] / [fd_lowest_closed] *)
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import PipeInvDefs.         (* [pipe_rw_ret] -- what read answers here *)
Require Import PipeNames.           (* [pipe_names] / [pipe_st] / [pst0] *)
Require Import PipeQueue.           (* [pipe_rpay] / [pipe_rpost_img] / [pipe_qfrag] *)
Require Import PipeReg.             (* [pipe_reg]: THE REGISTRY the caller hands back *)
Require Import ChildTok.            (* [kill_shot] -- the -1-by-kill arm *)
Require Import UexecExecInst.       (* THE INSTANCE: [spost_at_pipe_elim], [xfam] *)
Require Import UserPtTree.          (* [uptd] -- the page-table view the post is at *)
Require Import UserFd.
Require Import UserHeap.
Require Import ProcGeom.            (* [NOFILE] / [NSTD] / [tf_arg_idx] *)
Require Import VcGen.               (* [trunc32] *)
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UkReadRows.          (* the shared key-level rows *)
Require Import SpecFileread.        (* [fileread_in] / [fileread_ret] *)
Require Import SpecSysRead.         (* [sys_rw_count] *)
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

Section UkReadPipe.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  (* THE PROGRAM'S SUPPLY CLASS IS GENERALIZED and not resolved here, for
     [UkReadCons.v]'s reason (RD-4): the kernel's own instance is
     [UexecExecInst.uprogSG_gen] and a program whose numbers are free runs
     at [uprogSG_free]; the two are NOT convertible, so a leaf that fixes
     one cannot be applied by a program at the other. *)
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  1.  THE FAMILY                                                      *)
  (* =================================================================== *)
  (* THE CHOICE IS NO LONGER IMMATERIAL (design/pipe.md, "The byte
     queue").  Row 5's pipe arm reads TWO family fields now -- [rf_pq], the
     caller's cursor over the bytes it takes OUT of the pipe, and [rf_pqe],
     its observation at a stop on an empty ring -- so the member is stated
     at a caller's own pair.  Everything else is [UkReadRows.xfam_rd] at
     the trivial readings: the console fields and the inode receipt are
     unread at a pipe descriptor. *)
  Definition read_pipe_fam (Q : Z -> iProp Σ)
      (Rp : list (bv 8) -> iProp Σ)
      (Rpe : list (bv 8) -> pipe_st -> iProp Σ) : sfam :=
    let f0 := xfam_rd Q (fun _ _ => True%I) (fun _ => True%I) in
    {| xf_P      := xf_P f0;
       xf_Pmiss  := xf_Pmiss f0;
       xf_Fo     := xf_Fo f0;
       xf_Rs     := xf_Rs f0;
       rf_F      := rf_F f0;
       cf_P      := cf_P f0;
       cf_Pmiss  := cf_Pmiss f0;
       cf_Fo     := cf_Fo f0;
       of_P      := of_P f0;
       of_Pmiss  := of_Pmiss f0;
       of_Farm   := of_Farm f0;
       of_Fun    := of_Fun f0;
       of_Fok    := of_Fok f0;
       of_Fex    := of_Fex f0;
       of_Fo     := of_Fo f0;
       of_Ft     := of_Ft f0;
       of_om    := OffParked;
       wf_Q      := wf_Q f0;
       nf_P      := nf_P f0;
       nf_Pmiss  := nf_Pmiss f0;
       nf_Farm   := nf_Farm f0;
       nf_Fun    := nf_Fun f0;
       nf_Fok    := nf_Fok f0;
       nf_Fex    := nf_Fex f0;
       uf_P      := uf_P f0;
       uf_Pmiss  := uf_Pmiss f0;
       uf_Fent   := uf_Fent f0;
       uf_Ftgt   := uf_Ftgt f0;
       uf_Fex    := uf_Fex f0;
       uf_Fmiss  := uf_Fmiss f0;
       lf_Ftgt   := lf_Ftgt f0;
       lf_Fent   := lf_Fent f0;
       lf_Funt   := lf_Funt f0;
       df_P      := df_P f0;
       df_Pmiss  := df_Pmiss f0;
       df_Farm   := df_Farm f0;
       df_Fdots  := df_Fdots f0;
       df_Fun    := df_Fun f0;
       df_Fok    := df_Fok f0;
       df_Fex    := df_Fex f0;
       kf_pay    := kf_pay f0;
       kf_lend   := kf_lend f0;
       kf_xpay   := kf_xpay f0;
       rf_ret    := rf_ret f0;
       rf_in     := rf_in f0;
       rf_pq     := Rp;
       rf_pqe    := Rpe;
       wf_Qe     := wf_Qe f0;
       cl_P      := cl_P f0 |}.

  (* =================================================================== *)
  (*  2.  THE DEPOSIT'S SUPPLIER: THE PIPE'S REAL PAYMENT                  *)
  (* =================================================================== *)
  (* The whole price of a pipe read, and it is no longer [emp]:
     [SpecFileread.fileread_in] at [FdOpen true _ (FdPipe γp)] is the
     caller's own payload BESIDE [PipeQueue.pipe_rpay] -- one read link per
     byte the call may dequeue, at the caller's cursor, or the taint.  A
     holder of the pipe's exact fragment builds the chain out of
     [PipeQueue.pipe_rlink_of_frag] and [pipe_olink_of_frag]; a caller with
     neither pays the taint ([pipe_rpay_taint]).  The supplier takes it as
     it stands, which is what keeps this file out of the business of
     deciding which. *)
  Lemma udepwf_st_read_pipe (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (wb : bool) (γp : pipe_names)
      (Rp : list (bv 8) -> iProp Σ)
      (Rpe : list (bv 8) -> pipe_st -> iProp Σ) :
    pipe_rpay (pn_queue γp) Rp Rpe
      (Z.to_nat (sys_rw_count (m !!! Regidx a2_idx))) -∗
    udepwf_st N m pc USYS_read (read_pipe_fam (ukn_pay N) Rp Rpe)
      (FdOpen true wb (FdPipe γp)).
  Proof using .
    iIntros "Hpay".
    rewrite /udepwf_st. iSplit; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Hkey _ Hheap Hufd".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_read_intro uslot (read_pipe_fam (ukn_pay N) Rp Rpe)
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              (m !!! Regidx a0_idx) (m !!! Regidx a2_idx) fdv
              (tf_of_arg0 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all)).
    rewrite Hkey. rewrite /fileread_in /=. iIntros "$". iExact "Hpay".
  Qed.

  (* ...AND THE POST'S PIPE ARM, read off [fileread_extra_core] at a state
     the walk holds through an equation.  [SpecFileread] states the
     introduction ([fileread_extra_pipe]); this is the elimination, and it
     is the match at one constructor. *)
  (* the family's three READ fields go in through the record rather than by
     name, so this file does not have to import the vocabulary of the two
     arms it is not about *)
  Lemma uread_pipe_core (gn : gname) (pt : uptd) (st : fdstate) (wb : bool)
      (γp : pipe_names) (n : Z) (fm : xfam)
      (Rp : list (bv 8) -> iProp Σ) (Rpe : list (bv 8) -> pipe_st -> iProp Σ)
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64) :
    st = FdOpen true wb (FdPipe γp) ->
    fileread_extra_core gn pt st n (rf_F fm) (rf_ret fm) (rf_in fm)
      Rp Rpe r M' addr -∗
    pipe_rpost_img pt (pn_queue γp) Rp Rpe (ChildTok.kill_shot gn ∗ app_taint)%I
      (Z.to_nat n) r M' addr.
  Proof using . intros ->. by iIntros "$". Qed.

  (* =================================================================== *)
  (*  3.  THE CONTENT POST                                                *)
  (* =================================================================== *)
  (* ...WHICH IS PURE, and that is the whole of section 3's Pipe row as the
     tree supports it today (the header).  It is
     [PipeInvDefs.pipe_rw_ret] -- piperead's and pipewrite's shared return
     convention -- read at the caller's own [nat] request, which is the
     form a program that asked for [cap] bytes wants: either the call
     failed, or it delivered a count no larger than the request. *)
  Definition uread_pipe_ans (cap : nat) (r : mword 64) : Prop :=
    r = (mword_of_int (-1) : mword 64)
    \/ exists d : nat, r = (mword_of_int (Z.of_nat d) : mword 64)
                       /\ (d <= cap)%nat.

  Lemma uread_pipe_ans_of_ret (cap : nat) (r : mword 64) :
    fileread_ret (Z.of_nat cap) r -> uread_pipe_ans cap r.
  Proof using .
    rewrite /fileread_ret /pipe_rw_ret /uread_pipe_ans.
    intros [Hm1 | (i & Hi & Hb)]; [ by left | right ].
    assert (Hmax : Z.max 0 (Z.of_nat cap) = Z.of_nat cap) by lia.
    rewrite Hmax in Hb.
    exists (Z.to_nat i). split; [ rewrite Z2Nat.id; [ exact Hi | lia ] | lia ].
  Qed.

  (* =================================================================== *)
  (*  4.  THE LEAF                                                        *)
  (* =================================================================== *)
  (* [UkRunSys.wp_uk_ecall_read_at]'s walk at the PIPE arm.  The three
     differences from the console member are all in the descriptor, exactly
     as they are for the file member: the deposit is fixed at the STATE the
     caller's handle names rather than at the low [NSTD] ledger, what goes
     down and comes back is one [UserFd.ufd] rather than the whole ledger,
     and what the caller is told about the key is the arm itself.

     NO PAYMENT ARGUMENT, and no family argument either: there is nothing
     for a caller to choose (section 2 above).  The buffer's tail is pinned
     above the WINDOW LENGTH [d] and NOT above the returned count -- the
     join between them is the owed row in the header. *)
  Lemma wp_uk_ecall_read_pipe (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (k cap : nat) (f : nat -> bv 8) (avail : nat)
      (fd : nat) (wb : bool) (γp : pipe_names)
      (Rp : list (bv 8) -> iProp Σ)
      (Rpe : list (bv 8) -> pipe_st -> iProp Σ) :
    usysno m = USYS_read ->
    (* THE DESCRIPTOR IS THE ONE THE HANDLE NAMES; a0 carries it as a C
       [int], so the reading is the signed low word *)
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    uint (m !!! Regidx a2_idx) = Z.of_nat cap ->
    (cap <= k)%nat ->
    (* the kernel answers the SIGNED 32-bit count, so the request the caller
       made is the request file.c read only below the sign boundary *)
    (Z.of_nat cap < 2 ^ 31)%Z ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdPipe γp)) -∗
    (* THE PAYMENT: the caller's own read chain over the byte queue, or the
       taint (design/pipe.md, "The byte queue") *)
    pipe_rpay (pn_queue γp) Rp Rpe cap -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8)
       (M' : gmap Z (bv 8)) (Pt : uptd) (Rk : iProp Σ),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ⌜ uread_pipe_ans cap r ⌝ -∗
       (* THE RESUME IMAGE HOLDS THE CALLER'S BUFFER, which is what turns
          the post's IMAGE reading of the dequeued bytes into a statement
          about [g] -- the two pure rows the walk alone can state. *)
       ⌜ forall i : nat, (i < k)%nat ->
           uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat i))
           = (uint (m !!! Regidx a1_idx) + Z.of_nat i)%Z ⌝ -∗
       ⌜ forall j : nat, (j < k)%nat ->
           M' !! uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))
           = Some (g j) ⌝ -∗
       (* ...AND THE ANSWER: the chain at the dequeued bytes, the stop's
          reason -- request met, ring observed empty (an end-of-file when
          nothing came), copy-out fault, or the reader's kill shot [Rk] --
          or the taint with the payment back. *)
       pipe_rpost_img Pt (pn_queue γp) Rp Rpe Rk cap r M'
         (m !!! Regidx a1_idx) -∗
       UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdPipe γp)) -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Ha0 Hfdlt Ha2 Hcapk Hcap31 Hal.
    iIntros "#Hi Hrun Hufdh Hpay Hbuf Hcont".
    assert (Hcnt : sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat cap)
      by exact (uread_count_is_cap (m !!! Regidx a2_idx) cap Ha2 Hcap31).
    assert (Hcw : bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0
                             : mword 32) = Z.of_nat cap).
    { rewrite /sys_rw_count trunc32_subrange in Hcnt. exact Hcnt. }
    iPoseProof (udepwf_st_read_pipe N m pc wb γp Rp Rpe with "[Hpay]") as "Hsb";
      [ rewrite Hcnt Nat2Z.id; iExact "Hpay" | ].
    iApply (wp_uk_ecall_read_at N h m pc (Z.of_nat cap) k f avail
              (read_pipe_fam (ukn_pay N) Rp Rpe)
              (UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdPipe γp)))
              (fun fdv => fd_st_of_key (m !!! Regidx a0_idx) fdv
                          = FdOpen true wb (FdPipe γp))
              Hn Hcw ltac:(rewrite Nat2Z.id; exact Hcapk) Hal
              (ufd_key_agree N fd (FdOpen true wb (FdPipe γp))
                 (m !!! Regidx a0_idx) Ha0 Hfdlt)
              with "Hi Hrun [Hsb] Hufdh Hbuf").
    { rewrite /udepwf_st /udepwf_K. iExact "Hsb". }
    iIntros (h' r d g W M' fdv' cw' cs')
      "%Hd %Hgf %Hlin %Himg %Hnf %H0 %H1 %H2 %Hkey %Hlz %Hlive
       Hufdh Hpost Hrun Hbuf".
    iDestruct (spost_at_read_elim uslot (read_pipe_fam (ukn_pay N) Rp Rpe) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W) r M' fdv' cw' cs'
                 H0 H1 H2 eq_refl with "Hpost")
      as "[%Hret Hcore]".
    iDestruct "Hcore" as (P) "(%Hpmp & %Hwfp & %Hlzp & Hcore)".
    (* THE ARM IS THE PIPE'S OWN POST NOW (design/pipe.md): the chain at
       the bytes the call dequeued, the buffer holding them in the RESUME
       IMAGE, and the stop's reason. *)
    iDestruct (uread_pipe_core (uvis_gen W) P
                 (fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W)) wb γp
                 (sys_rw_count (m !!! Regidx a2_idx))
                 (read_pipe_fam (ukn_pay N) Rp Rpe)
                 Rp Rpe r M' (m !!! Regidx a1_idx) Hkey with "Hcore")
      as "Hrp".
    rewrite Hcnt in Hret.
    rewrite Hcnt Nat2Z.id.
    rewrite Nat2Z.id in Hd.
    iApply ("Hcont" $! h' r d g M' P ((ChildTok.kill_shot (uvis_gen W) ∗ app_taint)%I)
              with "[%] [%] [%] [%] [%] Hrp Hufdh Hrun Hbuf");
      [ exact Hd | exact Hgf | exact (uread_pipe_ans_of_ret cap r Hret)
      | exact Hlin | exact Himg ].
  Qed.

  (* =================================================================== *)
  (*  5.  THE CONSUMER TEST -- THE SEAM AT sys_pipe                        *)
  (* =================================================================== *)
  (* WHAT THE TEST CAN BE, and why it is this.  The test the lane owes is
     "a program holding the read end learns the writer's bytes across the
     two ends"; the content half of that is not derivable at any tier today
     (the header), and neither is a one-process write-then-read, for the
     same reason and no other -- a pipe read's post is [emp].  What IS
     derivable, and what actually has to hold for the member above to be
     reachable by a real program, is the SEAM: the two descriptors
     [sys_pipe] hands back are handles at exactly the two states the read
     and write members case on.  [UsysMemOk.usys_pipe_ok]'s join is what
     makes the bytes in the caller's [int fd[2]] name those slots, and
     [UkRunSys.wp_uk_ecall_pipe] already spends it; this lemma is that
     leaf's post read one step further, into the two members' own premises.

     THE SECOND CALL IS NOT IN THE TEST, and cannot be: the descriptor
     arrives in the caller's BUFFER and a program has to load it into a0
     with its own instructions before the read's ecall.  So the two ends
     are handed over at the first call's continuation, where a program
     proof picks them up. *)

  (* the ledger does not move when every standard slot is open: pipe's two
     allocations both land above [NSTD], so each [ustd_after] is the
     identity. *)
  Lemma ustd_after_none (l : list fdstate) (st : fdstate) :
    fd_lowest_closed l = None -> ustd_after l st = l.
  Proof using . intros H. rewrite /ustd_after H. reflexivity. Qed.

  (* the join's U-tier reading, at a ledger with no free standard slot --
     which is where any program that has not just closed a standard stream
     is, and the only case in which pipe's two arms are HANDLES rather than
     ledger writes. *)
  Lemma upipe_ends_handles (N : uk_names Σ) (l : list fdstate) (a b : nat)
      (γp : pipe_names) :
    fd_lowest_closed l = None ->
    ualloc_at (ukn_fd N) l a (FdOpen true false (FdPipe γp)) -∗
    ualloc_at (ukn_fd N) (ustd_after l (FdOpen true false (FdPipe γp))) b
      (FdOpen false true (FdPipe γp)) -∗
    UserFd.ufd (ukn_fd N) a (FdOpen true false (FdPipe γp)) ∗
    UserFd.ufd (ukn_fd N) b (FdOpen false true (FdPipe γp)).
  Proof using .
    intros Hnone.
    rewrite (ustd_after_none l (FdOpen true false (FdPipe γp)) Hnone).
    rewrite /ualloc_at Hnone.
    iIntros "[_ Ha] [_ Hb]". iFrame "Ha Hb".
  Qed.

  Lemma wp_uk_pipe_read_end (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (f : nat -> bv 8) (avail : nat)
      (Rp : pipe_names -> iProp Σ) :
    usysno m = USYS_pipe ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    fd_lowest_closed l = None ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_pipe -∗
    (* THE REGISTRAR, WHERE THE TAINT USED TO BE (design/app-pipe.md SS2,
       lane PIPE-REG).  This is [UkRunSys.wp_uk_ecall_pipe]'s registrar read
       at the INSTANCE, which is the only place the pipe's exact fragment
       can be named: the caller takes the new pipe's byte-queue fragment at
       the birth state and hands back the pipe's REGISTRATION -- the [□]
       -guarded close payment at either end, which is what the run's
       [UkRun.urun_nopipe] carries for each of the two new rows and what
       the dying process's exit spends.  It keeps whatever it made of the
       fragment, as [Rp γp], and that is what the post below hands over in
       the fragment's place: lane PIPE-PROTO's [pipe_proto_alloc] is the
       instance of record ([Rp γp := ∃ pn, pipe_inv pn γp L ∗ wtok]).

       REGISTERING CONSUMES THE FRAGMENT, necessarily: a registration is a
       [□] and one fragment buys exactly one payment
       ([PipeReg.pipe_cpay_of_frag]), so the fragment cannot both found the
       registry and come back out.  A caller that wants the OLD behaviour
       takes [Rp γp := pipe_qfrag (pn_queue γp) pst0] and answers from the
       credential ([PipeReg.pipe_reg_of_taint]), and nothing about it has
       changed. *)
    (∀ γp : pipe_names,
       pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗ pipe_reg γp ∗ Rp γp) -∗
    ustd (ukn_fd N) l -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a0_idx)) 8 f -∗
    (∀ (h' : CpuId) (r : mword 64) (g : nat -> bv 8),
       ((∃ (a b : nat) (γp : pipe_names),
           ⌜ uint r = 0 /\ a <> b /\ (a < NOFILE)%nat /\ (b < NOFILE)%nat
             /\ (forall i : nat, (i < 8)%nat ->
                   g i = if (i <? 4)%nat
                         then nth_byte
                                (trunc32 (mword_of_int (Z.of_nat a)
                                          : mword 64)) i
                         else nth_byte
                                (trunc32 (mword_of_int (Z.of_nat b)
                                          : mword 64)) (i - 4)%nat) ⌝ ∗
           (* THE TWO ENDS, AT THE TWO MEMBERS' OWN PREMISES: [a] is
              [wp_uk_ecall_read_pipe]'s handle and [b] is the write
              member's -- AND BOTH NAME ONE PIPE, [γp]. *)
           UserFd.ufd (ukn_fd N) a (FdOpen true false (FdPipe γp)) ∗
           UserFd.ufd (ukn_fd N) b (FdOpen false true (FdPipe γp)) ∗
           ustd (ukn_fd N) l ∗
           (* ...AND WHAT THE REGISTRAR MADE OF THE BYTE QUEUE'S EXACT
              FRAGMENT AT THE BIRTH STATE (design/pipe.md, "The byte
              queue"; design/app-pipe.md SS2).  The fragment itself went
              into the registration the run now carries for the two new
              rows -- it had to, a registration being a [□] -- and this is
              the caller's own successor of it, at the [γp] the two handles
              are ends of. *)
           Rp γp)
        (* ...OR THE CALL FAILED, AT -1 (lane PIPE-NEG1): the leaf's own
           failure arm, which the row now pins, relayed unchanged.  sh's
           PIPE arm is what needs the sign -- [bltz a0] -- and this is the
           end of the chain that carries it. *)
        ∨ (⌜ r = (mword_of_int (-1) : mword 64) ⌝ ∗ ustd (ukn_fd N) l)) -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a0_idx)) 8 g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal Hnone.
    iIntros "#Hi Hrun Hsb Hreg Hstd Hbuf Hcont".
    (* THE CLASS-LEVEL REGISTRAR, BUILT HERE.  The leaf below is stated
       over the deposit class and cannot open row 4's post, so what it
       takes is a fupd from that post to the two new rows' registration;
       this is that fupd at the instance, and [Rp'] is the shape the post
       leaves behind -- [spost_at_pipe_elim]'s own, with the fragment
       replaced by the caller's successor.  On a FAILED call the post
       promises nothing, the table did not move (the leaf's pure premise
       says so), and the run's own reading answers for free. *)
    iApply (wp_uk_ecall_pipe N h m pc l f avail
              (fun (fdep : sfam) (W : uvis) (r : mword 64) (M' : gmap Z (bv 8))
                   (fdv' : list fdstate) (cw' : Z) (cs' : gset gname) =>
                 (⌜uint r = 0⌝ -∗
                  ∃ (a b : nat) (γp : pipe_names),
                    ⌜a <> b /\ fd_least_closed (uvis_fd W) a
                     /\ fd_least_closed
                          (<[a := FdOpen true false (FdPipe γp)]> (uvis_fd W)) b
                     /\ fdv' = <[b := FdOpen false true (FdPipe γp)]>
                                 (<[a := FdOpen true false (FdPipe γp)]>
                                    (uvis_fd W))⌝ ∗ Rp γp)%I)
              Hn Hal with "Hi Hrun Hsb [Hreg] Hstd Hbuf").
    { iIntros (fdep W r M' fdv' cw' cs') "%Hfail #Hnpw Hsp".
      destruct (decide (uint r = 0)) as [Hr0 | Hr0].
      - iDestruct (spost_at_pipe_elim uslot fdep W r M' fdv' cw' cs' with "Hsp")
          as "Hsp".
        iSpecialize ("Hsp" with "[%]"); [ exact Hr0 | ].
        iDestruct "Hsp" as (a2 b2 γp2) "[%Hp2 Hfrag]".
        destruct Hp2 as (Hne2 & Hca2 & Hcb2 & Hfdv2).
        iMod ("Hreg" $! γp2 with "Hfrag") as "[#Hpr HRp]".
        iModIntro. iSplitR "HRp".
        + (* the two rows go in REGISTERED, read end first, and the run's
             reading survives pipe(2) -- which is the wall coming down *)
          rewrite Hfdv2.
          iAssert (urun_nopipe
                     (<[a2 := FdOpen true false (FdPipe γp2)]> (uvis_fd W)))
            as "#Hnp1";
            [ iApply (urun_nopipe_insert_reg (uvis_fd W) a2
                        (FdOpen true false (FdPipe γp2)) with "[] Hnpw");
              iApply (srow_reg_of_pipe_reg true false γp2 with "Hpr") | ].
          iApply (urun_nopipe_insert_reg _ b2
                    (FdOpen false true (FdPipe γp2)) with "[] Hnp1").
          iApply (srow_reg_of_pipe_reg false true γp2 with "Hpr").
        + (* ...and the residue the caller kept, at the post's own two
             slots and its own [γp] *)
          iIntros "_". iExists a2, b2, γp2. iSplitR; [ | iExact "HRp" ].
          iPureIntro. split_and!;
            [ exact Hne2 | exact Hca2 | exact Hcb2 | exact Hfdv2 ].
      - (* THE CALL FAILED: no pipe, no new row, and the fd row's
           else-branch says the table did not move -- so the run's own
           reading answers and the registrar is free *)
        iModIntro. rewrite (Hfail Hr0). iSplitL; [ iExact "Hnpw" | ].
        iIntros "%Hc". exfalso. exact (Hr0 Hc). }
    iIntros (h' r g W fdep M' fdv' cw' cs') "Harm HRp' Hrun Hbuf".
    iApply ("Hcont" $! h' r g with "[Harm HRp'] Hrun Hbuf").
    iDestruct "Harm" as "[Hok | Hbad]"; [ | iRight; iExact "Hbad" ].
    iDestruct "Hok" as (a b γp) "(%Hpure & Hra & Hrb & Hstd)".
    destruct Hpure as (Hr0 & Hne & Halt & Hblt & Hbytes & Hca & Hcb & Hfdv').
    (* THE REGISTRAR'S RESIDUE, READ HERE.  The post's two slots are a
       SECOND least-closed scan of the same table, so
       [UkRunSys.upipe_names_agree] identifies the pipe it is about with
       the one the two handles are ends of. *)
    iSpecialize ("HRp'" with "[%]"); [ exact Hr0 | ].
    iDestruct "HRp'" as (a2 b2 γp2) "[%Hp2 HRp]".
    destruct Hp2 as (Hne2 & Hca2 & Hcb2 & Hfdv2).
    pose proof (upipe_names_agree (uvis_fd W) fdv' a b a2 b2 γp γp2
                  Hca Hcb Hfdv' Hca2 Hcb2 Hfdv2) as Hgamma.
    subst γp2.
    iDestruct (upipe_ends_handles N l a b γp Hnone with "Hra Hrb")
      as "[Hha Hhb]".
    (* the ledger comes home UNMOVED: both allocations landed above the
       standard streams, so [ustd_after] is the identity at each step *)
    rewrite (ustd_after_none l (FdOpen true false (FdPipe γp)) Hnone).
    rewrite (ustd_after_none l (FdOpen false true (FdPipe γp)) Hnone).
    iLeft. iExists a, b, γp. iSplitR; [ by iPureIntro | ].
    iFrame "Hha Hhb Hstd HRp".
  Qed.


  (* =================================================================== *)
  (*  6.  THE LEDGER SLOT (design/app-pipe.md SS5.4; lane PIPE-STD)        *)
  (*                                                                      *)
  (*  cat reads fd 0, which is BELOW [NSTD]: its descriptor knowledge is    *)
  (*  the whole LEDGER ([UserFd.ustd]) and its deposit is fixed at it       *)
  (*  ([UkRun.udepwf_std]), while section 4's member is handle-fixed        *)
  (*  ([UserFd.ufd] carries [NSTD <= fd]).  These two are that member's     *)
  (*  ledger twins and nothing else: same walk, same family, same payment,  *)
  (*  same post -- only the descriptor knowledge and the deposit's reading  *)
  (*  change.  [UkWritePipe.v] section 4 is the write side of the same      *)
  (*  move, and its header has the two notes that apply here too: the slot  *)
  (*  is a PARAMETER (not pinned at 0) and the freedom a pipe row has where *)
  (*  the file leaf had an offset mode is the WRITE flag [wb].               *)
  (* =================================================================== *)

  (* THE DEPOSIT AT A LEDGER SLOT, [udepwf_st_read_pipe]'s twin: the arm is
     computed from the caller's own ledger rather than from a handle, and
     the payment is taken exactly as it stands. *)
  Lemma udepwf_std_read_pipe (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (l : list fdstate) (fd : nat) (wb : bool) (γp : pipe_names)
      (Rp : list (bv 8) -> iProp Σ)
      (Rpe : list (bv 8) -> pipe_st -> iProp Σ) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen true wb (FdPipe γp)) ->
    pipe_rpay (pn_queue γp) Rp Rpe
      (Z.to_nat (sys_rw_count (m !!! Regidx a2_idx))) -∗
    udepwf_std N m pc USYS_read (read_pipe_fam (ukn_pay N) Rp Rpe) l.
  Proof using .
    intros H0 Hlt Hl. iIntros "Hpay".
    rewrite /udepwf_std. iSplit; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Htake _ Hheap Hufd".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_read_intro uslot (read_pipe_fam (ukn_pay N) Rp Rpe)
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              (m !!! Regidx a0_idx) (m !!! Regidx a2_idx) fdv
              (tf_of_arg0 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all)).
    rewrite (std_fd_st_of_key (m !!! Regidx a0_idx) fdv l fd
               (FdOpen true wb (FdPipe γp)) H0 Hlt Htake Hl).
    rewrite /fileread_in /=. iIntros "$". iExact "Hpay".
  Qed.

  (* THE LEDGER-SLOT PIPE READ LEAF, [wp_uk_ecall_read_pipe]'s twin.  The
     one read walk at [K fdv := take NSTD fdv = l] with [UserFd.ustd] for
     [UserFd.ufd] and [UkRun.udepwf_std] for [udepwf_st]
     ([UserFd.ustd_agree] is the reading); EVERYTHING ELSE IS THE HANDLE
     LEAF'S -- the same [pipe_rpay] goes in, the same five pure rows and
     the same [pipe_rpost_img] come back, the buffer's tail is pinned
     above the same WINDOW LENGTH [d] and not above the returned count,
     and the ledger comes home unmoved (read moves no descriptor). *)
  Lemma wp_uk_ecall_read_pipe_std (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (k cap : nat) (f : nat -> bv 8) (avail : nat)
      (l : list fdstate) (fd : nat) (wb : bool) (γp : pipe_names)
      (Rp : list (bv 8) -> iProp Σ)
      (Rpe : list (bv 8) -> pipe_st -> iProp Σ) :
    usysno m = USYS_read ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (* THE DESCRIPTOR IS A LEDGER SLOT, and the ledger says it is this
       pipe's READ end *)
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen true wb (FdPipe γp)) ->
    uint (m !!! Regidx a2_idx) = Z.of_nat cap ->
    (cap <= k)%nat ->
    (Z.of_nat cap < 2 ^ 31)%Z ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* THE LEDGER, in place of the handle-fixed leaf's [UserFd.ufd] *)
    UserFd.ustd (ukn_fd N) l -∗
    (* THE PAYMENT: the caller's own read chain over the byte queue, or the
       taint (design/pipe.md, "The byte queue") *)
    pipe_rpay (pn_queue γp) Rp Rpe cap -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8)
       (M' : gmap Z (bv 8)) (Pt : uptd) (Rk : iProp Σ),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ⌜ uread_pipe_ans cap r ⌝ -∗
       ⌜ forall i : nat, (i < k)%nat ->
           uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat i))
           = (uint (m !!! Regidx a1_idx) + Z.of_nat i)%Z ⌝ -∗
       ⌜ forall j : nat, (j < k)%nat ->
           M' !! uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))
           = Some (g j) ⌝ -∗
       pipe_rpost_img Pt (pn_queue γp) Rp Rpe Rk cap r M'
         (m !!! Regidx a1_idx) -∗
       UserFd.ustd (ukn_fd N) l -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Ha0 Hlt Hl Ha2 Hcapk Hcap31 Hal.
    iIntros "#Hi Hrun Hstd Hpay Hbuf Hcont".
    assert (Hcnt : sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat cap)
      by exact (uread_count_is_cap (m !!! Regidx a2_idx) cap Ha2 Hcap31).
    assert (Hcw : bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0
                             : mword 32) = Z.of_nat cap).
    { rewrite /sys_rw_count trunc32_subrange in Hcnt. exact Hcnt. }
    iPoseProof (udepwf_std_read_pipe N m pc l fd wb γp Rp Rpe Ha0 Hlt Hl
                  with "[Hpay]") as "Hsb";
      [ rewrite Hcnt Nat2Z.id; iExact "Hpay" | ].
    iApply (wp_uk_ecall_read_at N h m pc (Z.of_nat cap) k f avail
              (read_pipe_fam (ukn_pay N) Rp Rpe)
              (UserFd.ustd (ukn_fd N) l)
              (fun fdv => take NSTD fdv = l)
              Hn Hcw ltac:(rewrite Nat2Z.id; exact Hcapk) Hal
              (fun fdv => ustd_agree (ukn_fd N) fdv l)
              with "Hi Hrun [Hsb] Hstd Hbuf").
    { iApply (udepwf_K_std N m pc USYS_read
                (read_pipe_fam (ukn_pay N) Rp Rpe) l with "Hsb"). }
    iIntros (h' r d g W M' fdv' cw' cs')
      "%Hd %Hgf %Hlin %Himg %Hnf %H0 %H1 %H2 %Htake %Hlz %Hlive
       Hstd Hpost Hrun Hbuf".
    iDestruct (spost_at_read_elim uslot (read_pipe_fam (ukn_pay N) Rp Rpe) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W) r M' fdv' cw' cs'
                 H0 H1 H2 eq_refl with "Hpost")
      as "[%Hret Hcore]".
    iDestruct "Hcore" as (P) "(%Hpmp & %Hwfp & %Hlzp & Hcore)".
    (* THE ARM, OUT OF THE CALLER'S OWN LEDGER: the key's low [NSTD] slots
       ARE the ledger ([Htake], the walk's row), so the row at [fd] is the
       state the call ran on. *)
    iDestruct (uread_pipe_core (uvis_gen W) P
                 (fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W)) wb γp
                 (sys_rw_count (m !!! Regidx a2_idx))
                 (read_pipe_fam (ukn_pay N) Rp Rpe)
                 Rp Rpe r M' (m !!! Regidx a1_idx)
                 (std_fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W) l fd
                    (FdOpen true wb (FdPipe γp)) Ha0 Hlt Htake Hl)
                 with "Hcore") as "Hrp".
    rewrite Hcnt in Hret.
    rewrite Hcnt Nat2Z.id.
    rewrite Nat2Z.id in Hd.
    iApply ("Hcont" $! h' r d g M' P ((ChildTok.kill_shot (uvis_gen W) ∗ app_taint)%I)
              with "[%] [%] [%] [%] [%] Hrp Hstd Hrun Hbuf");
      [ exact Hd | exact Hgf | exact (uread_pipe_ans_of_ret cap r Hret)
      | exact Hlin | exact Himg ].
  Qed.

End UkReadPipe.
