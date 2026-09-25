(* ===================================================================== *)
(*  UkWriteLeaf.v -- THE U-TIER WRITE LEAF'S CONCRETE HALF                *)
(*  (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM: DESIGN OF RECORD", (W);   *)
(*   lane IO-LEAF, first half.)                                          *)
(*                                                                       *)
(*  [UkRunSys.wp_uk_ecall_write_chain] is the leaf, and like every other  *)
(*  U-tier leaf it is stated against the ABSTRACT deposit class           *)
(*  ([UexecSG.sbundle_at] / [spost_at]): UkRunSys sits below the file     *)
(*  system and cannot name a row.  This file is where row 16 is named --  *)
(*  [UConsOpen.v] (open), [UInitConsK.v] (mknod) and [UShLine.v] (read)   *)
(*  are the three moulds, and this is the fourth:                         *)
(*                                                                       *)
(*    S1  THE FAMILY.  [UexecExecInst.xfam] at the ONE field row 16 reads *)
(*        ([wf_Q], the caller's own output cursor) and the payload field  *)
(*        every deposit must answer at ([kf_xpay]); trivial everywhere    *)
(*        else, because a deposit is read at one number.                  *)
(*    S2  THE TWO KEY-LEVEL ROWS, IN THE PROCESS'S DIRECTION.             *)
(*        [UexecExecInst] states row 16's deposit ELIM and its post INTRO *)
(*        -- the dispatcher's two -- so a process needs the other two.    *)
(*    S3  THE ARM, out of the caller's own ledger: which arm              *)
(*        [SpecFilewrite.filewrite_in] takes is decided by the KEY's      *)
(*        descriptor table, and what a program holds is the low [NSTD]    *)
(*        slots of it.  [UShLine.ush_fd_st_console] is the read's; this   *)
(*        is the same fact at an arbitrary standard descriptor (a write   *)
(*        goes to fd 1 or fd 2, never to fd 0).                           *)
(*    S4  THE SUPPLY: the process's chain, minted as the deposit.  The    *)
(*        chain is over the image [UkRun.udepwf_std]'s ∀ binds, so the    *)
(*        program supplies it against the heap the wand lends it --       *)
(*        [UkRunSys.uheap_ubytes_wat] is what turns a program's byte RUN  *)
(*        into the per-byte lookups the chain's nodes ask for.            *)
(*    S5  THE SMOKE TEST: a two-byte write paid from the OUTPUT LICENCE   *)
(*        at a cursor family that is not the trivial one, and the post    *)
(*        read back at that same family.  This is the anti-vacuity        *)
(*        witness: the deposit is satisfiable and the post says           *)
(*        something.                                                      *)
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
(* THE GHOST BINDER LIST, each module IMPORTED and not merely required --
   naming a class without its defining module in scope introduces a FRESH
   Type variable and the kernel's [uexecSG] instance becomes invisible to
   resolution ([UInitSh.v]'s header). *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UserPerm.           (* [uperm] -- the heap's permission map *)
Require Import ProcPtOwn.
Require Import UserPtTree.
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import PieceFam.
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import SpecFilewrite.      (* [filewrite_in] / [filewrite_extra] *)
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import PipeInvDefs.        (* [pipe_rw_ret]: what [filewrite_ret] is *)
Require Import WpUart.             (* [cons_licence] / [out_link] *)
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

Section UkWriteLeaf.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  S1  THE FAMILY                                                      *)
  (* =================================================================== *)
  (* [UShLine.xfam_rd] is the mould.  Row 16 reads ONE field -- [wf_Q],
     the caller's own output cursor, which serves BOTH arms of
     [SpecFilewrite.filewrite_in] since lane OUT-FUPD retired the trace
     seed -- and every deposit must answer the payload row, which is
     [kf_xpay] ([UexecSG.sexit_pay]).  Everything else is inert. *)
  Definition xfam_wr (Q : nat -> iProp Σ) (Xp : Z -> iProp Σ) : xfam :=
    {| xf_P     := fun _ _ => True%I;
       xf_Pmiss := fun _ _ => True%I;
       xf_Fo    := pfam_triv (fun _ _ _ => True%I);
       xf_Rs    := True%I;
       rf_F     := pfam_triv (fun _ _ _ _ => True%I);
       cf_P     := fun _ _ => True%I;
       cf_Pmiss := fun _ _ => True%I;
       cf_Fo    := pfam_triv (fun _ _ _ => True%I);
       of_P     := fun _ _ => True%I;
       of_Pmiss := fun _ _ => True%I;
       of_Farm  := pfam_triv (fun _ _ => True%I);
       of_Fun   := pfam_triv (fun _ _ => True%I);
       of_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fo    := pfam_triv (fun _ _ _ => True%I);
       of_Ft    := pfam_triv (fun _ _ _ => True%I);
       of_om    := OffParked;
       wf_Q     := Q;
       nf_P     := fun _ _ => True%I;
       nf_Pmiss := fun _ _ => True%I;
       nf_Farm  := pfam_triv (fun _ _ => True%I);
       nf_Fun   := pfam_triv (fun _ _ => True%I);
       nf_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       nf_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       uf_P     := fun _ _ => True%I;
       uf_Pmiss := fun _ _ => True%I;
       uf_Fent  := pfam_triv (fun _ _ _ _ => True%I);
       uf_Ftgt  := pfam_triv (fun _ _ => True%I);
       uf_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       uf_Fmiss := pfam_triv (fun _ _ _ => True%I);
       lf_Ftgt  := pfam_triv (fun _ _ _ => True%I);
       lf_Fent  := pfam_triv (fun _ _ _ _ => True%I);
       lf_Funt  := pfam_triv (fun _ _ => True%I);
       df_P     := fun _ _ => True%I;
       df_Pmiss := fun _ _ => True%I;
       df_Farm  := pfam_triv (fun _ _ => True%I);
       df_Fdots := pfam_triv (fun _ _ _ _ => True%I);
       df_Fun   := pfam_triv (fun _ _ => True%I);
       df_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       df_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       kf_pay   := fun _ => True%I;
       (* a program that forks lends nothing at this record (lane
          FORK-REFUND): [UexecSG.sfork_lend] is [emp]. *)
       kf_lend  := emp%I;
       kf_xpay  := Xp;
       rf_ret   := fun _ _ => True%I;
       (* the console's input link, at the trivial claim (lane CONS-IO,
          milestone B): this program says nothing about what it read *)
       rf_in    := fun _ => True%I ;
       rf_pq    := fun _ => True%I;
       rf_pqe   := fun _ _ => True%I;
       wf_Qe    := fun _ _ => True%I;
       cl_P     := True%I |}.

  (* the payload row [UkRun.udepwf_std] asks for, by computation *)
  Lemma xfam_wr_pay (Q : nat -> iProp Σ) (Xp : Z -> iProp Σ) :
    sexit_pay (xfam_wr Q Xp) = Xp.
  Proof using . reflexivity. Qed.

  (* =================================================================== *)
  (*  S2  THE TWO KEY-LEVEL ROWS, IN THE PROCESS'S DIRECTION              *)
  (*                                                                      *)
  (*  [UConsOpen]'s two are the mould; the proofs are the same three      *)
  (*  lines, the match at one literal.                                    *)
  (* =================================================================== *)
  Local Ltac xv6_skip :=
    match goal with
    | |- context [ @decide (?a = ?b) _ ] =>
        let Hc := fresh "Hc" in
        destruct (decide (a = b)) as [Hc | _]; [ exfalso; by vm_compute in Hc | ]
    end.
  Local Ltac xv6_take :=
    match goal with
    | |- context [ @decide (?a = ?b) _ ] =>
        let Hc := fresh "Hc" in
        destruct (decide (a = b)) as [_ | Hc]; [ | exfalso; by apply Hc ]
    end.

  Lemma sbundle_at_write_intro_at (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (v0 v1 v2 : mword 64) (sts : list fdstate) (Mv : gmap Z (bv 8))
      (pmv : gmap (mword 27) uperm) (szv : Z) (lzv : bool) :
    tf_w (uvis_tf W) (tf_arg_idx 0) = v0 ->
    tf_w (uvis_tf W) (tf_arg_idx 1) = v1 ->
    tf_w (uvis_tf W) (tf_arg_idx 2) = v2 ->
    uvis_fd W = sts ->
    uvis_M W = Mv ->
    uvis_perm W = pmv -> uvis_sz W = szv -> uvis_lazy W = lzv ->
    filewrite_in pmv szv lzv (fd_st_of_key v0 sts) (sys_rw_count v2) Mv v1
      (wf_Q f) (wf_Qe f) -∗
    sbundle_at X 16 f W.
  Proof using .
    intros H0 H1 H2 Hfd HM Hpm Hsz Hlz. iIntros "H".
    (* the REWRITE GOES FIRST, against the lemma's own variables
       ([UConsOpen.sbundle_at_open_intro_at]'s note) *)
    rewrite -H0 -H1 -H2 -Hfd -HM -Hpm -Hsz -Hlz.
    rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma spost_at_write_elim_at (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (v0 v1 v2 : mword 64) (sts : list fdstate) (Mv : gmap Z (bv 8))
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate)
      (cw' : Z) (cs' : gset gname) :
    tf_w (uvis_tf W) (tf_arg_idx 0) = v0 ->
    tf_w (uvis_tf W) (tf_arg_idx 1) = v1 ->
    tf_w (uvis_tf W) (tf_arg_idx 2) = v2 ->
    uvis_fd W = sts ->
    uvis_M W = Mv ->
    spost_at X 16 f W r M' fdv' cw' cs' -∗
    (* THE BLANKET COMES OUT FIRST (lane NIL-RET): [filewrite_ret] at the
       caller's own count, which is all the row says at a pipe or a
       read-only descriptor, where the arm below is [emp]. *)
    ⌜filewrite_ret (sys_rw_count v2) r⌝ ∗
    (* THE TABLE COMES OUT WITH THE ARM (lane TRAP-ROWS, T1), exactly as it
       does on the read side ([UShLine.spost_at_read_elim_at]): the short
       console write's reason is a fact about the process's page table and
       the key carries only the projection. *)
    ∃ P : uptd,
      ⌜perm_of (ud_um P) (uvis_sz W) = uvis_perm W⌝ ∗
      ⌜ProcPtOwn.proc_pt_wf P⌝ ∗
      ⌜uvis_lazy W = false -> lazy_free (ud_um P) (uvis_sz W)⌝ ∗
      filewrite_extra (uvis_gen W) P (fd_st_of_key v0 sts) (sys_rw_count v2) Mv v1
        (wf_Q f) (wf_Qe f) r.
  Proof using .
    intros H0 H1 H2 Hfd HM. iIntros "H".
    rewrite -H0 -H1 -H2 -Hfd -HM.
    rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  (* ...AND THE BLANKET IN THE PROGRAM'S OWN READING: the answer is [-1]
     or a count between 0 and the request, read as the C reads the return
     register.  [filewrite_ret] names the WORD [mword_of_int i]; below the
     sign boundary that word's signed reading is [i], and a count that came
     off argument 2 as a 32-bit int is ([SpecSysRead.sys_rw_count_lt]). *)
  Lemma filewrite_ret_signed (n : Z) (r : mword 64) :
    n < 2 ^ 63 ->
    filewrite_ret n r ->
    bv_signed r = -1 \/ (0 <= bv_signed r <= Z.max 0 n)%Z.
  Proof using .
    intros Hn [-> | (i & -> & Hi)]; [ left; vm_compute; reflexivity | right ].
    assert (Hs : bv_signed (mword_of_int i : mword 64) = i).
    { unfold bv_signed, bv_swrap. rewrite moi64_unsigned. unfold bv_wrap.
      assert (Eh : bv_half_modulus (MachineWord.Z_idx 64) = (2 ^ 63)%Z)
        by (vm_compute; reflexivity).
      assert (Em : bv_modulus (MachineWord.Z_idx 64) = (2 ^ 64)%Z)
        by (vm_compute; reflexivity).
      rewrite Eh Em.
      rewrite (Z.mod_small i (2 ^ 64)); [ | lia ].
      rewrite (Z.mod_small (i + 2 ^ 63) (2 ^ 64)); lia. }
    rewrite Hs. exact Hi.
  Qed.

  (* the same at a count the caller named as a [nat], which is how every
     member states its request *)
  Lemma filewrite_ret_nat (nb : nat) (r : mword 64) :
    Z.of_nat nb < 2 ^ 63 ->
    filewrite_ret (Z.of_nat nb) r ->
    bv_signed r = -1 \/ (0 <= bv_signed r <= Z.of_nat nb)%Z.
  Proof using .
    intros Hn Hr. destruct (filewrite_ret_signed _ _ Hn Hr) as [H | H];
      [ left; exact H | right; rewrite Z.max_r in H; [ exact H | lia ] ].
  Qed.


  (* =================================================================== *)
  (*  S3  THE ARM, OUT OF THE CALLER'S OWN LEDGER                         *)
  (* =================================================================== *)
  (* [UShLine.ush_fd_st_console] at an arbitrary standard descriptor: a
     write goes to fd 1 or fd 2, never to fd 0, so the index cannot be
     baked in the way the read's is.  The WRITABLE bit is what selects
     [SpecFilewrite.filewrite_in]'s device arm; the major is left free
     because the input arm asks for the chain at EVERY major
     ([filewrite_in]'s header: the devsw cell is null-or-consolewrite
     everywhere), and only the POST's arm is keyed on [CONSOLE]. *)
  Lemma uwr_fd_st_dev (v0 : mword 64) (fdv l : list fdstate)
      (i : nat) (rb : bool) (mj : Z) :
    bv_signed (trunc32 v0) = Z.of_nat i ->
    (i < NSTD)%nat ->
    take NSTD fdv = l ->
    l !! i = Some (FdOpen rb true (FdDevice mj)) ->
    fd_st_of_key v0 fdv = FdOpen rb true (FdDevice mj).
  Proof using .
    intros H0 Hi Htake Hli. rewrite /fd_st_of_key H0.
    destruct (decide (0 <= Z.of_nat i < Z.of_nat NOFILE)) as [_ | Hc];
      [ | exfalso; apply Hc; unfold NOFILE, NSTD in *; lia ].
    rewrite <- Htake in Hli.
    rewrite lookup_take in Hli; [ | exact Hi ].
    rewrite Nat2Z.id Hli. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  S4  THE SUPPLY                                                      *)
  (* =================================================================== *)
  (* THE DEPOSIT, AT THE PROGRAM'S OWN CURSOR.  [UkRun.udepwf_std] binds
     the image, the permission map and the break, and LENDS the heap
     authority inside the wand -- which is exactly what a program needs to
     justify its bytes: it owns its output run as [UserHeap.ubytesq] at a
     source function and reads the chain's per-byte premise off the heap
     with [UkRunSys.uheap_ubytes_wat].  So the chain enters here as a wand
     over the lent heap, and nothing about the image is fixed. *)
  Lemma uwrite_chain_sup (N : uk_names Σ) (Q : nat -> iProp Σ)
      (m : regfile) (pc : mword 64) (l : list fdstate)
      (i : nat) (rb : bool) (mj : Z) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat i ->
    (i < NSTD)%nat ->
    l !! i = Some (FdOpen rb true (FdDevice mj)) ->
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗
       cons_out_chain (S gen_id) M (m !!! Regidx a1_idx) Q 0%nat
         (Z.to_nat (sys_rw_count (m !!! Regidx a2_idx)))) -∗
    udepwf_std N m pc 16 (xfam_wr Q (ukn_pay N)) l.
  Proof using .
    intros H0 Hi Hli. iIntros "Hch".
    rewrite /udepwf_std. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Htake #Hmpay Hheap Hufd".
    iDestruct ("Hch" $! M pm sz with "Hheap") as "[Hheap Hch]".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_write_intro_at uslot (xfam_wr Q (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
              (m !!! Regidx a2_idx) fdv M _ _ _
              (tf_of_arg0 m pc) (tf_of_arg1 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all)
              eq_refl eq_refl eq_refl eq_refl).
    rewrite (uwr_fd_st_dev (m !!! Regidx a0_idx) fdv l i rb mj H0 Hi Htake Hli).
    cbn [xfam_wr wf_Q].
    rewrite /filewrite_in. iExact "Hch".
  Qed.

  (* =================================================================== *)
  (*  S4b  THE DEPOSIT THAT GIVES THE SOURCE RUN BACK                     *)
  (*       (lane CAT-ENTRY-2, RULING (h))                                 *)
  (*                                                                     *)
  (*  S4's deposit premise is a wand over the LENT heap, and the only     *)
  (*  thing a program can read the chain's per-byte premise off is its    *)
  (*  own source run ([UkRunSys.uheap_ubytes_wat]).  echo's run is        *)
  (*  [ustr … DfracDiscarded] -- persistent -- so one copy serves both    *)
  (*  the wand and the leaf underneath.  cat's run is its 512-byte READ   *)
  (*  BUFFER at [DfracOwn 1]: the copy put into the wand is consumed      *)
  (*  there, and the buffer cannot be rebuilt for the next turn.          *)
  (*                                                                     *)
  (*  THE FIX IS TO LET THE WAND HAND IT BACK, and the way out is the     *)
  (*  chain's own payload: [cons_out_chain]'s nodes are ADDITIVE, so a    *)
  (*  resource held beside the cursor answers every node and rides out    *)
  (*  with [Q] at the count the post reports ([uwrite_no_short] below).   *)
  (*  So the caller halves its run ([ubytes_halve]), lends one half to    *)
  (*  the leaf and one to the wand, and gets both back.                   *)
  (* =================================================================== *)

  (* the chain carries a frame: every node is [Q j ∧ the step], and an
     additive conjunction is answered by ONE copy of the context *)
  Lemma cons_out_chain_frame (k : nat) (M : gmap Z (bv 8)) (ua : mword 64)
      (Q : nat -> iProp Σ) (R : iProp Σ) (j cnt : nat) :
    R -∗ cons_out_chain k M ua Q j cnt -∗
    cons_out_chain k M ua (fun i : nat => Q i ∗ R)%I j cnt.
  Proof using .
    revert j. induction cnt as [| cnt IH]; intros j.
    - iIntros "HR HQ". cbn [cons_out_chain]. iFrame "HQ HR".
    - iIntros "HR H". cbn [cons_out_chain]. iSplit.
      + iDestruct "H" as "[HQ _]". iFrame "HQ HR".
      + iDestruct "H" as "[_ H]". iIntros (b) "%Hb".
        iDestruct ("H" $! b with "[%]") as "H"; [ exact Hb | ].
        iApply (out_link_mono Uart0 k b
                  (cons_out_chain k M ua Q (S j) cnt)
                  (cons_out_chain k M ua (fun i : nat => Q i ∗ R)%I (S j) cnt)
                  with "[HR] H").
        iIntros "Hc". iApply (IH (S j) with "HR Hc").
  Qed.

  (* ...and S4's supply at it: the deposit premise RETURNS the caller's
     source run beside the chain, and the run comes home in the post's
     own [Q] ([uwrite_post_cons] / [uwrite_no_short] at [fun j => Q j ∗ R]) *)
  Lemma uwrite_chain_sup_ret (N : uk_names Σ) (Q : nat -> iProp Σ)
      (R : iProp Σ) (m : regfile) (pc : mword 64) (l : list fdstate)
      (i : nat) (rb : bool) (mj : Z) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat i ->
    (i < NSTD)%nat ->
    l !! i = Some (FdOpen rb true (FdDevice mj)) ->
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ R ∗
       cons_out_chain (S gen_id) M (m !!! Regidx a1_idx) Q 0%nat
         (Z.to_nat (sys_rw_count (m !!! Regidx a2_idx)))) -∗
    udepwf_std N m pc 16 (xfam_wr (fun j : nat => Q j ∗ R)%I (ukn_pay N)) l.
  Proof using .
    intros H0 Hi Hli. iIntros "Hch".
    iApply (uwrite_chain_sup N (fun j : nat => Q j ∗ R)%I m pc l i rb mj
              H0 Hi Hli).
    iIntros (M pm sz) "Hheap".
    iDestruct ("Hch" $! M pm sz with "Hheap") as "(Hheap & HR & Hch)".
    iFrame "Hheap".
    iApply (cons_out_chain_frame (S gen_id) M (m !!! Regidx a1_idx) Q R
              0%nat _ with "HR Hch").
  Qed.

  (* ...AND THE RUN'S OWN HALVING, so a caller whose source run is
     EXCLUSIVE can be in both places at once.  [UserHeap.v] is the natural
     home for this and [UserHeap.ubytesq] has no fractional law today; it
     is stated here, beside its one consumer, because that file's cone is
     the whole U tier. *)
  Lemma ubytesq_frac (γd : gname) (q1 q2 : Qp) (a : Z) (n : nat)
      (f : nat -> bv 8) :
    ubytesq γd (DfracOwn (q1 + q2)) a n f ⊣⊢
    ubytesq γd (DfracOwn q1) a n f ∗ ubytesq γd (DfracOwn q2) a n f.
  Proof using .
    rewrite /ubytesq -big_sepL_sep.
    apply big_opL_proper. intros k j _. rewrite /ubyteq.
    exact (ghost_map_elem_fractional (a + Z.of_nat j)%Z γd (f j) q1 q2).
  Qed.

  Lemma ubytes_halve (γd : gname) (a : Z) (n : nat) (f : nat -> bv 8) :
    ubytes γd a n f ⊣⊢
    ubytesq γd (DfracOwn (1/2)) a n f ∗ ubytesq γd (DfracOwn (1/2)) a n f.
  Proof using .
    rewrite /ubytes -(ubytesq_frac γd (1/2)%Qp (1/2)%Qp a n f).
    by rewrite Qp.half_half.
  Qed.

  (* ...AND THE POST, READ BACK AT THE SAME FAMILY.  The device arm of
     [SpecFilewrite.filewrite_extra] is keyed on [CONSOLE] -- at any other
     major the call reached a callee this layer cannot name and nothing
     true is left to say ([filewrite_extra_dev_drop]) -- so this is where
     the major stops being free. *)
  Lemma uwrite_post_cons (Q : nat -> iProp Σ) (Xp : Z -> iProp Σ)
      (W : uvis) (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate)
      (cw' : Z) (cs' : gset gname) (l : list fdstate) (i : nat) (rb : bool) :
    bv_signed (trunc32 (tf_w (uvis_tf W) (tf_arg_idx 0))) = Z.of_nat i ->
    (i < NSTD)%nat ->
    take NSTD (uvis_fd W) = l ->
    l !! i = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    spost_at uslot 16 (xfam_wr Q Xp) W r M' fdv' cw' cs' -∗
    ∃ P : uptd,
      ⌜perm_of (ud_um P) (uvis_sz W) = uvis_perm W⌝ ∗
      ⌜ProcPtOwn.proc_pt_wf P⌝ ∗
      ⌜uvis_lazy W = false -> lazy_free (ud_um P) (uvis_sz W)⌝ ∗
      write_cons_arms P (tf_w (uvis_tf W) (tf_arg_idx 1)) Q
        (sys_rw_count (tf_w (uvis_tf W) (tf_arg_idx 2))) r.
  Proof using .
    intros H0 Hi Htake Hli. iIntros "H".
    iDestruct (spost_at_write_elim_at uslot (xfam_wr Q Xp) W
                 (tf_w (uvis_tf W) (tf_arg_idx 0))
                 (tf_w (uvis_tf W) (tf_arg_idx 1))
                 (tf_w (uvis_tf W) (tf_arg_idx 2))
                 (uvis_fd W) (uvis_M W) r M' fdv' cw' cs'
                 eq_refl eq_refl eq_refl eq_refl eq_refl with "H") as "H".
    iDestruct "H" as "(_ & %P & %Hperm & %Hwf & %Hlz & H)".
    iExists P. iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    rewrite (uwr_fd_st_dev (tf_w (uvis_tf W) (tf_arg_idx 0)) (uvis_fd W)
               l i rb CONSOLE H0 Hi Htake Hli).
    cbn [xfam_wr wf_Q].
    rewrite /filewrite_extra.
    case_decide as Hc; [ iExact "H" | exfalso; by apply Hc ].
  Qed.

  (* =================================================================== *)
  (*  S5  THE SMOKE TEST (W3): A TWO-BYTE WRITE FROM THE LICENCE           *)
  (*                                                                      *)
  (*  [SpecConsolewrite.cons_out_chain_of_licence] pays the chain at the   *)
  (*  TRIVIAL cursor, which is what every quiet write leaf does and what   *)
  (*  says nothing.  This is the same payment at a cursor that DEPENDS ON  *)
  (*  ITS INDEX, which is the whole point of the leaf: the caller's own    *)
  (*  family travels into the deposit and comes back out of the post.      *)
  (* =================================================================== *)

  (* the licence pays any cursor the chain's own range makes free -- the
     bounded form of [SpecConsolewrite.cons_out_chain_of_licence] *)
  Lemma cons_out_chain_of_licence_bnd (M : gmap Z (bv 8)) (ua : mword 64)
      (Q : nat -> iProp Σ) (k cnt : nat) :
    (forall j : nat, (k <= j <= k + cnt)%nat -> ⊢ Q j) ->
    cons_licence -∗ cons_out_chain (S gen_id) M ua Q k cnt.
  Proof using .
    revert k. induction cnt as [| cnt IH]; intros k HQ.
    - iIntros "_". cbn [cons_out_chain].
      iApply (HQ k ltac:(lia)).
    - iIntros "#Hlic". cbn [cons_out_chain]. iSplit.
      + iApply (HQ k ltac:(lia)).
      + iIntros (b) "_". iApply (out_link_of_licence _ b with "Hlic").
        iApply (IH (S k) with "Hlic"). intros j Hj. apply HQ. lia.
  Qed.

  (* a cursor that is not the trivial one: "at most two bytes so far" *)
  Definition uwr_demo_Q : nat -> iProp Σ := fun k => (⌜(k <= 2)%nat⌝)%I.

  Lemma uwrite_two_of_licence (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (l : list fdstate) (i : nat) (rb : bool) (mj : Z) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat i ->
    (i < NSTD)%nat ->
    l !! i = Some (FdOpen rb true (FdDevice mj)) ->
    sys_rw_count (m !!! Regidx a2_idx) = 2 ->
    cons_licence -∗
    udepwf_std N m pc 16 (xfam_wr uwr_demo_Q (ukn_pay N)) l.
  Proof using .
    intros H0 Hi Hli Hcnt. iIntros "#Hlic".
    iApply (uwrite_chain_sup N uwr_demo_Q m pc l i rb mj H0 Hi Hli).
    iIntros (M pm sz) "Hheap". iFrame "Hheap".
    rewrite Hcnt. change (Z.to_nat 2) with 2%nat.
    iApply (cons_out_chain_of_licence_bnd M (m !!! Regidx a1_idx) uwr_demo_Q
              0%nat 2%nat with "Hlic").
    intros j Hj. rewrite /uwr_demo_Q. iPureIntro. lia.
  Qed.

  (* ...AND WHAT COMES BACK IS THE COUNT, AT THE CALLER'S OWN FAMILY: not
     [emp], not a claim about the wire, but "the answer is a byte count
     this call did not exceed", read off [uwr_demo_Q] at the very index
     [SpecFilewrite.write_cons_arms] hands the cursor back at. *)
  Lemma uwrite_two_post (W : uvis) (r : mword 64) (M' : gmap Z (bv 8))
      (fdv' : list fdstate) (cw' : Z) (cs' : gset gname)
      (Xp : Z -> iProp Σ) (l : list fdstate) (i : nat) (rb : bool) :
    bv_signed (trunc32 (tf_w (uvis_tf W) (tf_arg_idx 0))) = Z.of_nat i ->
    (i < NSTD)%nat ->
    take NSTD (uvis_fd W) = l ->
    l !! i = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    sys_rw_count (tf_w (uvis_tf W) (tf_arg_idx 2)) = 2 ->
    spost_at uslot 16 (xfam_wr uwr_demo_Q Xp) W r M' fdv' cw' cs' -∗
    ⌜filewrite_ret 2 r⌝ ∗
    ∃ k : nat, ⌜r = (mword_of_int (Z.of_nat k) : mword 64) /\ (k <= 2)%nat⌝.
  Proof using .
    intros H0 Hi Htake Hli Hcnt. iIntros "H".
    iDestruct (uwrite_post_cons uwr_demo_Q Xp W r M' fdv' cw' cs' l i rb
                 H0 Hi Htake Hli with "H") as (P) "(_ & _ & _ & H)".
    rewrite Hcnt /write_cons_arms /uwr_demo_Q.
    iDestruct "H" as "[[%Hr %Hq] | [Hs | %Hr]]".
    - destruct Hr as [-> _]. iSplit.
      + iPureIntro. apply filewrite_ret_all. lia.
      + iExists 2%nat. iPureIntro. split; [ reflexivity | lia ].
    - iDestruct "Hs" as (k) "(%Hr & %Hlt & %Hsh & %Hq)". subst r. iSplit.
      + iPureIntro. rewrite /filewrite_ret /pipe_rw_ret. right.
        exists (Z.of_nat k). split; [ reflexivity | lia ].
      + iExists k. iPureIntro. split; [ reflexivity | lia ].
    - exfalso. destruct Hr as [_ Hlt]. lia.
  Qed.

  (* =================================================================== *)
  (*  S6  THE SHORT ARM IS REFUTABLE (lane IO-LEAF; lane TRAP-ROWS T1's     *)
  (*      deliverable, CASHED)                                             *)
  (*                                                                      *)
  (*  S5 above pays a cursor and reads it back at “the count consolewrite  *)
  (*  reached”, which is all a caller can say while the SHORT arm stands.  *)
  (*  A caller threading a per-byte cursor cannot live with that arm: it   *)
  (*  hands the cursor back UNMOVED while the program's own string index   *)
  (*  has advanced, so every byte after a short write is stuck on an arm   *)
  (*  nothing refutes.                                                     *)
  (*                                                                      *)
  (*  T1 gave the arm its REASON -- a byte of the run at or after the      *)
  (*  cursor is on a page the kernel could not read through                *)
  (*  ([SpecFilewrite.write_cons_short], [UserPtTree.uva_rmapped]) -- and  *)
  (*  [UkRunSys.wp_uk_ecall_write_chain_buf] hands out the fact that       *)
  (*  refutes it for the caller's OWN run.  This is the two put together:  *)
  (*  a console write of a run the caller owns returns the FULL count and  *)
  (*  the caller's own cursor at it.  Nothing else in the post survives,   *)
  (*  and nothing else is wanted.                                         *)
  (* =================================================================== *)
  Lemma uwrite_no_short (Q : nat -> iProp Σ) (Xp : Z -> iProp Σ)
      (W : uvis) (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate)
      (cw' : Z) (cs' : gset gname) (l : list fdstate) (i : nat) (rb : bool)
      (nb : nat) :
    bv_signed (trunc32 (tf_w (uvis_tf W) (tf_arg_idx 0))) = Z.of_nat i ->
    (i < NSTD)%nat ->
    take NSTD (uvis_fd W) = l ->
    l !! i = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    sys_rw_count (tf_w (uvis_tf W) (tf_arg_idx 2)) = Z.of_nat nb ->
    (* the two rows the buffer-carrying leaf hands back *)
    uvis_lazy W = false ->
    (forall (P : uptd) (j : nat),
       ProcPtOwn.proc_pt_wf P ->
       perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
       lazy_free (ud_um P) (uvis_sz W) ->
       (j < nb)%nat ->
       UserPtTree.uva_rmapped P
         (uint (add_vec_int (tf_w (uvis_tf W) (tf_arg_idx 1)) (Z.of_nat j)))) ->
    spost_at uslot 16 (xfam_wr Q Xp) W r M' fdv' cw' cs' -∗
    ⌜r = (mword_of_int (Z.of_nat nb) : mword 64)⌝ ∗ Q nb.
  Proof using .
    intros H0 Hi Htake Hli Hcnt Hlz Hnf. iIntros "H".
    iDestruct (uwrite_post_cons Q Xp W r M' fdv' cw' cs' l i rb
                 H0 Hi Htake Hli with "H") as (P) "(%Hperm & %Hwf & %Hlf & H)".
    rewrite Hcnt.
    iDestruct "H" as "[[%Hr Hq] | [Hs | %Hr]]".
    - destruct Hr as [-> _]. iSplitR; [by iPureIntro |].
      by rewrite Nat2Z.id.
    - (* THE SHORT ARM, refuted at the offset its reason exhibits *)
      iDestruct "Hs" as (k) "(%Hr & %Hlt & %Hsh & _)".
      exfalso. destruct Hsh as (d & Hkd & Hdn & Hno).
      apply Hno. apply (Hnf P d Hwf Hperm (Hlf Hlz)). lia.
    - exfalso. destruct Hr as [_ Hlt]. lia.
  Qed.

End UkWriteLeaf.
