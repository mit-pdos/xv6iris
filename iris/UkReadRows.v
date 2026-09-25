(* ===================================================================== *)
(* UkReadRows.v -- THE READ LEAF'S SHARED KEY-LEVEL ROWS.                 *)
(*                                                                        *)
(* [UexecExecInst] states read's deposit ELIM and its post INTRO -- the    *)
(* DISPATCHER's two directions.  A PROCESS needs the other two, at         *)
(* readings it can name, and until this file each arm of the read leaf     *)
(* carried its own copy of them: [UkReadFile]'s pair (suffix [_st]) and    *)
(* [UShLine]'s (suffix [_at]) were the SAME TWO LEMMAS, word for word,     *)
(* because neither could see the other -- one sits under the file arm and  *)
(* one under the echo application's line lemma.  RD-2's report flagged the *)
(* duplication and this is its one home.  The pair is arm-INDEPENDENT by   *)
(* construction: it says nothing about the descriptor, only that read's    *)
(* row of [UexecExecInst.xv6_sbundle] / [xv6_spost] is the one at          *)
(* [USYS_read], and which arm of [SpecFileread.fileread_in] the caller     *)
(* then lands on is decided by the KEY's own table.                        *)
(*                                                                        *)
(* THE TWO FAMILIES live here for the same reason.  [UexecExecInst.xfam]   *)
(* is a wide record and a deposit is read at ONE number                    *)
(* ([xv6_sbundle] is a match on it), so read's family is that record at    *)
(* the two or three fields read's rows look at and the trivial ones        *)
(* everywhere else.  There are exactly two such points and they are THE    *)
(* ARMS: [xfam_rd] names [rf_ret] / [rf_in] and leaves [rf_F] at the unit  *)
(* (the CONSOLE member -- what the caller asks to be told about the        *)
(* cursor and about the input window it consumed), [xfam_rdf] does the     *)
(* reverse (the INODE member -- the observation receipt).  Both were       *)
(* spelled out in the file that first needed them; they are spelled once   *)
(* here, and that difference IS the arm.                                   *)
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
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UserPerm.           (* [perm_of] / [lazy_free] *)
Require Import ProcPtOwn.          (* [uptd] / [ud_um] / [proc_pt_wf] *)
Require Import UserPtTree.
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import VcGen.              (* [trunc32] *)
Require Import PieceFam.           (* [pfam] / [pfam_triv] *)
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6], [xfam] *)
Require Import SpecFileread.       (* [fileread_in] / [fileread_extra_core] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import FsAbsDefs.          (* [aview] / [anode] *)
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

Section UkReadRows.
  (* the kernel bundle's binder list, and nothing of any application: this
     file is below every arm. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.

  (* =================================================================== *)
  (*  1.  THE TWO FAMILIES                                                *)
  (* =================================================================== *)

  (* THE CONSOLE / STANDARD-STREAM MEMBER: [rf_ret] is what the caller asks
     to be told about the cursor the call ran at, [rf_in] what it asks to be
     told about the INPUT WINDOW the call consumed
     ([WpUart.cons_read_pay]'s answer).  [rf_F] is the unit. *)
  Definition xfam_rd (Q : Z -> iProp Σ) (Rd : nat -> nat -> iProp Σ)
      (Rin : list (list mobs * bv 8) -> iProp Σ) : xfam :=
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
       wf_Q     := fun _ => True%I;
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
       kf_xpay  := Q;
       rf_ret   := Rd;
       rf_in    := Rin ;
       rf_pq    := fun _ => True%I;
       rf_pqe   := fun _ _ => True%I;
       wf_Qe    := fun _ _ => True%I;
       cl_P     := True%I |}.

  (* THE INODE MEMBER: [rf_F] is the observation commit's receipt, and the
     two console fields are the unit. *)
  Definition xfam_rdf (Q : Z -> iProp Σ)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) : xfam :=
    {| xf_P     := fun _ _ => True%I;
       xf_Pmiss := fun _ _ => True%I;
       xf_Fo    := pfam_triv (fun _ _ _ => True%I);
       xf_Rs    := True%I;
       rf_F     := F;
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
       wf_Q     := fun _ => True%I;
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
       kf_lend  := emp%I;
       kf_xpay  := Q;
       rf_ret   := fun _ _ => True%I;
       rf_in    := fun _ => True%I ;
       rf_pq    := fun _ => True%I;
       rf_pqe   := fun _ _ => True%I;
       wf_Qe    := fun _ _ => True%I;
       cl_P     := True%I |}.

  (* =================================================================== *)
  (*  2.  THE PAIR                                                        *)
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

  (* THE DEPOSIT, IN THE PROCESS'S DIRECTION.  The key's own projections
     enter as PURE premises, because a program names the argument word and
     the table it believes the key carries, not the key. *)
  Lemma sbundle_at_read_intro (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (v0 v2 : mword 64) (sts : list fdstate) :
    tf_w (uvis_tf W) (tf_arg_idx 0) = v0 ->
    tf_w (uvis_tf W) (tf_arg_idx 2) = v2 ->
    uvis_fd W = sts ->
    fileread_in (fd_st_of_key v0 sts) (sys_rw_count v2) (rf_F f) (rf_ret f) (rf_in f)
      (rf_pq f) (rf_pqe f) True%I -∗
    sbundle_at X USYS_read f W.
  Proof using .
    intros H0 H2 Hfd. iIntros "H".
    (* the REWRITE GOES FIRST, against the lemma's own variables
       ([UConsOpen.sbundle_at_open_intro_at]'s note) *)
    rewrite -H0 -H2 -Hfd.
    rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_take. iExact "H".
  Qed.

  (* ...AND THE POST.  THE ANSWER'S RANGE COMES OUT WITH THE RECEIPT (lane
     CONS-ROWS, B3): row 5 carries [SpecFileread.fileread_ret] at the key's
     own count, and a process that has not tied [r] to its request can spend
     neither of the receipt's control-flow rows. *)
  Lemma spost_at_read_elim (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (v0 v1 v2 : mword 64) (sts : list fdstate)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate)
      (cw' : Z) (cs' : gset gname) :
    tf_w (uvis_tf W) (tf_arg_idx 0) = v0 ->
    tf_w (uvis_tf W) (tf_arg_idx 1) = v1 ->
    tf_w (uvis_tf W) (tf_arg_idx 2) = v2 ->
    uvis_fd W = sts ->
    spost_at X USYS_read f W r M' fdv' cw' cs' -∗
    ⌜fileread_ret (sys_rw_count v2) r⌝ ∗
    ∃ P : uptd,
      ⌜perm_of (ud_um P) (uvis_sz W) = uvis_perm W⌝ ∗
      ⌜proc_pt_wf P⌝ ∗
      ⌜uvis_lazy W = false -> lazy_free (ud_um P) (uvis_sz W)⌝ ∗
      fileread_extra_core (uvis_gen W) P (fd_st_of_key v0 sts) (sys_rw_count v2)
        (rf_F f) (rf_ret f) (rf_in f) (rf_pq f) (rf_pqe f) r M' v1.
  Proof using .
    intros H0 H1 H2 Hfd. iIntros "H".
    rewrite -H0 -H1 -H2 -Hfd.
    rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_take. iExact "H".
  Qed.

  (* =================================================================== *)
  (*  3.  THE DESCRIPTOR THE CALL WILL RUN ON                              *)
  (* =================================================================== *)
  (* Which arm [SpecFileread.fileread_in] takes is selected by the KEY's
     table, and a program holds either its LEDGER of the low [NSTD] slots or
     a HANDLE on one descriptor.  Both readings are one step; both live here
     so that neither arm's file has to restate the other's. *)
  Lemma std_fd_st_of_key (v0 : mword 64) (fdv l : list fdstate)
      (fd : nat) (st : fdstate) :
    bv_signed (trunc32 v0) = Z.of_nat fd ->
    (fd < NSTD)%nat ->
    take NSTD fdv = l ->
    l !! fd = Some st ->
    fd_st_of_key v0 fdv = st.
  Proof using .
    intros H0 Hlt Htake Hl0. rewrite /fd_st_of_key H0.
    destruct (decide (0 <= Z.of_nat fd < Z.of_nat NOFILE)) as [_ | Hc];
      [ | exfalso; apply Hc; unfold NSTD, NOFILE in *; lia ].
    rewrite <- Htake in Hl0.
    rewrite lookup_take in Hl0; [ | lia ].
    rewrite Nat2Z.id Hl0. reflexivity.
  Qed.

  Lemma ufd_fd_st_of_key (v0 : mword 64) (fdv : list fdstate) (fd : nat)
      (st : fdstate) :
    bv_signed (trunc32 v0) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    fdv !! fd = Some st ->
    fd_st_of_key v0 fdv = st.
  Proof using .
    intros H0 Hlt Hlk. rewrite /fd_st_of_key H0.
    destruct (decide (0 <= Z.of_nat fd < Z.of_nat NOFILE)) as [_ | Hc];
      [ | exfalso; apply Hc; lia ].
    rewrite Nat2Z.id Hlk. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  3b.  THE STATE-FIXED DEPOSIT, AND THE HANDLE'S AGREEMENT             *)
  (*                                                                      *)
  (*  Both MOVED here from [UkReadFile.v] (lane RD-6), which is the home   *)
  (*  design/user-read.md section 3's housekeeping paragraph named: they   *)
  (*  are ARM-independent (the "file" leaf is really the HANDLE leaf) and  *)
  (*  they are SYSCALL-independent too -- [udepwf_st] takes the number,    *)
  (*  and the write side's file arm (lane RD-6) reaches its own row        *)
  (*  through exactly these two.  [UkReadPipe.v] used to import them from  *)
  (*  [UkReadFile.v] for want of a lower home; both keep their exact       *)
  (*  statements, so every caller is untouched.                           *)
  (* =================================================================== *)
  (* [UkRun.udepwf_std]'s third sibling.  Row 5's / row 16's bundle is the
     contract at [FdSlots.fd_st_of_key (xk_a W 0) (uvis_fd W)], so which
     ARM the supplier must answer is decided by the KEY's own descriptor
     table -- and a supplier holding an observation commit at inode [i] (or
     a write chain at it) answers the INODE arm at THAT file and no other.
     [udepwf]'s own forall binds [fdv], so it cannot be told; the leaf,
     which has destructed [urun] and holds both the authority and the
     caller's HANDLE, can ([UserFd.ufd_agree]), and that is why the fact
     enters as a premise INSIDE the forall here.

     THE CWD IS STILL forall-BOUND, as in the ledger-fixed form: neither a
     read's nor a write's bundle reads a path. *)
  Definition udepwf_st (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (fdep : sfam) (st : fdstate) : iProp Σ :=
    (⌜sexit_pay fdep = ukn_pay N⌝ ∗
     ∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname)
       (pidv : mword 32),
       ⌜fd_st_of_key (m !!! Regidx (mword_of_int 10 : mword 5)) fdv = st⌝ -∗
       my_pay gn (ukn_pay N) -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       sbundle_at uslot n fdep
         (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all))%I.

  (* ...AND IT IS [UkRunSys.udepwf_K] AT THAT READING, so the one read walk
     and the one write walk take it as it stands. *)
  Lemma udepwf_st_K (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (fdep : sfam) (st : fdstate) :
    udepwf_st N m pc n fdep st
    ⊣⊢ udepwf_K N m pc n fdep
          (fun fdv =>
             fd_st_of_key (m !!! Regidx (mword_of_int 10 : mword 5)) fdv = st).
  Proof using . rewrite /udepwf_st /udepwf_K. iSplit; iIntros "H"; iExact "H". Qed.

  (* THE DESCRIPTOR THE CALL WILL RUN ON, OUT OF THE CALLER'S OWN HANDLE --
     the walks' agreement premise at the HANDLE.  The console twin reads it
     out of the LEDGER ([std_fd_st_of_key] above), which can only speak of
     the low [NSTD] slots; a file descriptor is never one of those
     ([UserFd.ufd] carries the bound), so this is the same step at the
     handle instead. *)
  Lemma ufd_key_agree (N : uk_names Σ) (fd : nat) (st : fdstate)
      (v0 : mword 64) :
    bv_signed (trunc32 v0) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    forall fdv : list fdstate,
      ufd_auth (ukn_fd N) fdv -∗ UserFd.ufd (ukn_fd N) fd st -∗
      ⌜fd_st_of_key v0 fdv = st⌝.
  Proof using .
    intros H0 Hlt fdv. iIntros "Ha Hh".
    iDestruct (ufd_agree (ukn_fd N) fdv fd st with "Ha Hh") as %Hlk.
    iPureIntro. exact (ufd_fd_st_of_key v0 fdv fd st H0 Hlt Hlk).
  Qed.

  (* =================================================================== *)
  (*  4.  THE COUNT, ACROSS THE SIGN BOUNDARY                              *)
  (* =================================================================== *)
  (* A program names its request as a [nat] read off argument 2 UNSIGNED;
     the trapframe's word reaches file.c as a 32-bit INT
     ([SpecSysRead.sys_rw_count]) and the leaf's window is cut at the SIGNED
     low word.  The two agree exactly below the sign boundary.  Above it the
     kernel really is answering a different request, so these are bridges
     and not formalities. *)
  Lemma uread_count_le (w : mword 64) (k : nat) :
    uint w = Z.of_nat k ->
    (Z.to_nat (bv_signed (subrange_vec_dec w 31 0 : mword 32)) <= k)%nat.
  Proof using .
    intros Hu. rewrite uint_unsigned in Hu.
    pose proof (subrange_31_0_unsigned w) as Hlo.
    assert (Hs : bv_signed (subrange_vec_dec w 31 0 : mword 32)
                 = (bv_unsigned (subrange_vec_dec w 31 0 : mword 32)
                    + 2147483648) mod 4294967296 - 2147483648)
      by reflexivity.
    rewrite Hs Hlo.
    set (u := bv_unsigned w mod 4294967296).
    assert (Hub : 0 <= u < 4294967296)
      by (apply Z.mod_pos_bound; lia).
    assert (Hule : u <= bv_unsigned w)
      by (apply Z.mod_le; [ lia | lia ]).
    pose proof (Z.div_mod (u + 2147483648) 4294967296 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (u + 2147483648) 4294967296 ltac:(lia)) as Hmb.
    lia.
  Qed.

  Lemma uread_count_is_cap (w : mword 64) (cap : nat) :
    uint w = Z.of_nat cap -> (Z.of_nat cap < 2 ^ 31)%Z ->
    sys_rw_count w = Z.of_nat cap.
  Proof using .
    intros Hu Hlt. rewrite uint_unsigned in Hu.
    change (2 ^ 31)%Z with 2147483648%Z in Hlt.
    rewrite /sys_rw_count. unfold bv_signed.
    rewrite trunc32_subrange subrange_31_0_unsigned Hu.
    rewrite (Z.mod_small (Z.of_nat cap) 4294967296); [| lia].
    assert (Hhm : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
    rewrite bv_swrap_small; [ reflexivity | rewrite Hhm; lia ].
  Qed.

End UkReadRows.
