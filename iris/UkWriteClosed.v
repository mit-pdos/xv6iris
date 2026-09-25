(* ===================================================================== *)
(*  UkWriteClosed.v -- THE WRITE OBLIGATION AT A CLOSED DESCRIPTOR        *)
(*  (app-echo.md, lane IO-LEAF; the endgame audit's blocker -- ksh_w at a *)
(*   non-console descriptor has no discharge -- RULED: derive it from the *)
(*   write syscall's own closed-fd arm.)                                  *)
(*                                                                       *)
(*  WHAT A WRITE TO A CLOSED DESCRIPTOR DOES.  sys_write's argfd fails    *)
(*  before any file is touched: the call returns -1 and prints nothing.   *)
(*  At the U tier that is row 16's CLOSED arm --                          *)
(*  [SpecFilewrite.filewrite_in] at [FdClosed] is [emp], and which arm    *)
(*  the row asks for is decided by the KEY's own descriptor table         *)
(*  ([FdSlots.fd_st_of_key] at argument 0), of which a program holds      *)
(*  the low [NSTD] slots ([UserFd.ustd]).  So a program whose ledger says *)
(*  the descriptor it is about to write is closed owes NOTHING for the    *)
(*  call: the deposit [UkRun.udepwf_std] is supplied out of thin air, the *)
(*  same way [UShLine.ush_read_sup_closed] supplies the read's shut arm.  *)
(*                                                                       *)
(*  WHY IT IS A FILE OF ITS OWN.  The two per-call obligations it         *)
(*  discharges -- [UkSh.ksh_w] (the shell's, per call) and                *)
(*  [UkInit.kinit_w1] (init's, per byte) -- live below the file system    *)
(*  and cannot name row 16's reading; [UkWriteLeaf] is where row 16 is    *)
(*  named, and it sits above both walks.  This file sits above all three, *)
(*  and below the application: nothing here names an era, a link or a    *)
(*  credential.  [UShOut.ksh_w_of_link_prompt] and                        *)
(*  [UInitBanner.kinit_w1_of_link] are the CONSOLE instances of the same  *)
(*  two obligations; these are the CLOSED ones, and the audit's sites     *)
(*  (init's all-closed head arm [UInitFd.ufd_l0], where sh's fd 2 and     *)
(*  init's fd 1 are shut) are where they stop spending the free write law *)
(*  [UkRun.udepw_law 16].                                                 *)
(*                                                                       *)
(*    S1  THE ARM, out of the caller's own ledger: [fd_st_of_key] reads   *)
(*        [FdClosed] at a closed low slot ([UkWriteLeaf.uwr_fd_st_dev]'s  *)
(*        twin, and [UShLine.ush_fd_st_closed] at any standard slot).     *)
(*    S2  THE SUPPLY at that arm, at ANY cursor family: the closed arm    *)
(*        reads no field of the family, so the deposit costs nothing.     *)
(*    S3  THE TWO OBLIGATIONS, met by the syscall's own arm: the ledger   *)
(*        goes in and comes back, and the post is thrown away -- there is *)
(*        nothing in it ([filewrite_extra] at [FdClosed] is [emp] too).   *)
(*    S4  THE WITNESSES: both, at init's head ledger [UInitFd.ufd_l0],    *)
(*        which is where the audit needs them.                            *)
(*                                                                       *)
(*  THE DESCRIPTOR IS NAMED AS THE KERNEL READS IT: [sys_write]'s argfd   *)
(*  reads argument 0 as a 32-bit signed int ([bv_signed (trunc32 v)]),    *)
(*  so the premise is that reading, at a slot below [NSTD] -- exactly     *)
(*  [UkWriteLeaf.uwr_fd_st_dev]'s shape, and a literal descriptor         *)
(*  discharges it by [vm_compute; reflexivity] (S4).                      *)
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
(* THE GHOST BINDER LIST, each module IMPORTED and not merely required
   ([UkWriteLeaf.v]'s header) *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import UexecRet UexecSG.
Require Import UkRun.
Require Import SpecFilewrite.      (* [filewrite_in] *)
Require Import UkWriteLeaf.        (* [xfam_wr] / [sbundle_at_write_intro_at] *)
Require Import UkSh.               (* [ksh_w] / [wp_ksh_write_chain] *)
Require Import UkInit.             (* [kinit_w1] / [wp_kinit_write_chain] *)
Require Import UInitFd.            (* [ufd_l0] -- the witnesses' ledger *)
Require Import CtxIdDefs.
Require User.ShSyms User.InitSyms.  (* the two stubs' entry pcs *)
Local Open Scope Z_scope.
Import Defs.

Section UkWriteClosed.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  (* NO [ctokG] AND NO [uexecSG] VARIABLE, for [UInitBanner]'s reasons:
     [Xv6G.xv6_ctok] is an instance and this file reads row 16's CONCRETE
     arm, so the deposit instance has to be the xv6 one. *)
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* =================================================================== *)
  (*  S1  THE ARM, OUT OF THE CALLER'S OWN LEDGER                         *)
  (* =================================================================== *)
  (* [UkWriteLeaf.uwr_fd_st_dev] at the CLOSED row: the kernel's reading of
     argument 0 lands on a low slot the program's ledger says is shut. *)
  Lemma uwr_fd_st_closed (v0 : mword 64) (fdv l : list fdstate) (i : nat) :
    bv_signed (trunc32 v0) = Z.of_nat i ->
    (i < NSTD)%nat ->
    take NSTD fdv = l ->
    l !! i = Some FdClosed ->
    fd_st_of_key v0 fdv = FdClosed.
  Proof using .
    intros H0 Hi Htake Hli. rewrite /fd_st_of_key H0.
    destruct (decide (0 <= Z.of_nat i < Z.of_nat NOFILE)) as [_ | Hc];
      [ | exfalso; apply Hc; unfold NOFILE, NSTD in *; lia ].
    rewrite <- Htake in Hli.
    rewrite lookup_take in Hli; [ | exact Hi ].
    rewrite Nat2Z.id Hli. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  S2  THE SUPPLY AT THAT ARM                                          *)
  (* =================================================================== *)
  (* [UShLine.ush_read_sup_closed]'s twin at row 16, and at ANY cursor
     family [Q]: the closed arm of [SpecFilewrite.filewrite_in] is [emp]
     and reads no field of the family, so the deposit is minted from
     nothing and the lent heap and table go straight back.  Stated at the
     shape [UkRun.udepwf_std] the two write leaves take, so that it plugs
     in where [UkWriteLeaf.uwrite_chain_sup] does. *)
  Lemma uwrite_sup_closed (N : uk_names Σ) (Q : nat -> iProp Σ)
      (m : regfile) (pc : mword 64) (l : list fdstate) (i : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat i ->
    (i < NSTD)%nat ->
    l !! i = Some FdClosed ->
    ⊢ udepwf_std N m pc 16 (xfam_wr Q (ukn_pay N)) l.
  Proof using .
    intros H0 Hi Hli.
    rewrite /udepwf_std. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Htake _ Hheap Hufd".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_write_intro_at uslot (xfam_wr Q (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
              (m !!! Regidx a2_idx) fdv M _ _ _
              (tf_of_arg0 m pc) (tf_of_arg1 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all)
              eq_refl eq_refl eq_refl eq_refl).
    rewrite (uwr_fd_st_closed (m !!! Regidx a0_idx) fdv l i H0 Hi Htake Hli).
    rewrite /filewrite_in. done.
  Qed.

  (* =================================================================== *)
  (*  S3  THE TWO OBLIGATIONS, MET BY THE SYSCALL'S OWN ARM               *)
  (* =================================================================== *)
  (* the ecall leaves take [UexecSG.sfam] and an [xfam]-typed argument is
     not one until the instance is fixed -- [UInitBanner.kbn_fam]'s mould.
     At the TRIVIAL cursor family: the closed arm has no cursor to move. *)
  Definition kwc_fam (N : uk_names Σ) : sfam :=
    xfam_wr (fun _ => True%I) (ukn_pay N).

  (* the descriptor the stub traps with is the caller's a0: the stub
     writes a7 and then a0, and a7 is neither *)
  Local Lemma a0_after_a7 (m : regfile) (fdw : mword 64) (i : nat) :
    m !!! Regidx a0_idx = fdw ->
    bv_signed (trunc32 fdw) = Z.of_nat i ->
    bv_signed (trunc32
      ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
         !!! Regidx a0_idx)) = Z.of_nat i.
  Proof using .
    intros Ha0 Hfd.
    rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite Ha0. exact Hfd.
  Qed.

  (* THE SHELL'S, per call: [write(fdw, ua, nb)] at a ledger whose slot
     [i] -- the one [fdw] names -- is closed.  The ledger goes in and comes
     back, nothing is deposited and nothing is printed.  [UkSh.ksh_w_of_law]
     is the same statement paid from the free law; this one is paid from
     the kernel's own closed arm and takes no law at all. *)
  Lemma ksh_w_of_closed (N : uk_names Σ) (fdw ua : mword 64) (nb : nat)
      (l : list fdstate) (i : nat) :
    bv_signed (trunc32 fdw) = Z.of_nat i ->
    (i < NSTD)%nat ->
    l !! i = Some FdClosed ->
    ⊢ UkSh.ksh_w N fdw ua nb
        (UserFd.ustd (ukn_fd N) l) (UserFd.ustd (ukn_fd N) l).
  Proof using .
    intros Hfd Hi Hli.
    iIntros (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode Hstd Hrun Hcont".
    iApply (UkSh.wp_ksh_write_chain N h m avail
              (kwc_fam N) l
              with "Hcode Hrun [] Hstd").
    { (* THE DEPOSIT: the closed arm's, from nothing *)
      iApply (uwrite_sup_closed N (fun _ => True%I)
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int ShSyms.write : mword 64) 2)
                l i (a0_after_a7 m fdw i Ha0 Hfd) Hi Hli). }
    iIntros (h' ret W cw' cs') "_ _ _ _ Hstd _ Hrun".
    iApply ("Hcont" $! h' ret with "Hstd Hrun").
  Qed.

  (* one byte as the one-byte run the buffered leaf takes, both ways
     ([UInitBanner.ubytesq_one], restated here because that file sits
     above the application and this one does not) *)
  Local Lemma ubyte_run_one (γd : gname) (a : Z) (b : bv 8) :
    ubyte γd a b ⊣⊢ ubytesq γd (DfracOwn 1) a 1%nat (fun _ => b).
  Proof using . by rewrite /ubyte /ubytesq /= Z.add_0_r right_id. Qed.

  Local Lemma ubyte_to_run (γd : gname) (a : Z) (b : bv 8) :
    ubyte γd a b -∗ ubytesq γd (DfracOwn 1) a 1%nat (fun _ => b).
  Proof using . rewrite (ubyte_run_one γd a b). by iIntros "$". Qed.

  Local Lemma ubyte_of_run (γd : gname) (a : Z) (b : bv 8) :
    ubytesq γd (DfracOwn 1) a 1%nat (fun _ => b) -∗ ubyte γd a b.
  Proof using . rewrite (ubyte_run_one γd a b). by iIntros "$". Qed.

  (* INIT'S, per byte: putc's [write(fdw, &c, 1)] at a ledger whose slot
     [i] is closed.  The byte comes back with the ledger, as [kinit_w1]
     asks; [UkInit.kinit_w1_of_law] is the free-law twin. *)
  Lemma kinit_w1_of_closed (N : uk_names Σ) (fdw : mword 64) (b : bv 8)
      (l : list fdstate) (i : nat) :
    bv_signed (trunc32 fdw) = Z.of_nat i ->
    (i < NSTD)%nat ->
    l !! i = Some FdClosed ->
    ⊢ UkInit.kinit_w1 N fdw b
        (UserFd.ustd (ukn_fd N) l) (UserFd.ustd (ukn_fd N) l).
  Proof using .
    intros Hfd Hi Hli.
    iIntros (h m avail) "%Ha0 %Ha2 #Hcode Hbuf Hstd Hrun Hcont".
    iApply (UkInit.wp_kinit_write_chain N h m avail
              (kwc_fam N) l
              (DfracOwn 1) 1%nat (fun _ => b)
              with "Hcode Hrun [] Hstd [Hbuf]").
    { (* THE DEPOSIT: the closed arm's, from nothing *)
      iApply (uwrite_sup_closed N (fun _ => True%I)
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int InitSyms.write : mword 64) 2)
                l i (a0_after_a7 m fdw i Ha0 Hfd) Hi Hli). }
    { iApply (ubyte_to_run with "Hbuf"). }
    iIntros (h' ret W cw' cs') "_ _ _ _ _ _ Hstd Hbuf _ Hrun".
    iApply ("Hcont" $! h' ret with "[Hbuf] Hstd Hrun").
    iApply (ubyte_of_run with "Hbuf").
  Qed.

  (* =================================================================== *)
  (*  S4  THE WITNESSES, AT INIT'S HEAD LEDGER                            *)
  (* =================================================================== *)
  (* [UInitFd.ufd_l0] is the ledger /init enters with -- every standard
     stream closed -- and it is the ledger the audit's two sites are at:
     sh's prompt and diagnostics go to fd 2, init's banner to fd 1.  Both
     premises are closed facts there. *)
  Lemma ksh_w_of_closed_l0 (N : uk_names Σ) (ua : mword 64) (nb : nat) :
    ⊢ UkSh.ksh_w N (mword_of_int 2 : mword 64) ua nb
        (UserFd.ustd (ukn_fd N) ufd_l0) (UserFd.ustd (ukn_fd N) ufd_l0).
  Proof using .
    apply (ksh_w_of_closed N (mword_of_int 2) ua nb ufd_l0 2%nat
             ltac:(vm_compute; reflexivity)
             ltac:(unfold NSTD; lia)
             ltac:(reflexivity)).
  Qed.

  Lemma kinit_w1_of_closed_l0 (N : uk_names Σ) (b : bv 8) :
    ⊢ UkInit.kinit_w1 N (mword_of_int 1 : mword 64) b
        (UserFd.ustd (ukn_fd N) ufd_l0) (UserFd.ustd (ukn_fd N) ufd_l0).
  Proof using .
    apply (kinit_w1_of_closed N (mword_of_int 1) b ufd_l0 1%nat
             ltac:(vm_compute; reflexivity)
             ltac:(unfold NSTD; lia)
             ltac:(reflexivity)).
  Qed.

End UkWriteClosed.
