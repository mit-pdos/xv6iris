(* ===================================================================== *)
(*  UkShRedirChild.v -- THE REDIRECT CHILD'S WALK, 0x9c0 TO ITS EXITS     *)
(*                                                                       *)
(*  [UkShRedirSeam.wp_kshm_child_alloc_redir_g] (parse, close(1), the     *)
(*  open as the application's call) with both of its continuations        *)
(*  filled: [exec /echo] at the fd-1 row the open left                    *)
(*  ([UkShEcho.wp_kshr_exec_echo_at_holds]), and the failed open's        *)
(*  diagnostic PAID ([UkShRedirPaid.wp_kshd_openfail_paid]).  No          *)
(*  [UkSh.sh_deps] anywhere on the walk, which is what makes it a         *)
(*  verified shell's and not only a tainted one's.                        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith.
Require Import UserHeap UkRun.
Require Import FdSlots UserFd.
Require Import UCodeShK UCodeShP.
Require Import LineWords.
Require Import FileDisc.        (* [uline]: the three lines the file
                                   discipline admits *)
Require Import UkSh.
Require Import UkShParse.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import UkShRedirPc.     (* [ushs_nulcut]: the redirect line's cut *)
Require Import UkShEcho.        (* [echo_argv_bytes] and the exec arm *)
Require Import UkShRedirSeam.   (* [wp_kshm_child_alloc_redir]: the walk *)
Require Import UShLexRedir.     (* [ush_line_toks_holds_redir] *)
Require Import PipeNames.
Require Import UkShRedirLine.   (* [ushs_line_is] and the typed bridge *)
Require Import CtxIdDefs.
Require Import UexecSG.
Require Import UserCwd.
Require Import UserChildren.
Require Import UserPerm.        (* [usz_ok] *)
Require Import UserPtTree.
Require Import ChildTok.
Require Import UkShRedirBody.   (* [ushs_fd1f] / [echo_argv_bytes_of_redir] *)
Require Import UkShRedirAns.    (* [ush_open_call2]: the open, the deed its hand *)
Require Import UkShRedirPaid.   (* the paid open-failed diagnostic; the call's adapter *)
Local Open Scope Z_scope.
Import Defs.

Section UkShRedirChild.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation s1_idx := (mword_of_int 9 : mword 5).

  (* RESTATED ON THE GENERIC SEAM (the PROGRAM STREAM, stretch 9).  The
     landed statement took [UkShRedir.ush_open_call] -- the call with no
     [-1] payload and no path -- and [UkSh.sh_deps] for the failed open's
     diagnostic; the application proves [UkShRedirAns.ush_open_call2] and
     holds [sh_deps] only under the taint, so nothing could apply it.

     FAMILY-FREE: the lend is [Cr], and what varies is said in pieces --
       [Cr -∗ Dd a ∗ Cr']   the lend splits AT THE CALL (the deed goes in);
       [K ty ={⊤}=∗ K' ty]  the receipt's READING, one invariant opening
                            right after the open returns (the exec supply
                            is a [□] box with no fupd in its body, so the
                            pure facts K1's entry wants must be in [K']);
       [Cx] / [Cd]          where the exec-failed and the open-failed
                            diagnostics leave the credential.
     Every exit is paid by a law into the payload [Q]. *)
  Lemma wp_kshm_child_file_redir {A : Type}
      (N' : uk_names Σ) (Hc : ukn_const N')
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 : Z) (len : nat) (ws : list (list (bv 8))) (file : list (bv 8))
      (fb : nat -> bv 8) (sz : Z) (ld : list fdstate) (st1 : fdstate)
      (n : nat) (Q : Z -> iProp Σ)
      (K K' : fdtype -> iProp Σ) (Dd Kf : A -> iProp Σ) (a : A)
      (Cr Cr' Cx Cd : iProp Σ) :
    ukn_pay N' = Q ->
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    UkShRedirLine.ushs_line_is ws file fb 0%nat len ->
    (* THE FILE IS A NAME OF THE CLASS, of any length (cut W3) *)
    FileDisc.uname file ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    ld !! 1%nat = Some st1 ->
    st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : PipeNames.pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    UkSh.ush_fd2p ld ->
    fd_lowest_closed (<[1%nat := FdClosed]> ld) = Some 1%nat ->
    UCodeShK.shk_code (ukn_t N') -∗
    UkSh.ush_jtab (ukn_t N') -∗
    UCodeShP.shp_code (ukn_t N') -∗
    UCodeShP.shp_rodata (ukn_t N') -∗
    ustr (ukn_d N') (DfracOwn 1) s0 len fb -∗
    ustr (ukn_d N') dw ushp_whitespace 5 ushp_ws_f -∗
    ustr (ukn_d N') dv ushp_symbols 7 ushp_sym_f -∗
    UserFd.ustd (ukn_fd N') ld -∗
    UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
    UserChildren.uch_any (ukn_ch N') -∗
    UkShMalloc.ushm_fresh N' sz -∗
    (* the open, as the application's CALL premise -- the deed its hand *)
    UkShRedirAns.ush_open_call2 N' FsImg.ROOTINO
      (s0 + Z.of_nat (S (S (length (wl_body ws) + 1)))) 1537 file
      (<[1%nat := FdClosed]> ld) K Dd Kf -∗
    □ (∀ ty : fdtype, K ty ={⊤}=∗ K' ty) -∗
    (* ...the child's exec supply AT THE FILE the open returned, WITH THE
       RECEIPT IN THE LEND (RULING RECEIPT-IN-CR) *)
    (∀ ty : fdtype,
       UkShEcho.sh_exec_sup_echo_at (UkShRedirBody.ushs_fd1f ty) ws Q (Cr' ∗ K' ty)) -∗
    (∀ ty : fdtype, UkShDiag.ush_execfail_law (Cr' ∗ K' ty) Cx) -∗
    □ (Cx -∗ Q (-1)) -∗
    (* ...the FAILED OPEN's diagnostic, at what the call left of its hand *)
    UkShDiag.ush_execfail_law_at (FileDisc.alt_openfailN file) (13 + length file)%nat
      (Kf a ∗ Cr') Cd -∗
    □ (Cd -∗ Q (-1)) -∗
    (* ...and the lend, whole across the parse and split at the call *)
    □ (Cr -∗ Q (-1)) -∗
    (Cr -∗ Dd a ∗ Cr') -∗
    Cr -∗
    urun N' h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Hpeq Hs1 Hline Hfu Hs0 Hs64 Hs38 Hszlo Hszal Hszok
           Hst1 Hne Hnp Hfd2 Hfdl.
    iIntros "#Hcode #Hjt #Hpcode #Hpro Hstr Hws Hsy Hstd Hcwd Hch HM
             Hopen #Hrd Hsup #Hxl #Hcx #Hol #Hcd #Hpx Hsplit Hcr Hrun".
    iDestruct (UkSh.ush_jtab_ro with "Hjt") as "#Hro".
    (* the parser's premises, off the line (lane SH-LEX-REDIR) *)
    destruct (UShLexRedir.ush_line_toks_holds_redir ws file fb 0%nat len
                Hline) as (Hred & Htoks & Hpos & Htlen).
    pose proof (proj1 Hline) as Hok.
    pose proof (lookup_lt_Some ld 1%nat st1 Hst1) as Hlen1.
    (* the REDIR node's file string IS the line's name *)
    set (gp := (length (wl_body ws) + 1)%nat).
    set (fe := (length (wl_body ws) + 3 + length file)%nat).
    set (fu := UkShRedirSeam.ushs_file s0 len (fun j : nat => fb (0 + j)%nat)
                 (wl_toks ws) gp fe).
    assert (Hful : ua_len fu = length file).
    { rewrite /fu /UkShRedirSeam.ushs_file. cbn [ua_len]. unfold fe, gp. lia. }
    assert (Hfub : forall j : nat, (j < length file)%nat ->
                     ua_bytes fu j = file !!! j).
    { intros j Hj. rewrite /fu /UkShRedirSeam.ushs_file. cbn [ua_bytes].
      rewrite (UkShRedirSeam.ushs_nulcut_filebyte len
                 (fun j : nat => fb (0 + j)%nat) gp fe (wl_toks ws)
                 Hred Htoks j ltac:(unfold fe, gp; lia)).
      destruct Hline as (_ & _ & _ & _ & _ & _ & _ & Hfb & _).
      rewrite <- (Hfb j Hj).
      f_equal. unfold gp. lia. }
    assert (Hfd2c : UkSh.ush_fd2p (<[1%nat := FdClosed]> ld)).
    { destruct Hfd2 as [ rb Hrb ]. exists rb.
      rewrite list_lookup_insert_ne; [ exact Hrb | lia ]. }
    iApply (UkShRedirSeam.wp_kshm_child_alloc_redir_g N' (Hpay := Hc)
              Hpsok_free h m dw dv s0 FsImg.ROOTINO len fb (wl_toks ws)
              gp fe sz ld st1 n (Dd a) K (Kf a) Cr Cr'
              Hs1 Hred Htoks Hpos Htlen Hs0 Hs64 Hs38 Hst1 Hne Hnp
              Hszlo Hszal Hszok
              with "Hcode Hjt Hpcode Hpro Hstr Hws Hsy Hstd Hcwd HM
                    [Hopen] [] Hsplit Hcr Hrun").
    { iApply (UkShRedirPaid.ush_open_call_g_of_call2 N' fu file 1537
                (<[1%nat := FdClosed]> ld) K Dd Kf a Hfu Hful Hfub Hfdl
                with "Hopen"). }
    { iIntros "!> Hc". rewrite Hpeq. iApply ("Hpx" with "Hc"). }
    iSplit.
    - (* ============ the open SUCCEEDED: exec /echo at fd 1 = f ============ *)
      iIntros (hf mf q ty) "%Ha0f #Hsub Hstd Hcwd HK HM2 Hcr Hrun".
      iApply fupd_wp. iMod ("Hrd" $! ty with "HK") as "HK". iModIntro.
      assert (Hfd1' : UkShRedirBody.ushs_fd1f ty
                (<[1%nat := FdOpen false true ty]>
                   (<[1%nat := FdClosed]> ld))).
      { rewrite /UkShRedirBody.ushs_fd1f. apply list_lookup_insert.
        rewrite length_insert. exact Hlen1. }
      assert (Hfd2' : UkSh.ush_fd2p
                (<[1%nat := FdOpen false true ty]>
                   (<[1%nat := FdClosed]> ld))).
      { destruct Hfd2 as [ rb Hrb ]. exists rb.
        rewrite list_lookup_insert_ne; [ | lia ].
        rewrite list_lookup_insert_ne; [ exact Hrb | lia ]. }
      (* the break, out of the free list the parse left *)
      iDestruct "HM2" as (R') "[_ HM2]".
      rewrite /UkShMalloc.ushm_one.
      iDestruct "HM2" as (cq) "(_ & _ & _ & _ & _ & Hsz)".
      (* the argv bytes at the REDIRECT cut *)
      pose proof (UkShRedirBody.echo_argv_bytes_of_redir ws file fb 0%nat len
                    (length (wl_body ws) + 3 + length file)%nat Hline eq_refl)
        as Hbytes.
      replace (UkShDiag.ush_Dg + (70 + n))%nat
        with (6 + (2 + (UkShDiag.ush_Dg + (62 + n))))%nat by lia.
      iApply (UkShEcho.wp_kshr_exec_echo_at_holds (UkShRedirBody.ushs_fd1f ty) ws Q
                (Cr' ∗ K' ty)%I Cx N' Hc hf mf q (sz + 65536) s0
                (UkShRedirPc.ushs_nulcut (wl_toks ws) len
                   (fun j : nat => fb (0 + j)%nat)
                   (length (wl_body ws) + 3 + length file)%nat)
                (<[1%nat := FdOpen false true ty]> (<[1%nat := FdClosed]> ld))
                (62 + n)%nat
                Hok Hpeq Ha0f Hbytes Hfd1' Hfd2'
                with "Hcode [Hsup] [Hxl] Hcx Hjt Hsub Hsz Hstd Hcwd Hch [Hcr HK]
                      Hrun").
      + iApply ("Hsup" $! ty).
      + iApply ("Hxl" $! ty).
      + iFrame "Hcr HK".
    - (* ============ the open FAILED: the diagnostic, exit(1) ============ *)
      iIntros (hf mf) "%Hat #Hfp #Hfs Hstd Hcwd HKf Hcr Hrun".
      iApply (UkShRedirPaid.wp_kshd_openfail_paid N' (Kf a ∗ Cr')%I Cd
                (<[1%nat := FdClosed]> ld) hf mf (70 + n)%nat fu file
                Hfd2c Hat Hful Hfub
                with "Hol Hcode Hro Hfp Hfs Hstd [HKf Hcr] [] Hrun").
      + iFrame "HKf Hcr".
      + iIntros "_ Hc". rewrite Hpeq. iApply ("Hcd" with "Hc").
  Qed.

End UkShRedirChild.
