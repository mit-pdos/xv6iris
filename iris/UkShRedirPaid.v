(* ===================================================================== *)
(*  UkShRedirPaid.v -- THE REDIRECT CHILD'S TWO PAID PIECES               *)
(*                                                                       *)
(*  sh's redirect child is a PAID child: its exit payload is the era's    *)
(*  console credential ([UkShFork.ushf_wq]), so nothing it prints may go  *)
(*  through the free write law ([UkSh.sh_deps], which a verified shell    *)
(*  holds only under the taint), and what it opens is the application's   *)
(*  file, whose open takes the DEED.  [UkShRedir.wp_kshr_redir_arm_g]     *)
(*  leaves both to its caller; this file is the two fillings:             *)
(*                                                                       *)
(*    S1  the "open f failed" diagnostic on a LAW ([UkShDiag.             *)
(*        ush_execfail_law_at] -- the law is already general in its       *)
(*        bytes), [UkShDiag.wp_kshd_execfail_paid]'s twin at the 0x10e    *)
(*        site;                                                          *)
(*    S2  the name `f`, as the image the open's ecall reads, out of the   *)
(*        REDIR node's own file string;                                  *)
(*    S3  [UkShRedirAns.ush_open_call2] as an instance of the generic     *)
(*        call ([UkShRedir.ush_open_call_g]), the deed the call's hand.   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UserBits.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunMem.
Require Import UCodeShK.
Require Import UkSh.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShRedir.
Require Import UkShRedirAns.
Require Import ChildTok.
Require Import FileDisc.           (* [alt_openfail] *)
Require Import FdSlots.
Require Import UserFd.
Require Import UexecSG.
Require Import ArgPath.            (* [arg_path_of] *)
Require Import PathElems.          (* [path_elems] *)
Require Import FsAbsEra.           (* [np_elems] / [um_start_of] *)
Require Import FsImg.
Require Import FsImgCheck.         (* [fname_f] *)
Local Open Scope Z_scope.
Import Defs.

Section UkShRedirPaid.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  S1  "open f failed", PAID                                           *)
  (* =================================================================== *)
  Lemma ush_openfail_len : length alt_openfail = 16%nat.
  Proof using . vm_compute. reflexivity. Qed.

  Lemma ush_openfail_lookup (p : nat) :
    (p < 16)%nat -> alt_openfail !! p = Some (alt_openfail !!! p).
  Proof using .
    intros Hp. apply list_lookup_lookup_total_lt. rewrite ush_openfail_len.
    exact Hp.
  Qed.

  (* the format's two windows at 0x12c8 ("open " and " failed\n") and the
     one-byte argument are the alternative's first fourteen bytes *)
  Lemma ush_openfail_w1 :
    forall p : nat, (0 <= p < 0 + 5)%nat ->
      shd_lit 0x12c8 p = alt_openfail !!! p.
  Proof using . apply ush_bytes_of_forallb. vm_compute. reflexivity. Qed.

  Lemma ush_openfail_arg :
    FsImgCheck.fname_f !!! 0%nat = alt_openfail !!! 5%nat.
  Proof using . apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma ush_openfail_w2 :
    forall p : nat, (7 <= p < 7 + 8)%nat ->
      shd_lit 0x12c8 p = alt_openfail !!! (p - 1)%nat.
  Proof using .
    apply (ush_bytes_of_forallb (shd_lit 0x12c8)
             (fun p : nat => alt_openfail !!! (p - 1)%nat)).
    vm_compute. reflexivity.
  Qed.

  (* THE WALK: [UkShDiag.ush_diag_leaf_holds]'s 0x10e arm at the law's
     family, the ledger riding beside the credential.  The argument is the
     REDIR node's file, which the discipline makes the one byte `f`. *)
  Lemma wp_kshd_openfail_paid (N : uk_names Σ) `{!ukn_const N}
      (Cr Cd : iProp Σ) (l : list fdstate) (h : CpuId) (m : regfile)
      (n : nat) (x : uarg) :
    UkSh.ush_fd2p l ->
    UkShRun.ush_diag_at 0x10e m ->
    ua_len x = 1%nat ->
    ua_bytes x 0%nat = FsImgCheck.fname_f !!! 0%nat ->
    ush_execfail_law_at alt_openfail 14%nat Cr Cd -∗
    shk_code (ukn_t N) -∗
    shk_rodata (ukn_t N) -∗
    UkShRun.ush_ptr (ukn_d N) (uint (m !!! Regidx s1_idx) + 16) (ua_ptr x) -∗
    UkShRun.ush_str (ukn_d N) x -∗
    UserFd.ustd (ukn_fd N) l -∗
    Cr -∗
    (UserFd.ustd (ukn_fd N) l -∗ Cd -∗ ukn_pay N (-1)) -∗
    urun N h m (mword_of_int 0x10e) (ush_Dg + n) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hfd2 Hat Hxlen Hxb.
    assert (Hal : uint (m !!! Regidx s1_idx) mod 8 = 0).
    { destruct Hat as [ [Hc _] | [ [Hc _] | [_ Hal] ] ];
        [ exfalso; vm_compute in Hc; discriminate Hc
        | exfalso; discriminate Hc | exact Hal ]. }
    iIntros "#Hlaw #Hcode #Hro #Hw [%Hxr #Hxs] Hstd Hc Hpay Hrun".
    iDestruct ("Hlaw" $! N l with "[%] Hc") as (Pf) "(HPf & #Hstep & #Hdone)";
      [ exact Hfd2 | ].
    replace (ush_Dg + n)%nat with (10 + (12 + (4 + (n + 2))))%nat
      by (unfold ush_Dg; lia).
    (* ---- 0x10e  c.ld a2,16(s1) -- rcmd->file ---- *)
    iApply (UkShRun.wp_uk_cldq N h m (mword_of_int 0x10e)
              (mword_of_int 2 : mword 5) (mword_of_int 1 : mword 3)
              (mword_of_int 4 : mword 3) s1_idx a2_idx DfracDiscarded
              (uint (m !!! Regidx s1_idx) + 16) (mword_of_int (ua_ptr x))
              (10 + (12 + (4 + (n + 2))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute uoff_c8; lia)
              ltac:(rewrite Zplus_mod Hal; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw Hrun").
    { iApply (uis_shk_10e with "Hcode"). }
    iIntros "_".
    assert (E10e : add_vec_int (mword_of_int 0x10e : mword 64) 2
                   = mword_of_int 0x110)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E10e. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int (ua_ptr x) : mword 64)]> m).
    iDestruct (shd_str_of_ustr (ukn_t N) (ukn_d N) DfracDiscarded (ua_ptr x)
                 (ua_len x) (ua_bytes x)
                 with "Hxs") as "#Hs".
    assert (Hlits110 : shd_die_lits 0x110 0x114 0x118 0x11a 0x11e 0x120
                      (mword_of_int 1 : mword 20) (mword_of_int 440 : mword 12)
                      (mword_of_int 3992 : mword 21) (mword_of_int 2918 : mword 21)
                      (mword_of_int 1 : mword 6)
                      0x12c8 15%nat 5%nat)
      by shd_die_solve.
    set (C1 := (fun p : nat => UserFd.ustd (ukn_fd N) l ∗ Pf p)%I).
    set (C2 := (fun p : nat => UserFd.ustd (ukn_fd N) l ∗ Pf (5 + p)%nat)%I).
    set (C3 := (fun p : nat => UserFd.ustd (ukn_fd N) l ∗ Pf (p - 1)%nat)%I).
    assert (E12 : C1 5%nat = C2 0%nat) by reflexivity.
    assert (E23 : C2 (ua_len x) = C3 (S (S 5%nat)))
      by (rewrite Hxlen; reflexivity).
    iApply (wp_kshd_die_chain N false DfracDiscarded
              0x110 0x114 0x118 0x11a 0x11e 0x120
              (mword_of_int 1 : mword 20) (mword_of_int 440 : mword 12)
              (mword_of_int 3992 : mword 21) (mword_of_int 2918 : mword 21)
              (mword_of_int 1 : mword 6)
              0x12c8 15%nat 5%nat
              (ua_ptr x) (ua_len x) (ua_bytes x) C1 C2 C3 h1 m1 (n + 2)
              Hlits110
              ltac:(lia)
              ltac:(exact (upd_eq m (Regidx a2_idx) (regval_into_reg _)))
              E12 E23
              with "[] [] [] [Hstd HPf] Hcode Hro Hs [] [] [] [] [] [] [Hpay] Hrun").
    { iModIntro. iIntros (p) "%Hp". rewrite /C1.
      rewrite (ush_openfail_w1 p ltac:(lia)).
      iApply ("Hstep" $! p (alt_openfail !!! p) with "[%] [%]").
      { apply ush_openfail_lookup. lia. }
      { lia. } }
    { iModIntro. iIntros (p) "%Hp". rewrite /C2. rewrite Hxlen in Hp.
      assert (p = 0%nat) as -> by lia.
      rewrite Hxb ush_openfail_arg.
      iApply ("Hstep" $! 5%nat (alt_openfail !!! 5%nat) with "[%] [%]").
      { apply ush_openfail_lookup. lia. }
      { lia. } }
    { iModIntro. iIntros (p) "%Hp". rewrite /C3.
      rewrite (ush_openfail_w2 p ltac:(lia)).
      replace (S p - 1)%nat with (S (p - 1))%nat by lia.
      iApply ("Hstep" $! (p - 1)%nat (alt_openfail !!! (p - 1)%nat)
                with "[%] [%]").
      { apply ush_openfail_lookup. lia. }
      { lia. } }
    { rewrite /C1. iFrame "Hstd HPf". }
    { iApply (uis_shk_110 with "Hcode"). }
    { iApply (uis_shk_114 with "Hcode"). }
    { iApply (uis_shk_118 with "Hcode"). }
    { iApply (uis_shk_11a with "Hcode"). }
    { iApply (uis_shk_11e with "Hcode"). }
    { iApply (uis_shk_120 with "Hcode"). }
    { rewrite /C3. iIntros "[Hstd HPf]". cbn [Nat.sub].
      iApply ("Hpay" with "Hstd"). iApply ("Hdone" with "HPf"). }
  Qed.

  (* =================================================================== *)
  (*  S2  THE NAME `f` AS THE IMAGE THE OPEN READS                        *)
  (* =================================================================== *)
  Lemma ushr_fname_shape : arg_path_shape FsImgCheck.fname_f.
  Proof using .
    split; [ vm_compute; reflexivity | ].
    intros j b Hb.
    destruct j as [| j]; cbn in Hb; [ | discriminate Hb ].
    injection Hb as <-.
    intro Hc. apply (f_equal bv_unsigned) in Hc.
    vm_compute in Hc. discriminate Hc.
  Qed.

  Lemma ushr_fname_last :
    list_basics.last (path_elems FsImgCheck.fname_f) = Some FsImgCheck.fname_f.
  Proof using . vm_compute. reflexivity. Qed.

  Lemma ushr_fname_np : np_elems FsImgCheck.fname_f = [].
  Proof using . vm_compute. reflexivity. Qed.

  Lemma ushr_fname_start (cwv : Z) :
    um_start_of cwv FsImgCheck.fname_f = cwv.
  Proof using .
    unfold FsAbsEra.um_start_of.
    destruct (decide (FsImgCheck.fname_f !! 0%nat = Some PathElems.SLASH))
      as [He | _]; [ | reflexivity ].
    exfalso. vm_compute in He. discriminate He.
  Qed.

  Local Lemma ushr_uint_avi (p k : Z) :
    0 < p < 2 ^ 38 -> 0 <= k < 2 ^ 31 ->
    uint (add_vec_int (mword_of_int p : mword 64) k) = p + k.
  Proof using .
    intros Hp Hk.
    assert (Hpu : bv_unsigned (mword_of_int p : mword 64) = p)
      by (apply moi_small; unfold Z64; lia).
    rewrite uint_unsigned.
    rewrite (uint_add_vec_int_small (mword_of_int p : mword 64) k
               ltac:(lia) ltac:(rewrite Hpu; lia)).
    rewrite Hpu. reflexivity.
  Qed.

  Lemma ushr_fname_img (γd : gname) (x : uarg) :
    ua_len x = 1%nat ->
    ua_bytes x 0%nat = FsImgCheck.fname_f !!! 0%nat ->
    UkShRun.ush_str γd x -∗
    ∃ Img : gmap Z (bv 8),
      ⌜ forall M : gmap Z (bv 8), uimg_sub Img M ->
          arg_path_of M (mword_of_int (ua_ptr x) : mword 64)
            FsImgCheck.fname_f ⌝
      ∗ ([∗ map] ad ↦ b ∈ Img, ubyteq γd DfracDiscarded ad b).
  Proof using .
    intros Hlen Hb. iIntros "[%Hr #Hs]". rewrite Hlen.
    iDestruct (ustr_byte γd DfracDiscarded (ua_ptr x) 1 (ua_bytes x) 0%nat
                 ltac:(lia) with "Hs") as "[#Hb0 _]".
    iDestruct (ustr_nul γd DfracDiscarded (ua_ptr x) 1 (ua_bytes x)
                 with "Hs") as "[#Hb1 _]".
    iExists (<[ua_ptr x + Z.of_nat 0 := ua_bytes x 0%nat]>
               (<[ua_ptr x + Z.of_nat 1 := ubyte0]> ∅)).
    iSplit.
    - iPureIntro. intros M Hsub. split; [ exact ushr_fname_shape | ]. split.
      + intros j b Hj.
        destruct j as [| j]; cbn in Hj; [ | discriminate Hj ].
        injection Hj as <-.
        rewrite (ushr_uint_avi (ua_ptr x) (Z.of_nat 0) Hr ltac:(lia)).
        apply Hsub. rewrite lookup_insert.
        f_equal. rewrite Hb. reflexivity.
      + change (length FsImgCheck.fname_f) with 1%nat.
        rewrite (ushr_uint_avi (ua_ptr x) (Z.of_nat 1) Hr ltac:(lia)).
        apply Hsub. rewrite lookup_insert_ne; [ | lia ].
        rewrite lookup_insert. f_equal. apply bv_eq. vm_compute. reflexivity.
    - rewrite big_sepM_insert;
        [ | rewrite lookup_insert_ne; [ apply lookup_empty | lia ] ].
      iSplitR; [ iExact "Hb0" | ].
      rewrite big_sepM_insert; [ | apply lookup_empty ].
      iSplitR; [ iExact "Hb1" | ]. by rewrite big_sepM_empty.
  Qed.

  (* =================================================================== *)
  (*  S3  THE FILE APPLICATION'S CALL IS AN INSTANCE OF THE GENERIC ONE   *)
  (*                                                                     *)
  (*  The hand is the DEED at the state the caller names; the four path   *)
  (*  facts are closed facts about `f`, the cwd is the root (so the start *)
  (*  is), and the image is the node's own string.                        *)
  (* =================================================================== *)
  Lemma ush_open_call_g_of_call2 {A : Type} (N : uk_names Σ) (file : uarg)
      (mode : Z) (l : list fdstate) (K : fdtype -> iProp Σ)
      (Dd Kf : A -> iProp Σ) (a : A) :
    ua_len file = 1%nat ->
    ua_bytes file 0%nat = FsImgCheck.fname_f !!! 0%nat ->
    fd_lowest_closed l = Some 1%nat ->
    UkShRedirAns.ush_open_call2 N FsImg.ROOTINO (ua_ptr file) mode l K Dd Kf -∗
    UkShRedir.ush_open_call_g N FsImg.ROOTINO file mode l (Dd a) K (Kf a).
  Proof using .
    intros Hlen Hb Hfdl. iIntros "Hc".
    rewrite /UkShRedirAns.ush_open_call2 /UkShRedir.ush_open_call_g.
    iIntros (h m av) "%Ha0 %Ha1 #Hstr Hd #Hcode Hcwd Hstd Hrun Hcont".
    iDestruct (ushr_fname_img (ukn_d N) file Hlen Hb with "Hstr")
      as (Img) "[%Hpath #Himg]".
    iApply ("Hc" $! h m av Img FsImgCheck.fname_f a
              with "[%] [%] [%] [%] [%] [%] [%] Himg Hd Hcode Hcwd Hstd Hrun");
      [ exact Ha0 | exact Ha1 | exact Hpath | exact ushr_fname_np
      | exact (ushr_fname_start FsImg.ROOTINO) | exact ushr_fname_last
      | exact Hfdl | ].
    iIntros (h' m' r) "%Hcs %Hr Hcwd Hans Hrun".
    iApply ("Hcont" $! h' m' r with "[%//] [%//] Hcwd [Hans] Hrun").
    rewrite /UkShRedirAns.ush_open_ans2 /UkShRedir.ush_open_ans_g.
    iExact "Hans".
  Qed.

End UkShRedirPaid.
