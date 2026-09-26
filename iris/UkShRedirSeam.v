(* ===================================================================== *)
(* UkShRedirSeam.v -- the SEAM and the CHILD at the redirect shape,       *)
(* lane SH-PARSE-2 (design/app-file.md SS5.1).                            *)
(*                                                                        *)
(* [UkShMain.ush_cmd_of_ushp] turns the parser's EXEC node into the       *)
(* runner's tree; this file does the same for a REDIR node over one.  The *)
(* exec half is [UkShMain.ush_cmd_of_ushp_gen] -- the conversion at what   *)
(* it actually needs, which is three facts about the cut line and not the *)
(* cut itself -- and what is added here is the REDIR node's own five      *)
(* fields and the FILE NAME as a [UserHeap.uarg].                          *)
(*                                                                        *)
(* THE SEPARATION FACT IS REUSED, NOT RE-PROVED.  The argument tokens all *)
(* end below the '>', and every scan that measures them stops below it    *)
(* too, so they are [ushp_tokens] of the line TRUNCATED at the '>' --     *)
(* whose only symbol byte is the one the truncation cut off.  That is     *)
(* [ushs_toks_below], and it puts [UkShMain.ushp_tokens_gap] back in      *)
(* scope unchanged.                                                       *)
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
Require Import UserPtTree.
Require Import UmodeArith UmodeAbi.
Require Import UserPerm.
Require Import UserHeap UkRun UkRunLeaf.
Require Import FdSlots UserFd.
Require Import UCodeShK.
Require Import UCodeShP.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShParseCmd.
Require Import UkShRedirCmd.
Require Import UkShRedirCut.    (* [ushs_nulcut]: the redirect line's cut *)
Require Import UkShRedir.
Require Import UkShMain.
Require Import RefParse.
Require Import RefParseSym.    (* [ref_parsecmd_redir]: the redirect line at the reference *)
Require Import UkShRedirs.      (* [ushp_malloc_chain] *)
Require Import UkShParser.      (* [ushp_zero_at]: the reference's cut *)
Require Import UkShSeam.        (* THE SEAM AND THE CHILD, once *)
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UkShRedirSeam.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.

  (* the four ghost names a program proof runs at, as every file in the
     lane binds them *)
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT OWES ITS PARENT NOTHING at this lane, as a
     CLASS so that it reaches the exit ecall without an argument at every
     call site ([UkRun.ukn_triv]). *)
  Context `{Hpay : !ukn_const N}.
  (* THE CHILD'S PAYLOAD IS NOT TRIVIAL ANY MORE (lane IO-LEAF, M3b).
     There used to be a second class here, [UkRun.ukn_triv N], because the
     generic exec supply [UkRun.uxsup] is the exec bundle at the trivial
     payload and this file walks the process sh FORKED.  A child that has
     to ECHO A LINE cannot be at the trivial payload: what it owes its
     parent is the era's credential at the alternative it took.  So the
     two things the class was used for -- the free exit row and the exec
     supply -- are PREMISES of the two lemmas below, at whatever payload
     sh chose for its child. *)
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  Local Notation γch := (ukn_ch N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* THE NUMBERS THIS PROGRAM ADMITS ([UexecSG.uprogSG]'s [psok]).  A SECTION
     hypothesis, so no lemma statement in this file names it and the ~570
     [urun] sites did not move; the program's kernel-side constructor
     discharges it.
     AT THE FREE NUMBERS AND NO MORE (lane SUPPLY-SPLIT).  It used to read
     "every number but exec", which at the generic instance is true and at
     a VERIFIED program's instance is not: a program whose supplier is the
     application's ([AppInv.app_sup] -- for the echo application, the
     TAINT) could only ever be entered tainted.  What a verified program
     admits is [UexecSG.free_num] -- every number whose bundle is [emp],
     plus chdir, whose branch is a closed fact -- and at
     [UexecExecInst.uprogSG_free] this hypothesis is the identity.  A call
     at a number OUTSIDE that set takes its own deposit as a premise
     ([UkRun.udepw_law]) and is named at its site. *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).

(*ALIASES-BEGIN*)

  (* ===================================================================== *)
  (* §1 THE TOKEN MODEL, RESTRICTED TO THE PREFIX BEFORE THE '>'.           *)
  (*                                                                       *)
  (* The argument tokens of `w1 ... wn > f' all end before the '>', and     *)
  (* every scan that measures them stops before it too -- so they are       *)
  (* [UkShParse.ushp_tokens] of the line TRUNCATED at [gp], whose symbol    *)
  (* byte is the one the truncation cut off.  That is what lets the         *)
  (* separation fact ([UkShMain.ushp_tokens_gap]) be REUSED rather than     *)
  (* re-proved: it is a fact about token indices, and the indices are the   *)
  (* same on both readings.                                                 *)
  (* ===================================================================== *)

  Lemma ushs_skipws_trunc (n n' i : nat) (f : nat -> bv 8) :
    (n' <= n)%nat -> (ushp_skipws n i f <= n')%nat ->
    ushp_skipws n' i f = ushp_skipws n i f.
  Proof using .
    revert n i. induction n' as [| n' IH ]; intros n i Hle Hb.
    - cbn [ushp_skipws]. lia.
    - destruct n as [| n ]; [ lia | ].
      cbn [ushp_skipws] in Hb |- *.
      destruct (ushp_is_ws (f i)) eqn:Hw; [ | reflexivity ].
      f_equal. apply IH; lia.
  Qed.

  Lemma ushs_toklen_trunc (n n' i : nat) (f : nat -> bv 8) :
    (n' <= n)%nat -> (ushp_toklen n i f <= n')%nat ->
    ushp_toklen n' i f = ushp_toklen n i f.
  Proof using .
    revert n i. induction n' as [| n' IH ]; intros n i Hle Hb.
    - cbn [ushp_toklen]. lia.
    - destruct n as [| n ]; [ lia | ].
      cbn [ushp_toklen] in Hb |- *.
      destruct (ushp_is_ws (f i) || ushp_is_sym (f i)) eqn:Hw;
        [ reflexivity | ].
      f_equal. apply IH; lia.
  Qed.

  Lemma ushs_toks_below (len gp : nat) (f : nat -> bv 8) (off : nat)
      (toks : list (nat * nat)) :
    (off <= gp)%nat -> (gp <= len)%nat ->
    ushs_toks len f gp off toks -> ushp_tokens gp f off toks.
  Proof using .
    intros Hoff Hgp H. revert Hoff.
    induction H as [ off Hnil | off toks k n Hn Htoks IH ]; intro Hoff.
    - apply UshpTokNil.
      rewrite (ushs_skipws_trunc (len - off) (gp - off) off f
                 ltac:(lia) ltac:(lia)). exact Hnil.
    - assert (Hle : (off + k + n <= gp)%nat)
        by exact (ushs_toks_le len f gp (off + k + n)%nat toks Htoks).
      assert (Ek : ushp_skipws (gp - off) off f = k)
        by exact (ushs_skipws_trunc (len - off) (gp - off) off f
                    ltac:(lia) ltac:(lia)).
      assert (En : ushp_toklen (gp - (off + k)) (off + k) f = n)
        by exact (ushs_toklen_trunc (len - (off + k)) (gp - (off + k))
                    (off + k) f ltac:(lia) ltac:(lia)).
      assert (C := UshpTokCons gp f off toks).
      cbv zeta in C. rewrite Ek En in C.
      exact (C Hn (IH ltac:(lia))).
  Qed.


  (* ===================================================================== *)
  (* §2 THE SEAM AT THE REDIRECT SHAPE.                                     *)
  (*                                                                       *)
  (* [UkShMain.ush_cmd_of_ushp_gen] does the exec node; what is left is the *)
  (* REDIR node's own five fields and the FILE NAME as a string.  The cut   *)
  (* the redirect parse leaves is one byte longer than the symbol-free one  *)
  (* -- nulterminate's REDIR arm zeroes [efile] too -- and that byte is     *)
  (* exactly what terminates the file name.                                 *)
  (* ===================================================================== *)

  Local Notation ushs_nulcut := UkShRedirCut.ushs_nulcut.

  (* the file name, as the runner reads it *)
  Definition ushs_file (s0 : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp fe : nat) : uarg :=
    UArg (s0 + Z.of_nat (S (S gp))) (fe - S (S gp))%nat
         (fun j : nat => ushs_nulcut args len f fe (S (S gp) + j)%nat).

  (* no argument token's end lands inside another token's body -- the
     separation fact, on the TRUNCATED line, where it is stage 4's own *)
  Lemma ushs_arg_gap (len : nat) (f : nat -> bv 8) (gp fe : nat)
      (args : list (nat * nat)) :
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    forall (i : nat) (tk : nat * nat), args !! i = Some tk ->
    forall (q : nat) (t : nat * nat), args !! q = Some t ->
    forall x : nat, (fst tk <= x < snd tk)%nat -> x <> snd t.
  Proof using .
    intros Hred Htoks.
    assert (Hgl : (gp < len)%nat) by exact (ushs_redir_lt len f gp fe Hred).
    exact (UkShMain.ushp_tokens_gap gp f 0%nat args
             (ushs_one_nosym_below len f gp (ushs_redir_one len f gp fe Hred))
             (ushs_toks_below len gp f 0%nat args ltac:(lia) ltac:(lia) Htoks)
             ltac:(lia)).
  Qed.

  (* ...and every argument lies strictly below the '>' *)
  Lemma ushs_arg_below (len : nat) (f : nat -> bv 8) (gp fe : nat)
      (args : list (nat * nat)) :
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    forall (i : nat) (tk : nat * nat), args !! i = Some tk ->
      (fst tk < snd tk)%nat /\ (snd tk <= gp)%nat.
  Proof using .
    intros Hred Htoks i tk Hi.
    assert (Hgl : (gp < len)%nat) by exact (ushs_redir_lt len f gp fe Hred).
    destruct (ushp_tokens_in gp f 0%nat args
                (ushs_toks_below len gp f 0%nat args ltac:(lia) ltac:(lia)
                   Htoks) ltac:(lia) i tk Hi) as [ Hlo Hhi ].
    split; lia.
  Qed.

  Lemma ushs_nulcut_body (len : nat) (f : nat -> bv 8) (gp fe : nat)
      (args : list (nat * nat)) :
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    forall (i : nat) (tk : nat * nat), args !! i = Some tk ->
    forall j : nat, (j < snd tk - fst tk)%nat ->
      ushs_nulcut args len f fe (fst tk + j)%nat <> ubyte0.
  Proof using .
    intros Hred Htoks Hnn i tk Hi j Hj.
    destruct (ushs_arg_below len f gp fe args Hred Htoks i tk Hi)
      as [ Hlo Hhi ].
    pose proof Hred as HR.
    destruct HR as (Hone & Hgp0 & Hb1 & Hb2 & Hlo2 & Hhi2 & Hfw & Htail).
    rewrite /ushs_nulcut /UkShParseCmd.ushp_setb.
    rewrite (proj2 (Nat.eqb_neq (fst tk + j)%nat fe) ltac:(lia)).
    rewrite (UkShMain.ushp_nulfold_miss args (UkShParseCmd.ushp_ext len f)
               (fst tk + j)%nat
               ltac:(intros q t Hq;
                     exact (ushs_arg_gap len f gp fe args Hred Htoks
                              i tk Hi q t Hq (fst tk + j)%nat ltac:(lia)))).
    rewrite /UkShParseCmd.ushp_ext
      (bool_decide_eq_true_2 ((fst tk + j) < len)%nat ltac:(lia)).
    apply Hnn. lia.
  Qed.

  Lemma ushs_nulcut_filebody (len : nat) (f : nat -> bv 8) (gp fe : nat)
      (args : list (nat * nat)) :
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    forall j : nat, (j < fe - S (S gp))%nat ->
      ushs_nulcut args len f fe (S (S gp) + j)%nat <> ubyte0.
  Proof using .
    intros Hred Htoks Hnn j Hj.
    pose proof Hred as HR.
    destruct HR as (Hone & Hgp0 & Hb1 & Hb2 & Hlo2 & Hhi2 & Hfw & Htail).
    rewrite /ushs_nulcut /UkShParseCmd.ushp_setb.
    rewrite (proj2 (Nat.eqb_neq (S (S gp) + j)%nat fe) ltac:(lia)).
    rewrite (UkShMain.ushp_nulfold_miss args (UkShParseCmd.ushp_ext len f)
               (S (S gp) + j)%nat
               ltac:(intros q t Hq;
                     destruct (ushs_arg_below len f gp fe args Hred Htoks
                                 q t Hq) as [ _ Hhi ]; lia)).
    rewrite /UkShParseCmd.ushp_ext
      (bool_decide_eq_true_2 ((S (S gp) + j) < len)%nat ltac:(lia)).
    apply Hnn. lia.
  Qed.

  (* ...and WHICH bytes they are: the line's own, untouched by either cut *)
  Lemma ushs_nulcut_filebyte (len : nat) (f : nat -> bv 8) (gp fe : nat)
      (args : list (nat * nat)) :
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    forall j : nat, (j < fe - S (S gp))%nat ->
      ushs_nulcut args len f fe (S (S gp) + j)%nat = f (S (S gp) + j)%nat.
  Proof using .
    intros Hred Htoks j Hj.
    pose proof Hred as HR.
    destruct HR as (Hone & Hgp0 & Hb1 & Hb2 & Hlo2 & Hhi2 & Hfw & Htail).
    rewrite /ushs_nulcut /UkShParseCmd.ushp_setb.
    rewrite (proj2 (Nat.eqb_neq (S (S gp) + j)%nat fe) ltac:(lia)).
    rewrite (UkShMain.ushp_nulfold_miss args (UkShParseCmd.ushp_ext len f)
               (S (S gp) + j)%nat
               ltac:(intros q t Hq;
                     destruct (ushs_arg_below len f gp fe args Hred Htoks
                                 q t Hq) as [ _ Hhi ]; lia)).
    rewrite /UkShParseCmd.ushp_ext
      (bool_decide_eq_true_2 ((S (S gp) + j) < len)%nat ltac:(lia)).
    reflexivity.
  Qed.

  (* the REDIR row, INTRODUCED rather than unfolded: [c1] is a variable
     here, so [cbn] reduces the outer node and cannot touch the sub-tree *)
  Lemma ush_cmd_redir_intro (g : gname) (t q : Z) (c1 : ushcmd)
      (file : uarg) (mode fd : Z) :
    0 < t < 2 ^ 38 -> t mod 8 = 0 ->
    ush_w32 g t 2 -∗ ush_ptr g (t + 8) q -∗ ush_cmd g q c1 -∗
    ush_ptr g (t + 16) (ua_ptr file) -∗ ush_str g file -∗
    ush_w32 g (t + 32) mode -∗ ush_w32 g (t + 36) fd -∗
    ush_cmd g t (URedir c1 file mode fd).
  Proof using .
    intros Ht38 Ht8.
    iIntros "#Hty #Hp #Hc #Hfp #Hfs #Hm #Hf".
    cbn [ush_cmd ush_ty].
    iSplit; [ iPureIntro; exact Ht38 | ].
    iSplit; [ iPureIntro; exact Ht8 | ].
    iSplit; [ iExact "Hty" | ].
    iSplit; [ iExists q; iSplit; [ iExact "Hp" | iExact "Hc" ] | ].
    iSplit; [ iExact "Hfp" | ].
    iSplit; [ iExact "Hfs" | ].
    iSplit; [ iExact "Hm" | iExact "Hf" ].
  Qed.

  (* THE CONVERSION at the redirect shape. *)
  Lemma ush_cmd_of_ushs_redir (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (s0 t pe : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp fe : nat) :
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    Z.of_nat len < 2 ^ 31 ->
    0 < s0 -> s0 + Z.of_nat len < 2 ^ 38 ->
    urun N h m pc avail -∗
    UkShRedirCmd.ushp_redir_node N s0 t pe (S (S gp)) fe 1537 1 -∗
    UkShParse.ushp_tree N s0 pe (UshpExec args) -∗
    ubytes γd s0 (S len) (ushs_nulcut args len f fe) ==∗
    urun N h m pc avail ∗
    ush_cmd γd t
      (URedir (UExec (ush_args s0 (ushs_nulcut args len f fe) args))
              (ushs_file s0 len f args gp fe) 1537 1).
  Proof using .
    intros Hred Htoks Hnn Hlen31 Hs0 Hs0hi.
    pose proof Hred as HR.
    destruct HR as (Hone & Hgp0 & Hb1 & Hb2 & Hlo2 & Hhi2 & Hfw & Htail).
    assert (Hgl : (gp < len)%nat) by exact (ushs_redir_lt len f gp fe Hred).
    iIntros "Hrun Hn Hnode Hline".
    iMod (UkShMain.ubytes_persist γd s0 (S len) _ with "Hline") as "#Hline".
    (* the two nodes are the tree, closed *)
    iDestruct (UkShRedirCmd.ushp_redir_close N s0 t pe (S (S gp)) fe 1537 1
                 (UshpExec args) with "Hn Hnode") as "Htree".
    (* ...and the redirect line's cut is readable at both of them: the
       three landed facts about the arguments, the two about the file *)
    assert (Hcut : UkShSeam.ushp_cut_ok len (ushs_nulcut args len f fe)
                     (UshpRedir (UshpExec args) (S (S gp)) fe 1537 1)).
    { cbn [UkShSeam.ushp_cut_ok]. split_and!.
      - intros i tk Hi.
        destruct (ushs_arg_below len f gp fe args Hred Htoks i tk Hi) as [Hl Hh].
        split; lia.
      - intros i tk Hi. exact (UkShRedirCut.ushs_nulcut_arg args len f fe i tk Hi).
      - exact (ushs_nulcut_body len f gp fe args Hred Htoks Hnn).
      - lia.
      - lia.
      - exact (UkShRedirCut.ushs_nulcut_file args len f fe).
      - exact (ushs_nulcut_filebody len f gp fe args Hred Htoks Hnn). }
    iMod (UkShSeam.ush_cmd_of_ushp_tree N h m pc avail s0 len
            (ushs_nulcut args len f fe)
            (UshpRedir (UshpExec args) (S (S gp)) fe 1537 1) Hcut
            Hlen31 Hs0 Hs0hi t with "Hrun Htree Hline") as "[Hrun #Hcmd]".
    iModIntro. iFrame "Hrun". rewrite /ushs_file. iExact "Hcmd".
  Qed.


  (* ===================================================================== *)
  (* §3 THE CHILD, at the redirect shape.                                   *)
  (*                                                                       *)
  (*   0x9c0  c.mv a0,s1        the line                                    *)
  (*   0x9c2  jal  ra,parsecmd  -> the REDIR node over the exec node        *)
  (*   0x9c6  jal  ra,runcmd    -> close(1), open(file), and the sub-tree   *)
  (*                                                                       *)
  (* [UkShMain.wp_kshm_child]'s two parser premises become [ushs_redir] /   *)
  (* [ushs_toks] (and the count is bounded BELOW as well, because the       *)
  (* redirect parse needs at least one argument), and ONE premise is new:   *)
  (* the open, as a CALL ([UkShRedir.ush_open_call]) at the file name the   *)
  (* line itself names.                                                     *)
  (*                                                                       *)
  (* THE TWO CAPABILITIES ARE BOUNDED (lane SH-MALLOC-3): each is           *)
  (* [UkShParse.ushp_malloc_ty_le N 168], not [ushp_malloc_ty], because     *)
  (* two unbounded ones cannot both be discharged from one 64 KiB chunk     *)
  (* (iris/UkShMalloc.v §7) and 168 is the larger of the two sizes sh's     *)
  (* constructors ask for.  [wp_kshm_child_alloc_redir] below is this       *)
  (* lemma with both of them spent out of [UkShMalloc.ushm_fresh].          *)
  (*                                                                        *)
  (* THE RECEIPT IS NOT DROPPED.  [UkShRedir.wp_kshr_redir_arm] hands its   *)
  (* caller the run back at runcmd's own entry pc with the SUB-TREE, the    *)
  (* ledger the open left and the application's receipt [K ty]; this walk   *)
  (* relays all four to ITS caller rather than spending them on             *)
  (* [wp_kshr_runcmd_final], which would drop [K ty].  That continuation is *)
  (* what the application lane fills with its own EXEC walk.                *)
  (* ===================================================================== *)
  Lemma wp_kshm_child_redir_g (UM0 UM1 UM2 : iProp Σ)
      (Hm0 : UkShParse.ushp_malloc_ty_le N 168 UM0 UM1)
      (Hm1 : UkShParse.ushp_malloc_ty_le N 168 UM1 UM2)
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 cwdv : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp fe : nat)
      (ld : list fdstate) (st1 : fdstate) (n : nat)
      (H : iProp Σ) (K : fdtype -> iProp Σ) (Kf : iProp Σ)
      (Cr Cr' : iProp Σ) :
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    ld !! 1%nat = Some st1 ->
    st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : PipeNames.pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    (* THE EXIT IS PAID FROM THE LEND (lane SH-CHILD-2), not from a free
       payload: this walk is the PAID child's, whose [ukn_pay] is the block
       credential it was lent ([UkShFork.ushf_wq]).  Both places that can
       exit -- the parser's NULL store and the open's failure -- take the
       pair, and the lend comes back on the arm where neither fired. *)
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UM0 -∗
    UkShRedir.ush_open_call_g N cwdv (ushs_file s0 len f args gp fe) 1537
      (<[1%nat := FdClosed]> ld) H K Kf -∗
    □ (Cr -∗ ukn_pay N (-1)) -∗
    (* THE LEND SPLITS AT THE CALL: whole across the parse (it pays the
       parser's exits), and then what the open is handed and the rest *)
    (Cr -∗ H ∗ Cr') -∗
    Cr -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    ((∀ (h' : CpuId) (m' : regfile) (q : Z) (ty : fdtype),
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       ush_cmd γd q
         (UExec (ush_args s0 (ushs_nulcut args len f fe) args)) -∗
       UserFd.ustd γfd
         (<[1%nat := FdOpen false true ty]> (<[1%nat := FdClosed]> ld)) -∗
       UserCwd.ucwd γcwd cwdv -∗
       K ty -∗
       UM2 -∗
       Cr' -∗
       urun N h' m' (mword_of_int ShSyms.runcmd)
         (UkShDiag.ush_Dg + (70 + n)) -∗
       mWP (Loop : expr riscv_lang))
     (* ...OR THE OPEN FAILED, at the diagnostic cut ([UkShRedir.
        wp_kshr_redir_arm_g]'s additive pair, relayed) *)
     ∧
     (∀ (h' : CpuId) (m' : regfile),
        ⌜ UkShRun.ush_diag_at 0x10e m' ⌝ -∗
        UkShRun.ush_ptr γd (uint (m' !!! Regidx s1_idx) + 16)
          (ua_ptr (ushs_file s0 len f args gp fe)) -∗
        UkShRun.ush_str γd (ushs_file s0 len f args gp fe) -∗
        UserFd.ustd γfd (<[1%nat := FdClosed]> ld) -∗
        UserCwd.ucwd γcwd cwdv -∗
        Kf -∗
        Cr' -∗
        urun N h' m' (mword_of_int 0x10e) (UkShDiag.ush_Dg + (70 + n)) -∗
        mWP (Loop : expr riscv_lang))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay.
    intros Hs1 Hred Htoks Hpos Htlen Hs0 Hs64 Hs38 Hst1 Hne Hnp.
    iIntros "#Hcode #Hjt #Hpcode #Hpro Hline Hws Hsy Hstd Hcwd HM Hopen
             #Hpxw Hsplit Hcr Hrun Hk".
    iDestruct (ustr_nonul with "Hline") as %Hnn0.
    (* THE GENERAL CHILD at the redirect line's tree: the line parses to
       ONE REDIR over ONE EXEC (RefParseSym.ref_parsecmd_redir), its symbol
       bytes are in the catalogued scope, its cut is the reference's, and
       the two allocations chain *)
    iApply (UkShSeam.wp_ref_child_redir N UM0 UM2 h m dw dv s0 cwdv len f args
              (S (S gp)) fe (ushs_nulcut args len f fe) ld st1 n H K Kf Cr Cr'
              Hs1
              (ushs_gt_ok_scope len f (ushs_gt_ok_redir len f gp fe Hred))
              (ref_parsecmd_redir len f gp fe args Hnn0 Hred Htoks Htlen)
              ltac:(cbn [ref_nulcut]; rewrite UkShParser.ushp_zero_at_snoc;
                    rewrite <- UkShParser.ushp_nulfold_zero_at; reflexivity)
              ltac:(cbn [UkShRedirs.ushp_malloc_chain];
                    exists UM1; split; [ exact Hm0 | ];
                    exists UM2; split; [ exact Hm1 | reflexivity ])
              Hs0 Hs64 Hs38 Hst1 Hne Hnp
              with "Hcode Hjt Hpcode Hpro Hline Hws Hsy Hstd Hcwd HM Hopen
                    Hpxw Hsplit Hcr Hrun Hk").
  Qed.

  (* ...and the landed seam, VERBATIM, as its instance: the landed call,
     the whole lend kept, the failed open printed on the free write law. *)
  Lemma wp_kshm_child_redir (UM0 UM1 UM2 : iProp Σ)
      (Hm0 : UkShParse.ushp_malloc_ty_le N 168 UM0 UM1)
      (Hm1 : UkShParse.ushp_malloc_ty_le N 168 UM1 UM2)
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 cwdv : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp fe : nat)
      (ld : list fdstate) (st1 : fdstate) (n : nat)
      (K : fdtype -> iProp Σ) (Cr : iProp Σ) :
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    ld !! 1%nat = Some st1 ->
    st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : PipeNames.pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    (* THE EXIT IS PAID FROM THE LEND (lane SH-CHILD-2), not from a free
       payload: this walk is the PAID child's, whose [ukn_pay] is the block
       credential it was lent ([UkShFork.ushf_wq]).  Both places that can
       exit -- the parser's NULL store and the open's failure -- take the
       pair, and the lend comes back on the arm where neither fired. *)
    UkSh.sh_deps -∗
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UM0 -∗
    UkShRedir.ush_open_call N cwdv (s0 + Z.of_nat (S (S gp))) 1537
      (<[1%nat := FdClosed]> ld) K -∗
    □ (Cr -∗ ukn_pay N (-1)) -∗
    Cr -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (∀ (h' : CpuId) (m' : regfile) (q : Z) (ty : fdtype),
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       ush_cmd γd q
         (UExec (ush_args s0 (ushs_nulcut args len f fe) args)) -∗
       UserFd.ustd γfd
         (<[1%nat := FdOpen false true ty]> (<[1%nat := FdClosed]> ld)) -∗
       UserCwd.ucwd γcwd cwdv -∗
       K ty -∗
       UM2 -∗
       Cr -∗
       urun N h' m' (mword_of_int ShSyms.runcmd)
         (UkShDiag.ush_Dg + (70 + n)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay.
    intros Hs1 Hred Htoks Hpos Htlen Hs0 Hs64 Hs38 Hst1 Hne Hnp.
    iIntros "#Hdp #Hcode #Hjt #Hpcode #Hpro Hline Hws Hsy Hstd Hcwd HM Hopen
             #Hpxw Hcr Hrun Hcont".
    iDestruct (ush_jtab_ro with "Hjt") as "#Hro".
    iApply (wp_kshm_child_redir_g UM0 UM1 UM2 Hm0 Hm1 h m dw dv s0 cwdv len f
              args gp fe ld st1 n emp%I K emp%I Cr Cr
              Hs1 Hred Htoks Hpos Htlen Hs0 Hs64 Hs38 Hst1 Hne Hnp
              with "Hcode Hjt Hpcode Hpro Hline Hws Hsy Hstd Hcwd HM [Hopen]
                    Hpxw [] Hcr Hrun [Hcont]").
    - iApply (UkShRedir.ush_open_call_g_of N cwdv
                (ushs_file s0 len f args gp fe) 1537
                (<[1%nat := FdClosed]> ld) K with "Hopen").
    - iIntros "$".
    - iSplit.
      + iExact "Hcont".
      + iIntros (h' m') "%Hat #Hfp #Hfs _ _ _ Hcr Hrun".
        iDestruct ("Hpxw" with "Hcr") as "Hpay".
        iApply (UkShDiag.ush_diag_leaf_holds N h' m' 0x10e (70 + n) Hat
                  with "Hdp Hcode Hro [] Hpay Hrun").
        rewrite /UkShRun.ush_diag_res.
        destruct (decide ((0x10e : Z) = 0xda)) as [Hc | _];
          [ exfalso; discriminate Hc | ].
        destruct (decide ((0x10e : Z) = 0x10e)) as [_ | Hc];
          [ | exfalso; exact (Hc eq_refl) ].
        iExists (ushs_file s0 len f args gp fe).
        iSplitR; [ iExact "Hfp" | iExact "Hfs" ].
  Qed.

  (* ===================================================================== *)
  (* §4 THE CHILD AT THE REDIRECT SHAPE, WITH THE ALLOCATOR DISCHARGED.     *)
  (*                                                                       *)
  (* [wp_kshm_child_redir] is stated over TWO abstract capabilities because *)
  (* the redirect line's parse calls [malloc] twice -- [execcmd] and then,  *)
  (* from [parseredirs], [redircmd].  This is it at the CONCRETE one: the   *)
  (* heap /init handed sh's child, [UkShMalloc.ushm_fresh sz] -- [freep]    *)
  (* holding zero, the sixteen bytes of [base], the break where [exec]      *)
  (* left it.                                                              *)
  (*                                                                       *)
  (* WHAT MAKES THE CHAIN CLOSE IS THE BOUND, not a second [morecore].      *)
  (* The first call runs on an EMPTY free list, so it walks [sbrk] and      *)
  (* [free] and leaves the 64 KiB chunk [morecore] inserted minus its own   *)
  (* twelve units: [ushm_one_ge (sz + 65536) 4084].  The second runs on     *)
  (* THAT list, which is non-empty, so it is the short walk with no back    *)
  (* edge ([UkShMalloc.wp_kshm_malloc_one]) and it leaves 4072.  Neither    *)
  (* step is expressible at the unbounded contract, where a call at 65504   *)
  (* takes 4095 of the 4096 units and nothing is left for the next one --   *)
  (* see iris/UkShMalloc.v §7 and iris/UkShParse.v at                       *)
  (* [ushp_malloc_ty_le].                                                   *)
  (*                                                                       *)
  (* THE LEFTOVER IS HANDED ON.  Where [wp_kshm_child_redir]'s continuation *)
  (* has [UM2] this one has [ushm_one_ge (sz + 65536) 4072]: the free list  *)
  (* the child's own [runcmd] arm inherits, so a later lane that needs sh   *)
  (* to allocate again inside the redirect has the capability to hand.      *)
  (* The break is at [sz + 65536] because the allocator asked the kernel    *)
  (* for sixteen pages on the way through, exactly as in                    *)
  (* [UkShMain.wp_kshm_child_alloc].                                        *)
  (* ===================================================================== *)
  Lemma wp_kshm_child_alloc_redir_g
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 cwdv : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp fe : nat)
      (sz : Z) (ld : list fdstate) (st1 : fdstate) (n : nat)
      (H : iProp Σ) (K : fdtype -> iProp Σ) (Kf : iProp Σ)
      (Cr Cr' : iProp Σ) :
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    ld !! 1%nat = Some st1 ->
    st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : PipeNames.pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    (* the break is above [base] (0x2088, the last sixteen bytes of the
       image) and page-aligned, which [exec] leaves it -- the same three
       premises [UkShMain.wp_kshm_child_alloc] carries *)
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UkShMalloc.ushm_fresh N sz -∗
    UkShRedir.ush_open_call_g N cwdv (ushs_file s0 len f args gp fe) 1537
      (<[1%nat := FdClosed]> ld) H K Kf -∗
    □ (Cr -∗ ukn_pay N (-1)) -∗
    (Cr -∗ H ∗ Cr') -∗
    Cr -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    ((∀ (h' : CpuId) (m' : regfile) (q : Z) (ty : fdtype),
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       ush_cmd γd q
         (UExec (ush_args s0 (ushs_nulcut args len f fe) args)) -∗
       UserFd.ustd γfd
         (<[1%nat := FdOpen false true ty]> (<[1%nat := FdClosed]> ld)) -∗
       UserCwd.ucwd γcwd cwdv -∗
       K ty -∗
       UkShMalloc.ushm_one_ge N (sz + 65536) 4072 -∗
       Cr' -∗
       urun N h' m' (mword_of_int ShSyms.runcmd)
         (UkShDiag.ush_Dg + (70 + n)) -∗
       mWP (Loop : expr riscv_lang))
     ∧
     (∀ (h' : CpuId) (m' : regfile),
        ⌜ UkShRun.ush_diag_at 0x10e m' ⌝ -∗
        UkShRun.ush_ptr γd (uint (m' !!! Regidx s1_idx) + 16)
          (ua_ptr (ushs_file s0 len f args gp fe)) -∗
        UkShRun.ush_str γd (ushs_file s0 len f args gp fe) -∗
        UserFd.ustd γfd (<[1%nat := FdClosed]> ld) -∗
        UserCwd.ucwd γcwd cwdv -∗
        Kf -∗
        Cr' -∗
        urun N h' m' (mword_of_int 0x10e) (UkShDiag.ush_Dg + (70 + n)) -∗
        mWP (Loop : expr riscv_lang))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free.
    intros Hs1 Hred Htoks Hpos Htlen Hs0 Hs64 Hs38 Hst1 Hne Hnp
           Hszlo Hszal Hszok.
    iIntros "#Hcode #Hjt #Hpcode #Hpro Hline Hws Hsy Hstd Hcwd HM Hopen
             #Hpxw Hsplit Hcr Hrun Hk".
    iApply (wp_kshm_child_redir_g
              (UkShMalloc.ushm_fresh N sz)
              (UkShMalloc.ushm_one_ge N (sz + 65536) 4084)
              (UkShMalloc.ushm_one_ge N (sz + 65536) 4072)
              (UkShMalloc.ushm_malloc_le_exec N Hpsok_free sz
                 Hszlo Hszal Hszok)
              (UkShMalloc.ushm_malloc_le_next N (sz + 65536))
              h m dw dv s0 cwdv len f args gp fe ld st1 n H K Kf Cr Cr'
              Hs1 Hred Htoks Hpos Htlen Hs0 Hs64 Hs38 Hst1 Hne Hnp
              with "Hcode Hjt Hpcode Hpro Hline Hws Hsy Hstd Hcwd HM
                    Hopen Hpxw Hsplit Hcr Hrun Hk").
  Qed.

  (* the landed statement, unchanged *)
  Lemma wp_kshm_child_alloc_redir
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 cwdv : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp fe : nat)
      (sz : Z) (ld : list fdstate) (st1 : fdstate) (n : nat)
      (K : fdtype -> iProp Σ) (Cr : iProp Σ) :
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    ld !! 1%nat = Some st1 ->
    st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : PipeNames.pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    (* the break is above [base] (0x2088, the last sixteen bytes of the
       image) and page-aligned, which [exec] leaves it -- the same three
       premises [UkShMain.wp_kshm_child_alloc] carries *)
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    UkSh.sh_deps -∗
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UkShMalloc.ushm_fresh N sz -∗
    UkShRedir.ush_open_call N cwdv (s0 + Z.of_nat (S (S gp))) 1537
      (<[1%nat := FdClosed]> ld) K -∗
    □ (Cr -∗ ukn_pay N (-1)) -∗
    Cr -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (∀ (h' : CpuId) (m' : regfile) (q : Z) (ty : fdtype),
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       ush_cmd γd q
         (UExec (ush_args s0 (ushs_nulcut args len f fe) args)) -∗
       UserFd.ustd γfd
         (<[1%nat := FdOpen false true ty]> (<[1%nat := FdClosed]> ld)) -∗
       UserCwd.ucwd γcwd cwdv -∗
       K ty -∗
       UkShMalloc.ushm_one_ge N (sz + 65536) 4072 -∗
       Cr -∗
       urun N h' m' (mword_of_int ShSyms.runcmd)
         (UkShDiag.ush_Dg + (70 + n)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free.
    intros Hs1 Hred Htoks Hpos Htlen Hs0 Hs64 Hs38 Hst1 Hne Hnp
           Hszlo Hszal Hszok.
    iIntros "#Hdp #Hcode #Hjt #Hpcode #Hpro Hline Hws Hsy Hstd Hcwd HM Hopen
             #Hpxw Hcr Hrun Hcont".
    iApply (wp_kshm_child_redir
              (UkShMalloc.ushm_fresh N sz)
              (UkShMalloc.ushm_one_ge N (sz + 65536) 4084)
              (UkShMalloc.ushm_one_ge N (sz + 65536) 4072)
              (UkShMalloc.ushm_malloc_le_exec N Hpsok_free sz
                 Hszlo Hszal Hszok)
              (UkShMalloc.ushm_malloc_le_next N (sz + 65536))
              h m dw dv s0 cwdv len f args gp fe ld st1 n K Cr
              Hs1 Hred Htoks Hpos Htlen Hs0 Hs64 Hs38 Hst1 Hne Hnp
              with "Hdp Hcode Hjt Hpcode Hpro Hline Hws Hsy Hstd Hcwd HM
                    Hopen Hpxw Hcr Hrun Hcont").
  Qed.

End UkShRedirSeam.
