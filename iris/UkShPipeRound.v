(* ===================================================================== *)
(* UkShPipeRound.v -- THE CHILD WALK AT THE PIPE SHAPE, lane              *)
(* SH-PIPE-ROUND item A (design/app-pipe.md SS5.1).                        *)
(*                                                                        *)
(* [UkShRedirSeam.wp_kshm_child_redir] is the mould, one line shape over:  *)
(* sh's forked child enters at 0x9c0 with the line in s1, calls            *)
(* [parsecmd] and then [runcmd].  What differs is which parser theorem     *)
(* and which [runcmd] arm run:                                            *)
(*                                                                        *)
(*   0x9c0  c.mv a0,s1        the line                                     *)
(*   0x9c2  jal  ra,parsecmd  -> [UkShParser.wp_ref_parser] at the        *)
(*                              reference's PIPE of two EXECs              *)
(*   0x9c6  jal  ra,runcmd    -> [UkShPipe.wp_kshr_pipe_arm]:              *)
(*                              pipe(2), two fork1s, six closes, two waits *)
(*                                                                        *)
(* and between them the seam [UkShPipeSeam.ush_cmd_of_ushp_pipe], whose    *)
(* two [ushq_cut_ok] premises are SS1 of this file.                         *)
(*                                                                        *)
(* SINCE user-once A3a the walk is a corollary: [UkShSeam.wp_ref_child_pipe] *)
(* is the child at ANY pipe line the reference parses, and [wp_kshm_child_ *)
(* pipe] below is it at this file's line shape ([RefParseBridge.            *)
(* ref_parsecmd_pipe] turns [ushq_pipe]/[ushs_toks] into the reference's   *)
(* equation, [UkShParser.ushp_nulfold_zero_at] turns [ushq_cut] into the   *)
(* reference's cut).  SS1's [ushq_cut_ok] facts are what the landed seam    *)
(* [UkShPipeSeam.ush_cmd_of_ushp_pipe] still states, for its own           *)
(* consumers.                                                              *)
(*                                                                        *)
(* WHAT THE ARM FORCES ON THE WALK, and it is a finding for the round:     *)
(* [wp_kshr_pipe_arm] takes the exit payload FREE ([(⊢ ukn_pay N (-1))],   *)
(* a Prop), where [UkShRedir.wp_kshr_redir_arm_at] takes the pair          *)
(* [□ (Cr -∗ ukn_pay N (-1))] / [Cr].  A resource the caller brings can    *)
(* still travel -- through the arm's own SPLIT wand, into exactly one of   *)
(* [RcL]/[RcR]/[Rk] -- and that is what [Cr] does here; but the free       *)
(* payload itself is a real premise of the arm and this walk inherits it.  *)
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
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf.
Require Import FdSlots UserFd.
Require Import PipeNames.
Require Import UserCwd.
Require Import UserChildren.
Require Import UCodeShK.
Require Import UCodeShP.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShParseCmd.
Require Import UkShMain.
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShRedirSeam.   (* [ushs_toks_below] -- the truncation *)
Require Import UkShPipe.        (* the runcmd arm *)
Require Import LineWords.
Require Import PipeDisc.
Require Import UkShPipeLex.
Require Import UkShPipeSeam.
Require Import RefParse.
Require Import RefParseBridge.  (* [ref_parsecmd_pipe]: the pipe line at the reference *)
Require Import UkShRedirs.      (* [ushp_malloc_chain] *)
Require Import UkShParser.      (* [ushp_zero_at]: the reference's cut *)
Require Import UkShSeam.        (* THE CHILD, once *)
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UexecSG.
Require Import UexecRet.
Local Open Scope Z_scope.
Import Defs.

Section UkShPipeRound.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  Local Notation γch := (ukn_ch N).

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).

  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).

  (* the three allocator links a pipe line's parse spends (design SS5.1 as
     landed: two [execcmd]s and one [pipecmd]); UM1 -> UM2 was a section
     hypothesis of the pipe parser shell and stays one here so the landed
     statements do not move -- the three together are
     [UkShRedirs.ushp_malloc_chain 3 UM0 UM3] *)
  Context (UM0 UM1 UM2 UM3 : iProp Σ).
  Hypothesis ushq_malloc_ok12 : ushp_malloc_ty UM1 UM2.

  (* ===================================================================== *)
  (* §1 THE CUT, AND THE SEAM'S TWO PREMISES.                               *)
  (*                                                                        *)
  (* [nulterminate]'s PIPE row zeroes the end index of every argument       *)
  (* token of the LEFT command and then the end index of the right          *)
  (* command's single word, on ONE buffer -- which is exactly the redirect  *)
  (* cut [UkShRedirCut.ushs_nulcut args len f ge] (the outer fold over a    *)
  (* one-element list IS [ushp_setb]).  So the two shapes share one         *)
  (* definition and only the INDEX BOUNDS differ.                           *)
  (* ===================================================================== *)

  Definition ushq_cut (args : list (nat * nat)) (len : nat)
      (f : nat -> bv 8) (ge : nat) : nat -> bv 8 :=
    UkShParseCmd.ushp_nulfold [(0%nat, ge)]
      (UkShParseCmd.ushp_nulfold args (UkShParseCmd.ushp_ext len f)).

  (* what [wp_kshp_parsecmd_bar] hands back IS this cut *)
  Lemma ushq_cut_eq (args : list (nat * nat)) (len : nat) (f : nat -> bv 8)
      (gp ge : nat) :
    UkShParseCmd.ushp_nulfold [(S (S gp), ge)]
      (UkShParseCmd.ushp_nulfold args (UkShParseCmd.ushp_ext len f))
    = ushq_cut args len f ge.
  Proof using . reflexivity. Qed.

  Lemma ushq_cut_off (args : list (nat * nat)) (len : nat) (f : nat -> bv 8)
      (ge j : nat) :
    j <> ge ->
    ushq_cut args len f ge j
    = UkShParseCmd.ushp_nulfold args (UkShParseCmd.ushp_ext len f) j.
  Proof using .
    intro Hj. rewrite /ushq_cut. cbn [UkShParseCmd.ushp_nulfold snd].
    rewrite /UkShParseCmd.ushp_setb.
    rewrite (proj2 (Nat.eqb_neq j ge) Hj). reflexivity.
  Qed.

  (* the LEFT command's tokens, read on the line TRUNCATED at the '|' --
     [UkShRedirSeam]'s route, at the pipe shape's own symbol fact *)
  Lemma ushq_args_below (len : nat) (f : nat -> bv 8) (gp ge : nat)
      (args : list (nat * nat)) :
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    forall (i : nat) (tk : nat * nat), args !! i = Some tk ->
      (fst tk < snd tk)%nat /\ (snd tk <= gp)%nat.
  Proof using .
    intros Hpq Htoks i tk Hi.
    assert (Hgl : (gp < len)%nat) by exact (ushq_pipe_lt len f gp ge Hpq).
    destruct (ushp_tokens_in gp f 0%nat args
                (UkShRedirSeam.ushs_toks_below len gp f 0%nat args
                   ltac:(lia) ltac:(lia) Htoks) ltac:(lia) i tk Hi)
      as [ Hlo Hhi ].
    split; lia.
  Qed.

  Lemma ushq_args_gap (len : nat) (f : nat -> bv 8) (gp ge : nat)
      (args : list (nat * nat)) :
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    forall (i : nat) (tk : nat * nat), args !! i = Some tk ->
    forall (q : nat) (t : nat * nat), args !! q = Some t ->
    forall x : nat, (fst tk <= x < snd tk)%nat -> x <> snd t.
  Proof using .
    intros Hpq Htoks.
    assert (Hgl : (gp < len)%nat) by exact (ushq_pipe_lt len f gp ge Hpq).
    exact (UkShMain.ushp_tokens_gap gp f 0%nat args
             (ushq_pipe_nosym_below len f gp ge Hpq)
             (UkShRedirSeam.ushs_toks_below len gp f 0%nat args
                ltac:(lia) ltac:(lia) Htoks)
             ltac:(lia)).
  Qed.

  (* SEAM PREMISE 1: the LEFT command's token list, at the cut *)
  Lemma ushq_cut_ok_left (len : nat) (f : nat -> bv 8) (gp ge : nat)
      (args : list (nat * nat)) :
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    UkShPipeSeam.ushq_cut_ok len (ushq_cut args len f ge) args.
  Proof using .
    intros Hpq Htoks Hnn.
    pose proof Hpq as HQ.
    destruct HQ as (Hone & Hgp0 & Hb1 & Hb2 & Hlo & Hhi & Hfw & Htail).
    assert (Hgl : (gp < len)%nat) by exact (ushq_pipe_lt len f gp ge Hpq).
    split_and!.
    - intros i tk Hi.
      destruct (ushq_args_below len f gp ge args Hpq Htoks i tk Hi) as [H1 H2].
      split; lia.
    - intros i tk Hi.
      destruct (ushq_args_below len f gp ge args Hpq Htoks i tk Hi) as [H1 H2].
      rewrite (ushq_cut_off args len f ge (snd tk) ltac:(lia)).
      exact (UkShParseCmd.ushp_nulfold_hit args
               (UkShParseCmd.ushp_ext len f) i tk Hi).
    - intros i tk Hi j Hj.
      destruct (ushq_args_below len f gp ge args Hpq Htoks i tk Hi) as [H1 H2].
      rewrite (ushq_cut_off args len f ge (fst tk + j)%nat ltac:(lia)).
      rewrite (UkShMain.ushp_nulfold_miss args (UkShParseCmd.ushp_ext len f)
                 (fst tk + j)%nat
                 ltac:(intros q t Hq;
                       exact (ushq_args_gap len f gp ge args Hpq Htoks
                                i tk Hi q t Hq (fst tk + j)%nat ltac:(lia)))).
      rewrite /UkShParseCmd.ushp_ext
        (bool_decide_eq_true_2 ((fst tk + j) < len)%nat ltac:(lia)).
      apply Hnn. lia.
  Qed.

  (* SEAM PREMISE 2: the RIGHT command's ONE word, at the same cut *)
  Lemma ushq_cut_ok_right (len : nat) (f : nat -> bv 8) (gp ge : nat)
      (args : list (nat * nat)) :
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    UkShPipeSeam.ushq_cut_ok len (ushq_cut args len f ge)
      [(S (S gp), ge)].
  Proof using .
    intros Hpq Htoks Hnn.
    pose proof Hpq as HQ.
    destruct HQ as (Hone & Hgp0 & Hb1 & Hb2 & Hlo & Hhi & Hfw & Htail).
    split_and!.
    - intros i tk Hi.
      destruct i as [| i ]; cbn [lookup list_lookup] in Hi;
        [ injection Hi as <-; cbn [fst snd]; lia | ].
      rewrite lookup_nil in Hi. discriminate.
    - intros i tk Hi.
      destruct i as [| i ]; cbn [lookup list_lookup] in Hi;
        [ injection Hi as <- | rewrite lookup_nil in Hi; discriminate ].
      cbn [snd]. rewrite /ushq_cut.
      cbn [UkShParseCmd.ushp_nulfold snd].
      rewrite /UkShParseCmd.ushp_setb Nat.eqb_refl. reflexivity.
    - intros i tk Hi j Hj.
      destruct i as [| i ]; cbn [lookup list_lookup] in Hi;
        [ injection Hi as <- | rewrite lookup_nil in Hi; discriminate ].
      cbn [fst snd] in Hj |- *.
      rewrite (ushq_cut_off args len f ge (S (S gp) + j)%nat ltac:(lia)).
      rewrite (UkShMain.ushp_nulfold_miss args (UkShParseCmd.ushp_ext len f)
                 (S (S gp) + j)%nat
                 ltac:(intros q t Hq;
                       destruct (ushq_args_below len f gp ge args Hpq Htoks
                                   q t Hq) as [ _ Hhi' ]; lia)).
      rewrite /UkShParseCmd.ushp_ext
        (bool_decide_eq_true_2 ((S (S gp) + j) < len)%nat ltac:(lia)).
      apply Hnn. lia.
  Qed.

  (* ===================================================================== *)
  (* §2 THE CHILD, at the pipe shape.                                       *)
  (* ===================================================================== *)
  Lemma wp_kshm_child_pipe
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 szv cwdv : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp ge : nat)
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (n : nat)
      (R RcL RcR Rk : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ)
      (Cr : iProp Σ) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (forall x y : Z, Qc x = Qc y) ->
    (⊢ ukn_pay N (-1)) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gn)) ->
    (forall (rb wb : bool) (gn : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    UkSh.sh_deps -∗
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    usz γs szv -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UserChildren.uch γch Sc -∗
    UM0 -∗
    Cr -∗
    □ (app_taint -∗ Qc (-1)) -∗
    (* the arm's own split, with the walk's leftovers ([UM3], [Cr]) free to
       ride into whichever of the three it likes *)
    (∀ γp : pipe_names, UM3 -∗ Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ Rk γp)) -∗
    UkShPipe.ush_pipe_call N ld R -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (* ---- THE LEFT CHILD: fd 1 is the pipe's WRITE end ---- *)
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0 (ushq_cut args len f ge) args)) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[1%nat := FdOpen false true (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcL γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* ---- THE RIGHT CHILD: fd 0 is the pipe's READ end ---- *)
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0 (ushq_cut args len f ge) [(S (S gp), ge)])) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[0%nat := FdOpen true false (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcR γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* ---- THE PARENT, at 0xea ---- *)
    (∀ (h' : CpuId) (m' : regfile) (γp : pipe_names)
       (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname),
       UkShPipe.ush_fork_ans Sc S1 (RcL γp) Qc r1 -∗
       UkShPipe.ush_fork_ans S1 S2 (RcR γp) Qc r2 -∗
       uwait_ans rw1 S2 S3 -∗
       uwait_ans rw2 S3 S4 -∗
       UserChildren.uch γch S4 -∗
       ush_jtab γt -∗
       usz γs szv -∗
       UserFd.ustd γfd ld -∗
       UserCwd.ucwd γcwd cwdv -∗
       Rk γp -∗
       urun N h' m' (mword_of_int 0xea)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free ushq_malloc_ok12.
    intros Hm01 Hm23 Hs1 Hpq Htoks Hpos Htlen Hs0 Hs64 Hs38
           HQc Hpx Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1.
    iIntros "#Hdp #Hcode #Hjt #Hpcode #Hpro Hline Hws Hsy Hsz Hstd Hcwd Hch
             HM Hcr #Hkw Hsplit Hpipe Hrun HcL HcR Hpar".
    iDestruct (ustr_nonul with "Hline") as %Hnn0.
    (* THE GENERAL CHILD at the pipe line's tree: the line parses to ONE
       PIPE of two EXECs (RefParseBridge.ref_parsecmd_pipe), its symbol
       bytes are in the catalogued scope, its cut is the reference's, and
       the three allocations chain *)
    iApply (UkShSeam.wp_ref_child_pipe N Hpsok_free UM0 UM3 h m dw dv s0 szv cwdv len f
              args [(S (S gp), ge)] (ushq_cut args len f ge) ld st0 st1 Sc n
              R RcL RcR Rk Qc Cr
              Hs1
              (UkShPipeLex.ushq_sym_ok_scope len f (UkShPipeLex.ushq_sym_ok_pipe len f gp ge Hpq))
              (ref_parsecmd_pipe len f gp ge args Hnn0 Hpq Htoks Htlen)
              ltac:(cbn [ref_nulcut]; rewrite UkShParser.ushp_zero_at_app;
                    rewrite <- (UkShParser.ushp_nulfold_zero_at args);
                    rewrite <- (UkShParser.ushp_nulfold_zero_at [(S (S gp), ge)]);
                    reflexivity)
              ltac:(cbn [UkShRedirs.ushp_malloc_chain];
                    exists UM1; split; [ exact Hm01 | ];
                    exists UM2; split; [ exact ushq_malloc_ok12 | ];
                    exists UM3; split; [ exact Hm23 | reflexivity ])
              Hs0 Hs64 Hs38 HQc Hpx Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1
              with "Hdp Hcode Hjt Hpcode Hpro Hline Hws Hsy Hsz Hstd Hcwd Hch
                    HM Hcr Hkw Hsplit Hpipe Hrun HcL HcR Hpar").
  Qed.


  (* ===================================================================== *)
  (* §3 THE LINE, AND WHAT THE FOURTH ARM OF THE DISJUNCT WOULD CARRY.      *)
  (*                                                                        *)
  (* [UkSh.ush_line_at] reads exactly three projections of its line --      *)
  (* [FileDisc.uline_ok], [FileDisc.line_bytes] and (through                *)
  (* [ush_rest_line_at]) [FileDisc.uline_ws] -- so the pipe line's arm is   *)
  (* that predicate at [PipeDisc]'s own [LPipe].  It is written out here    *)
  (* because [FileDisc.uline] HAS NO SUCH CONSTRUCTOR and adding one is     *)
  (* not this lane's to make (see the lane report, STOP A): what is landed  *)
  (* is the load-bearing half -- the buffer holds the pipe line's bytes,   *)
  (* hence the lexer's premise -- which is what the fourth arm delivers.    *)
  (* ===================================================================== *)

  Definition ushq_line_at (ws : list (list (bv 8))) (f : nat -> bv 8)
      (k len : nat) : Prop :=
    PipeDisc.pline_ok (PipeDisc.LPipe ws)
    /\ len = length (PipeDisc.line_bytes (PipeDisc.LPipe ws))
    /\ (forall j : nat, (j < len)%nat ->
          f (k + j)%nat = PipeDisc.line_bytes (PipeDisc.LPipe ws) !!! j).

  Local Lemma ushq_bytes_lo (ws : list (list (bv 8))) (j : nat) :
    (j < length (wl_body ws))%nat ->
    PipeDisc.line_bytes (PipeDisc.LPipe ws) !!! j = wl_body ws !!! j.
  Proof using .
    intro Hj.
    rewrite /PipeDisc.line_bytes /PipeDisc.line_body -app_assoc.
    rewrite lookup_total_app_l; [ reflexivity | exact Hj ].
  Qed.

  Local Lemma ushq_bytes_hi (ws : list (list (bv 8))) (j : nat) :
    (length (wl_body ws) <= j)%nat ->
    PipeDisc.line_bytes (PipeDisc.LPipe ws) !!! j
    = (PipeDisc.suf_pipecat ++ [wl_nl]) !!! (j - length (wl_body ws))%nat.
  Proof using .
    intro Hj.
    rewrite /PipeDisc.line_bytes /PipeDisc.line_body -app_assoc.
    rewrite lookup_total_app_r; [ reflexivity | exact Hj ].
  Qed.

  (* THE BRIDGE: the loop's line fact at the pipe shape IS the lexer's
     premise, at the canonical right-hand command [cat]. *)
  Lemma ushq_line_is_of_at (ws : list (list (bv 8))) (f : nat -> bv 8)
      (k len : nat) :
    ushq_line_at ws f k len -> ushq_line_is ws UkShPipeLex.ushq_cat f k len.
  Proof using .
    intros (Hok & Hlen & Hb).
    assert (Hl7 : len = (length (wl_body ws) + 7)%nat).
    { rewrite Hlen /PipeDisc.line_bytes /PipeDisc.line_body !length_app
        PipeDisc.suf_pipecat_len. cbn [length]. lia. }
    rewrite /ushq_line_is. cbv zeta. split_and!.
    - exact (proj1 Hok).
    - exact UkShPipeLex.ushq_cat_word.
    - rewrite UkShPipeLex.ushq_cat_len. lia.
    - intros j Hj. rewrite (Hb j ltac:(lia)).
      exact (ushq_bytes_lo ws j Hj).
    - rewrite (Hb (length (wl_body ws)) ltac:(lia))
        (ushq_bytes_hi ws (length (wl_body ws)) ltac:(lia)).
      rewrite Nat.sub_diag. apply bv_eq. by vm_compute.
    - replace (k + length (wl_body ws) + 1)%nat
        with (k + (length (wl_body ws) + 1))%nat by lia.
      rewrite (Hb (length (wl_body ws) + 1)%nat ltac:(lia))
        (ushq_bytes_hi ws (length (wl_body ws) + 1)%nat ltac:(lia)).
      replace (length (wl_body ws) + 1 - length (wl_body ws))%nat
        with 1%nat by lia.
      apply bv_eq. by vm_compute.
    - replace (k + length (wl_body ws) + 2)%nat
        with (k + (length (wl_body ws) + 2))%nat by lia.
      rewrite (Hb (length (wl_body ws) + 2)%nat ltac:(lia))
        (ushq_bytes_hi ws (length (wl_body ws) + 2)%nat ltac:(lia)).
      replace (length (wl_body ws) + 2 - length (wl_body ws))%nat
        with 2%nat by lia.
      apply bv_eq. by vm_compute.
    - intros j Hj. rewrite UkShPipeLex.ushq_cat_len in Hj.
      replace (k + length (wl_body ws) + 3 + j)%nat
        with (k + (length (wl_body ws) + 3 + j))%nat by lia.
      rewrite (Hb (length (wl_body ws) + 3 + j)%nat ltac:(lia))
        (ushq_bytes_hi ws (length (wl_body ws) + 3 + j)%nat ltac:(lia)).
      replace (length (wl_body ws) + 3 + j - length (wl_body ws))%nat
        with (3 + j)%nat by lia.
      destruct j as [| [| [| j ]]];
        [ apply bv_eq; by vm_compute | apply bv_eq; by vm_compute
        | apply bv_eq; by vm_compute | lia ].
    - rewrite UkShPipeLex.ushq_cat_len.
      replace (k + length (wl_body ws) + 3 + 3)%nat
        with (k + (length (wl_body ws) + 6))%nat by lia.
      rewrite (Hb (length (wl_body ws) + 6)%nat ltac:(lia))
        (ushq_bytes_hi ws (length (wl_body ws) + 6)%nat ltac:(lia)).
      replace (length (wl_body ws) + 6 - length (wl_body ws))%nat
        with 6%nat by lia.
      apply bv_eq. by vm_compute.
  Qed.

  (* ...AND THE CHILD WALK AT THE LINE.  This is the statement the round
     instantiates: the buffer at [s0] holds `echo w1 ... wn | cat\n', and
     the two children come out at [runcmd]'s entry with the pipe's two
     ends at fd 1 and fd 0. *)
  Corollary wp_kshm_child_pipe_line
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 szv cwdv : Z) (len : nat) (f : nat -> bv 8)
      (ws : list (list (bv 8)))
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (n : nat)
      (R RcL RcR Rk : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ)
      (Cr : iProp Σ) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushq_line_at ws f 0%nat len ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (forall x y : Z, Qc x = Qc y) ->
    (⊢ ukn_pay N (-1)) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gn)) ->
    (forall (rb wb : bool) (gn : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    UkSh.sh_deps -∗
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    usz γs szv -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UserChildren.uch γch Sc -∗
    UM0 -∗
    Cr -∗
    □ (app_taint -∗ Qc (-1)) -∗
    (* the arm's own split, with the walk's leftovers ([UM3], [Cr]) free to
       ride into whichever of the three it likes *)
    (∀ γp : pipe_names, UM3 -∗ Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ Rk γp)) -∗
    UkShPipe.ush_pipe_call N ld R -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (* ---- THE LEFT CHILD: fd 1 is the pipe's WRITE end ---- *)
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0 (ushq_cut (wl_toks ws) len f (length (wl_body ws) + 3 + 3)%nat) (wl_toks ws))) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[1%nat := FdOpen false true (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcL γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* ---- THE RIGHT CHILD: fd 0 is the pipe's READ end ---- *)
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0 (ushq_cut (wl_toks ws) len f (length (wl_body ws) + 3 + 3)%nat) [((length (wl_body ws) + 3)%nat,
            (length (wl_body ws) + 3 + 3)%nat)])) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[0%nat := FdOpen true false (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcR γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* ---- THE PARENT, at 0xea ---- *)
    (∀ (h' : CpuId) (m' : regfile) (γp : pipe_names)
       (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname),
       UkShPipe.ush_fork_ans Sc S1 (RcL γp) Qc r1 -∗
       UkShPipe.ush_fork_ans S1 S2 (RcR γp) Qc r2 -∗
       uwait_ans rw1 S2 S3 -∗
       uwait_ans rw2 S3 S4 -∗
       UserChildren.uch γch S4 -∗
       ush_jtab γt -∗
       usz γs szv -∗
       UserFd.ustd γfd ld -∗
       UserCwd.ucwd γcwd cwdv -∗
       Rk γp -∗
       urun N h' m' (mword_of_int 0xea)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free ushq_malloc_ok12.
    intros Hm01 Hm23 Hs1 Hline Hs0 Hs64 Hs38 HQc Hpx Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1.
    pose proof (ushq_line_is_of_at ws f 0%nat len Hline) as Hli.
    destruct (UkShPipeLex.ush_line_toks_holds_pipe ws UkShPipeLex.ushq_cat f
                0%nat len Hli) as (Hq & Ht & Hpos & Htlen & _).
    assert (Ef : (fun j : nat => f (0 + j)%nat) = f) by reflexivity.
    rewrite Ef in Hq, Ht.
    rewrite UkShPipeLex.ushq_cat_len in Hq.
    (* the walk's right-hand token is [(S (S gp), ge)] at [gp := p0 + 1];
       [S (S (p0 + 1))] and [p0 + 3] are equal and not convertible *)
    assert (Ege : (length (wl_body ws) + 3)%nat
                  = S (S (length (wl_body ws) + 1))) by lia.
    rewrite Ege in Hq |- *.
    exact (wp_kshm_child_pipe h m dw dv s0 szv cwdv len f (wl_toks ws)
             (length (wl_body ws) + 1)%nat
             (S (S (length (wl_body ws) + 1)) + 3)%nat
             ld st0 st1 Sc n R RcL RcR Rk Qc Cr
             Hm01 Hm23 Hs1 Hq Ht Hpos Htlen Hs0 Hs64 Hs38
             HQc Hpx Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1).
  Qed.

End UkShPipeRound.

(* AUDITED, 2026-09-18 (the two [Print Assumptions] are NOT left in the
   build: they re-cook the whole parser cone on every build, which is why
   [FileAssumptions.v] and its siblings are out of [iris/_CoqProject]).
   [wp_kshm_child_pipe] and [wp_kshm_child_pipe_line] print EXACTLY the
   three the landed redirect parser theorem prints and nothing else:
   [xv6iris_extras.resv_matches], [xv6iris_extras.resv_is_valid] and
   [FunctionalExtensionality.functional_extensionality_dep]. *)
