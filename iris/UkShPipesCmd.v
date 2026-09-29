(* ===================================================================== *)
(* UkShPipesCmd.v -- [nulterminate], [parseline] AND [parsecmd] ON A      *)
(* PIPELINE OF ANY LENGTH, lane PIPES-C3b (design/pipes-general.md §5,    *)
(* cut C3, the part C3 left).                                             *)
(*                                                                        *)
(* sh.c's nulterminate (sh.c:471-501) recurses into BOTH sides of a PIPE  *)
(* node (sh.c:481-485):                                                   *)
(*                                                                        *)
(*   case PIPE:                                                           *)
(*     pcmd = (struct pipecmd* )cmd;                                      *)
(*     nulterminate(pcmd->left);                                          *)
(*     nulterminate(pcmd->right);                                         *)
(*     break;                                                             *)
(*                                                                        *)
(* and the parse is right-nested, so on a pipeline the left recursion is  *)
(* always the landed EXEC walk and the right one is the same function one *)
(* stage shorter.  §3 is therefore ONE induction on the stages over       *)
(* [UkShPipeParse.wp_kshp_nulterminate_pipe_g], the landed PIPE row with   *)
(* its right call a premise.                                              *)
(*                                                                        *)
(* [parseline] and [parsecmd] do not look at the shape of what they call: *)
(* [UkShPipeCm.wp_kshp_parseline_bar_g] and [wp_kshp_parsecmd_bar_g] are  *)
(* the landed walks with their calls premises, and §4 fills them with     *)
(* [UkShPipesParse.wp_kshp_parsepipe_bars] and §3.  The answer is the     *)
(* parser's own right spine [UkShPipesParse.ushq_ptree] over the line cut *)
(* at every token of every stage ([ushq_nulfolds]).                       *)
(*                                                                        *)
(* §1 is the PURE half: that cut satisfies [UkShPipesSeam.ushq_cuts_ok],  *)
(* the premise [UkShPipesSeam.ush_cmd_of_ushp_pipes] assumes -- on any    *)
(* nul-free line of a pipeline ([UkShPipesLex.ushq_bars]).  Every token   *)
(* ends where the scan stopped, on a blank, a symbol or the line's end,   *)
(* and no byte of a token's body is either, so no token's end falls in    *)
(* any token's body, whichever stage either belongs to.                   *)
(*                                                                        *)
(* TAINT: none -- nothing here forks, and the allocator is the caller's   *)
(* chain.                                                                 *)
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
Require Import UserHeap UkRun.
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UserFd.
Require Import UkShParse.
Require UkShCmdalloc.
Require Import UkShParseSym.
Require Import UkShParseCmd.
Require Import UkShMain.
Require Import UkShPipeSeam.
Require Import UkShPipesLex.
Require Import UkShPipesParse.
Require Import UkShPipesSeam.
Require Import RefParse RefParseSym RefParseBridge.  (* the reference's answer on the bars *)
Require Import UkShRedirs.      (* [ushp_malloc_chain] *)
Require Import UkShParser.      (* the general walks and the cut [ushp_zero_at] *)
Require Import UexecSG.
Require Import UkShPipeNode.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 THE CUT OF A PIPELINE, AND THE SEAM'S PREMISE                       *)
(* ===================================================================== *)

(* what [nulterminate] leaves on a right spine: every stage's argv cut,
   left to right, on one buffer *)
Fixpoint ushq_nulfolds (a : list (nat * nat)) (rest : list (list (nat * nat)))
    (g : nat -> bv 8) : nat -> bv 8 :=
  match rest with
  | [] => UkShParseCmd.ushp_nulfold a g
  | b :: rest' => ushq_nulfolds b rest' (UkShParseCmd.ushp_nulfold a g)
  end.

Lemma ushq_nulfold_app (x y : list (nat * nat)) (g : nat -> bv 8) :
  UkShParseCmd.ushp_nulfold (x ++ y) g
  = UkShParseCmd.ushp_nulfold y (UkShParseCmd.ushp_nulfold x g).
Proof using.
  revert g. induction x as [| tk x IH ]; intros g; [ reflexivity | ].
  cbn [app UkShParseCmd.ushp_nulfold]. exact (IH _).
Qed.

(* ...which is ONE fold over all the stages' tokens *)
Lemma ushq_nulfolds_flat (a : list (nat * nat))
    (rest : list (list (nat * nat))) (g : nat -> bv 8) :
  ushq_nulfolds a rest g = UkShParseCmd.ushp_nulfold (a ++ concat rest) g.
Proof using.
  revert a g. induction rest as [| b rest IH ]; intros a g.
  - cbn [ushq_nulfolds concat]. rewrite app_nil_r. reflexivity.
  - cbn [ushq_nulfolds concat]. rewrite IH.
    rewrite (ushq_nulfold_app a (b ++ concat rest)). reflexivity.
Qed.

(* the one landed pipe line's cut is the two-stage member *)
Lemma ushq_nulfolds_two (a b : list (nat * nat)) (g : nat -> bv 8) :
  ushq_nulfolds a [b] g
  = UkShParseCmd.ushp_nulfold b (UkShParseCmd.ushp_nulfold a g).
Proof using. reflexivity. Qed.

(* the bytes of a token's body are neither blank nor symbol *)
Lemma ushq_toklen_body (n i : nat) (f : nat -> bv 8) (j : nat) :
  (j < ushp_toklen n i f)%nat ->
  ushp_is_ws (f (i + j)%nat) || ushp_is_sym (f (i + j)%nat) = false.
Proof using.
  revert i j. induction n as [| n IH ]; intros i j Hj;
    cbn [ushp_toklen] in Hj; [ lia | ].
  destruct (ushp_is_ws (f i) || ushp_is_sym (f i)) eqn:E; [ lia | ].
  destruct j as [| j ].
  - rewrite Nat.add_0_r. exact E.
  - replace (i + S j)%nat with (S i + j)%nat by lia. apply IH. lia.
Qed.

(* A TOKEN THE SCAN PRODUCED: inside the line, a body of word bytes, and
   an end on a blank or a symbol unless it is the line's end *)
Definition ushq_tok_good (len : nat) (f : nat -> bv 8) (tk : nat * nat)
    : Prop :=
  (fst tk < snd tk /\ snd tk <= len)%nat
  /\ (forall x : nat, (fst tk <= x < snd tk)%nat ->
        ushp_is_ws (f x) || ushp_is_sym (f x) = false)
  /\ ((snd tk < len)%nat ->
        ushp_is_ws (f (snd tk)) || ushp_is_sym (f (snd tk)) = true).

Lemma ushq_toks_good (len : nat) (f : nat -> bv 8) (stop off : nat)
    (toks : list (nat * nat)) :
  ushs_toks len f stop off toks ->
  forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
    ushq_tok_good len f tk.
Proof using.
  induction 1 as [ off Hnil | off toks k n Hn Htoks IH ]; intros i tk Hi.
  - rewrite lookup_nil in Hi. discriminate.
  - destruct i as [| i ]; cbn in Hi; [ | exact (IH i tk Hi) ].
    injection Hi as <-.
    assert (Hk : (k <= len - off)%nat)
      by exact (ushp_skipws_le (len - off) off f).
    assert (Hn' : (n <= len - (off + k))%nat)
      by exact (ushp_toklen_le (len - (off + k)) (off + k) f).
    unfold ushq_tok_good. cbn [fst snd].
    split; [ lia | ]. split.
    + intros x Hx.
      replace x with (off + k + (x - (off + k)))%nat by lia.
      apply (ushq_toklen_body (len - (off + k)) (off + k) f).
      unfold n in Hx; lia.
    + intros Hlt.
      exact (UkShMain.ushp_toklen_end (len - (off + k)) (off + k) f
               ltac:(unfold n in Hlt; lia)).
Qed.

(* every token of every stage of a pipeline's line is one *)
Lemma ushq_bars_good (len : nat) (f : nat -> bv 8) :
  forall (c : nat) (a : list (nat * nat)) (rest : list (list (nat * nat))),
    ushq_bars len f c a rest ->
    forall (i : nat) (tk : nat * nat), (a ++ concat rest) !! i = Some tk ->
      ushq_tok_good len f tk.
Proof using.
  induction 1 as [ c toks Hcle Hns Htoks Htlen
                 | c gp toks b rest Hcle Hbw Htoks Hpos Htlen Hbars IH ];
    intros i tk Hi.
  - cbn [concat] in Hi. rewrite app_nil_r in Hi.
    exact (ushq_toks_good len f len c toks Htoks i tk Hi).
  - cbn [concat] in Hi.
    apply lookup_app_Some in Hi as [ Hi | [ _ Hi ] ].
    + exact (ushq_toks_good len f gp c toks Htoks i tk Hi).
    + exact (IH _ tk Hi).
Qed.

(* ...and the index bounds [nulterminate] reads, stage by stage *)
Lemma ushq_bars_bnd (len : nat) (f : nat -> bv 8) :
  forall (c : nat) (a : list (nat * nat)) (rest : list (list (nat * nat))),
    ushq_bars len f c a rest ->
    forall (j : nat) (toks : list (nat * nat)), (a :: rest) !! j = Some toks ->
    forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
      (fst tk <= len)%nat /\ (snd tk <= len)%nat.
Proof using.
  induction 1 as [ c toks Hcle Hns Htoks Htlen
                 | c gp toks b rest Hcle Hbw Htoks Hpos Htlen Hbars IH ];
    intros j tl Hj i tk Hi.
  - destruct j as [| j ]; cbn in Hj; [ | rewrite lookup_nil in Hj; discriminate ].
    injection Hj as <-.
    destruct (ushs_toks_in len f len c toks Htoks i tk Hi). split; lia.
  - destruct j as [| j ]; cbn in Hj.
    + injection Hj as <-.
      destruct (ushs_toks_in len f gp c toks Htoks i tk Hi). split; lia.
    + exact (IH j tl Hj i tk Hi).
Qed.

(* THE SEAM'S PREMISE for one token list, off a set [T] of good tokens it
   is drawn from, at the fold over all of [T] *)
Lemma ushq_cut_ok_of_good (len : nat) (f : nat -> bv 8)
    (T toks : list (nat * nat)) :
  (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
  (forall (i : nat) (tk : nat * nat), T !! i = Some tk ->
     ushq_tok_good len f tk) ->
  (forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
     exists q : nat, T !! q = Some tk) ->
  UkShPipeSeam.ushq_cut_ok len
    (UkShParseCmd.ushp_nulfold T (UkShParseCmd.ushp_ext len f)) toks.
Proof using.
  intros Hnn HT Hsub.
  unfold UkShPipeSeam.ushq_cut_ok. split_and!.
  - intros i tk Hi. destruct (Hsub i tk Hi) as [ q Hq ].
    destruct (HT q tk Hq) as ((H1 & H2) & _). split; lia.
  - intros i tk Hi. destruct (Hsub i tk Hi) as [ q Hq ].
    exact (UkShParseCmd.ushp_nulfold_hit T _ q tk Hq).
  - intros i tk Hi j Hj. destruct (Hsub i tk Hi) as [ q Hq ].
    destruct (HT q tk Hq) as ((H1 & H2) & Hbody & _).
    assert (Hx : ushp_is_ws (f (fst tk + j)%nat)
                 || ushp_is_sym (f (fst tk + j)%nat) = false)
      by (apply Hbody; lia).
    rewrite (UkShMain.ushp_nulfold_miss T _ (fst tk + j)%nat).
    + rewrite /UkShParseCmd.ushp_ext
        (bool_decide_eq_true_2 ((fst tk + j) < len)%nat ltac:(lia)).
      apply Hnn. lia.
    + intros q' t' Hq' He.
      destruct (HT q' t' Hq') as ((H1' & H2') & _ & Hend).
      assert (Hlt : (snd t' < len)%nat) by lia.
      pose proof (Hend Hlt) as He'. rewrite <- He in He'.
      rewrite Hx in He'. discriminate.
Qed.

(* ...AND AT EVERY STAGE: the cut [nulterminate] leaves on a nul-free line
   of a pipeline is what [UkShPipesSeam.ush_cmd_of_ushp_pipes] assumes *)
Lemma ushq_cuts_ok_bars (len : nat) (f : nat -> bv 8) (c : nat)
    (a : list (nat * nat)) (rest : list (list (nat * nat))) :
  (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
  ushq_bars len f c a rest ->
  UkShPipesSeam.ushq_cuts_ok len
    (ushq_nulfolds a rest (UkShParseCmd.ushp_ext len f)) a rest.
Proof using.
  intros Hnn Hb.
  rewrite ushq_nulfolds_flat.
  pose proof (ushq_bars_good len f c a rest Hb) as HT.
  set (T := (a ++ concat rest)) in *.
  assert (Hgen : forall (rest' : list (list (nat * nat)))
                   (a' pre : list (nat * nat)),
            T = pre ++ a' ++ concat rest' ->
            UkShPipesSeam.ushq_cuts_ok len
              (UkShParseCmd.ushp_nulfold T (UkShParseCmd.ushp_ext len f))
              a' rest').
  { induction rest' as [| b rest' IH ]; intros a' pre ET.
    - cbn [UkShPipesSeam.ushq_cuts_ok].
      apply (ushq_cut_ok_of_good len f T a' Hnn HT).
      intros i tk Hi. exists (length pre + i)%nat. rewrite ET.
      rewrite lookup_app_r; [ | lia ].
      replace (length pre + i - length pre)%nat with i by lia.
      apply lookup_app_l_Some. exact Hi.
    - cbn [UkShPipesSeam.ushq_cuts_ok]. split.
      + apply (ushq_cut_ok_of_good len f T a' Hnn HT).
        intros i tk Hi. exists (length pre + i)%nat. rewrite ET.
        rewrite lookup_app_r; [ | lia ].
        replace (length pre + i - length pre)%nat with i by lia.
        apply lookup_app_l_Some. exact Hi.
      + apply (IH b (pre ++ a')). rewrite ET.
        cbn [concat]. rewrite !app_assoc. reflexivity. }
  exact (Hgen rest a [] eq_refl).
Qed.



(* ===================================================================== *)
(* THE SPINE'S CUT IS THE REFERENCE'S (user-once N)                        *)
(* ===================================================================== *)
Lemma ushq_nulfolds_zero_at (a : list (nat * nat)) (rest : list (list (nat * nat)))
    (g : nat -> bv 8) :
  ushq_nulfolds a rest g = UkShParser.ushp_zero_at (ref_nulcut (ushq_ptree a rest)) g.
Proof using.
  revert a g. induction rest as [| b rest IH ]; intros a g;
    cbn [ushq_nulfolds ushq_ptree ref_nulcut].
  - exact (UkShParser.ushp_nulfold_zero_at a g).
  - rewrite IH UkShParser.ushp_zero_at_app UkShParser.ushp_nulfold_zero_at. reflexivity.
Qed.

Lemma ushq_ptree_walked (a : list (nat * nat)) (rest : list (list (nat * nat))) :
  ushp_walked (ushq_ptree a rest).
Proof using.
  revert a. induction rest as [| b rest IH ]; intro a; cbn [ushq_ptree ushp_walked];
    [ exact I | exact (conj I (IH b)) ].
Qed.

Lemma ushq_ptree_bounded (len : nat) (a : list (nat * nat)) (rest : list (list (nat * nat))) :
  Forall (fun toks : list (nat * nat) => (length toks < 10)%nat) (a :: rest) ->
  (forall (j : nat) (toks : list (nat * nat)), (a :: rest) !! j = Some toks ->
   forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
     (fst tk <= len)%nat /\ (snd tk <= len)%nat) ->
  ushp_bounded len (ushq_ptree a rest).
Proof using.
  revert a. induction rest as [| b rest IH ]; intros a Hlens Hbnd;
    cbn [ushq_ptree ushp_bounded].
  - split; [ exact (Forall_inv Hlens) | ].
    apply Forall_lookup_2. intros i tk Hi. exact (Hbnd 0%nat a eq_refl i tk Hi).
  - split.
    + split; [ exact (Forall_inv Hlens) | ].
      apply Forall_lookup_2. intros i tk Hi. exact (Hbnd 0%nat a eq_refl i tk Hi).
    + apply IH; [ exact (Forall_inv_tail Hlens) | ].
      intros j toks Hj. exact (Hbnd (S j) toks Hj).
Qed.

Section UkShPipesCmd.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation ushp_oom := (UkShCmdalloc.ushp_oom N).
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  Local Notation ushp_exec_at := (UkShParse.ushp_exec_at N).
  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation ushp_pipe_node := (UkShPipeNode.ushp_pipe_node N).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).

  (* ===================================================================== *)
  (* §2 A NODE'S ADDRESS, READ OFF THE RUN'S HEAP                           *)
  (* The parse answers the finished tree, whose rows keep no address        *)
  (* bound; [nulterminate]'s walk wants one per node, and the run's own     *)
  (* heap has it ([UkShMain.urun_ubytes_bnd], the seam's reading).          *)
  (* ===================================================================== *)
  Lemma ushq_exec_bnd (h : CpuId) (m : regfile) (pc : mword 64) (av : nat)
      (s0 p : Z) (toks : list (nat * nat)) :
    urun N h m pc av -∗ ushp_exec_at s0 p toks -∗ ⌜ p + 168 < Z64 ⌝.
  Proof using .
    iIntros "Hrun Hn".
    iDestruct "Hn" as "(_ & _ & _ & [Hty _] & _)".
    iDestruct (UkShMain.urun_ubytes_bnd N h m pc av p 4 _ with "Hrun Hty")
      as %Hb.
    destruct (Hb 0%nat ltac:(lia)) as [ _ Hhi ].
    assert (E38 : (2 ^ 38 = 274877906944)%Z) by reflexivity.
    rewrite E38 in Hhi.
    iPureIntro. unfold Z64. lia.
  Qed.

  (* a PIPE node of the spine, taken apart into the arm's three pieces *)
  Lemma ushq_tree_pipe_node (h : CpuId) (m : regfile) (pc : mword 64)
      (av : nat) (s0 t : Z) (a : list (nat * nat)) (r : ushp_cmd) :
    urun N h m pc av -∗
    ushp_tree s0 t (UshpPipe (UshpExec a) r) -∗
    urun N h m pc av ∗
    ∃ pl pr : Z,
      ushp_pipe_node t pl pr ∗ ushp_exec_at s0 pl a ∗ ushp_tree s0 pr r.
  Proof using .
    iIntros "Hrun Ht". cbn [UkShParse.ushp_tree].
    rewrite /UkShParse.ushp_type_at. cbn [UkShParse.ushp_ty].
    iDestruct "Ht" as "(%H0 & %H8 & [Hty Hpad] & Hl & Hr)".
    iDestruct "Hl" as (pl) "[Hwl Hl]".
    iDestruct "Hr" as (pr) "[Hwr Hr]".
    iDestruct (UkShMain.urun_ubytes_bnd N h m pc av t 4 _ with "Hrun Hty")
      as %Hb.
    destruct (Hb 0%nat ltac:(lia)) as [ _ Hhi ].
    assert (E38 : (2 ^ 38 = 274877906944)%Z) by reflexivity.
    rewrite E38 in Hhi.
    iFrame "Hrun". iExists pl, pr. iFrame "Hl Hr".
    rewrite /UkShPipeNode.ushp_pipe_node.
    iSplitR; [ iPureIntro; exact H0 | ].
    iSplitR; [ iPureIntro; exact H8 | ].
    iSplitR; [ iPureIntro; unfold Z64; lia | ].
    iFrame "Hty Hpad Hwl Hwr".
  Qed.

  (* ===================================================================== *)
  (* §3 nulterminate ON THE RIGHT SPINE, BY INDUCTION ON THE STAGES         *)
  (*                                                                        *)
  (* The budget is the EXEC walk's [4 + nn] plus one four-word frame per    *)
  (* PIPE node above it (the two recursions of one node run at the same     *)
  (* depth, so only the spine's length counts).                             *)
  (* ===================================================================== *)
  (* ===================================================================== *)
  (* THE SPINE AT THE GENERAL WALKS (user-once N): the tree opened to the    *)
  (* addressed tree (the bounds read off the run, as above), its token      *)
  (* counts read off its nodes, and the three walks below as corollaries   *)
  (* of [UkShParser]'s.                                                     *)
  (* ===================================================================== *)
  Lemma ushq_spine_otree (h : CpuId) (m : regfile) (pc : mword 64) (av : nat) (s0 : Z) :
    forall (rest : list (list (nat * nat))) (a : list (nat * nat)) (t : Z),
    urun N h m pc av -∗
    ushp_tree s0 t (ushq_ptree a rest) -∗
    urun N h m pc av ∗ UkShParser.ushp_otree N s0 t (ushq_ptree a rest).
  Proof using .
    induction rest as [| b rest IH ]; intros a t; iIntros "Hrun Ht".
    - cbn [ushq_ptree]. iDestruct (ushq_exec_bnd with "Hrun Ht") as %Hb.
      iFrame "Hrun". iExists UpExec. cbn [UkShParser.ushp_atree].
      iSplitR; [ iPureIntro; exact Hb | iExact "Ht" ].
    - cbn [ushq_ptree]. iDestruct (ushq_tree_pipe_node with "Hrun Ht") as "[Hrun Hn]".
      iDestruct "Hn" as (pl pr) "(Hpn & Hl & Hr)".
      iDestruct (ushq_exec_bnd with "Hrun Hl") as %Hbl.
      iDestruct (IH b pr with "Hrun Hr") as "[Hrun Hor]".
      iDestruct "Hor" as (ar) "Har".
      iFrame "Hrun". iExists (UpPipe pl pr UpExec ar). cbn [UkShParser.ushp_atree].
      iFrame "Hpn Har". iSplitR; [ iPureIntro; exact Hbl | iExact "Hl" ].
  Qed.

  Lemma ushq_spine_lens (s0 : Z) :
    forall (rest : list (list (nat * nat))) (a : list (nat * nat)) (t : Z),
    ushp_tree s0 t (ushq_ptree a rest) -∗
    ⌜ Forall (fun toks : list (nat * nat) => (length toks < 10)%nat) (a :: rest) ⌝.
  Proof using .
    induction rest as [| b rest IH ]; intros a t; iIntros "Ht".
    - cbn [ushq_ptree UkShParse.ushp_tree]. iDestruct "Ht" as "(%Hl & _)".
      iPureIntro. constructor; [ exact Hl | constructor ].
    - cbn [ushq_ptree UkShParse.ushp_tree]. iDestruct "Ht" as "(_ & _ & _ & Hl & Hr)".
      iDestruct "Hl" as (pl) "[_ Hl]". iDestruct "Hr" as (pr) "[_ Hr]".
      iDestruct "Hl" as "(%Hla & _)". iDestruct (IH b pr with "Hr") as %Hlr.
      iPureIntro. constructor; [ exact Hla | exact Hlr ].
  Qed.

  Lemma wp_kshp_nulterminate_pipes (s0 : Z) (len : nat) :
    0 < s0 -> s0 + Z.of_nat len < Z64 ->
    forall (rest : list (list (nat * nat))) (a : list (nat * nat))
           (h : CpuId) (m : regfile) (t : Z) (g : nat -> bv 8) (nn : nat),
    m !!! Regidx a0_idx = mword_of_int t ->
    (forall (j : nat) (toks : list (nat * nat)), (a :: rest) !! j = Some toks ->
     forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
       (fst tk <= len)%nat /\ (snd tk <= len)%nat) ->
    shp_code γt -∗
    shp_rodata γt -∗
    ushp_tree s0 t (ushq_ptree a rest) -∗
    ubytes γd s0 (S len) g -∗
    urun N h m (mword_of_int ShSyms.nulterminate)
      (4 + (length rest * 4 + nn)) -∗
    (ushp_tree s0 t (ushq_ptree a rest) -∗
     ubytes γd s0 (S len) (ushq_nulfolds a rest g) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx))
           (4 + (length rest * 4 + nn)) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hs0 Hs64 rest a h m t g nn Ha0 Hbnd.
    iIntros "#Hcode #Hro Ht Hline Hrun Hcont".
    iDestruct (ushq_spine_lens with "Ht") as %Hlens.
    iDestruct (ushq_spine_otree with "Hrun Ht") as "[Hrun Hot]".
    iDestruct "Hot" as (ap) "Hat".
    replace (4 + (length rest * 4 + nn))%nat
      with (4 * ushp_ht (ushq_ptree a rest) + nn)%nat by (rewrite ushq_ptree_ht; lia).
    iApply (UkShParser.wp_ref_nulterminate N s0 len (ushq_ptree a rest) h m t ap g nn
              Ha0 Hs0 Hs64 (ushq_ptree_walked a rest) (ushq_ptree_bounded len a rest Hlens Hbnd)
              with "Hcode Hro Hat Hline Hrun").
    iIntros "Hat Hline" (h' m') "%Hcs %Ha0' Hrun".
    rewrite <- ushq_nulfolds_zero_at.
    iApply ("Hcont" with "[Hat] Hline [%//] [%//] Hrun").
    iApply (UkShParser.ushp_atree_close N with "Hat").
  Qed.

  (* the one-bar line through it, as a check that the induction composes at
     the landed shape *)
  Corollary wp_kshp_nulterminate_pipes_one (s0 : Z) (len : nat)
      (a b : list (nat * nat)) (h : CpuId) (m : regfile) (t : Z)
      (g : nat -> bv 8) (nn : nat) :
    0 < s0 -> s0 + Z.of_nat len < Z64 ->
    m !!! Regidx a0_idx = mword_of_int t ->
    (forall (j : nat) (toks : list (nat * nat)), [a; b] !! j = Some toks ->
     forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
       (fst tk <= len)%nat /\ (snd tk <= len)%nat) ->
    shp_code γt -∗
    shp_rodata γt -∗
    ushp_tree s0 t (UshpPipe (UshpExec a) (UshpExec b)) -∗
    ubytes γd s0 (S len) g -∗
    urun N h m (mword_of_int ShSyms.nulterminate) (4 + (4 + nn)) -∗
    (ushp_tree s0 t (UshpPipe (UshpExec a) (UshpExec b)) -∗
     ubytes γd s0 (S len)
       (UkShParseCmd.ushp_nulfold b (UkShParseCmd.ushp_nulfold a g)) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + (4 + nn)) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hs0 Hs64 Ha0 Hbnd.
    exact (wp_kshp_nulterminate_pipes s0 len Hs0 Hs64 [b] a h m t g nn
             Ha0 Hbnd).
  Qed.

  (* ===================================================================== *)
  (* §4 parseline AND parsecmd AT ANY NUMBER OF BARS                        *)
  (*                                                                        *)
  (* The allocator chain of [UkShPipesParse] ([UkShPipesSeam.ushq_um_chain] *)
  (* at the landed allocator): the parse spends links [i .. i + 2k] for k   *)
  (* bars.  The budget is the landed pipe line's with six words per further *)
  (* bar, [length rest * 6 + k]: [parsepipe]'s frames need exactly that,    *)
  (* and [nulterminate]'s four per bar fit under it.                        *)
  (* ===================================================================== *)
  Context (UM : nat -> iProp Σ) (K : nat).
  Hypothesis Hchain :
    forall i : nat, (i < K)%nat -> ushp_malloc_ty (UM i) (UM (S i)).

  Lemma wp_kshp_parseline_pipes {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dq dw dv : dfrac) (ps s0 : Z) (len : nat) (f : nat -> bv 8)
      (a : list (nat * nat)) (rest : list (list (nat * nat))) (i k : nat) :
    ushq_bars len f 0%nat a rest ->
    (i + 2 * length rest + 1 <= K)%nat ->
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int s0) -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM i -∗
    ushp_oom Pex (20 + (6 + k)) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parseline)
      (6 + (6 + (16 + (24 + (8 + (length rest * 6 + k)))))) -∗
    (∀ t : Z,
       ushp_tree s0 t (ushq_ptree a rest) -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
           UM (i + 2 * length rest + 1) -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (6 + (16 + (24 + (8 + (length rest * 6 + k)))))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hchain.
    intros Hbars HK Ha0 Ha1 Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    iDestruct (ustr_nonul with "Hstr") as %Hnn.
    replace (6 + (6 + (16 + (24 + (8 + (length rest * 6 + k))))))%nat
      with (UkShParser.ushp_pl_room (ushq_ptree a rest) + (8 + k))%nat
      by (unfold UkShParser.ushp_pl_room; rewrite UkShPipesParse.ushq_ptree_pp_room; lia).
    (* the law at the general walk's budget: the room less the spine's depth *)
    iDestruct (UkShCmdalloc.ushp_oom_mono N Pex (20 + (6 + k))
                 (UkShParser.ushp_pl_room (ushq_ptree a rest) + (8 + k)
                  - UkShParser.ushp_pl_deep (ushq_ptree a rest))
                 ltac:(unfold UkShParser.ushp_pl_room, UkShParser.ushp_pl_deep;
                       rewrite UkShPipesParse.ushq_ptree_pp_room UkShPipesParse.ushq_ptree_pp_deep; lia)
                 with "Hpx") as "#Hpxg".
    iApply (UkShParser.wp_ref_parseline N h m dq dw dv ps s0 len 0%nat
              (S (len + length rest + 1)) len f (mword_of_int s0) (ushq_ptree a rest)
              (UM i) (UM (i + 2 * length rest + 1)) (8 + k)
              Ha0 Ha1 ltac:(lia) ltac:(f_equal; lia)
              (ushq_bars_scope len f 0%nat a rest Hbars)
              (ref_parseline_end len f (S (len + length rest + 1)) 0%nat (ushq_ptree a rest) ltac:(lia)
                 (ushq_bars_parsepipe len f Hnn 0%nat a rest Hbars (len + length rest + 1) ltac:(lia)))
              ltac:(rewrite ushq_ptree_nodes;
                    replace (i + 2 * length rest + 1)%nat with (i + (2 * length rest + 1))%nat by lia;
                    exact (UkShPipesParse.ushq_UM_chain N UM K Hchain (2 * length rest + 1) i ltac:(lia)))
              Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM Hpxg Hpay Hrun").
    iIntros (root) "Hot Hcur Hstr Hws Hsy".
    iIntros (h' m') "%Hcs %Ha0' HM' Hpay Hrun".
    iApply ("Hcont" $! root with "[Hot] Hcur Hstr Hws Hsy [%//] [%//] HM' Hpay Hrun").
    iApply (UkShParser.ushp_otree_close N with "Hot").
  Qed.

  Lemma wp_kshp_parsecmd_pipes {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dw dv : dfrac) (s0 : Z) (len : nat) (f : nat -> bv 8)
      (a : list (nat * nat)) (rest : list (list (nat * nat))) (i k : nat) :
    ushq_bars len f 0%nat a rest ->
    (i + 2 * length rest + 1 <= K)%nat ->
    m !!! Regidx a0_idx = mword_of_int s0 ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM i -∗
    ushp_oom Pex (20 + (6 + k)) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsecmd)
      (8 + (6 + (6 + (16 + (24 + (8 + (length rest * 6 + k))))))) -∗
    (∀ t : Z,
       ushp_tree s0 t (ushq_ptree a rest) -∗
       ubytes γd s0 (S len)
         (ushq_nulfolds a rest (UkShParseCmd.ushp_ext len f)) -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
           UM (i + 2 * length rest + 1) -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (8 + (6 + (6 + (16 + (24 + (8 + (length rest * 6 + k))))))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hchain.
    intros Hbars HK Ha0 Hs0 Hs64.
    iIntros "#Hcode #Hro Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    iDestruct (ustr_nonul with "Hstr") as %Hnn.
    replace (8 + (6 + (6 + (16 + (24 + (8 + (length rest * 6 + k)))))))%nat
      with (UkShParser.ushp_room (ushq_ptree a rest) + (8 + k))%nat
      by (unfold UkShParser.ushp_room, UkShParser.ushp_pl_room;
          rewrite UkShPipesParse.ushq_ptree_pp_room ushq_ptree_ht; lia).
    (* the law at the general walk's budget: the room less the spine's depth *)
    iDestruct (UkShCmdalloc.ushp_oom_mono N Pex (20 + (6 + k))
                 (UkShParser.ushp_room (ushq_ptree a rest) + (8 + k)
                  - UkShParser.ushp_deep (ushq_ptree a rest))
                 ltac:(unfold UkShParser.ushp_room, UkShParser.ushp_pl_room,
                         UkShParser.ushp_deep, UkShParser.ushp_pl_deep;
                       rewrite UkShPipesParse.ushq_ptree_pp_room UkShPipesParse.ushq_ptree_pp_deep
                         ushq_ptree_ht; lia)
                 with "Hpx") as "#Hpxg".
    assert (Hch : UkShRedirs.ushp_malloc_chain N (ushp_nodes (ushq_ptree a rest))
                    (UM i) (UM (i + 2 * length rest + 1))).
    { rewrite ushq_ptree_nodes.
      replace (i + 2 * length rest + 1)%nat with (i + (2 * length rest + 1))%nat by lia.
      exact (UkShPipesParse.ushq_UM_chain N UM K Hchain (2 * length rest + 1) i ltac:(lia)). }
    iApply (UkShParser.wp_ref_parsecmd N h m dw dv s0 len f (ushq_ptree a rest)
              (UM i) (UM (i + 2 * length rest + 1)) (8 + k)
              Ha0 (ref_sym_scope_of_from_0 len f (ushq_bars_scope len f 0%nat a rest Hbars))
              (ref_parsecmd_bars len f a rest Hnn Hbars) (ushq_ptree_cat a rest)
              Hch Hs0 Hs64
              with "Hcode Hro Hstr Hws Hsy HM Hpxg Hpay Hrun").
    iIntros (p) "Hot Hline Hws Hsy".
    iIntros (h' m') "%Hcs %Ha0' HM' Hpay Hrun".
    rewrite <- ushq_nulfolds_zero_at.
    iApply ("Hcont" $! p with "[Hot] Hline Hws Hsy [%//] [%//] HM' Hpay Hrun").
    iApply (UkShParser.ushp_otree_close N with "Hot").
  Qed.

End UkShPipesCmd.
