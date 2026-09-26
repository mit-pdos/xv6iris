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
Require Import UkShPipeLex.
Require Import UkShPipeParse.
Require Import UkShPipeSeam.
Require Import UkShPipeCm.
Require Import UkShPipesLex.
Require Import UkShPipesParse.
Require Import UkShPipesSeam.
Require Import UexecSG.
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
  Local Notation ushp_pipe_node := (UkShPipeParse.ushp_pipe_node N).
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
    rewrite /UkShPipeParse.ushp_pipe_node.
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
    intros Hs0 Hs64 rest.
    induction rest as [| b rest IH ];
      intros a h m t g nn Ha0 Hbnd;
      iIntros "#Hcode #Hro Ht Hline Hrun Hcont".
    - (* ---- THE LAST STAGE: the landed EXEC walk ---- *)
      change (ushq_ptree a []) with (UshpExec a).
      change (ushq_nulfolds a [] g) with (UkShParseCmd.ushp_nulfold a g).
      change (4 + (length (@nil (list (nat * nat))) * 4 + nn))%nat
        with (4 + nn)%nat.
      iDestruct (UkShPipeParse.ushp_exec_at_facts N with "Ht")
        as "[%Hf Ht]".
      destruct Hf as (Hlen & Ht0 & Ht8).
      iDestruct (ushq_exec_bnd with "Hrun Ht") as %Htb.
      iApply (UkShParseCmd.wp_kshp_nulterminate N h m s0 t len g a nn
                Ha0 Hs0 Hs64 Ht0 Ht8 Htb Hlen (Hbnd 0%nat a eq_refl)
                with "Hcode Hro Ht Hline Hrun Hcont").
    - (* ---- A PIPE NODE: its EXEC child, and the rest by induction ---- *)
      change (ushq_ptree a (b :: rest))
        with (UshpPipe (UshpExec a) (ushq_ptree b rest)).
      change (ushq_nulfolds a (b :: rest) g)
        with (ushq_nulfolds b rest (UkShParseCmd.ushp_nulfold a g)).
      assert (E : (4 + (length (b :: rest) * 4 + nn))%nat
                  = (4 + (4 + (length rest * 4 + nn)))%nat)
        by (cbn [length]; lia).
      rewrite E.
      iDestruct (ushq_tree_pipe_node with "Hrun Ht")
        as "[Hrun Hn]".
      iDestruct "Hn" as (pl pr) "(Hpn & Hl & Hr)".
      iDestruct (UkShPipeParse.ushp_pipe_node_addr N with "Hpn")
        as "[%Haddr Hpn]".
      destruct Haddr as (Ht0 & Ht8 & Ht40).
      iDestruct (UkShPipeParse.ushp_exec_at_facts N with "Hl")
        as "[%Hf Hl]".
      destruct Hf as (Hlen & Hpl0 & Hpl8).
      iDestruct (ushq_exec_bnd with "Hrun Hl") as %Hplb.
      iApply (UkShPipeParse.wp_kshp_nulterminate_pipe_g N h m s0 t pl pr
                len g a (ushp_tree s0 pr (ushq_ptree b rest))
                (ushq_nulfolds b rest) (length rest * 4 + nn)
                Ha0 Hs0 Hs64 Ht0 Ht8 Ht40 Hpl0 Hpl8 Hplb Hlen
                (Hbnd 0%nat a eq_refl)
                with "Hcode Hro Hpn Hl Hr Hline Hrun [] [Hcont]").
      + (* the RIGHT call is the induction hypothesis *)
        iIntros (h1 m1 g1) "%Ha0' Hr Hline Hrun Hk".
        iApply (IH b h1 m1 pr g1 nn Ha0'
                  (fun j toks Hj => Hbnd (S j) toks Hj)
                  with "Hcode Hro Hr Hline Hrun Hk").
      + iIntros "Hpn Hl Hr Hline" (h' m') "%Hcs %Ha0' Hrun".
        iApply ("Hcont" with "[Hpn Hl Hr] Hline [] [] Hrun").
        * iApply (UkShPipeParse.ushp_pipe_close N s0 t pl pr
                    (UshpExec a) (ushq_ptree b rest) with "Hpn Hl Hr").
        * iPureIntro. exact Hcs.
        * iPureIntro. exact Ha0'.
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
    iApply (UkShPipeCm.wp_kshp_parseline_bar_g N h m dq dw dv ps s0 len f
              (UM i) (UM (i + 2 * length rest + 1))
              (fun t : Z => ushp_tree s0 t (ushq_ptree a rest))
              (length rest * 6 + k)
              Ha0 Ha1 Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM Hpay Hrun [] Hcont").
    (* the call: [parsepipe] at any number of bars *)
    iIntros (h1 m1) "%Ha0' %Ha1' Hcur Hstr Hws Hsy HM Hpay Hrun Hk".
    assert (E : (6 + (16 + (24 + (8 + (length rest * 6 + k)))))%nat
                = (6 + (16 + (24 + (2 + (length rest * 6 + (6 + k))))))%nat)
      by lia.
    rewrite E.
    iApply (UkShPipesParse.wp_kshp_parsepipe_bars N UM K Hchain dq dw dv
              ps s0 len f Hs0 Hs64 Hps0 Hps8 Hpssz 0%nat a rest Hbars
              i (6 + k) h1 m1 HK Ha0' Ha1'
              with "Hcode Hro [Hcur] Hstr Hws Hsy HM Hpx Hpay Hrun Hk").
    replace (s0 + Z.of_nat 0) with s0 by lia. iExact "Hcur".
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
    iApply (UkShPipeCm.wp_kshp_parsecmd_bar_g N h m dw dv s0 len f
              (UM i) (UM (i + 2 * length rest + 1))
              (fun t : Z => ushp_tree s0 t (ushq_ptree a rest))
              (ushq_nulfolds a rest (UkShParseCmd.ushp_ext len f))
              (length rest * 6 + k)
              Ha0 Hs0 Hs64
              with "Hcode Hro Hstr Hws Hsy HM Hpay Hrun [] [] Hcont").
    - (* parseline *)
      iIntros (h1 m1 ps) "%Ha0' %Ha1' %Hps0 %Hps8 %Hpsz Hcur Hstr Hws Hsy HM
                          Hpay Hrun Hk".
      iApply (wp_kshp_parseline_pipes h1 m1 (DfracOwn 1) dw dv ps s0 len f
                a rest i k Hbars HK Ha0' Ha1' ltac:(lia) ltac:(lia)
                Hps0 Hps8 Hpsz
                with "Hcode Hro Hcur Hstr Hws Hsy HM Hpx Hpay Hrun Hk").
    - (* nulterminate, on the spine *)
      iIntros (h1 m1 t) "%Ha0' HPT Hline Hrun Hk".
      assert (E : (60 + (length rest * 6 + k))%nat
                  = (4 + (length rest * 4
                          + (56 + (length rest * 2 + k))))%nat)
        by lia.
      rewrite E.
      iApply (wp_kshp_nulterminate_pipes s0 len ltac:(lia) ltac:(lia)
                rest a h1 m1 t (UkShParseCmd.ushp_ext len f)
                (56 + (length rest * 2 + k)) Ha0'
                (ushq_bars_bnd len f 0%nat a rest Hbars)
                with "Hcode Hro HPT Hline Hrun Hk").
  Qed.

End UkShPipesCmd.
