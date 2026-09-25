(* ===================================================================== *)
(* PipesDiscDec.v -- A DECISION PROCEDURE for the blocks of a pipeline   *)
(* ([PipesDisc.line_blocks]) and the demos run through it (cut C2).       *)
(*                                                                        *)
(*  The runs of a line are FINITE -- every [D] is a prefix of the line's *)
(*  content -- so they are enumerated ([stage_outs], [sfx_runs],          *)
(*  [line_runs], each proved equal to its relation), and a merge is       *)
(*  tested byte by byte ([mergeb], pruning at the first byte no stream    *)
(*  offers).  [line_blocksb_spec] is the reflection the demos spend.      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list countable bitvector.definitions.
Require Import RiscvLang ObsTrace.
Require Import LineWords EchoDisc LineBytes LineModel PipeDisc.
Require Import StringBytes ProgTree ProgTreePipes PipesPair PipesDisc.
Require Import LineModelLinks.
From stdpp Require Import list.

Local Open Scope nat_scope.

(* ===================================================================== *)
(*  1.  THE ENUMERATIONS                                                  *)
(* ===================================================================== *)

Definition prefixes (L : bytes) : list bytes := (fun k => take k L) <$> seq 0 (S (length L)).

Lemma prefixes_spec D L : D ∈ prefixes L <-> D `prefix_of` L.
Proof using.
  unfold prefixes. rewrite elem_of_list_fmap. split.
  - intros (k & -> & _). apply prefix_take.
  - intros HD. exists (length D). split; [exact (prefix_take_eq D L HD) |].
    apply elem_of_seq. pose proof (prefix_length _ _ HD). lia.
Qed.

(* the program's own outcomes of a stage, past sh's two *)
Definition stage_outs_prog (fc : bytes -> option bytes) (L : bytes) (st : stage) : list st_out :=
  match st with
  | SProd (PrEcho ws) =>
      if decide (L = wl_line (drop 1 ws))
      then MkSO [] None (Some (WrAll L)) :: ((fun D => MkSO [] None (Some (WrHalt D))) <$> prefixes L)
      else []
  | SProd (PrCatF f) =>
      MkSO (cat_dg_open f) None (Some WrNone)
      :: (if decide (fc f = Some L)
          then MkSO [] None (Some (WrAll L))
               :: ((fun D => MkSO cat_dg_write None (Some (WrHalt D))) <$> prefixes L)
          else [])
  | SMid =>
      ((fun D => MkSO [] (Some (RdEof D)) (Some (WrAll D))) <$> prefixes L)
      ++ ((fun D => MkSO cat_dg_write (Some RdGone) (Some (WrHalt D))) <$> prefixes L)
  | SLast => (fun D => MkSO D (Some (RdEof D)) None) <$> prefixes L
  end.

Definition stage_outs (fc : bytes -> option bytes) (L : bytes) (st : stage) : list st_out :=
  MkSO (st_dg_exec st) (st_rd_dead st) (st_wr_dead st)
  :: MkSO [] (st_rd_dead st) (st_wr_dead st)
  :: stage_outs_prog fc L st.

Lemma stage_outs_spec fc L st so : so ∈ stage_outs fc L st <-> stage_out fc L st so.
Proof using.
  split.
  - unfold stage_outs. intros H.
    apply elem_of_cons in H as [-> | H]; [apply so_exec |].
    apply elem_of_cons in H as [-> | H]; [apply so_silent |].
    destruct st as [[ws | f] | |]; cbn [stage_outs_prog] in H.
    + destruct (decide (L = wl_line (drop 1 ws))) as [HL | HL]; [| by apply elem_of_nil in H].
      apply elem_of_cons in H as [-> | H]; [apply so_echo; exact HL |].
      apply elem_of_list_fmap in H as (D & -> & HD).
      apply so_echo_halt; [exact HL | apply prefixes_spec; exact HD].
    + apply elem_of_cons in H as [-> | H]; [apply so_catf_open |].
      destruct (decide (fc f = Some L)) as [HL | HL]; [| by apply elem_of_nil in H].
      apply elem_of_cons in H as [-> | H]; [apply so_catf; exact HL |].
      apply elem_of_list_fmap in H as (D & -> & HD).
      apply so_catf_halt; [exact HL | apply prefixes_spec; exact HD].
    + apply elem_of_app in H as [H | H]; apply elem_of_list_fmap in H as (D & -> & HD).
      * apply so_mid_copy. apply prefixes_spec. exact HD.
      * apply so_mid_halt. apply prefixes_spec. exact HD.
    + apply elem_of_list_fmap in H as (D & -> & HD). apply so_last. apply prefixes_spec. exact HD.
  - unfold stage_outs. intros H.
    destruct H as [st | st | ws HL | ws D HL HD | f Hf | f D Hf HD | f | D HD | D HD | D HD].
    + apply elem_of_cons. left. reflexivity.
    + apply elem_of_cons. right. apply elem_of_cons. left. reflexivity.
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog].
      rewrite decide_True by exact HL. apply elem_of_cons. left. reflexivity.
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog].
      rewrite decide_True by exact HL. apply elem_of_cons. right.
      apply elem_of_list_fmap. exists D. split; [reflexivity | apply prefixes_spec; exact HD].
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog]. apply elem_of_cons. right.
      rewrite decide_True by exact Hf. apply elem_of_cons. left. reflexivity.
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog]. apply elem_of_cons. right.
      rewrite decide_True by exact Hf. apply elem_of_cons. right.
      apply elem_of_list_fmap. exists D. split; [reflexivity | apply prefixes_spec; exact HD].
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog]. apply elem_of_cons. left. reflexivity.
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog]. apply elem_of_app. left.
      apply elem_of_list_fmap. exists D. split; [reflexivity | apply prefixes_spec; exact HD].
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog]. apply elem_of_app. right.
      apply elem_of_list_fmap. exists D. split; [reflexivity | apply prefixes_spec; exact HD].
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog].
      apply elem_of_list_fmap. exists D. split; [reflexivity | apply prefixes_spec; exact HD].
Qed.

Fixpoint sfx_runs (fc : bytes -> option bytes) (L : bytes) (m : nat) (w : wr_out) (wc : bool)
    : list (list bytes) :=
  match m with
  | 0 => []
  | 1 => (fun so => [so_cons so])
           <$> filter (fun so => pipe_pairB L wc w (rd_of so)) (stage_outs fc L SLast)
  | S (S m' as m1) =>
      [dg_pipe_b]
      :: mjoin ((fun so => (fun ss => so_cons so :: ss) <$> sfx_runs fc L m1 (wr_of so) true)
                  <$> filter (fun so => pipe_pairB L wc w (rd_of so)) (stage_outs fc L SMid))
  end.

Lemma sfx_runs_spec fc L m w wc ss : ss ∈ sfx_runs fc L m w wc <-> sfx_run fc L m w wc ss.
Proof using.
  revert w wc ss. induction m as [| m IH]; intros w wc ss.
  - cbn [sfx_runs]. split; [intros H; by apply elem_of_nil in H |].
    intros H. remember 0 as z eqn:Hz in H. revert Hz. destruct H; intros Hz; discriminate Hz.
  - destruct m as [| m'].
    + cbn [sfx_runs]. rewrite elem_of_list_fmap. split.
      * intros (so & -> & Hso). apply elem_of_list_filter in Hso as [Hp Hso].
        apply stage_outs_spec in Hso. apply sr_last; assumption.
      * intros H. remember 1 as z eqn:Hz in H. revert Hz.
        destruct H as [win wc0 so Hso Hp | m0 win wc0 | m0 win wc0 so ss0 Hso Hp Hr];
          intros Hz; [| discriminate Hz | discriminate Hz].
        exists so. split; [reflexivity |].
        apply elem_of_list_filter. split; [exact Hp | apply stage_outs_spec; exact Hso].
    + cbn [sfx_runs]. rewrite elem_of_cons, elem_of_list_join. split.
      * intros [-> | (l & Hss & Hl)]; [apply sr_pipe_fail |].
        apply elem_of_list_fmap in Hl as (so & -> & Hso).
        apply elem_of_list_filter in Hso as [Hp Hso].
        apply elem_of_list_fmap in Hss as (ss' & -> & Hss'). apply IH in Hss'.
        apply stage_outs_spec in Hso. apply sr_node; assumption.
      * intros H. remember (S (S m')) as z eqn:Hz in H. revert Hz.
        destruct H as [win wc0 so Hso Hp | m0 win wc0 | m0 win wc0 so ss0 Hso Hp Hr];
          intros Hz; [discriminate Hz | left; reflexivity |].
        injection Hz as ->. right.
        exists ((fun ss => so_cons so :: ss) <$> sfx_runs fc L (S m') (wr_of so) true). split.
        -- apply elem_of_list_fmap. exists ss0. split; [reflexivity | apply IH; exact Hr].
        -- apply elem_of_list_fmap. exists so. split; [reflexivity |].
           apply elem_of_list_filter. split; [exact Hp | apply stage_outs_spec; exact Hso].
Qed.

Definition line_runs (fc : bytes -> option bytes) (l : pline') : list (list bytes) :=
  match l with
  | LEcho' ws => [[wl_line (drop 1 ws)]; [dg_execL]; [[]]]
  | LPipes p n =>
      (if decide (1 <= n) then [[dg_pipe_b]] else [])
      ++ mjoin ((fun so => (fun ss => so_cons so :: ss)
                             <$> sfx_runs fc (prod_content fc p) n (wr_of so) (prod_cat p))
                  <$> stage_outs fc (prod_content fc p) (SProd p))
  end.

Lemma line_runs_spec fc l ss : ss ∈ line_runs fc l <-> line_run fc l ss.
Proof using.
  destruct l as [ws | p n]; cbn [line_runs].
  - split.
    + intros H. apply elem_of_cons in H as [-> | H]; [apply lr_echo |].
      apply elem_of_cons in H as [-> | H]; [apply lr_echo_exec |].
      apply elem_of_list_singleton in H as ->. apply lr_echo_silent.
    + intros H. remember (LEcho' ws) as l eqn:Hl. revert Hl.
      destruct H as [ws0 | ws0 | ws0 | p n Hn | p n so ss0 Hso Hr]; intros Hl;
        try discriminate Hl; injection Hl as ->.
      * apply elem_of_cons. left. reflexivity.
      * apply elem_of_cons. right. apply elem_of_cons. left. reflexivity.
      * apply elem_of_cons. right. apply elem_of_cons. right. apply elem_of_list_singleton. reflexivity.
  - rewrite elem_of_app, elem_of_list_join. split.
    + intros [H | (l & Hss & Hl)].
      * destruct (decide (1 <= n)) as [Hn | Hn]; [| by apply elem_of_nil in H].
        apply elem_of_list_singleton in H as ->. apply lr_pipe_fail. exact Hn.
      * apply elem_of_list_fmap in Hl as (so & -> & Hso).
        apply elem_of_list_fmap in Hss as (ss' & -> & Hss').
        apply sfx_runs_spec in Hss'. apply stage_outs_spec in Hso. apply lr_node; assumption.
    + intros H. remember (LPipes p n) as l eqn:Hl. revert Hl.
      destruct H as [ws0 | ws0 | ws0 | p0 n0 Hn | p0 n0 so ss0 Hso Hr]; intros Hl;
        try discriminate Hl; injection Hl as -> ->.
      * left. rewrite decide_True by exact Hn. apply elem_of_list_singleton. reflexivity.
      * right. exists ((fun ss => so_cons so :: ss)
                         <$> sfx_runs fc (prod_content fc p) n (wr_of so) (prod_cat p)). split.
        -- apply elem_of_list_fmap. exists ss0. split; [reflexivity | apply sfx_runs_spec; exact Hr].
        -- apply elem_of_list_fmap. exists so. split; [reflexivity | apply stage_outs_spec; exact Hso].
Qed.

(* ===================================================================== *)
(*  2.  THE MERGE TEST                                                    *)
(* ===================================================================== *)

(* every way to take the byte [x] off the head of one of the streams *)
Fixpoint picks (x : bv 8) (ss : list bytes) : list (list bytes) :=
  match ss with
  | [] => []
  | s :: ss' =>
      (match s with y :: s' => if decide (y = x) then [s' :: ss'] else [] | [] => [] end)
      ++ ((fun r => s :: r) <$> picks x ss')
  end.

Lemma picks_spec x ss ss' :
  ss' ∈ picks x ss <-> exists i s, ss !! i = Some (x :: s) /\ ss' = <[i := s]> ss.
Proof using.
  revert ss'. induction ss as [| s ss IH]; intros ss'; cbn [picks].
  - split; [intros H; by apply elem_of_nil in H | intros (i & s & H & _); discriminate H].
  - rewrite elem_of_app. split.
    + intros [H | H].
      * destruct s as [| y s']; [by apply elem_of_nil in H |].
        destruct (decide (y = x)) as [-> | Hne]; [| by apply elem_of_nil in H].
        apply elem_of_list_singleton in H as ->. exists 0, s'. split; reflexivity.
      * apply elem_of_list_fmap in H as (r & -> & Hr). apply IH in Hr as (i & s0 & Hi & ->).
        exists (S i), s0. split; [exact Hi | reflexivity].
    + intros ([| i] & s0 & Hi & ->).
      * left. injection Hi as ->. cbn. rewrite decide_True by reflexivity.
        apply elem_of_list_singleton. reflexivity.
      * right. apply elem_of_list_fmap. exists (<[i := s0]> ss). split; [reflexivity |].
        apply IH. exists i, s0. split; [exact Hi | reflexivity].
Qed.

Fixpoint mergeb (ss : list bytes) (b : bytes) : bool :=
  match b with
  | [] => forallb (fun s => bool_decide (s = [])) ss
  | x :: b' => existsb (fun ss' => mergeb ss' b') (picks x ss)
  end.

Lemma mergeb_spec ss b : mergeb ss b = true <-> merge_all ss b.
Proof using.
  revert ss. induction b as [| x b IH]; intros ss; cbn [mergeb].
  - rewrite forallb_forall. split.
    + intros H. apply ma_done. apply Forall_forall. intros s Hs.
      apply elem_of_list_In in Hs. exact (bool_decide_eq_true_1 _ (H s Hs)).
    + intros Hm s Hs. apply bool_decide_eq_true_2.
      inversion Hm as [ss' HF | ]; subst.
      exact (proj1 (Forall_forall _ _) HF s (proj2 (elem_of_list_In _ _) Hs)).
  - rewrite existsb_exists. split.
    + intros (ss' & Hin & Hm). apply elem_of_list_In, picks_spec in Hin as (i & s & Hi & ->).
      apply (ma_take ss i x s b Hi). apply IH. exact Hm.
    + intros Hm. inversion Hm as [| ss0 i x0 s b0 Hi Hm']; subst.
      exists (<[i := s]> ss). split; [| apply IH; exact Hm'].
      apply elem_of_list_In, picks_spec. exists i, s. split; [exact Hi | reflexivity].
Qed.

Definition line_blocksb (fc : bytes -> option bytes) (l : pline') (b : bytes) : bool :=
  existsb (fun ss => mergeb ss b) (line_runs fc l).

Lemma line_blocksb_spec fc l b : line_blocksb fc l b = true <-> line_blocks fc l b.
Proof using.
  unfold line_blocksb, line_blocks. rewrite existsb_exists. split.
  - intros (ss & Hin & Hm). exists ss.
    split; [apply line_runs_spec, elem_of_list_In; exact Hin | apply mergeb_spec; exact Hm].
  - intros (ss & Hr & Hm). exists ss.
    split; [apply elem_of_list_In, line_runs_spec; exact Hr | apply mergeb_spec; exact Hm].
Qed.

(* ===================================================================== *)
(*  2b.  THE TERMINAL BLOCKS, PREFIX-CLOSED                               *)
(*                                                                        *)
(*  [plalt_ok]'s [PLTerm] arm asks for a prefix of a terminal block       *)
(*  ([line_term_blocks]): the waited streams merged, then sh's prompt,    *)
(*  shuffled with a prefix of the stray's stream.  The terminal runs are  *)
(*  finite ([line_terms], proved equal to [line_term]), and a prefix of  *)
(*  such a block is tested byte by byte ([ptermb]): a byte comes off the  *)
(*  head of a waited stream, off the prompt once every waited stream is  *)
(*  empty, or off the stray -- and nothing has to be exhausted.           *)
(* ===================================================================== *)

Fixpoint sfx_terms (fc : bytes -> option bytes) (L : bytes) (m : nat) (w : wr_out) (wc : bool)
    : list (list bytes * bytes) :=
  match m with
  | 0 => []
  | 1 => []
  | S (S m' as m1) =>
      ((fun so => ([dg_fork_b], so_cons so)) <$> stage_outs fc L SMid)
      ++ mjoin ((fun so => (fun Ws : list bytes * bytes => (so_cons so :: Ws.1, Ws.2))
                             <$> sfx_terms fc L m1 (wr_of so) true)
                  <$> filter (fun so => pipe_pairB L wc w (rd_of so)) (stage_outs fc L SMid))
  end.

Lemma sfx_terms_spec fc L m w wc W s :
  (W, s) ∈ sfx_terms fc L m w wc <-> sfx_term fc L m w wc W s.
Proof using.
  revert w wc W s. induction m as [| m IH]; intros w wc W s.
  - cbn [sfx_terms]. split; [intros H; by apply elem_of_nil in H |].
    intros H. remember 0 as z eqn:Hz in H. revert Hz. destruct H; intros Hz; discriminate Hz.
  - destruct m as [| m'].
    + cbn [sfx_terms]. split; [intros H; by apply elem_of_nil in H |].
      intros H. remember 1 as z eqn:Hz in H. revert Hz. destruct H; intros Hz; discriminate Hz.
    + cbn [sfx_terms]. rewrite elem_of_app, elem_of_list_join. split.
      * intros [H | (l & HWs & Hl)].
        -- apply elem_of_list_fmap in H as (so & Hq & Hso). injection Hq as -> ->.
           apply stt_here. apply stage_outs_spec. exact Hso.
        -- apply elem_of_list_fmap in Hl as (so & -> & Hso).
           apply elem_of_list_filter in Hso as [Hp Hso].
           apply elem_of_list_fmap in HWs as ([W' s'] & Hq & HWs'). injection Hq as -> ->.
           apply IH in HWs'. apply stage_outs_spec in Hso. cbn [fst snd].
           apply stt_next; assumption.
      * intros H. remember (S (S m')) as z eqn:Hz in H. revert Hz.
        destruct H as [m0 win wc0 so Hso | m0 win wc0 so W' s' Hso Hp Hr]; intros Hz;
          injection Hz as ->.
        -- left. apply elem_of_list_fmap. exists so.
           split; [reflexivity | apply stage_outs_spec; exact Hso].
        -- right.
           exists ((fun Ws : list bytes * bytes => (so_cons so :: Ws.1, Ws.2))
                     <$> sfx_terms fc L (S m') (wr_of so) true). split.
           ++ apply elem_of_list_fmap. exists (W', s'). split; [reflexivity |].
              apply IH. exact Hr.
           ++ apply elem_of_list_fmap. exists so. split; [reflexivity |].
              apply elem_of_list_filter. split; [exact Hp | apply stage_outs_spec; exact Hso].
Qed.

Definition line_terms (fc : bytes -> option bytes) (l : pline') : list (list bytes * bytes) :=
  match l with
  | LEcho' _ => []
  | LPipes p n =>
      (if decide (1 <= n)
       then (fun so => ([dg_fork_b], so_cons so)) <$> stage_outs fc (prod_content fc p) (SProd p)
       else [])
      ++ mjoin ((fun so => (fun Ws : list bytes * bytes => (so_cons so :: Ws.1, Ws.2))
                             <$> sfx_terms fc (prod_content fc p) n (wr_of so) (prod_cat p))
                  <$> stage_outs fc (prod_content fc p) (SProd p))
  end.

Lemma line_terms_spec fc l W s : (W, s) ∈ line_terms fc l <-> line_term fc l W s.
Proof using.
  destruct l as [ws | p n]; cbn [line_terms].
  - split; [intros H; by apply elem_of_nil in H |].
    intros H. remember (LEcho' ws) as l eqn:Hl. revert Hl. destruct H; intros Hl; discriminate Hl.
  - rewrite elem_of_app, elem_of_list_join. split.
    + intros [H | (l & HWs & Hl)].
      * destruct (decide (1 <= n)) as [Hn | Hn]; [| by apply elem_of_nil in H].
        apply elem_of_list_fmap in H as (so & Hq & Hso). injection Hq as -> ->.
        apply lt_here; [exact Hn | apply stage_outs_spec; exact Hso].
      * apply elem_of_list_fmap in Hl as (so & -> & Hso).
        apply elem_of_list_fmap in HWs as ([W' s'] & Hq & HWs'). injection Hq as -> ->.
        apply sfx_terms_spec in HWs'. apply stage_outs_spec in Hso. apply lt_next; assumption.
    + intros H. remember (LPipes p n) as l eqn:Hl. revert Hl.
      destruct H as [p0 n0 so Hn Hso | p0 n0 so W' s' Hso Hr]; intros Hl;
        injection Hl as -> ->.
      * left. rewrite decide_True by exact Hn. apply elem_of_list_fmap. exists so.
        split; [reflexivity | apply stage_outs_spec; exact Hso].
      * right.
        exists ((fun Ws : list bytes * bytes => (so_cons so :: Ws.1, Ws.2))
                  <$> sfx_terms fc (prod_content fc p) n (wr_of so) (prod_cat p)). split.
        -- apply elem_of_list_fmap. exists (W', s'). split; [reflexivity |].
           apply sfx_terms_spec. exact Hr.
        -- apply elem_of_list_fmap. exists so. split; [reflexivity | apply stage_outs_spec; exact Hso].
Qed.

(* ---- merges, the few facts the prefix test spends ---- *)

Lemma merge_all_cons_nil ss b : merge_all ss b -> merge_all ([] :: ss) b.
Proof using.
  induction 1 as [ss HF | ss i x s b Hi Hm IH].
  - apply ma_done. constructor; [reflexivity | exact HF].
  - apply (ma_take _ (S i) x s); [exact Hi | exact IH].
Qed.

Lemma merge_all_concat ss : merge_all ss (concat ss).
Proof using.
  induction ss as [| s ss IH]; [apply ma_done; constructor |].
  cbn [concat]. induction s as [| x s IHs]; [exact (merge_all_cons_nil _ _ IH) |].
  apply (ma_take _ 0 x s); [reflexivity | exact IHs].
Qed.

Lemma merge_all_nil_inv ss : merge_all ss [] -> Forall (fun s => s = []) ss.
Proof using.
  intros H. remember ([] : bytes) as b eqn:Hb.
  destruct H as [ss HF | ss i x s b Hi Hm]; [exact HF | discriminate Hb].
Qed.

Lemma merge_all_of_nils ss b : Forall (fun s => s = []) ss -> merge_all ss b -> b = [].
Proof using.
  intros HF Hm. destruct Hm as [ss HF' | ss i x s b Hi Hm]; [reflexivity |].
  exfalso. pose proof (Forall_lookup_1 _ _ _ _ HF Hi) as Hq. discriminate Hq.
Qed.

Lemma merge_all_2nil x : merge_all [x; []] x.
Proof using. apply merge2_shuf2, shuf2_nil_r. reflexivity. Qed.

Lemma forallb_nil_iff (W : list bytes) :
  forallb (fun w => bool_decide (w = [])) W = true <-> Forall (fun w => w = []) W.
Proof using.
  rewrite forallb_forall, Forall_forall. split.
  - intros H w Hw. apply (bool_decide_eq_true_1 (w = [])). apply H. by apply elem_of_list_In.
  - intros H w Hw. apply bool_decide_eq_true_2. apply H. by apply elem_of_list_In.
Qed.

(* THE PREFIX TEST: [b] is a prefix of a shuffle of (a merge of the waited
   streams [W], then [pr]) with a prefix of the stray's stream [s] *)
Fixpoint ptermb (W : list bytes) (pr s : bytes) (b : bytes) : bool :=
  match b with
  | [] => true
  | x :: b' =>
      existsb (fun W' => ptermb W' pr s b') (picks x W)
      || (forallb (fun w => bool_decide (w = [])) W
          && match pr with y :: pr' => bool_decide (y = x) && ptermb W pr' s b' | [] => false end)
      || match s with y :: s' => bool_decide (y = x) && ptermb W pr s' b' | [] => false end
  end.

Lemma ptermb_spec W pr s b :
  ptermb W pr s b = true <->
  exists Wm sp b', merge_all W Wm /\ sp `prefix_of` s /\ merge_all [Wm ++ pr; sp] b'
                   /\ b `prefix_of` b'.
Proof using.
  revert W pr s. induction b as [| x b IH]; intros W pr s; cbn [ptermb].
  - split; [intros _ | done].
    exists (concat W), [], (concat W ++ pr). split_and!.
    + apply merge_all_concat.
    + apply prefix_nil.
    + apply merge_all_2nil.
    + apply prefix_nil.
  - rewrite !orb_true_iff. split.
    + intros [[H | H] | H].
      * apply existsb_exists in H as (W' & Hin & H).
        apply elem_of_list_In, picks_spec in Hin as (i & t & Hi & ->).
        apply IH in H as (Wm & sp & c & HWm & Hsp & Hm & Hp).
        exists (x :: Wm), sp, (x :: c). split_and!.
        -- exact (ma_take _ i x t Wm Hi HWm).
        -- exact Hsp.
        -- apply (ma_take _ 0 x (Wm ++ pr)); [reflexivity | exact Hm].
        -- apply prefix_cons. exact Hp.
      * apply andb_true_iff in H as [HF H].
        destruct pr as [| y pr']; [discriminate H |].
        apply andb_true_iff in H as [Hy H]. apply bool_decide_eq_true in Hy as ->.
        apply IH in H as (Wm & sp & c & HWm & Hsp & Hm & Hp).
        apply forallb_nil_iff in HF.
        rewrite (merge_all_of_nils W Wm HF HWm) in Hm.
        exists [], sp, (x :: c). split_and!.
        -- apply ma_done. exact HF.
        -- exact Hsp.
        -- apply (ma_take _ 0 x pr'); [reflexivity | exact Hm].
        -- apply prefix_cons. exact Hp.
      * destruct s as [| y s']; [discriminate H |].
        apply andb_true_iff in H as [Hy H]. apply bool_decide_eq_true in Hy as ->.
        apply IH in H as (Wm & sp & c & HWm & Hsp & Hm & Hp).
        exists Wm, (x :: sp), (x :: c). split_and!.
        -- exact HWm.
        -- apply prefix_cons. exact Hsp.
        -- apply (ma_take _ 1 x sp); [reflexivity | exact Hm].
        -- apply prefix_cons. exact Hp.
    + intros (Wm & sp & b' & HWm & Hsp & Hm & Hp).
      destruct b' as [| x' c]; [apply prefix_nil_inv in Hp; discriminate Hp |].
      pose proof (prefix_cons_inv_1 _ _ _ _ Hp) as <-. apply prefix_cons_inv_2 in Hp.
      remember [Wm ++ pr; sp] as ss eqn:Hss. remember (x :: c) as bb eqn:Hbb.
      destruct Hm as [ss0 HF | ss0 i y t c0 Hi Hm]; [discriminate Hbb |].
      injection Hbb as -> ->. subst ss0.
      destruct i as [| [| i]]; cbn in Hi; [| | discriminate Hi].
      * destruct Wm as [| z Wm0].
        -- (* the prompt, every waited stream done *)
           cbn [app] in Hi. injection Hi as ->.
           left. right. apply andb_true_iff. split.
           ++ apply forallb_nil_iff. exact (merge_all_nil_inv W HWm).
           ++ change (bool_decide (x = x) && ptermb W t s b = true).
              rewrite bool_decide_eq_true_2; [| reflexivity]. cbn [andb].
              apply IH. exists [], sp, c. split_and!; [exact HWm | exact Hsp | exact Hm | exact Hp].
        -- (* a waited stream's byte *)
           cbn [app] in Hi. injection Hi as -> <-.
           remember (x :: Wm0) as ww eqn:Hww.
           destruct HWm as [W0 HF0 | W0 j z u Wm1 Hj HWm1]; [discriminate Hww |].
           injection Hww as -> ->.
           left. left. apply existsb_exists. exists (<[j := u]> W0). split.
           ++ apply elem_of_list_In, picks_spec. exists j, u. split; [exact Hj | reflexivity].
           ++ apply IH. exists Wm0, sp, c. split_and!; [exact HWm1 | exact Hsp | | exact Hp].
              exact Hm.
      * (* the stray's byte *)
        injection Hi as ->.
        destruct s as [| y s']; [apply prefix_nil_inv in Hsp; discriminate Hsp |].
        pose proof (prefix_cons_inv_1 _ _ _ _ Hsp) as <-. apply prefix_cons_inv_2 in Hsp.
        right. change (bool_decide (x = x) && ptermb W pr s' b = true).
        rewrite bool_decide_eq_true_2; [| reflexivity]. cbn [andb].
        apply IH. exists Wm, t, c. split_and!; [exact HWm | exact Hsp | exact Hm | exact Hp].
Qed.

(* THE DECIDER FOR THE [PLTerm] ARM: a prefix of a terminal block *)
Definition line_termb (fc : bytes -> option bytes) (l : pline') (b : bytes) : bool :=
  existsb (fun Ws : list bytes * bytes => ptermb Ws.1 u_prompt Ws.2 b) (line_terms fc l).

Lemma line_termb_spec fc l b :
  line_termb fc l b = true <-> exists b', line_term_blocks fc l b' /\ b `prefix_of` b'.
Proof using.
  unfold line_termb. rewrite existsb_exists. split.
  - intros ([W s] & Hin & H). cbn [fst snd] in H.
    apply elem_of_list_In, line_terms_spec in Hin.
    apply ptermb_spec in H as (Wm & sp & b' & HWm & Hsp & Hm & Hp).
    exists b'. split; [| exact Hp]. exists W, s, Wm, sp. split_and!; assumption.
  - intros (b' & (W & s & Wm & sp & Hlt & HWm & Hsp & Hm) & Hp).
    exists (W, s). split; [apply elem_of_list_In, line_terms_spec; exact Hlt |].
    cbn [fst snd]. apply ptermb_spec. exists Wm, sp, b'. split_and!; assumption.
Qed.

Global Instance line_blocks_dec fc l b : Decision (line_blocks fc l b).
Proof using.
  destruct (line_blocksb fc l b) eqn:H; [left; by apply line_blocksb_spec |].
  right. intros Hb. apply line_blocksb_spec in Hb. congruence.
Defined.

Global Instance plalt_ok_dec fc l a : Decision (plalt_ok fc l a).
Proof using.
  destruct a as [| b | b]; cbn [plalt_ok].
  - left. exact I.
  - apply _.
  - destruct (decide (b = [])) as [-> | Hne]; [right; intros [H _]; exact (H eq_refl) |].
    destruct (line_termb fc l b) eqn:H.
    + left. split; [exact Hne | apply line_termb_spec; exact H].
    + right. intros [_ Hb]. apply line_termb_spec in Hb. congruence.
Defined.

(* THE RANGE CONDITION OF [pipes_lm], DECIDED, at any content function
   and any admission *)
Global Instance pipes_lm_ok_dec fc adm s l a : Decision (lm_ok (pipes_lm fc adm) s l a).
Proof using. cbn [pipes_lm lm_ok]. apply _. Defined.

(* ===================================================================== *)
(*  2c.  THE HOOKS OF [pipes_lm] ([LineModelLinks.lm_hooks])              *)
(*                                                                        *)
(*  At every content function and every admission: state-freedom is      *)
(*  [~ PLTerm] (the state is [unit]), the panic is [PLPanic], the exec    *)
(*  failure is the round's first process's diagnostic [PipesDisc.pl_exfb] *)
(*  and the silent round [PLRun []] -- the three admissible at every line *)
(*  ([PipesDisc.plsafe]) -- and the range condition is decided above.     *)
(* ===================================================================== *)
Section pipes_hooks.
  Context (fc : bytes -> option bytes) (adm : pline' -> bool).
  Local Notation PM := (pipes_lm fc adm).

  Lemma phk_free_term (a : plalt) : negb (plterm a) = true -> plterm a = false.
  Proof using. destruct (plterm a); [discriminate | reflexivity]. Qed.

  Lemma phk_pan_ok s l : lm_ok PM s l (lm_dec PM (plalt_code PLPanic)).
  Proof using. cbn [pipes_lm lm_ok lm_dec]. rewrite plalt_of_code. left. left. reflexivity. Qed.

  Lemma phk_exf_ok s l : lm_ok PM s l (lm_dec PM (plalt_code (PLRun (pl_exfb l)))).
  Proof using.
    cbn [pipes_lm lm_ok lm_dec]. rewrite plalt_of_code. left. right. right. reflexivity.
  Qed.

  Lemma phk_noc_ok s l : lm_ok PM s l (lm_dec PM (plalt_code (PLRun []))).
  Proof using. cbn [pipes_lm lm_ok lm_dec]. rewrite plalt_of_code. left. right. left. reflexivity. Qed.

  Lemma phk_code_free a : negb (plterm (lm_dec PM (plalt_code a))) = negb (plterm a).
  Proof using. cbn [pipes_lm lm_dec]. by rewrite plalt_of_code. Qed.

  Lemma phk_code_panic a : lm_panic PM (lm_dec PM (plalt_code a)) = plpanic a.
  Proof using. cbn [pipes_lm lm_panic lm_dec]. by rewrite plalt_of_code. Qed.

  Lemma phk_code_cont s l a : lm_cont PM s l (lm_dec PM (plalt_code a)) = plcont a.
  Proof using. cbn [pipes_lm lm_cont lm_dec]. by rewrite plalt_of_code. Qed.

  Lemma phk_cont_prompt s l a :
    lm_ok PM s l a -> lm_panic PM a = false -> lm_term PM a = false ->
    exists u, lm_cont PM s l a = u ++ u_prompt.
  Proof using.
    intros _ Hp Ht. destruct a as [| b | b]; [discriminate Hp | | discriminate Ht].
    exists b. reflexivity.
  Qed.

  Lemma phk_cont_nonnil s l a :
    lm_ok PM s l a \/ a = lm_dec PM 0 -> lm_cont PM s l a <> [].
  Proof using.
    intros Ha. cbn [pipes_lm lm_cont]. destruct a as [| b | b]; cbn [plcont].
    - intros Hq. apply (f_equal length) in Hq. rewrite lb_panic_len in Hq. discriminate Hq.
    - intros Hq. apply (f_equal length) in Hq. rewrite length_app, ll_prompt_len in Hq.
      cbn [length] in Hq. lia.
    - destruct Ha as [Hok | Hq].
      + apply (pipes_lm_ok_term fc adm s) in Hok as [_ [Hne _]]. exact Hne.
      + exfalso. cbn [pipes_lm lm_dec] in Hq. unfold plalt_of in Hq.
        rewrite decide_True in Hq; [discriminate Hq | reflexivity].
  Qed.

  Definition pipes_hooks : lm_hooks PM :=
    MkLMH PM (fun a => negb (plterm a)) tt
      (fun _ => plalt_code PLPanic) (fun l => plalt_code (PLRun (pl_exfb l)))
      (fun l => pl_exfb l ++ u_prompt) (fun _ => plalt_code (PLRun []))
      (pipes_lm_ok_dec fc adm)
      (fun _ _ _ _ _ => eq_refl) phk_free_term (fun _ _ _ _ _ H => H)
      phk_pan_ok (fun _ => eq_trans (phk_code_free PLPanic) eq_refl)
      (fun _ => eq_trans (phk_code_panic PLPanic) eq_refl)
      phk_exf_ok (fun l => eq_trans (phk_code_free (PLRun (pl_exfb l))) eq_refl)
      (fun l => eq_trans (phk_code_panic (PLRun (pl_exfb l))) eq_refl)
      (fun s l => phk_code_cont s l (PLRun (pl_exfb l)))
      phk_noc_ok (fun _ => eq_trans (phk_code_free (PLRun [])) eq_refl)
      (fun _ => eq_trans (phk_code_panic (PLRun [])) eq_refl)
      (fun s l => phk_code_cont s l (PLRun []))
      phk_cont_prompt phk_cont_nonnil.
End pipes_hooks.

(* ===================================================================== *)
(*  3.  DEMOS                                                             *)
(* ===================================================================== *)

Definition fc0 : bytes -> option bytes := fun _ => None.
Definition nlb' : bytes := [wl_nl].

(* cat f as the producer, at a content function that has [f] *)
Definition fc1 : bytes -> option bytes :=
  fun f => if decide (f = sb "f") then Some (sb "foo bar" ++ nlb') else None.

Example demo_catf_cat_cat :
  line_blocks fc1 (LPipes (PrCatF (sb "f")) 2) (sb "foo bar" ++ nlb').
Proof using. apply line_blocksb_spec. vm_compute. reflexivity. Qed.
