(* ===================================================================== *)
(* UnionDisc.v -- THE UNION MODEL (cut C9b; design: claude-notes/design/ *)
(* union.md section 1, with the review amendments B2 and S3).  Pure.     *)
(*                                                                        *)
(*  One line model [ulm adm] for every line shape the shell reads:        *)
(*  [echo ws], [echo ws > f], [cat f] (the file model's lines and          *)
(*  alternatives, [UR]) and [p | cat^n] for a producer [p] -- echo or      *)
(*  [cat f] -- (the N-stage pipeline model's, [UP]).  The state is the     *)
(*  file's ([fstate]); a pipeline round reads it through                  *)
(*  [FileDisc.files_of] (so [cat f | cat] prints the round's content) and *)
(*  leaves it alone.                                                      *)
(*                                                                        *)
(*  THE CROSS CASES ARE [False] (amendment B2).  [FileDisc.ralt_ok]'s     *)
(*  dead [LPipe] arm admits [LCat]'s five alternatives, [RCRan] (f's     *)
(*  content) among them; reading it at a pipeline would admit the file's *)
(*  content as the output of [echo hi | cat].  So a pipeline line admits  *)
(*  no [UR] alternative and a file line no [UP] one.                     *)
(*                                                                        *)
(*  THE ADMISSION [adm] IS A PARAMETER.  [adm_u_f] admits every echo      *)
(*  pipeline and every [cat f | ..] pipeline at the model's one file name *)
(*  [fname_f].  WHETHER OTHER FILE NAMES ARE ADMITTED IS AN OPEN OWNER    *)
(*  RULING (review S4): the file model has one name, so [cat g | cat]     *)
(*  at [g <> f] would read a file the model does not describe (its        *)
(*  content function answers [None] there, which is honest -- the open    *)
(*  fails -- only if no other file exists).                               *)
(*                                                                        *)
(*  THE LAWS hold at EVERY admission ([ulm_laws]): the pipeline half is   *)
(*  [PipesDisc.pipes_lm_laws_fc] at the round's content function, whose   *)
(*  only premise ([fc_ok]) is the file state's own shape                  *)
(*  ([fstate_ok]).  No [adm_ok] is needed and [adm_u_f] does not satisfy  *)
(*  it: [echo fork > f] then [cat f | cat] prints the panic line.         *)
(*                                                                        *)
(*  THE HOOKS DO NOT HOLD AS DESIGNED (section 4).  The exec failure of   *)
(*  an echo pipeline's first process prints [exec echo failed], so its   *)
(*  alternative is [UP (PLRun dg_execL)], and [lmh_exf_free] needs it     *)
(*  FREE.  But at a [cat f] pipeline the same alternative is admissible   *)
(*  exactly when the file holds those bytes ([UnionDiscDec.               *)
(*  demo_execL_state_dep]), so no free set containing it satisfies        *)
(*  [lmh_free_ok], whose quantifier ranges over every line.  Everything   *)
(*  but that one field is proved below at the free set of the             *)
(*  state-independent alternatives ([ufree], [ufree_ok]).                 *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list countable bitvector.definitions.
Require Import RiscvLang ObsTrace.
Require Import LineWords EchoDisc LineBytes LineModel LineModelLinks.
Require Import StringBytes ProgTree ProgTreePipes PipesPair PipesDisc.
Require PipeDisc.
Require Import PipesUline.
Require Import FileState FileDisc FileOutPure FileHooks.
From stdpp Require Import list.

Local Open Scope nat_scope.

(* ===================================================================== *)
(*  1.  THE ALTERNATIVES                                                  *)
(* ===================================================================== *)

(* a file line's alternative, or a pipeline's *)
Inductive ualt :=
  | UR (a : ralt)
  | UP (a : plalt).

Global Instance ualt_eq_dec : EqDecision ualt.
Proof using. solve_decision. Defined.

(* THE CODE: the two injective codes interleaved.  Like [plalt_code] it is
   built, never computed. *)
Definition ualt_code (a : ualt) : nat :=
  match a with
  | UR r => 2 * ralt_enc r
  | UP x => 2 * plalt_code x + 1
  end.

Definition ualt_dec (n : nat) : ualt :=
  if decide (n mod 2 = 0) then UR (ralt_dec (n / 2)) else UP (plalt_of (n / 2)).

Lemma ualt_dec_R (k : nat) : ualt_dec (2 * k) = UR (ralt_dec k).
Proof using.
  unfold ualt_dec. rewrite decide_True; [| rewrite Nat.mul_comm, Nat.Div0.mod_mul; reflexivity].
  rewrite Nat.mul_comm, Nat.div_mul; [reflexivity | lia].
Qed.

Lemma ualt_dec_P (k : nat) : ualt_dec (2 * k + 1) = UP (plalt_of k).
Proof using.
  unfold ualt_dec.
  assert (Hm : (2 * k + 1) mod 2 = 1).
  { rewrite Nat.add_comm, Nat.mul_comm, Nat.Div0.mod_add. reflexivity. }
  assert (Hd : (2 * k + 1) / 2 = k).
  { rewrite Nat.add_comm, Nat.mul_comm, Nat.div_add; [reflexivity | lia]. }
  rewrite decide_False; [| lia]. rewrite Hd. reflexivity.
Qed.

Lemma ualt_dec_0 : ualt_dec 0 = UR (ralt_dec 0).
Proof using. exact (ualt_dec_R 0). Qed.

Lemma ualt_dec_code (a : ualt) : ualt_dec (ualt_code a) = a.
Proof using.
  destruct a as [r | x]; cbn [ualt_code].
  - by rewrite ualt_dec_R, ralt_dec_enc.
  - by rewrite ualt_dec_P, plalt_of_code.
Qed.

Lemma ualt_code_inj (a b : ualt) : ualt_code a = ualt_code b -> a = b.
Proof using. intros H. by rewrite <- (ualt_dec_code a), <- (ualt_dec_code b), H. Qed.

Definition upanic (a : ualt) : bool :=
  match a with UR r => ralt_panic r | UP x => plpanic x end.
Definition uterm (a : ualt) : bool :=
  match a with UR _ => false | UP x => plterm x end.

(* the console continuation: the file's, at the round's state, or the
   pipeline's (which names its whole block) *)
Definition ucont (s : fstate) (l : uline) (a : ualt) : list (bv 8) :=
  match a with UR r => cont s l r | UP x => plcont x end.

(* the step: the file's; a pipeline leaves [f] alone *)
Definition ustep (s : fstate) (l : uline) (a : ualt) : fstate :=
  match a with UR r => fsm s l r | UP _ => s end.

(* THE RANGE CONDITION at the round's state.  The cross cases are [False]
   (amendment B2); at a pipeline the shell's own three ([plsafe]) at every
   state, or an admitted line's run at the content [s] gives [f]. *)
Definition uok (adm : pline' -> bool) (s : fstate) (l : uline) (a : ualt) : Prop :=
  match l, a with
  | LPipe p n, UP x =>
      plsafe (LPipes p n) x
      \/ (adm (LPipes p n) = true /\ plalt_ok (files_of s) (LPipes p n) x)
  | LPipe _ _, UR _ => False
  | _, UR r => ralt_ok l r
  | _, UP _ => False
  end.

(* ===================================================================== *)
(*  2.  THE LINES: the file's parser, then the pipeline's                 *)
(* ===================================================================== *)

Definition uline_of_u (b : list (bv 8)) : uline :=
  match parse_line b with
  | Some l => l
  | None => match pl_parse b with Some (LPipes p n) => LPipe p n | _ => inhabitant end
  end.

(* a body the admission lets through as a pipeline *)
Definition upipe_ok (adm : pline' -> bool) (b : list (bv 8)) : Prop :=
  match pl_parse b with Some (LPipes p n) => adm (LPipes p n) = true | _ => False end.

Global Instance upipe_ok_dec adm b : Decision (upipe_ok adm b).
Proof using. unfold upipe_ok. destruct (pl_parse b) as [[ws | p n] |]; apply _. Defined.

Definition ubody_ok (adm : pline' -> bool) (b : list (bv 8)) : Prop :=
  fbody_ok b \/ upipe_ok adm b.

Global Instance ubody_ok_dec adm b : Decision (ubody_ok adm b).
Proof using. unfold ubody_ok. apply _. Defined.

Definition ubyte (b : bv 8) : Prop := fbody_byte b \/ b = fd_bar.

Global Instance ubyte_dec b : Decision (ubyte b).
Proof using. unfold ubyte. apply _. Defined.

(* the coverage-ending outputs: a prefix of an admitted pipeline's
   terminal block at SOME admissible state (terminal runs carry no
   content, so the state is immaterial) *)
Definition umerge (adm : pline' -> bool) (u : list (bv 8)) : Prop :=
  exists s, fstate_ok s /\ pl_merge (files_of s) adm u.

(* ===================================================================== *)
(*  3.  THE MODEL AND ITS LAWS                                            *)
(* ===================================================================== *)

Definition ulm (adm : pline' -> bool) : lmodel :=
  MkLM fstate uline uline_of_u ualt ualt_dec upanic ucont ustep (uok adm)
       (ubody_ok adm) ubyte uline_ok fstate_ok uterm (umerge adm).

(* THE ADMISSION the union application instantiates: every echo pipeline
   and every [cat f | ..] at the model's file name.  An echo line alone is
   the file's [LEcho], so [LEcho'] is not admitted here. *)
Definition adm_u_f (l : pline') : bool :=
  match l with
  | LEcho' _ => false
  | LPipes (PrEcho _) _ => true
  | LPipes (PrCatF g) _ => bool_decide (g = fname_f)
  end.

Definition ulmU : lmodel := ulm adm_u_f.

(* ---- the pieces ---- *)

(* the round's content function has a word line's shape *)
Lemma files_of_fc_ok (s : fstate) : fstate_ok s -> fc_ok (files_of s).
Proof using.
  intros Hs g c Hg. apply files_of_some in Hg. subst s. cbn [fstate_ok] in Hs.
  split; [exact (fcont_ok_nodollar c Hs) | exact (fcont_ok_nl c Hs)].
Qed.

Lemma uline_of_u_ok (adm : pline' -> bool) (b : list (bv 8)) :
  ubody_ok adm b -> uline_ok (uline_of_u b).
Proof using.
  unfold uline_of_u. destruct (parse_line b) as [l |] eqn:Hp.
  { intros _. exact (parse_line_ok b l Hp). }
  intros [[l Hl] | Hpipe]; [rewrite Hp in Hl; discriminate Hl |].
  revert Hpipe. unfold upipe_ok.
  destruct (pl_parse b) as [[ws | p n] |] eqn:Hq; intros Hpipe; try contradiction.
  destruct (pl_parse_some b _ Hq) as [Hok _].
  exact (uline_ok_of_pl_all (LPipes p n) Hok).
Qed.

(* a run proves its line has a cat *)
Lemma sfx_run_pos fc L m w wc ss : sfx_run fc L m w wc ss -> 1 <= m.
Proof using. destruct 1; lia. Qed.

Lemma line_blocks_pos fc p n b : line_blocks fc (LPipes p n) b -> 1 <= n.
Proof using.
  intros (ss & Hr & _). remember (LPipes p n) as l eqn:Hl.
  destruct Hr as [ws | ws | ws | p' n' Hn | p' n' so ss' Hso Hsr]; try discriminate Hl;
    injection Hl as -> ->; [exact Hn | exact (sfx_run_pos _ _ _ _ _ _ Hsr)].
Qed.

Lemma sfx_term_pos fc L m w wc W t : sfx_term fc L m w wc W t -> 1 <= m.
Proof using. destruct 1; lia. Qed.

Lemma line_term_pos fc p n W t : line_term fc (LPipes p n) W t -> 1 <= n.
Proof using.
  intros H. remember (LPipes p n) as l eqn:Hl.
  destruct H as [p' n' so Hn Hso | p' n' so W' t' Hso Hst];
    injection Hl as -> ->; [exact Hn | exact (sfx_term_pos _ _ _ _ _ _ _ Hst)].
Qed.

(* A TERMINAL ALTERNATIVE AT EVERY CONTENT: the fork of the node below
   the producer fails after the producer was forked, and the producer's
   exec fails -- [lt_here] and [so_exec], whatever [f] holds *)
Lemma plterm_fork_ok fc p n :
  1 <= n -> plalt_ok fc (LPipes p n) (PLTerm dg_fork_b).
Proof using.
  intros Hn. split.
  { intros H. apply (f_equal length) in H. unfold dg_fork_b in H.
    rewrite wl_line_length in H. cbn [length] in H. lia. }
  exists (dg_fork_b ++ u_prompt). split; [| by exists u_prompt].
  exists [dg_fork_b], (st_dg_exec (SProd p)), dg_fork_b, []. split_and!.
  - exact (lt_here fc p n (MkSO (st_dg_exec (SProd p)) (st_rd_dead (SProd p))
                             (st_wr_dead (SProd p))) Hn (so_exec _ _ _)).
  - apply merge_all_one. reflexivity.
  - apply prefix_nil.
  - exact (merge_all_nils (dg_fork_b ++ u_prompt) 1).
Qed.

Section laws.
  Context (adm : pline' -> bool).

  Lemma ulm_st_step s l a :
    fstate_ok s -> uline_ok l -> uok adm s l a -> fstate_ok (ustep s l a).
  Proof using.
    intros Hs Hl Ha. destruct a as [r | x]; cbn [ustep]; [| exact Hs].
    destruct l as [ws | ws | | p n]; cbn [uok] in Ha;
      [exact (fstate_ok_fsm s _ r Hs Hl Ha) | exact (fstate_ok_fsm s _ r Hs Hl Ha)
      | exact (fstate_ok_fsm s _ r Hs Hl Ha) | contradiction].
  Qed.

  Lemma ulm_cont_panic s l a : upanic a = true -> ucont s l a = alt_panic.
  Proof using.
    destruct a as [r | [| b | b]]; cbn [upanic ucont]; intros H.
    - exact (cont_panic s l r H).
    - reflexivity.
    - discriminate H.
    - discriminate H.
  Qed.

  Lemma ulm_term_nopanic a : uterm a = true -> upanic a = false.
  Proof using.
    destruct a as [r | [| b | b]]; cbn; intros H; first [discriminate H | reflexivity].
  Qed.

  Lemma ulm_term_merge s l a :
    fstate_ok s -> uok adm s l a -> uterm a = true -> umerge adm (ucont s l a).
  Proof using.
    intros Hs Hok Ht. destruct a as [r | [| b | b]]; try discriminate Ht.
    destruct l as [ws | ws | | p n]; cbn [uok] in Hok; try contradiction.
    destruct Hok as [Hsafe | [Ha Hok]].
    { exfalso. destruct Hsafe as [H | [H | H]]; discriminate H. }
    exists s. split; [exact Hs |]. exists (LPipes p n), b. split_and!; [exact Ha | exact Hok |].
    reflexivity.
  Qed.

  Lemma ulm_merge_prefix u' u : u' `prefix_of` u -> umerge adm u -> umerge adm u'.
  Proof using.
    intros Hp (s & Hs & l & b & Ha & Hok & Hu). exists s. split; [exact Hs |].
    exists l, b. split_and!; [exact Ha | exact Hok | etrans; [exact Hp | exact Hu]].
  Qed.

  Lemma ulm_cont_shape s l a :
    fstate_ok s -> uline_ok l -> uok adm s l a -> upanic a = false -> uterm a = false ->
    exists u, ucont s l a = u ++ u_prompt
              /\ Forall nodollar u
              /\ (forall Y ps W,
                    Forall (fun x => x < length pro_alts) ps ->
                    lm_below_panic u Y ps W -> u = alt_panic).
  Proof using.
    intros Hs Hl Hok Hp Ht. destruct a as [r | x].
    - (* a file alternative at a file line: the file model's law *)
      assert (Hr : ralt_ok l r).
      { destruct l as [ws | ws | | p n]; cbn [uok] in Hok; [exact Hok | exact Hok | exact Hok | contradiction]. }
      exact (lml_cont_shape file_lm_laws s l r Hs Hl Hr Hp eq_refl).
    - (* a pipeline alternative at a pipeline: the pipeline model's law at
         the round's content function *)
      destruct l as [ws | ws | | p n]; cbn [uok] in Hok; try contradiction.
      exact (lml_cont_shape (pipes_lm_laws_fc (files_of s) adm (files_of_fc_ok s Hs))
               tt (LPipes p n) x I (pl_ok_of_uline p n Hl) Hok Hp Ht).
  Qed.

  (* a terminal alternative at one state has one at every state: the
     producer's exec failure below a failed fork ([plterm_fork_ok]) *)
  Lemma ulm_term_st s l c :
    uok adm s l c -> uterm c = true ->
    forall s', exists c', uok adm s' l c' /\ uterm c' = true.
  Proof using.
    intros Hok Ht s'. destruct c as [r | [| b | b]]; try discriminate Ht.
    destruct l as [ws | ws | | p n]; cbn [uok] in Hok; try contradiction.
    destruct Hok as [Hsafe | [Ha (_ & b' & (W & t & Wm & sp & Hlt & _) & _)]].
    { exfalso. destruct Hsafe as [H | [H | H]]; discriminate H. }
    exists (UP (PLTerm dg_fork_b)). split; [| reflexivity].
    cbn [uok]. right. split; [exact Ha |].
    exact (plterm_fork_ok _ p n (line_term_pos _ _ _ _ _ Hlt)).
  Qed.

  Theorem ulm_laws : lm_laws (ulm adm).
  Proof using.
    constructor; cbn [ulm lm_ok lm_cont lm_merge lm_panic lm_term lm_line_ok lm_body_ok
                      lm_of lm_st_ok lm_step].
    - exact (uline_of_u_ok adm).
    - exact ulm_st_step.
    - exact ulm_cont_panic.
    - exact ulm_term_nopanic.
    - exact ulm_term_merge.
    - exact ulm_merge_prefix.
    - exact ulm_cont_shape.
    - exact ulm_term_st.
  Qed.

  Theorem ulm_byte_laws : lm_byte_laws (ulm adm).
  Proof using.
    constructor; cbn [ulm lm_body_ok lm_body_byte lm_panic lm_dec].
    - intros b [Hb | Hb].
      + eapply Forall_impl; [exact (fbody_ok_bytes b Hb) |]. intros x Hx. by left.
      + revert Hb. unfold upipe_ok.
        destruct (pl_parse b) as [[ws | p n] |] eqn:Hq; intros Hb; try contradiction.
        destruct (pl_parse_some b _ Hq) as [Hok ->].
        eapply Forall_impl; [exact (pl_body_bytes _ Hok) |].
        intros x [Hx | Hx]; [left; left; exact Hx | right; exact Hx].
    - intros b [Hb | Hb]; [exact (fbody_ok_short b Hb) |].
      revert Hb. unfold upipe_ok.
      destruct (pl_parse b) as [[ws | p n] |] eqn:Hq; intros Hb; try contradiction.
      destruct (pl_parse_some b _ Hq) as [Hok ->]. exact (pl_body_short _ Hok).
    - intros b [Hb | ->].
      + exact (lmb_byte_printable file_lm_byte_laws b Hb).
      + assert (Hbar : bv_unsigned fd_bar = 124%Z) by (vm_compute; reflexivity).
        rewrite Hbar. lia.
    - rewrite ualt_dec_0. exact (lmb_dec0_nopanic file_lm_byte_laws).
  Qed.
End laws.

Corollary ulmU_laws : lm_laws ulmU.
Proof using. exact (ulm_laws adm_u_f). Qed.

(* ===================================================================== *)
(*  4.  THE HOOKS, AND WHERE THEY STOP                                    *)
(*                                                                        *)
(*  [lmh_free] is a function of the ALTERNATIVE alone and [lmh_free_ok]   *)
(*  quantifies over every line.  At [UR] the file's [fstate_free] is free *)
(*  (the file's range condition reads no state).  At [UP] the state-      *)
(*  independent alternatives are the panic, the silent round and          *)
(*  [exec cat failed] -- a cat stage's exec failure is a block of EVERY   *)
(*  pipeline at every content ([blocks_execR]) -- and nothing else: a     *)
(*  [PLRun] block is otherwise read at the round's content, and a         *)
(*  [PLTerm] is never free.                                               *)
(*                                                                        *)
(*  THE ONE FIELD THAT FAILS is [lmh_exf_free] at an echo pipeline: its   *)
(*  exec alternative is [UP (PLRun dg_execL)], which a [cat f] pipeline   *)
(*  admits exactly at the content [exec echo failed] -- see              *)
(*  [uexf_echo_not_free] and [UnionDiscDec.demo_execL_state_dep].  The    *)
(*  record [lm_hooks (ulm adm)] is therefore NOT built here.              *)
(* ===================================================================== *)

Definition ufree (a : ualt) : bool :=
  match a with
  | UR r => fstate_free r
  | UP PLPanic => true
  | UP (PLRun b) => bool_decide (b = [] \/ b = PipeDisc.dg_execR)
  | UP (PLTerm _) => false
  end.

(* [exec cat failed] below every producer, at every content: the first
   cat stage's exec fails, every other stage exits silently *)
Lemma merge_all_cons_nil' ss b : merge_all ss b -> merge_all ([] :: ss) b.
Proof using.
  induction 1 as [ss HF | ss i x t b Hi Hm IH].
  - apply ma_done. constructor; [reflexivity | exact HF].
  - apply (ma_take _ (S i) x t); [exact Hi | exact IH].
Qed.

Lemma blocks_execR fc p n : 1 <= n -> line_blocks fc (LPipes p n) PipeDisc.dg_execR.
Proof using.
  intros Hn. destruct n as [| [| m]]; [lia | |].
  - exists [[]; PipeDisc.dg_execR]. split.
    + apply (lr_node fc p 1 (MkSO [] (st_rd_dead (SProd p)) (st_wr_dead (SProd p))));
        [apply so_silent |].
      apply (sr_last fc _ _ (prod_cat p)
               (MkSO (st_dg_exec SLast) (st_rd_dead SLast) (st_wr_dead SLast)));
        [apply so_exec | cbn; exact I].
    + apply merge2_shuf2, shuf2_nil_l. reflexivity.
  - exists ([] :: PipeDisc.dg_execR :: replicate (S m) []). split.
    + apply (lr_node fc p (S (S m)) (MkSO [] (st_rd_dead (SProd p)) (st_wr_dead (SProd p))));
        [apply so_silent |].
      apply (sr_node fc _ m _ (prod_cat p)
               (MkSO (st_dg_exec SMid) (st_rd_dead SMid) (st_wr_dead SMid)));
        [apply so_exec | cbn; exact I |].
      exact (sfx_run_silent _ _ (S m) _ _ ltac:(lia)).
    + apply merge_all_cons_nil'. exact (merge_all_nils _ (S m)).
Qed.

Section hooks.
  Context (adm : pline' -> bool).

  Lemma ufree_cont s s' l a : ufree a = true -> ucont s l a = ucont s' l a.
  Proof using.
    destruct a as [r | x]; cbn [ufree ucont]; [exact (cont_state_free s s' l r) |].
    intros _. reflexivity.
  Qed.

  Lemma ufree_term a : ufree a = true -> uterm a = false.
  Proof using. destruct a as [r | [| b | b]]; cbn; done. Qed.

  (* THE STATE-INDEPENDENCE of the free alternatives *)
  Lemma ufree_ok s s' l a : ufree a = true -> uok adm s l a -> uok adm s' l a.
  Proof using.
    intros Hfr Hok. destruct a as [r | x].
    - destruct l; exact Hok.
    - destruct l as [ws | ws | | p n]; cbn [uok] in Hok |- *; try contradiction.
      destruct Hok as [Hsafe | [Ha Hb]]; [left; exact Hsafe |].
      destruct x as [| b | b]; cbn [ufree] in Hfr; [left; left; reflexivity | | discriminate Hfr].
      apply bool_decide_eq_true in Hfr as [-> | ->]; [left; right; left; reflexivity |].
      right. split; [exact Ha |].
      exact (blocks_execR _ p n (line_blocks_pos _ _ _ _ Hb)).
  Qed.

  (* the shell's own three, per line: the file's at a file line, the
     pipeline's ([plsafe]) at a pipeline *)
  Definition upan (l : uline) : nat :=
    match l with LPipe _ _ => 2 * plalt_code PLPanic + 1 | _ => 2 * fpan_of l end.
  Definition uexf (l : uline) : nat :=
    match l with
    | LPipe p n => 2 * plalt_code (PLRun (pl_exfb (LPipes p n))) + 1
    | _ => 2 * fexf_of l
    end.
  Definition uexfb (l : uline) : list (bv 8) :=
    match l with LPipe p n => pl_exfb (LPipes p n) ++ u_prompt | _ => fexfb l end.
  Definition unoc (l : uline) : nat :=
    match l with LPipe _ _ => 2 * plalt_code (PLRun []) + 1 | _ => 2 * fnoc_of l end.

  Lemma upan_ok s l : uok adm s l (ualt_dec (upan l)).
  Proof using.
    destruct l as [ws | ws | | p n]; cbn [upan];
      [rewrite ualt_dec_R; exact (fpan_of_ok _) | rewrite ualt_dec_R; exact (fpan_of_ok _)
      | rewrite ualt_dec_R; exact (fpan_of_ok _) |].
    rewrite ualt_dec_P, plalt_of_code. left. left. reflexivity.
  Qed.

  Lemma upan_free l : ufree (ualt_dec (upan l)) = true.
  Proof using.
    destruct l as [ws | ws | | p n]; cbn [upan];
      [rewrite ualt_dec_R; exact (fpan_of_free _) | rewrite ualt_dec_R; exact (fpan_of_free _)
      | rewrite ualt_dec_R; exact (fpan_of_free _) |].
    rewrite ualt_dec_P, plalt_of_code. reflexivity.
  Qed.

  Lemma upan_panic l : upanic (ualt_dec (upan l)) = true.
  Proof using.
    destruct l as [ws | ws | | p n]; cbn [upan];
      [rewrite ualt_dec_R; exact (fpan_of_panic _) | rewrite ualt_dec_R; exact (fpan_of_panic _)
      | rewrite ualt_dec_R; exact (fpan_of_panic _) |].
    rewrite ualt_dec_P, plalt_of_code. reflexivity.
  Qed.

  Lemma uexf_ok s l : uok adm s l (ualt_dec (uexf l)).
  Proof using.
    destruct l as [ws | ws | | p n]; cbn [uexf];
      [rewrite ualt_dec_R; exact (fexf_of_ok _) | rewrite ualt_dec_R; exact (fexf_of_ok _)
      | rewrite ualt_dec_R; exact (fexf_of_ok _) |].
    rewrite ualt_dec_P, plalt_of_code. left. right. right. reflexivity.
  Qed.

  Lemma uexf_nopanic l : upanic (ualt_dec (uexf l)) = false.
  Proof using.
    destruct l as [ws | ws | | p n]; cbn [uexf];
      [rewrite ualt_dec_R; exact (fexf_of_nopanic _) | rewrite ualt_dec_R; exact (fexf_of_nopanic _)
      | rewrite ualt_dec_R; exact (fexf_of_nopanic _) |].
    rewrite ualt_dec_P, plalt_of_code. reflexivity.
  Qed.

  Lemma uexf_cont s l : ucont s l (ualt_dec (uexf l)) = uexfb l.
  Proof using.
    destruct l as [ws | ws | | p n]; cbn [uexf uexfb];
      [rewrite ualt_dec_R; exact (cont_fexf _ _) | rewrite ualt_dec_R; exact (cont_fexf _ _)
      | rewrite ualt_dec_R; exact (cont_fexf _ _) |].
    rewrite ualt_dec_P, plalt_of_code. reflexivity.
  Qed.

  (* THE OBSTRUCTION: at an echo pipeline the exec alternative is not
     state-independent, so it cannot be counted free *)
  Lemma uexf_echo_not_free ws n : ufree (ualt_dec (uexf (LPipe (PrEcho ws) n))) = false.
  Proof using.
    cbn [uexf]. rewrite ualt_dec_P, plalt_of_code. cbn [ufree pl_exfb st_dg_exec].
    apply bool_decide_eq_false. intros [H | H]; apply (f_equal length) in H;
      vm_compute in H; discriminate H.
  Qed.

  (* ...and where the exec alternative IS free: a [cat f] pipeline's is
     [exec cat failed], and every file line's is the file's *)
  Lemma uexf_catf_free f n : ufree (ualt_dec (uexf (LPipe (PrCatF f) n))) = true.
  Proof using.
    cbn [uexf]. rewrite ualt_dec_P, plalt_of_code. cbn [ufree pl_exfb st_dg_exec].
    apply bool_decide_eq_true. by right.
  Qed.

  Lemma unoc_ok s l : uok adm s l (ualt_dec (unoc l)).
  Proof using.
    destruct l as [ws | ws | | p n]; cbn [unoc];
      [rewrite ualt_dec_R; exact (fnoc_of_ok _) | rewrite ualt_dec_R; exact (fnoc_of_ok _)
      | rewrite ualt_dec_R; exact (fnoc_of_ok _) |].
    rewrite ualt_dec_P, plalt_of_code. left. right. left. reflexivity.
  Qed.

  Lemma unoc_free l : ufree (ualt_dec (unoc l)) = true.
  Proof using.
    destruct l as [ws | ws | | p n]; cbn [unoc];
      [rewrite ualt_dec_R; exact (fnoc_of_free _) | rewrite ualt_dec_R; exact (fnoc_of_free _)
      | rewrite ualt_dec_R; exact (fnoc_of_free _) |].
    rewrite ualt_dec_P, plalt_of_code. cbn [ufree]. apply bool_decide_eq_true. by left.
  Qed.

  Lemma unoc_nopanic l : upanic (ualt_dec (unoc l)) = false.
  Proof using.
    destruct l as [ws | ws | | p n]; cbn [unoc];
      [rewrite ualt_dec_R; exact (fnoc_of_nopanic _) | rewrite ualt_dec_R; exact (fnoc_of_nopanic _)
      | rewrite ualt_dec_R; exact (fnoc_of_nopanic _) |].
    rewrite ualt_dec_P, plalt_of_code. reflexivity.
  Qed.

  Lemma unoc_cont s l : ucont s l (ualt_dec (unoc l)) = u_prompt.
  Proof using.
    destruct l as [ws | ws | | p n]; cbn [unoc];
      [rewrite ualt_dec_R; exact (cont_fnoc _ _) | rewrite ualt_dec_R; exact (cont_fnoc _ _)
      | rewrite ualt_dec_R; exact (cont_fnoc _ _) |].
    rewrite ualt_dec_P, plalt_of_code. reflexivity.
  Qed.

  Lemma ucont_prompt s l a :
    uok adm s l a -> upanic a = false -> uterm a = false ->
    exists u, ucont s l a = u ++ u_prompt.
  Proof using.
    intros Hok Hp Ht. destruct a as [r | [| b | b]]; cbn [ucont];
      try discriminate Hp; try discriminate Ht.
    - assert (Hr : ralt_ok l r).
      { destruct l as [ws | ws | | p n]; cbn [uok] in Hok; [exact Hok | exact Hok | exact Hok | contradiction]. }
      exact (cont_prompt s l r Hr Hp).
    - exists b. reflexivity.
  Qed.

  Lemma ucont_nonnil s l a : uok adm s l a \/ a = ualt_dec 0 -> ucont s l a <> [].
  Proof using.
    intros Ha. destruct a as [r | [| b | b]]; cbn [ucont plcont].
    - apply (cont_nonnil_dec s l r). destruct Ha as [Hok | Hq].
      + left. destruct l as [ws | ws | | p n]; cbn [uok] in Hok; [exact Hok | exact Hok | exact Hok | contradiction].
      + right. rewrite ualt_dec_0 in Hq. injection Hq as ->. reflexivity.
    - intros Hq. apply (f_equal length) in Hq. rewrite lb_panic_len in Hq. discriminate Hq.
    - intros Hq. apply (f_equal length) in Hq. rewrite length_app, ll_prompt_len in Hq.
      cbn [length] in Hq. lia.
    - destruct Ha as [Hok | Hq].
      + destruct l as [ws | ws | | p n]; cbn [uok] in Hok; try contradiction.
        destruct Hok as [Hsafe | [_ [Hne _]]]; [| exact Hne].
        exfalso. destruct Hsafe as [H | [H | H]]; discriminate H.
      + rewrite ualt_dec_0 in Hq. discriminate Hq.
  Qed.
End hooks.
