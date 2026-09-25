(* ===================================================================== *)
(* UnionDiscDec.v -- THE UNION MODEL'S RANGE CONDITION, DECIDED, and the *)
(* demos run through it (cut C9b).  Pure.                                *)
(*                                                                        *)
(*  [uok_dec] decides [UnionDisc.uok] at every admission, state, line and *)
(*  alternative (the pipeline half is [PipesDiscDec.plalt_ok_dec] at the  *)
(*  round's content function).  The demos:                                *)
(*    - [cat f | cat | cat] prints [f]'s content at [Some c], and cat's   *)
(*      open diagnostic at [None];                                        *)
(*    - [echo x > f] then [cat f | cat]: the state the first round leaves *)
(*      is what the second prints, through the model's own [lm_upto];    *)
(*    - NEGATIVE (amendment B2): the file's [RCRan] is not admitted at    *)
(*      [echo hi | cat], though [FileDisc.ralt_ok]'s dead arm admits it;  *)
(*    - THE TWO-STAGE CORNER (amendment S3): at [cat f | cat] the         *)
(*      producer's [cat: write error] beside a printed prefix of the      *)
(*      content is admitted -- an honest limit -- while at [echo hi |     *)
(*      cat] it is not;                                                   *)
(*    - THE PRODUCER SPLIT (C9b2): [exec echo failed] at a [cat f]      *)
(*      pipeline is admissible at one content and not at another, so no   *)
(*      free set satisfying [lmh_free_ok] contains [UPC] of it            *)
(*      ([no_free_execL]); at an echo pipeline it is [UPE] of it,         *)
(*      admissible at every state, and free ([demo_execL_echo]).          *)
(*                                                                        *)
(*  THE HOOKS: [ulm_hooks adm : lm_hooks (ulm adm)] at every admission,   *)
(*  and [ulmU_hooks] at the union application's.                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list countable bitvector.definitions.
Require Import RiscvLang ObsTrace.
Require Import LineWords EchoDisc LineBytes LineModel LineModelLinks.
Require Import StringBytes ProgTree ProgTreePipes PipesPair PipesDisc PipesDiscDec.
Require PipeDisc.
Require Import FileState FileDisc.
Require Import UnionDisc.
From stdpp Require Import list ssreflect.

Local Open Scope nat_scope.

(* ===================================================================== *)
(*  1.  THE DECISION                                                      *)
(* ===================================================================== *)

Global Instance uok_dec adm s l a : Decision (uok adm s l a).
Proof using. destruct l as [ws | ws | | [ws | f] n], a as [r | x | x]; cbn [uok]; apply _. Defined.

Global Instance ulm_ok_dec adm s l a : Decision (lm_ok (ulm adm) s l a) := uok_dec adm s l a.

(* ===================================================================== *)
(*  1b.  THE HOOKS ([LineModelLinks.lm_hooks]) at every admission          *)
(*                                                                        *)
(*  Free: the file's state-free alternatives, every non-terminal echo-    *)
(*  pipeline alternative, and at a [cat f] pipeline the panic, the silent *)
(*  round and [exec cat failed] ([UnionDisc.ufree]).  The boot state      *)
(*  [lmh_st0] is the file's, [None].                                      *)
(* ===================================================================== *)
Definition ulm_hooks (adm : pline' -> bool) : lm_hooks (ulm adm) :=
  MkLMH (ulm adm) ufree None upan uexf uexfb unoc (ulm_ok_dec adm)
    ufree_cont ufree_term (ufree_ok adm)
    (upan_ok adm) upan_free upan_panic
    (uexf_ok adm) uexf_free uexf_nopanic uexf_cont
    (unoc_ok adm) unoc_free unoc_nopanic unoc_cont
    (ucont_prompt adm) (ucont_nonnil adm).

Definition ulmU_hooks : lm_hooks ulmU := ulm_hooks adm_u_f.

(* the hooks' three codes at a pipeline, read back *)
Lemma ulm_hooks_pan adm p n : lm_dec (ulm adm) (lmh_pan (ulm_hooks adm) (LPipe p n)) = upl p PLPanic.
Proof using. exact (ualt_dec_code _). Qed.
Lemma ulm_hooks_exf adm p n :
  lm_dec (ulm adm) (lmh_exf (ulm_hooks adm) (LPipe p n)) = upl p (PLRun (pl_exfb (LPipes p n))).
Proof using. exact (ualt_dec_code _). Qed.
Lemma ulm_hooks_noc adm p n : lm_dec (ulm adm) (lmh_noc (ulm_hooks adm) (LPipe p n)) = upl p (PLRun []).
Proof using. exact (ualt_dec_code _). Qed.

Local Ltac dec_yes := apply (bool_decide_unpack _); vm_compute; exact I.
Local Ltac dec_no := apply (bool_decide_unpack _); vm_compute; exact I.

(* ===================================================================== *)
(*  2.  DEMOS                                                             *)
(* ===================================================================== *)

Definition nl1 : list (bv 8) := [wl_nl].
Definition c_hi : list (bv 8) := sb "hi" ++ nl1.

(* ---- cat f | cat | cat ---- *)
Definition l_cf2 : uline := LPipe (PrCatF fname_f) (cats 2).

Example demo_parse_cf2 :
  uline_of_u (sb "cat f | cat | cat") = l_cf2 /\ ubody_ok adm_u_f (sb "cat f | cat | cat").
Proof using. split; [vm_compute; reflexivity | dec_yes]. Qed.

(* at [Some c]: the content, then the prompt *)
Example demo_cf2_some :
  lm_ok ulmU (Some c_hi) l_cf2 (UPC (PLRun c_hi))
  /\ lm_cont ulmU (Some c_hi) l_cf2 (UPC (PLRun c_hi)) = c_hi ++ u_prompt.
Proof using. split; [cbn [ulmU ulm lm_ok]; dec_yes | reflexivity]. Qed.

(* ...and not someone else's *)
Example demo_cf2_some_neg : ~ uok adm_u_f (Some c_hi) l_cf2 (UPC (PLRun (sb "bye" ++ nl1))).
Proof using. dec_no. Qed.

(* at [None]: cat's open diagnostic *)
Example demo_cf2_none :
  lm_ok ulmU None l_cf2 (UPC (PLRun (cat_dg_open fname_f)))
  /\ lm_cont ulmU None l_cf2 (UPC (PLRun (cat_dg_open fname_f)))
     = sb "cat: cannot open f" ++ nl1 ++ u_prompt.
Proof using. split; [cbn [ulmU ulm lm_ok]; dec_yes | vm_compute; reflexivity]. Qed.

(* ...and at [None] no content *)
Example demo_cf2_none_neg : ~ uok adm_u_f None l_cf2 (UPC (PLRun c_hi)).
Proof using. dec_no. Qed.

(* ---- echo x > f, then cat f | cat: the state threaded ---- *)
Definition ws_x : list (list (bv 8)) := [cmd_echo; sb "x"].
Definition x_nl : list (bv 8) := sb "x" ++ nl1.
Definition b_thr1 : list (bv 8) := sb "echo x > f".
Definition b_thr2 : list (bv 8) := sb "cat f | cat".
Definition I_thr : list (bv 8) := b_thr1 ++ nl1 ++ b_thr2 ++ nl1.
Definition a_thr1 : ualt := UR (RFRan (sel_all (echo_chunks ws_x))).
Definition a_thr2 : ualt := UPC (PLRun x_nl).
(* the stage's choice list: the codes are BUILT, never computed *)
Definition cs_thr : list nat := [ualt_code a_thr1; ualt_code a_thr2].

Lemma thr_bodies : bodies_of I_thr = [b_thr1; b_thr2].
Proof using. vm_compute. reflexivity. Qed.

Lemma thr_line1 : uline_of_u b_thr1 = LEchoF ws_x.
Proof using. vm_compute. reflexivity. Qed.

Lemma thr_line2 : uline_of_u b_thr2 = LPipe (PrCatF fname_f) (cats 1).
Proof using. vm_compute. reflexivity. Qed.

Lemma thr_at0 : lm_at ulmU cs_thr 0 = a_thr1.
Proof using.
  unfold lm_at. cbn [ulmU ulm lm_dec].
  rewrite (_ : cs_thr !!! 0 = ualt_code a_thr1); [apply ualt_dec_code | reflexivity].
Qed.

Lemma thr_at1 : lm_at ulmU cs_thr 1 = a_thr2.
Proof using.
  unfold lm_at. cbn [ulmU ulm lm_dec].
  rewrite (_ : cs_thr !!! 1 = ualt_code a_thr2); [apply ualt_dec_code | reflexivity].
Qed.

(* the first round leaves [f] holding [x] *)
Example demo_thread_upto : lm_upto ulmU cs_thr None (bodies_of I_thr) 1 = Some x_nl.
Proof using.
  cbn [lm_upto]. rewrite thr_at0 thr_bodies.
  change ([b_thr1; b_thr2] !!! 0) with b_thr1.
  cbn [ulmU ulm lm_of lm_step]. rewrite thr_line1. vm_compute. reflexivity.
Qed.

(* both rounds are in range, each at the state ITS round starts in *)
Example demo_thread_ok : lm_alts_ok ulmU None I_thr cs_thr.
Proof using.
  split; [rewrite /nlines thr_bodies; reflexivity |].
  intros i Hi. rewrite /nlines thr_bodies in Hi. cbn [length] in Hi.
  destruct i as [| [| i]]; [| | lia].
  - cbn [lm_upto]. rewrite thr_at0 thr_bodies.
    change ([b_thr1; b_thr2] !!! 0) with b_thr1.
    cbn [ulmU ulm lm_of lm_ok]. rewrite thr_line1. dec_yes.
  - rewrite demo_thread_upto thr_at1 thr_bodies.
    change ([b_thr1; b_thr2] !!! 1) with b_thr2.
    cbn [ulmU ulm lm_of lm_ok]. rewrite thr_line2. dec_yes.
Qed.

(* ...and the second round prints what the first wrote *)
Example demo_thread_cont :
  lm_cont ulmU (lm_upto ulmU cs_thr None (bodies_of I_thr) 1)
    (lm_of ulmU (bodies_of I_thr !!! 1)) (lm_at ulmU cs_thr 1) = x_nl ++ u_prompt.
Proof using. rewrite thr_at1. reflexivity. Qed.

(* ---- NEGATIVE (B2): the file's alternatives are not a pipeline's ---- *)
Definition l_hi1 : uline := LPipe (PrEcho [cmd_echo; sb "hi"]) (cats 1).

(* the dead arm of [FileDisc.ralt_ok] admits [RCRan] here, and [RCRan]'s
   continuation at [Some c] is the file's content ... *)
Example demo_B2_deadarm :
  ralt_ok l_hi1 RCRan /\ cont (Some c_hi) l_hi1 RCRan = c_hi ++ u_prompt.
Proof using. split; [exact I | reflexivity]. Qed.

(* ... which the union does NOT admit, at any state *)
Example demo_B2_neg : forall s, ~ lm_ok ulmU s l_hi1 (UR RCRan).
Proof using. intros s H. exact H. Qed.

(* ---- THE TWO-STAGE CORNER (S3) ---- *)
Definition l_cf1 : uline := LPipe (PrCatF fname_f) (cats 1).
Definition corner_blk : list (bv 8) := sb "h" ++ cat_dg_write.

(* at [cat f | cat] the producer's write error beside a printed prefix *)
Example demo_S3_corner : uok adm_u_f (Some c_hi) l_cf1 (UPC (PLRun corner_blk)).
Proof using. dec_yes. Qed.

(* ... and beside the whole content *)
Example demo_S3_corner_full :
  uok adm_u_f (Some c_hi) l_cf1 (UPC (PLRun (c_hi ++ cat_dg_write))).
Proof using. dec_yes. Qed.

(* ... while at [echo hi | cat] (echo's halt is silent) it is not *)
Example demo_S3_echo_neg : ~ uok adm_u_f (Some c_hi) l_hi1 (UPE (PLRun corner_blk)).
Proof using. dec_no. Qed.

(* ---- THE ADMISSION: [cat g] at another name is not admitted ---- *)
Example demo_adm_other : ~ ubody_ok adm_u_f (sb "cat g | cat").
Proof using. dec_no. Qed.

(* ---- ...NOR, YET, A GREP STAGE (cut G3: the lines parse, the round
        admits cats only) ---- *)
Example demo_grep_parse :
  uline_of_u (sb "echo hi | grep h | cat")
  = LPipe (PrEcho [cmd_echo; sb "hi"]) [FGrep (sb "h"); FCat].
Proof using. vm_compute. reflexivity. Qed.

Example demo_adm_grep :
  ~ ubody_ok adm_u_f (sb "echo hi | grep h | cat") /\ ~ ubody_ok adm_u_f (sb "cat f | grep h").
Proof using. split; dec_no. Qed.

(* ---- THE PRODUCER SPLIT: the cross cases ---- *)
Example demo_split_cross :
  forall s x, ~ uok adm_u_f s l_hi1 (UPC x) /\ ~ uok adm_u_f s l_cf1 (UPE x).
Proof using. intros s x. split; intros H; exact H. Qed.

(* ---- WHY THE PRODUCERS ARE SPLIT ---- *)
(* [exec echo failed] is a content [f] may hold ([echo exec echo failed >
   f]); at [cat f | cat] the last cat then prints it *)
Example demo_execL_state_dep :
  fstate_ok (Some PipeDisc.dg_execL)
  /\ uok adm_u_f (Some PipeDisc.dg_execL) l_cf1 (UPC (PLRun PipeDisc.dg_execL))
  /\ ~ uok adm_u_f None l_cf1 (UPC (PLRun PipeDisc.dg_execL)).
Proof using.
  split_and!; [| dec_yes | dec_no].
  right. exists (sb "exec echo failed"). split; [| vm_compute; reflexivity].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* so a free set meeting [lmh_free_ok] never counts it free at [UPC] ... *)
Lemma no_free_execL (free : ualt -> bool) :
  (forall s s' l a, free a = true -> uok adm_u_f s l a -> uok adm_u_f s' l a) ->
  free (UPC (PLRun PipeDisc.dg_execL)) = false.
Proof using.
  intros Hfr. destruct (free (UPC (PLRun PipeDisc.dg_execL))) eqn:E; [| reflexivity].
  exfalso. destruct demo_execL_state_dep as (_ & Hs & Hn).
  exact (Hn (Hfr _ _ _ _ E Hs)).
Qed.

(* ... while at an echo pipeline the same block is [UPE] of it: the hooks'
   exec alternative there, admissible at every state, and free *)
Example demo_execL_echo :
  lm_dec ulmU (lmh_exf ulmU_hooks l_hi1) = UPE (PLRun PipeDisc.dg_execL)
  /\ (forall s, lm_ok ulmU s l_hi1 (UPE (PLRun PipeDisc.dg_execL)))
  /\ lmh_free ulmU_hooks (UPE (PLRun PipeDisc.dg_execL)) = true.
Proof using.
  split_and!; [exact (ulm_hooks_exf adm_u_f (PrEcho [cmd_echo; sb "hi"]) (cats 1)) | | reflexivity].
  intros s. left. right. right. reflexivity.
Qed.
