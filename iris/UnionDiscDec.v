(* ===================================================================== *)
(* UnionDiscDec.v -- THE UNION MODEL'S RANGE CONDITION, DECIDED, and the *)
(* demos run through it (cut C9b).  Pure.                                *)
(*                                                                        *)
(*  [uok_dec] decides [UnionDisc.uok] at every admission, state, line and *)
(*  alternative (the pipeline half is [PipesDiscDec.plalt_ok_dec] at the  *)
(*  round's content function).  The demos:                                *)
(*    - [cat f | cat | cat] prints [f]'s content at a state holding it,   *)
(*      and cat's open diagnostic at the empty state;                     *)
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
(*      admissible at every state, and free ([demo_execL_echo]);          *)
(*    - GREP STAGES (cut G8, at the union application's [ulmG]):          *)
(*      [echo foo | grep o | cat] prints the line, [echo foo | grep z |   *)
(*      cat] nothing (and never the line), [cat f | grep x | cat] prints  *)
(*      [f]'s line when it holds an [x] and nothing when it does not.     *)
(*                                                                        *)
(*  THE HOOKS: [ulm_hooks adm : lm_hooks (ulm adm)] at every admission,   *)
(*  and [ulmG_hooks] at the union application's.                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import gmap list countable bitvector.definitions.
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
Proof using. destruct l as [ws | ws N | N | [ws | f] n], a as [r | x | x]; cbn [uok]; apply _. Defined.

Global Instance ulm_ok_dec adm s l a : Decision (lm_ok (ulm adm) s l a) := uok_dec adm s l a.

(* ===================================================================== *)
(*  1b.  THE HOOKS ([LineModelLinks.lm_hooks]) at every admission          *)
(*                                                                        *)
(*  Free: the file's state-free alternatives, every non-terminal echo-    *)
(*  pipeline alternative, and at a [cat f] pipeline the panic, the silent *)
(*  round and [exec cat failed] ([UnionDisc.ufree]).  The boot state      *)
(*  [lmh_st0] is the file's, the empty map.                                      *)
(* ===================================================================== *)
Definition ulm_hooks (adm : pline' -> bool) : lm_hooks (ulm adm) :=
  MkLMH (ulm adm) ufree ∅ upan uexf uexfb unoc (ulm_ok_dec adm)
    ufree_cont ufree_term (ufree_ok adm)
    (upan_ok adm) upan_free upan_panic
    (uexf_ok adm) uexf_free uexf_nopanic uexf_cont
    (unoc_ok adm) unoc_free unoc_nopanic unoc_cont
    (ucont_prompt adm) (ucont_nonnil adm).

Definition ulmG_hooks : lm_hooks ulmG := ulm_hooks adm_u_g.

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

(* ---- cat a.txt | cat | cat ---- *)
Definition l_cf2 : uline := LPipe (PrCatF txt_a) (cats 2).

Example demo_parse_cf2 :
  uline_of_u (sb "cat a.txt | cat | cat") = l_cf2 /\ ubody_ok adm_u_g (sb "cat a.txt | cat | cat").
Proof using. split; [vm_compute; reflexivity | dec_yes]. Qed.

(* at a state holding [c]: the content, then the prompt *)
Example demo_cf2_some :
  lm_ok ulmG {[txt_a := c_hi]} l_cf2 (UPC (PLRun c_hi))
  /\ lm_cont ulmG {[txt_a := c_hi]} l_cf2 (UPC (PLRun c_hi)) = c_hi ++ u_prompt.
Proof using. split; [cbn [ulmG ulm lm_ok]; dec_yes | reflexivity]. Qed.

(* ...and not someone else's *)
Example demo_cf2_some_neg : ~ uok adm_u_g {[txt_a := c_hi]} l_cf2 (UPC (PLRun (sb "bye" ++ nl1))).
Proof using. dec_no. Qed.

(* at the empty map: cat's open diagnostic *)
Example demo_cf2_none :
  lm_ok ulmG ∅ l_cf2 (UPC (PLRun (cat_dg_open txt_a)))
  /\ lm_cont ulmG ∅ l_cf2 (UPC (PLRun (cat_dg_open txt_a)))
     = sb "cat: cannot open a.txt" ++ nl1 ++ u_prompt.
Proof using. split; [cbn [ulmG ulm lm_ok]; dec_yes | vm_compute; reflexivity]. Qed.

(* ...and at the empty map no content *)
Example demo_cf2_none_neg : ~ uok adm_u_g ∅ l_cf2 (UPC (PLRun c_hi)).
Proof using. dec_no. Qed.

(* ---- echo x > a.txt, then cat a.txt | cat: the state threaded ---- *)
Definition ws_x : list (list (bv 8)) := [cmd_echo; sb "x"].
Definition x_nl : list (bv 8) := sb "x" ++ nl1.
Definition b_thr1 : list (bv 8) := sb "echo x > a.txt".
Definition b_thr2 : list (bv 8) := sb "cat a.txt | cat".
Definition I_thr : list (bv 8) := b_thr1 ++ nl1 ++ b_thr2 ++ nl1.
Definition a_thr1 : ualt := UR (RFRan (sel_all (echo_chunks ws_x))).
Definition a_thr2 : ualt := UPC (PLRun x_nl).
(* the stage's choice list: the codes are BUILT, never computed *)
Definition cs_thr : list nat := [ualt_code a_thr1; ualt_code a_thr2].

Lemma thr_bodies : bodies_of I_thr = [b_thr1; b_thr2].
Proof using. vm_compute. reflexivity. Qed.

Lemma thr_line1 : uline_of_u b_thr1 = LEchoF ws_x txt_a.
Proof using. vm_compute. reflexivity. Qed.

Lemma thr_line2 : uline_of_u b_thr2 = LPipe (PrCatF txt_a) (cats 1).
Proof using. vm_compute. reflexivity. Qed.

Lemma thr_at0 : lm_at ulmG cs_thr 0 = a_thr1.
Proof using.
  unfold lm_at. cbn [ulmG ulm lm_dec].
  rewrite (_ : cs_thr !!! 0 = ualt_code a_thr1); [apply ualt_dec_code | reflexivity].
Qed.

Lemma thr_at1 : lm_at ulmG cs_thr 1 = a_thr2.
Proof using.
  unfold lm_at. cbn [ulmG ulm lm_dec].
  rewrite (_ : cs_thr !!! 1 = ualt_code a_thr2); [apply ualt_dec_code | reflexivity].
Qed.

(* the first round leaves [a.txt] holding [x] *)
Example demo_thread_upto : lm_upto ulmG cs_thr ∅ (bodies_of I_thr) 1 = {[txt_a := x_nl]}.
Proof using.
  cbn [lm_upto]. rewrite thr_at0 thr_bodies.
  change ([b_thr1; b_thr2] !!! 0) with b_thr1.
  cbn [ulmG ulm lm_of lm_step]. rewrite thr_line1. dec_yes.
Qed.

(* the line count, as a lemma: rewriting [nlines] away by conversion in a
   hypothesis makes the kernel run the cut over the input lazily *)
Lemma thr_nlines : nlines I_thr = 2.
Proof using. rewrite /nlines thr_bodies. reflexivity. Qed.

(* both rounds are in range, each at the state ITS round starts in *)
Example demo_thread_ok : lm_alts_ok ulmG ∅ I_thr cs_thr.
Proof using.
  split; [rewrite thr_nlines; reflexivity |].
  intros i Hi. rewrite thr_nlines in Hi.
  destruct i as [| [| i]]; [| | lia].
  - cbn [lm_upto]. rewrite thr_at0 thr_bodies.
    change ([b_thr1; b_thr2] !!! 0) with b_thr1.
    cbn [ulmG ulm lm_of lm_ok]. rewrite thr_line1. dec_yes.
  - rewrite demo_thread_upto thr_at1 thr_bodies.
    change ([b_thr1; b_thr2] !!! 1) with b_thr2.
    cbn [ulmG ulm lm_of lm_ok]. rewrite thr_line2. dec_yes.
Qed.

(* ...and the second round prints what the first wrote *)
Example demo_thread_cont :
  lm_cont ulmG (lm_upto ulmG cs_thr ∅ (bodies_of I_thr) 1)
    (lm_of ulmG (bodies_of I_thr !!! 1)) (lm_at ulmG cs_thr 1) = x_nl ++ u_prompt.
Proof using. rewrite thr_at1. reflexivity. Qed.

(* ---- NEGATIVE (B2): the file's alternatives are not a pipeline's ---- *)
Definition l_hi1 : uline := LPipe (PrEcho [cmd_echo; sb "hi"]) (cats 1).

(* the dead arm of [FileDisc.ralt_ok] admits [RCRan] here, and [RCRan]'s
   continuation at a state holding [c] is the file content ... *)
Example demo_B2_deadarm :
  ralt_ok l_hi1 RCRan /\ cont {[fname_f := c_hi]} l_hi1 RCRan = c_hi ++ u_prompt.
Proof using. split; [exact I | vm_compute; reflexivity]. Qed.

(* ... which the union does NOT admit, at any state *)
Example demo_B2_neg : forall s, ~ lm_ok ulmG s l_hi1 (UR RCRan).
Proof using. intros s H. exact H. Qed.

(* ---- THE TWO-STAGE CORNER (S3) ---- *)
Definition l_cf1 : uline := LPipe (PrCatF txt_a) (cats 1).
Definition corner_blk : list (bv 8) := sb "h" ++ cat_dg_write.

(* at [cat f | cat] the producer's write error beside a printed prefix *)
Example demo_S3_corner : uok adm_u_g {[txt_a := c_hi]} l_cf1 (UPC (PLRun corner_blk)).
Proof using. dec_yes. Qed.

(* ... and beside the whole content *)
Example demo_S3_corner_full :
  uok adm_u_g {[txt_a := c_hi]} l_cf1 (UPC (PLRun (c_hi ++ cat_dg_write))).
Proof using. dec_yes. Qed.

(* ... while at [echo hi | cat] (echo's halt is silent) it is not *)
Example demo_S3_echo_neg : ~ uok adm_u_g {[txt_a := c_hi]} l_hi1 (UPE (PLRun corner_blk)).
Proof using. dec_no. Qed.

(* ---- THE ADMISSION: [cat g] at another name is not admitted ---- *)
Example demo_adm_other : ~ ubody_ok adm_u_g (sb "cat g | cat").
Proof using. dec_no. Qed.

(* ---- GREP STAGES (cut G8): the lines parse and are admitted ---- *)
Example demo_grep_parse :
  uline_of_u (sb "echo hi | grep h | cat")
  = LPipe (PrEcho [cmd_echo; sb "hi"]) [FGrep (sb "h"); FCat].
Proof using. vm_compute. reflexivity. Qed.

Example demo_adm_grep :
  ubody_ok adm_u_g (sb "echo hi | grep h | cat") /\ ubody_ok adm_u_g (sb "cat a.txt | grep h").
Proof using. split; dec_yes. Qed.

(* ...but no pattern-less grep, and no grep of two words *)
Example demo_adm_grep_neg :
  ~ ubody_ok adm_u_g (sb "echo hi | grep") /\ ~ ubody_ok adm_u_g (sb "echo hi | grep a b").
Proof using. split; dec_no. Qed.

(* echo foo | grep o | cat: the line passes the gate, so it is printed *)
Definition l_eg_o : uline := LPipe (PrEcho [cmd_echo; sb "foo"]) [FGrep (sb "o"); FCat].
Definition c_foo : list (bv 8) := sb "foo" ++ nl1.

Example demo_grep_pass :
  uline_of_u (sb "echo foo | grep o | cat") = l_eg_o
  /\ lm_ok ulmG ∅ l_eg_o (UPE (PLRun c_foo))
  /\ lm_cont ulmG ∅ l_eg_o (UPE (PLRun c_foo)) = c_foo ++ u_prompt.
Proof using. split_and!; [vm_compute; reflexivity | cbn [ulmG ulm lm_ok]; dec_yes | reflexivity]. Qed.

(* echo foo | grep z | cat: the gate is shut, the round prints nothing
   ... *)
Definition l_eg_z : uline := LPipe (PrEcho [cmd_echo; sb "foo"]) [FGrep (sb "z"); FCat].

Example demo_grep_block :
  uline_of_u (sb "echo foo | grep z | cat") = l_eg_z
  /\ lm_ok ulmG ∅ l_eg_z (UPE (PLRun []))
  /\ lm_cont ulmG ∅ l_eg_z (UPE (PLRun [])) = u_prompt.
Proof using. split_and!; [vm_compute; reflexivity | cbn [ulmG ulm lm_ok]; dec_yes | reflexivity]. Qed.

(* ... and never the line *)
Example demo_grep_block_neg : forall s, ~ lm_ok ulmG s l_eg_z (UPE (PLRun c_foo)).
Proof using.
  enough (Hn : ~ uok adm_u_g ∅ l_eg_z (UPE (PLRun c_foo)))
    by (intros s H; apply Hn; exact (uok_echo_st adm_u_g s ∅ _ _ _ H)).
  dec_no.
Qed.

(* cat f | grep x | cat at a state with [f]: [f]'s line when it holds an
   [x], nothing when it does not *)
Definition l_cg_x : uline := LPipe (PrCatF txt_a) [FGrep (sb "x"); FCat].
Definition c_box : list (bv 8) := sb "box" ++ nl1.

Example demo_grep_catf :
  uline_of_u (sb "cat a.txt | grep x | cat") = l_cg_x
  /\ lm_ok ulmG {[txt_a := c_box]} l_cg_x (UPC (PLRun c_box))
  /\ lm_cont ulmG {[txt_a := c_box]} l_cg_x (UPC (PLRun c_box)) = c_box ++ u_prompt
  /\ ~ lm_ok ulmG {[txt_a := c_hi]} l_cg_x (UPC (PLRun c_hi))
  /\ lm_ok ulmG {[txt_a := c_hi]} l_cg_x (UPC (PLRun [])).
Proof using.
  split_and!; [vm_compute; reflexivity | cbn [ulmG ulm lm_ok]; dec_yes | reflexivity
              | cbn [ulmG ulm lm_ok]; dec_no | cbn [ulmG ulm lm_ok]; dec_yes].
Qed.

(* ---- THE PRODUCER SPLIT: the cross cases ---- *)
Example demo_split_cross :
  forall s x, ~ uok adm_u_g s l_hi1 (UPC x) /\ ~ uok adm_u_g s l_cf1 (UPE x).
Proof using. intros s x. split; intros H; exact H. Qed.

(* ---- WHY THE PRODUCERS ARE SPLIT ---- *)
(* [exec echo failed] is a content [f] may hold ([echo exec echo failed >
   f]); at [cat f | cat] the last cat then prints it *)
Example demo_execL_state_dep :
  fstate_ok {[txt_a := PipeDisc.dg_execL]}
  /\ uok adm_u_g {[txt_a := PipeDisc.dg_execL]} l_cf1 (UPC (PLRun PipeDisc.dg_execL))
  /\ ~ uok adm_u_g ∅ l_cf1 (UPC (PLRun PipeDisc.dg_execL)).
Proof using.
  split_and!; [| dec_yes | dec_no].
  rewrite /fstate_ok map_Forall_singleton. split; [exact txt_a_name |].
  right. exists (sb "exec echo failed"). split; [| vm_compute; reflexivity].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* so a free set meeting [lmh_free_ok] never counts it free at [UPC] ... *)
Lemma no_free_execL (free : ualt -> bool) :
  (forall s s' l a, free a = true -> uok adm_u_g s l a -> uok adm_u_g s' l a) ->
  free (UPC (PLRun PipeDisc.dg_execL)) = false.
Proof using.
  intros Hfr. destruct (free (UPC (PLRun PipeDisc.dg_execL))) eqn:E; [| reflexivity].
  exfalso. destruct demo_execL_state_dep as (_ & Hs & Hn).
  exact (Hn (Hfr _ _ _ _ E Hs)).
Qed.

(* ... while at an echo pipeline the same block is [UPE] of it: the hooks'
   exec alternative there, admissible at every state, and free *)
Example demo_execL_echo :
  lm_dec ulmG (lmh_exf ulmG_hooks l_hi1) = UPE (PLRun PipeDisc.dg_execL)
  /\ (forall s, lm_ok ulmG s l_hi1 (UPE (PLRun PipeDisc.dg_execL)))
  /\ lmh_free ulmG_hooks (UPE (PLRun PipeDisc.dg_execL)) = true.
Proof using.
  split_and!; [exact (ulm_hooks_exf adm_u_g (PrEcho [cmd_echo; sb "hi"]) (cats 1)) | | reflexivity].
  intros s. left. right. right. reflexivity.
Qed.

(* ===================================================================== *)
(*  3.  THE CLASS OF USER FILES, `stem.txt` (cut W4; filenames.md)        *)
(*                                                                        *)
(*  A session at the widened model: a file of the class is written and    *)
(*  read back, two files of the class are independent, a class file       *)
(*  feeds a pipeline with a grep -- and no line naming a file outside     *)
(*  the class is admitted (the owner's ruling: user files, never the     *)
(*  image's binaries), nor does the dot widen an echo word or a grep     *)
(*  pattern.                                                              *)
(* ===================================================================== *)

(* one round of [lm_upto], by its own equation (a [change] makes the
   unifier run the rounds) *)
Lemma lm_upto_S2 (cs : list nat) (bs : list (list (bv 8))) (q : nat) :
  lm_upto ulmG cs ∅ bs (S q)
  = lm_step ulmG (lm_upto ulmG cs ∅ bs q) (lm_of ulmG (bs !!! q)) (lm_at ulmG cs q).
Proof using. reflexivity. Qed.

Definition nm_b : list (bv 8) := sb "b.txt".
Definition ws_hi : list (list (bv 8)) := [cmd_echo; sb "hi"].
Definition ws_y : list (list (bv 8)) := [cmd_echo; sb "y"].
Definition y_nl : list (bv 8) := sb "y" ++ nl1.

Lemma nm_b_class : uname nm_b.
Proof using. apply txt_nameb_spec. vm_compute. reflexivity. Qed.

(* ---- echo hi > a.txt, then cat a.txt prints hi ---- *)
Definition b_hi1 : list (bv 8) := sb "echo hi > a.txt".
Definition b_ca : list (bv 8) := sb "cat a.txt".
Definition I_hi : list (bv 8) := b_hi1 ++ nl1 ++ b_ca ++ nl1.
Definition a_hi1 : ualt := UR (RFRan (sel_all (echo_chunks ws_hi))).
Definition a_cat : ualt := UR RCRan.
Definition cs_hi : list nat := [ualt_code a_hi1; ualt_code a_cat].

Lemma hi_bodies : bodies_of I_hi = [b_hi1; b_ca].
Proof using. vm_compute. reflexivity. Qed.

Lemma hi_line1 : uline_of_u b_hi1 = LEchoF ws_hi txt_a.
Proof using. vm_compute. reflexivity. Qed.

Lemma ca_line : uline_of_u b_ca = LCat txt_a.
Proof using. vm_compute. reflexivity. Qed.

Lemma hi_at0 : lm_at ulmG cs_hi 0 = a_hi1.
Proof using.
  unfold lm_at. cbn [ulmG ulm lm_dec].
  rewrite (_ : cs_hi !!! 0 = ualt_code a_hi1); [apply ualt_dec_code | reflexivity].
Qed.

Lemma hi_at1 : lm_at ulmG cs_hi 1 = a_cat.
Proof using.
  unfold lm_at. cbn [ulmG ulm lm_dec].
  rewrite (_ : cs_hi !!! 1 = ualt_code a_cat); [apply ualt_dec_code | reflexivity].
Qed.

(* the first round leaves [a.txt] holding [hi] *)
Example demo_txt_upto : lm_upto ulmG cs_hi ∅ (bodies_of I_hi) 1 = {[txt_a := c_hi]}.
Proof using.
  cbn [lm_upto]. rewrite hi_at0 hi_bodies.
  change ([b_hi1; b_ca] !!! 0) with b_hi1.
  cbn [ulmG ulm lm_of lm_step]. rewrite hi_line1. dec_yes.
Qed.

Lemma hi_nlines : nlines I_hi = 2.
Proof using. rewrite /nlines hi_bodies. reflexivity. Qed.

(* both rounds are in range, each at the state its round starts in *)
Example demo_txt_ok : lm_alts_ok ulmG ∅ I_hi cs_hi.
Proof using.
  split; [rewrite hi_nlines; reflexivity |].
  intros i Hi. rewrite hi_nlines in Hi.
  destruct i as [| [| i]]; [| | lia].
  - cbn [lm_upto]. rewrite hi_at0 hi_bodies.
    change ([b_hi1; b_ca] !!! 0) with b_hi1.
    cbn [ulmG ulm lm_of lm_ok]. rewrite hi_line1. dec_yes.
  - rewrite demo_txt_upto hi_at1 hi_bodies.
    change ([b_hi1; b_ca] !!! 1) with b_ca.
    cbn [ulmG ulm lm_of lm_ok]. rewrite ca_line. dec_yes.
Qed.

(* ...and [cat a.txt] prints [hi] *)
Example demo_txt_cat :
  lm_cont ulmG (lm_upto ulmG cs_hi ∅ (bodies_of I_hi) 1)
    (lm_of ulmG (bodies_of I_hi !!! 1)) (lm_at ulmG cs_hi 1) = c_hi ++ u_prompt.
Proof using.
  rewrite demo_txt_upto hi_at1 hi_bodies.
  change ([b_hi1; b_ca] !!! 1) with b_ca.
  cbn [ulmG ulm lm_of lm_cont]. rewrite ca_line. dec_yes.
Qed.

(* ---- TWO FILES ARE INDEPENDENT: echo x > a.txt, echo y > b.txt, then
   cat a.txt prints x ---- *)
Definition b_y : list (bv 8) := sb "echo y > b.txt".
Definition I_2f : list (bv 8) := b_thr1 ++ nl1 ++ b_y ++ nl1 ++ b_ca ++ nl1.
Definition a_y : ualt := UR (RFRan (sel_all (echo_chunks ws_y))).
Definition cs_2f : list nat := [ualt_code a_thr1; ualt_code a_y; ualt_code a_cat].

Lemma f2_bodies : bodies_of I_2f = [b_thr1; b_y; b_ca].
Proof using. vm_compute. reflexivity. Qed.

Lemma y_line : uline_of_u b_y = LEchoF ws_y nm_b.
Proof using. vm_compute. reflexivity. Qed.

Lemma f2_at (i : nat) (a : ualt) :
  [ualt_code a_thr1; ualt_code a_y; ualt_code a_cat] !! i = Some (ualt_code a) ->
  lm_at ulmG cs_2f i = a.
Proof using.
  intros Hi. unfold lm_at. cbn [ulmG ulm lm_dec].
  rewrite (list_lookup_total_correct _ _ _ Hi). apply ualt_dec_code.
Qed.

Example demo_2f_upto1 : lm_upto ulmG cs_2f ∅ (bodies_of I_2f) 1 = {[txt_a := x_nl]}.
Proof using.
  cbn [lm_upto]. rewrite (f2_at 0 a_thr1 eq_refl) f2_bodies.
  change ([b_thr1; b_y; b_ca] !!! 0) with b_thr1.
  cbn [ulmG ulm lm_of lm_step]. rewrite thr_line1. dec_yes.
Qed.

(* the second round writes [b.txt] and leaves [a.txt] alone *)
Example demo_2f_upto2 :
  lm_upto ulmG cs_2f ∅ (bodies_of I_2f) 2 = <[nm_b := y_nl]> {[txt_a := x_nl]}.
Proof using.
  rewrite (lm_upto_S2 cs_2f (bodies_of I_2f) 1) demo_2f_upto1 (f2_at 1 a_y eq_refl) f2_bodies.
  change ([b_thr1; b_y; b_ca] !!! 1) with b_y.
  cbn [ulmG ulm lm_of lm_step]. rewrite y_line. dec_yes.
Qed.

Lemma f2_nlines : nlines I_2f = 3.
Proof using. rewrite /nlines f2_bodies. reflexivity. Qed.

Example demo_2f_ok : lm_alts_ok ulmG ∅ I_2f cs_2f.
Proof using.
  split; [rewrite f2_nlines; reflexivity |].
  intros i Hi. rewrite f2_nlines in Hi.
  destruct i as [| [| [| i]]]; [| | | lia].
  - cbn [lm_upto]. rewrite (f2_at 0 a_thr1 eq_refl) f2_bodies.
    change ([b_thr1; b_y; b_ca] !!! 0) with b_thr1.
    cbn [ulmG ulm lm_of lm_ok]. rewrite thr_line1. dec_yes.
  - rewrite demo_2f_upto1 (f2_at 1 a_y eq_refl) f2_bodies.
    change ([b_thr1; b_y; b_ca] !!! 1) with b_y.
    cbn [ulmG ulm lm_of lm_ok]. rewrite y_line. dec_yes.
  - rewrite demo_2f_upto2 (f2_at 2 a_cat eq_refl) f2_bodies.
    change ([b_thr1; b_y; b_ca] !!! 2) with b_ca.
    cbn [ulmG ulm lm_of lm_ok]. rewrite ca_line. dec_yes.
Qed.

(* [cat a.txt] prints [x], whatever [b.txt] holds *)
Example demo_2f_cat :
  lm_cont ulmG (lm_upto ulmG cs_2f ∅ (bodies_of I_2f) 2)
    (lm_of ulmG (bodies_of I_2f !!! 2)) (lm_at ulmG cs_2f 2) = x_nl ++ u_prompt.
Proof using.
  rewrite demo_2f_upto2 (f2_at 2 a_cat eq_refl) f2_bodies.
  change ([b_thr1; b_y; b_ca] !!! 2) with b_ca.
  cbn [ulmG ulm lm_of lm_cont]. rewrite ca_line. dec_yes.
Qed.

(* ---- cat a.txt | grep h | cat prints the file's line when it holds an
   h ---- *)
Definition l_cg_h : uline := LPipe (PrCatF txt_a) [FGrep (sb "h"); FCat].

Example demo_txt_grep :
  uline_of_u (sb "cat a.txt | grep h | cat") = l_cg_h
  /\ ubody_ok adm_u_g (sb "cat a.txt | grep h | cat")
  /\ lm_ok ulmG {[txt_a := c_hi]} l_cg_h (UPC (PLRun c_hi))
  /\ lm_cont ulmG {[txt_a := c_hi]} l_cg_h (UPC (PLRun c_hi)) = c_hi ++ u_prompt.
Proof using.
  split_and!; [vm_compute; reflexivity | dec_yes | cbn [ulmG ulm lm_ok]; dec_yes | reflexivity].
Qed.

(* ---- NOT ADMITTED: a file outside the class (the image's README, the
   old one-name class's [f], a binary's name), and the dot anywhere but
   a file name ---- *)
Example demo_txt_neg :
  ~ ubody_ok adm_u_g (sb "cat README") /\ ~ ubody_ok adm_u_g (sb "cat f")
  /\ ~ ubody_ok adm_u_g (sb "echo x > sh") /\ ~ ubody_ok adm_u_g (sb "cat /sh")
  /\ ~ ubody_ok adm_u_g (sb "cat README | cat")
  /\ ~ ubody_ok adm_u_g (sb "echo a.txt")
  /\ ~ ubody_ok adm_u_g (sb "echo hi | grep a.txt").
Proof using. split_and!; dec_no. Qed.
