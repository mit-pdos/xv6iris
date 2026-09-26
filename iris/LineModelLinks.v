(* ===================================================================== *)
(*  LineModelLinks.v -- THE WRITER'S PURE READING OF A LINE MODEL, once  *)
(*  (app-both milestone M2a).                                            *)
(*                                                                       *)
(*  What the console credential families ([FileLinksLine] S8,            *)
(*  [PipeLinksLine] S5, [EchoLinks]/[EchoLinksLine]) spend of the model  *)
(*  is PURE: the block an alternative owes at the line that was typed    *)
(*  ([lm_ab]), which alternatives end in the prompt ([lm_apr]), the      *)
(*  alternatives the shell's own code names (the fork panic, the exec    *)
(*  failure, and a silent one where the model has one), and the facts   *)
(*  about the stream                                                     *)
(*  ([LineModel.lm_proc_stream]) that the write links ask for: the       *)
(*  stream byte at the cursor, the cursor after a choice byte, a prompt  *)
(*  byte, a line's read.  Each application had proved that list over its *)
(*  own stream ([FileLinksLine] S0-S7, [PipeLinksLine] S0-S4,            *)
(*  [EchoLinks] + [EchoLinksLine] + [EchoLinksPro]); it is proved here   *)
(*  ONCE over the model, from a record of HOOKS ([lm_hooks]: the three   *)
(*  named alternatives per line, state-freedom, and what the writer      *)
(*  knows of a continuation without holding the discipline's premises). *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import LineWords.
Require Import EchoDisc.
Require Import LineBytes.
Require Import LineModel.
From stdpp Require Import ssreflect.

Local Open Scope nat_scope.

(* ====================================================================== *)
(*  0.  SMALL LIST FACTS, AND THE PROLOGUE'S                               *)
(* ====================================================================== *)

Lemma ll_app_snoc {A} (pre : list A) (a : A) (l : list A) :
  (pre ++ [a]) ++ l = pre ++ a :: l.
Proof. by rewrite -app_assoc. Qed.

Lemma ll_app_cons_ne {A} (l : list A) (a : A) (r : list A) :
  l <> l ++ a :: r.
Proof.
  intro Hq. apply (f_equal length) in Hq.
  rewrite (length_app l (a :: r)) in Hq. cbn [length] in Hq. lia.
Qed.

Lemma ll_removelast_snoc {A} (l : list A) (a : A) : removelast (l ++ [a]) = l.
Proof.
  induction l as [| b l IH]; [reflexivity |].
  change ((b :: l) ++ [a]) with (b :: (l ++ [a])).
  assert (Hne : l ++ [a] <> [])
    by (intro Hq; by apply app_eq_nil in Hq as [_ ?]).
  destruct (l ++ [a]) as [| z zs] eqn:Hz; [by destruct (Hne eq_refl) |].
  change (removelast (b :: z :: zs)) with (b :: removelast (z :: zs)).
  by rewrite IH.
Qed.

Lemma ll_snoc_cases {A} (l : list A) : l = [] \/ exists u x, l = u ++ [x].
Proof.
  induction l as [| a l IH]; [by left |]. right.
  destruct IH as [-> | (u & x & ->)].
  - by exists [], a.
  - by exists (a :: u), x.
Qed.

Lemma ll_removelast_take {A} (l : list A) :
  removelast l = take (length l - 1) l.
Proof.
  induction l as [| a l IH]; [done |].
  destruct l as [| b l']; [reflexivity |].
  change (removelast (a :: b :: l')) with (a :: removelast (b :: l')).
  rewrite IH.
  replace (length (a :: b :: l') - 1) with (S (length (b :: l') - 1))
    by (cbn [length]; lia).
  reflexivity.
Qed.

Lemma ll_removelast_prefix {A} (l : list A) : removelast l `prefix_of` l.
Proof. rewrite ll_removelast_take. apply prefix_take. Qed.

Lemma ll_prefix_of_removelast {A} (l l' : list A) :
  l `prefix_of` l' -> l <> l' -> l `prefix_of` removelast l'.
Proof.
  intros Hp Hne. pose proof (prefix_length _ _ Hp) as Hlen.
  assert (Hlt : length l < length l').
  { destruct (decide (length l = length l')) as [He | He]; [| lia].
    exfalso. exact (Hne (prefix_length_eq _ _ Hp ltac:(lia))). }
  assert (Hl : l = take (length l) l').
  { destruct Hp as [z ->]. by rewrite take_app_length. }
  rewrite ll_removelast_take {1}Hl. apply prefix_take_le. lia.
Qed.

Lemma ll_nlines_removelast (I : list (bv 8)) :
  rest_of I = [] -> nlines (removelast I) = nlines I - 1.
Proof.
  intros Hr. destruct (ll_snoc_cases I) as [-> | (u & x & ->)].
  - cbn [removelast]. rewrite nlines_nil. lia.
  - destruct (decide (x = wl_nl)) as [-> | Hx].
    + rewrite ll_removelast_snoc nlines_snoc_nl. lia.
    + exfalso. rewrite (rest_of_snoc_other u x Hx) in Hr.
      by destruct (app_eq_nil (rest_of u) [x] Hr) as [_ Hb].
Qed.

Lemma ll_nstarted_rest_nil (I : list (bv 8)) :
  rest_of I = [] -> nstarted I = nlines I.
Proof.
  intros Hr. rewrite /nstarted Hr. case_decide as Hd;
    [lia | by destruct (Hd eq_refl)].
Qed.

Lemma ll_nstarted_snoc (I : list (bv 8)) (b : bv 8) :
  nstarted (I ++ [b]) = S (nlines I).
Proof.
  destruct (decide (b = wl_nl)) as [-> | Hb].
  - apply nstarted_snoc_nl.
  - by apply nstarted_snoc_other.
Qed.

Lemma ll_lta_prefix (cs0 cs : list nat) (i : nat) :
  cs0 `prefix_of` cs -> i < length cs0 -> cs !!! i = cs0 !!! i.
Proof.
  intros [z ->] Hi. rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
Qed.

Lemma ll_snoc_lookup_total (cs : list nat) (a : nat) :
  (cs ++ [a]) !!! length cs = a.
Proof.
  rewrite list_lookup_total_alt lookup_app_r; [| lia].
  by rewrite Nat.sub_diag.
Qed.

Lemma ll_bodies_of_app_nonl (I l : list (bv 8)) :
  wl_nl ∉ l -> bodies_of (I ++ l) = bodies_of I.
Proof.
  intro Hl.
  assert (Hc : wl_cut (I ++ l) = (bodies_of I, rest_of I ++ l))
    by exact (wl_cut_app_nonl I l Hl).
  rewrite /bodies_of Hc. by cbn [fst].
Qed.

Lemma ll_nlines_app_nonl (I l : list (bv 8)) :
  wl_nl ∉ l -> nlines (I ++ l) = nlines I.
Proof. intro Hl. by rewrite /nlines (ll_bodies_of_app_nonl I l Hl). Qed.

Lemma ll_rest_of_app_nonl (I l : list (bv 8)) :
  rest_of I = [] -> wl_nl ∉ l -> rest_of (I ++ l) = l.
Proof.
  intros Hr Hl.
  assert (Hc : wl_cut (I ++ l) = (bodies_of I, rest_of I ++ l))
    by exact (wl_cut_app_nonl I l Hl).
  rewrite {1}/rest_of Hc. cbn [snd]. by rewrite Hr.
Qed.

Lemma ll_pro_rounds_one : pro_rounds [0] = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma ll_prompt_len : length u_prompt = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma ll_pro_alts_0 : pro_alts !!! 0 = u_prompt.
Proof. reflexivity. Qed.

Lemma ll_prompt_tail : u_prompt !! 1 = Some (u_prompt !!! 1).
Proof. vm_compute. reflexivity. Qed.

Lemma ll_pro_of_open_snoc_eq (ps : list nat) (a : nat) :
  ~ pro_done ps -> pro_of (ps ++ [a]) = pro_of ps ++ pro_alts !!! a.
Proof. intros Hnd. by rewrite (pro_of_open_app ps [a] Hnd) pro_of_singleton. Qed.

(* ====================================================================== *)
(*  1.  THE HOOKS: what the shell's own code names in a model              *)
(* ====================================================================== *)
Record lm_hooks (M : lmodel) := MkLMH {
  (* the alternatives whose output is a function of the LINE alone --
     the only ones a block-byte lookup may be premise-free at *)
  lmh_free : lm_alt M -> bool;
  (* the state [lm_ab] reads a state-free continuation at *)
  lmh_st0 : lm_st M;
  (* per line: the CODE of the shell's fork panic, of the exec failure
     (with its bytes, which name the command), and -- WHERE THE MODEL HAS
     ONE -- of a silent round, the bare prompt and nothing moved.  It is
     optional (sync design section 2): at a line sh forks for, the command
     that did not run says so ([FileDisc.ROom]), and a model with a silent
     alternative there would read "did not run" into any transcript *)
  lmh_pan : lm_line M -> nat;
  lmh_exf : lm_line M -> nat;
  lmh_exfb : lm_line M -> list (bv 8);
  lmh_noc : lm_line M -> option nat;
  (* the range condition is decidable, which is what guards [lm_ab] *)
  lmh_ok_dec : forall s l a, Decision (lm_ok M s l a);

  lmh_free_cont : forall s s' l a,
    lmh_free a = true -> lm_cont M s l a = lm_cont M s' l a;
  lmh_free_term : forall a, lmh_free a = true -> lm_term M a = false;
  (* ...and whose ADMISSIBILITY is a function of the line alone: a byte
     lookup at [lm_ab] (read at [lmh_st0]) says it at the round's state *)
  lmh_free_ok : forall s s' l a,
    lmh_free a = true -> lm_ok M s l a -> lm_ok M s' l a;
  lmh_pan_ok : forall s l, lm_ok M s l (lm_dec M (lmh_pan l));
  lmh_pan_free : forall l, lmh_free (lm_dec M (lmh_pan l)) = true;
  lmh_pan_panic : forall l, lm_panic M (lm_dec M (lmh_pan l)) = true;
  lmh_exf_ok : forall s l, lm_ok M s l (lm_dec M (lmh_exf l));
  lmh_exf_free : forall l, lmh_free (lm_dec M (lmh_exf l)) = true;
  lmh_exf_nopanic : forall l, lm_panic M (lm_dec M (lmh_exf l)) = false;
  lmh_exf_cont : forall s l, lm_cont M s l (lm_dec M (lmh_exf l)) = lmh_exfb l;
  lmh_noc_ok : forall s l c, lmh_noc l = Some c -> lm_ok M s l (lm_dec M c);
  lmh_noc_free : forall l c, lmh_noc l = Some c -> lmh_free (lm_dec M c) = true;
  lmh_noc_nopanic : forall l c, lmh_noc l = Some c -> lm_panic M (lm_dec M c) = false;
  lmh_noc_cont : forall s l c, lmh_noc l = Some c -> lm_cont M s l (lm_dec M c) = u_prompt;
  (* what a WRITER knows of a continuation, holding none of the
     discipline's premises: it ends in the prompt, and it is not empty
     (nor is the out-of-range decode's, which is what a cursor past the
     choice list reads) *)
  lmh_cont_prompt : forall s l a,
    lm_ok M s l a -> lm_panic M a = false -> lm_term M a = false ->
    exists u, lm_cont M s l a = u ++ u_prompt;
  lmh_cont_nonnil : forall s l a,
    lm_ok M s l a \/ a = lm_dec M 0 -> lm_cont M s l a <> [];
}.
Arguments lmh_free {M} _ _.
Arguments lmh_st0 {M} _.
Arguments lmh_pan {M} _ _.
Arguments lmh_exf {M} _ _.
Arguments lmh_exfb {M} _ _.
Arguments lmh_noc {M} _ _.
Arguments lmh_ok_dec {M} _ _ _ _.
Arguments lmh_free_cont {M} _.
Arguments lmh_free_term {M} _.
Arguments lmh_free_ok {M} _.
Arguments lmh_pan_ok {M} _.
Arguments lmh_pan_free {M} _.
Arguments lmh_pan_panic {M} _.
Arguments lmh_exf_ok {M} _.
Arguments lmh_exf_free {M} _.
Arguments lmh_exf_nopanic {M} _.
Arguments lmh_exf_cont {M} _.
Arguments lmh_noc_ok {M} _.
Arguments lmh_noc_free {M} _.
Arguments lmh_noc_nopanic {M} _.
Arguments lmh_noc_cont {M} _.
Arguments lmh_cont_prompt {M} _.
Arguments lmh_cont_nonnil {M} _.

(* an instance whose silent round is TOTAL ([Some] at every line) proves
   the [lmh_noc] laws from its landed per-line ones through this *)
Lemma lmh_noc_some (P : nat -> Prop) (x c : nat) : P x -> Some x = Some c -> P c.
Proof. intros HP Hc. injection Hc as <-. exact HP. Qed.

Section line_model_links.
  Context (M : lmodel) (L : lm_laws M) (K : lm_hooks M).

  (* ================================================================== *)
  (*  2.  THE MODEL'S STRUCTURE THE STREAM SPENDS                        *)
  (* ================================================================== *)
  Lemma lm_upto_ext cs1 cs2 s bs1 bs2 q :
    (forall j, j < q -> cs1 !!! j = cs2 !!! j) ->
    (forall j, j < q -> bs1 !!! j = bs2 !!! j) ->
    lm_upto M cs1 s bs1 q = lm_upto M cs2 s bs2 q.
  Proof using.
    intros Hc Hb. induction q as [| q IH]; [reflexivity |].
    cbn [lm_upto]. rewrite IH; [| intros j Hj; apply Hc; lia
                              | intros j Hj; apply Hb; lia].
    by rewrite /lm_at (Hc q ltac:(lia)) (Hb q ltac:(lia)).
  Qed.

  Lemma lm_pro_idx_app_le (cs z : list nat) (q : nat) :
    q <= length cs -> lm_pro_idx M (cs ++ z) q = lm_pro_idx M cs q.
  Proof using.
    intro Hq. apply (lm_pro_idx_ext M (cs ++ z) cs q); [| lia].
    intros j Hj. rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
  Qed.

  Lemma lm_pro_idx_nlines (cs : list nat) (I : list (bv 8)) :
    I <> [] -> rest_of I = [] ->
    lm_panic M (lm_at M cs (nlines I - 1)) = true ->
    S (lm_pro_idx M cs (nlines I - 1)) = lm_pro_idx M cs (nlines I).
  Proof using.
    intros H0 Hm H3. pose proof (nlines_pos_of_rest_nil I H0 Hm) as Hq.
    replace (nlines I) with (S (nlines I - 1)) at 2 by lia.
    symmetry. by apply lm_pro_idx_Sp.
  Qed.

  Lemma lm_pro_idx_snoc_ne (cs : list nat) (a : nat) :
    lm_panic M (lm_dec M a) = false ->
    lm_pro_idx M (cs ++ [a]) (S (length cs)) = lm_pro_idx M cs (length cs).
  Proof using.
    intros Ha. rewrite lm_pro_idx_S /lm_at ll_snoc_lookup_total Ha.
    rewrite (lm_pro_idx_ext M (cs ++ [a]) cs (length cs)
               ltac:(intros j Hj; rewrite list_lookup_total_alt lookup_app_l;
                     [by rewrite -list_lookup_total_alt | lia])
               (length cs) ltac:(lia)).
    lia.
  Qed.

  Lemma lm_pro_idx_snoc_pan (cs : list nat) (a : nat) :
    lm_panic M (lm_dec M a) = true ->
    lm_pro_idx M (cs ++ [a]) (S (length cs)) = S (lm_pro_idx M cs (length cs)).
  Proof using.
    intros Ha. rewrite lm_pro_idx_S /lm_at ll_snoc_lookup_total Ha.
    rewrite (lm_pro_idx_ext M (cs ++ [a]) cs (length cs)
               ltac:(intros j Hj; rewrite list_lookup_total_alt lookup_app_l;
                     [by rewrite -list_lookup_total_alt | lia])
               (length cs) ltac:(lia)).
    lia.
  Qed.

  Lemma lm_at_ge (cs : list nat) (i : nat) :
    length cs <= i -> lm_at M cs i = lm_dec M 0.
  Proof using.
    intro Hi. rewrite /lm_at list_lookup_total_alt (lookup_ge_None_2 cs i Hi).
    reflexivity.
  Qed.

  Lemma lm_panic_ge (B : lm_byte_laws M) (cs : list nat) (i : nat) :
    length cs <= i -> lm_panic M (lm_at M cs i) = false.
  Proof using. intro Hi. rewrite (lm_at_ge cs i Hi). exact (lmb_dec0_nopanic B). Qed.

  (* the pin, and the round it settles *)
  Lemma lm_pro_pin_nil (ps cs : list nat) : lm_pro_pin M ps cs [].
  Proof using. intros q Hq. rewrite nstarted_nil in Hq. lia. Qed.

  Lemma lm_pro_pin_at (ps cs : list nat) (I : list (bv 8)) (q : nat) :
    lm_pro_pin M ps cs I -> q < nstarted I ->
    lm_pro_idx M cs q < pro_rounds ps.
  Proof using. intros H Hq. exact (H q Hq). Qed.

  Lemma lm_pro_pin_mono ps ps' cs I :
    ps `prefix_of` ps' -> lm_pro_pin M ps cs I -> lm_pro_pin M ps' cs I.
  Proof using.
    intros [z ->] Hpin q Hq. pose proof (Hpin q Hq) as H.
    rewrite pro_rounds_app. lia.
  Qed.

  Lemma lm_pro_pin_round_le (ps cs : list nat) (I : list (bv 8)) :
    rest_of I = [] ->
    (I = [] \/ lm_panic M (lm_at M cs (nlines I - 1)) = true) ->
    lm_pro_pin M ps cs I ->
    lm_pro_idx M cs (nlines I) <= pro_rounds ps.
  Proof using.
    intros Hm Ho Hpin. destruct (decide (I = [])) as [-> | Hn0].
    { rewrite nlines_nil. cbn [lm_pro_idx]. lia. }
    assert (H3 : lm_panic M (lm_at M cs (nlines I - 1)) = true)
      by (destruct Ho as [Hz | H3]; [by destruct (Hn0 Hz) | exact H3]).
    pose proof (nlines_pos_of_rest_nil I Hn0 Hm) as Hq.
    pose proof (lm_pro_idx_nlines cs I Hn0 Hm H3) as Hs.
    assert (Hlt : nlines I - 1 < nstarted I)
      by (pose proof (nlines_le_nstarted I); lia).
    pose proof (Hpin (nlines I - 1) Hlt). lia.
  Qed.

  (* ================================================================== *)
  (*  3.  THE STREAM                                                     *)
  (* ================================================================== *)
  Lemma lm_pending_at_ps_ext ps ps' cs s0 I :
    ps `prefix_of` ps' ->
    lm_pro_idx M cs (nlines I) < pro_rounds ps ->
    lm_pending_at M ps cs s0 I = lm_pending_at M ps' cs s0 I.
  Proof using.
    intros Hp Hr. rewrite /lm_pending_at. case_decide as H0.
    { subst I. apply (pro_of_from_done_ext 0); [exact Hp |].
      rewrite nlines_nil in Hr. cbn [lm_pro_idx] in Hr. exact Hr. }
    case_decide as Hm; [| done].
    rewrite /lm_cont_at. f_equal.
    destruct (lm_panic M (lm_at M cs (nlines I - 1))) eqn:H3; [| done].
    rewrite (lm_pro_idx_nlines cs I H0 Hm H3).
    by apply pro_of_from_done_ext.
  Qed.

  Lemma lm_pending_at_round_pre (ps cs : list nat) (s0 : lm_st M)
      (I : list (bv 8)) :
    rest_of I = [] ->
    (I = [] \/ lm_panic M (lm_at M cs (nlines I - 1)) = true) ->
    lm_pending_at M ps cs s0 I
    = lm_wr_pre I ++ pro_of (pro_from (lm_pro_idx M cs (nlines I)) ps).
  Proof using L.
    intros Hm Hopen. rewrite /lm_pending_at /lm_wr_pre. case_decide as H0.
    - subst I. rewrite nlines_nil. by cbn [lm_pro_idx pro_from app].
    - rewrite decide_True; [| exact Hm].
      assert (H3 : lm_panic M (lm_at M cs (nlines I - 1)) = true)
        by (destruct Hopen as [Hn | H3]; [by destruct (H0 Hn) | exact H3]).
      rewrite /lm_cont_at H3 (lm_pro_idx_nlines cs I H0 Hm H3).
      by rewrite (lml_cont_panic L _ _ _ H3).
  Qed.

  Lemma lm_pending_at_round_snoc (ps cs : list nat) (s0 : lm_st M)
      (I : list (bv 8)) (a : nat) :
    rest_of I = [] ->
    (I = [] \/ lm_panic M (lm_at M cs (nlines I - 1)) = true) ->
    ~ pro_done (pro_from (lm_pro_idx M cs (nlines I)) ps) ->
    lm_pro_idx M cs (nlines I) <= pro_rounds ps ->
    lm_pending_at M (ps ++ [a]) cs s0 I
    = lm_pending_at M ps cs s0 I ++ pro_alts !!! a.
  Proof using L.
    intros Hm Hr Hnd Hle.
    rewrite (lm_pending_at_round_pre (ps ++ [a]) cs s0 I Hm Hr)
            (lm_pending_at_round_pre ps cs s0 I Hm Hr)
            (pro_from_snoc_le (lm_pro_idx M cs (nlines I)) ps a Hle)
            (ll_pro_of_open_snoc_eq _ a Hnd).
    by rewrite app_assoc.
  Qed.

  Lemma lm_pending_at_cs_ext ps cs0 cs s0 I :
    cs0 `prefix_of` cs -> nlines I <= length cs0 ->
    lm_pending_at M ps cs0 s0 I = lm_pending_at M ps cs s0 I.
  Proof using.
    intros Hp Hn. rewrite /lm_pending_at.
    case_decide as H0; [done |].
    case_decide as Hr; [| done].
    pose proof (nlines_pos_of_rest_nil I H0 Hr) as Hpos.
    assert (Hlk : forall j, j < nlines I -> cs0 !!! j = cs !!! j).
    { intros j Hj. symmetry. apply (ll_lta_prefix cs0 cs j Hp). lia. }
    rewrite /lm_cont_at /lm_at (Hlk (nlines I - 1) ltac:(lia)).
    rewrite (lm_upto_ext cs0 cs s0 (bodies_of I) (bodies_of I)
               (nlines I - 1) ltac:(intros j Hj; apply Hlk; lia)
               ltac:(intros j Hj; reflexivity)).
    by rewrite (lm_pro_idx_ext M cs0 cs (nlines I) Hlk (nlines I - 1)
                  ltac:(lia)).
  Qed.

  Lemma lm_pending_at_cs_prefix ps0 ps cs0 cs s0 I :
    ps0 `prefix_of` ps -> cs0 `prefix_of` cs ->
    nlines I <= length cs0 ->
    lm_pro_idx M cs0 (nlines I) < pro_rounds ps0 ->
    lm_pending_at M ps0 cs0 s0 I = lm_pending_at M ps cs s0 I.
  Proof using.
    intros Hps Hcs Hn Hr.
    rewrite (lm_pending_at_ps_ext ps0 ps cs0 s0 I Hps Hr).
    by apply lm_pending_at_cs_ext.
  Qed.

  Lemma lm_pending_at_stage_ext ps0 ps cs0 cs s0 I0 J :
    ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> lm_pro_pin M ps0 cs0 I0 ->
    nlines (removelast I0) <= length cs0 ->
    J `prefix_of` I0 -> J <> I0 ->
    lm_pending_at M ps0 cs0 s0 J = lm_pending_at M ps cs s0 J.
  Proof using.
    intros Hps Hcs Hpin Hn HJ Hne.
    assert (Hjl : nlines J <= length cs0).
    { etrans; [| exact Hn].
      apply nlines_prefix, (ll_prefix_of_removelast J I0 HJ Hne). }
    apply (lm_pending_at_cs_prefix ps0 ps cs0 cs s0 J Hps Hcs Hjl).
    apply Hpin. exact (nstarted_strict J I0 HJ Hne).
  Qed.

  Lemma lm_proc_before_from_app ps cs s0 pre I1 I2 :
    lm_proc_before_from M ps cs s0 pre (I1 ++ I2)
    = lm_proc_before_from M ps cs s0 pre I1
      ++ lm_proc_before_from M ps cs s0 (pre ++ I1) I2.
  Proof using.
    revert pre. induction I1 as [| b I1 IH]; intros pre.
    - cbn [lm_proc_before_from app]. by rewrite app_nil_r.
    - cbn [app lm_proc_before_from]. rewrite IH app_assoc.
      by rewrite ll_app_snoc.
  Qed.

  Lemma lm_proc_before_app ps cs s0 I k :
    lm_proc_before M ps cs s0 (I ++ k)
    = lm_proc_before M ps cs s0 I ++ lm_proc_before_from M ps cs s0 I k.
  Proof using.
    rewrite /lm_proc_before lm_proc_before_from_app. by cbn [app].
  Qed.

  Lemma lm_proc_before_nil ps cs s0 : lm_proc_before M ps cs s0 [] = [].
  Proof using. reflexivity. Qed.

  Lemma lm_proc_before_snoc ps cs s0 I b :
    lm_proc_before M ps cs s0 (I ++ [b]) = lm_proc_stream M ps cs s0 I.
  Proof using.
    rewrite lm_proc_before_app /lm_proc_stream. cbn [lm_proc_before_from].
    by rewrite app_nil_r.
  Qed.

  Lemma lm_proc_before_prefix ps cs s0 I I' :
    I `prefix_of` I' ->
    lm_proc_before M ps cs s0 I `prefix_of` lm_proc_before M ps cs s0 I'.
  Proof using. intros [z ->]. rewrite lm_proc_before_app. by eexists. Qed.

  Lemma lm_proc_stream_before ps cs s0 I I' :
    I `prefix_of` I' -> I <> I' ->
    lm_proc_stream M ps cs s0 I `prefix_of` lm_proc_before M ps cs s0 I'.
  Proof using.
    intros [z Hz] Hne. destruct z as [| b z].
    { exfalso. apply Hne. by rewrite Hz app_nil_r. }
    rewrite Hz lm_proc_before_app /lm_proc_stream. cbn [lm_proc_before_from].
    rewrite app_assoc. by eexists.
  Qed.

  Lemma lm_proc_stream_mono ps cs s0 I I' :
    I `prefix_of` I' ->
    lm_proc_stream M ps cs s0 I `prefix_of` lm_proc_stream M ps cs s0 I'.
  Proof using.
    intros Hp. destruct (decide (I = I')) as [-> | Hne]; [reflexivity |].
    etrans; [exact (lm_proc_stream_before ps cs s0 I I' Hp Hne) |].
    rewrite /lm_proc_stream. by eexists.
  Qed.

  Lemma lm_proc_before_head (ps cs : list nat) (s0 : lm_st M)
      (I : list (bv 8)) :
    I <> [] ->
    lm_pending_at M ps cs s0 [] `prefix_of` lm_proc_before M ps cs s0 I.
  Proof using.
    destruct I as [| b I']; [done |]. intros _.
    rewrite /lm_proc_before. cbn [lm_proc_before_from]. by eexists.
  Qed.

  Lemma lm_proc_before_from_ext ps0 ps cs0 cs s0 pre I :
    (forall J, pre `prefix_of` J -> J `prefix_of` pre ++ I -> J <> pre ++ I ->
       lm_pending_at M ps0 cs0 s0 J = lm_pending_at M ps cs s0 J) ->
    lm_proc_before_from M ps0 cs0 s0 pre I
    = lm_proc_before_from M ps cs s0 pre I.
  Proof using.
    revert pre. induction I as [| b I IH]; intros pre Hj; [done |].
    assert (Hshape : (pre ++ [b]) ++ I = pre ++ b :: I) by apply ll_app_snoc.
    assert (Hhere : lm_pending_at M ps0 cs0 s0 pre
                    = lm_pending_at M ps cs s0 pre).
    { apply Hj.
      - reflexivity.
      - by eexists.
      - apply (ll_app_cons_ne pre b I). }
    cbn [lm_proc_before_from]. rewrite Hhere. f_equal.
    apply IH. intros J H1 H2 H3. apply Hj.
    - etrans; [| exact H1]. by eexists.
    - rewrite -Hshape. exact H2.
    - rewrite -Hshape. exact H3.
  Qed.

  Lemma lm_proc_before_ext ps0 ps cs0 cs s0 I :
    (forall J, J `prefix_of` I -> J <> I ->
       lm_pending_at M ps0 cs0 s0 J = lm_pending_at M ps cs s0 J) ->
    lm_proc_before M ps0 cs0 s0 I = lm_proc_before M ps cs s0 I.
  Proof using.
    intros Hj. rewrite /lm_proc_before. apply lm_proc_before_from_ext.
    intros J _ H2 H3. rewrite app_nil_l in H2, H3. by apply Hj.
  Qed.

  Lemma lm_proc_before_cs_prefix ps0 ps cs0 cs s0 I0 :
    ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> lm_pro_pin M ps0 cs0 I0 ->
    nlines (removelast I0) <= length cs0 ->
    lm_proc_before M ps0 cs0 s0 I0 = lm_proc_before M ps cs s0 I0.
  Proof using.
    intros Hps Hcs Hpin Hn. apply lm_proc_before_ext.
    intros J HJ Hne.
    exact (lm_pending_at_stage_ext ps0 ps cs0 cs s0 I0 J Hps Hcs Hpin Hn HJ Hne).
  Qed.

  Lemma lm_proc_stream_round_banner (ps cs : list nat) (s0 : lm_st M)
      (I : list (bv 8)) (j i : nat) (pre : list (bv 8)) (b : bv 8) :
    lm_pending_at M ps cs s0 I
    = pre ++ pro_of (pro_from (lm_pro_idx M cs (nlines I)) ps) ->
    pro_from (lm_pro_idx M cs (nlines I)) ps = pro_fail j ++ [3] ->
    u_banner !! i = Some b ->
    lm_proc_stream M ps cs s0 I
      !! (length (lm_proc_before M ps cs s0 I) + length pre + pro_round * j + i)
    = Some b.
  Proof using.
    intros Hshape Hopen Hb.
    rewrite /lm_proc_stream Hshape Hopen.
    replace (length (lm_proc_before M ps cs s0 I) + length pre + pro_round * j + i)
      with (length (lm_proc_before M ps cs s0 I)
            + (length pre + (pro_round * j + i))) by lia.
    rewrite (lookup_app_shift (lm_proc_before M ps cs s0 I)) (lookup_app_shift pre).
    by apply pro_of_fail_banner.
  Qed.

  Lemma lm_proc_stream_round_banner_open (ps cs : list nat) (s0 : lm_st M)
      (I : list (bv 8)) (j i : nat) (b : bv 8) :
    rest_of I = [] ->
    (I = [] \/ lm_panic M (lm_at M cs (nlines I - 1)) = true) ->
    pro_from (lm_pro_idx M cs (nlines I)) ps = pro_fail j ++ [3] ->
    u_banner !! i = Some b ->
    lm_proc_stream M ps cs s0 I
      !! (length (lm_proc_before M ps cs s0 I) + length (lm_wr_pre I)
          + pro_round * j + i)
    = Some b.
  Proof using L.
    intros Hr Ho Hopen Hb.
    apply (lm_proc_stream_round_banner ps cs s0 I j i _ b);
      [by apply lm_pending_at_round_pre | exact Hopen | exact Hb].
  Qed.

  (* THE GAP LAW: nothing is pending strictly inside a line *)
  Lemma lm_proc_before_from_gap (ps cs : list nat) (s0 : lm_st M)
      (pre k : list (bv 8)) :
    (forall J : list (bv 8), J `prefix_of` k -> J <> k ->
       lm_pending_at M ps cs s0 (pre ++ J) = []) ->
    lm_proc_before_from M ps cs s0 pre k = [].
  Proof using.
    revert pre. induction k as [| b k IH]; intros pre Hj; [reflexivity |].
    assert (H0 : lm_pending_at M ps cs s0 pre = []).
    { rewrite -(app_nil_r pre). apply Hj; [apply prefix_nil | discriminate]. }
    cbn [lm_proc_before_from]. rewrite H0 app_nil_l.
    apply IH. intros J HJ Hne.
    rewrite (ll_app_snoc pre b J). apply Hj.
    - destruct HJ as [z ->]. exists z. by cbn [app].
    - intros Heq. apply Hne. by injection Heq.
  Qed.

  Lemma lm_proc_before_line (ps cs : list nat) (s0 : lm_st M)
      (I l : list (bv 8)) :
    rest_of I = [] -> wl_nl ∉ l ->
    lm_proc_before M ps cs s0 (I ++ l ++ [wl_nl]) = lm_proc_stream M ps cs s0 I.
  Proof using.
    intros Hr Hl. rewrite lm_proc_before_app /lm_proc_stream. f_equal.
    destruct l as [| b l'].
    - cbn [app lm_proc_before_from]. by rewrite app_nil_r.
    - destruct (wl_nonl_cons b l' Hl) as [Hb Hl'].
      assert (Hgap : lm_proc_before_from M ps cs s0 (I ++ [b]) (l' ++ [wl_nl]) = []).
      { apply lm_proc_before_from_gap. intros J HJ Hne.
        assert (HJl : J `prefix_of` l').
        { rewrite -(ll_removelast_snoc l' wl_nl).
          exact (ll_prefix_of_removelast J (l' ++ [wl_nl]) HJ Hne). }
        assert (HJn : wl_nl ∉ J).
        { intro Hin. destruct HJl as [z ->].
          apply Hl'. apply elem_of_app. by left. }
        assert (Hshape : (I ++ [b]) ++ J = I ++ (b :: J)) by apply ll_app_snoc.
        rewrite Hshape /lm_pending_at.
        rewrite decide_False;
          [| intros Hq; by destruct (app_eq_nil I (b :: J) Hq) as [_ Hc]].
        rewrite decide_False; [reflexivity |].
        rewrite (ll_rest_of_app_nonl I (b :: J) Hr (wl_nonl_cons_2 b J Hb HJn)).
        discriminate. }
      cbn [app lm_proc_before_from]. rewrite Hgap app_nil_r. reflexivity.
  Qed.

  (* ================================================================== *)
  (*  4.  THE LINE THAT WAS TYPED, AND ITS ALTERNATIVES' OUTPUT           *)
  (* ================================================================== *)

  #[local] Instance lm_ok_dec_hook s l a : Decision (lm_ok M s l a) := lmh_ok_dec K s l a.

  (* the line the last COMPLETE body of [I] parses to *)
  Definition lm_line_at (I : list (bv 8)) : lm_line M :=
    lm_of M (bodies_of I !!! (nlines I - 1)).

  (* THE RECORD'S [lk_ab]: the block alternative [a] owes at input [I],
     GUARDED so that a byte lookup alone says the alternative is
     admissible and state-free -- which is what makes the block-byte
     step premise-free.  Both are read at the hook's state [lmh_st0]; a
     state-free alternative is admissible at every state
     ([lmh_free_ok]) *)
  Definition lm_ab (I : list (bv 8)) (a : nat) : list (bv 8) :=
    if decide (lm_ok M (lmh_st0 K) (lm_line_at I) (lm_dec M a)
               /\ lmh_free K (lm_dec M a) = true)
    then lm_cont M (lmh_st0 K) (lm_line_at I) (lm_dec M a) else [].

  (* THE RECORD'S [lk_apr]: the alternative ends with the shell's prompt,
     i.e. it is admissible, state-free and does NOT reopen the prologue *)
  Definition lm_apr (I : list (bv 8)) (a : nat) : Prop :=
    lm_ok M (lmh_st0 K) (lm_line_at I) (lm_dec M a) /\ lmh_free K (lm_dec M a) = true
    /\ lm_panic M (lm_dec M a) = false.

  (* ...with the state kept: the era's boot state and the choice list
     filed so far determine the round's state, and the block at it *)
  Definition lm_abs (s0 : lm_st M) (cs : list nat) (I : list (bv 8)) (a : nat)
    : list (bv 8) :=
    lm_cont M (lm_upto M cs s0 (bodies_of I) (nlines I - 1)) (lm_line_at I)
      (lm_dec M a).

  (* [lm_apr] without state-freedom: admissible (at every state, since the
     round's is not in scope here), and not a panic *)
  Definition lm_aprs (I : list (bv 8)) (a : nat) : Prop :=
    (forall s, lm_ok M s (lm_line_at I) (lm_dec M a))
    /\ lm_panic M (lm_dec M a) = false
    /\ lm_term M (lm_dec M a) = false.

  Lemma lm_apr_aprs (I : list (bv 8)) (a : nat) : lm_apr I a -> lm_aprs I a.
  Proof using K.
    intros (H1 & H2 & H3). split; [intros s; exact (lmh_free_ok K _ s _ _ H2 H1) |].
    split; [exact H3 |]. exact (lmh_free_term K _ H2).
  Qed.

  Lemma lm_ab_ok (I : list (bv 8)) (a i : nat) (b : bv 8) :
    lm_ab I a !! i = Some b ->
    lm_ok M (lmh_st0 K) (lm_line_at I) (lm_dec M a) /\ lmh_free K (lm_dec M a) = true.
  Proof using K.
    rewrite /lm_ab. case_decide as H; [intros _; exact H |].
    intros Hq. rewrite lookup_nil in Hq. discriminate.
  Qed.

  Lemma lm_ab_is (I : list (bv 8)) (a : nat) :
    lm_ok M (lmh_st0 K) (lm_line_at I) (lm_dec M a) -> lmh_free K (lm_dec M a) = true ->
    lm_ab I a = lm_cont M (lmh_st0 K) (lm_line_at I) (lm_dec M a).
  Proof using K. intros Hok Hfr. rewrite /lm_ab decide_True; [reflexivity | done]. Qed.

  Lemma lm_ab_at (I : list (bv 8)) (a : nat) (s : lm_st M) :
    lm_ok M (lmh_st0 K) (lm_line_at I) (lm_dec M a) -> lmh_free K (lm_dec M a) = true ->
    lm_ab I a = lm_cont M s (lm_line_at I) (lm_dec M a).
  Proof using K.
    intros Hok Hfr. rewrite (lm_ab_is I a Hok Hfr).
    exact (lmh_free_cont K _ _ _ _ Hfr).
  Qed.

  Lemma lm_abs_ab (s0 : lm_st M) (cs : list nat) (I : list (bv 8)) (a : nat) :
    lm_apr I a -> lm_abs s0 cs I a = lm_ab I a.
  Proof using K.
    intros (Hok & Hfr & _). rewrite /lm_abs. symmetry. exact (lm_ab_at I a _ Hok Hfr).
  Qed.

  Lemma lm_abs_prompt (s0 : lm_st M) (cs : list nat) (I : list (bv 8)) (a : nat) :
    lm_aprs I a -> exists pre : list (bv 8), lm_abs s0 cs I a = pre ++ u_prompt.
  Proof using K.
    intros (Hok & Hp & Ht). rewrite /lm_abs.
    exact (lmh_cont_prompt K _ _ _ (Hok _) Hp Ht).
  Qed.

  Lemma ll_prompt_tail_facts (x u : list (bv 8)) :
    x = u ++ u_prompt ->
    2 <= length x
    /\ x !! (length x - 2) = Some (u_prompt !!! 0)
    /\ x !! (length x - 1) = Some (u_prompt !!! 1).
  Proof using.
    intros ->. rewrite length_app ll_prompt_len.
    split; [lia |]. split.
    - replace (length u + 2 - 2) with (length u + 0) by lia.
      rewrite lookup_app_shift. vm_compute. reflexivity.
    - replace (length u + 2 - 1) with (length u + 1) by lia.
      rewrite lookup_app_shift. vm_compute. reflexivity.
  Qed.

  Lemma lm_abs_len_ge2 (s0 : lm_st M) (cs : list nat) (I : list (bv 8)) (a : nat) :
    lm_aprs I a -> 2 <= length (lm_abs s0 cs I a).
  Proof using K.
    intros Hpr. destruct (lm_abs_prompt s0 cs I a Hpr) as [u Hu].
    exact (proj1 (ll_prompt_tail_facts _ u Hu)).
  Qed.

  Lemma lm_abs_dollar (s0 : lm_st M) (cs : list nat) (I : list (bv 8)) (a : nat) :
    lm_aprs I a ->
    lm_abs s0 cs I a !! (length (lm_abs s0 cs I a) - 2) = Some (u_prompt !!! 0).
  Proof using K.
    intros Hpr. destruct (lm_abs_prompt s0 cs I a Hpr) as [u Hu].
    exact (proj1 (proj2 (ll_prompt_tail_facts _ u Hu))).
  Qed.

  Lemma lm_abs_space (s0 : lm_st M) (cs : list nat) (I : list (bv 8)) (a : nat) :
    lm_aprs I a ->
    lm_abs s0 cs I a !! (length (lm_abs s0 cs I a) - 1) = Some (u_prompt !!! 1).
  Proof using K.
    intros Hpr. destruct (lm_abs_prompt s0 cs I a Hpr) as [u Hu].
    exact (proj2 (proj2 (ll_prompt_tail_facts _ u Hu))).
  Qed.

  (* THE PROMPT-FREE BODY of a block alternative (program-specs SS3.4e):
     what the round's CHILD writes.  The alternative ends with the shell's
     prompt ([lm_abs_prompt]), which the shell writes after the child has
     exited, so a device owing the whole alternative can never be drained
     by the child; one owing the body can. *)
  Definition lm_body (s0 : lm_st M) (cs : list nat) (I : list (bv 8)) (a : nat)
    : list (bv 8) :=
    take (length (lm_abs s0 cs I a) - 2) (lm_abs s0 cs I a).

  Lemma lm_body_length (s0 : lm_st M) (cs : list nat) (I : list (bv 8)) (a : nat) :
    length (lm_body s0 cs I a) = length (lm_abs s0 cs I a) - 2.
  Proof using. rewrite /lm_body length_take. lia. Qed.

  (* a byte of the body is the alternative's byte *)
  Lemma lm_body_lookup (s0 : lm_st M) (cs : list nat) (I : list (bv 8)) (a j : nat) :
    j < length (lm_body s0 cs I a) ->
    lm_body s0 cs I a !! j = lm_abs s0 cs I a !! j.
  Proof using.
    intros Hj. rewrite lm_body_length in Hj. rewrite /lm_body.
    apply lookup_take. lia.
  Qed.

  Lemma lm_body_lookup_Some (s0 : lm_st M) (cs : list nat) (I : list (bv 8))
      (a j : nat) (b : bv 8) :
    lm_body s0 cs I a !! j = Some b -> lm_abs s0 cs I a !! j = Some b.
  Proof using.
    intros Hb. rewrite -(lm_body_lookup s0 cs I a j); [exact Hb |].
    exact (lookup_lt_Some _ _ _ Hb).
  Qed.

  (* the alternative is its body and the prompt *)
  Lemma lm_abs_body (s0 : lm_st M) (cs : list nat) (I : list (bv 8)) (a : nat) :
    lm_aprs I a -> lm_abs s0 cs I a = lm_body s0 cs I a ++ u_prompt.
  Proof using K.
    intros Hpr. destruct (lm_abs_prompt s0 cs I a Hpr) as [u Hu].
    rewrite /lm_body Hu length_app ll_prompt_len.
    replace (length u + 2 - 2) with (length u) by lia.
    rewrite take_app_length. reflexivity.
  Qed.

  Lemma lm_ab_len_ge2 (I : list (bv 8)) (a : nat) :
    lm_apr I a -> 2 <= length (lm_ab I a).
  Proof using K.
    intros Hpr. rewrite -(lm_abs_ab (lmh_st0 K) [] I a Hpr).
    exact (lm_abs_len_ge2 _ _ I a (lm_apr_aprs I a Hpr)).
  Qed.

  Lemma lm_ab_dollar (I : list (bv 8)) (a : nat) :
    lm_apr I a -> lm_ab I a !! (length (lm_ab I a) - 2) = Some (u_prompt !!! 0).
  Proof using K.
    intros Hpr. rewrite -(lm_abs_ab (lmh_st0 K) [] I a Hpr).
    exact (lm_abs_dollar _ _ I a (lm_apr_aprs I a Hpr)).
  Qed.

  Lemma lm_ab_space (I : list (bv 8)) (a : nat) :
    lm_apr I a -> lm_ab I a !! (length (lm_ab I a) - 1) = Some (u_prompt !!! 1).
  Proof using K.
    intros Hpr. rewrite -(lm_abs_ab (lmh_st0 K) [] I a Hpr).
    exact (lm_abs_space _ _ I a (lm_apr_aprs I a Hpr)).
  Qed.

  (* the three alternatives the shell's own code names, at the line typed *)
  Lemma lm_cont_pan (s : lm_st M) (l : lm_line M) :
    lm_cont M s l (lm_dec M (lmh_pan K l)) = alt_panic.
  Proof using L K. exact (lml_cont_panic L _ _ _ (lmh_pan_panic K l)). Qed.

  Lemma lm_ab_pan (I : list (bv 8)) : lm_ab I (lmh_pan K (lm_line_at I)) = alt_panic.
  Proof using L K.
    rewrite (lm_ab_is I _ (lmh_pan_ok K _ _) (lmh_pan_free K _)). apply lm_cont_pan.
  Qed.

  Lemma lm_ab_exf (I : list (bv 8)) :
    lm_ab I (lmh_exf K (lm_line_at I)) = lmh_exfb K (lm_line_at I).
  Proof using K.
    rewrite (lm_ab_is I _ (lmh_exf_ok K _ _) (lmh_exf_free K _)). apply lmh_exf_cont.
  Qed.

  Lemma lm_apr_exf (I : list (bv 8)) : lm_apr I (lmh_exf K (lm_line_at I)).
  Proof using K.
    split; [apply lmh_exf_ok |]. split; [apply lmh_exf_free | apply lmh_exf_nopanic].
  Qed.

  (* ...and the silent round, at a line whose model has one *)
  Lemma lm_ab_noc (I : list (bv 8)) (c : nat) :
    lmh_noc K (lm_line_at I) = Some c -> lm_ab I c = u_prompt.
  Proof using K.
    intros Hc. rewrite (lm_ab_is I _ (lmh_noc_ok K _ _ _ Hc) (lmh_noc_free K _ _ Hc)).
    exact (lmh_noc_cont K _ _ _ Hc).
  Qed.

  Lemma lm_apr_noc (I : list (bv 8)) (c : nat) :
    lmh_noc K (lm_line_at I) = Some c -> lm_apr I c.
  Proof using K.
    intros Hc. split; [exact (lmh_noc_ok K _ _ _ Hc) |].
    split; [exact (lmh_noc_free K _ _ Hc) | exact (lmh_noc_nopanic K _ _ Hc)].
  Qed.

  Lemma lm_ab_noc_len (I : list (bv 8)) (c : nat) :
    lmh_noc K (lm_line_at I) = Some c -> length (lm_ab I c) - 2 = 0.
  Proof using K. intros Hc. rewrite (lm_ab_noc I c Hc) ll_prompt_len. lia. Qed.

  (* ================================================================== *)
  (*  5.  THE PURE LEMMAS ([FileLinksLine] S2)                           *)
  (* ================================================================== *)
  Lemma lm_wr_blk_nonnil (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P : nat) : lm_wr_blk M ps cs s0 I P -> I <> [].
  Proof using.
    intros (_ & _ & Hn & _) Heq. rewrite Heq nlines_nil in Hn. discriminate.
  Qed.

  Lemma lm_wr_blk_lines (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P : nat) : lm_wr_blk M ps cs s0 I P -> nlines I = S (length cs).
  Proof using. by intros (_ & _ & Hn & _). Qed.

  Lemma lm_wr_blk_started (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P : nat) : lm_wr_blk M ps cs s0 I P -> nstarted I = S (length cs).
  Proof using.
    intros (_ & Hr & Hn & _). by rewrite (ll_nstarted_rest_nil I Hr) Hn.
  Qed.

  (* filing an alternative reads no round below the boundary *)
  Lemma lm_wr_blk_pin_snoc (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a : nat) : lm_wr_blk M ps cs s0 I P -> lm_pro_pin M ps (cs ++ [a]) I.
  Proof using.
    intros Hw. pose proof (lm_wr_blk_started ps cs s0 I P Hw) as Hst.
    destruct Hw as (Hpin & _).
    intros q Hq. rewrite Hst in Hq.
    rewrite (lm_pro_idx_ext M (cs ++ [a]) cs q
               ltac:(intros j Hj; rewrite list_lookup_total_alt lookup_app_l;
                     [by rewrite -list_lookup_total_alt | lia])
               q ltac:(lia)).
    apply Hpin. rewrite Hst. exact Hq.
  Qed.

  (* ...and it moves no byte of what is already out *)
  Lemma lm_wr_blk_low (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a : nat) :
    lm_wr_blk M ps cs s0 I P ->
    lm_proc_before M ps (cs ++ [a]) s0 I = lm_proc_before M ps cs s0 I.
  Proof using.
    intros Hw. pose proof Hw as (Hpin & Hr & Hn & _). symmetry.
    apply (lm_proc_before_cs_prefix ps ps cs (cs ++ [a]) s0 I
             ltac:(reflexivity) ltac:(by eexists) Hpin).
    rewrite (ll_nlines_removelast I Hr). lia.
  Qed.

  (* the round's state and choice at the boundary, once [a] is filed *)
  Lemma lm_blk_snoc_at (cs : list nat) (I : list (bv 8)) (a : nat) :
    nlines I = S (length cs) ->
    lm_at M (cs ++ [a]) (nlines I - 1) = lm_dec M a.
  Proof using.
    intros Hn. rewrite /lm_at.
    replace (nlines I - 1) with (length cs) by lia.
    by rewrite ll_snoc_lookup_total.
  Qed.

  Lemma lm_blk_snoc_upto (cs : list nat) (s0 : lm_st M) (I : list (bv 8)) (a : nat) :
    nlines I = S (length cs) ->
    lm_upto M (cs ++ [a]) s0 (bodies_of I) (nlines I - 1)
    = lm_upto M cs s0 (bodies_of I) (nlines I - 1).
  Proof using.
    intros Hn.
    apply (lm_upto_ext (cs ++ [a]) cs s0 (bodies_of I) (bodies_of I));
      [| intros j _; reflexivity ].
    intros j Hj. rewrite list_lookup_total_alt lookup_app_l; [| lia].
    by rewrite -list_lookup_total_alt.
  Qed.

  (* THE BLOCK THE ROUND OWES once alternative [a] is filed, at a
     non-panic alternative: exactly the block at the round's state *)
  Lemma lm_wr_blk_pending_s (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a : nat) :
    lm_wr_blk M ps cs s0 I P ->
    lm_panic M (lm_dec M a) = false ->
    lm_pending_at M ps (cs ++ [a]) s0 I = lm_abs s0 cs I a.
  Proof using.
    intros Hw Hnp.
    pose proof (lm_wr_blk_nonnil ps cs s0 I P Hw) as Hne.
    pose proof Hw as (_ & Hr & Hn & _).
    rewrite /lm_pending_at decide_False; [| exact Hne].
    rewrite decide_True; [| exact Hr].
    rewrite /lm_cont_at (lm_blk_snoc_at cs I a Hn) (lm_blk_snoc_upto cs s0 I a Hn)
            Hnp app_nil_r.
    reflexivity.
  Qed.

  Lemma lm_wr_blk_pending (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a : nat) :
    lm_wr_blk M ps cs s0 I P -> lm_apr I a ->
    lm_pending_at M ps (cs ++ [a]) s0 I = lm_ab I a.
  Proof using K.
    intros Hw Hpr. rewrite -(lm_abs_ab s0 cs I a Hpr).
    exact (lm_wr_blk_pending_s ps cs s0 I P a Hw (proj2 (proj2 Hpr))).
  Qed.

  (* THE STREAM BYTE THE WRITE LINK ASKS FOR *)
  Lemma lm_wr_blk_byte_s (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a j : nat) (b : bv 8) :
    lm_wr_blk M ps cs s0 I P -> lm_panic M (lm_dec M a) = false ->
    lm_abs s0 cs I a !! j = Some b ->
    lm_proc_stream M ps (cs ++ [a]) s0 I !! (P + j) = Some b.
  Proof using.
    intros Hw Hnp Hb. pose proof Hw as (_ & _ & _ & HP).
    rewrite /lm_proc_stream (lm_wr_blk_low ps cs s0 I P a Hw) lookup_app_r; [| lia].
    replace (P + j - length (lm_proc_before M ps cs s0 I)) with j by lia.
    by rewrite (lm_wr_blk_pending_s ps cs s0 I P a Hw Hnp).
  Qed.

  Lemma lm_wr_blk_byte (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a j : nat) (b : bv 8) :
    lm_wr_blk M ps cs s0 I P -> lm_apr I a ->
    lm_ab I a !! j = Some b ->
    lm_proc_stream M ps (cs ++ [a]) s0 I !! (P + j) = Some b.
  Proof using K.
    intros Hw Hpr Hb. rewrite -(lm_abs_ab s0 cs I a Hpr) in Hb.
    exact (lm_wr_blk_byte_s ps cs s0 I P a j b Hw (proj2 (proj2 Hpr)) Hb).
  Qed.

  (* the block's bytes are a PREFIX of what the round then owes -- an
     equality at a non-panic alternative, a prefix at the panic one (whose
     block runs on into the next round's prologue) *)
  Lemma lm_wr_blk_pending_pre (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a : nat) :
    lm_wr_blk M ps cs s0 I P ->
    lm_ok M (lmh_st0 K) (lm_line_at I) (lm_dec M a) -> lmh_free K (lm_dec M a) = true ->
    lm_ab I a `prefix_of` lm_pending_at M ps (cs ++ [a]) s0 I.
  Proof using K.
    intros Hw Hok Hfr.
    pose proof (lm_wr_blk_nonnil ps cs s0 I P Hw) as Hne.
    pose proof Hw as (_ & Hr & Hn & _).
    rewrite /lm_pending_at decide_False; [| exact Hne].
    rewrite decide_True; [| exact Hr].
    rewrite /lm_cont_at (lm_blk_snoc_at cs I a Hn) (lm_blk_snoc_upto cs s0 I a Hn)
            -(lm_ab_at I a _ Hok Hfr).
    by eexists.
  Qed.

  Lemma lm_wr_tail_snoc (ps cs : list nat) (a : nat) :
    lm_panic M (lm_dec M a) = false -> lm_wr_tail M ps cs -> lm_wr_tail M ps (cs ++ [a]).
  Proof using.
    intros Ha Ht. rewrite /lm_wr_tail length_app. cbn [length].
    rewrite Nat.add_1_r (lm_pro_idx_snoc_ne cs a Ha). exact Ht.
  Qed.

  (* ================================================================== *)
  (*  6.  THE ROUND'S BANNER, STILL OWED ([FileLinksLine] S3)            *)
  (* ================================================================== *)
  Lemma lm_wr_ban_pro (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8)) (P : nat) :
    lm_wr_ban M ps cs s0 I P -> lm_wr_pro M ps cs s0 I P.
  Proof using L.
    intros (Hpin & Hm & Hdv & Hr & (j & Hopen & HP)).
    rewrite /lm_wr_pro. split_and!; try assumption.
    - rewrite Hopen. exact (pro_done_fail j).
    - rewrite /lm_proc_stream
              (length_app (lm_proc_before M ps cs s0 I) (lm_pending_at M ps cs s0 I))
              (lm_pending_at_round_pre ps cs s0 I Hm Hr)
              (length_app (lm_wr_pre I)
                 (pro_of (pro_from (lm_pro_idx M cs (nlines I)) ps)))
              Hopen pro_of_fail_length HP.
      lia.
  Qed.

  Lemma lm_wr_ban_low (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8)) (P : nat) :
    lm_wr_ban M ps cs s0 I P ->
    lm_proc_before M (ps ++ [3]) cs s0 I = lm_proc_before M ps cs s0 I.
  Proof using.
    intros (Hpin & _). symmetry. apply lm_proc_before_ext. intros J HJ Hne.
    apply (lm_pending_at_ps_ext ps (ps ++ [3]) cs s0 J); [by eexists |].
    exact (lm_pro_pin_at ps cs I (nlines J) Hpin (nstarted_strict J I HJ Hne)).
  Qed.

  Lemma lm_wr_ban_filed (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P : nat) :
    lm_wr_ban M ps cs s0 I P ->
    exists j : nat,
      pro_from (lm_pro_idx M cs (nlines I)) (ps ++ [3]) = pro_fail j ++ [3]
      /\ P = (length (lm_proc_before M (ps ++ [3]) cs s0 I)
              + length (lm_wr_pre I) + pro_round * j).
  Proof using.
    intros Hw. pose proof Hw as (Hpin & Hm & Hdv & Hr & (j & Hopen & HP)).
    exists j. split.
    - rewrite (pro_from_snoc_le _ ps 3 (lm_pro_pin_round_le ps cs I Hm Hr Hpin)).
      by rewrite Hopen.
    - by rewrite (lm_wr_ban_low ps cs s0 I P Hw).
  Qed.

  Lemma lm_wr_ban_byte (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P i : nat) (b : bv 8) :
    lm_wr_ban M ps cs s0 I P -> u_banner !! i = Some b ->
    lm_proc_stream M (ps ++ [3]) cs s0 I !! (P + i) = Some b.
  Proof using L.
    intros Hw Hb. pose proof Hw as (Hpin & Hm & Hdv & Hr & _).
    destruct (lm_wr_ban_filed ps cs s0 I P Hw) as (j & Hopen & HP).
    rewrite HP.
    exact (lm_proc_stream_round_banner_open (ps ++ [3]) cs s0 I j i b
             Hm Hr Hopen Hb).
  Qed.

  Lemma lm_wr_ban_done (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8)) (P : nat) :
    lm_wr_ban M ps cs s0 I P ->
    lm_wr_pro M (ps ++ [3]) cs s0 I (P + length u_banner).
  Proof using L.
    intros Hw. pose proof Hw as (Hpin & Hm & Hdv & Hr & (j & Hopen & HP)).
    assert (Hle : lm_pro_idx M cs (nlines I) <= pro_rounds ps)
      by exact (lm_pro_pin_round_le ps cs I Hm Hr Hpin).
    assert (Hnd : ~ pro_done (pro_from (lm_pro_idx M cs (nlines I)) ps))
      by (rewrite Hopen; exact (pro_done_fail j)).
    rewrite /lm_wr_pro. split_and!.
    - exact (lm_pro_pin_mono ps (ps ++ [3]) cs I ltac:(by eexists) Hpin).
    - exact Hm.
    - exact Hdv.
    - exact Hr.
    - rewrite (pro_from_snoc_le _ ps 3 Hle) Hopen.
      apply pro_done_cont. rewrite Forall_app. split; [exact (pro_fail_cont j) |].
      constructor; [by right | constructor].
    - rewrite /lm_proc_stream
              (length_app (lm_proc_before M (ps ++ [3]) cs s0 I)
                 (lm_pending_at M (ps ++ [3]) cs s0 I))
              (lm_wr_ban_low ps cs s0 I P Hw)
              (lm_pending_at_round_snoc ps cs s0 I 3 Hm Hr Hnd Hle)
              (length_app (lm_pending_at M ps cs s0 I) (pro_alts !!! 3))
              (lm_pending_at_round_pre ps cs s0 I Hm Hr)
              (length_app (lm_wr_pre I)
                 (pro_of (pro_from (lm_pro_idx M cs (nlines I)) ps)))
              Hopen pro_of_fail_length pro_alts_3 HP.
      lia.
  Qed.

  (* THE TRANSCRIPT'S HEAD *)
  Lemma lm_wr_ban_round0 (s0 : lm_st M) : lm_wr_ban M [] [] s0 [] 0.
  Proof using.
    rewrite /lm_wr_ban. split_and!.
    - exact (lm_pro_pin_nil _ _).
    - exact rest_of_nil.
    - by rewrite nlines_nil.
    - by left.
    - exists 0. split.
      + by rewrite nlines_nil pro_fail_0.
      + rewrite lm_proc_before_nil /lm_wr_pre.
        case_decide as Hd; [| by destruct (Hd eq_refl)].
        cbn [length]. lia.
  Qed.

  (* ================================================================== *)
  (*  7.  THE STEPS, PURE ([FileLinksLine] S5, S6)                       *)
  (* ================================================================== *)

  (* (1) the round's CHOICE BYTE at an open prologue: filing alternative 0
         appends the prompt's two bytes to the round's block *)
  Lemma lm_wr_pro_dollar (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P : nat) :
    lm_wr_pro M ps cs s0 I P -> lm_wr_sp M (ps ++ [0]) cs s0 I (S P).
  Proof using L.
    intros (Hpin & Hm & Hdv & Hr & Hnd & HP).
    assert (Hle : lm_pro_idx M cs (nlines I) <= pro_rounds ps)
      by exact (lm_pro_pin_round_le ps cs I Hm Hr Hpin).
    assert (Hpre : ps `prefix_of` (ps ++ [0])) by by eexists.
    assert (Hlow : lm_proc_before M (ps ++ [0]) cs s0 I = lm_proc_before M ps cs s0 I).
    { symmetry. apply lm_proc_before_ext. intros J HJ Hne.
      apply (lm_pending_at_ps_ext ps (ps ++ [0]) cs s0 J Hpre).
      exact (lm_pro_pin_at ps cs I (nlines J) Hpin (nstarted_strict J I HJ Hne)). }
    assert (Hup : lm_proc_stream M (ps ++ [0]) cs s0 I
                  = lm_proc_stream M ps cs s0 I ++ u_prompt).
    { rewrite {1}/lm_proc_stream Hlow
        (lm_pending_at_round_snoc ps cs s0 I 0 Hm Hr Hnd Hle) ll_pro_alts_0.
      by rewrite /lm_proc_stream app_assoc. }
    assert (Hlen : length (lm_proc_stream M (ps ++ [0]) cs s0 I) = S (S P)).
    { rewrite Hup (length_app (lm_proc_stream M ps cs s0 I) u_prompt) ll_prompt_len.
      lia. }
    split.
    - rewrite /lm_wr_open. split_and!.
      + exact (lm_pro_pin_mono ps (ps ++ [0]) cs I Hpre Hpin).
      + exact Hm.
      + exact Hdv.
      + rewrite pro_rounds_app ll_pro_rounds_one. lia.
      + by rewrite Hlen.
    - rewrite Hup lookup_app_r; [| lia].
      replace (S P - length (lm_proc_stream M ps cs s0 I)) with 1 by lia.
      exact ll_prompt_tail.
  Qed.

  (* (2) the LINE's choice byte at a settled round: the shell's '$' is the
         block's first byte and files an alternative whose block is the
         bare prompt (the line's silent round, where its model has one) *)
  Lemma lm_wr_blk_dollar (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P : nat) (c : nat) :
    lm_apr I c -> lm_ab I c = u_prompt ->
    lm_wr_blk M ps cs s0 I P ->
    lm_wr_sp M ps (cs ++ [c]) s0 I (S P).
  Proof using K.
    intros Hc Hcb Hw. pose proof (lm_wr_blk_nonnil ps cs s0 I P Hw) as Hne.
    pose proof (lm_wr_blk_started ps cs s0 I P Hw) as Hst.
    pose proof Hw as (Hpin & Hm & Hdv & HP).
    assert (Hnp : lm_panic M (lm_dec M c) = false) by exact (proj2 (proj2 Hc)).
    assert (Hpend : lm_pending_at M ps (cs ++ [c]) s0 I = u_prompt).
    { rewrite (lm_wr_blk_pending ps cs s0 I P _ Hw Hc). exact Hcb. }
    assert (Hlow : lm_proc_before M ps (cs ++ [c]) s0 I
                   = lm_proc_before M ps cs s0 I)
      by exact (lm_wr_blk_low ps cs s0 I P _ Hw).
    assert (Hup : lm_proc_stream M ps (cs ++ [c]) s0 I
                  = lm_proc_before M ps cs s0 I ++ u_prompt)
      by (rewrite /lm_proc_stream Hlow Hpend; reflexivity).
    assert (Hlen : length (lm_proc_stream M ps (cs ++ [c]) s0 I)
                   = S (S P)).
    { rewrite Hup (length_app (lm_proc_before M ps cs s0 I) u_prompt) ll_prompt_len.
      lia. }
    split.
    - rewrite /lm_wr_open. split_and!.
      + exact (lm_wr_blk_pin_snoc ps cs s0 I P _ Hw).
      + exact Hm.
      + rewrite length_app Hdv. cbn [length]. lia.
      + rewrite Hdv (lm_pro_idx_snoc_ne cs _ Hnp).
        pose proof (Hpin (length cs) ltac:(rewrite Hst; lia)). lia.
      + by rewrite Hlen.
    - rewrite Hup lookup_app_r; [| lia].
      replace (S P - length (lm_proc_before M ps cs s0 I)) with 1 by lia.
      exact ll_prompt_tail.
  Qed.

  (* (3) the SPACE, and (4) the READ *)
  Lemma lm_wr_sp_open (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8)) (P : nat) :
    lm_wr_sp M ps cs s0 I P -> lm_wr_open M ps cs s0 I (S P).
  Proof using. by intros [H _]. Qed.

  Lemma lm_wr_open_read (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P : nat) (l : list (bv 8)) :
    lm_wr_open M ps cs s0 I P -> wl_nl ∉ l ->
    lm_wr_blk M ps cs s0 (I ++ l ++ [wl_nl]) P.
  Proof using.
    intros (Hpin & Hm & Hdv & Hrd & HP) Hl.
    assert (Hassoc : I ++ l ++ [wl_nl] = (I ++ l) ++ [wl_nl])
      by (by rewrite app_assoc).
    assert (Hnl : nlines (I ++ l) = nlines I) by exact (ll_nlines_app_nonl I l Hl).
    assert (Hlines : nlines (I ++ l ++ [wl_nl]) = S (length cs))
      by (rewrite Hassoc nlines_snoc_nl Hnl Hdv; reflexivity).
    rewrite /lm_wr_blk. split_and!.
    - intros q Hq. rewrite Hassoc ll_nstarted_snoc Hnl Hdv in Hq.
      destruct (decide (q < length cs)) as [Hlt | Hge].
      + apply Hpin. rewrite (ll_nstarted_rest_nil I Hm) Hdv. exact Hlt.
      + assert (Hqe : q = length cs) by lia.
        rewrite Hqe -Hdv. exact Hrd.
    - rewrite Hassoc. exact (rest_of_snoc_nl (I ++ l)).
    - exact Hlines.
    - rewrite (lm_proc_before_line ps cs s0 I l Hm Hl). exact HP.
  Qed.

  (* the tight steps *)
  Lemma lm_wr_blk_open_s (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a : nat) :
    lm_wr_blk_t M ps cs s0 I P -> lm_panic M (lm_dec M a) = false ->
    lm_wr_open_t M ps (cs ++ [a]) s0 I (P + length (lm_abs s0 cs I a)).
  Proof using.
    intros [Hw Ht] Hnp.
    pose proof (lm_wr_blk_started ps cs s0 I P Hw) as Hst.
    pose proof Hw as (Hpin & Hm & Hdv & HP).
    split; [| exact (lm_wr_tail_snoc ps cs a Hnp Ht)].
    rewrite /lm_wr_open. split_and!.
    - exact (lm_wr_blk_pin_snoc ps cs s0 I P a Hw).
    - exact Hm.
    - rewrite length_app Hdv. cbn [length]. lia.
    - rewrite Hdv (lm_pro_idx_snoc_ne cs a Hnp).
      pose proof (Hpin (length cs) ltac:(rewrite Hst; lia)). lia.
    - rewrite /lm_proc_stream (lm_wr_blk_low ps cs s0 I P a Hw)
              (lm_wr_blk_pending_s ps cs s0 I P a Hw Hnp)
              (length_app (lm_proc_before M ps cs s0 I) (lm_abs s0 cs I a)) HP.
      reflexivity.
  Qed.

  Lemma lm_wr_blk_open (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a : nat) :
    lm_wr_blk_t M ps cs s0 I P -> lm_apr I a ->
    lm_wr_open_t M ps (cs ++ [a]) s0 I (P + length (lm_ab I a)).
  Proof using K.
    intros Hw Hpr. rewrite -(lm_abs_ab s0 cs I a Hpr).
    exact (lm_wr_blk_open_s ps cs s0 I P a Hw (proj2 (proj2 Hpr))).
  Qed.

  Lemma lm_wr_blk_sp_s (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a : nat) :
    lm_wr_blk_t M ps cs s0 I P -> lm_aprs I a ->
    lm_wr_sp_t M ps (cs ++ [a]) s0 I (P + (length (lm_abs s0 cs I a) - 1)).
  Proof using K.
    intros Hw Hpr. pose proof (lm_abs_len_ge2 s0 cs I a Hpr) as Hlen.
    destruct (lm_wr_blk_open_s ps cs s0 I P a Hw (proj1 (proj2 Hpr))) as [Hop Ht].
    split; [| exact Ht]. split.
    - replace (S (P + (length (lm_abs s0 cs I a) - 1)))
        with (P + length (lm_abs s0 cs I a)) by lia.
      exact Hop.
    - exact (lm_wr_blk_byte_s ps cs s0 I P a (length (lm_abs s0 cs I a) - 1)
               (u_prompt !!! 1) (proj1 Hw) (proj1 (proj2 Hpr)) (lm_abs_space s0 cs I a Hpr)).
  Qed.

  Lemma lm_wr_blk_sp (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a : nat) :
    lm_wr_blk_t M ps cs s0 I P -> lm_apr I a ->
    lm_wr_sp_t M ps (cs ++ [a]) s0 I (P + (length (lm_ab I a) - 1)).
  Proof using K.
    intros Hw Hpr. rewrite -(lm_abs_ab s0 cs I a Hpr).
    exact (lm_wr_blk_sp_s ps cs s0 I P a Hw (lm_apr_aprs I a Hpr)).
  Qed.

  Lemma lm_wr_sp_open_t (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P : nat) :
    lm_wr_sp_t M ps cs s0 I P -> lm_wr_open_t M ps cs s0 I (S P).
  Proof using.
    intros [Hs Ht]. split; [exact (lm_wr_sp_open ps cs s0 I P Hs) | exact Ht].
  Qed.

  Lemma lm_wr_open_read_t (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P : nat) (l : list (bv 8)) :
    lm_wr_open_t M ps cs s0 I P -> wl_nl ∉ l ->
    lm_wr_blk_t M ps cs s0 (I ++ l ++ [wl_nl]) P.
  Proof using.
    intros [Ho Ht] Hl.
    split; [exact (lm_wr_open_read ps cs s0 I P l Ho Hl) | exact Ht].
  Qed.

  Lemma lm_wr_pro_tail (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P : nat) :
    lm_wr_pro M ps cs s0 I P -> lm_wr_tail M (ps ++ [0]) cs.
  Proof using.
    intros Hw. pose proof Hw as (Hpin & Hr & Hn & Hopen & Hnd & HP).
    pose proof (lm_pro_pin_round_le ps cs I Hr Hopen Hpin) as Hle.
    rewrite Hn in Hnd Hle.
    rewrite /lm_wr_tail.
    replace (S (lm_pro_idx M cs (length cs))) with (lm_pro_idx M cs (length cs) + 1)
      by lia.
    rewrite -(pro_from_add 1 (lm_pro_idx M cs (length cs)))
            (pro_from_snoc_le (lm_pro_idx M cs (length cs)) ps 0 Hle).
    cbn [pro_from]. exact (pro_tail_open_snoc _ 0 Hnd).
  Qed.

  Lemma lm_wr_pro_dollar_t (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P : nat) :
    lm_wr_pro M ps cs s0 I P -> lm_wr_sp_t M (ps ++ [0]) cs s0 I (S P).
  Proof using L.
    intros Hw. split;
      [exact (lm_wr_pro_dollar ps cs s0 I P Hw) | exact (lm_wr_pro_tail ps cs s0 I P Hw)].
  Qed.

  (* the PANIC alternative opens a fresh round at the same input *)
  Lemma lm_wr_blk_pending_pan (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P : nat) :
    lm_wr_blk M ps cs s0 I P ->
    lm_pending_at M ps (cs ++ [lmh_pan K (lm_line_at I)]) s0 I
    = alt_panic ++ pro_of (pro_from (S (lm_pro_idx M cs (length cs))) ps).
  Proof using L K.
    intros Hw. pose proof (lm_wr_blk_nonnil ps cs s0 I P Hw) as Hne.
    pose proof Hw as (_ & Hr & Hn & _).
    assert (Hlow : lm_pro_idx M (cs ++ [lmh_pan K (lm_line_at I)]) (nlines I - 1)
                   = lm_pro_idx M cs (length cs)).
    { replace (nlines I - 1) with (length cs) by lia.
      exact (lm_pro_idx_ext M (cs ++ [lmh_pan K (lm_line_at I)]) cs (length cs)
               ltac:(intros j Hj; rewrite list_lookup_total_alt lookup_app_l;
                     [by rewrite -list_lookup_total_alt | lia])
               (length cs) ltac:(lia)). }
    rewrite /lm_pending_at decide_False; [| exact Hne].
    rewrite decide_True; [| exact Hr].
    rewrite /lm_cont_at (lm_blk_snoc_at cs I _ Hn) Hlow.
    assert (Hp : lm_panic M (lm_dec M (lmh_pan K (lm_line_at I))) = true)
      by exact (lmh_pan_panic K (lm_line_at I)).
    by rewrite Hp (lml_cont_panic L _ _ _ Hp).
  Qed.

  Lemma lm_wr_blk_ban (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8)) (P : nat) :
    lm_wr_blk_t M ps cs s0 I P ->
    lm_wr_ban M ps (cs ++ [lmh_pan K (lm_line_at I)]) s0 I
      (P + length (lm_ab I (lmh_pan K (lm_line_at I)))).
  Proof using L K.
    intros [Hw Ht]. pose proof (lm_wr_blk_nonnil ps cs s0 I P Hw) as Hne.
    pose proof (lm_wr_blk_started ps cs s0 I P Hw) as Hst.
    pose proof Hw as (Hpin & Hr & Hn & HP).
    assert (Hpanat : lm_panic M (lm_at M (cs ++ [lmh_pan K (lm_line_at I)])
                                   (nlines I - 1)) = true).
    { rewrite (lm_blk_snoc_at cs I _ Hn). exact (lmh_pan_panic K (lm_line_at I)). }
    rewrite /lm_wr_ban. split_and!.
    - exact (lm_wr_blk_pin_snoc ps cs s0 I P (lmh_pan K (lm_line_at I)) Hw).
    - exact Hr.
    - rewrite length_app Hn. cbn [length]. lia.
    - by right.
    - exists 0. split.
      + rewrite Hn.
        rewrite (lm_pro_idx_snoc_pan cs (lmh_pan K (lm_line_at I))
                   (lmh_pan_panic K (lm_line_at I))).
        rewrite pro_fail_0. exact Ht.
      + rewrite (lm_wr_blk_low ps cs s0 I P (lmh_pan K (lm_line_at I)) Hw) -HP
                /lm_wr_pre.
        rewrite decide_False; [| exact Hne].
        rewrite (lm_ab_pan I). lia.
  Qed.

  (* the shapes the era's HEAD lands on after its first byte *)
  Lemma lm_wr_pro_head (s0 : lm_st M) : lm_wr_pro M [] [] s0 [] 0.
  Proof using.
    rewrite /lm_wr_pro. split_and!.
    - exact (lm_pro_pin_nil _ _).
    - exact rest_of_nil.
    - by rewrite nlines_nil.
    - by left.
    - rewrite nlines_nil. cbn [lm_pro_idx pro_from].
      rewrite -pro_fail_0. exact (pro_done_fail 0).
    - rewrite /lm_proc_stream lm_proc_before_nil /lm_pending_at.
      case_decide as Hd; [| by destruct (Hd eq_refl)]. by cbn [app pro_of length].
  Qed.

  Lemma lm_wr_sp_head (s0 : lm_st M) : lm_wr_sp M [0] [] s0 [] 1.
  Proof using L.
    exact (lm_wr_pro_dollar [] [] s0 [] 0 (lm_wr_pro_head s0)).
  Qed.

  Lemma lm_wr_tail_head : lm_wr_tail M [0] [].
  Proof using. rewrite /lm_wr_tail. cbn [length lm_pro_idx]. by vm_compute. Qed.

  (* ================================================================== *)
  (*  8.  THE DISCIPLINE LEMMA ([FileLinksLine] S7): an untainted input   *)
  (*      past a boundary means the boundary's prompt was written        *)
  (* ================================================================== *)

  (* the reader's range condition: POINTWISE, since the list runs one
     short at a block boundary; each entry at its round's state from the
     era's boot state [s0] *)
  Definition lm_alts_pre (s0 : lm_st M) (I : list (bv 8)) (cs : list nat) : Prop :=
    forall (i : nat) (c : nat),
      cs !! i = Some c ->
      i < nlines I
      /\ lm_ok M (lm_upto M cs s0 (bodies_of I) i) (lm_of M (bodies_of I !!! i))
           (lm_dec M c).

  Lemma lm_alts_pre_nil s0 I : lm_alts_pre s0 I [].
  Proof using. intros i c Hc. by rewrite lookup_nil in Hc. Qed.

  Lemma lm_alts_pre_at s0 I cs i :
    lm_alts_pre s0 I cs -> i < length cs ->
    lm_ok M (lm_upto M cs s0 (bodies_of I) i) (lm_of M (bodies_of I !!! i))
      (lm_at M cs i).
  Proof using.
    intros H Hi. destruct (lookup_lt_is_Some_2 cs i Hi) as [c Hc].
    rewrite /lm_at (list_lookup_total_correct cs i c Hc).
    exact (proj2 (H i c Hc)).
  Qed.

  Lemma lm_alts_pre_le s0 I cs : lm_alts_pre s0 I cs -> length cs <= nlines I.
  Proof using.
    intros H. destruct (decide (length cs = 0)) as [Hz | Hz]; [lia |].
    destruct (lookup_lt_is_Some_2 cs (length cs - 1) ltac:(lia)) as [c Hc].
    destruct (H _ c Hc) as [Hlt _]. lia.
  Qed.

  Lemma lm_alts_pre_of_alts_ok s0 I cs :
    lm_alts_ok M s0 I cs -> lm_alts_pre s0 I cs.
  Proof using.
    intros [Hlen Ha] i c Hc.
    assert (Hi : i < nlines I) by (rewrite -Hlen; by eapply lookup_lt_Some).
    split; [exact Hi |].
    pose proof (Ha i Hi) as Hok.
    by rewrite /lm_at (list_lookup_total_correct _ _ _ Hc) in Hok.
  Qed.

  (* the input GROWS and the entries keep their meaning: a completed line's
     body is the same body in every longer input *)
  Lemma lm_alts_pre_mono s0 I I' cs :
    I `prefix_of` I' -> lm_alts_pre s0 I cs -> lm_alts_pre s0 I' cs.
  Proof using.
    intros Hp H i c Hc. destruct (H i c Hc) as [Hi Hok].
    destruct (bodies_of_prefix I I' Hp) as [z Hz].
    assert (Hbod : forall j, j < nlines I -> bodies_of I' !!! j = bodies_of I !!! j).
    { intros j Hj. rewrite Hz !list_lookup_total_alt lookup_app_l;
        [reflexivity | rewrite /nlines in Hj; lia]. }
    split; [rewrite /nlines Hz length_app; rewrite /nlines in Hi; lia |].
    rewrite (Hbod i Hi).
    rewrite (lm_upto_ext cs cs s0 (bodies_of I') (bodies_of I) i
               ltac:(intros j _; reflexivity) ltac:(intros j Hj; apply Hbod; lia)).
    exact Hok.
  Qed.

  (* what the claim knows of the writer's stage at the input its log has
     echoed, from the era's boot state [s0] *)
  Definition lm_rd_stage (ps0 cs0 : list nat) (s0 : lm_st M) (I : list (bv 8)) : Prop :=
    Forall (fun a => a < length pro_alts) ps0
    /\ lm_alts_pre s0 I cs0
    /\ lm_pro_pin M ps0 cs0 I
    /\ nlines (removelast I) <= length cs0.

  Lemma lm_rd_stage_0 s0 : lm_rd_stage [] [] s0 [].
  Proof using.
    rewrite /lm_rd_stage. split_and!.
    - constructor.
    - apply lm_alts_pre_nil.
    - apply lm_pro_pin_nil.
    - cbn [removelast]. rewrite nlines_nil. lia.
  Qed.

  Lemma lm_pending_at_nonnil_at (ps cs0 : list nat) (s0 : lm_st M)
      (I I0 : list (bv 8)) :
    I `prefix_of` I0 -> lm_alts_pre s0 I0 cs0 -> I <> [] -> rest_of I = [] ->
    lm_pending_at M ps cs0 s0 I <> [].
  Proof using K.
    intros Hp Hao Hne Hr.
    pose proof (nlines_pos_of_rest_nil I Hne Hr) as Hq.
    rewrite /lm_pending_at decide_False; [| exact Hne].
    rewrite decide_True; [| exact Hr].
    rewrite /lm_cont_at. intros Hc. apply app_eq_nil in Hc as [Hc _].
    revert Hc. apply (lmh_cont_nonnil K).
    destruct (decide (nlines I - 1 < length cs0)) as [Hlt | Hge].
    - left.
      pose proof (lm_alts_pre_at s0 I0 cs0 (nlines I - 1) Hao Hlt) as Hok.
      destruct (bodies_of_prefix I I0 Hp) as [z Hz].
      assert (Hbod : forall j, j < nlines I -> bodies_of I0 !!! j = bodies_of I !!! j).
      { intros j Hj. rewrite Hz !list_lookup_total_alt lookup_app_l;
          [reflexivity | rewrite /nlines in Hj; lia]. }
      rewrite (Hbod (nlines I - 1) ltac:(lia)) in Hok.
      rewrite (lm_upto_ext cs0 cs0 s0 (bodies_of I0) (bodies_of I) (nlines I - 1)
                 ltac:(intros j _; reflexivity)
                 ltac:(intros j Hj; apply Hbod; lia)) in Hok.
      exact Hok.
    - right. apply lm_at_ge. lia.
  Qed.

  Lemma lm_pending_at_nonnil (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8)) :
    lm_alts_pre s0 I cs -> I <> [] -> rest_of I = [] ->
    lm_pending_at M ps cs s0 I <> [].
  Proof using K.
    intros Hao Hne Hr.
    exact (lm_pending_at_nonnil_at ps cs s0 I I ltac:(reflexivity) Hao Hne Hr).
  Qed.

  Lemma lm_wr_owed_read_refute (ps cs ps0 cs0 : list nat) (s0 : lm_st M)
      (I I0 : list (bv 8)) (P : nat) :
    lm_wr_owed M ps cs s0 I P ->
    I `prefix_of` I0 -> I <> I0 -> lm_rd_stage ps0 cs0 s0 I0 ->
    (ps `prefix_of` ps0 \/ ps0 `prefix_of` ps) ->
    (cs `prefix_of` cs0 \/ cs0 `prefix_of` cs) ->
    length (lm_proc_before M ps0 cs0 s0 I0) <= P -> False.
  Proof using L K.
    intros Hw HI Hne Hrs Hps Hcs Hle.
    pose proof Hrs as (HFps0 & Hao0 & Hpin0 & Hbnd0).
    assert (Hqle : nlines I <= length cs0).
    { etrans; [| exact Hbnd0].
      apply nlines_prefix, (ll_prefix_of_removelast I I0 HI Hne). }
    assert (Hmono : length (lm_proc_stream M ps0 cs0 s0 I)
                    <= length (lm_proc_before M ps0 cs0 s0 I0))
      by (apply prefix_length, (lm_proc_stream_before ps0 cs0 s0 I I0 HI Hne)).
    destruct Hw as [Hw | Hw]; last first.
    { (* THE BLOCK IS OWED: its first byte is unwritten *)
      pose proof (lm_wr_blk_nonnil ps cs s0 I P Hw) as Hnil.
      pose proof (lm_wr_blk_started ps cs s0 I P Hw) as Hstar.
      pose proof Hw as (Hpin & Hm & Hdv & HP).
      assert (Hb1 : nlines (removelast I) <= length cs)
        by (rewrite (ll_nlines_removelast I Hm); lia).
      assert (Hcs' : cs `prefix_of` cs0).
      { destruct Hcs as [Hc | Hc]; [exact Hc |].
        apply prefix_length in Hc. exfalso. lia. }
      assert (Hpin0c : lm_pro_pin M ps0 cs I).
      { intros q Hq. destruct Hcs' as [z Hz].
        rewrite -(lm_pro_idx_app_le cs z q ltac:(lia)) -Hz.
        apply Hpin0. pose proof (nstarted_strict I I0 HI Hne). lia. }
      assert (Hlow : lm_proc_before M ps0 cs0 s0 I = lm_proc_before M ps cs s0 I).
      { destruct Hps as [Hps | Hps].
        - symmetry.
          exact (lm_proc_before_cs_prefix ps ps0 cs cs0 s0 I Hps Hcs' Hpin Hb1).
        - transitivity (lm_proc_before M ps0 cs s0 I).
          + symmetry.
            exact (lm_proc_before_cs_prefix ps0 ps0 cs cs0 s0 I
                     ltac:(reflexivity) Hcs' Hpin0c Hb1).
          + exact (lm_proc_before_cs_prefix ps0 ps cs cs s0 I Hps
                     ltac:(reflexivity) Hpin0c Hb1). }
      assert (Hne0 : lm_pending_at M ps0 cs0 s0 I <> [])
        by exact (lm_pending_at_nonnil_at ps0 cs0 s0 I I0 HI Hao0 Hnil Hm).
      assert (Hpos : 0 < length (lm_pending_at M ps0 cs0 s0 I)).
      { destruct (lm_pending_at M ps0 cs0 s0 I) as [| y ys];
          [by destruct (Hne0 eq_refl) | cbn [length]; lia]. }
      rewrite /lm_proc_stream
        (length_app (lm_proc_before M ps0 cs0 s0 I) (lm_pending_at M ps0 cs0 s0 I))
        Hlow in Hmono.
      lia. }
    (* THE PROLOGUE IS OPEN: the reader's round is settled *)
    pose proof Hw as (Hpin & Hm & Hdv & Hr & Hnd & HP).
    assert (Hcs' : cs `prefix_of` cs0).
    { destruct Hcs as [Hc | Hc]; [exact Hc |].
      pose proof (prefix_length _ _ Hc) as Hlc.
      rewrite (prefix_length_eq _ _ Hc ltac:(lia)). reflexivity. }
    destruct Hcs' as [z Hz].
    assert (Hidx : lm_pro_idx M cs0 (nlines I) = lm_pro_idx M cs (nlines I)).
    { rewrite Hz. apply lm_pro_idx_app_le. lia. }
    assert (Hdone0 : pro_done (pro_from (lm_pro_idx M cs (nlines I)) ps0)).
    { apply pro_from_done. rewrite -Hidx.
      exact (Hpin0 (nlines I) (nstarted_strict I I0 HI Hne)). }
    destruct Hps as [Hps | Hps]; last first.
    { apply Hnd. exact (pro_done_mono _ _ (pro_from_mono _ _ _ Hps) Hdone0). }
    assert (Hlow : lm_proc_before M ps cs s0 I = lm_proc_before M ps0 cs0 s0 I).
    { apply (lm_proc_before_cs_prefix ps ps0 cs cs0 s0 I Hps ltac:(by eexists) Hpin).
      etrans; [apply nlines_prefix, ll_removelast_prefix | lia]. }
    assert (Hr0 : I = [] \/ lm_panic M (lm_at M cs0 (nlines I - 1)) = true).
    { destruct (decide (I = [])) as [-> | Hn0]; [by left | right].
      destruct Hr as [Hr | Hr]; [done |].
      assert (Hq1 : 1 <= length cs)
        by (pose proof (nlines_pos_of_rest_nil I Hn0 Hm); lia).
      rewrite /lm_at Hz list_lookup_total_alt lookup_app_l; [| lia].
      rewrite -list_lookup_total_alt. exact Hr. }
    assert (Hlt : length (lm_pending_at M ps cs s0 I)
                  < length (lm_pending_at M ps0 cs0 s0 I)).
    { rewrite (lm_pending_at_round_pre ps cs s0 I Hm Hr)
              (lm_pending_at_round_pre ps0 cs0 s0 I Hm Hr0).
      rewrite !(length_app (lm_wr_pre I) _) Hidx.
      pose proof (pro_of_open_done_lt _ _ Hnd Hdone0 (pro_from_mono _ _ _ Hps)
                    (pro_from_Forall _ _ _ HFps0)).
      lia. }
    rewrite HP /lm_proc_stream
      (length_app (lm_proc_before M ps cs s0 I) (lm_pending_at M ps cs s0 I))
      Hlow in Hle.
    rewrite /lm_proc_stream
      (length_app (lm_proc_before M ps0 cs0 s0 I) (lm_pending_at M ps0 cs0 s0 I))
      in Hmono.
    lia.
  Qed.

  (* ================================================================== *)
  (*  9.  /INIT'S PROLOGUE DIAGNOSTICS, PURE ([EchoLinksPro],             *)
  (*      [PipeLinksLine] S4)                                            *)
  (* ================================================================== *)
  Definition lm_wr_pban (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P : nat) : Prop :=
    lm_wr_pro M ps cs s0 I P
    /\ (exists j : nat,
          pro_from (lm_pro_idx M cs (nlines I)) ps = pro_fail j ++ [3]).

  Lemma lm_wr_pban_of_ban (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P : nat) :
    lm_wr_ban M ps cs s0 I P ->
    lm_wr_pban (ps ++ [3]) cs s0 I (P + length u_banner).
  Proof using L.
    intros Hw. split; [exact (lm_wr_ban_done ps cs s0 I P Hw) |].
    destruct (lm_wr_ban_filed ps cs s0 I P Hw) as (j & Hj & _). by exists j.
  Qed.

  Definition lm_wr_pdiag (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a i : nat) : Prop :=
    lm_pro_pin M ps cs I
    /\ rest_of I = []
    /\ nlines I = length cs
    /\ (I = [] \/ lm_panic M (lm_at M cs (nlines I - 1)) = true)
    /\ (exists j : nat,
          pro_from (lm_pro_idx M cs (nlines I)) ps = pro_fail j ++ [3; a]
          /\ P = (length (lm_proc_before M ps cs s0 I) + length (lm_wr_pre I)
                  + pro_round * j + length u_banner + i)).

  Lemma lm_wr_pdiag_S (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a i : nat) :
    lm_wr_pdiag ps cs s0 I P a i -> lm_wr_pdiag ps cs s0 I (S P) a (S i).
  Proof using.
    intros (Hpin & Hm & Hdv & Hr & (j & Hj & HP)).
    split_and!; try assumption. exists j. split; [exact Hj | lia].
  Qed.

  Lemma ll_pro_of_fail_snoc (j a : nat) :
    pro_of (pro_fail j ++ [3; a])
    = pro_of (pro_fail j) ++ u_banner ++ pro_alts !!! a.
  Proof using.
    rewrite (pro_of_open_app _ _ (pro_done_fail j)).
    cbn [pro_of]. rewrite pro_alts_3 (pro_more_cont 3 _ ltac:(by right)).
    rewrite /pro_more. case_decide; by rewrite app_nil_r.
  Qed.

  Lemma lm_wr_pdiag_byte (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a i : nat) (b : bv 8) :
    lm_wr_pdiag ps cs s0 I P a i -> pro_alts !!! a !! i = Some b ->
    lm_proc_stream M ps cs s0 I !! P = Some b.
  Proof using L.
    intros (Hpin & Hm & Hdv & Hr & (j & Hj & HP)) Hb.
    rewrite /lm_proc_stream (lm_pending_at_round_pre ps cs s0 I Hm Hr) Hj
            ll_pro_of_fail_snoc HP.
    replace (length (lm_proc_before M ps cs s0 I) + length (lm_wr_pre I)
             + pro_round * j + length u_banner + i)
      with (length (lm_proc_before M ps cs s0 I)
            + (length (lm_wr_pre I)
               + (length (pro_of (pro_fail j)) + (length u_banner + i))))
      by (rewrite pro_of_fail_length; lia).
    rewrite (lookup_app_shift (lm_proc_before M ps cs s0 I))
            (lookup_app_shift (lm_wr_pre I))
            (lookup_app_shift (pro_of (pro_fail j))) (lookup_app_shift u_banner).
    exact Hb.
  Qed.

  Lemma lm_wr_pdiag_1_of_pro (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P a : nat) :
    lm_wr_pban ps cs s0 I P -> lm_wr_pdiag (ps ++ [a]) cs s0 I (S P) a 1.
  Proof using L.
    intros ((Hpin & Hm & Hdv & Hr & Hnd & HP) & (j & Hj)).
    assert (Hle : lm_pro_idx M cs (nlines I) <= pro_rounds ps)
      by exact (lm_pro_pin_round_le ps cs I Hm Hr Hpin).
    assert (Hpre : ps `prefix_of` (ps ++ [a])) by by eexists.
    assert (Hlow : lm_proc_before M (ps ++ [a]) cs s0 I = lm_proc_before M ps cs s0 I).
    { symmetry. apply lm_proc_before_ext. intros J HJ Hne.
      apply (lm_pending_at_ps_ext ps (ps ++ [a]) cs s0 J Hpre).
      exact (Hpin (nlines J) (nstarted_strict J I HJ Hne)). }
    assert (H3 : length (pro_of (pro_fail j ++ [3]))
                 = pro_round * j + length u_banner).
    { rewrite (pro_of_open_app _ _ (pro_done_fail j)) pro_of_singleton pro_alts_3.
      rewrite length_app pro_of_fail_length. reflexivity. }
    rewrite /lm_wr_pdiag. split_and!.
    - exact (lm_pro_pin_mono ps (ps ++ [a]) cs I Hpre Hpin).
    - exact Hm.
    - exact Hdv.
    - exact Hr.
    - exists j. split.
      + rewrite (pro_from_snoc_le _ ps a Hle) Hj. by rewrite -app_assoc.
      + rewrite Hlow HP /lm_proc_stream (length_app (lm_proc_before M ps cs s0 I))
                (lm_pending_at_round_pre ps cs s0 I Hm Hr)
                (length_app (lm_wr_pre I)) Hj H3. lia.
  Qed.

  Lemma lm_wr_pdiag_done_1 (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (P i : nat) :
    i = length (pro_alts !!! 1) ->
    lm_wr_pdiag ps cs s0 I P 1 i -> lm_wr_ban M ps cs s0 I P.
  Proof using.
    intros Hi (Hpin & Hm & Hdv & Hr & (j & Hj & HP)).
    assert (Hb : length u_banner = 18) by (vm_compute; reflexivity).
    assert (Ha : length (pro_alts !!! 1) = 21) by (vm_compute; reflexivity).
    assert (Hrd : pro_round = 39) by (vm_compute; reflexivity).
    rewrite /lm_wr_ban. split_and!; try assumption.
    exists (S j). split.
    - rewrite Hj. by rewrite pro_fail_S.
    - rewrite HP Hi Hb Ha Hrd. lia.
  Qed.
End line_model_links.
