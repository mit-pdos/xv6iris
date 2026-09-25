(* ===================================================================== *)
(* UkShRedirLine.v -- THE REDIRECT LINE AS A LINE, lane SH-PARSE          *)
(* (design/app-file.md SS5.1, deliverable 5's pure half).                  *)
(*                                                                        *)
(* THE BRIEF ASKED FOR [UkShLoop.ush_line_lexable] TO BECOME A             *)
(* DISJUNCTION -- today's symbol-free shape OR the redirect shape -- and   *)
(* that shape of edit is REFUTED here, as a theorem rather than a claim.   *)
(* [ush_line_lexable] is quantified over [UkSh.ush_line_is ws f k len],    *)
(* and [ush_line_is] carries [EchoDisc.line_ok ws], hence                  *)
(* [LineWords.wl_wf ws], hence every byte of the buffer is alphanumeric,   *)
(* a blank or the newline ([LineWords.wl_line_byte_val]).  None of those   *)
(* is a byte of sh's symbol table, so [ushs_line_is_nosym] below proves    *)
(* that a line [ush_line_is] describes NEVER has a '>' in it: a right      *)
(* disjunct for the redirect shape would be vacuous, and a consumer that   *)
(* case-split on it would be case-splitting on something that cannot       *)
(* happen.  (durable-notes, Vacuity: the defect class nothing in the       *)
(* build sees.)                                                              *)
(*                                                                        *)
(* WHAT REPLACES IT is a SECOND line predicate, stated positionally the    *)
(* way [ush_line_is] is: [ushs_line_is ws file f k len] says the buffer at *)
(* [k] holds the words of [ws], then one blank, the '>', one blank, then   *)
(* the file name, then the newline.  [ushs_line_is_redir] is the bridge    *)
(* the parser walks want -- it turns that into                             *)
(* [UkShParseSym.ushs_redir len (fun j => f (k + j)) p e] at the two       *)
(* positions the line's own lengths name -- and it is what a widened       *)
(* [ush_line_lexable] has to be quantified over instead.                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
Require Import RiscvModelBytes.
Require Import LineWords.
Require Import EchoDisc.
Require Import FileDisc.   (* [uline] / [line_bytes] / [fname_f] -- the line
                              the file discipline TYPES, which the redirect
                              shape below is the positional reading of *)
Require Import UkSh.
Require Import UkShParse.
Require Import UkShParseSym.
Local Open Scope Z_scope.


(* ===================================================================== *)
(* §1 THE FOUR BYTE CLASSES A LINE CAN CARRY, AGAINST THE LEXER'S TABLES  *)
(* ===================================================================== *)

(* the two tables, as NUMBERS.  Every byte fact below is then one [lia]
   between a range and an enumeration, and no proof has to look at a
   literal bitvector. *)
Lemma ushs_sym_val (b : bv 8) :
  ushp_is_sym b = true ->
  bv_unsigned b = 60 \/ bv_unsigned b = 124 \/ bv_unsigned b = 62
  \/ bv_unsigned b = 38 \/ bv_unsigned b = 59 \/ bv_unsigned b = 40
  \/ bv_unsigned b = 41.
Proof.
  intro E. unfold ushp_is_sym in E. apply bool_decide_eq_true in E.
  unfold ushp_sym_bytes in E. cbn [fmap list_fmap] in E.
  apply elem_of_list_lookup_1 in E as [ i Hi ].
  destruct i as [| [| [| [| [| [| [| i ]]]]]]]; cbn in Hi;
    try discriminate Hi;
    (injection Hi as Hb; rewrite <- Hb; vm_compute; tauto).
Qed.

Lemma ushs_ws_val (b : bv 8) :
  ushp_is_ws b = true ->
  bv_unsigned b = 32 \/ bv_unsigned b = 9 \/ bv_unsigned b = 13
  \/ bv_unsigned b = 10 \/ bv_unsigned b = 11.
Proof.
  intro E. unfold ushp_is_ws in E. apply bool_decide_eq_true in E.
  unfold ushp_ws_bytes in E. cbn [fmap list_fmap] in E.
  apply elem_of_list_lookup_1 in E as [ i Hi ].
  destruct i as [| [| [| [| [| i ]]]]]; cbn in Hi;
    try discriminate Hi;
    (injection Hi as Hb; rewrite <- Hb; vm_compute; tauto).
Qed.

Lemma ushs_alnum_not_sym (b : bv 8) : wl_alnum b -> ushp_is_sym b = false.
Proof.
  intro Ha. destruct (ushp_is_sym b) eqn:E; [ exfalso | reflexivity ].
  pose proof (ushs_sym_val b E) as Hval.
  unfold wl_alnum in Ha.
  destruct Ha as [ H1 | [ H1 | H1 ] ];
    destruct Hval as [ H2 | [ H2 | [ H2 | [ H2 | [ H2 | [ H2 | H2 ]]]]]]; lia.
Qed.

Lemma ushs_alnum_not_ws (b : bv 8) : wl_alnum b -> ushp_is_ws b = false.
Proof.
  intro Ha. destruct (ushp_is_ws b) eqn:E; [ exfalso | reflexivity ].
  pose proof (ushs_ws_val b E) as Hval.
  unfold wl_alnum in Ha.
  destruct Ha as [ H1 | [ H1 | H1 ] ];
    destruct Hval as [ H2 | [ H2 | [ H2 | [ H2 | H2 ]]]]; lia.
Qed.

Lemma ushs_sp_ws : ushp_is_ws wl_sp = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ushs_nl_ws : ushp_is_ws wl_nl = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ushs_sp_not_sym : ushp_is_sym wl_sp = false.
Proof. vm_compute. reflexivity. Qed.

Lemma ushs_nl_not_sym : ushp_is_sym wl_nl = false.
Proof. vm_compute. reflexivity. Qed.

Lemma ushs_body_not_sym (b : bv 8) : wl_body_byte b -> ushp_is_sym b = false.
Proof.
  intros [ Ha | -> ]; [ exact (ushs_alnum_not_sym b Ha) | exact ushs_sp_not_sym ].
Qed.


(* ===================================================================== *)
(* §2 THE REFUTATION: A LINE [ush_line_is] DESCRIBES HAS NO SYMBOL BYTE   *)
(*                                                                        *)
(* This is the design fact that decides deliverable 5's shape.  It is     *)
(* also, on its own, the FIRST HALF of [UkShLoop.ush_line_lexable] --     *)
(* which is a [Prop] premise today -- so the premise is that much         *)
(* narrower than it looks.                                                *)
(* ===================================================================== *)

Lemma ushs_line_is_nosym (ws : list (list (bv 8))) (f : nat -> bv 8)
    (k len : nat) :
  ush_line_is ws f k len -> ushp_no_symbols len (fun j : nat => f (k + j)%nat).
Proof.
  intros (Hok & Hlen & Hbytes) j Hj.
  assert (Hjl : (j < length (wl_line ws))%nat) by lia.
  assert (Hin : wl_line ws !!! j ∈ wl_line ws)
    by (apply elem_of_list_lookup_2 with j;
        exact (list_lookup_lookup_total_lt (wl_line ws) j Hjl)).
  pose proof (wl_line_byte_val ws (wl_line ws !!! j)
                (line_ok_wf ws Hok) Hin) as Hv.
  cbn beta. rewrite (Hbytes j Hj).
  destruct (ushp_is_sym (wl_line ws !!! j)) eqn:E; [ exfalso | reflexivity ].
  pose proof (ushs_sym_val (wl_line ws !!! j) E) as Hval.
  destruct Hv as [ H1 | [ H1 | [ H1 | [ H1 | H1 ]]]];
    destruct Hval as [ H2 | [ H2 | [ H2 | [ H2 | [ H2 | [ H2 | H2 ]]]]]]; lia.
Qed.


(* ===================================================================== *)
(* §3 THE REDIRECT LINE, STATED POSITIONALLY                              *)
(*                                                                        *)
(*   <the words of ws>  ' '  '>'  ' '  <file>  '\n'                       *)
(*                       ^p0  ^p                                          *)
(*                                                                        *)
(* Positional, exactly as [UkSh.ush_line_is] is, so that a walk reads the  *)
(* bytes it needs off the predicate with no list-append arithmetic.       *)
(* ===================================================================== *)

Definition ushs_line_is (ws : list (list (bv 8))) (file : list (bv 8))
    (f : nat -> bv 8) (k len : nat) : Prop :=
  let p0 := length (wl_body ws) in
  line_ok ws
  /\ wl_word file
  /\ len = (p0 + 3 + length file + 1)%nat
  /\ (forall j : nat, (j < p0)%nat -> f (k + j)%nat = wl_body ws !!! j)
  /\ f (k + p0)%nat = wl_sp
  /\ f (k + p0 + 1)%nat = ushs_gt
  /\ f (k + p0 + 2)%nat = wl_sp
  /\ (forall j : nat, (j < length file)%nat ->
        f (k + p0 + 3 + j)%nat = file !!! j)
  /\ f (k + p0 + 3 + length file)%nat = wl_nl.

(* ...and it IS the canonical redirect the parser walks are stated over *)
Lemma ushs_line_is_redir (ws : list (list (bv 8))) (file : list (bv 8))
    (f : nat -> bv 8) (k len : nat) :
  ushs_line_is ws file f k len ->
  ushs_redir len (fun j : nat => f (k + j)%nat)
    (length (wl_body ws) + 1)%nat
    (length (wl_body ws) + 3 + length file)%nat.
Proof.
  intros (Hok & Hfile & Hlen & Hbody & Hsp1 & Hgt & Hsp2 & Hfb & Hnl).
  set (p0 := length (wl_body ws)) in *.
  assert (Hfpos : (0 < length file)%nat)
    by (destruct Hfile as [ Hne _ ]; destruct file; [ done | cbn; lia ]).
  (* the three byte classes, at each region of the line *)
  assert (Hbodycl : forall j : nat, (j < p0)%nat ->
            ushp_is_sym (f (k + j)%nat) = false).
  { intros j Hj. rewrite (Hbody j Hj). apply ushs_body_not_sym.
    refine (Forall_lookup_1 _ _ _ _ (wl_body_bytes ws (line_ok_wf ws Hok)) _).
    exact (list_lookup_lookup_total_lt (wl_body ws) j Hj). }
  assert (Hfilecl : forall j : nat, (j < length file)%nat ->
            wl_alnum (f (k + p0 + 3 + j)%nat)).
  { intros j Hj. rewrite (Hfb j Hj).
    destruct Hfile as [ _ Hall ].
    refine (Forall_lookup_1 _ _ _ _ Hall _).
    exact (list_lookup_lookup_total_lt file j Hj). }
  (* every index of the line, classified *)
  assert (Hclass : forall j : nat, (j < len)%nat ->
            j <> (p0 + 1)%nat -> ushp_is_sym (f (k + j)%nat) = false).
  { intros j Hj Hne.
    destruct (lt_dec j p0) as [ Hlo | Hge ]; [ exact (Hbodycl j Hlo) | ].
    destruct (Nat.eq_dec j p0) as [ -> | Hn0 ].
    { rewrite Hsp1. exact ushs_sp_not_sym. }
    destruct (Nat.eq_dec j (p0 + 2)%nat) as [ -> | Hn2 ].
    { replace (k + (p0 + 2))%nat with (k + p0 + 2)%nat by lia.
      rewrite Hsp2. exact ushs_sp_not_sym. }
    destruct (lt_dec j (p0 + 3 + length file)%nat) as [ Hfi | Hgf ].
    { assert (Hd : (j - (p0 + 3) < length file)%nat) by lia.
      replace (k + j)%nat with (k + p0 + 3 + (j - (p0 + 3)))%nat by lia.
      exact (ushs_alnum_not_sym _ (Hfilecl (j - (p0 + 3))%nat Hd)). }
    assert (Hj' : j = (p0 + 3 + length file)%nat) by lia. subst j.
    replace (k + (p0 + 3 + length file))%nat
      with (k + p0 + 3 + length file)%nat by lia.
    rewrite Hnl. exact ushs_nl_not_sym. }
  assert (Hone : ushs_one len (fun j : nat => f (k + j)%nat)
                   (Some (p0 + 1)%nat)).
  { split.
    - intros j Hj Hs.
      destruct (Nat.eq_dec j (p0 + 1)%nat) as [ -> | Hne ]; [ reflexivity | ].
      exfalso. rewrite (Hclass j Hj Hne) in Hs. discriminate.
    - intros q Hq. injection Hq as <-. split; [ lia | ].
      cbn beta. replace (k + (p0 + 1))%nat with (k + p0 + 1)%nat by lia.
      exact Hgt. }
  unfold ushs_redir. split; [ exact Hone | ].
  repeat split.
  - lia.
  - (* a blank before *)
    replace (k + (p0 + 1 - 1))%nat with (k + p0)%nat by lia.
    rewrite Hsp1. exact ushs_sp_ws.
  - (* a blank after *)
    replace (k + S (p0 + 1))%nat with (k + p0 + 2)%nat by lia.
    rewrite Hsp2. exact ushs_sp_ws.
  - lia.
  - lia.
  - (* the file name has no blank in it *)
    intros j Hj.
    assert (Hd : (j - (p0 + 3) < length file)%nat) by lia.
    replace (k + j)%nat with (k + p0 + 3 + (j - (p0 + 3)))%nat by lia.
    exact (ushs_alnum_not_ws _ (Hfilecl (j - (p0 + 3))%nat Hd)).
  - (* ...and past it there is only the newline *)
    intros j Hj.
    assert (Hj' : j = (p0 + 3 + length file)%nat) by lia. subst j.
    replace (k + (p0 + 3 + length file))%nat
      with (k + p0 + 3 + length file)%nat by lia.
    rewrite Hnl. exact ushs_nl_ws.
Qed.


(* ===================================================================== *)
(* §4 THE REDIRECT LINE IS THE TYPED LINE [LEchoF] (lane SH-CHILD)        *)
(*                                                                        *)
(* [UkSh.ush_rest_line_at]'s payload says the buffer at [k] holds the     *)
(* bytes of an admissible line of [FileDisc.uline].  At [LEcho ws] that IS *)
(* [UkSh.ush_line_is] ([UkSh.ush_line_at_echo], by conversion); at         *)
(* [LEchoF_f ws] it is the redirect shape at the model's own file name, and  *)
(* this section is that one step.  It lives HERE, below [UkShFork], because *)
(* that is where the command loop's three-way case needs it -- the         *)
(* TOKENS ([UShLexRedir]) are a file above and are not needed to know       *)
(* which walk the line takes.                                             *)
(* ===================================================================== *)

(* the file name is one alphanumeric byte, so it is a WORD *)
Lemma fname_f_word : wl_word fname_f.
Proof using. apply (bool_decide_unpack _); vm_compute; exact I. Qed.

Lemma fname_f_len : length fname_f = 1%nat.
Proof using. vm_compute; reflexivity. Qed.

(* the redirect suffix, positionally: ' ' '>' ' ' then the file name *)
Lemma suf_gtf_0 : suf_gtf !!! 0%nat = wl_sp.
Proof using. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma suf_gtf_1 : suf_gtf !!! 1%nat = ushs_gt.
Proof using. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma suf_gtf_2 : suf_gtf !!! 2%nat = wl_sp.
Proof using. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma suf_gtf_3 : suf_gtf !!! 3%nat = fname_f !!! 0%nat.
Proof using. apply bv_eq; vm_compute; reflexivity. Qed.

(* THE BRIDGE: the typed line, read positionally. *)
Lemma ushs_line_is_of_at (ws : list (list (bv 8))) (f : nat -> bv 8)
    (k len : nat) :
  UkSh.ush_line_at (LEchoF_f ws) f k len ->
  ushs_line_is ws fname_f f k len.
Proof using.
  intros (Hok & Hlen & Hby).
  destruct Hok as [ Hok _ ].
  (* the line's bytes are [wl_body ws ++ suf_gtf] and then the newline *)
  assert (Hlb : length (line_bytes (LEchoF_f ws))
                = (length (wl_body ws) + 4 + 1)%nat).
  { unfold line_bytes, line_body.
    rewrite length_app. rewrite length_app. rewrite suf_gtf_len.
    cbn [length]. lia. }
  assert (Hpre : length (wl_body ws ++ suf_gtf)
                 = (length (wl_body ws) + 4)%nat)
    by (rewrite length_app; rewrite suf_gtf_len; lia).
  (* ...so every index below the newline reads out of the two pieces *)
  assert (Hbody : forall j : nat, (j < length (wl_body ws))%nat ->
            f (k + j)%nat = wl_body ws !!! j).
  { intros j Hj. rewrite (Hby j ltac:(lia)).
    unfold line_bytes, line_body.
    rewrite (wl_lta_app_l (wl_body ws ++ suf_gtf) [wl_nl] j ltac:(lia)).
    exact (wl_lta_app_l (wl_body ws) suf_gtf j Hj). }
  assert (Hsuf : forall i : nat, (i < 4)%nat ->
            f (k + (length (wl_body ws) + i))%nat = suf_gtf !!! i).
  { intros i Hi. rewrite (Hby (length (wl_body ws) + i)%nat ltac:(lia)).
    unfold line_bytes, line_body.
    rewrite (wl_lta_app_l (wl_body ws ++ suf_gtf) [wl_nl]
               (length (wl_body ws) + i)%nat ltac:(lia)).
    exact (wl_lta_app_r (wl_body ws) suf_gtf i). }
  assert (Hnl : f (k + (length (wl_body ws) + 4))%nat = wl_nl).
  { rewrite (Hby (length (wl_body ws) + 4)%nat ltac:(lia)).
    unfold line_bytes, line_body.
    pose proof (wl_lta_app_r (wl_body ws ++ suf_gtf) [wl_nl] 0%nat) as Hr.
    rewrite Hpre in Hr. rewrite Nat.add_0_r in Hr. rewrite Hr. reflexivity. }
  unfold ushs_line_is. split_and!.
  - exact Hok.
  - exact fname_f_word.
  - rewrite Hlen. rewrite Hlb. rewrite fname_f_len. lia.
  - exact Hbody.
  - pose proof (Hsuf 0%nat ltac:(lia)) as H0.
    rewrite Nat.add_0_r in H0. rewrite H0. exact suf_gtf_0.
  - pose proof (Hsuf 1%nat ltac:(lia)) as H1.
    replace (k + length (wl_body ws) + 1)%nat
      with (k + (length (wl_body ws) + 1))%nat by lia.
    rewrite H1. exact suf_gtf_1.
  - pose proof (Hsuf 2%nat ltac:(lia)) as H2.
    replace (k + length (wl_body ws) + 2)%nat
      with (k + (length (wl_body ws) + 2))%nat by lia.
    rewrite H2. exact suf_gtf_2.
  - intros j Hj. rewrite fname_f_len in Hj.
    replace j with 0%nat by lia. rewrite Nat.add_0_r.
    pose proof (Hsuf 3%nat ltac:(lia)) as H3.
    replace (k + length (wl_body ws) + 3)%nat
      with (k + (length (wl_body ws) + 3))%nat by lia.
    rewrite H3. exact suf_gtf_3.
  - rewrite fname_f_len.
    replace (k + length (wl_body ws) + 3 + 1)%nat
      with (k + (length (wl_body ws) + 4))%nat by lia.
    exact Hnl.
Qed.

(* ...AND ITS FIRST BYTE IS 'e', which is the ONE reading sh's body makes
   of a line ([UkShFork.wp_kshm_body_at]'s [Hlp0]): the redirect line's
   command word is echo's, because [ushs_line_is] carries the same
   [EchoDisc.line_ok]. *)
Lemma ushs_line_is_byte0 (ws : list (list (bv 8))) (file : list (bv 8))
    (f : nat -> bv 8) (k len : nat) :
  ushs_line_is ws file f k len -> bv_unsigned (f k) = 101%Z.
Proof using.
  intros (Hok & _ & _ & Hbody & _).
  assert (Hpos : (0 < length (wl_body ws))%nat).
  { destruct ws as [| w r ]; [ exfalso; exact (Nat.nlt_0_r 0 (line_ok_pos [] Hok)) | ].
    destruct (wl_wf_cons w r (line_ok_wf _ Hok)) as [ Hword _ ].
    rewrite wl_body_cons. rewrite length_app.
    pose proof (wl_word_pos w Hword). lia. }
  pose proof (Hbody 0%nat Hpos) as H0. rewrite Nat.add_0_r in H0.
  rewrite H0.
  rewrite <- (wl_lta_app_l (wl_body ws) [wl_nl] 0%nat Hpos).
  exact (line_ok_head_byte0 ws Hok).
Qed.

(* ...AND THE LINE RE-BASED AT ITS OWN START, which is the form the CHILD's
   law is stated at ([UkShFork.ushf_child_law_at]: the child holds a copy of
   the line at [s0] and reads it from 0).  [UkSh.ush_line_is] needs no such
   lemma -- it writes every index as [f (k + j)] and the re-basing is a
   conversion -- while this predicate names three bytes by POSITION
   ([f (k + p0 + 1)] and its neighbours), and [k + (0 + p0 + 1)] is not
   convertible to [k + p0 + 1] with [k] a variable. *)
Lemma ushs_line_is_shift (ws : list (list (bv 8))) (file : list (bv 8))
    (f : nat -> bv 8) (k len : nat) :
  ushs_line_is ws file f k len ->
  ushs_line_is ws file (fun j : nat => f (k + j)%nat) 0%nat len.
Proof using.
  intros (Hok & Hfile & Hlen & Hbody & Hsp1 & Hgt & Hsp2 & Hfb & Hnl).
  unfold ushs_line_is. split_and!.
  - exact Hok.
  - exact Hfile.
  - exact Hlen.
  - intros j Hj. cbn beta. rewrite Nat.add_0_l. exact (Hbody j Hj).
  - cbn beta. rewrite Nat.add_0_l. exact Hsp1.
  - cbn beta.
    replace (k + (0 + length (wl_body ws) + 1))%nat
      with (k + length (wl_body ws) + 1)%nat by lia.
    exact Hgt.
  - cbn beta.
    replace (k + (0 + length (wl_body ws) + 2))%nat
      with (k + length (wl_body ws) + 2)%nat by lia.
    exact Hsp2.
  - intros j Hj. cbn beta.
    replace (k + (0 + length (wl_body ws) + 3 + j))%nat
      with (k + length (wl_body ws) + 3 + j)%nat by lia.
    exact (Hfb j Hj).
  - cbn beta.
    replace (k + (0 + length (wl_body ws) + 3 + length file))%nat
      with (k + length (wl_body ws) + 3 + length file)%nat by lia.
    exact Hnl.
Qed.
