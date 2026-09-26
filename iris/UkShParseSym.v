(* ===================================================================== *)
(* UkShParseSym.v -- THE LINE MODEL WITH ONE SYMBOL BYTE, lane SH-PARSE.  *)
(*                                                                        *)
(* Stage 4's whole parser is scoped by [UkShParse.ushp_no_symbols]: the    *)
(* line has no byte of sh's symbol table in it, which keeps [gettoken] in  *)
(* its default arm and every constructor but [execcmd] out of the walk.    *)
(* The FILE application needs one line that is not of that shape --        *)
(*                                                                        *)
(*     echo w1 ... wn > f                                                  *)
(*                                                                        *)
(* -- and this file is the pure vocabulary for it.  Nothing here is an     *)
(* Iris proposition and nothing here mentions a register: it is the byte   *)
(* algebra the redirect walks are stated over, so that a 500-line walk     *)
(* file never has to [cbn] a [Fixpoint] in a proofmode goal.               *)
(*                                                                        *)
(* THE MODEL IS AN OPTION, NOT A SECOND PREDICATE.  [ushs_one len f o]     *)
(* says: every symbol byte in the line is at [o], and if [o] is a       *)
(* position then the byte there is '>'.  At [o = None] it IS              *)
(* [ushp_no_symbols] ([ushs_one_none], both directions), so the landed     *)
(* stage-4 lemmas are this model's symbol-free instance rather than a      *)
(* parallel development -- which is what lets a redirect walk and a        *)
(* symbol-free walk share every pure lemma below.                          *)
(*                                                                        *)
(* THE TOKEN MODEL IS GENERALISED THE SAME WAY.  [UkShParse.ushp_tokens]   *)
(* has NO INHABITANT on a line with a reachable symbol byte: its [Cons]    *)
(* needs [0 < ushp_toklen], which is 0 at a symbol, and its [Nil] needs the *)
(* blank scan to reach [len].  So a redirect line's ARGUMENT tokens are    *)
(* not [ushp_tokens] of anything.  [ushs_toks len f stop off toks] is the  *)
(* same induction with the terminator a PARAMETER, and                     *)
(* [ushs_toks_tokens] proves [stop = len] is exactly [ushp_tokens] --      *)
(* again an instance, not a clone.                                         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
Require Import RiscvModelBytes.
Require Import UmodeAbi.
Require Import UkShParse.
Local Open Scope Z_scope.


(* ===================================================================== *)
(* §1 THE BYTE CLASSES                                                    *)
(* ===================================================================== *)

(* the ONE symbol byte a stage-4+ line may carry *)
Definition ushs_gt : bv 8 := Z_to_bv 8 62.

Lemma ushs_gt_val : bv_unsigned ushs_gt = 62.
Proof. vm_compute. reflexivity. Qed.

Lemma ushs_gt_sym : ushp_is_sym ushs_gt = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ushs_gt_not_ws : ushp_is_ws ushs_gt = false.
Proof. vm_compute. reflexivity. Qed.

Lemma ushs_gt_not_nul : ushs_gt <> ubyte0.
Proof. vm_compute. discriminate. Qed.

(* a whitespace byte is never a symbol byte, and never '>' -- the two
   one-line facts a canonical redirect's blanks are read through *)
Lemma ushs_ws_not_sym (b : bv 8) : ushp_is_ws b = true -> ushp_is_sym b = false.
Proof.
  unfold ushp_is_ws, ushp_is_sym.
  rewrite bool_decide_eq_true, bool_decide_eq_false.
  unfold ushp_ws_bytes, ushp_sym_bytes. cbn [fmap list_fmap].
  intro Hin. intro Hin'.
  repeat (apply elem_of_cons in Hin as [ -> | Hin ];
          [ revert Hin'; clear;
            intro H; repeat (apply elem_of_cons in H as [ H | H ];
                             [ revert H; vm_compute; discriminate | ]);
            apply elem_of_nil in H; exact H
          | ]).
  apply elem_of_nil in Hin. exact Hin.
Qed.

Lemma ushs_ws_not_gt (b : bv 8) : ushp_is_ws b = true -> b <> ushs_gt.
Proof.
  intros Hws ->. rewrite ushs_gt_not_ws in Hws. discriminate.
Qed.


(* ===================================================================== *)
(* §2 THE LINE MODEL: AT MOST ONE SYMBOL BYTE, AND IT IS A '>'            *)
(* ===================================================================== *)

Definition ushs_one (len : nat) (f : nat -> bv 8) (o : option nat) : Prop :=
  (forall j : nat, (j < len)%nat -> ushp_is_sym (f j) = true -> o = Some j)
  /\ (forall p : nat, o = Some p -> (p < len)%nat /\ f p = ushs_gt).

(* THE SYMBOL-FREE INSTANCE, both ways: the landed stage-4 premise is this
   model at [None] and nothing else. *)
Lemma ushs_one_none (len : nat) (f : nat -> bv 8) :
  ushs_one len f None <-> ushp_no_symbols len f.
Proof.
  split.
  - intros [ H1 _ ] j Hj.
    destruct (ushp_is_sym (f j)) eqn:E; [ | reflexivity ].
    exfalso. discriminate (H1 j Hj E).
  - intro H. split; [ | intros p Hp; discriminate Hp ].
    intros j Hj Hs. rewrite (H j Hj) in Hs. discriminate.
Qed.

(* ...and the two readings of the [Some] instance a walk needs *)
Lemma ushs_one_some_at (len : nat) (f : nat -> bv 8) (p : nat) :
  ushs_one len f (Some p) -> (p < len)%nat /\ f p = ushs_gt.
Proof. intros [ _ H ]. exact (H p eq_refl). Qed.

Lemma ushs_one_some_off (len : nat) (f : nat -> bv 8) (p j : nat) :
  ushs_one len f (Some p) -> (j < len)%nat -> j <> p ->
  ushp_is_sym (f j) = false.
Proof.
  intros [ H1 _ ] Hj Hne.
  destruct (ushp_is_sym (f j)) eqn:E; [ | reflexivity ].
  exfalso. apply Hne. injection (H1 j Hj E) as He. exact (eq_sym He).
Qed.

(* every byte of the line except the '>' is a symbol-free byte, so the
   line RESTRICTED to any window that misses [p] satisfies the landed
   premise -- this is how a redirect walk reuses a stage-4 lemma on the
   prefix it did not change *)
Lemma ushs_one_nosym_below (len : nat) (f : nat -> bv 8) (p : nat) :
  ushs_one len f (Some p) -> ushp_no_symbols p f.
Proof.
  intros Hone j Hj.
  destruct (ushs_one_some_at len f p Hone) as [ Hp _ ].
  exact (ushs_one_some_off len f p j Hone ltac:(lia) ltac:(lia)).
Qed.


(* ===================================================================== *)
(* §3 THE CANONICAL REDIRECT SHAPE                                        *)
(*                                                                        *)
(*   ... w   >   f \n                                                     *)
(*         ^p                                                             *)
(* one blank at [p-1], one blank at [p+1], the file name is the run       *)
(* [[S (S p), e)] and everything from [e] to the end of the line is blank *)
(* (that is the newline [gets] kept).  design/app-file.md SS5.1.           *)
(* ===================================================================== *)

Definition ushs_redir (len : nat) (f : nat -> bv 8) (p e : nat) : Prop :=
  ushs_one len f (Some p)
  /\ (0 < p)%nat
  /\ ushp_is_ws (f (p - 1)%nat) = true
  /\ ushp_is_ws (f (S p)) = true
  /\ (S (S p) < e)%nat
  /\ (e < len)%nat
  /\ (forall j : nat, (S (S p) <= j < e)%nat -> ushp_is_ws (f j) = false)
  /\ (forall j : nat, (e <= j < len)%nat -> ushp_is_ws (f j) = true).

Lemma ushs_redir_one (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e -> ushs_one len f (Some p).
Proof. by intros (H & _ & _ & _ & _ & _ & _ & _). Qed.

Lemma ushs_redir_gt (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e -> f p = ushs_gt.
Proof.
  intro H. exact (proj2 (ushs_one_some_at len f p (ushs_redir_one _ _ _ _ H))).
Qed.

Lemma ushs_redir_lt (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e -> (p < len)%nat.
Proof.
  intro H. exact (proj1 (ushs_one_some_at len f p (ushs_redir_one _ _ _ _ H))).
Qed.

(* THE '>>' LOOKAHEAD IS REFUTED, and not by a side premise: the byte after
   the '>' is a blank, and no blank is a '>'.  This is what
   [UkShRedirTok.wp_kshp_gtk_disp_gt]'s third hypothesis asks for. *)
Lemma ushs_redir_next (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e -> f (S p) <> ushs_gt.
Proof.
  intros (_ & _ & _ & Hws & _ & _ & _ & _). exact (ushs_ws_not_gt _ Hws).
Qed.

Lemma ushs_redir_sp_lt (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e -> (S p < len)%nat.
Proof. intros (_ & _ & _ & _ & H1 & H2 & _ & _). lia. Qed.

(* the file name's bytes are neither blank nor symbol, so [ushp_toklen]
   measures it exactly *)
Lemma ushs_redir_file_byte (len : nat) (f : nat -> bv 8) (p e j : nat) :
  ushs_redir len f p e -> (S (S p) <= j < e)%nat ->
  ushp_is_ws (f j) = false /\ ushp_is_sym (f j) = false.
Proof.
  intros Hr Hj.
  destruct Hr as (Hone & Hp0 & Hb1 & Hb2 & Hlo & Hhi & Hfw & Htail).
  split; [ exact (Hfw j Hj) | ].
  exact (ushs_one_some_off len f p j Hone ltac:(lia) ltac:(lia)).
Qed.


(* ===================================================================== *)
(* §4 THE SCAN MEASURES AT THE REDIRECT SHAPE                             *)
(* ===================================================================== *)

(* a run of [n] whitespace-free bytes is measured exactly *)
Lemma ushs_toklen_exact (n i b : nat) (f : nat -> bv 8) :
  (i + b <= i + n)%nat ->
  (forall j : nat, (i <= j < i + b)%nat ->
     ushp_is_ws (f j) = false /\ ushp_is_sym (f j) = false) ->
  (ushp_is_ws (f (i + b)%nat) = true \/ ushp_is_sym (f (i + b)%nat) = true) ->
  ushp_toklen n i f = b.
Proof.
  revert n i. induction b as [| b IH ]; intros n i Hle Hin Hstop.
  - rewrite Nat.add_0_r in Hstop. destruct n as [| n ]; cbn; [ reflexivity | ].
    destruct Hstop as [ H | H ]; rewrite H; [ reflexivity | ].
    rewrite orb_true_r. reflexivity.
  - destruct n as [| n ]; [ lia | ].
    destruct (Hin i ltac:(lia)) as [ Hw Hs ].
    cbn [ushp_toklen]. rewrite Hw, Hs. cbn [orb].
    f_equal. apply IH; [ lia | | ].
    + intros j Hj. exact (Hin j ltac:(lia)).
    + replace (S i + b)%nat with (i + S b)%nat by lia. exact Hstop.
Qed.

(* ...and a run of [b] whitespace bytes likewise *)
Lemma ushs_skipws_exact (n i b : nat) (f : nat -> bv 8) :
  (i + b <= i + n)%nat ->
  (forall j : nat, (i <= j < i + b)%nat -> ushp_is_ws (f j) = true) ->
  ((i + b)%nat = (i + n)%nat \/ ushp_is_ws (f (i + b)%nat) = false) ->
  ushp_skipws n i f = b.
Proof.
  revert n i. induction b as [| b IH ]; intros n i Hle Hin Hstop.
  - rewrite Nat.add_0_r in Hstop.
    destruct n as [| n ]; cbn; [ reflexivity | ].
    destruct Hstop as [ H | H ]; [ lia | rewrite H; reflexivity ].
  - destruct n as [| n ]; [ lia | ].
    cbn [ushp_skipws]. rewrite (Hin i ltac:(lia)).
    f_equal. apply IH; [ lia | | ].
    + intros j Hj. exact (Hin j ltac:(lia)).
    + replace (S i + b)%nat with (i + S b)%nat by lia.
      replace (S i + n)%nat with (i + S n)%nat by lia. exact Hstop.
Qed.

(* the blank scan stops dead at the '>' *)
Lemma ushs_skipws_at_gt (len : nat) (f : nat -> bv 8) (p e n : nat) :
  ushs_redir len f p e -> ushp_skipws n p f = 0%nat.
Proof.
  intro Hr. apply ushp_skipws_stop.
  destruct (ushp_is_ws (f p)) eqn:E; [ exfalso | reflexivity ].
  rewrite (ushs_redir_gt len f p e Hr), ushs_gt_not_ws in E. discriminate.
Qed.

(* the token scan does too: [gettoken] at the '>' takes the SWITCH arm, and
   the default arm's measure is 0 there *)
Lemma ushs_toklen_at_gt (len : nat) (f : nat -> bv 8) (p e n : nat) :
  ushs_redir len f p e -> ushp_toklen n p f = 0%nat.
Proof.
  intro Hr. destruct n as [| n ]; cbn [ushp_toklen]; [ reflexivity | ].
  rewrite (ushs_redir_gt len f p e Hr), ushs_gt_sym, orb_true_r. reflexivity.
Qed.

(* ONE blank between the '>' and the file name *)
Lemma ushs_skipws_after_gt (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e -> ushp_skipws (len - S p) (S p) f = 1%nat.
Proof.
  intro Hr. pose proof Hr as HR.
  destruct HR as (Hone & Hp0 & Hb1 & Hb2 & Hlo & Hhi & Hfw & Htail).
  apply (ushs_skipws_exact (len - S p) (S p) 1 f).
  - lia.
  - intros j Hj. replace j with (S p) by lia. exact Hb2.
  - right. replace (S p + 1)%nat with (S (S p)) by lia.
    exact (Hfw (S (S p)) ltac:(lia)).
Qed.

(* the file name is the token [[S (S p), e)] *)
Lemma ushs_toklen_file (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e ->
  ushp_toklen (len - S (S p)) (S (S p)) f = (e - S (S p))%nat.
Proof.
  intro Hr. pose proof Hr as HR.
  destruct HR as (Hone & Hp0 & Hb1 & Hb2 & Hlo & Hhi & Hfw & Htail).
  apply (ushs_toklen_exact (len - S (S p)) (S (S p)) (e - S (S p)) f).
  - lia.
  - intros j Hj. exact (ushs_redir_file_byte len f p e j Hr ltac:(lia)).
  - left. replace (S (S p) + (e - S (S p)))%nat with e by lia.
    exact (Htail e ltac:(lia)).
Qed.

(* ...and past it there is nothing but blanks, so the line ends there *)
Lemma ushs_skipws_tail (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e -> ushp_skipws (len - e) e f = (len - e)%nat.
Proof.
  intro Hr. pose proof Hr as HR.
  destruct HR as (Hone & Hp0 & Hb1 & Hb2 & Hlo & Hhi & Hfw & Htail).
  apply (ushs_skipws_exact (len - e) e (len - e) f).
  - lia.
  - intros j Hj. exact (Htail j ltac:(lia)).
  - left. reflexivity.
Qed.


(* ===================================================================== *)
(* §5 THE TOKEN MODEL WITH A TERMINATOR                                   *)
(*                                                                        *)
(* [UkShParse.ushp_tokens] is [ushs_toks] at [stop = len]; on a line whose *)
(* symbol byte is reachable it has no inhabitant at all, which is why the  *)
(* argument loop's invariant needs the terminator as a parameter.          *)
(* ===================================================================== *)

Inductive ushs_toks (len : nat) (f : nat -> bv 8) (stop : nat)
  : nat -> list (nat * nat) -> Prop :=
| UshsTokNil (off : nat) :
    (off + ushp_skipws (len - off) off f = stop)%nat ->
    ushs_toks len f stop off []
| UshsTokCons (off : nat) (toks : list (nat * nat)) :
    let k := ushp_skipws (len - off) off f in
    let n := ushp_toklen (len - (off + k)) (off + k) f in
    (0 < n)%nat ->
    ushs_toks len f stop (off + k + n)%nat toks ->
    ushs_toks len f stop off ((off + k, off + k + n)%nat :: toks).

Lemma ushs_toks_tokens (len : nat) (f : nat -> bv 8) (off : nat)
    (toks : list (nat * nat)) :
  ushs_toks len f len off toks -> ushp_tokens len f off toks.
Proof.
  induction 1 as [ off Hnil | off toks k n Hn _ IH ];
    [ exact (UshpTokNil len f off Hnil) | exact (UshpTokCons len f off toks Hn IH) ].
Qed.

Lemma ushp_tokens_toks (len : nat) (f : nat -> bv 8) (off : nat)
    (toks : list (nat * nat)) :
  ushp_tokens len f off toks -> ushs_toks len f len off toks.
Proof.
  induction 1 as [ off Hnil | off toks k n Hn _ IH ];
    [ exact (UshsTokNil len f len off Hnil) | exact (UshsTokCons len f len off toks Hn IH) ].
Qed.

(* the two facts every consumer of a token list needs, at the terminator
   form -- [UkShParse.ushp_tokens_in] with no [stop] bound at all, because
   a token's END is bounded by the SCAN's [len] and not by the terminator *)
Lemma ushs_toks_in (len : nat) (f : nat -> bv 8) (stop off : nat)
    (toks : list (nat * nat)) :
  ushs_toks len f stop off toks ->
  forall (i : nat) (t : nat * nat), toks !! i = Some t ->
    (off <= fst t < snd t /\ snd t <= len)%nat.
Proof.
  induction 1 as [ off Hnil | off toks k n Hn Htoks IH ]; intros i t Hi.
  - rewrite lookup_nil in Hi. discriminate.
  - assert (Hk : (k <= len - off)%nat)
      by exact (ushp_skipws_le (len - off) off f).
    assert (Hn' : (n <= len - (off + k))%nat)
      by exact (ushp_toklen_le (len - (off + k)) (off + k) f).
    destruct i as [| i ]; cbn in Hi.
    + injection Hi as <-. cbn. lia.
    + destruct (IH i t Hi) as [ Hlo Hhi ]. split; lia.
Qed.

(* ...and a run that terminates at [stop] never runs past it *)
Lemma ushs_toks_le (len : nat) (f : nat -> bv 8) (stop off : nat)
    (toks : list (nat * nat)) :
  ushs_toks len f stop off toks -> (off <= stop)%nat.
Proof.
  induction 1 as [ off Hnil | off toks k n Hn Htoks IH ]; lia.
Qed.


(* ===================================================================== *)
(* §6 GETTOKEN'S ANSWER, AT ONE SYMBOL                                    *)
(*                                                                        *)
(* [UkShParseTok.ushp_gettok_res] / [_end] / [_fin] are the symbol-free    *)
(* instances of these three; the bridge lemmas below are what let a walk   *)
(* at [ushs_one _ _ None] read the landed spelling back.                   *)
(* ===================================================================== *)

(* WHAT gettoken NEEDS TO KNOW ABOUT THE LINE, and nothing more: every
   symbol byte in it is a '>' that is neither the last byte of the line nor
   doubled.  That is precisely the premise of
   [UkShRedirGtk.wp_kshp_gettoken_sym] -- the first conjunct keeps the six
   other switch arms refuted, the second and third refute the '>>'
   lookahead at 0x3ae/0x3b6.  Both line shapes below satisfy it. *)
Definition ushs_gt_ok (len : nat) (f : nat -> bv 8) : Prop :=
  forall j : nat, (j < len)%nat -> ushp_is_sym (f j) = true ->
    f j = ushs_gt /\ (S j < len)%nat /\ f (S j) <> ushs_gt.

(* the SYMBOL-FREE instance: stage 4's landed premise implies it vacuously *)
Lemma ushs_gt_ok_nosym (len : nat) (f : nat -> bv 8) :
  ushp_no_symbols len f -> ushs_gt_ok len f.
Proof.
  intros Hns j Hj Hs. rewrite (Hns j Hj) in Hs. discriminate.
Qed.

(* ...and the canonical redirect satisfies it too *)
Lemma ushs_gt_ok_redir (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e -> ushs_gt_ok len f.
Proof.
  intros Hr j Hj Hs.
  assert (Hjp : j = p).
  { destruct (Nat.eq_dec j p) as [ He | Hne ]; [ exact He | exfalso ].
    rewrite (ushs_one_some_off len f p j (ushs_redir_one _ _ _ _ Hr) Hj Hne)
      in Hs. discriminate. }
  subst j. split; [ exact (ushs_redir_gt len f p e Hr) | ].
  split.
  - destruct Hr as (_ & _ & _ & _ & H1 & H2 & _ & _). lia.
  - exact (ushs_redir_next len f p e Hr).
Qed.


Definition ushs_gettok_res (len : nat) (f : nat -> bv 8) (k : nat) : Z :=
  if bool_decide (k < len)%nat
  then (if ushp_is_sym (f k) then bv_unsigned (f k) else 97)
  else 0.

Definition ushs_gettok_end (len : nat) (f : nat -> bv 8) (k : nat) : nat :=
  if bool_decide (k < len)%nat
  then (if ushp_is_sym (f k) then S k else (k + ushp_toklen (len - k) k f)%nat)
  else k.

Definition ushs_gettok_fin (len : nat) (f : nat -> bv 8) (k : nat) : nat :=
  let e := ushs_gettok_end len f k in (e + ushp_skipws (len - e) e f)%nat.

(* ---- the symbol-free instance: the landed spellings, verbatim -------- *)

Lemma ushs_gettok_res_nosym (len : nat) (f : nat -> bv 8) (k : nat) :
  ushp_no_symbols len f -> (k <= len)%nat ->
  ushs_gettok_res len f k = (if bool_decide (k < len)%nat then 97 else 0).
Proof.
  intros Hns Hk. unfold ushs_gettok_res.
  destruct (bool_decide (k < len)%nat) eqn:E; [ | reflexivity ].
  apply bool_decide_eq_true in E. rewrite (Hns k E). reflexivity.
Qed.

Lemma ushs_gettok_end_nosym (len : nat) (f : nat -> bv 8) (k : nat) :
  ushp_no_symbols len f -> (k <= len)%nat ->
  ushs_gettok_end len f k = (k + ushp_toklen (len - k) k f)%nat.
Proof.
  intros Hns Hk. unfold ushs_gettok_end.
  destruct (bool_decide (k < len)%nat) eqn:E.
  - apply bool_decide_eq_true in E. rewrite (Hns k E). reflexivity.
  - apply bool_decide_eq_false in E.
    assert (Hke : k = len) by lia. subst k.
    rewrite Nat.sub_diag. cbn [ushp_toklen]. lia.
Qed.

(* ---- and the three readings a redirect walk turns on ----------------- *)

Lemma ushs_gettok_res_gt (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e -> ushs_gettok_res len f p = 62.
Proof.
  intro Hr. unfold ushs_gettok_res.
  rewrite (bool_decide_eq_true_2 _ (ushs_redir_lt len f p e Hr)).
  rewrite (ushs_redir_gt len f p e Hr), ushs_gt_sym, ushs_gt_val. reflexivity.
Qed.

Lemma ushs_gettok_end_gt (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e -> ushs_gettok_end len f p = S p.
Proof.
  intro Hr. unfold ushs_gettok_end.
  rewrite (bool_decide_eq_true_2 _ (ushs_redir_lt len f p e Hr)).
  rewrite (ushs_redir_gt len f p e Hr), ushs_gt_sym. reflexivity.
Qed.

(* the cursor after the '>' token: one blank, then the file name *)
Lemma ushs_gettok_fin_gt (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e -> ushs_gettok_fin len f p = S (S p).
Proof.
  intro Hr. unfold ushs_gettok_fin. rewrite (ushs_gettok_end_gt len f p e Hr).
  rewrite (ushs_skipws_after_gt len f p e Hr). lia.
Qed.

(* ...and the file-name token that follows it *)
Lemma ushs_gettok_res_file (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e -> ushs_gettok_res len f (S (S p)) = 97.
Proof.
  intro Hr. unfold ushs_gettok_res.
  assert (Hlt : (S (S p) < len)%nat)
    by (destruct Hr as (_ & _ & _ & _ & H1 & H2 & _ & _); lia).
  rewrite (bool_decide_eq_true_2 _ Hlt).
  rewrite (proj2 (ushs_redir_file_byte len f p e (S (S p)) Hr
                    ltac:(destruct Hr as (_ & _ & _ & _ & H1 & _); lia))).
  reflexivity.
Qed.

Lemma ushs_gettok_end_file (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e -> ushs_gettok_end len f (S (S p)) = e.
Proof.
  intro Hr. unfold ushs_gettok_end.
  assert (Hlt : (S (S p) < len)%nat)
    by (destruct Hr as (_ & _ & _ & _ & H1 & H2 & _ & _); lia).
  rewrite (bool_decide_eq_true_2 _ Hlt).
  rewrite (proj2 (ushs_redir_file_byte len f p e (S (S p)) Hr
                    ltac:(destruct Hr as (_ & _ & _ & _ & H1 & _); lia))).
  rewrite (ushs_toklen_file len f p e Hr).
  destruct Hr as (_ & _ & _ & _ & H1 & H2 & _ & _). lia.
Qed.

Lemma ushs_gettok_fin_file (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushs_redir len f p e -> ushs_gettok_fin len f (S (S p)) = len.
Proof.
  intro Hr. unfold ushs_gettok_fin. rewrite (ushs_gettok_end_file len f p e Hr).
  rewrite (ushs_skipws_tail len f p e Hr).
  destruct Hr as (_ & _ & _ & _ & H1 & H2 & _ & _). lia.
Qed.

(* the line is EXHAUSTED after the file name, so the next [gettoken]
   answers 0 and [parseexec]'s loop stops *)
Lemma ushs_gettok_res_end (len : nat) (f : nat -> bv 8) :
  ushs_gettok_res len f len = 0.
Proof.
  unfold ushs_gettok_res.
  rewrite (bool_decide_eq_false_2 (len < len)%nat ltac:(lia)).
  reflexivity.
Qed.


(* ===================================================================== *)
(* §7 WHAT THE ARGUMENT LOOP READS OFF THE MODEL                          *)
(*                                                                        *)
(* [UkShParseExec.wp_kshp_pex_loop] turns on three readings of the token   *)
(* model ([ushp_tokens_nil_inv] / [_cons_inv'] / [_skip]) and three of     *)
(* gettoken's answer.  At the redirect shape the loop's invariant is       *)
(* [ushs_toks] and the answers are [ushs_gettok_*], so these are the same  *)
(* six facts in this file's vocabulary -- pure, so the walk file never     *)
(* [cbn]s a [Fixpoint] under a proofmode goal.                             *)
(* ===================================================================== *)

(* a token of positive length starts at a byte that is neither blank nor
   symbol -- which is what makes the loop's [peek] miss and gettoken's
   answer 'a' *)
Lemma ushs_toklen_pos_nosym (n i : nat) (f : nat -> bv 8) :
  (0 < ushp_toklen n i f)%nat -> ushp_is_sym (f i) = false.
Proof.
  intro Hpos. destruct (ushp_is_sym (f i)) eqn:E; [ exfalso | reflexivity ].
  rewrite (ushp_toklen_stop n i f ltac:(rewrite E; rewrite orb_true_r; reflexivity))
    in Hpos. lia.
Qed.

Lemma ushs_toklen_pos_nows (n i : nat) (f : nat -> bv 8) :
  (0 < ushp_toklen n i f)%nat -> ushp_is_ws (f i) = false.
Proof.
  intro Hpos. destruct (ushp_is_ws (f i)) eqn:E; [ exfalso | reflexivity ].
  rewrite (ushp_toklen_stop n i f ltac:(rewrite E; reflexivity)) in Hpos. lia.
Qed.

(* ---- the three readings of [ushs_toks] ------------------------------- *)

Lemma ushs_toks_nil' (len stop i : nat) (f : nat -> bv 8) :
  (i + ushp_skipws (len - i) i f)%nat = stop -> ushs_toks len f stop i [].
Proof. intro H. exact (UshsTokNil len f stop i H). Qed.

Lemma ushs_toks_cons' (len stop : nat) (f : nat -> bv 8) (i n : nat)
    (toks : list (nat * nat)) :
  ushp_skipws (len - i) i f = 0%nat ->
  ushp_toklen (len - i) i f = n ->
  (0 < n)%nat ->
  ushs_toks len f stop (i + n)%nat toks ->
  ushs_toks len f stop i ((i, (i + n)%nat) :: toks).
Proof.
  intros Hk Hn Hpos Ht.
  assert (E : (i + ushp_skipws (len - i) i f)%nat = i) by (rewrite Hk; lia).
  assert (C := UshsTokCons len f stop i toks).
  cbv zeta in C. rewrite E in C. rewrite Hn in C.
  exact (C Hpos Ht).
Qed.

Lemma ushs_toks_nil_inv (len stop i : nat) (f : nat -> bv 8) :
  ushs_toks len f stop i [] -> (i + ushp_skipws (len - i) i f)%nat = stop.
Proof. inversion 1. assumption. Qed.

Lemma ushs_toks_cons_inv (len stop i : nat) (f : nat -> bv 8)
    (tk : nat * nat) (rest : list (nat * nat)) :
  ushs_toks len f stop i (tk :: rest) ->
  (0 < ushp_toklen (len - (i + ushp_skipws (len - i) i f))
         (i + ushp_skipws (len - i) i f) f)%nat /\
  tk = ((i + ushp_skipws (len - i) i f)%nat,
        (i + ushp_skipws (len - i) i f
         + ushp_toklen (len - (i + ushp_skipws (len - i) i f))
             (i + ushp_skipws (len - i) i f) f)%nat) /\
  ushs_toks len f stop
    (i + ushp_skipws (len - i) i f
     + ushp_toklen (len - (i + ushp_skipws (len - i) i f))
         (i + ushp_skipws (len - i) i f) f)%nat rest.
Proof.
  inversion 1 as [ | off toks0 Hn Ht Eoff Etoks ]; subst.
  cbv zeta in *. split; [ assumption | ].
  split; [ reflexivity | assumption ].
Qed.

Lemma ushs_toks_cons_inv' (len stop i j q : nat) (f : nat -> bv 8)
    (tk : nat * nat) (rest : list (nat * nat)) :
  j = (i + ushp_skipws (len - i) i f)%nat ->
  q = ushp_toklen (len - j) j f ->
  ushs_toks len f stop i (tk :: rest) ->
  (0 < q)%nat /\ tk = (j, (j + q)%nat) /\ ushs_toks len f stop (j + q)%nat rest.
Proof. intros -> ->. apply ushs_toks_cons_inv. Qed.

Lemma ushs_toks_skip (len stop : nat) (f : nat -> bv 8) (off : nat)
    (toks : list (nat * nat)) :
  (off <= len)%nat ->
  ushs_toks len f stop off toks ->
  ushs_toks len f stop (off + ushp_skipws (len - off) off f)%nat toks.
Proof.
  intros Hoff H.
  pose proof (ushp_skipws_idem len off f Hoff) as Hk0.
  pose proof (ushp_skipws_le (len - off) off f) as Hle.
  destruct toks as [| tk rest ].
  - apply ushs_toks_nil'.
    pose proof (ushs_toks_nil_inv len stop off f H) as Hnil. lia.
  - destruct (ushs_toks_cons_inv len stop off f tk rest H)
      as (Hn & Htk & Hrest).
    subst tk.
    exact (ushs_toks_cons' len stop f (off + ushp_skipws (len - off) off f)
             (ushp_toklen (len - (off + ushp_skipws (len - off) off f))
                (off + ushp_skipws (len - off) off f) f) rest
             Hk0 eq_refl Hn Hrest).
Qed.


(* ---- and the three readings of gettoken's answer at a WORD ----------- *)

Lemma ushs_gettok_res_word (len : nat) (f : nat -> bv 8) (k : nat) :
  (k < len)%nat -> ushp_is_sym (f k) = false -> ushs_gettok_res len f k = 97.
Proof.
  intros Hk Hs. unfold ushs_gettok_res.
  rewrite (bool_decide_eq_true_2 _ Hk), Hs. reflexivity.
Qed.

Lemma ushs_gettok_end_word (len : nat) (f : nat -> bv 8) (k : nat) :
  (k < len)%nat -> ushp_is_sym (f k) = false ->
  ushs_gettok_end len f k = (k + ushp_toklen (len - k) k f)%nat.
Proof.
  intros Hk Hs. unfold ushs_gettok_end.
  rewrite (bool_decide_eq_true_2 _ Hk), Hs. reflexivity.
Qed.

Lemma ushs_gettok_end_stop (len : nat) (f : nat -> bv 8) :
  ushs_gettok_end len f len = len.
Proof.
  unfold ushs_gettok_end.
  rewrite (bool_decide_eq_false_2 (len < len)%nat ltac:(lia)). reflexivity.
Qed.

Lemma ushs_gettok_fin_stop (len : nat) (f : nat -> bv 8) :
  ushs_gettok_fin len f len = len.
Proof.
  unfold ushs_gettok_fin. rewrite ushs_gettok_end_stop.
  rewrite Nat.sub_diag. cbn [ushp_skipws]. lia.
Qed.
