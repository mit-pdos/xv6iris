(* ===================================================================== *)
(*  LineBytes.v -- THE BYTE FACTS THE DETERMINACY ARGUMENT SPENDS, once.  *)
(*                                                                       *)
(*  Every application's determinacy theorem (two expected sessions       *)
(*  below one wire are the same bytes) runs on ONE observation about     *)
(*  the console: '$' is the byte the prompt opens on and nothing a round  *)
(*  writes before its prompt carries -- not a word, not a blank, not a    *)
(*  newline, and so not any content echo can have written.  Two '$'-free  *)
(*  runs each closed by the prompt are therefore comparable byte by byte  *)
(*  ([lb_dollar_split]), a settled prologue whose first byte is '$' is    *)
(*  the bare prompt ([lb_prompt_of_dollar]), and the one collision the    *)
(*  prompt does not settle -- a round whose own output IS sh's panic line *)
(*  (the fork line) -- is forced to be exactly that line               *)
(*  ([lb_out_eq_panic]).                                                 *)
(*                                                                       *)
(*  These were proved twice, under [FileDisc]'s and [PipeDisc]'s own      *)
(*  names, so that neither model imported the other; the line model      *)
(*  ([LineModel.v]) proves the determinacy theorem once over them, and   *)
(*  both models now read them from here.                                 *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list bitvector.definitions.
Require Import LineWords.        (* [wl_nl], [wl_body_byte], the raw-line facts *)
Require Import EchoDisc.         (* [u_prompt], [alt_panic], [pro_of], [pro_done] *)
From stdpp Require Import ssreflect.

(* ====================================================================== *)
(*  0.  SMALL LIST AND PREFIX FACTS                                        *)
(* ====================================================================== *)

Lemma lb_prefix_lookup {A} (u v : list A) (i : A) (n : nat) :
  u `prefix_of` v -> u !! n = Some i -> v !! n = Some i.
Proof. intros Hp Hu. exact (prefix_lookup_Some u v n i Hu Hp). Qed.

Lemma lb_Forall_drop {A} (P : A -> Prop) (n : nat) (l : list A) :
  Forall P l -> Forall P (drop n l).
Proof.
  intro HF. apply Forall_forall. intros x Hx.
  apply list_elem_of_lookup in Hx as [i Hi]. rewrite lookup_drop in Hi.
  exact (Forall_lookup_1 _ _ _ _ HF Hi).
Qed.

Lemma lb_lookup_total_drop {A} `{!Inhabited A} (n i : nat) (l : list A) :
  drop n l !!! i = l !!! (n + i).
Proof. by rewrite !list_lookup_total_alt lookup_drop. Qed.

Lemma lb_take_S {A} `{!Inhabited A} (n : nat) (l : list A) :
  (S n <= length l)%nat -> take (S n) l = l !!! 0%nat :: take n (drop 1 l).
Proof.
  destruct l as [| a l]; [cbn [length]; lia |].
  intros _. cbn [take drop]. by rewrite list_lookup_total_alt /=.
Qed.

Lemma lb_lta_take_eq {A} `{!Inhabited A} (l l' : list A) (q j : nat) :
  take q l' = take q l -> (j < q)%nat -> l' !!! j = l !!! j.
Proof.
  intros Heq Hj.
  assert (H1 : l' !! j = take q l' !! j)
    by (symmetry; rewrite lookup_take_lt; [done | lia]).
  assert (H2 : l !! j = take q l !! j)
    by (symmetry; rewrite lookup_take_lt; [done | lia]).
  by rewrite !list_lookup_total_alt H1 H2 Heq.
Qed.

Lemma lb_app4 {A} (a c s t : list A) (n : A) :
  ((a ++ n :: c) ++ s) ++ t = a ++ n :: (c ++ (s ++ t)).
Proof. by rewrite -!app_assoc. Qed.

(* comparable wires agree wherever both have a byte *)
Lemma lb_cmp_at {A} (l1 l2 : list A) (i : nat) (x y : A) :
  (l1 `prefix_of` l2 \/ l2 `prefix_of` l1) ->
  l1 !! i = Some x -> l2 !! i = Some y -> x = y.
Proof.
  intros [Hp | Hp] H1 H2.
  - rewrite (lb_prefix_lookup _ _ _ _ Hp H1) in H2. by injection H2.
  - rewrite (lb_prefix_lookup _ _ _ _ Hp H2) in H1. by injection H1.
Qed.

Lemma lb_prefix_eq {A} (u v : list A) :
  u `prefix_of` v -> (length v <= length u)%nat -> u = v.
Proof.
  intros [k ->] Hl. rewrite length_app in Hl.
  assert (Hk : k = []) by (destruct k; [reflexivity | cbn [length] in Hl; lia]).
  subst k. by rewrite app_nil_r.
Qed.

Lemma lb_nonl_lta (bs : list (list (bv 8))) (i : nat) :
  Forall (fun l => wl_nl ∉ l) bs -> (i < length bs)%nat -> wl_nl ∉ bs !!! i.
Proof.
  intros HF Hi. destruct (lookup_lt_is_Some_2 bs i Hi) as [l Hl].
  rewrite (list_lookup_total_correct bs i l Hl).
  exact (Forall_lookup_1 _ _ _ _ HF Hl).
Qed.

(* ====================================================================== *)
(*  1.  '$'-FREE BYTES, AND THE THREE LITERAL READINGS OF THE PANIC LINE   *)
(* ====================================================================== *)

Definition nodollar (b : bv 8) : Prop := bv_unsigned b <> 36%Z.

Global Instance nodollar_dec b : Decision (nodollar b).
Proof. rewrite /nodollar. apply _. Defined.

Lemma body_byte_nodollar b : wl_body_byte b -> nodollar b.
Proof.
  rewrite /wl_body_byte /wl_alnum /nodollar. intros [[H | [H | H]] | ->].
  - lia.
  - lia.
  - lia.
  - rewrite wl_sp_val. lia.
Qed.

Lemma nl_nodollar : nodollar wl_nl.
Proof. rewrite /nodollar wl_nl_val. lia. Qed.

Lemma lb_panic_len : length alt_panic = 5%nat.
Proof. by vm_compute. Qed.

Lemma lb_panic_nd : Forall nodollar alt_panic.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma lb_panic_nl4 : alt_panic !! 4%nat = Some wl_nl.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma lb_panic_split : alt_panic = sb "fork"%string ++ [wl_nl].
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma lb_fork_nonl : wl_nl ∉ sb "fork"%string.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ====================================================================== *)
(*  2.  THE PROMPT SETTLES THE COMPARISON                                  *)
(* ====================================================================== *)

(* the prompt's '$' sits exactly where the '$'-free run ends *)
Lemma lb_dollar_at (u Y : list (bv 8)) :
  (u ++ u_prompt ++ Y) !! (length u) = Some (Z_to_bv 8 36%Z).
Proof.
  rewrite lookup_app_r; [| lia]. rewrite Nat.sub_diag.
  rewrite lookup_app_l; [exact u_prompt_head | exact u_prompt_pos].
Qed.

(* THE SPLIT.  Two '$'-free runs, each closed by the prompt, below one
   wire: the runs are EQUAL, whatever alternatives produced them.  This is
   the whole of the comparison between two non-panic alternatives. *)
Lemma lb_dollar_split (u u' Y Y' : list (bv 8)) :
  Forall nodollar u -> Forall nodollar u' ->
  (u' ++ u_prompt ++ Y') `prefix_of` (u ++ u_prompt ++ Y) ->
  u' = u /\ Y' `prefix_of` Y.
Proof.
  intros Hu Hu' Hp.
  assert (Hcmp : (u' ++ u_prompt ++ Y') `prefix_of` (u ++ u_prompt ++ Y)
                 \/ (u ++ u_prompt ++ Y) `prefix_of` (u' ++ u_prompt ++ Y'))
    by (by left).
  assert (Hlen : length u' = length u).
  { destruct (Nat.lt_trichotomy (length u') (length u))
      as [Hlt | [Heq | Hgt]]; [| exact Heq |]; exfalso.
    - destruct (lookup_lt_is_Some_2 u (length u') Hlt) as [b Hb].
      assert (H2 : (u ++ u_prompt ++ Y) !! (length u') = Some b)
        by (rewrite lookup_app_l; [exact Hb | exact Hlt]).
      pose proof (lb_cmp_at _ _ _ _ _ Hcmp (lb_dollar_at u' Y') H2) as Heq.
      pose proof (Forall_lookup_1 _ _ _ _ Hu Hb) as Hnd.
      rewrite /nodollar -Heq in Hnd. apply Hnd. by vm_compute.
    - destruct (lookup_lt_is_Some_2 u' (length u) Hgt) as [b Hb].
      assert (H1 : (u' ++ u_prompt ++ Y') !! (length u) = Some b)
        by (rewrite lookup_app_l; [exact Hb | exact Hgt]).
      pose proof (lb_cmp_at _ _ _ _ _ Hcmp H1 (lb_dollar_at u Y)) as Heq.
      pose proof (Forall_lookup_1 _ _ _ _ Hu' Hb) as Hnd.
      rewrite /nodollar Heq in Hnd. apply Hnd. by vm_compute. }
  assert (Hu'u : u' = u).
  { assert (Hpu' : u' `prefix_of` (u ++ u_prompt ++ Y)).
    { etrans; [| exact Hp]. apply prefix_app_r. reflexivity. }
    assert (Hpu : u `prefix_of` (u ++ u_prompt ++ Y))
      by (apply prefix_app_r; reflexivity).
    destruct (prefix_weak_total _ _ _ Hpu' Hpu) as [H | H].
    - apply (lb_prefix_eq _ _ H). lia.
    - symmetry. apply (lb_prefix_eq _ _ H). lia. }
  split; [exact Hu'u |]. subst u'.
  apply wl_prefix_app_cancel in Hp. by apply wl_prefix_app_cancel in Hp.
Qed.

(* ...AND THE ONE COLLISION THE PROMPT DOES NOT SETTLE: an alternative
   whose own output IS sh's panic line, which the user can type
   ([echo fork > f] leaves the fork line in the file, and [cat f] prints it;
   [echo fork | cat] prints it too).  Below one wire with a panicking
   round it is forced to be exactly that line -- the '$' cannot fall
   inside the fork line, so the newline of the fork line falls inside the output,
   and two raw lines below one wire are one line. *)
Lemma lb_out_eq_panic (u Y Z : list (bv 8)) :
  Forall nodollar u ->
  (wl_nl ∉ u \/ exists v, wl_nl ∉ v /\ u = v ++ [wl_nl]) ->
  ((u ++ u_prompt ++ Y) `prefix_of` (alt_panic ++ Z)
   \/ (alt_panic ++ Z) `prefix_of` (u ++ u_prompt ++ Y)) ->
  u = alt_panic.
Proof.
  intros Hnd Hnl Hcmp.
  assert (H5 : (5 <= length u)%nat).
  { destruct (decide (length u < 5)%nat) as [Hlt | Hge]; [| lia]. exfalso.
    destruct (lookup_lt_is_Some_2 alt_panic (length u)
                ltac:(rewrite lb_panic_len; lia)) as [b Hb].
    assert (H2 : (alt_panic ++ Z) !! (length u) = Some b)
      by (rewrite lookup_app_l; [exact Hb | rewrite lb_panic_len; lia]).
    pose proof (lb_cmp_at _ _ _ _ _ Hcmp (lb_dollar_at u Y) H2) as Heq.
    pose proof (Forall_lookup_1 _ _ _ _ lb_panic_nd Hb) as Hb'.
    rewrite /nodollar -Heq in Hb'. apply Hb'. by vm_compute. }
  assert (Hnlin : wl_nl ∈ u).
  { destruct (lookup_lt_is_Some_2 u 4%nat ltac:(lia)) as [b Hb].
    assert (H1 : (u ++ u_prompt ++ Y) !! 4%nat = Some b)
      by (rewrite lookup_app_l; [exact Hb | lia]).
    assert (H2 : (alt_panic ++ Z) !! 4%nat = Some wl_nl)
      by (rewrite lookup_app_l;
          [exact lb_panic_nl4 | rewrite lb_panic_len; lia]).
    pose proof (lb_cmp_at _ _ _ _ _ Hcmp H1 H2) as Hb2.
    rewrite Hb2 in Hb. exact (list_elem_of_lookup_2 _ _ _ Hb). }
  destruct Hnl as [Hno | (v & Hv & Hu)]; [by destruct (Hno Hnlin) |].
  rewrite Hu lb_panic_split. f_equal.
  rewrite Hu lb_panic_split in Hcmp.
  rewrite -(app_assoc v [wl_nl] (u_prompt ++ Y))
          -(app_assoc (sb "fork"%string) [wl_nl] Z) in Hcmp.
  assert (Hc2 : (v ++ wl_nl :: (u_prompt ++ Y))
                  `prefix_of` (sb "fork"%string ++ wl_nl :: Z)
                \/ (sb "fork"%string ++ wl_nl :: Z)
                  `prefix_of` (v ++ wl_nl :: (u_prompt ++ Y)))
    by exact Hcmp.
  destruct Hc2 as [Hc2 | Hc2].
  - exact (proj1 (wl_raw_line_prefix_det v (sb "fork"%string) _ _
                    Hv lb_fork_nonl Hc2)).
  - symmetry.
    exact (proj1 (wl_raw_line_prefix_det (sb "fork"%string) v _ _
                    lb_fork_nonl Hv Hc2)).
Qed.

(* ...and an output opening on 'e' (the pipeline's exec diagnostics) is
   never below one wire with the panic line, which opens on 'f' *)
Lemma lb_head_ne_panic (u Y Z : list (bv 8)) :
  u !! 0%nat = Some (Z_to_bv 8 101%Z) ->
  ((u ++ u_prompt ++ Y) `prefix_of` (alt_panic ++ Z)
   \/ (alt_panic ++ Z) `prefix_of` (u ++ u_prompt ++ Y)) -> False.
Proof.
  intros Hhd Hcmp.
  assert (Hlu : (0 < length u)%nat)
    by (apply lookup_lt_Some in Hhd; lia).
  assert (H1 : (u ++ u_prompt ++ Y) !! 0%nat = Some (Z_to_bv 8 101%Z))
    by (rewrite lookup_app_l; [exact Hhd | exact Hlu]).
  assert (H2 : (alt_panic ++ Z) !! 0%nat = Some (Z_to_bv 8 102%Z))
    by (rewrite lookup_app_l;
        [exact alt_panic_head | rewrite lb_panic_len; lia]).
  pose proof (lb_cmp_at _ _ _ _ _ Hcmp H1 H2) as Heq.
  apply (f_equal bv_unsigned) in Heq. vm_compute in Heq. lia.
Qed.

(* a settled prologue whose first byte is '$' IS the bare prompt *)
Lemma lb_prompt_of_dollar (P : list nat) (X Y : list (bv 8)) :
  Forall (fun a => (a < length pro_alts)%nat) P -> pro_done P ->
  (u_prompt ++ Y) `prefix_of` (pro_of P ++ X) ->
  pro_of P = u_prompt.
Proof.
  intros HF Hd Hp.
  assert (Hne : P <> []) by (intros ->; by apply Exists_nil in Hd).
  pose proof (pro_of_pos P HF Hne) as Hpos.
  apply (pro_of_dollar_prompt P HF Hne). intros b Hb.
  assert (H1 : (u_prompt ++ Y) !! 0%nat = Some (Z_to_bv 8 36%Z))
    by (rewrite lookup_app_l; [exact u_prompt_head | exact u_prompt_pos]).
  assert (H2 : (pro_of P ++ X) !! 0%nat = Some (Z_to_bv 8 36%Z))
    by (eapply lb_prefix_lookup; [exact Hp | exact H1]).
  rewrite (lookup_app_l (pro_of P) X 0%nat Hpos) Hb in H2.
  injection H2 as H2. rewrite H2. by vm_compute.
Qed.

Lemma lb_prompt_of_dollar_r (P : list nat) (X Y : list (bv 8)) :
  Forall (fun a => (a < length pro_alts)%nat) P -> pro_done P ->
  (pro_of P ++ X) `prefix_of` (u_prompt ++ Y) ->
  pro_of P = u_prompt.
Proof.
  intros HF Hd Hp.
  assert (Hne : P <> []) by (intros ->; by apply Exists_nil in Hd).
  pose proof (pro_of_pos P HF Hne) as Hpos.
  apply (pro_of_dollar_prompt P HF Hne). intros b Hb.
  assert (H1 : (pro_of P ++ X) !! 0%nat = Some b)
    by (rewrite lookup_app_l; [exact Hb | exact Hpos]).
  assert (H2 : (u_prompt ++ Y) !! 0%nat = Some b)
    by (eapply lb_prefix_lookup; [exact Hp | exact H1]).
  rewrite (lookup_app_l u_prompt Y 0%nat u_prompt_pos) u_prompt_head in H2.
  injection H2 as H2. rewrite -H2. by vm_compute.
Qed.
