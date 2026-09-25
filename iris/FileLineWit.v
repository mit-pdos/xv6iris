(* ===================================================================== *)
(*  FileLineWit.v -- THE TYPED LINE'S WITNESS, PURELY                     *)
(*                                                                       *)
(*  A file's content is typed by the LEDGER's line list                   *)
(*  ([AppFile.fl_auth c (FileOut.efl_of h)]), and the only lower bound of  *)
(*  it a program ever sees is the one in an input byte's TAG              *)
(*  ([FileOut.ftag h]).  So the shell has to know that the [echo ... > f]  *)
(*  lines of the input IT read are among the lines of the history ITS     *)
(*  last byte is tagged with.  That is this file, and it is pure:         *)
(*                                                                       *)
(*    the consumed entries [E] are indexed ([EchoOutPure.E_index]: entry  *)
(*    [j]'s cycle history holds exactly [j + 1] inputs and ends in its     *)
(*    byte), chained ([ConsLog.hist_chain]) and of one boot, so the LAST   *)
(*    entry's cycle history reads back exactly the bytes of [E]           *)
(*    ([EchoOutPure.E_bytes_of_hist]); and that cycle is the last of the   *)
(*    history's cycles, so its lines are among [echof_lines_of h].         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
               SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import FileDisc.
Require Import EchoOut.           (* [seg_of] *)
From stdpp Require Import ssreflect.

(* a chain's histories are prefix-ordered by index *)
Lemma hist_chain_prefix (E : list (list mobs * bv 8)) (i j : nat)
    (x y : list mobs * bv 8) :
  hist_chain E -> (i <= j)%nat ->
  E !! i = Some x -> E !! j = Some y -> x.1 `prefix_of` y.1.
Proof using.
  intros Hch Hij Hx. revert y.
  induction Hij as [| j Hij IH]; intros y Hy.
  - rewrite Hx in Hy. injection Hy as <-. done.
  - destruct (lookup_lt_is_Some_2 E j
                ltac:(apply lookup_lt_Some in Hy; lia)) as [z Hz].
    destruct z as [hz cz]. destruct y as [hy cy].
    etrans; [ exact (IH _ Hz) | ].
    exact (proj1 (Hch j hz cz hy cy Hz Hy)).
Qed.

(* THE READ-BACK: the last consumed entry's cycle history holds exactly the
   consumed bytes *)
Lemma consumed_ins_last (k : nat) (E : list (list mobs * bv 8))
    (h : list mobs) (b : bv 8) :
  E_index (seg_of E) -> hist_chain E ->
  (forall x, x ∈ E -> obs_boots x.1 = k) ->
  last E = Some (h, b) ->
  trace_shape h true ->
  ins (open_seg h) = snd <$> E.
Proof using.
  intros Hidx Hch Hb Hlast Hsh.
  rewrite last_lookup in Hlast.
  assert (Hne : (0 < length E)%nat)
    by (apply lookup_lt_Some in Hlast; lia).
  set (n := length E) in *.
  assert (Hpre : forall j x, seg_of E !! j = Some x ->
                   x.1 `prefix_of` open_seg h).
  { intros j x Hx. rewrite /seg_of list_lookup_fmap fmap_Some in Hx.
    destruct Hx as (y & Hy & ->). cbn [fst].
    apply (open_seg_prefix_boots y.1 h).
    - exact (hist_chain_prefix E j (pred n) y (h, b) Hch
               ltac:(apply lookup_lt_Some in Hy; lia) Hy Hlast).
    - rewrite (Hb y (elem_of_list_lookup_2 _ _ _ Hy)).
      symmetry. exact (Hb (h, b) (elem_of_list_lookup_2 _ _ _ Hlast)).
    - exact Hsh. }
  pose proof (E_length_le_hist (seg_of E) (open_seg h) Hidx Hpre) as Hle.
  pose proof (E_bytes_of_hist (seg_of E) (open_seg h) Hidx Hpre Hle) as Hby.
  rewrite seg_of_snd seg_of_length in Hby.
  (* the last entry's own index law closes the length *)
  assert (Hl : seg_of E !! pred n = Some (open_seg h, b)).
  { rewrite /seg_of list_lookup_fmap Hlast. reflexivity. }
  destruct (Hidx (pred n) _ Hl) as [_ Hlen]. simpl in Hlen.
  rewrite Hby. rewrite take_ge; [ reflexivity | ]. unfold n in *. lia.
Qed.

(* ...AND THE WITNESS: the [echo ... > f] lines of the consumed input are
   lines of the history its last byte is tagged with *)
Lemma echof_lines_of_consumed (k : nat) (E : list (list mobs * bv 8))
    (h : list mobs) (b : bv 8) (w : list (bv 8) * list (list (bv 8))) :
  E_index (seg_of E) -> hist_chain E ->
  (forall x, x ∈ E -> obs_boots x.1 = k) ->
  last E = Some (h, b) ->
  trace_shape h true ->
  w ∈ echof_lines_in (snd <$> E) -> w ∈ echof_lines_of h.
Proof using.
  intros Hidx Hch Hb Hlast Hsh Hw.
  rewrite <- (consumed_ins_last k E h b Hidx Hch Hb Hlast Hsh) in Hw.
  destruct (cycles_of_io h [] Hsh (Forall_nil_2 _)) as (cs & Hcs & _).
  rewrite /echof_lines_of Hcs fmap_app concat_app.
  apply elem_of_app. right.
  cbn [fmap list_fmap concat]. rewrite app_nil_r. exact Hw.
Qed.
