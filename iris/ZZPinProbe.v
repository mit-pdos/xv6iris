(* PROBE: the two PURE lemmas the canon-pin design rests on, over TsoMemPa. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap list.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import TsoMemPa.

Local Open Scope Z_scope.

(* THE PIN'S TIE, one address: "from view [B] on, every agent's read of [a]
   lands in [S]".  This is the pure fact a per-address pin auth in
   [tso_interp_at] would carry. *)
Definition pin_ok (img : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (a : Arch.pa) (B : nat) (Sv : gset (bv 8)) : Prop :=
  forall (h : agent) (tv' : nat), (B <= tv')%nat ->
    exists b, tso_read img log h tv' a = Some b /\ b ∈ Sv.

(* ------------------------------------------------------------------ *)
(* (1) THE MINT.  Exactly A6.47's refuted [t ≤ B] tie -- TRUE as the
   pin's CREATION obligation, which is the point: it is false as a
   standing invariant, true at publication. *)
Lemma pin_ok_mint img log a B Sv t v :
  latest img log a t v -> (t <= B)%nat -> v ∈ Sv -> pin_ok img log a B Sv.
Proof.
  move => Hlat HtB Hv h tv' HB. exists v. split; [|exact Hv].
  apply (tso_read_of_latest _ _ _ _ _ t); [exact Hlat|].
  apply visibleb_below. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* the frame lemma the preservation step needs, and which TsoMemPa does
   NOT have: [read_down_app_below] asks [t ≤ tv], which a reader BELOW
   the append does not have. *)
Lemma read_down_app_frame img log m h tv a t :
  (t <= length log)%nat ->
  read_down img (log ++ [m]) h tv a t = read_down img log h tv a t.
Proof.
  elim: t => [|t IH] Hlen; first by rewrite !read_down_0.
  rewrite !read_down_S.
  have Hlk : (log ++ [m]) !! t = log !! t by apply lookup_app_l; lia.
  have Hvis : visibleb h tv (log ++ [m]) (S t) = visibleb h tv log (S t)
    by rewrite /visibleb Hlk.
  rewrite Hvis {1}/log_byte /= Hlk.
  case: (visibleb h tv log (S t)) => /=; last by apply IH; lia.
  case: (log !! t) => [m0|]; last by apply IH; lia.
  case: (msg_byte m0 a) => [b|] //. apply IH; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* (2) THE PRESERVATION.  The store gate's side condition is exactly
   "this message's byte at [a] is absent, or in [S]". *)
Lemma pin_ok_app img log m a B Sv :
  pin_ok img log a B Sv ->
  (msg_byte m a = None \/ exists b, msg_byte m a = Some b /\ b ∈ Sv) ->
  pin_ok img (log ++ [m]) a B Sv.
Proof.
  move => Hpin Hm h tv' HB.
  rewrite /tso_read length_app /= Nat.add_1_r read_down_S.
  rewrite log_byte_top.
  case Hv : (visibleb h tv' (log ++ [m]) (S (length log))) => /=.
  - case: Hm => [-> | [b [-> Hb]]].
    + rewrite read_down_app_frame //.
      have [b [Hr Hb]] := Hpin h tv' HB. by exists b.
    + by exists b.
  - rewrite read_down_app_frame //.
    have [b [Hr Hb]] := Hpin h tv' HB. by exists b.
Qed.

(* ------------------------------------------------------------------ *)
(* (3) THE FRAME AT AN UNPINNED ADDRESS is the [msg_byte = None] arm of
   (2), so an append that misses [a] is free -- no premise at all. *)
Lemma pin_ok_app_frame img log m a B Sv :
  pin_ok img log a B Sv -> msg_byte m a = None ->
  pin_ok img (log ++ [m]) a B Sv.
Proof. move => Hpin Hm. apply pin_ok_app; [done|by left]. Qed.
