(* DirView.v -- the RECORD VIEW of a directory's data blocks.

   Layer 3 of the fs-namei campaign (claude-notes/projects/fs-namei.md).
   dirlookup and dirlink both walk a directory's file bytes SIXTEEN AT A
   TIME, through readi/writei's contracts, and both speak about the k-th
   16-byte record.  This file is the pure vocabulary for that: the k-th
   record's inum halfword and name bytes read straight off
   [InodeInv.file_byte], the "is it live" and "does it match" predicates,
   and the FIRST-index searches the two loops implement.

   ---- WHY IT IS A SEPARATE FILE ---------------------------------------

   [DirentEnc.v] (N1) is the byte vocabulary of a dirent RECORD -- an
   abstract [dirent] and its 16 bytes.  It is a pure leaf and is frozen.
   What the two proofs actually hold is not a [dirent] but readi's
   delivered bytes, i.e. [file_byte data] at an offset; the bridge between
   the two lives here, which is why this file imports InodeInv (for
   [file_byte]) and therefore, transitively, the iris proofmode.

   FLAG: a LOCAL copy of [file_byte] was rejected.  readi's and writei's
   postconditions are stated on InodeInv's one, and a second definition
   would only be CONVERTIBLE to it, forcing a bridge at every use.
   Importing InodeInv costs this file nothing except the import time --
   note in particular that ssreflect is NOT in scope here (nothing in
   InodeInv's cone exports it), so every rewrite below is the vanilla one:
   no [rewrite a b c], no [rewrite !lem].

   ---- THE FIRST-INDEX SEARCH ------------------------------------------

   Both loops are "scan records 0,1,2,... and stop at the first one that
   ...":  dirlookup stops at the first record whose name matches, dirlink
   at the first FREE record (and falls off the end at [nrec], which is
   where it appends).  That is one function, [dfirst], over a BOOLEAN
   predicate -- boolean rather than a decidable Prop so that the
   extensionality law dirlink's write-back needs ([dfirst_ext]) is an
   ordinary equation with no instance juggling.

   The three loop-facing laws are [dfirst_step_false] / [dfirst_step_true]
   (the invariant "nothing below i matches" steps by one record) and
   [dfirst_mono] (having found at i, the answer at [nrec] is the same). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.Values.
Require Import RiscvModelBytes.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import InodeDefs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  0.  THE GENERIC FIRST-INDEX SEARCH                                     *)
(* ====================================================================== *)

(* [dfirst p n] = the LEAST [k < n] with [p k = true], if there is one. *)
Fixpoint dfirst (p : nat -> bool) (n : nat) : option nat :=
  match n with
  | O => None
  | S n' => match dfirst p n' with
            | Some k => Some k
            | None => if p n' then Some n' else None
            end
  end.

Lemma dfirst_0 (p : nat -> bool) : dfirst p 0 = None.
Proof. reflexivity. Qed.

Lemma dfirst_S (p : nat -> bool) (n : nat) :
  dfirst p (S n) = match dfirst p n with
                   | Some k => Some k
                   | None => if p n then Some n else None
                   end.
Proof. reflexivity. Qed.

Lemma dfirst_None_1 (p : nat -> bool) (n : nat) :
  dfirst p n = None -> forall j, (j < n)%nat -> p j = false.
Proof.
  induction n as [|n IH]; intros Hn j Hj; [exfalso; lia|].
  rewrite dfirst_S in Hn.
  destruct (dfirst p n) as [k|] eqn:E; [discriminate|].
  destruct (p n) eqn:Ep; [discriminate|].
  destruct (Nat.eq_dec j n) as [Hjn|Hjn].
  - rewrite Hjn. exact Ep.
  - assert (Hj' : (j < n)%nat) by lia. exact (IH eq_refl j Hj').
Qed.

Lemma dfirst_None_2 (p : nat -> bool) (n : nat) :
  (forall j, (j < n)%nat -> p j = false) -> dfirst p n = None.
Proof.
  induction n as [|n IH]; intros H; [reflexivity|].
  rewrite dfirst_S.
  assert (Hn : dfirst p n = None).
  { apply IH. intros j Hj. apply H. lia. }
  rewrite Hn.
  assert (Hpn : p n = false). { apply H. lia. }
  rewrite Hpn. reflexivity.
Qed.

Lemma dfirst_Some_1 (p : nat -> bool) (n k : nat) :
  dfirst p n = Some k ->
  (k < n)%nat /\ p k = true /\ (forall j, (j < k)%nat -> p j = false).
Proof.
  induction n as [|n IH]; intros Hn; [discriminate|].
  rewrite dfirst_S in Hn.
  destruct (dfirst p n) as [k'|] eqn:E.
  - assert (Hk : k' = k) by congruence. subst k'.
    destruct (IH eq_refl) as (H1 & H2 & H3).
    split; [lia | split; [exact H2 | exact H3]].
  - destruct (p n) eqn:Ep; [| discriminate].
    assert (Hk : n = k) by congruence. subst n.
    split; [lia | split; [exact Ep | exact (dfirst_None_1 p k E)]].
Qed.

Lemma dfirst_Some_2 (p : nat -> bool) (n k : nat) :
  (k < n)%nat -> p k = true -> (forall j, (j < k)%nat -> p j = false) ->
  dfirst p n = Some k.
Proof.
  induction n as [|n IH]; intros Hk Hpk Hlt; [exfalso; lia|].
  rewrite dfirst_S.
  destruct (Nat.eq_dec k n) as [Hkn|Hkn].
  - assert (Hn : dfirst p n = None).
    { apply dfirst_None_2. rewrite <- Hkn. exact Hlt. }
    rewrite Hn. rewrite <- Hkn. rewrite Hpk. reflexivity.
  - assert (Hkn' : (k < n)%nat) by lia.
    rewrite (IH Hkn' Hpk Hlt). reflexivity.
Qed.

Lemma dfirst_lt (p : nat -> bool) (n k : nat) :
  dfirst p n = Some k -> (k < n)%nat.
Proof. intros H. destruct (dfirst_Some_1 p n k H) as (H1 & _ & _). exact H1. Qed.

Lemma dfirst_true (p : nat -> bool) (n k : nat) :
  dfirst p n = Some k -> p k = true.
Proof. intros H. destruct (dfirst_Some_1 p n k H) as (_ & H2 & _). exact H2. Qed.

Lemma dfirst_before (p : nat -> bool) (n k : nat) :
  dfirst p n = Some k -> forall j, (j < k)%nat -> p j = false.
Proof. intros H. destruct (dfirst_Some_1 p n k H) as (_ & _ & H3). exact H3. Qed.

Lemma dfirst_mono (p : nat -> bool) (n m k : nat) :
  (n <= m)%nat -> dfirst p n = Some k -> dfirst p m = Some k.
Proof.
  intros Hnm H. destruct (dfirst_Some_1 p n k H) as (H1 & H2 & H3).
  apply dfirst_Some_2; [lia | exact H2 | exact H3].
Qed.

(* the two loop-invariant steps: one record is scanned *)
Lemma dfirst_step_false (p : nat -> bool) (n : nat) :
  dfirst p n = None -> p n = false -> dfirst p (S n) = None.
Proof.
  intros Hn Hp. rewrite dfirst_S. rewrite Hn. rewrite Hp. reflexivity.
Qed.

Lemma dfirst_step_true (p : nat -> bool) (n : nat) :
  dfirst p n = None -> p n = true -> dfirst p (S n) = Some n.
Proof.
  intros Hn Hp. rewrite dfirst_S. rewrite Hn. rewrite Hp. reflexivity.
Qed.

(* what dirlink's write-back needs: only the scanned prefix matters *)
Lemma dfirst_ext (p q : nat -> bool) (n : nat) :
  (forall j, (j < n)%nat -> p j = q j) -> dfirst p n = dfirst q n.
Proof.
  induction n as [|n IH]; intros H; [reflexivity|].
  rewrite (dfirst_S p n). rewrite (dfirst_S q n).
  assert (Hpq : dfirst p n = dfirst q n).
  { apply IH. intros j Hj. apply H. lia. }
  rewrite Hpq.
  assert (Hn : p n = q n). { apply H. lia. }
  rewrite Hn. reflexivity.
Qed.

(* ====================================================================== *)
(*  1.  A NAME-VIEW EXTENSIONALITY LAW DirentEnc DOES NOT STATE            *)
(* ====================================================================== *)

Lemma bname_ext (n : nat) (f g : nat -> bv 8) :
  (forall j, (j < n)%nat -> f j = g j) -> bname n f = bname n g.
Proof. intros H. unfold bname. rewrite (bview_ext n f g H). reflexivity. Qed.

(* ====================================================================== *)
(*  2.  THE RECORD VIEW                                                    *)
(* ====================================================================== *)

(* The k-th record's inum halfword, assembled little-endian out of the two
   bytes at file offsets [16k] and [16k+1] -- which is what dirlookup's
   [lhu a5,-96(s0)] reads once readi has delivered the record.  Stated
   through [RiscvModelBytes.assemble_bytes] so that
   [nth_byte_assemble_len] gives the two byte readings, and hence so that
   [DirentEnc.dirent_bytes_inum] connects it to an ENCODED record
   ([dir_record_inum] below). *)
Definition dir_inum (data : nat -> list (bv 8)) (k : nat) : bv 16 :=
  Z_to_bv (16%N) (assemble_bytes [file_byte data (16 * k)%nat;
                                  file_byte data (16 * k + 1)%nat]).

(* The k-th record's name bytes, as a naming FUNCTION -- namecmp's [g], and
   [DirentEnc.bname 14] of it is its canonical C string. *)
Definition dir_name (data : nat -> list (bv 8)) (k : nat) : nat -> bv 8 :=
  fun j => file_byte data (16 * k + 2 + j)%nat.

(* the FREE test the [lhu]/[beqz] pair performs, and its negation *)
Definition dir_freeb (data : nat -> list (bv 8)) (k : nat) : bool :=
  bool_decide (dir_inum data k = bv_0 16).

Definition dir_live (data : nat -> list (bv 8)) (k : nat) : Prop :=
  dir_inum data k <> bv_0 16.

Definition dir_liveb (data : nat -> list (bv 8)) (k : nat) : bool :=
  negb (dir_freeb data k).

(* the full hit test: live AND the canonical name is [s] *)
Definition dir_matchb (data : nat -> list (bv 8)) (k : nat)
    (s : list (bv 8)) : bool :=
  andb (dir_liveb data k) (bool_decide (bname 14 (dir_name data k) = s)).

Definition dir_match (data : nat -> list (bv 8)) (k : nat)
    (s : list (bv 8)) : Prop :=
  dir_live data k /\ bname 14 (dir_name data k) = s.

(* ---- the boolean/Prop bridges ---------------------------------------- *)

Lemma dir_freeb_true (data : nat -> list (bv 8)) (k : nat) :
  dir_freeb data k = true <-> dir_inum data k = bv_0 16.
Proof. unfold dir_freeb. apply bool_decide_eq_true. Qed.

Lemma dir_freeb_false (data : nat -> list (bv 8)) (k : nat) :
  dir_freeb data k = false <-> dir_live data k.
Proof. unfold dir_freeb, dir_live. apply bool_decide_eq_false. Qed.

Lemma dir_liveb_true (data : nat -> list (bv 8)) (k : nat) :
  dir_liveb data k = true <-> dir_live data k.
Proof.
  unfold dir_liveb. split.
  - intros H. apply dir_freeb_false. apply negb_true_iff. exact H.
  - intros H. apply negb_true_iff. apply dir_freeb_false. exact H.
Qed.

Lemma dir_liveb_false (data : nat -> list (bv 8)) (k : nat) :
  dir_liveb data k = false <-> dir_inum data k = bv_0 16.
Proof.
  unfold dir_liveb. split.
  - intros H. apply dir_freeb_true. apply negb_false_iff. exact H.
  - intros H. apply negb_false_iff. apply dir_freeb_true. exact H.
Qed.

Lemma dir_matchb_true (data : nat -> list (bv 8)) (k : nat)
    (s : list (bv 8)) :
  dir_matchb data k s = true <-> dir_match data k s.
Proof.
  unfold dir_matchb, dir_match. split.
  - intros H. apply andb_true_iff in H. destruct H as [H1 H2]. split.
    + apply dir_liveb_true. exact H1.
    + exact (proj1 (bool_decide_eq_true _) H2).
  - intros [H1 H2]. apply andb_true_iff. split.
    + apply dir_liveb_true. exact H1.
    + exact (proj2 (bool_decide_eq_true _) H2).
Qed.

Lemma dir_matchb_false (data : nat -> list (bv 8)) (k : nat)
    (s : list (bv 8)) :
  dir_matchb data k s = false <-> ~ dir_match data k s.
Proof.
  split.
  - intros H Hm. apply dir_matchb_true in Hm. congruence.
  - intros H. destruct (dir_matchb data k s) eqn:E; [| reflexivity].
    exfalso. apply H. apply dir_matchb_true. exact E.
Qed.

(* ====================================================================== *)
(*  3.  THE TWO SEARCHES                                                   *)
(* ====================================================================== *)

(* dirlookup's answer: the least record below [nrec] whose name is [s]. *)
Definition dir_first (data : nat -> list (bv 8)) (nrec : nat)
    (s : list (bv 8)) : option nat :=
  dfirst (fun k => dir_matchb data k s) nrec.

(* dirlink's free-slot scan, and the slot it settles on: the first free
   record, or [nrec] itself when every record is live (which is where the
   loop's own [off] lands when it falls off the end). *)
Definition dir_free_first (data : nat -> list (bv 8)) (nrec : nat)
  : option nat := dfirst (dir_freeb data) nrec.

Definition dir_slot (data : nat -> list (bv 8)) (nrec : nat) : nat :=
  match dir_free_first data nrec with
  | Some k => k
  | None => nrec
  end.

(* ---- dir_first's characterisation ------------------------------------ *)

Lemma dir_first_Some (data : nat -> list (bv 8)) (nrec k : nat)
    (s : list (bv 8)) :
  dir_first data nrec s = Some k <->
  ((k < nrec)%nat /\ dir_match data k s
   /\ forall j, (j < k)%nat -> ~ dir_match data j s).
Proof.
  unfold dir_first. split.
  - intros H. destruct (dfirst_Some_1 _ _ _ H) as (H1 & H2 & H3).
    split; [exact H1 | split].
    + apply dir_matchb_true. exact H2.
    + intros j Hj. apply dir_matchb_false. exact (H3 j Hj).
  - intros (H1 & H2 & H3). apply dfirst_Some_2; [exact H1 | | ].
    + apply dir_matchb_true. exact H2.
    + intros j Hj. apply dir_matchb_false. exact (H3 j Hj).
Qed.

Lemma dir_first_None (data : nat -> list (bv 8)) (nrec : nat)
    (s : list (bv 8)) :
  dir_first data nrec s = None <->
  (forall j, (j < nrec)%nat -> ~ dir_match data j s).
Proof.
  unfold dir_first. split.
  - intros H j Hj. apply dir_matchb_false. exact (dfirst_None_1 _ _ H j Hj).
  - intros H. apply dfirst_None_2. intros j Hj.
    apply dir_matchb_false. exact (H j Hj).
Qed.

(* the two facts a caller reads off a hit *)
Lemma dir_first_live (data : nat -> list (bv 8)) (nrec k : nat)
    (s : list (bv 8)) :
  dir_first data nrec s = Some k -> dir_live data k.
Proof.
  intros H. apply dir_first_Some in H. destruct H as (_ & [Hl _] & _). exact Hl.
Qed.

Lemma dir_first_name (data : nat -> list (bv 8)) (nrec k : nat)
    (s : list (bv 8)) :
  dir_first data nrec s = Some k -> bname 14 (dir_name data k) = s.
Proof.
  intros H. apply dir_first_Some in H. destruct H as (_ & [_ Hn] & _). exact Hn.
Qed.

Lemma dir_first_lt (data : nat -> list (bv 8)) (nrec k : nat)
    (s : list (bv 8)) :
  dir_first data nrec s = Some k -> (k < nrec)%nat.
Proof.
  intros H. apply dir_first_Some in H. destruct H as (H1 & _ & _). exact H1.
Qed.

(* the loop steps *)
Lemma dir_first_step_miss (data : nat -> list (bv 8)) (i : nat)
    (s : list (bv 8)) :
  dir_first data i s = None -> ~ dir_match data i s ->
  dir_first data (S i) s = None.
Proof.
  intros H Hm. unfold dir_first. apply dfirst_step_false; [exact H|].
  apply dir_matchb_false. exact Hm.
Qed.

Lemma dir_first_step_hit (data : nat -> list (bv 8)) (i : nat)
    (s : list (bv 8)) :
  dir_first data i s = None -> dir_match data i s ->
  dir_first data (S i) s = Some i.
Proof.
  intros H Hm. unfold dir_first. apply dfirst_step_true; [exact H|].
  apply dir_matchb_true. exact Hm.
Qed.

Lemma dir_first_mono (data : nat -> list (bv 8)) (n m k : nat)
    (s : list (bv 8)) :
  (n <= m)%nat -> dir_first data n s = Some k -> dir_first data m s = Some k.
Proof. unfold dir_first. apply dfirst_mono. Qed.

(* ---- the first-FREE twin --------------------------------------------- *)

Lemma dir_free_first_None (data : nat -> list (bv 8)) (nrec : nat) :
  dir_free_first data nrec = None <->
  (forall j, (j < nrec)%nat -> dir_live data j).
Proof.
  unfold dir_free_first. split.
  - intros H j Hj. apply dir_freeb_false. exact (dfirst_None_1 _ _ H j Hj).
  - intros H. apply dfirst_None_2. intros j Hj.
    apply dir_freeb_false. exact (H j Hj).
Qed.

Lemma dir_free_first_Some (data : nat -> list (bv 8)) (nrec k : nat) :
  dir_free_first data nrec = Some k <->
  ((k < nrec)%nat /\ dir_inum data k = bv_0 16
   /\ forall j, (j < k)%nat -> dir_live data j).
Proof.
  unfold dir_free_first. split.
  - intros H. destruct (dfirst_Some_1 _ _ _ H) as (H1 & H2 & H3).
    split; [exact H1 | split].
    + apply dir_freeb_true. exact H2.
    + intros j Hj. apply dir_freeb_false. exact (H3 j Hj).
  - intros (H1 & H2 & H3). apply dfirst_Some_2; [exact H1 | | ].
    + apply dir_freeb_true. exact H2.
    + intros j Hj. apply dir_freeb_false. exact (H3 j Hj).
Qed.

Lemma dir_free_first_step_live (data : nat -> list (bv 8)) (i : nat) :
  dir_free_first data i = None -> dir_live data i ->
  dir_free_first data (S i) = None.
Proof.
  intros H Hl. unfold dir_free_first. apply dfirst_step_false; [exact H|].
  apply dir_freeb_false. exact Hl.
Qed.

Lemma dir_free_first_step_free (data : nat -> list (bv 8)) (i : nat) :
  dir_free_first data i = None -> dir_inum data i = bv_0 16 ->
  dir_free_first data (S i) = Some i.
Proof.
  intros H Hf. unfold dir_free_first. apply dfirst_step_true; [exact H|].
  apply dir_freeb_true. exact Hf.
Qed.

Lemma dir_free_first_mono (data : nat -> list (bv 8)) (n m k : nat) :
  (n <= m)%nat -> dir_free_first data n = Some k ->
  dir_free_first data m = Some k.
Proof. unfold dir_free_first. apply dfirst_mono. Qed.

(* ---- [dir_slot]: what dirlink's [s1] holds when the scan stops -------- *)

Lemma dir_slot_le (data : nat -> list (bv 8)) (nrec : nat) :
  (dir_slot data nrec <= nrec)%nat.
Proof.
  unfold dir_slot. destruct (dir_free_first data nrec) as [k|] eqn:E; [| lia].
  assert (Hk : (k < nrec)%nat).
  { apply dir_free_first_Some in E. destruct E as (H & _ & _). exact H. }
  lia.
Qed.

Lemma dir_slot_free (data : nat -> list (bv 8)) (nrec : nat) :
  (dir_slot data nrec < nrec)%nat ->
  dir_inum data (dir_slot data nrec) = bv_0 16.
Proof.
  unfold dir_slot. destruct (dir_free_first data nrec) as [k|] eqn:E.
  - intros _. apply dir_free_first_Some in E.
    destruct E as (_ & H & _). exact H.
  - intros H. exfalso. lia.
Qed.

Lemma dir_slot_live_below (data : nat -> list (bv 8)) (nrec : nat) :
  forall j, (j < dir_slot data nrec)%nat -> dir_live data j.
Proof.
  unfold dir_slot. destruct (dir_free_first data nrec) as [k|] eqn:E.
  - destruct (proj1 (dir_free_first_Some data nrec k) E) as (_ & _ & H).
    exact H.
  - intros j Hj. exact (proj1 (dir_free_first_None data nrec) E j Hj).
Qed.

(* the shape the WP loop leaves: the scan stopped at [i], everything below
   was live, and either [i = nrec] or record [i] is free *)
Lemma dir_slot_char (data : nat -> list (bv 8)) (nrec i : nat) :
  (i <= nrec)%nat ->
  (forall j, (j < i)%nat -> dir_live data j) ->
  (i = nrec \/ dir_inum data i = bv_0 16) ->
  dir_slot data nrec = i.
Proof.
  intros Hle Hlive Hstop. unfold dir_slot.
  destruct (Nat.eq_dec i nrec) as [Hin|Hin].
  - assert (E : dir_free_first data nrec = None).
    { apply (proj2 (dir_free_first_None data nrec)).
      rewrite <- Hin. exact Hlive. }
    rewrite E. exact (eq_sym Hin).
  - assert (Hfree : dir_inum data i = bv_0 16).
    { destruct Hstop as [H|H]; [exfalso; exact (Hin H) | exact H]. }
    assert (E : dir_free_first data nrec = Some i).
    { apply (proj2 (dir_free_first_Some data nrec i)).
      split; [lia | split; [exact Hfree | exact Hlive]]. }
    rewrite E. reflexivity.
Qed.

(* ====================================================================== *)
(*  4.  READING AN ENCODED RECORD OUT OF THE BYTES                         *)
(* ====================================================================== *)

(* the two byte readings of [dir_inum] -- the whole reason it is spelled
   through [assemble_bytes] *)
Lemma dir_inum_byte0 (data : nat -> list (bv 8)) (k : nat) :
  nth_byte (dir_inum data k) 0%nat = file_byte data (16 * k)%nat.
Proof.
  unfold dir_inum.
  rewrite (nth_byte_assemble_len (16%N)
             [file_byte data (16 * k)%nat; file_byte data (16 * k + 1)%nat]
             0%nat).
  - reflexivity.
  - simpl. lia.
  - simpl. lia.
Qed.

Lemma dir_inum_byte1 (data : nat -> list (bv 8)) (k : nat) :
  nth_byte (dir_inum data k) 1%nat = file_byte data (16 * k + 1)%nat.
Proof.
  unfold dir_inum.
  rewrite (nth_byte_assemble_len (16%N)
             [file_byte data (16 * k)%nat; file_byte data (16 * k + 1)%nat]
             1%nat).
  - reflexivity.
  - simpl. lia.
  - simpl. lia.
Qed.

Lemma dir_inum_half_bytes (data : nat -> list (bv 8)) (k : nat) :
  half_bytes (dir_inum data k)
  = [file_byte data (16 * k)%nat; file_byte data (16 * k + 1)%nat].
Proof.
  unfold half_bytes. rewrite dir_inum_byte0. rewrite dir_inum_byte1.
  reflexivity.
Qed.

(* THE BRIDGE TO DirentEnc: a window that holds an encoded record has that
   record's inum and that record's canonical name. *)
Lemma dir_record_inum (data : nat -> list (bv 8)) (k : nat) (d : dirent) :
  dirent_wf d ->
  (forall j, (j < 16)%nat -> file_byte data (16 * k + j)%nat
                             = dirent_bytes d !!! j) ->
  dir_inum data k = de_inum d.
Proof.
  intros Hwf Hb.
  assert (Hb0 : file_byte data (16 * k + 0)%nat = dirent_bytes d !!! 0%nat).
  { apply Hb. lia. }
  assert (Hb1 : file_byte data (16 * k + 1)%nat = dirent_bytes d !!! 1%nat).
  { apply Hb. lia. }
  assert (E0 : (16 * k + 0)%nat = (16 * k)%nat) by lia.
  rewrite E0 in Hb0.
  assert (Hd0 : dirent_bytes d !!! 0%nat = nth_byte (de_inum d) 0%nat).
  { apply dirent_bytes_inum_t. lia. }
  assert (Hd1 : dirent_bytes d !!! 1%nat = nth_byte (de_inum d) 1%nat).
  { apply dirent_bytes_inum_t. lia. }
  apply de_half_bytes_inj.
  rewrite dir_inum_half_bytes. unfold half_bytes.
  rewrite Hb0. rewrite Hb1. rewrite Hd0. rewrite Hd1. reflexivity.
Qed.

Lemma dir_record_name (data : nat -> list (bv 8)) (k : nat) (d : dirent) :
  dirent_wf d ->
  (forall j, (j < 16)%nat -> file_byte data (16 * k + j)%nat
                             = dirent_bytes d !!! j) ->
  bname 14 (dir_name data k) = de_name_str d.
Proof.
  intros Hwf Hb.
  rewrite <- (de_bname_name d Hwf). apply bname_ext. intros j Hj.
  unfold dir_name.
  assert (E : (16 * k + 2 + j)%nat = (16 * k + (2 + j))%nat) by lia.
  rewrite E.
  assert (Hbj : file_byte data (16 * k + (2 + j))%nat
                = dirent_bytes d !!! (2 + j)%nat).
  { apply Hb. lia. }
  rewrite Hbj. apply dirent_bytes_name_t.
Qed.

(* dirlink's own record, at the level its postcondition speaks: the window
   holds [de_of_name i s], so the slot is live at [i] and its canonical name
   is [s]. *)
Lemma dir_record_of_name (data : nat -> list (bv 8)) (k : nat)
    (i : bv 16) (s : list (bv 8)) :
  (length s <= 14)%nat -> nonul s ->
  (forall j, (j < 16)%nat -> file_byte data (16 * k + j)%nat
                             = dirent_bytes (de_of_name i s) !!! j) ->
  dir_inum data k = i /\ bname 14 (dir_name data k) = s.
Proof.
  intros Hlen Hs Hb. split.
  - rewrite (dir_record_inum data k (de_of_name i s) (de_of_name_wf i s) Hb).
    reflexivity.
  - rewrite (dir_record_name data k (de_of_name i s) (de_of_name_wf i s) Hb).
    apply de_of_name_str; assumption.
Qed.

(* ====================================================================== *)
(*  5.  STABILITY UNDER A DATA UPDATE OUTSIDE THE WINDOW                   *)
(* ====================================================================== *)

(* [data'] agrees with [data] on record [k]'s sixteen bytes *)
Definition dir_win_agree (data data' : nat -> list (bv 8)) (k : nat) : Prop :=
  forall j, (j < 16)%nat ->
    file_byte data' (16 * k + j)%nat = file_byte data (16 * k + j)%nat.

Lemma dir_win_agree_below (data data' : nat -> list (bv 8)) (n k : nat) :
  (forall j, (j < 16 * n)%nat -> file_byte data' j = file_byte data j) ->
  (k < n)%nat -> dir_win_agree data data' k.
Proof. intros H Hk j Hj. apply H. lia. Qed.

Lemma dir_inum_agree (data data' : nat -> list (bv 8)) (k : nat) :
  dir_win_agree data data' k -> dir_inum data' k = dir_inum data k.
Proof.
  intros H. unfold dir_inum.
  assert (H0' : file_byte data' (16 * k + 0)%nat
                = file_byte data (16 * k + 0)%nat).
  { apply H. lia. }
  assert (E0 : (16 * k + 0)%nat = (16 * k)%nat) by lia.
  rewrite E0 in H0'.
  assert (H1' : file_byte data' (16 * k + 1)%nat
                = file_byte data (16 * k + 1)%nat).
  { apply H. lia. }
  rewrite H0'. rewrite H1'. reflexivity.
Qed.

Lemma dir_bname_agree (data data' : nat -> list (bv 8)) (k : nat) :
  dir_win_agree data data' k ->
  bname 14 (dir_name data' k) = bname 14 (dir_name data k).
Proof.
  intros H. apply bname_ext. intros j Hj. unfold dir_name.
  assert (E : (16 * k + 2 + j)%nat = (16 * k + (2 + j))%nat) by lia.
  rewrite E. apply H. lia.
Qed.

Lemma dir_freeb_agree (data data' : nat -> list (bv 8)) (k : nat) :
  dir_win_agree data data' k -> dir_freeb data' k = dir_freeb data k.
Proof.
  intros H. unfold dir_freeb. rewrite (dir_inum_agree data data' k H).
  reflexivity.
Qed.

Lemma dir_liveb_agree (data data' : nat -> list (bv 8)) (k : nat) :
  dir_win_agree data data' k -> dir_liveb data' k = dir_liveb data k.
Proof.
  intros H. unfold dir_liveb. rewrite (dir_freeb_agree data data' k H).
  reflexivity.
Qed.

Lemma dir_matchb_agree (data data' : nat -> list (bv 8)) (k : nat)
    (s : list (bv 8)) :
  dir_win_agree data data' k -> dir_matchb data' k s = dir_matchb data k s.
Proof.
  intros H. unfold dir_matchb.
  rewrite (dir_liveb_agree data data' k H).
  rewrite (dir_bname_agree data data' k H). reflexivity.
Qed.

Lemma dir_first_agree (data data' : nat -> list (bv 8)) (n : nat)
    (s : list (bv 8)) :
  (forall k, (k < n)%nat -> dir_win_agree data data' k) ->
  dir_first data' n s = dir_first data n s.
Proof.
  intros H. unfold dir_first. apply dfirst_ext. intros j Hj.
  apply dir_matchb_agree. exact (H j Hj).
Qed.

Lemma dir_free_first_agree (data data' : nat -> list (bv 8)) (n : nat) :
  (forall k, (k < n)%nat -> dir_win_agree data data' k) ->
  dir_free_first data' n = dir_free_first data n.
Proof.
  intros H. unfold dir_free_first. apply dfirst_ext. intros j Hj.
  apply dir_freeb_agree. exact (H j Hj).
Qed.

Lemma dir_slot_agree (data data' : nat -> list (bv 8)) (n : nat) :
  (forall k, (k < n)%nat -> dir_win_agree data data' k) ->
  dir_slot data' n = dir_slot data n.
Proof.
  intros H. unfold dir_slot. rewrite (dir_free_first_agree data data' n H).
  reflexivity.
Qed.

(* ====================================================================== *)
(*  6.  WHAT strncpy LEAVES IN dirlink'S RECORD                            *)
(* ====================================================================== *)

(* [SpecStrncpy.snc_post] TRANSCRIBED, with [ByteBuf.bb_nonul] /
   [ByteBuf.bb_cstr] unfolded and NUL spelled DirentEnc's way (the two
   spellings are the same term).  SpecStrncpy is another function's Spec
   file and must not be a dependency of this one -- the same reason
   [DirentEnc.nc_stop] / [nc_run] transcribe SpecStrncmp's arms.  The
   bridge at the call site is then [exact (fun H => H)]. *)
Definition dl_nonul (f : nat -> bv 8) (d : nat) : Prop :=
  forall j, (j < d)%nat -> f j <> NUL.

Definition dl_cstr (f : nat -> bv 8) (k : nat) : Prop :=
  dl_nonul f k /\ f k = NUL.

Definition dl_snc (f h : nat -> bv 8) (n : nat) : Prop :=
  (dl_nonul f n /\ forall j, (j < n)%nat -> h j = f j)
  \/ exists k, (k < n)%nat /\ dl_cstr f k
       /\ (forall j, (j < k)%nat -> h j = f j)
       /\ (forall j, (k <= j)%nat -> (j < n)%nat -> h j = NUL).

(* both of strncpy's arms leave a buffer whose canonical prefix is [kk]
   bytes of [f] and whose tail to 14 is NUL; that is exactly [name_pad] of
   the source's canonical name, i.e. [DirentEnc.de_padded]. *)
Lemma snc_bview_aux (f h : nat -> bv 8) (kk : nat) :
  (kk <= 14)%nat ->
  (forall j, (j < kk)%nat -> f j <> NUL) ->
  (kk = 14%nat \/ f kk = NUL) ->
  (forall j, (j < kk)%nat -> h j = f j) ->
  (forall j, (kk <= j)%nat -> (j < 14)%nat -> h j = NUL) ->
  bview 14 h = name_pad (bname 14 f) /\ bname 14 h = bname 14 f.
Proof.
  intros Hkk Hne Hstop Hhf Hhn.
  assert (Hbf : bname 14 f = bview kk f)
    by (apply bname_char; assumption).
  assert (Hbh : bname 14 h = bview kk h).
  { apply bname_char; [exact Hkk | | ].
    - intros x Hx. rewrite (Hhf x Hx). exact (Hne x Hx).
    - destruct (Nat.eq_dec kk 14%nat) as [He|He];
        [left; exact He | right; apply Hhn; lia]. }
  assert (Hbvk : bview kk h = bview kk f)
    by (apply bview_ext; exact Hhf).
  split; [| rewrite Hbh; rewrite Hbvk; rewrite Hbf; reflexivity ].
  rewrite Hbf. unfold name_pad.
  assert (Htk : take 14 (bview kk f) = bview kk f).
  { apply take_ge. rewrite bview_length. exact Hkk. }
  rewrite Htk.
  assert (Hlen : length (bview kk f) = kk) by apply bview_length.
  rewrite Hlen.
  apply list_eq. intros x.
  destruct (Nat.lt_ge_cases x 14) as [Hx|Hx].
  - rewrite (bview_lookup 14 h x Hx).
    destruct (Nat.lt_ge_cases x kk) as [Hxk|Hxk].
    + rewrite lookup_app_l.
      2:{ rewrite bview_length. exact Hxk. }
      rewrite (bview_lookup kk f x Hxk). rewrite (Hhf x Hxk). reflexivity.
    + rewrite lookup_app_r.
      2:{ rewrite bview_length. exact Hxk. }
      rewrite bview_length.
      rewrite lookup_replicate_2.
      2:{ lia. }
      rewrite (Hhn x Hxk Hx). reflexivity.
  - rewrite lookup_ge_None_2.
    2:{ rewrite bview_length. exact Hx. }
    symmetry. apply lookup_ge_None_2.
    rewrite length_app. rewrite bview_length. rewrite length_replicate. lia.
Qed.

Lemma snc_bview (f h : nat -> bv 8) :
  dl_snc f h 14 -> bview 14 h = name_pad (bname 14 f).
Proof.
  intros [[Hne Hhf] | (k & Hk & [Hne Hnul] & Hhf & Hhn)].
  - apply (snc_bview_aux f h 14%nat);
      [lia | exact Hne | left; reflexivity | exact Hhf |].
    intros x H1 H2. exfalso. lia.
  - apply (snc_bview_aux f h k);
      [lia | exact Hne | right; exact Hnul | exact Hhf | exact Hhn].
Qed.

Lemma snc_bname (f h : nat -> bv 8) :
  dl_snc f h 14 -> bname 14 h = bname 14 f.
Proof.
  intros [[Hne Hhf] | (k & Hk & [Hne Hnul] & Hhf & Hhn)].
  - apply (snc_bview_aux f h 14%nat);
      [lia | exact Hne | left; reflexivity | exact Hhf |].
    intros x H1 H2. exfalso. lia.
  - apply (snc_bview_aux f h k);
      [lia | exact Hne | right; exact Hnul | exact Hhf | exact Hhn].
Qed.

(* ...hence the record dirlink stores IS [de_of_name inum (bname 14 fn)] *)
Lemma snc_record (f h : nat -> bv 8) (i : bv 16) :
  dl_snc f h 14 -> MkDirent i (bview 14 h) = de_of_name i (bname 14 f).
Proof.
  intros H. unfold de_of_name. rewrite (snc_bview f h H). reflexivity.
Qed.

(* ====================================================================== *)
(*  7.  THE RECORD COUNT                                                   *)
(* ====================================================================== *)

(* [nrec], the number of WHOLE 16-byte records a directory of size [sz]
   holds.  Both loops run [off = 0, 16, 32, ...] while [off < sz]; when
   [16 | sz] that is exactly [dir_nrec sz] iterations and every readi is a
   full-length one, and when it is NOT the loop takes ONE more turn, whose
   readi is short and whose next instruction is panic("dirlookup read").
   See fs-icache.md §15(b): granularity is NOT a system invariant, so the
   two directory proofs carry that turn as a live panic arm rather than
   refuting it. *)
Definition dir_nrec (sz : Z) : nat := Z.to_nat (sz / 16).

Lemma dir_nrec_exact (sz : Z) :
  0 <= sz -> (16 | sz) -> Z.of_nat (16 * dir_nrec sz)%nat = sz.
Proof.
  intros Hnn [q Hq]. unfold dir_nrec.
  assert (Hq' : sz / 16 = q).
  { rewrite Hq. rewrite Z.div_mul; [reflexivity | lia]. }
  rewrite Hq'.
  assert (Hq0 : 0 <= q) by lia.
  rewrite Nat2Z.inj_mul. rewrite (Z2Nat.id q Hq0). lia.
Qed.

Lemma dir_nrec_bound (sz : Z) (i : nat) :
  0 <= sz -> (16 | sz) ->
  ((Z.of_nat i * 16 < sz) <-> (i < dir_nrec sz)%nat).
Proof.
  intros Hnn Hd. pose proof (dir_nrec_exact sz Hnn Hd) as He.
  rewrite Nat2Z.inj_mul in He. lia.
Qed.

(* ---- the GRANULARITY-FREE arithmetic (fs-icache.md §15(b)) -------------

   Without [16 | sz] the loop bound [off < sz] and the record count part
   ways in exactly one place: at [i = dir_nrec sz] the loop may still run
   (when [16 * nrec < sz], i.e. a short tail record exists) and its readi is
   short.  These three replace [dir_nrec_bound]'s two directions, each with
   the premise that is actually available:

   - [dir_nrec_ge] -- a WHOLE record below [nrec] fits, always;
   - [dir_nrec_le] -- and conversely, so "readi returned 16" IS [i < nrec];
   - [dir_nrec_lt_le] -- the loop test alone only bounds [i] by [nrec].     *)
Lemma dir_nrec_le (sz : Z) (i : nat) :
  0 <= sz -> ((Z.of_nat i * 16 + 16 <= sz) <-> (i < dir_nrec sz)%nat).
Proof.
  intros Hnn. unfold dir_nrec.
  pose proof (Z.div_mod sz 16 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound sz 16 ltac:(lia)) as Hmb.
  assert (Hd0 : 0 <= sz / 16) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma dir_nrec_ge (sz : Z) (i : nat) :
  0 <= sz -> (i < dir_nrec sz)%nat -> Z.of_nat i * 16 + 16 <= sz.
Proof. intros Hnn Hi. exact (proj2 (dir_nrec_le sz i Hnn) Hi). Qed.

Lemma dir_nrec_lt_le (sz : Z) (i : nat) :
  0 <= sz -> Z.of_nat i * 16 < sz -> (i <= dir_nrec sz)%nat.
Proof.
  intros Hnn Hi. unfold dir_nrec.
  pose proof (Z.div_mod sz 16 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound sz 16 ltac:(lia)) as Hmb.
  assert (Hd0 : 0 <= sz / 16) by (apply Z.div_pos; lia).
  lia.
Qed.

(* ====================================================================== *)
(*  8.  THE DIRECTORY-WF GATE (fs-icache.md §15(a))                        *)
(* ====================================================================== *)

(* EVERY LIVE RECORD'S INUM IS INSIDE THE INODE REGION.  This is iget's one
   argument premise ([bv_unsigned inum < 16 * nib]) lifted over the records,
   because the record a scan stops at is not known until it stops.  It used
   to live in [SpecDirlookup.v]; §15 makes it a SYSTEM INVARIANT riding in
   the icache's escrow payloads, which needs it visible from
   [IcacheEscrow.v] -- far below any spec file -- so it lives here, in the
   pure record view, and SpecDirlookup re-exports it by importing DirView. *)
Definition dir_inums_ok (data : nat -> list (bv 8)) (nrec nib : nat) : Prop :=
  forall k : nat, (k < nrec)%nat -> dir_live data k ->
    bv_unsigned (dir_inum data k) < 16 * Z.of_nat nib.

(* T_DIR as a NUMBER.  [SpecDirlookup.T_DIR] is the [mword 16] the
   [lh a4,68(a0)] / [li a5,1] pair compares; the escrow payloads have no
   register vocabulary and state the same test on [bv_unsigned]. *)
Definition T_DIR_z : Z := 1.

(* THE CONJUNCT THE TWO ESCROW PAYLOADS GAIN ([IcacheEscrow.ic_loaded] and
   [ipool_shape]'s allocated arm).  TYPE-CONDITIONAL, because it is only
   directories whose bytes are records: a file's data is arbitrary and a
   free inode has no data at all.  [nib] is the ambient [icfg_nib] at both
   payloads -- capacity, no resource.

   The writers that exist today preserve it, and every re-park in the cache
   (ilock's fill, iget's eviction, iunlock's park) carries it unchanged
   because it changed no byte.  itrunc leaves size 0, which makes it
   vacuous; iupdate touches no data; filewrite cannot reach a T_DIR inode
   (sys_open refuses writable directories).  dirlink is the one writer that
   needs an argument rather than a rides: see the N4a ledger in
   claude-notes/projects/fs-namei.md.

   ITS MIDDLE-SLOT ARM WAS ONCE UNDERIVABLE (§15.1(i)) and no longer is.
   writei's postcondition admitted a disturbed region of unspecified bytes
   after the write, which on an interior slot could have clobbered up to 64
   FOLLOWING records.  The fs-sysfile S2 retrofit strengthened SpecWritei's
   KERNEL arm to [dist = 0] -- either_copyin cannot fail there -- and
   SpecDirlink's clause is now exact.  [dir_ok_dirlink] below is the
   resulting derivation, for both the append and the middle-slot arm; it is
   the lemma create (fs-sysfile S5) uses to re-park the parent. *)
Definition dir_ok (nib : nat) (dn : dinode) (data : nat -> list (bv 8)) : Prop :=
  bv_unsigned (di_type dn) = T_DIR_z ->
  dir_inums_ok data (dir_nrec (bv_unsigned (di_size dn))) nib.

(* ---- the four ways a holder discharges it ---------------------------- *)

(* (i) it is not a directory *)
Lemma dir_ok_not_dir (nib : nat) (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> T_DIR_z -> dir_ok nib dn data.
Proof. intros H Hc. exfalso. exact (H Hc). Qed.

(* (ii) it is FREE -- [ipool_shape]'s free arm, and iput's post-itrunc park *)
Lemma dir_ok_free (nib : nat) (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) = 0 -> dir_ok nib dn data.
Proof.
  intros H. apply dir_ok_not_dir. rewrite H. unfold T_DIR_z. lia.
Qed.

(* (iii) it holds no whole record -- itrunc's zeroed directory, whose size
   is 0, and which is therefore wf whatever its type says *)
Lemma dir_ok_size_zero (nib : nat) (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_size dn) = 0 -> dir_ok nib dn data.
Proof.
  intros Hsz _ k Hk. exfalso.
  unfold dir_nrec in Hk. rewrite Hsz in Hk.
  assert (Hz : Z.to_nat (0 / 16) = 0%nat) by (vm_compute; reflexivity).
  rewrite Hz in Hk. clear -Hk. lia.
Qed.

(* (iv) the DATA is unchanged and so is the record -- the "rides" case every
   re-park in the cache is (ilock's fill, iget's eviction, iunlock's park) *)
Lemma dir_ok_eq (nib : nat) (dn dn' : dinode) (data data' : nat -> list (bv 8)) :
  dn = dn' -> data = data' -> dir_ok nib dn data -> dir_ok nib dn' data'.
Proof. intros -> ->. exact id. Qed.

(* ====================================================================== *)
(*  8a'.  THE ".." INDEX BRIDGE (fs-icache §20.17.4's owed fact,            *)
(*        fs-fragments R9).                                                 *)
(*                                                                          *)
(*  rmdir's [dp->nlink--] must be paid by ONE fragment of [dp]'s register    *)
(*  ([FsStateLink.link_tok]), and the only one in the system sits in the     *)
(*  CHILD's own [ent_toks], at the index of the child's [".."].  [dir_ok]    *)
(*  says only that live records COVER; nothing said WHICH index carries the  *)
(*  parent, so the arm could not name the fragment it had to spend.  This is *)
(*  that fact.                                                               *)
(*                                                                          *)
(*  IT IS THE INDEX HALF ONLY, AND DELIBERATELY SO.  "The parent" is a       *)
(*  relation between two inodes; a conjunct on ONE payload cannot state it,  *)
(*  and a parent parameter on the payload would move every contract that     *)
(*  names [ic_loaded].  So this says only WHERE the [".."] entry is; the     *)
(*  tree layer's [ents ip !! ".." = Some dp] says WHAT it names, and the     *)
(*  two compose because [dir_names_unique] (FsRep, R2's amendment) makes     *)
(*  any-match = first-match -- a live [".."] at index 1 is the ONLY live     *)
(*  [".."].  That is why no [dir_first] clause is needed here.               *)
(*                                                                          *)
(*  THE GUARD IS [T_DIR] *AND* [nlink <> 0], AND BOTH HALVES ARE            *)
(*  LOAD-BEARING: as a PAYLOAD conjunct the type guard alone is not weak     *)
(*  enough, because it is FALSE of a reachable parked state.  create's       *)
(*  mkdir arm reaches [fail:] from three [bltz]es (ProofCreate.v, +0x10a /   *)
(*  +0x11e / +0x130) and re-parks the child's [ic_loaded] at every one of    *)
(*  them; at the first two the child IS a directory whose [".."] was never   *)
(*  written -- the ["."] link fell short, or the [".."] link did -- so a     *)
(*  type-guarded clause is not vacuous there, it is false.  What discharges  *)
(*  all three is the [sh zero,74(s3)] at +0x146: [ip->nlink = 0] is stored   *)
(*  BEFORE the re-park, so what the walk rebuilds is an ORPHAN and           *)
(*  [dir_dots_ix_orphan] closes it in one line at every entry, with no     *)
(*  premise threaded to the body.  The complement -- what an orphaned        *)
(*  directory's records ARE -- is the [nlink = 0] clause riding beside this  *)
(*  one; the two guards partition the directory case and neither weakens     *)
(*  the other.                                                              *)
(*                                                                          *)
(*  IT COUNTS ITS OWN RECORDS, AND THAT IS WHAT MAKES THE PRESERVATION       *)
(*  SELF-SUPPLYING.  [dir_dots_ix_dirlink] has to know the write window is *)
(*  not index 1, i.e. that [dir_slot data nrec <> 1]: BELOW [nrec] the slot  *)
(*  is free ([dir_slot_free]) while index 1 is live, and AT [nrec] the slot  *)
(*  IS [nrec] -- which differs from 1 only because the clause carries        *)
(*  [2 <= nrec].  Stated as a premise instead, that fact has no supplier:    *)
(*  nothing in any walk pins a parent directory's size, so every caller      *)
(*  would have to assume a directory it never measured has two records.      *)
(*  Carrying the count HERE costs one [dir_nrec_mono] step per dirlink (the  *)
(*  size only ever grows) and closes the gap for every caller at once.       *)
(*                                                                          *)
(*  ITS CONTENT IS OVER [data] AND THE RECORD'S OWN THREE FIELDS, and the    *)
(*  round trip is what fixes which fields are admissible:                    *)
(*  [IcacheEscrow.dlinks_open] -> write -> [dlinks_intro] reconstructs       *)
(*  at a [dn'] related to nothing, so every field the clause names must be   *)
(*  one the RECONSTRUCTING caller knows of its own [dn'].  Type, nlink and   *)
(*  size all are -- and [dir_dots_ix_eq] is the congruence that says so,   *)
(*  in the form the re-parks need: nlink as an IMPLICATION and size as a     *)
(*  BOUND, because create's [dp->nlink++] moves the first and every growing  *)
(*  flush moves the second.                                                  *)
(* ====================================================================== *)

Definition dot_name    : list (bv 8) := [Z_to_bv 8 0x2e].
Definition dotdot_name : list (bv 8) := [Z_to_bv 8 0x2e; Z_to_bv 8 0x2e].

(*  IT PINS BOTH DOT RECORDS, AND THE SELF ONE IS NOT DECORATION.  The
    ["."] half is what supplies the ONE fact create's [".."] establishment
    cannot get anywhere else: [dirlink(ip, "..", dp->inum)] writes the
    PARENT's inum into the child's record 1, and [dir_live] of that record
    is exactly [dp->inum <> 0] -- which no landed statement provides
    ([IcacheRef.inode_held] carries only the upper bound, and namex drops
    [SpecDirlookup]'s own [0 < inum] when it returns an entry pointer).
    Under this clause the parent supplies it about ITSELF: a live directory's
    record 0 is a live ["."] naming its own inum, so [dir_dots_ix_self]
    reads [dp->inum <> 0] straight off the payload the walk already holds.
    That is why the clause takes [self] -- both payloads have the inum in
    hand, so it costs no arity anywhere. *)
Definition dir_dots_ix (self : Z) (dn : dinode)
    (data : nat -> list (bv 8)) : Prop :=
  bv_unsigned (di_type dn) = T_DIR_z ->
  bv_unsigned (di_nlink dn) <> 0 ->
    (2 <= dir_nrec (bv_unsigned (di_size dn)))%nat
    /\ dir_live data 0
    /\ bv_unsigned (dir_inum data 0) = self
    /\ bname 14 (dir_name data 0) = dot_name
    /\ dir_live data 1
    /\ bname 14 (dir_name data 1) = dotdot_name.

(* ---- A NAME A LOOKUP MISSED IS NEITHER DOT NAME (durable-disk G3) ----
   [InodeRegion]'s (U1)/(U2) price a register unit at [None] -- the value an
   UP-POINTING record carries -- so both walks that DEPOSIT a name record
   ([create]'s and [sys_link]'s) owe "the name I am about to write is not a
   dot name".  Neither has to look: the deposit only happens on the arm
   where [dirlookup] MISSED over the whole record range, and a live
   directory's records 0 and 1 ARE the two dot names.  The kernel agrees --
   xv6's [create] returns the existing inode and its [dirlink] returns -1. *)
Lemma dir_dots_miss_not_dots (self : Z) (dn : dinode)
    (data : nat -> list (bv 8)) (s : list (bv 8)) :
  bv_unsigned (di_type dn) = T_DIR_z ->
  bv_unsigned (di_nlink dn) <> 0 ->
  dir_dots_ix self dn data ->
  dir_first data (dir_nrec (bv_unsigned (di_size dn))) s = None ->
  s <> dot_name /\ s <> dotdot_name.
Proof.
  intros Hty Hnl Hddix Hnone.
  destruct (Hddix Hty Hnl) as (Hn2 & Hlv0 & _ & Hnm0 & Hlv1 & Hnm1).
  pose proof (proj1 (dir_first_None data
                       (dir_nrec (bv_unsigned (di_size dn))) s) Hnone) as Hm.
  split; intro Hc.
  - apply (Hm 0%nat); [lia |].
    unfold dir_match. split.
    + exact Hlv0.
    + rewrite Hnm0. rewrite Hc. reflexivity.
  - apply (Hm 1%nat); [lia |].
    unfold dir_match. split.
    + exact Hlv1.
    + rewrite Hnm1. rewrite Hc. reflexivity.
Qed.

(* the record count is monotone in the size, which is all a dirlink ever
   does to it ([cr_wi_size_max]: [di_size dn' = Z.max (di_size dn) …]) *)
Lemma dir_nrec_mono (sz sz' : Z) :
  sz <= sz' -> (dir_nrec sz <= dir_nrec sz')%nat.
Proof.
  intro H. unfold dir_nrec.
  pose proof (Z.div_le_mono sz sz' 16 ltac:(lia) H) as Hd. lia.
Qed.

(* THE DIVIDEND, and the reason the ["."] half is carried: a live directory
   has a NONZERO inum, said by the directory's own payload. *)
Lemma dir_dots_ix_self (self : Z) (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) = T_DIR_z -> bv_unsigned (di_nlink dn) <> 0 ->
  dir_dots_ix self dn data -> self <> 0.
Proof.
  intros Hty Hnl Hd. destruct (Hd Hty Hnl) as (_ & Hlv & Hin & _).
  rewrite <- Hin. unfold dir_live in Hlv. intro Hc. apply Hlv.
  apply bv_eq. rewrite Hc. reflexivity.
Qed.

(* ====================================================================== *)
(*  THE COMPLEMENT CLAUSE: what an ORPHANED directory's records ARE.       *)
(*                                                                        *)
(*  [dir_dots_ix] speaks only under [nlink <> 0]; this one speaks only     *)
(*  under [nlink = 0], and between them the directory case is partitioned  *)
(*  with no overlap and no gap.  An orphaned directory holds nothing but   *)
(*  its own two dot records -- true of THIS binary because sys_link's      *)
(*  orphan guard (xv6 f60ff58, ARM E2) refuses to [dirlink] into a         *)
(*  directory whose count has already fallen to zero.                      *)
(*                                                                        *)
(*  IT CARRIES THREE LOADS AT ONCE (fs-icache §20.6's itrunc row,          *)
(*  §20.17.5's residue, and sys_unlink's own input premise): a live        *)
(*  NON-dot record under it forces the home's count nonzero -- the fact    *)
(*  sys_unlink's rmdir arm could not otherwise supply, since its walker's  *)
(*  guard does not cross the [iunlock]/re-[ilock] window.                  *)
(*                                                                        *)
(*  THE CONTENT IS SPLIT OUT AS [dir_dots_only] because that is the form   *)
(*  a WALK carries: create's [fail:] twin takes the child at [nlink = 1]   *)
(*  and parks it at [nlink = 0], so a guarded premise would be vacuous on  *)
(*  the way in and demanded on the way out.  The bound is [dir_nrec], and  *)
(*  it is what makes the three [fail:] entries discharge -- at nrec 0 and  *)
(*  1 there is nothing or only [","]'s slot to check.                      *)
(* ====================================================================== *)

Definition dir_dots_only (dn : dinode) (data : nat -> list (bv 8)) : Prop :=
  forall k : nat, (k < dir_nrec (bv_unsigned (di_size dn)))%nat ->
    dir_live data k ->
    bname 14 (dir_name data k) = dot_name
    \/ bname 14 (dir_name data k) = dotdot_name.

Definition dir_orphan_clean (dn : dinode) (data : nat -> list (bv 8)) : Prop :=
  bv_unsigned (di_type dn) = T_DIR_z ->
  bv_unsigned (di_nlink dn) = 0 ->
    dir_dots_only dn data.

(* ---- its discharges, the same shape as the sibling clause's ---------- *)

Lemma dir_orphan_clean_not_dir (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> T_DIR_z -> dir_orphan_clean dn data.
Proof. intros H Hc _. exfalso. exact (H Hc). Qed.

Lemma dir_orphan_clean_free (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) = 0 -> dir_orphan_clean dn data.
Proof.
  intros H. apply dir_orphan_clean_not_dir. rewrite H. unfold T_DIR_z. lia.
Qed.

(* THE LIVE DISCHARGE, the exact mirror of [dir_dots_ix_orphan]: a
   directory somebody still names says nothing here. *)
Lemma dir_orphan_clean_live (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_nlink dn) <> 0 -> dir_orphan_clean dn data.
Proof. intros H _ Hc. exfalso. exact (H Hc). Qed.

(* ...and the size-zero one, which is what a truncated corpse and a claim
   box both are ([fresh_shape]'s [di_size = 0]). *)
Lemma dir_orphan_clean_size_zero (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_size dn) = 0 -> dir_orphan_clean dn data.
Proof.
  intros H _ _ k Hk. rewrite H in Hk.
  change (dir_nrec 0) with 0%nat in Hk. lia.
Qed.

(* the CONTENT form is what walks carry, so it needs the same two movers *)
Lemma dir_dots_only_of (dn dn' : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_size dn') = bv_unsigned (di_size dn) ->
  dir_dots_only dn data -> dir_dots_only dn' data.
Proof. intros Hsz Hd k Hk. rewrite Hsz in Hk. exact (Hd k Hk). Qed.

Lemma dir_orphan_clean_of_only (dn : dinode) (data : nat -> list (bv 8)) :
  dir_dots_only dn data -> dir_orphan_clean dn data.
Proof. intros H _ _. exact H. Qed.

(* the DIRLINK mover: a link into an orphan is what sys_link's guard makes
   unreachable, so the clause only has to survive a link into a LIVE
   directory -- where it is vacuous on both sides.  Stated over the content
   for the walk that appends to a directory it is about to orphan (create's
   [fail:] twin writes nothing after the store, so this is the shape the
   three entries need): a new record at [k0] is one of the two dot names,
   or the count did not reach it. *)
Lemma dir_dots_only_dirlink (dn dn' : dinode)
    (data data' : nat -> list (bv 8))
    (inum : bv 16) (s : list (bv 8)) (nrec k0 tot : nat) :
  nrec = dir_nrec (bv_unsigned (di_size dn)) ->
  k0 = dir_slot data nrec ->
  (dir_nrec (bv_unsigned (di_size dn')) <= S k0)%nat ->
  (s = dot_name \/ s = dotdot_name) ->
  (length s <= 14)%nat -> nonul s ->
  (16 <= tot)%nat ->
  (forall x : nat,
     file_byte data' x
     = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
       then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
       else file_byte data x) ->
  dir_dots_only dn data ->
  dir_dots_only dn' data'.
Proof.
  intros Hnrec Hk0 Hle Hs Hlen Hnn Htot Hrng Hd k Hk Hlv.
  destruct (decide (k = k0)) as [-> | Hne].
  - (* the written record IS one of the two names *)
    assert (Hb : forall j, (j < 16)%nat ->
              file_byte data' (16 * k0 + j)%nat
              = dirent_bytes (de_of_name inum s) !!! j).
    { intros j Hj. rewrite (Hrng (16 * k0 + j)%nat).
      rewrite decide_True; [| lia].
      replace (16 * k0 + j - 16 * k0)%nat with j by (clear -j; lia).
      reflexivity. }
    destruct (dir_record_of_name data' k0 inum s Hlen Hnn Hb) as [_ Hn].
    rewrite Hn. exact Hs.
  - (* every other record is BELOW the old count and rode through *)
    assert (Hwin : dir_win_agree data data' k).
    { intros j Hj. rewrite (Hrng (16 * k + j)%nat).
      rewrite decide_False; [reflexivity |]. intros [Hlo Hhi].
      apply Hne. lia. }
    (* [k <> k0] and [k] is below the new count, which reaches at most one
       past the write -- so [k] is below the OLD count, where the incoming
       clause speaks.  [dir_slot_le] is the only fact needed. *)
    assert (Hlt : (k < nrec)%nat).
    { pose proof (dir_slot_le data nrec) as Hsle.
      rewrite <- Hk0 in Hsle. clear -Hk Hle Hne Hsle. lia. }
    rewrite Hnrec in Hlt.
    rewrite (dir_bname_agree data data' k Hwin).
    apply (Hd k Hlt). unfold dir_live in Hlv |- *.
    rewrite <- (dir_inum_agree data data' k Hwin). exact Hlv.
Qed.

(* ---- the discharges: [dir_ok]'s four, plus the ORPHAN one the guard adds *)

Lemma dir_dots_ix_not_dir (self : Z) (dn : dinode)
    (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> T_DIR_z -> dir_dots_ix self dn data.
Proof. intros H Hc _. exfalso. exact (H Hc). Qed.

Lemma dir_dots_ix_free (self : Z) (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) = 0 -> dir_dots_ix self dn data.
Proof.
  intros H. apply dir_dots_ix_not_dir. rewrite H. unfold T_DIR_z. lia.
Qed.

(* THE ORPHAN DISCHARGE -- create's three [fail:] entries, and iput's
   post-itrunc park.  A directory nobody names has nothing to say about its
   dot records, which is exactly the state the [nlink = 0] sibling clause
   describes instead. *)
Lemma dir_dots_ix_orphan (self : Z) (dn : dinode)
    (data : nat -> list (bv 8)) :
  bv_unsigned (di_nlink dn) = 0 -> dir_dots_ix self dn data.
Proof. intros H _ Hc. exfalso. exact (Hc H). Qed.

(* THE CONGRUENCE over the three fields the clause names, and it takes the
   nlink one as an IMPLICATION and the size one as a BOUND rather than as
   three equalities -- because the re-parks that need it MOVE those fields.
   create's [dp->nlink++] at +0x134 hands the PARENT back at
   [cr_setf dp3 _ _ (di_nlink dp3 + 1)] (ProofCreate.v's ARM C-OK re-walk),
   a live directory whose count changed; there the caller closes the premise
   from its own [dp->nlink != 0] guard (sysfile.c:262) rather than from any
   equation, which an equality could not express.  All-equal is the
   degenerate case. *)
Lemma dir_dots_ix_eq (self : Z) (dn dn' : dinode)
    (data data' : nat -> list (bv 8)) :
  di_type dn' = di_type dn ->
  (bv_unsigned (di_nlink dn') <> 0 -> bv_unsigned (di_nlink dn) <> 0) ->
  bv_unsigned (di_size dn) <= bv_unsigned (di_size dn') ->
  data = data' ->
  dir_dots_ix self dn data -> dir_dots_ix self dn' data'.
Proof.
  intros Hty Hnl Hsz <- Hd Hdir' Hnl'.
  assert (Hdir : bv_unsigned (di_type dn) = T_DIR_z)
    by (rewrite <- Hty; exact Hdir').
  destruct (Hd Hdir (Hnl Hnl')) as (Hnrec & Hrest).
  split; [| exact Hrest]. pose proof (dir_nrec_mono _ _ Hsz). lia.
Qed.

(* ...and the one that makes it FREE across every append, WITH NO COUNT
   PREMISE.  [dir_slot] never returns a LIVE record ([dir_slot_free]) and
   the clause's own halves say records 0 AND 1 are live, so below [nrec] the
   window can be neither; AT [nrec] it cannot be either, because the
   clause's FIRST half says [2 <= nrec].  Both records then ride on the
   range clause untouched and the count rides on the size, which a dirlink
   only grows.  The clause preserves ITSELF -- every premise below is one
   the writing caller already holds about its own two records. *)
Lemma dir_dots_ix_dirlink (self : Z) (dn dn' : dinode)
    (data data' : nat -> list (bv 8))
    (inum : bv 16) (s : list (bv 8)) (nrec k0 tot : nat) :
  nrec = dir_nrec (bv_unsigned (di_size dn)) ->
  k0 = dir_slot data nrec ->
  (tot <= 16)%nat ->
  di_type dn' = di_type dn ->
  di_nlink dn' = di_nlink dn ->
  bv_unsigned (di_size dn) <= bv_unsigned (di_size dn') ->
  (forall x : nat,
     file_byte data' x
     = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
       then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
       else file_byte data x) ->
  dir_dots_ix self dn data ->
  dir_dots_ix self dn' data'.
Proof.
  intros Hnrec Hk0 Htot Hty Hnl Hsz Hrng Hd Hdir' Hnl'.
  assert (Hdir : bv_unsigned (di_type dn) = T_DIR_z)
    by (rewrite <- Hty; exact Hdir').
  assert (Hnlz : bv_unsigned (di_nlink dn) <> 0)
    by (rewrite <- Hnl; exact Hnl').
  destruct (Hd Hdir Hnlz) as (Hnrec2 & Hlv0 & Hin0 & Hnm0 & Hlv1 & Hnm1).
  rewrite <- Hnrec in Hnrec2.
  (* THE WINDOW MISSES BOTH DOT RECORDS, and every half of the clause is
     what makes it: [dir_slot] never returns a LIVE record below [nrec], and
     at [nrec] the count itself is what separates the slot from 0 and 1. *)
  assert (Hne : forall k : nat, (k < 2)%nat -> k0 <> k).
  { intros k Hk Hc.
    assert (Hlt : (dir_slot data nrec < nrec)%nat)
      by (rewrite <- Hk0; rewrite Hc; lia).
    pose proof (dir_slot_free data nrec Hlt) as Hfree.
    rewrite <- Hk0 in Hfree. rewrite Hc in Hfree.
    destruct k as [| k]; [exact (Hlv0 Hfree) |].
    destruct k as [| k]; [exact (Hlv1 Hfree) | lia]. }
  assert (Hwin : forall k : nat, (k < 2)%nat -> dir_win_agree data data' k).
  { intros k Hk j Hj. rewrite (Hrng (16 * k + j)%nat).
    rewrite decide_False; [reflexivity |]. intros [Hlo Hhi].
    apply (Hne k Hk). lia. }
  pose proof (Hwin 0%nat ltac:(lia)) as Hw0.
  pose proof (Hwin 1%nat ltac:(lia)) as Hw1.
  split; [pose proof (dir_nrec_mono _ _ Hsz); lia |].
  split; [unfold dir_live; rewrite (dir_inum_agree data data' 0 Hw0);
          exact Hlv0 |].
  split; [rewrite (dir_inum_agree data data' 0 Hw0); exact Hin0 |].
  split; [rewrite (dir_bname_agree data data' 0 Hw0); exact Hnm0 |].
  split; [unfold dir_live; rewrite (dir_inum_agree data data' 1 Hw1);
          exact Hlv1 |].
  rewrite (dir_bname_agree data data' 1 Hw1). exact Hnm1.
Qed.

(* ====================================================================== *)
(*  8b.  (v) THE WRITER'S CASE: the directory a dirlink just wrote into.    *)
(*       fs-icache.md §15.1(i), discharged by the fs-sysfile S2 retrofit.   *)
(* ====================================================================== *)

(* §15.1(i) recorded this as UNDERIVABLE, and it was, for a precise reason:
   writei's range clause conceded a DISTURBED REGION of up to BSIZE
   unspecified bytes above the written window, so a middle-slot link could
   have rewritten up to 64 FOLLOWING records with arbitrary bytes.  The
   retrofit removes the concession on the KERNEL arm ([SpecWritei]'s new
   [user = false -> dist = 0]), dirlink's clause is now EXACT, and the
   derivation below is what that buys.  create (fs-sysfile S5) is its
   caller: it re-parks the parent directory's escrow bundle after linking
   the new entry.

   THE THREE CASES AT THE WRITTEN SLOT [k0]:

     tot = 0    nothing was written -- [data'] IS [data] pointwise, and the
                size did not move either (the slot is at or below [nrec]).
     tot >= 2   the inum halfword is WHOLLY new, so the record's inum is
                [inum] and the premise bounds it directly.
     tot = 1    only the LOW byte is new.  The slot dirlink chose is FREE
                ([dir_slot_free]), so the old HIGH byte is zero and the
                stored halfword is [inum mod 256] -- no larger than [inum],
                hence still in range.  This is §15(a)'s mod-256 argument;
                §15.1(ii) correctly observed it had no home in the APPEND
                analysis, and here is where it does belong.

   EVERY OTHER RECORD is untouched: its two inum bytes lie outside
   [16*k0, 16*k0+tot) because [tot <= 16] and the record windows are
   16-aligned.  And the record COUNT grows by at most one, only when
   [k0 = nrec] AND the write was full -- which is the [tot >= 2] case. *)

(* the two bounds [dir_nrec] satisfies, in the one shape the count
   arithmetic below wants *)
Lemma dir_nrec_range (sz : Z) :
  0 <= sz ->
  Z.of_nat (16 * dir_nrec sz)%nat <= sz
  /\ sz < Z.of_nat (16 * dir_nrec sz)%nat + 16.
Proof.
  intros Hnn. unfold dir_nrec.
  pose proof (Z.div_mod sz 16 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound sz 16 ltac:(lia)) as Hmb.
  assert (Hd0 : 0 <= sz / 16) by (apply Z.div_pos; lia).
  rewrite Nat2Z.inj_mul. rewrite Z2Nat.id; [| exact Hd0].
  change (Z.of_nat 16) with 16. lia.
Qed.

(* the halfword's VALUE from its two bytes -- what the [tot = 1] link needs,
   where only the low byte is new and the high one is known zero *)
Lemma dir_inum_unsigned (data : nat -> list (bv 8)) (k : nat) :
  bv_unsigned (dir_inum data k)
  = bv_unsigned (file_byte data (16 * k)%nat)
    + 2 ^ 8 * bv_unsigned (file_byte data (16 * k + 1)%nat).
Proof.
  unfold dir_inum.
  pose proof (bv_unsigned_in_range 8 (file_byte data (16 * k)%nat)) as H0.
  pose proof (bv_unsigned_in_range 8 (file_byte data (16 * k + 1)%nat)) as H1.
  unfold bv_modulus in H0, H1. change (2 ^ Z.of_N 8) with 256 in H0, H1.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 16) with 65536.
  cbn [assemble_bytes]. rewrite Z.mod_small; [lia | lia].
Qed.

(* [dir_record_inum] needs only the record's FIRST TWO bytes; a partially
   written record supplies exactly those once [tot >= 2] *)
Lemma dir_inum_of_two (data : nat -> list (bv 8)) (k : nat) (d : dirent) :
  (forall j, (j < 2)%nat -> file_byte data (16 * k + j)%nat
                            = dirent_bytes d !!! j) ->
  dir_inum data k = de_inum d.
Proof.
  intros Hb.
  assert (Hb0 : file_byte data (16 * k + 0)%nat = dirent_bytes d !!! 0%nat)
    by (apply Hb; lia).
  assert (Hb1 : file_byte data (16 * k + 1)%nat = dirent_bytes d !!! 1%nat)
    by (apply Hb; lia).
  assert (E0 : (16 * k + 0)%nat = (16 * k)%nat) by lia.
  rewrite E0 in Hb0.
  assert (Hd0 : dirent_bytes d !!! 0%nat = nth_byte (de_inum d) 0%nat)
    by (apply dirent_bytes_inum_t; lia).
  assert (Hd1 : dirent_bytes d !!! 1%nat = nth_byte (de_inum d) 1%nat)
    by (apply dirent_bytes_inum_t; lia).
  apply de_half_bytes_inj.
  rewrite dir_inum_half_bytes. unfold half_bytes.
  rewrite Hb0. rewrite Hb1. rewrite Hd0. rewrite Hd1. reflexivity.
Qed.

Lemma dir_ok_dirlink (nib : nat) (dn dn' : dinode)
    (data data' : nat -> list (bv 8))
    (inum : bv 16) (s : list (bv 8)) (nrec k0 tot : nat) :
  nrec = dir_nrec (bv_unsigned (di_size dn)) ->
  k0 = dir_slot data nrec ->
  (tot <= 16)%nat ->
  (* THE LINKED CHILD'S RANGE -- SpecDirlink's new premise *)
  bv_unsigned inum < 16 * Z.of_nat nib ->
  (* writei preserves the type and installs [max(size, off+tot)] *)
  di_type dn' = di_type dn ->
  bv_unsigned (di_size dn')
    = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (16 * k0 + tot)) ->
  (* dirlink's TIGHTENED range clause: no disturbed region *)
  (forall x : nat,
     file_byte data' x
     = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
       then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
       else file_byte data x) ->
  dir_ok nib dn data ->
  dir_ok nib dn' data'.
Proof.
  intros Hnrec Hk0 Htot Hinum Hty Hsz Hrng Hok Hdir'.
  assert (Hdir : bv_unsigned (di_type dn) = T_DIR_z)
    by (rewrite <- Hty; exact Hdir').
  specialize (Hok Hdir).
  assert (Hsznn : 0 <= bv_unsigned (di_size dn))
    by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
  assert (Hsznn' : 0 <= bv_unsigned (di_size dn'))
    by exact (proj1 (bv_unsigned_in_range _ (di_size dn'))).
  destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hsznn) as [Hnr1 Hnr2].
  destruct (dir_nrec_range (bv_unsigned (di_size dn')) Hsznn') as [Hnr1' Hnr2'].
  rewrite <- Hnrec in Hnr1, Hnr2.
  assert (Hk0le : (k0 <= nrec)%nat) by (rewrite Hk0; apply dir_slot_le).
  (* THE COUNT ARITHMETIC: at most one more record, and only on a FULL
     write at the very end. *)
  assert (Hcount : (nrec <= dir_nrec (bv_unsigned (di_size dn')))%nat
                   /\ (dir_nrec (bv_unsigned (di_size dn')) = nrec
                       \/ (dir_nrec (bv_unsigned (di_size dn')) = S nrec
                           /\ k0 = nrec /\ tot = 16%nat))) by lia.
  destruct Hcount as [Hcle Hcalt].
  intros k Hk Hlive.
  (* the two inum bytes of a record OTHER than [k0] are untouched *)
  assert (Hagree : forall q : nat, q <> k0 -> dir_inum data' q = dir_inum data q).
  { intros q Hq. unfold dir_inum.
    rewrite (Hrng (16 * q)%nat). rewrite (Hrng (16 * q + 1)%nat).
    rewrite decide_False; [| lia]. rewrite decide_False; [| lia]. reflexivity. }
  destruct (Nat.eq_dec k k0) as [Hkk | Hkn].
  - (* ======== THE WRITTEN SLOT ======== *)
    subst k.
    destruct tot as [| tot1].
    + (* nothing written: [data'] IS [data], and the size did not move *)
      assert (Hag0 : dir_inum data' k0 = dir_inum data k0).
      { unfold dir_inum.
        rewrite (Hrng (16 * k0)%nat). rewrite (Hrng (16 * k0 + 1)%nat).
        rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
        reflexivity. }
      rewrite Hag0. unfold dir_live in Hlive. rewrite Hag0 in Hlive.
      apply Hok; [lia | exact Hlive].
    + destruct tot1 as [| tot2].
      * (* ---- tot = 1: only the LOW byte is new ---- *)
        (* a one-byte write cannot have grown the record count, so the slot
           is a genuine MIDDLE slot and [dir_slot_free] applies *)
        assert (Hk0n : (k0 < nrec)%nat) by lia.
        assert (Hfree : dir_inum data k0 = bv_0 16)
          by (rewrite Hk0; apply dir_slot_free; rewrite <- Hk0; exact Hk0n).
        assert (Hhi : file_byte data' (16 * k0 + 1)%nat = NUL).
        { rewrite (Hrng (16 * k0 + 1)%nat). rewrite decide_False; [| lia].
          rewrite <- dir_inum_byte1. rewrite Hfree. apply nth_byte_bv0. }
        assert (Hlo : file_byte data' (16 * k0)%nat = nth_byte inum 0%nat).
        { rewrite (Hrng (16 * k0)%nat). rewrite decide_True; [| lia].
          replace (16 * k0 - 16 * k0)%nat with 0%nat by lia.
          rewrite (dirent_bytes_inum_t (de_of_name inum s) 0%nat ltac:(lia)).
          reflexivity. }
        rewrite dir_inum_unsigned. rewrite Hhi. rewrite Hlo.
        assert (HNUL : bv_unsigned NUL = 0) by (vm_compute; reflexivity).
        rewrite HNUL.
        rewrite nth_byte_unsigned.
        change (Z.of_N (8 * N.of_nat 0)) with 0.
        rewrite Z.shiftr_0_r.
        pose proof (Z.mod_pos_bound (bv_unsigned inum) (2 ^ 8) ltac:(lia)) as Hmb.
        pose proof (Z.mod_le (bv_unsigned inum) (2 ^ 8)
                      (proj1 (bv_unsigned_in_range _ inum)) ltac:(lia)) as Hml.
        lia.
      * (* ---- tot >= 2: the whole inum halfword is new ---- *)
        assert (Hrec : dir_inum data' k0 = inum).
        { rewrite (dir_inum_of_two data' k0 (de_of_name inum s)); [reflexivity |].
          intros jj Hjj. rewrite (Hrng (16 * k0 + jj)%nat).
          rewrite decide_True; [| lia].
          replace (16 * k0 + jj - 16 * k0)%nat with jj by lia. reflexivity. }
        rewrite Hrec. exact Hinum.
  - (* ======== ANY OTHER RECORD: untouched, and below [nrec] ======== *)
    rewrite (Hagree k Hkn).
    unfold dir_live in Hlive. rewrite (Hagree k Hkn) in Hlive.
    apply Hok; [lia | exact Hlive].
Qed.

(* ...and the way a CONSUMER uses it: namex knows the type, off the very
   [lh]/[li] test that refutes panic("dirlookup not DIR"). *)
Lemma dir_ok_dir (nib : nat) (dn : dinode) (data : nat -> list (bv 8)) :
  di_type dn = (mword_of_int 1 : mword 16) ->
  dir_ok nib dn data ->
  dir_inums_ok data (dir_nrec (bv_unsigned (di_size dn))) nib.
Proof.
  intros Ht H. apply H. rewrite Ht. vm_compute. reflexivity.
Qed.

