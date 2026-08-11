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
Require Import BlockWords.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import InodeInv.

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

(* [nrec], the number of 16-byte records a directory of size [sz] holds.
   Both loops run [off = 0, 16, 32, ...] while [off < sz], so under the
   GRANULARITY premise [16 | sz] the loop performs exactly [dir_nrec sz]
   iterations and every readi is a full-length one. *)
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
