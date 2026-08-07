(* BlockWords.v -- the words inside a disk block.

   A disk block is 1024 raw bytes ([list (bv 8)] of length BSIZE); an
   INDIRECT block is those same bytes read as 256 little-endian 32-bit
   entries ([list (bv 32)] of length NINDIRECT).  [ByteBuf.v] is
   byte-granular and says nothing about that reading, so the inode layer
   (see claude-notes/design/fs-inode.md, "Words inside a block") needs this
   small vocabulary of its own:

     [ind_bytes e]  -- the byte image of the entry list [e]: each entry's
                       four little-endian bytes, entries in order.  Entry
                       [i]'s byte [j] sits at index [4*i+j], which is
                       exactly the address the code computes
                       ([bp->data + 4*(bn-NDIRECT)] plus the byte offset).

   The four consumer-facing laws are LENGTH ([ind_bytes_length],
   [ind_bytes_insert_length]) and LOOKUP ([ind_bytes_lookup], and the two
   insert laws [ind_bytes_insert_same] / [ind_bytes_insert_other] that say
   installing a new entry rewrites its own four bytes and disturbs nothing
   else).  Together they are what lets bmap's [log_write] of a whole block
   be related to a one-entry update of the pure entry list.

   The byte extractor is the tree's EXISTING [RiscvModelBytes.nth_byte]
   (the same one [RiscvPtsto.word4_pointsto] splits a [bv 32] with, over
   [seq 0 4]) -- there is deliberately no second byte-splitting function.

   This file is iris-FREE (no proofmode, no ssreflect) so it stays usable
   from the vanilla-[rewrite ... by ...] files, per durable-notes'
   ssreflect-free rule; [RiscvModelBytes.v] is iris-free for the same
   reason, so naming [nth_byte] costs nothing here. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import RiscvModelBytes.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The byte image of one entry, and of a list of entries.                  *)
(* ---------------------------------------------------------------------- *)

(* one 32-bit entry, little-endian: byte 0 is the least significant *)
Definition word_bytes (w : bv 32) : list (bv 8) :=
  [nth_byte w 0%nat; nth_byte w 1%nat; nth_byte w 2%nat; nth_byte w 3%nat].

Fixpoint ind_bytes (e : list (bv 32)) : list (bv 8) :=
  match e with
  | [] => []
  | w :: e' => word_bytes w ++ ind_bytes e'
  end.

(* The two defining equations, stated so no proof below ever has to [simpl]
   through [ind_bytes] (which would also expand [word_bytes]' literal). *)
Lemma ind_bytes_nil : ind_bytes [] = [].
Proof. reflexivity. Qed.

Lemma ind_bytes_cons (w : bv 32) (e : list (bv 32)) :
  ind_bytes (w :: e) = (word_bytes w ++ ind_bytes e)%list.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Helpers about one entry.                                                *)
(* ---------------------------------------------------------------------- *)

Lemma word_bytes_length (w : bv 32) : length (word_bytes w) = 4%nat.
Proof. reflexivity. Qed.

Lemma word_bytes_lookup (w : bv 32) (j : nat) :
  (j < 4)%nat -> word_bytes w !! j = Some (nth_byte w j).
Proof.
  intros Hj. destruct j as [|[|[|[|j]]]]; try reflexivity. exfalso; lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* Length.                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma ind_bytes_length (e : list (bv 32)) :
  length (ind_bytes e) = (4 * length e)%nat.
Proof.
  induction e as [|w e IH]; [reflexivity|].
  rewrite ind_bytes_cons, length_app, word_bytes_length, IH.
  simpl length. lia.
Qed.

(* the shape the inode layer uses it at: NINDIRECT entries fill a block *)
Lemma ind_bytes_length_256 (e : list (bv 32)) :
  length e = 256%nat -> length (ind_bytes e) = 1024%nat.
Proof. intros He. rewrite ind_bytes_length, He. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Lookup.                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma ind_bytes_lookup (e : list (bv 32)) (i j : nat) :
  (i < length e)%nat -> (j < 4)%nat ->
  ind_bytes e !! (4 * i + j)%nat = Some (nth_byte (e !!! i) j).
Proof.
  revert i. induction e as [|w e IH]; intros i Hi Hj.
  { simpl length in Hi. exfalso; lia. }
  simpl length in Hi. rewrite ind_bytes_cons.
  destruct i as [|i'].
  - replace (4 * 0 + j)%nat with j by lia.
    rewrite lookup_app_l by (rewrite word_bytes_length; lia).
    rewrite word_bytes_lookup by lia. reflexivity.
  - replace (4 * S i' + j)%nat with (4 + (4 * i' + j))%nat by lia.
    rewrite lookup_app_r by (rewrite word_bytes_length; lia).
    rewrite word_bytes_length.
    replace (4 + (4 * i' + j) - 4)%nat with (4 * i' + j)%nat by lia.
    rewrite IH by lia. reflexivity.
Qed.

Lemma ind_bytes_lookup_None (e : list (bv 32)) (k : nat) :
  (4 * length e <= k)%nat -> ind_bytes e !! k = None.
Proof.
  intros Hk. apply lookup_ge_None_2. rewrite ind_bytes_length. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* Installing one entry.                                                   *)
(* ---------------------------------------------------------------------- *)

Lemma ind_bytes_insert_same (e : list (bv 32)) (i : nat) (v : bv 32) (j : nat) :
  (i < length e)%nat -> (j < 4)%nat ->
  ind_bytes (<[i:=v]> e) !! (4 * i + j)%nat = Some (nth_byte v j).
Proof.
  intros Hi Hj.
  rewrite ind_bytes_lookup; [| rewrite length_insert; exact Hi | exact Hj].
  rewrite list_lookup_total_insert by exact Hi. reflexivity.
Qed.

Lemma ind_bytes_insert_other (e : list (bv 32)) (i : nat) (v : bv 32) (k : nat) :
  (i < length e)%nat -> (k < 4 * i \/ 4 * i + 4 <= k)%nat ->
  ind_bytes (<[i:=v]> e) !! k = ind_bytes e !! k.
Proof.
  intros Hi Hk.
  destruct (Nat.lt_ge_cases k (4 * length e)) as [Hlt|Hge].
  - (* inside the image: both sides are entry [k/4]'s byte [k mod 4] *)
    pose proof (Nat.div_mod_eq k 4) as Hk4.
    assert (Hr : (k mod 4 < 4)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (Hq : (k / 4 < length e)%nat) by lia.
    assert (Hqi : (k / 4 <> i)%nat) by lia.
    remember (k / 4)%nat as q eqn:Hq'.
    remember (k mod 4)%nat as r eqn:Hr'.
    clear Hq' Hr'. subst k.
    rewrite ind_bytes_lookup; [| rewrite length_insert; exact Hq | exact Hr].
    rewrite ind_bytes_lookup by assumption.
    rewrite list_lookup_total_insert_ne by lia. reflexivity.
  - (* past the image: both sides are None *)
    rewrite ind_bytes_lookup_None by (rewrite length_insert; lia).
    rewrite ind_bytes_lookup_None by lia. reflexivity.
Qed.

Lemma ind_bytes_insert_length (e : list (bv 32)) (i : nat) (v : bv 32) :
  length (ind_bytes (<[i:=v]> e)) = length (ind_bytes e).
Proof. rewrite !ind_bytes_length, length_insert. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The ALL-ZERO entry list.                                                *)
(*                                                                         *)
(* balloc hands out a block whose content is [replicate BSIZE 0] (bzero has *)
(* already logged it as a zero block), and bmap installs exactly such a     *)
(* block as a fresh INDIRECT block.  So the inode layer has to read that    *)
(* byte image back as an entry list, and the only entry list it can be is   *)
(* the all-zero one.  Stated at a symbolic length so the two constants      *)
(* ([NINDIRECT], [BSIZE]) stay in the file that owns them.                  *)
(* ---------------------------------------------------------------------- *)

Lemma nth_byte_zero {m : N} (j : nat) : nth_byte (bv_0 m) j = bv_0 8.
Proof.
  apply bv_eq. unfold nth_byte.
  rewrite bv_extract_unsigned, !bv_0_unsigned, Z.shiftr_0_l.
  unfold bv_wrap. reflexivity.
Qed.

Lemma word_bytes_zero : word_bytes (bv_0 32) = replicate 4 (bv_0 8).
Proof. unfold word_bytes. rewrite !nth_byte_zero. reflexivity. Qed.

Lemma ind_bytes_replicate (n : nat) :
  ind_bytes (replicate n (bv_0 32)) = replicate (4 * n) (bv_0 8).
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [replicate]. rewrite ind_bytes_cons, word_bytes_zero, IH.
  replace (4 * S n)%nat with (4 + 4 * n)%nat by lia.
  rewrite replicate_add. reflexivity.
Qed.
