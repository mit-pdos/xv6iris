(* DirentEnc.v -- the DIRECTORY ENTRY: [struct dirent], its 16-byte encoding,
   the sixty-four of them that fill one block, and the NAME model the
   directory layer compares with.

   The fourth byte vocabulary of the tree, after [BlockWords.v]'s words,
   [DinodeEnc.v]'s records and [BitmapEnc.v]'s bits, and it follows the same
   discipline as [DinodeEnc.v]: a block's content is always kept in the IMAGE
   of an encoding function over a list of PURE records, so an update is an
   [<[k := d]>] on that list and the byte level is only ever READ BACK.

     dirent_bytes d   16 bytes:  inum@0 (2 bytes, little-endian)
                                 name@2 (DIRSIZ = 14 bytes)
     dirblk_bytes ds  the sixty-four in order = 1024 bytes = BSIZE

   THE GEOMETRY IS READ OFF dirlookup's AND dirlink's INSTRUCTION STREAMS,
   not off fs.h (the rule [DinodeEnc.v] and [InodeInv.v] already state):

     dirlookup+0x2a  addi s4,s0,-96   ; +0x30  addi s6,s0,-94
                                  ==>  &de = s0-96, &de.name = s0-94,
                                       i.e. INUM AT +0, NAME AT +2
     dirlookup+0x2e  li s3,16 ; +0x5c mv a4,s3 ; jal readi
                     +0x52  addiw s1,s1,16
                                  ==>  readi's n is 16 and off advances by
                                       16, i.e. THE STRIDE IS 16 BYTES
     dirlookup+0x6e  lhu a5,-96(s0) ; +0x72 beqz a5,<continue>
                                  ==>  the FREE test is [de.inum == 0], read
                                       as an UNSIGNED halfword ([de_free])
     dirlookup+0x74  mv a1,s6 ; mv a0,s5 ; jal namecmp
     namecmp+0x08    li a2,14 ; jal strncmp
                                  ==>  DIRSIZ = 14, and namecmp IS
                                       strncmp(name, de.name, 14)
     dirlink+0x70    li a2,14 ; mv a1,s5 ; addi a0,s0,-78 ; jal STRNCPY
                     +0x7c  sh s6,-80(s0)
                                  ==>  the name is written with strncpy, so
                                       it is NUL-PADDED to 14 ([de_padded]),
                                       and the inum with a 2-byte [sh]

   Sixty-four records per block is BSIZE/16 = 1024/16; the file states every
   law with the LITERALS 16 and 64 (never [DESIZE]/[DPB]) for the same reason
   [DinodeEnc.v] does: a consumer's offsets arrive as literals out of the
   instruction stream and a [rewrite] against a folded constant does not
   match.

   ---- THE NAME MODEL -------------------------------------------------------

   Names are C strings inside a fixed 14-byte field, so the CANONICAL name is
   the prefix before the first NUL, capped at 14: [cut_nul] on a list,
   [bname n f] on a [ByteBuf] naming function.  Two facts justify this being
   the only name notion the directory layer needs:

   - dirlink writes with STRNCPY, which NUL-pads the tail ([de_padded]); so a
     dirent on disk is exactly [name_pad s] for its canonical [s], and
     canonical equality determines the bytes ([de_name_faithful]).  This is
     what makes the directory's [name -> inum] view well defined.
   - namex's own name buffer is NOT padded -- skipelem's short branch writes
     [memmove(name, s, len); name[len] = 0] and leaves the bytes past the NUL
     untouched, and its long branch ([len >= DIRSIZ]) writes 14 bytes and NO
     terminator at all.  strncmp at n = 14 never looks past the first NUL or
     past index 13, so the bridge below needs NO padding hypothesis on either
     side: [nc_zero_iff] is an unconditional equivalence between "namecmp
     returned 0" and "the canonical views agree".

   [SpecStrncmp.v] is iris-heavy and this file is a pure leaf, so the bridge
   is stated over [nc_stop] / [nc_run] -- the two arms of [strncmp_res]
   transcribed byte for byte ([bb_nonul] unfolded), with the returned word
   removed.  A caller turns [strncmp_res f g 14 res] with [res = 0] into
   [(exists k, nc_stop f g 14 k /\ f k = g k) \/ nc_run f g 14] by the one
   arithmetic step [mword_of_int (bv_unsigned (f k) - bv_unsigned (g k)) = 0
   -> f k = g k] (both bytes are below 256, so the 64-bit difference is
   small), and then reads off [nc_zero_iff].

   iris-FREE (no proofmode, no ssreflect), like [DinodeEnc.v], so it stays
   usable from the vanilla-[rewrite ... by ...] files.  It does name
   [SailStdpp.Values], which [BitmapEnc.v] deliberately avoids: the NUL byte
   is spelled [mword_of_int 0] so that the bridge's statement is SYNTACTICALLY
   the one [SpecStrncmp.v] and [ByteBuf.v] use.  Every consumer of this file
   (the dirlookup / dirlink / namex proofs) imports [SailStdpp.Values]
   already.                                                                *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.Values.
Require Import RiscvModelBytes.
Require Import BlockWords.
Require Import DinodeEnc.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The record, and the block geometry.                                     *)
(* ---------------------------------------------------------------------- *)

Record dirent := MkDirent {
  de_inum : bv 16;
  de_name : list (bv 8);     (* DIRSIZ = 14 bytes *)
}.

Definition DIRSIZ : nat := 14%nat.        (* sizeof(de.name) *)
Definition DESIZE : nat := 16%nat.        (* sizeof(struct dirent) *)
Definition DPB : nat := 64%nat.           (* BSIZE / sizeof(struct dirent) *)
(* NOTE: as in [DinodeEnc.v], every law below is stated with the LITERALS
   14 / 16 / 64, never with these names. *)

Definition dirent_wf (d : dirent) : Prop := length (de_name d) = 14%nat.
Definition dirblk_wf (ds : list dirent) : Prop :=
  length ds = 64%nat /\ Forall dirent_wf ds.

(* the NUL byte, spelled exactly as [ByteBuf.v] / [SpecStrncmp.v] spell it *)
Definition NUL : bv 8 := (mword_of_int 0 : mword 8).

(* [!!!] over a [list dirent] needs a default; nothing below ever reads it
   (every lookup is guarded by [k < length ds]). *)
Global Instance dirent_inhabited : Inhabited dirent :=
  populate (MkDirent (bv_0 16) []).

(* the FREE test dirlookup's [lhu]/[beqz] pair performs *)
Definition de_free (d : dirent) : Prop := de_inum d = bv_0 16.

(* ---------------------------------------------------------------------- *)
(* The encoding.                                                           *)
(* ---------------------------------------------------------------------- *)

(* [half_bytes] is [DinodeEnc]'s: there is deliberately no second
   little-endian 16-bit encoder. *)
Definition dirent_bytes (d : dirent) : list (bv 8) :=
  (half_bytes (de_inum d) ++ de_name d)%list.

Fixpoint dirblk_bytes (ds : list dirent) : list (bv 8) :=
  match ds with
  | [] => []
  | d :: ds' => (dirent_bytes d ++ dirblk_bytes ds')%list
  end.

Lemma dirblk_bytes_nil : dirblk_bytes [] = [].
Proof. reflexivity. Qed.

Lemma dirblk_bytes_cons (d : dirent) (ds : list dirent) :
  dirblk_bytes (d :: ds) = (dirent_bytes d ++ dirblk_bytes ds)%list.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* One record: length, and the two field readings.                         *)
(* ---------------------------------------------------------------------- *)

Lemma dirent_bytes_length (d : dirent) :
  dirent_wf d -> length (dirent_bytes d) = 16%nat.
Proof.
  unfold dirent_wf, dirent_bytes. intros Hd.
  rewrite length_app, half_bytes_length, Hd. reflexivity.
Qed.

Lemma dirent_bytes_inum (d : dirent) (j : nat) :
  (j < 2)%nat -> dirent_bytes d !! j = Some (nth_byte (de_inum d) j).
Proof.
  intros Hj. unfold dirent_bytes.
  rewrite lookup_app_l by (rewrite half_bytes_length; lia).
  apply half_bytes_lookup; exact Hj.
Qed.

Lemma dirent_bytes_name (d : dirent) (j : nat) :
  dirent_bytes d !! (2 + j)%nat = de_name d !! j.
Proof.
  unfold dirent_bytes.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length. replace (2 + j - 2)%nat with j by lia.
  reflexivity.
Qed.

Lemma dirent_bytes_inum_t (d : dirent) (j : nat) :
  (j < 2)%nat -> dirent_bytes d !!! j = nth_byte (de_inum d) j.
Proof. intros Hj. apply list_lookup_total_correct, dirent_bytes_inum, Hj. Qed.

Lemma dirent_bytes_name_t (d : dirent) (j : nat) :
  dirent_bytes d !!! (2 + j)%nat = de_name d !!! j.
Proof. rewrite !list_lookup_total_alt, dirent_bytes_name. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The block: length, slot lookup, and one-slot installation.              *)
(* ---------------------------------------------------------------------- *)

Lemma dirblk_bytes_length (ds : list dirent) :
  Forall dirent_wf ds -> length (dirblk_bytes ds) = (16 * length ds)%nat.
Proof.
  induction ds as [|d ds IH]; intros Hall; [reflexivity|].
  inversion Hall as [|xd xds Hd Hds]; subst.
  rewrite dirblk_bytes_cons, length_app, (dirent_bytes_length d Hd), (IH Hds).
  simpl length. lia.
Qed.

Lemma dirblk_bytes_length_64 (ds : list dirent) :
  dirblk_wf ds -> length (dirblk_bytes ds) = 1024%nat.
Proof.
  intros [Hlen Hall]. rewrite (dirblk_bytes_length ds Hall), Hlen. reflexivity.
Qed.

Lemma dirblk_bytes_lookup (ds : list dirent) (k j : nat) :
  Forall dirent_wf ds -> (k < length ds)%nat -> (j < 16)%nat ->
  dirblk_bytes ds !! (16 * k + j)%nat = dirent_bytes (ds !!! k) !! j.
Proof.
  revert k. induction ds as [|d ds IH]; intros k Hall Hk Hj.
  { simpl length in Hk. exfalso; lia. }
  inversion Hall as [|xd xds Hd Hds]; subst.
  simpl length in Hk. rewrite dirblk_bytes_cons.
  destruct k as [|k'].
  - replace (16 * 0 + j)%nat with j by lia.
    rewrite lookup_app_l by (rewrite (dirent_bytes_length d Hd); lia).
    reflexivity.
  - replace (16 * S k' + j)%nat with (16 + (16 * k' + j))%nat by lia.
    rewrite lookup_app_r by (rewrite (dirent_bytes_length d Hd); lia).
    rewrite (dirent_bytes_length d Hd).
    replace (16 + (16 * k' + j) - 16)%nat with (16 * k' + j)%nat by lia.
    rewrite (IH k' Hds ltac:(lia) Hj). reflexivity.
Qed.

Lemma dirblk_bytes_lookup_None (ds : list dirent) (i : nat) :
  Forall dirent_wf ds -> (16 * length ds <= i)%nat ->
  dirblk_bytes ds !! i = None.
Proof.
  intros Hall Hi. apply lookup_ge_None_2.
  rewrite (dirblk_bytes_length ds Hall). lia.
Qed.

Lemma dirent_wf_insert (ds : list dirent) (k : nat) (d : dirent) :
  Forall dirent_wf ds -> dirent_wf d -> Forall dirent_wf (<[k := d]> ds).
Proof. intros Hall Hd. apply Forall_insert; [exact Hall | exact Hd]. Qed.

Lemma dirblk_wf_insert (ds : list dirent) (k : nat) (d : dirent) :
  dirblk_wf ds -> dirent_wf d -> dirblk_wf (<[k := d]> ds).
Proof.
  intros [Hlen Hall] Hd. split.
  - rewrite length_insert. exact Hlen.
  - apply dirent_wf_insert; assumption.
Qed.

Lemma dirblk_bytes_insert_same (ds : list dirent) (k : nat) (d : dirent) (j : nat) :
  Forall dirent_wf ds -> dirent_wf d -> (k < length ds)%nat -> (j < 16)%nat ->
  dirblk_bytes (<[k := d]> ds) !! (16 * k + j)%nat = dirent_bytes d !! j.
Proof.
  intros Hall Hd Hk Hj.
  rewrite (dirblk_bytes_lookup (<[k := d]> ds) k j
             (dirent_wf_insert ds k d Hall Hd)
             ltac:(rewrite length_insert; exact Hk) Hj).
  rewrite list_lookup_total_insert by exact Hk. reflexivity.
Qed.

Lemma dirblk_bytes_insert_other (ds : list dirent) (k : nat) (d : dirent) (i : nat) :
  Forall dirent_wf ds -> dirent_wf d -> (k < length ds)%nat ->
  (i < 16 * k \/ 16 * k + 16 <= i)%nat ->
  dirblk_bytes (<[k := d]> ds) !! i = dirblk_bytes ds !! i.
Proof.
  intros Hall Hd Hk Hi.
  pose proof (dirent_wf_insert ds k d Hall Hd) as Hall'.
  destruct (Nat.lt_ge_cases i (16 * length ds)) as [Hlt|Hge].
  - (* inside the image: both sides are record [i / 16]'s byte [i mod 16] *)
    pose proof (Nat.div_mod_eq i 16) as Hi16.
    assert (Hr : (i `mod` 16 < 16)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (Hq : (i `div` 16 < length ds)%nat) by nia.
    assert (Hqi : (i `div` 16 <> k)%nat) by nia.
    remember (i `div` 16)%nat as q eqn:Hq'.
    remember (i `mod` 16)%nat as r eqn:Hr'.
    clear Hq' Hr'. subst i.
    rewrite (dirblk_bytes_lookup (<[k := d]> ds) q r Hall'
               ltac:(rewrite length_insert; exact Hq) Hr).
    rewrite (dirblk_bytes_lookup ds q r Hall Hq Hr).
    rewrite list_lookup_total_insert_ne by lia. reflexivity.
  - (* past the image: both sides are None *)
    rewrite (dirblk_bytes_lookup_None (<[k := d]> ds) i Hall'
               ltac:(rewrite length_insert; exact Hge)).
    rewrite (dirblk_bytes_lookup_None ds i Hall Hge). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The same readings in TOTAL-lookup form: a [ByteBuf] window is named by a *)
(* FUNCTION, so every consumer wants [!!!], not [!!].                       *)
(* ---------------------------------------------------------------------- *)

Lemma dirblk_wf_slot (ds : list dirent) (k : nat) :
  Forall dirent_wf ds -> (k < length ds)%nat -> dirent_wf (ds !!! k).
Proof.
  intros Hall Hk. eapply Forall_lookup_1; [exact Hall |].
  apply list_lookup_lookup_total_lt; exact Hk.
Qed.

Lemma dirblk_bytes_lookup_t (ds : list dirent) (k j : nat) :
  Forall dirent_wf ds -> (k < length ds)%nat -> (j < 16)%nat ->
  dirblk_bytes ds !!! (16 * k + j)%nat = dirent_bytes (ds !!! k) !!! j.
Proof.
  intros Hall Hk Hj. apply list_lookup_total_correct.
  rewrite (dirblk_bytes_lookup ds k j Hall Hk Hj).
  apply list_lookup_lookup_total_lt.
  rewrite (dirent_bytes_length (ds !!! k) (dirblk_wf_slot ds k Hall Hk)). lia.
Qed.

Lemma dirblk_bytes_insert_same_t (ds : list dirent) (k : nat) (d : dirent) (j : nat) :
  Forall dirent_wf ds -> dirent_wf d -> (k < length ds)%nat -> (j < 16)%nat ->
  dirblk_bytes (<[k := d]> ds) !!! (16 * k + j)%nat = dirent_bytes d !!! j.
Proof.
  intros Hall Hd Hk Hj. apply list_lookup_total_correct.
  rewrite (dirblk_bytes_insert_same ds k d j Hall Hd Hk Hj).
  apply list_lookup_lookup_total_lt.
  rewrite (dirent_bytes_length d Hd). lia.
Qed.

Lemma dirblk_bytes_insert_other_t (ds : list dirent) (k : nat) (d : dirent) (i : nat) :
  Forall dirent_wf ds -> dirent_wf d -> (k < length ds)%nat ->
  (i < 16 * k \/ 16 * k + 16 <= i)%nat ->
  dirblk_bytes (<[k := d]> ds) !!! i = dirblk_bytes ds !!! i.
Proof.
  intros Hall Hd Hk Hi.
  rewrite !list_lookup_total_alt, (dirblk_bytes_insert_other ds k d i Hall Hd Hk Hi).
  reflexivity.
Qed.

(* the two PER-BYTE readings straight out of the block image, at the offsets
   dirlookup's [lhu ...,-96(s0)] and its [de.name] pointer name *)
Lemma dirblk_bytes_inum (ds : list dirent) (k j : nat) :
  Forall dirent_wf ds -> (k < length ds)%nat -> (j < 2)%nat ->
  dirblk_bytes ds !! (16 * k + j)%nat = Some (nth_byte (de_inum (ds !!! k)) j).
Proof.
  intros Hall Hk Hj.
  rewrite (dirblk_bytes_lookup ds k j Hall Hk ltac:(lia)).
  apply dirent_bytes_inum; exact Hj.
Qed.

Lemma dirblk_bytes_name (ds : list dirent) (k j : nat) :
  Forall dirent_wf ds -> (k < length ds)%nat -> (j < 14)%nat ->
  dirblk_bytes ds !! (16 * k + 2 + j)%nat = de_name (ds !!! k) !! j.
Proof.
  intros Hall Hk Hj.
  replace (16 * k + 2 + j)%nat with (16 * k + (2 + j))%nat by lia.
  rewrite (dirblk_bytes_lookup ds k (2 + j)%nat Hall Hk ltac:(lia)).
  apply dirent_bytes_name.
Qed.

(* ---------------------------------------------------------------------- *)
(* ZERO records: what a bzero'd directory block decodes to.                *)
(* ---------------------------------------------------------------------- *)

Lemma NUL_bv0 : NUL = bv_0 8.
Proof. unfold NUL. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma nth_byte_bv0 {m : N} (j : nat) : nth_byte (bv_0 m) j = NUL.
Proof.
  rewrite NUL_bv0. apply bv_eq.
  rewrite nth_byte_unsigned, !bv_0_unsigned, Z.shiftr_0_l.
  reflexivity.
Qed.

Lemma half_bytes_bv0 : half_bytes (bv_0 16) = [NUL; NUL].
Proof. unfold half_bytes. rewrite !nth_byte_bv0. reflexivity. Qed.

Lemma Forall_replicate_de {A : Type} (P : A -> Prop) (n : nat) (b : A) :
  P b -> Forall P (replicate n b).
Proof.
  intros HP. induction n as [|n IH]; [constructor|].
  simpl. constructor; [exact HP | exact IH].
Qed.

Definition dirent_zero : dirent := MkDirent (bv_0 16) (replicate 14 NUL).

Lemma dirent_zero_wf : dirent_wf dirent_zero.
Proof. unfold dirent_wf, dirent_zero. cbn [de_name]. apply length_replicate. Qed.

Lemma dirent_zero_free : de_free dirent_zero.
Proof. reflexivity. Qed.

Lemma dirent_bytes_zero : dirent_bytes dirent_zero = replicate 16 NUL.
Proof.
  unfold dirent_bytes, dirent_zero. cbn [de_inum de_name].
  rewrite half_bytes_bv0. reflexivity.
Qed.

Lemma dirblk_bytes_replicate (n : nat) :
  dirblk_bytes (replicate n dirent_zero) = replicate (16 * n) NUL.
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite replicate_S, dirblk_bytes_cons, dirent_bytes_zero, IH.
  replace (16 * S n)%nat with (16 + 16 * n)%nat by lia.
  rewrite replicate_add. reflexivity.
Qed.

Definition dirblk_zero : list dirent := replicate 64 dirent_zero.

Lemma dirblk_zero_wf : dirblk_wf dirblk_zero.
Proof.
  unfold dirblk_wf, dirblk_zero. split.
  - apply length_replicate.
  - apply Forall_replicate_de, dirent_zero_wf.
Qed.

Lemma dirblk_bytes_zero : dirblk_bytes dirblk_zero = replicate 1024 NUL.
Proof. unfold dirblk_zero. rewrite dirblk_bytes_replicate. reflexivity. Qed.

(* a free record contributes two zero bytes at its inum, which is exactly what
   dirlookup's [lhu] reads *)
Lemma de_free_inum_bytes (d : dirent) :
  de_free d -> half_bytes (de_inum d) = [NUL; NUL].
Proof. unfold de_free. intros Hd. rewrite Hd. apply half_bytes_bv0. Qed.

(* ---------------------------------------------------------------------- *)
(* THE ENCODING IS INJECTIVE ON WELL-FORMED RECORDS (the §12.3 lesson:      *)
(* provide it before anyone needs it).                                      *)
(* ---------------------------------------------------------------------- *)

(* [InodeRegion.half_bytes_inj] is the same fact, but that file is iris-heavy
   and cannot be imported here; restated, and RENAMED so that importing both
   is never ambiguous. *)
Lemma de_half_bytes_inj (w1 w2 : bv 16) :
  half_bytes w1 = half_bytes w2 -> w1 = w2.
Proof.
  intros H.
  apply (bv_eq_of_bytes (n := 2%N) w1 w2).
  intros j Hj.
  assert (Hj2 : (j < 2)%nat) by lia.
  pose proof (half_bytes_lookup w1 j Hj2) as L1.
  pose proof (half_bytes_lookup w2 j Hj2) as L2.
  rewrite H in L1. rewrite L2 in L1.
  apply (inj Some). exact (eq_sym L1).
Qed.

Lemma dirent_bytes_inj (d1 d2 : dirent) :
  dirent_wf d1 -> dirent_wf d2 ->
  dirent_bytes d1 = dirent_bytes d2 -> d1 = d2.
Proof.
  intros H1 H2 H. unfold dirent_bytes in H.
  apply app_inj_1 in H as [Hin Hnm];
    [| rewrite !half_bytes_length; reflexivity].
  destruct d1, d2; cbn in *.
  f_equal.
  - exact (de_half_bytes_inj _ _ Hin).
  - exact Hnm.
Qed.

Lemma dirblk_bytes_inj_aux (ds1 ds2 : list dirent) :
  length ds1 = length ds2 ->
  Forall dirent_wf ds1 -> Forall dirent_wf ds2 ->
  dirblk_bytes ds1 = dirblk_bytes ds2 -> ds1 = ds2.
Proof.
  revert ds2. induction ds1 as [|d1 ds1 IH]; intros [|d2 ds2] Hlen Hw1 Hw2 H;
    [reflexivity | discriminate | discriminate |].
  inversion Hw1 as [|? ? Hd1 Hds1]; subst.
  inversion Hw2 as [|? ? Hd2 Hds2]; subst.
  rewrite !dirblk_bytes_cons in H.
  apply app_inj_1 in H as [Hd Hds];
    [| rewrite (dirent_bytes_length d1 Hd1), (dirent_bytes_length d2 Hd2);
       reflexivity].
  f_equal.
  - exact (dirent_bytes_inj d1 d2 Hd1 Hd2 Hd).
  - apply IH; [injection Hlen; auto | exact Hds1 | exact Hds2 | exact Hds].
Qed.

Lemma dirblk_bytes_inj (ds1 ds2 : list dirent) :
  dirblk_wf ds1 -> dirblk_wf ds2 ->
  dirblk_bytes ds1 = dirblk_bytes ds2 -> ds1 = ds2.
Proof.
  intros [Hl1 Hw1] [Hl2 Hw2].
  apply dirblk_bytes_inj_aux; [congruence | exact Hw1 | exact Hw2].
Qed.

(* ====================================================================== *)
(*  THE NAME MODEL                                                         *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(* The canonical name of a byte list: the prefix before the first NUL.      *)
(* ---------------------------------------------------------------------- *)

Definition nonul (l : list (bv 8)) : Prop := Forall (fun b => b <> NUL) l.

Fixpoint cut_nul (l : list (bv 8)) : list (bv 8) :=
  match l with
  | [] => []
  | b :: l' => if bool_decide (b = NUL) then [] else b :: cut_nul l'
  end.

Lemma nonul_lookup (l : list (bv 8)) (j : nat) :
  nonul l -> (j < length l)%nat -> l !!! j <> NUL.
Proof.
  intros Hl Hj.
  exact (Forall_lookup_1 (fun b => b <> NUL) l j (l !!! j) Hl
           (list_lookup_lookup_total_lt l j Hj)).
Qed.

Lemma cut_nul_nil : cut_nul [] = [].
Proof. reflexivity. Qed.

Lemma cut_nul_cons_nul (l : list (bv 8)) : cut_nul (NUL :: l) = [].
Proof. simpl. rewrite bool_decide_true by reflexivity. reflexivity. Qed.

Lemma cut_nul_cons_ne (b : bv 8) (l : list (bv 8)) :
  b <> NUL -> cut_nul (b :: l) = b :: cut_nul l.
Proof. intros Hb. simpl. rewrite bool_decide_false by exact Hb. reflexivity. Qed.

Lemma cut_nul_length (l : list (bv 8)) :
  (length (cut_nul l) <= length l)%nat.
Proof.
  induction l as [|b l IH]; [reflexivity|]. simpl.
  destruct (bool_decide (b = NUL)); simpl; lia.
Qed.

Lemma cut_nul_nonul (l : list (bv 8)) : nonul (cut_nul l).
Proof.
  unfold nonul. induction l as [|b l IH]; [constructor|]. simpl.
  destruct (bool_decide (b = NUL)) eqn:Hb; [constructor|].
  apply bool_decide_eq_false in Hb.
  constructor; [exact Hb | exact IH].
Qed.

Lemma cut_nul_lookup (l : list (bv 8)) (j : nat) :
  (j < length (cut_nul l))%nat -> cut_nul l !! j = l !! j.
Proof.
  revert j. induction l as [|b l IH]; intros j Hj; [simpl in Hj; lia|].
  simpl in Hj |- *. destruct (bool_decide (b = NUL)) eqn:Hb.
  - simpl in Hj. lia.
  - destruct j as [|j']; [reflexivity|]. simpl in Hj |- *. apply IH. lia.
Qed.

Lemma cut_nul_stop (l : list (bv 8)) :
  (length (cut_nul l) < length l)%nat -> l !! (length (cut_nul l)) = Some NUL.
Proof.
  induction l as [|b l IH]; intros Hlt; [simpl in Hlt; lia|].
  simpl in Hlt |- *. destruct (bool_decide (b = NUL)) eqn:Hb.
  - apply bool_decide_eq_true in Hb. simpl. rewrite Hb. reflexivity.
  - simpl in Hlt |- *. apply IH. lia.
Qed.

(* the UNIQUENESS law: any index with the two characteristic properties IS
   the canonical length.  This is [ByteBuf.bb_cstr_uniq]'s list-level twin. *)
Lemma cut_nul_length_char (l : list (bv 8)) (k : nat) :
  (k <= length l)%nat ->
  (forall j, (j < k)%nat -> l !! j <> Some NUL) ->
  (k = length l \/ l !! k = Some NUL) ->
  length (cut_nul l) = k.
Proof.
  revert k. induction l as [|b l IH]; intros k Hk Hne Hstop.
  { simpl in Hk |- *. lia. }
  simpl. destruct (bool_decide (b = NUL)) eqn:Hb.
  - apply bool_decide_eq_true in Hb. simpl.
    destruct k as [|k']; [reflexivity|].
    exfalso. apply (Hne 0%nat ltac:(lia)). simpl. rewrite Hb. reflexivity.
  - apply bool_decide_eq_false in Hb.
    destruct k as [|k'].
    { exfalso. destruct Hstop as [Hstop|Hstop].
      - simpl in Hstop. lia.
      - simpl in Hstop. injection Hstop. exact Hb. }
    simpl. f_equal. apply IH.
    + simpl in Hk. lia.
    + intros j Hj. apply (Hne (S j)). lia.
    + destruct Hstop as [Hstop|Hstop].
      * left. simpl in Hstop. lia.
      * right. exact Hstop.
Qed.

(* ...and the lower half of it, which is what the "the names differ" arm of
   the strncmp bridge needs *)
Lemma cut_nul_length_ge (l : list (bv 8)) (k : nat) :
  (k <= length l)%nat ->
  (forall j, (j < k)%nat -> l !! j <> Some NUL) ->
  (k <= length (cut_nul l))%nat.
Proof.
  revert k. induction l as [|b l IH]; intros k Hk Hne; [simpl in Hk; lia|].
  simpl. destruct (bool_decide (b = NUL)) eqn:Hb.
  - apply bool_decide_eq_true in Hb.
    destruct k as [|k']; [lia|].
    exfalso. apply (Hne 0%nat ltac:(lia)). simpl. rewrite Hb. reflexivity.
  - destruct k as [|k']; [lia|]. simpl.
    apply le_n_S, IH.
    + simpl in Hk. lia.
    + intros j Hj. apply (Hne (S j)). lia.
Qed.

Lemma cut_nul_take (l : list (bv 8)) : cut_nul l = take (length (cut_nul l)) l.
Proof.
  apply list_eq. intros j.
  destruct (Nat.lt_ge_cases j (length (cut_nul l))) as [Hj|Hj].
  - rewrite lookup_take by exact Hj. apply cut_nul_lookup, Hj.
  - rewrite lookup_take_ge by exact Hj.
    apply lookup_ge_None_2. exact Hj.
Qed.

Lemma cut_nul_app_drop (l : list (bv 8)) :
  cut_nul l ++ drop (length (cut_nul l)) l = l.
Proof.
  pose proof (take_drop (length (cut_nul l)) l) as H.
  rewrite <- cut_nul_take in H. exact H.
Qed.

Lemma cut_nul_id (l : list (bv 8)) : nonul l -> cut_nul l = l.
Proof.
  unfold nonul. induction 1 as [|b l Hb Hl IH]; [reflexivity|].
  rewrite cut_nul_cons_ne by exact Hb. rewrite IH. reflexivity.
Qed.

Lemma cut_nul_idem (l : list (bv 8)) : cut_nul (cut_nul l) = cut_nul l.
Proof. apply cut_nul_id, cut_nul_nonul. Qed.

Lemma cut_nul_app (l1 l2 : list (bv 8)) :
  nonul l1 -> cut_nul (l1 ++ l2) = l1 ++ cut_nul l2.
Proof.
  unfold nonul. induction 1 as [|b l Hb Hl IH]; [reflexivity|].
  simpl. rewrite bool_decide_false by exact Hb. rewrite IH. reflexivity.
Qed.

Lemma cut_nul_replicate (n : nat) : cut_nul (replicate n NUL) = [].
Proof. destruct n as [|n]; [reflexivity | apply cut_nul_cons_nul]. Qed.

(* ---------------------------------------------------------------------- *)
(* strncpy's image: a name NUL-PADDED to 14 bytes.                         *)
(* ---------------------------------------------------------------------- *)

(* exactly strncpy(dst, s, 14): the first min(14, |s|) bytes of [s], then
   NULs out to 14 -- and NO terminator when [s] is 14 bytes or longer. *)
Definition name_pad (s : list (bv 8)) : list (bv 8) :=
  take 14 s ++ replicate (14 - length s) NUL.

Lemma name_pad_length (s : list (bv 8)) : length (name_pad s) = 14%nat.
Proof.
  unfold name_pad. rewrite length_app, length_take, length_replicate. lia.
Qed.

Lemma name_pad_eq (s : list (bv 8)) :
  (length s <= 14)%nat -> name_pad s = s ++ replicate (14 - length s) NUL.
Proof. intros Hs. unfold name_pad. rewrite take_ge by exact Hs. reflexivity. Qed.

Lemma name_pad_cut (s : list (bv 8)) :
  (length s <= 14)%nat -> nonul s -> cut_nul (name_pad s) = s.
Proof.
  intros Hlen Hs. rewrite name_pad_eq by exact Hlen.
  rewrite cut_nul_app by exact Hs. rewrite cut_nul_replicate.
  apply app_nil_r.
Qed.

(* "once NUL, always NUL": what strncpy leaves behind, stated as a property of
   the STORED bytes rather than of the caller's argument *)
Definition de_padded_l (l : list (bv 8)) : Prop :=
  Forall (fun b => b = NUL) (drop (length (cut_nul l)) l).

Definition de_padded (d : dirent) : Prop := de_padded_l (de_name d).

Lemma Forall_eq_replicate (l : list (bv 8)) (b : bv 8) :
  Forall (fun c => c = b) l -> l = replicate (length l) b.
Proof.
  induction 1 as [|c l Hc Hl IH]; [reflexivity|].
  simpl. rewrite <- IH, Hc. reflexivity.
Qed.

Lemma name_pad_padded (s : list (bv 8)) :
  (length s <= 14)%nat -> nonul s -> de_padded_l (name_pad s).
Proof.
  intros Hlen Hs. unfold de_padded_l.
  rewrite (name_pad_cut s Hlen Hs), (name_pad_eq s Hlen).
  rewrite drop_app_length.
  apply Forall_replicate_de. reflexivity.
Qed.

(* the shape law: a padded 14-byte name IS the padding of its canonical view *)
Lemma de_padded_name_pad (l : list (bv 8)) :
  length l = 14%nat -> de_padded_l l -> l = name_pad (cut_nul l).
Proof.
  intros Hlen Hpad. unfold de_padded_l in Hpad.
  assert (Hk : (length (cut_nul l) <= 14)%nat)
    by (rewrite <- Hlen; apply cut_nul_length).
  assert (Hdrop : drop (length (cut_nul l)) l
                  = replicate (14 - length (cut_nul l)) NUL).
  { rewrite (Forall_eq_replicate _ _ Hpad), length_drop, Hlen. reflexivity. }
  rewrite name_pad_eq by exact Hk.
  rewrite <- Hdrop. symmetry. apply cut_nul_app_drop.
Qed.

(* ...hence canonical equality determines the bytes, which is what makes the
   directory's [name -> inum] view well defined *)
Lemma de_name_faithful (d1 d2 : dirent) :
  dirent_wf d1 -> dirent_wf d2 -> de_padded d1 -> de_padded d2 ->
  cut_nul (de_name d1) = cut_nul (de_name d2) -> de_name d1 = de_name d2.
Proof.
  unfold dirent_wf, de_padded. intros H1 H2 P1 P2 Hc.
  pose proof (de_padded_name_pad _ H1 P1) as E1.
  pose proof (de_padded_name_pad _ H2 P2) as E2.
  rewrite E1, E2, Hc. reflexivity.
Qed.

(* the canonical name of a record, and the record dirlink builds *)
Definition de_name_str (d : dirent) : list (bv 8) := cut_nul (de_name d).

Definition de_of_name (i : bv 16) (s : list (bv 8)) : dirent :=
  MkDirent i (name_pad s).

Lemma de_of_name_wf (i : bv 16) (s : list (bv 8)) : dirent_wf (de_of_name i s).
Proof. unfold dirent_wf, de_of_name. cbn [de_name]. apply name_pad_length. Qed.

Lemma de_of_name_padded (i : bv 16) (s : list (bv 8)) :
  (length s <= 14)%nat -> nonul s -> de_padded (de_of_name i s).
Proof.
  intros Hlen Hs. unfold de_padded, de_of_name. cbn [de_name].
  apply name_pad_padded; assumption.
Qed.

Lemma de_of_name_str (i : bv 16) (s : list (bv 8)) :
  (length s <= 14)%nat -> nonul s -> de_name_str (de_of_name i s) = s.
Proof.
  intros Hlen Hs. unfold de_name_str, de_of_name. cbn [de_name].
  apply name_pad_cut; assumption.
Qed.

(* ---------------------------------------------------------------------- *)
(* The same, over a [ByteBuf] naming function.                             *)
(* ---------------------------------------------------------------------- *)

Definition bview (n : nat) (f : nat -> bv 8) : list (bv 8) := f <$> seq 0 n.

Lemma bview_length (n : nat) (f : nat -> bv 8) : length (bview n f) = n.
Proof. unfold bview. rewrite length_fmap, length_seq. reflexivity. Qed.

Lemma bview_lookup (n : nat) (f : nat -> bv 8) (j : nat) :
  (j < n)%nat -> bview n f !! j = Some (f j).
Proof.
  intros Hj. unfold bview. rewrite list_lookup_fmap, lookup_seq_lt by exact Hj.
  reflexivity.
Qed.

Lemma bview_ext (n : nat) (f g : nat -> bv 8) :
  (forall j, (j < n)%nat -> f j = g j) -> bview n f = bview n g.
Proof.
  intros H. apply list_eq. intros j.
  destruct (Nat.lt_ge_cases j n) as [Hj|Hj].
  - rewrite !bview_lookup by exact Hj. rewrite H by exact Hj. reflexivity.
  - rewrite !lookup_ge_None_2 by (rewrite bview_length; lia). reflexivity.
Qed.

(* the buffer's CANONICAL NAME: the string [strncmp ... n] would see *)
Definition bname (n : nat) (f : nat -> bv 8) : list (bv 8) := cut_nul (bview n f).

Lemma bname_length_le (n : nat) (f : nat -> bv 8) :
  (length (bname n f) <= n)%nat.
Proof.
  unfold bname. pose proof (cut_nul_length (bview n f)) as H.
  rewrite bview_length in H. exact H.
Qed.

Lemma bname_lookup (n : nat) (f : nat -> bv 8) (j : nat) :
  (j < length (bname n f))%nat -> bname n f !! j = Some (f j).
Proof.
  intros Hj. unfold bname. rewrite cut_nul_lookup by exact Hj.
  apply bview_lookup. pose proof (bname_length_le n f). lia.
Qed.

Lemma bname_nonul (n : nat) (f : nat -> bv 8) (j : nat) :
  (j < length (bname n f))%nat -> f j <> NUL.
Proof.
  intros Hj.
  exact (Forall_lookup_1 (fun b => b <> NUL) (bname n f) j (f j)
           (cut_nul_nonul _) (bname_lookup n f j Hj)).
Qed.

Lemma bname_stop (n : nat) (f : nat -> bv 8) :
  (length (bname n f) < n)%nat -> f (length (bname n f)) = NUL.
Proof.
  intros Hlt. unfold bname in *.
  assert (Hlt' : (length (cut_nul (bview n f)) < length (bview n f))%nat)
    by (rewrite bview_length; exact Hlt).
  pose proof (cut_nul_stop (bview n f) Hlt') as H.
  rewrite bview_lookup in H by (rewrite <- bview_length with (f := f); exact Hlt').
  injection H. intros He. exact He.
Qed.

Lemma bname_length_char (n : nat) (f : nat -> bv 8) (k : nat) :
  (k <= n)%nat -> (forall j, (j < k)%nat -> f j <> NUL) ->
  (k = n \/ f k = NUL) -> length (bname n f) = k.
Proof.
  intros Hk Hne Hstop. unfold bname.
  apply cut_nul_length_char.
  - rewrite bview_length. exact Hk.
  - intros j Hj Heq. rewrite bview_lookup in Heq by lia.
    injection Heq. exact (Hne j Hj).
  - destruct (Nat.eq_dec k n) as [Hkn|Hkn].
    + left. rewrite bview_length. exact Hkn.
    + right. rewrite bview_lookup by lia.
      destruct Hstop as [He|He];
        [exfalso; apply Hkn; exact He | rewrite He; reflexivity].
Qed.

Lemma bname_length_ge (n : nat) (f : nat -> bv 8) (k : nat) :
  (k <= n)%nat -> (forall j, (j < k)%nat -> f j <> NUL) ->
  (k <= length (bname n f))%nat.
Proof.
  intros Hk Hne. unfold bname. apply cut_nul_length_ge.
  - rewrite bview_length. exact Hk.
  - intros j Hj Heq. rewrite bview_lookup in Heq by lia.
    injection Heq. exact (Hne j Hj).
Qed.

(* the shape a caller reads off: below the canonical length the buffer IS the
   name, and the canonical length is where the NUL is (or [n]) *)
Lemma bname_char (n : nat) (f : nat -> bv 8) (k : nat) :
  (k <= n)%nat -> (forall j, (j < k)%nat -> f j <> NUL) ->
  (k = n \/ f k = NUL) -> bname n f = bview k f.
Proof.
  intros Hk Hne Hstop.
  pose proof (bname_length_char n f k Hk Hne Hstop) as Hlen.
  apply list_eq. intros j.
  destruct (Nat.lt_ge_cases j k) as [Hj|Hj].
  - rewrite bname_lookup by lia. rewrite bview_lookup by lia. reflexivity.
  - rewrite !lookup_ge_None_2
      by (first [rewrite Hlen | rewrite bview_length]; lia).
    reflexivity.
Qed.

(* a record's 14 bytes, seen as a naming function -- the [g] side of namecmp *)
Lemma bname_of_list (l : list (bv 8)) (n : nat) :
  length l = n -> bname n (fun j => l !!! j) = cut_nul l.
Proof.
  intros Hlen. unfold bname. f_equal.
  apply list_eq. intros j.
  destruct (Nat.lt_ge_cases j n) as [Hj|Hj].
  - rewrite bview_lookup by exact Hj. symmetry.
    apply list_lookup_lookup_total_lt. lia.
  - rewrite !lookup_ge_None_2
      by (first [rewrite bview_length | rewrite Hlen]; lia).
    reflexivity.
Qed.

Lemma de_bname_name (d : dirent) :
  dirent_wf d -> bname 14 (fun j => de_name d !!! j) = de_name_str d.
Proof. intros Hd. unfold de_name_str. apply bname_of_list. exact Hd. Qed.

(* ---------------------------------------------------------------------- *)
(* THE namecmp BRIDGE.                                                      *)
(* ---------------------------------------------------------------------- *)

(* [SpecStrncmp.strncmp_stop] with [bb_nonul] unfolded and the returned word
   dropped: strncmp stopped at index [k]. *)
Definition nc_stop (f g : nat -> bv 8) (n k : nat) : Prop :=
  (k < n)%nat /\
  (forall j, (j < k)%nat -> f j <> NUL) /\
  (forall j, (j < k)%nat -> f j = g j) /\
  (f k = NUL \/ f k <> g k).

(* ...and the other arm of [strncmp_res]: it never stopped. *)
Definition nc_run (f g : nat -> bv 8) (n : nat) : Prop :=
  forall j, (j < n)%nat -> f j = g j /\ f j <> NUL.

Lemma nc_run_bname (f g : nat -> bv 8) (n : nat) :
  nc_run f g n -> bname n f = bname n g.
Proof.
  intros Hrun.
  assert (Hf : forall j, (j < n)%nat -> f j <> NUL)
    by (intros j Hj; destruct (Hrun j Hj) as [_ H]; exact H).
  assert (Hg : forall j, (j < n)%nat -> g j <> NUL).
  { intros j Hj. destruct (Hrun j Hj) as [He Hn]. rewrite <- He. exact Hn. }
  rewrite (bname_char n f n ltac:(lia) Hf (or_introl eq_refl)),
          (bname_char n g n ltac:(lia) Hg (or_introl eq_refl)).
  apply bview_ext. intros j Hj. destruct (Hrun j Hj) as [He _]. exact He.
Qed.

(* THE law namecmp's contract is: at a stop, the returned difference is zero
   exactly when the two canonical names agree. *)
Lemma nc_stop_iff (f g : nat -> bv 8) (n k : nat) :
  nc_stop f g n k -> (f k = g k <-> bname n f = bname n g).
Proof.
  intros (Hkn & Hnonul & Heq & Hstop).
  assert (Hgnonul : forall j, (j < k)%nat -> g j <> NUL).
  { intros j Hj. rewrite <- (Heq j Hj). apply Hnonul, Hj. }
  split.
  - (* equal bytes at the stop: the stop must be a NUL on both sides *)
    intros Hfg.
    assert (Hf : f k = NUL).
    { destruct Hstop as [Hstop|Hstop];
        [exact Hstop | exfalso; apply Hstop; exact Hfg]. }
    assert (Hg : g k = NUL) by (rewrite <- Hfg; exact Hf).
    rewrite (bname_char n f k ltac:(lia) Hnonul (or_intror Hf)).
    rewrite (bname_char n g k ltac:(lia) Hgnonul (or_intror Hg)).
    apply bview_ext. exact Heq.
  - (* conversely: differing bytes make the canonical names differ *)
    intros Hbn.
    destruct (decide (f k = g k)) as [Hfg|Hfg]; [exact Hfg | exfalso].
    destruct (decide (f k = NUL)) as [Hf|Hf].
    + (* f stops here, g does not *)
      assert (Hg : g k <> NUL)
        by (rewrite <- Hf; intros Hc; apply Hfg; symmetry; exact Hc).
      pose proof (bname_length_char n f k ltac:(lia) Hnonul (or_intror Hf)) as HLf.
      assert (HLg : (S k <= length (bname n g))%nat).
      { apply bname_length_ge; [lia|]. intros j Hj.
        destruct (Nat.lt_ge_cases j k) as [Hjk|Hjk];
          [ apply Hgnonul, Hjk
          | assert (Hje : j = k) by lia; rewrite Hje; exact Hg ]. }
      rewrite Hbn in HLf. lia.
    + (* f does not stop with a NUL, so it stopped on a difference *)
      assert (HLf : (S k <= length (bname n f))%nat).
      { apply bname_length_ge; [lia|]. intros j Hj.
        destruct (Nat.lt_ge_cases j k) as [Hjk|Hjk];
          [ apply Hnonul, Hjk
          | assert (Hje : j = k) by lia; rewrite Hje; exact Hf ]. }
      destruct (decide (g k = NUL)) as [Hg|Hg].
      * pose proof (bname_length_char n g k ltac:(lia) Hgnonul (or_intror Hg)) as HLg.
        rewrite Hbn in HLf. lia.
      * assert (HLg : (S k <= length (bname n g))%nat).
        { apply bname_length_ge; [lia|]. intros j Hj.
          destruct (Nat.lt_ge_cases j k) as [Hjk|Hjk];
            [ apply Hgnonul, Hjk
            | assert (Hje : j = k) by lia; rewrite Hje; exact Hg ]. }
        pose proof (bname_lookup n f k ltac:(lia)) as Lf.
        pose proof (bname_lookup n g k ltac:(lia)) as Lg.
        rewrite Hbn, Lg in Lf. apply Hfg. injection Lf. intros He.
        symmetry. exact He.
Qed.

(* THE top-level bridge: "namecmp returned 0" IS "the canonical names agree".
   Note there is NO padding or well-formedness hypothesis on either side --
   strncmp never looks past the first NUL, so the equivalence is honest for
   namex's UNPADDED buffer as well as for a dirent's padded field. *)
Lemma nc_zero_iff (f g : nat -> bv 8) (n : nat) :
  ((exists k, nc_stop f g n k /\ f k = g k) \/ nc_run f g n)
  <-> bname n f = bname n g.
Proof.
  split.
  - intros [[k [Hst Hfg]] | Hrun].
    + apply (nc_stop_iff f g n k Hst). exact Hfg.
    + apply nc_run_bname. exact Hrun.
  - intros Hbn.
    assert (Hnonul : forall j, (j < length (bname n f))%nat -> f j <> NUL)
      by (intros j Hj; exact (bname_nonul n f j Hj)).
    assert (Heq : forall j, (j < length (bname n f))%nat -> f j = g j).
    { intros j Hj.
      pose proof (bname_lookup n f j Hj) as Lf.
      assert (Hj' : (j < length (bname n g))%nat) by (rewrite <- Hbn; exact Hj).
      pose proof (bname_lookup n g j Hj') as Lg.
      rewrite Hbn, Lg in Lf. injection Lf. intros He. symmetry. exact He. }
    destruct (Nat.lt_ge_cases (length (bname n f)) n) as [Hlt|Hge].
    + (* the first NUL of [f] is at [length (bname n f)]: that is the stop *)
      left. exists (length (bname n f)).
      pose proof (bname_stop n f Hlt) as Hf.
      assert (Hg : g (length (bname n f)) = NUL).
      { destruct (decide (g (length (bname n f)) = NUL)) as [Hg|Hg];
          [exact Hg | exfalso].
        assert (HLg : (S (length (bname n f)) <= length (bname n g))%nat).
        { apply bname_length_ge; [lia|]. intros j Hj.
          destruct (Nat.lt_ge_cases j (length (bname n f))) as [Hjk|Hjk].
          - rewrite <- (Heq j Hjk). apply Hnonul, Hjk.
          - assert (Hje : j = length (bname n f)) by lia.
            rewrite Hje. exact Hg. }
        rewrite <- Hbn in HLg. lia. }
      split.
      * split; [exact Hlt |]. split; [exact Hnonul |].
        split; [exact Heq | left; exact Hf].
      * rewrite Hf, Hg. reflexivity.
    + (* no NUL below [n] at all: strncmp ran to the end *)
      right. intros j Hj.
      assert (Hjl : (j < length (bname n f))%nat)
        by (pose proof (bname_length_le n f); lia).
      split; [exact (Heq j Hjl) | exact (Hnonul j Hjl)].
Qed.

(* namecmp's contract, at the width the code uses.  [f] is the SEARCH name
   (dirlookup passes [name] in a0), [g] the record's field (a1). *)
Lemma namecmp_bridge (f : nat -> bv 8) (d : dirent) :
  dirent_wf d ->
  (((exists k, nc_stop f (fun j => de_name d !!! j) 14 k
               /\ f k = de_name d !!! k)
    \/ nc_run f (fun j => de_name d !!! j) 14)
   <-> bname 14 f = de_name_str d).
Proof.
  intros Hd. rewrite <- (de_bname_name d Hd). apply nc_zero_iff.
Qed.

(* the buffer shape skipelem's two branches leave behind: a name shorter than
   14 terminated by a NUL, or exactly 14 bytes with no terminator at all.
   Either way the canonical view is the element. *)
Lemma bname_of_buf (f : nat -> bv 8) (e : list (bv 8)) :
  (length e <= 14)%nat -> nonul e ->
  (forall j, (j < length e)%nat -> f j = e !!! j) ->
  ((length e < 14)%nat -> f (length e) = NUL) ->
  bname 14 f = e.
Proof.
  intros Hlen Hne Hf Hstop.
  assert (Hne' : forall j, (j < length e)%nat -> f j <> NUL).
  { intros j Hj. rewrite (Hf j Hj). apply nonul_lookup; assumption. }
  rewrite (bname_char 14 f (length e) Hlen Hne').
  2:{ destruct (decide (length e = 14%nat)) as [He14|He14];
      [ left; exact He14 | right; apply Hstop; lia ]. }
  apply list_eq. intros j.
  destruct (Nat.lt_ge_cases j (length e)) as [Hj|Hj].
  - rewrite bview_lookup by exact Hj. rewrite (Hf j Hj). symmetry.
    apply list_lookup_lookup_total_lt. exact Hj.
  - rewrite !lookup_ge_None_2 by (first [rewrite bview_length | idtac]; lia).
    reflexivity.
Qed.
