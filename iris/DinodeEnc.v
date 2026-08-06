(* DinodeEnc.v -- the ON-DISK inode: [struct dinode], its 64-byte encoding,
   and the sixteen of them that fill one block.

   The counterpart of [BlockWords.v] one level up: that file reads a block
   as 256 little-endian [uint]s, this one reads it as IPB = 16 records.
   Same discipline, and it is the point of both -- the block's content is
   always kept in the IMAGE of an encoding function over a list of PURE
   records, so an update is an [<[k := d]>] on that list and the byte level
   is only ever READ BACK.  Nothing below ever has to exhibit a byte list.

     dinode_bytes d   64 bytes:  type@0 major@2 minor@4 nlink@6
                                 size@8 addrs@12 (13 words, 52 bytes)
     diblk_bytes ds   the sixteen in order = 1024 bytes = BSIZE

   THE GEOMETRY IS READ OFF iupdate's STORES, not off fs.h (the same rule
   [InodeInv.v] states for the in-memory [struct inode]):

     sh a4,0(a5)   after  lh a4,68(s1)   ==>  type  at +0  (inode +68)
     sh ...,2/4/6(a5)                    ==>  major +2, minor +4, nlink +6
     sw a4,8(a5)   after  lw a4,76(s1)   ==>  size  at +8
     addi a0,a5,12 / li a2,52            ==>  addrs at +12, 52 bytes
     andi a4,a4,15 ; slli a4,a4,0x6      ==>  slot = (inum & 15) * 64,
                                              i.e. IPB = 16

   THE BYTE SPLITTER IS THE TREE'S EXISTING [RiscvModelBytes.nth_byte],
   which is width-generic over [bv m] -- so the four 16-bit fields need no
   new splitter, only a two-element [half_bytes] beside [BlockWords]'
   four-element [word_bytes].  The addrs array IS [BlockWords.ind_bytes]
   at thirteen entries; there is deliberately no second little-endian
   word-array encoder.

   [dinode_wf] (the addrs list really has NDIRECT+1 = 13 entries) is a
   premise rather than a [resize] baked into the encoder: with it every law
   below is an equality between the two natural terms, and a caller gets it
   for free from [InodeInv.bm_cells]'s length.

   iris-FREE (no proofmode, no ssreflect), like [BlockWords.v], so it stays
   usable from the vanilla-[rewrite ... by ...] files -- which is also why
   every rewrite below is comma-separated and every side condition is
   discharged with [by]. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import RiscvModelBytes.
Require Import BlockWords.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The record, and the block geometry.                                     *)
(* ---------------------------------------------------------------------- *)

Record dinode := MkDinode {
  di_type  : bv 16;
  di_major : bv 16;
  di_minor : bv 16;
  di_nlink : bv 16;
  di_size  : bv 32;
  di_addrs : list (bv 32);   (* NDIRECT + 1 = 13 entries *)
}.

(* [!!!] over a [list dinode] needs a default; nothing below ever reads it
   (every lookup is guarded by [k < length ds]). *)
Global Instance dinode_inhabited : Inhabited dinode :=
  populate (MkDinode (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 32) []).

Definition IPB : nat := 16%nat.            (* BSIZE / sizeof(struct dinode) *)
Definition DISIZE : nat := 64%nat.         (* sizeof(struct dinode) *)
(* NOTE: every law below is stated with the LITERALS 64 and 16, never with
   [DISIZE]/[IPB]: a consumer's offsets come out of the instruction stream as
   literals, and a [rewrite] against a folded constant does not match. *)

(* IBLOCK(i, sb) = i / IPB + sb.inodestart, and the slot inside it.  The
   code computes the first as [srliw a5,a5,0x4] then [addw], the second as
   [andi a4,a4,15] then [slli a4,a4,0x6]. *)
Definition IBLOCK (inum : bv 32) (inodestart : Z) : Z :=
  bv_unsigned inum / 16 + inodestart.
Definition islot (inum : bv 32) : nat :=
  Z.to_nat (bv_unsigned inum `mod` 16).

Lemma islot_lt (inum : bv 32) : (islot inum < 16)%nat.
Proof.
  unfold islot.
  pose proof (Z.mod_pos_bound (bv_unsigned inum) 16 ltac:(lia)) as [H1 H2]. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The encoding.                                                           *)
(* ---------------------------------------------------------------------- *)

(* one 16-bit field, little-endian.  [nth_byte] is width-generic, so this
   is the [BlockWords.word_bytes] pattern at two bytes instead of four. *)
Definition half_bytes (w : bv 16) : list (bv 8) :=
  [nth_byte w 0%nat; nth_byte w 1%nat].

Definition dinode_bytes (d : dinode) : list (bv 8) :=
  (half_bytes (di_type d) ++ half_bytes (di_major d)
   ++ half_bytes (di_minor d) ++ half_bytes (di_nlink d)
   ++ word_bytes (di_size d) ++ ind_bytes (di_addrs d))%list.

Fixpoint diblk_bytes (ds : list dinode) : list (bv 8) :=
  match ds with
  | [] => []
  | d :: ds' => (dinode_bytes d ++ diblk_bytes ds')%list
  end.

Definition dinode_wf (d : dinode) : Prop := length (di_addrs d) = 13%nat.
Definition diblk_wf (ds : list dinode) : Prop :=
  length ds = 16%nat /\ Forall dinode_wf ds.

Lemma diblk_bytes_nil : diblk_bytes [] = [].
Proof. reflexivity. Qed.

Lemma diblk_bytes_cons (d : dinode) (ds : list dinode) :
  diblk_bytes (d :: ds) = (dinode_bytes d ++ diblk_bytes ds)%list.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* One record: length, and the six field readings.                         *)
(* ---------------------------------------------------------------------- *)

Lemma half_bytes_length (w : bv 16) : length (half_bytes w) = 2%nat.
Proof. reflexivity. Qed.

Lemma half_bytes_lookup (w : bv 16) (j : nat) :
  (j < 2)%nat -> half_bytes w !! j = Some (nth_byte w j).
Proof. intros Hj. destruct j as [|[|j]]; [reflexivity|reflexivity|exfalso; lia]. Qed.

(* The two [ind_bytes] cons readings the addrs-cells bridge
   ([InodeInv.ia_cells_bytes]) peels a word run with.  They belong beside
   [BlockWords]' own [ind_bytes_*] laws, but that file is frozen under the
   rest of the tree; here is the next-best home, since this is the file
   that reuses [ind_bytes] as the [addrs] field encoder. *)
Lemma ind_bytes_cons_lo (w : bv 32) (l : list (bv 32)) (i : nat) :
  (i < 4)%nat -> ind_bytes (w :: l) !!! i = nth_byte w i.
Proof.
  intros Hi. rewrite ind_bytes_cons.
  apply list_lookup_total_correct.
  rewrite lookup_app_l by (rewrite word_bytes_length; lia).
  apply word_bytes_lookup; exact Hi.
Qed.

Lemma ind_bytes_cons_hi (w : bv 32) (l : list (bv 32)) (i : nat) :
  ind_bytes (w :: l) !!! (4 + i)%nat = ind_bytes l !!! i.
Proof.
  rewrite ind_bytes_cons, !list_lookup_total_alt.
  rewrite lookup_app_r by (rewrite word_bytes_length; lia).
  rewrite word_bytes_length. replace (4 + i - 4)%nat with i by lia. reflexivity.
Qed.

Lemma dinode_bytes_length (d : dinode) :
  dinode_wf d -> length (dinode_bytes d) = 64%nat.
Proof.
  unfold dinode_wf, dinode_bytes. intros Hd.
  rewrite !length_app, !half_bytes_length, word_bytes_length,
    ind_bytes_length, Hd.
  reflexivity.
Qed.

(* the six readings, each stated at the offset the corresponding store
   uses.  Written with [!!] so a total-lookup form follows by
   [list_lookup_total_correct]. *)
Lemma dinode_bytes_type (d : dinode) (j : nat) :
  (j < 2)%nat -> dinode_bytes d !! j = Some (nth_byte (di_type d) j).
Proof.
  intros Hj. unfold dinode_bytes.
  rewrite lookup_app_l by (rewrite half_bytes_length; lia).
  apply half_bytes_lookup; exact Hj.
Qed.

Lemma dinode_bytes_major (d : dinode) (j : nat) :
  (j < 2)%nat -> dinode_bytes d !! (2 + j)%nat = Some (nth_byte (di_major d) j).
Proof.
  intros Hj. unfold dinode_bytes.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length.
  replace (2 + j - 2)%nat with j by lia.
  rewrite lookup_app_l by (rewrite half_bytes_length; lia).
  apply half_bytes_lookup; exact Hj.
Qed.

Lemma dinode_bytes_minor (d : dinode) (j : nat) :
  (j < 2)%nat -> dinode_bytes d !! (4 + j)%nat = Some (nth_byte (di_minor d) j).
Proof.
  intros Hj. unfold dinode_bytes.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length. replace (4 + j - 2)%nat with (2 + j)%nat by lia.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length. replace (2 + j - 2)%nat with j by lia.
  rewrite lookup_app_l by (rewrite half_bytes_length; lia).
  apply half_bytes_lookup; exact Hj.
Qed.

Lemma dinode_bytes_nlink (d : dinode) (j : nat) :
  (j < 2)%nat -> dinode_bytes d !! (6 + j)%nat = Some (nth_byte (di_nlink d) j).
Proof.
  intros Hj. unfold dinode_bytes.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length. replace (6 + j - 2)%nat with (4 + j)%nat by lia.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length. replace (4 + j - 2)%nat with (2 + j)%nat by lia.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length. replace (2 + j - 2)%nat with j by lia.
  rewrite lookup_app_l by (rewrite half_bytes_length; lia).
  apply half_bytes_lookup; exact Hj.
Qed.

Lemma dinode_bytes_size (d : dinode) (j : nat) :
  (j < 4)%nat -> dinode_bytes d !! (8 + j)%nat = Some (nth_byte (di_size d) j).
Proof.
  intros Hj. unfold dinode_bytes.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length. replace (8 + j - 2)%nat with (6 + j)%nat by lia.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length. replace (6 + j - 2)%nat with (4 + j)%nat by lia.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length. replace (4 + j - 2)%nat with (2 + j)%nat by lia.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length. replace (2 + j - 2)%nat with j by lia.
  rewrite lookup_app_l by (rewrite word_bytes_length; lia).
  apply word_bytes_lookup; exact Hj.
Qed.

Lemma dinode_bytes_addrs (d : dinode) (j : nat) :
  dinode_bytes d !! (12 + j)%nat = ind_bytes (di_addrs d) !! j.
Proof.
  unfold dinode_bytes.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length. replace (12 + j - 2)%nat with (10 + j)%nat by lia.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length. replace (10 + j - 2)%nat with (8 + j)%nat by lia.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length. replace (8 + j - 2)%nat with (6 + j)%nat by lia.
  rewrite lookup_app_r by (rewrite half_bytes_length; lia).
  rewrite half_bytes_length. replace (6 + j - 2)%nat with (4 + j)%nat by lia.
  rewrite lookup_app_r by (rewrite word_bytes_length; lia).
  rewrite word_bytes_length. replace (4 + j - 4)%nat with j by lia.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The block: length, slot lookup, and one-slot installation.              *)
(* ---------------------------------------------------------------------- *)

Lemma diblk_bytes_length (ds : list dinode) :
  Forall dinode_wf ds -> length (diblk_bytes ds) = (64 * length ds)%nat.
Proof.
  induction ds as [|d ds IH]; intros Hall; [reflexivity|].
  inversion Hall as [|xd xds Hd Hds]; subst.
  rewrite diblk_bytes_cons, length_app, (dinode_bytes_length d Hd), (IH Hds).
  simpl length. lia.
Qed.

Lemma diblk_bytes_length_16 (ds : list dinode) :
  diblk_wf ds -> length (diblk_bytes ds) = 1024%nat.
Proof.
  intros [Hlen Hall]. rewrite (diblk_bytes_length ds Hall), Hlen. reflexivity.
Qed.

Lemma diblk_bytes_lookup (ds : list dinode) (k j : nat) :
  Forall dinode_wf ds -> (k < length ds)%nat -> (j < 64)%nat ->
  diblk_bytes ds !! (64 * k + j)%nat = dinode_bytes (ds !!! k) !! j.
Proof.
  revert k. induction ds as [|d ds IH]; intros k Hall Hk Hj.
  { simpl length in Hk. exfalso; lia. }
  inversion Hall as [|xd xds Hd Hds]; subst.
  simpl length in Hk. rewrite diblk_bytes_cons.
  destruct k as [|k'].
  - replace (64 * 0 + j)%nat with j by lia.
    rewrite lookup_app_l by (rewrite (dinode_bytes_length d Hd); lia).
    reflexivity.
  - replace (64 * S k' + j)%nat with (64 + (64 * k' + j))%nat by lia.
    rewrite lookup_app_r by (rewrite (dinode_bytes_length d Hd); lia).
    rewrite (dinode_bytes_length d Hd).
    replace (64 + (64 * k' + j) - 64)%nat
      with (64 * k' + j)%nat by lia.
    rewrite (IH k' Hds ltac:(lia) Hj). reflexivity.
Qed.

Lemma diblk_bytes_lookup_None (ds : list dinode) (i : nat) :
  Forall dinode_wf ds -> (64 * length ds <= i)%nat ->
  diblk_bytes ds !! i = None.
Proof.
  intros Hall Hi. apply lookup_ge_None_2.
  rewrite (diblk_bytes_length ds Hall). lia.
Qed.

Lemma dinode_wf_insert (ds : list dinode) (k : nat) (d : dinode) :
  Forall dinode_wf ds -> dinode_wf d -> Forall dinode_wf (<[k := d]> ds).
Proof. intros Hall Hd. apply Forall_insert; [exact Hall | exact Hd]. Qed.

Lemma diblk_wf_insert (ds : list dinode) (k : nat) (d : dinode) :
  diblk_wf ds -> dinode_wf d -> diblk_wf (<[k := d]> ds).
Proof.
  intros [Hlen Hall] Hd. split.
  - rewrite length_insert. exact Hlen.
  - apply dinode_wf_insert; assumption.
Qed.

Lemma diblk_bytes_insert_same (ds : list dinode) (k : nat) (d : dinode) (j : nat) :
  Forall dinode_wf ds -> dinode_wf d -> (k < length ds)%nat -> (j < 64)%nat ->
  diblk_bytes (<[k := d]> ds) !! (64 * k + j)%nat = dinode_bytes d !! j.
Proof.
  intros Hall Hd Hk Hj.
  rewrite (diblk_bytes_lookup (<[k := d]> ds) k j
             (dinode_wf_insert ds k d Hall Hd)
             ltac:(rewrite length_insert; exact Hk) Hj).
  rewrite list_lookup_total_insert by exact Hk. reflexivity.
Qed.

Lemma diblk_bytes_insert_other (ds : list dinode) (k : nat) (d : dinode) (i : nat) :
  Forall dinode_wf ds -> dinode_wf d -> (k < length ds)%nat ->
  (i < 64 * k \/ 64 * k + 64 <= i)%nat ->
  diblk_bytes (<[k := d]> ds) !! i = diblk_bytes ds !! i.
Proof.
  intros Hall Hd Hk Hi.
  pose proof (dinode_wf_insert ds k d Hall Hd) as Hall'.
  destruct (Nat.lt_ge_cases i (64 * length ds)) as [Hlt|Hge].
  - (* inside the image: both sides are record [i / 64]'s byte [i mod 64] *)
    pose proof (Nat.div_mod_eq i 64) as Hi4.
    assert (Hr : (i `mod` 64 < 64)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (Hq : (i `div` 64 < length ds)%nat) by nia.
    assert (Hqi : (i `div` 64 <> k)%nat) by nia.
    remember (i `div` 64)%nat as q eqn:Hq'.
    remember (i `mod` 64)%nat as r eqn:Hr'.
    clear Hq' Hr'. subst i.
    rewrite (diblk_bytes_lookup (<[k := d]> ds) q r Hall'
               ltac:(rewrite length_insert; exact Hq) Hr).
    rewrite (diblk_bytes_lookup ds q r Hall Hq Hr).
    rewrite list_lookup_total_insert_ne by lia. reflexivity.
  - (* past the image: both sides are None *)
    rewrite (diblk_bytes_lookup_None (<[k := d]> ds) i Hall'
               ltac:(rewrite length_insert; exact Hge)).
    rewrite (diblk_bytes_lookup_None ds i Hall Hge). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The same six readings in TOTAL-lookup form.  A [ByteBuf] window is named *)
(* by a FUNCTION, so every consumer wants [!!!], not [!!].                  *)
(* ---------------------------------------------------------------------- *)

Lemma dinode_bytes_type_t (d : dinode) (j : nat) :
  (j < 2)%nat -> dinode_bytes d !!! j = nth_byte (di_type d) j.
Proof. intros Hj. apply list_lookup_total_correct, dinode_bytes_type, Hj. Qed.

Lemma dinode_bytes_major_t (d : dinode) (j : nat) :
  (j < 2)%nat -> dinode_bytes d !!! (2 + j)%nat = nth_byte (di_major d) j.
Proof. intros Hj. apply list_lookup_total_correct, dinode_bytes_major, Hj. Qed.

Lemma dinode_bytes_minor_t (d : dinode) (j : nat) :
  (j < 2)%nat -> dinode_bytes d !!! (4 + j)%nat = nth_byte (di_minor d) j.
Proof. intros Hj. apply list_lookup_total_correct, dinode_bytes_minor, Hj. Qed.

Lemma dinode_bytes_nlink_t (d : dinode) (j : nat) :
  (j < 2)%nat -> dinode_bytes d !!! (6 + j)%nat = nth_byte (di_nlink d) j.
Proof. intros Hj. apply list_lookup_total_correct, dinode_bytes_nlink, Hj. Qed.

Lemma dinode_bytes_size_t (d : dinode) (j : nat) :
  (j < 4)%nat -> dinode_bytes d !!! (8 + j)%nat = nth_byte (di_size d) j.
Proof. intros Hj. apply list_lookup_total_correct, dinode_bytes_size, Hj. Qed.

Lemma dinode_bytes_addrs_t (d : dinode) (j : nat) :
  dinode_bytes d !!! (12 + j)%nat = ind_bytes (di_addrs d) !!! j.
Proof.
  rewrite !list_lookup_total_alt, dinode_bytes_addrs. reflexivity.
Qed.

(* slot [k]'s bytes, in the [!!!] form a [ByteBuf] naming function takes *)
Lemma diblk_wf_slot (ds : list dinode) (k : nat) :
  Forall dinode_wf ds -> (k < length ds)%nat -> dinode_wf (ds !!! k).
Proof.
  intros Hall Hk. eapply Forall_lookup_1; [exact Hall |].
  apply list_lookup_lookup_total_lt; exact Hk.
Qed.

Lemma diblk_bytes_lookup_t (ds : list dinode) (k j : nat) :
  Forall dinode_wf ds -> (k < length ds)%nat -> (j < 64)%nat ->
  diblk_bytes ds !!! (64 * k + j)%nat = dinode_bytes (ds !!! k) !!! j.
Proof.
  intros Hall Hk Hj. apply list_lookup_total_correct.
  rewrite (diblk_bytes_lookup ds k j Hall Hk Hj).
  apply list_lookup_lookup_total_lt.
  rewrite (dinode_bytes_length (ds !!! k) (diblk_wf_slot ds k Hall Hk)). lia.
Qed.

Lemma diblk_bytes_insert_same_t (ds : list dinode) (k : nat) (d : dinode) (j : nat) :
  Forall dinode_wf ds -> dinode_wf d -> (k < length ds)%nat -> (j < 64)%nat ->
  diblk_bytes (<[k := d]> ds) !!! (64 * k + j)%nat = dinode_bytes d !!! j.
Proof.
  intros Hall Hd Hk Hj. apply list_lookup_total_correct.
  rewrite (diblk_bytes_insert_same ds k d j Hall Hd Hk Hj).
  apply list_lookup_lookup_total_lt.
  rewrite (dinode_bytes_length d Hd). lia.
Qed.

Lemma diblk_bytes_insert_other_t (ds : list dinode) (k : nat) (d : dinode) (i : nat) :
  Forall dinode_wf ds -> dinode_wf d -> (k < length ds)%nat ->
  (i < 64 * k \/ 64 * k + 64 <= i)%nat ->
  diblk_bytes (<[k := d]> ds) !!! i = diblk_bytes ds !!! i.
Proof.
  intros Hall Hd Hk Hi.
  rewrite !list_lookup_total_alt, (diblk_bytes_insert_other ds k d i Hall Hd Hk Hi).
  reflexivity.
Qed.
