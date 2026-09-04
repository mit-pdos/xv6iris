(* ElfBridge.v -- the CODE side of the ELF readers meets the FILE side.

   [ElfEnc.v] is what kexec's two stack buffers say ([le_at f o n] over a
   buffer naming function [f : nat -> bv 8]); [ElfFile.v] is what the file
   the process [readi]s says ([elf_le_at l o n] over the byte list [l]).
   [ElfFile.v]'s header promises that the two "agree on layout and disagree
   only in width, by design", and that under the truncation bounds the
   bridge is "a one-line congruence through [ElfEnc.le_at_ext]".  This file
   is that congruence, plus the inversions of [elf_parse_ehdr] /
   [elf_parse_phdr] / [elf_table] that turn a parsed record's FIELD back
   into the [elf_le_at] the congruence lands on.

   WHAT THE EXEC PROOF ACTUALLY HOLDS.  kexec reads the file with [readi],
   whose postcondition names each delivered byte [rd_delivered data olds
   off tot j], which below [tot] is [InodeDefs.file_byte data (off + j)]
   ([SpecReadi.rd_delivered_bytes]).  The observation the AU delivers
   carries [AFile (fn_file_bytes (era_node dn bm data))], and
   [fn_file_bytes] is [FsTree.file_bytes data (Z.to_nat (fn_size n))].
   So the missing pure link is index-by-index: [file_bytes]'s [!!!] at [k]
   IS [file_byte] at [k], below the size ([file_bytes_lookup]).  The two
   halves compose into [le_at_of_file_bytes], which is the shape a proof
   with a [readi]-filled buffer wants.  (The [era] half --
   [fn_data (era_node dn bm data) = data] under [blk_holes_zero] -- lives
   in [FsStateEra.era_node_data] and cannot be restated here: it is an
   iris file.)

   THE TWO TRUNCATIONS ARE THE ONLY REAL CONTENT.  [eh_phoff] and [ph_off]
   are FOUR-byte loads of EIGHT-byte fields (the C assigns a [uint64] to an
   [int]), so they equal [ee_phoff] / [ep_offset] only under the bounds
   [SpecKexecAU.kexec_loadable] carries ([< 2 ^ 31]).  Every such lemma
   below therefore states its bound as a hypothesis rather than hiding it;
   [elf_le_at_trunc] is where the arithmetic happens, once.

   iris-FREE (no proofmode, no ssreflect), like [ElfEnc.v] and
   [ElfFile.v], so vanilla [rewrite ... by ...] stays available. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap.
From stdpp Require Import bitvector.definitions.
Require Import RiscvModelBytes.
Require Import ElfEnc.
Require Import ElfFile.
Require Import InodeDefs.      (* [file_byte]                              *)
Require Import FsTree.         (* [file_bytes] -- [fn_file_bytes]'s body   *)

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE CONGRUENCE: a buffer that MIRRORS a window of the file        *)
(* ====================================================================== *)

(* The buffer [g] was filled from the file at file offset [base]: byte [j]
   of [g] is byte [base + j] of [l].  Then every [le_at] on [g] is the
   [elf_le_at] on [l] shifted by [base].  No length side condition: both
   readers are TOTAL ([!!!] returns the inhabitant out of range), so only
   the bytes the hypothesis covers can matter. *)
Lemma le_at_shift_of_list (g : nat -> bv 8) (l : elf_bytes) (base o n : nat) :
  (forall j, (j < n)%nat -> g (o + j)%nat = l !!! (base + o + j)%nat) ->
  le_at g o n = elf_le_at l (base + o) n.
Proof.
  intros H. unfold le_at, elf_le_at. f_equal.
  rewrite !map_eq_fmap. apply list_eq. intros k.
  destruct (Nat.lt_ge_cases k n) as [Hk|Hk].
  - rewrite !list_lookup_fmap, lookup_seq_lt by exact Hk. simpl.
    rewrite H by exact Hk. reflexivity.
  - rewrite !list_lookup_fmap.
    rewrite lookup_ge_None_2 by (rewrite length_seq; lia). reflexivity.
Qed.

(* the [base = 0] instance: the buffer IS the front of the file *)
Lemma le_at_of_list (g : nat -> bv 8) (l : elf_bytes) (o n : nat) :
  (forall j, (j < n)%nat -> g (o + j)%nat = l !!! (o + j)%nat) ->
  le_at g o n = elf_le_at l o n.
Proof. intros H. exact (le_at_shift_of_list g l 0 o n H). Qed.

(* ...and the form a "the buffer agrees with the file below [m]" hypothesis
   (which is how a [readi] postcondition reads) is used at. *)
Lemma le_at_of_list_below (g : nat -> bv 8) (l : elf_bytes) (o n m : nat) :
  (o + n <= m)%nat ->
  (forall j, (j < m)%nat -> g j = l !!! j) ->
  le_at g o n = elf_le_at l o n.
Proof. intros Hm H. apply le_at_of_list. intros j Hj. apply H. lia. Qed.

(* ====================================================================== *)
(*  2.  TRUNCATION: an [m]-byte read of an [n]-byte field                  *)
(* ====================================================================== *)

Lemma elf_le_at_bound (l : elf_bytes) (o n : nat) :
  0 <= elf_le_at l o n < 2 ^ (8 * Z.of_nat n).
Proof.
  unfold elf_le_at.
  pose proof (assemble_bytes_bound
                (map (fun j => l !!! (o + j)%nat) (seq 0 n))) as H.
  rewrite elf_le_bytes_length in H. exact H.
Qed.

(* the low [k] bytes of a little-endian list are the value mod 2^(8k) *)
Lemma assemble_bytes_take (bs : list (bv 8)) (k : nat) :
  assemble_bytes (take k bs) = assemble_bytes bs `mod` 2 ^ (8 * Z.of_nat k).
Proof.
  revert k. induction bs as [|b bs IH]; intros k.
  - rewrite take_nil. simpl assemble_bytes.
    rewrite Z.mod_0_l; [reflexivity|].
    apply Z.pow_nonzero; [lia|lia].
  - destruct k as [|k].
    + simpl. rewrite Z.mod_1_r. reflexivity.
    + simpl take. simpl assemble_bytes. rewrite IH.
      assert (HM : 0 < 2 ^ (8 * Z.of_nat k))
        by (apply Z.pow_pos_nonneg; lia).
      assert (Hpow : 2 ^ (8 * Z.of_nat (S k)) = 256 * 2 ^ (8 * Z.of_nat k)).
      { replace 256 with (2 ^ 8) by reflexivity.
        rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      assert (H8 : (2:Z) ^ 8 = 256) by reflexivity.
      rewrite Hpow, H8.
      pose proof (bv_unsigned_in_range 8 b) as [Hb0 Hb1].
      change (bv_modulus 8) with 256 in Hb1.
      assert (Hsplit : forall a r,
                 assemble_bytes bs = 2 ^ (8 * Z.of_nat k) * a + r ->
                 bv_unsigned b + 256 * assemble_bytes bs
                 = (bv_unsigned b + 256 * r) + a * (256 * 2 ^ (8 * Z.of_nat k))).
      { intros a r Hr. rewrite Hr. ring. }
      rewrite (Hsplit (assemble_bytes bs `div` 2 ^ (8 * Z.of_nat k))
                      (assemble_bytes bs `mod` 2 ^ (8 * Z.of_nat k)))
        by (apply Z.div_mod; lia).
      rewrite Z.mod_add by lia.
      symmetry. apply Z.mod_small.
      pose proof (Z.mod_pos_bound (assemble_bytes bs)
                    (2 ^ (8 * Z.of_nat k)) HM) as [Hr0 Hr1].
      lia.
Qed.

Lemma elf_le_bytes_take (l : elf_bytes) (o m n : nat) :
  (m <= n)%nat ->
  map (fun j => l !!! (o + j)%nat) (seq 0 m)
  = take m (map (fun j => l !!! (o + j)%nat) (seq 0 n)).
Proof.
  intros Hmn. rewrite !map_eq_fmap. apply list_eq. intros k.
  destruct (Nat.lt_ge_cases k m) as [Hk|Hk].
  - rewrite list_lookup_fmap, lookup_seq_lt by exact Hk.
    rewrite lookup_take by exact Hk.
    rewrite list_lookup_fmap, lookup_seq_lt by lia. reflexivity.
  - rewrite list_lookup_fmap.
    rewrite lookup_ge_None_2 by (rewrite length_seq; lia).
    symmetry. apply lookup_ge_None_2.
    rewrite length_take, length_fmap, length_seq. lia.
Qed.

(* THE TRUNCATION LAW.  An [m]-byte read of the same offset is the [n]-byte
   value's low [m] bytes. *)
Lemma elf_le_at_trunc (l : elf_bytes) (o m n : nat) :
  (m <= n)%nat ->
  elf_le_at l o m = elf_le_at l o n `mod` 2 ^ (8 * Z.of_nat m).
Proof.
  intros Hmn. unfold elf_le_at.
  rewrite (elf_le_bytes_take l o m n Hmn). apply assemble_bytes_take.
Qed.

(* ...and the only use of it: under the bound, the truncation is exact. *)
Lemma elf_le_at_trunc_small (l : elf_bytes) (o m n : nat) :
  (m <= n)%nat -> elf_le_at l o n < 2 ^ (8 * Z.of_nat m) ->
  elf_le_at l o m = elf_le_at l o n.
Proof.
  intros Hmn Hlt. rewrite (elf_le_at_trunc l o m n Hmn).
  apply Z.mod_small. split; [apply elf_le_at_bound | exact Hlt].
Qed.

(* ====================================================================== *)
(*  3.  INVERTING [elf_parse_ehdr]                                        *)
(* ====================================================================== *)

Lemma elf_parse_ehdr_fields (l : elf_bytes) (e : elf_ehdr) :
  elf_parse_ehdr l = Some e ->
  (64 <= length l)%nat
  /\ ee_entry e = elf_le_at l 24 8
  /\ ee_phoff e = elf_le_at l 32 8
  /\ ee_phentsize e = elf_le_at l 54 2
  /\ ee_phnum e = elf_le_at l 56 2.
Proof.
  unfold elf_parse_ehdr, elf_read_u64, elf_read_u16.
  destruct (elf_read l 0x18 8) as [entry|] eqn:E1; [|discriminate].
  destruct (elf_read l 0x20 8) as [phoff|] eqn:E2; [|discriminate].
  destruct (elf_read l 0x28 8) as [shoff|] eqn:E3; [|discriminate].
  destruct (elf_read l 0x36 2) as [phentsize|] eqn:E4; [|discriminate].
  destruct (elf_read l 0x38 2) as [phnum|] eqn:E5; [|discriminate].
  destruct (elf_read l 0x3A 2) as [shentsize|] eqn:E6; [|discriminate].
  destruct (elf_read l 0x3C 2) as [shnum|] eqn:E7; [|discriminate].
  destruct (elf_read l 0x3E 2) as [shstrndx|] eqn:E8; [|discriminate].
  simpl. intros Heq. injection Heq as <-.
  pose proof (proj1 (elf_read_Some l 0x18 8 entry ltac:(lia)) E1)
    as (_ & _ & Hv1).
  pose proof (proj1 (elf_read_Some l 0x20 8 phoff ltac:(lia)) E2)
    as (_ & _ & Hv2).
  pose proof (proj1 (elf_read_Some l 0x36 2 phentsize ltac:(lia)) E4)
    as (_ & _ & Hv4).
  pose proof (proj1 (elf_read_Some l 0x38 2 phnum ltac:(lia)) E5)
    as (_ & _ & Hv5).
  pose proof (proj1 (elf_read_Some l 0x3E 2 shstrndx ltac:(lia)) E8)
    as (_ & Hb8 & _).
  change (Z.to_nat 0x18) with 24%nat in Hv1.
  change (Z.to_nat 0x20) with 32%nat in Hv2.
  change (Z.to_nat 0x36) with 54%nat in Hv4.
  change (Z.to_nat 0x38) with 56%nat in Hv5.
  repeat split; [lia | exact Hv1 | exact Hv2 | exact Hv4 | exact Hv5].
Qed.

(* THE HEADER BRIDGE.  [g] is the [struct elfhdr] kexec [readi]d into its
   frame; it agrees with the file's first 64 bytes.  [eh_phoff] is the
   FOUR-byte read, so it needs [kexec_loadable]'s bound. *)
Lemma eh_fields_of_ehdr (g : nat -> bv 8) (l : elf_bytes) (e : elf_ehdr) :
  elf_parse_ehdr l = Some e ->
  (forall j, (j < 64)%nat -> g j = l !!! j) ->
  eh_entry g = ee_entry e
  /\ eh_phnum g = ee_phnum e
  /\ (ee_phoff e < 2 ^ 31 -> eh_phoff g = ee_phoff e).
Proof.
  intros He Hag.
  destruct (elf_parse_ehdr_fields l e He) as (_ & H1 & H2 & _ & H5).
  unfold eh_entry, eh_phnum, eh_phoff.
  rewrite (le_at_of_list_below g l 24 8 64) by (lia || exact Hag).
  rewrite (le_at_of_list_below g l 56 2 64) by (lia || exact Hag).
  rewrite (le_at_of_list_below g l 32 4 64) by (lia || exact Hag).
  repeat split; [symmetry; exact H1 | symmetry; exact H5 |].
  intros Hlt. rewrite H2.
  apply elf_le_at_trunc_small; [lia|].
  rewrite <- H2. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). lia.
Qed.

(* the entry point in the shape [KexecOkQ.kxq_entry] carries it *)
Lemma kxq_entry_of_ehdr (g : nat -> bv 8) (l : elf_bytes) (e : elf_ehdr) :
  elf_parse_ehdr l = Some e ->
  (forall j, (j < 64)%nat -> g j = l !!! j) ->
  (Z_to_bv 64 (le_at g 24 8) : bv 64) = Z_to_bv 64 (ee_entry e).
Proof.
  intros He Hag.
  destruct (eh_fields_of_ehdr g l e He Hag) as (H1 & _ & _).
  unfold eh_entry in H1. rewrite H1. reflexivity.
Qed.

(* ====================================================================== *)
(*  4.  INVERTING [elf_table] AND [elf_parse_phdr]                        *)
(* ====================================================================== *)

Lemma elf_table_length {A : Type} (parse : Z -> option A) (o step : Z)
    (n : nat) (r : list A) :
  elf_table parse o step n = Some r -> length r = n.
Proof.
  revert o r. induction n as [|k IH]; intros o r Ht; simpl in Ht.
  - injection Ht as <-. reflexivity.
  - destruct (parse o) as [a|] eqn:Ea; [|discriminate].
    destruct (elf_table parse (o + step) step k) as [r'|] eqn:Et;
      [|discriminate].
    simpl in Ht. injection Ht as <-. simpl. rewrite (IH (o + step) r' Et).
    reflexivity.
Qed.

Lemma elf_table_lookup {A : Type} (parse : Z -> option A) (o step : Z)
    (n : nat) (r : list A) (i : nat) (a : A) :
  elf_table parse o step n = Some r -> r !! i = Some a ->
  parse (o + step * Z.of_nat i) = Some a.
Proof.
  revert o r i. induction n as [|k IH]; intros o r i Ht Hi; simpl in Ht.
  - injection Ht as <-. destruct i; discriminate.
  - destruct (parse o) as [a0|] eqn:Ea; [|discriminate].
    destruct (elf_table parse (o + step) step k) as [r'|] eqn:Et;
      [|discriminate].
    simpl in Ht. injection Ht as <-.
    destruct i as [|j].
    + simpl in Hi. injection Hi as <-.
      replace (o + step * Z.of_nat 0) with o by lia. exact Ea.
    + simpl in Hi.
      pose proof (IH (o + step) r' j Et Hi) as Hj.
      replace (o + step * Z.of_nat (S j))
        with (o + step + step * Z.of_nat j) by lia.
      exact Hj.
Qed.

Lemma elf_parse_phdr_fields (l : elf_bytes) (o : Z) (p : elf_phdr) :
  elf_parse_phdr l o = Some p ->
  0 <= o
  /\ o + 56 <= Z.of_nat (length l)
  /\ ep_type p = elf_le_at l (Z.to_nat o) 4
  /\ ep_flags p = elf_le_at l (Z.to_nat o + 4) 4
  /\ ep_offset p = elf_le_at l (Z.to_nat o + 8) 8
  /\ ep_vaddr p = elf_le_at l (Z.to_nat o + 16) 8
  /\ ep_filesz p = elf_le_at l (Z.to_nat o + 32) 8
  /\ ep_memsz p = elf_le_at l (Z.to_nat o + 40) 8.
Proof.
  unfold elf_parse_phdr, elf_read_u32, elf_read_u64.
  destruct (elf_read l o 4) as [ty|] eqn:E1; [|discriminate].
  destruct (elf_read l (o + 4) 4) as [fl|] eqn:E2; [|discriminate].
  destruct (elf_read l (o + 8) 8) as [off|] eqn:E3; [|discriminate].
  destruct (elf_read l (o + 16) 8) as [va|] eqn:E4; [|discriminate].
  destruct (elf_read l (o + 24) 8) as [pa|] eqn:E5; [|discriminate].
  destruct (elf_read l (o + 32) 8) as [fsz|] eqn:E6; [|discriminate].
  destruct (elf_read l (o + 40) 8) as [msz|] eqn:E7; [|discriminate].
  destruct (elf_read l (o + 48) 8) as [al|] eqn:E8; [|discriminate].
  simpl. intros Heq. injection Heq as <-.
  pose proof (proj1 (elf_read_Some l o 4 ty ltac:(lia)) E1) as (Ho & _ & Hv1).
  pose proof (proj1 (elf_read_Some l (o + 4) 4 fl ltac:(lia)) E2)
    as (_ & _ & Hv2).
  pose proof (proj1 (elf_read_Some l (o + 8) 8 off ltac:(lia)) E3)
    as (_ & _ & Hv3).
  pose proof (proj1 (elf_read_Some l (o + 16) 8 va ltac:(lia)) E4)
    as (_ & _ & Hv4).
  pose proof (proj1 (elf_read_Some l (o + 32) 8 fsz ltac:(lia)) E6)
    as (_ & _ & Hv6).
  pose proof (proj1 (elf_read_Some l (o + 40) 8 msz ltac:(lia)) E7)
    as (_ & _ & Hv7).
  pose proof (proj1 (elf_read_Some l (o + 48) 8 al ltac:(lia)) E8)
    as (_ & Hb8 & _).
  rewrite (Z2Nat.inj_add o 4) in Hv2 by lia.
  rewrite (Z2Nat.inj_add o 8) in Hv3 by lia.
  rewrite (Z2Nat.inj_add o 16) in Hv4 by lia.
  rewrite (Z2Nat.inj_add o 32) in Hv6 by lia.
  rewrite (Z2Nat.inj_add o 40) in Hv7 by lia.
  change (Z.to_nat 4) with 4%nat in Hv2.
  change (Z.to_nat 8) with 8%nat in Hv3.
  change (Z.to_nat 16) with 16%nat in Hv4.
  change (Z.to_nat 32) with 32%nat in Hv6.
  change (Z.to_nat 40) with 40%nat in Hv7.
  repeat split;
    [lia | lia | exact Hv1 | exact Hv2 | exact Hv3 | exact Hv4
     | exact Hv6 | exact Hv7].
Qed.

(* ...ALL EIGHT FIELDS, which is what identifies the parsed record with the
   TOTAL reader the phdr loop's invariant is stated on
   ([KexecBuilt.kxb_phdr_at]).  [elf_parse_phdr_fields] above exposes only
   the six the code reads; the invariant needs the record itself. *)
Lemma elf_parse_phdr_all (l : elf_bytes) (o : Z) (p : elf_phdr) :
  elf_parse_phdr l o = Some p ->
  p = ElfPhdr (elf_le_at l (Z.to_nat o) 4) (elf_le_at l (Z.to_nat o + 4) 4)
              (elf_le_at l (Z.to_nat o + 8) 8) (elf_le_at l (Z.to_nat o + 16) 8)
              (elf_le_at l (Z.to_nat o + 24) 8) (elf_le_at l (Z.to_nat o + 32) 8)
              (elf_le_at l (Z.to_nat o + 40) 8) (elf_le_at l (Z.to_nat o + 48) 8).
Proof.
  unfold elf_parse_phdr, elf_read_u32, elf_read_u64.
  destruct (elf_read l o 4) as [ty|] eqn:E1; [|discriminate].
  destruct (elf_read l (o + 4) 4) as [fl|] eqn:E2; [|discriminate].
  destruct (elf_read l (o + 8) 8) as [off|] eqn:E3; [|discriminate].
  destruct (elf_read l (o + 16) 8) as [va|] eqn:E4; [|discriminate].
  destruct (elf_read l (o + 24) 8) as [pa|] eqn:E5; [|discriminate].
  destruct (elf_read l (o + 32) 8) as [fsz|] eqn:E6; [|discriminate].
  destruct (elf_read l (o + 40) 8) as [msz|] eqn:E7; [|discriminate].
  destruct (elf_read l (o + 48) 8) as [al|] eqn:E8; [|discriminate].
  simpl. intros Heq. injection Heq as <-.
  pose proof (proj1 (elf_read_Some l o 4 ty ltac:(lia)) E1) as (Ho & _ & Hv1).
  pose proof (proj1 (elf_read_Some l (o + 4) 4 fl ltac:(lia)) E2) as (_ & _ & Hv2).
  pose proof (proj1 (elf_read_Some l (o + 8) 8 off ltac:(lia)) E3) as (_ & _ & Hv3).
  pose proof (proj1 (elf_read_Some l (o + 16) 8 va ltac:(lia)) E4) as (_ & _ & Hv4).
  pose proof (proj1 (elf_read_Some l (o + 24) 8 pa ltac:(lia)) E5) as (_ & _ & Hv5).
  pose proof (proj1 (elf_read_Some l (o + 32) 8 fsz ltac:(lia)) E6) as (_ & _ & Hv6).
  pose proof (proj1 (elf_read_Some l (o + 40) 8 msz ltac:(lia)) E7) as (_ & _ & Hv7).
  pose proof (proj1 (elf_read_Some l (o + 48) 8 al ltac:(lia)) E8) as (_ & _ & Hv8).
  rewrite (Z2Nat.inj_add o 4) in Hv2 by lia.
  rewrite (Z2Nat.inj_add o 8) in Hv3 by lia.
  rewrite (Z2Nat.inj_add o 16) in Hv4 by lia.
  rewrite (Z2Nat.inj_add o 24) in Hv5 by lia.
  rewrite (Z2Nat.inj_add o 32) in Hv6 by lia.
  rewrite (Z2Nat.inj_add o 40) in Hv7 by lia.
  rewrite (Z2Nat.inj_add o 48) in Hv8 by lia.
  change (Z.to_nat 4) with 4%nat in Hv2.
  change (Z.to_nat 8) with 8%nat in Hv3.
  change (Z.to_nat 16) with 16%nat in Hv4.
  change (Z.to_nat 24) with 24%nat in Hv5.
  change (Z.to_nat 32) with 32%nat in Hv6.
  change (Z.to_nat 40) with 40%nat in Hv7.
  change (Z.to_nat 48) with 48%nat in Hv8.
  rewrite Hv1, Hv2, Hv3, Hv4, Hv5, Hv6, Hv7, Hv8. reflexivity.
Qed.

(* THE PROGRAM-HEADER BRIDGE.  [g] is the 56-byte [struct proghdr] kexec
   [readi]d out of the file at offset [o]; [ph_off] is the FOUR-byte read,
   so it needs [kexec_loadable]'s [ep_offset p < 2 ^ 31]. *)
Lemma ph_fields_of_phdr (g : nat -> bv 8) (l : elf_bytes) (o : Z)
    (p : elf_phdr) :
  elf_parse_phdr l o = Some p ->
  (forall j, (j < 56)%nat -> g j = l !!! (Z.to_nat o + j)%nat) ->
  ph_type g = ep_type p
  /\ ph_flags g = ep_flags p
  /\ ph_vaddr g = ep_vaddr p
  /\ ph_filesz g = ep_filesz p
  /\ ph_memsz g = ep_memsz p
  /\ (ep_offset p < 2 ^ 31 -> ph_off g = ep_offset p).
Proof.
  intros Hp Hag.
  destruct (elf_parse_phdr_fields l o p Hp)
    as (_ & _ & H1 & H2 & H3 & H4 & H6 & H7).
  assert (Hsh : forall a n : nat, (a + n <= 56)%nat ->
            le_at g a n = elf_le_at l (Z.to_nat o + a) n).
  { intros a n Han. apply le_at_shift_of_list. intros j Hj.
    replace (Z.to_nat o + a + j)%nat with (Z.to_nat o + (a + j))%nat by lia.
    apply Hag. lia. }
  unfold ph_type, ph_flags, ph_vaddr, ph_filesz, ph_memsz, ph_off.
  rewrite (Hsh 0%nat 4%nat) by lia. rewrite (Hsh 4%nat 4%nat) by lia.
  rewrite (Hsh 16%nat 8%nat) by lia. rewrite (Hsh 32%nat 8%nat) by lia.
  rewrite (Hsh 40%nat 8%nat) by lia. rewrite (Hsh 8%nat 4%nat) by lia.
  repeat split.
  - replace (Z.to_nat o + 0)%nat with (Z.to_nat o) by lia.
    symmetry. exact H1.
  - symmetry. exact H2.
  - symmetry. exact H4.
  - symmetry. exact H6.
  - symmetry. exact H7.
  - intros Hlt. rewrite H3. apply elf_le_at_trunc_small; [lia|].
    rewrite <- H3. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). lia.
Qed.

(* ====================================================================== *)
(*  5.  THE TABLE, AS THE PHDR LOOP WALKS IT                              *)
(* ====================================================================== *)

Lemma elf_wf_phentsize (l : elf_bytes) (e : elf_ehdr) :
  elf_wf l = true -> elf_parse_ehdr l = Some e -> ee_phentsize e = 56.
Proof.
  intros Hwf He. unfold elf_wf in Hwf. rewrite He in Hwf.
  destruct (elf_phdrs l) as [ps|]; [|discriminate].
  rewrite !andb_true_iff in Hwf.
  destruct Hwf as [[[[[[_ Hb] _] _] _] _] _].
  apply Z.eqb_eq in Hb. exact Hb.
Qed.

Lemma elf_wf_phdrs (l : elf_bytes) :
  elf_wf l = true -> exists ps, elf_phdrs l = Some ps.
Proof.
  intros Hwf. unfold elf_wf in Hwf.
  destruct (elf_parse_ehdr l) as [e|]; [|discriminate].
  destruct (elf_phdrs l) as [ps|]; [|discriminate].
  exists ps. reflexivity.
Qed.

(* the phdr table has exactly [ee_phnum] entries -- the loop's trip count *)
Lemma elf_phdrs_length (l : elf_bytes) (e : elf_ehdr) (ps : list elf_phdr) :
  elf_parse_ehdr l = Some e -> elf_phdrs l = Some ps ->
  length ps = Z.to_nat (ee_phnum e).
Proof.
  intros He Hps. unfold elf_phdrs in Hps. rewrite He in Hps. simpl in Hps.
  exact (elf_table_length _ _ _ _ _ Hps).
Qed.

(* entry [i] of the table is parsed from [ee_phoff e + 56 * i] -- which is
   [ElfEnc.ph_at] once [eh_phoff] is known to be [ee_phoff]. *)
Lemma elf_phdrs_parse (l : elf_bytes) (e : elf_ehdr) (ps : list elf_phdr)
    (i : nat) (p : elf_phdr) :
  elf_wf l = true -> elf_parse_ehdr l = Some e -> elf_phdrs l = Some ps ->
  ps !! i = Some p ->
  elf_parse_phdr l (ee_phoff e + 56 * Z.of_nat i) = Some p.
Proof.
  intros Hwf He Hps Hi. unfold elf_phdrs in Hps. rewrite He in Hps.
  simpl in Hps.
  rewrite <- (elf_wf_phentsize l e Hwf He).
  exact (elf_table_lookup _ _ _ _ _ _ _ Hps Hi).
Qed.

(* [ph_at] of the code's own header IS the file offset of entry [i]. *)
Lemma ph_at_of_ehdr (g : nat -> bv 8) (l : elf_bytes) (e : elf_ehdr)
    (i : nat) :
  elf_parse_ehdr l = Some e ->
  (forall j, (j < 64)%nat -> g j = l !!! j) ->
  ee_phoff e < 2 ^ 31 ->
  ph_at g i = ee_phoff e + 56 * Z.of_nat i.
Proof.
  intros He Hag Hlt.
  destruct (eh_fields_of_ehdr g l e He Hag) as (_ & _ & H3).
  unfold ph_at. rewrite (H3 Hlt). reflexivity.
Qed.

(* a PT_LOAD entry of the table is a member of [elf_loads] *)
Lemma elf_loads_elem (l : elf_bytes) (ps : list elf_phdr) (i : nat)
    (p : elf_phdr) :
  elf_phdrs l = Some ps -> ps !! i = Some p -> ep_type p = 1 ->
  p ∈ elf_loads l.
Proof.
  intros Hps Hi Hty. unfold elf_loads. rewrite Hps.
  apply elem_of_list_In, List.filter_In. split.
  - apply elem_of_list_In, (elem_of_list_lookup_2 ps i p Hi).
  - apply Z.eqb_eq, Hty.
Qed.

(* ...and conversely every member of [elf_loads] is a table entry, which is
   what turns a [Forall] over [elf_loads] into a fact about entry [i]. *)
Lemma elf_loads_sub (l : elf_bytes) (ps : list elf_phdr) (p : elf_phdr) :
  elf_phdrs l = Some ps -> p ∈ elf_loads l -> p ∈ ps /\ ep_type p = 1.
Proof.
  intros Hps Hp. unfold elf_loads in Hp. rewrite Hps in Hp.
  apply elem_of_list_In, List.filter_In in Hp as [Hin Hty].
  split; [apply elem_of_list_In, Hin | apply Z.eqb_eq, Hty].
Qed.

(* ====================================================================== *)
(*  6.  THE [readi] WINDOW: the bytes kexec reads ARE the abstract file    *)
(* ====================================================================== *)

(* [FsTree.file_bytes]' total lookup below the size IS [file_byte].  With
   [SpecReadi.rd_delivered_bytes] ([rd_delivered data olds off tot j =
   file_byte data (off + j)] for [j < tot]) this is the whole tie between
   what [readi] delivers and the [AFile] list the observation carries:
   [fn_file_bytes (era_node dn bm data)] is [file_bytes data (Z.to_nat
   (bv_unsigned (di_size dn)))] once [FsStateEra.era_node_data] has
   replaced [fn_data (era_node dn bm data)] by [data]. *)
Lemma file_bytes_lookup (data : nat -> list (bv 8)) (sz k : nat) :
  (k < sz)%nat -> file_bytes data sz !!! k = file_byte data k.
Proof.
  intros Hk. apply list_lookup_total_correct.
  unfold file_bytes. rewrite list_lookup_fmap, lookup_seq_lt by exact Hk.
  reflexivity.
Qed.

(* THE COMPOSITE the exec proof applies: a buffer filled by [readi] from
   file offset [base] reads exactly as the abstract byte list does. *)
Lemma le_at_of_file_bytes (g : nat -> bv 8) (data : nat -> list (bv 8))
    (sz base o n : nat) :
  (forall j, (j < n)%nat -> g (o + j)%nat = file_byte data (base + o + j)%nat) ->
  (base + o + n <= sz)%nat ->
  le_at g o n = elf_le_at (file_bytes data sz) (base + o) n.
Proof.
  intros Hg Hsz. apply le_at_shift_of_list. intros j Hj.
  rewrite Hg by exact Hj. symmetry. apply file_bytes_lookup. lia.
Qed.
