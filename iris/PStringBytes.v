(* PStringBytes.v -- a lowercase-hex primitive string, read as a byte list.

   A BRIDGE, not a theory.  A large binary blob (an ELF image, a disk
   image) cannot be written into a Rocq file as a [list (bv 8)] literal
   without the file becoming unusable -- the term is enormous and every
   [vm_compute] pays for re-elaborating it.  A Rocq 9 PRIMITIVE STRING
   (Stdlib.Strings.PString) holds the same bytes as a compact literal with
   O(1) [get], and stays native under [vm_compute].  So a generated file
   emits the blob as HEX in a [PrimString.string], and THIS file turns that
   string into the [list (bv 8)] the rest of the tree speaks.

   The pstring literal is the ground truth: nothing here is proved about
   the CONTENTS of a blob -- the consumer does that by [vm_compute] on the
   decoded list.  What is proved here is only the SHAPE of the decoding
   ([pstring_hex_bytes_spec] and its two corollaries), which is what a
   consumer needs in order to reason about the list rather than compute
   with it.

   THE DECODE IS REV-FREE, AND THAT IS LOAD-BEARING.  [List.rev] is
   quadratic under [vm_compute] and costs ~55 s on a 55k-element list.
   [pstring_hex_aux] therefore counts its fuel DOWN with a DESCENDING byte
   index and conses onto the front, so the accumulator is already in final
   order and no reversal is ever needed.  Do not "simplify" it into an
   ascending loop plus [rev].

   Hex digits are assumed LOWERCASE ('0'-'9', 'a'-'f'): [hex_digit_val]
   maps a code point below '9'+1 by subtracting 48 and anything else by
   subtracting 87.  A generated file that emits uppercase, or any
   non-hex character, decodes to garbage rather than failing -- which is
   harmless, because the consumer's [vm_compute] check is what certifies
   the blob.

   Nothing ELF-specific lives here; [ElfFile.v] does not import this file
   and this file does not import it. *)

From Stdlib Require Import ZArith List Lia.
From Stdlib.Strings Require Import PString.
From stdpp Require Import list.
From stdpp.bitvector Require Import definitions.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Reading the string                                                      *)
(* ---------------------------------------------------------------------- *)

(* The code point of character [i], as a [Z].  Out of range, [PrimString.get]
   returns 0, so [pstring_char] is total. *)
Definition pstring_char (s : PrimString.string) (i : Z) : Z :=
  Uint63.to_Z (PrimString.get s (Uint63.of_Z i)).

(* '0'..'9' are 48..57, 'a'..'f' are 97..102. *)
Definition hex_digit_val (c : Z) : Z := if c <? 58 then c - 48 else c - 87.

(* The number of BYTES the hex string encodes: two characters per byte. *)
Definition pstring_hex_length (s : PrimString.string) : Z :=
  Uint63.to_Z (PrimString.length s) / 2.

(* Byte [i]: the high nibble first, as hex is written. *)
Definition pstring_hex_byte (s : PrimString.string) (i : Z) : bv 8 :=
  Z_to_bv 8 (hex_digit_val (pstring_char s (2 * i)) * 16
             + hex_digit_val (pstring_char s (2 * i + 1))).

(* ---------------------------------------------------------------------- *)
(* The decode -- descending index, cons at the front, NO [List.rev]        *)
(* ---------------------------------------------------------------------- *)

Fixpoint pstring_hex_aux (s : PrimString.string) (fuel : nat) (i : Z)
                         (acc : list (bv 8)) : list (bv 8) :=
  match fuel with
  | O => acc
  | S k => pstring_hex_aux s k (i - 1) (pstring_hex_byte s i :: acc)
  end.

Definition pstring_hex_bytes (s : PrimString.string) : list (bv 8) :=
  pstring_hex_aux s (Z.to_nat (pstring_hex_length s)) (pstring_hex_length s - 1) nil.

(* ---------------------------------------------------------------------- *)
(* What the decode IS                                                      *)
(* ---------------------------------------------------------------------- *)

Lemma pstring_hex_length_nonneg (s : PrimString.string) : 0 <= pstring_hex_length s.
Proof.
  unfold pstring_hex_length.
  pose proof (Uint63.to_Z_bounded (PrimString.length s)).
  apply Z.div_pos; lia.
Qed.

(* The accumulator loop, in closed form: [fuel] bytes starting at [base]. *)
Lemma pstring_hex_aux_spec (s : PrimString.string) (fuel : nat) (base : Z)
                           (acc : list (bv 8)) :
  pstring_hex_aux s fuel (base + Z.of_nat fuel - 1) acc
  = map (fun k => pstring_hex_byte s (base + Z.of_nat k)) (seq 0 fuel) ++ acc.
Proof.
  revert acc. induction fuel as [|n IH]; intros acc; [reflexivity|].
  replace (base + Z.of_nat (S n) - 1) with (base + Z.of_nat n) by lia.
  simpl pstring_hex_aux.
  rewrite IH, seq_S, map_app, <- app_assoc; simpl; reflexivity.
Qed.

Lemma pstring_hex_bytes_spec (s : PrimString.string) :
  pstring_hex_bytes s
  = map (fun k => pstring_hex_byte s (Z.of_nat k))
        (seq 0 (Z.to_nat (pstring_hex_length s))).
Proof.
  unfold pstring_hex_bytes.
  pose proof (pstring_hex_length_nonneg s).
  replace (pstring_hex_length s - 1)
    with (0 + Z.of_nat (Z.to_nat (pstring_hex_length s)) - 1) by lia.
  rewrite pstring_hex_aux_spec, app_nil_r.
  apply map_ext; intros k; f_equal; lia.
Qed.

(* The length, stated over [Z] -- never over [nat], where a 55024 literal
   is a 55024-deep successor chain (see claude-notes/durable-notes.md). *)
Lemma pstring_hex_bytes_length (s : PrimString.string) :
  Z.of_nat (length (pstring_hex_bytes s)) = pstring_hex_length s.
Proof.
  pose proof (pstring_hex_length_nonneg s).
  rewrite pstring_hex_bytes_spec, length_map, length_seq. lia.
Qed.

Lemma pstring_hex_bytes_lookup (s : PrimString.string) (k : nat) :
  Z.of_nat k < pstring_hex_length s ->
  pstring_hex_bytes s !! k = Some (pstring_hex_byte s (Z.of_nat k)).
Proof.
  intros Hk. pose proof (pstring_hex_length_nonneg s).
  rewrite pstring_hex_bytes_spec.
  assert (Hmap : forall (g : nat -> bv 8) (l : list nat), map g l = g <$> l).
  { intros g l. induction l as [|x l IHl]; [reflexivity|].
    simpl. rewrite IHl. reflexivity. }
  rewrite Hmap, list_lookup_fmap, lookup_seq_lt by lia. reflexivity.
Qed.
