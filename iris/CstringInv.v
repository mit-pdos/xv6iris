(* CstringInv.v -- the INVERSE of [RiscvPtsto.cstring_bytes].

   [cstring_bytes] goes string -> bytes.  The tree had no way back, so every
   reader of a NUL-terminated byte buffer had to ASSUME the split existed:
   syscall()'s [printk("%s", p->name)] fallback did (as a module axiom), and
   [SpecProcdump.proc_dump_slot] has the same shape.  It does not have to be
   assumed -- a buffer with a NUL in it DETERMINES the string, and that is
   what this file proves.

   It is its own file because it belongs to neither side: [string_bytes] and
   [cstring_bytes] live in RiscvPtsto.v, which knows nothing of printk, and
   [nonul] lives in PrintkFmt.v, which is stdlib-only and knows nothing of
   bytes.  This is the one place that needs both. *)
From Stdlib Require Import ZArith List Bool Ascii String Lia.
From stdpp Require Import list bitvector.definitions.
Require Import RiscvPtsto.
Require Import PrintkFmt.
Import ListNotations.
Local Open Scope Z_scope.

Definition byte_ascii (b : bv 8) : ascii :=
  Ascii.ascii_of_N (Z.to_N (bv_unsigned b)).

Fixpoint bytes_string (bs : list (bv 8)) : string :=
  match bs with
  | [] => EmptyString
  | b :: bs' =>
      if bool_decide (b = Z_to_bv 8 0) then EmptyString
      else String (byte_ascii b) (bytes_string bs')
  end.

(* the round trip on ONE byte: [bv 8] is exactly the range [ascii_of_N] and
   [N_of_ascii] are inverse on. *)
Lemma byte_ascii_roundtrip (b : bv 8) :
  Z_to_bv 8 (Z.of_N (Ascii.N_of_ascii (byte_ascii b))) = b.
Proof.
  unfold byte_ascii.
  rewrite Ascii.N_ascii_embedding.
  - rewrite Z2N.id; [| apply bv_unsigned_in_range].
    apply bv_eq. rewrite Z_to_bv_unsigned.
    apply bv_wrap_small. apply bv_unsigned_in_range.
  - pose proof (bv_unsigned_in_range 8 b) as Hr.
    unfold bv_modulus in Hr. cbn in Hr. lia.
Qed.

(* ...and a NON-NUL byte gives a NON-NUL character, which is the other half
   of [nonul] holding by construction. *)
Lemma byte_ascii_nonul (b : bv 8) :
  b <> Z_to_bv 8 0 -> Ascii.eqb (byte_ascii b) pk_nul = false.
Proof.
  intro Hb. apply Bool.not_true_is_false. intro He.
  apply Ascii.eqb_eq in He. apply Hb.
  rewrite <- (byte_ascii_roundtrip b). rewrite He.
  assert (Hz : Ascii.N_of_ascii pk_nul = 0%N) by (vm_compute; reflexivity).
  rewrite Hz. reflexivity.
Qed.

Lemma bytes_string_nonul (bs : list (bv 8)) : nonul (bytes_string bs) = true.
Proof.
  induction bs as [| b bs IH]; [reflexivity |]; cbn.
  case_bool_decide as Hb; [reflexivity |].
  cbn. rewrite (byte_ascii_nonul b Hb). exact IH.
Qed.

(* [cstring_bytes] on a cons: the NUL rides at the END, so prefixing a
   character prefixes its byte.  Definitional, and it is what keeps the
   induction below from having to reassociate anything. *)
Lemma cstring_bytes_cons (c : ascii) (s : string) :
  cstring_bytes (String c s)
  = Z_to_bv 8 (Z.of_N (Ascii.N_of_ascii c)) :: cstring_bytes s.
Proof. reflexivity. Qed.

(* THE SPLIT.  A buffer with a NUL anywhere in it IS a C string followed by
   whatever the compiler left behind. *)
Lemma bytes_string_split (bs : list (bv 8)) :
  (exists k, (k < length bs)%nat /\ bs !! k = Some (Z_to_bv 8 0)) ->
  exists pad : list (bv 8), bs = cstring_bytes (bytes_string bs) ++ pad.
Proof.
  induction bs as [| b bs IH]; intros (k & Hk & Hb); [cbn in Hk; lia |].
  cbn [bytes_string]. case_bool_decide as Hz.
  - exists bs. unfold cstring_bytes; cbn. rewrite Hz. reflexivity.
  - destruct k as [| k'].
    { cbn in Hb. exfalso. apply Hz. injection Hb. intro Hq. exact Hq. }
    destruct IH as (pad & Hpad).
    { exists k'. cbn in Hk, Hb. split; [lia | exact Hb]. }
    exists pad. rewrite cstring_bytes_cons. rewrite byte_ascii_roundtrip.
    cbn [app]. f_equal. exact Hpad.
Qed.
