(* WpUserDecodeWidth.v -- load/store decode width-totality.

   The user-mode decoder maps a LOAD/STORE instruction word to
   [LOAD (imm, rs1, rd, is_unsigned, W)] / [STORE (imm, rs2, rs1, W)] where the
   width [W : word_width = Z] is a SYMBOLIC value extracted from the funct3
   field via [width_enc_backwards].  Downstream classification needs to know
   that any decoded width is one of the four legal RISC-V access widths
   {1,2,4,8}.

   This file proves exactly that: reusing the [goodbP] leaf-predicate
   traversal machinery of DecodeSetU (the same [dtp_core] driver that closes
   [goodbP_encdec_u]) with a leaf predicate [Pwidth] that pins every reachable
   LOAD/STORE leaf's width to {1,2,4,8}, and then extracting the fact for a
   concretely-decoded word via [goodbP_exec].                                *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvExec.
Require Import WpDecodeBridge UmodeEcall.
Require Import DecodeSetU.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The leaf predicate.                                                 *)
(* ===================================================================== *)

Definition wok (W : Z) : bool :=
  orb (Z.eqb W 1) (orb (Z.eqb W 2) (orb (Z.eqb W 4) (Z.eqb W 8))).

Definition Pwidth (i : instruction) : bool :=
  match i with
  | LOAD (_, _, _, _, W) => wok W
  | STORE (_, _, _, W) => wok W
  | _ => true
  end.

(* ===================================================================== *)
(* §2 The width-leaf tactic.                                             *)
(*                                                                        *)
(* [dtp_core] closes every leaf whose [Pwidth] value is [true] by         *)
(* conversion (all non-LOAD/STORE constructors), but a LOAD/STORE leaf     *)
(* reduces to [wok (width_enc_backwards <funct3 bits>) = true], which is   *)
(* stuck on the symbolic funct3.  [width_enc_backwards] is a 2-bit         *)
(* case split into exactly {1,2,4,8}, so unfolding it and destructing the  *)
(* (≤3) [eq_vec] guards (plus any residual value/validity [if]s, whose     *)
(* branches all land in {1,2,4,8} or [None]) makes every branch close by   *)
(* computation.                                                            *)
(* ===================================================================== *)

Ltac wtac :=
  lazymatch goal with
  | |- ?g = true =>
      match g with
      | context[width_enc_backwards _] =>
          cbv beta iota zeta delta [Pwidth wok width_enc_backwards optP];
          repeat match goal with
                 | |- context[if ?c then _ else _] => destruct c
                 end;
          reflexivity
      end
  end.

(* ===================================================================== *)
(* §3 The classified traversal.                                          *)
(* ===================================================================== *)

Lemma goodbP_width_u (w : mword 32) :
  goodbP D_u Pwidth (ext_decode w) dstateU = true.
Proof.
  unfold ext_decode, encdec_backwards. cbv beta zeta.
  repeat (first [ dtp_core | wtac ]).
Qed.

(* ===================================================================== *)
(* §4 Extraction: a decoded LOAD/STORE width is one of {1,2,4,8}.         *)
(* ===================================================================== *)

Theorem load_width_cases (w : mword 32) (imm : mword 12) (rs1 rd : mword 5)
        (isu : bool) (W : Z) :
  (forall s, agree_on D_u s dstateU ->
             exec (ext_decode w) s = Some (LOAD (imm, Regidx rs1, Regidx rd, isu, W), s)) ->
  W = 1 \/ W = 2 \/ W = 4 \/ W = 8.
Proof.
  intros H.
  destruct (goodbP_exec D_u Pwidth (ext_decode w) dstateU dstateU
              (fun r _ => eq_refl) (goodbP_width_u w)) as (i & Hi & _ & HP).
  specialize (H dstateU (fun r _ => eq_refl)).
  assert (i = LOAD (imm, Regidx rs1, Regidx rd, isu, W)) as -> by congruence.
  cbv beta iota delta [Pwidth wok] in HP.
  apply orb_true_iff in HP as [HP | HP].
  - left. now apply Z.eqb_eq.
  - apply orb_true_iff in HP as [HP | HP].
    + right; left. now apply Z.eqb_eq.
    + apply orb_true_iff in HP as [HP | HP].
      * right; right; left. now apply Z.eqb_eq.
      * right; right; right. now apply Z.eqb_eq.
Qed.

Theorem store_width_cases (w : mword 32) (imm : mword 12) (rs2 rs1 : mword 5)
        (W : Z) :
  (forall s, agree_on D_u s dstateU ->
             exec (ext_decode w) s = Some (STORE (imm, Regidx rs2, Regidx rs1, W), s)) ->
  W = 1 \/ W = 2 \/ W = 4 \/ W = 8.
Proof.
  intros H.
  destruct (goodbP_exec D_u Pwidth (ext_decode w) dstateU dstateU
              (fun r _ => eq_refl) (goodbP_width_u w)) as (i & Hi & _ & HP).
  specialize (H dstateU (fun r _ => eq_refl)).
  assert (i = STORE (imm, Regidx rs2, Regidx rs1, W)) as -> by congruence.
  cbv beta iota delta [Pwidth wok] in HP.
  apply orb_true_iff in HP as [HP | HP].
  - left. now apply Z.eqb_eq.
  - apply orb_true_iff in HP as [HP | HP].
    + right; left. now apply Z.eqb_eq.
    + apply orb_true_iff in HP as [HP | HP].
      * right; right; left. now apply Z.eqb_eq.
      * right; right; right. now apply Z.eqb_eq.
Qed.
