(* ===================================================================== *)
(* UkProgAbi.v -- the REGISTER-INDEX facts a program proof needs to state *)
(* and discharge a [ucallee_saved] post.                                  *)
(*                                                                        *)
(* None of this is about any one program, and none of it is Iris: it is   *)
(* the arithmetic of [mword 5] register indices.  It lives in its own     *)
(* file because every function proof that RETURNS wants it, and because   *)
(* the three shapes below are each a trap the first time:                 *)
(*                                                                        *)
(*   [uidx_ne] / [uidx_eq]  -- a register disequality is an INDEX one,    *)
(*     and the index lemma is [UserBits.uint_unsigned_n], not             *)
(*     [RiscvExtras.uint_unsigned] (which is [mword 64] only).            *)
(*   [ucs_cases]            -- [ucallee_saved_idx] is a boolean, and a    *)
(*     post quantified over it needs the ENUMERATION to be discharged.    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvExtras.
Require Import RegFile.
Require Import UserBits.
Require Import UmodeAbi.
Local Open Scope Z_scope.
Import Defs.


(* a callee-saved register is none of the ones a caller may clobber *)
Lemma ucs_ne (r q : mword 5) :
  ucallee_saved_idx r = true -> ucallee_saved_idx q = false ->
  Regidx r <> Regidx q.
Proof.
  intros Hr Hq He.
  assert (Hrr : r = q) by (injection He; trivial).
  rewrite Hrr, Hq in Hr. discriminate.
Qed.

(* the fifteen callee-saved registers, ENUMERATED.  A post of the form
   [ucallee_saved m0 m'] is a [forall r] over a boolean, and discharging it
   for a function that spills ten of them means knowing there is nothing
   else; this is that fact, and it is stated once. *)
Lemma ucs_cases (r : mword 5) :
  ucallee_saved_idx r = true ->
  uint r = 2 \/ uint r = 3 \/ uint r = 4 \/ uint r = 8 \/ uint r = 9 \/
  (18 <= uint r <= 27).
Proof.
  unfold ucallee_saved_idx. intros H.
  repeat (apply orb_true_iff in H as [H | H]);
    [ apply Z.eqb_eq in H; lia | apply Z.eqb_eq in H; lia
    | apply Z.eqb_eq in H; lia | apply Z.eqb_eq in H; lia
    | apply Z.eqb_eq in H; lia
    | apply andb_true_iff in H as [H1 H2];
      apply Z.leb_le in H1; apply Z.leb_le in H2; lia ].
Qed.

(* [Regidx] is injective, so a register disequality is an index one *)
Lemma uidx_ne (r q : mword 5) : uint r <> uint q -> Regidx r <> Regidx q.
Proof. intros H He. apply H. injection He as ->. reflexivity. Qed.

Lemma uidx_eq (r : mword 5) (z : Z) (q : mword 5) :
  uint r = z -> uint q = z -> Regidx r = Regidx q.
Proof.
  intros H1 H2. f_equal. apply bv_eq.
  (* [uint_unsigned] is the [mword 64] lemma; a register index is
     [mword 5], and its twin is [UserBits.uint_unsigned_n].  NOTE the
     COMMAS: this file does not load ssreflect, so [rewrite] is the
     vanilla one. *)
  rewrite <- (uint_unsigned_n 5 r), <- (uint_unsigned_n 5 q), H1, H2.
  reflexivity.
Qed.
