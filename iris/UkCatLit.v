(* ===================================================================== *)
(* UkCatLit.v -- cat's three string LITERALS, cut out of the read-only    *)
(* image at a concrete base and length.                                    *)
(*                                                                         *)
(* Everything a caller needs about a literal -- that its body bytes are     *)
(* non-NUL, that none of them is '%', and that a NUL follows -- is DECIDED  *)
(* by [cat_lit_ok], one [vm_compute] per literal.  The alternative is a    *)
(* [destruct j] chain as long as the string at every use site.              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import UmodeAbi.
Require Import UserHeap.
Require Import UCodeCat.
Require User.CatSyms User.CatInstrs.
Local Open Scope Z_scope.
Import Defs.

Local Open Scope Z_scope.

(* the byte function of the literal based at [base] *)
Definition cat_lit (base : Z) : nat -> mword 8 :=
  fun j => default (bv_0 8) (cat_ro !! (base + Z.of_nat j)%Z).

(* ...and the whole of what makes it a printable C string *)
Definition cat_lit_ok (base : Z) (len : nat) : bool :=
  forallb (fun j => match cat_ro !! (base + Z.of_nat j)%Z with
                    | Some b => negb (Z.eqb (bv_unsigned b) 0)
                                && negb (Z.eqb (bv_unsigned b) 37)
                    | None => false
                    end)
          (seq 0 len)
  && match cat_ro !! (base + Z.of_nat len)%Z with
     | Some b => Z.eqb (bv_unsigned b) 0
     | None => false
     end.

Lemma cat_lit_ok_body (base : Z) (len : nat) (j : nat) :
  cat_lit_ok base len = true -> (j < len)%nat ->
  cat_ro !! (base + Z.of_nat j)%Z = Some (cat_lit base j)
  /\ bv_unsigned (cat_lit base j) <> 0
  /\ bv_unsigned (cat_lit base j) <> 37.
Proof.
  unfold cat_lit_ok, cat_lit. intros H Hj.
  apply andb_true_iff in H as [H _].
  rewrite forallb_forall in H.
  specialize (H j ltac:(apply in_seq; lia)).
  destruct (cat_ro !! (base + Z.of_nat j)%Z) as [b | ] eqn:Hb;
    [ | discriminate ].
  apply andb_true_iff in H as [H0 H37].
  apply negb_true_iff, Z.eqb_neq in H0.
  apply negb_true_iff, Z.eqb_neq in H37.
  cbn [default]. split; [ reflexivity | ]. split; assumption.
Qed.

Lemma cat_lit_ok_nul (base : Z) (len : nat) :
  cat_lit_ok base len = true ->
  cat_ro !! (base + Z.of_nat len)%Z = Some ubyte0.
Proof.
  unfold cat_lit_ok. intro H.
  apply andb_true_iff in H as [_ H].
  destruct (cat_ro !! (base + Z.of_nat len)%Z) as [b | ] eqn:Hb;
    [ | discriminate ].
  apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H.
  vm_compute. reflexivity.
Qed.

Section UkCatLit.
  Context `{!riscvGS Σ}.

  (* the literal, as the resource vprintf reads *)
  Lemma cat_lit_str (γt : gname) (base : Z) (len : nat) :
    cat_lit_ok base len = true ->
    Z.of_nat len < 2 ^ 31 ->
    cat_rodata γt -∗ utext_str γt base len (cat_lit base).
  Proof.
    intros Hok Hlen. iIntros "#Hro". rewrite /cat_rodata.
    iApply (utext_str_of_img γt cat_ro base len (cat_lit base)).
    - intros j Hj. intro He.
      destruct (cat_lit_ok_body base len j Hok Hj) as (_ & Hnz & _).
      apply Hnz. rewrite He. vm_compute. reflexivity.
    - exact Hlen.
    - intros j Hj. exact (proj1 (cat_lit_ok_body base len j Hok Hj)).
    - exact (cat_lit_ok_nul base len Hok).
    - iExact "Hro".
  Qed.

  Lemma cat_lit_nopct (base : Z) (len : nat) (j : nat) :
    cat_lit_ok base len = true -> (j < len)%nat ->
    bv_unsigned (cat_lit base j) <> 37.
  Proof.
    intros Hok Hj.
    exact (proj2 (proj2 (cat_lit_ok_body base len j Hok Hj))).
  Qed.

End UkCatLit.
