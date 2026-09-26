(* ===================================================================== *)
(* UkSeccLit.v -- seccomp's four string LITERALS and its MASK LITERAL.    *)
(*                                                                        *)
(* The strings are cut out of the read-only image at a concrete base and  *)
(* length ([UkCatLit.v]'s mould, at [seccomp_ro]); each is decided by one *)
(* [vm_compute] of [secc_lit_ok] (or of [secc_lit_nul], for the one with  *)
(* a '%s').  Their addresses are the ones main's auipc/addi pairs         *)
(* compute ([uis_seccomp_4e]/[_52] etc.: site + (0x1 << 12) + imm):       *)
(*   0x950  "usage: seccomp prog [args...]\n"   30 bytes  (0x4e, -1790)   *)
(*   0x978  "seccomp: fork failed\n"            21 bytes  (0x62, -1770)   *)
(*   0x990  "seccomp: seccomp failed\n"         24 bytes  (0x76, -1766)   *)
(*   0x9b0  "seccomp: exec %s failed\n"         24 bytes  (0x38, -1672)   *)
(*                                                                        *)
(* THE MASK is the value [lui a0,0xffe18 ; addi a0,a0,-65] at main+0x1c   *)
(* builds, spelled at the very immediates [uis_seccomp_1c]/[uis_seccomp_20] *)
(* state, so a walk's register reads it by conversion and a moved         *)
(* immediate breaks the walk rather than this lemma.  [secc_mask_masked]  *)
(* is THE ONE PLACE THE BINARY'S LITERAL ENTERS the seccomp proof         *)
(* (design/seccomp.md SS1, SS7): row 23 ANDs it into the full mask, and   *)
(* the result clears all six numbers of [UexecSecc.secc_B].               *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvExtras.
Require Import UmodeAbi UmodeArith.
Require Import UserHeap.
Require Import WpMmodeLeafBase. (* [luival] *)
Require Import ProcDefs.        (* [secc_all] *)
Require Import UexecSecc.       (* [secc_masked] *)
Require Import UCodeSeccomp.
Require Import StringBytes LineWords ProgTree.   (* [sb], [wl_nl] *)
Require User.SeccompSyms User.SeccompInstrs.
Local Open Scope Z_scope.
Import Defs.

(* the byte function of the literal based at [base] *)
Definition secc_lit (base : Z) : nat -> mword 8 :=
  fun j => default (bv_0 8) (seccomp_ro !! (base + Z.of_nat j)%Z).

(* ...and the whole of what makes it a printable C string *)
Definition secc_lit_ok (base : Z) (len : nat) : bool :=
  forallb (fun j => match seccomp_ro !! (base + Z.of_nat j)%Z with
                    | Some b => negb (Z.eqb (bv_unsigned b) 0)
                                && negb (Z.eqb (bv_unsigned b) 37)
                    | None => false
                    end)
          (seq 0 len)
  && match seccomp_ro !! (base + Z.of_nat len)%Z with
     | Some b => Z.eqb (bv_unsigned b) 0
     | None => false
     end.

Lemma secc_lit_ok_body (base : Z) (len : nat) (j : nat) :
  secc_lit_ok base len = true -> (j < len)%nat ->
  seccomp_ro !! (base + Z.of_nat j)%Z = Some (secc_lit base j)
  /\ bv_unsigned (secc_lit base j) <> 0
  /\ bv_unsigned (secc_lit base j) <> 37.
Proof using .
  unfold secc_lit_ok, secc_lit. intros H Hj.
  apply andb_true_iff in H as [H _].
  rewrite forallb_forall in H.
  specialize (H j ltac:(apply in_seq; lia)).
  destruct (seccomp_ro !! (base + Z.of_nat j)%Z) as [b | ] eqn:Hb;
    [ | discriminate ].
  apply andb_true_iff in H as [H0 H37].
  apply negb_true_iff, Z.eqb_neq in H0.
  apply negb_true_iff, Z.eqb_neq in H37.
  cbn [default]. split; [ reflexivity | ]. split; assumption.
Qed.

Lemma secc_lit_ok_nul (base : Z) (len : nat) :
  secc_lit_ok base len = true ->
  seccomp_ro !! (base + Z.of_nat len)%Z = Some ubyte0.
Proof using .
  unfold secc_lit_ok. intro H.
  apply andb_true_iff in H as [_ H].
  destruct (seccomp_ro !! (base + Z.of_nat len)%Z) as [b | ] eqn:Hb;
    [ | discriminate ].
  apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H.
  vm_compute. reflexivity.
Qed.


Section UkSeccLit.
  Context `{!riscvGS Σ}.

  (* the literal, as the resource vprintf reads *)
  Lemma secc_lit_str (γt : gname) (base : Z) (len : nat) :
    secc_lit_ok base len = true ->
    Z.of_nat len < 2 ^ 31 ->
    seccomp_rodata γt -∗ utext_str γt base len (secc_lit base).
  Proof using .
    intros Hok Hlen. iIntros "#Hro". rewrite /seccomp_rodata.
    iApply (utext_str_of_img γt seccomp_ro base len (secc_lit base)).
    - intros j Hj. intro He.
      destruct (secc_lit_ok_body base len j Hok Hj) as (_ & Hnz & _).
      apply Hnz. rewrite He. vm_compute. reflexivity.
    - exact Hlen.
    - intros j Hj. exact (proj1 (secc_lit_ok_body base len j Hok Hj)).
    - exact (secc_lit_ok_nul base len Hok).
    - iExact "Hro".
  Qed.

  Lemma secc_lit_nopct (base : Z) (len : nat) (j : nat) :
    secc_lit_ok base len = true -> (j < len)%nat ->
    bv_unsigned (secc_lit base j) <> 37.
  Proof using .
    intros Hok Hj.
    exact (proj2 (proj2 (secc_lit_ok_body base len j Hok Hj))).
  Qed.

End UkSeccLit.

(* ---- the four literals ---------------------------------------------- *)
Lemma secc_lit_usage_ok : secc_lit_ok 0x950 30%nat = true.
Proof using . vm_compute. reflexivity. Qed.
Lemma secc_lit_fork_ok : secc_lit_ok 0x978 21%nat = true.
Proof using . vm_compute. reflexivity. Qed.
Lemma secc_lit_secc_ok : secc_lit_ok 0x990 24%nat = true.
Proof using . vm_compute. reflexivity. Qed.

(* the exec diagnostic has its '%s' at 14..15: the prefix and the suffix
   are directive-free, and the whole is a NUL-terminated string *)
Lemma secc_lit_exec_pre : @map nat (bv 8) (secc_lit 0x9b0) (seq 0 14) = sb "seccomp: exec ".
Proof using . vm_compute. reflexivity. Qed.
Lemma secc_lit_exec_pct :
  bv_unsigned (secc_lit 0x9b0 14) = 37 /\ bv_unsigned (secc_lit 0x9b0 15) = 115.
Proof using . vm_compute. split; reflexivity. Qed.
Lemma secc_lit_exec_post : @map nat (bv 8) (secc_lit 0x9b0) (seq 16 7) = sb " failed".
Proof using . vm_compute. reflexivity. Qed.
Lemma secc_lit_exec_nl : @map nat (bv 8) (secc_lit 0x9b0) (seq 23 1) = [wl_nl].
Proof using . vm_compute. reflexivity. Qed.
Lemma secc_lit_exec_nul : seccomp_ro !! (0x9b0 + 24) = Some ubyte0.
Proof using . vm_compute. first [ reflexivity | f_equal; apply bv_eq; reflexivity ]. Qed.

(* ---- THE MASK ------------------------------------------------------- *)
Definition secc_mask_lit : mword 64 :=
  add_vec (luival (mword_of_int 1048088 : mword 20))
    (sign_extend' 64 (mword_of_int 4031 : mword 12)).

Lemma secc_mask_lit_val : bv_unsigned secc_mask_lit = 0xffffffffffe17fbf.
Proof using . vm_compute. reflexivity. Qed.

(* row 23's new mask, [UsysMemOk.usys_secc_ok] at the full mask *)
Lemma secc_mask_masked : secc_masked (and_vec secc_all secc_mask_lit).
Proof using .
  intros n Hn. rewrite and_vec64_unsigned secc_mask_lit_val.
  rewrite elem_of_list_In in Hn. cbn in Hn.
  destruct Hn as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
    vm_compute; reflexivity.
Qed.
