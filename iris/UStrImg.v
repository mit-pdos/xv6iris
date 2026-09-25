(* ===================================================================== *)
(*  UStrImg.v -- THE IMAGE OF A NUL-TERMINATED STRING OF ANY LENGTH (cut  *)
(*  W3; claude-notes/design/filenames.md section 4).                      *)
(*                                                                        *)
(*  The open leaves read a path off a piece of the caller's image ([Img], *)
(*  a map from addresses to bytes) and ask that every map containing it   *)
(*  reads the path ([ArgPath.arg_path_of]).  The landed file leaves built *)
(*  that piece for the ONE-byte name `f` by hand (two inserts).  At a     *)
(*  name of any length it is [str_img pv n f]: the [n] bytes of [f] at    *)
(*  [pv], then the terminator.                                            *)
(*                                                                        *)
(*  Everything here is instance-free: the byte ownership is an arbitrary  *)
(*  [Φ] over any BI ([str_img_sep]), so a caller instantiates it at its   *)
(*  own [ubyteq]/[utext] inside its own section and no ghost class is     *)
(*  generalized here.                                                     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.bi Require Import bi big_op.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvExtras.
Require Import UserBits UmodeArith UmodeAbi.   (* [uint_add_vec_int_small], [moi_small], [ubyte0], [uimg_sub] *)
Require Import ArgPath.                        (* [arg_path_of] *)
Import Defs.

Local Open Scope Z_scope.

Definition str_cells (pv : Z) (n : nat) (f : nat -> bv 8) : list (Z * bv 8) :=
  (fun j : nat => (pv + Z.of_nat j, f j)) <$> seq 0 n.

Definition str_img (pv : Z) (n : nat) (f : nat -> bv 8) : gmap Z (bv 8) :=
  <[pv + Z.of_nat n := ubyte0]> (list_to_map (str_cells pv n f)).

Lemma str_cells_keys (pv : Z) (n : nat) (f : nat -> bv 8) :
  base.NoDup (str_cells pv n f).*1.
Proof using.
  rewrite /str_cells -list_fmap_compose.
  apply NoDup_fmap_2_strong; [| apply NoDup_seq].
  intros x y _ _ Hxy. cbn in Hxy. lia.
Qed.

Lemma str_cells_key_ne (pv : Z) (n : nat) (f : nat -> bv 8) :
  pv + Z.of_nat n ∉ (str_cells pv n f).*1.
Proof using.
  rewrite /str_cells -list_fmap_compose. intros Hin.
  apply elem_of_list_fmap in Hin as (j & Hj & Hs).
  apply elem_of_seq in Hs. cbn in Hj. lia.
Qed.

(* every cell the image holds is a byte of the string or its terminator *)
Lemma str_img_lookup (pv : Z) (n : nat) (f : nat -> bv 8) (a : Z) (b : bv 8) :
  str_img pv n f !! a = Some b ->
  (a = pv + Z.of_nat n /\ b = ubyte0)
  \/ exists j : nat, (j < n)%nat /\ a = pv + Z.of_nat j /\ b = f j.
Proof using.
  rewrite /str_img lookup_insert_Some. intros [[<- <-] | [_ Hl]]; [by left |].
  right. apply elem_of_list_to_map_2 in Hl.
  apply elem_of_list_fmap in Hl as (j & Hj & Hs).
  apply elem_of_seq in Hs. injection Hj as -> ->. exists j.
  split; [lia | split; reflexivity].
Qed.

Lemma str_img_byte (pv : Z) (n : nat) (f : nat -> bv 8) (j : nat) :
  (j < n)%nat -> str_img pv n f !! (pv + Z.of_nat j) = Some (f j).
Proof using.
  intros Hj. rewrite /str_img lookup_insert_ne; [| lia].
  apply elem_of_list_to_map_1; [apply str_cells_keys |].
  rewrite /str_cells. apply elem_of_list_fmap. exists j. split; [reflexivity |].
  apply elem_of_seq. lia.
Qed.

Lemma str_img_nul (pv : Z) (n : nat) (f : nat -> bv 8) :
  str_img pv n f !! (pv + Z.of_nat n) = Some ubyte0.
Proof using. rewrite /str_img. apply lookup_insert. Qed.

(* THE OWNERSHIP: the string's bytes and its terminator ARE the image's
   cells, at any per-cell predicate *)
Lemma str_img_sep {PROP : bi} (Φ : Z -> bv 8 -> PROP) (pv : Z) (n : nat)
    (f : nat -> bv 8) :
  ([∗ list] j ∈ seq 0 n, Φ (pv + Z.of_nat j) (f j)) ∗ Φ (pv + Z.of_nat n) ubyte0
  ⊣⊢ [∗ map] a ↦ b ∈ str_img pv n f, Φ a b.
Proof using.
  rewrite /str_img big_sepM_insert.
  2: { apply not_elem_of_list_to_map_1. apply str_cells_key_ne. }
  rewrite big_sepM_list_to_map; [| apply str_cells_keys].
  rewrite /str_cells big_sepL_fmap /=.
  iSplit; iIntros "[A B]"; iFrame.
Qed.

(* the machine's address arithmetic below the image bound *)
Lemma str_uint_avi (p k : Z) :
  0 <= p < 2 ^ 38 -> 0 <= k < 2 ^ 31 ->
  uint (add_vec_int (mword_of_int p : mword 64) k) = p + k.
Proof using.
  intros Hp Hk.
  assert (Hpu : bv_unsigned (mword_of_int p : mword 64) = p)
    by (apply moi_small; unfold Z64; lia).
  rewrite uint_unsigned.
  rewrite (uint_add_vec_int_small (mword_of_int p : mword 64) k
             ltac:(lia) ltac:(rewrite Hpu; lia)).
  rewrite Hpu. reflexivity.
Qed.

(* THE READING: any map containing the image reads the path *)
Lemma str_img_path (M : gmap Z (bv 8)) (pv : Z) (pl : list (bv 8))
    (f : nat -> bv 8) :
  0 <= pv < 2 ^ 38 ->
  arg_path_shape pl ->
  (forall j : nat, (j < length pl)%nat -> pl !! j = Some (f j)) ->
  uimg_sub (str_img pv (length pl) f) M ->
  arg_path_of M (mword_of_int pv : mword 64) pl.
Proof using.
  intros Hpv Hsh Hf Hsub. pose proof Hsh as [Hlen _].
  split; [exact Hsh |]. split.
  - intros j b Hj.
    pose proof (lookup_lt_Some _ _ _ Hj) as Hjl.
    rewrite (str_uint_avi pv (Z.of_nat j) Hpv ltac:(lia)).
    apply Hsub. rewrite (str_img_byte pv (length pl) f j Hjl).
    rewrite (Hf j Hjl) in Hj. by injection Hj as ->.
  - rewrite (str_uint_avi pv (Z.of_nat (length pl)) Hpv ltac:(lia)).
    apply Hsub. rewrite str_img_nul. f_equal. apply bv_eq. vm_compute. reflexivity.
Qed.
