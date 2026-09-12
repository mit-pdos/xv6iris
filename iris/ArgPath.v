(* ArgPath.v -- THE PATH ARGUMENT OF A SYSCALL, READ OFF THE CALLER'S OWN
   IMAGE.  A pure leaf: two definitions, four small lemmas, and nothing
   in [iProp].

   A path-taking syscall ([exec], [open], [mknod], ...) is handed a
   POINTER in a trapframe argument word and [argstr]s the NUL-terminated
   string behind it out of the calling process's user memory.  Every one
   of those syscalls therefore has the same pure question to answer --
   "WHICH list of bytes did argument [k] name?" -- and this file is the
   one answer: [arg_path_of M pv pl].

   WHY THE QUESTION IS WORTH A DEFINITION.  A contract whose walk premise
   is stated at EVERY path ([forall pl, ...]) is honest but useless to a
   caller that wants to know which file it opened: the receipt binds a
   path existentially and ties it to nothing, so a pinned cursor -- sound
   at ONE path -- cannot be handed in and nothing comes back about the
   node the call actually reached.  Stated AT the caller's own argument,
   under the guard [arg_path_of M pv pl], the bundle is owed at the one
   path the caller passed and the receipt names it.  sys_exec was stated
   this way first (SpecSysExec.v's header); open and mknod are stated
   this way too, and this file is what they share.

   THE READING IS A PAIR.  [arg_path_shape] is the string's own shape --
   NUL-free and int-sized, which is what [fetchstr]'s buffer promise
   ([ByteBuf.bb_cstr] plus [maxn]) gives -- and the other two conjuncts
   are the TIE TO THE IMAGE: byte [j] of [pl] is the process's byte at
   [pv + j], counted the copy loop's way ([add_vec_int], modulo 2^64,
   exactly as [SpecCopyinstr.copyinstr_got] counts), with a NUL just past
   the end.  The shape is named separately because a proof usually wants
   one half at a time ([arg_path_of_shape] projects it).

   THE READING IS A FUNCTION of [(M, pv)] ([arg_path_of_uniq]), which is
   what makes the [forall pl, [arg_path_of M pv pl] -* ...] form a
   one-path obligation for a caller that knows its own image, and what
   lets a proof that read ONE path answer a consumer asking at another.

   NO CONTRACT LIVES HERE and nothing here mentions a syscall number:
   [SpecSysExec.v] (as [exec_path_of], an alias), [SysOpenDefs.v] /
   [SpecSysOpen.v] and [SpecSysMknod.v] state their bundles and receipts
   over these, and [UexecExecInst.v]'s key-level rows read them off
   [uvis_M] and the argument word. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
(* the proofs below are ssreflect-style multi-rewrites, which is what the
   proofmode's tactic language gives; nothing here is an [iProp] *)
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvLang.
Require Import ByteBuf.        (* [bb_cstr]: fetchstr's shape promise      *)
Require Import DirentEnc.      (* [bview]: the buffer as a list            *)
Require Import SpecCopyinstr.  (* [copyinstr_got]: the content half        *)
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE READING                                                       *)
(* ===================================================================== *)

Definition arg_path_shape (pl : list (bv 8)) : Prop :=
  (Z.of_nat (length pl) < 2 ^ 31)%Z
  /\ (forall (j : nat) (b : bv 8), pl !! j = Some b ->
        b <> (mword_of_int 0 : mword 8)).

Definition arg_path_of (M : gmap Z (bv 8)) (pv : mword 64)
    (pl : list (bv 8)) : Prop :=
  arg_path_shape pl
  /\ (forall (j : nat) (b : bv 8), pl !! j = Some b ->
        M !! uint (add_vec_int pv (Z.of_nat j)) = Some b)
  /\ M !! uint (add_vec_int pv (Z.of_nat (length pl))) = Some (bv_0 8).

Lemma arg_path_of_shape (M : gmap Z (bv 8)) (pv : mword 64)
    (pl : list (bv 8)) :
  arg_path_of M pv pl -> arg_path_shape pl.
Proof. intros [H _]. exact H. Qed.

(* ===================================================================== *)
(*  2.  THE SUPPLIERS: the buffer argstr handed the syscall               *)
(* ===================================================================== *)

(* the SHAPE supplier.  [bb_cstr] is exactly [fetchstr]'s shape promise
   about that buffer. *)
Lemma arg_path_shape_bview (plen : nat) (pfun : nat -> bv 8) :
  (Z.of_nat plen < 2 ^ 31)%Z -> bb_cstr pfun plen ->
  arg_path_shape (bview plen pfun).
Proof.
  intros Hlen [Hnn _]. split; [ by rewrite bview_length | ].
  intros j b Hb.
  destruct (decide (j < plen)%nat) as [Hj | Hj].
  - rewrite (bview_lookup plen pfun j Hj) in Hb. injection Hb as <-.
    exact (Hnn j Hj).
  - rewrite lookup_ge_None_2 in Hb; [ discriminate | rewrite bview_length; lia ].
Qed.

(* ...and the READING supplier, the one step from the syscall's own
   vocabulary.  [SpecCopyinstr.copyinstr_got] is what [argstr] relays about
   the path buffer ([SpecFetchstr.fetchstr_got]); [bview] is the same buffer
   as a list.

   The step is an index shuffle and nothing else: both sides count bytes as
   [uint (add_vec_int pv j)], the machine's own arithmetic, so there is no
   no-wrap side condition to discharge -- a user may pass any 64-bit pointer
   and the reading is about the addresses the copy loop actually touched.
   [copyinstr_got]'s [j <= plen] range covers the terminator, which is the
   third conjunct here. *)
Lemma arg_path_of_bview (M : gmap Z (bv 8)) (pv : mword 64)
    (plen : nat) (pfun : nat -> bv 8) :
  (Z.of_nat plen < 2 ^ 31)%Z ->
  bb_cstr pfun plen ->
  copyinstr_got M pv pfun plen ->
  arg_path_of M pv (bview plen pfun).
Proof.
  intros Hlen Hcstr Hgot.
  split_and!.
  - exact (arg_path_shape_bview plen pfun Hlen Hcstr).
  - intros j b Hb.
    destruct (decide (j < plen)%nat) as [Hj | Hj].
    + rewrite (bview_lookup plen pfun j Hj) in Hb. injection Hb as <-.
      exact (Hgot j ltac:(lia)).
    + rewrite lookup_ge_None_2 in Hb; [ discriminate | rewrite bview_length; lia ].
  - rewrite bview_length (Hgot plen ltac:(lia)) (proj2 Hcstr).
    f_equal. apply bv_eq. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  3.  THE READING PINS THE PATH                                         *)
(* ===================================================================== *)

(* [arg_path_of M pv] is a FUNCTION of the image and the pointer: the bytes
   below the terminator are [M]'s, the terminator is at [length pl], and the
   shape says no earlier byte is a NUL -- so two readings at one [(M, pv)]
   have the same length and, byte for byte, the same content.  This is what a
   bundle owed at every path the caller MIGHT have passed reduces to at a
   caller whose image is known: the one path it did pass ([PinnedExec.v]
   takes [arg_path_of M pv pl] as its premise and answers the forall through
   this lemma), and what lets a syscall proof that read ONE path answer a
   receipt asked for at another. *)
Lemma arg_path_of_uniq (M : gmap Z (bv 8)) (pv : mword 64)
    (pl1 pl2 : list (bv 8)) :
  arg_path_of M pv pl1 -> arg_path_of M pv pl2 -> pl1 = pl2.
Proof.
  intros (Hs1 & Hb1 & Hn1) (Hs2 & Hb2 & Hn2).
  assert (Hz : bv_0 8 = (mword_of_int 0 : mword 8))
    by (apply bv_eq; vm_compute; reflexivity).
  (* the terminator of the shorter reading is a non-NUL byte of the
     longer one, which its shape forbids *)
  assert (Hcut : forall (q1 q2 : list (bv 8)),
             (forall (j : nat) (b : bv 8), q2 !! j = Some b ->
                M !! uint (add_vec_int pv (Z.of_nat j)) = Some b) ->
             (forall (j : nat) (b : bv 8), q2 !! j = Some b ->
                b <> (mword_of_int 0 : mword 8)) ->
             M !! uint (add_vec_int pv (Z.of_nat (length q1))) = Some (bv_0 8) ->
             (length q2 <= length q1)%nat).
  { intros q1 q2 Hb Hnn Hnul.
    destruct (decide (length q2 <= length q1)%nat) as [Hle | Hgt]; [ exact Hle | ].
    exfalso.
    destruct (lookup_lt_is_Some_2 q2 (length q1) ltac:(lia)) as [b Hbj].
    pose proof (Hb _ _ Hbj) as HM. rewrite Hnul in HM.
    apply Some_inj in HM. rewrite Hz in HM.
    exact (Hnn _ _ Hbj (eq_sym HM)). }
  assert (Hlen : length pl1 = length pl2).
  { pose proof (Hcut pl1 pl2 Hb2 (proj2 Hs2) Hn1) as H12.
    pose proof (Hcut pl2 pl1 Hb1 (proj2 Hs1) Hn2) as H21. lia. }
  apply list_eq. intros j.
  destruct (pl1 !! j) as [b1 |] eqn:H1.
  - destruct (lookup_lt_is_Some_2 pl2 j
                ltac:(rewrite -Hlen; exact (lookup_lt_Some _ _ _ H1)))
      as [b2 H2].
    rewrite H2. f_equal.
    pose proof (Hb1 _ _ H1) as E1. pose proof (Hb2 _ _ H2) as E2.
    rewrite E1 in E2. by apply Some_inj in E2.
  - apply lookup_ge_None in H1. symmetry.
    apply lookup_ge_None_2. lia.
Qed.
