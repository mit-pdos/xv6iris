(* ===================================================================== *)
(* UsysMemOkSpec.v -- [UsysMemOk.usys_mem_ok] IS [SpecSyscall.sysc_mem_ok] *)
(* read on the trapframe word list: the one lemma that lets the kernel     *)
(* discharge the user-side table from the dispatcher's own post           *)
(* (milestone J).  Above SpecSyscall.v on purpose; nothing below it may   *)
(* import this file.                                                      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvLang.
Require Import ProcGeom ProcDefs.
Require Import SpecSyscall.
Require Import UsysMemOk.
Local Open Scope Z_scope.

(* the number the dispatcher reads is the number the table is keyed by *)
Lemma sysc_num_usys (V : pprivate) : sysc_num V = usys_num (pv_tf V).
Proof. reflexivity. Qed.

(* Every entry but exec: the kernel's table implies the user's, at any
   return value.  exec is excluded because its success arm never returns
   to this WP at all (the new program's WP is a kernel mint), and its
   failure arm's [r = -1] is the dispatcher's return-value fact, which
   [sysc_mem_ok] does not carry. *)
Lemma sysc_mem_ok_usys (V V' : pprivate) (M M' : gmap Z (bv 8)) (r : mword 64) :
  sysc_num V <> 7 ->
  sysc_mem_ok V V' M M' ->
  usys_mem_ok (sysc_num V) (pv_tf V) r M M'.
Proof.
  intros Hne H. unfold sysc_mem_ok in H. unfold usys_mem_ok, USYS_exec, USYS_sbrk.
  destruct (decide (sysc_num V = 7)); [ contradiction | ].
  destruct (decide (sysc_num V = 12)).
  { exists (pv_sz V'). exact H. }
  exact H.
Qed.
