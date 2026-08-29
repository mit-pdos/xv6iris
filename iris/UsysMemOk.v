(* ===================================================================== *)
(* UsysMemOk.v -- WHICH USER BYTES A SYSCALL MAY HAVE MOVED, restated on   *)
(* the TRAPFRAME WORD LIST, so that a file below the kernel proofs can     *)
(* import it.                                                              *)
(*                                                                         *)
(* See claude-notes/design/user-wp-slot.md, "The ruled design for the      *)
(* user/kernel trap contract".  [SpecSyscall.sysc_mem_ok V V' M M'] is the *)
(* kernel dispatcher's table -- keyed by the syscall number in the a7 word *)
(* of the entry trapframe -- and it is stated over [pprivate], which lives *)
(* far above the user-execution tier.  [usys_mem_ok] below is THE SAME     *)
(* TABLE stated over the word list alone (plus the return value, which the *)
(* exec row needs), and [UsysMemOkSpec.sysc_mem_ok_usys] -- above          *)
(* SpecSyscall.v -- is the proof that the two agree, so the kernel can     *)
(* discharge this one from the dispatcher's post at milestone J.           *)
(*                                                                         *)
(* THE PERMISSION MAP RIDES BESIDE THE IMAGE.  The key carries the        *)
(* user-visible per-page permission view ([UserPerm.perm_of], the leaf   *)
(* bits with the lazy pages filled in RW), so every row also says how    *)
(* [π] moves: unchanged on the sixteen quiet entries, the four windows   *)
(* and the exec failure arm; sbrk's row is [usys_sbrk_perm] -- unchanged,*)
(* grown by a set of pages at {X := false; W := true} (the lazy fill of  *)
(* the new live pages; [vmfault] later maps exactly that), or shrunk by  *)
(* a set of pages.  The page sets are EXISTENTIAL for the same reason    *)
(* sbrk's size is: the word list does not carry [pv_sz].                 *)
(*                                                                         *)
(* THE ROWS, one for one with [sysc_mem_ok]:                               *)
(*   exec (7)   -- the FAILURE arm only: [r = -1] and the image is intact. *)
(*                 A successful exec never returns to this WP at all: the  *)
(*                 new program's WP is MINTED by exec from the new         *)
(*                 trapframe and image, so the success arm has no row.     *)
(*   sbrk (12)  -- the three arms of [SpecSyscall.sysc_sbrk_img] at an     *)
(*                 EXISTENTIAL new size: exactly what the kernel's table   *)
(*                 says (its size is the outgoing record's [pv_sz], which  *)
(*                 the word list does not carry).  Tying the size to the   *)
(*                 return value ([r + a0] on success) is sbrk's own        *)
(*                 contract's refinement, not this table's.               *)
(*   wait/pipe/read/fstat -- a [umem_wr] window based at the argument the *)
(*                 kernel's [sysc_window] names.                           *)
(*   the other sixteen -- [M' = M].                                        *)
(*                                                                         *)
(* PURE, and deliberately NOT importing SpecSyscall (whose cone is the     *)
(* whole kernel).  The word-index map is ProcGeom.v's ([tf_arg_idx],       *)
(* [tf_epc_idx]); the image algebra is UserPtTree.v's ([umem_wr],          *)
(* [umem_grow], [umem_del]); [pgroundup] on words is ProcPtOwn.v's.        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvLang.
Require Import ProcGeom.     (* [tf_arg_idx] / [tf_epc_idx] / [TFWORDS] *)
Require Import UserPtTree.   (* [umem_wr] / [umem_grow] / [umem_del] *)
Require Import ProcPtOwn.    (* [pgroundup] on words *)
Require Import UserPerm.     (* [uperm] / [uperm_rw] -- the permission view *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(* SS1 The number, read as the dispatcher reads it.                        *)
(*                                                                         *)
(* [p->trapframe->a7] as a SIGNED 32-bit value (the C reads it into an     *)
(* [int]); trapframe word [tf_arg_idx 7] = 21.  Definitionally             *)
(* [SpecSyscall.sysc_num V] at [tf := pv_tf V].                            *)
(* ===================================================================== *)
Definition usys_num (tf : list (mword 64)) : Z :=
  bv_signed (subrange_vec_dec (tf !!! tf_arg_idx 7) 31 0 : mword 32).

(* the syscall numbers this table names (kernel/syscall.h) *)
Definition USYS_fork : Z := 1.
Definition USYS_exit : Z := 2.
Definition USYS_exec : Z := 7.
Definition USYS_sbrk : Z := 12.

(* ===================================================================== *)
(* SS2 The table.                                                          *)
(* ===================================================================== *)

(* which ARGUMENT the four copyout entries base their window at
   (verbatim [SpecSyscall.sysc_window]) *)
Definition usys_window (n : Z) : option nat :=
  if decide (n = 3) then Some 0%nat        (* wait  -- int *status     *)
  else if decide (n = 4) then Some 0%nat   (* pipe  -- int fd[2]       *)
  else if decide (n = 5) then Some 1%nat   (* read  -- char *buf       *)
  else if decide (n = 8) then Some 1%nat   (* fstat -- struct stat *st *)
  else None.

(* sbrk's three arms at new size [szv'] (verbatim [SpecSyscall.sysc_sbrk_img]) *)
Definition usys_sbrk_img (M M' : gmap Z (bv 8)) (szv' : mword 64) : Prop :=
  M' = M
  \/ M' = umem_grow M (uint szv')
  \/ exists np : nat,
       M' = umem_del M (uint (ProcPtOwn.pgroundup szv')) (4096 * np).

(* how the permission map may move under sbrk: not at all, grown by some
   pages at RW (the lazy fill of the new live pages), or shrunk by some
   pages *)
Definition usys_sbrk_perm (π π' : gmap (mword 27) uperm) : Prop :=
  π' = π
  \/ (exists P : gset (mword 27), π' = π ∪ gset_to_gmap uperm_rw P)
  \/ (exists D : gset (mword 27), π' = base.filter (fun kv : mword 27 * uperm => kv.1 ∉ D) π).

(* THE TABLE: syscall [n], entered with trapframe words [tf], returned
   [r], may take the image from [M] to [M'] and the permission map from
   [π] to [π']. *)
Definition usys_mem_ok (n : Z) (tf : list (mword 64)) (r : mword 64)
    (M : gmap Z (bv 8)) (π : gmap (mword 27) uperm)
    (M' : gmap Z (bv 8)) (π' : gmap (mword 27) uperm) : Prop :=
  if decide (n = USYS_exec) then
    r = (mword_of_int (-1) : mword 64) /\ M' = M /\ π' = π
  else if decide (n = USYS_sbrk) then
    (exists szv' : mword 64, usys_sbrk_img M M' szv') /\ usys_sbrk_perm π π'
  else match usys_window n with
       | Some i => (exists (d : nat) (bs : nat -> bv 8),
                      M' = umem_wr M (tf !!! tf_arg_idx i) d bs) /\ π' = π
       | None   => M' = M /\ π' = π
       end.

(* the sixteen quiet entries, by name: what a program calling one of them
   learns.  Stated for the row shape rather than per number so a program
   proof picks it up with one [apply] after [vm_compute]-ing the number. *)
Lemma usys_mem_ok_quiet (n : Z) (tf : list (mword 64)) (r : mword 64)
    (M M' : gmap Z (bv 8)) (π π' : gmap (mword 27) uperm) :
  n <> USYS_exec -> n <> USYS_sbrk -> usys_window n = None ->
  usys_mem_ok n tf r M π M' π' -> M' = M /\ π' = π.
Proof.
  intros Hne Hns Hw H. unfold usys_mem_ok in H.
  destruct (decide (n = USYS_exec)); [contradiction |].
  destruct (decide (n = USYS_sbrk)); [contradiction |].
  rewrite Hw in H. exact H.
Qed.

(* the permission map is untouched by every entry but sbrk *)
Lemma usys_mem_ok_perm (n : Z) (tf : list (mword 64)) (r : mword 64)
    (M M' : gmap Z (bv 8)) (π π' : gmap (mword 27) uperm) :
  n <> USYS_sbrk ->
  usys_mem_ok n tf r M π M' π' -> π' = π.
Proof.
  intros Hns H. unfold usys_mem_ok in H.
  destruct (decide (n = USYS_exec)); [exact (proj2 (proj2 H)) |].
  destruct (decide (n = USYS_sbrk)); [contradiction |].
  destruct (usys_window n); exact (proj2 H).
Qed.

(* ===================================================================== *)
(* SS3 THE RESUME TRAPFRAME after a returning syscall: epc advanced past   *)
(* the ecall, a0 := the return value.  This is what the kernel's trap loop *)
(* does to the process's trapframe between the ecall and the sret          *)
(* ([usertrap]: [p->trapframe->epc += 4]; [syscall]: [p->trapframe->a0 =   *)
(* syscalls[num]()]), so it is the key the returned slot is stated at.     *)
(* ===================================================================== *)
Definition bump_tf (tf : list (mword 64)) (r : mword 64) : list (mword 64) :=
  <[tf_arg_idx 0 := r]> (<[tf_epc_idx := add_vec_int (tf !!! tf_epc_idx) 4]> tf).

Lemma bump_tf_length (tf : list (mword 64)) (r : mword 64) :
  length (bump_tf tf r) = length tf.
Proof. unfold bump_tf. rewrite !length_insert. reflexivity. Qed.

(* the words the resume state reads, through the bump *)
Lemma bump_tf_epc (tf : list (mword 64)) (r : mword 64) :
  (tf_epc_idx < length tf)%nat ->
  bump_tf tf r !!! tf_epc_idx = add_vec_int (tf !!! tf_epc_idx) 4.
Proof.
  intros Hl. unfold bump_tf.
  rewrite list_lookup_total_insert_ne; [ | unfold tf_arg_idx, tf_epc_idx; lia ].
  apply list_lookup_total_insert. exact Hl.
Qed.

Lemma bump_tf_a0 (tf : list (mword 64)) (r : mword 64) :
  (tf_arg_idx 0 < length tf)%nat ->
  bump_tf tf r !!! tf_arg_idx 0 = r.
Proof.
  intros Hl. unfold bump_tf.
  apply list_lookup_total_insert. rewrite length_insert. exact Hl.
Qed.

Lemma bump_tf_other (tf : list (mword 64)) (r : mword 64) (i : nat) :
  i <> tf_arg_idx 0 -> i <> tf_epc_idx ->
  bump_tf tf r !!! i = tf !!! i.
Proof.
  intros Ha He. unfold bump_tf.
  rewrite list_lookup_total_insert_ne; [ | exact (not_eq_sym Ha) ].
  rewrite list_lookup_total_insert_ne; [ reflexivity | exact (not_eq_sym He) ].
Qed.

(* the number is not moved by the bump (a7 is word 21, not 14 or 3) *)
Lemma bump_tf_num (tf : list (mword 64)) (r : mword 64) :
  usys_num (bump_tf tf r) = usys_num tf.
Proof.
  unfold usys_num. rewrite bump_tf_other; [ reflexivity | | ];
    unfold tf_arg_idx, tf_epc_idx; lia.
Qed.

(* ===================================================================== *)
(* SS4 The scause value of an ecall from U-mode: interrupt bit 0,          *)
(* exception code 8 ([E_U_EnvCall]).  The user-execution contract's case   *)
(* analysis is on this value; the U-mode engine's trap tower delivers it   *)
(* as [UserTrap.utrap_scause (Exception (E_U_EnvCall tt)) sc0], and the    *)
(* bridge between the two spellings is the engine's to prove where it      *)
(* raises the trap (UserTrap.v is not in this file's cone).                *)
(* ===================================================================== *)
Definition uecall_scause : mword 64 := mword_of_int 8.
