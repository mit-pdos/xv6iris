(* FileOffCell.v -- THE FILE ENTRY'S ADDRESSES AND ITS [off] CELL, BELOW THE
   OFF BOX (tso-cutover r25 shapes, 2026-09-02; plan §9 items 16/17).

   Split out of FileInvDefs.v for one reason: [OffBox.v] (the third CtxBox
   instance, R4b) needs [off_resident] -- the one cell it boxes -- and
   FileInvDefs.v needs OffBox's rows in [fslot]'s allocated arm and in
   [file_core_off]'s FD_INODE arm (the fourth and fifth final shapes).  So
   the cell and the addresses it is computed from live here, both files
   import this one, and FileInvDefs [Require Export]s it so that no consumer
   changes an import.  Nothing here is new; the text is FileInvDefs.v's. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own.   (* [iProp] *)
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvExtras.
Require Import ArrCursor.
Require Import BioDefs.    (* [BSIZE] *)
Require Import InodeInv.   (* [MAXFILE] *)
From Kernel Require KernelSyms.
Require Import TsoCtx.
Local Open Scope Z_scope.

Definition file_stride : Z := 40.               (* the loop's [addi s1,s1,40] *)
Definition file_base : Z := KernelSyms.ftable + 24.

(* the [k]th entry, &ftable.file[k].  [fnode NFILE] is one past the last entry
   -- which is where the next global (<disk>) starts, and is the literal end
   pointer filealloc's scan compares its cursor against. *)
Definition fnode (k : nat) : mword 64 := acur file_base file_stride k.

(* the field addresses, in the EXACT [add_vec base (sign_extend' 64 imm)] form
   the instructions compute, so a load/store address unifies with the cell
   without rewriting. *)
Definition foff_of (a : mword 64) (i : Z) : mword 64 :=
  add_vec a (sign_extend' 64 (mword_of_int i : mword 12)).

Definition a_ftype     (k : nat) : mword 64 := fnode k.
Definition a_fref      (k : nat) : mword 64 := foff_of (fnode k) 4.
Definition a_freadable (k : nat) : mword 64 := foff_of (fnode k) 8.
Definition a_fwritable (k : nat) : mword 64 := foff_of (fnode k) 9.
Definition a_fpipe     (k : nat) : mword 64 := foff_of (fnode k) 16.
Definition a_fip       (k : nat) : mword 64 := foff_of (fnode k) 24.
Definition a_foff      (k : nat) : mword 64 := foff_of (fnode k) 32.
Definition a_fmajor    (k : nat) : mword 64 := foff_of (fnode k) 36.

(* [f->off] is 4-aligned for EVERY [k]: [ftable] is 16-aligned, the entry
   stride is 40 and the field offset 32, and the wrap-around modulus is a
   multiple of 4.  The visibility-free cell [off_free] carries this fact, and
   the last close has no word cell to read it from (r25 pass 1, reviewer 1). *)
Lemma a_foff_aligned (k : nat) : is_aligned_paddr (Physaddr (a_foff k)) 4 = true.
Proof.
  unfold is_aligned_paddr. apply Z.eqb_eq. rewrite uint_unsigned.
  unfold a_foff, foff_of. rewrite add_vec64_unsigned.
  assert (H32 : bv_unsigned (sign_extend' 64 (mword_of_int 32 : mword 12)) = 32)
    by (vm_compute; reflexivity).
  rewrite H32. unfold fnode, acur. rewrite moi64_unsigned.
  assert (Hm : bv_modulus 64 = 18446744073709551616) by reflexivity.
  unfold bv_wrap. rewrite Hm.
  unfold file_base, file_stride, KernelSyms.ftable.
  rewrite Z.rem_mod_nonneg; [| apply Z.mod_pos_bound; lia | lia].
  Z.div_mod_to_equations. lia.
Qed.


Definition off_wf (v : mword 32) : Prop :=
  bv_unsigned v <= Z.of_nat MAXFILE * Z.of_nat BSIZE.

Lemma off_wf_zero : off_wf (mword_of_int 0 : mword 32).
Proof.
  rewrite /off_wf.
  assert (Hz : bv_unsigned (mword_of_int 0 : mword 32) = 0) by reflexivity.
  rewrite Hz. unfold MAXFILE, BSIZE. lia.
Qed.

(* an offset in range is BELOW int range, which is what makes the [lw] that
   loads it read the literal (and readi's [off + n < 2^31] premise
   dischargeable from a bound on [n] alone). *)
Lemma off_wf_lt31 (v : mword 32) : off_wf v -> bv_unsigned v < 2 ^ 31.
Proof.
  rewrite /off_wf. unfold MAXFILE, BSIZE. intro H.
  assert (E : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  rewrite E. lia.
Qed.

Section FileOffCell.
  Context `{!riscvGS Σ}.
  Context `{XI : CurCtx}.

  (* the resident cell, wf -- what the off box holds while a file's [f->off]
     is not checked out (OffBox.off_hdr), and what the free slot row holds *)
  Definition off_resident (k : nat) : iProp Σ :=
    (∃ v : mword 32, a_foff k ↦₄ v ∗ ⌜off_wf v⌝)%I.
End FileOffCell.
