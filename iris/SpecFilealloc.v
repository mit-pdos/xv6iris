(* SpecFilealloc.v -- the public interface of filealloc, stated independently
   of its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     struct file *filealloc(void) {
       struct file *f;
       acquire(&ftable.lock);
       for (f = ftable.file; f < ftable.file + NFILE; f++) {
         if (f->ref == 0) { f->ref = 1; release(&ftable.lock); return f; }
       }
       release(&ftable.lock);
       return 0;
     }

   filealloc reads the [ref] field of EVERY table entry, which is exactly why
   [ftable_res] owns all NFILE of them and no reference ever carries one; and
   it touches no OTHER field of any entry, which is why the scan needs no
   content fraction at all.  What it returns on success is the exclusive
   reference [file_ref γf k 1 Cf]: fraction 1 of all seven content cells, so
   the caller (sys_open, pipealloc) can initialize them with no lock held,
   which is precisely the discipline the real kernel relies on.  The
   [fc_type Cf = FD_NONE] conjunct is the free-slot invariant coming back out
   (fileclose writes FD_NONE before releasing; the BSS starts zeroed).

   Design: claude-notes/design/file-table.md. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import FdSlots FileInv.
Require Import WpLock.
Require Import SpecPanic.
Require Import IntrDefs.
Require Import CpuOwn.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Notation FA := KernelSyms.filealloc.

Section SpecFilealloc.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ}.

  (* filealloc's return value: either the table was full (a0 = 0), or a0 points
     at entry [k] and the caller owns it exclusively and uninitialized.

     THE FAILURE ARM GIVES THE fd_slot BACK.  The unit below pays for a
     reference, and on this arm no reference was created -- the scan ran off
     the end of the table and nothing entered the authority -- so keeping it
     would burn a unit of a CONSERVED supply on a call that did nothing
     (FdSlots.v).  A caller that retries, or that allocates two files and
     must return its whole allowance whichever way the calls went (pipealloc,
     hence sys_pipe), cannot balance its books without this. *)
  Definition filealloc_post (γf : gname) (r : mword 64) : iProp Σ :=
    (⌜r = (zero_reg : mword 64)⌝ ∗ fd_slot
     ∨ ∃ (k : nat) (Cf : fcontent),
         ⌜(k < NFILE)%nat /\ r = fnode k /\ fc_type Cf = FD_NONE⌝ ∗
         file_ref γf k 1 Cf)%I.

End SpecFilealloc.

Definition wp_filealloc_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (γl γf : gname) (m : regfile)
    (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.filealloc in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (* filealloc's own frame is 4 slots (addi sp,sp,-32); acquire/release want 10
     below that. *)
  (14 <= K)%nat ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  is_ftable γl γf -∗
  panic_wp_any -∗
  (* the new reference needs somewhere to live: one fd slot goes into the
     table and comes back out of fileclose. *)
  fd_slot -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p C b -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    filealloc_post γf (mr !!! Regidx (mword_of_int 10 : mword 5)) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type FILEALLOC.
  Parameter wp_filealloc_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (γl γf : gname) (m : regfile)
      (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) (b : bool),
      wp_filealloc_sconf_body Φ γl γf m n eb p C K b.
End FILEALLOC.
