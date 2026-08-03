(* SpecFileclose.v -- the public interface of fileclose, stated independently
   of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

     void fileclose(struct file *f) {
       struct file ff;
       acquire(&ftable.lock);
       if (f->ref < 1) panic("fileclose");
       if (--f->ref > 0) { release(&ftable.lock); return; }
       ff = *f;
       f->ref = 0;
       f->type = FD_NONE;
       release(&ftable.lock);
       if (ff.type == FD_PIPE) pipeclose(ff.pipe, ff.writable);
       else if (ff.type == FD_INODE || ff.type == FD_DEVICE) {
         begin_op(); iput(ff.ip); end_op();
       }
     }

   The CALLER-facing contract is the simple one, and it is stable: a
   reference goes in and nothing comes back.  Everything interesting happens
   inside.  Which of the two arms runs is invisible from outside, and
   deliberately so -- the caller of fileclose neither knows nor cares whether
   it held the last reference.

   The internal split is where the design earns its keep, and it is entirely
   [FileInv]'s two close steps:

   * [--f->ref > 0] (file_close_step): the departing reference's fraction is
     absorbed back into the invariant's leftover [file_rest].  That the
     fraction has somewhere to GO is why the authority's frac component
     tracks outstanding fraction rather than being pinned at 1.
   * [--f->ref == 0] (file_close_last_step): validity forces q = qt = 1, so
     the closer walks away holding fraction 1 of every content cell -- which
     is exactly what licenses the unlocked-looking [ff = *f] read and the
     [f->type = FD_NONE] store, and what will hand [pipeclose]/[iput] the
     pipe or inode reference once [file_payload] lands (stage 2 in
     claude-notes/design/file-table.md).  The slot leaves the authority and
     the free-state invariant (type = FD_NONE) is re-established.

   The [f->ref < 1] panic arm is dead for the same reason as filedup's: the
   caller's [file_ref] puts slot k in the authority's domain.

   WHAT COMES BACK: one [fd_slot].  That is not a decoration -- it is the
   return leg of the conservation law that makes filedup's unchecked
   [f->ref++] safe (FdSlots.v / design/file-table.md).  [ftable_res] holds one
   unit per outstanding reference, so destroying a reference releases exactly
   one, whichever arm ran: at [n >= 2] the slot's [fd_slots n] shrinks to
   [fd_slots (n-1)], and at [n = 1] the whole entry leaves the authority.  The
   caller needs it: sys_close's descriptor is empty afterwards, and an empty
   [ProcInv.ofile_slot] owns its unit itself.

   TWO PROVISIONAL BITS, both flagged rather than hidden:
   * the stack bound below is fileclose's own 8-slot frame plus acquire /
     release; it will GROW once pipeclose / begin_op / iput / end_op have
     specs, since the last-reference arm calls them below this frame.
   * the postcondition is silent about the pipe/inode because stage-1
     [file_ref] carries no payload.  When it does, this contract does not
     change -- fileclose consumes the payload itself. *)
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

Notation FC := KernelSyms.fileclose.

(* fileclose's own frame is 8 slots (addi sp,sp,-64: ra, s0..s3 saved), and
   acquire/release want 10 below that.  PROVISIONAL: the last-reference arm
   also calls begin_op / iput / end_op / pipeclose, whose depths are not yet
   known, so this will grow. *)
Definition fileclose_stack : nat := 18%nat.

Definition wp_fileclose_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (γl γf : gname)
    (k : nat) (q : Qp) (Cf : fcontent)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.fileclose in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (fileclose_stack <= K)%nat ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* a0 is the file being closed *)
  m !!! Regidx (mword_of_int 10 : mword 5) = fnode k ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  is_ftable γl γf -∗
  panic_wp_any -∗
  file_ref γf k q Cf -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p C b -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    fd_slot -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type FILECLOSE.
  Parameter wp_fileclose_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (γl γf : gname)
      (k : nat) (q : Qp) (Cf : fcontent)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) (b : bool),
      wp_fileclose_sconf_body Φ γl γf k q Cf m n eb p C K b.
End FILECLOSE.
