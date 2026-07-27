(* SpecSysClose.v -- the public interface of sys_close(), stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     uint64 sys_close(void) {
       int fd; struct file *f;
       if (argfd(0, &fd, &f) < 0) return -1;
       myproc()->ofile[fd] = 0;
       fileclose(f);
       return 0;
     }

   @ KernelSyms.sys_close = 0x80004cb2, 24 instructions (see
   WpSysCloseDecode.v for the listing).

   THE POINT OF THIS SPEC.  sys_close is the first proof in which a
   [FileInv.file_ref] LEAVES the process: [proc_priv]'s descriptor [fd] gives
   up the reference it was holding, the descriptor becomes null, and
   fileclose consumes the reference.  Three resources have to line up for
   that, and they are exactly the three ends of the file-table design
   (claude-notes/design/file-table.md):

     - [ProcInv.proc_priv_ofile] borrows descriptor [fd] out of the
       thread-local fd table -- no lock, because the table IS thread-local --
       and takes back a descriptor holding a DIFFERENT value;
     - the reference inside it is what [SpecFileclose] consumes;
     - the [fd_slot] fileclose returns is what re-establishes the EMPTY
       descriptor's own conservation obligation ([ProcInv.ofile_slot]'s left
       disjunct).  Without it the postcondition below would be unprovable --
       which is the whole point of that unit existing.

   The [sd x0,0(a0)] store lands BEFORE the fileclose call, so there is a
   window in which the descriptor is null and the reference is loose in a
   register.  That is not a hole for the same reason sys_dup's window is not
   (design/file-table.md): no other core can reach this process's fd table,
   so the intermediate state never has to be an invariant -- it only has to
   be re-established by the time sys_close returns.

   DETERMINISM.  Which arm runs is a function of the syscall argument and the
   process's own descriptor array, both of which the caller knows, so the
   postcondition says so ([SpecArgfd.arg_fd]) rather than offering an
   unconstrained "closed it, or didn't": a kernel that always returned -1
   would not satisfy this spec. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpLock.
Require Import SpecPanic.
Require Import ProcGeom CpuOwn.
Require Import FdSlots FileInv ProcInv.
Require Import SpecArgfd.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

Notation SCL := KernelSyms.sys_close.

(* sys_close's own frame is 4 slots (addi sp,sp,-32); below it argfd wants
   24, fileclose 18 and myproc 10. *)
Definition sys_close_stack : nat := 28%nat.

Section SpecSysClose.
  Context `{!riscvGS Σ, !lockG Σ, !fileG Σ, !fdslotG Σ}.

  (* sys_close's result, keyed by the returned a0.  In the success case the
     descriptor named by the argument is null and one file reference is
     gone; in the failure case nothing at all has happened. *)
  Definition sys_close_post (γf : gname) (p : mword 64) (pid : mword 32)
      (V : pprivate) (v : mword 64) (r : mword 64) : iProp Σ :=
    (⌜r = (mword_of_int (-1) : mword 64) /\ arg_fd v (pv_ofile V) = None⌝ ∗
       proc_priv γf p pid V
     ∨ ∃ (fd : nat) (fv : mword 64),
         ⌜r = (zero_reg : mword 64) /\ arg_fd v (pv_ofile V) = Some (fd, fv)⌝ ∗
         proc_priv γf p pid (upd_ofile V fd (zero_reg : mword 64)))%I.

End SpecSysClose.

Definition wp_sys_close_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γl γf : gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (v : mword 64) (pid : mword 32) (V : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_close in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the hart id is the ambient CpuId (myproc / acquire convention) *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (* sys_close reads syscall argument 0, out of the trapframe page
     [proc_priv] carries *)
  pv_tf V !! tf_arg_idx 0 = Some v ->
  (* push_off's transient noff increment stays in int range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (sys_close_stack <= av)%nat ->
  sie_cap_gpr γ m av -∗
  cpu_own γ n eb p C -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  is_ftable γl γf -∗
  panic_wp -∗
  proc_priv γf p pid V -∗
  ( ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr γ mf av -∗
      cpu_own γ n eb p C -∗
      pc_is ret_tgt -∗
      sys_close_post γf p pid V v (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type SYSCLOSE.
  Parameter wp_sys_close_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γl γf : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (v : mword 64) (pid : mword 32) (V : pprivate),
      wp_sys_close_sconf_body γ Φ γl γf m av n eb p C v pid V.
End SYSCLOSE.
