(* SpecSysDup.v -- the public interface of sys_dup(), stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     uint64 sys_dup(void) {
       struct file *f; int fd;
       if (argfd(0, 0, &f) < 0) return -1;
       if ((fd = fdalloc(f)) < 0) return -1;
       filedup(f);
       return fd;
     }

   @ KernelSyms.sys_dup = 0x80004bd6, 24 instructions (a 48-byte frame; the
   [struct file *f] local lives at s0-40, [f] rides in the callee-saved s1 and
   the descriptor in s2 across the filedup call).  Decode: CodeSysDup.v.

   THE WINDOW, AND WHY IT IS THE INTERESTING PART.  [fdalloc] stores the
   pointer BEFORE [filedup] bumps the count, so between the two calls two
   descriptors name one [struct file] and only one reference exists.  That is
   not a soundness problem -- the fd table is thread-local, so no other core
   can observe it -- but nothing in [ProcInv.proc_priv] can STATE it: the
   destination's cell names a file and [ofile_slot] then demands a reference
   that is not there.

   Worse, the reference [filedup] needs in hand is the SOURCE descriptor's, so
   that descriptor is payloadless too -- and it must stay that way ACROSS the
   fdalloc call, which itself wants the descriptor array.  A borrow with
   [ProcInv.proc_priv_ofile] cannot span the call (its wand demands the whole
   slot back first), which is exactly why the block is split at the fd table
   and the deficit tracked in [ProcInv.proc_ofiles_owe].  sys_dup is the
   function that forced that design; see claude-notes/design/file-table.md.

   THE LEDGER BALANCES WITH ZERO ALLOWANCE, and that is worth stating: the
   [fd_slot] fdalloc releases when it fills the destination descriptor is
   exactly the one [filedup] consumes to pay for the higher count.  So sys_dup
   needs none of the process's [FdSlots.FDSPARE] units -- unlike sys_open (one)
   or sys_pipe (two), which hold references in locals before installing them.
   The fd-slot conservation law never even wobbles here.

   DETERMINISM.  Which of the three exits runs is a function of the syscall
   argument and the process's own descriptor array, both of which the caller
   knows, so the postcondition says so ([SpecArgfd.arg_fd] and
   [SpecFdalloc.fd_frees]) rather than offering an unconstrained "duplicated
   it, or didn't": a kernel that always returned -1 would not satisfy this
   spec.  And the descriptor sys_dup returns is the LEAST free one, naming the
   very pointer the source held.

   THE FRACTION IS NOT OBSERVABLE, deliberately.  filedup halves the source's
   [file_ref] fraction, but [ofile_slot] existentially quantifies it, so the
   postcondition never mentions [q] -- which is what lets sys_dup be called any
   number of times without the spec accumulating halvings. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
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
Require Import WpNext.
Require Import WpLock.
Require Import PanicStub.
Require Import ProcGeom CpuOwn.
Require Import FdSlots FileInv ProcInv.
Require Import SpecArgfd SpecFdalloc.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.


(* sys_dup's own frame is 6 slots (addi sp,sp,-48); argfd wants 24 below it,
   fdalloc 14 and filedup 14, so argfd sets the bound. *)
Definition sys_dup_stack : nat := 30%nat.

Section SpecSysDup.
  Context `{!riscvGS Σ, !lockG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.

  (* sys_dup's result, keyed by the returned a0.  THREE arms, because there are
     two ways to fail and they are distinguishable: no such descriptor, or no
     room for another one.  Both leave the process exactly as it was. *)
  Definition sys_dup_post (γf : gname) (p : mword 64) (pid : mword 32)
      (V : pprivate) (v : mword 64) (r : mword 64) : iProp Σ :=
    ((* argfd said no: the argument is not an open descriptor *)
     ⌜r = (mword_of_int (-1) : mword 64) /\ arg_fd v (pv_ofile V) = None⌝ ∗
       proc_priv γf p pid V
     ∨
     (* the descriptor exists but the table is full.  xv6 does NOT close
        anything here -- it never took a reference -- so the block is
        untouched, and the [fd_slot] fdalloc would have released was never
        released either. *)
     (∃ (fd0 : nat) (fv : mword 64),
        ⌜r = (mword_of_int (-1) : mword 64) /\
         arg_fd v (pv_ofile V) = Some (fd0, fv) /\
         fd_frees (pv_ofile V) = []⌝ ∗
        proc_priv γf p pid V)
     ∨
     (* duplicated: the least free descriptor now names the same file the
        source did, and the count behind it has gone up by one. *)
     (∃ (fd0 fd1 : nat) (fv : mword 64) (l : list nat),
        ⌜r = (mword_of_int (Z.of_nat fd1) : mword 64) /\
         arg_fd v (pv_ofile V) = Some (fd0, fv) /\
         fd_frees (pv_ofile V) = fd1 :: l⌝ ∗
        proc_priv γf p pid (upd_ofile V fd1 fv)))%I.

End SpecSysDup.

Definition wp_sys_dup_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} (γl γf : gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (v : mword 64) (pid : mword 32) (V : pprivate) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_dup in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* sys_dup reads syscall argument 0, out of the trapframe page [proc_priv]
     carries *)
  pv_tf V !! tf_arg_idx 0 = Some v ->
  (* push_off's transient noff increment stays in int range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (sys_dup_stack <= av)%nat ->
  (* THE RANK BOUND, FOR THE ONE LOCK BELOW.  sys_dup takes no lock of its
     own, but filedup acquires "ftable", and the rank discipline needs every
     rank the caller arrives holding to sit strictly BELOW that one --
     [LockRank.locks_below], not mere non-membership, because only the bound
     composes across a call chain ([locks_below_mono] weakens it to any higher
     rank, [locks_below_not_elem] recovers the non-membership a ghost step
     wants).  It is passed straight through to filedup, which states it in
     exactly this shape.  A syscall entry point holds nothing, so at every
     real instantiation [lks] is ∅ and this is [locks_below_empty]; the body
     is stated ∀-generically in [lks], so it has to be said. *)
  locks_below lks "ftable" ->
  sie_cap_gpr m av b p -∗
  cpu_own n eb p C b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the ftable lock, for filedup's ghost step *)
  is_ftable γl γf -∗
  panic_wp_any -∗
  proc_priv γf p pid V -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own n eb p C b lks -∗
      pc_is ret_tgt -∗
      sys_dup_post γf p pid V v (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSDUP.
  Parameter wp_sys_dup_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} (γl γf : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (v : mword 64) (pid : mword 32) (V : pprivate) (b : bool) (lks : gset string),
      wp_sys_dup_sconf_body γl γf m av n eb p C v pid V b lks.
End SYSDUP.
