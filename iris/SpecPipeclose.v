(* SpecPipeclose.v -- the public interface of pipeclose, stated independently
   of its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void pipeclose(struct pipe *pi, int writable);

   The precondition is one END of the pipe, held whole: [pipe_ref γp w 1],
   where [w] is the [writable] argument -- the same bool that indexes the
   reference algebra (PipeInv.v), and the one [fileclose] reads out of
   [f->writable].  Holding the END WHOLE is what licenses closing it: an end
   cannot be closed twice, and a dup'ed file cannot close the pipe out from
   under its twin.

   pipeclose either leaves the pipe alive (the other end is still open) or
   frees its page, and the caller cannot tell which -- so the postcondition
   says exactly that about the page count, and nothing about the pipe.  The
   reference is gone either way; [is_pipe] is persistent and stays, but with
   no reference it is worth nothing: it cannot even be used to take the lock.

   Note what the caller does NOT have to supply: any knowledge of the other
   end.  The whole point of the two-ended algebra is that the two closers need
   not meet. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.algebra Require Import frac.
From iris.base_logic.lib Require Import invariants ghost_var gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import FdSlots.
Require Import SchedCtx.
Require Import WpLock.
Require Import KallocInv.
Require Import PipeInv.
Require Import SpecPanic.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


Definition wp_pipeclose_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !pipeG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (γs : list gname)
    (γl : gname) (γp : pipe_names) (w : bool)
    (γkl : gname) (γk : gname * gname) (klk kfl : mword 64) (on : option nat)
    (m : regfile) (n : nat) (eb : bool) (pme : mword 64) (C : iProp Σ) (av : nat)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.pipeclose in
  let pi := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* a1 IS the [writable] argument: zero exactly when [w] is false.  This is
     the one coupling between an argument and a branch, and it is the natural
     one -- [w] is the argument's truth value, not a side condition on it. *)
  eq_vec (m !!! Regidx (mword_of_int 11 : mword 5)) (zero_reg : mword 64) = negb w ->
  (* 4 slots for pipeclose's own frame, over wakeup's 18 *)
  (22 <= av)%nat ->
  (* acquire's push_off increments the nesting count, and wakeup's myproc
     increments it again on top of that *)
  (Z.of_nat n + 2 < 2 ^ 31)%Z ->
  klk = mword_of_int KernelSyms.kmem ->
  kfl = mword_of_int (KernelSyms.kmem + 24) ->
  sie_cap_gpr m av b pme -∗
  cpu_own n eb pme C b -∗
  kernel_text -∗ pc_is pcE -∗
  is_pipe γl γp pi -∗
  pipe_ref γp w 1 -∗
  (* kfree's resources: the kmem lock and the page count *)
  is_lock γkl klk "kmem"%string (kmem_res γk kfl) -∗
  kalloc_avail γk on -∗
  (* wakeup's *)
  procs_inv γs -∗
  panic_wp_any -∗
  wp_next b pme (fun (CID : CpuId) =>
  ∀ mr,
    sie_cap_gpr mr av b pme -∗
    cpu_own n eb pme C b -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (* the page came back iff this was the LAST reference; the caller cannot
       tell, and does not need to *)
    (kalloc_avail γk on ∨ kalloc_avail γk (avail_inc on)) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PIPECLOSE.
  Parameter wp_pipeclose_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !pipeG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname)
      (γl : gname) (γp : pipe_names) (w : bool)
      (γkl : gname) (γk : gname * gname) (klk kfl : mword 64) (on : option nat)
      (m : regfile) (n : nat) (eb : bool) (pme : mword 64) (C : iProp Σ) (av : nat)
      (b : bool),
      wp_pipeclose_sconf_body γs γl γp w γkl γk klk kfl on m n eb pme C av b.
End PIPECLOSE.
