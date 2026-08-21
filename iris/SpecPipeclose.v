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
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import FdSlots.
Require Import SchedCtx.
Require Import WpLock.
Require Import KallocInv.
Require Import PipeInvDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.


Definition wp_pipeclose_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γs : list gname)
    (γl : gname) (γp : pipe_names) (w : bool)
    (γkl : gname) (γk : gname * gname) (klk kfl : mword 64) (on : option nat)
    (m : regfile) (n : nat) (eb : bool) (pme : mword 64) (av : nat)
    (b : bool) (lks : gset string) :=
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
  (* THE ORDER PREMISE for the one lock pipeclose takes itself, pi->lock,
     which [pipealloc]'s [initlock] names "pipe": everything the caller holds
     ranks strictly below it.  [LockRank.locks_below_not_elem] recovers the
     non-membership the set algebra below needs.  No execution ever holds two
     "pipe" locks at once (LockRank.v).  pipeclose is BALANCED: BOTH C exit
     paths release pi->lock (the freeing one releases and only then kfree's
     the page), so entry and exit [cpu_own] carry the same [lks].  The kmem
     lock kfree takes is entirely inside kfree, after the release. *)
  locks_below lks "pipe" ->
  sie_cap_gpr KT1 m av b pme -∗
  cpu_own n eb pme b lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_pipe γl γp pi -∗
  pipe_ref γp w 1 -∗
  (* kfree's resources: the kmem lock and the page count *)
  is_lock γkl klk "kmem"%string (kmem_res γk kfl) -∗
  kalloc_avail γk on -∗
  (* wakeup's *)
  procs_inv γs -∗
  wp_next b pme (fun (CID : CpuId) =>
  ∀ mr,
    sie_cap_gpr KT1 mr av b pme -∗
    cpu_own n eb pme b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (* the page came back iff this was the LAST reference; the caller cannot
       tell, and does not need to *)
    (kalloc_avail γk on ∨ kalloc_avail γk (avail_inc on)) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PIPECLOSE.
  Parameter wp_pipeclose_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname)
      (γl : gname) (γp : pipe_names) (w : bool)
      (γkl : gname) (γk : gname * gname) (klk kfl : mword 64) (on : option nat)
      (m : regfile) (n : nat) (eb : bool) (pme : mword 64) (av : nat)
      (b : bool) (lks : gset string),
      wp_pipeclose_sconf_body γs γl γp w γkl γk klk kfl on m n eb pme av b lks.
End PIPECLOSE.
