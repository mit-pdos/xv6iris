(* SpecConsoleread.v -- the public interface of consoleread, stated
   independently of its proof.

     int consoleread(int user_dst, uint64 dst, int n);

   consoleread takes cons.lock, sleeps on &cons.r until a whole line has been
   typed, copies up to [n] bytes of it out to the user address [dst] with
   either_copyout, and returns the number copied -- or -1 if the process was
   killed while it waited.  @ KernelSyms.consoleread = 0x80000178.

   *** THIS CONTRACT IS ASSUMED (LinkConsoleread.v). ***  It is the third of
   its kind, after LinkKerneltrap.v and LinkConsoleintr.v, and it exists for
   the same reason: fileread's FD_DEVICE arm dispatches through
   [devsw[f->major].read], the console is the only device xv6 installs, and
   consoleread has no proof.  Isolating the assumption here keeps
   ProofFileread.v itself axiom-free -- it is a functor over [CONSOLEREAD],
   and proving consoleread later replaces this file and nothing else.

   ---- THE SHAPE, AND WHY IT IS PIPEREAD'S ------------------------------

   consoleread and piperead are the same kind of animal: a blocking read into
   USER memory by the running thread.  So this contract is stated in
   [SpecPiperead.v]'s shape, conjunct for conjunct, minus the pipe:

   * it SLEEPS, so it threads the running-thread bundle ([procs_inv]) and
     takes the hart-generic parking premise [eb = true] at [noff = 0] --
     cons.lock is the only lock it holds and sleep demands that.  The parked
     scheduler record is NOT threaded: it lives in the running proc's own
     [p->lock] ([SchedCtx.run_slot]), which sleep reaches by holding it;
   * it copies out, so it takes [proc_priv] and [kalloc_env] (copyout reaches
     vmfault, hence kalloc) and gives the block back at an EXTENDED page
     table ([uptd_ext]), exactly as readi's user arm does;
   * it gives back every callee-saved register and the nesting level.

   ---- WHAT THE ASSUMPTION HIDES ---------------------------------------

   Worth naming, because a proven consoleread could not be silent about it:
   consoleread reads [cons.buf] and advances [cons.r], which
   [consoleintr] -- itself assumed (LinkConsoleintr.v) -- writes and whose
   [wakeup] is what ends the sleep.  This contract says nothing about the
   console's ring buffer at all, so the two assumptions are not independent:
   together they assert that the console line discipline is correct.  What
   fileread's caller gets out of it is only the RETURN VALUE bound
   [-1 <= r <= n] -- deliberately, since a device read's bytes are not a
   function of any state the file system models. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import PanicStub.
Require Import SchedCtx.
Require Export SwtchCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

(* consoleread's own frame plus its deepest callee.  It reaches
   either_copyout -> copyout -> vmfault, the same tower piperead is sized by
   (50), on top of sleep (22) and acquire/release (10); the constant is
   piperead's, which is the honest bound for "a blocking read into user
   memory". *)
Definition consoleread_stack : nat := 62%nat.

Definition wp_consoleread_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ, !kallocG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (γf : gname) 
    (γs : list gname) (j : nat) (γlp : gname)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
    (pid : mword 32) (V : pprivate) (n : Z) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.consoleread in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the process running here is proc j (sleep/killed's linkage) *)
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  (* a0 = 1: the destination is a USER address.  fileread's dispatch passes
     the literal 1, and this contract is only stated for that case -- the
     kernel-destination arm has no caller. *)
  m !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64) ->
  (* a2 is the int argument [n] *)
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int n : mword 64) ->
  (- 2 ^ 31 <= n < 2 ^ 31)%Z ->
  (consoleread_stack <= av)%nat ->
  (* PARKING PREMISE (hart-generic scheduler protocol).  See SpecSched.v. *)
  eb = true ->
  sie_cap_gpr m av b pj -∗
  (* noff = 0: sleep demands cons.lock be the ONLY lock held *)
  cpu_own 0%nat eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  proc_priv_core pj pid V -∗
  kalloc_env γa None -∗
  procs_inv γs -∗
  panic_wp_any -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (r : Z) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      (* the whole of what a device read promises: it delivered somewhere
         between "failed" and "all of it". *)
      ⌜(-1 <= r <= n)%Z⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int r : mword 64)⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0%nat eb pj C b -∗
      pc_is ret_tgt -∗
      proc_priv_core pj pid (upd_upt V P') -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CONSOLEREAD.
  Parameter wp_consoleread_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ, !kallocG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (n : Z) (b : bool),
      wp_consoleread_sconf_body γa γf γs j γlp m av eb C pid V n b.
End CONSOLEREAD.
