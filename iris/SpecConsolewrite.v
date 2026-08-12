(* SpecConsolewrite.v -- the public interface of consolewrite, stated
   independently of its proof.

     int consolewrite(int user_src, uint64 src, int n);

   consolewrite copies [n] bytes of the caller's buffer out one at a time
   with either_copyin and hands each to uartputc, stopping early if a copy
   faults; it returns the number of bytes it managed to push.
   @ KernelSyms.consolewrite = 0x800000d6.

   *** THIS CONTRACT IS ASSUMED (LinkConsolewrite.v). ***  It is the fourth
   of its kind, after LinkKerneltrap.v, LinkConsoleintr.v and
   LinkConsoleread.v, and it is here for exactly the reason the third one is:
   filewrite's FD_DEVICE arm dispatches through [devsw[f->major].write], the
   console is the only device xv6 installs, and consolewrite has no proof.
   Isolating the assumption here keeps ProofFilewrite.v itself axiom-free --
   it is a functor over [CONSOLEWRITE], and proving consolewrite later
   replaces this file and nothing else.

   ---- THE SHAPE, AND WHY IT IS CONSOLEREAD'S ---------------------------

   Conjunct for conjunct [SpecConsoleread.v]'s, with the copy direction
   reversed and nothing else moved.  That is not laziness: the two are the
   same kind of animal (a blocking transfer between USER memory and the
   console by the running thread), and -- more to the point -- the shape is
   FORCED.  [SpecFilewrite.filewrite_dev_env] is ONE devsw cell and nothing
   else, so the only resources this call can be handed are the ones
   filewrite's own contract already holds: the register capability, the
   nesting level, the text, [proc_priv], [kalloc_env], [procs_inv] and
   [panic_wp_any].  A contract asking for more could not be applied at
   filewrite's [c.jalr a5] at +0x7e.

   So:

   * it SLEEPS (uartputc parks on the transmit ring when it is full), so it
     threads the running-thread bundle ([procs_inv]) and takes the
     hart-generic parking premise [eb = true] at [noff = 0].  The parked
     scheduler record is NOT threaded: it lives in the running proc's own
     [p->lock] ([SchedCtx.run_slot]), which sleep reaches by holding it;
   * it copies IN from user memory, so it takes [proc_priv] and [kalloc_env]
     (either_copyin reaches copyin, hence walkaddr and vmfault, hence
     kalloc) and gives the block back at an EXTENDED page table
     ([uptd_ext]) -- writei's user arm does exactly the same;
   * it gives back every callee-saved register and the nesting level.

   ---- WHAT THE ASSUMPTION HIDES ---------------------------------------

   Worth naming, because a proved consolewrite could not be silent about it,
   and because it is a strictly LONGER list than consoleread's:

   1. THE UART.  consolewrite's per-byte tail is [uartputc], which takes
      [uart_tx_lock], appends to [uart_tx_buf] and sleeps on it; the bytes
      leave through [uartstart] and the transmit interrupt.  None of
      [WpUart]'s state ([dev_inv], [uart_tx_own], [uart_dlab_off]) is
      mentioned here, so this contract asserts that the console's own
      transmit machinery is correct and self-contained.  That is the SAME
      elision LinkConsoleread already makes for [cons.lock] and
      [cons.buf] -- neither contract names the console module's private
      state -- and it is the reason both live behind an [Axiom] rather than
      inside the verified cone.  When console.c is proved, the console
      module will have to publish a persistent invariant that its own
      entry points can open; if it cannot, THIS contract (and
      SpecConsoleread's) is what has to grow, and SpecFilewrite's device
      arm with it.
   2. WHICH BYTES ARRIVE.  Nothing: the destination is a serial line, not a
      resource this file system models.  What filewrite's caller gets out of
      the call is only the RETURN VALUE BOUND [-1 <= r <= n].

   THE BOUND IS DELIBERATELY WEAK.  The C returns [i], the number of bytes
   pushed, which is between 0 and [n]; this contract admits -1 as well.
   Under-promising costs filewrite nothing -- its postcondition is
   [PipeInv.pipe_rw_ret], which already admits -1 on the pipe arm -- and it
   keeps the eventual discharge obligation as small as possible, which is
   the whole point of writing an assumed contract MINIMALLY. *)
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
Require Import FdSlots FileInv ProcInv.
Require Import SpecPanic.
Require Import SchedCtx.
Require Export SwtchCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

(* consolewrite's own frame plus its deepest callee.  It reaches
   either_copyin -> copyin -> vmfault, the same tower piperead/pipewrite are
   sized by (50), on top of uartputc's sleep (22) and acquire/release (10);
   the constant is consoleread's, which is the honest bound for "a blocking
   transfer between user memory and the console". *)
Definition consolewrite_stack : nat := 62%nat.

Definition wp_consolewrite_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ, !kallocG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
    (pid : mword 32) (V : pprivate) (n : Z) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.consolewrite in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the process running here is proc j (sleep/killed's linkage) *)
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  (* a0 = 1: the source is a USER address.  filewrite's dispatch passes the
     literal 1 (the [c.li a0,1] at +0x7c), and this contract is only stated
     for that case -- the kernel-source arm has no caller. *)
  m !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64) ->
  (* a2 is the int argument [n] *)
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int n : mword 64) ->
  (- 2 ^ 31 <= n < 2 ^ 31)%Z ->
  (consolewrite_stack <= av)%nat ->
  (* PARKING PREMISE (hart-generic scheduler protocol).  See SpecSched.v. *)
  eb = true ->
  sie_cap_gpr m av b pj -∗
  (* noff = 0: sleep demands the uart lock be the ONLY lock held *)
  cpu_own 0%nat eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  proc_priv_core pj pid V -∗
  kalloc_env γa None -∗
  procs_inv γs -∗
  panic_wp_any -∗
  (* THE CROSSING IS [true], NOT [b] -- consolewrite sleeps on the uart, so it
     is a PARKING function and the porting guide's rule applies: a parking
     function's [wp_next] index is [true] unconditionally.  With [eb = true]
     above and [cpu_own_eb_agree] at level 0 the two spellings coincide at
     every constructible instance. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (r : Z) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      (* the whole of what a device write promises: it delivered somewhere
         between "failed" and "all of it". *)
      ⌜(-1 <= r <= n)%Z⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int r : mword 64)⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0%nat eb pj C b -∗
      pc_is ret_tgt -∗
      proc_priv_core pj pid (upd_upt V P') -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CONSOLEWRITE.
  Parameter wp_consolewrite_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ, !kallocG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (n : Z) (b : bool),
      wp_consolewrite_sconf_body γa γf γs j γlp m av eb C pid V n b.
End CONSOLEWRITE.
