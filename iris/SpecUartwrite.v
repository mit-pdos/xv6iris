(* SpecUartwrite.v -- the public interface of uartwrite, stated independently
   of its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void uartwrite(char buf[], int n);

   uartwrite is xv6's INTERRUPT-DRIVEN UART output path (the one write() uses,
   as opposed to printk's spinning uartputc_sync).  It takes tx_lock and pushes
   [buf[0..n)] into THR one byte at a time, sleeping on &tx_chan whenever
   [tx_busy] says the previous byte has not yet been reported transmitted.
   @ KernelSyms.uartwrite = 0x800008dc, 52 instructions, an 80-byte frame;
   ra/s0/s1/s5 saved in the prologue, s2/s3/s4/s6/s7 SHRINK-WRAPPED onto the
   n > 0 path.

   THE ALTITUDE is the tx_lock's ([UartTxInv.v]).  [is_txlock] is persistent and
   is the entire credential: it carries both the lock (whose resource is the
   [tx_busy] cell plus the EXCLUSIVE TRANSMITTER TOKEN) and the frozen
   [uart_dlab_off].  Nothing about the transmitter is threaded by the caller --
   which is forced, not chosen: the token has to be reachable by uartintr as
   well, and the two meet only under the lock.  See UartTxInv.v for why
   "tx_busy == 0" is what licenses the THR store.

   WHAT THE CONTRACT PROMISES ABOUT THE OUTPUT.  Not "the bytes were sent
   contiguously" -- uartwrite SLEEPS between bytes, and while it sleeps any
   other hart may push its own (uartputc_sync does not take this lock at all).
   The honest statement is the one the accepted-byte trace supports, and it is
   [UartTxInv.uart_sent_sub]:

       ∃ tr, uart_sent γu tr ∗ ⌜ (f <$> seq 0 n) `sublist_of` tr ⌝

   -- every byte of the buffer was accepted by the UART, IN ORDER, possibly
   interleaved with other harts' bytes.  [uart_sent] is persistent and
   monotone, so this survives everything that happens afterwards.

   THE BUFFER is taken at an arbitrary [dq] and handed back untouched
   (uartwrite only reads it), named by [f] in strlen's vocabulary.  [n] is a
   [nat]: a caller with a non-positive count has nothing to say and nothing to
   pass, and the C's [n <= 0] guard then IS the [n = 0] arm.

   INTERRUPT LEVEL IS PINNED AT 0, as in pipewrite: sleep parks through
   sched(), whose invariant demands noff = 1 -- tx_lock and nothing else -- so
   uartwrite must be entered with no lock held.  The running-thread bundle
   ([own_ctx] + [▷ sched_vc] + [procs_inv], SpecSleep.v's shape) rides along
   for the same reason.

   Design & worklist: claude-notes/projects/uartwrite.md. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvModelBytes RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import FdSlots.
Require Import DiskPtsto WpUart.
Require Import UartTxInv.
Require Import SchedCtx.
Require Export SwtchCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.
Local Open Scope Z_scope.


(* uartwrite's own frame is 8 slots ([c.addi16sp sp,-64] at the prologue), and
   the deepest callee is now ACQUIRESLEEP at 26 (releasesleep 22, sleep 20,
   sleep_prepare 14) -- so the body's first call needs [26 <= av - 8], i.e.
   [av >= 30], and the bound is exactly tight: a TEN-slot frame
   ([addi sp,sp,-80]) over [sleep]'s 20, which is the deepest thing below --
   [sleep_prepare] wants 14 and acquire/release 10 apiece.

   IT WAS 34, AND THAT WAS THE SLEEPLOCK ERA'S NUMBER.  `ae96fd0` made
   uartwrite hold a SLEEPLOCK across the park, so [acquiresleep]'s own budget
   dominated; `d80e61c5` takes and releases a SPINLOCK around each
   LSR-check/THR-write and parks outside it, so [sleep] is the floor again.
   34 was not wrong, only loose -- it over-charged every caller by four slots.
   Nothing downstream constrains this constant: consolewrite, uartwrite's only
   caller, is unproven. *)
Notation uartwrite_stack := (30%nat) (only parsing).
Definition wp_uartwrite_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γu : uart_names) (γv : disk_names) 
    (γs : list gname) (j : nat) (γlp : gname) (γl : gname)
    (m : regfile) (av : nat) (eb : bool)
    (n : nat) (f : nat -> bv 8) (dq : dfrac) (b : bool)
    (pidv : mword 32) (dqp : dfrac) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uartwrite in
  let pj := proc_addr j in
  (* a0 = the buffer, a1 = the count *)
  let buf := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the process running here is proc j (sleep's linkage) *)
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  m !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int (Z.of_nat n) : mword 64) ->
  (Z.of_nat n < 2 ^ 31)%Z ->
  (uartwrite_stack <= av)%nat ->
  (* PARKING PREMISE (hart-generic scheduler protocol): the saved base enable
     is [true].  Everything below sleeps, and a parking thread must hand the
     trap CSRs across the crossing -- at level 0 with an enabled base the
     pushing acquire produces exactly that set.  See SpecSched.v. *)
  eb = true ->
  (* THE LOWEST RANK, NOT "uart".  uartwrite's cone touches "uart" (15) at
     its own acquire, but ALSO "proc" (11, LockRank.v) at both
     sleep_prepare and sleep -- and both of those run BEFORE the acquire in
     the loop body (sleep_prepare(&tx_chan); acquire(&tx_lock)), against the
     same held set [lks] the function starts with.  A bound at "uart" says
     nothing about "proc" (mono only lifts a LOW bound to a higher rank, never
     the reverse), so the premise has to be stated at "proc" -- the true
     floor of the cone -- and [locks_below_mono] (11 <= 15) lifts it to
     "uart" for the acquire call.  uartwrite is BALANCED overall (each byte's
     acquire/release pair cancels), so [lks] is unchanged end to end. *)
  locks_below lks "proc" ->
  sie_cap_gpr KT1 m av b pj -∗
  (* noff = 0: sleep demands tx_lock be the ONLY lock held *)
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  (* the device, and the transmitter's lock -- the whole credential.  The
     lock is a SLEEPLOCK now (UartTxInv.v): uartwrite parks between bytes and
     Its resource is just the token -- the [tx_busy] certificate is gone,
     because the writer polls THRE itself before every byte.  NOTE this is a
     SPINLOCK again (`d80e61c5`): nothing is held across the park, because
     the lock is taken and released around each LSR-check/THR-write and the
     [sleep()] happens outside it. *)
  dev_inv γu γv -∗
  is_txlock γl γu -∗
  (* PURE PASSTHROUGH as of `d80e61c5`.  It was here because [acquiresleep]
     recorded the holder's pid in the sleeplock; a spinlock has no such field
     and no callee below now reads it.  Kept because it costs a caller
     nothing and dropping it would churn every call site, but it is no longer
     motivated -- delete it when the cone is next touched. *)
  p_pid pj ↦₄{dqp} pidv -∗
  (* the buffer, read-only *)
  ([∗ list] k ∈ seq 0 n, (pa_add buf k) ↦ₘ{dq} f k) -∗
  (* the running-thread bundle (SpecSleep.v) *)
  procs_inv γs -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf av b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      ([∗ list] k ∈ seq 0 n, (pa_add buf k) ↦ₘ{dq} f k) -∗
      p_pid pj ↦₄{dqp} pidv -∗
      uart_sent_sub γu (f <$> seq 0 n) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type UARTWRITE.
  Parameter wp_uartwrite_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γu : uart_names) (γv : disk_names) (γs : list gname) (j : nat) (γlp : gname) (γl : gname)
      (m : regfile) (av : nat) (eb : bool)
      (n : nat) (f : nat -> bv 8) (dq : dfrac) (b : bool)
      (pidv : mword 32) (dqp : dfrac) (lks : gset string),
      wp_uartwrite_sconf_body γu γv γs j γlp γl m av eb n f dq b pidv dqp lks.
End UARTWRITE.
