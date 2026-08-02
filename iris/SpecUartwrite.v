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
Require Import HartTp WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import FdSlots.
Require Import DiskPtsto WpUart.
Require Import UartTxInv.
Require Import SpecPanic.
Require Import SchedCtx.
Require Export SwtchCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

Notation UW := KernelSyms.uartwrite.

(* uartwrite's own frame is 10 slots; the deepest callee is sleep at 22
   (acquire and release want 10). *)
Definition uartwrite_stack : nat := 32%nat.

Definition wp_uartwrite_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ} `{CID : CpuId}
    (γu : uart_names) (γv : disk_names) (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γlp : gname) (γl : gname)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
    (n : nat) (f : nat -> bv 8) (dq : dfrac) (b : bool) :=
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
  sie_cap_gpr m av b pj -∗
  (* noff = 0: sleep demands tx_lock be the ONLY lock held *)
  cpu_own 0%nat eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  (* the device, and the transmitter's lock -- the whole credential *)
  dev_inv γu γv -∗
  is_txlock γl γu -∗
  (* the buffer, read-only *)
  ([∗ list] k ∈ seq 0 n, (pa_add buf k) ↦ₘ{dq} f k) -∗
  (* the running-thread bundle (SpecSleep.v) *)
  procs_inv Φ γs -∗
  panic_wp_any -∗
  own_ctx (p_context pj) -∗
  ▷ sched_vc Φ γs (a_cpu_ctx cid_word) pj -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0%nat eb pj C b -∗
      pc_is ret_tgt -∗
      ([∗ list] k ∈ seq 0 n, (pa_add buf k) ↦ₘ{dq} f k) -∗
      uart_sent_sub γu (f <$> seq 0 n) -∗
      own_ctx (p_context pj) -∗
      ▷ sched_vc Φ γs (a_cpu_ctx cid_word) pj -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type UARTWRITE.
  Parameter wp_uartwrite_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{CID : CpuId}
      (γu : uart_names) (γv : disk_names) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γlp : gname) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (n : nat) (f : nat -> bv 8) (dq : dfrac) (b : bool),
      wp_uartwrite_sconf_body γu γv Φ γs j γlp γl m av eb C n f dq b.
End UARTWRITE.
