(* SpecUartwrite.v -- the public interface of uartwrite, stated independently
   of its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void uartwrite(int uid, char buf[], int n);

   uartwrite is xv6's INTERRUPT-DRIVEN UART output path (the one write() uses,
   as opposed to printk's spinning uartputc_sync).  At XV6_REV 163d39b it
   gained a PORT INDEX: the two 16550s share one `struct uart uarts[2]`, so
   the lock it takes is the FIELD `&uarts[uid].tx_lock`, the channel it parks
   on is the ELEMENT `&uarts[uid]`, and the MMIO window is the word
   `uarts[uid].base` -- LOADED, not a compile-time constant.  It pushes
   [buf[0..n)] into port [i]'s THR one byte at a time, taking and releasing
   that port's tx_lock around each LSR-check/THR-write and sleeping outside it
   whenever the transmitter is busy.

   ONE CONTRACT, PARAMETRIC IN THE PORT.  Nothing here is the console's: the
   registers move (a0 = uid, a1 = buf, a2 = n), the three addresses are
   [UartsFields]'s [uart_f_lock i] / [uart_f_chan i] / [uart_f_base i], and
   the device premise is the BARE [uart_inv i gu] rather than the [dev_inv]
   bundle -- which is also strictly easier for a console caller, who projects
   it with [WpUart.dev_inv_uart].  The OUTPUT CLAIM is kept at BOTH ports: the
   owner's ruling is that nothing has to TRACK port 1's output, not that the
   THR write stops landing, and [uart_sent_sub] is keyed on the ghost bundle
   [gu] rather than on the port, so producing it at port 1 costs this contract
   nothing and gives a future caller the option.

   @ KernelSyms.uartwrite, 142 bytes, 54 instructions, a 64-byte frame.
   EVERYTHING IS SHRINK-WRAPPED ONTO THE n > 0 PATH now: the `blez a2` is the first
   instruction, before the prologue, so the [n = 0] arm is a bare `ret` that
   touches no stack at all and the eight callee-saved spills (ra, s0-s6) all
   happen on the other side of it.

   THE ALTITUDE is port [i]'s tx_lock ([UartTxInv.is_txlock_at i], over
   [UartTxInv]'s payload).  It is persistent and is the entire credential: it
   carries both the lock (whose resource is the EXCLUSIVE TRANSMITTER TOKEN)
   and the frozen [uart_dlab_off].  Nothing about the transmitter is threaded
   by the caller -- which is forced, not chosen: the token has to be reachable
   by uartintr as well, and the two meet only under the lock.  See UartTxInv.v
   for why the lock is a spinlock again and what a driver that re-acquires per
   byte may claim.

   WHAT THE CONTRACT PROMISES ABOUT THE OUTPUT.  Not "the bytes were sent
   contiguously" -- uartwrite SLEEPS between bytes, and while it sleeps any
   other hart may push its own (uartputc_sync takes the same lock but not for
   the whole run).  The honest statement is the one the accepted-byte trace
   supports, and it is [UartTxInv.uart_sent_sub]:

       exists tr, uart_sent gu tr * ((f <$> seq 0 n) `sublist_of` tr)

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
   ([own_ctx] + sched_vc + [procs_inv], SpecSleep.v's shape) rides along for
   the same reason.

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
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import LockRank.
Require Import ProcGeom CpuOwn.
Require Import FdSlots.
Require Import DevModel.
Require Import DiskPtsto WpUart.

Require Import UartTxInv.
Require Import UartsFields.
Require Import SpecUartPutc.  (* [uart_base_word]: the VA-tier `uarts[i].base` *)
Require Import SchedCtx.
Require Export SwtchCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.
Local Open Scope Z_scope.


(* PORT [i]'s TRANSMIT LOCK is [UartTxInv.is_txlock_at i] -- the same payload
   ([tx_res] + the frozen [uart_dlab_off], both keyed on the ghost bundle and
   neither of them port-dependent) at the lock FIELD `uarts + 40*uid + 16`,
   under the name [uart_lock_name i] that `uartinit` initialised it with.  A
   console caller holding the old [is_txlock] has [is_txlock_at Uart0] by
   definition. *)

(* uartwrite's own frame is 8 slots ([c.addi16sp sp,-64] at the prologue), and
   the deepest callee is [sleep] at 20 (sleep_prepare 14, acquire and release
   10 apiece) -- so the body's first call needs [20 <= av - 8], i.e.
   [av >= 28], and the bound is exactly tight.

   IT WAS 30, over a TEN-slot frame.  163d39b's uartwrite keeps its port
   pointer, its lock pointer and its base pointer in callee-saved registers
   instead of recomputing them, which costs one more spill and saves two
   slots' worth of scratch: the frame is 64 bytes now, so the number drops by
   two.  Before that it was 34, the sleeplock era's figure ([acquiresleep] at
   26 dominated); `d80e61c5` parks OUTSIDE the lock, so [sleep] is the floor.
   Nothing downstream constrains this constant: consolewrite, uartwrite's only
   caller, is unproven. *)
Notation uartwrite_stack := (28%nat) (only parsing).
Definition wp_uartwrite_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (i : uart_id) (gu : uart_names)
    (gs : list gname) (j : nat) (glp : gname) (gl : gname)
    (m : regfile) (av : nat) (eb : bool)
    (n : nat) (f : nat -> bv 8) (dq : dfrac) (b : bool)
    (pidv : mword 32) (dqp : dfrac) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uartwrite in
  let pj := proc_addr j in
  (* a0 = the PORT INDEX, a1 = the buffer, a2 = the count.  The buffer and the
     count each shifted up one register when `uid` took a0. *)
  let buf := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the process running here is proc j (sleep's linkage) *)
  (j < NPROC)%nat ->
  gs !! j = Some glp ->
  (* THE PORT, AS THE ARGUMENT REGISTER HOLDS IT.  The prologue turns a0 into
     `&uarts[uid]` by `((uid*4 + uid) << 3) + uarts`, which is [uart_elt i]
     exactly when a0 is [uart_index i]; the lock pointer is that plus 16. *)
  m !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int (uart_index i) : mword 64) ->
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int (Z.of_nat n) : mword 64) ->
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
     the loop body (sleep_prepare(u); acquire(&u->tx_lock)), against the
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
  (* THE ELEMENT'S [base] FIELD, AT THE TIER AN S-MODE LOAD CONSUMES.
     [uart_base_word i] is what turns the `ld a4,0(s4)` in front of every LSR
     read and every THR write into "a4 holds [uart_base i]"; the MMIO address
     is a LOADED VALUE now, and this is the only premise that says what was
     loaded.

     NOT [UartsFields.uarts_pinned], which is the same fact at the RAW
     PHYSICAL tier ([↦ₚ₈□]).  An S-mode load leaf consumes the context-tier
     [↦₈] and there is NO law crossing the two ([DiskInv.phys_win_to_mem]
     drops the ledger; [KMap.phys_ident_mem] lands at [mem_pointsto], not
     [ctx_pointsto]) -- only the BOOT CHAIN may cross them, and it already
     does ([BootShared.uart_base_word_of_pinned], minting both ports beside
     [uarts_pinned]).  Same correction as uartputc_sync's, uartinitone's and
     uartintr's.  uartwrite does NOT read `u->rx`, so it takes no
     [uart_rx_word]. *)
  uart_base_word i -∗
  (* THE DEVICE, PORT-GENERICALLY.  Not the [dev_inv] bundle: uartwrite opens
     port [i]'s invariant and nothing else -- no PLIC, no disk -- and at the
     second port the bundle does not exist.  A console caller projects this
     with [WpUart.dev_inv_uart]. *)
  uart_inv i gu -∗
  (* PORT [i]'s TRANSMIT LOCK -- the whole credential.  A SPINLOCK
     (`d80e61c5`): nothing is held across the park, because the lock is taken
     and released around each LSR-check/THR-write and the [sleep()] happens
     outside it.  Its resource is just the transmitter token; the [tx_busy]
     certificate is gone, because the writer polls THRE itself before every
     byte. *)
  is_txlock_at i gl gu -∗
  (* PURE PASSTHROUGH as of `d80e61c5`.  It was here because [acquiresleep]
     recorded the holder's pid in the sleeplock; a spinlock has no such field
     and no callee below now reads it.  Kept because it costs a caller
     nothing and dropping it would churn every call site, but it is no longer
     motivated -- delete it when the cone is next touched. *)
  p_pid pj ↦₄{dqp} pidv -∗
  (* the buffer, read-only *)
  ([∗ list] kk ∈ seq 0 n, (pa_add buf kk) ↦ₘ[KT1]{dq} f kk) -∗
  (* the running-thread bundle (SpecSleep.v) *)
  procs_inv gs -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf av b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      ([∗ list] kk ∈ seq 0 n, (pa_add buf kk) ↦ₘ[KT1]{dq} f kk) -∗
      p_pid pj ↦₄{dqp} pidv -∗
      uart_sent_sub gu (f <$> seq 0 n) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type UARTWRITE.
  Parameter wp_uartwrite_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (i : uart_id) (gu : uart_names) (gs : list gname) (j : nat) (glp : gname) (gl : gname)
      (m : regfile) (av : nat) (eb : bool)
      (n : nat) (f : nat -> bv 8) (dq : dfrac) (b : bool)
      (pidv : mword 32) (dqp : dfrac) (lks : gset string),
      wp_uartwrite_sconf_body i gu gs j glp gl m av eb n f dq b pidv dqp lks.
End UARTWRITE.
