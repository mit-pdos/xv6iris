(* SpecUartinitone.v -- the public interface of Uartinitone, stated
   independently of its proof.  Requires only the definitional layer -- never
   a whole-function proof file -- so every function proof can be checked in
   parallel.

   [uartinitone(struct uart *u, char *name)] is the 16550 device-init routine
   at ONE port (kernel/uart.c at XV6_REV 163d39b); [uartinit] is now nothing
   but two calls to it, one per element of [uarts[]].  It runs in S-mode
   during boot.  The seven MMIO byte writes are, in order (all through the
   base [u->base] the .data word holds, i.e. [uart_pa i off]):

     off 1 = 0x00   disable interrupts (IER)
     off 3 = 0x80   set DLAB (LCR_BAUD_LATCH)
     off 0 = 0x03   LSB divisor       (DLL, DLAB set)
     off 1 = 0x00   MSB divisor       (DLM, DLAB set)
     off 3 = 0x03   8N1, clear DLAB   (LCR_EIGHT_BITS)
     off 2 = 0x07   enable + clear both FIFOs (FCR)
     off 1 = 2|rx   enable tx interrupts, and rx interrupts iff [u->rx] != 0

   then [initlock(&u->tx_lock, name)].

   THREE THINGS ARE NEW RELATIVE TO THE OLD SINGLE-PORT [uartinit].

   (1) THE MMIO BASE IS LOADED, NOT A CONSTANT.  Every [WriteReg(u, …)]
   begins [ld a5,0(a0)], so the address the store leaf sees comes out of the
   .data word [uarts[i].base].  [SpecUartPutc.uart_base_word i] is the
   persistent snapshot of that word at the value [uart_base i], minted once
   in the boot chain, and it is what turns the loaded register into
   [uart_pa i 0].  Without it nothing in the proof knows which device
   the stores reach -- and since eight harts share the array, a persistent
   snapshot is the only honest resource for it.

   (2) THE SEVENTH WRITE READS [u->rx].  [IER <- IER_TX_ENABLE | (u->rx ?
   IER_RX_ENABLE : 0)] compiles to [ld a5,8(a0); snez a5,a5; addi a5,a5,2],
   so the byte is 3 at the console (whose [rx] is [consoleintr]) and 2 at the
   port with nowhere for input to go.  [UartsFields.uart_rx_pinned i] is what
   decides which: it pins the .data word to [uart_rx_hook i].  The contract
   does NOT name the resulting byte -- the ghost step for offset 1 is stable
   at either value ([uart_write_1_stable]) -- but the proof needs the word to
   be able to run the [snez] at all.

   (3) THE LOCK'S NAME IS AN ARGUMENT.  [initlock(&u->tx_lock, name)] takes
   the caller's string, so this contract is parametric in [nm : string] and
   in the [.rodata] address the caller put in a1.  [uartinit] instantiates it
   at "uart0" and "uart1"; nothing here decides the port's name.

   EVERYTHING ELSE IS THE OLD CONTRACT, INDEXED BY THE PORT.  In particular
   it is still STATED OVER THE TIME-0 DEVICE INVARIANT -- device init does
   NOT run before [uart_inv i] is allocated: the UART thread is a top-level
   thread from step 0 and every one of its steps needs the fragment, so
   [uart_frag] can never sit raw in a CPU's precondition -- and the two
   writes that look incompatible with an invariant are both discharged by
   ghost arithmetic rather than by running early:

     - the FCR FIFO-CLEAR (off 2, bit 2) discards queued bytes, which a
       [mono_list] over [uart_acc] cannot do -- unless the FIFO is provably
       empty.  It is: the caller's [uart_tx_own γ l] pins [uart_acc u = l]
       and [uart_out_lb γ l] says the transmitted prefix has already reached
       [l], so [DevModel.uart_tx_empty_of_out] leaves nothing in [u_tx] and
       the clear shrinks nothing.
     - the DLAB SET (off 3 = 0x80) is why the caller threads the UNFROZEN
       half [uart_dlab_is γ (DfracOwn (1/2)) b0] at an ARBITRARY [b0] rather
       than the persistent [uart_dlab_off]: the freeze happens in this
       function's tail, where the final LCR write has just cleared DLAB.  So
       [uart_dlab_off] is uartinitone's OUTPUT.

   AND IT IS THE SAME CONTRACT AT BOTH PORTS.  The owner's ruling for this
   bump is that UART1's OUTPUT is unconstrained -- nothing tracks what
   printk/panic put on that wire -- but that is a statement about who
   CONSUMES [uart_sent]; the port still needs its FIFO and DLAB ghosts to
   exist, because the FCR clear and the baud-latch dance are the same seven
   instructions at both ports.  So the ghosts are threaded uniformly and the
   second port's caller simply drops the trace claims it is handed back.

   uartinitone writes no THR, so the accepted trace is unchanged and the
   token and receipt come back at the same [l]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List String.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import KernelText KernelDataInv.
Require Import DevModel WpUart.
Require Import UartsFields.
Require Import UartTxInv.
Require Import SpecUartPutc.  (* [uart_base_word] -- the VA-tier [uarts[i].base] snapshot *)
(* [lk_raw] / [lk_fresh] -- the three-cell spinlock bundle, before and after
   [initlock].  They live in SpecProcinit.v with the rest of the boot-time
   lock vocabulary; nothing else in that file is used here. *)
Require Import SpecProcinit.
Require Import IntrDefs.
Require Import RegFile.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.


(* BOOT-ONLY: uartinitone runs strictly before interrupts are ever enabled
   (main()'s [consoleinit()], on hart 0, always before scheduler()'s
   [intr_on()]), so the contract is stated at the literal index [false]
   rather than a generic [b], with no [wp_next] wrapper at all (it would
   collapse via [wp_next_off] anyway, since the hart cannot move). *)
Definition wp_uartinitone_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (i : uart_id) (γd : uart_names) (nm : string) (nm_addr : mword 64)
    (m : regfile) (K : nat)
    (l : list (bv 8)) (b0 : bool) (k : nat) (hl : option (list mobs))
    (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uartinitone in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (* THE FRAME PLUS THE CALLEE.  uartinitone's own frame is
     [addi sp,sp,-16] = 2 slots, and [initlock] demands [(2 <= av)] of what
     is left, so the budget is 2 + 2. *)
  (4 <= K)%nat ->
  (* THE TWO ARGUMENTS.  a0 is [&uarts[i]] -- the element, which is also the
     sleep channel and, at +16, the transmit lock -- and a1 the name. *)
  m !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i) ->
  m !!! Regidx (mword_of_int 11 : mword 5) = nm_addr ->
  sie_cap_gpr KT0 m K false p -∗
  kernel_text -∗ pc_is pcE -∗
  (* THE TWO IMMUTABLE FIELDS OF THIS ELEMENT, AT THE VA TIER.  [base] is
     what every [WriteReg] loads and [rx] is what the last one branches on;
     both are persistent, because the loader wrote them and the kernel never
     does, and both are the CONTEXT-tier form an S-mode [ld] leaf consumes.
     [UartsFields.uart_base_pinned] / [_rx_pinned] are the same two facts at
     the PHYSICAL tier, which is what the boot carve produces; the crossing
     is the boot chain's ([BootShared.uart_field_word_of_pinned]) because a
     VA-tier points-to carries the mapping claim and no function proof holds
     [KMap.kmap_static_claims]. *)
  uart_base_word i -∗ uart_rx_word i -∗
  (* the name the caller passes to [initlock], as the duplicable ∀-context
     string ownership that spec takes.  A [.rodata] literal's producer is
     [KernelDataInv.kernel_data_string_all]; [uartinit] runs it for
     "uart0"/"uart1" and hands the result down. *)
  ctx_string_all nm_addr DfracDiscarded nm -∗
  (* the UART fabric at THIS port, borrowed from the invariant around each
     write *)
  uart_inv i γd -∗
  (* "everything accepted has been transmitted, and the transmitter is
     mine": the pair that makes the FCR FIFO-clear shrink nothing *)
  uart_tx_own γd l -∗ uart_out_lb γd l -∗ uart_sent γd l -∗
  (* THE RECEIVE TOKEN.  The FCR write is [FCR_FIFO_ENABLE | FCR_FIFO_CLEAR],
     and the CLEAR empties the RECEIVE FIFO -- a pop of everything, which
     only the token's holder may perform (WpUart.v's receive column). *)
  uart_rx_tok γd k hl -∗
  (* the UNFROZEN DLAB half, at an arbitrary power-on value *)
  uart_dlab_is γd (DfracOwn (1/2)) b0 -∗
  (* this port's transmit lock, uninitialized: all three fields of
     [struct spinlock tx_lock] at [uarts + 40*i + 16], contents arbitrary. *)
  lk_raw (a_tx_lock_at i) -∗
  ( ∀ mr,
    sie_cap_gpr KT0 mr K false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (* no THR write, so the accepted trace is untouched *)
    uart_tx_own γd l -∗ uart_sent γd l -∗
    (* ...and the token back, at whatever the flush left the counter *)
    (∃ (k' : nat) (hl' : option (list mobs)), uart_rx_tok γd k' hl') -∗
    (* the final LCR write cleared DLAB, so the half is frozen for good *)
    uart_dlab_off γd -∗
    (* THE TRANSMIT LOCK COMES BACK OUT, INITIALIZED -- the "newlock" ghost
       step's raw material.  [initlock] zeroes [locked] and [cpu] and writes
       [name], which is then DISCARDED in favour of the persistent
       [lock_name]: [uarts[]] is a static global that is never freed, so
       nothing needs the field back owned. *)
    lk_fresh (a_tx_lock_at i) nm -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type UARTINITONE.
  Parameter wp_uartinitone_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (i : uart_id) (γd : uart_names) (nm : string) (nm_addr : mword 64)
      (m : regfile) (K : nat)
      (l : list (bv 8)) (b0 : bool) (k : nat) (hl : option (list mobs))
      (p : mword 64),
      wp_uartinitone_sconf_body i γd nm nm_addr m K l b0 k hl p.
End UARTINITONE.
