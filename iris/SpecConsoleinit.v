(* SpecConsoleinit.v -- the public interface of Consoleinit, stated
   independently of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

     void consoleinit(void) {
       initlock(&cons.lock, "cons");
       uartinit();
       devsw[CONSOLE].read  = consoleread;
       devsw[CONSOLE].write = consolewrite;
     }

   consoleinit is the first thing main() calls, and it is a pure composition:
   its contract is exactly initlock's on [cons.lock] (which sits at offset 0 of
   the [cons] global, so [&cons.lock = &cons]) + uartinit's, plus the two
   function-pointer stores.  So it carries uartinit's DEVICE transit one level
   up, verbatim: in come [WpUart.uart_inv], the "everything accepted has been
   transmitted / the transmitter is mine" pair at [l], and the UNFROZEN DLAB
   half at an arbitrary [b0]; out come the tokens at the same [l] (uartinit
   writes no THR) and the frozen [uart_dlab_off].  See SpecUartinit.v for why a
   raw [uart_frag] shape is not viable here: the UART thread runs from step 0,
   so the fragment can never sit raw in a CPU's precondition, and the
   FIFO-clear / DLAB-set writes are discharged by ghost arithmetic instead.

   The devsw[] slots are handed back as the raw 8-byte cells holding the two
   function addresses.  Nothing yet says what a [struct devsw] entry MEANS --
   consoleread/consolewrite are unproven and the fs-side dispatch that reads
   these slots does not exist -- so anything richer would be a predicate with no
   consumer.  When one arrives it is built at the caller from these cells.

   TWO LOCKS ARE INITIALIZED UNDER THIS CONTRACT: [cons.lock], by consoleinit
   itself, and [tx_lock], by the uartinit call it makes.  tx_lock is a [struct
   spinlock] and uartinit ends with [initlock(&tx_lock, "uart")], so its
   storage rides through here as [SpecProcinit.lk_raw] in and [lk_fresh] out
   -- three cells over 24 bytes.
     It is PURE TRANSIT: consoleinit never names a field of it, and the round
   trip costs this contract nothing at all -- not even a stack slot, since
   [initlock] is no deeper than the frame consoleinit already reserves for
   uartinit.  What it BUYS is that [lk_fresh] reaches a caller that can run
   [WpLock.newlock], which is the missing half of
   [WpLock.newlock], once a boot assembly wants the transmit lock.

   ProofConsoleinit.v proves it as a functor over [INITLOCK] and [UARTINIT];
   consoleinit touches no MMIO of its own, so the device side is pure transit
   into and out of the uartinit call. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpLock.
Require Import WpUart.
Require Import UartTxInv.
(* [lk_raw] / [lk_fresh] -- the three-cell spinlock bundle, before and after
   [initlock]; tx_lock's storage is pure transit through this contract. *)
Require Import SpecProcinit.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)


(* The address of the string literal "cons" that consoleinit passes as
   initlock's [name] argument.  It is the first word of .rodata, at [etext]
   itself, and has no ELF symbol of its own, so it is spelled out here (see
   kernel.asm: 80007000 <etext>). *)
Definition cons_name_str : Z := 0x80007000%Z.

(* devsw[CONSOLE].  CONSOLE = 1 and a [struct devsw] is two function pointers,
   so the entry starts at devsw + 16, its [.read] field at +0 and [.write] at
   +8 -- the two offsets the code's [c.sd a4,16(a5)] / [c.sd a4,24(a5)] pair
   writes. *)
Definition devsw_console_read : mword 64 := mword_of_int (KernelSyms.devsw + 16).
Definition devsw_console_write : mword 64 := mword_of_int (KernelSyms.devsw + 24).

(* BOOT-ONLY: consoleinit's callee uartinit is itself stated at the literal
   index [false] (interrupts never on before intr_on(), see
   SpecUartinit.v), so a [b]-generic consoleinit could never call it -- the
   [sie_cap_gpr] its call to uartinit hands over would need to unify a
   generic [b] with the callee's literal [false].  consoleinit is called
   only from main() before intr_on(), so it is stated at [false] with no
   [wp_next] wrapper, the same shape as SpecCpuid.v / SpecTrapinithart.v /
   SpecPlicClaim.v. *)
Definition wp_consoleinit_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
    (γd : uart_names) (m : regfile) (K : nat)
    (l : list (bv 8)) (b0 : bool)
    (vclock : bv 32) (vcname vccpu : bv 64)
    (dread0 dwrite0 : mword 64) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.consoleinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (* &cons.lock = &cons: the spinlock is the first field of the [cons] struct *)
  let clk : mword 64 := mword_of_int KernelSyms.cons in
  let c_cname := lock_name_field clk in
  let c_ccpu := add_vec clk (sign_extend' 64 (mword_of_int 0x10 : mword 12)) in
  (* consoleinit's own frame is [addi sp,sp,-16] = 2 slots, and its deepest
     callee is uartinit, which needs 4 (its own 2-slot frame plus initlock's
     2).  So the budget is 2 + 4. *)
  (6 <= K)%nat ->
  sie_cap_gpr KT0 m K false p -∗
  (* [kernel_data] supplies the "cons" string literal consoleinit's [auipc a1 /
     addi a1] points at -- the name it hands to initlock -- and, through
     uartinit's own spec, the "uart" one. *)
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the UART fabric, borrowed from the invariant around each of uartinit's
     seven writes; the token/receipt pair is what makes the FCR FIFO-clear
     shrink nothing, and the unfrozen DLAB half is what survives the
     divisor-latch dance (SpecUartinit.v). *)
  uart_inv γd -∗
  uart_tx_own γd l -∗ uart_out_lb γd l -∗ uart_sent γd l -∗
  uart_dlab_is γd (DfracOwn (1/2)) b0 -∗
  clk ↦₄ vclock -∗
  c_cname ↦₈ vcname -∗
  c_ccpu ↦₈ vccpu -∗
  (* tx_lock's three raw fields, PASSED STRAIGHT THROUGH to uartinit.
     consoleinit itself names no field of it; it is only on the path between
     the boot assembly that owns the bss and the initlock call that consumes
     it. *)
  lk_raw UartTxInv.a_tx_lock -∗
  devsw_console_read ↦₈ dread0 -∗
  devsw_console_write ↦₈ dwrite0 -∗
  ( ∀ mr,
    sie_cap_gpr KT0 mr K false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (* uartinit writes no THR, so the accepted trace is unchanged; its final
       LCR write cleared DLAB, so the half is frozen for good. *)
    uart_tx_own γd l -∗ uart_sent γd l -∗ uart_dlab_off γd -∗
    (* cons.lock comes back initialized; it is a static global that is never
       freed, so its name field is DISCARDED for the persistent [lock_name],
       ready to be sealed into an [is_lock]. *)
    clk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name clk "cons"%string -∗
    c_ccpu ↦₈ (zero_reg : mword 64) -∗
    (* and back out initialized: [WpLock.newlock]'s raw material, which is
       what lets a boot assembly mint [UartTxInv.is_txlock]
       ([WpLock.newlock] over [UartTxInv.tx_res]). *)
    lk_fresh UartTxInv.a_tx_lock "uart"%string -∗
    devsw_console_read ↦₈ (mword_of_int KernelSyms.consoleread : mword 64) -∗
    devsw_console_write ↦₈ (mword_of_int KernelSyms.consolewrite : mword 64) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CONSOLEINIT.
  Parameter wp_consoleinit_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
      (γd : uart_names) (m : regfile) (K : nat)
      (l : list (bv 8)) (b0 : bool)
      (vclock : bv 32) (vcname vccpu : bv 64)
      (dread0 dwrite0 : mword 64) (p : mword 64),
      wp_consoleinit_sconf_body γd m K l b0 vclock vcname vccpu dread0 dwrite0 p.
End CONSOLEINIT.
