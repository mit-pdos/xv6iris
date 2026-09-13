(* SpecUartinit.v -- the public interface of Uartinit, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   AT XV6_REV 163d39b [uartinit] IS A TWO-CALL WRAPPER AND NOTHING ELSE:

     void uartinit(void) {
       uartinitone(&uarts[0], "uart0");
       uartinitone(&uarts[1], "uart1");
     }

   The seven MMIO writes and the [initlock] moved into [uartinitone], which
   has a symbol and a contract of its own ([SpecUartinitone]); this file is
   two applications of that contract, one per element of [uarts[]], plus the
   prologue/epilogue and the two argument pairs.  Everything that used to be
   said here about the device -- the FCR FIFO-clear, the baud-latch dance,
   the DLAB freeze -- is said there, once, for both ports.

   WHAT THIS FILE STILL OWNS is the pairing:

   - THE TWO PORTS' GHOST BUNDLES, side by side.  The contract takes one per
     port and hands one back per port.  The bundles are the SAME shape at
     both, deliberately: the owner's ruling for this bump is that UART1's
     OUTPUT is unconstrained, but that says who CONSUMES [uart_sent], not
     whether the port has FIFO and DLAB ghosts -- the FCR clear and the
     baud-latch dance are the same instructions at both ports, so both need
     the token, the transmitted-prefix bound and the unfrozen DLAB half.
     The second port's caller simply drops the trace claims it gets back.

   - THE TWO [.rodata] NAMES.  The old single "uart" left the image with the
     old single [tx_lock]; the literals are "uart0" and "uart1" now, and
     [uartinit] is the only place that knows which port gets which.  Their
     addresses are DERIVED BY CONTENT out of [KernelData] (a NUL before and
     after) and spelled [KernelSyms.etext + <off>], so an ordinary
     text-growing bump carries them for free.

   - THE PINNED FIELDS.  Every [WriteReg(u, …)] inside [uartinitone] loads
     [u->base] out of `.data` and the last one reads [u->rx], so the callee
     takes [uart_base_word i] / [uart_rx_word i] -- the VA-tier snapshots an
     S-mode [ld] leaf consumes.  uartinit relays all four; the boot chain
     mints them.

   THE STACK BUDGET IS 2 + 4.  uartinit's own frame is two slots
   ([addi sp,sp,-16]) and [uartinitone] asks [(4 <= av)] of what is left
   (its own two plus [initlock]'s two).  That is ONE SLICE MORE than the old
   flat uartinit needed, and it ripples: [SpecConsoleinit]'s premise, and
   main's through it, have to widen with it. *)
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
Require Import SpecUartPutc.  (* [uart_base_word] *)
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
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The two lock-name literals in `.rodata`.                                *)
(*                                                                        *)
(* DERIVED BY CONTENT, not by arithmetic: each is the unique NUL-preceded, *)
(* NUL-terminated occurrence of its own name in [KernelData.kernel_data],  *)
(* and both are spelled [KernelSyms.etext + <off>] because [etext] IS the  *)
(* base of `.rodata` -- written that way an ordinary text-growing bump     *)
(* carries them and only a `.rodata` REORDERING touches the offset.        *)
(* The [ltac:(eval vm_compute …)] shape is load-bearing: the body stays a  *)
(* plain [Z] literal downstream, which is what the byte lemmas'            *)
(* [vm_compute] and [lia] need (xv6-bump-playbook.md section 4b).          *)
(* ---------------------------------------------------------------------- *)
Definition uart0_name_str : Z :=
  ltac:(let x := eval vm_compute in (KernelSyms.etext + 0x30)%Z in exact x).
Definition uart1_name_str : Z :=
  ltac:(let x := eval vm_compute in (KernelSyms.etext + 0x38)%Z in exact x).

Definition uart_name_str (i : uart_id) : Z :=
  match i with Uart0 => uart0_name_str | Uart1 => uart1_name_str end.

(* the string itself is the LOCK's name, so it is [UartTxInv]'s -- the one
   place that says what an [is_lock] over a transmit lock is named. *)
Definition uart_name (i : uart_id) : string := uart_lock_name i.


Definition wp_uartinit_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γ0 γ1 : uart_names) (m : regfile) (K : nat)
    (l0 l1 : list (bv 8)) (d0 d1 : bool)
    (k0 k1 : nat) (hl0 hl1 : option (list mobs))
    (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uartinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (* uartinit's own two slots over [uartinitone]'s four *)
  (6 <= K)%nat ->
  sie_cap_gpr KT0 m K false p -∗
  (* [kernel_data] is load-bearing: it is where the two "uart0"/"uart1"
     string literals the [auipc a1 / addi a1] pairs point at come from. *)
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the four immutable `.data` words of [uarts[]], both ports, at the VA
     tier -- the form the callee's [ld] leaves consume.  Persistent, minted
     once in the boot chain ([BootShared]'s `.data` walk, which crosses them
     from the physical [UartsFields.uarts_pinned] it carves). *)
  uart_base_word Uart0 -∗ uart_rx_word Uart0 -∗
  uart_base_word Uart1 -∗ uart_rx_word Uart1 -∗
  (* ---- the console port ---- *)
  uart_inv Uart0 γ0 -∗
  uart_tx_own γ0 l0 -∗ uart_out_lb γ0 l0 -∗ uart_sent γ0 l0 -∗
  uart_rx_tok γ0 k0 hl0 -∗
  uart_dlab_is γ0 (DfracOwn (1/2)) d0 -∗
  lk_raw (a_tx_lock_at Uart0) -∗
  (* ---- the printk/panic port ---- *)
  uart_inv Uart1 γ1 -∗
  uart_tx_own γ1 l1 -∗ uart_out_lb γ1 l1 -∗ uart_sent γ1 l1 -∗
  uart_rx_tok γ1 k1 hl1 -∗
  uart_dlab_is γ1 (DfracOwn (1/2)) d1 -∗
  lk_raw (a_tx_lock_at Uart1) -∗
  ( ∀ mr,
    sie_cap_gpr KT0 mr K false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (* neither call writes THR, so both accepted traces are untouched *)
    uart_tx_own γ0 l0 -∗ uart_sent γ0 l0 -∗
    (∃ (k' : nat) (hl' : option (list mobs)), uart_rx_tok γ0 k' hl') -∗
    uart_dlab_off γ0 -∗
    lk_fresh (a_tx_lock_at Uart0) (uart_name Uart0) -∗
    uart_tx_own γ1 l1 -∗ uart_sent γ1 l1 -∗
    (∃ (k' : nat) (hl' : option (list mobs)), uart_rx_tok γ1 k' hl') -∗
    uart_dlab_off γ1 -∗
    lk_fresh (a_tx_lock_at Uart1) (uart_name Uart1) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type UARTINIT.
  Parameter wp_uartinit_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γ0 γ1 : uart_names) (m : regfile) (K : nat)
      (l0 l1 : list (bv 8)) (d0 d1 : bool)
      (k0 k1 : nat) (hl0 hl1 : option (list mobs))
      (p : mword 64),
      wp_uartinit_sconf_body γ0 γ1 m K l0 l1 d0 d1 k0 k1 hl0 hl1 p.
End UARTINIT.
