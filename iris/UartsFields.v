(* UartsFields.v -- the two IMMUTABLE fields of each `struct uart`.
   
   At XV6_REV 163d39b the kernel's two 16550s share one array in .data:
   
     struct uart { uint64 base; void ( *rx)(int); struct spinlock tx_lock; };
     struct uart uarts[] = { [0] = {UART0, consoleintr}, [1] = {UART1, 0} };
   
   so the two statics the driver used to have -- `tx_lock` and `tx_chan` --
   are gone from the symbol table and every UART function reaches its port
   through `&uarts[uid]`.  The layout is read off the code, not assumed:
   [uartinit] passes `uarts + 0x28` for `&uarts[1]` (so the STRIDE is 40) and
   [uartputc_sync] computes `((uid*4 + uid) << 3) + 16 + uarts` for the lock
   (so `tx_lock` is at +16, leaving `base` at +0 and `rx` at +8).
   
   THE MMIO ADDRESS IS NOW A LOADED VALUE.  `uartputc_sync` does `ld a3,0(s4)`
   and stores at `a3 + off`, so a proof of that store needs to know what the
   .data word HOLDS.  `base` and `rx` are written by the loader and by nobody
   else -- the kernel never assigns either -- so the right resource is a
   PERSISTENT word snapshot at [DfracDiscarded], minted once at boot out of
   the loaded image, exactly as the boot chain already mints `_entry`'s GOT
   slot ([BootShared]'s `entry_got` / [BootCarve.boot_ran_phys_word]).  It is
   persistent because eight harts share it and nobody may take it away.
   
   THE CARVE HAS ROOM.  `uarts` sits in the gap between `nextpid + 4` and the
   GOT, which the boot chain currently cuts out and DROPS, so claiming these
   two words per port is additive: no existing claim shrinks.
   
   The tx_lock field is NOT here -- it is a lock like any other, and its
   address is [UartTxInv]'s business. *)
From stdpp Require Import gmap finite bitvector.definitions.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes RiscvLang RiscvPtsto DevModel PowerBoot.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Geometry.                                                            *)
(* ---------------------------------------------------------------------- *)

(* the array's stride, in bytes: [uartinit] passes [uarts + 0x28] for
   [&uarts[1]] *)
Definition uart_stride : Z := 40.

Definition uart_index (i : uart_id) : Z :=
  match i with Uart0 => 0 | Uart1 => 1 end.

Definition uart_elt (i : uart_id) : Z :=
  KernelSyms.uarts + uart_stride * uart_index i.

(* the three fields, at the offsets [uartinitone]/[uartputc_sync] use *)
Definition uart_f_base (i : uart_id) : Z := uart_elt i.
Definition uart_f_rx   (i : uart_id) : Z := uart_elt i + 8.
Definition uart_f_lock (i : uart_id) : Z := uart_elt i + 16.

(* THE SLEEP CHANNEL IS THE ELEMENT ITSELF: `sleep_prepare(u)` /
   `wakeup(u)` with `u = &uarts[uid]`, where the old code used
   `&tx_chan`. *)
Definition uart_f_chan (i : uart_id) : Z := uart_elt i.

(* the array is eighty bytes of .data, above [nextpid] and below the GOT *)
Lemma uart_elt_range (i : uart_id) :
  KernelSyms.uarts <= uart_elt i /\ uart_elt i + uart_stride
                                    <= KernelSyms.uarts + 2 * uart_stride.
Proof. destruct i; unfold uart_elt, uart_stride, uart_index; cbn; lia. Qed.

Lemma uart_elt_inj (i j : uart_id) : uart_elt i = uart_elt j -> i = j.
Proof.
  destruct i, j; unfold uart_elt, uart_stride, uart_index; cbn; try done;
    intro H; exfalso; lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. What the two immutable fields HOLD, as a persistent snapshot.        *)
(* ---------------------------------------------------------------------- *)

Section UartsFields.
  Context `{!riscvGS Σ}.

  (* port [i]'s MMIO window base, as the .data word holds it *)
  Definition uart_base_pinned (i : uart_id) : iProp Σ :=
    (pa_of_z (uart_f_base i) ↦ₚ₈□ Z_to_bv 64 (uart_base i))%I.

  (* ...and its receive hook: [consoleintr] for the console, NULL for the
     port with nowhere for input to go.  [uartinitone] reads it to decide
     whether to enable the receive interrupt, and [uartintr] to decide
     whether to call it, so both need the value and not just the cell. *)
  Definition uart_rx_hook (i : uart_id) : Z :=
    match i with Uart0 => KernelSyms.consoleintr | Uart1 => 0 end.

  Definition uart_rx_pinned (i : uart_id) : iProp Σ :=
    (pa_of_z (uart_f_rx i) ↦ₚ₈□ Z_to_bv 64 (uart_rx_hook i))%I.

  (* the pair, at both ports: what the boot chain mints once and every UART
     function takes *)
  Definition uarts_pinned : iProp Σ :=
    ([∗ list] i ∈ enum uart_id, uart_base_pinned i ∗ uart_rx_pinned i)%I.

  Global Instance uart_base_pinned_persistent i : Persistent (uart_base_pinned i).
  Proof. rewrite /uart_base_pinned. apply _. Qed.
  Global Instance uart_rx_pinned_persistent i : Persistent (uart_rx_pinned i).
  Proof. rewrite /uart_rx_pinned. apply _. Qed.
  Global Instance uarts_pinned_persistent : Persistent uarts_pinned.
  Proof. rewrite /uarts_pinned. apply _. Qed.

  (* focus one port out of the pair, the only way a rule reaches it *)
  Lemma uarts_pinned_at (i : uart_id) :
    uarts_pinned -∗ uart_base_pinned i ∗ uart_rx_pinned i.
  Proof.
    rewrite /uarts_pinned /enum /uart_id_finite /=.
    iIntros "#(H0 & H1 & _)". by destruct i.
  Qed.
End UartsFields.
