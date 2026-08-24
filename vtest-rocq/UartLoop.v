(* UartLoop.v -- MCR, and the one bit of it with semantics: LOOPBACK.
   Ten observations and the serial channel, all agreeing.

   Source: tools/vtest/tests/uart_loop.S.  Capture: UartLoopGen.v.

   MCR bit 4 disconnects the transmitter from SOUT and wires it to this
   UART's own receiver, and wires the four modem OUTPUTS to the four modem
   INPUTS (DTR->DSR, RTS->CTS, OUT1->RI, OUT2->DCD).  It is the standard way
   to self-test a 16550, and the only way to exercise the receive path on a
   port nobody is typing at.

   THIS TEST EXISTS BECAUSE OF FINDING 6.  MCR used to read as zero and
   swallow its writes, so the model had no loopback -- and the fix could not
   be to make MCR readable and leave the bit inert, because a driver that
   enabled loopback would then have its bytes go out on the WIRE, which is a
   value the hardware never produces.  Making the register real means making
   the mode real, which is what [DevModel.uart_tx_pop]'s two arms are.

   THE SERIAL CHANNEL IS HALF THE TEST.  The byte transmitted under LOOP must
   come back on RHR and must NOT reach the host; the byte transmitted after
   LOOP is cleared must reach the host and must not come back.  So the
   expected output is exactly "Y" -- and that line is what a model which let
   the loopbacked 'A' onto the wire would fail, rather than any result
   word. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list bitvector.definitions.
Require Import VTest UartLoopGen.
Local Open Scope Z_scope.

Definition loop_run : option mstate := run_until 50000 (start uart_loop_text).

(* result-region offsets, mirroring tools/vtest/tests/uart_loop.S *)
Definition loop_offs : list nat :=
  [4;   (* progress marker: 4 = the whole program ran *)
   8;   (* MCR at power-on                              8    = OUT2 *)
   12;  (* MCR read back after storing 0xff             0x1f = five bits *)
   16;  (* MSR with LOOP|RTS|DTR                        0x30 = DSR|CTS *)
   20;  (* MSR with LOOP and all four outputs driven    0xf0 = all four *)
   24;  (* LSR after a THR write under LOOP             0x61 = DR set *)
   28;  (* RHR: the byte, back from our own transmitter 0x41 = 'A' *)
   32;  (* LSR after that read                          0x60 = DR gone *)
   36;  (* MSR with LOOP cleared again                  0xb0 = the cable *)
   40]%nat. (* LSR at the end                           0x60 *)

Definition loop_expect :=
  ((fun o => cap_word uart_loop_qemu_result o) <$> loop_offs,
   uart_loop_qemu_serial).

Lemma uart_loop_agrees :
  ((fun o => res_word loop_run o) <$> loop_offs, serial_of loop_run)
  = loop_expect.
Proof. solve_vtest loop_expect. Qed.

(* ---------------------------------------------------------------------- *)
(* 1. What each field rules out.                                           *)
(*                                                                         *)
(*  - MCR IS FIVE BITS OF STORAGE (+8, +12).  0xff reads back as 0x1f, so   *)
(*    a model that stored the whole byte would fail +12 and one that        *)
(*    stored nothing would fail both.  +8 is the power-on value, which is   *)
(*    the board's and not the chip's: this port comes up with OUT2          *)
(*    asserted (it is also the byte UartWidth.v's 4-byte read hands back).  *)
(*                                                                         *)
(*  - THE MODEM LOOP IS WIRED PIN FOR PIN (+16, +20).  With DTR and RTS     *)
(*    driven, DSR and CTS come back and RI and DCD do not; with all four    *)
(*    driven, all four come back.  One field alone would be passed by a     *)
(*    model that returned a constant under LOOP; the pair pins the mapping. *)
(*    +36 is the same register with LOOP cleared, which is the port's own   *)
(*    idle level again -- so the aliasing is not sticky.                    *)
(*                                                                         *)
(*  - THE DATA LOOP IS THE RECEIVE PATH (+24, +28, +32).  DR becomes set    *)
(*    with no serial input at all, RHR hands back the transmitted byte, and *)
(*    DR goes away when it is read.  The program SPINS on DR rather than    *)
(*    reading it once, so the return trip is allowed to be the device's own *)
(*    later step -- which it is on both machines, and the model's is        *)
(*    [uart_tx_pop]'s loopback arm handing the byte to [uart_recv].         *)
(*                                                                         *)
(*  - AND NOTHING OF IT REACHED THE HOST.  The serial channel is "Y": one   *)
(*    byte, the one written after LOOP was cleared.  This is the field that *)
(*    a "store MCR but ignore bit 4" model fails, and it is the reason      *)
(*    [DevModel.uart_state] carries [u_wire] beside [u_out] at all -- the   *)
(*    transmitter is done with a loopbacked byte (so [uart_acc] and the     *)
(*    whole transmitter-token argument in WpUart.v are untouched), but the  *)
(*    wire never carried it.                                               *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(* 2. The two states off the model, so the claim above is stated about the  *)
(*    DEVICE and not only about this program's schedule.                    *)
(* ---------------------------------------------------------------------- *)

Definition loop_uart : uart_state :=
  match uart_write uart0_state 4 (Z_to_bv 8 0x10) with   (* MCR: LOOP *)
  | Some u => match uart_write u 0 (Z_to_bv 8 0x41) with (* THR: 'A' *)
              | Some u' => match uart_tx_pop u' with
                           | Some (_, u'') => u'' | None => u'
                           end
              | None => u
              end
  | None => uart0_state
  end.

Definition plain_uart : uart_state :=
  match uart_write uart0_state 0 (Z_to_bv 8 0x41) with
  | Some u => match uart_tx_pop u with Some (_, u') => u' | None => u end
  | None => uart0_state
  end.

(* the byte was ACCEPTED and the transmitter is done with it in both cases --
   which is what a driver's postcondition talks about... *)
Lemma uart_loop_accepted :
  (bv_unsigned <$> uart_acc loop_uart, bv_unsigned <$> uart_acc plain_uart)
  = ([0x41], [0x41]).
Proof. solve_vtest ([0x41] : list Z, [0x41] : list Z). Qed.

(* ...and the WIRE tells the two apart. *)
Lemma uart_loop_wire :
  (bv_unsigned <$> u_wire loop_uart, bv_unsigned <$> u_wire plain_uart)
  = (@nil Z, [0x41]).
Proof. solve_vtest (@nil Z, [0x41] : list Z). Qed.

(* the loopbacked byte is where the receiver put it, and only there *)
Lemma uart_loop_received :
  (bv_unsigned <$> u_rx loop_uart, bv_unsigned <$> u_rx plain_uart)
  = ([0x41], @nil Z).
Proof. solve_vtest ([0x41] : list Z, @nil Z). Qed.
