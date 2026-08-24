(* UartRx.v -- THE RECEIVE DATAPATH.  Nine observations agree; ONE diverges,
   and it is a new finding.

   Source: tools/vtest/tests/uart_rx.S.  Capture: UartRxGen.v.

   UartIrqRx.v receives a byte, but only as the condition that raises an
   interrupt.  This test is about the receive FIFO itself: four bytes are
   pushed in by the host, three are read out and checked for ORDER, and the
   fourth is still queued when an FCR write clears the FIFO out from under
   it.

   THE BYTES ARE A SCHEDULE CHOICE.  Receiving is the only externally-driven
   event in the suite and [VSched.settle] deliberately does not invent it, so
   the four bytes are four [SUartRx] items -- [DevModel.uart_rx_push] -- and
   this file delivers them before the program starts.  That is the shortest
   witness: the program spins on LSR bit 0 before every read, so any delivery
   point at or before each spin gives the same run.

   WHY THE FIFOs ARE NOT ENABLED, and what it costs.  Flipping FCR bit 0
   moves QEMU's 16550 from its one-byte holding register to its 16-byte FIFO,
   and the transition FLUSHES.  Measured: the host's first byte is already in
   the holding register before the guest's first instructions run, so an FCR
   FIFO-enable at the top of the program silently eats it -- the run then
   reads 0x42 first, 8 times out of 8.  With the FIFOs off, QEMU's front end
   hands over one character at a time and re-offers the next only after RHR
   has been read, so an "LSR bit 0 immediately after a read" field would be a
   race against the host rather than a fact about the device.  The test does
   not ask it, and does not need to: see section 2. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list bitvector.definitions.
Require Import VTest UartRxGen.
Local Open Scope Z_scope.

(* THE WITNESS: four bytes, delivered as four device steps. *)
Definition rx_start : option mstate :=
  srun [SUartRx 0x41; SUartRx 0x42; SUartRx 0x43; SUartRx 0x44]
       (start uart_rx_text).

Definition rx_run : option mstate :=
  match rx_start with Some s => run_until 50000 s | None => None end.

(* result-region offsets, mirroring tools/vtest/tests/uart_rx.S *)
Definition rx_agree_offs : list nat :=
  [4;   (* progress marker: 3 = the whole program ran *)
   8;   (* LSR with bytes waiting                 0x61 = DR|THRE|TEMT *)
   12; 16; 20;   (* RHR #1, #2, #3            0x41, 0x42, 0x43 -- IN ORDER *)
   24;  (* LSR with the fourth byte still waiting          0x61 *)
   28;  (* LSR after the FCR write with bit 1 set          0x60: DR gone *)
   36;  (* LSR after reading the emptied FIFO              0x60 *)
   40;  (* how many bytes a drain loop still finds         0 *)
   44]%nat. (* LSR at the end                             0x60 *)

Definition rx_diverge_offs : list nat :=
  [32]%nat.  (* RHR on the FIFO the clear just emptied *)

(* ---------------------------------------------------------------------- *)
(* 1. What agrees -- which is the datapath.                                *)
(* ---------------------------------------------------------------------- *)

Definition rx_expect :=
  (fun o => cap_word uart_rx_qemu_result o) <$> rx_agree_offs.

Lemma uart_rx_agrees :
  (fun o => res_word rx_run o) <$> rx_agree_offs = rx_expect.
Proof. solve_vtest rx_expect. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. What each field rules out.                                           *)
(*                                                                         *)
(*  - ORDER (+12/+16/+20 = 0x41, 0x42, 0x43).  [u_rx] is a FIFO in the      *)
(*    model: [uart_rx_push] appends to the tail and [uart_read] at offset 0 *)
(*    pops the head.  A LIFO, or a one-deep register that the newest byte   *)
(*    overwrites, passes a one-byte test and fails this one -- it would     *)
(*    give 0x44 or a repeat.  The hardware agrees byte for byte.            *)
(*                                                                         *)
(*  - EXACTLY ONE BYTE PER READ.  Not asked as an "LSR is still set" field, *)
(*    for the front-end reason in the header, but established anyway and    *)
(*    without a race: three reads of a four-byte queue return three         *)
(*    DISTINCT bytes in the injected order and the fourth is still there    *)
(*    at +24.  A read that popped two would have given 0x41, 0x43 and left  *)
(*    the queue dry, so the spin before the fourth observation would hang   *)
(*    and the test would never publish its result; a read that popped none  *)
(*    would have repeated 0x41.                                            *)
(*                                                                         *)
(*  - LSR BIT 0 TRACKS THE FIFO, across the whole sequence: set while bytes *)
(*    remain (+8, +24), clear once the FIFO is empty (+28, +36, +44), and   *)
(*    not sticky either way.  [uart_lsr]'s [uart_rx_ready] disjunct is the  *)
(*    only thing that can move that bit, and 0x61 versus 0x60 is exactly    *)
(*    it, with THRE|TEMT constant underneath.                               *)
(*                                                                         *)
(*  - FCR BIT 1 CLEARS THE RECEIVE FIFO (+28 = 0x60, +40 = 0).  This is a   *)
(*    live arm of [uart_write] offset 2 that no test had exercised on the   *)
(*    rx side, and it is what xv6's uartinit writes at boot.  A byte that   *)
(*    had ALREADY ARRIVED is discarded by it -- the model's [u_rx] becomes  *)
(*    [] and the hardware's data-ready goes away -- so a driver that clears  *)
(*    the FIFO after opening the port loses what was typed before, on both  *)
(*    machines.  Note this is the receive-side twin of the transmit-side    *)
(*    fact UartRegs.v section 4 pins on [uart_acc].                         *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(* 3. The one divergence: RHR on an EMPTY receive FIFO.                    *)
(* ---------------------------------------------------------------------- *)

Definition rx_model_diverging : list Z := [0].
Definition rx_qemu_diverging  : list Z := [0x44].

Lemma uart_rx_model_diverging :
  (fun o => res_word rx_run o) <$> rx_diverge_offs = rx_model_diverging.
Proof. solve_vtest rx_model_diverging. Qed.

Lemma uart_rx_qemu_diverging :
  (fun o => cap_word uart_rx_qemu_result o) <$> rx_diverge_offs
  = rx_qemu_diverging.
Proof. solve_vtest rx_qemu_diverging. Qed.

Lemma uart_rx_really_diverges : rx_model_diverging <> rx_qemu_diverging.
Proof. discriminate. Qed.

(* INCOMPLETENESS, and NEW -- nothing in the suite had read RHR on a FIFO
   that had held something.

   [uart_read]'s offset-0 arm returns [byte0] when [u_rx] is empty.  The
   hardware's receive holding register is not cleared by a read and not
   cleared by the FCR clear either: only the DATA-READY flag is, so a read
   with DR clear returns the LAST BYTE RECEIVED -- here 0x44, the byte the
   FCR write had just discarded.  Both machines agree the byte is GONE in
   the sense that matters (+28 and +36 show DR clear, +40 shows the drain
   loop finds nothing), and a correct driver reads RHR only when DR is set,
   which is why this costs xv6 nothing.

   The direction is the model producing a value the hardware does not, which
   is the shape of a defect; it is classified as incompleteness because the
   value is only produced on a read the hardware calls undefined -- RHR with
   no data ready -- and 0 is as good an answer as any.  What it does mean is
   that no proof against this model can conclude anything about what such a
   read returns on a real port, and a driver that (wrongly, but really) uses
   a zero from RHR as an end-of-input signal would be verified against a
   device that does not exist.  UartDlab.v +32 is the other data point: on a
   port that has never received anything, both machines do read 0.

   The obvious fix -- keep the last byte in [uart_state] and return it -- is
   local to [uart_read], but it is not obviously right either, since the FCR
   clear and the DR flag would then have to be separated from [u_rx] being
   empty.  Recorded rather than made. *)

(* ---------------------------------------------------------------------- *)
(* 4. The receive FIFO's DEPTH is not worth a test, and this says why.     *)
(*                                                                         *)
(*    [uart_rx_push] refuses when [u_rx] already holds [uart_fifo_depth] =  *)
(*    16 bytes.  On the model side a refusal is not an observation: the     *)
(*    [SUartRx] item simply is not enabled, so [srun] answers [None] and    *)
(*    the whole run vanishes -- a fact about the harness, not a divergence  *)
(*    from anything.  Pinned here so that a future test does not mistake    *)
(*    the empty result for a finding.                                       *)
(* ---------------------------------------------------------------------- *)

Definition rx_seventeen : list sitem :=
  SUartRx <$> [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17].

Lemma uart_rx_seventeenth_push_is_not_enabled :
  srun rx_seventeen (start uart_rx_text) = None.
Proof. solve_vtest (@None mstate). Qed.

(* ...and sixteen are fine, in order, which is the FIFO depth stated
   positively. *)
Definition rx_sixteen : list sitem :=
  SUartRx <$> [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16].

Definition rx_sixteen_queued : list Z :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16].

Lemma uart_rx_sixteen_fit :
  match srun rx_sixteen (start uart_rx_text) with
  | Some s => bv_unsigned <$> u_rx (duart (mdev s))
  | None => []
  end = rx_sixteen_queued.
Proof. solve_vtest rx_sixteen_queued. Qed.
