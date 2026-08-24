(* UartWidth.v -- THE BUS NARROWS a wide access to ONE byte register.
   Eleven observations, all of them agreeing.

   Source: tools/vtest/tests/uart_width.S.  Capture: UartWidthGen.v.

   All eight of the 16550's registers are bytes inside a single aligned
   doubleword, so reading the status word with one `lw` is a thing real
   drivers do.  What such an access MEANS is not the guess a reader makes:
   the bus does NOT gather offsets 4..7 into a word.  It hands the access to
   the ONE register the address names, zero-extends the byte on the way back
   and takes the low byte on the way in -- at 2, 4 and 8 bytes alike, which
   this program checks at each width in each direction.

   THIS FILE USED TO RECORD FINDING 9, and the shape of the fix is why the
   finding was worth recording.  [DevModel.dev_read]/[dev_write] decoded the
   UART window at width 1 and refused every other, so an ordinary `lw` of the
   status word was a STUCK machine and a driver that did it had no model
   execution at all.  The fix is NOT to gather bytes -- that is what the
   hardware does not do, and the test says so at +16, which would carry the
   SCRATCH byte the program stores at +7 if the bus gathered.  It is to
   model the NARROWING: [uart_dev_read]/[uart_dev_write] service one byte
   register per transaction at any width the bus carries. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest UartWidthGen.
Local Open Scope Z_scope.

Definition width_run : option mstate := run_until 50000 (start uart_width_text).

(* result-region offsets, mirroring tools/vtest/tests/uart_width.S *)
Definition width_offs : list nat :=
  [4;   (* progress marker: 3 = the whole program ran *)
   8;   (* LSR by a 1-byte read                            0x60 *)
   12;  (* SCRATCH by a 1-byte read                        0x5a *)
   16;  (* 4-byte read at UART0+4: MCR ALONE                  3 *)
   20;  (* 2-byte read at UART0+6: MSR                     0xb0 *)
   24;  (* 2-byte read at UART0+4: MCR again                  3 *)
   28;  (* 4-byte read at UART0+0, DLAB set: DLL           0x33 *)
   32;  (* 8-byte read at the same place, low word         0x33 *)
   36;  (* ...and its high word                               0 *)
   40;  (* MCR after a 4-byte STORE of 0x11223344 to +4       4 *)
   44;  (* DLL after a 2-byte STORE of 0xbeef to +0        0xef *)
   48]%nat. (* DLM, which that store did NOT reach         0x44 *)

Definition width_expect :=
  (fun o => cap_word uart_width_qemu_result o) <$> width_offs.

Lemma uart_width_agrees :
  (fun o => res_word width_run o) <$> width_offs = width_expect.
Proof. solve_vtest width_expect. Qed.

(* Spelled out, because the point of the test is which of two plausible
   answers the machine gives:

     +16  lw  at +4   3       -- MCR alone.  A bus that GATHERED would give
                                 0x5ab06003 (SCRATCH, MSR, LSR, MCR), and the
                                 program stores 0x5a to SCRATCH first exactly
                                 so that the difference is visible.
     +20  lhu at +6   0xb0    -- MSR alone, not MSR|SCRATCH<<8.
     +32  ld  at +0   0x33    -- and +36 = 0, so eight bytes is still one
                                 register, zero-extended.
     +40  sw  at +4   4       -- the low byte 0x44 landed, masked to MCR's
                                 five bits; the other three bytes are gone.
     +48  DLM         0x44    -- the 2-byte store at +0 did not spill into
                                 the next register, which is the write-side
                                 twin of +20. *)

(* ---------------------------------------------------------------------- *)
(* What this does NOT say.  The narrowing is the BUS's, not the device's:   *)
(* it is [dev_read]/[dev_write] that split the transaction, and             *)
(* [uart_read]/[uart_write] still only ever see a byte offset.  So a wide   *)
(* access is not the concatenation of independent byte accesses, and it     *)
(* must not become one: offset 0 is READ-SENSITIVE (RHR pops the receive    *)
(* FIFO), so a gathering read would pop it as a side effect of reading the  *)
(* line status.  The machine does not, and neither does the model.          *)
(* ---------------------------------------------------------------------- *)
