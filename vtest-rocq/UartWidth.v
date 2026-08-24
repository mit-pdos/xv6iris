(* UartWidth.v -- THE MODEL GETS STUCK where the hardware completes: a 4-byte
   access to the UART window.

   Source: tools/vtest/tests/uart_width.S.  Capture: UartWidthGen.v.

   [DevModel.dev_read] and [dev_write] decode the UART window at width 1 and
   at no other: every other [n] falls through to [None].  There is nothing
   accidental about the bus, either -- the PLIC is decoded at width 4 only
   and the virtio window at width 4 only -- but for the UART the restriction
   is visible to an ordinary driver, because all eight of its registers are
   bytes inside a single aligned word and reading them with one `lw` is a
   thing real code does.

   The program does two byte-wide accesses first (LSR, then SCRATCH written
   and read back) so that the stopping point is unambiguous, then one
   `lw t0, 4(s0)`.  QEMU completes it; the model has no transition at all. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest UartWidthGen.
Local Open Scope Z_scope.

(* Stated POSITIVELY: not "the result is empty" but "the machine is stuck",
   and at WHICH instruction.  [VBudget] would mean a broken test instead. *)
Lemma uart_width_model_stuck :
  run_status 50000 (start uart_width_text) = VStuck.
Proof. solve_vtest VStuck. Qed.

(* 0x80000074 is `lw t0,4(s0)` in
   riscv64-linux-gnu-objdump -d tools/vtest/build/uart_width.elf,
   i.e. the 4-byte load at UART0+4 -- checked against the disassembly, so
   this test names the access the model refuses and not merely that one of
   them was refused. *)
Lemma uart_width_stuck_at :
  stuck_pc 50000 (start uart_width_text) = 0x80000074.
Proof. solve_vtest (0x80000074 : Z). Qed.

(* What QEMU did instead.  The load returns 0x00000008: the virt board's
   serial device implements byte accesses only, so the bus hands the 4-byte
   read to register 4 alone and zero-extends -- 0x08 is the MCR's reset
   value (OUT2).  It notably does NOT gather offsets 4..7 into a word, so
   the 0x5a this program had just stored to the SCRATCH register at offset 7
   does not appear in it.  The byte-wide fields either side agree with the
   model (see UartTx.v / UartRegs.v for those registers); this lemma exists
   to pin the value the model has no way to produce. *)
Definition width_qemu_word : list Z :=
  [cap_word uart_width_qemu_result 8;    (* LSR by a 1-byte read:  0x60 *)
   cap_word uart_width_qemu_result 12;   (* SCRATCH by a 1-byte read: 0x5a *)
   cap_word uart_width_qemu_result 16].  (* the 4-byte read at UART0+4: 8 *)

Lemma uart_width_qemu : width_qemu_word = [0x60; 0x5a; 8].
Proof. solve_vtest ([0x60; 0x5a; 8] : list Z). Qed.

(* ---------------------------------------------------------------------- *)
(* CLASSIFICATION: INCOMPLETENESS, and a stuck machine is never anything   *)
(* else.  The system theorem proves xv6 never gets stuck, so a stuck model *)
(* cannot make a proof wrong; what it does is put a driver outside the     *)
(* development entirely.  A driver that reads the UART's status word with  *)
(* one load -- or writes one, or uses `lh` for the two divisor-latch bytes *)
(* at once -- has NO model execution, so no proof about it can even be     *)
(* stated.  xv6's uart.c uses `volatile unsigned char *` throughout, which *)
(* is why the restriction has cost the development nothing so far.         *)
(*                                                                         *)
(* It is also cheap to lift, unlike the disk findings: [dev_read]'s UART    *)
(* arm would split an [n]-byte access into [n] calls of [uart_read] at      *)
(* consecutive offsets.  What makes that a decision rather than a          *)
(* drive-by is that the offsets are READ-SENSITIVE -- offset 0 pops the rx *)
(* FIFO -- so a wide read is not the concatenation of independent byte     *)
(* reads, and QEMU shows the hardware does not do the concatenation either *)
(* (it services register 4 only).  Matching the hardware means modelling    *)
(* the BUS's narrowing, not widening the device.                           *)
(* ---------------------------------------------------------------------- *)
