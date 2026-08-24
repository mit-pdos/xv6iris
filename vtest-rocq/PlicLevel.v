(* PlicLevel.v -- the GATEWAY on a source whose level the driver never drops.

   Source: tools/vtest/tests/plic_level.S.  Capture: PlicLevelGen.v.

   disk_intr walks the happy path: it acknowledges the DEVICE first, so by
   the time it completes at the PLIC the line is already low and the gateway
   has nothing left to forward.  This test does the two things that path
   never does, on one source -- the 16550 on source 10, raised with NO serial
   input by enabling the transmit-holding-register-empty interrupt in IER
   while the FIFO is empty.  No virtqueue, so the model side declares only
   the stack and the result region.

   Phase 1, the level DROPS with the request still pending and unclaimed,
   AGREES: pending is sticky on both machines, and the context still sees the
   request after its source has gone quiet.  Phase 2, the context COMPLETES
   while the level is still asserted, does not -- section 3. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PlicLevelGen.
Local Open Scope Z_scope.

Definition level_run : option mstate := run_until 50000 (start plic_level_text).

(* result-region offsets, mirroring tools/vtest/tests/plic_level.S *)
Definition level_agree_offs : list nat :=
  [4;   (* progress marker: 3 = ran to the end                            *)
   8;   (* pending, the line up                              0x400        *)
   12;  (* pending after the line DROPS -- STICKY            0x400        *)
   16;  (* mip & SEIP there                                  0x200        *)
   20;  (* pending, the line up again                        0x400        *)
   24;  (* the claim                                         10           *)
   28;  (* pending after it                                  0            *)
   44;  (* the UART's IER read back                          2            *)
   48]%nat. (* the UART's LSR: THRE|TEMT still set           0x60         *)

Definition level_diverge_offs : list nat :=
  [32;  (* pending after COMPLETE, the line still asserted                *)
   36;  (* mip & SEIP there                                               *)
   40]%nat. (* a second claim                                             *)

(* ---------------------------------------------------------------------- *)
(* 1. What agrees, and the first half of it is worth its own sentence.     *)
(*                                                                         *)
(*    A FORWARDED REQUEST IS STICKY.  +12: the driver lowers IER, the       *)
(*    16550 drops its line, and the pending bit stays -- on both machines.  *)
(*    [plic_latch] only ever SETS [p_pending] and nothing but a claim ever  *)
(*    clears it, so the model could not do otherwise; the question was      *)
(*    whether the hardware agrees, and it does (QEMU's PLIC sets pending on *)
(*    a rising level and never on a falling one).  +16 confirms the         *)
(*    notification is still driven from the pending SET, not from the wire. *)
(*    A gateway that mirrored the line instead would withdraw an interrupt  *)
(*    the driver has already been told about.                              *)
(*                                                                         *)
(*    +44 and +48 are what make section 3 a statement about the GATEWAY     *)
(*    rather than about the UART: at the end of the run IER bit 1 is still  *)
(*    set and the transmit FIFO is still empty, on both machines, and that  *)
(*    conjunction IS the THRE interrupt condition.  So the source's level   *)
(*    really is asserted at the moment of the complete on both sides, and   *)
(*    the two machines differ on what to do about it, not on whether there  *)
(*    is anything to do.                                                    *)
(* ---------------------------------------------------------------------- *)

Definition level_expect : list Z :=
  (fun o => cap_word plic_level_qemu_result o) <$> level_agree_offs.

Lemma plic_level_agrees :
  (fun o => res_word level_run o) <$> level_agree_offs = level_expect.
Proof. solve_vtest level_expect. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. What does not.  Pinned on both sides.                                *)
(* ---------------------------------------------------------------------- *)

(* the model: [plic_complete] clears [p_claimed], and the gateway's guard
   -- forward only when neither pending nor claimed -- comes true again with
   the level still high, so the source re-pends, the notification comes back
   and a second claim collects it *)
Definition level_model_diverging : list Z := [0x400; 0x200; 10].
(* QEMU: pending is set only by a RISING level, and there is no new edge *)
Definition level_qemu_diverging  : list Z := [0; 0; 0].

Lemma plic_level_model_diverging :
  (fun o => res_word level_run o) <$> level_diverge_offs = level_model_diverging.
Proof. solve_vtest level_model_diverging. Qed.

Lemma plic_level_qemu_diverging :
  (fun o => cap_word plic_level_qemu_result o) <$> level_diverge_offs
  = level_qemu_diverging.
Proof. solve_vtest level_qemu_diverging. Qed.

Lemma plic_level_really_diverges :
  level_model_diverging <> level_qemu_diverging.
Proof. discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The divergence, classified: INCOMPLETENESS -- the benign direction,   *)
(*    and it is benign for a reason worth writing down.                     *)
(*                                                                         *)
(* WHAT HAPPENS.  One device request; the model delivers TWO interrupts.    *)
(* [plic_complete] clears the claimed bit, [plic_latch]'s guard             *)
(* [negb (p_pending p i) && negb (p_claimed p i)] is satisfied again, the   *)
(* level is still high because nothing has told the 16550 to stop asking,   *)
(* and the gateway forwards it a second time.  QEMU forwards nothing: its   *)
(* PLIC takes pending off the RISING edge of the line, and there is no new  *)
(* edge, so the second request only appears there if something touches the  *)
(* UART again.                                                             *)
(*                                                                         *)
(* WHICH ONE IS THE HARDWARE?  The MODEL is the one following the PLIC      *)
(* specification here: a level-sensitive gateway is required to re-forward  *)
(* a level that is still asserted once the completion clears the in-service *)
(* marker -- that is precisely why a driver must acknowledge the DEVICE     *)
(* before completing at the PLIC, and why disk_intr does.  QEMU's           *)
(* edge-driven pending bit is the simplification.  So this is not the model *)
(* inventing behaviour: it is the model being FAITHFUL where the reference  *)
(* platform is loose.                                                       *)
(*                                                                         *)
(* WHY IT IS STILL RECORDED AS A DIVERGENCE.  Because the suite's question  *)
(* is about executions, not about who is right: what QEMU did here (pending *)
(* staying 0) must be something the model ALLOWS, and under the eager       *)
(* schedule this harness runs it is not.  It is allowed under a             *)
(* non-eager one -- [VSched.settle] fires [SLatch uart_irq_id] as soon as   *)
(* it is enabled, but a hand-written [sitem] list may simply decline to     *)
(* take that step, since a device arm is never forced.  So the honest       *)
(* statement is: the two machines' EAGER behaviours differ, and the model   *)
(* has an execution matching QEMU's that this test does not exhibit.  That  *)
(* makes it incompleteness of the harness's default schedule rather than of *)
(* the model, and it is the reason this file does not ask for a change to   *)
(* DevModel.v the way PlicThresh.v does.                                    *)
(*                                                                         *)
(* WHAT IT COSTS.  A driver verified here must tolerate a spurious repeat   *)
(* interrupt after every complete of a still-asserted source.  xv6's does:  *)
(* devintr re-enters, plic_claim returns the source again, and uartintr     *)
(* finds nothing to do.  A driver that instead assumed one interrupt per    *)
(* request would be provable against QEMU's PLIC and not against this one,  *)
(* which is the safe way round.                                             *)
(*                                                                         *)
(* WHY THE UART MAKES A GOOD PROBE for a gateway question: the transmit     *)
(* interrupt stays asserted for as long as IER bit 1 is set and nothing     *)
(* acknowledges it, and the only two things that DO acknowledge it are a    *)
(* THR write and an ISR read ([DevModel.u_thri], the latch).  This program  *)
(* does neither -- it never touches offsets 0 or 2 -- so the level under    *)
(* test is held up by the program itself, which is what makes the           *)
(* gateway's behaviour visible at all.  +44/+48 check exactly that at the   *)
(* end: IER bit 1 still set, transmit FIFO still empty.  Testing the ISR    *)
(* itself belongs to a `uart` test (UartRegs.v, UartIrqTx.v).               *)
(* ---------------------------------------------------------------------- *)
