(* PlicThresh.v -- the CONTEXT THRESHOLD.  It gates the notification, on both
   machines and strictly.  It does NOT gate the CLAIM in this model, and on
   the hardware it does.

   Source: tools/vtest/tests/plic_thresh.S.  Capture: PlicThreshGen.v.

   One source is enough, so this uses the cheap one: the 16550 on source 10,
   raised with NO serial input by enabling the transmit-holding-register-empty
   interrupt in IER while the FIFO is empty.  No virtqueue, so the model side
   declares only the stack and the result region.

   Section 3 classifies the divergence.  It is the one finding this area has
   produced that is not merely incompleteness. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PlicThreshGen.
Local Open Scope Z_scope.

Definition thresh_run : option mstate := run_until 50000 (start plic_thresh_text).

(* result-region offsets, mirroring tools/vtest/tests/plic_thresh.S *)
Definition thresh_agree_offs : list nat :=
  [4;   (* progress marker: 3 = ran to the end                            *)
   8;   (* pending, source 10 up                              0x400       *)
   12;  (* mip & SEIP with threshold == priority              0     masked *)
   16;  (* mip & SEIP with threshold <  priority              0x200        *)
   20;  (* mip & SEIP with threshold == priority again        0     masked *)
   40;  (* pending, at the end                                0           *)
   44]%nat. (* the threshold register read back               0           *)

Definition thresh_diverge_offs : list nat :=
  [24;  (* the claim while the source is MASKED                           *)
   28;  (* pending after that claim                                       *)
   32;  (* mip & SEIP once the threshold drops to 0                       *)
   36]%nat. (* the claim after that                                       *)

(* ---------------------------------------------------------------------- *)
(* 1. What agrees: the threshold gates the NOTIFICATION, strictly.         *)
(*                                                                         *)
(*    Priority 3 against thresholds 3, 2, 3 in that order, with the source  *)
(*    pending and enabled throughout, so the only thing moving is the       *)
(*    threshold.  [plic_eip]'s conjunct is [p_thresh p h <? p_prio p i] and *)
(*    QEMU's is [source_priority > target_priority]: both STRICT, so equal  *)
(*    is masked, and the pin follows the threshold DOWN and back UP again   *)
(*    rather than latching either way.                                      *)
(* ---------------------------------------------------------------------- *)

Definition thresh_expect : list Z :=
  (fun o => cap_word plic_thresh_qemu_result o) <$> thresh_agree_offs.

Lemma plic_thresh_agrees :
  (fun o => res_word thresh_run o) <$> thresh_agree_offs = thresh_expect.
Proof. solve_vtest thresh_expect. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. What does not: the CLAIM.  Pinned on both sides.                     *)
(* ---------------------------------------------------------------------- *)

(* the model: the masked source is handed back, and its pending bit cleared;
   after that there is nothing left, so lowering the threshold reveals
   nothing and the second claim returns 0 *)
Definition thresh_model_diverging : list Z := [10; 0; 0; 0].
(* the hardware: the claim returns 0 and the source STAYS pending, so
   lowering the threshold re-exposes it -- notification and all -- and the
   second claim gets it *)
Definition thresh_qemu_diverging  : list Z := [0; 0x400; 0x200; 10].

Lemma plic_thresh_model_diverging :
  (fun o => res_word thresh_run o) <$> thresh_diverge_offs = thresh_model_diverging.
Proof. solve_vtest thresh_model_diverging. Qed.

Lemma plic_thresh_qemu_diverging :
  (fun o => cap_word plic_thresh_qemu_result o) <$> thresh_diverge_offs
  = thresh_qemu_diverging.
Proof. solve_vtest thresh_qemu_diverging. Qed.

Lemma plic_thresh_really_diverges :
  thresh_model_diverging <> thresh_qemu_diverging.
Proof. discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The divergence, classified: a DEFECT, and the hardware's behaviour    *)
(*    has NO model execution.                                              *)
(*                                                                         *)
(* THE CAUSE, in one line.  [plic_claim] goes through [plic_best] over      *)
(* [plic_cand], and                                                        *)
(*                                                                         *)
(*   plic_cand p h i = p_pending p i && plic_enabled p h i && (0 <? p_prio) *)
(*                                                                         *)
(* never mentions [p_thresh].  The threshold appears in exactly one place   *)
(* in DevModel.v, [plic_eip], where it is ANDed on top of [plic_cand].  So  *)
(* the model's notification and the model's claim disagree with each other: *)
(* a source can be invisible to the context (no interrupt) and still be the *)
(* thing the context's claim register hands back.                          *)
(*                                                                         *)
(* WHY IT IS A DEFECT AND NOT INCOMPLETENESS.  Incompleteness is the model  *)
(* being STRICTER than the hardware -- it costs reach and cannot make a     *)
(* proof wrong.  Here the model produces a value the hardware never         *)
(* produces (a masked source id out of the claim register) and, in the same *)
(* step, clears a pending bit the hardware leaves standing.  A driver       *)
(* verified against it would be verified against a device that does not     *)
(* exist.                                                                   *)
(*                                                                         *)
(* AND IT IS THE UNSOUND DIRECTION TOO, which is the sharper statement.     *)
(* The suite's question is one-directional: is what the hardware did an     *)
(* execution the model ALLOWS?  Here the answer is NO, and not because of   *)
(* this test's schedule.  The claim is a pure function of [plic_state]      *)
(* ([plic_read]'s [Some (plic_claim p h)] is the only transition for that   *)
(* MMIO read), so there is no [sitem] list, eager or otherwise, under which *)
(* the model answers 0 to that read.  That is the same shape as the disk's  *)
(* finding 5 (DiskOrder.v): a hardware behaviour with no model transition,  *)
(* so a theorem proved against the model does not cover the machine it      *)
(* claims to.                                                               *)
(*                                                                         *)
(* IS IT LIVE?  Not in xv6 as it stands: [plicinithart] writes 0 to         *)
(* PLIC_SPRIORITY(hart), so every context runs at threshold 0 and no source *)
(* is ever masked by it.  But the KERNEL'S PLAN does not say so --          *)
(* PlicPlan.v deliberately leaves the per-hart threshold completely free   *)
(* (every 32-bit value is a legal threshold, so there is nothing to         *)
(* maintain), because [plicinithart] runs concurrently on every hart and   *)
(* the invariant has to be re-establishable from one hart's own writes.  So *)
(* the device invariant admits states in which this is exactly the          *)
(* difference between the model and the machine, and the reason nothing has *)
(* gone wrong is a fact about plic.c, not about anything that is proved.    *)
(* Any use of the threshold for what it is FOR -- masking low-priority      *)
(* sources while servicing a high-priority one, which is the entire purpose *)
(* of a per-context threshold -- lands on it immediately.                   *)
(*                                                                         *)
(* THE FIX IS THREE TOKENS, and it makes the two halves agree by            *)
(* construction rather than by hand: move the threshold conjunct out of     *)
(* [plic_eip] and into [plic_cand],                                        *)
(*                                                                         *)
(*   plic_cand p h i := p_pending p i && plic_enabled p h i                 *)
(*                      && (bv_unsigned (p_thresh p h) <? p_prio p i)       *)
(*                                                                         *)
(* -- which subsumes the [0 <? p_prio] guard, since a priority-0 source     *)
(* cannot exceed a threshold of 0 -- and let [plic_eip] be                  *)
(* [existsb (plic_cand p h) plic_srcs].  [plic_best], [plic_claim] and      *)
(* [plic_eip] then read the same predicate, which is the property that was  *)
(* missing.  What makes it a decision rather than a drive-by edit is        *)
(* DevModel.v's reverse-dependency closure, and that PlicPlan.v's           *)
(* nothing-to-maintain note should be revisited at the same time.           *)
(* ---------------------------------------------------------------------- *)
