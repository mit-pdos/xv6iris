(* PlicThresh.v -- the CONTEXT THRESHOLD.  It gates the notification AND the
   claim, on both machines and strictly.  EVERY OBSERVATION AGREES; this file
   used to record finding 10, the one divergence this area produced that was
   not merely incompleteness.

   Source: tools/vtest/tests/plic_thresh.S.  Capture: PlicThreshGen.v.

   One source is enough, so this uses the cheap one: the 16550 on source 10,
   raised with NO serial input by enabling the transmit-holding-register-empty
   interrupt in IER while the FIFO is empty.  No virtqueue, so the model side
   declares only the stack and the result region.

   WHAT WAS WRONG.  [plic_claim] went through [plic_best] over [plic_cand],
   and

     plic_cand p h i = p_pending p i && plic_enabled p h i && (0 <? p_prio)

   never mentioned [p_thresh]: the threshold appeared in exactly one place in
   DevModel.v, [plic_eip], ANDed on top of [plic_cand].  So the model's
   notification and its claim disagreed with each other -- a source could be
   invisible to a context (no interrupt) and still be the thing that
   context's claim register handed back, with its pending bit cleared on the
   way out.  That is a value the hardware never produces, and the hardware's
   behaviour (return 0, leave it pending) had NO model execution, so it was
   the unsound direction too.

   THE FIX put the threshold where the rest of the context's view already
   was: [plic_cand] carries it, [plic_eip] is now [existsb (plic_cand p c)]
   and [plic_best] folds the same predicate, so the pin and the claim
   register cannot disagree by construction.  It also subsumed the old
   [0 <? p_prio] guard -- a priority-0 source cannot exceed a threshold of
   0 -- so the model got smaller as well as righter. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list bitvector.definitions.
Require Import VTest PlicThreshGen.
Local Open Scope Z_scope.

Definition thresh_run : option mstate := run_until 50000 (start plic_thresh_text).

(* result-region offsets, mirroring tools/vtest/tests/plic_thresh.S *)
Definition thresh_offs : list nat :=
  [4;   (* progress marker: 3 = ran to the end                            *)
   8;   (* pending, source 10 up                              0x400       *)
   12;  (* mip & SEIP with threshold == priority              0     masked *)
   16;  (* mip & SEIP with threshold <  priority              0x200        *)
   20;  (* mip & SEIP with threshold == priority again        0     masked *)
   24;  (* the claim while the source is MASKED               0           *)
   28;  (* pending after that claim -- STILL THERE            0x400       *)
   32;  (* mip & SEIP once the threshold drops to 0           0x200       *)
   36;  (* the claim after that                               10          *)
   40;  (* pending, at the end                                0           *)
   44]%nat. (* the threshold register read back               0           *)

Definition thresh_expect : list Z :=
  (fun o => cap_word plic_thresh_qemu_result o) <$> thresh_offs.

Lemma plic_thresh_agrees :
  (fun o => res_word thresh_run o) <$> thresh_offs = thresh_expect.
Proof. solve_vtest thresh_expect. Qed.

(* ---------------------------------------------------------------------- *)
(* 1. The notification, which was always right: strict, and in both         *)
(*    directions.                                                          *)
(*                                                                         *)
(*    Priority 3 against thresholds 3, 2, 3 in that order (+12/+16/+20),    *)
(*    with the source pending and enabled throughout, so the only thing     *)
(*    moving is the threshold.  Both machines compare STRICTLY, so equal is *)
(*    masked, and the pin follows the threshold DOWN and back UP again      *)
(*    rather than latching either way.                                     *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(* 2. The claim, which was not, and what the four fields now pin.           *)
(*                                                                         *)
(*    +24  the claim while masked      0    -- not the source id           *)
(*    +28  pending afterwards          0x400 -- and not cleared            *)
(*    +32  SEIP once the threshold drops     0x200                          *)
(*    +36  the claim then              10                                   *)
(*                                                                         *)
(*    The four are one statement, and it takes all four: a model that       *)
(*    merely answered 0 to the masked claim while still clearing the        *)
(*    pending bit would pass +24 and fail +28, and then fail +32 and +36    *)
(*    as well, because there would be nothing left to reveal.  What the     *)
(*    sequence says is that masking HIDES a source rather than consuming    *)
(*    it: the request survives the claim that could not see it, and the     *)
(*    context gets it as soon as the threshold lets it.                     *)
(*                                                                         *)
(*    That is also why the fix had to be made in the shared predicate       *)
(*    rather than by special-casing the claim: the same [plic_cand] decides *)
(*    +32 (through [plic_eip]) and +36 (through [plic_best]).               *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(* 3. Stated off the MODEL, not off this program: the notification and the  *)
(*    claim agree at every state, which is the property whose absence was   *)
(*    the finding.  A context's claim is nonzero exactly when that context  *)
(*    has a notification -- the two are the same [plic_cand] asked two      *)
(*    different ways ("is there one?" versus "which one?").                 *)
(* ---------------------------------------------------------------------- *)

Definition eip_agrees_claim (p : plic_state) (c : nat) : bool :=
  Bool.eqb (plic_eip p c) (negb (bv_unsigned (fst (plic_claim p c)) =? 0)).

(* the masked state this program passes through, built off the model *)
Definition thresh_masked : plic_state :=
  match plic_write plic0_state (4 * 10) (Z_to_bv 32 3) with
  | Some p =>
      match plic_write p 0x2080 (Z_to_bv 32 0x400) with
      | Some p =>
          match plic_write p 0x201000 (Z_to_bv 32 3) with
          | Some p => match plic_latch p 10 with Some p => p | None => p end
          | None => p
          end
      | None => p
      end
  | None => plic0_state
  end.

Lemma plic_thresh_eip_agrees_claim :
  (eip_agrees_claim thresh_masked (plic_sctx 0),
   eip_agrees_claim thresh_masked (plic_mctx 0),
   eip_agrees_claim plic0_state (plic_sctx 0)) = (true, true, true).
Proof. solve_vtest (true, true, true). Qed.

(* ...and the masked claim really is the identity on the PLIC: it returns 0
   and hands back a state in which the request is still pending, so the
   hardware's "the source stays pending" is the model's transition too. *)
Lemma plic_thresh_masked_claim_is_id :
  (bv_unsigned (fst (plic_claim thresh_masked (plic_sctx 0))),
   p_pending (snd (plic_claim thresh_masked (plic_sctx 0))) 10)
  = (0, true).
Proof. solve_vtest (0, true). Qed.
