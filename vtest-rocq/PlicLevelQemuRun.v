(* PlicLevelQemuRun.v -- HAND-WRITTEN.  The generator leaves this alone
   (tools/vtest/vtest.py, [hand_written]); it is not derived from any
   builder, because no builder computes what this run needs.

   ======================================================================
   WHY THIS ONE IS BY HAND
   ======================================================================

   Every other run's [outcome] is "step the model until it publishes".  This
   case's is "step the model until it publishes, ALONG A PARTICULAR DEVICE
   SCHEDULE", and that difference is the whole content of the run.

   THE DIVERGENCE, and who is right.  [plic_level] phase 2 completes at the
   PLIC while the source level is still asserted.  The model's gateway
   re-forwards the still-high level the instant [plic_complete] clears the
   claimed bit, so one device request yields a SECOND interrupt; QEMU's
   pending bit comes off the RISING EDGE only, so it stays down.  The three
   result words where they differ -- R_PENDC (+32), R_MIPC (+36), R_CLAIM2
   (+40) -- are named and predicted in tools/vtest/tests/plic_level.S itself.

   THE MODEL IS THE ONE THAT IS RIGHT.  A level gateway that re-forwards is
   the spec-faithful behaviour; it is exactly why a driver acknowledges the
   DEVICE before it completes at the PLIC.  Nothing here is a model defect
   and no model change is wanted.

   SO WHY DID THE RUN FAIL?  Because [VSched.settle] is HARNESS machinery,
   not the model's transition relation.  A device step is an OPTIONAL
   transition -- the relation permits taking it or not at any moment -- and
   [settle] takes every enabled arm.  That is the right default for every
   other test, but it means the harness could not reach an execution the
   model HAS: the one that does not take [SLatch] again after the complete.
   The run therefore reported a mismatch where what it really showed was a
   gap in the harness.  Recorded in tools/vtest/README.md ("One divergence
   where the MODEL is right") as needing "a run_until variant parameterised
   by the device policy"; this is that variant.

   ======================================================================
   THE SCHEDULE, and why it is a CREDIT rather than a step count
   ======================================================================

   The obvious encoding -- "eager settling for the first K instructions,
   gateway-free thereafter" -- would work and would be a lie: K is a magic
   number tied to the exact instruction sequence, it says nothing about the
   DEVICE, and it silently stops meaning anything the moment the .S changes.

   What the execution actually is: THE GATEWAY FORWARDS ONCE.  That is what
   an edge-triggered gateway does with a level that rises once, and it is
   stated without reference to the program at all.  [latch_credit] = 1.

   One forward is also demonstrably enough for everything phase 1 checks:
   the first forward sets pending (R_PEND0), [plic_latch] is itself guarded
   so the level dropping does not clear it (R_PENDD is sticky) and the level
   rising again cannot re-forward while it is still pending (R_PENDR).  Only
   the post-complete forward is denied, which is precisely the one QEMU does
   not make.

   THE CREDIT IS SPENT ONLY WHEN A GATEWAY ARM ACTUALLY FIRES, and that is
   what [settle1_credit] below is for: it offers the round WITHOUT the
   gateway first, and only when nothing else is enabled does it spend a
   credit to let the gateway go.  So the count is a count of FORWARDS, not
   of settle rounds, and the other arms -- the UART, the disk, the wire --
   run exactly as they always do. *)
From Stdlib Require Import List ZArith String.
Import ListNotations.
Require Import VTest VSched VRun PlicLevelGen.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The device schedule: settle as usual, but the gateway forwards at most   *)
(* [k] times over the whole run.                                           *)
(* ---------------------------------------------------------------------- *)

Definition settle1_credit (k : nat) (s : mstate) : option (mstate * nat) :=
  match settle1_gated lowest_head false s with
  | Some s' => Some (s', k)          (* some non-gateway arm was enabled *)
  | None =>
      match k with
      | 0%nat => None                (* out of credit: settle is finished *)
      | S k' =>
          (* nothing but a gateway arm can be enabled, so if this fires it
             IS the gateway, and the credit is spent. *)
          match settle1_gated lowest_head true s with
          | Some s' => Some (s', k')
          | None => None
          end
      end
  end.

Fixpoint settle_credit (fuel : nat) (s : mstate) (k : nat) : mstate * nat :=
  match fuel with
  | 0%nat => (s, k)
  | S f => match settle1_credit k s with
           | Some (s', k') => settle_credit f s' k'
           | None => (s, k)
           end
  end.

(* [VRun.eval_run], with the device schedule threaded through. *)
Fixpoint eval_run_credit (n : nat) (s : mstate) (k : nat) : eresult :=
  if flag_set s then RDone s else
  match n with
  | 0%nat => RBudget
  | S n' => match exec_r (riscv_step false) s with
            | inl (_, s') => let '(s2, k2) := settle_credit dev_fuel s' k in
                             eval_run_credit n' s2 k2
            | inr e => RStuck e
            end
  end.

(* ---------------------------------------------------------------------- *)
(* The run itself, which is a [VRun.TEST_RUN] like every other.            *)
(* ---------------------------------------------------------------------- *)

Definition latch_credit : nat := 1.
Definition budget : nat := 4000.

Definition start : mstate :=
  start_hart_with 0 plic_level_text std_regions.

Module PlicLevelQemu <: TEST_RUN.
  Definition case     := "plic_level"%string.
  Definition platform := "qemu"%string.
  Definition observed : list (list Z) := [plic_level_qemu_result].
  Definition outcome : model_outcome :=
    match eval_run_credit budget start latch_credit with
    | RDone s => MDone [peek_mem (mem s) result_base result_size]
    | RStuck e => outcome_of_stuck e
    | RBudget => MBudget
    end.
End PlicLevelQemu.
