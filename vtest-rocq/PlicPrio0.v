(* PlicPrio0.v -- source 0's priority register, the init loop a driver
   actually writes, and the sources past the thirty-second.  EVERY
   OBSERVATION AGREES; this file used to record finding 12, which was a STUCK
   machine on both counts.

   Source: tools/vtest/tests/plic_prio0.S.  Capture: PlicPrio0Gen.v.

   [DevModel.plic_read]/[plic_write] used to gate the priority window on

     (0 <? off) && (off <? 4 * plic_nsrc) && (off mod 4 =? 0)

   and BOTH bounds cut off registers the hardware has.

   The lower one had a driver behind it.  Offset 0 is source 0's priority
   register; source 0 does not exist, so the register is hardwired to zero --
   readable, and writes dropped.  With no transition for it at all,

       for (i = 0; i < NSRC; i++) plic_priority[i] = 0;

   -- the loop a driver writes to mask everything before enabling what it
   wants -- was a stuck machine on its FIRST iteration.  [plic_prio_src] now
   admits offset 0 and [plic_read]/[plic_write] answer for it the way the
   hardware does.

   The upper one was [plic_nsrc] = 32 against the board's 96.  The model now
   has all ninety-six sources, so source 32's register (offset 128) is a
   register here too -- and the enable and pending bitmaps are three words
   each, which is what carries the other sixty-four. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list bitvector.definitions.
Require Import VTest PlicPrio0Gen.
Local Open Scope Z_scope.

Definition prio0_run : option mstate := run_until 50000 (start plic_prio0_text).

(* result-region offsets, mirroring tools/vtest/tests/plic_prio0.S *)
Definition prio0_offs : list nat :=
  [4;   (* progress marker: 2 = the whole program ran *)
   8;   (* source 1's priority, read back            7 *)
   12;  (* source 0's priority after a store of 0    0 *)
   16;  (* ...and after a store of 5                 0  -- read-only zero *)
   20]%nat. (* source 32's priority after a store of 4   4  -- a real register *)

Definition prio0_expect :=
  (fun o => cap_word plic_prio0_qemu_result o) <$> prio0_offs.

Lemma plic_prio0_agrees :
  (fun o => res_word prio0_run o) <$> prio0_offs = prio0_expect.
Proof. solve_vtest prio0_expect. Qed.

(* ---------------------------------------------------------------------- *)
(* What each field rules out.                                              *)
(*                                                                         *)
(*  - +8 is the ordinary case, and it is here so that the two interesting   *)
(*    fields cannot pass vacuously: a model that answered 0 to every        *)
(*    priority read would fail it.                                         *)
(*                                                                         *)
(*  - +12 versus +16 is what "hardwired zero" means, and it takes both      *)
(*    fields to say it: the register READS (a model that got stuck, or      *)
(*    refused the write, fails) and the value read is zero WHATEVER was     *)
(*    written (a model that stored the 5 fails +16).  Source 0 does not     *)
(*    exist, so there is nothing for a priority to be about.               *)
(*                                                                         *)
(*  - +20 is source 32, which needs [plic_nsrc] = 96 to exist at all, and   *)
(*    which is in the second word of every bitmap -- so it is also the      *)
(*    field that would fail if the model had grown the source count while   *)
(*    leaving the enable and pending words single.                         *)
(* ---------------------------------------------------------------------- *)

(* ...and the model's own statement of the two bounds, off the decode rather
   than off this program: offset 0 is a register, so is source 95's, and
   source 96's is not.  (The upper bound has to stop somewhere, and where it
   stops is what [plic_nsrc] says.) *)
Definition prio0_decode : list Z :=
  [match plic_read plic0_state 0 with
   | Some (w, _) => bv_unsigned w | None => -1 end;
   match plic_read plic0_state (4 * 95) with
   | Some (w, _) => bv_unsigned w | None => -1 end;
   match plic_read plic0_state (4 * 96) with
   | Some (w, _) => bv_unsigned w | None => -1 end].

Lemma plic_prio0_bounds : prio0_decode = [0; 0; -1].
Proof. solve_vtest ([0; 0; -1] : list Z). Qed.
