(* ====================================================================== *)
(* VRunConc.v -- the MULTI-HART builder for [VRun.TEST_RUN].               *)
(*                                                                         *)
(* [VRun.SingleHart] computes a run's outcome from one hart stepping with   *)
(* [run_until].  A case that RACES two harts cannot use it: the model side  *)
(* has to name an INTERLEAVING, because a race has several outcomes and the *)
(* suite's question is whether the model has one for each.  Run such a case *)
(* through the single-hart builder and the second hart never executes at    *)
(* all -- measured, and it made six cases look like findings when they were *)
(* an arithmetic error in the harness.                                     *)
(*                                                                         *)
(* [VConc] already has the machinery: [citem] schedules, [cobs_all] to      *)
(* exhibit one observation per schedule.  So this is a thin adapter, and    *)
(* that is the point -- a builder is only a different way to COMPUTE        *)
(* [outcome], and [TEST_RUN] is unchanged.                                  *)
(*                                                                         *)
(* THE SCHEDULES ARE THE CASE'S OWN KNOWLEDGE and cannot be generated: an   *)
(* interleaving that reproduces a particular observed outcome is the thing  *)
(* a human works out.  So a multi-hart case has a hand-written             *)
(* <Case>Sched.v supplying them, and everything else about the run is       *)
(* generated as usual.                                                     *)
(*                                                                         *)
(* WHAT THIS BUILDER CANNOT SAY.  [VConc] steps with [exec], not [exec_r],  *)
(* so a schedule that fails to step yields no observation and the run reads *)
(* as a mismatch.  It cannot distinguish [MNoStep] from [MUnknown], and so  *)
(* never reports the stuck-is-a-pass case.  For a race that is the right    *)
(* default -- a stuck race is not evidence of anything -- but it is a       *)
(* difference from [SingleHart] worth knowing.                             *)
(* ====================================================================== *)
From Stdlib Require Import List ZArith String.
From stdpp Require Import base list.
Import ListNotations.
Require Import VTest VConc VRun.
Local Open Scope Z_scope.

Module Type CONC_CASE.
  Parameter case      : string.
  Parameter platform  : string.
  Parameter text      : list Z.
  Parameter regions   : list region.
  (* the budget [cfinish] gets after the named interleaving has run *)
  Parameter budget    : nat.
  (* ONE SCHEDULE PER OBSERVED OUTCOME, in the order the capture lists
     them.  This is the hand-written part. *)
  Parameter schedules : list (list citem).
  Parameter proj      : list Z -> list Z.
  Parameter observed_raw : list (list Z).
End CONC_CASE.

Module ConcRun (P : CONC_CASE) <: TEST_RUN.
  Definition case := P.case.
  Definition platform := P.platform.
  Definition observed : list (list Z) := map P.proj P.observed_raw.
  Definition start : gstate := g0_of P.text P.regions.
  (* every observation the named schedules exhibit *)
  Definition outcome : model_outcome :=
    MDone (map P.proj (cobs_all P.budget P.schedules start)).
End ConcRun.
