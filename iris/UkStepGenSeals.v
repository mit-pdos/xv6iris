(* ===================================================================== *)
(* UkStepGenSeals.v -- THE PILOT'S WALKS, OVER DISCHARGED SEALS.          *)
(*                                                                        *)
(* A LEAF, and the last line of ask (4)'s compiled receipt.  Stage P2 and  *)
(* stage P5 left the fd-row pilot standing on two [Module Type]s --        *)
(* [UkRunSysFs.FDROW_UKFS_STEP] (the enriched ecall machine step) and      *)
(* [UkRunFsLeaf.FDROW_UKFS_RETIRE] (the enriched retire funnel) -- and the *)
(* walks above them ([FdRowPilot.FdRowPilotWalk], [UkInitFs.UkInitFsWalk]) *)
(* were FUNCTORS with nothing to apply them to.  UkStepGenFs.v discharges  *)
(* both seals from the X-generic engine; this file applies the walks at    *)
(* the discharged modules, so the pilot's theorems and init's enriched     *)
(* console walk are unconditional constants.                               *)
(*                                                                        *)
(* The audit that matters is [Print Assumptions PilotW.wp_pilot_open2]:    *)
(* the two platform axioms ([resv_matches], [resv_is_valid]) and           *)
(* [functional_extensionality_dep], and nothing else -- no [Parameter]     *)
(* stand-in survives under the pilot.                                     *)
(* ===================================================================== *)
Require Import FdRowPilot.
Require Import UkInitFs.
Require Import UkStepGenFs.

(* the enriched ecall leaf's seal, discharged -- the pilot's row theorems *)
Module PilotW := FdRowPilotWalk FdRowUkfsEngineGen.

(* ...and both seals at once -- init's console preamble on the enriched
   tier, with no assumed module anywhere below it *)
Module InitW := UkInitFsWalk FdRowUkfsRetireGen FdRowUkfsStepGen.
