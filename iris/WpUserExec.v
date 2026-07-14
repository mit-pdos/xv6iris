(* WpUserExec.v -- compatibility shim: the monolithic user-execution file
   was split into WpUserBase (frames/engines) + per-family arm files +
   WpUserSteps (classification & the end-to-end theorem).               *)
Require Export WpUserBase.
Require Export WpUserFetch WpUserCompute WpUserCtrl WpUserComputeC WpUserTrap WpUserMem.
Require Export WpUserSteps.
(* the spatial-composed step obligation: the frame-consuming memory
   dispatchers (WpUserMemStep) + user_step_holds_full (WpUserFull) *)
Require Export WpUserMemStep WpUserFull.
