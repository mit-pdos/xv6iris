(* WpUserExec.v -- compatibility shim: the monolithic user-execution file
   was split into WpUserBase (frames/engines) + per-family arm files +
   WpUserSteps (classification & the end-to-end theorem).               *)
Require Export WpUserBase.
Require Export WpUserFetch WpUserCompute WpUserCtrl WpUserComputeC WpUserTrap WpUserMem.
Require Export WpUserSteps.
