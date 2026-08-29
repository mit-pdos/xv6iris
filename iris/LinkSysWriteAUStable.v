(* LinkSysWriteAUStable.v -- the stable corollary, instantiated.  One line
   over [LinkSysWriteAU]: [SYSWRITE_AU_ERA_STABLE] is a DERIVATION from the
   AU form plus the agreement seed, never a second walk. *)
Require Import LinkSysWriteAU ProofSysWriteAUStable.

Module SysWriteStable := SysWriteAUStable SysWriteAU.
