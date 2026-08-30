(* ConcSmokeSched.v -- the interleaving for the [conc_smoke] run.

   Hand-written, as every multi-hart case's is: which schedule reproduces
   which observed outcome is the one thing about a race that cannot be
   generated.  This case is the DEGENERATE one -- the second hart only spins
   and never touches the result region, so the empty schedule (let [cfinish]
   drive both harts to quiescence) already exhibits what QEMU produced.  It
   is here so that conc_smoke goes through the same builder as the races
   that do need a real interleaving, rather than being a special case. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Require Import VTest VConc.
Local Open Scope Z_scope.

Definition schedules : list (list citem) := [[]].
