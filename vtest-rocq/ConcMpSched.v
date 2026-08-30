(* ConcMpSched.v -- the interleaving for the [conc_mp] run.

   ONE SCHEDULE, AND IT IS THE EMPTY ONE, which is not laziness: this case's
   two harts FREE-RUN against each other -- a writer looping until told to
   stop, a reader sweeping NITER iterations -- so there is no distinguished
   moment to name.  What the case is about is whether the model can produce
   r1 > r2 at ANY point in that sweep, and [cfinish]'s strict alternation is
   the schedule that gives it the most chances: the reader's two loads are
   separated by a writer instruction on every single iteration.

   THAT MAKES THE ZERO MEAN SOMETHING.  A model that reordered would be
   caught here; the model does not, because a [gstate] has ONE [gmem] and a
   store is globally visible the instant it is taken (VModelFacts'
   [model_hart_sees_the_one_memory] and [model_store_is_immediately_global]).
   So this run EXHIBITS on one image what those two lemmas say in general,
   and QEMU's captured zero is a behaviour the model has. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Require Import VTest VConc.
Local Open Scope Z_scope.

Definition schedules : list (list citem) := [[]].
