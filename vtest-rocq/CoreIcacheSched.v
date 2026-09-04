(* CoreIcacheSched.v -- the FETCH POLICIES for the self-modifying-code case.

   One schedule per outcome a platform can show, in the order the captures
   are expected to list them.  The program stores over its own code and
   runs it; the model reads an instruction fetch at the hart's INSTRUCTION
   view or anywhere above it (RiscvLang.mnode_step, icache.md), so:

     [IFresh]  every fetch reads at the top of the log: the store is seen at
               once -- QEMU's answer (2 2 2 2);
     [IStale]  every fetch reads at the instruction view, which only the
               program's own fence.i raises -- a non-coherent I-cache's
               answer (1 1 1 2).

   Both are executions of the model.  See VIcache.v. *)
From Stdlib Require Import List ZArith.
From stdpp Require Import base list.
Import ListNotations.
Require Import VTest VIcache.
Local Open Scope Z_scope.

Definition schedules : list (list iitem) :=
  [ [IPol IFresh 4000]; [IPol IStale 4000] ].
