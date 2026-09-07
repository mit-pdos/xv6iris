(* QEMU/CoreSmokeTest.v -- the TEST: a program on a machine, and what it is
   given.

   THE CAPTURE IS THE SOURCE.  [text] and [hart] are read out of
   CoreSmokeGen.v rather than copied, so the image a test runs and the image
   a capture recorded cannot drift apart -- and the capture file finally has
   a consumer. *)
From Stdlib Require Import List ZArith String.
From stdpp Require Import base list gmap bitvector.definitions.
Import ListNotations.
From VTest Require Import VTest VRun.
From VTest.QEMU Require Import CoreSmokeGen.
Local Open Scope Z_scope.

Module CoreSmoke <: TEST.
  Definition name       := "core_smoke"%string.
  Definition platform   := "qemu"%string.
  Definition text       : list Z := core_smoke_text.
  Definition hart       : Z := core_smoke_primary_hart.
  Definition regions    : list region := std_regions.
  Definition uart_input : list (bv 8) := [].
  Definition disk_init  : list (Z * list Z) := [].
End CoreSmoke.
