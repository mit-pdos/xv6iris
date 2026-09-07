(* QEMU/CoreSmokeRun.v -- the RUN: what QEMU produced, on every channel. *)
From Stdlib Require Import List ZArith.
From stdpp Require Import base list gmap bitvector.definitions.
Import ListNotations.
From VTest Require Import VTest VRun.
From VTest.QEMU Require Import CoreSmokeGen CoreSmokeTest.
Local Open Scope Z_scope.

Module CoreSmokeRun <: TEST_RUN CoreSmoke.
  Definition observed : list observation :=
    (fun r => Obs r core_smoke_qemu_serial core_smoke_qemu_disk)
      <$> core_smoke_qemu_results.
End CoreSmokeRun.
