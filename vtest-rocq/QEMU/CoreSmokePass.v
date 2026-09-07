(* QEMU/CoreSmokePass.v -- the proof. *)
From Stdlib Require Import List ZArith.
From stdpp Require Import base list.
Import ListNotations.
From VTest Require Import VTest VRun VExecStep.
From VTest.QEMU Require Import CoreSmokeTest CoreSmokeRun.

Module CoreSmokePass <: TEST_PASSES CoreSmoke CoreSmokeRun.
  Lemma passes :
    run_passes CoreSmoke.hart CoreSmoke.text CoreSmoke.regions
               CoreSmoke.uart_input CoreSmoke.disk_init CoreSmokeRun.observed.
  Proof.
    left. intros o Ho. cbn [CoreSmokeRun.observed] in Ho.
    destruct Ho as [<-|Ho]; [|destruct Ho].
    apply (run_shows false lowest_head 2000).
    vm_compute. repeat split.
  Qed.
End CoreSmokePass.
