(* LinkVirtioDiskRw.v -- instantiates virtio_disk_rw's proof against its five
   callees' proofs (acquire / release / sleep_prepare / sleep / free_desc).  Sealed, so this
   is the only place the whole-function proofs ever meet. *)
Require Import LinkAcquire LinkRelease LinkSleepPrepare LinkSleep LinkFreeDesc ProofVirtioDiskRwF.

Module VirtioDiskRw := VirtioDiskRwProof Acquire Release SleepPrepare Sleep FreeDesc.
