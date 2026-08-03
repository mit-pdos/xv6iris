(* LinkVirtioDiskRw.v -- instantiates virtio_disk_rw's proof against its four
   callees' proofs (acquire / release / sleep / free_desc).  Sealed, so this
   is the only place the whole-function proofs ever meet. *)
Require Import LinkAcquire LinkRelease LinkSleep LinkFreeDesc ProofVirtioDiskRwF.

Module VirtioDiskRw := VirtioDiskRwProof Acquire Release Sleep FreeDesc.
