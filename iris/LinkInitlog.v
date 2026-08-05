(* LinkInitlog.v -- instantiates the Initlog proof against its callees'
   proofs (initlock / bread / brelse / install_trans / write_head).  Sealed,
   so this is the only place the six ever meet.

   bwrite and memmove are NOT among them: initlog never calls them directly
   (write_head's bwrite and install_trans's memmove are sealed inside those
   two functions' own Link files). *)
Require Import LinkInitlock LinkBread LinkBrelse LinkInstallTrans LinkWriteHead
        ProofInitlog.

Module Initlog := InitlogProof Initlock Bread Brelse InstallTrans WriteHead.
