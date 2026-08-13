(* LinkCopyinstr.v -- instantiates the Copyinstr proof against its callees'
   proofs.  Sealed, so this is the only place the three meet.

   IT USED TO BE THE SMALLEST LINK IN THE COPY FAMILY, because walkaddr was
   copyinstr's only callee: an unmapped page was simply [-1], so there was no
   vmfault and no kalloc tier beneath it.  xv6 `4f2fc8b` gave copyinstr's
   [pa0 == 0] arm a real [vmfault(pagetable, psz, va0, 1)] call, which lifts
   it to copyin's altitude (SpecCopyinstr.v) -- so the functor takes vmfault
   too, and copyinstr's axiom footprint now inherits vmfault's. *)
Require Import LinkWalkaddr LinkVmfault.
Require Import ProofCopyinstr.

Module Copyinstr := CopyinstrProof Walkaddr Vmfault.
