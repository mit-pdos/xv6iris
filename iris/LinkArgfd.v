(* LinkArgfd.v -- the one place argfd's proof meets argint's and myproc's.

   This became writable when argraw stopped being parked: [LinkArgint.v]
   discharges ARGINT, [LinkMyproc.v] MYPROC, and argfd needs nothing else. *)
Require Import LinkArgint LinkMyproc ProofArgfd.

Module Argfd := ArgfdProof Argint Myproc.
