(* UserFetchPt.v -- the U-mode fetch FAULT FLAVOR over the ptree user
   table (UserPtTree.v).

   The SC-era Iris fetch composers that used to live here (the
   [gen_heap_interp]-threaded success/fault/split composers over
   [udata_own]) are RETIRED on the TSO tree: the safety tier's fetch is
   the PURE exec+goodmb route ([UserFetchCert]), consumed through
   [HartMemRun.swp_hmrun_of_exec].  What remains is the one pure
   definition the classification layer ([UserActiveClass],
   [UserFaultCert]) names. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import UserPtTree.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* the fetch instance of the access-generic fault flavor (UserPtTree §5b) *)
Definition u_fetch_fault_flavor (tfp : mword 44)
    (um : gmap (mword 27) (mword 64)) (va : mword 64) : Prop :=
  u_fault_flavor (InstructionFetch tt) tfp um va.
