(* ======================================================================= *)
(* PtFault.v -- THE FAULT MATRIX: FIVE WAYS A TRANSLATION IS REFUSED.       *)
(*                                                                          *)
(* Source: tools/vtest/tests/pt_fault.S.  Capture: PtFaultGen.v.            *)
(* 205 instructions on the model side.                                      *)
(*                                                                          *)
(* The interesting half of a translation model is what it REFUSES, and a    *)
(* model that quietly omits a check passes every positive test there is.    *)
(* This one drives five refusals and one permission grant, each recorded as *)
(* scause / sepc / stval, and THE WHOLE 4 KB RESULT REGION AGREES.          *)
(*                                                                          *)
(*   1  a LOAD  of an unmapped VA                     -> scause 13          *)
(*   2  a STORE to an unmapped VA                     -> scause 15          *)
(*   3  a STORE to a read-only page (R = 1, W = 0)    -> scause 15          *)
(*   4  an S-mode LOAD of a U = 1 page, SUM = 0       -> scause 13          *)
(*   5  the SAME load with sstatus.SUM = 1            -> SUCCEEDS           *)
(*   6  an instruction FETCH of an unmapped VA        -> scause 12          *)
(*                                                                          *)
(* Case 5 is what makes case 4 mean anything: without it, a U page that    *)
(* faults is also produced by a model that cannot read a U page at all.     *)
(* Case 6 is the only one whose sepc is NOT in the text -- it is the        *)
(* unmapped VA itself, which is also why the handler cannot resume at       *)
(* sepc+4 the way the others do and resumes at a label instead.             *)
(*                                                                          *)
(* WHAT stval CARRIES is checked in every case and is not incidental: for   *)
(* the four data faults it is the faulting VIRTUAL address (including the   *)
(* byte offset within the page -- 0x40001018 and 0x40002000 are not page-   *)
(* aligned), and for the fetch it is the unmapped pc.  A model that         *)
(* reported the page-aligned VA, the physical address, or the PTE address   *)
(* would disagree here.                                                     *)
(*                                                                          *)
(* menvcfg.ADUE is SET (Svadu) so both machines are in the same A/D mode    *)
(* (finding 20), and every leaf carries A and D, so "needs an A/D update"   *)
(* is never an alternative explanation for one of these faults.             *)
(*                                                                          *)
(* RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):     *)
(*   +8   the control load from VA 0x40000000                                *)
(*   +16  the load from the unmapped VA (0xBAD1 poison)                      *)
(*   +24  PA 0x80303018 after the read-only store attempt                    *)
(*   +32  the load from the U page with SUM = 0 (0xBAD2 poison)              *)
(*   +40  the load from the U page with SUM = 1                              *)
(*   +48  how many faults were taken                                         *)
(*   +56  sstatus after SUM was set                                          *)
(*   +0x80   the M-mode backstop's record (must be all zero)                 *)
(*   +0x100  the fault records, 24 bytes each: scause, sepc, stval           *)
(* ======================================================================= *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PtFaultGen.
Local Open Scope Z_scope.

Definition res_dw (o : option mstate) (off : nat) : Z :=
  res_word o off + 4294967296 * res_word o (off + 4)%nat.
Definition cap_dw (c : list Z) (off : nat) : Z :=
  cap_word c off + 4294967296 * cap_word c (off + 4)%nat.

Definition fault_run : option mstate := run_until 400 (start_pt pt_fault_text).

Lemma pt_fault_result : result_of fault_run = pt_fault_qemu_result.
Proof. solve_vtest pt_fault_qemu_result. Qed.

Lemma pt_fault_disk : pt_fault_qemu_disk = [].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 1. THE FIVE CAUSES, in the order the program provokes them.             *)
(* ---------------------------------------------------------------------- *)

Definition fault_causes : list Z := [13; 15; 15; 13; 12].

Lemma pt_fault_qemu_causes :
  ((fun i => cap_dw pt_fault_qemu_result (256 + 24 * i)%nat)
     <$> [0; 1; 2; 3; 4]%nat) = fault_causes.
Proof. reflexivity. Qed.

Lemma pt_fault_model_causes :
  ((fun i => res_dw fault_run (256 + 24 * i)%nat)
     <$> [0; 1; 2; 3; 4]%nat) = fault_causes.
Proof. solve_vtest fault_causes. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE FIVE stval VALUES, which is where a model that reports the wrong *)
(*    address would show up.  Three of them are unaligned within the page. *)
(* ---------------------------------------------------------------------- *)

Definition fault_stvals : list Z :=
  [0x40003000;   (* load of an unmapped page                               *)
   0x40003008;   (* store to the same, at offset 8                         *)
   0x40001018;   (* store to a read-only page, at offset 0x18              *)
   0x40002000;   (* load of a U page with SUM clear                        *)
   0x40003000].  (* the FETCH: the unmapped pc itself                      *)

Lemma pt_fault_qemu_stvals :
  ((fun i => cap_dw pt_fault_qemu_result (272 + 24 * i)%nat)
     <$> [0; 1; 2; 3; 4]%nat) = fault_stvals.
Proof. reflexivity. Qed.

(* THE FIVE sepc VALUES.  The first four are addresses in the text -- the
   faulting instruction itself -- and the FIFTH is the unmapped VA, because
   the fetch fault was taken before any instruction there existed to be
   blamed.  Pinning all five is what says the trap was attributed to the
   right instruction each time. *)
Definition fault_sepcs : list Z :=
  [0x800001A0; 0x800001B4; 0x800001C4; 0x800001EC; 0x40003000].

Lemma pt_fault_qemu_sepcs :
  ((fun i => cap_dw pt_fault_qemu_result (264 + 24 * i)%nat)
     <$> [0; 1; 2; 3; 4]%nat) = fault_sepcs.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. THE PERMISSION GRANT, and the two data channels.                     *)
(*                                                                        *)
(*    +32 vs +40 is the SUM bit doing its job: the identical load of the   *)
(*    identical U = 1 page faults with SUM clear and succeeds with it set. *)
(*    +24 is the read-only store's OTHER half -- not merely that it        *)
(*    faulted, but that the target word in memory is still zero, so no     *)
(*    part of the refused store leaked through.                            *)
(* ---------------------------------------------------------------------- *)

Definition fault_values : list Z :=
  [0x11223344;    (* the control load works                                *)
   0xBAD1;        (* the unmapped load faulted                             *)
   0;             (* the read-only store did NOT land                      *)
   0xBAD2;        (* the U page with SUM = 0 faulted                       *)
   0x11223344;    (* the U page with SUM = 1 SUCCEEDED                     *)
   5;             (* exactly five faults, so nothing faulted twice         *)
   0x200040020].  (* sstatus with SUM (bit 18) set                         *)

Lemma pt_fault_qemu_values :
  ((fun o => cap_dw pt_fault_qemu_result o) <$> [8; 16; 24; 32; 40; 48; 56]%nat)
  = fault_values.
Proof. reflexivity. Qed.

Lemma pt_fault_model_values :
  ((fun o => res_dw fault_run o) <$> [8; 16; 24; 32; 40; 48; 56]%nat)
  = fault_values.
Proof. solve_vtest fault_values. Qed.

(* the M-mode backstop never fired: all five faults were DELEGATED, so
   medeleg bits 12/13/15 behave on both machines *)
Lemma pt_fault_qemu_no_mtrap :
  ((fun o => cap_dw pt_fault_qemu_result o) <$> [128; 136; 144]%nat) = [0; 0; 0].
Proof. reflexivity. Qed.
