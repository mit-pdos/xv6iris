(* ======================================================================= *)
(* PtResv.v -- THE RESERVED LEAF ENCODING R = 0, W = 1.                     *)
(*                                                                          *)
(* Source: tools/vtest/tests/pt_resv.S.  Capture: PtResvGen.v.              *)
(* 139 instructions on the model side.                                      *)
(*                                                                          *)
(* A PTE with W set and R clear is RESERVED by the privileged spec: it is   *)
(* not a pointer to the next level (a pointer is R = W = X = 0), it is not  *)
(* a write-only page, and it must raise a page fault.  Omitting the check   *)
(* costs a model nothing until software gets a bit wrong, which is exactly  *)
(* why it earns its own image.                                              *)
(*                                                                          *)
(* THE WHOLE 4 KB RESULT REGION AGREES: both machines refuse both accesses  *)
(* through the reserved leaf, with scause 13 for the load and 15 for the    *)
(* store, and nothing is written.  A CONTROL leaf at VA 0x40001000, built   *)
(* from the same PPN with R added, is loaded first and works -- so the      *)
(* fault at the reserved leaf cannot be blamed on the table, the walk       *)
(* depth, or the page being unreachable.                                    *)
(*                                                                          *)
(* The reserved leaf carries A and D, and menvcfg.ADUE is SET (Svadu) on    *)
(* both machines, so "the walk wanted an A/D update" is ruled out as an     *)
(* alternative explanation for the fault.                                   *)
(*                                                                          *)
(* RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):     *)
(*   +8   the control load through the well-formed leaf                      *)
(*   +16  the load through the reserved leaf (0xBAD1 poison)                 *)
(*   +24  PA 0x80303020 after a store through the reserved leaf              *)
(*   +32  how many faults were taken                                         *)
(*   +0x100  the fault records, 24 bytes each: scause, sepc, stval           *)
(* ======================================================================= *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PtResvGen.
Local Open Scope Z_scope.

Definition res_dw (o : option mstate) (off : nat) : Z :=
  res_word o off + 4294967296 * res_word o (off + 4)%nat.
Definition cap_dw (c : list Z) (off : nat) : Z :=
  cap_word c off + 4294967296 * cap_word c (off + 4)%nat.

Definition resv_run : option mstate := run_until 400 (start_pt pt_resv_text).

Lemma pt_resv_result : result_of resv_run = pt_resv_qemu_result.
Proof. solve_vtest pt_resv_qemu_result. Qed.

Lemma pt_resv_disk : pt_resv_qemu_disk = [].
Proof. reflexivity. Qed.

Definition resv_fields : list Z :=
  [0x11223344;   (* the CONTROL leaf, same PPN plus R: the page is fine    *)
   0xBAD1;       (* the load through R=0,W=1 FAULTED                       *)
   0;            (* the store through it did not land                      *)
   2;            (* exactly two faults                                     *)
   13; 0x40000000;   (* load page fault at the reserved leaf's VA          *)
   15; 0x40000020].  (* store page fault, stval keeping the byte offset    *)

Lemma pt_resv_qemu_fields :
  ((fun o => cap_dw pt_resv_qemu_result o)
     <$> [8; 16; 24; 32; 256; 272; 280; 296]%nat) = resv_fields.
Proof. reflexivity. Qed.

Lemma pt_resv_model_fields :
  ((fun o => res_dw resv_run o)
     <$> [8; 16; 24; 32; 256; 272; 280; 296]%nat) = resv_fields.
Proof. solve_vtest resv_fields. Qed.
