(* ======================================================================= *)
(* PtSuper.v -- A MISALIGNED SUPERPAGE.                                     *)
(*                                                                          *)
(* Source: tools/vtest/tests/pt_super.S.  Capture: PtSuperGen.v.            *)
(* 127 instructions on the model side.                                      *)
(*                                                                          *)
(* A leaf PTE at level 1 maps 2 MB, so the low 9 bits of its PPN must be    *)
(* ZERO; a nonzero value is a MISALIGNED SUPERPAGE and the spec requires a  *)
(* page fault.  Nothing in xv6 can produce one -- mappages only ever builds *)
(* level-0 leaves -- which is precisely why a model could omit the check    *)
(* and never be caught by any kernel proof.                                 *)
(*                                                                          *)
(* THE WHOLE 4 KB RESULT REGION AGREES: both machines refuse both accesses  *)
(* through a level-1 leaf whose PPN is 0x80001 (PA 0x80001000, one 4 KB     *)
(* page above the 2 MB boundary), with scause 13 for the load and 15 for    *)
(* the store.  A CONTROL megapage at L1[2] with the properly aligned PPN    *)
(* 0x80000 is loaded first and works, so the fault cannot be blamed on      *)
(* level-1 leaves being unsupported.                                        *)
(*                                                                          *)
(* THE STORE CASE IS ALSO A HARNESS ARGUMENT.  Had the model omitted the    *)
(* check, the store through VA 0x40300340 would have been directed at       *)
(* PA 0x80001000 + 0x100340 -- outside every region the test declares --    *)
(* and the model would have gone STUCK rather than merely disagreeing.  It  *)
(* does not: the fault is taken and the run completes.                      *)
(*                                                                          *)
(* menvcfg.ADUE is SET (Svadu) on both machines and both leaves carry A and *)
(* D, so an A/D update is not an alternative explanation for the fault.     *)
(*                                                                          *)
(* RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):     *)
(*   +8   the control load through the ALIGNED megapage                      *)
(*   +16  the load through the MISALIGNED megapage (0xBAD1 poison)           *)
(*   +24  PA 0x80100340 after a store through the misaligned megapage        *)
(*   +32  how many faults were taken                                         *)
(*   +0x100  the fault records, 24 bytes each: scause, sepc, stval           *)
(* ======================================================================= *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PtSuperGen.
Local Open Scope Z_scope.

Definition res_dw (o : option mstate) (off : nat) : Z :=
  res_word o off + 4294967296 * res_word o (off + 4)%nat.
Definition cap_dw (c : list Z) (off : nat) : Z :=
  cap_word c off + 4294967296 * cap_word c (off + 4)%nat.

Definition super_run : option mstate := run_until 400 (start_pt pt_super_text).

Lemma pt_super_result : result_of super_run = pt_super_qemu_result.
Proof. solve_vtest pt_super_qemu_result. Qed.

Lemma pt_super_disk : pt_super_qemu_disk = [].
Proof. reflexivity. Qed.

Definition super_fields : list Z :=
  [0xF14022F3;   (* the ALIGNED megapage works: the image's first word     *)
   0xBAD1;       (* the MISALIGNED one faulted on a load                   *)
   0;            (* ...and on a store, which therefore did not land        *)
   2;            (* exactly two faults                                     *)
   13; 0x40200000;   (* load page fault at the misaligned megapage's VA    *)
   15; 0x40300340].  (* store page fault 1 MB into the same megapage       *)

Lemma pt_super_qemu_fields :
  ((fun o => cap_dw pt_super_qemu_result o)
     <$> [8; 16; 24; 32; 256; 272; 280; 296]%nat) = super_fields.
Proof. reflexivity. Qed.

Lemma pt_super_model_fields :
  ((fun o => res_dw super_run o)
     <$> [8; 16; 24; 32; 256; 272; 280; 296]%nat) = super_fields.
Proof. solve_vtest super_fields. Qed.
