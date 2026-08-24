(* ======================================================================= *)
(* PtLevels.v -- THE WALK ACTUALLY DESCENDS: THREE LEVELS, AND A MEGAPAGE.  *)
(*                                                                          *)
(* Source: tools/vtest/tests/pt_levels.S.  Capture: PtLevelsGen.v.          *)
(* 130 instructions on the model side.                                      *)
(*                                                                          *)
(* PtIdent uses a single level-2 leaf, so its walk terminates at the ROOT   *)
(* and nothing below the first slot is ever read.  This test puts all three *)
(* Sv39 leaf levels in ONE table and uses two of them:                      *)
(*                                                                          *)
(*   L1[0] -> an L0 page whose slot 5 is a 4 KB leaf                        *)
(*            VA 0x40005000 -> PA 0x80303000     (level 0: three PTE reads) *)
(*   L1[1] is itself a LEAF -- a 2 MB megapage                              *)
(*            VA 0x40200000 -> PA 0x80000000     (level 1: two PTE reads)   *)
(*                                                                          *)
(* THE WHOLE 4 KB RESULT REGION AGREES.                                     *)
(*                                                                          *)
(* THE MEGAPAGE IS THE OFFSET TEST, and it is why the test is not just      *)
(* "a deeper walk works".  A level-1 leaf takes TWENTY-ONE bits of offset   *)
(* from the VA, not twelve, so the second store goes through VA 0x40300300  *)
(* -- one megabyte into the same megapage -- and must land at PA            *)
(* 0x80100300, which is inside the RESULT region and therefore readable     *)
(* back through the identity gigapage.  A model that took only 12 offset    *)
(* bits would put VA 0x40200000 and VA 0x40300300 in the same 4 KB page and *)
(* the two observations would collide.  They do not: +24 reads the image's  *)
(* first word and +32 reads the value stored a megabyte away.               *)
(*                                                                          *)
(* menvcfg.ADUE is SET (Svadu) so both machines are in the same A/D mode    *)
(* (finding 20); every leaf carries A and D, so no write-back fires.        *)
(*                                                                          *)
(* RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):     *)
(*   +8   the load from the 4 KB leaf VA 0x40005000                          *)
(*   +16  PA 0x80303010 after storing 0xDEC0DE through VA 0x40005010         *)
(*   +24  the load from the megapage VA 0x40200000                           *)
(*   +32  PA 0x80100300 after storing 0xC0FFEE through VA 0x40300300         *)
(*   +40  how many faults were taken                                         *)
(*   +0x300 is where that second store landed, so it is checked twice: once  *)
(*        by the explicit readback at +32 and once by the whole-region       *)
(*        comparison                                                         *)
(* ======================================================================= *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PtLevelsGen.
Local Open Scope Z_scope.

Definition res_dw (o : option mstate) (off : nat) : Z :=
  res_word o off + 4294967296 * res_word o (off + 4)%nat.
Definition cap_dw (c : list Z) (off : nat) : Z :=
  cap_word c off + 4294967296 * cap_word c (off + 4)%nat.

Definition levels_run : option mstate := run_until 400 (start_pt pt_levels_text).

Lemma pt_levels_result : result_of levels_run = pt_levels_qemu_result.
Proof. solve_vtest pt_levels_qemu_result. Qed.

Lemma pt_levels_disk : pt_levels_qemu_disk = [].
Proof. reflexivity. Qed.

Definition levels_fields : list Z :=
  [0x11223344;   (* three-level walk: the 4 KB leaf reads the right page   *)
   0xDEC0DE;     (* ...and a store through it lands at PA 0x80303010       *)
   0xF14022F3;   (* the megapage maps VA 0x40200000 to the image's start   *)
   0xC0FFEE;     (* ...and 1 MB further in lands at PA 0x80100300, so the
                    level-1 leaf really takes 21 offset bits              *)
   0;            (* no faults                                              *)
   0xC0FFEE].    (* the same store seen at +0x300 of the result region     *)

Lemma pt_levels_qemu_fields :
  ((fun o => cap_dw pt_levels_qemu_result o) <$> [8; 16; 24; 32; 40; 768]%nat)
  = levels_fields.
Proof. reflexivity. Qed.

Lemma pt_levels_model_fields :
  ((fun o => res_dw levels_run o) <$> [8; 16; 24; 32; 40; 768]%nat)
  = levels_fields.
Proof. solve_vtest levels_fields. Qed.
