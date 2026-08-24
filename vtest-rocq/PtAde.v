(* ======================================================================= *)
(* PtAde.v -- SVADE: THE OTHER HALF OF THE ARCHITECTURAL CHOICE.            *)
(*                                                                          *)
(* Source: tools/vtest/tests/pt_ade.S.  Capture: PtAdeGen.v.                *)
(* 151 instructions on the model side.                                      *)
(*                                                                          *)
(* PtAdu.v pins menvcfg.ADUE to 1 on both machines and both write the PTE   *)
(* back.  This is the same program with the bit CLEARED on both, where      *)
(* neither may write anything: an access whose leaf lacks A -- or D, for a  *)
(* store -- must raise a page fault and leave the entry alone.  The whole   *)
(* 4 KB result region agrees byte for byte.                                 *)
(*                                                                          *)
(* THE FIRST THING THIS ESTABLISHES IS THAT THE EXPERIMENT IS POSSIBLE.     *)
(* ADUE is WARL, and a machine that hardwired it to 1 would silently turn   *)
(* this test into a second copy of PtAdu.  The menvcfg readback at +8 is    *)
(* that check, and it is 0 on BOTH sides: QEMU accepts the clear.  (It is   *)
(* also the reverse direction of finding 20 -- the model's power-on 0 is    *)
(* reachable on the hardware, it is just not where the hardware starts.)    *)
(*                                                                          *)
(* xv6 never runs this way -- start() sets ADUE -- so nothing in the        *)
(* development depends on this arm.  It is here because it is the other     *)
(* half of one choice, it is cheap once the machinery exists, and a model   *)
(* that had quietly hardwired Svadu would pass PtAdu and fail here.         *)
(*                                                                          *)
(* RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):     *)
(*   +8   menvcfg read back AFTER the clear                                  *)
(*   +16  the value loaded from VA 0x40000000 (0xBAD1 = the poison, i.e.     *)
(*        it faulted and the handler skipped the instruction)                *)
(*   +24  the A = 0 leaf PTE, read back: must be UNCHANGED                   *)
(*   +32  the word at PA 0x80303008: 0, the store never landed               *)
(*   +40  the D = 0 leaf PTE, read back: must be UNCHANGED                   *)
(*   +48  how many faults were taken                                         *)
(*   +0x100  the fault records, 24 bytes each: scause, sepc, stval           *)
(* ======================================================================= *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PtAdeGen.
Local Open Scope Z_scope.

Definition res_dw (o : option mstate) (off : nat) : Z :=
  res_word o off + 4294967296 * res_word o (off + 4)%nat.
Definition cap_dw (c : list Z) (off : nat) : Z :=
  cap_word c off + 4294967296 * cap_word c (off + 4)%nat.

Definition ade_run : option mstate := run_until 400 (start_pt pt_ade_text).

Lemma pt_ade_result : result_of ade_run = pt_ade_qemu_result.
Proof. solve_vtest pt_ade_qemu_result. Qed.

Lemma pt_ade_disk : pt_ade_qemu_disk = [].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* What the agreeing values are.  The two PTE words are byte-identical to   *)
(* what the program wrote, which is the "and nothing was written back"     *)
(* half; the two fault records carry the architecturally prescribed causes *)
(* (13 = load page fault, 15 = store page fault) with stval holding the    *)
(* faulting VIRTUAL address, not the physical one and not the PTE address. *)
(* ---------------------------------------------------------------------- *)

Definition ade_fields : list Z :=
  [0;                    (* menvcfg: QEMU ACCEPTED the ADUE clear          *)
   0xBAD1;               (* the load faulted; the poison survived          *)
   0x200C0C07;           (* the A = 0 leaf, exactly as written             *)
   0;                    (* the store never landed                         *)
   0x200C0C47;           (* the D = 0 leaf, exactly as written             *)
   2;                    (* two faults                                     *)
   13; 0x40000000;       (* fault 1: load page fault at VA 0x40000000      *)
   15; 0x40001008]%Z.    (* fault 2: store page fault at VA 0x40001008     *)

Lemma pt_ade_qemu_fields :
  ((fun o => cap_dw pt_ade_qemu_result o)
     <$> [8; 16; 24; 32; 40; 48; 256; 272; 280; 296]%nat) = ade_fields.
Proof. reflexivity. Qed.

Lemma pt_ade_model_fields :
  ((fun o => res_dw ade_run o)
     <$> [8; 16; 24; 32; 40; 48; 256; 272; 280; 296]%nat) = ade_fields.
Proof. solve_vtest ade_fields. Qed.
