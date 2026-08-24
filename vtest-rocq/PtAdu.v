(* ======================================================================= *)
(* PtAdu.v -- SVADU: THE MODEL EXECUTES THE A/D WRITE-BACK, AND IT WRITES   *)
(* WHAT THE HARDWARE WRITES.                                                *)
(*                                                                          *)
(* Source: tools/vtest/tests/pt_adu.S.  Capture: PtAduGen.v.                *)
(* 129 instructions on the model side.                                      *)
(*                                                                          *)
(* PtAd.v runs the DEFAULT configuration, where the model is Svade and QEMU *)
(* is Svadu (finding 20) and every observation therefore diverges.  This    *)
(* test removes that difference: menvcfg bit 61 is SET explicitly in M-mode *)
(* before satp, so BOTH machines are Svadu and both are required to write   *)
(* the PTE back.  The whole 4 KB result region then agrees byte for byte.   *)
(*                                                                          *)
(* WHAT THIS EXERCISES ON THE MODEL SIDE.  sail-riscv's only local delta    *)
(* from upstream is this write-back, and it is the LR/SC-shaped path:       *)
(*                                                                          *)
(*   update_and_write_pte  (rv64d.v:24949, reached from BOTH               *)
(*   translate_TLB_hit and translate_TLB_miss)                              *)
(*     update_PTE_Bits pte = Some _        -- the access needs A and/or D   *)
(*     Svadu && menvcfg.ADUE = 1           -- the gate this test opens      *)
(*     read_pte_exclusive                  -- an EXCLUSIVE re-read          *)
(*     check_leaf_pte on the RE-READ word  -- the checks run again          *)
(*     update_PTE_Bits (re-read)                                            *)
(*     write_pte_conditional               -- a CONDITIONAL store           *)
(*     Ok false -> internal_error          -- stuck, by the model's choice  *)
(*                                                                          *)
(* [conc_amo] (finding 25) found that a single [sc.w] does not return from  *)
(* [vm_compute] at all, so it was a live question whether this path could   *)
(* be EXECUTED by the harness even though it is proven.  IT CAN: the two    *)
(* write-backs here evaluate in the ordinary way, no differently from any   *)
(* other store.  The reason is that they are not the same machinery --      *)
(* [execute_STORECON] goes through the opaque platform axioms              *)
(* [match_reservation]/[cancel_reservation], which [exec] cannot step, while*)
(* [write_pte_conditional] is [mem_write_value_priv ... con = true], an     *)
(* ordinary [Interface.MemWrite] outcome whose [Ok] result [exec] supplies. *)
(* So the conditional write always SUCCEEDS under [exec]; the              *)
(* [internal_error] arm is unreachable here, and this test does not probe   *)
(* it.                                                                      *)
(*                                                                          *)
(* THE OBSERVATION THAT MATTERS is not that the accesses succeeded -- a     *)
(* machine that ignored A and D entirely would also succeed -- but that the *)
(* LEAF PTE IN MEMORY CHANGED, and changed to the same word on both sides.  *)
(*                                                                          *)
(* RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):     *)
(*   +8   menvcfg read back AFTER the write -- did bit 61 stick?             *)
(*   +16  the value loaded from VA 0x40000000 (the A = 0 leaf)               *)
(*   +24  the A = 0 leaf PTE, read back out of the page-table page           *)
(*   +32  the word at PA 0x80303008 after a store through VA 0x40001008      *)
(*   +40  the D = 0 leaf PTE, read back out of the page-table page           *)
(*   +48  how many faults were taken                                         *)
(*   +0x100  the fault records, 24 bytes each: scause, sepc, stval           *)
(* ======================================================================= *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PtAduGen.
Local Open Scope Z_scope.

Definition res_dw (o : option mstate) (off : nat) : Z :=
  res_word o off + 4294967296 * res_word o (off + 4)%nat.
Definition cap_dw (c : list Z) (off : nat) : Z :=
  cap_word c off + 4294967296 * cap_word c (off + 4)%nat.

Definition adu_run : option mstate := run_until 400 (start_pt pt_adu_text).

(* ---------------------------------------------------------------------- *)
(* 1. The whole result region, nothing trimmed.                            *)
(* ---------------------------------------------------------------------- *)

Lemma pt_adu_result : result_of adu_run = pt_adu_qemu_result.
Proof. solve_vtest pt_adu_qemu_result. Qed.

Lemma pt_adu_disk : pt_adu_qemu_disk = [].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. What the agreeing values ARE -- read off the capture, so free.       *)
(*                                                                        *)
(*    The two PTE words are the point.  The A = 0 leaf was written with    *)
(*    flag byte 0x07 (R|W|V) and reads back 0x47: the walker set A.  The   *)
(*    other leaf was written 0x47 (A|R|W|V) and reads back 0xC7: the store *)
(*    made the walker set D.  The upper 54 bits -- the PPN and the         *)
(*    reserved/PBMT field -- are IDENTICAL in both, which is the check     *)
(*    that the write-back rewrote the flag bits and nothing else.          *)
(* ---------------------------------------------------------------------- *)

Definition adu_fields : list Z :=
  [0x2000000000000000;   (* menvcfg: bit 61 accepted on both machines      *)
   0x11223344;           (* the load through the A = 0 leaf SUCCEEDED      *)
   0x200C0C47;           (* that leaf now has A set   (0x07 -> 0x47)       *)
   0x5A5A;               (* the store through the D = 0 leaf SUCCEEDED     *)
   0x200C0CC7;           (* that leaf now has D set   (0x47 -> 0xC7)       *)
   0].                   (* NO faults                                      *)

Lemma pt_adu_qemu_fields :
  ((fun o => cap_dw pt_adu_qemu_result o) <$> [8; 16; 24; 32; 40; 48]%nat)
  = adu_fields.
Proof. reflexivity. Qed.

(* the same list, taken off the MODEL rather than the capture, so that the
   two write-backs are named as model facts and not only as 4096 matching
   bytes *)
Lemma pt_adu_model_fields :
  ((fun o => res_dw adu_run o) <$> [8; 16; 24; 32; 40; 48]%nat) = adu_fields.
Proof. solve_vtest adu_fields. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. A CONFIRMATION, and which one.                                       *)
(*                                                                        *)
(* The A/D write-back arm is PROVEN in this development -- PtTreeAdue.v is *)
(* the exec layer for it and ten-plus live files depend on it, including   *)
(* the user/trap tier.  What had never been done is checking it against    *)
(* real hardware, and that is what this file is: the model's write-back    *)
(* produces the same PTE word, in the same memory location, as the virt    *)
(* board's, for both the A case and the D case, and leaves the rest of the *)
(* machine in a state whose entire observable projection agrees.           *)
(*                                                                        *)
(* It also settles a harness question that was open before this test: the  *)
(* write-back is not merely proven but EXECUTABLE by [exec], so a test may *)
(* drive it, and the finding-25 [sc.w] non-termination does not reach it.  *)
(* ---------------------------------------------------------------------- *)
