(* ======================================================================= *)
(* PtTlb.v -- A STALE TRANSLATION, AND THE ONE PLACE THE MODEL CANNOT KEEP  *)
(* ONE.  THIS FILE RECORDS A DIVERGENCE IN THE UNSOUND DIRECTION.           *)
(*                                                                          *)
(* Source: tools/vtest/tests/pt_tlb.S.  Capture: PtTlbGen.v (20 runs).      *)
(* 134 instructions on the model side.                                      *)
(*                                                                          *)
(* The program maps ONE physical word two ways in succession: a level-0     *)
(* leaf is walked, then REWRITTEN through the identity map to point at a    *)
(* different page, then read again WITHOUT an sfence.vma, then sfenced and  *)
(* read a third time.  It does this at TWO virtual addresses that differ    *)
(* only in which TLB set they land in.                                      *)
(*                                                                          *)
(* NEITHER ANSWER TO THE MIDDLE READ IS WRONG.  The architecture permits an *)
(* implementation to keep the old translation until an sfence.vma, and      *)
(* equally permits it to have dropped the entry for any reason at all.  The *)
(* test is captured as a SET over 20 runs for exactly that reason; QEMU     *)
(* produced one outcome in all 20.                                          *)
(*                                                                          *)
(* WHAT THE TWO ADDRESSES ARE FOR.  The model's TLB is 64 entries and       *)
(* DIRECT-MAPPED: [tlb] is a [vec (option TLB_Entry) 64] and [tlb_hash]     *)
(* (rv64d.v:24650) is literally the low [num_tlb_entries_exp] = 6 bits of   *)
(* the VPN.  Every instruction in this image is fetched from VA 0x800001xx  *)
(* (VPN 0x80000, set 0) and every result store goes to VA 0x801000xx (VPN   *)
(* 0x80100, set 0), so an entry for a test VA in SET 0 is evicted by the    *)
(* very next instruction the program executes.  A test VA in a set nothing  *)
(* else touches is not.  Hence:                                             *)
(*                                                                          *)
(*   VA 0x40000300  VPN 0x40000, SET 0  -- collides with text and result    *)
(*   VA 0x40007300  VPN 0x40007, SET 7  -- collides with nothing here       *)
(*                                                                          *)
(* AND THAT SPLITS THE RESULT CLEANLY.  At set 7 the two machines AGREE:    *)
(* both keep the stale translation and both return the old page's value.    *)
(* At set 0 they do not: QEMU still returns the old page, and the model has *)
(* re-walked and returns the new one.  So the difference is not about       *)
(* staleness policy at all -- it is CAPACITY, and set 7 is the control that *)
(* proves it.                                                               *)
(*                                                                          *)
(* RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):     *)
(*   +8   VA 0x40000300, first load -- fills set 0                           *)
(*   +16  VA 0x40007300, first load -- fills set 7                           *)
(*   +24  VA 0x40000300 after the rewrite, NO sfence.vma   <-- DIVERGES      *)
(*   +32  VA 0x40007300 after the rewrite, NO sfence.vma                     *)
(*   +40  VA 0x40000300 after sfence.vma                                     *)
(*   +48  VA 0x40007300 after sfence.vma                                     *)
(*   +56  how many faults were taken                                         *)
(* ======================================================================= *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import VTest PtTlbGen.
Local Open Scope Z_scope.

Definition res_dw (o : option mstate) (off : nat) : Z :=
  res_word o off + 4294967296 * res_word o (off + 4)%nat.
Definition cap_dw (c : list Z) (off : nat) : Z :=
  cap_word c off + 4294967296 * cap_word c (off + 4)%nat.

Definition tlb_run : option mstate := run_until 400 (start_pt pt_tlb_text).

(* ---------------------------------------------------------------------- *)
(* 1. THE SIX FIELDS THAT AGREE, and they are most of the test.            *)
(*                                                                        *)
(*    +8/+16   both first loads see the ORIGINAL mapping (0x11223344).     *)
(*    +32      THE CONTROL: at set 7, with no sfence.vma, BOTH machines    *)
(*             still use the STALE entry.  So the model does implement a   *)
(*             TLB that survives a PTE write, and QEMU's behaviour at set  *)
(*             0 is not something the model is categorically unable to do. *)
(*    +40/+48  after sfence.vma both machines see the NEW mapping at both  *)
(*             addresses (0x99887766), so the flush is total on both.      *)
(*    +56      no faults anywhere.                                         *)
(* ---------------------------------------------------------------------- *)

Definition tlb_agree_offs : list nat := [8; 16; 32; 40; 48; 56]%nat.

Definition tlb_agreed : list Z :=
  [0x11223344;   (* set 0, first load                                      *)
   0x11223344;   (* set 7, first load                                      *)
   0x11223344;   (* set 7, no sfence: BOTH machines keep the stale entry   *)
   0x99887766;   (* set 0, after sfence.vma                                *)
   0x99887766;   (* set 7, after sfence.vma                                *)
   0].           (* no faults                                              *)

Lemma pt_tlb_qemu_agreed :
  ((fun o => cap_dw pt_tlb_qemu_result o) <$> tlb_agree_offs) = tlb_agreed.
Proof. reflexivity. Qed.

Lemma pt_tlb_model_agreed :
  ((fun o => res_dw tlb_run o) <$> tlb_agree_offs) = tlb_agreed.
Proof. solve_vtest tlb_agreed. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE ONE FIELD THAT DOES NOT, pinned on both sides.                   *)
(* ---------------------------------------------------------------------- *)

Definition tlb_model_diverging : Z := 0x99887766.  (* the model RE-WALKED  *)
Definition tlb_qemu_diverging  : Z := 0x11223344.  (* QEMU kept the entry  *)

Lemma pt_tlb_model_diverging : res_dw tlb_run 24%nat = tlb_model_diverging.
Proof. solve_vtest tlb_model_diverging. Qed.

Lemma pt_tlb_qemu_diverging :
  cap_dw pt_tlb_qemu_result 24%nat = tlb_qemu_diverging.
Proof. reflexivity. Qed.

Lemma pt_tlb_really_diverges : tlb_model_diverging <> tlb_qemu_diverging.
Proof. discriminate. Qed.

(* QEMU produced this ONE outcome in all 20 runs -- the capture is a set,
   and the set is a singleton, so the divergence is not a rare interleaving *)
Lemma pt_tlb_qemu_is_deterministic :
  length pt_tlb_qemu_results = 1%nat.
Proof. reflexivity. Qed.

Lemma pt_tlb_disk : pt_tlb_qemu_disk = [].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. WHY, OFF THE MODEL RATHER THAN OFF THE TEST.                         *)
(*                                                                        *)
(*    [tlb_hash] discards everything but the low 6 bits of the VPN, and    *)
(*    both [lookup_TLB] and [add_to_TLB] index the single 64-slot vector   *)
(*    with it, so the structure is direct-mapped by construction and two   *)
(*    VPNs congruent mod 64 CANNOT be resident at the same time.  The test *)
(*    VA 0x40000300 (VPN 0x40000) and the text/result pages (VPNs 0x80000  *)
(*    and 0x80100) are all congruent to 0, which is the whole mechanism.   *)
(*    0x40007 is not, which is why set 7 agrees.                           *)
(* ---------------------------------------------------------------------- *)

Definition sv39_vpn (v : Z) :=
  SailStdpp.Values.mword_of_int (len := 39 - 12) v.

Lemma model_tlb_is_64_way_direct_mapped : num_tlb_entries_exp = 6.
Proof. reflexivity. Qed.

Lemma model_tlb_sets_collide :
  tlb_hash 39 (sv39_vpn 0x40000) = tlb_hash 39 (sv39_vpn 0x80000)
  /\ tlb_hash 39 (sv39_vpn 0x40000) = tlb_hash 39 (sv39_vpn 0x80100).
Proof. split; vm_compute; reflexivity. Qed.

Lemma model_tlb_set7_does_not :
  tlb_hash 39 (sv39_vpn 0x40007) <> tlb_hash 39 (sv39_vpn 0x80000).
Proof. vm_compute; discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* 4. CLASSIFICATION, and how far it reaches.                              *)
(*                                                                        *)
(* BY THE SUITE'S OWN RULE THIS IS THE UNSOUND DIRECTION: the hardware did *)
(* something -- returned the OLD translation for VA 0x40000300 -- for      *)
(* which the model has no execution.  It is not a scheduling gap either.   *)
(* [exec] is deterministic through the walk, [tlb_hash] is a function, and *)
(* the eviction happens inside the FETCH of the very next instruction, so  *)
(* no choice the harness can make keeps that entry resident.               *)
(*                                                                        *)
(* BUT THE SHAPE IS DIFFERENT FROM FINDINGS 5, 10 AND 24, and the          *)
(* difference is worth being precise about.  Those are cases where the     *)
(* model's transition relation LACKS an architecturally required freedom.  *)
(* Here the model has the freedom -- it keeps stale entries, as +32 shows  *)
(* -- and merely has a SMALLER, less associative TLB than the reference    *)
(* machine.  Both are legal implementations.  What makes it matter is the  *)
(* direction of the resulting proof obligation: a theorem proved against   *)
(* this model may conclude that the access after a PTE write uses the NEW *)
(* mapping, in a case where the real machine uses the old one, because the *)
(* model's eviction is guaranteed and the hardware's is not.  That         *)
(* conclusion is only reachable for software that omits sfence.vma, which  *)
(* is software the architecture already declares wrong -- so nothing in    *)
(* xv6 is exposed (kvminithart and the satp switch both fence) -- but the  *)
(* model does not REFUSE such a program, it silently gives it the          *)
(* favourable answer.                                                      *)
(*                                                                        *)
(* THE FIX, IF ONE IS WANTED, IS NOT A CAPACITY INCREASE.  Making the TLB  *)
(* bigger or associative moves the collision, it does not remove it; any   *)
(* deterministic finite TLB is eventually forced to evict where a real one *)
(* need not.  A model that admitted the hardware here would have to make   *)
(* eviction NONDETERMINISTIC -- an entry may be dropped at any time, and   *)
(* an sfence.vma is the only thing that must drop it -- which is the same  *)
(* over-approximation shape finding 17's [DevStepDiskWild] uses for the    *)
(* disk.  That is a change to [translate], not to a constant, and it is    *)
(* the kind of thing the owner decides.  Recorded, not proposed.           *)
(* ---------------------------------------------------------------------- *)
