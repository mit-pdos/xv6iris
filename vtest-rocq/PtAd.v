(* ======================================================================= *)
(* PtAd.v -- A/D BITS IN THE DEFAULT CONFIGURATION.  THE TWO MACHINES TAKE  *)
(* DIFFERENT ARCHITECTURAL PATHS, AND EVERY OBSERVATION DIVERGES.           *)
(*                                                                          *)
(* Source: tools/vtest/tests/pt_ad.S.  Capture: PtAdGen.v.                  *)
(* 148 instructions on the model side.                                      *)
(*                                                                          *)
(* This is finding 20 with a program attached.  menvcfg bit 61 is ADUE, the *)
(* Svadu enable, and neither side touches it here:                          *)
(*                                                                          *)
(*   ADUE = 1 (Svadu)  a walk that finds A clear -- or D clear on a store   *)
(*                     -- WRITES THE UPDATED PTE BACK and the access        *)
(*                     succeeds.                                            *)
(*   ADUE = 0 (Svade)  the same walk raises a PAGE FAULT and software is    *)
(*                     expected to set the bit.                             *)
(*                                                                          *)
(* The model powers up at 0 and QEMU powers up at 1, so the SAME PROGRAM is *)
(* Svade on one machine and Svadu on the other.  The program maps two 4 KB  *)
(* leaves through a full three-level walk -- one with A = 0, loaded         *)
(* through, one with A = 1 and D = 0, stored through -- and reads BOTH LEAF *)
(* PTEs BACK OUT OF MEMORY afterwards, so "the hardware wrote the bit" is   *)
(* observed rather than inferred.                                          *)
(*                                                                          *)
(* AND THIS IS THE COMMON CASE, not a corner.  xv6's riscv.h defines no     *)
(* PTE_A and no PTE_D at all, and mappages writes PA2PTE(pa) | perm |       *)
(* PTE_V, so the post-kvmmake table has A and D CLEAR in every entry and a  *)
(* real run takes one of these two paths on the FIRST access to every page. *)
(*                                                                          *)
(* WHAT IS *NOT* A FINDING HERE: neither behaviour is wrong.  Both are      *)
(* faithful implementations of their own value of ADUE, and PtAdu.v and     *)
(* PtAde.v show the two machines agreeing EXACTLY once the bit is pinned to *)
(* the same value on both.  The divergence is entirely the power-on value.  *)
(*                                                                          *)
(* RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):     *)
(*   +8   menvcfg read in M-mode at entry, before anything else              *)
(*   +16  the value loaded from VA 0x40000000 (A = 0 leaf); the destination  *)
(*        register is preloaded with 0xBAD1 and the handler skips the        *)
(*        faulting instruction, so 0xBAD1 means "it faulted"                 *)
(*   +24  the A = 0 leaf PTE, read back out of the page-table page           *)
(*   +32  the word at PA 0x80303008 after a store through VA 0x40001008      *)
(*        (the page is zeroed, so 0 means the store never landed)            *)
(*   +40  the D = 0 leaf PTE, read back out of the page-table page           *)
(*   +48  how many faults were taken                                         *)
(*   +0x100  the fault records, 24 bytes each: scause, sepc, stval           *)
(* ======================================================================= *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PtAdGen.
Local Open Scope Z_scope.

Definition res_dw (o : option mstate) (off : nat) : Z :=
  res_word o off + 4294967296 * res_word o (off + 4)%nat.
Definition cap_dw (c : list Z) (off : nat) : Z :=
  cap_word c off + 4294967296 * cap_word c (off + 4)%nat.

Definition ad_run : option mstate := run_until 400 (start_pt pt_ad_text).

(* the six observations, plus the two fault records the Svade machine
   produces and the Svadu machine does not *)
Definition ad_offs : list nat :=
  [8; 16; 24; 32; 40; 48;
   256; 264; 272;          (* fault 1: scause, sepc, stval *)
   280; 288; 296]%nat.     (* fault 2: scause, sepc, stval *)

(* ---------------------------------------------------------------------- *)
(* 1. THE MODEL: Svade.  Both accesses fault, both PTEs are untouched, and  *)
(*    neither the load nor the store happened.                             *)
(*                                                                        *)
(*    The two fault records are exactly what the architecture prescribes:  *)
(*    scause 13 (load page fault) at the load and 15 (store page fault) at *)
(*    the store, with stval carrying the faulting VIRTUAL address in both  *)
(*    cases -- not the physical one and not the PTE address.               *)
(* ---------------------------------------------------------------------- *)

Definition ad_model : list Z :=
  [0;                     (* menvcfg -- ArchReset.board_regs pins the whole
                             value, so ADUE is 0 and the machine is Svade  *)
   0xBAD1;                (* the load FAULTED; the poison survived         *)
   0x200C0C07;            (* the A = 0 leaf, UNCHANGED (flags 0x07 = R|W|V)*)
   0;                     (* the store never landed                        *)
   0x200C0C47;            (* the D = 0 leaf, UNCHANGED (flags 0x47 = A|R|W|V) *)
   2;                     (* two faults                                    *)
   13; 0x80000180; 0x40000000;
   15; 0x800001AC; 0x40001008].

Lemma pt_ad_model : ((fun o => res_dw ad_run o) <$> ad_offs) = ad_model.
Proof. solve_vtest ad_model. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE HARDWARE: Svadu.  Both accesses SUCCEED, and the two leaf PTEs   *)
(*    in memory have GAINED the bits -- 0x07 -> 0x47 (A set by the load)   *)
(*    and 0x47 -> 0xC7 (D set by the store).  Nothing faulted.             *)
(*                                                                        *)
(*    That the PTE WORD IN MEMORY CHANGED is the observation that matters. *)
(*    "The access succeeded" alone would also be produced by a machine     *)
(*    that ignored A/D entirely; only reading the entry back distinguishes *)
(*    a real write-back from a check that was never performed.             *)
(* ---------------------------------------------------------------------- *)

Definition ad_qemu : list Z :=
  [0x2000000000000000;    (* menvcfg at power-on: ADUE set                 *)
   0x11223344;            (* the load succeeded                            *)
   0x200C0C47;            (* the A = 0 leaf: HARDWARE SET A (0x07 -> 0x47) *)
   0x5A5A;                (* the store succeeded                           *)
   0x200C0CC7;            (* the D = 0 leaf: HARDWARE SET D (0x47 -> 0xC7) *)
   0;                     (* no faults                                     *)
   0; 0; 0;
   0; 0; 0].

Lemma pt_ad_qemu :
  ((fun o => cap_dw pt_ad_qemu_result o) <$> ad_offs) = ad_qemu.
Proof. reflexivity. Qed.

Lemma pt_ad_really_diverges : ad_model <> ad_qemu.
Proof. discriminate. Qed.

Lemma pt_ad_disk : pt_ad_qemu_disk = [].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. CLASSIFICATION.                                                      *)
(*                                                                        *)
(* INCOMPLETENESS, with one root cause and a concrete consequence.  The    *)
(* root cause is the single register value finding 20 already named:       *)
(* [ArchReset.board_regs] writes menvcfg = 0 as a whole-value board        *)
(* obligation (the spec's own [reset_sys] never touches menvcfg, and the   *)
(* fast decode bridge consumes all 64 bits), and the virt board powers up  *)
(* with ADUE set.  Both machines HAVE Svadu -- sail-config-rv64d.json says *)
(* "Svadu": supported, and QEMU's rv64 implements it -- so this is not the *)
(* which-machine-is-modelled axis that findings 19 and 22 sit on.  It is   *)
(* one bit of assumed board state, and it is false of this board.          *)
(*                                                                        *)
(* The consequence is not abstract.  Under the model's power-on value the  *)
(* FIRST access to every page of a faithfully-built xv6 kernel table is a  *)
(* page fault, because xv6 sets neither A nor D.  A model run from the     *)
(* faithful post-kvmmake state therefore diverges from the machine on its  *)
(* very first translated access -- which is why the live development       *)
(* instead assumes the bits preset ([kpt_adf1 := fun _ => (true, true)]).  *)
(*                                                                        *)
(* IT IS ALSO A ONE-INSTRUCTION FIX AT THE SOFTWARE LEVEL, and xv6 already *)
(* applies it: start() sets ADUE before entering S-mode.  So the model's   *)
(* menvcfg = 0 is a statement about the machine BEFORE the kernel's first  *)
(* CSR write, and the whole divergence disappears once either machine      *)
(* names the mode it wants.  PtAdu.v and PtAde.v are that experiment, and  *)
(* both come out identical byte for byte.                                  *)
(* ---------------------------------------------------------------------- *)
