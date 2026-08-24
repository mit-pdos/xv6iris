(* ======================================================================= *)
(* PtIdent.v -- THE BASELINE OF THE `pt` AREA: S-MODE WITH PAGING ON.       *)
(*                                                                          *)
(* Source: tools/vtest/tests/pt_ident.S.  Capture: PtIdentGen.v.            *)
(* 89 instructions on the model side.                                       *)
(*                                                                          *)
(* This is the test the rest of the area rests on.  It builds ONE Sv39      *)
(* page-table entry -- a level-2 leaf, i.e. a gigapage, identity-mapping    *)
(* VA 0x80000000 to PA 0x80000000, which covers the text, the stack, the    *)
(* result region and the page-table pages themselves -- turns translation   *)
(* on, drops to S-mode with [mret], and then does ordinary work through it: *)
(* a store, a load back, a fetch of every instruction it executes, and a    *)
(* read of the image's own first word.                                      *)
(*                                                                          *)
(* THE WHOLE 4 KB RESULT REGION AGREES, byte for byte.  That is six         *)
(* independent things at once, and each is a way the model could have been  *)
(* wrong:                                                                   *)
(*                                                                          *)
(*   - the PMP grant.  The model implements 16 PMP entries and the boot     *)
(*     chain leaves them ALL OFF; with entries implemented and none         *)
(*     matching, M-mode passes and S-mode FAILS EVERY ACCESS.  The one TOR  *)
(*     entry xv6's start() writes (pmpaddr0 = 0x3fffffffffffff,             *)
(*     pmpcfg0 = 0xf) is what makes S-mode possible at all, on both sides.  *)
(*   - the satp write and the [sfence.vma] after it, and the readback of    *)
(*     satp FROM S-MODE (0x8000000000080300 = MODE 8, ASID 0, PPN 0x80300). *)
(*   - [mret] to Supervisor with mstatus.MPP = 1.                           *)
(*   - the level-2 leaf itself: a walk that terminates at the ROOT, taking  *)
(*     30 bits of page offset from the VA.                                  *)
(*   - a FETCH through translation -- every instruction after the mret --   *)
(*     as well as a load and a store.                                       *)
(*   - sstatus as S-mode sees it (0x200000000 = UXL 2), derived through the *)
(*     model's [lower_mstatus] window onto the board-written mstatus.       *)
(*                                                                          *)
(* menvcfg.ADUE IS PINNED DELIBERATELY, and every pt_ test does the same.   *)
(* Finding 20 says the power-on value DIFFERS -- bit 61 is 0 in the model   *)
(* (Svade) and set on QEMU (Svadu) -- so a table written the natural way,   *)
(* with no A/D bits, faults on one machine and succeeds on the other for a  *)
(* reason that has nothing to do with translation.  This test sets ADUE (it *)
(* is what xv6 runs under, since start() sets it) AND presets A and D in    *)
(* the leaf, so no A/D write-back can fire either.  PtAd/PtAdu/PtAde are    *)
(* the tests that are ABOUT that path.                                      *)
(*                                                                          *)
(* RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):     *)
(*   +8   satp read back in S-mode      +16  the value stored and re-loaded  *)
(*   +24  scause (0 -- nothing trapped) +32  the image's first word          *)
(*   +40  sstatus in S-mode             +48  menvcfg after the ADUE write    *)
(*   +0x100  the M-mode backstop's record: mcause, mepc, mtval               *)
(* ======================================================================= *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PtIdentGen.
Local Open Scope Z_scope.

Definition res_dw (o : option mstate) (off : nat) : Z :=
  res_word o off + 4294967296 * res_word o (off + 4)%nat.
Definition cap_dw (c : list Z) (off : nat) : Z :=
  cap_word c off + 4294967296 * cap_word c (off + 4)%nat.

Definition ident_run : option mstate := run_until 300 (start_pt pt_ident_text).

(* ---------------------------------------------------------------------- *)
(* 1. Everything agrees, and nothing is trimmed: the WHOLE result region,   *)
(*    untouched zeros included.                                            *)
(* ---------------------------------------------------------------------- *)

Lemma pt_ident_result : result_of ident_run = pt_ident_qemu_result.
Proof. solve_vtest pt_ident_qemu_result. Qed.

Lemma pt_ident_disk : pt_ident_qemu_disk = [].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. What the agreeing values ARE.  These are read off the CAPTURE, so     *)
(*    they cost no model run; §1 is what ties them to the model.  Naming    *)
(*    them is the difference between "4096 bytes matched" and knowing that  *)
(*    the program really did reach S-mode with paging on.                  *)
(* ---------------------------------------------------------------------- *)

Definition ident_fields : list Z :=
  [0x8000000000080300;   (* satp: MODE = 8 (Sv39), ASID = 0, PPN = 0x80300 *)
   0x123456789ABCDEF0;   (* stored through the VA and loaded back          *)
   0;                    (* scause -- no trap of any kind                  *)
   0xF14022F3;           (* the image's own first word (csrr t0, mhartid)  *)
   0x200000000;          (* sstatus: UXL = 2, everything else clear        *)
   0x2000000000000000].  (* menvcfg after the ADUE write: bit 61 stuck     *)

Lemma pt_ident_qemu_fields :
  ((fun o => cap_dw pt_ident_qemu_result o) <$> [8; 16; 24; 32; 40; 48]%nat)
  = ident_fields.
Proof. reflexivity. Qed.

(* the M-mode backstop never fired, which is how we know every trap that
   could have happened was DELEGATED and none happened at all *)
Lemma pt_ident_no_mtrap :
  ((fun o => cap_dw pt_ident_qemu_result o) <$> [256; 264; 272]%nat)
  = [0; 0; 0].
Proof. reflexivity. Qed.
