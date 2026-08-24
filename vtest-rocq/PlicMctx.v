(* PlicMctx.v -- the M-CONTEXT registers.  All five observations agree; this
   file used to record finding 11, where the model had no transition for any
   of them and the program STOPPED at the first one.

   Source: tools/vtest/tests/plic_mctx.S.  Capture: PlicMctxGen.v.

   The virt machine's PLIC gives every hart TWO contexts: 2h is the M-mode
   one and 2h+1 the S-mode one.  The decode used to recognise only the second
   of each pair, because that is all xv6 uses:

     enable          0x2080   + h*0x100
     threshold       0x201000 + h*0x2000
     claim/complete  0x201004 + h*0x2000

   Hart 0's M-context registers sit one stride below each of those, at
   0x2000, 0x200000 and 0x200004, and all three fell through every arm of
   [plic_read]/[plic_write] to [None].

   [DevModel]'s PLIC is now indexed by CONTEXT rather than by hart -- both
   halves of every pair, [plic_nctx] of them, with [plic_mctx]/[plic_sctx]
   naming the two a hart owns -- so the M registers are the S registers'
   equals: same code, different index.  The program does its S-context work
   first and its M-context work second, and the two sets are INDEPENDENT,
   which is the part worth checking (see below). *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list bitvector.definitions.
Require Import VTest PlicMctxGen.
Local Open Scope Z_scope.

Definition mctx_run : option mstate := run_until 50000 (start plic_mctx_text).

(* result-region offsets, mirroring tools/vtest/tests/plic_mctx.S *)
Definition mctx_offs : list nat :=
  [4;   (* progress marker: 2 = the whole program ran *)
   8;   (* S-context enable word read back           0x402 *)
   12;  (* S-context threshold read back                 3 *)
   16;  (* M-context enable word read back           0x402 *)
   20;  (* M-context threshold read back                 2 *)
   24]%nat. (* M-context claim                           0 *)

Definition mctx_expect :=
  (fun o => cap_word plic_mctx_qemu_result o) <$> mctx_offs.

Lemma plic_mctx_agrees :
  (fun o => res_word mctx_run o) <$> mctx_offs = mctx_expect.
Proof. solve_vtest mctx_expect. Qed.

(* ---------------------------------------------------------------------- *)
(* 1. What the fields say.                                                 *)
(*                                                                         *)
(*    +8/+12 against +16/+20 is the point: the same two registers of the    *)
(*    two contexts of ONE hart, written with DIFFERENT thresholds (3 and 2) *)
(*    and read back independently.  A model that aliased the pair -- one    *)
(*    threshold per hart, say, with the M address folded onto the S one --   *)
(*    would report 2 at +12 as well, so the pair is what pins that a hart   *)
(*    has two contexts and not one register file seen from two addresses.   *)
(*                                                                         *)
(*    +24 is the M claim with nothing pending: 0, the same "nothing to      *)
(*    serve" answer the S claim gives, from the same [plic_claim] at the     *)
(*    other context index.                                                 *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(* 2. The pins, which no program in this suite can observe.                *)
(*                                                                         *)
(*    A context's threshold and enable bitmap decide its NOTIFICATION, and  *)
(*    the board wires each context to a pin: 2h+1 to hart h's external      *)
(*    S-interrupt pin and 2h to its M one ([DevModel.dev_seip]/[dev_meip],  *)
(*    one [RiscvLang.plic_step] wire arm each).  Decoding the M registers    *)
(*    without driving the M pin would have been the same half-fix as a      *)
(*    stored-but-inert control bit, so the pin is modelled -- and stated    *)
(*    here off the model, since this program runs with interrupts disabled  *)
(*    and cannot see either pin move.                                      *)
(* ---------------------------------------------------------------------- *)

Definition mctx_pin_state : plic_state :=
  match plic_write plic0_state (4 * 10) (Z_to_bv 32 3) with   (* prio[10] := 3 *)
  | Some p =>
      match plic_write p 0x2000 (Z_to_bv 32 0x400) with       (* M ctx enables 10 *)
      | Some p =>
          match plic_latch p 10 with Some p => p | None => p end
      | None => p
      end
  | None => plic0_state
  end.

Definition mctx_pins : dev_state :=
  DevState uart0_state mctx_pin_state virtio0_state.

(* the M context sees it, so hart 0's M pin is high; its S context enables
   nothing, so its S pin is low; and no other hart's context is touched *)
Lemma plic_mctx_pins :
  (dev_meip mctx_pins 0, dev_seip mctx_pins 0, dev_meip mctx_pins 1)
  = (true, false, false).
Proof. solve_vtest (true, false, false). Qed.
