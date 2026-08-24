(* PlicMctx.v -- the M-CONTEXT registers, and the model has no transition for
   any of them.

   Source: tools/vtest/tests/plic_mctx.S.  Capture: PlicMctxGen.v.

   The virt machine's PLIC gives every hart TWO contexts: 2h is the M-mode
   one and 2h+1 the S-mode one.  [DevModel]'s decode recognises only the
   second of each pair, because that is all xv6 uses:

     enable          0x2080   + h*0x100     ([plic_senable_hart])
     threshold       0x201000 + h*0x2000    ([plic_sthresh_hart])
     claim/complete  0x201004 + h*0x2000    ([plic_sclaim_hart])

   Hart 0's M-context registers sit one stride below each of those, at
   0x2000, 0x200000 and 0x200004.  All three fall through every arm of
   [plic_read]/[plic_write] to [None], so the transaction has no successor
   and the machine is STUCK -- while QEMU services all three (section 2).

   The program does its S-context work FIRST, and that part runs: the window
   is decoded, the enable and threshold registers read back what was written.
   It is the first M-context access, and only that, that stops the model. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PlicMctxGen.
Local Open Scope Z_scope.

Definition mctx_run : option mstate := run_until 50000 (start plic_mctx_text).

(* ---------------------------------------------------------------------- *)
(* 1. The model, stated positively.                                        *)
(* ---------------------------------------------------------------------- *)

(* Not a budget that ran out -- a machine with nowhere to go. *)
Lemma plic_mctx_model_stuck :
  run_status 50000 (start plic_mctx_text) = VStuck.
Proof. solve_vtest VStuck. Qed.

(* ...and WHICH access.  riscv64-linux-gnu-objdump -d
   tools/vtest/build/plic_mctx.elf:

     8000009c:  00532023   sw  t0,0(t1)

   with t1 = PLIC + 0x2000, i.e. the store of the enable word for hart 0's
   M context.  The two S-context accesses before it (0x80000064 and
   0x8000007c) completed. *)
Lemma plic_mctx_stuck_at :
  stuck_pc 50000 (start plic_mctx_text) = 0x8000009c.
Proof. solve_vtest (0x8000009c : Z). Qed.

Lemma plic_mctx_no_result : result_of mctx_run = [].
Proof. solve_vtest (@nil Z). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. What the hardware did instead.                                       *)
(*                                                                         *)
(*      +8   S enable    read back   0x402                                 *)
(*      +12  S threshold read back   3                                     *)
(*      +16  M enable    read back   0x402                                 *)
(*      +20  M threshold read back   2                                     *)
(*      +24  M claim                 0                                     *)
(*                                                                         *)
(*    All five, so the M-context registers are not merely tolerated on the  *)
(*    hardware, they are fully functional: writable, and reading back what  *)
(*    was written.                                                         *)
(* ---------------------------------------------------------------------- *)

Definition mctx_qemu : list Z :=
  [cap_word plic_mctx_qemu_result 8;  cap_word plic_mctx_qemu_result 12;
   cap_word plic_mctx_qemu_result 16; cap_word plic_mctx_qemu_result 20;
   cap_word plic_mctx_qemu_result 24].

Definition mctx_qemu_expect : list Z := [0x402; 3; 0x402; 2; 0].

Lemma plic_mctx_qemu : mctx_qemu = mctx_qemu_expect.
Proof. solve_vtest mctx_qemu_expect. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. Classification: INCOMPLETENESS.                                      *)
(*                                                                         *)
(*    A stuck machine is not unsoundness.  The system theorem proves xv6    *)
(*    never gets stuck, so a state the model cannot leave is a state xv6    *)
(*    never reaches, and no theorem about xv6 is weakened.  What it costs   *)
(*    is REACH: an M-mode external-interrupt handler, or a machine-mode     *)
(*    bootloader that parks its own context by writing the M threshold      *)
(*    before handing off to S mode, cannot be described in this model at    *)
(*    all -- not proved wrong, simply outside it.                          *)
(*                                                                         *)
(*    The fix is three lines and entirely local: each of the three          *)
(*    sub-decodes gets its M-context twin (0x2000 + h*0x100, 0x200000 +     *)
(*    h*0x2000, 0x200004 + h*0x2000), and [plic_state]'s [p_enable] /       *)
(*    [p_thresh] are already indexed by a [nat] context, so they would      *)
(*    take a context number rather than a hart number.  That last part is   *)
(*    what makes it a decision rather than a drive-by edit: [plic_eip] is   *)
(*    called from [dev_seip], which the language uses to drive sig_seip,    *)
(*    and an M context would need its own pin.                             *)
(* ---------------------------------------------------------------------- *)
