(* PlicPrio0.v -- source 0's priority register, and the init loop that a
   driver actually writes.

   Source: tools/vtest/tests/plic_prio0.S.  Capture: PlicPrio0Gen.v.

   [DevModel.plic_read] and [plic_write] gate the priority window on

     (0 <? off) && (off <? 4 * plic_nsrc) && (off mod 4 =? 0)

   and BOTH bounds cut off registers the hardware has.

   The lower one is the one with a driver behind it.  Offset 0 is source 0's
   priority register; source 0 does not exist, so on real hardware the
   register is hardwired to zero -- readable, and writes dropped.  The model
   has no transition for it at all, so

       for (i = 0; i < NSRC; i++) plic_priority[i] = 0;

   -- the loop a driver writes to mask everything before enabling what it
   wants -- is a STUCK machine on its FIRST iteration.  That is not an
   exotic access; it is the most ordinary line in a PLIC init routine.

   The upper one is recorded here too: source 32's register (offset 128) is
   a perfectly good register on the hardware, because the virt machine's
   PLIC has 96 sources where [plic_nsrc] is 32. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PlicPrio0Gen.
Local Open Scope Z_scope.

Definition prio0_run : option mstate := run_until 50000 (start plic_prio0_text).

(* ---------------------------------------------------------------------- *)
(* 1. The model, stated positively.                                        *)
(* ---------------------------------------------------------------------- *)

Lemma plic_prio0_model_stuck :
  run_status 50000 (start plic_prio0_text) = VStuck.
Proof. solve_vtest VStuck. Qed.

(* riscv64-linux-gnu-objdump -d tools/vtest/build/plic_prio0.elf:

     8000006c:  00092023   sw  zero,0(s2)

   with s2 = PLIC, i.e. the store of 0 to source 0's priority register.  The
   ORDINARY priority write two instructions earlier -- 0x80000058, source 1
   at offset 4 -- completed, and its read-back reached the result region, so
   nothing about the window or the access width is at fault: it is the
   [0 <? off] guard alone. *)
Lemma plic_prio0_stuck_at :
  stuck_pc 50000 (start plic_prio0_text) = 0x8000006c.
Proof. solve_vtest (0x8000006c : Z). Qed.

Lemma plic_prio0_no_result : result_of prio0_run = [].
Proof. solve_vtest (@nil Z). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. What the hardware did instead.                                       *)
(*                                                                         *)
(*      +8   source 1's priority, read back            7                   *)
(*      +12  source 0's priority after a store of 0    0                   *)
(*      +16  ...and after a store of 5                 0  (read-only zero)  *)
(*      +20  source 32's priority after a store of 4   4  (a real register) *)
(* ---------------------------------------------------------------------- *)

Definition prio0_qemu : list Z :=
  [cap_word plic_prio0_qemu_result 8;  cap_word plic_prio0_qemu_result 12;
   cap_word plic_prio0_qemu_result 16; cap_word plic_prio0_qemu_result 20].

Definition prio0_qemu_expect : list Z := [7; 0; 0; 4].

Lemma plic_prio0_qemu : prio0_qemu = prio0_qemu_expect.
Proof. solve_vtest prio0_qemu_expect. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. Classification: INCOMPLETENESS -- and the cheapest one in the suite   *)
(*    to retire.                                                           *)
(*                                                                         *)
(*    Not unsoundness: the system theorem proves xv6 never gets stuck, so   *)
(*    a state the model cannot leave is never reached, and nothing already  *)
(*    proved is weakened.  What it costs is which drivers can be described  *)
(*    at all -- and unlike the M-context gap (PlicMctx.v), this one is hit  *)
(*    by code that has no interest in any unusual feature.  xv6's own       *)
(*    plicinit only touches the two sources it uses, which is the only      *)
(*    reason the tree has never noticed.                                    *)
(*                                                                         *)
(*    The fix is ONE CHARACTER on the lower bound in each of [plic_read]    *)
(*    and [plic_write]: admit offset 0, reading zero and dropping the       *)
(*    write, which is what the hardware does.  It is not free only because  *)
(*    DevModel.v has a reverse-dependency closure to rebuild, so it wants   *)
(*    to be made together with the other DevModel changes this area has     *)
(*    turned up (PlicThresh.v section 3 is the one that matters).           *)
(*                                                                         *)
(*    The upper bound -- [plic_nsrc] = 32 against the machine's 96 -- is    *)
(*    the same kind of gap and a bigger change (the pending word becomes    *)
(*    three words, the enable word three per context), with no driver in    *)
(*    this tree behind it.  Recorded, not argued for.                       *)
(* ---------------------------------------------------------------------- *)
