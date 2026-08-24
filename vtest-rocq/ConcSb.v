(* ConcSb.v -- STORE BUFFERING.
   THIS FILE RECORDS THE SUITE'S SECOND UNSOUNDNESS, and the first one that
   is about the CPU rather than a device.

   Source: tools/vtest/tests/conc_sb.S (`vtest: smp=2 repeat=700`).
   Capture: ConcSbGen.v.

       hart 0:  X = 1 ; a = Y          hart 1:  Y = 1 ; b = X

   Under SEQUENTIAL CONSISTENCY (a,b) = (0,0) is impossible: the two stores
   are ordered somehow, and the load that follows the SECOND of them sees
   the first.  Under RVWMO -- and on any machine that lets a store sit in a
   buffer while a later load to a different address completes -- it is
   allowed.

   QEMU PRODUCES IT.  Over 1200 measured runs on an x86-64 host:

       (0,1)  905      (1,0)  226      (1,1)   14      (0,0)   55

   so 4.6% of runs are non-SC, and the capture -- 700 runs, sorted by the
   raw result bytes -- has all four outcomes, (0,0) first.  It is not a
   half-executed run: in that capture X and Y are BOTH 1, so both stores
   did happen and both loads still returned 0.  QEMU is within its rights;
   RISC-V permits it and the program has no fence between its store and its
   load.  This is the hardware behaviour that xv6's own lock code is
   written against.

   OUR MODEL CANNOT DO IT.  [RiscvLang]'s state has ONE memory, [gmem], and
   VConc hands each hart a projection of it and writes the whole thing back
   (section 3 below states exactly that, off the model rather than off this
   test).  There is nowhere for a store to wait, so every load reads the
   last store in the schedule order and the machine is SC by construction.
   That is the safe direction for a DEVICE test and the unsafe direction
   here: a mutual-exclusion proof discharged against this model is a proof
   about a machine that does not exist.  It is live in xv6 -- `acquire`'s
   `__sync_lock_test_and_set` / `release`'s `__sync_lock_release` carry
   `__sync_synchronize()` on either side precisely because the hardware
   reorders a store past a later load, and under this model those fences
   are unobservable no-ops.

   Fixing it is not local: it is the difference between a single [gmem] and
   a per-hart store buffer plus a `fence` transition that drains it, i.e. a
   different memory model under [prim_step], so this file only records it.

   RESULT layout, mirroring tools/vtest/tests/conc_sb.S:
     +0x000  DONE          +0x100  X               +0x104  Y
     +0x004  status = 1    +0x108  BAR0A  +0x10c  BAR1A   pass-1 rendezvous
     +0x008  a = hart 0's load of Y    +0x110  BAR0B  +0x114  BAR1B  pass 2
     +0x00c  b = hart 1's load of X    +0x118  P0X    +0x11c  P0Y
                                       +0x120  P1X    +0x124  P1Y
                                       +0x128  A0     +0x12c  A1  (warm-up)
                                       +0x130  DONE1 *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VConc ConcSbGen.
Local Open Scope Z_scope.

Definition sb_g0 : gstate := g0 conc_sb_text.

(* the pair (a,b) a result region records *)
Definition sb_pair (r : list Z) : Z * Z := (cap_word r 8, cap_word r 12).

(* ---------------------------------------------------------------------- *)
(* 1. Getting both harts to the litmus pair.                               *)
(*                                                                         *)
(*    Instruction counts off `riscv64-linux-gnu-objdump -d`.  Both harts    *)
(*    take 22 instructions from reset into <pass> and 6 more to the store   *)
(*    that publishes their pass-1 rendezvous flag, so:                      *)
(*                                                                         *)
(*      28  hart 0 arrives at rendezvous A                                  *)
(*      31  hart 1 arrives, sees hart 0, and falls through the spin         *)
(*      26  hart 0 falls through (3) and runs the WARM-UP pass (23),        *)
(*          ending on the store that publishes rendezvous B                 *)
(*      28  hart 1 does the same, falls through rendezvous B, and runs its  *)
(*          skew-trim delay loop, ending on `li t0, 1`                      *)
(*       9  hart 0 does the same (its delay loop is one round longer)       *)
(*                                                                         *)
(*    Both harts are now poised on their STORE, with two instructions each  *)
(*    left in the litmus test: [1] is the store, [2] is the store and the   *)
(*    load.  The counts differ (26/28/9 rather than one number) only        *)
(*    because the program deliberately gives the harts delay loops of       *)
(*    different lengths -- see the header of conc_sb.S.                     *)
(* ---------------------------------------------------------------------- *)

Definition align : list citem :=
  [CCpu hart0 28; CCpu hart1 31; CCpu hart0 26; CCpu hart1 28; CCpu hart0 9].

(* ---------------------------------------------------------------------- *)
(* 2. ALL SIX interleavings of the two two-instruction sequences, and what  *)
(*    each gives.  This is the exhaustive form of the SC argument: with     *)
(*    [s] the store and [l] the load,                                       *)
(*                                                                         *)
(*      s0 l0 s1 l1  (0,1)     s0 s1 l0 l1  (1,1)     s0 s1 l1 l0  (1,1)    *)
(*      s1 s0 l0 l1  (1,1)     s1 s0 l1 l0  (1,1)     s1 l1 s0 l0  (1,0)    *)
(*                                                                         *)
(*    -- and (0,0) is in none of them.                                     *)
(* ---------------------------------------------------------------------- *)

Definition sb_01 : list citem := align ++ [CCpu hart0 2; CCpu hart1 2].
Definition sb_11 : list citem :=
  align ++ [CCpu hart0 1; CCpu hart1 1; CCpu hart0 1; CCpu hart1 1].
Definition sb_ss_lr : list citem := align ++ [CCpu hart0 1; CCpu hart1 2; CCpu hart0 1].
Definition sb_ss_rl : list citem := align ++ [CCpu hart1 1; CCpu hart0 2; CCpu hart1 1].
Definition sb_11' : list citem :=
  align ++ [CCpu hart1 1; CCpu hart0 1; CCpu hart1 1; CCpu hart0 1].
Definition sb_10 : list citem := align ++ [CCpu hart1 2; CCpu hart0 2].

Definition sb_all_interleavings : list (list citem) :=
  [sb_01; sb_11; sb_ss_lr; sb_ss_rl; sb_11'; sb_10].

Definition sb_interleave_pairs : list (Z * Z) :=
  [(0,1); (1,1); (1,1); (1,1); (1,1); (1,0)].

Lemma conc_sb_interleavings :
  sb_pair <$> cobs_all 20000 sb_all_interleavings sb_g0 = sb_interleave_pairs.
Proof. solve_vtest sb_interleave_pairs. Qed.

Lemma conc_sb_no_interleaving_is_00 :
  Forall (fun p => p <> (0,0)) sb_interleave_pairs.
Proof. repeat constructor; discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. WHY, off the model rather than off this test.  A [gstate] has ONE     *)
(*    [gmem]; [ghart] hands a hart that same memory and [gput] takes the    *)
(*    memory the hart's step produced and makes it THE memory again.  There *)
(*    is no per-hart buffer for a store to wait in, so a load can only ever *)
(*    read the most recent store in the schedule -- which is what           *)
(*    sequential consistency IS, and what QEMU is not.                      *)
(* ---------------------------------------------------------------------- *)

Lemma model_hart_sees_the_one_memory : forall g c, mem (ghart g c) = gmem g.
Proof. reflexivity. Qed.

Lemma model_store_is_immediately_global : forall g c s, gmem (gput g c s) = mem s.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 4. THE TEST.  QEMU's capture has four outcomes; the model reproduces the *)
(*    three SEQUENTIALLY CONSISTENT ones, whole 4 KB region each, in the    *)
(*    order the capture lists them.  The capture is sorted by the raw       *)
(*    bytes, i.e. by (a,b), so the non-SC (0,0) is entry 0 and [tail] is    *)
(*    exactly the part the model can do.                                    *)
(* ---------------------------------------------------------------------- *)

Definition sb_schedules : list (list citem) := [sb_01; sb_10; sb_11].

Lemma conc_sb_model_admits_every_sc_outcome :
  cobs_all 20000 sb_schedules sb_g0 = tail conc_sb_qemu_results.
Proof. solve_vtest (tail conc_sb_qemu_results). Qed.

(* ---------------------------------------------------------------------- *)
(* 5. ...AND THE ONE IT CANNOT.  Cheap: these read the capture.            *)
(*    [conc_sb_qemu_is_not_sc] is the finding.                             *)
(*                                                                         *)
(*    WHAT A REGENERATION MUST SEE.  Both this section and section 4 (which *)
(*    lines its three schedules up with [tail]) assume the capture has all  *)
(*    four outcomes.  At the measured rates and repeat = 700 the binding    *)
(*    constraint is not (0,0) at 4.6% -- missing that is a 1-in-10^14       *)
(*    event -- but (1,1) at 1.2%, which a regeneration misses about once in *)
(*    4000.  If one of these goes red, regenerate; do not weaken the lemma. *)
(* ---------------------------------------------------------------------- *)

Definition sb_qemu_pairs : list (Z * Z) := sb_pair <$> conc_sb_qemu_results.

Lemma conc_sb_qemu_outcomes : sb_qemu_pairs = [(0,0); (0,1); (1,0); (1,1)].
Proof. reflexivity. Qed.

Lemma conc_sb_qemu_is_not_sc : (0,0) ∈ sb_qemu_pairs.
Proof. rewrite conc_sb_qemu_outcomes. left. Qed.

(* it is a real (0,0) and not a run that stopped early: BOTH stores landed *)
Lemma conc_sb_both_stores_happened :
  (cap_word (hd [] conc_sb_qemu_results) 256,
   cap_word (hd [] conc_sb_qemu_results) 260) = (1, 1).
Proof. reflexivity. Qed.

(* the model's six interleavings, side by side with QEMU's four outcomes:
   the model has (1,1) that QEMU rarely shows, and QEMU has (0,0) that the
   model never shows.  The second gap is the unsound one. *)
Lemma conc_sb_really_diverges : sb_interleave_pairs <> sb_qemu_pairs.
Proof. discriminate. Qed.
