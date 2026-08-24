(* ====================================================================== *)
(* VTest.v -- the model side of a device-semantics test.                   *)
(*                                                                         *)
(* WHAT A TEST CLAIMS, and why it is cheap.  The question these tests       *)
(* answer is one-directional: is what the real hardware (QEMU) did an       *)
(* execution our model ALLOWS?  So a test has only to EXHIBIT one model     *)
(* execution matching what QEMU produced -- not to reason about every       *)
(* execution.  Exhibiting one is a COMPUTATION, so there is no WP, no       *)
(* invariant and no Iris anywhere in this directory, and a test is one      *)
(* [vm_cast_no_check]d equation.  Nothing here is restricted to what the    *)
(* xv6 driver's proofs assume: a test may configure the queue illegally,    *)
(* and the only question is whether the model has a run that matches.       *)
(*                                                                         *)
(* WHAT IT DOES NOT YET CLAIM.  [exec] is the functional interpreter, tied  *)
(* to the relational [run] by [RiscvExec.exec_run_det]; [run] is the        *)
(* WHOLE-INSTRUCTION step, while the deployed language ([RiscvLang.         *)
(* prim_step]) steps one Sail-monad NODE at a time and [HartBlock] proves   *)
(* only block => run.  So a green test here is a fact about the model as    *)
(* [exec] interprets it -- which does exercise [DevModel]/[VirtioModel]     *)
(* directly, since [exec] calls [dev_read]/[dev_write]/[virtio_*] itself -- *)
(* and NOT yet a fact about [prim_step].  Closing that is the converse      *)
(* [HartBlock.v]'s header defers to "the language's own functional          *)
(* interpreter (the reflective stepper)"; when it lands, every test below   *)
(* is restated over [rtc erased_step] without changing a test.              *)
(*                                                                         *)
(* THE ABI IS tools/vtest/abi.h.  The constants below must match it, and    *)
(* so must tools/vtest/vtest.py's.                                          *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions list.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvExec VirtioModel DevModel ColdBoot.
(* EXPORT the language and the device schedule: a test names [mstate] and may
   name an [sitem], so [Require Import VTest] should be all it needs. *)
Require Export RiscvLang VSched.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The ABI (tools/vtest/abi.h).                                         *)
(* ---------------------------------------------------------------------- *)

Definition text_base   : Z := 0x80000000.
Definition stack_base  : Z := 0x80090000.  Definition stack_size  : nat := 4096.
Definition result_base : Z := 0x80100000.  Definition result_size : nat := 4096.
Definition dma_base    : Z := 0x80200000.  Definition dma_size    : nat := 8192.
Definition done_magic  : Z := 0x444f4e45.

(* ---------------------------------------------------------------------- *)
(* 2. The machine a test starts from.                                      *)
(*                                                                         *)
(*    Registers are ColdBoot's -- the model's OWN reset chain, run by       *)
(*    [exec] and tied to the semantics by [ColdBoot.cold_boot_run]; devices *)
(*    are [dev0_state], power-on.  Memory is the loaded image plus the      *)
(*    three zero-filled regions of abi.h, and NOTHING ELSE: the map is      *)
(*    finite, so an access outside them is stuck and the test fails loudly  *)
(*    rather than reading a zero QEMU would also have given.                *)
(* ---------------------------------------------------------------------- *)

Definition load_bytes (base : Z) (bs : list Z) : gmap Arch.pa (bv 8) :=
  list_to_map ((fun ib => (SailStdpp.Values.mword_of_int (base + Z.of_nat ib.1),
                           Z_to_bv 8 ib.2)) <$> imap pair bs).

Definition zeros (base : Z) (n : nat) : gmap Arch.pa (bv 8) :=
  load_bytes base (replicate n 0).

(* THE ZERO REGIONS ARE PER-TEST, and that is a performance decision, not a
   tidiness one: building the byte map dominates a test's cost.  Every entry
   is a [gmap] insert whose key is a [bv 64], i.e. a ~64-level trie descent,
   so the map build is linear in the DECLARED bytes and utterly independent
   of how many instructions the test runs.  Measured on core_smoke (29
   instructions): 24,696 entries = 20 s to build, versus 0.5 s to read the
   whole result region back and well under a second to run the program.  So
   a test declares the regions it USES and nothing more. *)
Definition region : Type := (Z * nat)%type.

Definition mem_of (text : list Z) (rs : list region) : gmap Arch.pa (bv 8) :=
  foldl (fun m r => m ∪ zeros r.1 r.2) (load_bytes text_base text) rs.

(* what a test that touches no device needs *)
Definition std_regions : list region :=
  [(stack_base, stack_size); (result_base, result_size)].

(* ...and what a test that drives the disk needs on top: the virtqueue and
   its data buffers *)
Definition dma_regions : list region :=
  std_regions ++ [(dma_base, dma_size)].

(* The device fabric a test starts from is [DevModel.dev0_state] -- power-on:
   FIFOs empty, PLIC masked, virtio reset, disk blank -- or, for a test that
   reads a sector it did not write, [VSched.dev_of img] with a seeded image.
   [VSched.dev_of_empty] is the proof the two agree at the blank image. *)
Definition start_with (text : list Z) (rs : list region) : mstate :=
  MState (ColdBoot.cold_regs (SailStdpp.Values.mword_of_int 0))
         (mem_of text rs) dev0_state.

Definition start_disk (text : list Z) (rs : list region)
    (img : gmap Z (bv 8)) : mstate :=
  MState (ColdBoot.cold_regs (SailStdpp.Values.mword_of_int 0))
         (mem_of text rs) (dev_of img).

Definition start     (text : list Z) : mstate := start_with text std_regions.
Definition start_dma (text : list Z) : mstate := start_with text dma_regions.

(* ---------------------------------------------------------------------- *)
(* 3. Stepping.                                                            *)
(*                                                                         *)
(*    One instruction, then every enabled device action ([VSched.settle],   *)
(*    the eager default).  A test that is ABOUT interleaving uses           *)
(*    [VSched.srun] with an explicit [sitem] list instead, and closes with  *)
(*    [result_of] on its result just the same.                              *)
(* ---------------------------------------------------------------------- *)

Definition dev_fuel : nat := 64.

Definition flag_set (s : mstate) : bool :=
  match read_bytes (mem s) (SailStdpp.Values.mword_of_int result_base) 4 with
  | Some w => bv_unsigned w =? done_magic
  | None => false
  end.

(* Run until the guest publishes its result, or the budget runs out.  [None]
   is a FAILED test either way -- a stuck machine and an exhausted budget are
   both "the model did not do what QEMU did" -- and [budget_left] tells them
   apart. *)
Fixpoint run_until (n : nat) (s : mstate) : option mstate :=
  if flag_set s then Some s else
  match n with
  | 0%nat => None
  | S n' => match exec (riscv_step false) s with
            | Some (_, s') => run_until n' (settle dev_fuel s')
            | None => None
            end
  end.

(* how much of the budget was left -- the diagnostic that tells "the budget
   was too small" apart from "the machine got stuck" *)
Fixpoint budget_left (n : nat) (s : mstate) : nat :=
  if flag_set s then n else
  match n with
  | 0%nat => 0%nat
  | S n' => match exec (riscv_step false) s with
            | Some (_, s') => budget_left n' (settle dev_fuel s')
            | None => 0%nat
            end
  end.

(* ---------------------------------------------------------------------- *)
(* 4. The observations, in the same currency vtest.py captures them.       *)
(*    A byte the map does not hold reads as -1, which no real byte can be,  *)
(*    so "the model never wrote here" is visible rather than silently zero. *)
(* ---------------------------------------------------------------------- *)

Definition peek_mem (m : gmap Arch.pa (bv 8)) (base : Z) (n : nat) : list Z :=
  (fun j => match m !! (SailStdpp.Values.mword_of_int (base + Z.of_nat j)) with
            | Some b => bv_unsigned b
            | None => -1
            end) <$> seq 0 n.

Definition result_of (o : option mstate) : list Z :=
  match o with
  | None => []
  | Some s => peek_mem (mem s) result_base result_size
  end.

(* the disk, per 512-byte sector, in the shape [<name>_qemu_disk] carries *)
Definition sector_of (o : option mstate) (i : Z) : list Z :=
  match o with
  | None => []
  | Some s => bv_unsigned <$>
      disk_read (v_disk (dvirtio (mdev s))) (i * virtio_sector_size) 512
  end.

Definition disk_of_run (o : option mstate) (is : list Z) : list (Z * list Z) :=
  (fun i => (i, sector_of o i)) <$> is.

(* ---------------------------------------------------------------------- *)
(* 4b. Reading ONE FIELD out of either side.                               *)
(*                                                                         *)
(*     [result_of = <capture>] is the right check when a test's whole       *)
(*     result should agree.  Once a test records several independent        *)
(*     observations and some of them are KNOWN to diverge, the whole-region *)
(*     equation can only be red or hidden, and neither is useful.  So a     *)
(*     test compares field by field: the fields that agree get an equation, *)
(*     and each field that does not gets a DISEQUALITY plus a comment       *)
(*     classifying it.  A [<>] lemma is green today and goes RED the day    *)
(*     someone makes the model match -- which is exactly when the test file *)
(*     should be revisited.                                                 *)
(* ---------------------------------------------------------------------- *)

Definition le_word (bs : list Z) : Z :=
  foldr (fun b acc => acc * 256 + b) 0 (take 4 bs).

(* a 4-byte little-endian word at [off] in the model's result region *)
Definition res_word (o : option mstate) (off : nat) : Z :=
  le_word (drop off (result_of o)).

(* ...and the same word in what vtest.py captured from QEMU *)
Definition cap_word (cap : list Z) (off : nat) : Z := le_word (drop off cap).

Definition res_bytes (o : option mstate) (off n : nat) : list Z :=
  take n (drop off (result_of o)).
Definition cap_bytes (cap : list Z) (off n : nat) : list Z :=
  take n (drop off cap).

(* the sectors a run changed, in the shape [<name>_qemu_disk] carries, so a
   test can compare the two disks with one equation *)
Definition disk_like (o : option mstate) (cap : list (Z * list Z))
  : list (Z * list Z) := disk_of_run o (fst <$> cap).

(* ---------------------------------------------------------------------- *)
(* 5. The tactic every test closes with.                                   *)
(*    [vm_cast_no_check] and not [vm_compute; reflexivity]: the latter      *)
(*    evaluates twice (once in the tactic, once in the kernel).  Measured   *)
(*    on a 1600-instruction test: 44 s versus 23 s.                         *)
(* ---------------------------------------------------------------------- *)

Ltac solve_vtest rhs := vm_cast_no_check (eq_refl rhs).
