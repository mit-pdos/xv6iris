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
(* [exec_r] and [exec_r_no_step]: what a stuck run's stuckness MEANS. *)
Require Export VExecStuck.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The ABI (tools/vtest/abi.h).                                         *)
(* ---------------------------------------------------------------------- *)

Definition text_base   : Z := 0x80000000.
Definition stack_base  : Z := 0x80090000.  Definition stack_size  : nat := 4096.
Definition result_base : Z := 0x80100000.  Definition result_size : nat := 4096.
Definition dma_base    : Z := 0x80200000.  Definition dma_size    : nat := 8192.
Definition pt_base     : Z := 0x80300000.  Definition pt_size     : nat := 16384.
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

(* ...and what a test that turns PAGING on needs: four 4 KB-aligned pages for
   an Sv39 root and a full three-level walk.  The walk reads these through
   the PHYSICAL map, so they have to be declared like any other memory --
   an undeclared PTE address makes the walk itself stuck. *)
Definition pt_regions : list region :=
  std_regions ++ [(pt_base, pt_size)].

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
Definition start_pt  (text : list Z) : mstate := start_with text pt_regions.

(* ---------------------------------------------------------------------- *)
(* 2b. THE SAME MACHINE, ON A HART THAT IS NOT HART 0.                     *)
(*                                                                         *)
(*     [start] above bakes in hart 0, because QEMU's virt board boots hart  *)
(*     0 and every QEMU capture is of a program that ran there.  A REAL     *)
(*     BOARD NEED NOT.  The JH7110's hart 0 is a 32-bit E24 monitor core    *)
(*     that cannot execute one of these images at all, so                   *)
(*     tools/vtest/board.py runs on a U74 -- mhartid 2 -- and the image is  *)
(*     built with PRIMARY_HART=2 so that the prologue's stack slot and its  *)
(*     primary/AP branch agree with where it actually runs.                 *)
(*                                                                         *)
(*     The model side has to follow, and NOT because the model cares which  *)
(*     hart runs: [ColdBoot.cold_regs] is parametric in the hart id and the *)
(*     id is the only thing the boot chain does with it (it stores it and   *)
(*     copies it into a0), which is exactly what makes `csrr mhartid` the   *)
(*     right way for a program to tell harts apart.  It has to follow       *)
(*     because the PROGRAM reads [mhartid]: run the board's image against   *)
(*     [start] and the prologue computes slot -2, puts sp two pages below   *)
(*     STACK_BASE, and the first push is an undeclared address -- a STUCK   *)
(*     machine that looks exactly like a genuine finding about memory.      *)
(*                                                                         *)
(*     So a hardware test says [start_hart <name>_hw_primary_hart           *)
(*     <name>_hw_text], and the capture carries that hart id for it.        *)
(* ---------------------------------------------------------------------- *)

Definition start_hart_with (h : Z) (text : list Z) (rs : list region) : mstate :=
  MState (ColdBoot.cold_regs (SailStdpp.Values.mword_of_int h))
         (mem_of text rs) dev0_state.

Definition start_hart    (h : Z) (text : list Z) : mstate :=
  start_hart_with h text std_regions.
Definition start_hart_pt (h : Z) (text : list Z) : mstate :=
  start_hart_with h text pt_regions.

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
Fixpoint run_until_at (pick : virtio_state -> option Z) (n : nat)
    (s : mstate) : option mstate :=
  if flag_set s then Some s else
  match n with
  | 0%nat => None
  | S n' => match exec (riscv_step false) s with
            | Some (_, s') => run_until_at pick n' (settle_at pick dev_fuel s')
            | None => None
            end
  end.

Definition run_until (n : nat) (s : mstate) : option mstate :=
  run_until_at lowest_head n s.

(* ---------------------------------------------------------------------- *)
(* 3a. THE SAME RUN, WITH THE CLOCK TICKING.                               *)
(*                                                                         *)
(*     [run_until] above steps [riscv_step false], and that is a CHOICE of  *)
(*     the harness, not a property of the model.  [RiscvLang.mnode_step]'s  *)
(*     boundary rule is                                                    *)
(*                                                                         *)
(*       | Interface.Ret _ => exists tick : bool, m' = riscv_step tick /\ ... *)
(*                                                                         *)
(*     -- the language quantifies EXISTENTIALLY over the tick at every      *)
(*     instruction boundary, which is the sound weakening of the model      *)
(*     [loop]'s deterministic every-[plat_insns_per_tick] tick.  So an      *)
(*     execution in which [mtime] and [mcycle] advance is one the model     *)
(*     ALLOWS; the harness had simply been resolving the choice one way     *)
(*     every time and never exhibiting the other.                          *)
(*                                                                         *)
(*     THAT MATTERS FOR WHAT A TEST CLAIMS.  The suite's question is        *)
(*     one-directional -- is what the hardware did an execution the model   *)
(*     ALLOWS? -- so a hardware run with a moving clock needs a TICKING     *)
(*     witness, and reporting "the model cannot do this" off the            *)
(*     non-ticking runner alone is a statement about the runner.            *)
(*                                                                         *)
(*     Ticking at EVERY boundary is the fastest clock the language permits  *)
(*     and is what these witnesses use: the tick is free at each boundary,  *)
(*     so all-ticks is as legal as no-ticks, and it is the cheapest         *)
(*     execution to exhibit.  A test that needs a particular RATE would     *)
(*     parameterise this the way [run_until_at] parameterises the disk.     *)
(* ---------------------------------------------------------------------- *)

Fixpoint run_until_tick (n : nat) (s : mstate) : option mstate :=
  if flag_set s then Some s else
  match n with
  | 0%nat => None
  | S n' => match exec (riscv_step true) s with
            | Some (_, s') => run_until_tick n' (settle dev_fuel s')
            | None => None
            end
  end.


(* ...and the run in which a LATER request overtakes an earlier one: the same
   machine, the same program, a device that pops both requests (it can only
   pop in order) and then completes the higher head first.  Only
   [DiskOrder.v] uses it, and what it demonstrates is that the model has
   BOTH of the executions the hardware has. *)
Definition run_until_rev (n : nat) (s : mstate) : option mstate :=
  run_until_at highest_head n s.

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
(* 3b. WHY a run did not finish.                                           *)
(*                                                                         *)
(*     [run_until] answers [None] for two very different reasons, and the   *)
(*     difference is usually the point of the test.                         *)
(*                                                                         *)
(*     WHAT [VStuck] DOES AND DOES NOT MEAN.  It means [exec] -- the        *)
(*     DETERMINISTIC interpreter -- could not take a step.  It does NOT     *)
(*     mean the model has no transition, and this file used to say it did.  *)
(*     [RiscvExec.exec_run_det] runs one way only ([exec = Some] implies    *)
(*     [run]); there is NO lemma anywhere in the tree of the form           *)
(*     [exec m s = None -> no run], and there cannot be a trivial one,      *)
(*     because [exec]'s own fallback is                                     *)
(*                                                                         *)
(*       | _ => fun _ => None   (* Choose / GenericFail / Discard / ... *)  *)
(*                                                                         *)
(*     -- it bails on [Choose], which is the Sail monad's NONDETERMINISM.   *)
(*     So [VStuck] covers both "the model really has no step here" (an      *)
(*     undecoded MMIO offset, an access outside the declared regions) and   *)
(*     "the model made a choice this interpreter cannot resolve", and the   *)
(*     harness cannot tell them apart.                                     *)
(*                                                                         *)
(*     A test may therefore state [VStuck] as a FACT ABOUT [exec], which is *)
(*     what it is, and must not report it as "the model cannot":            *)
(*                                                                         *)
(*       Lemma foo_model_stuck : run_status N (start_dma foo_text) = VStuck.*)
(*       Lemma foo_stuck_at : stuck_pc N (start_dma foo_text) = 0x800000ab. *)
(*                                                                         *)
(*     A budget that merely ran out is a broken test, not a finding, and    *)
(*     reads [VBudget] instead.  [stuck_pc] names the instruction, so the   *)
(*     test says WHICH access the model refuses rather than only that one   *)
(*     of them did.                                                        *)
(* ---------------------------------------------------------------------- *)

Inductive vstatus := VDone | VStuck | VBudget.

Fixpoint run_status (n : nat) (s : mstate) : vstatus :=
  if flag_set s then VDone else
  match n with
  | 0%nat => VBudget
  | S n' => match exec (riscv_step false) s with
            | Some (_, s') => run_status n' (settle dev_fuel s')
            | None => VStuck
            end
  end.

(* ...and the same, on the TICKING branch of the boundary's [exists tick] --
   see section 3a. *)
Fixpoint run_status_tick (n : nat) (s : mstate) : vstatus :=
  if flag_set s then VDone else
  match n with
  | 0%nat => VBudget
  | S n' => match exec (riscv_step true) s with
            | Some (_, s') => run_status_tick n' (settle dev_fuel s')
            | None => VStuck
            end
  end.

(* ---------------------------------------------------------------------- *)
(* 3c. WHY it was stuck, which [VStuck] alone does not say.                *)
(*                                                                         *)
(*     [VStuck] means [exec] would not step, and [exec] declines on a       *)
(*     [Choose] (nondeterminism) exactly as it declines where the relation  *)
(*     really is stuck.  [VExecStuck.exec_r] splits the two, so a test can  *)
(*     ask which it got -- and [ENoStep] is worth something, because        *)
(*                                                                         *)
(*       exec_r_no_step : exec_r m s = inr ENoStep ->                       *)
(*                        forall x s', ~ run m s x s'                       *)
(*                                                                         *)
(*     is a theorem about the RELATION.  A test that reports [ENoStep] may  *)
(*     say "the model has no transition here" and mean it; one that reports *)
(*     [EChoice] has learned only that this interpreter would not choose.   *)
(* ---------------------------------------------------------------------- *)

Fixpoint stuck_why (n : nat) (s : mstate) : option estuck :=
  if flag_set s then None else
  match n with
  | 0%nat => None
  | S n' => match exec_r (riscv_step false) s with
            | inl (_, s') => stuck_why n' (settle dev_fuel s')
            | inr e => Some e
            end
  end.

(* The two unfolding equations, so the proof below never has to [simpl]:
   any [simpl] here also unfolds [riscv_step] into the whole monadic term,
   and the [destruct] then has nothing syntactically matching
   [exec_r (riscv_step false) s] to abstract. *)
Lemma stuck_why_O (s : mstate) : stuck_why 0 s = None.
Proof. cbn [stuck_why]. destruct (flag_set s); reflexivity. Qed.

Lemma stuck_why_S (n : nat) (s : mstate) :
  stuck_why (S n) s =
    (if flag_set s then None
     else match exec_r (riscv_step false) s with
          | inl (_, s') => stuck_why n (settle dev_fuel s')
          | inr e => Some e
          end).
Proof. reflexivity. Qed.

(* ...AND WHAT [ENoStep] BUYS: a state the run reaches at which the MODEL
   -- the relation, not the interpreter -- has no transition at all.  This
   is the statement a test could not make before, and the reason a bare
   [VStuck] was uninterpretable. *)
Lemma stuck_why_no_step (n : nat) (s : mstate) :
  stuck_why n s = Some ENoStep ->
  exists s0 : mstate, forall x s', ~ run (riscv_step false) s0 x s'.
Proof.
  revert s. induction n as [|n IH]; intros s H.
  - rewrite stuck_why_O in H. discriminate.
  - rewrite stuck_why_S in H.
    destruct (flag_set s); [discriminate|].
    destruct (exec_r (riscv_step false) s) as [[u s']|e] eqn:He.
    + exact (IH _ H).
    + destruct e; [|discriminate].
      exists s. exact (exec_r_no_step _ _ He).
Qed.

(* the pc the machine was stuck AT, or -1 if it did not get stuck *)
Fixpoint stuck_pc (n : nat) (s : mstate) : Z :=
  if flag_set s then -1 else
  match n with
  | 0%nat => -1
  | S n' => match exec (riscv_step false) s with
            | Some (_, s') => stuck_pc n' (settle dev_fuel s')
            | None => bv_unsigned (register_lookup (R_bitvector_64 PC) (sregs s))
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

(* WHAT THE HOST RECEIVED, in the same currency vtest.py captures from QEMU's
   serial file: [u_wire], the bytes that actually left the port on SOUT.
   NOT [uart_acc] ([u_out ++ u_tx], every byte the device has ACCEPTED),
   which is the transmitter's business and not the host's -- under LOOPBACK
   an accepted byte goes to this UART's own receiver and the host never sees
   it, which is exactly what UartLoop.v checks.  The two agree on every
   other test: [VSched.settle] drains the FIFO after every instruction, so
   nothing is left in flight when the guest publishes its result. *)
Definition serial_of (o : option mstate) : list Z :=
  match o with
  | None => []
  | Some s => bv_unsigned <$> u_wire (duart (mdev s))
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
