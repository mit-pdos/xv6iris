(* ====================================================================== *)
(* VRun.v -- A TEST, A RUN OF IT, AND WHAT IT MEANS FOR A RUN TO PASS.     *)
(*                                                                         *)
(* THREE THINGS, and keeping them apart is the point of this file.         *)
(*                                                                         *)
(*   A TEST is a PROGRAM ON A MACHINE: the image, the hart it runs on, and *)
(*   the memory regions that are mapped.  Those three fix an initial       *)
(*   state, [test_start] is the only way to build one, and every claim     *)
(*   below is about THAT state -- so nothing can quietly substitute a      *)
(*   different machine.                                                    *)
(*                                                                         *)
(*   A RUN OF A TEST is a MEASUREMENT of it: the observations one platform *)
(*   produced, and nothing else.  It depends on a test -- [TEST_RUN T] --  *)
(*   and cannot be stated without one.  Everything that is not a           *)
(*   measurement has been pushed out of it: the machine and the input are  *)
(*   the TEST's (the experiment, not its result), and the resolutions of   *)
(*   the model's own nondeterminism are WITNESSES, so they live in the     *)
(*   proof and appear in no statement.                                     *)
(*                                                                         *)
(*   THE MODEL'S BEHAVIOUR IS NEITHER, and used to be a FIELD of the run   *)
(*   ([outcome : model_outcome]).  That is why the top-level theorem said  *)
(*   nothing: [run_passes observed outcome] related two data, named no     *)
(*   program, no state and no step relation, and on the stuck branch was   *)
(*   literally [True].  It is now QUANTIFIED OVER, in a proposition that   *)
(*   names the test's own initial state.                                   *)
(*                                                                         *)
(* THE JUDGEMENT is unchanged and one-directional: is what the real        *)
(* machine did an execution our model ALLOWS?  A run passes when           *)
(*                                                                         *)
(*   - the model, from the test's initial state, EXHIBITS every            *)
(*     observation the platform produced -- each by SOME execution, since  *)
(*     several observations mean the hardware itself has several legal     *)
(*     executions and they need not come from one resolution; or           *)
(*                                                                         *)
(*   - the model reaches a state it has NO TRANSITION FROM.  That is a     *)
(*     pass, and a real one: a state the relation cannot leave is a state  *)
(*     no proof over the model can reach, so nothing unsound can be        *)
(*     derived there.  It costs REACH, not soundness.  What it is not is   *)
(*     content-free, so it is stated -- [reaches_no_step] -- as a fact     *)
(*     about [run] at a state THIS test's execution arrives at.            *)
(*                                                                         *)
(* STUCK MEANS [ENoStep], NOT [VStuck].  [exec] also declines on           *)
(* [Interface.Choose] -- the Sail monad's nondeterminism -- where the      *)
(* RELATION does have transitions and the interpreter merely will not pick *)
(* one, and "our proofs can never run into this case" is FALSE there.      *)
(* [VExecStuck.exec_r_no_step] is what makes [ENoStep] mean the relation;  *)
(* [EChoice] is a GAP, and no pass.                                        *)
(* ====================================================================== *)
From Stdlib Require Import List ZArith String Bool.
From stdpp Require Import base list gmap bitvector.definitions.
Import ListNotations.
From VTest Require Import VTest.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. THE TEST.                                                            *)
(*                                                                         *)
(*    [text], [hart] and [regions] are not labels, they are the machine:   *)
(*                                                                         *)
(*    - [text] is the image, loaded at [text_base].                        *)
(*    - [hart] reaches the program.  [ColdBoot.cold_regs] is parametric in *)
(*      it, and the boot chain does exactly two things with it -- stores   *)
(*      it, so [csrr mhartid] reads it, and copies it into a0 -- which is  *)
(*      what makes [csrr mhartid] the way a program tells harts apart.     *)
(*      Run the board's image from hart 0 and its prologue computes stack  *)
(*      slot -2, [sp] lands two pages below [stack_base], and the first    *)
(*      push is an undeclared address: a stuck machine that looks exactly  *)
(*      like a genuine finding about memory.                               *)
(*    - [regions] IS the memory.  [mem_of] gives the image plus the        *)
(*      declared zero regions and NOTHING else; the map is finite, so an   *)
(*      access outside them is stuck.  A different region list is a        *)
(*      different machine, and can turn an agreeing run into a stuck one.  *)
(*                                                                         *)
(*    [name] and [platform] are labels -- for the table, not for any claim *)
(*    -- and are grouped apart here so nobody mistakes them for content.   *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(* 0. WHAT ONE EXECUTION PRODUCED, on every channel a platform has.        *)
(*                                                                         *)
(*    A test has three outputs and the suite used to judge one.  The other *)
(*    two were CAPTURED and compared against nothing: the bytes that left  *)
(*    the UART, and the disk sectors the run changed.                      *)
(*                                                                         *)
(*    [o_disk] is THE WHOLE DISK the run ended with, by absolute sector    *)
(*    number -- the same shape as the test's [disk_init], because it is    *)
(*    the same kind of thing.  Not a diff: "the sectors that changed" is a *)
(*    relative description, and a claim about it can never say what the    *)
(*    sectors it does not mention hold.                                    *)
(* ---------------------------------------------------------------------- *)

Record observation := Obs {
  o_result : list Z;              (* the whole result region, untrimmed   *)
  o_uart   : list Z;              (* the bytes that left the port on SOUT *)
  o_disk   : list (Z * list Z);   (* the disk it ended with, by sector    *)
}.

(* A DISK, from a finite description of its sectors.  [VSched.disk_of] is
   the total function a finite image denotes -- zero off it -- so this is
   the same object the device holds, and an [mstate]'s disk can be compared
   with it directly.

   [VirtioModel.v_disk] is a TOTAL function [Z -> bv 8], so that comparison
   is an equality of FUNCTIONS and not a computation.  That is the right
   shape and not a problem: the criterion is that the claim be PROVABLE,
   and the model carries the pointwise lemmas it needs ([disk_write_in],
   [disk_write_out]).  It is also what makes the claim COMPLETE -- it says
   what every byte of the disk holds, so a sector the model wrote and the
   platform did not is a violation, which no check over named sectors
   could see. *)
Definition img_of_sectors (ss : list (Z * list Z)) : gmap Z (bv 8) :=
  foldl (fun m p =>
           m ∪ list_to_map
                 (imap (fun j b => (fst p * virtio_sector_size + Z.of_nat j,
                                    Z_to_bv 8 b)) (snd p)))
        ∅ ss.

Definition disk_of_sectors (ss : list (Z * list Z)) : Z -> bv 8 :=
  disk_of (img_of_sectors ss).

Definition disk_of_state (s : mstate) : Z -> bv 8 :=
  v_disk (dvirtio (mdev s)).

Module Type TEST.
  (* labels *)
  Parameter name     : string.
  Parameter platform : string.
  (* the machine *)
  Parameter text     : list Z.
  Parameter hart     : Z.
  Parameter regions  : list region.
  (* WHAT IT IS GIVEN.  The bytes the host types are an INPUT to the
     experiment, not a result of it, and they must be PINNED: if the model
     were free to choose them, "the model can produce this output for SOME
     input" is what would be proved, which for a receiving test is no check
     at all.  The UART is the only input a test has; when there is another
     it gets its own field rather than being folded in here. *)
  Parameter uart_input : list Z.
  (* ...AND THE DISK IT STARTS FROM, by absolute sector number.  Blank for
     every test written so far, and unrepresentable until now: a test that
     reads a sector it did not itself write could not be stated at all. *)
  Parameter disk_init  : list (Z * list Z).
End TEST.

(* THE ONE INITIAL STATE OF A TEST.  Every proposition below is about this
   state, and no run may build another. *)
Definition test_start (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) : mstate :=
  MState (ColdBoot.cold_regs (SailStdpp.Values.mword_of_int hart))
         (mem_of text rs) (dev_of (img_of_sectors disk_init)).

(* ...AND ITS INPUT, as the model receives it.  A byte ARRIVING is a schedule
   choice ([VSched.SUartRx]), not something the program performs, so the
   input is delivered as a prefix before the program is stepped. *)
Definition uart_pre (bs : list Z) : list sitem :=
  List.map SUartRx bs.

(* ---------------------------------------------------------------------- *)
(* 2. Running the model once, keeping the state at every ending.           *)
(*                                                                         *)
(*    [VTest] has [run_until], [run_status], [stuck_why] and [budget_left] *)
(*    as four separate traversals; asking all four costs four runs of the  *)
(*    program, and a run is seconds to a minute.  This is one traversal.   *)
(*                                                                         *)
(*    EVERY ARM CARRIES ITS STATE, the stuck one included.  Without that,  *)
(*    "the model has no transition" can only be said of SOME state -- the  *)
(*    shape [VTest.stuck_why_no_step] is stuck with, and nearly vacuous,   *)
(*    since any junk state with no transition witnesses it.  With it, the  *)
(*    claim is about a state this test's own execution reaches.            *)
(*                                                                         *)
(*    [pick] is which in-flight virtio request the disk answers.  It was a *)
(*    global default ([lowest_head]) baked into [settle] and visible in no *)
(*    run -- yet it resolves the model's nondeterminism, and for a case    *)
(*    whose subject IS the completion order it is the whole content of the *)
(*    run.  It is a parameter here, and an argument to the decision        *)
(*    procedure -- never a field, because the claim is that the model      *)
(*    ADMITS the outcome, not that it admits it at one chosen order.       *)
(* ---------------------------------------------------------------------- *)

Inductive eresult :=
  | RDone   (s : mstate)                (* published its result            *)
  | RStuck  (s : mstate) (why : estuck) (* [exec] would not step, and why  *)
  | RBudget (s : mstate).               (* still running when time ran out *)

Fixpoint eval_run_at (pick : virtio_state -> option Z) (tick : bool)
    (n : nat) (s : mstate) : eresult :=
  if flag_set s then RDone s else
  match n with
  | 0%nat => RBudget s
  | S n' => match exec_r (riscv_step tick) s with
            | inl (_, s') => eval_run_at pick tick n' (settle_at pick dev_fuel s')
            | inr e => RStuck s e
            end
  end.

(* The two unfolding equations, so no proof below has to [cbn]: any [cbn]
   here also unfolds [riscv_step] into the whole monadic term, and the
   [destruct] then has nothing syntactically matching
   [exec_r (riscv_step tick) s] to abstract. *)
Lemma eval_run_at_O (pick : virtio_state -> option Z) (tick : bool)
    (s : mstate) :
  eval_run_at pick tick 0 s = if flag_set s then RDone s else RBudget s.
Proof. cbn [eval_run_at]. destruct (flag_set s); reflexivity. Qed.

Lemma eval_run_at_S (pick : virtio_state -> option Z) (tick : bool)
    (n : nat) (s : mstate) :
  eval_run_at pick tick (S n) s =
    (if flag_set s then RDone s
     else match exec_r (riscv_step tick) s with
          | inl (_, s') => eval_run_at pick tick n (settle_at pick dev_fuel s')
          | inr e => RStuck s e
          end).
Proof. reflexivity. Qed.

(* what a platform observes, on the model side *)
Definition result_region (s : mstate) : list Z :=
  peek_mem (mem s) result_base result_size.

(* ---------------------------------------------------------------------- *)
(* 3. THE TWO WAYS A RUN CAN PASS, both stated about the test's state.     *)
(*                                                                         *)
(*    [pre] is the TEST's input, delivered before the program runs (see    *)
(*    [test_pre]).  It is PINNED and never existential: a model free to    *)
(*    choose its own input proves nothing about a receiving test.  The     *)
(*    empty input is the ordinary case: [srun [] s = Some s].              *)
(* ---------------------------------------------------------------------- *)

(* "the model, from [s0], has an execution that publishes [o]" -- the WHOLE
   result region, nothing trimmed, so a difference cannot hide in the tail.

   THERE IS NO PROJECTION.  A test used to be able to name the words it
   wanted compared, for the honest reason that a raw [mtime] or a cycle
   counter differs between two runs of the SAME machine.  But a value that
   varies is a value the program should not have PUBLISHED: the result
   region is the test's answer, and the fix for a field that cannot agree
   is to stop writing it, not to agree to ignore it.  An arbitrary
   projection also let a test weaken its own claim invisibly, and hid from
   the theorem which bytes were being compared. *)
Definition exhibits (pre : list sitem) (pick : virtio_state -> option Z)
    (tick : bool) (budget : nat) (s0 : mstate) (o : observation) : Prop :=
  exists s1 s,
    srun pre s0 = Some s1
    /\ eval_run_at pick tick budget s1 = RDone s
    /\ result_region s = o.(o_result)
    /\ serial_of (Some s) = o.(o_uart)
    /\ disk_of_state s = disk_of_sectors o.(o_disk).

(* "the model, from [s0], reaches a state THE RELATION cannot step from".
   [run] is RiscvModelLang's relation and not the interpreter: that is what
   [VExecStuck.exec_r_no_step] buys, and it is the only reason a stuck run
   is admissible at all. *)
Definition reaches_no_step (pre : list sitem)
    (pick : virtio_state -> option Z) (tick : bool) (budget : nat)
    (s0 : mstate) : Prop :=
  exists s1 s, srun pre s0 = Some s1
               /\ eval_run_at pick tick budget s1 = RStuck s ENoStep
               /\ forall x s', ~ run (riscv_step tick) s x s'.

Lemma eval_run_at_stuck (pick : virtio_state -> option Z) (tick : bool)
    (n : nat) : forall s0 s,
  eval_run_at pick tick n s0 = RStuck s ENoStep ->
  exec_r (riscv_step tick) s = inr ENoStep.
Proof.
  induction n as [|n IH]; intros s0 s H.
  - rewrite eval_run_at_O in H. destruct (flag_set s0); discriminate.
  - rewrite eval_run_at_S in H. destruct (flag_set s0); [discriminate|].
    destruct (exec_r (riscv_step tick) s0) as [[u s1]|e] eqn:He.
    + exact (IH _ _ H).
    + destruct e; [|discriminate]. inversion H; subst. exact He.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. A RUN OF A TEST, and the theorem.                                    *)
(*                                                                         *)
(*    A run has no [outcome].  What the model does is not data the run     *)
(*    carries; it is what [run_passes] quantifies over, out of the initial *)
(*    state [T] fixes -- and [start] is a DEFINITION here, not a           *)
(*    parameter, so a run of [T] has [T]'s machine by construction.        *)
(*                                                                         *)
(*    [picks], [tick] and [budget] are fields because a proof has to name  *)
(*    the witnesses it computed with, but NONE of them appears in the      *)
(*    theorem: [run_passes] quantifies them existentially.  What is        *)
(*    claimed is "the model has such an execution", not "it has one within *)
(*    2000 steps with the clock held still and the disk answering its      *)
(*    lowest in-flight head".                                              *)
(* ---------------------------------------------------------------------- *)

Module Type TEST_RUN (T : TEST).
  (* WHAT THE PLATFORM PRODUCED, and nothing else -- a run is a measurement.
     Several observations mean the hardware itself has several legal
     executions here, and the model must have each.

     What is NOT here: the machine and the input (those are [T]'s, the
     experiment rather than its result), and the resolutions of the MODEL's
     own nondeterminism -- how long to run, whether the clock ticks, which
     in-flight request the disk answers.  Those are witnesses for the
     existentials in [run_passes], so they live in the PROOF, as arguments
     to [run_passes_b_sound], and appear in no statement. *)
  Parameter observed : list observation.
End TEST_RUN.

(* THE THEOREM, over the test's own initial state. *)
Definition run_passes (hart : Z) (text : list Z) (rs : list region)
    (uart_input : list Z) (disk_init : list (Z * list Z))
    (observed : list observation) : Prop :=
  let s0 := test_start hart text rs disk_init in
  (forall o, In o observed ->
     exists pick tick budget,
       exhibits (uart_pre uart_input) pick tick budget s0 o)
  \/ (exists pick tick budget,
       reaches_no_step (uart_pre uart_input) pick tick budget s0).

Module Type TEST_PASSES (T : TEST) (R : TEST_RUN T).
  Axiom passes :
    run_passes T.hart T.text T.regions T.uart_input T.disk_init R.observed.
End TEST_PASSES.

(* ---------------------------------------------------------------------- *)
(* 5. WHAT A PROOF LOOKS LIKE.                                             *)
(*                                                                         *)
(*    [result_region] and [serial_of] are lists and settle by computation, *)
(*    as they always did.  The disk clause is an equality of FUNCTIONS and *)
(*    does not: it is discharged from [VirtioModel]'s pointwise lemmas.    *)
(*    A test that touches no disk has [o_disk = disk_init], so the clause  *)
(*    says the disk did not move -- itself worth saying, and for a blank   *)
(*    start it is [eq_refl].                                               *)
(* ---------------------------------------------------------------------- *)
