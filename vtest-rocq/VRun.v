(* ====================================================================== *)
(* VRun.v -- WHAT A TEST RUN IS, AND WHAT IT MEANS FOR ONE TO PASS.        *)
(*                                                                         *)
(* The suite has ONE set of test CASES (tools/vtest/tests/*.S).  Each case  *)
(* declares which PLATFORMS it is meaningful on, and executing a case on a  *)
(* platform produces a test RUN.  So a case yields zero, one or two runs,   *)
(* and every run -- whichever platform it came from -- is the same kind of  *)
(* object and is judged by the same theorem.                               *)
(*                                                                         *)
(* THE JUDGEMENT.  The suite's question is one-directional: is what the     *)
(* real machine did an execution our model ALLOWS?  So a run PASSES when    *)
(* either                                                                   *)
(*                                                                         *)
(*   - the model executes and exhibits every outcome the platform observed  *)
(*     (if the platform showed several, because the hardware itself has     *)
(*     more than one legal execution, the model must have each), OR         *)
(*                                                                         *)
(*   - the model is STUCK -- and that is a pass too, because a state the    *)
(*     model has no transition from is a state no proof over the model can  *)
(*     ever reach.  It costs REACH, not soundness.                          *)
(*                                                                         *)
(* STUCK MEANS [ENoStep], NOT [VStuck].  This is the one place the          *)
(* distinction has teeth.  [exec] also declines on [Interface.Choose] --    *)
(* the Sail monad's nondeterminism -- where the RELATION does have          *)
(* transitions and the interpreter merely will not pick one, and "our       *)
(* proofs can never run into this case" is FALSE there.  [VExecStuck]'s     *)
(* [exec_r] separates the two and [exec_r_no_step] proves that [ENoStep]    *)
(* really is "no transition", so only [ENoStep] is admitted as a pass.      *)
(* [EChoice] is [MUnknown]: not a pass, not a refutation, a gap.            *)
(* ====================================================================== *)
From Stdlib Require Import List ZArith String.
From stdpp Require Import base list.
Import ListNotations.
Require Import VTest.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Running the model once, keeping everything the judgement needs.      *)
(*                                                                         *)
(*    [VTest] has [run_until], [run_status], [stuck_why] and [budget_left]  *)
(*    as four separate traversals; asking all four costs four runs of the   *)
(*    program, and a run is seconds to a minute.  This is one traversal     *)
(*    that answers all of them.                                            *)
(*                                                                         *)
(*    [tick] is the boundary's [exists tick : bool] -- see VTest section    *)
(*    3a.  A case whose subject is elapsed time asks for [true]; everything *)
(*    else takes the [false] default, which is a DEFAULT and not a limit.   *)
(* ---------------------------------------------------------------------- *)

Inductive eresult :=
  | RDone   (s : mstate)      (* published its result           *)
  | RStuck  (why : estuck)    (* [exec] would not step, and why *)
  | RBudget.                  (* still running when time ran out *)

Fixpoint eval_run (tick : bool) (n : nat) (s : mstate) : eresult :=
  if flag_set s then RDone s else
  match n with
  | 0%nat => RBudget
  | S n' => match exec_r (riscv_step tick) s with
            | inl (_, s') => eval_run tick n' (settle dev_fuel s')
            | inr e => RStuck e
            end
  end.

(* ---------------------------------------------------------------------- *)
(* 2. What the model did, in the currency a platform observation is in.    *)
(* ---------------------------------------------------------------------- *)

Inductive model_outcome :=
  | MDone    (exhibited : list (list Z))  (* the observations it exhibits *)
  | MNoStep                               (* no transition: a PASS        *)
  | MUnknown                              (* a [Choose]: a GAP            *)
  | MBudget.                              (* did not finish               *)

Definition outcome_of_stuck (e : estuck) : model_outcome :=
  match e with ENoStep => MNoStep | EChoice => MUnknown end.

(* ---------------------------------------------------------------------- *)
(* 3. THE MODULE TYPE: what a test run IS.                                 *)
(*                                                                         *)
(*    Deliberately small, and deliberately in PROJECTED form on both        *)
(*    sides.  A projection is needed because several cases observe fields   *)
(*    that legitimately differ between two runs of the SAME machine -- the  *)
(*    cycle counters, a raw [mtime], the image-dependent [mtvec], the hart  *)
(*    id -- and demanding those agree would be demanding the wrong thing.   *)
(*    The projection is part of the run and therefore visible; a run that   *)
(*    projects away too much is a run whose module says so.                *)
(* ---------------------------------------------------------------------- *)

Module Type TEST_RUN.
  (* which case, and which platform executed it *)
  Parameter case      : string.
  Parameter platform  : string.
  (* every DISTINCT projected observation the platform produced.  More than
     one means the platform itself has more than one legal execution here. *)
  Parameter observed  : list (list Z).
  (* what the model did, in the same projected currency *)
  Parameter outcome   : model_outcome.
End TEST_RUN.

(* ---------------------------------------------------------------------- *)
(* 4. THE THEOREM, parametric in the run.                                  *)
(* ---------------------------------------------------------------------- *)

Definition run_passes (observed : list (list Z)) (outcome : model_outcome)
  : Prop :=
  match outcome with
  | MNoStep => True
  | MDone exhibited => forall o, o ∈ observed -> o ∈ exhibited
  | MUnknown => False
  | MBudget => False
  end.

Module Type TEST_PASSES (R : TEST_RUN).
  Axiom passes : run_passes R.observed R.outcome.
End TEST_PASSES.

(* ...and its decision procedure, so that every instantiation's proof is
   the same one line.  [run_passes_b] is what a run's [Pass] module
   computes; [run_passes_b_sound] is why computing it is enough. *)

Definition run_passes_b (observed : list (list Z)) (outcome : model_outcome)
  : bool :=
  match outcome with
  | MNoStep => true
  | MDone exhibited => forallb (fun o => bool_decide (o ∈ exhibited)) observed
  | MUnknown => false
  | MBudget => false
  end.

Lemma run_passes_b_sound (observed : list (list Z)) (outcome : model_outcome) :
  run_passes_b observed outcome = true -> run_passes observed outcome.
Proof.
  destruct outcome as [exhibited| | |]; simpl; try discriminate; [|done].
  intros Hall o Ho.
  rewrite forallb_forall in Hall.
  apply elem_of_list_In in Ho.
  specialize (Hall o Ho).
  by apply bool_decide_eq_true in Hall.
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. THE BUILDER for a single-hart run, which is most of them.            *)
(*                                                                         *)
(*    [outcome] is COMPUTED here rather than asserted by the run's module,  *)
(*    so a run cannot claim a model execution it does not have.  That is    *)
(*    the whole reason this is a functor and not a record a generator       *)
(*    fills in.                                                            *)
(* ---------------------------------------------------------------------- *)

Module Type SINGLE_HART_CASE.
  Parameter case      : string.
  Parameter platform  : string.
  Parameter text      : list Z.       (* the image THIS platform ran *)
  Parameter hart      : Z.            (* ...on this hart             *)
  Parameter regions   : list region.
  Parameter budget    : nat.
  Parameter tick      : bool.
  Parameter proj      : list Z -> list Z.
  Parameter observed_raw : list (list Z).   (* whole result regions *)
End SINGLE_HART_CASE.

Module SingleHart (P : SINGLE_HART_CASE) <: TEST_RUN.
  Definition case := P.case.
  Definition platform := P.platform.
  Definition observed : list (list Z) := map P.proj P.observed_raw.
  Definition start : mstate := start_hart_with P.hart P.text P.regions.
  Definition outcome : model_outcome :=
    match eval_run P.tick P.budget start with
    | RDone s => MDone [P.proj (peek_mem (mem s) result_base result_size)]
    | RStuck e => outcome_of_stuck e
    | RBudget => MBudget
    end.
End SingleHart.

(* ---------------------------------------------------------------------- *)
(* 6. TWO MORE BUILDERS, for the two other shapes a single-hart case takes. *)
(*                                                                         *)
(*    Both are still [TEST_RUN]: a builder is only a different way to       *)
(*    COMPUTE [outcome], which is exactly why that is a functor.            *)
(* ---------------------------------------------------------------------- *)

(* (a) A case that needs a SCHEDULE PREFIX before it runs.  A serial byte
       ARRIVING is a schedule choice -- [SUartRx] -- not something
       [eval_run] performs, so a receiving case starts from the state
       [srun] reaches and runs from there. *)

Module Type SCHED_CASE.
  Parameter case      : string.
  Parameter platform  : string.
  Parameter text      : list Z.
  Parameter hart      : Z.
  Parameter regions   : list region.
  Parameter budget    : nat.
  Parameter prefix    : list sitem.   (* delivered before the run *)
  Parameter proj      : list Z -> list Z.
  Parameter observed_raw : list (list Z).
End SCHED_CASE.

Module SchedHart (P : SCHED_CASE) <: TEST_RUN.
  Definition case := P.case.
  Definition platform := P.platform.
  Definition observed : list (list Z) := map P.proj P.observed_raw.
  Definition outcome : model_outcome :=
    match srun P.prefix (start_hart_with P.hart P.text P.regions) with
    | None => MBudget          (* the prefix itself was not enabled *)
    | Some s0 =>
        match eval_run false P.budget s0 with
        | RDone s => MDone [P.proj (peek_mem (mem s) result_base result_size)]
        | RStuck e => outcome_of_stuck e
        | RBudget => MBudget
        end
    end.
End SchedHart.

(* (b) A case whose several outcomes come from the DEVICE, not from two
       harts: the disk may complete two in-flight requests in either order,
       and [run_until_at] takes which in-flight head to answer as a
       parameter.  One run per pick, one observation each. *)

Module Type PICKS_CASE.
  Parameter case      : string.
  Parameter platform  : string.
  Parameter text      : list Z.
  Parameter hart      : Z.
  Parameter regions   : list region.
  Parameter budget    : nat.
  Parameter picks     : list (virtio_state -> option Z).
  Parameter proj      : list Z -> list Z.
  Parameter observed_raw : list (list Z).
End PICKS_CASE.

Module PicksHart (P : PICKS_CASE) <: TEST_RUN.
  Definition case := P.case.
  Definition platform := P.platform.
  Definition observed : list (list Z) := map P.proj P.observed_raw.
  Definition start : mstate := start_hart_with P.hart P.text P.regions.
  Definition outcome : model_outcome :=
    MDone (map (fun pk => P.proj (result_of (run_until_at pk P.budget start)))
               P.picks).
End PicksHart.

(* The two projections almost every run uses.  [whole] is the default and
   the strongest: the entire 4 KB result region, nothing trimmed, so a
   difference cannot hide in the tail.  [fields] keeps a named list of
   4-byte words and is for a case some of whose fields legitimately differ
   between two runs of the same machine. *)
Definition whole : list Z -> list Z := fun r => r.

Definition fields (offs : list nat) : list Z -> list Z :=
  fun r => flat_map (fun o => take 4 (drop o r)) offs.
