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
(*   THE MODEL'S BEHAVIOUR IS NEITHER.  It is not a field of the run: a    *)
(*   claim relating two stored values names no program, no state and no    *)
(*   step relation.  It is QUANTIFIED OVER, out of the initial state the   *)
(*   test fixes.                                                           *)
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
(* THERE IS NO INTERPRETER IN THIS FILE, and that is the point.  [exec],   *)
(* [VConc.crun], [VTso.texec] and [VIcache.itexec] are proof STRATEGIES:   *)
(* each is a different way to establish the one statement below, and each  *)
(* owes a bridge to [prim_step] before it establishes anything at all.     *)
(* A fact about [exec] is a fact about the interpreter until then.         *)
(* ====================================================================== *)
From Stdlib Require Import List ZArith String Bool.
From stdpp Require Import base list gmap bitvector.definitions.
Import ListNotations.
From iris.program_logic Require Import language.
From VTest Require Import VTest.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. WHAT A TEST IS -- the fields, and why each is the machine.           *)
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
(* 2. WHAT ONE EXECUTION PRODUCED, on every channel a platform has.        *)
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
     it gets its own field rather than being folded in here.

     BYTES, not [Z].  What the host types is a byte, and saying so is what
     makes [obs_in] of a delivered input the identity rather than the
     identity-on-values-that-happen-to-fit; the alternative is a range side
     condition on the theorem, which would be the same fact written where
     it cannot be checked. *)
  Parameter uart_input : list (bv 8).
  (* ...AND THE DISK IT STARTS FROM, by absolute sector number.  Blank for
     every test written so far, and unrepresentable until now: a test that
     reads a sector it did not itself write could not be stated at all. *)
  Parameter disk_init  : list (Z * list Z).
End TEST.

(* ---------------------------------------------------------------------- *)
(* 3. THE MACHINE THE TEST IS, AS THE LANGUAGE SEES IT.                    *)
(*                                                                         *)
(*     Everything above is about [mstate] and [exec] -- ONE hart, stepped  *)
(*     by the reflective interpreter.  That is a proof STRATEGY, not the   *)
(*     claim: the model our proofs are about is [RiscvLang.prim_step] over *)
(*     [gstate], and a fact about [exec] is a fact about the interpreter   *)
(*     until something connects them.                                      *)
(*                                                                         *)
(*     So the theorem is stated HERE, over [rtc erased_step] from the      *)
(*     test's own configuration, and every interpreter -- [eval_run_at]    *)
(*     for one hart, [VConc.crun]/[cfinish] for an interleaving,           *)
(*     [VTso.texec] under the relaxed machine, [VIcache.itexec] for a      *)
(*     fetch schedule -- becomes a different way to PROVE it.  That is     *)
(*     also why the single-hart shape could never have covered VRunConc:   *)
(*     they are two strategies for one statement, not two statements.      *)
(*                                                                         *)
(*     THE THREAD POOL IS THE LANGUAGE'S OWN.  A powered-on generation-0   *)
(*     machine is [power_fork 0]: every hart at an instruction boundary,   *)
(*     plus the UART, disk and PLIC loops.  A vtest has no power thread -- *)
(*     the machine starts powered on -- so the configuration is that pool  *)
(*     over the test's state, and nothing here invents a shape of its own. *)
(* ---------------------------------------------------------------------- *)

Definition test_gstate (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) : gstate :=
  GState (fun c => ColdBoot.cold_regs
                     (SailStdpp.Values.mword_of_int (hart + Z.of_nat (fin_to_nat c))))
         (mem_of text rs) (dev_of (img_of_sectors disk_init))
         0%nat true (fun _ => None)
         (mem_of text rs) [] (fun _ => 0%nat) (fun _ => 0%nat)
         (fun _ => hread0).

Definition test_config (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) : cfg riscv_lang :=
  (power_fork 0, test_gstate hart text rs disk_init).

(* THE BYTES THE HOST TYPED, out of an observation trace.  The language
   lets a byte arrive at any time, so an execution that is merely REACHABLE
   is one in which the model chose its own input -- which is why the
   theorem below is over [nsteps], where the trace survives, and not over
   [erased_step], where it does not.  ([ObsTrace.obs_wire] is the output
   half of the same idea, and equals the [u_wire] read below.) *)
Fixpoint obs_in (l : list mobs) : list (bv 8) :=
  match l with
  | [] => []
  | ObsUartIn b :: l' => b :: obs_in l'
  | _ :: l' => obs_in l'
  end.

(* WHAT A CONFIGURATION SHOWS, on the three channels a platform has. *)
Definition observed_at (g : gstate) (o : observation) : Prop :=
  peek_mem (gmem g) result_base result_size = o.(o_result)
  /\ (bv_unsigned <$> u_wire (duart (gdev g))) = o.(o_uart)
  /\ v_disk (dvirtio (gdev g)) = disk_of_sectors o.(o_disk).

(* ...AND WHAT IT MEANS FOR THE MODEL TO BE STUCK THERE.  Not the whole
   configuration -- the device loops always have a step -- but ONE THREAD
   with no transition, which is what makes a stuck run admissible: no proof
   over the model gets past that thread either. *)
Definition thread_no_step (g : gstate) (e : mexpr) : Prop :=
  forall κ e' g' efs, ~ prim_step e g κ e' g' efs.

(* ---------------------------------------------------------------------- *)
(* 4. A RUN OF A TEST, and the theorem.                                    *)
(*                                                                         *)
(*    A run has no [outcome].  What the model does is not data the run     *)
(*    carries; it is what the two claims below quantify over, out of the   *)
(*    state [T] fixes -- and [start] is a DEFINITION here, not a           *)
(*    parameter, so a run of [T] has [T]'s machine by construction.        *)
(*                                                                         *)
(*    [picks], [tick] and [budget] are fields because a proof has to name  *)
(*    the witnesses it computed with, but NONE of them appears in the      *)
(*    theorem: the claims quantify them existentially.  What is            *)
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
     existentials in the claims below, so they live in the PROOF, as
     arguments to [VExecStep]'s wrappers, and appear in no statement. *)
  Parameter observed : list observation.

  (* A RUN THAT OBSERVED NOTHING IS NOT A RUN, and this is the field that
     says so.  [run_agrees] quantifies over the observations, so an empty
     list makes it VACUOUSLY TRUE -- a Pass module ascribing to
     TEST_PASSES_AGREE would compile, be listed in _CoqProject, and be
     counted as a proof, while claiming nothing whatever about the model.

     That is not hypothetical: it is how 25 of the board's runs came to
     have green proofs.  The capture side had emptied them and nothing
     downstream could tell, because there is nothing to tell -- a vacuous
     proof and a real one look the same from outside.  Requiring the
     witness here makes the module type reject the case at the point where
     the run is DECLARED, which is the only place the difference is still
     visible. *)
  Axiom observed_ne : observed <> [].
End TEST_RUN.

(* THE THEOREM, over the test's own initial state. *)
(* THE TWO WAYS A RUN PASSES, as two separate claims.  A run proves ONE of
   them, and which one is part of what its file SAYS -- its module
   ascription -- rather than a remark in a header.

   THEY ARE NOT THE SAME KIND OF FACT.  [run_agrees] is about the
   observations: the model exhibits each of them, from this test's own
   configuration, along an execution that typed exactly this test's input.
   [run_no_step_at] is about REACH: this test's execution arrives at a
   thread the RELATION cannot step from, so no proof over the model gets
   past it either.  That is a genuine pass -- it costs reach, not soundness
   -- and it is why [TEST_PASSES_STUCK] below takes no run at all: there is
   no observation anywhere in the statement, and pretending otherwise by
   passing one in would be the misleading part. *)

Definition run_agrees (hart : Z) (text : list Z) (rs : list region)
    (uart_input : list (bv 8)) (disk_init : list (Z * list Z))
    (observed : list observation) : Prop :=
  let c0 := test_config hart text rs disk_init in
  forall o, In o observed ->
    exists n l ts g,
      nsteps n c0 l (ts, g)
      /\ obs_in l = uart_input
      /\ observed_at g o.

Definition run_no_step_at (hart : Z) (text : list Z) (rs : list region)
    (uart_input : list (bv 8)) (disk_init : list (Z * list Z)) : Prop :=
  let c0 := test_config hart text rs disk_init in
  exists n l ts g e,
    nsteps n c0 l (ts, g)
    /\ obs_in l = uart_input
    /\ In e ts /\ thread_no_step g e.

(* A run that AGREES.  Its statement names the run, because it is about
   what the run measured. *)
Module Type TEST_PASSES_AGREE (T : TEST) (R : TEST_RUN T).
  Axiom agrees :
    run_agrees T.hart T.text T.regions T.uart_input T.disk_init R.observed.
End TEST_PASSES_AGREE.

(* A run that is STUCK.  Its statement does NOT name the run: nothing about
   the measurement is claimed, and the module type says so by not taking
   one.  A reader who wants to know whether the model reproduced anything
   can tell from the ascription alone. *)
Module Type TEST_PASSES_STUCK (T : TEST).
  Axiom no_step :
    run_no_step_at T.hart T.text T.regions T.uart_input T.disk_init.
End TEST_PASSES_STUCK.

