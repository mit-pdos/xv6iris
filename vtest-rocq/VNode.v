(* ====================================================================== *)
(* VNode.v -- STEPPING ONE SAIL EVENT AT A TIME.                           *)
(*                                                                         *)
(* [VConc] steps whole INSTRUCTIONS: [VTso.texec] runs a hart from one     *)
(* boundary to the next, so every memory access an instruction            *)
(* makes happens with no other hart in between.  For a plain load or store *)
(* that is exactly right -- the access IS the instruction.  It stops being *)
(* right the moment an instruction makes MORE THAN ONE access, and the     *)
(* case that matters is a PAGE TABLE WALK: an Sv39 data access is three    *)
(* PTE reads, possibly an A/D write-back, and then the access itself, and  *)
(* real hardware does not hold the bus across all of them.  A hart that    *)
(* rewrites a PTE between another hart's second and third walk reads       *)
(* produces a translation NO interleaving of whole instructions explains.  *)
(*                                                                         *)
(* THE LANGUAGE ALREADY WORKS THIS WAY.  [RiscvLang.prim_step]'s hart arm  *)
(* is [mnode_step] -- one Sail-monad NODE per language step -- and         *)
(* [HartBlock.v] relates a contiguous interference-free run of those to    *)
(* one old whole-instruction [run].  So this file is not a new semantics;  *)
(* it is the executable side of the granularity the model ALREADY has, and *)
(* [VConc]'s instruction-granular schedules are the special case where     *)
(* nothing interleaves inside a block.                                     *)
(*                                                                         *)
(* WHAT IS STILL MISSING, stated plainly: the soundness lemma              *)
(*   tnode pol h img s log tv hr m = Some (m', s', log', tv', hr') ->     *)
(*     mnode_step oth h img s log tv itv hr r m m' s' log' tv' itv hr' r' *)
(* which is the converse [HartBlock.v]'s header defers to "the language's  *)
(* own functional interpreter (the reflective stepper)".  Every arm below  *)
(* is a transcription of the corresponding [mnode_step] arm, so the proof  *)
(* is a case analysis with no content -- but it is not written yet, and    *)
(* until it is, a result here is a fact about [tnode] and not yet about    *)
(* [prim_step].  Same standing caveat as the rest of the suite.            *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions list.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvModelBytes RiscvExec DevModel TsoMemPa.
Require Export VConc.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. One node: [VTso.tnode], the transcription of [mnode_step]'s arms     *)
(*    with the recursion removed, memory-model state and all.  The read    *)
(*    policy is the schedule's, as in VConc.                              *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(* 2. Seeing where a hart IS.  This is what makes a sub-instruction test   *)
(*    writable: without it a schedule can only count nodes, which is       *)
(*    unreadable and breaks the moment the model's node sequence shifts.   *)
(* ---------------------------------------------------------------------- *)


(* the memory access a hart is ABOUT to make: (address, width, is-write) *)


(* ---------------------------------------------------------------------- *)
(* 3. The node-granular multi-hart machine.  [gstate] plus, per hart, the  *)
(*    residual monad -- which is precisely what [RiscvLang]'s expression   *)
(*    [HartE gen cpu m] carries, so this is the same state the language    *)
(*    keeps, not an invention.                                             *)
(* ---------------------------------------------------------------------- *)

Global Instance nm_insert : Insert CPU (M unit) (CPU -> M unit) :=
  fun c m f c' => if decide (c = c') then m else f c'.

Record nstate := NState { ns_g : gstate; ns_m : CPU -> M unit }.


(* one node of hart [c]; at a cycle boundary, start the next cycle *)
Definition nstep1 (pol : rpol) (c : CPU) (x : nstate) : option nstate :=
  match ns_m x c with
  | Interface.Ret _ =>
      Some (NState (gboundary (ns_g x) c) (<[c := riscv_step false]> (ns_m x)))
  | m =>
      match tnode pol (hart_agent c) (gimg (ns_g x)) (gfocus (ns_g x) c)
                  (glog (ns_g x)) (gtv (ns_g x) c) (ghr (ns_g x) c) m with
      | Some (m', s', log', tv', hr') =>
          Some (NState (gwb (ns_g x) c s' log' tv' hr') (<[c := m']> (ns_m x)))
      | None => None
      end
  end.

Fixpoint nsteps (pol : rpol) (c : CPU) (n : nat) (x : nstate) : option nstate :=
  match n with
  | 0%nat => Some x
  | S n' => match nstep1 pol c x with
            | Some x' => nsteps pol c n' x'
            | None => None
            end
  end.

(* THE SURGICAL TOOL: run hart [c] until it is ABOUT to touch [addr] and
   stop there, INSIDE the instruction.  A test says "walk hart 0 up to the
   read of the level-0 PTE" instead of counting nodes, so the schedule stays
   readable and survives an unrelated change to the model's node sequence. *)

Inductive nitem :=
  | NCpu (c : CPU) (n : nat)        (* n NODES of hart c, loads read at the top *)
  | NCpuStale (c : CPU) (n : nat)   (* n NODES of hart c, loads as stale as allowed *)
  | NUntil (c : CPU) (addr : Z)     (* hart c up to its access of addr *)
  | NDev.



(* finish: round-robin both harts a node at a time until hart 0 publishes *)


