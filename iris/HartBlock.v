(* HartBlock.v -- THE SOLO-BLOCK BRACKET.

   [RiscvLang.mnode_step] steps a hart ONE Sail-monad node at a time; the
   pre-port machine ran a WHOLE instruction ([RiscvLang.run (riscv_step
   tick)]) in one step.  This file relates the two: a CONTIGUOUS run of node
   steps, boundary to boundary and with NO INTERFERENCE, is exactly one old
   [run].

   WHAT IT IS FOR.  Every certification in the tree -- the [exec_*] catalogue,
   the decode bridge, the per-instruction interpreter-run facts the leaves are
   proven with -- is a fact about [run]/[exec] over a whole instruction.  The
   bracket is what lets the adapter that rebuilds the whole-instruction WP
   CONSUME those facts unchanged instead of re-deriving them node by node.  It
   is the SC analogue of an interpreter/LTS bracket, and it is pure: no Iris.

   DIRECTION.  Only the SOUND direction (block => run) is proven here, and it
   is the unconditional one: whatever the new machine does in a solo block,
   the old machine also did.  The converse (run => block) is deliberately not
   stated here; its honest witness is the language's own functional
   interpreter (the reflective stepper), and it belongs with that stepper.

   INTERFERENCE.  "No interference" is not a hypothesis of any lemma below --
   it is built into the shape: [mblock] chains [mnode_step] on ONE hart's
   [mstate] with NO OTHER HART'S RESERVATION in force ([oth = ∅], design
   §3a), so there is nowhere for another thread's effect to enter and no
   self-loop arm is ever enabled.  The hart's OWN reservation is threaded
   existentially: with nobody else reserving, it changes what the memory arms
   RECORD but never what they DO, so [run] -- which has no reservation --
   is reached regardless.  A caller in the logic earns that shape by owning
   what the block reads. *)
From stdpp Require Import gmap relations bitvector.definitions.
(* imported for the same reason RiscvLang.v does, and BEFORE the model: it is
   what makes ssreflect's [rewrite /def] available (the model's own imports
   otherwise restore vanilla [rewrite]) *)
From iris.program_logic Require Import language.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The block relation.                                                  *)
(*                                                                         *)
(* [mstep1] is [mnode_step] with the RESTART arm removed: at [Ret _] the    *)
(* language begins a fresh cycle, so an unrestricted [rtc] would run        *)
(* straight through the boundary and the bracket would be false (a block    *)
(* from [Ret tt] to [Ret tt] could be a whole extra instruction).  Stopping *)
(* at the boundary is what makes "boundary to boundary" mean one cycle.     *)
(* ====================================================================== *)

Definition mstep1 (c c' : M unit * mstate) : Prop :=
  match c.1 with
  | Interface.Ret _ => False
  | _ => exists r r' : option resv, mnode_step ∅ c.2 r c.1 c'.1 c'.2 r'
  end.

Definition mblock : relation (M unit * mstate) := rtc mstep1.

(* ====================================================================== *)
(* 2. One node folds back into [run] -- the whole bracket in one step.      *)
(* ====================================================================== *)

Lemma mnode_step_run (s : mstate) (m m' : M unit) (s' : mstate) :
  mstep1 (m, s) (m', s') ->
  forall x s2, run m' s' x s2 -> run m s x s2.
Proof.
  rewrite /mstep1 /=.
  destruct m as [y|T oc k]; [by intros []|].
  intros (r & r' & Hn). revert Hn. rewrite /mnode_step.
  (* [cbn beta iota] and NOT [simpl]: it reduces the dependent match that
     selects this outcome's arm WITHOUT also unfolding the [run] in the
     conclusion -- which would pre-destruct [dev_addr] and leave the memory
     arms with nothing to rewrite. *)
  destruct oc; cbn beta iota; try (by intros []);
    try (intros (-> & -> & _); intros x s2 H; exact H).
  - (* MemRead *)
    destruct (dev_addr _) eqn:Hd.
    + intros (w & d' & Hdr & Hm & Hs & _) x s2 H. subst m' s'.
      cbn [run]. rewrite Hd Hdr. exact H.
    + (* plain or exclusive, the read is the same; the self-loop arm needs an
         overlap with the EMPTY set *)
      intros [(_ & w & Hbytes & Hm & Hs & _)
             |(_ & [(Hov & _) | (_ & w & Hbytes & Hm & Hs & _)])] x s2 H;
        [ | by exfalso; apply Hov; set_solver | ];
        subst m' s'; cbn [run]; rewrite Hd; exists w; split; [exact Hbytes|exact H
        | exact Hbytes | exact H].
  - (* MemWrite *)
    destruct (dev_addr _) eqn:Hd.
    + intros (d' & Hdw & Hm & Hs & _) x s2 H. subst m' s'.
      cbn [run]. rewrite Hd Hdw. exact H.
    + intros [(Hov & _) | (_ & Hm & Hs & _)] x s2 H;
        [by exfalso; apply Hov; set_solver|].
      subst m' s'. cbn [run]. rewrite Hd. exact H.
  - (* Choose *) intros (ch & -> & -> & _) x s2 H. cbn [run]. by exists ch.
Qed.

(* ====================================================================== *)
(* 3. THE BRACKET.                                                          *)
(* ====================================================================== *)

Lemma mblock_run (c c' : M unit * mstate) :
  mblock c c' ->
  forall u : unit, c'.1 = Interface.Ret u -> run c.1 c.2 u c'.2.
Proof.
  induction 1 as [c|c c1 c2 Hstep _ IH]; intros u Hu.
  - destruct c as [m s]. simpl in *. subst m. by simpl.
  - destruct c as [m s], c1 as [m1 s1]. simpl in *.
    eapply mnode_step_run; [exact Hstep|]. by apply IH.
Qed.

(* The headline: a contiguous, interference-free run of the new machine from
   the START of a cycle to the next boundary is exactly one [run] of the old
   machine's loop body.  [run] is functional where [exec] succeeds
   ([RiscvExec.exec_run_det]), so this is also what pins the block's END
   state to the certified one. *)
Corollary hart_block_run (tick : bool) (s s' : mstate) :
  mblock (riscv_step tick, s) (Interface.Ret tt, s') ->
  run (riscv_step tick) s tt s'.
Proof. intros H. exact (mblock_run _ _ H tt eq_refl). Qed.
