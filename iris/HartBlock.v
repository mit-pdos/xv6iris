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
   the old machine also did.  The converse (run => block) is NOT
   unconditionally true and is deliberately not stated here -- the language
   FUSES an exclusive read with its paired conditional write and guards the
   plain read arm with [ak_excl = false], so a [run] containing a BARE
   exclusive read has no block.  Its honest witness is the language's own
   functional interpreter (the reflective stepper), where "the fused window
   was found" is a computation rather than a hypothesis; it belongs with that
   stepper, not here.

   INTERFERENCE.  "No interference" is not a hypothesis of any lemma below --
   it is built into the shape: [mblock] chains [mnode_step] on ONE hart's
   [mstate], so there is nowhere for another thread's effect to enter.  A
   caller in the logic earns that shape by owning what the block reads. *)
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
  | _ => mnode_step c.2 c.1 c'.1 c'.2
  end.

Definition mblock : relation (M unit * mstate) := rtc mstep1.

(* ====================================================================== *)
(* 2. The window ingredients: silent nodes and the conditional write both   *)
(*    fold back into [run].                                                 *)
(*                                                                         *)
(* These are what the FUSED AMO arm costs: its single language step stands  *)
(* for a whole stretch of [run], so the bracket has to re-expand it.        *)
(* ====================================================================== *)

Lemma silent1_run (c c' : M unit * regstate)
    (mem : gmap Arch.pa (bv 8)) (d : dev_state) :
  silent1 c c' ->
  forall x s2, run c'.1 (MState c'.2 mem d) x s2
            -> run c.1 (MState c.2 mem d) x s2.
Proof.
  destruct c as [m rs]. rewrite /silent1 /=.
  destruct m as [y|T oc k]; [by intros []|].
  destruct oc; simpl; try (by intros []);
    try (intros ->; simpl; intros x s2 H; exact H).
  (* Choose: the language picked one branch, [run] quantifies over some *)
  intros (ch & ->) x s2 H. simpl. by exists ch.
Qed.

Lemma silent_run_run (c c' : M unit * regstate)
    (mem : gmap Arch.pa (bv 8)) (d : dev_state) :
  silent_run c c' ->
  forall x s2, run c'.1 (MState c'.2 mem d) x s2
            -> run c.1 (MState c.2 mem d) x s2.
Proof.
  rewrite /silent_run. induction 1 as [c|c c1 c2 Hstep _ IH]; [done|].
  intros x s2 H. eapply silent1_run; [exact Hstep|]. by apply IH.
Qed.

Lemma wr_node_run (m1 m' : M unit) (mem mem1 : gmap Arch.pa (bv 8))
    (rs : regstate) (d : dev_state) :
  wr_node m1 mem mem1 m' ->
  forall x s2, run m' (MState rs mem1 d) x s2
            -> run m1 (MState rs mem d) x s2.
Proof.
  rewrite /wr_node. destruct m1 as [y|T oc k]; [by intros []|].
  destruct oc; try (by intros []).
  intros (Hdev & _ & -> & ->) x s2 H. cbn [run]. by rewrite Hdev.
Qed.

(* ====================================================================== *)
(* 3. One node folds back into [run] -- the whole bracket in one step.      *)
(* ====================================================================== *)

Lemma mnode_step_run (s : mstate) (m m' : M unit) (s' : mstate) :
  mstep1 (m, s) (m', s') ->
  forall x s2, run m' s' x s2 -> run m s x s2.
Proof.
  (* [s] is destructed up front: [mstate] is not a primitive record, so [s]
     and [MState (sregs s) (mem s) (mdev s)] are NOT convertible, and the
     fused arm's appeal to [silent_run_run] needs the latter shape. *)
  destruct s as [rs0 mem0 dv0].
  rewrite /mstep1 /= /mnode_step.
  destruct m as [y|T oc k]; [by intros []|].
  (* [cbn beta iota] and NOT [simpl]: it reduces the dependent match that
     selects this outcome's arm WITHOUT also unfolding the [run] in the
     conclusion -- which would pre-destruct [dev_addr] and leave the memory
     arms with nothing to rewrite. *)
  destruct oc; cbn beta iota; try (by intros []);
    try (intros (-> & ->); intros x s2 H; exact H).
  - (* MemRead *)
    destruct (dev_addr _) eqn:Hd.
    + intros (w & d' & Hdr & Hm & Hs) x s2 H. subst m' s'.
      cbn [run]. rewrite Hd Hdr. exact H.
    + intros [(_ & w & Hbytes & Hm & Hs)
             |(_ & w & m1 & rs1 & mem1 & Hbytes & Hsil & Hwr & Hs)] x s2 H.
      * (* the plain read *)
        subst m' s'. cbn [run]. rewrite Hd.
        exists w. split; [exact Hbytes|exact H].
      * (* THE FUSED WINDOW, re-expanded: read, silent stretch, write *)
        subst s'. cbn [run]. rewrite Hd.
        exists w. split; [exact Hbytes|].
        (* both pair arguments given LITERALLY: [silent_run_run]'s conclusion
           projects out of its cursor, and a projection of an evar pair does
           not unify. *)
        eapply (silent_run_run (k (inl (w, None)), rs0) (m1, rs1) mem0 dv0);
          [exact Hsil|]. cbn.
        eapply wr_node_run; [exact Hwr|]. exact H.
  - (* MemWrite *)
    destruct (dev_addr _) eqn:Hd.
    + intros (d' & Hdw & Hm & Hs) x s2 H. subst m' s'.
      cbn [run]. rewrite Hd Hdw. exact H.
    + intros (Hm & Hs) x s2 H. subst m' s'. cbn [run]. rewrite Hd. exact H.
  - (* Choose *) intros (ch & -> & ->) x s2 H. cbn [run]. by exists ch.
Qed.

(* ====================================================================== *)
(* 4. THE BRACKET.                                                          *)
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
