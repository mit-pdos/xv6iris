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
   what the block reads.

   THE TSO PORT (tso-machine-flip.md RULING 3).  [run] and [exec] STAY FLAT:
   they read [s.(mem)], the flat cache.  Post-flip that is no longer what
   every read arm of [mnode_step] does -- the PLAIN EXPLICIT RAM LOAD reads
   [tso_read img log h tv'] at a nondeterministically advanced view -- so the
   bracket is no longer unconditionally true, and RULING 3 says to re-prove
   it under whichever premise the proof actually needs.  IT NEEDS TWO, both
   about the era the block runs in, and both discharged per step:

     [c.2.(mem) = flat img log]   the FLAT TIE -- [RiscvLang.mm_ok]'s first
                                  conjunct, i.e. the machine invariant, so
                                  it is free at every reachable state;
     [all_own h log]              the SOLO ERA -- every message in the log is
                                  this hart's own.

   Together they are exactly [TsoMemPa.tso_read_all_own]: the sole author of
   the log sees all of it at EVERY view (own-always-visible IS store
   forwarding), so its plain load reads the flat cache no matter where the
   arm's nondeterministic drain put the view, and the arm folds back onto
   [run]'s [s.(mem)] read.  The alternative premise RULING 3 offers -- "the
   run touches no plain RAM data loads" -- would also do, and is STRICTLY
   STRONGER here: it would exclude every load-bearing instruction, whereas
   the solo era excludes only concurrency.  The solo era is the boot
   bracket's and the device-conformance tester's actual situation, which is
   what the bracket exists to serve.

   WHY PER STEP AND NOT THREADED.  Both ties are stated inside [mstep1]'s
   existential rather than as parameters of [mblock], which makes the bracket
   the WEAKEST statement: a chain only has to be a chain of good steps, and
   nothing forces the same [log] on two neighbours.  A caller that has the
   ties at the block's START gets them at every step for free -- the flat tie
   by [RiscvLang.mnode_step_mm] and the solo era by
   [TsoMemPa.all_own_app] (the only arm that appends is the RAM write, and
   it appends [PWMsg _ h]), which is [mnode_step_all_own] below. *)
From stdpp Require Import gmap relations bitvector.definitions.
(* imported for the same reason RiscvLang.v does, and BEFORE the model: it is
   what makes ssreflect's [rewrite /def] available (the model's own imports
   otherwise restore vanilla [rewrite]) *)
From iris.program_logic Require Import language.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
(* [Require Import] and not merely inherited: [RiscvLang] requires TsoMemPa
   but Import is not transitive, and the era vocabulary ([all_own],
   [tso_read_all_own], [flat]) is spelled unqualified below. *)
Require Import TsoMemPa.
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
(*                                                                         *)
(* The memory-model state ([log], [tv]) is existential exactly as the       *)
(* reservation always was, and carries the two era ties of the header --    *)
(* the only thing the fold-back needs to know about it.                    *)
(* ====================================================================== *)

Definition mstep1 (h : agent) (img : gmap Arch.pa (bv 8))
    (c c' : M unit * mstate) : Prop :=
  match c.1 with
  | Interface.Ret _ => False
  | _ => exists (log log' : list pwmsg) (tv tv' : nat) (r r' : option resv),
      c.2.(mem) = flat img log /\ all_own h log /\
      mnode_step ∅ h img c.2 log tv r c.1 c'.1 c'.2 log' tv' r'
  end.

Definition mblock (h : agent) (img : gmap Arch.pa (bv 8))
  : relation (M unit * mstate) := rtc (mstep1 h img).

(* ====================================================================== *)
(* 2. One node folds back into [run] -- the whole bracket in one step.      *)
(*                                                                         *)
(* Only ONE arm has changed since the SC proof: the plain explicit RAM      *)
(* load, which is now a [tso_read] at the arm's chosen view and is folded   *)
(* back onto [run]'s flat read by the two era ties.  The strongly-ordered   *)
(* read (ifetch / page walk, RULING 1) and the exclusive read still read    *)
(* [s.(mem)] verbatim, and the write arm's [s.(mem)] update is untouched    *)
(* by the append beside it.                                                 *)
(* ====================================================================== *)

Lemma mnode_step_run (h : agent) (img : gmap Arch.pa (bv 8))
    (s : mstate) (m m' : M unit) (s' : mstate) :
  mstep1 h img (m, s) (m', s') ->
  forall x s2, run m' s' x s2 -> run m s x s2.
Proof.
  rewrite /mstep1 /=.
  destruct m as [y|T oc k]; [by intros []|].
  intros (log & log' & tv & tv' & r & r' & Hflat & Hown & Hn). revert Hn.
  rewrite /mnode_step.
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
    + intros [(_ & tvn & w & _ & _ & Hbytes & Hm & Hs & _)
             |(_ & [(Hov & _) | (_ & w & Hbytes & Hm & Hs & _)])] x s2 H.
      * (* THE PLAIN LOAD -- now EVERY non-exclusive read, implicit ones
           included (RULING 1 overruled).  [Hbytes] reads
           [tso_read] at the drained view [tvn]; the solo era collapses that
           onto the flat cache at ANY view, and the flat tie names the flat
           cache [s.(mem)]. *)
        subst m' s'. cbn [run]. rewrite Hd.
        exists w. split; [|exact H].
        intros j Hj. rewrite Hflat -(tso_read_all_own img log h tvn _ Hown).
        exact (Hbytes j Hj).
      * (* blocked exclusive read: the self-loop needs an overlap with the
           EMPTY set *)
        by exfalso; apply Hov; set_solver.
      * (* exclusive read: reads [s.(mem)], which IS the read at the top *)
        subst m' s'. cbn [run]. rewrite Hd.
        exists w. split; [exact Hbytes|exact H].
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

Lemma mblock_run (h : agent) (img : gmap Arch.pa (bv 8))
    (c c' : M unit * mstate) :
  mblock h img c c' ->
  forall u : unit, c'.1 = Interface.Ret u -> run c.1 c.2 u c'.2.
Proof.
  induction 1 as [c|c c1 c2 Hstep _ IH]; intros u Hu.
  - destruct c as [m s]. simpl in *. subst m. by simpl.
  - destruct c as [m s], c1 as [m1 s1]. simpl in *.
    eapply mnode_step_run; [exact Hstep|]. by apply IH.
Qed.

(* The headline: a contiguous, interference-free run of the new machine from
   the START of a cycle to the next boundary, IN A SOLO ERA, is exactly one
   [run] of the old machine's loop body.  [run] is functional where [exec]
   succeeds ([RiscvExec.exec_run_det]), so this is also what pins the block's
   END state to the certified one. *)
Corollary hart_block_run (h : agent) (img : gmap Arch.pa (bv 8))
    (tick : bool) (s s' : mstate) :
  mblock h img (riscv_step tick, s) (Interface.Ret tt, s') ->
  run (riscv_step tick) s tt s'.
Proof. intros H. exact (mblock_run _ _ _ _ H tt eq_refl). Qed.

(* ====================================================================== *)
(* 4. THE ERA TIES ARE INDUCTIVE -- why [mstep1]'s premises are not vacuous. *)
(*                                                                          *)
(* The flat tie's induction is [RiscvLang.mnode_step_mm] (it is [mm_ok]'s    *)
(* first conjunct).  The solo era's is here, and it is one line of content:  *)
(* the ONLY arm that appends is the RAM write, and it appends a message      *)
(* authored by the stepping hart.  Together they say that a caller holding   *)
(* the two ties at the START of a block holds them at every node of it, so   *)
(* an [mblock] can actually be built.                                        *)
(* ====================================================================== *)

Lemma mnode_step_all_own (oth : gset Arch.pa) (h : agent)
    (img : gmap Arch.pa (bv 8)) (s : mstate) (log : list pwmsg) (tv : nat)
    (r : option resv) (m m' : M unit) (s' : mstate) (log' : list pwmsg)
    (tv' : nat) (r' : option resv) :
  mnode_step oth h img s log tv r m m' s' log' tv' r' ->
  all_own h log -> all_own h log'.
Proof.
  rewrite /mnode_step. destruct m as [y|T oc k].
  { by intros (tick & _ & _ & -> & _). }
  destruct oc; cbn beta iota;
    try (by intros (_ & _ & -> & _)); try (by intros []).
  - (* MemRead: no arm appends *)
    destruct (dev_addr _).
    + by intros (w & d' & _ & _ & _ & -> & _).
    + by intros [(_ & tvn & w & _ & _ & _ & _ & _ & -> & _)
                |(_ & [(_ & _ & _ & -> & _) | (_ & w & _ & _ & _ & -> & _)])].
  - (* MemWrite: the MMIO half is strongly ordered (no log); the RAM half
       appends THIS hart's message *)
    destruct (dev_addr _).
    + by intros (d' & _ & _ & _ & -> & _).
    + intros [(_ & _ & _ & -> & _) | (_ & _ & _ & -> & _)] Hown; [done|].
      apply all_own_app; [exact Hown|done].
  - (* Choose *) by intros (ch & _ & _ & -> & _).
Qed.
