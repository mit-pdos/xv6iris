(* ====================================================================== *)
(* VExecStuck.v -- WHY [exec] STOPPED, and the theorem that makes the      *)
(* answer worth anything.                                                  *)
(*                                                                         *)
(* [RiscvExec.exec] is a partial FUNCTION mirroring the relation [run].    *)
(* [exec_run_det] ties them ONE WAY:                                       *)
(*                                                                         *)
(*     exec m s = Some (x,s')  ->  run m s x s'  /\  the run is unique     *)
(*                                                                         *)
(* and there is deliberately no converse, because there cannot be a useful *)
(* one: [exec]'s failure clause is                                         *)
(*                                                                         *)
(*     | _ => fun _ => None      -- Choose, GenericFail, Discard, ...      *)
(*                                                                         *)
(* which lumps together two completely different situations.  On           *)
(* [Interface.Choose] the RELATION branches over every choice              *)
(* ([run (Choose) = exists c, run (k c) ...]) and it is only the           *)
(* deterministic interpreter that declines to pick one.  On                *)
(* [GenericFail]/[Discard], and at an undecoded MMIO offset or an unmapped *)
(* RAM address, the relation really is [False].                            *)
(*                                                                         *)
(* SO [exec m s = None] PROVES NOTHING ABOUT THE MODEL, and reading it as  *)
(* "the model has no transition" is a mistake this development has made    *)
(* twice -- see claude-notes/durable-notes.md, "AN ABSENT WITNESS IS NOT   *)
(* AN ABSENT EXECUTION", and the two retracted device-conformance findings *)
(* it cost.                                                                *)
(*                                                                         *)
(* THIS FILE SPLITS THE TWO.  [exec_r] is [exec] with its failure clause   *)
(* refined into [ENoStep] and [EChoice], it agrees with [exec] everywhere  *)
(* ([exec_r_exec]), and then                                               *)
(*                                                                         *)
(*     exec_r m s = inr ENoStep  ->  forall x s', ~ run m s x s'           *)
(*                                                                         *)
(* is the converse the tree did not have.  A caller that gets [ENoStep]    *)
(* may now say "the model has no transition here" and MEAN it; a caller    *)
(* that gets [EChoice] has learned only that this interpreter would not    *)
(* choose.                                                                 *)
(*                                                                         *)
(* IT LIVES IN THE HARNESS, not in iris/.  Nothing in the proof tower needs *)
(* it -- the WP rules consume [exec_run_det]'s Some-direction and never ask *)
(* why [exec] declined -- and RiscvExec.v's reverse-dependency closure is   *)
(* ~1286 files.  What needs it is the device-conformance suite, which       *)
(* reports [VStuck] and, until this file, could not say what that meant.    *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions list.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvExec.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Why the interpreter stopped.                                         *)
(* ---------------------------------------------------------------------- *)

Inductive estuck : Set :=
  | ENoStep   (* the RELATION has no transition here either              *)
  | EChoice.  (* a [Choose]: the relation branches, [exec] will not pick *)

(* ---------------------------------------------------------------------- *)
(* 2. [exec], with the failure clause split.                               *)
(*                                                                         *)
(*    Every successful clause is [RiscvExec.exec]'s, character for         *)
(*    character; the only change is that [Interface.Choose] is now its own *)
(*    arm.  [exec_r_exec] below is what makes that claim checkable rather  *)
(*    than a comment.                                                      *)
(* ---------------------------------------------------------------------- *)

Fixpoint exec_r {X} (m : M X) (s : mstate) {struct m}
  : (X * mstate) + estuck :=
  match m with
  | Interface.Ret y => inl (y, s)
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M X) -> (X * mstate) + estuck with
       | Interface.RegRead r _ => fun k =>
           exec_r (k (register_lookup r s.(sregs))) s
       | Interface.RegWrite r _ v => fun k => exec_r (k tt) (set_reg s r v)
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then
             match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
             | Some (w, d') =>
                 exec_r (k (inl (w, None))) (MState s.(sregs) s.(mem) d')
             | None => inr ENoStep
             end
           else
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w => exec_r (k (inl (w, None))) s
             | None => inr ENoStep
             end
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req) then
             match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) with
             | Some d' => exec_r (k (inl None)) (MState s.(sregs) s.(mem) d')
             | None => inr ENoStep
             end
           else
             exec_r (k (inl None))
                  (MState s.(sregs)
                     (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                  (Interface.WriteReq.value req)) s.(mdev))
       | Interface.InstrAnnounce _   => fun k => exec_r (k tt) s
       | Interface.BranchAnnounce _ _=> fun k => exec_r (k tt) s
       | Interface.Barrier _         => fun k => exec_r (k tt) s
       | Interface.CacheOp _         => fun k => exec_r (k tt) s
       | Interface.TlbOp _           => fun k => exec_r (k tt) s
       | Interface.TakeException _   => fun k => exec_r (k tt) s
       | Interface.ReturnException _ => fun k => exec_r (k tt) s
       | Interface.TranslationStart _=> fun k => exec_r (k tt) s
       | Interface.TranslationEnd _  => fun k => exec_r (k tt) s
       | Interface.CycleCount        => fun k => exec_r (k tt) s
       | Interface.Message _         => fun k => exec_r (k tt) s
       | Interface.GetCycleCount     => fun k => exec_r (k 0%Z) s
       (* THE SPLIT: nondeterminism is not stuckness *)
       | Interface.Choose _          => fun _ => inr EChoice
       | _ => fun _ => inr ENoStep
       end) k
  end.

(* ---------------------------------------------------------------------- *)
(* 3. [exec_r] IS [exec], refined.                                         *)
(* ---------------------------------------------------------------------- *)

Lemma exec_r_exec {X} (m : M X) (s : mstate) :
  match exec_r m s with
  | inl p => exec m s = Some p
  | inr _ => exec m s = None
  end.
Proof.
  revert s. induction m as [y|T oc k IH]; intros s; [done|].
  (* every deterministic arm is [IH]; [Choose] and the failure arms are
     [None = None] on both sides *)
  destruct oc; simpl; try apply IH; try done.
  - (* MemRead *)
    destruct (dev_addr _).
    + destruct (dev_read _ _ _) as [[w0 d']|]; [apply IH|done].
    + destruct (read_bytes _ _ _) as [w0|]; [apply IH|done].
  - (* MemWrite *)
    destruct (dev_addr _).
    + destruct (dev_write _ _ _ _) as [d'|]; [apply IH|done].
    + apply IH.
Qed.

Corollary exec_r_inl {X} (m : M X) s p :
  exec_r m s = inl p -> exec m s = Some p.
Proof. intros H. pose proof (exec_r_exec m s) as He. rewrite H in He. exact He. Qed.

Corollary exec_r_inr {X} (m : M X) s e :
  exec_r m s = inr e -> exec m s = None.
Proof. intros H. pose proof (exec_r_exec m s) as He. rewrite H in He. exact He. Qed.

(* ...and the other direction, so a caller holding [exec m s = None] can
   always ASK which kind it was. *)
Lemma exec_none_why {X} (m : M X) s :
  exec m s = None -> exec_r m s = inr ENoStep \/ exec_r m s = inr EChoice.
Proof.
  intros Hn. destruct (exec_r m s) as [p|[|]] eqn:Hr; [|by left|by right].
  pose proof (exec_r_inl _ _ _ Hr) as Hs. congruence.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. THE MISSING CONVERSE.                                                *)
(*                                                                         *)
(*    [read_bytes] returns [None] exactly when some byte of the window is  *)
(*    absent, and [run]'s RAM-read arm demands a [w] whose every byte IS   *)
(*    the memory byte -- so an absent byte leaves no candidate at all.     *)
(* ---------------------------------------------------------------------- *)

Lemma read_bytes_none mm pa n :
  read_bytes mm pa n = None ->
  exists j : nat, (N.of_nat j < n)%N /\ mm !! pa_add pa j = None.
Proof.
  unfold read_bytes.
  destruct (mapM (fun j : nat => mm !! pa_add pa j) (seq 0 (N.to_nat n)))
    as [bs|] eqn:Hm; [discriminate|intros _].
  apply mapM_None in Hm.
  apply Exists_exists in Hm as (j & Hj & Hnone).
  apply elem_of_seq in Hj as [_ Hlt].
  exists j. split; [lia|exact Hnone].
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. THE THEOREM.                                                         *)
(*                                                                         *)
(*    [ENoStep] means what it says: the RELATION has no transition.  This  *)
(*    is the statement the tree did not have, and the reason [VStuck] used *)
(*    to be uninterpretable.                                               *)
(* ---------------------------------------------------------------------- *)

Lemma exec_r_no_step {X} (m : M X) (s : mstate) :
  exec_r m s = inr ENoStep -> forall x s', ~ run m s x s'.
Proof.
  revert s. induction m as [y|T oc k IH]; intros s Hst x s' Hrun; [discriminate|].
  (* [destruct] on a scrutinee that both hypotheses mention substitutes in
     BOTH, so no [rewrite ... in Hrun] is needed (or possible). *)
  (* three shapes: a deterministic arm is the IH; [Choose] contradicts
     [Hst] (it is [inr EChoice]); a failure arm makes [Hrun] itself [False]. *)
  destruct oc; simpl in Hst, Hrun;
    try (eapply IH; [exact Hst|exact Hrun]);
    try discriminate; try exact Hrun.
  - (* MemRead *)
    destruct (dev_addr _).
    + (* device fabric: an undecoded offset or width is [False] in [run] *)
      destruct (dev_read _ _ _) as [[w0 d']|]; [|exact Hrun].
      eapply IH; [exact Hst|exact Hrun].
    + destruct (read_bytes s.(mem) _ _) as [w0|] eqn:Hrb.
      * (* the window is present, so [run]'s witness is forced to be it *)
        destruct Hrun as (w & Hbytes & Hrun).
        assert (Hweq : w = w0).
        { apply bv_eq_of_bytes. intros j Hj.
          pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
          pose proof (Hbytes j Hj) as Hw.
          (* RiscvModelBytes' [pa_add]/[nth_byte] and RiscvLang's are
             DIFFERENT CONSTANTS with the same bodies -- convertible but not
             syntactically equal (see RiscvExec.v's header) -- so [rewrite]
             and [congruence] cannot see through them and the two equations
             have to be chained with [exact], which checks up to conversion. *)
          apply Some_inj.
          etransitivity; [symmetry; exact Hw | exact H0]. }
        subst w. eapply IH; [exact Hst|exact Hrun].
      * (* a byte of the window is absent, so NO witness exists *)
        destruct Hrun as (w & Hbytes & _).
        destruct (read_bytes_none _ _ _ Hrb) as (j & Hj & Hnone).
        (* same conversion caveat: chain with [exact], not [rewrite] *)
        assert (Hcontra : @None (bv 8) = Some (nth_byte w j))
          by (etransitivity; [symmetry; exact Hnone | exact (Hbytes j Hj)]).
        discriminate.
  - (* MemWrite *)
    destruct (dev_addr _).
    + destruct (dev_write _ _ _ _) as [d'|]; [|exact Hrun].
      eapply IH; [exact Hst|exact Hrun].
    + eapply IH; [exact Hst|exact Hrun].
Qed.

(* ...and its contrapositive, which is the shape a caller usually wants:
   if the model DOES step, the interpreter's refusal was a [Choose]. *)
Corollary run_exec_r_choice {X} (m : M X) s x s' :
  run m s x s' -> exec m s = None -> exec_r m s = inr EChoice.
Proof.
  intros Hrun Hnone.
  destruct (exec_none_why _ _ Hnone) as [H|H]; [|exact H].
  exfalso. exact (exec_r_no_step _ _ H _ _ Hrun).
Qed.
