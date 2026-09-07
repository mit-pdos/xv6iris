(* ====================================================================== *)
(* VExecStep.v -- FROM THE INTERPRETER TO THE LANGUAGE, ONE NODE.          *)
(*                                                                         *)
(* [VRun.run_passes] is a statement about [RiscvLang.prim_step].  The       *)
(* suite computes with [RiscvExec.exec], which is a different artefact:     *)
(* a functional interpreter over [mstate], reading and writing memory       *)
(* FLAT.  Until the two are connected a green test is a fact about the      *)
(* interpreter and about nothing else.                                      *)
(*                                                                         *)
(* THIS IS THE CONVERSE [HartBlock.v]'s header defers to -- "its honest     *)
(* witness is the language's own functional interpreter (the reflective     *)
(* stepper), and it belongs with that stepper".  [exec_run_det] already     *)
(* goes the easy way ([exec] succeeds => [run] holds).  What is needed is   *)
(* the step-granular direction, against [mnode_step]: one node of the Sail  *)
(* monad, executed, IS one [prim_step] of that hart.                        *)
(*                                                                         *)
(* WHY IT IS NOT DEFINITIONAL, and where the content is.  [mnode_step] is   *)
(* the RELAXED machine: a plain load reads through the write log at some    *)
(* admissible view, and a store appends a message rather than mutating a    *)
(* map.  [exec] does neither -- it reads and writes [s.(mem)].  The two     *)
(* agree because a hart ALONE IN ITS ERA may read at the TOP of the log,    *)
(* where [TsoMemPa.tso_read_top_flat] says [tso_read] IS the flat cache,    *)
(* and because a store's append keeps that cache in lock-step               *)
(* ([TsoMemPa.flat_store]).  [hart_ok] below is exactly the invariant       *)
(* those two facts need, and the flip's RULING 3 -- "a hart alone in its    *)
(* era reads flat" -- is why the harness was left computing this way.       *)
(* ====================================================================== *)
From Stdlib Require Import List ZArith Lia.
From stdpp Require Import base list gmap functions relations bitvector.definitions.
Import ListNotations.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvExec VirtioModel DevModel ColdBoot.
Require Import RiscvLang TsoMemPa.
From VTest Require Import VTest VRun.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. ONE HART, ALONE IN ITS ERA, READING FLAT.                            *)
(*                                                                         *)
(*    The [mstate] the interpreter carries is the projection of [g] at      *)
(*    [cpu]; the log is whatever this hart has authored; and the flat       *)
(*    cache [gmem] is the log's top, which is what makes a flat read a      *)
(*    read the relation admits.                                            *)
(*                                                                         *)
(*    [ho_alone] is the single-hart hypothesis in its exact form: no OTHER  *)
(*    hart reserves anything, so every "blocked while another hart          *)
(*    reserves my bytes" side condition is discharged by disjointness with  *)
(*    the empty set.  It is why the self-loop arms never fire here.         *)
(*                                                                         *)
(*    [ho_tv], [ho_itv], [ho_rv] and [ho_coh] are the bounds that let the   *)
(*    top of the log be an admissible view for this hart's next read.       *)
(* ---------------------------------------------------------------------- *)

Record hart_ok (cpu : CPU) (g : gstate) (s : mstate) : Prop := HartOk {
  ho_regs  : g.(gregs) cpu = s.(sregs);
  ho_mem   : g.(gmem) = s.(mem);
  ho_dev   : g.(gdev) = s.(mdev);
  ho_flat  : g.(gmem) = flat g.(gimg) g.(glog);
  ho_alone : others_resv g.(gresv) cpu = ∅;
  ho_tv    : (g.(gtv) cpu <= length g.(glog))%nat;
  ho_itv   : (g.(gitv) cpu <= length g.(glog))%nat;
  ho_rv    : (hr_rv (g.(ghr) cpu) <= length g.(glog))%nat;
  ho_coh   : forall a, (hr_coh (g.(ghr) cpu) a <= length g.(glog))%nat;
}.

(* ---------------------------------------------------------------------- *)
(* 2. ONE NODE OF THE INTERPRETER.                                         *)
(*                                                                         *)
(*    [RiscvExec.exec] runs a monad to its VALUE, so it cannot be lined up  *)
(*    with a step relation at all.  [enode] is the same match, taking ONE   *)
(*    node and returning the RESIDUAL monad -- the shape [mnode_step] is    *)
(*    in.  [exec] is its transitive closure, which is the next lemma up.    *)
(*                                                                         *)
(*    [Ret] is the INSTRUCTION BOUNDARY, not an ending: the cycle is over   *)
(*    and the next one begins, which is where the language's [exists tick]  *)
(*    is resolved.  The harness resolves it the same way for a whole run,   *)
(*    so [tick] is a parameter here.                                       *)
(* ---------------------------------------------------------------------- *)

Definition enode (tick : bool) (m : M unit) (s : mstate)
  : option (M unit * mstate) :=
  match m with
  | Interface.Ret _ => Some (riscv_step tick, s)
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option (M unit * mstate) with
       | Interface.RegRead rg _ => fun k =>
           Some (k (register_lookup rg s.(sregs)), s)
       | Interface.RegWrite rg _ v => fun k => Some (k tt, set_reg s rg v)
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then
             match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
             | Some (w, d') =>
                 Some (k (inl (w, None)), MState s.(sregs) s.(mem) d')
             | None => None
             end
           else
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w => Some (k (inl (w, None)), s)
             | None => None
             end
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req) then
             match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) with
             | Some d' => Some (k (inl None), MState s.(sregs) s.(mem) d')
             | None => None
             end
           else
             Some (k (inl None),
                   MState s.(sregs)
                     (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                  (Interface.WriteReq.value req)) s.(mdev))
       | Interface.InstrAnnounce _    => fun k => Some (k tt, s)
       | Interface.BranchAnnounce _ _ => fun k => Some (k tt, s)
       | Interface.Barrier _          => fun k => Some (k tt, s)
       | Interface.CacheOp _          => fun k => Some (k tt, s)
       | Interface.TlbOp _            => fun k => Some (k tt, s)
       | Interface.TakeException _    => fun k => Some (k tt, s)
       | Interface.ReturnException _  => fun k => Some (k tt, s)
       | Interface.TranslationStart _ => fun k => Some (k tt, s)
       | Interface.TranslationEnd _   => fun k => Some (k tt, s)
       | Interface.CycleCount         => fun k => Some (k tt, s)
       | Interface.Message _          => fun k => Some (k tt, s)
       | Interface.GetCycleCount      => fun k => Some (k 0%Z, s)
       (* Choose / GenericFail / Discard / ExtraOutcome: [exec] declines,
          and only [Choose] is a case where the RELATION has a step --
          [VExecStuck] is what tells the two apart. *)
       | _ => fun _ => None
       end) k
  end.

(* ---------------------------------------------------------------------- *)
(* 2b. THE HARNESS'S RUN, which is what the suite actually computes.       *)
(*                                                                         *)
(*     One instruction, then every enabled device action, until the guest  *)
(*     publishes its result or the budget runs out.  It lives HERE and not *)
(*     in VRun.v: it is an interpreter, and VRun.v states the theorem.     *)
(*                                                                         *)
(*     EVERY ARM CARRIES ITS STATE, the stuck one included.  Without that, *)
(*     "the model has no transition" can only be said of SOME state -- the *)
(*     shape [VTest.stuck_why_no_step] is stuck with, and nearly vacuous,  *)
(*     since any junk state with no transition witnesses it.               *)
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

(* ---------------------------------------------------------------------- *)
(* 3. THE BOOKKEEPING, once.                                               *)
(*                                                                         *)
(*    Every arm of [hart_node_step] writes the same shape back: this       *)
(*    hart's slot of each per-hart field, the whole memory and device.  So  *)
(*    the invariant is re-established once here, and an arm below owes      *)
(*    only the five facts that are actually about it.                      *)
(* ---------------------------------------------------------------------- *)

(* [RiscvLang] has its OWN [Insert] instances for the per-hart fields --
   [fun cpu v f c => if decide (c = cpu) then v else f c] -- whose guard is
   the reverse of stdpp's, so stdpp's [fn_lookup_insert] lemmas do not
   apply.  These are the four readings the write-back needs. *)

Lemma greg_ins_eq (f : CPU -> regstate) (cpu : CPU) (v : regstate) :
  <[cpu := v]> f cpu = v.
Proof.
  unfold insert, greg_insert.
  destruct (decide (cpu = cpu)) as [_|H]; [reflexivity|contradiction (H eq_refl)].
Qed.

Lemma gtv_ins_eq (f : CPU -> nat) (cpu : CPU) (v : nat) :
  <[cpu := v]> f cpu = v.
Proof.
  unfold insert, gtv_insert.
  destruct (decide (cpu = cpu)) as [_|H]; [reflexivity|contradiction (H eq_refl)].
Qed.

Lemma ghr_ins_eq (f : CPU -> hread) (cpu : CPU) (v : hread) :
  <[cpu := v]> f cpu = v.
Proof.
  unfold insert, ghr_insert.
  destruct (decide (cpu = cpu)) as [_|H]; [reflexivity|contradiction (H eq_refl)].
Qed.

Lemma gresv_ins_ne (f : CPU -> option resv) (cpu c : CPU) (v : option resv) :
  c <> cpu -> <[cpu := v]> f c = f c.
Proof.
  intros Hne. unfold insert, gresv_insert.
  destruct (decide (c = cpu)) as [->|_]; [contradiction (Hne eq_refl)|reflexivity].
Qed.

Lemma others_resv_insert (gr : CPU -> option resv) (cpu : CPU)
    (r : option resv) :
  others_resv (<[cpu := r]> gr) cpu = others_resv gr cpu.
Proof.
  unfold others_resv. f_equal. apply list_fmap_ext.
  intros i c Hc. destruct (decide (c = cpu)) as [->|Hne]; [reflexivity|].
  unfold resv_dom. rewrite (gresv_ins_ne gr cpu c r Hne). reflexivity.
Qed.

Definition wb (cpu : CPU) (g : gstate) (s' : mstate) (log' : list pwmsg)
    (tv' itv' : nat) (hr' : hread) (r' : option resv) : gstate :=
  GState (<[cpu := s'.(sregs)]> g.(gregs)) s'.(mem) s'.(mdev)
         g.(ggen) g.(gpow) (<[cpu := r']> g.(gresv))
         g.(gimg) log' (<[cpu := tv']> g.(gtv)) (<[cpu := itv']> g.(gitv))
         (<[cpu := hr']> g.(ghr)).

Lemma hart_ok_wb (cpu : CPU) (g : gstate) (s' : mstate) (log' : list pwmsg)
    (tv' itv' : nat) (hr' : hread) (r' : option resv) :
  others_resv g.(gresv) cpu = ∅ ->
  s'.(mem) = flat g.(gimg) log' ->
  (tv' <= length log')%nat ->
  (itv' <= length log')%nat ->
  (hr_rv hr' <= length log')%nat ->
  (forall a, (hr_coh hr' a <= length log')%nat) ->
  hart_ok cpu (wb cpu g s' log' tv' itv' hr' r') s'.
Proof.
  intros Hal Hfl Htv Hitv Hrv Hcoh. unfold wb. constructor;
    cbn [gregs gmem gdev ggen gpow gresv gimg glog gtv gitv ghr].
  - apply greg_ins_eq.
  - reflexivity.
  - reflexivity.
  - exact Hfl.
  - rewrite others_resv_insert. exact Hal.
  - rewrite gtv_ins_eq. exact Htv.
  - rewrite gtv_ins_eq. exact Hitv.
  - rewrite ghr_ins_eq. exact Hrv.
  - intros a. rewrite ghr_ins_eq. exact (Hcoh a).
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. ONE NODE IS ONE [prim_step].                                         *)
(*                                                                         *)
(*    The lift is the easy half and is where [wb] pays off: [hart_node_step]*)
(*    writes back exactly that shape, so the hart arm of [prim_step] is a   *)
(*    matter of naming the witnesses.  All the content is in [enode_mnode]  *)
(*    below, which is where the flat/relaxed gap is actually crossed.       *)
(* ---------------------------------------------------------------------- *)

Lemma mnode_prim (gen : nat) (cpu : CPU) (g : gstate) (m m' : M unit)
    (s' : mstate) (log' : list pwmsg) (tv' itv' : nat) (hr' : hread)
    (r' : option resv) :
  thread_live g gen ->
  mnode_step (others_resv g.(gresv) cpu) (hart_agent cpu) g.(gimg)
    (MState (g.(gregs) cpu) g.(gmem) g.(gdev)) g.(glog) (g.(gtv) cpu)
    (g.(gitv) cpu) (g.(ghr) cpu) (g.(gresv) cpu) m m' s' log' tv' itv' hr' r' ->
  prim_step (HartE gen cpu m) g [] (HartE gen cpu m')
            (wb cpu g s' log' tv' itv' hr' r') [].
Proof.
  intros Hlive Hnode. unfold prim_step. left.
  exists gen, cpu, m. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. left. split; [exact Hlive|].
  unfold hart_node_step.
  exists m', s', log', tv', itv', hr', r'.
  split; [exact Hnode|]. split; [reflexivity|]. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. THE BRIDGE.  ONE INTERPRETER NODE IS ONE [mnode_step].               *)
(*                                                                         *)
(*    Where the content is, arm by arm:                                    *)
(*                                                                         *)
(*    - the PURE arms (registers, announces, the exception and translation *)
(*      markers, the cycle counter) are the same equations on both sides;  *)
(*    - a LOAD is the relaxed machine's plain/fetch/exclusive arm read at  *)
(*      the TOP of the log, where [tso_read_top_flat] says [tso_read] is   *)
(*      the flat cache -- which is the map [exec] read;                    *)
(*    - a STORE appends its message and [flat_store] keeps the cache in    *)
(*      lock-step with the append, which is the map [exec] wrote;          *)
(*    - every "blocked while another hart reserves my bytes" side          *)
(*      condition is disjointness with [∅], by [ho_alone].  This is the    *)
(*      single-hart hypothesis doing its work, and it is why no self-loop  *)
(*      arm fires.                                                         *)
(* ---------------------------------------------------------------------- *)

Lemma hart_ok_proj (cpu : CPU) (g : gstate) (s : mstate) :
  hart_ok cpu g s -> MState (g.(gregs) cpu) g.(gmem) g.(gdev) = s.
Proof.
  intros [Hr Hm Hd _ _ _ _ _ _]. destruct s as [sr sm sd]; cbn in Hr, Hm, Hd.
  rewrite Hr, Hm, Hd. reflexivity.
Qed.

Lemma hart_ok_wb_same (cpu : CPU) (g : gstate) (s s' : mstate)
    (tv' itv' : nat) (hr' : hread) (r' : option resv) :
  hart_ok cpu g s ->
  s'.(mem) = s.(mem) ->
  (tv' <= length g.(glog))%nat ->
  (itv' <= length g.(glog))%nat ->
  (hr_rv hr' <= length g.(glog))%nat ->
  (forall a, (hr_coh hr' a <= length g.(glog))%nat) ->
  hart_ok cpu (wb cpu g s' g.(glog) tv' itv' hr' r') s'.
Proof.
  intros [Hr Hm Hd Hfl Hal Htv Hitv Hrv Hcoh] Hmem Ha Hb Hc He.
  apply hart_ok_wb; try assumption.
  rewrite Hmem, <- Hm. exact Hfl.
Qed.

(* the two shapes a bound takes in the arms below *)
Lemma if_le (c : bool) (x y L : nat) :
  (x <= L)%nat -> (y <= L)%nat -> ((if c then x else y) <= L)%nat.
Proof. intros Hx Hy. destruct c; assumption. Qed.

Ltac hok_bounds :=
  repeat first
    [ assumption
    | reflexivity
    | apply Nat.max_lub
    | apply if_le
    | apply fence_post_le
    | apply own_pub_le
    | apply coh_upd_win_le
    | lia ].

Lemma enode_mnode (tick : bool) (cpu : CPU) (g : gstate) (s : mstate)
    (m m' : M unit) (s' : mstate) :
  hart_ok cpu g s ->
  enode tick m s = Some (m', s') ->
  exists log' tv' itv' hr' r',
    mnode_step (others_resv g.(gresv) cpu) (hart_agent cpu) g.(gimg)
      s g.(glog) (g.(gtv) cpu) (g.(gitv) cpu) (g.(ghr) cpu) (g.(gresv) cpu)
      m m' s' log' tv' itv' hr' r'
    /\ hart_ok cpu (wb cpu g s' log' tv' itv' hr' r') s'.
Proof.
  intros Hok Hen.
  pose proof Hok as [Hr Hm Hd Hfl Hal Htv Hitv Hrv Hcoh].
  destruct m as [y|T oc k].
  (* --- the instruction boundary ------------------------------------- *)
  - cbn [enode] in Hen. revert Hen; intros [= <- <-].
    exists g.(glog), (g.(gtv) cpu), (g.(gitv) cpu),
           (HRead (hr_rv (g.(ghr) cpu)) (hr_coh (g.(ghr) cpu)) false), None.
    split.
    + cbn [mnode_step]. exists tick. repeat (split; [reflexivity|]). reflexivity.
    + apply (hart_ok_wb_same cpu g s s); try assumption; cbn; hok_bounds.
  (* --- one outcome, dispatched by SHAPE and not by position --------- *)
  - destruct oc; cbn [enode] in Hen;
    first
      [ (* [exec] declines, and so does the relation or [VExecStuck] says
           why -- either way there is nothing to bridge *)
        discriminate Hen
      | (* PURE: registers, announces, the exception and translation
           markers, the cycle counter.  The same equations on both sides. *)
        revert Hen; intros [= <- <-];
        exists g.(glog), (g.(gtv) cpu), (g.(gitv) cpu), (g.(ghr) cpu),
               (g.(gresv) cpu);
        split;
        [ cbn [mnode_step]; repeat (split; [reflexivity|]); reflexivity
        | apply (hart_ok_wb_same cpu g s _); try assumption; hok_bounds ]
      | (* THE FENCE: the state does not move, but the views do, and the
           witnesses are whatever [mnode_step]'s own equations say. *)
        revert Hen; intros [= <- <-];
        eexists g.(glog), _, _, (g.(ghr) cpu), (g.(gresv) cpu);
        split;
        [ cbn [mnode_step]; repeat (split; [reflexivity|]); reflexivity
        | apply (hart_ok_wb_same cpu g s _); try assumption; hok_bounds ]
      | (* the two MEMORY arms are the content; they get their own bullets *)
        idtac ].
    (* --- A LOAD ----------------------------------------------------- *)
    + destruct (dev_addr (Interface.ReadReq.pa t)) eqn:Hda.
      * (* MMIO: the device answers and its state may move.  Strongly
           ordered -- no log, no view action -- so this is a PURE arm with
           a device write-back. *)
        destruct (dev_read (mdev s) (Interface.ReadReq.pa t) n)
          as [[w d']|] eqn:Hdr; [|discriminate Hen].
        revert Hen; intros [= <- <-].
        exists g.(glog), (g.(gtv) cpu), (g.(gitv) cpu), (g.(ghr) cpu),
               (g.(gresv) cpu).
        split.
        -- cbn [mnode_step]. rewrite Hda. exists w, d'.
           repeat split; first [ assumption | reflexivity ].
        -- apply (hart_ok_wb_same cpu g s _); try assumption; hok_bounds.
      * (* RAM.  [exec] read the FLAT map; the relation reads through the
           log at an admissible view, and the TOP of the log is one --
           [tso_read_top_flat] is the equation, and it holds at EVERY
           agent, which is what the fetch arm (reading at [ifetch_agent])
           needs as much as the plain one. *)
        destruct (read_bytes (mem s) (Interface.ReadReq.pa t) n)
          as [w|] eqn:Hrb; [|discriminate Hen].
        revert Hen; intros [= <- <-].
        assert (Hby : forall (a : agent) (j : nat), (N.of_nat j < n)%N ->
                  tso_read g.(gimg) g.(glog) a (length g.(glog))
                    (pa_add (Interface.ReadReq.pa t) j) = Some (nth_byte w j)).
        { intros a j Hj. rewrite tso_read_top_flat, <- Hfl, Hm.
          exact (read_bytes_spec _ _ _ _ Hrb j Hj). }
        destruct (ak_ifetch (Interface.ReadReq.access_kind t)) eqn:Hif.
        -- (* the FETCH: any view at or above the INSTRUCTION view, and the
              top is one. *)
           exists g.(glog), (g.(gtv) cpu), (g.(gitv) cpu), (g.(ghr) cpu),
                  (g.(gresv) cpu).
           split.
           ++ cbn [mnode_step]. rewrite Hda. left. split; [exact Hif|].
              exists (length g.(glog)), w.
              repeat split;
                first [ assumption | reflexivity | apply Nat.le_refl
                      | intros j Hj; apply Hby; exact Hj ].
           ++ apply (hart_ok_wb_same cpu g s _); try assumption; hok_bounds.
        -- destruct (ak_excl (Interface.ReadReq.access_kind t)) eqn:Hex.
           ++ (* THE EXCLUSIVE READ: never blocked here, because
                 [ho_alone] says no other hart reserves anything. *)
              eexists g.(glog), _, (g.(gitv) cpu), _, _.
              split.
              ** cbn [mnode_step]. rewrite Hda. right. right.
                 split; [exact Hex|]. right.
                 split; [rewrite Hal; set_solver|].
                 exists w. repeat split;
                   first [ assumption | reflexivity
                         | intros j Hj; exact (read_bytes_spec _ _ _ _ Hrb j Hj) ].
              ** apply (hart_ok_wb_same cpu g s _); try assumption;
                   cbn [hr_rv hr_coh]; hok_bounds.
           ++ (* THE PLAIN LOAD, at the top of the log. *)
              eexists g.(glog), (g.(gtv) cpu), (g.(gitv) cpu), _,
                      (g.(gresv) cpu).
              split.
              ** cbn [mnode_step]. rewrite Hda. right. left.
                 split; [exact Hif|]. split; [exact Hex|].
                 exists (length g.(glog)), w.
                 repeat split;
                   first [ assumption | reflexivity | apply Nat.le_refl
                         | intros j Hj; apply Hcoh
                         | intros j Hj; apply Hby; exact Hj ].
              ** apply (hart_ok_wb_same cpu g s _); try assumption;
                   cbn [hr_rv hr_coh]; hok_bounds.
    (* --- A STORE ---------------------------------------------------- *)
    + destruct (dev_addr (Interface.WriteReq.pa t)) eqn:Hda.
      * (* MMIO write: strongly ordered, no log. *)
        destruct (dev_write (mdev s) (Interface.WriteReq.pa t) n
                            (Interface.WriteReq.value t)) as [d'|] eqn:Hdw;
          [|discriminate Hen].
        revert Hen; intros [= <- <-].
        exists g.(glog), (g.(gtv) cpu), (g.(gitv) cpu),
               (HRead (hr_rv (g.(ghr) cpu)) (hr_coh (g.(ghr) cpu)) false), None.
        split.
        -- cbn [mnode_step]. rewrite Hda. exists d'.
           repeat split; first [ assumption | reflexivity ].
        -- apply (hart_ok_wb_same cpu g s _); try assumption;
             cbn [hr_rv hr_coh]; hok_bounds.
      * (* THE RAM WRITE.  This is the one arm where the LOG MOVES: the
           message is appended and [flat_store] keeps the flat cache in
           lock-step, which is exactly the map [exec] wrote. *)
        revert Hen; intros [= <- <-].
        eexists (g.(glog) ++ [PWMsg (snap_of (Interface.WriteReq.pa t) n
                                       (Interface.WriteReq.value t))
                                    (hart_agent cpu)]), _, (g.(gitv) cpu), _, _.
        split.
        -- cbn [mnode_step]. rewrite Hda. right.
           split; [rewrite Hal; set_solver|].
           repeat split; first [ assumption | reflexivity ].
        -- apply hart_ok_wb.
           ++ exact Hal.
           ++ cbn [mem]. unfold snap_of.
              rewrite flat_store, <- Hfl, Hm. reflexivity.
           ++ rewrite length_app; cbn [length]. hok_bounds.
           ++ rewrite length_app; cbn [length]. hok_bounds.
           ++ rewrite length_app; cbn [length]. cbn [hr_rv]. hok_bounds.
           ++ intros a. rewrite length_app; cbn [length]. cbn [hr_coh].
              pose proof (Hcoh a). hok_bounds.
Qed.

(* ---------------------------------------------------------------------- *)
(* 6. THE BRIDGE, COMPOSED: one interpreter node is one [prim_step].       *)
(*                                                                         *)
(*    This is the statement the suite has never had.  Everything the       *)
(*    harness computes is built out of [exec], and [exec] is [enode]       *)
(*    iterated; so from here a whole run lifts to a chain of [prim_step]s  *)
(*    of the hart thread, which is what [VRun.run_passes] quantifies over. *)
(* ---------------------------------------------------------------------- *)

Lemma enode_prim (tick : bool) (gen : nat) (cpu : CPU) (g : gstate)
    (s : mstate) (m m' : M unit) (s' : mstate) :
  thread_live g gen ->
  hart_ok cpu g s ->
  enode tick m s = Some (m', s') ->
  exists g', prim_step (HartE gen cpu m) g [] (HartE gen cpu m') g' []
             /\ hart_ok cpu g' s' /\ thread_live g' gen.
Proof.
  intros Hlive Hok Hen.
  destruct (enode_mnode tick cpu g s m m' s' Hok Hen)
    as (log' & tv' & itv' & hr' & r' & Hnode & Hok').
  exists (wb cpu g s' log' tv' itv' hr' r').
  split; [|split; [exact Hok'|]].
  - apply mnode_prim; [exact Hlive|].
    rewrite (hart_ok_proj cpu g s Hok). exact Hnode.
  - (* the write-back touches neither the power nor the generation *)
    unfold thread_live, wb in *; cbn [gpow ggen] in *. exact Hlive.
Qed.

(* ---------------------------------------------------------------------- *)
(* 7. [exec] IS [enode], ITERATED.                                         *)
(*                                                                         *)
(*    The harness computes with [exec], which runs a monad to its VALUE.   *)
(*    Node by node it is doing exactly what [enode] does -- the two are    *)
(*    the same match -- so an [exec] that succeeds is a CHAIN of [enode]   *)
(*    steps ending at the instruction boundary.  With section 6 that chain *)
(*    is a chain of [prim_step]s.                                          *)
(* ---------------------------------------------------------------------- *)

Definition estep (tick : bool) : relation (M unit * mstate) :=
  fun p q => enode tick (fst p) (snd p) = Some q.

(* one node, on both sides *)
Lemma exec_enode_step (tick : bool) (T : Type)
    (oc : Interface.outcome _ T) (k : T -> M unit) (s : mstate) :
  exec (Interface.Next oc k) s
  = match enode tick (Interface.Next oc k) s with
    | Some (m', s'') => exec m' s''
    | None => None
    end.
Proof.
  destruct oc; cbn [exec enode]; try reflexivity.
  - destruct (dev_addr (Interface.ReadReq.pa t)).
    + destruct (dev_read (mdev s) (Interface.ReadReq.pa t) n) as [[w d']|];
        reflexivity.
    + destruct (read_bytes (mem s) (Interface.ReadReq.pa t) n) as [w|];
        reflexivity.
  - destruct (dev_addr (Interface.WriteReq.pa t)).
    + destruct (dev_write (mdev s) (Interface.WriteReq.pa t) n
                          (Interface.WriteReq.value t)) as [d'|]; reflexivity.
    + reflexivity.
Qed.

(* ...and the successor is always a CONTINUATION, which is what lets the
   induction on the monad reach it *)
Lemma enode_next_shape (tick : bool) (T : Type)
    (oc : Interface.outcome _ T) (k : T -> M unit) (s : mstate)
    (m' : M unit) (s'' : mstate) :
  enode tick (Interface.Next oc k) s = Some (m', s'') -> exists v : T, m' = k v.
Proof.
  intros H. destruct oc; cbn [enode] in H;
    first
      [ discriminate H
      | revert H; intros [= <- <-]; eexists; reflexivity
      | idtac ].
  - destruct (dev_addr (Interface.ReadReq.pa t)) in H.
    + destruct (dev_read (mdev s) (Interface.ReadReq.pa t) n) as [[w d']|] in H;
        [revert H; intros [= <- <-]; eexists; reflexivity | discriminate H].
    + destruct (read_bytes (mem s) (Interface.ReadReq.pa t) n) as [w|] in H;
        [revert H; intros [= <- <-]; eexists; reflexivity | discriminate H].
  - destruct (dev_addr (Interface.WriteReq.pa t)) in H.
    + destruct (dev_write (mdev s) (Interface.WriteReq.pa t) n
                          (Interface.WriteReq.value t)) as [d'|] in H;
        [revert H; intros [= <- <-]; eexists; reflexivity | discriminate H].
    + revert H; intros [= <- <-]; eexists; reflexivity.
Qed.

Lemma exec_enode_rtc (tick : bool) (m : M unit) (s : mstate) (x : unit)
    (s' : mstate) :
  exec m s = Some (x, s') ->
  rtc (estep tick) (m, s) (Interface.Ret x, s').
Proof.
  revert s. induction m as [y|T oc k IH]; intros s Hex.
  - cbn [exec] in Hex. revert Hex; intros [= <- <-]. apply rtc_refl.
  - rewrite (exec_enode_step tick T oc k s) in Hex.
    destruct (enode tick (Interface.Next oc k) s) as [[m' s'']|] eqn:He;
      [|discriminate Hex].
    destruct (enode_next_shape tick T oc k s m' s'' He) as [v ->].
    eapply rtc_l; [unfold estep; cbn [fst snd]; exact He|].
    exact (IH v s'' Hex).
Qed.

(* ---------------------------------------------------------------------- *)
(* 8. A WHOLE [exec] IS A CHAIN OF THIS HART'S [prim_step]s.               *)
(* ---------------------------------------------------------------------- *)

Definition hstep (gen : nat) (cpu : CPU) : relation (M unit * gstate) :=
  fun p q => prim_step (HartE gen cpu (fst p)) (snd p) []
                       (HartE gen cpu (fst q)) (snd q) [].

Lemma estep_hstep (tick : bool) (gen : nat) (cpu : CPU) :
  forall p q : M unit * mstate, rtc (estep tick) p q ->
  forall g, thread_live g gen -> hart_ok cpu g (snd p) ->
    exists g', rtc (hstep gen cpu) (fst p, g) (fst q, g')
               /\ hart_ok cpu g' (snd q) /\ thread_live g' gen.
Proof.
  intros p q Hrtc. induction Hrtc as [p|p1 p2 p3 Hstep Hrtc IH];
    intros g Hlive Hok.
  - exists g. split; [apply rtc_refl|]. split; assumption.
  - destruct p1 as [m1 s1], p2 as [m2 s2].
    unfold estep in Hstep; cbn [fst snd] in Hstep, Hok.
    destruct (enode_prim tick gen cpu g s1 m1 m2 s2 Hlive Hok Hstep)
      as (g1 & Hps & Hok1 & Hlive1).
    destruct (IH g1 Hlive1 Hok1) as (g' & Hrtc' & Hok' & Hlive').
    exists g'. split; [|split; assumption].
    assert (Hstep1 : hstep gen cpu (m1, g) (m2, g1))
      by (unfold hstep; cbn [fst snd]; exact Hps).
    cbn [fst snd]. cbn [fst snd] in Hrtc'.
    eapply rtc_l; [exact Hstep1|exact Hrtc'].
Qed.

(* ...so an instruction the harness executed is a chain of this hart's own
   [prim_step]s, ending at the instruction boundary. *)
Lemma exec_hstep (tick : bool) (gen : nat) (cpu : CPU) (m : M unit)
    (s : mstate) (x : unit) (s' : mstate) (g : gstate) :
  exec m s = Some (x, s') ->
  thread_live g gen ->
  hart_ok cpu g s ->
  exists g', rtc (hstep gen cpu) (m, g) (Interface.Ret x, g')
             /\ hart_ok cpu g' s' /\ thread_live g' gen.
Proof.
  intros Hex Hlive Hok.
  exact (estep_hstep tick gen cpu (m, s) (Interface.Ret x, s')
           (exec_enode_rtc tick m s x s' Hex) g Hlive Hok).
Qed.

(* ---------------------------------------------------------------------- *)
(* 9. ...AND THAT CHAIN IS [nsteps] OF THE WHOLE CONFIGURATION.            *)
(*                                                                         *)
(*    A hart step forks nothing and observes nothing, so the rest of the   *)
(*    pool rides along untouched and the observation list stays empty.     *)
(*    The pool is left ABSTRACT here ([t1], [t2]): what a vtest's pool     *)
(*    actually is -- [RiscvLang.power_fork 0], every hart at an            *)
(*    instruction boundary plus the three device loops -- is the caller's  *)
(*    business, and this lemma should not know it.                         *)
(* ---------------------------------------------------------------------- *)

Lemma hstep_step (gen : nat) (cpu : CPU) (t1 t2 : list mexpr)
    (m1 m2 : M unit) (g1 g2 : gstate) :
  prim_step (HartE gen cpu m1) g1 [] (HartE gen cpu m2) g2 [] ->
  @language.step riscv_lang (t1 ++ HartE gen cpu m1 :: t2, g1) []
                            (t1 ++ HartE gen cpu m2 :: t2, g2).
Proof.
  intros Hps.
  eapply language.step_atomic; [reflexivity| |exact Hps].
  rewrite app_nil_r. reflexivity.
Qed.

(* [nsteps_l] concatenates the observation lists; both are empty here, and
   [[] ++ [] = []] holds by conversion, so this is the same constructor with
   the concatenation already done. *)
Lemma nsteps_l_nil (n : nat) (r1 r2 r3 : language.cfg riscv_lang) :
  @language.step riscv_lang r1 [] r2 ->
  @language.nsteps riscv_lang n r2 [] r3 ->
  @language.nsteps riscv_lang (S n) r1 [] r3.
Proof. intros H1 H2. exact (language.nsteps_l _ _ _ _ _ _ H1 H2). Qed.

(* ...and the same when only the STEP is silent: [[] ++ ks] is [ks] by
   conversion, so the observation list of the tail survives unchanged. *)
Lemma nsteps_l_silent (n : nat) (r1 r2 r3 : language.cfg riscv_lang)
    (ks : list mobs) :
  @language.step riscv_lang r1 [] r2 ->
  @language.nsteps riscv_lang n r2 ks r3 ->
  @language.nsteps riscv_lang (S n) r1 ks r3.
Proof.
  intros H1 H2. exact (@language.nsteps_l riscv_lang n r1 r2 r3 [] ks H1 H2).
Qed.

Lemma hstep_nsteps (gen : nat) (cpu : CPU) (t1 t2 : list mexpr) :
  forall p q : M unit * gstate, rtc (hstep gen cpu) p q ->
    exists n, @language.nsteps riscv_lang n
                (t1 ++ HartE gen cpu (fst p) :: t2, snd p) []
                (t1 ++ HartE gen cpu (fst q) :: t2, snd q).
Proof.
  intros p q Hrtc. induction Hrtc as [p|p1 p2 p3 Hstep Hrtc IH].
  - exists 0%nat. apply language.nsteps_refl.
  - destruct IH as [n Hn]. exists (S n).
    destruct p1 as [m1 g1], p2 as [m2 g2]; cbn [fst snd] in *.
    eapply nsteps_l_nil; [|exact Hn].
    apply hstep_step. unfold hstep in Hstep; cbn [fst snd] in Hstep.
    exact Hstep.
Qed.

(* THE STATEMENT THE SUITE HAS NEVER HAD: what the harness computed for one
   instruction is an execution of the language, from a configuration whose
   only distinguished part is the hart it ran. *)
Lemma exec_nsteps (tick : bool) (gen : nat) (cpu : CPU) (t1 t2 : list mexpr)
    (m : M unit) (s : mstate) (x : unit) (s' : mstate) (g : gstate) :
  exec m s = Some (x, s') ->
  thread_live g gen ->
  hart_ok cpu g s ->
  exists n g',
    @language.nsteps riscv_lang n (t1 ++ HartE gen cpu m :: t2, g) []
                     (t1 ++ HartE gen cpu (Interface.Ret x) :: t2, g')
    /\ hart_ok cpu g' s' /\ thread_live g' gen.
Proof.
  intros Hex Hlive Hok.
  destruct (exec_hstep tick gen cpu m s x s' g Hex Hlive Hok)
    as (g' & Hrtc & Hok' & Hlive').
  destruct (hstep_nsteps gen cpu t1 t2 (m, g) (Interface.Ret x, g') Hrtc)
    as [n Hn]; cbn [fst snd] in Hn.
  exists n, g'. split; [exact Hn|]. split; assumption.
Qed.

(* ---------------------------------------------------------------------- *)
(* 10. THE TEST'S OWN STARTING POINT.                                      *)
(*                                                                         *)
(*     [VRun.test_gstate] is the machine the theorem starts from and       *)
(*     [VRun.test_start] is the one the harness computes from; the         *)
(*     invariant holds between them at HART 0, which is the primary.  The  *)
(*     hart the PROGRAM sees is [hart] either way -- the gstate gives hart *)
(*     index [c] the id [hart + c], and the harness's single hart is       *)
(*     index 0 -- so this is where "the model must be started on the SAME  *)
(*     hart" becomes a proof obligation rather than a comment.             *)
(* ---------------------------------------------------------------------- *)

Lemma others_resv_none (cpu : CPU) : others_resv (fun _ => None) cpu = ∅.
Proof.
  unfold others_resv.
  assert (H : forall c : CPU,
            (if decide (c = cpu) then ∅ else resv_dom (fun _ => None) c)
            = (∅ : gset Arch.pa)).
  { intros c. unfold resv_dom. destruct (decide (c = cpu)); reflexivity. }
  induction (finite.enum CPU) as [|c cs IH]; [reflexivity|].
  rewrite fmap_cons. rewrite union_list_cons. rewrite H. rewrite IH.
  set_solver.
Qed.

(* the PRIMARY: index 0 of the pool, whose mhartid is the test's [hart] *)
Definition hart_primary : CPU := 0%fin.

(* The [mstate] the interpreter starts a test from.  [VTest.start_hart_with]
   is this with a BLANK disk; a test that seeds sectors needs the device
   fabric built from them, which nothing could express before. *)
Definition exec_start (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) : mstate :=
  MState (ColdBoot.cold_regs (SailStdpp.Values.mword_of_int hart))
         (mem_of text rs) (dev_of (img_of_sectors disk_init)).

Lemma hart_ok_test_start (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) :
  hart_ok hart_primary (test_gstate hart text rs disk_init)
                       (exec_start hart text rs disk_init).
Proof.
  unfold test_gstate, exec_start, hart_primary. constructor;
    cbn [gregs gmem gdev gimg glog gtv gitv ghr gresv sregs mem mdev].
  - (* the primary is index 0, and [hart + 0] is [hart] *)
    rewrite Z.add_0_r. reflexivity.
  - reflexivity.
  - reflexivity.
  - (* the flat cache of an empty log is the image *)
    reflexivity.
  - apply others_resv_none.
  - apply Nat.le_refl.
  - apply Nat.le_refl.
  - cbn [hr_rv]. apply Nat.le_refl.
  - intros a. cbn [hr_coh]. apply Nat.le_refl.
Qed.

(* ---------------------------------------------------------------------- *)
(* 11. THE DEVICES.  A SCHEDULE ITEM IS A DEVICE LOOP'S [prim_step].       *)
(*                                                                         *)
(*     The harness drives the fabric with [VSched.sapply], one [sitem] at  *)
(*     a time, through the fine-grained functions ([uart_tx_pop],          *)
(*     [plic_latch], ...).  The language drives it with the aggregate      *)
(*     RELATIONS ([uart_step], [disk_step], [plic_step]) at three device   *)
(*     threads.  Each item is one arm of one relation -- and this is where *)
(*     the OBSERVATIONS enter, since the UART's transmit and receive arms  *)
(*     are the only steps in the machine that emit any.                    *)
(*                                                                         *)
(*     A UART item moves [gdev] and nothing else, so the hart's invariant  *)
(*     rides through untouched: same registers, same memory, same log.     *)
(* ---------------------------------------------------------------------- *)

Definition wdev (g : gstate) (d : dev_state) : gstate :=
  GState g.(gregs) g.(gmem) d g.(ggen) g.(gpow) g.(gresv)
         g.(gimg) g.(glog) g.(gtv) g.(gitv) g.(ghr).

Lemma hart_ok_wdev (cpu : CPU) (g : gstate) (s : mstate) (d : dev_state) :
  hart_ok cpu g s -> gdev g = mdev s ->
  hart_ok cpu (wdev g d) (with_dev s d).
Proof.
  intros [Hr Hm Hd Hfl Hal Htv Hitv Hrv Hcoh] _.
  unfold wdev, with_dev. constructor;
    cbn [gregs gmem gdev gimg glog gresv gtv gitv ghr sregs mem mdev];
    assumption || reflexivity.
Qed.

Lemma thread_live_wdev (g : gstate) (d : dev_state) (gen : nat) :
  thread_live g gen -> thread_live (wdev g d) gen.
Proof. unfold thread_live, wdev; cbn [gpow ggen]. exact id. Qed.

(* THE TRANSMIT ARM: the byte leaves the port, and unless the UART is in
   LOOPBACK that is an observation.  [uart_step]'s own arm chooses the
   observation list, so the bridge does not get to. *)
Lemma sapply_uart_tx (gen : nat) (cpu : CPU) (g : gstate) (s s' : mstate) :
  thread_live g gen ->
  hart_ok cpu g s ->
  sapply SUartTx s = Some s' ->
  exists kappa g',
    prim_step (UartLoopE gen) g kappa (UartLoopE gen) g' []
    /\ hart_ok cpu g' s' /\ thread_live g' gen
    /\ g'.(gresv) = g.(gresv)
    (* a transmitted byte is an OUTPUT: it types nothing *)
    /\ obs_in kappa = [].
Proof.
  intros Hlive Hok Hap.
  pose proof (ho_dev _ _ _ Hok) as Hd.
  unfold sapply, sapply_w in Hap; cbn [mdev] in Hap.
  destruct (uart_tx_pop (duart (mdev s))) as [[b u']|] eqn:Htx;
    [|discriminate Hap].
  revert Hap; intros [= <-].
  exists (if uart_loopback (duart (gdev g)) then [] else [ObsUartOut b]),
         (wdev g (set_duart (gdev g) u')).
  split; [|split; [|split; [|split]]].
  - unfold prim_step. right. left. exists gen.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    left. split; [exact Hlive|].
    exists (set_duart (gdev g) u'). split; [|reflexivity].
    apply UartStepTx. rewrite Hd. exact Htx.
  - rewrite Hd at 1. apply (hart_ok_wdev cpu g s _ Hok Hd).
  - apply thread_live_wdev. exact Hlive.
  - reflexivity.
  - destruct (uart_loopback (duart (gdev g))); reflexivity.
Qed.

(* THE RECEIVE ARM: the host types a byte.  This is the step the test's
   [uart_input] is PINNED against -- [VRun.obs_in] reads exactly these
   events out of the trace. *)
Lemma sapply_uart_rx (gen : nat) (cpu : CPU) (b : Z) (g : gstate)
    (s s' : mstate) :
  thread_live g gen ->
  hart_ok cpu g s ->
  sapply (SUartRx b) s = Some s' ->
  exists g',
    prim_step (UartLoopE gen) g [ObsUartIn (Z_to_bv 8 b)] (UartLoopE gen) g' []
    /\ hart_ok cpu g' s' /\ thread_live g' gen
             /\ g'.(gresv) = g.(gresv).
Proof.
  intros Hlive Hok Hap.
  pose proof (ho_dev _ _ _ Hok) as Hd.
  unfold sapply, sapply_w in Hap; cbn [mdev] in Hap.
  destruct (uart_rx_push (duart (mdev s)) (Z_to_bv 8 b)) as [u'|] eqn:Hrx;
    [|discriminate Hap].
  revert Hap; intros [= <-].
  exists (wdev g (set_duart (gdev g) u')).
  split; [|split; [|split]].
  - unfold prim_step. right. left. exists gen.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    left. split; [exact Hlive|].
    exists (set_duart (gdev g) u'). split; [|reflexivity].
    apply UartStepRx. rewrite Hd. exact Hrx.
  - rewrite Hd at 1. apply (hart_ok_wdev cpu g s _ Hok Hd).
  - apply thread_live_wdev. exact Hlive.
  - reflexivity.
Qed.

(* THE LATCH: the UART's own interrupt source reaches the PLIC.  Silent. *)
Lemma sapply_uart_latch (gen : nat) (cpu : CPU) (g : gstate) (s s' : mstate) :
  thread_live g gen ->
  hart_ok cpu g s ->
  sapply (SLatch uart_irq_id) s = Some s' ->
  exists g',
    prim_step (UartLoopE gen) g [] (UartLoopE gen) g' []
    /\ hart_ok cpu g' s' /\ thread_live g' gen
             /\ g'.(gresv) = g.(gresv).
Proof.
  intros Hlive Hok Hap.
  pose proof (ho_dev _ _ _ Hok) as Hd.
  unfold sapply, sapply_w in Hap; cbn [mdev] in Hap.
  destruct (dev_irq_level (mdev s) uart_irq_id) eqn:Hlvl; [|discriminate Hap].
  destruct (plic_latch (dplic (mdev s)) uart_irq_id) as [p'|] eqn:Hlat;
    [|discriminate Hap].
  revert Hap; intros [= <-].
  exists (wdev g (set_dplic (gdev g) p')).
  split; [|split; [|split]].
  - unfold prim_step. right. left. exists gen.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    left. split; [exact Hlive|].
    exists (set_dplic (gdev g) p'). split; [|reflexivity].
    apply UartStepLatch; rewrite Hd; assumption.
  - rewrite Hd at 1. apply (hart_ok_wdev cpu g s _ Hok Hd).
  - apply thread_live_wdev. exact Hlive.
  - reflexivity.
Qed.

(* THE WIRE: the PLIC drives this hart's external S-interrupt pin.  It is
   the one device step that writes a HART's register file, so the write-back
   is the register one and the invariant is re-established at [cpu]. *)
Definition wregs (g : gstate) (gr : CPU -> regstate) : gstate :=
  GState gr g.(gmem) g.(gdev) g.(ggen) g.(gpow) g.(gresv)
         g.(gimg) g.(glog) g.(gtv) g.(gitv) g.(ghr).

Lemma sapply_wire (gen : nat) (cpu : CPU) (g : gstate) (s s' : mstate) :
  thread_live g gen ->
  hart_ok cpu g s ->
  sapply (SWire (fin_to_nat cpu)) s = Some s' ->
  exists g',
    prim_step (PlicLoopE gen) g [] (PlicLoopE gen) g' []
    /\ hart_ok cpu g' s' /\ thread_live g' gen
             /\ g'.(gresv) = g.(gresv).
Proof.
  intros Hlive Hok Hap.
  pose proof Hok as [Hr Hm Hd Hfl Hal Htv Hitv Hrv Hcoh].
  unfold sapply, sapply_w in Hap. revert Hap; intros [= <-].
  exists (wregs g (<[cpu := register_set sig_seip
                       (bool_to_bit (dev_seip g.(gdev) (fin_to_nat cpu)))
                       (g.(gregs) cpu)]> g.(gregs))).
  split; [|split; [|split]].
  - unfold prim_step. right. right. right. left. exists gen.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. left. split; [exact Hlive|].
    eexists. split; [apply PlicStepWire|reflexivity].
  - unfold wregs. constructor;
      cbn [gregs gmem gdev gimg glog gresv gtv gitv ghr sregs mem mdev];
      try assumption;
      rewrite greg_ins_eq; rewrite Hr; rewrite Hd; reflexivity.
  - unfold thread_live, wregs; cbn [gpow ggen]. exact Hlive.
  - reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 12. THE DISK.                                                           *)
(*                                                                         *)
(*     Unlike the UART, a disk step may move MEMORY and the LOG: the disk  *)
(*     masters the bus, so a DMA-writing step publishes its whole write    *)
(*     set as one authored message and updates the flat cache in lock-step *)
(*     -- the same [flat_snoc] discipline the hart's store arm uses, with  *)
(*     [disk_agent] as the author.  A step that writes nothing says [∅]    *)
(*     and the log does not move, which is exactly the fact the log arm    *)
(*     needs in order NOT to publish.                                      *)
(*                                                                         *)
(*     THE RESERVATION SIDE CONDITION is the one thing the harness cannot  *)
(*     see: a DMA may not touch a byte any hart has reserved.  Here it is  *)
(*     discharged by [all_resv = ∅] -- no hart reserves anything -- which  *)
(*     for a single-hart run means taking the INSTRUCTION BOUNDARY step    *)
(*     first (it clears the reservation) and settling the devices after.   *)
(*     The language admits that interleaving; the harness's order is only  *)
(*     one of many.                                                        *)
(* ---------------------------------------------------------------------- *)

(* stdpp's [left_id_L] does not rewrite here (the class is not registered as
   a reflexive relation in this context), so the one map fact these arms
   need is spelled out once. *)
Lemma map_union_empty_l (m : gmap Arch.pa (bv 8)) : ∅ ∪ m = m.
Proof.
  apply map_eq. intros k. rewrite lookup_union. rewrite lookup_empty.
  by destruct (m !! k).
Qed.

Lemma all_resv_of_none (gr : CPU -> option resv) (cpu : CPU) :
  others_resv gr cpu = ∅ -> gr cpu = None -> all_resv gr = ∅.
Proof.
  intros Hoth Hnone. unfold all_resv. unfold others_resv in Hoth.
  assert (Hpt : forall c : CPU,
            resv_dom gr c
            = (if decide (c = cpu) then ∅ else resv_dom gr c)).
  { intros c. destruct (decide (c = cpu)) as [->|_]; [|reflexivity].
    unfold resv_dom. rewrite Hnone. reflexivity. }
  rewrite <- Hoth. f_equal. apply list_fmap_ext. intros i c _. apply Hpt.
Qed.

(* A DISK STEP THAT WRITES NOTHING. *)
Lemma sapply_disk_nil (gen : nat) (cpu : CPU) (g : gstate) (s s' : mstate)
    (d' : dev_state) :
  thread_live g gen ->
  hart_ok cpu g s ->
  disk_step g.(gdev) g.(gmem) d' ∅ ->
  s' = with_dev s d' ->
  exists g', prim_step (DiskLoopE gen) g [] (DiskLoopE gen) g' []
             /\ hart_ok cpu g' s' /\ thread_live g' gen
             /\ g'.(gresv) = g.(gresv).
Proof.
  intros Hlive Hok Hds ->.
  pose proof Hok as [Hr Hm Hd Hfl Hal Htv Hitv Hrv Hcoh].
  exists (GState g.(gregs) (∅ ∪ g.(gmem)) d' g.(ggen) g.(gpow) g.(gresv)
                 g.(gimg) g.(glog) g.(gtv) g.(gitv) g.(ghr)).
  split; [|split; [|split]].
  - unfold prim_step. right. right. left. exists gen.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. left. split; [exact Hlive|].
    exists d', ∅, g.(glog).
    split; [exact Hds|]. split; [left; split; reflexivity|].
    split; [intros a _; rewrite map_union_empty_l; reflexivity|]. reflexivity.
  - constructor;
      cbn [gregs gmem gdev gimg glog gresv gtv gitv ghr sregs mem mdev];
      try assumption; try reflexivity;
      rewrite map_union_empty_l; assumption.
  - unfold thread_live; cbn [gpow ggen]. exact Hlive.
  - reflexivity.
Qed.

(* ...AND ONE THAT WRITES.  The write set becomes a message on the era log
   and the flat cache follows it. *)
Lemma sapply_disk_w (gen : nat) (cpu : CPU) (g : gstate) (s s' : mstate)
    (d' : dev_state) (w : gmap Arch.pa (bv 8)) :
  thread_live g gen ->
  hart_ok cpu g s ->
  all_resv g.(gresv) = ∅ ->
  disk_step g.(gdev) g.(gmem) d' w ->
  s' = MState s.(sregs) (w ∪ s.(mem)) d' ->
  exists g', prim_step (DiskLoopE gen) g [] (DiskLoopE gen) g' []
             /\ hart_ok cpu g' s' /\ thread_live g' gen
             /\ g'.(gresv) = g.(gresv).
Proof.
  intros Hlive Hok Hres Hds ->.
  pose proof Hok as [Hr Hm Hd Hfl Hal Htv Hitv Hrv Hcoh].
  destruct (decide (w = ∅)) as [->|Hne].
  - (* nothing published: the log does not move *)
    exists (GState g.(gregs) (∅ ∪ g.(gmem)) d' g.(ggen) g.(gpow) g.(gresv)
                   g.(gimg) g.(glog) g.(gtv) g.(gitv) g.(ghr)).
    split; [|split; [|split]].
    + unfold prim_step. right. right. left. exists gen.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. left. split; [exact Hlive|].
      exists d', ∅, g.(glog).
      split; [exact Hds|]. split; [left; split; reflexivity|].
      split; [intros a _; rewrite map_union_empty_l; reflexivity|]. reflexivity.
    + constructor;
        cbn [gregs gmem gdev gimg glog gresv gtv gitv ghr sregs mem mdev];
        try assumption; try reflexivity;
        repeat rewrite map_union_empty_l; assumption.
    + unfold thread_live; cbn [gpow ggen]. exact Hlive.
    + reflexivity.
  - (* one message, authored by the disk *)
    exists (GState g.(gregs) (w ∪ g.(gmem)) d' g.(ggen) g.(gpow) g.(gresv)
                   g.(gimg) (g.(glog) ++ [PWMsg w disk_agent])
                   g.(gtv) g.(gitv) g.(ghr)).
    split; [|split; [|split]].
    + unfold prim_step. right. right. left. exists gen.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. left. split; [exact Hlive|].
      exists d', w, (g.(glog) ++ [PWMsg w disk_agent]).
      split; [exact Hds|]. split; [right; split; [exact Hne|reflexivity]|].
      split; [rewrite Hres; intros a Ha; set_solver|]. reflexivity.
    + constructor;
        cbn [gregs gmem gdev gimg glog gresv gtv gitv ghr sregs mem mdev];
        try assumption; try reflexivity.
      * rewrite Hm. reflexivity.
      * rewrite flat_snoc. cbn [pm_map]. rewrite <- Hfl. reflexivity.
      * rewrite length_app; cbn [length]; lia.
      * rewrite length_app; cbn [length]; lia.
      * rewrite length_app; cbn [length]; lia.
      * intros a. rewrite length_app; cbn [length].
        pose proof (Hcoh a). lia.
    + unfold thread_live; cbn [gpow ggen]. exact Hlive.
    + reflexivity.
Qed.

(* The six items, each one arm.  The bus VIEW the relation quantifies over
   existentially is the harness's [view_of] ([VSched.view_of_ok]). *)

Lemma sapply_disk_pop (gen : nat) (cpu : CPU) (g : gstate) (s s' : mstate) :
  thread_live g gen -> hart_ok cpu g s ->
  sapply SDiskPop s = Some s' ->
  exists g', prim_step (DiskLoopE gen) g [] (DiskLoopE gen) g' []
             /\ hart_ok cpu g' s' /\ thread_live g' gen
             /\ g'.(gresv) = g.(gresv).
Proof.
  intros Hlive Hok Hap.
  pose proof (ho_dev _ _ _ Hok) as Hd. pose proof (ho_mem _ _ _ Hok) as Hm.
  unfold sapply, sapply_w in Hap; cbn [mdev] in Hap.
  destruct (virtio_pop_step (dvirtio (mdev s)) (view_of (mem s))) as [v'|]
    eqn:Hp; [|discriminate Hap].
  revert Hap; intros [= <-].
  eapply sapply_disk_nil; [exact Hlive|exact Hok| |reflexivity].
  rewrite Hd. eapply DiskStepPop; [rewrite Hm; apply view_of_ok|exact Hp].
Qed.

Lemma sapply_disk_fetch (gen : nat) (cpu : CPU) (h : Z) (g : gstate)
    (s s' : mstate) :
  thread_live g gen -> hart_ok cpu g s ->
  sapply (SDiskFetch h) s = Some s' ->
  exists g', prim_step (DiskLoopE gen) g [] (DiskLoopE gen) g' []
             /\ hart_ok cpu g' s' /\ thread_live g' gen
             /\ g'.(gresv) = g.(gresv).
Proof.
  intros Hlive Hok Hap.
  pose proof (ho_dev _ _ _ Hok) as Hd. pose proof (ho_mem _ _ _ Hok) as Hm.
  unfold sapply, sapply_w in Hap; cbn [mdev] in Hap.
  destruct (virtio_fetch_step (dvirtio (mdev s)) (view_of (mem s))
              (Z_to_bv 16 h)) as [v'|] eqn:Hp; [|discriminate Hap].
  revert Hap; intros [= <-].
  eapply sapply_disk_nil; [exact Hlive|exact Hok| |reflexivity].
  rewrite Hd. eapply DiskStepFetch; [rewrite Hm; apply view_of_ok|exact Hp].
Qed.

Lemma sapply_disk_capture (gen : nat) (cpu : CPU) (h : Z) (g : gstate)
    (s s' : mstate) :
  thread_live g gen -> hart_ok cpu g s ->
  sapply (SDiskCapture h) s = Some s' ->
  exists g', prim_step (DiskLoopE gen) g [] (DiskLoopE gen) g' []
             /\ hart_ok cpu g' s' /\ thread_live g' gen
             /\ g'.(gresv) = g.(gresv).
Proof.
  intros Hlive Hok Hap.
  pose proof (ho_dev _ _ _ Hok) as Hd. pose proof (ho_mem _ _ _ Hok) as Hm.
  unfold sapply, sapply_w in Hap; cbn [mdev] in Hap.
  destruct (virtio_capture_step (dvirtio (mdev s)) (view_of (mem s))
              (Z_to_bv 16 h)) as [v'|] eqn:Hp; [|discriminate Hap].
  revert Hap; intros [= <-].
  eapply sapply_disk_nil; [exact Hlive|exact Hok| |reflexivity].
  rewrite Hd. eapply DiskStepCapture; [rewrite Hm; apply view_of_ok|exact Hp].
Qed.

Lemma sapply_disk_drain (gen : nat) (cpu : CPU) (sec : Z) (g : gstate)
    (s s' : mstate) :
  thread_live g gen -> hart_ok cpu g s ->
  sapply (SDiskDrain sec) s = Some s' ->
  exists g', prim_step (DiskLoopE gen) g [] (DiskLoopE gen) g' []
             /\ hart_ok cpu g' s' /\ thread_live g' gen
             /\ g'.(gresv) = g.(gresv).
Proof.
  intros Hlive Hok Hap.
  pose proof (ho_dev _ _ _ Hok) as Hd.
  unfold sapply, sapply_w in Hap; cbn [mdev] in Hap.
  destruct (virtio_drain_step (dvirtio (mdev s)) sec) as [v'|] eqn:Hp;
    [|discriminate Hap].
  revert Hap; intros [= <-].
  eapply sapply_disk_nil; [exact Hlive|exact Hok| |reflexivity].
  rewrite Hd. eapply DiskStepDrain. exact Hp.
Qed.

(* the two that WRITE: the write set becomes a message on the log *)
Lemma sapply_disk_write (gen : nat) (cpu : CPU) (h : Z) (g : gstate)
    (s s' : mstate) :
  thread_live g gen -> hart_ok cpu g s -> all_resv g.(gresv) = ∅ ->
  sapply (SDiskWrite h) s = Some s' ->
  exists g', prim_step (DiskLoopE gen) g [] (DiskLoopE gen) g' []
             /\ hart_ok cpu g' s' /\ thread_live g' gen
             /\ g'.(gresv) = g.(gresv).
Proof.
  intros Hlive Hok Hres Hap.
  pose proof (ho_dev _ _ _ Hok) as Hd.
  unfold sapply, sapply_w in Hap; cbn [mdev] in Hap.
  destruct (virtio_write_step (dvirtio (mdev s)) (Z_to_bv 16 h))
    as [[v' w]|] eqn:Hp; [|discriminate Hap].
  revert Hap; intros [= <-].
  eapply sapply_disk_w; [exact Hlive|exact Hok|exact Hres| |reflexivity].
  rewrite Hd. eapply DiskStepWrite. exact Hp.
Qed.

Lemma sapply_disk_dma (gen : nat) (cpu : CPU) (h : Z) (g : gstate)
    (s s' : mstate) :
  thread_live g gen -> hart_ok cpu g s -> all_resv g.(gresv) = ∅ ->
  sapply (SDiskDma h) s = Some s' ->
  exists g', prim_step (DiskLoopE gen) g [] (DiskLoopE gen) g' []
             /\ hart_ok cpu g' s' /\ thread_live g' gen
             /\ g'.(gresv) = g.(gresv).
Proof.
  intros Hlive Hok Hres Hap.
  pose proof (ho_dev _ _ _ Hok) as Hd.
  unfold sapply, sapply_w in Hap; cbn [mdev] in Hap.
  destruct (virtio_complete_step (dvirtio (mdev s)) (Z_to_bv 16 h))
    as [[v' w]|] eqn:Hp; [|discriminate Hap].
  revert Hap; intros [= <-].
  eapply sapply_disk_w; [exact Hlive|exact Hok|exact Hres| |reflexivity].
  rewrite Hd. eapply DiskStepComplete. exact Hp.
Qed.

(* THE WILD ARM: a malformed queue lets the device write anything anywhere.
   That is the model's own side condition ([virtio_stalled]), not a licence
   to scribble whenever convenient, and it is the arm that makes "model UB
   as ANYTHING, never as nothing" pay off. *)
Lemma sapply_disk_wild (gen : nat) (cpu : CPU) (wl : list (Z * Z))
    (g : gstate) (s s' : mstate) :
  thread_live g gen -> hart_ok cpu g s -> all_resv g.(gresv) = ∅ ->
  sapply (SDiskWild wl) s = Some s' ->
  exists g', prim_step (DiskLoopE gen) g [] (DiskLoopE gen) g' []
             /\ hart_ok cpu g' s' /\ thread_live g' gen
             /\ g'.(gresv) = g.(gresv).
Proof.
  intros Hlive Hok Hres Hap.
  pose proof (ho_dev _ _ _ Hok) as Hd. pose proof (ho_mem _ _ _ Hok) as Hm.
  unfold sapply, sapply_w in Hap; cbn [mdev] in Hap.
  destruct (virtio_stalled (dvirtio (mdev s)) (view_of (mem s))) eqn:Hst;
    [|discriminate Hap].
  revert Hap; intros [= <-].
  eapply sapply_disk_w; [exact Hlive|exact Hok|exact Hres| |reflexivity].
  rewrite Hd. eapply DiskStepWild; [rewrite Hm; apply view_of_ok|exact Hst].
Qed.

(* the DISK's own interrupt source reaching the PLIC *)
Lemma sapply_disk_latch (gen : nat) (cpu : CPU) (g : gstate) (s s' : mstate) :
  thread_live g gen -> hart_ok cpu g s ->
  sapply (SLatch virtio_irq_id) s = Some s' ->
  exists g', prim_step (DiskLoopE gen) g [] (DiskLoopE gen) g' []
             /\ hart_ok cpu g' s' /\ thread_live g' gen
             /\ g'.(gresv) = g.(gresv).
Proof.
  intros Hlive Hok Hap.
  pose proof (ho_dev _ _ _ Hok) as Hd.
  unfold sapply, sapply_w in Hap; cbn [mdev] in Hap.
  destruct (dev_irq_level (mdev s) virtio_irq_id) eqn:Hlvl; [|discriminate Hap].
  destruct (plic_latch (dplic (mdev s)) virtio_irq_id) as [p'|] eqn:Hlat;
    [|discriminate Hap].
  revert Hap; intros [= <-].
  eapply sapply_disk_nil; [exact Hlive|exact Hok| |reflexivity].
  rewrite Hd. eapply DiskStepLatch; assumption.
Qed.

(* ---------------------------------------------------------------------- *)
(* 13. ONE SETTLE ROUND.                                                   *)
(*                                                                         *)
(*     Every device arm has [e' = e], so a device step leaves the THREAD   *)
(*     POOL literally unchanged -- which makes the lift to the whole       *)
(*     configuration uniform, and independent of which device stepped.     *)
(* ---------------------------------------------------------------------- *)

Lemma dev_prim_nsteps (ts : list mexpr) (e : mexpr) (g g' : gstate)
    (kappa : list mobs) :
  e ∈ ts ->
  prim_step e g kappa e g' [] ->
  @language.nsteps riscv_lang 1 (ts, g) kappa (ts, g').
Proof.
  intros Hin Hps.
  apply elem_of_list_split in Hin as (t1 & t2 & ->).
  assert (Hst : @language.step riscv_lang (t1 ++ e :: t2, g) kappa
                                          (t1 ++ e :: t2, g')).
  { eapply language.step_atomic; [reflexivity| |exact Hps].
    rewrite app_nil_r. reflexivity. }
  pose proof (@language.nsteps_l riscv_lang 0 (t1 ++ e :: t2, g)
                (t1 ++ e :: t2, g') (t1 ++ e :: t2, g') kappa [] Hst
                (@language.nsteps_refl riscv_lang _)) as Hn.
  rewrite app_nil_r in Hn. exact Hn.
Qed.

(* WHICH SCHEDULE ITEMS ARE THE DEVICES'.  [SCpu]/[SCpuTick] are the HART's
   and go through [exec_nsteps]; a latch is a device's only for its own
   interrupt source; and the wire is driven for a hart that exists.  Nothing
   else is excluded -- these are all the arms the relations have. *)
Definition dev_item (i : sitem) : bool :=
  match i with
  | SCpu _ | SCpuTick _ => false
  | SLatch src => bool_decide (src = uart_irq_id)
                  || bool_decide (src = virtio_irq_id)
  | SWire h => bool_decide (h = fin_to_nat hart_primary)
  | _ => true
  end.

Lemma obs_in_app (l1 l2 : list mobs) :
  obs_in (l1 ++ l2) = obs_in l1 ++ obs_in l2.
Proof.
  induction l1 as [|e l1' IH]; [reflexivity|].
  destruct e; cbn [obs_in app]; rewrite IH; reflexivity.
Qed.

(* WHICH ITEMS TYPE.  Only [SUartRx] puts an [ObsUartIn] in the trace, which
   is what lets a run report that it consumed no input of its own. *)
Definition item_no_input (i : sitem) : bool :=
  match i with SUartRx _ => false | _ => true end.

(* [sapply_sound]: ONE SCHEDULE ITEM IS ONE DEVICE THREAD'S [prim_step].
   The pool is unchanged because every device arm has [e' = e]. *)
Lemma sapply_dev_nsteps (gen : nat) (ts : list mexpr) (i : sitem)
    (g : gstate) (s s' : mstate) :
  UartLoopE gen ∈ ts -> DiskLoopE gen ∈ ts -> PlicLoopE gen ∈ ts ->
  thread_live g gen ->
  hart_ok hart_primary g s ->
  all_resv g.(gresv) = ∅ ->
  dev_item i = true ->
  sapply i s = Some s' ->
  exists kappa g',
    @language.nsteps riscv_lang 1 (ts, g) kappa (ts, g')
    /\ hart_ok hart_primary g' s' /\ thread_live g' gen
    /\ all_resv g'.(gresv) = ∅
    /\ (item_no_input i = true -> obs_in kappa = []).
Proof.
  intros Hu Hdk Hp Hlive Hok Hres Hdev Hap.
  (* every branch: replay that item's lemma, lift, and note [gresv] did not
     move so [all_resv] survives into the next round *)
  destruct i; cbn [dev_item] in Hdev; try discriminate Hdev.
  - (* SUartTx *)
    destruct (sapply_uart_tx gen hart_primary g s s' Hlive Hok Hap)
      as (kap & g2 & Hps & Hok2 & Hlv2 & Hg2 & Hq2).
    exists kap, g2. split; [exact (dev_prim_nsteps _ _ _ _ _ Hu Hps)|].
    split; [exact Hok2|]. split; [exact Hlv2|].
    split; [unfold all_resv; rewrite Hg2; exact Hres|].
    intros _. exact Hq2.
  - (* SUartRx *)
    destruct (sapply_uart_rx gen hart_primary _ g s s' Hlive Hok Hap)
      as (g2 & Hps & Hok2 & Hlv2 & Hg2).
    exists [ObsUartIn (Z_to_bv 8 b)], g2.
    split; [exact (dev_prim_nsteps _ _ _ _ _ Hu Hps)|].
    split; [exact Hok2|]. split; [exact Hlv2|].
    split; [unfold all_resv; rewrite Hg2; exact Hres|].
    intros H. discriminate H.
  - (* SDiskPop *)
    destruct (sapply_disk_pop gen hart_primary g s s' Hlive Hok Hap)
      as (g2 & Hps & Hok2 & Hlv2 & Hg2).
    exists (@nil mobs), g2.
    split; [exact (dev_prim_nsteps _ _ _ _ _ Hdk Hps)|].
    split; [exact Hok2|]. split; [exact Hlv2|].
    split; [unfold all_resv; rewrite Hg2; exact Hres|].
    intros _. reflexivity.
  - (* SDiskFetch *)
    destruct (sapply_disk_fetch gen hart_primary _ g s s' Hlive Hok Hap)
      as (g2 & Hps & Hok2 & Hlv2 & Hg2).
    exists (@nil mobs), g2.
    split; [exact (dev_prim_nsteps _ _ _ _ _ Hdk Hps)|].
    split; [exact Hok2|]. split; [exact Hlv2|].
    split; [unfold all_resv; rewrite Hg2; exact Hres|].
    intros _. reflexivity.
  - (* SDiskCapture *)
    destruct (sapply_disk_capture gen hart_primary _ g s s' Hlive Hok Hap)
      as (g2 & Hps & Hok2 & Hlv2 & Hg2).
    exists (@nil mobs), g2.
    split; [exact (dev_prim_nsteps _ _ _ _ _ Hdk Hps)|].
    split; [exact Hok2|]. split; [exact Hlv2|].
    split; [unfold all_resv; rewrite Hg2; exact Hres|].
    intros _. reflexivity.
  - (* SDiskWrite *)
    destruct (sapply_disk_write gen hart_primary _ g s s' Hlive Hok Hres Hap)
      as (g2 & Hps & Hok2 & Hlv2 & Hg2).
    exists (@nil mobs), g2.
    split; [exact (dev_prim_nsteps _ _ _ _ _ Hdk Hps)|].
    split; [exact Hok2|]. split; [exact Hlv2|].
    split; [unfold all_resv; rewrite Hg2; exact Hres|].
    intros _. reflexivity.
  - (* SDiskDma *)
    destruct (sapply_disk_dma gen hart_primary _ g s s' Hlive Hok Hres Hap)
      as (g2 & Hps & Hok2 & Hlv2 & Hg2).
    exists (@nil mobs), g2.
    split; [exact (dev_prim_nsteps _ _ _ _ _ Hdk Hps)|].
    split; [exact Hok2|]. split; [exact Hlv2|].
    split; [unfold all_resv; rewrite Hg2; exact Hres|].
    intros _. reflexivity.
  - (* SDiskDrain *)
    destruct (sapply_disk_drain gen hart_primary _ g s s' Hlive Hok Hap)
      as (g2 & Hps & Hok2 & Hlv2 & Hg2).
    exists (@nil mobs), g2.
    split; [exact (dev_prim_nsteps _ _ _ _ _ Hdk Hps)|].
    split; [exact Hok2|]. split; [exact Hlv2|].
    split; [unfold all_resv; rewrite Hg2; exact Hres|].
    intros _. reflexivity.
  - (* SDiskWild *)
    destruct (sapply_disk_wild gen hart_primary _ g s s' Hlive Hok Hres Hap)
      as (g2 & Hps & Hok2 & Hlv2 & Hg2).
    exists (@nil mobs), g2.
    split; [exact (dev_prim_nsteps _ _ _ _ _ Hdk Hps)|].
    split; [exact Hok2|]. split; [exact Hlv2|].
    split; [unfold all_resv; rewrite Hg2; exact Hres|].
    intros _. reflexivity.
  - (* SLatch: the UART's source or the disk's *)
    apply orb_prop in Hdev. destruct Hdev as [Hsrc|Hsrc];
      apply bool_decide_eq_true in Hsrc; subst.
    + destruct (sapply_uart_latch gen hart_primary g s s' Hlive Hok Hap)
        as (g2 & Hps & Hok2 & Hlv2 & Hg2).
      exists (@nil mobs), g2.
      split; [exact (dev_prim_nsteps _ _ _ _ _ Hu Hps)|].
      split; [exact Hok2|]. split; [exact Hlv2|].
      split; [unfold all_resv; rewrite Hg2; exact Hres|].
    intros _. reflexivity.
    + destruct (sapply_disk_latch gen hart_primary g s s' Hlive Hok Hap)
        as (g2 & Hps & Hok2 & Hlv2 & Hg2).
      exists (@nil mobs), g2.
      split; [exact (dev_prim_nsteps _ _ _ _ _ Hdk Hps)|].
      split; [exact Hok2|]. split; [exact Hlv2|].
      split; [unfold all_resv; rewrite Hg2; exact Hres|].
    intros _. reflexivity.
  - (* SWire *)
    apply bool_decide_eq_true in Hdev; subst.
    destruct (sapply_wire gen hart_primary g s s' Hlive Hok Hap)
      as (g2 & Hps & Hok2 & Hlv2 & Hg2).
    exists (@nil mobs), g2.
    split; [exact (dev_prim_nsteps _ _ _ _ _ Hp Hps)|].
    split; [exact Hok2|]. split; [exact Hlv2|].
    split; [unfold all_resv; rewrite Hg2; exact Hres|].
    intros _. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 14. A SETTLE ROUND IS ONE ITEM.                                         *)
(*                                                                         *)
(*     [settle1] tries nine arms in a fixed priority order and takes the   *)
(*     first that fires.  WHICH one fired is a fact about the harness      *)
(*     alone -- no [gstate], no [prim_step] -- so it is proved separately  *)
(*     here and the semantic step is [sapply_dev_nsteps] on the result.    *)
(* ---------------------------------------------------------------------- *)

Lemma item_of (i : sitem) (s s' : mstate) (w : gmap Arch.pa (bv 8)) :
  dev_item i = true -> sapply_w i s = Some (s', w) ->
  exists j, dev_item j = true /\ sapply j s = Some s'.
Proof.
  intros Hd He. exists i. split; [exact Hd|].
  unfold sapply. rewrite He. reflexivity.
Qed.

(* Stated on [settle1_gated_w] -- the raw round -- so the only matches in
   the goal are the ones this proof means to split.  Unfolding [settle1_gated]
   as well puts a composite match outermost, and a [repeat destruct] then
   takes the whole chain apart instead of one arm. *)
Lemma settle1_item_w (pick : virtio_state -> option Z) (s s' : mstate)
    (w : gmap Arch.pa (bv 8)) :
  settle1_gated_w pick true s = Some (s', w) ->
  exists i, dev_item i = true /\ item_no_input i = true
            /\ sapply_w i s = Some (s', w).
Proof.
  unfold settle1_gated_w, pick_at_w, drain_one_w, settle_wire_w. intros H.
  repeat (match type of H with
          | context[sapply_w ?i s] =>
              destruct (sapply_w i s) as [[?a ?wa]|] eqn:?
          | context[pick (dvirtio (mdev s))] =>
              destruct (pick (dvirtio (mdev s))) as [?h|] eqn:?
          | context[lowest_cached (dvirtio (mdev s))] =>
              destruct (lowest_cached (dvirtio (mdev s))) as [?sec|] eqn:?
          | context[wire_needed s ?k] => destruct (wire_needed s k) eqn:?
          end; try discriminate H);
    revert H; intros [= <- <-];
    match goal with
    | Heq : sapply_w ?i s = Some (_, _) |- _ =>
        exists i; split;
        [ first [reflexivity | vm_compute; reflexivity] | split;
          [ first [reflexivity | vm_compute; reflexivity] | exact Heq ] ]
    end.
Qed.

Lemma settle1_item (pick : virtio_state -> option Z) (s s' : mstate) :
  settle1_at pick s = Some s' ->
  exists i, dev_item i = true /\ item_no_input i = true
            /\ sapply i s = Some s'.
Proof.
  unfold settle1_at, settle1_gated. intros H.
  destruct (settle1_gated_w pick true s) as [[s1 w1]|] eqn:E; [|discriminate H].
  revert H; intros [= <-].
  destruct (settle1_item_w pick s s1 w1 E) as (i & Hd & Hq & Hw).
  exists i. split; [exact Hd|]. split; [exact Hq|].
  unfold sapply. rewrite Hw. reflexivity.
Qed.

Lemma settle1_nsteps (gen : nat) (ts : list mexpr) (g : gstate)
    (s s' : mstate) (pick : virtio_state -> option Z) :
  UartLoopE gen ∈ ts -> DiskLoopE gen ∈ ts -> PlicLoopE gen ∈ ts ->
  thread_live g gen ->
  hart_ok hart_primary g s ->
  all_resv g.(gresv) = ∅ ->
  settle1_at pick s = Some s' ->
  exists kappa g',
    @language.nsteps riscv_lang 1 (ts, g) kappa (ts, g')
    /\ hart_ok hart_primary g' s' /\ thread_live g' gen
    /\ all_resv g'.(gresv) = ∅ /\ obs_in kappa = [].
Proof.
  intros Hu Hdk Hp Hlive Hok Hres Hset.
  destruct (settle1_item pick s s' Hset) as (i & Hd & Hq & Hap).
  destruct (sapply_dev_nsteps gen ts i g s s' Hu Hdk Hp Hlive Hok Hres Hd Hap)
    as (kappa & g' & Hn & Hok' & Hlv & Hres' & Hqu).
  exists kappa, g'. split; [exact Hn|]. split; [exact Hok'|].
  split; [exact Hlv|]. split; [exact Hres'|]. exact (Hqu Hq).
Qed.

(* ---------------------------------------------------------------------- *)
(* 15. ...AND A WHOLE SETTLE IS A CHAIN OF THEM.                           *)
(*                                                                         *)
(*     [settle] is TOTAL -- it stops when no arm fires or the fuel runs    *)
(*     out -- so this needs no side condition: whatever the harness's      *)
(*     rounds did, the language did too.                                   *)
(* ---------------------------------------------------------------------- *)

Lemma nsteps_trans (n m : nat) (r1 r2 r3 : language.cfg riscv_lang)
    (k1 k2 : list mobs) :
  @language.nsteps riscv_lang n r1 k1 r2 ->
  @language.nsteps riscv_lang m r2 k2 r3 ->
  @language.nsteps riscv_lang (n + m) r1 (k1 ++ k2) r3.
Proof.
  intros H1. revert m r3 k2. induction H1 as [r|n' r1' r2' r3' k ks Hst Hns IH];
    intros m r3 k2 H2.
  - exact H2.
  - cbn [Nat.add]. rewrite <- app_assoc.
    exact (@language.nsteps_l riscv_lang _ _ _ _ _ _ Hst (IH _ _ _ H2)).
Qed.

Lemma settle_nsteps (gen : nat) (ts : list mexpr)
    (pick : virtio_state -> option Z) (fuel : nat) :
  UartLoopE gen ∈ ts -> DiskLoopE gen ∈ ts -> PlicLoopE gen ∈ ts ->
  forall (g : gstate) (s : mstate),
  thread_live g gen ->
  hart_ok hart_primary g s ->
  all_resv g.(gresv) = ∅ ->
  exists n kappa g',
    @language.nsteps riscv_lang n (ts, g) kappa (ts, g')
    /\ hart_ok hart_primary g' (settle_at pick fuel s)
    /\ thread_live g' gen /\ all_resv g'.(gresv) = ∅
    /\ obs_in kappa = [].
Proof.
  intros Hu Hdk Hp. induction fuel as [|f IH]; intros g s Hlive Hok Hres.
  - exists 0%nat, [], g. split; [apply language.nsteps_refl|].
    split; [exact Hok|]. split; [assumption|]. split; [assumption|reflexivity].
  - unfold settle_at, settle_gated. cbn [settle_gated_w].
    destruct (settle1_gated_w pick true s) as [[s1 w1]|] eqn:E1.
    + assert (Hs1 : settle1_at pick s = Some s1)
        by (unfold settle1_at, settle1_gated; rewrite E1; reflexivity).
      destruct (settle1_nsteps gen ts g s s1 pick Hu Hdk Hp Hlive Hok Hres Hs1)
        as (k1 & g1 & Hn1 & Hok1 & Hlv1 & Hres1 & Hq1).
      destruct (IH g1 s1 Hlv1 Hok1 Hres1)
        as (n2 & k2 & g2 & Hn2 & Hok2 & Hlv2 & Hres2 & Hq2).
      exists (1 + n2)%nat, (k1 ++ k2), g2.
      split; [exact (nsteps_trans _ _ _ _ _ _ _ Hn1 Hn2)|].
      destruct (settle_gated_w pick true f s1) as [s'' ws] eqn:E2.
      cbn [fst]. unfold settle_at, settle_gated in Hok2. rewrite E2 in Hok2.
      cbn [fst] in Hok2. split; [exact Hok2|]. split; [assumption|].
      split; [assumption|]. rewrite obs_in_app, Hq1, Hq2. reflexivity.
    + exists 0%nat, [], g. split; [apply language.nsteps_refl|].
      cbn [fst]. split; [exact Hok|]. split; [assumption|].
      split; [assumption|reflexivity].
Qed.

(* ---------------------------------------------------------------------- *)
(* 16. THE INSTRUCTION BOUNDARY, AND WHY THE DEVICES MAY THEN RUN.         *)
(*                                                                         *)
(*     The boundary is the [Ret] arm: the cycle is over, the next one      *)
(*     begins, and A DANGLING RESERVATION IS DROPPED -- it never crosses   *)
(*     an instruction.  That is what makes [all_resv = ∅] true for the     *)
(*     settle that follows, and it is why the harness's order (instruction,*)
(*     then devices) is replayed here as instruction, BOUNDARY, devices.   *)
(*     The language admits that interleaving; the boundary is a step the   *)
(*     hart has available and nothing else depends on when it is taken.    *)
(* ---------------------------------------------------------------------- *)

Lemma gresv_ins_eq (f : CPU -> option resv) (cpu : CPU) (v : option resv) :
  <[cpu := v]> f cpu = v.
Proof.
  unfold insert, gresv_insert.
  destruct (decide (cpu = cpu)) as [_|H]; [reflexivity|contradiction (H eq_refl)].
Qed.

Lemma boundary_prim (tick : bool) (gen : nat) (cpu : CPU) (g : gstate)
    (s : mstate) (u : unit) :
  thread_live g gen -> hart_ok cpu g s ->
  exists g',
    prim_step (HartE gen cpu (Interface.Ret u)) g []
              (HartE gen cpu (riscv_step tick)) g' []
    /\ hart_ok cpu g' s /\ thread_live g' gen /\ all_resv g'.(gresv) = ∅.
Proof.
  intros Hlive Hok.
  pose proof Hok as [Hr Hm Hd Hfl Hal Htv Hitv Hrv Hcoh].
  exists (wb cpu g s g.(glog) (g.(gtv) cpu) (g.(gitv) cpu)
             (HRead (hr_rv (g.(ghr) cpu)) (hr_coh (g.(ghr) cpu)) false) None).
  split; [|split; [|split]].
  - apply mnode_prim; [exact Hlive|].
    rewrite (hart_ok_proj cpu g s Hok).
    cbn [mnode_step]. exists tick. repeat (split; [reflexivity|]). reflexivity.
  - apply (hart_ok_wb_same cpu g s s); try assumption; cbn; hok_bounds.
  - unfold thread_live, wb; cbn [gpow ggen]. exact Hlive.
  - unfold wb; cbn [gresv]. apply (all_resv_of_none _ cpu).
    + rewrite others_resv_insert. exact Hal.
    + apply gresv_ins_eq.
Qed.

Lemma elem_of_pool (e x : mexpr) (t1 t2 : list mexpr) :
  e ∈ t1 ++ t2 -> e ∈ t1 ++ x :: t2.
Proof.
  intros H. apply elem_of_app. apply elem_of_app in H.
  destruct H as [H|H]; [by left|right]. apply elem_of_cons. by right.
Qed.

(* ---------------------------------------------------------------------- *)
(* 17. THE HARNESS'S OWN LOOP.                                             *)
(*                                                                         *)
(*     [eval_run_at] is: publish?  no -- one instruction, then settle the  *)
(*     devices, and again.  Each round is now three chains of [prim_step]s *)
(*     -- the instruction (section 8), the boundary (section 16), the      *)
(*     settle (section 15) -- composed by [nsteps_trans].  The hart is     *)
(*     back at [riscv_step tick] at the end of every round, so the pool is *)
(*     the same one the next round starts from, and the induction closes.  *)
(* ---------------------------------------------------------------------- *)

Lemma eval_run_nsteps (tick : bool) (gen : nat)
    (pick : virtio_state -> option Z) (t1 t2 : list mexpr) (n : nat) :
  UartLoopE gen ∈ t1 ++ t2 ->
  DiskLoopE gen ∈ t1 ++ t2 ->
  PlicLoopE gen ∈ t1 ++ t2 ->
  forall (g : gstate) (s sf : mstate),
  thread_live g gen ->
  hart_ok hart_primary g s ->
  all_resv g.(gresv) = ∅ ->
  eval_run_at pick tick n s = RDone sf ->
  exists N kappa g',
    @language.nsteps riscv_lang N
      (t1 ++ HartE gen hart_primary (riscv_step tick) :: t2, g) kappa
      (t1 ++ HartE gen hart_primary (riscv_step tick) :: t2, g')
    /\ hart_ok hart_primary g' sf /\ thread_live g' gen
    /\ obs_in kappa = [].
Proof.
  intros Hu Hdk Hp. induction n as [|n' IH]; intros g s sf Hlive Hok Hres Hev.
  - rewrite eval_run_at_O in Hev. destruct (flag_set s) eqn:Hf; [|discriminate].
    revert Hev; intros [= <-].
    exists 0%nat, [], g. split; [apply language.nsteps_refl|].
    split; [exact Hok|]. split; [exact Hlive|reflexivity].
  - rewrite eval_run_at_S in Hev. destruct (flag_set s) eqn:Hf.
    { revert Hev; intros [= <-].
      exists 0%nat, [], g. split; [apply language.nsteps_refl|].
      split; [exact Hok|]. split; [exact Hlive|reflexivity]. }
    destruct (exec_r (riscv_step tick) s) as [[u s1]|e] eqn:Hex;
      [|discriminate Hev].
    (* 1. the instruction *)
    destruct (exec_nsteps tick gen hart_primary t1 t2 (riscv_step tick) s u s1 g
                (exec_r_inl _ _ _ Hex) Hlive Hok)
      as (N1 & g1 & Hn1 & Hok1 & Hlv1).
    (* 2. the boundary, which drops the reservation *)
    destruct (boundary_prim tick gen hart_primary g1 s1 u Hlv1 Hok1)
      as (g2 & Hps2 & Hok2 & Hlv2 & Hres2).
    (* 3. the devices *)
    destruct (settle_nsteps gen
                (t1 ++ HartE gen hart_primary (riscv_step tick) :: t2)
                pick dev_fuel
                (elem_of_pool _ _ _ _ Hu) (elem_of_pool _ _ _ _ Hdk)
                (elem_of_pool _ _ _ _ Hp) g2 s1 Hlv2 Hok2 Hres2)
      as (N3 & k3 & g3 & Hn3 & Hok3 & Hlv3 & Hres3 & Hq3).
    (* 4. and around again *)
    destruct (IH g3 (settle_at pick dev_fuel s1) sf Hlv3 Hok3 Hres3 Hev)
      as (N4 & k4 & g4 & Hn4 & Hok4 & Hlv4 & Hq4).
    exists (N1 + S (N3 + N4))%nat, (k3 ++ k4), g4.
    split; [|split; [exact Hok4|split; [exact Hlv4|]]];
      [|rewrite obs_in_app, Hq3, Hq4; reflexivity].
    apply (nsteps_trans _ _ _ _ _ _ _ Hn1).
    apply (nsteps_l_silent _ _ _ _ _
             (hstep_step gen hart_primary t1 t2 (Interface.Ret u)
                (riscv_step tick) g1 g2 Hps2)).
    exact (nsteps_trans _ _ _ _ _ _ _ Hn3 Hn4).
Qed.

(* ---------------------------------------------------------------------- *)
(* 18. WHAT THE CONFIGURATION SHOWS.                                       *)
(*                                                                         *)
(*     [VRun.observed_at] reads the three channels off the [gstate]; the   *)
(*     harness reads them off its [mstate].  [hart_ok] says those are the  *)
(*     same memory and the same device fabric, so this is immediate -- and *)
(*     that is the point of having carried the invariant this far.         *)
(* ---------------------------------------------------------------------- *)

Lemma observed_at_of_hart_ok (cpu : CPU) (g : gstate) (s : mstate)
    (o : observation) :
  hart_ok cpu g s ->
  result_of (Some s) = o.(o_result) ->
  serial_of (Some s) = o.(o_uart) ->
  v_disk (dvirtio (mdev s)) = disk_of_sectors o.(o_disk) ->
  observed_at g o.
Proof.
  intros [_ Hm Hd _ _ _ _ _ _] Hres Hser Hdsk.
  unfold observed_at. split; [|split].
  - unfold result_of in Hres. rewrite Hm. exact Hres.
  - unfold serial_of in Hser. rewrite Hd. exact Hser.
  - rewrite Hd. exact Hdsk.
Qed.

(* ---------------------------------------------------------------------- *)
(* 19. THE INPUT.                                                          *)
(*                                                                         *)
(*     [settle] never delivers a byte -- its nine arms do not include      *)
(*     [SUartRx].  Input arrives ONLY through the test's own prefix, which *)
(*     is why [VRun.run_passes] can pin it: every [ObsUartIn] in the trace *)
(*     comes from an item the TEST supplied, and there is nowhere else for *)
(*     one to come from.                                                   *)
(* ---------------------------------------------------------------------- *)

(* HOW THE INTERPRETER DELIVERS THE INPUT: a byte ARRIVING is a schedule
   choice ([VSched.SUartRx]), not something the program performs, so the
   test's bytes are handed over as a prefix before it is stepped.  The
   THEOREM does not mention this -- it pins the input through the trace --
   which is exactly why this is the interpreter's business and not
   VRun.v's. *)
Definition uart_pre (bs : list (bv 8)) : list sitem :=
  List.map (fun b => SUartRx (bv_unsigned b)) bs.

Lemma srun_cons (i : sitem) (is : list sitem) (s : mstate) :
  srun (i :: is) s
  = match sapply i s with Some s1 => srun is s1 | None => None end.
Proof.
  unfold srun. cbn [foldl]. destruct (sapply i s) as [s1|]; [reflexivity|].
  induction is as [|j js IH]; [reflexivity|]. cbn [foldl]. exact IH.
Qed.

Lemma srun_uart_nsteps (gen : nat) (ts : list mexpr) (bs : list (bv 8)) :
  UartLoopE gen ∈ ts -> DiskLoopE gen ∈ ts -> PlicLoopE gen ∈ ts ->
  forall (g : gstate) (s s1 : mstate),
  thread_live g gen ->
  hart_ok hart_primary g s ->
  all_resv g.(gresv) = ∅ ->
  srun (uart_pre bs) s = Some s1 ->
  exists N g',
    @language.nsteps riscv_lang N (ts, g) (List.map ObsUartIn bs) (ts, g')
    /\ hart_ok hart_primary g' s1 /\ thread_live g' gen
    /\ all_resv g'.(gresv) = ∅.
Proof.
  intros Hu Hdk Hp. induction bs as [|b bs' IH];
    intros g s s1 Hlive Hok Hres Hrun.
  - unfold uart_pre in Hrun; cbn [List.map] in Hrun.
    unfold srun in Hrun; cbn [foldl] in Hrun.
    revert Hrun; intros [= <-].
    exists 0%nat, g. cbn [List.map].
    split; [exact (@language.nsteps_refl riscv_lang (ts, g))|].
    split; [exact Hok|]. split; assumption.
  - unfold uart_pre in Hrun; cbn [List.map] in Hrun.
    rewrite srun_cons in Hrun.
    destruct (sapply (SUartRx (bv_unsigned b)) s) as [sa|] eqn:E;
      [|discriminate Hrun].
    (* the item's OWN lemma, not the dispatcher: the trace of this step is
       exactly this byte, and the dispatcher hides it behind an existential *)
    destruct (sapply_uart_rx gen hart_primary (bv_unsigned b) g s sa
                Hlive Hok E) as (g1 & Hps & Hok1 & Hlv1 & Hg1).
    rewrite Z_to_bv_bv_unsigned in Hps.
    pose proof (dev_prim_nsteps ts (UartLoopE gen) g g1 _ Hu Hps) as Hn1.
    assert (Hres1 : all_resv g1.(gresv) = ∅)
      by (unfold all_resv; rewrite Hg1; exact Hres).
    destruct (IH g1 sa s1 Hlv1 Hok1 Hres1 Hrun)
      as (N2 & g2 & Hn2 & Hok2 & Hlv2 & Hres2).
    exists (1 + N2)%nat, g2. split; [|split; [exact Hok2|split; assumption]].
    cbn [List.map].
    replace (ObsUartIn b :: List.map ObsUartIn bs')
      with ([ObsUartIn b] ++ List.map ObsUartIn bs') by reflexivity.
    apply (nsteps_trans _ _ _ _ _ _ _ Hn1 Hn2).
Qed.

(* ...and the trace says exactly what the host typed.  Because the input is
   BYTES the round trip is the identity outright, with no range side
   condition anywhere. *)
Lemma obs_in_uart_pre (bs : list (bv 8)) :
  obs_in (List.map ObsUartIn bs) = bs.
Proof.
  induction bs as [|b bs' IH]; [reflexivity|]. cbn [List.map obs_in].
  rewrite IH. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 20. THE WHOLE THING.                                                    *)
(*                                                                         *)
(*     What the suite computes for a test -- deliver the input, then run   *)
(*     until it publishes -- is an execution of the language from the      *)
(*     test's own configuration, whose trace types exactly the test's      *)
(*     input and whose final state shows what the harness saw.  That is    *)
(*     the first disjunct of [VRun.run_passes], for one observation.       *)
(* ---------------------------------------------------------------------- *)

Lemma power_fork_split (gen : nat) :
  exists t1 t2,
    power_fork gen = t1 ++ HartE gen hart_primary (Interface.Ret tt) :: t2
    /\ UartLoopE gen ∈ t1 ++ t2
    /\ DiskLoopE gen ∈ t1 ++ t2
    /\ PlicLoopE gen ∈ t1 ++ t2.
Proof.
  unfold power_fork.
  assert (Hin : LoopE gen hart_primary ∈ (LoopE gen <$> finite.enum CPU)).
  { apply elem_of_list_fmap. exists hart_primary.
    split; [reflexivity|apply finite.elem_of_enum]. }
  apply elem_of_list_split in Hin as (u1 & u2 & Heq).
  exists u1, (u2 ++ [UartLoopE gen; DiskLoopE gen; PlicLoopE gen]).
  split; [rewrite Heq, <- app_assoc; reflexivity|].
  split; [|split];
    apply elem_of_app; right; apply elem_of_app; right;
    apply elem_of_cons; [by left| right; apply elem_of_cons; by left
                        | right; apply elem_of_cons; right;
                          apply elem_of_cons; by left].
Qed.

Theorem exec_run_exhibits (tick : bool) (pick : virtio_state -> option Z)
    (n : nat) (hart : Z) (text : list Z) (rs : list region)
    (uart_input : list (bv 8)) (disk_init : list (Z * list Z))
    (s1 sf : mstate) (o : observation) :
  srun (uart_pre uart_input) (exec_start hart text rs disk_init) = Some s1 ->
  eval_run_at pick tick n s1 = RDone sf ->
  result_of (Some sf) = o.(o_result) ->
  serial_of (Some sf) = o.(o_uart) ->
  v_disk (dvirtio (mdev sf)) = disk_of_sectors o.(o_disk) ->
  exists N l ts g,
    @language.nsteps riscv_lang N
      (test_config hart text rs disk_init) l (ts, g)
    /\ obs_in l = uart_input
    /\ observed_at g o.
Proof.
  intros Hpre Hrun Hres Hser Hdsk.
  destruct (power_fork_split 0) as (t1 & t2 & Hpool & Hu & Hdk & Hp).
  (* the machine the theorem starts from, and the invariant at it *)
  pose proof (hart_ok_test_start hart text rs disk_init) as Hok0.
  assert (Hlive0 : thread_live (test_gstate hart text rs disk_init) 0)
    by (unfold thread_live, test_gstate; cbn [gpow ggen]; split; reflexivity).
  (* 1. the boundary: the pool's hart starts AT one, and taking it is what
        empties the reservation set the devices need *)
  destruct (boundary_prim tick 0 hart_primary
              (test_gstate hart text rs disk_init)
              (exec_start hart text rs disk_init) tt Hlive0 Hok0)
    as (gb & Hpsb & Hokb & Hlvb & Hresb).
  (* 2. the input *)
  destruct (srun_uart_nsteps 0
              (t1 ++ HartE 0 hart_primary (riscv_step tick) :: t2) uart_input
              (elem_of_pool _ _ _ _ Hu) (elem_of_pool _ _ _ _ Hdk)
              (elem_of_pool _ _ _ _ Hp) gb (exec_start hart text rs disk_init)
              s1 Hlvb Hokb Hresb Hpre)
    as (N2 & g2 & Hn2 & Hok2 & Hlv2 & Hres2).
  (* 3. the run *)
  destruct (eval_run_nsteps tick 0 pick t1 t2 n Hu Hdk Hp g2 s1 sf
              Hlv2 Hok2 Hres2 Hrun)
    as (N3 & k3 & g3 & Hn3 & Hok3 & Hlv3 & Hq3).
  exists (S (N2 + N3)), (List.map ObsUartIn uart_input ++ k3),
         (t1 ++ HartE 0 hart_primary (riscv_step tick) :: t2), g3.
  split; [|split].
  - unfold test_config. rewrite Hpool.
    apply (nsteps_l_silent _ _ _ _ _
             (hstep_step 0 hart_primary t1 t2 (Interface.Ret tt)
                (riscv_step tick) _ gb Hpsb)).
    exact (nsteps_trans _ _ _ _ _ _ _ Hn2 Hn3).
  - rewrite obs_in_app, obs_in_uart_pre, Hq3. apply app_nil_r.
  - exact (observed_at_of_hart_ok hart_primary g3 sf o Hok3 Hres Hser Hdsk).
Qed.

(* ---------------------------------------------------------------------- *)
(* 21. THE OTHER ENDING: A NODE THE RELATION CANNOT STEP FROM.             *)
(*                                                                         *)
(*     A stuck run is a PASS, and a real one -- a state the relation       *)
(*     cannot leave is a state no proof over the model can reach.  What it *)
(*     is not is free: [exec_r] refusing a node is a fact about the        *)
(*     INTERPRETER, and turning it into "[mnode_step] has no transition"   *)
(*     is the converse of section 5.                                       *)
(*                                                                         *)
(*     The RAM read is the only arm where that converse has content.  The  *)
(*     interpreter read the flat map and found a byte missing; the         *)
(*     relation may read at ANY admissible view, so the argument has to be *)
(*     that the byte is missing at every one -- which it is, because a     *)
(*     byte absent from the flat cache is absent from the image AND from   *)
(*     every message, i.e. [unwritten].                                    *)
(* ---------------------------------------------------------------------- *)

Lemma flat_none_unwritten (img : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (a : Arch.pa) :
  flat img log !! a = None -> unwritten log a /\ img !! a = None.
Proof.
  induction log as [|m log IH] using rev_ind; intros H.
  - split; [|exact H]. intros m0 Hm0. apply elem_of_nil in Hm0. contradiction.
  - rewrite flat_snoc in H. apply lookup_union_None in H as [Hm Hf].
    destruct (IH Hf) as [Hu Himg]. split; [|exact Himg].
    intros m0 Hm0. apply elem_of_app in Hm0 as [Hm0|Hm0].
    + exact (Hu m0 Hm0).
    + apply elem_of_list_singleton in Hm0 as ->. exact Hm.
Qed.

Lemma tso_read_none (img : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (h : agent) (tv : nat) (a : Arch.pa) :
  flat img log !! a = None -> tso_read img log h tv a = None.
Proof.
  intros H. destruct (flat_none_unwritten img log a H) as [Hu Himg].
  rewrite (tso_read_unwritten img log h tv a Hu). exact Himg.
Qed.

Lemma read_bytes_none (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N) :
  read_bytes mm pa n = None ->
  exists j : nat, (N.of_nat j < n)%N /\ mm !! pa_add pa j = None.
Proof.
  unfold read_bytes.
  destruct (mapM (fun j : nat => mm !! pa_add pa j) (seq 0 (N.to_nat n)))
    as [bs|] eqn:Hm; [discriminate|intros _].
  apply mapM_None_1 in Hm.
  apply Exists_exists in Hm as (j & Hj & Hnone).
  apply elem_of_list_In, elem_of_seq in Hj.
  exists j. split; [lia|exact Hnone].
Qed.

(* [exec_r] walks the same nodes [enode] does *)
Lemma exec_r_enode_step (tick : bool) (T : Type)
    (oc : Interface.outcome _ T) (k : T -> M unit) (s : mstate)
    (m' : M unit) (s'' : mstate) :
  enode tick (Interface.Next oc k) s = Some (m', s'') ->
  exec_r (Interface.Next oc k) s = exec_r m' s''.
Proof.
  destruct oc; cbn [exec_r enode];
    try (intros [= <- <-]; reflexivity).
  - destruct (dev_addr (Interface.ReadReq.pa t)).
    + destruct (dev_read (mdev s) (Interface.ReadReq.pa t) n) as [[w d']|];
        [intros [= <- <-]; reflexivity|discriminate].
    + destruct (read_bytes (mem s) (Interface.ReadReq.pa t) n) as [w|];
        [intros [= <- <-]; reflexivity|discriminate].
  - destruct (dev_addr (Interface.WriteReq.pa t)).
    + destruct (dev_write (mdev s) (Interface.WriteReq.pa t) n
                          (Interface.WriteReq.value t)) as [d'|];
        [intros [= <- <-]; reflexivity|discriminate].
    + intros [= <- <-]; reflexivity.
Qed.

(* ...so a refusal is reached by a chain of nodes it DID step *)
Lemma exec_r_stuck_node (tick : bool) (m : M unit) (s : mstate) :
  exec_r m s = inr ENoStep ->
  exists m2 s2, rtc (estep tick) (m, s) (m2, s2)
                /\ enode tick m2 s2 = None
                /\ exec_r m2 s2 = inr ENoStep.
Proof.
  revert s. induction m as [y|T oc k IH]; intros s H.
  - cbn [exec_r] in H. discriminate H.
  - destruct (enode tick (Interface.Next oc k) s) as [[m' s'']|] eqn:He.
    + destruct (enode_next_shape tick T oc k s m' s'' He) as [v ->].
      rewrite (exec_r_enode_step tick T oc k s _ s'' He) in H.
      destruct (IH v s'' H) as (m2 & s2 & Hrtc & Hnone & Hstuck).
      exists m2, s2. split; [|split; assumption].
      eapply rtc_l; [unfold estep; cbn [fst snd]; exact He|exact Hrtc].
    + exists (Interface.Next oc k), s. split; [apply rtc_refl|].
      split; [exact He|exact H].
Qed.

(* THE CONVERSE OF SECTION 5, at one node.  [ENoStep] rules out [Choose],
   which is the one refusal where the relation DOES have transitions and
   only the interpreter will not pick one -- that is the whole reason
   [VExecStuck] separates the two. *)
Lemma enode_none_no_mnode (tick : bool) (cpu : CPU) (g : gstate)
    (s : mstate) (m : M unit) :
  hart_ok cpu g s ->
  enode tick m s = None ->
  exec_r m s = inr ENoStep ->
  forall m' s' log' tv' itv' hr' r',
    ~ mnode_step (others_resv g.(gresv) cpu) (hart_agent cpu) g.(gimg) s
        g.(glog) (g.(gtv) cpu) (g.(gitv) cpu) (g.(ghr) cpu) (g.(gresv) cpu)
        m m' s' log' tv' itv' hr' r'.
Proof.
  intros Hok Hen Hst m' s' log' tv' itv' hr' r' Hnode.
  pose proof Hok as [Hr Hm Hd Hfl Hal Htv Hitv Hrv Hcoh].
  (* the flat cache, as the relation's reads see it *)
  assert (Hflat : forall a, s.(mem) !! a = None ->
                    forall (h : agent) (tv : nat),
                      tso_read g.(gimg) g.(glog) h tv a = None).
  { intros a Ha h tv. apply tso_read_none. rewrite <- Hfl. rewrite Hm. exact Ha. }
  destruct m as [y|T oc k]; [cbn [enode] in Hen; discriminate Hen|].
  destruct oc; cbn [enode] in Hen; try discriminate Hen;
    cbn [mnode_step] in Hnode;
    (* [Choose]: the relation HAS transitions and [exec_r] said so, which is
       the whole reason [VExecStuck] separates it from [ENoStep].
       GenericFail / Discard / ExtraOutcome: [mnode_step] is [False]. *)
    try (first [ contradiction Hnode
               | cbn [exec_r] in Hst; discriminate Hst ]).
  - (* A LOAD that found nothing *)
    destruct (dev_addr (Interface.ReadReq.pa t)) eqn:Hda.
    + (* MMIO: the device declined, and the arm needs it to answer *)
      destruct (dev_read (mdev s) (Interface.ReadReq.pa t) n)
        as [[w d']|] eqn:Hdr; [discriminate Hen|].
      destruct Hnode as (w & d' & Hdr' & _).
      discriminate Hdr'.
    + (* RAM: some byte is in no message and not in the image, so it is
         missing at EVERY view, and all three sub-arms want it *)
      destruct (read_bytes (mem s) (Interface.ReadReq.pa t) n) as [w|] eqn:Hrb;
        [discriminate Hen|].
      destruct (read_bytes_none _ _ _ Hrb) as (j & Hj & Hnone).
      destruct Hnode as [(_ & tvn & w0 & _ & _ & Hby & _)
                        |[(_ & _ & tvn & w0 & _ & _ & _ & Hby & _)
                         |(_ & [(Hblk & _)|(_ & w0 & Hby & _)])]].
      * specialize (Hby j Hj). rewrite (Hflat _ Hnone _ tvn) in Hby.
        discriminate Hby.
      * specialize (Hby j Hj). rewrite (Hflat _ Hnone _ tvn) in Hby.
        discriminate Hby.
      * apply Hblk. rewrite Hal. set_solver.
      * specialize (Hby j Hj). rewrite Hnone in Hby. discriminate Hby.
  - (* A STORE the device declined *)
    destruct (dev_addr (Interface.WriteReq.pa t)) eqn:Hda;
      [|discriminate Hen].
    destruct (dev_write (mdev s) (Interface.WriteReq.pa t) n
                        (Interface.WriteReq.value t)) as [d'|] eqn:Hdw;
      [discriminate Hen|].
    destruct Hnode as (d' & Hdw' & _).
    discriminate Hdw'.
Qed.

(* ...and that IS "this thread has no transition": the other four arms of
   [prim_step] want a different expression, and the corpse arm wants a dead
   generation, which [thread_live] rules out. *)
Lemma thread_no_step_hart (tick : bool) (gen : nat) (cpu : CPU) (g : gstate)
    (s : mstate) (m : M unit) :
  thread_live g gen -> hart_ok cpu g s ->
  enode tick m s = None -> exec_r m s = inr ENoStep ->
  thread_no_step g (HartE gen cpu m).
Proof.
  intros Hlive Hok Hen Hst kappa e' g' efs Hps.
  unfold prim_step in Hps.
  destruct Hps as [(gen2 & cpu2 & m2 & Heq & _ & _ & Harm)
                  |[(gen2 & Heq & _)
                   |[(gen2 & Heq & _)|[(gen2 & Heq & _)|(Heq & _)]]]];
    try discriminate Heq.
  injection Heq as <- <- <-.
  destruct Harm as [(_ & Hnode)|(Hdead & _)].
  - unfold hart_node_step in Hnode.
    destruct Hnode as (m3 & s3 & log3 & tv3 & itv3 & hr3 & r3 & Hmn & _ & _).
    rewrite (hart_ok_proj cpu g s Hok) in Hmn.
    exact (enode_none_no_mnode tick cpu g s m Hok Hen Hst _ _ _ _ _ _ _ Hmn).
  - exact (Hdead Hlive).
Qed.

Lemma eval_run_stuck_nsteps (tick : bool) (gen : nat)
    (pick : virtio_state -> option Z) (t1 t2 : list mexpr) (n : nat) :
  UartLoopE gen ∈ t1 ++ t2 ->
  DiskLoopE gen ∈ t1 ++ t2 ->
  PlicLoopE gen ∈ t1 ++ t2 ->
  forall (g : gstate) (s sx : mstate),
  thread_live g gen ->
  hart_ok hart_primary g s ->
  all_resv g.(gresv) = ∅ ->
  eval_run_at pick tick n s = RStuck sx ENoStep ->
  exists N kappa g' m2 s2,
    @language.nsteps riscv_lang N
      (t1 ++ HartE gen hart_primary (riscv_step tick) :: t2, g) kappa
      (t1 ++ HartE gen hart_primary m2 :: t2, g')
    /\ hart_ok hart_primary g' s2 /\ thread_live g' gen
    /\ obs_in kappa = []
    /\ enode tick m2 s2 = None /\ exec_r m2 s2 = inr ENoStep.
Proof.
  intros Hu Hdk Hp. induction n as [|n' IH]; intros g s sx Hlive Hok Hres Hev.
  - rewrite eval_run_at_O in Hev. destruct (flag_set s); discriminate Hev.
  - rewrite eval_run_at_S in Hev. destruct (flag_set s) eqn:Hf;
      [discriminate Hev|].
    destruct (exec_r (riscv_step tick) s) as [[u s1]|e] eqn:Hex.
    + (* the instruction ran; the refusal is later *)
      destruct (exec_nsteps tick gen hart_primary t1 t2 (riscv_step tick) s u s1
                  g (exec_r_inl _ _ _ Hex) Hlive Hok)
        as (N1 & g1 & Hn1 & Hok1 & Hlv1).
      destruct (boundary_prim tick gen hart_primary g1 s1 u Hlv1 Hok1)
        as (g2 & Hps2 & Hok2 & Hlv2 & Hres2).
      destruct (settle_nsteps gen
                  (t1 ++ HartE gen hart_primary (riscv_step tick) :: t2)
                  pick dev_fuel
                  (elem_of_pool _ _ _ _ Hu) (elem_of_pool _ _ _ _ Hdk)
                  (elem_of_pool _ _ _ _ Hp) g2 s1 Hlv2 Hok2 Hres2)
        as (N3 & k3 & g3 & Hn3 & Hok3 & Hlv3 & Hres3 & Hq3).
      destruct (IH g3 (settle_at pick dev_fuel s1) sx Hlv3 Hok3 Hres3 Hev)
        as (N4 & k4 & g4 & m2 & s2 & Hn4 & Hok4 & Hlv4 & Hq4 & Hen4 & Hst4).
      exists (N1 + S (N3 + N4))%nat, (k3 ++ k4), g4, m2, s2.
      split; [|split; [exact Hok4|split; [exact Hlv4|split;
        [rewrite obs_in_app, Hq3, Hq4; reflexivity|split; assumption]]]].
      apply (nsteps_trans _ _ _ _ _ _ _ Hn1).
      apply (nsteps_l_silent _ _ _ _ _
               (hstep_step gen hart_primary t1 t2 (Interface.Ret u)
                  (riscv_step tick) g1 g2 Hps2)).
      exact (nsteps_trans _ _ _ _ _ _ _ Hn3 Hn4).
    + (* THIS round is where it stopped *)
      revert Hev; intros [= <- ->].
      destruct (exec_r_stuck_node tick (riscv_step tick) s Hex)
        as (m2 & s2 & Hrtc & Hen2 & Hst2).
      destruct (estep_hstep tick gen hart_primary (riscv_step tick, s)
                  (m2, s2) Hrtc g Hlive Hok)
        as (g' & Hh & Hok' & Hlv'); cbn [fst snd] in Hh, Hok'.
      destruct (hstep_nsteps gen hart_primary t1 t2
                  (riscv_step tick, g) (m2, g') Hh) as [N Hn];
        cbn [fst snd] in Hn.
      exists N, [], g', m2, s2.
      split; [exact Hn|]. split; [exact Hok'|]. split; [exact Hlv'|].
      split; [reflexivity|]. split; assumption.
Qed.

(* ---------------------------------------------------------------------- *)
(* 22. THE OTHER DISJUNCT, WHOLE.                                          *)
(*                                                                         *)
(*     A run the interpreter refused is a configuration of the language    *)
(*     with a thread that has no transition -- which is the second         *)
(*     disjunct of [VRun.run_passes], and the honest form of "stuck is a   *)
(*     pass": not [True], but a fact about [prim_step] at a state THIS     *)
(*     test's execution arrives at.                                        *)
(* ---------------------------------------------------------------------- *)

Theorem exec_run_no_step (tick : bool) (pick : virtio_state -> option Z)
    (n : nat) (hart : Z) (text : list Z) (rs : list region)
    (uart_input : list (bv 8)) (disk_init : list (Z * list Z))
    (s1 sx : mstate) :
  srun (uart_pre uart_input) (exec_start hart text rs disk_init) = Some s1 ->
  eval_run_at pick tick n s1 = RStuck sx ENoStep ->
  exists N l ts g e,
    @language.nsteps riscv_lang N
      (test_config hart text rs disk_init) l (ts, g)
    /\ obs_in l = uart_input
    /\ In e ts /\ thread_no_step g e.
Proof.
  intros Hpre Hrun.
  destruct (power_fork_split 0) as (t1 & t2 & Hpool & Hu & Hdk & Hp).
  pose proof (hart_ok_test_start hart text rs disk_init) as Hok0.
  assert (Hlive0 : thread_live (test_gstate hart text rs disk_init) 0)
    by (unfold thread_live, test_gstate; cbn [gpow ggen]; split; reflexivity).
  destruct (boundary_prim tick 0 hart_primary
              (test_gstate hart text rs disk_init)
              (exec_start hart text rs disk_init) tt Hlive0 Hok0)
    as (gb & Hpsb & Hokb & Hlvb & Hresb).
  destruct (srun_uart_nsteps 0
              (t1 ++ HartE 0 hart_primary (riscv_step tick) :: t2) uart_input
              (elem_of_pool _ _ _ _ Hu) (elem_of_pool _ _ _ _ Hdk)
              (elem_of_pool _ _ _ _ Hp) gb (exec_start hart text rs disk_init)
              s1 Hlvb Hokb Hresb Hpre)
    as (N2 & g2 & Hn2 & Hok2 & Hlv2 & Hres2).
  destruct (eval_run_stuck_nsteps tick 0 pick t1 t2 n Hu Hdk Hp g2 s1 sx
              Hlv2 Hok2 Hres2 Hrun)
    as (N3 & k3 & g3 & m2 & s2 & Hn3 & Hok3 & Hlv3 & Hq3 & Hen3 & Hst3).
  exists (S (N2 + N3)), (List.map ObsUartIn uart_input ++ k3),
         (t1 ++ HartE 0 hart_primary m2 :: t2), g3,
         (HartE 0 hart_primary m2).
  split; [|split; [|split]].
  - unfold test_config. rewrite Hpool.
    apply (nsteps_l_silent _ _ _ _ _
             (hstep_step 0 hart_primary t1 t2 (Interface.Ret tt)
                (riscv_step tick) _ gb Hpsb)).
    exact (nsteps_trans _ _ _ _ _ _ _ Hn2 Hn3).
  - rewrite obs_in_app, obs_in_uart_pre, Hq3. apply app_nil_r.
  - apply in_or_app. right. apply in_eq.
  - exact (thread_no_step_hart tick 0 hart_primary g3 s2 m2 Hlv3 Hok3
             Hen3 Hst3).
Qed.

(* ---------------------------------------------------------------------- *)
(* 23. THE FORM A GENERATED PROOF USES.                                    *)
(*                                                                         *)
(*     [exec_run_exhibits] wants the two intermediate states named, which  *)
(*     a generated file cannot do -- they are the run's own output, tens   *)
(*     of thousands of bytes.  These fold them into a MATCH, so the        *)
(*     premise mentions nothing a generator has to write down and reduces  *)
(*     by computation, exactly as the old one-line proofs did.             *)
(* ---------------------------------------------------------------------- *)

Definition run_result (tick : bool) (pick : virtio_state -> option Z)
    (n : nat) (hart : Z) (text : list Z) (rs : list region)
    (uart_input : list (bv 8)) (disk_init : list (Z * list Z))
  : option mstate :=
  match srun (uart_pre uart_input) (exec_start hart text rs disk_init) with
  | Some s1 => match eval_run_at pick tick n s1 with
               | RDone sf => Some sf
               | _ => None
               end
  | None => None
  end.

Theorem run_shows (tick : bool) (pick : virtio_state -> option Z) (n : nat)
    (hart : Z) (text : list Z) (rs : list region)
    (uart_input : list (bv 8)) (disk_init : list (Z * list Z))
    (o : observation) :
  match run_result tick pick n hart text rs uart_input disk_init with
  | Some sf => result_of (Some sf) = o.(o_result)
               /\ serial_of (Some sf) = o.(o_uart)
               /\ v_disk (dvirtio (mdev sf)) = disk_of_sectors o.(o_disk)
  | None => False
  end ->
  exists N l ts g,
    @language.nsteps riscv_lang N
      (test_config hart text rs disk_init) l (ts, g)
    /\ obs_in l = uart_input
    /\ observed_at g o.
Proof.
  unfold run_result.
  destruct (srun (uart_pre uart_input) (exec_start hart text rs disk_init))
    as [s1|] eqn:Hpre; [|intros []].
  destruct (eval_run_at pick tick n s1) as [sf|sf e|sf] eqn:Hrun;
    [|intros []|intros []].
  intros (Hres & Hser & Hdsk).
  exact (exec_run_exhibits tick pick n hart text rs uart_input disk_init
           s1 sf o Hpre Hrun Hres Hser Hdsk).
Qed.

Definition run_stuck (tick : bool) (pick : virtio_state -> option Z)
    (n : nat) (hart : Z) (text : list Z) (rs : list region)
    (uart_input : list (bv 8)) (disk_init : list (Z * list Z)) : bool :=
  match srun (uart_pre uart_input) (exec_start hart text rs disk_init) with
  | Some s1 => match eval_run_at pick tick n s1 with
               | RStuck _ ENoStep => true
               | _ => false
               end
  | None => false
  end.

Theorem run_no_step (tick : bool) (pick : virtio_state -> option Z) (n : nat)
    (hart : Z) (text : list Z) (rs : list region)
    (uart_input : list (bv 8)) (disk_init : list (Z * list Z)) :
  run_stuck tick pick n hart text rs uart_input disk_init = true ->
  run_no_step_at hart text rs uart_input disk_init.
Proof.
  unfold run_stuck.
  destruct (srun (uart_pre uart_input) (exec_start hart text rs disk_init))
    as [s1|] eqn:Hpre; [|discriminate].
  destruct (eval_run_at pick tick n s1) as [sf|sf e|sf] eqn:Hrun;
    [discriminate| |discriminate].
  destruct e; [|discriminate]. intros _. unfold run_no_step_at.
  exact (exec_run_no_step tick pick n hart text rs uart_input disk_init
           s1 sf Hpre Hrun).
Qed.
