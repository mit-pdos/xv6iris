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
Require Import RiscvModelBytes RiscvExec VirtioModel DevModel ColdBoot.
Require Import RiscvLang TsoMemPa.
From VTest Require Import VTest.
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
