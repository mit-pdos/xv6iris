(** * WeakEffSkel.v — the SHARED [exec_eff] SKELETON (M4 batch 0)

    WHAT THIS IS FOR.  A leaf's whole remaining obligation is
    [WeakCert.wP_eff tid es σ]: "the confined run of [riscv_step tick]
    succeeds, with effect trace [es]".  [WeakEff] supplied the toolkit for
    that (the composition kit, the memory frame, the empty-memory detector,
    the generalised certificates) and ONE measured artifact — the [try_step]
    wrapper, [WeakEff.exec_eff_riscv_step_hart_active].  What it did NOT
    supply is everything the wrapper stands on:

      - [run_hart_active] is a [Defs.catch_early_return] over the EARLY-RETURN
        monad, whose interpreter [RiscvTryStep.execR] is a SEPARATE [Fixpoint]
        from [RiscvExec.exec].  Every reduction of the privilege read, the
        interrupt dispatch, the fetch, the decode and the [execute] call goes
        through it.  So the instrumented interpreter needs an [execR] twin,
        with its own composition kit;
      - the two [run_hart_active] progress lemmas
        ([SmodeCore.exec_hart_active_progress_base_gen] / [_RVC_gen]) are what
        turn "fetch = this word, decode = this instruction, execute = this
        result" into one [exec] fact about the whole step.  Their mirrors are
        what turn the same three FACTS-WITH-TRACES into the step's trace.

    THIS FILE IS THOSE TWO THINGS, and nothing else:

      §1  [execR_eff] — [RiscvTryStep.execR], arm for arm, with the trace
          threaded.  The three arms that differ are the RAM read, the RAM
          write and [Barrier] — exactly the three that differ between
          [RiscvExec.exec] and [WeakCert.exec_eff], and for the same reason.
          Plus the two agreement lemmas ([execR_eff] and [execR] compute the
          same value and state; every [execR] success has SOME trace).
      §2  THE COMPOSITION KIT, mirroring [RiscvTryStep]'s: [execR_eff_bind] /
          [_bind0] / [_returnR] / [_liftR], their [_Some] / [_fwd] / [_seq]
          forward forms, and the [_nil] variants that are the DROP-IN
          replacements for [execR_bind_Some] / [execR_bind0_Some] /
          [execR_liftR_seq] when the sub-run has an empty trace (which every
          register-only sub-run does).
      §3  [exec_eff_catch_early_return] — the bridge back into the base monad,
          the one place [run_hart_active]'s trace crosses from [execR_eff] to
          [exec_eff].
      §4  THE TWO PROGRESS MIRRORS,
          [exec_eff_hart_active_progress_base_gen] / [_RVC_gen]: the SC
          scripts replayed with §2's names.  Their trace is
          [es_fetch ++ es_execute] — the decode, the landing-pad check, the
          privilege read and the interrupt dispatch are all register-only, so
          they contribute nothing, and that is the whole content of the
          statement.

    WHAT IS DELIBERATELY NOT HERE: the fetch's own [exec_eff] reduction (the
    one place the fetch's [WEread] is emitted).  It is stated here as a
    HYPOTHESIS of §4, in exactly the shape [SmodeCore]'s lemmas state their
    [exec (fetch tt) s = Some (F_Base w, s_f)] premise, so that a leaf which
    can produce the fetch's trace can close the whole step.  See the closing
    note (§5) for what producing it costs and why no semantic argument can
    replace it.

    NOTHING HERE REDUCES A MODEL FUNCTION BY COMPUTATION: every step is a
    named lemma over a bind spine, exactly as the SC originals are. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
(* [proofmode] is required for its SSREFLECT tactic language ONLY: every
   [rewrite a b c] below is the space-separated ssreflect form, as in the SC
   originals this file mirrors.  There is no Iris in this file. *)
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr.
Require Import WeakCert.
Require Import WeakEff.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec SmodeCore.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. [execR_eff] — the early-return interpreter, instrumented

    [RiscvTryStep.execR] verbatim, with [list weff] threaded.  Note the
    [ExtraOutcome] arm, which is what makes this a SEPARATE fixpoint rather
    than an instance of [exec_eff]: an early return is a VALUE of the
    interpreter, not a stuck program, and it carries the trace accumulated so
    far. *)

Fixpoint execR_eff {R X} (m : Defs.monadR R exception X) (s : mstate)
    {struct m} : option (((R + X) * mstate) * list weff) :=
  match m with
  | Interface.Ret y => Some (inr y, s, [])
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> Defs.monadR R exception X) ->
                    option (((R + X) * mstate) * list weff) with
       | Interface.RegRead r _ =>
           fun k => execR_eff (k (register_lookup r s.(sregs))) s
       | Interface.RegWrite r _ v =>
           fun k => execR_eff (k tt) (set_reg s r v)
       | Interface.MemRead n req =>
           fun k =>
             if dev_addr (Interface.ReadReq.pa req) then
               match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
               | Some (w, d') =>
                   execR_eff (k (inl (w, None))) (MState s.(sregs) s.(mem) d')
               | None => None
               end
             else
               match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
               | Some w =>
                   match execR_eff (k (inl (w, None))) s with
                   | Some (y, s', es) =>
                       Some (y, s',
                             WEread (classify (Interface.ReadReq.access_kind req))
                                    (Interface.ReadReq.pa req) n :: es)
                   | None => None
                   end
               | None => None
               end
       | Interface.MemWrite n req =>
           fun k =>
             if dev_addr (Interface.WriteReq.pa req) then
               match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                               (Interface.WriteReq.value req) with
               | Some d' =>
                   execR_eff (k (inl None)) (MState s.(sregs) s.(mem) d')
               | None => None
               end
             else
               match execR_eff (k (inl None))
                       (MState s.(sregs)
                          (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                       (Interface.WriteReq.value req))
                          s.(mdev)) with
               | Some (y, s', es) =>
                   Some (y, s',
                         WEwrite (classify (Interface.WriteReq.access_kind req))
                                 (Interface.WriteReq.pa req) n
                                 (Interface.WriteReq.value req) :: es)
               | None => None
               end
       | Interface.InstrAnnounce _    => fun k => execR_eff (k tt) s
       | Interface.BranchAnnounce _ _ => fun k => execR_eff (k tt) s
       | Interface.Barrier b          =>
           fun k => match execR_eff (k tt) s with
                    | Some (y, s', es) => Some (y, s', WEbar b :: es)
                    | None => None
                    end
       | Interface.CacheOp _          => fun k => execR_eff (k tt) s
       | Interface.TlbOp _            => fun k => execR_eff (k tt) s
       | Interface.TakeException _    => fun k => execR_eff (k tt) s
       | Interface.ReturnException _  => fun k => execR_eff (k tt) s
       | Interface.TranslationStart _ => fun k => execR_eff (k tt) s
       | Interface.TranslationEnd _   => fun k => execR_eff (k tt) s
       | Interface.CycleCount         => fun k => execR_eff (k tt) s
       | Interface.Message _          => fun k => execR_eff (k tt) s
       | Interface.GetCycleCount      => fun k => execR_eff (k 0%Z) s
       | Interface.ExtraOutcome e =>
           fun _ => match e with
                    | inl r => Some (inl r, s, [])
                    | inr _ => None
                    end
       | _ => fun _ => None   (* Choose / GenericFail / Discard: stuck *)
       end) k
  end.

(** The instrumentation is exactly that: the two interpreters agree on the
    value and the state and differ only in whether the trace is recorded.
    (The [exec_eff_exec] / [exec_exec_eff] pair of [WeakCert] §4, at the
    early-return altitude.) *)

Lemma execR_eff_execR {R X} (m : Defs.monadR R exception X) :
  forall s r s' es, execR_eff m s = Some (r, s', es) -> execR m s = Some (r, s').
Proof.
  induction m as [y|T oc k IH]; intros s r s' es Hex.
  - simpl in Hex |- *. by injection Hex as <- <- <-.
  - destruct oc; simpl in Hex |- *; try discriminate;
      try (exact (IH _ _ _ _ _ Hex));
      try (destruct (execR_eff _ _) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate];
           injection Hex as <- <- <-; exact (IH _ _ _ _ _ Hee)).
    + (* MemRead *)
      destruct (dev_addr _).
      * destruct (dev_read _ _ _) as [[w0 d']|]; [|discriminate].
        exact (IH _ _ _ _ _ Hex).
      * destruct (read_bytes _ _ _) as [w0|]; [|discriminate].
        destruct (execR_eff _ _) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-. exact (IH _ _ _ _ _ Hee).
    + (* MemWrite *)
      destruct (dev_addr _).
      * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
        exact (IH _ _ _ _ _ Hex).
      * destruct (execR_eff _ _) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-. exact (IH _ _ _ _ _ Hee).
    + (* ExtraOutcome: the early return itself *)
      match goal with
      | He : (_ + exception)%type |- _ => destruct He; [|discriminate]
      end. by injection Hex as <- <- <-.
Qed.

Lemma execR_execR_eff {R X} (m : Defs.monadR R exception X) :
  forall s r s', execR m s = Some (r, s') ->
  exists es, execR_eff m s = Some (r, s', es).
Proof.
  induction m as [y|T oc k IH]; intros s r s' Hex.
  - simpl in Hex |- *. injection Hex as <- <-. by exists [].
  - destruct oc; simpl in Hex |- *; try discriminate;
      try (exact (IH _ _ _ _ Hex));
      try (destruct (IH _ _ _ _ Hex) as [es0 Hee]; rewrite Hee /=; eexists; reflexivity).
    + (* MemRead *)
      destruct (dev_addr _).
      * destruct (dev_read _ _ _) as [[w0 d']|]; [|discriminate].
        exact (IH _ _ _ _ Hex).
      * destruct (read_bytes _ _ _) as [w0|]; [|discriminate].
        destruct (IH _ _ _ _ Hex) as [es0 Hee]. rewrite Hee /=. eexists; reflexivity.
    + (* MemWrite *)
      destruct (dev_addr _).
      * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
        exact (IH _ _ _ _ Hex).
      * destruct (IH _ _ _ _ Hex) as [es0 Hee]. rewrite Hee /=. by eexists.
    + (* ExtraOutcome *)
      match goal with
      | He : (_ + exception)%type |- _ => destruct He; [|discriminate]
      end. injection Hex as <- <-. by exists [].
Qed.

(* ====================================================================== *)
(** ** 2. THE COMPOSITION KIT

    [RiscvTryStep.execR_bind] with the trace threaded.  Read the conclusion
    as: an early return short-circuits and KEEPS its trace; a normal return
    concatenates. *)

Lemma execR_eff_bind {R X Y} (m : Defs.monadR R exception Y)
    (f : Y -> Defs.monadR R exception X) :
  forall s r st es, execR_eff m s = Some (r, st, es) ->
    execR_eff (Defs.bind m f) s =
      match r with
      | inl e => Some (inl e, st, es)
      | inr a =>
          match execR_eff (f a) st with
          | Some (y, s', es') => Some (y, s', (es ++ es')%list)
          | None => None
          end
      end.
Proof.
  induction m as [a0 | T oc k IH]; intros s r st es Hm.
  - rewrite bindR_Ret. simpl in Hm. injection Hm as <- <- <-.
    destruct (execR_eff (f a0) s) as [[[y s'] es']|]; reflexivity.
  - rewrite bindR_Next. destruct oc; simpl in Hm |- *; try discriminate;
      try (exact (IH _ _ _ _ _ Hm)).
    + (* MemRead *)
      destruct (dev_addr _).
      * destruct (dev_read _ _ _) as [[w0 d']|]; [|discriminate].
        exact (IH _ _ _ _ _ Hm).
      * destruct (read_bytes _ _ _) as [w0|]; [|discriminate].
        destruct (execR_eff (k _) s) as [[[x0 t0] es0]|] eqn:Hee;
          [|discriminate].
        injection Hm as <- <- <-. rewrite (IH _ _ _ _ _ Hee).
        destruct x0 as [e|a]; [reflexivity|].
        destruct (execR_eff (f a) t0) as [[[y s'] es']|]; reflexivity.
    + (* MemWrite *)
      destruct (dev_addr _).
      * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
        exact (IH _ _ _ _ _ Hm).
      * destruct (execR_eff (k _) _) as [[[x0 t0] es0]|] eqn:Hee;
          [|discriminate].
        injection Hm as <- <- <-. rewrite (IH _ _ _ _ _ Hee).
        destruct x0 as [e|a]; [reflexivity|].
        destruct (execR_eff (f a) t0) as [[[y s'] es']|]; reflexivity.
    + (* Barrier *)
      destruct (execR_eff (k tt) s) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
      injection Hm as <- <- <-. rewrite (IH _ _ _ _ _ Hee).
      destruct x0 as [e|a]; [reflexivity|].
      destruct (execR_eff (f a) t0) as [[[y s'] es']|]; reflexivity.
    + (* ExtraOutcome *)
      match goal with
      | He : (_ + exception)%type |- _ => destruct He; [|discriminate]
      end. by injection Hm as <- <- <-.
Qed.

Lemma execR_eff_returnR {R X} (x : X) s :
  execR_eff (Defs.returnR R x) s = Some (inr x, s, []).
Proof. reflexivity. Qed.

(** ... and the UNCONDITIONAL equations, which are what makes an existing
    [execR]-level script replay by renaming: [RiscvTryStep.execR_bind] and
    [execR_bind0] are stated this way and every SC proof rewrites with them
    directly.  The failure arm needs [execR_eff]'s completeness ([execR_eff]
    is [None] only where [execR] is). *)

Lemma execR_eff_None {R X} (m : Defs.monadR R exception X) s :
  execR_eff m s = None -> execR m s = None.
Proof.
  intros H. destruct (execR m s) as [[r s']|] eqn:E; [|reflexivity].
  destruct (execR_execR_eff m s r s' E) as [es Hee]. by rewrite Hee in H.
Qed.

Lemma execR_eff_bind_eq {R X Y} (m : Defs.monadR R exception Y)
    (f : Y -> Defs.monadR R exception X) s :
  execR_eff (Defs.bind m f) s =
    match execR_eff m s with
    | Some (inl e, st, es) => Some (inl e, st, es)
    | Some (inr a, st, es) =>
        match execR_eff (f a) st with
        | Some (y, s', es') => Some (y, s', (es ++ es')%list)
        | None => None
        end
    | None => None
    end.
Proof.
  destruct (execR_eff m s) as [[[r st] es]|] eqn:Hm.
  - rewrite (execR_eff_bind m f s r st es Hm). by destruct r.
  - destruct (execR_eff (Defs.bind m f) s) as [[[y s'] es']|] eqn:Hb;
      [|reflexivity].
    exfalso. pose proof (execR_eff_execR _ _ _ _ _ Hb) as Hbe.
    by rewrite execR_bind (execR_eff_None m s Hm) in Hbe.
Qed.

Lemma execR_eff_bind0 {R X} (m : Defs.monadR R exception unit)
    (n : Defs.monadR R exception X) :
  forall s r st es, execR_eff m s = Some (r, st, es) ->
    execR_eff (Defs.bind0 m n) s =
      match r with
      | inl e => Some (inl e, st, es)
      | inr _ =>
          match execR_eff n st with
          | Some (y, s', es') => Some (y, s', (es ++ es')%list)
          | None => None
          end
      end.
Proof.
  intros s r st es Hm. unfold Defs.bind0.
  rewrite (execR_eff_bind m _ s r st es Hm). by destruct r as [|[]].
Qed.

Lemma execR_eff_bind0_eq {R X} (m : Defs.monadR R exception unit)
    (n : Defs.monadR R exception X) s :
  execR_eff (Defs.bind0 m n) s =
    match execR_eff m s with
    | Some (inl e, st, es) => Some (inl e, st, es)
    | Some (inr _, st, es) =>
        match execR_eff n st with
        | Some (y, s', es') => Some (y, s', (es ++ es')%list)
        | None => None
        end
    | None => None
    end.
Proof.
  unfold Defs.bind0. rewrite execR_eff_bind_eq.
  by destruct (execR_eff m s) as [[[[|[]] st] es]|].
Qed.

(** A lifted base computation never early-returns, so its [execR_eff] is its
    [exec_eff] with an [inr] on the value — trace included. *)
Lemma execR_eff_liftR {R X} (m : M X) :
  forall s, execR_eff (Defs.liftR (R:=R) m) s =
    match exec_eff m s with
    | Some (x, s', es) => Some (inr x, s', es)
    | None => None
    end.
Proof.
  unfold Defs.liftR. induction m as [x0 | T oc k IH]; intros s.
  - reflexivity.
  - destruct oc; cbn [Defs.try_catch execR_eff exec_eff Defs.throw];
      try (apply IH); try reflexivity.
    + (* MemRead *)
      destruct (dev_addr _).
      * destruct (dev_read _ _ _) as [[w0 d']|]; [apply IH|reflexivity].
      * destruct (read_bytes _ _ _) as [w0|]; [|reflexivity].
        rewrite IH. by destruct (exec_eff (k _) s) as [[[x0 t0] es0]|].
    + (* MemWrite *)
      destruct (dev_addr _).
      * destruct (dev_write _ _ _ _) as [d'|]; [apply IH|reflexivity].
      * rewrite IH. by destruct (exec_eff (k _) _) as [[[x0 t0] es0]|].
    + (* Barrier *)
      rewrite IH. by destruct (exec_eff (k tt) s) as [[[x0 t0] es0]|].
Qed.

(* ---------------------------------------------------------------------- *)
(** *** 2b. The forward forms — the DROP-IN replacements

    [execR_eff_bind_nil] / [_bind0_nil] / [_liftR_seq_nil] are what an
    existing [execR]-level script replays with: every register-only sub-run
    has an empty trace, so the rewrite is name-for-name with no trace
    bookkeeping.  The [_cat] forms are for the one sub-run per instruction
    that does touch memory. *)

Lemma execR_eff_bind_cat {R X Y} (m : Defs.monadR R exception Y)
    (f : Y -> Defs.monadR R exception X) s a st es :
  execR_eff m s = Some (inr a, st, es) ->
  execR_eff (Defs.bind m f) s =
    match execR_eff (f a) st with
    | Some (y, s', es') => Some (y, s', (es ++ es')%list)
    | None => None
    end.
Proof. intros H. exact (execR_eff_bind m f s (inr a) st es H). Qed.

Lemma execR_eff_bind_nil {R X Y} (m : Defs.monadR R exception Y)
    (f : Y -> Defs.monadR R exception X) s a st :
  execR_eff m s = Some (inr a, st, []) ->
  execR_eff (Defs.bind m f) s = execR_eff (f a) st.
Proof.
  intros H. rewrite (execR_eff_bind_cat m f s a st [] H).
  by destruct (execR_eff (f a) st) as [[[y s'] es']|].
Qed.

Lemma execR_eff_bind0_cat {R X} (m : Defs.monadR R exception unit)
    (n : Defs.monadR R exception X) s st es :
  execR_eff m s = Some (inr tt, st, es) ->
  execR_eff (Defs.bind0 m n) s =
    match execR_eff n st with
    | Some (y, s', es') => Some (y, s', (es ++ es')%list)
    | None => None
    end.
Proof. intros H. exact (execR_eff_bind0 m n s (inr tt) st es H). Qed.

Lemma execR_eff_bind0_nil {R X} (m : Defs.monadR R exception unit)
    (n : Defs.monadR R exception X) s st :
  execR_eff m s = Some (inr tt, st, []) ->
  execR_eff (Defs.bind0 m n) s = execR_eff n st.
Proof.
  intros H. rewrite (execR_eff_bind0_cat m n s st [] H).
  by destruct (execR_eff n st) as [[[y s'] es']|].
Qed.

Lemma execR_eff_liftR_cat {R X Y} (m : M Y)
    (f : Y -> Defs.monadR R exception X) (s st : mstate) (x : Y) es :
  exec_eff m s = Some (x, st, es) ->
  execR_eff (Defs.bind (Defs.liftR m) f) s =
    match execR_eff (f x) st with
    | Some (y, s', es') => Some (y, s', (es ++ es')%list)
    | None => None
    end.
Proof.
  intros Hm. apply (execR_eff_bind_cat _ f s x st es).
  by rewrite execR_eff_liftR Hm.
Qed.

Lemma execR_eff_liftR_seq {R X Y} (m : M Y)
    (f : Y -> Defs.monadR R exception X) (s st : mstate) (x : Y) :
  exec_eff m s = Some (x, st, []) ->
  execR_eff (Defs.bind (Defs.liftR m) f) s = execR_eff (f x) st.
Proof.
  intros Hm. apply (execR_eff_bind_nil _ f s x st). by rewrite execR_eff_liftR Hm.
Qed.

(* ====================================================================== *)
(** ** 3. THE BRIDGE BACK: [catch_early_return]

    The one place a [run_hart_active]-shaped program's trace crosses from the
    early-return interpreter to the base one.  [RiscvTryStep.exec_catch_early_return]
    with the trace carried through both arms. *)

Lemma exec_eff_catch_early_return {X} (body : Defs.monadR X exception X) :
  forall s, exec_eff (Defs.catch_early_return body) s =
    match execR_eff body s with
    | Some (inl r, s', es) => Some (r, s', es)
    | Some (inr r, s', es) => Some (r, s', es)
    | None => None
    end.
Proof.
  unfold Defs.catch_early_return.
  induction body as [a0 | T oc k IH]; intros s.
  - reflexivity.
  - destruct oc; cbn [Defs.try_catch exec_eff execR_eff Defs.throw Defs.returnm];
      try (apply IH); try reflexivity.
    + (* MemRead *)
      destruct (dev_addr _).
      * destruct (dev_read _ _ _) as [[w0 d']|]; [apply IH|reflexivity].
      * destruct (read_bytes _ _ _) as [w0|]; [|reflexivity].
        rewrite IH. by destruct (execR_eff (k _) s) as [[[[r0|r0] t0] es0]|].
    + (* MemWrite *)
      destruct (dev_addr _).
      * destruct (dev_write _ _ _ _) as [d'|]; [apply IH|reflexivity].
      * rewrite IH. by destruct (execR_eff (k _) _) as [[[[r0|r0] t0] es0]|].
    + (* Barrier *)
      rewrite IH. by destruct (execR_eff (k tt) s) as [[[[r0|r0] t0] es0]|].
    + (* ExtraOutcome: the early return *)
      match goal with
      | He : (_ + exception)%type |- _ => destruct He; reflexivity
      end.
Qed.

(* ====================================================================== *)
(** ** 3b. The two cheap leaf twins [run_hart_active] needs

    [RiscvTryStep.exec_dispatchInterrupt_none] and [exec_is_landing_pad],
    mirrored — both are register-only, so both traces are [[]] and the scripts
    are the SC ones with the bind lemma renamed.  (The dispatch one is stated
    privilege-generically here, covering both [RiscvTryStep]'s Machine version
    and [SmodeCore]'s Supervisor one.) *)

Lemma exec_eff_dispatchInterrupt_none (p : Privilege) s :
  exec_eff (getPendingSet p) s = Some (None, s, []) ->
  exec_eff (dispatchInterrupt p) s = Some (None, s, []).
Proof.
  intros Hgp. unfold dispatchInterrupt.
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hgp). cbn match.
  apply exec_eff_returnm.
Qed.

Lemma exec_eff_is_landing_pad s :
  exec_eff (is_landing_pad_expected tt) s
  = Some (eq_vec (register_lookup elp s.(sregs))
                 (landing_pad_bits_backwards LP_EXPECTED), s, []).
Proof.
  unfold is_landing_pad_expected.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg elp s)).
  apply exec_eff_returnm.
Qed.

(* ====================================================================== *)
(** ** 4. THE TWO [run_hart_active] PROGRESS MIRRORS

    [SmodeCore.exec_hart_active_progress_base_gen] and [_RVC_gen], replayed
    with §2's names.  The premises are the SC ones with [exec] replaced by
    [exec_eff] and a trace attached; the conclusion's trace is
    [es_f ++ es_x] — the fetch's, then the [execute]'s.

    EVERYTHING ELSE CONTRIBUTES NOTHING, and that is the content:
    [cur_privilege] is a register read, [dispatchInterrupt] is register-only
    ([exec_dispatchInterrupt_none]'s premise is [getPendingSet], likewise), the
    decode is a pure function of the fetched word, the landing-pad check is a
    read of [elp], the [nextPC] write is a register write, and
    [currentlyEnabled Ext_Zca] is a [misa] read — so each of their traces is
    [[]] and the concatenations collapse.  Where a premise is register-only we
    demand the empty trace outright rather than an existential: every SC lemma
    that produces one of these facts is a pure register reduction, and
    [WeakEff.exec_eff_quiet_of_empty] cannot give [[]] (a zero-width access is
    invisible to [exec], see [WeakEff]'s header), so the empty trace is the
    honest premise, discharged by the same script that produces the SC fact. *)

Lemma exec_eff_hart_active_progress_base_gen
    (priv : Privilege) (s s_f s_x : mstate) (w : SailStdpp.Values.mword 32) (instr : instruction)
    (pc : SailStdpp.Values.mword 64) (resf : ExecutionResult) (es_f es_x : list weff) :
  register_lookup cur_privilege s.(sregs) = priv ->
  exec_eff (dispatchInterrupt priv) s = Some (None, s, []) ->
  exec_eff (fetch tt) s = Some (F_Base w, s_f, es_f) ->
  exec_eff (ext_decode w) s_f = Some (instr, s_f, []) ->
  eq_vec (register_lookup elp s_f.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  is_lpad_instruction instr = false ->
  register_lookup PC s_f.(sregs) = pc ->
  exec_eff (execute instr) (set_reg s_f nextPC (add_vec_int pc 4))
    = Some (resf, s_x, es_x) ->
  (match resf with ExecuteAs _ => False | _ => True end) ->
  exec_eff (run_hart_active 0) s
    = Some (Step_Execute (resf, zero_extend' 32 w), s_x, (es_f ++ es_x)%list).
Proof.
  intros Hpriv Hdisp Hfetch Hdec Hlpad Hnotlpad HpcF Hexec Hnotexec.
  unfold run_hart_active.
  rewrite exec_eff_catch_early_return.
  rewrite execR_eff_bind_eq execR_eff_liftR exec_eff_read_reg Hpriv. cbn match.
  rewrite execR_eff_bind_eq execR_eff_liftR Hdisp. cbn match.
  rewrite execR_eff_bind_eq. rewrite execR_eff_bind0_eq execR_eff_returnR.
  cbn match.
  rewrite execR_eff_liftR Hfetch. cbn match. cbn match.
  unfold ext_fetch_hook. cbn match. cbn beta iota.
  rewrite execR_eff_bind_eq execR_eff_liftR Hdec. cbn match.
  unfold get_config_print_instr. cbn match.
  rewrite execR_eff_bind_eq. rewrite execR_eff_bind0_eq execR_eff_returnR.
  cbn match.
  unfold Defs.and_boolM.
  rewrite execR_eff_bind_eq execR_eff_liftR exec_eff_is_landing_pad Hlpad.
  cbn match. cbn match.
  rewrite execR_eff_returnR. cbn match. cbn match.
  rewrite execR_eff_bind_eq execR_eff_liftR (exec_eff_read_reg PC) HpcF. cbn match.
  rewrite execR_eff_bind_eq. rewrite execR_eff_bind0_eq execR_eff_liftR
    exec_eff_write_reg. cbn match.
  rewrite execR_eff_liftR Hexec. cbn match. cbn match.
  rewrite execR_eff_bind_eq.
  destruct resf; cbn in Hnotexec; try contradiction;
    cbn match; rewrite execR_eff_returnR; cbn match;
    rewrite execR_eff_returnR; cbn [app]; by rewrite ?app_nil_r.
Qed.

Lemma exec_eff_hart_active_progress_RVC_gen
    (priv : Privilege) (s s_f s_x : mstate) (h : SailStdpp.Values.mword 16)
    (instr other : instruction) (pc : SailStdpp.Values.mword 64) (resf : ExecutionResult)
    (es_f es_x : list weff) :
  register_lookup cur_privilege s.(sregs) = priv ->
  exec_eff (dispatchInterrupt priv) s = Some (None, s, []) ->
  exec_eff (fetch tt) s = Some (F_RVC h, s_f, es_f) ->
  exec_eff (ext_decode_compressed h) s_f = Some (instr, s_f, []) ->
  eq_vec (register_lookup elp s_f.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  register_lookup PC s_f.(sregs) = pc ->
  exec_eff (currentlyEnabled Ext_Zca) s_f = Some (true, s_f, []) ->
  exec_eff (execute instr) (set_reg s_f nextPC (add_vec_int pc 2))
    = Some (ExecuteAs other, set_reg s_f nextPC (add_vec_int pc 2), []) ->
  exec_eff (execute other) (set_reg s_f nextPC (add_vec_int pc 2))
    = Some (resf, s_x, es_x) ->
  exec_eff (run_hart_active 0) s
    = Some (Step_Execute (resf, zero_extend' 32 h), s_x, (es_f ++ es_x)%list).
Proof.
  intros Hpriv Hdisp Hfetch Hdec Hlpad HpcF Hzca Hexec Hexec2.
  unfold run_hart_active.
  rewrite exec_eff_catch_early_return.
  rewrite execR_eff_bind_eq execR_eff_liftR exec_eff_read_reg Hpriv. cbn match.
  rewrite execR_eff_bind_eq execR_eff_liftR Hdisp. cbn match.
  rewrite execR_eff_bind_eq. rewrite execR_eff_bind0_eq execR_eff_returnR.
  cbn match.
  rewrite execR_eff_liftR Hfetch. cbn match. cbn match.
  unfold ext_fetch_hook. cbn match. cbn beta iota.
  rewrite execR_eff_bind_eq execR_eff_liftR Hdec. cbn match.
  unfold get_config_print_instr. cbn match.
  rewrite execR_eff_bind_eq. rewrite execR_eff_bind0_eq execR_eff_returnR.
  cbn match.
  rewrite execR_eff_liftR exec_eff_is_landing_pad Hlpad. cbn match.
  rewrite execR_eff_bind_eq execR_eff_liftR Hzca. cbn match.
  rewrite execR_eff_bind_eq execR_eff_liftR (exec_eff_read_reg PC) HpcF. cbn match.
  rewrite execR_eff_bind_eq. rewrite execR_eff_bind0_eq execR_eff_liftR
    exec_eff_write_reg. cbn match.
  rewrite execR_eff_liftR Hexec. cbn match. cbn match.
  rewrite execR_eff_bind_eq execR_eff_liftR Hexec2. cbn match.
  rewrite execR_eff_returnR. cbn match. cbn [app]. by rewrite ?app_nil_r.
Qed.

(* ====================================================================== *)
(** ** 5. THE ASSEMBLY: one whole [riscv_step], from the fetch's trace and
        the [execute]'s

    [WeakEff.exec_eff_riscv_step_hart_active] (the [try_step] wrapper) on top
    of §4.  This is the shape a LEAF meets: everything between the wrapper and
    the instruction — the privilege read, [should_inc_minstret], the
    [minstret_increment] pre-write, the hart-active gate, the decode, the
    landing-pad check, the [nextPC] write, the PC tick and the conditional
    [minstret] bump — is register-only and contributes NOTHING to the trace,
    so the whole step's trace is exactly

        (the fetch's) ++ (the [execute]'s)

    and a leaf owes those two facts and nothing else.  Compare
    [WeakFunnel.wwp_instr], which assembles the same chain at the [exec]
    altitude: the premise list here is that one with [exec] replaced by
    [exec_eff] and two traces attached. *)

Section StepBaseEff.
  Context (s s_exec : mstate) (w : SailStdpp.Values.mword 32)
          (i : instruction) (pc : SailStdpp.Values.mword 64) (b : bool)
          (es_f es_x : list weff).

  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.

  Hypothesis Hsi :
    exec_eff (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s, []).
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hpriv : register_lookup cur_privilege s_a.(sregs) = Machine.
  Hypothesis Hdisp : exec_eff (dispatchInterrupt Machine) s_a = Some (None, s_a, []).
  Hypothesis Hfetch : exec_eff (fetch tt) s_a = Some (F_Base w, s_a, es_f).
  Hypothesis Hdec : exec_eff (ext_decode w) s_a = Some (i, s_a, []).
  Hypothesis Hlpad : eq_vec (register_lookup elp s_a.(sregs))
                            (landing_pad_bits_backwards LP_EXPECTED) = false.
  Hypothesis Hnotlpad : is_lpad_instruction i = false.
  Hypothesis HpcF : register_lookup PC s_a.(sregs) = pc.
  Hypothesis Hexec :
    exec_eff (execute i) (set_reg s_a nextPC (add_vec_int pc 4))
      = Some (RETIRE_SUCCESS, s_exec, es_x).
  Hypothesis Hhart_exec : register_lookup hart_state s_exec.(sregs) = HART_ACTIVE tt.
  Hypothesis Hmi_exec :
    register_lookup (R_bool minstret_increment) s_exec.(sregs) = b.

  Let s_tick : mstate :=
    set_reg s_exec PC (register_lookup nextPC s_exec.(sregs)).
  Let s_final : mstate :=
    if b then set_reg s_tick minstret
                      (add_vec_int (register_lookup minstret s_tick.(sregs)) 1)
         else s_tick.

  Lemma exec_eff_riscv_step_base :
    exec_eff (riscv_step false) s = Some (tt, s_final, (es_f ++ es_x)%list).
  Proof using All.
    refine (WeakEff.exec_eff_riscv_step_hart_active s s_exec
              (zero_extend' 32 w) b _ Hsi Hhart_a _ Hhart_exec Hmi_exec).
    exact (exec_eff_hart_active_progress_base_gen Machine s_a s_a s_exec w i pc
             RETIRE_SUCCESS es_f es_x Hpriv Hdisp Hfetch Hdec Hlpad Hnotlpad
             HpcF Hexec I).
  Qed.

End StepBaseEff.

(* ---------------------------------------------------------------------- *)
(** *** 5b. The compressed twin *)

Section StepRVCEff.
  Context (s s_exec : mstate) (h : SailStdpp.Values.mword 16)
          (i other : instruction) (pc : SailStdpp.Values.mword 64) (b : bool)
          (es_f es_x : list weff).

  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.

  Hypothesis Hsi :
    exec_eff (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s, []).
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hpriv : register_lookup cur_privilege s_a.(sregs) = Machine.
  Hypothesis Hdisp : exec_eff (dispatchInterrupt Machine) s_a = Some (None, s_a, []).
  Hypothesis Hfetch : exec_eff (fetch tt) s_a = Some (F_RVC h, s_a, es_f).
  Hypothesis Hdec : exec_eff (ext_decode_compressed h) s_a = Some (i, s_a, []).
  Hypothesis Hlpad : eq_vec (register_lookup elp s_a.(sregs))
                            (landing_pad_bits_backwards LP_EXPECTED) = false.
  Hypothesis HpcF : register_lookup PC s_a.(sregs) = pc.
  Hypothesis Hzca : exec_eff (currentlyEnabled Ext_Zca) s_a = Some (true, s_a, []).
  Hypothesis Hexp :
    exec_eff (execute i) (set_reg s_a nextPC (add_vec_int pc 2))
      = Some (ExecuteAs other, set_reg s_a nextPC (add_vec_int pc 2), []).
  Hypothesis Hexec :
    exec_eff (execute other) (set_reg s_a nextPC (add_vec_int pc 2))
      = Some (RETIRE_SUCCESS, s_exec, es_x).
  Hypothesis Hhart_exec : register_lookup hart_state s_exec.(sregs) = HART_ACTIVE tt.
  Hypothesis Hmi_exec :
    register_lookup (R_bool minstret_increment) s_exec.(sregs) = b.

  Let s_tick : mstate :=
    set_reg s_exec PC (register_lookup nextPC s_exec.(sregs)).
  Let s_final : mstate :=
    if b then set_reg s_tick minstret
                      (add_vec_int (register_lookup minstret s_tick.(sregs)) 1)
         else s_tick.

  Lemma exec_eff_riscv_step_rvc :
    exec_eff (riscv_step false) s = Some (tt, s_final, (es_f ++ es_x)%list).
  Proof using All.
    refine (WeakEff.exec_eff_riscv_step_hart_active s s_exec
              (zero_extend' 32 h) b _ Hsi Hhart_a _ Hhart_exec Hmi_exec).
    exact (exec_eff_hart_active_progress_RVC_gen Machine s_a s_a s_exec h i
             other pc RETIRE_SUCCESS es_f es_x Hpriv Hdisp Hfetch Hdec Hlpad
             HpcF Hzca Hexp Hexec).
  Qed.

End StepRVCEff.

(* ====================================================================== *)
(** ** 6. THE RECIPE, NAMED — and the completeness check

    [WeakCert.wP_eff] is a conjunction under an existential over the window,
    so "produce it" is not a proof step a leaf should have to spell.  §6a
    names it; §6b is the whole batch-2 recipe in one statement; §6c is the
    check that a certificate really does come out with NO hand-peeling. *)

(** *** 6a. The window obligation, as an [apply]-able rule. *)
Lemma wP_eff_of_window (cid : nat) (es : list weff) (σ : wmstate)
    (W : gset Arch.pa) :
  wlog_wf (wm_log σ) ->
  (forall a, a ∈ W -> pa_z a <> 0) ->
  (forall a, a ∈ W -> pinned_read σ (pa_z a)) ->
  (forall tick : bool, exists t' : mstate,
     exec_eff (riscv_step tick)
       (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ)) = Some (tt, t', es) /\
     dom (mem t') ⊆ W) ->
  wP_eff (Some cid) es σ.
Proof.
  intros Hwf HW0 HWp Hrun. split; [exact Hwf|].
  exists W. split_and!; [exact HW0|exact HWp|exact Hrun].
Qed.

(** *** 6b. WHAT IS STILL MISSING BETWEEN §5 AND [wP_eff], and it is exactly
    TWO facts — both of them model reductions, neither of them per-leaf:

      (i)  THE FETCH's own [exec_eff] reduction, i.e. the [exec_eff] twin of
           [RiscvFetchExec.exec_fetch_done] (and of [WeakFunnel.exec_fetch_flat]
           over it), whose trace is the [WEread] of the text word.  This is the
           one place a [WEread] is emitted for every instruction, and NO
           semantic argument can replace it: [WeakEff]'s empty-memory detector
           does not apply (the fetch fails at the empty memory, since it reads
           the text), and a domain-growth argument cannot exclude a
           value-preserving write to a byte the map already has — which is
           M3c's recorded finding, at the fetch.  It is a syntactic replay of
           the chain [exec_fetch_done] -> [exec_fetch_bytes_4] ->
           [exec_mem_read_fetch] -> [exec_checked_mem_read_ram] ->
           [exec_read_ram_plain_4], plus the register-only sub-lemmas that
           chain names ([exec_translateAddr_identity],
           [exec_pmpCheck_machine_unlocked_ifetch4], [exec_pmaCheck_ram],
           [exec_currentlyEnabled_Ziccif], [within_clint_false] and its two
           siblings), each of which must be restated with an EMPTY trace
           because the detector can only give [quiet_trace] (a zero-width
           access is invisible to [exec] — [WeakEff]'s header) and
           [WeakEff.wcert_*_gen] need [nowrite_trace].
      (ii) THE [tick_clock] MIRROR, i.e. the [exec_eff] twin of
           [RiscvExec.exec_riscv_step_tick] over [MinstretInv.exec_tick_clock],
           which is what turns §5's [riscv_step false] fact into the
           [forall tick] shape [WeakCert.wstep_conf_eff] asks for.  It is
           register-only, so its trace is [[]] and §5's conclusion is unchanged
           by the tick.

    With those two, §6a closes [wP_eff] from a window and §6c's join makes the
    certificate; nothing else about an instruction enters. *)

(** *** 6c. COMPLETENESS CHECK: [WeakCert.wcert_load] re-derived through the
    skeleton, at the trace the skeleton produces.

    The point is not the certificate (that is [WeakCert]'s) but the JOIN: the
    trace [WeakCert.wcert_load] demands — [[the fetch's read; the data read]] —
    is EXACTLY [es_f ++ es_x] at [es_f := [fetch read]] and
    [es_x := [data read]], on the nose ([app] of two singletons), so the two
    halves meet with no adapter and no peeling.  The same join at
    [es_x := [WEwrite …]] is [wcert_store], and at
    [es_x := [WEread …; WEwrite …]] is [wcert_amo_aq]. *)

Lemma wcert_load_via_skeleton (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akf : akinfo) (pf : Arch.pa) (nf : N) (akl : akinfo) (ea : Arch.pa) :
  ak_coh akl = false ->
  wstep_cert cid pc
    (wP_eff (Some cid) ([WEread akf pf nf] ++ [WEread akl ea 4])%list)
    (wQ_load ea).
Proof. intros Hcoh. exact (wcert_load cid pc akf pf nf akl ea Hcoh). Qed.

Lemma wcert_store_via_skeleton (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akf : akinfo) (pf : Arch.pa) (nf : N) (akw : akinfo) (ea : Arch.pa)
    (v : bv 32) :
  wstep_cert cid pc
    (wP_eff (Some cid) ([WEread akf pf nf] ++ [WEwrite akw ea 4 v])%list)
    (wQ_store (Some cid) ea v).
Proof. exact (wcert_store cid pc akf pf nf akw ea v). Qed.

Lemma wcert_amo_aq_via_skeleton (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akf : akinfo) (pf : Arch.pa) (nf : N) (aka akw : akinfo) (ea : Arch.pa)
    (v : bv 32) :
  ak_coh aka = false -> ak_sync aka = true ->
  wstep_cert cid pc
    (wP_eff (Some cid)
       ([WEread akf pf nf] ++ [WEread aka ea 4; WEwrite akw ea 4 v])%list)
    (wQ_amo_aq (Some cid) ea v).
Proof.
  intros Hcoh Hsync. exact (wcert_amo_aq cid pc akf pf nf aka akw ea v Hcoh Hsync).
Qed.

(* ====================================================================== *)
(** ** 7. Soundness check

    [execR_eff] and its kit mention no model function, so they are closed
    under the global context; everything that mentions [riscv_step] /
    [run_hart_active] carries exactly the 5 rv64d platform axioms, as every
    [exec]-level lemma in this tree does. *)

Print Assumptions execR_eff_bind.
Print Assumptions exec_eff_catch_early_return.
Print Assumptions exec_eff_hart_active_progress_base_gen.
Print Assumptions exec_eff_riscv_step_base.
Print Assumptions wcert_load_via_skeleton.
