(** * WkFetchPeel.v — THE PEEL OF THE S-MODE FETCH (walk-bridge §8, 6a first half)

    This is the FETCH half of 6a's "S-mode fetch-chain restatement": the peel
    of the WHOLE [fetch tt] at the PC page's leaf window, obtained by
    composing [WeakKptStale.wwalk_peel_of_exports] (the peel of the
    translation) with an ORDINARY-certified tail through the landed
    single-window kit ([WeakStale] §§7–8).  The Iris absorption / ghost-
    matching half — turning the step-level register wand and log arms of
    [WeakKptStale.wtlb_res_pt_translateAddr_stale_at] into a WP rule — is
    future work and is NOT attempted here.

    Design: claude-notes/design/weak-memory-walk-bridge.md §8.

    ---------------------------------------------------------------------
    WHY §1 EXISTS (the reconnaissance finding that shapes this file).

    [WeakStale] §7's CPS kit ([wstep_ok_racy_k], [wstep_ok_racy_k_bind],
    [wstep_ok_racy_bind]) grabs a SYNTACTIC [Defs.bind m f] in the base monad
    [M].  The fetch has no such seam at [M].  The generated model reads

      fetch tt      = catch_early_return (… liftR (read_reg PC) … >>=
                        … liftR (fetch_bytes pc pc 4) >>= …)
      fetch_bytes   = catch_early_return (… >> liftR (translateAddr …) >>=
                        … >>= liftR (mem_read (InstructionFetch tt) …) >>= …)

    so [translateAddr] sits TWO [catch_early_return] levels down, under a
    [Defs.liftR], inside the EARLY-RETURN monad [Defs.monadR R exception].
    [catch_early_return] and [liftR] are [Defs.try_catch] — a fixpoint, not a
    bind — so no amount of [Defs.bind]-associativity exposes the seam, and
    the base-monad kit cannot be applied.  It is the same obstruction that
    forced [WeakEffSkel.execR_eff] and [WeakWalkStale.execR_stale] to be
    their OWN fixpoints rather than instances of [exec_eff]/[exec_stale].

    §1 is therefore the CPS peel at the early-return altitude
    ([wstep_ok_racy_kR]) plus the three transports that connect it to
    [WeakStale] §7:

      [wstep_ok_racy_kR_bind]   — the bind rule, in [monadR];
      [wstep_ok_racy_kR_liftR]  — a [liftR]-ed base-monad computation is
                                  peeled by [WeakStale]'s [wstep_ok_racy_k];
      [wstep_ok_racy_k_cer]     — and [catch_early_return] comes back.

    None of the three is an equation between monad terms (the [ExtraOutcome]
    arms genuinely differ: [liftR]'s rewraps the exception, [bind]'s keeps a
    dead continuation), which is why they are stated as implications between
    the PREDICATES, where every such arm is [True] or the early-return value.

    ---------------------------------------------------------------------
    WHAT THE FETCH DOES, and where the racy window is (finding (b)/(c)).

    (c) The pre-translation prefix is REGISTER-ONLY: six reads of [PC], the
        [ext_fetch_check_pc] extension hook (constantly [None]), the
        [or_boolM]/[and_boolM] alignment gates and [currentlyEnabled
        Ext_Ziccif] (a closed recursion with no register read at all).  No
        RAM is touched, so it peels at ANY phase and needs exactly two pure
        premises: [register_lookup PC] and the PC's 4-alignment.

    (b) A 4-ALIGNED fetch performs ONE translation and ONE 4-byte read.
        That is the case this file covers, and it is the only one that is a
        single-window consumer.

    TODO (the straddle, deferred with a precise note).  A 2-aligned-but-not-
    4-aligned [F_Base] fetch calls [fetch_bytes va va 2] and
    [fetch_bytes va (va+2) 2] — TWO translations of TWO virtual addresses,
    hence TWO leaf windows [la_lo] (for [va]) and [la_hi] (for [va+2], a
    different page whenever [va+2] crosses a page boundary), and TWO 2-byte
    text reads; the SC assembly is [SmodeCore.exec_fetch_F_Base_2_S_gen].
    That case is NOT a single-window peel and must go through [WeakStale] §9's
    SEQUENTIAL-WINDOW kit — [wstep_ok_racy_k_seq_intro] to build the nested
    object over (window₁ := la_lo, window₂ := la_hi), then
    [wrun_wexec_racy_seq2] / [wexec_of_exec_racy_seq2] at the consumer.  The
    §1 machinery below is window-generic and is what that case would peel
    with; only the two-window bookkeeping is missing.  Same for the [F_RVC]
    arms ([exec_fetch_RVC_4_S_gen] is single-window and would reuse this file
    almost verbatim; [exec_fetch_RVC_2_S_gen] is two-window).

    ---------------------------------------------------------------------
    THE TAIL.  After the seam the fetch only READS: the instruction bytes at
    the translated [pa] are kernel TEXT — single-message, hence
    [pinned_read] — and everything after them is pure decode.  So the tail is
    certifiable by an ORDINARY [WeakBridge.wstep_ok] and rides §4's embedding
    ([wstep_ok_racy_false_of_wstep_ok] at [Wp := True]) plus
    [wstep_ok_racy_phase_mono] — exactly the dance
    [wwalk_peel_of_exports]' hit-write sub-case does.

    The tail is owed at the POST-TRANSLATION states [s'], which the peel's
    bind premise quantifies as [∀ x s', wrun tid (translateAddr …) σ x s' → …].
    This file takes that quantified fact as a PREMISE ([wfetch_tail]) and
    supplies its READ half's producer in §2b ([wfetch_tail_read]: pinnedness
    of the four text bytes, their contents, and the register-only gates give
    the tail's [wstep_ok] outright, through a privilege-generic [exec_eff]
    mirror of the S-mode read chain that did not exist before — see §2b's
    own finding).  What is NOT discharged here, and why:

      - the OUTCOME of the weak translation run ([x = Ok (Physaddr pa, …)])
        is exactly what the absorption theorem's ghost half determines, and
        that half is future work;

      - THE σ → s' TRANSPORT OF PINNEDNESS IS NOT DERIVABLE FROM THE PEEL,
        and this is a finding, not an omission.  [WeakCert.pinned_read_mono]
        wants the log UNCHANGED; a walking fetch's run may append the CAS's
        message, so what one needs is "the appended messages do not write
        the text bytes".  [WeakInterp.wrun_log_app]/[_log_tid] give the
        append shape and the writer's tid but say NOTHING about addresses,
        and the peel cannot supply them either: this consumer runs at
        [D := wD_any] and [W := True], so [wstep_ok_racy]'s write arm
        constrains no address at all, and the [exec_stale] exports (which DO
        pin the write to [la]) reach the weak run only through
        [WeakRacy.exec_of_wrun_racy], which is stated at [W := False].  The
        fact therefore has to come from the Iris side — the absorption
        theorem's log arm, which already says the walk appends at most the
        one PTE message at [la] — which is precisely the ghost half above.
        [wfetch_tail] is the interface at which the two meet. *)
From Stdlib Require Import ZArith Bool Lia Wf_nat.
From stdpp Require Import gmap list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff.
Require Import WeakEffSkel WeakLeafEffCommon WeakFetchEff.
Require Import WeakRacy WeakVarCert WeakStale WeakWalkStale.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree.
Require Import SmodeCore.
Require Import WeakVariant WeakKpt WeakKptStale.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(** ** 1. THE CPS PEEL AT THE EARLY-RETURN ALTITUDE

    [WeakStale] §7's [wstep_ok_racy_k], restated over [Defs.monadR R
    exception] with the continuation taking the early-return sum, plus the
    [ExtraOutcome] arm that makes an early return a VALUE of the peel (the
    same reason [WeakEffSkel.execR_eff] is its own fixpoint).  A REAL
    exception ([inr]) is stuck for [exec]/[execR_eff] alike, so the peel owes
    nothing there — [True], as at every other stuck node. *)

(** [RiscvExec.bind_Ret] / [_Next] at the early-return monad. *)
Lemma bindR_Ret {R X Y} (y : X) (f : X -> Defs.monadR R exception Y) :
  Defs.bind (Interface.Ret y) f = f y.
Proof. reflexivity. Qed.

Lemma bindR_Next {R X Y T}
    (oc : Interface.outcome (fun _ => (R + exception)%type) T)
    (k : T -> Defs.monadR R exception X) (f : X -> Defs.monadR R exception Y) :
  Defs.bind (Interface.Next oc k) f = Interface.Next oc (fun z => Defs.bind (k z) f).
Proof. reflexivity. Qed.

Section KR.
  Context (tid : option nat) (ra : Arch.pa) (rn : N) (rak : akinfo)
          (Φ : (nat -> bv 8) -> Prop) (D : Arch.pa -> N -> Prop) (W : Prop).

  Fixpoint wstep_ok_racy_kR (b : bool) {R X}
      (m : Defs.monadR R exception X) (s : wmstate)
      (K : (R + X) -> wmstate -> bool -> Prop) {struct m} : Prop :=
    match m with
    | Interface.Ret y => K (inr y) s b
    | Interface.Next oc k =>
        (match oc in Interface.outcome _ T
               return (T -> Defs.monadR R exception X) -> Prop with
         | Interface.RegRead r _ =>
             fun k => wstep_ok_racy_kR b (k (register_lookup r s.(wm_regs))) s K
         | Interface.RegWrite r _ v =>
             fun k => wstep_ok_racy_kR b (k tt) (wset_reg s r v) K
         | Interface.MemRead n req =>
             fun k =>
               if dev_addr (Interface.ReadReq.pa req) then
                 forall w d',
                   dev_read s.(wm_dev) (Interface.ReadReq.pa req) n = Some (w, d') ->
                   wstep_ok_racy_kR b (k (inl (w, None))) (wset_dev s d') K
               else
                 acc_wf (Interface.ReadReq.pa req) n /\
                 ( (D (Interface.ReadReq.pa req) n /\
                    (ak_pins (classify (Interface.ReadReq.access_kind req)) = false ->
                       forall j, (j < N.to_nat n)%nat ->
                         pinned_read s (acc_addr (Interface.ReadReq.pa req) j)) /\
                    (forall w,
                       wread_bytes s (classify (Interface.ReadReq.access_kind req))
                         (Interface.ReadReq.pa req) n
                         (coh_ts s (Interface.ReadReq.pa req) n) = Some w ->
                       wstep_ok_racy_kR b (k (inl (w, None)))
                         (wread_post s (classify (Interface.ReadReq.access_kind req))
                            (Interface.ReadReq.pa req)
                            (coh_ts s (Interface.ReadReq.pa req) n)) K))
                   \/
                   (b = true /\ Interface.ReadReq.pa req = ra /\ n = rn /\
                    classify (Interface.ReadReq.access_kind req) = rak /\
                    (forall ts w,
                       wread_bytes s (classify (Interface.ReadReq.access_kind req))
                         (Interface.ReadReq.pa req) n ts = Some w ->
                       Φ (fun j : nat => nth_byte w j) ->
                       wstep_ok_racy_kR false (k (inl (w, None)))
                         (wread_post s (classify (Interface.ReadReq.access_kind req))
                            (Interface.ReadReq.pa req) ts) K)) )
         | Interface.MemWrite n req =>
             fun k =>
               if dev_addr (Interface.WriteReq.pa req) then
                 forall d',
                   dev_write s.(wm_dev) (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) = Some d' ->
                   wstep_ok_racy_kR b (k (inl None)) (wset_dev s d') K
               else
                 (b = false \/ W) /\
                 acc_wf (Interface.WriteReq.pa req) n /\
                 D (Interface.WriteReq.pa req) n /\
                 wstep_ok_racy_kR false (k (inl None))
                   (wwrite_post tid s
                      (classify (Interface.WriteReq.access_kind req))
                      (Interface.WriteReq.pa req) n (Interface.WriteReq.value req)) K
         | Interface.Barrier bk =>
             fun k => wstep_ok_racy_kR b (k tt)
                        (wset_ws s (barrier_post s.(wm_ws) bk)) K
         | Interface.InstrAnnounce _   => fun k => wstep_ok_racy_kR b (k tt) s K
         | Interface.BranchAnnounce _ _=> fun k => wstep_ok_racy_kR b (k tt) s K
         | Interface.CacheOp _         => fun k => wstep_ok_racy_kR b (k tt) s K
         | Interface.TlbOp _           => fun k => wstep_ok_racy_kR b (k tt) s K
         | Interface.TakeException _   => fun k => wstep_ok_racy_kR b (k tt) s K
         | Interface.ReturnException _ => fun k => wstep_ok_racy_kR b (k tt) s K
         | Interface.TranslationStart _=> fun k => wstep_ok_racy_kR b (k tt) s K
         | Interface.TranslationEnd _  => fun k => wstep_ok_racy_kR b (k tt) s K
         | Interface.CycleCount        => fun k => wstep_ok_racy_kR b (k tt) s K
         | Interface.Message _         => fun k => wstep_ok_racy_kR b (k tt) s K
         | Interface.GetCycleCount     => fun k => wstep_ok_racy_kR b (k 0%Z) s K
         (* THE EARLY RETURN: a value of the peel, exactly as in [execR_eff] *)
         | Interface.ExtraOutcome e =>
             fun _ => match e with
                      | inl r => K (inl r) s b
                      | inr _ => True
                      end
         (* as in [wstep_ok_racy]: a [Choose] breaks the wrun -> wexec bridge *)
         | Interface.Choose _          => fun _ => False
         | _ => fun _ => True
         end) k
    end.

  (** *** 1a. The bind rule, in [monadR].

      An early return SHORT-CIRCUITS the bind — [Defs.bind] keeps the node and
      a dead continuation — so the [inl] arm hands [K] straight through. *)
  Lemma wstep_ok_racy_kR_bind (b : bool) {R X Y}
      (m : Defs.monadR R exception X) (f : X -> Defs.monadR R exception Y)
      (s : wmstate) (K : (R + Y) -> wmstate -> bool -> Prop) :
    wstep_ok_racy_kR b m s
      (fun v s' b' =>
         match v with
         | inl r => K (inl r) s' b'
         | inr x => wstep_ok_racy_kR b' (f x) s' K
         end) ->
    wstep_ok_racy_kR b (Defs.bind m f) s K.
  Proof.
    revert b s. induction m as [y|T oc k IH]; intros b s Hok.
    - exact Hok.
    - rewrite bindR_Next. destruct oc; simpl in Hok |- *; try done;
        try (exact (IH _ _ _ Hok)).
      + (* MemRead *)
        destruct (dev_addr _).
        * intros w d' Hdr. exact (IH _ _ _ (Hok w d' Hdr)).
        * destruct Hok as (Hacc & [(Hdisj & Hpin & Hk)|(Hb & Hpa & Hn & Hak & Hk)]).
          -- split; [exact Hacc|]. left. split_and!; [exact Hdisj|exact Hpin|].
             intros w Hw. exact (IH _ _ _ (Hk w Hw)).
          -- split; [exact Hacc|]. right.
             split_and!; [exact Hb|exact Hpa|exact Hn|exact Hak|].
             intros ts w Hw HΦ. exact (IH _ _ _ (Hk ts w Hw HΦ)).
      + (* MemWrite *)
        destruct (dev_addr _).
        * intros d' Hdw. exact (IH _ _ _ (Hok d' Hdw)).
        * destruct Hok as (Hb & Hacc & Hdisj & Hk).
          split_and!; [exact Hb|exact Hacc|exact Hdisj|exact (IH _ _ _ Hk)].
      (* ExtraOutcome: the early return is propagated verbatim, so [done]
         above already closed that arm. *)
  Qed.

  (** *** 1b. [liftR]: a base-monad computation peeled by [WeakStale] §7.

      [Defs.liftR m = Defs.try_catch m (fun e => throw (inr e))] preserves
      every node except [m]'s own exceptions, which it REWRAPS — and both
      predicates are [True] there. *)
  Lemma wstep_ok_racy_kR_liftR (b : bool) {R X} (m : M X) (s : wmstate)
      (K : (R + X) -> wmstate -> bool -> Prop) :
    wstep_ok_racy_k tid ra rn rak Φ D W b m s (fun x s' b' => K (inr x) s' b') ->
    wstep_ok_racy_kR b (Defs.liftR m : Defs.monadR R exception X) s K.
  Proof.
    unfold Defs.liftR. revert b s.
    induction m as [y|T oc k IH]; intros b s Hok; [exact Hok|].
    destruct oc; simpl in Hok |- *; try done;
      try (exact (IH _ _ _ Hok)).
    - (* MemRead *)
      destruct (dev_addr _).
      + intros w d' Hdr. exact (IH _ _ _ (Hok w d' Hdr)).
      + destruct Hok as (Hacc & [(Hdisj & Hpin & Hk)|(Hb & Hpa & Hn & Hak & Hk)]).
        * split; [exact Hacc|]. left. split_and!; [exact Hdisj|exact Hpin|].
          intros w Hw. exact (IH _ _ _ (Hk w Hw)).
        * split; [exact Hacc|]. right.
          split_and!; [exact Hb|exact Hpa|exact Hn|exact Hak|].
          intros ts w Hw HΦ. exact (IH _ _ _ (Hk ts w Hw HΦ)).
    - (* MemWrite *)
      destruct (dev_addr _).
      + intros d' Hdw. exact (IH _ _ _ (Hok d' Hdw)).
      + destruct Hok as (Hb & Hacc & Hdisj & Hk).
        split_and!; [exact Hb|exact Hacc|exact Hdisj|exact (IH _ _ _ Hk)].
  Qed.

  (** *** 1c. …and [catch_early_return] comes back to the base monad. *)
  Lemma wstep_ok_racy_k_cer (b : bool) {X}
      (m : Defs.monadR X exception X) (s : wmstate)
      (K : X -> wmstate -> bool -> Prop) :
    wstep_ok_racy_kR b m s
      (fun v s' b' => K (match v with inl r => r | inr y => y end) s' b') ->
    wstep_ok_racy_k tid ra rn rak Φ D W b (Defs.catch_early_return m) s K.
  Proof.
    unfold Defs.catch_early_return. revert b s.
    induction m as [y|T oc k IH]; intros b s Hok; [exact Hok|].
    destruct oc; simpl in Hok |- *; try done;
      try (exact (IH _ _ _ Hok)).
    - (* MemRead *)
      destruct (dev_addr _).
      + intros w d' Hdr. exact (IH _ _ _ (Hok w d' Hdr)).
      + destruct Hok as (Hacc & [(Hdisj & Hpin & Hk)|(Hb & Hpa & Hn & Hak & Hk)]).
        * split; [exact Hacc|]. left. split_and!; [exact Hdisj|exact Hpin|].
          intros w Hw. exact (IH _ _ _ (Hk w Hw)).
        * split; [exact Hacc|]. right.
          split_and!; [exact Hb|exact Hpa|exact Hn|exact Hak|].
          intros ts w Hw HΦ. exact (IH _ _ _ (Hk ts w Hw HΦ)).
    - (* MemWrite *)
      destruct (dev_addr _).
      + intros d' Hdw. exact (IH _ _ _ (Hok d' Hdw)).
      + destruct Hok as (Hb & Hacc & Hdisj & Hk).
        split_and!; [exact Hb|exact Hacc|exact Hdisj|exact (IH _ _ _ Hk)].
    - (* ExtraOutcome: [inl] is the caught early return, [inr] a rethrow *)
      match goal with
      | He : (_ + exception)%type |- _ => by destruct He
      end.
  Qed.

  (** *** 1d. The two leaves the fetch's register-only prefix is made of. *)
  Lemma wstep_ok_racy_kR_ret (b : bool) {R X} (x : X) (s : wmstate)
      (K : (R + X) -> wmstate -> bool -> Prop) :
    K (inr x) s b -> wstep_ok_racy_kR b (Defs.returnR R x) s K.
  Proof. exact id. Qed.

  Lemma wstep_ok_racy_kR_read_reg (b : bool) {R} (r : register) (s : wmstate)
      (K : (R + type_of_register r) -> wmstate -> bool -> Prop) :
    K (inr (register_lookup r s.(wm_regs))) s b ->
    wstep_ok_racy_kR b (Defs.liftR (Defs.read_reg r : M _)) s K.
  Proof. exact id. Qed.

  Lemma wstep_ok_racy_k_ret (b : bool) {X} (x : X) (s : wmstate)
      (K : X -> wmstate -> bool -> Prop) :
    K x s b -> wstep_ok_racy_k tid ra rn rak Φ D W b (Defs.returnm x) s K.
  Proof. exact id. Qed.

  Lemma wstep_ok_racy_k_read_reg (b : bool) (r : register) (s : wmstate)
      (K : _ -> wmstate -> bool -> Prop) :
    K (register_lookup r s.(wm_regs)) s b ->
    wstep_ok_racy_k tid ra rn rak Φ D W b (Defs.read_reg r : M _) s K.
  Proof. exact id. Qed.

  (** The two closed extension probes the 4-aligned fetch evaluates.  Both are
      [WeakFetchEff]'s [exec_eff] scripts with the [rewrite]s of the bind
      equations replaced by [apply]s of the CPS bind rule — the monad TERM
      reductions are identical, only the predicate differs. *)
  Lemma wstep_ok_racy_k_hartSupports_Ziccif (b : bool) (s : wmstate)
      (K : bool -> wmstate -> bool -> Prop) :
    K true s b ->
    wstep_ok_racy_k tid ra rn rak Φ D W b (hartSupports Ext_Ziccif) s K.
  Proof.
    intros H. unfold hartSupports. destruct (Defs.Zwf_guarded _).
    cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
    replace (Z.geb (hartSupports_measure Ext_Ziccif) 0) with true by reflexivity.
    cbn match.
    apply wstep_ok_racy_k_bind. apply wstep_ok_racy_k_ret. exact H.
  Qed.

  Lemma wstep_ok_racy_k_currentlyEnabled_Ziccif (b : bool) (s : wmstate)
      (K : bool -> wmstate -> bool -> Prop) :
    K true s b ->
    wstep_ok_racy_k tid ra rn rak Φ D W b (currentlyEnabled Ext_Ziccif) s K.
  Proof.
    intros H. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
    cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
    replace (Z.geb (currentlyEnabled_measure Ext_Ziccif) 0) with true
      by reflexivity.
    cbn match.
    apply wstep_ok_racy_k_bind. apply wstep_ok_racy_k_ret. cbn match.
    apply wstep_ok_racy_k_hartSupports_Ziccif. exact H.
  Qed.

End KR.

Arguments wstep_ok_racy_kR _ _ _ _ _ _ _ _ {R X} _ _ _.

(** *** 1e. §4's embedding at EITHER phase.

    [wstep_ok_racy_k_of_run] demands its peel at the phase the CPS goal
    carries, which after a bind is a VARIABLE — so the tail's ordinary
    certificate has to be lifted at both.  [WeakStale] §4 gives phase [false]
    and §8's [wstep_ok_racy_phase_mono] (legal at [W := True]) gives [true].
    This is [wwalk_peel_of_exports]' hit-write dance, packaged. *)
Lemma wstep_ok_racy_any_of_wstep_ok (tid : option nat) (ra : Arch.pa) (rn : N)
    (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) (b : bool) {X} (m : M X)
    (s : wmstate) :
  wstep_ok tid m s -> wstep_ok_racy tid ra rn rak Φ wD_any True b m s.
Proof.
  intros H. destruct b.
  - apply wstep_ok_racy_phase_mono.
    exact (wstep_ok_racy_false_of_wstep_ok tid ra rn rak Φ True m s H).
  - exact (wstep_ok_racy_false_of_wstep_ok tid ra rn rak Φ True m s H).
Qed.

(* ====================================================================== *)
(** ** 2b. THE TAIL'S PRODUCER: the S-mode instruction read, at [exec_eff]

    FINDING: there is no S-mode fetch chain at [exec_eff] anywhere in the
    tree — [WeakFetchEff] §3, [WeakFetch2] and [WeakFetchRvc] all hardwire
    [Machine], and the S-mode weak material ([WeakWalkEff], [WeakKpt],
    [WeakKptStale], [WeakWalkStale]) stops at [translateAddr].  The
    privilege, however, is only THREADED through the read chain (the SC pair
    [RiscvFetchExec.exec_checked_mem_read_ram] vs
    [SmodeCore.exec_checked_mem_read_ram_4_S] differ in exactly one step, the
    PMP grant, which both take as a hypothesis), so the [exec_eff] mirror
    generalises to an arbitrary [priv] with NO change of script.  The two
    lemmas below are [WeakFetchEff]'s [exec_eff_checked_mem_read_ram] and
    [exec_eff_mem_read_fetch] with [Machine] replaced by a parameter; the
    Supervisor PMP grant itself is taken in its [exec_eff] form (exactly as
    the Machine originals take theirs — [WeakPmpEff] has no Supervisor
    mirror, which is the one genuinely missing piece downstream). *)

Local Lemma avi0_mul4' (a : SailStdpp.Values.mword 64) :
  add_vec_int a (0 * 4) = a.
Proof. change (0 * 4)%Z with 0%Z. apply avi0. Qed.

Lemma exec_eff_checked_mem_read_ram_gen (priv : Privilege)
    (pbmt : page_based_mem_type)
    (addr : SailStdpp.Values.mword 64) (region : PMA_Region) (w : bv 32) s :
  exec_eff (pmpCheck (Physaddr addr) 4 (InstructionFetch tt) priv) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec_eff (within_clint (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr addr) 4) s = Some (false, s, []) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec_eff (checked_mem_read (InstructionFetch tt) pbmt priv
              (Physaddr addr) 4 false false false false) s
    = Some (Ok (w, default_meta), s, [WEread wak_plain addr 4]).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes.
  (* the PMA/PMP decision, with the PMA answer prioritised on failure *)
  assert (Hcp : exec_eff (check_pma_with_pmp_priority (InstructionFetch tt) pbmt priv
                            (Physaddr addr) 4 false) s
                = Some (Ok pma_ok_aligned, s, [])).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_eff_bind_nil _ _ _ _ _
               (exec_eff_pmaCheck_ram addr pbmt region s Hmatch Halign Hexec)).
    cbn match. apply exec_eff_returnM. }
  (* within_mmio_readable = false, trace [] *)
  assert (Hmmio : exec_eff (within_mmio_readable (Physaddr addr) 4) s
                  = Some (false, s, [])).
  { unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hc). cbn match.
    rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hh). cbn match. reflexivity. }
  unfold checked_mem_read. rewrite exec_eff_catch_early_return.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
  rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
  rewrite (execR_eff_liftR_seq _ _ _ _ _
             (exec_eff_split_misaligned_unsplit addr 4 0 s)). cbn beta.
  rewrite misaligned_order_1. cbn zeta.
  rewrite (execR_eff_liftR_seq _ _ _ _ _
             (_ : exec_eff (read_kind_of_flags false false false) s
                  = Some (Read_plain, s, []))).
  2:{ unfold read_kind_of_flags. apply exec_eff_returnM. }
  cbn beta.
  (* the split loop: ONE iteration at offset 0, and THE trace element *)
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
    assert (Hu : execR_eff (Defs.untilMT vs m c b) s
                 = Some (inr (w, true, 0), s, [WEread wak_plain addr 4])) end.
  { eapply execR_eff_untilMT_1; [ reflexivity | | apply execR_eff_returnR ].
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    rewrite avi0_mul4'.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hpmp). cbn beta.
    cbn match.
    (* the pmpCheck arm is a [bind0] seq into within_mmio_readable *)
    match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
      assert (Hseq : execR_eff (Defs.bind0 a b) s = Some (inr false, s, [])) end.
    { rewrite execR_eff_bind0_eq. rewrite execR_eff_returnR. cbn match.
      rewrite execR_eff_liftR. rewrite Hmmio. reflexivity. }
    rewrite (execR_eff_bind_nil _ _ _ _ _ Hseq). cbn beta. cbn match.
    (* the RAM read, whose own bind returns just the data (the meta is dropped) *)
    match goal with
      |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?pa ?wd ?mt)) ?k1) _] =>
      assert (Hrd : execR_eff (Defs.bind (Defs.liftR (read_ram rk pa wd mt)) k1) s
                    = Some (inr w, s, [WEread wak_plain addr 4])) end.
    { rewrite (execR_eff_liftR_cat _ _ _ _ _ _
                 (exec_eff_read_ram_plain_4 addr w s Hdev Hbytes)).
      cbn beta match. rewrite execR_eff_returnR. cbn [app]. reflexivity. }
    rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hrd). cbn beta zeta.
    rewrite autocast_id. rewrite usvd_zeros_full_32.
    rewrite execR_eff_returnR. cbn [app]. reflexivity. }
  rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hu). cbn beta zeta.
  rewrite autocast_id. rewrite execR_eff_returnR. cbn [app]. reflexivity.
Qed.

Lemma exec_eff_mem_read_fetch_gen (priv : Privilege)
    (pbmt : page_based_mem_type)
    (addr : SailStdpp.Values.mword 64) (region : PMA_Region) (w : bv 32) s :
  exec_eff (pmpCheck (Physaddr addr) 4 (InstructionFetch tt) priv) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec_eff (within_clint (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr addr) 4) s = Some (false, s, []) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = priv ->
  exec_eff (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 4 false false false) s
    = Some (Ok w, s, [WEread wak_plain addr 4]).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes Hpriv.
  unfold mem_read.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_effectivePrivilege_fetch _ _ s)).
  rewrite Hpriv.
  unfold mem_read_priv.
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (_ : exec_eff (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s
                 = Some (Ok (w, default_meta), s, [WEread wak_plain addr 4]))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_eff_bind_Some _ _ _ _ _ _
                (_ : exec_eff (checked_mem_read _ _ _ _ 4 _ _ _ _) s
                     = Some (Ok (w, default_meta), s, [WEread wak_plain addr 4]))).
      2:{ cbn match.
          apply exec_eff_checked_mem_read_ram_gen with (region := region); assumption. }
      cbn match. unfold mem_read_callback. rewrite exec_eff_returnM.
      by rewrite app_nil_r. }
  cbn [MemoryOpResult_drop_meta]. rewrite exec_eff_returnM.
  by rewrite app_nil_r.
Qed.

(** [fetch_bytes pc pc 4] — [RiscvFetchExec.exec_fetch_bytes_4] replayed.  The
    [execR] plumbing (catch_early_return, the [liftR]s, the [returnR]s) is all
    trace-free; the one [_cat] is the [mem_read]. *)

(** … and the [wstep_ok] the fetch's tail owes, from PINNEDNESS of the four
    text bytes and the flat memory's contents at them.  Kernel TEXT is
    single-message, so [pinned_read] is what the caller's [wkernel_text]
    fact gives per byte; everything else is register-only.

    [WeakCert.wstep_eff_confined_pin] at the four-byte window: the confined
    map is [wmem_restrict], the window is the read's own footprint, and the
    trace is the single pinned [WEread]. *)
Lemma wfetch_tail_read (tid : option nat) (s : wmstate)
    (pa : SailStdpp.Values.mword 64) (region : PMA_Region) (w : bv 32) :
  wlog_wf (wm_log s) ->
  acc_wf pa 4 ->
  (forall j : nat, (j < 4)%nat -> pa_z (pa_add pa j) <> 0) ->
  (forall j : nat, (j < 4)%nat -> pinned_read s (acc_addr pa j)) ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     wflat (wm_img s) (wm_log s) !! (pa_add pa j) = Some (nth_byte w j)) ->
  (* the register-only gates, at the state the peel hands the tail *)
  (forall mm : gmap Arch.pa (bv 8),
     let t := MState (wm_regs s) mm (wm_dev s) in
     exec_eff (pmpCheck (Physaddr pa) 4 (InstructionFetch tt) Supervisor) t
       = Some (None, t, []) /\
     matching_pma_region (register_lookup pma_regions (wm_regs s))
       (Physaddr pa) 4 = Some region /\
     exec_eff (within_clint (Physaddr pa) 4) t = Some (false, t, []) /\
     exec_eff (within_sig (Physaddr pa) 4) t = Some (false, t, []) /\
     exec_eff (within_htif_readable (Physaddr pa) 4) t = Some (false, t, [])) ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  dev_addr pa = false ->
  register_lookup cur_privilege (wm_regs s) = Supervisor ->
  wstep_ok tid (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
                 false false false) s.
Proof.
  intros Hwf Hacc HW0 Hpin Hbytes Hgates Halign Hexecp Hdev Hpriv.
  set (Wn := acc_win [pa] 4).
  set (mm := wmem_restrict s Wn).
  destruct (Hgates mm) as (Hpmp & Hmatch & Hc & Hsig & Hh).
  assert (Hbf : forall j : nat, (N.of_nat j < 4)%N ->
            (MState (wm_regs s) mm (wm_dev s)).(mem) !! (pa_add pa j)
            = Some (nth_byte w j)).
  { intros j Hj. cbn [mem].
    apply wmem_restrict_lookup; [|exact (Hbytes j Hj)].
    apply (acc_win_in [pa] 4 pa j); [by left|lia]. }
  pose proof (exec_eff_mem_read_fetch_gen Supervisor PBMT_PMA pa region w
                (MState (wm_regs s) mm (wm_dev s)) Hpmp Hmatch Halign Hexecp
                Hc Hsig Hh Hdev Hbf Hpriv) as Hex.
  refine (proj1 (wstep_eff_confined_pin tid _ s mm Wn _ _ _ Hwf _ _
                   (wmem_restrict_dom s Wn) (wmem_restrict_sub s Wn) _ Hex)).
  - (* no window byte wraps to 0 *)
    intros a Ha. destruct (acc_win_inv [pa] 4 a Ha) as (b & j & Hb & Hj & ->).
    apply elem_of_list_singleton in Hb as ->. exact (HW0 j Hj).
  - (* the trace's single read is pinned *)
    intros ak0 pa0 n0 Hin Hnp j Hj.
    apply elem_of_list_singleton in Hin. injection Hin as -> -> ->.
    change (N.to_nat 4) with 4%nat in Hj. exact (Hpin j Hj).
  - (* the run's memory stays inside the window *)
    cbn [mem]. etrans; [apply (wmem_restrict_dom s Wn)|done].
Qed.

(* ====================================================================== *)
(** ** 2. THE FETCH PEEL

    [WeakKptStale.wwalk_peel_of_exports]' premise bundle VERBATIM (the walk
    exports for the PC's page: the variant witness, log well-formedness, the
    three slot facts, the two pointer-slot pins, the two slot
    disjointnesses, the collapse, and the ghost-arm family), PLUS

      - the fetch's own pure register facts — the [PC] lookup and the PC's
        4-alignment, which is ALL the register-only prefix needs (see the
        header, finding (c)); and
      - the tail, at the post-translation states the peel's bind premise
        quantifies over.

    Conclusion: the peel of the WHOLE [fetch tt] at the PC page's leaf
    window, plus [wwalk_peel_of_exports]' own [wadm_filter] side condition,
    which is a fact about [σ] and rides through unchanged. *)

Section WfetchPeel.

  (** The tail obligation, named: at every state the weak translation run can
      reach, the translation's outcome is the walked [pa] and the instruction
      read at it is an ORDINARY [WeakBridge.wstep_ok] — which is what kernel
      TEXT being single-message ([pinned_read] per byte) buys.  Both halves
      are stated at [s'] and not at [σ]; see the header for why they are
      premises. *)
  Definition wfetch_tail (tid : option nat) (σ : wmstate) (va pa : mword 64)
      : Prop :=
    forall (x : result (physaddr * page_based_mem_type * unit)
                       (ExceptionType * unit)) (s' : wmstate),
      wrun tid (translateAddr (Virtaddr va) (InstructionFetch tt)) σ x s' ->
      x = Ok (Physaddr pa, PBMT_PMA, init_ext_ptw) /\
      wstep_ok tid (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
                     false false false) s'.

  (** The walk exports for the PC's page, bundled: [wwalk_peel_of_exports]'
      premise set VERBATIM (the variant witness, log well-formedness, the
      three slot facts, the two pointer-slot pins, the two slot
      disjointnesses, the collapse, and the ghost-arm family with its
      σ-uniform write-arm trace selector [wtr]), at [acc := InstructionFetch
      tt].  Bundled only so that the peel and its CPS form can share it. *)
  (** The walk exports for the PC's page, bundled: [wwalk_peel_of_exports]'
      premise set VERBATIM (the variant witness, log well-formedness, the
      three slot facts, the two pointer-slot pins, the two slot
      disjointnesses, the collapse, and the ghost-arm family with its
      σ-uniform write-arm trace selector [wtr]), at [acc := InstructionFetch
      tt].  Bundled only so that the peel and its CPS form can share it. *)
  Definition wwalk_exports (tid : option nat) (σ : wmstate)
      (root_ppn : mword 44) (va pa p2 p1 w0 lw : mword 64) : Prop :=
    let vpn := svpn_of va in
    let a2 := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
    let a1 := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
    let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
    (exists a d : mword 1, lw = pte_set_ad w0 a d) /\
    wlog_wf (wm_log σ) /\
    pt_slot_mem (wflat_st σ) a2 p2 /\
    pt_slot_mem (wflat_st σ) a1 p1 /\
    pt_slot_mem (wflat_st σ) la lw /\
    (forall j : nat, (j < 8)%nat ->
       pinned_read σ (acc_addr a2 j) /\ pinned_read σ (acc_addr a1 j)) /\
    racc_disj la 8 a2 8 /\
    racc_disj la 8 a1 8 /\
    (forall (rak : akinfo) (wv : bv (8 * 8)%N),
       wadm σ rak la 8 wv ->
       (exists a d : mword 1, (wv : mword 64) = pte_set_ad w0 a d) /\
       pte_ad_le (wv : mword 64) lw) /\
    ( (* READ-ONLY *)
      (forall av dv : mword 1,
         pte_ad_le (pte_set_ad w0 av dv) lw ->
         exists (sg' : mstate) (es : list weff),
           exec_stale la 8 (pte_set_ad w0 av dv)
             (translateAddr (Virtaddr va) (InstructionFetch tt)) (wflat_st σ)
           = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg', es) /\
           mem sg' = wflat (wm_img σ) (wm_log σ) /\
           mdev sg' = wm_dev σ /\
           (es = [] \/
            es = [WEread wak_plain a2 8; WEread wak_plain a1 8;
                  WEread wak_plain la 8] \/
            es = [WEread wak_excl la 8] \/
            es = [WEread wak_plain a2 8; WEread wak_plain a1 8;
                  WEread wak_plain la 8; WEread wak_excl la 8]))
      \/
      (* WRITE-BACK *)
      (exists (lw' : mword 64) (wtr : bool),
         update_PTE_Bits (lw : mword 64) (InstructionFetch tt) = Some lw' /\
         forall av dv : mword 1,
           pte_ad_le (pte_set_ad w0 av dv) lw ->
           exists (sg' : mstate) (es : list weff),
             exec_stale la 8 (pte_set_ad w0 av dv)
               (translateAddr (Virtaddr va) (InstructionFetch tt)) (wflat_st σ)
             = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg', es) /\
             mem sg' = write_bytes (wflat (wm_img σ) (wm_log σ))
                         (la : Arch.pa) 8 (lw' : mword 64) /\
             mdev sg' = wm_dev σ /\
             es = (if wtr
                   then [WEread wak_plain a2 8; WEread wak_plain a1 8;
                         WEread wak_plain la 8; WEread wak_excl la 8;
                         WEwrite wak_excl la 8 (lw' : mword 64)]
                   else [WEread wak_excl la 8;
                         WEwrite wak_excl la 8 (lw' : mword 64)])) ).

  Lemma wfetch_peel_of_exports (tid : option nat) (σ : wmstate)
      (root_ppn : mword 44) (va pa : mword 64) (p2 p1 w0 lw : mword 64) :
    let vpn := svpn_of va in
    let a2 := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
    let a1 := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
    let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
    (* --- the fetch's register-only prefix --- *)
    register_lookup PC σ.(wm_regs) = va ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    (* --- the walk exports for the PC's page --- *)
    wwalk_exports tid σ root_ppn va pa p2 p1 w0 lw ->
    (* --- the tail --- *)
    wfetch_tail tid σ va pa ->
    wstep_ok_racy tid la 8 wak_plain (wwalk_filter w0 lw) wD_any True true
      (fetch tt) σ /\
    wadm_filter σ wak_plain la 8 (wwalk_filter w0 lw).
  Proof.
    intros vpn a2 a1 la Hpc Hal
      (Hvar & Hwf & Hs2 & Hs1 & Hs0 & Hpin & Hd2 & Hd1 & Hcoll & Harm) Htail.
    (* the translation's own peel and the filter, from the walk slice *)
    destruct (wwalk_peel_of_exports (InstructionFetch tt) tid σ root_ppn va pa
                p2 p1 w0 lw Hvar Hwf Hs2 Hs1 Hs0 Hpin Hd2 Hd1 Hcoll Harm)
      as [Hwalk Hfilt].
    split; [|exact Hfilt].
    destruct (align4_low_bits va Hal) as [Hbit0 Hbit1].
    apply wstep_ok_racy_k_triv.
    unfold fetch.
    change (get_config_rvfi tt) with false. cbv iota beta.
    apply wstep_ok_racy_k_cer.
    (* w__1, w__2: the two PC reads before the extension hook *)
    apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_liftR,
      wstep_ok_racy_k_read_reg. rewrite Hpc.
    apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_liftR,
      wstep_ok_racy_k_read_reg. rewrite Hpc.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    (* the misalignment gate: [or_boolM] short-circuits on bit 0 = 0 and then
       [and_boolM] on bit 1 = 0, so [Ext_Zca] is never probed *)
    apply wstep_ok_racy_kR_bind.
    apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_ret.
    unfold or_boolM.
    apply wstep_ok_racy_kR_bind.
    apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_liftR,
      wstep_ok_racy_k_read_reg. rewrite Hpc.
    apply wstep_ok_racy_kR_ret. rewrite Hbit0. cbv iota beta.
    unfold and_boolM.
    apply wstep_ok_racy_kR_bind.
    apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_liftR,
      wstep_ok_racy_k_read_reg. rewrite Hpc.
    apply wstep_ok_racy_kR_ret. rewrite Hbit1. cbv iota beta.
    apply wstep_ok_racy_kR_ret. cbv iota beta.
    (* the 4-alignment gate: [is_aligned_vaddr] holds, so [Ext_Ziccif] IS
       probed — a closed recursion, no register read *)
    apply wstep_ok_racy_kR_bind.
    apply wstep_ok_racy_kR_bind.
    apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_liftR,
      wstep_ok_racy_k_read_reg. rewrite Hpc.
    apply wstep_ok_racy_kR_ret. rewrite Hal. cbv iota beta.
    apply wstep_ok_racy_kR_liftR, wstep_ok_racy_k_currentlyEnabled_Ziccif.
    cbv iota beta.
    (* w__12, w__13: the PC reads that feed [fetch_bytes] *)
    apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_liftR,
      wstep_ok_racy_k_read_reg. rewrite Hpc.
    apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_liftR,
      wstep_ok_racy_k_read_reg. rewrite Hpc.
    apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_liftR.
    (* ---------------- inside [fetch_bytes va va 4] ---------------- *)
    unfold fetch_bytes.
    apply wstep_ok_racy_k_cer.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    apply wstep_ok_racy_kR_bind.
    apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_ret.
    (* ================= THE SEAM ================= *)
    apply wstep_ok_racy_kR_liftR.
    apply (wstep_ok_racy_k_of_run _ _ _ _ _ _ _ _ _ σ _ Hwalk).
    intros x s' Hrun b'.
    destruct (Htail x s' Hrun) as [-> Hmr].
    (* the OK arm: the translated address, then the text read *)
    cbv iota beta.
    apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_ret. cbv iota beta.
    apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_liftR.
    (* the tail's ORDINARY certificate, embedded and phase-lifted — the same
       dance [wwalk_peel_of_exports]' hit-write sub-case does *)
    apply (wstep_ok_racy_k_of_run _ _ _ _ _ _ _ _ _ s' _
             (wstep_ok_racy_any_of_wstep_ok _ _ _ _ _ _ _ _ Hmr)).
    intros y s'' Hrun2 b''.
    (* everything after the text read is pure decode, so the peel is [True]
       whatever the read returned *)
    destruct y as [bytes | [exc_addr e]]; cbv iota beta.
    - apply wstep_ok_racy_kR_ret. cbv iota beta.
      apply wstep_ok_racy_kR_ret. exact I.
    - apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_liftR.
      unfold assert_exp. destruct (generic_eq exc_addr (Physaddr pa)).
      + apply wstep_ok_racy_k_ret. cbv iota beta.
        apply wstep_ok_racy_kR_ret. cbv iota beta.
        apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_liftR,
          wstep_ok_racy_k_read_reg.
        apply wstep_ok_racy_kR_ret. exact I.
      + exact I.
  Qed.

  (** *** The CPS form — what 6c's funnel consumes.

      It falls straight out of the same proof: [WeakStale] §7's
      [wstep_ok_racy_k_of_run] turns the peel plus a fact about every state
      the WHOLE fetch's run can reach into the CPS object the execute phase
      binds behind.  Note the [∀ b'] in [HK]: the phase at the fetch's [Ret]
      leaf is [false] if the walk took its racy read and [true] if it did
      not, and a non-CPS bind cannot state that ([WeakStale] §7's design
      point). *)
  Lemma wfetch_peel_k (tid : option nat) (σ : wmstate)
      (root_ppn : mword 44) (va pa : mword 64) (p2 p1 w0 lw : mword 64)
      (K : FetchResult -> wmstate -> bool -> Prop) :
    let vpn := svpn_of va in
    let a2 := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
    let a1 := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
    let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
    register_lookup PC σ.(wm_regs) = va ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    wwalk_exports tid σ root_ppn va pa p2 p1 w0 lw ->
    wfetch_tail tid σ va pa ->
    (forall (r : FetchResult) (s' : wmstate),
       wrun tid (fetch tt) σ r s' -> forall b' : bool, K r s' b') ->
    wstep_ok_racy_k tid la 8 wak_plain (wwalk_filter w0 lw) wD_any True true
      (fetch tt) σ K /\
    wadm_filter σ wak_plain la 8 (wwalk_filter w0 lw).
  Proof.
    intros vpn a2 a1 la Hpc Hal Hexp Htail HK.
    destruct (wfetch_peel_of_exports tid σ root_ppn va pa p2 p1 w0 lw
                Hpc Hal Hexp Htail) as [Hpeel Hfilt].
    split; [|exact Hfilt].
    exact (wstep_ok_racy_k_of_run _ _ _ _ _ _ _ _ _ σ K Hpeel HK).
  Qed.

End WfetchPeel.

(* ====================================================================== *)
(** ** 4. THE TAIL, DISCHARGED FROM THE WALK EXPORTS
    (the pure gap the header's finding (e) left open)

    The header records why [wfetch_tail] had to be a premise: the peel runs
    at [D := wD_any] and [W := True], so [wstep_ok_racy]'s write arm
    constrains no address, and [WeakRacy.exec_of_wrun_racy] — the only
    bridge that DOES pin the write to [la] — is stated at [W := False].
    [WeakStale] §10's ⇐-bridge is the missing link: it says the weak run of
    a PEELED program lands on a family member's [exec_stale] outcome, so the
    family's own trace description — which pins the write to [la] and
    nothing else — transports to the weak run.  §10-0's log-footprint
    conjunct is what turns that into the statement a consumer can use:

        A BYTE NO TRACE WRITE TOUCHES KEEPS ITS [latest_ts].

    That, plus [WeakInterp.wrun_ws_le], is exactly [pinned_read]'s two
    ingredients, so pinnedness of the four TEXT bytes transports from [σ] to
    every post-translation [s']; the contents transport through the family's
    memory description ([write_bytes_lookup_ne] off the leaf window).

    WHAT REMAINS A PREMISE, and why.  The REGISTERS at [s']: the exports
    bundle ([wwalk_exports], landed and not touched here) describes the
    member's [mem] and [mdev] but not its [sregs], and the walk really does
    write one register on a TLB miss (the absorption theorem's §2 dispatch
    reports [sregs sg' = sg.(sregs) \/ sregs sg' = register_set tlb … ]).
    So the fetch's register-only gates are taken at the post-states, as
    [wfetch_gates] — a premise with NO memory, view or pinnedness content,
    which is what the capstone below means by "gates".

    THE DISJOINTNESS is taken as the premise [racc_disj la 8 pa 4]: kernel
    TEXT and a page-table slot are different regions, and this is the cheap
    spelling of that for the caller. *)

Section WfetchTail.

  (** *** 4a. Pinnedness transports along a run that MISSES the byte.

      [WeakCert.pinned_read_mono] wants the log unchanged; this wants only
      the byte's own [latest_ts] unchanged, which is what §10-0 exports. *)
  Lemma pinned_read_ts_mono (s s' : wmstate) (a : Z) :
    latest_ts (wm_log s') a = latest_ts (wm_log s) a ->
    ws_le (wm_ws s) (wm_ws s') ->
    pinned_read s a -> pinned_read s' a.
  Proof.
    intros Hts Hle Hp. destruct Hle as (Hcoh & _ & _ & Hnew & _ & _).
    rewrite /pinned_read Hts. rewrite /pinned_read in Hp.
    pose proof (Hcoh a). lia.
  Qed.

  (** *** 4b. Reading the filter backwards: a [Φ]-accepted word IS an A/D
      variant, in the shape the exports' family takes its arguments.  This is
      [WeakKptStale.wstep_ok_racy_true_of_walk_family]'s opening move, named. *)
  Lemma wwalk_filter_inv (w0 lw : mword 64) (u : bv (8 * 8)%N) :
    wwalk_filter w0 lw (fun j : nat => nth_byte u j) ->
    exists av dv : mword 1,
      u = pte_set_ad w0 av dv /\ pte_ad_le (pte_set_ad w0 av dv) lw.
  Proof.
    intros (wv & Hbs & (av & dv & Hwv) & Hle).
    assert (Hweq : u = wv).
    { apply (bv_eq_of_bytes (n := 8%N)). intros j Hj.
      exact (f_equal (fun f : nat -> bv 8 => f j) Hbs). }
    exists av, dv. split; [exact (eq_trans Hweq Hwv)|rewrite -Hwv; exact Hle].
  Qed.

  (** *** 4c. The walk's trace footprint, in §10-0's shape.

      Every write of every shape the absorption theorem produces is the
      8-byte leaf store ([WeakKptStale.wwalk_ev_ok]), so a byte off the leaf
      window is written by no trace write at all. *)
  Lemma wtrace_wonly_of_evs (a2 a1 la : Arch.pa) (es : list weff) (a : Arch.pa) :
    Forall (wwalk_ev_ok a2 a1 la) es ->
    (forall j : nat, (j < 8)%nat -> pa_add la j <> a) ->
    wtrace_wonly (fun (pa : Arch.pa) (n : N) =>
                    forall j : nat, (j < N.to_nat n)%nat -> pa_add pa j <> a) es.
  Proof.
    intros Hall Hoff ak pa n v Hin j Hj.
    assert (Hev : wwalk_ev_ok a2 a1 la (WEwrite ak pa n v)).
    { rewrite ->Forall_forall in Hall. apply Hall.
      first [exact Hin | exact (proj1 (elem_of_list_In _ _) Hin)]. }
    simpl in Hev. destruct Hev as (Hn & Hpa). subst n pa.
    apply Hoff. change (N.to_nat 8) with 8%nat in Hj. lia.
  Qed.

  (** *** 4d. THE OUTCOME OF THE WEAK TRANSLATION RUN.

      Case on the exports' ghost arms: the read-only and MISS write-back
      shapes are [trace_stale] (five of the six shapes — exactly
      [WeakKptStale.trace_stale_walk_shapes]) and go through
      [WeakStale.wrun_exec_stale_elim]; the HIT write-back's only read is
      EXCLUSIVE, so its family is constant and [trace_off_win] holds
      vacuously — [WeakStale.wrun_exec_stale_elim_const].  In every case
      [exec_stale] is a FUNCTION, so the family's own equation pins the
      result, the post-memory, the post-device and the trace. *)
  Lemma wwalk_run_outcome (tid : option nat) (σ : wmstate)
      (root_ppn : mword 44) (va pa p2 p1 w0 lw : mword 64) :
    let vpn := svpn_of va in
    let a2 := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
    let a1 := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
    let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
    wwalk_exports tid σ root_ppn va pa p2 p1 w0 lw ->
    forall (x : result (physaddr * page_based_mem_type * unit)
                       (ExceptionType * unit)) (s' : wmstate),
      wrun tid (translateAddr (Virtaddr va) (InstructionFetch tt)) σ x s' ->
      x = Ok (Physaddr pa, PBMT_PMA, init_ext_ptw) /\
      wlog_wf (wm_log s') /\
      ws_le (wm_ws σ) (wm_ws s') /\
      wm_dev s' = wm_dev σ /\
      (forall a : Arch.pa,
         (forall j : nat, (j < 8)%nat -> pa_add la j <> a) ->
         latest_ts (wm_log s') (pa_z a) = latest_ts (wm_log σ) (pa_z a)) /\
      (forall a : Arch.pa,
         (forall j : nat, (j < 8)%nat -> pa_add la j <> a) ->
         wflat (wm_img s') (wm_log s') !! a = wflat (wm_img σ) (wm_log σ) !! a).
  Proof.
    intros vpn a2 a1 la Hexp x s' Hrun.
    pose proof Hexp as Hexp'.
    destruct Hexp' as (Hvar & Hwf & Hs2 & Hs1 & Hs0 & Hpin & Hd2 & Hd1 & Hcoll
                       & Harm).
    pose proof (pt_slot_mem_acc_wf _ _ _ Hs0) as Hwf0.
    destruct (wwalk_peel_of_exports (InstructionFetch tt) tid σ root_ppn va pa
                p2 p1 w0 lw Hvar Hwf Hs2 Hs1 Hs0 Hpin Hd2 Hd1 Hcoll Harm)
      as [Hpeel Hfilt].
    assert (Hrd : is_Some (read_bytes (wflat (wm_img σ) (wm_log σ)) la 8)).
    { exists (lw : bv (8 * 8)%N). apply read_bytes_of_bytes. intros j Hj.
      rewrite -(wflat_st_mem σ). apply (proj1 Hs0). lia. }
    (* ---- the member the run landed on, and everything it says ---- *)
    assert (Hcore : exists (sg' : mstate) (es : list weff),
              x = Ok (Physaddr pa, PBMT_PMA, init_ext_ptw) /\
              wflat_st s' = sg' /\
              mdev sg' = wm_dev σ /\
              (mem sg' = wflat (wm_img σ) (wm_log σ) \/
               exists lw' : mword 64,
                 mem sg' = write_bytes (wflat (wm_img σ) (wm_log σ))
                             (la : Arch.pa) 8 lw') /\
              wlog_wf (wm_log s') /\
              Forall (wwalk_ev_ok a2 a1 la) es /\
              (forall a : Arch.pa,
                 wtrace_wonly (fun (pa0 : Arch.pa) (n : N) =>
                    forall j : nat, (j < N.to_nat n)%nat -> pa_add pa0 j <> a) es ->
                 latest_ts (wm_log s') (pa_z a) = latest_ts (wm_log σ) (pa_z a))).
    { destruct Harm as [Hro | (lw' & wtr & Hupd & Hfam)].
      - (* ---------- READ-ONLY: four stale-friendly shapes ---------- *)
        assert (Hst : forall u : bv (8 * 8)%N,
                  wwalk_filter w0 lw (fun j : nat => nth_byte u j) ->
                  exists (y : result (physaddr * page_based_mem_type * unit)
                                     (ExceptionType * unit))
                         (t' : mstate) (es : list weff),
                    exec_stale la 8 u
                      (translateAddr (Virtaddr va) (InstructionFetch tt))
                      (wflat_st σ) = Some (y, t', es) /\
                    trace_stale wak_plain la 8 es).
        { intros u Hu. destruct (wwalk_filter_inv w0 lw u Hu) as (av & dv & Hw & Hle).
          destruct (Hro av dv Hle) as (sgm & esm & Hex & _ & _ & Hes).
          exists (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), sgm, esm.
          split; [rewrite Hw; exact Hex|].
          apply (trace_stale_walk_shapes a2 a1 la lw esm Hd2 Hd1).
          destruct Hes as [->|[->|[-> | ->]]];
            [by left|by right; left|by right; right; left
            |by right; right; right; left]. }
        destruct (wrun_exec_stale_elim tid la 8 wak_plain (wwalk_filter w0 lw)
                    True (translateAddr (Virtaddr va) (InstructionFetch tt))
                    Hwf0 ltac:(lia) ak_pins_plain σ Hpeel Hwf Hfilt Hrd Hst
                    x s' Hrun)
          as (u & es & _ & HΦu & Hexu & Hwf' & Hlt).
        destruct (wwalk_filter_inv w0 lw u HΦu) as (av & dv & Hw & Hle).
        destruct (Hro av dv Hle) as (sgm & esm & Hex & Hmem & Hmdev & Hes).
        rewrite Hw Hex in Hexu. injection Hexu as Hx Hst' Hes'.
        exists sgm, es. split_and!.
        + by rewrite -Hx.
        + by rewrite -Hst'.
        + exact Hmdev.
        + left. exact Hmem.
        + exact Hwf'.
        + rewrite -Hes'. destruct Hes as [->|[->|[-> | ->]]]; walk_evs.
        + exact Hlt.
      - destruct wtr.
        + (* ---------- MISS write-back: the five-event walk ---------- *)
          assert (Hst : forall u : bv (8 * 8)%N,
                    wwalk_filter w0 lw (fun j : nat => nth_byte u j) ->
                    exists (y : result (physaddr * page_based_mem_type * unit)
                                       (ExceptionType * unit))
                           (t' : mstate) (es : list weff),
                      exec_stale la 8 u
                        (translateAddr (Virtaddr va) (InstructionFetch tt))
                        (wflat_st σ) = Some (y, t', es) /\
                      trace_stale wak_plain la 8 es).
          { intros u Hu. destruct (wwalk_filter_inv w0 lw u Hu)
              as (av & dv & Hw & Hle).
            destruct (Hfam av dv Hle) as (sgm & esm & Hex & _ & _ & Hes).
            exists (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), sgm, esm.
            split; [rewrite Hw; exact Hex|].
            apply (trace_stale_walk_shapes a2 a1 la lw' esm Hd2 Hd1).
            rewrite Hes. by right; right; right; right. }
          destruct (wrun_exec_stale_elim tid la 8 wak_plain (wwalk_filter w0 lw)
                      True (translateAddr (Virtaddr va) (InstructionFetch tt))
                      Hwf0 ltac:(lia) ak_pins_plain σ Hpeel Hwf Hfilt Hrd Hst
                      x s' Hrun)
            as (u & es & _ & HΦu & Hexu & Hwf' & Hlt).
          destruct (wwalk_filter_inv w0 lw u HΦu) as (av & dv & Hw & Hle).
          destruct (Hfam av dv Hle) as (sgm & esm & Hex & Hmem & Hmdev & Hes).
          rewrite Hw Hex in Hexu. injection Hexu as Hx Hst' Hes'.
          exists sgm, es. split_and!.
          * by rewrite -Hx.
          * by rewrite -Hst'.
          * exact Hmdev.
          * right. exists lw'. exact Hmem.
          * exact Hwf'.
          * rewrite -Hes' Hes. walk_evs.
          * exact Hlt.
        + (* ---------- HIT write-back: the CONSTANT family ---------- *)
          assert (Hst : forall u : bv (8 * 8)%N,
                    wwalk_filter w0 lw (fun j : nat => nth_byte u j) ->
                    exists (y : result (physaddr * page_based_mem_type * unit)
                                       (ExceptionType * unit))
                           (t' : mstate) (es : list weff),
                      exec_stale la 8 u
                        (translateAddr (Virtaddr va) (InstructionFetch tt))
                        (wflat_st σ) = Some (y, t', es) /\
                      trace_off_win la 8 es).
          { intros u Hu. destruct (wwalk_filter_inv w0 lw u Hu)
              as (av & dv & Hw & Hle).
            destruct (Hfam av dv Hle) as (sgm & esm & Hex & _ & _ & Hes).
            exists (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), sgm, esm.
            split; [rewrite Hw; exact Hex|].
            rewrite Hes. apply trace_off_win_pinned. pinned_trace. }
          destruct (wrun_exec_stale_elim_const tid la 8 wak_plain
                      (wwalk_filter w0 lw) True true
                      (translateAddr (Virtaddr va) (InstructionFetch tt))
                      Hwf0 ltac:(lia) ak_pins_plain σ Hpeel Hwf Hfilt Hrd Hst
                      x s' Hrun)
            as (u & es & _ & HΦu & Hexu & Hwf' & Hlt).
          destruct (wwalk_filter_inv w0 lw u HΦu) as (av & dv & Hw & Hle).
          destruct (Hfam av dv Hle) as (sgm & esm & Hex & Hmem & Hmdev & Hes).
          rewrite Hw Hex in Hexu. injection Hexu as Hx Hst' Hes'.
          exists sgm, es. split_and!.
          * by rewrite -Hx.
          * by rewrite -Hst'.
          * exact Hmdev.
          * right. exists lw'. exact Hmem.
          * exact Hwf'.
          * rewrite -Hes' Hes. walk_evs.
          * exact Hlt. }
    (* ---- and now the post-state facts the fetch's tail needs ---- *)
    destruct Hcore as (sgm & es & Hx & Hsg & Hmdev & Hmem & Hwf' & Hev & Hlt).
    split_and!.
    - exact Hx.
    - exact Hwf'.
    - exact (wrun_ws_le tid _ σ x s' Hrun).
    - rewrite -(wflat_st_dev s') Hsg. exact Hmdev.
    - intros a Hoff. apply Hlt.
      exact (wtrace_wonly_of_evs a2 a1 la es a Hev Hoff).
    - intros a Hoff. rewrite -(wflat_st_mem s') Hsg.
      destruct Hmem as [Hmem | (lw' & Hmem)]; rewrite Hmem; [reflexivity|].
      apply write_bytes_lookup_ne. intros j Hj Heq.
      apply (Hoff j ltac:(change (N.to_nat 8) with 8%nat in Hj; lia)).
      by rewrite Heq.
  Qed.

  (** *** 4e. The fetch's REGISTER-ONLY gates, at the post-translation states.

      [wfetch_tail_read]'s gate premises verbatim, moved to the states the
      peel's bind premise quantifies over — see §4's header for why they, and
      only they, stay premises. *)
  Definition wfetch_gates (tid : option nat) (σ : wmstate) (va pa : mword 64)
      (region : PMA_Region) : Prop :=
    forall (x : result (physaddr * page_based_mem_type * unit)
                       (ExceptionType * unit)) (s' : wmstate),
      wrun tid (translateAddr (Virtaddr va) (InstructionFetch tt)) σ x s' ->
      (forall mm : gmap Arch.pa (bv 8),
         let t := MState (wm_regs s') mm (wm_dev s') in
         exec_eff (pmpCheck (Physaddr pa) 4 (InstructionFetch tt) Supervisor) t
           = Some (None, t, []) /\
         matching_pma_region (register_lookup pma_regions (wm_regs s'))
           (Physaddr pa) 4 = Some region /\
         exec_eff (within_clint (Physaddr pa) 4) t = Some (false, t, []) /\
         exec_eff (within_sig (Physaddr pa) 4) t = Some (false, t, []) /\
         exec_eff (within_htif_readable (Physaddr pa) 4) t = Some (false, t, [])) /\
      register_lookup cur_privilege (wm_regs s') = Supervisor.

  (** *** 4f. THE TAIL ITSELF. *)
  Lemma wfetch_tail_of_exports (tid : option nat) (σ : wmstate)
      (root_ppn : mword 44) (va pa p2 p1 w0 lw : mword 64)
      (region : PMA_Region) (w : bv 32) :
    let vpn := svpn_of va in
    let a2 := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
    let a1 := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
    let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
    wwalk_exports tid σ root_ppn va pa p2 p1 w0 lw ->
    (* the four TEXT bytes are not window bytes *)
    racc_disj la 8 pa 4 ->
    acc_wf pa 4 ->
    (forall j : nat, (j < 4)%nat -> pa_z (pa_add pa j) <> 0) ->
    (* kernel text is single-message, hence pinned, and holds [w] — at σ *)
    (forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pa j)) ->
    (forall j : nat, (N.of_nat j < 4)%N ->
       wflat (wm_img σ) (wm_log σ) !! (pa_add pa j) = Some (nth_byte w j)) ->
    (* the register-only gates *)
    wfetch_gates tid σ va pa region ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
    dev_addr pa = false ->
    wfetch_tail tid σ va pa.
  Proof.
    intros vpn a2 a1 la Hexp Hdisj Haccp HW0 Hpin Hbytes Hgates Halign Hexecp Hdev.
    pose proof Hexp as Hexp'.
    destruct Hexp' as (_ & _ & _ & _ & Hs0 & _).
    pose proof (pt_slot_mem_acc_wf _ _ _ Hs0) as Hwf0.
    (* the leaf window and the text window are byte-wise apart *)
    assert (Hne : forall i j : nat, (i < 8)%nat -> (j < 4)%nat ->
              pa_add la i <> pa_add pa j).
    { intros i j Hi Hj Heq.
      apply (pa_add_neq pa la 4 8 j i Haccp Hwf0 Hdisj
               ltac:(change (N.to_nat 4) with 4%nat; lia)
               ltac:(change (N.to_nat 8) with 8%nat; lia)).
      by rewrite Heq. }
    intros x s' Hrun.
    destruct (wwalk_run_outcome tid σ root_ppn va pa p2 p1 w0 lw Hexp x s' Hrun)
      as (Hx & Hwf' & Hws & _ & Hlt & Hmem).
    destruct (Hgates x s' Hrun) as (Hg & Hpriv).
    split; [exact Hx|].
    refine (wfetch_tail_read tid s' pa region w Hwf' Haccp HW0 _ _ Hg
              Halign Hexecp Hdev Hpriv).
    - (* the four text bytes are still PINNED at [s'] *)
      intros j Hj.
      refine (pinned_read_ts_mono σ s' (acc_addr pa j) _ Hws (Hpin j Hj)).
      rewrite -(acc_wf_byte pa 4 j Haccp
                  ltac:(change (N.to_nat 4) with 4%nat; lia)).
      apply Hlt. intros i Hi. exact (Hne i j Hi Hj).
    - (* ... and still hold [w] *)
      intros j Hj. rewrite (Hmem (pa_add pa j)); [apply Hbytes; exact Hj|].
      intros i Hi. apply Hne; [exact Hi|lia].
  Qed.

  (** *** 4g. THE CAPSTONE: the fetch peel from the exports, the text pins
      and the gates — [wfetch_tail] is no longer a premise anywhere. *)
  Lemma wfetch_peel_selfcontained (tid : option nat) (σ : wmstate)
      (root_ppn : mword 44) (va pa p2 p1 w0 lw : mword 64)
      (region : PMA_Region) (w : bv 32) :
    let vpn := svpn_of va in
    let a2 := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
    let a1 := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
    let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
    (* --- the fetch's register-only prefix --- *)
    register_lookup PC σ.(wm_regs) = va ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    (* --- the walk exports for the PC's page --- *)
    wwalk_exports tid σ root_ppn va pa p2 p1 w0 lw ->
    (* --- the text window, and its disjointness from the leaf slot --- *)
    racc_disj la 8 pa 4 ->
    acc_wf pa 4 ->
    (forall j : nat, (j < 4)%nat -> pa_z (pa_add pa j) <> 0) ->
    (forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pa j)) ->
    (forall j : nat, (N.of_nat j < 4)%N ->
       wflat (wm_img σ) (wm_log σ) !! (pa_add pa j) = Some (nth_byte w j)) ->
    (* --- the register-only gates --- *)
    wfetch_gates tid σ va pa region ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
    dev_addr pa = false ->
    wstep_ok_racy tid la 8 wak_plain (wwalk_filter w0 lw) wD_any True true
      (fetch tt) σ /\
    wadm_filter σ wak_plain la 8 (wwalk_filter w0 lw).
  Proof.
    intros vpn a2 a1 la Hpc Hal Hexp Hdisj Haccp HW0 Hpin Hbytes Hgates
      Halign Hexecp Hdev.
    apply (wfetch_peel_of_exports tid σ root_ppn va pa p2 p1 w0 lw Hpc Hal Hexp).
    exact (wfetch_tail_of_exports tid σ root_ppn va pa p2 p1 w0 lw region w
             Hexp Hdisj Haccp HW0 Hpin Hbytes Hgates Halign Hexecp Hdev).
  Qed.

  (** The CPS form, likewise self-contained — what 6c's funnel consumes. *)
  Lemma wfetch_peel_k_selfcontained (tid : option nat) (σ : wmstate)
      (root_ppn : mword 44) (va pa p2 p1 w0 lw : mword 64)
      (region : PMA_Region) (w : bv 32)
      (K : FetchResult -> wmstate -> bool -> Prop) :
    let vpn := svpn_of va in
    let a2 := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
    let a1 := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
    let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
    register_lookup PC σ.(wm_regs) = va ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    wwalk_exports tid σ root_ppn va pa p2 p1 w0 lw ->
    racc_disj la 8 pa 4 ->
    acc_wf pa 4 ->
    (forall j : nat, (j < 4)%nat -> pa_z (pa_add pa j) <> 0) ->
    (forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pa j)) ->
    (forall j : nat, (N.of_nat j < 4)%N ->
       wflat (wm_img σ) (wm_log σ) !! (pa_add pa j) = Some (nth_byte w j)) ->
    wfetch_gates tid σ va pa region ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
    dev_addr pa = false ->
    (forall (r : FetchResult) (s' : wmstate),
       wrun tid (fetch tt) σ r s' -> forall b' : bool, K r s' b') ->
    wstep_ok_racy_k tid la 8 wak_plain (wwalk_filter w0 lw) wD_any True true
      (fetch tt) σ K /\
    wadm_filter σ wak_plain la 8 (wwalk_filter w0 lw).
  Proof.
    intros vpn a2 a1 la Hpc Hal Hexp Hdisj Haccp HW0 Hpin Hbytes Hgates
      Halign Hexecp Hdev HK.
    apply (wfetch_peel_k tid σ root_ppn va pa p2 p1 w0 lw K Hpc Hal Hexp);
      [|exact HK].
    exact (wfetch_tail_of_exports tid σ root_ppn va pa p2 p1 w0 lw region w
             Hexp Hdisj Haccp HW0 Hpin Hbytes Hgates Halign Hexecp Hdev).
  Qed.

End WfetchTail.

(* ====================================================================== *)
(** ** 3. Soundness checks *)

Print Assumptions wstep_ok_racy_kR_bind.
Print Assumptions wstep_ok_racy_kR_liftR.
Print Assumptions wstep_ok_racy_k_cer.
Print Assumptions exec_eff_mem_read_fetch_gen.
Print Assumptions wfetch_tail_read.
Print Assumptions wfetch_peel_of_exports.
Print Assumptions wfetch_peel_k.
Print Assumptions wwalk_run_outcome.
Print Assumptions wfetch_tail_of_exports.
Print Assumptions wfetch_peel_selfcontained.
Print Assumptions wfetch_peel_k_selfcontained.
