(** * WkStepPeel.v — THE PEEL AND FAMILY OF A WHOLE WALKING STEP
      (walk-bridge §8, 6a: the whole-step layer above [WkFetchPeel])

    [WkFetchPeel] peels the S-mode [fetch tt] at the PC page's leaf window.
    This file lifts that peel to a COMPLETE instruction step
    [RiscvLang.riscv_step tick] whose FETCH walks the page table and whose
    EXECUTE phase is WINDOW-FREE (register-only, or touching only pinned /
    owned memory).

    ------------------------------------------------------------------
    RECONNAISSANCE — where the fetch sits inside a step, and what the
    M-mode whole-step certificates do with that structure.

    [RiscvLang.riscv_step tick = Defs.bind (try_step 0 false)
                                   (fun _ => if tick then tick_clock tt
                                             else Defs.returnm tt)]

    and [try_step 0 false] is, in the BASE monad [M],

      read_reg cur_privilege        >>= fun w0 =>
      should_inc_minstret w0        >>= fun w1 =>
      write_reg minstret_increment w1 >>
      read_reg hart_state           >>= fun w2 =>
      (match w2 with HART_ACTIVE tt => run_hart_active 0 | … end)
                                    >>= fun step_val =>
      (match step_val with … end)   >>          (* the trap / retire arms *)
      read_reg hart_state           >>= fun w10 =>
      match w10 with HART_ACTIVE tt =>
        tick_pc tt >> (retired && minstret_increment) ? minstret bump
        >> … >> returnM false | … end

    — every layer of which is REGISTER-ONLY except [run_hart_active].  And
    [run_hart_active step_no] is, in the EARLY-RETURN monad,

      catch_early_return (
        liftR (read_reg cur_privilege) >>= fun w0 =>
        liftR (dispatchInterrupt w0)   >>= fun w1 =>
        (match w1 with Some … => early_return (Step_Pending_Interrupt …)
                     | None   => returnR Step tt end)
        >> liftR (fetch tt)            >>= fun w2 =>
        match ext_fetch_hook w2 with F_Base w => … decode … execute … end)

    so the fetch sits ONE [catch_early_return] level down, under a [liftR],
    behind a register-only prefix (the privilege read and the interrupt
    dispatch).  Note the parse: [A >> B >>= f] is [Defs.bind (Defs.bind0 A B) f],
    so the fetch's [liftR] is the SECOND argument of a [bind0] whose first
    argument mentions the interrupt result — which is why §1's continuation
    extractions have to use an Ltac wildcard there (the [bind0]'s first
    argument is under a binder).

    WHAT THE M-MODE CERTIFICATES DO.  [WeakEffSkel] §§4–5 and
    [WeakFetchEff] §8 ([exec_eff_step_of_leaf_base]) assemble the whole step
    at [exec_eff] as

        trace(riscv_step tick) = trace(fetch) ++ trace(execute)

    because everything else is register-only; the assembly is
    [exec_eff_hart_active_progress_base_gen] (the [run_hart_active] mirror,
    written as a [rewrite] script over [WeakEffSkel]'s [execR_eff] kit) on
    top of [WeakEff.exec_eff_riscv_step_hart_active] (the [try_step]
    wrapper), then [WeakFetchEff] §7's [exec_eff_riscv_step_all_ticks] for
    the tick.  THE SEAM at which [WkFetchPeel]'s CPS conclusion composes is
    therefore the [Defs.bind (Defs.bind0 … (Defs.liftR (fetch tt))) k]
    node inside [run_hart_active]'s [catch_early_return] — a node in the
    EARLY-RETURN monad, which is exactly why [WkFetchPeel] §1's [kR] kit
    ([wstep_ok_racy_kR], [_kR_bind], [_kR_liftR], [_k_cer]) exists.

    ------------------------------------------------------------------
    WHAT THIS FILE ADDS on top of that kit.

    §1  Two transports the whole-step composition needs and the kit did not
        have:

        [wstep_ok_racy_k_of_eff_nil] — a REGISTER-ONLY (empty-trace) sub-run
          peels at any phase, with its post-state read off its [exec_eff]
          fact.  This is what makes every layer of the [try_step] wrapper,
          [should_inc_minstret] and [dispatchInterrupt] free: their existing
          [exec_eff] lemmas ARE their peels.

        [wstep_ok_racy_kR_of_k_cer] — the CONVERSE of [WkFetchPeel]'s
          [wstep_ok_racy_k_cer].  It is what lets the whole post-fetch
          remainder of [run_hart_active] — a term in the early-return monad,
          for which no ordinary certificate predicate exists — be owed as an
          ORDINARY [WeakBridge.wstep_ok] for its [catch_early_return].

    §2  The three tail interfaces and §3 the step peel.

    ------------------------------------------------------------------
    SCOPE.

      - ALIGNED fetch only.  The straddling ([2-aligned, not 4-aligned])
        fetch is OUT of scope here exactly as it is in [WkFetchPeel]: it is
        a TWO-window consumer and needs [WeakStale] §9's sequential-window
        kit ([wstep_ok_racy_k_seq_intro], [wrun_wexec_racy_seq2]).

      - WINDOW-FREE EXECUTE only.  An instruction whose EXECUTE phase walks
        the page table again (a user-memory load/store) is a second window
        and likewise composes through §9's seq kit, not through this file.

      - The interrupt arm is GATED OFF by a premise ([dispatchInterrupt
        Supervisor] returns [None] at σ's registers), exactly as the M-mode
        assembly gates it off with [mstatus.MIE = false].  With a pending
        interrupt the fetch never happens and the step is a different
        certificate altogether.

    Design: claude-notes/design/weak-memory-walk-bridge.md §8. *)
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
Require Import RiscvTryStep.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff.
Require Import WeakEffSkel WeakLeafEffCommon WeakFetchEff.
Require Import WeakRacy WeakVarCert WeakStale WeakWalkStale.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree.
Require Import SmodeCore.
Require Import WeakWalkEff.
Require Import WeakVariant WeakKpt WeakKptStale.
Require Import WkFetchPeel.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(** ** 0. THE TWO CONTINUATIONS THE STEP'S SEAMS EXPOSE

    Both are the model's own sub-terms, extracted rather than re-typed, so
    they cannot drift from [rv64d.v].  [rha_after_fetch] is the fetch's
    continuation inside [run_hart_active] (decode, landing-pad check,
    [nextPC] write, [execute], and the [Step] it returns); [ts_after_rha] is
    [run_hart_active]'s continuation inside [try_step] (the trap/retire
    dispatch, the PC tick, the [minstret] bump). *)

Definition rha_after_fetch : FetchResult -> MR Step Step :=
  ltac:(let t := eval cbv delta [run_hart_active] in (run_hart_active 0) in
        let t := eval cbv beta in t in
        match t with
        | context [Defs.bind (Defs.bind0 _ (Defs.liftR (fetch tt))) ?k] => exact k
        end).

Definition ts_after_rha : Step -> M bool :=
  ltac:(let t := eval cbv delta [try_step] in (try_step 0 false) in
        let t := eval cbv beta in t in
        match t with
        | context [@Defs.bind Step bool _ _ ?k] => exact k
        end).

(** The tick arm of [riscv_step], named so a tail interface can mention it. *)
Definition step_tick (tick : bool) : M unit :=
  if tick then tick_clock tt else Defs.returnm tt.

Lemma riscv_step_unfold (tick : bool) :
  riscv_step tick = Defs.bind (try_step 0 false) (fun _ : bool => step_tick tick).
Proof. reflexivity. Qed.

(* ====================================================================== *)
(** ** 1. THE TWO TRANSPORTS *)

Lemma wmstate_eq (s1 s2 : wmstate) :
  wm_regs s1 = wm_regs s2 -> wm_img s1 = wm_img s2 -> wm_log s1 = wm_log s2 ->
  wm_ws s1 = wm_ws s2 -> wm_dev s1 = wm_dev s2 -> s1 = s2.
Proof. destruct s1, s2; simpl; intros -> -> -> -> ->; reflexivity. Qed.

(** *** 1a. A REGISTER-ONLY sub-run peels at any phase.

    An [exec_eff] run with the EMPTY trace touches no RAM at all (every RAM
    access emits an event), so it moves only registers and the device
    fabric — and both interpreters move those the same way.  The [exec_eff]
    fact is therefore already the peel, at either phase, with the
    continuation owed at the post-state the fact names.

    This is what makes the whole [try_step] wrapper free: its layers'
    [exec_eff] lemmas ([WeakEff.exec_eff_read_reg]/[_write_reg],
    [WeakFetchEff.exec_eff_should_inc_minstret_Some],
    [WeakEffSkel.exec_eff_dispatchInterrupt_none]) are exactly this shape. *)
Lemma wstep_ok_racy_k_of_eff_nil (tid : option nat) (ra : Arch.pa) (rn : N)
    (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) (D : Arch.pa -> N -> Prop)
    (W : Prop) {X} (m : M X) :
  forall (b : bool) (s s2 : wmstate) (mm : gmap Arch.pa (bv 8)) (x : X)
         (t : mstate) (K : X -> wmstate -> bool -> Prop),
    exec_eff m (MState (wm_regs s) mm (wm_dev s)) = Some (x, t, []) ->
    wm_regs s2 = sregs t -> wm_dev s2 = mdev t ->
    wm_img s2 = wm_img s -> wm_log s2 = wm_log s -> wm_ws s2 = wm_ws s ->
    K x s2 b ->
    wstep_ok_racy_k tid ra rn rak Φ D W b m s K.
Proof.
  induction m as [y|T oc k IH];
    intros b s s2 mm x t K Hex Hr Hd Hi Hl Hw HK.
  - simpl in Hex. injection Hex as Hx Ht. subst.
    simpl in Hr, Hd.
    assert (Hs : s2 = s) by (apply wmstate_eq; congruence).
    by rewrite -Hs.
  - destruct oc; simpl in Hex |- *; try discriminate; try exact I;
      try (exact (IH _ _ _ _ _ _ _ _ Hex Hr Hd Hi Hl Hw HK)).
    + (* RegWrite: the peel moves to [wset_reg], whose projection is [set_reg] *)
      refine (IH _ _ (wset_reg s reg regval) _ mm _ _ _ _ Hr Hd Hi Hl Hw HK).
      exact Hex.
    + (* MemRead: the RAM arm emits an event, so only the device arm survives *)
      destruct (dev_addr _) eqn:Hdev.
      * intros w d' Hdr. rewrite Hdr in Hex.
        refine (IH _ _ (wset_dev s d') _ mm _ _ _ _ Hr Hd Hi Hl Hw HK).
        exact Hex.
      * destruct (read_bytes _ _ _) as [w0|]; [|discriminate].
        destruct (exec_eff (k _) _) as [[[ya ta] esa]|]; discriminate.
    + (* MemWrite: likewise *)
      destruct (dev_addr _) eqn:Hdev.
      * intros d' Hdw. rewrite Hdw in Hex.
        refine (IH _ _ (wset_dev s d') _ mm _ _ _ _ Hr Hd Hi Hl Hw HK).
        exact Hex.
      * destruct (exec_eff (k _) _) as [[[ya ta] esa]|]; discriminate.
    + (* Barrier: emits an event *)
      destruct (exec_eff (k tt) _) as [[[ya ta] esa]|]; discriminate.
Qed.

(** *** 1b. [catch_early_return], BACKWARDS.

    [WkFetchPeel] §1c turns a [kR] peel of a body into a [k] peel of its
    [catch_early_return].  The composition below needs the CONVERSE: the
    post-fetch remainder of [run_hart_active] lives in the early-return
    monad, where no ORDINARY certificate predicate exists, so its tail
    obligation has to be owed as a [WeakBridge.wstep_ok] for the
    [catch_early_return] of that remainder and pushed back inside.  Both
    directions are the same induction: at every node the two predicates are
    literally the same proposition (the [ExtraOutcome] arms included — a
    caught [inl] is [K r s b] on both sides, a rethrown [inr] is [True]). *)
Lemma wstep_ok_racy_kR_of_k_cer (tid : option nat) (ra : Arch.pa) (rn : N)
    (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) (D : Arch.pa -> N -> Prop)
    (W : Prop) (b : bool) {X} (m : Defs.monadR X exception X) (s : wmstate)
    (K : X -> wmstate -> bool -> Prop) :
  wstep_ok_racy_k tid ra rn rak Φ D W b (Defs.catch_early_return m) s K ->
  wstep_ok_racy_kR tid ra rn rak Φ D W b m s
    (fun v s' b' => K (match v with inl r => r | inr y => y end) s' b').
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

(** The composite the tails actually use: an ORDINARY certificate for the
    [catch_early_return] of an early-return term IS a [kR] peel of that term
    at either phase, at the trivial continuation. *)
Lemma wstep_ok_racy_kR_triv_of_wstep_ok (tid : option nat) (ra : Arch.pa)
    (rn : N) (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) (b : bool)
    {X} (m : Defs.monadR X exception X) (s : wmstate) :
  wstep_ok tid (Defs.catch_early_return m) s ->
  wstep_ok_racy_kR tid ra rn rak Φ wD_any True b m s (fun _ _ _ => True).
Proof.
  intros Hok.
  exact (wstep_ok_racy_kR_of_k_cer tid ra rn rak Φ wD_any True b m s
           (fun _ _ _ => True)
           (proj2 (wstep_ok_racy_k_triv tid ra rn rak Φ wD_any True b _ s)
              (wstep_ok_racy_any_of_wstep_ok tid ra rn rak Φ b _ s Hok))).
Qed.

(** ... and the base-monad twin, for the two tails that are already in [M]. *)
Lemma wstep_ok_racy_k_triv_of_wstep_ok (tid : option nat) (ra : Arch.pa)
    (rn : N) (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) (b : bool)
    {X} (m : M X) (s : wmstate) :
  wstep_ok tid m s ->
  wstep_ok_racy_k tid ra rn rak Φ wD_any True b m s (fun _ _ _ => True).
Proof.
  intros Hok.
  exact (proj2 (wstep_ok_racy_k_triv tid ra rn rak Φ wD_any True b m s)
           (wstep_ok_racy_any_of_wstep_ok tid ra rn rak Φ b m s Hok)).
Qed.

(** *** 1c. Two more leaves the [try_step] wrapper is made of. *)

Lemma wstep_ok_racy_k_write_reg (tid : option nat) (ra : Arch.pa) (rn : N)
    (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) (D : Arch.pa -> N -> Prop)
    (W : Prop) (b : bool) (r : register) (v : type_of_register r)
    (s : wmstate) (K : unit -> wmstate -> bool -> Prop) :
  K tt (wset_reg s r v) b ->
  wstep_ok_racy_k tid ra rn rak Φ D W b (Defs.write_reg r v : M unit) s K.
Proof. exact id. Qed.

(** The STATE-PRESERVING instance of §1a — the shape every read-only
    register probe ([should_inc_minstret], [dispatchInterrupt]) has. *)
Lemma wstep_ok_racy_k_quiet (tid : option nat) (ra : Arch.pa) (rn : N)
    (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) (D : Arch.pa -> N -> Prop)
    (W : Prop) (b : bool) {X} (m : M X) (s : wmstate) (x : X)
    (K : X -> wmstate -> bool -> Prop) :
  exec_eff m (MState (wm_regs s) ∅ (wm_dev s))
    = Some (x, MState (wm_regs s) ∅ (wm_dev s), []) ->
  K x s b ->
  wstep_ok_racy_k tid ra rn rak Φ D W b m s K.
Proof.
  intros Hex HK.
  exact (wstep_ok_racy_k_of_eff_nil tid ra rn rak Φ D W m b s s ∅ x _ K
           Hex eq_refl eq_refl eq_refl eq_refl eq_refl HK).
Qed.

(** ... and its FLAT-MEMORY instance, which is the one that lets the SAME
    register-only [exec_eff] premise serve both the peel (§3) and the family
    (§5): the peel does not care which memory the quiet fact is stated at,
    and the family needs it at the weak state's own flat projection. *)
Lemma wstep_ok_racy_k_quiet_flat (tid : option nat) (ra : Arch.pa) (rn : N)
    (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) (D : Arch.pa -> N -> Prop)
    (W : Prop) (b : bool) {X} (m : M X) (s : wmstate) (x : X)
    (K : X -> wmstate -> bool -> Prop) :
  exec_eff m (wflat_st s) = Some (x, wflat_st s, []) ->
  K x s b ->
  wstep_ok_racy_k tid ra rn rak Φ D W b m s K.
Proof.
  intros Hex HK.
  exact (wstep_ok_racy_k_of_eff_nil tid ra rn rak Φ D W m b s s
           (wflat (wm_img s) (wm_log s)) x _ K
           Hex eq_refl eq_refl eq_refl eq_refl eq_refl HK).
Qed.

(* ====================================================================== *)
(** ** 2. THE INTERFACES

    Three tails and one fetch.  Each is owed at the states the PRECEDING
    run can reach — the same discipline [WkFetchPeel]'s [wfetch_tail] uses,
    and for the same reason: what the weak run did to the log between σ and
    the tail's state is the absorption theorem's business, not the peel's.

    [wexec_tail] is the one that carries the INSTRUCTION.  Its
    [catch_early_return] is not decoration: [rha_after_fetch r] lives in the
    early-return monad, where there is no ordinary certificate predicate at
    all, and §1b is what pushes the [catch_early_return]'s certificate back
    inside.  An instruction-specific discharger (decode + a window-free
    [execute]) is future work; this is the seam it will plug into. *)

Definition wmi (σ : wmstate) (b : bool) : wmstate :=
  wset_reg σ (R_bool minstret_increment) b.

Definition wexec_tail (tid : option nat) (σ : wmstate) : Prop :=
  forall (r : FetchResult) (s' : wmstate),
    wrun tid (fetch tt) σ r s' ->
    wstep_ok tid (Defs.catch_early_return (rha_after_fetch r)) s'.

Definition wstep_post_tail (tid : option nat) (σ : wmstate) : Prop :=
  forall (sv : Step) (s' : wmstate),
    wrun tid (run_hart_active 0) σ sv s' -> wstep_ok tid (ts_after_rha sv) s'.

Definition wstep_tick_tail (tid : option nat) (σ : wmstate) (tick : bool) : Prop :=
  forall (x : bool) (s' : wmstate),
    wrun tid (try_step 0 false) σ x s' -> wstep_ok tid (step_tick tick) s'.

(** The fetch peel, in the CPS form [WkFetchPeel] §2 delivers it — taken as
    an interface here so that §3's assembly is stated once and instantiated
    both from the exports bundle (§4) and, later, from the funnel's fupd. *)
Definition wfetch_peel_k_at (tid : option nat) (la : Arch.pa)
    (Φ : (nat -> bv 8) -> Prop) (σ : wmstate) : Prop :=
  forall K : FetchResult -> wmstate -> bool -> Prop,
    (forall (r : FetchResult) (s' : wmstate),
       wrun tid (fetch tt) σ r s' -> forall b' : bool, K r s' b') ->
    wstep_ok_racy_k tid la 8 wak_plain Φ wD_any True true (fetch tt) σ K.

(* ====================================================================== *)
(** ** 3. THE PEEL OF [run_hart_active], AND OF THE WHOLE STEP *)

(** *** 3a. [run_hart_active], from the fetch peel and the execute tail.

    The prefix is the privilege read and [dispatchInterrupt], both
    register-only; the interrupt gate is a premise (see the header). *)
Lemma wrha_peel (tid : option nat) (σ : wmstate) (la : Arch.pa)
    (Φ : (nat -> bv 8) -> Prop) :
  register_lookup cur_privilege (wm_regs σ) = Supervisor ->
  exec_eff (dispatchInterrupt Supervisor) (wflat_st σ)
    = Some (None, wflat_st σ, []) ->
  wfetch_peel_k_at tid la Φ σ ->
  wexec_tail tid σ ->
  wstep_ok_racy tid la 8 wak_plain Φ wD_any True true (run_hart_active 0) σ.
Proof.
  intros Hpriv Hdisp Hfetch Htail.
  apply wstep_ok_racy_k_triv.
  unfold run_hart_active.
  apply wstep_ok_racy_k_cer.
  (* the privilege read *)
  apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_liftR,
    wstep_ok_racy_k_read_reg. rewrite Hpriv.
  (* the interrupt dispatch: register-only, and gated to [None] *)
  apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_liftR.
  apply (wstep_ok_racy_k_quiet_flat _ _ _ _ _ _ _ _ _ σ None _ Hdisp).
  cbv iota beta.
  (* [returnR tt >> liftR (fetch tt)] — the seam *)
  apply wstep_ok_racy_kR_bind.
  apply wstep_ok_racy_kR_bind, wstep_ok_racy_kR_ret.
  apply wstep_ok_racy_kR_liftR.
  apply Hfetch.
  intros r s' Hrun b'.
  exact (wstep_ok_racy_kR_triv_of_wstep_ok tid la 8 wak_plain Φ b'
           (rha_after_fetch r) s' (Htail r s' Hrun)).
Qed.

(** *** 3b. THE WHOLE STEP.

    Everything around [run_hart_active] is register-only: the privilege
    read, [should_inc_minstret], the [minstret_increment] pre-write, the
    hart-active gate, and — through the tails — the trap/retire dispatch,
    the PC tick, the [minstret] bump and the clock tick.  The
    [minstret_increment] pre-write is why the fetch-side premises are owed
    at [wmi σ b] for BOTH values of [b]: the funnel's own choice of the flag
    is not visible to the caller, exactly as in
    [WeakFetchEff.exec_eff_step_of_leaf_base]'s [forall b : bool] execute
    premise. *)
Lemma wstep_peel (tid : option nat) (σ : wmstate) (la : Arch.pa)
    (Φ : (nat -> bv 8) -> Prop) (tick : bool) :
  register_lookup cur_privilege (wm_regs σ) = Supervisor ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  (forall bmi : bool,
     wstep_ok_racy tid la 8 wak_plain Φ wD_any True true
       (run_hart_active 0) (wmi σ bmi)) ->
  (forall bmi : bool, wstep_post_tail tid (wmi σ bmi)) ->
  wstep_tick_tail tid σ tick ->
  wstep_ok_racy tid la 8 wak_plain Φ wD_any True true (riscv_step tick) σ.
Proof.
  intros Hpriv Hhart Hrha Hpost Htick.
  rewrite (riscv_step_unfold tick).
  apply wstep_ok_racy_bind.
  2:{ intros x s' Hrun b'.
      exact (wstep_ok_racy_any_of_wstep_ok tid la 8 wak_plain Φ b'
               (step_tick tick) s' (Htick x s' Hrun)). }
  apply wstep_ok_racy_k_triv.
  unfold try_step. cbn [ext_pre_step_hook].
  (* the privilege read *)
  apply wstep_ok_racy_k_bind, wstep_ok_racy_k_read_reg. rewrite Hpriv.
  (* [should_inc_minstret]: register-only, and its answer is the funnel's *)
  apply wstep_ok_racy_k_bind.
  destruct (exec_eff_should_inc_minstret_Some Supervisor (wflat_st σ))
    as [bmi Hsi].
  apply (wstep_ok_racy_k_quiet_flat _ _ _ _ _ _ _ _ _ σ bmi _ Hsi).
  (* the [minstret_increment] pre-write, and the hart-active gate after it *)
  apply wstep_ok_racy_k_bind.
  apply wstep_ok_racy_k_bind, wstep_ok_racy_k_write_reg.
  apply wstep_ok_racy_k_read_reg.
  rewrite (irrelevant_register_set hart_state (R_bool minstret_increment)
             (wm_regs σ) bmi ltac:(vm_compute; reflexivity)) Hhart.
  cbv iota beta.
  (* [run_hart_active], then the trap/retire postlude *)
  apply wstep_ok_racy_k_bind.
  eapply wstep_ok_racy_k_of_run; [exact (Hrha bmi)|].
  intros sv s'' Hrun b'.
  exact (wstep_ok_racy_k_triv_of_wstep_ok tid la 8 wak_plain Φ b'
           (ts_after_rha sv) s'' (Hpost bmi sv s'' Hrun)).
Qed.

(* ====================================================================== *)
(** ** 4. THE STEP PEEL FROM THE FETCH-PEEL PREMISE BUNDLE

    [WkFetchPeel] §4g's premise list, VERBATIM, with the three premises that
    genuinely depend on the state ([wwalk_exports], [wfetch_gates], and the
    [PC] lookup) owed at the post-[minstret_increment] states — see §3b.
    Everything else is either pure geometry or a fact about the log / image
    / weak state, which a register write does not move, so it is stated at
    σ and transported by conversion. *)

Definition wfetch_ready (tid : option nat) (σ : wmstate) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : mword 64) (region : PMA_Region) : Prop :=
  wwalk_exports tid σ root_ppn va pa p2 p1 w0 lw /\
  wfetch_gates tid σ va pa region.

Lemma wstep_peel_fetchwalk (tid : option nat) (σ : wmstate)
    (root_ppn : mword 44) (va pa p2 p1 w0 lw : mword 64)
    (region : PMA_Region) (w : bv 32) (tick : bool) :
  let vpn := svpn_of va in
  let a2 := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
  let a1 := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  (* --- the step's own register gates, at σ --- *)
  register_lookup cur_privilege (wm_regs σ) = Supervisor ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  register_lookup PC (wm_regs σ) = va ->
  (forall bmi : bool,
     exec_eff (dispatchInterrupt Supervisor) (wflat_st (wmi σ bmi))
     = Some (None, wflat_st (wmi σ bmi), [])) ->
  (* --- the walk exports and the fetch's gates, at the post-write states --- *)
  (forall bmi : bool,
     wfetch_ready tid (wmi σ bmi) root_ppn va pa p2 p1 w0 lw region) ->
  (* --- the fetch's pure and log-shaped premises, at σ --- *)
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  racc_disj la 8 pa 4 ->
  acc_wf pa 4 ->
  (forall j : nat, (j < 4)%nat -> pa_z (pa_add pa j) <> 0) ->
  (forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pa j)) ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     wflat (wm_img σ) (wm_log σ) !! (pa_add pa j) = Some (nth_byte w j)) ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  dev_addr pa = false ->
  (* --- the tails --- *)
  (forall bmi : bool, wexec_tail tid (wmi σ bmi)) ->
  (forall bmi : bool, wstep_post_tail tid (wmi σ bmi)) ->
  wstep_tick_tail tid σ tick ->
  wstep_ok_racy tid la 8 wak_plain (wwalk_filter w0 lw) wD_any True true
    (riscv_step tick) σ /\
  wadm_filter σ wak_plain la 8 (wwalk_filter w0 lw).
Proof.
  intros vpn a2 a1 la Hpriv Hhart Hpc Hdisp Hready Hal Hdisj Haccp HW0 Hpin
    Hbytes Halign Hexecp Hdev Hexec Hpost Htick.
  (* the PC lookup and the privilege, past the [minstret_increment] write *)
  assert (Hpcb : forall bmi : bool, register_lookup PC (wm_regs (wmi σ bmi)) = va).
  { intros bmi. unfold wmi. cbn [wm_regs wset_reg].
    rewrite (irrelevant_register_set PC (R_bool minstret_increment)
               (wm_regs σ) bmi ltac:(vm_compute; reflexivity)). exact Hpc. }
  assert (Hprivb : forall bmi : bool,
            register_lookup cur_privilege (wm_regs (wmi σ bmi)) = Supervisor).
  { intros bmi. unfold wmi. cbn [wm_regs wset_reg].
    rewrite (irrelevant_register_set cur_privilege (R_bool minstret_increment)
               (wm_regs σ) bmi ltac:(vm_compute; reflexivity)). exact Hpriv. }
  (* the fetch peel, in CPS form, at each post-write state *)
  assert (Hfk : forall bmi : bool,
            wfetch_peel_k_at tid la (wwalk_filter w0 lw) (wmi σ bmi)).
  { intros bmi K HK.
    destruct (Hready bmi) as [Hexp Hgates].
    exact (proj1 (wfetch_peel_k_selfcontained tid (wmi σ bmi) root_ppn va pa
                    p2 p1 w0 lw region w K (Hpcb bmi) Hal Hexp Hdisj Haccp HW0
                    Hpin Hbytes Hgates Halign Hexecp Hdev HK)). }
  split.
  - apply (wstep_peel tid σ la (wwalk_filter w0 lw) tick Hpriv Hhart);
      [| exact Hpost | exact Htick].
    intros bmi.
    exact (wrha_peel tid (wmi σ bmi) la (wwalk_filter w0 lw)
             (Hprivb bmi) (Hdisp bmi) (Hfk bmi) (Hexec bmi)).
  - destruct (Hready false) as [Hexp Hgates].
    exact (proj2 (wfetch_peel_selfcontained tid (wmi σ false) root_ppn va pa
                    p2 p1 w0 lw region w (Hpcb false) Hal Hexp Hdisj Haccp HW0
                    Hpin Hbytes Hgates Halign Hexecp Hdev)).
Qed.

(* ====================================================================== *)
(** ** 5. THE FAMILY — the whole step at the STALE MIRROR

    [WeakStale] §10's ⇐-bridge takes its family over the WHOLE program the
    peel is stated at, so a walking step owes an [exec_stale] run of
    [riscv_step tick] per admissible leaf word.  Everything except the walk
    itself is WINDOW-FREE, so it rides [WeakStale] §3's forward transfer
    ([exec_stale_of_exec_eff]) from the [exec_eff] facts the SC/[exec_eff]
    library already proves; the composition is [WeakStale] §2's [exec_stale]
    bind kit at the base monad and [WeakWalkStale] §4's [execR_stale] kit
    inside [run_hart_active]'s [catch_early_return] — one level up from where
    §§3–5 of that file composed [translate] / [translateAddr] out of the
    walk family.

    THE TRACE SIDE.  [trace_stale] is not closed under appending an
    arbitrary suffix: before the racy read it forbids RAM WRITES outright.
    §5a's [trace_stale_app] is therefore stated with the suffix required to
    be [trace_stale] as well as [trace_off_win] — which for a window-free
    tail means "reads pinned or off-window, and NO RAM write".  See the
    note after [wstep_family_fetchwalk] for what a WRITING window-free
    execute would additionally need. *)

(** *** 5a. The two trace lemmas the concatenation needs. *)

Lemma trace_off_win_app (ra : Arch.pa) (rn : N) (es1 es2 : list weff) :
  trace_off_win ra rn es1 -> trace_off_win ra rn es2 ->
  trace_off_win ra rn (es1 ++ es2).
Proof.
  intros H1 H2 ak pa n Hin Hnp.
  apply elem_of_app in Hin as [Hin|Hin];
    [exact (H1 ak pa n Hin Hnp)|exact (H2 ak pa n Hin Hnp)].
Qed.

Lemma trace_stale_app (rak : akinfo) (ra : Arch.pa) (rn : N)
    (es1 es2 : list weff) :
  trace_stale rak ra rn es1 -> trace_stale rak ra rn es2 ->
  trace_off_win ra rn es2 -> trace_stale rak ra rn (es1 ++ es2).
Proof.
  induction es1 as [|e es1 IH]; intros H1 H2 Hoff; [exact H2|].
  destruct e; simpl in H1 |- *.
  - destruct H1 as [[Hp Ht]|[(Hnp & Hd & Ht)|(Hak & Hpa & Hn & Ht)]].
    + left. split; [exact Hp|exact (IH Ht H2 Hoff)].
    + right; left. split_and!; [exact Hnp|exact Hd|exact (IH Ht H2 Hoff)].
    + right; right. split_and!; [exact Hak|exact Hpa|exact Hn|].
      exact (trace_off_win_app ra rn es1 es2 Ht Hoff).
  - exact H1.
  - exact (IH H1 H2 Hoff).
Qed.

(** *** 5b. [catch_early_return], backwards at the mirror — §1b's twin on the
    interpreter side.  The whole post-fetch remainder is owed as an
    [exec_eff] fact for its [catch_early_return] (a term in the BASE monad,
    where the [exec_eff] library lives); this pushes it back inside. *)
Lemma execR_stale_of_cer (ra : Arch.pa) (rn : N) (u : bv (8 * rn)%N)
    {X} (m : Defs.monadR X exception X) (s : mstate) (y : X) (t : mstate)
    (es : list weff) :
  exec_stale ra rn u (Defs.catch_early_return m) s = Some (y, t, es) ->
  exists v : (X + X)%type,
    execR_stale ra rn u m s = Some (v, t, es) /\
    match v with inl r => r | inr r => r end = y.
Proof.
  rewrite (exec_stale_catch_early_return ra rn u m s).
  destruct (execR_stale ra rn u m s) as [[[[r|r] t0] es0]|] eqn:E;
    intros H; try discriminate; injection H as <- <- <-.
  - by exists (inl r).
  - by exists (inr r).
Qed.

(** *** 5c. [run_hart_active] at the mirror, from the fetch's mirror run and
    the post-fetch remainder's [exec_eff] fact. *)
Lemma exec_stale_run_hart_active (la : Arch.pa) (u : bv (8 * 8)%N)
    (sa sf sx : mstate) (r : FetchResult) (sv : Step) (esf es1 : list weff) :
  acc_wf la 8 ->
  register_lookup cur_privilege (sregs sa) = Supervisor ->
  exec_eff (dispatchInterrupt Supervisor) sa = Some (None, sa, []) ->
  exec_stale la 8 u (fetch tt) sa = Some (r, sf, esf) ->
  exec_eff (Defs.catch_early_return (rha_after_fetch r)) sf = Some (sv, sx, es1) ->
  trace_off_win la 8 es1 ->
  exec_stale la 8 u (run_hart_active 0) sa = Some (sv, sx, (esf ++ es1)%list).
Proof.
  intros Hacc Hpriv Hdisp Hfetch Htail Hoff1.
  pose proof (exec_stale_of_exec_eff la 8 u
                (Defs.catch_early_return (rha_after_fetch r)) Hacc
                sf sv sx es1 Htail Hoff1) as Hts.
  destruct (execR_stale_of_cer la 8 u (rha_after_fetch r) sf sv sx es1 Hts)
    as (vv & HvR & Hvproj).
  pose proof (exec_stale_of_eff_quiet la 8 u (dispatchInterrupt Supervisor)
                sa sa None Hacc Hdisp) as Hdisps.
  unfold run_hart_active.
  rewrite (exec_stale_catch_early_return la 8 u _ sa).
  rewrite (execR_stale_liftR_seq _ _ _ _ _ _ _ _
             (exec_stale_read_reg la 8 u cur_privilege sa)).
  rewrite Hpriv.
  rewrite (execR_stale_liftR_seq _ _ _ _ _ _ _ _ Hdisps).
  cbv iota beta.
  (* [returnR tt >> liftR (fetch tt)], then the remainder *)
  rewrite (execR_stale_bind_cat _ _ _ _ _ _ _ _ _
    (_ : execR_stale la 8 u
           (Defs.bind0 (Defs.returnR Step tt) (Defs.liftR (fetch tt))) sa
         = Some (inr r, sf, esf))).
  2:{ rewrite (execR_stale_bind_nil _ _ _ _ _ _ _ _
                 (execR_stale_returnR la 8 u tt sa)).
      rewrite execR_stale_liftR Hfetch. reflexivity. }
  rewrite HvR.
  destruct vv as [rr|rr]; simpl in Hvproj |- *; by rewrite Hvproj.
Qed.

(** *** 5d. THE WHOLE STEP at the mirror.  Everything between the wrapper and
    [run_hart_active] is register-only and rides the [exec_eff] library
    verbatim; the trap/retire postlude and the clock tick are the two
    [exec_eff] interfaces (§6 packages them). *)
Lemma exec_stale_riscv_step (la : Arch.pa) (u : bv (8 * 8)%N) (tick : bool)
    (sg0 sx sy sfin : mstate) (bmi bb : bool) (sv : Step)
    (esr es2 es3 : list weff) :
  acc_wf la 8 ->
  register_lookup cur_privilege (sregs sg0) = Supervisor ->
  exec_eff (should_inc_minstret Supervisor) sg0 = Some (bmi, sg0, []) ->
  register_lookup hart_state
    (sregs (set_reg sg0 (R_bool minstret_increment) bmi)) = HART_ACTIVE tt ->
  exec_stale la 8 u (run_hart_active 0)
    (set_reg sg0 (R_bool minstret_increment) bmi) = Some (sv, sx, esr) ->
  exec_eff (ts_after_rha sv) sx = Some (bb, sy, es2) ->
  trace_off_win la 8 es2 ->
  exec_eff (step_tick tick) sy = Some (tt, sfin, es3) ->
  trace_off_win la 8 es3 ->
  exec_stale la 8 u (riscv_step tick) sg0
    = Some (tt, sfin, (esr ++ es2 ++ es3)%list).
Proof.
  intros Hacc Hpriv Hsi Hhart Hrha Hpost Hoff2 Htick Hoff3.
  pose proof (exec_stale_of_eff_quiet la 8 u (should_inc_minstret Supervisor)
                sg0 sg0 bmi Hacc Hsi) as Hsis.
  pose proof (exec_stale_of_exec_eff la 8 u (ts_after_rha sv) Hacc
                sx bb sy es2 Hpost Hoff2) as Hposts.
  pose proof (exec_stale_of_exec_eff la 8 u (step_tick tick) Hacc
                sy tt sfin es3 Htick Hoff3) as Hticks.
  assert (Htry : exec_stale la 8 u (try_step 0 false) sg0
                 = Some (bb, sy, (esr ++ es2)%list)).
  { unfold try_step. cbn [ext_pre_step_hook].
    rewrite (exec_stale_bind_nil _ _ _ _ _ _ _ _
               (exec_stale_read_reg la 8 u cur_privilege sg0)).
    rewrite Hpriv.
    rewrite (exec_stale_bind_nil _ _ _ _ _ _ _ _ Hsis).
    rewrite (exec_stale_bind_nil _ _ _ _ _ _ _ _
      (_ : exec_stale la 8 u
             (Defs.bind0 (Defs.write_reg (R_bool minstret_increment) bmi)
                (Defs.read_reg hart_state : M _)) sg0
           = Some (HART_ACTIVE tt,
                   set_reg sg0 (R_bool minstret_increment) bmi, []))).
    2:{ rewrite (exec_stale_bind0_nil _ _ _ _ _ _ _ _
                   (exec_stale_write_reg la 8 u
                      (R_bool minstret_increment) bmi sg0)).
        rewrite (exec_stale_read_reg la 8 u hart_state _). by rewrite Hhart. }
    cbv iota beta.
    rewrite (exec_stale_bind_Some _ _ _ _ _ _ _ _ _ Hrha).
    rewrite Hposts. reflexivity. }
  rewrite (riscv_step_unfold tick).
  rewrite (exec_stale_bind_Some _ _ _ _ _ _ _ _ _ Htry).
  rewrite Hticks. by rewrite app_assoc.
Qed.

(** *** 5e. THE S-MODE FETCH AT THE MIRROR.

    [WeakFetchEff.exec_eff_fetch_bytes_4] / [_fetch_done] replayed at
    [exec_stale], with the identity translation replaced by the WALK's own
    mirror run (which is where the leaf word [u] enters) and the text read
    taken as an [exec_eff] fact and transferred — the post-translation half
    of the fetch is window-free, which is exactly the disjointness
    [WkFetchPeel] already asks its caller for ([racc_disj la 8 pa 4]).
    Everything else in the chain is PC reads and closed extension probes. *)

Lemma exec_stale_fetch_bytes_4_S (la : Arch.pa) (u : bv (8 * 8)%N)
    (va pa : mword 64) (w : mword 32) (s sg : mstate) (esw : list weff) :
  acc_wf la 8 ->
  acc_wf pa 4 ->
  racc_disj la 8 pa 4 ->
  exec_stale la 8 u (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg, esw) ->
  exec_eff (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
              false false false) sg
    = Some (Ok w, sg, [WEread wak_plain pa 4]) ->
  exec_stale la 8 u (fetch_bytes va va 4) s
    = Some (@FetchBytes_Success 4 w, sg, (esw ++ [WEread wak_plain pa 4])%list).
Proof.
  intros Hacc Haccp Hdisj Htr Hmr.
  assert (Hoff : trace_off_win la 8 [WEread wak_plain pa 4]).
  { apply trace_off_win_of_all. intros ak pa0 n Hin.
    apply elem_of_list_singleton in Hin. by injection Hin as -> -> ->. }
  pose proof (exec_stale_of_exec_eff la 8 u _ Hacc sg (Ok w) sg
                [WEread wak_plain pa 4] Hmr Hoff) as Hmrs.
  unfold fetch_bytes.
  rewrite (exec_stale_catch_early_return la 8 u _ s).
  change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
  rewrite (execR_stale_bind_cat _ _ _ _ _ _ _ _ _
    (_ : execR_stale la 8 u
           (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
         = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), sg, esw))).
  2:{ rewrite (execR_stale_bind_nil _ _ _ _ _ _ _ _
                 (execR_stale_returnR la 8 u tt s)).
      rewrite execR_stale_liftR Htr. reflexivity. }
  cbv iota beta.
  rewrite (execR_stale_bind_nil _ _ _ _ _ _ _ _
             (execR_stale_returnR la 8 u (Physaddr pa, PBMT_PMA) sg)).
  cbv iota beta.
  rewrite (execR_stale_liftR_cat _ _ _ _ _ _ _ _ _ Hmrs).
  cbv iota beta. rewrite autocast_mword_id.
  rewrite execR_stale_returnR. cbn match. cbn [app]. reflexivity.
Qed.

Lemma exec_stale_fetch_S (la : Arch.pa) (u : bv (8 * 8)%N)
    (va pa : mword 64) (w : mword 32) (s sg : mstate) (esw : list weff) :
  acc_wf la 8 ->
  acc_wf pa 4 ->
  racc_disj la 8 pa 4 ->
  register_lookup PC (sregs s) = va ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  exec_stale la 8 u (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg, esw) ->
  exec_eff (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
              false false false) sg
    = Some (Ok w, sg, [WEread wak_plain pa 4]) ->
  exec_stale la 8 u (fetch tt) s
    = Some (F_Base w, sg, (esw ++ [WEread wak_plain pa 4])%list).
Proof.
  intros Hacc Haccp Hdisj HpcPC Hvalign HnotRVC Htr Hmr.
  destruct (align4_low_bits va Hvalign) as [Hbit0 Hbit1].
  assert (HrdPC : exec_stale la 8 u (Defs.read_reg PC : M _) s = Some (va, s, [])).
  { rewrite (exec_stale_read_reg la 8 u PC s). by rewrite HpcPC. }
  pose proof (exec_eff_currentlyEnabled_Ziccif s) as Hzi.
  pose proof (exec_stale_of_eff_quiet la 8 u (currentlyEnabled Ext_Ziccif)
                s s true Hacc Hzi) as Hzis.
  unfold fetch.
  rewrite (exec_stale_catch_early_return la 8 u _ s).
  change (get_config_rvfi tt) with false. cbv iota beta.
  rewrite (execR_stale_liftR_seq _ _ _ _ _ _ _ _ HrdPC).
  rewrite (execR_stale_liftR_seq _ _ _ _ _ _ _ _ HrdPC).
  change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
  rewrite (execR_stale_bind_nil _ _ _ _ _ _ false s).
  2:{ rewrite (execR_stale_bind_nil _ _ _ _ _ _ _ _
                 (execR_stale_returnR la 8 u tt s)).
      unfold Defs.or_boolM.
      rewrite (execR_stale_bind_nil _ _ _ _ _ _ false s).
      2:{ rewrite (execR_stale_liftR_seq _ _ _ _ _ _ _ _ HrdPC). rewrite Hbit0.
          apply execR_stale_returnR. }
      cbv iota beta.
      unfold Defs.and_boolM.
      rewrite (execR_stale_bind_nil _ _ _ _ _ _ false s).
      2:{ rewrite (execR_stale_liftR_seq _ _ _ _ _ _ _ _ HrdPC). rewrite Hbit1.
          apply execR_stale_returnR. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_stale_bind_nil _ _ _ _ _ _ true s).
  2:{ unfold Defs.and_boolM.
      rewrite (execR_stale_bind_nil _ _ _ _ _ _ true s).
      2:{ rewrite (execR_stale_liftR_seq _ _ _ _ _ _ _ _ HrdPC).
          rewrite Hvalign. apply execR_stale_returnR. }
      cbv iota beta.
      rewrite execR_stale_liftR. rewrite Hzis. reflexivity. }
  cbv iota beta.
  rewrite (execR_stale_liftR_seq _ _ _ _ _ _ _ _ HrdPC).
  rewrite (execR_stale_liftR_seq _ _ _ _ _ _ _ _ HrdPC).
  rewrite (execR_stale_liftR_cat _ _ _ _ _ _ _ _ _
             (exec_stale_fetch_bytes_4_S la u va pa w s sg esw
                Hacc Haccp Hdisj Htr Hmr)).
  cbv iota beta. rewrite HnotRVC. cbv iota beta.
  rewrite execR_stale_returnR. cbn match. cbn [app].
  by rewrite app_nil_r.
Qed.

(** *** 5f. The step's WINDOW-FREE tail, as one [exec_eff] interface.

    The exec_eff twin of §2's three [wstep_ok] tails: the post-fetch
    remainder of [run_hart_active] (decode + execute), [run_hart_active]'s
    own continuation inside [try_step] (the trap/retire dispatch, the PC
    tick, the [minstret] bump) and the clock tick, each with its trace.
    [trace_off_win] is what §3's transfer needs; [trace_stale] is what the
    CONCATENATION needs (§5a) and is where a WRITING execute would fall
    out — see the note at the end of this section. *)
Definition wstep_tail_eff (la : Arch.pa) (tick : bool) (sf : mstate)
    (r : FetchResult) : Prop :=
  exists (sv : Step) (sx sy sfin : mstate) (bb : bool)
         (es1 es2 es3 : list weff),
    exec_eff (Defs.catch_early_return (rha_after_fetch r)) sf = Some (sv, sx, es1) /\
    exec_eff (ts_after_rha sv) sx = Some (bb, sy, es2) /\
    exec_eff (step_tick tick) sy = Some (tt, sfin, es3) /\
    trace_off_win la 8 (es1 ++ es2 ++ es3) /\
    trace_stale wak_plain la 8 (es1 ++ es2 ++ es3).

Lemma trace_off_win_app_l (ra : Arch.pa) (rn : N) (es1 es2 : list weff) :
  trace_off_win ra rn (es1 ++ es2) -> trace_off_win ra rn es1.
Proof.
  intros H ak pa n Hin. apply (H ak pa n), elem_of_app. by left.
Qed.

Lemma trace_off_win_app_r (ra : Arch.pa) (rn : N) (es1 es2 : list weff) :
  trace_off_win ra rn (es1 ++ es2) -> trace_off_win ra rn es2.
Proof.
  intros H ak pa n Hin. apply (H ak pa n), elem_of_app. by right.
Qed.

(** *** 5g. THE CORE ASSEMBLY: one whole step at the mirror, from ONE walk
    family member.  The trace comes out in the shape the two trace-side
    corollaries want: the WALK's own events, then the text read, then the
    window-free tail's. *)
Lemma exec_stale_step_of_walk (la : Arch.pa) (u : bv (8 * 8)%N) (tick : bool)
    (sg0 sg' : mstate) (bmi : bool) (va pa : mword 64) (w : mword 32)
    (esw : list weff) :
  acc_wf la 8 -> acc_wf pa 4 -> racc_disj la 8 pa 4 ->
  register_lookup cur_privilege (sregs sg0) = Supervisor ->
  exec_eff (should_inc_minstret Supervisor) sg0 = Some (bmi, sg0, []) ->
  register_lookup cur_privilege
    (sregs (set_reg sg0 (R_bool minstret_increment) bmi)) = Supervisor ->
  register_lookup PC
    (sregs (set_reg sg0 (R_bool minstret_increment) bmi)) = va ->
  register_lookup hart_state
    (sregs (set_reg sg0 (R_bool minstret_increment) bmi)) = HART_ACTIVE tt ->
  exec_eff (dispatchInterrupt Supervisor)
    (set_reg sg0 (R_bool minstret_increment) bmi)
    = Some (None, set_reg sg0 (R_bool minstret_increment) bmi, []) ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  exec_stale la 8 u (translateAddr (Virtaddr va) (InstructionFetch tt))
    (set_reg sg0 (R_bool minstret_increment) bmi)
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg', esw) ->
  exec_eff (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
              false false false) sg'
    = Some (Ok w, sg', [WEread wak_plain pa 4]) ->
  wstep_tail_eff la tick sg' (F_Base w) ->
  exists (t' : mstate) (est : list weff),
    exec_stale la 8 u (riscv_step tick) sg0
      = Some (tt, t', (esw ++ ([WEread wak_plain pa 4] ++ est))%list) /\
    trace_off_win la 8 est /\ trace_stale wak_plain la 8 est.
Proof.
  intros Hacc Haccp Hdisj Hpriv Hsi Hpriva Hpc Hhart Hdisp Hval HnotRVC Htr Hmr
    (sv & sx & sy & sfin & bb & es1 & es2 & es3 & H1 & H2 & H3 & Hoff & Hst).
  pose proof (exec_stale_fetch_S la u va pa w
                (set_reg sg0 (R_bool minstret_increment) bmi) sg' esw
                Hacc Haccp Hdisj Hpc Hval HnotRVC Htr Hmr) as Hf.
  pose proof (trace_off_win_app_l la 8 es1 (es2 ++ es3) Hoff) as Hoff1.
  pose proof (trace_off_win_app_r la 8 es1 (es2 ++ es3) Hoff) as Hoff23.
  pose proof (trace_off_win_app_l la 8 es2 es3 Hoff23) as Hoff2.
  pose proof (trace_off_win_app_r la 8 es2 es3 Hoff23) as Hoff3.
  pose proof (exec_stale_run_hart_active la u
                (set_reg sg0 (R_bool minstret_increment) bmi) sg' sx
                (F_Base w) sv (esw ++ [WEread wak_plain pa 4])%list es1
                Hacc Hpriva Hdisp Hf H1 Hoff1) as Hrha.
  pose proof (exec_stale_riscv_step la u tick sg0 sx sy sfin bmi bb sv
                ((esw ++ [WEread wak_plain pa 4]) ++ es1)%list es2 es3
                Hacc Hpriv Hsi Hhart Hrha H2 Hoff2 H3 Hoff3) as Hstep.
  exists sfin, (es1 ++ es2 ++ es3)%list. split_and!; [|exact Hoff|exact Hst].
  rewrite Hstep. by rewrite -!app_assoc.
Qed.

(** *** 5h. The family-side interface, keyed on the mirror post-state.

    [WkFetchPeel]'s [wfetch_gates] is keyed on the states the WEAK run can
    reach; this is its mirror twin, keyed on the states a family member's
    [exec_stale] run reaches.  Both say the same thing — "the text word is
    readable there, and the rest of the step is window-free" — on the two
    sides of the bridge.

    THE LEAF WORD IS GUARDED BY THE WALK FILTER, and that guard is not
    cosmetic: the landed walk layer describes a stale walk only at an A/D
    VARIANT of the invariant's word (the absorption theorem's family is
    indexed by [av dv] with [pte_ad_le], and so is [WeakKptStale]'s pure
    dispatch), so a run at a WILD [u] that still returns [Ok] has nothing
    pinning its post-registers or its post-memory — which is exactly what a
    discharger needs.  §5i only ever USES this interface at a
    filter-accepted word (its [Hcore] is applied right after
    [wwalk_filter_inv]), so the guard costs the consumer nothing. *)
Definition wstep_family_ready (tid : option nat) (σ : wmstate) (la : Arch.pa)
    (va pa w0 lw : mword 64) (w : mword 32) (tick : bool) : Prop :=
  forall (bmi : bool) (u : bv (8 * 8)%N) (sg' : mstate) (esw : list weff),
    wwalk_filter w0 lw (fun j : nat => nth_byte u j) ->
    exec_stale la 8 u (translateAddr (Virtaddr va) (InstructionFetch tt))
      (wflat_st (wmi σ bmi))
      = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg', esw) ->
    exec_eff (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
                false false false) sg'
      = Some (Ok w, sg', [WEread wak_plain pa 4]) /\
    wstep_tail_eff la tick sg' (F_Base w).

Lemma wflat_st_wmi (σ : wmstate) (b : bool) :
  wflat_st (wmi σ b) = set_reg (wflat_st σ) (R_bool minstret_increment) b.
Proof. reflexivity. Qed.

(** *** 5i. THE STEP FAMILY.

    The case split is [wwalk_run_outcome]'s: five of the absorption
    theorem's six trace shapes are [trace_stale] (so the whole step's trace
    is, by §5a); the SIXTH — the TLB-hit write-back [[excl-read; write]] —
    has no racy read at all, its only read PINS, and it goes to
    [WeakStale] §10d's [_const] elimination with [trace_off_win] instead. *)
Lemma wstep_family_fetchwalk (tid : option nat) (σ : wmstate)
    (root_ppn : mword 44) (va pa p2 p1 w0 lw : mword 64) (w : mword 32)
    (tick : bool) :
  let vpn := svpn_of va in
  let a2 := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
  let a1 := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  register_lookup cur_privilege (wm_regs σ) = Supervisor ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  register_lookup PC (wm_regs σ) = va ->
  (forall bmi : bool,
     exec_eff (dispatchInterrupt Supervisor) (wflat_st (wmi σ bmi))
     = Some (None, wflat_st (wmi σ bmi), [])) ->
  (forall bmi : bool, wwalk_exports tid (wmi σ bmi) root_ppn va pa p2 p1 w0 lw) ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  acc_wf pa 4 ->
  racc_disj la 8 pa 4 ->
  wstep_family_ready tid σ la va pa w0 lw w tick ->
  (forall u : bv (8 * 8)%N, wwalk_filter w0 lw (fun j : nat => nth_byte u j) ->
     exists (y : unit) (t' : mstate) (es : list weff),
       exec_stale la 8 u (riscv_step tick) (wflat_st σ) = Some (y, t', es) /\
       trace_stale wak_plain la 8 es)
  \/
  (forall u : bv (8 * 8)%N, wwalk_filter w0 lw (fun j : nat => nth_byte u j) ->
     exists (y : unit) (t' : mstate) (es : list weff),
       exec_stale la 8 u (riscv_step tick) (wflat_st σ) = Some (y, t', es) /\
       trace_off_win la 8 es).
Proof.
  intros vpn a2 a1 la Hpriv Hhart Hpc Hdisp Hexp Hval HnotRVC Haccp Hdisj Hready.
  destruct (exec_eff_should_inc_minstret_Some Supervisor (wflat_st σ))
    as [bmi Hsi].
  pose proof (Hexp bmi) as Hexpb.
  destruct Hexpb as (Hvar & Hwf & Hs2 & Hs1 & Hs0 & Hpin & Hd2 & Hd1 & Hcoll
                     & Harm & Hregs).
  pose proof (pt_slot_mem_acc_wf _ _ _ Hs0) as Hacc.
  (* the three register facts, past the [minstret_increment] pre-write *)
  assert (Hpriva : register_lookup cur_privilege
            (sregs (set_reg (wflat_st σ) (R_bool minstret_increment) bmi))
            = Supervisor).
  { cbn [sregs set_reg wflat_st].
    rewrite (irrelevant_register_set cur_privilege (R_bool minstret_increment)
               (wm_regs σ) bmi ltac:(vm_compute; reflexivity)). exact Hpriv. }
  assert (Hpca : register_lookup PC
            (sregs (set_reg (wflat_st σ) (R_bool minstret_increment) bmi)) = va).
  { cbn [sregs set_reg wflat_st].
    rewrite (irrelevant_register_set PC (R_bool minstret_increment)
               (wm_regs σ) bmi ltac:(vm_compute; reflexivity)). exact Hpc. }
  assert (Hharta : register_lookup hart_state
            (sregs (set_reg (wflat_st σ) (R_bool minstret_increment) bmi))
            = HART_ACTIVE tt).
  { cbn [sregs set_reg wflat_st].
    rewrite (irrelevant_register_set hart_state (R_bool minstret_increment)
               (wm_regs σ) bmi ltac:(vm_compute; reflexivity)). exact Hhart. }
  (* ONE family member, run through the whole step *)
  assert (Hcore : forall (u : bv (8 * 8)%N) (sgm : mstate) (esm : list weff),
            wwalk_filter w0 lw (fun j : nat => nth_byte u j) ->
            exec_stale la 8 u (translateAddr (Virtaddr va) (InstructionFetch tt))
              (wflat_st (wmi σ bmi))
              = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sgm, esm) ->
            exists (t' : mstate) (est : list weff),
              exec_stale la 8 u (riscv_step tick) (wflat_st σ)
                = Some (tt, t', (esm ++ ([WEread wak_plain pa 4] ++ est))%list) /\
              trace_off_win la 8 est /\ trace_stale wak_plain la 8 est).
  { intros u sgm esm Hu Hex.
    destruct (Hready bmi u sgm esm Hu Hex) as [Hmr Htail].
    rewrite wflat_st_wmi in Hex.
    exact (exec_stale_step_of_walk la u tick (wflat_st σ) sgm bmi va pa w esm
             Hacc Haccp Hdisj Hpriv Hsi Hpriva Hpca Hharta (Hdisp bmi)
             Hval HnotRVC Hex Hmr Htail). }
  destruct Harm as [Hro | (lw' & wtr & Hupd & Hfam)].
  - (* ---------- READ-ONLY: four stale-friendly shapes ---------- *)
    left. intros u Hu.
    destruct (wwalk_filter_inv w0 lw u Hu) as (av & dv & Hw & Hle).
    destruct (Hro av dv Hle) as (sgm & esm & Hex & _ & _ & Hes).
    rewrite Hw in Hu. rewrite Hw.
    destruct (Hcore _ sgm esm Hu Hex) as (t' & est & Hstep & Hoffe & Hste).
    exists tt, t', (esm ++ ([WEread wak_plain pa 4] ++ est))%list.
    split; [exact Hstep|].
    apply trace_stale_app.
    + apply (trace_stale_walk_shapes a2 a1 la lw esm Hd2 Hd1).
      destruct Hes as [->|[->|[-> | ->]]];
        [by left|by right; left|by right; right; left
        |by right; right; right; left].
    + simpl. right; left. split_and!; [reflexivity|exact Hdisj|exact Hste].
    + apply trace_off_win_app; [|exact Hoffe].
      apply trace_off_win_of_all. intros ak pa0 n Hin.
      apply elem_of_list_singleton in Hin. by injection Hin as -> -> ->.
  - destruct wtr.
    + (* ---------- MISS write-back: the five-event walk ---------- *)
      left. intros u Hu.
      destruct (wwalk_filter_inv w0 lw u Hu) as (av & dv & Hw & Hle).
      destruct (Hfam av dv Hle) as (sgm & esm & Hex & _ & _ & Hes).
      rewrite Hw in Hu. rewrite Hw.
      destruct (Hcore _ sgm esm Hu Hex) as (t' & est & Hstep & Hoffe & Hste).
      exists tt, t', (esm ++ ([WEread wak_plain pa 4] ++ est))%list.
    split; [exact Hstep|].
      apply trace_stale_app.
      * apply (trace_stale_walk_shapes a2 a1 la lw' esm Hd2 Hd1).
        rewrite Hes. by right; right; right; right.
      * simpl. right; left. split_and!; [reflexivity|exact Hdisj|exact Hste].
      * apply trace_off_win_app; [|exact Hoffe].
        apply trace_off_win_of_all. intros ak pa0 n Hin.
        apply elem_of_list_singleton in Hin. by injection Hin as -> -> ->.
    + (* ---------- HIT write-back: the CONSTANT-family shape ---------- *)
      right. intros u Hu.
      destruct (wwalk_filter_inv w0 lw u Hu) as (av & dv & Hw & Hle).
      destruct (Hfam av dv Hle) as (sgm & esm & Hex & _ & _ & Hes).
      rewrite Hw in Hu. rewrite Hw.
      destruct (Hcore _ sgm esm Hu Hex) as (t' & est & Hstep & Hoffe & Hste).
      exists tt, t', (esm ++ ([WEread wak_plain pa 4] ++ est))%list.
    split; [exact Hstep|].
      apply trace_off_win_app.
      * rewrite Hes. apply trace_off_win_pinned. pinned_trace.
      * apply trace_off_win_app; [|exact Hoffe].
        apply trace_off_win_of_all. intros ak pa0 n Hin.
        apply elem_of_list_singleton in Hin. by injection Hin as -> -> ->.
Qed.

(** WHAT A *WRITING* WINDOW-FREE EXECUTE WOULD STILL NEED — the one place
    where the FAMILY is narrower than the PEEL, recorded rather than hidden.

    §3's peel admits an execute that WRITES owned memory: at [W := True]
    [wstep_ok_racy]'s write arm is discharged outright, and the tail
    interfaces ([wexec_tail] and friends) say nothing about writes.  The
    family does not, and the obstruction is [trace_stale], not the run: it
    forbids a RAM write BEFORE the racy read, so a step whose walk shape has
    no racy read at all — the TLB-hit shapes [[]], [[excl-read]] and
    [[excl-read; write]] — cannot have a writing tail appended and stay
    [trace_stale].  Two of those three (the empty and the excl-read shapes)
    are today routed through §5i's LEFT disjunct, where the appended tail is
    required to be [trace_stale] as well.

    The fix is not a lemma about traces: those three shapes should go through
    the RIGHT disjunct ([trace_off_win], which admits writes), and for that
    the ⇐-bridge's [_const] arm needs the exports' family — which quantifies
    its member [(sg', es)] INSIDE the [∀ av dv] — to be exhibited as CONSTANT
    in the leaf word on precisely those shapes.  The absorption theorem does
    produce constant members there (no window read is performed at all), but
    [WkFetchPeel]'s [wwalk_exports] bundle does not say so, so the fact is not
    available to this file.  Widening the bundle with a per-shape constancy
    conjunct is the whole of the work; nothing below it changes. *)

(* ====================================================================== *)
(** ** 6. THE Q-HALF: every outcome of the step matches a family member

    [WeakStale] §10's ⇐-bridge, applied to the whole step.  Read it as: the
    weak machine's run of a WALKING instruction did exactly what ONE
    admissible leaf word's mirror run does — same result, same post-state
    (registers, memory AND device, through [wflat_st]), same trace — and any
    byte the trace does not write keeps its [latest_ts].  That conjunct is
    what a consumer turns back into pinnedness ([WkFetchPeel] §4a).

    ... and the LOG-IDENTITY conjunct on top of it ([WeakStale] §10-0's
    [wtrace_msgs]): the successor's log is the pre-log with EXACTLY the
    messages the trace's writes append, in order.  Flat-memory equality does
    not force that — a same-value rewrite appends a message and moves no byte
    — so the WP layer's continuation, which has to re-establish a log
    AUTHORITY at σ', needs the tail named rather than existentially
    quantified.  On the walk's four read-only shapes the projection computes
    to [[]] (so the log is unmoved, by [app_nil_r]); on the two write-back
    shapes to the single [WCexcl] message the absorption theorem's
    appended-log arm hands out — see [WkWalkRule] §4.

    Both arms of §5i's disjunction land here: the five stale-friendly walk
    shapes through [wrun_exec_stale_elim], the TLB-hit write-back through
    §10d's [_const] twin.  This is the certificate's Q-half in pure form —
    no Iris, no ghost state. *)

Lemma wstep_outcome_of_peel (tid : option nat) (σ : wmstate) (la : Arch.pa)
    (Φ : (nat -> bv 8) -> Prop) (tick : bool) :
  acc_wf la 8 ->
  wlog_wf (wm_log σ) ->
  is_Some (read_bytes (wflat (wm_img σ) (wm_log σ)) la 8) ->
  wstep_ok_racy tid la 8 wak_plain Φ wD_any True true (riscv_step tick) σ ->
  wadm_filter σ wak_plain la 8 Φ ->
  ((forall u : bv (8 * 8)%N, Φ (fun j : nat => nth_byte u j) ->
      exists (y : unit) (t' : mstate) (es : list weff),
        exec_stale la 8 u (riscv_step tick) (wflat_st σ) = Some (y, t', es) /\
        trace_stale wak_plain la 8 es)
   \/
   (forall u : bv (8 * 8)%N, Φ (fun j : nat => nth_byte u j) ->
      exists (y : unit) (t' : mstate) (es : list weff),
        exec_stale la 8 u (riscv_step tick) (wflat_st σ) = Some (y, t', es) /\
        trace_off_win la 8 es)) ->
  forall (x : unit) (s' : wmstate), wrun tid (riscv_step tick) σ x s' ->
    exists (u : bv (8 * 8)%N) (es : list weff),
      wadm σ wak_plain la 8 u /\ Φ (fun j : nat => nth_byte u j) /\
      exec_stale la 8 u (riscv_step tick) (wflat_st σ)
        = Some (x, wflat_st s', es) /\
      wlog_wf (wm_log s') /\
      (forall a : Arch.pa,
         wtrace_wonly (fun (pa : Arch.pa) (n : N) =>
             forall j : nat, (j < N.to_nat n)%nat -> pa_add pa j <> a) es ->
         latest_ts (wm_log s') (pa_z a) = latest_ts (wm_log σ) (pa_z a)) /\
      wm_log s' = (wm_log σ ++ wtrace_msgs tid (w_relp (wm_ws σ)) es)%list.
Proof.
  intros Hacc Hwf Hrd Hpeel Hfilt [Hst|Hoff] x s' Hrun.
  - exact (wrun_exec_stale_elim_msgs tid la 8 wak_plain Φ True (riscv_step tick)
             Hacc ltac:(lia) ak_pins_plain σ Hpeel Hwf Hfilt Hrd Hst x s' Hrun).
  - exact (wrun_exec_stale_elim_const_msgs tid la 8 wak_plain Φ True true
             (riscv_step tick) Hacc ltac:(lia) ak_pins_plain σ Hpeel Hwf Hfilt
             Hrd Hoff x s' Hrun).
Qed.

(** THE CAPSTONE: (2) + (3) + the ⇐-bridge, at the fetch-walking step. *)
Lemma wstep_outcome_fetchwalk (tid : option nat) (σ : wmstate)
    (root_ppn : mword 44) (va pa p2 p1 w0 lw : mword 64)
    (region : PMA_Region) (w : mword 32) (tick : bool) :
  let vpn := svpn_of va in
  let a2 := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
  let a1 := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  (* --- the step's own register gates --- *)
  register_lookup cur_privilege (wm_regs σ) = Supervisor ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  register_lookup PC (wm_regs σ) = va ->
  (forall bmi : bool,
     exec_eff (dispatchInterrupt Supervisor) (wflat_st (wmi σ bmi))
     = Some (None, wflat_st (wmi σ bmi), [])) ->
  (* --- the walk exports and the fetch's gates --- *)
  (forall bmi : bool,
     wfetch_ready tid (wmi σ bmi) root_ppn va pa p2 p1 w0 lw region) ->
  (* --- the text window --- *)
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  racc_disj la 8 pa 4 ->
  acc_wf pa 4 ->
  (forall j : nat, (j < 4)%nat -> pa_z (pa_add pa j) <> 0) ->
  (forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pa j)) ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     wflat (wm_img σ) (wm_log σ) !! (pa_add pa j) = Some (nth_byte w j)) ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  dev_addr pa = false ->
  (* --- the tails, on both sides of the bridge --- *)
  (forall bmi : bool, wexec_tail tid (wmi σ bmi)) ->
  (forall bmi : bool, wstep_post_tail tid (wmi σ bmi)) ->
  wstep_tick_tail tid σ tick ->
  wstep_family_ready tid σ la va pa w0 lw w tick ->
  forall (x : unit) (s' : wmstate), wrun tid (riscv_step tick) σ x s' ->
    exists (u : bv (8 * 8)%N) (es : list weff),
      wadm σ wak_plain la 8 u /\
      wwalk_filter w0 lw (fun j : nat => nth_byte u j) /\
      exec_stale la 8 u (riscv_step tick) (wflat_st σ)
        = Some (x, wflat_st s', es) /\
      wlog_wf (wm_log s') /\
      (forall a : Arch.pa,
         wtrace_wonly (fun (pa0 : Arch.pa) (n : N) =>
             forall j : nat, (j < N.to_nat n)%nat -> pa_add pa0 j <> a) es ->
         latest_ts (wm_log s') (pa_z a) = latest_ts (wm_log σ) (pa_z a)) /\
      wm_log s' = (wm_log σ ++ wtrace_msgs tid (w_relp (wm_ws σ)) es)%list.
Proof.
  intros vpn a2 a1 la Hpriv Hhart Hpc Hdisp Hready Hal HnotRVC Hdisj Haccp HW0
    Hpin Hbytes Halign Hexecp Hdev Hexec Hpost Htick Hfam.
  destruct (Hready false) as [Hexp0 _].
  pose proof Hexp0 as Hexp0'.
  destruct Hexp0' as (_ & Hwf & _ & _ & Hs0 & _).
  pose proof (pt_slot_mem_acc_wf _ _ _ Hs0) as Hacc.
  assert (Hrd : is_Some (read_bytes (wflat (wm_img σ) (wm_log σ)) la 8)).
  { exists (lw : bv (8 * 8)%N). apply read_bytes_of_bytes. intros j Hj.
    rewrite -(wflat_st_mem σ). apply (proj1 Hs0). lia. }
  destruct (wstep_peel_fetchwalk tid σ root_ppn va pa p2 p1 w0 lw region w tick
              Hpriv Hhart Hpc Hdisp Hready Hal Hdisj Haccp HW0 Hpin Hbytes
              Halign Hexecp Hdev Hexec Hpost Htick) as [Hpeel Hfilt].
  refine (wstep_outcome_of_peel tid σ la (wwalk_filter w0 lw) tick
            Hacc Hwf Hrd Hpeel Hfilt _).
  exact (wstep_family_fetchwalk tid σ root_ppn va pa p2 p1 w0 lw w tick
           Hpriv Hhart Hpc Hdisp (fun bmi => proj1 (Hready bmi))
           Hal HnotRVC Haccp Hdisj Hfam).
Qed.

(** The [wexec] corollary — the FUNCTIONAL interpreter's outcomes at EVERY
    oracle, through [WeakInterp.wexec_wrun]. *)
Lemma wexec_outcome_of_peel (tid : option nat) (σ : wmstate) (la : Arch.pa)
    (Φ : (nat -> bv 8) -> Prop) (tick : bool) :
  acc_wf la 8 ->
  wlog_wf (wm_log σ) ->
  is_Some (read_bytes (wflat (wm_img σ) (wm_log σ)) la 8) ->
  wstep_ok_racy tid la 8 wak_plain Φ wD_any True true (riscv_step tick) σ ->
  wadm_filter σ wak_plain la 8 Φ ->
  ((forall u : bv (8 * 8)%N, Φ (fun j : nat => nth_byte u j) ->
      exists (y : unit) (t' : mstate) (es : list weff),
        exec_stale la 8 u (riscv_step tick) (wflat_st σ) = Some (y, t', es) /\
        trace_stale wak_plain la 8 es)
   \/
   (forall u : bv (8 * 8)%N, Φ (fun j : nat => nth_byte u j) ->
      exists (y : unit) (t' : mstate) (es : list weff),
        exec_stale la 8 u (riscv_step tick) (wflat_st σ) = Some (y, t', es) /\
        trace_off_win la 8 es)) ->
  forall (χ : list (list nat)) (x : unit) (s' : wmstate) (χ' : list (list nat)),
    wexec tid (riscv_step tick) χ σ = Some (x, s', χ') ->
    exists (u : bv (8 * 8)%N) (es : list weff),
      wadm σ wak_plain la 8 u /\ Φ (fun j : nat => nth_byte u j) /\
      exec_stale la 8 u (riscv_step tick) (wflat_st σ)
        = Some (x, wflat_st s', es) /\
      wlog_wf (wm_log s') /\
      (forall a : Arch.pa,
         wtrace_wonly (fun (pa : Arch.pa) (n : N) =>
             forall j : nat, (j < N.to_nat n)%nat -> pa_add pa j <> a) es ->
         latest_ts (wm_log s') (pa_z a) = latest_ts (wm_log σ) (pa_z a)) /\
      wm_log s' = (wm_log σ ++ wtrace_msgs tid (w_relp (wm_ws σ)) es)%list.
Proof.
  intros Hacc Hwf Hrd Hpeel Hfilt Hfam χ x s' χ' Hex.
  exact (wstep_outcome_of_peel tid σ la Φ tick Hacc Hwf Hrd Hpeel Hfilt Hfam
           x s' (wexec_wrun tid (riscv_step tick) χ σ x s' χ' Hex)).
Qed.

(* ====================================================================== *)
(** ** 7. Soundness checks *)

Print Assumptions wstep_ok_racy_k_of_eff_nil.
Print Assumptions wstep_ok_racy_kR_of_k_cer.
Print Assumptions wrha_peel.
Print Assumptions wstep_peel.
Print Assumptions wstep_peel_fetchwalk.
Print Assumptions exec_stale_fetch_S.
Print Assumptions exec_stale_run_hart_active.
Print Assumptions exec_stale_riscv_step.
Print Assumptions exec_stale_step_of_walk.
Print Assumptions wstep_family_fetchwalk.
Print Assumptions wstep_outcome_of_peel.
Print Assumptions wstep_outcome_fetchwalk.
Print Assumptions wexec_outcome_of_peel.
