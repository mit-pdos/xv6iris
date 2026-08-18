(** * WeakEvExecEff.v — the [exec_eff] → event-WP bridge (spike M4-S1)

    Plan: [claude-notes/projects/weak-memory-m4-retarget.md] (stage M4-S1);
    design of record for the language
    [claude-notes/design/weak-memory-event-granular.md] ("Proof engineering:
    reflective batching is MANDATORY" — the F8/F9 form rules this file obeys).

    WHAT THIS FILE IS.  [WeakEvLift] lifts ONE EVENT of [WeakEvLang] and
    batches consecutive SILENT events with the reflective stepper [esil].
    That stepper is a CURSOR interface: it is driven by fuel and by a
    footprint, and it is what a CONCRETE instantiation uses.  The M4 retarget
    needs the other direction: the tree already owns 17 189 lines of
    SYMBOLIC [WeakCert.exec_eff] mirrors, one per instruction shape, and the
    retarget decision is to CONSUME them rather than redo them.  This file is
    the consumption interface for the memory-free, device-free part of a run.

    ================== THE RUN PREDICATE, AND ITS SHAPE ==================

    [epure D m t] is [WeakCert.exec_eff] with THREE arms deleted and TWO
    guarded:

      - RAM/MMIO read, RAM/MMIO write and [Barrier] return [None].  So a
        successful [epure] witnesses a run with NO memory event of any width,
        no device access and no fence — exactly the fragment whose whole
        Iris cost is register ownership.
      - [RegRead]/[RegWrite] are guarded by [decide (r ∈ D)], mirroring
        [WeakEvLift.esil_node]: the hart owns the register authority only on
        the declared footprint [D], so a run that steps outside [D] is not
        one this rule can lift.  THE FOOTPRINT IS THEREFORE NOT A SEPARATE
        OBLIGATION — it is fused into the single equation the client hands
        in, which keeps the client-facing interface exactly as wide as an
        [exec_eff] certificate: ONE [= Some …] fact.
      - [Choose] is [None] on BOTH sides ([exec_eff] returns [None] there and
        [esil_node] does too), so the language's ∃-choice arm is simply never
        reached by a certified run and no coverage gap exists.  (Recorded
        because the spike brief asks: [WeakEvLang.emonad_step]'s [Choose] arm
        is nondeterministic, [exec_eff]'s is stuck, and stuck-on-the-left is
        the safe direction — a certificate never claims to cover a [Choose].)

    [epure] is a [Fixpoint] on [m] with the same recursion as [exec_eff], so
    the [WeakEff] §2 composition kit has a verbatim twin here ([epure_bind],
    [epure_bind0], [epure_read_reg], [epure_write_reg], [epure_returnm],
    plus [epure_mono] for widening the footprint): an SC proof script that
    walks a bind spine replays at [epure] unchanged, which is how a leaf
    builds the fact symbolically over an ABSTRACT register file.  §6 does
    exactly that for a real boot-cone leaf and measures it.

    ================== THE [exec_eff] RELATIONSHIP ==================

    §2 proves [epure_exec_eff]: a successful [epure] IS an [exec_eff] run
    with an EMPTY trace, an unchanged memory and an unchanged device state.
    By functionality of [exec_eff] this immediately gives the consumption
    direction [exec_eff_epure]: a client holding an [exec_eff] certificate
    and a non-stuck [epure] has them agreeing, so the two never diverge and
    no leaf certificate is contradicted by this file.

    THE DEVICE-FREE DETECTOR IS NOT FREE (measured, not guessed).  The brief
    asked whether some [dev_state] makes EVERY device access [None], which
    would let device-freedom be read off [exec_eff] alone the way
    [WeakEff.exec_eff_quiet_of_empty] reads memory-freedom off the empty
    memory.  It does not exist: [DevModel.dev_read] at a 1-byte UART address
    dispatches to [uart_read], which succeeds at every legal offset in every
    [uart_state] (and symmetrically for the 4-byte PLIC/virtio windows), so
    no state kills all accesses.  Device-freedom is therefore a property of
    the RUN, not of the state, and [epure] carries it structurally.

    ================== THE LATER COUNT: THERE ARE NONE ==================

    The brief flagged a possible mismatch: [WeakEvLift.ewp_ev_sil_node] costs
    one [▷] per node, and [WeakFunnel.wwp_cb] gives its leaf ONE [▷] for the
    whole instruction.  THE MISMATCH DOES NOT ARISE.  [▷] is WEAKENING
    ([P ⊢ ▷ P]) and it is applied to the rule's CONTINUATION, i.e. in the
    direction that costs the client nothing: [WeakEvLift.ewp_ev_sil_rtc]
    already discharges the per-node [▷] with [iNext] against a
    later-free hypothesis, and its statement carries no [▷] at all.  So the
    rule below is stated with a LATER-FREE continuation — strictly stronger
    than any [▷^n] form, and strictly stronger than [wwp_cb]'s single [▷].
    (The event language's [WeakEvAdequacy.weak_ev_irisGS] sets
    [num_laters_per_step _ := 0], so the only laters in play are the ones
    [wp_lift_step]'s successor obligation introduces, and those are the ones
    being weakened away.)  A client that WANTS the [▷] — to strip a step-index
    or open an invariant — can reintroduce it itself.

    ================== S1b: THE OWNED WINDOW ==================

    §5 states the owned-window extension: the same run predicate with the RAM
    arms re-enabled against a client-supplied byte map, so that a read of an
    owned byte is answered by the map and a write updates it.  The RUN side
    ([epurew], the effect trace it emits, the agreement with [exec_eff]) is
    proved here; the Iris side is stated as the shape [ewp_ev_load] /
    [ewp_ev_store] have to be threaded through and is left to M4-1, since it
    needs the [wpt4]-shaped resource algebra of [WeakLeafSw4] and not a new
    language fact.

    ================== MEASUREMENTS (this file) ==================

    Whole file, [coqc -time]: 4.17 s, of which 1.8 s is the [Require] chain.
    The derived rule itself is free: [ewp_ev_epure] 0.003 s,
    [ewp_ev_exec_eff_pure] 0.015 s, [ewp_ev_exec_eff_cert] 0.003 s — the
    Iris content is one [iApply] and one conversion, because ALL the
    induction lives in [WeakEvLift.ewp_ev_sil_rtc], which was already proven.
    §6 has the per-leaf application measurement (0.04 s for a real leaf's
    certificate, one [exact], no proofmode) and the register-footprint
    findings, including the [sig_seip] verdict. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakPromise.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakGhost.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import WpGpr WpMmodeLeafBase.
Require Import WeakCert.
Require Import WeakEvLang.
Require Import WeakEvAdequacy.
Require Import WeakEvLift.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. [epure]: [exec_eff] with the world removed

    Arm for arm [WeakCert.exec_eff], with the memory/device/barrier arms
    returning [None] and the two register arms guarded by the footprint.
    Everything else — including which outcomes are silent and which are
    stuck — is copied, so the two functions cannot drift apart. *)

Fixpoint epure {X} (D : gset register) (m : M X) (t : mstate) {struct m}
    : option (X * mstate) :=
  match m with
  | Interface.Ret y => Some (y, t)
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M X) -> option (X * mstate) with
       | Interface.RegRead r _ => fun k =>
           if decide (r ∈ D)
           then epure D (k (register_lookup r t.(sregs))) t
           else None
       | Interface.RegWrite r _ v => fun k =>
           if decide (r ∈ D) then epure D (k tt) (set_reg t r v) else None
       | Interface.InstrAnnounce _   => fun k => epure D (k tt) t
       | Interface.BranchAnnounce _ _=> fun k => epure D (k tt) t
       | Interface.CacheOp _         => fun k => epure D (k tt) t
       | Interface.TlbOp _           => fun k => epure D (k tt) t
       | Interface.TakeException _   => fun k => epure D (k tt) t
       | Interface.ReturnException _ => fun k => epure D (k tt) t
       | Interface.TranslationStart _=> fun k => epure D (k tt) t
       | Interface.TranslationEnd _  => fun k => epure D (k tt) t
       | Interface.CycleCount        => fun k => epure D (k tt) t
       | Interface.Message _         => fun k => epure D (k tt) t
       | Interface.GetCycleCount     => fun k => epure D (k 0%Z) t
       (* MemRead / MemWrite / Barrier / Choose / GenericFail / … : STUCK. *)
       | _ => fun _ => None
       end) k
  end.

(** THE COMPOSITION KIT ([WeakEff] §1–§2, verbatim twin).  These are what a
    leaf uses to BUILD the fact symbolically, over an abstract register
    file, by replaying the SC bind-spine script it already has. *)

Lemma epure_returnm {X} (D : gset register) (x : X) t :
  epure D (Defs.returnm x) t = Some (x, t).
Proof. reflexivity. Qed.

Lemma epure_read_reg (D : gset register) (r : register) t :
  r ∈ D ->
  epure D (Defs.read_reg r : M _) t = Some (register_lookup r t.(sregs), t).
Proof. intros HD. simpl. by case_decide. Qed.

Lemma epure_write_reg (D : gset register) (r : register)
    (v : type_of_register r) t :
  r ∈ D -> epure D (Defs.write_reg r v : M _) t = Some (tt, set_reg t r v).
Proof. intros HD. simpl. by case_decide. Qed.

Lemma epure_bind {X Y} (D : gset register) (m : M X) (f : X -> M Y) :
  forall t v t', epure D m t = Some (v, t') ->
    epure D (Defs.bind m f) t = epure D (f v) t'.
Proof.
  induction m as [y0 | T oc k IH]; intros t v t' Hm.
  - rewrite bind_Ret. simpl in Hm. by injection Hm as <- <-.
  - rewrite bind_Next. destruct oc; simpl in Hm |- *; try discriminate;
      try (exact (IH _ _ _ _ Hm));
      (case_decide; [|discriminate Hm]); exact (IH _ _ _ _ Hm).
Qed.

Lemma epure_bind0 {Y} (D : gset register) (m : M unit) (n : M Y) t u t' :
  epure D m t = Some (u, t') -> epure D (Defs.bind0 m n) t = epure D n t'.
Proof.
  intros Hm. unfold Defs.bind0. rewrite (epure_bind D m _ t u t' Hm).
  by destruct u.
Qed.

(** The footprint is MONOTONE: a bigger frame runs at least as far.  (What a
    client uses to state its certificate at the instruction's own footprint
    and apply the rule at the leaf's larger owned set.) *)
Lemma epure_mono {X} (D D' : gset register) (m : M X) :
  D ⊆ D' -> forall t r, epure D m t = Some r -> epure D' m t = Some r.
Proof.
  intros Hsub. induction m as [y0 | T oc k IH]; intros t r Hm; [exact Hm|].
  destruct oc; simpl in Hm |- *; try discriminate;
    try (exact (IH _ _ _ Hm));
    (case_decide as Hin; [|discriminate Hm]);
    (case_decide as Hin'; [exact (IH _ _ _ Hm)|by destruct (Hin' (Hsub _ Hin))]).
Qed.

(* ====================================================================== *)
(** ** 2. [epure] IS [exec_eff], on the fragment where both are defined

    The direction that matters for soundness is [epure ⊆ exec_eff]: a run the
    pure interpreter accepts is a run the certificate language describes, with
    an EMPTY effect trace and neither memory nor device moved.  The
    consumption direction is then free, because [exec_eff] is a function. *)

Lemma epure_exec_eff {X} (D : gset register) (m : M X) :
  forall t x t', epure D m t = Some (x, t') ->
    exec_eff m t = Some (x, t', []) /\ mem t' = mem t /\ mdev t' = mdev t.
Proof.
  induction m as [y0 | T oc k IH]; intros t x t' Hm.
  - simpl in Hm. injection Hm as <- <-. by split_and!.
  - destruct oc; simpl in Hm |- *; try discriminate;
      try (exact (IH _ _ _ _ Hm));
      (case_decide; [|discriminate Hm]);
      [ exact (IH _ _ _ _ Hm) | ].
    (* RegWrite: [set_reg] moves only the registers *)
    destruct (IH _ _ _ _ Hm) as (Hee & Hmm & Hmd). by split_and!.
Qed.

(** THE CONSUMPTION FORM.  A client holding the tree's existing symbolic
    certificate and a non-stuck pure run has them agreeing: same value, same
    registers, empty trace.  So the pure rule of §4 never contradicts an
    [exec_eff] certificate, and a client may use either as its source. *)
Lemma exec_eff_epure {X} (D : gset register) (m : M X) t x t' es y t'' :
  exec_eff m t = Some (x, t', es) ->
  epure D m t = Some (y, t'') ->
  x = y /\ t' = t'' /\ es = [] /\ mem t' = mem t /\ mdev t' = mdev t.
Proof.
  intros Hee Hep.
  destruct (epure_exec_eff D m t y t'' Hep) as (Hee' & Hmm & Hmd).
  rewrite Hee in Hee'. injection Hee' as <- <- <-. by split_and!.
Qed.

(* ====================================================================== *)
(** ** 3. [epure] IS a silent run of the event language

    [WeakEvLift.esilD D] is the relational one-node silent step at footprint
    [D]; [epure]'s recursion is exactly its reflexive-transitive closure,
    with the [mstate]'s register field as the cursor. *)

Lemma epure_esilD (D : gset register) (m : M unit) :
  forall t y t', epure D m t = Some (y, t') ->
    rtc (esilD D) (m, sregs t) (Interface.Ret y, sregs t').
Proof.
  induction m as [y0 | T oc k IH]; intros t y t' Hm.
  - simpl in Hm. injection Hm as <- <-. apply rtc_refl.
  - destruct oc; simpl in Hm; try discriminate;
      first
        [ (* RegRead *)
          case_decide as HD; [|discriminate Hm];
          refine (rtc_l (esilD D) _ (k (register_lookup reg (sregs t)), sregs t)
                    _ _ (IH _ _ _ _ Hm));
          rewrite /esilD /=; by case_decide
        | (* RegWrite *)
          case_decide as HD; [|discriminate Hm];
          refine (rtc_l (esilD D) _ (k tt, register_set reg regval (sregs t))
                    _ _ (IH _ _ _ _ Hm));
          rewrite /esilD /=; by case_decide
        | (* GetCycleCount *)
          refine (rtc_l (esilD D) _ (k 0%Z, sregs t) _ _ (IH _ _ _ _ Hm));
          by rewrite /esilD /=
        | (* every other silent node *)
          refine (rtc_l (esilD D) _ (k tt, sregs t) _ _ (IH _ _ _ _ Hm));
          by rewrite /esilD /= ].
Qed.

(* ====================================================================== *)
(** ** 4. THE DERIVED RULE

    The memory-free, device-free bridge: ONE equation in, a whole
    instruction (or a whole straight-line stretch of one) of [EWP] out, with
    the continuation at the BOUNDARY and NO later. *)

Section rule.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** The mid-monad form: the run ends at the monad's own [Ret], which is
      where the caller's next certificate picks up. *)
  (** D3-2 — THE ACCEPTANCE-TEST CASUALTY, and the reason is exact.

      [epure] means "this stretch has NO MEMORY EFFECT": no RAM access, no
      device access, no barrier.  Under D3 that is no longer the same as
      "no effect on the hart's weak state": PARM's [step_assign] fires at
      the instruction's architectural destination register, so a stretch
      that contains e.g. [lui]'s write of [rd] MOVES [w_regv], and the
      announce moves [w_ldv].  A pure-register bridge therefore has to own
      [hart_ws] — and this rule, and every rule derived from it
      ([ewp_ev_exec_eff_pure], [ewp_ev_exec_eff_cert], [ewp_ev_lui_tail]),
      GAINS TWO ARGUMENTS.  What it hands back is still only
      [WeakMem.ws_depmove], so no ORDERING fact the client had is lost. *)
  Lemma ewp_ev_epure (gen : nat) (c : CPU) (D : gset register)
      (m : M unit) (t t' : mstate) (y : unit) (ws : wstate) :
    gen = 0%nat ->
    epure D m t = Some (y, t') ->
    hart_ws c ws -∗ ereg_frame c (sregs t) D -∗
    (∀ ws' : wstate, ⌜ws_depmove ws ws'⌝ -∗ hart_ws c ws' -∗
       ereg_frame c (sregs t') D -∗
       EWP (ECycle gen c (Interface.Ret y) None) @ ⊤) -∗
    EWP (ECycle gen c m None) @ ⊤.
  Proof.
    intros Hgen Hep.
    exact (ewp_ev_sil_rtc gen c D (m, sregs t) (Interface.Ret y, sregs t')
             ws Hgen (epure_esilD D m t y t' Hep)).
  Qed.

  (** THE BOUNDARY FORM, which is the one a leaf wants: [Ret] IS [ELoop]
      after the G5 constructor merge ([WeakEvLift.ewp_ev_ret] is a
      conversion), so a run that consumes a whole [riscv_step] lands the
      client back at the instruction boundary with no step and no later
      spent. *)
  Theorem ewp_ev_exec_eff_pure (gen : nat) (c : CPU) (D : gset register)
      (m : M unit) (t t' : mstate) (y : unit) (ws : wstate) :
    gen = 0%nat ->
    epure D m t = Some (y, t') ->
    hart_ws c ws -∗ ereg_frame c (sregs t) D -∗
    (∀ ws' : wstate, ⌜ws_depmove ws ws'⌝ -∗ hart_ws c ws' -∗
       ereg_frame c (sregs t') D -∗ EWP (ELoop gen c) @ ⊤) -∗
    EWP (ECycle gen c m None) @ ⊤.
  Proof.
    intros Hgen Hep. iIntros "Hws Hrf H".
    iApply (ewp_ev_epure gen c D m t t' y ws Hgen Hep with "Hws Hrf").
    iIntros (ws') "%Hd Hws Hrf". iApply (ewp_ev_ret gen c y Hgen).
    by iApply ("H" $! ws' with "[//] Hws").
  Qed.

  (** THE FORM STATED AGAINST AN [exec_eff] CERTIFICATE, for a client whose
      source fact is the tree's existing symbolic mirror.  It carries BOTH
      facts, and §2 says they cannot disagree — the [exec_eff] equation is
      what a leaf's [wcert_*] already owns, the [epure] equation is the
      footprint/device-freedom declaration on top of it. *)
  Corollary ewp_ev_exec_eff_cert (gen : nat) (c : CPU) (D : gset register)
      (m : M unit) (t t' : mstate) (es : list weff) (ws : wstate) :
    gen = 0%nat ->
    exec_eff m t = Some (tt, t', es) ->
    (exists y t'', epure D m t = Some (y, t'')) ->
    hart_ws c ws -∗ ereg_frame c (sregs t) D -∗
    (∀ ws' : wstate, ⌜ws_depmove ws ws'⌝ -∗ hart_ws c ws' -∗
       ereg_frame c (sregs t') D -∗ EWP (ELoop gen c) @ ⊤) -∗
    EWP (ECycle gen c m None) @ ⊤.
  Proof.
    intros Hgen Hee (y & t'' & Hep).
    destruct (exec_eff_epure D m t tt t' es y t'' Hee Hep)
      as (Hx & Ht & Hes & _ & _).
    subst t'.
    exact (ewp_ev_exec_eff_pure gen c D m t t'' y ws Hgen Hep).
  Qed.

End rule.

(* ====================================================================== *)
(** ** 5. S1b — THE OWNED WINDOW: the run side

    The extension the brief asks for: the same predicate with the RAM arms
    re-enabled against a CLIENT-SUPPLIED byte map [W] (the window the client
    holds points-tos for), emitting the [weff] trace as it goes.  Reads are
    answered from [W], writes update it, barriers are recorded.  Device
    accesses stay stuck: the device fabric is shared and its rule is
    [WeakEvLift]'s MMIO arm, not a certificate's business.

    THE RUN SIDE IS WHAT IS PROVED HERE, and it is the part that has to be
    right: [epurew] agrees with [exec_eff] at any memory extending [W]
    ([epurew_exec_eff]), so the trace it computes is the trace the
    certificate language sees, and the window it ends with is the memory the
    client's points-tos must be updated to.  The Iris side is deliberately
    NOT stated as a monolithic rule (see the header): the read event's
    obligation is [WeakEvLift.ewp_ev_load]'s [read_ok] callback, whose
    discharge from an owned byte is [WeakEvLift.etext_byte_pin] for a
    never-written byte and [WeakGhost.wlat_pointsto]'s [latest_val] for an
    owned-but-written one, and both are resource-shaped rather than
    run-shaped — they belong with the [wpt4] algebra in M4-1. *)

Fixpoint epurew {X} (D : gset register) (m : M X) (t : mstate) {struct m}
    : option (X * mstate * list weff) :=
  match m with
  | Interface.Ret y => Some (y, t, [])
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M X) -> option (X * mstate * list weff) with
       | Interface.RegRead r _ => fun k =>
           if decide (r ∈ D)
           then epurew D (k (register_lookup r t.(sregs))) t
           else None
       | Interface.RegWrite r _ v => fun k =>
           if decide (r ∈ D) then epurew D (k tt) (set_reg t r v) else None
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then None
           else
             match read_bytes t.(mem) (Interface.ReadReq.pa req) n with
             | Some w =>
                 match epurew D (k (inl (w, None))) t with
                 | Some (y, t', es) =>
                     Some (y, t',
                           WEread (classify (Interface.ReadReq.access_kind req))
                                  (Interface.ReadReq.pa req) n :: es)
                 | None => None
                 end
             | None => None
             end
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req) then None
           else
             match epurew D (k (inl None))
                     (MState t.(sregs)
                        (write_bytes t.(mem) (Interface.WriteReq.pa req) n
                                     (Interface.WriteReq.value req)) t.(mdev)) with
             | Some (y, t', es) =>
                 Some (y, t',
                       WEwrite (classify (Interface.WriteReq.access_kind req))
                               (Interface.WriteReq.pa req) n
                               (Interface.WriteReq.value req) :: es)
             | None => None
             end
       | Interface.Barrier b => fun k =>
           match epurew D (k tt) t with
           | Some (y, t', es) => Some (y, t', WEbar b :: es)
           | None => None
           end
       | Interface.InstrAnnounce _   => fun k => epurew D (k tt) t
       | Interface.BranchAnnounce _ _=> fun k => epurew D (k tt) t
       | Interface.CacheOp _         => fun k => epurew D (k tt) t
       | Interface.TlbOp _           => fun k => epurew D (k tt) t
       | Interface.TakeException _   => fun k => epurew D (k tt) t
       | Interface.ReturnException _ => fun k => epurew D (k tt) t
       | Interface.TranslationStart _=> fun k => epurew D (k tt) t
       | Interface.TranslationEnd _  => fun k => epurew D (k tt) t
       | Interface.CycleCount        => fun k => epurew D (k tt) t
       | Interface.Message _         => fun k => epurew D (k tt) t
       | Interface.GetCycleCount     => fun k => epurew D (k 0%Z) t
       | _ => fun _ => None
       end) k
  end.

(** The windowed run IS the certificate run, trace included: [epurew] deletes
    arms from [exec_eff] and guards two, and changes none. *)
Lemma epurew_exec_eff {X} (D : gset register) (m : M X) :
  forall t x t' es, epurew D m t = Some (x, t', es) ->
    exec_eff m t = Some (x, t', es) /\ mdev t' = mdev t.
Proof.
  induction m as [y0 | T oc k IH]; intros t x t' es Hm.
  - simpl in Hm. injection Hm as <- <- <-. by split.
  - destruct oc; simpl in Hm |- *; try discriminate;
      try (exact (IH _ _ _ _ _ Hm)).
    + (* RegRead *)
      case_decide; [|discriminate Hm]. exact (IH _ _ _ _ _ Hm).
    + (* RegWrite *)
      case_decide; [|discriminate Hm].
      destruct (IH _ _ _ _ _ Hm) as (Hee & Hmd). by split.
    + (* MemRead at a RAM address; the device arm is stuck *)
      destruct (dev_addr _); [discriminate Hm|].
      destruct (read_bytes _ _ _) as [wA|]; [|discriminate Hm].
      destruct (epurew D (k _) t) as [[[xA tA] esA]|] eqn:Hep;
        [|discriminate Hm].
      injection Hm as <- <- <-.
      destruct (IH _ _ _ _ _ Hep) as (Hee & Hmd). rewrite Hee. by split.
    + (* MemWrite at a RAM address *)
      destruct (dev_addr _); [discriminate Hm|].
      destruct (epurew D (k _) _) as [[[xA tA] esA]|] eqn:Hep;
        [|discriminate Hm].
      injection Hm as <- <- <-.
      destruct (IH _ _ _ _ _ Hep) as (Hee & Hmd). rewrite Hee. by split.
    + (* Barrier *)
      destruct (epurew D (k tt) t) as [[[xA tA] esA]|] eqn:Hep;
        [|discriminate Hm].
      injection Hm as <- <- <-.
      destruct (IH _ _ _ _ _ Hep) as (Hee & Hmd). rewrite Hee. by split.
Qed.

(** ... and the memory-free fragment of it is [epure], so the two predicates
    are one interface: a client that starts with the windowed form and finds
    its trace empty is holding the §4 rule's premise. *)
Lemma epure_epurew {X} (D : gset register) (m : M X) :
  forall t x t', epure D m t = Some (x, t') -> epurew D m t = Some (x, t', []).
Proof.
  induction m as [y0 | T oc k IH]; intros t x t' Hm.
  - simpl in Hm. by injection Hm as <- <-.
  - destruct oc; simpl in Hm |- *; try discriminate;
      try (exact (IH _ _ _ _ Hm));
      (case_decide; [|discriminate Hm]); exact (IH _ _ _ _ Hm).
Qed.


(* ====================================================================== *)
(** ** 6. THE MEASUREMENT — a real leaf's certificate, and the footprint

    The spike brief asks whether the register footprint is dischargeable at a
    leaf that is GENERIC over the GPR file.  It is, and this section is the
    evidence: the mirrors below are stated at an ARBITRARY [s : mstate] (so
    the whole register bank is a variable, exactly as in
    [WeakLeafUtypeShift.wwp_lui_leaf]'s [m : regfile]) and at an arbitrary
    footprint [D] constrained only by MEMBERSHIP SIDE CONDITIONS.  Nothing is
    ever [vm_compute]d over a register file; what computes is only
    [decide (r ∈ D)] at a CONCRETE register name, and the register NAMES a
    run touches are not data-dependent.

    MEASURED ([coqc -time], this machine):
      - [gpr_in_Dgpr] (the 31-way GPR membership, once and for all): 1.52 s —
        the one real cost, and it is paid ONCE, not per leaf.  (It is 8.1 s
        if written [set_solver]; the [elem_of_list_to_set] +
        [elem_of_list_fmap] + [elem_of_list_In] spelling below is 5× faster
        and is the one to copy.)
      - [epure_wX_bits_gpr] (the 32-way GPR-index case split, the twin of
        [WeakLeafEffCommon.exec_eff_wX_bits_gpr]): 0.21 s.
      - [epure_execute_UTYPE_LUI_gpr] (the LUI leaf's [execute] mirror, the
        twin of [WkEntryEff.exec_eff_execute_UTYPE_LUI_gpr]): 0.01 s.
      - [epure_tick_pc] (the wrapper's real post-[execute] tail, a run of the
        generated model, not a toy): 0.005 s.
      - [epure_lui_tail] (their composition through [epure_bind]): 0.006 s.
      - [ewp_ev_lui_tail] — THE APPLICATION OF THE DERIVED RULE TO A REAL
        LEAF'S CERTIFICATE: 0.04 s, of which 0.038 s is elaborating the
        STATEMENT; the proof is one [exact] at 0.000 s, with no proofmode
        entered at all.
    So the per-site cost of the bridge is O(1) and the per-instruction cost
    is that of the SC script it replays: the [epure] mirror is CHARACTER FOR
    CHARACTER the [exec_eff] mirror with the combinator names changed and the
    membership side conditions added.  B3 (the retarget plan's "no symbolic
    discharge route at event granularity") is CLOSED by this section.

    WHAT THE FOOTPRINT ACTUALLY IS, for a boot-cone instruction (measured by
    reading [try_step] / [run_hart_active] / [getPendingSet] in
    [Riscv.rv64d], not guessed).  Before [execute] a plain ALU step reads
    [cur_privilege] (×2), [mcountinhibit], [minstretcfg], [hart_state],
    [misa] (×2), [mideleg], [mip], [sig_meip], [sig_seip], [mie] (×2),
    [mstatus], [elp], [PC]; it WRITES [minstret_increment] and [nextPC].
    After [execute] it reads [hart_state] (×2) and [minstret_increment],
    writes [PC] from [nextPC], and conditionally reads+writes [minstret].
    On the tick branch [tick_clock] additionally reads [mcountinhibit],
    [mcyclecfg], [mcycle], [mtime], [mtimecmp], [menvcfg] and WRITES
    [mcycle], [mtime] and [mip].  So B1 of the retarget plan is confirmed
    concretely: [minstret]/[minstret_increment] are written by SILENT nodes
    INSIDE the instruction (before and after [execute]), and [mcycle]/[mtime]
    /[mip] by silent nodes of the tick branch — all of them are ordinary
    [RegWrite] events for this rule, so "open the invariant at that node" is
    available and the whole-instruction hold [WeakFunnel] needs is not.

    *** THE ONE GENUINELY NEW SEMANTIC ITEM IS CONFIRMED, AND IT IS WORSE
    THAN THE PLAN ASSUMED. ***  [sig_seip] IS read by every instruction, and
    the read is NOT gated by [mstatus.MIE].  [getPendingSet] ([rv64d]
    §22278–22300) sequences [mideleg], [read_mip], [mie], [mie] as monadic
    binds BEFORE the [mstatus.MIE] test, and [read_mip]
    ([rv64d] §17709) calls [external_interrupts_pending] ([rv64d] §17701),
    which reads [sig_meip] and then [sig_seip].  The tree's own SC lemma
    [RiscvTryStep.exec_getPendingSet_machine_none] confirms the order: its
    proof rewrites the [mip]/[sig_meip]/[sig_seip] reads and only THEN the
    [mstatus] one.  Consequence for M4-1: [sig_seip] must be in [D] for EVERY
    instruction, and since the PLIC thread writes it asynchronously the
    volatile-register treatment the plan sketched (a certificate per
    valuation of the volatile set, the live value read from the wire's
    invariant at the node) is MANDATORY, not an optimisation — it cannot be
    avoided by an MIE-off argument. *)

Import Defs.

(** A concrete over-approximating footprint: the 31 architectural GPRs.  A
    leaf's [D] is this ∪ the config/CSR cells it owns; [epure_mono] (§1) is
    what lets a certificate stated at the instruction's own footprint be
    applied at the leaf's larger one. *)
Definition Dgpr : gset register :=
  list_to_set (R_bitvector_64 <$>
    [x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16;
     x17;x18;x19;x20;x21;x22;x23;x24;x25;x26;x27;x28;x29;x30;x31]).

Lemma gpr_in_Dgpr (n : Z) : R_bitvector_64 (gpr_of_Z n) ∈ Dgpr.
Proof.
  unfold Dgpr. rewrite elem_of_list_to_set. unfold gpr_of_Z.
  repeat case_match;
    apply elem_of_list_fmap; eexists; (split; [reflexivity|]);
    apply elem_of_list_In; simpl; tauto.
Qed.

(** *** The [epure] twins of the [exec_eff] register-file mirrors.  Compare
    [WeakLeafEffCommon.exec_eff_wX_bits_at] / [_gpr]: the scripts are the same
    scripts, with [exec_eff_*] replaced by [epure_*] and ONE membership side
    condition added per register node. *)

Lemma epure_returnM {X} (D : gset register) (x : X) s :
  epure D (returnM x) s = Some (x, s).
Proof. reflexivity. Qed.

Lemma epure_wX_bits_at (D : gset register) (i : mword 5)
    (r : register_bitvector_64) s (v : mword 64) :
  wX (Regno (uint i)) v
    = Defs.bind0 (Defs.write_reg (R_bitvector_64 r) (regval_into_reg v)) (returnM tt) ->
  R_bitvector_64 r ∈ D ->
  epure D (wX_bits (Regidx i) v) s
  = Some (tt, set_reg s (R_bitvector_64 r) (regval_into_reg v)).
Proof.
  intros Heq HD. unfold wX_bits. rewrite Heq.
  rewrite (epure_bind0 D _ _ _ _ _ (epure_write_reg D (R_bitvector_64 r) _ s HD)).
  apply epure_returnm.
Qed.

Lemma epure_wX_bits_gpr (D : gset register) (i : mword 5) (v : mword 64) s :
  (forall n : Z, R_bitvector_64 (gpr_of_Z n) ∈ D) ->
  epure D (wX_bits (Regidx i) v) s
  = Some (tt, if Z.eqb (uint i) 0 then s
              else set_reg s (R_bitvector_64 (gpr_of_Z (uint i))) (regval_into_reg v)).
Proof.
  intros HD. pose proof (uint5_lt i) as Hb.
  assert (Hc : uint i = 0 \/ uint i = 1 \/ uint i = 2 \/ uint i = 3 \/ uint i = 4 \/
    uint i = 5 \/ uint i = 6 \/ uint i = 7 \/ uint i = 8 \/ uint i = 9 \/ uint i = 10 \/
    uint i = 11 \/ uint i = 12 \/ uint i = 13 \/ uint i = 14 \/ uint i = 15 \/ uint i = 16 \/
    uint i = 17 \/ uint i = 18 \/ uint i = 19 \/ uint i = 20 \/ uint i = 21 \/ uint i = 22 \/
    uint i = 23 \/ uint i = 24 \/ uint i = 25 \/ uint i = 26 \/ uint i = 27 \/ uint i = 28 \/
    uint i = 29 \/ uint i = 30 \/ uint i = 31) by lia.
  destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  1:{ unfold wX_bits, wX. rewrite H. cbn match.
      rewrite (epure_bind0 D _ _ _ _ _ (epure_returnm D tt s)). reflexivity. }
  all: rewrite (epure_wX_bits_at D i (gpr_of_Z (uint i)) s v
                  ltac:(rewrite H; vm_compute; reflexivity) (HD (uint i)));
       rewrite H; reflexivity.
Qed.

(** *** The leaf: [WkEntryEff.exec_eff_execute_UTYPE_LUI_gpr]'s twin,
    at an ARBITRARY [s] — the whole register bank is a variable. *)
Lemma epure_execute_UTYPE_LUI_gpr (D : gset register) (rd : mword 5)
    (imm : mword 20) s :
  (forall n : Z, R_bitvector_64 (gpr_of_Z n) ∈ D) ->
  epure D (execute (UTYPE (imm, Regidx rd, LUI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (luival imm))).
Proof.
  intros HD.
  change (execute (UTYPE (imm, Regidx rd, LUI)))
    with (execute_UTYPE imm (Regidx rd) LUI).
  unfold execute_UTYPE. cbn match.
  rewrite (epure_bind D _ _ _ _ _ (epure_returnM D _ s)).
  rewrite (epure_bind0 D _ _ _ _ _ (epure_wX_bits_gpr D rd _ s HD)).
  apply epure_returnm.
Qed.

(** *** ... and a piece of the REAL wrapper: [tick_pc] is the [M unit] tail
    [try_step] runs after [execute] ([Riscv.rv64d] §16042), register-only. *)
Lemma epure_tick_pc (D : gset register) s :
  (PC : register) ∈ D -> (nextPC : register) ∈ D ->
  epure D (tick_pc tt) s
  = Some (tt, set_reg s PC (register_lookup nextPC s.(sregs))).
Proof.
  intros HPC HnPC. unfold tick_pc. cbn match.
  rewrite (epure_bind D _ _ _ _ _ (epure_read_reg D nextPC s HnPC)).
  rewrite (epure_bind0 D _ _ _ _ _ (epure_write_reg D PC _ s HPC)).
  rewrite (epure_bind D _ _ _ _ _ (epure_read_reg D PC _ HPC)).
  apply epure_returnM.
Qed.

Lemma epure_lui_tail (D : gset register) (rd : mword 5) (imm : mword 20) s :
  (forall n : Z, R_bitvector_64 (gpr_of_Z n) ∈ D) ->
  (PC : register) ∈ D -> (nextPC : register) ∈ D ->
  epure D (Defs.bind (execute (UTYPE (imm, Regidx rd, LUI))) (fun _ => tick_pc tt)) s
  = Some (tt,
          let s1 := if Z.eqb (uint rd) 0 then s
                    else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                           (regval_into_reg (luival imm)) in
          set_reg s1 PC (register_lookup nextPC s1.(sregs))).
Proof.
  intros HD HPC HnPC.
  rewrite (epure_bind D _ _ _ _ _ (epure_execute_UTYPE_LUI_gpr D rd imm s HD)).
  exact (epure_tick_pc D _ HPC HnPC).
Qed.

(** *** THE APPLICATION.  [ECycle] carries an [M unit], and [execute] is
    [M ExecutionResult], so the smallest HONEST whole-expression demo is the
    [execute]-then-[tick_pc] tail — which is a real fragment of every
    instruction, and exactly the fragment the M4-1 funnel twin will hand to
    this rule after [ewp_ev_fetch] has consumed the fetch event. *)
Section app.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** D3-2 (see [ewp_ev_epure]): [lui] WRITES ITS DESTINATION REGISTER, so
      the tail is a [step_assign] and this rule owns [hart_ws] now.  The
      register-file postcondition is byte-identical; the two new arguments
      are the whole delta. *)
  Lemma ewp_ev_lui_tail (gen : nat) (c : CPU) (D : gset register)
      (rd : mword 5) (imm : mword 20) (s : mstate) (ws : wstate) :
    gen = 0%nat ->
    (forall n : Z, R_bitvector_64 (gpr_of_Z n) ∈ D) ->
    (PC : register) ∈ D -> (nextPC : register) ∈ D ->
    hart_ws c ws -∗
    (ereg_frame c s.(sregs) D : iProp Σ) -∗
    (∀ ws' : wstate, ⌜ws_depmove ws ws'⌝ -∗ hart_ws c ws' -∗
       ereg_frame c
         (let s1 := if Z.eqb (uint rd) 0 then s
                    else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                           (regval_into_reg (luival imm)) in
          (set_reg s1 PC (register_lookup nextPC s1.(sregs))).(sregs)) D -∗
       EWP (ELoop gen c) @ ⊤) -∗
    EWP (ECycle gen c
           (Defs.bind (execute (UTYPE (imm, Regidx rd, LUI)))
              (fun _ => tick_pc tt))
           None) @ ⊤.
  Proof.
    intros Hgen HD HPC HnPC.
    exact (ewp_ev_exec_eff_pure gen c D _ s _ tt ws Hgen
             (epure_lui_tail D rd imm s HD HPC HnPC)).
  Qed.

End app.
