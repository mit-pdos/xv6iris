(** * WeakSailLTS2.v — the ⇐ direction of the Sail bracket (lift stage L2)

    [WeakSailLTS.v] delivers the ⇒ half of the Sail bracket: a [wrun] of an
    instruction monad IS an [rtc] of promise-free steps of the [sail_step]
    LTS ([wrun_sail_bracket], [sail_instr_bracket]).  Its header delta (g)
    records what is NOT there: the ⇐ half — every COMPLETED [sail_step] block
    is a [wrun].  THIS FILE IS THAT HALF, stage L2 of
    [claude-notes/completed/weak-memory-lift.md].

    It is a NEW file rather than an extension of [WeakSailLTS.v] so that the
    latter's [.vo] stays byte-stable for the other in-flight lift stages; it
    is purely additive and folds back later if that is ever wanted.

    ------------------------------------------------------------------------
    WHAT IS DELIVERED

    (1) [dev_ok_blk] — the device-seam premise (§2).  [wrun] serves a device
        access from its own [dev_state] with the PARTIAL
        [DevModel.dev_read]/[dev_write]; [sail_step] serves it from the
        hart's private fabric [sp_dev] with the TOTALIZED
        [WeakSailLTS.dev_read_t]/[dev_write_t].  Since stage D the two
        fabrics are the same TYPE and the ⇒ bracket simply starts at
        [wm_dev s] and ends at [wm_dev s'] — nothing to assume there, because
        a [wrun] only reaches accesses the partial functions accepted.

        The ⇐ direction is handed a pf run that may have taken a device
        access the partial function DECLINES (bad width, undecoded offset):
        the pf machine stepped anyway, [wrun] cannot.  [dev_ok_blk next i c']
        excludes exactly that, and — this is the point of its shape — it is a
        predicate on the block's ACTUAL RUN (every configuration from which
        the block reaches [c']), NOT a ∀-path predicate on the monad.  A
        ∀-path form would be unsatisfiable for the same reason the OLD oracle
        premise was (see [WeakSailLTS] delta (b)): junk fetches decode to
        instructions making device accesses of every width.  Being indexed by
        the run's TARGET [c'] alone, it is also a CONSTANT of the induction
        below — no threading.

    (1') [fused_blk] — the exclusive-window seam (§2), the exact twin of
        [dev_ok_blk] and introduced for the same reason.  [WeakSailLTS]
        deltas (e)/(e'') give the two HALF-WINDOWS an arm of their own
        (hardware runs a bare [lr], a failing [sc] and a faulting AMO, and it
        runs a STANDALONE [sc] whose reservation is a different instruction's;
        the LTS was stuck at all of them).  Neither has an image in [wrun]:
        a bare exclusive read steps as a plain [LLoad], which an interpreter
        exclusive read is not; and a standalone conditional write steps as a
        plain [LStore], which [wrun] does accept structurally (its write arm
        never inspects [ak_latest]) but stamps with the message class
        [WCexcl] where the pf step carries [lbl_class], i.e. [WCrel]/
        [WCplain].  So the ⇐ direction excludes blocks that used either:
        "every exclusive access of the block is part of a FUSED rmw" — a step
        from an exclusive-read node APPENDS a message (the fused arm is an
        [LRmw], the bare one an [LLoad]), and no step is taken from a
        conditional-write node at all (the fused arm consumes that node
        INSIDE its bracket, so a pf configuration never sits there).
        Target-indexed like [dev_ok_blk], for the same no-threading reason,
        and — like it — a fact about the block's own run, not a ∀-path
        property of the monad.  Per-image discharge: kernel AMOs target
        mapped lock words and do not fault, and the kernel uses [amoswap],
        not [sc].

    (2) [sail_block_wrun] — the ⇐ bracket (§8).  A COMPLETED block of agent
        [i] (from [sp_m = None], through the events of [next tick], back to
        [sp_m = None]) yields a [wrun (Some i) (next tick) s x s'] whose
        [wmstate] effect is exactly the block's effect on the configuration:
        same image, log [wm_log s'], and agent [i] rebuilt from [s'].
        DETERMINISM IS NOT USED anywhere: the fused-RMW arm's [silent_run] and
        the [Choose] arm carry their choices existentially, and the inverse
        simply replays them into [wrun]'s ∃-arms.

    (3) [wprim_hart_block] — the hart-arm equivalence (§9), at the level L3
        consumes: one [WeakLang.wprim_step] hart arm ⇔ one completed irq-free
        block, framed by [whart_view]/[whart_write].

    ------------------------------------------------------------------------
    THE IRQ SPLIT (deliberate, and what L3 must do with it).

    [sail_step]'s [irq_deliver] arm (WeakSailLTS delta (b')) has NO image in
    [wrun]: an interrupt delivery is a [RiscvLang.plic_step], i.e. a SEPARATE
    [WeakLang.wprim_step] arm, not part of any instruction's [wrun].  So the
    ⇐ bracket is stated for IRQ-FREE blocks: §1 defines [sail_step_ni]
    ([sail_step] minus the irq arm), [sail_step_irq_or_ni] splits an arbitrary
    [sail_step] into "one irq delivery" or "one [sail_step_ni]", and
    [sail_step_ni_irq] / [pf_solo_irq] show a block leaves [sp_irq] untouched
    (so "the block consumed no irq entry" is observable, and conversely a
    segment with [sp_irq] unchanged is irq-free).  L3 regroups a pf run into
    (irq step | irq-free block)* and maps the irq steps to plic steps.

    ------------------------------------------------------------------------
    THE PF-SIDE FAITHFULNESS RESIDUE (§2, [pf_solo]).

    [WeakPromiseBridge.wp_pf_step] is strictly LOOSER than the interpreter in
    two inert-looking respects, and the ⇐ has to close both.  Neither affects
    the pf machine's own dynamics; both are recorded in [pf_solo] as side
    conditions on the block, exactly as [dev_ok_blk] records the device seam.

    (a) MESSAGE CLASS.  [wrun] COMPUTES the class ([wm_class_of]).
        [lbl_class] is that computation expressed in the data a pf step has
        ([wlabel] + the agent's [wstate]) — it agrees with [wm_class_of] on
        every step [sail_step] can take, because the plain store arm pins
        [ak_latest = false] and [ak_sync = rl] and the fused arm pins
        [ak_latest = true] ([lbl_class_store], [wr_node_class]).
        [cls_canon] requires the block's messages to carry it.

        SINCE G6a [PFStore]/[PFRmw] PIN the class rather than leaving it a
        free binder ("inert — no rule reads it", WeakMem §5): the arms carry
        [k = pcls l (pa_ws ag)], and every pf step below is taken at
        [pcls := lbl_class].  [cls_canon] is therefore now IMPLIED by the
        step it accompanies rather than an independent restriction — it is
        kept in [pf_solo] verbatim because the ⇐ direction reads it directly
        and because it is the statement that survives if the machine's binder
        is ever freed again.  [lbl_class_obl] discharges the replay-side half
        of the pinning ([WeakRobustTrace.pcls_obl]) once, below.

    (b) RMW READ ADMISSIBILITY.  [PFRmw] carries [read_ok … lat := false] plus
        PARM's [excl_ok], which forbids only OTHER agents' writes in the
        window; [wrun]'s exclusive read ([wbyte_ok] at [ak_latest]) forbids
        ALL writes, including the reader's own.  [rmw_tight] requires the
        stronger [read_ok … lat := true], which is what [wread_ok] gives on
        the ⇒ side ([WeakSailLTS.wread_read_ok] deliberately weakens it).

    Both are the safe direction for L3's use (they restrict the pf runs that
    must be mapped back, and every pf run the ⇒ bracket PRODUCES satisfies
    them); the alternative — retagging an arbitrary pf run to canonical
    classes and tightening its rmw reads — is a [WeakPromiseBridge]-level
    lemma and is deliberately out of L2's scope.

    ------------------------------------------------------------------------
    WHAT L3 CONSUMES.  [sail_block] (the block relation), [dev_ok_blk] and
    [fused_blk]
    (stated premises it must thread from the MMIO / exclusive-window seams),
    [sail_block_wrun]
    and [wprim_hart_block_bwd] (to turn each hart block of a block-atomic pf
    run into one [wprim_step]), [pf_solo_run] (a block IS a [wp_pf_run] run,
    so the two brackets sandwich), and [sail_step_irq_or_ni] / [pf_solo_irq]
    (to do the regrouping).

    NOTE ON NAMES.  [WeakPromise] and [WeakAxiomatic] both export
    [LLoad]/[LStore]/[LFence]/[LRmw]; every occurrence below is QUALIFIED
    [WeakPromise.LLoad] &c, as in [WeakSailLTS.v]. *)
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From Stdlib.ssr Require Import ssreflect.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import DevModel.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge.
From xv6iris Require Import WeakInterp WeakInterpProj WeakSailLTS.
(* [WeakRobustTrace] only for [pcls_obl], the replay-side obligation
   [lbl_class] discharges below (§2); it depends on nothing Sail-side. *)
From xv6iris Require Import WeakRobustTrace.
Require Import RiscvLang WeakLang.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The irq-free fragment of [sail_step]

    [sail_step] is [irq_deliver ∨ (the parked fence / boundary / monad
    arms)].  [sail_step_ni] is the right disjunct — everything an INSTRUCTION
    does.  The two lemmas below are the split L3 regroups on. *)

Definition sail_step_ni (next : bool → M unit)
    (p : psail) (l : wlabel) (p' : psail) : Prop :=
  match sp_fence p with
  | Some (pr, pw, sr, sw) =>
      l = WeakPromise.LFence pr pw sr sw ∧
      p' = PSail (sp_m p) (sp_regs p) (sp_dev p) None (sp_irq p)
  | None =>
      match sp_m p with
      | None =>
          l = WeakPromise.LSilent ∧
          ∃ tick : bool,
            p' = PSail (Some (next tick)) (sp_regs p) (sp_dev p) None (sp_irq p)
      | Some m => sail_mstep m (sp_regs p) (sp_dev p) (sp_irq p) l p'
      end
  end.

Lemma sail_step_ni_step next p l p' :
  sail_step_ni next p l p' → sail_step next p l p'.
Proof.
  rewrite /sail_step_ni /sail_step.
  destruct (sp_fence p) as [[[[pr pw] sr] sw]|]; [done|]. by right.
Qed.

(** Every [sail_step] is either ONE interrupt delivery (which has no image in
    [wrun] at all — it is a [plic_step] of the real machine) or one irq-free
    step.  This is the split L3's regrouping runs on. *)
Lemma sail_step_irq_or_ni next p l p' :
  sail_step next p l p' →
  (sp_fence p = None ∧ irq_deliver p l p') ∨ sail_step_ni next p l p'.
Proof.
  rewrite /sail_step /sail_step_ni.
  destruct (sp_fence p) as [[[[pr pw] sr] sw]|] eqn:Hf; [by right|].
  intros [Hirq|H]; [left; by split|by right].
Qed.

(** ... and an irq-free step consumes NO interrupt-oracle entry: [sp_irq] is
    literally preserved.  So a segment whose [sp_irq] is unchanged is
    irq-free, which is how L3 recognises a block. *)
Lemma sail_step_ni_irq next p l p' :
  sail_step_ni next p l p' → sp_irq p' = sp_irq p.
Proof.
  rewrite /sail_step_ni.
  destruct (sp_fence p) as [[[[pr pw] sr] sw]|]; [by intros [_ ->]|].
  destruct (sp_m p) as [m|]; [|by intros [_ [tick ->]]].
  rewrite /sail_mstep. destruct m as [y|T oc k]; [by intros [_ ->]|].
  destruct oc; simpl; try (by intros [_ ->]); try done.
  - (* MemRead *)
    destruct (dev_addr _).
    + by intros [_ ->].
    + intros [_ H].
      destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data
                    |pr pw sr sw]; try done.
      * destruct lat; [done|].
        by destruct H as (_ & _ & _ & w & _ & ->).
      * by destruct H as (_ & _ & _ & _ & _ & w & m1 & m2 & rs1 & _ & _ & _ & ->).
  - (* MemWrite *)
    destruct (dev_addr _); [by intros [_ ->]|]. by intros (_ & _ & ->).
  - (* Choose *)
    by intros [_ [c ->]].
Qed.

(* ====================================================================== *)
(** ** 2. The faithful solo pf step, and what a BLOCK is

    A block is a run of the ONE agent [i] (the log may not grow underneath
    it, or no [wrun] could be reconstructed), over [sail_step_ni] (the irq
    split), with the two faithfulness side conditions of the header. *)

(** The message class [wrun] would compute, expressed in the data a pf step
    has.  Compare [WeakInterp.wm_class_of]: the plain-store arm of
    [sail_mstep] pins [ak_latest = false] and [aq = ak_sync], and the fused
    arm's write half pins [ak_latest = true] ([wr_node]). *)
Definition lbl_class (l : wlabel) (ws : wstate) : wm_class :=
  match l with
  | WeakPromise.LStore rl _ _ => if (w_relp ws || rl)%bool then WCrel else WCplain
  | WeakPromise.LRmw _ _ _ _ _ => WCexcl
  | _ => WCplain
  end.

Lemma lbl_class_store ak ws base data :
  ak_latest ak = false →
  wm_class_of ak ws = lbl_class (WeakPromise.LStore (ak_sync ak) base data) ws.
Proof. intros H. by rewrite /wm_class_of /lbl_class H. Qed.

Lemma lbl_class_rmw ak ws aq rl base tvs data :
  ak_latest ak = true →
  wm_class_of ak ws = lbl_class (WeakPromise.LRmw aq rl base tvs data) ws.
Proof. intros H. by rewrite /wm_class_of /lbl_class H. Qed.

(** THE REPLAY-SIDE OBLIGATION (G6a).  [lbl_class] is the canonical [pcls]
    for the whole archive route, and the replay ([WeakRobustSim]) hands the
    same events back at PERMUTED timestamps — so the class function must look
    at no timestamp.  [lbl_class] looks at [rl] and at [w_relp ws] on the
    store arm and is constant on the rmw arm, so it does not.  Every archive
    consumer that owes [WeakRobustTrace.pcls_obl] discharges it with this. *)
Lemma lbl_class_obl : pcls_obl lbl_class.
Proof.
  split.
  - intros rl base data ws ws' Hrel. by rewrite /lbl_class Hrel.
  - intros aq rl base tvs tvs' data ws ws' _ _. reflexivity.
Qed.

(** (a) the class the step appends is the computed one. *)
Definition cls_canon (i : agent) (l : wlabel) (c c' : wpcfg psail unit) : Prop :=
  ∀ ag msg, pc_ags c !! i = Some ag → pc_log c' = pc_log c ++ [msg] →
    wm_ak msg = lbl_class l (pa_ws ag).

(** (b) the rmw read half is admissible in the interpreter's STRONG sense
    (no write at all in the window, not merely no other agent's). *)
Definition rmw_tight (i : agent) (l : wlabel) (c : wpcfg psail unit) : Prop :=
  match l with
  | WeakPromise.LRmw aq _ base tvs _ =>
      ∀ ag, pc_ags c !! i = Some ag →
        read_ok (pc_img c) (pc_log c) (pa_ws ag) aq true base tvs
  | _ => True
  end.

Definition pf_solo (next : bool → M unit) (i : agent)
    (c c' : wpcfg psail unit) : Prop :=
  ∃ l : wlabel,
    wp_pf_step (pstep_unit (sail_step_ni next)) lbl_class i l c c' ∧
    cls_canon i l c c' ∧ rmw_tight i l c.

(** A block IS a promise-free run — the two brackets sandwich the same
    relation. *)
Lemma pf_solo_run next i c c' :
  pf_solo next i c c' → wp_pf_run (pstep_unit (sail_step next)) lbl_class c c'.
Proof.
  intros (l & Hstep & _ & _). exists i, l.
  destruct Hstep as
    [cfg ag st' dd Hlk Hps
    |cfg ag aq lat base tvs st' dd Hlk Hps Hr
    |cfg ag rl base data kk st' dd Hlk Hps Hne Hkc
    |cfg ag aq rl base tvs data kk st' dd Hlk Hps Hne Hlen Hr He Hkc
    |cfg ag pr pw sr sw st' dd Hlk Hps];
    [ by eapply PFSilent, sail_step_ni_step
    | by eapply PFLoad; [done|apply sail_step_ni_step|done]
    | by eapply PFStore; [done|apply sail_step_ni_step|done|done]
    | by eapply PFRmw; [done|apply sail_step_ni_step|done|done|done|done|done]
    | by eapply PFFence; [done|apply sail_step_ni_step] ].
Qed.

Lemma lookup_insert_at (l : list (wpagent psail)) (i : agent) a b :
  l !! i = Some a → (<[i := b]> l) !! i = Some b.
Proof. intros H. apply list_lookup_insert. exact (lookup_lt_Some _ _ _ H). Qed.

Lemma pf_solo_irq next i c c' ag :
  pf_solo next i c c' → pc_ags c !! i = Some ag →
  ∃ ag', pc_ags c' !! i = Some ag' ∧ sp_irq (pa_st ag') = sp_irq (pa_st ag).
Proof.
  intros (l & Hstep & _ & _) Hlk.
  destruct Hstep as
    [cfg ag0 st' dd H0 Hps
    |cfg ag0 aq lat base tvs st' dd H0 Hps Hr
    |cfg ag0 rl base data kk st' dd H0 Hps Hne Hkc
    |cfg ag0 aq rl base tvs data kk st' dd H0 Hps Hne Hlen Hr He Hkc
    |cfg ag0 pr pw sr sw st' dd H0 Hps];
    simpl in Hlk; rewrite Hlk in H0; injection H0 as <-;
    (eexists; (split;
      [ by eapply lookup_insert_at, Hlk
      | simpl; by apply (sail_step_ni_irq next _ _ _ Hps) ])).
Qed.

(** The agent's position in the block: at an instruction boundary, or
    strictly inside one. *)
Definition at_boundary (i : agent) (c : wpcfg psail unit) : Prop :=
  ∃ ag, pc_ags c !! i = Some ag ∧ sp_m (pa_st ag) = None.

Definition in_block (i : agent) (c : wpcfg psail unit) : Prop :=
  ∃ ag, pc_ags c !! i = Some ag ∧ sp_m (pa_st ag) ≠ None.

Lemma boundary_not_in_block i c : at_boundary i c → in_block i c → False.
Proof.
  intros (ag & Hlk & He) (ag' & Hlk' & Hne).
  rewrite Hlk in Hlk'. by injection Hlk' as <-.
Qed.

(** One step of the block, taken from INSIDE the block.  The source-side
    gating is what pins a block down: an [rtc] of these from the first
    in-block configuration to a boundary can pass through no boundary
    strictly inside. *)
Definition pf_in_block (next : bool → M unit) (i : agent)
    (c c' : wpcfg psail unit) : Prop :=
  in_block i c ∧ pf_solo next i c c'.

(** THE BLOCK: boundary, one step that loads [next tick], the instruction's
    events, boundary. *)
Definition sail_block (next : bool → M unit) (i : agent)
    (c c' : wpcfg psail unit) : Prop :=
  at_boundary i c ∧ at_boundary i c' ∧
  ∃ c0, pf_solo next i c c0 ∧ rtc (pf_in_block next i) c0 c'.

(** *** [dev_ok_blk]: the device seam, stated on the block's ACTUAL RUN

    [WeakSailLTS.sail_mstep]'s device arms are TOTAL: an access
    [DevModel.dev_read]/[dev_write] declines (bad width, undecoded offset in
    a device window) reads junk and leaves the fabric alone.  [wrun] is not
    total there — it is STUCK.  So the ⇐ direction must know that every
    device access the block actually performed was one the partial functions
    accepted; [dev_ok_m] is that fact at one monad node, [dev_ok] at one
    configuration, and [dev_ok_blk] over the whole block.

    THE INDEXING IS BY THE BLOCK'S TARGET [c'], not its source, and that is
    deliberate: every peel of the induction below hands back an [rtc] to the
    SAME [c'], so [dev_ok_blk next i c'] is a constant of the induction and
    needs no threading.  (Indexing by the source would need the peeled step
    to be exported by every forcing lemma.)  It is also why the premise is
    NOT a ∀-path predicate on the monad: which device access is reached
    depends on the RAM values read, and the pf run pins those. *)
Definition dev_ok_m (d : dev_state) (m : option (M unit)) : Prop :=
  match m with
  | Some (Interface.Next oc _) =>
      match oc with
      | Interface.MemRead n req =>
          if dev_addr (Interface.ReadReq.pa req)
          then is_Some (dev_read d (Interface.ReadReq.pa req) n)
          else True
      | Interface.MemWrite n req =>
          if dev_addr (Interface.WriteReq.pa req)
          then is_Some (dev_write d (Interface.WriteReq.pa req) n
                          (Interface.WriteReq.value req))
          else True
      | _ => True
      end
  | _ => True
  end.

Definition dev_ok (i : agent) (c : wpcfg psail unit) : Prop :=
  ∀ ag, pc_ags c !! i = Some ag → dev_ok_m (sp_dev (pa_st ag)) (sp_m (pa_st ag)).

Definition dev_ok_blk (next : bool → M unit) (i : agent)
    (c' : wpcfg psail unit) : Prop :=
  ∀ c1, rtc (pf_in_block next i) c1 c' → dev_ok i c1.

(** *** [fused_blk]: the exclusive-window seam, the SECOND run-local side
    condition, and the exact twin of [dev_ok_blk]

    [WeakSailLTS] delta (e) gives an [ak_latest] read TWO arms: the FUSED one
    (one [LRmw] label spanning read, silent window and conditional write) and
    the BARE one (one ordinary [LLoad], since stage C8 a single step — an
    exclusive read that is not part of a fused rmw simply loads).  Only the
    fused one has an image in [wrun]: the interpreter's exclusive read is not
    a plain load, and its [wbyte_ok] at [ak_latest] is strictly stronger than
    the [read_ok] a [PFLoad] carries.  Delta (e'') adds the MIRROR arm on the write side: a
    STANDALONE conditional write (a lone [sc]) steps as a plain [LStore],
    which [wrun] does take — its write arm never inspects [ak_latest] — but
    stamps with [WCexcl] ([WeakInterp.wm_class_of]) where the pf step carries
    [lbl_class], i.e. [WCrel]/[WCplain].  So the ⇐ direction must know the
    block took NEITHER half-window arm — and, exactly as for the device seam,
    that is a fact about the block's ACTUAL RUN, not a ∀-path property of the
    monad (which value a window is abandoned at depends on what was read).

    [at_excl_read i c] is "agent [i] is AT an exclusive RAM read" and
    [at_con_write i c] is "agent [i] is AT a conditional RAM write" (both
    with no parked fence, so the step really is the access's).  A step from
    an exclusive read is fused exactly when it APPENDS a message — the fused
    arm is an [LRmw], the bare one an [LLoad], and nothing else can fire
    there — and a conditional-write configuration may not be reached at all:
    the fused arm consumes the write node INSIDE its bracket, so the only way
    a pf configuration sits at one is the standalone arm.  Together that is
    [pf_solo_f], and it needs no label to state.

    THE INDEXING IS BY THE BLOCK'S TARGET [c'], for the reason recorded at
    [dev_ok_blk]: every peel hands back an [rtc] to the SAME [c'], so
    [fused_blk next i c'] is a constant of the mutual induction below.  It is
    also deliberately NOT a conjunct of [pf_solo]: [WeakSailComplete]'s
    reader-tail completion constructs [pf_solo] steps over an arbitrary
    residual and takes the bare arms where the window is abandoned or never
    opened, so it could not discharge one. *)
Definition excl_read_node (m : option (M unit)) : Prop :=
  match m with
  | Some (Interface.Next oc _) =>
      match oc with
      | Interface.MemRead n req =>
          dev_addr (Interface.ReadReq.pa req) = false ∧
          ak_latest (classify (Interface.ReadReq.access_kind req)) = true
      | _ => False
      end
  | _ => False
  end.

Definition at_excl_read (i : agent) (c : wpcfg psail unit) : Prop :=
  ∃ ag, pc_ags c !! i = Some ag ∧ sp_fence (pa_st ag) = None ∧
        excl_read_node (sp_m (pa_st ag)).

(** …and the mirror node ([WeakSailLTS] delta (e'')): a CONDITIONAL RAM
    write.  A pf configuration can only sit at one when the write is
    STANDALONE — inside a fused window the write node is consumed by the
    read's [LRmw] bracket and is never an agent state. *)
Definition con_write_node (m : option (M unit)) : Prop :=
  match m with
  | Some (Interface.Next oc _) =>
      match oc with
      | Interface.MemWrite n req =>
          dev_addr (Interface.WriteReq.pa req) = false ∧
          ak_latest (classify (Interface.WriteReq.access_kind req)) = true
      | _ => False
      end
  | _ => False
  end.

Definition at_con_write (i : agent) (c : wpcfg psail unit) : Prop :=
  ∃ ag, pc_ags c !! i = Some ag ∧ sp_fence (pa_st ag) = None ∧
        con_write_node (sp_m (pa_st ag)).

Definition pf_solo_f (next : bool → M unit) (i : agent)
    (c c' : wpcfg psail unit) : Prop :=
  pf_solo next i c c' ∧ (at_excl_read i c → pc_log c' ≠ pc_log c) ∧
  ¬ at_con_write i c.

Lemma pf_solo_f_solo next i c c' : pf_solo_f next i c c' → pf_solo next i c c'.
Proof. by intros [H _]. Qed.

Definition fused_blk (next : bool → M unit) (i : agent)
    (c' : wpcfg psail unit) : Prop :=
  ∀ c1 c2, pf_solo next i c1 c2 → rtc (pf_in_block next i) c2 c' →
           pf_solo_f next i c1 c2.

(* ====================================================================== *)
(** ** 4. Replaying registers and the write node into [wrun]

    The silent window of a fused RMW is [silent_run] on
    [(M unit * regstate)]; the matching [wrun] arms touch nothing but
    [wm_regs].  [WeakSailLTS.wregs_set] is the whole-file register update the
    replay needs ([WeakInterp.wset_reg] is the single-register one). *)

Lemma silent1_wrun tid (c c' : M unit * regstate) s x s'' :
  silent1 c c' →
  wrun tid c'.1 (wregs_set s c'.2) x s'' →
  wrun tid c.1 (wregs_set s c.2) x s''.
Proof.
  destruct c as [m rs]. rewrite /silent1 /=.
  destruct m as [y|T oc k]; [done|].
  destruct oc; simpl; try done;
    try (by intros ->; simpl); try (by intros [ch ->]; simpl; exists ch).
Qed.

Lemma silent_run_wrun' tid (c c' : M unit * regstate) s x s'' :
  silent_run c c' →
  wrun tid c'.1 (wregs_set s c'.2) x s'' →
  wrun tid c.1 (wregs_set s c.2) x s''.
Proof.
  induction 1 as [|a b e Hab Hbe IH]; [done|].
  intros H. eapply silent1_wrun; [exact Hab|]. by apply IH.
Qed.

Lemma silent_run_wrun tid (m m' : M unit) (rs' : regstate) s x s'' :
  silent_run (m, wm_regs s) (m', rs') →
  wrun tid m' (wregs_set s rs') x s'' →
  wrun tid m s x s''.
Proof.
  intros H1 H2.
  have H := silent_run_wrun' tid (m, wm_regs s) (m', rs') s x s'' H1 H2.
  simpl in H. by rewrite wregs_set_id in H.
Qed.

(** The write half of a fused RMW, replayed into [wrun]'s store arm.  The
    class is [WCexcl] because [wr_node] pins [ak_latest = true]. *)
Lemma wr_node_wrun (tid : option nat) m1 rl base data m2 s x s'' :
  wr_node m1 rl base data m2 →
  wrun tid m2
    (WMState (wm_regs s) (wm_img s)
       (wm_log s ++ [WMsg base data tid WCexcl])
       (store_post_run (wm_ws s) rl base (length data) (S (length (wm_log s))))
       (wm_dev s)) x s'' →
  wrun tid m1 s x s''.
Proof.
  destruct m1 as [y|T oc k]; [done|].
  destruct oc; try done. simpl.
  intros (Hd & Hn & Hlat & Hrl & Hbase & Hdata & Hm2) H.
  rewrite Hd. subst m2 rl base data. rewrite wbytes_length in H.
  rewrite /wwrite_post /wwrite_msg /wm_class_of Hlat.
  exact H.
Qed.

(* ====================================================================== *)
(** ** 5. [read_ok] ⟹ [wread_ok]: the converse of [WeakSailLTS.wread_read_ok]

    The pf side indexes by [tvs !! j]; the interpreter by [j < n] with the
    timestamps in [ts] and the values in the word.  [lat] is passed as
    [ak_latest ak] — [false] for a plain load (which is what [PFLoad] carries)
    and [true] for the fused arm (which is what [rmw_tight] supplies). *)
Lemma read_ok_wread_ok (s : wmstate) (ak : akinfo) (pa : Arch.pa) (n : N)
    (tvs : list (nat * bv 8)) (w : bv (8 * n)) :
  ak_coh ak = false →
  length tvs = N.to_nat n →
  (∀ j : nat, (j < N.to_nat n)%nat → tvs.*2 !! j = Some (nth_byte w j)) →
  read_ok (wimg s) (wm_log s) (wm_ws s) (ak_sync ak) (ak_latest ak)
          (pa_z pa) tvs →
  wread_ok s ak pa n tvs.*1 w.
Proof.
  intros Hcoh Hlen Hval Hok. split; [by rewrite length_fmap|].
  intros j Hj.
  have Hjn : (j < N.to_nat n)%nat by lia.
  have Hlt : (j < length tvs)%nat by lia.
  destruct (lookup_lt_is_Some_2 tvs j Hlt) as [[t v] Htv].
  have Hv : v = nth_byte w j.
  { have Hs := Hval j Hjn. rewrite list_lookup_fmap Htv /= in Hs.
    by injection Hs as <-. }
  have Ht : tvs.*1 !!! j = t.
  { rewrite list_lookup_total_alt list_lookup_fmap Htv //. }
  destruct (Hok j t v Htv) as (Hb & Hrd & Hlat).
  rewrite /wbyte_ok /acc_addr Ht Hcoh -Hv. split_and!; [exact Hb|exact Hrd|].
  intros Hl. by apply Hlat.
Qed.

(* ====================================================================== *)
(** ** 6. Peeling a block step

    Every arm below has the same skeleton: the agent is in the block, so the
    run is not finished; peel its first step, read off which pf arm it was
    (the [sail_step_ni] arm at the current monad node determines the label,
    so four of the five are contradictory), and recurse. *)

Section peel.
  Context (next : bool → M unit) (i : agent).

  Implicit Types c : wpcfg psail unit.
  Implicit Types ags : list (wpagent psail).

  (** The five pf arms with the two faithfulness conditions already read
      off: the store/rmw classes are the computed ones and the rmw read is
      the tight one. *)
  Lemma pf_solo_inv c c' :
    pf_solo next i c c' →
    ∃ ag, pc_ags c !! i = Some ag ∧
      ((∃ st', sail_step_ni next (pa_st ag) WeakPromise.LSilent st' ∧
          c' = WPCfgU (pc_img c) (pc_log c)
                 (<[i := WPAgent st' (pa_ws ag) (pa_prom ag)]> (pc_ags c)))
     ∨ (∃ aq lat base tvs st',
          sail_step_ni next (pa_st ag) (WeakPromise.LLoad aq lat base tvs) st' ∧
          read_ok (pc_img c) (pc_log c) (pa_ws ag) aq lat base tvs ∧
          c' = WPCfgU (pc_img c) (pc_log c)
                 (<[i := WPAgent st' (load_post_run (pa_ws ag) aq base tvs.*1)
                           (pa_prom ag)]> (pc_ags c)))
     ∨ (∃ rl base data st',
          sail_step_ni next (pa_st ag) (WeakPromise.LStore rl base data) st' ∧
          data ≠ [] ∧
          c' = WPCfgU (pc_img c)
                 (pc_log c ++ [WMsg base data (Some i)
                                 (lbl_class (WeakPromise.LStore rl base data)
                                    (pa_ws ag))])
                 (<[i := WPAgent st'
                           (store_post_run (pa_ws ag) rl base (length data)
                              (S (length (pc_log c)))) (pa_prom ag)]> (pc_ags c)))
     ∨ (∃ aq rl base tvs data st',
          sail_step_ni next (pa_st ag) (WeakPromise.LRmw aq rl base tvs data) st' ∧
          data ≠ [] ∧ length tvs = length data ∧
          read_ok (pc_img c) (pc_log c) (pa_ws ag) aq true base tvs ∧
          excl_ok (pc_log c) i base tvs (S (length (pc_log c))) ∧
          c' = WPCfgU (pc_img c)
                 (pc_log c ++ [WMsg base data (Some i) WCexcl])
                 (<[i := WPAgent st'
                           (store_post_run
                              (load_post_run (pa_ws ag) aq base tvs.*1)
                              rl base (length data) (S (length (pc_log c))))
                           (pa_prom ag)]> (pc_ags c)))
     ∨ (∃ pr pw sr sw st',
          sail_step_ni next (pa_st ag) (WeakPromise.LFence pr pw sr sw) st' ∧
          c' = WPCfgU (pc_img c) (pc_log c)
                 (<[i := WPAgent st' (fence_post (pa_ws ag) pr pw sr sw)
                           (pa_prom ag)]> (pc_ags c)))).
  Proof.
    intros (l & Hstep & Hcls & Hrmw).
    destruct Hstep as
      [cfg ag st' dd Hlk Hps
      |cfg ag aq lat base tvs st' dd Hlk Hps Hr
      |cfg ag rl base data kk st' dd Hlk Hps Hne Hkc
      |cfg ag aq rl base tvs data kk st' dd Hlk Hps Hne Hlen Hr He Hkc
      |cfg ag pr pw sr sw st' dd Hlk Hps]; destruct dd.
    - exists ag. split; [done|]. left. by exists st'.
    - exists ag. split; [done|]. right; left. by exists aq, lat, base, tvs, st'.
    - exists ag. split; [done|]. right; right; left.
      have Hk : kk = lbl_class (WeakPromise.LStore rl base data) (pa_ws ag).
      { exact (Hcls ag (WMsg base data (Some i) kk) Hlk eq_refl). }
      exists rl, base, data, st'. split_and!; [done|done|]. by rewrite -Hk.
    - exists ag. split; [done|]. right; right; right; left.
      have Hk : kk = lbl_class (WeakPromise.LRmw aq rl base tvs data) (pa_ws ag).
      { exact (Hcls ag (WMsg base data (Some i) kk) Hlk eq_refl). }
      exists aq, rl, base, tvs, data, st'. split_and!; [done|done|done| |done|].
      + exact (Hrmw ag Hlk).
      + by rewrite Hk.
    - exists ag. split; [done|]. right; right; right; right.
      by exists pr, pw, sr, sw, st'.
  Qed.

  (** In the block ⟹ the run has not stopped: peel the first step. *)
  Lemma block_peel c c' ag :
    pc_ags c !! i = Some ag → sp_m (pa_st ag) ≠ None →
    rtc (pf_in_block next i) c c' → at_boundary i c' →
    ∃ c1, pf_solo next i c c1 ∧ rtc (pf_in_block next i) c1 c'.
  Proof.
    intros Hlk Hne Hrtc Hbd. apply rtc_inv in Hrtc as [->|(c1 & (_ & Hs) & Hr)].
    - exfalso. eapply boundary_not_in_block; [exact Hbd|]. by exists ag.
    - by exists c1.
  Qed.

  (** ... and at a boundary it HAS stopped: no [pf_in_block] step leaves. *)
  Lemma block_done c c' : at_boundary i c → rtc (pf_in_block next i) c c' → c' = c.
  Proof.
    intros Hbd Hrtc. apply rtc_inv in Hrtc as [->|(c1 & (Hin & _) & _)]; [done|].
    exfalso. exact (boundary_not_in_block i c Hbd Hin).
  Qed.

  (** The three forced-shape corollaries the arms below use. *)
  Lemma block_forced_silent (p : psail) ws img log prom ags c'
      (Q : psail → Prop) :
    ags !! i = Some (WPAgent p ws prom) → sp_m p ≠ None →
    (∀ l st', sail_step_ni next p l st' → l = WeakPromise.LSilent ∧ Q st') →
    rtc (pf_in_block next i) (WPCfgU img log ags) c' →
    at_boundary i c' →
    ∃ p1, Q p1 ∧
      rtc (pf_in_block next i)
        (WPCfgU img log (<[i := WPAgent p1 ws prom]> ags)) c'.
  Proof.
    intros Hlk Hne Hforce Hrtc Hbd.
    destruct (block_peel (WPCfgU img log ags) c' _ Hlk Hne Hrtc Hbd)
      as (c1 & Hsolo & Hrtc1).
    destruct (pf_solo_inv _ _ Hsolo) as (ag & Hag & Hcase).
    simpl in Hag. rewrite Hlk in Hag. injection Hag as <-. simpl in Hcase.
    destruct Hcase as
      [(st' & Hst & ->)
      |[(aq & lat & base & tvs & st' & Hst & _ & _)
      |[(rl & base & data & st' & Hst & _ & _)
      |[(aq & rl & base & tvs & data & st' & Hst & _ & _ & _ & _ & _)
      |(pr & pw & sr & sw & st' & Hst & _)]]]];
      try (by destruct (Hforce _ _ Hst) as [? _]).
    exists st'. split; [by destruct (Hforce _ _ Hst) as [_ ?]|exact Hrtc1].
  Qed.

  Lemma block_forced_fence (p : psail) ws img log prom ags c' pr pw sr sw p1 :
    ags !! i = Some (WPAgent p ws prom) → sp_m p ≠ None →
    (∀ l st', sail_step_ni next p l st' →
       l = WeakPromise.LFence pr pw sr sw ∧ st' = p1) →
    rtc (pf_in_block next i) (WPCfgU img log ags) c' →
    at_boundary i c' →
    rtc (pf_in_block next i)
      (WPCfgU img log (<[i := WPAgent p1 (fence_post ws pr pw sr sw) prom]> ags))
      c'.
  Proof.
    intros Hlk Hne Hforce Hrtc Hbd.
    destruct (block_peel (WPCfgU img log ags) c' _ Hlk Hne Hrtc Hbd)
      as (c1 & Hsolo & Hrtc1).
    destruct (pf_solo_inv _ _ Hsolo) as (ag & Hag & Hcase).
    simpl in Hag. rewrite Hlk in Hag. injection Hag as <-. simpl in Hcase.
    destruct Hcase as
      [(st' & Hst & ->)
      |[(aq & lat & base & tvs & st' & Hst & _ & _)
      |[(rl & base & data & st' & Hst & _ & _)
      |[(aq & rl & base & tvs & data & st' & Hst & _ & _ & _ & _ & _)
      |(pr' & pw' & sr' & sw' & st' & Hst & ->)]]]];
      try (by destruct (Hforce _ _ Hst) as [? _]).
    destruct (Hforce _ _ Hst) as [Hl ->]. by injection Hl as -> -> -> ->.
  Qed.

  Lemma block_forced_stuck (p : psail) ws img log prom ags c' :
    ags !! i = Some (WPAgent p ws prom) → sp_m p ≠ None →
    (∀ l st', ¬ sail_step_ni next p l st') →
    rtc (pf_in_block next i) (WPCfgU img log ags) c' →
    at_boundary i c' → False.
  Proof.
    intros Hlk Hne Hforce Hrtc Hbd.
    destruct (block_peel (WPCfgU img log ags) c' _ Hlk Hne Hrtc Hbd)
      as (c1 & Hsolo & _).
    destruct (pf_solo_inv _ _ Hsolo) as (ag & Hag & Hcase).
    simpl in Hag. rewrite Hlk in Hag. injection Hag as <-. simpl in Hcase.
    destruct Hcase as
      [(st' & Hst & _)
      |[(aq & lat & base & tvs & st' & Hst & _ & _)
      |[(rl & base & data & st' & Hst & _ & _)
      |[(aq & rl & base & tvs & data & st' & Hst & _ & _ & _ & _ & _)
      |(pr & pw & sr & sw & st' & Hst & _)]]]];
      exact (Hforce _ _ Hst).
  Qed.

End peel.

(* ====================================================================== *)
(** ** 7. The core: a completed run of a residual monad IS a [wrun]

    [sail_unbracket] is the exact inverse of [WeakSailLTS.sail_bracket].  The
    induction is MUTUAL — [amo_unbracket] is the second statement — because
    the FUSED rmw arm's write half is reached from the read's continuation
    through a silent window, so the statement carried along that window is a
    second one.  (The ⇒ side no longer needs its twin: since stage C8 it
    takes the one-step bare arm at every exclusive read.  The ⇐ side still
    does, because the pf run it consumes may contain a fused [LRmw].) *)

Section unbracket.
  Context (next : bool → M unit) (i : agent).

  Definition sail_unbracket (m : M unit) : Prop :=
    ∀ (s : wmstate) (iq : istream) (prom : gset nat)
      (ags : list (wpagent psail)) (c' : wpcfg psail unit),
      sail_shaped m →
      dev_ok_blk next i c' →
      fused_blk next i c' →
      ags !! i = Some (WPAgent (PSail (Some m) (wm_regs s) (wm_dev s) None iq)
                         (wm_ws s) prom) →
      rtc (pf_in_block next i) (WPCfgU (wimg s) (wm_log s) ags) c' →
      at_boundary i c' →
      ∃ (x : unit) (s' : wmstate),
        wrun (Some i) m s x s' ∧
        c' = WPCfgU (wimg s) (wm_log s')
               (<[i := WPAgent (PSail None (wm_regs s') (wm_dev s') None iq)
                         (wm_ws s') prom]> ags).

  (** …and the second, for the FUSED rmw arm: [m] is the read's
      continuation, which the LTS's own arm says reaches a conditional write
      ([silent_run] to a [wr_node]) — and SINCE STAGE C8 that is the ONLY
      place the amo structure comes from.  Through C7 the hypothesis was
      [amo_tail pa n m], i.e. the shape predicate's claim that the window
      closes at the read's own address and width; (O10) deleted that claim,
      and nothing was lost here, because the LTS arm ALREADY pins the write's
      base ([base = pa_z (ReadReq.pa req)]) and its length.  So the window's
      address agreement is supplied by the RUN, and this statement is indexed
      by the base the fused label carries. *)
  Definition amo_unbracket (base : Z) (m : M unit) : Prop :=
    ∀ (s : wmstate) (m1 m2 : M unit) (rs1 : regstate) (rl : bool)
      (data : list (bv 8)) (iq : istream) (prom : gset nat)
      (ags : list (wpagent psail)) (c' : wpcfg psail unit),
      sail_shaped m →
      dev_ok_blk next i c' →
      fused_blk next i c' →
      silent_run (m, wm_regs s) (m1, rs1) →
      wr_node m1 rl base data m2 →
      ags !! i = Some (WPAgent (PSail (Some m2) rs1 (wm_dev s) None iq)
                         (store_post_run (wm_ws s) rl base (length data)
                            (S (length (wm_log s)))) prom) →
      rtc (pf_in_block next i)
        (WPCfgU (wimg s) (wm_log s ++ [WMsg base data (Some i) WCexcl]) ags)
        c' →
      at_boundary i c' →
      ∃ (x : unit) (s' : wmstate),
        wrun (Some i) m s x s' ∧
        c' = WPCfgU (wimg s) (wm_log s')
               (<[i := WPAgent (PSail None (wm_regs s') (wm_dev s') None iq)
                         (wm_ws s') prom]> ags).

  Local Lemma lk_ins (ags : list (wpagent psail)) a b :
    ags !! i = Some a → (<[i := b]> ags) !! i = Some b.
  Proof. intros H. apply list_lookup_insert. exact (lookup_lt_Some _ _ _ H). Qed.

  (** the silent-node script: one forced silent step, then the IH at [ihv]
      with the (possibly updated) interpreter state [s2]. *)
  Local Ltac ubr_sil p1t ihv s2 IH Hsh Hdev Hfus Hlk Hrtc Hbd :=
    let p1 := fresh "p1" in let Hr1 := fresh "Hrtc1" in
    let xx := fresh "xx" in let ss := fresh "ss" in
    let Hrun := fresh "Hrun" in let Heq := fresh "Heq" in
    destruct (block_forced_silent next i _ _ _ _ _ _ _ (λ st', st' = p1t)
                Hlk ltac:(done) ltac:(intros ? ? HH; exact HH) Hrtc Hbd)
      as (p1 & -> & Hr1);
    destruct (proj1 (IH ihv) s2 _ _ _ _ (Hsh ihv) Hdev Hfus
                ltac:(eapply lk_ins, Hlk) Hr1 Hbd)
      as (xx & ss & Hrun & Heq);
    rewrite list_insert_insert in Heq;
    exists xx, ss; split; [exact Hrun|exact Heq].

  (** the amo silent-node script: peel the first [silent1] step instead. *)
  Local Ltac uamo_sil ihv s2 IH Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd :=
    apply rtc_inv in Hsil;
    destruct Hsil as [Hrf|(cmid & Hs1 & Hsil')];
    [ simplify_eq/=; rewrite /wr_node /= in Hwr; destruct Hwr
    | destruct cmid as [mm rr];
      rewrite /silent1 /= in Hs1; simplify_eq/=;
      let xx := fresh "xx" in let ss := fresh "ss" in
      let Hrun := fresh "Hrun" in let Heq := fresh "Heq" in
      destruct (proj2 (IH ihv) _ s2 _ _ _ _ _ _ _ _ _
                  (Hsh ihv) Hdev Hfus Hsil' Hwr Hlk Hrtc Hbd)
        as (xx & ss & Hrun & Heq);
      exists xx, ss; split; [exact Hrun|exact Heq] ].

  Lemma sail_unbracket_all (m : M unit) :
    sail_unbracket m ∧ ∀ base, amo_unbracket base m.
  Proof.
    induction m as [y|T oc k IH].
    { split.
      - (* Ret: one silent step back to the boundary, and the run stops *)
        intros s iq prom ags c' _ _ _ Hlk Hrtc Hbd.
        destruct (block_forced_silent next i _ _ _ _ _ _ _
                    (λ st', st' = PSail None (wm_regs s) (wm_dev s) None iq)
                    Hlk ltac:(done) ltac:(intros ? ? HH; exact HH) Hrtc Hbd)
          as (p1 & -> & Hrtc1).
        have Hbd1 : at_boundary i
          (WPCfgU (wimg s) (wm_log s)
             (<[i := WPAgent (PSail None (wm_regs s) (wm_dev s) None iq)
                       (wm_ws s) prom]> ags)).
        { eexists. split; [by eapply lk_ins, Hlk|reflexivity]. }
        rewrite (block_done next i _ c' Hbd1 Hrtc1).
        by exists y, s.
      - intros base s m1 m2 rs1 rl data iq prom ags c' _ _ _ Hsil Hwr _ _ _.
        (* the window may be ABANDONED — but then it never reached a
           [wr_node], and [silent_run] out of [Interface.Ret] is stuck *)
        apply rtc_inv in Hsil.
        destruct Hsil as [Hrf|(cmid & Hs1 & _)];
          [ simplify_eq/=; rewrite /wr_node /= in Hwr; destruct Hwr
          | by rewrite /silent1 /= in Hs1 ]. }
    split.
    - (* ================= sail_unbracket ================= *)
      intros s iq prom ags c' Hsh Hdev Hfus Hlk Hrtc Hbd.
      destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                     |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hsh.
      + (* RegRead *)
        ubr_sil (PSail (Some (k (register_lookup rg (wm_regs s)))) (wm_regs s)
                   (wm_dev s) None iq) (register_lookup rg (wm_regs s)) s IH Hsh Hdev Hfus Hlk Hrtc Hbd.
      + (* RegWrite *)
        ubr_sil (PSail (Some (k tt)) (register_set rg rv (wm_regs s)) (wm_dev s) None iq)
                tt (wset_reg s rg rv) IH Hsh Hdev Hfus Hlk Hrtc Hbd.
      + (* MemRead *)
        destruct (dev_addr (Interface.ReadReq.pa req)) eqn:Hd.
        * (* MMIO: the block's own run took this access, so the PARTIAL
             [dev_read] accepted it ([dev_ok_blk]) and the totalized one
             computes the same pair *)
          have Hdo := Hdev _ Hrtc _ Hlk. rewrite /dev_ok_m /= Hd in Hdo.
          destruct Hdo as [[w d'] Hdr].
          have Hf : ∀ l st',
              sail_step_ni next
                (PSail (Some (Interface.Next (Interface.MemRead nn req) k))
                   (wm_regs s) (wm_dev s) None iq) l st' →
              l = WeakPromise.LSilent ∧
              st' = PSail (Some (k (inl (w, None)))) (wm_regs s) d' None iq.
          { intros l st' HH.
            rewrite /sail_step_ni /sail_mstep /= Hd
                    (dev_read_t_Some _ _ _ _ _ Hdr) /= in HH.
            exact HH. }
          destruct (block_forced_silent next i _ _ _ _ _ _ _
                      (λ st', st' = PSail (Some (k (inl (w, None)))) (wm_regs s)
                                d' None iq)
                      Hlk ltac:(done) Hf Hrtc Hbd)
            as (p1 & -> & Hrtc1).
          rewrite /wrun Hd Hdr.
          destruct (proj1 (IH (inl (w, None))) (wset_dev s d') _ _ _ _
                      (proj2 Hsh _) Hdev Hfus
                      ltac:(eapply lk_ins, Hlk) Hrtc1 Hbd)
            as (xx & ss & Hrun & Heq).
          rewrite list_insert_insert in Heq.
          exists xx, ss. split; [exact Hrun|exact Heq].
        * (* RAM read: a plain load (any access kind), or the fused RMW *)
          destruct Hsh as (Hcoh & Hsh).
          destruct (block_peel next i (WPCfgU (wimg s) (wm_log s) ags) c' _
                      Hlk ltac:(done) Hrtc Hbd) as (c1 & Hsolo & Hrtc1).
          destruct (pf_solo_inv next i _ _ Hsolo) as (ag & Hag & Hcase).
          simpl in Hag. rewrite Hlk in Hag. injection Hag as <-.
          simpl in Hcase.
          destruct Hcase as
            [(st' & Hst & _)
            |[(aq & lat & base & tvs & st' & Hst & Hrok & ->)
            |[(rl & base & data & st' & Hst & _ & _)
            |[(aq & rl & base & tvs & data & st' & Hst & Hne & Hlen & Hrok & Hex & ->)
            |(pr & pw & sr & sw & st' & Hst & _)]]]];
            rewrite /sail_step_ni /sail_mstep /= Hd in Hst;
            try (by destruct Hst as (_ & [])).
          { (* a load label.  ONE arm since stage C8 — a bare exclusive read
               takes the same one — so what [fused_blk] excludes is not a
               second disjunct but the ACCESS KIND: an [ak_latest] read that
               steps as a plain load appends nothing, which [pf_solo_f]
               forbids. *)
            destruct Hst as (_ & Hst). destruct lat; [done|].
            destruct Hst as (-> & -> & Hlents & w & Hw & ->).
            have Hlat : ak_latest (classify (Interface.ReadReq.access_kind req))
                        = false.
            { destruct (ak_latest (classify (Interface.ReadReq.access_kind req)))
                eqn:Hl; [|done].
              exfalso.
              exact (proj1 (proj2 (Hfus _ _ Hsolo Hrtc1))
                       (ex_intro _ _ (conj Hlk (conj eq_refl (conj Hd Hl))))
                       eq_refl). }
            destruct (proj1 (IH (inl (w, None)))
                        (wset_ws s (load_post_run (wm_ws s)
                           (ak_sync (classify (Interface.ReadReq.access_kind req)))
                           (pa_z (Interface.ReadReq.pa req)) tvs.*1))
                        _ _ _ _ (Hsh _) Hdev Hfus
                        ltac:(eapply lk_ins, Hlk) Hrtc1 Hbd)
              as (xx & ss & Hrun & Heq).
            rewrite list_insert_insert in Heq.
            exists xx, ss. split; [|exact Heq].
            rewrite /wrun Hd. exists w, tvs.*1. split.
            { eapply read_ok_wread_ok; [exact Hcoh|exact Hlents|exact Hw|].
              by rewrite Hlat. }
            rewrite /wread_post Hcoh. exact Hrun. }
          { (* the fused RMW *)
            destruct Hst as (_ & Hst).
            destruct Hst as (Hlat & -> & -> & Hlents & Hlend & w & m1 & m2 & rs1
                             & Hw & Hsil & Hwr & ->).
            destruct (proj2 (IH (inl (w, None)))
                        (pa_z (Interface.ReadReq.pa req))
                        (wset_ws s (load_post_run (wm_ws s)
                           (ak_sync (classify (Interface.ReadReq.access_kind req)))
                           (pa_z (Interface.ReadReq.pa req)) tvs.*1))
                        m1 m2 rs1 _ _ _ _ _ _
                        (Hsh w) Hdev Hfus Hsil Hwr
                        ltac:(eapply lk_ins, Hlk) Hrtc1 Hbd)
              as (xx & ss & Hrun & Heq).
            rewrite list_insert_insert in Heq.
            exists xx, ss. split; [|exact Heq].
            rewrite /wrun Hd. exists w, tvs.*1. split.
            { eapply read_ok_wread_ok; [exact Hcoh|exact Hlents|exact Hw|].
              by rewrite Hlat. }
            rewrite /wread_post Hcoh. exact Hrun. }
      + (* MemWrite *)
        destruct Hsh as (Hn & Hsh).
        destruct (dev_addr (Interface.WriteReq.pa req)) eqn:Hd.
        * have Hdo := Hdev _ Hrtc _ Hlk. rewrite /dev_ok_m /= Hd in Hdo.
          destruct Hdo as [d' Hdw].
          rewrite /wrun Hd Hdw.
          destruct (block_forced_silent next i _ _ _ _ _ _ _
                      (λ st', st' = PSail (Some (k (inl None))) (wm_regs s)
                                d' None iq)
                      Hlk ltac:(done)
                      ltac:(intros ? ? HH;
                            rewrite /sail_step_ni /sail_mstep /= Hd
                                    (dev_write_t_Some _ _ _ _ _ Hdw) in HH;
                            exact HH) Hrtc Hbd)
            as (p1 & -> & Hrtc1).
          destruct (proj1 (IH (inl None)) (wset_dev s d') _ _ _ _
                      Hsh Hdev Hfus
                      ltac:(eapply lk_ins, Hlk) Hrtc1 Hbd)
            as (xx & ss & Hrun & Heq).
          rewrite list_insert_insert in Heq.
          exists xx, ss. split; [exact Hrun|exact Heq].
        * destruct (block_peel next i (WPCfgU (wimg s) (wm_log s) ags) c' _
                      Hlk ltac:(done) Hrtc Hbd) as (c1 & Hsolo & Hrtc1).
          (* THE STANDALONE CONDITIONAL WRITE (delta (e'')) is what
             [fused_blk]'s [at_con_write] conjunct excludes: [wrun] would
             stamp the message [WCexcl], the pf step stamps [lbl_class]. *)
          have Hnlat : ak_latest (classify (Interface.WriteReq.access_kind req))
                       = false.
          { destruct (ak_latest (classify (Interface.WriteReq.access_kind req)))
              eqn:Hlat; [|done].
            exfalso. apply (proj2 (proj2 (Hfus _ _ Hsolo Hrtc1))).
            eexists. split_and!;
              [exact Hlk|reflexivity|by simpl; rewrite Hd Hlat]. }
          destruct (pf_solo_inv next i _ _ Hsolo) as (ag & Hag & Hcase).
          simpl in Hag. rewrite Hlk in Hag. injection Hag as <-.
          cbn [pc_img pc_log pc_ags] in Hcase.
          destruct Hcase as
            [(st' & Hst & _)
            |[(aq & lat & base & tvs & st' & Hst & _ & _)
            |[(rl & base & data & st' & Hst & Hne & ->)
            |[(aq & rl & base & tvs & data & st' & Hst & _ & _ & _ & _ & _)
            |(pr & pw & sr & sw & st' & Hst & _)]]]];
            rewrite /sail_step_ni /sail_mstep /= Hd in Hst;
            try (by destruct Hst as (Hx & _)).
          destruct Hst as (Hl & _ & ->). injection Hl as -> -> ->.
          have Hcls : lbl_class (WeakPromise.LStore
                        (ak_sync (classify (Interface.WriteReq.access_kind req)))
                        (pa_z (Interface.WriteReq.pa req))
                        (wbytes nn (Interface.WriteReq.value req))) (wm_ws s)
                      = wm_class_of
                          (classify (Interface.WriteReq.access_kind req)) (wm_ws s).
          { symmetry. by rewrite /wm_class_of /lbl_class Hnlat. }
          rewrite Hcls wbytes_length in Hrtc1.
          destruct (proj1 (IH (inl None))
                      (wwrite_post (Some i) s
                         (classify (Interface.WriteReq.access_kind req))
                         (Interface.WriteReq.pa req) nn
                         (Interface.WriteReq.value req))
                      _ _ _ _ Hsh Hdev Hfus
                      ltac:(eapply lk_ins, Hlk) Hrtc1 Hbd)
            as (xx & ss & Hrun & Heq).
          rewrite list_insert_insert in Heq.
          exists xx, ss. split; [|exact Heq].
          rewrite /wrun Hd. exact Hrun.
      + (* InstrAnnounce *)
        ubr_sil (PSail (Some (k tt)) (wm_regs s) (wm_dev s) None iq) tt s IH Hsh Hdev Hfus Hlk Hrtc Hbd.
      + (* BranchAnnounce *)
        ubr_sil (PSail (Some (k tt)) (wm_regs s) (wm_dev s) None iq) tt s IH Hsh Hdev Hfus Hlk Hrtc Hbd.
      + (* Barrier: the label table [barrier_lbl] mirrors [barrier_post] *)
        rewrite /wrun.
        have Hrtc1 : rtc (pf_in_block next i)
          (WPCfgU (wimg s) (wm_log s)
             (<[i := WPAgent (PSail (Some (k tt)) (wm_regs s) (wm_dev s) None iq)
                       (barrier_post (wm_ws s) bk) prom]> ags)) c'.
        { destruct bk.
          1-9: (exact (block_forced_fence next i _ _ _ _ _ _ _ _ _ _ _ _
                         Hlk ltac:(done) ltac:(intros ? ? HH; exact HH)
                         Hrtc Hbd)).
          - (* fence.tso: the first fence, then the parked second *)
            have Hr1 := block_forced_fence next i _ _ _ _ _ _ _
                          true false true false
                          (PSail (Some (k tt)) (wm_regs s) (wm_dev s)
                             (Some (true, true, false, true)) iq)
                          Hlk ltac:(done) ltac:(intros ? ? HH; exact HH)
                          Hrtc Hbd.
            have Hr2 := block_forced_fence next i
                          (PSail (Some (k tt)) (wm_regs s) (wm_dev s)
                             (Some (true, true, false, true)) iq)
                          _ _ _ _ _ _
                          true true false true
                          (PSail (Some (k tt)) (wm_regs s) (wm_dev s) None iq)
                          ltac:(eapply lk_ins, Hlk) ltac:(done)
                          ltac:(intros ? ? HH; exact HH) Hr1 Hbd.
            rewrite list_insert_insert in Hr2. exact Hr2.
          - (* fence.i: no event *)
            destruct (block_forced_silent next i _ _ _ _ _ _ _
                        (λ st', st' = PSail (Some (k tt)) (wm_regs s) (wm_dev s) None iq)
                        Hlk ltac:(done) ltac:(intros ? ? HH; exact HH) Hrtc Hbd)
              as (p1 & -> & Hr). exact Hr. }
        destruct (proj1 (IH tt) (wset_ws s (barrier_post (wm_ws s) bk))
                    _ _ _ _ (Hsh tt) Hdev Hfus
                    ltac:(eapply lk_ins, Hlk) Hrtc1 Hbd)
          as (xx & ss & Hrun & Heq).
        rewrite list_insert_insert in Heq.
        exists xx, ss. split; [exact Hrun|exact Heq].
      + (* CacheOp *) ubr_sil (PSail (Some (k tt)) (wm_regs s) (wm_dev s) None iq) tt s IH Hsh Hdev Hfus Hlk Hrtc Hbd.
      + (* TlbOp *) ubr_sil (PSail (Some (k tt)) (wm_regs s) (wm_dev s) None iq) tt s IH Hsh Hdev Hfus Hlk Hrtc Hbd.
      + (* TakeException *)
        ubr_sil (PSail (Some (k tt)) (wm_regs s) (wm_dev s) None iq) tt s IH Hsh Hdev Hfus Hlk Hrtc Hbd.
      + (* ReturnException *)
        ubr_sil (PSail (Some (k tt)) (wm_regs s) (wm_dev s) None iq) tt s IH Hsh Hdev Hfus Hlk Hrtc Hbd.
      + (* TranslationStart *)
        ubr_sil (PSail (Some (k tt)) (wm_regs s) (wm_dev s) None iq) tt s IH Hsh Hdev Hfus Hlk Hrtc Hbd.
      + (* TranslationEnd *)
        ubr_sil (PSail (Some (k tt)) (wm_regs s) (wm_dev s) None iq) tt s IH Hsh Hdev Hfus Hlk Hrtc Hbd.
      + (* ExtraOutcome: stuck *)
        exfalso. eapply (block_forced_stuck next i _ _ _ _ _ _ _ Hlk);
          [done|intros ? ? HH; exact HH|exact Hrtc|exact Hbd].
      + (* GenericFail: stuck *)
        exfalso. eapply (block_forced_stuck next i _ _ _ _ _ _ _ Hlk);
          [done|intros ? ? HH; exact HH|exact Hrtc|exact Hbd].
      + (* CycleCount *) ubr_sil (PSail (Some (k tt)) (wm_regs s) (wm_dev s) None iq) tt s IH Hsh Hdev Hfus Hlk Hrtc Hbd.
      + (* GetCycleCount *)
        ubr_sil (PSail (Some (k 0%Z)) (wm_regs s) (wm_dev s) None iq) 0%Z s IH Hsh Hdev Hfus Hlk Hrtc Hbd.
      + (* Choose *)
        destruct (block_forced_silent next i _ _ _ _ _ _ _
                    (λ st', ∃ ch, st' = PSail (Some (k ch)) (wm_regs s) (wm_dev s) None iq)
                    Hlk ltac:(done) ltac:(intros ? ? HH; exact HH) Hrtc Hbd)
          as (p1 & (ch & ->) & Hrtc1).
        destruct (proj1 (IH ch) s _ _ _ _ (Hsh ch) Hdev Hfus
                    ltac:(eapply lk_ins, Hlk) Hrtc1 Hbd)
          as (xx & ss & Hrun & Heq).
        rewrite list_insert_insert in Heq.
        exists xx, ss. split; [by exists ch|exact Heq].
      + (* Discard: stuck *)
        exfalso. eapply (block_forced_stuck next i _ _ _ _ _ _ _ Hlk);
          [done|intros ? ? HH; exact HH|exact Hrtc|exact Hbd].
      + (* Message *) ubr_sil (PSail (Some (k tt)) (wm_regs s) (wm_dev s) None iq) tt s IH Hsh Hdev Hfus Hlk Hrtc Hbd.
    - (* ================= amo_unbracket ================= *)
      intros base s m1 m2 rs1 rl data iq prom ags c'
             Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd.
      destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                     |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hsh.
      + (* RegRead *)
        uamo_sil (register_lookup rg (wm_regs s)) s
                 IH Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd.
      + (* RegWrite *)
        uamo_sil tt (wset_reg s rg rv) IH Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd.
      + (* MemRead: no [silent1] arm, so the window's run stops here *)
        (* no [silent1] arm here, and no [wr_node] either: the window's
           run cannot pass through a memory node or a barrier *)
        apply rtc_inv in Hsil;
        destruct Hsil as [Hrf|(cmid & Hs1 & _)];
          [ simplify_eq/=; rewrite /wr_node /= in Hwr; destruct Hwr
          | by rewrite /silent1 /= in Hs1 ].
      + (* MemWrite: THE write half — the silent window ends here *)
        apply rtc_inv in Hsil.
        destruct Hsil as [Hrf|(cmid & Hs1 & _)];
          [|by rewrite /silent1 /= in Hs1].
        injection Hrf as Hm1 Hrs1. subst m1 rs1.
        destruct Hsh as (_ & Hsh).
        have Hm2 := Hwr. rewrite /wr_node /= in Hm2.
        destruct Hm2 as (_ & _ & _ & _ & _ & _ & ->).
        destruct (proj1 (IH (inl None))
                    (WMState (wm_regs s) (wm_img s)
                       (wm_log s ++ [WMsg base data (Some i) WCexcl])
                       (store_post_run (wm_ws s) rl base (length data)
                          (S (length (wm_log s)))) (wm_dev s))
                    _ _ _ _ Hsh Hdev Hfus Hlk Hrtc Hbd)
          as (xx & ss & Hrun & Heq).
        exists xx, ss. split; [|exact Heq].
        eapply (wr_node_wrun (Some i) _ rl _ data _ s); [exact Hwr|exact Hrun].
      + (* InstrAnnounce *) uamo_sil tt s IH Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd.
      + (* BranchAnnounce *) uamo_sil tt s IH Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd.
      + (* Barrier: likewise *)
        (* no [silent1] arm here, and no [wr_node] either: the window's
           run cannot pass through a memory node or a barrier *)
        apply rtc_inv in Hsil;
        destruct Hsil as [Hrf|(cmid & Hs1 & _)];
          [ simplify_eq/=; rewrite /wr_node /= in Hwr; destruct Hwr
          | by rewrite /silent1 /= in Hs1 ].
      + (* CacheOp *) uamo_sil tt s IH Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd.
      + (* TlbOp *) uamo_sil tt s IH Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd.
      + (* TakeException *) uamo_sil tt s IH Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd.
      + (* ReturnException *) uamo_sil tt s IH Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd.
      + (* TranslationStart *) uamo_sil tt s IH Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd.
      + (* TranslationEnd *) uamo_sil tt s IH Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd.
      + (* ExtraOutcome *)
        apply rtc_inv in Hsil.
        destruct Hsil as [Hrf|(cmid & Hs1 & _)];
          [ simplify_eq/=; rewrite /wr_node /= in Hwr; destruct Hwr
          | by rewrite /silent1 /= in Hs1 ].
      + (* GenericFail *)
        apply rtc_inv in Hsil.
        destruct Hsil as [Hrf|(cmid & Hs1 & _)];
          [ simplify_eq/=; rewrite /wr_node /= in Hwr; destruct Hwr
          | by rewrite /silent1 /= in Hs1 ].
      + (* CycleCount *) uamo_sil tt s IH Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd.
      + (* GetCycleCount *) uamo_sil 0%Z s IH Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd.
      + (* Choose *)
        apply rtc_inv in Hsil.
        destruct Hsil as [Hrf|(cmid & Hs1 & Hsil')];
          [by (simplify_eq/=; rewrite /wr_node /= in Hwr; destruct Hwr)|].
        destruct cmid as [mm rr].
        rewrite /silent1 /= in Hs1. destruct Hs1 as (ch & Hch). simplify_eq/=.
        destruct (proj2 (IH ch) base s _ _ _ _ _ _ _ _ _
                    (Hsh ch) Hdev Hfus Hsil' Hwr Hlk Hrtc Hbd)
          as (xx & ss & Hrun & Heq).
        exists xx, ss. split; [by exists ch|exact Heq].
      + (* Discard *)
        apply rtc_inv in Hsil.
        destruct Hsil as [Hrf|(cmid & Hs1 & _)];
          [ simplify_eq/=; rewrite /wr_node /= in Hwr; destruct Hwr
          | by rewrite /silent1 /= in Hs1 ].
      + (* Message *) uamo_sil tt s IH Hsh Hdev Hfus Hsil Hwr Hlk Hrtc Hbd.
  Qed.

  (** THE ⇐ BRACKET at the residual monad — the exact inverse of
      [WeakSailLTS.wrun_sail_bracket]. *)
  Theorem sail_run_wrun (m : M unit) s iq prom ags c' :
    sail_shaped m →
    dev_ok_blk next i c' →
    fused_blk next i c' →
    ags !! i = Some (WPAgent (PSail (Some m) (wm_regs s) (wm_dev s) None iq)
                       (wm_ws s) prom) →
    rtc (pf_in_block next i) (WPCfgU (wimg s) (wm_log s) ags) c' →
    at_boundary i c' →
    ∃ (x : unit) (s' : wmstate),
      wrun (Some i) m s x s' ∧
      c' = WPCfgU (wimg s) (wm_log s')
             (<[i := WPAgent (PSail None (wm_regs s') (wm_dev s') None iq)
                       (wm_ws s') prom]> ags).
  Proof. apply (proj1 (sail_unbracket_all m)). Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 8. The block statement: boundary to boundary *)

  Theorem sail_block_wrun (s : wmstate) (iq : istream)
      (prom : gset nat) (ags : list (wpagent psail)) (c' : wpcfg psail unit) :
    (∀ b, sail_shaped (next b)) →
    dev_ok_blk next i c' →
    fused_blk next i c' →
    ags !! i = Some (WPAgent (PSail None (wm_regs s) (wm_dev s) None iq)
                       (wm_ws s) prom) →
    sail_block next i (WPCfgU (wimg s) (wm_log s) ags) c' →
    ∃ (tick : bool) (x : unit) (s' : wmstate),
      wrun (Some i) (next tick) s x s' ∧
      c' = WPCfgU (wimg s) (wm_log s')
             (<[i := WPAgent (PSail None (wm_regs s') (wm_dev s') None iq)
                       (wm_ws s') prom]> ags).
  Proof.
    intros Hsh Hdev Hfus Hlk (_ & Hbd & c0 & Hsolo & Hrtc).
    destruct (pf_solo_inv next i _ _ Hsolo) as (ag & Hag & Hcase).
    simpl in Hag. rewrite Hlk in Hag. injection Hag as <-. simpl in Hcase.
    destruct Hcase as
      [(st' & Hst & ->)
      |[(aq & lat & base & tvs & st' & Hst & _ & _)
      |[(rl & base & data & st' & Hst & _ & _)
      |[(aq & rl & base & tvs & data & st' & Hst & _ & _ & _ & _ & _)
      |(pr & pw & sr & sw & st' & Hst & _)]]]];
      rewrite /sail_step_ni /= in Hst; try (by destruct Hst as [Hx _]).
    destruct Hst as (_ & tick & ->).
    destruct (sail_run_wrun (next tick) s iq prom _ c'
                (Hsh tick) Hdev Hfus ltac:(eapply lk_ins, Hlk) Hrtc Hbd)
      as (xx & ss & Hrun & Heq).
    rewrite list_insert_insert in Heq.
    by exists tick, xx, ss.
  Qed.

End unbracket.

(* ====================================================================== *)
(** ** 9. The hart-arm equivalence

    One [WeakLang.wprim_step] hart arm ⇔ one completed irq-free block of the
    hart's agent, framed by [whart_view] / [whart_write].

    THE DEVICE FABRIC IS NOW SYMMETRIC across the two directions: both run
    the hart's agent from [wgdev g] and land it at [wgdev g'] (the machine
    updates its fabric to the hart's, [WeakLang.whart_write_dev]).  Only the
    ⇐ direction carries a device side condition, and it is not about a
    stream: [dev_ok_blk] says the block's OWN device accesses were ones the
    partial [dev_read]/[dev_write] accepted — which the ⇒ direction gets for
    free, because a [wrun] cannot take any other.

    The ⇒ direction lands in [wp_pf_run (pstep_unit (sail_step riscv_step))] (what
    [sail_instr_bracket] proves) and the ⇐ direction starts from the finer
    [sail_block] (solo, irq-free, faithfully classed); [pf_solo_run] is the
    inclusion that makes them a sandwich. *)

(** ⇐ — what L3 consumes. *)
Theorem wprim_hart_block_bwd (cpu : CPU) (gen : nat) (g : wgstate)
    (iq : istream) (prom : gset nat)
    (ags : list (wpagent psail)) (c' : wpcfg psail unit) :
  (∀ b, sail_shaped (riscv_step b)) →
  dev_ok_blk riscv_step (fin_to_nat cpu) c' →
  fused_blk riscv_step (fin_to_nat cpu) c' →
  wthread_live g gen →
  ags !! (fin_to_nat cpu)
    = Some (WPAgent (PSail None (wgregs g cpu) (wgdev g) None iq)
              (wgws g cpu) prom) →
  sail_block riscv_step (fin_to_nat cpu)
    (WPCfgU (img_z (wgimg g)) (wglog g) ags) c' →
  ∃ g' : wgstate,
    wprim_step (LoopE gen cpu) g [] (LoopE gen cpu) g' [] ∧
    c' = WPCfgU (img_z (wgimg g)) (wglog g')
           (<[fin_to_nat cpu :=
                WPAgent (PSail None (wgregs g' cpu) (wgdev g') None iq)
                  (wgws g' cpu) prom]> ags).
Proof.
  intros Hsh Hdev Hfus Hlive Hlk Hblk.
  destruct (sail_block_wrun riscv_step (fin_to_nat cpu) (whart_view g cpu)
              iq prom ags c' Hsh Hdev Hfus Hlk Hblk)
    as (tick & xx & ss & Hrun & Heq).
  exists (whart_write g cpu ss). split.
  - left. exists gen, cpu. split_and!; try reflexivity.
    left. split; [exact Hlive|]. by exists tick, xx, ss.
  - rewrite whart_write_log whart_write_regs_eq whart_write_ws_eq
            whart_write_dev. exact Heq.
Qed.

(** ⇒ — [WeakSailLTS.sail_instr_bracket] at the [wgstate] seam. *)
Theorem wprim_hart_block_fwd (cpu : CPU) (gen : nat) (g g' : wgstate) :
  (∀ b, sail_shaped (riscv_step b)) →
  wrun_plainw (wglog g) (wglog g') →
  wthread_live g gen →
  wprim_step (LoopE gen cpu) g [] (LoopE gen cpu) g' [] →
  ∀ (iq : istream) (prom : gset nat) (ags : list (wpagent psail)),
    ags !! (fin_to_nat cpu)
      = Some (WPAgent (PSail None (wgregs g cpu) (wgdev g) None iq)
                (wgws g cpu) prom) →
    rtc (wp_pf_run (pstep_unit (sail_step riscv_step)) lbl_class)
      (WPCfgU (img_z (wgimg g)) (wglog g) ags)
      (WPCfgU (img_z (wgimg g)) (wglog g')
         (<[fin_to_nat cpu :=
              WPAgent (PSail None (wgregs g' cpu) (wgdev g') None iq)
                (wgws g' cpu) prom]> ags)).
Proof.
  intros Hsh Hpl Hlive Hstep.
  apply wprim_step_loop_inv in Hstep as (_ & _ & _ & [(_ & tick & u & ss & Hrun & ->)|(Hnl & _)]);
    [|done].
  rewrite whart_write_log in Hpl. rewrite -(whart_view_log g cpu) in Hpl.
  pose proof (sail_instr_bracket (fin_to_nat cpu) lbl_class
                (λ ak ws base data Hlat, lbl_class_store ak ws base data Hlat)
                tick (whart_view g cpu) u ss (Hsh tick) Hrun Hpl) as Hch.
  intros iq prom ags Hlk.
  rewrite whart_write_log whart_write_regs_eq whart_write_ws_eq
          whart_write_dev.
  exact (Hch iq prom ags Hlk).
Qed.

(** THE EQUIVALENCE, packaged. *)
Theorem wprim_hart_block (cpu : CPU) (gen : nat) (g : wgstate)
    (iq : istream) (prom : gset nat) (ags : list (wpagent psail)) :
  (∀ b, sail_shaped (riscv_step b)) →
  wthread_live g gen →
  ags !! (fin_to_nat cpu)
    = Some (WPAgent (PSail None (wgregs g cpu) (wgdev g) None iq)
              (wgws g cpu) prom) →
  (* ⇐ : a completed irq-free block whose device accesses all decoded IS one
     hart step *)
  (∀ c', dev_ok_blk riscv_step (fin_to_nat cpu) c' →
     fused_blk riscv_step (fin_to_nat cpu) c' →
     sail_block riscv_step (fin_to_nat cpu)
       (WPCfgU (img_z (wgimg g)) (wglog g) ags) c' →
     ∃ g' : wgstate,
       wprim_step (LoopE gen cpu) g [] (LoopE gen cpu) g' [] ∧
       c' = WPCfgU (img_z (wgimg g)) (wglog g')
              (<[fin_to_nat cpu :=
                   WPAgent (PSail None (wgregs g' cpu) (wgdev g') None iq)
                     (wgws g' cpu) prom]> ags))
  ∧
  (* ⇒ : one hart step IS a run of the same shape, at the same fabric *)
  (∀ g', wprim_step (LoopE gen cpu) g [] (LoopE gen cpu) g' [] →
     wrun_plainw (wglog g) (wglog g') →
     ∀ (iq' : istream) (prom' : gset nat) (ags' : list (wpagent psail)),
       ags' !! (fin_to_nat cpu)
         = Some (WPAgent (PSail None (wgregs g cpu) (wgdev g) None iq')
                   (wgws g cpu) prom') →
       rtc (wp_pf_run (pstep_unit (sail_step riscv_step)) lbl_class)
         (WPCfgU (img_z (wgimg g)) (wglog g) ags')
         (WPCfgU (img_z (wgimg g)) (wglog g')
            (<[fin_to_nat cpu :=
                 WPAgent (PSail None (wgregs g' cpu) (wgdev g') None iq')
                   (wgws g' cpu) prom']> ags'))).
Proof.
  intros Hsh Hlive Hlk. split.
  - intros c' Hdev Hfus Hblk. by eapply wprim_hart_block_bwd.
  - intros g' Hstep Hpl.
    exact (wprim_hart_block_fwd cpu gen g g' Hsh Hpl Hlive Hstep).
Qed.
