(** * WeakComposeLang.v — L3: THE pf-RUN ⇒ WeakLang REGROUPING and the
      φ-CONSUMPTION COROLLARY
      (lift stage L3 of [claude-notes/projects/weak-memory-lift.md])

    WHAT THIS FILE IS.  [WeakCompose.xv6_weak_robust] is the M6 headline
    theorem over the wp machine ([wpcfg pxv6]); [WeakAdequacy] exports φ
    ([WeakGhost.no_violation]) at every state of the [WeakLang] machine
    ([wgstate], [wprim_step]).  Seam (1) of [WeakCompose] §6 is the missing
    bridge between the two, and its ONE consumer is the second conjunct of
    [WeakCompose.m6_side_conditions] — [WeakRobust.pf_violation_free_hart],
    the place φ/Iris is still load-bearing.  This file builds the bridge in the ⇐
    direction the consumption needs, and derives that conjunct.

    ------------------------------------------------------------------------
    §A  WHAT IS DELIVERED (all machine-checked; no [Axiom], no [Admitted]).

    (1) THE CORRESPONDENCE, as a FUNCTION rather than a relation (§1).
        [wl_cfg g u] is the [wpcfg pxv6] a [WeakLang] state [g] denotes, given
        the per-agent data a [wgstate] does NOT carry: the two ORACLE STREAMS
        of [WeakSailLTS.psail] ([wa_dstr], [wa_iq]) and the disk agent's own
        fabric state and [wstate] ([wa_dd], [wa_dws]).  Harts sit at
        [0 .. NCPU-1] and the disk at [NCPU = WeakLang.n_disk] — exactly
        [WeakCompose.xv6_ps]'s layout, which is what keeps every [wm_tid]
        stable across the seam.  The two facts the transport reads off it are
        [wl_cfg_log] ([pc_log (wl_cfg g u) = wglog g]) and [wl_cfg_obs_flr]
        ([obs_flr (wl_cfg g u) (fin_to_nat cpu) a = coh (wgws g cpu) a]).

    (2) THE SEGMENTS (§3) and THE REGROUPING THEOREM ([xv6_blocks_lang], §7).
        [xv6_seg g u g' u'] is one of:
          - [seg_hart]: an irq-free INSTRUCTION BLOCK of one hart —
            [WeakSailLTS2.sail_block], i.e. boundary to boundary, solo,
            faithfully classed ([cls_canon]/[rmw_tight] live inside
            [pf_solo]) — mapped to [wprim_step]'s hart arm by
            [WeakSailLTS2.sail_block_wrun];
          - [seg_plic]: ONE interrupt delivery ([WeakSailLTS.irq_deliver]),
            mapped to [RiscvLang.plic_step]'s [PlicStepWire];
          - [seg_disk]: ONE disk burst plus its emit group — L0(d) buffers a
            [WeakLang.wdisk_step]'s write set and emits it one message at a
            time, so one [WeakLang] disk arm is [1 + |w|] pf steps; [emit_run]
            inverts that, appending EXACTLY [WeakLang.wmsgs_of_map w].
        [xv6_blocks] is their [rtc], and [xv6_blocks_lang] says such a run is
        BOTH an [rtc (wp_pf_run (pstep_xv6 riscv_step))] between the
        corresponding configurations AND an [rtc erased_step] of
        [WeakLang.weak_riscv_lang] over the standard pool
        ([wpool gen_id = WeakAdequacy.wcpu_pool (enum CPU)]).
        NO UART SEGMENT and NO POWER SEGMENT, deliberately: the wp machine has
        no uart agent at all (so the produced [WeakLang] runs are uart-free,
        which is the free direction — we only need EXISTENCE of a run), and
        the power arm is vacuous at a pinned generation ([wthread_live] is an
        invariant of every segment).

    (3) THE φ TRANSPORT ([xv6_blocks_no_hart_violation], §8).  φ at the
        reached [WeakLang] state refutes a HART-AUTHORED, HART-OBSERVED
        violation at the corresponding pf configuration — which, since the
        Layer-1 fix of §B, is the only kind [WeakRobust.violation_hart] has.  The transport is SYNTACTIC, and that is L0(c)'s
        payoff: [WeakRobustMain.pub_of] IS [WeakMem.wpublished] at the
        configuration's log, the very predicate [no_violation] is stated with,
        and [WeakRobust.obs_flr] IS the agent's [coh].  Nothing is renamed.

    (4) THE φ-CONSUMPTION COROLLARY ([xv6_pf_violation_free], §10) and THE
        UPDATED COMPOSITION ([xv6_weak_robust_lifted] /
        [xv6_weak_robust_adequate], §11): [WeakCompose.xv6_weak_robust] with
        [pf_violation_free_hart] REPLACED by its derivation from the adequacy
        export.  [xv6_weak_robust_adequate] takes [WeakAdequacy]'s own WP
        premise package and runs [weak_system_adequacy_phi] on the spot, so
        the composition's only Iris-side obligation is the thread pool's WPs.

    ------------------------------------------------------------------------
    §B  THE RESIDUE, STATED AS A PREMISE — and the FINDING that was the
    second one until Layer 1 absorbed it.

    (A) is a named definition in §10, consumed in exactly one place and NOT
    dressed up as a theorem; (B) is now history, kept as a record of the bug
    and of where its fix lives.

    (A) [xv6_block_cover] — BLOCK-ATOMICITY (the interleaving / mover residue,
        and the honest one).  A [wp_pf_run] interleaves the harts at EVENT
        granularity; [WeakLang] executes whole instructions atomically.  The
        regrouping therefore consumes runs that ALREADY are a concatenation of
        segments, and the premise says a violating pf-reachable configuration
        has a block-atomic witness of the SAME violation.
        WHY IT IS BELIEVABLE, and how it is meant to be discharged: for rv64d
        a hart block contains AT MOST ONE log-touching event (ifetch and page
        walks are never emitted — [WeakSailLTS] delta (d) / [WeakInterp] §3's
        finding (1) — so an instruction has at most its one data access, plus
        the walker A/D CAS that [WeakRobustBlocks.blk_shape] admits).  Every
        other step of a block is silent: it neither reads nor appends to the
        log, and [WeakPromiseBridge.wp_pf_step]'s [PFSilent]/[PFFence] arms
        touch only the stepping agent.  Such steps COMMUTE with any other
        agent's step, so an arbitrary pf run can be sorted into block-atomic
        form without changing the log.  That commutation lemma plus the
        "≤ one memory event per rv64d block" shape premise is the missing
        theorem; it is a self-contained piece of work at the
        [WeakPromiseBridge] layer and is NOT attempted here.
        WHY [WeakRobustBlocks]'s COMPLETION MACHINERY IS *NOT* USED FOR IT.
        [complete_block] needs [blk_fin], whose [bf_prog] conjunct ("off a
        boundary the program always has a step") is FALSE for [sail_step] as
        it stands: a device read with an EXHAUSTED oracle stream
        ([sp_dev = []]) is stuck, and so is a monad node whose shape premise
        fails.  Completing a Sail block therefore needs additional honest
        premises (infinite oracle streams, and a nat measure on the residual
        instruction monad — the free monad has no structural one, since a
        continuation is indexed by an infinite value type).  That is recorded
        here as a finding: L1's completion lemmas apply to the abstract LTS,
        but the [sail_step] instantiation of [blk_fin] is NOT free.  (The
        other L1 instantiation obligation, [WeakRobustBlocks.lts_enabled],
        is value-input-enabledness — [WeakRobustSim.ts_oblivious]'s big
        sibling; it looks provable for [sail_step] modulo a surjectivity
        lemma for [WeakInterpProj.wbytes], but nothing on the route taken
        here consumes it without [blk_fin], so it is not proved.)
        THE AUTHOR CORNER, correspondingly: it does not arise in this route.
        [xv6_block_cover]'s conclusion is stated at a BLOCK-ATOMIC run, and
        every such run ends with EVERY hart at an instruction boundary (each
        segment leaves its own agent at [sp_m = None] and moves no other), so
        no agent — the violating message's author included — ever has to be
        completed, and [cone_boundary_sub]'s sub-block reading is not needed
        either.  L1's [complete_cut]/[complete_agents]/[cone_boundary_thm]
        remain the route for a mid-block cut and are what a proof of
        [xv6_block_cover] going through the EXHIBIT (rather than through a
        commutation argument) would use.

    (B) THE AGENT QUANTIFIER — FOUND HERE, FIXED IN LAYER 1, GONE FROM THE
        PREMISE LIST (2026-08-12).  It was a premise of this file for exactly
        one revision, under the name [xv6_violation_harts], and it was FALSE
        AS STATED for xv6.  Recorded because the shape recurs:
        [WeakRobust.violation] quantified the AUTHOR [i] and the OBSERVER [j]
        over ALL agents, while [WeakGhost.no_violation] — and the C/D/S
        invariants behind it — speak only about HARTS ([CPU]s), because a
        device never publishes and is exempt by construction
        ([WeakGhost.wcds_clean], [WeakLang.n_disk_not_hart]).  Concretely:
          - a hart that READS a byte the virtio DMA wrote raises its [coh] to
            that message's timestamp; the message is [WCplain]
            ([wmsgs_of_map]), hence [cls_of = SCowned], and it is never
            published, so [violation] holds with [i = n_disk].  φ says nothing
            about it and cannot.
          - symmetrically, the DISK agent's own [store_post_run] raises its
            [coh], so a DMA over a byte a hart wrote plainly gives
            [violation] with [j = n_disk].
        So [pf_violation_free cls_of pub_of (pstep_xv6 next) img (xv6_ps …)]
        was not merely undischarged: it was REFUTABLE for any run in which a
        hart reads DMA'd data, which made [xv6_weak_robust] VACUOUS on
        realistic runs.  THE FIX, and it was small and mechanical, belonged in
        Layer 1 and has landed there:
          (i)   [WeakRobust.violation_hart nh] (= [violation] with
                [WeakMem.tid_hart nh (wm_tid m)] and [tid_hart nh (Some j)])
                and [WeakRobust.pf_violation_free_hart nh];
          (ii)  [WeakRobustMain.bad] carries the reader's bound [e2.1 < nh]
                beside the author's [e1.1 < nh] (both are free at the site
                that discharges [edges_split]: only the hart arms of
                [pstep_xv6] emit [LLoad]/[LRmw], so a [grf] edge's reader is a
                hart), and [bad_edge_violates] concludes [violation_hart nh]
                — the author conjunct is [bad]'s third component and the
                observer conjunct its fourth, verbatim;
          (iii) [no_bad_edge] / [gdep2_acyclic_main] / [robust_main] /
                [robust_transport] and [WeakCompose.m6_side_conditions] all
                consume the [_hart] form.
        [xv6_pf_violation_free] below therefore closes with residue (A)
        alone: the two indices arrive bounded by [n_disk = NCPU] and
        [nat_to_fin] hands the transport its [CPU]s.

    ------------------------------------------------------------------------
    §C  THE cls_canon / rmw_tight RESIDUE (L2's header) — ROUTE CHOSEN: (B).

    [WeakPromiseBridge.wp_pf_step] carries a message's [wm_class] as a FREE
    BINDER, while [WeakInterp.wrun] COMPUTES it; L2 records the gap as
    [WeakSailLTS2.cls_canon] (and [rmw_tight] for the exclusive read window),
    both side conditions of [pf_solo] and hence of [sail_block].  The task
    offered two ways to pay for it:

      (A) a RETAG lemma — map an arbitrary pf run to a canonically classed one
          with the same log shape and the same [wstate]s.  It is sound in the
          direction that matters (retagging DOWN, [WCrel] ↦ [WCplain], only
          REMOVES publications, and [¬ pub] is exactly what the violation
          needs, so a violation survives), but retagging UP would destroy it,
          and the canonical class of a store is [WCrel] whenever the author's
          [w_relp] is set — i.e. the retag is NOT uniformly downward.  Making
          it work needs the [w_relp] bookkeeping of the whole run, which is a
          [WeakPromiseBridge]-level induction.

      (B) CLASS-CANONICITY AS A CONDITION ON THE RUNS BEING MAPPED.  This is
          what is taken here, and it costs nothing extra: [cls_canon] is
          already inside [sail_block] (so the HART side is paid by residue
          (A)'s provider), and the DISK side is paid OUTRIGHT — [emit_run]
          instantiates [PFStore]'s class binder at the message's own
          [wm_ak], and [seg_disk] pins the emitted list to
          [WeakLang.wmsgs_of_map w], whose messages are [WCplain] by
          construction.  So the disk's classes are canonical by CONSTRUCTION
          here, not by assumption.
    Nothing is added to [WeakCompose.m6_side_conditions]: [WeakCompose.v] is
    UNCHANGED by this file.

    ------------------------------------------------------------------------
    §D  THE PREMISE LIST OF [xv6_weak_robust_adequate] — the composition's new
    assumptions inventory (against [WeakCompose] §6's):

      1. [∀ b, sail_shaped (riscv_step b)] — seam (6), unchanged.
      2. THE FRESH ERA: [gen_id = 0], [wgpow g0 = true], [wggen g0 = 0],
         [wglog g0 = []], [∀ c, wgws g0 c = ws_init], [wa_dws u0 = ws_init]
         — literally [weak_system_adequacy_phi]'s, plus the disk agent's own
         [wstate] (the wp machine has an agent [WeakLang] does not).
      3. THE ADEQUACY WP PACKAGE — the pool's WPs from the initial resources,
         verbatim [WeakAdequacy.weak_system_adequacy_phi]'s premise.
      4. [xv6_block_cover] — residue (A) above, and THE ONLY RESIDUE: (B) is
         gone, fixed in Layer 1 (see §B).
      5. The FIRST conjunct of [m6_side_conditions] (the per-bundle static
         side conditions [main_premises n_disk], = [WeakCompose] §6 (3)),
         with [bad] now bounding the READER's agent index too.
      6. Inside the segments, three DEVICE-SEAM side conditions, all of them
         seam (4) ([WeakCompose] §6) in sharper form:
         [WeakSailLTS2.oracle_consistent] per hart block (L2's, unchanged);
         [hart_dev_seam] — the post-block fabric IS the one the block's own
         [wrun] produces (the companion of [oracle_consistent]: a [wpcfg] has
         no device component, so this is not a function of the pf state);
         the PLIC WIRE premise inside [seg_plic] (the delivered value is
         [bool_to_bit (dev_seip …)], the interrupt-oracle twin of
         [oracle_consistent]); and [wa_dd u = wgdev g] inside [seg_disk] (the
         M5 device-view residue, [WeakCompose] delta (i)).
      7. The 5 rv64d baseline axioms.  NO functional extensionality, NO
         classical axiom: [Print Assumptions xv6_weak_robust_adequate] lists
         exactly [rv64d.load_reservation], [match_reservation],
         [cancel_reservation], [valid_reservation], [plat_term_write].

    WHAT IS GONE relative to [WeakCompose] §6: seam (1a) (the ⇐ hart
    direction — L2 built it, §3 consumes it), (1b) (interleaving regrouping —
    §7, for block-atomic runs), (1c) (device and power arms — the plic and
    disk arms are built; uart and power are shown unnecessary rather than
    assumed), and, MODULO residue (A), seam (2)
    ([pf_violation_free_hart] itself).

    NOTE ON NAMES.  [WeakAxiomatic] is imported FIRST so that [WeakPromise]'s
    [wlabel] constructors shadow its [lbl] ones (as in [WeakRobustBlocks]);
    every label occurrence is QUALIFIED [WeakPromise.LStore] &c. anyway. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge.
From xv6iris Require Import WeakRobust WeakRobustTrace WeakRobustSim WeakRobustMain.
From xv6iris Require Import WeakRobustBlocks.
From xv6iris Require Import WeakInterp WeakInterpProj WeakSailLTS WeakSailLTS2.
Require Import RiscvLang WeakLang.
From xv6iris Require Import WeakCompose.
From iris.algebra Require Import dfrac.
From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import RiscvPtsto RiscvAdequacy.
From xv6iris Require Import WeakGhost WeakAdequacy.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. Small list / [CPU] plumbing *)

Lemma fin_enum_lookup (n : nat) (h : fin n) :
  fin_enum n !! (fin_to_nat h) = Some h.
Proof. induction h as [|n h IH]; simpl; [done|]. by rewrite list_lookup_fmap IH. Qed.

Lemma cpu_enum_lookup (h : CPU) : enum CPU !! (fin_to_nat h) = Some h.
Proof. apply fin_enum_lookup. Qed.

Lemma cpu_enum_length : length (enum CPU) = NCPU.
Proof. exact (fin_card NCPU). Qed.

Lemma cpu_enum_index (k : nat) (c : CPU) : enum CPU !! k = Some c → k = fin_to_nat c.
Proof.
  intros Hk. eapply (list_relations.NoDup_lookup (enum CPU)); [apply NoDup_enum|exact Hk|].
  apply cpu_enum_lookup.
Qed.

(** A pointwise function update on [CPU] (the [dstream] / [istream] twin of
    [RiscvLang.greg_insert] and [WeakLang.gws_insert]). *)
Definition cupd {A} (c : CPU) (x : A) (f : CPU → A) : CPU → A :=
  λ c', if decide (c' = c) then x else f c'.

Lemma cupd_eq {A} (c : CPU) (x : A) f : cupd c x f c = x.
Proof. rewrite /cupd. by destruct (decide (c = c)). Qed.

Lemma cupd_ne {A} (c c' : CPU) (x : A) f : c' ≠ c → cupd c x f c' = f c'.
Proof. intros Hne. rewrite /cupd. by destruct (decide (c' = c)). Qed.

(** Updating the [fin_to_nat cpu] slot of a [CPU]-indexed vector to a new
    indexing function that agrees with the old one everywhere else. *)
Lemma cpu_fmap_insert {A} (f h : CPU → A) (cpu : CPU) :
  (∀ c, c ≠ cpu → f c = h c) →
  <[fin_to_nat cpu := h cpu]> (f <$> enum CPU) = h <$> enum CPU.
Proof.
  intros Hne. apply list_eq. intros k.
  destruct (decide (k = fin_to_nat cpu)) as [->|Hk].
  - rewrite list_lookup_insert;
      [|rewrite length_fmap cpu_enum_length; apply fin_to_nat_lt].
    by rewrite list_lookup_fmap cpu_enum_lookup.
  - rewrite list_lookup_insert_ne; [|done].
    rewrite !list_lookup_fmap.
    destruct (enum CPU !! k) as [c|] eqn:Hc; [|done]. simpl.
    f_equal. apply Hne. intros ->. apply Hk. by eapply cpu_enum_index.
Qed.

Lemma fmap_fmap_l {A B C} (f : B → C) (h : A → B) (l : list A) :
  f <$> (h <$> l) = (λ x, f (h x)) <$> l.
Proof. by rewrite -list_fmap_compose. Qed.

Lemma lookup_app_last {A} (l : list A) (x : A) : (l ++ [x]) !! length l = Some x.
Proof. rewrite lookup_app_r; [|lia]. by rewrite Nat.sub_diag. Qed.

Lemma insert_app_last {A} (l : list A) (x y : A) :
  <[length l := x]> (l ++ [y]) = l ++ [x].
Proof.
  apply list_eq. intros k.
  destruct (decide (k = length l)) as [->|Hk].
  - rewrite list_lookup_insert; [|rewrite length_app /=; lia].
    by rewrite lookup_app_last.
  - rewrite list_lookup_insert_ne; [|done].
    destruct (decide (k < length l)%nat) as [Hlt|Hge].
    + by rewrite !lookup_app_l.
    + rewrite (lookup_app_r l [y] k); [|lia].
      rewrite (lookup_app_r l [x] k); [|lia].
      assert (Hs : (k - length l)%nat = S (k - length l - 1)) by lia.
      rewrite Hs /=. done.
Qed.

(* ====================================================================== *)
(** ** 1. THE CORRESPONDENCE

    A [WeakLang] state [g] plus the per-agent data the wp machine carries and
    [wgstate] does not — the two ORACLE STREAMS of [WeakSailLTS.psail] and the
    disk agent's own fabric state and [wstate] — determine one [wpcfg pxv6],
    with the harts at indices [0 .. NCPU-1] and the disk at [NCPU]
    ([WeakLang.n_disk], [WeakCompose.xv6_ps]'s layout). *)

Record wlaux := WLAux {
  wa_dstr : CPU → dstream;
  wa_iq   : CPU → istream;
  wa_dd   : dev_state;
  wa_dws  : wstate;
}.

Definition hag (g : wgstate) (u : wlaux) (c : CPU) : wpagent psail :=
  WPAgent (PSail None (wgregs g c) (wa_dstr u c) None (wa_iq u c))
          (wgws g c) (∅ : gset nat).

(** The HART-ONLY configuration, at the [psail] program type: this is what
    [WeakSailLTS2]'s ⇐ bracket is stated over. *)
Definition hcfg (g : wgstate) (u : wlaux) : wpcfg psail :=
  WPCfg (img_z (wgimg g)) (wglog g) (hag g u <$> enum CPU).

Definition dkag (u : wlaux) : wpagent pxv6 :=
  WPAgent (PDisk (wa_dd u) []) (wa_dws u) (∅ : gset nat).

(** …and the full [pxv6] configuration: the harts embedded by
    [WeakCompose.lift_cfg], the disk agent framed at index [NCPU]. *)
Definition wl_cfg (g : wgstate) (u : wlaux) : wpcfg pxv6 :=
  lift_cfg [dkag u] (hcfg g u).

Lemma wl_cfg_alt g u :
  wl_cfg g u
  = WPCfg (img_z (wgimg g)) (wglog g)
      (((λ c, lift_ag (hag g u c)) <$> enum CPU) ++ [dkag u]).
Proof.
  rewrite /wl_cfg /lift_cfg /hcfg. cbn [pc_img pc_log pc_ags].
  by rewrite fmap_fmap_l.
Qed.

Lemma wl_cfg_img g u : pc_img (wl_cfg g u) = img_z (wgimg g).
Proof. done. Qed.

Lemma wl_cfg_log g u : pc_log (wl_cfg g u) = wglog g.
Proof. done. Qed.

Lemma hcfg_lookup g u (cpu : CPU) :
  (hag g u <$> enum CPU) !! (fin_to_nat cpu) = Some (hag g u cpu).
Proof. by rewrite list_lookup_fmap cpu_enum_lookup. Qed.

Lemma wl_cfg_hart_lookup g u (cpu : CPU) :
  pc_ags (wl_cfg g u) !! (fin_to_nat cpu) = Some (lift_ag (hag g u cpu)).
Proof. apply lift_ags_lookup, hcfg_lookup. Qed.

Lemma wl_cfg_harts_len g u : length ((λ c, lift_ag (hag g u c)) <$> enum CPU) = NCPU.
Proof. by rewrite length_fmap cpu_enum_length. Qed.

Lemma wl_cfg_disk_lookup g u : pc_ags (wl_cfg g u) !! n_disk = Some (dkag u).
Proof.
  have Hl : length ((λ c, lift_ag (hag g u c)) <$> enum CPU) = n_disk
    by rewrite wl_cfg_harts_len.
  rewrite wl_cfg_alt. cbn [pc_ags]. rewrite -Hl. apply lookup_app_last.
Qed.

(** The observation floor of hart [cpu] in the corresponding configuration IS
    that hart's [coh] in [g] — the [φ] transport reads exactly this. *)
Lemma wl_cfg_obs_flr g u (cpu : CPU) (a : Z) :
  obs_flr (wl_cfg g u) (fin_to_nat cpu) a = coh (wgws g cpu) a.
Proof. by rewrite /obs_flr wl_cfg_hart_lookup. Qed.

(* ====================================================================== *)
(** ** 2. The three [wgstate] transitions the segments land on *)

Definition wplic_write (g : wgstate) (cpu : CPU) : wgstate :=
  WGState (<[cpu := register_set sig_seip
                      (bool_to_bit (dev_seip (wgdev g) (fin_to_nat cpu)))
                      (wgregs g cpu)]> (wgregs g))
          (wgimg g) (wglog g) (wgws g) (wgdev g) (wggen g) (wgpow g).

Definition wdisk_write (g : wgstate) (d' : dev_state)
    (w : gmap Arch.pa (bv 8)) : wgstate :=
  WGState (wgregs g) (wgimg g) (wglog g ++ wmsgs_of_map w) (wgws g)
          d' (wggen g) (wgpow g).

(** The disk agent's own [wstate] after emitting a burst: one
    [store_post_run] per buffered message, at consecutive timestamps. *)
Fixpoint emit_ws (ws : wstate) (t : nat) (ms : list wmsg) : wstate :=
  match ms with
  | [] => ws
  | m :: ms' =>
      emit_ws (store_post_run ws false (wm_pa m) (length (wm_data m)) (S t))
              (S t) ms'
  end.

(* ====================================================================== *)
(** ** 3. THE THREE SEGMENTS

    A block-atomic pf run is a concatenation of three kinds of segment, one
    per [WeakLang.wprim_step] arm the wp machine can express: a hart's
    irq-free INSTRUCTION BLOCK, one INTERRUPT DELIVERY, and one DISK BURST
    with its emit group.  (The uart arm has no wp-side agent at all, and the
    power arm is vacuous at a pinned generation — see the header.) *)

(** THE DEVICE SEAM OF THE HART ARM (seam (4) of [WeakCompose] §6, here in
    its sharpest form).  A [wpcfg] has no device component: the pf machine
    serves a hart's MMIO from the oracle stream [sp_dev] and NEVER moves a
    shared fabric, while [wrun] threads [wm_dev].  The post-block fabric is
    therefore not a function of the pf configuration, and the segment must
    name it.  [hart_dev_seam g cpu g'] says [wgdev g'] IS the fabric the
    block's own [wrun] produces — the exact companion of L2's
    [oracle_consistent], which says the stream IS what that fabric returns. *)
Definition hart_dev_seam (g : wgstate) (cpu : CPU) (g' : wgstate) : Prop :=
  ∀ (tick : bool) (x : unit) (s' : wmstate),
    wrun (Some (fin_to_nat cpu)) (riscv_step tick) (whart_view g cpu) x s' →
    wm_log s' = wglog g' → wm_regs s' = wgregs g' cpu → wm_ws s' = wgws g' cpu →
    wm_dev s' = wgdev g'.

(** ONE HART BLOCK.  [sail_block] is L2's boundary-to-boundary,
    solo, irq-free, faithfully-classed block ([cls_canon] / [rmw_tight] are
    inside [pf_solo]); the frame conditions say the block moves only its own
    hart's registers and weak state, and nothing of the disk agent. *)
Definition seg_hart (g : wgstate) (u : wlaux) (cpu : CPU)
    (g' : wgstate) (u' : wlaux) : Prop :=
  (∀ b, oracle_consistent (wgdev g) (riscv_step b) (wa_dstr u cpu)) ∧
  sail_block riscv_step (fin_to_nat cpu) (hcfg g u) (hcfg g' u') ∧
  wgimg g' = wgimg g ∧ wggen g' = wggen g ∧ wgpow g' = wgpow g ∧
  wgregs g' = <[cpu := wgregs g' cpu]> (wgregs g) ∧
  wgws g' = <[cpu := wgws g' cpu]> (wgws g) ∧
  wa_dd u' = wa_dd u ∧ wa_dws u' = wa_dws u ∧
  hart_dev_seam g cpu g'.

(** ONE INTERRUPT DELIVERY.  [RiscvLang.plic_step]'s [PlicStepWire] writes
    hart [cpu]'s [sig_seip] from [dev_seip]; the wp side's [irq_deliver]
    consumes the head of that hart's interrupt oracle.  THE WIRE PREMISE is
    that the two carry the same value — the [plic_consistent] slot, the
    interrupt-oracle twin of [oracle_consistent]. *)
Definition seg_plic (g : wgstate) (u : wlaux) (cpu : CPU)
    (g' : wgstate) (u' : wlaux) : Prop :=
  (∃ (v : type_of_register sig_seip) (iq' : istream),
     wa_iq u cpu = v :: iq' ∧
     v = bool_to_bit (dev_seip (wgdev g) (fin_to_nat cpu)) ∧
     u' = WLAux (wa_dstr u) (cupd cpu iq' (wa_iq u)) (wa_dd u) (wa_dws u)) ∧
  g' = wplic_write g cpu.

(** ONE DISK STEP.  L0(d) buffers a [wdisk_step]'s write set in the disk
    agent and emits it one message at a time, so ONE [WeakLang] disk arm is
    [1 + |w|] pf steps; this segment is that whole group.  [wa_dd u = wgdev
    g] is the M5 device-view residue (delta (i) of [WeakCompose]): the pf
    disk agent's fabric is the machine's at a DMA. *)
Definition seg_disk (g : wgstate) (u : wlaux) (g' : wgstate) (u' : wlaux)
    : Prop :=
  wa_dd u = wgdev g ∧
  ∃ (d' : dev_state) (w : gmap Arch.pa (bv 8)),
    wdisk_step (wgdev g) (wflat (wgimg g) (wglog g)) d' w ∧
    g' = wdisk_write g d' w ∧
    u' = WLAux (wa_dstr u) (wa_iq u) d'
           (emit_ws (wa_dws u) (length (wglog g)) (wmsgs_of_map w)).

Definition xv6_seg (g : wgstate) (u : wlaux) (g' : wgstate) (u' : wlaux)
    : Prop :=
  (∃ cpu, seg_hart g u cpu g' u') ∨ (∃ cpu, seg_plic g u cpu g' u')
  ∨ seg_disk g u g' u'.

Definition xv6_stepR (x y : wgstate * wlaux) : Prop := xv6_seg x.1 x.2 y.1 y.2.

(** A BLOCK-ATOMIC RUN. *)
Definition xv6_blocks : relation (wgstate * wlaux) := rtc xv6_stepR.

(* ====================================================================== *)
(** ** 4. Each segment IS a promise-free run of [pstep_xv6] *)

Lemma sail_block_pf_run (i : agent) (c c' : wpcfg psail) :
  sail_block riscv_step i c c' → rtc (wp_pf_run (sail_step riscv_step)) c c'.
Proof.
  intros (_ & _ & c0 & Hsolo & Hrtc).
  eapply rtc_l; [by eapply pf_solo_run|].
  clear Hsolo. induction Hrtc as [|x y z [_ Hs] _ IH]; [done|].
  eapply rtc_l; [by eapply pf_solo_run|exact IH].
Qed.

(** The emit group: one [PFStore] per buffered message, appending EXACTLY
    the messages [WeakLang.wmsgs_of_map] would.  The class binder of
    [PFStore] is instantiated at the message's own [wm_ak] — that is the
    disk half of the [cls_canon] residue (see the header). *)
Lemma emit_run (img : image) (hags : list (wpagent pxv6)) (d : dev_state)
    (ms : list wmsg) :
  Forall (λ m, wm_tid m = Some (length hags) ∧ wm_data m ≠ []) ms →
  ∀ (log : list wmsg) (ws : wstate),
  rtc (wp_pf_run (pstep_xv6 riscv_step))
    (WPCfg img log (hags ++ [WPAgent (PDisk d ms) ws ∅]))
    (WPCfg img (log ++ ms)
       (hags ++ [WPAgent (PDisk d []) (emit_ws ws (length log) ms) ∅])).
Proof.
  induction ms as [|m ms' IH]; intros Hall log ws.
  { rewrite app_nil_r /=. apply rtc_refl. }
  apply Forall_cons in Hall as [[Htid Hdata] Hall'].
  have Hm : WMsg (wm_pa m) (wm_data m) (Some (length hags)) (wm_ak m) = m.
  { destruct m as [pa dat tid ak]; simpl in Htid; by rewrite Htid. }
  eapply rtc_l.
  { exists (length hags), (WeakPromise.LStore false (wm_pa m) (wm_data m)).
    eapply (PFStore (pstep_xv6 riscv_step) (length hags)
              (WPCfg img log (hags ++ [WPAgent (PDisk d (m :: ms')) ws ∅]))
              (WPAgent (PDisk d (m :: ms')) ws ∅) false (wm_pa m) (wm_data m)
              (wm_ak m) (PDisk d ms')).
    - cbn [pc_ags]. apply lookup_app_last.
    - cbn [pa_st]. right. by exists m, ms'.
    - exact Hdata. }
  cbn [pc_img pc_log pc_ags pa_ws pa_prom].
  rewrite Hm insert_app_last.
  have Hlen : length (log ++ [m]) = S (length log) by rewrite length_app /=; lia.
  have HIH := IH Hall' (log ++ [m])
                (store_post_run ws false (wm_pa m) (length (wm_data m))
                   (S (length log))).
  rewrite Hlen -app_assoc /= in HIH. exact HIH.
Qed.

(* ====================================================================== *)
(** ** 5. THE THREAD POOL and one [erased_step] *)

Definition wpool (gen : nat) : list mexpr :=
  (LoopE gen <$> enum CPU) ++ [UartLoopE gen; DiskLoopE gen; PlicLoopE gen].

Lemma wpool_hart gen (cpu : CPU) :
  wpool gen !! (fin_to_nat cpu) = Some (LoopE gen cpu).
Proof.
  rewrite /wpool lookup_app_l;
    [|rewrite length_fmap cpu_enum_length; apply fin_to_nat_lt].
  by rewrite list_lookup_fmap cpu_enum_lookup.
Qed.

Lemma wpool_disk gen : wpool gen !! (NCPU + 1)%nat = Some (DiskLoopE gen).
Proof.
  rewrite /wpool lookup_app_r;
    [|rewrite length_fmap cpu_enum_length; lia].
  rewrite length_fmap cpu_enum_length.
  by replace (NCPU + 1 - NCPU)%nat with 1%nat by lia.
Qed.

Lemma wpool_plic gen : wpool gen !! (NCPU + 2)%nat = Some (PlicLoopE gen).
Proof.
  rewrite /wpool lookup_app_r;
    [|rewrite length_fmap cpu_enum_length; lia].
  rewrite length_fmap cpu_enum_length.
  by replace (NCPU + 2 - NCPU)%nat with 2%nat by lia.
Qed.

(** One [wprim_step] of a thread of the pool IS one [erased_step]; no arm
    used below forks, so the pool is literally constant. *)
Lemma pool_erased (t : list mexpr) (k : nat) (e : mexpr) (g g' : wgstate) :
  t !! k = Some e → wprim_step e g [] e g' [] →
  @erased_step weak_riscv_lang (t, g) (t, g').
Proof.
  intros Hk Hst. exists [].
  have Ht := take_drop_middle t k e Hk.
  eapply (@step_atomic weak_riscv_lang _ [] _ e g e g' [] (take k t) (drop (S k) t)).
  - by rewrite Ht.
  - rewrite app_nil_r. by rewrite Ht.
  - exact Hst.
Qed.

(* ====================================================================== *)
(** ** 6. Each segment maps to ONE [wprim_step] *)

(** THE HART ARM.  [WeakSailLTS2.sail_block_wrun] inverts the block into the
    [wrun] of one instruction at [whart_view g cpu]; the frame conditions of
    [seg_hart] then say the segment's target IS [whart_write g cpu s']. *)
Lemma seg_hart_step (gen : nat) g u cpu g' u' :
  (∀ b, sail_shaped (riscv_step b)) →
  wthread_live g gen →
  seg_hart g u cpu g' u' →
  wthread_live g' gen ∧
  rtc (wp_pf_run (pstep_xv6 riscv_step)) (wl_cfg g u) (wl_cfg g' u') ∧
  wprim_step (LoopE gen cpu) g [] (LoopE gen cpu) g' [].
Proof.
  intros Hsh Hlive
    (Hoc & Hblk & Himg & Hgen & Hpow & Hregs & Hws & Hdd & Hdws & Hseam).
  have Hdk : dkag u' = dkag u by rewrite /dkag Hdd Hdws.
  split_and!.
  { destruct Hlive as [Hp Hg]. split; [by rewrite Hpow|by rewrite Hgen]. }
  { rewrite /wl_cfg Hdk. apply (pf_run_frame riscv_step [dkag u]).
    exact (sail_block_pf_run (fin_to_nat cpu) _ _ Hblk). }
  destruct (sail_block_wrun riscv_step (fin_to_nat cpu) (whart_view g cpu)
              (wa_dstr u cpu) (wa_iq u cpu) ∅ (hag g u <$> enum CPU)
              (hcfg g' u') Hsh Hoc (hcfg_lookup g u cpu) Hblk)
    as (tick & x & s' & dtl & Hrun & Heq).
  have Hl : wglog g' = wm_log s' by exact (f_equal (@pc_log psail) Heq).
  have Ha : (hag g' u' <$> enum CPU)
          = <[fin_to_nat cpu :=
                WPAgent (PSail None (wm_regs s') dtl None (wa_iq u cpu))
                  (wm_ws s') ∅]> (hag g u <$> enum CPU)
    by exact (f_equal (@pc_ags psail) Heq).
  have Hcpu : hag g' u' cpu
            = WPAgent (PSail None (wm_regs s') dtl None (wa_iq u cpu))
                (wm_ws s') ∅.
  { have H : (hag g' u' <$> enum CPU) !! (fin_to_nat cpu)
           = (<[fin_to_nat cpu :=
                  WPAgent (PSail None (wm_regs s') dtl None (wa_iq u cpu))
                    (wm_ws s') ∅]> (hag g u <$> enum CPU)) !! (fin_to_nat cpu)
      by rewrite Ha.
    rewrite (hcfg_lookup g' u' cpu) in H.
    rewrite list_lookup_insert in H;
      [|rewrite length_fmap cpu_enum_length; apply fin_to_nat_lt].
    apply (inj Some) in H. exact H. }
  have Hregc : wgregs g' cpu = wm_regs s'
    by exact (f_equal (λ a : wpagent psail, sp_regs (pa_st a)) Hcpu).
  have Hwsc : wgws g' cpu = wm_ws s'
    by exact (f_equal (λ a : wpagent psail, pa_ws a) Hcpu).
  have Hdev : wm_dev s' = wgdev g'.
  { apply (Hseam tick x s' Hrun);
      [by rewrite Hl|by rewrite Hregc|by rewrite Hwsc]. }
  left. exists gen, cpu. split_and!; [reflexivity|reflexivity|reflexivity|reflexivity|].
  left. split; [exact Hlive|]. exists tick, x, s'. split; [exact Hrun|].
  rewrite /whart_write.
  destruct g' as [r0 i0 l0 w0 d0 n0 p0]. cbn in *.
  rewrite -Hdev -Himg -Hgen -Hpow -Hl. f_equal.
  - rewrite Hregs. by rewrite Hregc.
  - rewrite Hws. by rewrite Hwsc.
Qed.

(** A one-hart update of the configuration, in the shape [PFSilent] /
    [PFLoad] / … produce it. *)
Lemma wl_cfg_hart_update g u cpu (g' : wgstate) (u' : wlaux) (st' : psail) :
  wa_dd u' = wa_dd u → wa_dws u' = wa_dws u →
  wgimg g' = wgimg g → wglog g' = wglog g →
  (∀ c, c ≠ cpu → hag g' u' c = hag g u c) →
  hag g' u' cpu = WPAgent st' (wgws g cpu) ∅ →
  WPCfg (pc_img (wl_cfg g u)) (pc_log (wl_cfg g u))
    (<[fin_to_nat cpu := WPAgent (PHart st') (wgws g cpu) (∅ : gset nat)]>
       (pc_ags (wl_cfg g u)))
  = wl_cfg g' u'.
Proof.
  intros Hdd Hdws Himg Hlog Hne Hcpu.
  rewrite !wl_cfg_alt. cbn [pc_img pc_log pc_ags].
  rewrite Himg Hlog /dkag Hdd Hdws. f_equal.
  rewrite insert_app_l; [|rewrite wl_cfg_harts_len; apply fin_to_nat_lt].
  f_equal.
  have Hx : WPAgent (PHart st') (wgws g cpu) (∅ : gset nat)
          = lift_ag (hag g' u' cpu) by rewrite Hcpu.
  rewrite Hx.
  apply (cpu_fmap_insert (λ c, lift_ag (hag g u c))
           (λ c, lift_ag (hag g' u' c)) cpu).
  intros c Hc. by rewrite (Hne c Hc).
Qed.

(** THE PLIC ARM. *)
Lemma seg_plic_step (gen : nat) g u cpu g' u' :
  wthread_live g gen →
  seg_plic g u cpu g' u' →
  wthread_live g' gen ∧
  rtc (wp_pf_run (pstep_xv6 riscv_step)) (wl_cfg g u) (wl_cfg g' u') ∧
  wprim_step (PlicLoopE gen) g [] (PlicLoopE gen) g' [].
Proof.
  intros Hlive ((v & iq' & Hiq & Hv & ->) & ->).
  split_and!; [exact Hlive| |].
  - apply rtc_once.
    have Heq : WPCfg (pc_img (wl_cfg g u)) (pc_log (wl_cfg g u))
                 (<[fin_to_nat cpu :=
                      WPAgent (PHart (PSail None
                                        (register_set sig_seip v (wgregs g cpu))
                                        (wa_dstr u cpu) None iq'))
                        (wgws g cpu) (∅ : gset nat)]> (pc_ags (wl_cfg g u)))
             = wl_cfg (wplic_write g cpu)
                 (WLAux (wa_dstr u) (cupd cpu iq' (wa_iq u)) (wa_dd u) (wa_dws u)).
    { apply wl_cfg_hart_update; [done|done|done|done| |].
      - intros c Hc. rewrite /hag /wplic_write /=.
        by rewrite (greg_insert_ne _ _ _ _ Hc) (cupd_ne _ _ _ _ Hc).
      - rewrite /hag /wplic_write /=. by rewrite greg_insert_eq cupd_eq -Hv. }
    rewrite -Heq. exists (fin_to_nat cpu), WeakPromise.LSilent.
    apply (PFSilent (pstep_xv6 riscv_step) (fin_to_nat cpu) (wl_cfg g u)
             (lift_ag (hag g u cpu)) _ (wl_cfg_hart_lookup g u cpu)).
    cbn [pa_st lift_ag hag]. rewrite /pstep_xv6 /sail_step /=.
    left. split; [reflexivity|]. exists v, iq'. by rewrite Hiq.
  - right. right. right. left. exists gen.
    split_and!; [reflexivity|reflexivity|reflexivity|reflexivity|].
    left. split; [exact Hlive|].
    exists (<[cpu := register_set sig_seip
                       (bool_to_bit (dev_seip (wgdev g) (fin_to_nat cpu)))
                       (wgregs g cpu)]> (wgregs g)).
    split; [apply PlicStepWire|reflexivity].
Qed.

(** THE DISK ARM: the burst step plus its emit group — [1 + |w|] pf steps
    against ONE [WeakLang] disk arm (delta (i) of [WeakCompose], inverted). *)
Lemma seg_disk_step (gen : nat) g u g' u' :
  wthread_live g gen →
  seg_disk g u g' u' →
  wthread_live g' gen ∧
  rtc (wp_pf_run (pstep_xv6 riscv_step)) (wl_cfg g u) (wl_cfg g' u') ∧
  wprim_step (DiskLoopE gen) g [] (DiskLoopE gen) g' [].
Proof.
  intros Hlive (Hdd & d' & w & Hds & -> & ->).
  set (hags := (λ c, lift_ag (hag g u c)) <$> enum CPU).
  have Hlen : length hags = n_disk by rewrite /hags wl_cfg_harts_len.
  have Hags : pc_ags (wl_cfg g u) = hags ++ [dkag u] by rewrite wl_cfg_alt.
  split_and!; [exact Hlive| |].
  - have Hburst : wp_pf_run (pstep_xv6 riscv_step) (wl_cfg g u)
        (WPCfg (img_z (wgimg g)) (wglog g)
           (hags ++ [WPAgent (PDisk d' (wmsgs_of_map w))
                       (wa_dws u) (∅ : gset nat)])).
    { have Heqm : WPCfg (pc_img (wl_cfg g u)) (pc_log (wl_cfg g u))
                    (<[n_disk := WPAgent (PDisk d' (wmsgs_of_map w))
                                   (pa_ws (dkag u)) (pa_prom (dkag u))]>
                       (pc_ags (wl_cfg g u)))
                = WPCfg (img_z (wgimg g)) (wglog g)
                    (hags ++ [WPAgent (PDisk d' (wmsgs_of_map w))
                                (wa_dws u) (∅ : gset nat)]).
      { rewrite Hags.
        change (pa_ws (dkag u)) with (wa_dws u).
        change (pa_prom (dkag u)) with (∅ : gset nat).
        f_equal; rewrite -Hlen; apply insert_app_last. }
      rewrite -Heqm. exists n_disk, WeakPromise.LSilent.
      apply (PFSilent (pstep_xv6 riscv_step) n_disk (wl_cfg g u) (dkag u)
               (PDisk d' (wmsgs_of_map w)) (wl_cfg_disk_lookup g u)).
      cbn [pa_st dkag]. left. split; [reflexivity|]. right.
      split; [reflexivity|]. exists (wflat (wgimg g) (wglog g)), w.
      split; [by rewrite Hdd|reflexivity]. }
    eapply rtc_transitive.
    { apply rtc_once. exact Hburst. }
    have Hall : Forall (λ m, wm_tid m = Some (length hags) ∧ wm_data m ≠ [])
                  (wmsgs_of_map w).
    { apply Forall_forall. intros m Hm. split.
      - rewrite (wmsgs_of_map_tid w m Hm). by rewrite Hlen.
      - by apply (wmsgs_of_map_data w). }
    have HE := emit_run (img_z (wgimg g)) hags d' (wmsgs_of_map w) Hall
                 (wglog g) (wa_dws u).
    exact HE.
  - right. right. left. exists gen.
    split_and!; [reflexivity|reflexivity|reflexivity|reflexivity|].
    left. split; [exact Hlive|]. exists d', w. split; [exact Hds|reflexivity].
Qed.

(* ====================================================================== *)
(** ** 7. THE REGROUPING THEOREM

    A block-atomic pf run of [pstep_xv6 riscv_step] from a corresponding
    configuration IS an [rtc erased_step] of [WeakLang.weak_riscv_lang] over
    the standard pool, and the reached configurations correspond again — same
    log, same per-hart [wstate], same per-hart registers. *)

Theorem xv6_seg_lang (gen : nat) g u g' u' :
  (∀ b, sail_shaped (riscv_step b)) → wthread_live g gen →
  xv6_seg g u g' u' →
  wthread_live g' gen ∧
  rtc (wp_pf_run (pstep_xv6 riscv_step)) (wl_cfg g u) (wl_cfg g' u') ∧
  @erased_step weak_riscv_lang (wpool gen, g) (wpool gen, g').
Proof.
  intros Hsh Hlive [[cpu Hs]|[[cpu Hs]|Hs]].
  - destruct (seg_hart_step gen g u cpu g' u' Hsh Hlive Hs) as (H1 & H2 & H3).
    split_and!; [done|done|]. by eapply pool_erased; [apply wpool_hart|].
  - destruct (seg_plic_step gen g u cpu g' u' Hlive Hs) as (H1 & H2 & H3).
    split_and!; [done|done|]. by eapply pool_erased; [apply wpool_plic|].
  - destruct (seg_disk_step gen g u g' u' Hlive Hs) as (H1 & H2 & H3).
    split_and!; [done|done|]. by eapply pool_erased; [apply wpool_disk|].
Qed.

Theorem xv6_blocks_lang (gen : nat) (Hsh : ∀ b, sail_shaped (riscv_step b))
    (x y : wgstate * wlaux) :
  xv6_blocks x y → wthread_live x.1 gen →
  wthread_live y.1 gen ∧
  rtc (wp_pf_run (pstep_xv6 riscv_step)) (wl_cfg x.1 x.2) (wl_cfg y.1 y.2) ∧
  rtc (@erased_step weak_riscv_lang) (wpool gen, x.1) (wpool gen, y.1).
Proof.
  induction 1 as [x|x y z Hxy _ IH]; intros Hlive.
  - split_and!; [done|apply rtc_refl|apply rtc_refl].
  - destruct (xv6_seg_lang gen x.1 x.2 y.1 y.2 Hsh Hlive Hxy) as (H1 & H2 & H3).
    destruct (IH H1) as (H4 & H5 & H6).
    split_and!; [done|by eapply rtc_transitive|by eapply rtc_l].
Qed.

(* ====================================================================== *)
(** ** 8. THE φ TRANSPORT

    [WeakGhost.no_violation] at the reached [WeakLang] state refutes a
    HART-AUTHORED, HART-OBSERVED violation at the corresponding pf
    configuration.  The transport is SYNTACTIC — L0(c) made [pub_of] the log
    predicate [WeakMem.wpublished], which is the one [no_violation] is stated
    with, and [obs_flr] IS the agent's [coh]. *)

Theorem xv6_blocks_no_hart_violation
    (gen : nat) (g0 : wgstate) (u0 : wlaux) (g' : wgstate) (u' : wlaux)
    (p : nat) (m : wmsg) (ci cj : CPU) (a : Z) :
  (∀ b, sail_shaped (riscv_step b)) →
  wthread_live g0 gen →
  (∀ t2 g2, rtc (@erased_step weak_riscv_lang) (wpool gen, g0) (t2, g2) →
            no_violation (wglog g2) (wgws g2)) →
  xv6_blocks (g0, u0) (g', u') →
  violates_at (wl_cfg g' u') p m (fin_to_nat ci) (fin_to_nat cj) a →
  False.
Proof.
  intros Hsh Hlive Hphi Hrun (Hlog & Htid & Hcls & Hpub & Hne & Hbyte & Hobs).
  destruct (xv6_blocks_lang gen Hsh (g0, u0) (g', u') Hrun Hlive)
    as (_ & _ & Her).
  have Hnv := Hphi _ _ Her.
  have Hak : wm_ak m = WCplain.
  { rewrite /cls_of in Hcls.
    destruct (wm_ak m); [reflexivity|discriminate|discriminate]. }
  have Hnp : ¬ wpublished (wglog g') (wm_tid m) p.
  { intros Hp. apply Hpub. exists p, m.
    split_and!; [reflexivity|exact Hlog|exact Hp]. }
  have Hcne : cj ≠ ci.
  { intros Heq. apply Hne. by rewrite Heq. }
  have Hlt := Hnv p m ci a Hlog Htid Hak Hnp Hbyte cj Hcne.
  rewrite wl_cfg_obs_flr in Hobs.
  exact (Nat.lt_irrefl _ (Nat.le_lt_trans _ _ _ Hobs Hlt)).
Qed.

(* ====================================================================== *)
(** ** 9. The initial configuration *)

Lemma map_fmap_eq {A B} (f : A → B) (l : list A) : map f l = f <$> l.
Proof. by induction l as [|x l IH]; simpl; [|rewrite IH]. Qed.

Lemma fmap_ext_l {A B} (f h : A → B) (l : list A) :
  (∀ x, f x = h x) → f <$> l = h <$> l.
Proof.
  intros H. induction l as [|x l IH]; [done|].
  by rewrite !fmap_cons H IH.
Qed.

(** The hart vector [WeakCompose.xv6_ps] is applied to. *)
Definition xv6_harts (g : wgstate) (u : wlaux) : list psail :=
  (λ c, PSail None (wgregs g c) (wa_dstr u c) None (wa_iq u c)) <$> enum CPU.

Definition xv6_ps0 (g : wgstate) (u : wlaux) : list pxv6 :=
  xv6_ps (wa_dd u) (xv6_harts g u).

(** In a FRESH ERA (empty log, every hart at [ws_init]) the wp machine's
    initial configuration IS the corresponding configuration. *)
Lemma wp_init_wl (g : wgstate) (u : wlaux) :
  wglog g = [] → (∀ c : CPU, wgws g c = ws_init) → wa_dws u = ws_init →
  wp_init (img_z (wgimg g)) (xv6_ps0 g u) = wl_cfg g u.
Proof.
  intros Hlog Hws Hdws.
  rewrite wl_cfg_alt Hlog /wp_init /xv6_ps0 /xv6_ps /xv6_harts.
  rewrite map_fmap_eq fmap_app !fmap_fmap_l.
  f_equal; f_equal.
  - apply fmap_ext_l. intros c. rewrite /lift_ag /hag /=. by rewrite (Hws c).
  - rewrite fmap_cons fmap_nil /dkag. by rewrite Hdws.
Qed.

(* ====================================================================== *)
(** ** 10. THE RESIDUE, and the derived [pf_violation_free_hart] *)

(** RESIDUE (A) — BLOCK-ATOMICITY (the interleaving/mover residue).  An
    arbitrary [wp_pf_run] interleaves the harts at EVENT granularity, while
    [WeakLang] steps whole instructions; the regrouping above therefore
    consumes runs that are already a concatenation of segments.  This premise
    is exactly the missing reordering theorem, stated where it is used: a
    violating pf-reachable configuration has a BLOCK-ATOMIC witness of the
    SAME violation.  (Its intended discharge, and why it is believable for
    rv64d, is in the header.) *)
Definition xv6_block_cover (g0 : wgstate) (u0 : wlaux) : Prop :=
  ∀ (c : wpcfg pxv6) p m i j a,
    rtc (wp_pf_run (pstep_xv6 riscv_step)) (wl_cfg g0 u0) c →
    violates_at c p m i j a →
    ∃ g' u', xv6_blocks (g0, u0) (g', u') ∧
             violates_at (wl_cfg g' u') p m i j a.

(** THE φ-CONSUMPTION COROLLARY: [pf_violation_free_hart] — the ONE conjunct
    of [WeakCompose.m6_side_conditions] that φ/Iris was left carrying —
    DERIVED from the adequacy export through the lift.

    THE AGENT QUANTIFIER IS NO LONGER A PREMISE (the L3 finding of §B, fixed
    in Layer 1 on 2026-08-12).  [WeakRobust.violation_hart] restricts BOTH the
    author and the observer to harts, exactly as [WeakGhost.no_violation]
    does, so the two indices arrive here already bounded by
    [WeakLang.n_disk = NCPU] and [nat_to_fin] turns them into the [CPU]s the
    transport wants.  The disk-authored and disk-observed DMA violations that
    made the OLD, unrestricted conjunct refutable are simply not instances of
    the statement any more. *)
Theorem xv6_pf_violation_free (gen : nat) (g0 : wgstate) (u0 : wlaux) :
  (∀ b, sail_shaped (riscv_step b)) →
  wthread_live g0 gen →
  (∀ t2 g2, rtc (@erased_step weak_riscv_lang) (wpool gen, g0) (t2, g2) →
            no_violation (wglog g2) (wgws g2)) →
  xv6_block_cover g0 u0 →
  ∀ c, rtc (wp_pf_run (pstep_xv6 riscv_step)) (wl_cfg g0 u0) c →
       ¬ violation_hart cls_of pub_of n_disk c.
Proof.
  intros Hsh Hlive Hphi Hcov c Hrun Hviol.
  destruct (violation_hart_violates_at n_disk c Hviol)
    as (p & m & i & j & a & Hv & Hi & Hj).
  destruct (Hcov c p m i j a Hrun Hv) as (g' & u' & Hbl & Hv').
  set (ci := nat_to_fin Hi : CPU).
  set (cj := nat_to_fin Hj : CPU).
  have Hci : fin_to_nat ci = i by apply fin_to_nat_to_fin.
  have Hcj : fin_to_nat cj = j by apply fin_to_nat_to_fin.
  eapply (xv6_blocks_no_hart_violation gen g0 u0 g' u' p m ci cj a);
    [exact Hsh|exact Hlive|exact Hphi|exact Hbl|].
  by rewrite Hci Hcj.
Qed.

(* ====================================================================== *)
(** ** 11. THE UPDATED COMPOSITION

    [WeakCompose.xv6_weak_robust] with [pf_violation_free_hart] REPLACED by
    its derivation.  The full premise list is in the header. *)

Corollary xv6_weak_robust_lifted (gen : nat) (g0 : wgstate) (u0 : wlaux)
    (c : wpcfg pxv6) :
  (∀ b, sail_shaped (riscv_step b)) →
  wthread_live g0 gen →
  wglog g0 = [] → (∀ cc : CPU, wgws g0 cc = ws_init) → wa_dws u0 = ws_init →
  (∀ t2 g2, rtc (@erased_step weak_riscv_lang) (wpool gen, g0) (t2, g2) →
            no_violation (wglog g2) (wgws g2)) →
  xv6_block_cover g0 u0 →
  (∀ (cb mid : wpcfg pxv6) (TS : ptraces pxv6),
     wp_behavior (pstep_xv6 riscv_step) (img_z (wgimg g0)) (xv6_ps0 g0 u0) cb →
     rtc (wp_promise_step (P := pxv6))
       (wp_init (img_z (wgimg g0)) (xv6_ps0 g0 u0)) mid →
     ptraces_of (pstep_xv6 riscv_step) TS mid cb →
     main_premises n_disk TS) →
  wp_behavior (pstep_xv6 riscv_step) (img_z (wgimg g0)) (xv6_ps0 g0 u0) c →
  ∃ cf, rtc (wp_pf_run (pstep_xv6 riscv_step))
          (wp_init (img_z (wgimg g0)) (xv6_ps0 g0 u0)) cf ∧
        prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
Proof.
  intros Hsh Hlive Hlog Hws Hdws Hphi Hcov Hprem Hbeh.
  apply (xv6_weak_robust riscv_step (img_z (wgimg g0)) (xv6_ps0 g0 u0) c);
    [|exact Hbeh].
  split; [exact Hprem|].
  rewrite /pf_violation_free_hart (wp_init_wl g0 u0 Hlog Hws Hdws).
  by eapply xv6_pf_violation_free.
Qed.

(** …and the same with the φ export produced ON THE SPOT by
    [WeakAdequacy.weak_system_adequacy_phi] from its WP premise package, so
    that the composition's only Iris-side obligation is the pool's WPs. *)
Corollary xv6_weak_robust_adequate Σ `{!riscvGpreS Σ, !weakGpreS Σ}
    `{GEN : GenId}
    (D : CPU -> gset register) (g0 : wgstate) (u0 : wlaux) (c : wpcfg pxv6)
    (Hgid : gen_id = 0%nat)
    (Hpow : wgpow g0 = true) (Hgen0 : wggen g0 = 0%nat)
    (Hlog : wglog g0 = [])
    (Hws : forall cc : CPU, wgws g0 cc = ws_init)
    (Hdws : wa_dws u0 = ws_init) :
  (∀ b, sail_shaped (riscv_step b)) →
  (forall (HR : riscvGS Σ) (HW : weakGS Σ),
     ⊢@{iPropI Σ} ([∗ set] cc ∈ (fin_to_set CPU : gset CPU),
          [∗ set] r ∈ D cc,
            reg_pointsto_at cc r (DfracOwn 1)
              (register_lookup r (wgregs g0 cc))) ∗
       ([∗ map] aa ↦ b ∈ wgimg g0, wlat_pointsto (pa_z aa) (DfracOwn 1) 0%nat b) ∗
       ([∗ set] cc ∈ (fin_to_set CPU : gset CPU), hart_view cc) ∗
       wlog_lb [] ∗
       uart_frag (wgdev g0).(duart) ∗ plic_frag (wgdev g0).(dplic) ∗
       virtio_frag (wgdev g0).(dvirtio)
       ={⊤}=∗
       ([∗ list] cc ∈ (enum CPU), WWP (LoopE gen_id cc) @ ⊤) ∗
       WWP UartLoop @ ⊤ ∗ WWP DiskLoop @ ⊤ ∗ WWP PlicLoop @ ⊤) →
  xv6_block_cover g0 u0 →
  (∀ (cb mid : wpcfg pxv6) (TS : ptraces pxv6),
     wp_behavior (pstep_xv6 riscv_step) (img_z (wgimg g0)) (xv6_ps0 g0 u0) cb →
     rtc (wp_promise_step (P := pxv6))
       (wp_init (img_z (wgimg g0)) (xv6_ps0 g0 u0)) mid →
     ptraces_of (pstep_xv6 riscv_step) TS mid cb →
     main_premises n_disk TS) →
  wp_behavior (pstep_xv6 riscv_step) (img_z (wgimg g0)) (xv6_ps0 g0 u0) c →
  ∃ cf, rtc (wp_pf_run (pstep_xv6 riscv_step))
          (wp_init (img_z (wgimg g0)) (xv6_ps0 g0 u0)) cf ∧
        prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
Proof.
  intros Hsh Hwp Hcov Hprem Hbeh.
  eapply (xv6_weak_robust_lifted gen_id g0 u0 c Hsh);
    [|exact Hlog|exact Hws|exact Hdws| |exact Hcov|exact Hprem
     |exact Hbeh].
  - split; [exact Hpow|]. by rewrite Hgen0 Hgid.
  - intros t2 g2 Hr.
    exact (proj1 (weak_system_adequacy_phi Σ (enum CPU) g0 D Hgid Hpow Hgen0
                    Hlog Hws Hwp t2 g2 Hr)).
Qed.
