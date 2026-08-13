(** * WeakComposeLang.v — L3/B5b: THE CONE-ROUTE φ-CONSUMPTION AND THE
      LIFTED COMPOSITION
      (lift stages L3 + B5b of [claude-notes/projects/weak-memory-lift.md])

    WHAT THIS FILE IS.  [WeakCompose.xv6_weak_robust] is the M6 headline
    theorem over the wp machine ([wpcfg pxv6]); [WeakAdequacy] exports φ
    ([WeakGhost.no_violation]) at every state of the [WeakLang] machine
    ([wgstate], [wprim_step]).  Seam (1) of [WeakCompose] §6 is the missing
    bridge between the two, and its ONE consumer is
    [WeakRobust.pf_violation_free_hart] — the place φ/Iris is still
    load-bearing.  This file builds the bridge in the ⇐ direction the
    consumption needs, and uses it to refute EVERY BAD EDGE of every traced
    behavior, which is what the acyclicity (and hence the robustness)
    actually needs.

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

    (2) THE pxv6 → psail PROJECTION OF A SOLO HART RUN (§3), the mirror image
        of [WeakSailCone]'s [pf_step_lift]/[hlink]: a [pf_xsolo] step of a
        HART agent projects along [WeakSailCone.prj_cfg] to a
        [WeakSailLTS2.pf_solo] step (the disk agent is inert filler
        throughout), carrying [cls_canon] and [rmw_tight] with it.  Plus THE
        BLOCK DECOMPOSITION ([xsolo_run_blocks]): a solo run between two
        [sp_m = None] points is an [rtc] of SINGLE INSTRUCTION BLOCKS
        ([xblk], the [pxv6] twin of [WeakSailLTS2.sail_block]), obtained by
        cutting at the first internal boundary and recursing.

    (3) THE SEGMENT REFINEMENT (§4).  [WeakSailCone.cone_segments2] exports a
        chain of [seg2] segments whose HART segments are boundary-to-boundary
        but possibly MANY instructions long, while one [WeakLang] hart step
        is exactly ONE instruction.  [seg2_refine] re-cuts such a chain into
        one whose hart segments are single blocks, keeping the same start,
        the same END CONFIGURATION [cf], and the same per-segment data for
        the irq and disk kinds ([seg2_fine]).  Nothing else about the chain
        moves — in particular the violation at [cf] is untouched.

    (4) THE LIFT ([wl_lift], §6) AND ITS SOUNDNESS ([wl_lift_sound]).
        [wl_lift gen segs g u] is a PREDICATE on the [WeakLang] start state
        (no successor: the successor is CONSTRUCTED by the soundness proof,
        from the [wrun] that [WeakSailLTS2.sail_block_wrun] reconstructs).
        Per segment it carries exactly the DEVICE-SEAM residue and nothing
        else:
          - [SegHart]: [WeakSailLTS2.oracle_consistent] of that hart's stream
            against [wgdev g], plus a continuation quantified over the
            [wrun]s whose [WeakLang] successor MATCHES the segment's target;
          - [SegIrq]: the wire fact — the delivered value is
            [bool_to_bit (dev_seip (wgdev g) i)] — and the continuation;
          - [SegDisk]: [wa_dd u = wgdev g] (the M5 device-view residue) and,
            for the segment's OWN [(d', w)], the [WeakLang] disk arm at the
            TRUE flat memory (premise (P4): [pstep_xv6]'s burst arm is
            existential in the memory, [WeakLang.wdisk_step] is not).
        NO [hart_dev_seam] CONJUNCT: because the successor is built from the
        chosen [wrun], the post-block fabric IS [wm_dev s'] by construction.
        [wl_lift_sound] turns such a chain into an
        [rtc erased_step] of [WeakLang.weak_riscv_lang] over the standard
        pool ([wpool gen = WeakAdequacy.wcpu_pool (enum CPU)]) ending at a
        state [g'] with [cf = wl_cfg g' u'].  NO UART SEGMENT and NO POWER
        SEGMENT, deliberately: the wp machine has no uart agent at all, and
        the power arm is vacuous at a pinned generation ([wthread_live] is an
        invariant of every segment).

    (5) THE φ TRANSPORT ([wl_no_hart_violation], §7).  φ at the reached
        [WeakLang] state refutes a HART-AUTHORED, HART-OBSERVED violation at
        the corresponding pf configuration — which, since the Layer-1 fix of
        §B, is the only kind [WeakRobust.violation_hart] has.  The transport
        is SYNTACTIC, and that is L0(c)'s payoff: [WeakRobustMain.pub_of] IS
        [WeakMem.wpublished] at the configuration's log, the very predicate
        [no_violation] is stated with, and [WeakRobust.obs_flr] IS the
        agent's [coh].  Nothing is renamed.

    (6) THE BAD-EDGE REFUTATION ([xv6_no_bad_edge], §9) and THE UPDATED
        COMPOSITION ([xv6_weak_robust_lifted] / [xv6_weak_robust_adequate],
        §10).  A bad edge would give (via [bad_wf], [cone_segments2], the
        refinement and the lift) a [WeakLang] run whose final state violates
        φ; so there is NO bad edge, so [gdep2_acyclic_bad_free] applies and
        the robustness follows by [robust_main_no_bad] — [WeakRobustMain]'s
        [robust_main] with [pf_violation_free_hart] replaced by "no bad
        edge", proved here over a generic [pstep] so that
        [WeakRobustMain.v] is untouched.  [xv6_weak_robust_adequate] takes
        [WeakAdequacy]'s own WP premise package and runs
        [weak_system_adequacy_phi] on the spot, so the composition's only
        Iris-side obligation is the thread pool's WPs.

    ------------------------------------------------------------------------
    §B  THE RESIDUE, STATED AS A PREMISE — and the two FINDINGS behind its
    present shape.

    (A) [cone_liftable] (§9) — THE MMIO/M5 SEAM, IN PER-DECOMPOSITION FORM.
        It says: for the segment chain a MINIMAL BAD EDGE's cone decomposes
        into, the [WeakLang] machine can follow along — i.e. [wl_lift] holds
        at the initial state.  It is a named definition, consumed in exactly
        one place, and NOT dressed up as a theorem.  What it really assumes
        is only what §A(4) lists: per hart block an [oracle_consistent]
        stream, per delivery the plic wire, per disk group the device view
        and the true-memory [wdisk_step].  Everything else about the
        correspondence — the log, the registers, the [wstate]s, the agent
        vector — is DERIVED (that is what [wl_lift_sound] is).

    (B) [xv6_block_cover] IS REFUTABLE — THE FINDING THAT RETIRED THE OLD
        ROUTE (2026-08-13).  The previous revision of this file consumed φ
        through a premise [xv6_block_cover g0 u0]: "any [wp_pf_run]-reachable
        violating configuration has a BLOCK-ATOMIC witness of the same
        violation".  That premise is FALSE for xv6.  Counterexample shape:
        hart [i] does a plain store [m] to an owned, unpublished byte; then a
        [fence rw,w] (which sets [w_relp], so [i]'s NEXT store publishes
        [m]); then it BEGINS a store instruction whose page walk CASes a PTE
        (the fork's atomic A/D update, a fused mid-block [LRmw] of class
        [WCexcl]) and the pf run switches away — the CAS is in the log, the
        publishing data store is not.  Hart [j] then reads that dangling CAS,
        branches on the A bit, and racily reads [m].  At EVENT granularity
        this is pf-reachable and [violates_at] holds; in ANY
        instruction-atomic ([WeakLang]) run the author's instruction is
        atomic, so either the CAS is absent (j branches the other way) or the
        [WCrel] data store landed with it (m is published) — no block-atomic
        witness exists.  The coarse premise is therefore replaced by the cone
        route of §A: the violating configuration is not an arbitrary
        reachable one but the one the EXHIBIT builds, and
        [WeakSailCone.cone_segments2] hands it over already segmented.

    (C) THE AGENT QUANTIFIER — FOUND HERE, FIXED IN LAYER 1, GONE FROM THE
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
        THE FIX belonged in Layer 1 and has landed there:
          (i)   [WeakRobust.violation_hart nh] (= [violation] with
                [WeakMem.tid_hart nh (wm_tid m)] and [tid_hart nh (Some j)])
                and [WeakRobust.pf_violation_free_hart nh];
          (ii)  [WeakRobustMain.bad] carries the reader's bound [e2.1 < nh]
                beside the author's [e1.1 < nh], and [bad_edge_violates]
                concludes [violation_hart nh];
          (iii) [no_bad_edge] / [gdep2_acyclic_main] / [robust_main] and
                [WeakCompose.m6_side_conditions] all consume the [_hart] form.
        §9 below therefore closes with residue (A) alone: the two indices
        arrive bounded by [n_disk = NCPU] and [nat_to_fin] hands the
        transport its [CPU]s.

    ------------------------------------------------------------------------
    §C  THE cls_canon / rmw_tight RESIDUE (L2's header) — PAID, NOT ASSUMED.

    [WeakPromiseBridge.wp_pf_step] carries a message's [wm_class] as a FREE
    BINDER, while [WeakInterp.wrun] COMPUTES it; L2 records the gap as
    [WeakSailLTS2.cls_canon] (and [rmw_tight] for the exclusive read window),
    both side conditions of [pf_solo] and hence of [sail_block].  Neither is
    a premise HERE: [WeakSailCone.pf_xsolo] already carries both at every
    step of every segment it exports ([xcls_canon] / [xrmw_tight]), and §3's
    projection transports them verbatim to the [psail] side.  On the disk
    side the classes are canonical by CONSTRUCTION ([wmsgs_of_map]'s messages
    are [WCplain], and a disk agent's [w_relp] is always [false] —
    [WeakSailCone.disk_relp]).  [WeakCompose.v] is UNCHANGED by this file.

    ------------------------------------------------------------------------
    §D  THE PREMISE LIST OF [xv6_weak_robust_adequate] — the composition's
    assumptions inventory (against [WeakCompose] §6's):

      1. [∀ b, sail_shaped (riscv_step b)] — seam (6), unchanged.
      2. THE FRESH ERA: [gen_id = 0], [wgpow g0 = true], [wggen g0 = 0],
         [wglog g0 = []], [∀ c, wgws g0 c = ws_init], [wa_dws u0 = ws_init]
         — literally [weak_system_adequacy_phi]'s, plus the disk agent's own
         [wstate] (the wp machine has an agent [WeakLang] does not).
      3. THE ADEQUACY WP PACKAGE — the pool's WPs from the initial resources,
         verbatim [WeakAdequacy.weak_system_adequacy_phi]'s premise.
      4. [img_total (img_z (wgimg g0))] — the boot image covers every byte
         (discharged by [WeakAdequacy]'s [wlat_init]); consumed by the cone's
         reader-tail completion.
      5. The per-traced-bundle static package: [main_premises n_disk TS]
         (= [WeakCompose] §6 (3), with [bad] now bounding the READER's agent
         index too) AND [xv6_cone_premises TS] — [Hcq] (a cross-edge source's
         post-state is quiet), [Hres] ([sail_shaped]/[sail_live]/oracle
         consistency of every trace record's residual), [Hirqb] (a delivery
         has a boundary pre-state) and [Hcls] (a logged message carries its
         author's computed class), stated exactly as [WeakSailCone] §11-§12's
         section context.
      6. [cone_liftable] — residue (A) of §B, and THE ONLY LIFT RESIDUE:
         the MMIO/M5 device seam, per decomposition.
      7. The 5 rv64d baseline axioms.  NO functional extensionality, NO
         classical axiom.

    WHAT IS GONE relative to [WeakCompose] §6: seam (1a) (the ⇐ hart
    direction — L2 built it, §6 consumes it), (1b) (interleaving regrouping —
    the cone route replaced the block-atomicity premise outright, §B(B)),
    (1c) (device and power arms — the plic and disk arms are built; uart and
    power are shown unnecessary rather than assumed), and seam (2)
    ([pf_violation_free_hart] itself, which is not merely discharged but
    BYPASSED: its one consumer, the bad-edge refutation, is proved directly).

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
From xv6iris Require Import WeakRobust WeakRobustTrace WeakRobustGraph
                            WeakRobustProv WeakRobustLin WeakRobustOrd
                            WeakRobustSer WeakRobustAcyc WeakRobustAcyc2
                            WeakRobustSim WeakRobustMain WeakRobustBlocks
                            WeakRobustCone.
From xv6iris Require Import WeakInterp WeakInterpProj WeakSailLTS WeakSailLTS2.
From xv6iris Require Import WeakSailComplete WeakSailCone.
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

(** A list that agrees with another off [i] and holds [x] at [i] IS the
    insert — the shape every "the segment moved only agent [i]" argument
    below reassembles through. *)
Lemma list_eq_insert {A} (l l' : list A) (i : nat) (x : A) :
  l' !! i = Some x → is_Some (l !! i) →
  (∀ j, j ≠ i → l' !! j = l !! j) → l' = <[i := x]> l.
Proof.
  intros Hi Hs Hne. apply list_eq. intros k.
  destruct (decide (k = i)) as [->|Hk].
  - rewrite Hi. symmetry. destruct Hs as (y & Hy).
    exact (lookup_insert_self l i x y Hy).
  - by rewrite (lookup_insert_other l i x k Hk) (Hne k Hk).
Qed.

Lemma map_fmap_eq {A B} (f : A → B) (l : list A) : map f l = f <$> l.
Proof. by induction l as [|x l IH]; simpl; [|rewrite IH]. Qed.

Lemma fmap_ext_l {A B} (f h : A → B) (l : list A) :
  (∀ x, f x = h x) → f <$> l = h <$> l.
Proof.
  intros H. induction l as [|x l IH]; [done|].
  by rewrite !fmap_cons H IH.
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

(** The HART-ONLY configuration, at the [psail] program type. *)
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

(** The corresponding configuration carries no promises — every agent of it
    is built with [∅]. *)
Lemma wl_cfg_no_promises g u : no_promises (wl_cfg g u).
Proof.
  intros j ag Hj. rewrite wl_cfg_alt in Hj. cbn [pc_ags] in Hj.
  destruct (decide (j < NCPU)%nat) as [Hlt|Hge].
  - rewrite lookup_app_l in Hj; [|by rewrite wl_cfg_harts_len].
    rewrite list_lookup_fmap in Hj.
    destruct (enum CPU !! j) as [c|]; simplify_eq/=; done.
  - rewrite lookup_app_r in Hj; [|by rewrite wl_cfg_harts_len; lia].
    rewrite wl_cfg_harts_len in Hj.
    destruct (j - NCPU)%nat as [|k]; simpl in Hj;
      [by simplify_eq|by destruct k; simplify_eq].
Qed.

Lemma pf_run_no_promises (c c' : wpcfg pxv6) :
  rtc (wp_pf_run (pstep_xv6 riscv_step)) c c' → no_promises c → no_promises c'.
Proof.
  induction 1 as [|x y z (i & l & Hs) _ IH]; [done|].
  intros Hnp. apply IH. by eapply wp_pf_step_no_promises.
Qed.

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

(** The three [wlaux] updates: a hart's device stream advances, a hart's
    interrupt stream advances, the disk's own fabric/[wstate] are replaced. *)
Definition wl_dstr (cpu : CPU) (dtl : dstream) (u : wlaux) : wlaux :=
  WLAux (cupd cpu dtl (wa_dstr u)) (wa_iq u) (wa_dd u) (wa_dws u).

Definition wl_iq (cpu : CPU) (iq' : istream) (u : wlaux) : wlaux :=
  WLAux (wa_dstr u) (cupd cpu iq' (wa_iq u)) (wa_dd u) (wa_dws u).

Definition wl_dk (d' : dev_state) (ws' : wstate) (u : wlaux) : wlaux :=
  WLAux (wa_dstr u) (wa_iq u) d' ws'.

(** REASSEMBLY, for a step that moved ONE HART: the configuration whose
    agent [cpu] has been replaced IS the corresponding configuration of the
    updated [WeakLang] state.  (The old file's [wl_cfg_hart_update], with the
    log freed — a hart block appends to it.) *)
Lemma wl_cfg_hart_upd g u cpu (g' : wgstate) (u' : wlaux) (st' : psail)
    (ws' : wstate) :
  wgimg g' = wgimg g → wa_dd u' = wa_dd u → wa_dws u' = wa_dws u →
  (∀ c, c ≠ cpu → hag g' u' c = hag g u c) →
  hag g' u' cpu = WPAgent st' ws' ∅ →
  WPCfg (pc_img (wl_cfg g u)) (wglog g')
    (<[fin_to_nat cpu := WPAgent (PHart st') ws' (∅ : gset nat)]>
       (pc_ags (wl_cfg g u)))
  = wl_cfg g' u'.
Proof.
  intros Himg Hdd Hdws Hne Hcpu.
  rewrite !wl_cfg_alt. cbn [pc_img pc_log pc_ags].
  rewrite Himg /dkag Hdd Hdws. f_equal.
  rewrite insert_app_l; [|rewrite wl_cfg_harts_len; apply fin_to_nat_lt].
  f_equal.
  have Hx : WPAgent (PHart st') ws' (∅ : gset nat) = lift_ag (hag g' u' cpu)
    by rewrite Hcpu.
  rewrite Hx.
  apply (cpu_fmap_insert (λ c, lift_ag (hag g u c))
           (λ c, lift_ag (hag g' u' c)) cpu).
  intros c Hc. by rewrite (Hne c Hc).
Qed.

(** …and its DISK twin. *)
Lemma wl_cfg_disk_upd g u (g' : wgstate) (u' : wlaux) (st' : pxv6)
    (ws' : wstate) :
  wgimg g' = wgimg g →
  (∀ c, hag g' u' c = hag g u c) →
  dkag u' = WPAgent st' ws' ∅ →
  WPCfg (pc_img (wl_cfg g u)) (wglog g')
    (<[n_disk := WPAgent st' ws' (∅ : gset nat)]> (pc_ags (wl_cfg g u)))
  = wl_cfg g' u'.
Proof.
  intros Himg Hne Hdk.
  rewrite !wl_cfg_alt. cbn [pc_img pc_log pc_ags].
  rewrite Himg. f_equal.
  have Hl : length ((λ c, lift_ag (hag g u c)) <$> enum CPU) = n_disk
    by rewrite wl_cfg_harts_len.
  rewrite -Hl insert_app_last -Hdk.
  f_equal. apply fmap_ext_l. intros c. by rewrite Hne.
Qed.

(* ====================================================================== *)
(** ** 3. pxv6 ⇒ psail: PROJECTING A SOLO HART RUN, AND CUTTING IT INTO
       INSTRUCTION BLOCKS

    [WeakSailCone.pf_step_lift] moves a [psail] step to [pxv6]; this is the
    mirror.  [WeakSailCone.prj_cfg] is the projection (the disk agent gets an
    inert filler state, never stepped and never read), and a [pf_xsolo] step
    of a HART agent projects to a [WeakSailLTS2.pf_solo] step — with
    [cls_canon]/[rmw_tight] carried across, since [prj_cfg] preserves the
    image, the log and every agent's [wstate].

    Then [xblk] — the [pxv6] twin of [WeakSailLTS2.sail_block] — and the
    decomposition of a boundary-to-boundary solo run into [xblk]s. *)

Section prj.
  Context (next : bool → M unit).

  Definition xhart (i : agent) (c : wpcfg pxv6) : Prop :=
    ∃ ag q, pc_ags c !! i = Some ag ∧ pa_st ag = PHart q.

  Definition xat_bnd (i : agent) (c : wpcfg pxv6) : Prop :=
    ∃ ag q, pc_ags c !! i = Some ag ∧ pa_st ag = PHart q ∧ sp_m q = None.

  Definition xin_blk (i : agent) (c : wpcfg pxv6) : Prop :=
    ∃ ag q, pc_ags c !! i = Some ag ∧ pa_st ag = PHart q ∧ sp_m q ≠ None.

  Definition xpf_in_blk (i : agent) (c c' : wpcfg pxv6) : Prop :=
    xin_blk i c ∧ pf_xsolo next i c c'.

  (** ONE INSTRUCTION BLOCK at [pxv6]: boundary, one step that loads the
      instruction, its events, boundary — no interior boundary. *)
  Definition xblk (i : agent) (c c' : wpcfg pxv6) : Prop :=
    xat_bnd i c ∧ xat_bnd i c' ∧
    ∃ c0, pf_xsolo next i c c0 ∧ rtc (xpf_in_blk i) c0 c'.

  Lemma xat_bnd_hart i c : xat_bnd i c → xhart i c.
  Proof. intros (ag & q & H1 & H2 & _). by exists ag, q. Qed.

  Lemma xin_blk_hart i c : xin_blk i c → xhart i c.
  Proof. intros (ag & q & H1 & H2 & _). by exists ag, q. Qed.

  Lemma xhart_cases i c : xhart i c → xat_bnd i c ∨ xin_blk i c.
  Proof.
    intros (ag & q & Hlk & Hst). destruct (sp_m q) as [m|] eqn:Hm.
    - right. exists ag, q. split_and!; [done|done|by rewrite Hm].
    - left. by exists ag, q.
  Qed.

  Lemma xat_bnd_not_in i c : xat_bnd i c → xin_blk i c → False.
  Proof.
    intros (ag & q & Hlk & Hst & Hm) (ag' & q' & Hlk' & Hst' & Hm').
    apply Hm'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    rewrite Hst in Hst'. by injection Hst' as <-.
  Qed.

  Lemma prj_lookup (q0 : psail) (i : agent) (c : wpcfg pxv6) ag :
    pc_ags c !! i = Some ag → pc_ags (prj_cfg q0 c) !! i = Some (prj_ag q0 ag).
  Proof. intros H. by rewrite /prj_cfg /= list_lookup_fmap H. Qed.

  (** SPECIES IS PRESERVED: a solo step of a hart agent leaves a hart. *)
  Lemma pf_xsolo_hart (i : agent) (c c' : wpcfg pxv6) :
    xhart i c → pf_xsolo next i c c' → xhart i c'.
  Proof.
    intros (agx & qx & Hax & Hstx) (l & Hstep & _ & _).
    destruct Hstep as
      [cfg ag st' Hlk Hps
      |cfg ag aq lat base tvs st' Hlk Hps Hr
      |cfg ag rl base data kk st' Hlk Hps Hne
      |cfg ag aq rl base tvs data kk st' Hlk Hps Hne Hlen Hr He
      |cfg ag pr pw sr sw st' Hlk Hps];
      simpl in Hax; rewrite Hlk in Hax; injection Hax as <-;
      rewrite Hstx /= in Hps;
      (destruct st' as [q'|dd pend]; [|done]);
      (eexists _, q'; simpl; split; [by eapply lookup_insert_self|done]).
  Qed.

  Lemma pf_xsolo_run_hart (i : agent) (c c' : wpcfg pxv6) :
    xhart i c → rtc (pf_xsolo next i) c c' → xhart i c'.
  Proof.
    intros Hh Hrun. revert Hh. induction Hrun as [|x y z Hxy _ IH]; [done|].
    intros Hh. apply IH. by eapply pf_xsolo_hart.
  Qed.

  (** THE STEP PROJECTION. *)
  Lemma pf_xsolo_prj (q0 : psail) (i : agent) (c c' : wpcfg pxv6) :
    xhart i c → pf_xsolo next i c c' →
    xhart i c' ∧ pf_solo next i (prj_cfg q0 c) (prj_cfg q0 c').
  Proof.
    intros (agx & qx & Hax & Hstx) (l & Hstep & Hcls & Hrmw).
    destruct Hstep as
      [cfg ag st' Hlk Hps
      |cfg ag aq lat base tvs st' Hlk Hps Hr
      |cfg ag rl base data kk st' Hlk Hps Hne
      |cfg ag aq rl base tvs data kk st' Hlk Hps Hne Hlen Hr He
      |cfg ag pr pw sr sw st' Hlk Hps];
      simpl in Hax; rewrite Hlk in Hax; injection Hax as <-;
      rewrite Hstx /= in Hps;
      (destruct st' as [q'|dd pend]; [|done]);
      (have Hlks : pc_ags (prj_cfg q0 cfg) !! i = Some (prj_ag q0 ag)
         by apply prj_lookup);
      (have Hlt : (i < length (pc_ags cfg))%nat
         by exact (lookup_lt_Some _ _ _ Hlk));
      rewrite /prj_cfg; cbn [pc_img pc_log pc_ags];
      rewrite list_fmap_insert.
    - split.
      { exists (WPAgent (PHart q') (pa_ws ag) (pa_prom ag)), q'. simpl.
        split; [by eapply lookup_insert_self|done]. }
      exists WeakPromise.LSilent. split_and!.
      + apply (PFSilent (sail_step_ni next) i (prj_cfg q0 cfg)
                 (prj_ag q0 ag) q' Hlks).
        rewrite /prj_ag /= Hstx. exact Hps.
      + intros ag2 msg Hag2 Heq. simpl in Heq.
        by destruct (app_snoc_absurd _ _ Heq).
      + exact I.
    - split.
      { exists (WPAgent (PHart q') (load_post_run (pa_ws ag) aq base tvs.*1)
                  (pa_prom ag)), q'. simpl.
        split; [by eapply lookup_insert_self|done]. }
      exists (WeakPromise.LLoad aq lat base tvs). split_and!.
      + apply (PFLoad (sail_step_ni next) i (prj_cfg q0 cfg)
                 (prj_ag q0 ag) aq lat base tvs q' Hlks);
          [rewrite /prj_ag /= Hstx; exact Hps|exact Hr].
      + intros ag2 msg Hag2 Heq. simpl in Heq.
        by destruct (app_snoc_absurd _ _ Heq).
      + exact I.
    - split.
      { eexists _, q'. simpl. split; [by eapply lookup_insert_self|done]. }
      exists (WeakPromise.LStore rl base data). split_and!.
      + apply (PFStore (sail_step_ni next) i (prj_cfg q0 cfg)
                 (prj_ag q0 ag) rl base data kk q' Hlks);
          [rewrite /prj_ag /= Hstx; exact Hps|exact Hne].
      + intros ag2 msg Hag2 Heq. simpl in Heq, Hag2.
        rewrite Hlks in Hag2. injection Hag2 as <-.
        exact (Hcls ag msg Hlk Heq).
      + exact I.
    - split.
      { eexists _, q'. simpl. split; [by eapply lookup_insert_self|done]. }
      exists (WeakPromise.LRmw aq rl base tvs data). split_and!.
      + apply (PFRmw (sail_step_ni next) i (prj_cfg q0 cfg)
                 (prj_ag q0 ag) aq rl base tvs data kk q' Hlks);
          [rewrite /prj_ag /= Hstx; exact Hps|exact Hne|exact Hlen
          |exact Hr|exact He].
      + intros ag2 msg Hag2 Heq. simpl in Heq, Hag2.
        rewrite Hlks in Hag2. injection Hag2 as <-.
        exact (Hcls ag msg Hlk Heq).
      + intros ag2 Hag2. simpl in Hag2. rewrite Hlks in Hag2.
        injection Hag2 as <-. exact (Hrmw ag Hlk).
    - split.
      { eexists _, q'. simpl. split; [by eapply lookup_insert_self|done]. }
      exists (WeakPromise.LFence pr pw sr sw). split_and!.
      + apply (PFFence (sail_step_ni next) i (prj_cfg q0 cfg)
                 (prj_ag q0 ag) pr pw sr sw q' Hlks).
        rewrite /prj_ag /= Hstx. exact Hps.
      + intros ag2 msg Hag2 Heq. simpl in Heq.
        by destruct (app_snoc_absurd _ _ Heq).
      + exact I.
  Qed.

  Lemma pf_xsolo_run_prj (q0 : psail) (i : agent) (c c' : wpcfg pxv6) :
    xhart i c → rtc (pf_xsolo next i) c c' →
    xhart i c' ∧ rtc (pf_solo next i) (prj_cfg q0 c) (prj_cfg q0 c').
  Proof.
    intros Hh Hrun. revert Hh. induction Hrun as [x|x y z Hxy _ IH]; intros Hh.
    { split; [done|apply rtc_refl]. }
    destruct (pf_xsolo_prj q0 i x y Hh Hxy) as (Hh' & Hs).
    destruct (IH Hh') as (Hh'' & Hrs).
    split; [done|by eapply rtc_l].
  Qed.

  Lemma xat_bnd_prj (q0 : psail) i c :
    xat_bnd i c → at_boundary i (prj_cfg q0 c).
  Proof.
    intros (ag & q & Hlk & Hst & Hm).
    exists (prj_ag q0 ag). split; [by apply prj_lookup|].
    by rewrite /prj_ag /= Hst.
  Qed.

  Lemma xin_blk_prj (q0 : psail) i c :
    xin_blk i c → in_block i (prj_cfg q0 c).
  Proof.
    intros (ag & q & Hlk & Hst & Hm).
    exists (prj_ag q0 ag). split; [by apply prj_lookup|].
    by rewrite /prj_ag /= Hst.
  Qed.

  Lemma xblk_run i c c' : xblk i c c' → rtc (pf_xsolo next i) c c'.
  Proof.
    intros (_ & _ & c0 & H0 & Hrtc). eapply rtc_l; [exact H0|].
    clear H0. induction Hrtc as [|x y z [_ Hs] _ IH]; [apply rtc_refl|].
    by eapply rtc_l.
  Qed.

  Lemma xpf_in_blk_run_prj (q0 : psail) (i : agent) (c c' : wpcfg pxv6) :
    xhart i c → rtc (xpf_in_blk i) c c' →
    rtc (pf_in_block next i) (prj_cfg q0 c) (prj_cfg q0 c').
  Proof.
    intros Hh Hrtc. revert Hh.
    induction Hrtc as [x|x y z [Hin Hxy] _ IH]; intros Hh.
    { apply rtc_refl. }
    destruct (pf_xsolo_prj q0 i x y Hh Hxy) as (Hh' & Hs).
    eapply rtc_l; [split; [by apply xin_blk_prj|exact Hs]|].
    exact (IH Hh').
  Qed.

  (** THE BLOCK, PROJECTED — a [WeakSailLTS2.sail_block]. *)
  Lemma xblk_prj (q0 : psail) i c c' :
    xblk i c c' → sail_block next i (prj_cfg q0 c) (prj_cfg q0 c').
  Proof.
    intros (Hb & Hb' & c0 & H0 & Hrtc).
    split_and!; [by apply xat_bnd_prj|by apply xat_bnd_prj|].
    destruct (pf_xsolo_prj q0 i c c0 (xat_bnd_hart i c Hb) H0) as (Hh0 & Hs0).
    exists (prj_cfg q0 c0). split; [exact Hs0|].
    exact (xpf_in_blk_run_prj q0 i c0 c' Hh0 Hrtc).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** THE DECOMPOSITION.  Cut a solo run at the FIRST interior boundary and
      recurse: what precedes the cut is one [xblk], what follows is shorter. *)

  Lemma xblk_split (i : agent) (n : nat) (c c' : wpcfg pxv6) :
    relations.nsteps (pf_xsolo next i) n c c' → xhart i c → xat_bnd i c' →
    ∃ (k : nat) (ck : wpcfg pxv6),
      (k ≤ n)%nat ∧ rtc (xpf_in_blk i) c ck ∧ xat_bnd i ck ∧
      relations.nsteps (pf_xsolo next i) (n - k) ck c'.
  Proof.
    revert c. induction n as [|n IH]; intros c Hst Hh Hb.
    - exists 0%nat, c'. inversion Hst; subst.
      split_and!; [lia|apply rtc_refl|done|by constructor].
    - destruct (xhart_cases i c Hh) as [Hbc|Hic].
      { exists 0%nat, c. split_and!; [lia|apply rtc_refl|done|].
        by rewrite Nat.sub_0_r. }
      inversion Hst as [|n0 x y z Hxy Hyz Hn0 Hx Hz]; subst.
      destruct (IH y Hyz (pf_xsolo_hart i c y Hh Hxy) Hb)
        as (k & ck & Hk & Hrun & Hbk & Hrest).
      exists (S k), ck. split_and!; [lia| |done|].
      + eapply rtc_l; [split; [exact Hic|exact Hxy]|exact Hrun].
      + by replace (S n - S k)%nat with (n - k)%nat by lia.
  Qed.

  Lemma xsolo_blocks (i : agent) (n : nat) :
    ∀ (m : nat) (c c' : wpcfg pxv6), (m ≤ n)%nat →
      relations.nsteps (pf_xsolo next i) m c c' → xat_bnd i c → xat_bnd i c' →
      rtc (xblk i) c c'.
  Proof.
    induction n as [|n IH]; intros m c c' Hm Hst Hb Hb'.
    - assert (m = 0%nat) as -> by lia. inversion Hst; subst. apply rtc_refl.
    - destruct m as [|m].
      { inversion Hst; subst. apply rtc_refl. }
      inversion Hst as [|n0 x y z Hxy Hyz Hn0 Hx Hz]; subst.
      destruct (xblk_split i m y c' Hyz
                  (pf_xsolo_hart i c y (xat_bnd_hart i c Hb) Hxy) Hb')
        as (k & ck & Hk & Hrun & Hbk & Hrest).
      eapply rtc_l; [|eapply (IH (m - k)%nat ck c'); [lia|exact Hrest|done|done]].
      split_and!; [exact Hb|exact Hbk|]. by exists y.
  Qed.

  Lemma xsolo_run_blocks (i : agent) (c c' : wpcfg pxv6) :
    rtc (pf_xsolo next i) c c' → xat_bnd i c → xat_bnd i c' →
    rtc (xblk i) c c'.
  Proof.
    intros Hrun Hb Hb'. apply rtc_nsteps in Hrun as (n & Hn).
    by eapply (xsolo_blocks i n n).
  Qed.

End prj.

(* ====================================================================== *)
(** ** 4. THE SEGMENT REFINEMENT

    [WeakSailCone.cone_segments2]'s hart segments run from boundary to
    boundary but may cover MANY instructions; one [WeakLang] hart step is
    exactly ONE.  [seg2_refine] re-cuts a chain so that every hart segment is
    a single [xblk], leaving the chain's start, its END configuration and the
    irq/disk segments alone.  [seg2_fine] is the resulting per-segment data —
    for harts it is SHARPER than [seg2_ok] in the block dimension and drops
    [seg2_ok]'s parked-fence conjunct, which the lift never reads (the
    corresponding state is pinned by [wl_cfg] anyway). *)

Definition seg2_fine (s : seg2) : Prop :=
  match s with
  | SegHart i c c' => xblk riscv_step i c c'
  | SegIrq i c c' => seg2_irq_ok i c c'
  | SegDisk i c c' => seg2_disk_ok i c c'
  end.

Lemma xblk_chain (i : agent) (c c' : wpcfg pxv6) :
  rtc (xblk riscv_step i) c c' →
  ∃ segs, chained2 segs c c' ∧ Forall seg2_fine segs.
Proof.
  induction 1 as [x|x y z Hxy _ (segs & Hch & Hall)].
  - exists []. split; [done|constructor].
  - exists (SegHart i x y :: segs). split; [by split|by constructor].
Qed.

Lemma seg2_hart_refine (i : agent) (c c' : wpcfg pxv6) :
  seg2_hart_ok i c c' →
  ∃ segs, chained2 segs c c' ∧ Forall seg2_fine segs.
Proof.
  intros ((ag & q & Hlk & Hst) & Hb & Hb' & Hrun).
  have Hp : pbnd (pa_st ag) := Hb ag Hlk.
  rewrite Hst in Hp. destruct Hp as (Hm & _).
  have Hbc : xat_bnd i c by exists ag, q.
  destruct (pf_xsolo_run_hart riscv_step i c c' (xat_bnd_hart i c Hbc) Hrun)
    as (ag2 & q2 & Hlk2 & Hst2).
  have Hp2 : pbnd (pa_st ag2) := Hb' ag2 Hlk2.
  rewrite Hst2 in Hp2. destruct Hp2 as (Hm2 & _).
  have Hbc' : xat_bnd i c' by exists ag2, q2.
  exact (xblk_chain i c c' (xsolo_run_blocks riscv_step i c c' Hrun Hbc Hbc')).
Qed.

Lemma seg2_refine (segs : list seg2) (c cf : wpcfg pxv6) :
  chained2 segs c cf → Forall seg2_ok segs →
  ∃ segs', chained2 segs' c cf ∧ Forall seg2_fine segs'.
Proof.
  revert c. induction segs as [|s segs IH]; intros c Hch Hall.
  { exists []. simpl in Hch. split; [by simpl|constructor]. }
  apply Forall_cons in Hall as [Hok Hall].
  destruct s as [i c1 c2|i c1 c2|i c1 c2]; simpl in Hch, Hok;
    destruct Hch as (Hsrc & Hch); subst c1;
    destruct (IH c2 Hch Hall) as (segs' & Hch' & Hall').
  - destruct (seg2_hart_refine i c c2 Hok) as (sh & Hchh & Hallh).
    exists (sh ++ segs'). split.
    + by eapply chained2_app; [exact Hchh|exact Hch'].
    + by apply Forall_app.
  - exists (SegIrq i c c2 :: segs'). split; [by split|by constructor].
  - exists (SegDisk i c c2 :: segs'). split; [by split|by constructor].
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
(** ** 6. THE LIFT, AND ITS SOUNDNESS

    [wl_lift gen segs g u] is the per-segment DEVICE-SEAM residue, and
    nothing else: the successor [WeakLang] state is never named by it, it is
    constructed by [wl_lift_sound] out of the [wrun] that
    [WeakSailLTS2.sail_block_wrun] reconstructs from the segment.  The
    continuations are quantified over exactly the successors that MATCH the
    segment's target configuration — which is what makes the residue
    per-decomposition rather than global. *)

Fixpoint wl_lift (gen : nat) (segs : list seg2) (g : wgstate) (u : wlaux)
    : Prop :=
  match segs with
  | [] => True
  | SegHart i c c' :: rest =>
      ∃ cpu : CPU, i = fin_to_nat cpu ∧
        (** the MMIO seam: this hart's oracle stream is what the fabric
            [wgdev g] answers, along every path of every instruction *)
        (∀ b, oracle_consistent (wgdev g) (riscv_step b) (wa_dstr u cpu)) ∧
        (∀ (tick : bool) (x : unit) (s' : wmstate) (dtl : dstream),
           wrun (Some i) (riscv_step tick) (whart_view g cpu) x s' →
           wl_cfg (whart_write g cpu s') (wl_dstr cpu dtl u) = c' →
           wl_lift gen rest (whart_write g cpu s') (wl_dstr cpu dtl u))
  | SegIrq i c c' :: rest =>
      ∃ cpu : CPU, i = fin_to_nat cpu ∧
        (** the PLIC WIRE: the delivered value is the fabric's [seip] pin *)
        (∀ (v : type_of_register sig_seip) (iq' : istream),
           wa_iq u cpu = v :: iq' →
           v = bool_to_bit (dev_seip (wgdev g) (fin_to_nat cpu)) ∧
           wl_lift gen rest (wplic_write g cpu) (wl_iq cpu iq' u))
  | SegDisk i c c' :: rest =>
      i = n_disk ∧
      (** the M5 DEVICE VIEW: the pf disk agent's fabric is the machine's *)
      wa_dd u = wgdev g ∧
      (∀ (d' : dev_state) (w : gmap Arch.pa (bv 8)) (ws' : wstate),
         pc_ags c' !! n_disk = Some (WPAgent (PDisk d' []) ws' ∅) →
         pc_log c' = wglog g ++ wmsgs_of_map w →
         (∃ mem, wdisk_step (wgdev g) mem d' w) →
         (** …and the burst holds at the TRUE flat memory (P4) *)
         wdisk_step (wgdev g) (wflat (wgimg g) (wglog g)) d' w ∧
         wl_lift gen rest (wdisk_write g d' w) (wl_dk d' ws' u))
  end.

Lemma wpcfg_eq {P : Type} (c1 c2 : wpcfg P) :
  pc_img c1 = pc_img c2 → pc_log c1 = pc_log c2 → pc_ags c1 = pc_ags c2 →
  c1 = c2.
Proof. destruct c1, c2; simpl; by intros -> -> ->. Qed.

Theorem wl_lift_sound (gen : nat) (Hsh : ∀ b, sail_shaped (riscv_step b))
    (segs : list seg2) :
  ∀ (g : wgstate) (u : wlaux) (cf : wpcfg pxv6),
    chained2 segs (wl_cfg g u) cf → Forall seg2_fine segs →
    wthread_live g gen → wl_lift gen segs g u →
    ∃ g' u', cf = wl_cfg g' u' ∧ wthread_live g' gen ∧
             rtc (@erased_step weak_riscv_lang) (wpool gen, g) (wpool gen, g').
Proof.
  induction segs as [|s segs IH]; intros g u cf Hch Hall Hlive Hlift.
  { simpl in Hch. exists g, u. split_and!; [by rewrite Hch|done|apply rtc_refl]. }
  apply Forall_cons in Hall as [Hfine Hall].
  destruct s as [i c c'|i c c'|i c c']; simpl in Hch, Hfine, Hlift;
    destruct Hch as (Hsrc & Hch); subst c.
  - (* ---------------- ONE HART INSTRUCTION BLOCK ---------------- *)
    destruct Hlift as (cpu & -> & Hoc & Hcont).
    set (q0 := PSail None (wgregs g cpu) (wa_dstr u cpu) None (wa_iq u cpu)).
    have Hlkp : pc_ags (prj_cfg q0 (wl_cfg g u)) !! (fin_to_nat cpu)
              = Some (WPAgent (PSail None (wgregs g cpu) (wa_dstr u cpu) None
                                 (wa_iq u cpu)) (wgws g cpu) ∅)
      := prj_lookup q0 _ _ _ (wl_cfg_hart_lookup g u cpu).
    have Hblk : sail_block riscv_step (fin_to_nat cpu)
                  (prj_cfg q0 (wl_cfg g u)) (prj_cfg q0 c')
      := xblk_prj riscv_step q0 (fin_to_nat cpu) (wl_cfg g u) c' Hfine.
    destruct (wprim_hart_block_bwd cpu gen g (wa_dstr u cpu) (wa_iq u cpu) ∅
                (prj_ag q0 <$> pc_ags (wl_cfg g u)) (prj_cfg q0 c')
                Hsh Hoc Hlive Hlkp Hblk)
      as (g2 & dtl & Hstep & Heq).
    have Hstep2 := Hstep.
    apply wprim_step_loop_inv in Hstep2
      as (_ & _ & _ & [(_ & tick & xx & s' & Hrun & Hg2)|(Hnl & _)]);
      [|by destruct (Hnl Hlive)].
    subst g2.
    (* the frame of the whole block, at [pxv6] *)
    have Hxt : xtframe (fin_to_nat cpu) (wl_cfg g u) c'
      := pf_xsolo_run_xtframe riscv_step (fin_to_nat cpu) (wl_cfg g u) c'
           (xblk_run riscv_step (fin_to_nat cpu) (wl_cfg g u) c' Hfine).
    destruct Hxt as (_ & Hximg & Hxfr & _).
    (* the block's own agent, at the target *)
    destruct (pf_xsolo_run_hart riscv_step (fin_to_nat cpu) (wl_cfg g u) c'
                (xat_bnd_hart (fin_to_nat cpu) (wl_cfg g u)
                   (proj1 Hfine)) 
                (xblk_run riscv_step (fin_to_nat cpu) (wl_cfg g u) c' Hfine))
      as (agc & qc & Hlkc & Hstc).
    have Hagsc : prj_ag q0 <$> pc_ags c'
               = <[fin_to_nat cpu :=
                     WPAgent (PSail None (wgregs (whart_write g cpu s') cpu) dtl None (wa_iq u cpu))
                       (wgws (whart_write g cpu s') cpu) ∅]>
                   (prj_ag q0 <$> pc_ags (wl_cfg g u))
      := f_equal (@pc_ags psail) Heq.
    have Hcpu : prj_ag q0 agc
              = WPAgent (PSail None (wgregs (whart_write g cpu s') cpu) dtl None (wa_iq u cpu))
                  (wgws (whart_write g cpu s') cpu) ∅.
    { have H : (prj_ag q0 <$> pc_ags c') !! fin_to_nat cpu
             = (<[fin_to_nat cpu :=
                    WPAgent (PSail None (wgregs (whart_write g cpu s') cpu) dtl None (wa_iq u cpu))
                      (wgws (whart_write g cpu s') cpu) ∅]>
                 (prj_ag q0 <$> pc_ags (wl_cfg g u))) !! fin_to_nat cpu
        by rewrite Hagsc.
      have Hlen : (fin_to_nat cpu
                   < length (prj_ag q0 <$> pc_ags (wl_cfg g u)))%nat.
      { rewrite length_fmap.
        eapply lookup_lt_Some, (wl_cfg_hart_lookup g u cpu). }
      rewrite list_lookup_fmap Hlkc /= in H.
      rewrite list_lookup_insert in H; [|exact Hlen].
      apply (inj Some) in H. exact H. }
    have Hagc : agc = WPAgent (PHart (PSail None (wgregs (whart_write g cpu s') cpu) dtl None
                                        (wa_iq u cpu))) (wgws (whart_write g cpu s') cpu) ∅.
    { destruct agc as [st ws pr]. simpl in Hstc, Hcpu. rewrite Hstc in Hcpu |- *.
      by injection Hcpu as -> -> ->. }
    have Hceq : wl_cfg (whart_write g cpu s') (wl_dstr cpu dtl u) = c'.
    { symmetry.
      rewrite -(wl_cfg_hart_upd g u cpu (whart_write g cpu s') (wl_dstr cpu dtl u)
                  (PSail None (wgregs (whart_write g cpu s') cpu) dtl None (wa_iq u cpu))
                  (wgws (whart_write g cpu s') cpu)).
      - apply wpcfg_eq; cbn [pc_img pc_log pc_ags].
        + rewrite Hximg. done.
        + exact (f_equal (@pc_log psail) Heq).
        + apply (list_eq_insert (pc_ags (wl_cfg g u)) (pc_ags c')).
          * by rewrite Hlkc Hagc.
          * eexists. apply wl_cfg_hart_lookup.
          * intros j Hj. by apply Hxfr.
      - done.
      - done.
      - done.
      - intros cc Hcc. rewrite /hag /whart_write /=.
        by rewrite (greg_insert_ne _ _ _ _ Hcc) (gws_insert_ne _ _ _ _ Hcc)
                   /wl_dstr /= (cupd_ne _ _ _ _ Hcc).
      - by rewrite /hag /wl_dstr /= cupd_eq. }
    have Hlive2 : wthread_live (whart_write g cpu s') gen.
    { destruct Hlive as [Hp Hg]. rewrite /wthread_live /whart_write /=.
      by split. }
    destruct (IH (whart_write g cpu s') (wl_dstr cpu dtl u) cf
                ltac:(by rewrite Hceq) Hall Hlive2
                (Hcont tick xx s' dtl Hrun Hceq))
      as (g' & u' & Hcf & Hlive' & Hrun').
    exists g', u'. split_and!; [done|done|].
    eapply rtc_l; [|exact Hrun'].
    eapply pool_erased; [apply wpool_hart|exact Hstep].
  - (* ---------------- ONE INTERRUPT DELIVERY ---------------- *)
    destruct Hlift as (cpu & -> & Hwire).
    destruct Hfine as (ag & ag' & q & q' & Hlk & Hst & Hlk' & Hst' & Hb & Hb'
                       & Hf & Hdel & Hws & Himg' & Hlog' & Hfr & Hpfstep).
    rewrite (wl_cfg_hart_lookup g u cpu) in Hlk. injection Hlk as <-.
    simpl in Hst. injection Hst as <-.
    destruct Hdel as (_ & v & iq & Hiq & Hq'). simpl in Hiq, Hq'.
    destruct (Hwire v iq Hiq) as (Hv & Hlift').
    have Hnp : no_promises c'
      := wp_pf_step_no_promises (pstep_xv6 riscv_step) (fin_to_nat cpu)
           WeakPromise.LSilent _ _ (wl_cfg_no_promises g u) Hpfstep.
    have Hag' : ag' = WPAgent (PHart q') (wgws g cpu) ∅.
    { have Hpr : pa_prom ag' = ∅ := Hnp _ _ Hlk'.
      destruct ag' as [st ws pr]. simpl in Hst', Hws, Hpr.
      by rewrite Hst' Hws Hpr. }
    have Hceq : wl_cfg (wplic_write g cpu) (wl_iq cpu iq u) = c'.
    { symmetry.
      rewrite -(wl_cfg_hart_upd g u cpu (wplic_write g cpu) (wl_iq cpu iq u)
                  q' (wgws g cpu)).
      - apply wpcfg_eq; cbn [pc_img pc_log pc_ags].
        + exact Himg'.
        + exact Hlog'.
        + apply (list_eq_insert (pc_ags (wl_cfg g u)) (pc_ags c')).
          * by rewrite Hlk' Hag'.
          * eexists. apply wl_cfg_hart_lookup.
          * intros j Hj. by apply Hfr.
      - done.
      - done.
      - done.
      - intros cc Hcc. rewrite /hag /wplic_write /wl_iq /=.
        by rewrite (greg_insert_ne _ _ _ _ Hcc) (cupd_ne _ _ _ _ Hcc).
      - rewrite /hag /wplic_write /wl_iq /=.
        rewrite greg_insert_eq cupd_eq -Hv. by rewrite Hq'. }
    destruct (IH (wplic_write g cpu) (wl_iq cpu iq u) cf
                ltac:(by rewrite Hceq) Hall Hlive Hlift')
      as (g' & u' & Hcf & Hlive' & Hrun').
    exists g', u'. split_and!; [done|done|].
    eapply rtc_l; [|exact Hrun'].
    eapply pool_erased; [apply wpool_plic|].
    right. right. right. left. exists gen.
    split_and!; [reflexivity|reflexivity|reflexivity|reflexivity|].
    left. split; [exact Hlive|].
    exists (<[cpu := register_set sig_seip
                       (bool_to_bit (dev_seip (wgdev g) (fin_to_nat cpu)))
                       (wgregs g cpu)]> (wgregs g)).
    split; [apply PlicStepWire|reflexivity].
  - (* ---------------- ONE DISK BURST + ITS EMIT GROUP ---------------- *)
    destruct Hlift as (-> & Hdd & Hcont).
    destruct Hfine as (d & d' & mem & w & (agd & Hlkd & Hstd)
                       & (agd2 & Hlkd2 & Hstd2) & Hrund & Hds & Hlogd).
    rewrite (wl_cfg_disk_lookup g u) in Hlkd. injection Hlkd as <-.
    simpl in Hstd. injection Hstd as Hdeq.
    have Hxt : xtframe n_disk (wl_cfg g u) c'
      := pf_xsolo_run_xtframe riscv_step n_disk (wl_cfg g u) c' Hrund.
    destruct Hxt as (_ & Hximg & Hxfr & _).
    have Hnp : no_promises c'
      := pf_run_no_promises (wl_cfg g u) c'
           (pf_xsolo_rtc_run riscv_step n_disk (wl_cfg g u) c' Hrund)
           (wl_cfg_no_promises g u).
    have Hagd2 : agd2 = WPAgent (PDisk d' []) (pa_ws agd2) ∅.
    { have Hpr : pa_prom agd2 = ∅ := Hnp _ _ Hlkd2.
      destruct agd2 as [st ws pr]. simpl in Hstd2, Hpr |- *.
      by rewrite Hstd2 Hpr. }
    rewrite dmsgs_n_disk in Hlogd.
    destruct (Hcont d' w (pa_ws agd2) ltac:(by rewrite Hlkd2 -Hagd2)
                ltac:(exact Hlogd) ltac:(exists mem; by rewrite -Hdd Hdeq))
      as (Htrue & Hlift').
    have Hceq : wl_cfg (wdisk_write g d' w) (wl_dk d' (pa_ws agd2) u) = c'.
    { symmetry.
      rewrite -(wl_cfg_disk_upd g u (wdisk_write g d' w)
                  (wl_dk d' (pa_ws agd2) u) (PDisk d' []) (pa_ws agd2)).
      - apply wpcfg_eq; cbn [pc_img pc_log pc_ags].
        + exact Hximg.
        + exact Hlogd.
        + apply (list_eq_insert (pc_ags (wl_cfg g u)) (pc_ags c')).
          * by rewrite Hlkd2 -Hagd2.
          * eexists. apply wl_cfg_disk_lookup.
          * intros j Hj. by apply Hxfr.
      - done.
      - done.
      - done. }
    destruct (IH (wdisk_write g d' w) (wl_dk d' (pa_ws agd2) u) cf
                ltac:(by rewrite Hceq) Hall Hlive Hlift')
      as (g' & u' & Hcf & Hlive' & Hrun').
    exists g', u'. split_and!; [done|done|].
    eapply rtc_l; [|exact Hrun'].
    eapply pool_erased; [apply wpool_disk|].
    right. right. left. exists gen.
    split_and!; [reflexivity|reflexivity|reflexivity|reflexivity|].
    left. split; [exact Hlive|]. exists d', w.
    split; [exact Htrue|reflexivity].
Qed.

(* ====================================================================== *)
(** ** 7. THE φ TRANSPORT

    [WeakGhost.no_violation] at a [WeakLang] state refutes a HART-AUTHORED,
    HART-OBSERVED violation at the corresponding pf configuration.  The
    transport is SYNTACTIC — L0(c) made [pub_of] the log predicate
    [WeakMem.wpublished], which is the one [no_violation] is stated with, and
    [obs_flr] IS the agent's [coh]. *)

Theorem wl_no_hart_violation (g' : wgstate) (u' : wlaux)
    (p : nat) (m : wmsg) (ci cj : CPU) (a : Z) :
  no_violation (wglog g') (wgws g') →
  violates_at (wl_cfg g' u') p m (fin_to_nat ci) (fin_to_nat cj) a → False.
Proof.
  intros Hnv (Hlog & Htid & Hcls & Hpub & Hne & Hbyte & Hobs).
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
(** ** 8. The initial configuration *)

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

(** …and every one of its program states is an instruction BOUNDARY — the
    cone's [Hps_bnd], discharged rather than assumed. *)
Lemma xv6_ps0_bnd (g : wgstate) (u : wlaux) :
  ∀ i p, xv6_ps0 g u !! i = Some p → pbnd p.
Proof.
  intros i p Hi. rewrite /xv6_ps0 /xv6_ps /xv6_harts in Hi.
  destruct (decide (i < NCPU)%nat) as [Hlt|Hge].
  - rewrite lookup_app_l in Hi;
      [|by rewrite length_fmap length_fmap cpu_enum_length].
    rewrite list_lookup_fmap list_lookup_fmap in Hi.
    destruct (enum CPU !! i) as [c|]; simplify_eq/=; by split.
  - rewrite lookup_app_r in Hi;
      [|rewrite length_fmap length_fmap cpu_enum_length; lia].
    rewrite length_fmap length_fmap cpu_enum_length in Hi.
    destruct (i - NCPU)%nat as [|k]; simpl in Hi;
      [by simplify_eq|by destruct k; simplify_eq].
Qed.

(* ====================================================================== *)
(** ** 9. THE RESIDUE, and THE BAD-EDGE REFUTATION *)

(** THE MMIO/M5 SEAM, PER DECOMPOSITION (residue (A) of the header): for the
    segment chain that a MINIMAL BAD EDGE's cone decomposes into, the
    [WeakLang] machine can follow along.  Quantified over exactly what
    [WeakSailCone.cone_segments2] produces — the two events, the segment
    list, the final configuration and the violation at it — and over segment
    chains refined to single hart blocks, which is the form the lift
    consumes. *)
Definition cone_liftable (gen : nat) (g0 : wgstate) (u0 : wlaux)
    (TS : ptraces pxv6) : Prop :=
  ∀ (b1 b2 : gev) (segs : list seg2) (cf : wpcfg pxv6),
    bad n_disk TS b1 b2 → bad_min n_disk TS b2 →
    chained2 segs (wl_cfg g0 u0) cf →
    Forall seg2_fine segs →
    violation_hart cls_of pub_of n_disk cf →
    (∀ j ag, pc_ags cf !! j = Some ag → pbnd (pa_st ag)) →
    wl_lift gen segs g0 u0.

(** The per-bundle premises of [WeakSailCone] §11-§12, verbatim its section
    context (minus the ones this file discharges — [Hps_bnd] by
    [xv6_ps0_bnd], [Himgt] from the boot image — and minus the ones
    [robust_main]'s own derivation supplies). *)
Definition xv6_cone_premises (TS : ptraces pxv6) : Prop :=
  (** [Hcq]: the post-state of a cross-edge source is quiet *)
  (∀ e1 e2, gdep2 TS e1 e2 → e1.1 ≠ e2.1 →
     ∀ T ag', pt_trs TS !! e1.1 = Some T →
       at_ags T !! S e1.2 = Some ag' → pquiet (pa_st ag')) ∧
  (** [Hres]: every record's residual is shaped, live and oracle-consistent *)
  (∀ i T k ag q,
     pt_trs TS !! i = Some T → at_ags T !! k = Some ag →
     pa_st ag = PHart q →
     match sp_m q with
     | None => True
     | Some m => sail_shaped m ∧ sail_live m ∧
                 ∃ d, oracle_consistent d m (sp_dev q)
     end) ∧
  (** [Hirqb]: an interrupt delivery has a boundary pre-state *)
  (∀ i T k ag ag' q q' l,
     pt_trs TS !! i = Some T →
     at_ags T !! k = Some ag → at_ags T !! S k = Some ag' →
     pa_st ag = PHart q → pa_st ag' = PHart q' →
     irq_deliver q l q' → pbnd (PHart q)) ∧
  (** [Hcls]: a logged message carries its author's computed class *)
  (∀ i T k ev ag ts m,
     pt_trs TS !! i = Some T →
     at_evs T !! k = Some ev → at_ags T !! k = Some ag →
     ae_ts ev = Some ts → pt_log TS !! (ts - 1)%nat = Some m →
     wm_ak m = lbl_class (ae_lb ev) (pa_ws ag)).

(** THE BUNDLE FACTS [robust_main]'s own proof derives from a behavior — and
    which the cone consumes.  Packaged so that the "no bad edge" premise of
    [robust_main_no_bad] may USE them rather than re-derive them. *)
Definition tb_facts {P : Type} (pstep : P → wlabel → P → Prop) (nh : nat)
    (img : image) (ps : list P) (TS : ptraces P) : Prop :=
  ptraces_wf pstep TS ∧ ptraces_ws_init TS ∧ (∀ a, co_tc TS a) ∧
  writes_fulfilled TS ∧ pt_img TS = img ∧
  length (pt_trs TS) = length ps ∧
  (∀ p m, pt_log TS !! p = Some m → wm_data m ≠ []) ∧
  (∀ j T ag0, pt_trs TS !! j = Some T →
     at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)) ∧
  ptraces_fwd_own TS ∧ ee_ok TS ∧ edges_split nh TS.

(** THE REFUTATION.  A bad edge would give a minimal one, whose cone
    [WeakSailCone.cone_segments2] segments; the refinement cuts the hart
    segments into instructions; [cone_liftable] lifts the chain into the
    [WeakLang] machine; and φ at the state it reaches refutes the violation
    the cone exhibits.  So there is no bad edge. *)
Theorem xv6_no_bad_edge (gen : nat) (g0 : wgstate) (u0 : wlaux)
    (TS : ptraces pxv6) :
  (∀ b, sail_shaped (riscv_step b)) →
  wthread_live g0 gen →
  wglog g0 = [] → (∀ cc : CPU, wgws g0 cc = ws_init) → wa_dws u0 = ws_init →
  img_total (img_z (wgimg g0)) →
  (∀ t2 g2, rtc (@erased_step weak_riscv_lang) (wpool gen, g0) (t2, g2) →
            no_violation (wglog g2) (wgws g2)) →
  bad_wf n_disk TS →
  tb_facts (pstep_xv6 riscv_step) n_disk (img_z (wgimg g0)) (xv6_ps0 g0 u0) TS →
  xv6_cone_premises TS →
  cone_liftable gen g0 u0 TS →
  ∀ e1 e2, ¬ bad n_disk TS e1 e2.
Proof.
  intros Hsh Hlive Hlog0 Hws0 Hdws0 Himgt Hphi Hbwf
    (Hwf & Hwsi & Hco & Hwfl & Himg & Hnag & Hdata & Hps0 & Hfo & Hee & Hsplit)
    (Hcq & Hres & Hirqb & Hcls) Hcl e1 e2 Hbad.
  destruct (Hbwf e1 e2 Hbad) as (f1 & f2 & Hbad' & Hmin).
  destruct (cone_segments2 TS (img_z (wgimg g0)) (xv6_ps0 g0 u0)
              Hwf Hwsi Hco Hwfl Himg Hnag Hdata Hps0 Hfo Hee n_disk Hsplit
              (xv6_ps0_bnd g0 u0) Hcq Hres Himgt Hirqb Hcls f1 f2 Hbad' Hmin)
    as (segs & cf & Hch & Hok & _ & Hvio & Hbnd).
  rewrite (wp_init_wl g0 u0 Hlog0 Hws0 Hdws0) in Hch.
  destruct (seg2_refine segs (wl_cfg g0 u0) cf Hch Hok)
    as (segs' & Hch' & Hfine).
  have Hwl := Hcl f1 f2 segs' cf Hbad' Hmin Hch' Hfine Hvio Hbnd.
  destruct (wl_lift_sound gen Hsh segs' g0 u0 cf Hch' Hfine Hlive Hwl)
    as (g' & u' & Hcf & _ & Hrun).
  destruct (violation_hart_violates_at n_disk cf Hvio)
    as (p & m & i & j & a & Hv & Hi & Hj).
  set (ci := nat_to_fin Hi : CPU).
  set (cj := nat_to_fin Hj : CPU).
  have Hci : fin_to_nat ci = i by apply fin_to_nat_to_fin.
  have Hcj : fin_to_nat cj = j by apply fin_to_nat_to_fin.
  eapply (wl_no_hart_violation g' u' p m ci cj a (Hphi _ _ Hrun)).
  rewrite Hci Hcj -Hcf. exact Hv.
Qed.

(* ====================================================================== *)
(** ** 10. THE UPDATED COMPOSITION

    [WeakRobustMain.robust_main] consumes [pf_violation_free_hart] in exactly
    ONE place — [gdep2_acyclic_main], to rule out bad edges.  Since the cone
    route rules them out directly, that call is replaced by
    [gdep2_acyclic_bad_free] (whose [bad_wf_strong] is vacuous once no bad
    edge exists) and everything else is [robust_main]'s own derivation,
    mirrored here so that [WeakRobustMain.v] itself is untouched. *)

Theorem robust_main_no_bad {P : Type} (pstep : P → wlabel → P → Prop)
    (nh : nat) (img : image) (ps : list P) (c : wpcfg P) :
  lat_free_prog pstep → ts_oblivious pstep →
  wp_behavior pstep img ps c →
  (∀ mid TS,
     rtc (wp_promise_step (P:=P)) (wp_init img ps) mid →
     ptraces_of pstep TS mid c → main_premises nh TS) →
  (∀ mid TS,
     rtc (wp_promise_step (P:=P)) (wp_init img ps) mid →
     ptraces_of pstep TS mid c → tb_facts pstep nh img ps TS →
     ∀ e1 e2, ¬ bad nh TS e1 e2) →
  ∃ cf, rtc (wp_pf_run pstep) (wp_init img ps) cf ∧
        prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
Proof.
  intros Hlf Hobl Hb Hprem Hnb.
  destruct (wp_behavior_fulfil_once pstep img ps c Hlf Hb)
    as (mid & TS & Hprom & Hof & Hnp & Hacct).
  destruct (Hprem mid TS Hprom Hof)
    as (Hsplit & Hbwf & Hee & (sync & Hbytes)).
  (* the derived bundle facts — verbatim [robust_main]'s *)
  have Hwf : ptraces_wf pstep TS by eapply ptraces_of_wf.
  have Hla : log_authored (pc_log mid).
  { eapply log_authored_promise_run; [apply log_authored_init|exact Hprom]. }
  have Hwfl : writes_fulfilled TS
    by eapply (ptraces_of_writes_fulfilled pstep TS mid c).
  have Hlne : log_ne (pc_log mid).
  { eapply log_ne_promise_run; [apply log_ne_init|exact Hprom]. }
  have Hinit : cfg_ws_init mid.
  { eapply cfg_ws_init_promise_run; [apply cfg_ws_init_init|exact Hprom]. }
  have Hwsi : ptraces_ws_init TS by eapply (ptraces_of_ws_init pstep TS mid c).
  have Hfo : ptraces_fwd_own TS by eapply (ptraces_of_fwd_own pstep TS mid c).
  have Hco : ∀ a, co_tc TS a
    by eapply (co_serialized_pkg pstep TS sync Hwf Hwfl Hbytes).
  destruct (promise_run_shape (wp_init img ps) mid Hprom)
    as (Hpimg & Hplen & Hpst).
  have Hof' := Hof.
  destruct Hof' as (Himg0 & Hlog0 & Hlent & Hwft & Hfst & Hlst
                    & Hclogc & Hcimgc & Hclenc).
  have Himg1 : pt_img TS = img by rewrite Himg0 Hpimg.
  have Hlen1 : length (pt_trs TS) = length ps.
  { by rewrite Hlent Hplen /wp_init /= length_map. }
  have Hdata1 : ∀ p m, pt_log TS !! p = Some m → wm_data m ≠ [].
  { rewrite Hlog0. exact Hlne. }
  have Hps1 : ∀ j T ag0, pt_trs TS !! j = Some T →
                at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0).
  { intros j T ag0 HT Hag0.
    have Hmid : pc_ags mid !! j = Some ag0 by rewrite -(Hfst j T HT).
    destruct (Hpst j ag0 Hmid) as (ag & Hag & Hst).
    rewrite /wp_init /= list_lookup_fmap in Hag.
    destruct (ps !! j) as [p0|] eqn:Hp0; simpl in Hag; [|done].
    injection Hag as <-. by rewrite Hst. }
  (* NO BAD EDGE — so the per-edge split is [rf_edges_ok] outright *)
  have Hnobad : ∀ e1 e2, ¬ bad nh TS e1 e2.
  { apply (Hnb mid TS Hprom Hof). by split_and!. }
  have Hacyc : gdep2_acyclic TS.
  { eapply (gdep2_acyclic_bad_free pstep nh TS Hwf Hfo Hee Hsplit).
    intros e1 e2 Hbe. by destruct (Hnobad e1 e2 Hbe). }
  eapply (sim_full pstep TS img ps Hwf Hwsi Hco Hwfl Hlf Hobl Himg1 Hlen1
            Hdata1 Hps1 c Hacyc).
  - by rewrite Himg0 Hcimgc.
  - by rewrite Hlog0 Hclogc.
  - by rewrite Hclenc Hplen /wp_init /= length_map.
  - exact Hlst.
Qed.

(** THE HEADLINE, LIFTED: [WeakCompose.xv6_weak_robust] with
    [pf_violation_free_hart] replaced by the cone route's premises. *)
Corollary xv6_weak_robust_lifted (gen : nat) (g0 : wgstate) (u0 : wlaux)
    (c : wpcfg pxv6) :
  (∀ b, sail_shaped (riscv_step b)) →
  wthread_live g0 gen →
  wglog g0 = [] → (∀ cc : CPU, wgws g0 cc = ws_init) → wa_dws u0 = ws_init →
  img_total (img_z (wgimg g0)) →
  (∀ t2 g2, rtc (@erased_step weak_riscv_lang) (wpool gen, g0) (t2, g2) →
            no_violation (wglog g2) (wgws g2)) →
  (∀ (cb mid : wpcfg pxv6) (TS : ptraces pxv6),
     wp_behavior (pstep_xv6 riscv_step) (img_z (wgimg g0)) (xv6_ps0 g0 u0) cb →
     rtc (wp_promise_step (P := pxv6))
       (wp_init (img_z (wgimg g0)) (xv6_ps0 g0 u0)) mid →
     ptraces_of (pstep_xv6 riscv_step) TS mid cb →
     main_premises n_disk TS ∧ xv6_cone_premises TS ∧
     cone_liftable gen g0 u0 TS) →
  wp_behavior (pstep_xv6 riscv_step) (img_z (wgimg g0)) (xv6_ps0 g0 u0) c →
  ∃ cf, rtc (wp_pf_run (pstep_xv6 riscv_step))
          (wp_init (img_z (wgimg g0)) (xv6_ps0 g0 u0)) cf ∧
        prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
Proof.
  intros Hsh Hlive Hlog0 Hws0 Hdws0 Himgt Hphi Hprem Hbeh.
  eapply (robust_main_no_bad (pstep_xv6 riscv_step) n_disk
            (img_z (wgimg g0)) (xv6_ps0 g0 u0) c
            (xv6_lat_free riscv_step) (xv6_ts_oblivious riscv_step) Hbeh).
  - intros mid TS Hprom Hof.
    by destruct (Hprem c mid TS Hbeh Hprom Hof) as (H & _ & _).
  - intros mid TS Hprom Hof Htb.
    destruct (Hprem c mid TS Hbeh Hprom Hof) as ((_ & Hbwf & _ & _) & Hcp & Hcl).
    by eapply (xv6_no_bad_edge gen g0 u0 TS Hsh Hlive Hlog0 Hws0 Hdws0 Himgt
                 Hphi Hbwf Htb Hcp Hcl).
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
  img_total (img_z (wgimg g0)) →
  (∀ (cb mid : wpcfg pxv6) (TS : ptraces pxv6),
     wp_behavior (pstep_xv6 riscv_step) (img_z (wgimg g0)) (xv6_ps0 g0 u0) cb →
     rtc (wp_promise_step (P := pxv6))
       (wp_init (img_z (wgimg g0)) (xv6_ps0 g0 u0)) mid →
     ptraces_of (pstep_xv6 riscv_step) TS mid cb →
     main_premises n_disk TS ∧ xv6_cone_premises TS ∧
     cone_liftable gen_id g0 u0 TS) →
  wp_behavior (pstep_xv6 riscv_step) (img_z (wgimg g0)) (xv6_ps0 g0 u0) c →
  ∃ cf, rtc (wp_pf_run (pstep_xv6 riscv_step))
          (wp_init (img_z (wgimg g0)) (xv6_ps0 g0 u0)) cf ∧
        prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
Proof.
  intros Hsh Hwp Himgt Hprem Hbeh.
  eapply (xv6_weak_robust_lifted gen_id g0 u0 c Hsh);
    [|exact Hlog|exact Hws|exact Hdws|exact Himgt| |exact Hprem|exact Hbeh].
  - split; [exact Hpow|]. by rewrite Hgen0 Hgid.
  - intros t2 g2 Hr.
    exact (proj1 (weak_system_adequacy_phi Σ (enum CPU) g0 D Hgid Hpow Hgen0
                    Hlog Hws Hwp t2 g2 Hr)).
Qed.
