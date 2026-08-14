(** * WeakComposeLang.v — L3/B5b: THE CONE-ROUTE φ-CONSUMPTION AND THE
      LIFTED COMPOSITION
      (lift stages L3 + B5b of [claude-notes/completed/weak-memory-lift.md])

    WHAT THIS FILE IS.  [WeakCompose.xv6_weak_robust] is the M6 headline
    theorem over the wp machine ([wpcfg pxv6 unit]); [WeakAdequacy] exports φ
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
        [wl_cfg g u] is the [wpcfg pxv6 unit] a [WeakLang] state [g] denotes, given
        the per-agent data a [wgstate] does NOT carry: each hart's PRIVATE
        DEVICE FABRIC and interrupt oracle ([wa_dev], [wa_iq] — the two
        [WeakSailLTS.psail] fields the machine state has no image of) and the
        disk agent's own fabric state and [wstate] ([wa_dd], [wa_dws]).  Harts sit at
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
        chain of [seg2] segments whose HART segments are boundary-to-boundary,
        possibly MANY instructions long, and — since the [Hseip] coverage fix
        — possibly containing INTERRUPT DELIVERIES ([WeakSailCone.xstep]),
        while one [WeakLang] hart step is exactly ONE delivery-free
        instruction and one [WeakLang] plic step is one delivery at a
        boundary.  [seg2_refine] re-cuts such a chain into one whose hart
        segments are single delivery-free blocks ([xblk]) and whose
        deliveries are boundary [SegIrq]s: each block's deliveries are
        COMMUTED FORWARD to its end by [WeakSailComplete] §9's reordering
        (sound because [Hseip] says the interrupted residual never touches
        the pin).  ONE thing does move, and only one: the chain now ends at
        a configuration [WeakSailCone.xcfg_eqv]-related to [cf] rather than
        at [cf] itself — register files agree POINTWISE, not by [=], since
        two [register_set]s of the same field group commute only up to
        funext, which this chain does not use.  The log, the [wstate]s, the
        promise sets and every other agent are literally equal, so
        [violates_at] / [violation_hart] / boundary-ness transport
        ([WeakSailCone.xcfg_eqv_violation_hart], [xcfg_eqv_bnd]).

    (4) THE LIFT ([wl_lift], §6) AND ITS SOUNDNESS ([wl_lift_sound]).
        [wl_lift gen segs g u] is a PREDICATE on the [WeakLang] start state
        (no successor: the successor is CONSTRUCTED by the soundness proof,
        from the [wrun] that [WeakSailLTS2.sail_block_wrun] reconstructs).
        Per segment it carries exactly the DEVICE-SEAM residue and nothing
        else:
          - [SegHart]: FABRIC AGREEMENT ([wa_dev u cpu = wgdev g] — the twin
            of [SegDisk]'s [wa_dd u = wgdev g]), DEVICE DECODABILITY along
            this segment's own run ([WeakSailLTS2.dev_ok_blk]) and
            EXCLUSIVE-WINDOW FUSION along the same run
            ([WeakSailLTS2.fused_blk] — no step of the block took the BARE
            exclusive-read arm, §B(E)), plus a
            continuation quantified over the [wrun]s whose [WeakLang]
            successor MATCHES the segment's target.  The successor updates
            that hart's private fabric to the block's own [wm_dev s'], which
            is exactly what [WeakLang.whart_write] does to [wgdev];
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
        is only what §A(4) lists: per hart block the fabric agreement and
        the block's device decodability, per delivery the plic wire, per disk
        group the device view and the true-memory [wdisk_step].  Everything else about the
        correspondence — the log, the registers, the [wstate]s, the agent
        vector — is DERIVED (that is what [wl_lift_sound] is).

    (A') [Hirqb] WAS A COVERAGE GAP — THE FIX THAT RETIRED IT (stage B).
        Until stage B the segmentation took "every [irq_deliver] step of
        every trace has a BOUNDARY pre-state" as a premise.  That is not an
        assumption about the PROGRAM, it is a restriction on the MACHINE,
        and it is one real hardware violates: the PLIC asserts SEIP
        whenever it likes, including in the middle of an instruction, so
        the premise silently excluded those behaviors.  What replaces it,
        [Hseip], is a per-image checker-style fact of the same family as
        [sail_shaped]: a delivery that lands mid-instruction interrupts a
        residual that neither reads nor writes [sig_seip]
        ([WeakSailComplete.seip_free_psail]; the WRITE half is not
        optional — see that file's §9 deviation (a)).  Mid-block deliveries
        then travel forward to the block's end (§A(3)) where the plic wire
        is exactly the [SegIrq] arm the lift already had.
        RECORDED NARROWING: the remaining excluded corner is a delivery
        landing between an SIE-on interrupt check and an in-block [sip]
        read; kernel [sip] reads run with SIE off, so the per-image
        discharge is a checker fact.

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

    (C) THE ∀-PATH DEVICE ORACLE WAS UNSATISFIABLE — THE FINDING THAT
        RETIRED THE STREAM (2026-08-13).  Until stage D each hart's MMIO
        responses came from a positional ORACLE STREAM
        ([WeakSailLTS.psail]'s old [sp_dev : dstream]) and the ⇐ direction
        needed [WeakSailLTS2.oracle_consistent] — "this stream is what the
        device would have answered, ALONG EVERY PATH of the instruction".
        That premise is FALSE at essentially every S-mode record, and had
        been since L3: [WeakInterp.wrun]'s RAM reads quantify over every read
        value, including the FETCHED WORD and every page-walk PTE, so one
        stream would have to serve, from one device state, every device
        access every junk fetch decodes to along every junk-but-valid
        translation path — two fetched words decoding to [lw]/[lb] at one VA
        demand the same stream head have length 4 and length 1.  It appeared
        here as [cone_liftable]'s hart conjunct and in
        [WeakSailCone] as [horc_prem]; both are gone.  THE FIX (stage D):
        the hart carries a private copy of the DEVICE AUTOMATON, read and
        written through totalized accessors, and the retained assumption
        shrinks to the two satisfiable halves listed in §A(4) — fabric
        agreement at each segment, and decodability along the segment's OWN
        run.  Third finding of the false-premise genre in this file; cf. (B)
        and (D).

    (E) THE ∀-ANSWER SHAPE PREMISES WERE REFUTABLE — (O1), FIXED IN THE
        PREDICATES (2026-08-13, stage C1 finding / C2 fix).  Premise 1's
        [∀ b, sail_live (riscv_step b)] was FALSE AS STATED, and so was
        [sail_shaped]'s reading of the same arms: both quantified their
        [MemRead]/[MemWrite] arms over the FULL answer type, including the
        abort [inr ab], which [rv64d.read_ram] answers with [exit tt]
        ([GenericFail]) — every load in the model goes through there
        ([WeakShape]'s [read_ram_not_live], the refutation, deleted when this
        was fixed).  [WeakSailLTS.sail_mstep] only ever supplies
        [inl (w, None)] / [inl None], so the fix is to quantify over exactly
        those.  Fourth finding of the over-quantified-∀ genre in this cone
        (cf. (C), and [WeakSailLTS] delta (b)).  Nothing downstream weakens:
        every consumer instantiates those arms at exactly those answers.

    (F) THE EXCLUSIVE WINDOW WAS A MACHINE COVERAGE GAP — (O2), FIXED IN THE
        LTS, AND THE NEW SEAM CONJUNCT (2026-08-13).  [sail_shaped]'s
        [amo_tail] demanded a conditional write before the instruction ended,
        and [sail_mstep] could step an [ak_latest] read ONLY by fusing it
        with that write.  Hardware executes a bare [lr], a FAILING [sc], an
        [amocas] whose comparison misses and a page walk whose exclusive PTE
        read errors out; the model issues all of them
        ([rv64d.execute_LOADRES], [execute_AMO]'s fault/mismatch arms,
        [update_and_write_pte]'s error arms).  So premise 1 was false AND the
        machine was STUCK there — a coverage gap of the same genre as
        [Hirqb] (A'), not a predicate bug alone.  THE FIX:
        [WeakSailLTS.amo_tail]'s [Interface.Ret] arm becomes [True] (a window
        MAY be abandoned, and what it still forbids — reads, barriers,
        non-closing writes — is what keeps the abandoned tail steppable), and
        [sail_mstep] gains the BARE EXCLUSIVE-READ ARM: the read steps as a
        plain [LLoad] (lat := false — lat-freedom is preserved) bracketing
        the whole abandoned window to the instruction's [Interface.Ret],
        symmetrically to the way the fused arm brackets to its conditional
        write.  The machine only GAINS behaviors, which is the safe
        direction, and the residual after a bare step is [Interface.Ret], so
        no residual invariant of the completion kit moves.
        WHAT IT COSTS: the ⇐ reconstruction cannot map a bare step back to a
        [wrun] (an interpreter exclusive read is not a plain load), so
        [wl_lift]'s [SegHart] gains [WeakSailLTS2.fused_blk] beside
        [dev_ok_blk] — the same run-local, TARGET-INDEXED shape, and the same
        per-image discharge family: kernel AMOs target mapped lock words and
        do not fault, so their windows close.  [WeakSailComplete.tail_complete]
        takes the fused route where the window closes and the bare one where
        it does not, and EXPORTS WHICH (its [fu : bool] and the conjunct
        [fu = true → rtc (pf_solo_f next i) c c']), so a supplier can see
        exactly when a completed reader tail is [fused_blk]-compatible.

        (O4), THE MIRROR IMAGE, FIXED THE SAME WAY IN STAGE C4.  A CONDITIONAL
        WRITE WITH NO EXCLUSIVE READ — a standalone [sc], which
        [rv64d.execute_STORECON] issues because the lr/sc reservation lives in
        the model's pure axioms and the matching [lr] is a different
        [riscv_step] — made premise 1 false and the machine stuck for the
        same reason on the write side.  The fix is one conjunct in each of
        [sail_shaped] and [sail_mstep]: the window-closed [MemWrite] arms
        accept ANY RAM write of nonzero width, so the standalone conditional
        write steps as a plain [LStore] (a succeeding [sc] really does store;
        the machine again only GAINS behaviors).  It is ONE step, not a
        bracket — there is no open window to abandon, so no residual
        invariant moves.  The ⇐ cost is folded into the SAME predicate:
        [pf_solo_f] additionally forbids stepping from a conditional-write
        node, so [fused_blk] now reads "every exclusive access of the block
        is part of a fused rmw", and [tail_complete]'s [fu] flag reports the
        standalone conditional write exactly as it reports the bare read.
        (The side condition is needed even though [wrun]'s write arm accepts a
        conditional write unchanged, because [wrun] stamps the message
        [WCexcl] where the pf step carries [lbl_class].)

        (O10), THE THIRD AND LAST OF THE FAMILY — AND IT DELETED THE WINDOW
        (stage C7 finding, stage C8 fix).  C2's bracket assumed the abandoned
        tail is SILENT.  [rv64d.update_and_write_pte] abandons its exclusive
        PTE reservation DEEP INSIDE [translate], on the arm where the re-read
        entry needs no A/D update, so the abandoned tail is the whole rest of
        the instruction — memory accesses included — and every memory
        instruction and the fetch translate.  Premise 1 was false again.
        A "the tail is quiet from here" bracket is only as good as the CALL
        DEPTH at which the window is abandoned.  THE FIX is the same
        narrowing the two arms above took: [sail_shaped]'s [MemRead] arm
        DROPS the window entirely (an exclusive read is shaped exactly like a
        plain one), [amo_tail] is DELETED, and [sail_mstep]'s bare arm
        becomes ONE STEP — the plain [LLoad] arm simply stopped requiring
        [ak_latest = false].  Nothing new is owed: [pf_solo_f]/[fused_blk]
        are UNCHANGED (a step from an exclusive read must still APPEND), the
        fused rmw arm stays and takes its structure from the RUN
        ([silent_run] to a [wr_node]) rather than from the predicate, and
        [tail_complete] simply reports [fu := false] at an exclusive read.
        Per-image discharge grows one clause: xv6 runs with
        [menvcfg.ADUE = 0].

    (D) THE AGENT QUANTIFIER — FOUND HERE, FIXED IN LAYER 1, GONE FROM THE
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

      1. [rv64d_axiom_shapes] AND [rv64d_live_residue] — what is left of
         seam (6)'s two group-3 model facts.  BOTH ARE NOW RECORDS, NOT
         [∀ b] PREMISES (stages C8 and C9).

         THE SHAPE HALF IS NO LONGER A PREMISE (stage C8).
         [WeakShapeTop.riscv_step_shaped_ax] PROVES
         [∀ b, sail_shaped (riscv_step b)] from [rv64d_axiom_shapes] alone —
         a three-line [Record] of [gquiet] facts about the three OPAQUE
         MONADIC AXIOMS [rv64d] declares ([load_reservation],
         [cancel_reservation], [plat_term_write]; finding (O5), and the only
         irreducible one of the family, since nothing about an opaque
         constant's shape is provable OR refutable).  Everything else is
         machine-checked: the 294-lemma generated tower
         ([tools/gen_shape.py], [WeakShapeGen01..15]), the 116-lemma value
         sweep ([WeakShapeExecGen01..03]), the decoder postcondition
         ([WeakShapeAst.ast_wf], [WeakShapeDec.gpureP_ext_decode]), the
         memory cone ([WeakShapeMem]) and the peel
         ([WeakShapePeel], [WeakShapeExec]).  Getting there took FIVE
         findings, four of which were REFUTATIONS OF THIS PREMISE AS STATED —
         (O2) the abandoned exclusive window, (O4) the standalone
         store-conditional, (O6) the decoder's zero width, (O9) the raised
         Sail exception, (O10) the page walker's abandoned reservation — each
         fixed by NARROWING the specification to what the machine enforces,
         never by adding an index; §B(F) has the whole arc, and the
         worklist [claude-notes/projects/weak-memory-premises.md] has the
         findings verbatim.

         THE LIVENESS HALF IS NO LONGER A PREMISE EITHER (stage C9), AND
         THE PREMISE IT REPLACES WAS FALSE.  (O9)'s witness refutes
         [∀ b, sail_live (riscv_step b)] as written — liveness forbids a
         raised Sail exception and [rv64d.zicfiss_xSSE] raises one at
         [VirtualSupervisor], a value the OLD [RegRead] arm quantified over
         — so a capstone carrying it was VACUOUS.  C9 took the same
         narrowing the five shape findings took: [sail_mstep] answers a
         [RegRead] concretely, so the predicate does too.
         [WeakSailComplete.sail_live_st rs m] answers every [RegRead] from
         [rs] and THREADS every [RegWrite]; the sole exception is
         [sig_seip], still ∀-quantified because [irq_deliver] writes the pin
         behind the residual's back (note (g) there).  Then
         [WeakShapeLive.riscv_step_live_ax] PROVES
         [∀ rs b, priv_ok rs → sail_live_st rs (riscv_step b)] from the
         record [rv64d_live_residue].

         READ THE TWO RECORDS DIFFERENTLY.  [rv64d_axiom_shapes] is
         IRREDUCIBLE.  [rv64d_live_residue] is the (O3) LIVENESS SWEEP,
         UN-RUN — two fields ([try_step], [tick_clock]) standing for a
         campaign whose size is now measured ([make live-sites]): 123 of the
         345 reachable monadic definitions carry a failure node directly,
         302 carry one in their cone, 431 sites in all, each needing a
         REACHABILITY argument rather than a shape lemma.  It is a [Record]
         and not an [Axiom] precisely so that this shows up as a named
         hypothesis a caller must supply.

         THE SWAP IS NOT A WEAKENING, AND SAYING SO IS THE POINT.  The
         deleted [∀ b] premise is unsatisfiable, so it formally implies
         anything, including this record; but [Hpriv] (5 below) is a NEW
         per-trace obligation that the old premise did not imply, and a
         supplier who had "discharged" the old one had in fact discharged
         nothing.  What the swap buys is that the capstones are no longer
         vacuous.
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
         index too) AND [xv6_cone_premises TS], which is now exactly THREE
         conjuncts — [Hcq] (a cross-edge source's post-state is quiet),
         [Hseip] (a delivery either lands at an instruction boundary or the
         residual it interrupts never touches [sig_seip]) and, since stage
         C9, [Hpriv] (every hart record's [cur_privilege] is one of
         [Machine]/[Supervisor]/[User]) — stated exactly as [WeakSailCone]
         §11-§13's section context.  [Hpriv] is the per-trace input of
         premise 1's liveness half: a boundary record is where a fresh
         instruction is loaded, and [riscv_step_live_ax] gives its liveness
         only at a [priv_ok] register file.  Per-image discharge: xv6 never
         enables the hypervisor extension.  RECORDED UPGRADE PATH (not
         attempted): the model-level reachability invariant "[priv_ok] is
         preserved by [riscv_step]", which would delete the premise — it is
         the same whole-instruction-set sweep [rv64d_live_residue] is.
         The package is
         demanded ONLY of bundles satisfying [WeakRetag.cls_canonical
         lbl_class] (see 5' below), so the supplier's obligation is strictly
         smaller than it looks.
         [Hres] IS NO LONGER A CONJUNCT: [WeakSailCone.hres_derived] proves
         it inside [xv6_no_bad_edge] from premise 1 and the trace
         well-formedness of [tb_facts] (stage D — with the device residue
         gone, the derivation has no leftover input).
      5'. CANONICITY IS A FREE HYPOTHESIS, NOT A PREMISE.  What used to be
         [xv6_cone_premises]'s [Hcls] conjunct ("a logged message carries
         its author's computed class") is now handed TO the supplier:
         the per-bundle package is required only when
         [WeakRetag.cls_canonical lbl_class TS] holds, and the capstone
         discharges it by PRECOMPOSING WITH THE RETAG — [wm_ak] is inert
         ([WeakRetag]), so the behavior's own [wp_behavior_fulfil_once]
         bundle retagged at [WeakRetag.canon_f] is canonical, describes a
         behavior with the same [prog_of] and [mem_of], and carries the
         fulfilment accounting across ([fulfil_acct_retag]).  The retag is
         composed here rather than through [WeakRetag.behavior_canonical]
         precisely because that lemma's own decomposition comes from
         [wp_behavior_traced] and so has no accounting.
      6. [cone_liftable] — residue (A) of §B, and THE ONLY LIFT RESIDUE:
         the MMIO/M5 device seam, per decomposition.  Its [SegHart] bundle
         now carries THREE conjuncts, not two: fabric agreement, device
         decodability ([dev_ok_blk]) and exclusive-window fusion
         ([fused_blk], §B(F)) — the last two being the two run-local,
         target-indexed side conditions the ⇐ bracket needs.
      7. The 5 rv64d baseline axioms.  NO functional extensionality, NO
         classical axiom.  (Checked with [Print Assumptions] on both
         capstones; the funext-free discipline is why the refinement's
         output is [xcfg_eqv]-related rather than equal, §A(3).)

    WHAT IS GONE relative to the previous revision:
    [∀ b, sail_shaped (riscv_step b)] (a THEOREM now, §D 1 — replaced by the
    strictly smaller [rv64d_axiom_shapes]), [Hcls] (a free
    hypothesis now, §D 5') and [Hirqb] (RETIRED — it was a COVERAGE GAP,
    not an assumption about the program: hardware asserts SEIP
    mid-instruction, and demanding that every delivery land at an
    instruction boundary excluded those behaviors outright.  Its
    replacement [Hseip] constrains only what an interrupted residual may
    do, and the deliveries it now admits are commuted forward to their
    block's end, §A(3)).  From the revision before that: [Hres] (derived,
    §D 5) and the per-hart oracle-stream conjunct of [cone_liftable]
    (§B(C)), replaced by an equality and a run-local side condition inside
    [wl_lift].

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
From xv6iris Require Import WeakRetag.
From xv6iris Require Import WeakInterp WeakInterpProj WeakSailLTS WeakSailLTS2.
From xv6iris Require Import WeakSailComplete WeakSailCone.
(* seam (6): the SHAPE half as a theorem over the axiom record, the
   LIVENESS half as a theorem over the residue record + [Hpriv] (§D 1) *)
From xv6iris Require Import WeakShapeMem WeakShapeTop WeakShapeLive.
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

(** A pointwise function update on [CPU] (the [dev_state] / [istream] twin of
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
    disk agent's own fabric state and [wstate] — determine one [wpcfg pxv6 unit],
    with the harts at indices [0 .. NCPU-1] and the disk at [NCPU]
    ([WeakLang.n_disk], [WeakCompose.xv6_ps]'s layout). *)

Record wlaux := WLAux {
  wa_dev  : CPU → dev_state;
  wa_iq   : CPU → istream;
  wa_dd   : dev_state;
  wa_dws  : wstate;
}.

Definition hag (g : wgstate) (u : wlaux) (c : CPU) : wpagent psail :=
  WPAgent (PSail None (wgregs g c) (wa_dev u c) None (wa_iq u c))
          (wgws g c) (∅ : gset nat).

(** The HART-ONLY configuration, at the [psail] program type. *)
Definition hcfg (g : wgstate) (u : wlaux) : wpcfg psail unit :=
  WPCfgU (img_z (wgimg g)) (wglog g) (hag g u <$> enum CPU).

Definition dkag (u : wlaux) : wpagent pxv6 :=
  WPAgent (PDisk (wa_dd u) []) (wa_dws u) (∅ : gset nat).

(** …and the full [pxv6] configuration: the harts embedded by
    [WeakCompose.lift_cfg], the disk agent framed at index [NCPU]. *)
Definition wl_cfg (g : wgstate) (u : wlaux) : wpcfg pxv6 unit :=
  lift_cfg [dkag u] (hcfg g u).

Lemma wl_cfg_alt g u :
  wl_cfg g u
  = WPCfgU (img_z (wgimg g)) (wglog g)
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

Lemma pf_run_no_promises (c c' : wpcfg pxv6 unit) :
  rtc (wp_pf_run (pstep_unit (pstep_xv6 riscv_step))) c c' → no_promises c → no_promises c'.
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

(** The three [wlaux] updates: a hart's private device fabric advances to
    what its own block's accesses produced, a hart's interrupt stream
    advances, the disk's own fabric/[wstate] are replaced. *)
Definition wl_dev (cpu : CPU) (d' : dev_state) (u : wlaux) : wlaux :=
  WLAux (cupd cpu d' (wa_dev u)) (wa_iq u) (wa_dd u) (wa_dws u).

Definition wl_iq (cpu : CPU) (iq' : istream) (u : wlaux) : wlaux :=
  WLAux (wa_dev u) (cupd cpu iq' (wa_iq u)) (wa_dd u) (wa_dws u).

Definition wl_dk (d' : dev_state) (ws' : wstate) (u : wlaux) : wlaux :=
  WLAux (wa_dev u) (wa_iq u) d' ws'.

(** REASSEMBLY, for a step that moved ONE HART: the configuration whose
    agent [cpu] has been replaced IS the corresponding configuration of the
    updated [WeakLang] state.  (The old file's [wl_cfg_hart_update], with the
    log freed — a hart block appends to it.) *)
Lemma wl_cfg_hart_upd g u cpu (g' : wgstate) (u' : wlaux) (st' : psail)
    (ws' : wstate) :
  wgimg g' = wgimg g → wa_dd u' = wa_dd u → wa_dws u' = wa_dws u →
  (∀ c, c ≠ cpu → hag g' u' c = hag g u c) →
  hag g' u' cpu = WPAgent st' ws' ∅ →
  WPCfgU (pc_img (wl_cfg g u)) (wglog g')
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
  WPCfgU (pc_img (wl_cfg g u)) (wglog g')
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

  Definition xhart (i : agent) (c : wpcfg pxv6 unit) : Prop :=
    ∃ ag q, pc_ags c !! i = Some ag ∧ pa_st ag = PHart q.

  Definition xat_bnd (i : agent) (c : wpcfg pxv6 unit) : Prop :=
    ∃ ag q, pc_ags c !! i = Some ag ∧ pa_st ag = PHart q ∧ sp_m q = None.

  Definition xin_blk (i : agent) (c : wpcfg pxv6 unit) : Prop :=
    ∃ ag q, pc_ags c !! i = Some ag ∧ pa_st ag = PHart q ∧ sp_m q ≠ None.

  Definition xpf_in_blk (i : agent) (c c' : wpcfg pxv6 unit) : Prop :=
    xin_blk i c ∧ pf_xsolo next i c c'.

  (** ONE INSTRUCTION BLOCK at [pxv6]: boundary, one step that loads the
      instruction, its events, boundary — no interior boundary. *)
  Definition xblk (i : agent) (c c' : wpcfg pxv6 unit) : Prop :=
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

  Lemma prj_lookup (q0 : psail) (i : agent) (c : wpcfg pxv6 unit) ag :
    pc_ags c !! i = Some ag → pc_ags (prj_cfg q0 c) !! i = Some (prj_ag q0 ag).
  Proof. intros H. by rewrite /prj_cfg /= list_lookup_fmap H. Qed.

  (** SPECIES IS PRESERVED: a solo step of a hart agent leaves a hart. *)
  Lemma pf_xsolo_hart (i : agent) (c c' : wpcfg pxv6 unit) :
    xhart i c → pf_xsolo next i c c' → xhart i c'.
  Proof.
    intros (agx & qx & Hax & Hstx) (l & Hstep & _ & _).
    destruct Hstep as
      [cfg ag st' dv Hlk Hps

      |cfg ag aq lat base tvs st' dv Hlk Hps Hr

      |cfg ag rl base data kk st' dv Hlk Hps Hne

      |cfg ag aq rl base tvs data kk st' dv Hlk Hps Hne Hlen Hr He

      |cfg ag pr pw sr sw st' dv Hlk Hps];
      simpl in Hax; rewrite Hlk in Hax; injection Hax as <-;
      rewrite Hstx /= in Hps;
      (destruct st' as [q'|dd pend]; [|done]);
      (eexists _, q'; simpl; split; [by eapply lookup_insert_self|done]).
  Qed.

  Lemma pf_xsolo_run_hart (i : agent) (c c' : wpcfg pxv6 unit) :
    xhart i c → rtc (pf_xsolo next i) c c' → xhart i c'.
  Proof.
    intros Hh Hrun. revert Hh. induction Hrun as [|x y z Hxy _ IH]; [done|].
    intros Hh. apply IH. by eapply pf_xsolo_hart.
  Qed.

  (** THE STEP PROJECTION. *)
  Lemma pf_xsolo_prj (q0 : psail) (i : agent) (c c' : wpcfg pxv6 unit) :
    xhart i c → pf_xsolo next i c c' →
    xhart i c' ∧ pf_solo next i (prj_cfg q0 c) (prj_cfg q0 c').
  Proof.
    intros (agx & qx & Hax & Hstx) (l & Hstep & Hcls & Hrmw).
    destruct Hstep as
      [cfg ag st' dv Hlk Hps

      |cfg ag aq lat base tvs st' dv Hlk Hps Hr

      |cfg ag rl base data kk st' dv Hlk Hps Hne

      |cfg ag aq rl base tvs data kk st' dv Hlk Hps Hne Hlen Hr He

      |cfg ag pr pw sr sw st' dv Hlk Hps]; destruct dv;
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
      + apply (PFSilent (pstep_unit (sail_step_ni next)) i (prj_cfg q0 cfg)
                 (prj_ag q0 ag) q' tt Hlks).
        rewrite /prj_ag /= Hstx. exact Hps.
      + intros ag2 msg Hag2 Heq. simpl in Heq.
        by destruct (app_snoc_absurd _ _ Heq).
      + exact I.
    - split.
      { exists (WPAgent (PHart q') (load_post_run (pa_ws ag) aq base tvs.*1)
                  (pa_prom ag)), q'. simpl.
        split; [by eapply lookup_insert_self|done]. }
      exists (WeakPromise.LLoad aq lat base tvs). split_and!.
      + apply (PFLoad (pstep_unit (sail_step_ni next)) i (prj_cfg q0 cfg)
                 (prj_ag q0 ag) aq lat base tvs q' tt Hlks);
          [rewrite /prj_ag /= Hstx; exact Hps|exact Hr].
      + intros ag2 msg Hag2 Heq. simpl in Heq.
        by destruct (app_snoc_absurd _ _ Heq).
      + exact I.
    - split.
      { eexists _, q'. simpl. split; [by eapply lookup_insert_self|done]. }
      exists (WeakPromise.LStore rl base data). split_and!.
      + apply (PFStore (pstep_unit (sail_step_ni next)) i (prj_cfg q0 cfg)
                 (prj_ag q0 ag) rl base data kk q' tt Hlks);
          [rewrite /prj_ag /= Hstx; exact Hps|exact Hne].
      + intros ag2 msg Hag2 Heq. simpl in Heq, Hag2.
        rewrite Hlks in Hag2. injection Hag2 as <-.
        exact (Hcls ag msg Hlk Heq).
      + exact I.
    - split.
      { eexists _, q'. simpl. split; [by eapply lookup_insert_self|done]. }
      exists (WeakPromise.LRmw aq rl base tvs data). split_and!.
      + apply (PFRmw (pstep_unit (sail_step_ni next)) i (prj_cfg q0 cfg)
                 (prj_ag q0 ag) aq rl base tvs data kk q' tt Hlks);
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
      + apply (PFFence (pstep_unit (sail_step_ni next)) i (prj_cfg q0 cfg)
                 (prj_ag q0 ag) pr pw sr sw q' tt Hlks).
        rewrite /prj_ag /= Hstx. exact Hps.
      + intros ag2 msg Hag2 Heq. simpl in Heq.
        by destruct (app_snoc_absurd _ _ Heq).
      + exact I.
  Qed.

  Lemma pf_xsolo_run_prj (q0 : psail) (i : agent) (c c' : wpcfg pxv6 unit) :
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

  Lemma xpf_in_blk_run_prj (q0 : psail) (i : agent) (c c' : wpcfg pxv6 unit) :
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

  Lemma xblk_split (i : agent) (n : nat) (c c' : wpcfg pxv6 unit) :
    relations.nsteps (pf_xsolo next i) n c c' → xhart i c → xat_bnd i c' →
    ∃ (k : nat) (ck : wpcfg pxv6 unit),
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
    ∀ (m : nat) (c c' : wpcfg pxv6 unit), (m ≤ n)%nat →
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

  Lemma xsolo_run_blocks (i : agent) (c c' : wpcfg pxv6 unit) :
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

(* ---------------------------------------------------------------- *)
(** *** BOUNDARY / IN-BLOCK, ACROSS [xcfg_eqv] AND ACROSS A DELIVERY *)

Lemma xat_bnd_m i c :
  xat_bnd i c →
  ∀ ag q, pc_ags c !! i = Some ag → pa_st ag = PHart q → sp_m q = None.
Proof.
  intros (ag2 & q2 & Hlk2 & Hst2 & Hm2) ag q Hlk Hst.
  have Hag : ag2 = ag by congruence. subst ag2.
  have Hq : q2 = q by congruence. by subst q2.
Qed.

Lemma xin_blk_m i c :
  xin_blk i c →
  ∀ ag q, pc_ags c !! i = Some ag → pa_st ag = PHart q → sp_m q ≠ None.
Proof.
  intros (ag2 & q2 & Hlk2 & Hst2 & Hm2) ag q Hlk Hst.
  have Hag : ag2 = ag by congruence. subst ag2.
  have Hq : q2 = q by congruence. by subst q2.
Qed.

Lemma xseip_ok_free i c : xin_blk i c → xseip_ok i c → xseip_free i c.
Proof.
  intros Hin Hok ag q Hlk Hst. apply (Hok ag q Hlk Hst).
  intros (Hm & _). exact (xin_blk_m i c Hin ag q Hlk Hst Hm).
Qed.

Lemma xat_bnd_eqv i c d : xcfg_eqv c d → xat_bnd i c → xat_bnd i d.
Proof.
  intros Heq (ag & q & Hlk & Hst & Hm).
  destruct (xcfg_eqv_lookup c d i ag Heq Hlk) as (ag' & Hlk' & (_ & _ & Hs)).
  rewrite Hst in Hs.
  destruct (pxv6_eqv_hart q (pa_st ag') Hs) as (b & Hb & Hqb).
  exists ag', b. split_and!; [exact Hlk'|exact Hb|].
  by rewrite -(proj1 (proj1 Hqb)).
Qed.

Lemma xin_blk_eqv i c d : xcfg_eqv c d → xin_blk i c → xin_blk i d.
Proof.
  intros Heq (ag & q & Hlk & Hst & Hm).
  destruct (xcfg_eqv_lookup c d i ag Heq Hlk) as (ag' & Hlk' & (_ & _ & Hs)).
  rewrite Hst in Hs.
  destruct (pxv6_eqv_hart q (pa_st ag') Hs) as (b & Hb & Hqb).
  exists ag', b. split_and!; [exact Hlk'|exact Hb|].
  by rewrite -(proj1 (proj1 Hqb)).
Qed.

Lemma xat_bnd_irq i c c' : pf_xirq i c c' → xat_bnd i c → xat_bnd i c'.
Proof.
  intros Hirq (ag & q & Hlk & Hst & Hm).
  destruct (pf_xirq_at i c c' Hirq)
    as (ag0 & ag' & q0 & q' & Hlk0 & Hst0 & Hlk' & Hst' & _ & _ & Hdel).
  have Hq : q0 = q by congruence. subst q0.
  destruct (irq_deliver_shape q q' Hdel) as (Hm' & _ & _).
  exists ag', q'. split_and!; [exact Hlk'|exact Hst'|by rewrite Hm'].
Qed.

Lemma xat_bnd_irq_back i c c' : pf_xirq i c c' → xat_bnd i c' → xat_bnd i c.
Proof.
  intros Hirq (ag' & q' & Hlk' & Hst' & Hm).
  destruct (pf_xirq_at i c c' Hirq)
    as (ag0 & ag2 & q0 & q2 & Hlk0 & Hst0 & Hlk2 & Hst2 & _ & _ & Hdel).
  have Hq : q2 = q' by congruence. subst q2.
  destruct (irq_deliver_shape q0 q' Hdel) as (Hm' & _ & _).
  exists ag0, q0. split_and!; [exact Hlk0|exact Hst0|by rewrite -Hm'].
Qed.

Lemma xin_blk_irq i c c' : pf_xirq i c c' → xin_blk i c → xin_blk i c'.
Proof.
  intros Hirq (ag & q & Hlk & Hst & Hm).
  destruct (pf_xirq_at i c c' Hirq)
    as (ag0 & ag' & q0 & q' & Hlk0 & Hst0 & Hlk' & Hst' & _ & _ & Hdel).
  have Hq : q0 = q by congruence. subst q0.
  destruct (irq_deliver_shape q q' Hdel) as (Hm' & _ & _).
  exists ag', q'. split_and!; [exact Hlk'|exact Hst'|by rewrite Hm'].
Qed.

Lemma xin_blk_irq_back i c c' : pf_xirq i c c' → xin_blk i c' → xin_blk i c.
Proof.
  intros Hirq (ag' & q' & Hlk' & Hst' & Hm).
  destruct (pf_xirq_at i c c' Hirq)
    as (ag0 & ag2 & q0 & q2 & Hlk0 & Hst0 & Hlk2 & Hst2 & _ & _ & Hdel).
  have Hq : q2 = q' by congruence. subst q2.
  destruct (irq_deliver_shape q0 q' Hdel) as (Hm' & _ & _).
  exists ag0, q0. split_and!; [exact Hlk0|exact Hst0|by rewrite -Hm'].
Qed.

Lemma xat_bnd_irq_rtc_back i c c' :
  rtc (pf_xirq i) c c' → xat_bnd i c' → xat_bnd i c.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [done|].
  intros Hb. eapply xat_bnd_irq_back; [exact Hxy|by apply IH].
Qed.

Lemma xin_blk_irq_rtc_back i c c' :
  rtc (pf_xirq i) c c' → xin_blk i c' → xin_blk i c.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [done|].
  intros Hb. eapply xin_blk_irq_back; [exact Hxy|by apply IH].
Qed.

Lemma at_pbnd_irq i c c' : pf_xirq i c c' → at_pbnd i c → at_pbnd i c'.
Proof.
  intros Hirq Hb ag2 Hlk2.
  destruct (pf_xirq_at i c c' Hirq)
    as (ag0 & ag' & q0 & q' & Hlk0 & Hst0 & Hlk' & Hst' & _ & _ & Hdel).
  have Hag : ag2 = ag' by congruence. subst ag2.
  have Hp := Hb ag0 Hlk0. rewrite Hst0 in Hp. destruct Hp as (Hm & Hf).
  destruct (irq_deliver_shape q0 q' Hdel) as (Hm' & Hf' & _).
  rewrite Hst' /=. split; [by rewrite Hm'|by rewrite Hf'].
Qed.

Lemma xat_bnd_at_pbnd i c : xat_bnd i c → xfence_free i c → at_pbnd i c.
Proof.
  intros Hb Hf ag2 Hlk2.
  destruct Hb as (ag & q & Hlk & Hst & Hm).
  have Hag : ag2 = ag by congruence. subst ag2.
  rewrite Hst /=. split; [exact Hm|exact (Hf ag q Hlk Hst)].
Qed.

Lemma xstep_hart i c c' : xhart i c → xstep i c c' → xhart i c'.
Proof.
  intros Hh [Hs|(_ & _ & Hirq)]; [by eapply pf_xsolo_hart|].
  destruct (pf_xirq_at i c c' Hirq)
    as (_ & ag' & _ & q' & _ & _ & Hlk' & Hst' & _). by exists ag', q'.
Qed.

Lemma xstep_rtc_hart i c c' : xhart i c → rtc (xstep i) c c' → xhart i c'.
Proof.
  intros Hh Hrun. revert Hh. induction Hrun as [|x y z Hxy _ IH]; [done|].
  intros Hh. apply IH. by eapply xstep_hart.
Qed.

(** A chain of deliveries at a boundary IS a chain of [SegIrq] segments. *)
Lemma xirq_chain_segs (i : agent) (z z' : wpcfg pxv6 unit) :
  rtc (pf_xirq i) z z' → at_pbnd i z →
  ∃ segs, chained2 segs z z' ∧ Forall seg2_fine segs ∧ at_pbnd i z'.
Proof.
  induction 1 as [x|x y z Hxy _ IH]; intros Hb.
  - exists []. split_and!; [done|constructor|exact Hb].
  - destruct (IH (at_pbnd_irq i x y Hxy Hb)) as (segs & Hch & Hall & Hb').
    exists (SegIrq i x y :: segs). split_and!; [by split| |exact Hb'].
    constructor; [by split|exact Hall].
Qed.

(* ---------------------------------------------------------------- *)
(** *** THE HART SEGMENT'S REFINEMENT — WHERE THE DELIVERIES COME OUT

    Since stage B a hart segment's run is a MIX of solo steps and
    interrupt deliveries ([WeakSailCone.xstep]); one [WeakLang] hart step
    is one delivery-free instruction and one [WeakLang] plic step is one
    delivery at an instruction boundary.  This induction walks the mixed
    run carrying the block under construction on the [WeakLang]-facing
    side: [dnd] is the end of its DELIVERY-FREE part, [dcur] is [dnd]
    with the deliveries commuted past it so far
    ([WeakSailCone.xirq_run_commute], i.e. [WeakSailComplete] §9's
    reordering), and the original run's configuration is [xcfg_eqv] to
    [dcur].  When the block ends, [dnd] is at a boundary, so the block is
    an [xblk] ([SegHart]) and the pending deliveries are boundary
    [SegIrq]s — exactly the shapes [wl_lift] consumes.

    THE PRICE, and it is the only one: the refined chain ends at an
    [xcfg_eqv]-related configuration rather than at the same one (no
    funext — [WeakSailComplete] §9 deviation (b)).  [violates_at] and
    [violation_hart] transport across it ([WeakSailCone]). *)

Definition xopen (i : agent) (dstart dnd dcur : wpcfg pxv6 unit) : Prop :=
  xat_bnd i dstart ∧
  (∃ c0, pf_xsolo riscv_step i dstart c0 ∧
         rtc (xpf_in_blk riscv_step i) c0 dnd) ∧
  rtc (pf_xirq i) dnd dcur ∧
  (dnd = dcur ∨ xseip_free i dnd).

Definition xrst (i : agent) (ccur dstart dnd dcur : wpcfg pxv6 unit) : Prop :=
  (dstart = dcur ∧ dnd = dcur ∧ xat_bnd i ccur ∧ at_pbnd i dcur)
  ∨ (xin_blk i ccur ∧ xopen i dstart dnd dcur).

Lemma xopen_close (i : agent) (dstart dnd dcur : wpcfg pxv6 unit) :
  xopen i dstart dnd dcur → xat_bnd i dnd → at_pbnd i dnd →
  ∃ segs, chained2 segs dstart dcur ∧ Forall seg2_fine segs ∧ at_pbnd i dcur.
Proof.
  intros (Hb0 & (c0 & Hs0 & Hrun) & Hirq & _) Hbnd Hpb.
  destruct (xirq_chain_segs i dnd dcur Hirq Hpb) as (segs & Hch & Hall & Hpb').
  exists (SegHart i dstart dnd :: segs). split_and!; [by split| |exact Hpb'].
  constructor; [|exact Hall].
  split_and!; [exact Hb0|exact Hbnd|by exists c0].
Qed.

Lemma xseg_refine (i : agent) (m : nat) :
  ∀ (ccur c' dstart dnd dcur : wpcfg pxv6 unit),
    relations.nsteps (xstep i) m ccur c' →
    xat_bnd i c' → xcfg_eqv ccur dcur → xrst i ccur dstart dnd dcur →
    ∃ segs df, chained2 segs dstart df ∧ Forall seg2_fine segs ∧
               xcfg_eqv c' df ∧ at_pbnd i df.
Proof.
  induction m as [|m IH]; intros ccur c' dstart dnd dcur Hst Hbf Heq Hinv.
  { inversion Hst; subst.
    destruct Hinv as [(Hds & Hdn & Hb & Hpb)|(Hin & _)].
    - exists [], dcur. split_and!; [exact Hds|constructor|exact Heq|exact Hpb].
    - by destruct (xat_bnd_not_in i c' Hbf Hin). }
  inversion Hst as [|m0 x y z Hxy Hyz Hm0 Hx Hz]; subst.
  have Hhc : xhart i ccur.
  { destruct Hinv as [(_ & _ & Hb & _)|(Hin & _)];
      [by apply xat_bnd_hart|by apply xin_blk_hart]. }
  destruct Hxy as [Hsolo|(Hseipc & Hfenc & Hirq)].
  - (* ================= AN IRQ-FREE STEP ================= *)
    destruct (pf_xsolo_eqv i ccur dcur y Heq Hsolo) as (dy & Hdy & Heqy).
    have Hhy : xhart i y := pf_xsolo_hart riscv_step i ccur y Hhc Hsolo.
    have Hnew : ∃ dstart2 dnd2 dcur2 dprev pre,
        chained2 pre dstart dstart2 ∧ Forall seg2_fine pre ∧
        xopen i dstart2 dnd2 dcur2 ∧ xcfg_eqv y dcur2 ∧
        pf_xsolo riscv_step i dprev dnd2.
    { destruct Hinv as [(Hds & Hdn & Hb & Hpb)
                       |(Hin & Hb0 & (c0 & Hs0 & Hrun) & Hirqr & Hdisj)].
      - (* opening a new block at the boundary *)
        subst dstart. subst dnd.
        exists dcur, dy, dy, dcur, []. split_and!;
          [done|constructor| |exact Heqy|exact Hdy].
        split_and!;
          [by eapply xat_bnd_eqv| |apply rtc_refl|by left].
        exists dy. split; [exact Hdy|apply rtc_refl].
      - (* extending the block that is open *)
        have Hind : xin_blk i dnd.
        { eapply xin_blk_irq_rtc_back; [exact Hirqr|by eapply xin_blk_eqv]. }
        destruct Hdisj as [Hde|Hfr].
        + subst dcur.
          exists dstart, dy, dy, dnd, []. split_and!;
            [done|constructor| |exact Heqy|exact Hdy].
          split_and!; [exact Hb0| |apply rtc_refl|by left].
          exists c0. split; [exact Hs0|].
          eapply rtc_r; [exact Hrun|by split].
        + destruct (xirq_run_commute i dnd dcur Hirqr dy Hfr Hdy)
            as (dnd2 & dcur2 & Hsolo2 & Hirq2 & Heq2).
          exists dstart, dnd2, dcur2, dnd, []. split_and!;
            [done|constructor| |by eapply xcfg_eqv_trans|exact Hsolo2].
          split_and!; [exact Hb0| |exact Hirq2|right].
          * exists c0. split; [exact Hs0|].
            eapply rtc_r; [exact Hrun|by split].
          * eapply xseip_free_step;
              [by eapply xin_blk_m|exact Hfr|exact Hsolo2]. }
    destruct Hnew
      as (dstart2 & dnd2 & dcur2 & dprev & pre & Hpre & Hprea & Hopen & Heqy2
          & Hprev).
    destruct (xhart_cases i y Hhy) as [Hby|Hiny].
    + (* the block ENDS: close it, and go on at a boundary *)
      have Hopen2 := Hopen. destruct Hopen2 as (_ & _ & Hirq2 & _).
      have Hbnd2 : xat_bnd i dnd2
        := xat_bnd_irq_rtc_back i dnd2 dcur2 Hirq2
             (xat_bnd_eqv i y dcur2 Heqy2 Hby).
      have Hpb2 : at_pbnd i dnd2.
      { apply xat_bnd_at_pbnd; [exact Hbnd2|].
        exact (pf_xsolo_bnd_fence i dprev dnd2 Hprev (xat_bnd_m i dnd2 Hbnd2)). }
      destruct (xopen_close i dstart2 dnd2 dcur2 Hopen Hbnd2 Hpb2)
        as (segs0 & Hch0 & Hall0 & Hpbc).
      destruct (IH y c' dcur2 dcur2 dcur2 Hyz Hbf Heqy2
                  (or_introl (conj eq_refl (conj eq_refl (conj Hby Hpbc)))))
        as (segs1 & df & Hch1 & Hall1 & Heqf & Hpbf).
      exists (pre ++ segs0 ++ segs1), df. split_and!;
        [|by apply Forall_app; split; [exact Hprea|apply Forall_app]
         |exact Heqf|exact Hpbf].
      eapply chained2_app; [exact Hpre|by eapply chained2_app].
    + (* the block CONTINUES *)
      destruct (IH y c' dstart2 dnd2 dcur2 Hyz Hbf Heqy2
                  (or_intror (conj Hiny Hopen)))
        as (segs1 & df & Hch1 & Hall1 & Heqf & Hpbf).
      exists (pre ++ segs1), df. split_and!;
        [by eapply chained2_app|by apply Forall_app|exact Heqf|exact Hpbf].
  - (* ================= A DELIVERY ================= *)
    destruct (pf_xirq_eqv i ccur dcur y Heq Hirq) as (dy & Hdy & Heqy).
    destruct Hinv as [(Hds & Hdn & Hb & Hpb)
                     |(Hin & Hb0 & (c0 & Hs0 & Hrun) & Hirqr & Hdisj)].
    + (* AT A BOUNDARY: a segment of its own *)
      subst dstart. subst dnd.
      have Hby : xat_bnd i y := xat_bnd_irq i ccur y Hirq Hb.
      destruct (IH y c' dy dy dy Hyz Hbf Heqy
                  (or_introl (conj eq_refl (conj eq_refl
                     (conj Hby (at_pbnd_irq i dcur dy Hdy Hpb))))))
        as (segs1 & df & Hch1 & Hall1 & Heqf & Hpbf).
      exists (SegIrq i dcur dy :: segs1), df. split_and!;
        [by split| |exact Heqf|exact Hpbf].
      constructor; [by split|exact Hall1].
    + (* MID-BLOCK: it joins the pending chain *)
      have Hiny : xin_blk i y := xin_blk_irq i ccur y Hirq Hin.
      have Hfr : xseip_free i dnd.
      { eapply xseip_free_irq_rtc_back; [exact Hirqr|].
        eapply xseip_free_eqv; [exact Heq|by apply xseip_ok_free]. }
      destruct (IH y c' dstart dnd dy Hyz Hbf Heqy
                  (or_intror (conj Hiny (conj Hb0
                     (conj (ex_intro _ c0 (conj Hs0 Hrun))
                        (conj (rtc_r _ _ _ Hirqr Hdy) (or_intror Hfr)))))))
        as (segs1 & df & Hch1 & Hall1 & Heqf & Hpbf).
      by exists segs1, df.
Qed.

Lemma seg2_hart_refine (i : agent) (c c' d : wpcfg pxv6 unit) :
  seg2_hart_ok i c c' → xcfg_eqv c d →
  ∃ segs df, chained2 segs d df ∧ Forall seg2_fine segs ∧ xcfg_eqv c' df.
Proof.
  intros ((ag & q & Hlk & Hst) & Hb & Hb' & Hrun) Heq.
  have Hbc : xat_bnd i c.
  { exists ag, q. split_and!; [exact Hlk|exact Hst|].
    have Hp := Hb ag Hlk. rewrite Hst in Hp. by destruct Hp. }
  have Hhc' : xhart i c'
    := xstep_rtc_hart i c c' (ex_intro _ ag (ex_intro _ q (conj Hlk Hst))) Hrun.
  have Hbc' : xat_bnd i c'.
  { destruct Hhc' as (ag2 & q2 & Hlk2 & Hst2). exists ag2, q2.
    split_and!; [exact Hlk2|exact Hst2|].
    have Hp := Hb' ag2 Hlk2. rewrite Hst2 in Hp. by destruct Hp. }
  apply rtc_nsteps in Hrun as (n & Hn).
  destruct (xseg_refine i n c c' d d d Hn Hbc' Heq
              (or_introl (conj eq_refl (conj eq_refl
                 (conj Hbc (at_pbnd_eqv i c d Heq Hb))))))
    as (segs & df & Hch & Hall & Heqf & _).
  by exists segs, df.
Qed.

Lemma seg2_refine (segs : list seg2) (c cf d : wpcfg pxv6 unit) :
  chained2 segs c cf → Forall seg2_ok segs → xcfg_eqv c d →
  ∃ segs' df, chained2 segs' d df ∧ Forall seg2_fine segs' ∧ xcfg_eqv cf df.
Proof.
  revert c d. induction segs as [|s segs IH]; intros c d Hch Hall Heq.
  { exists [], d. simpl in Hch. subst c.
    split_and!; [done|constructor|exact Heq]. }
  apply Forall_cons in Hall as [Hok Hall].
  destruct s as [i c1 c2|i c1 c2|i c1 c2]; simpl in Hch, Hok;
    destruct Hch as (Hsrc & Hch); subst c1.
  - destruct (seg2_hart_refine i c c2 d Hok Heq)
      as (sh & d2 & Hchh & Hallh & Heq2).
    destruct (IH c2 d2 Hch Hall Heq2) as (segs' & df & Hch' & Hall' & Heqf).
    exists (sh ++ segs'), df. split_and!;
      [by eapply chained2_app|by apply Forall_app|exact Heqf].
  - destruct (seg2_irq_ok_eqv i c c2 d Hok Heq) as (d2 & Hok2 & Heq2).
    destruct (IH c2 d2 Hch Hall Heq2) as (segs' & df & Hch' & Hall' & Heqf).
    exists (SegIrq i d d2 :: segs'), df. split_and!;
      [by split|by constructor|exact Heqf].
  - destruct (seg2_disk_ok_eqv i c c2 d Hok Heq) as (d2 & Hok2 & Heq2).
    destruct (IH c2 d2 Hch Hall Heq2) as (segs' & df & Hch' & Hall' & Heqf).
    exists (SegDisk i d d2 :: segs'), df. split_and!;
      [by split|by constructor|exact Heqf].
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
        (** THE MMIO SEAM, in its two satisfiable halves (WeakCompose §6(4)).
            (i) FABRIC AGREEMENT: this hart's private device automaton is
            the machine's at the start of the segment — the exact twin of
            [SegDisk]'s [wa_dd u = wgdev g]. *)
        wa_dev u cpu = wgdev g ∧
        (** (ii) DEVICE DECODABILITY along the segment's OWN run: every
            device access the block actually performed is one the partial
            [dev_read]/[dev_write] accepts.  Stated on the run, not on the
            monad — the ∀-path form is unsatisfiable (WeakCompose §6(4)). *)
        dev_ok_blk riscv_step i
          (prj_cfg (PSail None (wgregs g cpu) (wa_dev u cpu) None (wa_iq u cpu))
             c') ∧
        (** (iii) EXCLUSIVE-WINDOW FUSION along the same run: no step of the
            block took either HALF-WINDOW arm — the BARE exclusive read
            ([WeakSailLTS] delta (e)) or the STANDALONE conditional write
            (delta (e'')) — neither of which [wrun] reproduces (the first is
            a plain [LLoad] where the interpreter has an exclusive read; the
            second differs from [wrun]'s own write only in the message
            class).  Same shape as (ii) — run-local, target-indexed — and the
            same discharge family: per-image, kernel AMOs target mapped lock
            words and do not fault, so their windows close, and the kernel
            uses [amoswap], not [sc].  §B (O2)/(O4). *)
        fused_blk riscv_step i
          (prj_cfg (PSail None (wgregs g cpu) (wa_dev u cpu) None (wa_iq u cpu))
             c') ∧
        (∀ (tick : bool) (x : unit) (s' : wmstate),
           wrun (Some i) (riscv_step tick) (whart_view g cpu) x s' →
           wl_cfg (whart_write g cpu s') (wl_dev cpu (wm_dev s') u) = c' →
           wl_lift gen rest (whart_write g cpu s') (wl_dev cpu (wm_dev s') u))
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

Lemma wpcfg_eq {P : Type} (c1 c2 : wpcfg P unit) :
  pc_img c1 = pc_img c2 → pc_log c1 = pc_log c2 → pc_ags c1 = pc_ags c2 →
  c1 = c2.
Proof.
  destruct c1 as [i1 l1 d1 a1], c2 as [i2 l2 d2 a2]; destruct d1, d2; simpl.
  by intros -> -> ->.
Qed.

Theorem wl_lift_sound (gen : nat) (Hsh : ∀ b, sail_shaped (riscv_step b))
    (segs : list seg2) :
  ∀ (g : wgstate) (u : wlaux) (cf : wpcfg pxv6 unit),
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
    destruct Hlift as (cpu & -> & Hfab & Hdev & Hfus & Hcont).
    set (q0 := PSail None (wgregs g cpu) (wa_dev u cpu) None (wa_iq u cpu)).
    have Hlkp : pc_ags (prj_cfg q0 (wl_cfg g u)) !! (fin_to_nat cpu)
              = Some (WPAgent (PSail None (wgregs g cpu) (wgdev g) None
                                 (wa_iq u cpu)) (wgws g cpu) ∅).
    { rewrite -Hfab.
      exact (prj_lookup q0 _ _ _ (wl_cfg_hart_lookup g u cpu)). }
    have Hblk : sail_block riscv_step (fin_to_nat cpu)
                  (prj_cfg q0 (wl_cfg g u)) (prj_cfg q0 c')
      := xblk_prj riscv_step q0 (fin_to_nat cpu) (wl_cfg g u) c' Hfine.
    destruct (wprim_hart_block_bwd cpu gen g (wa_iq u cpu) ∅
                (prj_ag q0 <$> pc_ags (wl_cfg g u)) (prj_cfg q0 c')
                Hsh Hdev Hfus Hlive Hlkp Hblk)
      as (g2 & Hstep & Heq).
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
                     WPAgent (PSail None (wgregs (whart_write g cpu s') cpu) (wm_dev s') None (wa_iq u cpu))
                       (wgws (whart_write g cpu s') cpu) ∅]>
                   (prj_ag q0 <$> pc_ags (wl_cfg g u))
      := f_equal (@pc_ags psail unit) Heq.
    have Hcpu : prj_ag q0 agc
              = WPAgent (PSail None (wgregs (whart_write g cpu s') cpu) (wm_dev s') None (wa_iq u cpu))
                  (wgws (whart_write g cpu s') cpu) ∅.
    { have H : (prj_ag q0 <$> pc_ags c') !! fin_to_nat cpu
             = (<[fin_to_nat cpu :=
                    WPAgent (PSail None (wgregs (whart_write g cpu s') cpu) (wm_dev s') None (wa_iq u cpu))
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
    have Hagc : agc = WPAgent (PHart (PSail None (wgregs (whart_write g cpu s') cpu) (wm_dev s') None
                                        (wa_iq u cpu))) (wgws (whart_write g cpu s') cpu) ∅.
    { destruct agc as [st ws pr]. simpl in Hstc, Hcpu. rewrite Hstc in Hcpu |- *.
      by injection Hcpu as -> -> ->. }
    have Hceq : wl_cfg (whart_write g cpu s') (wl_dev cpu (wm_dev s') u) = c'.
    { symmetry.
      rewrite -(wl_cfg_hart_upd g u cpu (whart_write g cpu s') (wl_dev cpu (wm_dev s') u)
                  (PSail None (wgregs (whart_write g cpu s') cpu) (wm_dev s') None (wa_iq u cpu))
                  (wgws (whart_write g cpu s') cpu)).
      - apply wpcfg_eq; cbn [pc_img pc_log pc_ags].
        + rewrite Hximg. done.
        + exact (f_equal (@pc_log psail unit) Heq).
        + apply (list_eq_insert (pc_ags (wl_cfg g u)) (pc_ags c')).
          * by rewrite Hlkc Hagc.
          * eexists. apply wl_cfg_hart_lookup.
          * intros j Hj. by apply Hxfr.
      - done.
      - done.
      - done.
      - intros cc Hcc. rewrite /hag /whart_write /=.
        by rewrite (greg_insert_ne _ _ _ _ Hcc) (gws_insert_ne _ _ _ _ Hcc)
                   /wl_dev /= (cupd_ne _ _ _ _ Hcc).
      - by rewrite /hag /wl_dev /= cupd_eq. }
    have Hlive2 : wthread_live (whart_write g cpu s') gen.
    { destruct Hlive as [Hp Hg]. rewrite /wthread_live /whart_write /=.
      by split. }
    destruct (IH (whart_write g cpu s') (wl_dev cpu (wm_dev s') u) cf
                ltac:(by rewrite Hceq) Hall Hlive2
                (Hcont tick xx s' Hrun Hceq))
      as (g' & u' & Hcf & Hlive' & Hrun').
    exists g', u'. split_and!; [done|done|].
    eapply rtc_l; [|exact Hrun'].
    eapply pool_erased; [apply wpool_hart|exact Hstep].
  - (* ---------------- ONE INTERRUPT DELIVERY ---------------- *)
    destruct Hlift as (cpu & -> & Hwire).
    destruct Hfine as (Hbnd & Hxirq).
    have Hpfstep : wp_pf_step (pstep_unit (pstep_xv6 riscv_step)) (fin_to_nat cpu)
                     WeakPromise.LSilent (wl_cfg g u) c'
      := pf_xirq_pf_step riscv_step (fin_to_nat cpu) (wl_cfg g u) c'
           (xfence_free_bnd _ _ Hbnd) Hxirq.
    destruct (pf_xirq_at (fin_to_nat cpu) (wl_cfg g u) c' Hxirq)
      as (ag & ag' & q & q' & Hlk & Hst & Hlk' & Hst' & Hws & Hprom & Hdel).
    destruct (pf_xirq_frame (fin_to_nat cpu) (wl_cfg g u) c' Hxirq)
      as (Himg' & Hlog' & _ & Hfr).
    rewrite (wl_cfg_hart_lookup g u cpu) in Hlk. injection Hlk as <-.
    simpl in Hst. injection Hst as <-.
    destruct Hdel as (_ & v & iq & Hiq & Hq'). simpl in Hiq, Hq'.
    destruct (Hwire v iq Hiq) as (Hv & Hlift').
    have Hnp : no_promises c'
      := wp_pf_step_no_promises (pstep_unit (pstep_xv6 riscv_step)) (fin_to_nat cpu)
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
  (λ c, PSail None (wgregs g c) (wa_dev u c) None (wa_iq u c)) <$> enum CPU.

Definition xv6_ps0 (g : wgstate) (u : wlaux) : list pxv6 :=
  xv6_ps (wa_dd u) (xv6_harts g u).

(** In a FRESH ERA (empty log, every hart at [ws_init]) the wp machine's
    initial configuration IS the corresponding configuration. *)
Lemma wp_init_wl (g : wgstate) (u : wlaux) :
  wglog g = [] → (∀ c : CPU, wgws g c = ws_init) → wa_dws u = ws_init →
  wp_init (img_z (wgimg g)) tt (xv6_ps0 g u) = wl_cfg g u.
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
    (TS : ptraces pxv6 unit) : Prop :=
  ∀ (b1 b2 : gev) (segs : list seg2) (cf : wpcfg pxv6 unit),
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
Definition xv6_cone_premises (TS : ptraces pxv6 unit) : Prop :=
  (** [Hcq]: the post-state of a cross-edge source is quiet *)
  (∀ e1 e2, gdep2 TS e1 e2 → e1.1 ≠ e2.1 →
     ∀ T ag', pt_trs TS !! e1.1 = Some T →
       at_ags T !! S e1.2 = Some ag' → pquiet (pa_st ag')) ∧
  (** [Hseip]: a MID-BLOCK interrupt delivery interrupts a residual that
      never touches the [sig_seip] pin.  (Deliveries AT a boundary are
      unconstrained — this is strictly weaker than the retired [Hirqb],
      which demanded the boundary outright and so excluded the behaviors
      real hardware produces.) *)
  (∀ i T k ag ag' q q' l,
     pt_trs TS !! i = Some T →
     at_ags T !! k = Some ag → at_ags T !! S k = Some ag' →
     pa_st ag = PHart q → pa_st ag' = PHart q' →
     irq_deliver q l q' → ¬ pbnd (PHart q) → seip_free_psail q) ∧
  (** [Hpriv] (stage C9): every hart record's [cur_privilege] is one of the
      three privileges an H-less machine has.  It is the per-trace input of
      the LIVENESS half of seam (6) — [WeakShapeLive.riscv_step_live_ax]
      supplies liveness of a fresh instruction only at a [priv_ok] register
      file, and a boundary record is where that instruction is loaded.

      PER-IMAGE DISCHARGE: xv6 never enables the hypervisor extension
      (misa.H is clear at reset and no kernel store sets it), so
      [VirtualUser]/[VirtualSupervisor] are unreachable.  This is the same
      family as [Hcq]/[Hseip] — a per-image, checker-style fact — and its
      RECORDED UPGRADE PATH is the model-level reachability invariant
      ("[priv_ok] is preserved by [riscv_step] from a [priv_ok] reset
      state"), which would delete the premise outright.  Not attempted:
      it is a statement about the whole instruction set, i.e. the same
      sweep as [rv64d_live_residue] itself, and it is recorded rather than
      forced into this stage. *)
  (∀ i T k ag q,
     pt_trs TS !! i = Some T → at_ags T !! k = Some ag →
     pa_st ag = PHart q → priv_ok (sp_regs q)).

(** THE BUNDLE FACTS [robust_main]'s own proof derives from a behavior — and
    which the cone consumes.  Packaged so that the "no bad edge" premise of
    [robust_main_no_bad] may USE them rather than re-derive them. *)
Definition tb_facts {P D : Type} (pstep : P → D → wlabel → P → D → Prop)
    (nh : nat)
    (img : image) (ps : list P) (TS : ptraces P D) : Prop :=
  ptraces_wf pstep TS ∧ ptraces_ws_init TS ∧ (∀ a, co_tc TS a) ∧
  writes_fulfilled TS ∧ pt_img TS = img ∧
  length (pt_trs TS) = length ps ∧
  (∀ p m, pt_log TS !! p = Some m → wm_data m ≠ []) ∧
  (∀ j T ag0, pt_trs TS !! j = Some T →
     at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)) ∧
  ptraces_fwd_own TS ∧ ee_ok TS ∧ edges_split nh TS.

(** THE FULFILMENT ACCOUNTING ([WeakRobustTrace.wp_behavior_fulfil_once]'s
    fourth output), named so that [robust_main_no_bad] can TAKE a
    decomposition instead of re-deriving one — and so that the retag
    precomposition can hand it the canonical bundle's copy. *)
Definition fulfil_acct {P D : Type} (mid : wpcfg P D) (TS : ptraces P D)
    : Prop :=
  ∀ p m i, pc_log mid !! p = Some m → wm_tid m = Some i →
    ∃ T, pt_trs TS !! i = Some T ∧
      (∃ k ev, at_evs T !! k = Some ev ∧ ae_ts ev = Some (S p)) ∧
      (∀ k1 k2 ev1 ev2,
         at_evs T !! k1 = Some ev1 → ae_ts ev1 = Some (S p) →
         at_evs T !! k2 = Some ev2 → ae_ts ev2 = Some (S p) → k1 = k2).

(** …and it is class-blind, so it survives the retag. *)
Lemma fulfil_acct_retag {P D : Type} (f : nat → wm_class) (mid : wpcfg P D)
    (TS : ptraces P D) :
  fulfil_acct mid TS →
  fulfil_acct (WeakRetag.retag_cfg f mid) (WeakRetag.retag_traces f TS).
Proof.
  intros Hacct p m' i Hp Htid. simpl in Hp.
  apply WeakRetag.retag_log_lookup_inv in Hp as (m & Hm & ->).
  rewrite WeakRetag.retag_msg_tid in Htid.
  exact (Hacct p m i Hm Htid).
Qed.

(** THE REFUTATION.  A bad edge would give a minimal one, whose cone
    [WeakSailCone.cone_segments2] segments; the refinement cuts the hart
    segments into instructions; [cone_liftable] lifts the chain into the
    [WeakLang] machine; and φ at the state it reaches refutes the violation
    the cone exhibits.  So there is no bad edge. *)
Theorem xv6_no_bad_edge (gen : nat) (g0 : wgstate) (u0 : wlaux)
    (TS : ptraces pxv6 unit) :
  (∀ b, sail_shaped (riscv_step b)) →
  (∀ rs b, priv_ok rs → sail_live_st rs (riscv_step b)) →
  wthread_live g0 gen →
  wglog g0 = [] → (∀ cc : CPU, wgws g0 cc = ws_init) → wa_dws u0 = ws_init →
  img_total (img_z (wgimg g0)) →
  (∀ t2 g2, rtc (@erased_step weak_riscv_lang) (wpool gen, g0) (t2, g2) →
            no_violation (wglog g2) (wgws g2)) →
  bad_wf n_disk TS →
  (** the fabric scope, as everywhere on the archived per-hart track *)
  (∀ j T k ev, pt_trs TS !! j = Some T →
     at_evs T !! k = Some ev → ae_dev ev = None) →
  tb_facts (pstep_unit (pstep_xv6 riscv_step)) n_disk (img_z (wgimg g0))
    (xv6_ps0 g0 u0) TS →
  xv6_cone_premises TS →
  WeakRetag.cls_canonical lbl_class TS →
  cone_liftable gen g0 u0 TS →
  ∀ e1 e2, ¬ bad n_disk TS e1 e2.
Proof.
  intros Hsh Hslv Hlive Hlog0 Hws0 Hdws0 Himgt Hphi Hbwf Hdf
    (Hwf & Hwsi & Hco & Hwfl & Himg & Hnag & Hdata & Hps0 & Hfo & Hee & Hsplit)
    (Hcq & Hseip & Hpriv) Hcls Hcl e1 e2 Hbad.
  (** [Hres] IS DERIVED (WeakSailCone §13): the residual invariant follows
      from the two group-3 facts and the trace well-formedness already in
      hand.  Since stage D there is no device residue to re-establish, so
      the old [horc_prem] input is gone with it. *)
  have Hres : hres_prem TS
    := hres_derived TS (xv6_ps0 g0 u0) Hwf Hps0 (xv6_ps0_bnd g0 u0) Hsh Hslv
         Hpriv.
  destruct (Hbwf e1 e2 Hbad) as (f1 & f2 & Hbad' & Hmin).
  destruct (cone_segments2 TS (img_z (wgimg g0)) (xv6_ps0 g0 u0)
              Hwf Hwsi Hco Hwfl Himg Hnag Hdata Hdf Hps0 Hfo Hee n_disk Hsplit
              (xv6_ps0_bnd g0 u0) Hcq Hres Himgt Hseip Hcls f1 f2 Hbad' Hmin)
    as (segs & cf & Hch & Hok & _ & Hvio & Hbnd).
  rewrite (wp_init_wl g0 u0 Hlog0 Hws0 Hdws0) in Hch.
  (** THE REFINEMENT (§4): the hart segments become single blocks and the
      deliveries inside them are commuted out to their block boundaries.
      That is what moves the chain's end to an [xcfg_eqv]-related [df] —
      and the violation, being a statement about the log and the
      [wstate]s, moves with it. *)
  destruct (seg2_refine segs (wl_cfg g0 u0) cf (wl_cfg g0 u0) Hch Hok
              (xcfg_eqv_refl _)) as (segs' & df & Hch' & Hfine & Heqf).
  have Hviof : violation_hart cls_of pub_of n_disk df
    := xcfg_eqv_violation_hart n_disk cf df Heqf Hvio.
  have Hbndf : ∀ j ag, pc_ags df !! j = Some ag → pbnd (pa_st ag)
    := xcfg_eqv_bnd cf df Heqf Hbnd.
  have Hwl := Hcl f1 f2 segs' df Hbad' Hmin Hch' Hfine Hviof Hbndf.
  destruct (wl_lift_sound gen Hsh segs' g0 u0 df Hch' Hfine Hlive Hwl)
    as (g' & u' & Hcf & _ & Hrun).
  destruct (violation_hart_violates_at n_disk df Hviof)
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

Theorem robust_main_no_bad {P D : Type}
    (pstep : P → D → wlabel → P → D → Prop)
    (pdev : P → wlabel → P → bool)
    (nh : nat) (img : image) (d0 : D) (ps : list P)
    (c mid : wpcfg P D) (TS : ptraces P D) :
  lat_free_prog pstep → ts_oblivious pstep →
  rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid →
  ptraces_of pstep TS mid c →
  fulfil_acct mid TS →
  main_premises nh TS →
  (∀ j T k ev, pt_trs TS !! j = Some T →
     at_evs T !! k = Some ev → ae_dev ev = None) →
  (tb_facts pstep nh img ps TS → ∀ e1 e2, ¬ bad nh TS e1 e2) →
  ∃ cf, rtc (wp_pf_run pstep) (wp_init img d0 ps) cf ∧
        prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
Proof.
  intros Hlf Hobl Hprom Hof Hacct Hprem Hdf Hnb.
  destruct Hprem as (Hsplit & Hbwf & Hee & (sync & Hbytes)).
  (* the derived bundle facts — verbatim [robust_main]'s *)
  have Hwf : ptraces_wf pstep TS by eapply ptraces_of_wf.
  have Hla : log_authored (pc_log mid).
  { eapply log_authored_promise_run;
      [apply (log_authored_init img d0 ps)|exact Hprom]. }
  have Hwfl : writes_fulfilled TS
    by eapply (ptraces_of_writes_fulfilled pstep TS mid c).
  have Hlne : log_ne (pc_log mid).
  { eapply log_ne_promise_run; [apply (log_ne_init img d0 ps)|exact Hprom]. }
  have Hinit : cfg_ws_init mid.
  { eapply cfg_ws_init_promise_run;
      [apply (cfg_ws_init_init img d0 ps)|exact Hprom]. }
  have Hwsi : ptraces_ws_init TS by eapply (ptraces_of_ws_init pstep TS mid c).
  have Hfo : ptraces_fwd_own TS by eapply (ptraces_of_fwd_own pstep TS mid c).
  have Hco : ∀ a, co_tc TS a
    by eapply (co_serialized_pkg pstep pdev TS sync Hwf Hwfl Hbytes).
  destruct (promise_run_shape (wp_init img d0 ps) mid Hprom)
    as (Hpimg & Hplen & Hpdev & Hpst).
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
  { apply Hnb. by split_and!. }
  have Hacyc : gdep2_acyclic TS.
  { eapply (gdep2_acyclic_bad_free pstep nh TS Hwf Hfo Hee Hsplit).
    intros e1 e2 Hbe. by destruct (Hnobad e1 e2 Hbe). }
  eapply (sim_full pstep pdev TS (PDevs d0 []) img d0 ps Hwf Hwsi Hco Hwfl Hlf
            Hobl Himg1 Hlen1 Hdata1 Hps1 (ptraces_wit_nil TS d0 Hdf) eq_refl
            c (gdep3_acyclic_nodev TS d0 Hacyc)).
  - by rewrite Himg0 Hcimgc.
  - by rewrite Hlog0 Hclogc.
  - by rewrite Hclenc Hplen /wp_init /= length_map.
  - exact Hlst.
Qed.

(** THE HEADLINE, LIFTED: [WeakCompose.xv6_weak_robust] with
    [pf_violation_free_hart] replaced by the cone route's premises. *)
Corollary xv6_weak_robust_lifted (gen : nat) (g0 : wgstate) (u0 : wlaux)
    (c : wpcfg pxv6 unit) :
  rv64d_axiom_shapes →
  rv64d_live_residue →
  wthread_live g0 gen →
  wglog g0 = [] → (∀ cc : CPU, wgws g0 cc = ws_init) → wa_dws u0 = ws_init →
  img_total (img_z (wgimg g0)) →
  (∀ t2 g2, rtc (@erased_step weak_riscv_lang) (wpool gen, g0) (t2, g2) →
            no_violation (wglog g2) (wgws g2)) →
  (∀ (cb mid : wpcfg pxv6 unit) (TS : ptraces pxv6 unit),
     wp_behavior (pstep_unit (pstep_xv6 riscv_step)) (img_z (wgimg g0)) tt (xv6_ps0 g0 u0) cb →
     rtc (wp_promise_step (P := pxv6) (D := unit))
       (wp_init (img_z (wgimg g0)) tt (xv6_ps0 g0 u0)) mid →
     ptraces_of (pstep_unit (pstep_xv6 riscv_step)) TS mid cb →
     WeakRetag.cls_canonical lbl_class TS →
     main_premises n_disk TS ∧ xv6_cone_premises TS ∧
     cone_liftable gen g0 u0 TS) →
  wp_behavior (pstep_unit (pstep_xv6 riscv_step)) (img_z (wgimg g0)) tt (xv6_ps0 g0 u0) c →
  ∃ cf, rtc (wp_pf_run (pstep_unit (pstep_xv6 riscv_step)))
          (wp_init (img_z (wgimg g0)) tt (xv6_ps0 g0 u0)) cf ∧
        prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
Proof.
  intros Hax Hlvr Hlive Hlog0 Hws0 Hdws0 Himgt Hphi Hprem Hbeh.
  have Hsh := riscv_step_shaped_ax Hax.
  have Hslv := riscv_step_live_ax Hlvr.
  (** THE RETAG PRECOMPOSITION (premise-ledger stage A1).  [wm_ak] is an
      INERT tag, so retagging the behavior's own traced factorization at
      each message's fulfil pre-record ([WeakRetag.canon_f]) gives a
      CLASS-CANONICAL bundle of a behavior with the SAME [prog_of] and
      [mem_of] — and it is that bundle the pipeline runs on, which is why
      the supplier only ever has to serve canonical bundles.

      The retag is composed HERE rather than through
      [WeakRetag.behavior_canonical] because the pipeline also needs the
      FULFILMENT ACCOUNTING, which [behavior_canonical]'s own
      decomposition (a [wp_behavior_traced] one) does not carry: we take
      [wp_behavior_fulfil_once]'s bundle and retag THAT, transporting the
      accounting with [fulfil_acct_retag]. *)
  destruct (wp_behavior_fulfil_once_dev (pstep_unit (pstep_xv6 riscv_step))
              (λ _ _ _, false) (img_z (wgimg g0)) tt (xv6_ps0 g0 u0) c
              (xv6_pdev_ok riscv_step) (xv6_lat_free riscv_step) Hbeh)
    as (mid & TS & DS & Hprom & Hofd & Hnp & Hacct).
  have Hdf := ptraces_dev_of_free (pstep_unit (pstep_xv6 riscv_step))
                (λ _ _ _, false) TS DS mid c (λ _ _ _, eq_refl) Hofd.
  destruct Hofd as (Hof & _).
  have Hbeh' : wp_behavior (pstep_unit (pstep_xv6 riscv_step)) (img_z (wgimg g0))
                 tt (xv6_ps0 g0 u0)
                 (WeakRetag.retag_cfg (WeakRetag.canon_f lbl_class TS) c)
    := WeakRetag.wp_behavior_retag (pstep_unit (pstep_xv6 riscv_step))
         _ _ _ _ _ Hbeh.
  have Hprom' : rtc (wp_promise_step (P := pxv6) (D := unit))
                  (wp_init (img_z (wgimg g0)) tt (xv6_ps0 g0 u0))
                  (WeakRetag.retag_cfg (WeakRetag.canon_f lbl_class TS) mid).
  { rewrite -(WeakRetag.retag_wp_init (WeakRetag.canon_f lbl_class TS)
                (img_z (wgimg g0)) tt (xv6_ps0 g0 u0)).
    by apply WeakRetag.wp_promise_steps_retag. }
  have Hof' := WeakRetag.ptraces_of_retag (pstep_unit (pstep_xv6 riscv_step))
                 (WeakRetag.canon_f lbl_class TS) TS mid c Hof.
  have Hcwf : cfg_wf mid.
  { eapply (WeakRetag.cfg_wf_promise_run (pstep_unit (pstep_xv6 riscv_step)));
      [apply (cfg_wf_init (P := pxv6) (img_z (wgimg g0)) tt (xv6_ps0 g0 u0))
      |exact Hprom]. }
  have Hcanon : WeakRetag.cls_canonical lbl_class
                  (WeakRetag.retag_traces (WeakRetag.canon_f lbl_class TS) TS).
  { apply (WeakRetag.cls_canonical_canon (pstep_unit (pstep_xv6 riscv_step))
             (λ _ _ _, false)).
    - by destruct Hof as (_ & _ & _ & Hwft & _).
    - by eapply (WeakRetag.ts_pos_of_ptraces
                   (pstep_unit (pstep_xv6 riscv_step)) (λ _ _ _, false)). }
  destruct (Hprem _ _ _ Hbeh' Hprom' Hof' Hcanon) as (Hmain & Hcp & Hcl).
  destruct (robust_main_no_bad (pstep_unit (pstep_xv6 riscv_step))
              (λ _ _ _, false) n_disk
              (img_z (wgimg g0)) tt (xv6_ps0 g0 u0) _ _ _
              (xv6_lat_free riscv_step) (xv6_ts_oblivious riscv_step)
              Hprom' Hof' (fulfil_acct_retag _ mid TS Hacct) Hmain Hdf)
    as (cf & Hrun & Hpg & Hmm).
  { intros Htb.
    destruct Hmain as (_ & Hbwf & _ & _).
    by eapply (xv6_no_bad_edge gen g0 u0 _
                 Hsh Hslv Hlive Hlog0 Hws0 Hdws0 Himgt Hphi Hbwf Hdf Htb Hcp
                 Hcanon Hcl). }
  (** …and the conclusion comes back to [c]: the retag moves neither the
      program states nor the flat memory. *)
  exists cf. split_and!;
    [exact Hrun|by rewrite Hpg WeakRetag.prog_of_retag|].
  intros a. by rewrite Hmm WeakRetag.mem_of_retag.
Qed.

(** …and the same with the φ export produced ON THE SPOT by
    [WeakAdequacy.weak_system_adequacy_phi] from its WP premise package, so
    that the composition's only Iris-side obligation is the pool's WPs. *)
Corollary xv6_weak_robust_adequate Σ `{!riscvGpreS Σ, !weakGpreS Σ}
    `{GEN : GenId}
    (D : CPU -> gset register) (g0 : wgstate) (u0 : wlaux) (c : wpcfg pxv6 unit)
    (Hgid : gen_id = 0%nat)
    (Hpow : wgpow g0 = true) (Hgen0 : wggen g0 = 0%nat)
    (Hlog : wglog g0 = [])
    (Hws : forall cc : CPU, wgws g0 cc = ws_init)
    (Hdws : wa_dws u0 = ws_init) :
  rv64d_axiom_shapes →
  rv64d_live_residue →
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
  (∀ (cb mid : wpcfg pxv6 unit) (TS : ptraces pxv6 unit),
     wp_behavior (pstep_unit (pstep_xv6 riscv_step)) (img_z (wgimg g0)) tt (xv6_ps0 g0 u0) cb →
     rtc (wp_promise_step (P := pxv6) (D := unit))
       (wp_init (img_z (wgimg g0)) tt (xv6_ps0 g0 u0)) mid →
     ptraces_of (pstep_unit (pstep_xv6 riscv_step)) TS mid cb →
     WeakRetag.cls_canonical lbl_class TS →
     main_premises n_disk TS ∧ xv6_cone_premises TS ∧
     cone_liftable gen_id g0 u0 TS) →
  wp_behavior (pstep_unit (pstep_xv6 riscv_step)) (img_z (wgimg g0)) tt (xv6_ps0 g0 u0) c →
  ∃ cf, rtc (wp_pf_run (pstep_unit (pstep_xv6 riscv_step)))
          (wp_init (img_z (wgimg g0)) tt (xv6_ps0 g0 u0)) cf ∧
        prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
Proof.
  intros Hax Hlvr Hwp Himgt Hprem Hbeh.
  eapply (xv6_weak_robust_lifted gen_id g0 u0 c Hax Hlvr);
    [|exact Hlog|exact Hws|exact Hdws|exact Himgt| |exact Hprem|exact Hbeh].
  - split; [exact Hpow|]. by rewrite Hgen0 Hgid.
  - intros t2 g2 Hr.
    exact (proj1 (weak_system_adequacy_phi Σ (enum CPU) g0 D Hgid Hpow Hgen0
                    Hlog Hws Hwp t2 g2 Hr)).
Qed.
