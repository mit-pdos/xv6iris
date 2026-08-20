(** * WkYieldFrame.v — THE FRAMING PATTERN: ownership across a [yield]
      (φ-upgrade §1.5–§1.7)

    THE CONTEXT IS AMBIENT HERE (§1.7): §4's section takes ONE [`{CurCtx}]
    and every access site writes the bare [x ↦wo v].  The instance is THE SAME
    ONE on both sides of the migration — that is not an ergonomic detail but
    the claim the file exists to check: a thread's context is invariant across
    a yield (its hart is not), so §4b's resource on hart A and §4d's resource
    on hart B are literally the same proposition, and §4a's access block is
    ONE lemma applied twice with no context argument at all.  [ξ] survives
    explicitly only where it must: §2/§3/§5's park, resume and WP-altitude
    lemmas, which quantify over the context they park.

    THE POINT, in one sentence: a thread's ownership facts FRAME AROUND a call
    to [yield] — they appear in NEITHER its precondition NOR its
    postcondition — while [yield] internally fences on the old CPU before
    migrating and acquires on the new CPU before returning, and the only
    memory-visible thing it hands back is ONE persistent publication-floor
    token.

    [WkOwnPingPong] is the other migration test: there the byte's ownership
    is TRANSFERRED, through a lock payload, from one hart to another.  Here
    nothing is transferred at all — the same thread keeps everything it owns
    and merely changes CPU underneath itself.  That is the shape xv6's
    scheduler actually has, and it is the one that decides whether the C/D/S
    protocol's hart-indexed [WDirty] is a problem.  It is not — and, since
    Stage 1.6, it is not even visible: the points-to is indexed by the
    CONTEXT, the publication evidence rides in the scheduler's migration
    invariant, and the retarget happens inside the leaf.  §4a's access block
    is applied UNCHANGED before the yield (§4b) and after it (§4d).

    ==================== THE PROGRAM ====================

      thread T, running on hart A                  ... resumed on hart B
      -------------------------------------------  --------------------------
        sb  1, 0(x)      # x := 1   (D-A)
                         # z ↦w{q} vz in hand, CLEAN and untouched
        lb  a5, 0(x)     # reads 1   \
        sb  2, 0(x)      # x := 2     > §4a's ACCESS BLOCK, before the yield
        lb  a5, 0(z)     # reads vz  /
        call yield  --------------------------->
           fence rw,w    # arms w_relp                1: amoswap.w.aq a5,a4,0(hf)
           sw  zero,0(hf) # handoff release ========>     bnez a5,1b
                                                       ret
        <--------------------------------------------------
        lb  a5, 0(x)     # reads 1   \
        sb  2, 0(x)      # x := 2     > §4a's ACCESS BLOCK, AFTER the yield —
        lb  a5, 0(z)     # reads vz  /  the SAME lemma, the same script

    ==================== WHAT MAKES IT WORK ====================

    (1) THE FRAME IS LITERAL.  A thread's facts are held at ITS OWN INDEX; at
        the park they are FROZEN there ([WeakVProp.vwp_hold_freeze] — free,
        definitional), and [monPred_at P V] is an objective [iProp] that the
        yield lemmas simply do not mention.  §4's [wyf_park_frames] is
        [wyield_park_core] with the two facts threaded verbatim: its proof is
        the core plus [iFrame], which IS the claim.

    (2) WHAT COMES BACK IS TWO THINGS AND NO MORE.  From the park: the
        context's own migration invariant, in its parked form
        [WeakGhost.ctx_migr_all ξ] — a SCHEDULER resource, not a memory fact,
        and one the caller does nothing with but carry.  From the resume:
        [V ⊑ ws_view (wm_ws σ')] — the new hart's index dominates the parked
        one.  Neither mentions [x] or [z].  The second is delivered by the
        handoff flag's lock payload, which is a BARE VIEW RECEIPT
        ([wbaton] = [⊒V]) and carries no memory facts whatsoever.

        STAGE 1.5 RETURNED A THIRD THING, [pub_covers_view A V], because the
        caller had to spend it at the first touch of each dirty byte.  Its
        disappearance from this spec is the whole of Stage 1.6.

        AT THE PORT the raw [⊒V] becomes [WeakCtx.ctx_view_lb ξ V] (that is
        what crosses [WpNext.wp_next]); the example uses the lowered form only
        because its thread is not a registered [WeakCtx] context.  The two
        halves stay independent and both stay necessary — the view half is
        about what the context OBSERVED (it frames the CLEAN facts and says
        nothing about publication, which is deliberately not a view
        component), the publication half about what the world may READ of the
        old hart's writes (the lazy-upgrade evidence AND the φ payment).

    (3) BOTH FACTS FRAME FOR FREE, AND BY THE SAME LINE.  [z ↦w{q} vz] and
        [wpt_own ξ x 1] at [V] are both re-established at [B] by
        [vwp_hold_intro] and the view fact alone — see §4d, where the two
        thaws are literally the same tactic at different arguments.  The dirty
        byte's state element still says [WDirty A], and B is still not A; what
        changed is that nobody at this altitude has to care.  The retarget
        ([WeakGhost.wown_ctx_retarget]) fires inside the store leaf, out of the
        breadcrumb the points-to carries and the coverage the migration
        invariant supplies — and the timestamp side condition one would expect
        is ABSENT, because the breadcrumb and the coverage are both stated
        over VIEWS, so the points-to's own receipt [⊒(view_byte x t)]
        discharges it by construction.

    (4) φ COSTS NOTHING NEW, AND COSTS THE SAME LEMMA.  A foreign-dirty but
        PUBLISHED byte carries no [no_violation] obligation at all
        ([WeakGhost.nv_free_published]: the predicate only ever constrains
        UNPUBLISHED owned stores).  [WeakVProp.nv_ok_of_wpt_own] takes the
        owned points-to and the migration invariant and pays either way,
        BEFORE any ghost step — so §4e's obligation and an unmigrated
        thread's are discharged by the same application.

    ==================== WHAT IS NEW HERE VS. THE PING-PONG ====================

    Machinery: [WeakGhost.pub_floor] (the publication floor) +
    [wlat_flip_pure] (the floor-based D→C flip, which needs no premise about
    the log's top); [WeakGhost.ctx_wrote] / [ctx_migr] / [ctx_migr_all] (the
    breadcrumb and the migration invariant, φ-upgrade §1.6) and
    [wown_ctx_retarget] (the acceptance arm, now leaf-internal); and
    [WeakVProp.wpt_load_rule_own] (a thread reading its OWN dirty byte — which
    turns out to need no migration machinery at all).  Everything else below
    is composition. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac excl.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakGhost.
Require Import WeakExec.
Require Import WeakView.
Require Import WeakVProp.
Require Import WeakFence.
Require Import WeakBridge.
Require Import WeakInstr.
Require Import WeakStore.
Require Import WeakCert.
Require Import WeakViolation.
Require Import WeakLock.
Require Import WeakAcquire.
Require Import WkOwnPingPong.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import WpLock.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE SCHEDULER BATON — the handoff flag's payload

    A migration handoff transfers NO memory.  What it must transfer is the
    one thing a [vProp]-indexed assertion cannot carry across harts by
    itself: the INDEX.  So the flag's lock payload is a bare view receipt.

    It is not [emp] and it could not be: a thread's framed facts are frozen
    at the parking index [V], and re-establishing them on the new CPU is
    exactly [V ⊑ ws_view ws_B].  It is also not more than this — no [↦w], no
    [↦wo], nothing existentially quantified — which is what makes the yield
    specification below frame-shaped. *)

Section baton.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Definition wbaton (V : view) : vProp Σ := (⊒V)%I.

  Lemma wbaton_at V ws : vwp_hold (wbaton V) ws ⊣⊢ ⌜V ⊑ ws_view ws⌝.
  Proof. apply vwp_hold_seen. Qed.

  Lemma wbaton_intro V ws : V ⊑ ws_view ws → ⊢ vwp_hold (wbaton V) ws.
  Proof. intros H. rewrite wbaton_at. by iPureIntro. Qed.

  (** A [vProp] entailment applied at a FROZEN index — the [vwp_hold_ent] of
      the framing altitude.  (Everything a parked thread holds lives at such
      an index, so this is used wherever a rule is stated at [vwp_hold].) *)
  Lemma monPred_at_ent (P Q : vProp Σ) (V : view) :
    (P ⊢ Q) → monPred_at P V ⊢ monPred_at Q V.
  Proof. intros H. by apply H. Qed.

End baton.

(** The two byte values the thread writes, spelled the way [WeakLock] spells
    the lock word's. *)
Definition byte1 : bv 8 := (SailStdpp.Values.mword_of_int 1 : SailStdpp.Values.mword 8).
Definition byte2 : bv 8 := (SailStdpp.Values.mword_of_int 2 : SailStdpp.Values.mword 8).

Section yield.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.

(* ====================================================================== *)
(** ** 2. [yield_park] — the A-side: fence, handoff release, park the context

    THE SPEC SHAPE IS THE DELIVERABLE, and Stage 1.6 makes it sharper than
    Stage 1.5's.  Read the statement: its precondition is the machine's own
    state pieces plus the SCHEDULER's resources (the handoff flag's lock body,
    the holder token, and the context's migration invariant), and its
    postcondition returns exactly those, with the invariant in its PARKED form
    [ctx_migr_all].  There is no [↦w], no owned points-to — and, unlike Stage
    1.5, no [pub_covers_view] handed back to the caller either.

    THAT LAST ABSENCE IS THE STAGE.  Stage 1.5 returned the publication token
    because the CALLER had to spend it, at the first touch of each dirty byte
    after the migration.  Here the token is minted, spent against the
    migration invariant, and forgotten, all inside this lemma: what crosses
    the yield is a scheduler resource that mentions no byte, and the caller's
    access sites never learn that a migration happened.

    The [fence rw,w] is the caller's previous instruction and appears here as
    what it produces: the appended message is [WCrel] on the nose ([Hlog]),
    which the WP-altitude rule of §5 reads off the certificate's own trace
    with [WkOwnPingPong.wQ_eff_store_rel].  That single class fact is what
    makes the handoff store BORN-PUBLISHED, and hence what discharges the
    invariant's live-hart exception — no ghost operation on any of the
    thread's bytes is performed, or could be: the yield does not know which
    bytes they are. *)

  Lemma wyield_park_core (ξ : CtxId) (γ : gname) (hf : Arch.pa) (V : view)
      (i : CPU) (σ σ' : wmstate) :
    wQ_store (Some (fin_to_nat i)) hf lock_zero σ σ' →
    wm_log σ' =
      (wm_log σ ++ [wwrite_msg (Some (fin_to_nat i)) WCrel hf 4 lock_zero])%list →
    ws_bounded (wm_ws σ) (length (wm_log σ)) →
    (* the parking hart has observed [V] — a fact about its INDEX, not about
       any byte it owns *)
    V ⊑ ws_view (wm_ws σ) →
    wlog_auth (wm_log σ) -∗ ctx_migr ξ i -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ hf (wbaton V) -∗
    locked γ i ==∗
    wlog_auth (wm_log σ') ∗ ctx_migr_all ξ ∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wlock_inv γ hf (wbaton V).
  Proof.
    intros (Himg & _ & Hle & Hflr) Hlog Hbnd HV.
    iIntros "Hlog Hmg Hi Hinv Htok".
    iDestruct "Hinv" as (st t w) "(Hw & Ha & _)".
    iDestruct (locked_state with "Ha Htok") as %->.
    (* the flag word's bundle moves to the fresh top and stays CLEAN — a
       [WCrel] message is not an owned store *)
    iMod (wlat4L_store_gen (Some (fin_to_nat i)) WCrel σ σ' hf t w lock_zero
            (wlock_shaped_rel _ WCrel _ ltac:(discriminate)) Himg Hlog
            with "Hi Hw") as "[Hi Hw]".
    (* THE MINT.  The step's own message is this hart's, release-class, and at
       the log's fresh top — so it covers every earlier position at once. *)
    iMod (wlog_update (wm_log σ)
            [wwrite_msg (Some (fin_to_nat i)) WCrel hf 4 lock_zero]
            with "Hlog") as "Hlog".
    iDestruct (pub_floor_mint (wm_log σ)
                 (wwrite_msg (Some (fin_to_nat i)) WCrel hf 4 lock_zero) i
                 eq_refl eq_refl with "Hlog") as "[Hlog #Hpf]".
    (* THE PARK.  The floor covers every position the invariant's map records
       for this hart, so the live-hart exception discharges and the invariant
       re-forms in its parked form — at WHATEVER hart the context resumes on. *)
    assert (Hlen : (length (wm_log σ ++
              [wwrite_msg (Some (fin_to_nat i)) WCrel hf 4 lock_zero])
              <= S (length (wm_log σ)))%nat) by (rewrite length_app /=; lia).
    iDestruct (ctx_migr_park ξ i _ _ Hlen with "Hlog Hpf Hmg")
      as "[Hlog Hall]".
    (* the baton: the parking hart's own index, frozen at the store's
       timestamp — pure view arithmetic, [ws_bounded] and nothing else *)
    iAssert (monPred_at (wbaton V) (view_scl (S (length (wm_log σ)))))%I as "HR".
    { iApply (wwp_release_deposit (wbaton V) σ Hbnd).
      by iApply (wbaton_intro V (wm_ws σ) HV). }
    iMod (lock_clrcpu γ (Some (i, true)) i with "Ha Htok") as "(_ & Ha & Hpre)".
    iMod (lock_give γ (Some (i, false)) i with "Ha Hpre") as "(_ & Ha & Hfrag)".
    iModIntro. rewrite -Hlog. iFrame "Hlog Hall Hi".
    iExists None, (S (length (wm_log σ))), lock_zero.
    iFrame "Hw Ha". iLeft. iSplitR; [done|]. iSplitR; [done|].
    iFrame "Hfrag HR".
  Qed.

(* ====================================================================== *)
(** ** 3. [yield_resume] — the B-side: acquire the flag, install the index

    The other half, and it needs NO new machinery: [WeakLock.wacquire_core] at
    the baton payload, with the payload's decode ([wbaton_at]) applied on the
    far side, plus ONE line that re-forms the migration invariant at the
    resuming hart.  Its postcondition is one pure inequality about the
    RESUMING hart's index and one scheduler resource; again, no points-to.

    [ctx_migr_all_run] is that one line, and it is worth pausing on: the
    parked invariant carries publication coverage for EVERY hart, so it
    satisfies the running invariant at every hart.  Nothing about the
    resuming hart has to be checked, which is exactly why the scheduler is
    free to put the context wherever it likes.

    Two lemmas rather than one because there are two harts: [wlat_interp] is
    the authority over the latest-write map, so no proposition can hold it at
    the parking hart's state and at the resuming hart's later state at once
    ([WkStartedMp] §2's reason, verbatim).  The composed call shape is

      [wyield_park_core] … ==∗ … ∗ ctx_migr_all ξ
      ‹the machine runs; other harts run; the thread is not scheduled›
      [wyield_resume_core] … ==∗ … ∗ locked γ B ∗ ctx_migr ξ B ∗
                                     ⌜V ⊑ ws_view (wm_ws σ')⌝ *)

  Lemma wyield_resume_core (ξ : CtxId) (γ : gname) (hf : Arch.pa) (V : view)
      (i : CPU) (tid : option nat) (σ σ' : wmstate) :
    wlog_wf (wm_log σ) → acc_wf hf 4 →
    wQ_amo_aq tid hf lock_one σ σ' →
    (* the spin loop's successful attempt: the flag word read 0 *)
    (∀ j : nat, (j < 4)%nat →
       wflat (wm_img σ) (wm_log σ) !! pa_add hf j = Some (nth_byte lock_zero j)) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    ctx_migr_all ξ -∗
    wlock_inv γ hf (wbaton V) ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wlock_inv γ hf (wbaton V) ∗
    locked γ i ∗ ctx_migr ξ i ∗ ⌜V ⊑ ws_view (wm_ws σ')⌝.
  Proof.
    intros Hwf Hacc HQ Hzero. iIntros "Hi Hall Hinv".
    iDestruct (wacquire_core γ hf (wbaton V) i tid σ σ' Hwf Hacc HQ
                 with "Hi Hinv") as (v0) "[%Hflat Hupd]".
    assert (Hv : lock_zero = v0)
      by exact (wflat_word_agree σ hf lock_zero v0 Hzero Hflat).
    iMod "Hupd" as "(Hi & Hbody & Harm)".
    iDestruct "Harm" as "[(_ & HR & Htok)|%Hne]"; [|by rewrite -Hv in Hne].
    rewrite wbaton_at. iDestruct "HR" as %HV.
    iModIntro. iFrame "Hi Hbody Htok".
    iSplitL; [by iApply (ctx_migr_all_run with "Hall")|by iPureIntro].
  Qed.

End yield.

(* ====================================================================== *)
(** ** 4. THE EXAMPLE — thread T's own facts, framed around the yield

    Everything below is at the σ altitude, with T's facts appearing ONLY in
    T's own pre/post.  Compare the statements: §2's and §3's mention neither
    [x] nor [z]; §4's carry them, and their proofs are §2/§3 plus framing. *)

Section example.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.
  (** THREAD T'S CONTEXT, AMBIENT (φ-upgrade §1.7).  ONE instance for the
      whole section, and that is the substance rather than the notation: §4b
      runs on hart A and §4d runs on hart B, and both resolve [cur_ctx] to
      THIS hypothesis — so the [x ↦wo 1] that §4c frames and the [x ↦wo 1]
      that §4d thaws are not merely similar propositions, they are the SAME
      one, and the frame rule applies with nothing to prove.  That is exactly
      the property [CpuId] does not have (a thread's hart changes at the
      migration; its context does not), which is why the hart stays an
      explicit argument everywhere below and the context does not. *)
  Context `{XI : CurCtx}.

(* ---------------------------------------------------------------------- *)
(** *** 4a. THE ACCESS BLOCK — [load x; x := 2; load z]

    THIS LEMMA IS STAGE 1.6'S ACID TEST, and it is a test rather than a claim
    because of how it is USED: §4b instantiates it on hart A, BEFORE the
    yield, and §4d instantiates it on hart B, AFTER the migration, at a byte
    [x] that hart A dirtied and hart B has never touched.  Same lemma, same
    arguments, same script.  Nothing anywhere applies an upgrade.

    Under Stage 1.5 this was impossible: the post-migration load of [x] had to
    go through [wpt_own_upgrade] (or the composite [wpt_load_rule_pub]),
    against a [pub_covers_view] token the yield handed back, and the store
    after it re-owned at the new hart by hand — three lemma applications and a
    token the pre-migration site does not have.  What replaced them:

      - [WeakVProp.wpt_load_rule_own] needs NOTHING new, because a load moves
        no [wcds] state — a foreign-dirty byte reads through it verbatim;
      - [WkOwnPingPong.wpt_store_post_dirty] takes the migration invariant and
        the post-log authority, which are threaded at EVERY store site,
        migrated or not, and does the retarget inside;
      - the framed points-to is [wpt_own ξ], which is literally the same
        proposition on both harts, so it frames rather than converts.

    AND SINCE §1.7 THE CONTEXT IS NOT AN ARGUMENT EITHER: the two rules are
    quoted in their ambient form ([wpt_load_rule_own_cur],
    [wpt_store_post_dirty_cur]) and the resource is the bare [x ↦wo vx], so
    the statement below names a hart (which the machine supplies and which
    really does change) and no context at all. *)

  Lemma wyf_touch (c : CPU) (σ : wmstate) (m : wmsg)
      (x z : Z) (vx vz : bv 8) (q : dfrac)
      (akx akz : akinfo) (tx tz : nat) (bx bz : bv 8) (rl : bool) :
    ak_coh akx = false → wbyte_ok σ akx x tx bx →
    ak_coh akz = false → wbyte_ok σ akz z tz bz →
    msg_byte m x = Some byte2 →
    (∀ a', a' ≠ x → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat c) →
    wm_ak m = WCplain →
    wlog_auth ((wm_log σ ++ [m])%list) -∗ ctx_migr cur_ctx c -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (x ↦wo vx) (wm_ws σ) -∗
    vwp_hold (z ↦w{q} vz) (wm_ws σ) ==∗
    wlog_auth ((wm_log σ ++ [m])%list) ∗ ctx_migr cur_ctx c ∗
    wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list) ∗
    ⌜bx = vx⌝ ∗ ⌜bz = vz⌝ ∗
    vwp_hold (wpt_dirty cur_ctx c x byte2)
      (store_post (wm_ws σ) rl x (S (length (wm_log σ)))) ∗
    vwp_hold (z ↦w{q} vz)
      (store_post (wm_ws σ) rl x (S (length (wm_log σ)))).
  Proof.
    intros Hcohx Hokx Hcohz Hokz Hmb Hother Htid Hk.
    iIntros "Hlg Hmg Hi Hx Hz".
    (* --- load [x]: THE OWNED LOAD RULE, and nothing else --- *)
    iDestruct (wpt_load_rule_own_cur σ σ akx x vx tx bx
                 Hcohx Hokx eq_refl eq_refl ltac:(lia) with "Hi Hx")
      as "(%Hbx & Hi & Hx)".
    (* --- load [z]: the ordinary clean rule --- *)
    iDestruct (wpt_load_rule σ σ akz z q vz tz bz
                 Hcohz Hokz eq_refl eq_refl ltac:(lia) with "Hi Hz")
      as "(%Hbz & Hi & Hz)".
    (* --- [x := 2]: the ordinary owned store --- *)
    iMod (wpt_store_post_dirty_cur c σ m x vx byte2 rl
            Hmb Hother Htid Hk with "Hlg Hmg Hi Hx") as "(Hlg & Hmg & Hi & Hx)".
    iModIntro. iFrame "Hlg Hmg Hi Hx".
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iApply (vwp_hold_mono (z ↦w{q} vz)%I (wm_ws σ)); [|iExact "Hz"].
    apply store_post_le.
  Qed.

(* ---------------------------------------------------------------------- *)
(** *** 4b. ON HART A, BEFORE THE YIELD: dirty [x], then use it

    The store is [WkOwnPingPong.wpt_store_post_dirty] — which says "[WDirty
    A]" in its conclusion, so the framed fact visibly IS a dirty one — and
    then §4a's access block runs on hart A.  Keep this statement side by side
    with §4d's: they differ in the hart, the state and nothing else. *)

  Lemma wyf_store_and_use (A : CPU) (σ σ2 : wmstate) (m m2 : wmsg)
      (x z : Z) (v0 : bv 8) (vz : bv 8) (q : dfrac) (rl : bool)
      (akx akz : akinfo) (tx tz : nat) (bx bz : bv 8) :
    msg_byte m x = Some byte1 →
    (∀ a', a' ≠ x → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat A) →
    wm_ak m = WCplain →
    (* the access block's state has the same memory as the store's post-state *)
    wm_img σ2 = wm_img σ → wm_log σ2 = (wm_log σ ++ [m])%list →
    ws_le (store_post (wm_ws σ) rl x (S (length (wm_log σ)))) (wm_ws σ2) →
    ak_coh akx = false → wbyte_ok σ2 akx x tx bx →
    ak_coh akz = false → wbyte_ok σ2 akz z tz bz →
    msg_byte m2 x = Some byte2 →
    (∀ a', a' ≠ x → msg_byte m2 a' = None) →
    wm_tid m2 = Some (fin_to_nat A) →
    wm_ak m2 = WCplain →
    wlog_auth ((wm_log σ ++ [m])%list) -∗ ctx_migr cur_ctx A -∗
    wlog_auth ((wm_log σ2 ++ [m2])%list) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (x ↦wo v0) (wm_ws σ) -∗
    vwp_hold (z ↦w{q} vz) (wm_ws σ) ==∗
    wlog_auth ((wm_log σ2 ++ [m2])%list) ∗ ctx_migr cur_ctx A ∗
    wlat_interp (wm_img σ2) ((wm_log σ2 ++ [m2])%list) ∗
    ⌜bx = byte1⌝ ∗ ⌜bz = vz⌝ ∗
    vwp_hold (wpt_dirty cur_ctx A x byte2)
      (store_post (wm_ws σ2) rl x (S (length (wm_log σ2)))) ∗
    vwp_hold (z ↦w{q} vz)
      (store_post (wm_ws σ2) rl x (S (length (wm_log σ2)))).
  Proof.
    intros Hma Hother Htid Hk Himg Hlg Hle Hcohx Hokx Hcohz Hokz
           Hmb Hother2 Htid2 Hk2.
    iIntros "Hlg1 Hmg Hlg2 Hi Hx Hz".
    iMod (wpt_store_post_dirty_cur A σ m x v0 byte1 rl
            Hma Hother Htid Hk with "Hlg1 Hmg Hi Hx") as "(_ & Hmg & Hi & Hx)".
    (* the clean fact rides the same step's view growth, and nothing else *)
    iDestruct (vwp_hold_mono (z ↦w{q} vz)%I (wm_ws σ) _ (store_post_le _ _ _ _)
                 with "Hz") as "Hz".
    rewrite -Himg -Hlg.
    iDestruct (vwp_hold_mono _ _ _ Hle with "Hx") as "Hx".
    iDestruct (vwp_hold_mono _ _ _ Hle with "Hz") as "Hz".
    (* ---- THE ACCESS BLOCK, ON HART A ---- *)
    iMod (wyf_touch A σ2 m2 x z byte1 vz q akx akz tx tz bx bz rl
            Hcohx Hokx Hcohz Hokz Hmb Hother2 Htid2 Hk2
            with "Hlg2 Hmg Hi [Hx] Hz")
      as "($ & $ & $ & $ & $ & $ & $)"; [|done].
    by iApply (vwp_hold_ent _ _ _ (wpt_dirty_own cur_ctx A x byte1)).
  Qed.

(* ---------------------------------------------------------------------- *)
(** *** 4c. THE PARK, WITH T'S FACTS IN THE FRAME

    THE STATEMENT IS THE POINT.  This is [wyield_park_core] verbatim with two
    conjuncts threaded from premise to conclusion, untouched; the proof is the
    core plus [iFrame].  Nothing about [x] or [z] is used, and nothing about
    them could be used — the yield does not know they exist.

    NOTE THAT THE TWO FRAMED FACTS ARE TREATED IDENTICALLY.  Under Stage 1.5
    the dirty one was [wpt_dirty A …], a proposition about hart A, and it
    survived only because it was FROZEN at an index and re-thawed by hand;
    here it is [wpt_own ξ …], a proposition about the context, and it frames
    for exactly the reason the clean [z ↦w{q} vz] does.  The freeze is still
    used below — it is how a [vProp] crosses a state change at all — but it is
    now the same freeze for both. *)

  Corollary wyf_park_frames (γ : gname) (hf : Arch.pa) (A : CPU)
      (σ σ' : wmstate) (x z : Z) (vx vz : bv 8) (q : dfrac) :
    wQ_store (Some (fin_to_nat A)) hf lock_zero σ σ' →
    wm_log σ' =
      (wm_log σ ++ [wwrite_msg (Some (fin_to_nat A)) WCrel hf 4 lock_zero])%list →
    ws_bounded (wm_ws σ) (length (wm_log σ)) →
    wlog_auth (wm_log σ) -∗ ctx_migr cur_ctx A -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ hf (wbaton (ws_view (wm_ws σ))) -∗
    locked γ A -∗
    (* ------------------------ THE FRAME ------------------------ *)
    monPred_at (x ↦wo vx) (ws_view (wm_ws σ)) -∗
    monPred_at (z ↦w{q} vz) (ws_view (wm_ws σ)) ==∗
    (* ----------------------------------------------------------- *)
    wlog_auth (wm_log σ') ∗ ctx_migr_all cur_ctx ∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    wlock_inv γ hf (wbaton (ws_view (wm_ws σ))) ∗
    monPred_at (x ↦wo vx) (ws_view (wm_ws σ)) ∗
    monPred_at (z ↦w{q} vz) (ws_view (wm_ws σ)).
  Proof.
    intros HQ Hlog Hbnd. iIntros "Hlog Hmg Hi Hinv Htok Hx Hz".
    (* the scheduler lemma is [ξ]-EXPLICIT — it quantifies over the context it
       parks — so the seam between the two worlds is this one argument *)
    iMod (wyield_park_core cur_ctx γ hf (ws_view (wm_ws σ)) A σ σ' HQ Hlog Hbnd
            ltac:(reflexivity) with "Hlog Hmg Hi Hinv Htok")
      as "($ & $ & $ & $)".
    by iFrame "Hx Hz".
  Qed.

(* ---------------------------------------------------------------------- *)
(** *** 4d. ON HART B: resume, then USE the framed facts

    The resume installs the index and re-forms the migration invariant; then
    BOTH framed facts are thawed by [vwp_hold_intro] and the view fact alone —
    the dirty one exactly like the clean one — and §4a's access block runs.

    COMPARE WITH §4b LINE BY LINE.  The access block's application is
    character-for-character the same:

      §4b   iMod (wyf_touch A σ2 m2 x z byte1 vz q akx akz tx tz bx bz rl
                    Hcohx Hokx Hcohz Hokz Hmb Hother2 Htid2 Hk2
                    with "Hlg2 Hmg Hi [Hx] Hz") …
      §4d   iMod (wyf_touch B σn mB x z byte1 vz q akx akz tx tz bx bz rl
                    Hcohx Hokx Hcohz Hokz Hmb Hother Htid Hk
                    with "Hlog Hmg Hi Hx Hz") …

    and since §1.7 the context is not even an argument: both lines resolve
    [cur_ctx] to the SECTION'S ONE INSTANCE, so the resource [x ↦wo …] that
    §4b consumes and the one §4d consumes are the same proposition — which is
    the whole reason the ambient reading is sound here and was not for the
    hart.  In §4d the byte [x] is still [WDirty A] in the ghost map when that
    line runs.  There is no upgrade lemma in this proof, and no token
    threaded to make one possible. *)

  Lemma wyf_resume_and_use (γ : gname) (hf : Arch.pa) (V : view)
      (B : CPU) (tid : option nat) (σ σ' σn : wmstate) (mB : wmsg)
      (x z : Z) (vz : bv 8) (q : dfrac)
      (akx akz : akinfo) (tx tz : nat) (bx bz : bv 8) (rl : bool) :
    (* --- the resume --- *)
    wlog_wf (wm_log σ) → acc_wf hf 4 →
    wQ_amo_aq tid hf lock_one σ σ' →
    (∀ j : nat, (j < 4)%nat →
       wflat (wm_img σ) (wm_log σ) !! pa_add hf j = Some (nth_byte lock_zero j)) →
    (* --- and then T's own three accesses, at a state with the same memory --- *)
    wm_img σn = wm_img σ' → wm_log σn = wm_log σ' →
    ws_le (wm_ws σ') (wm_ws σn) →
    ak_coh akx = false → wbyte_ok σn akx x tx bx →
    ak_coh akz = false → wbyte_ok σn akz z tz bz →
    msg_byte mB x = Some byte2 →
    (∀ a', a' ≠ x → msg_byte mB a' = None) →
    wm_tid mB = Some (fin_to_nat B) →
    wm_ak mB = WCplain →
    wlog_auth ((wm_log σn ++ [mB])%list) -∗
    (* the ONLY things the yield handed back: a lock body and a scheduler
       resource.  Neither mentions [x] or [z]. *)
    ctx_migr_all cur_ctx -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ hf (wbaton V) -∗
    (* the FRAMED facts, still frozen at the parking index — and [x ↦wo byte1]
       is §4c's conjunct on the nose, the same instance on both sides *)
    monPred_at (x ↦wo byte1) V -∗
    monPred_at (z ↦w{q} vz) V ==∗
    wlog_auth ((wm_log σn ++ [mB])%list) ∗ ctx_migr cur_ctx B ∗
    wlat_interp (wm_img σn) ((wm_log σn ++ [mB])%list) ∗
    wlock_inv γ hf (wbaton V) ∗ locked γ B ∗
    (* the load of [x] returned what A wrote; [z] returned what T framed *)
    ⌜bx = byte1⌝ ∗ ⌜bz = vz⌝ ∗
    (* [x] is now DIRTY AT B — the author alternated across a migration with
       no transfer and no payload *)
    vwp_hold (wpt_dirty cur_ctx B x byte2)
      (store_post (wm_ws σn) rl x (S (length (wm_log σn)))) ∗
    (* ... and [z] is still T's, clean, at the new hart *)
    vwp_hold (z ↦w{q} vz)
      (store_post (wm_ws σn) rl x (S (length (wm_log σn)))).
  Proof.
    intros Hwf Hacc HQ Hzero Himg Hlg Hle Hcohx Hokx Hcohz Hokz
           Hmb Hother Htid Hk.
    iIntros "Hlog Hall Hi Hinv Hx Hz".
    (* --- the resume: the index and the invariant arrive, and nothing else --- *)
    iMod (wyield_resume_core cur_ctx γ hf V B tid σ σ' Hwf Hacc HQ Hzero
            with "Hi Hall Hinv") as "(Hi & Hbody & Htok & Hmg & %HV)".
    (* carry everything to the state T's own accesses run at *)
    assert (HVn : V ⊑ ws_view (wm_ws σn))
      by (etrans; [exact HV|by apply ws_view_mono]).
    rewrite -Himg -Hlg.
    (* --- the FRAMED facts, thawed by the view alone.  TWO IDENTICAL LINES:
           the dirty byte and the clean byte cost exactly the same. --- *)
    iDestruct (vwp_hold_intro V (x ↦wo byte1)%I (wm_ws σn) HVn with "Hx")
      as "Hx".
    iDestruct (vwp_hold_intro V (z ↦w{q} vz)%I (wm_ws σn) HVn with "Hz")
      as "Hz".
    (* ---- THE ACCESS BLOCK, ON HART B — §4b's line, at the new hart ---- *)
    iMod (wyf_touch B σn mB x z byte1 vz q akx akz tx tz bx bz rl
            Hcohx Hokx Hcohz Hokz Hmb Hother Htid Hk
            with "Hlog Hmg Hi Hx Hz")
      as "($ & $ & $ & $ & $ & $ & $)".
    by iFrame "Hbody Htok".
  Qed.

(* ---------------------------------------------------------------------- *)
(** *** 4e. THE φ PAYMENT OF THE MIGRATED THREAD'S FIRST TOUCH

    Every instruction fetches, so every leaf owes [nv_hart] at its post-log,
    one [WeakGhost.nv_byte] per byte its trace touches ([WeakCert]'s
    reduction).  The migrated thread's load of [x] touches a byte that is
    still [WDirty A] at that moment and the reading hart is [B ≠ A] — the one
    configuration neither [nv_ok_of_own_st] (wrong hart) nor
    [nv_ok_of_pointsto] (not clean) can pay.

    IT IS PAID BY THE SAME LEMMA A NON-MIGRATED THREAD USES.  [nv_ok_of_wpt_own]
    takes the owned points-to, the migration invariant and the log authority —
    all three present at every access site — and does the case analysis
    internally: own-dirty pays through the state element, foreign-dirty pays
    because a published owned store is not a violation to anybody.  Compare
    with §4b's φ obligation, which is this lemma at [c := A]. *)

  Lemma wyf_phi_migrated (B : CPU) (V : view) (img : _)
      (log : list wmsg) (pcb x : Z) (vx : bv 8) :
    latest_ts log pcb = 0%nat →
    wlog_auth log -∗ ctx_migr cur_ctx B -∗ wlat_interp img log -∗
    monPred_at (x ↦wo vx) V -∗
    ⌜nv_ok log B pcb ∧ nv_ok log B x⌝.
  Proof.
    intros Htext. iIntros "Hlog Hmg Hi Hx".
    iDestruct (nv_ok_of_wpt_own_cur B x vx V img log log
                 (pub_transfer_refl log B) with "Hlog Hmg Hi Hx") as %Hnx.
    iPureIntro. split; [by apply nv_ok_unwritten|exact Hnx].
  Qed.

End example.

(* ====================================================================== *)
(** ** 5. THE PARK AT THE WP ALTITUDE — one [sw] through the handoff flag

    [WeakAcquire.wwp_release_store] with two changes and no more:

      - the callback hands over NO payload at all (contrast [wrel_cb], which
        hands over [vwp_hold R (wm_ws σ)]); what it hands over is the pure
        fact that the parking hart has observed [V], which is not a resource;
      - the post-step continuation is handed the PARKED MIGRATION INVARIANT.
        It is delivered AFTER the continuation has returned the state
        remainder, because the log authority the mint rides lives in that
        remainder — which is why the continuation's type ends in
        [ctx_migr_all ξ -∗ WWP Loop] rather than taking it up front.

    NOTHING MEMORY-SHAPED CROSSES THIS SPEC.  Stage 1.5's version ended in
    [pub_covers_view cpu_id V -∗ WWP Loop] — a token about what hart [cpu_id]
    had published, which the caller then had to spend at each dirty byte.
    What crosses now is the scheduler's own resource, and the caller does
    nothing with it but carry it.

    The class fact the mint needs is read off the certificate's own trace by
    [WkOwnPingPong.wQ_eff_store_rel], exactly as the ping-pong's release does;
    the φ payment is [wwp_release_store]'s verbatim. *)

Section wp_yield.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition wyield_park_cb (ξ : CtxId) (V : view)
      (pc : SailStdpp.Values.mword 64) (P : wmstate → Prop) : iProp Σ :=
    (∀ σ : wmstate,
       wlat_interp (wm_img σ) (wm_log σ) -∗
       wmstate_rest σ ={⊤ ∖ ↑wlockN, ∅}=∗
         ⌜register_lookup PC (wm_regs σ) = pc⌝ ∗
         ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pc j)⌝ ∗
         ⌜P σ⌝ ∗
         ⌜∀ j : nat, (j < 4)%nat → nv_ok (wm_log σ) cpu_id (acc_addr pc j)⌝ ∗
         (* the [fence rw,w] at [pc-4]: what makes the handoff store [WCrel],
            hence BORN-PUBLISHED, hence the mint site *)
         ⌜w_relp (wm_ws σ) = true⌝ ∗
         (* the parked index — a fact, not a resource *)
         ⌜V ⊑ ws_view (wm_ws σ)⌝ ∗
         wlat_interp (wm_img σ) (wm_log σ) ∗
         ∃ t0 t1 : mstate,
           ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝ ∗
           ⌜exec (riscv_step true) (wflat_st σ) = Some (tt, t1)⌝ ∗
           ▷ (∀ (tick : bool) (σ' : wmstate),
                ⌜wstep_post σ σ' (if tick then t1 else t0)⌝ -∗
                |={∅, ⊤ ∖ ↑wlockN}=> wmstate_rest_nonv σ' ∗
                  (* THE WHOLE POSTCONDITION OF THE PARK — and it names no
                     byte, no view and no hart's publication state *)
                  (ctx_migr_all ξ -∗ WWP Loop)))%I.

  Lemma wwp_yield_park (ξ : CtxId) (γ : gname) (hf : Arch.pa) (V : view)
      (pc : SailStdpp.Values.mword 64)
      (akf : akinfo) (pf : Arch.pa) (nf : N) (akw : akinfo) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    acc_wf hf 4 →
    (* the handoff store is a plain [sw], not an AMO *)
    ak_latest akw = false →
    (∀ a : Z, weff_touches (WEread akf pf nf) a →
       ∃ j : nat, (j < 4)%nat ∧ a = acc_addr pc j) →
    inv wlockN (wlock_inv γ hf (wbaton V)) -∗
    locked γ cpu_id -∗
    ctx_migr ξ cpu_id -∗
    wyield_park_cb ξ V pc
      (wP_eff (Some (fin_to_nat cpu_id))
         [WEread akf pf nf; WEwrite akw hf 4 lock_zero]) -∗
    WWP Loop.
  Proof.
    intros Hgid Haccpc Hacchf Hlatw Hfetch. iIntros "#Hinv Htok Hmg Hk".
    rewrite /wyield_park_cb.
    assert (Hfoot : ∀ a : Z,
              weffs_touch [WEread akf pf nf; WEwrite akw hf 4 lock_zero] a →
              (∃ j : nat, (j < 4)%nat ∧ a = acc_addr pc j) ∨
              (∃ j : nat, (j < 4)%nat ∧ a = acc_addr hf j)).
    { intros a Ha. apply weffs_touch_cons in Ha as [Ha|Ha].
      - left. by apply Hfetch.
      - right. destruct (weffs_touch_write1 _ hf _ _ a Ha) as (j & Hj & ->).
        exists j. split; [cbn in Hj; lia|done]. }
    iApply (wp_winstr pc
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread akf pf nf; WEwrite akw hf 4 lock_zero])
              (wQ_fr (wQ_store (Some (fin_to_nat cpu_id)) hf lock_zero)
                     (Some (fin_to_nat cpu_id))
                     [WEread akf pf nf; WEwrite akw hf 4 lock_zero])
              Hgid Haccpc).
    { apply wstep_cert_fr.
      exact (wcert_store (fin_to_nat cpu_id) pc akf pf nf akw hf lock_zero). }
    iIntros (σ) "Hσ".
    iDestruct (wmstate_interp_split σ with "Hσ") as "[Hlat Hrest]".
    iDestruct (wmstate_rest_facts with "Hrest") as %[Hbnd Hwf].
    iDestruct (wmstate_rest_nv with "Hrest") as %Hnvσ.
    iInv wlockN as "Hbody" "Hclose".
    iMod ("Hk" $! σ with "Hlat Hrest")
      as "(%Hpc & %Htext & %HP & %Hnvpc & %Hrelp & %HV & Hlat & Hcont)".
    iModIntro. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|].
    iDestruct "Hcont" as (t0 t1) "(%Hex0 & %Hex1 & Hcont)".
    iExists t0, t1. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iNext. iIntros (tick σ') "%Hpost %HQfr".
    destruct HQfr as [HQ HQeff].
    assert (Hlog : wm_log σ' =
              (wm_log σ ++ [wwrite_msg (Some (fin_to_nat cpu_id))
                              WCrel hf 4 lock_zero])%list)
      by exact (wQ_eff_store_rel _ akf pf nf akw hf lock_zero σ σ'
                  Hlatw Hrelp HQeff).
    (* the continuation FIRST: it returns the state remainder, and the log
       authority inside it is what the mint rides *)
    iMod ("Hcont" $! tick σ' with "[%]") as "[Hrest Hk2]"; [exact Hpost|].
    iDestruct "Hrest" as "(%Hb' & %Hw' & Hr & Hd & Hlogauth & Hws)".
    iEval (rewrite Hlog) in "Hlogauth".
    iDestruct (pub_floor_mint (wm_log σ)
                 (wwrite_msg (Some (fin_to_nat cpu_id)) WCrel hf 4 lock_zero)
                 cpu_id eq_refl eq_refl with "Hlogauth") as "[Hlogauth #Hpf]".
    (* THE PARK on the migration invariant, in one line and with no byte
       named: the floor the release just minted covers everything the context
       wrote through this hart, so the invariant re-forms in its parked form *)
    assert (Hlen : (length (wm_log σ ++
              [wwrite_msg (Some (fin_to_nat cpu_id)) WCrel hf 4 lock_zero])
              <= S (length (wm_log σ)))%nat) by (rewrite length_app /=; lia).
    iDestruct (ctx_migr_park ξ cpu_id _ _ Hlen with "Hlogauth Hpf Hmg")
      as "[Hlogauth Hall]".
    iSpecialize ("Hk2" with "Hall").
    (* the release itself, and the φ payment — [wwp_release_store]'s verbatim *)
    iMod (wrelease_core γ hf (wbaton V) cpu_id (Some (fin_to_nat cpu_id)) σ σ'
            HQ Hrelp Hbnd with "Hlat Hbody Htok []") as "[Hlat Hbody]".
    { by iApply (wbaton_intro V (wm_ws σ) HV). }
    iAssert (⌜nv_hart (wm_log σ') cpu_id (wm_ws σ')⌝)%I as %Hnv'.
    { iDestruct "Hbody" as (st' t' v'') "[Hw' Hlk']".
      iDestruct (nv_ok_wlat4L cpu_id _ _ hf t' v''
                   with "Hlat Hw'") as %Hnvhf.
      iPureIntro.
      apply (nv_hart_of_wQ_eff_ok cpu_id σ σ'
               [WEread akf pf nf; WEwrite akw hf 4 lock_zero] HQeff Hnvσ).
      intros a Ha. destruct (Hfoot a Ha) as [(j & Hj & ->)|(j & Hj & ->)].
      - rewrite Hlog. intros n. apply nv_byte_app_own; [by apply Hnvpc|].
        intros m Hm. apply elem_of_list_singleton in Hm as ->. reflexivity.
      - by apply Hnvhf. }
    iMod ("Hclose" with "[Hbody]") as "_"; [by iNext|].
    iModIntro. iFrame "Hk2".
    iApply (wmstate_interp_split σ'). iFrame "Hlat".
    iApply (wmstate_rest_of_nonv σ' with "[%]"); [exact Hnv'|].
    rewrite /wmstate_rest_nonv. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|]. iFrame "Hr Hd Hws".
    iEval (rewrite -Hlog) in "Hlogauth". iExact "Hlogauth".
  Qed.

  (** ... AND THE RESUME NEEDS NO NEW RULE AT ALL — the spin-acquire is
      [WeakAcquire.wwp_acquire_loop_cert] at [R := wbaton V], instantiated and
      nothing else.  The whole protocol's work is at the park; the resume is
      an ordinary lock acquire whose payload happens to be a view receipt. *)
  Corollary wwp_yield_resume (γ : gname) (hf : Arch.pa) (V : view)
      (pc : SailStdpp.Values.mword 64)
      (akf : akinfo) (pf : Arch.pa) (nf : N) (aka akw : akinfo) (K : iProp Σ) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    acc_wf hf 4 →
    ak_coh aka = false →
    ak_sync aka = true →
    ak_latest akw = true →
    (∀ a : Z, weff_touches (WEread akf pf nf) a →
       ∃ j : nat, (j < 4)%nat ∧ a = acc_addr pc j) →
    inv wlockN (wlock_inv γ hf (wbaton V)) -∗
    □ (K -∗ ▷ (K -∗ WWP Loop) -∗
         wacq_cb γ hf (wbaton V) pc
           (wP_eff (Some (fin_to_nat cpu_id))
              [WEread akf pf nf; WEread aka hf 4; WEwrite akw hf 4 lock_one])) -∗
    K -∗ WWP Loop.
  Proof.
    exact (wwp_acquire_loop_cert γ hf (wbaton V) pc akf pf nf aka akw K).
  Qed.

End wp_yield.

(* ====================================================================== *)
(** ** 6. WHAT A PORTED PROOF TAKES FROM THIS FILE

    1. A thread that is about to park FREEZES its facts at its own index
       ([vwp_hold_freeze]) and frames [monPred_at P V] around the call.  There
       is nothing to prove: the freeze is definitional and the frozen fact is
       objective.

    2. [yield]'s specification carries the scheduler's resources — the lock
       body, the holder token, and the context's migration invariant — and
       returns them, with the invariant in its parked form.  It carries NO
       publication token and no memory fact of any kind.  At the port the
       index half of the baton becomes [WeakCtx.ctx_view_lb ξ V], which is
       what crosses [WpNext.wp_next].

    3. On the far side, EVERY framed fact — clean or dirty — is thawed by
       [vwp_hold_intro] and the index fact, and then used through the
       ordinary rules.  There is no upgrade step, at the first touch or ever;
       [WeakGhost.wown_ctx_retarget] does the work inside the store leaf, and
       the load leaf does not need it at all.  Pay φ with
       [WeakVProp.nv_ok_of_wpt_own], which is the same lemma an unmigrated
       thread uses.

    4. The mint site is the handoff release store, and it needs exactly what
       [WkOwnPingPong]'s release needed: [ak_latest akw = false] plus the
       [w_relp] fact the preceding [fence rw,w] delivers, fed to
       [wQ_eff_store_rel].  No new certificate. *)

Print Assumptions wyf_touch.
Print Assumptions wyf_store_and_use.
Print Assumptions wyf_park_frames.
Print Assumptions wyf_resume_and_use.
Print Assumptions wyf_phi_migrated.
Print Assumptions wwp_yield_park.
