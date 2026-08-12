(** * WkYieldFrame.v — THE FRAMING PATTERN: ownership across a [yield]
      (φ-upgrade §1.5, Stage 1.5)

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
    protocol's hart-indexed [WDirty] is a problem.  It is not: publication at
    the migration handoff plus a LAZY UPGRADE at first use on the new CPU is
    exactly context indexing, with no [wcds] redesign.

    ==================== THE PROGRAM ====================

      thread T, running on hart A                  ... resumed on hart B
      -------------------------------------------  --------------------------
        sb  1, 0(x)      # x := 1   (D-A)
                         # z ↦w{q} vz in hand, CLEAN and untouched
        call yield  --------------------------->
           fence rw,w    # arms w_relp                1: amoswap.w.aq a5,a4,0(hf)
           sw  zero,0(hf) # handoff release ========>     bnez a5,1b
                                                       ret
        <--------------------------------------------------
        lb  a5, 0(x)     # reads 1   <- the LAZY UPGRADE
        sb  2, 0(x)      # x := 2    (D-B: re-dirtied under the NEW author)
        lb  a5, 0(z)     # reads vz  <- the framed clean fact

    ==================== WHAT MAKES IT WORK ====================

    (1) THE FRAME IS LITERAL.  A thread's facts are held at ITS OWN INDEX; at
        the park they are FROZEN there ([WeakVProp.vwp_hold_freeze] — free,
        definitional), and [monPred_at P V] is an objective [iProp] that the
        yield lemmas simply do not mention.  §4's [wyf_park_frames] is
        [wyield_park_core] with the two facts threaded verbatim: its proof is
        the core plus [iFrame], which IS the claim.

    (2) WHAT COMES BACK IS TWO THINGS AND NO MORE.  From the park:
        [pub_covers_view A V] — "hart A has published everything the parked
        index [V] can see".  From the resume: [V ⊑ ws_view (wm_ws σ')] — the
        new hart's index dominates the parked one.  Neither mentions [x] or
        [z].  The second is delivered by the handoff flag's lock payload,
        which is a BARE VIEW RECEIPT ([wbaton] = [⊒V]) and carries no memory
        facts whatsoever.

        AT THE PORT the raw [⊒V] becomes [WeakCtx.ctx_view_lb ξ V] (that is
        what crosses [WpNext.wp_next]); the example uses the lowered form only
        because its thread is not a registered [WeakCtx] context.  The two
        halves stay independent and both stay necessary — the view half is
        about what the context OBSERVED (it frames the CLEAN facts and says
        nothing about publication, which is deliberately not a view
        component), the publication half about what the world may READ of the
        old hart's writes (the lazy-upgrade evidence AND the φ payment).

    (3) THE CLEAN FACT FRAMES FOR FREE, the DIRTY one is LAZILY UPGRADED.
        [z ↦w{q} vz] at [V] is re-established at [B] by [vwp_hold_intro] and
        the view fact alone.  [x ↦wo 1] at [V] cannot be: its state element
        says [WDirty A], and B is not A.  [WeakVProp.wpt_own_upgrade] retargets
        it to [WClean] out of the token — and the timestamp side condition one
        would expect is ABSENT, because the framed [↦wo]'s own receipt
        [⊒(view_byte x t)] read at the frozen index IS [t ≤ flr V x], and the
        token covers [V].  That is why the token is stated over a VIEW and not
        over a position.

    (4) φ COSTS NOTHING NEW.  A foreign-dirty but PUBLISHED byte carries no
        [no_violation] obligation at all ([WeakGhost.nv_free_published]: the
        predicate only ever constrains UNPUBLISHED owned stores).  So the
        migrated thread pays for [x] out of the same token it upgrades with,
        BEFORE the ghost step — [WeakVProp.nv_free_of_own_upgrade] — which is
        what lets a leaf state its obligation where it holds its resources.

    ==================== WHAT IS NEW HERE VS. THE PING-PONG ====================

    Machinery: [WeakGhost.pub_floor] (the token) + [wlat_flip_pub] (the
    floor-based D→C flip, which needs no premise about the log's top) and
    [WeakVProp.pub_covers_view] + [wpt_own_upgrade] (the acceptance arm) +
    [wpt_load_rule_own] (the ping-pong's recorded gap (1), a hart reading its
    OWN dirty byte — the foreign-published arm generalises it).  Everything
    else below is composition. *)
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
(** ** 2. [yield_park] — the A-side: fence, handoff release, mint the token

    THE SPEC SHAPE IS THE DELIVERABLE.  Read the statement: its precondition
    is the machine's own state pieces plus the SCHEDULER's resources (the
    handoff flag's lock body and the holder token) and nothing else; its
    postcondition adds exactly ONE thing beyond what it consumed —
    [pub_covers_view i V].  There is no [↦w] and no [↦wo] anywhere in it.

    The [fence rw,w] is the caller's previous instruction and appears here as
    what it produces: the appended message is [WCrel] on the nose ([Hlog]),
    which the WP-altitude rule of §5 reads off the certificate's own trace
    with [WkOwnPingPong.wQ_eff_store_rel].  That single class fact is what
    makes the handoff store BORN-PUBLISHED, and hence what mints the token —
    no ghost operation on any of the thread's bytes is performed, or could
    be: the yield does not know which bytes they are. *)

  Lemma wyield_park_core (γ : gname) (hf : Arch.pa) (V : view) (i : CPU)
      (σ σ' : wmstate) :
    wQ_store (Some (fin_to_nat i)) hf lock_zero σ σ' →
    wm_log σ' =
      (wm_log σ ++ [wwrite_msg (Some (fin_to_nat i)) WCrel hf 4 lock_zero])%list →
    ws_bounded (wm_ws σ) (length (wm_log σ)) →
    (* the parking hart has observed [V] — a fact about its INDEX, not about
       any byte it owns *)
    V ⊑ ws_view (wm_ws σ) →
    wlog_auth (wm_log σ) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ hf (wbaton V) -∗
    locked γ i ==∗
    wlog_auth (wm_log σ') ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    wlock_inv γ hf (wbaton V) ∗ pub_covers_view i V.
  Proof.
    intros (Himg & _ & Hle & Hflr) Hlog Hbnd HV.
    iIntros "Hlog Hi Hinv Htok".
    iDestruct "Hinv" as (st t w) "(Hw & Ha & _)".
    iDestruct (locked_state with "Ha Htok") as %->.
    (* the flag word's bundle moves to the fresh top and stays CLEAN — a
       [WCrel] message is not an owned store *)
    iMod (wlat4_store_gen (Some (fin_to_nat i)) WCrel σ σ' hf t w lock_zero
            ltac:(discriminate) Himg Hlog with "Hi Hw") as "[Hi Hw]".
    (* THE MINT.  The step's own message is this hart's, release-class, and at
       the log's fresh top — so it covers every earlier position at once, and
       hence the whole parked index. *)
    iMod (wlog_update (wm_log σ)
            [wwrite_msg (Some (fin_to_nat i)) WCrel hf 4 lock_zero]
            with "Hlog") as "Hlog".
    iDestruct (pub_floor_mint (wm_log σ)
                 (wwrite_msg (Some (fin_to_nat i)) WCrel hf 4 lock_zero) i
                 eq_refl eq_refl with "Hlog") as "[Hlog #Hpf]".
    (* the baton: the parking hart's own index, frozen at the store's
       timestamp — pure view arithmetic, [ws_bounded] and nothing else *)
    iAssert (monPred_at (wbaton V) (view_scl (S (length (wm_log σ)))))%I as "HR".
    { iApply (wwp_release_deposit (wbaton V) σ Hbnd).
      by iApply (wbaton_intro V (wm_ws σ) HV). }
    iMod (lock_clrcpu γ (Some (i, true)) i with "Ha Htok") as "(_ & Ha & Hpre)".
    iMod (lock_give γ (Some (i, false)) i with "Ha Hpre") as "(_ & Ha & Hfrag)".
    iModIntro. rewrite -Hlog. iFrame "Hlog Hi".
    iSplitL "Hw Ha Hfrag HR".
    { iExists None, (S (length (wm_log σ))), lock_zero.
      iFrame "Hw Ha". iLeft. iSplitR; [done|]. iSplitR; [done|].
      iFrame "Hfrag HR". }
    iApply (pub_covers_view_intro i V (S (length (wm_log σ)))).
    - etrans; [exact HV|]. by apply ws_view_store_dom.
    - iExact "Hpf".
  Qed.

(* ====================================================================== *)
(** ** 3. [yield_resume] — the B-side: acquire the flag, install the index

    The other half, and it needs NO new machinery: [WeakLock.wacquire_core]
    at the baton payload, with the payload's decode ([wbaton_at]) applied on
    the far side.  Its postcondition is one pure inequality about the
    RESUMING hart's index; again, no [↦w] and no [↦wo].

    Two lemmas rather than one because there are two harts: [wlat_interp] is
    the authority over the latest-write map, so no proposition can hold it at
    the parking hart's state and at the resuming hart's later state at once
    ([WkStartedMp] §2's reason, verbatim).  The composed call shape is

      [wyield_park_core] … ==∗ … ∗ pub_covers_view A V
      ‹the machine runs; other harts run; the thread is not scheduled›
      [wyield_resume_core] … ==∗ … ∗ locked γ B ∗ ⌜V ⊑ ws_view (wm_ws σ')⌝

    and §4's [wyf_park_frames] / §4's [wyf_resume_and_use] are exactly those
    two with the thread's own facts threaded through the FRAME. *)

  Lemma wyield_resume_core (γ : gname) (hf : Arch.pa) (V : view) (i : CPU)
      (tid : option nat) (σ σ' : wmstate) :
    wlog_wf (wm_log σ) → acc_wf hf 4 →
    wQ_amo_aq tid hf lock_one σ σ' →
    (* the spin loop's successful attempt: the flag word read 0 *)
    (∀ j : nat, (j < 4)%nat →
       wflat (wm_img σ) (wm_log σ) !! pa_add hf j = Some (nth_byte lock_zero j)) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ hf (wbaton V) ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wlock_inv γ hf (wbaton V) ∗
    locked γ i ∗ ⌜V ⊑ ws_view (wm_ws σ')⌝.
  Proof.
    intros Hwf Hacc HQ Hzero. iIntros "Hi Hinv".
    iDestruct (wacquire_core γ hf (wbaton V) i tid σ σ' Hwf Hacc HQ
                 with "Hi Hinv") as (v0) "[%Hflat Hupd]".
    assert (Hv : lock_zero = v0)
      by exact (wflat_word_agree σ hf lock_zero v0 Hzero Hflat).
    iMod "Hupd" as "(Hi & Hbody & Harm)".
    iDestruct "Harm" as "[(_ & HR & Htok)|%Hne]"; [|by rewrite -Hv in Hne].
    rewrite wbaton_at. iDestruct "HR" as %HV.
    iModIntro. by iFrame "Hi Hbody Htok".
  Qed.

End yield.

(* ====================================================================== *)
(** ** 4. THE EXAMPLE — thread T's own facts, framed around the yield

    Everything below is at the σ altitude, with T's facts appearing ONLY in
    T's own pre/post.  Compare the statements: §2's and §3's mention neither
    [x] nor [z]; §4's carry them, and their proofs are §2/§3 plus framing. *)

Section example.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.

(* ---------------------------------------------------------------------- *)
(** *** 4a. ON HART A: [x := 1], and the freeze

    The store is [WeakVProp.wpt_store_post_own] (unchanged, absorbing form) —
    or, for the exhibit, [WkOwnPingPong.wpt_store_post_dirty], which says
    "[WDirty A]" in its conclusion so that the framed fact visibly IS a dirty
    one.  Then [vwp_hold_freeze] turns "T holds it at A" into "T holds it at
    the objective index [V]", which is the form that frames. *)

  Lemma wyf_store_and_freeze (A : CPU) (σ : wmstate) (m : wmsg)
      (x z : Z) (v0 : bv 8) (vz : bv 8) (q : dfrac) (rl : bool) :
    msg_byte m x = Some byte1 →
    (∀ a', a' ≠ x → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat A) →
    wm_ak m = WCplain →
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt_own A x v0) (wm_ws σ) -∗
    vwp_hold (z ↦w{q} vz) (wm_ws σ) ==∗
    wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list) ∗
    (* the two facts T carries into the yield, at its own index — and, since
       [vwp_hold P ws] IS [monPred_at P (ws_view ws)], already FROZEN there:
       objective from here on, so the yield lemmas cannot see them *)
    monPred_at (wpt_dirty A x byte1)
      (ws_view (store_post (wm_ws σ) rl x (S (length (wm_log σ))))) ∗
    monPred_at (z ↦w{q} vz)
      (ws_view (store_post (wm_ws σ) rl x (S (length (wm_log σ))))).
  Proof.
    intros Hma Hother Htid Hk. iIntros "Hi Hx Hz".
    iMod (wpt_store_post_dirty A σ m x v0 byte1 rl
            Hma Hother Htid Hk with "Hi Hx") as "[Hi Hx]".
    iModIntro. iFrame "Hi Hx".
    (* the clean fact rides the same step's view growth, and nothing else *)
    iApply (vwp_hold_mono (z ↦w{q} vz)%I (wm_ws σ)); [|iExact "Hz"].
    apply store_post_le.
  Qed.

(* ---------------------------------------------------------------------- *)
(** *** 4b. THE PARK, WITH T'S FACTS IN THE FRAME

    THE STATEMENT IS THE POINT.  This is [wyield_park_core] verbatim with two
    conjuncts threaded from premise to conclusion, untouched; the proof is the
    core plus [iFrame].  Nothing about [x] or [z] is used, and nothing about
    them could be used — the yield does not know they exist. *)

  Corollary wyf_park_frames (γ : gname) (hf : Arch.pa) (A : CPU)
      (σ σ' : wmstate) (x z : Z) (vx vz : bv 8) (q : dfrac) :
    wQ_store (Some (fin_to_nat A)) hf lock_zero σ σ' →
    wm_log σ' =
      (wm_log σ ++ [wwrite_msg (Some (fin_to_nat A)) WCrel hf 4 lock_zero])%list →
    ws_bounded (wm_ws σ) (length (wm_log σ)) →
    wlog_auth (wm_log σ) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ hf (wbaton (ws_view (wm_ws σ))) -∗
    locked γ A -∗
    (* ------------------------ THE FRAME ------------------------ *)
    monPred_at (wpt_dirty A x vx) (ws_view (wm_ws σ)) -∗
    monPred_at (z ↦w{q} vz) (ws_view (wm_ws σ)) ==∗
    (* ----------------------------------------------------------- *)
    wlog_auth (wm_log σ') ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    wlock_inv γ hf (wbaton (ws_view (wm_ws σ))) ∗
    pub_covers_view A (ws_view (wm_ws σ)) ∗
    monPred_at (wpt_dirty A x vx) (ws_view (wm_ws σ)) ∗
    monPred_at (z ↦w{q} vz) (ws_view (wm_ws σ)).
  Proof.
    intros HQ Hlog Hbnd. iIntros "Hlog Hi Hinv Htok Hx Hz".
    iMod (wyield_park_core γ hf (ws_view (wm_ws σ)) A σ σ' HQ Hlog Hbnd
            ltac:(reflexivity) with "Hlog Hi Hinv Htok") as "($ & $ & $ & $)".
    by iFrame "Hx Hz".
  Qed.

(* ---------------------------------------------------------------------- *)
(** *** 4c. ON HART B: resume, then USE the framed facts

    The resume installs the index; then, in order:
      - [x]: the LAZY UPGRADE ([WeakVProp.wpt_load_rule_pub] = upgrade +
        the ordinary load + re-own at B).  The load returns 1.
      - [x := 2]: an ORDINARY owned store at the new author, whose
        postcondition is [WDirty B] on the nose.
      - [z]: the framed clean fact, thawed by the view alone and collapsed by
        the ordinary [WeakVProp.wpt_load_rule].  It returns [vz]. *)

  Lemma wyf_resume_and_use (γ : gname) (hf : Arch.pa) (V : view)
      (A B : CPU) (tid : option nat) (σ σ' σn : wmstate) (mB : wmsg)
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
    wlog_auth (wm_log σn) -∗
    (* the ONLY things the yield handed back *)
    pub_covers_view A V -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ hf (wbaton V) -∗
    (* the FRAMED facts, still frozen at the parking index *)
    monPred_at (wpt_dirty A x byte1) V -∗
    monPred_at (z ↦w{q} vz) V ==∗
    wlog_auth (wm_log σn) ∗
    wlat_interp (wm_img σn) ((wm_log σn ++ [mB])%list) ∗
    wlock_inv γ hf (wbaton V) ∗ locked γ B ∗
    (* the load of [x] returned what A wrote; [z] returned what T framed *)
    ⌜bx = byte1⌝ ∗ ⌜bz = vz⌝ ∗
    (* [x] is now DIRTY AT B — the author alternated across a migration with
       no transfer and no payload *)
    vwp_hold (wpt_dirty B x byte2)
      (store_post (wm_ws σn) rl x (S (length (wm_log σn)))) ∗
    (* ... and [z] is still T's, clean, at the new hart *)
    vwp_hold (z ↦w{q} vz)
      (store_post (wm_ws σn) rl x (S (length (wm_log σn)))).
  Proof.
    intros Hwf Hacc HQ Hzero Himg Hlg Hle Hcohx Hokx Hcohz Hokz
           Hmb Hother Htid Hk.
    iIntros "Hlog #Hpf Hi Hinv Hx Hz".
    (* --- the resume: the index arrives, and nothing else --- *)
    iMod (wyield_resume_core γ hf V B tid σ σ' Hwf Hacc HQ Hzero with "Hi Hinv")
      as "(Hi & Hbody & Htok & %HV)".
    (* carry everything to the state T's own accesses run at *)
    assert (HVn : V ⊑ ws_view (wm_ws σn))
      by (etrans; [exact HV|by apply ws_view_mono]).
    rewrite -Himg -Hlg.
    (* --- [x]: THE LAZY UPGRADE, and the load --- *)
    iDestruct (monPred_at_ent _ _ V (wpt_dirty_own A x byte1) with "Hx") as "Hx".
    iMod (wpt_load_rule_pub A B V σn σn akx x byte1 tx bx
            Hcohx Hokx eq_refl eq_refl HVn ltac:(lia)
            with "Hlog Hpf Hi Hx") as "(%Hbx & Hlog & Hi & Hx)".
    (* --- [z]: the framed CLEAN fact, thawed by the view alone --- *)
    iDestruct (vwp_hold_intro V (z ↦w{q} vz)%I (wm_ws σn) HVn with "Hz") as "Hz".
    iDestruct (wpt_load_rule σn σn akz z q vz tz bz
                 Hcohz Hokz eq_refl eq_refl ltac:(lia) with "Hi Hz")
      as "(%Hbz & Hi & Hz)".
    (* --- [x := 2] at the NEW author --- *)
    iMod (wpt_store_post_dirty B σn mB x byte1 byte2 rl
            Hmb Hother Htid Hk with "Hi Hx") as "[Hi Hx]".
    iModIntro. iFrame "Hlog Hi Hbody Htok Hx".
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iApply (vwp_hold_mono (z ↦w{q} vz)%I (wm_ws σn)); [|iExact "Hz"].
    apply store_post_le.
  Qed.

(* ---------------------------------------------------------------------- *)
(** *** 4d. THE φ PAYMENT OF THE MIGRATED THREAD'S FIRST TOUCH

    Every instruction fetches, so every leaf owes [nv_hart] at its post-log,
    one [WeakGhost.nv_byte] per byte its trace touches ([WeakCert]'s
    reduction).  The migrated thread's load of [x] touches a byte that is
    still [WDirty A] at that moment and the reading hart is [B ≠ A] — the one
    configuration neither [nv_ok_of_own_st] (wrong hart) nor
    [nv_ok_of_pointsto] (not clean) can pay.

    The token pays it, and pays it BEFORE the ghost step: a published owned
    store is not a violation, whoever reads it. *)

  Lemma wyf_phi_migrated (A B : CPU) (V : view) (img : _) (log : list wmsg)
      (pcb x : Z) (vx : bv 8) :
    latest_ts log pcb = 0%nat →
    wlog_auth log -∗ pub_covers_view A V -∗ wlat_interp img log -∗
    monPred_at (wpt_dirty A x vx) V -∗
    ⌜nv_ok log B pcb ∧ nv_ok log B x⌝.
  Proof.
    intros Htext. iIntros "Hlog #Hpf Hi Hx".
    iDestruct (monPred_at_ent _ _ V (wpt_dirty_own A x vx) with "Hx") as "Hx".
    iDestruct (nv_free_of_own_upgrade A x vx V img log
                 with "Hlog Hpf Hi Hx") as %Hnx.
    iPureIntro. split; [by apply nv_ok_unwritten|by apply nv_ok_of_free].
  Qed.

End example.

(* ====================================================================== *)
(** ** 5. THE PARK AT THE WP ALTITUDE — one [sw] through the handoff flag

    [WeakAcquire.wwp_release_store] with two changes and no more:

      - the callback hands over NO payload at all (contrast [wrel_cb], which
        hands over [vwp_hold R (wm_ws σ)]); what it hands over is the pure
        fact that the parking hart has observed [V], which is not a resource;
      - the post-step continuation is handed the token.  It is delivered
        AFTER the continuation has returned the state remainder, because the
        log authority the mint rides lives in that remainder — which is why
        the continuation's type ends in [pub_covers_view … -∗ WWP Loop]
        rather than taking the token as an argument up front.

    The class fact the mint needs is read off the certificate's own trace by
    [WkOwnPingPong.wQ_eff_store_rel], exactly as the ping-pong's release does;
    the φ payment is [wwp_release_store]'s verbatim. *)

Section wp_yield.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition wyield_park_cb (V : view) (pc : SailStdpp.Values.mword 64)
      (P : wmstate → Prop) : iProp Σ :=
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
                  (* THE WHOLE MEMORY-VISIBLE POSTCONDITION OF THE PARK *)
                  (pub_covers_view cpu_id V -∗ WWP Loop)))%I.

  Lemma wwp_yield_park (γ : gname) (hf : Arch.pa) (V : view)
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
    wyield_park_cb V pc
      (wP_eff (Some (fin_to_nat cpu_id))
         [WEread akf pf nf; WEwrite akw hf 4 lock_zero]) -∗
    WWP Loop.
  Proof.
    intros Hgid Haccpc Hacchf Hlatw Hfetch. iIntros "#Hinv Htok Hk".
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
    assert (HVs : V ⊑ view_scl (S (length (wm_log σ))))
      by (etrans; [exact HV|by apply ws_view_store_dom]).
    iAssert (pub_covers_view cpu_id V) as "#Hpcv".
    { iApply (pub_covers_view_intro cpu_id V (S (length (wm_log σ))) HVs).
      iExact "Hpf". }
    iSpecialize ("Hk2" with "Hpcv").
    (* the release itself, and the φ payment — [wwp_release_store]'s verbatim *)
    iMod (wrelease_core γ hf (wbaton V) cpu_id (Some (fin_to_nat cpu_id)) σ σ'
            HQ Hrelp Hbnd with "Hlat Hbody Htok []") as "[Hlat Hbody]".
    { by iApply (wbaton_intro V (wm_ws σ) HV). }
    iAssert (⌜nv_hart (wm_log σ') cpu_id (wm_ws σ')⌝)%I as %Hnv'.
    { iDestruct "Hbody" as (st' t' v'') "[Hw' Hlk']".
      iDestruct (nv_ok_wlat4 cpu_id _ _ hf (DfracOwn 1) t' v''
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

    2. [yield]'s specification carries the scheduler's resources and returns
       [pub_covers_view c_old V] plus the resuming index.  At the port the
       index half becomes [WeakCtx.ctx_view_lb ξ V], which is what crosses
       [WpNext.wp_next]; the publication half is unchanged, because it is
       about the LOG and not about any hart's view.

    3. On the far side, a CLEAN framed fact is thawed by [vwp_hold_intro] and
       the index fact.  A DIRTY one goes through [WeakVProp.wpt_own_upgrade]
       once, at first use, and is an ordinary clean full-fraction byte
       afterwards — so every subsequent load/store site is untouched.  Pay φ
       for it with [WeakVProp.nv_free_of_own_upgrade].

    4. The mint site is the handoff release store, and it needs exactly what
       [WkOwnPingPong]'s release needed: [ak_latest akw = false] plus the
       [w_relp] fact the preceding [fence rw,w] delivers, fed to
       [wQ_eff_store_rel].  No new certificate. *)

Print Assumptions wyf_park_frames.
Print Assumptions wyf_resume_and_use.
Print Assumptions wyf_phi_migrated.
Print Assumptions wwp_yield_park.
