(** * WeakInstr.v — the weak instruction-leaf layer (M3a)

    Everything between [WeakExec.wp_wexec_step] (the raw lifting rule, stated
    over the ORACLE and [wexec]) and a whole-instruction leaf rule stated over
    the memory resources of [WeakVProp]/[WeakFence].

    ======================= THE THREE THINGS IN HERE =======================

    (1) THE FLAT BRIDGE FOR RESOURCES (§1–§2).  [WeakBridge] transfers the
        exec-level library on the PINNED fragment, but it transfers a RUN; a
        leaf still has to say what the flat memory HOLDS at the bytes it owns.
        That is [wlat_flat_lookup]: an element of the latest-write map at byte
        [a] IS what [WeakLang.wflat] holds there — for ANY timestamp, hence for
        an owned [↦w] and, as the special case that matters, for an era-image
        byte ([wpt_img], timestamp 0: all kernel text).  With it, the whole
        fetch/decode side of an instruction transfers as a statement about the
        flat projection, and [wkernel_text] (§2) is the objective, freely
        shareable resource that carries it.

    (2) THE PIN CERTIFICATE (§3).  [WeakBridge.wstep_ok] is a structural peel
        of the WHOLE step ([riscv_step tick]), i.e. of [try_step] /
        [run_hart_active] / [fetch] / [decode] / [execute].  Its per-access
        content is tiny (the text is unwritten, the data footprint is pinned or
        the access kind forces the latest read) but obtaining it requires
        walking the model exactly as [RiscvFetchExec]'s [exec_hart_active_*]
        chain does — a per-instruction obligation of the same nature as a
        decode fact.  It is therefore packaged AS one: [wpin_step cid pc P] is
        the pure, per-(pc, instruction) statement "given the text at [pc] is
        unwritten and [P] holds of the hart's weak state, the step's peel goes
        through", and a leaf takes it as a premise exactly the way the SC
        leaves take [pmp_allows_all] and an [instr] fact.  §3 supplies the
        connectors that discharge its hypotheses from resources.

    (3) THE RULE (§4).  [wp_wstep_flat] is the weak analogue of
        [InstrBytes.wp_exec_step_decode_execute_inv]'s altitude: the caller
        supplies the SAME [exec] facts it supplies today — but over
        [WeakBridge.wflat_st σ], the flat projection — plus ONE peel
        ([wstep_ok]), and receives back a successor [σ'] described by
        [wstep_post]: registers/devices/flat-memory are the SC ones, the image
        is unchanged, the log only grew, and the hart's views only grew.  That
        last conjunct is what [WeakVProp.vwp_hold_mono] consumes, so every
        resource a leaf did not touch crosses the step for free.

    ======================= WHAT DID *NOT* HAVE TO MOVE =======================

    THE CONFIG TOWER TRANSFERS AS-IS.  [RiscvFetchExec.hw_config],
    [InstrBytes.mmode_config], the sconf bundles, [KMap.kmap_static_claims] —
    every one of them is a conjunction of REGISTER points-to, pure facts and
    ghost state, i.e. an [iProp] over [riscvGS], which the weak side carries
    unchanged; and [WeakGhost.wmstate_interp] contains
    [reg_interp σ.(wm_regs)] with [wm_regs σ = sregs (wflat_st σ)], so
    [RiscvPtsto.reg_valid]/[reg_valid_dq]/[reg_update] apply verbatim and the
    exec-facts they feed are facts about a state whose registers ARE the weak
    hart's.  Embedded into [vProp] they are objective by [embed_objective], so
    no view plumbing appears anywhere.  The ONLY things that do not carry over
    are the lemmas that consume [RiscvPtsto.mstate_interp] AS A BUNDLE
    ([InstrBytes.fetch_from_instr_bytes], [instr_lift],
    [dispatchInterrupt_none_from_regs], [state_interp_reg_dq], [wp_instr]) —
    because that bundle contains [gen_heap_interp], which the weak state
    interpretation replaces.  Each of those is a mechanical restatement with
    the memory hypothesis taken as the pure fact §1 produces. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop ghost_map ghost_var.
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
Require Import RiscvLang RiscvPtsto RiscvExec.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. What the flat projection HOLDS at an owned byte

    The one-line answer, and the reason the fetch/decode side needs no view
    reasoning at all: the [γlat] element for a byte says its LATEST write is
    [(t, v)], and [WeakLang.wflat_latest] says the flat projection holds
    exactly the latest write's value.  So an element — at ANY timestamp —
    determines the flat byte.  No hypothesis about the reader's views. *)

Section flat_bridge.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma wlat_flat_lookup (σ : wmstate) (a : Arch.pa) (dq : dfrac) (t : nat)
      (v : bv 8) :
    wlog_wf (wm_log σ) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat_pointsto (pa_z a) dq t v -∗
    ⌜wflat (wm_img σ) (wm_log σ) !! a = Some v⌝.
  Proof.
    intros Hwf. iIntros "Hi He".
    iDestruct (wlat_lookup with "Hi He") as %Hlat.
    iPureIntro.
    rewrite (wflat_latest (wm_img σ) (wm_log σ) a t Hwf
               (latest_val_latest _ _ _ _ _ Hlat)).
    exact (proj1 Hlat).
  Qed.

  (** The same over the BARE value element — the form the C/D/S owned
      points-to decodes to, and the one both surface forms go through. *)
  Lemma wlat_flat_lookup_e (σ : wmstate) (a : Arch.pa) (dq : dfrac) (t : nat)
      (v : bv 8) :
    wlog_wf (wm_log σ) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat_elem (pa_z a) dq t v -∗
    ⌜wflat (wm_img σ) (wm_log σ) !! a = Some v⌝.
  Proof.
    intros Hwf. iIntros "Hi He".
    iDestruct (wlat_lookup_elem with "Hi He") as %Hlat.
    iPureIntro.
    rewrite (wflat_latest (wm_img σ) (wm_log σ) a t Hwf
               (latest_val_latest _ _ _ _ _ Hlat)).
    exact (proj1 Hlat).
  Qed.

  Lemma wpt_own_h_flat_lookup (c : CPU) (σ : wmstate) (a : Arch.pa) (v : bv 8) :
    wlog_wf (wm_log σ) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt_own_h c (pa_z a) v) (wm_ws σ) -∗
    ⌜wflat (wm_img σ) (wm_log σ) !! a = Some v⌝.
  Proof.
    intros Hwf. iIntros "Hi Hpt". rewrite wpt_own_h_at.
    iDestruct "Hpt" as (t) "(He & _ & _)".
    by iApply (wlat_flat_lookup_e σ a (DfracOwn 1) t v Hwf with "Hi He").
  Qed.

  (** The owned form.  ([wpt_at] hands out the element; the receipt is not
      needed — which is the whole point.) *)
  Lemma wpt_flat_lookup (σ : wmstate) (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    wlog_wf (wm_log σ) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (pa_z a ↦w{dq} v) (wm_ws σ) -∗
    ⌜wflat (wm_img σ) (wm_log σ) !! a = Some v⌝.
  Proof.
    intros Hwf. iIntros "Hi Hpt". rewrite wpt_at.
    iDestruct "Hpt" as (t) "[He _]".
    by iApply (wlat_flat_lookup σ a dq t v Hwf with "Hi He").
  Qed.

  (** The ERA-IMAGE form — objective, no receipt, no view.  This is the one
      the fetch path uses. *)
  Lemma wpt_img_flat_lookup_gen (σ : wmstate) (a : Arch.pa) (dq : dfrac)
      (t : nat) (v : bv 8) :
    wlog_wf (wm_log σ) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat_pointsto (pa_z a) dq t v -∗
    ⌜wflat (wm_img σ) (wm_log σ) !! a = Some v ∧
     latest_ts (wm_log σ) (pa_z a) = t⌝.
  Proof.
    intros Hwf. iIntros "Hi He".
    iDestruct (wlat_lookup with "Hi He") as %Hlat.
    iDestruct (wlat_flat_lookup σ a dq t v Hwf with "Hi He") as %Hfl.
    iPureIntro. split; [exact Hfl|].
    exact (latest_val_ts _ _ _ _ _ Hlat).
  Qed.

  Lemma wpt_img_flat_lookup (σ : wmstate) (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    wlog_wf (wm_log σ) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat_pointsto (pa_z a) dq 0%nat v -∗
    ⌜wflat (wm_img σ) (wm_log σ) !! a = Some v ∧
     latest_ts (wm_log σ) (pa_z a) = 0%nat⌝.
  Proof. apply wpt_img_flat_lookup_gen. Qed.

End flat_bridge.

(* ====================================================================== *)
(** ** 1a'. THE PER-BYTE BRIDGES, WIDTH-GENERIC

    The one-byte content of the whole flat/pinned side, stated once for an
    access of ANY width [n].  Every width-[k] bundle lemma below ([wpt4_flat],
    [wpt4_pinned], [WeakLock.wlat4_flat_gen], [wwp_amoswap_w_aq_inv]'s inner
    block, and the whole [WeakWord8] tower) is [k] applications of one of
    these and nothing else.

    Both are stated at the log's own key [WeakInterp.acc_addr a j] (which is
    what a bundle carries) and convert to the [Arch.pa]-keyed flat map through
    [WeakBridge.acc_wf_byte] — the conversion [acc_wf] exists to make
    available. *)

Section byte_bridges.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** An OWNED byte of an access window: what the flat projection holds
      there, and that it is pinned for this hart. *)
  Lemma wpt_byte_flat_pin (σ : wmstate) (a : Arch.pa) (n : N) (dq : dfrac)
      (b : bv 8) (j : nat) :
    wlog_wf (wm_log σ) → acc_wf a n → (j < N.to_nat n)%nat →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (acc_addr a j ↦w{dq} b) (wm_ws σ) -∗
    ⌜wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some b ∧
     pinned_read σ (acc_addr a j)⌝.
  Proof.
    intros Hwf Hacc Hj. iIntros "Hi Hpt".
    iDestruct (wpt_pinned_read σ (acc_addr a j) dq b with "Hi Hpt") as %Hpin.
    iAssert (⌜wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some b⌝)%I as %Hfl.
    { iApply (wpt_flat_lookup σ (pa_add a j) dq b Hwf with "Hi [Hpt]").
      rewrite (acc_wf_byte a n j Hacc Hj). iExact "Hpt". }
    iPureIntro. by split.
  Qed.

  (** The OWNED (C-or-D) twin of [wpt_byte_flat_pin]. *)
  Lemma wpt_own_h_byte_flat_pin (c : CPU) (σ : wmstate) (a : Arch.pa) (n : N)
      (b : bv 8) (j : nat) :
    wlog_wf (wm_log σ) → acc_wf a n → (j < N.to_nat n)%nat →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt_own_h c (acc_addr a j) b) (wm_ws σ) -∗
    ⌜wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some b ∧
     pinned_read σ (acc_addr a j)⌝.
  Proof.
    intros Hwf Hacc Hj. iIntros "Hi Hpt".
    iDestruct (wpt_own_h_pinned_read c σ (acc_addr a j) b with "Hi Hpt")
      as %Hpin.
    iAssert (⌜wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some b⌝)%I as %Hfl.
    { iApply (wpt_own_h_flat_lookup c σ (pa_add a j) b Hwf with "Hi [Hpt]").
      rewrite (acc_wf_byte a n j Hacc Hj). iExact "Hpt". }
    iPureIntro. by split.
  Qed.

  (** A BARE ELEMENT of an access window (no receipt, no view): the same flat
      fact, plus the identification of the element's timestamp with the byte's
      [latest_ts] — which is what makes an [ak_latest] read return exactly this
      element's value. *)
  Lemma wlat_byte_flat_gen (σ : wmstate) (a : Arch.pa) (n : N) (dq : dfrac)
      (t : nat) (b : bv 8) (j : nat) :
    wlog_wf (wm_log σ) → acc_wf a n → (j < N.to_nat n)%nat →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat_pointsto (acc_addr a j) dq t b -∗
    ⌜wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some b ∧
     latest_ts (wm_log σ) (acc_addr a j) = t⌝.
  Proof.
    intros Hwf Hacc Hj. iIntros "Hi He".
    rewrite -(acc_wf_byte a n j Hacc Hj).
    iApply (wpt_img_flat_lookup_gen σ (pa_add a j) dq t b Hwf with "Hi [He]").
    rewrite (acc_wf_byte a n j Hacc Hj). iExact "He".
  Qed.

End byte_bridges.

(* ====================================================================== *)
(** ** 1b. [↦w₄] — the four-byte bundle

    M2b's cut item 3, in the minimal form M3a needs: four consecutive weak
    bytes plus the two pure facts every consumer wants — 4-alignment (the
    model's access check) and WRAP-FREEDOM of the four-byte range
    ([WeakBridge.acc_wf], what makes the [Z]-keyed log and the [Arch.pa]-keyed
    flat map agree on this window).  Both are free for a RAM address.

    The bytes are keyed at [WeakInterp.acc_addr] — the log's own [Z] key —
    rather than at [pa_z (pa_add a j)]; [acc_wf_byte] converts, and carrying
    [acc_wf] in the bundle is what makes that conversion available wherever
    the bundle is. *)

Section word4.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Definition wpt4 (a : Arch.pa) (dq : dfrac) (w : bv 32) : vProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗ ⌜acc_wf a 4⌝ ∗
     (acc_addr a 0) ↦w{dq} nth_byte w 0 ∗
     (acc_addr a 1) ↦w{dq} nth_byte w 1 ∗
     (acc_addr a 2) ↦w{dq} nth_byte w 2 ∗
     (acc_addr a 3) ↦w{dq} nth_byte w 3)%I.

  Global Instance wpt4_persistent a w : Persistent (wpt4 a DfracDiscarded w).
  Proof. rewrite /wpt4. apply _. Qed.
  Global Instance wpt4_timeless a q w : Timeless (wpt4 a (DfracOwn q) w).
  Proof. rewrite /wpt4. apply _. Qed.

  Lemma wpt4_facts a dq w :
    wpt4 a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 4 = true ∧ acc_wf a 4⌝.
  Proof. iIntros "(% & % & _)". by iPureIntro. Qed.

  (** FRACTION SPLIT / JOIN — inherited byte by byte from [wpt_split]. *)
  Lemma wpt4_split a q1 q2 w :
    wpt4 a (DfracOwn (q1 + q2)) w
    ⊣⊢ wpt4 a (DfracOwn q1) w ∗ wpt4 a (DfracOwn q2) w.
  Proof.
    rewrite /wpt4 !wpt_split. iSplit.
    - iIntros "(%Hal & %Hwf & [A0 B0] & [A1 B1] & [A2 B2] & [A3 B3])".
      iSplitL "A0 A1 A2 A3";
        (iSplitR; [by iPureIntro|]); (iSplitR; [by iPureIntro|]); iFrame.
    - iIntros "[(%Hal & %Hwf & A0 & A1 & A2 & A3) (_ & _ & B0 & B1 & B2 & B3)]".
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iFrame.
  Qed.

  Lemma wpt4_agree a dq1 w1 dq2 w2 :
    wpt4 a dq1 w1 ∗ wpt4 a dq2 w2 ⊢ ⌜w1 = w2⌝.
  Proof.
    rewrite /wpt4.
    iIntros "[(_ & _ & A0 & A1 & A2 & A3) (_ & _ & B0 & B1 & B2 & B3)]".
    iDestruct (wpt_agree with "[$A0 $B0]") as %E0.
    iDestruct (wpt_agree with "[$A1 $B1]") as %E1.
    iDestruct (wpt_agree with "[$A2 $B2]") as %E2.
    iDestruct (wpt_agree with "[$A3 $B3]") as %E3.
    iPureIntro. apply (bv_eq_of_bytes (n := 4%N)). intros j Hj.
    destruct j as [|[|[|[|j]]]]; [exact E0|exact E1|exact E2|exact E3|lia].
  Qed.

  (** THE FLAT + PINNED FACTS over the window, in one pass — four
      applications of §1a''s [wpt_byte_flat_pin] and nothing else. *)
  Lemma wpt4_flat_pin (σ : wmstate) (a : Arch.pa) (dq : dfrac) (w : bv 32) :
    wlog_wf (wm_log σ) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt4 a dq w) (wm_ws σ) -∗
    ⌜acc_wf a 4 ∧
     ∀ j : nat, (j < 4)%nat →
       wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte w j) ∧
       pinned_read σ (acc_addr a j)⌝.
  Proof.
    intros Hwf. rewrite /wpt4 !vwp_hold_sep !vwp_hold_pure.
    iIntros "Hi (%Hal & %Hacc & H0 & H1 & H2 & H3)".
    iDestruct (wpt_byte_flat_pin σ a 4 dq (nth_byte w 0) 0 Hwf Hacc
                 ltac:(lia) with "Hi H0") as %E0.
    iDestruct (wpt_byte_flat_pin σ a 4 dq (nth_byte w 1) 1 Hwf Hacc
                 ltac:(lia) with "Hi H1") as %E1.
    iDestruct (wpt_byte_flat_pin σ a 4 dq (nth_byte w 2) 2 Hwf Hacc
                 ltac:(lia) with "Hi H2") as %E2.
    iDestruct (wpt_byte_flat_pin σ a 4 dq (nth_byte w 3) 3 Hwf Hacc
                 ltac:(lia) with "Hi H3") as %E3.
    iPureIntro. split; [exact Hacc|]. intros j Hj.
    destruct j as [|[|[|[|j]]]]; [exact E0|exact E1|exact E2|exact E3|lia].
  Qed.

  (** WHAT THE FLAT PROJECTION HOLDS over the window — the fact the SC
      execute-lemma of a load wants, verbatim. *)
  Lemma wpt4_flat (σ : wmstate) (a : Arch.pa) (dq : dfrac) (w : bv 32) :
    wlog_wf (wm_log σ) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt4 a dq w) (wm_ws σ) -∗
    ⌜∀ j : nat, (j < 4)%nat →
       wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte w j)⌝.
  Proof.
    intros Hwf. iIntros "Hi Hpt".
    iDestruct (wpt4_flat_pin σ a dq w Hwf with "Hi Hpt") as %[_ Hall].
    iPureIntro. intros j Hj. exact (proj1 (Hall j Hj)).
  Qed.

  (** ... and that the window is PINNED for this hart, which is what the
      weak arm of [wstep_ok]'s read obligation asks for.  Kept SEPARATE from
      [wpt4_flat_pin] and free of its [wlog_wf] premise: pinnedness is a
      statement about views alone ([WeakBridge.wpt_pinned_read] needs no
      well-formedness), and a leaf that only owes the peel should not have to
      produce the log's well-formedness to discharge it. *)
  Lemma wpt4_pinned (σ : wmstate) (a : Arch.pa) (dq : dfrac) (w : bv 32) :
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt4 a dq w) (wm_ws σ) -∗
    ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr a j)⌝.
  Proof.
    iIntros "Hi Hpt". rewrite /wpt4 !vwp_hold_sep !vwp_hold_pure.
    iDestruct "Hpt" as "(%Hal & %Hacc & H0 & H1 & H2 & H3)".
    iDestruct (wpt_pinned_read σ (acc_addr a 0) dq (nth_byte w 0)
                 with "Hi H0") as %E0.
    iDestruct (wpt_pinned_read σ (acc_addr a 1) dq (nth_byte w 1)
                 with "Hi H1") as %E1.
    iDestruct (wpt_pinned_read σ (acc_addr a 2) dq (nth_byte w 2)
                 with "Hi H2") as %E2.
    iDestruct (wpt_pinned_read σ (acc_addr a 3) dq (nth_byte w 3)
                 with "Hi H3") as %E3.
    iPureIntro. intros j Hj.
    destruct j as [|[|[|[|j]]]]; [exact E0|exact E1|exact E2|exact E3|lia].
  Qed.

  (** MONOTONICITY across a step: the bundle is a [vProp], so
      [vwp_hold_mono] carries it over any view growth. *)
  Lemma wpt4_mono a dq w ws ws' :
    ws_le ws ws' → vwp_hold (wpt4 a dq w) ws ⊢ vwp_hold (wpt4 a dq w) ws'.
  Proof. apply vwp_hold_mono. Qed.

End word4.

Notation "a ↦w₄{ dq } w" := (wpt4 a dq w)
  (at level 20, format "a  ↦w₄{ dq }  w") : bi_scope.

(* ====================================================================== *)
(** ** 2. [wkernel_text] — the weak kernel-text resource

    An era-image byte's element is [wlat_pointsto a dq 0 v], which is an
    ordinary [iProp]: OBJECTIVE (so it may sit in an invariant and be shared
    across harts with no receipt), PERSISTENT at [DfracDiscarded], and — by §1
    — enough to pin the flat byte AND to give [pinned_read] for free.  That is
    the whole kernel-text story on the weak side: [wkernel_text] is what
    [RiscvPtsto.kernel_text] becomes, and its consumers get exactly the two
    facts the SC fetch reductions ([RiscvFetchExec.exec_fetch_done] & co.)
    take as premises. *)

Section text.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Definition wkernel_text (bs : gmap Arch.pa (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ b ∈ bs, wlat_pointsto (pa_z a) DfracDiscarded 0%nat b)%I.

  Global Instance wkernel_text_persistent bs : Persistent (wkernel_text bs).
  Proof. rewrite /wkernel_text. apply _. Qed.

  (** The [vProp] reading: a big-op of [WeakVProp.wpt_img]s, hence objective
      — this is the resource the design doc's "every discarded-fraction
      points-to is objective" bullet is about. *)
  Definition wkernel_text_v (bs : gmap Arch.pa (bv 8)) : vProp Σ :=
    ([∗ map] a ↦ b ∈ bs, wpt_img (pa_z a) DfracDiscarded b)%I.

  Global Instance wkernel_text_v_objective bs : Objective (wkernel_text_v bs).
  Proof. rewrite /wkernel_text_v. apply _. Qed.
  Global Instance wkernel_text_v_persistent bs : Persistent (wkernel_text_v bs).
  Proof. rewrite /wkernel_text_v. apply _. Qed.

  Lemma wkernel_text_at bs ws :
    vwp_hold (wkernel_text_v bs) ws ⊣⊢ wkernel_text bs.
  Proof.
    rewrite /vwp_hold /wkernel_text_v /wkernel_text monPred_at_big_sepM.
    apply big_sepM_proper. intros a b _. apply wpt_img_at.
  Qed.

  (** THE TWO FACTS A FETCH NEEDS, off one text byte. *)
  Lemma wkernel_text_flat (σ : wmstate) bs (a : Arch.pa) (b : bv 8) :
    wlog_wf (wm_log σ) → bs !! a = Some b →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wkernel_text bs -∗
    ⌜wflat (wm_img σ) (wm_log σ) !! a = Some b ∧
     latest_ts (wm_log σ) (pa_z a) = 0%nat⌝.
  Proof.
    intros Hwf Hlk. iIntros "Hi #Ht".
    iDestruct (big_sepM_lookup _ _ a _ Hlk with "Ht") as "He".
    by iApply (wpt_img_flat_lookup σ a DfracDiscarded b Hwf with "Hi He").
  Qed.

  (** ... and, over a whole window, the [pinned_read] side, which is what
      makes the fetch footprint free of any view hypothesis. *)
  Lemma wkernel_text_pinned (σ : wmstate) bs (a : Arch.pa) (n : nat) :
    acc_wf a (N.of_nat n) →
    (∀ j, (j < n)%nat → is_Some (bs !! pa_add a j)) →
    wlog_wf (wm_log σ) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wkernel_text bs -∗
    ⌜∀ j : nat, (j < n)%nat → pinned_read σ (acc_addr a j)⌝.
  Proof.
    intros Hacc Hdom Hwf. iIntros "Hi #Ht".
    rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
    destruct (Hdom j Hj) as [b Hb].
    iDestruct (wkernel_text_flat σ bs (pa_add a j) b Hwf Hb with "Hi Ht")
      as %[_ Hts].
    iPureIntro. apply pinned_read_unwritten.
    rewrite -(acc_wf_byte a (N.of_nat n) j Hacc ltac:(lia)). exact Hts.
  Qed.

End text.

(* ====================================================================== *)
(** ** 3. The pin certificate

    [WeakBridge.wstep_ok tid (riscv_step tick) σ] is the ONE peel a leaf owes
    (M3a item 1 merged the two M2b predicates into it).  Its content is
    per-access and small, but obtaining it means walking [riscv_step] down
    through [try_step], [run_hart_active], [fetch], the decoder and [execute]
    — the same walk [RiscvExec.exec_riscv_step_hart_active] and
    [RiscvFetchExec.exec_hart_active_progress] already do for [exec], and of
    the same size.  So it is treated the way this tree treats every other
    per-instruction model fact: as a PURE, caller-supplied obligation, stated
    once, here, in the form that makes its hypotheses discharge from
    resources.

    READ IT AS: "a step of the hart [cid] whose PC is [pc] touches the four
    text bytes at [pc] (which are unwritten this era) and, beyond that, only
    what [P] describes".  [P] is instantiated per leaf:

      - a plain LOAD:   [λ σ, acc_wf ea 4 ∧ (∀ j<4, pinned_read σ (acc_addr ea j))]
                        — discharged by [wpt4_pinned];
      - a plain STORE:  [λ σ, acc_wf ea 4] — a write has no read to pin;
      - [amoswap.w.aq]: [λ σ, acc_wf ea 4] — the read half is [ak_latest],
                        whose admissibility condition IS [WeakMem.latest]
                        ([WeakBridge.ak_pins]), so it needs NO ownership and
                        no view.  THIS is why the invariant form of the
                        acquire is possible at all;
      - [fence]:        [λ _, True] — no data access. *)


(**  AND WHAT THE CERTIFICATE ALSO CARRIES.  A leaf needs more than "the peel
    goes through": it needs the instruction's WEAK-MEMORY EFFECT — that a
    [fence rw,rw] really did raise the hart's index to the acquire frontier,
    that an acquire-AMO really did take the read timestamp into the scalar
    floor.  Those are facts about the same walk, so they ride in the same
    certificate as its second component [Q].

    THE TYPE OF [Q] IS THE SUCCESSOR *STATE*, NOT ITS VIEWS (M3b's correction,
    landed at M3c).  A store leaf has to retarget the latest-write elements of
    the bytes it wrote, so it must be able to say WHICH message the step
    appended — a statement about [wm_log σ'], which a [wstate] cannot express.
    The view-level predicates the leaf lemmas of §5 consume are spelled [wV_*];
    the certificate-level ones are the [wQ_*] built on top of them. *)

Definition wstep_cert (cid : nat) (pc : SailStdpp.Values.mword 64)
    (P : wmstate → Prop) (Q : wmstate → wmstate → Prop) : Prop :=
  ∀ (σ : wmstate) (tick : bool),
    register_lookup PC (wm_regs σ) = pc →
    acc_wf pc 4 →
    (∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pc j)) →
    P σ →
    wstep_ok (Some cid) (riscv_step tick) σ ∧
    (∀ χ σ' χ',
       wexec (Some cid) (riscv_step tick) χ σ = Some (tt, σ', χ') →
       Q σ σ').

(** The certificate is contravariant in [P] and covariant in [Q]. *)
Lemma wstep_cert_mono cid pc (P P' : wmstate → Prop) (Q Q' : wmstate → wmstate → Prop) :
  (∀ σ, P' σ → P σ) → (∀ σ σ', Q σ σ' → Q' σ σ') →
  wstep_cert cid pc P Q → wstep_cert cid pc P' Q'.
Proof.
  intros HP HQ Hc σ tick Hpc Hwf Htext HP'.
  destruct (Hc σ tick Hpc Hwf Htext (HP σ HP')) as [Hok Hq].
  split; [exact Hok|]. intros χ σ' χ' Hex.
  exact (HQ σ σ' (Hq χ σ' χ' Hex)).
Qed.

(* ====================================================================== *)
(** ** 4. THE RULE

    The weak analogue of the altitude
    [InstrBytes.wp_exec_step_decode_execute_inv] sits at: the caller supplies
    [exec] facts for both tick values — over the FLAT PROJECTION
    [WeakBridge.wflat_st σ], which is where every existing decode/execute
    lemma of the tree already lives — plus ONE certificate, and gets back a
    fully described successor.

    [wstep_post] is the successor's contract, and its last four conjuncts are
    what makes leaf composition cheap: the image never moves, the log only
    grows, the hart's views only grow (so [WeakVProp.vwp_hold_mono] carries
    every untouched resource across), and the two machine invariants
    ([wlog_wf], [ws_bounded]) are re-established. *)

Definition wstep_post (σ σ' : wmstate) (t : mstate) : Prop :=
  wm_regs σ' = sregs t ∧
  wm_dev σ' = mdev t ∧
  wflat (wm_img σ') (wm_log σ') = mem t ∧
  wm_img σ' = wm_img σ ∧
  (∃ l, wm_log σ' = (wm_log σ ++ l)%list) ∧
  ws_le (wm_ws σ) (wm_ws σ') ∧
  wlog_wf (wm_log σ') ∧
  ws_bounded (wm_ws σ') (length (wm_log σ')).

Lemma wstep_post_ws_le σ σ' t : wstep_post σ σ' t → ws_le (wm_ws σ) (wm_ws σ').
Proof. by intros (_ & _ & _ & _ & _ & ? & _ & _). Qed.

Lemma wstep_post_log_le σ σ' t :
  wstep_post σ σ' t → (length (wm_log σ) ≤ length (wm_log σ'))%nat.
Proof.
  intros (_ & _ & _ & _ & (l & Hl) & _ & _ & _). rewrite Hl length_app. lia.
Qed.

Section rule.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_winstr (pc : SailStdpp.Values.mword 64)
      (P : wmstate → Prop) (Q : wmstate → wmstate → Prop) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    wstep_cert (fin_to_nat cpu_id) pc P Q →
    (∀ σ, wmstate_interp σ ={⊤,∅}=∗
       ⌜register_lookup PC (wm_regs σ) = pc⌝ ∗
       ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pc j)⌝ ∗
       ⌜P σ⌝ ∗
       ∃ t0 t1 : mstate,
         ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝ ∗
         ⌜exec (riscv_step true) (wflat_st σ) = Some (tt, t1)⌝ ∗
         ▷ (∀ (tick : bool) (σ' : wmstate),
              ⌜wstep_post σ σ' (if tick then t1 else t0)⌝ -∗
              ⌜Q σ σ'⌝
              ={∅,⊤}=∗ wmstate_interp σ' ∗
                       WWP Loop)) -∗
    WWP Loop.
  Proof.
    iIntros (Hgid Haccpc Hcert) "H".
    iApply (wp_wexec_step with "[H]"); [exact Hgid|].
    iIntros (σ) "Hσ".
    iDestruct "Hσ" as "(%Hbnd & %Hnv & %Hwf & Hrest)".
    iMod ("H" $! σ with "[Hrest]") as "(%Hpc & %Htext & %HP & Hk)".
    { rewrite /wmstate_interp.
      iSplitR; [iPureIntro; exact Hbnd|].
      iSplitR; [iPureIntro; exact Hnv|].
      iSplitR; [iPureIntro; exact Hwf|]. iExact "Hrest". }
    iDestruct "Hk" as (t0 t1) "(%Hex0 & %Hex1 & Hk)".
    assert (Hc : ∀ tick : bool,
              wstep_ok (Some (fin_to_nat cpu_id)) (riscv_step tick) σ ∧
              (∀ χ σ' χ',
                 wexec (Some (fin_to_nat cpu_id)) (riscv_step tick) χ σ
                 = Some (tt, σ', χ') → Q σ σ'))
      by (intros tick; exact (Hcert σ tick Hpc Haccpc Htext HP)).
    iModIntro.
    iSplitR.
    { iPureIntro. intros tick. apply wstep_ok_covers, (proj1 (Hc tick)). }
    iSplitR.
    { iPureIntro.
      destruct (wexec_leaf_agree _ _ _ _ _ (proj1 (Hc false)) Hwf Hex0)
        as (_ & Hred & _).
      exact Hred. }
    iNext. iIntros (tick χ σ' χ' Hex).
    iApply ("Hk" $! tick σ').
    2:{ iPureIntro. exact (proj2 (Hc tick) χ σ' χ' Hex). }
    iPureIntro.
    assert (Hag : wm_regs σ' = sregs (if tick then t1 else t0) ∧
                  wm_dev σ' = mdev (if tick then t1 else t0) ∧
                  wflat (wm_img σ') (wm_log σ') = mem (if tick then t1 else t0) ∧
                  wlog_wf (wm_log σ')).
    { destruct tick.
      - destruct (wexec_leaf_agree _ _ _ _ _ (proj1 (Hc true)) Hwf Hex1)
          as (_ & _ & Hag).
        destruct (Hag χ tt σ' χ' Hex) as (_ & ? & ? & ? & ?). by split_and!.
      - destruct (wexec_leaf_agree _ _ _ _ _ (proj1 (Hc false)) Hwf Hex0)
          as (_ & _ & Hag).
        destruct (Hag χ tt σ' χ' Hex) as (_ & ? & ? & ? & ?). by split_and!. }
    destruct Hag as (Hr & Hd & Hm & Hw).
    pose proof (wexec_wrun _ _ _ _ _ _ _ Hex) as Hrun.
    rewrite /wstep_post. split_and!; try done.
    - exact (wrun_img _ _ _ _ _ Hrun).
    - exact (wrun_log_app _ _ _ _ _ Hrun).
    - exact (wrun_ws_le _ _ _ _ _ Hrun).
    - exact (wrun_ws_bounded _ _ _ _ _ Hrun Hbnd).
  Qed.

End rule.

(* ====================================================================== *)
(** ** 5. THE FOUR LEAVES

    One [P]/[Q] pair per instruction class, and the resource-side lemmas that
    discharge [P] and consume [Q].  Everything except the MEMORY ARM is
    already carried by §4 (registers, devices and the flat memory come out of
    [wstep_post]; the config tower is objective and untouched), so what is
    left here is exactly the weak-memory content of each instruction.

    THE WHOLE FAMILY IS WIDTH-GENERIC.  Nothing in any of these predicates is
    about the number 4 beyond the width of the access, so each is stated over
    an arbitrary [n : N] — the [_w] names below are the PRIMARY statements —
    and the width-4 names every consumer already uses are their [n := 4]
    instances, on the nose (each definition below is a delta step, so a
    [rewrite /wQ_store] still works; it now takes one more [/wQ_store_w] to
    reach the body).  [WeakWord8] supplies the [n := 8] instances the same
    way.  This is the M4-prep finding acted on: generalise before the sweep
    doubles the call sites, not after. *)

Definition wP_load_w (n : N) (ea : Arch.pa) : wmstate → Prop :=
  λ σ, acc_wf ea n ∧
       ∀ j : nat, (j < N.to_nat n)%nat → pinned_read σ (acc_addr ea j).
Definition wP_mem_w (n : N) (ea : Arch.pa) : wmstate → Prop :=
  λ _, acc_wf ea n.
Definition wP_none : wmstate → Prop := λ _, True.

(** *** The VIEW-level effects ([wV_*]) — what the leaf lemmas of §5 consume.
    Each says what the instruction did to the hart's index, as a relation
    between the pre-STATE (whose log length is the store's timestamp) and the
    post-state's [wstate]. *)

Definition wV_fence (b : barrier_kind) : wmstate → wstate → Prop :=
  λ σ ws', ws_le (barrier_post (wm_ws σ) b) ws'.
Definition wV_store_w (n : N) (ea : Arch.pa) : wmstate → wstate → Prop :=
  λ σ ws', ∀ j : nat, (j < N.to_nat n)%nat →
     (S (length (wm_log σ)) ≤ flr (ws_view ws') (acc_addr ea j))%nat.
Definition wV_amo_aq_w (n : N) (ea : Arch.pa) : wmstate → wstate → Prop :=
  λ σ ws', ∀ j : nat, (j < N.to_nat n)%nat →
     view_scl (latest_ts (wm_log σ) (acc_addr ea j)) ⊑ ws_view ws'.
Definition wV_load_w (n : N) (ea : Arch.pa) : wmstate → wstate → Prop :=
  λ σ ws', ∀ j : nat, (j < N.to_nat n)%nat →
     view_byte (acc_addr ea j) (latest_ts (wm_log σ) (acc_addr ea j)) ⊑ ws_view ws'.

(** *** The CERTIFICATE-level effects ([wQ_*]) — what [wstep_cert] carries.
    Over the successor STATE, so that a store's [Q] can name the message the
    step appended: without that identity the latest-write elements of the
    written bytes cannot be retargeted and [wmstate_interp σ'] is unprovable
    (M3b's finding; the two lock cores are stated at this shape). *)

Definition wQ_none : wmstate → wmstate → Prop := λ _ _, True.

(** [w_relp] after a barrier: a [pw ∧ sw] fence ARMS the next store.  It is
    absent from [ws_le] (it toggles), so [wV_fence] cannot carry it and
    [wQ_fence] states it separately — this is the one fact the release
    discipline of the φ-upgrade (§1) needs from a fence. *)
Definition barrier_arms (b : barrier_kind) : bool :=
  match b with
  | Barrier_RISCV_rw_w | Barrier_RISCV_w_w | Barrier_RISCV_rw_rw
  | Barrier_RISCV_w_rw | Barrier_RISCV_tso => true
  | _ => false
  end.

Lemma barrier_post_relp ws b :
  barrier_arms b = true -> w_relp (barrier_post ws b) = true.
Proof. destruct b; try discriminate; reflexivity. Qed.

Definition wQ_fence (b : barrier_kind) : wmstate → wmstate → Prop :=
  λ σ σ', wV_fence b σ (wm_ws σ') ∧
          (barrier_arms b = true → w_relp (wm_ws σ') = true).

Definition wQ_load_w (n : N) (ea : Arch.pa) : wmstate → wmstate → Prop :=
  λ σ σ', wm_img σ' = wm_img σ ∧ wm_log σ' = wm_log σ ∧
          wV_load_w n ea σ (wm_ws σ').

(** A width-[n] STORE of [v] to [ea]: ONE message at the log's fresh top, and
    the hart's own floor covers it afterwards.  The stored value's width [m]
    is left free — the message carries whatever the interpreter was handed. *)
(** [w_relp] IS INERT UNDER READS (φ-upgrade §1).  A load never touches the
    release-pending flag, so a store's class as computed by
    [WeakInterp.wm_class_of] at the post-fetch state is the class computed at
    the instruction's own entry state — which is what lets [wQ_store_w] below
    record "if the hart was release-pending, this message is not an owned
    store". *)
Lemma load_post_fold_relp aq vpre ats ws :
  w_relp (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats)
  = w_relp ws.
Proof.
  revert ws. induction ats as [|a l IH]; [done|]. intros ws. simpl. by rewrite IH.
Qed.

Lemma load_post_bytes_relp ws aq ats :
  w_relp (load_post_bytes ws aq ats) = w_relp ws.
Proof. apply load_post_fold_relp. Qed.

Lemma load_post_run_relp ws aq base ts :
  w_relp (load_post_run ws aq base ts) = w_relp ws.
Proof. apply load_post_bytes_relp. Qed.

Lemma wread_post_relp s ak pa ts :
  w_relp (wm_ws (wread_post s ak pa ts)) = w_relp (wm_ws s).
Proof.
  rewrite /wread_post. destruct (ak_coh ak); [reflexivity|].
  apply load_post_run_relp.
Qed.

(** ... hence a class computed at a state whose [w_relp] is set is never
    [WCplain]. *)
Lemma wm_class_of_relp ak ws : w_relp ws = true -> wm_class_of ak ws <> WCplain.
Proof.
  intros Hr. rewrite /wm_class_of Hr. by destruct (ak_latest ak).
Qed.

Definition wQ_store_w (n : N) (tid : option nat) (ea : Arch.pa) {m : N}
    (v : bv m) : wmstate → wmstate → Prop :=
  λ σ σ',
    wm_img σ' = wm_img σ ∧
    (* M6: the message's CLASS ([wm_ak], D-M6-6) is existential here.  It is
       fixed by the operational semantics ([WeakInterp.wwrite_post] computes
       [wm_class_of] from the access kind and the writer's own [w_relp]), and
       it differs between a plain store ([WCplain]/[WCrel]) and the AMO's
       write half ([WCexcl]) — so pinning it at this altitude would make
       [wQ_amo_aq_w] unprovable, since it is defined THROUGH this predicate.
       Nothing above the leaves reads the class; φ reads it off the log. *)
    (∃ k, wm_log σ' = (wm_log σ ++ [wwrite_msg tid k ea n v])%list ∧
          (w_relp (wm_ws σ) = true → k ≠ WCplain)) ∧
    ws_le (wm_ws σ) (wm_ws σ') ∧
    wV_store_w n ea σ (wm_ws σ').

(** [amoswap] with [.aq] writing [v]: the same store effect, PLUS the
    acquire's index gain — the scalar floor covers the timestamp the read half
    took, which is the latest write to the word ([ak_latest]). *)
Definition wQ_amo_aq_w (n : N) (tid : option nat) (ea : Arch.pa) {m : N}
    (v : bv m) : wmstate → wmstate → Prop :=
  λ σ σ', wQ_store_w n tid ea v σ σ' ∧ wV_amo_aq_w n ea σ (wm_ws σ') ∧
          (* M6/φ: an exclusive write half is [WCexcl] — pinned here (not in
             [wQ_store_w], where the class must stay existential) so that the
             lock word's invariant-held bundle can be retargeted CLEAN. *)
          wm_log σ' = (wm_log σ ++ [wwrite_msg tid WCexcl ea n v])%list.

(** *** The WIDTH-4 NAMES, as instances.  Every existing call site is
    unchanged; the only churn is that a proof which unfolded the body with
    [rewrite /wQ_store] now unfolds [/wQ_store /wQ_store_w]. *)

Definition wP_load (ea : Arch.pa) : wmstate → Prop := wP_load_w 4 ea.
Definition wP_mem (ea : Arch.pa) : wmstate → Prop := wP_mem_w 4 ea.
Definition wV_store (ea : Arch.pa) : wmstate → wstate → Prop := wV_store_w 4 ea.
Definition wV_amo_aq (ea : Arch.pa) : wmstate → wstate → Prop :=
  wV_amo_aq_w 4 ea.
Definition wV_load (ea : Arch.pa) : wmstate → wstate → Prop := wV_load_w 4 ea.
Definition wQ_load (ea : Arch.pa) : wmstate → wmstate → Prop := wQ_load_w 4 ea.
Definition wQ_store (tid : option nat) (ea : Arch.pa) (v : bv 32)
    : wmstate → wmstate → Prop := wQ_store_w 4 tid ea v.
Definition wQ_amo_aq (tid : option nat) (ea : Arch.pa) (v : bv 32)
    : wmstate → wmstate → Prop := wQ_amo_aq_w 4 tid ea v.

Lemma wQ_amo_aq_store tid ea v σ σ' :
  wQ_amo_aq tid ea v σ σ' → wQ_store tid ea v σ σ'.
Proof. by intros (? & _ & _). Qed.

Lemma wQ_amo_aq_excl tid ea v σ σ' :
  wQ_amo_aq tid ea v σ σ' →
  wm_log σ' = (wm_log σ ++ [wwrite_msg tid WCexcl ea 4 v])%list.
Proof. by intros (_ & _ & ?). Qed.

Lemma wQ_store_wV tid ea v σ σ' :
  wQ_store tid ea v σ σ' → wV_store ea σ (wm_ws σ').
Proof. by intros (_ & _ & _ & ?). Qed.

Lemma wQ_amo_aq_gain tid ea v σ σ' :
  wQ_amo_aq tid ea v σ σ' → wV_amo_aq ea σ (wm_ws σ').
Proof. by intros (_ & ? & _). Qed.

Section leaves.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Implicit Types R : vProp Σ.

  (* ------------------------------------------------------------------ *)
  (** *** 5a. [lw] / [ld] — the plain 4-byte LOAD, owned form

      Owning [ea ↦w₄{dq} w] at the hart's index does the whole job: it
      discharges the peel's read obligation ([wP_load]) and it pins the flat
      word, which is the premise the SC execute-lemma of a load
      ([ExecCommon]/[WpMmodeLoad]'s [exec_execute_LOAD_*]) takes verbatim.
      The value is thereby determined although the TIMESTAMP the oracle chose
      is not — that collapse is [WeakMem.readable_latest_pin], spent once
      inside [WeakBridge].  The points-to itself crosses the step by
      [wpt4_mono]; the view it gains is [WeakFence.load_byte_gain]'s. *)
  Lemma wwp_lw4 (σ : wmstate) (ea : Arch.pa) (dq : dfrac) (w : bv 32) :
    wlog_wf (wm_log σ) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt4 ea dq w) (wm_ws σ) -∗
    ⌜wP_load ea σ ∧
     (∀ j : nat, (j < 4)%nat →
        wflat (wm_img σ) (wm_log σ) !! pa_add ea j = Some (nth_byte w j))⌝.
  Proof.
    intros Hwf. iIntros "Hi Hpt".
    iDestruct (wpt4_flat_pin σ ea dq w Hwf with "Hi Hpt") as %[Hacc Hall].
    iPureIntro. split.
    - rewrite /wP_load /wP_load_w. split; [exact Hacc|].
      intros j Hj. exact (proj2 (Hall j Hj)).
    - intros j Hj. exact (proj1 (Hall j Hj)).
  Qed.

  (** ... and the frame: the loaded word survives the step. *)
  Lemma wwp_lw4_carry (σ σ' : wmstate) (t : mstate) ea dq w :
    wstep_post σ σ' t →
    vwp_hold (wpt4 ea dq w) (wm_ws σ) ⊢ vwp_hold (wpt4 ea dq w) (wm_ws σ').
  Proof. intros Hp. by apply wpt4_mono, (wstep_post_ws_le σ σ' t). Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 5b. [sw] / [sd] — the 4-byte STORE, and the release deposit

      A store has no read to pin, so its peel obligation is only
      wrap-freedom ([wP_mem]).  Its weak-memory content is entirely on the
      OUTPUT side, and it is a TIMESTAMP: the message lands at
      [S (length (wm_log σ))] — visible to the caller, because [σ] is — and
      [wV_store] says the hart's own index covers it afterwards.

      THE RELEASE DEPOSIT is the composition M3b's [release] needs: by
      [WeakMem.ws_bounded] (a conjunct of [wmstate_interp]) the releaser's
      WHOLE index is below that timestamp, so anything it holds may be frozen
      at the objective scalar view [view_scl (S (length log))] and handed to
      an invariant.  [WeakFence.release_deposit] is the arithmetic; this is
      it at the step altitude, where [ws_bounded] is in hand. *)
  Lemma wwp_release_deposit R (σ : wmstate) :
    ws_bounded (wm_ws σ) (length (wm_log σ)) →
    vwp_hold R (wm_ws σ) ⊢ monPred_at R (view_scl (S (length (wm_log σ)))).
  Proof. intros Hb. by apply (release_deposit R (wm_ws σ) (wm_log σ)). Qed.

  (** The store's own post-view, in the form the next instruction consumes:
      after the store the hart's floor at every byte of the word covers the
      store's timestamp. *)
  Lemma wwp_sw4_post (σ : wmstate) (ws' : wstate) ea :
    wV_store ea σ ws' →
    ∀ j : nat, (j < 4)%nat →
      view_byte (acc_addr ea j) (S (length (wm_log σ))) ⊑ ws_view ws'.
  Proof. intros HQ j Hj. apply view_byte_le. by apply HQ. Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 5c. [amoswap.w.aq] — THE ACQUIRE, invariant form

      The workhorse of the lock.  The read half of an AMO is [ak_latest]
      ([WeakInterp]'s access-kind table), whose admissibility condition IS
      [WeakMem.latest] — so [WeakBridge.ak_pins] holds and the read is on the
      pinned fragment with NO ownership and NO hypothesis about the reader's
      views.  Consequently the resource this leaf fires off is a BARE
      LATEST-WRITE ELEMENT BUNDLE, which is an [iProp], hence OBJECTIVE,
      hence admissible inside an invariant: an acquiring hart opens the lock
      invariant, hands the element bundle in, and gets back

        - the flat lock word (so the SC [amoswap] execute-lemma applies and
          returns it), and
        - the acquire's index gain [view_scl t ⊑ ws_view ws'] at the very
          timestamp [t] the element names,

      which THAWS the releaser's deposited [R @@ view_scl t] (§5b) into the
      acquirer's own index.  That is the whole handoff, and no view crosses
      the invariant boundary. *)
  Definition wlat4 (ea : Arch.pa) (dq : dfrac) (t : nat) (w : bv 32) : iProp Σ :=
    (wlat_pointsto (acc_addr ea 0) dq t (nth_byte w 0) ∗
     wlat_pointsto (acc_addr ea 1) dq t (nth_byte w 1) ∗
     wlat_pointsto (acc_addr ea 2) dq t (nth_byte w 2) ∗
     wlat_pointsto (acc_addr ea 3) dq t (nth_byte w 3))%I.

  Global Instance wlat4_objective ea dq t w : Objective (⎡wlat4 ea dq t w⎤ : vProp Σ).
  Proof. apply _. Qed.

  Lemma wwp_amoswap_w_aq_inv R (σ : wmstate) (ws' : wstate)
      (ea : Arch.pa) (dq : dfrac) (t : nat) (w : bv 32) :
    wlog_wf (wm_log σ) →
    acc_wf ea 4 →
    wV_amo_aq ea σ ws' →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat4 ea dq t w -∗
    monPred_at R (view_scl t) -∗
    ⌜wP_mem ea σ⌝ ∗
    ⌜∀ j : nat, (j < 4)%nat →
       wflat (wm_img σ) (wm_log σ) !! pa_add ea j = Some (nth_byte w j)⌝ ∗
    ⌜view_scl t ⊑ ws_view ws'⌝ ∗
    vwp_hold R ws'.
  Proof.
    intros Hwf Hacc HQ. iIntros "Hi (H0 & H1 & H2 & H3) HR".
    (* every byte of the word: the element determines the flat byte AND
       [latest_ts], because an element IS the latest write — four applications
       of §1a''s [wlat_byte_flat_gen] *)
    iAssert (⌜∀ j : nat, (j < 4)%nat →
               wflat (wm_img σ) (wm_log σ) !! pa_add ea j = Some (nth_byte w j)
               ∧ latest_ts (wm_log σ) (acc_addr ea j) = t⌝)%I as %Hall.
    { iDestruct (wlat_byte_flat_gen σ ea 4 dq t (nth_byte w 0) 0 Hwf Hacc
                   ltac:(lia) with "Hi H0") as %E0.
      iDestruct (wlat_byte_flat_gen σ ea 4 dq t (nth_byte w 1) 1 Hwf Hacc
                   ltac:(lia) with "Hi H1") as %E1.
      iDestruct (wlat_byte_flat_gen σ ea 4 dq t (nth_byte w 2) 2 Hwf Hacc
                   ltac:(lia) with "Hi H2") as %E2.
      iDestruct (wlat_byte_flat_gen σ ea 4 dq t (nth_byte w 3) 3 Hwf Hacc
                   ltac:(lia) with "Hi H3") as %E3.
      iPureIntro. intros j Hj.
      destruct j as [|[|[|[|j]]]]; [exact E0|exact E1|exact E2|exact E3|lia]. }
    assert (Hscl : view_scl t ⊑ ws_view ws').
    { rewrite -(proj2 (Hall 0%nat ltac:(lia))). apply HQ. lia. }
    iSplitR; [by iPureIntro|].
    iSplitR; [iPureIntro; intros j Hj; exact (proj1 (Hall j Hj))|].
    iSplitR; [by iPureIntro|].
    rewrite /vwp_hold. by iApply (monPred_mono R _ _ Hscl with "HR").
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 5d. [fence pred,succ]

      No data access at all, so the peel obligation is [wP_none].  The
      content is [wV_fence]: the hart's index really did move to what
      [WeakInterp.barrier_post] says, and for a succ-R fence with pred-RW
      that is exactly [WeakFence.acq_view] — so a [∇]-held assertion
      ([WeakFence.vwp_acq]) becomes an ordinary held one.  The two kinds the
      kernel uses instantiate directly. *)
  Lemma wwp_fence_deliver R (σ : wmstate) (ws' : wstate) :
    wV_fence Barrier_RISCV_rw_rw σ ws' →
    vwp_acq R (wm_ws σ) ⊢ vwp_hold R ws'.
  Proof.
    intros HQ. rewrite /vwp_acq /vwp_hold. apply monPred_mono.
    rewrite -(ws_view_barrier_rw_rw (wm_ws σ)). by apply ws_view_mono.
  Qed.

  (** [fence rw,rw] delivers everything deposited at a SCALAR view the hart
      has already read — the [started]/MP shape, and the reader half of a
      fence-mediated handoff. *)
  Lemma wwp_fence_scl_gen R (σ : wmstate) (ws' : wstate) (t : nat)
      (b : barrier_kind) :
    acq_pred_r b →
    wV_fence b σ ws' →
    (t ≤ w_vrOld (wm_ws σ))%nat →
    monPred_at R (view_scl t) ⊢ vwp_hold R ws'.
  Proof.
    intros Hb HQ Ht. rewrite /vwp_hold. apply monPred_mono.
    etrans; [by apply (view_scl_acq_pred_r b (wm_ws σ) t)|].
    by apply ws_view_mono.
  Qed.

  Lemma wwp_fence_scl R (σ : wmstate) (ws' : wstate) (t : nat) :
    wV_fence Barrier_RISCV_rw_rw σ ws' →
    (t ≤ w_vrOld (wm_ws σ))%nat →
    monPred_at R (view_scl t) ⊢ vwp_hold R ws'.
  Proof. exact (wwp_fence_scl_gen R σ ws' t _ acq_pred_r_rw_rw). Qed.

  (** THE ACQUIRE FENCE THE KERNEL ACTUALLY EXECUTES.  xv6's secondary-hart
      wait is [__atomic_load_n(&started, __ATOMIC_ACQUIRE)], and gcc puts the
      ordering in a [fence r,rw] AFTER the load, inside the loop
      ([kernel.asm], [main+0x18]).  Pred-R is enough: the timestamp being
      delivered is one this hart READ. *)
  Lemma wwp_fence_scl_r R (σ : wmstate) (ws' : wstate) (t : nat) :
    wV_fence Barrier_RISCV_r_rw σ ws' →
    (t ≤ w_vrOld (wm_ws σ))%nat →
    monPred_at R (view_scl t) ⊢ vwp_hold R ws'.
  Proof. exact (wwp_fence_scl_gen R σ ws' t _ acq_pred_r_r_rw). Qed.

  (** [fence rw,w] — the RELEASE fence.  Promise-free, a predecessor-W fence
      constrains nothing (design doc, Decision 1), so its leaf carries no
      view content beyond [ws_le]; the release's real content is
      [wwp_release_deposit] above.  Stated so the kind instantiates. *)
  Lemma wwp_fence_rw_w R (σ : wmstate) (ws' : wstate) :
    wV_fence Barrier_RISCV_rw_w σ ws' →
    vwp_hold R (wm_ws σ) ⊢ vwp_hold R ws'.
  Proof.
    intros HQ. apply vwp_hold_mono. etrans; [apply barrier_post_le|exact HQ].
  Qed.

End leaves.

(* ====================================================================== *)
(** ** 6. Smoke tests: two leaves in a row

    Not theorems of record — the check that the leaf statements above COMPOSE
    over §4's step contract with no glue, at the two shapes M3b needs.  Both
    are straight-line two-instruction sequences on one hart: the resource a
    leaf produces at step 1 is exactly what the leaf at step 2 consumes, and
    what carries it between them is [wstep_post] (the successor contract of
    [wp_winstr]) and nothing else. *)

Section smoke.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** [sw] ; [fence rw,rw] — the RELEASE/publication shape (the [started]
      handoff's writer side followed by a reader's fence). *)
  Example wwp_smoke_sw_fence (R : vProp Σ) (σ0 σ1 : wmstate) (ws2 : wstate) (t0 : mstate) :
    ws_bounded (wm_ws σ0) (length (wm_log σ0)) →
    wstep_post σ0 σ1 t0 →
    (S (length (wm_log σ0)) ≤ w_vrOld (wm_ws σ1))%nat →
    wV_fence Barrier_RISCV_rw_rw σ1 ws2 →
    vwp_hold R (wm_ws σ0) ⊢ vwp_hold R ws2.
  Proof.
    intros Hb Hp Hrd HQ.
    etrans; [by apply wwp_release_deposit|].
    exact (wwp_fence_scl R σ1 ws2 (S (length (wm_log σ0))) HQ Hrd).
  Qed.

  (** [amoswap.w.aq] ; [lw] — the ACQUIRE shape: the acquire thaws the
      payload the releaser deposited, and the following plain load of a byte
      the payload gave us still owns it one step later. *)
  Example wwp_smoke_amo_lw (R : vProp Σ) (σ0 σ1 σ2 : wmstate) (t1 : mstate)
      (ea la : Arch.pa) (dq : dfrac) (t : nat) (w lw : bv 32) :
    wlog_wf (wm_log σ0) →
    acc_wf ea 4 →
    wV_amo_aq ea σ0 (wm_ws σ1) →
    wstep_post σ1 σ2 t1 →
    (wlat_interp (wm_img σ0) (wm_log σ0) : iProp Σ) -∗
    wlat4 ea dq t w -∗
    monPred_at (R ∗ wpt4 la (DfracOwn 1) lw) (view_scl t) -∗
    ⌜∀ j : nat, (j < 4)%nat →
       wflat (wm_img σ0) (wm_log σ0) !! pa_add ea j = Some (nth_byte w j)⌝ ∗
    vwp_hold R (wm_ws σ2) ∗ vwp_hold (wpt4 la (DfracOwn 1) lw) (wm_ws σ2).
  Proof.
    intros Hwf Hacc HQ Hp. iIntros "Hi Hl HR".
    iDestruct (wwp_amoswap_w_aq_inv (R ∗ wpt4 la (DfracOwn 1) lw) σ0 (wm_ws σ1)
                 ea dq t w Hwf Hacc HQ with "Hi Hl HR")
      as "(_ & %Hflat & _ & Hpay)".
    iSplitR; [by iPureIntro|].
    rewrite vwp_hold_sep. iDestruct "Hpay" as "[HR Hpt]".
    iSplitL "HR"; iApply (vwp_hold_mono _ (wm_ws σ1) (wm_ws σ2));
      [exact (wstep_post_ws_le σ1 σ2 t1 Hp)|iExact "HR"
      |exact (wstep_post_ws_le σ1 σ2 t1 Hp)|iExact "Hpt"].
  Qed.

End smoke.
