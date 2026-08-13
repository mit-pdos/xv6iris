(** * WkWalkRule.v — THE S-MODE RACY WP RULE OF A FETCH-WALKING STEP
      (walk-bridge §8, 6b: the WP layer above [WkStepPeel])

    [WkStepPeel] delivers, in PURE form, the three halves of a whole
    instruction step whose FETCH walks the page table and whose EXECUTE phase
    is window-free: the PEEL ([wstep_peel_fetchwalk]), the step-level FAMILY
    at the stale mirror ([wstep_family_fetchwalk]) and the Q-half
    ([wstep_outcome_fetchwalk] / [wexec_outcome_of_peel]).  This file lifts
    that triple to ONE weakest-precondition step rule, [wp_wwalk_step], in
    exactly the shape [WeakRacy]'s [wp_wracy_load] has — same [wp_wrun_step]
    plumbing, same σ-callback, same ▷-continuation discipline — with the
    walk's two structural deltas:

      - THE CERTIFICATE IS AT [wD_any] / [W := True] (the started cone's
        [wp_wracy_load] is pinned at [D := racc_disj ra rn] / [W := False]).
        A walking step WRITES (the A/D write-back), so the peel cannot be
        taken at the racy rules' write-refusing instance; [WkStepPeel]'s peel
        is stated at [wD_any]/[True] and this rule consumes it there.

      - THE CONTINUATION IS HANDED AN [exec_stale] EQUATION, not a patched-
        [exec] one.  [wp_wracy_load] tells its caller
        [exec (riscv_step tick) (wpatch_st σ ra rn w) = Some (tt, wpatch_st σ' …)];
        for a walk that would demand the whole fetch/decode/execute skeleton
        mirrored over patched memory.  What the ⇐-bridge actually proves —
        and what the leaf's ghost work rewrites the FAMILY against — is
        [exec_stale la 8 w (riscv_step tick) (wflat_st σ)
           = Some (tt, wflat_st σ', es)]
        for ONE admissible leaf word [w], together with the §10 preservation
        conjuncts ([wlog_wf]; [latest_ts] unmoved off the trace's writes,
        which is what a consumer turns back into pinnedness; and the
        LOG-IDENTITY equation [wm_log σ' = wm_log σ ++ wtrace_msgs …, which
        names the appended messages themselves).

      - THE LOG-IDENTITY CONJUNCT IS WHAT LETS THE LEAF MOVE ITS LOG
        AUTHORITY.  Re-establishing [wmstate_interp σ'] means owning
        [wlog_auth (wm_log σ')], and the [exec_stale] equation does NOT force
        the log: it pins the FLAT memory, and a same-value rewrite appends a
        message while moving no byte.  §4 below computes the projection on the
        walk's six trace shapes — [[]] on the four read-only ones (so the
        authority is unchanged), and the single [WCexcl] message on the two
        write-back ones, which is precisely the tail the absorption theorem's
        appended-log arm ([WeakKptStale]'s [wtlb_res_pt_translateAddr_stale_at])
        already hands out.

    ==================================================================
    THE φ-UPGRADE OBLIGATION AT THIS RULE IS THE *CLEAN-WINDOW* ARM,
    NOT [sync_win].
    ==================================================================

    [wp_wracy_load] carries a persistent [sync_win ra rn] premise: its window
    is a genuine single-occurrence racy window (the [started] flag), and §C's
    violation-freedom preservation reads sync-ness there.  THIS rule has NO
    such premise, and the omission is a recorded decision, not an oversight —
    the walk-bridge decision record (claude-notes/design/weak-memory-walk-
    bridge.md, "DECISION (2026-08-12, the φ-upgrade author)"):

      Under the C/D/S points-to surgery a TRANSLATION IS NOT A RACY-WINDOW
      CONSUMER AT ALL.  The PTE bytes' [wlat] elements live in the kpt /
      proc-pt resources as CLEAN fragments, and BOTH of the walk's reads —
      the plain stale read and the exclusive-latest CAS read — discharge the
      φ obligation through the CLEAN arm of the load trichotomy: a clean
      element gives clean-purity, i.e. every [WCplain] message on the byte is
      published, so no timestamp the racy read may land on is a foreign
      unpublished owned store.  The witness that the walk's window is in that
      state is the absorption theorem's own export: [WeakKptStale]'s
      [wtlb_res_pt_translateAddr_stale_at] hands out
      [forall j < 8, nv_free (wm_log σ) (acc_addr la j)]
      alongside the family and the register wand.

    WIRING THAT EXPORT INTO φ'S PRESERVATION IS THE φ-MECHANIZATION'S ITEM,
    NOT THIS FILE'S — it belongs where the state interpretation's [nv_hart]
    conjunct is re-established (WeakGhost), and it has to be re-established
    per byte the step touches, which is a resource-side argument this pure
    rule has no access to.  The debt is flagged HERE so that the INTERFACE
    records it: a caller of [wp_wwalk_step] owes, at the resource level, the
    clean/published state of the eight PTE bytes of [la] — the same fact the
    absorption theorem already exports — and NOT a sync token.

    ==================================================================

    Design: claude-notes/design/weak-memory-walk-bridge.md §8. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import RiscvTryStep.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakGhost WeakExec.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff.
Require Import WeakEffSkel WeakLeafEffCommon WeakFetchEff.
Require Import WeakRacy WeakVarCert WeakStale WeakWalkStale.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree.
Require Import SmodeCore.
Require Import WeakWalkEff.
Require Import WeakVariant WeakKpt WeakKptStale.
Require Import WkFetchPeel WkStepPeel.
Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE CERTIFICATE

    [WeakRacy]'s [wracy_cert], with the three deltas the walk forces.  The
    hypotheses are VERBATIM the racy certificate's (the PC lookup, the fetch
    window's well-formedness and pinnedness, and the caller's own state
    predicate [P]); what changes is the three conclusions:

    (a) the PEEL is at the walk's leaf window [(la, 8)], at [wak_plain], and
        at [wD_any] / [W := True] — the instance [WkStepPeel]'s
        [wstep_peel_fetchwalk] produces;

    (b) THE FAMILY, spelled EXACTLY as [wexec_outcome_of_peel] consumes it:
        the disjunction whose left arm is the five stale-friendly walk shapes
        ([trace_stale]) and whose right arm is the TLB-hit write-back
        ([trace_off_win], the constant-family shape).  This is literally
        [wstep_family_fetchwalk]'s conclusion at [Φ := wwalk_filter w0 lw];

    (c) the Q-half, unchanged in shape from [wracy_cert]. *)

Definition wwalk_cert (cid : nat) (pc : SailStdpp.Values.mword 64)
    (la : Arch.pa) (Φ : (nat -> bv 8) -> Prop)
    (P : wmstate -> Prop) (Q : wmstate -> wmstate -> Prop) : Prop :=
  forall (σ : wmstate) (tick : bool),
    register_lookup PC (wm_regs σ) = pc ->
    acc_wf pc 4 ->
    (forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pc j)) ->
    P σ ->
    (* (a) the peel of the whole step, at the leaf window *)
    wstep_ok_racy (Some cid) la 8 wak_plain Φ wD_any True true
      (riscv_step tick) σ /\
    (* (b) the step-level family at the stale mirror *)
    ((forall u : bv (8 * 8)%N, Φ (fun j : nat => nth_byte u j) ->
        exists (y : unit) (t' : mstate) (es : list weff),
          exec_stale la 8 u (riscv_step tick) (wflat_st σ) = Some (y, t', es) /\
          trace_stale wak_plain la 8 es)
     \/
     (forall u : bv (8 * 8)%N, Φ (fun j : nat => nth_byte u j) ->
        exists (y : unit) (t' : mstate) (es : list weff),
          exec_stale la 8 u (riscv_step tick) (wflat_st σ) = Some (y, t', es) /\
          trace_off_win la 8 es)) /\
    (* (c) the Q-half *)
    (forall χ σ' χ',
       wexec (Some cid) (riscv_step tick) χ σ = Some (tt, σ', χ') ->
       Q σ σ').

(* ====================================================================== *)
(** ** 2. THE RULE *)

Section rule.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (** THE S-MODE RACY STEP RULE.

      Statement-for-statement [WeakRacy.wp_wracy_load], with:

        - the window fixed to the walk's leaf slot [(la, 8)] at [wak_plain]
          (a walker read is plain-tier; the CAS read inside the write-back is
          the exclusive one and is PINNED, which is why it does not appear
          here at all);

        - NO [sync_win] premise — see the file header for the decision record
          and for what a caller owes instead;

        - an [exec_stale] equation plus the §10 preservation conjuncts in the
          continuation, in place of the patched-[exec] equation.

      WHAT THE CALLER SUPPLIES ABOUT MEMORY is unchanged from the template:
      that the window is IN memory ([is_Some (read_bytes …)]), that every
      admissible word passes the certificate's filter
      ([wadm_filter]), and ONE ordinary [exec] fact about [wflat_st σ] — the
      reducibility witness, taken at the COHERENT (pinned) value.

      WHAT THE CALLER GETS BACK, for the run that actually happened, is the
      racy leaf word [u], its admissibility and filter membership, the mirror
      run's own trace [es], and the equation identifying the successor's flat
      projection with that mirror run's post-state. *)
  Lemma wp_wwalk_step (pc : SailStdpp.Values.mword 64) (la : Arch.pa)
      (Φ : (nat -> bv 8) -> Prop) (P : wmstate -> Prop)
      (Q : wmstate -> wmstate -> Prop) :
    gen_id = 0%nat ->
    acc_wf pc 4 ->
    acc_wf la 8 ->
    wwalk_cert (fin_to_nat cpu_id) pc la Φ P Q ->
    (∀ σ, wmstate_interp σ ={⊤,∅}=∗
       ⌜register_lookup PC (wm_regs σ) = pc⌝ ∗
       ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pc j)⌝ ∗
       ⌜P σ⌝ ∗
       ⌜wadm_filter σ wak_plain la 8 Φ⌝ ∗
       ⌜is_Some (read_bytes (wflat (wm_img σ) (wm_log σ)) la 8)⌝ ∗
       (∃ t0 : mstate,
          ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝) ∗
       ▷ (∀ (tick : bool) (σ' : wmstate) (u : bv (8 * 8)%N) (es : list weff),
            ⌜wadm σ wak_plain la 8 u⌝ -∗
            ⌜Φ (fun j : nat => nth_byte u j)⌝ -∗
            ⌜exec_stale la 8 u (riscv_step tick) (wflat_st σ)
             = Some (tt, wflat_st σ', es)⌝ -∗
            ⌜∀ a : Arch.pa,
               wtrace_wonly (fun (pa : Arch.pa) (n : N) =>
                   ∀ j : nat, (j < N.to_nat n)%nat → pa_add pa j ≠ a) es →
               latest_ts (wm_log σ') (pa_z a) = latest_ts (wm_log σ) (pa_z a)⌝ -∗
            ⌜wm_log σ' = (wm_log σ
                          ++ wtrace_msgs (Some (fin_to_nat cpu_id))
                               (w_relp (wm_ws σ)) es)%list⌝ -∗
            ⌜wstep_post_racy σ σ'⌝ -∗
            ⌜Q σ σ'⌝
            ={∅,⊤}=∗ wmstate_interp σ' ∗
                     WWP Loop)) -∗
    WWP Loop.
  Proof.
    iIntros (Hgid Haccpc Hacc Hcert) "H".
    iApply (wp_wrun_step with "[H]"); [exact Hgid|].
    iIntros (σ) "Hσ".
    iDestruct "Hσ" as "(%Hbnd & %Hnv & %Hwf & Hrest)".
    iMod ("H" $! σ with "[Hrest]")
      as "(%Hpc & %Htext & %HP & %HΦ & %Hrd & Ht0 & Hk)".
    { rewrite /wmstate_interp.
      iSplitR; [iPureIntro; exact Hbnd|].
      iSplitR; [iPureIntro; exact Hnv|].
      iSplitR; [iPureIntro; exact Hwf|]. iExact "Hrest". }
    iDestruct "Ht0" as (t0) "%Hex0".
    assert (Hc : ∀ tick : bool,
              wstep_ok_racy (Some (fin_to_nat cpu_id)) la 8 wak_plain Φ
                wD_any True true (riscv_step tick) σ ∧
              ((∀ u : bv (8 * 8)%N, Φ (fun j : nat => nth_byte u j) →
                  ∃ (y : unit) (t' : mstate) (es : list weff),
                    exec_stale la 8 u (riscv_step tick) (wflat_st σ)
                    = Some (y, t', es) ∧ trace_stale wak_plain la 8 es)
               ∨
               (∀ u : bv (8 * 8)%N, Φ (fun j : nat => nth_byte u j) →
                  ∃ (y : unit) (t' : mstate) (es : list weff),
                    exec_stale la 8 u (riscv_step tick) (wflat_st σ)
                    = Some (y, t', es) ∧ trace_off_win la 8 es)) ∧
              (∀ χ σ' χ',
                 wexec (Some (fin_to_nat cpu_id)) (riscv_step tick) χ σ
                 = Some (tt, σ', χ') → Q σ σ'))
      by (intros tick; exact (Hcert σ tick Hpc Haccpc Htext HP)).
    iModIntro.
    iSplitR.
    { (* REDUCIBILITY: the caller's [exec] fact at the coherent value, moved
         to [wexec] by the W-generic [wexec_of_exec_racy] at [W := True]. *)
      iPureIntro.
      destruct (wexec_of_exec_racy (Some (fin_to_nat cpu_id)) la 8 wak_plain Φ
                  wD_any True (riscv_step false) Hacc true σ
                  (proj1 (Hc false)) Hwf (fun _ => HΦ) tt t0 Hex0)
        as (χ & σ0 & χ' & Hw & _).
      by exists χ, σ0, χ'. }
    iNext. iIntros (tick σ' Hrun).
    (* the actual run, as a [wexec] run at SOME oracle — [wrun_wexec_racy] is
       likewise W-generic, so it applies at [W := True] *)
    destruct (wrun_wexec_racy (Some (fin_to_nat cpu_id)) la 8 wak_plain Φ
                wD_any True (riscv_step tick) true σ (proj1 (Hc tick))
                (fun _ => HΦ) tt σ' Hrun) as (χ & χ' & Hwex).
    (* the Q-half in pure form: peel + family ⇒ one family member matches *)
    destruct (wexec_outcome_of_peel (Some (fin_to_nat cpu_id)) σ la Φ tick
                Hacc Hwf Hrd (proj1 (Hc tick)) HΦ (proj1 (proj2 (Hc tick)))
                χ tt σ' χ' Hwex)
      as (u & es & Hadm & HΦu & Hex & Hwf' & Hlat & Hlog).
    iApply ("Hk" $! tick σ' u es with "[%] [%] [%] [%] [%] [%] [%]").
    - exact Hadm.
    - exact HΦu.
    - exact Hex.
    - exact Hlat.
    - exact Hlog.
    - rewrite /wstep_post_racy. split_and!.
      + exact (wrun_img _ _ _ _ _ Hrun).
      + exact (wrun_log_app _ _ _ _ _ Hrun).
      + exact (wrun_ws_le _ _ _ _ _ Hrun).
      + exact Hwf'.
      + exact (wrun_ws_bounded _ _ _ _ _ Hrun Hbnd).
    - exact (proj2 (proj2 (Hc tick)) χ σ' χ' Hwex).
  Qed.

End rule.

(* ====================================================================== *)
(** ** 3. THE CERTIFICATE IS INHABITED BY THE LANDED LAYER

    The glue that shows [wwalk_cert] is not a wish: [WkStepPeel]'s
    [wstep_peel_fetchwalk] gives (a) and [wstep_family_fetchwalk] gives (b),
    from ONE premise bundle — the union of their two premise lists, minus the
    PC lookup, which the certificate's own hypothesis already supplies.

    PACKAGING.  Both landed lemmas quantify their state σ OUTSIDE (they are
    facts about one σ), while the certificate quantifies σ and [tick] INSIDE.
    The bundle is therefore stated as a σ- and [tick]-indexed predicate
    [wwalk_site] and the glue asks for it AT EVERY σ SATISFYING [P] — which is
    exactly how the funnel will instantiate it: [P] is the site predicate the
    leaf's fupd re-establishes at each step, and the walk exports / tails /
    family-readiness are read off it.  No lemma here is heavy; the whole glue
    is a destructuring plus two [exact]s. *)

(** The σ-dependent premise bundle of [WkStepPeel] §§4–5, verbatim.  The
    fetch-side geometry ([racc_disj], the alignments, the PMA gate) is
    σ-independent but is carried here too, so that ONE hypothesis of the glue
    covers the two landed lemmas' premise lists between them. *)
Definition wwalk_site (tid : option nat) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : mword 64) (region : PMA_Region) (w : mword 32)
    (σ : wmstate) (tick : bool) : Prop :=
  let vpn := svpn_of va in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  (* --- the step's own register gates (the PC lookup comes from the
         certificate's hypothesis) --- *)
  register_lookup cur_privilege (wm_regs σ) = Supervisor /\
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt /\
  (forall bmi : bool,
     exec_eff (dispatchInterrupt Supervisor) (wflat_st (wmi σ bmi))
     = Some (None, wflat_st (wmi σ bmi), [])) /\
  (* --- the walk exports and the fetch's gates, at the post-write states --- *)
  (forall bmi : bool,
     wfetch_ready tid (wmi σ bmi) root_ppn va pa p2 p1 w0 lw region) /\
  (* --- the text window --- *)
  is_aligned_vaddr (Virtaddr va) 4 = true /\
  isRVC (subrange_vec_dec w 15 0) = false /\
  racc_disj la 8 pa 4 /\
  acc_wf pa 4 /\
  (forall j : nat, (j < 4)%nat -> pa_z (pa_add pa j) <> 0) /\
  (forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pa j)) /\
  (forall j : nat, (N.of_nat j < 4)%N ->
     wflat (wm_img σ) (wm_log σ) !! (pa_add pa j) = Some (nth_byte w j)) /\
  is_aligned_paddr (Physaddr pa) 4 = true /\
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true /\
  dev_addr pa = false /\
  (* --- the tails, on both sides of the bridge --- *)
  (forall bmi : bool, wexec_tail tid (wmi σ bmi)) /\
  (forall bmi : bool, wstep_post_tail tid (wmi σ bmi)) /\
  wstep_tick_tail tid σ tick /\
  wstep_family_ready tid σ la va pa w tick.

(** THE INHABITATION.  [P] is the caller's site predicate; the two premises
    are "every [P]-state is a walking-fetch site" and the Q-half. *)
Lemma wp_wwalk_step_cert_of_peel (cid : nat) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : mword 64) (region : PMA_Region) (w : mword 32)
    (P : wmstate -> Prop) (Q : wmstate -> wmstate -> Prop) :
  let vpn := svpn_of va in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  (forall (σ : wmstate) (tick : bool), P σ ->
     wwalk_site (Some cid) root_ppn va pa p2 p1 w0 lw region w σ tick) ->
  (forall (σ : wmstate) (tick : bool) (χ : list (list nat)) (σ' : wmstate)
          (χ' : list (list nat)),
     P σ -> wexec (Some cid) (riscv_step tick) χ σ = Some (tt, σ', χ') ->
     Q σ σ') ->
  wwalk_cert cid va la (wwalk_filter w0 lw) P Q.
Proof.
  intros vpn la Hsite HQ σ tick Hpc Haccpc Hpinpc HP.
  destruct (Hsite σ tick HP) as (Hpriv & Hhart & Hdisp & Hready & Hal & HnotRVC
    & Hdisj & Haccp & HW0 & Hpin & Hbytes & Halign & Hexecp & Hdev & Hexec
    & Hpost & Htick & Hfam).
  split_and!.
  - exact (proj1 (wstep_peel_fetchwalk (Some cid) σ root_ppn va pa p2 p1 w0 lw
             region w tick Hpriv Hhart Hpc Hdisp Hready Hal Hdisj Haccp HW0
             Hpin Hbytes Halign Hexecp Hdev Hexec Hpost Htick)).
  - exact (wstep_family_fetchwalk (Some cid) σ root_ppn va pa p2 p1 w0 lw w tick
             Hpriv Hhart Hpc Hdisp (fun bmi => proj1 (Hready bmi)) Hal HnotRVC
             Haccp Hdisj Hfam).
  - intros χ σ' χ' Hwex. exact (HQ σ tick χ σ' χ' HP Hwex).
Qed.

(** The [wadm_filter] half of the σ-callback comes from the SAME bundle — it
    is [wstep_peel_fetchwalk]'s second conjunct — so a caller that has a
    [wwalk_site] owes nothing extra for the rule's fourth pure output. *)
Lemma wwalk_site_adm_filter (cid : nat) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : mword 64) (region : PMA_Region) (w : mword 32)
    (σ : wmstate) (tick : bool) :
  let vpn := svpn_of va in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  register_lookup PC (wm_regs σ) = va ->
  wwalk_site (Some cid) root_ppn va pa p2 p1 w0 lw region w σ tick ->
  wadm_filter σ wak_plain la 8 (wwalk_filter w0 lw).
Proof.
  intros vpn la Hpc (Hpriv & Hhart & Hdisp & Hready & Hal & HnotRVC & Hdisj &
    Haccp & HW0 & Hpin & Hbytes & Halign & Hexecp & Hdev & Hexec & Hpost &
    Htick & Hfam).
  exact (proj2 (wstep_peel_fetchwalk (Some cid) σ root_ppn va pa p2 p1 w0 lw
           region w tick Hpriv Hhart Hpc Hdisp Hready Hal Hdisj Haccp HW0
           Hpin Hbytes Halign Hexecp Hdev Hexec Hpost Htick)).
Qed.

(* ====================================================================== *)
(** ** 4. THE LOG-IDENTITY CONJUNCT, ON THE WALK'S SIX TRACE SHAPES

    The rule's continuation is handed [wm_log σ' = wm_log σ ++ wtrace_msgs …
    es] at the run's OWN trace [es], and the caller pins [es] by rewriting the
    [exec_stale] equation against the family it owns — which is the absorption
    theorem's, whose traces are six literal shapes.  These four lemmas compute
    the projection on all six, so the leaf never unfolds [wtrace_msgs].

    THE CLASS AGREES ON BOTH SIDES.  The walk's write-back event is
    [WEwrite (AkInfo false true false) la 8 lw'] — [wak_excl], i.e.
    [ak_latest = true] — and [wm_class_rp] sends every [ak_latest] write to
    [WCexcl] regardless of the writer's pending-release flag
    ([WeakStale.wm_class_rp_latest]).  So the message the projection names is
    [wwrite_msg tid WCexcl la 8 lw'], which is exactly what the absorption
    theorem's appended-log arm carries (its [kcls] existential is instantiated
    at [WCexcl] by its own proof).  No mismatch: the two sides model the CAS
    write-back at the same class, and the walk's write is the ONE case where
    the class is recoverable from the trace event alone. *)

(** (a) THE FOUR READ-ONLY SHAPES: nothing is appended. *)
Lemma wtrace_msgs_walk_ro (tid : option nat) (rp : bool)
    (a2 a1 la : Arch.pa) (es : list weff) :
  (es = [] \/
   es = [WEread wak_plain a2 8; WEread wak_plain a1 8; WEread wak_plain la 8] \/
   es = [WEread (AkInfo false true false) la 8] \/
   es = [WEread wak_plain a2 8; WEread wak_plain a1 8; WEread wak_plain la 8;
         WEread (AkInfo false true false) la 8]) ->
  wtrace_msgs tid rp es = [].
Proof. intros [->|[->|[-> | ->]]]; reflexivity. Qed.

(** ... so the successor's log IS the pre-log, which is what re-establishing
    an UNCHANGED [wlog_auth] needs. *)
Lemma wm_log_of_msgs_nil (tid : option nat) (rp : bool) (σ σ' : wmstate)
    (es : list weff) :
  wtrace_msgs tid rp es = [] ->
  wm_log σ' = (wm_log σ ++ wtrace_msgs tid rp es)%list ->
  wm_log σ' = wm_log σ.
Proof. intros Hnil ->. rewrite Hnil List.app_nil_r //. Qed.

(** (b) THE TWO WRITE-BACK SHAPES: exactly the one [WCexcl] message. *)
Lemma wtrace_msgs_walk_wb (tid : option nat) (rp : bool)
    (a2 a1 la : Arch.pa) (lw' : mword 64) (wtr : bool) (es : list weff) :
  es = (if wtr
        then [WEread wak_plain a2 8; WEread wak_plain a1 8; WEread wak_plain la 8;
              WEread (AkInfo false true false) la 8;
              WEwrite (AkInfo false true false) la 8 (lw' : mword 64)]
        else [WEread (AkInfo false true false) la 8;
              WEwrite (AkInfo false true false) la 8 (lw' : mword 64)]) ->
  wtrace_msgs tid rp es
  = [wwrite_msg tid WCexcl (la : Arch.pa) 8 (lw' : mword 64)].
Proof. intros ->. by destruct wtr. Qed.

(** ... so the successor's log is the pre-log plus that message — the shape
    [WeakKptStale]'s appended-log arm states its [wlog_auth] in. *)
Lemma wm_log_of_walk_wb (tid : option nat) (rp : bool) (a2 a1 la : Arch.pa)
    (lw' : mword 64) (wtr : bool) (σ σ' : wmstate) (es : list weff) :
  es = (if wtr
        then [WEread wak_plain a2 8; WEread wak_plain a1 8; WEread wak_plain la 8;
              WEread (AkInfo false true false) la 8;
              WEwrite (AkInfo false true false) la 8 (lw' : mword 64)]
        else [WEread (AkInfo false true false) la 8;
              WEwrite (AkInfo false true false) la 8 (lw' : mword 64)]) ->
  wm_log σ' = (wm_log σ ++ wtrace_msgs tid rp es)%list ->
  wm_log σ' = (wm_log σ
               ++ [wwrite_msg tid WCexcl (la : Arch.pa) 8 (lw' : mword 64)])%list.
Proof.
  intros Hes ->. by rewrite (wtrace_msgs_walk_wb tid rp a2 a1 la lw' wtr es Hes).
Qed.

(* ====================================================================== *)
(** ** 5. Soundness checks *)

Print Assumptions wp_wwalk_step.
Print Assumptions wp_wwalk_step_cert_of_peel.
Print Assumptions wwalk_site_adm_filter.
