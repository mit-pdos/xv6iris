(** * WeakViewRacy.v — PROTOTYPE: the [wp_wracy_load] experiment.

    Design: [`claude-notes/design/weak-memory-sc-parity.md`] §6, RISK 2 —
    "exactness vs lower bounds".  The recorded worry was:

    > [WeakRacy.wp_wracy_load] quantifies over the ADMISSIBLE READ RESULTS,
    > and that set is computed from the hart's actual weak state, which a
    > lower bound may under-determine.  If so, keep an exact fragment
    > available for the racy sites — but this must be CHECKED, not assumed,
    > because it decides whether the racy layer survives unchanged.

    THIS FILE CHECKS IT, and the answer is that a lower bound suffices.

    WHY (the shape of the argument, which is worth stating before the Coq).
    Admissibility is ANTITONE in the hart's state: [WeakInterp.wbyte_ok]
    depends on [wm_ws] only through

      [readable img log ws vpre a t
         := is_Some (log_byte img log t a)
            /\ ~ writes_in log a t (Nat.max vpre (coh ws a))]

    and [load_vpre ws aq := Nat.max (w_vrNew ws) (...)].  A LARGER [ws]
    raises the exclusion window [Nat.max vpre (coh ws a)], so it excludes
    MORE timestamps.  Racy clients never want to enlarge the admissible set —
    they want to shrink it, i.e. to rule out stale reads — and shrinking is
    driven by knowing the hart's view is AT LEAST something.  That is exactly
    a lower bound.

    The landed exclusion lemmas already say so in their own statements:
    [WeakKpt.wbyte_ok_ge] and [WeakKpt.wbyte_ok_variant_from] each take
    [(tc <= w_vrNew (wm_ws s))%nat] as a hypothesis — a bare inequality, not
    an equation.  So no exact fragment is needed at the racy sites, and the
    single persistent [ws_lb] of [WeakViewMono] serves both the owned and
    the racy layer. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop own mono_nat.
From stdpp Require Import bitvector.definitions.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import WeakMem WeakInterp WeakRacy WeakKpt.
Require Import WeakViewMono.

Section racy_lb.
  Context `{!weakViewG Σ}.

  (* ------------------------------------------------------------------ *)
  (** ** 1. The floor is never rebased.

      A floor taken at [w0] is still a valid floor at [w'] after the hart
      steps, and the client did not have to touch it.  Contrast [hart_ws],
      where the client must move every fact from [ws] to [ws'] at EVERY
      instruction — including instructions that touch no data, since the
      instruction fetch itself raises the view. *)
  Lemma ws_lb_survives_step γ w w' w0 :
    ws_le w w' ->
    ws_auth γ w -∗ ws_lb γ w0 ==∗ ws_auth γ w' ∗ ws_lb γ w0 ∗ ⌜ws_le w0 w'⌝.
  Proof.
    iIntros (Hle) "Ha #Hlb".
    iDestruct (ws_lb_valid with "Ha Hlb") as %Hle0.
    iMod (ws_update with "Ha") as "Ha"; [exact Hle|].
    iModIntro. iFrame "Ha Hlb". iPureIntro. by etrans.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 2. The exclusion, driven by the floor alone.

      [WeakKpt.wbyte_ok_ge] wants [tc <= w_vrNew (wm_ws s)].  A [ws_lb] at
      any [w0] with [tc <= w_vrNew w0] delivers it, because [ws_lb_valid]
      gives [ws_le w0 (wm_ws s)] and [ws_le] is pointwise [<=]. *)
  Lemma wbyte_ok_ge_from_lb γ (s : wmstate) (w0 : wstate) ak a t tc b :
    (1 <= tc)%nat ->
    (tc <= w_vrNew w0)%nat ->
    is_Some (log_byte (wimg s) (wm_log s) tc a) ->
    wbyte_ok s ak a t b ->
    ws_auth γ (wm_ws s) -∗ ws_lb γ w0 -∗ ⌜(tc <= t)%nat⌝.
  Proof.
    iIntros (Htc1 Htc0 Hlog Hok) "Ha Hlb".
    iDestruct (ws_lb_valid with "Ha Hlb") as %(_ & _ & _ & Hvr & _).
    iPureIntro. eapply wbyte_ok_ge; [exact Htc1| |exact Hlog|exact Hok].
    lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 3. The same, at the rule's actual oracle surface.

      [WeakRacy.wadm] is "the whole ∀-oracle surface of the rule" (its own
      comment).  This is the statement a racy client consumes: whatever the
      oracle hands back, every byte of it was written no earlier than [tc] —
      established from a floor the client snapshotted, with no exact
      knowledge of the hart's state anywhere. *)
  Lemma wadm_not_stale_from_lb γ (s : wmstate) (w0 : wstate)
      rak (ra : Arch.pa) (rn : N) (w : bv (8 * rn)) (tc j : nat) :
    (j < N.to_nat rn)%nat ->
    (1 <= tc)%nat ->
    (tc <= w_vrNew w0)%nat ->
    is_Some (log_byte (wimg s) (wm_log s) tc (acc_addr ra j)) ->
    wadm s rak ra rn w ->
    ws_auth γ (wm_ws s) -∗ ws_lb γ w0 -∗
    ⌜∃ t, (tc <= t)%nat ∧
          wbyte_ok s rak (acc_addr ra j) t (nth_byte w j)⌝.
  Proof.
    iIntros (Hj Htc1 Htc0 Hlog Hadm) "Ha Hlb".
    destruct (Hadm j Hj) as [t Hok].
    iDestruct (wbyte_ok_ge_from_lb _ _ _ _ _ _ _ _ Htc1 Htc0 Hlog Hok
                 with "Ha Hlb") as %Hge.
    iPureIntro. by exists t.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 4. THE POINT, in one statement.

      The floor is snapshotted at the OLD state, the hart then takes an
      arbitrary [ws_le] step, and the exclusion still lands at the NEW
      state.  Nothing was rebased, nothing was re-proved, and the client
      never named a [wstate] belonging to the machine.

      This is what "the view bump lives in the leaf" buys, and it is why the
      racy layer does not need an exact fragment: [ws_lb] is the only
      client-facing fact, for the owned layer and the racy layer alike. *)
  Lemma wracy_exclusion_after_step γ (s s' : wmstate) (w0 : wstate)
      rak (ra : Arch.pa) (rn : N) (w : bv (8 * rn)) (tc j : nat) :
    ws_le (wm_ws s) (wm_ws s') ->
    (j < N.to_nat rn)%nat ->
    (1 <= tc)%nat ->
    (tc <= w_vrNew w0)%nat ->
    is_Some (log_byte (wimg s') (wm_log s') tc (acc_addr ra j)) ->
    wadm s' rak ra rn w ->
    ws_auth γ (wm_ws s) -∗ ws_lb γ w0 ==∗
    ws_auth γ (wm_ws s') ∗
    ⌜∃ t, (tc <= t)%nat ∧
          wbyte_ok s' rak (acc_addr ra j) t (nth_byte w j)⌝.
  Proof.
    iIntros (Hstep Hj Htc1 Htc0 Hlog Hadm) "Ha #Hlb".
    iMod (ws_lb_survives_step with "Ha Hlb") as "(Ha & _ & _)"; [exact Hstep|].
    iDestruct (wadm_not_stale_from_lb with "Ha Hlb") as %Hfresh;
      [exact Hj|exact Htc1|exact Htc0|exact Hlog|exact Hadm|].
    by iFrame.
  Qed.

End racy_lb.
