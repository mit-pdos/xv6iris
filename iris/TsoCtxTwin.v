(* TsoCtxTwin.v -- THE LEG-C GATE: the context machinery instantiated
   against the real TSO semantics ([claude-notes/projects/tso-port.md],
   T2b).

   A self-contained Iris ghost theory over [TsoMem.v] -- no WP, no
   language, ghost updates only -- showing that the context surface's
   statement shape ([TsoCtx.v]'s SC-degenerate exports) is satisfiable by
   the single-nat-view TSO machine.  The four gate lemmas are the
   deliverable:

     [twin_load_ok]    a running context's registered byte fact predicts
                       the machine's load result at EVERY admissible view
                       advance of its hart;
     [twin_store_ok]   a store re-registers the fact at the new log top
                       under the own-author visibility arm -- the view
                       does not move;
     [twin_transport]  the lock seam: a fact changes context against
                       domination evidence (the acquirer's hart sits at
                       the log top -- exactly what the machine's AMO
                       acquire delivers);
     [twin_park] /     migration: park publishes at the log top; resume
     [twin_resume]     needs ONLY that the resuming hart's view passed
                       that timestamp -- no relation between the parking
                       and resuming harts' states.

   THE GHOST STRUCTURE.  One global map per concern (a deliberate
   simplification of per-context gnames -- a single ledger keyed by
   (context, byte) changes nothing about the gate):

     γheap   : Z ↪ (nat * bv 8)   -- a's LATEST write: timestamp + value;
     γledger : (CtxId * Z) ↪ nat  -- ξ's registration of byte a at t;
                                     NON-persistent, rides inside
                                     [ctx_pointsto], re-minted at
                                     transport (why migration needs no
                                     per-fact work above the seam);
     γrun    : agent ↪ CtxId      -- the running pairing; the fragment
                                     IS [own_context];
     γpark   : CtxId ↪ nat        -- parked contexts and their publish
                                     timestamps.

   THE SEES INVARIANT ([twin_wf]): every ledger entry (ξ, a, t) is
   covered -- ξ running on h with [visibleb h (tvs h) log t] (the t ≤ view
   arm or the own-author/forwarding arm), or ξ parked at T with t ≤ T.
   Three auxiliary clauses turned out to be load-bearing and are part of
   the design's answer:

     - RUN-INJECTIVITY (a context runs on at most one hart): without it,
       [own_context ξ h] cannot conclude that the SEES witness hart IS h,
       and the load rule dies.  (The real system gets this from
       [own_context]'s exclusivity inside one [sie_cap_gpr] per hart.)
     - PARKED-NOT-RUNNING: resume's insertion needs it for injectivity,
       and the load rule needs it to rule the parked arm out.
     - PER-BYTE LEDGER UNIQUENESS (at most one context registers a byte):
       transport's re-registration inserts at the target key and needs
       its freshness.  (Full-fraction facts only in this prototype; the
       fractional generalization must split registrations and is deferred
       -- recorded in tso-port.md.)

   Everything here imports only stdpp + Iris + [TsoMem] -- NOT the main
   tree, which may be rebuilding concurrently. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From xv6iris Require Import TsoMem.

Local Open Scope Z_scope.

(* The twin's context identity: an abstract identifier.  (The real
   surface's [CtxId] carries gnames; with the twin's global maps a bare
   identifier suffices, and [nat] keeps every gmap instance free.) *)
Notation CtxId := nat (only parsing).

(* The era image as a finite map; [TsoMem.image] is a function. *)
Definition img_fun (img : gmap Z (bv 8)) : image := λ a, img !! a.

(* ------------------------------------------------------------------ *)
(* Pure layer: "latest write", and the bridge to [tso_read]            *)
(* ------------------------------------------------------------------ *)

(* Timestamp [t] holds a's latest write, with value [v].  The upper arm
   needs no bound: [log_byte] beyond the log is [None] by lookup. *)
Definition latest (img : image) (log : list wmsg) (a : Z) (t : nat)
    (v : bv 8) : Prop :=
  log_byte img log t a = Some v ∧
  ∀ t', (t < t')%nat → log_byte img log t' a = None.

Lemma log_byte_some_le img log t a v :
  log_byte img log t a = Some v → (t ≤ length log)%nat.
Proof.
  destruct t as [|i]; first by move => _; lia.
  rewrite /log_byte. destruct (log !! i) as [m|] eqn:Hlk; last done.
  move => _. apply lookup_lt_Some in Hlk. lia.
Qed.

Lemma log_byte_app_le img log m t a :
  (t ≤ length log)%nat →
  log_byte img (log ++ [m]) t a = log_byte img log t a.
Proof.
  destruct t as [|i] => Ht //.
  have Hlk : (log ++ [m]) !! i = log !! i by apply lookup_app_l; lia.
  by rewrite /log_byte Hlk.
Qed.

Lemma log_byte_top img log m a :
  log_byte img (log ++ [m]) (S (length log)) a = msg_byte m a.
Proof.
  rewrite /log_byte /=.
  have -> : (log ++ [m]) !! length log = Some m by apply list_lookup_middle.
  done.
Qed.

Lemma log_byte_beyond img log t a :
  (length log < t)%nat → log_byte img log t a = None.
Proof.
  destruct t as [|i] => Ht; first lia.
  rewrite /log_byte /=.
  have -> : log !! i = None by apply lookup_ge_None_2; lia.
  done.
Qed.

Lemma msg_byte_singleton_eq a w h : msg_byte (WMsg a [w] h) a = Some w.
Proof.
  rewrite /msg_byte /=.
  have -> : bool_decide (a ≤ a) = true by apply bool_decide_eq_true_2; lia.
  by rewrite Z.sub_diag.
Qed.

Lemma msg_byte_singleton_ne a w h a0 :
  a0 ≠ a → msg_byte (WMsg a [w] h) a0 = None.
Proof.
  move => Hne. rewrite /msg_byte /=.
  destruct (bool_decide (a ≤ a0)) eqn:Hle; last done.
  apply bool_decide_eq_true in Hle.
  have -> : Z.to_nat (a0 - a) = S (Z.to_nat (a0 - a - 1)) by lia.
  done.
Qed.

(* Appending preserves visibility of in-range timestamps (both arms). *)
Lemma visibleb_app h tv log m t :
  (t ≤ length log)%nat → visibleb h tv log t = true →
  visibleb h tv (log ++ [m]) t = true.
Proof.
  move => Ht Hvis.
  destruct (visibleb_true _ _ _ _ Hvis) as [Hle | (i & m0 & -> & Hlk & Htid)].
  - by apply visibleb_below.
  - have Hlk' : (log ++ [m]) !! i = Some m0.
    { rewrite lookup_app_l; last by eapply lookup_lt_Some. exact Hlk. }
    by apply (visibleb_own _ _ _ _ _ Hlk' Htid).
Qed.

Lemma latest_app_new img log h a w :
  latest img (store_log log h a [w]) a (S (length log)) w.
Proof.
  rewrite /store_log. split.
  - rewrite log_byte_top msg_byte_singleton_eq //.
  - move => t' Ht'. apply log_byte_beyond. rewrite length_app /=. lia.
Qed.

Lemma latest_app_frame img log m a t v :
  msg_byte m a = None → latest img log a t v →
  latest img (log ++ [m]) a t v.
Proof.
  move => Hm [Hb Hab]. split.
  - rewrite log_byte_app_le //. by eapply log_byte_some_le.
  - move => t' Ht'.
    destruct (decide (t' ≤ length log)%nat) as [Hle|Hgt].
    + rewrite log_byte_app_le //. by apply Hab.
    + destruct (decide (t' = S (length log))) as [->|Hne].
      * rewrite log_byte_top //.
      * apply log_byte_beyond. rewrite length_app /=. lia.
Qed.

(* THE BRIDGE: a visible latest write determines the machine's read. *)
Lemma tso_read_of_latest img log h tv a t v :
  latest img log a t v → visibleb h tv log t = true →
  tso_read img log h tv a = Some v.
Proof.
  move => [Hb Hab] Hvis.
  have Hle : (t ≤ length log)%nat by eapply log_byte_some_le.
  destruct (read_down_latest img log h tv a (length log) t v Hle Hvis Hb)
    as (t'' & v'' & Ht'' & Hr & Hvis'' & Hb'').
  rewrite /tso_read Hr.
  destruct (decide (t'' = t)) as [->|Hne]; first congruence.
  exfalso.
  have HN : log_byte img log t'' a = None by apply Hab; lia.
  congruence.
Qed.

(* ------------------------------------------------------------------ *)
(* The well-formedness invariant                                       *)
(* ------------------------------------------------------------------ *)

Record twin_wf (img : image) (log : list wmsg) (tvs : agent → nat)
    (run : gmap agent CtxId) (parked : gmap CtxId nat)
    (HM : gmap Z (nat * bv 8)) (LL : gmap (CtxId * Z) nat) : Prop := TwinWf {
  twf_latest : ∀ a t v, HM !! a = Some (t, v) → latest img log a t v;
  twf_bound : ∀ ξ a t, LL !! (ξ, a) = Some t → (t ≤ length log)%nat;
  twf_sees : ∀ ξ a t, LL !! (ξ, a) = Some t →
      (∃ h, run !! h = Some ξ ∧ visibleb h (tvs h) log t = true) ∨
      (∃ T, parked !! ξ = Some T ∧ (t ≤ T)%nat);
  twf_parked_le : ∀ ξ T, parked !! ξ = Some T → (T ≤ length log)%nat;
  twf_run_inj : ∀ h1 h2 ξ, run !! h1 = Some ξ → run !! h2 = Some ξ → h1 = h2;
  twf_parked_not_run : ∀ ξ T h, parked !! ξ = Some T → run !! h ≠ Some ξ;
  twf_uniq : ∀ ξ1 ξ2 a t1 t2,
      LL !! (ξ1, a) = Some t1 → LL !! (ξ2, a) = Some t2 → ξ1 = ξ2;
}.

(* ------------------------------------------------------------------ *)
(* The resources                                                       *)
(* ------------------------------------------------------------------ *)

Class tsoTwinG Σ := TsoTwinG {
  twin_heapG :: ghost_mapG Σ Z (nat * bv 8);
  twin_ledgerG :: ghost_mapG Σ (nat * Z) nat;
  twin_natG :: ghost_mapG Σ nat nat;
}.

Section twin.
  Context {Σ : gFunctors} `{!tsoTwinG Σ}.
  Context (γheap γledger γrun γpark : gname).

  Definition own_context (ξ : CtxId) (h : agent) : iProp Σ :=
    h ↪[γrun] ξ.

  Definition ctx_parked (ξ : CtxId) (T : nat) : iProp Σ :=
    ξ ↪[γpark] T.

  Definition ctx_pointsto (ξ : CtxId) (a : Z) (v : bv 8) : iProp Σ :=
    ∃ t, a ↪[γheap] (t, v) ∗ (ξ, a) ↪[γledger] t.

  (* Ledger domination, RELATIVE TO THE CURRENT (log, tvs): the target
     context's hart has observed the whole log.  In the real system this
     is minted inside the lock's acquire proof, where the state interp is
     open and the AMO has just set the hart's view to the top; the twin
     has no step relation to carry a frozen coverage forward, so the
     honest freestanding form carries the state indices.  Note ξ (the
     source) plays no role: under TSO the single total order plus the
     ledger BOUND subsumes the release-side evidence -- domination is
     strictly simpler here than the weak-memory branch's. *)
  Definition ctx_dom (log : list wmsg) (tvs : agent → nat)
      (ξ ξ' : CtxId) : iProp Σ :=
    ∃ h', own_context ξ' h' ∗ ⌜(length log ≤ tvs h')%nat⌝.

  Lemma ctx_dom_mint log tvs ξ ξ' h' :
    (length log ≤ tvs h')%nat →
    own_context ξ' h' -∗ ctx_dom log tvs ξ ξ'.
  Proof. iIntros (?) "H". iExists h'. by iFrame. Qed.

  Definition tso_interp (img : gmap Z (bv 8)) (log : list wmsg)
      (tvs : agent → nat) (run : gmap agent CtxId)
      (parked : gmap CtxId nat) : iProp Σ :=
    ∃ (HM : gmap Z (nat * bv 8)) (LL : gmap (CtxId * Z) nat),
      ghost_map_auth γheap 1 HM ∗
      ghost_map_auth γledger 1 LL ∗
      ghost_map_auth γrun 1 run ∗
      ghost_map_auth γpark 1 parked ∗
      ⌜twin_wf (img_fun img) log tvs run parked HM LL⌝.

  (* ---------------------------------------------------------------- *)
  (* Gate lemma 1: LOAD                                                *)
  (* ---------------------------------------------------------------- *)

  Lemma twin_load_ok img log tvs run parked ξ h a v :
    tso_interp img log tvs run parked ∗ own_context ξ h ∗
    ctx_pointsto ξ a v ⊢
    ⌜∀ tv', (tvs h ≤ tv')%nat →
       tso_read (img_fun img) log h tv' a = Some v⌝.
  Proof.
    iIntros "(Hint & Hrun & Hpt)".
    iDestruct "Hint" as (HM LL) "(Hh & Hl & Hr & Hp & %Hwf)".
    rewrite /own_context /ctx_pointsto.
    iDestruct "Hpt" as (t) "[Hpt Hreg]".
    iDestruct (ghost_map_lookup with "Hh Hpt") as %HHa.
    iDestruct (ghost_map_lookup with "Hl Hreg") as %HLa.
    iDestruct (ghost_map_lookup with "Hr Hrun") as %HRh.
    iPureIntro.
    destruct Hwf as [Hlat Hbnd Hsees Hple Hinj Hpnr Huniq].
    have Hvis : visibleb h (tvs h) log t = true.
    { destruct (Hsees _ _ _ HLa) as [(h0 & Hh0 & Hv0) | (T & HpT & _)].
      - by have -> : h = h0 by apply (Hinj h h0 ξ).
      - exfalso. exact (Hpnr _ _ _ HpT HRh). }
    move => tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ t).
    - by apply (Hlat _ _ _ HHa).
    - eapply visibleb_le; last exact Hvis. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Gate lemma 2: STORE                                               *)
  (* ---------------------------------------------------------------- *)

  Lemma twin_store_ok img log tvs run parked ξ h a v w :
    tso_interp img log tvs run parked -∗ own_context ξ h -∗
    ctx_pointsto ξ a v ==∗
    tso_interp img (store_log log h a [w]) tvs run parked ∗
    own_context ξ h ∗ ctx_pointsto ξ a w.
  Proof.
    iIntros "Hint Hrun Hpt".
    iDestruct "Hint" as (HM LL) "(Hh & Hl & Hr & Hp & %Hwf)".
    rewrite /own_context /ctx_pointsto.
    iDestruct "Hpt" as (t) "[Hpt Hreg]".
    iDestruct (ghost_map_lookup with "Hh Hpt") as %HHa.
    iDestruct (ghost_map_lookup with "Hl Hreg") as %HLa.
    iDestruct (ghost_map_lookup with "Hr Hrun") as %HRh.
    iMod (ghost_map_update (S (length log), w) with "Hh Hpt")
      as "[Hh Hpt]".
    iMod (ghost_map_update (S (length log)) with "Hl Hreg")
      as "[Hl Hreg]".
    iModIntro.
    iSplitR "Hrun Hpt Hreg"; last by iFrame.
    iExists _, _. iFrame "Hh Hl Hr Hp".
    iPureIntro.
    destruct Hwf as [Hlat Hbnd Hsees Hple Hinj Hpnr Huniq].
    constructor.
    - (* latest *)
      move => a0 t0 v0.
      destruct (decide (a0 = a)) as [->|Hne].
      + rewrite lookup_insert. intros [= <- <-]. apply latest_app_new.
      + rewrite lookup_insert_ne; last congruence.
        move => HH0. rewrite /store_log.
        apply latest_app_frame; last by apply (Hlat _ _ _ HH0).
        by apply msg_byte_singleton_ne.
    - (* bound *)
      move => ξ0 a0 t0.
      destruct (decide ((ξ0, a0) = (ξ, a))) as [[= -> ->]|Hne].
      + rewrite lookup_insert. intros [= <-].
        rewrite /store_log length_app /=. lia.
      + rewrite lookup_insert_ne; last congruence.
        move => HL0. have := Hbnd _ _ _ HL0.
        rewrite /store_log length_app /=. lia.
    - (* sees *)
      move => ξ0 a0 t0.
      destruct (decide ((ξ0, a0) = (ξ, a))) as [[= -> ->]|Hne].
      + rewrite lookup_insert. intros [= <-].
        left. exists h. split; first done.
        rewrite /store_log.
        apply (visibleb_own _ _ _ (length log) (WMsg a [w] h)).
        * by apply list_lookup_middle.
        * done.
      + rewrite lookup_insert_ne; last congruence.
        move => HL0.
        destruct (Hsees _ _ _ HL0) as [(h0 & Hh0 & Hv0) | (T & HT & Hle)].
        * left. exists h0. split; first done.
          rewrite /store_log. apply visibleb_app; last done.
          by apply (Hbnd _ _ _ HL0).
        * right. by exists T.
    - (* parked_le *)
      move => ξ0 T HT. have := Hple _ _ HT.
      rewrite /store_log length_app /=. lia.
    - exact Hinj.
    - exact Hpnr.
    - (* uniq *)
      move => ξ1 ξ2 a0 t1 t2.
      destruct (decide ((ξ1, a0) = (ξ, a))) as [[= -> ->]|Hne1].
      + destruct (decide ((ξ2, a) = (ξ, a))) as [[= ->]|Hne2].
        * move => _ _. done.
        * rewrite lookup_insert. rewrite lookup_insert_ne; last congruence.
          move => _ HL2. symmetry. exact (Huniq _ _ _ _ _ HL2 HLa).
      + destruct (decide ((ξ2, a0) = (ξ, a))) as [[= -> ->]|Hne2].
        * rewrite lookup_insert_ne; last congruence. rewrite lookup_insert.
          move => HL1 _. exact (Huniq _ _ _ _ _ HL1 HLa).
        * rewrite !lookup_insert_ne; [|congruence..].
          move => HL1 HL2. exact (Huniq _ _ _ _ _ HL1 HL2).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Gate lemma 3: TRANSPORT (the lock seam)                           *)
  (* ---------------------------------------------------------------- *)

  Lemma twin_transport img log tvs run parked ξ ξ' a v :
    tso_interp img log tvs run parked -∗ ctx_dom log tvs ξ ξ' -∗
    ctx_pointsto ξ a v ==∗
    tso_interp img log tvs run parked ∗ ctx_dom log tvs ξ ξ' ∗
    ctx_pointsto ξ' a v.
  Proof.
    iIntros "Hint Hdom Hpt".
    destruct (decide (ξ = ξ')) as [->|Hne].
    { iModIntro. iFrame. }
    iDestruct "Hdom" as (h') "[Hrun' %Htop]".
    iDestruct "Hint" as (HM LL) "(Hh & Hl & Hr & Hp & %Hwf)".
    rewrite /own_context /ctx_pointsto.
    iDestruct "Hpt" as (t) "[Hpt Hreg]".
    iDestruct (ghost_map_lookup with "Hh Hpt") as %HHa.
    iDestruct (ghost_map_lookup with "Hl Hreg") as %HLa.
    iDestruct (ghost_map_lookup with "Hr Hrun'") as %HRh'.
    destruct Hwf as [Hlat Hbnd Hsees Hple Hinj Hpnr Huniq].
    iMod (ghost_map_delete with "Hl Hreg") as "Hl".
    have Hfresh : delete (ξ, a) LL !! (ξ', a) = None.
    { destruct (delete (ξ, a) LL !! (ξ', a)) eqn:Hd; last done.
      exfalso. move: Hd.
      rewrite lookup_delete_ne; last congruence.
      move => Hd. exact (Hne (Huniq _ _ _ _ _ HLa Hd)). }
    iMod (ghost_map_insert (ξ', a) t Hfresh with "Hl") as "[Hl Hreg]".
    iModIntro.
    iSplitR "Hrun' Hpt Hreg"; last first.
    { iSplitL "Hrun'"; first by (iExists h'; iFrame).
      iExists t. iFrame. }
    iExists _, _. iFrame "Hh Hl Hr Hp".
    iPureIntro.
    have Hbt : (t ≤ length log)%nat by apply (Hbnd _ _ _ HLa).
    constructor.
    - exact Hlat.
    - (* bound *)
      move => ξ0 a0 t0.
      destruct (decide ((ξ0, a0) = (ξ', a))) as [[= -> ->]|Hne0].
      + rewrite lookup_insert. intros [= <-]. exact Hbt.
      + rewrite lookup_insert_ne; last congruence.
        rewrite lookup_delete_Some. move => [_ HL0].
        exact (Hbnd _ _ _ HL0).
    - (* sees *)
      move => ξ0 a0 t0.
      destruct (decide ((ξ0, a0) = (ξ', a))) as [[= -> ->]|Hne0].
      + rewrite lookup_insert. intros [= <-].
        left. exists h'. split; first done.
        apply visibleb_below. lia.
      + rewrite lookup_insert_ne; last congruence.
        rewrite lookup_delete_Some. move => [_ HL0].
        exact (Hsees _ _ _ HL0).
    - exact Hple.
    - exact Hinj.
    - exact Hpnr.
    - (* uniq *)
      move => ξ1 ξ2 a0 t1 t2.
      destruct (decide ((ξ1, a0) = (ξ', a))) as [[= -> ->]|Hne1].
      + destruct (decide ((ξ2, a) = (ξ', a))) as [[= ->]|Hne2].
        * move => _ _. done.
        * rewrite lookup_insert. rewrite lookup_insert_ne; last congruence.
          rewrite lookup_delete_Some.
          move => _ [Hne2' HL2]. exfalso.
          have : ξ2 = ξ by exact (Huniq _ _ _ _ _ HL2 HLa).
          congruence.
      + destruct (decide ((ξ2, a0) = (ξ', a))) as [[= -> ->]|Hne2].
        * rewrite lookup_insert_ne; last congruence. rewrite lookup_insert.
          rewrite lookup_delete_Some.
          move => [Hne1' HL1] _. exfalso.
          have : ξ1 = ξ by exact (Huniq _ _ _ _ _ HL1 HLa).
          congruence.
        * rewrite !lookup_insert_ne; [|congruence..].
          rewrite !lookup_delete_Some.
          move => [_ HL1] [_ HL2]. exact (Huniq _ _ _ _ _ HL1 HL2).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Gate lemma 4: PARK / RESUME                                       *)
  (* ---------------------------------------------------------------- *)

  Lemma twin_park img log tvs run parked ξ h :
    tso_interp img log tvs run parked -∗ own_context ξ h ==∗
    tso_interp img log tvs (delete h run) (<[ξ := length log]> parked) ∗
    ctx_parked ξ (length log).
  Proof.
    iIntros "Hint Hrun".
    iDestruct "Hint" as (HM LL) "(Hh & Hl & Hr & Hp & %Hwf)".
    rewrite /own_context /ctx_parked.
    iDestruct (ghost_map_lookup with "Hr Hrun") as %HRh.
    destruct Hwf as [Hlat Hbnd Hsees Hple Hinj Hpnr Huniq].
    have Hpfresh : parked !! ξ = None.
    { destruct (parked !! ξ) eqn:Hpk; last done.
      exfalso. exact (Hpnr _ _ _ Hpk HRh). }
    iMod (ghost_map_delete with "Hr Hrun") as "Hr".
    iMod (ghost_map_insert ξ (length log) Hpfresh with "Hp")
      as "[Hp Hparked]".
    iModIntro. iFrame "Hparked".
    iExists _, _. iFrame "Hh Hl Hr Hp".
    iPureIntro. constructor.
    - exact Hlat.
    - exact Hbnd.
    - (* sees *)
      move => ξ0 a0 t0 HL0.
      destruct (decide (ξ0 = ξ)) as [->|Hne].
      + right. exists (length log).
        rewrite lookup_insert. split; first done.
        exact (Hbnd _ _ _ HL0).
      + destruct (Hsees _ _ _ HL0) as [(h0 & Hh0 & Hv0) | (T & HT & Hle)].
        * left. exists h0. split; last done.
          rewrite lookup_delete_ne; first done.
          move => Heq. subst h0. congruence.
        * right. exists T.
          rewrite lookup_insert_ne; last congruence.
          by split.
    - (* parked_le *)
      move => ξ0 T.
      destruct (decide (ξ0 = ξ)) as [->|Hne].
      + rewrite lookup_insert. intros [= <-]. lia.
      + rewrite lookup_insert_ne; last congruence. exact (Hple ξ0 T).
    - (* run_inj *)
      move => h1 h2 ξ0.
      rewrite !lookup_delete_Some. move => [_ H1] [_ H2].
      exact (Hinj _ _ _ H1 H2).
    - (* parked_not_run *)
      move => ξ0 T h0.
      destruct (decide (ξ0 = ξ)) as [->|Hne].
      + move => _. rewrite lookup_delete_Some. move => [Hne0 HR0].
        have : h0 = h by exact (Hinj _ _ _ HR0 HRh).
        congruence.
      + rewrite lookup_insert_ne //. move => HT.
        rewrite lookup_delete_Some. move => [_ HR0].
        exact (Hpnr _ _ _ HT HR0).
    - exact Huniq.
  Qed.

  Lemma twin_resume img log tvs run parked ξ T h' :
    run !! h' = None → (T ≤ tvs h')%nat →
    tso_interp img log tvs run parked -∗ ctx_parked ξ T ==∗
    tso_interp img log tvs (<[h' := ξ]> run) (delete ξ parked) ∗
    own_context ξ h'.
  Proof.
    iIntros (Hfresh Hcov) "Hint Hparked".
    iDestruct "Hint" as (HM LL) "(Hh & Hl & Hr & Hp & %Hwf)".
    rewrite /own_context /ctx_parked.
    iDestruct (ghost_map_lookup with "Hp Hparked") as %HpT.
    destruct Hwf as [Hlat Hbnd Hsees Hple Hinj Hpnr Huniq].
    iMod (ghost_map_delete with "Hp Hparked") as "Hp".
    iMod (ghost_map_insert h' ξ Hfresh with "Hr") as "[Hr Hrun]".
    iModIntro. iFrame "Hrun".
    iExists _, _. iFrame "Hh Hl Hr Hp".
    iPureIntro. constructor.
    - exact Hlat.
    - exact Hbnd.
    - (* sees *)
      move => ξ0 a0 t0 HL0.
      destruct (decide (ξ0 = ξ)) as [->|Hne].
      + left. exists h'. rewrite lookup_insert. split; first done.
        destruct (Hsees _ _ _ HL0) as [(h0 & Hh0 & _) | (T0 & HT0 & Hle)].
        * exfalso. exact (Hpnr _ _ _ HpT Hh0).
        * apply visibleb_below.
          have HTT : T0 = T by congruence. lia.
      + destruct (Hsees _ _ _ HL0) as [(h0 & Hh0 & Hv0) | (T0 & HT0 & Hle)].
        * left. exists h0. split; last done.
          rewrite lookup_insert_ne; last congruence. exact Hh0.
        * right. exists T0.
          rewrite lookup_delete_ne; last congruence. by split.
    - (* parked_le *)
      move => ξ0 T0. rewrite lookup_delete_Some. move => [_ HT0].
      exact (Hple _ _ HT0).
    - (* run_inj *)
      move => h1 h2 ξ0.
      destruct (decide (h1 = h')) as [->|Hne1];
        destruct (decide (h2 = h')) as [->|Hne2].
      + done.
      + rewrite lookup_insert.
        rewrite lookup_insert_ne; last congruence.
        intros [= <-] HR2. exfalso. exact (Hpnr _ _ _ HpT HR2).
      + rewrite lookup_insert.
        rewrite lookup_insert_ne; last congruence.
        move => HR1. intros [= <-]. exfalso. exact (Hpnr _ _ _ HpT HR1).
      + rewrite !lookup_insert_ne; [|congruence..].
        exact (Hinj h1 h2 ξ0).
    - (* parked_not_run *)
      move => ξ0 T0 h0. rewrite lookup_delete_Some. move => [Hne0 HT0].
      destruct (decide (h0 = h')) as [->|Hneh].
      + rewrite lookup_insert. congruence.
      + rewrite lookup_insert_ne; last congruence.
        exact (Hpnr _ _ _ HT0).
    - exact Huniq.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Structural exports' twin images                                   *)
  (* ---------------------------------------------------------------- *)

  (* Full-fraction facts about one byte exclude each other (the twin
     carries no dq axis; the SC surface's cross-context AGREE is the
     fractional refinement, deferred). *)
  Lemma twin_pointsto_excl ξ1 ξ2 a v1 v2 :
    ctx_pointsto ξ1 a v1 -∗ ctx_pointsto ξ2 a v2 -∗ False.
  Proof.
    rewrite /ctx_pointsto.
    iIntros "[%t1 [H1 _]] [%t2 [H2 _]]".
    iDestruct (ghost_map_elem_ne with "H1 H2") as %Hne.
    done.
  Qed.

  (* CtxMorph-style composition over the transport: a lock-payload shape
     (two facts and a pure conjunct under an ∃) crosses in one pass. *)
  Lemma twin_transport_payload img log tvs run parked ξ ξ' a1 a2 v1
      (P : Prop) :
    tso_interp img log tvs run parked -∗ ctx_dom log tvs ξ ξ' -∗
    (ctx_pointsto ξ a1 v1 ∗ ∃ v2 : bv 8, ⌜P⌝ ∗ ctx_pointsto ξ a2 v2) ==∗
    tso_interp img log tvs run parked ∗ ctx_dom log tvs ξ ξ' ∗
    (ctx_pointsto ξ' a1 v1 ∗ ∃ v2 : bv 8, ⌜P⌝ ∗ ctx_pointsto ξ' a2 v2).
  Proof.
    iIntros "Hint Hdom [Hp1 (%v2 & %HP & Hp2)]".
    iMod (twin_transport with "Hint Hdom Hp1") as "(Hint & Hdom & Hp1)".
    iMod (twin_transport with "Hint Hdom Hp2") as "(Hint & Hdom & Hp2)".
    iModIntro.
    iSplitL "Hint"; first iExact "Hint".
    iSplitL "Hdom"; first iExact "Hdom".
    iSplitL "Hp1"; first iExact "Hp1".
    iExists v2. iSplitR; first done. iExact "Hp2".
  Qed.

End twin.

(* Satisfiability: the interp is inhabited at the empty era. *)
Lemma twin_init `{!tsoTwinG Σ} (img : gmap Z (bv 8)) (tvs : agent → nat) :
  ⊢ |==> ∃ γheap γledger γrun γpark,
      tso_interp γheap γledger γrun γpark img [] tvs ∅ ∅.
Proof.
  iMod (ghost_map_alloc (∅ : gmap Z (nat * bv 8))) as (γheap) "[Hh _]".
  iMod (ghost_map_alloc (∅ : gmap (CtxId * Z) nat)) as (γledger) "[Hl _]".
  iMod (ghost_map_alloc (∅ : gmap agent CtxId)) as (γrun) "[Hr _]".
  iMod (ghost_map_alloc (∅ : gmap CtxId nat)) as (γpark) "[Hp _]".
  iModIntro. iExists γheap, γledger, γrun, γpark.
  rewrite /tso_interp. iExists ∅, ∅. iFrame.
  iPureIntro. constructor; intros *; rewrite lookup_empty; done.
Qed.
