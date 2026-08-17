(** * WeakRobustSim.v — THE SIMULATION (M6 W2b): replaying a traced
      full-machine behavior as a PROMISE-FREE run along a topological
      order of the extended dependency graph [gdep2 = gdep ∪ gE]

    THE CONSTRUCTION.  [WeakRobustOrd.toposort_ind_S] hands the events of
    a downward-closed subset [S] one at a time, in an order in which every
    [gdep2]-predecessor of the next event is already processed.  After
    processing [done] we have built:

    - the TIMESTAMP MAP π = [pi done]: the behavior's fulfilled timestamps
      that occur in [done], in PROCESSING order, mapped to the
      promise-free log positions [1 .. |fl done|]; everything else is sent
      injectively above that range, and 0 is fixed.  [sigma_ok (pi done)]
      is what [WeakRobustProv]'s transport theorems consume.
    - the PROMISE-FREE LOG [pf_log done]: the behavior's messages, in the
      same processing order — literally [msg_at <$> fl done], so the
      log/timestamp correspondence is a [list_lookup_fmap] away.
    - a pf configuration [cf] reached from [wp_init img d0 ps] whose agent
      [j] sits at trace position [nproc done j] with [wstate]
      [aevs_post (pi done) (take (nproc done j) evs) ws_init] — the
      π-transported fold of [WeakRobustProv].

    THE FOUR CRUXES, and what each spends:

    (1) VALUES.  A read of [t] in the behavior reads [pf_log]'s position
        [pi done t - 1], which holds the SAME message; [t = 0] reads the
        image on both sides.
    (2) READABLE.  A byte-[a] write at pf position [q' ∈ (π t, pf-floor]]
        is [π t̂] for a PROCESSED [t̂]; four cases, all refuted:
        [t̂ = t] (π injective), [t̂ < t] (co-serialization [Hco] + the
        processing order), [t < t̂ ≤ F] (the BEHAVIOR's own [readable]),
        [t̂ > F] (the [gE] edges: every floor leaf's fulfil is processed
        strictly before [t̂]'s, so [π t̂] is above the whole transported
        floor).
    (3) EXCL_OK (rmw).  Same shape, with the behavior's [excl_ok] in the
        middle band, the rmw's own event for [t̂ = ts], and — for
        [t̂ > ts] — the observation that [Hco] would put the current
        (unprocessed) event inside [done].
    (4) FINAL MEMORY.  Every log message is fulfilled ([Hwfl]), so
        [fl full] enumerates every timestamp and [pf_log full] is a
        reordering of [pt_log TS]; per-byte [Hco]-monotonicity of π sends
        the behavior's latest byte-[a] write to the pf log's latest.

    THE FABRIC (G4).  The section also carries the behavior's GLOBAL
    DEVICE-ORDER WITNESS [DS] ([Hwit : ptraces_wit TS DS], [Hd0]), and the
    invariant a fifth clause: [qcfg]'s [qfab done (pc_dev cf)] says the
    replayed configuration's fabric is [dev_at]'s FOLD over the processed
    witness prefix, and [qdev done n] says the processed events include
    exactly the first [n] witness entries.  That prefix property is what
    the [gdev] edges buy: the order [Qinv_step] runs along is a
    topological order of [gdep3 = gdep2 ∪ gdev], so an event's gdev
    predecessor is already processed.  [qfab_step] is then the whole of
    G4's device arm — a fabric-touching event is at witness position
    [n] exactly ([qdev_index], the device analogue of [nproc_cur]), so
    (W4) makes the replay's fabric LITERALLY the [din] it recorded and
    the recorded step applies verbatim; a dev-free event runs at EVERY
    fabric and leaves it (and the fold) alone.

    THE PREMISES (the section context) are all bundle-level: [ptraces_wf],
    [ptraces_ws_init], [gdep2_acyclic] (from [WeakRobustAcyc2]), [co_tc]
    (from [WeakRobustSer]), [writes_fulfilled], [lat_free_prog], and the
    two SHAPE premises the wrapper discharges from the promise phase
    (every log message is nonempty; the traces start at [ps]).  Plus
    [ts_oblivious] — worklist finding (v): the pf witness steps the
    program with π-RETIMED labels, so [pstep] must not branch on a
    timestamp.  DISCIPLINE PREMISES ARE NOT USED (worklist finding (vi)):
    they are consumed by the acyclicity theorem alone.

    [WeakAxiomatic] is imported FIRST so that [WeakPromise]'s [wlabel]
    constructors shadow its [lbl] ones, exactly as [WeakRobustOrd] does. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge
                            WeakRobustTrace WeakRobustGraph WeakRobust
                            WeakRobustProv WeakRobustAcyc WeakRobustLin
                            WeakRobustOrd WeakRobustSer.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** LAYER 0: two generic list facts, and one [WeakMem] convenience *)

Lemma NoDup_omap_inj {A B} (f : A → option B) (l : list A) :
  NoDup l →
  (∀ x y b, x ∈ l → y ∈ l → f x = Some b → f y = Some b → x = y) →
  NoDup (omap f l).
Proof.
  induction l as [|x l IH]; intros Hnd Hinj; [by constructor|].
  apply list_relations.NoDup_cons in Hnd as [Hx Hnd].
  have Hinj' : ∀ y z b, y ∈ l → z ∈ l → f y = Some b → f z = Some b → y = z.
  { intros y z b ????. eapply Hinj; [by apply elem_of_list_further..|done|done]. }
  rewrite /=. destruct (f x) as [b|] eqn:Hfx; [|by apply IH].
  constructor; [|by apply IH].
  intros Hb. rewrite elem_of_list_omap in Hb. destruct Hb as (y & Hy & Hfy).
  have Hyx : y = x by eapply Hinj; [by apply elem_of_list_further|
                                    apply elem_of_list_here|done|done].
  subst y. by apply Hx.
Qed.

Lemma log_byte_pos (img : image) (log : list wmsg) q m a :
  (0 < q)%nat → log !! (q - 1)%nat = Some m →
  log_byte img log q a = msg_byte m a.
Proof.
  intros Hq Hm. destruct q as [|p]; [lia|].
  rewrite log_byte_S. replace (S p - 1)%nat with p in Hm by lia.
  by rewrite Hm.
Qed.

(** [latest_ts] is 0 exactly when nothing in the log writes the byte. *)
Lemma latest_ts_zero_iff (log : list wmsg) a :
  latest_ts log a = 0%nat ↔ ¬ writes_in log a 0%nat (length log).
Proof.
  split.
  - intros Hz Hw. apply (latest_ts_top log a). by rewrite Hz.
  - intros Hn. destruct (latest_ts_writes log a) as [Hz|(i & m & Hr & Hlk & Hs)];
      [done|].
    destruct Hn. exists (S i). split_and!; [lia| |].
    + rewrite -Hr. apply latest_ts_le.
    + exists m. replace (S i - 1)%nat with i by lia. by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** LAYER 1: the timestamp map π, on an abstract position list *)

(** [piL L t]: 0 is fixed; a member of [L] goes to (its first index) + 1;
    a non-member goes injectively ABOVE [|L|].  The two ranges are
    disjoint, which is the whole of [piL_inj]. *)
Definition piL (L : list nat) (t : nat) : nat :=
  if bool_decide (t = 0%nat) then 0%nat
  else match list_find (λ t', t' = t) L with
       | Some (i, _) => S i
       | None => (S (length L) + t)%nat
       end.

Lemma piL_0 L : piL L 0%nat = 0%nat.
Proof. rewrite /piL bool_decide_eq_true_2 //. Qed.

Lemma piL_spec L t :
  t ≠ 0%nat →
  (∃ i, L !! i = Some t ∧ (i < length L)%nat ∧ piL L t = S i) ∨
  (t ∉ L ∧ piL L t = (S (length L) + t)%nat).
Proof.
  intros Ht. rewrite /piL bool_decide_eq_false_2 //.
  destruct (list_find (λ t', t' = t) L) as [[i x]|] eqn:Hf.
  - left. apply list_find_Some in Hf as (Hi & -> & _).
    exists i. split_and!; [done|by eapply lookup_lt_Some|done].
  - right. split; [|done]. intros Hin.
    destruct (list_find_elem_of (λ t', t' = t) L t Hin eq_refl) as [y Hy].
    by rewrite Hf in Hy.
Qed.

Lemma piL_pos L t : t ≠ 0%nat → (0 < piL L t)%nat.
Proof. intros Ht. destruct (piL_spec L t Ht) as [(i & _ & _ & ->)|[_ ->]]; lia. Qed.

Lemma piL_eq_zero L t : piL L t = 0%nat → t = 0%nat.
Proof.
  intros H. destruct (decide (t = 0%nat)) as [->|Ht]; [done|].
  have := piL_pos L t Ht. lia.
Qed.

Global Instance piL_inj L : Inj eq eq (piL L).
Proof.
  intros t1 t2 Heq.
  destruct (decide (t1 = 0%nat)) as [->|H1].
  { symmetry. apply (piL_eq_zero L). by rewrite -Heq piL_0. }
  destruct (decide (t2 = 0%nat)) as [->|H2].
  { apply (piL_eq_zero L). by rewrite Heq piL_0. }
  destruct (piL_spec L t1 H1) as [(i1 & Hi1 & Hlt1 & Hp1)|[Hn1 Hp1]],
           (piL_spec L t2 H2) as [(i2 & Hi2 & Hlt2 & Hp2)|[Hn2 Hp2]];
    rewrite Hp1 Hp2 in Heq.
  - assert (i1 = i2) as -> by lia. rewrite Hi1 in Hi2. by simplify_eq.
  - lia.
  - lia.
  - lia.
Qed.

Lemma piL_sigma_ok L : sigma_ok (piL L).
Proof. split; [apply piL_0|apply _]. Qed.

(** MEMBERSHIP, at a KNOWN index — needs [NoDup] to identify the index
    [list_find] returns with the one at hand. *)
Lemma piL_mem L i t : NoDup L → L !! i = Some t → t ≠ 0%nat → piL L t = S i.
Proof.
  intros Hnd Hi Ht. rewrite /piL bool_decide_eq_false_2 //.
  destruct (list_find (λ t', t' = t) L) as [[i' x]|] eqn:Hf.
  - apply list_find_Some in Hf as (Hi' & -> & _).
    by rewrite (list_relations.NoDup_lookup L i' i t Hnd Hi' Hi).
  - exfalso. destruct (list_find_elem_of (λ t', t' = t) L t) as [y Hy];
      [by eapply elem_of_list_lookup_2|done|]. by rewrite Hf in Hy.
Qed.

Lemma piL_mem_le L t : t ∈ L → (piL L t ≤ length L)%nat.
Proof.
  intros Hin.
  destruct (decide (t = 0%nat)) as [->|Ht]; [rewrite piL_0; lia|].
  destruct (piL_spec L t Ht) as [(i & _ & Hlt & ->)|[Hn _]]; [lia|done].
Qed.

(** STABILITY under append: [list_find] over a prefix is unchanged. *)
Lemma piL_app L L' t : t ∈ L ∨ t = 0%nat → piL (L ++ L') t = piL L t.
Proof.
  intros Hin. destruct (decide (t = 0%nat)) as [->|Ht]; [by rewrite !piL_0|].
  have Hmem : t ∈ L by destruct Hin.
  rewrite /piL bool_decide_eq_false_2 //.
  destruct (list_find (λ t', t' = t) L) as [[i x]|] eqn:Hf.
  - by rewrite (list_find_app_l _ L L' i x Hf).
  - exfalso. destruct (list_find_elem_of (λ t', t' = t) L t Hmem eq_refl) as [y Hy].
    by rewrite Hf in Hy.
Qed.

(* ------------------------------------------------------------------ *)
(** ** LAYER 2: the bookkeeping over a processed prefix *)

Section book.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).
  Context (TS : ptraces P D).

  Implicit Types done : list gev.
  Implicit Types e : gev.

  (** The processed timestamps, in processing order. *)
  Definition fl done : list nat := omap (gev_ts TS) done.

  Definition pi done : nat → nat := piL (fl done).

  (** The message a timestamp names (junk off the log — never consumed). *)
  Definition msg_at (t : nat) : wmsg :=
    default (WMsg 0 [] None WCplain) (pt_log TS !! (t - 1)%nat).

  (** THE PROMISE-FREE LOG.  Definitionally a [fmap] of [fl], so
      [pf_log done !! i] and [fl done !! i] move together. *)
  Definition pf_log done : list wmsg := msg_at <$> fl done.

  (** The position [fl] reaches after [n] processed events. *)
  Definition fpos done (n : nat) : nat := length (fl (take n done)).

  (* ---------------------------------------------------------------- *)
  (** *** [fl] *)

  Lemma fl_app done l : fl (done ++ l) = fl done ++ fl l.
  Proof. by rewrite /fl omap_app. Qed.

  Lemma fl_app_none done e : gev_ts TS e = None → fl (done ++ [e]) = fl done.
  Proof. intros He. rewrite fl_app /fl /= He /=. by rewrite app_nil_r. Qed.

  Lemma fl_app_some done e t :
    gev_ts TS e = Some t → fl (done ++ [e]) = fl done ++ [t].
  Proof. intros He. by rewrite fl_app /fl /= He /=. Qed.

  Lemma elem_of_fl done t : t ∈ fl done ↔ ∃ e, e ∈ done ∧ gev_ts TS e = Some t.
  Proof. rewrite /fl elem_of_list_omap. done. Qed.

  Lemma fl_len done : length (pf_log done) = length (fl done).
  Proof. by rewrite /pf_log length_fmap. Qed.

  (** [pi] is stable on already-processed timestamps. *)
  Lemma pi_app done l t :
    t ∈ fl done ∨ t = 0%nat → pi (done ++ l) t = pi done t.
  Proof. intros Ht. rewrite /pi fl_app. by apply piL_app. Qed.

  Lemma pi_0 done : pi done 0%nat = 0%nat.
  Proof. apply piL_0. Qed.

  Lemma pi_sigma_ok done : sigma_ok (pi done).
  Proof. apply piL_sigma_ok. Qed.

  Lemma pi_pos done t : t ≠ 0%nat → (0 < pi done t)%nat.
  Proof. apply piL_pos. Qed.

  (* ---------------------------------------------------------------- *)
  (** *** [fpos]: the position an event's timestamp takes in [fl] *)

  Lemma fl_take_app done n n' :
    (n ≤ n')%nat → ∃ L, fl (take n' done) = fl (take n done) ++ L.
  Proof.
    intros Hle. exists (fl (take (n' - n)%nat (drop n done))).
    rewrite -fl_app take_take_drop. by replace (n + (n' - n))%nat with n' by lia.
  Qed.

  Lemma fpos_mono done n n' : (n ≤ n')%nat → (fpos done n ≤ fpos done n')%nat.
  Proof.
    intros Hle. destruct (fl_take_app done n n' Hle) as (L & HL).
    rewrite /fpos HL length_app. lia.
  Qed.

  Lemma fpos_succ done n e t :
    done !! n = Some e → gev_ts TS e = Some t →
    fpos done (S n) = S (fpos done n).
  Proof.
    intros Hn Ht. rewrite /fpos (take_S_r _ _ _ Hn) (fl_app_some _ e t Ht)
                          length_app /=. lia.
  Qed.

  Lemma fl_lookup_fpos done n e t :
    done !! n = Some e → gev_ts TS e = Some t →
    fl done !! fpos done n = Some t.
  Proof.
    intros Hn Ht.
    have Hsplit : done = take n done ++ drop n done by rewrite take_drop.
    rewrite {2}Hsplit fl_app (drop_S _ _ _ Hn) /fl /= Ht /=.
    rewrite lookup_app_r; [done|]. by rewrite Nat.sub_diag.
  Qed.

  Lemma fpos_lt done n n' e t :
    done !! n = Some e → gev_ts TS e = Some t → (n < n')%nat →
    (fpos done n < fpos done n')%nat.
  Proof.
    intros Hn Ht Hlt.
    have H1 : fpos done (S n) = S (fpos done n) by eapply fpos_succ.
    have H2 : (fpos done (S n) ≤ fpos done n')%nat by apply fpos_mono; lia.
    lia.
  Qed.

End book.

(* ------------------------------------------------------------------ *)
(** ** [nproc]: how many of agent [j]'s events are processed *)

Definition nproc (done : list gev) (j : nat) : nat :=
  length (filter (λ e : gev, e.1 = j) done).

Lemma nproc_app_eq done e : nproc (done ++ [e]) e.1 = S (nproc done e.1).
Proof.
  rewrite /nproc list_basics.filter_app length_app list_basics.filter_cons list_basics.filter_nil.
  rewrite decide_True; [done|]. rewrite /=. lia.
Qed.

Lemma nproc_app_ne done e j : j ≠ e.1 → nproc (done ++ [e]) j = nproc done j.
Proof.
  intros Hne. rewrite /nproc list_basics.filter_app length_app list_basics.filter_cons list_basics.filter_nil.
  rewrite decide_False; [naive_solver|]. rewrite /=. lia.
Qed.

Lemma nproc_nil j : nproc [] j = 0%nat.
Proof. done. Qed.

(* ------------------------------------------------------------------ *)
(** ** LAYER 2b: EXTENSIONALITY of the σ-transported fold

    Two transports agreeing on every timestamp the events touch produce
    the same fold — this is what keeps the already-built [wstate]s stable
    as [done] grows and π is extended. *)

Lemma tlabel_ts_snd σ tvs : (tlabel_ts σ tvs).*2 = tvs.*2.
Proof. rewrite /tlabel_ts -list_fmap_compose //. Qed.

Lemma tlabel_ts_length σ tvs : length (tlabel_ts σ tvs) = length tvs.
Proof. by rewrite /tlabel_ts length_fmap. Qed.

Lemma tlabel_ts_lookup σ tvs j t v :
  tvs !! j = Some (t, v) → tlabel_ts σ tvs !! j = Some (σ t, v).
Proof. intros Hj. by rewrite /tlabel_ts list_lookup_fmap Hj /=. Qed.

Lemma tlabel_ts_lookup_inv σ tvs j t' v :
  tlabel_ts σ tvs !! j = Some (t', v) →
  ∃ t, tvs !! j = Some (t, v) ∧ t' = σ t.
Proof.
  rewrite /tlabel_ts list_lookup_fmap.
  destruct (tvs !! j) as [[t v']|] eqn:Hj; [|done].
  intros [= <- <-]. by exists t.
Qed.

Lemma aev_post_ext {D : Type} σ σ' (ev : aev D) w :
  (∀ t, aev_ts_occurs ev t → σ t = σ' t) →
  aev_post σ ev w = aev_post σ' ev w.
Proof.
  intros Hag. destruct ev as [lb ts dd].
  rewrite /aev_post /aev_ts_occurs /= in Hag |- *.
  have Hread : ∀ base tvs, lb_reads lb = tvs_reads base tvs →
                 σ <$> tvs.*1 = σ' <$> tvs.*1.
  { intros base tvs Hlb. apply list_fmap_ext. intros i u Hu.
    apply Hag. left. destruct (tvs_fst_reads base tvs i u Hu) as (a & Ha).
    exists a. by rewrite Hlb. }
  destruct lb as [|aq lat base tvs|rl base data|aq rl base tvs data|pr pw sr sw|].
  - done.
  - by rewrite (Hread base tvs eq_refl).
  - destruct ts as [t|]; [|done]. by rewrite (Hag t (or_intror eq_refl)).
  - destruct ts as [t|]; [|done].
    by rewrite (Hread base tvs eq_refl) (Hag t (or_intror eq_refl)).
  - done.
  - done.
Qed.

Lemma aevs_post_ext {D : Type} σ σ' (evs : list (aev D)) w :
  (∀ t, ev_ts_occurs evs t → σ t = σ' t) →
  aevs_post σ evs w = aevs_post σ' evs w.
Proof.
  revert w. induction evs as [|ev evs IH]; intros w Hag; [done|].
  rewrite /aevs_post /= -/(aevs_post σ evs) -/(aevs_post σ' evs).
  have Heq : aev_post σ ev w = aev_post σ' ev w.
  { apply aev_post_ext. intros t Ht. apply Hag. by apply ev_ts_occurs_cons; left. }
  rewrite Heq. apply IH.
  intros t Ht. apply Hag. by apply ev_ts_occurs_cons; right.
Qed.

(** Every element of a read floor is a LEAF of the state it is computed
    from — the well-definedness the [gE] edges are consumed through. *)
Lemma lfloor_leaf S aq a t : t ∈ lfloor S aq a → lstate_leaf S t.
Proof.
  rewrite /lfloor. intros Ht. apply elem_of_app in Ht as [Ht|Ht].
  - by eapply lload_vpre_leaf.
  - by eapply lcoh_leaf.
Qed.

(* ------------------------------------------------------------------ *)
(** ** LAYER 3: the simulation invariant

    TIMESTAMP OBLIVIOUSNESS (worklist finding (v)): the pf witness steps
    the program with π-RETIMED labels, so [robust] is only provable for
    programs that do not branch on a timestamp.  The Sail instantiation
    satisfies this trivially — a program sees VALUES, never timestamps. *)

Definition ts_oblivious {P D : Type}
    (pstep : P → D → wlabel → P → D → Prop) : Prop :=
  (∀ p d aq lat base tvs tvs' p' d', tvs.*2 = tvs'.*2 →
     pstep p d (LLoad aq lat base tvs) p' d' →
     pstep p d (LLoad aq lat base tvs') p' d') ∧
  (∀ p d aq rl base tvs tvs' data p' d', tvs.*2 = tvs'.*2 →
     pstep p d (LRmw aq rl base tvs data) p' d' →
     pstep p d (LRmw aq rl base tvs' data) p' d').

Section sim.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pcls : P → wlabel → wstate → wm_class).
  Context (pdev : P → wlabel → P → bool).
  Context (TS : ptraces P D) (DS : pdevs D) (img : image) (d0 : D) (ps : list P).
  Context (Hwf : ptraces_wf pstep TS).
  Context (Hwsi : ptraces_ws_init TS).
  Context (Hco : ∀ a, co_tc TS a).
  Context (Hwfl : writes_fulfilled TS).
  Context (Hlf : lat_free_prog pstep).
  Context (Hobl : ts_oblivious pstep).
  (** THE CLASS HALVES OF G6a.  [wp_pf_step] PINS the class of the message
      a store/rmw appends to [pcls p l ws] at the fulfilling agent's own
      [wstate], so the replay owes that equation at every store it
      rebuilds.  [Hcls] supplies the RECORDED side (the logged message
      already carries the class [pcls] computes at its fulfil event's
      pre-record agent state — [WeakRetag] brings any bundle into this
      form) and [Hclsobl] the REPLAYED side ([pcls] reads neither the
      store's own timestamp nor the read timestamps, so the π-permuted
      replay computes the same class as the recording did; the only
      [wstate] field it may read, [w_relp], is σ-independent by
      [WeakRobustProv.w_relp_aevs_post_indep]). *)
  Context (Hcls : cls_canonical pcls TS).
  Context (Hclsobl : pcls_obl pcls).
  Context (Himg : pt_img TS = img).
  Context (Hnag : length (pt_trs TS) = length ps).
  Context (Hdata : ∀ p m, pt_log TS !! p = Some m → wm_data m ≠ []).
  Context (Hps0 : ∀ j T ag0, pt_trs TS !! j = Some T →
                    at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)).
  (** THE FABRIC (G4).  [DS] is the behavior's GLOBAL DEVICE-ORDER
      WITNESS; [Hwit] is everything the replay needs of it (W1–W4, see
      [WeakRobustTrace.ptraces_wit]) and [Hd0] says the state phase starts
      at the run's own initial fabric.  Because the replay processes the
      fabric-touching events IN WITNESS ORDER (the [gdev] edges are part
      of the graph it sorts), the fabric it hands each of them is the one
      that event recorded — see [qfab] / [qfab_step]. *)
  Context (Hwit : ptraces_wit TS DS).
  Context (Hd0 : pd_init DS = d0).

  Implicit Types done : list gev.
  Implicit Types e : gev.

  (* ---------------------------------------------------------------- *)
  (** *** THE FABRIC HALF OF THE INVARIANT

      [qdev done n]: the processed events include EXACTLY the first [n]
      entries of the witness — the [gdev] edges are what make the
      processed device set a witness PREFIX at all.  [qfab done d] adds
      that [d] is [dev_at]'s fold over that prefix, i.e. the design
      kernel's "the replay's fabric is the fold of the processed device
      events". *)

  Definition qdev done (n : nat) : Prop :=
    ∀ m e, pd_ord DS !! m = Some e → (e ∈ done ↔ (m < n)%nat).

  Definition qfab done (d : D) : Prop :=
    ∃ n, qdev done n ∧ d = dev_at TS DS n.

  Lemma qfab_init : qfab [] d0.
  Proof.
    exists 0%nat. split.
    - intros m e Hm. split; [by intros ?%elem_of_nil|lia].
    - by rewrite /dev_at Hd0.
  Qed.

  (** The witness never lists a DEV-FREE event (W1). *)
  Lemma pd_ord_not_free m e ev :
    pd_ord DS !! m = Some e → gev_ev TS e = Some ev → ae_dev ev = None →
    False.
  Proof.
    intros Hm Hev Hnone. destruct Hwit as (HW1 & _).
    destruct (HW1 m e Hm) as (ev' & Hev' & Hs).
    rewrite gev_ev_ev_at Hev' in Hev. simplify_eq.
    rewrite Hnone in Hs. by destruct Hs.
  Qed.

  (** THE POSITION OF THE EVENT BEING PROCESSED.  Its gdev predecessor is
      processed and it is not, so the processed prefix of the witness is
      exactly the part strictly below it — the device analogue of
      [nproc_cur]. *)
  Lemma qdev_index done n e m :
    qdev done n → e ∉ done →
    (∀ e', gdep3 TS DS e' e → gev_wf TS e' → e' ∈ done) →
    pd_ord DS !! m = Some e → n = m.
  Proof.
    intros Hqd Hnin Hpre Hm.
    have Hle : (n ≤ m)%nat.
    { destruct (decide (m < n)%nat) as [Hlt|Hge]; [|lia].
      destruct Hnin. by apply (Hqd m e Hm). }
    destruct m as [|m']; [lia|].
    have [e' He'] : is_Some (pd_ord DS !! m').
    { apply lookup_lt_is_Some_2.
      have Hb : (S m' < length (pd_ord DS))%nat by eapply lookup_lt_Some.
      lia. }
    have Hin : e' ∈ done.
    { apply Hpre; [apply gdev_gdep3; by exists m'|].
      apply gev_dev_wf. by eapply pd_ord_dev. }
    have := proj1 (Hqd m' e' He') Hin. lia.
  Qed.

  (** THE HEART OF G4.  One traced event replays at the fabric the
      replayed configuration is holding, and that fabric is the RECORDED
      one whenever the event is fabric-touching; the fold advances by
      exactly this event's [dout] (and stands still on a dev-free one,
      which runs at EVERY fabric and leaves it alone). *)
  Lemma qfab_step done e T ev ag st' (cf : wpcfg P D) :
    e ∉ done →
    (∀ e', gdep3 TS DS e' e → gev_wf TS e' → e' ∈ done) →
    pt_trs TS !! e.1 = Some T → at_evs T !! e.2 = Some ev →
    astep_prog pstep ag ev st' →
    qfab done (pc_dev cf) →
    ∃ d', pstep (pa_st ag) (pc_dev cf) (ae_lb ev) st' d' ∧
          qfab (done ++ [e]) d'.
  Proof.
    intros Hnin Hpre HT Hev Hprog (n & Hqd & Hfab).
    have Hgev : gev_ev TS e = Some ev by rewrite /gev_ev HT /=.
    have Hea : ev_at TS e = Some ev by rewrite -gev_ev_ev_at.
    rewrite /astep_prog in Hprog.
    have Hwit' := Hwit. destruct Hwit' as (HW1 & HW2 & HW3 & HW4).
    destruct (ae_dev ev) as [dd|] eqn:Hdd.
    - (* FABRIC-TOUCHING: replayed AT ITS RECORDED FABRIC *)
      have Hdev : is_Some (ae_dev ev) by rewrite Hdd; eexists.
      destruct (HW2 e.1 e.2 ev) as (m & Hm);
        [by rewrite -(surjective_pairing e)|done|].
      rewrite -(surjective_pairing e) in Hm.
      have Hn : n = m by eapply qdev_index. subst n.
      (* the input fabric IS the recorded [din] *)
      have Hdin : ev_din TS e = Some (dev_at TS DS m) by apply HW4.
      have Hfst : dd.1 = dev_at TS DS m.
      { move: Hdin. rewrite /ev_din Hea /= Hdd /=. by intros [= ->]. }
      exists dd.2. split.
      { rewrite Hfab -Hfst. exact Hprog. }
      exists (S m). split.
      + intros m0 e0 Hm0. rewrite elem_of_app elem_of_list_singleton. split.
        * intros [Hin| ->].
          -- have := proj1 (Hqd m0 e0 Hm0) Hin. lia.
          -- have Hm0m : m0 = m by eapply (pd_ord_index_inj TS DS m0 m e).
             lia.
        * intros Hlt. destruct (decide (m0 = m)) as [->|Hne].
          -- right. rewrite Hm in Hm0. by simplify_eq.
          -- left. apply (Hqd m0 e0 Hm0). lia.
      + rewrite /dev_at Hm /= /ev_dout Hea /= Hdd //.
    - (* DEV-FREE: the fold, and the fabric, stand still *)
      exists (pc_dev cf). split; [apply Hprog|].
      exists n. split; [|done].
      intros m0 e0 Hm0. rewrite elem_of_app elem_of_list_singleton. split.
      + intros [Hin| ->]; [by apply (Hqd m0 e0 Hm0)|].
        by destruct (pd_ord_not_free m0 e ev Hm0 Hgev Hdd).
      + intros Hlt. left. by apply (Hqd m0 e0 Hm0).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** The order half of the invariant *)

  Definition qorder done : Prop :=
    NoDup done ∧
    (∀ e, e ∈ done → gev_wf TS e) ∧
    (∀ x, x ∈ done → ∀ y, gdep2 TS y x → gev_wf TS y → y ∈ done) ∧
    (∀ n y, done !! n = Some y → ∀ x, gdep2 TS x y →
       ∃ i, (i < n)%nat ∧ done !! i = Some x) ∧
    (∀ j k, (j, k) ∈ done ↔ (gev_wf TS (j, k) ∧ (k < nproc done j)%nat)).

  (** The pf-configuration half — the last clause is G4's FABRIC CLAUSE:
      the replayed configuration's fabric is the [dev_at] fold of the
      PROCESSED witness prefix. *)
  Definition qcfg done (cf : wpcfg P D) : Prop :=
    rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) cf ∧
    pc_img cf = img ∧ pc_log cf = pf_log TS done ∧
    length (pc_ags cf) = length ps ∧
    (∀ j T, pt_trs TS !! j = Some T →
       ∃ agn, at_ags T !! nproc done j = Some agn ∧
         pc_ags cf !! j
         = Some (WPAgent (pa_st agn)
                   (aevs_post (pi TS done) (take (nproc done j) (at_evs T)) ws_init)
                   ∅)) ∧
    qfab done (pc_dev cf).

  Definition Qinv done : Prop := qorder done ∧ ∃ cf, qcfg done cf.

  (* ---------------------------------------------------------------- *)
  (** *** What the order half buys *)

  Lemma qorder_dc done x y :
    qorder done → x ∈ done → gdep2 TS y x → gev_wf TS y → y ∈ done.
  Proof. intros (_ & _ & Hdc & _ & _) ???. by eapply Hdc. Qed.

  Lemma qorder_wf done e : qorder done → e ∈ done → gev_wf TS e.
  Proof. intros (_ & Hw & _) ?. by apply Hw. Qed.

  Lemma qorder_mem done j k :
    qorder done → ((j, k) ∈ done ↔ (gev_wf TS (j, k) ∧ (k < nproc done j)%nat)).
  Proof. intros (_ & _ & _ & _ & H). apply H. Qed.

  (** The processing order respects [tc gdep2] — the fact every ordering
      argument below is spent on.  (Carried as [Hpred] and iterated: this
      is the "retroactive" argument of the design note.) *)
  Lemma qorder_tc_index done x y n :
    qorder done → done !! n = Some y → tc (gdep2 TS) x y →
    ∃ i, (i < n)%nat ∧ done !! i = Some x.
  Proof.
    intros Hq Hn Htc. move: n Hn.
    have Hpred : ∀ n y, done !! n = Some y → ∀ x, gdep2 TS x y →
       ∃ i, (i < n)%nat ∧ done !! i = Some x by apply Hq.
    induction Htc as [x y Hxy|x y z Hxy Hyz IH]; intros n Hn.
    - by eapply Hpred.
    - destruct (IH n Hn) as (m & Hm & Hlkm).
      destruct (Hpred m y Hlkm x Hxy) as (i & Hi & Hlki).
      exists i. split; [lia|done].
  Qed.

  Lemma qorder_tc_in done x y :
    qorder done → y ∈ done → tc (gdep2 TS) x y → x ∈ done.
  Proof.
    intros Hq Hy Htc. apply elem_of_list_lookup in Hy as (n & Hn).
    destruct (qorder_tc_index done x y n Hq Hn Htc) as (i & _ & Hi).
    by eapply elem_of_list_lookup_2.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** [fl] / [pf_log] bookkeeping under the invariant *)

  Lemma fl_ts_pos done t : t ∈ fl TS done → (0 < t)%nat.
  Proof.
    rewrite elem_of_fl. intros (e & _ & Hts). by eapply gev_ts_pos.
  Qed.

  Lemma NoDup_fl done : qorder done → NoDup (fl TS done).
  Proof.
    intros (Hnd & _ & _). apply NoDup_omap_inj; [done|].
    intros x y b _ _ Hx Hy. by eapply (grf_source_unique pstep pdev).
  Qed.

  Lemma pi_mem done i t :
    qorder done → fl TS done !! i = Some t → pi TS done t = S i.
  Proof.
    intros Hq Hi. eapply piL_mem; [by apply NoDup_fl|exact Hi|].
    have : (0 < t)%nat by eapply fl_ts_pos, elem_of_list_lookup_2, Hi. lia.
  Qed.

  (** A processed timestamp names its own pf log position. *)
  Lemma pf_log_pi done t :
    qorder done → t ∈ fl TS done →
    (0 < pi TS done t)%nat ∧ (pi TS done t ≤ length (pf_log TS done))%nat ∧
    pf_log TS done !! (pi TS done t - 1)%nat = Some (msg_at TS t).
  Proof.
    intros Hq Ht. apply elem_of_list_lookup in Ht as (i & Hi).
    have Hp : pi TS done t = S i by eapply pi_mem.
    have Hlt : (i < length (fl TS done))%nat by eapply lookup_lt_Some.
    rewrite Hp. split_and!; [lia|rewrite fl_len; lia|].
    replace (S i - 1)%nat with i by lia.
    by rewrite /pf_log list_lookup_fmap Hi /=.
  Qed.

  (** …and the message it names is the behavior's own. *)
  Lemma msg_at_eq t m :
    pt_log TS !! (t - 1)%nat = Some m → msg_at TS t = m.
  Proof. intros H. by rewrite /msg_at H. Qed.

  Lemma fl_msg done t :
    qorder done → t ∈ fl TS done →
    ∃ e, e ∈ done ∧ gev_ts TS e = Some t ∧
         pt_log TS !! (t - 1)%nat = Some (msg_at TS t) ∧
         wm_tid (msg_at TS t) = Some e.1.
  Proof.
    intros Hq Ht. apply elem_of_fl in Ht as (e & He & Hts).
    destruct (gev_ts_msg pstep TS e t Hwf Hts) as (base & data & kc & Hm).
    exists e. rewrite (msg_at_eq t _ Hm). by split_and!.
  Qed.

  (** THE INVERSION the two cruxes run on: a byte-[a] write inside a pf
      window is [π t̂] for a PROCESSED byte-[a] write [t̂]. *)
  Lemma pf_writes_in_inv done a lo hi :
    qorder done → writes_in (pf_log TS done) a lo hi →
    ∃ that ehat,
      (lo < pi TS done that)%nat ∧ (pi TS done that ≤ hi)%nat ∧
      ehat ∈ done ∧ writes_b TS a ehat that ∧
      wm_tid (msg_at TS that) = Some ehat.1.
  Proof.
    intros Hq (q & Hlo & Hhi & m & Hm & Hb).
    rewrite /pf_log list_lookup_fmap in Hm.
    destruct (fl TS done !! (q - 1)%nat) as [that|] eqn:Hfl; simpl in Hm; [|done].
    simplify_eq.
    have Hin : that ∈ fl TS done by eapply elem_of_list_lookup_2.
    have Hpi : pi TS done that = S (q - 1)%nat by eapply pi_mem.
    have Hq1 : S (q - 1)%nat = q by lia.
    rewrite Hq1 in Hpi.
    destruct (fl_msg done that Hq Hin) as (ehat & He & Hts & Hlog & Htid).
    exists that, ehat. rewrite Hpi. split_and!; [done|done|done| |done].
    split; [done|]. by exists (msg_at TS that).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** Leaf/read provenance: every timestamp a processed event touched
         is itself processed *)

  Lemma read_source_in done e a t :
    (∀ e', gdep2 TS e' e → gev_wf TS e' → e' ∈ done) →
    gev_reads TS e a t → (0 < t)%nat →
    ∃ er, er ∈ done ∧ writes_b TS a er t.
  Proof.
    intros Hpre Hr Hpos.
    destruct (gev_reads_source pstep TS e a t Hwf Hwfl Hr Hpos) as (er & Hw & Hrf).
    exists er. split; [|done]. apply Hpre; [by apply grf_gdep2|].
    by eapply writes_b_wf.
  Qed.

  Lemma read_ts_in_fl done e a t :
    qorder done →
    (∀ e', gdep2 TS e' e → gev_wf TS e' → e' ∈ done) →
    gev_reads TS e a t → (0 < t)%nat → t ∈ fl TS done.
  Proof.
    intros Hq Hpre Hr Hpos.
    destruct (read_source_in done e a t Hpre Hr Hpos) as (er & He & Hw).
    apply elem_of_fl. exists er. split; [done|apply Hw].
  Qed.

  (** Every nonzero timestamp occurring in agent [j]'s PROCESSED prefix
      is in [fl done]: a fulfil is the processed event's own; a read's
      source is a [gdep2]-predecessor, hence processed by closure. *)
  Lemma occ_processed done j T t :
    qorder done → pt_trs TS !! j = Some T →
    ev_ts_occurs (take (nproc done j) (at_evs T)) t → (0 < t)%nat →
    t ∈ fl TS done.
  Proof.
    intros Hq HT (ev & Hev & Hocc) Hpos.
    apply elem_of_take in Hev as (k & Hk & Hklt).
    have Hgev : gev_ev TS (j, k) = Some ev by rewrite /gev_ev /= HT /=.
    have Hwfe : gev_wf TS (j, k) by rewrite /gev_wf Hgev; eauto.
    have Hin : (j, k) ∈ done by apply (qorder_mem done j k Hq).
    destruct Hocc as [(a & Ha)|Hts].
    - have Hr : gev_reads TS (j, k) a t.
      { exists (ae_lb ev). split; [|done]. by rewrite /gev_lb Hgev. }
      eapply read_ts_in_fl; [done| |exact Hr|done].
      intros e' Hd Hw'. eapply qorder_dc; [exact Hq|exact Hin|done|done].
    - apply elem_of_fl. exists (j, k). split; [done|].
      by rewrite /gev_ts Hgev /=.
  Qed.

  (** …hence [pi] is STABLE on the processed prefixes as [done] grows. *)
  Lemma ws_stable done l j T :
    qorder done → pt_trs TS !! j = Some T →
    aevs_post (pi TS (done ++ l)) (take (nproc done j) (at_evs T)) ws_init
    = aevs_post (pi TS done) (take (nproc done j) (at_evs T)) ws_init.
  Proof.
    intros Hq HT. apply aevs_post_ext. intros t Hocc.
    apply pi_app. destruct (decide (t = 0%nat)) as [->|Ht]; [by right|].
    left. eapply occ_processed; [done|exact HT|exact Hocc|lia].
  Qed.

  (** π ORDERS the timestamps of [tc gdep2]-related PROCESSED events —
      the monotonicity every window argument below spends. *)
  Lemma pi_lt_of_tc done e1 e2 t1 t2 :
    qorder done → e2 ∈ done → tc (gdep2 TS) e1 e2 →
    gev_ts TS e1 = Some t1 → gev_ts TS e2 = Some t2 →
    (pi TS done t1 < pi TS done t2)%nat.
  Proof.
    intros Hq He2 Htc H1 H2.
    apply elem_of_list_lookup in He2 as (n2 & Hn2).
    destruct (qorder_tc_index done e1 e2 n2 Hq Hn2 Htc) as (n1 & Hlt & Hn1).
    have Hf1 : fl TS done !! fpos TS done n1 = Some t1 by eapply fl_lookup_fpos.
    have Hf2 : fl TS done !! fpos TS done n2 = Some t2 by eapply fl_lookup_fpos.
    have Hp1 : pi TS done t1 = S (fpos TS done n1) by eapply pi_mem.
    have Hp2 : pi TS done t2 = S (fpos TS done n2) by eapply pi_mem.
    have Hfl : (fpos TS done n1 < fpos TS done n2)%nat by eapply fpos_lt.
    lia.
  Qed.

  (** The co-order version, packaged against [Hco]: two PROCESSED byte-[a]
      writes are π-ordered by their timestamps. *)
  Lemma pi_lt_of_co done a e1 e2 t1 t2 :
    qorder done → e2 ∈ done →
    writes_b TS a e1 t1 → writes_b TS a e2 t2 → (t1 < t2)%nat →
    (pi TS done t1 < pi TS done t2)%nat.
  Proof.
    intros Hq He2 H1 H2 Hlt. eapply pi_lt_of_tc; [done|done| |apply H1|apply H2].
    apply tc_gdep_gdep2. by eapply (Hco a).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** The per-agent prefix fact, and the order step *)

  (** THE EVENT BEING PROCESSED IS THE NEXT ONE OF ITS AGENT.  Its po
      predecessors are all processed (the step hypothesis) and it is not,
      so the processed count of its agent is exactly its step index. *)
  Lemma nproc_cur done e :
    qorder done → gev_wf TS e → e ∉ done →
    (∀ e', gdep2 TS e' e → gev_wf TS e' → e' ∈ done) →
    nproc done e.1 = e.2.
  Proof.
    intros Hq Hwfe Hnin Hpre. destruct e as [j k]. simpl.
    have Hle : (nproc done j ≤ k)%nat.
    { destruct (decide (k < nproc done j)%nat) as [Hlt|Hge]; [|lia].
      destruct Hnin. apply (qorder_mem done j k Hq). by split. }
    destruct (decide (nproc done j < k)%nat) as [Hlt|Hge]; [|lia]. exfalso.
    have Hwf' : gev_wf TS (j, nproc done j).
    { apply gev_wf_bounds. apply gev_wf_bounds in Hwfe as (T & HT & Hk).
      exists T. simpl in HT, Hk |- *. split; [done|lia]. }
    have Hin : (j, nproc done j) ∈ done.
    { apply Hpre; [|done]. apply gpo_gdep2. by split_and!. }
    apply (qorder_mem done j (nproc done j) Hq) in Hin as [_ Hc]. lia.
  Qed.

  Lemma qorder_step done e :
    qorder done → gev_wf TS e → e ∉ done →
    (∀ e', gdep2 TS e' e → gev_wf TS e' → e' ∈ done) →
    qorder (done ++ [e]).
  Proof.
    intros Hq Hwfe Hnin Hpre.
    have Hnp := nproc_cur done e Hq Hwfe Hnin Hpre.
    have Hq' := Hq. destruct Hq' as (Hnd & Hwfs & Hdc & Hpred & Hmem).
    split_and!.
    - apply list_relations.NoDup_app. split_and!; [done| |apply NoDup_singleton].
      intros x Hx Hx'. apply elem_of_list_singleton in Hx' as ->. done.
    - intros e' He'. apply elem_of_app in He' as [He'|He']; [by apply Hwfs|].
      apply elem_of_list_singleton in He' as ->. done.
    - intros x Hx y Hd Hy. apply elem_of_app.
      apply elem_of_app in Hx as [Hx|Hx]; left.
      + by eapply Hdc.
      + apply elem_of_list_singleton in Hx as ->. by apply Hpre.
    - intros n y Hn x Hd.
      destruct (decide (n < length done)%nat) as [Hlt|Hge].
      + rewrite lookup_app_l in Hn; [done|].
        destruct (Hpred n y Hn x Hd) as (i & Hi & Hlki).
        exists i. split; [done|]. rewrite lookup_app_l; [|done].
        eapply lookup_lt_Some, Hlki.
      + have Hn' : n = length done.
        { apply lookup_lt_Some in Hn. rewrite length_app /= in Hn. lia. }
        subst n. rewrite lookup_app_r in Hn; [lia|].
        rewrite Nat.sub_diag /= in Hn. simplify_eq.
        have Hxin : x ∈ done.
        { apply Hpre; [done|]. by destruct (gdep2_wf TS x _ Hd). }
        apply elem_of_list_lookup in Hxin as (i & Hi).
        exists i. split; [by eapply lookup_lt_Some|].
        rewrite lookup_app_l; [by eapply lookup_lt_Some|done].
    - intros j k. destruct e as [j0 k0]. simpl in Hnp.
      destruct (decide (j = j0)) as [->|Hne].
      + have Hnn : nproc (done ++ [(j0, k0)]) j0 = S (nproc done j0)
          by apply (nproc_app_eq done (j0, k0)).
        rewrite Hnn Hnp elem_of_app. split.
        * intros [Hin|Hin].
          -- apply Hmem in Hin as [Hw Hlt]. split; [done|lia].
          -- apply elem_of_list_singleton in Hin. simplify_eq.
             split; [done|lia].
        * intros [Hw Hlt]. destruct (decide (k = k0)) as [->|Hne2].
          -- right. by apply elem_of_list_singleton.
          -- left. apply Hmem. split; [done|lia].
      + have Hnn : nproc (done ++ [(j0, k0)]) j = nproc done j
          by apply (nproc_app_ne done (j0, k0) j).
        rewrite Hnn elem_of_app. split.
        * intros [Hin|Hin]; [by apply Hmem|].
          apply elem_of_list_singleton in Hin. by simplify_eq.
        * intros H. left. by apply Hmem.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** CRUX 1+2: the transported READ (values and readability)

      The four cases of the [readable] window are exactly the design
      note's: [t̂ = t] (π injective), [t̂ < t] (co + processing order),
      [t < t̂ ≤ F] (the behavior's own readability), [t̂ > F] (the [gE]
      edges put π t̂ above every transported floor leaf). *)

  Lemma read_ok_pf done e T ev ag l base tvs lat ws :
    qorder done →
    (∀ e', gdep2 TS e' e → gev_wf TS e' → e' ∈ done) →
    nproc done e.1 = e.2 →
    pt_trs TS !! e.1 = Some T →
    at_evs T !! e.2 = Some ev →
    at_ags T !! e.2 = Some ag →
    ae_lb ev = l →
    match l with LLoad _ _ _ _ | LRmw _ _ _ _ _ => True | _ => False end →
    lb_reads l = tvs_reads base tvs →
    read_ok (pt_img TS) (pt_log TS) (pa_ws ag) (lb_aq l) lat base tvs →
    ws = aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init →
    read_ok img (pf_log TS done) ws (lb_aq l) false base
      (tlabel_ts (pi TS done) tvs).
  Proof.
    intros Hq Hpre Hnp HT Hev Hag Hlbe Hrdl Hreads Hro Hws.
    have Hgev : gev_ev TS e = Some ev by rewrite /gev_ev HT /=.
    have Hlb : gev_lb TS e = Some l by rewrite /gev_lb Hgev /= Hlbe.
    have Hrel : lrel (pi TS done) (pre_lstate TS e) ws.
    { rewrite Hws (pre_lstate_tr TS e T HT).
      apply lrel_aevs_post_init, pi_sigma_ok. }
    have Hleaves : ∀ a, rd_leaves TS e a = lfloor (pre_lstate TS e) (lb_aq l) a.
    { intros a. rewrite /rd_leaves Hlb. by destruct l. }
    have Hfpf : ∀ a, Nat.max (load_vpre ws (lb_aq l)) (coh ws a)
                     = lval (pi TS done) (rd_leaves TS e a).
    { intros a. rewrite (Hleaves a). by apply lrel_floor. }
    have Hfbeh : ∀ a, rd_floor TS e a
                 = Nat.max (load_vpre (pa_ws ag) (lb_aq l)) (coh (pa_ws ag) a).
    { intros a. by eapply (rd_floor_ws pstep). }
    intros jb t' v Hjb.
    destruct (tlabel_ts_lookup_inv (pi TS done) tvs jb t' v Hjb) as (t & Htv & ->).
    destruct (Hro jb t v Htv) as (Hval & Hrd & _).
    have Hreadin : (base + Z.of_nat jb, t) ∈ lb_reads l.
    { rewrite Hreads. apply elem_of_tvs_reads. by exists jb, v. }
    have Hgr : gev_reads TS e (base + Z.of_nat jb) t by exists l.
    (* ---- VALUES ---- *)
    have Hvalpf : log_byte img (pf_log TS done) (pi TS done t)
                    (base + Z.of_nat jb) = Some v.
    { destruct (decide (t = 0%nat)) as [->|Htpos].
      - rewrite pi_0 log_byte_0. rewrite log_byte_0 in Hval. by rewrite -Himg.
      - have Hin : t ∈ fl TS done
          by eapply read_ts_in_fl; [done|done|exact Hgr|lia].
        destruct (pf_log_pi done t Hq Hin) as (Hp1 & Hp2 & Hp3).
        rewrite (log_byte_pos img (pf_log TS done) _ (msg_at TS t) _ Hp1 Hp3).
        destruct t as [|p]; [lia|]. rewrite log_byte_S in Hval.
        destruct (pt_log TS !! p) as [m|] eqn:Hm; simpl in Hval; [|done].
        rewrite /msg_at. replace (S p - 1)%nat with p by lia.
        by rewrite Hm /=. }
    (* ---- READABILITY ---- *)
    have Hnw : ¬ writes_in (pf_log TS done) (base + Z.of_nat jb) (pi TS done t)
                 (Nat.max (load_vpre ws (lb_aq l)) (coh ws (base + Z.of_nat jb))).
    { rewrite (Hfpf (base + Z.of_nat jb)). intros Hw.
      destruct (pf_writes_in_inv done (base + Z.of_nat jb) _ _ Hq Hw)
        as (that & ehat & Hlo & Hhi & Hehat & Hwb & Htid).
      have Hthatpos : (0 < that)%nat by eapply writes_b_pos.
      destruct (Nat.lt_trichotomy that t) as [Hlt|[Heq|Hgt]].
      - have Htpos : (0 < t)%nat by lia.
        destruct (read_source_in done e (base + Z.of_nat jb) t Hpre Hgr Htpos)
          as (er & Her & Hwr).
        have Hmono := pi_lt_of_co done (base + Z.of_nat jb) ehat er that t
                        Hq Her Hwb Hwr Hlt.
        lia.
      - subst that. lia.
      - destruct (decide (that ≤ rd_floor TS e (base + Z.of_nat jb))%nat)
          as [Hle|Habove].
        + destruct Hrd as [_ Hnwb]. apply Hnwb.
          rewrite -(Hfbeh (base + Z.of_nat jb)).
          exists that. split_and!; [lia|lia|].
          destruct Hwb as (_ & m & Hm & Hb). by exists m.
        + have Hbound : (lval (pi TS done)
                           (rd_leaves TS e (base + Z.of_nat jb))
                         < pi TS done that)%nat.
          { apply lval_lt; [|apply pi_pos; lia].
            intros tstar Hstar.
            destruct (decide (tstar = 0%nat)) as [->|Hstarpos].
            { rewrite pi_0. apply pi_pos. lia. }
            have Hleaf : lstate_leaf (pre_lstate TS e) tstar.
            { apply (lfloor_leaf _ (lb_aq l) (base + Z.of_nat jb)).
              by rewrite -(Hleaves (base + Z.of_nat jb)). }
            have Hocc := pre_lstate_leaf_occurs TS e T tstar HT Hleaf.
            rewrite -Hnp in Hocc.
            have Hinfl : tstar ∈ fl TS done
              by eapply occ_processed; [done|exact HT|exact Hocc|lia].
            apply elem_of_fl in Hinfl as (estar & Hestar & Htsstar).
            eapply pi_lt_of_tc; [done|exact Hehat| |exact Htsstar|apply Hwb].
            apply tc_once, gE_gdep2. exists e.
            exists l, (base + Z.of_nat jb), t, tstar, that.
            split_and!; [done|done|done|lia|done|apply Hwb| |lia].
            destruct Hwb as (_ & m & Hm & Hb). by exists m. }
          lia. }
    split_and!; [done| |done].
    split; [by rewrite Hvalpf|done].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** CRUX 3: the transported EXCLUSIVITY WINDOW of an rmw *)

  (** The author-aware form of [pf_writes_in_inv]. *)
  Lemma pf_writes_in_by_inv done Q a lo hi :
    qorder done → writes_in_by (pf_log TS done) Q a lo hi →
    ∃ that ehat,
      (lo < pi TS done that)%nat ∧ (pi TS done that ≤ hi)%nat ∧
      ehat ∈ done ∧ writes_b TS a ehat that ∧ Q (Some ehat.1).
  Proof.
    intros Hq (q & Hlo & Hhi & m & Hm & Hb & HQ).
    rewrite /pf_log list_lookup_fmap in Hm.
    destruct (fl TS done !! (q - 1)%nat) as [that|] eqn:Hfl; simpl in Hm; [|done].
    simplify_eq.
    have Hin : that ∈ fl TS done by eapply elem_of_list_lookup_2.
    have Hpi : pi TS done that = S (q - 1)%nat by eapply pi_mem.
    have Hq1 : S (q - 1)%nat = q by lia.
    rewrite Hq1 in Hpi.
    destruct (fl_msg done that Hq Hin) as (ehat & He & Hts & Hlog & Htid).
    exists that, ehat. rewrite Hpi. rewrite Htid in HQ.
    split_and!; [done|done|done| |done].
    split; [done|]. by exists (msg_at TS that).
  Qed.

  Lemma msg_byte_run base data tid k (jb : nat) :
    (jb < length data)%nat →
    is_Some (msg_byte (WMsg base data tid k) (base + Z.of_nat jb)).
  Proof.
    intros Hj. rewrite /msg_byte /=. case_bool_decide as Hb; [|lia].
    replace (Z.to_nat (base + Z.of_nat jb - base)) with jb by lia.
    by apply lookup_lt_is_Some_2.
  Qed.

  Lemma excl_ok_pf done e T ev (ag : wpagent P) f aq rl base tvs data ts :
    qorder done →
    e ∉ done →
    (∀ e', gdep2 TS e' e → gev_wf TS e' → e' ∈ done) →
    pt_trs TS !! e.1 = Some T →
    at_evs T !! e.2 = Some ev →
    ae_lb ev = LRmw aq rl base tvs data →
    ae_ts ev = Some ts →
    astep_ok (pt_img TS) (pt_log TS) e.1 ag (ae_lb ev) f (ae_ts ev) →
    excl_ok (pf_log TS done) e.1 base (tlabel_ts (pi TS done) tvs)
      (S (length (pf_log TS done))).
  Proof.
    intros Hq Hnin Hpre HT Hev Hlbe Htse Hok.
    have Hgev : gev_ev TS e = Some ev by rewrite /gev_ev HT /=.
    have Hgts : gev_ts TS e = Some ts by rewrite /gev_ts Hgev /=.
    have Hok' := Hok. rewrite Hlbe Htse /= in Hok'.
    destruct Hok' as (ts' & kc & Hlen & _ & Hlog & _ & _ & _ & _ & Heq).
    injection Heq as <-.
    intros jb t' v Hjb.
    destruct (tlabel_ts_lookup_inv (pi TS done) tvs jb t' v Hjb)
      as (tr & Htv & ->).
    have Hreadin : (base + Z.of_nat jb, tr) ∈ lb_reads (ae_lb ev).
    { rewrite Hlbe /=. apply elem_of_tvs_reads. by exists jb, v. }
    have Hgr : gev_reads TS e (base + Z.of_nat jb) tr.
    { exists (ae_lb ev). split; [by rewrite /gev_lb Hgev /=|done]. }
    have Hjblt : (jb < length data)%nat.
    { rewrite -Hlen. by eapply lookup_lt_Some. }
    have Hwbe : writes_b TS (base + Z.of_nat jb) e ts.
    { split; [done|]. exists (WMsg base data (Some e.1) kc). split; [done|].
      by apply msg_byte_run. }
    replace (S (length (pf_log TS done)) - 1)%nat
      with (length (pf_log TS done)) by lia.
    intros Hw.
    destruct (pf_writes_in_by_inv done _ (base + Z.of_nat jb) _ _ Hq Hw)
      as (that & ehat & Hlo & Hhi & Hehat & Hwb & Hfor).
    have Hthatpos : (0 < that)%nat by eapply writes_b_pos.
    destruct (Nat.lt_trichotomy that tr) as [Hlt|[Heq|Hgt]].
    - (* below the read: co-monotonicity puts it below π tr *)
      have Htrpos : (0 < tr)%nat by lia.
      destruct (read_source_in done e (base + Z.of_nat jb) tr Hpre Hgr Htrpos)
        as (er & Her & Hwr).
      have Hmono := pi_lt_of_co done (base + Z.of_nat jb) ehat er that tr
                      Hq Her Hwb Hwr Hlt.
      lia.
    - subst that. lia.
    - destruct (decide (that ≤ ts - 1)%nat) as [Hle|Habove].
      + (* the BEHAVIOR's own exclusivity window *)
        eapply (astep_ok_read_excl (pt_img TS) (pt_log TS) e.1 ag (ae_lb ev) f ts
                  tr (base + Z.of_nat jb));
          [by rewrite -Htse|exact Hreadin|].
        exists that. split_and!; [lia|lia|].
        destruct (fl_msg done that Hq) as (e2 & He2 & Hts2 & Hlog2 & Htid2).
        { apply elem_of_fl. exists ehat. split; [done|apply Hwb]. }
        destruct Hwb as (Hts_ & m & Hm & Hb).
        have Hmm : msg_at TS that = m.
        { rewrite Hlog2 in Hm. by injection Hm. }
        exists m. split_and!; [done|done|]. rewrite -Hmm Htid2.
        have Heq2 : e2 = ehat.
        { eapply (grf_source_unique pstep pdev); [done|exact Hts2|exact Hts_]. }
        rewrite Heq2. exact Hfor.
      + destruct (decide (that = ts)) as [->|Hne].
        * (* the rmw's OWN message: its event is not processed *)
          have Heq3 : ehat = e.
          { eapply (grf_source_unique pstep pdev); [done|apply Hwb|exact Hgts]. }
          apply Hnin. by rewrite -Heq3.
        * (* strictly above: co would drag the current event into [done] *)
          have Htc : tc (gdep TS) e ehat.
          { eapply (Hco (base + Z.of_nat jb)); [exact Hwbe|exact Hwb|lia]. }
          apply Hnin. eapply qorder_tc_in; [done|exact Hehat|].
          by apply tc_gdep_gdep2.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** THE REPLAYED AGENT STATE AGREES WITH THE RECORDED ONE ON
          [w_relp] (the G6a bridge)

      The replay hands the acting agent the π-transported fold
      [aevs_post (pi TS done) (take k (at_evs T)) ws_init]; the recording
      held [pa_ws ag], which is the SAME fold at σ = [id]
      ([WeakRobustProv.asteps_ws_fold], with [Hwsi] pinning the trace's
      first record at [ws_init]).  [w_relp] is σ-independent
      ([WeakRobustProv.w_relp_aevs_post_indep]), so the two agree on it —
      and [w_relp] is the only [wstate] field [pcls_obl] lets [pcls]
      read. *)
  Lemma replay_ws_relp (j : agent) (k : nat) T ag σ :
    pt_trs TS !! j = Some T → at_ags T !! k = Some ag →
    w_relp (pa_ws ag) = w_relp (aevs_post σ (take k (at_evs T)) ws_init).
  Proof.
    intros HT Hag.
    have Hwfi : atrace_wf pstep (pt_img TS) (pt_log TS) j T by apply Hwf.
    destruct (atrace_first_is_Some pstep (pt_img TS) (pt_log TS) j T Hwfi)
      as [ag0 Hag0].
    have Hws0 : pa_ws ag0 = ws_init by eapply Hwsi.
    have Hfold : pa_ws ag = aevs_post id (take k (at_evs T)) (pa_ws ag0).
    { eapply (asteps_ws_fold pstep (pt_img TS) (pt_log TS) j
                (at_ags T) (at_evs T) k ag0 ag);
        [exact Hwfi|exact Hag0|exact Hag]. }
    rewrite Hfold Hws0. by apply w_relp_aevs_post_indep.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** Assembling the configuration half after one pf step

      Every label arm produces a configuration of the SAME shape — the
      new pf log, and the acting agent's record advanced by one trace
      position — so the bookkeeping is done once here. *)

  Lemma qcfg_step done e T ev ag' cf newws lb' (dv : D) :
    qorder done →
    nproc done e.1 = e.2 →
    pt_trs TS !! e.1 = Some T → at_evs T !! e.2 = Some ev →
    at_ags T !! S e.2 = Some ag' →
    qcfg done cf →
    newws = aev_post (pi TS (done ++ [e])) ev
              (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) →
    qfab (done ++ [e]) dv →
    wp_pf_step pstep pcls e.1 lb' cf
      (WPCfg (pc_img cf) (pf_log TS (done ++ [e])) dv
             (<[e.1 := WPAgent (pa_st ag') newws ∅]> (pc_ags cf))) →
    qcfg (done ++ [e])
      (WPCfg (pc_img cf) (pf_log TS (done ++ [e])) dv
             (<[e.1 := WPAgent (pa_st ag') newws ∅]> (pc_ags cf))).
  Proof.
    intros Hq Hnp HT Hev Hag' Hc Hnew Hdv Hstep.
    have Hc' := Hc. destruct Hc' as (Hrun & Hcimg & Hclog & Hclen & Hcags & _).
    have Hlt : (e.1 < length (pc_ags cf))%nat.
    { destruct (Hcags e.1 T HT) as (agn & _ & Hlk). by eapply lookup_lt_Some. }
    split_and!.
    - eapply rtc_r; [exact Hrun|]. by exists e.1, lb'.
    - done.
    - done.
    - by rewrite /= length_insert.
    - intros j T' HT'. destruct (decide (j = e.1)) as [->|Hne].
      + rewrite HT' in HT. injection HT as <-.
        exists ag'. rewrite (nproc_app_eq done e) Hnp. split; [done|].
        rewrite /= list_lookup_insert; [done|]. rewrite Hnew.
        rewrite (take_S_r _ _ _ Hev) aevs_post_app.
        rewrite -Hnp (ws_stable done [e] e.1 T' Hq HT') Hnp //.
      + destruct (Hcags j T' HT') as (agn & Hagn & Hlkj).
        exists agn. rewrite (nproc_app_ne done e j Hne). split; [done|].
        rewrite /= list_lookup_insert_ne; [done|]. rewrite Hlkj.
        by rewrite (ws_stable done [e] j T' Hq HT').
    - exact Hdv.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** THE STEP: one traced event becomes one promise-free step *)

  Lemma Qinv_step done e :
    Qinv done → gev_wf TS e → e ∉ done →
    (∀ e', gdep3 TS DS e' e → gev_wf TS e' → e' ∈ done) →
    Qinv (done ++ [e]).
  Proof.
    intros [Hq Hcfe] Hwfe Hnin Hpre3.
    (* the ORDER half sees only [gdep2]; the FABRIC half is what spends
       the [gdev] edges ([qfab_step] below) *)
    have Hpre : ∀ e', gdep2 TS e' e → gev_wf TS e' → e' ∈ done.
    { intros e' Hd Hw. apply Hpre3; [by apply gdep2_gdep3|done]. }
    have Hq' : qorder (done ++ [e]) by apply qorder_step.
    have Hnp : nproc done e.1 = e.2 by apply nproc_cur.
    split; [done|].
    destruct Hcfe as (cf & Hc).
    have Hc' := Hc.
    destruct Hc' as (Hrun & Hcimg & Hclog & Hclen & Hcags & Hfab).
    destruct (proj1 (gev_wf_bounds TS e) Hwfe) as (T & HT & Hklt).
    have [ev Hev] : is_Some (at_evs T !! e.2) by apply lookup_lt_is_Some_2.
    have Hgev : gev_ev TS e = Some ev by rewrite /gev_ev HT /=.
    have Hatr : atrace_wf pstep (pt_img TS) (pt_log TS) e.1 T by apply Hwf.
    destruct (asteps_wf_step pstep (pt_img TS) (pt_log TS) e.1 (at_ags T)
                (at_evs T) e.2 ev Hatr Hev)
      as (ag & ag2 & st' & f & Hag & Hag2 & Hps & Hok & Hagn).
    (* THE FABRIC ARM: the recorded step runs AT THE REPLAY'S FABRIC —
       which, for a fabric-touching event, IS the fabric it recorded *)
    destruct (qfab_step done e T ev ag st' cf Hnin Hpre3 HT Hev Hps Hfab)
      as (dnew & Hpure & Hfab').
    destruct (Hcags e.1 T HT) as (agn & Hagn0 & Hcflk).
    rewrite Hnp Hag in Hagn0. injection Hagn0 as <-. rewrite Hnp in Hcflk.
    have Hstpost : pa_st ag2 = st' by rewrite Hagn.
    (* π is stable on everything this event READS *)
    have Hstab : ∀ a t, gev_reads TS e a t → pi TS (done ++ [e]) t = pi TS done t.
    { intros a t Hr. apply pi_app.
      destruct (decide (t = 0%nat)) as [->|Ht]; [by right|].
      left. eapply read_ts_in_fl; [done|exact Hpre|exact Hr|lia]. }
    have Hokc := Hok.
    destruct (ae_lb ev) as [|aq lat base tvs|rl base data|aq rl base tvs data
                            |pr pw sr sw|] eqn:Hlbe.
    - (* ---- LSilent ---- *)
      destruct Hok as (Hf & Hts0).
      have Hgts : gev_ts TS e = None by rewrite /gev_ts Hgev /= Hts0.
      have Hlogq : pf_log TS (done ++ [e]) = pc_log cf.
      { by rewrite Hclog /pf_log (fl_app_none TS done e Hgts). }
      eexists. eapply (qcfg_step done e T ev ag2 cf
                 (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) LSilent);
        [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe.
      + rewrite Hstpost Hlogq.
        apply (PFSilent pstep pcls e.1 cf (WPAgent (pa_st ag)
                 (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅) st'
                 dnew);
          [done|]. simpl. exact Hpure.
    - (* ---- LLoad ---- *)
      have Hlat : lat = false.
      { destruct lat; [|done]. exfalso.
        by destruct (Hlf _ _ _ _ _ _ _ Hpure). }
      subst lat.
      destruct Hok as (Hro & Hf & Hts0).
      have Hgts : gev_ts TS e = None by rewrite /gev_ts Hgev /= Hts0.
      have Hlogq : pf_log TS (done ++ [e]) = pc_log cf.
      { by rewrite Hclog /pf_log (fl_app_none TS done e Hgts). }
      have Hmap : (pi TS (done ++ [e])) <$> tvs.*1 = (pi TS done) <$> tvs.*1.
      { apply list_fmap_ext. intros i t Hi.
        rewrite list_lookup_fmap in Hi.
        destruct (tvs !! i) as [[t' v]|] eqn:Htv; simplify_eq/=.
        apply (Hstab (base + Z.of_nat i)). exists (ae_lb ev).
        split; [by rewrite /gev_lb Hgev|].
        rewrite Hlbe /=. apply elem_of_tvs_reads. by exists i, v. }
      eexists. eapply (qcfg_step done e T ev ag2 cf
                 (load_post_run (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) aq base
                    ((tlabel_ts (pi TS done) tvs).*1))
                 (LLoad aq false base (tlabel_ts (pi TS done) tvs)));
        [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe tlabel_ts_fst Hmap.
      + rewrite Hstpost Hlogq.
        apply (PFLoad pstep pcls e.1 cf (WPAgent (pa_st ag)
                 (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅)
                 aq false base (tlabel_ts (pi TS done) tvs) st' dnew);
          [done| |].
        * simpl. eapply (proj1 Hobl (pa_st ag) (pc_dev cf) aq false base tvs);
            [by rewrite tlabel_ts_snd|]. exact Hpure.
        * simpl. rewrite Hcimg Hclog.
          eapply (read_ok_pf done e T ev ag (LLoad aq false base tvs) base tvs
                    false);
            [done|done|done|done|done|done|exact Hlbe|done|done|exact Hro|done].
    - (* ---- LStore ---- *)
      destruct Hok as (ts & kc & _ & Hlog & _ & Hf & Hts).
      have Hgts : gev_ts TS e = Some ts by rewrite /gev_ts Hgev /= Hts.
      have Hmsg : msg_at TS ts = WMsg base data (Some e.1) kc by apply msg_at_eq.
      have Hlogq : pf_log TS (done ++ [e])
                   = pc_log cf ++ [WMsg base data (Some e.1) kc].
      { by rewrite Hclog /pf_log (fl_app_some TS done e ts Hgts)
                   fmap_app /= Hmsg. }
      have Hpits : pi TS (done ++ [e]) ts = S (length (pc_log cf)).
      { rewrite Hclog fl_len. eapply pi_mem; [done|].
        rewrite (fl_app_some TS done e ts Hgts) lookup_app_r; [lia|].
        by rewrite Nat.sub_diag. }
      have Hnedata : data ≠ []
        by exact (Hdata (ts - 1)%nat (WMsg base data (Some e.1) kc) Hlog).
      eexists. eapply (qcfg_step done e T ev ag2 cf
                 (store_post_run (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) rl base (length data)
                    (S (length (pc_log cf))))
                 (LStore rl base data)); [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe Hts Hpits.
      + rewrite Hstpost Hlogq.
        apply (PFStore pstep pcls e.1 cf (WPAgent (pa_st ag)
                 (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅)
                 rl base data kc st' dnew); [done| |done|].
        * simpl. exact Hpure.
        * (* THE PINNED CLASS (G6a) *)
          have Hkc : kc = pcls (pa_st ag) (ae_lb ev) (pa_ws ag).
          { exact (Hcls e.1 T e.2 ev ag ts (WMsg base data (Some e.1) kc)
                     HT Hev Hag Hts Hlog). }
          simpl. rewrite Hkc Hlbe.
          apply (proj1 Hclsobl). by eapply replay_ws_relp.
    - (* ---- LRmw ---- *)
      destruct Hok as (ts & kc & Hlen & _ & Hlog & Hro & Hex & _ & Hf & Hts).
      have Hgts : gev_ts TS e = Some ts by rewrite /gev_ts Hgev /= Hts.
      have Hmsg : msg_at TS ts = WMsg base data (Some e.1) kc by apply msg_at_eq.
      have Hlogq : pf_log TS (done ++ [e])
                   = pc_log cf ++ [WMsg base data (Some e.1) kc].
      { by rewrite Hclog /pf_log (fl_app_some TS done e ts Hgts)
                   fmap_app /= Hmsg. }
      have Hpits : pi TS (done ++ [e]) ts = S (length (pc_log cf)).
      { rewrite Hclog fl_len. eapply pi_mem; [done|].
        rewrite (fl_app_some TS done e ts Hgts) lookup_app_r; [lia|].
        by rewrite Nat.sub_diag. }
      have Hnedata : data ≠ []
        by exact (Hdata (ts - 1)%nat (WMsg base data (Some e.1) kc) Hlog).
      have Hmap : (pi TS (done ++ [e])) <$> tvs.*1 = (pi TS done) <$> tvs.*1.
      { apply list_fmap_ext. intros i t Hi.
        rewrite list_lookup_fmap in Hi.
        destruct (tvs !! i) as [[t' v]|] eqn:Htv; simplify_eq/=.
        apply (Hstab (base + Z.of_nat i)). exists (ae_lb ev).
        split; [by rewrite /gev_lb Hgev|].
        rewrite Hlbe /=. apply elem_of_tvs_reads. by exists i, v. }
      eexists. eapply (qcfg_step done e T ev ag2 cf
                 (store_post_run
                    (load_post_run (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) aq base
                       ((tlabel_ts (pi TS done) tvs).*1))
                    rl base (length data) (S (length (pc_log cf))))
                 (LRmw aq rl base (tlabel_ts (pi TS done) tvs) data));
        [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe Hts tlabel_ts_fst Hmap Hpits.
      + rewrite Hstpost Hlogq.
        apply (PFRmw pstep pcls e.1 cf (WPAgent (pa_st ag)
                 (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅)
                 aq rl base (tlabel_ts (pi TS done) tvs) data kc st'
                 dnew);
          [done| |done| | | |].
        * simpl. eapply (proj2 Hobl (pa_st ag) (pc_dev cf) aq rl base tvs);
            [by rewrite tlabel_ts_snd|]. exact Hpure.
        * by rewrite tlabel_ts_length.
        * simpl. rewrite Hcimg Hclog.
          eapply (read_ok_pf done e T ev ag (LRmw aq rl base tvs data) base tvs
                    false);
            [done|done|done|done|done|done|exact Hlbe|done|done|exact Hro|done].
        * simpl. rewrite Hclog.
          eapply (excl_ok_pf done e T ev ag f aq rl base tvs data ts);
            [done|done|done|done|done|exact Hlbe|exact Hts|].
          by rewrite Hlbe.
        * (* THE PINNED CLASS (G6a) *)
          have Hkc : kc = pcls (pa_st ag) (ae_lb ev) (pa_ws ag).
          { exact (Hcls e.1 T e.2 ev ag ts (WMsg base data (Some e.1) kc)
                     HT Hev Hag Hts Hlog). }
          simpl. rewrite Hkc Hlbe.
          apply (proj2 Hclsobl); [by rewrite tlabel_ts_snd|].
          by eapply replay_ws_relp.
    - (* ---- LFence ---- *)
      destruct Hok as (Hf & Hts0).
      have Hgts : gev_ts TS e = None by rewrite /gev_ts Hgev /= Hts0.
      have Hlogq : pf_log TS (done ++ [e]) = pc_log cf.
      { by rewrite Hclog /pf_log (fl_app_none TS done e Hgts). }
      eexists. eapply (qcfg_step done e T ev ag2 cf
                 (fence_post (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) pr pw sr sw)
                 (LFence pr pw sr sw));
        [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe.
      + rewrite Hstpost Hlogq.
        apply (PFFence pstep pcls e.1 cf (WPAgent (pa_st ag)
                 (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅)
                 pr pw sr sw st' dnew); [done|].
        simpl. exact Hpure.
    - (* ---- LDev: the LSilent case verbatim, at [PFDev] ---- *)
      destruct Hok as (Hf & Hts0).
      have Hgts : gev_ts TS e = None by rewrite /gev_ts Hgev /= Hts0.
      have Hlogq : pf_log TS (done ++ [e]) = pc_log cf.
      { by rewrite Hclog /pf_log (fl_app_none TS done e Hgts). }
      eexists. eapply (qcfg_step done e T ev ag2 cf
                 (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) LDev);
        [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe.
      + rewrite Hstpost Hlogq.
        apply (PFDev pstep pcls e.1 cf (WPAgent (pa_st ag)
                 (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅) st'
                 dnew);
          [done|]. simpl. exact Hpure.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** The base case, and the induction *)

  Lemma Qinv_nil : Qinv [].
  Proof.
    split.
    - split_and!.
      + apply NoDup_nil_2.
      + intros e He. by apply elem_of_nil in He.
      + intros x Hx. by apply elem_of_nil in Hx.
      + intros n y Hn. by rewrite lookup_nil in Hn.
      + intros j k. split.
        * intros He. by apply elem_of_nil in He.
        * rewrite nproc_nil. intros [_ Hlt]. lia.
    - exists (wp_init img d0 ps). split_and!.
      + apply rtc_refl.
      + done.
      + done.
      + by rewrite /wp_init /= length_map.
      + intros j T HT.
        have Hatr : atrace_wf pstep (pt_img TS) (pt_log TS) j T by apply Hwf.
        destruct (atrace_first_is_Some pstep (pt_img TS) (pt_log TS) j T Hatr)
          as [ag0 Hag0].
        exists ag0. rewrite nproc_nil. split; [done|].
        rewrite /wp_init /= list_lookup_fmap (Hps0 j T ag0 HT Hag0) //.
      + apply qfab_init.
  Qed.

  (** THE SUBSET SIMULATION (design item (iv)): the invariant holds after
      processing the WHOLE of any downward-closed, sortable event subset.
      The minimal-bad-edge argument consumes exactly this form. *)
  Theorem sim_prefix (Ssub : gev → Prop) `{!∀ e, Decision (Ssub e)} :
    gdep3_acyclic TS DS → sub_ok TS (gdep3 TS DS) Ssub →
    ∃ order,
      Qinv order ∧
      NoDup order ∧
      (∀ e, e ∈ order ↔ (gev_wf TS e ∧ Ssub e)) ∧
      (∀ x y i j, order !! i = Some x → order !! j = Some y →
                  gdep3 TS DS x y → (i < j)%nat).
  Proof.
    intros Hacyc [Hdc _].
    apply (toposort_ind_S TS (gdep3 TS DS) Ssub Qinv Hacyc Hdc Qinv_nil).
    intros done e HQ Hwfe _ Hnin Hpre. by apply Qinv_step.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** THE FULL SIMULATION: the promise-free witness of a behavior *)

  Theorem sim_full (cend : wpcfg P D) :
    gdep3_acyclic TS DS →
    pt_img TS = pc_img cend →
    pt_log TS = pc_log cend →
    length (pc_ags cend) = length ps →
    (∀ j T, pt_trs TS !! j = Some T →
       at_ags T !! length (at_evs T) = pc_ags cend !! j) →
    ∃ cf, rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) cf ∧
          prog_of cf = prog_of cend ∧ (∀ a, mem_of cf a = mem_of cend a).
  Proof.
    intros Hacyc Himgc Hlogc Hlenc Hlast.
    destruct (toposort_ind_full TS (gdep3 TS DS) Qinv Hacyc Qinv_nil)
      as (order & HQ & Hnd & Hmemo & Hord).
    { intros done e HQ Hwfe Hnin Hpre. by apply Qinv_step. }
    destruct HQ as (Hq & cf & Hrun & Hcimg & Hclog & Hclen & Hcags & Hfab).
    exists cf. split; [done|].
    (* every agent's trace is fully processed *)
    have Hfulln : ∀ j T, pt_trs TS !! j = Some T →
                    nproc order j = length (at_evs T).
    { intros j T HT. destruct (Hcags j T HT) as (agn & Hagn & _).
      have Hlen2 : length (at_ags T) = S (length (at_evs T)).
      { eapply (asteps_wf_len pstep (pt_img TS) (pt_log TS) j). by apply Hwf. }
      have Hle : (nproc order j ≤ length (at_evs T))%nat.
      { have := lookup_lt_Some _ _ _ Hagn. lia. }
      destruct (decide (nproc order j = length (at_evs T))) as [Heq|Hne];
        [done|exfalso].
      have Hwfe : gev_wf TS (j, nproc order j).
      { apply gev_wf_bounds. exists T. simpl. split; [done|lia]. }
      have Hin : (j, nproc order j) ∈ order by apply Hmemo.
      apply (qorder_mem order j (nproc order j) Hq) in Hin as [_ Hcc]. lia. }
    split.
    - (* PROGRAM STATES *)
      rewrite /prog_of. apply list_eq. intros i. rewrite !list_lookup_fmap.
      destruct (decide (i < length ps)%nat) as [Hi|Hi].
      + have [T HT] : is_Some (pt_trs TS !! i)
          by apply lookup_lt_is_Some_2; lia.
        destruct (Hcags i T HT) as (agn & Hagn & Hlk).
        rewrite (Hfulln i T HT) (Hlast i T HT) in Hagn.
        by rewrite Hlk Hagn.
      + have H1 : pc_ags cf !! i = None by apply lookup_ge_None; lia.
        have H2 : pc_ags cend !! i = None by apply lookup_ge_None; lia.
        by rewrite H1 H2.
    - (* FINAL FLAT MEMORY *)
      intros a. rewrite /mem_of Hcimg Hclog -Himgc -Hlogc -Himg.
      destruct (latest_ts_writes (pt_log TS) a) as [Hz|(p & m & Hr & Hlk & Hs)].
      + (* nothing writes [a] at all, on either side *)
        have Hz' : latest_ts (pf_log TS order) a = 0%nat.
        { apply latest_ts_zero_iff. intros Hw.
          destruct (pf_writes_in_inv order a _ _ Hq Hw)
            as (that & ehat & _ & _ & _ & Hwb & _).
          apply (proj1 (latest_ts_zero_iff (pt_log TS) a) Hz).
          have Hpos : (0 < that)%nat by eapply writes_b_pos.
          destruct Hwb as (Hts & mm & Hmm & Hb).
          exists that. split_and!; [lia| |by exists mm].
          have := lookup_lt_Some _ _ _ Hmm. lia. }
        by rewrite Hz Hz' !log_byte_0.
      + (* the latest byte-[a] write maps to the pf log's latest *)
        have Hpos : (0 < latest_ts (pt_log TS) a)%nat by rewrite Hr; lia.
        have Hlk' : pt_log TS !! (latest_ts (pt_log TS) a - 1)%nat = Some m.
        { rewrite Hr. by replace (S p - 1)%nat with p by lia. }
        have Hmsg : msg_at TS (latest_ts (pt_log TS) a) = m by apply msg_at_eq.
        destruct (Hwfl (latest_ts (pt_log TS) a) m Hpos Hlk') as (em & Hem).
        have Hemin : em ∈ order by apply Hmemo; eapply gev_ts_wf.
        have Hwbm : writes_b TS a em (latest_ts (pt_log TS) a).
        { split; [done|]. by exists m. }
        have Hinfl : latest_ts (pt_log TS) a ∈ fl TS order.
        { apply elem_of_fl. by exists em. }
        destruct (pf_log_pi order _ Hq Hinfl) as (Hp1 & Hp2 & Hp3).
        have Hlat : latest (pt_img TS) (pf_log TS order) a
                      (pi TS order (latest_ts (pt_log TS) a)).
        { split.
          - rewrite (log_byte_pos (pt_img TS) (pf_log TS order) _
                       (msg_at TS (latest_ts (pt_log TS) a)) _ Hp1 Hp3) Hmsg.
            exact Hs.
          - intros Hw.
            destruct (pf_writes_in_inv order a _ _ Hq Hw)
              as (that & ehat & Hlo & Hhi & Hehat & Hwb & _).
            have Hthatpos : (0 < that)%nat by eapply writes_b_pos.
            have Hle : (that ≤ latest_ts (pt_log TS) a)%nat.
            { destruct (decide (that ≤ latest_ts (pt_log TS) a)%nat)
                as [Hle|Hgt]; [done|exfalso].
              apply (latest_ts_top (pt_log TS) a).
              destruct Hwb as (Hts & mm & Hmm & Hb).
              exists that. split_and!; [lia| |by exists mm].
              have := lookup_lt_Some _ _ _ Hmm. lia. }
            destruct (decide (that = latest_ts (pt_log TS) a)) as [->|Hne];
              [lia|].
            have := pi_lt_of_co order a ehat em that (latest_ts (pt_log TS) a)
                      Hq Hemin Hwb Hwbm ltac:(lia). lia. }
        rewrite (latest_ts_eq (pt_img TS) (pf_log TS order) a _ Hlat).
        rewrite (log_byte_pos (pt_img TS) (pf_log TS order) _
                   (msg_at TS (latest_ts (pt_log TS) a)) _ Hp1 Hp3) Hmsg.
        by rewrite (log_byte_pos (pt_img TS) (pt_log TS) _ m _ Hpos Hlk').
  Qed.

End sim.

(* ------------------------------------------------------------------ *)
(** ** The invariant's configuration half, as a standalone accessor

    [Qinv] is transparent, but the minimal-bad-edge consumer only ever
    wants the pf run and the per-agent picture; this is that projection. *)

Lemma Qinv_run {P D} (pstep : P → D → wlabel → P → D → Prop)
    (pcls : P → wlabel → wstate → wm_class) TS DS img d0 ps done :
  Qinv pstep pcls TS DS img d0 ps done →
  ∃ cf, rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) cf ∧
        pc_img cf = img ∧ pc_log cf = pf_log TS done ∧
        length (pc_ags cf) = length ps ∧
        (∀ j T, pt_trs TS !! j = Some T →
           ∃ agn, at_ags T !! nproc done j = Some agn ∧
             pc_ags cf !! j
             = Some (WPAgent (pa_st agn)
                       (aevs_post (pi TS done) (take (nproc done j) (at_evs T))
                          ws_init) ∅)) ∧
        qfab TS DS done (pc_dev cf).
Proof. intros [_ (cf & Hc)]. by exists cf. Qed.

Lemma Qinv_order {P D} (pstep : P → D → wlabel → P → D → Prop)
    (pcls : P → wlabel → wstate → wm_class) TS DS img d0 ps done :
  Qinv pstep pcls TS DS img d0 ps done → qorder TS done.
Proof. by intros [? _]. Qed.

(* ------------------------------------------------------------------ *)
(** ** LAYER 4: the behavior-level wrapper

    Everything the section context asks for that is not already a
    published theorem of a sibling file is discharged here from the
    PROMISE PHASE: the image, the agent count and the program states are
    frozen by it, and every logged message is authored with a nonempty
    payload. *)

Section wrapper.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pcls : P → wlabel → wstate → wm_class).
  Context (pdev : P → wlabel → P → bool).

  Implicit Types c : wpcfg P D.

  (** Every logged message carries a nonempty payload — the promise
      rule's [data ≠ []] as a run invariant (mirrors
      [WeakRobustGraph.log_authored]). *)
  Definition log_ne (log : list wmsg) : Prop :=
    ∀ p m, log !! p = Some m → wm_data m ≠ [].

  Lemma log_ne_init img d0 ps :
    log_ne (pc_log (wp_init (P:=P) (D:=D) img d0 ps)).
  Proof. intros p m Hp. by rewrite /wp_init /= lookup_nil in Hp. Qed.

  Lemma log_ne_promise_step c c' :
    log_ne (pc_log c) → wp_promise_step c c' → log_ne (pc_log c').
  Proof.
    intros Hne Hs.
    destruct (wp_promise_step_inv c c' Hs)
      as (j & agj & base & data & kc & _ & Hnn & ->).
    intros p m Hp. simpl in Hp.
    destruct (decide (p < length (pc_log c))%nat) as [Hlt|Hge].
    - rewrite lookup_app_l in Hp; [done|]. by eapply Hne.
    - have Hp' : p = length (pc_log c).
      { apply lookup_lt_Some in Hp. rewrite length_app /= in Hp. lia. }
      subst p. rewrite lookup_app_r in Hp; [lia|].
      rewrite Nat.sub_diag /= in Hp. by simplify_eq/=.
  Qed.

  Lemma log_ne_promise_run c c' :
    log_ne (pc_log c) → rtc (wp_promise_step (P:=P) (D:=D)) c c' → log_ne (pc_log c').
  Proof.
    intros H0 Hr. induction Hr as [|??? Hs _ IH]; [done|].
    apply IH. by eapply log_ne_promise_step.
  Qed.

  (** The promise phase freezes the image, the agent count and every
      program state. *)
  (** …and the FABRIC: no program moves in the promise phase, so it does
      not move either — which is what identifies the witness's [pd_init]
      with the run's own [d0]. *)
  Lemma promise_run_shape c c' :
    rtc (wp_promise_step (P:=P) (D:=D)) c c' →
    pc_img c' = pc_img c ∧ length (pc_ags c') = length (pc_ags c) ∧
    pc_dev c' = pc_dev c ∧
    (∀ i ag', pc_ags c' !! i = Some ag' →
       ∃ ag, pc_ags c !! i = Some ag ∧ pa_st ag' = pa_st ag).
  Proof.
    induction 1 as [c|c y z Hs Hr IH].
    - split_and!; [done|done|done|]. intros i ag' Hlk. by exists ag'.
    - destruct (wp_promise_step_inv c y Hs)
        as (j & agj & base & data & kc & Hlkj & _ & ->).
      destruct IH as (H1 & H2 & Hdv & H3).
      have Hjlt : (j < length (pc_ags c))%nat by eapply lookup_lt_Some.
      split_and!.
      + by rewrite H1.
      + by rewrite H2 /= length_insert.
      + by rewrite Hdv.
      + intros i ag' Hlk. destruct (H3 i ag' Hlk) as (agm & Hagm & Hst).
        simpl in Hagm. destruct (decide (i = j)) as [->|Hne].
        * rewrite list_lookup_insert in Hagm; [done|].
          injection Hagm as <-. exists agj. split; [done|]. by rewrite Hst.
        * rewrite list_lookup_insert_ne in Hagm; [done|]. by exists agm.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** THE BEHAVIOR-LEVEL SIMULATION (what W5 chains after
      [WeakRobustAcyc2]'s and [WeakRobustSer]'s behavior-level wrappers):
      a lat-free, timestamp-oblivious program whose traced behavior has an
      ACYCLIC extended dependency graph and SERIALIZED writes is matched
      by a promise-free run with the same program states and the same flat
      memory. *)
  (** THE FABRIC-CARRYING FORM (G4).  The extra premise is the same one
      as before with the DEVICE WITNESS in scope: for the [(mid, TS, DS)]
      the factorization produces, the FABRIC-ORDERED graph
      [gdep3 = gdep2 ∪ gdev] is acyclic and every byte's writes are
      serialized.  The replay then processes the fabric-touching events in
      witness order and hands each of them the fabric it recorded. *)
  (** THE CLASS PREMISES (G6a).  [wp_pf_run] pins the class of every
      message it appends, so the replay owes the pinned equation: [pcls]
      must be timestamp-blind ([pcls_obl]) and the behavior's own log must
      already carry the classes [pcls] computes ([cls_canonical], which
      [WeakRetag]'s retag establishes for any bundle).  They are SEPARATE
      premises, not part of the acyclicity bundle, because canonicity is
      discharged by the retag at the capstone and obliviousness by the
      concrete class function. *)
  Theorem wp_behavior_robust_dev img d0 ps c :
    pdev_ok pstep pdev →
    lat_free_prog pstep → ts_oblivious pstep →
    pcls_obl pcls →
    wp_behavior pstep img d0 ps c →
    (∀ mid TS DS,
       rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid →
       ptraces_dev_of pstep pdev TS DS mid c →
       gdep3_acyclic TS DS ∧ (∀ a, co_tc TS a)) →
    (∀ mid TS DS,
       rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid →
       ptraces_dev_of pstep pdev TS DS mid c →
       cls_canonical pcls TS) →
    ∃ cf, rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) cf ∧
          prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
  Proof.
    intros Hpok Hlf Hobl Hclsobl Hb Hprem Hpcan.
    destruct (wp_behavior_fulfil_once_dev pstep pdev img d0 ps c Hpok Hlf Hb)
      as (mid & TS & DS & Hprom & Hofd & Hnp & Hacct).
    have Hwit : ptraces_wit TS DS by eapply ptraces_dev_of_wit.
    have Hinit : pd_init DS = pc_dev mid by destruct Hofd as (_ & ? & _).
    destruct (Hprem mid TS DS Hprom Hofd) as (Hacyc & Hco).
    have Hcls : cls_canonical pcls TS by apply (Hpcan mid TS DS Hprom Hofd).
    destruct Hofd as (Hof & _).
    have Hwf : ptraces_wf pstep TS by eapply ptraces_of_wf.
    have Hla : log_authored (pc_log mid).
    { eapply log_authored_promise_run; [apply log_authored_init|exact Hprom]. }
    have Hwfl : writes_fulfilled TS
      by eapply (ptraces_of_writes_fulfilled pstep TS mid c).
    have Hlne : log_ne (pc_log mid).
    { eapply log_ne_promise_run; [apply log_ne_init|exact Hprom]. }
    have Hwsi : ptraces_ws_init TS.
    { eapply (ptraces_of_ws_init pstep TS mid c); [exact Hof|].
      eapply cfg_ws_init_promise_run; [apply cfg_ws_init_init|exact Hprom]. }
    destruct (promise_run_shape (wp_init img d0 ps) mid Hprom)
      as (Hpimg & Hplen & Hpdev & Hpst).
    have Hd01 : pd_init DS = d0 by rewrite Hinit Hpdev.
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
    eapply (sim_full pstep pcls pdev TS DS img d0 ps Hwf Hwsi Hco Hwfl Hlf Hobl
              Hcls Hclsobl Himg1 Hlen1 Hdata1 Hps1 Hwit Hd01 c Hacyc).
    - by rewrite Himg0 Hcimgc.
    - by rewrite Hlog0 Hclogc.
    - by rewrite Hclenc Hplen /wp_init /= length_map.
    - exact Hlst.
  Qed.

  (** THE DEV-FREE READING (the OLD [wp_behavior_robust], statement for
      statement): under a marker that never fires no event is
      fabric-touching, so there are no gdev edges, [gdep3] IS [gdep2] and
      the fabric never moves. *)
  Corollary wp_behavior_robust img d0 ps c :
    pdev_ok pstep pdev →
    (∀ p l p', pdev p l p' = false) →
    lat_free_prog pstep → ts_oblivious pstep →
    pcls_obl pcls →
    wp_behavior pstep img d0 ps c →
    (∀ mid TS,
       rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid →
       ptraces_of pstep TS mid c →
       gdep2_acyclic TS ∧ (∀ a, co_tc TS a)) →
    (∀ mid TS,
       rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid →
       ptraces_of pstep TS mid c →
       cls_canonical pcls TS) →
    ∃ cf, rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) cf ∧
          prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
  Proof.
    intros Hpok Hnodev Hlf Hobl Hclsobl Hb Hprem Hpcan.
    eapply (wp_behavior_robust_dev img d0 ps c Hpok Hlf Hobl Hclsobl Hb).
    - intros mid TS DS Hprom Hofd.
      have Hdf := ptraces_dev_of_free pstep pdev TS DS mid c Hnodev Hofd.
      have Hwit : ptraces_wit TS DS by eapply ptraces_dev_of_wit.
      destruct Hofd as (Hof & _).
      destruct (Hprem mid TS Hprom Hof) as (Hacyc & Hco).
      split; [|done]. by eapply gdep3_acyclic_devfree.
    - intros mid TS DS Hprom Hofd. destruct Hofd as (Hof & _).
      by apply (Hpcan mid TS Hprom Hof).
  Qed.

End wrapper.

(* ------------------------------------------------------------------ *)
(** ** What the rest of W2b/W5 inherits from this file

    - [ts_oblivious]: worklist finding (v), the ONE new premise the
      simulation forces on [pstep].  The Sail instantiation satisfies it
      trivially (a program sees values, never timestamps).

    - [sim_full]: the promise-free witness of a traced behavior — same
      per-agent program states, same flat memory — from [gdep3_acyclic]
      (the FABRIC-ORDERED graph; [WeakRobustOrd.gdep3_acyclic_devfree]
      derives it from [gdep2_acyclic] wherever the traces are dev-free,
      which is every current consumer), [co_tc] (owed by [WeakRobustSer]),
      [writes_fulfilled], [ptraces_wf]/[ptraces_ws_init] and the two
      promise-phase shape facts.  NO discipline premise is used: worklist
      finding (vi) is realized literally.

    - [wp_behavior_robust_dev]: the behavior-level packaging, whose extra
      premise is exactly "for the [(mid, TS, DS)] the factorization
      produces, the FABRIC-ORDERED graph is acyclic and every byte's
      writes are serialized" — the shape W5 chains the two sibling
      wrappers into.  [wp_behavior_robust] is its DEV-FREE reading
      (marker never fires ⇒ no gdev edges ⇒ [gdep3] is [gdep2]), the
      shape every current consumer takes.

    - [qdev] / [qfab] / [qfab_step]: the fabric half of the invariant.
      [qfab_step] is the only place a device event's replay fabric is
      identified with its recorded one; everything else in the file is
      fabric-blind (the read/excl cruxes and [ts_oblivious] are about
      TIMESTAMPS, which are orthogonal).

    - [sim_prefix] (+ [Qinv_run] / [Qinv_order]): the SUBSET form over any
      [sub_ok TS S], which is what design item (iv)'s minimal-bad-edge
      argument consumes — it needs a pf run of the ancestor closure of a
      candidate bad edge, not of the whole event set.  [Qinv] is
      transparent; [Qinv_run] projects out the pf run, the log identity
      [pc_log cf = pf_log TS done] and the per-agent trace-prefix picture.

    - [piL] / [pi] / [fl] / [pf_log] / [nproc]: the π machinery.  [pi] is
      [sigma_ok] ([pi_sigma_ok]) so [WeakRobustProv]'s transport theorems
      apply at it; [pi_app] is the stability that keeps already-built
      [wstate]s fixed as [done] grows ([aevs_post_ext] is the vehicle);
      [pi_lt_of_tc] / [pi_lt_of_co] are the two monotonicity facts every
      window argument is spent on.

    DELTAS FROM THE SPEC (all deliberate):

    - [pf_log done] is [msg_at <$> fl done] rather than an [omap] over
      [done] directly.  The two are equal on wf bundles, but the [fmap]
      spelling makes [pf_log done !! i] and [fl done !! i] move together
      by [list_lookup_fmap] — the log/timestamp correspondence is then
      definitional rather than an induction.

    - The invariant's order half ([qorder]) carries [Hpred] as the design
      note prescribes (predecessors occur EARLIER in [done]) plus [NoDup]
      and the per-agent prefix biconditional; [nproc_cur] derives "the
      event being processed is its agent's next one" from them, which is
      what makes the per-agent bookkeeping a one-liner at each step.

    - The read crux is factored as [read_ok_pf] and the rmw crux as
      [excl_ok_pf], both stated on the trace vocabulary alone; the five
      label arms of [Qinv_step] then differ only in which of them they
      call, and the configuration bookkeeping is shared in [qcfg_step]. *)
