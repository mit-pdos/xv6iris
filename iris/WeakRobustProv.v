(** * WeakRobustProv.v — VIEW PROVENANCE for the W2b simulation (M6 W2b (i))

    THE PROBLEM.  The W2b simulation replays a traced full-machine
    behavior as a PROMISE-FREE run whose log is a PERMUTATION π of the
    behavior's timestamps.  The pf agent's [wstate] is then the SAME
    per-event fold as the behavior's, with every leaf timestamp
    transported through π.  But π is not monotone, so
    [π (max S) ≠ max (π <$> S)]: no lemma of the form "the pf views are
    π of the behavior's views" can hold.

    THE FIX (this file).  For every [wstate] component, compute from the
    TRACE ALONE the LEAF SET of message timestamps that the component is
    the [max] of, and state the valuation lemma for an ARBITRARY
    transport [σ]:

      [lrel σ S w]  —  every component of [w] is [lval σ] (= max of
                       [σ] over the leaves) of the corresponding
                       component of the leaf state [S].

    [lrel] is preserved by every step function, with the mirror step on
    the leaf side and the σ-TRANSPORTED step on the [wstate] side
    ([lrel_aev_post], [lrel_aevs_post]).  σ = [id] recovers the
    behavior's own [wstate] (via [asteps_ws_fold], which shows the
    behavior's per-agent [wstate] IS the [id]-fold of its trace prefix);
    σ = π gives the promise-free run's.

    WHAT EACH SIDE CONDITION BUYS.  [Inj eq eq σ] is spent in EXACTLY ONE
    place, [lrel_fwd_view]: the [wstate] side decides the forward bank's
    hit/miss on [bool_decide (σ t = σ tf)] while the leaf mirror — whose
    leaves are RAW timestamps — decides it on [bool_decide (t = tf)];
    injectivity is what makes the two agree.  Everything else is
    structural.

    DELTAS FROM THE SPEC (all in the direction of a stronger/cleaner
    statement):

    - [lrel_init] needs NO hypothesis on σ at all.  [linit] has no
      leaves, and [lval σ [] = 0] definitionally, so [σ 0 = 0] is not
      used.  In fact [σ 0 = 0] is used NOWHERE in this file: since
      [aev_post] applies σ to the label's timestamps, a read of the
      era-initial image contributes the leaf [0] on the mirror side and
      [σ 0] on the [wstate] side, and the two match by construction.
      [sigma_ok] is kept as the packaged consumer-facing notion (W2b's π
      does fix 0, and the consumer needs that fact elsewhere) and is the
      hypothesis of the two top-level theorems; the per-step lemmas take
      the weaker [Inj eq eq σ].

    - [laevs_leaves_occur] needs no [t ≠ 0] side condition: [linit] is
      leaf-free, so EVERY leaf of [laevs_post evs linit] — including 0 —
      comes from an event of [evs].

    - The [coh] component of [lstate_leaf] is stated on [l_coh S !! a]
      rather than on [lcoh S a]; the two are interchangeable
      ([lcoh_leaf]) and the [lookup_insert_Some] form is what the step
      lemmas want.

    - The inner byte folds are related through [tats σ] (the
      address-preserving, timestamp-transporting map on the zipped
      access list) rather than by re-deriving the address list twice;
      [tats_run] is the one lemma that aligns the two [zip_with]s, and
      it is where [length_fmap] is spent.

    DEPENDENCY-FREE (stdpp only, no Iris, no Sail).  [WeakAxiomatic] is
    imported FIRST — exactly as [WeakRobustGraph] does — so that
    [WeakPromise]'s [wlabel] constructors shadow its [lbl] ones;
    [WeakRobustGraph] itself is imported only for [lb_reads] /
    [elem_of_tvs_reads], the vocabulary the provenance bound is stated
    in. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakRobustTrace
                            WeakRobustGraph.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** A. The σ-transported event fold *)

(** A label's read half with its timestamps transported. *)
Definition tlabel_ts (σ : nat → nat) (tvs : list (nat * bv 8))
    : list (nat * bv 8) := (λ tv, (σ tv.1, tv.2)) <$> tvs.

Lemma tlabel_ts_fst σ tvs : (tlabel_ts σ tvs).*1 = σ <$> tvs.*1.
Proof.
  rewrite /tlabel_ts -!list_fmap_compose //.
Qed.

(** ONE event's [wstate] update, with every leaf timestamp transported
    through σ.  The [None] arms of a store/rmw are junk (a wf trace
    never takes them — [astep_ok] forces [ae_ts] to be [Some] there). *)
Definition aev_post (σ : nat → nat) (ev : aev) (w : wstate) : wstate :=
  match ae_lb ev with
  | LSilent => w
  | LLoad aq lat base tvs => load_post_run w aq base (σ <$> tvs.*1)
  | LStore rl base data =>
      match ae_ts ev with
      | Some ts => store_post_run w rl base (length data) (σ ts)
      | None => w
      end
  | LRmw aq rl base tvs data =>
      match ae_ts ev with
      | Some ts =>
          store_post_run (load_post_run w aq base (σ <$> tvs.*1)) rl base
            (length data) (σ ts)
      | None => w
      end
  | LFence pr pw sr sw => fence_post w pr pw sr sw
  end.

Definition aevs_post (σ : nat → nat) (evs : list aev) (w : wstate) : wstate :=
  foldl (λ w ev, aev_post σ ev w) w evs.

Lemma aevs_post_nil σ w : aevs_post σ [] w = w.
Proof. done. Qed.

Lemma aevs_post_app σ evs ev w :
  aevs_post σ (evs ++ [ev]) w = aev_post σ ev (aevs_post σ evs w).
Proof. by rewrite /aevs_post foldl_app. Qed.

(* ------------------------------------------------------------------ *)
(** ** B. Behavior correspondence: the behavior's own [wstate] IS the
       [id]-fold of its trace prefix *)

Section fold.
  Context {P : Type}.
  Context (pstep : P → wlabel → P → Prop).

  (** [astep_ok] pins the step's [wstate] update to exactly [aev_post
      id] of the event. *)
  Lemma astep_ok_aev_post img log i (ag : wpagent P) ev f :
    astep_ok img log i ag (ae_lb ev) f (ae_ts ev) →
    ∀ w, f w = aev_post id ev w.
  Proof.
    destruct ev as [lb ts]. rewrite /aev_post /=.
    destruct lb as [|aq lat base tvs|rl base data|aq rl base tvs data|pr pw sr sw].
    - by intros [-> _] w.
    - intros (_ & -> & _) w. by rewrite list_fmap_id.
    - intros (ts' & _ & _ & _ & -> & ->) w. done.
    - intros (ts' & _ & _ & _ & _ & _ & _ & -> & ->) w.
      by rewrite list_fmap_id.
    - by intros [-> _] w.
  Qed.

  (** THE CORRESPONDENCE.  Every prefix of a wf trace folds the agent's
      [wstate] forward by [aev_post id]. *)
  Lemma asteps_ws_fold img log i ags evs k ag0 agk :
    asteps_wf pstep img log i ags evs →
    ags !! 0%nat = Some ag0 → ags !! k = Some agk →
    pa_ws agk = aevs_post id (take k evs) (pa_ws ag0).
  Proof.
    intros Hwf H0. revert agk.
    induction k as [|k IH]; intros agk Hk.
    { rewrite H0 in Hk. by simplify_eq. }
    have [ag Hag] : is_Some (ags !! k).
    { apply lookup_lt_is_Some_2. apply lookup_lt_Some in Hk. lia. }
    have [ev Hev] : is_Some (evs !! k).
    { apply lookup_lt_is_Some_2. destruct Hwf as [Hlen _].
      apply lookup_lt_Some in Hk. lia. }
    destruct (asteps_wf_step pstep img log i ags evs k ev Hwf Hev)
      as (agA & agB & st' & f & HagA & HagB & _ & Hok & Heq).
    assert (agA = ag) as -> by congruence.
    assert (agB = agk) as -> by congruence.
    rewrite (take_S_r _ _ _ Hev) aevs_post_app -(IH ag Hag) Heq /=.
    by apply (astep_ok_aev_post img log i ag ev f).
  Qed.

End fold.

Global Arguments astep_ok_aev_post {P} _ _ _ _ _ _.
Global Arguments asteps_ws_fold {P} _ _ _ _ _ _ _ _ _.

(* ------------------------------------------------------------------ *)
(** ** C. The leaf-state mirror

    Leaves are [list nat]; duplicates are harmless because every
    component is read off with a [max]. *)

Record lstate := LState {
  l_coh   : gmap Z (list nat);
  l_vrOld : list nat;
  l_vwOld : list nat;
  l_vrNew : list nat;
  l_vwNew : list nat;
  l_vRel  : list nat;
  l_fwd   : gmap Z (nat * list nat);  (* RAW store timestamp + view leaves *)
}.
Add Printing Constructor lstate.

(** The valuation of a leaf set under a transport σ. *)
Definition lval (σ : nat → nat) (L : list nat) : nat :=
  foldr (λ t n, Nat.max (σ t) n) 0%nat L.
Global Arguments lval : simpl never.

Definition lcoh (S : lstate) (a : Z) : list nat := default [] (l_coh S !! a).

Definition linit : lstate :=
  {| l_coh := ∅; l_vrOld := []; l_vwOld := []; l_vrNew := []; l_vwNew := [];
     l_vRel := []; l_fwd := ∅ |}.

(** *** Basic laws of [lval] *)

Lemma lval_nil σ : lval σ [] = 0%nat.
Proof. done. Qed.

Lemma lval_cons σ t L : lval σ (t :: L) = Nat.max (σ t) (lval σ L).
Proof. done. Qed.

Lemma lval_singleton σ t : lval σ [t] = σ t.
Proof. rewrite lval_cons lval_nil. lia. Qed.

Lemma lval_app σ L1 L2 : lval σ (L1 ++ L2) = Nat.max (lval σ L1) (lval σ L2).
Proof.
  induction L1 as [|t L1 IH]; [done|].
  rewrite -app_comm_cons !lval_cons IH. lia.
Qed.

Lemma lval_ge σ L t : t ∈ L → (σ t ≤ lval σ L)%nat.
Proof.
  induction L as [|u L IH]; [by intros ?%elem_of_nil|].
  intros [->|Hin]%elem_of_cons; rewrite lval_cons; [lia|].
  pose proof (IH Hin). lia.
Qed.

Lemma lval_le_iff σ L n : (lval σ L ≤ n)%nat ↔ ∀ t, t ∈ L → (σ t ≤ n)%nat.
Proof.
  induction L as [|u L IH].
  - rewrite lval_nil. split; [by intros _ t ?%elem_of_nil|intros _; lia].
  - rewrite lval_cons. destruct IH as [IH1 IH2]. split.
    + intros Hle t [->|Hin]%elem_of_cons; [lia|]. apply IH1; [lia|done].
    + intros Hall.
      have H1 : (σ u ≤ n)%nat by apply Hall, elem_of_list_here.
      have H2 : (lval σ L ≤ n)%nat.
      { apply IH2. intros t Ht. apply Hall. by apply elem_of_list_further. }
      lia.
Qed.

Lemma lval_lt σ L n :
  (∀ t, t ∈ L → (σ t < n)%nat) → (0 < n)%nat → (lval σ L < n)%nat.
Proof.
  intros Hall Hn.
  have Hle : (lval σ L ≤ n - 1)%nat.
  { apply lval_le_iff. intros t Ht. pose proof (Hall t Ht). lia. }
  lia.
Qed.

(** *** [lcoh] under an insert (mirrors [coh_upd_eq] / [coh_upd_ne]) *)

Lemma lcoh_ins_eq m rO wO rN wN R fwd a L :
  lcoh {| l_coh := <[a := L]> m; l_vrOld := rO; l_vwOld := wO;
          l_vrNew := rN; l_vwNew := wN; l_vRel := R; l_fwd := fwd |} a = L.
Proof. rewrite /lcoh /= lookup_insert //. Qed.

Lemma lcoh_ins_ne m rO wO rN wN R fwd a a' L :
  a' ≠ a →
  lcoh {| l_coh := <[a := L]> m; l_vrOld := rO; l_vwOld := wO;
          l_vrNew := rN; l_vwNew := wN; l_vRel := R; l_fwd := fwd |} a'
  = default [] (m !! a').
Proof. intros ?. rewrite /lcoh /= lookup_insert_ne //. Qed.

(** *** The mirrored step functions

    Structurally identical to [WeakMem]'s, with [max] ↦ [++] and each
    timestamp ↦ the singleton leaf list [[t]] — RAW, untransported. *)

Definition lload_vpre (S : lstate) (aq : bool) : list nat :=
  l_vrNew S ++ (if aq then l_vRel S else []).

(** THE FORWARD BANK, mirrored.  The hit/miss decision is taken on the
    RAW timestamps; [lrel_fwd_view] is where injectivity of σ makes that
    agree with the [wstate] side's decision on the transported ones. *)
Definition lfwd_view (S : lstate) (aq : bool) (a : Z) (t : nat) : list nat :=
  if aq then [t]
  else match l_fwd S !! a with
       | Some (tf, V) => if bool_decide (t = tf) then V else [t]
       | None => [t]
       end.

Definition lload_post_at (S : lstate) (aq : bool) (vpreL : list nat) (a : Z)
    (t : nat) : lstate :=
  let vpostL := vpreL ++ lfwd_view S aq a t in
  {| l_coh   := <[a := lcoh S a ++ (vpostL ++ [t])]> (l_coh S);
     l_vrOld := l_vrOld S ++ vpostL;
     l_vwOld := l_vwOld S;
     l_vrNew := if aq then l_vrNew S ++ vpostL else l_vrNew S;
     l_vwNew := if aq then l_vwNew S ++ vpostL else l_vwNew S;
     l_vRel  := l_vRel S;
     l_fwd   := l_fwd S |}.

Definition lstore_post (S : lstate) (rl : bool) (a : Z) (t : nat) : lstate :=
  {| l_coh   := <[a := lcoh S a ++ [t]]> (l_coh S);
     l_vrOld := l_vrOld S;
     l_vwOld := l_vwOld S ++ [t];
     l_vrNew := l_vrNew S;
     l_vwNew := l_vwNew S;
     l_vRel  := if rl then l_vRel S ++ [t] else l_vRel S;
     l_fwd   := <[a := (t, l_vwNew S)]> (l_fwd S) |}.

Definition lfence_post (S : lstate) (pr pw sr sw : bool) : lstate :=
  let v1L := (if pr then l_vrOld S else []) ++ (if pw then l_vwOld S else []) in
  {| l_coh   := l_coh S;
     l_vrOld := l_vrOld S;
     l_vwOld := l_vwOld S;
     l_vrNew := if sr then l_vrNew S ++ v1L else l_vrNew S;
     l_vwNew := if sw then l_vwNew S ++ v1L else l_vwNew S;
     l_vRel  := l_vRel S;
     l_fwd   := l_fwd S |}.

(** The multi-byte folds, mirroring [load_post_bytes] / [store_post_bytes]
    EXACTLY — including the compute-[vpre]-ONCE-from-the-PRE-state
    structure (the [lload_vpre] argument is the OUTER [S]'s). *)
Definition lload_post_bytes (S : lstate) (aq : bool) (ats : list (Z * nat))
    : lstate :=
  foldl (λ S' at_, lload_post_at S' aq (lload_vpre S aq) at_.1 at_.2) S ats.

Definition lstore_post_bytes (S : lstate) (rl : bool) (as_ : list Z) (t : nat)
    : lstate :=
  foldl (λ S' a, lstore_post S' rl a t) S as_.

Definition lload_post_run (S : lstate) (aq : bool) (base : Z) (ts : list nat)
    : lstate :=
  lload_post_bytes S aq
    (zip_with (λ j t, (base + Z.of_nat j, t)) (seq 0 (length ts)) ts).

Definition lstore_post_run (S : lstate) (rl : bool) (base : Z) (n : nat)
    (t : nat) : lstate :=
  lstore_post_bytes S rl (map (λ j : nat, base + Z.of_nat j) (seq 0 n)) t.

(** The event fold, mirrored.  No σ: leaves are raw. *)
Definition laev_post (ev : aev) (S : lstate) : lstate :=
  match ae_lb ev with
  | LSilent => S
  | LLoad aq lat base tvs => lload_post_run S aq base tvs.*1
  | LStore rl base data =>
      match ae_ts ev with
      | Some ts => lstore_post_run S rl base (length data) ts
      | None => S
      end
  | LRmw aq rl base tvs data =>
      match ae_ts ev with
      | Some ts =>
          lstore_post_run (lload_post_run S aq base tvs.*1) rl base
            (length data) ts
      | None => S
      end
  | LFence pr pw sr sw => lfence_post S pr pw sr sw
  end.

Definition laevs_post (evs : list aev) (S : lstate) : lstate :=
  foldl (λ S ev, laev_post ev S) S evs.

Lemma laevs_post_nil S : laevs_post [] S = S.
Proof. done. Qed.

Lemma laevs_post_app evs ev S :
  laevs_post (evs ++ [ev]) S = laev_post ev (laevs_post evs S).
Proof. by rewrite /laevs_post foldl_app. Qed.

(* ------------------------------------------------------------------ *)
(** ** D. The relation and the transport theorem *)

Definition sigma_ok (σ : nat → nat) : Prop := σ 0%nat = 0%nat ∧ Inj eq eq σ.

Lemma sigma_ok_id : sigma_ok id.
Proof. split; [done|apply _]. Qed.

Definition lrel (σ : nat → nat) (S : lstate) (w : wstate) : Prop :=
  (∀ a, coh w a = lval σ (lcoh S a)) ∧
  w_vrOld w = lval σ (l_vrOld S) ∧
  w_vwOld w = lval σ (l_vwOld S) ∧
  w_vrNew w = lval σ (l_vrNew S) ∧
  w_vwNew w = lval σ (l_vwNew S) ∧
  w_vRel w = lval σ (l_vRel S) ∧
  (∀ a, match l_fwd S !! a, w_fwd w !! a with
        | Some (tf, V), Some (tf', vf) => tf' = σ tf ∧ vf = lval σ V
        | None, None => True
        | _, _ => False
        end).

Lemma lrel_init σ : lrel σ linit ws_init.
Proof.
  rewrite /lrel /linit /ws_init /=. split_and!; try done.
  all: intros a; rewrite /coh /lcoh /= ?lookup_empty ?lval_nil //.
Qed.

(** THE ONE PLACE INJECTIVITY IS SPENT. *)
Lemma lrel_fwd_view σ S w aq a t :
  Inj eq eq σ → lrel σ S w →
  fwd_view w aq a (σ t) = lval σ (lfwd_view S aq a t).
Proof.
  intros Hinj (_ & _ & _ & _ & _ & _ & Hfwd).
  rewrite /fwd_view /lfwd_view. destruct aq; [by rewrite lval_singleton|].
  specialize (Hfwd a). revert Hfwd.
  destruct (l_fwd S !! a) as [[tf V]|], (w_fwd w !! a) as [[tf' vf]|];
    [|by intros []|by intros []|by intros _; rewrite lval_singleton].
  intros [-> ->]. case_bool_decide as H1; case_bool_decide as H2.
  - done.
  - destruct H2. by apply Hinj.
  - destruct H1. by f_equal.
  - by rewrite lval_singleton.
Qed.

Lemma lrel_load_vpre σ S w aq :
  lrel σ S w → load_vpre w aq = lval σ (lload_vpre S aq).
Proof.
  intros (_ & _ & _ & HrN & _ & HR & _).
  rewrite /load_vpre /lload_vpre lval_app HrN. destruct aq; [by rewrite HR|].
  by rewrite lval_nil.
Qed.

(** *** Preservation, step by step *)

Lemma lrel_load_post_at σ S w aq vpreL vpre a t :
  Inj eq eq σ → lrel σ S w → vpre = lval σ vpreL →
  lrel σ (lload_post_at S aq vpreL a t) (load_post_at w aq vpre a (σ t)).
Proof.
  intros Hinj Hrel Hvp.
  have Hfv : fwd_view w aq a (σ t) = lval σ (lfwd_view S aq a t)
    by apply lrel_fwd_view.
  destruct Hrel as (Hcoh & HrO & HwO & HrN & HwN & HR & Hfwd).
  rewrite /lrel /load_post_at /lload_post_at /=. split_and!.
  - intros a'. destruct (decide (a' = a)) as [->|Hne].
    + rewrite coh_upd_eq lcoh_ins_eq !lval_app lval_singleton Hvp Hfv (Hcoh a).
      lia.
    + rewrite coh_upd_ne // lcoh_ins_ne //. apply (Hcoh a').
  - rewrite !lval_app Hvp Hfv HrO. lia.
  - exact HwO.
  - destruct aq; [|exact HrN]. rewrite !lval_app Hvp Hfv HrN. lia.
  - destruct aq; [|exact HwN]. rewrite !lval_app Hvp Hfv HwN. lia.
  - exact HR.
  - exact Hfwd.
Qed.

Lemma lrel_store_post σ S w rl a t :
  lrel σ S w → lrel σ (lstore_post S rl a t) (store_post w rl a (σ t)).
Proof.
  intros (Hcoh & HrO & HwO & HrN & HwN & HR & Hfwd).
  rewrite /lrel /store_post /lstore_post /=. split_and!.
  - intros a'. destruct (decide (a' = a)) as [->|Hne].
    + rewrite coh_upd_eq lcoh_ins_eq lval_app lval_singleton -(Hcoh a). lia.
    + rewrite coh_upd_ne // lcoh_ins_ne //. apply (Hcoh a').
  - exact HrO.
  - by rewrite lval_app lval_singleton -HwO.
  - exact HrN.
  - exact HwN.
  - destruct rl; [by rewrite lval_app lval_singleton -HR|exact HR].
  - intros a'. destruct (decide (a' = a)) as [->|Hne].
    + rewrite !lookup_insert. by split.
    + rewrite !lookup_insert_ne //. apply (Hfwd a').
Qed.

Lemma lrel_fence_post σ S w pr pw sr sw :
  lrel σ S w → lrel σ (lfence_post S pr pw sr sw) (fence_post w pr pw sr sw).
Proof.
  intros (Hcoh & HrO & HwO & HrN & HwN & HR & Hfwd).
  have Hv1 : Nat.max (if pr then w_vrOld w else 0%nat)
                     (if pw then w_vwOld w else 0%nat)
             = lval σ ((if pr then l_vrOld S else []) ++
                       (if pw then l_vwOld S else [])).
  { rewrite lval_app. destruct pr, pw; by rewrite ?lval_nil -?HrO -?HwO. }
  rewrite /lrel /fence_post /lfence_post /=. split_and!.
  - exact Hcoh.
  - exact HrO.
  - exact HwO.
  - destruct sr; [by rewrite lval_app -Hv1 -HrN|exact HrN].
  - destruct sw; [by rewrite lval_app -Hv1 -HwN|exact HwN].
  - exact HR.
  - exact Hfwd.
Qed.

(** *** Preservation through the byte folds

    The [wstate] fold runs over the SAME address list with TRANSPORTED
    timestamps; [tats] is that map, and [tats_run] is what aligns the
    two contiguous-run [zip_with]s (this is where [length_fmap] is
    spent). *)

Definition tats (σ : nat → nat) (ats : list (Z * nat)) : list (Z * nat) :=
  (λ p, (p.1, σ p.2)) <$> ats.

Local Lemma fmap_zip_with_gen {A B C D} (f : A → B → C) (g : C → D) l k :
  g <$> zip_with f l k = zip_with (λ x y, g (f x y)) l k.
Proof.
  revert k. by induction l; intros [|??]; f_equal/=.
Qed.

Lemma tats_run σ base ts :
  tats σ (zip_with (λ (j : nat) (t : nat), (base + Z.of_nat j, t))
            (seq 0 (length ts)) ts)
  = zip_with (λ (j : nat) (t : nat), (base + Z.of_nat j, t))
      (seq 0 (length (σ <$> ts))) (σ <$> ts).
Proof. by rewrite length_fmap zip_with_fmap_r /tats fmap_zip_with_gen. Qed.

(** The pre-view is computed ONCE from the pre-state, so the inner
    induction must carry "[vpre] = [lval σ vpreL]" as its own premise —
    the intermediate states change but the pre-view does not. *)
Lemma lrel_load_fold σ aq vpre vpreL ats :
  Inj eq eq σ →
  ∀ S w, lrel σ S w → vpre = lval σ vpreL →
    lrel σ (foldl (λ S' at_, lload_post_at S' aq vpreL at_.1 at_.2) S ats)
           (foldl (λ w' at_, load_post_at w' aq vpre at_.1 at_.2) w
              (tats σ ats)).
Proof.
  intros Hinj. induction ats as [|p ats IH]; intros S w Hrel Hvp; [done|].
  rewrite /tats /= -/(tats σ ats). apply IH; [|done].
  by apply lrel_load_post_at.
Qed.

Lemma lrel_load_post_run σ S w aq base ts :
  Inj eq eq σ → lrel σ S w →
  lrel σ (lload_post_run S aq base ts) (load_post_run w aq base (σ <$> ts)).
Proof.
  intros Hinj Hrel.
  rewrite /lload_post_run /load_post_run /lload_post_bytes /load_post_bytes
          -tats_run.
  apply lrel_load_fold; [done|done|by apply lrel_load_vpre].
Qed.

Lemma lrel_store_fold σ rl t as_ :
  ∀ S w, lrel σ S w →
    lrel σ (foldl (λ S' a, lstore_post S' rl a t) S as_)
           (foldl (λ w' a, store_post w' rl a (σ t)) w as_).
Proof.
  induction as_ as [|a as_ IH]; intros S w Hrel; [done|].
  rewrite /=. apply IH. by apply lrel_store_post.
Qed.

Lemma lrel_store_post_run σ S w rl base n t :
  lrel σ S w →
  lrel σ (lstore_post_run S rl base n t) (store_post_run w rl base n (σ t)).
Proof.
  intros Hrel. rewrite /lstore_post_run /store_post_run /lstore_post_bytes
                       /store_post_bytes.
  by apply lrel_store_fold.
Qed.

(** *** THE TRANSPORT THEOREMS *)

Theorem lrel_aev_post σ ev S w :
  sigma_ok σ → lrel σ S w → lrel σ (laev_post ev S) (aev_post σ ev w).
Proof.
  intros [_ Hinj] Hrel. destruct ev as [lb ts]. rewrite /laev_post /aev_post /=.
  destruct lb as [|aq lat base tvs|rl base data|aq rl base tvs data|pr pw sr sw].
  - exact Hrel.
  - by apply lrel_load_post_run.
  - destruct ts as [t|]; [|exact Hrel]. by apply lrel_store_post_run.
  - destruct ts as [t|]; [|exact Hrel].
    apply lrel_store_post_run. by apply lrel_load_post_run.
  - by apply lrel_fence_post.
Qed.

Theorem lrel_aevs_post σ evs S w :
  sigma_ok σ → lrel σ S w → lrel σ (laevs_post evs S) (aevs_post σ evs w).
Proof.
  intros Hσ. revert S w. induction evs as [|ev evs IH]; intros S w Hrel; [done|].
  rewrite /laevs_post /aevs_post /=. apply IH. by apply lrel_aev_post.
Qed.

(** The two instances the simulation reads off: the behavior's own
    [wstate] fold (σ = [id]) and the promise-free run's (σ = π). *)
Corollary lrel_aevs_post_init σ evs :
  sigma_ok σ → lrel σ (laevs_post evs linit) (aevs_post σ evs ws_init).
Proof. intros Hσ. apply lrel_aevs_post; [done|apply lrel_init]. Qed.

Corollary lrel_aevs_post_id evs :
  lrel id (laevs_post evs linit) (aevs_post id evs ws_init).
Proof. apply lrel_aevs_post_init, sigma_ok_id. Qed.

(* ------------------------------------------------------------------ *)
(** ** E. Leaf provenance: every leaf comes from an event *)

(** [t] occurs in [ev] — either as a timestamp the label reads, or as
    the timestamp the event fulfils. *)
Definition aev_ts_occurs (ev : aev) (t : nat) : Prop :=
  (∃ a, (a, t) ∈ lb_reads (ae_lb ev)) ∨ ae_ts ev = Some t.

Definition ev_ts_occurs (evs : list aev) (t : nat) : Prop :=
  ∃ ev, ev ∈ evs ∧ aev_ts_occurs ev t.

Lemma ev_ts_occurs_cons ev evs t :
  aev_ts_occurs ev t ∨ ev_ts_occurs evs t → ev_ts_occurs (ev :: evs) t.
Proof.
  intros [H|(e & He & H)].
  - exists ev. split; [apply elem_of_list_here|done].
  - exists e. split; [by apply elem_of_list_further|done].
Qed.

(** [t] is a leaf of [S]: it occurs in some component list, some [coh]
    entry, or some forward-bank entry (as the raw store timestamp or in
    the banked view). *)
Definition lstate_leaf (S : lstate) (t : nat) : Prop :=
  t ∈ l_vrOld S ∨ t ∈ l_vwOld S ∨ t ∈ l_vrNew S ∨ t ∈ l_vwNew S ∨
  t ∈ l_vRel S ∨
  (∃ a L, l_coh S !! a = Some L ∧ t ∈ L) ∨
  (∃ a tf V, l_fwd S !! a = Some (tf, V) ∧ (t = tf ∨ t ∈ V)).

Lemma lcoh_leaf S a t : t ∈ lcoh S a → lstate_leaf S t.
Proof.
  rewrite /lcoh. destruct (l_coh S !! a) as [L|] eqn:HL; [|by intros ?%elem_of_nil].
  intros Ht. rewrite /lstate_leaf. naive_solver.
Qed.

Lemma linit_no_leaf t : ¬ lstate_leaf linit t.
Proof.
  rewrite /lstate_leaf /linit /=.
  intros [H|[H|[H|[H|[H|[(a & L & H & _)|(a & tf & V & H & _)]]]]]];
    try (by apply elem_of_nil in H); by rewrite lookup_empty in H.
Qed.

Lemma lload_vpre_leaf S aq t : t ∈ lload_vpre S aq → lstate_leaf S t.
Proof.
  rewrite /lload_vpre /lstate_leaf. intros [H|H]%elem_of_app; [naive_solver|].
  destruct aq; [naive_solver|by apply elem_of_nil in H].
Qed.

Lemma lfwd_view_leaf S aq a t u :
  u ∈ lfwd_view S aq a t → lstate_leaf S u ∨ u = t.
Proof.
  rewrite /lfwd_view. destruct aq; [by intros ->%elem_of_list_singleton; right|].
  destruct (l_fwd S !! a) as [[tf V]|] eqn:HS;
    [|by intros ->%elem_of_list_singleton; right].
  case_bool_decide as Ht; [|by intros ->%elem_of_list_singleton; right].
  intros Hu. left. rewrite /lstate_leaf. naive_solver.
Qed.

Lemma lload_post_at_leaf S aq vpreL a t u :
  lstate_leaf (lload_post_at S aq vpreL a t) u →
  lstate_leaf S u ∨ u ∈ vpreL ∨ u = t.
Proof.
  have Hpost : ∀ v, v ∈ vpreL ++ lfwd_view S aq a t →
                    lstate_leaf S v ∨ v ∈ vpreL ∨ v = t.
  { intros v [Hv|Hv]%elem_of_app; [by right; left|].
    by destruct (lfwd_view_leaf S aq a t v Hv) as [Hl|Hl]; auto. }
  rewrite {1}/lstate_leaf /lload_post_at /=.
  intros [H|[H|[H|[H|[H|[(a' & L & HL & H)|(a' & tf & V & HL & H)]]]]]].
  - apply elem_of_app in H as [H|H]; [|by apply Hpost].
    left. rewrite /lstate_leaf. naive_solver.
  - left. rewrite /lstate_leaf. naive_solver.
  - destruct aq; [|left; rewrite /lstate_leaf; naive_solver].
    apply elem_of_app in H as [H|H]; [|by apply Hpost].
    left. rewrite /lstate_leaf. naive_solver.
  - destruct aq; [|left; rewrite /lstate_leaf; naive_solver].
    apply elem_of_app in H as [H|H]; [|by apply Hpost].
    left. rewrite /lstate_leaf. naive_solver.
  - left. rewrite /lstate_leaf. naive_solver.
  - apply lookup_insert_Some in HL as [[-> <-]|[Hne HL]].
    + apply elem_of_app in H as [H|H]; [by left; eapply lcoh_leaf|].
      apply elem_of_app in H as [H|H]; [by apply Hpost|].
      by apply elem_of_list_singleton in H; right; right.
    + left. rewrite /lstate_leaf. naive_solver.
  - left. rewrite /lstate_leaf. naive_solver.
Qed.

Lemma lstore_post_leaf S rl a t u :
  lstate_leaf (lstore_post S rl a t) u → lstate_leaf S u ∨ u = t.
Proof.
  rewrite {1}/lstate_leaf /lstore_post /=.
  intros [H|[H|[H|[H|[H|[(a' & L & HL & H)|(a' & tf & V & HL & H)]]]]]];
    try (left; rewrite /lstate_leaf; naive_solver).
  - apply elem_of_app in H as [H|H]; [left; rewrite /lstate_leaf; naive_solver|].
    by apply elem_of_list_singleton in H; right.
  - destruct rl; [|left; rewrite /lstate_leaf; naive_solver].
    apply elem_of_app in H as [H|H]; [left; rewrite /lstate_leaf; naive_solver|].
    by apply elem_of_list_singleton in H; right.
  - apply lookup_insert_Some in HL as [[-> <-]|[Hne HL]].
    + apply elem_of_app in H as [H|H]; [by left; eapply lcoh_leaf|].
      by apply elem_of_list_singleton in H; right.
    + left. rewrite /lstate_leaf. naive_solver.
  - apply lookup_insert_Some in HL as [[-> [= <- <-]]|[Hne HL]].
    + destruct H as [->|H]; [by right|]. left. rewrite /lstate_leaf. naive_solver.
    + left. rewrite /lstate_leaf. naive_solver.
Qed.

Lemma lfence_post_leaf S pr pw sr sw u :
  lstate_leaf (lfence_post S pr pw sr sw) u → lstate_leaf S u.
Proof.
  have Hv1 : ∀ v, v ∈ (if pr then l_vrOld S else []) ++
                       (if pw then l_vwOld S else []) → lstate_leaf S v.
  { intros v [Hv|Hv]%elem_of_app.
    - destruct pr; [rewrite /lstate_leaf; naive_solver|by apply elem_of_nil in Hv].
    - destruct pw; [rewrite /lstate_leaf; naive_solver|by apply elem_of_nil in Hv]. }
  rewrite {1}/lstate_leaf /lfence_post /=.
  intros [H|[H|[H|[H|[H|[(a' & L & HL & H)|(a' & tf & V & HL & H)]]]]]];
    try (rewrite /lstate_leaf; naive_solver).
  - destruct sr; [|rewrite /lstate_leaf; naive_solver].
    apply elem_of_app in H as [H|H]; [rewrite /lstate_leaf; naive_solver|by apply Hv1].
  - destruct sw; [|rewrite /lstate_leaf; naive_solver].
    apply elem_of_app in H as [H|H]; [rewrite /lstate_leaf; naive_solver|by apply Hv1].
Qed.

Lemma lload_fold_leaf aq vpreL ats :
  ∀ S u,
    lstate_leaf (foldl (λ S' at_, lload_post_at S' aq vpreL at_.1 at_.2) S ats) u →
    lstate_leaf S u ∨ u ∈ vpreL ∨ ∃ p, p ∈ ats ∧ u = p.2.
Proof.
  induction ats as [|p ats IH]; intros S u Hu; [by left|].
  rewrite /= in Hu. apply IH in Hu as [Hu|[Hu|(q & Hq & ->)]].
  - apply lload_post_at_leaf in Hu as [Hu|[Hu|Heq]]; [| |subst u].
    + by left.
    + by right; left.
    + right; right. exists p. split; [apply elem_of_list_here|done].
  - by right; left.
  - right; right. exists q. split; [by apply elem_of_list_further|done].
Qed.

Lemma lload_post_bytes_leaf S aq ats u :
  lstate_leaf (lload_post_bytes S aq ats) u →
  lstate_leaf S u ∨ ∃ p, p ∈ ats ∧ u = p.2.
Proof.
  rewrite /lload_post_bytes.
  intros [Hu|[Hu|Hu]]%lload_fold_leaf; [by left| |by right].
  left. by eapply lload_vpre_leaf.
Qed.

Lemma lstore_fold_leaf rl t as_ :
  ∀ S u,
    lstate_leaf (foldl (λ S' a, lstore_post S' rl a t) S as_) u →
    lstate_leaf S u ∨ u = t.
Proof.
  induction as_ as [|a as_ IH]; intros S u Hu; [by left|].
  rewrite /= in Hu. apply IH in Hu as [Hu|Heq]; [|by right].
  by apply lstore_post_leaf in Hu.
Qed.

Lemma lstore_post_run_leaf S rl base n t u :
  lstate_leaf (lstore_post_run S rl base n t) u → lstate_leaf S u ∨ u = t.
Proof.
  rewrite /lstore_post_run /lstore_post_bytes. apply lstore_fold_leaf.
Qed.

(** The contiguous-run access list only ever carries timestamps that are
    IN the run's timestamp list. *)
Lemma run_ats_ts base ts p :
  p ∈ zip_with (λ (j : nat) (t : nat), (base + Z.of_nat j, t))
        (seq 0 (length ts)) ts →
  ∃ j, ts !! j = Some p.2.
Proof.
  intros Hp. apply elem_of_lookup_zip_with_1 in Hp as (i & x & y & Hpe & _ & Hy).
  exists i. by rewrite Hpe /=.
Qed.

Lemma lload_post_run_leaf S aq base ts u :
  lstate_leaf (lload_post_run S aq base ts) u →
  lstate_leaf S u ∨ ∃ j, ts !! j = Some u.
Proof.
  rewrite /lload_post_run.
  intros [Hu|(p & Hp & ->)]%lload_post_bytes_leaf; [by left|].
  right. exact (run_ats_ts base ts p Hp).
Qed.

(** A timestamp read by byte [j] of a load/rmw label IS one of the
    label's reads. *)
Lemma tvs_fst_reads base (tvs : list (nat * bv 8)) j u :
  tvs.*1 !! j = Some u → ∃ a, (a, u) ∈ tvs_reads base tvs.
Proof.
  rewrite list_lookup_fmap. destruct (tvs !! j) as [[t v]|] eqn:Hj; [|done].
  intros [= <-]. exists (base + Z.of_nat j).
  apply elem_of_tvs_reads. by exists j, v.
Qed.

Lemma laev_post_leaf ev S u :
  lstate_leaf (laev_post ev S) u → lstate_leaf S u ∨ aev_ts_occurs ev u.
Proof.
  destruct ev as [lb ts]. rewrite /laev_post /aev_ts_occurs /=.
  destruct lb as [|aq lat base tvs|rl base data|aq rl base tvs data|pr pw sr sw].
  - by left.
  - intros [Hu|(j & Hj)]%lload_post_run_leaf; [by left|].
    right; left. by eapply tvs_fst_reads.
  - destruct ts as [t|]; [|by left].
    intros [Hu|Heq]%lstore_post_run_leaf; [by left|]. subst u. by right; right.
  - destruct ts as [t|]; [|by left].
    intros [Hu|Heq]%lstore_post_run_leaf; [|subst u; by right; right].
    apply lload_post_run_leaf in Hu as [Hu|(j & Hj)]; [by left|].
    right; left. by eapply tvs_fst_reads.
  - intros Hu%lfence_post_leaf. by left.
Qed.

Lemma laevs_post_leaf evs :
  ∀ S u, lstate_leaf (laevs_post evs S) u →
         lstate_leaf S u ∨ ev_ts_occurs evs u.
Proof.
  induction evs as [|ev evs IH]; intros S u Hu; [by left|].
  rewrite /laevs_post /= in Hu. apply IH in Hu as [Hu|Hu].
  - apply laev_post_leaf in Hu as [Hu|Hu]; [by left|].
    right. by apply ev_ts_occurs_cons; left.
  - right. by apply ev_ts_occurs_cons; right.
Qed.

(** THE PROVENANCE BOUND: every leaf of the whole fold from [linit] is a
    timestamp some event of the trace read or fulfilled. *)
Theorem laevs_leaves_occur evs t :
  lstate_leaf (laevs_post evs linit) t → ev_ts_occurs evs t.
Proof.
  intros [Ht|Ht]%laevs_post_leaf; [|done]. by destruct (linit_no_leaf t).
Qed.

(* ------------------------------------------------------------------ *)
(** ** F. What the consumer reads off *)

(** The READ FLOOR of an access: [max (load_vpre, coh a)], as a leaf
    set.  This is the [F] of the W2b design's E-edges. *)
Definition lfloor (S : lstate) (aq : bool) (a : Z) : list nat :=
  lload_vpre S aq ++ lcoh S a.

Lemma lrel_floor σ S w aq a :
  lrel σ S w → Nat.max (load_vpre w aq) (coh w a) = lval σ (lfloor S aq a).
Proof.
  intros Hrel. rewrite /lfloor lval_app -(lrel_load_vpre σ S w aq Hrel).
  destruct Hrel as (Hcoh & _). by rewrite -(Hcoh a).
Qed.

(* ------------------------------------------------------------------ *)
(** ** What W2b inherits

    - [asteps_ws_fold]: a wf trace's [k]-th agent record carries exactly
      [aevs_post id (take k evs)] of the initial [wstate].  So the
      behavior's own views ARE the [id]-instance of the fold.

    - [lrel_aevs_post] (+ [lrel_aevs_post_init]): the SAME leaf state
      [laevs_post evs linit] valuates, under ANY [sigma_ok] σ, to
      [aevs_post σ evs ws_init].  Instantiating at σ = [id] and at σ = π
      gives the behavior's and the promise-free run's views as two
      valuations of ONE leaf state — which is what makes a floor
      comparison across the two runs a statement about π on leaves
      rather than about π on maxima.

    - [lrel_floor] + [lfloor]: the read floor [max (load_vpre, coh a)]
      is [lval σ] of a leaf list computable from the trace; with
      [lval_le_iff] / [lval_lt] / [lval_ge] a floor bound is exactly a
      pointwise bound on σ of the leaves.  That is the form the E-edge
      construction of the revised W2b design ("an edge from every leaf
      [t*] of [r]'s floor to every byte-[a] write above it") consumes.

    - [laevs_leaves_occur]: every leaf is a timestamp SOME event of the
      trace read or fulfilled, so an E-edge's source is always a
      graph node — the well-definedness the extended graph needs. *)
