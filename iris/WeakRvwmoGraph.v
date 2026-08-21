(** * WeakRvwmoGraph.v — RVWMO⁻, the tier-2 declared model (T2-1, slice 1)

    Design: [claude-notes/design/weak-memory-tier2-s6.md] §1 (F1/F2 and the
    F2 realizability caveat); worklist: the certification project file's
    T2 staging.

    THE POINT.  Tier 2's declared model must express EARLY STORES, and the
    [cand] presentation provably cannot (its gmo IS trace order —
    [WeakSrvwmoLitmus.lb_values_forbidden] is the machine-checked witness).
    This file is the herd-style presentation: per-agent label lists (po =
    position), and the GLOBAL MEMORY ORDER as DATA — a list [gx_gmo] of the
    memory events — so a store may sit gmo-before its own po-earlier reads.

    THE ENCODING TRICK that keeps the two presentations aligned: the fused
    label alphabet [WeakAxiomatic.lbl] is reused UNCHANGED, with a read's
    per-byte [ts] entries reinterpreted as GMO-WRITE-INDICES (0 = the
    era-initial image; [t > 0] names the [t]-th write in [gx_gmo]).  In a
    [cand], [ts] entries are log positions and the log is the trace's
    writes in trace order — i.e. exactly the same convention — so the
    [cand → graph] embedding ([graph_of_cand]) is the IDENTITY on labels
    and programs, with [gx_gmo] the trace's memory events in trace order.

    THE MODEL (RVWMO⁻ = RVWMO minus ppo rules 6 and 9–13, per S6 F2):
    the herd-standard axiom set —

      - [gwf]            shapes + gmo well-formedness (the order is data);
      - [gppo_gmo]       ppo⁻ ⊆ gmo, where ppo⁻ keeps rules 1–3 (same-byte
                         program order), 4 (fences), 5 (acquires) and
                         7 (RCsc pairs) ONLY — no rule 14, no dependency
                         rules;
      - [gload_value]    a read names a same-byte write that is (gmo ∪ po)-
                         before it and co-maximal among such (the po
                         disjunct is store forwarding — legal here, unlike
                         in [cand]);
      - [gatomicity]     no same-byte write co-between a fused RMW's read
                         source and the RMW itself.

    Dropping ppo rules only ADDS behaviors, so a safety theorem against
    RVWMO⁻ covers RVWMO.  THE DEFERRED PIECE (recorded, not lost): the F2
    CAVEAT's store-side dependency fragment — the realizability direction
    (graph → machine) will need dep edges as graph DATA ([gx_deps], edges
    into stores ⊆ gmo) because the machine's D2/D3 EXT floors enforce
    them; it lands with that direction, not here, because adding
    constraints only SHRINKS the declared model's behavior set toward
    RVWMO and never invalidates this slice's theorems.

    THIS SLICE delivers: the presentation; the model; the embedding
    [graph_of_cand] (definition only — its well-formedness and
    consistency transfer are T2-1b's contract); and the
    NON-COLLAPSE WITNESS [lb_graph_consistent] — the four-event LB
    execution is RVWMO⁻-consistent, i.e. the declared model genuinely
    admits what sRVWMO forbids ([WeakSrvwmoLitmus.lb_forbidden_model]),
    so tier 2 is about a real gap.  The two translation THEOREMS
    (consistency transfer along the embedding; the rule-14 linearization
    graph → cand) are the next slices (T2-1b/T2-1c; the linearization is
    the A3(v) shape: a linear extension of po ∪ gmo|W ∪ rf, acyclic via
    rule 14's contraction argument).

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakLitmus WeakAxiomatic WeakAxiomatic2.

(* ====================================================================== *)
(** * 1. The presentation *)

(** An event id: (agent, position in the agent's program). *)
Notation geid := (agent * nat)%type.

Record gexec := GExec {
  gx_img  : image;
  gx_prog : list (list lbl);
  gx_gmo  : list geid;
}.

Definition gx_lbl (G : gexec) (e : geid) : option lbl :=
  gx_prog G !! e.1 ≫= (λ p, p !! e.2).

(** Memory events: reads and writes.  Fences are program events but not
    memory events — they are not in gmo (riscv.cat's [gmo] ranges over
    memory accesses). *)
Definition lb_is_mem (l : lbl) : bool := lb_is_r l || lb_is_w l.

Definition gmem (G : gexec) (e : geid) : Prop :=
  ∃ l, gx_lbl G e = Some l ∧ lb_is_mem l = true.

(** gmo POSITION (junk off the order; guarded by membership). *)
Definition gpos (G : gexec) (e : geid) : nat :=
  match list_find (λ e', e' = e) (gx_gmo G) with
  | Some (i, _) => i
  | None => 0%nat
  end.

Definition gmo_lt (G : gexec) (e1 e2 : geid) : Prop :=
  e1 ∈ gx_gmo G ∧ e2 ∈ gx_gmo G ∧ (gpos G e1 < gpos G e2)%nat.

(** The WRITE SUB-ORDER and write indices.  [gwrites G] enumerates the
    write events in gmo order; a read's per-byte [ts] entry [t > 0] names
    [gwrites G !! (t - 1)]; [t = 0] names the era-initial image. *)
Definition gis_w (G : gexec) (e : geid) : bool :=
  match gx_lbl G e with Some l => lb_is_w l | None => false end.

Definition gwrites (G : gexec) : list geid := filter (gis_w G) (gx_gmo G).

Definition gwrite_at (G : gexec) (t : nat) : option geid :=
  match t with 0%nat => None | S i => gwrites G !! i end.

(** The write index of a write event (1-based; 0 is the image). *)
Definition gwix (G : gexec) (e : geid) : nat :=
  match list_find (λ e', e' = e) (gwrites G) with
  | Some (i, _) => S i
  | None => 0%nat
  end.

(** The byte footprints, off the labels (the [cand] vocabulary reused). *)
Definition gwrites_byte (G : gexec) (e : geid) (a : Z) (v : bv 8) : Prop :=
  ∃ l base vs j, gx_lbl G e = Some l ∧ lb_wr l = Some (base, vs) ∧
                 vs !! j = Some v ∧ acc_addr base j = a.

Definition greads_byte (G : gexec) (e : geid) (a : Z) (t : nat) (v : bv 8)
    : Prop :=
  ∃ l base ts vs j, gx_lbl G e = Some l ∧ lb_rd l = Some (base, ts, vs) ∧
                    ts !! j = Some t ∧ vs !! j = Some v ∧ acc_addr base j = a.

(** Program order. *)
Definition gpo (G : gexec) (e1 e2 : geid) : Prop :=
  e1.1 = e2.1 ∧ (e1.2 < e2.2)%nat ∧
  is_Some (gx_lbl G e1) ∧ is_Some (gx_lbl G e2).

(* ====================================================================== *)
(** * 2. Well-formedness: the order is DATA, so its sanity is an axiom *)

Definition gwf (G : gexec) : Prop :=
  NoDup (gx_gmo G) ∧
  (∀ e, e ∈ gx_gmo G ↔ gmem G e) ∧
  (* label shapes, as in [cand_shape] *)
  (∀ i p k l, gx_prog G !! i = Some p → p !! k = Some l →
     match l with
     | LLoad _ _ ts vs => length vs = length ts
     | LStore _ _ vs _ => vs ≠ []
     | LFence _ _ _ _ => True
     | LRmw _ _ _ ts rvs wvs _ =>
         wvs ≠ [] ∧ length wvs = length ts ∧ length rvs = length ts
     end).

(* ====================================================================== *)
(** * 3. RVWMO⁻: the kept ppo arms, load-value, atomicity *)

(** Rule 4: a fence between, with the given predecessor/successor bits. *)
Definition gfence_between (G : gexec) (e1 e2 : geid)
    (pr pw sr sw : bool) : Prop :=
  e1.1 = e2.1 ∧ (e1.2 < e2.2)%nat ∧
  ∃ kf, (e1.2 < kf)%nat ∧ (kf < e2.2)%nat ∧
        gx_lbl G (e1.1, kf) = Some (LFence pr pw sr sw).

(** The label classifiers, reused from [WeakAxiomatic]. *)
Definition glbl_is (G : gexec) (e : geid) (P : lbl → bool) : Prop :=
  ∃ l, gx_lbl G e = Some l ∧ P l = true.

(** ppo⁻, the kept arms:
    - rules 1–3 as same-byte program order (the coherence-facing fragment);
    - rule 4, in the two covering renderings [WeakAxiomatic] uses
      ([pr∧sr]-shaped and [pw∧sr]/[pr∧sw]/[pw∧sw] all reduce to: SOME
      fence whose predecessor bit covers [e1]'s kind and whose successor
      bit covers [e2]'s kind);
    - rule 5: [e1] an acquire read;
    - rule 7: an RCsc pair ([e1] a release write, [e2] a po-later acquire
      read). *)
Definition gfence_covers (G : gexec) (e1 e2 : geid) : Prop :=
  ∃ pr pw sr sw,
    gfence_between G e1 e2 pr pw sr sw ∧
    ((glbl_is G e1 lb_is_r ∧ pr = true) ∨ (glbl_is G e1 lb_is_w ∧ pw = true)) ∧
    ((glbl_is G e2 lb_is_r ∧ sr = true) ∨ (glbl_is G e2 lb_is_w ∧ sw = true)).

Definition gacq_po (G : gexec) (e1 e2 : geid) : Prop :=
  gpo G e1 e2 ∧ glbl_is G e1 lb_is_r ∧ glbl_is G e1 lb_aq.

Definition grel_acq (G : gexec) (e1 e2 : geid) : Prop :=
  gpo G e1 e2 ∧ glbl_is G e1 lb_is_w ∧ glbl_is G e1 lb_rl ∧
  glbl_is G e2 lb_is_r ∧ glbl_is G e2 lb_aq.

Definition gaccesses (G : gexec) (e : geid) (a : Z) : Prop :=
  (∃ v, gwrites_byte G e a v) ∨ (∃ t v, greads_byte G e a t v).

Definition gpoloc (G : gexec) (e1 e2 : geid) : Prop :=
  gpo G e1 e2 ∧ ∃ a, gaccesses G e1 a ∧ gaccesses G e2 a.

Definition gppo (G : gexec) (e1 e2 : geid) : Prop :=
  gpoloc G e1 e2 ∨ gfence_covers G e1 e2 ∨ gacq_po G e1 e2 ∨
  grel_acq G e1 e2.

Definition gppo_gmo (G : gexec) : Prop :=
  ∀ e1 e2, gppo G e1 e2 → gmo_lt G e1 e2.

(** LOAD VALUE.  A read's named source must exist, cover the byte with the
    value, be visible ((gmo ∪ po)-before the read — the po disjunct is
    store forwarding), and be co-MAXIMAL among visible same-byte writes.
    [t = 0] (the image) additionally requires NO visible same-byte
    write at all. *)
Definition gvisible (G : gexec) (w r : geid) : Prop :=
  gmo_lt G w r ∨ gpo G w r.

Definition gload_value (G : gexec) : Prop :=
  ∀ e a t v, greads_byte G e a t v →
    (match t with
     | 0%nat => gx_img G a = Some v
     | S _ => ∃ w, gwrite_at G t = Some w ∧ gwrites_byte G w a v ∧
                   gvisible G w e
     end) ∧
    (∀ w' v', gwrites_byte G w' a v' → gvisible G w' e →
       (gwix G w' ≤ t)%nat).

(** ATOMICITY (the fused RMW): no same-byte write co-between the read
    source and the RMW's own write. *)
Definition gatomicity (G : gexec) : Prop :=
  ∀ e a t v, greads_byte G e a t v → glbl_is G e lb_is_w →
    ∀ w' v', gwrites_byte G w' a v' →
      ¬ ((t < gwix G w')%nat ∧ (gwix G w' < gwix G e)%nat).

Definition rvwmo_minus_consistent (G : gexec) : Prop :=
  gwf G ∧ gppo_gmo G ∧ gload_value G ∧ gatomicity G.

(** RULE 14, as the graph-side gate the linearization (T2-1c) consumes:
    a memory event po-before a write is gmo-before it. *)
Definition grule14 (G : gexec) : Prop :=
  ∀ e w, gpo G e w → gmem G e → glbl_is G w lb_is_w → gmo_lt G e w.

(* ====================================================================== *)
(** * 4. The embedding: every [cand] IS a graph *)

Definition graph_of_cand (c : cand) : gexec :=
  GExec (cd_img c)
        ((λ i, (λ s : estep, es_lb s) <$>
                 (filter (λ s, es_ag s = i) (cd_tr c)))
           <$> seq 0%nat (S (list_max (es_ag <$> cd_tr c))))
        ((λ ks : nat * estep, ((ks.2).(es_ag),
            length (filter (λ s, es_ag s = (ks.2).(es_ag))
                           (take ks.1 (cd_tr c)))))
           <$> (filter (λ ks : nat * estep, lb_is_mem (es_lb ks.2) = true)
                       (imap pair (cd_tr c)))).

(* ====================================================================== *)
(** * 5. THE NON-COLLAPSE WITNESS: LB is RVWMO⁻-consistent

    The four-event load-buffering execution — each hart reads the OTHER
    hart's po-later store — with gmo placing both stores FIRST.  sRVWMO
    forbids this outcome for every conformant candidate
    ([WeakSrvwmoLitmus.lb_forbidden_model]); RVWMO⁻ admits it, so the
    tier-2 gap is real and this model is not sRVWMO in disguise. *)

Definition lbg : gexec :=
  GExec WeakLitmus.img0
        [[LLoad false 0 [2%nat] [WeakLitmus.b1];
          LStore false 8 [WeakLitmus.b1] WCplain];
         [LLoad false 8 [1%nat] [WeakLitmus.b1];
          LStore false 0 [WeakLitmus.b1] WCplain]]
        [(0%nat, 1%nat); (1%nat, 1%nat); (0%nat, 0%nat); (1%nat, 0%nat)].

(** The byte each [lbg] event accesses — the poloc refutation's engine. *)
Lemma lbg_acc (e : geid) (a : Z) :
  gaccesses lbg e a →
  (e = (0%nat, 0%nat) ∧ a = 0%Z) ∨ (e = (0%nat, 1%nat) ∧ a = 8%Z) ∨
  (e = (1%nat, 0%nat) ∧ a = 8%Z) ∨ (e = (1%nat, 1%nat) ∧ a = 0%Z).
Proof.
  intros [Hw|Hr].
  - destruct Hw as (v & l & b & vs & j & Hl & Hwr & Hv & Ha).
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=;
      destruct j as [|j]; simplify_eq/=;
      rewrite /acc_addr /=; naive_solver.
  - destruct Hr as (t & v & l & b & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=;
      destruct j as [|j]; simplify_eq/=;
      rewrite /acc_addr /=; naive_solver.
Qed.

Lemma lbg_wr (e : geid) (a : Z) (v : bv 8) :
  gwrites_byte lbg e a v →
  (e = (0%nat, 1%nat) ∧ a = 8%Z) ∨ (e = (1%nat, 1%nat) ∧ a = 0%Z).
Proof.
  intros (l & b & vs & j & Hl & Hwr & Hv & Ha).
  destruct e as [i k]. rewrite /gx_lbl /= in Hl.
  destruct i as [|[|i]]; simpl in Hl; [| |done];
    destruct k as [|[|k]]; simplify_eq/=;
    destruct j as [|j]; simplify_eq/=;
    rewrite /acc_addr /=; naive_solver.
Qed.

Theorem lb_graph_consistent : rvwmo_minus_consistent lbg.
Proof.
  split_and!.
  - (* gwf *) split_and!.
    + repeat constructor; rewrite ?elem_of_list_In; simpl; intuition congruence.
    + intros e. split.
      * intros He. rewrite !elem_of_cons elem_of_nil in He.
        destruct He as [-> |[-> |[-> | [-> | []]]]];
          eexists; split; reflexivity.
      * intros (l & Hl & Hm).
        destruct e as [i k]. rewrite /gx_lbl /= in Hl.
        destruct i as [|[|i]]; simpl in Hl; [| |done];
          destruct k as [|[|k]]; simplify_eq/=;
          rewrite !elem_of_cons; auto.
    + intros i p k l Hp Hk.
      destruct i as [|[|i]]; simplify_eq/=;
        destruct k as [|[|k]]; simplify_eq/=; done.
  - (* gppo⁻ ⊆ gmo: there are NO ppo⁻ edges — different bytes per hart,
       no fences, no acquires, no releases *)
    intros e1 e2 Hppo. exfalso.
    destruct Hppo as [Hpl|[Hf|[Ha|Hr]]].
    + (* poloc: the two events of one hart touch different bytes *)
      destruct Hpl as ((Hag & Hlt & _ & _) & a & H1 & H2).
      destruct (lbg_acc e1 a H1) as [[He1 Ha1]|[[He1 Ha1]|[[He1 Ha1]|[He1 Ha1]]]];
        destruct (lbg_acc e2 a H2) as [[He2 Ha2]|[[He2 Ha2]|[[He2 Ha2]|[He2 Ha2]]]];
        subst e1; subst e2; simpl in Hag, Hlt; lia.
    + destruct Hf as (pr & pw & sr & sw & (Hag & Hlt & kf & Hk1 & Hk2 & Hlf)
                      & _ & _).
      destruct e1 as [i1 k1], e2 as [i2 k2]; simpl in *; subst i2.
      rewrite /gx_lbl /= in Hlf.
      destruct i1 as [|[|i1]]; simpl in Hlf; [| |done];
        destruct kf as [|[|kf]]; simplify_eq/=; lia.
    + destruct Ha as (Hpo & (l & Hl & Hr') & (l' & Hl' & Haq)).
      destruct e1 as [i1 k1]. rewrite Hl in Hl'. simplify_eq.
      rewrite /gx_lbl /= in Hl.
      destruct i1 as [|[|i1]]; simpl in Hl; [| |done];
        destruct k1 as [|[|k1]]; simplify_eq/=; done.
    + destruct Hr as (Hpo & _ & (l & Hl & Hrl) & _).
      destruct e1 as [i1 k1]. rewrite /gx_lbl /= in Hl.
      destruct i1 as [|[|i1]]; simpl in Hl; [| |done];
        destruct k1 as [|[|k1]]; simplify_eq/=; done.
  - (* load value *)
    intros e a t v Hr.
    destruct Hr as (l & base & ts & vs & j & Hl & Hrd & Hj & Hv & Ha).
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=;
      destruct j as [|j]; simplify_eq/=.
    + (* hart 0 reads byte 0 at write index 2 = hart 1's store to 0 *)
      split.
      * eexists. split_and!; [done| |].
        { by exists (LStore false 0 [WeakLitmus.b1] WCplain), 0%Z, [WeakLitmus.b1], 0%nat. }
        { left. rewrite /gmo_lt /gpos /=. split_and!;
            [rewrite !elem_of_cons; auto|rewrite !elem_of_cons; auto
            |vm_compute; lia]. }
      * intros w' v' Hw' Hvis.
        destruct (lbg_wr w' _ _ Hw') as [[-> Hab]|[-> _]];
          [exfalso; rewrite /acc_addr /= in Hab; lia|].
        by vm_compute.
    + (* hart 1 reads byte 8 at write index 1 = hart 0's store to 8 *)
      split.
      * eexists. split_and!; [done| |].
        { by exists (LStore false 8 [WeakLitmus.b1] WCplain), 8%Z,
            [WeakLitmus.b1], 0%nat. }
        { left. rewrite /gmo_lt /gpos /=. split_and!;
            [rewrite !elem_of_cons; auto|rewrite !elem_of_cons; auto
            |vm_compute; lia]. }
      * intros w' v' Hw' Hvis.
        destruct (lbg_wr w' _ _ Hw') as [[-> _]|[-> Hab]];
          [|exfalso; rewrite /acc_addr /= in Hab; lia].
        by vm_compute.
  - (* atomicity: no event both reads and writes *)
    intros e a t v Hr (l & Hl & Hw).
    destruct Hr as (l' & base & ts & vs & j & Hl' & Hrd & _).
    rewrite Hl in Hl'. simplify_eq.
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=; done.
Qed.

(* ====================================================================== *)
(** * 6. POSITION ARITHMETIC (additive; consumed by [WeakRvwmoLin.v])

    The rule-14 linearization (T2-1c) is all [gpos]/[gwix] bookkeeping.  Two
    facts carry it: [gmo] is TOTAL on its members (the order is a [NoDup]
    list, so a member's position determines it), and the write sub-order
    [gwrites] is a FILTER of [gx_gmo] — hence write indices and gmo positions
    order the writes THE SAME WAY ([gwix_gpos_lt]), which is what lets a
    read's [ts] entry be reused verbatim as a candidate log position.

    Nothing above this line changes. *)

From stdpp Require Import sorting.

(** ** Sortedness by lookup — the generic kit the filter argument needs. *)

Lemma StronglySorted_lookup_elim {A} (R : relation A) (l : list A) i j x y :
  StronglySorted R l → l !! i = Some x → l !! j = Some y → (i < j)%nat → R x y.
Proof.
  intros Hss. revert i j.
  induction Hss as [|z l Hss IH Hall]; intros i j Hi Hj Hlt.
  { by rewrite lookup_nil in Hi. }
  destruct i as [|i]; simpl in Hi.
  - simplify_eq. destruct j as [|j]; [lia|]. simpl in Hj.
    rewrite Forall_forall in Hall. apply Hall. by eapply elem_of_list_lookup_2.
  - destruct j as [|j]; [lia|]. simpl in Hj. apply (IH i j); [done|done|lia].
Qed.

Lemma StronglySorted_lookup_intro {A} (R : relation A) (l : list A) :
  (∀ i j x y, l !! i = Some x → l !! j = Some y → (i < j)%nat → R x y) →
  StronglySorted R l.
Proof.
  induction l as [|z l IH]; intros Hl; [constructor|].
  constructor.
  - apply IH. intros i j x y Hi Hj Hlt. apply (Hl (S i) (S j)); [done|done|lia].
  - apply Forall_forall. intros y Hy.
    apply elem_of_list_lookup_1 in Hy as [j Hj].
    apply (Hl 0%nat (S j)); [done|done|lia].
Qed.

Lemma StronglySorted_filter {A} (R : relation A) (P : A → Prop)
    `{∀ x, Decision (P x)} (l : list A) :
  StronglySorted R l → StronglySorted R (filter P l).
Proof.
  induction 1 as [|z l Hss IH Hall]; [rewrite filter_nil; constructor|].
  rewrite filter_cons. case_decide as Hz; [|exact IH].
  constructor; [exact IH|].
  apply Forall_forall. intros y Hy. apply elem_of_list_filter in Hy as [_ Hy].
  rewrite Forall_forall in Hall. by apply Hall.
Qed.

(** ** [gpos]: the gmo position of a member *)

Lemma gpos_lookup G e :
  e ∈ gx_gmo G → ∃ i, gx_gmo G !! i = Some e ∧ gpos G e = i.
Proof.
  intros He. rewrite /gpos.
  destruct (list_find (λ e', e' = e) (gx_gmo G)) as [[i x]|] eqn:Hf.
  - apply list_find_Some in Hf as (Hi & -> & _). by exists i.
  - exfalso. rewrite list_find_None Forall_forall in Hf. by apply (Hf e He).
Qed.

Lemma gpos_elem_lookup G e : e ∈ gx_gmo G → gx_gmo G !! gpos G e = Some e.
Proof. intros He. by destruct (gpos_lookup G e He) as (i & Hi & ->). Qed.

Lemma gpos_of_lookup G i e :
  NoDup (gx_gmo G) → gx_gmo G !! i = Some e → gpos G e = i.
Proof.
  intros Hnd Hi.
  destruct (gpos_lookup G e (elem_of_list_lookup_2 _ _ _ Hi)) as (i' & Hi' & ->).
  by apply (NoDup_lookup (gx_gmo G) i' i e).
Qed.

Lemma gpos_lt_len G e : e ∈ gx_gmo G → (gpos G e < length (gx_gmo G))%nat.
Proof. intros He. by eapply lookup_lt_Some, gpos_elem_lookup. Qed.

Lemma gpos_inj G e1 e2 :
  NoDup (gx_gmo G) → e1 ∈ gx_gmo G → e2 ∈ gx_gmo G →
  gpos G e1 = gpos G e2 → e1 = e2.
Proof.
  intros Hnd H1 H2 Heq.
  pose proof (gpos_elem_lookup G e1 H1) as L1.
  pose proof (gpos_elem_lookup G e2 H2) as L2.
  rewrite Heq in L1. by simplify_eq.
Qed.

Lemma gmo_lt_trans G e1 e2 e3 : gmo_lt G e1 e2 → gmo_lt G e2 e3 → gmo_lt G e1 e3.
Proof. intros (?&?&?) (?&?&?). split_and!; [done|done|lia]. Qed.

Lemma gmo_lt_irrefl G e : ¬ gmo_lt G e e.
Proof. intros (_ & _ & ?). lia. Qed.

(** TOTALITY on members: the missing half of "gmo is a strict total order". *)
Lemma gmo_lt_total G e1 e2 :
  NoDup (gx_gmo G) → e1 ∈ gx_gmo G → e2 ∈ gx_gmo G → e1 ≠ e2 →
  gmo_lt G e1 e2 ∨ gmo_lt G e2 e1.
Proof.
  intros Hnd H1 H2 Hne.
  destruct (decide (gpos G e1 < gpos G e2)%nat) as [Hlt|Hge];
    [by left; split_and!|].
  right. split_and!; [done|done|].
  destruct (decide (gpos G e1 = gpos G e2)) as [Heq|Hne'];
    [by destruct Hne; eapply gpos_inj|lia].
Qed.

(** The contrapositive shape the load-value axiom hands back: not gmo-before
    means at-or-after. *)
Lemma gmo_nlt_ge G e1 e2 :
  NoDup (gx_gmo G) → e1 ∈ gx_gmo G → e2 ∈ gx_gmo G →
  ¬ gmo_lt G e1 e2 → (gpos G e2 ≤ gpos G e1)%nat.
Proof.
  intros Hnd H1 H2 Hn.
  destruct (decide (gpos G e1 < gpos G e2)%nat) as [Hlt|]; [|lia].
  destruct Hn. by split_and!.
Qed.

(** ** [gwrites] / [gwix]: the write sub-order *)

Lemma gwrites_elem_of G e : e ∈ gwrites G ↔ e ∈ gx_gmo G ∧ gis_w G e = true.
Proof.
  rewrite /gwrites elem_of_list_filter Is_true_true. naive_solver.
Qed.

Lemma gwrites_nodup G : NoDup (gx_gmo G) → NoDup (gwrites G).
Proof. intros Hnd. by apply NoDup_filter. Qed.

Lemma gwrites_lookup_elem G i w : gwrites G !! i = Some w → w ∈ gwrites G.
Proof. intros Hi. by eapply elem_of_list_lookup_2. Qed.

Lemma gwix_lookup G w :
  w ∈ gwrites G → ∃ i, gwrites G !! i = Some w ∧ gwix G w = S i.
Proof.
  intros He. rewrite /gwix.
  destruct (list_find (λ e', e' = w) (gwrites G)) as [[i x]|] eqn:Hf.
  - apply list_find_Some in Hf as (Hi & -> & _). by exists i.
  - exfalso. rewrite list_find_None Forall_forall in Hf. by apply (Hf w He).
Qed.

Lemma gwix_of_lookup G i w :
  NoDup (gx_gmo G) → gwrites G !! i = Some w → gwix G w = S i.
Proof.
  intros Hnd Hi.
  destruct (gwix_lookup G w (gwrites_lookup_elem G i w Hi)) as (i' & Hi' & ->).
  by rewrite (NoDup_lookup (gwrites G) i' i w (gwrites_nodup G Hnd) Hi' Hi).
Qed.

Lemma gwix_pos G w : w ∈ gwrites G → (0 < gwix G w)%nat.
Proof. intros He. destruct (gwix_lookup G w He) as (i & _ & ->). lia. Qed.

Lemma gwix_le G w :
  w ∈ gwrites G → (gwix G w ≤ length (gwrites G))%nat.
Proof.
  intros He. destruct (gwix_lookup G w He) as (i & Hi & ->).
  apply lookup_lt_Some in Hi. lia.
Qed.

Lemma gwrite_at_gwix G w :
  w ∈ gwrites G → gwrite_at G (gwix G w) = Some w.
Proof.
  intros He. destruct (gwix_lookup G w He) as (i & Hi & ->). exact Hi.
Qed.

Lemma gwrite_at_inv G t w :
  NoDup (gx_gmo G) → gwrite_at G t = Some w →
  w ∈ gwrites G ∧ gwix G w = t.
Proof.
  destruct t as [|i]; [done|]. intros Hnd Hi. split.
  - by eapply gwrites_lookup_elem.
  - by apply gwix_of_lookup.
Qed.

Lemma gwix_inj G w1 w2 :
  NoDup (gx_gmo G) → w1 ∈ gwrites G → w2 ∈ gwrites G →
  gwix G w1 = gwix G w2 → w1 = w2.
Proof.
  intros Hnd H1 H2 Heq.
  destruct (gwix_lookup G w1 H1) as (i1 & Hi1 & E1).
  destruct (gwix_lookup G w2 H2) as (i2 & Hi2 & E2).
  assert (i1 = i2) as -> by (rewrite E1 E2 in Heq; lia).
  rewrite Hi1 in Hi2. by simplify_eq.
Qed.

(** THE ORDER-PRESERVATION FACT: [gwrites] is a filter of [gx_gmo], so a
    write's INDEX and its gmo POSITION agree on order.  This is why a graph
    read's [ts] entry (a gmo-write index) is NUMERICALLY the candidate log
    position of the same write — the linearization renumbers nothing. *)
Lemma gwrites_sorted G :
  NoDup (gx_gmo G) →
  StronglySorted (λ x y, (gpos G x < gpos G y)%nat) (gwrites G).
Proof.
  intros Hnd. apply StronglySorted_filter.
  apply StronglySorted_lookup_intro. intros i j x y Hi Hj Hlt.
  rewrite (gpos_of_lookup G i x Hnd Hi) (gpos_of_lookup G j y Hnd Hj). lia.
Qed.

Lemma gwix_gpos_lt G w1 w2 :
  NoDup (gx_gmo G) → w1 ∈ gwrites G → w2 ∈ gwrites G →
  ((gwix G w1 < gwix G w2)%nat ↔ (gpos G w1 < gpos G w2)%nat).
Proof.
  intros Hnd H1 H2.
  destruct (gwix_lookup G w1 H1) as (i1 & Hi1 & E1).
  destruct (gwix_lookup G w2 H2) as (i2 & Hi2 & E2).
  pose proof (gwrites_sorted G Hnd) as Hss.
  split.
  - intros Hlt. apply (StronglySorted_lookup_elim _ _ i1 i2 w1 w2 Hss Hi1 Hi2).
    lia.
  - intros Hlt. rewrite E1 E2.
    destruct (decide (i1 < i2)%nat) as [?|Hge]; [lia|].
    destruct (decide (i1 = i2)) as [->|Hne].
    { rewrite Hi1 in Hi2. simplify_eq. lia. }
    exfalso.
    pose proof (StronglySorted_lookup_elim _ _ i2 i1 w2 w1 Hss Hi2 Hi1
                  ltac:(lia)) as Hgt. simpl in Hgt. lia.
Qed.

(** [gwf]'s membership clause, in the direction the linearization uses. *)
Lemma gwf_mem_gmo G e : gwf G → gmem G e → e ∈ gx_gmo G.
Proof. intros (_ & Hm & _) He. by apply Hm. Qed.

Lemma gwf_gmo_mem G e : gwf G → e ∈ gx_gmo G → gmem G e.
Proof. intros (_ & Hm & _) He. by apply Hm. Qed.

(** A write EVENT (label-level) is a member of the write sub-order. *)
Lemma gis_w_gwrites G e :
  gwf G → is_Some (gx_lbl G e) → gis_w G e = true → e ∈ gwrites G.
Proof.
  intros Hwf [l Hl] Hw. apply gwrites_elem_of. split; [|done].
  apply (gwf_mem_gmo G e Hwf). exists l. split; [done|].
  rewrite /gis_w Hl in Hw. by rewrite /lb_is_mem Hw orb_true_r.
Qed.

(* ====================================================================== *)
(** * 7. The dependency fragment (route B, stage B0)

    Design: [claude-notes/design/weak-memory-route-b.md] §2.

    Bare RVWMO⁻ admits thin-air (dropping ppo rules 9–13 is what admits
    it), and a thin-air execution of the xv6 image could fabricate values
    into protected bytes — so the tier-2 capstone's hypothesis must carry
    the STORE-DEP FRAGMENT.  It rides as graph DATA: a list of
    (read, store) event pairs — RVWMO's syntactic address/data deps into
    stores (rules 9/10's store halves), control deps into stores (rule
    11), and the W-TV translation edge (the adopted boundary sentence;
    rule 13's rationale) — with the ordering axiom [gdeps_gmo].  Sources
    are always READS: branch events are not in the fused alphabet, so a
    control dep names the branched-on read; a translation dep names the
    walk read.  Loads gain nothing as TARGETS (deviation D-8 stands;
    matches both Arm models per the W3 audit).

    Direction check: adding constraints SHRINKS the declared model toward
    RVWMO, and every added edge class is ⊆ RVWMO's own ppo, so the final
    theorem still covers RVWMO-conformant hardware.

    The CONFORMANCE clause ("[gd_deps] contains the deps the xv6 programs
    actually induce") is deliberately NOT part of consistency: it is a
    capstone-level hypothesis, stated through the per-hart row-emission
    interface (route-b design §2a, resolution (α) realized through
    [WeakAxRealize.exec_prog_ok]'s vocabulary) — stage B0b. *)

Record gdexec := GDExec {
  gd_g    : gexec;
  gd_deps : list (geid * geid);
}.

(** Well-formedness: each edge runs from a READ to a po-LATER WRITE of
    the same hart. *)
Definition gdeps_wf (G : gexec) (deps : list (geid * geid)) : Prop :=
  ∀ rw : geid * geid, rw ∈ deps →
    rw.1.1 = rw.2.1 ∧ (rw.1.2 < rw.2.2)%nat ∧
    glbl_is G rw.1 lb_is_r ∧ glbl_is G rw.2 lb_is_w.

(** THE ORDERING AXIOM — the ppo 9–13 store fragment: a dep-source read
    is globally ordered before its dependent store. *)
Definition gdeps_gmo (G : gexec) (deps : list (geid * geid)) : Prop :=
  ∀ rw : geid * geid, rw ∈ deps → gmo_lt G rw.1 rw.2.

Definition rvwmo_minus_deps_consistent (GD : gdexec) : Prop :=
  rvwmo_minus_consistent (gd_g GD) ∧
  gdeps_wf (gd_g GD) (gd_deps GD) ∧
  gdeps_gmo (gd_g GD) (gd_deps GD).

(** NON-COLLAPSE, re-checked for the extended model: LB's load;store
    pairs are syntactically independent (no address, data, control or
    translation dependency — the loads' values feed nothing), so the LB
    witness carries the EMPTY dep set and stays consistent.  The tier-2
    gap survives the model extension. *)
Definition lbgd : gdexec := GDExec lbg [].

Theorem lb_graph_deps_consistent : rvwmo_minus_deps_consistent lbgd.
Proof.
  split_and!; [exact lb_graph_consistent| |];
    by intros rw Hrw%elem_of_nil.
Qed.

(* ====================================================================== *)
(** * 8. ADDITIVE HELPERS for the exchange kit (route B, stage B2)

    Label-level bookkeeping the exchange lemmas ([WeakRvwmoXchg.v]) need:
    the two "this event is a write / a read" bridges between the byte
    footprints, the classifiers and [gis_w], and — the one that makes the
    exchange lemmas' ppo⁻ side condition FREE for cross-hart pairs —
    ppo⁻ IS SAME-HART.  Nothing above this line changes. *)

Lemma glbl_is_w_gis_w G e : glbl_is G e lb_is_w → gis_w G e = true.
Proof. intros (l & Hl & Hw). by rewrite /gis_w Hl. Qed.

(** (Named [_gis_w], not [_is_w]: [WeakRvwmoLin.v] has a SECTION-LOCAL
    [gwrites_byte_is_w] whose conclusion is the [glbl_is] form.) *)
Lemma gwrites_byte_gis_w G e a v : gwrites_byte G e a v → gis_w G e = true.
Proof.
  intros (l & base & vs & j & Hl & Hwr & _ & _).
  rewrite /gis_w Hl. by eapply lb_wr_is_w.
Qed.

(** EVERY ppo⁻ ARM IS SAME-HART — each of the four disjuncts carries
    either [gpo] or [gfence_between], both of which pin the agent.  So a
    CROSS-HART pair discharges any "no ppo⁻ edge" side condition for
    free. *)
Lemma gppo_same_hart G e1 e2 : gppo G e1 e2 → e1.1 = e2.1.
Proof.
  intros [[[Hag _] _]|[(pr & pw & sr & sw & (Hag & _) & _ & _)
                       |[[[Hag _] _]|[[Hag _] _]]]]; exact Hag.
Qed.

(** ** 8.1 [gwix]'s junk value, and its contrapositive

    [gwix] is [0] off the write sub-order (the [list_find] fallback), so a
    NONZERO write index is itself a membership certificate — the shape the
    (W,W) exchange's atomicity case analysis needs, where the only handle on
    an event is an equation between write indices. *)

Lemma gwix_zero G w : w ∉ gwrites G → gwix G w = 0%nat.
Proof.
  intros Hnin. rewrite /gwix.
  destruct (list_find (λ e', e' = w) (gwrites G)) as [[i z]|] eqn:Hf; [|done].
  exfalso. apply list_find_Some in Hf as (Hi & -> & _).
  apply Hnin. by eapply elem_of_list_lookup_2.
Qed.

Lemma gwix_elem G w : (0 < gwix G w)%nat → w ∈ gwrites G.
Proof.
  intros Hpos. destruct (decide (w ∈ gwrites G)) as [?|Hnin]; [done|].
  rewrite (gwix_zero G w Hnin) in Hpos. lia.
Qed.

(** ** 8.2 [gwf]'s shape clause, at an EVENT

    [gwf]'s third conjunct is indexed by (row, offset); every consumer holds
    a [gx_lbl] fact instead.  This is the one-line bridge. *)

Lemma gwf_lbl_shape G e l :
  gwf G → gx_lbl G e = Some l →
  match l with
  | LLoad _ _ ts vs => length vs = length ts
  | LStore _ _ vs _ => vs ≠ []
  | LFence _ _ _ _ => True
  | LRmw _ _ _ ts rvs wvs _ =>
      wvs ≠ [] ∧ length wvs = length ts ∧ length rvs = length ts
  end.
Proof.
  intros (_ & _ & Hsh) Hl. rewrite /gx_lbl in Hl.
  destruct (gx_prog G !! e.1) as [p|] eqn:Hp; simpl in Hl; [|done].
  by eapply Hsh.
Qed.

(** ** 8.3 A FUSED RMW'S READ FOOTPRINT IS ITS WRITE FOOTPRINT

    [LRmw] carries ONE base and [length rvs = length ts = length wvs], so an
    event that both reads and writes touches exactly the same bytes on both
    halves.  This is what makes a BYTE-DISJOINTNESS hypothesis between two
    writes cover their read halves too — the (W,W) exchange's load-bearing
    step. *)

Lemma gread_byte_write_byte G e a t v :
  gwf G → gis_w G e = true → greads_byte G e a t v →
  ∃ v', gwrites_byte G e a v'.
Proof.
  intros Hwf Hw (l & base & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
  pose proof (gwf_lbl_shape G e l Hwf Hl) as Hsh.
  rewrite /gis_w Hl in Hw.
  assert (Hwr : ∃ wvs, lb_wr l = Some (base, wvs) ∧ length wvs = length ts).
  { destruct l; simpl in *; simplify_eq/=; naive_solver. }
  destruct Hwr as (wvs & Hwr & Hlen).
  assert (Hj : (j < length wvs)%nat) by (rewrite Hlen; by eapply lookup_lt_Some).
  apply lookup_lt_is_Some_2 in Hj as [v' Hv'].
  exists v'. by exists l, base, wvs, j.
Qed.

(** ** 8.4 A read's NAMED SOURCE covers the byte with the read value *)

Lemma gread_source_byte G e a t v w :
  gload_value G → greads_byte G e a t v → gwrite_at G t = Some w →
  gwrites_byte G w a v.
Proof.
  intros Hlv Hrd Hwat. destruct (Hlv e a t v Hrd) as [Hsrc _].
  destruct t as [|t]; [done|].
  destruct Hsrc as (w0 & Hwat0 & Hwb & _).
  rewrite Hwat in Hwat0. by simplify_eq.
Qed.
