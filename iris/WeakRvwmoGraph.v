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
