(** * WeakRvwmoFloor.v — THE FLOOR DISCHARGE (the core of T2-1c′)

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.4 (the "B1b-2
    RESIDUE LANDED … T2-1c′" paragraph) and §4e's SUB-SLICES entry (3a).

    THE PROBLEM.  [WeakRvwmoCert.snoc_read_consistent] appends a read to an
    sRVWMO-consistent candidate as soon as the read's named source survives
    the agent's own COHERENCE FLOOR:

      ¬ writes_in (cd_log_end c) a t (cd_floor c i aq a),
      cd_floor c i aq a = Nat.max (load_vpre (ms_ws (cand_last_st c) i) aq)
                                  (coh  (ms_ws (cand_last_st c) i) a).

    [WeakRvwmoLin]'s rule-14 linearization (T2-1c) discharges the SAME
    obligation for ONE trace — the rank trace — and it does so DECLARATIVELY
    (through [ax_coherence]/[ax_ord]), which is exactly what does not
    generalize: T2-1c′ must admit ANY linear extension of po ∪ rf ∪ gmo|W
    (∪ dev), and the trace is then not available as a whole.  So this file
    discharges the floor OPERATIONALLY, by an induction on the candidate that
    tracks what each of the agent's own view components can possibly contain.

    THE DECOMPOSITION ([WeakMem]'s own step functions, read off §"The step
    functions"):

      load_vpre ws aq = w_vrNew ws ⊔ (aq ? w_vRel ws)
      coh ws a        = the per-byte floor, raised by the agent's own
                        accesses to [a] to (post-view ⊔ timestamp)

    and the two OLD watermarks feed [w_vrNew] only THROUGH A FENCE
    ([fence_post]: vrNew ⊔= (pr ? vrOld) ⊔ (pw ? vwOld) when sr).  Hence the
    invariant below is CONDITIONAL in exactly two places — [w_vrOld] /
    [w_vwOld] are bounded only when a fence still to come will publish them
    ([fhook]), and [w_vRel] only when an acquire still to come will consume it
    ([ahook]).  Each hook is precisely one riscv.cat ppo⁻ arm:

      coh          ← rules 1-3 (poloc)          [gpoloc_gmo]
      w_vrNew      ← rule 5 (acquire)           [gacq_gmo]
      w_vrOld/vwOld← rule 4 (fence)             [gfence_gmo]
      w_vRel       ← rule 7 (RCsc release)      [grelacq_gmo]

    and the arithmetic that closes the argument is: everything an ordered-
    before-[r] event can put into a view is a gmo write index BELOW [r], and
    [gload_value]'s co-maximality half says every gmo-visible same-byte write
    has index ≤ [t].  That is [gvis_ub] (§1) — "every log index at or below
    [n] names a write that is gmo-before [r]".

    WHAT IS NOT NEEDED: [grule14].  The floor is discharged from
    [rvwmo_minus_consistent] alone; rule 14 enters T2-1c′ only through the
    LOG-ORDER clause of a G-trace prefix ([gtp_wix] below), i.e. on the write
    side, where it is what makes the appended write the next [gwrites] entry.

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakAxiomatic3.
Require Import WeakRvwmoGraph.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. [gvis_ub]: "every write index below [n] is gmo-before [r]"

    The single numeric predicate the whole file runs on.  It is closed
    downward, hence [maxcl] ([WeakMem]'s DOMINATION vocabulary), which is
    exactly the interface the fold lemmas there are stated at. *)

Definition gvis_ub (G : gexec) (r : geid) (n : nat) : Prop :=
  ∀ (s : nat) w, gwrite_at G s = Some w → (s ≤ n)%nat → gmo_lt G w r.

Lemma gvis_ub_down G r m n :
  (m ≤ n)%nat → gvis_ub G r n → gvis_ub G r m.
Proof. intros Hle H s w Hw Hs. apply (H s w Hw). lia. Qed.

Lemma gvis_ub_0 G r : gvis_ub G r 0%nat.
Proof. intros s w Hw Hs. assert (s = 0%nat) as -> by lia. done. Qed.

Lemma gvis_ub_maxcl G r : maxcl (gvis_ub G r).
Proof.
  split; [apply gvis_ub_0|]. intros n1 n2 H1 H2.
  destruct (Nat.max_spec n1 n2) as [[_ ->]|[_ ->]]; [exact H2|exact H1].
Qed.

Lemma gvis_ub_ev G r r' n :
  gvis_ub G r n → gmo_lt G r r' → gvis_ub G r' n.
Proof.
  intros H Hlt s w Hw Hs. eapply gmo_lt_trans; [by apply (H s w)|exact Hlt].
Qed.

(** THE INTRODUCTION RULE: a single gmo-before write bounds the whole
    prefix below it, because [gwix] and [gpos] order the writes alike
    ([WeakRvwmoGraph.gwix_gpos_lt]). *)
Lemma gvis_ub_of_write G r t w :
  gwf G → gwrite_at G t = Some w → gmo_lt G w r → gvis_ub G r t.
Proof.
  intros Hwf Ht Hlt s w' Hs' Hle.
  destruct Hwf as (Hnd & _ & _).
  destruct (gwrite_at_inv G s w' Hnd Hs') as (Hw'g & Hix').
  destruct (gwrite_at_inv G t w Hnd Ht) as (Hwg & Hix).
  destruct (decide (s = t)) as [->|Hne].
  { assert (w' = w) as ->; [|exact Hlt].
    eapply gwix_inj; [exact Hnd|exact Hw'g|exact Hwg|]. by rewrite Hix' Hix. }
  eapply gmo_lt_trans; [|exact Hlt]. split_and!.
  - by apply (proj1 (gwrites_elem_of G w')).
  - by apply (proj1 (gwrites_elem_of G w)).
  - apply (gwix_gpos_lt G w' w Hnd Hw'g Hwg). rewrite Hix' Hix. lia.
Qed.

(* ====================================================================== *)
(** * 2. THE FORWARD BANK IS VIEW-FREE

    D-7r: [store_post] banks [(t, 0)], so a forwarded read contributes either
    its own timestamp or [0] — never a third number.  [fwd0] is that
    invariant, and it is what replaces [WeakMem]'s "no byte of this load is
    forwarded" side condition in the fold lemmas of §3. *)

Definition fwd0 (ws : wstate) : Prop :=
  ∀ b tf vf, w_fwd ws !! b = Some (tf, vf) → vf = 0%nat.

Lemma fwd0_init : fwd0 ws_init.
Proof. intros b tf vf. rewrite /ws_init /= lookup_empty //. Qed.

Lemma fwd0_ext ws ws' : w_fwd ws' = w_fwd ws → fwd0 ws → fwd0 ws'.
Proof. intros Heq H b tf vf. rewrite Heq. apply H. Qed.

Lemma fwd_view_P P ws aq b t :
  maxcl P → fwd0 ws → P t → P (fwd_view ws aq b t).
Proof.
  intros Hcl H0 Ht. rewrite /fwd_view. destruct aq; [exact Ht|].
  destruct (w_fwd ws !! b) as [[tf vf]|] eqn:Hf; [|exact Ht].
  case_bool_decide; [|exact Ht].
  rewrite (H0 b tf vf Hf). by apply maxcl_0.
Qed.

Lemma fwd0_store_post ws rl b t : fwd0 ws → fwd0 (store_post ws rl b t).
Proof.
  intros H b' tf vf. rewrite /store_post /=.
  destruct (decide (b' = b)) as [->|Hne].
  - rewrite lookup_insert. by intros [= <- <-].
  - rewrite lookup_insert_ne //. apply H.
Qed.

Lemma fwd0_store_fold rl t as_ ws :
  fwd0 ws → fwd0 (foldl (λ w b, store_post w rl b t) ws as_).
Proof.
  revert ws. induction as_ as [|b l IH]; intros ws H; [exact H|].
  simpl. apply IH. by apply fwd0_store_post.
Qed.

Lemma fwd0_store_post_run ws rl base n t :
  fwd0 ws → fwd0 (store_post_run ws rl base n t).
Proof.
  intros H. rewrite /store_post_run.
  eapply fwd0_ext; [apply ctrl_post_fwd|]. by apply fwd0_store_fold.
Qed.

Lemma fwd0_load_post_run ws aq base ts :
  fwd0 ws → fwd0 (load_post_run ws aq base ts).
Proof. intros H. eapply fwd0_ext; [apply load_post_run_fwd|exact H]. Qed.

Lemma fwd0_fence_post ws pr pw sr sw :
  fwd0 ws → fwd0 (fence_post ws pr pw sr sw).
Proof. intros H. eapply fwd0_ext; [apply fence_post_fwd|exact H]. Qed.

(* ====================================================================== *)
(** * 3. THE DOMINATION FOLD LEMMAS, AT [fwd0]

    [WeakMem]'s §DOMINATION states the load-fold bounds under "no byte of
    this load is forwarded".  Forwarding is not excluded here (a lock client
    forwards constantly), so the three lemmas are re-proved at [fwd0]: a
    forwarded byte contributes the BANKED view, which D-7r pins at [0], and
    [maxcl] holds at [0].  Everything else is [WeakMem]'s own. *)

Lemma load_fold_coh' P aq vpre ats ws a :
  maxcl P → fwd0 ws →
  P (coh ws a) → P vpre → (∀ p, p ∈ ats → p.1 = a → P p.2) →
  P (coh (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats) a).
Proof.
  intros Hcl. revert ws. induction ats as [|p l IH]; intros ws Hfw Hc Hv Hts;
    [exact Hc|].
  simpl. apply IH.
  - eapply fwd0_ext; [apply load_post_at_fwd|exact Hfw].
  - destruct (decide (a = p.1)) as [Heq|Hne]; last first.
    { rewrite (coh_load_post_at_ne _ _ _ _ _ _ Hne). exact Hc. }
    assert (Hpa : P p.2).
    { apply (Hts p); [apply elem_of_cons; by left|by rewrite -Heq]. }
    rewrite Heq coh_load_post_at_eq.
    apply maxcl_max; [done|rewrite -Heq; exact Hc|].
    apply maxcl_max; [done| |exact Hpa].
    apply maxcl_max; [done|exact Hv|by apply fwd_view_P].
  - exact Hv.
  - intros q Hq Hqa. apply (Hts q); [apply elem_of_cons; by right|exact Hqa].
Qed.

Lemma load_fold_vrOld' P aq vpre ats ws :
  maxcl P → fwd0 ws →
  P (w_vrOld ws) → P vpre → (∀ p, p ∈ ats → P p.2) →
  P (w_vrOld (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats)).
Proof.
  intros Hcl. revert ws. induction ats as [|p l IH]; intros ws Hfw Hc Hv Hts;
    [exact Hc|].
  simpl. apply IH.
  - eapply fwd0_ext; [apply load_post_at_fwd|exact Hfw].
  - rewrite /load_post_at /=.
    apply maxcl_max; [done|exact Hc|].
    apply maxcl_max; [done|exact Hv|].
    apply fwd_view_P; [done|exact Hfw|apply Hts, elem_of_cons; by left].
  - exact Hv.
  - intros q Hq. apply Hts, elem_of_cons; by right.
Qed.

Lemma load_fold_vrNew' P aq vpre ats ws :
  maxcl P → fwd0 ws →
  P (w_vrNew ws) → P vpre → (∀ p, p ∈ ats → P p.2) →
  P (w_vrNew (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats)).
Proof.
  intros Hcl. revert ws. induction ats as [|p l IH]; intros ws Hfw Hc Hv Hts;
    [exact Hc|].
  simpl. apply IH.
  - eapply fwd0_ext; [apply load_post_at_fwd|exact Hfw].
  - rewrite /load_post_at /=. destruct aq; [|exact Hc].
    apply maxcl_max; [done|exact Hc|].
    apply maxcl_max; [done|exact Hv|].
    apply fwd_view_P; [done|exact Hfw|apply Hts, elem_of_cons; by left].
  - exact Hv.
  - intros q Hq. apply Hts, elem_of_cons; by right.
Qed.

Lemma store_fold_vRel P rl t as_ ws :
  maxcl P → P (w_vRel ws) → P t →
  P (w_vRel (foldl (λ w b, store_post w rl b t) ws as_)).
Proof.
  intros Hcl. revert ws. induction as_ as [|b l IH]; intros ws Hc Ht; [exact Hc|].
  simpl. apply IH; [|exact Ht]. rewrite /store_post /=.
  destruct rl; [by apply maxcl_max|exact Hc].
Qed.

(** ** 3.1 The two footprint-membership dictionaries *)

Lemma elem_of_run_ats (base : Z) (ts : list nat) p :
  p ∈ zip_with (λ (j : nat) (t : nat), (base + Z.of_nat j, t))
        (seq 0 (length ts)) ts →
  ∃ j : nat, (j < length ts)%nat ∧ ts !! j = Some p.2 ∧
             p.1 = acc_addr base j.
Proof.
  intros Hp. apply elem_of_list_lookup_1 in Hp as [n Hn].
  rewrite lookup_zip_with in Hn.
  destruct (seq 0 (length ts) !! n) as [j|] eqn:Hs; simpl in Hn; [|done].
  destruct (ts !! n) as [t|] eqn:Ht; simpl in Hn; [|done].
  simplify_eq/=. apply lookup_seq in Hs as [-> Hlt].
  exists n. split_and!; [exact Hlt|exact Ht|done].
Qed.

Lemma elem_of_run_as (base : Z) (n : nat) (b : Z) :
  b ∈ map (λ j : nat, base + Z.of_nat j) (seq 0 n) →
  ∃ j : nat, (j < n)%nat ∧ b = acc_addr base j.
Proof.
  intros Hb. apply elem_of_list_In, in_map_iff in Hb as (j & <- & Hj).
  apply in_seq in Hj. exists j. split; [lia|done].
Qed.

(** ** 3.2 The run level

    The five components [finv] (§5) tracks, for each of the three run-level
    step functions: an upper bound where the step raises them, an equation
    where it does not. *)

Lemma load_run_coh P ws aq base ts a :
  maxcl P → fwd0 ws → P (coh ws a) → P (load_vpre ws aq) →
  (∀ (j : nat) t, ts !! j = Some t → acc_addr base j = a → P t) →
  P (coh (load_post_run ws aq base ts) a).
Proof.
  intros Hcl Hfw Hc Hv Hts.
  rewrite /load_post_run ctrl_post_coh /load_post_bytes.
  apply load_fold_coh'; [done|done|done|done|].
  intros p Hp Hpa. destruct (elem_of_run_ats base ts p Hp) as (j & _ & Ht & He).
  apply (Hts j); [exact Ht|by rewrite -He].
Qed.

Lemma load_run_vrOld P ws aq base ts :
  maxcl P → fwd0 ws → P (w_vrOld ws) → P (load_vpre ws aq) →
  (∀ (j : nat) t, ts !! j = Some t → P t) →
  P (w_vrOld (load_post_run ws aq base ts)).
Proof.
  intros Hcl Hfw Hc Hv Hts.
  rewrite /load_post_run ctrl_post_vrOld /load_post_bytes.
  apply load_fold_vrOld'; [done|done|done|done|].
  intros p Hp. destruct (elem_of_run_ats base ts p Hp) as (j & _ & Ht & _).
  by apply (Hts j).
Qed.

Lemma load_run_vrNew P ws aq base ts :
  maxcl P → fwd0 ws → P (w_vrNew ws) → P (load_vpre ws aq) →
  (∀ (j : nat) t, ts !! j = Some t → P t) →
  P (w_vrNew (load_post_run ws aq base ts)).
Proof.
  intros Hcl Hfw Hc Hv Hts.
  rewrite /load_post_run ctrl_post_vrNew /load_post_bytes.
  apply load_fold_vrNew'; [done|done|done|done|].
  intros p Hp. destruct (elem_of_run_ats base ts p Hp) as (j & _ & Ht & _).
  by apply (Hts j).
Qed.

Lemma load_run_vrNew_plain ws base ts :
  w_vrNew (load_post_run ws false base ts) = w_vrNew ws.
Proof.
  rewrite /load_post_run ctrl_post_vrNew /load_post_bytes.
  apply load_fold_vrNew_plain.
Qed.

Lemma load_run_vwOld ws aq base ts :
  w_vwOld (load_post_run ws aq base ts) = w_vwOld ws.
Proof.
  rewrite /load_post_run ctrl_post_vwOld /load_post_bytes. apply load_fold_vwOld.
Qed.

Lemma load_run_vRel ws aq base ts :
  w_vRel (load_post_run ws aq base ts) = w_vRel ws.
Proof.
  rewrite /load_post_run ctrl_post_vRel /load_post_bytes. apply load_fold_vRel.
Qed.

Lemma store_run_coh P ws rl base n t a :
  maxcl P → P (coh ws a) →
  ((∃ j : nat, (j < n)%nat ∧ acc_addr base j = a) → P t) →
  P (coh (store_post_run ws rl base n t) a).
Proof.
  intros Hcl Hc Ht. rewrite /store_post_run ctrl_post_coh /store_post_bytes.
  apply store_fold_coh; [done|done|].
  intros Hin. destruct (elem_of_run_as base n a Hin) as (j & Hj & He).
  apply Ht. by exists j.
Qed.

Lemma store_run_vwOld P ws rl base n t :
  maxcl P → P (w_vwOld ws) → P t →
  P (w_vwOld (store_post_run ws rl base n t)).
Proof.
  intros Hcl Hc Ht. rewrite /store_post_run ctrl_post_vwOld /store_post_bytes.
  by apply store_fold_vwOld.
Qed.

Lemma store_run_vRel P ws rl base n t :
  maxcl P → P (w_vRel ws) → P t →
  P (w_vRel (store_post_run ws rl base n t)).
Proof.
  intros Hcl Hc Ht. rewrite /store_post_run ctrl_post_vRel /store_post_bytes.
  by apply store_fold_vRel.
Qed.

Lemma store_run_vRel_norl ws base n t :
  w_vRel (store_post_run ws false base n t) = w_vRel ws.
Proof.
  rewrite /store_post_run ctrl_post_vRel /store_post_bytes.
  apply store_fold_vRel_norl.
Qed.

Lemma store_run_vrOld ws rl base n t :
  w_vrOld (store_post_run ws rl base n t) = w_vrOld ws.
Proof.
  rewrite /store_post_run ctrl_post_vrOld /store_post_bytes.
  apply store_fold_vrOld.
Qed.

Lemma store_run_vrNew ws rl base n t :
  w_vrNew (store_post_run ws rl base n t) = w_vrNew ws.
Proof.
  rewrite /store_post_run ctrl_post_vrNew /store_post_bytes.
  apply store_fold_vrNew.
Qed.

(** ** 3.3 The one-step wstate of the acting agent *)

Definition lstep (tw : nat) (ws : wstate) (l : lbl) : wstate :=
  match l with
  | LLoad aq base ts _ => load_post_run ws aq base ts
  | LStore rl base vs _ => store_post_run ws rl base (length vs) tw
  | LFence pr pw sr sw => fence_post ws pr pw sr sw
  | LRmw aq rl base ts _ wvs _ =>
      store_post_run (load_post_run ws aq base ts) rl base (length wvs) tw
  end.

Lemma mnext_ws_eq σ i l :
  ms_ws (mnext σ i l) i = lstep (S (length (ms_log σ))) (ms_ws σ i) l.
Proof. destruct l; simpl; by rewrite upd_ws_eq. Qed.

Lemma lstep_fwd0 tw ws l : fwd0 ws → fwd0 (lstep tw ws l).
Proof.
  intros H. destruct l; simpl.
  - by apply fwd0_load_post_run.
  - by apply fwd0_store_post_run.
  - by apply fwd0_fence_post.
  - apply fwd0_store_post_run. by apply fwd0_load_post_run.
Qed.

(* ====================================================================== *)
(** * 4. THE GRAPH SIDE: the four ppo⁻ arms as ordering facts *)

Section Graph.
  Context (G : gexec).
  Hypothesis Hwf  : gwf G.
  Hypothesis Hppo : gppo_gmo G.
  Hypothesis Hlv  : gload_value G.

  (** [gwf]'s shape clause, read at a label. *)
  Lemma gshape e l :
    gx_lbl G e = Some l →
    match l with
    | LLoad _ _ ts vs => length vs = length ts
    | LStore _ _ vs _ => vs ≠ []
    | LFence _ _ _ _ => True
    | LRmw _ _ _ ts rvs wvs _ =>
        wvs ≠ [] ∧ length wvs = length ts ∧ length rvs = length ts
    end.
  Proof.
    intros Hl. rewrite /gx_lbl in Hl.
    destruct (gx_prog G !! e.1) as [p|] eqn:Hp; simpl in Hl; [|done].
    destruct Hwf as (_ & _ & Hsh). by eapply Hsh.
  Qed.

  (** ** 4.1 The ordering arms *)

  Lemma gpoloc_gmo e1 e2 b :
    gpo G e1 e2 → gaccesses G e1 b → gaccesses G e2 b → gmo_lt G e1 e2.
  Proof. intros ???. apply Hppo. left. split; [done|]. by exists b. Qed.

  Lemma gacq_gmo e1 e2 :
    gpo G e1 e2 → glbl_is G e1 lb_is_r → glbl_is G e1 lb_aq → gmem G e2 →
    gmo_lt G e1 e2.
  Proof. intros ????. apply Hppo. right; right; left. by split_and!. Qed.

  Lemma grelacq_gmo e1 e2 :
    gpo G e1 e2 → glbl_is G e1 lb_is_w → glbl_is G e1 lb_rl →
    glbl_is G e2 lb_is_r → glbl_is G e2 lb_aq → gmo_lt G e1 e2.
  Proof. intros ?????. apply Hppo. right; right; right. by split_and!. Qed.

  Lemma gfence_gmo e1 e2 kf pr pw sr sw :
    e1.1 = e2.1 → (e1.2 < kf)%nat → (kf < e2.2)%nat →
    gx_lbl G (e1.1, kf) = Some (LFence pr pw sr sw) →
    ((glbl_is G e1 lb_is_r ∧ pr = true) ∨ (glbl_is G e1 lb_is_w ∧ pw = true)) →
    ((glbl_is G e2 lb_is_r ∧ sr = true) ∨ (glbl_is G e2 lb_is_w ∧ sw = true)) →
    gmo_lt G e1 e2.
  Proof.
    intros Hag H1 H2 Hf Hp Hs. apply Hppo. right; left.
    exists pr, pw, sr, sw. split_and!; [|exact Hp|exact Hs].
    rewrite /gfence_between. split_and!; [exact Hag|lia|].
    exists kf. split_and!; [exact H1|exact H2|exact Hf].
  Qed.

  (** ** 4.2 The source bound — [gload_value]'s existence half

    A read that is gmo-before [r] cannot see further than [r] does: its
    source is gmo-before it (the [gpo] disjunct is store forwarding, and a
    forwarded write is poloc-ordered anyway), hence gmo-before [r]. *)

  Lemma gread_src_ub (r : geid) e b t v :
    greads_byte G e b t v → gmo_lt G e r → gvis_ub G r t.
  Proof.
    intros Hr Hlt. destruct t as [|n]; [apply gvis_ub_0|].
    destruct (proj1 (Hlv e b (S n) v Hr)) as (w & Hw & Hwb & Hvis).
    assert (Hwe : gmo_lt G w e).
    { destruct Hvis as [Hv|Hv]; [exact Hv|].
      eapply gpoloc_gmo; [exact Hv|left; by exists v|right; by exists (S n), v]. }
    eapply gvis_ub_of_write; [exact Hwf|exact Hw|by eapply gmo_lt_trans].
  Qed.

  (** ** 4.3 The payoff shape — [gload_value]'s co-maximality half

    Nothing in the log at or below a [gvis_ub] bound can overwrite the
    source: it would be a gmo-visible same-byte write with a LARGER index
    than the one the read named. *)

  Lemma no_writes_in_of_ub (r : geid) b t v (log : list wmsg) n :
    greads_byte G r b t v →
    (∀ (s : nat) m, (0 < s)%nat → log !! (s - 1)%nat = Some m →
       ∀ b', is_Some (msg_byte m b') →
         ∃ w v', gwrite_at G s = Some w ∧ gwrites_byte G w b' v') →
    gvis_ub G r n → ¬ writes_in log b t n.
  Proof.
    intros Hr Hlog Hub (s & Hlo & Hhi & m & Hm & Hby).
    destruct (Hlog s m ltac:(lia) Hm b Hby) as (w & v' & Hw & Hwb).
    pose proof (Hub s w Hw Hhi) as Hgmo.
    pose proof (proj2 (Hlv r b t v Hr) w v' Hwb (or_introl Hgmo)) as Hle.
    destruct Hwf as (Hnd & _ & _).
    rewrite (proj2 (gwrite_at_inv G s w Hnd Hw)) in Hle. lia.
  Qed.
End Graph.

(* ====================================================================== *)
(** * 5. G-TRACE PREFIXES

    A candidate is a G-TRACE PREFIX when its trace is an initial segment of
    some linear extension of [G]: same image; every step is a G-event of the
    stepping agent at the row position its own earlier steps determine (so
    per hart the steps are a po-PREFIX of the row); the step's label is
    [G]'s label there (a read's [ts] entries are therefore [G]'s write
    indices); and the LOG IS THE gmo PREFIX — the [p]-th write step's message
    sits at log index [gwix G] of its event, and conversely every log index
    in range names [gwrites]'s entry there, carrying that write's bytes.

    The log clause is where rule 14 lives: it is what makes "the appended
    write is the next [gwrites] entry" a property one can maintain. *)

Definition gcnt (i : agent) (tr : list estep) : nat :=
  length (filter (λ s, es_ag s = i) tr).

Lemma gcnt_step_eq i tr k s :
  tr !! k = Some s → es_ag s = i → gcnt i (take (S k) tr) = S (gcnt i (take k tr)).
Proof.
  intros Hk Hag. rewrite /gcnt (take_S_r tr k s Hk) list_basics.filter_app
    (filter_cons_True _ s [] Hag) filter_nil length_app /=. lia.
Qed.

Lemma gcnt_step_ne i tr k s :
  tr !! k = Some s → es_ag s ≠ i → gcnt i (take (S k) tr) = gcnt i (take k tr).
Proof.
  intros Hk Hag. rewrite /gcnt (take_S_r tr k s Hk) list_basics.filter_app
    (filter_cons_False _ s [] Hag) filter_nil length_app /=. lia.
Qed.

Lemma gcnt_take_le i tr k : (gcnt i (take k tr) ≤ gcnt i tr)%nat.
Proof.
  rewrite /gcnt -{2}(take_drop k tr) list_basics.filter_app length_app. lia.
Qed.

(** The message a graph write contributes to the log — [WeakAxiomatic2.es_msg]
    read off the graph label. *)
Definition gwmsg (G : gexec) (w : geid) : option wmsg :=
  match gx_lbl G w with
  | Some l =>
      match lb_wr l with
      | Some (base, vs) => Some (WMsg base vs (Some w.1) (lb_cls l))
      | None => None
      end
  | None => None
  end.

Record gtrace_prefix (G : gexec) (c : cand) (ev : nat → geid) : Prop := {
  gtp_img : cd_img c = gx_img G;
  gtp_ag  : ∀ p s, cd_tr c !! p = Some s → (ev p).1 = es_ag s;
  gtp_pos : ∀ p s, cd_tr c !! p = Some s →
              (ev p).2 = gcnt (es_ag s) (take p (cd_tr c));
  gtp_lbl : ∀ p s, cd_tr c !! p = Some s → gx_lbl G (ev p) = Some (es_lb s);
  gtp_wix : ∀ p s, cd_tr c !! p = Some s → lb_is_w (es_lb s) = true →
              gwix G (ev p) = S (length (cd_log c p));
  gtp_log : ∀ s : nat, (0 < s)%nat →
              (s ≤ length (cd_log c (length (cd_tr c))))%nat →
              ∃ w, gwrite_at G s = Some w ∧
                   cd_log c (length (cd_tr c)) !! (s - 1)%nat = gwmsg G w;
}.

Lemma gtp_ev_eq G c ev p s :
  gtrace_prefix G c ev → cd_tr c !! p = Some s →
  ev p = (es_ag s, gcnt (es_ag s) (take p (cd_tr c))).
Proof.
  intros [_ Hag Hpos _ _ _] Hs.
  rewrite (surjective_pairing (ev p)) (Hag p s Hs) (Hpos p s Hs) //.
Qed.

(** THE LOG DICTIONARY, log → graph: every message in the log is a
    [gwrites] entry's message, at its own [gwix]. *)
Lemma gtp_log_writes G c ev :
  gtrace_prefix G c ev →
  ∀ (s : nat) m, (0 < s)%nat →
    cd_log c (length (cd_tr c)) !! (s - 1)%nat = Some m →
    ∀ b, is_Some (msg_byte m b) →
      ∃ w v', gwrite_at G s = Some w ∧ gwrites_byte G w b v'.
Proof.
  intros Hgt s m Hs Hm b [v Hv].
  have Hle : (s ≤ length (cd_log c (length (cd_tr c))))%nat.
  { apply lookup_lt_Some in Hm. lia. }
  destruct Hgt as [_ _ _ _ _ Hlog].
  destruct (Hlog s Hs Hle) as (w & Hw & Heq).
  rewrite Hm in Heq. symmetry in Heq. rewrite /gwmsg in Heq.
  destruct (gx_lbl G w) as [l|] eqn:Hl; [|done].
  destruct (lb_wr l) as [[base vs]|] eqn:Hwr; [|done].
  injection Heq as <-. rewrite /msg_byte /= in Hv.
  case_bool_decide as Hb; [|done].
  exists w, v. split; [exact Hw|].
  exists l, base, vs, (Z.to_nat (b - base)). split_and!;
    [exact Hl|exact Hwr|exact Hv|].
  rewrite /acc_addr Z2Nat.id; lia.
Qed.

(** THE LOG DICTIONARY, graph → log: a [gwrites] entry in range carries its
    bytes at its own index.  (The value half of an appended read.) *)
Lemma gtp_log_byte G c ev :
  gtrace_prefix G c ev →
  ∀ (s : nat) w b v, (0 < s)%nat →
    (s ≤ length (cd_log c (length (cd_tr c))))%nat →
    gwrite_at G s = Some w → gwrites_byte G w b v →
    log_byte (cd_img c) (cd_log c (length (cd_tr c))) s b = Some v.
Proof.
  intros Hgt s w b v Hs Hle Hw (l & base & vs & j & Hl & Hwr & Hj & Hb).
  destruct Hgt as [_ _ _ _ _ Hlog].
  destruct (Hlog s Hs Hle) as (w' & Hw' & Heq).
  rewrite Hw in Hw'. injection Hw' as <-.
  rewrite /gwmsg Hl Hwr in Heq.
  destruct s as [|n]; [lia|]. rewrite log_byte_S.
  replace (S n - 1)%nat with n in Heq by lia. rewrite Heq /= /msg_byte /=.
  case_bool_decide as Hba; last first.
  { exfalso. apply Hba. rewrite -Hb /acc_addr. lia. }
  rewrite -Hb.
  replace (Z.to_nat (acc_addr base j - base)) with j by (rewrite /acc_addr; lia).
  exact Hj.
Qed.

(* ====================================================================== *)
(** * 6. THE INVARIANT AND ITS INDUCTION

    [r] is the read whose floor is to be discharged, [a] one of its bytes.
    [finv k ws] says what the agent's own view components can hold after its
    first [k] row events.  Two of the six clauses are CONDITIONAL, and the
    conditions are exactly the two ppo⁻ arms that publish a watermark:

      [fhook k pb] — a fence at a row position ≥ [k] and before [r], with
                     the predecessor bit [pb] (read / write) and [sr] set:
                     it is what will carry [w_vrOld] / [w_vwOld] into
                     [w_vrNew], and rule 4 then orders the raiser before [r].
      [ahook k]    — an acquire read at a row position ≥ [k] that is [r] or
                     is gmo-before [r]: it is what will consume [w_vRel],
                     and rule 7 orders the release that raised it before it.

    Both are ANTI-monotone in [k], which is what makes the induction go. *)

Section Floor.
  Context (G : gexec).
  Hypothesis Hwf  : gwf G.
  Hypothesis Hppo : gppo_gmo G.
  Hypothesis Hlv  : gload_value G.
  Context (r : geid) (a : Z).
  Hypothesis Hrr : glbl_is G r lb_is_r.
  Hypothesis Hra : gaccesses G r a.

  Local Lemma Hrsome : is_Some (gx_lbl G r).
  Proof. destruct Hrr as (l & Hl & _). by exists l. Qed.

  Local Lemma Hrmem : gmem G r.
  Proof. by apply glbl_is_r_gmem. Qed.

  Definition fhook (k : nat) (pb : bool) : Prop :=
    ∃ (kf : nat) (pr pw sr sw : bool), (k ≤ kf)%nat ∧ (kf < r.2)%nat ∧
      gx_lbl G (r.1, kf) = Some (LFence pr pw sr sw) ∧
      (if pb then pr else pw) = true ∧ sr = true.

  Definition ahook (k : nat) : Prop :=
    ∃ kf : nat, (k ≤ kf)%nat ∧
      glbl_is G (r.1, kf) lb_is_r ∧ glbl_is G (r.1, kf) lb_aq ∧
      ((r.1, kf) = r ∨ gmo_lt G (r.1, kf) r).

  Lemma fhook_S k pb : fhook (S k) pb → fhook k pb.
  Proof.
    intros (kf & pr & pw & sr & sw & H1 & H2 & H3 & H4 & H5).
    exists kf, pr, pw, sr, sw. split_and!; [lia|exact H2|exact H3|exact H4|exact H5].
  Qed.

  Lemma ahook_S k : ahook (S k) → ahook k.
  Proof.
    intros (kf & H1 & H2 & H3 & H4). exists kf. split_and!;
      [lia|exact H2|exact H3|exact H4].
  Qed.

  Definition finv (k : nat) (ws : wstate) : Prop :=
    fwd0 ws ∧
    gvis_ub G r (coh ws a) ∧
    gvis_ub G r (w_vrNew ws) ∧
    (ahook k → gvis_ub G r (w_vRel ws)) ∧
    (fhook k true → gvis_ub G r (w_vrOld ws)) ∧
    (fhook k false → gvis_ub G r (w_vwOld ws)).

  Lemma finv_init : finv 0%nat ws_init.
  Proof.
    rewrite /finv coh_init. split_and!;
      [apply fwd0_init|apply gvis_ub_0|apply gvis_ub_0
      |intros _; apply gvis_ub_0|intros _; apply gvis_ub_0
      |intros _; apply gvis_ub_0].
  Qed.

  (** ** 6.1 THE STEP.  One row event of [r]'s own hart, at row position
      [k < r.2], preserves the invariant. *)

  Lemma finv_step k l ws tw :
    (k < r.2)%nat →
    gx_lbl G (r.1, k) = Some l →
    (lb_is_w l = true → gwix G (r.1, k) = tw) →
    finv k ws → finv (S k) (lstep tw ws l).
  Proof.
    intros Hk Hl Htw (Hfw & Hcoh & Hrn & Hrel & Hro & Hwo).
    have Hcl : maxcl (gvis_ub G r) := gvis_ub_maxcl G r.
    have Hesome : is_Some (gx_lbl G (r.1, k)) by exists l.
    have Hpo : gpo G (r.1, k) r.
    { rewrite /gpo /=. split_and!; [done|exact Hk|exact Hesome|apply Hrsome]. }
    (* the four ordering arms, as they apply to THIS event *)
    have Hoacc : gaccesses G (r.1, k) a → gmo_lt G (r.1, k) r.
    { intros Hacc. exact (gpoloc_gmo G Hppo _ _ a Hpo Hacc Hra). }
    have Hoaq : glbl_is G (r.1, k) lb_is_r → glbl_is G (r.1, k) lb_aq →
                gmo_lt G (r.1, k) r.
    { intros H1 H2. exact (gacq_gmo G Hppo _ _ Hpo H1 H2 Hrmem). }
    have Hof : ∀ pb, fhook (S k) pb →
      (if pb then glbl_is G (r.1, k) lb_is_r else glbl_is G (r.1, k) lb_is_w) →
      gmo_lt G (r.1, k) r.
    { intros pb (kf & pr & pw & sr & sw & Hk1 & Hk2 & Hf & Hpb & Hsr) Hcls.
      apply (gfence_gmo G Hppo (r.1, k) r kf pr pw sr sw);
        [done|simpl; lia|exact Hk2|exact Hf| |].
      - destruct pb; [left|right]; by split.
      - left. by split. }
    have Horl : ahook (S k) → glbl_is G (r.1, k) lb_is_w →
                glbl_is G (r.1, k) lb_rl → gmo_lt G (r.1, k) r.
    { intros (kf & Hk1 & Hr1 & Hr2 & Hle) Hw Hrl.
      have Hpo2 : gpo G (r.1, k) (r.1, kf).
      { rewrite /gpo /=. split_and!; [done|lia|exact Hesome|].
        by destruct Hr1 as (l' & Hl' & _); exists l'. }
      have Hlt := grelacq_gmo G Hppo _ _ Hpo2 Hw Hrl Hr1 Hr2.
      destruct Hle as [Heq|Hlt2]; [by rewrite Heq in Hlt|by eapply gmo_lt_trans]. }
    (* the two byte dictionaries and the two index bounds *)
    have Hacc_rd : ∀ base ts vs (j : nat) t',
        lb_rd l = Some (base, ts, vs) → length vs = length ts →
        ts !! j = Some t' → gaccesses G (r.1, k) (acc_addr base j).
    { intros base ts vs j t' Hrd Hlen Hj.
      have Hjlt : (j < length vs)%nat by (rewrite Hlen; eapply lookup_lt_Some).
      destruct (lookup_lt_is_Some_2 vs j Hjlt) as [v' Hv'].
      right. exists t', v'. by exists l, base, ts, vs, j. }
    have Hsrc : ∀ base ts vs (j : nat) t',
        lb_rd l = Some (base, ts, vs) → length vs = length ts →
        gmo_lt G (r.1, k) r → ts !! j = Some t' → gvis_ub G r t'.
    { intros base ts vs j t' Hrd Hlen Hord Hj.
      have Hjlt : (j < length vs)%nat by (rewrite Hlen; eapply lookup_lt_Some).
      destruct (lookup_lt_is_Some_2 vs j Hjlt) as [v' Hv'].
      apply (gread_src_ub G Hwf Hppo Hlv r (r.1, k) (acc_addr base j) t' v');
        [by exists l, base, ts, vs, j|exact Hord]. }
    have Hacc_wr : ∀ base vs (j : nat),
        lb_wr l = Some (base, vs) → (j < length vs)%nat →
        gaccesses G (r.1, k) (acc_addr base j).
    { intros base vs j Hwr Hj.
      destruct (lookup_lt_is_Some_2 vs j Hj) as [v' Hv'].
      left. exists v'. by exists l, base, vs, j. }
    have Hwix : lb_is_w l = true → gmo_lt G (r.1, k) r → gvis_ub G r tw.
    { intros Hw Hord.
      have Hg : (r.1, k) ∈ gwrites G.
      { eapply gis_w_gwrites; [exact Hwf|exact Hesome|by rewrite /gis_w Hl]. }
      apply (gvis_ub_of_write G r tw (r.1, k)); [exact Hwf| |exact Hord].
      rewrite -(Htw Hw). by apply gwrite_at_gwix. }
    destruct l as [aq base ts vs|rl base vs kc|pr pw sr sw|
                   aq rl base ts rvs wvs kc].
    - (* ---------------- LLoad ---------------- *)
      have Hlen : length vs = length ts := gshape G Hwf _ _ Hl.
      have Hisr : glbl_is G (r.1, k) lb_is_r by (exists (LLoad aq base ts vs)).
      have Hvpre : gvis_ub G r (load_vpre ws aq).
      { rewrite /load_vpre. apply maxcl_max; [exact Hcl|exact Hrn|].
        destruct aq; [|apply gvis_ub_0].
        apply Hrel. exists k. split_and!;
          [lia|exact Hisr|by exists (LLoad true base ts vs)|right].
        apply Hoaq; [exact Hisr|by exists (LLoad true base ts vs)]. }
      simpl. split_and!.
      + by apply fwd0_load_post_run.
      + apply load_run_coh; [exact Hcl|exact Hfw|exact Hcoh|exact Hvpre|].
        intros j t' Hj Hja.
        have Hord : gmo_lt G (r.1, k) r.
        { apply Hoacc. rewrite -Hja. by apply (Hacc_rd base ts vs j t'). }
        by apply (Hsrc base ts vs j t').
      + destruct aq.
        * apply load_run_vrNew; [exact Hcl|exact Hfw|exact Hrn|exact Hvpre|].
          intros j t' Hj.
          have Hord : gmo_lt G (r.1, k) r.
          { apply Hoaq; [exact Hisr|by exists (LLoad true base ts vs)]. }
          by apply (Hsrc base ts vs j t').
        * rewrite load_run_vrNew_plain. exact Hrn.
      + rewrite load_run_vRel. intros Hah. by apply Hrel, ahook_S.
      + intros Hfh. apply load_run_vrOld;
          [exact Hcl|exact Hfw|by apply Hro, fhook_S|exact Hvpre|].
        intros j t' Hj.
        have Hord : gmo_lt G (r.1, k) r := Hof true Hfh Hisr.
        by apply (Hsrc base ts vs j t').
      + rewrite load_run_vwOld. intros Hfh. by apply Hwo, fhook_S.
    - (* ---------------- LStore ---------------- *)
      have Hisw : glbl_is G (r.1, k) lb_is_w by (exists (LStore rl base vs kc)).
      simpl. split_and!.
      + by apply fwd0_store_post_run.
      + apply store_run_coh; [exact Hcl|exact Hcoh|].
        intros (j & Hj & Hja). apply (Hwix eq_refl).
        apply Hoacc. rewrite -Hja. by apply (Hacc_wr base vs j).
      + rewrite store_run_vrNew. exact Hrn.
      + intros Hah. destruct rl.
        * apply store_run_vRel; [exact Hcl|by apply Hrel, ahook_S|].
          apply (Hwix eq_refl). apply (Horl Hah Hisw).
          by exists (LStore true base vs kc).
        * rewrite store_run_vRel_norl. by apply Hrel, ahook_S.
      + rewrite store_run_vrOld. intros Hfh. by apply Hro, fhook_S.
      + intros Hfh. apply store_run_vwOld;
          [exact Hcl|by apply Hwo, fhook_S|].
        apply (Hwix eq_refl). exact (Hof false Hfh Hisw).
    - (* ---------------- LFence ---------------- *)
      simpl. split_and!.
      + by apply fwd0_fence_post.
      + exact Hcoh.
      + apply fence_post_vrNew_pred; [exact Hcl|exact Hrn| |].
        * intros Hpr Hsr. apply Hro. exists k, pr, pw, sr, sw.
          split_and!; [lia|exact Hk|exact Hl|exact Hpr|exact Hsr].
        * intros Hpw Hsr. apply Hwo. exists k, pr, pw, sr, sw.
          split_and!; [lia|exact Hk|exact Hl|exact Hpw|exact Hsr].
      + intros Hah. by apply Hrel, ahook_S.
      + intros Hfh. by apply Hro, fhook_S.
      + intros Hfh. by apply Hwo, fhook_S.
    - (* ---------------- LRmw ---------------- *)
      destruct (gshape G Hwf _ _ Hl) as (Hne & Hlenw & Hlenr).
      have Hisr : glbl_is G (r.1, k) lb_is_r
        by (exists (LRmw aq rl base ts rvs wvs kc)).
      have Hisw : glbl_is G (r.1, k) lb_is_w
        by (exists (LRmw aq rl base ts rvs wvs kc)).
      have Hvpre : gvis_ub G r (load_vpre ws aq).
      { rewrite /load_vpre. apply maxcl_max; [exact Hcl|exact Hrn|].
        destruct aq; [|apply gvis_ub_0].
        apply Hrel. exists k. split_and!;
          [lia|exact Hisr|by exists (LRmw true rl base ts rvs wvs kc)|right].
        apply Hoaq; [exact Hisr|by exists (LRmw true rl base ts rvs wvs kc)]. }
      have Hfw1 : fwd0 (load_post_run ws aq base ts)
        by apply fwd0_load_post_run.
      simpl. split_and!.
      + by apply fwd0_store_post_run.
      + apply store_run_coh; [exact Hcl| |].
        * apply load_run_coh; [exact Hcl|exact Hfw|exact Hcoh|exact Hvpre|].
          intros j t' Hj Hja.
          have Hord : gmo_lt G (r.1, k) r.
          { apply Hoacc. rewrite -Hja. by apply (Hacc_rd base ts rvs j t'). }
          by apply (Hsrc base ts rvs j t').
        * intros (j & Hj & Hja). apply (Hwix eq_refl).
          apply Hoacc. rewrite -Hja. by apply (Hacc_wr base wvs j).
      + rewrite store_run_vrNew. destruct aq.
        * apply load_run_vrNew; [exact Hcl|exact Hfw|exact Hrn|exact Hvpre|].
          intros j t' Hj.
          have Hord : gmo_lt G (r.1, k) r.
          { apply Hoaq; [exact Hisr|by exists (LRmw true rl base ts rvs wvs kc)]. }
          by apply (Hsrc base ts rvs j t').
        * rewrite load_run_vrNew_plain. exact Hrn.
      + intros Hah. destruct rl.
        * apply store_run_vRel; [exact Hcl| |].
          { rewrite load_run_vRel. by apply Hrel, ahook_S. }
          apply (Hwix eq_refl). apply (Horl Hah Hisw).
          by exists (LRmw aq true base ts rvs wvs kc).
        * rewrite store_run_vRel_norl load_run_vRel. by apply Hrel, ahook_S.
      + rewrite store_run_vrOld. intros Hfh.
        apply load_run_vrOld;
          [exact Hcl|exact Hfw|by apply Hro, fhook_S|exact Hvpre|].
        intros j t' Hj.
        have Hord : gmo_lt G (r.1, k) r := Hof true Hfh Hisr.
        by apply (Hsrc base ts rvs j t').
      + intros Hfh. apply store_run_vwOld; [exact Hcl| |].
        * rewrite load_run_vwOld. by apply Hwo, fhook_S.
        * apply (Hwix eq_refl). exact (Hof false Hfh Hisw).
  Qed.

  (** ** 6.2 THE INDUCTION over the candidate's trace *)

  Lemma finv_replay c ev p :
    gtrace_prefix G c ev →
    (gcnt r.1 (cd_tr c) ≤ r.2)%nat →
    (p ≤ length (cd_tr c))%nat →
    finv (gcnt r.1 (take p (cd_tr c))) (ms_ws (stt (cand_exec c) p) r.1).
  Proof.
    intros Hgt Hcnt. induction p as [|p IH]; intros Hp.
    - have Hσ : stt (cand_exec c) 0%nat = cand_init c
        by (apply stt_lookup; exact (replay_0 (cand_init c) (cd_tr c))).
      rewrite Hσ take_0 /=. apply finv_init.
    - destruct (lookup_lt_is_Some_2 (cd_tr c) p ltac:(lia)) as [s Hs].
      have Hlog : ms_log (stt (cand_exec c) p) = cd_log c p.
      { rewrite -(cand_elog c p ltac:(lia)) //. }
      rewrite (cand_next c p s Hs).
      destruct (decide (es_ag s = r.1)) as [Hag|Hag].
      + rewrite (gcnt_step_eq r.1 (cd_tr c) p s Hs Hag) Hag mnext_ws_eq.
        have Hev : ev p = (r.1, gcnt r.1 (take p (cd_tr c))).
        { rewrite (gtp_ev_eq G c ev p s Hgt Hs) Hag //. }
        apply (finv_step (gcnt r.1 (take p (cd_tr c))) (es_lb s)).
        * have Hle := gcnt_take_le r.1 (cd_tr c) (S p).
          rewrite (gcnt_step_eq r.1 (cd_tr c) p s Hs Hag) in Hle. lia.
        * rewrite -Hev. destruct Hgt as [_ _ _ Hlbl _ _]. by apply Hlbl.
        * intros Hw. rewrite -Hev Hlog.
          destruct Hgt as [_ _ _ _ Hwix _]. by apply (Hwix p s Hs Hw).
        * apply IH. lia.
      + rewrite (gcnt_step_ne r.1 (cd_tr c) p s Hs Hag).
        rewrite (mnext_ws_ne (stt (cand_exec c) p) (es_ag s) (es_lb s) r.1
                  (λ H, Hag (eq_sym H))).
        apply IH. lia.
  Qed.

  (** ** 6.3 THE FLOOR DISCHARGE *)

  Theorem floor_of_graph_sec c ev (aq : bool) t v :
    gtrace_prefix G c ev →
    r.2 = gcnt r.1 (cd_tr c) →
    greads_byte G r a t v →
    (aq = true → glbl_is G r lb_aq) →
    ¬ writes_in (cd_log c (length (cd_tr c))) a t
        (Nat.max
           (load_vpre (ms_ws (stt (cand_exec c) (length (cd_tr c))) r.1) aq)
           (coh (ms_ws (stt (cand_exec c) (length (cd_tr c))) r.1) a)).
  Proof.
    intros Hgt Hr2 Hrb Haq.
    have Hcl : maxcl (gvis_ub G r) := gvis_ub_maxcl G r.
    have Hrp : (r.1, r.2) = r := eq_sym (surjective_pairing r).
    have Hte : take (length (cd_tr c)) (cd_tr c) = cd_tr c
      by (apply take_ge; lia).
    have Hinv := finv_replay c ev (length (cd_tr c)) Hgt ltac:(lia) ltac:(lia).
    rewrite Hte -Hr2 in Hinv.
    destruct Hinv as (_ & Hcoh & Hrn & Hrel & _ & _).
    apply (no_writes_in_of_ub G Hwf Hlv r a t v); [exact Hrb| |].
    - by apply (gtp_log_writes G c ev).
    - apply maxcl_max; [exact Hcl| |exact Hcoh].
      rewrite /load_vpre. apply maxcl_max; [exact Hcl|exact Hrn|].
      destruct aq; [|apply gvis_ub_0].
      apply Hrel. exists r.2. split_and!; [lia|rewrite Hrp; exact Hrr| |left].
      + rewrite Hrp. by apply Haq.
      + exact Hrp.
  Qed.
End Floor.

(* ====================================================================== *)
(** * 7. THE FLOOR DISCHARGE, PACKAGED

    [grule14] is deliberately NOT a hypothesis: the floor follows from
    [rvwmo_minus_consistent] alone.  Rule 14 is what makes a candidate's log
    a gmo PREFIX in the first place — it is the content of [gtp_wix]/
    [gtp_log], i.e. of "the appended write is the next [gwrites] entry" —
    and it enters T2-1c′ there, on the write side. *)

Theorem floor_of_graph G c ev (i : agent) (r : geid) (a : Z) (t : nat)
    (v : bv 8) (aq : bool) :
  rvwmo_minus_consistent G →
  gtrace_prefix G c ev →
  r = (i, gcnt i (cd_tr c)) →
  greads_byte G r a t v →
  (aq = true → glbl_is G r lb_aq) →
  ¬ writes_in (cd_log c (length (cd_tr c))) a t
      (Nat.max (load_vpre (ms_ws (stt (cand_exec c) (length (cd_tr c))) i) aq)
               (coh (ms_ws (stt (cand_exec c) (length (cd_tr c))) i) a)).
Proof.
  intros (Hwf & Hppo & Hlv & _) Hgt Hr Hrb Haq.
  have Hrr : glbl_is G r lb_is_r.
  { destruct Hrb as (l & base & ts & vs & j & Hl & Hrd & _).
    exists l. split; [exact Hl|]. destruct l; simplify_eq/=; done. }
  have Hra : gaccesses G r a by (right; by exists t, v).
  have Hi : r.1 = i by rewrite Hr.
  have Hk : r.2 = gcnt r.1 (cd_tr c) by rewrite Hi Hr.
  rewrite -Hi.
  exact (floor_of_graph_sec G Hwf Hppo Hlv r a Hrr Hra c ev aq t v Hgt Hk
           Hrb Haq).
Qed.

(* ====================================================================== *)
(** * 8. THE TWO INDUCTION STEPS OF T2-1c′

    From here on the file is in [WeakRvwmoCert]'s import context, so the
    [WeakPromise] WLABEL constructors are the unqualified ones and the
    axiomatic label constructors are written qualified — the same discipline
    [WeakRvwmoCert] itself follows. *)
Require Import WeakSrvwmoLitmus.
Require Import WeakRvwmoCert.

(** The event naming of a snoc: the old naming below the end, the appended
    event at it. *)
Definition ev_snoc (c : cand) (ev : nat → geid) (e : geid) : nat → geid :=
  λ p, if bool_decide (p < length (cd_tr c))%nat then ev p else e.

Lemma ev_snoc_lt c ev e p : (p < length (cd_tr c))%nat → ev_snoc c ev e p = ev p.
Proof. intros H. rewrite /ev_snoc bool_decide_eq_true_2 //. Qed.

Lemma ev_snoc_end c ev e : ev_snoc c ev e (length (cd_tr c)) = e.
Proof. rewrite /ev_snoc bool_decide_eq_false_2 //. lia. Qed.

(** ** 8.1 A G-trace prefix extends by one step *)

Lemma gtrace_prefix_snoc G c ev i l :
  gwf G →
  gtrace_prefix G c ev →
  gx_lbl G (i, gcnt i (cd_tr c)) = Some l →
  (lb_is_w l = true →
     gwix G (i, gcnt i (cd_tr c)) = S (length (cd_log_end c))) →
  gtrace_prefix G (cand_snoc c (EStep i l))
    (ev_snoc c ev (i, gcnt i (cd_tr c))).
Proof.
  intros Hwf Hgt Hl Hix.
  have Hte : take (length (cd_tr c)) (cd_tr c) = cd_tr c
    by (apply take_ge; lia).
  destruct Hgt as [Himg Hag Hpos Hlbl Hwix Hlog].
  (* the three "below the end" transports, once *)
  have Hlt : ∀ p s, cd_tr (cand_snoc c (EStep i l)) !! p = Some s →
    (p < length (cd_tr c))%nat →
    cd_tr c !! p = Some s ∧ ev_snoc c ev (i, gcnt i (cd_tr c)) p = ev p ∧
    take p (cd_tr (cand_snoc c (EStep i l))) = take p (cd_tr c) ∧
    cd_log (cand_snoc c (EStep i l)) p = cd_log c p.
  { intros p s Hs Hp. rewrite cand_snoc_tr_lt // in Hs.
    split_and!; [exact Hs|by apply ev_snoc_lt|
      rewrite /= take_app_le //; lia|apply cand_snoc_log; rewrite /cd_end; lia]. }
  have Hend : ∀ p s, cd_tr (cand_snoc c (EStep i l)) !! p = Some s →
    ¬ (p < length (cd_tr c))%nat → p = length (cd_tr c) ∧ s = EStep i l.
  { intros p s Hs Hp. pose proof (lookup_lt_Some _ _ _ Hs) as Hb.
    rewrite cand_snoc_tr length_app /= in Hb.
    have Hpe : p = length (cd_tr c) by lia. subst p.
    split; [done|]. move: Hs. rewrite cand_snoc_tr
      (lookup_app_r (cd_tr c) [EStep i l] (length (cd_tr c)) (Nat.le_refl _))
      Nat.sub_diag /=. by intros [= <-]. }
  split.
  - by rewrite cand_snoc_img.
  - intros p s Hs. destruct (decide (p < length (cd_tr c))%nat) as [Hp|Hp].
    + destruct (Hlt p s Hs Hp) as (Hs' & Hev & _ & _). rewrite Hev. by apply Hag.
    + destruct (Hend p s Hs Hp) as (-> & ->). by rewrite ev_snoc_end.
  - intros p s Hs. destruct (decide (p < length (cd_tr c))%nat) as [Hp|Hp].
    + destruct (Hlt p s Hs Hp) as (Hs' & Hev & Htk & _).
      rewrite Hev Htk. by apply Hpos.
    + destruct (Hend p s Hs Hp) as (-> & ->).
      rewrite ev_snoc_end /= take_app_le // Hte //.
  - intros p s Hs. destruct (decide (p < length (cd_tr c))%nat) as [Hp|Hp].
    + destruct (Hlt p s Hs Hp) as (Hs' & Hev & _ & _). rewrite Hev. by apply Hlbl.
    + destruct (Hend p s Hs Hp) as (-> & ->). by rewrite ev_snoc_end.
  - intros p s Hs Hw. destruct (decide (p < length (cd_tr c))%nat) as [Hp|Hp].
    + destruct (Hlt p s Hs Hp) as (Hs' & Hev & _ & Hlg).
      rewrite Hev Hlg. by apply (Hwix p s Hs' Hw).
    + destruct (Hend p s Hs Hp) as (-> & ->). rewrite ev_snoc_end.
      rewrite (cand_snoc_log c (EStep i l) (length (cd_tr c)) (Nat.le_refl _)).
      by apply Hix.
  - (* the log clause *)
    intros s Hs Hle.
    have Hlen : length (cd_tr (cand_snoc c (EStep i l)))
              = S (length (cd_tr c)) by rewrite /= length_app /=; lia.
    have Hlg : cd_log (cand_snoc c (EStep i l))
                 (length (cd_tr (cand_snoc c (EStep i l))))
             = cd_log_end c ++ es_msg (EStep i l).
    { rewrite -(cd_log_end_snoc c (EStep i l)) /cd_log_end /cd_end Hlen //. }
    rewrite Hlg. rewrite Hlg in Hle.
    destruct (decide (s ≤ length (cd_log_end c))%nat) as [Hin|Hin].
    + destruct (Hlog s Hs ltac:(rewrite /cd_log_end /cd_end in Hin; exact Hin))
        as (w & Hw & Heq).
      exists w. split; [exact Hw|]. rewrite lookup_app_l; [|lia].
      rewrite -Heq /cd_log_end /cd_end //.
    + (* the appended message *)
      rewrite length_app in Hle.
      have Hwl : lb_is_w l = true.
      { destruct (lb_wr l) as [[base vs]|] eqn:Hwr.
        - by destruct l; simplify_eq/=.
        - exfalso. rewrite /es_msg /= Hwr /= in Hle. lia. }
      destruct (lb_is_w_wr l Hwl) as (base & vs & Hwr).
      have Hmsg : es_msg (EStep i l) = [WMsg base vs (Some i) (lb_cls l)]
        by rewrite /es_msg /= Hwr.
      rewrite Hmsg /= in Hle.
      have -> : s = S (length (cd_log_end c)) by lia.
      have Hgw : (i, gcnt i (cd_tr c)) ∈ gwrites G.
      { eapply gis_w_gwrites; [exact Hwf|by exists l|by rewrite /gis_w Hl]. }
      exists (i, gcnt i (cd_tr c)). split.
      * rewrite -(Hix Hwl). by apply gwrite_at_gwix.
      * rewrite Hmsg Nat.sub_succ Nat.sub_0_r.
        rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag /=.
        by rewrite /gwmsg Hl Hwr.
Qed.

(** ** 8.2 The read step

    All three clauses of [WeakRvwmoCert.snoc_rd_adm] at once: the shape
    clause is [gwf]'s, the VALUE clause is [gload_value]'s existence half
    read through the log dictionary, and the FLOOR clause is §7. *)

Theorem gtrace_snoc_read_consistent G c ev (i : agent) (aq : bool)
    (base : Z) (ts : list nat) (vs : list (bv 8)) :
  rvwmo_minus_consistent G →
  srvwmo_consistent c →
  gtrace_prefix G c ev →
  gx_lbl G (i, gcnt i (cd_tr c)) = Some (WeakAxiomatic.LLoad aq base ts vs) →
  (∀ (j : nat) t, ts !! j = Some t → (t ≤ length (cd_log_end c))%nat) →
  srvwmo_consistent
    (cand_snoc c (EStep i (WeakAxiomatic.LLoad aq base ts vs))) ∧
  gtrace_prefix G (cand_snoc c (EStep i (WeakAxiomatic.LLoad aq base ts vs)))
    (ev_snoc c ev (i, gcnt i (cd_tr c))).
Proof.
  intros Hcons Hc Hgt Hl Hsrc.
  destruct Hcons as (Hwf & Hppo & Hlv & Hat).
  have Hce : cd_log_end c = cd_log c (length (cd_tr c)) := eq_refl.
  have Hlen : length vs = length ts
    := gshape G Hwf (i, gcnt i (cd_tr c)) _ Hl.
  have Hrb : ∀ (j : nat) t v, ts !! j = Some t → vs !! j = Some v →
    greads_byte G (i, gcnt i (cd_tr c)) (acc_addr base j) t v.
  { intros j t v Hj Hv.
    by exists (WeakAxiomatic.LLoad aq base ts vs), base, ts, vs, j. }
  split; [|by eapply gtrace_prefix_snoc].
  apply snoc_read_consistent; [exact Hc|]. split_and!.
  - exact Hlen.
  - intros j t v Hj Hv.
    pose proof (proj1 (Hlv _ _ _ _ (Hrb j t v Hj Hv))) as Hval.
    destruct t as [|n].
    + rewrite /log_byte. destruct Hgt as [Himg _ _ _ _ _]. by rewrite Himg.
    + destruct Hval as (w & Hw & Hwb & _).
      rewrite Hce.
      apply (gtp_log_byte G c ev Hgt (S n) w (acc_addr base j) v);
        [lia| |exact Hw|exact Hwb].
      rewrite -Hce. by eapply Hsrc.
  - intros j t Hj.
    apply (floor_of_graph G c ev i (i, gcnt i (cd_tr c)) (acc_addr base j) t
             (default (bv_0 8) (vs !! j)) aq);
      [by split_and!|exact Hgt|done| |].
    + destruct (lookup_lt_is_Some_2 vs j
                  ltac:(rewrite Hlen; by eapply lookup_lt_Some)) as [v Hv].
      rewrite Hv /=. by apply Hrb.
    + intros ->. by exists (WeakAxiomatic.LLoad true base ts vs).
Qed.

(** ** 8.3 The write step

    Consistency is free ([WeakRvwmoCert.snoc_write_consistent]: a store has
    exactly one side condition, and rule 14 is trace order).  The CONTENT is
    the prefix extension: the appended write is [gwrites]'s next entry, so
    its [gwix] IS its log index and the log stays the gmo prefix. *)

Theorem gtrace_snoc_write_consistent G c ev (i : agent) (rl : bool)
    (base : Z) (vs : list (bv 8)) (kc : wm_class) :
  gwf G →
  srvwmo_consistent c →
  gtrace_prefix G c ev →
  gx_lbl G (i, gcnt i (cd_tr c)) = Some (WeakAxiomatic.LStore rl base vs kc) →
  gwix G (i, gcnt i (cd_tr c)) = S (length (cd_log_end c)) →
  srvwmo_consistent
    (cand_snoc c (EStep i (WeakAxiomatic.LStore rl base vs kc))) ∧
  gtrace_prefix G (cand_snoc c (EStep i (WeakAxiomatic.LStore rl base vs kc)))
    (ev_snoc c ev (i, gcnt i (cd_tr c))).
Proof.
  intros Hwf Hc Hgt Hl Hix.
  have Hne : vs ≠ [] := gshape G Hwf (i, gcnt i (cd_tr c)) _ Hl.
  split.
  - by apply snoc_write_consistent.
  - eapply gtrace_prefix_snoc; [exact Hwf|exact Hgt|exact Hl|by intros _].
Qed.

(* ====================================================================== *)
(** * 9. NON-VACUITY

    The empty candidate over [G]'s image is a G-trace prefix of every
    well-formed [G] (all five step clauses quantify over a step that does not
    exist; the log clause over an index that is not in range) — and §8.2 then
    APPENDS, at any hart, its whole first read whenever that read takes the
    era-initial image.  So the hypotheses of the two induction steps are
    jointly satisfiable, at a real graph read, with no litmus-specific data. *)

Lemma gtrace_prefix_empty G :
  gtrace_prefix G (Cand (gx_img G) []) (λ _, (0%nat, 0%nat)).
Proof.
  split.
  - done.
  - by intros [|p] s Hs.
  - by intros [|p] s Hs.
  - by intros [|p] s Hs.
  - by intros [|p] s Hs.
  - intros s Hs Hle. rewrite /cd_log /= in Hle. lia.
Qed.

Corollary gtrace_snoc_read_image G (i : agent) (aq : bool) (base : Z)
    (ts : list nat) (vs : list (bv 8)) :
  rvwmo_minus_consistent G →
  gx_lbl G (i, 0%nat) = Some (WeakAxiomatic.LLoad aq base ts vs) →
  (∀ (j : nat) t, ts !! j = Some t → t = 0%nat) →
  srvwmo_consistent
    (cand_snoc (Cand (gx_img G) [])
       (EStep i (WeakAxiomatic.LLoad aq base ts vs))).
Proof.
  intros Hcons Hl Hz.
  apply (gtrace_snoc_read_consistent G (Cand (gx_img G) [])
           (λ _, (0%nat, 0%nat)) i aq base ts vs Hcons).
  - apply srvwmo_of_wf, cand_reachable. intros k s Hs. by destruct k.
  - apply gtrace_prefix_empty.
  - exact Hl.
  - intros j t Hj. rewrite (Hz j t Hj). lia.
Qed.

(* ====================================================================== *)
(** * 10. WHAT REMAINS OF T2-1c′

    THE THEOREM this slice is the core of:

      gtrace_linearization :
        rvwmo_minus_consistent G → grule14 G →
        ∀ (tr : list geid),
          (* tr enumerates G's events exactly once *) NoDup tr ∧
          (∀ e, e ∈ tr ↔ is_Some (gx_lbl G e)) →
          (* and is a linear extension of po ∪ rf ∪ gmo|W *)
          (∀ e1 e2, gpo G e1 e2 → pidx tr e1 < pidx tr e2) →
          (∀ w r a t v, greads_byte G r a t v → gwrite_at G t = Some w →
             pidx tr w < pidx tr r) →
          (∀ w1 w2, w1 ∈ gwrites G → w2 ∈ gwrites G →
             gwix G w1 < gwix G w2 → pidx tr w1 < pidx tr w2) →
          srvwmo_consistent (cand_of tr G)
      where cand_of tr G = Cand (gx_img G) ((λ e, EStep e.1 (glbl G e)) <$> tr).

    ITS OBLIGATIONS, and where each stands after this file:

    (O1) EVERY PREFIX OF [cand_of tr G] IS A [gtrace_prefix].  Induction on
         the prefix length; the five step clauses are bookkeeping
         ([gtp_pos] is "the per-hart subsequence of [tr] is the row", i.e.
         [WeakRvwmoLin.glin_hart]'s argument at an arbitrary linear
         extension, which is where the po arm of the extension is used).
         [gtp_wix] / [gtp_log] are the gmo|W arm: the write steps appear in
         [gwix] order, so the [p]-th write step IS [gwrites]'s [p]-th entry.
         NOT in this file; it is pure list arithmetic over [tr].
    (O2) EVERY READ'S SOURCE IS ALREADY IN THE LOG at its own position —
         the rf arm of the extension, plus (O1)'s index identification.
         NOT in this file (it is the hypothesis [Hsrc] of §8.2).
    (O3) THE READ STEP IS ADMISSIBLE.  LANDED: §8.2, on (O1)+(O2).
    (O4) THE WRITE STEP IS ADMISSIBLE and the prefix extends.  LANDED for
         [LStore]: §8.3.
    (O5) THE FENCE STEP.  Free ([WeakRvwmoCert.snoc_fence_consistent]) plus
         the prefix extension ([gtrace_prefix_snoc], already general in the
         label).
    (O6) THE RMW STEP.  The read half is §8.2's argument verbatim (the floor
         induction of §6 already covers [LRmw] on BOTH of its sides); what is
         NOT here is [WeakAxiomatic.rmw_latest] — the appended RMW must name
         the LATEST message of every byte — which is [gatomicity]'s image
         under the log dictionary and is the one genuinely new obligation
         left on the write side.

    So T2-1c′ = (O1) + (O2) + (O6's atomicity clause) on top of this file. *)

(* ====================================================================== *)
(** * 11. AUDIT *)

Print Assumptions floor_of_graph.
Print Assumptions gtrace_snoc_read_consistent.
Print Assumptions gtrace_snoc_write_consistent.
Print Assumptions gtrace_prefix_snoc.
Print Assumptions gtrace_snoc_read_image.
