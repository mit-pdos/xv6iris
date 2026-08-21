(* BarePt.v -- THE PARKED USER TABLE, AT ANY STAGE OF ITS TEARDOWN.

   [ProcPtOwn.proc_pt] describes a LIVE process page table: the trampoline
   leaf, the trapframe leaf, the user map, everything else blocked.  The
   teardown path needs more shapes than that.  proc_freepagetable drops the
   two fixed leaves, ONE AT A TIME, before calling uvmfree:

     proc_freepagetable(pagetable, sz) {
       uvmunmap(pagetable, TRAMPOLINE, 1, 0);
       uvmunmap(pagetable, TRAPFRAME,  1, 0);
       uvmfree(pagetable, sz);
     }

   and it HAS to: freewalk panics on any leaf it meets, so a table with the
   trampoline still mapped cannot be torn down at all.  So uvmfree runs on
   a BARE table -- the user map and nothing else.

   ONE AXIS: THE FIXED-LEAF MAP ITSELF.  Bare and live differ in exactly
   which FIXED leaves the table carries, so this file makes that map the
   parameter:

     [fx : gmap (mword 27) (mword 64)]     the leaves the PROCESS does not own

   [uptg_map fx um] is the whole leaf map ([fx] wins over [um]) and
   [uptg fx uroot um] the parked table.  [proc_pt] is the [upt_fixed_both]
   instance ([proc_pt_uptg]) and [bare_pt] the [∅] one.

   WHY A MAP AND NOT AN [option (mword 44)].  The first version of this file
   had a two-point axis -- [Some tfp] = both fixed leaves, [None] = neither.
   That is one state short.  proc_freepagetable passes THROUGH
   "trampoline gone, trapframe still there", and proc_pagetable's second
   mappages failure tail STARTS in "trampoline mapped, trapframe never was":

     if (mappages(.., TRAPFRAME, ..) < 0) { uvmunmap(pt, TRAMPOLINE, 1, 0); .. }

   Neither is expressible as an [option], so neither function could be
   stated at all, let alone proved.  A map covers every stage uniformly and
   makes "drop one fixed leaf" a plain [delete].

   WHAT THE AXIS BUYS.  uvmunmap's proof touches the fixed leaves in exactly
   one way: it must know whether the vpn it is clearing is one of them.
   [uptg_fixed_user_none] answers "no" for every USER vpn at ANY [fx] (from
   the spec's own range premise), and [uptg_um_fixed_none] answers the dual
   for the two fixed vpns, so the whole uvmunmap proof goes through
   generically and is sealed three times -- [UVMUNMAP] for every existing
   caller, [UVMUNMAP_BARE] for uvmfree, and [UVMUNMAP_FIXED] for
   proc_freepagetable's two [do_free = 0] calls.  Nothing else changes.

   [fx] IS GENERIC ONLY IN HERE.  Every [Module Type] pins it to one of the
   three literals below ([upt_fixed_both] / [upt_fixed_tramp] / [∅]), so no
   contract ever leaves the fixed leaves' VALUES loose.  [fx_wf] -- every key
   is [tramp_vpn] or [tf_vpn] -- is carried INSIDE [uptg] so that consumers
   never have to thread it; it is what makes [fx] and [um] automatically
   disjoint, given [upt_map_wf um].

   OWNERSHIP DOES NOT MOVE WITH THE AXIS.  [upt_pages_own] is a function of
   [um] ALONE: the trampoline's page is global kernel text and the
   trapframe's belongs to [ProcInv.proc_priv], so neither was ever owned
   here.  That is why widening [fx] costs no resource bookkeeping, and why
   dropping a fixed leaf hands nothing back.

   NOT CARRIED IN [uptg_wf]: [upt_acc_wf] (about USER EXECUTION, which a
   bare table will never do again) and the trapframe page's [page_valid].
   [proc_pt_wf] is [uptg_wf] plus those two, which is why the live
   direction of the bridge is an entailment each way with those as
   side conditions rather than one [⊣⊢].  That split IS the "no longer a
   valid user page table, but still well-formed enough to be torn down"
   tier. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto.
Require Import PageGeom.
Require Import PtAdBits.
Require Import TrampPt.
Require Import KptTree.
Require Import PtTree.
Require Import PtBuild.
Require Import KMap.
Require Import UptTree.
Require Import UserPtTree.
Require Import KallocInv.
Require Import ProcPt.
Require Import ProcPtOwn.
Require Import PtFree.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1  The fixed-leaf map, its three literals, and its well-formedness.   *)
(* ===================================================================== *)

(* the leaves the table carries that the PROCESS does not own.  Only two
   vpns can ever appear, and this is the ONLY thing the loop proof needs to
   know about [fx]. *)
Definition fx_wf (fx : gmap (mword 27) (mword 64)) : Prop :=
  forall v w, fx !! v = Some w -> v = tramp_vpn \/ v = tf_vpn.

(* a LIVE table: trampoline + trapframe.  This is what [proc_pt] carries. *)
Definition upt_fixed_both (tfp : mword 44) : gmap (mword 27) (mword 64) :=
  <[tramp_vpn := pte_tramp]> {[tf_vpn := pte_tf tfp]}.

(* proc_pagetable's SECOND failure tail: the trampoline mapping succeeded,
   the trapframe one did not.  Also the state between
   proc_freepagetable's two unmaps, with the roles reversed. *)
Definition upt_fixed_tramp : gmap (mword 27) (mword 64) :=
  {[tramp_vpn := pte_tramp]}.

(* ...and [∅] is the bare table.  No definition needed. *)

Lemma fx_wf_both (tfp : mword 44) : fx_wf (upt_fixed_both tfp).
Proof.
  intros v w Hl. rewrite /upt_fixed_both in Hl.
  destruct (decide (v = tramp_vpn)) as [-> | Hne]; [left; reflexivity |].
  rewrite (lookup_insert_ne _ tramp_vpn v pte_tramp (not_eq_sym Hne)) in Hl.
  destruct (decide (v = tf_vpn)) as [-> | Hne2]; [right; reflexivity |].
  rewrite (lookup_singleton_ne tf_vpn v (pte_tf tfp) (not_eq_sym Hne2)) in Hl.
  discriminate.
Qed.

Lemma fx_wf_tramp : fx_wf upt_fixed_tramp.
Proof.
  intros v w Hl. rewrite /upt_fixed_tramp in Hl.
  destruct (decide (v = tramp_vpn)) as [-> | Hne]; [left; reflexivity |].
  rewrite (lookup_singleton_ne tramp_vpn v pte_tramp (not_eq_sym Hne)) in Hl.
  discriminate.
Qed.

Lemma fx_wf_empty : fx_wf ∅.
Proof. intros v w Hl. rewrite lookup_empty in Hl. discriminate. Qed.

Lemma fx_wf_delete (fx : gmap (mword 27) (mword 64)) (v : mword 27) :
  fx_wf fx -> fx_wf (delete v fx).
Proof.
  intros Hwf u w Hl.
  destruct (decide (u = v)) as [-> | Hne]; [rewrite lookup_delete in Hl; discriminate |].
  rewrite (lookup_delete_ne fx v u (not_eq_sym Hne)) in Hl.
  exact (Hwf u w Hl).
Qed.

(* dropping the trampoline from a live table leaves the trapframe-only one,
   and dropping the trapframe from THAT leaves the bare one.  These two are
   proc_freepagetable's whole ghost story, and both are decidable map
   equalities. *)
Lemma upt_fixed_both_del_tramp (tfp : mword 44) :
  delete tramp_vpn (upt_fixed_both tfp) = {[tf_vpn := pte_tf tfp]}.
Proof.
  rewrite /upt_fixed_both delete_insert_delete.
  apply delete_notin.
  apply lookup_singleton_ne. exact tf_vpn_ne_tramp.
Qed.

Lemma upt_fixed_tf_del_tf (tfp : mword 44) :
  delete tf_vpn ({[tf_vpn := pte_tf tfp]} : gmap (mword 27) (mword 64)) = ∅.
Proof. apply delete_singleton. Qed.

Lemma upt_fixed_tramp_del_tramp :
  delete tramp_vpn upt_fixed_tramp = ∅.
Proof. rewrite /upt_fixed_tramp. apply delete_singleton. Qed.

(* ===================================================================== *)
(* §2  The whole leaf map, and the two disjointness facts.                *)
(* ===================================================================== *)

(* the whole leaf map: the fixed leaves, then the user map.  At
   [upt_fixed_both tfp] this is [UptTree.upt_full_map tfp um]
   ([uptg_full_both]). *)
Definition uptg_map (fx um : gmap (mword 27) (mword 64))
    : gmap (mword 27) (mword 64) := fx ∪ um.

(* the three POSITIVE readings of [upt_full_map] this file's live-side
   bridges run on -- [UptTree.upt_full_map_tramp] / [_tf] / [_um] -- live
   next to their elimination forms, in UptTree.v. *)

Lemma uptg_full_both (tfp : mword 44) (um : gmap (mword 27) (mword 64)) :
  uptg_map (upt_fixed_both tfp) um = upt_full_map tfp um.
Proof.
  apply map_eq. intros v. rewrite /uptg_map /upt_fixed_both /upt_full_map.
  destruct (decide (v = tramp_vpn)) as [-> | Hne1].
  - rewrite lookup_insert. apply lookup_union_Some_l. apply lookup_insert.
  - rewrite (lookup_insert_ne _ tramp_vpn v pte_tramp (not_eq_sym Hne1)).
    destruct (decide (v = tf_vpn)) as [-> | Hne2].
    + rewrite lookup_insert. apply lookup_union_Some_l.
      rewrite (lookup_insert_ne _ tramp_vpn tf_vpn pte_tramp
                 (not_eq_sym tf_vpn_ne_tramp)).
      apply lookup_singleton.
    + rewrite (lookup_insert_ne _ tf_vpn v (pte_tf tfp) (not_eq_sym Hne2)).
      apply lookup_union_r.
      rewrite (lookup_insert_ne _ tramp_vpn v pte_tramp (not_eq_sym Hne1)).
      apply lookup_singleton_ne. exact (not_eq_sym Hne2).
Qed.

(* the bare end of the axis: nothing but the user map *)
Lemma uptg_map_empty (um : gmap (mword 27) (mword 64)) : uptg_map ∅ um = um.
Proof.
  apply map_eq. intros v. rewrite /uptg_map.
  apply lookup_union_r. apply lookup_empty.
Qed.

(* NO FIXED LEAF IS A USER VPN.  This is the ONE side condition uvmunmap's
   loop needs of the fixed part on a USER run, and it holds at every [fx]
   from the single range premise the spec already carries -- which is what
   makes the loop proof indifferent to [fx]. *)
Lemma uptg_fixed_user_none (fx : gmap (mword 27) (mword 64)) (vpn : mword 27) :
  fx_wf fx -> (bv_unsigned vpn < bv_unsigned tf_vpn)%Z -> fx !! vpn = None.
Proof.
  intros Hwf Hlt.
  destruct (fx !! vpn) as [w|] eqn:Hl; [| reflexivity].
  exfalso. destruct (Hwf vpn w Hl) as [-> | ->].
  - rewrite tramp_vpn_unsigned tf_vpn_unsigned in Hlt. lia.
  - exact (Z.lt_irrefl _ Hlt).
Qed.

(* THE DUAL, and what the FIXED-leaf unmap runs on: no user vpn is one of
   the two fixed ones, so at [tramp_vpn] / [tf_vpn] the whole leaf map IS
   [fx] and deleting there cannot expose a shadowed user entry.  Comes
   straight from [upt_map_wf], which [uptg_wf] already carries. *)
Lemma uptg_um_fixed_none (um : gmap (mword 27) (mword 64)) (v : mword 27) :
  upt_map_wf um -> (v = tramp_vpn \/ v = tf_vpn) -> um !! v = None.
Proof.
  intros Hwf Hv.
  destruct (um !! v) as [w|] eqn:Hl; [| reflexivity].
  exfalso. destruct (Hwf v w Hl) as [Hlt _].
  destruct Hv as [-> | ->].
  - rewrite tramp_vpn_unsigned tf_vpn_unsigned in Hlt. lia.
  - exact (Z.lt_irrefl _ Hlt).
Qed.

(* ...so at a user vpn the whole leaf map IS the user map, at any [fx].
   This is the one fact the USER-run loop-body lemmas below run on. *)
Lemma uptg_map_user (fx um : gmap (mword 27) (mword 64)) (vpn : mword 27) :
  fx_wf fx -> (bv_unsigned vpn < bv_unsigned tf_vpn)%Z ->
  uptg_map fx um !! vpn = um !! vpn.
Proof.
  intros Hwf Hlt. rewrite /uptg_map.
  apply lookup_union_r. exact (uptg_fixed_user_none fx vpn Hwf Hlt).
Qed.

(* ...and at a fixed vpn it IS the fixed map. *)
Lemma uptg_map_fixed (fx um : gmap (mword 27) (mword 64)) (v : mword 27) :
  upt_map_wf um -> (v = tramp_vpn \/ v = tf_vpn) ->
  uptg_map fx um !! v = fx !! v.
Proof.
  intros Hwf Hv. rewrite /uptg_map.
  destruct (fx !! v) as [w|] eqn:Hl.
  - apply lookup_union_Some_l. exact Hl.
  - rewrite (lookup_union_r fx um v Hl). exact (uptg_um_fixed_none um v Hwf Hv).
Qed.

Lemma uptg_map_delete (fx um : gmap (mword 27) (mword 64)) (vpn : mword 27) :
  fx_wf fx -> (bv_unsigned vpn < bv_unsigned tf_vpn)%Z ->
  uptg_map fx (delete vpn um) = delete vpn (uptg_map fx um).
Proof.
  intros Hwf Hlt. rewrite /uptg_map delete_union.
  assert (Hd : delete vpn fx = fx)
    by (apply delete_notin; exact (uptg_fixed_user_none fx vpn Hwf Hlt)).
  rewrite Hd. reflexivity.
Qed.

(* the FIXED-side twin: dropping a fixed leaf drops it from the whole leaf
   map, because [um] has nothing there to be exposed. *)
Lemma uptg_map_delete_fixed (fx um : gmap (mword 27) (mword 64)) (v : mword 27) :
  upt_map_wf um -> (v = tramp_vpn \/ v = tf_vpn) ->
  uptg_map (delete v fx) um = delete v (uptg_map fx um).
Proof.
  intros Hwf Hv. rewrite /uptg_map delete_union.
  rewrite (delete_notin um v (uptg_um_fixed_none um v Hwf Hv)). reflexivity.
Qed.

(* ===================================================================== *)
(* §3  The table spec, generic in [fx].                                   *)
(* ===================================================================== *)

Definition uptg_spec (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
    (um : gmap (mword 27) (mword 64)) (t : ptree) : Prop :=
  pt_base t = uroot /\
  (forall vpn w, uptg_map fx um !! vpn = Some w ->
     exists p2 p1 (a d : mword 1), ptree_maps t vpn p2 p1 (pte_set_ad w a d)) /\
  (forall vpn, uptg_map fx um !! vpn = None -> ptree_blocks0 t vpn).

(* NOTE (statement corrected -- see the report): the [->] direction is FALSE
   without [upt_map_wf um].  [uptg_spec] constrains the table at
   [upt_full_map tfp um], where the FIXED leaves win over [um]; if [um] itself
   mapped [tramp_vpn] to some other word, [upt_tree_spec]'s user-map conjunct
   would demand an A/D variant of THAT word at the trampoline vpn, which the
   tree does not carry.  [upt_map_wf] (every user vpn is strictly below
   [tf_vpn]) is exactly what rules that out, and it is available at both call
   sites ([proc_pt_wf] and [uptg_wf] each carry it), so the premise costs
   nothing.  Same story for [uptg_view_both]. *)
Lemma uptg_spec_both (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (t : ptree) :
  upt_map_wf um ->
  uptg_spec (upt_fixed_both tfp) uroot um t <-> upt_tree_spec uroot tfp um t.
Proof.
  intros Hwf. rewrite /uptg_spec uptg_full_both. split.
  - intros (Hbase & Hmaps & Hblk).
    split; [exact Hbase |].
    split; [exact (Hmaps tramp_vpn pte_tramp (upt_full_map_tramp tfp um)) |].
    split; [exact (Hmaps tf_vpn (pte_tf tfp) (upt_full_map_tf tfp um)) |].
    split.
    + intros vpn w Hu.
      exact (Hmaps vpn w (upt_full_map_um tfp um vpn w Hwf Hu)).
    + intros vpn Hntr Hntf Hu. apply Hblk.
      apply (proj2 (upt_full_map_None tfp um vpn)).
      split; [exact Hntr | split; [exact Hntf | exact Hu]].
  - intros Hspec. split; [exact (proj1 Hspec) |].
    split.
    + intros vpn w Hl.
      exact (upt_spec_maps uroot tfp um t vpn w Hspec
               (upt_full_map_leaf_at tfp um vpn w Hl)).
    + intros vpn Hl.
      destruct (proj1 (upt_full_map_None tfp um vpn) Hl) as (Hntr & Hntf & Hu).
      exact (proj2 (proj2 (proj2 (proj2 Hspec))) vpn Hntr Hntf Hu).
Qed.

(* the A/D-exact map view, generic in [fx] ([UptTree.upt_ad_view] is the
   [upt_fixed_both] instance) *)
Definition uptg_view (fx um m_ad : gmap (mword 27) (mword 64)) : Prop :=
  (forall vpn, m_ad !! vpn = None <-> uptg_map fx um !! vpn = None) /\
  (forall vpn w', m_ad !! vpn = Some w' ->
     exists w (a d : mword 1), uptg_map fx um !! vpn = Some w /\ w' = pte_set_ad w a d).

(* statement corrected with [upt_map_wf um] -- see the note on
   [uptg_spec_both] and the report. *)
Lemma uptg_view_both (tfp : mword 44) (um m_ad : gmap (mword 27) (mword 64)) :
  upt_map_wf um ->
  uptg_view (upt_fixed_both tfp) um m_ad <-> upt_ad_view tfp um m_ad.
Proof.
  intros Hwf. rewrite /uptg_view /upt_ad_view !uptg_full_both. split.
  - intros (Hnone & Hsome). split.
    + intros vpn. split.
      * intros Hl. exact (proj1 (upt_full_map_None tfp um vpn) (proj1 (Hnone vpn) Hl)).
      * intros Hr. exact (proj2 (Hnone vpn) (proj2 (upt_full_map_None tfp um vpn) Hr)).
    + intros vpn w' Hl. destruct (Hsome vpn w' Hl) as (w & a & d & Hf & Hr).
      exists w, a, d.
      split; [exact (upt_full_map_leaf_at tfp um vpn w Hf) | exact Hr].
  - intros (Hnone & Hsome). split.
    + intros vpn. split.
      * intros Hl. exact (proj2 (upt_full_map_None tfp um vpn) (proj1 (Hnone vpn) Hl)).
      * intros Hr. exact (proj2 (Hnone vpn) (proj1 (upt_full_map_None tfp um vpn) Hr)).
    + intros vpn w' Hl. destruct (Hsome vpn w' Hl) as (w & a & d & Hleaf & Hr).
      exists w, a, d. split; [| exact Hr].
      destruct Hleaf as [(-> & ->) | [(-> & ->) | Hu]].
      * apply upt_full_map_tramp.
      * apply upt_full_map_tf.
      * exact (upt_full_map_um tfp um vpn w Hwf Hu).
Qed.

(* ---- the OPEN / CLOSE pair between [uptg_spec] and the exact [pt_rep0]
   map, generic in [fx].  These are [UptTree.upt_spec_rep0] /
   [upt_spec_of_rep0] restated along the axis; both get SIMPLER, because
   [uptg_spec] and [uptg_view] are already phrased against one leaf map
   rather than through [upt_leaf_at] (the CLOSE direction loses its
   [upt_map_wf] premise entirely).  OPEN is literally
   [UptTree.gleaf_spec_rep0] -- the construction over an ARBITRARY leaf
   map -- fed [uptg_map fx um]. ---- *)

Lemma uptg_spec_rep0 (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
    (um : gmap (mword 27) (mword 64)) (t : ptree) :
  uptg_spec fx uroot um t ->
  exists m_ad, pt_rep0 t m_ad /\ uptg_view fx um m_ad.
Proof.
  intros (_ & Hm & Hb).
  destruct (gleaf_spec_rep0 (uptg_map fx um) t Hm Hb) as (m_ad & Hrep & H1 & H2).
  exists m_ad. split; [exact Hrep | split; [exact H1 | exact H2]].
Qed.

(* CLOSE.  No [upt_map_wf] premise: [uptg_view] pins the leaf map itself,
   so there is no [upt_leaf_at] disjunction left to rule out. *)
Lemma uptg_spec_of_rep0 (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
    (um m_ad : gmap (mword 27) (mword 64)) (t : ptree) :
  uptg_view fx um m_ad -> pt_rep0 t m_ad -> pt_base t = uroot ->
  uptg_spec fx uroot um t.
Proof.
  intros (Hnone & Hsome) (Hmap & Hblk) Hbase.
  split; [exact Hbase |]. split.
  - intros vpn w Hl.
    destruct (m_ad !! vpn) as [w'|] eqn:Had.
    + destruct (Hsome vpn w' Had) as (w0 & a & d & Hf & ->).
      destruct (Hmap vpn _ Had) as (p2 & p1 & Hm).
      assert (Hw : w0 = w) by congruence.
      exists p2, p1, a, d. rewrite <- Hw. exact Hm.
    + exfalso. rewrite (proj1 (Hnone vpn) Had) in Hl. discriminate.
  - intros vpn Hl. exact (Hblk vpn (proj2 (Hnone vpn) Hl)).
Qed.

(* the wf conjuncts, minus the ones that only make sense for a live table
   ([upt_acc_wf], which is about USER EXECUTION, and the trapframe page's
   validity).  [proc_pt_wf] is this plus those two. *)
Definition uptg_wf (um : gmap (mword 27) (mword 64)) : Prop :=
  upt_map_wf um /\ um_pages_valid um /\ um_inj um.

Lemma uptg_wf_delete (um : gmap (mword 27) (mword 64)) (vpn : mword 27) :
  uptg_wf um -> uptg_wf (delete vpn um).
Proof.
  intros (Hm & Hp & Hi). split_and!.
  - exact (upt_map_wf_delete um vpn Hm).
  - exact (um_pages_valid_delete um vpn Hp).
  - exact (um_inj_delete um vpn Hi).
Qed.

Lemma proc_pt_wf_uptg (P : uptd) : proc_pt_wf P -> uptg_wf P.(ud_um).
Proof.
  intros (Hm & _ & Hp & Hi & _). split_and!; [exact Hm | exact Hp | exact Hi].
Qed.

(* ...over a whole DELETION RUN, which is what a loop that clears
   [vpn_run vpn0 k] needs.  The [uptg_wf] twin of
   [ProcPtOwn.proc_pt_wf_del_run]. *)
Lemma uptg_wf_del_run (um : gmap (mword 27) (mword 64)) (vpn0 : mword 27)
    (k : nat) :
  uptg_wf um -> uptg_wf (um_del_run um vpn0 k).
Proof.
  intros Hwf. induction k as [| k IH]; [exact Hwf |].
  cbn [um_del_run]. exact (uptg_wf_delete _ _ IH).
Qed.

(* the [uptg_wf] twin of [ProcPtOwn.um_page_valid]: every page the user map
   names is a kalloc page, which is kfree's precondition. *)
Lemma uptg_page_valid (um : gmap (mword 27) (mword 64)) (vpn : mword 27)
    (w : mword 64) :
  uptg_wf um -> um !! vpn = Some w -> page_valid (page_base (pte_ppn w)).
Proof.
  intros (_ & Hpv & _) Hl. apply Hpv. apply elem_of_um_ppns.
  exists vpn, w. split; [exact Hl | reflexivity].
Qed.

Section BarePt.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  (* THE PREDICATE, at any [fx].  Compare [ProcPtOwn.proc_pt]: same three
     conjuncts, with the fixed-leaf map exposed and its [fx_wf] carried
     alongside so consumers never thread it. *)
  Definition uptg (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64)) : iProp Σ :=
    (⌜uptg_wf um⌝ ∗ ⌜fx_wf fx⌝ ∗ pt_frame (uptg_spec fx uroot um) ∗
     upt_pages_own um)%I.

  (* the bare table -- no trampoline, no trapframe.  What uvmfree takes
     and what freewalk can tear apart. *)
  Definition bare_pt (uroot : mword 44) (um : gmap (mword 27) (mword 64)) : iProp Σ :=
    uptg ∅ uroot um.

  Typeclasses Opaque uptg bare_pt.

  (* the two pure facts a consumer most often wants back out *)
  Lemma uptg_wf_get (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64)) :
    uptg fx uroot um ⊢ ⌜uptg_wf um⌝ ∗ ⌜fx_wf fx⌝.
  Proof.
    iIntros "H". rewrite /uptg.
    iDestruct "H" as "(%Hwf & %Hfx & _ & _)". iPureIntro. split; assumption.
  Qed.

  (* [ProcPtOwn.proc_pt_own_shrink] at [uptg_wf]: it only ever used
     [um_inj] (for the footprint) and [um_pages_valid] (for kfree's
     [page_valid]), neither of which is about the fixed leaves. *)
  Lemma uptg_own_shrink (um : gmap (mword 27) (mword 64))
      (vpn : mword 27) (w : mword 64) :
    uptg_wf um -> um !! vpn = Some w ->
    KMap.kmap_static_claims -∗ upt_pages_own um -∗
      page_own (page_base (pte_ppn w)) ∗ upt_pages_own (delete vpn um).
  Proof.
    intros Hwf Hl.
    pose proof (uptg_page_valid um vpn w Hwf Hl) as Hval.
    destruct Hwf as (_ & _ & Hinj).
    iIntros "#Hb Hown".
    iEval (rewrite (upt_pages_own_take um vpn w Hinj Hl)) in "Hown".
    iDestruct "Hown" as "[Hp Hrest]".
    iSplitL "Hp".
    { iApply (phys_to_page_own (pte_ppn w) Hval with "Hb Hp"). }
    iExact "Hrest".
  Qed.

  (* [proc_pt] IS the [upt_fixed_both] instance -- modulo [proc_pt_wf]'s two
     extra conjuncts, which [uptg] does not carry and which the live
     direction must therefore be given. *)
  Lemma proc_pt_uptg (P : uptd) :
    proc_pt P ⊢ uptg (upt_fixed_both P.(ud_tfp)) P.(ud_root) P.(ud_um).
  Proof.
    iIntros "H". rewrite /proc_pt /uptg /proc_pt_own /pt_frame.
    iDestruct "H" as "(%Hwf & Ht & Hown)".
    iDestruct "Ht" as (t) "(%Hspec & Ht)".
    iSplitR; [iPureIntro; exact (proc_pt_wf_uptg P Hwf) |].
    iSplitR; [iPureIntro; exact (fx_wf_both P.(ud_tfp)) |].
    iSplitL "Ht"; [| iExact "Hown"].
    iExists t. iFrame "Ht". iPureIntro.
    exact (proj2 (uptg_spec_both P.(ud_root) P.(ud_tfp) P.(ud_um) t (proj1 Hwf))
             Hspec).
  Qed.

  Lemma uptg_proc_pt (P : uptd) :
    upt_acc_wf P.(ud_um) -> page_valid (page_base P.(ud_tfp)) ->
    uptg (upt_fixed_both P.(ud_tfp)) P.(ud_root) P.(ud_um) ⊢ proc_pt P.
  Proof.
    intros Hacc Hval. iIntros "H".
    rewrite /proc_pt /uptg /proc_pt_own /pt_frame.
    iDestruct "H" as "(%Hwf & %Hfx & Ht & Hown)".
    iDestruct "Ht" as (t) "(%Hspec & Ht)".
    destruct Hwf as (Hm & Hp & Hi).
    iSplitR.
    { iPureIntro. rewrite /proc_pt_wf.
      split_and!; [exact Hm | exact Hacc | exact Hp | exact Hi | exact Hval]. }
    iSplitL "Ht"; [| iExact "Hown"].
    iExists t. iFrame "Ht". iPureIntro.
    exact (proj1 (uptg_spec_both P.(ud_root) P.(ud_tfp) P.(ud_um) t Hm) Hspec).
  Qed.

  (* ---- the open / close pair uvmunmap's wrapper runs on, at any [fx].
     Both are [ProcPtOwn.proc_pt_acc_rep0] / [_rebuild] with
     [upt_ad_view] replaced by [uptg_view]. ---- *)
  (* ------------------------------------------------------------------ *)
  (* THE TREE HALF, on its own.  [uptg] bundles the table with the pages  *)
  (* its map names; a function that touches only SOME of those pages      *)
  (* should be handed the tree and just those, so whatever else the       *)
  (* caller holds -- in the contents-indexed contracts, holds NAMED --     *)
  (* never crosses the call and never comes back existential.  See        *)
  (* ProofUvmunmap.v's [Own] parameter.                                   *)
  (* ------------------------------------------------------------------ *)
  Definition uptg_tree (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64)) : iProp Σ :=
    (⌜uptg_wf um⌝ ∗ ⌜fx_wf fx⌝ ∗ pt_frame (uptg_spec fx uroot um))%I.

  Lemma uptg_split (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64)) :
    uptg fx uroot um ⊣⊢ uptg_tree fx uroot um ∗ upt_pages_own um.
  Proof.
    rewrite /uptg /uptg_tree. iSplit.
    - iIntros "(%H1 & %H2 & Ht & Ho)". iFrame "Ht Ho".
      iSplitR; iPureIntro; assumption.
    - iIntros "((%H1 & %H2 & Ht) & Ho)". iFrame "Ht Ho".
      iSplitR; iPureIntro; assumption.
  Qed.

  Lemma uptg_join (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64)) :
    uptg_tree fx uroot um -∗ upt_pages_own um -∗ uptg fx uroot um.
  Proof.
    iIntros "Ht Ho". rewrite uptg_split. iFrame "Ht Ho".
  Qed.

  Lemma uptg_tree_acc_rep0 (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64)) :
    uptg_tree fx uroot um ⊢ ∃ t m_ad,
      ⌜pt_rep0 t m_ad⌝ ∗ ⌜uptg_view fx um m_ad⌝ ∗ ⌜pt_base t = uroot⌝ ∗
      ⌜uptg_wf um⌝ ∗ ⌜fx_wf fx⌝ ∗ ptree_own 2 (DfracOwn 1) t.
  Proof.
    iIntros "H". rewrite /uptg_tree /pt_frame.
    iDestruct "H" as "(%Hwf & %Hfx & Ht)".
    iDestruct "Ht" as (t) "(%Hspec & Ht)".
    destruct (uptg_spec_rep0 fx uroot um t Hspec) as (m_ad & Hrep & Hview).
    iExists t, m_ad.
    iSplitR; [iPureIntro; exact Hrep |].
    iSplitR; [iPureIntro; exact Hview |].
    iSplitR; [iPureIntro; exact (proj1 Hspec) |].
    iSplitR; [iPureIntro; exact Hwf |].
    iSplitR; [iPureIntro; exact Hfx |].
    iExact "Ht".
  Qed.

  Lemma uptg_tree_rebuild (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64)) (t' : ptree)
      (m_ad : gmap (mword 27) (mword 64)) :
    uptg_wf um -> fx_wf fx -> uptg_view fx um m_ad ->
    pt_rep0 t' m_ad -> pt_base t' = uroot ->
    ptree_own 2 (DfracOwn 1) t' -∗ uptg_tree fx uroot um.
  Proof.
    intros Hwf Hfx Hview Hrep Hbase. iIntros "Ht".
    rewrite /uptg_tree /pt_frame.
    iSplitR; [iPureIntro; exact Hwf |].
    iSplitR; [iPureIntro; exact Hfx |].
    iExists t'. iFrame "Ht". iPureIntro.
    exact (uptg_spec_of_rep0 fx uroot um m_ad t' Hview Hrep Hbase).
  Qed.

  (* ...and the TREE-only forms, for the contents-indexed seals: they keep
     the pages out of the conversion entirely, so a caller can hold them
     NAMED (as [umem_lazy]) on both sides of it. *)
  Lemma proc_ptm_uptg_tree (P : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    proc_ptm P sz M
    ⊢ uptg_tree (upt_fixed_both P.(ud_tfp)) P.(ud_root) P.(ud_um)
      ∗ umem_lazy P sz M.
  Proof.
    iIntros "H". rewrite /proc_ptm /uptg_tree /pt_frame.
    iDestruct "H" as "(%Hwf & Ht & Hm)".
    iDestruct "Ht" as (t) "(%Hspec & Ht)".
    iFrame "Hm".
    iSplitR; [iPureIntro; exact (proc_pt_wf_uptg P Hwf) |].
    iSplitR; [iPureIntro; exact (fx_wf_both P.(ud_tfp)) |].
    iExists t. iFrame "Ht". iPureIntro.
    exact (proj2 (uptg_spec_both P.(ud_root) P.(ud_tfp) P.(ud_um) t (proj1 Hwf))
             Hspec).
  Qed.

  Lemma uptg_tree_proc_ptm (P : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    upt_acc_wf P.(ud_um) -> page_valid (page_base P.(ud_tfp)) ->
    uptg_tree (upt_fixed_both P.(ud_tfp)) P.(ud_root) P.(ud_um) -∗
    umem_lazy P sz M -∗ proc_ptm P sz M.
  Proof.
    intros Hacc Hval. iIntros "H Hm".
    rewrite /proc_ptm /uptg_tree /pt_frame.
    iDestruct "H" as "(%Hwf & %Hfx & Ht)".
    iDestruct "Ht" as (t) "(%Hspec & Ht)".
    destruct Hwf as (Hm & Hp & Hi).
    iFrame "Hm".
    iSplitR.
    { iPureIntro. rewrite /proc_pt_wf.
      split_and!; [exact Hm | exact Hacc | exact Hp | exact Hi | exact Hval]. }
    iExists t. iFrame "Ht". iPureIntro.
    exact (proj1 (uptg_spec_both P.(ud_root) P.(ud_tfp) P.(ud_um) t Hm) Hspec).
  Qed.

  Lemma uptg_acc_rep0 (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64)) :
    uptg fx uroot um ⊢ ∃ t m_ad,
      ⌜pt_rep0 t m_ad⌝ ∗ ⌜uptg_view fx um m_ad⌝ ∗ ⌜pt_base t = uroot⌝ ∗
      ⌜uptg_wf um⌝ ∗ ⌜fx_wf fx⌝ ∗ ptree_own 2 (DfracOwn 1) t ∗ upt_pages_own um.
  Proof.
    iIntros "H". rewrite /uptg /pt_frame.
    iDestruct "H" as "(%Hwf & %Hfx & Ht & Hown)".
    iDestruct "Ht" as (t) "(%Hspec & Ht)".
    destruct (uptg_spec_rep0 fx uroot um t Hspec) as (m_ad & Hrep & Hview).
    iExists t, m_ad.
    iSplitR; [iPureIntro; exact Hrep |].
    iSplitR; [iPureIntro; exact Hview |].
    iSplitR; [iPureIntro; exact (proj1 Hspec) |].
    iSplitR; [iPureIntro; exact Hwf |].
    iSplitR; [iPureIntro; exact Hfx |].
    iFrame "Ht Hown".
  Qed.

  Lemma uptg_rebuild (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64)) (t' : ptree)
      (m_ad : gmap (mword 27) (mword 64)) :
    uptg_wf um -> fx_wf fx -> uptg_view fx um m_ad ->
    pt_rep0 t' m_ad -> pt_base t' = uroot ->
    ptree_own 2 (DfracOwn 1) t' -∗ upt_pages_own um -∗ uptg fx uroot um.
  Proof.
    intros Hwf Hfx Hview Hrep Hbase. iIntros "Ht Hown".
    rewrite /uptg /pt_frame.
    iSplitR; [iPureIntro; exact Hwf |].
    iSplitR; [iPureIntro; exact Hfx |].
    iSplitL "Ht"; [| iExact "Hown"].
    iExists t'. iFrame "Ht". iPureIntro.
    exact (uptg_spec_of_rep0 fx uroot um m_ad t' Hview Hrep Hbase).
  Qed.

  (* the two per-vpn view moves the USER-run loop body makes, at any [fx].
     Both are the [UptTree] originals with the two fixed-vpn
     disequalities replaced by [uptg_fixed_user_none]. *)
  Lemma uptg_view_um (fx um m_ad : gmap (mword 27) (mword 64))
      (vpn : mword 27) (w' : mword 64) :
    fx_wf fx -> (bv_unsigned vpn < bv_unsigned tf_vpn)%Z ->
    uptg_view fx um m_ad -> m_ad !! vpn = Some w' ->
    exists w (a d : mword 1), um !! vpn = Some w /\ w' = pte_set_ad w a d.
  Proof.
    intros Hfx Hlt (_ & Hsome) Hl.
    destruct (Hsome vpn w' Hl) as (w & a & d & Hf & Hr).
    rewrite (uptg_map_user fx um vpn Hfx Hlt) in Hf.
    exists w, a, d. split; [exact Hf | exact Hr].
  Qed.

  Lemma uptg_view_none (fx um m_ad : gmap (mword 27) (mword 64))
      (vpn : mword 27) :
    fx_wf fx -> (bv_unsigned vpn < bv_unsigned tf_vpn)%Z ->
    uptg_view fx um m_ad -> m_ad !! vpn = None -> um !! vpn = None.
  Proof.
    intros Hfx Hlt (Hnone & _) Hl.
    rewrite <- (uptg_map_user fx um vpn Hfx Hlt).
    exact (proj1 (Hnone vpn) Hl).
  Qed.

  Lemma uptg_view_delete (fx um m_ad : gmap (mword 27) (mword 64))
      (vpn : mword 27) :
    fx_wf fx -> (bv_unsigned vpn < bv_unsigned tf_vpn)%Z ->
    uptg_view fx um m_ad -> uptg_view fx (delete vpn um) (delete vpn m_ad).
  Proof.
    intros Hfx Hlt (Hnone & Hsome).
    rewrite /uptg_view (uptg_map_delete fx um vpn Hfx Hlt).
    split.
    - intros v. destruct (decide (v = vpn)) as [-> | Hne].
      + rewrite !lookup_delete. split; intros _; reflexivity.
      + rewrite (lookup_delete_ne m_ad vpn v (not_eq_sym Hne)).
        rewrite (lookup_delete_ne (uptg_map fx um) vpn v (not_eq_sym Hne)).
        exact (Hnone v).
    - intros v w' Hl. destruct (decide (v = vpn)) as [-> | Hne].
      { rewrite lookup_delete in Hl. discriminate. }
      rewrite (lookup_delete_ne m_ad vpn v (not_eq_sym Hne)) in Hl.
      rewrite (lookup_delete_ne (uptg_map fx um) vpn v (not_eq_sym Hne)).
      exact (Hsome v w' Hl).
  Qed.

  (* ---- the FIXED-side twins, which is what proc_freepagetable's two
     [do_free = 0] unmaps run on.  Same three moves, with the roles of
     [fx] and [um] swapped: the leaf comes out of [fx], [um] is untouched,
     and NOTHING is handed back -- the trampoline's page is kernel text and
     the trapframe's belongs to [proc_priv], so neither was ever in
     [upt_pages_own]. ---- *)
  Lemma uptg_view_fx (fx um m_ad : gmap (mword 27) (mword 64))
      (v : mword 27) (w' : mword 64) :
    upt_map_wf um -> (v = tramp_vpn \/ v = tf_vpn) ->
    uptg_view fx um m_ad -> m_ad !! v = Some w' ->
    exists w (a d : mword 1), fx !! v = Some w /\ w' = pte_set_ad w a d.
  Proof.
    intros Hwf Hv (_ & Hsome) Hl.
    destruct (Hsome v w' Hl) as (w & a & d & Hf & Hr).
    rewrite (uptg_map_fixed fx um v Hwf Hv) in Hf.
    exists w, a, d. split; [exact Hf | exact Hr].
  Qed.

  Lemma uptg_view_fx_none (fx um m_ad : gmap (mword 27) (mword 64))
      (v : mword 27) :
    upt_map_wf um -> (v = tramp_vpn \/ v = tf_vpn) ->
    uptg_view fx um m_ad -> m_ad !! v = None -> fx !! v = None.
  Proof.
    intros Hwf Hv (Hnone & _) Hl.
    rewrite <- (uptg_map_fixed fx um v Hwf Hv).
    exact (proj1 (Hnone v) Hl).
  Qed.

  Lemma uptg_view_delete_fixed (fx um m_ad : gmap (mword 27) (mword 64))
      (v : mword 27) :
    upt_map_wf um -> (v = tramp_vpn \/ v = tf_vpn) ->
    uptg_view fx um m_ad -> uptg_view (delete v fx) um (delete v m_ad).
  Proof.
    intros Hwf Hv (Hnone & Hsome).
    rewrite /uptg_view (uptg_map_delete_fixed fx um v Hwf Hv).
    split.
    - intros u. destruct (decide (u = v)) as [-> | Hne].
      + rewrite !lookup_delete. split; intros _; reflexivity.
      + rewrite (lookup_delete_ne m_ad v u (not_eq_sym Hne)).
        rewrite (lookup_delete_ne (uptg_map fx um) v u (not_eq_sym Hne)).
        exact (Hnone u).
    - intros u w' Hl. destruct (decide (u = v)) as [-> | Hne].
      { rewrite lookup_delete in Hl. discriminate. }
      rewrite (lookup_delete_ne m_ad v u (not_eq_sym Hne)) in Hl.
      rewrite (lookup_delete_ne (uptg_map fx um) v u (not_eq_sym Hne)).
      exact (Hsome u w' Hl).
  Qed.

  (* ================================================================== *)
  (* §4  THE STEP ALGEBRA uvmunmap's LOOP RUNS ON, indexed by [do_free]. *)
  (*                                                                     *)
  (*   [df = true]  (do_free != 0): a USER run.  Each iteration deletes  *)
  (*     from [um] and hands the page to kfree; [fx] never moves.        *)
  (*   [df = false] (do_free == 0): a FIXED-leaf run, which is           *)
  (*     proc_freepagetable's two calls and proc_pagetable's second      *)
  (*     failure tail.  Each iteration deletes from [fx] and frees       *)
  (*     NOTHING; [um] and [upt_pages_own] never move.                   *)
  (*                                                                     *)
  (* The loop proof is written against these three, so its body is one   *)
  (* [destruct df] at the [beq s5,zero] and nowhere else.                *)
  (* ================================================================== *)

  (* which side of the leaf map the run's vpns live on.  At [df = true]
     this is the spec's range premise; at [df = false] the caller says
     which fixed leaf it is unmapping. *)
  Definition uu_vpn_ok (df : bool) (v : mword 27) : Prop :=
    if df then (bv_unsigned v < bv_unsigned tf_vpn)%Z
          else (v = tramp_vpn \/ v = tf_vpn).

  Definition uu_fx (df : bool) (fx : gmap (mword 27) (mword 64))
      (vpn0 : mword 27) (k : nat) : gmap (mword 27) (mword 64) :=
    if df then fx else um_del_run fx vpn0 k.

  Definition uu_um (df : bool) (um : gmap (mword 27) (mword 64))
      (vpn0 : mword 27) (k : nat) : gmap (mword 27) (mword 64) :=
    if df then um_del_run um vpn0 k else um.

  Lemma fx_wf_del_run (fx : gmap (mword 27) (mword 64)) (vpn0 : mword 27)
      (k : nat) :
    fx_wf fx -> fx_wf (um_del_run fx vpn0 k).
  Proof.
    intros Hwf. induction k as [| k IH]; [exact Hwf |].
    cbn [um_del_run]. exact (fx_wf_delete _ _ IH).
  Qed.

  Lemma uu_fx_wf (df : bool) (fx : gmap (mword 27) (mword 64))
      (vpn0 : mword 27) (k : nat) :
    fx_wf fx -> fx_wf (uu_fx df fx vpn0 k).
  Proof.
    intros Hwf. rewrite /uu_fx. destruct df; [exact Hwf |].
    exact (fx_wf_del_run fx vpn0 k Hwf).
  Qed.

  Lemma uu_um_wf (df : bool) (um : gmap (mword 27) (mword 64))
      (vpn0 : mword 27) (k : nat) :
    uptg_wf um -> uptg_wf (uu_um df um vpn0 k).
  Proof.
    intros Hwf. rewrite /uu_um. destruct df; [| exact Hwf].
    exact (uptg_wf_del_run um vpn0 k Hwf).
  Qed.

  (* THE TWO PAGE-OWNERSHIP LAWS, at the ordinary [upt_pages_own] instance.
     [ProofUvmunmap]'s loop is abstract in what it holds for the pages it is
     about to free (so the contents-indexed seal can hold the LAZY VIEW
     instead); these are what the three existing seals feed it.

     THE PEEL LAW IS VACUOUS AT [df = false]: the vpn it names is a FIXED
     leaf, which [upt_map_wf] keeps out of [um] entirely, so the hypothesis
     refutes itself -- which is the same reason that branch skips kfree. *)
  Lemma uu_pages_laws (df : bool) (um : gmap (mword 27) (mword 64))
      (vpn0 : mword 27) (npages : nat) :
    uptg_wf um ->
    (forall k : nat, (k < npages)%nat -> uu_vpn_ok df (vpn_at vpn0 k)) ->
    KMap.kmap_static_claims -∗
      □ (∀ (k : nat) (w : mword 64),
           ⌜(k < npages)%nat⌝ -∗
           ⌜uu_um df um vpn0 k !! vpn_at vpn0 k = Some w⌝ -∗
           upt_pages_own (uu_um df um vpn0 k) -∗
             page_own (page_base (pte_ppn w))
             ∗ upt_pages_own (uu_um df um vpn0 (S k)))
      ∗ □ (∀ k : nat,
           ⌜(k < npages)%nat⌝ -∗
           ⌜uu_um df um vpn0 (S k) = uu_um df um vpn0 k⌝ -∗
           upt_pages_own (uu_um df um vpn0 k) -∗
           upt_pages_own (uu_um df um vpn0 (S k))).
  Proof.
    intros Hwf Hside. iIntros "#Hb". iSplit.
    - iIntros "!>" (k w) "%Hk %Hl Ho".
      destruct df.
      + iApply (uptg_own_shrink (uu_um true um vpn0 k) (vpn_at vpn0 k) w
                  (uu_um_wf true um vpn0 k Hwf) Hl with "Hb Ho").
      + exfalso. rewrite /uu_um in Hl.
        destruct Hwf as (Hmw & _ & _).
        pose proof (proj1 (Hmw _ _ Hl)) as Hlt.
        pose proof (Hside k Hk) as Hok. rewrite /uu_vpn_ok in Hok.
        destruct Hok as [Heq | Heq]; rewrite Heq in Hlt.
        * rewrite tramp_vpn_unsigned tf_vpn_unsigned in Hlt. lia.
        * exact (Z.lt_irrefl _ Hlt).
    - iIntros "!>" (k) "%Hk %Heq Ho". rewrite Heq. iExact "Ho".
  Qed.

  (* THE CONTINUE ARMS.  Walk found no leaf, or the leaf word was invalid:
     either way the vpn is absent from the whole leaf map, so the step is a
     no-op on BOTH components and the [S k] invariant is the [k] one. *)
  Lemma uu_step_absent (df : bool) (fx um m_ad : gmap (mword 27) (mword 64))
      (vpn0 : mword 27) (k : nat) :
    uptg_wf um -> fx_wf fx -> uu_vpn_ok df (vpn_at vpn0 k) ->
    uptg_view (uu_fx df fx vpn0 k) (uu_um df um vpn0 k) m_ad ->
    m_ad !! vpn_at vpn0 k = None ->
    uu_fx df fx vpn0 (S k) = uu_fx df fx vpn0 k
    /\ uu_um df um vpn0 (S k) = uu_um df um vpn0 k.
  Proof.
    intros Hwf Hfx Hok Hview Hnone. rewrite /uu_fx /uu_um in Hview |- *.
    destruct df.
    - split; [reflexivity |]. cbn [um_del_run]. apply delete_notin.
      exact (uptg_view_none fx (um_del_run um vpn0 k) m_ad (vpn_at vpn0 k)
               Hfx Hok Hview Hnone).
    - split; [| reflexivity]. cbn [um_del_run]. apply delete_notin.
      exact (uptg_view_fx_none (um_del_run fx vpn0 k) um m_ad (vpn_at vpn0 k)
               (proj1 Hwf) Hok Hview Hnone).
  Qed.

  (* THE CLEARING ARM.  The leaf is there and the store zeroes it; the
     deletion lands on whichever component [df] selects. *)
  Lemma uu_step_delete (df : bool) (fx um m_ad : gmap (mword 27) (mword 64))
      (vpn0 : mword 27) (k : nat) :
    uptg_wf um -> fx_wf fx -> uu_vpn_ok df (vpn_at vpn0 k) ->
    uptg_view (uu_fx df fx vpn0 k) (uu_um df um vpn0 k) m_ad ->
    uptg_view (uu_fx df fx vpn0 (S k)) (uu_um df um vpn0 (S k))
              (delete (vpn_at vpn0 k) m_ad).
  Proof.
    intros Hwf Hfx Hok Hview. rewrite /uu_fx /uu_um in Hview |- *.
    destruct df; cbn [um_del_run].
    - exact (uptg_view_delete fx (um_del_run um vpn0 k) m_ad (vpn_at vpn0 k)
               Hfx Hok Hview).
    - exact (uptg_view_delete_fixed (um_del_run fx vpn0 k) um m_ad
               (vpn_at vpn0 k) (proj1 Hwf) Hok Hview).
  Qed.

  (* ...and on the clearing arm at [df = true] ONLY, the page comes out.
     There is no [df = false] twin, by design: the trampoline's page is
     kernel text and the trapframe's belongs to [proc_priv], so a fixed
     leaf's page was never in [upt_pages_own] and nothing is handed back.
     That is also why the [do_free == 0] arm never calls kfree. *)

  (* ================================================================== *)
  (* §5  THE CONSTRUCTION-SIDE BRIDGES: what proc_pagetable's two mappages *)
  (*     FAILURE TAILS hold, in [uptg] terms.                              *)
  (*                                                                       *)
  (* mappages hands back [ptree_own] + a [pt_rep0] map view; [uptg] wants  *)
  (* [pt_frame (uptg_spec ..)].  These are the converse of                 *)
  (* [bare_pt_empty_free], and they are all the two tails need to reach    *)
  (* uvmfree -- both run at the EMPTY user map, so [upt_pages_own ∅] is    *)
  (* [emp] and nothing has to be handed over.                              *)
  (* ================================================================== *)

  Lemma uptg_wf_empty : uptg_wf ∅.
  Proof.
    split_and!;
      [ exact upt_map_wf_empty | exact um_pages_valid_empty | exact um_inj_empty ].
  Qed.

  Lemma upt_pages_own_empty : ⊢ upt_pages_own (∅ : gmap (mword 27) (mword 64)).
  Proof.
    rewrite /upt_pages_own.
    rewrite (_ : um_ppns ∅ = (∅ : gset (mword 44))); [| apply um_ppns_empty ].
    rewrite big_sepS_empty. done.
  Qed.

  (* TAIL #1: the FIRST mappages failed, so the table maps nothing at all
     and is already the bare table uvmfree takes. *)
  Lemma uptg_of_rep0_empty (uroot : mword 44) (t : ptree) :
    pt_rep0 t ∅ -> pt_base t = uroot ->
    ptree_own 2 (DfracOwn 1) t ⊢ bare_pt uroot ∅.
  Proof.
    intros Hrep Hbase.
    assert (Hview : uptg_view ∅ ∅ (∅ : gmap (mword 27) (mword 64))).
    { rewrite /uptg_view. split.
      - intros v. rewrite uptg_map_empty. split; intros _; apply lookup_empty.
      - intros v w' Hl. rewrite lookup_empty in Hl. discriminate. }
    iIntros "Ht". rewrite /bare_pt.
    iPoseProof upt_pages_own_empty as "Hown".
    iApply (uptg_rebuild ∅ uroot ∅ t ∅ uptg_wf_empty fx_wf_empty
              Hview Hrep Hbase with "Ht Hown").
  Qed.

  (* TAIL #2: the SECOND mappages failed, so the trampoline leaf IS there
     and the trapframe one never was -- the state the old [option] axis
     could not name.
     THE ONE THING TO CHECK, and it holds: mappages installs
     [mk_pte tramp_ppn (10 lor 1)] (flags 0xB) while [pte_tramp] is flags
     0x4B, i.e. the A bit is set in the canonical constant and clear in what
     the store leaves.  [uptg_spec] asks only for an A/D VARIANT, and
     [tramp_pte_ad] says the two agree at [a = d = 0] -- so no contract has
     to be weakened to accept the table this tail holds. *)
  Lemma tramp_pte_ad :
    mappages_pte tramp_ppn 10 0
    = pte_set_ad pte_tramp (mword_of_int 0 : mword 1) (mword_of_int 0 : mword 1).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.

  Lemma uptg_of_rep0_tramp (uroot : mword 44) (t : ptree) :
    pt_rep0 t (<[tramp_vpn := mappages_pte tramp_ppn 10 0]> ∅) ->
    pt_base t = uroot ->
    ptree_own 2 (DfracOwn 1) t ⊢ uptg upt_fixed_tramp uroot ∅.
  Proof.
    intros Hrep Hbase.
    assert (Hview : uptg_view upt_fixed_tramp ∅
                      (<[tramp_vpn := mappages_pte tramp_ppn 10 0]> ∅)).
    { rewrite /uptg_view /uptg_map /upt_fixed_tramp right_id_L. split.
      - intros v. destruct (decide (v = tramp_vpn)) as [-> | Hne].
        + rewrite lookup_insert lookup_singleton.
          split; intros H; discriminate.
        + rewrite (lookup_insert_ne _ tramp_vpn v _ (not_eq_sym Hne)).
          rewrite (lookup_singleton_ne tramp_vpn v pte_tramp (not_eq_sym Hne)).
          split; intros _; [reflexivity | apply lookup_empty].
      - intros v w' Hl. destruct (decide (v = tramp_vpn)) as [-> | Hne].
        + rewrite lookup_insert in Hl.
          exists pte_tramp, (mword_of_int 0 : mword 1), (mword_of_int 0 : mword 1).
          split; [apply lookup_singleton |].
          injection Hl as <-. exact tramp_pte_ad.
        + rewrite (lookup_insert_ne _ tramp_vpn v _ (not_eq_sym Hne)) in Hl.
          rewrite lookup_empty in Hl. discriminate. }
    iIntros "Ht". iPoseProof upt_pages_own_empty as "Hown".
    iApply (uptg_rebuild upt_fixed_tramp uroot ∅ t _ uptg_wf_empty fx_wf_tramp
              Hview Hrep Hbase with "Ht Hown").
  Qed.

  (* ---- what uvmfree hands freewalk: a bare table at the EMPTY user map
     owns nothing but its own nodes, and its tree is freewalk-safe. ---- *)
  Lemma bare_pt_empty_free (uroot : mword 44) :
    bare_pt uroot ∅ ⊢ ∃ t : ptree,
      ⌜pt_base t = uroot⌝ ∗ ⌜pt_free_ok 2 t⌝ ∗ ptree_own 2 (DfracOwn 1) t.
  Proof.
    iIntros "H". rewrite /bare_pt /uptg /pt_frame.
    iDestruct "H" as "(%Hwf & %Hfx & Ht & Hown)".
    iDestruct "Ht" as (t) "(%Hspec & Ht)".
    (* the bare table at the empty user map maps NOTHING, so its tree is an
       exact [pt_rep0] of the empty map -- the first conjunct is vacuous and
       the second is [uptg_spec]'s own blocking clause. *)
    assert (Hrep : pt_rep0 t (∅ : gmap (mword 27) (mword 64))).
    { destruct Hspec as (_ & _ & Hblk). split.
      - intros vpn w Hl. rewrite lookup_empty in Hl. discriminate.
      - intros vpn Hl. apply Hblk. rewrite uptg_map_empty. exact Hl. }
    iExists t.
    iSplitR; [iPureIntro; exact (proj1 Hspec) |].
    iSplitR; [iPureIntro; exact (pt_free_ok_rep0 t Hrep) |].
    iExact "Ht".
  Qed.

End BarePt.
