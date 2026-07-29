(* BarePt.v -- THE PARKED USER TABLE, WITH OR WITHOUT ITS FIXED LEAVES.

   [ProcPtOwn.proc_pt] describes a LIVE process page table: the trampoline
   leaf, the trapframe leaf, the user map, everything else blocked.  The
   teardown path needs one more shape.  proc_freepagetable drops the two
   fixed leaves before calling uvmfree:

     proc_freepagetable(pagetable, sz) {
       uvmunmap(pagetable, TRAMPOLINE, 1, 0);
       uvmunmap(pagetable, TRAPFRAME,  1, 0);
       uvmfree(pagetable, sz);
     }

   and it HAS to: freewalk panics on any leaf it meets, so a table with the
   trampoline still mapped cannot be torn down at all.  So uvmfree runs on
   a BARE table -- the user map and nothing else.

   ONE AXIS, NOT TWO PREDICATES.  Bare and live differ in exactly which
   FIXED leaves the table carries, so this file states both at once:

     [otf : option (mword 44)]    [Some tfp] = live, [None] = bare

   [upt_fixed otf] is that leaf map (trampoline + trapframe, or empty),
   [uptg_map otf um] the whole leaf map, and [uptg otf uroot um] the parked
   table.  [proc_pt] is the [Some] instance ([proc_pt_uptg]) and
   [bare_pt] the [None] one.

   WHAT THE AXIS BUYS.  uvmunmap's proof touches the fixed leaves in
   exactly one way: it must know the vpn it is clearing is not one of them,
   which it gets from its own range premise (the run lies below TRAPFRAME).
   [uptg_fixed_user_none] discharges that at BOTH ends of the axis, so the
   whole uvmunmap proof goes through generically and is sealed twice --
   [UVMUNMAP] for every existing caller and [UVMUNMAP_BARE] for uvmfree.
   Nothing else in the tree changes.

   NOT CARRIED IN [uptg_wf]: [upt_acc_wf] (about USER EXECUTION, which a
   bare table will never do again) and the trapframe page's [page_valid].
   [proc_pt_wf] is [uptg_wf] plus those two, which is why the [Some]
   direction of the bridge is an entailment each way with those as
   side conditions rather than one [⊣⊢]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExtras.
Require Import PageGeom.
Require Import SmodePte.
Require Import Pt4kWalk.
Require Import CommonWalk.
Require Import PtAdBits.
Require Import TrampPt.
Require Import KptTree.
Require Import PtTree.
Require Import PtBuild.
Require Import KMap.
Require Import UptTree.
Require Import UserPtTree.
Require Import KallocInv.
Require Import ProcPtOwn.
Require Import PtFree.
Local Open Scope Z_scope.
Import Defs.

(* the leaves the table carries that the PROCESS does not own.  [Some tfp]
   is a live table (trampoline + trapframe); [None] is what
   proc_freepagetable's two [do_free = 0] unmaps leave behind, and the
   only shape freewalk can take apart. *)
Definition upt_fixed (otf : option (mword 44)) : gmap (mword 27) (mword 64) :=
  match otf with
  | Some tfp => <[tramp_vpn := pte_tramp]> {[tf_vpn := pte_tf tfp]}
  | None => ∅
  end.

(* the whole leaf map: the fixed leaves, then the user map.  At
   [Some tfp] this is [UptTree.upt_full_map tfp um] ([uptg_full_Some]). *)
Definition uptg_map (otf : option (mword 44)) (um : gmap (mword 27) (mword 64))
    : gmap (mword 27) (mword 64) := upt_fixed otf ∪ um.

(* the two fixed leaves, read out of [upt_full_map] *)
Lemma upt_full_map_tramp (tfp : mword 44) (um : gmap (mword 27) (mword 64)) :
  upt_full_map tfp um !! tramp_vpn = Some pte_tramp.
Proof. apply lookup_insert. Qed.

Lemma upt_full_map_tf (tfp : mword 44) (um : gmap (mword 27) (mword 64)) :
  upt_full_map tfp um !! tf_vpn = Some (pte_tf tfp).
Proof.
  rewrite /upt_full_map.
  rewrite (lookup_insert_ne _ tramp_vpn tf_vpn pte_tramp (not_eq_sym tf_vpn_ne_tramp)).
  apply lookup_insert.
Qed.

(* a USER entry, read out of [upt_full_map]: [upt_map_wf] is what says the
   vpn is neither fixed vpn, so the two inserts miss it. *)
Lemma upt_full_map_um (tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) (w : mword 64) :
  upt_map_wf um -> um !! vpn = Some w -> upt_full_map tfp um !! vpn = Some w.
Proof.
  intros Hwf Hu. rewrite /upt_full_map.
  rewrite (lookup_insert_ne _ tramp_vpn vpn pte_tramp
             (not_eq_sym (upt_map_wf_not_tramp um vpn w Hwf Hu))).
  rewrite (lookup_insert_ne _ tf_vpn vpn (pte_tf tfp)
             (not_eq_sym (upt_map_wf_not_tf um vpn w Hwf Hu))).
  exact Hu.
Qed.

Lemma uptg_full_Some (tfp : mword 44) (um : gmap (mword 27) (mword 64)) :
  uptg_map (Some tfp) um = upt_full_map tfp um.
Proof.
  apply map_eq. intros v. rewrite /uptg_map /upt_fixed /upt_full_map.
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

(* the [None] end of the axis: nothing but the user map *)
Lemma uptg_map_None (um : gmap (mword 27) (mword 64)) : uptg_map None um = um.
Proof.
  apply map_eq. intros v. rewrite /uptg_map /upt_fixed.
  apply lookup_union_r. apply lookup_empty.
Qed.

(* NO FIXED LEAF IS A USER VPN.  This is the ONE side condition uvmunmap's
   loop needs of the fixed part, and it holds for both instances from the
   single range premise the spec already carries -- which is what makes
   the loop proof indifferent to [otf]. *)
Lemma uptg_fixed_user_none (otf : option (mword 44)) (vpn : mword 27) :
  (bv_unsigned vpn < bv_unsigned tf_vpn)%Z -> upt_fixed otf !! vpn = None.
Proof.
  intros Hlt.
  assert (Hntf : tf_vpn <> vpn).
  { intros He. rewrite <- He in Hlt. exact (Z.lt_irrefl _ Hlt). }
  assert (Hntr : tramp_vpn <> vpn).
  { intros He. rewrite <- He in Hlt.
    rewrite tramp_vpn_unsigned tf_vpn_unsigned in Hlt. lia. }
  destruct otf as [tfp|]; [| apply lookup_empty].
  rewrite /upt_fixed.
  rewrite (lookup_insert_ne _ tramp_vpn vpn pte_tramp Hntr).
  apply lookup_singleton_ne. exact Hntf.
Qed.

(* ...so at a user vpn the whole leaf map IS the user map, at either shape.
   This is the one fact the loop-body lemmas below run on. *)
Lemma uptg_map_user (otf : option (mword 44)) (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) :
  (bv_unsigned vpn < bv_unsigned tf_vpn)%Z -> uptg_map otf um !! vpn = um !! vpn.
Proof.
  intros Hlt. rewrite /uptg_map.
  apply lookup_union_r. exact (uptg_fixed_user_none otf vpn Hlt).
Qed.

Lemma uptg_map_delete (otf : option (mword 44)) (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) :
  (bv_unsigned vpn < bv_unsigned tf_vpn)%Z ->
  uptg_map otf (delete vpn um) = delete vpn (uptg_map otf um).
Proof.
  intros Hlt. rewrite /uptg_map delete_union.
  assert (Hd : delete vpn (upt_fixed otf) = upt_fixed otf)
    by (apply delete_notin; exact (uptg_fixed_user_none otf vpn Hlt)).
  rewrite Hd. reflexivity.
Qed.

(* uvmfree's run length: PGROUNDUP(sz)/PGSIZE, the number of user pages
   uvmunmap clears.  The sibling of [ProcPtOwn.uvma_np] / [uvmd_np]; at
   [sz = 0] it is 0, which is what makes uvmfree's ONE premise cover the
   branch that skips uvmunmap entirely. *)
Definition uvmf_np (sz : mword 64) : nat :=
  Z.to_nat (uint (pgroundup sz) / 4096).

Definition uptg_spec (otf : option (mword 44)) (uroot : mword 44)
    (um : gmap (mword 27) (mword 64)) (t : ptree) : Prop :=
  pt_base t = uroot /\
  (forall vpn w, uptg_map otf um !! vpn = Some w ->
     exists p2 p1 (a d : mword 1), ptree_maps t vpn p2 p1 (pte_set_ad w a d)) /\
  (forall vpn, uptg_map otf um !! vpn = None -> ptree_blocks0 t vpn).

(* NOTE (statement corrected -- see the report): the [->] direction is FALSE
   without [upt_map_wf um].  [uptg_spec] constrains the table at
   [upt_full_map tfp um], where the FIXED leaves win over [um]; if [um] itself
   mapped [tramp_vpn] to some other word, [upt_tree_spec]'s user-map conjunct
   would demand an A/D variant of THAT word at the trampoline vpn, which the
   tree does not carry.  [upt_map_wf] (every user vpn is strictly below
   [tf_vpn]) is exactly what rules that out, and it is available at both call
   sites ([proc_pt_wf] and [uptg_wf] each carry it), so the premise costs
   nothing.  Same story for [uptg_view_Some]. *)
Lemma uptg_spec_Some (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (t : ptree) :
  upt_map_wf um ->
  uptg_spec (Some tfp) uroot um t <-> upt_tree_spec uroot tfp um t.
Proof.
  intros Hwf. rewrite /uptg_spec uptg_full_Some. split.
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

(* the A/D-exact map view, at either shape ([UptTree.upt_ad_view] is the
   [Some] instance) *)
Definition uptg_view (otf : option (mword 44)) (um m_ad : gmap (mword 27) (mword 64))
    : Prop :=
  (forall vpn, m_ad !! vpn = None <-> uptg_map otf um !! vpn = None) /\
  (forall vpn w', m_ad !! vpn = Some w' ->
     exists w (a d : mword 1), uptg_map otf um !! vpn = Some w /\ w' = pte_set_ad w a d).

(* statement corrected with [upt_map_wf um] -- see the note on
   [uptg_spec_Some] and the report. *)
Lemma uptg_view_Some (tfp : mword 44) (um m_ad : gmap (mword 27) (mword 64)) :
  upt_map_wf um ->
  uptg_view (Some tfp) um m_ad <-> upt_ad_view tfp um m_ad.
Proof.
  intros Hwf. rewrite /uptg_view /upt_ad_view !uptg_full_Some. split.
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
   map, generic in [otf].  These are [UptTree.upt_spec_rep0] /
   [upt_spec_of_rep0] restated along the axis; both get SIMPLER, because
   [uptg_spec] and [uptg_view] are already phrased against one leaf map
   rather than through [upt_leaf_at] (the CLOSE direction loses its
   [upt_map_wf] premise entirely). ---- *)

(* OPEN, over an arbitrary leaf map. *)
Lemma gleaf_spec_rep0 (M : gmap (mword 27) (mword 64)) (t : ptree) :
  (forall vpn w, M !! vpn = Some w ->
     exists p2 p1 (a d : mword 1), ptree_maps t vpn p2 p1 (pte_set_ad w a d)) ->
  (forall vpn, M !! vpn = None -> ptree_blocks0 t vpn) ->
  exists m_ad, pt_rep0 t m_ad /\
    (forall vpn, m_ad !! vpn = None <-> M !! vpn = None) /\
    (forall vpn w', m_ad !! vpn = Some w' ->
       exists w (a d : mword 1), M !! vpn = Some w /\ w' = pte_set_ad w a d).
Proof.
  intros Hmaps Hblk.
  assert (Hlw : forall (vpn : mword 27) (x : mword 64),
            M !! vpn = Some x ->
            exists p2 p1 (a d : mword 1),
              ptree_maps t vpn p2 p1 (pte_set_ad x a d) /\
              pt_leaf_word t vpn = Some (pte_set_ad x a d)).
  { intros vpn x Hl.
    destruct (Hmaps vpn x Hl) as (p2 & p1 & a & d & Hm).
    exists p2, p1, a, d. split; [exact Hm |].
    exact (ptree_maps_leaf_word t vpn p2 p1 _ Hm). }
  exists (map_imap (fun vpn _ => pt_leaf_word t vpn) M).
  assert (HadSome : forall (vpn : mword 27) (w' : mword 64),
            map_imap (fun vpn _ => pt_leaf_word t vpn) M !! vpn = Some w' ->
            exists x, M !! vpn = Some x /\ pt_leaf_word t vpn = Some w').
  { intros vpn w' Hl. rewrite map_lookup_imap in Hl.
    destruct (M !! vpn) as [x|] eqn:Hf; [| discriminate].
    exists x. split; [reflexivity |]. cbn [mbind option_bind] in Hl. exact Hl. }
  assert (HadNone : forall vpn : mword 27,
            map_imap (fun vpn _ => pt_leaf_word t vpn) M !! vpn = None ->
            M !! vpn = None).
  { intros vpn Hl. rewrite map_lookup_imap in Hl.
    destruct (M !! vpn) as [x|] eqn:Hf; [| reflexivity].
    exfalso. cbn [mbind option_bind] in Hl.
    destruct (Hlw vpn x Hf) as (p2 & p1 & a & d & _ & Hq).
    rewrite Hq in Hl. discriminate. }
  split.
  - split.
    + intros vpn w' Hl.
      destruct (HadSome vpn w' Hl) as (x & Hf & Hq).
      destruct (Hlw vpn x Hf) as (p2 & p1 & a & d & Hm & Hq').
      rewrite Hq in Hq'. injection Hq' as Hq''.
      exists p2, p1. rewrite Hq''. exact Hm.
    + intros vpn Hl. exact (Hblk vpn (HadNone vpn Hl)).
  - split.
    + intros vpn. split.
      * intros Hl. exact (HadNone vpn Hl).
      * intros Hr. rewrite map_lookup_imap. rewrite Hr. reflexivity.
    + intros vpn w' Hl.
      destruct (HadSome vpn w' Hl) as (x & Hf & Hq).
      destruct (Hlw vpn x Hf) as (p2 & p1 & a & d & _ & Hq').
      rewrite Hq in Hq'. injection Hq' as Hq''.
      exists x, a, d. split; [exact Hf | exact Hq''].
Qed.

Lemma uptg_spec_rep0 (otf : option (mword 44)) (uroot : mword 44)
    (um : gmap (mword 27) (mword 64)) (t : ptree) :
  uptg_spec otf uroot um t ->
  exists m_ad, pt_rep0 t m_ad /\ uptg_view otf um m_ad.
Proof.
  intros (_ & Hm & Hb).
  destruct (gleaf_spec_rep0 (uptg_map otf um) t Hm Hb) as (m_ad & Hrep & H1 & H2).
  exists m_ad. split; [exact Hrep | split; [exact H1 | exact H2]].
Qed.

(* CLOSE.  No [upt_map_wf] premise: [uptg_view] pins the leaf map itself,
   so there is no [upt_leaf_at] disjunction left to rule out. *)
Lemma uptg_spec_of_rep0 (otf : option (mword 44)) (uroot : mword 44)
    (um m_ad : gmap (mword 27) (mword 64)) (t : ptree) :
  uptg_view otf um m_ad -> pt_rep0 t m_ad -> pt_base t = uroot ->
  uptg_spec otf uroot um t.
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

Section BarePt.
  Context `{!riscvGS Σ, !lockG Σ, !kallocG Σ}.

  (* THE PREDICATE, at either shape.  Compare [ProcPtOwn.proc_pt]: same
     three conjuncts, with the fixed-leaf axis exposed. *)
  Definition uptg (otf : option (mword 44)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64)) : iProp Σ :=
    (⌜uptg_wf um⌝ ∗ pt_frame (uptg_spec otf uroot um) ∗ upt_pages_own um)%I.

  (* the bare table -- no trampoline, no trapframe.  What uvmfree takes
     and what freewalk can tear apart. *)
  Definition bare_pt (uroot : mword 44) (um : gmap (mword 27) (mword 64)) : iProp Σ :=
    uptg None uroot um.

  Typeclasses Opaque uptg bare_pt.

  (* [proc_pt] IS the [Some] instance -- modulo [proc_pt_wf]'s two extra
     conjuncts, which [uptg] does not carry and which the [Some] direction
     must therefore be given. *)
  Lemma proc_pt_uptg (P : uptd) :
    proc_pt P ⊢ uptg (Some P.(ud_tfp)) P.(ud_root) P.(ud_um).
  Proof.
    iIntros "H". rewrite /proc_pt /uptg /proc_pt_own /pt_frame.
    iDestruct "H" as "(%Hwf & Ht & Hown)".
    iDestruct "Ht" as (t) "(%Hspec & Ht)".
    iSplitR; [iPureIntro; exact (proc_pt_wf_uptg P Hwf) |].
    iSplitL "Ht"; [| iExact "Hown"].
    iExists t. iFrame "Ht". iPureIntro.
    exact (proj2 (uptg_spec_Some P.(ud_root) P.(ud_tfp) P.(ud_um) t (proj1 Hwf))
             Hspec).
  Qed.

  Lemma uptg_proc_pt (P : uptd) :
    upt_acc_wf P.(ud_um) -> page_valid (page_base P.(ud_tfp)) ->
    uptg (Some P.(ud_tfp)) P.(ud_root) P.(ud_um) ⊢ proc_pt P.
  Proof.
    intros Hacc Hval. iIntros "H".
    rewrite /proc_pt /uptg /proc_pt_own /pt_frame.
    iDestruct "H" as "(%Hwf & Ht & Hown)".
    iDestruct "Ht" as (t) "(%Hspec & Ht)".
    destruct Hwf as (Hm & Hp & Hi).
    iSplitR.
    { iPureIntro. rewrite /proc_pt_wf.
      split_and!; [exact Hm | exact Hacc | exact Hp | exact Hi | exact Hval]. }
    iSplitL "Ht"; [| iExact "Hown"].
    iExists t. iFrame "Ht". iPureIntro.
    exact (proj1 (uptg_spec_Some P.(ud_root) P.(ud_tfp) P.(ud_um) t Hm) Hspec).
  Qed.

  (* ---- the open / close pair uvmunmap's wrapper runs on, at either
     shape.  Both are [ProcPtOwn.proc_pt_acc_rep0] / [_rebuild] with
     [upt_ad_view] replaced by [uptg_view]. ---- *)
  Lemma uptg_acc_rep0 (otf : option (mword 44)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64)) :
    uptg otf uroot um ⊢ ∃ t m_ad,
      ⌜pt_rep0 t m_ad⌝ ∗ ⌜uptg_view otf um m_ad⌝ ∗ ⌜pt_base t = uroot⌝ ∗
      ⌜uptg_wf um⌝ ∗ ptree_own 2 (DfracOwn 1) t ∗ upt_pages_own um.
  Proof.
    iIntros "H". rewrite /uptg /pt_frame.
    iDestruct "H" as "(%Hwf & Ht & Hown)".
    iDestruct "Ht" as (t) "(%Hspec & Ht)".
    destruct (uptg_spec_rep0 otf uroot um t Hspec) as (m_ad & Hrep & Hview).
    iExists t, m_ad.
    iSplitR; [iPureIntro; exact Hrep |].
    iSplitR; [iPureIntro; exact Hview |].
    iSplitR; [iPureIntro; exact (proj1 Hspec) |].
    iSplitR; [iPureIntro; exact Hwf |].
    iFrame "Ht Hown".
  Qed.

  Lemma uptg_rebuild (otf : option (mword 44)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64)) (t' : ptree)
      (m_ad : gmap (mword 27) (mword 64)) :
    uptg_wf um -> uptg_view otf um m_ad ->
    pt_rep0 t' m_ad -> pt_base t' = uroot ->
    ptree_own 2 (DfracOwn 1) t' -∗ upt_pages_own um -∗ uptg otf uroot um.
  Proof.
    intros Hwf Hview Hrep Hbase. iIntros "Ht Hown".
    rewrite /uptg /pt_frame.
    iSplitR; [iPureIntro; exact Hwf |].
    iSplitL "Ht"; [| iExact "Hown"].
    iExists t'. iFrame "Ht". iPureIntro.
    exact (uptg_spec_of_rep0 otf uroot um m_ad t' Hview Hrep Hbase).
  Qed.

  (* the two per-vpn view moves the loop body makes, at either shape.
     Both are the [UptTree] originals with the two fixed-vpn
     disequalities replaced by [uptg_fixed_user_none]. *)
  Lemma uptg_view_um (otf : option (mword 44)) (um m_ad : gmap (mword 27) (mword 64))
      (vpn : mword 27) (w' : mword 64) :
    (bv_unsigned vpn < bv_unsigned tf_vpn)%Z ->
    uptg_view otf um m_ad -> m_ad !! vpn = Some w' ->
    exists w (a d : mword 1), um !! vpn = Some w /\ w' = pte_set_ad w a d.
  Proof.
    intros Hlt (_ & Hsome) Hl.
    destruct (Hsome vpn w' Hl) as (w & a & d & Hf & Hr).
    rewrite (uptg_map_user otf um vpn Hlt) in Hf.
    exists w, a, d. split; [exact Hf | exact Hr].
  Qed.

  Lemma uptg_view_none (otf : option (mword 44)) (um m_ad : gmap (mword 27) (mword 64))
      (vpn : mword 27) :
    (bv_unsigned vpn < bv_unsigned tf_vpn)%Z ->
    uptg_view otf um m_ad -> m_ad !! vpn = None -> um !! vpn = None.
  Proof.
    intros Hlt (Hnone & _) Hl.
    rewrite <- (uptg_map_user otf um vpn Hlt).
    exact (proj1 (Hnone vpn) Hl).
  Qed.

  Lemma uptg_view_delete (otf : option (mword 44)) (um m_ad : gmap (mword 27) (mword 64))
      (vpn : mword 27) :
    (bv_unsigned vpn < bv_unsigned tf_vpn)%Z ->
    uptg_view otf um m_ad -> uptg_view otf (delete vpn um) (delete vpn m_ad).
  Proof.
    intros Hlt (Hnone & Hsome). rewrite /uptg_view (uptg_map_delete otf um vpn Hlt).
    split.
    - intros v. destruct (decide (v = vpn)) as [-> | Hne].
      + rewrite !lookup_delete. split; intros _; reflexivity.
      + rewrite (lookup_delete_ne m_ad vpn v (not_eq_sym Hne)).
        rewrite (lookup_delete_ne (uptg_map otf um) vpn v (not_eq_sym Hne)).
        exact (Hnone v).
    - intros v w' Hl. destruct (decide (v = vpn)) as [-> | Hne].
      { rewrite lookup_delete in Hl. discriminate. }
      rewrite (lookup_delete_ne m_ad vpn v (not_eq_sym Hne)) in Hl.
      rewrite (lookup_delete_ne (uptg_map otf um) vpn v (not_eq_sym Hne)).
      exact (Hsome v w' Hl).
  Qed.

  (* ---- what uvmfree hands freewalk: a bare table at the EMPTY user map
     owns nothing but its own nodes, and its tree is freewalk-safe. ---- *)
  Lemma bare_pt_empty_free (uroot : mword 44) :
    bare_pt uroot ∅ ⊢ ∃ t : ptree,
      ⌜pt_base t = uroot⌝ ∗ ⌜pt_free_ok 2 t⌝ ∗ ptree_own 2 (DfracOwn 1) t.
  Proof.
    iIntros "H". rewrite /bare_pt /uptg /pt_frame.
    iDestruct "H" as "(%Hwf & Ht & Hown)".
    iDestruct "Ht" as (t) "(%Hspec & Ht)".
    (* the bare table at the empty user map maps NOTHING, so its tree is an
       exact [pt_rep0] of the empty map -- the first conjunct is vacuous and
       the second is [uptg_spec]'s own blocking clause. *)
    assert (Hrep : pt_rep0 t (∅ : gmap (mword 27) (mword 64))).
    { destruct Hspec as (_ & _ & Hblk). split.
      - intros vpn w Hl. rewrite lookup_empty in Hl. discriminate.
      - intros vpn Hl. apply Hblk. rewrite uptg_map_None. exact Hl. }
    iExists t.
    iSplitR; [iPureIntro; exact (proj1 Hspec) |].
    iSplitR; [iPureIntro; exact (pt_free_ok_rep0 t Hrep) |].
    iExact "Ht".
  Qed.

End BarePt.
