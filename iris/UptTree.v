(* UptTree.v -- the USER page table over the general page-table tree
   abstraction (PtTree.v), mirroring the kernel's KptTree.v.

   A user-mode table (xv6 Sv39) maps exactly:
   - the TRAMPOLINE page (S-mode only, at TRAMPOLINE = top of VA space) to
     the kernel-text trampoline page -- the shared [pte_tramp] leaf;
   - the TRAPFRAME page (S-mode only, one page below) to the process's
     trapframe page [tfp] -- the [pte_tf tfp] leaf;
   - whatever user-accessible pages sit BELOW the trapframe -- an abstract
     finite map [um : gmap vpn leaf] from vpns to canonical leaf words.
   Everything else BLOCKS (faults).  As everywhere in the tree layer, every
   leaf is kept modulo the Svadu/ADUE A/D bits ([pte_set_ad] variants).

   [utlb_inv_pt uroot tfp um] is the [tlb_inv_pt] mirror: satp holds the
   user root, the TLB is consistent modulo A/D ([tlb_ok_pt]), the table is
   owned as a tree constrained only by the layout-free [upt_tree_spec], and
   the ambient PMP configuration rides along.  The absorption theorem
   instantiates the generic [ptree_translateAddr_own] core: an S-mode
   trampoline fetch or trapframe load/store (the userret / uservec paths)
   translates to the mapped physical page and the invariant absorbs
   whatever the walk did (nothing / TLB fill / A-D write-back). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import SmodePte.
Require Import PtAdBits.
Require Import Pt4kWalk.
Require Import PtTree.
Require Import PtBuild.
Require Import PtTreeAdue.
Require Import KptPt.
Require Import TrampPt.
Require Import KptPt.
Require Import Pt4kWalk.
Require Import RiscvExtras.
Require Import SmodePte.
Require Import UserTranslate.
Require Import KptTree.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The TRAPFRAME leaf and its A/D-variant classification.  (The        *)
(*    trampoline leaf [pte_tramp] and its lemmas live in KptTree.v --     *)
(*    both tables share that mapping.)                                    *)
(* ===================================================================== *)

Definition pte_tf (tfp : mword 44) : mword 64 := mk_pte tfp PTE_TF.

Lemma tf_variant_flags (tfp : mword 44) (a d : mword 1) :
  subrange_vec_dec (pte_set_ad (pte_tf tfp) a d) 7 0
  = (mword_of_int (Z.lor (Z.land PTE_TF 831)
       (Z.lor (Z.shiftl (bv_unsigned a) 6) (Z.shiftl (bv_unsigned d) 7))) : mword 8).
Proof.
  unfold pte_tf, mk_pte.
  rewrite (pte_set_ad_zext_concat tfp PTE_TF a d ltac:(unfold PTE_TF; lia)).
  apply mk_pte_flags.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    vm_compute; intuition congruence.
Qed.

Lemma tf_variant_ext (tfp : mword 44) (a d : mword 1) :
  ext_bits_of_PTE (pte_set_ad (pte_tf tfp) a d) = Mk_PTE_Ext (mword_of_int 0).
Proof.
  rewrite pte_set_ad_ext.
  unfold pte_tf.
  unfold ext_bits_of_PTE. change (Z.eqb 64 64) with true. cbv iota beta.
  rewrite mk_pte_ext; [reflexivity | unfold PTE_TF; lia].
Qed.

Lemma tf_variant_ppn (tfp : mword 44) (a d : mword 1) :
  autocast (T := mword) ((autocast (T := mword)
     (PPN_of_PTE (pte_set_ad (pte_tf tfp) a d : mword 64))) : mword 44)
  = tfp.
Proof.
  rewrite !autocast_id.
  rewrite pte_set_ad_ppn.
  unfold pte_tf, PPN_of_PTE.
  change (Z.eqb 64 32) with false. cbv iota.
  rewrite autocast_id.
  apply mk_pte_ppn_field. unfold PTE_TF; lia.
Qed.

Lemma tf_variant (tfp : mword 44) (a d : mword 1) :
  pte_valid (pte_set_ad (pte_tf tfp) a d) /\ pte_leaf (pte_set_ad (pte_tf tfp) a d) /\
  pte_no_napot (pte_set_ad (pte_tf tfp) a d) /\ pte_pbmt0 (pte_set_ad (pte_tf tfp) a d).
Proof.
  repeat split.
  - intros s. unfold Mk_PTE_Flags.
    rewrite tf_variant_flags. rewrite tf_variant_ext.
    destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
      vm_compute; reflexivity.
  - unfold pte_leaf, Mk_PTE_Flags.
    rewrite tf_variant_flags.
    destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
      vm_compute; reflexivity.
  - unfold pte_no_napot.
    rewrite tf_variant_ext.
    apply kpt_extN_red.
  - unfold pte_pbmt0.
    rewrite tf_variant_ext.
    vm_compute. reflexivity.
Qed.

(* S-mode data accesses to the trapframe pass the permission check on any
   A/D variant (the leaf is R|W with U=0). *)
Lemma tf_variant_check_load (tfp : mword 44) (a d : mword 1) (mxr do_sum : bool) :
  pte_check_ok (Load Data) Supervisor mxr do_sum (pte_set_ad (pte_tf tfp) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite tf_variant_flags. rewrite tf_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    destruct mxr, do_sum; vm_compute; reflexivity.
Qed.

(* vpn disequalities of the two top pages *)
Lemma tf_vpn_ne_tramp : tf_vpn <> tramp_vpn.
Proof.
  intro H.
  assert (Hu : bv_unsigned tf_vpn = bv_unsigned tramp_vpn) by (rewrite H; reflexivity).
  vm_compute in Hu. congruence.
Qed.

Lemma tf_vpn_unsigned : bv_unsigned tf_vpn = 67108862.
Proof. vm_compute; reflexivity. Qed.

Lemma tramp_vpn_unsigned : bv_unsigned tramp_vpn = 67108863.
Proof. vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(* §2 The layout-free USER mapping spec.                                  *)
(* ===================================================================== *)

(* well-formedness of the user map: every user page sits BELOW the
   trapframe, and its canonical leaf is a proper 4K leaf on every A/D
   variant (established once when the map is built, from the concrete
   R/W/X/U flag byte of each entry). *)
Definition upt_map_wf (um : gmap (mword 27) (mword 64)) : Prop :=
  forall vpn w, um !! vpn = Some w ->
    (bv_unsigned vpn < bv_unsigned tf_vpn)%Z /\
    (forall a d : mword 1,
       pte_valid (pte_set_ad w a d) /\ pte_leaf (pte_set_ad w a d) /\
       pte_no_napot (pte_set_ad w a d) /\ pte_pbmt0 (pte_set_ad w a d)).

Lemma upt_map_wf_not_tramp (um : gmap (mword 27) (mword 64)) (vpn : mword 27) (w : mword 64) :
  upt_map_wf um -> um !! vpn = Some w -> vpn <> tramp_vpn.
Proof.
  intros Hwf Hl ->.
  destruct (Hwf _ _ Hl) as (Hlt & _).
  rewrite tramp_vpn_unsigned tf_vpn_unsigned in Hlt. lia.
Qed.

Lemma upt_map_wf_not_tf (um : gmap (mword 27) (mword 64)) (vpn : mword 27) (w : mword 64) :
  upt_map_wf um -> um !! vpn = Some w -> vpn <> tf_vpn.
Proof.
  intros Hwf Hl ->.
  destruct (Hwf _ _ Hl) as (Hlt & _). lia.
Qed.

(* the user table's mapping spec: trampoline + trapframe + the user map,
   everything else blocks -- and it blocks in the xv6 SHAPE: an unmapped
   vpn's walk stops at a slot holding the LITERAL ZERO word
   ([PtBuild.ptree_blocks0]), not merely at a model-invalid one.  That is
   what every producer of this spec actually builds (a table is a
   memset-zeroed page grown by mappages, and the Svadu A/D write-backs
   only ever touch MAPPED leaves), and it is what the C walk's V-bit test
   dispatches on -- so it is what makes the spec convertible back into an
   exact [pt_rep0] map ([upt_spec_rep0] below). *)
Definition upt_tree_spec (uroot tfp : mword 44)
    (um : gmap (mword 27) (mword 64)) (t : ptree) : Prop :=
  pt_base t = uroot /\
  (exists p2 p1 (a d : mword 1),
     ptree_maps t tramp_vpn p2 p1 (pte_set_ad pte_tramp a d)) /\
  (exists p2 p1 (a d : mword 1),
     ptree_maps t tf_vpn p2 p1 (pte_set_ad (pte_tf tfp) a d)) /\
  (forall vpn w, um !! vpn = Some w ->
     exists p2 p1 (a d : mword 1),
       ptree_maps t vpn p2 p1 (pte_set_ad w a d)) /\
  (forall vpn, vpn <> tramp_vpn -> vpn <> tf_vpn -> um !! vpn = None ->
     ptree_blocks0 t vpn).

(* which canonical leaf a mapped vpn carries *)
Definition upt_leaf_at (tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) (w : mword 64) : Prop :=
  (vpn = tramp_vpn /\ w = pte_tramp) \/
  (vpn = tf_vpn /\ w = pte_tf tfp) \/
  (um !! vpn = Some w).

Lemma upt_spec_maps (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (t : ptree) (vpn : mword 27) (w : mword 64) :
  upt_tree_spec uroot tfp um t ->
  upt_leaf_at tfp um vpn w ->
  exists p2 p1 (a d : mword 1), ptree_maps t vpn p2 p1 (pte_set_ad w a d).
Proof.
  intros (Hbase & Htr & Htf & Hum & Hblk) [(-> & ->) | [(-> & ->) | Hl]].
  - exact Htr.
  - exact Htf.
  - exact (Hum _ _ Hl).
Qed.

Lemma upt_variant (tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) (w : mword 64) :
  upt_map_wf um ->
  upt_leaf_at tfp um vpn w ->
  forall a d : mword 1,
    pte_valid (pte_set_ad w a d) /\ pte_leaf (pte_set_ad w a d) /\
    pte_no_napot (pte_set_ad w a d) /\ pte_pbmt0 (pte_set_ad w a d).
Proof.
  intros Hwf [(-> & ->) | [(-> & ->) | Hl]] a d.
  - exact (tramp_variant a d).
  - exact (tf_variant tfp a d).
  - exact (proj2 (Hwf _ _ Hl) a d).
Qed.

(* ===================================================================== *)
(* §2b THE A/D-EXACT MAP a spec-satisfying tree represents.                *)
(*                                                                        *)
(*    [upt_tree_spec] is deliberately modulo the A/D bits, but the C code  *)
(*    that walks or extends a user table (walk / mappages, via [pt_rep0])  *)
(*    consumes the EXACT vpn -> word map.  The tree is concrete data, so   *)
(*    that map is a FUNCTION of it ([PtBuild.pt_leaf_word]); the two views *)
(*    are related by [upt_ad_view], which says the exact map has exactly   *)
(*    the canonical map's domain (trampoline + trapframe + [um]) and holds *)
(*    an A/D variant of each canonical leaf.                               *)
(* ===================================================================== *)

(* the canonical view as ONE map: what the table maps, ignoring A/D *)
Definition upt_full_map (tfp : mword 44) (um : gmap (mword 27) (mword 64))
    : gmap (mword 27) (mword 64) :=
  <[tramp_vpn := pte_tramp]> (<[tf_vpn := pte_tf tfp]> um).

(* the POSITIVE side: what each of the three kinds of leaf looks up to.
   [upt_full_map_leaf_at] / [_None] below are the elimination forms; these
   are the introduction forms, and they are what a caller phrased against
   the leaf map itself (BarePt's [uptg_map]) needs to enter this file's
   vocabulary. *)
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

(* a USER entry: [upt_map_wf] is what says the vpn is neither fixed vpn, so
   the two inserts miss it. *)
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

Lemma upt_full_map_leaf_at (tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) (w : mword 64) :
  upt_full_map tfp um !! vpn = Some w -> upt_leaf_at tfp um vpn w.
Proof.
  unfold upt_full_map. intros Hl.
  apply lookup_insert_Some in Hl. destruct Hl as [(Hv & Hw) | (_ & Hl)].
  - subst. left. split; reflexivity.
  - apply lookup_insert_Some in Hl. destruct Hl as [(Hv & Hw) | (_ & Hl)].
    + subst. right. left. split; reflexivity.
    + right. right. exact Hl.
Qed.

Lemma upt_full_map_None (tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) :
  upt_full_map tfp um !! vpn = None <->
  (vpn <> tramp_vpn /\ vpn <> tf_vpn /\ um !! vpn = None).
Proof.
  unfold upt_full_map. split.
  - intros Hl.
    apply lookup_insert_None in Hl. destruct Hl as (Hl & Htr).
    apply lookup_insert_None in Hl. destruct Hl as (Hu & Htf).
    split; [exact (not_eq_sym Htr) | split; [exact (not_eq_sym Htf) | exact Hu]].
  - intros (Htr & Htf & Hu).
    apply lookup_insert_None. split; [| exact (not_eq_sym Htr)].
    apply lookup_insert_None. split; [exact Hu | exact (not_eq_sym Htf)].
Qed.

Definition upt_ad_view (tfp : mword 44) (um m_ad : gmap (mword 27) (mword 64)) : Prop :=
  (forall vpn, m_ad !! vpn = None <->
     (vpn <> tramp_vpn /\ vpn <> tf_vpn /\ um !! vpn = None)) /\
  (forall vpn w', m_ad !! vpn = Some w' ->
     exists w (a d : mword 1), upt_leaf_at tfp um vpn w /\ w' = pte_set_ad w a d).

(* OPEN, over an ARBITRARY leaf map [M]: a tree that maps every entry of [M]
   modulo A/D and blocks everywhere else IS an exact [pt_rep0] of some map,
   namely its own leaf words, and that map has [M]'s domain and holds an A/D
   variant of each of [M]'s words.  This is the whole construction; the two
   instances below ([upt_spec_rep0] here, [BarePt.uptg_spec_rep0] at the
   [otf] axis) differ only in which leaf map they feed it. *)
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

(* OPEN: the modulo-A/D spec yields an exact map (the walk/mappages view) --
   [gleaf_spec_rep0] at [upt_full_map], with the [upt_leaf_at] disjunction
   put back on both sides. *)
Lemma upt_spec_rep0 (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (t : ptree) :
  upt_tree_spec uroot tfp um t ->
  exists m_ad, pt_rep0 t m_ad /\ upt_ad_view tfp um m_ad.
Proof.
  intros Hspec.
  pose proof Hspec as (Hbase & Htr & Htf & Hum & Hblk).
  destruct (gleaf_spec_rep0 (upt_full_map tfp um) t
              (fun vpn w Hl =>
                 upt_spec_maps uroot tfp um t vpn w Hspec
                   (upt_full_map_leaf_at tfp um vpn w Hl))
              (fun vpn Hl =>
                 match proj1 (upt_full_map_None tfp um vpn) Hl with
                 | conj Hnt (conj Hntf Hu) => Hblk vpn Hnt Hntf Hu
                 end))
    as (m_ad & Hrep & Hnone & Hsome).
  exists m_ad. split; [exact Hrep |]. split.
  - intros vpn.
    exact (iff_trans (Hnone vpn) (upt_full_map_None tfp um vpn)).
  - intros vpn w' Hl.
    destruct (Hsome vpn w' Hl) as (w & a & d & Hf & Hr).
    exists w, a, d.
    split; [exact (upt_full_map_leaf_at tfp um vpn w Hf) | exact Hr].
Qed.

(* CLOSE: an exact map in the canonical shape re-establishes the spec.
   Serves both of vmfault's exits: the failure arms (map unchanged, tree
   grew interior nodes only) and the success arm (view extended first). *)
Lemma upt_spec_of_rep0 (uroot tfp : mword 44) (um m_ad : gmap (mword 27) (mword 64))
    (t : ptree) :
  upt_map_wf um -> upt_ad_view tfp um m_ad ->
  pt_rep0 t m_ad -> pt_base t = uroot ->
  upt_tree_spec uroot tfp um t.
Proof.
  intros Hwf (Hnone & Hsome) (Hmap & Hblk) Hbase.
  split; [exact Hbase |].
  split.
  { (* trampoline *)
    destruct (m_ad !! tramp_vpn) as [w'|] eqn:Hl.
    - destruct (Hsome _ _ Hl) as (w & a & d & Hleaf & ->).
      destruct (Hmap _ _ Hl) as (p2 & p1 & Hmaps).
      destruct Hleaf as [(_ & ->) | [(Heq & _) | Hu]].
      + exists p2, p1, a, d. exact Hmaps.
      + exfalso. exact (tf_vpn_ne_tramp (eq_sym Heq)).
      + exfalso. exact (upt_map_wf_not_tramp um _ _ Hwf Hu eq_refl).
    - exfalso. destruct (proj1 (Hnone tramp_vpn) Hl) as (Hne & _). exact (Hne eq_refl). }
  split.
  { (* trapframe *)
    destruct (m_ad !! tf_vpn) as [w'|] eqn:Hl.
    - destruct (Hsome _ _ Hl) as (w & a & d & Hleaf & ->).
      destruct (Hmap _ _ Hl) as (p2 & p1 & Hmaps).
      destruct Hleaf as [(Heq & _) | [(_ & ->) | Hu]].
      + exfalso. exact (tf_vpn_ne_tramp Heq).
      + exists p2, p1, a, d. exact Hmaps.
      + exfalso. exact (upt_map_wf_not_tf um _ _ Hwf Hu eq_refl).
    - exfalso. destruct (proj1 (Hnone tf_vpn) Hl) as (_ & Hne & _). exact (Hne eq_refl). }
  split.
  { (* the user map *)
    intros vpn w Hu.
    destruct (m_ad !! vpn) as [w'|] eqn:Hl.
    - destruct (Hsome _ _ Hl) as (w0 & a & d & Hleaf & ->).
      destruct (Hmap _ _ Hl) as (p2 & p1 & Hmaps).
      destruct Hleaf as [(Heq & _) | [(Heq & _) | Hu0]].
      + exfalso. exact (upt_map_wf_not_tramp um vpn w Hwf Hu Heq).
      + exfalso. exact (upt_map_wf_not_tf um vpn w Hwf Hu Heq).
      + assert (Hw : w0 = w) by congruence.
        exists p2, p1, a, d. rewrite <- Hw. exact Hmaps.
    - exfalso. destruct (proj1 (Hnone vpn) Hl) as (_ & _ & Hnn). congruence. }
  (* everything else blocks, in the xv6 zero shape *)
  intros vpn Hnt Hntf Hu.
  apply Hblk. apply (proj2 (Hnone vpn)).
  split; [exact Hnt | split; [exact Hntf | exact Hu]].
Qed.

(* the success-arm extension: a fresh vpn's word is its own A/D variant *)
Lemma upt_ad_view_insert (tfp : mword 44) (um m_ad : gmap (mword 27) (mword 64))
    (vpn : mword 27) (w : mword 64) :
  upt_ad_view tfp um m_ad -> m_ad !! vpn = None ->
  upt_ad_view tfp (<[vpn := w]> um) (<[vpn := w]> m_ad).
Proof.
  intros (Hnone & Hsome) Hl.
  split.
  - intros v. destruct (decide (v = vpn)) as [-> | Hne].
    + rewrite !lookup_insert. split; [discriminate |].
      intros (_ & _ & Hc). discriminate.
    + rewrite (lookup_insert_ne m_ad vpn v w (not_eq_sym Hne)).
      rewrite (lookup_insert_ne um vpn v w (not_eq_sym Hne)).
      exact (Hnone v).
  - intros v w' Hl'. destruct (decide (v = vpn)) as [-> | Hne].
    + rewrite lookup_insert in Hl'.
      assert (Hw : w' = w) by congruence.
      destruct (pte_set_ad_refl w) as (a & d & Hr).
      exists w, a, d. split; [| rewrite Hw; exact Hr].
      right. right. apply lookup_insert.
    + rewrite (lookup_insert_ne m_ad vpn v w (not_eq_sym Hne)) in Hl'.
      destruct (Hsome v w' Hl') as (w0 & a & d & Hleaf & Hr).
      exists w0, a, d. split; [| exact Hr].
      destruct Hleaf as [Ht | [Ht | Hu0]];
        [left; exact Ht | right; left; exact Ht |].
      right. right.
      rewrite (lookup_insert_ne um vpn v w (not_eq_sym Hne)). exact Hu0.
Qed.

(* ...and its OVERWRITE sibling: the vpn is already in [um] (uvmclear
   rewrites one leaf in place), so instead of [m_ad !! vpn = None] the
   premise is [um !! vpn = Some w], and [upt_map_wf] supplies the two
   fixed-vpn disequalities. *)
Lemma upt_ad_view_set (tfp : mword 44) (um m_ad : gmap (mword 27) (mword 64))
    (vpn : mword 27) (w x : mword 64) (a d : mword 1) :
  upt_map_wf um -> upt_ad_view tfp um m_ad -> um !! vpn = Some w ->
  upt_ad_view tfp (<[vpn := x]> um) (<[vpn := pte_set_ad x a d]> m_ad).
Proof.
  intros Hwf (Hnone & Hsome) Hl.
  pose proof (upt_map_wf_not_tramp um vpn w Hwf Hl) as Hntr.
  pose proof (upt_map_wf_not_tf um vpn w Hwf Hl) as Hntf.
  split.
  - intros v. destruct (decide (v = vpn)) as [-> | Hne].
    + rewrite !lookup_insert. split; [discriminate |].
      intros (_ & _ & Hc). discriminate.
    + rewrite (lookup_insert_ne m_ad vpn v (pte_set_ad x a d) (not_eq_sym Hne)).
      rewrite (lookup_insert_ne um vpn v x (not_eq_sym Hne)).
      exact (Hnone v).
  - intros v w' Hl'. destruct (decide (v = vpn)) as [-> | Hne].
    + rewrite lookup_insert in Hl'.
      assert (Hw : w' = pte_set_ad x a d) by congruence.
      exists x, a, d. split; [| exact Hw].
      right. right. apply lookup_insert.
    + rewrite (lookup_insert_ne m_ad vpn v (pte_set_ad x a d) (not_eq_sym Hne)) in Hl'.
      destruct (Hsome v w' Hl') as (w0 & a0 & d0 & Hleaf & Hr).
      exists w0, a0, d0. split; [| exact Hr].
      destruct Hleaf as [Ht | [Ht | Hu0]];
        [left; exact Ht | right; left; exact Ht |].
      right. right.
      rewrite (lookup_insert_ne um vpn v x (not_eq_sym Hne)). exact Hu0.
Qed.

(* ---- the DELETION side (uvmunmap) ----------------------------------- *)

(* Reading an exact-map entry back into the canonical user map.  A vpn that
   is neither the trampoline nor the trapframe and that the exact map maps
   IS in [um], carrying a word the exact one is an A/D variant of.  This is
   the vpn-disequality twin of [ProcPtOwn.upt_ad_view_vu], which walkaddr's
   callers get from the U bit instead; uvmunmap knows its vpn is a user vpn
   from its RANGE, so it needs no flag test. *)
Lemma upt_ad_view_um (tfp : mword 44) (um m_ad : gmap (mword 27) (mword 64))
    (vpn : mword 27) (w' : mword 64) :
  upt_ad_view tfp um m_ad -> m_ad !! vpn = Some w' ->
  vpn <> tramp_vpn -> vpn <> tf_vpn ->
  exists (w : mword 64) (a d : mword 1), um !! vpn = Some w /\ w' = pte_set_ad w a d.
Proof.
  intros (_ & Hsome) Hl Hntr Hntf.
  destruct (Hsome vpn w' Hl) as (w & a & d & Hleaf & Hr).
  destruct Hleaf as [(Ht & _) | [(Ht & _) | Hu]].
  - exfalso. exact (Hntr Ht).
  - exfalso. exact (Hntf Ht).
  - exists w, a, d. split; [exact Hu | exact Hr].
Qed.

(* dropping one USER vpn from both views at once.  Deleting the trampoline or
   the trapframe would break [upt_tree_spec], which is why the disequalities
   are premises rather than conclusions. *)
Lemma upt_ad_view_delete (tfp : mword 44) (um m_ad : gmap (mword 27) (mword 64))
    (vpn : mword 27) :
  vpn <> tramp_vpn -> vpn <> tf_vpn ->
  upt_ad_view tfp um m_ad ->
  upt_ad_view tfp (delete vpn um) (delete vpn m_ad).
Proof.
  intros Hntr Hntf (Hnone & Hsome).
  split.
  - intros v. destruct (decide (v = vpn)) as [-> | Hne].
    + rewrite !lookup_delete. split.
      * intros _. split; [exact Hntr | split; [exact Hntf | reflexivity]].
      * intros _. reflexivity.
    + rewrite (lookup_delete_ne m_ad vpn v (not_eq_sym Hne)).
      rewrite (lookup_delete_ne um vpn v (not_eq_sym Hne)).
      exact (Hnone v).
  - intros v w' Hl'. destruct (decide (v = vpn)) as [-> | Hne].
    { rewrite lookup_delete in Hl'. discriminate. }
    rewrite (lookup_delete_ne m_ad vpn v (not_eq_sym Hne)) in Hl'.
    destruct (Hsome v w' Hl') as (w0 & a & d & Hleaf & Hr).
    exists w0, a, d. split; [| exact Hr].
    destruct Hleaf as [Ht | [Ht | Hu0]];
      [left; exact Ht | right; left; exact Ht |].
    right. right.
    rewrite (lookup_delete_ne um vpn v (not_eq_sym Hne)). exact Hu0.
Qed.

(* the spec survives the A/D write-back at any mapped vpn *)
Lemma upt_tree_spec_set_leaf (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (t : ptree) (vpn : mword 27) (w p2 p1 : mword 64) (a0 d0 a d : mword 1) :
  upt_map_wf um ->
  upt_tree_spec uroot tfp um t ->
  upt_leaf_at tfp um vpn w ->
  ptree_maps t vpn p2 p1 (pte_set_ad w a0 d0) ->
  upt_tree_spec uroot tfp um (ptree_set_leaf t vpn (pte_set_ad w a d)).
Proof.
  intros Hwf Hspec Hleaf Hmaps.
  pose proof Hspec as (Hbase & Htr & Htf & Hum & Hblk).
  assert (Hvarw := upt_variant tfp um vpn w Hwf Hleaf).
  assert (Hself : exists p2' p1' (a' d' : mword 1),
    ptree_maps (ptree_set_leaf t vpn (pte_set_ad w a d)) vpn p2' p1' (pte_set_ad w a' d')).
  { exists p2, p1, a, d.
    rewrite <- (pte_set_ad_absorb w a0 d0 a d).
    apply (ptree_set_leaf_maps_self t vpn p2 p1 (pte_set_ad w a0 d0));
      [exact Hmaps | ..]; rewrite (pte_set_ad_absorb w a0 d0 a d).
    - exact (proj1 (Hvarw a d)).
    - exact (proj1 (proj2 (Hvarw a d))).
    - exact (proj1 (proj2 (proj2 (Hvarw a d)))).
    - exact (proj2 (proj2 (proj2 (Hvarw a d)))). }
  split; [| split; [| split; [| split]]].
  - rewrite <- Hbase.
    unfold ptree_set_leaf.
    destruct (pt_kids t (vpn_idx 2 vpn)); [| reflexivity].
    destruct (pt_kids p (vpn_idx 1 vpn)); reflexivity.
  - (* trampoline *)
    destruct (decide (vpn = tramp_vpn)) as [-> | Hne].
    + destruct Hleaf as [(_ & ->) | [(Heq & _) | Hl]].
      * exact Hself.
      * exfalso. exact (tf_vpn_ne_tramp (eq_sym Heq)).
      * exfalso. exact (upt_map_wf_not_tramp um _ _ Hwf Hl eq_refl).
    + destruct Htr as (q2 & q1 & a' & d' & Hm2).
      exists q2, q1, a', d'.
      apply (ptree_set_leaf_maps_other t vpn tramp_vpn _ _ _ _
               (not_eq_sym Hne) Hm2).
  - (* trapframe *)
    destruct (decide (vpn = tf_vpn)) as [-> | Hne].
    + destruct Hleaf as [(Heq & _) | [(_ & ->) | Hl]].
      * exfalso. exact (tf_vpn_ne_tramp Heq).
      * exact Hself.
      * exfalso. exact (upt_map_wf_not_tf um _ _ Hwf Hl eq_refl).
    + destruct Htf as (q2 & q1 & a' & d' & Hm2).
      exists q2, q1, a', d'.
      apply (ptree_set_leaf_maps_other t vpn tf_vpn _ _ _ _
               (not_eq_sym Hne) Hm2).
  - (* the user map *)
    intros vpn' w' Hl'.
    destruct (decide (vpn' = vpn)) as [-> | Hne].
    + assert (Hw : w' = w).
      { destruct Hleaf as [(-> & _) | [(-> & _) | Hl]].
        - exfalso. exact (upt_map_wf_not_tramp um _ _ Hwf Hl' eq_refl).
        - exfalso. exact (upt_map_wf_not_tf um _ _ Hwf Hl' eq_refl).
        - congruence. }
      subst w'. exact Hself.
    + destruct (Hum _ _ Hl') as (q2 & q1 & a' & d' & Hm2).
      exists q2, q1, a', d'.
      apply (ptree_set_leaf_maps_other t vpn vpn' _ _ _ _ Hne Hm2).
  - intros vpn' Hn1 Hn2 Hn3.
    assert (Hne : vpn' <> vpn).
    { intros ->.
      destruct Hleaf as [(-> & _) | [(-> & _) | Hl]];
        [ exact (Hn1 eq_refl) | exact (Hn2 eq_refl) | congruence ]. }
    apply (ptree_set_leaf0_blocks_other t vpn vpn' p2 p1 (pte_set_ad w a0 d0)
             (pte_set_ad w a d) Hne (ptree_maps_level0 t vpn p2 p1 _ Hmaps));
      [].
    apply (Hblk vpn' Hn1 Hn2 Hn3).
Qed.

(* ===================================================================== *)
(* §3 THE USER TRANSLATION INVARIANT.                                     *)
(* ===================================================================== *)

Section UptTreeInv.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition utlb_inv_pt (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) : iProp Σ :=
    (∃ (usatp : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (t : ptree),
       satp ↦ᵣ usatp ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ⌝ ∗
       ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
       ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ⌝ ∗
       tlb ↦ᵣ tlbvec ∗ ⌜ tlb_ok_pt (mword_of_int 0) t tlbvec ⌝ ∗
       ⌜ upt_tree_spec uroot tfp um t ⌝ ∗
       ⌜ upt_map_wf um ⌝ ∗
       ⌜ forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0 ⌝ ∗
       ptree_own 2 (DfracOwn 1) t ∗
       pmp_config uroot)%I.

  (* THE TRANSLATION MODE IS DEFINED at a state this invariant governs.  The
     vmem level resolves it before every access (it is the page-split test),
     and only the invariant knows satp -- the same obligation [SRegime]'s
     [sr_tmode] discharges for the S-mode regimes. *)
  Lemma utlb_inv_pt_tmode (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (σ : mstate) :
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    reg_interp σ.(sregs) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜ exec (translationMode User) σ = Some (Sv39, σ) ⌝.
  Proof.
    intros HSXL.
    iIntros "Hri Hinv".
    iDestruct "Hinv" as (usatp tlbvec t)
      "(Hsatp & %Hmode & _ & _ & _ & _ & _ & _ & _ & _ & _)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iPureIntro.
    exact (UserTranslate.exec_translationMode_U_sv39 usatp σ HSXL Hsatpv Hmode).
  Qed.

  Lemma utlb_inv_pt_intro (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (usatp : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (t : ptree) :
    _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ->
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    upt_tree_spec uroot tfp um t ->
    upt_map_wf um ->
    (forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0) ->
    satp ↦ᵣ usatp -∗ tlb ↦ᵣ tlbvec -∗ ptree_own 2 (DfracOwn 1) t -∗
    pmp_config uroot -∗
    utlb_inv_pt uroot tfp um.
  Proof.
    intros Hmode Hasid Hppn Hok Hspec Hwf Hpmaw. iIntros "Hsatp Htlb Ht Hpmp".
    iExists usatp, tlbvec, t. iFrame "Hsatp Htlb Ht Hpmp". iPureIntro. tauto.
  Qed.


End UptTreeInv.

(* ===================================================================== *)
(* §4 THE USER INVARIANT ABSORBS TRANSLATION (S-mode: trampoline fetch,   *)
(*    trapframe data -- the userret/uservec paths).                       *)
(* ===================================================================== *)

Section UptTranslateIris.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  (* PRIVILEGE-GENERIC: the mode dispatch comes in as a callback premise
     ([Htmk] -- the satp value lives inside the invariant, so the caller
     cannot supply the closed [translationMode] fact directly); Supervisor
     callers pass [exec_translationMode_S_sv39], User callers
     [exec_translationMode_U_sv39]. *)
  Lemma utlb_inv_pt_translateAddr (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (w va pa : mword 64) (σ : mstate) :
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc p mxr do_sum (pte_set_ad w a d)) ->
    upt_leaf_at tfp um (svpn_of va) w ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = p ->
    (forall satp0 : mword 64,
       register_lookup satp σ.(sregs) = satp0 ->
       _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
       exec (translationMode p) σ = Some (Sv39, σ)) ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) p) σ
      = Some (p, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um.
  Proof.
    intros Hchk Hleaf Hcanon Hout Hmisa Hmenv Hhtif Hcp Htmk Heff Hss Hall.
    iIntros "Hri Hgh Hinv".
    iDestruct "Hinv" as (usatp tlbvec t)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hwf & %Hpmawimpl & Ht & Hpmp)".
    pose proof (Hpmawimpl _ Hall) as Hpmaw.
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    destruct (upt_spec_maps uroot tfp um t (svpn_of va) w Hspec Hleaf)
      as (p2 & p1 & a0 & d0 & Hmaps).
    pose proof Hspec as (Hbase & _).
    assert (HA' : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Hpcv; exact HA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64)
      (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Hpav; exact Hord).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R
      (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Hpcv; exact HR).
    assert (HW' : eq_vec (_get_Pmpcfg_ent_W
      (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Hpcv; exact HW).
    assert (Hcov' : (ram_base + ram_size
      <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Hpav; exact Hcov).
    pose proof (pma_allows_all_pte_read _ Hall) as Hpmar.
    assert (Htm : exec (translationMode p) σ = Some (Sv39, σ))
      by exact (Htmk usatp Hsatpv Hmode).
    iMod (ptree_translateAddr_own acc p uroot t w va pa usatp
            tlbvec p2 p1 a0 d0 σ
            Hchk (upt_variant tfp um (svpn_of va) w Hwf Hleaf) Hcanon Hout Hbase Hmaps Htlbok
            Hmisa Hmenv Hhtif Hcp Htm Heff Hss Hsatpv Hppn Hasid Htlbv
            HA' Hord' HR' HW' Hcov' Hpmar Hpmaw
            with "Hri Hgh Htlb Ht")
      as (σ' t' tlbvec') "(%Htrans & %Hmdev & %Hsregs & %Htsh & %Htlbok' & Hri & Hgh & Htlb & Ht)".
    iModIntro. iExists σ'.
    iSplit; [iPureIntro; exact Htrans |].
    iSplit; [iPureIntro; exact Hmdev |].
    iSplit; [iPureIntro; exact Hsregs |].
    iFrame "Hri Hgh".
    assert (Hspec' : upt_tree_spec uroot tfp um t').
    { destruct Htsh as [-> | (a1 & d1 & ->)]; [exact Hspec |].
      exact (upt_tree_spec_set_leaf uroot tfp um t (svpn_of va) w p2 p1 a0 d0 a1 d1
               Hwf Hspec Hleaf Hmaps). }
    iApply (utlb_inv_pt_intro uroot tfp um usatp tlbvec' t'
              Hmode Hasid Hppn Htlbok' Hspec' Hwf Hpmawimpl with "Hsatp Htlb Ht").
    iApply (pmp_config_intro uroot pmpcfg0 pmpaddr00
              HA Hord HX HW HR Hcov with "Hpc Hpa").
  Qed.

End UptTranslateIris.

(* the S-mode instantiations for the userret / uservec paths: trampoline
   fetch and trapframe load/store, with the concrete-geometry premises in
   the caller-friendly [tramp_ppn]/[tfp] compose forms. *)
Section UptTranslateIrisAcc.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma utlb_inv_pt_translateAddr_tramp_fetch (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va pa : mword 64) (σ : mstate) :
    svpn_of va = tramp_vpn ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec tramp_ppn
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege (InstructionFetch tt) (register_lookup mstatus σ.(sregs)) Supervisor) σ
      = Some (Supervisor, σ) ->
    exec (is_shadow_stack_access (InstructionFetch tt)) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um.
  Proof.
    intros Hvpn Hcanon Hid Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (pte_tramp : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (tramp_variant_ppn ('b"1") ('b"1")) in Hid.
      rewrite pte_set_ad_ppn in Hid. exact Hid. }
    apply (utlb_inv_pt_translateAddr (InstructionFetch tt) Supervisor uroot tfp um pte_tramp va pa σ
             (fun a d mxr do_sum => tramp_variant_check_fetch a d mxr do_sum)
             (or_introl (conj Hvpn eq_refl))
             Hcanon Hout Hmisa Hmenv Hhtif Hcp
             (fun satp0 Hs Hm => exec_translationMode_S_sv39 satp0 σ HSXL Hs Hm)
             Heff Hss Hall).
  Qed.

  Lemma utlb_inv_pt_translateAddr_tf_load (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va pa : mword 64) (σ : mstate) :
    svpn_of va = tf_vpn ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec tfp
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege (Load Data) (register_lookup mstatus σ.(sregs)) Supervisor) σ
      = Some (Supervisor, σ) ->
    exec (is_shadow_stack_access (Load Data)) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) (Load Data)) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um.
  Proof.
    intros Hvpn Hcanon Hid Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (pte_tf tfp : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (tf_variant_ppn tfp ('b"1") ('b"1")) in Hid.
      rewrite pte_set_ad_ppn in Hid. exact Hid. }
    apply (utlb_inv_pt_translateAddr (Load Data) Supervisor uroot tfp um (pte_tf tfp) va pa σ
             (fun a d mxr do_sum => tf_variant_check_load tfp a d mxr do_sum)
             (or_intror (or_introl (conj Hvpn eq_refl)))
             Hcanon Hout Hmisa Hmenv Hhtif Hcp
             (fun satp0 Hs Hm => exec_translationMode_S_sv39 satp0 σ HSXL Hs Hm)
             Heff Hss Hall).
  Qed.

End UptTranslateIrisAcc.
