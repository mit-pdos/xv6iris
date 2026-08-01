(* ProcPt.v -- the pure layer for proc_pagetable() (kernel/proc.c): the map a
   freshly created process page table represents, and the bridge from that map
   to [upt_tree_spec], the user-table mapping invariant of UptTree.v.

   proc_pagetable() builds a table with NO user memory: an empty root, then
   exactly two [mappages] runs of one page each --

     mappages(pt, TRAMPOLINE, PGSIZE, trampoline, PTE_R|PTE_X)   (perm 10)
     mappages(pt, TRAPFRAME,  PGSIZE, p->trapframe, PTE_R|PTE_W) (perm 6)

   -- so the represented map is [ppt_map tfp], stated as the two
   [pt_insert_run]s themselves (as KvmMap.v states kvmmake's regions) so each
   mappages post is DEFINITIONALLY the next call's precondition.

   [ppt_bridge] is the deliverable: a tree representing [ppt_map tfp] in the
   xv6 0-shape satisfies [upt_tree_spec (pt_base t) tfp empty t] -- the
   trampoline and trapframe pages map to their canonical leaves (modulo the
   Svadu A/D bits, which mappages writes CLEAR) and every other vpn blocks.
   The A/D bridges are the [pte_tramp]/[pte_tf] analogues of KptTree's
   [kperm_rx_tramp_variant]: [PTE_TRAMP = 0x4B] and [PTE_TF = 0xC7] differ
   from the words mappages writes (0x0B / 0x07) only in the A and D bits.

   The file also carries the budget vocabulary proc_pagetable's proof needs:
   the generic one-page bound [pt_missing_1_le_2], and the sharp fact that the
   TRAPFRAME run allocates NOTHING once the TRAMPOLINE run has run
   ([ppt_missing_tf_zero]) -- the two vpns are adjacent and share both their
   l1 and their l0 group, so the whole function consumes exactly 3 pages. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list list_numbers bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord SailStdpp.Operators_mwords.
Require Import PtAdBits Pt4kWalk PtBuild.
Require Import PtreeType.
Require Import KptExecMap KptTree TrampPt UptTree.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* §1 Small arithmetic identities the two one-page runs need.             *)
(* ===================================================================== *)

(* [RiscvExtras.avi0] at an arbitrary width (its proof is width-generic). *)
Lemma avi_0_gen (n : Z) (a : mword n) : add_vec_int a 0 = a.
Proof.
  unfold add_vec_int, add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
         SailStdpp.Values.with_word, mword_of_int,
         MachineWord.MachineWord.add, MachineWord.MachineWord.Z_to_word.
  apply bv_eq. rewrite bv_add_unsigned Z_to_bv_unsigned.
  rewrite bv_wrap_0 Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma vpn_at_0 (v : mword 27) : vpn_at v 0 = v.
Proof. unfold vpn_at. change (Z.of_nat 0) with 0. apply avi_0_gen. Qed.

Lemma mappages_pte_0 (p : mword 44) (perm : Z) :
  mappages_pte p perm 0 = mk_pte p (Z.lor perm 1).
Proof. unfold mappages_pte. change (Z.of_nat 0) with 0. rewrite avi_0_gen. reflexivity. Qed.

(* a ONE-page run is a single insert *)
Lemma pt_insert_run_1 (m : gmap (mword 27) (mword 64))
    (v : mword 27) (p : mword 44) (perm : Z) :
  pt_insert_run m v p perm 1 = <[v := mappages_pte p perm 0]> m.
Proof. cbn [pt_insert_run]. rewrite vpn_at_0. reflexivity. Qed.

(* ===================================================================== *)
(* §2 The map proc_pagetable builds.                                      *)
(* ===================================================================== *)

(* after the TRAMPOLINE run *)
Definition ppt_m1 : gmap (mword 27) (mword 64) :=
  pt_insert_run ∅ tramp_vpn tramp_ppn 10 1.

(* after the TRAPFRAME run: the finished table's map *)
Definition ppt_map (tfp : mword 44) : gmap (mword 27) (mword 64) :=
  pt_insert_run ppt_m1 tf_vpn tfp 6 1.

Lemma ppt_m1_eq : ppt_m1 = <[tramp_vpn := mappages_pte tramp_ppn 10 0]> ∅.
Proof. unfold ppt_m1. apply pt_insert_run_1. Qed.

Lemma ppt_map_eq (tfp : mword 44) :
  ppt_map tfp = <[tf_vpn := mappages_pte tfp 6 0]>
                  (<[tramp_vpn := mappages_pte tramp_ppn 10 0]> ∅).
Proof. unfold ppt_map. rewrite pt_insert_run_1 ppt_m1_eq. reflexivity. Qed.

Lemma ppt_m1_tramp : ppt_m1 !! tramp_vpn = Some (mappages_pte tramp_ppn 10 0).
Proof. rewrite ppt_m1_eq. apply lookup_insert. Qed.

Lemma ppt_m1_tf : ppt_m1 !! tf_vpn = None.
Proof.
  rewrite ppt_m1_eq. rewrite lookup_insert_ne;
    [apply lookup_empty | intro He; exact (tf_vpn_ne_tramp (eq_sym He))].
Qed.

Lemma ppt_map_tramp (tfp : mword 44) :
  ppt_map tfp !! tramp_vpn = Some (mappages_pte tramp_ppn 10 0).
Proof.
  rewrite ppt_map_eq. rewrite lookup_insert_ne; [apply lookup_insert | exact tf_vpn_ne_tramp].
Qed.

Lemma ppt_map_tf (tfp : mword 44) :
  ppt_map tfp !! tf_vpn = Some (mappages_pte tfp 6 0).
Proof. rewrite ppt_map_eq. apply lookup_insert. Qed.

Lemma ppt_map_other (tfp : mword 44) (vpn : mword 27) :
  vpn <> tramp_vpn -> vpn <> tf_vpn -> ppt_map tfp !! vpn = None.
Proof.
  intros Hnt Hntf. rewrite ppt_map_eq.
  rewrite lookup_insert_ne; [| intro He; exact (Hntf (eq_sym He))].
  rewrite lookup_insert_ne; [| intro He; exact (Hnt (eq_sym He))].
  apply lookup_empty.
Qed.

(* ===================================================================== *)
(* §3 A/D bridges: the words mappages writes ARE the canonical leaves      *)
(*    with A and D clear.                                                  *)
(* ===================================================================== *)

Lemma pte_tramp_from_mappages :
  mappages_pte tramp_ppn 10 0 = pte_set_ad pte_tramp (mword_of_int 0) (mword_of_int 0).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma pte_tf_from_mappages (tfp : mword 44) :
  mappages_pte tfp 6 0 = pte_set_ad (pte_tf tfp) (mword_of_int 0) (mword_of_int 0).
Proof.
  rewrite mappages_pte_0. unfold pte_tf, mk_pte.
  rewrite (pte_set_ad_zext_concat tfp PTE_TF _ _ ltac:(unfold PTE_TF; lia)).
  assert (H7 : (mword_of_int (Z.lor 6 1) : mword 10)
             = mword_of_int (Z.lor (Z.land PTE_TF 831)
                 (Z.lor (Z.shiftl (bv_unsigned (mword_of_int 0 : mword 1)) 6)
                        (Z.shiftl (bv_unsigned (mword_of_int 0 : mword 1)) 7))))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H7. reflexivity.
Qed.

(* also needed by mappages' own precondition, for both perms *)
Lemma ppt_perm_ok10 : mappages_perm_ok 10.
Proof.
  unfold mappages_perm_ok. split; [lia|].
  split; [intro s; vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Lemma ppt_perm_ok6 : mappages_perm_ok 6.
Proof.
  unfold mappages_perm_ok. split; [lia|].
  split; [intro s; vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

(* ===================================================================== *)
(* §4 THE BRIDGE: represented map -> the user-table mapping invariant.     *)
(* ===================================================================== *)

Lemma upt_map_wf_empty : upt_map_wf (∅ : gmap (mword 27) (mword 64)).
Proof. intros vpn w Hl. rewrite lookup_empty in Hl. discriminate. Qed.

Lemma ppt_bridge (t : ptree) (tfp : mword 44) :
  pt_rep0 t (ppt_map tfp) -> upt_tree_spec (pt_base t) tfp ∅ t.
Proof.
  intros (Hmap & Hblk).
  split; [reflexivity |].
  split.
  { destruct (Hmap tramp_vpn _ (ppt_map_tramp tfp)) as (p2 & p1 & Hpm).
    exists p2, p1, (mword_of_int 0), (mword_of_int 0).
    rewrite <- pte_tramp_from_mappages. exact Hpm. }
  split.
  { destruct (Hmap tf_vpn _ (ppt_map_tf tfp)) as (p2 & p1 & Hpm).
    exists p2, p1, (mword_of_int 0), (mword_of_int 0).
    rewrite <- pte_tf_from_mappages. exact Hpm. }
  split.
  { intros vpn w Hl. rewrite lookup_empty in Hl. discriminate. }
  intros vpn Hnt Hntf _.
  apply Hblk. apply ppt_map_other; assumption.
Qed.

(* ===================================================================== *)
(* §5 Budget vocabulary: how many table pages the two runs allocate.       *)
(* ===================================================================== *)

Lemma pt_nodes_empty (b : mword 44) : pt_nodes (pt_empty_node b) = 1%nat.
Proof. unfold pt_nodes. apply pt_nodes_lvl_empty. Qed.

(* a one-page run allocates at most an l1 and an l0 table *)
Lemma pt_missing_1_le_2 (t : ptree) (v : mword 27) : (pt_missing t v 1 <= 2)%nat.
Proof.
  rewrite pt_missing_1_eq.
  assert (H0 : (l0_absent t (bv_unsigned v / 512) <= 1)%nat).
  { unfold l0_absent. destruct (pt_kids t _); [| lia]. destruct (pt_kids _ _); lia. }
  assert (H1 : (l1_absent t (bv_unsigned v / 262144) <= 1)%nat).
  { unfold l1_absent. destruct (pt_kids t _); lia. }
  lia.
Qed.

(* pt_rep0 pins both group-present facts at a MAPPED vpn *)
Lemma pt_rep0_groups_present (t : ptree) (m : gmap (mword 27) (mword 64))
    (vpn : mword 27) (w : mword 64) :
  pt_rep0 t m -> m !! vpn = Some w ->
  l0_absent t (bv_unsigned vpn / 512) = 0%nat /\
  l1_absent t (bv_unsigned vpn / 262144) = 0%nat.
Proof.
  intros (Hmap & _) Hl. destruct (Hmap vpn w Hl) as (p2 & p1 & Hpm).
  pose proof (ptree_maps_level0 t vpn p2 p1 w Hpm) as Hl0.
  split; [ exact (ptree_level0_l0_absent t vpn p2 p1 w Hl0)
         | exact (ptree_level0_l1_absent t vpn p2 p1 w Hl0) ].
Qed.

(* TRAPFRAME sits one page below TRAMPOLINE, so the two vpns share BOTH
   their l1 group (255) and their l0 group (131071): once the trampoline
   run has built the path, the trapframe run allocates nothing. *)
Lemma ppt_missing_tf_zero (t : ptree) :
  pt_rep0 t ppt_m1 -> pt_missing t tf_vpn 1 = 0%nat.
Proof.
  intro Hrep.
  destruct (pt_rep0_groups_present t ppt_m1 tramp_vpn _ Hrep ppt_m1_tramp) as (H0 & H1).
  rewrite tramp_vpn_unsigned in H0, H1.
  rewrite pt_missing_1_eq. rewrite tf_vpn_unsigned.
  assert (Hq0 : (67108862 / 512 = 67108863 / 512)%Z) by (vm_compute; reflexivity).
  assert (Hq1 : (67108862 / 262144 = 67108863 / 262144)%Z) by (vm_compute; reflexivity).
  rewrite Hq0 Hq1 H0 H1. reflexivity.
Qed.
