(* ===================================================================== *)
(* TreeImg.v -- ERA 0's TREE SHAPE, AT THE LITERAL mkfs IMAGE (lane TL-4  *)
(* deliverable 1).                                                       *)
(*                                                                       *)
(* [AppTree.tree_init] mints the era-0 claim of the tree application from *)
(* THREE PURE FACTS about the view a boot founds its file system at:      *)
(*                                                                       *)
(*   [TreeView.aview_tree_wf]  -- unique proper parenthood, and no        *)
(*                                dangling entry;                        *)
(*   [TreeView.adir_at _ ROOTINO] -- the root is a directory of the view; *)
(*   [TreeView.aview_rooted]   -- every proper edge's SOURCE is reachable *)
(*                                from the root (TL-3R's conjunct).       *)
(*                                                                       *)
(* [App.xv6_app_adequacy]'s [Happ_init] binder states that view as        *)
(* [abs_view (fss_inodes (FsDurImg.img_state (fs_blocks dk) sb nib))] --  *)
(* the image's OWN canonical state, not an arbitrary snapshot -- so the   *)
(* three facts are computations on the mkfs image and this file is where  *)
(* they are paid.                                                        *)
(*                                                                       *)
(* WHAT IS COMPUTED, AND WHAT IS NOT.  The view itself is NOT computed:   *)
(* [abs_view] of the image's node map forces every file's contents (~2 MB *)
(* across twenty-two ELF images), which is the trap [FsImgCheck.v]'s      *)
(* header names.  What is computed is THE ROOT'S ENTRY MAP and one        *)
(* region-wide record sweep:                                             *)
(*                                                                       *)
(*   [img_root_ents] -- [dir_view] of the root's data, ~24 records;       *)
(*   [img_root_range_ok] -- every name in it points into [1 .. 23], the   *)
(*     live set [FsImgCheck.fsimg_live_set] already computed;             *)
(*   [img_root_inj_ok] -- no two PROPER names of the root point at one    *)
(*     inum (the dots do: the root's [".."] is the root, which is why the *)
(*     check is at [TreeView.hide_dots]);                                 *)
(*   [fsimg_live_nlink_ok] -- a TYPED record of the region has a nonzero  *)
(*     link count.  One [FsImg.fs_region_free]-shaped pass over the same  *)
(*     thirteen inode blocks, and the only clause no landed sweep         *)
(*     carries: [FsImg.fs_region_nlink] is its converse (a FREE record    *)
(*     has [nlink = 0]) and W3 skips a type-0 record entirely.            *)
(*                                                                       *)
(* WHY THAT IS ENOUGH.  [FsImgCheck.fsimg_dir_root] says the image has    *)
(* exactly ONE directory and it is the root, so every proper edge of the  *)
(* view leaves [ROOTINO] -- which makes [aview_rooted] free               *)
(* ([nreach_refl]) and collapses unique parenthood to the root's own      *)
(* entry map being injective.  Closedness is that map's values being      *)
(* live rows of the view.                                                *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list.
From stdpp.bitvector Require Import definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import own ghost_map mono_nat invariants.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Values.
Require Import RiscvLang.          (* [gstate] *)
Require Import VirtioModel.        (* [v_disk] / [dvirtio] *)
Require Import FsState.            (* [fs_state_rec] / [fss_inodes] *)
Require Import FsStateInode.       (* [fn_type] / [fn_nlink] / [dir_entries] *)
Require Import BioDefs.            (* [BSIZE] *)
Require Import InodeDefs.          (* [file_byte] *)
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.             (* [fname] / [dir_view] / [DOT] *)
Require Import IcacheEscrow.       (* [region_inums_spec] *)
Require Import FsCrash.            (* [fs_blocks] *)
Require Import FsCfgBoot.          (* [img_node] / [img_nodes] / [fs_boot_image_wf] *)
Require Import FsDurImg.           (* [img_state] / [img_root_entries] *)
Require Import FsBootParams.       (* [XV6_DISK_BYTES] / [fsimg_cov] / [fsimg_nib] *)
Require Import FsImgDisk.          (* [fsimg_P] *)
Require Import FsImgCheck.
Require Import FsImg.
Require Import FsAbsDefs.              (* [abs_of] / [abs_view] / [astep] *)
Require Import TreeView.
Require Import App.                (* [xv6_app]'s projections *)
Require Import AppTree.

Local Open Scope Z_scope.

(* [FsImgCheck]'s own [Ltac], which is [Local] there: the cast is built
   directly rather than reduced twice (claude-notes/optimization.md). *)
Local Ltac vm_eq :=
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.

(* ===================================================================== *)
(*  0.  A BOOLEAN [NoDup] FOR [Z] LISTS                                   *)
(*                                                                       *)
(*  Written out rather than taken as [bool_decide (NoDup l)]: the         *)
(*  [Decision] instance for [NoDup] is a [sumbool] over a [Forall]        *)
(*  elaboration whose reduction behaviour under [vm_compute] is not this  *)
(*  file's to guarantee, and the fold below is ten lines.                 *)
(* ===================================================================== *)
Fixpoint zs_nodup (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: l' => negb (List.existsb (Z.eqb x) l') && zs_nodup l'
  end.

Lemma zs_nodup_spec (l : list Z) : zs_nodup l = true -> base.NoDup l.
Proof.
  induction l as [| x l IH]; [intros _; apply NoDup_nil_2 |].
  cbn [zs_nodup]. rewrite andb_true_iff. intros [Hx Hl].
  apply NoDup_cons_2; [| exact (IH Hl)].
  intros Hin. apply negb_true_iff in Hx.
  assert (Hex : List.existsb (Z.eqb x) l = true).
  { apply List.existsb_exists. exists x.
    split; [by apply elem_of_list_In | apply Z.eqb_refl]. }
  rewrite Hex in Hx. discriminate.
Qed.

(* ===================================================================== *)
(*  1.  THE REGION SWEEP NO LANDED CHECK CARRIES                          *)
(*                                                                       *)
(*  "A TYPED RECORD HAS A LINK."  [FsImg.fs_region_nlink] sweeps the      *)
(*  converse (a type-0 record has [nlink = 0]) and W3 skips a type-0      *)
(*  record entirely, so nothing above says that a LIVE inum of the image  *)
(*  has a row in [abs_view] -- which is exactly what era 0's closedness   *)
(*  needs at the inums the root names.  One pass, [fs_region_free]'s own  *)
(*  idiom, over the same thirteen inode blocks and forcing no file        *)
(*  contents.                                                            *)
(* ===================================================================== *)
Definition fs_region_live_nlink (P : Z -> list (bv 8)) (sb : fs_sb)
    (nib : nat) : bool :=
  List.forallb
    (fun i => let dn := fs_dinode P sb (Z.of_nat i) in
              (bv_unsigned (di_type dn) =? 0)
              || negb (bv_unsigned (di_nlink dn) =? 0))
    (seq 0 (16 * nib)%nat).

Lemma fs_region_live_nlink_spec (P : Z -> list (bv 8)) (sb : fs_sb)
    (nib : nat) (z : Z) :
  fs_region_live_nlink P sb nib = true -> 0 <= z < 16 * Z.of_nat nib ->
  bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
  bv_unsigned (di_nlink (fs_dinode P sb z)) <> 0.
Proof.
  intros H Hz Hty.
  pose proof (forallb_seq _ (16 * nib)%nat (Z.to_nat z) H ltac:(lia)) as Hk.
  cbv beta zeta in Hk.
  assert (Hzid : Z.of_nat (Z.to_nat z) = z) by lia. rewrite Hzid in Hk.
  apply orb_true_iff in Hk as [Hk | Hk].
  - exfalso. apply Hty, Z.eqb_eq. exact Hk.
  - apply negb_true_iff, Z.eqb_neq in Hk. exact Hk.
Qed.

Lemma fsimg_live_nlink_ok :
  fs_region_live_nlink fsimg_P fsimg_sb fsimg_nib = true.
Proof. vm_eq. Qed.

Lemma fsimg_live_nlink (z : Z) :
  0 <= z < 208 ->
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb z)) <> 0 ->
  bv_unsigned (di_nlink (fs_dinode fsimg_P fsimg_sb z)) <> 0.
Proof.
  intros Hz.
  apply (fs_region_live_nlink_spec fsimg_P fsimg_sb fsimg_nib z
           fsimg_live_nlink_ok).
  cbv [fsimg_nib]. lia.
Qed.

(* ===================================================================== *)
(*  2.  THE ROOT'S ENTRY MAP, AND THE TWO CHECKS ON IT                    *)
(*                                                                       *)
(*  THE ROOT'S DATA BLOCK IS HOISTED, and that is the difference between  *)
(*  two seconds and fifteen minutes.  [FsImg.fs_data_of] reads a FUNCTION *)
(*  of the block index, so each of [dir_view]'s O(nrec^2) byte accesses   *)
(*  re-decodes a block out of the 2 MB image -- measured ~9,000 decodes   *)
(*  per [dir_view] here, and the pair of checks below took 15m35s in that *)
(*  shape.  Naming the ONE block the root's records live in and reading   *)
(*  the view off a CONSTANT function of it pays the decode once;          *)
(*  [FsDurImg.dir_view_agree] is what says the two readings are the same  *)
(*  map, and [img_root_nrec_leb] is its side condition (the records fit   *)
(*  in the first block).  Same rule as [FsImgCheck.v]'s header: state the *)
(*  FORM TO COMPUTE WITH, never the naive one.                            *)
(* ===================================================================== *)

Definition img_root_blk : list (bv 8) := fsimg_root_data 0%nat.

Definition img_root_ents : gmap fname Z :=
  let b := img_root_blk in dir_view (fun _ : nat => b) fsimg_root_nrec.

(* the root's records fit in its first block: [64 * 16 = BSIZE] *)
Lemma img_root_nrec_leb : Nat.leb fsimg_root_nrec 64 = true.
Proof. vm_eq. Qed.

Lemma img_root_blk_agree (k : nat) :
  (k < fsimg_root_nrec)%nat ->
  dir_win_agree fsimg_root_data (fun _ : nat => img_root_blk) k.
Proof.
  intros Hk j Hj.
  pose proof (proj1 (Nat.leb_le _ _) img_root_nrec_leb) as Hn.
  rewrite /img_root_blk /file_byte.
  assert (H0 : ((16 * k + j) `div` BSIZE = 0)%nat)
    by (apply Nat.div_small; cbv [BSIZE]; lia).
  rewrite H0. reflexivity.
Qed.

Lemma img_root_ents_eq :
  dir_entries (img_node fsimg_P fsimg_sb FsImg.ROOTINO) = img_root_ents.
Proof.
  rewrite (img_root_entries fsimg_P fsimg_sb fsimg_wf_ok).
  rewrite /img_root_ents. symmetry.
  exact (dir_view_agree fsimg_root_data (fun _ : nat => img_root_blk)
           fsimg_root_nrec img_root_blk_agree).
Qed.

(* ---- 2a.  EVERY NAME POINTS INTO THE LIVE SET ----------------------- *)
Definition img_root_range_b : bool :=
  List.forallb (fun kv : fname * Z => (1 <=? kv.2) && (kv.2 <=? 23))
    (map_to_list img_root_ents).

Lemma img_root_range_ok : img_root_range_b = true.
Proof. vm_eq. Qed.

Lemma img_root_range (s : fname) (j : Z) :
  img_root_ents !! s = Some j -> 1 <= j <= 23.
Proof.
  intros Hs.
  assert (Hin : In (s, j) (map_to_list img_root_ents)).
  { rewrite <- elem_of_list_In. by apply elem_of_map_to_list. }
  pose proof img_root_range_ok as H. rewrite /img_root_range_b in H.
  rewrite List.forallb_forall in H.
  specialize (H (s, j) Hin). cbn in H.
  apply andb_true_iff in H as [H1 H2].
  split; [by apply Z.leb_le | by apply Z.leb_le].
Qed.

(* ---- 2b.  NO TWO PROPER NAMES POINT AT ONE INUM ---------------------- *)
(* AT [hide_dots], and it is not a convenience: the root's [".."] IS the
   root, so the unhidden map is not injective and never could be. *)
Definition img_root_inj_b : bool :=
  zs_nodup ((map_to_list (hide_dots img_root_ents)).*2).

Lemma img_root_inj_ok : img_root_inj_b = true.
Proof. vm_eq. Qed.

Lemma img_root_inj (s1 s2 : fname) (j : Z) :
  fs_pname s1 -> fs_pname s2 ->
  img_root_ents !! s1 = Some j -> img_root_ents !! s2 = Some j -> s1 = s2.
Proof.
  intros Hp1 Hp2 H1 H2.
  rewrite <- (hide_dots_lookup img_root_ents s1 Hp1) in H1.
  rewrite <- (hide_dots_lookup img_root_ents s2 Hp2) in H2.
  assert (Hnd : base.NoDup ((map_to_list (hide_dots img_root_ents)).*2))
    by (apply zs_nodup_spec; exact img_root_inj_ok).
  apply elem_of_map_to_list in H1. apply elem_of_map_to_list in H2.
  apply elem_of_list_lookup_1 in H1 as [i1 Hi1].
  apply elem_of_list_lookup_1 in H2 as [i2 Hi2].
  assert (Hf1 : (map_to_list (hide_dots img_root_ents)).*2 !! i1 = Some j)
    by (rewrite list_lookup_fmap Hi1 //).
  assert (Hf2 : (map_to_list (hide_dots img_root_ents)).*2 !! i2 = Some j)
    by (rewrite list_lookup_fmap Hi2 //).
  assert (Hij : i1 = i2)
    by exact (proj1 (NoDup_alt _) Hnd i1 i2 j Hf1 Hf2).
  revert Hi1. rewrite Hij. intros Hi1. rewrite Hi1 in Hi2.
  (* the projection, as a TERM.  No [simplify_eq] and no [injection]
     here: both may normalise the hypothesis to expose a constructor, and
     the hypothesis names [img_root_ents], whose normal form is the whole
     [dir_view] computation this section's [Opaque] exists to prevent
     (measured: 5 GB RSS and climbing). *)
  exact (f_equal (fun o : option (fname * Z) =>
                    match o with Some q => q.1 | None => s1 end) Hi2).
Qed.

(* NOTHING BELOW MAY UNFOLD THE IMAGE COMPUTATION.  Sections 3-5 need only
   [img_root_ents_eq], [img_root_range] and [img_root_inj]; a tactic that
   normalises past this line re-runs [dir_view] over the root's block. *)
Global Opaque img_root_blk img_root_ents img_root_range_b img_root_inj_b.

(* ===================================================================== *)
(*  3.  THE ERA-0 VIEW, ROW BY ROW                                        *)
(* ===================================================================== *)

Definition timg_av : aview :=
  abs_view (fss_inodes (img_state fsimg_P fsimg_sb fsimg_nib)).

Lemma timg_nodes :
  fss_inodes (img_state fsimg_P fsimg_sb fsimg_nib)
  = img_nodes fsimg_P fsimg_sb fsimg_nib.
Proof. reflexivity. Qed.

Lemma timg_row (z : Z) (a : anode) :
  timg_av !! z = Some a ->
  0 <= z < 208 /\ a = abs_row (img_node fsimg_P fsimg_sb z).
Proof.
  intros Ha.
  apply abs_view_lookup_Some in Ha as (n & Hn & Hab).
  rewrite timg_nodes in Hn.
  apply img_nodes_lookup_inv in Hn as [Hz ->].
  apply region_inums_spec in Hz.
  destruct (abs_of_Some _ a Hab) as (_ & _ & ->).
  split; [cbv [fsimg_nib] in Hz; lia | reflexivity].
Qed.

(* the row of a LIVE image inum: the two guards [abs_of] reads *)
Lemma timg_live_row (z : Z) :
  0 <= z < 208 ->
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb z)) <> 0 ->
  timg_av !! z = Some (abs_row (img_node fsimg_P fsimg_sb z)).
Proof.
  intros Hz Hty.
  assert (Hnl : bv_unsigned (di_nlink (fs_dinode fsimg_P fsimg_sb z)) <> 0)
    by exact (fsimg_live_nlink z Hz Hty).
  rewrite /timg_av timg_nodes.
  apply (abs_view_lookup_live _ z (img_node fsimg_P fsimg_sb z)).
  - apply img_nodes_lookup, region_inums_spec. cbv [fsimg_nib]. lia.
  - exact Hty.
  - change (fn_nlink (img_node fsimg_P fsimg_sb z))
      with (Z.to_nat (bv_unsigned (di_nlink (fs_dinode fsimg_P fsimg_sb z)))).
    pose proof (proj1 (bv_unsigned_in_range _
                         (di_nlink (fs_dinode fsimg_P fsimg_sb z)))). lia.
Qed.

(* ONLY THE ROOT IS A DIRECTORY, and its entry map is the computed one *)
Lemma timg_dir (z : Z) (a : anode) (e : gmap fname Z) :
  timg_av !! z = Some a -> an_node a = ADir e ->
  z = FsImg.ROOTINO /\ e = img_root_ents.
Proof.
  intros Ha He.
  destruct (timg_row z a Ha) as [Hz ->].
  apply abs_row_dir_inv in He as [Hd ->].
  rewrite /fn_is_dir in Hd. apply bool_decide_eq_true_1 in Hd.
  assert (Hty : bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb z)) = T_DIR_z)
    by exact Hd.
  assert (Hlt : z < FsImg.sb_ninodes fsimg_sb).
  { destruct (Z_lt_le_dec z 200) as [Hlt | Hge];
      [cbv [fsimg_sb FsImg.sb_ninodes]; lia |].
    exfalso. rewrite (fsimg_region_tail_free z ltac:(lia)) in Hty.
    cbv [T_DIR_z] in Hty. lia. }
  assert (Hroot : z = FsImg.ROOTINO)
    by exact (fsimg_dir_root z (conj (proj1 Hz) Hlt) Hty).
  subst z. split; [reflexivity | exact img_root_ents_eq].
Qed.

(* only a DIRECTORY row answers a hop, and with its own map *)
Lemma anode_ents_dir (a : anode) (e : gmap fname Z) :
  anode_ents a = Some e -> an_node a = ADir e.
Proof.
  rewrite /anode_ents.
  destruct (an_node a) as [bs | e' | ma mi] eqn:Hn;
    [discriminate | | discriminate].
  intros H. injection H as <-. reflexivity.
Qed.

(* EVERY PROPER EDGE LEAVES THE ROOT, at the root's computed map *)
Lemma timg_astep (d : Z) (s : fname) (j : Z) :
  astep timg_av d s = Some j ->
  d = FsImg.ROOTINO /\ img_root_ents !! s = Some j.
Proof.
  rewrite /astep /aents. intros Hst.
  apply bind_Some in Hst as (e & He & Hs).
  apply bind_Some in He as (a & Ha & Hae).
  destruct (timg_dir d a e Ha (anode_ents_dir a e Hae)) as [-> ->].
  by split.
Qed.

(* ===================================================================== *)
(*  4.  THE THREE FACTS [AppTree.tree_init] TAKES                         *)
(* ===================================================================== *)

Lemma timg_adir : adir_at timg_av FsImg.ROOTINO.
Proof.
  assert (Hty : bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb FsImg.ROOTINO))
                = T_DIR_z) by exact fsimg_root_type.
  assert (Hnz : bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb FsImg.ROOTINO))
                <> 0) by (rewrite Hty; cbv [T_DIR_z]; lia).
  pose proof (timg_live_row FsImg.ROOTINO
                ltac:(cbv [FsImg.ROOTINO]; lia) Hnz) as Hrow.
  exists (abs_row (img_node fsimg_P fsimg_sb FsImg.ROOTINO)),
         (dir_entries (img_node fsimg_P fsimg_sb FsImg.ROOTINO)).
  split; [exact Hrow |].
  apply abs_row_dir. apply bool_decide_eq_true_2. exact Hty.
Qed.

Lemma timg_rooted : aview_rooted timg_av.
Proof.
  intros d s i _ Hst.
  destruct (timg_astep d s i Hst) as [-> _]. apply nreach_refl.
Qed.

Lemma timg_uniq_parent : aview_uniq_parent timg_av.
Proof.
  apply aview_uniq_parent_astep.
  intros d1 s1 d2 s2 j Hp1 Hp2 H1 H2.
  destruct (timg_astep d1 s1 j H1) as [-> Hs1].
  destruct (timg_astep d2 s2 j H2) as [-> Hs2].
  split; [reflexivity | exact (img_root_inj s1 s2 j Hp1 Hp2 Hs1 Hs2)].
Qed.

Lemma timg_closed : aview_closed timg_av.
Proof.
  intros d s j _ Hst.
  destruct (timg_astep d s j Hst) as [_ Hs].
  pose proof (img_root_range s j Hs) as Hj.
  apply (proj1 (fsimg_live_iff j)) in Hj as [Hlt Hty].
  exists (abs_row (img_node fsimg_P fsimg_sb j)).
  apply timg_live_row;
    [cbv [fsimg_sb FsImg.sb_ninodes] in Hlt; lia | exact Hty].
Qed.

Lemma timg_tree_wf : aview_tree_wf timg_av.
Proof. split; [exact timg_uniq_parent | exact timg_closed]. Qed.

(* ===================================================================== *)
(*  5.  [App.xv6_app_adequacy]'s [Happ_init], AT [AppTree.app_tree]       *)
(* ===================================================================== *)

Section TreeImgInit.
  Context {Σ : gFunctors} `{!treeG Σ}.

  (* the mint, at the image's own view *)
  Lemma tree_init_img (c : tree_fixed) :
    ⊢ |==> ∃ r : tree_names, tree_pred c r timg_av.
  Proof using .
    iApply (tree_init c timg_av timg_tree_wf timg_adir timg_rooted).
  Qed.

  (* ...AND AT THE THEOREM'S OWN BINDER, on [AppEcho.echo_Happ_init]'s
     mould: [g], [sb], [nib] and [cov] are the theorem's own, and the three
     era-0 equations are what a closed corollary at the real image supplies
     from its own [Hdisk].  [nib] is not one of them and does not have to
     be: [fs_boot_image_wf]'s sixth conjunct PINS it at
     [sb_ninodes sb / 16 + 1], which is 13 at the image's superblock. *)
  Lemma tree_Happ_init (g : gstate) (sb : fs_sb) (nib : nat) (cov : gset Z) :
    fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES sb nib cov ->
    fs_blocks (v_disk (g.(gdev).(dvirtio))) = fsimg_P ->
    sb = fsimg_sb ->
    cov = fsimg_cov ->
    forall c : app_fixed app_tree,
      ⊢ |==> ∃ r : app_names app_tree,
          app_pred app_tree c r
            (abs_view (fss_inodes (img_state
               (fs_blocks (v_disk (g.(gdev).(dvirtio)))) sb nib))).
  Proof using .
    intros Himg Hdk -> -> c.
    assert (Hnib : nib = fsimg_nib).
    { destruct Himg as (_ & _ & _ & _ & _ & Hn & _).
      cbv [fsimg_sb FsImg.sb_ninodes fsimg_nib] in Hn |- *. lia. }
    cbn [app_tree app_fixed app_names app_pred] in c |- *.
    rewrite Hdk Hnib. exact (tree_init_img c).
  Qed.
End TreeImgInit.
