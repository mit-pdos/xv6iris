(* ====================================================================== *)
(* FsDurImg.v -- THE DURABLE FILE SYSTEM, BUILT FROM AN IMAGE              *)
(*                                                                        *)
(* durable-disk 2c-img, leaf 2, and lane C's image half.  Design of        *)
(* record: claude-notes/design/durable-fs-plan.md sections 2, 4a, 5 (the   *)
(* SNAPSHOT design); claude-notes/design/fs-state.md sections 1-4 for the  *)
(* predicate itself.                                                       *)
(*                                                                        *)
(* WHAT A READER SHOULD LOOK AT FIRST: SECTION 11.  Under the snapshot     *)
(* ruling the durable instance is never updated and never handed anyone    *)
(* else's resource -- it is ALLOCATED from a value and pure facts -- so    *)
(* the image side of the boot is the ONE pure theorem [img_snap_ok]        *)
(* (section 11) plus [FsDurAlloc.P_dur_alloc], which section 12 reads off  *)
(* the image as [img_P_dur_alloc].  That epoch is ALL the boot point asks  *)
(* of this file: [SystemAdequacy] mints the crash predicate itself from    *)
(* it, through [FsCrash.P_fs_alloc].                                       *)
(* THE OLDER RESOURCE-MOVING CONVERSION IS GONE (sections 3, 5,            *)
(* 6, 7 and 10): it distributed the image's blocks into an era instance,   *)
(* which the snapshot ruling made unnecessary, and nothing read it.  What  *)
(* is left is PURE: the image's decoded state (section 8), the link        *)
(* family's validity (section 9) and the snapshot theorem (section 11).    *)
(*                                                                        *)
(* THE BOOT ERA'S COMMITTED BLOCK VIEW is                                  *)
(* [fs_restrict (fs_blocks dk) (fs_home_set cov logstart)], and the        *)
(* snapshot [FsCrash.P_fs] carries is [FsDurSnap.P_dur] of exactly that    *)
(* map.  THIS FILE IS WHERE THE IMAGE IS DECODED into the abstract state   *)
(* that snapshot is [snap_ok] against.                                     *)
(*                                                                        *)
(* IT COMPUTES NOTHING AND NAMES NO LITERAL IMAGE (ruling R3, as           *)
(* [FsCfgBoot] follows it): every image fact arrives as a HYPOTHESIS, in   *)
(* [FsCfgBoot.fs_boot_image_wf]'s own vocabulary, and both adequacy        *)
(* theorems already carry that bundle.  The literal-image discharge stays  *)
(* in [FsImgCheck.v]/[SystemAdequacy.v] and does not move.                  *)
(*                                                                        *)
(* TWO THINGS A READER SHOULD KNOW BEFORE ANYTHING ELSE.                   *)
(*                                                                        *)
(* (1) THE FREE RECORDS NEED THEIR OWN SWEEP: CONJUNCT (14).              *)
(*     [FsState.fs_inodes] iterates [inode_owned] over the WHOLE inode     *)
(*     map, and [inode_owned] carries [FsStateInode.inode_local].  At a    *)
(*     LIVE inum that is [FsStateEra.inode_local_of_ok_rec] off W3/W6/W8   *)
(*     as [FsCfgBoot] already does it; at a FREE one (type 0) NOTHING in   *)
(*     [fsimg_wf] or [fs_region_wf] constrains the record's [size] or      *)
(*     [addrs], so [inl_size] and [inl_covers] are not derivable -- both   *)
(*     would be false of a garbage type-0 record.  [FsImg.fs_region_bare]  *)
(*     is the sweep, in [FsImg.fs_region_free]'s own idiom and reading the *)
(*     same thirteen inode blocks; [FsImgCheck.fsimg_region_bare]          *)
(*     discharges it at the literal image.  It is also what makes a free   *)
(*     inum own NO BLOCK, which section 11's used-set coupling needs.      *)
(*     SINCE LANE C IT IS CONJUNCT (14) OF [FsCfgBoot.fs_boot_image_wf]    *)
(*     rather than a separate premise -- the bundle is what every consumer *)
(*     already carries, and the discharge is still the same citation.      *)
(*                                                                        *)
(* (2) THE LINK FAMILY'S VALIDITY IS A THEOREM, and it costs ONE MORE      *)
(*     IMAGE SWEEP: CONJUNCT (15).  [FsState.fs_boot_alloc_at] needs       *)
(*     [✓ FsState.link_elem I]; [FsState.v]'s header says a map read off   *)
(*     the image discharges it from W9 ([FsImg.fs_links_wf]) plus conjunct *)
(*     (13) ([FsImg.fs_links_eq]).  Those two are NOT enough, because the  *)
(*     image's ticket discipline ([FsImg.fs_rec_ticket], which exempts a   *)
(*     record naming its OWN home under ANY name) and the RA's             *)
(*     ([FsStateInode.ent_tokenless], which exempts only the two dot       *)
(*     NAMES) disagree on exactly one shape: a root record called "foo"    *)
(*     pointing at the root.  [FsImg.fs_root_no_self] rules that shape     *)
(*     out, and section 9 then PROVES [img_link_valid] -- W9 forces the    *)
(*     image to have exactly ONE directory, so the family is one authority *)
(*     per inum composed with the root's outgoing tokens, and the tokens   *)
(*     are covered record by record.  Conjunct (15) of                     *)
(*     [FsCfgBoot.fs_boot_image_wf] since lane C, for (14)'s reason.       *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap gmultiset frac excl numbers.
From iris.base_logic.lib Require Import iprop own ghost_map mono_nat.
Require Import SailStdpp.Operators_mwords.
Require Import RiscvPtsto.
(* EARLY, before the block layer: [FsState] exports four names that collide
   with live ones ([fs_view], [link_auth], [byte_range], [blk_owned]) and
   the LAST import wins -- durable-notes.md. *)
Require Import FsState.
Require Import BioDefs.
Require Import BitmapEnc.
Require Import BlockWords.      (* [ind_bytes] -- [FsDurSnap.sk_ind]'s encoder *)
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.
Require Import InodeInv.
Require Import Xv6Cameras.
Require Import IcacheEscrow.    (* [region_inums] *)
Require Import IcacheBoot.      (* [diblk_bytes_surj] *)
Require Import FsBlocks.
Require Import FsBoot.          (* [big_sepS_carve] / [big_sepS_split_sub] *)
Require Import FsCrash.
Require Import LogDefs.
Require Import FsImg.
Require Import FsImgBridge.
Require Import FsStateBitmap.
Require Import FsStateEra.
Require Import FsBytesGamma.
Require Import FsCfgBoot.       (* [img_nodes] / [fs_boot_image_wf] *)
Require Import Xv6G.
(* LAST: it re-exports [FsStateDefs], whose [byte_range]/[blk_owned] must
   win over the block layer's twins. *)
Require Import FsDurBytes.
(* THE DURABLE SIDE, AND IT IS THE SNAPSHOT ONE (durable-disk lane C):
   [snap_ok] / [P_dur] / [P_dur_alloc].  It re-exports [FsState], so it
   comes after [FsDurBytes] for the same collision reason.  The 3b' object
   and kind algebras are gone from the tree altogether -- the pure-kinds
   tie they carried is the REJECTED design (plan section 8), and section
   11's header says what replaced it here. *)
(* [FsDurBytes] above also carries the durable family record [snap_gamma],
   which [FsDurAlloc]'s conclusion is stated over.  The TRANSPORT is not
   required here: this file names none of it. *)
Require Import FsDurSnap.
Require Import FsDurAlloc.   (* THE VALUE-FIRST ALLOCATOR (lane H5):
                                [P_dur_alloc], whose ONE caller in the
                                tree is this file's [img_P_dur_alloc]
                                below *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  WHERE THE TWO EXTRA IMAGE SWEEPS LIVE                             *)
(* ===================================================================== *)

(*  [FsImg.fs_region_bare] (conjunct (14)) and [FsImg.fs_root_no_self]
    (conjunct (15)) are stated in [FsImg.v], beside [fs_region_free] and
    [fs_links_eq] whose idiom they follow, and discharged at the literal
    image by [FsImgCheck.fsimg_region_bare] / [fsimg_root_no_self].  This
    file only CONSUMES them: (14) in section 11's used-set coupling, (15)
    in section 9.                                                         *)

(* ===================================================================== *)
(*  2.  THE IMAGE'S NODE, READ                                            *)
(* ===================================================================== *)

(* THE IMAGE'S NODE AND ITS WELL-FORMEDNESS live in [FsCfgBoot] now
   (durable-disk lane A): the era's own boot needs them, because the locked
   registry's row -- "every inode the abstract map names is well-formed" --
   is established where the map's authority is
   ([InodeRegion.ftop_alloc]).  This file consumes them through its import
   exactly as before; nothing here moved but the text.  [img_node_rec],
   [img_node_ent], [img_node_blk], [img_node_bare], [img_inode_local_free],
   [img_inode_ok_at], [img_inode_local_live], [img_inode_local]. *)

(* ===================================================================== *)
(*  8.  THE IMAGE'S ABSTRACT STATE                                        *)
(* ===================================================================== *)

(* the state [fs_view Gamma_D] binds at boot.  Every field is a FUNCTION of
   the image: the parsed superblock, block 1's raw bytes (there is no
   superblock encoder in the tree, so [FsState.fs_state_rec] carries the
   bytes), the region's decoded nodes, and the bitmap block's own bit set. *)
Definition img_state (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
  : fs_state_rec :=
  MkFsS sb (P SB_BNO) (img_nodes P sb nib)
        (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb))).

(* ===================================================================== *)
(*  9.  THE LINK FAMILY'S VALIDITY, PROVED FROM THE IMAGE CONJUNCTS      *)
(*                                                                        *)
(*  [FsState.fs_boot_alloc_at]'s premise [✓ link_elem I] is the           *)
(*  tokens-<=-nlink law of the initial map -- the fact                    *)
(*  [FsState.fs_links_valid] READS OFF a durable instance and which the   *)
(*  boot, having none, owes.  It is [img_link_valid] below, and it takes  *)
(*  FOUR image facts: W9 ([FsImg.fs_links_wf]), W6/W7, conjunct (13)      *)
(*  ([FsImg.fs_links_eq]) and conjunct (15)                               *)
(*  ([FsImg.fs_root_no_self]).  The first three are what [FsState.v]'s    *)
(*  header expected; (15) is what this lane found missing, and its        *)
(*  definition's header says why.                                        *)
(*                                                                        *)
(*  THE SHAPE OF THE PROOF, in three moves.                              *)
(*                                                                        *)
(*  (i)  W9 gives the STRUCTURAL half outright, and it is stronger than   *)
(*       expected: at every live inum which is a DIRECTORY W9 forces      *)
(*       [z = ROOTINO], so the image has EXACTLY ONE directory and every  *)
(*       other node's entry map is empty ([img_dir_entries_empty]).  The  *)
(*       family therefore splits into one authority per inum, times the   *)
(*       root's outgoing tokens ([link_elem_split] + [ent_ops_one]), and  *)
(*       since the all-at-home family [FsState.link_full_map] is valid    *)
(*       unconditionally, validity follows from ONE inclusion in          *)
(*       [fsLinkUR] ([link_elem_valid_of_root]).                          *)
(*                                                                        *)
(*  (ii) THE TOKEN-TO-TICKET BRIDGE ([img_link_incl]).  The root's        *)
(*       outgoing tokens are covered by the inodes' own [nlink]s.  The    *)
(*       two counting disciplines exempt different records --             *)
(*       [FsImg.fs_rec_ticket] exempts a record naming its OWN home under *)
(*       ANY name, [FsStateInode.ent_tokenless] only ["."] and an         *)
(*       orphaned-or-self [".."] -- and conjunct (15) is exactly the      *)
(*       difference: with it, every NON-tokenless entry of the root names *)
(*       something other than the root, hence is live-and-not-self, hence *)
(*       bears a ticket.                                                  *)
(*       The counting is done ONCE, by induction on the record count      *)
(*       ([view_ops_incl]): [DirView.dir_view]'s one-step recursion adds  *)
(*       at most one entry, at a name the prefix does not carry, so       *)
(*       [big_opM_insert] applies and the step is a single record's       *)
(*       comparison.  NO multiset argument and NO                         *)
(*       [FsTree.dir_names_unique] is needed -- a name is served by ONE   *)
(*       record because [DirView.dir_first] returns one, and W6's         *)
(*       uniqueness is what the CONVERSE (tickets <= tokens) would want.  *)
(*                                                                        *)
(*  (iii) THE ARITHMETIC ([toks_of_list_incl]).  A ticket list's element  *)
(*       in [fsLinkUR] has, at each key [z], the fragment                 *)
(*       [◯ (fs_tick_count L z)]; [link_toks_of I] is [◯ ∘ fn_nlink]      *)
(*       fmapped over [I].  So the inclusion is per-key [<=], which is    *)
(*       conjunct (13) at a live file inum and W9's directory arm at the  *)
(*       root -- with the root's own tickets bounded by the whole image's *)
(*       supply because [fs_all_tickets] JOINS the per-directory lists.   *)
(* ===================================================================== *)

(* ---- 9a.   THE FAMILY, SPLIT INTO AUTHORITIES AND TOKENS ------------ *)

(* one inode's outgoing tokens, as ONE resource-algebra element: the
   second half of [FsStateInode.link_elem_node] *)
(* one inode's outgoing tokens, as ONE resource-algebra element: the
   second half of [FsStateInode.link_elem_node] *)
Definition ent_ops (i : Z) (n : fs_node) (tyf : fname -> ity) : fsLinkUR :=
  [^op map] s ↦ t ∈ dir_entries n, ent_elem i (fn_orphan n) s t (tyf s).

(* ...and the TWO halves of [FsState.link_full_map].  Under the TYPE
   REGISTER (durable-disk G5) there is no parent column any more: an inum's
   whole ghost is ONE [auth (gmultiset ity)], whose authority is the
   UNIFORM pile [FsStateLink.link_reps (fn_mult n) (fv i)]. *)
Definition link_auths (I : gmap Z fs_node) (fv : Z -> ity) : fsLinkUR :=
  [^op map] i ↦ n ∈ I, link_auth_elem i (fn_mult n) (fv i).
Definition link_toks_of (I : gmap Z fs_node) (fv : Z -> ity) : fsLinkUR :=
  [^op map] i ↦ n ∈ I, link_toks_elem i (link_reps (fn_mult n) (fv i)).

Lemma link_full_map_split (I : gmap Z fs_node) (fv : Z -> ity) :
  link_full_map I fv ≡ link_auths I fv ⋅ link_toks_of I fv.
Proof.
  rewrite /link_full_map /link_auths /link_toks_of.
  rewrite -big_opM_op. apply big_opM_proper. intros i n _.
  rewrite /link_full_elem //.
Qed.

Lemma link_elem_split (I : gmap Z fs_node) (f : link_choice) :
  link_elem I f
  ≡ link_auths I (lc_v f) ⋅ ([^op map] i ↦ n ∈ I, ent_ops i n (lc_tyf f i)).
Proof.
  rewrite /link_elem /link_auths -big_opM_op. apply big_opM_proper.
  intros i n _. rewrite /link_elem_node /ent_ops //.
Qed.

Lemma ent_ops_empty (i : Z) (n : fs_node) (tyf : fname -> ity) :
  dir_entries n = ∅ -> ent_ops i n tyf = ε.
Proof. rewrite /ent_ops. intros ->. rewrite big_opM_empty //. Qed.

(* AT MOST ONE NODE HAS ENTRIES, so the whole family's token half is that
   one node's *)
Lemma ent_ops_one (I : gmap Z fs_node) (f : link_choice) (d : Z)
    (nd : fs_node) :
  I !! d = Some nd ->
  (forall i n, I !! i = Some n -> i <> d -> dir_entries n = ∅) ->
  ([^op map] i ↦ n ∈ I, ent_ops i n (lc_tyf f i)) ≡ ent_ops d nd (lc_tyf f d).
Proof.
  intros Hd Hrest.
  rewrite (big_opM_delete (fun i n => ent_ops i n (lc_tyf f i)) I d nd Hd).
  rewrite (big_opM_proper (fun i n => ent_ops i n (lc_tyf f i))
             (fun (_ : Z) (_ : fs_node) => ε) (delete d I)); last first.
  { intros i n Hi. apply lookup_delete_Some in Hi as [Hne Hi].
    rewrite (ent_ops_empty i n (lc_tyf f i)
               (Hrest i n Hi ltac:(congruence))) //. }
  rewrite big_opM_unit right_id //.
Qed.

(* THE REDUCTION.  [FsState.link_full_map_valid] is unconditional, and
   validity is downward closed, so the whole obligation is one inclusion.

   IT CARRIES A SLACK ELEMENT [e] (durable-disk lane E-clauses), because
   [FsDurSnap.sk_links] is the family's validity WITH one spare fragment at
   the root: the boot mint has to allocate the region's keep-alive token
   ([InodeRegion.ireg_keep]) out of the same [own_alloc].  At [e = ε] this
   is the plain statement, and nothing about the proof changes -- the slack
   rides through the same inclusion into [link_full_map]. *)
Lemma link_elem_valid_of_root (I : gmap Z fs_node) (f : link_choice)
    (d : Z) (nd : fs_node) (e : fsLinkUR) :
  I !! d = Some nd ->
  (forall i n, I !! i = Some n -> i <> d -> dir_entries n = ∅) ->
  ent_ops d nd (lc_tyf f d) ⋅ e ≼ link_toks_of I (lc_v f) ->
  ✓ (link_elem I f ⋅ e).
Proof.
  intros Hd Hrest [x Hx].
  apply (cmra_valid_included (link_elem I f ⋅ e) (link_full_map I (lc_v f))
           (link_full_map_valid I (lc_v f))).
  rewrite (link_full_map_split I (lc_v f)) (link_elem_split I f)
          (ent_ops_one I f d nd Hd Hrest).
  exists x.
  rewrite -(assoc op (link_auths I (lc_v f) ⋅ ent_ops d nd (lc_tyf f d)) e x).
  rewrite -(assoc op (link_auths I (lc_v f)) (ent_ops d nd (lc_tyf f d))
              (e ⋅ x)).
  rewrite (assoc op (ent_ops d nd (lc_tyf f d)) e x) -Hx. reflexivity.
Qed.

(* ---- 9b.   A LIST OF TOKENS AS ONE RA ELEMENT ----------------------- *)

(*  Every unit a ticket list contributes at a key carries THAT KEY'S OWN
    register value -- which is what makes the whole bridge a counting
    argument again: the pile at [z] is [link_reps (count) (fv z)], uniform
    by construction, so the inclusion into the authority's own uniform pile
    is [FsStateLink.link_reps_add] and nothing else. *)
Definition toks_of_list (fv : Z -> ity) (L : list Z) : fsLinkUR :=
  [^op list] t ∈ L, link_tok_elem t (fv t).

Lemma toks_of_list_cons (fv : Z -> ity) (t : Z) (L : list Z) :
  toks_of_list fv (t :: L) ≡ link_tok_elem t (fv t) ⋅ toks_of_list fv L.
Proof. rewrite /toks_of_list big_opL_cons //. Qed.

Lemma toks_of_list_app (fv : Z -> ity) (L1 L2 : list Z) :
  toks_of_list fv (L1 ++ L2) ≡ toks_of_list fv L1 ⋅ toks_of_list fv L2.
Proof. rewrite /toks_of_list big_opL_app //. Qed.

Lemma toks_of_list_singleton (fv : Z -> ity) (t : Z) :
  toks_of_list fv [t] ≡ link_tok_elem t (fv t).
Proof. rewrite /toks_of_list big_opL_singleton //. Qed.

Lemma fs_tick_count_cons (t : Z) (L : list Z) (z : Z) :
  fs_tick_count (t :: L) z
  = (if bool_decide (t = z) then S (fs_tick_count L z)
     else fs_tick_count L z).
Proof. rewrite /fs_tick_count /=. by destruct (bool_decide (t = z)). Qed.

(* THE LOOKUP, in the two directions the inclusion needs: a key carries
   one fragment per naming, and nothing at all when nothing names it --
   [FsImg.fs_tick_count]'s reading in the RA. *)
Lemma toks_of_list_lookup_zero (fv : Z -> ity) (L : list Z) (z : Z) :
  fs_tick_count L z = 0%nat -> toks_of_list fv L !! z = None.
Proof.
  induction L as [| t L IH]; intros H0.
  - reflexivity.
  - rewrite fs_tick_count_cons in H0.
    assert (Hne : t <> z).
    { intros ->. rewrite (bool_decide_eq_true_2 (z = z) eq_refl) in H0.
      discriminate. }
    rewrite (bool_decide_eq_false_2 (t = z) Hne) in H0.
    rewrite /toks_of_list big_opL_cons -/(toks_of_list fv L) lookup_op.
    rewrite /link_tok_elem /link_toks_elem lookup_singleton_ne; [| exact Hne].
    rewrite (IH H0). reflexivity.
Qed.

Lemma toks_of_list_lookup_pos (fv : Z -> ity) (L : list Z) (z : Z) :
  (0 < fs_tick_count L z)%nat ->
  toks_of_list fv L !! z
  ≡ Some ((◯ (link_reps (fs_tick_count L z) (fv z))) : fsLinkElemUR).
Proof.
  induction L as [| t L IH]; intros Hp.
  - rewrite /fs_tick_count /= in Hp. lia.
  - rewrite /toks_of_list big_opL_cons -/(toks_of_list fv L) lookup_op.
    rewrite fs_tick_count_cons in Hp |- *.
    destruct (decide (t = z)) as [-> | Hne].
    + rewrite (bool_decide_eq_true_2 (z = z) eq_refl) in Hp |- *.
      rewrite /link_tok_elem /link_toks_elem lookup_singleton.
      destruct (decide (fs_tick_count L z = 0%nat)) as [H0 | H0].
      * rewrite (toks_of_list_lookup_zero fv L z H0) H0 right_id
          link_reps_1. reflexivity.
      * rewrite (IH ltac:(lia)) -Some_op -auth_frag_op link_reps_S.
        reflexivity.
    + rewrite (bool_decide_eq_false_2 (t = z) Hne) in Hp |- *.
      rewrite /link_tok_elem /link_toks_elem lookup_singleton_ne;
        [| exact Hne].
      rewrite left_id. exact (IH Hp).
Qed.

(* ...and the boot family's token half, read at one key *)
Lemma link_toks_of_lookup (I : gmap Z fs_node) (fv : Z -> ity) (z : Z) :
  link_toks_of I fv !! z
  ≡ (fun n => (◯ (link_reps (fn_mult n) (fv z)) : fsLinkElemUR))
    <$> (I !! z).
Proof.
  revert z. induction I as [| i n I Hi IH] using map_ind; intros z.
  - rewrite /link_toks_of big_opM_empty lookup_empty //.
  - assert (Heq : link_toks_of (<[i := n]> I) fv
                  ≡ link_toks_elem i (link_reps (fn_mult n) (fv i))
                    ⋅ link_toks_of I fv)
      by (rewrite /link_toks_of big_opM_insert //).
    rewrite (Heq z) lookup_op.
    destruct (decide (z = i)) as [-> | Hne].
    + pose proof (IH i) as IHz. rewrite Hi in IHz. simpl in IHz.
      rewrite /link_toks_elem lookup_singleton lookup_insert IHz right_id.
      reflexivity.
    + rewrite /link_toks_elem lookup_singleton_ne; [| by apply not_eq_sym].
      rewrite lookup_insert_ne; [| by apply not_eq_sym].
      rewrite left_id. exact (IH z).
Qed.

(* THE INCLUSION, per key *)
Lemma toks_of_list_incl (fv : Z -> ity) (L : list Z) (I : gmap Z fs_node) :
  (forall z : Z, (0 < fs_tick_count L z)%nat ->
     exists n : fs_node,
       I !! z = Some n /\ (fs_tick_count L z <= fn_mult n)%nat) ->
  toks_of_list fv L ≼ link_toks_of I fv.
Proof.
  intros H. apply lookup_included. intros z.
  destruct (decide (fs_tick_count L z = 0%nat)) as [H0 | H0].
  - rewrite (toks_of_list_lookup_zero fv L z H0). apply option_included.
    by left.
  - destruct (H z ltac:(lia)) as (n & Hn & Hle).
    rewrite (toks_of_list_lookup_pos fv L z ltac:(lia)).
    rewrite (link_toks_of_lookup I fv z) Hn /=.
    apply Some_included_2. right. apply auth_frag_mono, gmultiset_included.
    replace (fn_mult n)
      with (fs_tick_count L z + (fn_mult n - fs_tick_count L z))%nat by lia.
    rewrite link_reps_add. multiset_solver.
Qed.

(* ---- 9c.   THE COUNT OVER A JOINED TICKET SUPPLY --------------------- *)

Lemma fs_tick_count_app (L1 L2 : list Z) (z : Z) :
  fs_tick_count (L1 ++ L2) z
  = (fs_tick_count L1 z + fs_tick_count L2 z)%nat.
Proof. rewrite /fs_tick_count List.filter_app length_app //. Qed.

Lemma fs_tick_count_join (ls : list (list Z)) (l : list Z) (z : Z) :
  l ∈ ls -> (fs_tick_count l z <= fs_tick_count (mjoin ls) z)%nat.
Proof.
  induction ls as [| a ls IH]; intros Hl.
  - by apply elem_of_nil in Hl.
  - change (mjoin (a :: ls)) with (a ++ mjoin ls).
    rewrite fs_tick_count_app.
    apply elem_of_cons in Hl as [-> | Hl]; [lia |].
    pose proof (IH Hl). lia.
Qed.

Lemma fs_tick_count_elem (L : list Z) (z : Z) :
  (0 < fs_tick_count L z)%nat -> z ∈ L.
Proof.
  rewrite /fs_tick_count. intros H.
  destruct (List.filter (fun t => bool_decide (t = z)) L) as [| a l] eqn:E;
    [cbn in H; lia |].
  assert (Hin : List.In a (List.filter (fun t => bool_decide (t = z)) L))
    by (rewrite E; left; reflexivity).
  apply List.filter_In in Hin as [Hin Ha].
  apply bool_decide_eq_true in Ha. subst a.
  by apply elem_of_list_In.
Qed.

(* ---- 9d.   A DIRECTORY'S VIEW READ AT AGREEING BYTES ----------------- *)

(*  [FsStateInode.dir_entries] reads [FsStateInode.fn_data] of the node --
    the node's own block map, with a zero block at every hole -- while the
    image's sweeps read [FsImg.fs_data_of].  The two agree on every block a
    directory's records can reach ([img_node_file_byte]), and these three
    are the transport.  [DirView]'s [dir_win_agree] family does the
    per-record half; only the two SCANS need saying.                       *)

(* [DirView.dir_bname_agree] is stated at the UNFOLDED [bname 14 …]; the
   two scans below meet it folded as [FsTree.dir_bname]. *)
Lemma dir_bname_win_agree (data data' : nat -> list (bv 8)) (k : nat) :
  dir_win_agree data data' k -> dir_bname data' k = dir_bname data k.
Proof. intros H. unfold dir_bname. exact (dir_bname_agree data data' k H). Qed.

Lemma dir_first_agree (data data' : nat -> list (bv 8)) (n : nat)
    (s : fname) :
  (forall k : nat, (k < n)%nat -> dir_win_agree data data' k) ->
  dir_first data' n s = dir_first data n s.
Proof.
  intros H. unfold dir_first. apply dfirst_ext. intros j Hj.
  unfold dir_matchb.
  rewrite (dir_liveb_agree data data' j (H j Hj)).
  rewrite (dir_bname_agree data data' j (H j Hj)). reflexivity.
Qed.

Lemma dir_wins_agree (data data' : nat -> list (bv 8)) (n : nat) :
  (forall k : nat, (k <= n)%nat -> dir_win_agree data data' k) ->
  dir_wins data' n = dir_wins data n.
Proof.
  intros H. unfold dir_wins.
  rewrite (dir_liveb_agree data data' n ltac:(apply H; lia)).
  rewrite (dir_bname_win_agree data data' n ltac:(apply H; lia)).
  rewrite (dir_first_agree data data' n (dir_bname data n)
             ltac:(intros k Hk; apply H; lia)).
  reflexivity.
Qed.

Lemma dir_view_agree (data data' : nat -> list (bv 8)) (n : nat) :
  (forall k : nat, (k < n)%nat -> dir_win_agree data data' k) ->
  dir_view data' n = dir_view data n.
Proof.
  induction n as [| n IH]; intros H; [reflexivity |].
  rewrite !dir_view_S.
  rewrite (IH ltac:(intros k Hk; apply H; lia)).
  rewrite (dir_wins_agree data data' n ltac:(intros k Hk; apply H; lia)).
  destruct (dir_wins data n); [| reflexivity].
  rewrite (dir_bname_win_agree data data' n ltac:(apply H; lia)).
  rewrite (dir_inum_agree data data' n ltac:(apply H; lia)).
  reflexivity.
Qed.

(* ...and the agreement itself, at the image's node *)
Lemma img_blkmap_holes (P : Z -> list (bv 8)) (dn : dinode) :
  dinode_wf dn -> blk_holes_zero (img_blkmap P dn) (fs_data_of P dn).
Proof.
  intros Hwf i Hi H0. apply fs_data_of_holes.
  rewrite <- (img_blkmap_get P dn i Hwf Hi). exact H0.
Qed.

Lemma img_node_data (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) (k : nat) :
  (k < MAXFILE)%nat ->
  fn_data (img_node P sb z) k = fs_data_of P (fs_dinode P sb z) k.
Proof.
  intros Hk.
  exact (era_node_data (fs_dinode P sb z) (img_blkmap P (fs_dinode P sb z))
           (fs_data_of P (fs_dinode P sb z)) k
           (img_blkmap_holes P (fs_dinode P sb z) (fs_dinode_wf P sb z)) Hk).
Qed.

Lemma img_node_file_byte (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z)
    (x : nat) :
  (x < MAXFILE * BSIZE)%nat ->
  file_byte (fn_data (img_node P sb z)) x
  = file_byte (fs_data_of P (fs_dinode P sb z)) x.
Proof.
  intros Hx. unfold file_byte. rewrite img_node_data; [reflexivity |].
  apply Nat.div_lt_upper_bound; [unfold BSIZE; lia | lia].
Qed.

(* THE ROOT'S ENTRY MAP, at the image's own byte reading *)
Lemma img_root_entries (P : Z -> list (bv 8)) (sb : fs_sb) :
  fsimg_wf P sb = true ->
  dir_entries (img_node P sb FsImg.ROOTINO)
  = dir_view (fs_data_of P (fs_dinode P sb FsImg.ROOTINO))
      (dir_nrec (bv_unsigned (di_size (fs_dinode P sb FsImg.ROOTINO)))).
Proof.
  intros Hwf.
  assert (Hty : bv_unsigned (di_type (fs_dinode P sb FsImg.ROOTINO))
                = T_DIR_z)
    by exact (fs_root_wf_type P sb (fsimg_wf_root P sb Hwf)).
  assert (Hnin : 0 <= FsImg.ROOTINO < FsImg.sb_ninodes sb).
  { pose proof (sbo_ninodes sb (fsimg_wf_sb P sb Hwf)).
    unfold FsImg.ROOTINO in *. lia. }
  assert (Hok : fs_inode_ok P sb (fs_dinode P sb FsImg.ROOTINO)).
  { apply (fsimg_wf_inode P sb FsImg.ROOTINO Hwf Hnin).
    rewrite Hty. unfold T_DIR_z. lia. }
  pose proof (fio_size P sb (fs_dinode P sb FsImg.ROOTINO) Hok) as Hsz.
  pose proof (proj1 (bv_unsigned_in_range _
                       (di_size (fs_dinode P sb FsImg.ROOTINO)))) as Hsz0.
  rewrite /dir_entries.
  assert (Hdir : fn_is_dir (img_node P sb FsImg.ROOTINO) = true)
    by (apply bool_decide_eq_true; exact Hty).
  rewrite Hdir.
  change (fn_nrec (img_node P sb FsImg.ROOTINO))
    with (dir_nrec (bv_unsigned (di_size (fs_dinode P sb FsImg.ROOTINO)))).
  apply dir_view_agree. intros k Hk j Hj.
  apply img_node_file_byte.
  (* the records live below [MAXFILE] blocks, by W3's size cap *)
  assert (H16 : 16 * (bv_unsigned (di_size (fs_dinode P sb FsImg.ROOTINO))
                      / 16)
                <= bv_unsigned (di_size (fs_dinode P sb FsImg.ROOTINO)))
    by (apply Z.mul_div_le; lia).
  unfold dir_nrec in Hk.
  unfold MAXFILE, BSIZE. unfold FS_MAXFILE, BSIZE_z in Hsz. lia.
Qed.

(* ---- 9e.   THE INDUCTION: EVERY NON-TOKENLESS ENTRY BEARS A TICKET ---- *)

(*  Generic in the ticket function, so nothing here knows about an image:
    the RA's [FsStateInode.ent_elem] and a ticket are compared record by
    record.  The premise is the WHOLE content of the bridge -- a record
    that WINS its name and owes a token has a ticket naming the same inum
    -- and the induction is [DirView.dir_view]'s own one-step recursion,
    which adds at most one entry at a name the prefix does not carry, so
    [big_opM_insert] applies and no multiset argument is needed.

    ONE NAME IS EXEMPT ([ex], durable-disk G5).  Under the TYPE REGISTER a
    directory's [.] record owes a fragment -- it is what pins the parent in
    [FsStateInode.ent_ty_ok] -- and [FsImg.fs_rec_ticket] does not ticket
    it, because it names its own home.  Rather than count the exempt record
    against the ticket supply, the caller DELETES its name from the map and
    covers that one fragment out of the multiplicity's own [+1] for a live
    directory.  At [ex] a name no record carries this is the plain
    statement.                                                             *)
Lemma view_ops_incl (data : nat -> list (bv 8)) (self : Z) (orph : bool)
    (tick : nat -> option Z) (fv : Z -> ity) (tyf : fname -> ity)
    (ex : fname) (n : nat) :
  (forall k : nat, (k < n)%nat -> dir_wins data k = true ->
     dir_bname data k <> ex ->
     ent_tokenless self orph (dir_bname data k)
       (bv_unsigned (dir_inum data k)) = false ->
     tick k = Some (bv_unsigned (dir_inum data k))
     /\ tyf (dir_bname data k) = fv (bv_unsigned (dir_inum data k))) ->
  ([^op map] s ↦ t ∈ delete ex (dir_view data n),
     ent_elem self orph s t (tyf s))
    ≼ toks_of_list fv (omap tick (seq 0 n)).
Proof.
  induction n as [| n IH].
  - intros _. rewrite dir_view_nil delete_empty big_opM_empty.
    apply ucmra_unit_least.
  - intros Hself.
    assert (IHn : ([^op map] s ↦ t ∈ delete ex (dir_view data n),
                     ent_elem self orph s t (tyf s))
                    ≼ toks_of_list fv (omap tick (seq 0 n)))
      by (apply IH; intros k Hk; apply Hself; lia).
    rewrite seq_S. replace (0 + n)%nat with n by lia.
    rewrite omap_app toks_of_list_app dir_view_S.
    destruct (dir_wins data n) eqn:Hw; last first.
    { rewrite right_id_L.
      apply (cmra_included_trans _
               (toks_of_list fv (omap tick (seq 0 n))));
        [exact IHn |].
      exists (toks_of_list fv (omap tick [n])). reflexivity. }
    (* the record enters the view, at a name the prefix does not carry *)
    assert (Hfresh : dir_view data n !! dir_bname data n = None).
    { apply dir_view_lookup_None.
      exact (proj2 (proj1 (dir_wins_true data n) Hw)). }
    rewrite insert_empty -insert_union_singleton_r; [| exact Hfresh].
    destruct (decide (dir_bname data n = ex)) as [Hex | Hex].
    { (* THE EXEMPT NAME: the caller carries it, so nothing is added *)
      rewrite Hex delete_insert_delete.
      apply (cmra_included_trans _
               (toks_of_list fv (omap tick (seq 0 n))));
        [exact IHn |].
      exists (toks_of_list fv (omap tick [n])). reflexivity. }
    rewrite (delete_insert_ne (dir_view data n) ex (dir_bname data n)
               (bv_unsigned (dir_inum data n)) ltac:(congruence)).
    assert (Hfresh' : delete ex (dir_view data n) !! dir_bname data n = None)
      by (rewrite lookup_delete_ne; [exact Hfresh | congruence]).
    rewrite (big_opM_insert (fun s t => ent_elem self orph s t (tyf s))
               (delete ex (dir_view data n)) (dir_bname data n)
               (bv_unsigned (dir_inum data n)) Hfresh').
    rewrite (cmra_comm (ent_elem self orph (dir_bname data n)
                          (bv_unsigned (dir_inum data n))
                          (tyf (dir_bname data n)))).
    apply cmra_mono; [exact IHn |].
    (* the one record's comparison *)
    destruct (ent_tokenless self orph (dir_bname data n)
                (bv_unsigned (dir_inum data n))) eqn:Htl.
    { rewrite /ent_elem Htl. apply ucmra_unit_least. }
    pose proof (Hself n ltac:(lia) Hw Hex Htl) as [Ht Hpv].
    assert (Homap : omap tick [n] = [bv_unsigned (dir_inum data n)])
      by (cbn; rewrite Ht; reflexivity).
    rewrite Homap toks_of_list_singleton /ent_elem Htl Hpv.
    exists ε. by rewrite right_id.
Qed.

(*  ...at the image's ticket function.  The exempt name is [DOT]: it is the
    only record of a well-formed directory that names its own home and
    still owes a fragment, so with it deleted every remaining token-owing
    winner is a NAME record, which [FsImg.fs_rec_ticket] tickets.          *)
Lemma view_ops_incl_tickets (P : Z -> list (bv 8)) (self : Z) (dn : dinode)
    (orph : bool) (fv : Z -> ity) (tyf : fname -> ity) :
  (forall k : nat,
     (k < dir_nrec (bv_unsigned (di_size dn)))%nat ->
     dir_wins (fs_data_of P dn) k = true ->
     dir_bname (fs_data_of P dn) k <> DOT ->
     ent_tokenless self orph (dir_bname (fs_data_of P dn) k)
       (bv_unsigned (dir_inum (fs_data_of P dn) k)) = false ->
     tyf (dir_bname (fs_data_of P dn) k)
     = fv (bv_unsigned (dir_inum (fs_data_of P dn) k))) ->
  ([^op map] s ↦ t ∈ delete DOT (dir_view (fs_data_of P dn)
                                   (dir_nrec (bv_unsigned (di_size dn)))),
     ent_elem self orph s t (tyf s))
    ≼ toks_of_list fv (fs_dir_tickets P self dn).
Proof.
  intros Hpv. rewrite /fs_dir_tickets.
  apply view_ops_incl. intros k Hk Hw Hex Htl.
  split; [| exact (Hpv k Hk Hw Hex Htl)].
  assert (Hlv : dir_live (fs_data_of P dn) k)
    by exact (dir_wins_live (fs_data_of P dn) k Hw).
  (* the record does not name its own home: [ent_tokenless]'s SELF clause
     exempts every such record BUT [.], and [.] is the deleted name *)
  assert (Hne : bv_unsigned (dir_inum (fs_data_of P dn) k) <> self).
  { intros Hc. rewrite /ent_tokenless Hc in Htl.
    rewrite (bool_decide_eq_true_2 (self = self) eq_refl) in Htl.
    rewrite (bool_decide_eq_false_2 (dir_bname (fs_data_of P dn) k = DOT) Hex)
      in Htl.
    destruct (bool_decide (dir_bname (fs_data_of P dn) k = DOTDOT)), orph;
      simpl in Htl; discriminate. }
  rewrite /fs_rec_ticket. cbv zeta.
  rewrite (proj2 (dir_liveb_true (fs_data_of P dn) k) Hlv).
  rewrite (bool_decide_eq_false_2 _ Hne). reflexivity.
Qed.

(* ---- 9f.   THE IMAGE'S OWN INSTANCE ---------------------------------- *)

Lemma img_nodes_lookup_inv (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) (n : fs_node) :
  img_nodes P sb nib !! z = Some n ->
  z ∈ region_inums nib /\ n = img_node P sb z.
Proof.
  intros Hz. rewrite /img_nodes in Hz.
  apply elem_of_list_to_map_2 in Hz.
  apply elem_of_list_fmap in Hz as (y & Heq & Hy).
  injection Heq as -> ->. split; [| reflexivity].
  by apply elem_of_elements.
Qed.

(* W9's STRUCTURAL HALF: the image has exactly one directory, the root. *)
Lemma img_dir_entries_empty (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) :
  fsimg_wf P sb = true -> fs_region_wf P sb nib = true ->
  z ∈ region_inums nib -> z <> FsImg.ROOTINO ->
  dir_entries (img_node P sb z) = ∅.
Proof.
  intros Hwf Hrw Hz Hne. apply region_inums_spec in Hz.
  rewrite /dir_entries.
  destruct (fn_is_dir (img_node P sb z)) eqn:Hd; [| reflexivity].
  exfalso.
  assert (Hty : bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z)
    by exact (proj1 (bool_decide_eq_true _) Hd).
  assert (Hran : 0 <= z < FsImg.sb_ninodes sb).
  { split; [lia |].
    destruct (Z_lt_ge_dec z (FsImg.sb_ninodes sb)) as [Hlt | Hge];
      [exact Hlt |].
    exfalso.
    rewrite (fs_region_free_spec P sb nib z (fs_region_wf_free _ _ _ Hrw)
               ltac:(lia) ltac:(lia) ltac:(lia)) in Hty.
    rewrite /T_DIR_z in Hty. discriminate. }
  destruct (proj2 (fs_links_wf_at P sb z (fsimg_wf_links P sb Hwf) Hran) Hty)
    as (_ & _ & Hroot).
  exact (Hne Hroot).
Qed.

(* ---- 9g.   THE BRIDGE ------------------------------------------------ *)

(* THE IMAGE'S REGISTER CHOICE (durable-disk G5).  An inum's value is
   [TDir p] at a directory and [TFile] otherwise, and a well-formed image
   has exactly ONE directory -- the root, whose [..] names itself (W9's
   (T) plus [FsImg.fs_root_wf_dotdot]) -- so the parent is [ROOTINO]
   everywhere it is read.  The ENTRY function reads the target's value off
   the target's own node: that is the one cross-inode reading the value
   side does, and it is what makes [FsStateInode.ent_ty_ok] hold at every
   record of the image at once. *)
Definition img_v (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) : ity :=
  if fn_is_dir (img_node P sb z) then TDir FsImg.ROOTINO else TFile.

Definition img_f (P : Z -> list (bv 8)) (sb : fs_sb) : link_choice :=
  fun z => (∅, (img_v P sb z,
                fun s => match dir_entries (img_node P sb z) !! s with
                         | Some t => img_v P sb t
                         | None => TFile
                         end)).

Lemma img_f_v (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  lc_v (img_f P sb) z = img_v P sb z.
Proof. reflexivity. Qed.

Lemma img_f_tyf (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) (s : fname) :
  lc_tyf (img_f P sb) z s
  = match dir_entries (img_node P sb z) !! s with
    | Some t => img_v P sb t
    | None => TFile
    end.
Proof. reflexivity. Qed.

Lemma img_f_D (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  lc_D (img_f P sb) z = ∅.
Proof. reflexivity. Qed.

(* THE ROOT IS THE IMAGE'S ONLY DIRECTORY, and its record says [nlink = 1]:
   the two readings both branches below want. *)
Lemma img_root_dir (P : Z -> list (bv 8)) (sb : fs_sb) :
  fsimg_wf P sb = true ->
  fn_is_dir (img_node P sb FsImg.ROOTINO) = true
  /\ fn_nlink (img_node P sb FsImg.ROOTINO) = 1%nat
  /\ fn_orphan (img_node P sb FsImg.ROOTINO) = false
  /\ fn_mult (img_node P sb FsImg.ROOTINO) = 2%nat.
Proof.
  intros Hwf.
  assert (Hty : bv_unsigned (di_type (fs_dinode P sb FsImg.ROOTINO))
                = T_DIR_z)
    by exact (fs_root_wf_type P sb (fsimg_wf_root P sb Hwf)).
  assert (Hd : fn_is_dir (img_node P sb FsImg.ROOTINO) = true)
    by (apply bool_decide_eq_true; rewrite /fn_type img_node_rec; exact Hty).
  destruct (fsimg_wf_root_link P sb Hwf) as [_ Hnl1].
  assert (Hnl : fn_nlink (img_node P sb FsImg.ROOTINO) = 1%nat)
    by (rewrite /fn_nlink img_node_rec Hnl1 //).
  assert (Ho : fn_orphan (img_node P sb FsImg.ROOTINO) = false)
    by (rewrite /fn_orphan Hnl (bool_decide_eq_false_2 (1%nat = 0%nat)); [done | lia]).
  split_and!; [exact Hd | exact Hnl | exact Ho |].
  rewrite /fn_mult Hnl Hd Ho //.
Qed.

(* IT CARRIES THE ROOT'S KEEP-ALIVE TOKEN (durable-disk lane E-clauses) AND
   THE ROOT'S OWN [.] FRAGMENT (G5).  Both sit at [ROOTINO] and both ride
   as consed heads of the ticket list: the root receives no ticket at all
   ([FsImg.fsimg_wf_root_link]: [fs_link_count P sb ROOTINO = 0], W9's
   directory arm) while its multiplicity is [nlink + 1 = 2], so the two
   spare fragments are EXACTLY covered.  That is the non-vacuity witness
   plan section 7 demands, at xv6's own mkfs image. *)
Lemma img_link_incl (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
  fsimg_wf P sb = true -> fs_links_eq P sb = true ->
  fs_root_no_self P sb = true ->
  FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
  ent_ops FsImg.ROOTINO (img_node P sb FsImg.ROOTINO)
    (lc_tyf (img_f P sb) FsImg.ROOTINO)
    ⋅ link_tok_elem FsImg.ROOTINO (img_v P sb FsImg.ROOTINO)
    ≼ link_toks_of (img_nodes P sb nib) (img_v P sb).
Proof.
  intros Hwf Heq Hns Hnib.
  assert (Hty : bv_unsigned (di_type (fs_dinode P sb FsImg.ROOTINO))
                = T_DIR_z)
    by exact (fs_root_wf_type P sb (fsimg_wf_root P sb Hwf)).
  assert (Hnin : 0 <= FsImg.ROOTINO < FsImg.sb_ninodes sb).
  { pose proof (sbo_ninodes sb (fsimg_wf_sb P sb Hwf)).
    unfold FsImg.ROOTINO in *. lia. }
  pose proof (fsimg_wf_dir P sb FsImg.ROOTINO Hwf Hnin Hty) as Hdok.
  pose proof (img_root_entries P sb Hwf) as Hents.
  destruct (img_root_dir P sb Hwf) as (Hrd & Hrnl & Hro & Hrm).
  (* the root's own ticket list is part of the image's whole supply, AT
     EVERY KEY -- the one arithmetic step both branches of step two use *)
  assert (Hjoin : forall t : Z,
    (fs_tick_count (fs_dir_tickets P FsImg.ROOTINO
                      (fs_dinode P sb FsImg.ROOTINO)) t
     <= fs_link_count P sb t)%nat).
  { intros t. rewrite /fs_link_count /fs_all_tickets.
    apply fs_tick_count_join. apply elem_of_list_fmap.
    exists (Z.to_nat FsImg.ROOTINO). split.
    - rewrite Z2Nat.id; [| unfold FsImg.ROOTINO; lia].
      rewrite /fs_dir_tickets_at. cbv zeta.
      rewrite (proj2 (Z.eqb_eq _ _) Hty) //.
    - apply elem_of_seq. unfold FsImg.ROOTINO in *. lia. }
  (* THE [.] ENTRY, peeled off the map: it names the root itself and, under
     the type register, owes a fragment at the root's own value. *)
  assert (Hdotv : dir_entries (img_node P sb FsImg.ROOTINO) !! DOT
                  = Some FsImg.ROOTINO)
    by (rewrite Hents; exact (fdo_dot P sb FsImg.ROOTINO _ Hdok)).
  assert (Hdotty : lc_tyf (img_f P sb) FsImg.ROOTINO DOT
                   = img_v P sb FsImg.ROOTINO)
    by (rewrite img_f_tyf Hdotv //).
  assert (Hdottl : ent_tokenless FsImg.ROOTINO
                     (fn_orphan (img_node P sb FsImg.ROOTINO)) DOT
                     FsImg.ROOTINO = false).
  { rewrite /ent_tokenless Hro
      (bool_decide_eq_true_2 (DOT = DOT) eq_refl)
      (bool_decide_eq_true_2 (FsImg.ROOTINO = FsImg.ROOTINO) eq_refl) //. }
  rewrite /ent_ops
    (big_opM_delete
       (fun s t => ent_elem FsImg.ROOTINO
                     (fn_orphan (img_node P sb FsImg.ROOTINO)) s t
                     (lc_tyf (img_f P sb) FsImg.ROOTINO s))
       (dir_entries (img_node P sb FsImg.ROOTINO)) DOT FsImg.ROOTINO Hdotv).
  rewrite {1}/ent_elem Hdottl Hdotty.
  (* THE REMAINING ENTRIES are covered by the root's own tickets *)
  assert (Hone : ([^op map] s ↦ t ∈
                    delete DOT (dir_entries (img_node P sb FsImg.ROOTINO)),
                    ent_elem FsImg.ROOTINO
                      (fn_orphan (img_node P sb FsImg.ROOTINO)) s t
                      (lc_tyf (img_f P sb) FsImg.ROOTINO s))
                 ≼ toks_of_list (img_v P sb)
                     (fs_dir_tickets P FsImg.ROOTINO
                        (fs_dinode P sb FsImg.ROOTINO))).
  { rewrite Hents. apply view_ops_incl_tickets.
    intros k Hk Hw Hex Htl.
    assert (Hlv : dir_live (fs_data_of P (fs_dinode P sb FsImg.ROOTINO)) k)
      by exact (dir_wins_live _ k Hw).
    pose proof (dir_view_live (fs_data_of P (fs_dinode P sb FsImg.ROOTINO))
                  (dir_nrec (bv_unsigned
                               (di_size (fs_dinode P sb FsImg.ROOTINO))))
                  k (fdo_unique P sb FsImg.ROOTINO _ Hdok) Hk Hlv) as Hlk.
    rewrite img_f_tyf Hents Hlk //. }
  apply (cmra_included_trans _
           (toks_of_list (img_v P sb)
              (FsImg.ROOTINO :: FsImg.ROOTINO
               :: fs_dir_tickets P FsImg.ROOTINO
                    (fs_dinode P sb FsImg.ROOTINO)))).
  (* STEP ONE: the two spare fragments are the two consed heads *)
  { rewrite !toks_of_list_cons.
    assert (Hsw : forall a b : fsLinkUR, (a ⋅ b) ⋅ a ≡ a ⋅ (a ⋅ b))
      by (intros a b; rewrite (cmra_comm (a ⋅ b) a) //).
    rewrite Hsw. apply cmra_mono; [done |].
    apply cmra_mono; [done | exact Hone]. }
  (* STEP TWO: the counts are covered by the inodes' multiplicities. *)
  apply toks_of_list_incl. intros z Hz.
  rewrite !fs_tick_count_cons in Hz |- *.
  destruct (decide (FsImg.ROOTINO = z)) as [<- | Hzne].
  { (* THE ROOT'S KEY: no ticket at all, and multiplicity two. *)
    rewrite (bool_decide_eq_true_2 (FsImg.ROOTINO = FsImg.ROOTINO) eq_refl).
    exists (img_node P sb FsImg.ROOTINO). split.
    { apply img_nodes_lookup. apply region_inums_spec.
      unfold FsImg.ROOTINO in *. lia. }
    destruct (fsimg_wf_root_link P sb Hwf) as [Hcnt _].
    pose proof (Hjoin FsImg.ROOTINO) as Hj. rewrite Hcnt in Hj.
    rewrite Hrm. lia. }
  rewrite (bool_decide_eq_false_2 (FsImg.ROOTINO = z) Hzne) in Hz |- *.
  pose proof (fs_tick_count_elem _ z Hz) as Hin.
  rewrite /fs_dir_tickets in Hin.
  apply elem_of_list_omap in Hin as (k & Hk & Hkt).
  apply elem_of_seq in Hk as [_ Hk].
  rewrite /fs_rec_ticket in Hkt. cbv zeta in Hkt.
  destruct (dir_liveb (fs_data_of P (fs_dinode P sb FsImg.ROOTINO)) k
            && negb (bool_decide
                       (bv_unsigned
                          (dir_inum
                             (fs_data_of P (fs_dinode P sb FsImg.ROOTINO)) k)
                        = FsImg.ROOTINO))) eqn:Hg; [| discriminate].
  injection Hkt as <-.
  apply andb_true_iff in Hg as [Hlv Hself].
  apply negb_true_iff, bool_decide_eq_false in Hself.
  destruct (fdo_ent P sb FsImg.ROOTINO (fs_dinode P sb FsImg.ROOTINO) Hdok
              k Hk (proj1 (dir_liveb_true _ k) Hlv)) as [Hran Hlive].
  set (t := bv_unsigned
              (dir_inum (fs_data_of P (fs_dinode P sb FsImg.ROOTINO)) k))
    in *.
  assert (Htran : 0 <= t < FsImg.sb_ninodes sb) by lia.
  exists (img_node P sb t). split.
  { apply img_nodes_lookup. apply region_inums_spec. lia. }
  (* not a directory (W9's arm), so conjunct (13) gives its exact count *)
  assert (Hnd : bv_unsigned (di_type (fs_dinode P sb t)) <> T_DIR_z).
  { intros Hc.
    destruct (proj2 (fs_links_wf_at P sb t (fsimg_wf_links P sb Hwf) Htran)
                Hc) as (_ & _ & Hr).
    exact (Hself Hr). }
  pose proof (fs_links_eq_at P sb t Heq Htran Hlive Hnd) as Hnl.
  assert (Hmlt : (fn_nlink (img_node P sb t) <= fn_mult (img_node P sb t))%nat)
    by (rewrite /fn_mult; lia).
  rewrite /fn_nlink img_node_rec Hnl Nat2Z.id in Hmlt.
  pose proof (Hjoin t). lia.
Qed.

(* ---- 9h.   THE FAMILY'S VALIDITY, AS A THEOREM ----------------------- *)

(* the value-side CLAUSE the same choice satisfies: every node's register
   value matches its kind, its marker set is empty (nothing is checked
   out at boot), the ONE directory's count is exact, and every ticketed
   record's value is its target's -- a NAME record's target is never a
   directory, by W9's (T). *)
Lemma img_link_elem_ok (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
  fsimg_wf P sb = true -> fs_region_wf P sb nib = true ->
  link_elem_ok (img_nodes P sb nib) (img_f P sb).
Proof.
  intros Hwf Hrw i n Hi.
  destruct (img_nodes_lookup_inv P sb nib i n Hi) as [Hreg ->].
  pose proof (sbo_ninodes sb (fsimg_wf_sb P sb Hwf)) as Hni.
  assert (Hnin : 0 <= FsImg.ROOTINO < FsImg.sb_ninodes sb)
    by (unfold FsImg.ROOTINO in *; lia).
  (* i is a directory only if it is the root -- W9's (T) *)
  assert (Hdirroot : fn_is_dir (img_node P sb i) = true ->
                     i = FsImg.ROOTINO).
  { intros Hd. apply region_inums_spec in Hreg.
    assert (Hty : bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z)
      by (rewrite -(img_node_rec P sb i); exact (proj1 (bool_decide_eq_true _) Hd)).
    assert (Hran : 0 <= i < FsImg.sb_ninodes sb).
    { split; [lia |].
      destruct (Z_lt_ge_dec i (FsImg.sb_ninodes sb)) as [Hlt | Hge];
        [exact Hlt |].
      exfalso.
      rewrite (fs_region_free_spec P sb nib i (fs_region_wf_free _ _ _ Hrw)
                 ltac:(lia) ltac:(lia) ltac:(lia)) in Hty.
      rewrite /T_DIR_z in Hty. discriminate. }
    destruct (proj2 (fs_links_wf_at P sb i (fsimg_wf_links P sb Hwf) Hran)
                Hty) as (_ & _ & Hroot).
    exact Hroot. }
  rewrite /node_ent_ok img_f_v img_f_D. split_and!.
  - (* the value matches the kind *)
    rewrite /fn_ity_ok /img_v.
    destruct (fn_is_dir (img_node P sb i)); reflexivity.
  - (* nothing is checked out at boot *)
    intros s Hs. exfalso. set_solver.
  - (* the ONE directory's count is exact *)
    intros Hd. pose proof (Hdirroot Hd) as Hri. rewrite Hri.
    destruct (img_root_dir P sb Hwf) as (_ & Hnl & Ho & _).
    rewrite Hnl Ho size_empty //.
  - (* every ticketed record's value is its target's *)
    intros s t Hst Htl.
    match goal with
    | |- ent_ty_ok _ _ ?b _ _ =>
        assert (Hnid : b = false)
          by (apply bool_decide_eq_false; set_solver);
        rewrite Hnid
    end.
    (* only the root has entries *)
    assert (Hroot : i = FsImg.ROOTINO).
    { destruct (decide (fn_is_dir (img_node P sb i) = true)) as [Hd | Hd].
      - exact (Hdirroot Hd).
      - exfalso. apply not_true_is_false in Hd.
        rewrite /dir_entries Hd in Hst. simpl in Hst.
        rewrite lookup_empty in Hst. discriminate. }
    subst i.
    pose proof (fsimg_wf_dir P sb FsImg.ROOTINO Hwf Hnin
                  (fs_root_wf_type P sb (fsimg_wf_root P sb Hwf))) as Hdok.
    pose proof (img_root_entries P sb Hwf) as Hents.
    rewrite /ent_ty_ok img_f_tyf Hst.
    destruct (bool_decide (s = DOT)) eqn:Hsdot.
    { (* the [.] record: its value is the root's own, and the root's [..]
         names the root, so the pinned parent agrees *)
      apply bool_decide_eq_true in Hsdot. subst s.
      assert (Ht : t = FsImg.ROOTINO).
      { rewrite Hents in Hst.
        rewrite (fdo_dot P sb FsImg.ROOTINO _ Hdok) in Hst.
        by injection Hst. }
      subst t. intros p q Hp Hq.
      destruct (img_root_dir P sb Hwf) as (Hrd & _ & _ & _).
      rewrite /img_v Hrd in Hp. injection Hp as <-.
      rewrite /fn_dd Hents (fs_root_wf_dotdot P sb
                              (fsimg_wf_root P sb Hwf)) in Hq.
      by injection Hq. }
    destruct (bool_decide (s = DOTDOT)) eqn:Hsdd; [exact I |].
    (* a NAME record: its target is not a directory *)
    assert (Hsne : s <> DOT) by exact (proj1 (bool_decide_eq_false _) Hsdot).
    assert (Htne : t <> FsImg.ROOTINO).
    { intros Hc. rewrite /ent_tokenless Hc in Htl.
      rewrite (bool_decide_eq_true_2 (FsImg.ROOTINO = FsImg.ROOTINO) eq_refl)
        (bool_decide_eq_false_2 (s = DOT) Hsne) in Htl.
      destruct (bool_decide (s = DOTDOT)),
               (fn_orphan (img_node P sb FsImg.ROOTINO));
        simpl in Htl; discriminate. }
    (* the record is live and inside the region *)
    rewrite Hents in Hst.
    apply dir_view_lookup_Some in Hst as (k & Hk & Hkt).
    apply dir_first_Some in Hk as (Hklt & [Hlv _] & _).
    destruct (fdo_ent P sb FsImg.ROOTINO (fs_dinode P sb FsImg.ROOTINO) Hdok
                k Hklt Hlv) as [Hran _].
    rewrite Hkt in Hran.
    assert (Hnd : bv_unsigned (di_type (fs_dinode P sb t)) <> T_DIR_z).
    { intros Hc.
      destruct (proj2 (fs_links_wf_at P sb t (fsimg_wf_links P sb Hwf)
                         ltac:(lia)) Hc) as (_ & _ & Hr).
      exact (Htne Hr). }
    assert (Hnotd : fn_is_dir (img_node P sb t) = false).
    { rewrite /fn_is_dir. apply bool_decide_eq_false.
      rewrite /fn_type img_node_rec. exact Hnd. }
    rewrite /img_v Hnotd //.
Qed.

Lemma img_link_valid (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
  fsimg_wf P sb = true -> fs_region_wf P sb nib = true ->
  fs_links_eq P sb = true -> fs_root_no_self P sb = true ->
  FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
  ✓ (link_elem (img_nodes P sb nib) (img_f P sb)
     ⋅ link_tok_elem FsImg.ROOTINO (img_v P sb FsImg.ROOTINO)).
Proof.
  intros Hwf Hrw Heq Hns Hnin.
  pose proof (sbo_ninodes sb (fsimg_wf_sb P sb Hwf)) as Hni.
  unfold FsImg.ROOTINO in Hni.
  assert (Hrootin : FsImg.ROOTINO ∈ region_inums nib)
    by (apply region_inums_spec; rewrite /FsImg.ROOTINO; lia).
  apply (link_elem_valid_of_root _ (img_f P sb) FsImg.ROOTINO
           (img_node P sb FsImg.ROOTINO) _
           (img_nodes_lookup P sb nib FsImg.ROOTINO Hrootin));
    [| exact (img_link_incl P sb nib Hwf Heq Hns Hnin)].
  intros i n Hi Hne.
  destruct (img_nodes_lookup_inv P sb nib i n Hi) as [Hin ->].
  exact (img_dir_entries_empty P sb nib i Hwf Hrw Hin Hne).
Qed.

(* ===================================================================== *)
(*  SECTION 10 IS GONE (durable-disk lane CE).  It built the durable      *)
(*  instance by MOVING the boot's byte elements into it                   *)
(*  ([fs_dur_of_image] / [fs_dur_view_of_image]).  Under the SNAPSHOT      *)
(*  ruling nothing is moved: [FsDurSnap.P_dur_alloc] builds the instance   *)
(*  from the PURE tie alone, and the boot mint plan section 5 wants runs   *)
(*  the same core at the ERA's own view ([fs_state_of_ledger_era]), not    *)
(*  through an image conversion.  Section 11 below is the whole image      *)
(*  side.                                                                 *)
(* ===================================================================== *)

(* ===================================================================== *)
(* 11.  THE IMAGE'S SNAPSHOT TIE: [FsDurSnap.snap_ok] AT THE IMAGE        *)
(*      (durable-disk lane C, image half; plan sections 2, 4a, 5)         *)
(*                                                                        *)
(*  WHAT THIS SECTION REPLACES.  Sections 3-7 and 10 build the durable    *)
(*  instance by MOVING the boot's byte elements into it, and the flip's   *)
(*  pure KIND ASSIGNMENT ([img_kinds*], [img_dur_seed]) used to ride      *)
(*  beside them.  Under the SNAPSHOT ruling (plan section 2) nothing is   *)
(*  moved and nothing is ever updated: [FsDurSnap.P_dur D] is allocated   *)
(*  from NOTHING but the pure tie [FsDurSnap.snap_ok S D], so the whole   *)
(*  image side of the boot is ONE pure theorem -- [img_snap_ok] -- plus   *)
(*  [FsDurSnap.P_dur_alloc].  The kind assignment and its seed were the   *)
(*  rejected pure-kinds tie (plan section 6, section 8's third bullet)    *)
(*  and are DELETED with this lane; nothing consumed them.                *)
(*                                                                        *)
(*  THE STATE AND THE MAP.  [S] is [img_state] (section 8) -- the SAME    *)
(*  decoder sections 8/10 read the image with, so no second decoder       *)
(*  exists -- and [D] is the clean image's committed home map             *)
(*  [fs_restrict (fs_blocks dk) (fs_home_set cov logstart)], which is     *)
(*  exactly the [fr_D] of the record [FsCrash.P_fs_alloc] mints at a      *)
(*  clean log.                                                            *)
(*                                                                        *)
(*  WHERE EACH CLAUSE COMES FROM.  The three byte ties are the PURE       *)
(*  halves of what sections 5/6 do with resources: the record from        *)
(*  [IcacheBoot.diblk_bytes_surj] + [FsImg.fs_dinode_of_diblk] (11a), the *)
(*  data blocks from [FsImg.fs_data_of_addr] and the indirect block from  *)
(*  [FsImg.fs_ind_bytes_round_trip] (11b).  THE USED-SET COUPLING -- the  *)
(*  one whole-map clause the plan sanctions (section 4a) -- is W3/W4/W5:  *)
(*  a node's own block is a [FsImg.fs_slot] of its record (11b), hence a  *)
(*  member of [FsImg.fs_inode_blocks] (W3's range bound), hence marked in *)
(*  use (W5) and above [fs_data_start] and so no metadata block; and two  *)
(*  nodes cannot share one because W4 says [fs_used_blocks] has no        *)
(*  duplicate.  A FREE inum owns no block at all -- that is conjunct      *)
(*  (14)'s ([FsImg.fs_region_bare]) second use, beside [inode_local].     *)
(*  [sk_links] is section 9h's [img_link_valid] and [snap_local] is       *)
(*  section 2's [img_inode_local]; both were already proved.              *)
(* ===================================================================== *)

(* ---- 11a.  A RECORD SITS AT ITS SLOT, PURELY ------------------------- *)

(*  [DinodeEnc.diblk_bytes] SPLIT at one slot -- the shape
    [FsDurSnap.rec_in_blk] is stated in, and the pure content of
    [FsStateInode.rec_owned_at_diblk].  FOR RELOCATION: it belongs beside
    [DinodeEnc.diblk_bytes_lookup]; it is here because an additive change
    to a file that low rebuilds its whole cone on every iteration
    (durable-notes.md).                                                    *)
Lemma diblk_bytes_split (ds : list dinode) (k : nat) :
  Forall dinode_wf ds -> (k < length ds)%nat ->
  exists pre post,
    diblk_bytes ds = (pre ++ dinode_bytes (ds !!! k) ++ post)%list
    /\ length pre = (64 * k)%nat.
Proof.
  revert k. induction ds as [| d ds IH]; intros k Hall Hk;
    [simpl in Hk; lia |].
  apply Forall_cons in Hall as [Hd Hall].
  destruct k as [| k].
  - exists [], (diblk_bytes ds).
    rewrite diblk_bytes_cons. split; reflexivity.
  - simpl in Hk.
    destruct (IH k Hall ltac:(lia)) as (pre & post & Heq & Hlen).
    exists (dinode_bytes d ++ pre)%list, post.
    assert (Hs : (d :: ds) !!! S k = ds !!! k) by reflexivity.
    (* NEITHER [rewrite length_app] NOR [rewrite app_assoc] MAY BE LEFT TO
       FIND ITS OWN MATCH HERE.  This file's [rewrite] is ssreflect's, and
       its keyed matching unfolds [dinode_bytes] to reach an EARLIER
       [_ ++ _] inside the record's own encoding -- so both rules fire in
       the wrong place and leave a goal that no longer mentions
       [dinode_bytes d] at all (durable-notes.md, "rewrite can fail on a
       subterm that prints character-for-character").  Both are applied at
       spelled-out arguments instead, and the length side is arithmetic. *)
    assert (Hla : length ((dinode_bytes d ++ pre)%list)
                  = (length (dinode_bytes d) + length pre)%nat)
      by apply length_app.
    pose proof (dinode_bytes_length d Hd) as H64.
    split; [| lia].
    rewrite Hs diblk_bytes_cons Heq.
    first [ exact (app_assoc (dinode_bytes d) pre
                     (dinode_bytes (ds !!! k) ++ post)%list)
          | exact (eq_sym (app_assoc (dinode_bytes d) pre
                     (dinode_bytes (ds !!! k) ++ post)%list)) ].
Qed.

(*  ...and the image's own record at its own slot.  [FsImg.fs_dinode] is
    the DECODER; this says the encoder's image of what it decodes sits in
    the block where [FsDurSnap.sk_rec] asks for it.  No image
    well-formedness is needed -- only that a block is a block.            *)
Lemma img_rec_in_blk (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_blocks_full P -> 0 <= i < 2 ^ 32 ->
  rec_in_blk (P (FsImg.sb_inodestart sb + i `div` 16))
             (64 * (i `mod` 16)) (fs_dinode P sb i).
Proof.
  intros Hfull Hi.
  assert (H32 : bv_modulus 32 = (2 ^ 32)%Z) by (vm_compute; reflexivity).
  assert (Hbv : bv_unsigned (fs_inum_bv i) = i).
  { rewrite /fs_inum_bv. apply Z_to_bv_small. rewrite H32. lia. }
  assert (Hblk : IBLOCK (fs_inum_bv i) (FsImg.sb_inodestart sb)
                 = FsImg.sb_inodestart sb + i `div` 16)
    by (rewrite /IBLOCK Hbv; lia).
  destruct (diblk_bytes_surj (P (FsImg.sb_inodestart sb + i `div` 16))
              (Hfull _)) as (ds & Hdwf & Hde).
  pose proof Hdwf as [Hlen16 Hall].
  pose proof (islot_lt (fs_inum_bv i)) as Hlt16.
  assert (Hks : (islot (fs_inum_bv i) < length ds)%nat) by lia.
  assert (Hrec : fs_dinode P sb i = ds !!! islot (fs_inum_bv i)).
  { apply (fs_dinode_of_diblk P sb i ds Hdwf). rewrite Hblk. exact Hde. }
  destruct (diblk_bytes_split ds (islot (fs_inum_bv i)) Hall Hks)
    as (pre & post & Heq & Hlp).
  rewrite /rec_in_blk. exists pre, post. split.
  - rewrite Hde Heq Hrec. reflexivity.
  - rewrite Hlp /islot Hbv.
    pose proof (Z.mod_pos_bound i 16 ltac:(lia)) as [Hm0 Hm1]. lia.
Qed.

(* ---- 11b.  A NODE'S OWN BLOCK IS A SLOT OF ITS RECORD ---------------- *)

(*  [FsDurSnap.fn_owns] names a node's data blocks and its indirect block;
    [FsImg.fs_slot] names the same thirteen-plus-256 addresses on the
    image side.  This is the one translation, and it is what turns the
    used-set coupling into W3/W4/W5.                                      *)
Lemma img_node_owns_slot (P : Z -> list (bv 8)) (sb : fs_sb) (z b : Z) :
  fn_owns (img_node P sb z) b ->
  exists k : nat, (k <= FS_MAXFILE)%nat
               /\ fs_slot P (fs_dinode P sb z) k = b /\ b <> 0.
Proof.
  intros Hown.
  pose proof (fs_dinode_wf P sb z) as Hwf.
  assert (Hsl : forall j : nat, (j < FS_MAXFILE)%nat ->
            fs_slot P (fs_dinode P sb z) j
            = fs_blk_addr P (fs_dinode P sb z) j).
  { intros j Hj. rewrite /fs_slot.
    destruct (decide (j = FS_MAXFILE)) as [-> | _]; [lia | reflexivity]. }
  destruct Hown as [(k & Hk & Hnad) | [Hnz Heq]].
  - rewrite /img_node era_node_blk node_blk_lookup in Hk.
    destruct (decide ((k < MAXFILE)%nat
                /\ bv_unsigned
                     (blkmap_get (img_blkmap P (fs_dinode P sb z)) k) <> 0))
      as [[Hklt Hbnz] | _]; [| destruct Hk as (? & Hc); discriminate Hc].
    assert (Hkf : (k < FS_MAXFILE)%nat)
      by (unfold MAXFILE, FS_MAXFILE in *; lia).
    exists k. split; [lia |].
    rewrite (Hsl k Hkf).
    rewrite (img_blkmap_get P (fs_dinode P sb z) k Hwf Hklt) in Hbnz.
    rewrite /img_node
      (era_node_naddr (fs_dinode P sb z) (img_blkmap P (fs_dinode P sb z))
         (fs_data_of P (fs_dinode P sb z)) k
         (eq_sym (img_blkmap_cells P (fs_dinode P sb z) Hwf))
         (img_blkmap_dirlen P (fs_dinode P sb z) Hwf) Hklt)
      (img_blkmap_get P (fs_dinode P sb z) k Hwf Hklt) in Hnad.
    split; [exact Hnad | rewrite -Hnad; exact Hbnz].
  - exists FS_MAXFILE. split; [lia |].
    rewrite fs_slot_max.
    assert (Hind : fn_indb (img_node P sb z)
                   = bv_unsigned (di_addrs (fs_dinode P sb z) !!! 12%nat))
      by reflexivity.
    rewrite Hind in Hnz, Heq.
    split; [exact Heq | rewrite -Heq; exact Hnz].
Qed.

(*  ...and the SAME reading pointwise, which is what [FsDurSnap.sk_slot]
    is stated over: the node's slot [k] IS the record's [FsImg.fs_slot k],
    the indirect block included.                                          *)
Lemma img_node_fn_naddr (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z)
    (k : nat) :
  (k < FS_MAXFILE)%nat ->
  fn_naddr (img_node P sb z) k = fs_blk_addr P (fs_dinode P sb z) k.
Proof.
  intros Hk.
  pose proof (fs_dinode_wf P sb z) as Hwf.
  assert (Hklt : (k < MAXFILE)%nat)
    by (unfold MAXFILE, FS_MAXFILE in *; lia).
  rewrite /img_node
    (era_node_naddr (fs_dinode P sb z) (img_blkmap P (fs_dinode P sb z))
       (fs_data_of P (fs_dinode P sb z)) k
       (eq_sym (img_blkmap_cells P (fs_dinode P sb z) Hwf))
       (img_blkmap_dirlen P (fs_dinode P sb z) Hwf) Hklt)
    (img_blkmap_get P (fs_dinode P sb z) k Hwf Hklt) //.
Qed.

Lemma img_node_fn_slot (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) (k : nat) :
  (k <= FS_MAXFILE)%nat ->
  fn_slot (img_node P sb z) k = fs_slot P (fs_dinode P sb z) k.
Proof.
  intros Hk. rewrite /fn_slot /fs_slot.
  destruct (decide (k = FS_MAXFILE)) as [-> | Hne];
    [reflexivity | apply img_node_fn_naddr; lia].
Qed.

(* W4 at one inum, in the node vocabulary *)
Lemma img_node_slot_inj (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fs_slot_inj P (fs_dinode P sb z) -> fn_slot_inj (img_node P sb z).
Proof.
  intros Hinj k j Hk Hj Hnz Heq. apply (Hinj k j Hk Hj).
  - rewrite -(img_node_fn_slot P sb z k Hk). exact Hnz.
  - rewrite -(img_node_fn_slot P sb z k Hk) -(img_node_fn_slot P sb z j Hj).
    exact Heq.
Qed.

(*  ...and the bytes at a HELD slot are the block's own, which is
    [FsDurSnap.sk_blk] with the map's lookup removed.                     *)
Lemma img_node_blk_at (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z)
    (k : nat) (bs : list (bv 8)) :
  fn_blk (img_node P sb z) !! k = Some bs ->
  bs = P (fn_naddr (img_node P sb z) k)
  /\ fn_owns (img_node P sb z) (fn_naddr (img_node P sb z) k).
Proof.
  intros Hk.
  pose proof (fs_dinode_wf P sb z) as Hwf.
  split; [| left; exists k; split; [by exists bs | reflexivity]].
  assert (Hb := Hk).
  rewrite /img_node era_node_blk node_blk_lookup in Hb.
  destruct (decide ((k < MAXFILE)%nat
              /\ bv_unsigned
                   (blkmap_get (img_blkmap P (fs_dinode P sb z)) k) <> 0))
    as [[Hklt Hbnz] | _]; [| discriminate Hb].
  apply (inj Some) in Hb. subst bs.
  assert (Hna : fn_naddr (img_node P sb z) k
                = fs_blk_addr P (fs_dinode P sb z) k).
  { rewrite /img_node
      (era_node_naddr (fs_dinode P sb z) (img_blkmap P (fs_dinode P sb z))
         (fs_data_of P (fs_dinode P sb z)) k
         (eq_sym (img_blkmap_cells P (fs_dinode P sb z) Hwf))
         (img_blkmap_dirlen P (fs_dinode P sb z) Hwf) Hklt).
    exact (img_blkmap_get P (fs_dinode P sb z) k Hwf Hklt). }
  rewrite (img_blkmap_get P (fs_dinode P sb z) k Hwf Hklt) in Hbnz.
  rewrite Hna fs_data_of_addr (proj2 (Z.eqb_neq _ _) Hbnz). reflexivity.
Qed.

(*  the same for the INDIRECT block: its bytes are [BlockWords.ind_bytes]
    of the node's entry array, which is [FsImg.fs_ind_bytes_round_trip]    *)
Lemma img_node_ind_at (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fs_blocks_full P -> fn_indb (img_node P sb z) <> 0 ->
  P (fn_indb (img_node P sb z)) = ind_bytes (fn_ent (img_node P sb z))
  /\ fn_owns (img_node P sb z) (fn_indb (img_node P sb z)).
Proof.
  intros Hfull Hnz.
  split; [| right; split; [exact Hnz | reflexivity]].
  assert (Hind : fn_indb (img_node P sb z)
                 = bv_unsigned (di_addrs (fs_dinode P sb z) !!! 12%nat))
    by reflexivity.
  assert (Hent : fn_ent (img_node P sb z)
                 = (fun q => Z_to_bv 32 q)
                     <$> fs_ind_ents P (fs_dinode P sb z))
    by reflexivity.
  rewrite Hind Hent. symmetry.
  apply (fs_ind_bytes_round_trip P (fs_dinode P sb z) Hfull).
  rewrite -Hind. exact Hnz.
Qed.

(* ---- 11c.  ...AND THAT BLOCK IS IN USE, ABOVE ALL METADATA ----------- *)

Lemma img_owned_block (P : Z -> list (bv 8)) (sb : fs_sb) (z b : Z) :
  fsimg_wf P sb = true ->
  0 <= z < FsImg.sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
  fn_owns (img_node P sb z) b ->
  b ∈ fs_inode_blocks P (fs_dinode P sb z)
  /\ fs_data_start sb <= b < FsImg.sb_size sb.
Proof.
  intros Hwf Hran Hty Hown.
  pose proof (fsimg_wf_inode P sb z Hwf Hran Hty) as Hok.
  destruct (img_node_owns_slot P sb z b Hown) as (k & Hk & Hsl & Hnz).
  assert (Hsnz : fs_slot P (fs_dinode P sb z) k <> 0)
    by (rewrite Hsl; exact Hnz).
  pose proof (fs_inode_blocks_lookup P sb (fs_dinode P sb z) k Hok Hk Hsnz)
    as Hlk.
  rewrite Hsl in Hlk.
  pose proof (elem_of_list_lookup_2 _ _ _ Hlk) as Hin.
  split; [exact Hin | exact (fs_inode_blocks_range P sb _ b Hok Hin)].
Qed.

(*  W5 read FORWARD: a block below [size] that is either metadata or in
    the used set has its BIT SET, hence lies in the block's own bit set --
    which is [img_state]'s [fss_used].                                    *)
Lemma img_used_of_blocks (P : Z -> list (bv 8)) (sb : fs_sb) (b : Z) :
  fsimg_wf P sb = true -> 0 <= b < FsImg.sb_size sb ->
  (b < fs_data_start sb \/ b ∈ fs_used_blocks P sb) ->
  b ∈ FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb)).
Proof.
  intros Hwf Hb Hor.
  pose proof (fsimg_wf_sb P sb Hwf) as Hsb.
  pose proof (sbo_one_bitmap sb Hsb) as Hone.
  destruct (fsimg_wf_used P sb Hwf) as (u & Hus & _ & Hbw).
  apply fs_bmap_set_elem.
  split; [rewrite BSIZE_z_nat; lia |].
  apply (proj2 (fs_bitmap_wf_spec P sb u b Hbw Hb)).
  destruct Hor as [Hlt | Hin]; [by left |].
  right. exact (proj2 (fs_used_set_elem P sb u b Hus) Hin).
Qed.

(* ---- 11c'. THE THREE DIRECTORY CLAUSES AT AN IMAGE NODE
       (durable-disk lane E-clauses) --------------------------------------

    [FsDurSnap.sk_dirloc] is what a boot mint needs to re-found
    [IcacheEscrow.ipool_alloc]'s three [DirView] premises.  At the image
    all three are W6/W7/W8 read through [FsImgBridge], exactly as
    [FsCfgBoot.img_inode_local_live] reads [dir_uniq] and [dir_dots_ix] --
    nothing is recomputed here.  The free arm is vacuous: a type-0 record
    is no directory.                                                       *)
Lemma img_node_dir_local (P : Z -> list (bv 8)) (sb : fs_sb) (cov : gset Z)
    (nib : nat) (z : Z) :
  fsimg_wf P sb = true -> fs_region_wf P sb nib = true ->
  fs_blocks_full P ->
  FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
  (forall b : Z, fs_data_start sb <= b < FsImg.sb_size sb -> b ∈ cov) ->
  z ∈ region_inums nib ->
  node_dir_local z nib (img_node P sb z).
Proof.
  intros Hwf Hrw Hfull Hnin Hcov Hz.
  apply region_inums_spec in Hz.
  destruct (decide (bv_unsigned (di_type (fs_dinode P sb z)) = 0))
    as [H0 | Hnz].
  - apply node_dir_local_free. rewrite /img_node era_node_rec. exact H0.
  - assert (Hran : 0 <= z < FsImg.sb_ninodes sb).
    { split; [lia |].
      destruct (Z_lt_ge_dec z (FsImg.sb_ninodes sb)) as [Hlt | Hge];
        [exact Hlt |].
      exfalso. apply Hnz.
      exact (fs_region_free_spec P sb nib z (fs_region_wf_free _ _ _ Hrw)
               ltac:(lia) ltac:(lia) ltac:(lia)). }
    assert (Hdir : bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z ->
                   fs_dir_ok P sb z (fs_dinode P sb z))
      by (intros Hd; exact (fsimg_wf_dir P sb z Hwf Hran Hd)).
    rewrite /img_node.
    apply (FsStateEra.node_dir_local_of_ok z cov (FsImg.sb_logstart sb) nib
             (fs_dinode P sb z) (img_blkmap P (fs_dinode P sb z))
             (fs_data_of P (fs_dinode P sb z))
             (img_inode_ok_at P sb cov z Hwf Hfull Hcov Hran Hnz)).
    + exact (img_dir_ok P sb z (fs_dinode P sb z) nib Hnin Hdir).
    + intros Hd Hnl0. exact (fsimg_wf_dots P sb z Hwf Hran Hd Hd Hnl0).
    + exact (img_dir_orphan_clean P sb (fs_dinode P sb z)
               (fsimg_wf_inode P sb z Hwf Hran Hnz)).
Qed.

(* ---- 11d.  THE THEOREM ----------------------------------------------- *)

(*  THE IMAGE'S SNAPSHOT TIE.  Every premise is a conjunct of
    [FsCfgBoot.fs_boot_image_wf] -- (14)/(15) among them since this lane --
    so no consumer carries anything new, and the literal-image discharge
    stays in [FsImgCheck]/[SystemAdequacy] (ruling R3: this file computes
    nothing).  Non-vacuity at the real image:
    [SystemAdequacy.fsimg_snap_ok].                                        *)
Theorem img_snap_ok (dk : Z -> bv 8) (ndisk : nat) (sb : fs_sb) (nib : nat)
    (cov : gset Z) :
  fs_boot_image_wf dk ndisk sb nib cov ->
  snap_ok (img_state (fs_blocks dk) sb nib)
          (fs_restrict (fs_blocks dk)
             (fs_home_set cov (FsImg.sb_logstart sb))).
Proof.
  intros (Hwf & Hrw & Hnin & Hnib32 & Hnibpos & Hnibq & Hcovin & Hcovmeta
          & Hcovdata & Hparse & Hnib16 & Hndisk & Hlinkeq & Hbare & Hns).
  (* ---- the geometry, off [fs_sb_ok] alone --------------------------- *)
  pose proof (fsimg_wf_sb _ _ Hwf) as Hsb.
  pose proof (fs_sb_ok_meta sb Hsb) as (Hi2 & Hids & Hdss).
  pose proof (sbo_logstart sb Hsb) as Hls.
  pose proof (sbo_nlog sb Hsb) as Hnl.
  pose proof (sbo_inodestart sb Hsb) as Hist.
  pose proof (sbo_bmapstart sb Hsb) as Hbms.
  pose proof (sbo_ninodes sb Hsb) as Hni. unfold FsImg.ROOTINO in Hni.
  assert (Hdiv0 : 0 <= FsImg.sb_ninodes sb / 16) by (apply Z.div_pos; lia).
  assert (Hfull : fs_blocks_full (fs_blocks dk))
    by (intros c; apply fs_blocks_length).
  destruct (fsimg_wf_used (fs_blocks dk) sb Hwf) as (u & Hus & Hnd & Hbw).
  (* ---- the home set: which blocks are in it ------------------------- *)
  assert (HlogI : forall b : Z,
            b ∈ log_region_set (FsImg.sb_logstart sb) ->
            1 < b < FsImg.sb_inodestart sb).
  { intros b Hb.
    pose proof (log_region_bound (FsImg.sb_logstart sb) b Hb).
    unfold LOGBLOCKS in *. lia. }
  assert (Hhome1 : (1 : Z) ∈ fs_home_set cov (FsImg.sb_logstart sb)).
  { rewrite /fs_home_set. apply elem_of_difference. split.
    - apply Hcovmeta. unfold fs_data_start in *. lia.
    - intros Hc. pose proof (HlogI 1 Hc). lia. }
  assert (Hhome_reg : forall b : Z,
            FsImg.sb_inodestart sb <= b < fs_data_start sb ->
            b ∈ fs_home_set cov (FsImg.sb_logstart sb)).
  { intros b Hb. rewrite /fs_home_set. apply elem_of_difference. split.
    - apply Hcovmeta. lia.
    - intros Hc. pose proof (HlogI b Hc). lia. }
  assert (Hhome_data : forall b : Z,
            fs_data_start sb <= b < FsImg.sb_size sb ->
            b ∈ fs_home_set cov (FsImg.sb_logstart sb)).
  { intros b Hb. rewrite /fs_home_set. apply elem_of_difference. split.
    - apply Hcovdata. lia.
    - intros Hc. pose proof (HlogI b Hc). unfold fs_data_start in *. lia. }
  (* ---- the state's four fields, as equations ------------------------ *)
  assert (Hpsb : fss_sb (img_state (fs_blocks dk) sb nib) = sb)
    by reflexivity.
  assert (Hpsbb : fss_sbb (img_state (fs_blocks dk) sb nib)
                  = fs_blocks dk SB_BNO) by reflexivity.
  assert (Hpin : fss_inodes (img_state (fs_blocks dk) sb nib)
                 = img_nodes (fs_blocks dk) sb nib) by reflexivity.
  assert (Hpu : fss_used (img_state (fs_blocks dk) sb nib)
                = FsImg.fs_bmap_set BSIZE
                    (fs_blocks dk (FsImg.sb_bmapstart sb))) by reflexivity.
  (* ---- ONLY A LIVE INUM OWNS A BLOCK -- conjunct (14)'s second use --- *)
  assert (Hlive_of_owns : forall (i b : Z),
            i ∈ region_inums nib ->
            fn_owns (img_node (fs_blocks dk) sb i) b ->
            0 <= i < FsImg.sb_ninodes sb
            /\ bv_unsigned (di_type (fs_dinode (fs_blocks dk) sb i)) <> 0).
  { intros i b Hreg Hown.
    pose proof (proj1 (region_inums_spec nib i) Hreg) as Hri.
    destruct (decide
                (bv_unsigned (di_type (fs_dinode (fs_blocks dk) sb i)) = 0))
      as [H0 | Hnz].
    - exfalso.
      pose proof (img_node_bare (fs_blocks dk) sb nib i Hbare
                    (fs_region_wf_nlink _ _ _ Hrw) Hri H0) as Hb.
      pose proof Hb as (_ & _ & Hblk0 & _ & _).
      destruct Hown as [(k & Hk & _) | [Hnzi _]].
      + rewrite Hblk0 lookup_empty in Hk.
        destruct Hk as (? & Hc). discriminate Hc.
      + exact (Hnzi (fn_bare_indb _ Hb)).
    - split; [| exact Hnz]. split; [lia |].
      destruct (Z_lt_ge_dec i (FsImg.sb_ninodes sb)) as [Hlt | Hge];
        [exact Hlt |].
      exfalso. apply Hnz.
      exact (fs_region_free_spec (fs_blocks dk) sb nib i
               (fs_region_wf_free _ _ _ Hrw)
               ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* ---- an owned block: in the home set, in the used list, in range --- *)
  assert (Hownhome : forall (i b : Z),
            0 <= i < FsImg.sb_ninodes sb ->
            bv_unsigned (di_type (fs_dinode (fs_blocks dk) sb i)) <> 0 ->
            fn_owns (img_node (fs_blocks dk) sb i) b ->
            b ∈ fs_home_set cov (FsImg.sb_logstart sb)
            /\ b ∈ fs_used_blocks (fs_blocks dk) sb
            /\ fs_data_start sb <= b < FsImg.sb_size sb).
  { intros i b Hran Hty Hown.
    destruct (img_owned_block (fs_blocks dk) sb i b Hwf Hran Hty Hown)
      as [Hin Hrng].
    split; [apply Hhome_data; lia |].
    split; [| exact Hrng].
    exact (fs_used_blocks_inode (fs_blocks dk) sb i b Hran Hty Hin). }
  (* ---- every metadata block sits below the data region --------------- *)
  assert (Hmeta_below : forall b : Z,
            snap_meta (img_state (fs_blocks dk) sb nib) b ->
            1 <= b < fs_data_start sb).
  { intros b Hm. rewrite /snap_meta Hpsb Hpin in Hm.
    destruct Hm as [-> | [-> | (i & Hi & ->)]].
    - unfold SB_BNO, fs_data_start in *. lia.
    - unfold fs_data_start in *. lia.
    - destruct Hi as [n Hn].
      destruct (img_nodes_lookup_inv (fs_blocks dk) sb nib i n Hn)
        as [Hreg _].
      apply region_inums_spec in Hreg.
      assert (Hd : 0 <= i `div` 16 < Z.of_nat nib).
      { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
      unfold fs_data_start in *. lia. }
  (* ---- the LOCAL half, off section 2 --------------------------------- *)
  assert (Hloc : snap_local (img_state (fs_blocks dk) sb nib)).
  { intros i n Hi. rewrite Hpin in Hi.
    destruct (img_nodes_lookup_inv (fs_blocks dk) sb nib i n Hi)
      as [Hreg ->].
    exact (img_inode_local (fs_blocks dk) sb cov nib i Hwf Hrw Hbare Hfull
             Hnin Hcovdata Hreg). }
  (* =================================================================== *)
  apply snap_ok_intro; [| exact Hloc].
  split.
  - (* sk_bsz *)
    intros b bs Hb. apply fs_restrict_lookup_Some in Hb as [_ ->].
    apply fs_blocks_length.
  - (* sk_sb *)
    rewrite Hpsbb. apply fs_restrict_lookup_Some.
    split; [exact Hhome1 | reflexivity].
  - (* sk_parse *)
    rewrite Hpsbb Hpsb. exact Hparse.
  - (* sk_bmap *)
    rewrite Hpsb Hpu (bm_bytes_fs_bmap_set BSIZE _ (Hfull _)).
    apply fs_restrict_lookup_Some. split; [| reflexivity].
    apply Hhome_reg. unfold fs_data_start in *. lia.
  - (* sk_pool *)
    rewrite Hpsb Hpu. intros b Hb Hnu.
    destruct (fs_bmap_set_free (fs_blocks dk) sb u b Hsb Hbw Hb Hnu)
      as [Hge _].
    exists (fs_blocks dk b). apply fs_restrict_lookup_Some.
    split; [apply Hhome_data; lia | reflexivity].
  - (* sk_inum *)
    rewrite Hpin. intros i n Hi.
    destruct (img_nodes_lookup_inv (fs_blocks dk) sb nib i n Hi) as [Hreg _].
    apply region_inums_spec in Hreg. lia.
  - (* sk_repr *)
    intros i n Hi. exact (inode_repr_of_local i n (Hloc i n Hi)).
  - (* sk_rec *)
    rewrite Hpsb Hpin. intros i n Hi.
    destruct (img_nodes_lookup_inv (fs_blocks dk) sb nib i n Hi)
      as [Hreg ->].
    apply region_inums_spec in Hreg.
    assert (Hd : 0 <= i `div` 16 < Z.of_nat nib).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    exists (fs_blocks dk (FsImg.sb_inodestart sb + i `div` 16)). split.
    + apply fs_restrict_lookup_Some. split; [| reflexivity].
      apply Hhome_reg. unfold fs_data_start in *. lia.
    + rewrite (img_node_rec (fs_blocks dk) sb i).
      apply (img_rec_in_blk (fs_blocks dk) sb i Hfull). lia.
  - (* sk_blk *)
    rewrite Hpin. intros i n k bs Hi Hk.
    destruct (img_nodes_lookup_inv (fs_blocks dk) sb nib i n Hi)
      as [Hreg ->].
    destruct (img_node_blk_at (fs_blocks dk) sb i k bs Hk) as [-> Hown].
    destruct (Hlive_of_owns i _ Hreg Hown) as [Hran Hty].
    destruct (Hownhome i _ Hran Hty Hown) as (Hh & _ & _).
    apply fs_restrict_lookup_Some. split; [exact Hh | reflexivity].
  - (* sk_ind *)
    rewrite Hpin. intros i n Hi Hnz.
    destruct (img_nodes_lookup_inv (fs_blocks dk) sb nib i n Hi)
      as [Hreg ->].
    destruct (img_node_ind_at (fs_blocks dk) sb i Hfull Hnz) as [Heq Hown].
    destruct (Hlive_of_owns i _ Hreg Hown) as [Hran Hty].
    destruct (Hownhome i _ Hran Hty Hown) as (Hh & _ & _).
    apply fs_restrict_lookup_Some.
    split; [exact Hh | symmetry; exact Heq].
  - (* sk_dom *)
    rewrite Hpsb Hpin. intros i Hi.
    exists (img_node (fs_blocks dk) sb i).
    apply img_nodes_lookup, region_inums_spec. lia.
  - (* sk_links *)
    rewrite Hpin. exists (img_f (fs_blocks dk) sb),
      (img_v (fs_blocks dk) sb FsImg.ROOTINO). split.
    + exact (img_link_elem_ok (fs_blocks dk) sb nib Hwf Hrw).
    + exact (img_link_valid (fs_blocks dk) sb nib Hwf Hrw Hlinkeq Hns Hnin).
  - (* sk_meta_used -- the metadata roles are MARKED IN USE *)
    rewrite Hpu. intros b Hm.
    pose proof (Hmeta_below b Hm) as Hbr.
    apply (img_used_of_blocks (fs_blocks dk) sb b Hwf); [lia | left; lia].
  - (* sk_own_used -- a node's own blocks are used, and are not metadata *)
    rewrite Hpin Hpu. intros i n b Hi Hown.
    destruct (img_nodes_lookup_inv (fs_blocks dk) sb nib i n Hi)
      as [Hreg ->].
    destruct (Hlive_of_owns i b Hreg Hown) as [Hran Hty].
    destruct (Hownhome i b Hran Hty Hown) as (_ & Hub & Hrng).
    split.
    + apply (img_used_of_blocks (fs_blocks dk) sb b Hwf);
        [lia | right; exact Hub].
    + intros Hm. pose proof (Hmeta_below b Hm). lia.
  - (* sk_disj -- W4: no block is named twice *)
    rewrite Hpin. intros i n j m b Hi Hj Hoi Hoj.
    destruct (img_nodes_lookup_inv (fs_blocks dk) sb nib i n Hi)
      as [Hregi ->].
    destruct (img_nodes_lookup_inv (fs_blocks dk) sb nib j m Hj)
      as [Hregj ->].
    destruct (Hlive_of_owns i b Hregi Hoi) as [Hrani Htyi].
    destruct (Hlive_of_owns j b Hregj Hoj) as [Hranj Htyj].
    destruct (decide (i = j)) as [-> | Hne]; [reflexivity |].
    exfalso.
    destruct (img_owned_block (fs_blocks dk) sb i b Hwf Hrani Htyi Hoi)
      as [Hbi _].
    destruct (img_owned_block (fs_blocks dk) sb j b Hwf Hranj Htyj Hoj)
      as [Hbj _].
    pose proof (fs_inode_blocks_disjoint (fs_blocks dk) sb i j Hnd
                  Hrani Hranj Hne Htyi Htyj) as Hdj.
    rewrite elem_of_disjoint in Hdj.
    apply (Hdj b);
      rewrite /fs_inode_blocks_set elem_of_list_to_set; assumption.
  - (* sk_sbok -- W1 *)
    rewrite Hpsb. exact Hsb.
  - (* sk_reg -- the region is EXACTLY [[inodestart, bmapstart)], which is
       the [nib = ninodes/16 + 1] conjunct of [fs_boot_image_wf] *)
    rewrite Hpsb Hpin. intros i n Hi.
    destruct (img_nodes_lookup_inv (fs_blocks dk) sb nib i n Hi) as [Hreg _].
    apply region_inums_spec in Hreg.
    assert (Hd : 0 <= i `div` 16 < Z.of_nat nib).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    split; lia.
  - (* sk_slot -- W4 per inum; a FREE inum's node is BARE and owes nothing *)
    rewrite Hpin. intros i n Hi.
    destruct (img_nodes_lookup_inv (fs_blocks dk) sb nib i n Hi) as [Hreg ->].
    pose proof (proj1 (region_inums_spec nib i) Hreg) as Hri.
    destruct (decide
                (bv_unsigned (di_type (fs_dinode (fs_blocks dk) sb i)) = 0))
      as [H0 | Hnz].
    + apply fn_slot_inj_bare.
      exact (img_node_bare (fs_blocks dk) sb nib i Hbare
               (fs_region_wf_nlink _ _ _ Hrw) Hri H0).
    + assert (Hran : 0 <= i < FsImg.sb_ninodes sb).
      { split; [lia |].
        destruct (Z_lt_ge_dec i (FsImg.sb_ninodes sb)) as [Hlt | Hge];
          [exact Hlt |].
        exfalso. apply Hnz.
        exact (fs_region_free_spec (fs_blocks dk) sb nib i
                 (fs_region_wf_free _ _ _ Hrw)
                 ltac:(lia) ltac:(lia) ltac:(lia)). }
      apply (img_node_slot_inj (fs_blocks dk) sb i).
      exact (fsimg_wf_slot_inj (fs_blocks dk) sb i Hwf Hran Hnz).
  - (* sk_regdom (durable-disk lane E-boot) -- the region's TAIL inums are
       named too, and at the image that is by construction: [img_nodes]'
       domain IS [region_inums nib], and [fs_boot_image_wf]'s width tie
       [Hnibq] is exactly [nib = ninodes/16 + 1]. *)
    rewrite Hpsb Hpin. intros i Hi.
    exists (img_node (fs_blocks dk) sb i).
    apply img_nodes_lookup, region_inums_spec. lia.
  - (* sk_dirloc (durable-disk lane E-clauses): the three directory
       clauses the escrow payloads carry, at the state's own region
       width -- which is [nib], by conjunct (6). *)
    rewrite Hpsb Hpin.
    assert (Hw : Z.to_nat (FsImg.sb_ninodes sb / 16 + 1) = nib)
      by (rewrite -Hnibq Nat2Z.id //).
    rewrite Hw. intros i n Hi.
    destruct (img_nodes_lookup_inv (fs_blocks dk) sb nib i n Hi)
      as [Hreg ->].
    exact (img_node_dir_local (fs_blocks dk) sb cov nib i Hwf Hrw Hfull
             Hnin Hcovdata Hreg).
  - (* sk_dombelow (durable-disk lane E-himg): the map's keys ARE the home
       blocks, and the image's own [fs_cov_in] against conjunct (12) --
       the disk is no larger than [size] blocks -- puts every covered block
       below [size]. *)
    rewrite Hpsb. intros b [bs Hbs].
    apply fs_restrict_lookup_Some in Hbs as [Hh _].
    rewrite /fs_home_set elem_of_difference in Hh.
    destruct (Hcovin b (proj1 Hh)) as [Hb0 Hbn]. lia.
Qed.

(* ===================================================================== *)
(* 12.  ERA 0'S SNAPSHOT -- THE ONE VALUE-FIRST ALLOCATION LEFT            *)
(*      (durable-disk lane H5)                                             *)
(*                                                                        *)
(*  Every other snapshot in the tree is MINTED off a source instance's own *)
(*  readings ([FsDurXfer.fs_state_mint_runs] over [FsDurSnap.snap_mint]).  *)
(*  Era 0 has no source instance -- the first file system exists only as   *)
(*  BYTES -- so exactly here, and nowhere else, a byte map is CARVED into  *)
(*  an [FsState.fs_state] by [FsDurSnap.snap_ok]'s disjointness clauses    *)
(*  ([FsDurAlloc]).  [FsDurSnap.P_dur D] is a function of [D] ALONE and is *)
(*  allocated by a basic update from nothing, so the image side of the     *)
(*  boot needs NO resource from anybody, which is what makes lane C's      *)
(*  change to [FsCrash.P_fs] arity-free and what lets [FsCrash.P_fs_alloc] *)
(*  take the epoch as a RESOURCE instead of taking [snap_ok] as a premise. *)
(* ===================================================================== *)

(* THE ALLOCATOR'S OWN SECTION, at the THREE classes [FsDurAlloc] needs and
   no more: the top-level theorem builds era 0's epoch before it has a
   [riscvGS], so a heavier binder list here would not resolve there
   (durable-notes.md, "a lemma's binder list must match the definition it is
   about").  [img_snap_ok] is pure, so nothing else is needed. *)
Section DurImgAlloc.
  Context `{!diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.

  Lemma img_P_dur_alloc (dk : Z -> bv 8) (ndisk : nat) (sb : fs_sb)
      (nib : nat) (cov : gset Z) :
    fs_boot_image_wf dk ndisk sb nib cov ->
    ⊢ |==> P_dur (fs_restrict (fs_blocks dk)
                    (fs_home_set cov (FsImg.sb_logstart sb))).
  Proof.
    intros Himg.
    exact (P_dur_alloc (img_state (fs_blocks dk) sb nib)
             (fs_restrict (fs_blocks dk)
                (fs_home_set cov (FsImg.sb_logstart sb)))
             (img_snap_ok dk ndisk sb nib cov Himg)).
  Qed.

End DurImgAlloc.
