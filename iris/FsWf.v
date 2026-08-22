(* ====================================================================== *)
(* FsWf.v -- [fs_durable_wf]: THE well-formedness invariant of the durable *)
(* committed view (claude-notes/design/crash.md, "The split crash           *)
(* predicate"; worklist stage F1).                                          *)
(*                                                                          *)
(* The property every reachable committed state has and every commit        *)
(* preserves; [fs.img] is merely the base case of the poweroff/poweron      *)
(* loop invariant.  It rides [FsCrash.fs_rec_wf] as the [P_wf] conjunct     *)
(* and is what the era's boot mint will read its image facts from           *)
(* (stage H).                                                               *)
(*                                                                          *)
(* THE REAL BODY IS [fs_durable_wf_body] BELOW (stage F1); the name         *)
(* [fs_durable_wf] keeps the placeholder body [True] until the SWITCH-ON    *)
(* (after stages G3 and H2) equates the two and deletes the placeholder --  *)
(* see the worklist's stage-F header for why the two names coexist.         *)
(*                                                                          *)
(* WHAT THE BODY SAYS, in one breath: the committed view [D] (a finite      *)
(* block map -- [FsCrash.fr_D]'s type) parses to a well-formed superblock   *)
(* and satisfies the general content sweeps of [FsImg] -- W3 minus the      *)
(* link floor (inode records; a committed orphan is live at [nlink = 0]),   *)
(* W4/W5 (used set + bitmap), W6 scoped to reachable dirs (an orphan        *)
(* dir's ".." may dangle), W7 (root), W8 (dot records), the region sweep    *)
(* at the geometry's own [nib] -- plus the GENERAL form of W9: link         *)
(* counts are ticket counts over REACHABLE directories, and every           *)
(* unreachable live directory is empty-but-dots.  NO log-cleanliness        *)
(* conjunct: a committed-uninstalled log is a fine durable state (ruling    *)
(* 2), which is the whole reason [fsimg_wf] cannot be the durable           *)
(* predicate.                                                               *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import BioDefs.     (* [BSIZE] *)
Require Import DirentEnc.   (* [bname], the canonical-name reader *)
Require Import DinodeEnc.   (* [dinode], [IBLOCK]/[islot] *)
Require Import InodeDefs.   (* [file_byte] *)
Require Import DirView.     (* the [dir_*] readers and their agree lemmas *)
Require Import FsTree.      (* [dir_view], [node_of], [path_at], [fstree] *)
Require Import FsImg.       (* the sweeps this predicate is built from *)

Local Open Scope Z_scope.

Definition fs_durable_wf (D : gmap Z (list (bv 8))) : Prop := True.

(* THE GATE (delete together with the placeholder body).  Every use of this
   lemma marks a site that may NOT survive the switch-on of the real body:
     - the recovery-side permits' RE-BASE of [fr_D] (stage H makes them
       ghost no-ops first);
     - the commit permit's compat wrapper (stage G supplies the real
       preservation fupd);
     - [P_fs_alloc]'s establishment (stage E4 discharges it at the image
       via [fsimg_durable_wf]).
   When the switch-on replaces the body, this lemma becomes unprovable and
   each use site surfaces as an error -- that is the mechanism, not an
   accident. *)
Lemma fs_durable_wf_placeholder (D : gmap Z (list (bv 8))) : fs_durable_wf D.
Proof. exact I. Qed.

(* ====================================================================== *)
(*  1.  THE VIEW OF A FINITE BLOCK MAP                                     *)
(* ====================================================================== *)

(* The committed view is a [gmap]; every [FsImg] decoder wants a total
   [Z -> list (bv 8)] and is junk-tolerant, so a missing block reads as
   [[]] (the superblock parse then fails on its length guard, every
   [fs_le_at] reads zeros, and no decoder gets stuck). *)
Definition dv_of_D (D : gmap Z (list (bv 8))) : Z -> list (bv 8) :=
  fun b => default [] (D !! b).

(* ====================================================================== *)
(*  2.  W9 GENERALIZED -- REACHABILITY AND THE REACHABLE-TICKET COUNT      *)
(* ====================================================================== *)

(* An inum is REACHABLE when some path from the root resolves to it.  This
   is a Prop over [FsTree.path_at] at [tree_of_disk] -- deliberately not a
   computation: the mkfs base case needs no computable reachability
   (under [fsimg_wf] the only directory is the root, so the reachable-dir
   set is {[ROOTINO]} by proof), and the update proofs manipulate paths,
   not sweeps. *)
Definition fs_reachable (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) : Prop :=
  exists p : list fname, path_at (tree_of_disk P sb) ROOTINO p = Some z.

(* THE SHAPE CHOICE for the reachable-ticket count (worklist F1): the
   count is [fs_tick_count] over a supply FILTERED BY A [gset] [rd], with
   [rd] pinned to "the reachable live directories" by the separate Prop
   [fs_rdirs].  Chosen over a Prop-level counting relation because every
   later update proof manipulates the count ARITHMETICALLY (one dirlink
   adds one ticket; one unlink removes one), and a filtered [omap]/[mjoin]
   supply has exactly the locality the all-dirs supply [fs_all_tickets]
   already enjoys: an update to one directory's records touches one
   segment of the join, and moving a directory in or out of [rd] adds or
   removes one whole segment.  [rd] is existentially quantified at the
   predicate: reachability is not computable here, and the updates know
   their [rd] delta explicitly (a link/unlink of a dir moves exactly that
   dir). *)
Definition fs_rdirs (P : Z -> list (bv 8)) (sb : fs_sb) (rd : gset Z)
  : Prop :=
  forall z : Z,
    z ∈ rd <-> 0 <= z < sb_ninodes sb
               /\ bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z
               /\ fs_reachable P sb z.

(* the ticket supply of the directories in [rd], in inum order --
   [fs_all_tickets]'s shape with the reachability filter *)
Definition fs_rtickets (P : Z -> list (bv 8)) (sb : fs_sb) (rd : gset Z)
  : list Z :=
  mjoin ((fun i => if bool_decide (Z.of_nat i ∈ rd)
                   then fs_dir_tickets_at P sb (Z.of_nat i) else [])
           <$> seq 0 (Z.to_nat (sb_ninodes sb))).

(* THE COUNT: how many ticket-bearing records of REACHABLE directories
   name [z] *)
Definition fs_rtick (P : Z -> list (bv 8)) (sb : fs_sb) (rd : gset Z)
    (z : Z) : nat :=
  fs_tick_count (fs_rtickets P sb rd) z.

(* W9's general clause: every live inum's [nlink] IS its reachable-ticket
   count -- plus one at the root, whose extra link (mkfs's own) no record
   pays for.  Self-tickets are excluded by [fs_rec_ticket]'s guard exactly
   as the resource ledger's [DirLinks.dir_link_at] excludes them, so a
   non-root directory's count is [1 (parent's entry) + #child-dirs
   (their ".." records)] -- exactly xv6's [nlink] discipline (create's
   [dp->nlink++] for "..", no self-count for ".").  A committed orphan
   FILE has [nlink = 0] and no entry names it, so the file arm needs no
   extra case. *)
Definition fs_links_gen (P : Z -> list (bv 8)) (sb : fs_sb) (rd : gset Z)
  : Prop :=
  forall z : Z, 0 <= z < sb_ninodes sb ->
    let dn := fs_dinode P sb z in
    bv_unsigned (di_type dn) <> 0 ->
    bv_unsigned (di_nlink dn)
    = Z.of_nat (fs_rtick P sb rd z)
      + (if bool_decide (bv_unsigned (di_type dn) = T_DIR_z)
         then (if bool_decide (z = ROOTINO) then 1 else 0)
         else 0).

(* "empty-but-dots", BY INDEX: no live record beyond the two dot slots.
   The index form (records >= 2 dead) rather than a by-name form because
   W8 ([fs_dots_all], a sibling conjunct of the body) already pins records
   0 and 1 as "." and "..", and because it is literally what xv6's
   [isdirempty] checks (fs.c: offsets from [2*sizeof(dirent)] up must have
   [inum == 0]). *)
Definition fs_dir_dots_only (P : Z -> list (bv 8)) (dn : dinode) : Prop :=
  forall k : nat, (2 <= k)%nat ->
    (k < dir_nrec (bv_unsigned (di_size dn)))%nat ->
    ~ dir_live (fs_data_of P dn) k.

(* every UNREACHABLE live directory is empty-but-dots.  This is what makes
   the orphan story closed -- xv6's unlink only removes EMPTY directories,
   so a dir that loses its last path is empty at that instant and nothing
   can ever populate it (no path reaches it) -- and it is what stage H's
   [ireclaim] routing consumes: an orphan dir owes the reclaim path
   exactly its two dot records and its own inode. *)
Definition fs_orphans_empty (P : Z -> list (bv 8)) (sb : fs_sb)
    (rd : gset Z) : Prop :=
  forall z : Z, 0 <= z < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z ->
    z ∉ rd ->
    fs_dir_dots_only P (fs_dinode P sb z).

(* ====================================================================== *)
(*  3.  THE PREDICATE                                                      *)
(* ====================================================================== *)

(* the sweeps, at a view and its parsed superblock.  A record so stage-G
   consumers project fields by name instead of destructing a conjunction
   tower.  NO W2: log cleanliness is no part of durability (ruling 2). *)
Record fs_durable_sweeps (P : Z -> list (bv 8)) (sb : fs_sb) : Prop := {
  fdw_sb : fs_sb_wf sb = true;                                    (* W1  *)
  (* W3 MINUS THE LINK FLOOR ([FsImg.fs_inodes_dwf]): the pinned W9 arm
     says a committed orphan has [nlink = 0] with a LIVE type, so
     [fs_inode_wf]'s [1 <= nlink] clause is a boot fact, not a durable
     one -- sweeping [fs_inodes_wf] here would make the predicate false
     at exactly the orphan states stage H's [ireclaim] consumes. *)
  fdw_inodes : fs_inodes_dwf P sb = true;
  fdw_used : exists u : gset Z,                                   (* W4/5 *)
      fs_used_set P sb = Some u /\ fs_bitmap_wf P sb u = true;
  fdw_root : fs_root_wf P sb = true;                              (* W7  *)
  fdw_dots : fs_dots_all P sb = true;                             (* W8  *)
  (* the inode-region tail and L3/L4, at the geometry's own [nib]
     ([FsCfgBoot.fs_boot_image_wf] conjunct (6)'s spelling) *)
  fdw_region : exists nib : nat,
      Z.of_nat nib = sb_ninodes sb / 16 + 1
      /\ fs_region_wf P sb nib = true;
  (* W6 SCOPED TO REACHABLE DIRS + W9 GENERALIZED, sharing one [rd].
     W6's per-dir bundle ([fs_dir_ok]) binds every live record's TARGET
     liveness -- and an ORPHAN dir's ".." can dangle (unlink the orphan's
     emptied parent: the parent's inode is freed while the orphan still
     carries a ".." naming it), so the bundle is durable only for
     REACHABLE dirs.  An orphan dir owes exactly W8's dots (swept above,
     target-free) and emptiness below -- which is also all stage H's
     [ireclaim] routing wants of it. *)
  fdw_links : exists rd : gset Z,
      fs_rdirs P sb rd
      /\ (forall z : Z, z ∈ rd -> fs_dir_ok P sb z (fs_dinode P sb z))
      /\ fs_links_gen P sb rd
      /\ fs_orphans_empty P sb rd;
}.

Definition fs_durable_wf_view (P : Z -> list (bv 8)) : Prop :=
  exists sb : fs_sb, fs_parse_sb P = Some sb /\ fs_durable_sweeps P sb.

(* THE REAL BODY (stage F1): the durable well-formedness of a committed
   view, stated at the [gmap] the crash predicate carries. *)
Definition fs_durable_wf_body (D : gmap Z (list (bv 8))) : Prop :=
  fs_durable_wf_view (dv_of_D D).

(* ====================================================================== *)
(*  4.  GEOMETRY HELPERS                                                   *)
(* ====================================================================== *)

(* what the agreement lemmas below need out of W1, bundled once *)
Lemma fs_sb_ok_geom (sb : fs_sb) :
  fs_sb_ok sb ->
  sb_inodestart sb <= sb_bmapstart sb
  /\ sb_bmapstart sb < fs_data_start sb
  /\ fs_data_start sb < sb_size sb
  /\ 1 < sb_ninodes sb
  /\ sb_ninodes sb <= 16 * (sb_ninodes sb / 16 + 1)
  /\ 16 * (sb_ninodes sb / 16 + 1) < bv_modulus 32.
Proof.
  intros Hok.
  pose proof (sbo_logstart sb Hok).
  pose proof (sbo_nlog sb Hok).
  pose proof (sbo_inodestart sb Hok).
  pose proof (sbo_bmapstart sb Hok).
  pose proof (sbo_size sb Hok).
  pose proof (sbo_ninodes sb Hok).
  pose proof (sbo_nblocks sb Hok).
  pose proof (sbo_one_bitmap sb Hok).
  unfold ROOTINO in *.
  pose proof (Z.mod_pos_bound (sb_ninodes sb) 16 ltac:(lia)).
  pose proof (Z.div_mod (sb_ninodes sb) 16 ltac:(lia)).
  assert (Hm : bv_modulus 32 = 4294967296) by reflexivity.
  unfold fs_data_start, BSIZE_z in *. lia.
Qed.

(* the block a record decode reads is an inode-region block *)
Lemma iblock_range (sb : fs_sb) (i : Z) :
  fs_sb_ok sb -> 0 <= i < 16 * (sb_ninodes sb / 16 + 1) ->
  sb_inodestart sb <= IBLOCK (fs_inum_bv i) (sb_inodestart sb) < sb_size sb.
Proof.
  intros Hok Hi.
  destruct (fs_sb_ok_geom sb Hok) as (H1 & H2 & H3 & H4 & H5 & H6).
  pose proof (sbo_bmapstart sb Hok) as Hbm.
  assert (Hbv : bv_unsigned (fs_inum_bv i) = i).
  { unfold fs_inum_bv. apply Z_to_bv_small. lia. }
  unfold IBLOCK. rewrite Hbv.
  assert (Hd : 0 <= i / 16 < sb_ninodes sb / 16 + 1).
  { split; [apply Z.div_pos; lia |]. apply Z.div_lt_upper_bound; lia. }
  unfold fs_data_start in *. lia.
Qed.

(* a directory or file of legal size keeps every read inside the first
   [FS_MAXFILE] content blocks -- the bound the data-agreement lemmas are
   stated at *)
Lemma dir_nrec_bound (sz : Z) :
  0 <= sz -> sz <= Z.of_nat FS_MAXFILE * BSIZE_z ->
  (16 * dir_nrec sz <= FS_MAXFILE * BSIZE)%nat
  /\ (Z.to_nat sz <= FS_MAXFILE * BSIZE)%nat.
Proof.
  intros H0 Hsz.
  assert (HB : Z.of_nat (FS_MAXFILE * BSIZE)
               = Z.of_nat FS_MAXFILE * BSIZE_z).
  { rewrite Nat2Z.inj_mul, BSIZE_z_nat. reflexivity. }
  assert (Hq : 0 <= sz / 16) by (apply Z.div_pos; lia).
  assert (Hd : 16 * (sz / 16) <= sz).
  { pose proof (Z.mod_pos_bound sz 16 ltac:(lia)).
    pose proof (Z.div_mod sz 16 ltac:(lia)). lia. }
  split.
  - apply Nat2Z.inj_le. rewrite Nat2Z.inj_mul, HB.
    unfold dir_nrec. rewrite Z2Nat.id by exact Hq. lia.
  - apply Nat2Z.inj_le. rewrite Z2Nat.id by exact H0. rewrite HB. lia.
Qed.

(* ====================================================================== *)
(*  5.  AGREEMENT: DATA-LEVEL                                              *)
(*                                                                        *)
(*  The reusable "the reader only reads <these blocks>" laws that both     *)
(*  the [gmap]-view bridge below and stage F2's update lemmas run on.      *)
(*  Everything here is against POINTWISE agreement of the block views      *)
(*  ([data' k = data k] below a block bound, [P' b = P b] on a region);    *)
(*  no functional extensionality anywhere.                                 *)
(* ====================================================================== *)

Lemma omap_ext_in {A B : Type} (f g : A -> option B) (l : list A) :
  (forall x : A, x ∈ l -> f x = g x) -> omap f l = omap g l.
Proof.
  induction l as [| a l IH]; intros H; [reflexivity |].
  csimpl. rewrite (H a (elem_of_list_here a l)).
  destruct (g a) as [b|]; [f_equal |]; apply IH; intros x Hx;
    apply H, elem_of_list_further, Hx.
Qed.

Lemma file_byte_agree (data data' : nat -> list (bv 8)) (m j : nat) :
  (forall k : nat, (k < m)%nat -> data' k = data k) ->
  (j < m * BSIZE)%nat ->
  file_byte data' j = file_byte data j.
Proof.
  intros Hd Hj. unfold file_byte. rewrite Hd; [reflexivity |].
  apply Nat.Div0.div_lt_upper_bound. lia.
Qed.

Lemma dir_win_agree_blocks (data data' : nat -> list (bv 8)) (m r : nat) :
  (forall k : nat, (k < m)%nat -> data' k = data k) ->
  (16 * r + 16 <= m * BSIZE)%nat ->
  dir_win_agree data data' r.
Proof.
  intros Hd Hr j Hj. apply (file_byte_agree data data' m); [exact Hd | lia].
Qed.

(* [DirView.dir_bname_agree] at [FsTree.dir_bname]'s spelling *)
Lemma dir_bname_agree' (data data' : nat -> list (bv 8)) (k : nat) :
  dir_win_agree data data' k -> dir_bname data' k = dir_bname data k.
Proof. intros H. unfold dir_bname. apply dir_bname_agree, H. Qed.

Lemma dir_entry_agree (data data' : nat -> list (bv 8)) (k : nat) :
  (forall r : nat, (r <= k)%nat -> dir_win_agree data data' r) ->
  dir_entry data' k = dir_entry data k.
Proof.
  intros H.
  assert (Hw : dir_wins data' k = dir_wins data k).
  { unfold dir_wins.
    rewrite (dir_liveb_agree data data' k (H k (le_n k))).
    unfold dir_bname.
    rewrite (dir_bname_agree data data' k (H k (le_n k))).
    rewrite (dir_first_agree data data' k
               (bname 14 (dir_name data k))); [reflexivity |].
    intros r Hr. apply H. lia. }
  unfold dir_entry. rewrite Hw.
  destruct (dir_wins data k); [| reflexivity].
  rewrite (dir_bname_agree' data data' k (H k (le_n k))).
  rewrite (dir_inum_agree data data' k (H k (le_n k))). reflexivity.
Qed.

Lemma dir_view_agree (data data' : nat -> list (bv 8)) (n : nat) :
  (forall r : nat, (r < n)%nat -> dir_win_agree data data' r) ->
  dir_view data' n = dir_view data n.
Proof.
  intros H. unfold dir_view. f_equal.
  apply omap_ext_in. intros k Hk. apply elem_of_seq in Hk.
  apply dir_entry_agree. intros r Hr. apply H. lia.
Qed.

Lemma dir_names_unique_agree (data data' : nat -> list (bv 8)) (n : nat) :
  (forall r : nat, (r < n)%nat -> dir_win_agree data data' r) ->
  dir_names_unique data n -> dir_names_unique data' n.
Proof.
  intros H Hu j k Hj Hk Hlj Hlk Heq.
  apply (Hu j k Hj Hk).
  - unfold dir_live in *.
    rewrite (dir_inum_agree _ _ j (H j Hj)) in Hlj. exact Hlj.
  - unfold dir_live in *.
    rewrite (dir_inum_agree _ _ k (H k Hk)) in Hlk. exact Hlk.
  - rewrite <- (dir_bname_agree' _ _ j (H j Hj)),
      <- (dir_bname_agree' _ _ k (H k Hk)). exact Heq.
Qed.

Lemma file_bytes_agree (data data' : nat -> list (bv 8)) (m n : nat) :
  (forall k : nat, (k < m)%nat -> data' k = data k) ->
  (n <= m * BSIZE)%nat ->
  file_bytes data' n = file_bytes data n.
Proof.
  intros Hd Hn. unfold file_bytes. apply list_fmap_ext.
  intros i x Hi. apply lookup_seq in Hi as [-> Hi].
  apply (file_byte_agree data data' m); [exact Hd | lia].
Qed.

Lemma node_of_agree (dn : dinode) (data data' : nat -> list (bv 8))
    (m : nat) :
  (forall k : nat, (k < m)%nat -> data' k = data k) ->
  (16 * dir_nrec (bv_unsigned (di_size dn)) <= m * BSIZE)%nat ->
  (Z.to_nat (bv_unsigned (di_size dn)) <= m * BSIZE)%nat ->
  node_of dn data' = node_of dn data.
Proof.
  intros Hd Hnr Hsz. unfold node_of.
  destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)).
  - f_equal. apply dir_view_agree. intros r Hr.
    apply (dir_win_agree_blocks data data' m); [exact Hd | lia].
  - f_equal. apply (file_bytes_agree data data' m); [exact Hd | exact Hsz].
Qed.

(* ====================================================================== *)
(*  6.  AGREEMENT: DECODER-LEVEL                                           *)
(*                                                                        *)
(*  Minimal-footprint [*_ext] forms (one block each) and their [*_agree]   *)
(*  corollaries under region agreement.  Region agreement is always        *)
(*  [forall b, sb_inodestart sb <= b < sb_size sb -> P' b = P b] -- the    *)
(*  inode blocks, the bitmap block and the data region in one range --     *)
(*  because the log region sits BELOW [sb_inodestart] (W1's geometry), so  *)
(*  this is exactly what the committed view of a disk agrees with the      *)
(*  disk on.                                                               *)
(* ====================================================================== *)

Lemma fs_parse_sb_ext (P P' : Z -> list (bv 8)) :
  P' SB_BNO = P SB_BNO -> fs_parse_sb P' = fs_parse_sb P.
Proof. intros H. unfold fs_parse_sb. rewrite H. reflexivity. Qed.

Lemma fs_dinode_ext (P P' : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  P' (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
  = P (IBLOCK (fs_inum_bv i) (sb_inodestart sb)) ->
  fs_dinode P' sb i = fs_dinode P sb i.
Proof.
  intros H. unfold fs_dinode, fs_dinode_bytes. rewrite H. reflexivity.
Qed.

Lemma fs_dinode_agree (P P' : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_sb_ok sb ->
  (forall b : Z, sb_inodestart sb <= b < sb_size sb -> P' b = P b) ->
  0 <= i < 16 * (sb_ninodes sb / 16 + 1) ->
  fs_dinode P' sb i = fs_dinode P sb i.
Proof.
  intros Hok Hag Hi. apply fs_dinode_ext, Hag, iblock_range; assumption.
Qed.

(* region agreement restricted to the data region *)
Lemma fs_agree_data (P P' : Z -> list (bv 8)) (sb : fs_sb) :
  fs_sb_ok sb ->
  (forall b : Z, sb_inodestart sb <= b < sb_size sb -> P' b = P b) ->
  forall b : Z, fs_data_start sb <= b < sb_size sb -> P' b = P b.
Proof.
  intros Hok Hag b Hb. apply Hag.
  destruct (fs_sb_ok_geom sb Hok) as (H1 & H2 & _). lia.
Qed.

Lemma fs_ind_ents_ext (P P' : Z -> list (bv 8)) (dn : dinode) :
  (bv_unsigned (di_addrs dn !!! 12%nat) <> 0 ->
   P' (bv_unsigned (di_addrs dn !!! 12%nat))
   = P (bv_unsigned (di_addrs dn !!! 12%nat))) ->
  fs_ind_ents P' dn = fs_ind_ents P dn.
Proof.
  intros H. unfold fs_ind_ents. cbv zeta.
  destruct (bv_unsigned (di_addrs dn !!! 12%nat) =? 0) eqn:E;
    [reflexivity |].
  rewrite H; [reflexivity |]. apply Z.eqb_neq. exact E.
Qed.

Lemma fs_ind_ents_agree (P P' : Z -> list (bv 8)) (sb : fs_sb)
    (dn : dinode) :
  fs_inode_dok P sb dn ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> P' b = P b) ->
  fs_ind_ents P' dn = fs_ind_ents P dn.
Proof.
  intros Hok Hag. apply fs_ind_ents_ext. intros Hnz. apply Hag.
  destruct (Z.le_gt_cases (fs_nblk (bv_unsigned (di_size dn)))
              (Z.of_nat FS_NDIRECT)) as [Hle | Hgt].
  - exfalso. apply Hnz. exact (fdi_ind_zero P sb dn Hok Hle).
  - exact (fdi_ind P sb dn Hok Hgt).
Qed.

Lemma fs_blk_addr_agree (P P' : Z -> list (bv 8)) (sb : fs_sb)
    (dn : dinode) (k : nat) :
  fs_inode_dok P sb dn ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> P' b = P b) ->
  fs_blk_addr P' dn k = fs_blk_addr P dn k.
Proof.
  intros Hok Hag. unfold fs_blk_addr.
  rewrite (fs_ind_ents_agree P P' sb dn Hok Hag). reflexivity.
Qed.

(* a nonzero block address of a legal-size inode is a data block --
   BELOW the [FS_MAXFILE] index bound, which is where every consumer
   ([node_of], the dir readers) stays *)
Lemma fs_blk_addr_range (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode)
    (k : nat) :
  fs_inode_dok P sb dn -> (k < FS_MAXFILE)%nat ->
  fs_blk_addr P dn k <> 0 ->
  fs_data_start sb <= fs_blk_addr P dn k < sb_size sb.
Proof.
  intros Hok Hk Hnz. unfold fs_blk_addr in *.
  destruct (Nat.ltb_spec k FS_NDIRECT) as [Hd | Hd].
  - destruct (Z.lt_ge_cases (Z.of_nat k)
                (fs_nblk (bv_unsigned (di_size dn)))) as [Hlt | Hge].
    + exact (fdi_direct P sb dn Hok k Hd Hlt).
    + exfalso. apply Hnz. exact (fdi_direct_zero P sb dn Hok k Hd Hge).
  - assert (Hj : (k - FS_NDIRECT < FS_NINDIRECT)%nat)
      by (unfold FS_MAXFILE, FS_NDIRECT, FS_NINDIRECT in *; lia).
    destruct (Z.lt_ge_cases (Z.of_nat (k - FS_NDIRECT))
                (fs_nblk (bv_unsigned (di_size dn)) - Z.of_nat FS_NDIRECT))
      as [Hlt | Hge].
    + exact (fdi_ent P sb dn Hok (k - FS_NDIRECT)%nat Hj Hlt).
    + exfalso. apply Hnz.
      exact (fdi_ent_zero P sb dn Hok (k - FS_NDIRECT)%nat Hj Hge).
Qed.

Lemma fs_data_of_agree (P P' : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode)
    (k : nat) :
  fs_inode_dok P sb dn ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> P' b = P b) ->
  (k < FS_MAXFILE)%nat ->
  fs_data_of P' dn k = fs_data_of P dn k.
Proof.
  intros Hok Hag Hk.
  rewrite !fs_data_of_addr, (fs_blk_addr_agree P P' sb dn k Hok Hag).
  destruct (fs_blk_addr P dn k =? 0) eqn:E; [reflexivity |].
  apply Hag, (fs_blk_addr_range P sb dn k Hok Hk).
  apply Z.eqb_neq. exact E.
Qed.

Lemma fs_inode_blocks_agree (P P' : Z -> list (bv 8)) (sb : fs_sb)
    (dn : dinode) :
  fs_inode_dok P sb dn ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> P' b = P b) ->
  fs_inode_blocks P' dn = fs_inode_blocks P dn.
Proof.
  intros Hok Hag. unfold fs_inode_blocks.
  rewrite (fs_ind_ents_agree P P' sb dn Hok Hag). reflexivity.
Qed.

Lemma fs_inode_dwf_agree (P P' : Z -> list (bv 8)) (sb : fs_sb)
    (dn : dinode) :
  fs_inode_dok P sb dn ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> P' b = P b) ->
  fs_inode_dwf P' sb dn = fs_inode_dwf P sb dn.
Proof.
  intros Hok Hag. unfold fs_inode_dwf.
  rewrite (fs_ind_ents_agree P P' sb dn Hok Hag). reflexivity.
Qed.

(* ====================================================================== *)
(*  7.  AGREEMENT: THE SWEEPS                                              *)
(* ====================================================================== *)

Section sweep_agree.
  Context (P P' : Z -> list (bv 8)) (sb : fs_sb).
  Context (Hok : fs_sb_ok sb).
  Context (Hag : forall b : Z,
              sb_inodestart sb <= b < sb_size sb -> P' b = P b).

  Let HagD : forall b : Z, fs_data_start sb <= b < sb_size sb -> P' b = P b
    := fs_agree_data P P' sb Hok Hag.

  (* one live inode's data view, below the consumer bound *)
  Lemma fs_live_data_agree (dn : dinode) :
    fs_inode_dok P sb dn ->
    forall k : nat, (k < FS_MAXFILE)%nat ->
      fs_data_of P' dn k = fs_data_of P dn k.
  Proof.
    intros Hio k Hk. exact (fs_data_of_agree P P' sb dn k Hio HagD Hk).
  Qed.

  (* ...and the record-window agreement it induces below [nrec] *)
  Lemma fs_live_win_agree (dn : dinode) :
    fs_inode_dok P sb dn ->
    forall r : nat, (r < dir_nrec (bv_unsigned (di_size dn)))%nat ->
      dir_win_agree (fs_data_of P dn) (fs_data_of P' dn) r.
  Proof.
    intros Hio r Hr.
    pose proof (fdi_size P sb dn Hio) as Hsz.
    pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as Hsz0.
    destruct (dir_nrec_bound (bv_unsigned (di_size dn)) Hsz0 Hsz)
      as [Hnr _].
    apply (dir_win_agree_blocks _ _ FS_MAXFILE);
      [exact (fs_live_data_agree dn Hio) | lia].
  Qed.

  (* --- W3 ------------------------------------------------------------- *)

  Lemma fs_inodes_dwf_agree :
    fs_inodes_dwf P sb = true -> fs_inodes_dwf P' sb = true.
  Proof.
    intros H.
    destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & Hn1 & Hn16 & _).
    unfold fs_inodes_dwf.
    rewrite List.forallb_forall. intros x Hin.
    apply elem_of_list_In, elem_of_seq in Hin.
    cbv beta zeta.
    rewrite (fs_dinode_agree P P' sb (Z.of_nat x) Hok Hag ltac:(lia)).
    pose proof (forallb_seq _ _ x H ltac:(lia)) as Hx.
    cbv beta zeta in Hx.
    destruct (bv_unsigned (di_type (fs_dinode P sb (Z.of_nat x))) =? 0)
      eqn:Ety; [reflexivity |].
    rewrite (fs_inode_dwf_agree P P' sb _
               (fs_inodes_dwf_spec P sb (Z.of_nat x) H ltac:(lia)
                  (proj1 (Z.eqb_neq _ _) Ety)) HagD).
    exact Hx.
  Qed.

  (* --- W4 ------------------------------------------------------------- *)

  Lemma fs_used_blocks_agree :
    fs_inodes_dwf P sb = true -> fs_used_blocks P' sb = fs_used_blocks P sb.
  Proof.
    intros HW3.
    destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & Hn1 & Hn16 & _).
    unfold fs_used_blocks. f_equal. apply list_fmap_ext.
    intros idx x Hx. apply lookup_seq in Hx as [-> Hx]. cbv beta zeta.
    rewrite (fs_dinode_agree P P' sb (Z.of_nat (0 + idx)) Hok Hag
               ltac:(lia)).
    destruct (bv_unsigned (di_type (fs_dinode P sb (Z.of_nat (0 + idx))))
              =? 0) eqn:Ety; [reflexivity |].
    apply (fs_inode_blocks_agree P P' sb); [| exact HagD].
    apply (fs_inodes_dwf_spec P sb (Z.of_nat (0 + idx)) HW3 ltac:(lia)).
    apply Z.eqb_neq. exact Ety.
  Qed.

  Lemma fs_used_set_agree :
    fs_inodes_dwf P sb = true -> fs_used_set P' sb = fs_used_set P sb.
  Proof.
    intros HW3. unfold fs_used_set.
    rewrite (fs_used_blocks_agree HW3). reflexivity.
  Qed.

  (* --- W5 ------------------------------------------------------------- *)

  Lemma fs_bitmap_wf_agree (u : gset Z) :
    fs_bitmap_wf P' sb u = fs_bitmap_wf P sb u.
  Proof.
    unfold fs_bitmap_wf.
    rewrite (Hag (sb_bmapstart sb)); [reflexivity |].
    destruct (fs_sb_ok_geom sb Hok) as (H1 & H2 & H3 & _). lia.
  Qed.

  (* --- W6, per REACHABLE dir: the [fs_dir_ok] bundle ------------------- *)

  Lemma fs_dir_ok_agree (i : Z) (dn : dinode) :
    fs_inode_dok P sb dn ->
    fs_dir_ok P sb i dn -> fs_dir_ok P' sb i dn.
  Proof.
    intros Hio H.
    destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & Hn1 & Hn16 & _).
    pose proof (fs_live_win_agree dn Hio) as Hwin.
    destruct H as [Hgr Hent Huq Hdot Hdd].
    constructor.
    - exact Hgr.
    - intros k Hk Hlive'.
      assert (Hlive : dir_live (fs_data_of P dn) k).
      { unfold dir_live in *.
        rewrite (dir_inum_agree _ _ k (Hwin k Hk)) in Hlive'. exact Hlive'. }
      destruct (Hent k Hk Hlive) as [Hran Hty].
      rewrite (dir_inum_agree _ _ k (Hwin k Hk)).
      split; [exact Hran |].
      rewrite (fs_dinode_agree P P' sb
                 (bv_unsigned (dir_inum (fs_data_of P dn) k)) Hok Hag
                 ltac:(lia)).
      exact Hty.
    - exact (dir_names_unique_agree _ _ _ Hwin Huq).
    - rewrite (dir_view_agree _ _ _ Hwin). exact Hdot.
    - rewrite (dir_view_agree _ _ _ Hwin). exact Hdd.
  Qed.

  (* --- W7 ------------------------------------------------------------- *)

  Lemma fs_root_wf_agree :
    fs_inodes_dwf P sb = true ->
    fs_root_wf P sb = true -> fs_root_wf P' sb = true.
  Proof.
    intros HW3 H.
    destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & Hn1 & Hn16 & _).
    assert (Hdn : fs_dinode P' sb ROOTINO = fs_dinode P sb ROOTINO)
      by (apply (fs_dinode_agree P P' sb ROOTINO Hok Hag);
          unfold ROOTINO; lia).
    unfold fs_root_wf in *. cbv zeta in *. rewrite Hdn.
    rewrite andb_true_iff in H. destruct H as [Hty Hdd].
    rewrite andb_true_iff. split; [exact Hty |].
    assert (Hio : fs_inode_dok P sb (fs_dinode P sb ROOTINO)).
    { apply (fs_inodes_dwf_spec P sb ROOTINO HW3);
        [unfold ROOTINO; lia |].
      rewrite (proj1 (Z.eqb_eq _ _) Hty). unfold T_DIR_z. lia. }
    pose proof (fs_live_win_agree _ Hio) as Hwin.
    rewrite (dir_first_agree _ _ _ DOTDOT Hwin).
    destruct (dir_first (fs_data_of P (fs_dinode P sb ROOTINO))
                (dir_nrec (bv_unsigned (di_size (fs_dinode P sb ROOTINO))))
                DOTDOT) as [k|] eqn:Hf; [| exact Hdd].
    rewrite (dir_inum_agree _ _ k (Hwin k (dir_first_lt _ _ _ _ Hf))).
    exact Hdd.
  Qed.

  (* --- W8 ------------------------------------------------------------- *)

  Lemma fs_dots_wf_agree (self : Z) (dn : dinode) :
    fs_inode_dok P sb dn ->
    fs_dots_wf P self dn = true -> fs_dots_wf P' self dn = true.
  Proof.
    intros Hio H.
    assert (Hwin : forall r : nat, (r < 2)%nat ->
              dir_win_agree (fs_data_of P dn) (fs_data_of P' dn) r).
    { intros r Hr.
      apply (dir_win_agree_blocks _ _ FS_MAXFILE);
        [exact (fs_live_data_agree dn Hio) |].
      unfold FS_MAXFILE, BSIZE. lia. }
    unfold fs_dots_wf in *. cbv zeta in *.
    rewrite (dir_liveb_agree _ _ 0%nat (Hwin 0%nat ltac:(lia))).
    rewrite (dir_liveb_agree _ _ 1%nat (Hwin 1%nat ltac:(lia))).
    rewrite (dir_inum_agree _ _ 0%nat (Hwin 0%nat ltac:(lia))).
    rewrite (dir_bname_agree' _ _ 0%nat (Hwin 0%nat ltac:(lia))).
    rewrite (dir_bname_agree' _ _ 1%nat (Hwin 1%nat ltac:(lia))).
    exact H.
  Qed.

  Lemma fs_dots_all_agree :
    fs_inodes_dwf P sb = true ->
    fs_dots_all P sb = true -> fs_dots_all P' sb = true.
  Proof.
    intros HW3 H.
    destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & Hn1 & Hn16 & _).
    unfold fs_dots_all.
    rewrite List.forallb_forall. intros x Hin.
    apply elem_of_list_In, elem_of_seq in Hin.
    cbv beta zeta.
    rewrite (fs_dinode_agree P P' sb (Z.of_nat x) Hok Hag ltac:(lia)).
    destruct (bv_unsigned (di_type (fs_dinode P sb (Z.of_nat x)))
              =? T_DIR_z) eqn:Ety; [| reflexivity].
    apply fs_dots_wf_agree.
    - apply (fs_inodes_dwf_spec P sb (Z.of_nat x) HW3 ltac:(lia)).
      rewrite (proj1 (Z.eqb_eq _ _) Ety). unfold T_DIR_z. lia.
    - pose proof (forallb_seq _ _ x H ltac:(lia)) as Hx.
      cbv beta zeta in Hx. rewrite Ety in Hx. exact Hx.
  Qed.

  (* --- the region sweep ------------------------------------------------ *)

  Lemma fs_region_wf_agree (nib : nat) :
    16 * Z.of_nat nib <= 16 * (sb_ninodes sb / 16 + 1) ->
    fs_region_wf P sb nib = true -> fs_region_wf P' sb nib = true.
  Proof.
    intros Hnib H. unfold fs_region_wf in *.
    rewrite andb_true_iff in H. destruct H as [Hf Hn].
    rewrite andb_true_iff. split.
    - unfold fs_region_free.
      rewrite List.forallb_forall. intros x Hin.
      apply elem_of_list_In, elem_of_seq in Hin.
      cbv beta zeta.
      rewrite (fs_dinode_agree P P' sb (Z.of_nat x) Hok Hag ltac:(lia)).
      pose proof (forallb_seq _ _ x Hf ltac:(lia)) as Hx.
      cbv beta zeta in Hx. exact Hx.
    - unfold fs_region_nlink.
      rewrite List.forallb_forall. intros x Hin.
      apply elem_of_list_In, elem_of_seq in Hin.
      cbv beta zeta.
      rewrite (fs_dinode_agree P P' sb (Z.of_nat x) Hok Hag ltac:(lia)).
      pose proof (forallb_seq _ _ x Hn ltac:(lia)) as Hx.
      cbv beta zeta in Hx. exact Hx.
  Qed.

  (* --- the tree -------------------------------------------------------- *)

  Lemma node_at_agree (i : Z) :
    fs_inodes_dwf P sb = true -> 0 <= i < sb_ninodes sb ->
    node_at P' sb i = node_at P sb i.
  Proof.
    intros HW3 Hi.
    destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & _ & Hn16 & _).
    unfold node_at. cbv zeta.
    rewrite (fs_dinode_agree P P' sb i Hok Hag ltac:(lia)).
    destruct (bv_unsigned (di_type (fs_dinode P sb i)) =? 0) eqn:Ety;
      [reflexivity |].
    f_equal.
    assert (Hio : fs_inode_dok P sb (fs_dinode P sb i))
      by (apply (fs_inodes_dwf_spec P sb i HW3 Hi), Z.eqb_neq, Ety).
    pose proof (fdi_size _ _ _ Hio) as Hsz.
    pose proof (proj1 (bv_unsigned_in_range _
                         (di_size (fs_dinode P sb i)))) as Hsz0.
    destruct (dir_nrec_bound (bv_unsigned (di_size (fs_dinode P sb i)))
                Hsz0 Hsz) as [Hnr Hszb].
    apply (node_of_agree _ _ _ FS_MAXFILE);
      [exact (fs_live_data_agree _ Hio) | exact Hnr | exact Hszb].
  Qed.

  Lemma tree_of_disk_agree :
    fs_inodes_dwf P sb = true ->
    tree_of_disk P' sb = tree_of_disk P sb.
  Proof.
    intros HW3. unfold tree_of_disk. f_equal.
    destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & Hn1 & _).
    assert (Hup : forall n : nat, Z.of_nat n <= sb_ninodes sb ->
              fs_nodes_upto P' sb n = fs_nodes_upto P sb n).
    { induction n as [| m IH]; intros Hn; [reflexivity |].
      cbn [fs_nodes_upto].
      rewrite (node_at_agree (Z.of_nat m) HW3 ltac:(lia)).
      rewrite IH by lia. reflexivity. }
    apply Hup. rewrite Z2Nat.id; lia.
  Qed.

  (* --- the ticket supply ----------------------------------------------- *)

  Lemma fs_dir_tickets_agree (self : Z) (dn : dinode) :
    fs_inode_dok P sb dn ->
    fs_dir_tickets P' self dn = fs_dir_tickets P self dn.
  Proof.
    intros Hio.
    pose proof (fs_live_win_agree dn Hio) as Hwin.
    unfold fs_dir_tickets. apply omap_ext_in.
    intros k Hk. apply elem_of_seq in Hk.
    unfold fs_rec_ticket. cbv zeta.
    rewrite (dir_liveb_agree _ _ k (Hwin k ltac:(lia))).
    rewrite (dir_inum_agree _ _ k (Hwin k ltac:(lia))).
    reflexivity.
  Qed.

  Lemma fs_dir_tickets_at_agree (z : Z) :
    fs_inodes_dwf P sb = true -> 0 <= z < sb_ninodes sb ->
    fs_dir_tickets_at P' sb z = fs_dir_tickets_at P sb z.
  Proof.
    intros HW3 Hz.
    destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & _ & Hn16 & _).
    unfold fs_dir_tickets_at. cbv zeta.
    rewrite (fs_dinode_agree P P' sb z Hok Hag ltac:(lia)).
    destruct (bv_unsigned (di_type (fs_dinode P sb z)) =? T_DIR_z)
      eqn:Ety; [| reflexivity].
    apply fs_dir_tickets_agree.
    apply (fs_inodes_dwf_spec P sb z HW3 Hz).
    rewrite (proj1 (Z.eqb_eq _ _) Ety). unfold T_DIR_z. lia.
  Qed.

  Lemma fs_rtickets_agree (rd : gset Z) :
    fs_inodes_dwf P sb = true ->
    fs_rtickets P' sb rd = fs_rtickets P sb rd.
  Proof.
    intros HW3. unfold fs_rtickets. f_equal. apply list_fmap_ext.
    intros idx x Hx. apply lookup_seq in Hx as [-> Hx]. cbv beta.
    destruct (bool_decide (Z.of_nat (0 + idx) ∈ rd)); [| reflexivity].
    apply fs_dir_tickets_at_agree; [exact HW3 | lia].
  Qed.

End sweep_agree.

(* ====================================================================== *)
(*  8.  THE VIEW TRANSFER AND THE [gmap] BODY                              *)
(* ====================================================================== *)

(* THE ONE FOOTPRINT FACT, packaged: the durable sweeps read block 1 and
   the range [inodestart, size) and NOTHING else, so any view agreeing
   there satisfies them alike.  This is what lets the committed view of a
   disk (which lacks the boot block and the log region) inherit the
   sweeps from the disk. *)
Lemma fs_durable_wf_view_ext (P P' : Z -> list (bv 8)) (sb : fs_sb) :
  fs_parse_sb P = Some sb ->
  (forall b : Z, b = SB_BNO \/ sb_inodestart sb <= b < sb_size sb ->
     P' b = P b) ->
  fs_durable_wf_view P -> fs_durable_wf_view P'.
Proof.
  intros Hp Hag2 (sb' & Hp' & Hsw).
  assert (Hsbeq : sb' = sb) by congruence. subst sb'.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hreg HW9].
  pose proof (fs_sb_wf_ok sb Hsb) as Hok.
  assert (Hag : forall b : Z,
            sb_inodestart sb <= b < sb_size sb -> P' b = P b)
    by (intros b Hb; apply Hag2; right; exact Hb).
  destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & Hn1 & Hn16 & _).
  exists sb. split.
  { rewrite (fs_parse_sb_ext P P')
      by (apply Hag2; left; reflexivity). exact Hp. }
  constructor.
  - exact Hsb.
  - exact (fs_inodes_dwf_agree P P' sb Hok Hag HW3).
  - destruct HW45 as (u & Hu & Hbm). exists u. split.
    + rewrite (fs_used_set_agree P P' sb Hok Hag HW3). exact Hu.
    + rewrite (fs_bitmap_wf_agree P P' sb Hok Hag u). exact Hbm.
  - exact (fs_root_wf_agree P P' sb Hok Hag HW3 HW7).
  - exact (fs_dots_all_agree P P' sb Hok Hag HW3 HW8).
  - destruct Hreg as (nib & Hnib & Hrw). exists nib.
    split; [exact Hnib |].
    apply (fs_region_wf_agree P P' sb Hok Hag nib); [lia | exact Hrw].
  - destruct HW9 as (rd & Hrd & Hdok & Hlk & Horph). exists rd.
    assert (Htree : tree_of_disk P' sb = tree_of_disk P sb)
      by (apply (tree_of_disk_agree P P' sb Hok Hag HW3)).
    assert (Hticks : fs_rtickets P' sb rd = fs_rtickets P sb rd)
      by (apply (fs_rtickets_agree P P' sb Hok Hag rd HW3)).
    split; [| split; [| split]].
    + (* fs_rdirs *)
      intros z. rewrite (Hrd z). split.
      * intros (Hz & Hty & Hreach). split; [exact Hz |]. split.
        -- rewrite (fs_dinode_agree P P' sb z Hok Hag ltac:(lia)).
           exact Hty.
        -- unfold fs_reachable in *. rewrite Htree. exact Hreach.
      * intros (Hz & Hty & Hreach). split; [exact Hz |]. split.
        -- rewrite (fs_dinode_agree P P' sb z Hok Hag ltac:(lia)) in Hty.
           exact Hty.
        -- unfold fs_reachable in *. rewrite Htree in Hreach. exact Hreach.
    + (* the per-reachable-dir bundle *)
      intros z Hin.
      destruct (proj1 (Hrd z) Hin) as (Hz & Hty & _).
      assert (Hio : fs_inode_dok P sb (fs_dinode P sb z)).
      { apply (fs_inodes_dwf_spec P sb z HW3 Hz).
        rewrite Hty. unfold T_DIR_z. lia. }
      rewrite (fs_dinode_agree P P' sb z Hok Hag ltac:(lia)).
      exact (fs_dir_ok_agree P P' sb Hok Hag z _ Hio (Hdok z Hin)).
    + (* fs_links_gen *)
      intros z Hz. cbv zeta.
      rewrite (fs_dinode_agree P P' sb z Hok Hag ltac:(lia)).
      intros Hty. unfold fs_rtick. rewrite Hticks.
      exact (Hlk z Hz Hty).
    + (* fs_orphans_empty *)
      intros z Hz Hty Hnin.
      rewrite (fs_dinode_agree P P' sb z Hok Hag ltac:(lia)) in Hty.
      assert (Hio : fs_inode_dok P sb (fs_dinode P sb z)).
      { apply (fs_inodes_dwf_spec P sb z HW3 Hz).
        rewrite Hty. unfold T_DIR_z. lia. }
      pose proof (fs_live_win_agree P P' sb Hok Hag _ Hio) as Hwin.
      unfold fs_dir_dots_only.
      rewrite (fs_dinode_agree P P' sb z Hok Hag ltac:(lia)).
      intros k Hk2 Hkn Hlive'.
      apply (Horph z Hz Hty Hnin k Hk2 Hkn).
      unfold dir_live in *.
      rewrite (dir_inum_agree _ _ k (Hwin k Hkn)) in Hlive'.
      exact Hlive'.
Qed.

(* the [gmap] body, from any total view the map covers on the footprint *)
Lemma fs_durable_wf_body_of_view (P : Z -> list (bv 8)) (sb : fs_sb)
    (D : gmap Z (list (bv 8))) :
  fs_parse_sb P = Some sb ->
  (forall b : Z, b = SB_BNO \/ sb_inodestart sb <= b < sb_size sb ->
     D !! b = Some (P b)) ->
  fs_durable_wf_view P -> fs_durable_wf_body D.
Proof.
  intros Hp HD Hv. unfold fs_durable_wf_body.
  apply (fs_durable_wf_view_ext P (dv_of_D D) sb Hp); [| exact Hv].
  intros b Hb. unfold dv_of_D. rewrite (HD b Hb). reflexivity.
Qed.

(* ====================================================================== *)
(*  9.  THE IMAGE DISCHARGE, VIEW LEVEL                                    *)
(*                                                                        *)
(*  Under [fsimg_wf], W9's mkfs pin forces every directory to BE the       *)
(*  root, so the reachable-directory set is {[ROOTINO]} outright, the      *)
(*  filtered ticket supply IS the full supply, and the general link        *)
(*  clause collapses to [fs_links_eq] (files) + W9's own root pair         *)
(*  (the root's count is zero -- all its tickets would be self-tickets     *)
(*  -- and its [nlink] is one = 0 + the root bonus).  The restriction to   *)
(*  the committed view [fs_restrict P (fs_home_set cov ls)] is the         *)
(*  [gmap]-level corollary in [FsWfImg.v] (it needs [FsCrash]'s            *)
(*  vocabulary, which sits ABOVE this file).                               *)
(* ====================================================================== *)

(* no ticket of a directory names its own home -- [fs_rec_ticket]'s self
   exemption, read back *)
Lemma fs_dir_tickets_self (P : Z -> list (bv 8)) (self : Z) (dn : dinode)
    (t : Z) :
  t ∈ fs_dir_tickets P self dn -> t <> self.
Proof.
  unfold fs_dir_tickets. intros Ht Heq. subst t.
  apply elem_of_list_omap in Ht as (k & _ & Hk).
  unfold fs_rec_ticket in Hk. cbv zeta in Hk.
  destruct (dir_liveb (fs_data_of P dn) k
            && negb (bool_decide
                       (bv_unsigned (dir_inum (fs_data_of P dn) k)
                        = self))) eqn:Hg; [| discriminate].
  injection Hk as Hk.
  apply andb_true_iff in Hg as [_ Hg].
  apply negb_true_iff, bool_decide_eq_false in Hg.
  exact (Hg Hk).
Qed.

(* the boolean conjuncts of [fsimg_wf] that have no standalone projection *)
Local Lemma fsimg_wf_split (P : Z -> list (bv 8)) (sb : fs_sb) :
  fsimg_wf P sb = true ->
  fs_sb_wf sb = true /\ fs_inodes_wf P sb = true
  /\ fs_root_wf P sb = true /\ fs_dots_all P sb = true.
Proof. unfold fsimg_wf. rewrite !andb_true_iff. tauto. Qed.

Lemma fsimg_durable_wf_view (P : Z -> list (bv 8)) (sb : fs_sb)
    (nib : nat) :
  fs_parse_sb P = Some sb ->
  fsimg_wf P sb = true ->
  fs_links_eq P sb = true ->
  fs_region_wf P sb nib = true ->
  Z.of_nat nib = sb_ninodes sb / 16 + 1 ->
  fs_durable_wf_view P.
Proof.
  intros Hp Hwf Hle Hrw Hnib.
  destruct (fsimg_wf_split P sb Hwf) as (Hsb & HW3 & HW7 & HW8).
  pose proof (fs_sb_wf_ok sb Hsb) as Hok.
  destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & Hn1 & _).
  exists sb. split; [exact Hp |]. constructor.
  - exact Hsb.
  - exact (fs_inodes_wf_dwf P sb HW3).
  - destruct (fsimg_wf_used P sb Hwf) as (u & Hu & _ & Hbm).
    exists u. split; [exact Hu | exact Hbm].
  - exact HW7.
  - exact HW8.
  - exists nib. split; [exact Hnib | exact Hrw].
  - exists ({[ROOTINO]} : gset Z).
    (* mkfs's one directory makes the filtered supply THE supply *)
    assert (Hsup : fs_rtickets P sb {[ROOTINO]} = fs_all_tickets P sb).
    { unfold fs_rtickets, fs_all_tickets. f_equal. apply list_fmap_ext.
      intros idx x Hx. apply lookup_seq in Hx as [-> Hx]. cbv beta.
      case_bool_decide as Hin; [reflexivity |].
      unfold fs_dir_tickets_at. cbv zeta.
      destruct (bv_unsigned (di_type (fs_dinode P sb (Z.of_nat (0 + idx))))
                =? T_DIR_z) eqn:Ety; [| reflexivity].
      exfalso. apply Hin. apply elem_of_singleton.
      apply (fsimg_wf_dir_root P sb _ Hwf); [lia |].
      apply Z.eqb_eq. exact Ety. }
    assert (Hroot0 : fs_rtick P sb {[ROOTINO]} ROOTINO = 0%nat).
    { unfold fs_rtick. apply fs_tick_count_zero.
      intros t Ht Heq. subst t.
      unfold fs_rtickets in Ht.
      apply elem_of_list_join in Ht as (l & Hl & Hls).
      apply elem_of_list_fmap in Hls as (idx & -> & _).
      revert Hl. cbv beta. case_bool_decide as Hin;
        [| intros Hl; by apply elem_of_nil in Hl].
      apply elem_of_singleton in Hin. rewrite Hin.
      unfold fs_dir_tickets_at. cbv zeta.
      destruct (bv_unsigned (di_type (fs_dinode P sb ROOTINO)) =? T_DIR_z);
        [| intros Hl; by apply elem_of_nil in Hl].
      intros Hl.
      exact (fs_dir_tickets_self P ROOTINO _ ROOTINO Hl eq_refl). }
    split; [| split; [| split]].
    + (* fs_rdirs at {[ROOTINO]} *)
      intros z. rewrite elem_of_singleton. split.
      * intros ->. split; [unfold ROOTINO; lia |]. split.
        -- exact (fs_root_wf_type P sb HW7).
        -- exists ([] : list fname). apply path_at_nil.
      * intros (Hz & Hty & _).
        exact (fsimg_wf_dir_root P sb z Hwf Hz Hty).
    + (* the per-reachable-dir bundle: the root's own W6 reading *)
      intros z Hin. apply elem_of_singleton in Hin. subst z.
      apply (fsimg_wf_dir P sb ROOTINO Hwf); [unfold ROOTINO in *; lia |].
      exact (fs_root_wf_type P sb HW7).
    + (* fs_links_gen at {[ROOTINO]} *)
      intros z Hz. cbv zeta. intros Hty.
      destruct (decide (bv_unsigned (di_type (fs_dinode P sb z))
                        = T_DIR_z)) as [Hd | Hnd].
      * pose proof (fsimg_wf_dir_root P sb z Hwf Hz Hd) as Hzr.
        subst z.
        rewrite (bool_decide_eq_true_2 _ Hd).
        rewrite (bool_decide_eq_true_2 (ROOTINO = ROOTINO) eq_refl).
        rewrite Hroot0.
        rewrite (fsimg_wf_dir_nlink P sb ROOTINO Hwf Hz Hd).
        reflexivity.
      * rewrite (bool_decide_eq_false_2 _ Hnd).
        rewrite (fs_links_eq_at P sb z Hle Hz Hty Hnd).
        unfold fs_rtick. rewrite Hsup. unfold fs_link_count.
        cbv iota. lia.
    + (* fs_orphans_empty at {[ROOTINO]}: there are no orphan dirs *)
      intros z Hz Hty Hnin. exfalso. apply Hnin.
      apply elem_of_singleton.
      exact (fsimg_wf_dir_root P sb z Hwf Hz Hty).
Qed.
