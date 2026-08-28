(* ====================================================================== *)
(*  FsDurSyscall.v -- THE PER-SYSCALL DURABILITY READINGS                  *)
(*  (fs-syscall-specs lane D; claude-notes/design/fs-syscall-specs.md      *)
(*   section 5 principle 3, claude-notes/design/durable-fs-plan.md         *)
(*   section 5's spike and section 8 (the state is DETERMINED by the map)  *)
(*                                                                        *)
(*  WHAT THIS FILE IS.  After a group commit, [FsCrash.fs_commit_receipt]  *)
(*  says the machine would recover to a map [D] and that [D] IS a file     *)
(*  system: [exists S, snap_ok S D].  Every per-syscall durability claim   *)
(*  -- the created node is in the durable table, the entry is gone from   *)
(*  the parent's durable row, the file's durable bytes are the written    *)
(*  value -- is a READING of that one sentence.  Nothing here is           *)
(*  an invariant, a resource or a ghost: every declaration is PURE, hence  *)
(*  persistent, which is what section 5 principle 3 asks a [dur_at]        *)
(*  certificate to be.                                                     *)
(*                                                                        *)
(*  WHY THE EXISTENTIAL [S] COSTS NOTHING, and why that is the whole       *)
(*  content.  The commit's receipt cannot NAME the file-system state its   *)
(*  batch produced -- [FsCollectAll.fs_collect_mint] closes [S]            *)
(*  existentially at the collection, and the WAL has no vocabulary for an  *)
(*  abstract state anyway.  So a durability claim phrased as -- the state  *)
(*  the transaction built has [i] at [n] -- would be unstatable at the     *)
(*  receipt.                                                               *)
(*  It does not need to be: [snap_ok] pins the state to the LAST BIT       *)
(*  against [D] at every inum the region names, so the snapshot's table is *)
(*  a FUNCTION of the recovered map.  That is [snap_node_det] below --     *)
(*  durable-fs-plan.md section 8's claim, discharged -- and it turns every *)
(*  per-node fact into a fact about [D] alone:                             *)
(*                                                                        *)
(*      [dur_node D i n]  :=  forall S, snap_ok S D -> S's table has i |-> n *)
(*                                                                        *)
(*  which is produced from RECOVERED BYTES ([dur_node_of_rec]) and read    *)
(*  back to recovered bytes ([dur_node_rec_at], [dur_data]).  A syscall    *)
(*  proof that knows what its transaction left in the logged view -- which *)
(*  IS the committed [D] ([LogSnapLaw], [FsCollectAll.fs_snap_law_build])  *)
(*  -- gets its durability statement with no knowledge of batches, ghosts  *)
(*  or the collection.                                                     *)
(*                                                                        *)
(*  THE THREE SYSCALL THEOREMS are section 3: [mknod_durable] (the         *)
(*  spike of durable-fs-plan.md section 5), [unlink_durable],              *)
(*  [write_durable].  Each is stated at an ARBITRARY [S] with              *)
(*  [snap_ok S D], i.e. at whichever snapshot the receipt happens to name, *)
(*  so no consumer ever has to identify one.                               *)
(*                                                                        *)
(*  WHAT IS DELIBERATELY NOT HERE.  No batch index and no [flushed b]:     *)
(*  the BOUND is section 5 principle 2 and rides the crash predicate's     *)
(*  epoch pointer (campaign lane Y, gated on durable lane F).  No          *)
(*  [abs_of]/[aview]: the abstract carrier is lane A's, and these readings *)
(*  are stated at [FsNode.fs_node] so that lane A can quotient them        *)
(*  afterwards without restating anything.                                 *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var mono_nat.

(* the crash predicate and the adequacy-level pure projection: the two
   PRODUCERS of [snap_holds] (section 4).  They come first so that the
   file-system stack's own names -- [fs_view], [byte_range], [blk_owned],
   [link_auth] and friends -- win over the block layer's twins that arrive
   through them (durable-notes.md, "AND WHERE THAT IMPORT COLLIDES, PUT IT
   EARLY"). *)
Require Import RiscvPtsto.      (* [riscvEraGS], [log_mirror] -- IMPORTED,
                                   since a class named in a backtick binder
                                   without its home file in scope silently
                                   becomes a VARIABLE                     *)
Require Import DiskImg.         (* [diskImgG]                             *)
Require Import Xv6Cameras.      (* [fsCrashG], [lockG], [fsLinkG],
                                   [fsTopG]                              *)
Require Import SystemAdequacy.  (* [fs_boot_pure]                         *)
Require Import FsCrash.         (* [P_fs], [fs_commit_receipt],
                                   [fs_recovery], [fs_blocks]             *)

Require Import BioDefs.         (* [BSIZE]                                *)
Require Import BlockWords.      (* [ind_bytes]                            *)
Require Import DinodeEnc.       (* [dinode], [dinode_wf]                  *)
Require Import InodeDefs.       (* [file_byte]                            *)
Require Import DirView.         (* [dir_first], [dir_match], [dir_inum]   *)
Require Import FsTree.           (* [fname], [dir_view], [file_bytes]      *)
Require Import FsImg.           (* [SB_BNO], [fs_parse_sb], [FS_MAXFILE]  *)
Require Import FsDurSnap.       (* [snap_ok] and its clauses; re-exports
                                   [FsState] -> [FsStateInode] -> [FsNode] *)

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE VOCABULARY (design section 5's certificates, as pure facts)    *)
(* ====================================================================== *)

(* WHAT A COMMIT LEAVES BEHIND, as one word.  It is exactly the last
   conjunct of [SystemAdequacy.fs_boot_pure] and exactly what
   [FsCrash.fs_commit_receipt] concludes; section 4 has both readings. *)
Definition snap_holds (D : gmap Z (list (bv 8))) : Prop :=
  exists S : fs_state_rec, snap_ok S D.

(* THE PER-OBJECT CERTIFICATES.  Each says what EVERY snapshot state over
   the committed map says -- which, by section 2's determinism, is what THE
   snapshot state says.  Both are [Prop]s, hence persistent and freely
   duplicable: design section 5 principle 3 asks for exactly that, and the
   snapshot itself is not persistent (its link family has no core), so a
   certificate must be a copy of the PURE tie and never a share of it. *)
Definition dur_sb (D : gmap Z (list (bv 8))) (sb : fs_sb) : Prop :=
  forall S : fs_state_rec, snap_ok S D -> fss_sb S = sb.

Definition dur_node (D : gmap Z (list (bv 8))) (i : Z) (n : fs_node) : Prop :=
  forall S : fs_state_rec, snap_ok S D -> fss_inodes S !! i = Some n.

(* the two addresses a record lives at, spelled once.  [sk_rec] states the
   tie at exactly this block and this offset. *)
Definition rec_bno (sb : fs_sb) (i : Z) : Z := sb_inodestart sb + i `div` 16.
Definition rec_off (i : Z) : Z := 64 * (i `mod` 16).

(* ====================================================================== *)
(*  2.  THE SNAPSHOT IS A FUNCTION OF THE COMMITTED MAP                    *)
(*                                                                        *)
(*  durable-fs-plan.md section 8: THE STATE IS DETERMINED BY THE MAP,       *)
(*  which is why the existential [S] here loses nothing.  The three       *)
(*  encoders are injective ([rec_in_blk_inj], [ind_bytes_inj], the         *)
(*  superblock's parse is a function), and the per-inode local clauses     *)
(*  pin everything the encoders do not reach: [inl_ind_zero] fixes the     *)
(*  entry array at a node with no indirect block, [inl_blk_dom] /          *)
(*  [inl_blk_top] fix WHICH slots a node holds, and [sk_blk] fixes their   *)
(*  contents.                                                             *)
(* ====================================================================== *)

Lemma snap_sb_det (S S' : fs_state_rec) (D : gmap Z (list (bv 8))) :
  snap_bytes S D -> snap_bytes S' D ->
  fss_sbb S = fss_sbb S' /\ fss_sb S = fss_sb S'.
Proof.
  intros Hb Hb'.
  assert (Hsbb : fss_sbb S = fss_sbb S').
  { pose proof (sk_sb Hb) as H1. pose proof (sk_sb Hb') as H2. congruence. }
  split; [exact Hsbb |].
  pose proof (sk_parse Hb) as H1. pose proof (sk_parse Hb') as H2.
  rewrite Hsbb in H1. congruence.
Qed.

(* THE HEADLINE OF THIS SECTION: one inum, one map, one node. *)
Lemma snap_node_det (S S' : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n n' : fs_node) :
  snap_ok S D -> snap_ok S' D ->
  fss_inodes S !! i = Some n -> fss_inodes S' !! i = Some n' ->
  n = n'.
Proof.
  intros Hs Hs' Hi Hi'.
  pose proof (sk_bytes Hs) as Hb. pose proof (sk_bytes Hs') as Hb'.
  pose proof (sk_local Hs i n Hi) as Hl.
  pose proof (sk_local Hs' i n' Hi') as Hl'.
  destruct (snap_sb_det S S' D Hb Hb') as [_ Hsb].
  (* ---- the record: same block, same offset, injective encoder ---- *)
  destruct (sk_rec Hb i n Hi) as (bs & Hbs & Hrec).
  destruct (sk_rec Hb' i n' Hi') as (bs' & Hbs' & Hrec').
  rewrite <- Hsb in Hbs'.
  assert (Hbb : bs' = bs) by congruence. subst bs'.
  assert (Hr : fn_rec n = fn_rec n').
  { exact (rec_in_blk_inj bs (64 * (i `mod` 16)) (fn_rec n) (fn_rec n')
             (inl_rec_wf Hl) (inl_rec_wf Hl') Hrec Hrec'). }
  (* ---- the entry array: off the record's own indirect address ---- *)
  assert (Hind : fn_indb n = fn_indb n').
  { unfold fn_indb. rewrite Hr. reflexivity. }
  assert (He : fn_ent n = fn_ent n').
  { destruct (decide (fn_indb n = 0)) as [Hz | Hnz].
    - assert (Hz' : fn_indb n' = 0) by (rewrite <- Hind; exact Hz).
      rewrite (inl_ind_zero Hl Hz) (inl_ind_zero Hl' Hz'). reflexivity.
    - assert (Hnz' : fn_indb n' <> 0) by (rewrite <- Hind; exact Hnz).
      pose proof (sk_ind Hb i n Hi Hnz) as H1.
      pose proof (sk_ind Hb' i n' Hi' Hnz') as H2.
      rewrite <- Hind in H2.
      assert (Hib : ind_bytes (fn_ent n) = ind_bytes (fn_ent n')) by congruence.
      apply ind_bytes_inj; [| exact Hib].
      rewrite (inl_ent_len Hl) (inl_ent_len Hl'). reflexivity. }
  (* ---- hence every slot address ---- *)
  assert (Ha : forall k : nat, fn_naddr n k = fn_naddr n' k).
  { intros k. unfold fn_naddr. rewrite Hr He. reflexivity. }
  (* ---- hence the block map: domain by the local clauses, values by D --- *)
  assert (Hbk : fn_blk n = fn_blk n').
  { apply map_eq. intros k.
    destruct (decide (k < FS_MAXFILE)%nat) as [Hk | Hk].
    - destruct (fn_blk n !! k) as [x |] eqn:E1;
        destruct (fn_blk n' !! k) as [y |] eqn:E2.
      + pose proof (sk_blk Hb i n k x Hi E1) as G1.
        pose proof (sk_blk Hb' i n' k y Hi' E2) as G2.
        rewrite <- (Ha k) in G2. congruence.
      + exfalso.
        assert (Hnz : fn_naddr n k <> 0).
        { apply (proj1 (inl_blk_dom Hl k Hk)). exists x. exact E1. }
        assert (Hnz' : fn_naddr n' k <> 0) by (rewrite <- (Ha k); exact Hnz).
        destruct (proj2 (inl_blk_dom Hl' k Hk) Hnz') as [y Hy].
        rewrite Hy in E2. discriminate.
      + exfalso.
        assert (Hnz' : fn_naddr n' k <> 0).
        { apply (proj1 (inl_blk_dom Hl' k Hk)). exists y. exact E2. }
        assert (Hnz : fn_naddr n k <> 0) by (rewrite (Ha k); exact Hnz').
        destruct (proj2 (inl_blk_dom Hl k Hk) Hnz) as [x Hx].
        rewrite Hx in E1. discriminate.
      + reflexivity.
    - assert (Hk' : (FS_MAXFILE <= k)%nat) by lia.
      rewrite (inl_blk_top Hl k Hk') (inl_blk_top Hl' k Hk'). reflexivity. }
  destruct n as [r e b]; destruct n' as [r' e' b'].
  f_equal; [exact Hr | exact He | exact Hbk].
Qed.

(* ...and the certificate is therefore unambiguous *)
Lemma dur_node_agree (D : gmap Z (list (bv 8))) (i : Z) (n n' : fs_node) :
  snap_holds D -> dur_node D i n -> dur_node D i n' -> n = n'.
Proof.
  intros [S HS] H1 H2.
  pose proof (H1 S HS) as G1. pose proof (H2 S HS) as G2. congruence.
Qed.

Lemma dur_sb_agree (D : gmap Z (list (bv 8))) (sb sb' : fs_sb) :
  snap_holds D -> dur_sb D sb -> dur_sb D sb' -> sb = sb'.
Proof.
  intros [S HS] H1 H2.
  pose proof (H1 S HS) as G1. pose proof (H2 S HS) as G2. congruence.
Qed.

(* ====================================================================== *)
(*  3.  THE PRODUCERS AND READERS: recovered bytes <-> the durable table   *)
(* ====================================================================== *)

(* THE SUPERBLOCK, off block 1's recovered bytes.  It takes no [snap_holds]:
   every snapshot over [D] parses the SAME block 1, so the certificate is
   about the map alone. *)
Lemma dur_sb_of_bytes (D : gmap Z (list (bv 8))) (sbb : list (bv 8))
    (sb : fs_sb) :
  D !! SB_BNO = Some sbb ->
  fs_parse_sb (fun _ => sbb) = Some sb ->
  dur_sb D sb.
Proof.
  intros Hd Hp S HS.
  pose proof (sk_sb (sk_bytes HS)) as H1.
  assert (Hsbb : fss_sbb S = sbb) by congruence.
  pose proof (sk_parse (sk_bytes HS)) as H2.
  rewrite Hsbb in H2. congruence.
Qed.

Lemma dur_sb_exists (D : gmap Z (list (bv 8))) :
  snap_holds D -> exists sb : fs_sb, dur_sb D sb.
Proof.
  intros [S HS]. exists (fss_sb S). intros S' HS'.
  destruct (snap_sb_det S' S D (sk_bytes HS') (sk_bytes HS)) as [_ H].
  exact H.
Qed.

(* THE NODE, off its RECORD's recovered bytes.  This is the producer a
   syscall proof calls: it knows the 64 bytes its transaction left in the
   inum's slot, and gets back the durable table's entry at that inum. *)
Lemma dur_node_of_rec (D : gmap Z (list (bv 8))) (sb : fs_sb) (i : Z)
    (bs : list (bv 8)) (d : dinode) :
  snap_holds D -> dur_sb D sb ->
  0 <= i < 16 * (sb_ninodes sb / 16 + 1) ->
  dinode_wf d ->
  D !! rec_bno sb i = Some bs ->
  rec_in_blk bs (rec_off i) d ->
  exists n : fs_node, dur_node D i n /\ fn_rec n = d.
Proof.
  intros [S0 HS0] Hsb Hran Hwf Hbs Hrec.
  unfold rec_bno, rec_off in *.
  assert (Hran0 : 0 <= i < 16 * (sb_ninodes (fss_sb S0) / 16 + 1)).
  { rewrite (Hsb S0 HS0). exact Hran. }
  destruct (sk_regdom (sk_bytes HS0) i Hran0) as [n Hn].
  assert (Hd : fn_rec n = d).
  { destruct (sk_rec (sk_bytes HS0) i n Hn) as (bs0 & Hbs0 & Hrec0).
    rewrite (Hsb S0 HS0) in Hbs0.
    assert (Hb0 : bs0 = bs) by congruence. subst bs0.
    exact (rec_in_blk_inj bs (64 * (i `mod` 16)) (fn_rec n) d
             (inl_rec_wf (sk_local HS0 i n Hn)) Hwf Hrec0 Hrec). }
  exists n. split; [| exact Hd].
  intros S HS.
  assert (HranS : 0 <= i < 16 * (sb_ninodes (fss_sb S) / 16 + 1)).
  { rewrite (Hsb S HS). exact Hran. }
  destruct (sk_regdom (sk_bytes HS) i HranS) as [n' Hn'].
  rewrite Hn'. f_equal.
  exact (snap_node_det S S0 D i n' n HS HS0 Hn' Hn).
Qed.

(* ...and the certificate off a snapshot one already holds.  This is the
   producer the COMMIT's own proof would use (it has a state in hand); the
   byte-level one above is what a syscall proof uses (it has bytes). *)
Lemma dur_node_of_snap (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) :
  snap_ok S D ->
  0 <= i < 16 * (sb_ninodes (fss_sb S) / 16 + 1) ->
  fss_inodes S !! i = Some n ->
  dur_node D i n.
Proof.
  intros HS Hran Hi S' HS'.
  destruct (snap_sb_det S' S D (sk_bytes HS') (sk_bytes HS)) as [_ Hsb].
  assert (Hran' : 0 <= i < 16 * (sb_ninodes (fss_sb S') / 16 + 1)).
  { rewrite Hsb. exact Hran. }
  destruct (sk_regdom (sk_bytes HS') i Hran') as [n' Hn'].
  rewrite Hn'. f_equal. exact (snap_node_det S' S D i n' n HS' HS Hn' Hi).
Qed.

(* ...and the reading back: a durable node's record IS on the recovered
   disk, at its own slot.  [sk_rec], with the block named through the
   superblock certificate rather than through [S]. *)
Lemma dur_node_rec_at (D : gmap Z (list (bv 8))) (sb : fs_sb) (i : Z)
    (n : fs_node) :
  snap_holds D -> dur_sb D sb -> dur_node D i n ->
  exists bs : list (bv 8),
    D !! rec_bno sb i = Some bs /\ rec_in_blk bs (rec_off i) (fn_rec n).
Proof.
  intros [S HS] Hsb Hd. unfold rec_bno, rec_off.
  destruct (sk_rec (sk_bytes HS) i n (Hd S HS)) as (bs & Hbs & Hrec).
  exists bs. rewrite <- (Hsb S HS). split; [exact Hbs | exact Hrec].
Qed.

(* the per-inode local clauses, at a durable node.  Everything a consumer
   wants to say about ONE node -- that its record is well formed, that its
   dots are where they should be, that a free record is bare -- is a
   projection of this. *)
Lemma dur_node_local (D : gmap Z (list (bv 8))) (i : Z) (n : fs_node) :
  snap_holds D -> dur_node D i n -> inode_local i n.
Proof. intros [S HS] Hd. exact (sk_local HS i n (Hd S HS)). Qed.

Lemma dur_node_bare (D : gmap Z (list (bv 8))) (i : Z) (n : fs_node) :
  snap_holds D -> dur_node D i n -> fn_type n = 0 -> fn_bare n.
Proof.
  intros Hh Hd Ht. exact (inl_bare_free (dur_node_local D i n Hh Hd) Ht).
Qed.

(* A NODE'S DATA, off the recovered disk.  [sk_blk] one slot at a time,
   with the slot's presence discharged from its address rather than
   assumed: this is what lets a caller compute [fn_data n] -- and hence
   [dir_entries n] and [fn_file_bytes n] -- from [D] alone. *)
Lemma dur_data (D : gmap Z (list (bv 8))) (i : Z) (n : fs_node) (k : nat) :
  snap_holds D -> dur_node D i n ->
  (k < FS_MAXFILE)%nat -> fn_naddr n k <> 0 ->
  D !! fn_naddr n k = Some (fn_data n k).
Proof.
  intros [S HS] Hd Hk Hnz.
  pose proof (Hd S HS) as Hn.
  pose proof (sk_local HS i n Hn) as Hl.
  destruct (proj2 (inl_blk_dom Hl k Hk) Hnz) as [bs Hbs].
  unfold fn_data. rewrite Hbs. simpl.
  exact (sk_blk (sk_bytes HS) i n k bs Hn Hbs).
Qed.

Lemma dur_data_of_block (D : gmap Z (list (bv 8))) (i : Z) (n : fs_node)
    (k : nat) (bs : list (bv 8)) :
  snap_holds D -> dur_node D i n ->
  (k < FS_MAXFILE)%nat -> fn_naddr n k <> 0 ->
  D !! fn_naddr n k = Some bs ->
  fn_data n k = bs.
Proof.
  intros Hh Hd Hk Hnz Hbs.
  pose proof (dur_data D i n k Hh Hd Hk Hnz) as G. congruence.
Qed.

(* ---------------------------------------------------------------------- *)
(*  3a. the two DIRECTORY readings, pure in the node                       *)
(*                                                                        *)
(*  [dir_entries] is [DirView]'s first-match view ([FsStateInode]), so an  *)
(*  entry is present exactly when some record is live, carries the name,   *)
(*  and no EARLIER record does -- [FsTree.dir_view_lookup_Some] through    *)
(*  [DirView.dir_first_Some].  Both directions are needed: mknod's arm is  *)
(*  the presence, unlink's the absence.                                    *)
(* ---------------------------------------------------------------------- *)

Lemma dir_entries_at (n : fs_node) (j : nat) (s : fname) (z : Z) :
  fn_is_dir n = true ->
  (j < fn_nrec n)%nat ->
  dir_match (fn_data n) j s ->
  (forall k : nat, (k < j)%nat -> ~ dir_match (fn_data n) k s) ->
  bv_unsigned (dir_inum (fn_data n) j) = z ->
  dir_entries n !! s = Some z.
Proof.
  intros Hdir Hj Hm Hno Hz.
  unfold dir_entries. rewrite Hdir.
  apply dir_view_lookup_Some. exists j. split; [| exact Hz].
  apply dir_first_Some. split; [exact Hj |]. split; [exact Hm | exact Hno].
Qed.

Lemma dir_entries_absent (n : fs_node) (s : fname) :
  (forall k : nat, (k < fn_nrec n)%nat -> ~ dir_match (fn_data n) k s) ->
  dir_entries n !! s = None.
Proof.
  intros Hno. unfold dir_entries. destruct (fn_is_dir n).
  - apply dir_view_lookup_None. apply dir_first_None. exact Hno.
  - apply lookup_empty.
Qed.

(* ---------------------------------------------------------------------- *)
(*  3b. the FILE reading's arithmetic, once                                *)
(* ---------------------------------------------------------------------- *)

(* [file_bytes] only ever consults slots the size reaches, so two data
   functions that agree there give the same content. *)
Lemma file_bytes_agree (dat dat' : nat -> list (bv 8)) (m : nat) :
  (forall q : nat, (q * BSIZE < m)%nat -> dat q = dat' q) ->
  file_bytes dat m = file_bytes dat' m.
Proof.
  intros H. unfold file_bytes. apply list_eq. intros k.
  rewrite !list_lookup_fmap.
  destruct (seq 0 m !! k) as [x |] eqn:E; [| reflexivity].
  apply lookup_seq in E as [-> Hlt]. simpl. f_equal.
  unfold file_byte. rewrite ?Nat.add_0_l.
  assert (Hdv : ((k `div` BSIZE) * BSIZE < m)%nat).
  { pose proof (Nat.div_mod_eq k BSIZE) as Hdm. unfold BSIZE in *. lia. }
  rewrite (H _ Hdv). reflexivity.
Qed.

(* a slot the size reaches is a slot the node OWNS, and its index is below
   the direct+indirect bound -- [inl_covers] and [inl_size], with the
   nat/Z crossing done here so no caller repeats it. *)
Lemma dur_slot_covered (D : gmap Z (list (bv 8))) (i : Z) (n : fs_node)
    (q : nat) :
  snap_holds D -> dur_node D i n ->
  (q * BSIZE < Z.to_nat (fn_size n))%nat ->
  (q < FS_MAXFILE)%nat /\ Z.of_nat q * BSIZE_z < fn_size n.
Proof.
  intros Hh Hd Hq.
  pose proof (inl_size (dur_node_local D i n Hh Hd)) as [Hsz0 Hszm].
  assert (Hid : Z.of_nat (Z.to_nat (fn_size n)) = fn_size n)
    by (apply Z2Nat.id; exact Hsz0).
  unfold BSIZE in Hq. unfold FS_MAXFILE in Hszm |- *.
  change BSIZE_z with 1024 in Hszm |- *.
  split; lia.
Qed.

(* ====================================================================== *)
(*  4.  THE THREE SYSCALL READINGS                                        *)
(*                                                                        *)
(*  Each is stated at an ARBITRARY snapshot state over the committed map,  *)
(*  so a consumer holding only [FsCrash.fs_commit_receipt]'s existential   *)
(*  can use it directly.                                                  *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(*  mknod -- the spike (durable-fs-plan.md section 5).                     *)
(*                                                                        *)
(*  After the batch containing a mknod's transaction commits: the current  *)
(*  snapshot's inode table at [inum] IS the created node (its record is    *)
(*  the [d] the transaction wrote -- for mknod, [T_DEVICE] with its major/ *)
(*  minor and [nlink = 1]), and the parent's directory entries contain     *)
(*  [(name |-> inum)].                                                     *)
(*                                                                        *)
(*  WHAT THE CALLER SUPPLIES, and why each piece is the honest one:        *)
(*  - the created node arrives as RECOVERED BYTES (the record block and    *)
(*    the 64-byte splice), because that is what the transaction actually   *)
(*    left in the logged view, and the logged view IS the committed map;   *)
(*  - the parent arrives as a durable NODE, because dirlink's effect is on *)
(*    a data block whose address is the parent's own record -- a caller    *)
(*    gets that node from [dur_node_of_rec] on the parent's slot and then  *)
(*    computes [fn_data] from [D] with [dur_data].                         *)
(* ---------------------------------------------------------------------- *)
Theorem mknod_durable
    (D : gmap Z (list (bv 8))) (sb : fs_sb)
    (parent inum : Z) (p : fs_node) (s : fname)
    (bs : list (bv 8)) (d : dinode) (j : nat) :
  (* the commit's receipt, and the superblock it fixes *)
  snap_holds D ->
  dur_sb D sb ->
  (* the created node, as the transaction left it on the recovered disk *)
  0 <= inum < 16 * (sb_ninodes sb / 16 + 1) ->
  dinode_wf d ->
  D !! rec_bno sb inum = Some bs ->
  rec_in_blk bs (rec_off inum) d ->
  (* the parent directory, and the record dirlink wrote *)
  dur_node D parent p ->
  fn_is_dir p = true ->
  (j < fn_nrec p)%nat ->
  dir_match (fn_data p) j s ->
  (forall k : nat, (k < j)%nat -> ~ dir_match (fn_data p) k s) ->
  bv_unsigned (dir_inum (fn_data p) j) = inum ->
  (* THE READING *)
  exists n : fs_node,
    fn_rec n = d
    /\ dir_entries p !! s = Some inum
    /\ forall S : fs_state_rec, snap_ok S D ->
         fss_inodes S !! inum = Some n /\ fss_inodes S !! parent = Some p.
Proof.
  intros Hh Hsb Hran Hwf Hbs Hrec Hp Hdir Hj Hm Hno Hz.
  destruct (dur_node_of_rec D sb inum bs d Hh Hsb Hran Hwf Hbs Hrec)
    as (n & Hdn & Hd).
  exists n. split; [exact Hd |]. split.
  - exact (dir_entries_at p j s inum Hdir Hj Hm Hno Hz).
  - intros S HS. split; [exact (Hdn S HS) | exact (Hp S HS)].
Qed.

(* NON-VACUITY, AT A REAL INSTANCE (durable-fs-plan.md section 7: every
   hedged or quantified premise gets a witness).  [mknod_durable]'s premise
   set is satisfied by ANY committed map with a directory that has a
   first-match entry: the byte premises are [snap_ok]'s own [sk_regdom] /
   [sk_rec] clauses, and the certificates are section 3's producers.  So
   the theorem fires, and what it returns at that instance is the
   snapshot's own node.  The point of the witness is that nothing in
   [mknod_durable] is provable only because its hypotheses cannot be met. *)
Lemma mknod_durable_inhabited
    (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (parent inum : Z) (p : fs_node) (s : fname) (j : nat) :
  snap_ok S D ->
  0 <= parent < 16 * (sb_ninodes (fss_sb S) / 16 + 1) ->
  0 <= inum < 16 * (sb_ninodes (fss_sb S) / 16 + 1) ->
  fss_inodes S !! parent = Some p ->
  fn_is_dir p = true ->
  (j < fn_nrec p)%nat ->
  dir_match (fn_data p) j s ->
  (forall k : nat, (k < j)%nat -> ~ dir_match (fn_data p) k s) ->
  bv_unsigned (dir_inum (fn_data p) j) = inum ->
  exists n : fs_node,
    fss_inodes S !! inum = Some n /\ dir_entries p !! s = Some inum.
Proof.
  intros HS Hpr Hir Hp Hdir Hj Hm Hno Hz.
  destruct (sk_regdom (sk_bytes HS) inum Hir) as [n Hn].
  destruct (sk_rec (sk_bytes HS) inum n Hn) as (bs & Hbs & Hrec).
  assert (Hsb : dur_sb D (fss_sb S)).
  { intros S' HS'.
    destruct (snap_sb_det S' S D (sk_bytes HS') (sk_bytes HS)) as [_ H].
    exact H. }
  destruct (mknod_durable D (fss_sb S) parent inum p s bs (fn_rec n) j
              (ex_intro _ S HS) Hsb Hir
              (inl_rec_wf (sk_local HS inum n Hn)) Hbs Hrec
              (dur_node_of_snap S D parent p HS Hpr Hp)
              Hdir Hj Hm Hno Hz)
    as (n' & _ & Hent & Hall).
  destruct (Hall S HS) as [H1 _].
  exists n'. split; [exact H1 | exact Hent].
Qed.

(* ---------------------------------------------------------------------- *)
(*  unlink -- the entry is GONE from the parent's snapshot row.            *)
(*                                                                        *)
(*  The premise is what unlink's [memset(&de, 0, sizeof(de))] leaves: no   *)
(*  record below the parent's record count is both LIVE and named [s].     *)
(*  A caller establishes it record by record off [D] ([dur_data] gives     *)
(*  [fn_data p] at every slot the parent owns).                            *)
(*                                                                        *)
(*  THE SECOND ARM, when the link count reached zero and [iput] freed the  *)
(*  inode, is [dur_node_bare] on the freed inum -- a type-0 record on the  *)
(*  recovered disk is a node with no blocks, no size and no links.  It is  *)
(*  stated separately below rather than folded in, because unlink's        *)
(*  ordinary case does NOT free the inode.                                 *)
(* ---------------------------------------------------------------------- *)
Theorem unlink_durable
    (D : gmap Z (list (bv 8))) (parent : Z) (p : fs_node) (s : fname) :
  dur_node D parent p ->
  (forall k : nat, (k < fn_nrec p)%nat -> ~ dir_match (fn_data p) k s) ->
  forall S : fs_state_rec, snap_ok S D ->
    fss_inodes S !! parent = Some p /\ dir_entries p !! s = None.
Proof.
  intros Hp Hno S HS.
  split; [exact (Hp S HS) | exact (dir_entries_absent p s Hno)].
Qed.

(* ...and the freed inode, off its recovered record: the durable table's
   node at [inum] holds no block, has size 0 and has no links. *)
Theorem unlink_durable_freed
    (D : gmap Z (list (bv 8))) (sb : fs_sb) (inum : Z)
    (bs : list (bv 8)) (d : dinode) :
  snap_holds D ->
  dur_sb D sb ->
  0 <= inum < 16 * (sb_ninodes sb / 16 + 1) ->
  dinode_wf d ->
  D !! rec_bno sb inum = Some bs ->
  rec_in_blk bs (rec_off inum) d ->
  bv_unsigned (di_type d) = 0 ->
  exists n : fs_node,
    fn_rec n = d /\ fn_bare n
    /\ forall S : fs_state_rec, snap_ok S D -> fss_inodes S !! inum = Some n.
Proof.
  intros Hh Hsb Hran Hwf Hbs Hrec Hty.
  destruct (dur_node_of_rec D sb inum bs d Hh Hsb Hran Hwf Hbs Hrec)
    as (n & Hdn & Hd).
  exists n. split; [exact Hd |]. split; [| exact Hdn].
  apply (dur_node_bare D inum n Hh Hdn).
  unfold fn_type. rewrite Hd. exact Hty.
Qed.

(* ---------------------------------------------------------------------- *)
(*  write -- the file's snapshot bytes ARE the written value.              *)
(*                                                                        *)
(*  Per block first ([write_durable_block]: the recovered disk holds the   *)
(*  file's k-th block at the address the file's own record names), then    *)
(*  the whole content ([write_durable]: the durable node's flat byte view  *)
(*  is [file_bytes] of whatever the caller can exhibit at each covered     *)
(*  slot).  A caller that wrote [dat] through the log and holds the        *)
(*  recovered blocks gets the second directly.                            *)
(*                                                                        *)
(*  HOLES ARE HANDLED BY [inl_covers], not assumed away: a slot BELOW the  *)
(*  size always has a nonzero address, so it is always a block of [D].     *)
(* ---------------------------------------------------------------------- *)
Lemma write_durable_block (D : gmap Z (list (bv 8))) (i : Z) (n : fs_node)
    (k : nat) :
  snap_holds D -> dur_node D i n ->
  (k < FS_MAXFILE)%nat -> Z.of_nat k * BSIZE_z < fn_size n ->
  D !! fn_naddr n k = Some (fn_data n k).
Proof.
  intros Hh Hd Hk Hlt.
  apply (dur_data D i n k Hh Hd Hk).
  exact (inl_covers (dur_node_local D i n Hh Hd) k Hk Hlt).
Qed.

Theorem write_durable (D : gmap Z (list (bv 8))) (i : Z) (n : fs_node)
    (dat : nat -> list (bv 8)) :
  snap_holds D -> dur_node D i n ->
  (forall k : nat, (k < FS_MAXFILE)%nat -> Z.of_nat k * BSIZE_z < fn_size n ->
     D !! fn_naddr n k = Some (dat k)) ->
  fn_file_bytes n = file_bytes dat (Z.to_nat (fn_size n))
  /\ forall S : fs_state_rec, snap_ok S D -> fss_inodes S !! i = Some n.
Proof.
  intros Hh Hd Hall. split; [| exact Hd].
  unfold fn_file_bytes. apply file_bytes_agree. intros q Hq.
  destruct (dur_slot_covered D i n q Hh Hd Hq) as [Hlt Hsz].
  pose proof (write_durable_block D i n q Hh Hd Hlt Hsz) as G1.
  pose proof (Hall q Hlt Hsz) as G2. congruence.
Qed.

(* ====================================================================== *)
(*  5.  WHERE [snap_holds] COMES FROM                                     *)
(*                                                                        *)
(*  Two producers, both landed, both READ rather than proved here.  The    *)
(*  first is the commit's own receipt; the second is the adequacy-level    *)
(*  pure projection, which says the same thing at EVERY reachable state of *)
(*  the whole machine -- power cycles included.                            *)
(* ====================================================================== *)

Lemma snap_holds_of_boot_pure (cov : gset Z) (ls : Z) (dk : Z -> bv 8) :
  fs_boot_pure cov ls dk ->
  exists D : gmap Z (list (bv 8)),
    fs_recovery (fs_blocks dk) D cov ls /\ snap_holds D.
Proof.
  intros [_ (D & Hrec & _ & HS)]. exists D. split; [exact Hrec | exact HS].
Qed.

Section commit.
  (* The binder list is [FsCrash]'s [Section fs_crash], VERBATIM: a lemma
     about a definition of that section stated with a SHORTER list sends
     typeclass search after an unknown [Σ] and the elaboration explodes
     (durable-notes.md, "A LEMMA'S binder list must match the definition
     it is about"). *)
  Context `{!fsCrashG Σ, !lockG Σ}.
  Context `{!ghost_mapG Σ nat riscvEraGS, !mono_natG Σ,
            !ghost_varG Σ log_mirror, !diskImgG Σ}.
  Context `{!fsLinkG Σ, !fsTopG Σ}.

  (* [FsCrash.fs_commit_receipt], with the state's name dropped: what the
     readings above consume is [snap_holds], never a particular [S]. *)
  Lemma fs_commit_snap_holds (γs : fs_crash_names) (cov : gset Z) (ls : Z)
      (dk : Z -> bv 8) :
    P_fs γs cov ls dk -∗
      ∃ D : gmap Z (list (bv 8)),
        ⌜fs_recovery (fs_blocks dk) D cov ls⌝ ∗ ⌜snap_holds D⌝ ∗
        P_fs γs cov ls dk.
  Proof.
    iIntros "Hp".
    iDestruct (fs_commit_receipt with "Hp") as (D S) "(%Hrec & %Hok & Hp)".
    iExists D. iSplitR; [iPureIntro; exact Hrec |].
    iSplitR; [iPureIntro; by exists S |]. iExact "Hp".
  Qed.
End commit.
