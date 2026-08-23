(* ======================================================================= *)
(* FsOpLink.v -- durable-disk stage G2, batch (2): sys_link's exit arms     *)
(* against the stage-F2 effect vocabulary (worklist §6, item G2).           *)
(*                                                                          *)
(* THE ARM INVENTORY (kernel/sysfile.c's sys_link, and the arm names of     *)
(* [ProofSysLink]/[ProofSysLinkTails]):                                     *)
(*                                                                          *)
(*     ARM A   argstr < 0 (before begin_op)                    IDENTITY     *)
(*     ARM B   namei(old) == 0                                 IDENTITY     *)
(*     ARM C   ip->type == T_DIR                               IDENTITY     *)
(*     ARM D   ip->nlink >= NLINK_MAX                          IDENTITY     *)
(*     ---- THE MINT: ip->nlink++; iupdate(ip); iunlock(ip) ----            *)
(*     ARM E   nameiparent(new) == 0            -> bad:        ROLLBACK     *)
(*     ARM E2  dp->nlink == 0 (the orphan guard) -> bad:       ROLLBACK     *)
(*     ARM F   dp->dev != ip->dev || dirlink < 0 -> bad:       ROLLBACK     *)
(*     ARM OK  dirlink succeeded                               eff_link_entry *)
(*                                                                          *)
(* Arms A-D write nothing at all: they exit BEFORE the [ip->nlink++], so    *)
(* they are identity on the committed view and owe no lemma.                *)
(*                                                                          *)
(* ARM OK HAS A SECOND SUB-ARM this file does not close: when the new       *)
(* parent's records exactly fill its last block, dirlink's writei runs      *)
(* bmap and ALLOCATES, and [eff_link_entry]'s append branch                 *)
(* ([16(k+1) <= fs_nblk sz * BSIZE]) is then false -- the arm is            *)
(* [eff_link_entry] after [FsEffAllocBlock.eff_alloc_file_block].  It is    *)
(* blocked on the effect files exporting nothing but                        *)
(* [fs_durable_wf_view] (a second effect's [fs_reachable] premise cannot    *)
(* be transported); worklist G2 batch (2) findings (v)/(vi).  ARM F's       *)
(* [dirlink < 0] route inherits the kernel-defect candidate of 2026-08-23   *)
(* the same way [FsOpMknod]'s FAIL note does.                               *)
(*                                                                          *)
(* THE THREE [bad:] ARMS ARE THE INTERESTING ONES.  Each has ALREADY        *)
(* written IBLOCK(ip) once (the mint), and the [bad:] tail writes it a      *)
(* second time:                                                             *)
(*                                                                          *)
(*     bad: ilock(ip); ip->nlink--; iupdate(ip); iunlockput(ip); end_op();  *)
(*                                                                          *)
(* so the arm's NET effect is two [eff_dinode]s at the SAME record, whose   *)
(* composition is the IDENTITY on the committed view.  That is proved here  *)
(* as an actual equation ([op_link_rollback_id]) rather than as a           *)
(* well-formedness step, because what the arm's finalize needs is           *)
(* "my blocks in L equal A's" -- a [fs_durable_wf_body] step would lose     *)
(* the block-by-block agreement row (a) is stated in terms of.              *)
(* [op_link_rollback_wf] is the wf reading, derived from the equation.      *)
(*                                                                          *)
(* (The [bad:] tail's [iunlockput(ip)] cannot free: the decrement restores  *)
(* [ip->nlink] to its PRE-MINT value, and namei reached [ip] through a live *)
(* dirent, so that value is at least one.  ARM OK's [iput(ip)] likewise --  *)
(* the new link has just been committed -- and its [iunlockput(dp)] is      *)
(* guarded by the [dp->nlink == 0] test of ARM E2.)                         *)
(*                                                                          *)
(*                                                                          *)
(* ---- THE CAVEAT ON EVERY [IDENTITY] ABOVE ----------------------------- *)
(* xv6's [iput] MAY TRUNCATE, and [SpecIput] is explicit that iput always   *)
(* MAY truncate and no caller can know in advance which arm runs; any arm   *)
(* that drops the LAST reference to an inode whose [nlink] is zero also     *)
(* runs itrunc + [ip->type = 0] + the bfrees, i.e. one                      *)
(* [FsEffFreeInode.eff_free_inode].  Every [iunlockput]/[iput] on the arms  *)
(* above -- and the ones inside namei/nameiparent -- carries that           *)
(* possibility, so [IDENTITY] here means identity APART FROM iput's free    *)
(* path.  That composition is CROSS-CUTTING (it rides every op of stage     *)
(* G2, not just this one) and is recorded at worklist item G2 rather than   *)
(* duplicated per op.                                                      *)
(*                                                                          *)
(* Pure Rocq: no Iris, no [log_state].                                      *)
(* ======================================================================= *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import DirentEnc.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.
Require Import FsImg.
Require Import FsWf.
Require Import FsEffBase.
Require Import FsEffLinkEntry.

Local Open Scope Z_scope.

(* ======================================================================= *)
(*  1.  ARM OK -- the new hard link                                         *)
(* ======================================================================= *)

Lemma op_link_ok (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (name : fname) (i : Z) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  (* the new parent: a reachable directory *)
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  (* the target: a live NON-directory (sys_link's [ip->type == T_DIR] arm) *)
  0 < i < sb_ninodes sb -> i < 65536 ->
  (bv_unsigned (di_type (fs_dinode P sb i)) = T_FILE_z
   \/ bv_unsigned (di_type (fs_dinode P sb i)) = T_DEVICE_z) ->
  (* sys_link's NLINK_MAX guard: the new link fits *)
  bv_unsigned (di_nlink (fs_dinode P sb i)) < 32767 ->
  (* the name, and that the new parent does not already carry it *)
  (length name <= 14)%nat -> nonul name ->
  dir_first (fs_file_data P sb d)
    (dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))) name = None ->
  (* dirlink's slot *)
  ((k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat
     /\ ~ dir_live (fs_file_data P sb d) k
   \/ k = dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))
     /\ 16 * (Z.of_nat k + 1)
        <= fs_nblk (bv_unsigned (di_size (fs_dinode P sb d))) * BSIZE_z) ->
  fs_durable_wf_view (eff_link_entry P sb d k name i).
Proof.
  intros Hv Hp Hd Hdty Hdre Hi Hi16 Hity Hnl Hlen Hnn Hnone Harm.
  exact (eff_link_entry_wfv P sb d k name i Hv Hp Hd Hdty Hdre Hi Hi16 Hity
           Hnl Hlen Hnn Hnone Harm).
Qed.

(* ======================================================================= *)
(*  2.  THE [eff_dinode] ALGEBRA THE ROLLBACK NEEDS                         *)
(*                                                                          *)
(*  [eff_dinode] RE-ENCODES a whole inode block out of the sixteen records  *)
(*  it decodes, so composing two of them at one inum is composition of the  *)
(*  record functions -- PROVIDED the block being decoded really is a        *)
(*  [diblk_bytes] encoding, which is exactly what the inode layer hands     *)
(*  every writer ([FsImg.fs_dinode_of_diblk] is the round trip, and this    *)
(*  is its list-level reading).                                            *)
(* ======================================================================= *)

Lemma fs_iblk_of_diblk (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (ds : list dinode) :
  fs_sb_ok sb ->
  0 <= i < 16 * (sb_ninodes sb / 16 + 1) ->
  diblk_wf ds ->
  P (IBLOCK (fs_inum_bv i) (sb_inodestart sb)) = diblk_bytes ds ->
  fs_iblk P sb i = ds.
Proof.
  intros Hok Hi Hds Hblk.
  destruct (fs_iblk_wf P sb i) as [Hlen16 _].
  destruct Hds as [Hdslen Hdsall] eqn:Hdswf.
  apply list_eq. intros s.
  destruct (decide (s < 16)%nat) as [Hs | Hs].
  2:{ rewrite (lookup_ge_None_2 (fs_iblk P sb i) s) by lia.
      rewrite (lookup_ge_None_2 ds s) by lia. reflexivity. }
  rewrite (list_lookup_lookup_total_lt (fs_iblk P sb i) s) by lia.
  rewrite (list_lookup_lookup_total_lt ds s) by lia.
  f_equal.
  assert (Hdiv : i / 16 < sb_ninodes sb / 16 + 1)
    by (apply Z.div_lt_upper_bound; lia).
  assert (Hdiv0 : 0 <= i / 16) by (apply Z.div_pos; lia).
  assert (Hjd : (16 * (i / 16) + Z.of_nat s) / 16 = i / 16).
  { rewrite Z.mul_comm, Z.div_add_l by lia.
    rewrite (Z.div_small (Z.of_nat s) 16) by lia. lia. }
  assert (Hjm : (16 * (i / 16) + Z.of_nat s) `mod` 16 = Z.of_nat s).
  { rewrite Z.add_comm, (Z.mul_comm 16 (i / 16)), Z.mod_add by lia.
    apply Z.mod_small. lia. }
  assert (Hj : 0 <= 16 * (i / 16) + Z.of_nat s
               < 16 * (sb_ninodes sb / 16 + 1)) by lia.
  set (j := 16 * (i / 16) + Z.of_nat s) in *.
  assert (Hislot : islot (fs_inum_bv j) = s).
  { rewrite (islot_of sb Hok j Hj), Hjm, Nat2Z.id. reflexivity. }
  assert (Hblkj : P (IBLOCK (fs_inum_bv j) (sb_inodestart sb))
                  = diblk_bytes ds).
  { rewrite (proj2 (iblock_eq_iff sb Hok i j Hi Hj) Hjd). exact Hblk. }
  assert (H1 : fs_iblk P sb i !!! s = fs_dinode P sb j).
  { rewrite <- Hislot. exact (fs_iblk_slot sb Hok P i j Hi Hj Hjd). }
  assert (H2 : fs_dinode P sb j = ds !!! s).
  { rewrite <- Hislot.
    exact (fs_dinode_of_diblk P sb j ds (conj Hdslen Hdsall) Hblkj). }
  rewrite H1, H2. reflexivity.
Qed.

(* re-encoding the record you just decoded writes the block back verbatim *)
Lemma eff_dinode_id (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (ds : list dinode) (b : Z) :
  fs_sb_ok sb ->
  0 <= i < 16 * (sb_ninodes sb / 16 + 1) ->
  diblk_wf ds ->
  P (IBLOCK (fs_inum_bv i) (sb_inodestart sb)) = diblk_bytes ds ->
  eff_dinode P sb i (fs_dinode P sb i) b = P b.
Proof.
  intros Hok Hi Hds Hblk.
  destruct (decide (b = IBLOCK (fs_inum_bv i) (sb_inodestart sb)))
    as [-> | Hne]; [| exact (eff_dinode_out sb P i _ b Hne)].
  unfold eff_dinode. rewrite fs_upd_at, Hblk.
  rewrite (fs_iblk_of_diblk P sb i ds Hok Hi Hds Hblk).
  rewrite (list_insert_id ds (islot (fs_inum_bv i)) (fs_dinode P sb i)).
  - reflexivity.
  - rewrite (fs_dinode_of_diblk P sb i ds Hds Hblk).
    apply list_lookup_lookup_total_lt.
    destruct Hds as [Hdslen _]. pose proof (islot_lt (fs_inum_bv i)). lia.
Qed.

(* the two writes of one [bad:] arm, at the values the code stores: each
   re-encodes the record the PREVIOUS view decodes, with [nlink] moved by
   one ([ProofSysLinkParts.sl_setnl] / [sl_ndec] at the F2 vocabulary) *)
Definition link_rollback (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
  : Z -> list (bv 8) :=
  let P1 := eff_dinode P sb i (di_nlink_inc (fs_dinode P sb i)) in
  eff_dinode P1 sb i (di_nlink_dec (fs_dinode P1 sb i)).

Lemma di_nlink_dec_inc (dn : dinode) :
  bv_unsigned (di_nlink dn) < 65535 -> di_nlink_dec (di_nlink_inc dn) = dn.
Proof.
  intros Hlt.
  pose proof (bv_unsigned_in_range 16 (di_nlink dn)) as Hr.
  assert (Hm : bv_modulus 16 = 65536) by reflexivity.
  unfold di_nlink_dec, di_nlink_inc, di_set_nlink.
  cbn [di_type di_major di_minor di_nlink di_size di_addrs].
  rewrite (Z_to_bv_small 16 (bv_unsigned (di_nlink dn) + 1)) by lia.
  replace (bv_unsigned (di_nlink dn) + 1 - 1)
    with (bv_unsigned (di_nlink dn)) by lia.
  rewrite Z_to_bv_bv_unsigned.
  destruct dn. reflexivity.
Qed.

(* ======================================================================= *)
(*  3.  THE ROLLBACK ARMS (E / E2 / F) -- NET IDENTITY                      *)
(* ======================================================================= *)

Lemma op_link_rollback_id (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (ds : list dinode) (b : Z) :
  fs_sb_ok sb ->
  0 <= i < 16 * (sb_ninodes sb / 16 + 1) ->
  diblk_wf ds ->
  P (IBLOCK (fs_inum_bv i) (sb_inodestart sb)) = diblk_bytes ds ->
  bv_unsigned (di_nlink (fs_dinode P sb i)) < 65535 ->
  link_rollback P sb i b = P b.
Proof.
  intros Hok Hi Hds Hblk Hnl.
  unfold link_rollback. cbv zeta.
  set (dn := fs_dinode P sb i) in *.
  set (dn1 := di_nlink_inc dn) in *.
  assert (Hwf1 : dinode_wf dn1)
    by (apply di_set_nlink_wf, fs_dinode_wf).
  (* the second write's VALUE: the intermediate view decodes [dn1], whose
     [nlink--] is [dn] again *)
  assert (Hmid : fs_dinode (eff_dinode P sb i dn1) sb i = dn1).
  { rewrite (eff_dinode_dec sb Hok P i dn1 i Hwf1 Hi Hi).
    rewrite decide_True by reflexivity. reflexivity. }
  assert (Hdec2 : di_nlink_dec dn1 = dn)
    by (unfold dn1; exact (di_nlink_dec_inc dn Hnl)).
  rewrite Hmid, Hdec2.
  (* the intermediate view's inode block IS a [diblk_bytes] encoding, so
     the second write is [eff_dinode_id] there... *)
  assert (Hds1 : diblk_wf (<[islot (fs_inum_bv i) := dn1]> ds))
    by (apply diblk_wf_insert; [exact Hds | exact Hwf1]).
  assert (Hblk1 : eff_dinode P sb i dn1
                    (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
                  = diblk_bytes (<[islot (fs_inum_bv i) := dn1]> ds)).
  { unfold eff_dinode. rewrite fs_upd_at.
    rewrite (fs_iblk_of_diblk P sb i ds Hok Hi Hds Hblk). reflexivity. }
  (* ...and its value there is [dn = fs_dinode (eff_dinode ...) sb i]
     transported back, which [eff_dinode_id] closes once the record is the
     decoded one.  Spell the second write out and compare blocks. *)
  destruct (decide (b = IBLOCK (fs_inum_bv i) (sb_inodestart sb)))
    as [-> | Hne].
  2:{ rewrite (eff_dinode_out sb _ i _ b Hne).
      exact (eff_dinode_out sb P i dn1 b Hne). }
  unfold eff_dinode at 1. rewrite fs_upd_at.
  rewrite (fs_iblk_of_diblk (eff_dinode P sb i dn1) sb i
             (<[islot (fs_inum_bv i) := dn1]> ds) Hok Hi Hds1 Hblk1).
  rewrite list_insert_insert.
  rewrite (list_insert_id ds (islot (fs_inum_bv i)) dn).
  - exact (eq_sym Hblk).
  - unfold dn. rewrite (fs_dinode_of_diblk P sb i ds Hds Hblk).
    apply list_lookup_lookup_total_lt.
    destruct Hds as [Hdslen _]. pose proof (islot_lt (fs_inum_bv i)). lia.
Qed.

(* the wf reading, for an arm that only needs the invariant back *)
Lemma op_link_rollback_wf (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (ds : list dinode) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  diblk_wf ds ->
  P (IBLOCK (fs_inum_bv i) (sb_inodestart sb)) = diblk_bytes ds ->
  bv_unsigned (di_nlink (fs_dinode P sb i)) < 65535 ->
  fs_durable_wf_view (link_rollback P sb i).
Proof.
  intros Hv Hp Hi Hds Hblk Hnl.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  pose proof (fs_sb_wf_ok sb (fdw_sb P sb Hsw)) as Hok.
  destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & _ & Hle & _).
  apply (fs_durable_wf_view_ext P (link_rollback P sb i) sb Hp).
  - intros b _. exact (op_link_rollback_id P sb i ds b Hok
                         ltac:(lia) Hds Hblk Hnl).
  - exists sb. split; [exact Hp | exact Hsw].
Qed.
