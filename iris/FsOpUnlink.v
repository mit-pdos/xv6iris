(* FsOpUnlink.v -- durable-disk stage G2 (batch 3): sys_unlink, both
   targets, both exit arms.

     sys_unlink(void) {                                (kernel/sysfile.c)
       begin_op();
       dp = nameiparent(path, name);           // "." / ".." rejected
       ip = dirlookup(dp, name, &off);
       if (ip->nlink < 1) panic("unlink: nlink < 1");
       if (ip->type == T_DIR && !isdirempty(ip)) { iunlockput(ip); goto bad; }
       memset(&de, 0, sizeof(de));
       writei(dp, 0, &de, off, sizeof(de));    // the record is zeroed
       if (ip->type == T_DIR) { dp->nlink--; iupdate(dp); }
       iunlockput(dp);
       ip->nlink--; iupdate(ip);
       iunlockput(ip);                         // <-- MAY FREE, same txn
       end_op();
     }

   FOUR ARMS with an effect, plus the two failure arms (nameiparent fails,
   or [bad]: the name is a dot, the lookup misses, or the target is a
   non-empty directory) whose transaction writes NOTHING -- for those the
   obligation is the identity, [op_unlink_bad_wfv].

     file target, target survives   [eff_unlink_entry]        (arm F1)
     file target, iput frees        [.. then eff_iput_free]   (arm F2)
     dir  target, target survives   [eff_unlink_entry]        (arm D1)
     dir  target, iput frees        [.. then eff_iput_free]   (arm D2)

   WHY THE SURVIVING ARM NEEDS NOTHING MORE THAN F2's WRAPPER.  On the
   file side the target may still be OPEN (another [struct file], or
   another link), and when the dropped link was its last one AND the file
   stays open the target becomes a COMMITTED ORPHAN: live type, nlink 0,
   unreachable.  W9/W3 admit exactly that state (F1's two refinements), so
   there is no further effect to compose and no further obligation --
   [eff_unlink_entry_file_wfv] IS the arm's lemma.  The dir side's
   surviving arm is the same statement (the child is orphaned but the
   caller still holds a reference).

   WHY THE FREEING ARM IS PRECONDITION TRANSPORT.  [FsOpIputFree]'s family
   asks for the target's nlink to be ZERO at the view it acts on, and what
   the arm holds is the nlink of the view BEFORE the unlink.  So the
   content of arms F2/D2 is: the unlink effect leaves the superblock alone
   (its three touched blocks are two inode blocks and one DATA block of
   [dp] -- [unlink_blk] is that geometry), so [sb] re-parses; and it
   rewrites record [i] to [di_nlink_dec], so the target's nlink at the
   intermediate view is [1 - 1 = 0] and its type is untouched.  The
   orphan characterisation ([FsOpIputFree.fs_orphan_unreachable]) then
   turns that into the unreachability [eff_free_inode_wfv] wants --
   which is how the FILE arm gets its unreachability without any
   in-edge counting: the dir arm's [nlink = 1] premise is doing that
   work already, and on the file side W9 does it.

   Pure Rocq, no Iris, no [log_state]: worklist item G2, batch (3).       *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvModelBytes.
Require Import BioDefs.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.
Require Import FsImg.
Require Import FsWf.
Require Import FsEffBase.
Require Import FsEffUnlinkEntry.
Require Import FsOpIputFree.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  WHAT THE UNLINK EFFECT LEAVES BEHIND (in the sweeps' context)      *)
(* ====================================================================== *)

Section UnlinkPost.
  Context (P : Z -> list (bv 8)) (sb : fs_sb).
  Context (Hp : fs_parse_sb P = Some sb).
  Context (Hsb : fs_sb_wf sb = true).
  Context (HW3 : fs_inodes_dwf P sb = true).
  Context (u : gset Z) (Hu : fs_used_set P sb = Some u).
  Context (Hbm : fs_bitmap_wf P sb u = true).
  Context (HW7 : fs_root_wf P sb = true).
  Context (HW8 : fs_dots_all P sb = true).
  Context (nib : nat) (Hnibz : Z.of_nat nib = sb_ninodes sb / 16 + 1).
  Context (Hreg : fs_region_wf P sb nib = true).
  Context (rd : gset Z) (Hrd : fs_rdirs P sb rd).
  Context (Hdok : forall z : Z, z ∈ rd ->
              fs_dir_ok P sb z (fs_dinode P sb z)).
  Context (Hlkg : fs_links_gen P sb rd).
  Context (Horph : fs_orphans_empty P sb rd).

  Set Default Proof Using "All".

  Let Hok : fs_sb_ok sb := fs_sb_wf_ok sb Hsb.

  Local Notation dok_at := (dok_at P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation blk_addr_covered := (blk_addr_covered P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).

  (* the parent's record [k] lives in a DATA block -- the geometry the
     three transport lemmas below all run on ([FsEffUnlinkEntry]'s own
     [Ha_rng], stated once) *)
  Lemma unlink_blk (d : Z) (k : nat) :
    0 <= d < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
    fs_reachable P sb d ->
    (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
    fs_data_start sb
    <= fs_blk_addr P (fs_dinode P sb d) (k / 64) < sb_size sb.
  Proof.
    intros Hd Hdty Hdre Hk.
    set (dn := fs_dinode P sb d) in *.
    assert (Hdlive : bv_unsigned (di_type dn) <> 0)
      by (rewrite Hdty; unfold T_DIR_z; discriminate).
    assert (Hd_rd : d ∈ rd)
      by (apply (Hrd d); split; [lia | split; [exact Hdty | exact Hdre]]).
    pose proof (Hdok d Hd_rd) as Hddok. fold dn in Hddok.
    pose proof (dok_at d Hd Hdlive) as Hdok_d. fold dn in Hdok_d.
    pose proof (fdi_size _ _ _ Hdok_d) as Hcapd. fold dn in Hcapd.
    pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as Hsz0.
    destruct (fdo_gran _ _ _ _ Hddok) as (qd & Hqd).
    set (szd := bv_unsigned (di_size dn)) in *.
    set (nrec := dir_nrec szd) in *.
    assert (Hsz16 : szd = 16 * Z.of_nat nrec).
    { unfold nrec, dir_nrec. rewrite Z2Nat.id by (apply Z.div_pos; lia).
      rewrite Hqd. rewrite Z.div_mul by lia. lia. }
    assert (Hkwin : 16 * (Z.of_nat k + 1) <= fs_nblk szd * BSIZE_z).
    { pose proof (fs_nblk_cover szd ltac:(lia)) as Hcov.
      unfold BSIZE_z in *. lia. }
    assert (Hkb : Z.of_nat (k / 64) < fs_nblk szd).
    { assert (Hkz : Z.of_nat k < 64 * fs_nblk szd)
        by (unfold BSIZE_z in Hkwin; lia).
      rewrite (Nat2Z.inj_div k 64).
      apply Z.div_lt_upper_bound; lia. }
    pose proof (fs_nblk_max szd ltac:(lia) Hcapd) as Hnm.
    exact (blk_addr_covered d (k / 64)%nat Hd Hdlive ltac:(lia) Hkb).
  Qed.

  (* the target inum is an inum *)
  Lemma unlink_target_range (d : Z) (k : nat) (i : Z) :
    0 <= d < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
    fs_reachable P sb d ->
    (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
    dir_live (fs_file_data P sb d) k ->
    bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
    0 <= i < sb_ninodes sb.
  Proof.
    intros Hd Hdty Hdre Hk Hlvk Hieq.
    assert (Hd_rd : d ∈ rd)
      by (apply (Hrd d); split; [lia | split; [exact Hdty | exact Hdre]]).
    destruct (fdo_ent _ _ _ _ (Hdok d Hd_rd) k Hk Hlvk) as (Hirange & _).
    unfold fs_file_data in Hieq. rewrite Hieq in Hirange. lia.
  Qed.

  (* the superblock is not one of the three blocks the effect writes *)
  Lemma unlink_sb_block (d : Z) (k : nat) (i : Z) :
    0 <= d < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
    fs_reachable P sb d ->
    (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
    dir_live (fs_file_data P sb d) k ->
    bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
    eff_unlink_entry P sb d k i SB_BNO = P SB_BNO.
  Proof.
    intros Hd Hdty Hdre Hk Hlvk Hieq.
    pose proof (unlink_blk d k Hd Hdty Hdre Hk) as Ha.
    pose proof (unlink_target_range d k i Hd Hdty Hdre Hk Hlvk Hieq) as Hi.
    destruct (iblock_bounds sb Hok i (iblk_z_range sb i Hi))
      as (Hib1 & _ & _).
    destruct (iblock_bounds sb Hok d (iblk_z_range sb d Hd))
      as (Hdb1 & _ & _).
    destruct (fs_sb_ok_meta sb Hok) as (Hm1 & Hm2 & Hm3).
    unfold eff_unlink_entry. cbv zeta.
    rewrite fs_upd_ne by (unfold SB_BNO, fs_data_start in *; lia).
    rewrite (eff_dinode_out sb _ i _ SB_BNO ltac:(unfold SB_BNO in *; lia)).
    destruct (decide (bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z))
      as [_ | _]; [| reflexivity].
    exact (eff_dinode_out sb P d _ SB_BNO ltac:(unfold SB_BNO in *; lia)).
  Qed.

  (* ...so [sb] re-parses, and the target's record is the decremented one *)
  Lemma unlink_parse (d : Z) (k : nat) (i : Z) :
    0 <= d < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
    fs_reachable P sb d ->
    (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
    dir_live (fs_file_data P sb d) k ->
    bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
    fs_parse_sb (eff_unlink_entry P sb d k i) = Some sb.
  Proof.
    intros Hd Hdty Hdre Hk Hlvk Hieq.
    rewrite (fs_parse_sb_ext P (eff_unlink_entry P sb d k i)
               (unlink_sb_block d k i Hd Hdty Hdre Hk Hlvk Hieq)).
    exact Hp.
  Qed.

  Lemma unlink_dinode (d : Z) (k : nat) (i : Z) :
    0 <= d < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
    fs_reachable P sb d ->
    (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
    dir_live (fs_file_data P sb d) k ->
    bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
    fs_dinode (eff_unlink_entry P sb d k i) sb i
    = di_nlink_dec (fs_dinode P sb i).
  Proof.
    intros Hd Hdty Hdre Hk Hlvk Hieq.
    pose proof (unlink_blk d k Hd Hdty Hdre Hk) as Ha.
    pose proof (unlink_target_range d k i Hd Hdty Hdre Hk Hlvk Hieq) as Hi.
    pose proof (iblk_z_range sb i Hi) as HiN.
    destruct (iblock_bounds sb Hok i HiN) as (_ & _ & Hib3).
    destruct (fs_sb_ok_meta sb Hok) as (Hm1 & Hm2 & Hm3).
    set (base := if decide (bv_unsigned (di_type (fs_dinode P sb i))
                            = T_DIR_z)
                 then eff_dinode P sb d (di_nlink_dec (fs_dinode P sb d))
                 else P).
    assert (Hblk : eff_unlink_entry P sb d k i
                     (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
                   = eff_dinode base sb i (di_nlink_dec (fs_dinode P sb i))
                       (IBLOCK (fs_inum_bv i) (sb_inodestart sb))).
    { unfold eff_unlink_entry. cbv zeta. fold base.
      apply fs_upd_ne. unfold fs_data_start in *. lia. }
    rewrite (fs_dinode_ext _ _ sb i Hblk).
    rewrite (eff_dinode_dec sb Hok base i (di_nlink_dec (fs_dinode P sb i)) i
               (di_set_nlink_wf _ _ (fs_dinode_wf P sb i)) HiN HiN).
    rewrite decide_True by reflexivity. reflexivity.
  Qed.

End UnlinkPost.

(* ====================================================================== *)
(*  2.  THE VIEW-LEVEL TRANSPORT                                           *)
(* ====================================================================== *)

(* the three facts above, at [fs_durable_wf_view] -- the shape an arm
   holds.  [Local Ltac] would not help here: each is one [destruct] of
   the record, spelled as in the F2 wrappers. *)

Lemma op_unlink_target_range (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (i : Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
  dir_live (fs_file_data P sb d) k ->
  bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
  0 <= i < sb_ninodes sb.
Proof.
  intros Hv Hp. intros.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  apply (unlink_target_range P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph d k); assumption.
Qed.

Lemma op_unlink_parse (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (i : Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
  dir_live (fs_file_data P sb d) k ->
  bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
  fs_parse_sb (eff_unlink_entry P sb d k i) = Some sb.
Proof.
  intros Hv Hp. intros.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  apply (unlink_parse P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph d k); assumption.
Qed.

Lemma op_unlink_dinode (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (i : Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
  dir_live (fs_file_data P sb d) k ->
  bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
  fs_dinode (eff_unlink_entry P sb d k i) sb i
  = di_nlink_dec (fs_dinode P sb i).
Proof.
  intros Hv Hp. intros.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  apply (unlink_dinode P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph d k); assumption.
Qed.

(* the last link, spent: [di_nlink_dec] of a [nlink = 1] record reads 0 *)
Lemma di_nlink_dec_last (dn : dinode) :
  bv_unsigned (di_nlink dn) = 1 ->
  bv_unsigned (di_nlink (di_nlink_dec dn)) = 0.
Proof.
  intros H1. unfold di_nlink_dec, di_set_nlink. cbn [di_nlink].
  rewrite H1. change (1 - 1) with 0. apply Z_to_bv_small.
  pose proof (bv_modulus_pos 16). lia.
Qed.

(* ====================================================================== *)
(*  3.  THE FOUR ARMS                                                      *)
(* ====================================================================== *)

(* ---- arm F1: a file target that survives the unlink ------------------- *)

(* The whole arm IS [FsEffUnlinkEntry]'s file wrapper; it is restated
   under the op's name so the G3 sweep cites one vocabulary, and because
   this is the arm on which the target may become a COMMITTED ORPHAN
   (last link gone, file still open): the invariant admits it and there
   is nothing further to prove. *)
Lemma op_unlink_file_wfv (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (i : Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
  (2 <= k)%nat ->
  dir_live (fs_file_data P sb d) k ->
  bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
  (bv_unsigned (di_type (fs_dinode P sb i)) = T_FILE_z
   \/ bv_unsigned (di_type (fs_dinode P sb i)) = T_DEVICE_z) ->
  fs_durable_wf_view (eff_unlink_entry P sb d k i).
Proof. exact (eff_unlink_entry_file_wfv P sb d k i). Qed.

(* ---- arm F2: the file target's last link, freed in the same txn ------- *)

Lemma op_unlink_file_free_wfv (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (i : Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
  (2 <= k)%nat ->
  dir_live (fs_file_data P sb d) k ->
  bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
  (bv_unsigned (di_type (fs_dinode P sb i)) = T_FILE_z
   \/ bv_unsigned (di_type (fs_dinode P sb i)) = T_DEVICE_z) ->
  bv_unsigned (di_nlink (fs_dinode P sb i)) = 1 ->
  fs_durable_wf_view (eff_iput_free (eff_unlink_entry P sb d k i) sb i).
Proof.
  intros Hv Hp Hd Hdty Hdre Hk Hk2 Hlvk Hieq Hity Hnl1.
  assert (Hi : 0 <= i < sb_ninodes sb)
    by (exact (op_unlink_target_range P sb d k i Hv Hp Hd Hdty Hdre Hk
                 Hlvk Hieq)).
  assert (Hdin : fs_dinode (eff_unlink_entry P sb d k i) sb i
                 = di_nlink_dec (fs_dinode P sb i))
    by (exact (op_unlink_dinode P sb d k i Hv Hp Hd Hdty Hdre Hk Hlvk Hieq)).
  apply (op_iput_free_wfv (eff_unlink_entry P sb d k i) sb i).
  - exact (eff_unlink_entry_file_wfv P sb d k i Hv Hp Hd Hdty Hdre Hk Hk2
             Hlvk Hieq Hity).
  - exact (op_unlink_parse P sb d k i Hv Hp Hd Hdty Hdre Hk Hlvk Hieq).
  - exact Hi.
  - rewrite Hdin. cbn [di_type di_nlink_dec di_set_nlink].
    unfold T_FILE_z, T_DEVICE_z in Hity. lia.
  - rewrite Hdin. exact (di_nlink_dec_last _ Hnl1).
Qed.

(* ---- arm D1: a directory target (empty but for its dots) -------------- *)

(* The dir arm's two extra premises are F2's: [nlink i = 1] (only then is
   the deleted record provably [i]'s ONLY in-edge -- the invariant alone
   admits a dir with two parents) and ".." naming the parent (stranding
   the ".."-target must strand only [i]).  Both are facts sys_unlink
   holds: the [!isdirempty] test and W8. *)
Lemma op_unlink_dir_wfv (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (i : Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
  (2 <= k)%nat ->
  dir_live (fs_file_data P sb d) k ->
  bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
  i <> d ->
  bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z ->
  bv_unsigned (di_nlink (fs_dinode P sb i)) = 1 ->
  fs_dir_dots_only P (fs_dinode P sb i) ->
  bv_unsigned (dir_inum (fs_data_of P (fs_dinode P sb i)) 1) = d ->
  fs_durable_wf_view (eff_unlink_entry P sb d k i).
Proof. exact (eff_unlink_entry_dir_wfv P sb d k i). Qed.

(* ---- arm D2: the directory target, freed in the same transaction ------ *)

(* NOTE THE ASYMMETRY WITH ARM F2, and that it is not an accident: the
   directory arm needs NO extra premise, because [nlink i = 1] is already
   what [eff_unlink_entry_dir_wfv] demands.  A directory's last link is
   its parent's entry; ".." is a self-paid ticket. *)
Lemma op_unlink_dir_free_wfv (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (i : Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
  (2 <= k)%nat ->
  dir_live (fs_file_data P sb d) k ->
  bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
  i <> d ->
  bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z ->
  bv_unsigned (di_nlink (fs_dinode P sb i)) = 1 ->
  fs_dir_dots_only P (fs_dinode P sb i) ->
  bv_unsigned (dir_inum (fs_data_of P (fs_dinode P sb i)) 1) = d ->
  fs_durable_wf_view (eff_iput_free (eff_unlink_entry P sb d k i) sb i).
Proof.
  intros Hv Hp Hd Hdty Hdre Hk Hk2 Hlvk Hieq Hid Hity Hnl1 Honly Hddi.
  assert (Hi : 0 <= i < sb_ninodes sb)
    by (exact (op_unlink_target_range P sb d k i Hv Hp Hd Hdty Hdre Hk
                 Hlvk Hieq)).
  assert (Hdin : fs_dinode (eff_unlink_entry P sb d k i) sb i
                 = di_nlink_dec (fs_dinode P sb i))
    by (exact (op_unlink_dinode P sb d k i Hv Hp Hd Hdty Hdre Hk Hlvk Hieq)).
  apply (op_iput_free_wfv (eff_unlink_entry P sb d k i) sb i).
  - exact (eff_unlink_entry_dir_wfv P sb d k i Hv Hp Hd Hdty Hdre Hk Hk2
             Hlvk Hieq Hid Hity Hnl1 Honly Hddi).
  - exact (op_unlink_parse P sb d k i Hv Hp Hd Hdty Hdre Hk Hlvk Hieq).
  - exact Hi.
  - rewrite Hdin. cbn [di_type di_nlink_dec di_set_nlink].
    rewrite Hity. unfold T_DIR_z. discriminate.
  - rewrite Hdin. exact (di_nlink_dec_last _ Hnl1).
Qed.

(* ---- the failure arms ------------------------------------------------- *)

(* nameiparent fails, or [bad]: no log_write ran, so the committed view
   does not move. *)
Lemma op_unlink_bad_wfv (P : Z -> list (bv 8)) :
  fs_durable_wf_view P -> fs_durable_wf_view P.
Proof. exact (fun H => H). Qed.
