(* ======================================================================= *)
(* FsOpOpen.v -- durable-disk stage G2, batch (2): sys_open's exit arms     *)
(* against the stage-F2 effect vocabulary (worklist §6, item G2).           *)
(*                                                                          *)
(* THE ARM INVENTORY (kernel/sysfile.c's sys_open, and [SpecSysOpen] /      *)
(* [SpecCreate]'s [ok]/[made] split):                                       *)
(*                                                                          *)
(*   BEFORE begin_op                                                        *)
(*     argstr < 0                                              IDENTITY     *)
(*   INSIDE THE TRANSACTION                                                 *)
(*     O_CREATE, create == 0        (create's N/G/F-BAD/A-FAIL) IDENTITY    *)
(*     O_CREATE, create == 0        (create's FAIL tail)        see below   *)
(*     no O_CREATE, namei == 0                                 IDENTITY     *)
(*     no O_CREATE, T_DIR opened for writing                   IDENTITY     *)
(*     T_DEVICE with an out-of-range major                     IDENTITY     *)
(*     filealloc / fdalloc failed                              IDENTITY     *)
(*     SUCCESS -- four cases, by [made] and by the O_TRUNC test             *)
(*       (a) no O_CREATE (or [made = false]), no O_TRUNC       IDENTITY     *)
(*       (b) no O_CREATE (or [made = false]), O_TRUNC on a                  *)
(*           T_FILE                                     [eff_trunc]         *)
(*       (c) [made = true], no O_TRUNC              [eff_create_entry]      *)
(*           at [ty = T_FILE]                                               *)
(*       (d) [made = true] and O_TRUNC          [eff_trunc] AFTER           *)
(*                                              [eff_create_entry]          *)
(*                                                                          *)
(* Case (b) is [op_open_trunc_ok]; it covers BOTH the [namei] route and     *)
(* create's [ARM F-OK] (the name was already there and its type is          *)
(* T_FILE), which is why sys_open needs no separate [existing] lemma.       *)
(* Case (c) is [op_open_created_ok].  Case (d) is [op_open_created_trunc_ok] *)
(* -- the one arm of this batch that CHAINS two effects, and therefore the  *)
(* one that owes PRECONDITION TRANSPORT: [eff_trunc]'s hypotheses have to   *)
(* be re-established at the INTERMEDIATE view.  Section 2 does that, and    *)
(* everything it needs is the observation that the third block             *)
(* [eff_create_entry] writes -- the parent's dirent block -- is a DATA      *)
(* block, so the superblock and the child's inode block survive it.         *)
(*                                                                          *)
(* create's [fail:] tail is the one arm of the O_CREATE route that is       *)
(* not identity: it nets to the free-slot rewrite of record [i]             *)
(* ([op_open_create_fail_ok] below).                                        *)
(*                                                                          *)
(*                                                                          *)
(* A SECOND SUCCESS SUB-ARM is NOT closed here: when the parent's records   *)
(* exactly fill its last block, dirlink's writei runs bmap and ALLOCATES,   *)
(* and the create effects' append branch ([16(k+1) <= fs_nblk sz * BSIZE])  *)
(* is false -- the arm is the create effect after                           *)
(* [FsEffAllocBlock.eff_alloc_file_block].  Blocked on the effect files     *)
(* exporting nothing but [fs_durable_wf_view], so a second effect's         *)
(* [fs_reachable] premise cannot be transported: worklist G2 batch (2)      *)
(* findings (v)/(vi).                                                      *)
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
Require Import FsEffCreateEntry.
Require Import FsEffTrunc.
Require Import FsEffFreeInode.

Local Open Scope Z_scope.

(* ======================================================================= *)
(*  1.  THE TWO SINGLE-EFFECT ARMS                                          *)
(* ======================================================================= *)

(* (c) O_CREATE made a fresh regular file *)
Lemma op_open_created_ok (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (name : fname) (i : Z) (ty maj min : bv 16) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  0 < i < sb_ninodes sb -> i < 65536 ->
  bv_unsigned (di_type (fs_dinode P sb i)) = 0 ->
  (* sys_open's own literal: create(path, T_FILE, 0, 0) *)
  bv_unsigned ty = T_FILE_z ->
  (length name <= 14)%nat -> nonul name ->
  dir_first (fs_file_data P sb d)
    (dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))) name = None ->
  ((k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat
     /\ ~ dir_live (fs_file_data P sb d) k
   \/ k = dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))
     /\ 16 * (Z.of_nat k + 1)
        <= fs_nblk (bv_unsigned (di_size (fs_dinode P sb d))) * BSIZE_z) ->
  fs_durable_wf_view (eff_create_entry P sb d k name i ty maj min).
Proof.
  intros Hv Hp Hd Hdty Hdre Hi Hi16 Hifree Hty Hlen Hnn Hnone Harm.
  exact (eff_create_entry_wfv P sb d k name i ty maj min Hv Hp Hd Hdty Hdre
           Hi Hi16 Hifree (or_introl Hty) Hlen Hnn Hnone Harm).
Qed.

(* (b) O_TRUNC on a file that was already there -- the [namei] route and
   create's [ARM F-OK] alike.  sys_open's guard is [ip->type == T_FILE];
   [eff_trunc] admits T_DEVICE too (itrunc's record move is the same), so
   the weaker disjunction is what the wrapper takes. *)
Lemma op_open_trunc_ok (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) = T_FILE_z ->
  fs_durable_wf_view (eff_trunc P sb i).
Proof.
  intros Hv Hp Hi Hty.
  exact (eff_trunc_wfv P sb i Hv Hp Hi (or_introl Hty)).
Qed.

(* ======================================================================= *)
(*  2.  PRECONDITION TRANSPORT ACROSS [eff_create_entry]                     *)
(*                                                                          *)
(*  [eff_create_entry] writes three blocks: the parent's inode block, the   *)
(*  child's inode block, and the parent's dirent DATA block.  The third is  *)
(*  the only one whose address is not geometry, so it is the only one that  *)
(*  has to be located -- and the durable invariant locates it: a live       *)
(*  directory's block [k / 64] is inside [fs_data_start, sb_size) whenever  *)
(*  dirlink's slot [k] is inside the file the size already covers, which    *)
(*  is exactly the reuse-or-append disjunction the arm carries.             *)
(* ======================================================================= *)

Lemma create_dirblk_range (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  ((k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat
     /\ ~ dir_live (fs_file_data P sb d) k
   \/ k = dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))
     /\ 16 * (Z.of_nat k + 1)
        <= fs_nblk (bv_unsigned (di_size (fs_dinode P sb d))) * BSIZE_z) ->
  fs_data_start sb
  <= fs_blk_addr P (fs_dinode P sb d) (k / 64)%nat < sb_size sb.
Proof.
  intros Hv Hp Hd Hdty Hdre Harm.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  set (dn := fs_dinode P sb d) in *.
  assert (Hdlive : bv_unsigned (di_type dn) <> 0)
    by (rewrite Hdty; unfold T_DIR_z; discriminate).
  assert (Hd_rd : d ∈ rd)
    by (apply (Hrd d); split; [exact Hd | split; [exact Hdty | exact Hdre]]).
  pose proof (Hdok d Hd_rd) as Hddok. fold dn in Hddok.
  pose proof (fs_inodes_dwf_spec P sb d HW3 Hd Hdlive) as Hdok_d.
  fold dn in Hdok_d.
  pose proof (fdi_size _ _ _ Hdok_d) as Hcapd.
  pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as Hsz0.
  destruct (fdo_gran _ _ _ _ Hddok) as (qd & Hqd).
  set (szd := bv_unsigned (di_size dn)) in *.
  assert (Hsz16 : szd = 16 * Z.of_nat (dir_nrec szd)).
  { unfold dir_nrec. rewrite Z2Nat.id by (apply Z.div_pos; lia).
    rewrite Hqd, Z.div_mul by lia. lia. }
  assert (Hkwin : 16 * (Z.of_nat k + 1) <= fs_nblk szd * BSIZE_z).
  { destruct Harm as [(Hk & _) | (_ & Hk)]; [| exact Hk].
    pose proof (fs_nblk_cover szd ltac:(lia)) as Hcov.
    unfold BSIZE_z in *. lia. }
  pose proof (fs_nblk_max szd ltac:(lia) Hcapd) as Hnm.
  assert (Hkb : Z.of_nat (k / 64) < fs_nblk szd).
  { assert (Hkz : Z.of_nat k < 64 * fs_nblk szd)
      by (unfold BSIZE_z in Hkwin; lia).
    rewrite (Nat2Z.inj_div k 64). apply Z.div_lt_upper_bound; lia. }
  assert (HkM : (k / 64 < FS_MAXFILE)%nat) by lia.
  exact (blk_addr_covered P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg
           rd Hrd Hdok Hlkg Horph d (k / 64)%nat Hd Hdlive HkM Hkb).
Qed.

(* the effect leaves every block outside its three alone *)
Lemma eff_create_entry_out (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (name : fname) (i : Z) (ty maj min : bv 16) (b : Z) :
  b <> fs_blk_addr P (fs_dinode P sb d) (k / 64)%nat ->
  b <> IBLOCK (fs_inum_bv d) (sb_inodestart sb) ->
  b <> IBLOCK (fs_inum_bv i) (sb_inodestart sb) ->
  eff_create_entry P sb d k name i ty maj min b = P b.
Proof.
  intros Hb1 Hb2 Hb3.
  unfold eff_create_entry. cbv zeta.
  rewrite fs_upd_ne by exact Hb1.
  rewrite (eff_dinode_out sb _ i _ b Hb3).
  exact (eff_dinode_out sb P d _ b Hb2).
Qed.

(* THE TRANSPORT.  Both halves of [eff_trunc]'s precondition, at the view
   [eff_create_entry] leaves behind: the superblock still parses to [sb]
   (its block is neither an inode block nor a data block), and the child's
   record is [di_create ty maj min], whose type is [ty]. *)
Lemma eff_create_entry_transport (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (name : fname) (i : Z) (ty maj min : bv 16) :
  fs_sb_wf sb = true ->
  fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  0 <= i < sb_ninodes sb ->
  fs_data_start sb
  <= fs_blk_addr P (fs_dinode P sb d) (k / 64)%nat < sb_size sb ->
  fs_parse_sb (eff_create_entry P sb d k name i ty maj min) = Some sb
  /\ fs_dinode (eff_create_entry P sb d k name i ty maj min) sb i
     = di_create ty maj min.
Proof.
  intros Hsb Hp Hd Hi Hrng.
  pose proof (fs_sb_wf_ok sb Hsb) as Hok.
  destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & _ & Hnle & _).
  destruct (fs_sb_ok_meta sb Hok) as (Hm1 & Hm2 & Hm3).
  assert (HdN : 0 <= d < 16 * (sb_ninodes sb / 16 + 1)) by lia.
  assert (HiN : 0 <= i < 16 * (sb_ninodes sb / 16 + 1)) by lia.
  destruct (iblock_bounds sb Hok d HdN) as (Hibd1 & Hibd2 & Hibd3).
  destruct (iblock_bounds sb Hok i HiN) as (Hibi1 & Hibi2 & Hibi3).
  unfold fs_data_start in Hrng, Hm2, Hm3.
  split.
  - rewrite (fs_parse_sb_ext P _).
    + exact Hp.
    + apply eff_create_entry_out; unfold SB_BNO; lia.
  - transitivity (fs_dinode
                    (eff_dinode
                       (eff_dinode P sb d
                          (di_set_size (fs_dinode P sb d)
                             (Z_to_bv 32
                                (Z.max (bv_unsigned (di_size (fs_dinode P sb d)))
                                   (16 * (Z.of_nat k + 1))))))
                       sb i (di_create ty maj min)) sb i).
    + apply fs_dinode_ext.
      unfold eff_create_entry. cbv zeta. apply fs_upd_ne. lia.
    + rewrite (eff_dinode_dec sb Hok _ i (di_create ty maj min) i
                 (di_create_wf ty maj min) HiN HiN).
      rewrite decide_True by reflexivity. reflexivity.
Qed.

(* ======================================================================= *)
(*  3.  ARM (d) -- O_CREATE THEN O_TRUNC                                    *)
(*                                                                          *)
(*  create() hands sys_open a fresh, empty, zero-addressed T_FILE, and      *)
(*  [itrunc] then runs on it unconditionally.  Its record move is a no-op   *)
(*  in VALUE ([di_trunc_v (di_create ty maj min) = di_create ty maj min])   *)
(*  and it frees no block, but it DOES log_write the inode block, so the    *)
(*  arm's net effect is the COMPOSITION, not the create alone.              *)
(*  ([eff_trunc]'s bitmap half re-encodes an UNCHANGED set here; that       *)
(*  agrees with the arm because the bitmap block is always a [bm_bytes]     *)
(*  image -- [BitmapInv.bitmap_inv]'s own shape.)                           *)
(* ======================================================================= *)

Lemma op_open_created_trunc_ok (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (name : fname) (i : Z) (ty maj min : bv 16) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  0 < i < sb_ninodes sb -> i < 65536 ->
  bv_unsigned (di_type (fs_dinode P sb i)) = 0 ->
  bv_unsigned ty = T_FILE_z ->
  (length name <= 14)%nat -> nonul name ->
  dir_first (fs_file_data P sb d)
    (dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))) name = None ->
  ((k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat
     /\ ~ dir_live (fs_file_data P sb d) k
   \/ k = dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))
     /\ 16 * (Z.of_nat k + 1)
        <= fs_nblk (bv_unsigned (di_size (fs_dinode P sb d))) * BSIZE_z) ->
  fs_durable_wf_view
    (eff_trunc (eff_create_entry P sb d k name i ty maj min) sb i).
Proof.
  intros Hv Hp Hd Hdty Hdre Hi Hi16 Hifree Hty Hlen Hnn Hnone Harm.
  assert (Hsb : fs_sb_wf sb = true).
  { destruct Hv as (sb0 & Hp0 & Hsw).
    assert (Hse : sb0 = sb) by congruence. subst sb0.
    exact (fdw_sb P sb Hsw). }
  pose proof (create_dirblk_range P sb d k Hv Hp Hd Hdty Hdre Harm) as Hrng.
  destruct (eff_create_entry_transport P sb d k name i ty maj min Hsb Hp Hd
              ltac:(lia) Hrng) as (Hp' & Hty').
  apply (eff_trunc_wfv _ sb i).
  - exact (op_open_created_ok P sb d k name i ty maj min Hv Hp Hd Hdty Hdre
             Hi Hi16 Hifree Hty Hlen Hnn Hnone Harm).
  - exact Hp'.
  - lia.
  - left. rewrite Hty'. exact Hty.
Qed.

(* ======================================================================= *)
(*  create's [fail:] TAIL -- the ninth effect, wired (durable-disk F3.4)    *)
(*                                                                          *)
(*  [SpecCreate]'s FAIL member is the only one that WRITES: [ialloc] takes  *)
(*  a free slot and types it, [dirlink] then fails, and [iunlockput] drops  *)
(*  the last reference at [nlink = 0] so [iput] frees the slot again inside *)
(*  the same transaction.  The transaction's NET on the committed view is   *)
(*  therefore ONE [eff_dinode] at a slot that was free before and is free   *)
(*  after -- [FsEffFreeInode.eff_free_slot].  mknod, mkdir and open's       *)
(*  O_CREATE arm share it verbatim: the arm never reaches the parent.       *)
(* ======================================================================= *)

Lemma op_open_create_fail_ok (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) = 0 ->
  fs_durable_wf_view (eff_free_slot P sb i).
Proof. exact (eff_free_slot_wfv P sb i). Qed.
