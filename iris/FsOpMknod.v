(* ======================================================================= *)
(* FsOpMknod.v -- durable-disk stage G2, batch (2): sys_mknod's exit arms   *)
(* against the stage-F2 effect vocabulary (worklist §6, item G2).           *)
(*                                                                          *)
(* THE ARM INVENTORY (read off kernel/sysfile.c's sys_mknod and its         *)
(* callee create(), and off [SpecSysMknod]/[SpecCreate]'s contracts):       *)
(*                                                                          *)
(*     uint64 sys_mknod(void) {                                             *)
(*       begin_op();                                                        *)
(*       argint(1,&major); argint(2,&minor);                                *)
(*       if (argstr(0,path,MAXPATH) < 0 ||                                  *)
(*           (ip = create(path,T_DEVICE,major,minor)) == 0) {               *)
(*         end_op(); return -1;                 <- ARMS argstr / create-   *)
(*       }                                         failed                  *)
(*       iunlockput(ip); end_op(); return 0;    <- ARM OK                    *)
(*     }                                                                    *)
(*                                                                          *)
(*   ARM OK    create's [ARM C-OK], non-directory copy: ialloc writes the   *)
(*             type, the three halfword stores + iupdate write major/       *)
(*             minor/nlink=1, and dirlink(dp,name,ip->inum) writes the      *)
(*             parent's dirent and (for an append) its size.  That IS       *)
(*             [FsEffCreateEntry.eff_create_entry] at [ty = T_DEVICE], and  *)
(*             [op_mknod_ok] below is the preservation lemma.               *)
(*             ([sys_mknod]'s own [iunlockput] cannot free: create returns  *)
(*             the inode with nlink = 1.)                                   *)
(*                                                                          *)
(*   ARM argstr  no FS write at all -- IDENTITY, no lemma.                  *)
(*   ARM N       create's nameiparent returned 0        -- IDENTITY.        *)
(*   ARM G       create's [dp->nlink == 0] orphan guard -- IDENTITY.        *)
(*   ARM F-BAD   the name already exists (T_DEVICE never takes create's     *)
(*               [F-OK] exit, whose test is [type == T_FILE]) -- IDENTITY.  *)
(*   ARM A-FAIL  ialloc found no free inode: ialloc writes ONLY on the arm  *)
(*               that succeeds                          -- IDENTITY.        *)
(*                                                                          *)
(*   ARM FAIL    create's [fail:] tail -- NOT identity, and NOT covered by  *)
(*               F2's eight effects.  See the note at the end of this file. *)
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
(* Pure Rocq: no Iris, no [log_state].  The lemma is stated against the     *)
(* committed view and composes only F2 wrappers, so stage G1-flip can wire  *)
(* it into the arm without any of this file's reasoning.                    *)
(* ======================================================================= *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import DirentEnc.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.
Require Import FsImg.
Require Import FsWf.
Require Import FsEffCreateEntry.
Require Import FsEffFreeInode.

Local Open Scope Z_scope.

(* ======================================================================= *)
(*  ARM OK -- the created device node                                       *)
(*                                                                          *)
(*  The preconditions are the F2 wrapper's, at [ty = T_DEVICE]: decode-     *)
(*  level throughout, so the arm discharges them from the postconditions    *)
(*  it already carries (create's [ARM C-OK] payload pins the type, the      *)
(*  device pair and [nlink = 1]; dirlink's [dl16_post] pins the slot [k]    *)
(*  and the reuse-or-append disjunction; namex pins [fs_reachable]).        *)
(* ======================================================================= *)

Lemma op_mknod_ok (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (name : fname) (i : Z) (ty maj min : bv 16) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  (* the parent: a reachable directory *)
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  (* the child: a FREE inum, in the range the dirent's [bv 16] can name *)
  0 < i < sb_ninodes sb -> i < 65536 ->
  bv_unsigned (di_type (fs_dinode P sb i)) = 0 ->
  (* sys_mknod's own literal *)
  bv_unsigned ty = T_DEVICE_z ->
  (* the name, and that the parent does not already carry it *)
  (length name <= 14)%nat -> nonul name ->
  dir_first (fs_file_data P sb d)
    (dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))) name = None ->
  (* dirlink's slot: a dead record, or the append that stays in the last
     block the parent already owns *)
  ((k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat
     /\ ~ dir_live (fs_file_data P sb d) k
   \/ k = dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))
     /\ 16 * (Z.of_nat k + 1)
        <= fs_nblk (bv_unsigned (di_size (fs_dinode P sb d))) * BSIZE_z) ->
  fs_durable_wf_view (eff_create_entry P sb d k name i ty maj min).
Proof.
  intros Hv Hp Hd Hdty Hdre Hi Hi16 Hifree Hty Hlen Hnn Hnone Harm.
  exact (eff_create_entry_wfv P sb d k name i ty maj min Hv Hp Hd Hdty Hdre
           Hi Hi16 Hifree (or_intror Hty) Hlen Hnn Hnone Harm).
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

Lemma op_mknod_fail_ok (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) = 0 ->
  fs_durable_wf_view (eff_free_slot P sb i).
Proof. exact (eff_free_slot_wfv P sb i). Qed.
