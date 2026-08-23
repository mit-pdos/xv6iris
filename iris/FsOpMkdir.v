(* ======================================================================= *)
(* FsOpMkdir.v -- durable-disk stage G2, batch (2): sys_mkdir's exit arms   *)
(* against the stage-F2 effect vocabulary (worklist §6, item G2).           *)
(*                                                                          *)
(* THE ARM INVENTORY (kernel/sysfile.c's sys_mkdir + create(), and          *)
(* [SpecSysMkdir]/[SpecCreate]):                                            *)
(*                                                                          *)
(*     uint64 sys_mkdir(void) {                                             *)
(*       begin_op();                                                        *)
(*       if (argstr(0,path,MAXPATH) < 0 ||                                  *)
(*           (ip = create(path,T_DIR,0,0)) == 0) { end_op(); return -1; }   *)
(*       iunlockput(ip); end_op(); return 0;                                *)
(*     }                                                                    *)
(*                                                                          *)
(*   ARM OK    create's [ARM C-OK], DIRECTORY copy.  Its writes, in order:  *)
(*               ialloc                IBLOCK(i) := type T_DIR              *)
(*               iupdate               IBLOCK(i) := major/minor/nlink=1     *)
(*               dirlink(ip,".",i)     balloc a data block for the child,   *)
(*                                     bzero it, write record 0, size := 16 *)
(*               dirlink(ip,"..",d)    record 1, size := 32                 *)
(*               dirlink(dp,name,i)    the parent's dirent (+ its size)     *)
(*               dp->nlink++; iupdate  the ".." back-link                   *)
(*             All six are ONE F2 effect, [eff_create_dir_entry] -- fused   *)
(*             because a typed directory without its dots block has no      *)
(*             well-formed intermediate (worklist F2, statement delta (1)). *)
(*             [op_mkdir_ok] below is the preservation lemma.               *)
(*                                                                          *)
(*   ARM argstr   no FS write                             -- IDENTITY.      *)
(*   ARM N        create's nameiparent returned 0         -- IDENTITY.      *)
(*   ARM G        create's [dp->nlink == 0] orphan guard  -- IDENTITY.      *)
(*   ARM NLINKMAX create's [type == T_DIR && dp->nlink >= NLINK_MAX] guard, *)
(*                the one that keeps the [nlink < 32767] precondition of    *)
(*                [eff_create_dir_entry] true                -- IDENTITY.   *)
(*   ARM F-BAD    the name already exists; T_DIR never takes the [F-OK]     *)
(*                exit, whose test is [type == T_FILE]      -- IDENTITY.    *)
(*   ARM A-FAIL   ialloc found no free inode                -- IDENTITY.    *)
(*                                                                          *)
(*   ARM FAIL     create's [fail:] tail -- the free-slot rewrite of        *)
(*                record [i] ([op_mkdir_fail_ok] below).  On the           *)
(*                directory copy it also frees the dots block it had just  *)
(*                allocated (iput's itrunc), so the bitmap round-trips.    *)
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
Require Import FsEffCreateEntry.
Require Import FsEffFreeInode.

Local Open Scope Z_scope.

(* ======================================================================= *)
(*  ARM OK -- the created directory                                         *)
(*                                                                          *)
(*  Two preconditions beyond [FsOpMknod]'s: the parent's [nlink] has room   *)
(*  for the ".." back-link (create's own NLINK_MAX guard supplies it), and  *)
(*  the fresh block's bitmap bit is CLEAR in the pre-transaction view --    *)
(*  which is balloc's own postcondition, and the form the committed view    *)
(*  can state (the used SET is existential inside [fs_durable_wf_view], so  *)
(*  the wrapper takes the bit, not the set membership).                     *)
(* ======================================================================= *)

Lemma op_mkdir_ok (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (name : fname) (i fb : Z) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  (* the parent: a reachable directory, nameable by a [bv 16] ".." record *)
  0 < d < sb_ninodes sb -> d < 65536 ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  (* create's NLINK_MAX guard: the ".." link fits *)
  bv_unsigned (di_nlink (fs_dinode P sb d)) < 32767 ->
  (* the child: a FREE inum *)
  0 < i < sb_ninodes sb -> i < 65536 ->
  bv_unsigned (di_type (fs_dinode P sb i)) = 0 ->
  (* the dots block: a data block whose bit balloc found CLEAR *)
  fs_data_start sb <= fb < sb_size sb ->
  fs_bit (P (sb_bmapstart sb)) fb = false ->
  (* the name, and that the parent does not already carry it *)
  (length name <= 14)%nat -> nonul name ->
  dir_first (fs_file_data P sb d)
    (dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))) name = None ->
  (* dirlink's slot in the parent *)
  ((k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat
     /\ ~ dir_live (fs_file_data P sb d) k
   \/ k = dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))
     /\ 16 * (Z.of_nat k + 1)
        <= fs_nblk (bv_unsigned (di_size (fs_dinode P sb d))) * BSIZE_z) ->
  fs_durable_wf_view (eff_create_dir_entry P sb d k name i fb).
Proof.
  intros Hv Hp Hd Hd16 Hdty Hdre Hnl Hi Hi16 Hifree Hfb Hbit Hlen Hnn
    Hnone Harm.
  exact (eff_create_dir_entry_wfv P sb d k name i fb Hv Hp Hd Hd16 Hdty Hdre
           Hnl Hi Hi16 Hifree Hfb Hbit Hlen Hnn Hnone Harm).
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

Lemma op_mkdir_fail_ok (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) = 0 ->
  fs_durable_wf_view (eff_free_slot P sb i).
Proof. exact (eff_free_slot_wfv P sb i). Qed.
