(* ====================================================================== *)
(*  FsBootWall.v -- WHY THE ERA'S FILE-SYSTEM INSTANCE CANNOT YET BE       *)
(*  MINTED FROM THE DURABLE SNAPSHOT (durable-disk lane E-boot)            *)
(*                                                                        *)
(*  A DOCUMENTED REFUTATION, in the family of [FsDurRefute.v] and          *)
(*  [FsDurDefer.v]: nothing above depends on it, and its purpose is to     *)
(*  stop the next lane from re-deriving a mint that cannot close.          *)
(*                                                                        *)
(*  THE TASK.  durable-fs-plan.md section 5 wants the era's instance       *)
(*  minted at boot from the durable snapshot --                            *)
(*  [FsDurSnap.fs_state_of_ledger_era] off [FsDurSnap.snap_ok S D] -- in    *)
(*  place of the boot-time decoding of fs.img, so that                     *)
(*  [FsCfgBoot.fs_boot_image_wf] stops being load-bearing at every era.     *)
(*  Measured, the FILE-SYSTEM PREDICATE's own content -- the node map, the  *)
(*  records, the data and indirect blocks, the bitmap and the free pool,    *)
(*  the abstract map, and the [FsStateLink] link family -- all comes off    *)
(*  [snap_ok], once lane E-boot's two new clauses                           *)
(*  ([FsStateInode.inl_bare_free] and [FsDurSnap.sk_regdom]) are in and the *)
(*  root's keep-alive slack is added beside [sk_links] (that third one is   *)
(*  stated in the worklist and not landed, because only the mint would      *)
(*  consume it).  WHAT DOES NOT COME OFF IT AT ALL is the OLD link ledger:  *)
(*  [DirLinks.dir_links] and the inode region's flavoured columns.          *)
(*                                                                        *)
(*  THE WALL, in one sentence: the boot's ONLY constructor for a            *)
(*  directory's [DirLinks.dir_links] is the ALL-PLAIN stock                 *)
(*  [DirLinks.dir_links_of_plain], and the all-plain stock is a fact about  *)
(*  the MKFS IMAGE -- it forces every live directory to have nlink at most  *)
(*  one, and (if the directory has a dotdot record) to BE the root.  Both   *)
(*  are false at any era in which mkdir has ever run, because create's      *)
(*  mkdir arm does dp->nlink++ ([ProofCreate], +0x134) and pays for it with *)
(*  a d-FLAVOURED ticket.  Theorem [boot_plain_stock_refuted] below is that *)
(*  first half, machine-checked; [dir_links_of_plain]'s own header in       *)
(*  DirLinks.v is the second -- it says outright that a rich, post-crash    *)
(*  image would break it and that a crash model would then have to mint the *)
(*  parent registers computationally off record 1 at boot, noted there for  *)
(*  that effort and not for the one that wrote it.                          *)
(*                                                                        *)
(*  THE SAME WALL FROM THE REGION'S SIDE.  [IcacheBoot.ireg_alloc] hands    *)
(*  the region its authorities with the d-flavoured columns and the parent  *)
(*  register at ZERO, and its premise [IcacheBoot.image_dir_wl0] says no    *)
(*  PLAIN ticket names a directory ([InodeRegion.ireg_dir_wl0]).  At an era *)
(*  with a subdirectory the parent's entry names a directory, so the plain  *)
(*  stock would spend a plain ticket there and the premise fails            *)
(*  ([boot_dir_wl0_refuted]).                                              *)
(*                                                                        *)
(*  WHAT WOULD CLOSE IT, and why it is not this lane's:                     *)
(*   (a) a flavour-map-aware stock in [DirLinks] -- choose the map [F] to   *)
(*       be the indicator of records naming a DIRECTORY -- which needs the  *)
(*       TARGET's type, cross-inode information the snapshot's per-object   *)
(*       clauses deliberately do not carry, plus the exact accounting       *)
(*       nlink at most 1 + number of subdirectories;                        *)
(*   (b) the parent registers ([DirLinks.dir_par_tie]) minted at boot off   *)
(*       each directory's record 1;                                        *)
(*   (c) [ireg_alloc]'s ledger premise generalised to nonzero wdu/wdt and a *)
(*       non-None parent register.                                         *)
(*  All three live in DirLinks.v and the region's flavoured columns, which  *)
(*  durable-disk lane G is scheduled to DEMOLISH -- [IcacheEscrow.dlinks]'s *)
(*  own header says that when DirLinks.v goes, that definition loses its    *)
(*  first conjunct.  So lane G precedes lane E.                             *)
(*                                                                        *)
(*  STILL OPEN AFTER LANE G3, AND NARROWED.  G3 took S7-unlink's (D2) off   *)
(*  the ledger ([InodeRegion]'s (U1)/(U2) on the parent register replace    *)
(*  [DirView.dlc_lower]) and REFUTED the custody move 6c asked for: the     *)
(*  register's authority cannot follow the payload, because sys_link        *)
(*  re-values its unit at a [dirlink] that runs after [iunlock(ip)]         *)
(*  (fs-state.md section 6.5; witness ProofSysLink.v:2961).  So (b) is      *)
(*  still the parent registers of DirLinks and (a)/(c) are still the        *)
(*  flavoured columns: this wall is UNCHANGED and still waits on lane G's   *)
(*  6d/6e, which now wait on (D1) alone.                                    *)
(*                                                                        *)
(*  THREE FURTHER CLAUSES THE POOL NEEDS AND [snap_ok] DOES NOT CARRY --    *)
(*  all per-object, all already re-proved at every iunlock by the escrow    *)
(*  arms, none of them a cross-inode content clause, so all three are       *)
(*  admissible under plan section 4's rule and are a straightforward sweep  *)
(*  once (a)-(c) are settled.  [IcacheBoot.ipool_alloc]'s per-inum bundle   *)
(*  demands [DirView.dir_ok] (every entry's inum is inside the region),     *)
(*  [DirView.dir_dots_ix] (a live directory's records 0 and 1 ARE its dot   *)
(*  and dotdot records -- POSITIONALLY, which [FsStateInode.inl_dir_dot]    *)
(*  does not say: that clause is about the entry VIEW                       *)
(*  [FsStateInode.dir_entries], a name-to-inum gmap that is blind to which  *)
(*  record carries the name) and [DirView.dir_orphan_clean].                *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import bitvector.definitions.

Require Import DinodeEnc.    (* [dinode], [di_nlink], [di_type]           *)
Require Import DirView.      (* [dlc_bound], [dlc_count], [dcnt_false]    *)
Require Import InodeRegion.  (* [ireg_dir_wl0], [ireg_dir_ty]             *)

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(*  1.  THE ALL-PLAIN STOCK COUNTS NOTHING                                 *)
(* ---------------------------------------------------------------------- *)

(* [dlc_ctb F data k] is [dlc_dotb k && dir_liveb data k && F k], so at the
   all-plain flavour map every record is out of the count. *)
Lemma dlc_count_plain (data : nat -> list (bv 8)) (n : nat) :
  dlc_count (fun _ => false) data n = 0%nat.
Proof.
  unfold dlc_count. apply dcnt_false. intros k _.
  unfold dlc_ctb. apply andb_false_r.
Qed.

(* ...so [DirLinks.dir_links_of_plain]'s bound premise IS "this directory
   has at most one link".  Stated as an iff, because that is what makes it
   a refutation and not a missing lemma: no proof effort can weaken it. *)
Theorem plain_stock_iff_nlink_le1 (dn : dinode) (data : nat -> list (bv 8)) :
  dlc_bound (fun _ => false) dn data <-> bv_unsigned (di_nlink dn) <= 1.
Proof.
  unfold dlc_bound. rewrite dlc_count_plain. lia.
Qed.

(* THE REFUTATION.  A directory that contains a subdirectory has had
   create's mkdir arm run dp->nlink++ on it, so its count is at least two
   and the boot's only directory stock does not apply to it. *)
Theorem boot_plain_stock_refuted (dn : dinode) (data : nat -> list (bv 8)) :
  2 <= bv_unsigned (di_nlink dn) ->
  ~ dlc_bound (fun _ => false) dn data.
Proof.
  intros H2 Hb. apply plain_stock_iff_nlink_le1 in Hb. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(*  2.  ...AND THE REGION'S SIDE OF THE SAME FACT                          *)
(* ---------------------------------------------------------------------- *)

(* [IcacheBoot.ireg_alloc]'s [image_dir_wl0] premise is this clause at every
   region inum, and the plain stock spends one PLAIN ticket per live
   non-self record -- so a parent whose entry names a directory would have
   to hand that directory a plain ticket. *)
Theorem boot_dir_wl0_refuted (d : dinode) (wl : nat) :
  bv_unsigned (di_type d) = ireg_dir_ty -> (1 <= wl)%nat ->
  ~ ireg_dir_wl0 d wl.
Proof.
  intros Hty Hwl Hc. pose proof (Hc Hty). lia.
Qed.
