(* ====================================================================== *)
(*  FsBootWall.v -- CLOSED BY durable-disk LANE G6.                        *)
(*                                                                        *)
(*  THE RECORD OF A WALL THAT NO LONGER EXISTS: why the era's file-system  *)
(*  instance could not be minted from the durable snapshot for as long as  *)
(*  the OLD LINK LEDGER was carried, and what removing the ledger did to   *)
(*  the obstruction.  Kept, as [FsDurRefute.v] and [FsDurDefer.v] are      *)
(*  kept, so that the next lane does not re-derive the mint that could     *)
(*  not close -- and so that the reason it CAN close now is written down   *)
(*  where the reason it could not used to be.                              *)
(* ---------------------------------------------------------------------- *)
(*                                                                        *)
(*  THE TASK.  durable-fs-plan.md §5 wants the era's instance minted at    *)
(*  boot from the durable snapshot -- [FsDurSnap.fs_state_of_ledger_era]   *)
(*  off [FsDurSnap.snap_ok S D] -- in place of the boot-time decoding of   *)
(*  fs.img, so that [FsCfgBoot.fs_boot_image_wf] stops being load-bearing  *)
(*  at every era.  Measured, the FILE-SYSTEM PREDICATE's own content --    *)
(*  the node map, the records, the data and indirect blocks, the bitmap    *)
(*  and the free pool, the abstract map, and the [FsStateLink] link        *)
(*  family -- all comes off [snap_ok], once lane E-boot's two new clauses  *)
(*  ([FsStateInode.inl_bare_free] and [FsDurSnap.sk_regdom]) are in and    *)
(*  the root's keep-alive slack is added beside [sk_links].                *)
(*                                                                        *)
(*  THE WALL, AS IT STOOD.  What did NOT come off [snap_ok] at all was the *)
(*  old link ledger: [DirLinks.dir_links] and the inode region's flavoured *)
(*  columns.  The boot's ONLY constructor for a directory's [dir_links]    *)
(*  was the ALL-PLAIN stock [DirLinks.dir_links_of_plain], and the         *)
(*  all-plain stock is a fact about the MKFS IMAGE -- it forces every live *)
(*  directory to have [nlink <= 1] (the count clause [DirView.dlc_bound]   *)
(*  at the all-false flavour map counts nothing) and, if the directory has *)
(*  a dotdot record, to BE the root ([DirLinks.dir_par_tie]'s root         *)
(*  exclusion).  Both are false at any era in which mkdir has ever run,    *)
(*  because create's mkdir arm does [dp->nlink++] ([ProofCreate], +0x134)  *)
(*  and pays for it with a d-FLAVOURED ticket.  The region's side of the   *)
(*  same fact: [IcacheBoot.ireg_alloc] handed the region its authorities   *)
(*  with the d columns and the parent register at ZERO, and its premise    *)
(*  [image_dir_wl0] ([InodeRegion.ireg_dir_wl0]) said no PLAIN ticket      *)
(*  names a directory -- which the plain stock violates at the first       *)
(*  subdirectory.                                                         *)
(*                                                                        *)
(*  Both halves were machine-checked here, as [boot_plain_stock_refuted]   *)
(*  ([2 <= nlink -> ~ dlc_bound (fun _ => false) dn data], an IFF away     *)
(*  from [nlink <= 1], so no proof effort could weaken it) and             *)
(*  [boot_dir_wl0_refuted].  Both statements are DELETED with the objects  *)
(*  they quantified over; the arithmetic was never the point.             *)
(*                                                                        *)
(*  HOW IT CLOSED, and it closed by DEMOLITION rather than by repair.      *)
(*  The three routes this file listed --                                   *)
(*    (a) a flavour-map-aware stock in [DirLinks] (needs the TARGET's      *)
(*        type, cross-inode information the snapshot's per-object clauses  *)
(*        deliberately do not carry, plus the exact accounting             *)
(*        [nlink <= 1 + #subdirectories]);                                 *)
(*    (b) the parent registers ([DirLinks.dir_par_tie]) minted at boot off *)
(*        each directory's record 1;                                       *)
(*    (c) [ireg_alloc]'s ledger premise generalised to nonzero [wdu]/[wdt] *)
(*        and a non-None parent register                                   *)
(*  -- were all about objects lane G6 removed.  Link counts and types are  *)
(*  ONE resource algebra now (design/fs-state.md §6½): an                  *)
(*  [auth (gmultiset ity)] per inum whose FRAGMENTS are the counted        *)
(*  dirents, so a dirent's own unit reveals its target's type and there is *)
(*  no second ledger to stock.  [IcacheEscrow.dlinks] is                    *)
(*  [FsStateInode.ent_toks_x] alone; [IcacheRef]'s element is [c]/[r] plus *)
(*  [f]/[rc]; the [fl] index is gone from [SpecIupdate]'s two link bodies. *)
(*  What the boot builds instead is what [FsCfgBoot.ent_toks_of_region]    *)
(*  already builds and [FsDurImg] section 9 already routes: ONE value      *)
(*  function [fv : Z -> ity], a key's whole pile [link_reps (count) (fv z)] *)
(*  by [FsStateLink.link_reps_add], and per-directory exactness            *)
(*  ([FsStateInode.node_exact]) at the marker set -- all per-object, and   *)
(*  all admissible under plan §4's rule.  The cross-inode reading that     *)
(*  remains ([FsDurSnap.sk_links]'s "each dirent's fragment from its       *)
(*  target's type") is the ONE the ruling sanctions and lane H removes.    *)
(*                                                                        *)
(*  THREE FURTHER CLAUSES THE POOL NEEDS AND [snap_ok] DOES NOT CARRY --   *)
(*  unchanged by G6, and still the next lane's sweep.  All per-object, all *)
(*  already re-proved at every iunlock by the escrow arms, none of them a  *)
(*  cross-inode content clause.  [IcacheBoot.ipool_alloc]'s per-inum       *)
(*  bundle demands [DirView.dir_ok] (every entry's inum is inside the      *)
(*  region), [DirView.dir_dots_ix] (a live directory's records 0 and 1 ARE *)
(*  its dot and dotdot records -- POSITIONALLY, which                      *)
(*  [FsStateInode.inl_dir_dot] does not say: that clause is about the      *)
(*  entry VIEW [FsStateInode.dir_entries], a name-to-inum gmap blind to    *)
(*  which record carries the name) and [DirView.dir_orphan_clean].         *)
(*                                                                        *)
(*  The retired ledger's own sources are kept off [_CoqProject] at         *)
(*  [iris/DirLinks.v] and [iris/IregDirBit.v]; read their headers for the  *)
(*  mechanism this file refuted.                                          *)
(* ====================================================================== *)

(* ====================================================================== *)
(*  A SECOND WALL: THE MINT'S *PLACEMENT*.  EXIT (1) IS BUILT.            *)
(*  (durable-disk lanes E-mint and E-except)                              *)
(*                                                                        *)
(*  The wall above was about the mint's VALUE side and it is down.  What   *)
(*  is written down below is the wall the same lane met next, which is     *)
(*  about WHERE the mint may run.                                         *)
(*                                                                        *)
(*  THE RULING (durable-fs-plan.md section 5) is that the era's            *)
(*  file-system instance is minted INSIDE [fsinit], after [initlog]        *)
(*  returns -- because at a header with [n > 0] the RAW home blocks are a  *)
(*  MIX of the old and the new committed values and are therefore no file  *)
(*  system at all, so no instance can be minted before [install_trans] has *)
(*  run.  The ruling adds: "the icache's slot escrows and pool are sealed  *)
(*  EMPTY at PowerOn ([iinit] needs only the lock) and stocked by the same *)
(*  mint".  The escrows are already sealed empty; THE POOL CANNOT BE.      *)
(*                                                                        *)
(*  WHY.  [userinit] runs BEFORE [fsinit] (main+0x9e; fsinit is called     *)
(*  from forkret, on the park userinit performs) and its body ends in      *)
(*  [p->cwd = namei("/")].  That walk is one [iget(ROOTDEV, ROOTINO)]      *)
(*  ([SpecNameiRootBoot]'s header says so), and [iget] at a cache miss     *)
(*  MOVES THE INUM'S POOL ROW into the slot escrow's MID arm --            *)
(*  [ProofIget.v] ~:1378, [IcacheEscrow.ipool_take_lend].  So the root's   *)
(*  row -- and, by the partition below, EVERY region inum's row -- has to  *)
(*  be in [IcacheEscrow.ipool_body] at [IcacheBoot.icache_boot_at]'s       *)
(*  ghost step, which is main+0x92, two calls before userinit and long     *)
(*  before fsinit.  A pool row is not a marker: [IcacheEscrow.ipool_ord]   *)
(*  carries [ipool_shape_np], whose allocated arm is the inode's whole     *)
(*  era-side bundle (its record proxy, its data and indirect blocks' byte  *)
(*  elements at the era's view, its [top_frag] and its [dlinks]).          *)
(*                                                                        *)
(*  The three lemmas below are the machine-checked half of that: at the    *)
(*  three EMPTY keys [icache_boot_at] is handed ([ghost_var icfg_pext 1    *)
(*  empty], [ghost_var icfg_ptrn 1 empty] and fifty DEAD identities, which *)
(*  is [IcacheEscrow.ic_ids_of_live]), [ipool_body]'s partition row FORCES *)
(*  the ordinary index to be the whole region.  There is no "unstocked"    *)
(*  state of the pool to seal.                                            *)
(*                                                                        *)
(*  THE TWO EXITS, neither of which is this lane's to take:                *)
(*                                                                        *)
(*   (1) MINT [L] AT [D] AND KEEP THE MINT AT PowerOn.  TAKEN, and the     *)
(*       WAL half of it is BUILT (lane E-except).  The era's byte view is  *)
(*       minted at the RECOVERED map rather than at the raw disk, so       *)
(*       nothing about the file system waits for [install_trans]; what     *)
(*       waits is [FsBlocks.bytes_tie], the tie between the byte view and  *)
(*       the buffer cache, false on the <= LOGSIZE pending home blocks.    *)
(*       [BioInv.pool_blk] is NOT affected -- the cache map is minted RAW, *)
(*       so the pool's pairing of a cache half with the physical disk cell *)
(*       stays honest, and the exception lands on the byte row alone.      *)
(*                                                                        *)
(*       AS BUILT: [FsBlocks.fs_bytes_body] carries an exception set [X]   *)
(*       and a function [Xv] naming what the byte view holds there;        *)
(*       [exc_own] is the WAL's exclusive handle on [X], which the         *)
(*       recovering [install_trans] shrinks one block per home [bwrite]    *)
(*       ([fsblock_install_exc]) and [initlog] spends EMPTY to persist it  *)
(*       into [exc_sealed], the permanent "recovery is done" certificate.  *)
(*       The seal rides [LogInv.log_ctx], hence [fs_bytes_any], hence      *)
(*       every runtime reader for free: the ~28 crossing sites the         *)
(*       E-recover pass measured did NOT move.  What did move is the two   *)
(*       invariants minted at PowerOn -- [BitmapInv.bitmap_inv] and        *)
(*       [InodeRegion.ireg_inv] split into a PowerOn form ([bitmap_reg],   *)
(*       [ireg_reg]) and the sealed one, built inside fsinit/forkret --    *)
(*       and the ONE pre-recovery reader, boot's [namei("/")] through      *)
(*       [iget], which takes the PowerOn form and gets its own licence     *)
(*       from the seal now carried in [IgetLic.iname]'s [BufL] row.        *)
(*       [SpecFsinit]'s clean-header premise (g) is DELETED.               *)
(*                                                                        *)
(*   (2) GIVE THE POOL AN UNMINTED ARM.  NOT TAKEN.  [ipool_shape_np]      *)
(*       gains a third, content-free arm; [iget] may move an unminted row  *)
(*       (nothing [ilock]s before fsinit); the mint inside fsinit fills    *)
(*       every row.  Its price is that the root's row is NOT in the pool   *)
(*       by then -- userinit took it -- so the mint has to reach into the  *)
(*       fifty slot escrows as well as the pool, which is the commit's own *)
(*       fifty-invariant opening ([FsCollectAll]) run in the other         *)
(*       direction, and every consumer of the pool's arms grows a case.    *)
(*                                                                        *)
(*  THE MINT'S VALUE IS CLOSED TOO (lanes E-except / E-himg).              *)
(*  [FsCfgSnap.fs_cfg_alloc_snap] takes the byte view's value [Pb] and the *)
(*  exception set, and what the boot chain hands it is the COMMITTED VIEW  *)
(*  read as a block view ([FsCrash.fs_rec_view] of the recovery record's   *)
(*  map, with [hdr_wset] its exception set), off                           *)
(*  [SystemAdequacy.fs_boot_pure] -- which delivers [fs_extent], the       *)
(*  recovery record, [FsCrash.hdr_wf] and "[exists S, snap_ok S D]" at     *)
(*  EVERY era through [RiscvAdequacy.riscv_power_adequacy]'s               *)
(*  [Hproj]/[Ppure].  The era's configuration is [S]'s own superblock and  *)
(*  region width; the two coverage readings are                            *)
(*  [FsDurSnap.snap_cov_window] and [snap_cov_below]; the snapshot-side    *)
(*  producers for [FirstTok.first_fsinit_pures] are that file's            *)
(*  [_of_snap] pair.  So [SystemAdequacy.xv6_power_adequacy] assumes the   *)
(*  image at [g]'s own disk ONCE and nothing about any later era.           *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list sets.
Require Import SailStdpp.Values.   (* [mword] *)
Require Import FsImg.              (* [ROOTINO] *)
Require Import IcacheEscrow.       (* [region_inums], [ic_live_inums]      *)
Local Open Scope Z_scope.

(* THE PARTITION ROW OF [IcacheEscrow.ipool_body], at the state
   [IcacheBoot.icache_boot_at] is handed: no inum in transition, no inum in
   the transit ledger, no slot live.  The ordinary index IS the region. *)
Lemma boot_pool_index_forced (nib : nat) (O : gset Z)
    (ids : list (bool * mword 32 * mword 32)) :
  ic_live_inums ids = ∅ ->
  region_inums nib
    = O ∪ (∅ : gset Z) ∪ dom (∅ : gmap Z (nat * Qp)) ∪ ic_live_inums ids ->
  O = region_inums nib.
Proof.
  intros Hlive Hrow.
  rewrite Hrow, Hlive, dom_empty_L, union_empty_r_L, union_empty_r_L,
          union_empty_r_L.
  reflexivity.
Qed.

(* ...so the root's row is in the pool at main+0x92, which is where
   [namei("/")] finds it.  ([IcacheEscrow.ipool_take_lend] is what moves
   it out; there is nothing else it could come from.) *)
Lemma boot_pool_holds_root (nib : nat) (O : gset Z)
    (ids : list (bool * mword 32 * mword 32)) :
  (0 < nib)%nat ->
  ic_live_inums ids = ∅ ->
  region_inums nib
    = O ∪ (∅ : gset Z) ∪ dom (∅ : gmap Z (nat * Qp)) ∪ ic_live_inums ids ->
  ROOTINO ∈ O.
Proof.
  intros Hnib Hlive Hrow.
  rewrite (boot_pool_index_forced nib O ids Hlive Hrow).
  apply region_inums_spec. unfold ROOTINO. lia.
Qed.

(* ...AND THE EMPTY POOL IS REFUTED OUTRIGHT: at [0 < nib] the region is
   inhabited, so no state of [ipool_body] with all four indices empty
   exists.  This is the statement the ruling's "sealed EMPTY at PowerOn"
   would need. *)
Lemma boot_empty_pool_refuted (nib : nat) (O X : gset Z)
    (T : gmap Z (nat * Qp)) (ids : list (bool * mword 32 * mword 32)) :
  (0 < nib)%nat ->
  region_inums nib = O ∪ X ∪ dom T ∪ ic_live_inums ids ->
  O = ∅ -> X = ∅ -> T = ∅ -> ic_live_inums ids = ∅ -> False.
Proof.
  intros Hnib Hrow HO HX HT Hlive.
  assert (Hin : ROOTINO ∈ region_inums nib)
    by (apply region_inums_spec; unfold ROOTINO; lia).
  rewrite Hrow, HO, HX, HT, Hlive, dom_empty_L, union_empty_r_L,
          union_empty_r_L, union_empty_r_L in Hin.
  exact (not_elem_of_empty ROOTINO Hin).
Qed.
