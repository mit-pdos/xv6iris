(* ======================================================================= *)
(* FsCfgKits.v -- THE BOOT KITS: what the era's ghost allocation hands to   *)
(* each consumption site, stated.                                           *)
(*                                                                          *)
(* WHY THIS IS ITS OWN FILE.  A kit is a HAND-OFF INVENTORY: the resources   *)
(* that exist after the era fupd has allocated the file system's ghost       *)
(* state and before the code at the other end has packaged them into the     *)
(* invariants runtime consumers use.  Its STATEMENT is vocabulary -- every   *)
(* consumption site has to name it -- while the PROOF THAT BOOT CAN PRODUCE  *)
(* IT is a one-site obligation, and those are different altitudes.  Keeping  *)
(* both in [FsCfgBoot.v] meant a file that needs only the vocabulary paid    *)
(* for the whole allocation proof: [FirstTok] uses TWO of that file's        *)
(* seventy-six declarations and dragged in [IcacheBoot] with it.             *)
(*                                                                          *)
(* This is the same split, for the same reason, that [LogDefs.v] already is  *)
(* against [LogInv.v] -- dependency-light log names, shared with layers      *)
(* that do not need the log invariant.  Measured: the twelve declarations    *)
(* below use nothing from [IcacheBoot] and nothing local to [FsCfgBoot], so  *)
(* the cut needs no proof to move with them.                                *)
(*                                                                          *)
(* WHAT IS HERE: the five kits and their accessors, in the order the boot    *)
(* walk consumes them -- kit 1 ([fs_kit_icache], spent before main+0x9e),    *)
(* kit 2 ([fs_kit_fsinit_ghost], fsinit's own inventory: the log's gnames    *)
(* at genesis, the inode region, the bio cache/dirty authorities at the raw  *)
(* disk [P], every covered-but-unspent block's bytes at the COMMITTED view   *)
(* [Pb], the byte-view invariant and the exception set [Xexc] where the two  *)
(* differ), and the three leftovers ([fs_kit_printk], [fs_kit_kalloc],       *)
(* [fs_kit_icache_rest]).  Each kit's header names the PRODUCER of every     *)
(* row; those producers, and the era fupd that runs them, stay in            *)
(* [FsCfgBoot.v], which re-exports this file so every existing spelling of   *)
(* a kit name keeps working.                                                *)
(* ======================================================================= *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac excl.
From iris.base_logic.lib Require Import invariants own ghost_map ghost_var mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvModelBytes.
(* THE ERA'S FILE-SYSTEM-STATE GHOSTS (durable-disk 2b-A / B3).  Required
   HERE, ahead of everything else, on purpose: [FsState] exports four names
   that collide with live ones ([fs_view] with [FsBlocks]', [link_auth]
   with [IcacheRef]'s ten-argument ledger, [byte_range]/[blk_owned] with
   [FsBlocks]'), and an earlier [Require Import] is exactly what lets the
   later ones win -- fs-state.md section 7's last two bullets. *)
Require Import FsState.
(* the four name records [fscfg] carries and this file must be able to spell *)
Require Import WpUart.         (* [uart_names]  *)
Require Import DiskPtsto.      (* [disk_names]  *)
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.        (* [dir_wins] / [dir_entry] -- the view is an [omap] *)
Require Import FsCrash.
Require Import LogDefs.
Require Import LogInv.
(* the era fupd's gname-only mints: the four spinlock ghosts, the buffer
   cache's whole ghost record, the page allocator's count/seal pair *)
Require Import WpLockAt.
Require Import SleepLock.      (* [sl_free_tok] / [slh_auth]: [icfg_isl]'s pair *)
Require Import BioInitAt.
Require Import KallocInv.
Require Import InodeInv.
Require Import InodeLock.   (* [inode_ok] -- the image node's readings, moved down here *)
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheEscrow.
Require Import FsBoot.
(* debt (D): the bitmap block's resource and the free pool.  [BioDefs] for
   [BSIZE] (the block size [bitmap_bytes] and [fs_bmap_set] are taken at),
   [BitmapEnc] for the encoder the equation is stated over. *)
Require Import BioDefs.
Require Import BitmapEnc.
Require Import BitmapInv.
Require Import FsStateBitmap.
Require Import FsBytesGamma.
Require Import FsImg.
Require Import FsImgBridge.
Require Import FsStateEra.     (* [era_node] / [inode_rec_local] -- the era node *)
Require Import FsCfg.          (* the record this file finally gives a value *)
Require Import Xv6G.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Local Open Scope Z_scope.

Section FsCfgKits.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId}.

  (* ==================================================================== *)
  (*  KIT 1 -- WHAT main SPENDS BEFORE +0x9e                               *)
  (* ==================================================================== *)

  (*  Consumed by [IcacheBoot.icache_boot_at] (after iinit, main+0x92),
      [BioInitAt.bio_init_at] (on binit's post, main+0x8e) and the four
      [WpLockAt.newlock_at]s (kmem / virtio_disk / itable / pr) that
      [ProofMain.mn_grp_fs] runs between +0x8e and +0xa2.  ONE opaque
      definition at the ambient names, [FsReady.fs_ready]'s own argument
      applied to the boot side; open it with [fs_kit_icache_open].

      *** WHAT (d2b) MUST ADJOIN, AND FROM WHERE ***  Every row below is a
      GHOST row, because [fs_cfg_alloc] holds no memory at all.  The
      PHYSICAL halves of the same three constructors join at the assembly
      site, and none of them can come from here:

        (P1) [icache_boot_at]'s five physical premises -- [itable_lock ↦₄ 0],
             [lock_name itable_lock "itable"], [lock_cpu itable_lock ↦₈ 0],
             the fifty [SleepLock.sl_fresh (i_lock (ientry k)) "inode"] and
             the fifty [IcacheInv.ientry_raw k].  Producer:
             [BootShared.boot_bss_carve]'s .bss rows plus iinit's own
             postcondition (the [sl_fresh]es exist only after [iinit] runs,
             fs-cfg-boot.md "What must NOT move here").
        (P2) [bio_init_at]'s physical premises -- [bcache_addr ↦₄ 0], its
             name and cpu cells, the thirty [sl_fresh (buf_lock (era_node k))]
             and the thirty zeroed [struct buf] rows, and
             [BcacheInv.bcache_lru bhead (blist 0 NBUF)].  Producer: binit's
             postcondition + [boot_bss_carve].
        (P3) each [newlock_at]'s three cells ([lk ↦₄ 0], [lock_name lk s],
             [lock_cpu lk ↦₈ 0]) and its RESOURCE: [KallocInv.kmem_res] for
             kmem (kinit's post), [DiskInv.disk_res] for virtio_disk
             ([SpecMainSecondary]'s [disk_res_boot], already at
             ProofMain.v:1346-1351), [SpecPrintk.pr_res] for pr.
        (P4) [IrefSlots.iref_slots_auth] and [iref_slots IREFSLOTS] -- NOT
             minted here: their home is [IrefSlots.iref_slots_alloc], run
             inside [BootShared.boot_shared_alloc] beside the [irefslotG]
             instance it returns.  [icache_boot_at] wants the auth; fsinit
             wants one [iref_slot] unit.  Adjoin both from the existing
             boot-shared row.

      The three PERSISTENT products of these constructors ([bio_ctx],
      [is_itable2], [itable_inv], [ic_escrows], [ic_sleeplocks], the three
      locks) go on to [SpecMainSecondary.main_deposit], not into a kit.   *)
  Definition fs_kit_icache (ICFG : icfg) (FSC : fscfg) : iProp Σ :=
    ((* --- [icache_boot_at]'s ghost premises, in its own order --- *)
     own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) ∗
     ([∗ list] k ∈ seq 0 (NINODE + NINODE), live_frac k 1%Qp) ∗
     ([∗ list] k ∈ seq 0 NINODE,
        sl_free_tok (icfg_isl k) ∗ slh_auth (icfg_isl k) None) ∗
     (* THE STOCKED POOL (R5): image-accurate before [userinit] runs, so
        that [iget] inside [namei("/")] can move the root's bundle out of
        it.  This is the row [ipool_alloc_of_image] produces. *)
     ipool_rows fsc_fs fsc_ireg fsc_cov fsc_logst (region_inums icfg_nib) ∗
     (* ...and the pool's RESIDENCY KEY, whole (durable-disk B''-esc):
        [icache_boot_at] is what turns the pair into the pool's invariant
        plus the itable lock's [ipool] conjunct. *)
     ghost_var icfg_pool 1 (∅ : gset Z) ∗
     (* ...and its IN-TRANSITION twin (durable-disk C-3b), whole: the pool
        invariant's partition needs both keys. *)
     ghost_var icfg_pext 1 (∅ : gset Z) ∗
     lock_free_tok fsc_itlock ∗
     ([∗ list] k ∈ seq 0 NINODE, ic_tok fsc_ic k) ∗
     ([∗ list] k ∈ seq 0 NINODE, ic_mid fsc_ic k) ∗
     (* the identification family at DUMMY recorded values: [ic_id] is a
        plain [ghost_var] and [icache_boot_at] re-tags every slot to the
        dev/inum words the entry cells actually hold ([ic_id_set]), so the
        era owes no image premise for it (scout verdict 3). *)
     ([∗ list] k ∈ seq 0 NINODE,
        ∃ (v : bool) (d n : mword 32), ic_id fsc_ic k 1 v d n) ∗
     (* --- [bio_init_at]'s ghost premises --- *)
     bio_free_tok fsc_bio ∗
     ([∗ set] b ∈ fsc_cov,
        pool_blk (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) b) ∗
     (* --- the four [newlock_at] ghosts --- *)
     lock_free_tok fsc_kalloc ∗
     lock_free_tok fsc_dlock ∗
     lock_free_tok fsc_printk ∗
     (* --- kinit's page count, at zero: the pair [fsc_kpages] names --- *)
     kalloc_avail fsc_kpages (Some 0%nat) ∗
     kmem_avail_auth fsc_kpages 0%nat ∗
     (* ...AND THE LOCK-WINDOW PIN (durable-disk B''-tx5), one WHOLE element
        per SLOT at [None]: [icache_boot_at]'s escrow loop puts one into
        each arm it builds.  LAST, so no destructuring pattern above moved. *)
     ([∗ list] k ∈ seq 0 NINODE, hpn_full k None) ∗
     (* ...AND THE POOL'S TRANSIT LEDGER (durable-disk C-4), whole and empty.
        LAST, for the pin's reason verbatim. *)
     ghost_var icfg_ptrn 1 (∅ : gmap Z (nat * Qp)) ∗
     (* ...AND THE POOL'S CORPSE LEDGER (durable-disk C-7), whole and empty:
        the image has no corpses.  LAST, for the transit ledger's reason. *)
     ghost_map_auth icfg_pcrp 1 (∅ : gmap Z icorpse))%I.

  Lemma fs_kit_icache_open (ICFG : icfg) (FSC : fscfg) :
    fs_kit_icache ICFG FSC -∗
      own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) ∗
      ([∗ list] k ∈ seq 0 (NINODE + NINODE), live_frac k 1%Qp) ∗
      ([∗ list] k ∈ seq 0 NINODE,
         sl_free_tok (icfg_isl k) ∗ slh_auth (icfg_isl k) None) ∗
      ipool_rows fsc_fs fsc_ireg fsc_cov fsc_logst (region_inums icfg_nib) ∗
      ghost_var icfg_pool 1 (∅ : gset Z) ∗
      ghost_var icfg_pext 1 (∅ : gset Z) ∗
      lock_free_tok fsc_itlock ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_tok fsc_ic k) ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_mid fsc_ic k) ∗
      ([∗ list] k ∈ seq 0 NINODE,
         ∃ (v : bool) (d n : mword 32), ic_id fsc_ic k 1 v d n) ∗
      bio_free_tok fsc_bio ∗
      ([∗ set] b ∈ fsc_cov,
         pool_blk (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) b) ∗
      lock_free_tok fsc_kalloc ∗
      lock_free_tok fsc_dlock ∗
      lock_free_tok fsc_printk ∗
      kalloc_avail fsc_kpages (Some 0%nat) ∗
      kmem_avail_auth fsc_kpages 0%nat ∗
      ([∗ list] k ∈ seq 0 NINODE, hpn_full k None) ∗
      ghost_var icfg_ptrn 1 (∅ : gmap Z (nat * Qp)) ∗
      ghost_map_auth icfg_pcrp 1 (∅ : gmap Z icorpse).
  Proof. iIntros "H". iExact "H". Qed.

  (* ==================================================================== *)
  (*  KIT 2 -- WHAT MUST SURVIVE TO forkret'S FIRST ARM                    *)
  (* ==================================================================== *)

  (*  [SpecFsinit.wp_fsinit_sconf_body]'s exclusive premise pile, restricted
      to the rows a fupd that holds NO MEMORY can mint.  Transported by
      widening [FirstTok.first_tok]'s left disjunct (fs-cfg-boot.md
      "Transport to forkret's first arm"); the name says GHOST so the split
      against the physical rows is explicit at the call site.

      *** WHAT (d2b) MUST ADJOIN, AND FROM WHERE ***

        (A) THE RAW CELLS fsinit and initlog write: the 32 [.bss] bytes at
            [&sb] ([∗ list] i ∈ seq 0 32, pa_add sb_base i ↦ₘ _), and
            [log_addr ↦₄ _], [lock_name_field log_addr], [lock_cpu log_addr],
            [l_start], [l_dev], [l_out], [l_cmt], [l_ncommit], [lh_n_pa],
            the thirty [lh_block i].  Producer:
            [BootShared.boot_bss_carve] / [boot_shared_alloc]'s globals row.
        (B) [LogDefs.log_mirror_born].  Producer:
            [BootShared.boot_shared_alloc] -- it is the ERA's mirror
            variable ([RiscvPtsto.mirror_name] = [era_mirror_name
            riscv_eraGS]), which [RiscvAdequacy] mints at power-on AT THE
            PICTURE OF THE DISK THE ERA BOOTS ON and whose other half its
            custody hook puts straight into [FsCrash.P_fs] (durable-disk
            1a), so this fupd cannot mint it and must not try to.
        (C) [IrefSlots.iref_slot] (one unit, for ireclaim's iget/iput pair)
            and [BioDefs.bslots 35].  Producers: the boot-shared
            [iref_slots IREFSLOTS] row, and [bio_init_at]'s POSTCONDITION
            ([bslots BSLOTS_FS] is produced at main+0x8e, not at the era) --
            so the [bslots] must be carried from kit 1's consumption site.
        (D) PAID, and it is a row below rather than an owed one:
            [BitmapInv.bitmap_inv], allocated in the era fupd from
            [BitmapInv.bitmap_res] at [used := FsImg.fs_bmap_set BSIZE
            (P fsc_bmapstart)], the bitmap block's OWN bit set.  Built by
            [bitmap_res_of_image] out of the coverage remainder, which is
            why [fs_kit_spent] now names [fs_bitmap_spent] (the bitmap
            block plus the whole free pool) -- those leave the remainder
            and enter the invariant.  Taking [used] to be the block's own
            bits is what makes the byte-level equation
            [P bmapstart = bitmap_bytes used] a THEOREM
            ([FsImg.bm_bytes_fs_bmap_set]) rather than a new image sweep.
        (E) [FsCrash.fs_crash_seam] and [RiscvPtsto.gen_cert] are
            PERSISTENT and reach fsinit through [main_deposit], not a kit.

      [ireg_inv] is persistent and also travels via [main_deposit]; it is
      here because THIS is where it is produced and it is cheap to carry. *)
  (* [P] is the era's RAW disk (the cache map and the log region read it);
     [Pb] is what the era's BYTE view was minted at -- the committed view
     [FsCrash.fr_D] -- and [Xexc] is where the two differ (durable-disk
     lane E-except).  At a clean on-disk header the two functions agree on
     the home set and [Xexc] is empty. *)
  Definition fs_kit_fsinit_ghost (ICFG : icfg) (FSC : fscfg)
      (P : Z -> list (bv 8)) (Rspent : gset Z)
      (Pb : Z -> list (bv 8)) (Xexc : gset Z) : iProp Σ :=
    ((* the log's four gnames at genesis, AT [icfg_log] -- which is what
        makes fsinit's post assemble into [FsReady.fs_ready] *)
     log_free_tok icfg_log ∗
     (* the boot shelter, carried through fsinit into ireclaim *)
     ireg_boot ∗
     ireg_reg fsc_ireg fsc_fs icfg_ist icfg_nib ∗
     (* block 1: the superblock's own block, whose bytes pin what bread
        returns to the image *)
     fsblock (fs_bytes fsc_fs) 1 (P 1) ∗
     (* initlog's FsBlocks material.  [L]/[D] are universally quantified in
        [SpecFsinit]'s contract, so an existential here is exactly right --
        with the ONE pure fact the era's own mint establishes and initlog
        needs (durable-disk 1a): the logged view IS the image, block by
        block, on the covered range.  The era's mirror is born at that same
        image, so [L] and the mirror are two readings of one thing, which is
        what turns the boot [log_state] pack's row (b) into computation. *)
     (∃ (L : gmap Z (list (bv 8))) (D : gmap Z bool),
        ⌜forall b : Z, b ∈ fsc_cov -> L !! b = Some (P b)⌝ ∗
        ghost_map_auth (fs_cache fsc_fs) 1 L ∗
        ghost_map_auth (fs_dirty fsc_fs) 1 D) ∗
     ([∗ set] z ∈ fsc_cov, z ↪[fs_dirty fsc_fs]{#(1/2)} false) ∗
     (* the log region, split as [initlog] wants it *)
     fs_chalf fsc_fs (log_hdr_bno fsc_logst) (P (log_hdr_bno fsc_logst)) ∗
     ([∗ list] i ∈ seq 0 LOGBLOCKS,
        ∃ bs : list (bv 8), fs_chalf fsc_fs (log_slot_bno fsc_logst i) bs) ∗
     (* THE BITMAP, row (D): its INVARIANT.  The block itself at its own bit
        set, plus the free pool, are carved out of the coverage remainder by
        [bitmap_res_of_image] in the era fupd and go straight into
        [BitmapInv.bitmap_inv] ([bitmap_inv_alloc]); the set is forgotten
        there and nothing downstream ever names it.  Persistent, like
        [ireg_inv] above. *)
     bitmap_reg fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size ∗
     (* THE COVERAGE REMAINDER, PAIRED: everything [cov] holds that the era
        did not spend.  At an image whose [cov] is exactly its own block
        range this is empty; it is kept because [cov] is a parameter. *)
     ([∗ set] b ∈ fsc_cov ∖ Rspent,
        fsblock (fs_bytes fsc_fs) b (Pb b)) ∗
     (* THE BYTE VIEW'S ROW, NAMED AT [Pb] (durable-disk lane E-except):
        fsinit needs it named so that [initlog] can say what the logged
        view holds on the exception set. *)
     fs_bytes_inv (fs_bytes fsc_fs) (fs_cache fsc_fs) (fs_exc fsc_fs)
                  (fs_home_set fsc_cov fsc_logst) Pb ∗
     (* ...AND THE WAL'S EXCEPTION HANDLE.  The era's mint hands the WAL the
        home blocks on which the byte view and the buffer cache disagree;
        fsinit threads it into [initlog], which empties it and seals it into
        [LogInv.log_ctx].  LAST. *)
     exc_own (fs_exc fsc_fs) Xexc)%I.

  Lemma fs_kit_fsinit_ghost_open (ICFG : icfg) (FSC : fscfg)
      (P : Z -> list (bv 8)) (Rspent : gset Z)
      (Pb : Z -> list (bv 8)) (Xexc : gset Z) :
    fs_kit_fsinit_ghost ICFG FSC P Rspent Pb Xexc -∗
      log_free_tok icfg_log ∗
      ireg_boot ∗
      ireg_reg fsc_ireg fsc_fs icfg_ist icfg_nib ∗
      fsblock (fs_bytes fsc_fs) 1 (P 1) ∗
      (∃ (L : gmap Z (list (bv 8))) (D : gmap Z bool),
         ⌜forall b : Z, b ∈ fsc_cov -> L !! b = Some (P b)⌝ ∗
         ghost_map_auth (fs_cache fsc_fs) 1 L ∗
         ghost_map_auth (fs_dirty fsc_fs) 1 D) ∗
      ([∗ set] z ∈ fsc_cov, z ↪[fs_dirty fsc_fs]{#(1/2)} false) ∗
      fs_chalf fsc_fs (log_hdr_bno fsc_logst) (P (log_hdr_bno fsc_logst)) ∗
      ([∗ list] i ∈ seq 0 LOGBLOCKS,
         ∃ bs : list (bv 8), fs_chalf fsc_fs (log_slot_bno fsc_logst i) bs) ∗
      bitmap_reg fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size ∗
      ([∗ set] b ∈ fsc_cov ∖ Rspent,
         fsblock (fs_bytes fsc_fs) b (Pb b)) ∗
      fs_bytes_inv (fs_bytes fsc_fs) (fs_cache fsc_fs) (fs_exc fsc_fs)
                   (fs_home_set fsc_cov fsc_logst) Pb ∗
      exc_own (fs_exc fsc_fs) Xexc.
  Proof. iIntros "H". iExact "H". Qed.

  (* ==================================================================== *)
  (*  KIT 1'S TWO EARLY PEELS (stage (e))                                  *)
  (* ==================================================================== *)

  (*  Three of kit 1's fifteen rows are spent BEFORE the inode-cache group:
      the "pr" lock's ghost at main+0x6a ([ProofMain.mn_grp_printk]) and the
      "kmem" lock's ghost plus kinit's genesis page count at main+0x6e
      ([ProofMain.mn_grp_kvm], through [SpecKinit]'s three premises -- debt
      (E)).  They are peeled as NAMED units rather than by opening the kit
      at main's top and handing eleven loose rows to one group: a walk group
      that names one opaque row says what it takes, and nothing has to carry
      another group's material past its own call.                          *)
  Definition fs_kit_printk (ICFG : icfg) (FSC : fscfg) : iProp Σ :=
    lock_free_tok fsc_printk.

  Definition fs_kit_kalloc (ICFG : icfg) (FSC : fscfg) : iProp Σ :=
    (lock_free_tok fsc_kalloc ∗
     kalloc_avail fsc_kpages (Some 0%nat) ∗
     kmem_avail_auth fsc_kpages 0%nat)%I.

  (*  ...and what is left, which is what [icache_boot_at] / [bio_init_at] /
      the vdisk [newlock_at] take between main+0x8e and +0xa2.             *)
  Definition fs_kit_icache_rest (ICFG : icfg) (FSC : fscfg) : iProp Σ :=
    (own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) ∗
     ([∗ list] k ∈ seq 0 (NINODE + NINODE), live_frac k 1%Qp) ∗
     ([∗ list] k ∈ seq 0 NINODE,
        sl_free_tok (icfg_isl k) ∗ slh_auth (icfg_isl k) None) ∗
     ipool_rows fsc_fs fsc_ireg fsc_cov fsc_logst (region_inums icfg_nib) ∗
     ghost_var icfg_pool 1 (∅ : gset Z) ∗
     (* ...and its IN-TRANSITION twin (durable-disk C-3b), whole: the pool
        invariant's partition needs both keys. *)
     ghost_var icfg_pext 1 (∅ : gset Z) ∗
     lock_free_tok fsc_itlock ∗
     ([∗ list] k ∈ seq 0 NINODE, ic_tok fsc_ic k) ∗
     ([∗ list] k ∈ seq 0 NINODE, ic_mid fsc_ic k) ∗
     ([∗ list] k ∈ seq 0 NINODE,
        ∃ (v : bool) (d n : mword 32), ic_id fsc_ic k 1 v d n) ∗
     bio_free_tok fsc_bio ∗
     ([∗ set] b ∈ fsc_cov,
        pool_blk (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) b) ∗
     lock_free_tok fsc_dlock ∗
     (* ...AND THE LOCK-WINDOW PIN (durable-disk B''-tx5), one WHOLE element
        per SLOT at [None]: [icache_boot_at]'s escrow loop puts one into
        each arm it builds.  LAST, so no destructuring pattern above moved. *)
     ([∗ list] k ∈ seq 0 NINODE, hpn_full k None) ∗
     (* ...AND THE POOL'S TRANSIT LEDGER (durable-disk C-4), whole and empty.
        LAST, for the pin's reason verbatim. *)
     ghost_var icfg_ptrn 1 (∅ : gmap Z (nat * Qp)) ∗
     (* ...AND THE POOL'S CORPSE LEDGER (durable-disk C-7), whole and empty:
        the image has no corpses.  LAST, for the transit ledger's reason. *)
     ghost_map_auth icfg_pcrp 1 (∅ : gmap Z icorpse))%I.

  Lemma fs_kit_icache_split (ICFG : icfg) (FSC : fscfg) :
    fs_kit_icache ICFG FSC -∗
      fs_kit_printk ICFG FSC ∗ fs_kit_kalloc ICFG FSC ∗
      fs_kit_icache_rest ICFG FSC.
  Proof.
    iIntros "H".
    iDestruct (fs_kit_icache_open with "H")
      as "(Hiref & Hlive & Hislg & Hipool & Hpkey & Hxkey & Hitlk & Htok & Hmid & Hgid &
           Hbio & Hpool & Hkmlk & Hdllk & Hprlk & Hkav & Hkauth & Hhpn & Htkey & Hckey)".
    rewrite /fs_kit_printk /fs_kit_kalloc /fs_kit_icache_rest.
    iFrame "Hprlk Hkmlk Hkav Hkauth Hiref Hlive Hislg Hipool Hpkey Hxkey Hitlk Htok
            Hmid Hgid Hbio Hpool Hdllk Hhpn Htkey Hckey".
  Qed.

  Lemma fs_kit_kalloc_open (ICFG : icfg) (FSC : fscfg) :
    fs_kit_kalloc ICFG FSC -∗
      lock_free_tok fsc_kalloc ∗
      kalloc_avail fsc_kpages (Some 0%nat) ∗
      kmem_avail_auth fsc_kpages 0%nat.
  Proof. iIntros "H". iExact "H". Qed.

  Lemma fs_kit_icache_rest_open (ICFG : icfg) (FSC : fscfg) :
    fs_kit_icache_rest ICFG FSC -∗
      own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) ∗
      ([∗ list] k ∈ seq 0 (NINODE + NINODE), live_frac k 1%Qp) ∗
      ([∗ list] k ∈ seq 0 NINODE,
         sl_free_tok (icfg_isl k) ∗ slh_auth (icfg_isl k) None) ∗
      ipool_rows fsc_fs fsc_ireg fsc_cov fsc_logst (region_inums icfg_nib) ∗
      ghost_var icfg_pool 1 (∅ : gset Z) ∗
      ghost_var icfg_pext 1 (∅ : gset Z) ∗
      lock_free_tok fsc_itlock ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_tok fsc_ic k) ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_mid fsc_ic k) ∗
      ([∗ list] k ∈ seq 0 NINODE,
         ∃ (v : bool) (d n : mword 32), ic_id fsc_ic k 1 v d n) ∗
      bio_free_tok fsc_bio ∗
      ([∗ set] b ∈ fsc_cov,
         pool_blk (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) b) ∗
      lock_free_tok fsc_dlock ∗
      ([∗ list] k ∈ seq 0 NINODE, hpn_full k None) ∗
      ghost_var icfg_ptrn 1 (∅ : gmap Z (nat * Qp)) ∗
      ghost_map_auth icfg_pcrp 1 (∅ : gmap Z icorpse).
  Proof. iIntros "H". iExact "H". Qed.

  (*  THE ONE ROW OF KIT 2 THAT main ITSELF NEEDS, peeled without spending
      the kit.  [ireg_inv] is PERSISTENT, so this is a duplication, not a
      split: [SpecUserinit]'s namei corner takes it as one of the four
      inode-cache rows (stage (e)), while the kit as a whole rides on to
      forkret's [fsinit] (stage (f)).  Stated as its own lemma so neither
      site has to know the kit's ordering.                                *)
  Lemma fs_kit_fsinit_ghost_ireg (ICFG : icfg) (FSC : fscfg)
      (P : Z -> list (bv 8)) (Rspent : gset Z)
      (Pb : Z -> list (bv 8)) (Xexc : gset Z) :
    fs_kit_fsinit_ghost ICFG FSC P Rspent Pb Xexc -∗
      ireg_reg fsc_ireg fsc_fs icfg_ist icfg_nib ∗
      fs_kit_fsinit_ghost ICFG FSC P Rspent Pb Xexc.
  Proof.
    iIntros "H".
    iDestruct (fs_kit_fsinit_ghost_open with "H")
      as "(Hlog & Hboot & #Hireg & Hb1 & Hauths & Hdty & Hhdr & Hslots &
           Hbmres & Hrem & #Hbinv & Hxo)".
    iSplitR; [iExact "Hireg" |].
    rewrite /fs_kit_fsinit_ghost.
    iFrame "Hireg Hlog Hboot Hb1 Hauths Hdty Hhdr Hslots Hbmres Hrem Hbinv Hxo".
  Qed.

  (* ...and the same peel for the equally-persistent BITMAP row, so a
     boot client (ProofMain's [first_boot_persist] assembly) reads it off
     the kit without knowing the kit's layout. *)
  Lemma fs_kit_fsinit_ghost_bitmap (ICFG : icfg) (FSC : fscfg)
      (P : Z -> list (bv 8)) (Rspent : gset Z)
      (Pb : Z -> list (bv 8)) (Xexc : gset Z) :
    fs_kit_fsinit_ghost ICFG FSC P Rspent Pb Xexc -∗
      bitmap_reg fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size ∗
      fs_kit_fsinit_ghost ICFG FSC P Rspent Pb Xexc.
  Proof.
    iIntros "H".
    iDestruct (fs_kit_fsinit_ghost_open with "H")
      as "(Hlog & Hboot & #Hireg & Hb1 & Hauths & Hdty & Hhdr & Hslots &
           #Hbmres & Hrem & #Hbinv & Hxo)".
    iSplitR; [iExact "Hbmres" |].
    rewrite /fs_kit_fsinit_ghost.
    iFrame "Hireg Hlog Hboot Hb1 Hauths Hdty Hhdr Hslots Hbmres Hrem Hbinv Hxo".
  Qed.

End FsCfgKits.
