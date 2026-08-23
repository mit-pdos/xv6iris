(*  FirstTok.v -- proc.c's [static int first], AS A RESOURCE A PROCESS
    CARRIES.

    forkret's first act after [release(&p->lock)] is

        if (__atomic_load_n(&first, __ATOMIC_ACQUIRE)) { fsinit(); ...; }

    and the branch is decided by WHICH ARM OF THIS DISJUNCTION the running
    process holds.  That is the whole design: no invariant, no mask, no
    atomicity argument.  The resource decides the branch, and the two arms
    are mutually exclusive as resources, so the kernel's own "exactly one
    process ever takes it" is a theorem about ownership rather than a claim
    about scheduling.

      - [first_addr ↦₄ 1] is EXCLUSIVE.  At most one process can hold it,
        and holding it is the right to run the boot arm: fsinit, the store
        of 0, kexec("/init").  The boot chain deposits it into the FIRST
        process's block ([SpecUserinit]) and nothing else can ever have it.

      - [first_addr ↦₄□ 0 ∗ fs_ready] is PERSISTENT, hence free for every
        process forever.  A process holding it reads 0, so the [c.beqz] at
        forkret+0x24 is TAKEN and the boot arm is dead -- and it already
        has the file system it would otherwise have had to build.

    The two cannot coexist: [DfracOwn 1] and [DfracDiscarded] at one
    address are incompatible, so the moment the boot arm persists its
    store, no second holder of the exclusive arm can exist.  That is the
    one-shot, without a one-shot ghost.

    WHY [fs_ready] RIDES IN THE SECOND ARM.  forkret's tail hands the trap
    loop a residue, and the loop's bundle wants the fs environment.  In the
    boot arm forkret BUILDS it (fsinit's post, sealed by
    [FsReady.fs_ready_establish]); in the steady arm it must already have
    it, and the only honest source is the process's own block.  Carrying it
    here is what lets forkret's contract drop the [first] premise
    altogether instead of trading it for an fs premise. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import KernelText KernelDataInv.
Require Import WpLock.
Require Import FdSlots.
Require Import WpUart.
Require Import DiskInv.
Require Import BioDefs BioInv.
Require Import BlockWords.
Require Import FsBlocks.
Require Import LogDefs.
Require Import LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import FsCfg.
Require Import KallocInv.
Require Import SpecPrintk.
Require Import FileInvDefs.
Require Import ProcAvail.
(* the image side: [FsImg.fs_parse_sb] / [fs_sb_ok] / [fsimg_wf], and
   [FsImgBridge.log_region_bound].  This file's two PURE producer lemmas
   ([fs_geom_ok_of_image], [first_fsinit_pures_of_image]) live here rather
   than in [FsCfgBoot.v] as the (f) charter said: [first_fsinit_pures] is a
   definition of THIS file and [FsCfgBoot] sits below it, so stating the
   second lemma there would be a dependency cycle. *)
Require Import FsBoot.
Require Import FsImg.
Require Import FsImgBridge.
Require Import FsCfgBoot.
Require Import FsReady.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* the static [int first], at its identity-mapped kernel address.
   [SpecForkret] names the same cell; this is the definition it uses. *)
Definition first_addr : mword 64 := mword_of_int KernelSyms.first_1.

(* ====================================================================== *)
(*  0.  THE SUPERBLOCK'S 32 BYTES, DUPLICATED RATHER THAN IMPORTED         *)
(* ====================================================================== *)

(* [&sb]'s ADDRESS and [struct superblock]'s BYTE IMAGE, both spelled here
   rather than taken from [SpecFsinit].  Same rule as
   [SpecForkretPark.forkret_pc]'s: do not pull a function Spec's whole cone
   into a token definition to name one constant.  All three are
   DEFINITIONALLY EQUAL to [SpecFsinit.sb_base] / [SpecFsinit.sb_image] /
   [SpecFsinit.FSMAGIC] (identical bodies), so the seal site discharges the
   bridge by [reflexivity] -- there is no conversion step and no lemma to
   carry. *)
Definition first_sb_base : mword 64 := mword_of_int KernelSyms.sb.

Definition first_sb_image (magic fssize nblocks ninodes
                          nlog logstart inodestart bmapstart : mword 32)
    : list (bv 8) :=
  word_bytes magic ++ word_bytes fssize ++
  word_bytes nblocks ++ word_bytes ninodes ++
  word_bytes nlog ++ word_bytes logstart ++
  word_bytes inodestart ++ word_bytes bmapstart.

(* ONE FIELD'S ROUND TRIP.  [FsImg.fs_le_at] is the tree's only
   little-endian reader and [BlockWords.word_bytes] its only writer;
   [FsImg.fs_le_word_at] is the direction "the bytes assemble to the
   value", and this is the other one. *)
Lemma nth_byte_fs_le_at (bs : list (bv 8)) (o j : nat) :
  (j < 4)%nat ->
  nth_byte (Z_to_bv 32 (FsImg.fs_le_at bs o 4) : bv 32) j = bs !!! (o + j)%nat.
Proof.
  intros Hj.
  rewrite /FsImg.fs_le_at.
  rewrite (nth_byte_assemble_len 32 _ j);
    [| rewrite length_fmap length_seq; cbn; lia
     | rewrite length_fmap length_seq; exact Hj].
  destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity
                               | reflexivity | exfalso; lia].
Qed.

(* the 32-byte image at a concrete index, as [nth_byte] of the field the
   index falls in.  Thirty-two conversions and no [cbn]: both sides are
   closed applications of the SAME [w] once the index is a literal. *)
Lemma first_sb_image_lookup_total (w : nat -> bv 32) (j : nat) :
  (j < 32)%nat ->
  first_sb_image (w 0%nat) (w 1%nat) (w 2%nat) (w 3%nat)
                 (w 4%nat) (w 5%nat) (w 6%nat) (w 7%nat) !!! j
  = nth_byte (w (j / 4)%nat) (j `mod` 4)%nat.
Proof.
  intro Hj.
  destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|
                 [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    [.. | exfalso; cbn in Hj; lia]; reflexivity.
Qed.

(* ...and the whole record's round trip, which is what [FsImg.fs_parse_sb]
   answering [Some sb] MEANS about block 1's bytes.  Nothing in
   [FsImg.fsimg_wf] says this (W1 is arithmetic on the RECORD alone), so it
   is a separate image fact -- and [FsImgCheck.fsimg_parse_sb] already
   proves it at the literal image, so it costs the adequacy cone no new
   computation. *)
Lemma first_sb_image_of_le (bs : list (bv 8)) :
  (32 <= length bs)%nat ->
  take 32 bs =
    first_sb_image (Z_to_bv 32 (FsImg.fs_le_at bs 0 4))
                   (Z_to_bv 32 (FsImg.fs_le_at bs 4 4))
                   (Z_to_bv 32 (FsImg.fs_le_at bs 8 4))
                   (Z_to_bv 32 (FsImg.fs_le_at bs 12 4))
                   (Z_to_bv 32 (FsImg.fs_le_at bs 16 4))
                   (Z_to_bv 32 (FsImg.fs_le_at bs 20 4))
                   (Z_to_bv 32 (FsImg.fs_le_at bs 24 4))
                   (Z_to_bv 32 (FsImg.fs_le_at bs 28 4)).
Proof.
  intros Hlen.
  pose (w := fun k : nat => Z_to_bv 32 (FsImg.fs_le_at bs (4 * k)%nat 4)).
  assert (Hw : forall k j : nat, (j < 4)%nat ->
            nth_byte (w k) j = bs !!! (4 * k + j)%nat).
  { intros k j Hj. rewrite /w. exact (nth_byte_fs_le_at bs (4 * k)%nat j Hj). }
  change (Z_to_bv 32 (FsImg.fs_le_at bs 0 4)) with (w 0%nat).
  change (Z_to_bv 32 (FsImg.fs_le_at bs 4 4)) with (w 1%nat).
  change (Z_to_bv 32 (FsImg.fs_le_at bs 8 4)) with (w 2%nat).
  change (Z_to_bv 32 (FsImg.fs_le_at bs 12 4)) with (w 3%nat).
  change (Z_to_bv 32 (FsImg.fs_le_at bs 16 4)) with (w 4%nat).
  change (Z_to_bv 32 (FsImg.fs_le_at bs 20 4)) with (w 5%nat).
  change (Z_to_bv 32 (FsImg.fs_le_at bs 24 4)) with (w 6%nat).
  change (Z_to_bv 32 (FsImg.fs_le_at bs 28 4)) with (w 7%nat).
  apply (list_eq_same_length _ _ 32%nat);
    [reflexivity | rewrite length_take; lia |].
  intros i x y Hi Hx Hy.
  assert (Hbx : bs !! i = Some x) by (apply lookup_take_Some in Hx; tauto).
  rewrite -(list_lookup_total_correct _ _ _ Hbx).
  rewrite -(list_lookup_total_correct _ _ _ Hy).
  rewrite (first_sb_image_lookup_total w i Hi) (Hw (i / 4)%nat (i `mod` 4)%nat
            (Nat.mod_upper_bound i 4 ltac:(lia))).
  f_equal; first [apply Nat.div_mod_eq | symmetry; apply Nat.div_mod_eq].
Qed.

(* ONE INODE BLOCK IS INSIDE THE REGION.  Stated over [bv 32] and not over
   [mword 32]: [DinodeEnc.IBLOCK]'s body spells [bv_unsigned] at the [bv]
   index, and a caller's [mword 32] elaborates the SAME projection at a
   different (convertible, not syntactically equal) implicit -- which
   [exact]/[apply] see through and [lia] does not.  Doing the division here
   is what keeps the caller's arithmetic linear in [IBLOCK] as an atom. *)
Lemma IBLOCK_in_range (w : bv 32) (ist n : Z) :
  0 <= n -> bv_unsigned w < 16 * n -> ist <= IBLOCK w ist < ist + n.
Proof.
  intros Hn Hw. rewrite /IBLOCK.
  pose proof (bv_unsigned_in_range _ w) as [Hw0 _].
  split.
  - assert (0 <= bv_unsigned w / 16) by (apply Z.div_pos; lia). lia.
  - assert (bv_unsigned w / 16 < n) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Section FirstTok.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.
  Context `{!xv6G Σ, !bioslotG Σ} `{ICFG : icfg}.

  (* ================================================================== *)
  (*  1.  THE PERSISTENT HALF -- what main has built by +0x9e             *)
  (* ================================================================== *)

  (* SIXTEEN ROWS, ALL PERSISTENT: exactly [FsReady.fs_ready_pre] MINUS the
     three conjuncts main cannot have at +0x9e -- [log_ctx] (initlog builds
     it, inside fsinit), [kalloc_avail _ None] (the seal is only possible
     after allocproc's last counted draw, so it is minted in userinit and
     rides [first_tok] as its own row -- (f-4)), and [fs_sb_cells] (fsinit's
     [memmove] is what creates them).  [first_persist_pre] below is the
     converse: those three, plus this, ARE the pre.

     WHY THIS IS A BUNDLE AND NOT THE BOOT KIT.  The seal site destructures
     against TWO different shapes -- [SpecFsinit]'s premise order, then
     [fs_ready_pre]'s conjunct order -- and the kit is indexed by era-side
     data ([P], [Rspent], [dk], [sb]) forkret must never mention.  Splitting
     by PRODUCTION SITE rather than by persistence is what keeps the two
     halves each destructurable in one step. *)
  Definition first_boot_persist : iProp Σ :=
    (kernel_text ∗ kernel_data ∗
     printk_env fsc_printk fsc_uart fsc_disk ∗
     ⌜printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk⌝ ∗
     bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) ∗
     fs_crash_seam fsc_cov fsc_logst ∗ gen_cert ∗
     dev_inv fsc_uart fsc_disk ∗
     (∃ pd pav pu : mword 64,
        disk_geom fsc_disk pd pav pu ∗
        is_lock fsc_dlock d_lock "virtio_disk"%string
                (disk_res fsc_disk pd pav pu)) ∗
     is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst
                icfg_nib icfg_dev ∗
     itable_inv ∗
     ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst ∗
     ic_sleeplocks fsc_ic ∗
     ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib ∗
     bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size ∗
     is_lock fsc_kalloc (mword_of_int KernelSyms.kmem) "kmem"%string
       (kmem_res fsc_kpages (mword_of_int (KernelSyms.kmem + 24))) ∗
     ⌜fs_geom_ok⌝)%I.

  Global Instance first_boot_persist_persistent : Persistent first_boot_persist.
  Proof. rewrite /first_boot_persist. apply _. Qed.

  (* sealed for [FsReady.fs_ready]'s own measured reason: leaving a
     sixteen-conjunct persistent bundle transparent lets instance resolution
     delta-unfold it against [fs_ready_pre]'s nineteen. *)
  Typeclasses Opaque first_boot_persist.

  (* ================================================================== *)
  (*  2.  THE PURE BLOCK                                                  *)
  (* ================================================================== *)

  (* [SpecFsinit]'s hypotheses (a), (b), (g) and its two block-1 coverage
     corners -- and NOTHING ELSE, because (c)/(d)/(e)/(f) and [log_geom_ok]
     are all projections of [FsReady.fs_geom_ok] (its [fgo_*] accessors
     exist for exactly this) and [fs_geom_ok] rides the persistent bundle
     above.

     [sb] is a parameter and not read: it is here so the pure block is
     indexed by the SAME pair the resource bundle's existential binds, which
     is what lets one [iDestruct] name both. *)
  Definition first_fsinit_pures (dk : Z -> bv 8) (sb : FsImg.fs_sb) : Prop :=
    (exists v_magic v_nblocks v_nlog : mword 32,
        take 32 (FsCrash.fs_blocks dk 1)
        = first_sb_image v_magic (mword_of_int fsc_size) v_nblocks
            (mword_of_int fsc_ninodes) v_nlog (mword_of_int fsc_logst)
            (mword_of_int icfg_ist) (mword_of_int fsc_bmapstart)
        /\ bv_unsigned v_magic = FsImg.FSMAGIC)
    /\ hdr_n (FsCrash.fs_blocks dk (log_hdr_bno fsc_logst)) = 0
    /\ (1 : Z) ∈ fsc_cov
    /\ ~ ((1 : Z) ∈ log_region_set fsc_logst).

  (* ================================================================== *)
  (*  3.  THE EXCLUSIVE HALF -- [SpecFsinit]'s premise pile               *)
  (* ================================================================== *)

  (* The era data is QUANTIFIED HERE, which is the whole point: forkret's
     walk names neither the image nor the spent set, and the kit rides
     inside opaquely.

     ROWS.  The pure block; kit 2 (TEN rows since (f0): the log free token,
     [ireg_boot], [ireg_inv], block 1's [fs_chalf], the [fs_cache]/[fs_dirty]
     auths, the dirty halves, the log header + slots, [bitmap_inv], the
     coverage remainder); rows (A) -- the 32 raw [&sb] bytes and the whole
     [struct log], carved in [BootShared.boot_bss_carve]; row (B) --
     [LogDefs.log_mirror_born], the ERA's mirror half at the disk's own
     picture plus the swap receipt; row (C) --
     [IrefSlots.iref_slots 2] and the 35 [bslots], neither of which the era
     fupd can mint ([bio_init_at] produces the slots at main+0x8e).

     ROW (D) IS GONE.  (f0) landed the bitmap INSIDE kit 2
     ([FsCfgBoot.fs_kit_fsinit_ghost]'s ninth row, now the persistent
     [BitmapInv.bitmap_inv]), so the standalone row the charter listed is
     deleted and the kit's spelling governs.  [bslots] did NOT move inside the kit -- it is
     produced at WP time -- so row (C) stays. *)
  Definition first_fsinit : iProp Σ :=
    (∃ (dk : Z -> bv 8) (sb : FsImg.fs_sb)
       (vlock v_start v_dev v_nc v_n : mword 32) (vname vcpu : mword 64)
       (sb_old : nat -> bv 8),
       ⌜first_fsinit_pures dk sb⌝ ∗
       fs_kit_fsinit_ghost _ _ (FsCrash.fs_blocks dk)
         (fs_kit_spent (FsCrash.fs_blocks dk) sb icfg_nib
            (FsImg.fs_live_set (FsCrash.fs_blocks dk) sb)) ∗
       (* rows (A): the raw cells fsinit / initlog write *)
       ([∗ list] i ∈ seq 0 32, pa_add first_sb_base i ↦ₘ sb_old i) ∗
       log_addr ↦₄ vlock ∗
       lock_name_field log_addr ↦₈ vname ∗ lock_cpu log_addr ↦₈ vcpu ∗
       l_start ↦₄ v_start ∗ l_dev ↦₄ v_dev ∗
       l_out ↦₄ (mword_of_int 0 : mword 32) ∗
       l_cmt ↦₄ (mword_of_int 0 : mword 32) ∗
       l_ncommit ↦₄ v_nc ∗ lh_n_pa ↦₄ v_n ∗
       ([∗ list] i ∈ seq 0 LOGBLOCKS, ∃ w : mword 32, lh_block i ↦₄ w) ∗
       (* row (B), value-bearing (durable-disk 1a): the era's mirror HALF at
          the picture of the disk this bundle is indexed by, plus the swap
          receipt.  PowerOn allocated it there and put the other half into
          [FsCrash.P_fs]'s custody arm in the same fupd, so there is no boot
          swap left to do and nothing on the boot path re-bases [fr_D]. *)
       log_mirror_born (FsCrash.mirror_of (FsCrash.fs_blocks dk)) ∗
       (* row (C) *) iref_slots 2 ∗
       bslots ((LOGBLOCKS + 2) + 2 + 1)%nat)%I.

  (* ONE [iDestruct], in [SpecFsinit]'s own premise order (kit 2 opened
     inside), so the seal site never has to know either bundle's layout. *)
  Lemma first_fsinit_open :
    first_fsinit -∗
      ∃ (dk : Z -> bv 8) (sb : FsImg.fs_sb)
        (vlock v_start v_dev v_nc v_n : mword 32) (vname vcpu : mword 64)
        (sb_old : nat -> bv 8),
        ⌜first_fsinit_pures dk sb⌝ ∗
        log_mirror_born (FsCrash.mirror_of (FsCrash.fs_blocks dk)) ∗
        log_free_tok icfg_log ∗
        fsblock (fs_bytes fsc_fs) 1 (FsCrash.fs_blocks dk 1) ∗
        ([∗ list] i ∈ seq 0 32, pa_add first_sb_base i ↦ₘ sb_old i) ∗
        ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib ∗
        ireg_boot ∗
        bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size ∗
        log_addr ↦₄ vlock ∗
        lock_name_field log_addr ↦₈ vname ∗ lock_cpu log_addr ↦₈ vcpu ∗
        l_start ↦₄ v_start ∗ l_dev ↦₄ v_dev ∗
        l_out ↦₄ (mword_of_int 0 : mword 32) ∗
        l_cmt ↦₄ (mword_of_int 0 : mword 32) ∗
        l_ncommit ↦₄ v_nc ∗ lh_n_pa ↦₄ v_n ∗
        ([∗ list] i ∈ seq 0 LOGBLOCKS, ∃ w : mword 32, lh_block i ↦₄ w) ∗
        (∃ (L : gmap Z (list (bv 8))) (D : gmap Z bool),
           ⌜forall b : Z, b ∈ fsc_cov ->
              L !! b = Some (FsCrash.fs_blocks dk b)⌝ ∗
           ghost_map_auth (fs_cache fsc_fs) 1 L ∗
           ghost_map_auth (fs_dirty fsc_fs) 1 D) ∗
        ([∗ set] z ∈ fsc_cov, z ↪[fs_dirty fsc_fs]{#(1/2)} false) ∗
        fs_chalf fsc_fs (log_hdr_bno fsc_logst)
                (FsCrash.fs_blocks dk (log_hdr_bno fsc_logst)) ∗
        ([∗ list] i ∈ seq 0 LOGBLOCKS,
           ∃ bs : list (bv 8), fs_chalf fsc_fs (log_slot_bno fsc_logst i) bs) ∗
        bslots ((LOGBLOCKS + 2) + 2 + 1)%nat ∗
        iref_slots 2 ∗
        (* the coverage remainder, which fsinit does not take: it is the
           first process's, R3 *)
        ([∗ set] b ∈ fsc_cov ∖ fs_kit_spent (FsCrash.fs_blocks dk) sb icfg_nib
                                 (FsImg.fs_live_set (FsCrash.fs_blocks dk) sb),
           fsblock (fs_bytes fsc_fs) b (FsCrash.fs_blocks dk b) ∗ blk_own fsc_fs b).
  Proof.
    iIntros "H". rewrite /first_fsinit.
    iDestruct "H" as (dk sb vlock v_start v_dev v_nc v_n vname vcpu sb_old)
      "(%Hp & Hkit & Hsb & Hlk & Hnm & Hcpu & Hst & Hdv & Hout & Hcmt &
        Hnc & Hn & Hblk & Hmir & Hiref & Hbsl)".
    iDestruct (fs_kit_fsinit_ghost_open with "Hkit")
      as "(Hlog & Hboot & #Hireg & Hb1 & Hauths & Hdty & Hhdr & Hslots &
           Hbmres & Hrem)".
    iExists dk, sb, vlock, v_start, v_dev, v_nc, v_n, vname, vcpu, sb_old.
    iFrame "Hmir Hlog Hb1 Hsb Hireg Hboot Hbmres Hlk Hnm Hcpu Hst Hdv Hout
            Hcmt Hnc Hn Hblk Hauths Hdty Hhdr Hslots Hbsl Hiref Hrem".
    iPureIntro. exact Hp.
  Qed.

  (* ================================================================== *)
  (*  4.  THE TOKEN                                                       *)
  (* ================================================================== *)

  (* THE ALLOCATOR ROW IS THE *BUNDLE*, NOT THE SPELLED PAIR, and the
     spelling is forced by WHO CAN PRODUCE IT (fs-cfg-boot.md (f-4), debt F,
     and its successor decision point D4).

     [fs_ready_pre] row 17 wants [kalloc_avail fsc_kpages None] -- the pair
     NAMED.  Nobody can hand that over.  The seal is
     [KallocInv.kalloc_avail_seal], which consumes the EXCLUSIVE counted
     token; the last counted draw in the whole boot is allocproc's, inside
     userinit; and what allocproc gives back is [KvmSpec.kalloc_env], whose
     [∃ γk] has already swallowed the name ([WpLock.is_lock] has no
     resource-agreement lemma, so no equation recovers it).  So the earliest
     moment the sealed regime EXISTS, it exists only in bundled form -- and
     the token has to carry what its one producer can produce, or userinit's
     park cannot be typed at all.

     WHAT THIS LEAVES OPEN, precisely: [first_persist_pre] below still takes
     [kalloc_avail fsc_kpages None] as its own argument, because
     [FsReady.fs_ready_pre] still spells it.  Bridging the two is exactly
     debt F / D4 (spell the pair through allocproc, or relax [fs_ready]'s
     rows 16+17 to this same bundle) and it is a separate, chartered change:
     [fs_ready]'s spelled pair is re-exported by
     [ProofSyscall.sysc_fs_env], so relaxing it moves the fileclose cone.

     THAT RESIDUAL IS GONE, and the row below is how.  What used to stand
     here said the token carries the bundle and that one named row was still
     owed at a seal site that did not exist yet.  The seal site exists now
     (forkret's boot arm), and the fix was not to bridge the two forms but
     to store the right one.

     THE ALLOCATOR ROW IS THE NAMED HALF, NOT [KvmSpec.kalloc_env], and the
     bundle was never the right thing to store.  [kalloc_env]'s [∃ γk]
     swallows the free-list name, and [WpLock.is_lock] is an [inv] -- Iris
     invariants do not agree -- so nothing recovers [γk = fsc_kpages].  The
     boot arm's whole point is the SEAL, and [FsReady.fs_ready_pre]'s row 17
     spells the pair named; a hidden name can never satisfy it.  Worse, the
     bundle's own [is_lock] duplicated the one [first_boot_persist] already
     carries at the real name, so the row was paying for a copy of a fact it
     had and hiding the one fact it needed.

     Nothing derives the BUNDLE from this, because nothing has to: the only
     consumer of the bundled form on this arm is kexec, which runs after the
     seal and takes it from [FsReady.fs_ready_kalloc].

     THE PRODUCER PAYS FOR IT WITH ONE [iDestruct].  [KvmSpec.kalloc_env]
     no longer quantifies the free-list pair -- it names [fsc_kpages], which
     is what [FsCfg]'s own note on that field says it should do and what
     makes the bundle "recovered as a projection" true in both directions.
     So [ProofUserinit], which holds the bundle when it deposits the token,
     projects this row straight out of it.  Before that change the row was
     unreachable from a bundle at all ([WpLock.is_lock] is an [inv], and
     Iris invariants do not agree), which is the whole reason the pinning
     happened. *)
  Definition first_tok : iProp Σ :=
    ((first_addr ↦₄ (mword_of_int 1 : mword 32)
        ∗ first_boot_persist ∗ kalloc_avail fsc_kpages None ∗ first_fsinit)
     ∨ (first_addr ↦₄□ (mword_of_int 0 : mword 32) ∗ fs_ready))%I.

  (* the steady-state arm is persistent, so a process that has booted can
     hand a copy to every process it creates -- which is how kfork pays the
     child's block without the parent losing anything. *)
  Lemma first_tok_done : first_addr ↦₄□ (mword_of_int 0 : mword 32) -∗ fs_ready -∗ first_tok.
  Proof. iIntros "H #F". iRight. iFrame "H F". Qed.

  (* ...AND THAT ARM AS A NAME OF ITS OWN.  [first_tok] now rides inside
     [ProcInv.proc_priv], and the parent's copy is NOT duplicable -- its boot
     arm is exclusive -- so fork, which has to build a SECOND block, cannot
     pay the child out of its own.  What it can carry is this: the steady
     arm alone, persistent, hence free to hand to every child forever.

     WHERE IT COMES FROM.  It is a conjunct of [ProofSyscall.syscall_env],
     the ambient bundle usertrap hands the dispatcher, and it is threaded
     [SpecSysFork] -> [SpecKfork] -> [kfork_arm3] -> [kfk_b4], where
     [first_tok_of_done] mints the child's token.  Nothing in the tree
     CONSTRUCTS [syscall_env] today (it arrives abstractly as usertrap's
     [Rsys]), so the obligation to produce this row lands exactly where
     forkret will discharge it: forkret's boot arm persists the store and
     seals the file system, and its steady arm already holds both halves. *)
  Definition first_done : iProp Σ :=
    (first_addr ↦₄□ (mword_of_int 0 : mword 32) ∗ fs_ready)%I.

  Global Instance first_done_persistent : Persistent first_done.
  Proof. rewrite /first_done. apply _. Qed.

  Lemma first_tok_of_done : first_done -∗ first_tok.
  Proof. iIntros "[H F]". iRight. iFrame "H F". Qed.

  (* THE DESTRUCTOR, so that forkret's walk never has to unfold the seal.
     [first_tok] is [Typeclasses Opaque] for a correctness reason (see the
     note at the bottom of this file), and a walk that opens it with
     [rewrite /first_tok] loses that protection for the rest of the proof.
     This hands the two arms out by name instead: the boot arm's four rows
     in the order the seal site wants them, or [first_done]. *)
  Lemma first_tok_open :
    first_tok -∗
      (first_addr ↦₄ (mword_of_int 1 : mword 32)
         ∗ first_boot_persist ∗ kalloc_avail fsc_kpages None ∗ first_fsinit)
      ∨ first_done.
  Proof.
    iIntros "H". rewrite /first_tok. iDestruct "H" as "[H | H]".
    - iLeft. iExact "H".
    - iRight. iExact "H".
  Qed.

  Lemma first_tok_boot :
    first_addr ↦₄ (mword_of_int 1 : mword 32) -∗
    first_boot_persist -∗ kalloc_avail fsc_kpages None -∗ first_fsinit -∗
    first_tok.
  Proof. iIntros "H #P #K F". iLeft. iFrame "H P K F". Qed.

  (* THE SEAL SITE'S WHOLE fs ASSEMBLY, one wand: the sixteen persistent
     rows main built, the count userinit sealed, and the two things fsinit
     itself returns.  What is left at the seal is
     [FsReady.fs_ready_establish] with fsinit's [ireg_boot]. *)
  Lemma first_persist_pre :
    first_boot_persist -∗ kalloc_avail fsc_kpages None -∗
    log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
    fs_sb_cells -∗ fs_ready_pre.
  Proof.
    iIntros "HP HK HL #HC". rewrite /fs_ready_pre /first_boot_persist.
    iDestruct "HP" as "(H1 & H2 & H3 & %H4 & H5 & H7 & H8 & H9 & H10 & H11 &
                        H12 & H13 & H14 & H15 & H16 & H17 & %H18)".
    iFrame "H1 H2 H3 H5 HL H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 HK HC".
    iFrame "%".
  Qed.

  (* THE TWO ARMS ARE MUTUALLY EXCLUSIVE, and this is the lemma that says
     the boot arm runs at most once.  Not used by forkret's walk (which
     cases on its OWN token) -- it is here because it is the property the
     design rests on, and a reader should be able to check it. *)
  Lemma first_tok_boot_excl :
    first_addr ↦₄ (mword_of_int 1 : mword 32) -∗
    first_addr ↦₄□ (mword_of_int 0 : mword 32) -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (word4_pointsto_agree with "H1 H2") as %Hv.
    exfalso. revert Hv. vm_compute. discriminate.
  Qed.

  (* ================================================================== *)
  (*  5.  THE TWO PURE PRODUCERS, off the image hypothesis                *)
  (* ================================================================== *)

  (* [FsReady.fs_geom_ok]'s eleven fields out of [BootShared.fs_boot_image_wf]
     and [FsCfgBoot.fs_boot_supply]'s ties.  Nothing here is new about the
     image: every field is either a tie, a projection of [FsImg.fs_sb_ok]
     (W1), or [FsBoot.fs_cov_in] read through [IcacheInv.cov_below_of_image].

     TWO PREMISES ARE TIGHTER THAN THE ERA'S.  [fgo_ushort] wants
     [16*nib <= 2^16] where [fs_cfg_alloc] threads only [2^32], and
     [cov_below] wants the disk image to be no larger than [size] blocks;
     both are true of the mkfs image (208 <= 65536; 2048000 = 1024*2000) and
     both are threaded exactly the way [0 < nib] is -- as conjuncts of
     [fs_boot_image_wf], discharged in [FsAdequacyImg]. *)
  (* THE DURABLE DISK'S EXTENT, off the image: every covered block and
     every log-region block lies inside the [ndisk] bytes.  What the crash
     predicate's fragments are stated over ([FsCrash.P_fs_named]). *)
  Lemma fs_extent_of_image (dk : Z -> bv 8) (ndisk : nat)
      (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z) :
    FsImg.fsimg_wf (FsCrash.fs_blocks dk) sb = true ->
    Z.of_nat nib = FsImg.sb_ninodes sb / 16 + 1 ->
    FsBoot.fs_cov_in cov ndisk ->
    (forall b : Z, 1 <= b < FsImg.fs_data_start sb -> b ∈ cov) ->
    FsCrash.fs_extent cov (FsImg.sb_logstart sb) ndisk.
  Proof.
    intros Hwf Hnibeq Hcovin Hcovmeta.
    pose proof (FsImg.fsimg_wf_sb _ _ Hwf) as Hsb.
    pose proof (FsImg.sbo_logstart sb Hsb) as Hls.
    pose proof (FsImg.sbo_nlog sb Hsb) as Hnl.
    pose proof (FsImg.sbo_inodestart sb Hsb) as Hist.
    pose proof (FsImg.sbo_bmapstart sb Hsb) as Hbms.
    pose proof (FsImg.sbo_ninodes sb Hsb) as Hni.
    unfold FsImg.ROOTINO in Hni.
    assert (Hdiv : 0 <= FsImg.sb_ninodes sb / 16) by (apply Z.div_pos; lia).
    assert (Hds : FsImg.fs_data_start sb = FsImg.sb_bmapstart sb + 1)
      by reflexivity.
    assert (Hbm : FsImg.sb_bmapstart sb = 33 + Z.of_nat nib) by lia.
    rewrite Hds Hbm in Hcovmeta.
    assert (Hincov : forall b, b ∈ cov -> 0 <= b /\ (b + 1) * Z.of_nat BSIZE <= Z.of_nat ndisk).
    { intros b Hb. destruct (Hcovin b Hb) as [Hb0 Hbn]. unfold BSIZE. lia. }
    intros b Hb. rewrite elem_of_union in Hb. destruct Hb as [Hb | Hb].
    - exact (Hincov b Hb).
    - apply Hincov.
      pose proof (log_region_bound (FsImg.sb_logstart sb) b Hb) as Hbb.
      unfold LOGBLOCKS in Hbb. apply Hcovmeta. lia.
  Qed.

  Lemma fs_geom_ok_of_image (dk : Z -> bv 8) (ndisk : nat)
      (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z) :
    FsImg.fsimg_wf (FsCrash.fs_blocks dk) sb = true ->
    FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
    16 * Z.of_nat nib <= 2 ^ 16 ->
    (0 < nib)%nat ->
    Z.of_nat nib = FsImg.sb_ninodes sb / 16 + 1 ->
    FsBoot.fs_cov_in cov ndisk ->
    Z.of_nat ndisk <= 1024 * FsImg.sb_size sb ->
    (forall b : Z, 1 <= b < FsImg.fs_data_start sb -> b ∈ cov) ->
    icfg_dev = ROOTDEV -> icfg_nib = nib ->
    icfg_ist = FsImg.sb_inodestart sb ->
    fsc_cov = cov -> fsc_logst = FsImg.sb_logstart sb ->
    fsc_bmapstart = FsImg.sb_bmapstart sb ->
    fsc_size = FsImg.sb_size sb -> fsc_ninodes = FsImg.sb_ninodes sb ->
    fs_geom_ok.
  Proof.
    intros Hwf Hnin Hush Hnib0 Hnibeq Hcovin Hnd Hcovmeta
           Hdevq Hnibq Histq Hcovq Hlogq Hbmq Hszq Hninq.
    pose proof (FsImg.fsimg_wf_sb _ _ Hwf) as Hsb.
    pose proof (FsImg.sbo_logstart sb Hsb) as Hls.
    pose proof (FsImg.sbo_nlog sb Hsb) as Hnl.
    pose proof (FsImg.sbo_inodestart sb Hsb) as Hist.
    pose proof (FsImg.sbo_bmapstart sb Hsb) as Hbms.
    pose proof (FsImg.sbo_size sb Hsb) as Hsz.
    pose proof (FsImg.sbo_ninodes sb Hsb) as Hni.
    pose proof (FsImg.sbo_nblocks sb Hsb) as Hnb.
    pose proof (FsImg.sbo_one_bitmap sb Hsb) as Hone.
    unfold FsImg.ROOTINO in Hni. unfold FsImg.BSIZE_z in Hone.
    assert (Hdiv : 0 <= FsImg.sb_ninodes sb / 16) by (apply Z.div_pos; lia).
    (* the block layout, all in one arithmetic fact *)
    assert (Hds : FsImg.fs_data_start sb = FsImg.sb_bmapstart sb + 1)
      by reflexivity.
    assert (Hbm : FsImg.sb_bmapstart sb = 33 + Z.of_nat nib) by lia.
    (* the metadata window in ARITHMETIC form, so every use below is [lia] *)
    rewrite Hds Hbm in Hcovmeta.
    (* the two constants the goals below mention as powers *)
    assert (H231 : (2 : Z) ^ 31 = 2147483648) by reflexivity.
    assert (H216 : (2 : Z) ^ 16 = 65536) by reflexivity.
    assert (HBPB : BPB = 8192).
    { rewrite /BPB. vm_compute. reflexivity. }
    (* ---- the three derived coverage facts ---- *)
    assert (Hbel : cov_below cov (FsImg.sb_size sb))
      by exact (cov_below_of_image cov ndisk _ Hcovin Hnd).
    assert (Hok : cov_ok cov).
    { intros z Hz. destruct (Hcovin z Hz) as [Hz0 _].
      pose proof (Hbel z Hz). lia. }
    assert (Hlogsub : log_region_set (FsImg.sb_logstart sb) ⊆ cov).
    { apply elem_of_subseteq. intros b Hb.
      pose proof (log_region_bound (FsImg.sb_logstart sb) b Hb) as Hbb.
      unfold LOGBLOCKS in Hbb. apply Hcovmeta. lia. }
    assert (Hlogout : forall b : Z, FsImg.sb_inodestart sb <= b ->
              ~ (b ∈ log_region_set (FsImg.sb_logstart sb))).
    { intros b Hb Hc.
      pose proof (log_region_bound (FsImg.sb_logstart sb) b Hc) as Hbb.
      unfold LOGBLOCKS in Hbb. lia. }
    constructor.
    - exact Hdevq.
    - rewrite Hnibq. exact Hnib0.
    - rewrite Hcovq Hlogq. split; [exact Hok | exact Hlogsub].
    - rewrite Histq. lia.
    - rewrite Hcovq Hszq. exact Hbel.
    - rewrite Hcovq Hlogq Hbmq Hszq.
      split; [lia |]. split; [lia |].
      split; [apply Hcovmeta; lia | apply Hlogout; lia].
    - rewrite Histq Hnibq Hcovq Hlogq.
      intros w Hw.
      pose proof (IBLOCK_in_range w (FsImg.sb_inodestart sb) (Z.of_nat nib)
                    ltac:(lia) Hw) as Hbnd.
      split; [apply Hcovmeta; lia | apply Hlogout; lia].
    - rewrite Hninq. lia.
    - rewrite Hninq Hnibq. exact Hnin.
    - rewrite Hninq. lia.
    - rewrite Hnibq. exact Hush.
  Qed.

  (* [SpecFsinit]'s (a)/(b)/(g) and its two block-1 corners.  The ONE fact
     no sweep in the tree provides is (a): [FsImg.fsimg_wf] is arithmetic on
     the RECORD, and nothing in it says block 1's bytes ARE that record.
     [FsImg.fs_parse_sb] is exactly that reading, and
     [FsImgCheck.fsimg_parse_sb] already proves it at the literal image --
     so this premise costs the adequacy cone no new computation. *)
  Lemma first_fsinit_pures_of_image (dk : Z -> bv 8) (sb : FsImg.fs_sb)
      (cov : gset Z) :
    FsImg.fsimg_wf (FsCrash.fs_blocks dk) sb = true ->
    FsImg.fs_parse_sb (FsCrash.fs_blocks dk) = Some sb ->
    (forall b : Z, 1 <= b < FsImg.fs_data_start sb -> b ∈ cov) ->
    icfg_ist = FsImg.sb_inodestart sb ->
    fsc_cov = cov -> fsc_logst = FsImg.sb_logstart sb ->
    fsc_bmapstart = FsImg.sb_bmapstart sb ->
    fsc_size = FsImg.sb_size sb -> fsc_ninodes = FsImg.sb_ninodes sb ->
    first_fsinit_pures dk sb.
  Proof.
    intros Hwf Hparse Hcovmeta Histq Hcovq Hlogq Hbmq Hszq Hninq.
    pose proof (FsImg.fsimg_wf_sb _ _ Hwf) as Hsb.
    pose proof (FsImg.sbo_magic sb Hsb) as Hmag.
    pose proof (FsImg.sbo_logstart sb Hsb) as Hls.
    pose proof (FsImg.sbo_nlog sb Hsb) as Hnl.
    pose proof (FsImg.sbo_inodestart sb Hsb) as Hist.
    pose proof (FsImg.sbo_bmapstart sb Hsb) as Hbms.
    pose proof (FsImg.sbo_ninodes sb Hsb) as Hni.
    unfold FsImg.ROOTINO in Hni.
    assert (Hdiv : 0 <= FsImg.sb_ninodes sb / 16) by (apply Z.div_pos; lia).
    assert (Hds : FsImg.fs_data_start sb = FsImg.sb_bmapstart sb + 1)
      by reflexivity.
    assert (Hlen : length (FsCrash.fs_blocks dk FsImg.SB_BNO) = BSIZE)
      by apply fs_blocks_length.
    (* THE EIGHT FIELDS ARE THE EIGHT WORDS, which is all [fs_parse_sb]
       answering [Some sb] says -- and it is exactly premise (a). *)
    rewrite /FsImg.fs_parse_sb in Hparse.
    destruct ((32 <=? length (FsCrash.fs_blocks dk FsImg.SB_BNO))%nat) eqn:Hb;
      [| discriminate].
    injection Hparse as Hsbeq.
    rewrite /first_fsinit_pures. split; [| split; [| split]].
    - exists (Z_to_bv 32 (FsImg.fs_le_at (FsCrash.fs_blocks dk FsImg.SB_BNO) 0 4)),
             (Z_to_bv 32 (FsImg.fs_le_at (FsCrash.fs_blocks dk FsImg.SB_BNO) 8 4)),
             (Z_to_bv 32 (FsImg.fs_le_at (FsCrash.fs_blocks dk FsImg.SB_BNO) 16 4)).
      split.
      + rewrite Hszq Hninq Hlogq Hbmq Histq -Hsbeq.
        exact (first_sb_image_of_le (FsCrash.fs_blocks dk FsImg.SB_BNO)
                 ltac:(rewrite Hlen; unfold BSIZE; lia)).
      + rewrite -Hsbeq in Hmag. cbn [FsImg.sb_magic] in Hmag.
        rewrite Z_to_bv_unsigned Hmag. reflexivity.
    - rewrite Hlogq /log_hdr_bno /hdr_n.
      exact (FsImg.fsimg_wf_log _ _ Hwf).
    - rewrite Hcovq. apply Hcovmeta. lia.
    - rewrite Hlogq. intro Hc.
      pose proof (log_region_bound _ _ Hc) as Hbb. lia.
  Qed.

End FirstTok.

(* ...AND THE SAME SEAL AT TOP LEVEL, for [FsReady.v]'s reason: a
   [Typeclasses Opaque] inside a Section does not survive it.

   [first_tok] IS SEALED TOO, AND IT IS NOT A PERFORMANCE MEASURE -- IT IS
   CORRECTNESS.  The token is a conjunct of [ProcInv.proc_priv], so a broad
   [iFrame] at a process-layer goal meets it; [Frame]'s [∨]/[∗] instances
   will happily descend into the boot arm and CONSUME a [kernel_text] or a
   [kernel_data] the caller meant for somewhere else, silently forcing the
   disjunction's left arm and leaving an unprovable residue several lines
   later (observed at [ForkretParkClose.forkret_park_pkg_intro], where
   [iFrame "Htext …"] ate the first row of [first_boot_persist]).  Sealed,
   the framing stops at the head symbol and the token travels by name. *)
Typeclasses Opaque first_boot_persist.
Typeclasses Opaque first_tok.
