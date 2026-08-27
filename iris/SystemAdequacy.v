(* ====================================================================== *)
(* SystemAdequacy.v -- THE SYSTEM THEOREM.                                 *)
(*                                                                        *)
(* [xv6_power_adequacy]: a machine that starts POWERED OFF at generation 0  *)
(* and is then power-cycled forever never gets stuck.  Every configuration  *)
(* reachable from the one-thread pool [[PowerLoopE]] by ANY interleaving of *)
(* power cycles, hart steps and device steps is reducible -- and there is    *)
(* no Iris judgment, no ghost state and no hypothesis about the software    *)
(* anywhere in the statement.                                              *)
(*                                                                        *)
(* It is exactly three things composed:                                    *)
(*                                                                        *)
(*   [RiscvAdequacy.riscv_power_adequacy]  -- the power thread + Iris        *)
(*                                            adequacy, over an arbitrary   *)
(*                                            per-era boot entailment;      *)
(*   [BootShared.boot_shared_alloc]        -- that entailment's allocation,  *)
(*                                            ONCE per era;                 *)
(*   [BootChain.boot_hart_primary] /       -- one hart's whole life, the arm *)
(*   [BootChain.boot_hart_secondary]          chosen by its index;           *)
(*                                                                        *)
(* plus the three device-loop WPs, exactly as [riscv_device_adequacy] does. *)
(*                                                                        *)
(* THE DISPATCH LIVES HERE, deliberately (BootChain §5's note): a           *)
(* [boot_hart] that selected the arm itself would have to take the boot     *)
(* supply for EVERY hart, or take it under an [if decide ... then ... else  *)
(* True].  This file holds the supply for hart 0 only, peels [enum CPU] at  *)
(* its head, and applies §5 there and §4 to the tail -- where every element *)
(* is an [FS], hence provably nonzero.                                     *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap finite list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
From iris.program_logic Require Import language lifting adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto.
(* durable-disk 2b-A / B3: the era's two file-system-state capacity classes.
   Required EARLY so the later imports shadow [FsState]'s four colliding
   exports again ([fs_view], [link_auth], [byte_range], [blk_owned]); the
   IMPORT is what makes [fsLinkG]/[fsTopG]'s instance fields active, which a
   bare [Require] does not. *)
Require Import FsState.
Require Import ProcGeom.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import WpUart.
Require Import BootConfig.
Require Import BootChain BootShared.
Require Import FsCfgBoot.   (* [fs_boot_image_wf], moved down at stage (f) *)
Require Import RiscvAdequacy.
Require Import FsCrash.
Require Import FsDurSnap.   (* [snap_ok] -- the theorem's durability claim *)
Require Import FsDurAlloc.  (* era 0's value-first carve, through FsDurImg *)
Require Import FsDurImg.    (* [img_snap_ok] / [img_P_dur_alloc]: era 0's own
                               epoch, the ONE value-first allocation left *)
Require Import FirstTok.    (* [fs_extent_of_image] *)
(* THE LITERAL mkfs IMAGE.  Both halves, since the corollary at the bottom
   of this file discharges every image hypothesis: [FsImgDisk] is the
   machine-facing half ([fsimg_dk], its block view, one recovery fact) and
   [FsImgCheck] is what the image MEANS as a file system.  [FsImgCheck] is
   ~120 s of [vm_compute] and used to be kept off this file's cone for that
   reason ([FsAdequacyImg.v], retired); it costs nothing on the critical
   path, because it is already required by [NameiInitPinned] /
   [ProofKexecPinnedA] / [SpecKexecPinned] and so is built long before this
   file's own dependencies are ready. *)
Require Import FsImgDisk.
Require Import FsImgCheck.
Require Import VirtioModel.  (* [v_disk] *)
Require Import IrefSlots.
Require Import LogDefs.   (* [log_mirror_born] -- row (B) of the fsinit bundle *)
Require Import Xv6Cameras.  (* its record constructors *)
Require Import FsImg.  (* [fs_sb]: the era-wide image hypothesis's shape.  No
   computation and no literal image comes with it -- [FsImgCheck.v] is what
   instantiates the sweeps, and it is NOT on this file's cone. *)
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ---------------------------------------------------------------------- *)
(* 1. Peeling the hart enumeration at its head.                            *)
(*                                                                        *)
(* [enum CPU] IS [0%fin :: FS <$> enum (fin 7)] by conversion (stdpp's      *)
(* [fin_enum]), so the boot hart and the seven secondaries separate with no *)
(* case analysis on a hart variable anywhere -- and every element of the    *)
(* tail is syntactically an [FS], which is what discharges the secondary    *)
(* arm's [fin_to_nat c <> 0] premise.                                      *)
(* ---------------------------------------------------------------------- *)

Lemma cpu_enum_cons : (enum CPU : list CPU) = 0%fin :: (FS <$> enum (fin 7)).
Proof. reflexivity. Qed.

Lemma big_sepL_cpu_split {PROP : bi} (Φ : CPU -> PROP) :
  ([∗ list] c ∈ enum CPU, Φ c)
  ⊣⊢ Φ 0%fin ∗ ([∗ list] c ∈ enum (fin 7), Φ (FS c)).
Proof.
  rewrite {1}cpu_enum_cons big_sepL_cons big_sepL_fmap. done.
Qed.

(* the two DIRECTIONS, spelled separately.  [iApply]/[iDestruct] on a [⊣⊢]
   picks a direction of its own accord and the resulting list is not the one
   either side of the goal has, so the failure reads as an unapplicable
   [big_sepL_impl] several lines later. *)
Lemma big_sepL_cpu_peel {PROP : bi} (Φ : CPU -> PROP) :
  ([∗ list] c ∈ enum CPU, Φ c)
  ⊢ Φ 0%fin ∗ ([∗ list] c ∈ enum (fin 7), Φ (FS c)).
Proof. apply bi.equiv_entails_1_1, big_sepL_cpu_split. Qed.

Lemma big_sepL_cpu_glue {PROP : bi} (Φ : CPU -> PROP) :
  Φ 0%fin ∗ ([∗ list] c ∈ enum (fin 7), Φ (FS c))
  ⊢ [∗ list] c ∈ enum CPU, Φ c.
Proof. apply bi.equiv_entails_1_2, big_sepL_cpu_split. Qed.

Lemma fin_FS_nz (c : fin 7) : (fin_to_nat (FS c) <> 0)%nat.
Proof. cbn. lia. Qed.

Lemma fin_0_z : (fin_to_nat (0%fin : CPU) = 0)%nat.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ONE ERA'S BOOT: the entailment [riscv_power_adequacy] asks for.       *)
(* ---------------------------------------------------------------------- *)

(* THE BOOT MINT's RANGE: the whole xv6 file system image, FSSIZE = 2000
   blocks of BSIZE = 1024 bytes (kernel/param.h, kernel/fs.h, mkfs/mkfs.c).
   Every boot is handed exclusive byte fragments of the era's disk image over
   [[0, XV6_DISK_BYTES)] ([RiscvAdequacy.power_boot_res]); the FS layer's
   block views are carved out of them (claude-notes/design/fs-log.md).  The
   base layer takes this as a PARAMETER -- no FS constant appears below this
   file. *)
Definition XV6_DISK_BYTES : nat := (2000 * 1024)%nat.

(* THE PURE PROJECTION OF THE CRASH PREDICATE: what [FsCrash.P_fs_named]
   says about the PHYSICAL disk it is stated over -- the durable extent's
   geometry, the map the machine would recover to, that map's log header,
   and that the recovered view IS a file system.

   IT IS WHAT EVERY BOOT AFTER THE FIRST KNOWS ABOUT ITS DISK, and there is
   nothing else: it is EXTRACTED from the crash predicate by
   [FsCrash.P_fs_project], which [RiscvAdequacy.riscv_power_adequacy] runs
   against its own [state_interp] at each PowerOn.  An assumed "the disk is
   still mkfs's image at every era" is refutable -- nothing proves that
   xv6's own writes leave the disk mkfs-shaped -- and there is none: the
   image hypothesis below is one equation about the INITIAL machine. *)
Definition fs_boot_pure (cov : gset Z) (ls : Z) (dk : Z -> bv 8) : Prop :=
  fs_extent cov ls XV6_DISK_BYTES /\
  exists D : gmap Z (list (bv 8)),
    fs_recovery (fs_blocks dk) D cov ls /\
    hdr_wf (fs_blocks dk) cov ls /\
    (* ...AND THE COMMITTED VIEW IS A FILE SYSTEM (lane CE).  This is the
       durability claim: the map the machine would recover to right now is
       the encoding of an abstract file-system state -- every inode's record
       parses and is locally well formed, no two inodes share a block, and
       the bitmap's bits are the used set ([FsDurSnap.snap_ok]).  It comes
       off [FsCrash.P_fs]'s durable snapshot, which the commit re-establishes
       at every group commit and nothing else ever moves. *)
    exists S : fs_state_rec, snap_ok S D.

(* THE THREE ERA-INDEPENDENT FACTS a boot needs about the COVERED RANGE
   (durable-disk lane E-himg), read off the initial machine's image.

   [cov] and the crash predicate's [logstart] are parameters of the whole
   execution -- one invariant, allocated once into the fixed layer -- so
   they are the same at every era, and a PER-ERA snapshot is a fact about
   [S] and [D] alone and therefore cannot mention either.  Everything else a
   later boot needs about its disk comes off [fs_boot_pure]; these three are
   what remains, and they cost nothing because they are already conjuncts
   (or immediate readings) of the image hypothesis at [g].

   [logstart = 2] is what identifies the crash predicate's log start with
   the era's own ([FsImg.sbo_logstart] pins the snapshot's superblock at the
   same 2), and the log region's coverage is [1 <= b < data_start -> b ∈ cov]
   read at the log's own blocks. *)
Lemma cov_facts_of_image (dk : Z -> bv 8) (ndisk : nat)
    (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z) :
  fs_boot_image_wf dk ndisk sb nib cov ->
  FsBoot.fs_cov_in cov ndisk
  /\ log_region_set (FsImg.sb_logstart sb) ⊆ cov
  /\ FsImg.sb_logstart sb = 2.
Proof.
  intros (Hwf & _ & _ & _ & _ & _ & Hcovin & Hcovmeta & _).
  pose proof (FsImg.fsimg_wf_sb _ _ Hwf) as Hsb.
  pose proof (FsImg.sbo_logstart _ Hsb) as Hls.
  pose proof (FsImg.sbo_nlog _ Hsb) as Hnl.
  pose proof (FsImg.sbo_inodestart _ Hsb) as Hist.
  pose proof (FsImg.sbo_bmapstart _ Hsb) as Hbms.
  pose proof (FsImg.sbo_ninodes _ Hsb) as Hni. unfold FsImg.ROOTINO in Hni.
  assert (Hdv : 0 <= FsImg.sb_ninodes sb / 16) by (apply Z.div_pos; lia).
  split; [exact Hcovin |].
  split; [| exact Hls].
  apply elem_of_subseteq. intros b Hb.
  pose proof (log_region_range _ _ Hb) as Hbb.
  unfold LOGBLOCKS in Hbb. apply Hcovmeta.
  unfold FsImg.fs_data_start. lia.
Qed.

(* ...AND THE SAME FACT AS A TRACE HOOK.  [fs_boot_pure] above is delivered
   INTO each boot, by [riscv_power_adequacy]'s [Hproj] channel.  This is the
   shape that exports it OUT of the whole execution: the trace obligation
   [Hphi], at the crash predicate this file always uses.

   IT IS THE SAME LEMMA.  [FsCrash.P_fs_project] is what discharges [Hproj];
   [RiscvAdequacy.disk_proj_trace] is the adapter that promotes a
   [Hproj]-shaped projection to a [Hphi]-shaped one, by pulling the durable
   disk's auth out of [state_interp] ([RiscvAdequacy.power_interp_disk_auth]
   -- a FIXED conjunct, so it is there at every state of the trace, powered
   on or off).  Nothing new is proved and nothing new is assumed. *)
Lemma fs_trace_hook (Σ : gFunctors) `{!xv6G Σ, !riscvGpreS Σ}
    (cov : gset Z) (ls : Z)
    (Hinv : invGS Σ) (γgen γstart γreg γd γdv γsw : gname)
    (Γd : fs_dur_names) (g' : gstate) :
  ⊢ @power_interp Σ
       (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γdv Γd γsw
          (P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv Γd cov ls)) g' -∗
    ▷ P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv Γd cov ls -∗
    ◇ ⌜fs_boot_pure cov ls (v_disk (g'.(gdev).(dvirtio)))⌝.
Proof.
  exact (disk_proj_trace XV6_DISK_BYTES
           (fun a b c d e Gd => P_fs_named a XV6_DISK_BYTES b c d e Gd cov ls)
           (fs_boot_pure cov ls)
           (fun a b c d e Gd dk =>
              P_fs_project a XV6_DISK_BYTES b c d e Gd cov ls dk)
           Hinv γgen γstart γreg γd γdv γsw Γd g').
Qed.

(* ...AND A [phi] THAT IS NOT ABOUT THE DISK AT ALL, beside it.

   [fs_boot_pure] is read off the crash INVARIANT (through the durable
   disk's auth); [resv_ok] is read straight off [state_interp]'s ERA
   conjunct, with no invariant involved.  They are put in ONE [phi] here on
   purpose: [phi] is a single [Prop], so a client that wants several facts
   conjoins them, and the two conjuncts below travel through two entirely
   different conjuncts of [state_interp].  That is the demonstration that
   [riscv_power_adequacy]'s trace channel is not a disk channel.

   The [gpow] guard on the second is forced and is not a weakness: between a
   PowerOff and the next PowerOn there IS no era, so registers, memory and
   the device fabric are described by no ghost state at all.  A UART or
   memory invariant would be stated the same way -- guarded by [gpow], via
   [RiscvAdequacy.power_interp_era] and the client's own era receipt. *)
Definition xv6_trace_pure (cov : gset Z) (ls : Z) (g : gstate) : Prop :=
  (* THE DISK, from the crash invariant *)
  fs_boot_pure cov ls (v_disk (g.(gdev).(dvirtio))) /\
  (* NOT THE DISK: the reservation invariant, from the era conjunct *)
  (g.(gpow) = true -> resv_ok g).

Lemma xv6_trace_hook (Σ : gFunctors) `{!xv6G Σ, !riscvGpreS Σ}
    (cov : gset Z) (ls : Z)
    (Hinv : invGS Σ) (γgen γstart γreg γd γdv γsw : gname)
    (Γd : fs_dur_names) (g' : gstate) :
  ⊢ @power_interp Σ
       (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γdv Γd γsw
          (P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv Γd cov ls)) g' -∗
    ▷ P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv Γd cov ls -∗
    ◇ ⌜xv6_trace_pure cov ls g'⌝.
Proof.
  iIntros "Hsi HP".
  (* the era-side fact first: its conclusion is PURE, so [state_interp] is
     not spent and the disk projection still has it *)
  iDestruct (power_interp_resv_ok with "Hsi") as %Hresv.
  iDestruct (fs_trace_hook Σ cov ls Hinv γgen γstart γreg γd γdv γsw Γd g'
               with "Hsi HP") as ">%Hdisk".
  iModIntro. iPureIntro. split; [exact Hdisk | exact Hresv].
Qed.

Section SystemBoot.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{!fileGpreS Σ, !fdslotGpreS Σ, !irefslotGpreS Σ, !pavGpreS Σ, !bioslotGpreS Σ}.
  (* B3's two classes are [xv6G] MEMBERS now (2b-inode-3 / 2b-inode-4), so
     nothing extra is bound here -- see [FsCfgBoot]'s era section. *)
  Context `{GEN : GenId}.

  (* NO [fileG] AND NO [icacheG] BINDER ANY MORE (fs-cfg-boot.md stage
     (d2b)).  [fileG] carries [IcacheRef.icfg] and [FsCfg.fscfg] as
     superclass fields, and nothing in the tree ever produced either: the
     two records used to be the hardcoded [adequacy_icfg]/[adequacy_fscfg]
     of this file, at [icfg_nib = 0], where an [IcacheRef.inode_held] cannot
     exist -- so the boot cone's one assumed contract was VACUOUS at the
     instance the corollaries below are taken at.  [boot_shared_alloc] now
     MINTS both inside the era fupd, off the era's own disk, and hands the
     class back existentially; only the camera ([fileGpreS]) is a functor
     constraint. *)
  Lemma xv6_boot_era (g : gstate) (sb : fs_sb) (nib : nat) (cov : gset Z) :
    boot_facts g ->
    (* THE PROJECTION THE POWER THEOREM PROVES AT THIS ERA, AND IT IS THE
       WHOLE OF WHAT THIS BOOT KNOWS ABOUT ITS DISK (durable-disk lane
       E-himg).  The crash predicate's own reading of the disk this boot
       runs on -- the durable extent, the recovery record, the header
       invariant and the DURABLE SNAPSHOT -- extracted from [P_fs] by
       [FsCrash.P_fs_project] rather than assumed.  There is no image
       hypothesis at this era and there cannot be one: what a later era
       boots on is whatever the previous era committed. *)
    fs_boot_pure cov (FsImg.sb_logstart sb)
      (v_disk (g.(gdev).(dvirtio))) ->
    (* ...AND THE THREE FACTS ABOUT THE COVERED RANGE, which the snapshot
       cannot carry: [cov] and the crash predicate's [logstart] are FIXED
       across power cycles while the era's superblock is not, so these are
       read once off the initial machine and threaded. *)
    FsBoot.fs_cov_in cov XV6_DISK_BYTES ->
    log_region_set (FsImg.sb_logstart sb) ⊆ cov ->
    FsImg.sb_logstart sb = 2 ->
    (* THE CRASH SLOT'S VALUE, as a PURE equation (fs-cfg-boot.md stage
       (f), row 7 of [FirstTok.first_boot_persist]).  The boot cone needs
       [FsCrash.fs_crash_seam], and no fupd inside an era can mint it:
       the seam relates the FIXED ghost layer's [riscv_crash_pred] FIELD to
       the FS's own [P_fs], and the per-era obligation
       [RiscvAdequacy.riscv_power_adequacy] asks for is quantified over an
       ARBITRARY [riscvFixedGS], so an era learns nothing about that field.
       Adequacy is where the record is built, so adequacy is where the fact
       has to come from -- that is [riscv_power_adequacy]'s [Hcp], and this
       premise is [Hcp] read at the FS's own [Pc].  The seam is assembled
       from it below and rides [first_tok] to forkret's first arm. *)
    riscv_crash_pred = P_fs_any cov (FsImg.sb_logstart sb) ->
    power_boot_res riscv_eraGS gen_id boot_D NPROC XV6_DISK_BYTES
      (fun dk => mirror_of (fs_blocks dk)) g
    ={⊤}=∗
      ([∗ list] c ∈ enum CPU,
         WP (LoopE gen_id c : expr riscv_lang) @ ⊤) ∗
      WP (UartLoopE gen_id : expr riscv_lang) @ ⊤ ∗
      WP (DiskLoopE gen_id : expr riscv_lang) @ ⊤ ∗
      WP (PlicLoopE gen_id : expr riscv_lang) @ ⊤.
  Proof.
    intros Hbf Hpure Hcovin Hlogsub Hls2 Hcp. iIntros "Hres".
    (* ================================================================ *)
    (* THE ERA'S OWN CONFIGURATION, OFF THE SNAPSHOT (durable-disk lane  *)
    (* E-himg).  [fs_boot_pure] names the committed map [D] and an        *)
    (* abstract state [S] it encodes; the boot mint takes a total block   *)
    (* view, which is [FsCrash.fs_rec_view] of that map, and the era's    *)
    (* superblock and region width are [S]'s own.  The one thing that     *)
    (* has to be reconciled is the LOG START: the crash predicate's is a  *)
    (* parameter and [S]'s comes out of its own superblock, and           *)
    (* [FsImg.sbo_logstart] pins both at 2.                               *)
    (* ================================================================ *)
    destruct Hpure as (Hext & D & Hrec & Hhwf & S & Hsnok).
    pose proof (sk_bytes Hsnok) as Hsnb.
    pose proof (sk_sbok Hsnb) as Hsbok.
    pose proof (FsImg.sbo_logstart _ Hsbok) as Hls'.
    pose proof (FsImg.sbo_ninodes _ Hsbok) as Hni.
    unfold FsImg.ROOTINO in Hni.
    assert (Hdv : 0 <= FsImg.sb_ninodes (fss_sb S) / 16)
      by (apply Z.div_pos; lia).
    assert (Hlseq : FsImg.sb_logstart (fss_sb S) = FsImg.sb_logstart sb)
      by (rewrite Hls' Hls2; reflexivity).
    pose (Pb := fs_rec_view
                  (fs_blocks (v_disk (g.(gdev).(dvirtio)))) D).
    assert (Hbundle : fs_boot_snap_wf (v_disk (g.(gdev).(dvirtio)))
                        XV6_DISK_BYTES S Pb (fss_sb S) (snap_nib S) cov).
    { split; [reflexivity |].
      split; [rewrite /snap_nib Z2Nat.id; [reflexivity | lia] |].
      split.
      { rewrite Hlseq (fs_recovery_restrict _ D cov _ Hrec Hhwf).
        exact Hsnok. }
      split.
      { intros b. apply fs_rec_view_len;
          [intros b'; apply fs_blocks_length
          | intros b' bs Hbs; exact (sk_bsz Hsnb b' bs Hbs)]. }
      split; [rewrite Hlseq; exact Hhwf |].
      split.
      { rewrite Hlseq. intros b Hh Hout.
        exact (fs_rec_view_raw _ D cov _ b Hrec Hhwf Hh Hout). }
      split.
      { rewrite Hlseq. intros i b Hi.
        exact (fs_rec_view_slot _ D cov _ i b Hrec Hhwf Hi). }
      split; [exact Hcovin | rewrite Hlseq; exact Hlogsub]. }
    (* THE SEAM, ASSEMBLED FROM THE SLOT EQUATION and put in the
       intuitionistic context: it rides [FirstTok.first_boot_persist] from
       here to forkret's first arm.  Both directions are the identity once
       [Hcp] has rewritten the field away, which is exactly what "the FS's
       predicate IS the crash predicate" means.  It is spelled at the ERA's
       superblock, which is where the boot chain wants it; [Hlseq] is the
       one step. *)
    iAssert (fs_crash_seam cov (FsImg.sb_logstart (fss_sb S))) as "#Hseam".
    { rewrite Hlseq /fs_crash_seam. iModIntro.
      rewrite Hcp. iSplitL; iIntros "H"; iExact "H". }
    iMod (boot_shared_alloc g XV6_DISK_BYTES (fss_sb S) (snap_nib S) cov
            S Pb Hbf Hbundle with "Hres")
      as (Hfd Hir Hpav Hbs HF γd γv Rspent)
      "(%Hdimg & #Htext & #Hdata & #Hstarted & #Hdev & #Hwinv &
        #Hcinv & #Hcert & Hharts & Hlk & Hgl & Hmdata & Hpark & Hpst & Hpavail & Huart &
        Hdlab & Hcfg & Hclaim & Hcmauth & #Hdone & Hkpt & Hkmap & Hmir & Hpages & Hirauth &
        Hirslot & Hfs)".
    (* THE FILE SYSTEM'S BOOT KITS ARE NO LONGER DROPPED (stage (e)).
       [Hfs] is the ten configuration ties plus [fs_kit_icache] plus
       [fs_kit_fsinit_ghost], and [Hirauth] is the iref-slot authority
       [icache_boot_at] takes.  Both now ride [boot_hart_primary] into
       [SpecMain]'s boot arm, where [ProofMain.mn_grp_fs] runs
       [icache_boot_at] on them and hands the four inode-cache rows to
       [userinit] -- which is what discharged [LinkNameiRootBoot]'s Axiom. *)
    (* the harts' reservation mirrors (design §3a) are gone from this
       interface: [boot_shared_alloc] threads each into its hart's [pc_is]. *)
    (* [Hmdata] IS [BootShared.main_data_raw] -- the image's writable
       initialized globals (`first`, `nextpid`), which [kernel_data] stopped
       claiming when it was narrowed to [rodata_end].  It is threaded to main
       now: [ProofMain.mn_grp_kvm] spends `nextpid` on the [newlock] that
       builds [SpecAllocpid]'s lock, which is allocproc's premise and hence
       userinit's.  `first` rides along and is dropped there -- its consumer
       is forkret's [if (first)] arm. *)
    iDestruct "Huart" as (l0) "(Htx & #Hsent & #Hlb)".
    iDestruct "Hdlab" as (b0) "Hdlab".
    iDestruct "Hcfg" as (c0) "[%Hlive Hcfg]".
    iDestruct "Hpages" as (ps) "(%Hprun & %Hplen & Hpages)".
    (* one row out of [boot_shared_alloc], two premises at [BootChain] -- the
       halves are what main spends and drops separately *)
    iDestruct "Hmdata" as "[Hmfirst Hmnext]".
    (* THE ERA'S MIRROR IS ROW (B) of [FirstTok.first_fsinit], and main
       parks it there for initlog.  Since durable-disk 1a it arrives
       VALUE-BEARING -- the era's half at the picture of its own disk plus
       the swap receipt -- so there is nothing to weaken here: what
       [boot_shared_alloc] hands over IS the shape [SpecInitlog] takes. *)
    iDestruct (big_sepL_cpu_peel with "Hharts") as "[Hh0 Hhrest]".
    (* the three device threads' invariants, off the one device fabric *)
    iDestruct (dev_inv_uart with "Hdev") as "#Huinv".
    iDestruct (dev_inv_plic with "Hdev") as "#Hpinv".
    iDestruct (dev_inv_disk with "Hdev") as "#Hvinv".
    iDestruct (dev_inv_perm with "Hdev") as "#Hqinv".
    iModIntro.
    iSplitL "Hh0 Hhrest Hlk Hgl Hmfirst Hmnext Hpark Hpst Hpavail Hfs Hmir Hirslot Hirauth Htx Hdlab Hcfg Hclaim Hcmauth Hkpt Hkmap
             Hpages".
    { iApply (big_sepL_cpu_glue
                (fun c => WP (LoopE gen_id c : expr riscv_lang) @ ⊤
)%I).
      iSplitL "Hh0 Hlk Hgl Hmfirst Hmnext Hpark Hpst Hpavail Hfs Hmir Hirslot Hirauth Htx Hdlab Hcfg Hclaim Hcmauth Hkpt Hkmap
               Hpages".
      { (* THE BOOT HART: the arm that consumes the whole supply. *)
        (* AT [HF] EXPLICITLY, not by resolution.  [SpecMain.MAIN]'s
           parameters are ∀-quantified over the classes, so handing the
           chain the instance the era fupd just built is an APPLICATION;
           asking resolution for a [fileG Σ] here would take the
           [subG_fileΣ -> fscfg -> file_fscfg -> fileG] cycle instead
           (FileInv.v's "two instance paths print identically and do not
           unify", and the 400 GB divergence the deleted [adequacy_fscfg]
           was written to block). *)
        iDestruct "Hh0" as (iv) "Hh0".
        iApply (boot_hart_primary (fileG0 := HF) (CID := 0%fin)
                  (g.(gregs) 0%fin) iv DfracDiscarded γd γv ps l0 b0 c0
                  (v_disk (g.(gdev).(dvirtio))) (fss_sb S) (snap_nib S) cov
                  XV6_DISK_BYTES S Pb Rspent
                  (boot_regs_of_facts g Hbf 0%fin) fin_0_z Hprun Hplen Hlive
                  Hbundle
                  with "Htext Hdata Hh0 Hstarted Hlk Hgl Hmfirst Hmnext Hpark Hpst Hpavail
                        Hfs Hmir Hirslot Hirauth Hcert Hseam
                        Hdev Hwinv Htx Hsent Hlb Hdlab Hcfg Hclaim Hcmauth Hdone Hkpt Hkmap
                        Hpages"). }
      (* THE SEVEN SECONDARIES: every element of the tail is an [FS]. *)
      iApply (big_sepL_impl with "Hhrest").
      iIntros "!>" (k c _) "Hh".
      iDestruct "Hh" as (iv) "Hh".
      iApply (boot_hart_secondary (fileG0 := HF) (CID := FS c)
                (g.(gregs) (FS c)) iv DfracDiscarded γd γv
                (boot_regs_of_facts g Hbf (FS c)) (fin_FS_nz c)
                with "Htext Hdata Hh Hstarted"). }
    iSplitR; [iApply (wp_uart_loop γd with "Hcert Huinv Hpinv") |].
    iSplitR;
      [iApply (wp_disk_loop γv Hdimg with "Hcert Hcinv Hqinv Hvinv Hpinv") |].
    iApply (wp_plic_loop with "Hcert Hpinv Hwinv").
  Qed.

End SystemBoot.

(* ---------------------------------------------------------------------- *)
(* 3. THE SYSTEM THEOREM.                                                  *)
(* ---------------------------------------------------------------------- *)

Theorem xv6_power_adequacy Σ
    `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ, !fdslotGpreS Σ,
      !irefslotGpreS Σ, !bioslotGpreS Σ}
    (g : gstate) (sb : fs_sb) (nib : nat) (cov : gset Z)
    (* THE TRACE INVARIANT, PASSED THROUGH TO
       [RiscvAdequacy.riscv_power_adequacy] (whose header is the full
       story).  [phi] is any pure statement about the OPERATIONAL state, and
       [Hphi] proves it from the two things adequacy holds at every point of
       the trace: [state_interp] -- the only bridge between the logic and
       [gstate] -- and the fixed-layer crash invariant, whose predicate here
       IS the file system's durability record [FsCrash.P_fs_named].  The
       conclusion then carries [phi] at EVERY reachable state, not just at
       the boot states [Ppure] is delivered to.

       Stated at the [boot_fixedGS] literal, exactly as the theorem below
       consumes it, so every field projection reduces by iota; the client
       never has to see a [riscvFixedGS] it did not build. *)
    (phi : gstate -> Prop)
    (Hphi : forall (Hinv : invGS Σ)
                   (γgen γstart γreg γd γdv γsw : gname) (Γd : fs_dur_names)
                   (g' : gstate),
       ⊢ @power_interp Σ
            (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γdv Γd γsw
               (P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv Γd cov
                  (FsImg.sb_logstart sb))) g' -∗
         ▷ P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv Γd cov (FsImg.sb_logstart sb) -∗
         ◇ ⌜phi g'⌝)
    (* the hypotheses about the machine: it is off, and nothing has ever
       run.  Everything else a boot needs -- RAM total and holding the loaded
       kernel image, the per-hart reset registers, the reset devices -- is
       supplied per ERA by [RiscvLang.boot_shape], which the power thread's
       PowerOn transition establishes itself. *)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (* ...AND ONE ABOUT THE DISK, AND IT IS ONE EQUATION ABOUT [g]
       (durable-disk lane E-himg): the machine the system is switched on
       with carries the file system's image.  NOTHING IS ASSUMED ABOUT ANY
       LATER ERA -- what a later boot finds is whatever the previous era
       committed, and that the committed view is still a file system is what
       [FsCrash.P_fs]'s durable snapshot says and what [fs_boot_pure]
       delivers into every boot.  The conclusion mentions none of it, so
       this is the price of a NON-VACUOUS boot cone, not a weaker theorem
       about reducibility.  the corollary at the bottom of this file discharges it at the literal
       mkfs image. *)
    (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
              sb nib cov) :
  forall t2 g2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ phi g2.
Proof.
  (* THE CRASH SLOT IS NO LONGER [True] HERE, AND THE STATEMENT IS UNCHANGED
     (fs-cfg-boot.md stage (f)).  This theorem used to instantiate
     [Pc := fun _ => True] -- "never stuck, nothing claimed about a power
     cycle".  It cannot any more: the boot cone now builds
     [FirstTok.first_boot_persist], whose seventh row is
     [FsCrash.fs_crash_seam], and at a constant-[True] slot that seam is
     FALSE (it would have to produce [P_fs] out of [True]).

     So the slot is filled with the FS record here too, and the recovery
     obligation that comes with it is DISCHARGED rather than assumed:
     [FsCrash.fs_recovery_total] says every disk image recovers to SOME
     committed state, which is all [P_fs_alloc] needs.  What this theorem
     says about a power cycle is still nothing, because [D0] is existential
     and never mentioned again -- [xv6_fs_adequacy_xv6Σ] at the bottom of
     this file is the one that makes a claim at every reachable state, by
     instantiating [phi] at the crash predicate's own pure content. *)
  destruct (fs_recovery_total (fs_blocks (v_disk (g.(gdev).(dvirtio))))
              cov (FsImg.sb_logstart sb)) as [D0 Hrec].
  (* the durable disk's extent, and the three ERA-INDEPENDENT facts about
     the covered range, all read off the initial machine's image *)
  pose proof (cov_facts_of_image _ _ sb nib cov Himg)
    as (Hcovin & Hlogsub & Hls2).
  assert (Hext : fs_extent cov (FsImg.sb_logstart sb) XV6_DISK_BYTES).
  { pose proof Himg as Hw.
    destruct Hw as (Hwf & _ & _ & _ & _ & Hnibeq & Hcin & Hcmeta & _).
    exact (FirstTok.fs_extent_of_image _ _ _ _ _ Hwf Hnibeq Hcin Hcmeta). }
  (* ...and the header invariant [P_fs_alloc] now carries (stage B's
     [hdr_wf]): the image's log is clean, so [hdr_wf_zero] closes it.  The
     boot state's disk IS [g]'s ([virtio_reset] keeps [v_disk]), so the
     image sweep applies by conversion. *)
  assert (Hhwf : hdr_wf (fs_blocks (v_disk (g.(gdev).(dvirtio)))) cov
                   (FsImg.sb_logstart sb)).
  { pose proof Himg as Hw.
    destruct Hw as (Hwf & _).
    apply hdr_wf_zero. rewrite /log_hdr_bno /hdr_n.
    exact (FsImg.fsimg_wf_log _ _ Hwf). }
  (* ...AND THE DURABLE SNAPSHOT ITSELF (lane CE, re-pointed by lane H5):
     [FsCrash.P_fs] carries one copy of the file-system predicate at the
     committed map, so the era-0 mint needs THE EPOCH, not a pure tie.  The
     image's log is clean, so [D0] is exactly its home blocks, and
     [FsDurImg.img_P_dur_alloc] -- the tree's ONE value-first allocation,
     over [FsDurAlloc]'s carve -- builds it.
     THIS IS THE ONLY PLACE THE IMAGE DECODER IS READ: every later era's boot
     re-founds the file system from the snapshot the previous era committed. *)
  assert (Hsnap0 : ⊢ |==> P_dur D0).
  { pose proof Himg as Hw.
    assert (Hclean : hdr_n (fs_blocks (v_disk (g.(gdev).(dvirtio)))
                              (log_hdr_bno (FsImg.sb_logstart sb))) = 0).
    { rewrite /hdr_n /log_hdr_bno.
      exact (FsImg.fsimg_wf_log _ _ (proj1 Hw)). }
    rewrite (proj1 (fs_recovery_clean _ D0 cov (FsImg.sb_logstart sb) Hclean)
               Hrec).
    exact (img_P_dur_alloc _ XV6_DISK_BYTES sb nib cov Hw). }
  (* THE CRASH PREDICATE AT ERA 0: the record from mkfs's recovery fact,
     and the DURABLE DISK's fragments -- the whole [0, XV6_DISK_BYTES) of the
     initial image, handed over once by the power theorem and owned by the
     predicate from here on (design/crash.md, "The durable disk").  This is
     the only place the initial image is ever named. *)
  apply (riscv_power_adequacy Σ boot_D NPROC XV6_DISK_BYTES g
           (fun (γd γsw γreg γst γdv : gname) (Γd : fs_dur_names) =>
              P_fs_named γd XV6_DISK_BYTES γsw γreg γst γdv Γd cov
                (FsImg.sb_logstart sb))
           ltac:(intros γd γsw γreg γst γdv; iIntros "(Hfr & Hsw & Hdv)";
                 iMod fs_boot_alloc_empty as (gl gt) "_";
                 iMod (P_fs_alloc γsw γreg γst γdv (MkFsDurNames gl gt (FsImg.sb_bmapstart sb) (FsImg.sb_inodestart sb) (16 * Z.of_nat nib))
                         _ D0 cov
                         (FsImg.sb_logstart sb) Hrec Hhwf Hsnap0
                         with "[$Hsw $Hdv]") as (γs) "(%Hseq & HP & _)";
                 iModIntro; iExists (MkFsDurNames gl gt (FsImg.sb_bmapstart sb) (FsImg.sb_inodestart sb) (16 * Z.of_nat nib));
                 rewrite /P_fs_named;
                 iExists (v_disk (g.(gdev).(dvirtio))); iFrame "Hfr";
                 iSplitR; [iPureIntro; exact Hext |];
                 rewrite /P_fs_rec_named; iExists γs;
                 iSplitR; [iPureIntro; exact Hseq | iExact "HP"])
           (* THE PURE PROJECTION (stage H0): the crash predicate's own
              reading of the physical disk, at every era.  [P_fs_project] IS
              the obligation -- the durable auth is lent for the one
              agreement that identifies [P_fs]'s image with the machine's,
              and nothing is spent. *)
           (fs_boot_pure cov (FsImg.sb_logstart sb))
           ltac:(intros γd γsw γreg γst γdv Gd dk;
                 exact (P_fs_project γd XV6_DISK_BYTES γsw γreg γst γdv Gd cov
                          (FsImg.sb_logstart sb) dk))
           (* CUSTODY AT BIRTH (durable-disk 1a): the era's mirror is the
              picture of the era's own disk, and [P_fs_swap] IS the hook's
              obligation -- it installs [P_fs]'s custody arm at that
              variable in the same fupd, so the era boots already holding a
              true picture and the swap receipt. *)
           (fun dk => mirror_of (fs_blocks dk))
           ltac:(intros γd γsw γreg γst γdv Gd Er gen dk;
                 exact (P_fs_swap γd XV6_DISK_BYTES γsw γreg γst γdv Gd cov
                          (FsImg.sb_logstart sb) dk Er gen))
           (* THE TRACE HOOK, threaded straight through: this layer fixes the
              crash predicate but says nothing about what the client reads off
              it, so [phi]/[Hphi] pass down unexamined. *)
           phi Hphi
           Hgen0 Hpow).
  (* the per-era boot entailment, at the era instance the power thread just
     minted.  [riscv_fixedGS (RiscvGS Σ F HE)] iota-reduces to [F] and
     [riscv_eraGS] to [HE], so §2's statement at the composed instance IS
     this obligation (crash.md's M0 gotcha, in the direction that works). *)
  intros F HE gen g' Hbf Hpure Hshape.
  (* THE RECORD'S SHAPE, destructed: every projection below reduces, which
     is what makes the crash slot's value -- and hence the seam -- visible
     to the boot cone at all.  [RiscvAdequacy.boot_fixedGS]'s header is the
     argument for why an equation about [riscv_crash_pred] alone would not
     do (the ghost CLASS instances have to agree too). *)
  destruct Hshape as (Hi & Gg & Gs & Gr & Gt & Gdv & Gsw & Gd & ->).
  (* one [_] fewer since durable-disk 2b-inode-3: [fsTopG] is an [xv6G]
     member now, so the section generalises one class less. *)
  refine (@xv6_boot_era Σ (RiscvGS Σ _ HE) _ _ _ _ _ _ gen g' sb nib cov Hbf
            Hpure Hcovin Hlogsub Hls2 _).
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. ...and at a CONCRETE functor list, so nothing at all is assumed.     *)
(* ---------------------------------------------------------------------- *)

(* [adequacy_icfg] AND [adequacy_fscfg] ARE GONE, and their deletion is the
   point of fs-cfg-boot.md stage (d2b).  They were two [Local Instance]s of
   all-[1%positive] records -- an [IcacheRef.icfg] with [icfg_nib = 0] and an
   [FsCfg.fscfg] nobody allocated -- and they existed only because [fileG]
   had to be RESOLVED here: nothing in the tree could produce either record,
   so the corollaries below could not be stated without inventing them.  At
   [icfg_nib = 0] an [IcacheRef.inode_held] cannot exist, so the boot cone's
   one assumed contract ([SpecNameiRootBoot.v]'s [namei("/")]) was VACUOUS at
   exactly the instance the corollaries were taken at.  That was a defect in
   the top-level statement, not a missing convenience.

   [BootShared.boot_shared_alloc] now MINTS both records inside the era fupd
   (off the era's own disk, at the parsed superblock's geometry) and returns
   the reassembled [fileG] existentially, so this file resolves [fileGpreS]
   -- whose only instance is [subG] on the functor list -- and never
   [fileG].  The 400 GB nontermination hazard documented at [adequacy_fscfg]
   goes with it: the cycle it blocked was
   [fileG -> subG_fileΣ -> fscfg -> file_fscfg -> fileG], and with no site
   resolving [fileG] there is nothing to enter it.  The compressed note now
   lives where [FileInvDefs.fileG_of] is APPLIED (BootShared.v §5) and at the
   chain application in §2 above. *)

Definition xv6Σ : gFunctors :=
  #[ riscvΣ; xv6GΣ; fileΣ; fdslotΣ; irefslotΣ; pavΣ ].

(* THE POWER THEOREM AT THE CONCRETE FUNCTOR LIST: every class is
   discharged, so "nothing about the ghost state is assumed" is checked
   rather than claimed.  [Himg] is still a premise -- this corollary does
   not name the literal image.

   IT IS NO LONGER THE ASSUMPTION AUDIT'S TARGET.  [SystemAssumptions.v]
   now audits [xv6_fs_adequacy_xv6Σ] at the bottom of this file, which is
   the theorem with NOTHING left as a premise and so the only one whose
   axiom list is the whole story.  The cost of that is real and expected:
   naming [FsImgDisk.fsimg_dk] pulls Rocq's [PrimString]/[PrimInt63]
   primitives in (MEASURED: ten extra entries, on any constant naming the
   image), so the baseline the audit diffs against is THIRTEEN, not three.
   Those ten are structural -- the same set appears on every literal-image
   theorem ([ElfKernel.v] / [ElfUser.v] / [FsImgCheck.v]) -- and
   durable-notes' "adequacy-print baseline" lists them by name so a reader
   can tell them from a regression. *)

(* ---------------------------------------------------------------------- *)
(* 1.  THE IMAGE'S COVERAGE SET (ruling R4).                               *)
(*                                                                        *)
(* [cov] is the set of block numbers the proof maintains logical content    *)
(* for -- the domain of [FsBoot.fs_C0], and exactly the set               *)
(* [bread] accepts.  The generic theorems keep it a PARAMETER, because      *)
(* nothing about the image constrains it and the conclusion never mentions  *)
(* it; here it is instantiated at the image's own range.  Block 0 is        *)
(* excluded (binit leaves all thirty buffers claiming blockno 0), and the   *)
(* top is the superblock's [size = 2000].                                  *)
(*                                                                        *)
(* Stocking the inode pool is what forces the choice: every block a live    *)
(* image inode names has to be in [cov], on top of the log region, the      *)
(* inode blocks and the bitmap block.  At [cov = ∅] the statement said      *)
(* nothing about a file system at all.                                      *)
(* ---------------------------------------------------------------------- *)
Definition fsimg_cov : gset Z := list_to_set (Z.of_nat <$> seq 1 1999).

Lemma fsimg_cov_elem_of (b : Z) : b ∈ fsimg_cov <-> 1 <= b < 2000.
Proof.
  rewrite /fsimg_cov elem_of_list_to_set elem_of_list_fmap. split.
  - intros (k & -> & Hk). apply elem_of_seq in Hk. lia.
  - intros Hb. exists (Z.to_nat b).
    split; [lia | apply elem_of_seq; lia].
Qed.

(* the image's inode-region size, in blocks: [ninodes/16 + 1 = 200/16 + 1],
   which is [bmapstart - inodestart = 46 - 33].  [FsImgCheck]'s own sweeps
   ([fsimg_region_wf], [fsimg_region_free]) are stated at this 13. *)
Definition fsimg_nib : nat := 13%nat.

(* ---------------------------------------------------------------------- *)
(* 2.  THE IMAGE HYPOTHESIS, DISCHARGED.                                   *)
(*                                                                        *)
(* [BootShared.fs_boot_image_wf]'s nine conjuncts at the literal image.     *)
(* Two are [FsImgCheck] citations; the other seven are arithmetic on the    *)
(* superblock's own eight numbers                                          *)
(* ([MkFsSb 0x10203040 2000 1953 200 31 2 33 46]) and on [fsimg_cov]'s      *)
(* membership law.  NO [vm_compute]: [fsimg_P] IS [fs_blocks fsimg_dk] by   *)
(* definition, so the two sweeps are cited, not re-run.                     *)
(* ---------------------------------------------------------------------- *)

(* [2 ^ 32], as a closed equation, so no goal below asks [lia] to evaluate a
   power.  (Conversion, not computation on the image.) *)
Local Lemma two_pow_32 : (2 : Z) ^ 32 = 4294967296.
Proof. reflexivity. Qed.

Local Lemma xv6_disk_bytes_z : Z.of_nat XV6_DISK_BYTES = 2048000.
Proof. unfold XV6_DISK_BYTES. rewrite Nat2Z.inj_mul. reflexivity. Qed.

Lemma fsimg_image_wf :
  fs_boot_image_wf FsImgDisk.fsimg_dk XV6_DISK_BYTES
    fsimg_sb fsimg_nib fsimg_cov.
Proof.
  rewrite /fs_boot_image_wf /fsimg_nib.
  (* (1) W1-W9, cited *)
  split; [exact fsimg_wf_ok |].
  (* (2) the whole [16*nib] region's L3/L4 and free tail, cited *)
  split; [exact fsimg_region_wf |].
  (* (3) the region covers every inum the superblock claims: 200 <= 208 *)
  split; [cbv [fsimg_sb sb_ninodes]; lia |].
  (* (4) and it fits in a 32-bit inum *)
  split; [rewrite two_pow_32; lia |].
  (* (5) it is not empty *)
  split; [lia |].
  (* (6) mkfs rounds [ninodes] up to a whole block: 13 = 200/16 + 1 *)
  split; [cbv [fsimg_sb sb_ninodes]; reflexivity |].
  (* (7) every covered block is a real client block inside the mint *)
  split.
  { intros b Hb. apply fsimg_cov_elem_of in Hb.
    rewrite xv6_disk_bytes_z. lia. }
  (* (8) every METADATA block is covered: block 1 up to the bitmap block *)
  split.
  { intros b Hb. apply fsimg_cov_elem_of.
    cbv [fs_data_start fsimg_sb sb_bmapstart] in Hb. lia. }
  (* (9) ...and every DATA block, up to the superblock's [size] *)
  split.
  { intros b Hb. apply fsimg_cov_elem_of.
    cbv [fs_data_start fsimg_sb sb_bmapstart sb_size] in Hb. lia. }
  (* (10) block 1's bytes ARE the record -- CITED, not recomputed: this is
     [FsImgCheck.fsimg_parse_sb], which the check file already proves.
     [fsimg_P] IS [fs_blocks fsimg_dk] by definition. *)
  split; [exact fsimg_parse_sb |].
  (* (11) the ushort bound: 16 * 13 = 208 <= 65536 *)
  split; [vm_compute; discriminate |].
  (* (12) the image is 2000 blocks: 2048000 = 1024 * 2000 *)
  split; [rewrite xv6_disk_bytes_z; cbv [fsimg_sb sb_size]; lia |].
  (* (13) the file-nlink EQUALITY sweep -- CITED, like (1)/(2)/(10):
     [FsImgCheck.fsimg_links_eq], and [fsimg_P] IS [fs_blocks fsimg_dk]. *)
  split; [exact fsimg_links_eq |].
  (* (14) every FREE record of the region is BARE -- CITED:
     [FsImgCheck.fsimg_region_bare], the same thirteen inode blocks the two
     region sweeps above read. *)
  split; [exact fsimg_region_bare |].
  (* (15) no live non-dot root record names the root -- CITED:
     [FsImgCheck.fsimg_root_no_self], one O(nrec) pass over the root. *)
  exact fsimg_root_no_self.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2b. THE NON-VACUITY WITNESS FOR THE DURABLE SNAPSHOT (plan section 7).  *)
(*                                                                        *)
(* [FsDurImg.img_snap_ok] is hedged behind [fs_boot_image_wf]'s fifteen     *)
(* conjuncts, so the plan's vacuity discipline owes a witness AT THE REAL   *)
(* INSTANCE -- xv6's own superblock layout, not a made-up one.  This is     *)
(* it, and it costs NO computation: it is [fsimg_image_wf] above, whose     *)
(* every image conjunct is a [FsImgCheck] citation.  What it says is that   *)
(* the mkfs image really does denote an abstract file-system state whose    *)
(* encoding is the image's own committed home blocks, with the used-set     *)
(* coupling and the per-inode local clauses -- i.e. that the durable        *)
(* snapshot the WAL carries is not empty at era 0.                          *)
(*                                                                        *)
(* IT MUST BE HERE AND NOT INSIDE A SECTION: a [vm_compute] on a goal       *)
(* containing a section variable hangs (durable-notes.md), and every        *)
(* literal-image fact this cites is already a closed lemma of              *)
(* [FsImgCheck].                                                           *)
(* ---------------------------------------------------------------------- *)
Theorem fsimg_snap_ok :
  snap_ok (img_state fsimg_P fsimg_sb fsimg_nib)
          (fs_restrict fsimg_P
             (fs_home_set fsimg_cov (FsImg.sb_logstart fsimg_sb))).
Proof.
  exact (img_snap_ok FsImgDisk.fsimg_dk XV6_DISK_BYTES fsimg_sb fsimg_nib
           fsimg_cov fsimg_image_wf).
Qed.

(* ---------------------------------------------------------------------- *)
(* 3.  THE TWO COROLLARIES, AT ONE EQUATION ABOUT [g].                     *)
(*                                                                        *)
(* [fsimg_at_every_era] IS GONE (durable-disk lane E-himg), and so is the  *)
(* [SystemAdequacy.fs_boot_image_eras] it was a bridge to.  Both said THE  *)
(* LITERAL IMAGE IS ON THE DISK AT EVERY ERA, which is refutable -- era N's *)
(* disk is whatever era N-1 wrote, so one [create] falsifies it.  The      *)
(* general theorem takes the image ONCE, at the machine the system is      *)
(* switched on with, and every later boot reads its file system off the    *)
(* crash predicate's durable snapshot instead.  So the corollary below     *)
(* assumes exactly what a reader would expect: the initial disk is mkfs's.  *)
(* ---------------------------------------------------------------------- *)

(* THE SYSTEM THEOREM AT THE LITERAL mkfs IMAGE -- the end of the line, and
   the [Print Assumptions] target ([SystemAssumptions.v]).

   NOTHING ABOUT THE FILE SYSTEM IS ASSUMED BEYOND THE INITIAL DISK: the
   one hypothesis is that the machine is switched on with the image mkfs
   built.  [FsImgDisk.fsimg_dk] is kernel-rocq/FsImgRaw.v's 2,048,000
   bytes, zero-padded beyond them (a virtio disk reads zeroes past the file
   backing it, and [XV6_DISK_BYTES] is larger than the image).

   THE PARAMETERS, and why each is what it is:
     [logstart] is pinned to [2], the IMAGE'S OWN [logstart]
       ([FsImgCheck.fsimg_sb_logstart] is what checks that the superblock
       says so);
     [cov] is [fsimg_cov] (section 1), NO LONGER PARAMETRIC: stocking the
       inode pool from the image forces every block a live inode names into
       it;
     [sb]/[nib] are the parsed superblock and its inode region's 13 blocks.

   THERE IS NO [Hrec] TO DISCHARGE.  There used to be: a second generic
   theorem [xv6_fs_adequacy] took mkfs's recovery obligation as a premise
   and this corollary supplied it from [FsImgDisk.fsimg_recovery].  That
   theorem was [xv6_power_adequacy] with two premises its conclusion never
   used -- provable from it by [intros; eapply xv6_power_adequacy;
   eassumption] -- so it is gone, and with it the obligation.  Do not
   reintroduce a "FS-flavoured" generic theorem: the FS content of this
   statement is entirely in [phi], and [phi] is [xv6_trace_pure].

   What the image MEANS as a file system -- [FsImg.fsimg_wf], and that
   /init /sh /echo /sync hold exactly the tracked ELF raws the U-mode proofs
   reason about -- is [iris/FsImgCheck.v], which this file Requires. *)

(* ---------------------------------------------------------------------- *)
(* 4. ...AT THE CONCRETE FUNCTOR LIST *AND* AT THE LITERAL mkfs IMAGE,      *)
(*    with [phi] STILL FREE.                                               *)
(*                                                                        *)
(* Two of the three things the general theorem leaves open are settled     *)
(* here -- the ghost state (every class discharged, so nothing about the   *)
(* ghost state is assumed is CHECKED rather than claimed) and the DISK.    *)
(* [phi] stays open, which is the point: a client with some other pure     *)
(* trace property -- a UART trace, a memory invariant -- instantiates THIS *)
(* and owes nothing about the image.                                      *)
(*                                                                        *)
(* WHY THE IMAGE IS DISCHARGED HERE AND NOT LOWER DOWN.  [Himg] cannot be  *)
(* discharged before the disk is named, and naming it in                   *)
(* [xv6_power_adequacy] would destroy that theorem's generality -- so this *)
(* is the earliest rung where it CAN go, and every statement below is      *)
(* image-free as a result.  The cost is that [sb]/[nib]/[cov] are no       *)
(* longer parameters here: pinning the disk pins them to [fsimg_sb] /      *)
(* [fsimg_nib] / [fsimg_cov].  A client wanting the concrete functor list  *)
(* at some OTHER image goes one rung up to [xv6_power_adequacy], which is  *)
(* still abstract in all three.                                           *)
(* ---------------------------------------------------------------------- *)
Corollary xv6_power_adequacy_xv6Σ (g : gstate)
    (phi : gstate -> Prop)
    (Hphi : forall (Hinv : invGS xv6Σ)
                   (γgen γstart γreg γd γdv γsw : gname) (Γd : fs_dur_names)
                   (g' : gstate),
       ⊢ @power_interp xv6Σ
            (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γdv Γd γsw
               (P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv Γd fsimg_cov
                  (FsImg.sb_logstart fsimg_sb))) g' -∗
         ▷ P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv Γd fsimg_cov
             (FsImg.sb_logstart fsimg_sb) -∗
         ◇ ⌜phi g'⌝)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (* THE ONE HYPOTHESIS LEFT, and it is about the HARDWARE SETUP, not the
       file system: the machine is switched on with the disk mkfs wrote. *)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall t2 g2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ phi g2.
Proof.
  apply (xv6_power_adequacy xv6Σ g fsimg_sb fsimg_nib fsimg_cov phi Hphi
           Hgen0 Hpow).
  (* THE IMAGE, DISCHARGED: [Hdisk] rewrites the machine's disk to the
     literal image, and [fsimg_image_wf] -- a CLOSED lemma, six [exact]s off
     [FsImgCheck]'s sweeps plus arithmetic -- closes it. *)
  rewrite Hdisk. exact fsimg_image_wf.
Qed.


(* ---------------------------------------------------------------------- *)
(* 4b. THE TRACE INVARIANT AT A NON-TRIVIAL [phi], DISK AND NON-DISK.      *)
(*                                                                        *)
(* [phi] above is a parameter, so the theorem is only as strong as what a  *)
(* client puts in it -- and [fun _ => True] is a legal choice.  This       *)
(* corollary is the demonstration that the slot is not vacuous: it         *)
(* instantiates [phi] at [fs_boot_pure], the pure content of the FS's      *)
(* DURABILITY invariant [FsCrash.P_fs_named] (the durable extent's         *)
(* geometry, plus: the physical image recovers to a committed view that IS *)
(* A FILE SYSTEM -- [FsDurSnap.snap_ok] of some abstract state -- and its  *)
(* log header is well-formed), and concludes it at                         *)
(* EVERY state the CSL-free operational semantics can reach -- across      *)
(* every power cycle, since [crash_inv] is fixed-layer and hence the same  *)
(* invariant at every era.                                                 *)
(*                                                                        *)
(* IT COSTS NO NEW PROOF.  [FsCrash.P_fs_project] is already the           *)
(* obligation [Hproj] -- the projection the power theorem runs at each     *)
(* PowerOn to tell a boot what disk it is booting on -- and                *)
(* [RiscvAdequacy.disk_proj_trace] is the adapter that promotes exactly    *)
(* that shape to [Hphi]'s.  The two hooks read the same fact off the same  *)
(* invariant; the difference is only where it is delivered (into a boot,   *)
(* versus out of the whole execution).                                     *)

Corollary xv6_fs_adequacy_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall t2 g2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\
    xv6_trace_pure fsimg_cov (FsImg.sb_logstart fsimg_sb) g2.
Proof.
  (* NOTHING IS LEFT BUT [phi].  The image went one rung up, so all this
     does is choose the pure trace property and hand over its Iris-side
     proof.  [logstart] is not an argument: the crash predicate sits at the
     SUPERBLOCK'S own log start (fs-cfg-boot.md stage (f) -- the boot seam's
     [fsc_logst] is tied to it), and [FsImg.sb_logstart fsimg_sb] IS the [2]
     this corollary used to pass, by conversion on the record literal. *)
  exact (xv6_power_adequacy_xv6Σ g
           (xv6_trace_pure fsimg_cov (FsImg.sb_logstart fsimg_sb))
           (xv6_trace_hook xv6Σ fsimg_cov (FsImg.sb_logstart fsimg_sb))
           Hgen0 Hpow Hdisk).
Qed.
