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
Require Import PowerBoot.   (* [boot_gstate]: one boot state, for the era-0 extent *)
Require Import FirstTok.    (* [fs_extent_of_image] *)
(* THE LITERAL mkfs IMAGE, for the generic FS theorem's [Hrec] vocabulary.
   (The corollaries AT the image live in [FsAdequacyImg.v] since stage
   (d2b); this import stays because §3b's statement is spelled in
   [FsBlocks]/[FsCrash] terms and the file's cone is measured below.)  This
   is the MACHINE-FACING half only ([fsimg_dk], its block view, and the one
   recovery fact) -- deliberately split out of [FsImgCheck.v] so that this
   file's cone gains [PStringBytes] + the generated [Kernel.FsImgRaw] and
   nothing else.  MEASURED, single-file [coqc] on the build VM: 3.63 s
   before this import, 3.51 s after -- the generated image is one compact
   [PrimString] literal, so loading it costs nothing worth naming.  Keep it
   that way: this file sits on the strictly serial build tail. *)
(* [ROOTDEV], for the two config ties the boot arm now carries *)
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

(* THE ERA-WIDE IMAGE HYPOTHESIS, and read its shape carefully.

   [RiscvAdequacy.riscv_power_adequacy] asks for a boot entailment at EVERY
   [g'] with [RiscvLang.boot_facts g'] -- one per era, for arbitrarily many
   power cycles -- and [boot_facts] says NOTHING about the disk's bytes
   ([virtio_reset] preserves [v_disk], which is exactly why a later era's
   disk is whatever the previous era WROTE).  So an image hypothesis about
   the initial machine's disk cannot reach the era fupd, and the honest
   statement quantifies over the eras: "every machine this system ever boots
   on carries the file system's image".

   THAT IS A STRENGTHENING OF WHAT THE FS COROLLARY USED TO ASSUME (one
   equation about [g]'s own disk), and it is the price of running
   [FsCfgBoot.fs_cfg_alloc] in the era fupd: the inode cache's configuration
   is now minted FROM THE ERA'S ACTUAL DISK, so the boot cone's assumed
   [namei("/")] contract is non-vacuous -- but nothing yet PROVES that xv6's
   own writes leave the disk image-shaped, which is the durability effort
   ([FsCrash.P_fs], claude-notes/design/crash.md).  Until it does, "boots
   twice on the image" is a hypothesis, not a theorem.
   claude-notes/projects/fs-cfg-boot.md records this as the (d2b) stop. *)
Definition fs_boot_image_eras (sb : fs_sb) (nib : nat) (cov : gset Z)
  : Prop :=
  forall g' : gstate,
    boot_facts g' ->
    fs_boot_image_wf (v_disk (g'.(gdev).(dvirtio))) XV6_DISK_BYTES
      sb nib cov.

(* THE PURE PROJECTION OF THE CRASH PREDICATE (stage H0, claude-notes/
   projects/durable-disk.md): what [FsCrash.P_fs_named] says about the
   PHYSICAL disk it is stated over -- the durable extent's geometry, and that
   the image recovers to a committed view that is FS-well-formed.

   This is [fs_boot_image_wf]'s SHAPE, and the point of the stage: the era
   hypothesis [fs_boot_image_eras] above ASSUMES a fact of this kind at every
   era, while this one is EXTRACTED from the crash predicate by
   [FsCrash.P_fs_project], which [RiscvAdequacy.riscv_power_adequacy] runs
   against its own [state_interp] at each PowerOn.  Stage I is what deletes
   the assumed form; H0 only builds the channel, so both are live here. *)
Definition fs_boot_pure (cov : gset Z) (ls : Z) (dk : Z -> bv 8) : Prop :=
  fs_extent cov ls XV6_DISK_BYTES /\
  exists D : gmap Z (list (bv 8)),
    fs_recovery (fs_blocks dk) D cov ls /\
    hdr_wf (fs_blocks dk) cov ls.

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
    (Hinv : invGS Σ) (γgen γstart γreg γd γdv γsw : gname) (g' : gstate) :
  ⊢ @power_interp Σ
       (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γdv γsw
          (P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv cov ls)) g' -∗
    ▷ P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv cov ls -∗
    ◇ ⌜fs_boot_pure cov ls (v_disk (g'.(gdev).(dvirtio)))⌝.
Proof.
  exact (disk_proj_trace XV6_DISK_BYTES
           (fun a b c d e => P_fs_named a XV6_DISK_BYTES b c d e cov ls)
           (fs_boot_pure cov ls)
           (fun a b c d e dk =>
              P_fs_project a XV6_DISK_BYTES b c d e cov ls dk)
           Hinv γgen γstart γreg γd γdv γsw g').
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
    (Hinv : invGS Σ) (γgen γstart γreg γd γdv γsw : gname) (g' : gstate) :
  ⊢ @power_interp Σ
       (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γdv γsw
          (P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv cov ls)) g' -∗
    ▷ P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv cov ls -∗
    ◇ ⌜xv6_trace_pure cov ls g'⌝.
Proof.
  iIntros "Hsi HP".
  (* the era-side fact first: its conclusion is PURE, so [state_interp] is
     not spent and the disk projection still has it *)
  iDestruct (power_interp_resv_ok with "Hsi") as %Hresv.
  iDestruct (fs_trace_hook Σ cov ls Hinv γgen γstart γreg γd γdv γsw g'
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
    fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
      sb nib cov ->
    (* THE PROJECTION THE POWER THEOREM PROVES AT THIS ERA (stage H0): the
       crash predicate's own reading of the disk this boot runs on, extracted
       from [P_fs] rather than assumed.  NOT USED YET -- it is the premise
       stage H1 mints the FS configuration from and stage I replaces [Himg]
       with; H0 only builds the channel and proves it carries the fact. *)
    fs_boot_pure cov (FsImg.sb_logstart sb)
      (v_disk (g.(gdev).(dvirtio))) ->
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
    intros Hbf Himg Hpure Hcp. iIntros "Hres".
    (* THE SEAM, ASSEMBLED FROM THE SLOT EQUATION and put in the
       intuitionistic context: it rides [FirstTok.first_boot_persist] from
       here to forkret's first arm.  Both directions are the identity once
       [Hcp] has rewritten the field away, which is exactly what "the FS's
       predicate IS the crash predicate" means. *)
    iAssert (fs_crash_seam cov (FsImg.sb_logstart sb)) as "#Hseam".
    { rewrite /fs_crash_seam. iModIntro.
      rewrite Hcp. iSplitL; iIntros "H"; iExact "H". }
    iMod (boot_shared_alloc g XV6_DISK_BYTES sb nib cov Hbf Himg with "Hres")
      as (Hfd Hir Hpav Hbs HF γd γv)
      "(%Hdimg & #Htext & #Hdata & #Hstarted & #Hdev & #Hwinv &
        #Hcinv & #Hcert & Hharts & Hlk & Hgl & Hmdata & Hpark & Hpst & Hpavail & Huart &
        Hdlab & Hcfg & Hclaim & #Hdone & Hkpt & Hkmap & Hmir & Hpages & Hirauth &
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
    iSplitL "Hh0 Hhrest Hlk Hgl Hmfirst Hmnext Hpark Hpst Hpavail Hfs Hmir Hirslot Hirauth Htx Hdlab Hcfg Hclaim Hkpt Hkmap
             Hpages".
    { iApply (big_sepL_cpu_glue
                (fun c => WP (LoopE gen_id c : expr riscv_lang) @ ⊤
)%I).
      iSplitL "Hh0 Hlk Hgl Hmfirst Hmnext Hpark Hpst Hpavail Hfs Hmir Hirslot Hirauth Htx Hdlab Hcfg Hclaim Hkpt Hkmap
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
                  (v_disk (g.(gdev).(dvirtio))) sb nib cov XV6_DISK_BYTES
                  (boot_regs_of_facts g Hbf 0%fin) fin_0_z Hprun Hplen Hlive
                  Himg
                  with "Htext Hdata Hh0 Hstarted Hlk Hgl Hmfirst Hmnext Hpark Hpst Hpavail
                        Hfs Hmir Hirslot Hirauth Hcert Hseam
                        Hdev Hwinv Htx Hsent Hlb Hdlab Hcfg Hclaim Hdone Hkpt Hkmap
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
                   (γgen γstart γreg γd γdv γsw : gname) (g' : gstate),
       ⊢ @power_interp Σ
            (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γdv γsw
               (P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv cov
                  (FsImg.sb_logstart sb))) g' -∗
         ▷ P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv cov (FsImg.sb_logstart sb) -∗
         ◇ ⌜phi g'⌝)
    (* the hypotheses about the machine: it is off, and nothing has ever
       run.  Everything else a boot needs -- RAM total and holding the loaded
       kernel image, the per-hart reset registers, the reset devices -- is
       supplied per ERA by [RiscvLang.boot_shape], which the power thread's
       PowerOn transition establishes itself. *)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (* ...AND ONE ABOUT THE DISK, WHICH IS NEW (fs-cfg-boot.md (d2b)): every
       era boots on a machine whose disk carries the file system's image.
       See [fs_boot_image_eras] for why this cannot be one equation about
       [g].  It is what [FsCfgBoot.fs_cfg_alloc] reads the configuration's
       geometry off, and the conclusion mentions none of it -- so this is
       the price of a NON-VACUOUS boot cone, not a weaker theorem about
       reducibility.  [FsAdequacyImg.v] discharges it at the literal mkfs
       image. *)
    (Himg : fs_boot_image_eras sb nib cov) :
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
     committed state, which is all [P_fs_alloc] needs.  Nothing about the
     conclusion changes, nothing new is assumed, and this theorem's
     premises are byte-identical to what they were -- what it says about a
     power cycle is still nothing, because [D0] is existential and never
     mentioned again.  [xv6_fs_adequacy] below is the theorem that makes a
     DURABILITY claim, by pinning [D0] to mkfs's own recovery. *)
  destruct (fs_recovery_total (fs_blocks (v_disk (g.(gdev).(dvirtio))))
              cov (FsImg.sb_logstart sb)) as [D0 Hrec].
  (* the durable disk's extent, read off the image at the first boot state
     ([PowerBoot.boot_gstate g] is one; [fs_extent] says nothing about the
     bytes) *)
  assert (Hext : fs_extent cov (FsImg.sb_logstart sb) XV6_DISK_BYTES).
  { pose proof (Himg (PowerBoot.boot_gstate g)
                  (proj2 (proj2 (PowerBoot.boot_shape_boot_gstate g)))) as Hw.
    destruct Hw as (Hwf & _ & _ & _ & _ & Hnibeq & Hcovin & Hcovmeta & _).
    exact (FirstTok.fs_extent_of_image _ _ _ _ _ Hwf Hnibeq Hcovin Hcovmeta). }
  (* ...and the header invariant [P_fs_alloc] now carries (stage B's
     [hdr_wf]): the image's log is clean, so [hdr_wf_zero] closes it.  The
     boot state's disk IS [g]'s ([virtio_reset] keeps [v_disk]), so the
     image sweep applies by conversion. *)
  assert (Hhwf : hdr_wf (fs_blocks (v_disk (g.(gdev).(dvirtio)))) cov
                   (FsImg.sb_logstart sb)).
  { pose proof (Himg (PowerBoot.boot_gstate g)
                  (proj2 (proj2 (PowerBoot.boot_shape_boot_gstate g)))) as Hw.
    destruct Hw as (Hwf & _).
    apply hdr_wf_zero. rewrite /log_hdr_bno /hdr_n.
    exact (FsImg.fsimg_wf_log _ _ Hwf). }
  (* THE CRASH PREDICATE AT ERA 0: the record from mkfs's recovery fact,
     and the DURABLE DISK's fragments -- the whole [0, XV6_DISK_BYTES) of the
     initial image, handed over once by the power theorem and owned by the
     predicate from here on (design/crash.md, "The durable disk").  This is
     the only place the initial image is ever named. *)
  apply (riscv_power_adequacy Σ boot_D NPROC XV6_DISK_BYTES g
           (fun (γd γsw γreg γst γdv : gname) =>
              P_fs_named γd XV6_DISK_BYTES γsw γreg γst γdv cov
                (FsImg.sb_logstart sb))
           ltac:(intros γd γsw γreg γst γdv; iIntros "(Hfr & Hsw & Hdv)";
                 iMod (P_fs_alloc γsw γreg γst γdv _ D0 cov
                         (FsImg.sb_logstart sb) Hrec Hhwf
                         with "[$Hsw $Hdv]") as (γs) "(%Hseq & HP & _)";
                 iModIntro; rewrite /P_fs_named;
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
           ltac:(intros γd γsw γreg γst γdv dk;
                 exact (P_fs_project γd XV6_DISK_BYTES γsw γreg γst γdv cov
                          (FsImg.sb_logstart sb) dk))
           (* CUSTODY AT BIRTH (durable-disk 1a): the era's mirror is the
              picture of the era's own disk, and [P_fs_swap] IS the hook's
              obligation -- it installs [P_fs]'s custody arm at that
              variable in the same fupd, so the era boots already holding a
              true picture and the swap receipt. *)
           (fun dk => mirror_of (fs_blocks dk))
           ltac:(intros γd γsw γreg γst γdv Er gen dk;
                 exact (P_fs_swap γd XV6_DISK_BYTES γsw γreg γst γdv cov
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
  destruct Hshape as (Hi & Gg & Gs & Gr & Gt & Gdv & Gsw & ->).
  (* one [_] fewer since durable-disk 2b-inode-3: [fsTopG] is an [xv6G]
     member now, so the section generalises one class less. *)
  refine (@xv6_boot_era Σ (RiscvGS Σ _ HE) _ _ _ _ _ _ gen g' sb nib cov Hbf
            (Himg g' Hbf) Hpure _).
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3b. THE SAME THEOREM WITH THE FILE SYSTEM'S DURABILITY INVARIANT IN     *)
(*     THE SLOT (phase C2b/D1 stage 5).                                    *)
(*                                                                        *)
(* [xv6_power_adequacy] above leaves the crash predicate at [True]: the    *)
(* machine never gets stuck, and nothing is claimed about what survives a  *)
(* power cycle.  This one instantiates the slot at [FsCrash.P_fs_named] -- *)
(* the FS's own record: a committed history whose last element is what the *)
(* PHYSICAL disk recovers to.  Because [crash_inv] is allocated ONCE into  *)
(* the fixed layer, that invariant is the same one across every boot, so   *)
(* the property it carries spans the power cycles the theorem quantifies   *)
(* over.                                                                   *)
(*                                                                        *)
(* THE ONE HYPOTHESIS IS mkfs's: the disk the machine powers on with       *)
(* recovers to SOME committed state [D0].  It is not vacuous and it is not *)
(* an assumption about the proof -- [FsCrash.fs_recovery_total] says such a *)
(* [D0] always exists, and [P_fs_alloc] is what turns it into the record.  *)
(* Everything else about the FS -- that its own writes maintain the        *)
(* invariant -- is the WAL fupds' business, carried by the write permits    *)
(* the log functions take (phase C2b/D1 stage 4).                          *)
(*                                                                        *)
(* ...AND [FsAdequacyImg.xv6_fs_adequacy_xv6Σ] DISCHARGES IT AT THE        *)
(* LITERAL mkfs IMAGE.  This theorem keeps [D0], [cov] and [logstart]      *)
(* abstract, because a generic statement should; but that corollary        *)
(* instantiates the disk at [FsImgDisk.fsimg_dk] --                        *)
(* the 2,048,000 bytes [mkfs] actually wrote (kernel-rocq/FsImgRaw.v) --    *)
(* and supplies [Hrec] from [FsImgDisk.fsimg_recovery], which is           *)
(* [fs_recovery_clean] at that image's own zero log header.  So mkfs's      *)
(* obligation is not merely satisfiable at this instance, it is PROVED, and *)
(* what the image MEANS as a file system (its superblock, [FsImg.fsimg_wf], *)
(* and that /init /sh /echo /sync hold exactly the tracked ELF raws) is     *)
(* [iris/FsImgCheck.v] -- deliberately NOT on this file's cone.            *)
(* ---------------------------------------------------------------------- *)

Theorem xv6_fs_adequacy Σ
    `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ, !fdslotGpreS Σ,
      !irefslotGpreS Σ, !bioslotGpreS Σ}
    (g : gstate) (cov : gset Z)
    (D0 : gmap Z (list (bv 8)))
    (sb : fs_sb) (nib : nat)
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
                   (γgen γstart γreg γd γdv γsw : gname) (g' : gstate),
       ⊢ @power_interp Σ
            (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γdv γsw
               (P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv cov
                  (FsImg.sb_logstart sb))) g' -∗
         ▷ P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv cov (FsImg.sb_logstart sb) -∗
         ◇ ⌜phi g'⌝)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (* mkfs's obligation, at the image the machine powers on with.
       [logstart] IS THE SUPERBLOCK'S OWN, no longer a free parameter
       (fs-cfg-boot.md stage (f)): the boot cone builds
       [FsCrash.fs_crash_seam] at the configuration the era mints, whose
       [fsc_logst] is [FsImg.sb_logstart sb] by
       [FsCfgBoot.fs_boot_supply]'s tie, so a crash predicate at some OTHER
       log start could never be sealed into [FsReady.fs_ready].  The mkfs
       corollary already instantiated it at exactly this value. *)
    (Hrec : fs_recovery (fs_blocks (v_disk (g.(gdev).(dvirtio)))) D0
              cov (FsImg.sb_logstart sb))
    (* ...and the era-wide image hypothesis the boot-era FS mint needs, at
       THE SAME [cov] (ruling R4: the parameter stays here and the corollary
       instantiates it at the image's own range).  [xv6_power_adequacy]'s
       note is the whole story. *)
    (Himg : fs_boot_image_eras sb nib cov) :
  forall t2 g2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ phi g2.
Proof.
  (* the durable disk's extent, read off the image at the first boot state
     ([PowerBoot.boot_gstate g] is one; [fs_extent] says nothing about the
     bytes) *)
  assert (Hext : fs_extent cov (FsImg.sb_logstart sb) XV6_DISK_BYTES).
  { pose proof (Himg (PowerBoot.boot_gstate g)
                  (proj2 (proj2 (PowerBoot.boot_shape_boot_gstate g)))) as Hw.
    destruct Hw as (Hwf & _ & _ & _ & _ & Hnibeq & Hcovin & Hcovmeta & _).
    exact (FirstTok.fs_extent_of_image _ _ _ _ _ Hwf Hnibeq Hcovin Hcovmeta). }
  (* ...and stage B's header invariant, from the image's clean log exactly
     as [xv6_power_adequacy] derives it *)
  assert (Hhwf : hdr_wf (fs_blocks (v_disk (g.(gdev).(dvirtio)))) cov
                   (FsImg.sb_logstart sb)).
  { pose proof (Himg (PowerBoot.boot_gstate g)
                  (proj2 (proj2 (PowerBoot.boot_shape_boot_gstate g)))) as Hw.
    destruct Hw as (Hwf & _).
    apply hdr_wf_zero. rewrite /log_hdr_bno /hdr_n.
    exact (FsImg.fsimg_wf_log _ _ Hwf). }
  (* THE CRASH PREDICATE AT ERA 0: the record from mkfs's recovery fact,
     and the DURABLE DISK's fragments -- the whole [0, XV6_DISK_BYTES) of the
     initial image, handed over once by the power theorem and owned by the
     predicate from here on (design/crash.md, "The durable disk").  This is
     the only place the initial image is ever named. *)
  apply (riscv_power_adequacy Σ boot_D NPROC XV6_DISK_BYTES g
           (fun (γd γsw γreg γst γdv : gname) =>
              P_fs_named γd XV6_DISK_BYTES γsw γreg γst γdv cov
                (FsImg.sb_logstart sb))
           ltac:(intros γd γsw γreg γst γdv; iIntros "(Hfr & Hsw & Hdv)";
                 iMod (P_fs_alloc γsw γreg γst γdv _ D0 cov
                         (FsImg.sb_logstart sb) Hrec Hhwf
                         with "[$Hsw $Hdv]") as (γs) "(%Hseq & HP & _)";
                 iModIntro; rewrite /P_fs_named;
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
           ltac:(intros γd γsw γreg γst γdv dk;
                 exact (P_fs_project γd XV6_DISK_BYTES γsw γreg γst γdv cov
                          (FsImg.sb_logstart sb) dk))
           (* CUSTODY AT BIRTH (durable-disk 1a): the era's mirror is the
              picture of the era's own disk, and [P_fs_swap] IS the hook's
              obligation -- it installs [P_fs]'s custody arm at that
              variable in the same fupd, so the era boots already holding a
              true picture and the swap receipt. *)
           (fun dk => mirror_of (fs_blocks dk))
           ltac:(intros γd γsw γreg γst γdv Er gen dk;
                 exact (P_fs_swap γd XV6_DISK_BYTES γsw γreg γst γdv cov
                          (FsImg.sb_logstart sb) dk Er gen))
           (* THE TRACE HOOK, threaded straight through: this layer fixes the
              crash predicate but says nothing about what the client reads off
              it, so [phi]/[Hphi] pass down unexamined. *)
           phi Hphi
           Hgen0 Hpow).
  intros F HE gen g' Hbf Hpure Hshape.
  (* THE RECORD'S SHAPE, destructed: every projection below reduces, which
     is what makes the crash slot's value -- and hence the seam -- visible
     to the boot cone at all.  [RiscvAdequacy.boot_fixedGS]'s header is the
     argument for why an equation about [riscv_crash_pred] alone would not
     do (the ghost CLASS instances have to agree too). *)
  destruct Hshape as (Hi & Gg & Gs & Gr & Gt & Gdv & Gsw & ->).
  (* one [_] fewer since durable-disk 2b-inode-3: [fsTopG] is an [xv6G]
     member now, so the section generalises one class less. *)
  refine (@xv6_boot_era Σ (RiscvGS Σ _ HE) _ _ _ _ _ _ gen g' sb nib cov Hbf
            (Himg g' Hbf) Hpure _).
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

(* THE ASSUMPTION AUDIT'S TARGET, and it stays in THIS file deliberately.

   This corollary is the power theorem at the concrete functor list: every
   class is discharged, so "nothing about the ghost state is assumed" is
   checked rather than claimed.  What it does NOT do is name the literal mkfs
   image -- [Himg] is left as a premise here -- and that is load-bearing for
   [SystemAssumptions.v]: a statement mentioning [FsImgDisk.fsimg_dk] pulls
   Rocq's [PrimString]/[PrimInt63] primitives into [Print Assumptions]
   (MEASURED: ten extra entries, on any constant naming the image), which
   would bury the eight-entry baseline the audit diffs against
   (durable-notes' "adequacy-print baseline").  The image-DISCHARGED
   corollaries therefore live in [FsAdequacyImg.v], one leaf up, where
   [FsImgCheck]'s citations are in scope and where their ~200 s of
   [vm_compute] stays off this file's strictly serial build tail. *)
Corollary xv6_power_adequacy_xv6Σ (g : gstate)
    (sb : fs_sb) (nib : nat) (cov : gset Z)
    (phi : gstate -> Prop)
    (Hphi : forall (Hinv : invGS xv6Σ)
                   (γgen γstart γreg γd γdv γsw : gname) (g' : gstate),
       ⊢ @power_interp xv6Σ
            (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γdv γsw
               (P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv cov
                  (FsImg.sb_logstart sb))) g' -∗
         ▷ P_fs_named γd XV6_DISK_BYTES γsw γreg γstart γdv cov
             (FsImg.sb_logstart sb) -∗
         ◇ ⌜phi g'⌝)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (Himg : fs_boot_image_eras sb nib cov) :
  forall t2 g2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ phi g2.
Proof.
  apply (xv6_power_adequacy xv6Σ g sb nib cov phi Hphi Hgen0 Hpow Himg).
Qed.

(* ---------------------------------------------------------------------- *)
(* 4b. THE TRACE INVARIANT AT A NON-TRIVIAL [phi], DISK AND NON-DISK.      *)
(*                                                                        *)
(* [phi] above is a parameter, so the theorem is only as strong as what a  *)
(* client puts in it -- and [fun _ => True] is a legal choice.  This       *)
(* corollary is the demonstration that the slot is not vacuous: it         *)
(* instantiates [phi] at [fs_boot_pure], the pure content of the FS's      *)
(* DURABILITY invariant [FsCrash.P_fs_named] (the durable extent's         *)
(* geometry, plus: the physical image recovers to a committed view that is *)
(* FS-well-formed, and its log header is well-formed), and concludes it at *)
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
(* ---------------------------------------------------------------------- *)

Corollary xv6_trace_invariant (g : gstate)
    (sb : fs_sb) (nib : nat) (cov : gset Z)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (Himg : fs_boot_image_eras sb nib cov) :
  forall t2 g2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\
    xv6_trace_pure cov (FsImg.sb_logstart sb) g2.
Proof.
  apply (xv6_power_adequacy_xv6Σ g sb nib cov
           (xv6_trace_pure cov (FsImg.sb_logstart sb))
           (xv6_trace_hook xv6Σ cov (FsImg.sb_logstart sb))
           Hgen0 Hpow Himg).
Qed.

(* THE ASSUMPTION AUDIT IS [SystemAssumptions.v], NOT A LINE HERE.
   [Print Assumptions xv6_power_adequacy_xv6Σ] used to sit at this point, and
   it measured 95 s of this file's 98.6 s -- on the strictly serial build tail,
   so ~30 % of a clean build's wall clock, paid on every build.  It now lives
   in a file [iris/_CoqProject] deliberately does not list, run by `make audit`
   and by CI after the build.  Do not put it back here.
   (claude-notes/optimization.md records why the command is that expensive.) *)

(* WHERE THE IMAGE WENT.  [xv6_fs_adequacy_xv6Σ] -- the FS form at this same
   functor list, at the LITERAL mkfs image, with mkfs's recovery obligation
   and every image hypothesis DISCHARGED -- is now
   [FsAdequacyImg.xv6_fs_adequacy_xv6Σ], beside
   [FsAdequacyImg.xv6_power_adequacy_fsimg].  It moved for the reason
   fs-cfg-boot.md's probe-STOP-3 ruling gives: discharging the image
   hypotheses needs [FsImgCheck.v]'s ~200 s of [vm_compute] in the cone, and
   this file is the serial tail of every build.  [FsImgDisk] stays imported
   here (3.6 s -> 3.5 s, measured: the image is one compact [PrimString]
   literal) because the generic theorem's [Hrec] is stated in its
   vocabulary. *)
