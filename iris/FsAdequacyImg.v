(* ====================================================================== *)
(* FsAdequacyImg.v -- THE SYSTEM THEOREM AT THE LITERAL mkfs IMAGE.        *)
(*                                                                        *)
(* [SystemAdequacy.v] proves the two generic theorems.  Since              *)
(* claude-notes/projects/fs-cfg-boot.md stage (d2b) both of them carry an   *)
(* IMAGE HYPOTHESIS -- because the boot-era fupd now MINTS the inode        *)
(* cache's [IcacheRef.icfg] and the file system's [FsCfg.fscfg] off the     *)
(* era's own disk ([FsCfgBoot.fs_cfg_alloc], wired in at                   *)
(* [BootShared.boot_shared_alloc]) instead of resolving two hardcoded       *)
(* all-[1%positive] records that made the boot cone's one assumed contract  *)
(* vacuous.  THIS FILE IS WHERE THAT HYPOTHESIS IS DISCHARGED at the        *)
(* 2,048,000 bytes mkfs actually wrote, out of [FsImgCheck.v]'s citations.  *)
(*                                                                        *)
(* WHY IT IS A LEAF OF ITS OWN (fs-cfg-boot.md, probe-STOP-3's ruling).     *)
(* Discharging the image sweeps needs [FsImgCheck.v] in the cone, and that  *)
(* file is ~200 s of [vm_compute] ([fsimg_wf_ok] alone is 106 s, half of it *)
(* [Qed]'s re-check).  [SystemAdequacy.v] is the strictly serial tail of    *)
(* every build, so the ~200 s must not land there; here it is paid by a     *)
(* file nothing imports.  This file itself computes NOTHING: every line is  *)
(* a citation, and the whole leaf compiles in seconds given                *)
(* [FsImgCheck.vo].                                                        *)
(*                                                                        *)
(* THE TWO COROLLARIES, AND WHY THEIR NAMES ARE NOT SYMMETRIC.             *)
(* [xv6_fs_adequacy_xv6Σ] MOVED here from [SystemAdequacy.v] unchanged in   *)
(* meaning (same statement, plus the new era hypothesis).                   *)
(* [xv6_power_adequacy_fsimg] is NEW: the power theorem at the image.  Its  *)
(* [_xv6Σ] sibling stays in [SystemAdequacy.v] because that is the          *)
(* [Print Assumptions] target ([SystemAssumptions.v]), and a statement      *)
(* naming [FsImgDisk.fsimg_dk] drags Rocq's [PrimString]/[PrimInt63]        *)
(* primitives into the audit -- MEASURED, ten extra entries -- which would  *)
(* bury the eight-entry baseline the audit is diffed against.  Both files'  *)
(* headers say so; do not "tidy" the pair into one place.                   *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list list_numbers.
From iris.program_logic Require Import language.
Require Import RiscvLang.
Require Import VirtioModel.
Require Import FsImg.
Require Import FsCfgBoot.       (* [fs_boot_image_wf], moved down at stage (f) *)
Require Import SystemAdequacy.  (* the two generic theorems, and [xv6Σ] *)
Require Import FsImgDisk.       (* [fsimg_dk] / [fsimg_D0] / [fsimg_recovery] *)
Require Import FsImgCheck.      (* what the image MEANS as a file system *)
Local Open Scope Z_scope.

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
  exact fsimg_links_eq.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3.  ...AT EVERY ERA.                                                    *)
(*                                                                        *)
(* READ THIS PREMISE CAREFULLY.  [SystemAdequacy.fs_boot_image_eras] is     *)
(* quantified over the eras, not stated at [g], and it has to be: the boot  *)
(* entailment [RiscvAdequacy.riscv_power_adequacy] asks for is at EVERY     *)
(* [g'] with [boot_facts g'], and [boot_facts] says nothing about the       *)
(* disk's bytes -- a second era's disk is whatever the first era WROTE      *)
(* ([virtio_reset] preserves [v_disk], which is the one crash-surviving     *)
(* component).  So the honest hypothesis is: EVERY machine this system      *)
(* boots on carries the mkfs image -- strictly stronger than the            *)
(* one equation about [g] the FS corollary used to take.                    *)
(*                                                                        *)
(* IT IS A HYPOTHESIS AND NOT YET A THEOREM.  What would discharge it is    *)
(* the durability effort: that xv6's own writes leave the disk a well       *)
(* formed file system, which is [FsCrash.P_fs]'s business                   *)
(* (claude-notes/design/crash.md) and is not proved.  The trade this stage  *)
(* makes is deliberate: before it, the boot cone's assumed [namei("/")]     *)
(* contract was VACUOUS at these corollaries' own instance                  *)
(* ([icfg_nib = 0]), so the theorem was unconditional about nothing.        *)
(* fs-cfg-boot.md (d2b) records it.                                        *)
(* ---------------------------------------------------------------------- *)
Definition fsimg_at_every_era (g : gstate) : Prop :=
  forall g' : gstate,
    boot_facts g' ->
    v_disk (g'.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk.

Lemma fsimg_boot_image_eras (g : gstate) :
  fsimg_at_every_era g ->
  fs_boot_image_eras fsimg_sb fsimg_nib fsimg_cov.
Proof.
  intros Hdisk g' Hbf. rewrite /fs_boot_image_eras.
  rewrite (Hdisk g' Hbf). exact fsimg_image_wf.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4.  THE TWO COROLLARIES.                                                *)
(* ---------------------------------------------------------------------- *)

(* THE POWER THEOREM AT THE IMAGE.  The crash predicate is [True] here (see
   [SystemAdequacy.xv6_power_adequacy]): nothing is claimed about what
   survives a power cycle, only that the machine never gets stuck.  What the
   image buys is that the boot cone's configuration is REAL -- the whole
   point of stage (d2b). *)
Corollary xv6_power_adequacy_fsimg (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (Hdisk : fsimg_at_every_era g) :
  forall t2 g2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\
    xv6_trace_pure fsimg_cov (FsImg.sb_logstart fsimg_sb) g2.
Proof.
  apply (xv6_trace_invariant g fsimg_sb fsimg_nib fsimg_cov Hgen0 Hpow
           (fsimg_boot_image_eras g Hdisk)).
Qed.

(* ...AND THE FS FORM, at the same functor list AND AT THE LITERAL mkfs
   IMAGE.  MOVED HERE from [SystemAdequacy.v] by fs-cfg-boot.md's
   probe-STOP-3 ruling; the statement is the same one it had there, plus the
   era hypothesis §3 explains.

   NOTHING ABOUT THE FILE SYSTEM IS ASSUMED BEYOND THAT.  The generic
   theorem takes mkfs's recovery obligation as [Hrec]; here the initial disk
   IS the image mkfs built -- [FsImgDisk.fsimg_dk] is kernel-rocq/FsImgRaw.v's
   2,048,000 bytes, zero-padded beyond them (a virtio disk reads zeroes past
   the file backing it, and [XV6_DISK_BYTES] is larger than the image) -- and
   the obligation is DISCHARGED by [FsImgDisk.fsimg_recovery], which is
   [FsCrash.fs_recovery_clean] at that image's own zero log header.

   THE PARAMETERS, and why each is what it is:
     [logstart] is pinned to [2], the IMAGE'S OWN [logstart]
       ([FsImgCheck.fsimg_sb_logstart] is what checks that the superblock
       says so);
     [D0] is [FsImgDisk.fsimg_D0 fsimg_cov] -- the image's own home blocks,
       since a clean log replays nothing;
     [cov] is [fsimg_cov] (§1), NO LONGER PARAMETRIC: stocking the inode
       pool from the image forces every block a live inode names into it;
     [sb]/[nib] are the parsed superblock and its inode region's 13 blocks.

   What the image MEANS as a file system -- [FsImg.fsimg_wf], and that
   /init /sh /echo /sync hold exactly the tracked ELF raws the U-mode proofs
   reason about -- is [iris/FsImgCheck.v], which IS on this file's cone and
   is why this file is not [SystemAdequacy.v]. *)
Corollary xv6_fs_adequacy_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk)
    (Hdisk' : fsimg_at_every_era g) :
  forall t2 g2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\
    xv6_trace_pure fsimg_cov (FsImg.sb_logstart fsimg_sb) g2.
Proof.
  (* [logstart] IS NO LONGER AN ARGUMENT: [xv6_fs_adequacy] now takes the
     crash predicate at the SUPERBLOCK'S own log start (fs-cfg-boot.md stage
     (f) -- the boot seam's [fsc_logst] is tied to it), and
     [FsImg.sb_logstart fsimg_sb] IS the [2] this corollary used to pass,
     by conversion on the record literal. *)
  apply (xv6_fs_adequacy xv6Σ g fsimg_cov (FsImgDisk.fsimg_D0 fsimg_cov)
           fsimg_sb fsimg_nib
           (* THE TRACE INVARIANT, at the FS's own durability record: the
              same [phi] [SystemAdequacy.xv6_fs_trace_invariant] takes for the
              power theorem, discharged by the same [xv6_trace_hook]. *)
           (xv6_trace_pure fsimg_cov (FsImg.sb_logstart fsimg_sb))
           (xv6_trace_hook xv6Σ fsimg_cov (FsImg.sb_logstart fsimg_sb))
           Hgen0 Hpow).
  - (* mkfs's obligation.  [fsimg_P] IS [fs_blocks fsimg_dk], so once the
       disk is rewritten to the image this is literally [fsimg_recovery]. *)
    rewrite Hdisk. exact (FsImgDisk.fsimg_recovery fsimg_cov).
  - exact (fsimg_boot_image_eras g Hdisk').
Qed.
