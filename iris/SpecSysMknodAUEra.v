(* SpecSysMknodAUEra.v -- sys_mknod's ATOMIC-UPDATE contract AT THE ERA
   WALK: [SpecSysMknodAU]'s statement with the three things the landed
   inventory forces changed, and nothing else.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W.  A PARALLEL
   FORM beside [SpecSysMknodAU.wp_sys_mknod_au] -- R10: that file does not
   move.

   ==== (1) THE FRAME IS RE-STATED, AND THAT IS AN UPSTREAM FINDING ======

   The intent was to reuse [SpecSysMknodAU.wp_sys_mknod_au_frame]
   verbatim.  It cannot be reused, because the ustate sweep converted it
   MECHANICALLY and its continuation is now UNPROVABLE: it binds
   [(mf, ns', P')] and hands back [proc_priv .. (us_upt U P')], while
   sys_mknod's own contract -- converted in the same sweep, and correctly
   -- binds a fourth [M' : gmap Z (bv 8)] and hands back
   [proc_priv .. (upd_usM (us_upt U P') M')].  The image MOVES across
   argstr (its fetchstr faults user pages in), so no proof of sys_mknod can
   deliver the frame's shape.  The frame below is therefore
   [SpecSysMknod.wp_sys_mknod_sconf_body] at the CURRENT head, abstracted
   over the AU-side extras exactly as the frozen frame abstracts over its
   own -- i.e. the frozen frame with its [M'] binder restored.  Fixing
   [SpecSysMknodAU] itself is upstream's call (R10 forbids this lane
   moving it); one line and one binder.

   ==== (2) THE TRACE PREMISE IS AT THE ERA LEND ========================

   [SpecSysMknodAU.mknod_walk_pre] rides [ax_hops_from dv_half].  The only
   nameiparent-side trace walk that exists is the ERA one
   ([SpecNparWrapEra], lane A-iii), and it consumes
   [ax_hops_from (elend ...)] -- a DIFFERENT ghost, so the two families do
   not convert.  A dv-firing nameiparent walk would be a second 5000-line
   copy of ProofNamex AND, per [FsAbsEraMknod]'s header, its hops could
   not reach the AU's fire points anyway.  So this form carries
   [FsAbsEraMknod.mknod_walk_pre_era] / [mknod_walk_dead_era] -- the era
   twins that file landed for exactly this moment -- and the commits are
   [FsAbsMknodFire]'s authority-shaped pair (see that file's header for
   why the [astate]-shaped ones cannot be discharged against
   [InodeRegion.ftop_body] at all).

   ==== (3) THE ret-0 ESCAPE IS RETIRED (lane A-iii, 2026-08-28) ========

   This arm used to read [mknod_post_ok_era ∨ mknod_au_pre_era], and the
   escape was the era walk's absolute-path scope: sys_mknod reads its path
   from USER memory and no premise can pin it (SpecFetchstr: "they came
   from user memory"), so on a fetched string that did not begin with
   SLASH this proof had no AU-carrying create to call and handed the
   bundle back unspent.

   The relative-start walk removed the reason, and with it the disjunct.
   [SpecCreateAU] now takes [FsAbsStart.ep_start] -- the trace deferred in
   the START INUM -- and has no absolute-path premise at all, so the proof
   calls ONE create contract for every fetched string; the [destruct] on
   the first byte and the 300-line landed-create branch under it are gone
   from [ProofSysMknodAU].  A [ret = 0] is now a RECEIPT unconditionally,
   which is what makes the theorem say anything about init's "console" and
   "sh" (relative, cwd = ROOTINO).

   [mknod_post_fail_era]'s first disjunct still IS "the whole bundle
   back", and it is still reachable and still honest: that is the argstr
   failure, where nothing fs-visible happened.

   ==== WHAT IS UNCHANGED ==============================================

   Everything else, deliberately: [mknod_post_ok_era] is
   [SpecSysMknodAU.mknod_post_ok] with the commit at the new shape (it is
   [SpecCreateAU.cau_ok] under an [∃ i] plus the region bound create's own
   post already states), and [mknod_post_fail_era] is
   [mknod_post_fail] with the same substitution (its second disjunct is
   [SpecCreateAU.cau_fail] under an [∃ pl]).  The three-way fold, the
   fetched-path existential, and the DETERMINISM: NONE stance of the -1
   arm are the frozen file's. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecPrintk.      (* [printk_env], [printk_gen_contract] *)
Require Import SpecDirlink.     (* [ic_sleeplocks], [ireg_blocks_ok] *)
Require Import SpecCreate.      (* [create_slots], [create_units], [T_DEVICE] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Require Import SpecSysMknod.   (* [K_sys_mknod]                        *)
Require Import FsTree.
Require Import FsBytesGamma.
Require Import SpecSysMknodAU.   (* [dev_arg], and the frozen statement  *)
Require Import FsAbsEraMknod.    (* the era twins of the walk predicates *)
Require Import FsAbsMknodFire.   (* the authority-shaped commits         *)
Require Import SpecCreateAU.     (* [cau_ok] / [cau_fail]                *)
Require Import FsAbs.            (* LAST (FsAbs's own rule)              *)
Import Defs.

Local Open Scope Z_scope.

Section SysMknodAUEra.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* everything the AU caller hands in, at the mask floor [∅] *)
  Definition mknod_au_pre_era Γ (γfs : fs_names) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (mknod_walk_pre_era γfs P Pmiss
     ∗ acre_commit_at Γ ∅ (ADev ma mi) Φok
     ∗ dlookup_commit_at Γ ∅ Φex)%I.

  (* ret 0's real arm: [SpecSysMknodAU.mknod_post_ok], which is
     [SpecCreateAU.cau_ok] at the fetched path beside the region bound
     create's own post already states. *)
  Definition mknod_post_ok_era Γ (ma mi : Z) (P : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (∃ (pl : list (bv 8)) (i : Z),
       ⌜0 < i < 16 * Z.of_nat icfg_nib⌝ ∗
       cau_ok Γ ma mi P Φok Φex pl i)%I.

  (* ret -1's three-way fold, the frozen file's verbatim: nothing
     fs-visible happened (argstr failed, or the path was relative -- see
     the header), or the walk died, or create failed at the parent. *)
  Definition mknod_post_fail_era Γ (γfs : fs_names) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (mknod_au_pre_era Γ γfs ma mi P Pmiss Φok Φex
     ∨ (∃ pl : list (bv 8),
          cau_fail Γ γfs ma mi P Pmiss Φok Φex pl))%I.

  (* the armed disjunction the continuation receives, keyed on a0.  NO
     ESCAPE on the [ret = 0] arm since lane A-iii: the walk takes the
     relative start, so a success is a RECEIPT whatever the fetched string
     looked like.  See the header. *)
  Definition mknod_arms_era Γ (γfs : fs_names) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (r : mword 64) : iProp Σ :=
    ((⌜r = (zero_reg : mword 64)⌝
      ∗ mknod_post_ok_era Γ ma mi P Φok Φex)
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ mknod_post_fail_era Γ γfs ma mi P Pmiss Φok Φex))%I.

End SysMknodAUEra.

(* the same seals the frozen file puts on its own pair, and for the same
   reason (big-op bodies behind Definitions at syscall altitude) *)
Global Typeclasses Opaque mknod_au_pre_era mknod_post_ok_era
  mknod_post_fail_era mknod_arms_era.

(* ===================================================================== *)
(*  THE FRAME: [SpecSysMknod.wp_sys_mknod_sconf_body] at the CURRENT      *)
(*  head, abstracted over the caller's bundle and the armed post -- i.e.  *)
(*  the frozen [wp_sys_mknod_au_frame] with its [M'] binder restored.     *)
(*  See the header's finding (1).                                        *)
(* ===================================================================== *)

Definition wp_sys_mknod_au_era_frame
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γf : gname)             (* ftable, kalloc, printk *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (ns : nat)                                          (* the iref ledger     *)
    (dqb dqs dqbs dqn : dfrac)
    (v0 v1 v2 : mword 64)                    (* syscall arguments 0 / 1 / 2 *)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (EXTRA : iProp Σ) (ARMS : mword 64 -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_mknod in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_mknod <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  (* ---- the block-layer geometry, threaded verbatim to create / iunlockput ---- *)
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  bitmap_geom_ok fsc_cov fsc_logst fsc_bmapstart fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  (* ---- ialloc's three geometry premises, and mkfs's [ushort] tie ---- *)
  1 < fsc_ninodes ->
  fsc_ninodes <= 16 * Z.of_nat icfg_nib ->
  fsc_ninodes < 2 ^ 31 ->
  16 * Z.of_nat icfg_nib <= 2 ^ 16 ->
  (* ---- ialloc's no-inodes arm calls printk, not panic ---- *)
  printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk ->
  (* ---- the reference allowance create's walk needs ---- *)
  (create_slots <= ns)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* create's own premise, inherited: the body runs with the base enabled *)
  eb = true ->
  (* THE THREE SYSCALL ARGUMENTS, read out of the trapframe page
     [proc_priv] carries: argstr takes 0, and the two argints take 1 and 2.
     The VALUES do not reach the postcondition -- [major] and [minor] are
     consumed inside create and the inode is dropped -- so all the caller
     owes is that the words exist. *)
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v0 ->
  pv_tf (us_V U) !! tf_arg_idx 1 = Some v1 ->
  pv_tf (us_V U) !! tf_arg_idx 2 = Some v2 ->
  sie_cap_gpr KT1 m K b pj -∗
  (* ENTERED WITH NO LOCK HELD: the depth is pinned at ZERO, so
     [CpuOwn.cpu_own_zero_empty] DERIVES [lks = ∅] and every order goal the
     five callees raise is [locks_below ∅ _]. *)
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, THREADED.  [emp] at [eb = true] -- which this
     contract's own premise forces -- so no caller gains an obligation. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* ---- the two persistent credentials ialloc's printk arm needs ---- *)
  printk_env fsc_printk fsc_uart fsc_disk -∗
  (* ---- the block layer ---- *)
  bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
  log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
  fs_crash_seam fsc_cov fsc_logst -∗
  gen_cert -∗
  dev_inv fsc_uart fsc_disk -∗
  disk_geom fsc_disk pd pav pu -∗
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res fsc_disk pd pav pu) -∗
  bslots 3 -∗
  (* ---- the inode cache, and the region ialloc claims out of ---- *)
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  (* ...AND THE SEALED REGIME (iclaim-ledger.md §3.2, RULING B).  Persistent,
     borrowed and never spent; it rides the SAME channel [ireg_inv] does,
     down to [SpecCreate] -> [SpecIalloc] -> [InodeRegion.ireg_claim_au],
     the one mover that mints a [c] column.  Its producer is the boot
     chain's ([IcacheRef.ity_shoot] on fsinit's returned [ireg_boot]), which
     terminates at the EXISTING [LinkForkretNF.wp_forkret_nf_ax] IOU -- no
     new axiom, and a premise pulls nothing into [Print Assumptions]. *)
  ireg_open -∗
  (* ---- the FOUR superblock cells (create reads all of them) ---- *)
  sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  (* argstr's page-table side, and create's (iget's ipool arm allocates) *)
  kalloc_env fsc_kalloc None -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* ---- the process, whole, and the reference allowance ---- *)
  iref_slots ns -∗
  proc_priv γf pj pid U -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b]: sys_mknod sleeps (begin_op,
     argstr's fault path, create and end_op all park), so it can return on
     another hart whatever SIE was doing. *)
  (* ---- THE AU SIDE (the one addition to the premise list) ---- *)
  EXTRA -∗
  wp_next true pj (fun (CID : CpuId) =>
  (* the image moves: the copy leaves may fault a page in, and copyout
     writes user memory -- milestone J item 1's ∃-weakened staging *)
  ∀ (mf : regfile) (ns' : nat) (P' : uptd) (M' : gmap Z (bv 8)),
      ⌜callee_saved m mf⌝ -∗
      (* the page table may have GROWN: argstr's fetchstr faults user pages
         in.  [uptd_ext] is argstr's own report, relayed. *)
      ⌜uptd_ext (pv_upt (us_V U)) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      bslots 3 -∗
      sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      (* NO ORDERING on the free pool: create both ALLOCATES and FREES. *)
      (* the allowance, spend-at-most: see the header's reference ledger *)
      (* THE LEDGER CLOSES, EXACTLY.  This used to be create's interval
         passed through; create states its figure exactly now (every failure
         arm returns the ledger whole, every success arm keeps ONE out), and
         this function's [iunlockput] is what hands that one back -- so all
         three arms end where they started.  A client can therefore
         re-establish its own [create_slots <= ns] and call again, which the
         interval could not support (FsSyscalls.v's note (S3)). *)
      ⌜ns' = ns⌝ -∗
      iref_slots ns' -∗
      proc_priv γf pj pid (upd_usM (us_upt U P') M') -∗
      (* the armed post on the returned a0 (implies [sys_mknod_ret]) *)
      ARMS (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE CONTRACT.  The abstract state is read at the LIVE Γ,
   [fs_gamma_L fsc_fs]; the device numbers are the syscall arguments' own
   low halfwords ([SpecSysMknodAU.dev_arg]), so the caller's receipts
   speak about the numbers IT passed. *)
Definition wp_sys_mknod_au_era_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (ns : nat)
    (dqb dqs dqbs dqn : dfrac)
    (v0 v1 v2 : mword 64)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  let ma := dev_arg v1 in
  let mi := dev_arg v2 in
  wp_sys_mknod_au_era_frame γf gs j gl pd pav pu ns dqb dqs dqbs dqn
    v0 v1 v2 pid U m K eb b lks
    (mknod_au_pre_era Γfs fsc_fs ma mi P Pmiss Φok Φex)
    (mknod_arms_era Γfs fsc_fs ma mi P Pmiss Φok Φex).

Module Type SYSMKNOD_AU_ERA.
  Parameter wp_sys_mknod_au_era :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v0 v1 v2 : mword 64)
      (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ),
      wp_sys_mknod_au_era_body γf gs j gl pd pav pu ns dqb dqs dqbs dqn
        v0 v1 v2 pid U m K eb b lks P Pmiss Φok Φex.
End SYSMKNOD_AU_ERA.

