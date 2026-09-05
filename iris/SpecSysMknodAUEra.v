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
   arm are the frozen file's.

   ==== (4) THE STABLE COROLLARY LIVES HERE, AND IT IS RE-CUT ===========

   [SYSMKNOD_AU_ERA_STABLE] is at the bottom of this file (statement and
   seal together, as the campaign's own files carry both), and it is NOT
   [SpecSysMknodAU.wp_sys_mknod_au_stable] at the era shape: that form's
   arms key on the fetched string, and no AU form of this shape can deliver
   that key.  The obstruction is written out in full in the note under the
   seal; the short version is that the cursor family takes [(k, d)] and is
   fixed before the fetched string exists, so nothing inside the syscall
   can report "the walk was the client's".  What the pins DO buy is
   agreement at the fire instants -- the client's chain still reads its own
   values there, hence its path still names its own parent inum THERE --
   and that is what the sealed form states.  It is derived, not owed:
   [ProofSysMknodAUEraStable.v] implements the functor
   [SYSMKNOD_AU_ERA -> SYSMKNOD_AU_ERA_STABLE]. *)
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
Require Import FsAbsMknodFire.   (* the authority-shaped commits         *)
Require Import SpecCreateAU.     (* [cau_ok] / [cau_fail]                *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import FsAbs.            (* LAST (FsAbs's own rule)              *)
Require Import PathElems.  (* [path_elems] -- previously via the trimmed SpecSysMknodAU *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

Section SysMknodAUEra.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* everything the AU caller hands in, at the commit mask [appE] *)
  Definition mknod_au_pre_era Γ (γfs : fs_names) (cw : Z) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (mknod_walk_pre_era γfs cw P Pmiss
     ∗ acre_commit_at Γ appE (ADev ma mi) Φok
     ∗ dlookup_commit_at Γ appE Φex)%I.

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
  Definition mknod_post_fail_era Γ (γfs : fs_names) (cw : Z) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (mknod_au_pre_era Γ γfs cw ma mi P Pmiss Φok Φex
     ∨ (∃ pl : list (bv 8),
          cau_fail Γ γfs ma mi P Pmiss Φok Φex pl))%I.

  (* the armed disjunction the continuation receives, keyed on a0.  NO
     ESCAPE on the [ret = 0] arm since lane A-iii: the walk takes the
     relative start, so a success is a RECEIPT whatever the fetched string
     looked like.  See the header. *)
  Definition mknod_arms_era Γ (γfs : fs_names) (cw : Z) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (r : mword 64) : iProp Σ :=
    ((⌜r = (zero_reg : mword 64)⌝
      ∗ mknod_post_ok_era Γ ma mi P Φok Φex)
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ mknod_post_fail_era Γ γfs cw ma mi P Pmiss Φok Φex))%I.

  (* the landed return blanket, read off the arms: this is the one
     conjunct of [SpecSysMknod.wp_sys_mknod_sconf_body]'s continuation the
     AU form replaces, and it is implied *)
  Lemma mknod_arms_era_ret Γ (γfs : fs_names) (cw : Z) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) (r : mword 64) :
    mknod_arms_era Γ γfs cw ma mi P Pmiss Φok Φex r ⊢ ⌜sys_mknod_ret r⌝.
  Proof.
    rewrite /mknod_arms_era /sys_mknod_ret.
    iIntros "[[%Hr _] | [%Hr _]]"; iPureIntro; [left | right]; exact Hr.
  Qed.

  (* =================================================================== *)
  (*  THE STABLE COROLLARY, AT THE ERA (and re-cut -- see the note at the *)
  (*  bottom of this file for why the frozen shape's arms cannot be       *)
  (*  derived from ANY AU form)                                           *)
  (* =================================================================== *)

  (* THE CLIENT'S CHAIN SHARE, PERSISTENT.  [FsAbs.apn_pin] at
     [DfracDiscarded] instead of [DfracOwn q], and the flavour is forced by
     the SHAPE of this contract rather than chosen: the bundle carries TWO
     commits, exactly one of which fires on any run, and the other comes
     back REFUNDED -- as a closure at whatever receipt it was built with.
     A fractional share handed into both is therefore stranded inside the
     refunded one on every arm (write's stable form dodges this by having a
     single commit; read's by refuting its refund arm with [0 <= n], and
     neither dodge exists here: argstr can fail).  A DISCARDED share is
     copied into both, returned to the client for free, and costs the
     client exactly what the corollary's name claims -- the chain
     directories' rows never move again.  The PARENT is not among them:
     [mkr_chain] pins [ds !!! j] for [j < |ps|] and the parent is
     [ds !!! |ps|], so the success retag is untouched (the frozen header's
     honesty note, satisfied by construction rather than by a side
     condition). *)
  Definition mkr_pin Γ (avc : aview) (d : Z) : iProp Σ :=
    (∃ a : anode, ⌜avc !! d = Some a⌝ ∗ nview_dq Γ DfracDiscarded d a)%I.

  Definition mkr_chain Γ (avc : aview) (ds : list Z)
      (ps : list fname) : iProp Σ :=
    ([∗ list] j ↦ _ ∈ ps, mkr_pin Γ avc (ds !!! j))%I.

  Global Instance mkr_pin_persistent Γ avc d : Persistent (mkr_pin Γ avc d).
  Proof. rewrite /mkr_pin /nview_dq /top_frag_q. apply _. Qed.

  Global Instance mkr_chain_persistent Γ avc ds ps :
    Persistent (mkr_chain Γ avc ds ps).
  Proof. rewrite /mkr_chain. apply _. Qed.

  (* THE ENRICHED RECEIPT, and it is the whole of what the pins buy: at the
     instant the receipt fires, the client's run is a run OF THE LIVE VIEW
     -- so [apath_at av root ps = Some (ds !!! |ps|)] holds THERE
     ([FsAbs.arun_apath_tot]), not merely in the client's remembered [avc].
     That is what makes the parent inum the arms expose comparable with the
     client's own [ds !!! |ps|]: on [d = ds !!! |ps|] -- a comparison the
     client makes itself, on data the arm hands it -- the create landed in
     the directory its path names, under a name absent from that directory
     at that instant ([cre_pre]'s second conjunct). *)
  Definition mkr_recv (root : Z) (ps : list fname) (ds : list Z)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      : aview -> Z -> fname -> Z -> iProp Σ :=
    fun av d nm i => (⌜arun av root ps ds⌝ ∗ Φ av d nm i)%I.

  (* ret 0: [mknod_post_ok_era] with the cursor gone (the stable form owes
     the walk nothing -- see the derivation) and the instant's run stated
     purely beside the client's own receipt.  The lookup commit comes back
     AT THE CLIENT'S OWN [Φex], not at the enriched one: the enrichment is
     a conjunct, so the refund weakens back. *)
  Definition mknod_stable_ok_era Γ (ma mi : Z) (root : Z)
      (ps : list fname) (ds : list Z)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (∃ (pl : list (bv 8)) (av : aview) (d i : Z) (nm : fname)
       (ents : gmap fname Z) (nl : nat),
       ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
       ⌜cre_pre av d nm ents nl i (ADev ma mi)⌝ ∗
       ⌜0 < i < 16 * Z.of_nat icfg_nib⌝ ∗
       ⌜arun av root ps ds⌝ ∗
       dlookup_commit_at Γ appE Φex ∗
       Φok av d nm i)%I.

  (* ret -1: TWO arms where the AU form has three folds, and the collapse
     is the cursor's disappearance -- "the walk died at hop k" and "nothing
     fs-visible happened" are the same statement once the residue is the
     bundle itself.  The surviving distinction is the one a client can act
     on: either NOTHING FIRED (both commits back, unspent), or the
     exists-observation fired at a name the parent already held. *)
  Definition mknod_stable_fail_era Γ (ma mi : Z) (root : Z)
      (ps : list fname) (ds : list Z)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    ((acre_commit_at Γ appE (ADev ma mi) Φok ∗ dlookup_commit_at Γ appE Φex)
     ∨ (∃ (pl : list (bv 8)) (av : aview) (d i : Z) (nm : fname)
          (ents : gmap fname Z) (nl : nat),
          ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
          ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
          ⌜ents !! nm = Some i⌝ ∗
          ⌜arun av root ps ds⌝ ∗
          acre_commit_at Γ appE (ADev ma mi) Φok ∗
          Φex av d nm i))%I.

  Definition mknod_stable_arms_era Γ (ma mi : Z) (root : Z)
      (ps : list fname) (ds : list Z)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (r : mword 64) : iProp Σ :=
    ((⌜r = (zero_reg : mword 64)⌝
      ∗ mknod_stable_ok_era Γ ma mi root ps ds Φok Φex)
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ mknod_stable_fail_era Γ ma mi root ps ds Φok Φex))%I.

End SysMknodAUEra.

(* the same seals the frozen file puts on its own pair, and for the same
   reason (big-op bodies behind Definitions at syscall altitude) *)
Global Typeclasses Opaque mknod_au_pre_era mknod_post_ok_era
  mknod_post_fail_era mknod_arms_era mkr_chain mknod_stable_ok_era
  mknod_stable_fail_era mknod_stable_arms_era.

(* ===================================================================== *)
(*  THE FRAME: [SpecSysMknod.wp_sys_mknod_sconf_body] at the CURRENT      *)
(*  head, abstracted over the caller's bundle and the armed post -- i.e.  *)
(*  the frozen [wp_sys_mknod_au_frame] with its [M'] binder restored.     *)
(*  See the header's finding (1).                                        *)
(* ===================================================================== *)

Definition wp_sys_mknod_au_era_frame
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
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
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
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
  (* THE IMAGE DOES NOT MOVE (the landed row, [SpecSysMknod]'s note):
     sys_mknod only READS user memory (argstr), so the binders are
     [(mf, ns', P')] and the block returns at [us_upt U P'] -- no [M']. *)
  ∀ (mf : regfile) (ns' : nat) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      (* the page table may have GROWN: argstr's fetchstr faults user pages
         in.  [uptd_ext_sz] is argstr's own report, relayed. *)
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
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
      proc_priv γf pj pid (us_upt U P') -∗
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
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
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
    (mknod_au_pre_era Γfs fsc_fs (pv_cwi (us_V U)) ma mi P Pmiss Φok Φex)
    (mknod_arms_era Γfs fsc_fs (pv_cwi (us_V U)) ma mi P Pmiss Φok Φex).

(* ===================================================================== *)
(*  THE STABLE COROLLARY'S BODY                                           *)
(* ===================================================================== *)

(* The client names a chain it holds persistently -- a root [root], the
   path elements [ps] of the directory it expects to create in, and the run
   [ds] of that chain through its own view [avc] -- and its own two
   receipts.  Every FIRED receipt then reports the run AT THE INSTANT.
   Nothing is claimed about the fetched string: see the note below, which
   is this lane's finding and the reason the frozen file's stable arms are
   not what this form derives.

   NOT A PARAMETER: the path itself.  [ps]/[ds] are the client's CHAIN, and
   [root] is deliberately free -- an absolute expectation instantiates it
   at [FsImg.ROOTINO], a relative one at the cwd's inum, and neither is
   tied to the fetched string by anything (that is the point of the note).
   Note also that [ps = []] -- init's own [mknod("console", 1, 1)] -- is a
   legal instance: the chain is empty, [arun av root [] [root]] holds for
   free, and the corollary degenerates to the AU form with the cursor
   erased.  It is a DEEP path that pays for the pins. *)
Definition wp_sys_mknod_au_era_stable_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (ns : nat)
    (dqb dqs dqbs dqn : dfrac)
    (v0 v1 v2 : mword 64)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (root : Z) (avc : aview) (ds : list Z) (ps : list fname)
    (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  let ma := dev_arg v1 in
  let mi := dev_arg v2 in
  arun avc root ps ds ->
  wp_sys_mknod_au_era_frame γf gs j gl pd pav pu ns dqb dqs dqbs dqn
    v0 v1 v2 pid U m K eb b lks
    (mkr_chain Γfs avc ds ps
     ∗ acre_commit_at Γfs appE (ADev ma mi) Φok
     ∗ dlookup_commit_at Γfs appE Φex)%I
    (mknod_stable_arms_era Γfs ma mi root ps ds Φok Φex).

Module Type SYSMKNOD_AU_ERA.
  Parameter wp_sys_mknod_au_era :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
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

(* owed as a DERIVATION from [wp_sys_mknod_au_era] + the agreement seeds
   ([FsAbsMknodFire]'s [_at_pinned] pair, at the chain rather than at one
   row), never as a second walk -- and DISCHARGED, in
   [ProofSysMknodAUEraStable.v]. *)
Module Type SYSMKNOD_AU_ERA_STABLE.
  Parameter wp_sys_mknod_au_era_stable :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v0 v1 v2 : mword 64)
      (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (root : Z) (avc : aview) (ds : list Z) (ps : list fname)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ),
      wp_sys_mknod_au_era_stable_body γf gs j gl pd pav pu ns dqb dqs dqbs
        dqn v0 v1 v2 pid U m K eb b lks root avc ds ps Φok Φex.
End SYSMKNOD_AU_ERA_STABLE.

(* ===================================================================== *)
(*  THE NOTE: WHY THE FROZEN STABLE ARMS ARE NOT WHAT THIS DERIVES        *)
(* ===================================================================== *)

(* [SpecSysMknodAU.mknod_stable_arms] keys its receipts on the FETCHED
   STRING -- "either [path_elems pl = path_elems pl0] and the receipt is at
   [dpar], or it did not match and the receipt is unlocated".  That key is
   NOT DERIVABLE FROM ANY AU FORM OF THIS SHAPE, and the obstruction is
   structural rather than a gap in a proof:

   - The walk's cursor family is the ONLY channel from the syscall's
     interior back to the client, and its members take [(k, d)] -- an index
     and an inum.  The cursor predicate is fixed when the contract is
     instantiated, which is BEFORE the fetched string exists
     ([mknod_walk_pre_era] is a one-shot universally quantified over [pl]),
     so no cursor can mention [pl].
   - Therefore the located branch of any match key must be an alternative
     whose OTHER branch is entered when a hop's name misses the client's
     chain -- and what a hop knows at that moment ("this name is not
     [ps !!! k]") is a fact about the fetched string, which the cursor
     cannot record.  Recording it as [emp] makes the disjunction
     [⌜located⌝ ∨ True], which carries nothing.
   - A ghost carried through the cursor does not break the wall either: the
     value it would have to carry is the fetched path, the hops that must
     compare against it are proved BEFORE the one-shot fires (they are
     [⊢]-facts of the cursor), and the arm's own [pl] is bound by a
     DIFFERENT existential from the cursor's -- nothing ties the two.

   So the honest content of a stable mknod is not "the walk was mine" but
   "MY TREE HELD AT THE INSTANT", which is what the form above states and
   what the two [_at_pinned] seeds were landed to buy.  The client is left
   holding the comparison the contract cannot make for it: the parent inum
   is exposed on the arm, [ds !!! |ps|] is the client's own, and equality
   of the two is decidable where it matters.  A contract that could key on
   the path needs a USER-MEMORY tie ([SpecFetchstr]: "they came from user
   memory"), i.e. a different premise at a lower altitude, not a stronger
   corollary here. *)

