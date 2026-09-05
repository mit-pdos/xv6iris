(* SpecSysChdirAU.v -- sys_chdir's AU contract: the landed
   [SpecSysChdir.wp_sys_chdir_sconf_body] with the walk at the era premise
   and the landed inode OBSERVED, so the success arm names the new cwd's
   inum as the walk's cursor (lane C3).

   ==== WHAT THIS CONTRACT ADDS ==========================================

   The landed post's success arm is [∃ ipv z, proc_priv .. (us_cwi (us_cwd
   U ipv) z)]: [z] is the real inum of the installed inode, but nothing
   above the icache could say WHICH inode that was.  This form is
   [SpecSysUnlinkAU]'s walk-only mold ([open_walk_pre_era] handed down
   unfired, the era refund on the dead arm) plus [SpecSysOpenAU]'s plain
   observation receipt ([aopen_commit_at], fired under the node's lock
   exactly where the landed proof tests [T_DIR]):

   * walk dead: a0 = -1, the block back unchanged, the death receipt beside
     the unfired commit ([open_walk_dead_era]'s shape, verbatim);
   * resolved and observed, NOT a directory: a0 = -1, the block back
     unchanged, the cursor [P L i] and the receipt [Φo av i a] at a node
     that is not [ADir];
   * resolved, a directory: a0 = 0, the cursor and the receipt at
     [MkAnode (ADir e) nl], and the block at [us_cwi (us_cwd U ipv) i] --
     the new [pv_cwi] IS the walk's cursor.

   THE START (lane C3): the walk premise is [open_walk_pre_era] at
   [pv_cwi (us_V U)], the calling process's cwd inum at entry, so a
   relative chdir's walk starts where the block says it does.

   [chdir_arms_landed] is the sanity tie: the arms imply the landed post,
   which is how the dispatcher keeps its chdir tail verbatim. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
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
Require Import SpecPanic.
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
Require Import SpecDirlink.    (* [ic_sleeplocks], [ireg_blocks_ok] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Require Import SpecSysChdir.    (* K_sys_chdir, [sys_chdir_post]: the landed
                                   contract this file states a parallel
                                   form beside *)
Require Import PathElems.       (* [path_elems] *)
Require Import FsTree.          (* [fname] *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the live Γ *)
Require Import FsAbsInv.        (* [fsabsE]: the commit mask *)
Require Import SpecSysOpenAU.   (* [open_walk_pre_era], [open_walk_dead_era],
                                   [aopen_commit_at] *)
Require Import FsAbsDefs.           (* LAST (FsAbs's own rule) *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE AU BUNDLE AND THE ARMS                                        *)
(* ===================================================================== *)

Section SysChdirAU.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* everything the AU caller hands in, at the commit mask [fsabsE]:
     open's walk premise at the process's cwd inum, and open's plain
     observation commit *)
  Definition chdir_au_pre Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ) : iProp Σ :=
    (open_walk_pre_era γfs cw P Pmiss
     ∗ aopen_commit_at Γ fsabsE Φo)%I.

  (* ret -1: the three-way fold -- (i) nothing fs-visible happened (argstr
     failed: the bundle back whole), (ii) the walk died (the era refund
     beside the unfired commit), (iii) the walk landed and the node was
     observed to be something other than a directory *)
  Definition chdir_post_fail Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ) : iProp Σ :=
    (chdir_au_pre Γ γfs cw P Pmiss Φo
     ∨ (∃ pl : list (bv 8),
          (open_walk_dead_era γfs P Pmiss pl
             ∗ aopen_commit_at Γ fsabsE Φo)
          ∨ (∃ (i : Z) (av : aview) (a : anode),
               P (length (path_elems pl)) i
               ∗ ⌜av !! i = Some a⌝ ∗ Φo av i a
               ∗ ⌜forall (e : gmap fname Z) (nl : nat),
                    a <> MkAnode (ADir e) nl⌝)))%I.

  (* ret 0: the walk landed on a DIRECTORY, observed as such, and the
     block's cwd moved to it -- pointer and inum both, the inum being the
     walk's own cursor [i] *)
  Definition chdir_post_ok Γ (γf : gname) (pj : mword 64) (pid : mword 32)
      (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (U : ustate) : iProp Σ :=
    (∃ (ipv : mword 64) (pl : list (bv 8)) (i : Z)
       (e : gmap fname Z) (nl : nat) (av : aview),
       P (length (path_elems pl)) i
       ∗ ⌜av !! i = Some (MkAnode (ADir e) nl)⌝
       ∗ Φo av i (MkAnode (ADir e) nl)
       ∗ proc_priv γf pj pid (us_cwi (us_cwd U ipv) i))%I.

  (* the armed disjunction the continuation receives, keyed on a0, at the
     block the syscall returns ([us_upt U P'], as the landed post) *)
  Definition chdir_arms Γ (γfs : fs_names) (γf : gname)
      (pj : mword 64) (pid : mword 32) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (U : ustate) (r : mword 64) : iProp Σ :=
    ((⌜r = (mword_of_int (-1) : mword 64)⌝
      ∗ proc_priv γf pj pid U
      ∗ chdir_post_fail Γ γfs cw P Pmiss Φo)
     ∨ (⌜r = (zero_reg : mword 64)⌝
        ∗ chdir_post_ok Γ γf pj pid P Φo U))%I.

  (* SANITY: the arms imply the landed [SpecSysChdir.sys_chdir_post] *)
  Lemma chdir_arms_landed Γ (γfs : fs_names) (γf : gname)
      (pj : mword 64) (pid : mword 32) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (U : ustate) (r : mword 64) :
    chdir_arms Γ γfs γf pj pid cw P Pmiss Φo U r ⊢
      sys_chdir_post γf pj pid U r.
  Proof.
    rewrite /chdir_arms /chdir_post_ok /sys_chdir_post.
    iIntros "[(%Hr & Hpriv & _) | (%Hr & H)]".
    - iLeft. iFrame "Hpriv". by iPureIntro.
    - iRight. iDestruct "H" as (ipv pl i e nl av) "(_ & _ & _ & Hpriv)".
      iExists ipv, i. iFrame "Hpriv". by iPureIntro.
  Qed.

End SysChdirAU.

(* big-op bodies behind definitions: sealed, per the family convention *)
Global Typeclasses Opaque chdir_au_pre chdir_post_fail chdir_post_ok
  chdir_arms.

(* ===================================================================== *)
(*  2.  THE MACHINE CONTRACT: SpecSysChdir's frame + the AU               *)
(* ===================================================================== *)

(* THE SHARED FRAME: [SpecSysChdir.wp_sys_chdir_sconf_body]'s premises and
   threaded resources VERBATIM, abstracted over the AU-side extras: the
   caller's bundle [EXTRA] and the armed post [ARMS] on the block and the
   returned a0, which REPLACES the landed [sys_chdir_post].  Every other
   row is byte-identical, INCLUDING the binder list [(mf, P')]: the image
   does not move (the landed header). *)
Definition wp_sys_chdir_au_frame
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)                          (* ftable, kalloc      *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (pd pav pu : mword 64)                              (* disk fabric + lock  *)
    (dqb dqs : dfrac)
    (v : mword 64)                                      (* syscall argument 0  *)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (EXTRA : iProp Σ) (ARMS : ustate -> mword 64 -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_chdir in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_chdir <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  (* ---- the block-layer geometry, threaded verbatim to namei / iput ---- *)
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* namei's own premise, inherited: the walker runs with the base enabled *)
  eb = true ->
  (* argstr reads syscall argument 0 out of the trapframe page *)
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v ->
  sie_cap_gpr KT1 m K b pj -∗
  (* entered with no lock held: depth pinned at zero (the landed row) *)
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  (* ---- the block layer ---- *)
  bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
  log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
  fs_crash_seam fsc_cov fsc_logst -∗
  gen_cert -∗
  dev_inv fsc_uart fsc_disk -∗
  disk_geom fsc_disk pd pav pu -∗
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
  bslots 3 -∗
  (* ---- the inode cache, and the region iput's truncate arm frees into ---- *)
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  (* the sealed regime, riding [ireg_inv]'s channel (the landed row) *)
  ireg_open -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  (* argstr's page-table side, and namei's (iget's ipool arm allocates) *)
  kalloc_env fsc_kalloc None -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* ---- the process, and the reference allowance its walk needs ---- *)
  iref_slots 2 -∗
  proc_priv γf pj pid U -∗
  (* ---- THE AU SIDE (the one addition to the landed premise list) ---- *)
  EXTRA -∗
  (* the crossing is the literal [true]: sys_chdir parks in five callees
     (the landed contract's row) *)
  wp_next true pj (fun (CID : CpuId) =>
  (* THE IMAGE DOES NOT MOVE (the landed header): only the descriptor
     grows, so the binders are [(mf, P')] and the block returns at
     [us_upt U P'] -- no [M']. *)
  ∀ (mf : regfile) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      bslots 3 -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      (* the allowance, whole: the landed header's ledger *)
      iref_slots 2 -∗
      (* the armed post on the final process state and the returned a0
         (implies the landed [sys_chdir_post]) *)
      ARMS (us_upt U P') (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE CONTRACT.  The abstract state is read at the LIVE Γ,
   [fs_gamma_L fsc_fs]; the walk starts at the block's own cwd inum. *)
Definition wp_sys_chdir_au_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (dqb dqs : dfrac)
    (v : mword 64)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Φo : aview -> Z -> anode -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  wp_sys_chdir_au_frame γf gs j gl pd pav pu dqb dqs
    v pid U m K eb b lks
    (chdir_au_pre Γfs fsc_fs (pv_cwi (us_V U)) P Pmiss Φo)
    (chdir_arms Γfs fsc_fs γf (proc_addr j) pid (pv_cwi (us_V U)) P Pmiss Φo).

(* ===================================================================== *)
(*  3.  THE SEAL                                                          *)
(* ===================================================================== *)

Module Type SYSCHDIR_AU.
  Parameter wp_sys_chdir_au :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs : dfrac)
      (v : mword 64)
      (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ),
      wp_sys_chdir_au_body γf gs j gl pd pav pu dqb dqs
        v pid U m K eb b lks P Pmiss Φo.
End SYSCHDIR_AU.
