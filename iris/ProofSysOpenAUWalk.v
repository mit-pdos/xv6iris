(* ProofSysOpenAUWalk.v -- THE else ARM (+0xdc .. +0xfa) AND ARMS B-FAIL /
   C-FAIL, at the ARMED post: [ProofSysOpen.so_entry_n] with the ERA namei
   walk in place of the landed one and THE TERMINAL OBSERVATION FIRED.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the open AU
   prover).  A PARALLEL block beside the landed one; this is the only block
   of the walk that consumes an AU premise rather than relaying one.

   ==== THE WALK (item 1) ===============================================

   [SpecNameiEra.wp_namei_era] in place of [SpecNamei.wp_namei_gen]: the
   SAME premise list with ONE row added -- [FsAbsStart.ex_start], the trace
   deferred in the start inum -- and the same post with the cursor
   [P L iL] on the success arm and the death receipt on the failure one.
   The contract's one-shot is specialised to the string argstr fetched by
   [FsAbsOpenFire.opf_start_of_open]; the walk itself decides whether it
   starts at ROOTINO or at [p->cwd], which is what makes this theorem say
   something about init's RELATIVE "console".

   The death receipt IS [SpecSysOpenAU.open_walk_dead_era] on the nose
   ([ex_hops_from] is [ax_hops_from (elend ...) (path_elems pl)] by
   [reflexivity]), so ARM B-FAIL's fold needs no bridge.

   ==== THE FIRE (item 2) ===============================================

   [FsAbsOpenFire.opf_open_fire_1], the instant ilock returns: the payload
   is peeled ([ProofSysOpenAUParts.so_flat]) and the commit reads the row
   off its own [top_frag] and hands it straight back.  From there down the
   receipt is inert -- every post-walk failure delivers it (ARM C-FAIL
   here, D/E/F below the join) and the success arms key on it.

   THE PEEL IS NOT RE-SEALED before the join: it travels as [so_flat] so
   that the O_TRUNC receipt, fired far below at the retag, reads the SAME
   [data] this observation did.  That is the observed-row tie. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import ByteBuf.
Require Import RegFile WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioInv.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED BEFORE
   [FsBlocks] on purpose -- the [FsState*] stack exports [fs_view] and
   [byte_range], both of which have live twins below, and the LAST import
   wins (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
Require Import FsStateEra.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import DirView.
Require Import FileInvDefs.
Require Import FileInv.
Require Import ProcInv.
Require Import SpecArgint.
Require Import SpecEndOp.
Require Import SpecIput.
Require Import SpecIlock.
Require Import SpecIunlock.
Require Import SpecIunlockput.
Require Import SpecFileclose.
Require Import SpecFilealloc.
Require Import SpecFdalloc.
Require Import SpecItrunc.
Require Import SpecPrintk.
Require Import SpecDirlink.
Require Import SpecCreate.
Require Import CodeSysOpen.
Require Import SpecSysOpen.
Require Import SysOpenBudget.
Require Import ProofSysOpenParts.
Require Import ProofSysOpenTails.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.

Require Import DirentEnc.   (* [bview]: the fetched string as a list *)
Require Import FsBytesGamma.
Require Import SpecNameiEra.
Require Import SpecSysOpenAU.
Require Import FsAbsOpenFire.
Require Import ProofSysOpenAUParts.
Require Import ProofSysOpenAUAlloc.
Require Import ProofSysOpenAUJoin.
Require Import ProofSysOpen.   (* [so_neq_of_eq] / [so_neq_of_ne] / [so_bud_iput] *)
Require Import FsAbsInv.        (* [fsabsE]: the commit mask *)
Require Import FsAbs.
Require Import TsoCtx.

Local Open Scope Z_scope.

Set Printing Depth 40.

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.

Module SysOpenAUWalk (Iunlock : IUNLOCK) (Iunlockput : IUNLOCKPUT)
                     (EndOp : END_OP) (Fileclose : FILECLOSE)
                     (Itrunc : ITRUNC) (Filealloc : FILEALLOC)
                     (Fdalloc : FDALLOC) (NameiEra : NAMEI_ERA)
                     (Ilock : ILOCK).

Module Join := SysOpenAUJoin Iunlock Iunlockput EndOp Fileclose Itrunc
                             Filealloc Fdalloc.
Module Alloc := SysOpenAUAlloc Iunlock Iunlockput EndOp Fileclose Itrunc
                               Filealloc Fdalloc.
Module Tails := SysOpenTails Iunlock Iunlockput EndOp Fileclose.

Section ProofSysOpenAUWalk.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rz  := (mword_of_int 0 : mword 5).

  (* ================================================================== *)
  (*  THE else ARM: +0xdc .. +0xfa, AND ARMS B-FAIL AND C-FAIL.          *)
  (*                                                                    *)
  (*    addi a0,s0,-176 ; jal namei ; c.mv s1,a0 ; c.beqz a0 -> +0x10c   *)
  (*    jal ilock ; lh a4,68(s1) ; c.li a5,1 ; bne -> +0x4a              *)
  (*    lw a5,-180(s0) ; c.beqz a5 -> +0x5e                              *)
  (*                                                                    *)
  (*  TWO BLOCK EXITS, NOT ONE.  The [bne] at +0xf2 leaves for the JOIN   *)
  (*  at +0x4a (the inode is not a directory); the [c.beqz] at +0xfa      *)
  (*  leaves for +0x5e -- [so_alloc], SKIPPING the T_DEVICE test, because *)
  (*  gcc knows a T_DIR inode cannot be a T_DEVICE.  Both are ordinary    *)
  (*  lemma applications, so the linear-exit problem of a chained pair    *)
  (*  never arises.                                                      *)
  (*                                                                    *)
  (*  BLOCKER 2's ANSWER IS FOUR LINES, and it is this arm's whole ghost  *)
  (*  content.  namei hands back [inode_held], which is generation-FREE;  *)
  (*  [so_publish] twenty instructions later needs the parent and the     *)
  (*  share ilock consumed at ONE named generation.  So: shed the         *)
  (*  reference ([inode_ref_shed]), NAME the share's generation           *)
  (*  ([inode_shr_gen_intro]) and the retained parent's                   *)
  (*  ([inode_ref_short_gen_intro]), and PIN the two together             *)
  (*  ([inode_ref_short_shr_gen_agree], which is [live_gen_agree] at the  *)
  (*  pointer-free altitude).  ilock then reports [ity_shot] and its      *)
  (*  deposit at that same [g].  The O_CREATE arm needs none of this --   *)
  (*  [create_locked] hands the parent back generation-NAMED already.     *)
  (*                                                                    *)
  (*  AND THE T_DIR WITNESS IS *EARNED* HERE.  On the [bne]-taken route   *)
  (*  the type is not T_DIR and [so_tdir_zne] makes the join's premise    *)
  (*  vacuous; on the fall-through the [c.beqz] at +0xfa forces           *)
  (*  [omode = O_RDONLY = 0] ([so_omode_eqz]), which is exactly           *)
  (*  [so_dir_forced]'s hypothesis -- and through [so_pay_witness] that   *)
  (*  is what says a WRITABLE fd never names a directory.                 *)
  (* ================================================================== *)
  Lemma so_entry_n_au `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gfl gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (plen : nat) (bp : nat -> bv 8)
      (om lo : mword 32) (ns : nat) (Sb : gset Z)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (U : ustate) (sts : list fdstate)
      (m N : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w4 w5 w6 w24 : mword 64)
      (* ---- the AU side ---- *)
      (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ) :
    (K_sys_open <= K)%nat -> icfg_dev = ROOTDEV -> (0 < icfg_nib)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < fsc_size <= BPB ->
    0 <= fsc_bmapstart ->
    fsc_bmapstart ∈ fsc_cov ->
    ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
    0 <= icfg_ist ->
    cov_below fsc_cov fsc_size ->
    bitmap_geom_ok fsc_cov fsc_logst fsc_bmapstart fsc_size ->
    ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
    bb_cstr bp plen ->
    (plen < 128)%nat ->
    1 < fsc_ninodes -> fsc_ninodes <= 16 * Z.of_nat icfg_nib -> fsc_ninodes < 2 ^ 31 ->
    16 * Z.of_nat icfg_nib <= 2 ^ 16 ->
    printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk ->
    (sys_open_slots <= ns)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    eb = true ->
    lks = ∅ ->
    (* ---- the AU side: the omode word is the caller's argument ---- *)
    om = arg_int32 vom ->
    is_aligned_paddr (Physaddr (pa_stk sp0 23)) 8 = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 N -> so_thr m N ->
    (N !!! Regidx Rs0 : mword 64) = sp0 ->
    (N !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (N !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    so_al sp0 ->
    sie_cap_gpr KT1 N (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0xdc)) -∗
    printk_env fsc_printk fsc_uart fsc_disk -∗
    is_ftable gfl gf -∗
    bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
    log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
    fs_crash_seam fsc_cov fsc_logst -∗
    gen_cert -∗
    kalloc_env fsc_kalloc None -∗
    is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
    itable_inv -∗
    ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
    ic_sleeplocks fsc_ic -∗
    ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
    ireg_open -∗
    sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
    bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
    proc_priv gf (proc_addr jx) pidv U -∗
    procs_inv gs -∗
    dev_inv fsc_uart fsc_disk -∗
    disk_geom fsc_disk pd pav pu -∗
    is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
    log_opS icfg_log MAXOPBLOCKS Sb -∗
    (* the transaction token, beside the budget: this arm's tail closes the
       operation, and end_op takes the whole [log_op] (durable-disk lane A) *)
    log_tx icfg_log -∗
    bslots 3 -∗
    iref_slots ns -∗
    fd_slot -∗
    (* the descriptor-state fragments, threaded exactly as the fd unit above
       is: sys_open spends one access, at the settle. *)
    fd_frags (pv_fdg (us_V U)) sts -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    (pa_stk sp0 5) ↦₈[KT1] w5 -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₄[KT1] lo -∗
    (pa_add (pa_stk sp0 23) 4) ↦₄[KT1] om -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    (* ---- THE AU BUNDLE.  The walk premise is the contract's own one-shot
       ([SpecSysOpenAU.open_walk_pre_era]), handed DOWN unfired: the walk
       picks the start inum -- ROOTINO on an absolute path, [p->cwd]'s on a
       relative one -- and fires it there. ---- *)
    open_walk_pre_era fsc_fs P Pmiss -∗
    aopen_commit_at (fs_gamma_L fsc_fs) fsabsE Φo -∗
    atrunc_commit_at (fs_gamma_L fsc_fs) fsabsE Φt -∗
    wp_next true (proc_addr jx)
      (so_cont0_au gf ns
                dqb dqs dqbs dqn (proc_addr jx) pidv vom U sts
                P Pmiss Φo Φt m K eb b lks) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK HdevR Hnib0 Hgeom Hsize Hbm0 Hbmcov
           Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hpcstr Hplen Hni1 Hni2 Hni3 Hush
           Hprkc Hnsb Hj Hgl Heb Hlkempty Hom Hal23 Hsp0 HNsp HNthr HNs0 HNs2
           HNs3 Hal.
    pose proof HK as HKfull.
    destruct (so_kb K HK) as (HKcr & HKna & HKai & HKas & HKbo & HKeo & HKil &
                              HKiu & HKit & HKip & HKup & HKfc & HKfa & HKfd &
                              HK10 & HK24 & Kpop).
    assert (Hns3 : (3 <= ns)%nat)
      by (revert Hnsb; unfold sys_open_slots, create_slots; lia).
    iIntros "Hcg Hown Htce Hcce #Htext #Hdata Hpc #Hpre #Hftab #Hbio
              #Hlog Hseam Hgen #Hkenv #Hitab #Hitinv #Hescrows #Hslks
              #Hireg #Hropen
              Hsbn Hsbi Hsbs Hsbb #Hbmres Hpriv #Hprocs #Hdev #Hgeo #Hdlk HopS Htx
              Hbsl Hisl Hfds Hfrag Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23lo H23hi H24
              Hwp Hoc Htc Hcont".
    iPoseProof (printk_env_panic with "Hpre") as "#Hpe".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0xdc addi a0,s0,-176 -- the path buffer ===== *)
    iApply (wp_addi4_s_sconf (CID := CID0) (mword_of_int (SO + 0xdc)) Ra0 Rs0
              (mword_of_int 3920 : mword 12) N (K - 24)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_0dc with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (N1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (N !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3920 : mword 12)))]> N).
    assert (HN1a0 : (N1 !!! Regidx Ra0 : mword 64) = pa_stk sp0 22).
    { etransitivity; [ rewrite /N1; apply upd_eq |].
      rewrite HNs0. apply so_bufpath. }
    assert (HN1sp : so_sp sp0 N1)
      by (rewrite /so_sp /N1 upd_ne; [exact HNsp | nz]).
    assert (HN1s0 : (N1 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /N1 upd_ne; [exact HNs0 | nz]).
    assert (HN1s2 : (N1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /N1 upd_ne; [exact HNs2 | nz]).
    assert (HN1s3 : (N1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /N1 upd_ne; [exact HNs3 | nz]).
    assert (HN1thr : so_thr m N1).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /N1 upd_ne; [| regne].
      exact (HNthr c Hc N2b N8 N9 N18 N19). }
    assert (Hppdc : add_vec_int (mword_of_int (SO + 0xdc) : mword 64) 4
                    = mword_of_int (SO + 0xe0)) by pcw.
    iEval (rewrite Hppdc) in "Hpc".
    (* ===== +0xe0 jal ra,namei ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SO + 0xe0)) Rra
              (mword_of_int 2091160 : mword 21) N1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_0e0 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (N2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0xe0) : mword 64) 4)]> N1).
    assert (Hjna : add_vec (mword_of_int (SO + 0xe0) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091160 : mword 21))
                   = mword_of_int KernelSyms.namei) by pcw.
    iEval (rewrite Hjna) in "Hpc".
    assert (HN2ra : (N2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0xe0) : mword 64) 4)
      by (rewrite /N2; apply upd_eq).
    assert (HN2a0 : (N2 !!! Regidx Ra0 : mword 64) = pa_stk sp0 22)
      by (rewrite /N2 upd_ne; [exact HN1a0 | nz]).
    assert (HN2sp : so_sp sp0 N2)
      by (rewrite /so_sp /N2 upd_ne; [exact HN1sp | nz]).
    assert (HN2s0 : (N2 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /N2 upd_ne; [exact HN1s0 | nz]).
    assert (HN2s2 : (N2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /N2 upd_ne; [exact HN1s2 | nz]).
    assert (HN2s3 : (N2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /N2 upd_ne; [exact HN1s3 | nz]).
    assert (HN2thr : so_thr m N2).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /N2 upd_ne; [| regne].
      exact (HN1thr c Hc N2b N8 N9 N18 N19). }
    (* ---- the process, carved for namei: the BLOCK and the cwd REFERENCE,
       and the two-slot allowance the walk takes EXACTLY.  [p->cwd] is one of
       the block's own cells now, so namei borrows it for its own load and
       nothing here carries it. ---- *)
    (* three-way now: [FirstTok.first_tok] parks beside the reference. *)
    iDestruct (proc_priv_split_cwd gf (proc_addr jx) pidv U with "Hpriv")
      as "[Hpnc [Href Hftok]]".
    iEval (rewrite proc_priv_nocwd_bare) in "Hpnc".
    iDestruct "Hpnc" as "[Hpbare Hofiles]".
    iDestruct (cwd_ref_held with "Href") as "Hcwdref".
    iDestruct (iref_slots_split 2 (ns - 2) with "[Hisl]") as "[Hir2 Hirr]".
    { replace (2 + (ns - 2))%nat with ns by lia. iExact "Hisl". }
    iDestruct (so_buf_split (pa_stk sp0 22) bp plen Hplen with "HbP")
      as "[Hbufk Hbufrest]".
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    (* THE ONE-SHOT, HANDED DOWN UNFIRED ([FsAbsOpenFire.opf_start_of_open]):
       [ex_start] at the string argstr fetched IS the contract's premise at
       that string, so nothing is fired here -- the WALK picks the start
       inum and fires it there. *)
    iDestruct (opf_start_of_open fsc_fs P Pmiss (bview plen bp) with "Hwp")
      as "Htrace".
    iApply (NameiEra.wp_namei_era (CID := CID2) gs jx gl pd pav pu
 gf
 plen bp MAXOPBLOCKS Sb P Pmiss
              pidv (DfracOwn (1/4)) dqb dqs (DfracOwn 1)
              N2 (K - 24)%nat eb b lks U
              HKna HdevR Hnib0 Hgeom Hsize Hbm0 Hbmcov
              Hbmlog Hist0 Hcovb Hiregb Hpcstr
              ltac:(exact (proj2 (so_len_range plen Hplen)))
              ltac:(apply so_namei_need) Hj Hgl
              with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hkenv Hitab Hitinv
                    Hescrows Hslks Hireg Hropen Hprocs Hdev Hgeo Hdlk Hsbb Hsbi
                    Hbmres Hpbare Hcwdref [Hbufk] Hbsl Hir2 [$HopS $Htx]
                    Htrace").
    (* namei is eb-generic now; sys_open is still at [eb = true]. *)
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iEval (rewrite HN2a0). iExact "Hbufk". }
    iIntros (CID3 Hq3 mna n1 Sb1 ok ipv w1)
      "%Hcsna Hcg Hown _ _ Hpc Hsbb Hsbi Hpbare Hcwdref
       Hbufk Hbsl %HSb1 %Hw1 %Hn1 [HopS Htx] Hres".
    iEval (rewrite HN2a0) in "Hbufk".
    assert (Hpcna : ret_pc (N2 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0xe4)) by (rewrite HN2ra; pcw).
    iEval (rewrite Hpcna) in "Hpc".
    (* the buffer, joined and renamed: nothing below reads it *)
    iDestruct (so_buf_join (pa_stk sp0 22) bp plen Hplen with "Hbufk Hbufrest")
      as "HbA".
    iDestruct (so_bytes_name (pa_stk sp0 22) 128 with "HbA") as (bp1) "HbP".
    assert (Hnasp : so_sp sp0 mna).
    { rewrite /so_sp (callee_saved_lookup Hcsna csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HN2sp. }
    assert (Hnas0 : (mna !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsna Rs0 ltac:(vm_compute; reflexivity)).
      exact HN2s0. }
    assert (Hnas2 : (mna !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsna Rs2 ltac:(vm_compute; reflexivity)).
      exact HN2s2. }
    assert (Hnas3 : (mna !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsna Rs3 ltac:(vm_compute; reflexivity)).
      exact HN2s3. }
    assert (Hnathr : so_thr m mna).
    { intros c Hc N2b N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsna c Hc).
      exact (HN2thr c Hc N2b N8 N9 N18 N19). }
    (* ===== +0xe4 c.mv s1,a0 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID3) (mword_of_int (SO + 0xe4)) Rs1 Ra0
              mna (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_0e4 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (P1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec zero_reg (mna !!! Regidx Ra0))]> mna).
    assert (HP1s1 : (P1 !!! Regidx Rs1 : mword 64) = (mna !!! Regidx Ra0 : mword 64)).
    { etransitivity; [ rewrite /P1; apply upd_eq |]. apply add_vec_zero_l. }
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mna !!! Regidx Ra0 : mword 64))
      by (rewrite /P1 upd_ne; [reflexivity | nz]).
    assert (HP1sp : so_sp sp0 P1)
      by (rewrite /so_sp /P1 upd_ne; [exact Hnasp | nz]).
    assert (HP1s0 : (P1 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /P1 upd_ne; [exact Hnas0 | nz]).
    assert (HP1s2 : (P1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P1 upd_ne; [exact Hnas2 | nz]).
    assert (HP1s3 : (P1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P1 upd_ne; [exact Hnas3 | nz]).
    assert (HP1thr : so_thr m P1).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (Hnathr c Hc N2b N8 N9 N18 N19). }
    assert (Hppe4 : add_vec_int (mword_of_int (SO + 0xe4) : mword 64) 2
                    = mword_of_int (SO + 0xe6)) by pcw.
    iEval (rewrite Hppe4) in "Hpc".
    (* ===== +0xe6 c.beqz a0, +0x10c  [ARM B-FAIL] ===== *)
    destruct ok.
    2:{ (* ---- namei refused: nothing is locked, the two slots come back,
             and the walk's DEATH RECEIPT comes with them ---- *)
      iDestruct "Hres" as "(%Hnaz & Hir2b & Hdead)".
      iApply (wp_cbeqz_taken_s_sconf (CID := CID4) (mword_of_int (SO + 0xe6))
                (mword_of_int 19 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                P1 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HP1a0 Hnaz; exact so_eqz_zero)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_0e6 with "Htext"). }
      iIntros (CID5 Hq5). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htge6 : add_vec (mword_of_int (SO + 0xe6) : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13 (concat_vec (mword_of_int 19 : mword 8) ('b"0"))))
                      = mword_of_int (SO + 0x10c)) by pcw.
      iEval (rewrite Htge6) in "Hpc".
      (* the process, put back whole and then re-carved for the tail's pid *)
      iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
      iCombine "Hpbare Hofiles" as "Hpnc".
    iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
      iDestruct (proc_priv_split_cwd gf (proc_addr jx) pidv U
                   with "[Hpnc Href Hftok]") as "Hpriv";
        [iSplitL "Hpnc"; [iExact "Hpnc" | iFrame "Href Hftok"] |].
      iDestruct (proc_priv_bare_acc with "Hpriv") as "[Hpbare Hpback2]".
      iDestruct (iref_slots_combine 2 (ns - 2) with "Hir2b Hirr") as "Hisl".
      assert (Hnsb2 : (2 + (ns - 2))%nat = ns) by lia.
      iEval (rewrite Hnsb2) in "Hisl".
      iDestruct (so_omode_join sp0 lo om Hal23 with "H23lo H23hi") as "H23".
      iDestruct (log_opS_op with "HopS Htx") as "Hop".
      iDestruct (cpu_own_transport CID3 CID5 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Tails.so_tail_b (CID0 := CID5) gs jx gl pd pav pu
 n1 pidv (DfracOwn (1/4)) m P1 sp0 K eb b
                lks w4 w5 w6 (word_of_words lo om) w24 bp1 U
                HKeo HK24 Kpop Hgeom Hj Hgl Hlkempty Hsp0 HP1sp HP1thr HP1s2
                HP1s3 Hal
                with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                      Hpbare Hprocs Hdev Hgeo Hdlk Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
                      HbP H23 H24 [Hpback2 Hfds Hisl Hsbn Hsbi Hsbs Hsbb
                      Hbsl Hfrag Hdead Hoc Htc Hcont]").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc
                                           Hpbare".
      iDestruct ("Hpback2" with "Hpbare") as "Hpriv".
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf ns with "[%] [%] Hcg Hown Htce Hcce Hpc
                Hsbn Hsbi Hsbs Hsbb Hbsl Hisl
                [Hpriv Hfds Hfrag Hdead Hoc Htc]").
      { exact Hcsf. }
      { unfold sys_open_slots, create_slots in *. lia. }
      { (* ARM B-FAIL: the walk died at some hop, so NOTHING was observed
           and both commits come home beside the era refund. *)
        iApply (so_arm_dead gf (proc_addr jx) pidv vom P Pmiss Φo Φt U sts _
                  (bview plen bp) Ha0f
                  with "Hpriv Hfrag Hfds Hdead Hoc Htc"). } }
    (* ---- namei RESOLVED: the reference, shed and generation-named, and
       THE CURSOR at the end of the walk ---- *)
    iDestruct "Hres" as (iL) "(%Hnaip & Hheldip & HP & Hir1)".
    (* the package comes apart HERE rather than after the branch: its own
       [ipv = ientry kk] is what refutes the [c.beqz]. *)
    iDestruct "Hheldip" as (kk qq inum)
      "(%Hipe & %Hkk & %Hinumc & %Hinumz & Hrefip & Hru)".
    assert (Hipnz : ipv <> (zero_reg : mword 64)).
    { rewrite Hipe. apply ientry_ne_zero. lia. }
    (* the cursor's inum IS the reference's ([SpecNameiTr.inode_held_at]'s
       one new tie), so the residue below is at [bv_unsigned inum]. *)
    subst iL.
    iApply (wp_cbeqz_fall_s_sconf (CID := CID4) (mword_of_int (SO + 0xe6))
              (mword_of_int 19 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              P1 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HP1a0 Hnaip;
                    apply (proj2 (eq_vec_false_iff _ _)); exact Hipnz)
              with "Hcg Hpc []").
    { iApply (soi_0e6 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    assert (Hppe6 : add_vec_int (mword_of_int (SO + 0xe6) : mword 64) 2
                    = mword_of_int (SO + 0xe8)) by pcw.
    iEval (rewrite Hppe6) in "Hpc".
    (* ===== BLOCKER 2's FOUR LINES ===== *)

    assert (Hinb : bv_unsigned inum < 16 * Z.of_nat icfg_nib)
      by (exact Hinumc).
    destruct (Hiregb inum Hinb) as [Hiblk Hiblog].
    iEval (rewrite inode_ref_shed) in "Hrefip".
    iDestruct "Hrefip" as "[Hkeep Hshr]".
    iEval (rewrite inode_shr_gen_intro) in "Hshr".
    iDestruct "Hshr" as (gy loy tly) "(%Hley & #Hfly & Hshr)".
    iEval (rewrite inode_ref_short_gen_intro) in "Hkeep".
    iDestruct "Hkeep" as (gp lop tlp) "(%Hlep & #Hflp & Hkeep)".
    iDestruct (inode_ref_short_shr_genlo_agree with "Hkeep Hshr") as %[-> ->].
    iDestruct (is_itable2_claims with "Hitab") as "#Hclaimsy".
    iAssert ((∃ loK tlK : nat,
       ⌜(loK <= tlK)%nat⌝ ∗ IcacheRef.cred_floor loK tlK ∗
       IcacheRef.inode_ref_short_genlo kk (qq/2 + qq/2)%Qp (qq/2)%Qp icfg_dev inum
         gy loK))%I with "[Hkeep]" as "Hkeep".
    { iExists loy, tlp. iSplitR; [by iPureIntro|]. iFrame "Hflp Hkeep". }
    iDestruct (so_esc_acc kk Hkk with "Hescrows")
      as "#Hesck".
    iDestruct (so_slk_acc kk Hkk with "Hslks") as (gil gisl) "#Hslkk".
    iDestruct (so_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    (* the reference ledger at the join: namei took two and gave one back *)
    iDestruct (iref_slots_combine 1 (ns - 2) with "Hir1 Hirr") as "Hisl".
    assert (Hnsj : (1 + (ns - 2))%nat = (ns - 1)%nat) by lia.
    iEval (rewrite Hnsj) in "Hisl".
    assert (Hiu : (iput_units <= n1)%nat)
      by exact (so_bud_iput _ w1 true (proj1 Hn1)).
    rewrite Hnaip Hipe in HP1s1.
    rewrite Hnaip Hipe in HP1a0.
    (* ===== +0xe8 jal ra,ilock  (a0 is STILL namei's return) ===== *)
    iApply (wp_jal_s_sconf (CID := CID5) (mword_of_int (SO + 0xe8)) Rra
              (mword_of_int 2088964 : mword 21) P1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_0e8 with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (P2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0xe8) : mword 64) 4)]> P1).
    assert (Hjil : add_vec (mword_of_int (SO + 0xe8) : mword 64)
                     (sign_extend' 64 (mword_of_int 2088964 : mword 21))
                   = mword_of_int KernelSyms.ilock) by pcw.
    iEval (rewrite Hjil) in "Hpc".
    assert (HP2ra : (P2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0xe8) : mword 64) 4)
      by (rewrite /P2; apply upd_eq).
    assert (HP2a0 : (P2 !!! Regidx Ra0 : mword 64) = ientry kk)
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (HP2sp : so_sp sp0 P2)
      by (rewrite /so_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2s0 : (P2 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /P2 upd_ne; [exact HP1s0 | nz]).
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /P2 upd_ne; [exact HP1s1 | nz]).
    assert (HP2s2 : (P2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s2 | nz]).
    assert (HP2s3 : (P2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s3 | nz]).
    assert (HP2thr : so_thr m P2).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2b N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID3 CID6 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    (* THE CHECKOUT IS ARMED (durable-disk B''-tx2) AT THE CHECKOUT ITSELF
       (B''-tx3): half of this transaction's element is handed to [ilock] as
       the descriptor's own parked share, so the slot's escrow holds a [DepTx]
       from the instant the entry leaves; sys_open keeps the other half inside
       the descriptor until the release, so the walk carries only the BUDGET
       half of the token from here on. *)

    iDestruct (log_tx_halve with "Htx") as (t) "[Htp Htr]".
    iPoseProof (TsoGhost.llb_0 loglen_name) as "#Hllb0".   (* r25 lane (ii): nothing to present at this ilock *)
    iApply (Ilock.wp_ilock_dep_sconf (CID := CID6) gs jx gl pd pav pu
              gil gisl
              kk (qq/2)%Qp gy loy tly (DepTx (qq/2)%Qp icfg_dev inum gy loy t (1/2)) PlainK
 inum pidv (DfracOwn (1/4)) dqs
              P2 (K - 24)%nat eb b lks U
              HKil eq_refl ltac:(discriminate)
              Hkk Hgeom Hist0 Hiblk Hinb Hj Hgl HP2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hitinv Hesck Hireg
                    Hslkk [//] Hfly Hclaimsy Hshr [Htp] Hru Hsbi Hpbare Hprocs Hdev Hgeo Hdlk Hbs1 Hllb0").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { rewrite /ic_dep_side. iExact "Htp". }
    iIntros (CID7 Hq7 mil dn bm fl)
      "%Hcsil _ Hcg Hown _ _ Hpc Hpbare Hsbi Hbs1 Hslkd Hdep Hoffr
       Hidev Hiinum Hivalid Hload #Hshot Hfrz %Hfl Hru %Hilkp".
    iEval (rewrite /ic_dep_held /=) in "Hload".
    iDestruct (ic_tx_dep_intro with "Hdep Htr") as "Hdep".
    (* ---- THE TERMINAL OBSERVATION (SpecSysOpenAU item 2): fired the
       instant the child is locked, off the payload's OWN era fragment.
       The payload STAYS PEELED from here down -- the O_TRUNC receipt far
       below has to read the same [data] this row was read at. ---- *)
    iDestruct (so_flat_open with "Hload") as (data) "Hflat".
    iDestruct (so_flat_top with "Hflat") as "[Htop Hflatb]".
    iApply fupd_wp.
    iMod (opf_open_fire_1 fsc_fs ⊤ Φo (bv_unsigned inum)
            (era_node dn bm data) ltac:(solve_ndisj) with "[] Hoc Htop")
      as "[Htop Hobs0]";
      [iApply (ireg_inv_ftop with "Hireg") |].
    iModIntro.
    iDestruct ("Hflatb" with "Htop") as "Hflat".
    iAssert (so_obs Φo (bv_unsigned inum) (era_node dn bm data))
      with "[Hobs0]" as "Hobs".
    { rewrite /so_obs. iExact "Hobs0". }
    assert (Hpcil : ret_pc (P2 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0xec)) by (rewrite HP2ra; pcw).
    iEval (rewrite Hpcil) in "Hpc".
    iDestruct (so_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
      [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
    (* the process, put back whole: everything below wants [proc_priv] *)
    iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
    iCombine "Hpbare Hofiles" as "Hpnc".
    iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
    iDestruct (proc_priv_split_cwd gf (proc_addr jx) pidv U
                 with "[Hpnc Href Hftok]") as "Hpriv";
      [iSplitL "Hpnc"; [iExact "Hpnc" | iFrame "Href Hftok"] |].
    assert (Hilsp : so_sp sp0 mil).
    { rewrite /so_sp (callee_saved_lookup Hcsil csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HP2sp. }
    assert (Hils0 : (mil !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsil Rs0 ltac:(vm_compute; reflexivity)).
      exact HP2s0. }
    assert (Hils1 : (mil !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite (callee_saved_lookup Hcsil Rs1 ltac:(vm_compute; reflexivity)).
      exact HP2s1. }
    assert (Hils2 : (mil !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsil Rs2 ltac:(vm_compute; reflexivity)).
      exact HP2s2. }
    assert (Hils3 : (mil !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsil Rs3 ltac:(vm_compute; reflexivity)).
      exact HP2s3. }
    assert (Hilthr : so_thr m mil).
    { intros c Hc N2b N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsil c Hc).
      exact (HP2thr c Hc N2b N8 N9 N18 N19). }
    (* ===== +0xec lh a4,68(s1) -- ip->type ===== *)
    iDestruct (so_flat_meta with "Hflat") as "[Hmeta Hlback]".
    iDestruct (so_type_acc with "Hmeta") as "[Hity Hmback]".
    iEval (rewrite /i_type) in "Hity".
    iApply (wp_lh_s_sconf (CID := CID7) (kt := KT1) (ktd := KT0) (mword_of_int (SO + 0xec)) Ra4 Rs1
              (mword_of_int 68 : mword 12) mil (K - 24)%nat
              (di_type dn : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hity]").
    { iApply (soi_0ec with "Htext"). }
    { iEval (rgne; rewrite Hils1). iExact "Hity". }
    iIntros (CID8 Hq8) "Hcg Hpc Hity".
    iEval (rgne; rewrite Hils1) in "Hity".
    iDestruct ("Hmback" with "[Hity]") as "Hmeta";
      [iEval (rewrite /i_type); iExact "Hity" |].
    iDestruct ("Hlback" with "Hmeta") as "Hflat".
    set (Q1 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_type dn : mword 16) : mword 64)]> mil).
    assert (HQ1a4 : (Q1 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /Q1; apply upd_eq).
    assert (Hppec : add_vec_int (mword_of_int (SO + 0xec) : mword 64) 4
                    = mword_of_int (SO + 0xf0)) by pcw.
    iEval (rewrite Hppec) in "Hpc".
    (* ===== +0xf0 c.li a5,1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID8) (mword_of_int (SO + 0xf0)) Ra5
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              Q1 (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (soi_0f0 with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (Q2 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> Q1).
    assert (HQ2a4 : (Q2 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /Q2 upd_ne; [exact HQ1a4 | nz]).
    assert (HQ2a5 : (Q2 !!! Regidx Ra5 : mword 64) = (mword_of_int 1 : mword 64))
      by (rewrite /Q2; apply upd_eq).
    assert (HQ2sp : so_sp sp0 Q2).
    { rewrite /so_sp /Q2 upd_ne; [| nz]. rewrite /Q1 upd_ne; [| nz].
      exact Hilsp. }
    assert (HQ2s0 : (Q2 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /Q2 upd_ne; [| nz]. rewrite /Q1 upd_ne; [| nz]. exact Hils0. }
    assert (HQ2s1 : (Q2 !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite /Q2 upd_ne; [| nz]. rewrite /Q1 upd_ne; [| nz]. exact Hils1. }
    assert (HQ2s2 : (Q2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /Q2 upd_ne; [| nz]. rewrite /Q1 upd_ne; [| nz]. exact Hils2. }
    assert (HQ2s3 : (Q2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /Q2 upd_ne; [| nz]. rewrite /Q1 upd_ne; [| nz]. exact Hils3. }
    assert (HQ2thr : so_thr m Q2).
    { intros c Hc N2b N8 N9 N18 N19.
      rewrite /Q2 upd_ne; [| regne]. rewrite /Q1 upd_ne; [| regne].
      exact (Hilthr c Hc N2b N8 N9 N18 N19). }
    assert (Hppf0 : add_vec_int (mword_of_int (SO + 0xf0) : mword 64) 2
                    = mword_of_int (SO + 0xf2)) by pcw.
    iEval (rewrite Hppf0) in "Hpc".
    (* ===== +0xf2 bne a4,a5, +0x4a  -- the JOIN ===== *)
    destruct (decide (di_type dn = (mword_of_int 1 : mword 16))) as [Hty | Hty].
    2:{ (* ---- NOT a directory: straight to the join at +0x4a ---- *)
      iApply (wp_bne_taken_s_sconf (CID := CID9) (mword_of_int (SO + 0xf2))
                (mword_of_int 8024 : mword 13) Ra5 Ra4 Q2 (K - 24)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HQ2a4 HQ2a5;
                      exact (so_neq_of_ne _ _
                               (so_ty_ne (di_type dn) 1 so_tdir_range Hty)))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_0f2 with "Htext"). }
      iIntros (CID10 Hq10). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgf2 : add_vec (mword_of_int (SO + 0xf2) : mword 64)
                        (sign_extend' 64 (mword_of_int 8024 : mword 13))
                      = mword_of_int (SO + 0x4a)) by pcw.
      iEval (rewrite Htgf2) in "Hpc".
      assert (Hdirw : bv_unsigned (di_type dn) = T_DIR_z ->
                      om = (mword_of_int 0 : mword 32)).
      { intro Hc. exfalso. exact (so_tdir_zne (di_type dn) Hty Hc). }
      iDestruct (log_opS_opb with "HopS") as "Hop".
      iDestruct (cpu_own_transport CID7 CID10 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      (* THE ADAPTER, the else arm's copy: the iref interval widens from
         the join's [nsj <= ns' <= S nsj] to the syscall's, namei having
         spent one of the three. *)
      iAssert (wp_next true (proc_addr jx)
                 (so_cont_au gf
                          (ns - 1)%nat dqb dqs (proc_addr jx) pidv vom U sts
                          P Pmiss Φo Φt m K eb b lks))
        with "[Hcont Hsbn Hsbs]" as "Hcontj".
      { iEval (rewrite /wp_next). iIntros (CIDz) "%Hqz".
        iEval (rewrite /so_cont_au). iIntros (mf ns2) "%Hcsf %Hns2".
        iIntros "Hcg Hown Htce Hcce Hpc Hsbb Hsbi Hbsl Hisl Hpost".
        iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf ns2 with "[%] [%] Hcg Hown Htce Hcce Hpc
                  Hsbn Hsbi Hsbs Hsbb Hbsl Hisl Hpost").
        { exact Hcsf. }
        { unfold sys_open_slots, create_slots in *. lia. } }
      iApply (Join.so_join_au (CID0 := CID10) gfl gf gs jx gl pd pav pu
                gil gisl
 kk (qq/2)%Qp (qq/2)%Qp gy loy tly inum dn bm om lo
                (ns - 1)%nat n1 pidv dqb dqs U sts m Q2 sp0 K eb b lks w4 w5 w6 w24
                bp1
                data vom (bview plen bp) P Pmiss Φo Φt
                eq_refl HKfull Hkk Hinb Hgeom Hsize Hbm0 Hbmcov Hbmlog
                Hist0 Hiblk Hiblog Hcovb Hiu Hj Hgl Hlkempty Hdirw Hom
                Hal23 Hsp0 HQ2sp HQ2thr HQ2s0 HQ2s1 HQ2s2 HQ2s3 Hal ltac:(unfold sys_open_slots, create_slots in *; lia)
                with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hftab Hbio Hlog
                      Hseam Hgen Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd
                      [//] Hfly Hclaimsy Hdep Hoffr Hidev Hiinum Hivalid Hflat Hshot Hfrz Hkeep Hru Hpriv Hprocs
                      Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hfrag Hf1
                      Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23lo H23hi H24
                      HP Hobs Htc Hcontj").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. } }
    (* ---- IT IS A DIRECTORY: the omode test decides ---- *)
    iApply (wp_bne_fall_s_sconf (CID := CID9) (mword_of_int (SO + 0xf2))
              (mword_of_int 8024 : mword 13) Ra5 Ra4 Q2 (K - 24)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HQ2a4 HQ2a5;
                    exact (so_neq_of_eq _ _
                             (so_ty_eq (di_type dn) 1 so_tdir_range Hty)))
              with "Hcg Hpc []").
    { iApply (soi_0f2 with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc".
    assert (Hppf2 : add_vec_int (mword_of_int (SO + 0xf2) : mword 64) 4
                    = mword_of_int (SO + 0xf6)) by pcw.
    iEval (rewrite Hppf2) in "Hpc".
    (* ===== +0xf6 lw a5,-180(s0) -- the omode word ===== *)
    iApply (wp_lw_s_sconf (CID := CID10) (mword_of_int (SO + 0xf6)) Ra5 Rs0
              (mword_of_int 3916 : mword 12) Q2 (K - 24)%nat om b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [H23hi]").
    { iApply (soi_0f6 with "Htext"). }
    { iEval (rgne; rewrite HQ2s0; rewrite so_omode). iExact "H23hi". }
    iIntros (CID11 Hq11) "Hcg Hpc H23hi".
    iEval (rgne; rewrite HQ2s0; rewrite so_omode) in "H23hi".
    set (Q3 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 om : mword 64)]> Q2).
    assert (HQ3a5 : (Q3 !!! Regidx Ra5 : mword 64) = so_omv om)
      by (rewrite /Q3 /so_omv; apply upd_eq).
    assert (HQ3sp : so_sp sp0 Q3)
      by (rewrite /so_sp /Q3 upd_ne; [exact HQ2sp | nz]).
    assert (HQ3s0 : (Q3 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /Q3 upd_ne; [exact HQ2s0 | nz]).
    assert (HQ3s1 : (Q3 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /Q3 upd_ne; [exact HQ2s1 | nz]).
    assert (HQ3s2 : (Q3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /Q3 upd_ne; [exact HQ2s2 | nz]).
    assert (HQ3s3 : (Q3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /Q3 upd_ne; [exact HQ2s3 | nz]).
    assert (HQ3thr : so_thr m Q3).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /Q3 upd_ne; [| regne].
      exact (HQ2thr c Hc N2b N8 N9 N18 N19). }
    assert (Hppf6 : add_vec_int (mword_of_int (SO + 0xf6) : mword 64) 4
                    = mword_of_int (SO + 0xfa)) by pcw.
    iEval (rewrite Hppf6) in "Hpc".
    (* ===== +0xfa c.beqz a5, +0x5e -- NOT the join: [so_alloc] ===== *)
    destruct (decide (om = (mword_of_int 0 : mword 32))) as [Hom0 | Homnz].
    { (* ---- O_RDONLY on a directory: the T_DEVICE test is SKIPPED ---- *)
      iApply (wp_cbeqz_taken_s_sconf (CID := CID11) (mword_of_int (SO + 0xfa))
                (mword_of_int 178 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                Q3 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HQ3a5 Hom0;
                      apply (proj2 (eq_vec_true_iff _ _)); exact so_omv_zero)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_0fa with "Htext"). }
      iIntros (CID12 Hq12). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgfa : add_vec (mword_of_int (SO + 0xfa) : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13 (concat_vec (mword_of_int 178 : mword 8) ('b"0"))))
                      = mword_of_int (SO + 0x5e)) by pcw.
      iEval (rewrite Htgfa) in "Hpc".
      iDestruct (log_opS_opb with "HopS") as "Hop".
      iDestruct (cpu_own_transport CID7 CID12 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iAssert (wp_next true (proc_addr jx)
                 (so_cont_au gf
                          (ns - 1)%nat dqb dqs (proc_addr jx) pidv vom U sts
                          P Pmiss Φo Φt m K eb b lks))
        with "[Hcont Hsbn Hsbs]" as "Hcontj".
      { iEval (rewrite /wp_next). iIntros (CIDz) "%Hqz".
        iEval (rewrite /so_cont_au). iIntros (mf ns2) "%Hcsf %Hns2".
        iIntros "Hcg Hown Htce Hcce Hpc Hsbb Hsbi Hbsl Hisl Hpost".
        iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf ns2 with "[%] [%] Hcg Hown Htce Hcce Hpc
                  Hsbn Hsbi Hsbs Hsbb Hbsl Hisl Hpost").
        { exact Hcsf. }
        { unfold sys_open_slots, create_slots in *. lia. } }
      (* a DIRECTORY at O_RDONLY, so the device arm is unreachable and the
         major bound is vacuous *)
      iApply (Alloc.so_alloc_au (CID0 := CID12) gfl gf gs jx gl pd pav pu
                gil gisl
 kk (qq/2)%Qp (qq/2)%Qp gy loy tly inum dn bm om lo
                (ns - 1)%nat n1 pidv dqb dqs U sts m Q3 sp0 K eb b lks w4 w5 w6 w24
                bp1
                data vom (bview plen bp) P Pmiss Φo Φt
                eq_refl HKfull Hkk Hinb Hgeom Hsize Hbm0 Hbmcov Hbmlog
                Hist0 Hiblk Hiblog Hcovb Hiu Hj Hgl Hlkempty
                ltac:(intros _; exact Hom0) Hom
                ltac:(intros Hq; exfalso; rewrite Hty in Hq;
                      vm_compute in Hq; discriminate)
                Hal23 Hsp0 HQ3sp HQ3thr HQ3s0 HQ3s1 HQ3s2 HQ3s3 Hal ltac:(unfold sys_open_slots, create_slots in *; lia)
                with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hftab Hbio Hlog
                      Hseam Hgen Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd
                      [//] Hfly Hclaimsy Hdep Hoffr Hidev Hiinum Hivalid Hflat Hshot Hfrz Hkeep Hru Hpriv Hprocs
                      Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hfrag Hf1
                      Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23lo H23hi H24
                      HP Hobs Htc Hcontj").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. } }
    (* ---- a directory opened for writing: ARM C-FAIL at +0xfc ---- *)
    iApply (wp_cbeqz_fall_s_sconf (CID := CID11) (mword_of_int (SO + 0xfa))
              (mword_of_int 178 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              Q3 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HQ3a5;
                    apply (proj2 (eq_vec_false_iff _ _)); intro Hc;
                    apply Homnz; apply so_omode_eqz;
                    apply (proj2 (eq_vec_true_iff _ _)); exact Hc)
              with "Hcg Hpc []").
    { iApply (soi_0fa with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc".
    assert (Hppfa : add_vec_int (mword_of_int (SO + 0xfa) : mword 64) 2
                    = mword_of_int (SO + 0xfc)) by pcw.
    iEval (rewrite Hppfa) in "Hpc".
    iDestruct "Hkeep" as (loK2 tlK2) "(%HleK2 & #HflK2 & Hkeep)".
    iDestruct (inode_ref_short_gen_forget _ _ _ _ _ _ _ _ HleK2
                 with "HflK2 Hkeep") as "Hkeepe".
    iDestruct (so_flat_close with "Hflat") as "Hload".
    iDestruct (proc_priv_bare_acc with "Hpriv") as "[Hpbare Hpback2]".
    iDestruct (so_omode_join sp0 lo om Hal23 with "H23lo H23hi") as "H23".
    iDestruct (log_opS_opb with "HopS") as "Hop".
    iDestruct (cpu_own_transport CID7 CID12 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Tails.so_tail_c (CID0 := CID12) gs jx gl pd pav pu
              gil gisl
 kk (qq/2)%Qp (qq/2)%Qp gy loy tly inum dn bm n1 pidv
              (DfracOwn (1/4)) dqb dqs m Q3 sp0 K eb b lks w4 w5 w6
              (word_of_words lo om) w24 bp1 U
              HKup HKeo HK24 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
              Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HQ3sp HQ3thr
              HQ3s1 HQ3s2 HQ3s3 Hal
              with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen Hitab
                    Hitinv Hesck Hireg Hropen Hslkk Hslkd [//] Hfly Hclaimsy Hdep Hoffr Hidev Hiinum
                    Hivalid Hload Hshot Hfrz Hkeepe Hru Hsbb Hsbi Hbmres Hpbare Hprocs
                    Hdev Hgeo Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23
                    H24 [Hpback2 Hfds Hisl Hsbn Hsbs Hfrag HP Hobs Htc Hcont]").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf)
      "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpbare Hsbb Hsbi Hbsl
       Hislot".
    iDestruct ("Hpback2" with "Hpbare") as "Hpriv".
    iEval (rewrite /iref_slot) in "Hislot".
    iDestruct (iref_slots_combine 1 (ns - 1) with "Hislot Hisl") as "Hisl".
    assert (Hnsc : (1 + (ns - 1))%nat = ns) by lia.
    iEval (rewrite Hnsc) in "Hisl".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf ns with "[%] [%] Hcg Hown Htce Hcce Hpc
              Hsbn Hsbi Hsbs Hsbb Hbsl Hisl [Hpriv Hfds Hfrag HP Hobs Htc]").
    { exact Hcsf. }
    { unfold sys_open_slots, create_slots in *. lia. }
    { (* ARM C-FAIL: a directory opened for writing.  The observation HAS
         fired -- this refusal is inside the child's lock window. *)
      iApply (so_arm_fail gf (proc_addr jx) pidv vom P Pmiss Φo Φt U sts _
                (bview plen bp) (bv_unsigned inum) (era_node dn bm data) Ha0f
                with "Hpriv Hfrag Hfds HP Hobs Htc"). }
  Qed.

End ProofSysOpenAUWalk.

End SysOpenAUWalk.
