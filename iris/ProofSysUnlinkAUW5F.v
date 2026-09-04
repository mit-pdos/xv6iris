(* ProofSysUnlinkAUW5F.v -- the unlink AU walk's BLOCK W5-FILE: the
   zeroing writei, ip->nlink--, iupdate(ip) and the success epilogue, on
   the +0x8a seam's [isdir = false] arm.

     W5-FILE  +0x8a .. +0xe0

   [ProofSysUnlink.su_w5_file]'s copy-adapt, at [SpecSysUnlinkAU]'s
   contract.  THIS BLOCK IS WHERE THE DELTA HAPPENS, and it happens at TWO
   instants, which is the statement's one structural deviation from the
   mknod mold:

     INSTANT 1, at the memset+writei that zeroes the found record:
       [FsAbsUnlinkFire.uf_uent_fire] REPLACES the [ireg_top_retag] the
       landed walk calls there.  Same premise, same payout, plus the
       caller's two phases inside the one [ftopN] critical section.  It
       reads [ip]'s row BESIDE the parent's -- [unl_pre]'s last three
       conjuncts -- off the fragment W3 locked and this block still holds,
       and that borrowed reading is what lets a quiescent consumer read the
       pair as one [delta_unlink] ([delta_unlink_split]).  On THIS arm the
       target is not a directory, so [unl_dec] is 0 and the parent's count
       does not move ([su_au_nondir_dec]).
     INSTANT 2, after [wp_iupdate_unlink]:
       [uf_utgt_fire] at the target's own retag, count lowered by one.  It
       is a SECOND instant and not a second phase of the first because
       [iunlockput(dp)] runs between them -- [ftopN] closes and reopens,
       real instructions run, and a concurrent observer may see the
       intermediate state (entry gone, target count not yet down).

   THE LINK-RA MOVES ARE THE LANDED WALK'S, UNREORDERED.  The fires sit
   BESIDE them: instant 1's where [FsStateEra.ent_toks_unlink] and
   [IregLinkNz.ireg_tok_nz] already sit (the zeroed entry gives up the
   target's [link_tok] and its type is read off that token, which is what
   this arm's [Htynzi] comes from), instant 2's after
   [SpecIupdate.wp_iupdate_unlink] has consumed it.  Nothing about the
   tokens crosses the AU interface.

   THE ret-0 ARM is the statement's: the fetched path existentially, the
   cursor at the parent, [unl_pre] restated purely at instant 1, BOTH fired
   receipts, the instant-2 pin [av1 !! t = Some a] (true because [ip]'s
   fragment was in this walk's custody across the gap), the region bound on
   [t], and the two observation commits refunded. *)
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
Require Import RegFile HartTp WpNext.
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
Require Import SpecPanic.
Require Import SpecPrintk.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioInv.
Require Import FsState.
Require Import FsBytesGamma.
Require Import FsStateEra.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import IregLinkNz.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecIput.
Require Import SpecIupdate.
Require Import SpecIunlockput.
Require Import SpecDirlookup.
Require Import SpecDirlink.
Require Import SpecMemset.
Require Import SpecWritei.
Require Import PathElems.
Require Import CodeSysUnlink.
Require Import SysUnlinkBudget.
Require Import SpecSysUnlink.
Require Import ProofSysUnlinkParts.
Require Import ProofSysUnlinkTails.
Require Import ProofSysUnlink.
Require Import SpecSysMknodAU.
Require Import FsAbsMknodFire.
Require Import SpecSysUnlinkAU.
Require Import FsAbsUnlinkFire.
Require Import ProofSysUnlinkAUParts.
Require Import FsAbsInv.        (* [fsabsE]: the commit mask *)
Require Import FsAbs.
From Kernel Require KernelSyms KernelData.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Local Open Scope Z_scope.
Require Import TsoCtx.
Require Import OffBox.   (* [off_rows] / [off_rows_dep] / [off_rows_to_dep] -- the inode's off rows (items 35/36) *)

Set Printing Depth 40.

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.


Module SysUnlinkAUW5F (Ilock : ILOCK) (Memset : MEMSET) (Writei : WRITEI)
                      (Iupdate : IUPDATE) (Iunlockput : IUNLOCKPUT)
                      (EndOp : END_OP) (PN : PANIC).

Module Tails := SysUnlinkTails Iunlockput EndOp PN.

Section ProofSysUnlinkAUW5F.
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

  (*  W5-FILE: +0x8a .. +0xe0 at the +0x8a seam's [isdir = false].       *)
  (*                                                                     *)
  (*    memset(&de,0,16) ; writei(dp,0,&de,off,16)  -- the zeroing.      *)
  (*    VERDICT #3 (home-live) and VERDICT #1                          *)
  (*    ([FsStateEra.ent_toks_unlink] + [dinode_at_excl]) both fire at   *)
  (*    the writei.                                                     *)
  (*    Then the +0xb4 T_DIR test FALLS (this arm's payload),            *)
  (*    iunlockput(dp) CREDITED off [wi16_post]'s membership trio,       *)
  (*    ip->nlink-- / iupdate(ip) at the LEFT receipt (a FILE's          *)
  (*    decrement can land at zero), iunlockput(ip) credited off         *)
  (*    iupdate's own [∪ {IBLOCK ip}], end_op, a0 = 0, the three         *)
  (*    reloads, and the shared epilogue.                                *)

  (* ================================================================== *)
  Lemma su_w5_file_au `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs dqbs : dfrac)
      (pid : mword 32) (U : ustate) (P1 : uptd)
      (n1 : nat) (Sb1 : gset Z) (w1 : bool)
      (kd ks kk : nat) (gild gisld gyd : gname) (qdi sd qs : Qp)
      (loyd tlyd : nat)
      (dinum : mword 32) (dnd : dinode) (bmd : blkmap)
      (datd : nat -> list (bv 8)) (lo : bv 32)
      (nf bnm0 bp bd bex : nat -> bv 8)
      (w6 w30 : mword 64)
      (gili gisli gyi : gname) (si qsi : Qp) (loyi tlyi : nat)
      (dni : dinode) (bmi : blkmap) (dati : nat -> list (bv 8))
      (m M3 : regfile) (sp0 s3x : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) (t : nat)
      (pl : list (bv 8))
      (P Pmiss : nat -> Z -> iProp Σ)
      (Phient : aview -> Z -> fname -> Z -> iProp Σ)
      (Phitgt : aview -> Z -> iProp Σ)
      (Phiex : aview -> Z -> fname -> Z -> iProp Σ)
      (Phimiss : aview -> Z -> fname -> iProp Σ) :
    (K_sys_unlink <= K)%nat ->
    printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk ->
    (0 < icfg_nib)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < fsc_size <= BPB ->
    0 <= fsc_bmapstart ->
    fsc_bmapstart ∈ fsc_cov ->
    ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
    0 <= icfg_ist ->
    cov_below fsc_cov fsc_size ->
    ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
    (jx < NPROC)%nat ->
    gs !! jx = Some gl ->
    eb = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_al sp0 ->
    (su_u1 w1 <= n1)%nat ->
    uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P1 ->
    (kd < NINODE)%nat ->
    (ks < NINODE)%nat ->
    bv_unsigned dinum < 16 * Z.of_nat icfg_nib ->
    di_type dnd = SpecDirlookup.T_DIR ->
    inode_ok fsc_cov fsc_logst dnd bmd datd ->
    (* durable-disk 2b-inode-3: the payload's record-only facts *)
    inode_rec_local dnd ->
    dir_ok icfg_nib dnd datd ->
    dir_dots_ix (bv_unsigned dinum) dnd datd ->
    dir_orphan_clean dnd datd ->
    dir_uniq dnd datd ->
    bname 14 nf <> dot_name ->
    bname 14 nf <> dotdot_name ->
    dir_first datd (dir_nrec (bv_unsigned (di_size dnd)))
              (bname 14 nf) = Some kk ->
    is_aligned_paddr (Physaddr (pa_stk sp0 27)) 8 = true ->
    (* ---- the +0x8a seam's pure facts, at the FILE payload ---- *)
    su_regs m sp0 (ientry kd) (ientry ks) s3x M3 ->
    bv_unsigned (di_nlink dni) <> 0 ->
    inode_ok fsc_cov fsc_logst dni bmi dati ->
    (* durable-disk 2b-inode-3: the child's record-only facts *)
    inode_rec_local dni ->
    dir_ok icfg_nib dni dati ->
    dir_dots_ix (bv_unsigned (zero_extend' 32
        (dir_inum datd kk : mword 16) : mword 32)) dni dati ->
    dir_orphan_clean dni dati ->
    dir_uniq dni dati ->
    bv_unsigned (di_type dni) <> T_DIR_z ->
    sie_cap_gpr KT1 M3 (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗
    kernel_data -∗
    printk_env fsc_printk fsc_uart fsc_disk -∗
    pc_is (mword_of_int (SU + 0x8a)) -∗
    bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
    log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
    fs_crash_seam fsc_cov fsc_logst -∗
    gen_cert -∗
    dev_inv fsc_uart fsc_disk -∗
    disk_geom fsc_disk pd pav pu -∗
    is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
    bslots 3 -∗
    is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
    itable_inv -∗
    ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
    ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
    ireg_open -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
    bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
    kalloc_env fsc_kalloc None -∗
    procs_inv gs -∗
    proc_priv gf (proc_addr jx) pid (us_upt U P1) -∗
    (* ---- [dp], LOCKED and OPEN ---- *)
    is_sleeplock_genl gild gisld (i_lock (ientry kd)) "inode"%string
                     (ic_slp fsc_ic kd) (slh_tok (icfg_isl kd)) -∗
    sleeplocked_q gisld sd (i_lock (ientry kd)) pid -∗
    ⌜(loyd <= tlyd)%nat⌝ -∗
    IcacheRef.cred_floor loyd tlyd -∗
    IcacheInv.iref_claims -∗
    ic_handle fsc_ic kd (DepTx sd icfg_dev dinum gyd loyd t (1/4)) -∗
    off_rows off_cfg kd cur_ctx -∗
    i_dev (ientry kd) ↦₄{DfracOwn (1/2)} icfg_dev -∗
    i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dinum -∗
    i_valid (ientry kd) ↦₄ valid_word true -∗
    dlinks fsc_fs (bv_unsigned dinum) dnd bmd datd -∗
    dinode_at fsc_ireg dinum dnd -∗
    inode_meta (ientry kd) dnd -∗
    inode_addrs (ientry kd) (bm_cells bmd) -∗
    ind_res fsc_fs bmd -∗
    inode_blocks fsc_fs bmd datd -∗
    (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
    top_frag (fs_gamma_L fsc_fs) (bv_unsigned dinum) (era_node dnd bmd datd) -∗
    ity_shot gyd (di_type dnd) -∗
    (* the payload's freeze token (§3.9, RULING A-prime) *)
    ifreeze_off (bv_unsigned dinum) -∗
    inode_ref_short kd (qdi + sd)%Qp qdi icfg_dev dinum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned dinum) -∗
    (* ---- [ip], LOCKED and OPEN ---- *)
    is_sleeplock_genl gili gisli (i_lock (ientry ks)) "inode"%string
                     (ic_slp fsc_ic ks) (slh_tok (icfg_isl ks)) -∗
    sleeplocked_q gisli si (i_lock (ientry ks)) pid -∗
    ⌜(loyi <= tlyi)%nat⌝ -∗
    IcacheRef.cred_floor loyi tlyi -∗
    IcacheInv.iref_claims -∗
    ic_handle fsc_ic ks (DepTx si icfg_dev (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) gyi loyi t (1/4)) -∗
    off_rows off_cfg ks cur_ctx -∗
    i_dev (ientry ks) ↦₄{DfracOwn (1/2)} icfg_dev -∗
    i_inum (ientry ks) ↦₄{DfracOwn (1/2)}
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) -∗
    i_valid (ientry ks) ↦₄ valid_word true -∗
    dlinks fsc_fs (bv_unsigned (zero_extend' 32
        (dir_inum datd kk : mword 16) : mword 32)) dni bmi dati -∗
    dinode_at fsc_ireg
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) dni -∗
    inode_meta (ientry ks) dni -∗
    inode_addrs (ientry ks) (bm_cells bmi) -∗
    ind_res fsc_fs bmi -∗
    inode_blocks fsc_fs bmi dati -∗
    (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
    top_frag (fs_gamma_L fsc_fs) (bv_unsigned (zero_extend' 32
        (dir_inum datd kk : mword 16) : mword 32)) (era_node dni bmi dati) -∗
    ity_shot gyi (di_type dni) -∗
    (* the payload's freeze token (§3.9, RULING A-prime) *)
    ifreeze_off (bv_unsigned
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)) -∗
    inode_ref_short ks (qsi + si)%Qp qsi icfg_dev
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any
      (bv_unsigned
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)) -∗
    log_opS icfg_log n1 Sb1 -∗
    (* the transaction token rides beside the budget: this walk ends the
       operation, and end_op takes the whole [log_op] (durable-disk lane A) *)
    t ↪[ln_tx icfg_log]{#(1/2)} tt -∗
    (* ---- THE AU SIDE, as W3's seam hands it ---- *)
    ⌜exists es e, nameiparent_of pl es e /\ bname 14 nf = e⌝ -∗
    P (length (mknod_parent_elems pl)) (bv_unsigned dinum) -∗
    uent_commit_at (fs_gamma_L fsc_fs) fsabsE Phient -∗
    utgt_commit_at (fs_gamma_L fsc_fs) fsabsE Phitgt -∗
    dlookup_commit_at (fs_gamma_L fsc_fs) fsabsE Phiex -∗
    dmiss_commit_at (fs_gamma_L fsc_fs) fsabsE Phimiss -∗
    (* ---- the frame, slot 5 FILLED ---- *)
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
    (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ[KT1] bd jj) -∗
    ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nf jj) -∗
    ([∗ list] jj ∈ seq 0 2,
       pa_add (pa_add (pa_stk sp0 10) 14) jj ↦ₘ[KT1] bnm0 (14 + jj)%nat) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 27) ↦₄[KT1] lo -∗
    (pa_add (pa_stk sp0 27) 4) ↦₄[KT1]
      (mword_of_int (Z.of_nat (16 * kk)) : mword 32) -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] bex jj) -∗
    (pa_stk sp0 30) ↦₈[KT1] w30 -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      su_au_closer (CID := CIDx) gf (proc_addr jx) pid U m
        (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
        dqb dqs dqbs (unlink_arms (fs_gamma_L fsc_fs) fsc_fs P Pmiss
                        Phient Phitgt Phiex Phimiss)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hprk Hnib0 Hgeom Hsize Hbm0 Hbmcov
           Hbmlog Hist0 Hcovb Hiregb Hj Hgl Heb Hsp0 Hal Hn1 Hupt1 Hkd Hks
           Hdinb Htydir Hiok Hrl_datd Hdok Hddix Hdoc Hduq Hnotdot Hnotdd
           Hfst Hal27
           Hregs Hnlzi Hioki Hrl_dati Hdoki Hddixi Hdoci Hduqi Htynzi.
    destruct (su_kb K HK) as (Knp & Kdl & Kre & Kwr & Kar & Kbo & Keo & Kil
                              & Kiupd & Kiup & Knc & K2 & K10 & K30 & Kpop).
    iIntros "Hcg Hown #Htext #Hdata #Hprenv Hpc #Hbio #Hlog Hseam Hgen
             #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hireg #Hropen
             Hsbb Hsbi Hsbs #Hbmres #Hkenv #Hprocs Hpriv
             #Hslkd Hslkdq %Hleyd #Hflyd #Hclaimsyd Hdepd Hoffrd Hidevd Hiinumd Hivalidd Hdlnkd
             Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop #Hshotd Hfrz Hkeepd Hrud
             #Hslki Hslkiq %Hleyi #Hflyi #Hclaimsyi Hdepi Hoffri Hidevi Hiinumi Hivalidi Hdlnki
             Hdiati Hmetai Haddrsi Hindi Hblocksi Htopi #Hshoti Hfrzi Hkeepi Hrui HopS Htx
             %Hname HP Hcent Hctgt Hcex Hcmiss
             Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi HbE H30
             Hcont".

    iPoseProof (printk_env_panic with "Hprenv") as "#Hpanenv".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbeq. cbn in Hbeq.
    iDestruct (cpu_own_zero_empty with "Hown") as "[%Hlkempty Hown]".
    assert (Hlb : forall r : string, locks_below lks r).
    { intro r. rewrite Hlkempty. apply locks_below_empty. }
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hcsa3 : is_cs_idx Ra3 = false) by (vm_compute; reflexivity).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    (* ---- the pure groundwork ---- *)
    assert (Htydz : bv_unsigned (di_type dnd) = T_DIR_z)
      by exact (su_tdir_zof _ Htydir).
    assert (Hinums : dir_inums_ok datd
                       (dir_nrec (bv_unsigned (di_size dnd))) icfg_nib)
      by (exact (Hdok Htydz)).
    assert (Hkklt : (kk < dir_nrec (bv_unsigned (di_size dnd)))%nat)
      by exact (dir_first_lt _ _ _ _ Hfst).
    assert (Hkklive : dir_live datd kk)
      by exact (dir_first_live _ _ _ _ Hfst).
    assert (Hkkname : bname 14 (dir_name datd kk) = bname 14 nf)
      by exact (dir_first_name _ _ _ _ Hfst).
    assert (Hinb : bv_unsigned (zero_extend' 32
                     (dir_inum datd kk : mword 16) : mword 32)
                   < 16 * Z.of_nat icfg_nib).
    { rewrite su_zext32_unsigned. exact (Hinums kk Hkklt Hkklive). }
    destruct (Hiregb dinum Hdinb) as [Hdiblk Hdiblog].
    destruct (Hiregb _ Hinb) as [Hiblki Hiblogi].
    (* VERDICT #3 -- the home-live derivation: the matched record's name is
       neither dot, so [dp] cannot be orphaned. *)
    assert (Hdplive : bv_unsigned (di_nlink dnd) <> 0).
    { intro Hz.
      destruct (Hdoc Htydz Hz kk Hkklt Hkklive) as [Hd | Hd];
        rewrite Hkkname in Hd; [exact (Hnotdot Hd) | exact (Hnotdd Hd)]. }
    (* ...and the matched record is neither dot SLOT *)
    destruct (Hddix Htydz Hdplive) as
      (Hnrec2 & Hlv0 & Hself0 & Hname0 & Hlv1 & Hname1).
    assert (Hkk0 : kk <> 0%nat).
    { intro He. rewrite He in Hkkname. rewrite Hkkname in Hname0.
      exact (Hnotdot Hname0). }
    assert (Hkk1 : kk <> 1%nat).
    { intro He. rewrite He in Hkkname. rewrite Hkkname in Hname1.
      exact (Hnotdd Hname1). }
    assert (Hkk0' : (0%nat <> kk)) by (intro He; apply Hkk0; symmetry; exact He).
    assert (Hkk1' : (1%nat <> kk)) by (intro He; apply Hkk1; symmetry; exact He).
    (* the byte bound of the zeroed slot *)
    assert (Hszcap : bv_unsigned (di_size dnd)
                     <= Z.of_nat MAXFILE * Z.of_nat BSIZE).
    { destruct Hiok as (_ & _ & _ & _ & Hc & _). exact Hc. }
    assert (Hmb : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)
      by (vm_compute; reflexivity).
    assert (Hsznn : 0 <= bv_unsigned (di_size dnd))
      by (pose proof (bv_unsigned_in_range _ (di_size dnd)) as Hr; lia).
    assert (Hkk16 : (16 * kk + 16 <= Z.to_nat (bv_unsigned (di_size dnd)))%nat).
    { pose proof (su_nrec16 (bv_unsigned (di_size dnd)) Hsznn) as Hle. lia. }
    assert (HkkZ : Z.of_nat (16 * kk + 16)%nat <= bv_unsigned (di_size dnd)).
    { rewrite <- (Z2Nat.id (bv_unsigned (di_size dnd)) Hsznn).
      apply Nat2Z.inj_le. exact Hkk16. }
    assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (Hkk31 : Z.of_nat (16 * kk)%nat < 2 ^ 31).
    { rewrite Nat2Z.inj_add in HkkZ. lia. }
    (* the record does not name [dp] ITSELF -- VERDICT #1's exclusivity
       half: two full [dinode_at]s at one inum collide. *)
    destruct (decide (bv_unsigned (dir_inum datd kk) = bv_unsigned dinum))
      as [Heqi | Hnotself].
    { assert (Hweq : (zero_extend' 32 (dir_inum datd kk : mword 16)
                      : mword 32) = dinum)
        by (apply bv_eq; rewrite su_zext32_unsigned; exact Heqi).
      iEval (rewrite Hweq) in "Hdiati".
      iExFalso. iApply (dinode_at_excl with "Hdiatd Hdiati"). }
    (* the process block, opened for the callees' pid fraction, and THE
       CLOSER, built once (W2/W3's shape) *)
    iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (us_upt U P1)
                 with "Hpriv") as "[Hpnc Href]".
    iEval (rewrite proc_priv_nocwd_bare) in "Hpnc".
    iDestruct "Hpnc" as "[Hpidq Hofiles]".
    iAssert (proc_priv_bare (proc_addr jx) pid (us_upt U P1) -∗
             proc_priv gf (proc_addr jx) pid (us_upt U P1))%I
      with "[Hofiles Href]" as "Hpre".
    { iIntros "Hpidq".
      iApply (proc_priv_split_cwd gf (proc_addr jx) pid (us_upt U P1)).
      rewrite proc_priv_nocwd_bare.
      iSplitR "Href"; [| iExact "Href"].
      iSplitL "Hpidq"; [iExact "Hpidq" | iExact "Hofiles"]. }
    (* ===== +0x8a addi s3,s0,-64 -- writei's [&de] ===== *)
    iApply (wp_addi4_s_sconf (CID := CID0) (mword_of_int (SU + 0x8a)) Rs3 Rs0
              (mword_of_int 4032 : mword 12) M3 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_08a with "Htext"). }
    iIntros (D1 Hd1) "Hcg Hpc".
    set (A1 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (M3 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 4032 : mword 12)))]> M3).
    assert (HA1v : add_vec (M3 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 4032 : mword 12))
                   = pa_stk sp0 8).
    { rewrite (su_regs_s0 _ _ _ _ _ _ Hregs). apply su_bufde. }
    assert (HA1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A1).
    { rewrite /A1.
      exact (su_regs_wr_s3 m sp0 (ientry kd) (ientry ks) s3x (pa_stk sp0 8)
               M3 _ HA1v Hregs). }
    assert (Hpp8e : add_vec_int (mword_of_int (SU + 0x8a) : mword 64) 4
                    = mword_of_int (SU + 0x8e)) by pcw.
    iEval (rewrite Hpp8e) in "Hpc".
    (* ===== +0x8e c.li a2,16 ===== *)
    iApply (wp_cli_s_sconf (CID := D1) (mword_of_int (SU + 0x8e)) Ra2
              (mword_of_int 16 : mword 6) (mword_of_int 16 : mword 64)
              A1 (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_08e with "Htext"). }
    iIntros (D2 Hd2) "Hcg Hpc".
    set (A2 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int 16 : mword 64)]> A1).
    assert (HA2a2 : (A2 !!! Regidx Ra2 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /A2; apply upd_eq).
    assert (HA2regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A2)
      by (rewrite /A2; apply su_regs_caller; [exact Hcsa2 | exact HA1regs]).
    assert (Hpp90 : add_vec_int (mword_of_int (SU + 0x8e) : mword 64) 2
                    = mword_of_int (SU + 0x90)) by pcw.
    iEval (rewrite Hpp90) in "Hpc".
    (* ===== +0x90 c.li a1,0 ===== *)
    iApply (wp_cli_s_sconf (CID := D2) (mword_of_int (SU + 0x90)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              A2 (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_090 with "Htext"). }
    iIntros (D3 Hd3) "Hcg Hpc".
    set (A3 := <[Regidx Ra1 := regval_into_reg
                  (mword_of_int 0 : mword 64)]> A2).
    assert (HA3a1 : (A3 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /A3; apply upd_eq).
    assert (HA3a2 : (A3 !!! Regidx Ra2 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /A3 upd_ne; [exact HA2a2 | nz]).
    assert (HA3regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A3)
      by (rewrite /A3; apply su_regs_caller; [exact Hcsa1 | exact HA2regs]).
    assert (Hpp92 : add_vec_int (mword_of_int (SU + 0x90) : mword 64) 2
                    = mword_of_int (SU + 0x92)) by pcw.
    iEval (rewrite Hpp92) in "Hpc".
    (* ===== +0x92 c.mv a0,s3 ===== *)
    iApply (wp_cmv_s_sconf (CID := D3) (mword_of_int (SU + 0x92)) Ra0 Rs3 A3
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_092 with "Htext"). }
    iIntros (D4 Hd4) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (A4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (A3 !!! Regidx Rs3))]> A3).
    assert (HA4a0 : (A4 !!! Regidx Ra0 : mword 64) = pa_stk sp0 8).
    { etransitivity; [rewrite /A4; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s3 _ _ _ _ _ _ HA3regs). }
    assert (HA4a1 : (A4 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /A4 upd_ne; [exact HA3a1 | nz]).
    assert (HA4a2 : (A4 !!! Regidx Ra2 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /A4 upd_ne; [exact HA3a2 | nz]).
    assert (HA4regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A4)
      by (rewrite /A4; apply su_regs_caller; [exact Hcsa0 | exact HA3regs]).
    assert (Hpp94 : add_vec_int (mword_of_int (SU + 0x92) : mword 64) 2
                    = mword_of_int (SU + 0x94)) by pcw.
    iEval (rewrite Hpp94) in "Hpc".
    (* ===== +0x94 jal ra,memset ===== *)
    iApply (wp_jal_s_sconf (CID := D4) (mword_of_int (SU + 0x94)) Rra
              (mword_of_int 2079820 : mword 21) A4 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_094 with "Htext"). }
    iIntros (D5 Hd5) "Hcg Hpc".
    set (A5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x94) : mword 64) 4)]> A4).
    assert (Hjms : add_vec (mword_of_int (SU + 0x94) : mword 64)
                     (sign_extend' 64 (mword_of_int 2079820 : mword 21))
                   = mword_of_int KernelSyms.memset) by pcw.
    iEval (rewrite Hjms) in "Hpc".
    assert (HA5ra : (A5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0x94) : mword 64) 4)
      by (rewrite /A5; apply upd_eq).
    assert (HA5a0 : (A5 !!! Regidx Ra0 : mword 64) = pa_stk sp0 8)
      by (rewrite /A5 upd_ne; [exact HA4a0 | nz]).
    assert (HA5a1 : (A5 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4a1 | nz]).
    assert (HA5a2 : (A5 !!! Regidx Ra2 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4a2 | nz]).
    assert (HA5regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A5)
      by (rewrite /A5; apply su_regs_caller; [exact Hcsra | exact HA4regs]).
    iApply (Memset.wp_memset_sconf KT1 KT1 (CID := D5) A5 (K - 30)%nat 16
              (mword_of_int 0 : mword 64) bd b (proc_addr jx)
              K2 ltac:(vm_compute; reflexivity) HA5a1
              ltac:(rewrite HA5a2; pcw)
              with "Hcg Htext Hpc [HbD]").
    { iEval (rewrite HA5a0). iExact "HbD". }
    iIntros (D6 Hd6 mms) "Hcg Hpc HbD %Hcsms".
    iEval (rewrite HA5a0) in "HbD".
    assert (Hpc98 : ret_pc (A5 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0x98)) by (rewrite HA5ra; pcw).
    iEval (rewrite Hpc98) in "Hpc".
    assert (Hmsregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) mms)
      by exact (su_regs_cs m sp0 _ _ _ A5 mms Hcsms HA5regs).
    (* the memset byte is NUL *)
    assert (Hcb : nth_byte (autocast (T := mword)
                    (subrange_vec_dec (mword_of_int 0 : mword 64)
                       (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0%nat = NUL)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hcb) in "HbD".
    (* ===== +0x98 c.li a4,16 ===== *)
    iApply (wp_cli_s_sconf (CID := D6) (mword_of_int (SU + 0x98)) Ra4
              (mword_of_int 16 : mword 6) (mword_of_int 16 : mword 64)
              mms (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_098 with "Htext"). }
    iIntros (D7 Hd7) "Hcg Hpc".
    set (B1 := <[Regidx Ra4 := regval_into_reg
                  (mword_of_int 16 : mword 64)]> mms).
    assert (HB1a4 : (B1 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B1; apply upd_eq).
    assert (HB1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B1)
      by (rewrite /B1; apply su_regs_caller; [exact Hcsa4 | exact Hmsregs]).
    assert (Hpp9a : add_vec_int (mword_of_int (SU + 0x98) : mword 64) 2
                    = mword_of_int (SU + 0x9a)) by pcw.
    iEval (rewrite Hpp9a) in "Hpc".
    (* ===== +0x9a lw a3,-212(s0) -- [uint off], slot 27's UPPER word ===== *)
    iApply (wp_lw_s_sconf (CID := D7) (mword_of_int (SU + 0x9a)) Ra3 Rs0
              (mword_of_int 3884 : mword 12) B1 (K - 30)%nat
              (mword_of_int (Z.of_nat (16 * kk)) : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [H27hi]").
    { iApply (suli_09a with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s0 _ _ _ _ _ _ HB1regs) su_offcell).
      iExact "H27hi". }
    iIntros (D8 Hd8) "Hcg Hpc H27hi".
    iEval (rgne; rewrite (su_regs_s0 _ _ _ _ _ _ HB1regs) su_offcell)
      in "H27hi".
    set (B2 := <[Regidx Ra3 := regval_into_reg
                  (sign_extend' 64
                     (mword_of_int (Z.of_nat (16 * kk)) : mword 32))]> B1).
    assert (Ha3lit : (sign_extend' 64
                        (mword_of_int (Z.of_nat (16 * kk)) : mword 32)
                      : mword 64)
                     = (mword_of_int (Z.of_nat (16 * kk)) : mword 64)).
    { assert (Hus : bv_unsigned (mword_of_int (Z.of_nat (16 * kk)) : mword 32)
                    = Z.of_nat (16 * kk)%nat)
        by (apply moi32_small; lia).
      rewrite su_size_sext; rewrite Hus; [reflexivity | lia]. }
    assert (HB2a3 : (B2 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64)).
    { etransitivity; [rewrite /B2; apply upd_eq |]. exact Ha3lit. }
    assert (HB2a4 : (B2 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B2 upd_ne; [exact HB1a4 | nz]).
    assert (HB2regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B2)
      by (rewrite /B2; apply su_regs_caller; [exact Hcsa3 | exact HB1regs]).
    assert (Hpp9e : add_vec_int (mword_of_int (SU + 0x9a) : mword 64) 4
                    = mword_of_int (SU + 0x9e)) by pcw.
    iEval (rewrite Hpp9e) in "Hpc".
    (* ===== +0x9e c.mv a2,s3 ===== *)
    iApply (wp_cmv_s_sconf (CID := D8) (mword_of_int (SU + 0x9e)) Ra2 Rs3 B2
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_09e with "Htext"). }
    iIntros (D9 Hd9) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (B3 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (B2 !!! Regidx Rs3))]> B2).
    assert (HB3a2 : (B3 !!! Regidx Ra2 : mword 64) = pa_stk sp0 8).
    { etransitivity; [rewrite /B3; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s3 _ _ _ _ _ _ HB2regs). }
    assert (HB3a3 : (B3 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64))
      by (rewrite /B3 upd_ne; [exact HB2a3 | nz]).
    assert (HB3a4 : (B3 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B3 upd_ne; [exact HB2a4 | nz]).
    assert (HB3regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B3)
      by (rewrite /B3; apply su_regs_caller; [exact Hcsa2 | exact HB2regs]).
    assert (Hppa0 : add_vec_int (mword_of_int (SU + 0x9e) : mword 64) 2
                    = mword_of_int (SU + 0xa0)) by pcw.
    iEval (rewrite Hppa0) in "Hpc".
    (* ===== +0xa0 c.li a1,0 ===== *)
    iApply (wp_cli_s_sconf (CID := D9) (mword_of_int (SU + 0xa0)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              B3 (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_0a0 with "Htext"). }
    iIntros (D10 Hd10) "Hcg Hpc".
    set (B4 := <[Regidx Ra1 := regval_into_reg
                  (mword_of_int 0 : mword 64)]> B3).
    assert (HB4a1 : (B4 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /B4; apply upd_eq).
    assert (HB4a2 : (B4 !!! Regidx Ra2 : mword 64) = pa_stk sp0 8)
      by (rewrite /B4 upd_ne; [exact HB3a2 | nz]).
    assert (HB4a3 : (B4 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64))
      by (rewrite /B4 upd_ne; [exact HB3a3 | nz]).
    assert (HB4a4 : (B4 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B4 upd_ne; [exact HB3a4 | nz]).
    assert (HB4regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B4)
      by (rewrite /B4; apply su_regs_caller; [exact Hcsa1 | exact HB3regs]).
    assert (Hppa2 : add_vec_int (mword_of_int (SU + 0xa0) : mword 64) 2
                    = mword_of_int (SU + 0xa2)) by pcw.
    iEval (rewrite Hppa2) in "Hpc".
    (* ===== +0xa2 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := D10) (mword_of_int (SU + 0xa2)) Ra0 Rs1 B4
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0a2 with "Htext"). }
    iIntros (D11 Hd11) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (B5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (B4 !!! Regidx Rs1))]> B4).
    assert (HB5a0 : (B5 !!! Regidx Ra0 : mword 64) = ientry kd).
    { etransitivity; [rewrite /B5; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s1 _ _ _ _ _ _ HB4regs). }
    assert (HB5a1 : (B5 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /B5 upd_ne; [exact HB4a1 | nz]).
    assert (HB5a2 : (B5 !!! Regidx Ra2 : mword 64) = pa_stk sp0 8)
      by (rewrite /B5 upd_ne; [exact HB4a2 | nz]).
    assert (HB5a3 : (B5 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64))
      by (rewrite /B5 upd_ne; [exact HB4a3 | nz]).
    assert (HB5a4 : (B5 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B5 upd_ne; [exact HB4a4 | nz]).
    assert (HB5regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B5)
      by (rewrite /B5; apply su_regs_caller; [exact Hcsa0 | exact HB4regs]).
    assert (Hppa4 : add_vec_int (mword_of_int (SU + 0xa2) : mword 64) 2
                    = mword_of_int (SU + 0xa4)) by pcw.
    iEval (rewrite Hppa4) in "Hpc".
    (* ===== +0xa4 jal ra,writei -- THE ZEROING ===== *)
    iApply (wp_jal_s_sconf (CID := D11) (mword_of_int (SU + 0xa4)) Rra
              (mword_of_int 2090644 : mword 21) B5 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0a4 with "Htext"). }
    iIntros (D12 Hd12) "Hcg Hpc".
    set (B6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xa4) : mword 64) 4)]> B5).
    assert (Hjwi : add_vec (mword_of_int (SU + 0xa4) : mword 64)
                     (sign_extend' 64 (mword_of_int 2090644 : mword 21))
                   = mword_of_int KernelSyms.writei) by pcw.
    iEval (rewrite Hjwi) in "Hpc".
    assert (HB6ra : (B6 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xa4) : mword 64) 4)
      by (rewrite /B6; apply upd_eq).
    assert (HB6a0 : (B6 !!! Regidx Ra0 : mword 64) = ientry kd)
      by (rewrite /B6 upd_ne; [exact HB5a0 | nz]).
    assert (HB6a1 : (B6 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /B6 upd_ne; [exact HB5a1 | nz]).
    assert (HB6a2 : (B6 !!! Regidx Ra2 : mword 64) = pa_stk sp0 8)
      by (rewrite /B6 upd_ne; [exact HB5a2 | nz]).
    assert (HB6a3 : (B6 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64))
      by (rewrite /B6 upd_ne; [exact HB5a3 | nz]).
    assert (HB6a4 : (B6 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B6 upd_ne; [exact HB5a4 | nz]).
    assert (HB6regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B6)
      by (rewrite /B6; apply su_regs_caller; [exact Hcsra | exact HB5regs]).
    (* [inode_ok dp]'s conjuncts, read once *)
    assert (Hiok0 : inode_ok fsc_cov fsc_logst dnd bmd datd) by exact Hiok.
    destruct Hiok0 as (Hwfd & Hcovd & Haddrd & Htynzd & _ & Hhzd & Hszdd).
    assert (Hoffn31 : Z.of_nat (16 * kk)%nat + Z.of_nat 16%nat < 2 ^ 31)
      by lia.
    assert (Hszd31 : bv_unsigned (di_size dnd) < 2 ^ 31) by lia.
    pose proof (su_u1_ge9 w1) as Hge9.
    assert (Hcost : (wi_cost_bmonly (16 * kk) 16 <= n1)%nat)
      by (rewrite (su_wi_cost kk); lia).
    assert (Htynzz : bv_unsigned (di_type dnd) <> 0)
      by (rewrite Htydz; unfold T_DIR_z; lia).
    assert (Hnls : di_nlink_stable dnd dnd)
      by (apply di_nlink_stable_refl; exact Htynzz).
    assert (Hbmgeom : bitmap_geom_ok fsc_cov fsc_logst fsc_bmapstart fsc_size)
      by (unfold bitmap_geom_ok;
          exact (conj Hsize (conj Hbm0 (conj Hbmcov Hbmlog)))).
    assert (Ha1t : eq_vec (B6 !!! Regidx Ra1 : mword 64) (zero_reg : mword 64)
                   = negb false)
      by (rewrite HB6a1; vm_compute; reflexivity).
    assert (Ha3t : (B6 !!! Regidx Ra3 : mword 64)
                   = (mword_of_int (Z.of_nat (16 * kk)%nat) : mword 64))
      by (rewrite HB6a3; reflexivity).
    assert (Ha4t : (B6 !!! Regidx Ra4 : mword 64)
                   = (mword_of_int (Z.of_nat 16%nat) : mword 64))
      by (rewrite HB6a4; pcw).
    iDestruct (cpu_own_transport CID0 D12 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Writei.wp_writei_gen KT1 (CID := D12) gs jx gl pd pav pu
 gf
 (ientry kd) dinum bmd datd dnd dnd false
              (16 * kk)%nat 16%nat (fun _ => NUL) (upd_usM (us_upt U P1) _) n1 Sb1 pid
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs dqb dqbs
              B6 (K - 30)%nat eb b lks
              ltac:(exact Kwr) Hcost
              Hgeom Hist0 Hdiblk Hdiblog Hdinb Haddrd
              Htynzz
              (di_type_stable_refl dnd)
              Hnls
              Hwfd Hhzd Hcovd Hoffn31 Hszd31
              Hbmgeom
              Hprk Hj Hgl HB6a0
              Ha1t Ha3t Ha4t
              (Hlb "log"%string)
              with "Hcg Hown [] [] Htext Hpc Hdata Hprenv Hbio Hlog
                    Hkenv Hidevd Hiinumd Hmetad [Haddrsd Hindd] Hblocksd
                    Hsbi Hsbs Hsbb Hbmres Hireg Hdiatd [HbD Hpidq] Hprocs
                    Hdev Hgeo Hdlk Hbsl HopS").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { rewrite /inode_map. iFrame "Haddrsd Hindd". }
    { iSplitL "HbD"; [| iExact "Hpidq"].
      iEval (rewrite HB6a2). iExact "HbD". }
    iIntros (D13 Hd13 mfw tot bm' data' dnW dn0W nw wrote dist dstb Pw
             Sbw)
      "%Hcsw %Hwf' %Hhz' %Haddr' %Hszlt' %Hcov' %Hcapp %Hszp %Hdistle
       %Hdisttot %Hdist0f %Hrng %Hwr %Hwru %Harm %Hspend %Hsbsub %Hpost16 %Hspendany
       %Hatomic %Hupw Hcg Hown _ _ Hpc Hidevd Hiinumd Hmetad Hmapd Hblocksd
       Hsbi Hsbs Hsbb Hdiatd [HbD Hpidq] Hbsl HopS".
    iEval (rewrite HB6a2) in "HbD".
    assert (Hpca8 : ret_pc (B6 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xa8)) by (rewrite HB6ra; pcw).
    iEval (rewrite Hpca8) in "Hpc".
    assert (Hwregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) mfw)
      by exact (su_regs_cs m sp0 _ _ _ B6 mfw Hcsw HB6regs).
    (* ===== +0xa8 c.li a5,16 ===== *)
    iApply (wp_cli_s_sconf (CID := D13) (mword_of_int (SU + 0xa8)) Ra5
              (mword_of_int 16 : mword 6) (mword_of_int 16 : mword 64)
              mfw (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_0a8 with "Htext"). }
    iIntros (D14 Hd14) "Hcg Hpc".
    set (C1 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int 16 : mword 64)]> mfw).
    assert (HC1a5 : (C1 !!! Regidx Ra5 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /C1; apply upd_eq).
    assert (HC1a0 : (C1 !!! Regidx Ra0 : mword 64)
                    = (mfw !!! Regidx Ra0 : mword 64))
      by (rewrite /C1 upd_ne; [reflexivity | nz]).
    assert (HC1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C1)
      by (rewrite /C1; apply su_regs_caller; [exact Hcsa5 | exact Hwregs]).
    assert (Hppaa : add_vec_int (mword_of_int (SU + 0xa8) : mword 64) 2
                    = mword_of_int (SU + 0xaa)) by pcw.
    iEval (rewrite Hppaa) in "Hpc".
    (* ===== +0xaa bne a0,a5 -> [panic "unlink: writei"] ===== *)
    destruct Harm as [(Ha0m & _ & Htot0 & _) | (Ha0w & _ & Htotle & HdnW & Hdn0W)].
    { (* the -1 arm: writei refused; the test is TAKEN and panic never
         returns *)
      iApply (wp_bne_taken_s_sconf (CID := D14) (mword_of_int (SU + 0xaa))
                (mword_of_int 144 : mword 13) Ra5 Ra0 C1 (K - 30)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HC1a0 Ha0m HC1a5;
                      apply su_neq_of_eq_false; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_0aa with "Htext"). }
      iIntros (D15 Hd15). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg13a : add_vec (mword_of_int (SU + 0xaa) : mword 64)
                         (sign_extend' 64 (mword_of_int 144 : mword 13))
                       = mword_of_int (SU + 0x13a)) by pcw.
      iEval (rewrite Htg13a) in "Hpc".
      iPoseProof (printk_env_panic with "Hprenv") as "#Hpe5".
      iDestruct (cpu_own_transport D13 D15 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Tails.su_panic_writei (CID0 := D15) C1 (K - 30)%nat 0%nat eb b
                (proc_addr jx) lks (su_pn_K K HK) su_pn_noff (Hlb "pr"%string)
                with "Hcg Hown Htext Hdata Hpe5 Hpc"). }
    destruct (decide (tot = 16%nat)) as [-> | Hne16].
    2:{ (* the SHORT WRITE: taken, panic *)
      iApply (wp_bne_taken_s_sconf (CID := D14) (mword_of_int (SU + 0xaa))
                (mword_of_int 144 : mword 13) Ra5 Ra0 C1 (K - 30)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HC1a0 Ha0w HC1a5;
                      exact (su_neq_of_eq_false _ _
                               (su_tot16_ne tot Htotle Hne16)))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_0aa with "Htext"). }
      iIntros (D15 Hd15). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg13a : add_vec (mword_of_int (SU + 0xaa) : mword 64)
                         (sign_extend' 64 (mword_of_int 144 : mword 13))
                       = mword_of_int (SU + 0x13a)) by pcw.
      iEval (rewrite Htg13a) in "Hpc".
      iPoseProof (printk_env_panic with "Hprenv") as "#Hpe5".
      iDestruct (cpu_own_transport D13 D15 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Tails.su_panic_writei (CID0 := D15) C1 (K - 30)%nat 0%nat eb b
                (proc_addr jx) lks (su_pn_K K HK) su_pn_noff (Hlb "pr"%string)
                with "Hcg Hown Htext Hdata Hpe5 Hpc"). }
    (* ===== the write is FULL: sixteen bytes, the record is DEAD ===== *)
    iApply (wp_bne_fall_s_sconf (CID := D14) (mword_of_int (SU + 0xaa))
              (mword_of_int 144 : mword 13) Ra5 Ra0 C1 (K - 30)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HC1a0 Ha0w HC1a5;
                    apply su_neq_of_eq_true;
                    apply (proj2 (eq_vec_true_iff _ _)); reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0aa with "Htext"). }
    iIntros (D15 Hd15) "Hcg Hpc".
    assert (Hppae : add_vec_int (mword_of_int (SU + 0xaa) : mword 64) 4
                    = mword_of_int (SU + 0xae)) by pcw.
    iEval (rewrite Hppae) in "Hpc".
    assert (Hdist0 : dist = 0%nat) by (exact (Hdist0f eq_refl)).
    (* the flushed record: type/nlink/addrs by definition, size by the
       in-range decide *)
    assert (Hty'v : di_type dnW = di_type dnd) by (rewrite HdnW; reflexivity).
    assert (Hnl'v : di_nlink dnW = di_nlink dnd) by (rewrite HdnW; reflexivity).
    assert (Hsz'v : di_size dnW = di_size dnd).
    { rewrite HdnW. unfold wi_dinode. cbn [di_size].
      rewrite decide_False; [reflexivity | lia]. }
    assert (Haddr'v : di_addrs dnW = bm_cells bm')
      by (rewrite HdnW; reflexivity).
    (* the membership trio -- what pays the whole tail *)
    (* [wi16_post]'s guard is [0 < tot], and this arm has already
       substituted [tot := 16], so the goal is [0 < 16].  HOISTED OUT OF
       ARGUMENT POSITION and closed by a term: spliced as [ltac:(lia)] it
       reifies this proof's whole context -- the tree's largest -- to
       decide it, and measured 3.4 s at each of the two sites. *)
    assert (Htot16 : (0 < 16)%nat) by (apply Nat.lt_0_succ).
    destruct (Hpost16 Htot16 (su_wi_blocks kk))
      as (Hsp16 & Htgt16 & Hibd16 & Halc16).
    (* the ledger figures *)
    assert (Hnw5 : (5 <= nw)%nat).
    { destruct Hspend as [Hs1 _]. rewrite (su_wi_cost kk) in Hs1. lia. }
    (* the range clause, specialised to the record's sixteen bytes *)
    assert (Hrng16 : forall x : nat,
              file_byte data' x
              = if decide ((16 * kk <= x)%nat /\ (x < 16 * kk + 16)%nat)
                then dirent_bytes dirent_zero !!! (x - 16 * kk)%nat
                else file_byte datd x).
    { intro x. rewrite (Hrng x). rewrite Hdist0.
      destruct (Nat.lt_ge_cases x (16 * kk)%nat) as [Hlo | Hge].
      - rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
        rewrite decide_False; [reflexivity | lia].
      - destruct (Nat.lt_ge_cases x (16 * kk + 16)%nat) as [Hin | Hhi].
        + rewrite decide_True; [| lia]. rewrite decide_True; [| lia].
          rewrite (Hwr eq_refl (x - 16 * kk)%nat ltac:(lia)).
          rewrite (su_dz_byte (x - 16 * kk)%nat ltac:(lia)). reflexivity.
        + rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
          rewrite decide_False; [reflexivity | lia]. }
    (* the three data' facts *)
    assert (Hz' : dir_inum data' kk = bv_0 16).
    { rewrite (dir_inum_of_two data' kk dirent_zero); [exact su_dz_inum |].
      intros jq Hjq. rewrite (Hrng16 (16 * kk + jq)%nat).
      rewrite decide_True; [| lia].
      replace (16 * kk + jq - 16 * kk)%nat with jq by lia. reflexivity. }
    assert (Hagree : forall q : nat, q <> kk ->
              dir_inum data' q = dir_inum datd q).
    { intros q Hq. unfold dir_inum.
      rewrite (Hrng16 (16 * q)%nat) (Hrng16 (16 * q + 1)%nat).
      rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
      reflexivity. }
    assert (Hnm' : forall q : nat, q <> kk ->
              bname 14 (dir_name data' q) = bname 14 (dir_name datd q)).
    { intros q Hq. unfold bname. f_equal.
      apply bview_ext. intros jq Hjq. unfold dir_name.
      rewrite (Hrng16 (16 * q + 2 + jq)%nat).
      rewrite decide_False; [reflexivity | lia]. }
    (* [dp]'s pure re-park facts at the flushed record *)
    assert (Hiok' : inode_ok fsc_cov fsc_logst dnW bm' data').
    { unfold inode_ok. split_and!.
      - exact Hwf'.
      - exact Hcov'.
      - exact Haddr'v.
      - rewrite Hty'v Htydz. unfold T_DIR_z. lia.
      - exact (Hcapp Hszcap).
      - exact Hhz'.
      - exact (Hszp Hszdd). }
    assert (Hdok' : dir_ok icfg_nib dnW data').
    { intros _ k Hk Hlvk. rewrite Hsz'v in Hk.
      destruct (decide (k = kk)) as [-> | Hne].
      - exfalso. apply Hlvk. exact Hz'.
      - rewrite (Hagree k Hne).
        apply (Hinums k Hk). unfold dir_live.
        rewrite <- (Hagree k Hne). exact Hlvk. }
    assert (Hddix' : dir_dots_ix (bv_unsigned dinum) dnW data').
    { intros _ _. rewrite Hsz'v. split_and!.
      - exact Hnrec2.
      - unfold dir_live. rewrite (Hagree 0%nat Hkk0'). exact Hlv0.
      - rewrite (Hagree 0%nat Hkk0'). exact Hself0.
      - rewrite (Hnm' 0%nat Hkk0'). exact Hname0.
      - unfold dir_live. rewrite (Hagree 1%nat Hkk1'). exact Hlv1.
      - rewrite (Hnm' 1%nat Hkk1'). exact Hname1. }
    (* the RECORD-ONLY facts at the zeroed record (durable-disk
       2b-inode-3): [wi_dinode] moved neither the type, the count nor the
       size, so all three ride. *)
    assert (Hrl_data' : inode_rec_local dnW).
    { apply (inode_rec_local_same_type dnd dnW Hrl_datd Hty'v).
      - rewrite Hnl'v. exact (proj1 (proj2 Hrl_datd)).
      - intros Hd. rewrite Hsz'v. apply (proj2 (proj2 Hrl_datd)).
        rewrite -Hty'v. exact Hd. }
    assert (Hnlz' : bv_unsigned (di_nlink dnW) <> 0)
      by (rewrite Hnl'v; exact Hdplive).
    assert (Hdoc' : dir_orphan_clean dnW data')
      by exact (dir_orphan_clean_live dnW data' Hnlz').
    (* UNIQUENESS across the zeroing: it only REMOVES a live name, and the
       size does not move ([Hsz'v]). *)
    assert (Hduq' : dir_uniq dnW data')
      by exact (dir_uniq_zero dnd dnW datd data' kk Hty'v
                  ltac:(rewrite Hsz'v; lia)
                  (conj Hz' (conj Hagree Hnm')) Hduq).
    (* ===== VERDICT #1: the entry gives up its unit, CALLER-side ===== *)
    assert (Hkknotdot : dir_bname datd kk <> DOT).
    { rewrite /dir_bname Hkkname. intro Hc. apply Hnotdot.
      rewrite Hc DOT_dot_name. reflexivity. }
    (* ...and the counting RA's half of the same move (durable-disk
       2b-inode-5): the entry that is being zeroed gives up its token, and
       that token is exactly what pays for [ip->nlink--] below. *)
    assert (Hkknotdd : dir_bname datd kk <> DOTDOT).
    { rewrite /dir_bname Hkkname. intro Hc. apply Hnotdd.
      rewrite Hc DOTDOT_dotdot. reflexivity. }
    iDestruct (dlinks_open with "Hdlnkd")
      as "(%Dd & [%Hdokd %Hxactd] & Hetkd)".
    iDestruct (ent_toks_unlink (fs_gamma_L fsc_fs) (bv_unsigned dinum)
                 dnd dnW bmd bm' datd data' kk Dd
                 Hkklt Hkklive Hnotself Hkknotdot Hkknotdd Hnotself (Hduq Htydz)
                 (conj Hz' (conj Hagree Hnm')) Htydz Hdplive Hnlz'
                 Hty'v Hsz'v Hhzd Hhz' Hszcap
                 with "Hetkd") as "[(%uty & Htoken & %Hutyd) Hetkd]".
    (* (D1) AT THE FILE ARM (durable-disk G5).  The zeroed record's fragment
       carries its TARGET'S register value, and the region says that value
       matches the target's record -- which this arm's payload knows is not
       a directory.  So the removed name was never MARKED: the marker set
       does not move, and neither does [dp]'s count.  This is the same
       reading the old ledger's flavour bit gave, taken off the type
       register instead. *)
    iApply fupd_wp.
    iEval (rewrite -(su_zext32_unsigned (dir_inum datd kk))) in "Htoken".
    iMod (IregLinkNz.ireg_tok_nz ⊤ fsc_ireg fsc_fs icfg_ist icfg_nib
            (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) dni uty
            ltac:(solve_ndisj) Hinb with "Hireg Hdiati Htoken")
      as "([%Hnzi %Hokty] & Hdiati & Htoken)".
    iEval (rewrite (su_zext32_unsigned (dir_inum datd kk))) in "Htoken".
    iModIntro.
    assert (HnotD : dir_bname datd kk ∉ Dd).
    { intros Hin. rewrite (bool_decide_eq_true_2 _ Hin) in Hutyd.
      rewrite Hutyd /InodeRegion.ireg_reg_ok in Hokty.
      apply Htynzi. rewrite Hokty /InodeRegion.ireg_dir_ty /T_DIR_z //. }
    assert (Hentsd : dir_entries (era_node dnW bm' data')
                     = delete (dir_bname datd kk)
                         (dir_entries (era_node dnd bmd datd)))
      by exact (dir_entries_unlink_eq dnd dnW bmd bm' datd data' kk
                  Hkklt Hkklive (Hduq Htydz)
                  (conj Hz' (conj Hagree Hnm')) Htydz Hty'v Hsz'v
                  Hhzd Hhz' Hszcap).
    (* PERFORMANCE (durable-notes): [set_solver] walks the WHOLE ambient
       context, which at this depth is several hundred machine-word and
       map hypotheses.  Every set fact in this lane's new blocks is a
       one-lemma step, so none of them calls it. *)
    assert (HDdiff : Dd ∖ {[dir_bname datd kk]} = Dd)
      by (apply leibniz_equiv, difference_disjoint,
                disjoint_singleton_r; exact HnotD).
    iEval (rewrite HDdiff) in "Hetkd".
    assert (Hdokd' : FsStateInode.ent_dset_ok (era_node dnW bm' data') Dd)
      by exact (FsStateInode.ent_dset_ok_delete _ _ (dir_bname datd kk) Dd
                  Hentsd HnotD Hdokd).
    assert (Hxactd' : FsStateInode.node_exact (era_node dnW bm' data') Dd).
    { apply (FsStateInode.node_exact_cong (era_node dnd bmd datd)
               (era_node dnW bm' data') Dd).
      - rewrite /fn_is_dir /fn_type !era_node_rec Hty'v //.
      - rewrite /fn_nlink !era_node_rec Hnl'v //.
      - exact Hxactd. }
    iDestruct (dlinks_intro _ _ _ _ _ Dd Hdokd' Hxactd'
                 with "Hetkd") as "Hdlnkd".
    (* [dp]'s bundle, repacked at the flushed record *)
    iDestruct "Hmapd" as "[Haddrsd Hindd]".
    (* THE MOVER (namei-pinned-lookup.md §9 W3, sys_unlink's row): the
       memset+writei zeroed this directory's record, so the hold moves with
       the bytes.  The fragment is WHOLE, so this is one free own-update --
       [dir_view_zero] states the DELTA and is the client's business
       (N-3/N-4), not the carrier's. *)
    iApply fupd_wp.
    (* ...and the ERA's abstract value with them (durable-disk 2b-inode-3):
       [ireg_top_retag] opens [ftopN] alone. *)
    (* THE RETAG OWES THE ROW (durable-disk lane A): the four facts are the
       re-pack's own, already named -- a zeroed entry leaves the directory
       well-formed (its dots are untouched and its names stay unique). *)
    (* ===== INSTANT 1: THE PARENT'S ROW =====
       The zeroing is the linearization instant for the ENTRY half of the
       delta, and the fire REPLACES the [ireg_top_retag] the landed walk
       calls here: same premise, same payout, plus the caller's two phases
       inside the one [ftopN] critical section.  It reads [ip]'s row too --
       [unl_pre]'s last three conjuncts -- off the fragment W3 locked and
       this block still holds, which is what lets the two instants be read
       as one delta ([delta_unlink_split]).  On THIS arm the target is not a
       directory, so [unl_dec] is 0 and the parent's count does not move. *)
    assert (Hdirdp : fn_is_dir (era_node dnd bmd datd) = true)
      by exact (mkf_era_is_dir dnd bmd datd Htydz).
    assert (Hipnd : fn_is_dir (era_node dni bmi dati) = false)
      by exact (su_au_era_not_dir dni bmi dati Htynzi).
    assert (Hentd : dir_entries (era_node dnd bmd datd) !! dir_bname datd kk
                    = Some (bv_unsigned (zero_extend' 32 (dir_inum datd kk : mword 16)
                                        : mword 32))).
    { rewrite (dir_entries_era_node dnd bmd datd Hhzd Hszcap)
              (bool_decide_eq_true_2 _ Htydz) su_zext32_unsigned.
      exact (dir_view_live datd _ kk (Hduq Htydz) Hkklt Hkklive). }
    iMod (uf_uent_fire fsc_fs ⊤ (DfracOwn 1) Phient
            (bv_unsigned dinum) (bv_unsigned (zero_extend' 32 (dir_inum datd kk : mword 16)
                                        : mword 32))
            (dir_bname datd kk) 0%nat
            (era_node dnd bmd datd) (era_node dnW bm' data')
            (era_node dni bmi dati)
            ltac:(solve_ndisj)
            (inode_local_of_ok_rec (bv_unsigned dinum) fsc_cov fsc_logst dnW bm'
               data' Hiok' Hrl_data' Hduq' Hddix')
            Hdirdp Hentd Hkknotdot Hkknotdd
            (su_au_nl1 dnd bmd datd Hdplive)
            (su_au_nl1 dni bmi dati Hnlzi)
            (su_au_nondir_node (era_node dni bmi dati) Hipnd)
            (su_au_nondir_dec (era_node dni bmi dati) Hipnd)
            (su_au_parent_row_era dnd dnW bmd bm' datd data'
               (dir_bname datd kk) 0%nat Htydz Hty'v
               ltac:(rewrite /fn_nlink !era_node_rec Hnl'v; lia) Hentsd)
            with "[] Hcent Htop Htopi") as "(Htop & Htopi & Hfire1)";
      [iApply (ireg_inv_ftop with "Hireg") |].
    iDestruct "Hfire1" as (av0) "(%Hpre0 & Hent)".
    iModIntro.
    iAssert (ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kd dinum dnW bm')
      with "[Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop]"
      as "Hloadd".
    { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body.
          iExists data'.
      rewrite Hdn0W.
      iFrame "Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop".
      iPureIntro. split_and!;[exact Hiok' | exact Hrl_data' | exact Hdok' | exact Hddix' | exact Hdoc'
        | exact Hduq']. }
    iAssert (ity_shot gyd (di_type dnW)) as "#Hshotd2".
    { rewrite Hty'v. iExact "Hshotd". }
    iClear "Hshotd".
    (* ===== +0xae lh a4,68(s2) -- ip->type ===== *)
    iEval (rewrite /inode_meta) in "Hmetai".
    iDestruct "Hmetai" as "(Hityi & Himai & Himii & Hinli & Hiszi)".
    iEval (rewrite /i_type) in "Hityi".
    iApply (wp_lh_s_sconf (CID := D15) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0xae)) Ra4 Rs2
              (mword_of_int 68 : mword 12) C1 (K - 30)%nat
              (di_type dni : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hityi]").
    { iApply (suli_0ae with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ HC1regs)).
      iExact "Hityi". }
    iIntros (D16 Hd16) "Hcg Hpc Hityi".
    iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ HC1regs)) in "Hityi".
    iAssert (inode_meta (ientry ks) dni)
      with "[Hityi Himai Himii Hinli Hiszi]" as "Hmetai".
    { rewrite /inode_meta /i_type. iFrame. }
    set (C2 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_type dni : mword 16))]> C1).
    assert (HC2a4 : (C2 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dni : mword 16) : mword 64))
      by (rewrite /C2; apply upd_eq).
    assert (HC2regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C2)
      by (rewrite /C2; apply su_regs_caller; [exact Hcsa4 | exact HC1regs]).
    assert (Hppb2 : add_vec_int (mword_of_int (SU + 0xae) : mword 64) 4
                    = mword_of_int (SU + 0xb2)) by pcw.
    iEval (rewrite Hppb2) in "Hpc".
    (* ===== +0xb2 c.li a5,1 ===== *)
    iApply (wp_cli_s_sconf (CID := D16) (mword_of_int (SU + 0xb2)) Ra5
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              C2 (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_0b2 with "Htext"). }
    iIntros (D17 Hd17) "Hcg Hpc".
    set (C3 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> C2).
    assert (HC3a4 : (C3 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dni : mword 16) : mword 64))
      by (rewrite /C3 upd_ne; [exact HC2a4 | nz]).
    assert (HC3a5 : (C3 !!! Regidx Ra5 : mword 64) = (mword_of_int 1 : mword 64))
      by (rewrite /C3; apply upd_eq).
    assert (HC3regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C3)
      by (rewrite /C3; apply su_regs_caller; [exact Hcsa5 | exact HC2regs]).
    assert (Hppb4 : add_vec_int (mword_of_int (SU + 0xb2) : mword 64) 2
                    = mword_of_int (SU + 0xb4)) by pcw.
    iEval (rewrite Hppb4) in "Hpc".
    (* ===== +0xb4 beq a4,a5 -- the second T_DIR test FALLS (this arm) ===== *)
    iApply (wp_beq_fall_s_sconf (CID := D17) (mword_of_int (SU + 0xb4))
              (mword_of_int 146 : mword 13) Ra5 Ra4 C3 (K - 30)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HC3a4 HC3a5;
                    exact (su_tdir_ne _ (su_tdir_z_ne _ Htynzi)))
              with "Hcg Hpc []").
    { iApply (suli_0b4 with "Htext"). }
    iIntros (D18 Hd18) "Hcg Hpc".
    assert (Hppb8 : add_vec_int (mword_of_int (SU + 0xb4) : mword 64) 4
                    = mword_of_int (SU + 0xb8)) by pcw.
    iEval (rewrite Hppb8) in "Hpc".
    (* ===== +0xb8 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := D18) (mword_of_int (SU + 0xb8)) Ra0 Rs1 C3
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0b8 with "Htext"). }
    iIntros (D19 Hd19) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (C4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (C3 !!! Regidx Rs1))]> C3).
    assert (HC4a0 : (C4 !!! Regidx Ra0 : mword 64) = ientry kd).
    { etransitivity; [rewrite /C4; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s1 _ _ _ _ _ _ HC3regs). }
    assert (HC4regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C4)
      by (rewrite /C4; apply su_regs_caller; [exact Hcsa0 | exact HC3regs]).
    assert (Hppba : add_vec_int (mword_of_int (SU + 0xb8) : mword 64) 2
                    = mword_of_int (SU + 0xba)) by pcw.
    iEval (rewrite Hppba) in "Hpc".
    (* ===== +0xba jal ra,iunlockput(dp) -- CREDITED off the trio ===== *)
    iApply (wp_jal_s_sconf (CID := D19) (mword_of_int (SU + 0xba)) Rra
              (mword_of_int 2089990 : mword 21) C4 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0ba with "Htext"). }
    iIntros (D20 Hd20) "Hcg Hpc".
    set (C5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xba) : mword 64) 4)]> C4).
    assert (Hjup : add_vec (mword_of_int (SU + 0xba) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089990 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HC5ra : (C5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xba) : mword 64) 4)
      by (rewrite /C5; apply upd_eq).
    assert (HC5a0 : (C5 !!! Regidx Ra0 : mword 64) = ientry kd)
      by (rewrite /C5 upd_ne; [exact HC4a0 | nz]).
    assert (HC5regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C5)
      by (rewrite /C5; apply su_regs_caller; [exact Hcsra | exact HC4regs]).
    iDestruct (cpu_own_transport D13 D20 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (su_esc_acc kd Hkd with "Hescrows")
      as "#Hescd".
    iDestruct (log_opS_named with "HopS") as (e0) "HopS".
    (* [dp]'s arm comes off at its own release (durable-disk B''-tx2) *)
    (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
       goes in and the quarter it parked comes back in the post, so no
       bundleless out-state stands across the call. *)
    iDestruct (off_rows_to_dep with "Hoffrd") as "Hoffdd".
    iApply (Iunlockput.wp_iunlockput_dep_gen (CID := D20) gs jx gl pd pav
              pu gild gisld
 kd qdi sd gyd loyd tlyd
              (DepTx sd icfg_dev dinum gyd loyd t (1/4)%Qp) dinum dnW bm'
              nw Sbw false true false e0 _ _ pid (DfracOwn (1/4)) dqb dqs
              C5 (K - 30)%nat eb b lks
              (us_upt U P1) ltac:(exact Kiup) eq_refl Hkd ltac:(discriminate)
              ltac:(intros _; exact Hibd16)
              Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hdiblk Hdiblog Hdinb Hcovb
              ltac:(unfold iput_units; lia) Hj Hgl HC5a0 (Hlb "log"%string) eq_refl
              with "Hcg Hown [] [] Htext Hdata Hpc Hpanenv Hbio Hlog Hitab Hitinv
                    Hescd Hireg Hropen Hslkd Hslkdq [//] Hflyd Hclaimsyd Hdepd Hoffdd Hidevd Hiinumd
                    Hivalidd Hloadd Hshotd2 Hfrz [$Hkeepd $Hrud] Hsbb Hsbi Hbmres Hpidq
                    Hprocs Hdev Hgeo Hdlk Hbsl [] HopS").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (D21 Hd21 mup n2 Sb2 wg)
      "%Hcsup Hcg Hown _ _ Hpc Hpidq Hsbb Hsbi Hbsl %Hsb2 %Hwg
       %Hwgc %Hn2 HopS Hisl Htq1".
    assert (Hpcbe : ret_pc (C5 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xbe)) by (rewrite HC5ra; pcw).
    iEval (rewrite Hpcbe) in "Hpc".
    assert (Hupregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) mup)
      by exact (su_regs_cs m sp0 _ _ _ C5 mup Hcsup HC5regs).
    assert (Hn24 : (4 <= n2)%nat).
    { destruct Hn2 as [Hn2a Hn2b].
      exact (su_iunlockput_from5 wg nw n2 Hnw5 Hn2a). }
    (* ===== +0xbe lhu a5,74(s2) -- ip->nlink ===== *)
    iEval (rewrite /inode_meta) in "Hmetai".
    iDestruct "Hmetai" as "(Hityi & Himai & Himii & Hinli & Hiszi)".
    iEval (rewrite /i_nlink) in "Hinli".
    iApply (wp_lhu_s_sconf (CID := D21) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0xbe)) Ra5 Rs2
              (mword_of_int 74 : mword 12) mup (K - 30)%nat
              (di_nlink dni : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hinli]").
    { iApply (suli_0be with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ Hupregs)).
      iExact "Hinli". }
    iIntros (D22 Hd22) "Hcg Hpc Hinli".
    iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ Hupregs)) in "Hinli".
    set (C6 := <[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (di_nlink dni : mword 16))]> mup).
    assert (HC6a5 : (C6 !!! Regidx Ra5 : mword 64)
                    = (zero_extend' 64 (di_nlink dni : mword 16) : mword 64))
      by (rewrite /C6; apply upd_eq).
    assert (HC6regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C6)
      by (rewrite /C6; apply su_regs_caller; [exact Hcsa5 | exact Hupregs]).
    assert (Hppc2 : add_vec_int (mword_of_int (SU + 0xbe) : mword 64) 4
                    = mword_of_int (SU + 0xc2)) by pcw.
    iEval (rewrite Hppc2) in "Hpc".
    (* ===== +0xc2 c.addiw a5,a5,-1 ===== *)
    iApply (wp_caddiw_s_sconf (CID := D22) (mword_of_int (SU + 0xc2)) Ra5
              (mword_of_int 63 : mword 6) C6 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0c2 with "Htext"). }
    iIntros (D23 Hd23) "Hcg Hpc".
    set (C7 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (rget C6 Ra5)
                        (sign_extend' 64
                           (sign_extend' 12 (mword_of_int 63 : mword 6))))
                     31 0))]> C6).
    assert (HC7a5 : (C7 !!! Regidx Ra5 : mword 64)
                    = sign_extend' 64 (subrange_vec_dec
                        (add_vec
                           (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                           (sign_extend' 64
                              (sign_extend' 12 (mword_of_int 63 : mword 6))
                            : mword 64)) 31 0)).
    { rewrite /C7 upd_eq. rgne. rewrite HC6a5. reflexivity. }
    assert (HC7regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C7)
      by (rewrite /C7; apply su_regs_caller; [exact Hcsa5 | exact HC6regs]).
    assert (Hppc4 : add_vec_int (mword_of_int (SU + 0xc2) : mword 64) 2
                    = mword_of_int (SU + 0xc4)) by pcw.
    iEval (rewrite Hppc4) in "Hpc".
    (* ===== +0xc4 sh a5,74(s2) -- the decrement lands ===== *)
    iApply (wp_sh_s_sconf (CID := D23) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0xc4))
              Ra5 Rs2 (mword_of_int 74 : mword 12) C7 (K - 30)%nat
              (di_nlink dni : mword 16) b with "Hcg Hpc [] [Hinli]").
    { iApply (suli_0c4 with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ HC7regs)).
      iExact "Hinli". }
    iIntros (D24 Hd24) "Hcg Hpc Hinli".
    iEval (rgne; rgne;
           rewrite (su_regs_s2 _ _ _ _ _ _ HC7regs) HC7a5) in "Hinli".
    (* the stored halfword, named; the record it makes is [su_setnl] *)
    iAssert (inode_meta (ientry ks)
               (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))))
      with "[Hityi Himai Himii Hinli Hiszi]" as "Hmetai".
    { rewrite /inode_meta /su_setnl /= /i_nlink. iFrame. }
    assert (Hdecr : bv_unsigned (di_nlink dni)
                    = bv_unsigned (di_nlink (su_setnl dni
                        (trunc16 (sign_extend' 64 (subrange_vec_dec
                           (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                                     : mword 64)
                              (sign_extend' 64
                                 (sign_extend' 12 (mword_of_int 63 : mword 6))
                               : mword 64)) 31 0))))) + 1).
    { rewrite su_setnl_nlink. exact (su_nlink_decr (di_nlink dni) Hnlzi). }
    assert (Hppc8 : add_vec_int (mword_of_int (SU + 0xc4) : mword 64) 4
                    = mword_of_int (SU + 0xc8)) by pcw.
    iEval (rewrite Hppc8) in "Hpc".
    (* ===== +0xc8 c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (CID := D24) (mword_of_int (SU + 0xc8)) Ra0 Rs2 C7
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0c8 with "Htext"). }
    iIntros (D25 Hd25) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (C8 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (C7 !!! Regidx Rs2))]> C7).
    assert (HC8a0 : (C8 !!! Regidx Ra0 : mword 64) = ientry ks).
    { etransitivity; [rewrite /C8; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s2 _ _ _ _ _ _ HC7regs). }
    assert (HC8regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C8)
      by (rewrite /C8; apply su_regs_caller; [exact Hcsa0 | exact HC7regs]).
    assert (Hppca : add_vec_int (mword_of_int (SU + 0xc8) : mword 64) 2
                    = mword_of_int (SU + 0xca)) by pcw.
    iEval (rewrite Hppca) in "Hpc".
    (* ===== +0xca jal ra,iupdate(ip) -- the LEFT receipt ===== *)
    iApply (wp_jal_s_sconf (CID := D25) (mword_of_int (SU + 0xca)) Rra
              (mword_of_int 2089198 : mword 21) C8 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0ca with "Htext"). }
    iIntros (D26 Hd26) "Hcg Hpc".
    set (C9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xca) : mword 64) 4)]> C8).
    assert (Hjiu : add_vec (mword_of_int (SU + 0xca) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089198 : mword 21))
                   = mword_of_int KernelSyms.iupdate) by pcw.
    iEval (rewrite Hjiu) in "Hpc".
    assert (HC9ra : (C9 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xca) : mword 64) 4)
      by (rewrite /C9; apply upd_eq).
    assert (HC9a0 : (C9 !!! Regidx Ra0 : mword 64) = ientry ks)
      by (rewrite /C9 upd_ne; [exact HC8a0 | nz]).
    assert (HC9regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C9)
      by (rewrite /C9; apply su_regs_caller; [exact Hcsra | exact HC8regs]).
    assert (Htynzi0 : bv_unsigned (di_type dni) <> 0).
    { destruct Hioki as (_ & _ & _ & Hc & _). exact Hc. }
    assert (Haddri : di_addrs dni = bm_cells bmi).
    { destruct Hioki as (_ & _ & Hc & _). exact Hc. }
    assert (Hdirleni : length (bm_dir bmi) = NDIRECT).
    { destruct Hioki as (Hc & _). exact (blkmap_wf_dir_len fsc_cov fsc_logst bmi Hc). }
    destruct n2 as [| c2]; [exfalso; lia |].
    iDestruct (su_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    iDestruct (cpu_own_transport D21 D26 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    (* the spent unit, at the region's own index spelling *)
    iEval (rewrite -(su_zext32_unsigned (dir_inum datd kk))) in "Htoken".
    iApply (Iupdate.wp_iupdate_unlink (CID := D26) gs jx gl pd pav pu
 (ientry ks)
              (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
              (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                 (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                           : mword 64)
                    (sign_extend' 64
                       (sign_extend' 12 (mword_of_int 63 : mword 6))
                     : mword 64)) 31 0))))
              dni bmi c2 (Sb2 : gset Z) false uty pid
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
              C9 (K - 30)%nat eb b lks
              (us_upt U P1) ltac:(exact Kiupd) ltac:(discriminate) Hgeom Hist0 Hiblki
              Hiblogi Hinb (su_setnl_type_stable dni _)
              ltac:(rewrite su_setnl_type; exact Htynzi0)
              ltac:(exact Hdecr)
              ltac:(rewrite su_setnl_addrs; exact Haddri)
              Hdirleni Hj Hgl HC9a0 Heb (Hlb "log"%string)
              with "Hcg Hown Htext Hdata Hpc Hpanenv Hbio Hlog Hidevi Hiinumi Hmetai
                    [Haddrsi Hindi] Hsbi Hireg Hdiati [Htoken] Hpidq
                    Hprocs Hdev Hgeo Hdlk Hbs2 HopS").
    { rewrite /inode_map. iFrame "Haddrsi Hindi". }
    { (* the pile is ONE unit here: the target is not a directory, so
         [ireg_dot_delta] is one. *)
      rewrite su_setnl_type
        (InodeRegion.ireg_dot_delta_not_dir (bv_unsigned (di_type dni)) _
           ltac:(rewrite /InodeRegion.ireg_dir_ty; rewrite /T_DIR_z in Htynzi;
                 exact Htynzi))
        FsStateLink.link_reps_1. iExact "Htoken". }
    iIntros (D27 Hd27 miu)
      "%Hcsiu Hcg Hown Hpc Hpidq Hidevi Hiinumi Hmetai Hmapi Hsbi Hdiati
       Hbs2 HopS".
    assert (Hpcce : ret_pc (C9 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xce)) by (rewrite HC9ra; pcw).
    iEval (rewrite Hpcce) in "Hpc".
    assert (Hiuregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) miu)
      by exact (su_regs_cs m sp0 _ _ _ C9 miu Hcsiu HC9regs).
    (* hm: the bslot unit peeled for iupdate must come back *)
    (* ===== +0xce c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (CID := D27) (mword_of_int (SU + 0xce)) Ra0 Rs2 miu
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0ce with "Htext"). }
    iIntros (D28 Hd28) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (E1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (miu !!! Regidx Rs2))]> miu).
    assert (HE1a0 : (E1 !!! Regidx Ra0 : mword 64) = ientry ks).
    { etransitivity; [rewrite /E1; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s2 _ _ _ _ _ _ Hiuregs). }
    assert (HE1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) E1)
      by (rewrite /E1; apply su_regs_caller; [exact Hcsa0 | exact Hiuregs]).
    assert (Hppd0 : add_vec_int (mword_of_int (SU + 0xce) : mword 64) 2
                    = mword_of_int (SU + 0xd0)) by pcw.
    iEval (rewrite Hppd0) in "Hpc".
    (* ===== +0xd0 jal ra,iunlockput(ip) -- credited off iupdate's own
       [∪ {IBLOCK ip}] ===== *)
    iApply (wp_jal_s_sconf (CID := D28) (mword_of_int (SU + 0xd0)) Rra
              (mword_of_int 2089968 : mword 21) E1 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0d0 with "Htext"). }
    iIntros (D29 Hd29) "Hcg Hpc".
    set (E2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xd0) : mword 64) 4)]> E1).
    assert (Hjup2 : add_vec (mword_of_int (SU + 0xd0) : mword 64)
                      (sign_extend' 64 (mword_of_int 2089968 : mword 21))
                    = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup2) in "Hpc".
    assert (HE2ra : (E2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xd0) : mword 64) 4)
      by (rewrite /E2; apply upd_eq).
    assert (HE2a0 : (E2 !!! Regidx Ra0 : mword 64) = ientry ks)
      by (rewrite /E2 upd_ne; [exact HE1a0 | nz]).
    assert (HE2regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) E2)
      by (rewrite /E2; apply su_regs_caller; [exact Hcsra | exact HE1regs]).
    (* [ip]'s bundle, repacked at the decremented record *)
    iDestruct "Hmapi" as "[Haddrsi Hindi]".
    iAssert (dlinks fsc_fs (bv_unsigned (zero_extend' 32
                 (dir_inum datd kk : mword 16) : mword 32))
               (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi dati)
      as "Hdlnki2".
    { iApply dlinks_not_dir. rewrite su_setnl_type. exact Htynzi. }
    (* ...and the ERA's abstract value follows the count (2b-inode-3). *)
    (* THE RETAG OWES THE ROW (durable-disk lane A): a lowered link count
       leaves the inode well-formed, and these are the re-pack's own four
       facts.  A directory that reaches nlink = 0 is an ORPHAN, whose dot
       clauses [FsStateInode.inode_local] guards away. *)
    assert (Hlocdec : inode_local
              (bv_unsigned (zero_extend' 32 (dir_inum datd kk : mword 16)
                            : mword 32))
              (era_node (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                    (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                              : mword 64)
                       (sign_extend' 64
                          (sign_extend' 12 (mword_of_int 63 : mword 6))
                        : mword 64)) 31 0)))) bmi dati)).
    { apply (inode_local_of_ok_rec _ fsc_cov fsc_logst _ bmi dati).
      - exact (su_setnl_inode_ok fsc_cov fsc_logst dni bmi dati _ Hioki).
      - apply (inode_rec_local_same_type dni _ Hrl_dati
                 (su_setnl_type dni _));
          [ exact (su_dec_short _ _ Hdecr (proj1 (proj2 Hrl_dati)))
          | exact (proj2 (proj2 Hrl_dati)) ].
      - apply dir_uniq_not_dir. rewrite su_setnl_type. exact Htynzi.
      - apply dir_dots_ix_not_dir. rewrite su_setnl_type. exact Htynzi. }
    iApply fupd_wp.
    (* ===== INSTANT 2: THE TARGET'S ROW =====
       [wp_iupdate_unlink] has flushed [ip] at its lowered count and spent
       the link token; this is the abstract half of the same move, and it is
       a SECOND instant because [iunlockput(dp)] ran between the two and
       [ftopN] had to close and reopen (the statement's banner).  The
       pre-state row it hands back is the one the ret-0 arm pins -- true
       because [ip]'s fragment has been in this walk's custody since W3. *)
    iMod (uf_utgt_fire fsc_fs ⊤ Phitgt
            (bv_unsigned (zero_extend' 32 (dir_inum datd kk : mword 16)
                          : mword 32))
            (era_node dni bmi dati)
            (era_node (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi dati)
            ltac:(solve_ndisj) Hlocdec
            (su_au_nl1 dni bmi dati Hnlzi)
            (uf_nlink_row dni (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi dati
               eq_refl eq_refl eq_refl eq_refl
               (su_au_nlink_down dni (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi bmi dati dati Hnlzi
                  ltac:(lia)))
            with "[] Hctgt Htopi") as "(Htopi & Hfire2)";
      [iApply (ireg_inv_ftop with "Hireg") |].
    iDestruct "Hfire2" as (av1) "(%Hrow1 & Htgt)".
    iModIntro.
    iAssert (ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst ks
               (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
               (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi)
      with "[Hdlnki2 Hdiati Hmetai Haddrsi Hindi Hblocksi Htopi]" as "Hloadi".
    { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body. iExists dati.
      iSplit; [iPureIntro; exact (su_setnl_inode_ok fsc_cov fsc_logst dni bmi dati _ Hioki) |].
      (* [su_setnl] moves the COUNT alone, so the type and the size ride;
         the new count is one BELOW one the region already bounded, and the
         directory clause is vacuous here (durable-disk 2b-inode-3). *)
      iSplit; [iPureIntro;
               apply (inode_rec_local_same_type dni _ Hrl_dati
                        (su_setnl_type dni _));
               [ exact (su_dec_short _ _ Hdecr (proj1 (proj2 Hrl_dati)))
               | exact (proj2 (proj2 Hrl_dati)) ] |].
      iSplit; [iPureIntro; exact (su_setnl_dir_ok icfg_nib dni dati _ Hdoki) |].
      iSplit; [iPureIntro; apply dir_dots_ix_not_dir;
               rewrite su_setnl_type; exact Htynzi |].
      iSplit; [iPureIntro; apply dir_orphan_clean_not_dir;
               rewrite su_setnl_type; exact Htynzi |].
      iSplit; [iPureIntro; apply dir_uniq_not_dir;
               rewrite su_setnl_type; exact Htynzi |].
      iSplitL "Hdlnki2"; [iExact "Hdlnki2" |].
      iSplitL "Hdiati"; [iExact "Hdiati" |].
      iSplitL "Hmetai"; [iExact "Hmetai" |].
      iSplitL "Haddrsi"; [iExact "Haddrsi" |].
      iSplitL "Hindi"; [iExact "Hindi" |].
      iSplitL "Hblocksi"; [iExact "Hblocksi" | iExact "Htopi"]. }
    iAssert (ity_shot gyi (di_type (su_setnl dni (trunc16 (sign_extend' 64
               (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))))) as "#Hshoti2".
    { rewrite su_setnl_type. iExact "Hshoti". }
    iDestruct (cpu_own_transport D27 D29 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (su_esc_acc ks Hks with "Hescrows")
      as "#Hesci".
    iDestruct (log_opS_named with "HopS") as (e1) "HopS".
    pose (dni2 := su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
              (add_vec (zero_extend' 64 (di_nlink dni : mword 16) : mword 64)
                 (sign_extend' 64
                    (sign_extend' 12 (mword_of_int 63 : mword 6))))
              31 0)))).
    assert (Hcrb2 : false = true ->
              fsc_bmapstart ∈ (Sb2 ∪ {[IBLOCK (zero_extend' 32
                (dir_inum datd kk : mword 16) : mword 32) icfg_ist]})).
    { intros Hfalse. discriminate Hfalse. }
    assert (Hcru2 : true = true ->
              IBLOCK (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
                icfg_ist ∈ (Sb2 ∪ {[IBLOCK (zero_extend' 32
                  (dir_inum datd kk : mword 16) : mword 32) icfg_ist]})).
    { intros _. apply elem_of_union_r, elem_of_singleton. reflexivity. }
    assert (Hnu2 : (iput_units <= c2)%nat).
    { unfold iput_units. lia. }
    (* ...and [ip]'s at its own *)
    (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
       goes in and the quarter it parked comes back in the post, so no
       bundleless out-state stands across the call. *)
    iDestruct (off_rows_to_dep with "Hoffri") as "Hoffdi".
    iApply (Iunlockput.wp_iunlockput_dep_gen (CID := D29) gs jx gl pd pav
              pu gili gisli
 ks qsi si gyi loyi tlyi
              (DepTx si icfg_dev
                 (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
                 gyi loyi t (1/4)%Qp)
              (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
              dni2
              bmi c2 (Sb2 ∪ {[IBLOCK (zero_extend' 32
                (dir_inum datd kk : mword 16) : mword 32) icfg_ist]})
              false true false e1 _ _ pid (DfracOwn (1/4)) dqb dqs
              E2 (K - 30)%nat eb b lks
              (us_upt U P1) Kiup eq_refl Hks Hcrb2 Hcru2
              Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblki Hiblogi Hinb Hcovb
              Hnu2 Hj Hgl HE2a0 (Hlb "log"%string) eq_refl
              with "Hcg Hown [] [] Htext Hdata Hpc Hpanenv Hbio Hlog Hitab Hitinv
                    Hesci Hireg Hropen Hslki Hslkiq [//] Hflyi Hclaimsyi Hdepi Hoffdi Hidevi Hiinumi
                    Hivalidi Hloadi Hshoti2 Hfrzi [$Hkeepi $Hrui] Hsbb Hsbi Hbmres Hpidq
                    Hprocs Hdev Hgeo Hdlk [Hbs1 Hbs2] [] HopS").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iApply su_bs3. iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"]. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (D30 Hd30 mip n3 Sb3 wh)
      "%Hcsip Hcg Hown Htce Hcce Hpc Hpidq Hsbb Hsbi Hbsl %Hsb3
       %Hwh %Hwhc %Hn3 HopS Hisl2 Htq2".
    clear Hcrb2 Hcru2 Hnu2 dni2.
    assert (Hpcd4 : ret_pc (E2 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xd4)) by (rewrite HE2ra; pcw).
    iEval (rewrite Hpcd4) in "Hpc".
    assert (Hipregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) mip)
      by exact (su_regs_cs m sp0 _ _ _ E2 mip Hcsip HE2regs).
    (* ===== +0xd4 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := D30) (mword_of_int (SU + 0xd4)) Rra
              (mword_of_int 2092174 : mword 21) mip (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0d4 with "Htext"). }
    iIntros (D31 Hd31) "Hcg Hpc".
    set (E3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xd4) : mword 64) 4)]> mip).
    assert (Hjeo : add_vec (mword_of_int (SU + 0xd4) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092174 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HE3ra : (E3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xd4) : mword 64) 4)
      by (rewrite /E3; apply upd_eq).
    assert (HE3regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) E3)
      by (rewrite /E3; apply su_regs_caller; [exact Hcsra | exact Hipregs]).
    (* ONE hoisted premise for the whole triple, not three inline [ltac:]s.
       [wp_next_chain] is a [repeat match goal], i.e. a whole-context scan, and
       optimization.md's rule is that such a tactic spliced into ARGUMENT
       position is priced by the depth of its call site rather than by its goal
       -- the splice's goal is an evar carrying every variable in scope.  The
       three transports here share one CID pair, so one [assert] serves all
       three and the [eb] form is one rewrite off the [b] form. *)
    assert (Htr1 : b = false \/ proc_addr jx = zero_reg
                     -> (D31 : CPU) = (D30 : CPU)) by wp_next_chain.
    assert (Htre1 : eb = false \/ proc_addr jx = zero_reg
                      -> (D31 : CPU) = (D30 : CPU)) by (rewrite Hbeq; exact Htr1).
    iDestruct (cpu_own_transport D30 D31 0 eb (proc_addr jx) b
                 Htr1 with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport D30 D31 eb (proc_addr jx)
                 Htre1 with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport D30 D31 eb (proc_addr jx)
                 Htre1 with "Hcce") as "Hcce".
    (* both arms are home, so the element is whole again for the [end_op] *)
    iDestruct (log_tx_add icfg_log t (1/2) (1/4) (1/4)
                 (eq_sym Qp.quarter_quarter) with "Htq1 Htq2") as "Htp".
    iDestruct (log_tx_add icfg_log t 1 (1/2) (1/2)
                 (eq_sym Qp.half_half) with "Htp Htx") as "Htw".
    iDestruct (log_tx_full with "Htw") as "Htx".

    iApply (EndOp.wp_end_op_sconf (CID := D31) gs jx gl fsc_uart fsc_disk fsc_dlock pd pav pu fsc_bio
              icfg_log fsc_fs fsc_cov fsc_logst icfg_dev n3 pid (DfracOwn (1/4)) E3 (K - 30)%nat
              eb b lks (us_upt U P1) Keo Hgeom Hj Hgl
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpanenv Hbio Hlog Hseam Hgen
                    Hpidq Hprocs Hdev Hgeo Hdlk [HopS Htx]").
    { iApply (log_opS_op with "HopS Htx"). }
    iIntros (D32 Hd32 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpidq".
    assert (Hpcd8 : ret_pc (E3 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xd8)) by (rewrite HE3ra; pcw).
    iEval (rewrite Hpcd8) in "Hpc".
    assert (Heoregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) meo)
      by exact (su_regs_cs m sp0 _ _ _ E3 meo Hcseo HE3regs).
    (* ===== +0xd8 c.li a0,0 ===== *)
    iApply (wp_cli_s_sconf (CID := D32) (mword_of_int (SU + 0xd8)) Ra0
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              meo (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_0d8 with "Htext"). }
    iIntros (D33 Hd33) "Hcg Hpc".
    set (F1 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int 0 : mword 64)]> meo).
    assert (HF1a0 : (F1 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /F1; apply upd_eq).
    assert (HF1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) F1)
      by (rewrite /F1; apply su_regs_caller; [exact Hcsa0 | exact Heoregs]).
    assert (Hppda : add_vec_int (mword_of_int (SU + 0xd8) : mword 64) 2
                    = mword_of_int (SU + 0xda)) by pcw.
    iEval (rewrite Hppda) in "Hpc".
    (* ===== +0xda c.ldsp s1,216(sp) ===== *)
    assert (Hd3a : add_vec (F1 !!! Regidx csp_rs1 : mword 64)
                     (zero_extend' 64
                        (concat_vec (mword_of_int 27 : mword 6) ('b"000")))
                   = pa_stk sp0 3)
      by (rewrite (su_regs_sp _ _ _ _ _ _ HF1regs); apply su_frm3).
    iApply (wp_cldsp_s_sconf (CID := D33) (mword_of_int (SU + 0xda))
              (mword_of_int 27 : mword 6) Rs1 F1 (K - 30)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf3]").
    { iApply (suli_0da with "Htext"). }
    { iEval (rewrite Hd3a). iExact "Hf3". }
    iIntros (D34 Hd34) "Hcg Hpc Hf3".
    iEval (rewrite Hd3a) in "Hf3".
    set (F2 := <[Regidx Rs1 := regval_into_reg
                  (m !!! Regidx Rs1 : mword 64)]> F1).
    assert (HF2a0 : (F2 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /F2 upd_ne; [exact HF1a0 | nz]).
    assert (HF2regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64) (ientry ks)
                        (pa_stk sp0 8) F2).
    { rewrite /F2.
      exact (su_regs_wr_s1 m sp0 (ientry kd) (m !!! Regidx Rs1 : mword 64)
               (ientry ks) (pa_stk sp0 8) F1 _ eq_refl HF1regs). }
    assert (Hppdc : add_vec_int (mword_of_int (SU + 0xda) : mword 64) 2
                    = mword_of_int (SU + 0xdc)) by pcw.
    iEval (rewrite Hppdc) in "Hpc".
    (* ===== +0xdc c.ldsp s2,208(sp) ===== *)
    assert (Hd4a : add_vec (F2 !!! Regidx csp_rs1 : mword 64)
                     (zero_extend' 64
                        (concat_vec (mword_of_int 26 : mword 6) ('b"000")))
                   = pa_stk sp0 4)
      by (rewrite (su_regs_sp _ _ _ _ _ _ HF2regs); apply su_frm4).
    iApply (wp_cldsp_s_sconf (CID := D34) (mword_of_int (SU + 0xdc))
              (mword_of_int 26 : mword 6) Rs2 F2 (K - 30)%nat
              (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf4]").
    { iApply (suli_0dc with "Htext"). }
    { iEval (rewrite Hd4a). iExact "Hf4". }
    iIntros (D35 Hd35) "Hcg Hpc Hf4".
    iEval (rewrite Hd4a) in "Hf4".
    set (F3 := <[Regidx Rs2 := regval_into_reg
                  (m !!! Regidx Rs2 : mword 64)]> F2).
    assert (HF3a0 : (F3 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /F3 upd_ne; [exact HF2a0 | nz]).
    assert (HF3regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64) (pa_stk sp0 8) F3).
    { rewrite /F3.
      exact (su_regs_wr_s2 m sp0 (m !!! Regidx Rs1 : mword 64) (ientry ks)
               (m !!! Regidx Rs2 : mword 64) (pa_stk sp0 8) F2 _ eq_refl
               HF2regs). }
    assert (Hppde : add_vec_int (mword_of_int (SU + 0xdc) : mword 64) 2
                    = mword_of_int (SU + 0xde)) by pcw.
    iEval (rewrite Hppde) in "Hpc".
    (* ===== +0xde c.ldsp s3,200(sp) ===== *)
    assert (Hd5a : add_vec (F3 !!! Regidx csp_rs1 : mword 64)
                     (zero_extend' 64
                        (concat_vec (mword_of_int 25 : mword 6) ('b"000")))
                   = pa_stk sp0 5)
      by (rewrite (su_regs_sp _ _ _ _ _ _ HF3regs); apply su_frm5).
    iApply (wp_cldsp_s_sconf (CID := D35) (mword_of_int (SU + 0xde))
              (mword_of_int 25 : mword 6) Rs3 F3 (K - 30)%nat
              (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf5]").
    { iApply (suli_0de with "Htext"). }
    { iEval (rewrite Hd5a). iExact "Hf5". }
    iIntros (D36 Hd36) "Hcg Hpc Hf5".
    iEval (rewrite Hd5a) in "Hf5".
    set (F4 := <[Regidx Rs3 := regval_into_reg
                  (m !!! Regidx Rs3 : mword 64)]> F3).
    assert (HF4a0 : (F4 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /F4 upd_ne; [exact HF3a0 | nz]).
    assert (HF4regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) F4).
    { rewrite /F4.
      exact (su_regs_wr_s3 m sp0 (m !!! Regidx Rs1 : mword 64)
               (m !!! Regidx Rs2 : mword 64) (pa_stk sp0 8)
               (m !!! Regidx Rs3 : mword 64) F3 _ eq_refl HF3regs). }
    assert (Hppe0 : add_vec_int (mword_of_int (SU + 0xde) : mword 64) 2
                    = mword_of_int (SU + 0xe0)) by pcw.
    iEval (rewrite Hppe0) in "Hpc".
    (* ===== +0xe0 c.j +0x168 -- into the shared epilogue ===== *)
    iApply (wp_cj_s_sconf (CID := D36) (mword_of_int (SU + 0xe0))
              (sign_extend' 21 (concat_vec (mword_of_int 68 : mword 11) ('b"0")))
              F4 (K - 30)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0e0 with "Htext"). }
    iIntros (D37 Hd37). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htg168 : add_vec (mword_of_int (SU + 0xe0) : mword 64)
                       (sign_extend' 64
                          (sign_extend' 21
                             (concat_vec (mword_of_int 68 : mword 11) ('b"0"))))
                     = mword_of_int (SU + 0x168)) by pcw.
    iEval (rewrite Htg168) in "Hpc".
    (* the buffers and slot 27, put back for the epilogue *)
    iDestruct (su_nm_join (pa_stk sp0 10) bnm0 nf with "Hnm14 Hnm2")
      as "HbNj".
    iDestruct (su_bytes_name (pa_stk sp0 10) 16 with "HbNj") as (bnf) "HbNj".
    iDestruct (su_off_join sp0 lo
                 (mword_of_int (Z.of_nat (16 * kk)) : mword 32) Hal27
                 with "H27lo H27hi") as "H27".
    assert (HF4sp : su_sp sp0 F4) by exact (su_regs_sp _ _ _ _ _ _ HF4regs).
    assert (HF4thr : su_thr m F4) by exact (su_regs_thr _ _ _ _ _ _ HF4regs).
    assert (HF4s1 : (F4 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by exact (su_regs_s1 _ _ _ _ _ _ HF4regs).
    assert (HF4s2 : (F4 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by exact (su_regs_s2 _ _ _ _ _ _ HF4regs).
    assert (HF4s3 : (F4 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by exact (su_regs_s3 _ _ _ _ _ _ HF4regs).
    (* ONE hoisted premise for the whole triple, not three inline [ltac:]s.
       [wp_next_chain] is a [repeat match goal], i.e. a whole-context scan, and
       optimization.md's rule is that such a tactic spliced into ARGUMENT
       position is priced by the depth of its call site rather than by its goal
       -- the splice's goal is an evar carrying every variable in scope.  The
       three transports here share one CID pair, so one [assert] serves all
       three and the [eb] form is one rewrite off the [b] form. *)
    assert (Htr3 : b = false \/ proc_addr jx = zero_reg
                     -> (D37 : CPU) = (D32 : CPU)) by wp_next_chain.
    assert (Htre3 : eb = false \/ proc_addr jx = zero_reg
                      -> (D37 : CPU) = (D32 : CPU)) by (rewrite Hbeq; exact Htr3).
    iDestruct (cpu_own_transport D32 D37 0 eb (proc_addr jx) b
                 Htr3 with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport D32 D37 eb (proc_addr jx)
                 Htre3 with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport D32 D37 eb (proc_addr jx)
                 Htre3 with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := D37)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (su_epilogue (CID0 := D37) m F4 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) (m !!! Regidx Rs2 : mword 64)
              (m !!! Regidx Rs3 : mword 64) w6
              (word_of_words lo (mword_of_int (Z.of_nat (16 * kk)) : mword 32))
              w30 (fun _ => NUL) bnf bp bex
              K30 Kpop Hsp0 HF4sp HF4thr HF4s1 HF4s2 HF4s3 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbNj HbP H27
                    HbE H30
                    [Hown Htce Hcce Hpidq Hsbb Hsbi Hsbs Hbsl Hisl
                     Hisl2 Hpre Hcont HP Hcex Hcmiss Hent Htgt]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
    (* ONE hoisted premise for the whole triple, not three inline [ltac:]s.
       [wp_next_chain] is a [repeat match goal], i.e. a whole-context scan, and
       optimization.md's rule is that such a tactic spliced into ARGUMENT
       position is priced by the depth of its call site rather than by its goal
       -- the splice's goal is an evar carrying every variable in scope.  The
       three transports here share one CID pair, so one [assert] serves all
       three and the [eb] form is one rewrite off the [b] form. *)
    assert (Htr5 : b = false \/ proc_addr jx = zero_reg
                     -> (CIDy : CPU) = (D37 : CPU)) by wp_next_chain.
    assert (Htre5 : eb = false \/ proc_addr jx = zero_reg
                      -> (CIDy : CPU) = (D37 : CPU)) by (rewrite Hbeq; exact Htr5).
    iDestruct (cpu_own_transport D37 CIDy 0 eb (proc_addr jx) b
                 Htr5 with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport D37 CIDy eb (proc_addr jx)
                 Htre5 with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport D37 CIDy eb (proc_addr jx)
                 Htre5 with "Hcce") as "Hcce".
    iDestruct ("Hpre" with "Hpidq") as "Hpriv".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf P1 with "[%] [%] Hcg Hown Htce Hcce Hpc
              Hbsl Hsbb Hsbi Hsbs [Hisl Hisl2] Hpriv
              [HP Hcex Hcmiss Hent Htgt]").
    { exact Hcsf. }
    { exact Hupt1. }
    { rewrite su_slots2. change 2%nat with (1 + 1)%nat.
      rewrite iref_slots_op. rewrite /iref_slot. iFrame. }
    (* ===== ret 0: BOTH receipts, and the instant-2 pin on the target =====
       [unl_pre] restated purely at instant 1, the two fired receipts, the
       target's row still readable at instant 2 (its lock was held across
       the gap), the region bound, and the two observation commits refunded
       -- the kernel observed nothing else it has not already reported. *)
    { rewrite /unlink_arms /unlink_post_ok. iLeft.
      iSplitR; [iPureIntro; rewrite Ha0f HF4a0; pcw |].
      iExists pl, av0, av1, (bv_unsigned dinum), (bv_unsigned (zero_extend' 32 (dir_inum datd kk : mword 16)
                                        : mword 32)),
              (dir_bname datd kk), (dir_entries (era_node dnd bmd datd)),
              (fn_nlink (era_node dnd bmd datd)),
              (abs_of (era_node dni bmi dati)).
      iSplitR.
      { iPureIntro. rewrite /dir_bname Hkkname.
        exact (su_last_of_npar pl nf Hname). }
      iSplitR; [by iPureIntro |].
      iSplitR.
      { iPureIntro. split; [| exact Hinb].
        rewrite su_zext32_unsigned.
        exact (su_au_inum_pos datd kk Hkklive). }
      iSplitR; [by iPureIntro |].
      iFrame "HP Hcex Hcmiss Hent Htgt". }
  Qed.

  (* ================================================================== *)

End ProofSysUnlinkAUW5F.

End SysUnlinkAUW5F.
