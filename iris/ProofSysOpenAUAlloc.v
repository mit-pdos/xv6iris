(* ProofSysOpenAUAlloc.v -- +0x5e .. +0x84 AND THE +0x140 FD_DEVICE BLOCK,
   at the ARMED post: [ProofSysOpen.so_alloc] with the AU residue threaded
   through filealloc and fdalloc and delivered at ARMs E-FAIL / F-FAIL.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the open AU
   prover).  A PARALLEL block beside the landed one.

   NOTHING ABSTRACT HAPPENS HERE.  The two table-full arms move no
   fs-abstract state at all -- the observation fired far above, in the walk
   block, and the trunc commit is still in hand -- so both of them are
   [ProofSysOpenAUParts.so_arm_fail] at the landed tail's own payout, and
   the failure tails ([ProofSysOpenTails]) are reused VERBATIM.

   WHAT THIS BLOCK DOES DECIDE is the DESCRIPTOR'S TYPE: the [beq] at +0x7a
   is where [f->type] becomes FD_DEVICE or FD_INODE, so this is where the
   store block's two conditional readings ([Htd] / [Hti], which the arm
   builder consumes) are earned.  The DEVICE arm's major bound is the
   join's [bltu] and arrives as a premise. *)
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
Require Import DinodeSlot.
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import FileOffProtocol.   (* [proto_store_free]: the free off cell is the free word (r25 item 24) *)
Require Import OffBox.   (* [off_rows] / [off_free] -- the fd off cell (r25 item 24) *)
Require Import DirView.
Require Import FileInvDefs.
Require Import FileInv.
Require Import ProcInv.
Require Import SpecArgint.
Require Import SpecEndOp.
Require Import SpecIput.
Require Import SpecIunlock.
Require Import SpecIunlockput.
Require Import SpecFileclose.
Require Import SpecFilealloc.
Require Import SpecFdalloc.
Require Import SpecItrunc.
Require Import CodeSysOpen.
Require Import SpecSysOpen.
Require Import ProofSysOpenParts.
Require Import ProofSysOpenTails.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.

Require Import ConsoleInv.
Require Import PathElems.
Require Import FsBytesGamma.
Require Import SpecSysOpenAU.
Require Import ProofSysOpenAUParts.
Require Import ProofSysOpenAUStores.
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import FsAbsDefs.
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

Module SysOpenAUAlloc (Iunlock : IUNLOCK) (Iunlockput : IUNLOCKPUT)
                      (EndOp : END_OP) (Fileclose : FILECLOSE)
                      (Itrunc : ITRUNC) (Filealloc : FILEALLOC)
                      (Fdalloc : FDALLOC).

Module Stores := SysOpenAUStores Iunlock Iunlockput EndOp Fileclose Itrunc.
Module Tails := SysOpenTails Iunlock Iunlockput EndOp Fileclose.

Section ProofSysOpenAUAlloc.
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
  (*  +0x5e .. +0x84 AND THE +0x140 FD_DEVICE BLOCK.                     *)
  (*                                                                    *)
  (*    c.sdsp s2,160 ; jal filealloc ; c.mv s2,a0 ; c.beqz -> +0x12e    *)
  (*    c.sdsp s3,152 ; jal fdalloc   ; c.mv s3,a0 ; bltz  -> +0x126     *)
  (*    lh a4,68(s1) ; c.li a5,3 ; beq -> +0x140                         *)
  (*    c.li a5,2 ; sw a5,0(s2) ; sw zero,32(s2)      [FD_INODE]         *)
  (*    +0x140: sw a4,0(s2) ; lh a5,70(s1) ; sh a5,36(s2) ; c.j +0x88    *)
  (*                                                                    *)
  (*  THE TWO SHRINK-WRAPPED SPILLS LIVE HERE, which is what makes ARMs  *)
  (*  E-FAIL and F-FAIL differ from D-FAIL at all: slot 4 holds the       *)
  (*  caller's s2 from +0x5e on, and slot 5 the caller's s3 from +0x68.   *)
  (*                                                                    *)
  (*  [so_open_slot] RUNS AFTER fdalloc, NOT AFTER filealloc: ARM F-FAIL  *)
  (*  hands the whole [file_ref] to [fileclose], so the slot may not be   *)
  (*  broken into cells until the descriptor is installed.                *)
  (* ================================================================== *)
  Lemma so_alloc_au `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gfl gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (gil gisl : gname)
      (kk : nat) (qi s : Qp) (gy : gname) (loy tly : nat) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (om lo : mword 32) (nsj : nat)
      (u : nat) (pidv : mword 32) (dqb dqs : dfrac)
      (U : ustate) (sts : list fdstate)
      (m N : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w4 w5 w6 w24 : mword 64)
      (bp : nat -> bv 8)
      (* ---- the AU side ---- *)
      (data : nat -> list (bv 8))
      (vom : mword 64) (pl : list (bv 8))
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ) :
    qi = s ->   (* r25 shapes: the parked ident fraction IS the travelling share (so_publish) *)
    (K_sys_open <= K)%nat ->
    (kk < NINODE)%nat ->
    bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < fsc_size <= BPB ->
    0 <= fsc_bmapstart ->
    fsc_bmapstart ∈ fsc_cov ->
    ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
    0 <= icfg_ist ->
    IBLOCK inum icfg_ist ∈ fsc_cov ->
    ~ (IBLOCK inum icfg_ist ∈ log_region_set fsc_logst) ->
    cov_below fsc_cov fsc_size ->
    (iput_units <= u)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    (bv_unsigned (di_type dn) = T_DIR_z -> om = (mword_of_int 0 : mword 32)) ->
    (* ---- the AU side: the omode word is the caller's argument, and the
       DEVICE arm's major bound is the join's single [bltu] ---- *)
    om = arg_int32 vom ->
    (bv_unsigned (di_type dn) = FsImg.T_DEVICE_z ->
       0 <= bv_unsigned (di_major dn) <= NDEV_max) ->
    is_aligned_paddr (Physaddr (pa_stk sp0 23)) 8 = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 N -> so_thr m N ->
    (N !!! Regidx Rs0 : mword 64) = sp0 ->
    (N !!! Regidx Rs1 : mword 64) = ientry kk ->
    (N !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (N !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    so_al sp0 ->
    (* the block takes [fileclose]'s loan off the top of the allowance
       ([so_iref_take]); see the [iref_slots nsj] row below. *)
    (1 <= nsj)%nat ->
    sie_cap_gpr KT1 N (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0x5e)) -∗
    panic_env -∗
    is_ftable gfl gf -∗
    bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
    log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
    fs_crash_seam fsc_cov fsc_logst -∗
    gen_cert -∗
    is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
    itable_inv -∗
    ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kk -∗
    ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
    ireg_open -∗
    is_sleeplock_genl gil gisl (i_lock (ientry kk)) "inode"%string (ic_slp fsc_ic kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s (i_lock (ientry kk)) pidv -∗
    ⌜(loy <= tly)%nat⌝ -∗
    IcacheRef.cred_floor loy tly -∗
    IcacheInv.iref_claims -∗
    ic_tx_dep fsc_ic kk s icfg_dev inum gy loy -∗
    off_rows off_cfg kk cur_ctx -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} icfg_dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    so_flat kk inum dn bm data -∗
    ity_shot gy (di_type dn) -∗
    (* the payload's freeze token (§3.9, RULING A-prime), relayed to
       [so_tail_s]'s iunlock *)
    ifreeze_off (bv_unsigned inum) -∗
    (∃ loK tlK : nat,
       ⌜(loK <= tlK)%nat⌝ ∗ IcacheRef.cred_floor loK tlK ∗
       IcacheRef.inode_ref_short_genlo kk (qi + s)%Qp qi icfg_dev inum gy loK) -∗
    (* its PROVENANCE UNIT (item 7a-wire): the parent parks in the fd slot's
       [cinv] as [IcacheRef.inode_held_short], and that is one of the unit's
       two rest homes, so it travels with [Hkeep] the whole way. *)
    runit_any (bv_unsigned inum) -∗
    proc_priv gf (proc_addr jx) pidv U -∗
    procs_inv gs -∗
    dev_inv fsc_uart fsc_disk -∗
    disk_geom fsc_disk pd pav pu -∗
    is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
    log_opb icfg_log u -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
    bslots 3 -∗
    (* ONE OF THESE IS [fileclose]'s LOAN.  The D-FAIL tail closes the file
       it just allocated, and [SpecFileclose] borrows an iref unit across
       the call -- see the note on its [iref_slot] row.  The block takes it
       off the top of the allowance ([so_iref_take], hence the [1 <= nsj]
       premise) and either spends it on that loan and gets it back from
       fileclose, or never touches it; either way it is folded back in
       before the block returns, which is why [so_cont]'s ledger is an
       equality. *)
    iref_slots nsj -∗
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
    (* ---- THE AU RESIDUE, inert across this block ---- *)
    P (length (path_elems pl)) (bv_unsigned inum) -∗
    so_obs Φo (bv_unsigned inum) (era_node dn bm data) -∗
    atrunc_commit_at (fs_gamma_L fsc_fs) appE Φt -∗
    wp_next true (proc_addr jx)
      (so_cont_au gf nsj
               dqb dqs (proc_addr jx) pidv vom U sts P Pmiss Φo Φt m K eb b lks) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hqs HK Hkk Hinb Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk
           Hiblog Hcovb Hiu Hj Hgl Hlkempty Hdir Hom Hmajb Hal23 Hsp0 HNsp
           HNthr HNs0 HNs1 HNs2 HNs3 Hal Hnspos.
    destruct (so_kb K HK) as (HKcr & HKna & HKai & HKas & HKbo & HKeo & HKil &
                              HKiu & HKit & HKip & HKup & HKfc & HKfa & HKfd &
                              HK10 & HK24 & Kpop).
    assert (Hu2 : (2 <= u)%nat) by (revert Hiu; unfold iput_units; lia).

    iIntros "Hcg Hown Htce Hcce #Htext #Hdata Hpc #Hpe #Hftab #Hbio #Hlog
              Hseam Hgen #Hitab #Hitinv #Hesck #Hireg #Hropen #Hslkk Hslkd %Hley #Hfly #Hclaimsy Hdep Hoffr
              Hidev Hiinum Hivalid Hflat #Hshot Hfrz Hkeep Hru Hpriv #Hprocs #Hdev #Hgeo
              #Hdlk Hop Hsbb Hsbi #Hbmres Hbsl Hisl Hfds Hfrag Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
              HbP H23lo H23hi H24 HP Hobs Htc Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* [fileclose]'s loan, off the top of the allowance *)
    iDestruct (so_iref_take nsj Hnspos with "Hisl") as "[Hires Hisl]".
    (* ===== +0x5e c.sdsp s2,160(sp) ===== *)
    assert (Hd4 : add_vec (N !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 20 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HNsp; apply so_frm4).
    iApply (wp_csdsp_s_sconf (CID := CID0) (mword_of_int (SO + 0x5e))
              (mword_of_int 20 : mword 6) Rs2 N (K - 24)%nat w4 b
              with "Hcg Hpc [] [Hf4]").
    { iApply (soi_05e with "Htext"). }
    { iEval (rewrite Hd4). iExact "Hf4". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf4".
    iEval (rewrite Hd4; rgne; rewrite HNs2) in "Hf4".
    assert (Hpp5e : add_vec_int (mword_of_int (SO + 0x5e) : mword 64) 2
                    = mword_of_int (SO + 0x60)) by pcw.
    iEval (rewrite Hpp5e) in "Hpc".
    (* ===== +0x60 jal ra,filealloc ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SO + 0x60)) Rra
              (mword_of_int 2092812 : mword 21) N (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_060 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x60) : mword 64) 4)]> N).
    assert (Hjfa : add_vec (mword_of_int (SO + 0x60) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092812 : mword 21))
                   = mword_of_int KernelSyms.filealloc) by pcw.
    iEval (rewrite Hjfa) in "Hpc".
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x60) : mword 64) 4)
      by (rewrite /M1; apply upd_eq).
    assert (HM1sp : so_sp sp0 M1)
      by (rewrite /so_sp /M1 upd_ne; [exact HNsp | nz]).
    assert (HM1s0 : (M1 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M1 upd_ne; [exact HNs0 | nz]).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M1 upd_ne; [exact HNs1 | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HNs2 | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [exact HNs3 | nz]).
    assert (HM1thr : so_thr m M1).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HNthr c Hc N2b N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Filealloc.wp_filealloc_sconf (CID := CID2) gfl gf M1 0%nat eb
              (proc_addr jx) (K - 24)%nat b lks HKfa so_noff0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htext Hpc Hftab Hfds").
    iIntros (CID3 Hq3 mfa) "Hcg Hown Hpc %Hcsfa Hfapost".
    assert (Hpcfa : ret_pc (M1 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0x64)) by (rewrite HM1ra; pcw).
    iEval (rewrite Hpcfa) in "Hpc".
    iDestruct (trap_csrs_ext_transport CID0 CID3 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID3 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    assert (Hfasp : so_sp sp0 mfa).
    { rewrite /so_sp (callee_saved_lookup Hcsfa csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM1sp. }
    assert (Hfas0 : (mfa !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsfa Rs0 ltac:(vm_compute; reflexivity)).
      exact HM1s0. }
    assert (Hfas1 : (mfa !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite (callee_saved_lookup Hcsfa Rs1 ltac:(vm_compute; reflexivity)).
      exact HM1s1. }
    assert (Hfas2 : (mfa !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsfa Rs2 ltac:(vm_compute; reflexivity)).
      exact HM1s2. }
    assert (Hfas3 : (mfa !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsfa Rs3 ltac:(vm_compute; reflexivity)).
      exact HM1s3. }
    assert (Hfathr : so_thr m mfa).
    { intros c Hc N2b N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsfa c Hc).
      exact (HM1thr c Hc N2b N8 N9 N18 N19). }
    (* ===== +0x64 c.mv s2,a0 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID3) (mword_of_int (SO + 0x64)) Rs2 Ra0
              mfa (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_064 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M2 := <[Regidx Rs2 := regval_into_reg
                  (add_vec zero_reg (mfa !!! Regidx Ra0))]> mfa).
    assert (HM2s2 : (M2 !!! Regidx Rs2 : mword 64)
                    = (mfa !!! Regidx Ra0 : mword 64)).
    { etransitivity; [ rewrite /M2; apply upd_eq |]. apply add_vec_zero_l. }
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = (mfa !!! Regidx Ra0 : mword 64))
      by (rewrite /M2 upd_ne; [reflexivity | nz]).
    assert (HM2sp : so_sp sp0 M2)
      by (rewrite /so_sp /M2 upd_ne; [exact Hfasp | nz]).
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M2 upd_ne; [exact Hfas0 | nz]).
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact Hfas1 | nz]).
    assert (HM2s3 : (M2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M2 upd_ne; [exact Hfas3 | nz]).
    assert (HM2thr : so_thr m M2).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /M2 upd_ne; [| regne].
      exact (Hfathr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp64 : add_vec_int (mword_of_int (SO + 0x64) : mword 64) 2
                    = mword_of_int (SO + 0x66)) by pcw.
    iEval (rewrite Hpp64) in "Hpc".
    (* ===== +0x66 c.beqz a0, +0x12e  [ARM E-FAIL] ===== *)
    rewrite /filealloc_post.
    iDestruct "Hfapost" as "[[%Hz Hfds] | (%kf & [%Hkf %Hfn] & Href)]".
    { (* ---- filealloc refused ---- *)
      iApply (wp_cbeqz_taken_s_sconf (CID := CID4) (mword_of_int (SO + 0x66))
                (mword_of_int 100 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                M2 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HM2a0 Hz;
                      exact (proj2 (eq_vec_true_iff _ _) eq_refl))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_066 with "Htext"). }
      iIntros (CID5 Hq5). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg66 : add_vec (mword_of_int (SO + 0x66) : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13 (concat_vec (mword_of_int 100 : mword 8) ('b"0"))))
                      = mword_of_int (SO + 0x12e)) by pcw.
      iEval (rewrite Htg66) in "Hpc".
      iDestruct (so_omode_join sp0 lo om Hal23 with "H23lo H23hi") as "H23".
      iDestruct (so_flat_close with "Hflat") as "Hload".
      iDestruct (proc_priv_bare_acc with "Hpriv") as "[Hpbare Hpback]".
      iDestruct "Hkeep" as (loK tlK) "(%HleK & #HflK & Hkeep)".
      iDestruct (inode_ref_short_gen_forget _ _ _ _ _ _ _ _ HleK
                   with "HflK Hkeep") as "Hkeep".
      iDestruct (cpu_own_transport CID3 CID5 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CID3 CID5 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
      iDestruct (cpu_claim_ext_transport CID3 CID5 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
      iApply (Tails.so_tail_e (CID0 := CID5) gs jx gl pd pav pu
                gil gisl
 kk qi s gy loy tly inum dn bm u pidv
                (DfracOwn (1/4)) dqb dqs m M2 sp0 K eb b lks w5 w6
                (word_of_words lo om) w24 bp U
                HKup HKeo HK24 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
                Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HM2sp HM2thr
                HM2s1 HM2s3 Hal
                with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                      Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd [//] Hfly Hclaimsy Hdep Hoffr Hidev
                      Hiinum Hivalid Hload Hshot Hfrz Hkeep Hru Hsbb Hsbi Hbmres Hpbare
                      Hprocs Hdev Hgeo Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
                      HbP H23 H24
                      [Hpback Hfds Hfrag Hisl Hires HP Hobs Htc Hcont]").
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf)
        "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpbare Hsbb Hsbi
         Hbsl Hislot".
      iDestruct ("Hpback" with "Hpbare") as "Hpriv".
      (* the loan was never spent on this arm: fold it back beside the unit
         the tail's iput released. *)
      iDestruct (iref_slots_combine (nsj - 1) 1 with "Hisl Hires") as "Hisl".
      iDestruct (iref_slots_combine (nsj - 1 + 1) 1 with "Hisl Hislot") as "Hisl".
      replace (nsj - 1 + 1 + 1)%nat with (S nsj) by lia.
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf (S nsj) with "[%] [%] Hcg Hown Htce Hcce
                Hpc Hsbb Hsbi Hbsl Hisl [Hpriv Hfds Hfrag HP Hobs Htc]").
      { exact Hcsf. }
      { reflexivity. }
      { iApply (so_arm_fail gf (proc_addr jx) pidv vom P Pmiss Φo Φt U sts _ pl
                  (bv_unsigned inum) (era_node dn bm data) Ha0f
                  with "Hpriv Hfrag Hfds HP Hobs Htc"). } }
    (* ---- filealloc succeeded ---- *)
    iApply (wp_cbeqz_fall_s_sconf (CID := CID4) (mword_of_int (SO + 0x66))
              (mword_of_int 100 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              M2 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HM2a0 Hfn; exact (fnode_nonzero kf Hkf))
              with "Hcg Hpc []").
    { iApply (soi_066 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    assert (Hpp66 : add_vec_int (mword_of_int (SO + 0x66) : mword 64) 2
                    = mword_of_int (SO + 0x68)) by pcw.
    iEval (rewrite Hpp66) in "Hpc".
    assert (HM2s2f : (M2 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite HM2s2; exact Hfn).
    (* ===== +0x68 c.sdsp s3,152(sp) ===== *)
    assert (Hd5 : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 19 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite HM2sp; apply so_frm5).
    iApply (wp_csdsp_s_sconf (CID := CID5) (mword_of_int (SO + 0x68))
              (mword_of_int 19 : mword 6) Rs3 M2 (K - 24)%nat w5 b
              with "Hcg Hpc [] [Hf5]").
    { iApply (soi_068 with "Htext"). }
    { iEval (rewrite Hd5). iExact "Hf5". }
    iIntros (CID6 Hq6) "Hcg Hpc Hf5".
    iEval (rewrite Hd5; rgne; rewrite HM2s3) in "Hf5".
    assert (Hpp68 : add_vec_int (mword_of_int (SO + 0x68) : mword 64) 2
                    = mword_of_int (SO + 0x6a)) by pcw.
    iEval (rewrite Hpp68) in "Hpc".
    (* ===== +0x6a jal ra,fdalloc ===== *)
    iApply (wp_jal_s_sconf (CID := CID6) (mword_of_int (SO + 0x6a)) Rra
              (mword_of_int 2095604 : mword 21) M2 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_06a with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (M3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x6a) : mword 64) 4)]> M2).
    assert (Hjfd : add_vec (mword_of_int (SO + 0x6a) : mword 64)
                     (sign_extend' 64 (mword_of_int 2095604 : mword 21))
                   = mword_of_int KernelSyms.fdalloc) by pcw.
    iEval (rewrite Hjfd) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x6a) : mword 64) 4)
      by (rewrite /M3; apply upd_eq).
    assert (HM3a0 : (M3 !!! Regidx Ra0 : mword 64) = fnode kf)
      by (rewrite /M3 upd_ne; [rewrite HM2a0 Hfn; reflexivity | nz]).
    assert (HM3sp : so_sp sp0 M3)
      by (rewrite /so_sp /M3 upd_ne; [exact HM2sp | nz]).
    assert (HM3s0 : (M3 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M3 upd_ne; [exact HM2s0 | nz]).
    assert (HM3s1 : (M3 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M3 upd_ne; [exact HM2s1 | nz]).
    assert (HM3s2 : (M3 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /M3 upd_ne; [exact HM2s2f | nz]).
    assert (HM3s3 : (M3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s3 | nz]).
    assert (HM3thr : so_thr m M3).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2b N8 N9 N18 N19). }
    iDestruct (proc_priv_split with "Hpriv") as "[Hcore Hofiles]".
    iDestruct (proc_ofiles_owe_empty gf (pv_fdg (us_V U)) (proc_addr jx) (pv_ofile (us_V U))) as "Hoeq".
    iDestruct (bi.equiv_entails_1_2 _ _ (proc_ofiles_owe_empty gf (pv_fdg (us_V U)) (proc_addr jx)
                 (pv_ofile (us_V U))) with "Hofiles") as "Howe".
    iDestruct (proc_ofiles_owe_len with "Howe") as %Hlen.
    iDestruct (cpu_own_transport CID3 CID7 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Fdalloc.wp_fdalloc_sconf (CID := CID7) gf kf ∅ M3 (K - 24)%nat
              0%nat eb (proc_addr jx) pidv U b lks HM3a0 Hkf so_noff0 HKfd
              with "Hcg Hown Htext Hdata Hpc Hcore Howe").
    iIntros (CID8 Hq8 mfd) "%Hcsfd Hcg Hown Hpc Hcore Hfdpost".
    assert (Hpcfd : ret_pc (M3 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0x6e)) by (rewrite HM3ra; pcw).
    iEval (rewrite Hpcfd) in "Hpc".
    iDestruct (trap_csrs_ext_transport CID3 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID3 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    assert (Hfdsp : so_sp sp0 mfd).
    { rewrite /so_sp (callee_saved_lookup Hcsfd csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM3sp. }
    assert (Hfds0 : (mfd !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsfd Rs0 ltac:(vm_compute; reflexivity)).
      exact HM3s0. }
    assert (Hfds1 : (mfd !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite (callee_saved_lookup Hcsfd Rs1 ltac:(vm_compute; reflexivity)).
      exact HM3s1. }
    assert (Hfds2 : (mfd !!! Regidx Rs2 : mword 64) = fnode kf).
    { rewrite (callee_saved_lookup Hcsfd Rs2 ltac:(vm_compute; reflexivity)).
      exact HM3s2. }
    assert (Hfds3 : (mfd !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsfd Rs3 ltac:(vm_compute; reflexivity)).
      exact HM3s3. }
    assert (Hfdthr : so_thr m mfd).
    { intros c Hc N2b N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsfd c Hc).
      exact (HM3thr c Hc N2b N8 N9 N18 N19). }
    (* ===== +0x6e c.mv s3,a0 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID8) (mword_of_int (SO + 0x6e)) Rs3 Ra0
              mfd (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_06e with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (M4 := <[Regidx Rs3 := regval_into_reg
                  (add_vec zero_reg (mfd !!! Regidx Ra0))]> mfd).
    assert (HM4s3 : (M4 !!! Regidx Rs3 : mword 64)
                    = (mfd !!! Regidx Ra0 : mword 64)).
    { etransitivity; [ rewrite /M4; apply upd_eq |]. apply add_vec_zero_l. }
    assert (HM4a0 : (M4 !!! Regidx Ra0 : mword 64) = (mfd !!! Regidx Ra0 : mword 64))
      by (rewrite /M4 upd_ne; [reflexivity | nz]).
    assert (HM4sp : so_sp sp0 M4)
      by (rewrite /so_sp /M4 upd_ne; [exact Hfdsp | nz]).
    assert (HM4s0 : (M4 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M4 upd_ne; [exact Hfds0 | nz]).
    assert (HM4s1 : (M4 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M4 upd_ne; [exact Hfds1 | nz]).
    assert (HM4s2 : (M4 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /M4 upd_ne; [exact Hfds2 | nz]).
    assert (HM4thr : so_thr m M4).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /M4 upd_ne; [| regne].
      exact (Hfdthr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp6e : add_vec_int (mword_of_int (SO + 0x6e) : mword 64) 2
                    = mword_of_int (SO + 0x70)) by pcw.
    iEval (rewrite Hpp6e) in "Hpc".
    (* ===== +0x70 bltz a0, +0x126  [ARM F-FAIL] ===== *)
    rewrite /fdalloc_post.
    iDestruct "Hfdpost" as "[[[%Hm1 %Hnofd] Howe] | (%fd & %ll & [%Hfdv %Hfrees] & Howe & Hfds & Hauth)]".
    { (* ---- fdalloc refused ---- *)
      iApply (wp_blt_x0_taken_s_sconf (CID := CID9) (mword_of_int (SO + 0x70))
                (mword_of_int 182 : mword 13) Ra0 M4 (K - 24)%nat b ltac:(nz)
                ltac:(rgne; rewrite HM4a0 Hm1; exact so_m1_neg)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_070 with "Htext"). }
      iIntros (CID10 Hq10). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg70 : add_vec (mword_of_int (SO + 0x70) : mword 64)
                        (sign_extend' 64 (mword_of_int 182 : mword 13))
                      = mword_of_int (SO + 0x126)) by pcw.
      iEval (rewrite Htg70) in "Hpc".
      iDestruct (so_omode_join sp0 lo om Hal23 with "H23lo H23hi") as "H23".
      iDestruct (so_flat_close with "Hflat") as "Hload".
      iDestruct (proc_priv_core_bare_acc with "Hcore") as "[Hpbare Hcback]".
      iDestruct "Hkeep" as (loK tlK) "(%HleK & #HflK & Hkeep)".
      iDestruct (inode_ref_short_gen_forget _ _ _ _ _ _ _ _ HleK
                   with "HflK Hkeep") as "Hkeep".
      iDestruct (cpu_own_transport CID8 CID10 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CID8 CID10 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
      iDestruct (cpu_claim_ext_transport CID8 CID10 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
      iApply (Tails.so_tail_f (CID0 := CID10) gfl gf gs jx gl pd pav
                pu gil gisl
 kk qi s gy loy tly inum dn bm
                kf 1%Qp _ inhabitant None u pidv
                (DfracOwn (1/4)) dqb dqs m M4 sp0 K eb b lks w6
                (word_of_words lo om) w24 bp U
                HKup HKeo HKfc HK24 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog
                Hist0 Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HM4sp
                HM4thr HM4s1 HM4s2 Hal
                with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpe Hftab Href
                      [] Hbio Hlog Hseam Hgen
                      Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd [//] Hfly Hclaimsy Hdep Hoffr Hidev
                      Hiinum Hivalid Hload Hshot Hfrz Hkeep Hru Hsbb Hsbi Hbmres Hpbare
                      Hprocs Hdev Hgeo Hdlk Hbsl Hires Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
                      HbP H23 H24
                      [Hcback Howe Hisl Hfrag HP Hobs Htc Hcont]").
      { iApply fileclose_env_none. }
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf)
        "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpbare Hsbb Hsbi
         Hbsl Hislot Hfds Hfout".
      iDestruct ("Hcback" with "Hpbare") as "Hcore".
      iDestruct (proc_priv_join with "Hcore Howe") as "Hpriv".
      (* [so_tail_f] hands back TWO: the loan fileclose repaid and the unit
         iput released.  With the one taken off the top, that is [S nsj]. *)
      iDestruct (iref_slots_combine (nsj - 1) 2 with "Hisl Hislot") as "Hisl".
      replace (nsj - 1 + 2)%nat with (S nsj) by lia.
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf (S nsj) with "[%] [%] Hcg Hown Htce Hcce
                Hpc Hsbb Hsbi Hbsl Hisl [Hpriv Hfds Hfrag HP Hobs Htc]").
      { exact Hcsf. }
      { reflexivity. }
      { iApply (so_arm_fail gf (proc_addr jx) pidv vom P Pmiss Φo Φt U sts _ pl
                  (bv_unsigned inum) (era_node dn bm data) Ha0f
                  with "Hpriv Hfrag Hfds HP Hobs Htc"). } }
    (* ---- fdalloc installed the descriptor ---- *)
    assert (Hfdlt : (fd < NOFILE)%nat).
    { rewrite -Hlen. exact (fd_frees_head_lt _ _ _ Hfrees). }
    iApply (wp_blt_x0_fall_s_sconf (CID := CID9) (mword_of_int (SO + 0x70))
              (mword_of_int 182 : mword 13) Ra0 M4 (K - 24)%nat b ltac:(nz)
              ltac:(rgne; rewrite HM4a0 Hfdv;
                    exact (so_nonneg _ (so_fd_range fd Hfdlt)))
              with "Hcg Hpc []").
    { iApply (soi_070 with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc".
    assert (Hpp70 : add_vec_int (mword_of_int (SO + 0x70) : mword 64) 4
                    = mword_of_int (SO + 0x74)) by pcw.
    iEval (rewrite Hpp70) in "Hpc".
    assert (HM4s3f : (M4 !!! Regidx Rs3 : mword 64)
                     = (mword_of_int (Z.of_nat fd) : mword 64))
      by (rewrite HM4s3; exact Hfdv).
    (* ---- THE FRESH SLOT, OPENED: six cells plain, [f->ip] WHOLE ---- *)
    iApply fupd_wp.
    iMod (so_open_slot ⊤ gf kf with "Href")
      as (Cf pn) "(%Hty0 & Hiru & Hfref & Hflive & Hfpn & Hfty
                        & Hfrd & Hfwr & Hfpip & Hfmaj & Hfip & Hfree)".
    iModIntro.
    (* the loan is not spent on this arm -- the file is about to be PUBLISHED,
       not closed -- so fold it back before the stores block, which is where
       [so_tail_pub] expects the ledger whole. *)
    iDestruct (iref_slots_combine (nsj - 1) 1 with "Hisl Hires") as "Hisl".
    replace (nsj - 1 + 1)%nat with nsj by lia.
    (* ===== +0x74 lh a4,68(s1) ===== *)
    iDestruct (so_flat_meta with "Hflat") as "[Hmeta Hlback]".
    iDestruct (so_type_acc with "Hmeta") as "[Hity Hmback]".
    iEval (rewrite /i_type) in "Hity".
    iApply (wp_lh_s_sconf (CID := CID10) (kt := KT1) (ktd := KT0) (mword_of_int (SO + 0x74)) Ra4 Rs1
              (mword_of_int 68 : mword 12) M4 (K - 24)%nat
              (di_type dn : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hity]").
    { iApply (soi_074 with "Htext"). }
    { iEval (rgne; rewrite HM4s1). iExact "Hity". }
    iIntros (CID11 Hq11) "Hcg Hpc Hity".
    iEval (rgne; rewrite HM4s1) in "Hity".
    iDestruct ("Hmback" with "[Hity]") as "Hmeta";
      [iEval (rewrite /i_type); iExact "Hity" |].
    iDestruct ("Hlback" with "Hmeta") as "Hflat".
    set (M5 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_type dn : mword 16) : mword 64)]> M4).
    assert (HM5a4 : (M5 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /M5; apply upd_eq).
    assert (Hpp74 : add_vec_int (mword_of_int (SO + 0x74) : mword 64) 4
                    = mword_of_int (SO + 0x78)) by pcw.
    iEval (rewrite Hpp74) in "Hpc".
    (* ===== +0x78 c.li a5,3 ===== *)
    iApply (wp_cli_s_sconf (CID := CID11) (mword_of_int (SO + 0x78)) Ra5
              (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64)
              M5 (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (soi_078 with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc".
    set (M6 := <[Regidx Ra5 := regval_into_reg (mword_of_int 3 : mword 64)]> M5).
    assert (HM6a4 : (M6 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /M6 upd_ne; [exact HM5a4 | nz]).
    assert (HM6a5 : (M6 !!! Regidx Ra5 : mword 64) = (mword_of_int 3 : mword 64))
      by (rewrite /M6; apply upd_eq).
    assert (HM6sp : so_sp sp0 M6).
    { rewrite /so_sp /M6 upd_ne; [| nz]. rewrite /M5 upd_ne; [| nz].
      exact HM4sp. }
    assert (HM6s0 : (M6 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /M6 upd_ne; [| nz]. rewrite /M5 upd_ne; [| nz]. exact HM4s0. }
    assert (HM6s1 : (M6 !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite /M6 upd_ne; [| nz]. rewrite /M5 upd_ne; [| nz]. exact HM4s1. }
    assert (HM6s2 : (M6 !!! Regidx Rs2 : mword 64) = fnode kf).
    { rewrite /M6 upd_ne; [| nz]. rewrite /M5 upd_ne; [| nz]. exact HM4s2. }
    assert (HM6s3 : (M6 !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64)).
    { rewrite /M6 upd_ne; [| nz]. rewrite /M5 upd_ne; [| nz]. exact HM4s3f. }
    assert (HM6thr : so_thr m M6).
    { intros c Hc N2b N8 N9 N18 N19.
      rewrite /M6 upd_ne; [| regne]. rewrite /M5 upd_ne; [| regne].
      exact (HM4thr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp78 : add_vec_int (mword_of_int (SO + 0x78) : mword 64) 2
                    = mword_of_int (SO + 0x7a)) by pcw.
    iEval (rewrite Hpp78) in "Hpc".
    (* ===== +0x7a beq a4,a5, +0x140 ===== *)
    destruct (decide (di_type dn = (mword_of_int 3 : mword 16))) as [Hdev3 | Hnd3].
    { (* ---- T_DEVICE: the +0x140 block ---- *)
      iApply (wp_beq_taken_s_sconf (CID := CID12) (mword_of_int (SO + 0x7a))
                (mword_of_int 198 : mword 13) Ra5 Ra4 M6 (K - 24)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HM6a4 HM6a5;
                      exact (so_ty_eq (di_type dn) 3 so_tdev_range Hdev3))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_07a with "Htext"). }
      iIntros (CID13 Hq13). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg7a : add_vec (mword_of_int (SO + 0x7a) : mword 64)
                        (sign_extend' 64 (mword_of_int 198 : mword 13))
                      = mword_of_int (SO + 0x140)) by pcw.
      iEval (rewrite Htg7a) in "Hpc".
      (* ===== +0x140 sw a4,0(s2) -- f->type = FD_DEVICE ===== *)
      assert (Had140 : a_ftype kf
                       = add_vec (M6 !!! Regidx Rs2 : mword 64)
                           (sign_extend' 64 (mword_of_int 0 : mword 12))).
      { rewrite HM6s2. unfold a_ftype. symmetry. apply addv_sext0. }
      assert (Had140' : a_ftype kf
                        = add_vec (rget M6 Rs2)
                            (sign_extend' 64 (mword_of_int 0 : mword 12)))
        by (rgne; exact Had140).
      iEval (rewrite Had140') in "Hfty".
      assert (Hvv140 : trunc32 (M6 !!! Regidx Ra4 : mword 64) = FD_DEVICE).
      { rewrite HM6a4 Hdev3. unfold FD_DEVICE.
        apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_sw_s_sconf (CID := CID13) (mword_of_int (SO + 0x140)) Ra4 Rs2
                (mword_of_int 0 : mword 12) M6 (K - 24)%nat (fc_type Cf) b
                with "Hcg Hpc [] Hfty").
      { iApply (soi_140 with "Htext"). }
      iIntros (CID14 Hq14) "Hcg Hpc Hfty".
      iEval (rgne) in "Hfty". iEval (rgne) in "Hfty".
      iEval (rewrite -Had140 Hvv140) in "Hfty".
      assert (Hpp140 : add_vec_int (mword_of_int (SO + 0x140) : mword 64) 4
                       = mword_of_int (SO + 0x144)) by pcw.
      iEval (rewrite Hpp140) in "Hpc".
      (* ===== +0x144 lh a5,70(s1) -- ip->major ===== *)
      iDestruct (so_flat_meta with "Hflat") as "[Hmeta Hlback]".
      iDestruct (so_maj_acc with "Hmeta") as "[Himaj Hmback]".
      iEval (rewrite /i_major) in "Himaj".
      iApply (wp_lh_s_sconf (CID := CID14) (kt := KT1) (ktd := KT0) (mword_of_int (SO + 0x144)) Ra5 Rs1
                (mword_of_int 70 : mword 12) M6 (K - 24)%nat
                (di_major dn : mword 16) b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc [] [Himaj]").
      { iApply (soi_144 with "Htext"). }
      { iEval (rgne; rewrite HM6s1). iExact "Himaj". }
      iIntros (CID15 Hq15) "Hcg Hpc Himaj".
      iEval (rgne; rewrite HM6s1) in "Himaj".
      iDestruct ("Hmback" with "[Himaj]") as "Hmeta";
        [iEval (rewrite /i_major); iExact "Himaj" |].
      iDestruct ("Hlback" with "Hmeta") as "Hflat".
      set (M7 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (di_major dn : mword 16) : mword 64)]> M6).
      assert (HM7a5 : (M7 !!! Regidx Ra5 : mword 64)
                      = (sign_extend' 64 (di_major dn : mword 16) : mword 64))
        by (rewrite /M7; apply upd_eq).
      assert (HM7sp : so_sp sp0 M7)
        by (rewrite /so_sp /M7 upd_ne; [exact HM6sp | nz]).
      assert (HM7s0 : (M7 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /M7 upd_ne; [exact HM6s0 | nz]).
      assert (HM7s1 : (M7 !!! Regidx Rs1 : mword 64) = ientry kk)
        by (rewrite /M7 upd_ne; [exact HM6s1 | nz]).
      assert (HM7s2 : (M7 !!! Regidx Rs2 : mword 64) = fnode kf)
        by (rewrite /M7 upd_ne; [exact HM6s2 | nz]).
      assert (HM7s3 : (M7 !!! Regidx Rs3 : mword 64)
                      = (mword_of_int (Z.of_nat fd) : mword 64))
        by (rewrite /M7 upd_ne; [exact HM6s3 | nz]).
      assert (HM7thr : so_thr m M7).
      { intros c Hc N2b N8 N9 N18 N19. rewrite /M7 upd_ne; [| regne].
        exact (HM6thr c Hc N2b N8 N9 N18 N19). }
      assert (Hpp144 : add_vec_int (mword_of_int (SO + 0x144) : mword 64) 4
                       = mword_of_int (SO + 0x148)) by pcw.
      iEval (rewrite Hpp144) in "Hpc".
      (* ===== +0x148 sh a5,36(s2) -- f->major = ip->major ===== *)
      iEval (rewrite /a_fmajor /foff_of) in "Hfmaj".
      iApply (wp_sh_s_sconf (CID := CID15) (kt := KT1) (ktd := KT0) (mword_of_int (SO + 0x148)) Ra5 Rs2
                (mword_of_int 36 : mword 12) M7 (K - 24)%nat (fc_major Cf) b
                with "Hcg Hpc [] [Hfmaj]").
      { iApply (soi_148 with "Htext"). }
      { iEval (rgne; rewrite HM7s2). iExact "Hfmaj". }
      iIntros (CID16 Hq16) "Hcg Hpc Hfmaj".
      iEval (rgne; rewrite HM7s2; rgne; rewrite HM7a5;
             rewrite trunc16_sext64) in "Hfmaj".
      assert (Hpp148 : add_vec_int (mword_of_int (SO + 0x148) : mword 64) 4
                       = mword_of_int (SO + 0x14c)) by pcw.
      iEval (rewrite Hpp148) in "Hpc".
      (* ===== +0x14c c.j +0x88 ===== *)
      iApply (wp_cj_s_sconf (CID := CID16) (mword_of_int (SO + 0x14c))
                (sign_extend' 21 (concat_vec (mword_of_int 1950 : mword 11) ('b"0")))
                M7 (K - 24)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_14c with "Htext"). }
      iIntros (CID17 Hq17). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg14c : add_vec (mword_of_int (SO + 0x14c) : mword 64)
                         (sign_extend' 64
                            (sign_extend' 21 (concat_vec (mword_of_int 1950 : mword 11) ('b"0"))))
                       = mword_of_int (SO + 0x88)) by pcw.
      iEval (rewrite Htg14c) in "Hpc".
      iDestruct (cpu_own_transport CID8 CID17 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CID8 CID17 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
      iDestruct (cpu_claim_ext_transport CID8 CID17 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID17)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      (* the +0x7a [beq] took the DEVICE arm, so the two cells this block
         wrote ARE the record's, and the join's bound applies *)
      assert (Hdvz : bv_unsigned (di_type dn) = FsImg.T_DEVICE_z)
        by (rewrite Hdev3; vm_compute; reflexivity).
      iApply (Stores.so_stores_au (CID0 := CID17) gf gs jx gl pd pav pu
                gil gisl
 kk qi s gy loy tly inum dn bm kf fd ll pn FD_DEVICE
                (fc_readable Cf) (fc_writable Cf) (fc_pipe Cf) (fc_ip Cf)
                (di_major dn) om (mword_of_int 0 : mword 32) lo nsj u pidv dqb dqs U sts m M7 sp0 K eb b
                lks w6 w24 bp
                data vom pl P Pmiss Φo Φt
                (FdDevice (bv_unsigned (di_major dn))) 1%positive
                Hqs HKiu HKeo HKit HK24 Kpop Hkk Hinb Hgeom Hsize
                Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog Hcovb Hu2 Hj Hgl
                Hlkempty Hkf Hfdlt Hlen Hfrees (or_intror eq_refl) Hdir
                (so_wf_dev (mword_of_int 0 : mword 32))
                Hom
                ltac:(intros _;
                      exact (conj eq_refl
                               (conj eq_refl
                                  (conj (Hmajb Hdvz) eq_refl))))
                ltac:(intros Hq; exfalso; exact (Hq Hdvz))
                Hal23 Hsp0 HM7sp HM7thr HM7s0 HM7s1 HM7s2 HM7s3 Hal
                with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                      Hitinv Hesck Hireg Hslkk Hslkd [//] Hfly Hclaimsy Hdep Hoffr Hidev Hiinum
                      Hivalid Hflat Hshot Hfrz Hkeep Hru Hfref Hflive Hfpn Hfty Hfrd
                      Hfwr Hfpip Hfmaj Hfip [Hfree] Hiru Hcore Howe Hprocs Hdev Hgeo
                      Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hfrag Hauth Hf1 Hf2 Hf3 Hf4
                      Hf5 Hf6 HbP H23lo H23hi H24 HP Hobs Htc Hcont").
      (* the device arm never touches [f->off]: the free cell rides through *)
      { try (rewrite bool_decide_eq_false_2;
             [| intro Hc; apply (f_equal bv_unsigned) in Hc; by vm_compute in Hc]).
        iExact "Hfree". } }
    (* ---- not a device: the FD_INODE pair ---- *)
    iApply (wp_beq_fall_s_sconf (CID := CID12) (mword_of_int (SO + 0x7a))
              (mword_of_int 198 : mword 13) Ra5 Ra4 M6 (K - 24)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HM6a4 HM6a5;
                    exact (so_ty_ne (di_type dn) 3 so_tdev_range Hnd3))
              with "Hcg Hpc []").
    { iApply (soi_07a with "Htext"). }
    iIntros (CID13 Hq13) "Hcg Hpc".
    assert (Hpp7a : add_vec_int (mword_of_int (SO + 0x7a) : mword 64) 4
                    = mword_of_int (SO + 0x7e)) by pcw.
    iEval (rewrite Hpp7a) in "Hpc".
    (* ===== +0x7e c.li a5,2 ===== *)
    iApply (wp_cli_s_sconf (CID := CID13) (mword_of_int (SO + 0x7e)) Ra5
              (mword_of_int 2 : mword 6) (mword_of_int 2 : mword 64)
              M6 (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (soi_07e with "Htext"). }
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (M8 := <[Regidx Ra5 := regval_into_reg (mword_of_int 2 : mword 64)]> M6).
    assert (HM8a5 : (M8 !!! Regidx Ra5 : mword 64) = (mword_of_int 2 : mword 64))
      by (rewrite /M8; apply upd_eq).
    assert (HM8sp : so_sp sp0 M8)
      by (rewrite /so_sp /M8 upd_ne; [exact HM6sp | nz]).
    assert (HM8s0 : (M8 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M8 upd_ne; [exact HM6s0 | nz]).
    assert (HM8s1 : (M8 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M8 upd_ne; [exact HM6s1 | nz]).
    assert (HM8s2 : (M8 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /M8 upd_ne; [exact HM6s2 | nz]).
    assert (HM8s3 : (M8 !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64))
      by (rewrite /M8 upd_ne; [exact HM6s3 | nz]).
    assert (HM8thr : so_thr m M8).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /M8 upd_ne; [| regne].
      exact (HM6thr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp7e : add_vec_int (mword_of_int (SO + 0x7e) : mword 64) 2
                    = mword_of_int (SO + 0x80)) by pcw.
    iEval (rewrite Hpp7e) in "Hpc".
    (* ===== +0x80 sw a5,0(s2) -- f->type = FD_INODE ===== *)
    assert (Had80 : a_ftype kf
                    = add_vec (M8 !!! Regidx Rs2 : mword 64)
                        (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite HM8s2. unfold a_ftype. symmetry. apply addv_sext0. }
    assert (Had80' : a_ftype kf
                     = add_vec (rget M8 Rs2)
                         (sign_extend' 64 (mword_of_int 0 : mword 12)))
      by (rgne; exact Had80).
    iEval (rewrite Had80') in "Hfty".
    assert (Hvv80 : trunc32 (M8 !!! Regidx Ra5 : mword 64) = FD_INODE).
    { rewrite HM8a5. unfold FD_INODE. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_sw_s_sconf (CID := CID14) (mword_of_int (SO + 0x80)) Ra5 Rs2
              (mword_of_int 0 : mword 12) M8 (K - 24)%nat (fc_type Cf) b
              with "Hcg Hpc [] Hfty").
    { iApply (soi_080 with "Htext"). }
    iIntros (CID15 Hq15) "Hcg Hpc Hfty".
    iEval (rgne) in "Hfty". iEval (rgne) in "Hfty".
    iEval (rewrite -Had80 Hvv80) in "Hfty".
    assert (Hpp80 : add_vec_int (mword_of_int (SO + 0x80) : mword 64) 4
                    = mword_of_int (SO + 0x84)) by pcw.
    iEval (rewrite Hpp80) in "Hpc".
    (* ===== +0x84 sw zero,32(s2) -- f->off = 0 ===== *)
    (* r25 item 24: the slot's off cell arrives FREE (nobody owns a view of
       it); the store of zero re-establishes the word at the running
       context ([wp_sw_zero_s_sconf_free]), and that word is what the
       publish deposits into the fd's box. *)
    iEval (rewrite proto_store_free /a_foff /foff_of) in "Hfree".
    iApply (wp_sw_zero_s_sconf_free (kt := KT1) (ktd := KT0) (CID := CID15) (mword_of_int (SO + 0x84)) Rs2
              (mword_of_int 32 : mword 12) M8 (K - 24)%nat b
              with "Hcg Hpc [] [Hfree]").
    { iApply (soi_084 with "Htext"). }
    { iEval (rgne; rewrite HM8s2). iExact "Hfree". }
    iIntros (CID16 Hq16) "Hcg Hpc Hfoff".
    iEval (rgne; rewrite HM8s2) in "Hfoff".
    iEval (rewrite /wordw_pointsto; change (Z.to_nat 4) with 4%nat;
           rewrite -TsoCtx.ctx_word4_pointsto_unfold) in "Hfoff".
    assert (Hpp84 : add_vec_int (mword_of_int (SO + 0x84) : mword 64) 4
                    = mword_of_int (SO + 0x88)) by pcw.
    iEval (rewrite Hpp84) in "Hpc".
    iDestruct (cpu_own_transport CID8 CID16 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID8 CID16 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID8 CID16 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID16)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    (* the [beq] fell through, so the node is NOT a device and the
       descriptor is FD_INODE at the walk's own inum *)
    assert (Hndz : bv_unsigned (di_type dn) <> FsImg.T_DEVICE_z).
    { intros Hc. apply Hnd3. apply bv_eq. rewrite Hc.
      vm_compute. reflexivity. }
    (* THE OFFSET SHADOW IS MINTED HERE, beside the word the store just
       wrote: the AU's descriptor type [FdInode inum γo] has to name it
       before the publication runs, so the name exists from the store on
       and the box is born holding both (ProofSysOpenParts.so_deposit). *)
    iApply fupd_wp.
    iMod (off_gv_alloc (bv_unsigned (mword_of_int 0 : mword 32))) as (γo) "Hgv".
    iModIntro.
    iApply (Stores.so_stores_au (CID0 := CID16) gf gs jx gl pd pav pu
              gil gisl
 kk qi s gy loy tly inum dn bm kf fd ll pn FD_INODE
              (fc_readable Cf) (fc_writable Cf) (fc_pipe Cf) (fc_ip Cf)
              (fc_major Cf) om (mword_of_int 0 : mword 32) lo nsj u pidv dqb
              dqs U sts m M8 sp0 K eb b lks w6 w24 bp
              data vom pl P Pmiss Φo Φt (FdInode (bv_unsigned inum) γo) γo
              Hqs HKiu HKeo HKit HK24 Kpop Hkk Hinb Hgeom Hsize
              Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog Hcovb Hu2 Hj Hgl Hlkempty
              Hkf Hfdlt Hlen Hfrees (or_introl eq_refl) Hdir
              (fun _ => off_wf_zero)
              Hom
              ltac:(intros Hq; exfalso; exact (Hndz Hq))
              ltac:(intros _; split; reflexivity)
              Hal23 Hsp0 HM8sp HM8thr HM8s0 HM8s1 HM8s2 HM8s3 Hal
              with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                    Hitinv Hesck Hireg Hslkk Hslkd [//] Hfly Hclaimsy Hdep Hoffr Hidev Hiinum
                    Hivalid Hflat Hshot Hfrz Hkeep Hru Hfref Hflive Hfpn Hfty Hfrd
                    Hfwr Hfpip Hfmaj Hfip [Hfoff Hgv] Hiru Hcore Howe Hprocs Hdev Hgeo
                    Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hfrag Hauth Hf1 Hf2 Hf3 Hf4
                    Hf5 Hf6 HbP H23lo H23hi H24 HP Hobs Htc Hcont").
    { try (rewrite (bool_decide_eq_true_2 _ eq_refl)). iFrame "Hfoff Hgv". }
  Qed.

End ProofSysOpenAUAlloc.

End SysOpenAUAlloc.
