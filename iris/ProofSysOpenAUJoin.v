(* ProofSysOpenAUJoin.v -- THE JOIN AT +0x4a AND ARM D-FAIL, at the ARMED
   post: [ProofSysOpen.so_join] with the AU residue threaded and the DEVICE
   arm's major bound EARNED here and relayed down.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the open AU
   prover).  A PARALLEL block beside the landed one.

   THE ONLY ABSTRACT THING THIS BLOCK DOES is item (6) of
   [SpecSysOpenAU]'s prover list: the [lhu] + [bltu] SINGLE unsigned
   compare that decides [0 <= ma <= NDEV_max] (a negative short zero-extends
   past 9, so one branch settles both halves of the C's disjunction).  The
   contract's DEVICE arm asserts that bound, and this is where it is paid;
   below the join it travels as a premise.

   ARM D-FAIL moves no fs-abstract state: the observation fired far above,
   in the walk block, and the trunc commit is still in hand, so the arm is
   [ProofSysOpenAUParts.so_arm_fail] at the landed tail's own payout. *)
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
Require Import RegFile WpNext.
Require Import WpMmodeLeafBase.
Require Import StackOwn.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import WpLock.
Require Import WpSconfBtype.
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
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
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
Require Import ProofSysOpenAUAlloc.
Require Import ProofSysOpen.   (* [so_neq_of_eq] / [so_neq_of_ne] / [so_bud_iput] *)
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

Module SysOpenAUJoin (Iunlock : IUNLOCK) (Iunlockput : IUNLOCKPUT)
                     (EndOp : END_OP) (Fileclose : FILECLOSE)
                     (Itrunc : ITRUNC) (Filealloc : FILEALLOC)
                     (Fdalloc : FDALLOC).

Module Alloc := SysOpenAUAlloc Iunlock Iunlockput EndOp Fileclose Itrunc
                               Filealloc Fdalloc.
Module Tails := SysOpenTails Iunlock Iunlockput EndOp Fileclose.

Section ProofSysOpenAUJoin.
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
  (*  THE JOIN AT +0x4a, AND ARM D-FAIL.                                 *)
  (*                                                                    *)
  (*    lh a4,68(s1) ; c.li a5,3 ; bne -> +0x5e                          *)
  (*    lhu a4,70(s1) ; c.li a5,9 ; bltu 9 <u a4 -> +0x116               *)
  (*                                                                    *)
  (*  ENTERED FROM BOTH ARMS with [ip] LOCKED: the O_CREATE arm's create *)
  (*  and the else arm's namei/ilock/T_DIR refusal.  Everything it needs *)
  (*  about which arm ran is in ONE pure premise -- [di_type = T_DIR ->  *)
  (*  om = 0], which is [so_pay_witness]'s second half and the theorem   *)
  (*  of this walk.                                                     *)
  (*                                                                    *)
  (*  THE [major] BOUNDS CHECK IS ONE UNSIGNED TEST, NOT TWO: the [lhu]  *)
  (*  zero-extends, so a negative [short] lands at or above 0x8000 > 9   *)
  (*  and the single [bltu] decides both halves of the C's disjunction.  *)
  (* ================================================================== *)
  Lemma so_join_au `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gfl gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (gil gisl : gname)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (om lo : mword 32) (nsj : nat)
      (u : nat) (pidv : mword 32) (dqb dqs : dfrac)
      (U : ustate)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w4 w5 w6 w24 : mword 64)
      (bp : nat -> bv 8)
      (* ---- the AU side ---- *)
      (data : nat -> list (bv 8))
      (vom : mword 64) (pl : list (bv 8))
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ) :
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
    (* ---- the AU side ---- *)
    om = arg_int32 vom ->
    is_aligned_paddr (Physaddr (pa_stk sp0 23)) 8 = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 M -> so_thr m M ->
    (M !!! Regidx Rs0 : mword 64) = sp0 ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    so_al sp0 ->
    (* the block takes [fileclose]'s loan off the top of the allowance
       ([so_iref_take]); see the [iref_slots nsj] row below. *)
    (1 <= nsj)%nat ->
    sie_cap_gpr KT1 M (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0x4a)) -∗
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
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok fsc_ic kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s (i_lock (ientry kk)) pidv -∗
    ic_tx_dep fsc_ic kk s icfg_dev inum gy -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} icfg_dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    so_flat kk inum dn bm data -∗
    ity_shot gy (di_type dn) -∗
    (* the payload's freeze token (§3.9, RULING A-prime), relayed to
       [so_tail_s]'s iunlock *)
    ifreeze_off (bv_unsigned inum) -∗
    inode_ref_short_gen kk (qi + s)%Qp qi icfg_dev inum gy -∗
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
    (* THE ALLOWANCE, PASSED STRAIGHT DOWN.  This block spends nothing of
       its own; [so_alloc] below is what takes [fileclose]'s loan off the
       top, which is where the [1 <= nsj] premise goes. *)
    iref_slots nsj -∗
    fd_slot -∗
    (* the descriptor-state fragments, threaded exactly as the fd unit above
       is: sys_open spends one access, at the settle. *)
    fd_frags_any (pv_fdg (us_V U)) -∗
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
    atrunc_commit_at (fs_gamma_L fsc_fs) ∅ Φt -∗
    wp_next true (proc_addr jx)
      (so_cont_au gf nsj
               dqb dqs (proc_addr jx) pidv vom U P Pmiss Φo Φt m K eb b lks) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hkk Hinb Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk
           Hiblog Hcovb Hiu Hj Hgl Hlkempty Hdir Hom Hal23 Hsp0 HMsp HMthr
           HMs0 HMs1 HMs2 HMs3 Hal Hnspos.
    pose proof HK as HKfull.
    destruct (so_kb K HK) as (HKcr & HKna & HKai & HKas & HKbo & HKeo & HKil &
                              HKiu & HKit & HKip & HKup & HKfc & HKfa & HKfd &
                              HK10 & HK24 & Kpop).

    iIntros "Hcg Hown Htce Hcce #Htext #Hdata Hpc #Hpe #Hftab #Hbio #Hlog
              Hseam Hgen #Hitab #Hitinv #Hesck #Hireg #Hropen #Hslkk Hslkd Hdep
              Hidev Hiinum Hivalid Hflat #Hshot Hfrz Hkeep Hru Hpriv #Hprocs #Hdev #Hgeo
              #Hdlk Hop Hsbb Hsbi #Hbmres Hbsl Hisl Hfds Hfrag Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
              HbP H23lo H23hi H24 HP Hobs Htc Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0x4a lh a4,68(s1) ===== *)
    iDestruct (so_flat_meta with "Hflat") as "[Hmeta Hlback]".
    iDestruct (so_type_acc with "Hmeta") as "[Hity Hmback]".
    iEval (rewrite /i_type) in "Hity".
    iApply (wp_lh_s_sconf (CID := CID0) (kt := KT1) (ktd := KT0) (mword_of_int (SO + 0x4a)) Ra4 Rs1
              (mword_of_int 68 : mword 12) M (K - 24)%nat
              (di_type dn : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hity]").
    { iApply (soi_04a with "Htext"). }
    { iEval (rgne; rewrite HMs1). iExact "Hity". }
    iIntros (CID1 Hq1) "Hcg Hpc Hity".
    iEval (rgne; rewrite HMs1) in "Hity".
    iDestruct ("Hmback" with "[Hity]") as "Hmeta";
      [iEval (rewrite /i_type); iExact "Hity" |].
    iDestruct ("Hlback" with "Hmeta") as "Hflat".
    set (M1 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_type dn : mword 16) : mword 64)]> M).
    assert (HM1a4 : (M1 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /M1; apply upd_eq).
    assert (Hpp4a : add_vec_int (mword_of_int (SO + 0x4a) : mword 64) 4
                    = mword_of_int (SO + 0x4e)) by pcw.
    iEval (rewrite Hpp4a) in "Hpc".
    (* ===== +0x4e c.li a5,3 ===== *)
    iApply (wp_cli_s_sconf (CID := CID1) (mword_of_int (SO + 0x4e)) Ra5
              (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64)
              M1 (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (soi_04e with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Ra5 := regval_into_reg (mword_of_int 3 : mword 64)]> M1).
    assert (HM2a4 : (M2 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1a4 | nz]).
    assert (HM2a5 : (M2 !!! Regidx Ra5 : mword 64) = (mword_of_int 3 : mword 64))
      by (rewrite /M2; apply upd_eq).
    assert (HM2sp : so_sp sp0 M2).
    { rewrite /so_sp /M2 upd_ne; [| nz]. rewrite /M1 upd_ne; [| nz].
      exact HMsp. }
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /M2 upd_ne; [| nz]. rewrite /M1 upd_ne; [| nz]. exact HMs0. }
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite /M2 upd_ne; [| nz]. rewrite /M1 upd_ne; [| nz]. exact HMs1. }
    assert (HM2s2 : (M2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /M2 upd_ne; [| nz]. rewrite /M1 upd_ne; [| nz]. exact HMs2. }
    assert (HM2s3 : (M2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /M2 upd_ne; [| nz]. rewrite /M1 upd_ne; [| nz]. exact HMs3. }
    assert (HM2thr : so_thr m M2).
    { intros c Hc N2b N8 N9 N18 N19.
      rewrite /M2 upd_ne; [| regne]. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp4e : add_vec_int (mword_of_int (SO + 0x4e) : mword 64) 2
                    = mword_of_int (SO + 0x50)) by pcw.
    iEval (rewrite Hpp4e) in "Hpc".
    (* ===== +0x50 bne a4,a5, +0x5e ===== *)
    destruct (decide (di_type dn = (mword_of_int 3 : mword 16))) as [Hdev3 | Hnd3].
    2:{ (* ---- not a device: the [major] test is skipped ---- *)
      iApply (wp_bne_taken_s_sconf (CID := CID2) (mword_of_int (SO + 0x50))
                (mword_of_int 14 : mword 13) Ra5 Ra4 M2 (K - 24)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HM2a4 HM2a5;
                      exact (so_neq_of_ne _ _
                               (so_ty_ne (di_type dn) 3 so_tdev_range Hnd3)))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_050 with "Htext"). }
      iIntros (CID3 Hq3). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg50 : add_vec (mword_of_int (SO + 0x50) : mword 64)
                        (sign_extend' 64 (mword_of_int 14 : mword 13))
                      = mword_of_int (SO + 0x5e)) by pcw.
      iEval (rewrite Htg50) in "Hpc".
      iDestruct (cpu_own_transport CID0 CID3 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CID0 CID3 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
      iDestruct (cpu_claim_ext_transport CID0 CID3 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID3)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (Alloc.so_alloc_au (CID0 := CID3) gfl gf gs jx gl pd pav pu
                gil gisl
 kk qi s gy inum dn bm om lo nsj u
                pidv dqb dqs U m M2 sp0 K eb b lks w4 w5 w6 w24 bp
                data vom pl P Pmiss Φo Φt
                HKfull Hkk Hinb Hgeom Hsize Hbm0 Hbmcov Hbmlog
                Hist0 Hiblk Hiblog Hcovb Hiu Hj Hgl Hlkempty Hdir Hom
                ltac:(intros Hq; exfalso; apply Hnd3; apply bv_eq;
                      rewrite Hq; vm_compute; reflexivity)
                Hal23 Hsp0
                HM2sp HM2thr HM2s0 HM2s1 HM2s2 HM2s3 Hal Hnspos
                with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpe Hftab Hbio Hlog
                      Hseam Hgen Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd
                      Hdep Hidev Hiinum Hivalid Hflat Hshot Hfrz Hkeep Hru Hpriv Hprocs
                      Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hfrag Hf1
                      Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23lo H23hi H24
                      HP Hobs Htc Hcont"). }
    (* ---- T_DEVICE: the [major] bounds test ---- *)
    iApply (wp_bne_fall_s_sconf (CID := CID2) (mword_of_int (SO + 0x50))
              (mword_of_int 14 : mword 13) Ra5 Ra4 M2 (K - 24)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HM2a4 HM2a5;
                    exact (so_neq_of_eq _ _
                             (so_ty_eq (di_type dn) 3 so_tdev_range Hdev3)))
              with "Hcg Hpc []").
    { iApply (soi_050 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc".
    assert (Hpp50 : add_vec_int (mword_of_int (SO + 0x50) : mword 64) 4
                    = mword_of_int (SO + 0x54)) by pcw.
    iEval (rewrite Hpp50) in "Hpc".
    (* ===== +0x54 lhu a4,70(s1) -- ip->major, ZERO extended ===== *)
    iDestruct (so_flat_meta with "Hflat") as "[Hmeta Hlback]".
    iDestruct (so_maj_acc with "Hmeta") as "[Himaj Hmback]".
    iEval (rewrite /i_major) in "Himaj".
    iApply (wp_lhu_s_sconf (CID := CID3) (kt := KT1) (ktd := KT0) (mword_of_int (SO + 0x54)) Ra4 Rs1
              (mword_of_int 70 : mword 12) M2 (K - 24)%nat
              (di_major dn : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Himaj]").
    { iApply (soi_054 with "Htext"). }
    { iEval (rgne; rewrite HM2s1). iExact "Himaj". }
    iIntros (CID4 Hq4) "Hcg Hpc Himaj".
    iEval (rgne; rewrite HM2s1) in "Himaj".
    iDestruct ("Hmback" with "[Himaj]") as "Hmeta";
      [iEval (rewrite /i_major); iExact "Himaj" |].
    iDestruct ("Hlback" with "Hmeta") as "Hflat".
    set (M3 := <[Regidx Ra4 := regval_into_reg
                  (zero_extend' 64 (di_major dn : mword 16) : mword 64)]> M2).
    assert (HM3a4 : (M3 !!! Regidx Ra4 : mword 64)
                    = (zero_extend' 64 (di_major dn : mword 16) : mword 64))
      by (rewrite /M3; apply upd_eq).
    assert (Hpp54 : add_vec_int (mword_of_int (SO + 0x54) : mword 64) 4
                    = mword_of_int (SO + 0x58)) by pcw.
    iEval (rewrite Hpp54) in "Hpc".
    (* ===== +0x58 c.li a5,9 ===== *)
    iApply (wp_cli_s_sconf (CID := CID4) (mword_of_int (SO + 0x58)) Ra5
              (mword_of_int 9 : mword 6) (mword_of_int 9 : mword 64)
              M3 (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (soi_058 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (M4 := <[Regidx Ra5 := regval_into_reg (mword_of_int 9 : mword 64)]> M3).
    assert (HM4a4 : (M4 !!! Regidx Ra4 : mword 64)
                    = (zero_extend' 64 (di_major dn : mword 16) : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3a4 | nz]).
    assert (HM4a5 : (M4 !!! Regidx Ra5 : mword 64) = (mword_of_int 9 : mword 64))
      by (rewrite /M4; apply upd_eq).
    assert (HM4sp : so_sp sp0 M4).
    { rewrite /so_sp /M4 upd_ne; [| nz]. rewrite /M3 upd_ne; [| nz].
      exact HM2sp. }
    assert (HM4s0 : (M4 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /M4 upd_ne; [| nz]. rewrite /M3 upd_ne; [| nz]. exact HM2s0. }
    assert (HM4s1 : (M4 !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite /M4 upd_ne; [| nz]. rewrite /M3 upd_ne; [| nz]. exact HM2s1. }
    assert (HM4s2 : (M4 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /M4 upd_ne; [| nz]. rewrite /M3 upd_ne; [| nz]. exact HM2s2. }
    assert (HM4s3 : (M4 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /M4 upd_ne; [| nz]. rewrite /M3 upd_ne; [| nz]. exact HM2s3. }
    assert (HM4thr : so_thr m M4).
    { intros c Hc N2b N8 N9 N18 N19.
      rewrite /M4 upd_ne; [| regne]. rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp58 : add_vec_int (mword_of_int (SO + 0x58) : mword 64) 2
                    = mword_of_int (SO + 0x5a)) by pcw.
    iEval (rewrite Hpp58) in "Hpc".
    (* ===== +0x5a bltu a5,a4, +0x116  [ARM D-FAIL] ===== *)
    destruct (Z_lt_le_dec 9 (bv_unsigned (di_major dn))) as [Hout | Hin].
    { (* ---- the major is out of range ---- *)
      iApply (wp_bltu_taken_s_sconf (CID := CID5) (mword_of_int (SO + 0x5a))
                (mword_of_int 188 : mword 13) Ra4 Ra5 M4 (K - 24)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HM4a4 HM4a5;
                      exact (so_major_out (di_major dn) Hout))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_05a with "Htext"). }
      iIntros (CID6 Hq6). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg5a : add_vec (mword_of_int (SO + 0x5a) : mword 64)
                        (sign_extend' 64 (mword_of_int 188 : mword 13))
                      = mword_of_int (SO + 0x116)) by pcw.
      iEval (rewrite Htg5a) in "Hpc".
      iDestruct (so_omode_join sp0 lo om Hal23 with "H23lo H23hi") as "H23".
      iDestruct (so_flat_close with "Hflat") as "Hload".
      iDestruct (proc_priv_bare_acc with "Hpriv") as "[Hpbare Hpback]".
      iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep".
      iDestruct (cpu_own_transport CID0 CID6 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CID0 CID6 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
      iDestruct (cpu_claim_ext_transport CID0 CID6 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
      iApply (Tails.so_tail_d (CID0 := CID6) gs jx gl pd pav pu
                gil gisl
 kk qi s gy inum dn bm u pidv
                (DfracOwn (1/4)) dqb dqs m M4 sp0 K eb b lks w4 w5 w6
                (word_of_words lo om) w24 bp U
                HKup HKeo HK24 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
                Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HM4sp HM4thr
                HM4s1 HM4s2 HM4s3 Hal
                with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                      Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd Hdep Hidev
                      Hiinum Hivalid Hload Hshot Hfrz Hkeep Hru Hsbb Hsbi Hbmres Hpbare
                      Hprocs Hdev Hgeo Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
                      HbP H23 H24
                      [Hpback Hfds Hfrag Hisl HP Hobs Htc Hcont]").
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf)
        "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpbare Hsbb Hsbi
         Hbsl Hislot".
      iDestruct ("Hpback" with "Hpbare") as "Hpriv".
      (* the loan was never spent on this arm: fold it back beside the unit
         the tail's iput released. *)
      iDestruct (iref_slots_combine nsj 1 with "Hisl Hislot") as "Hisl".
      replace (nsj + 1)%nat with (S nsj) by lia.
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf (S nsj) with "[%] [%] Hcg Hown Htce Hcce
                Hpc Hsbb Hsbi Hbsl Hisl [Hpriv Hfds Hfrag HP Hobs Htc]").
      { exact Hcsf. }
      { reflexivity. }
      { iApply (so_arm_fail gf (proc_addr jx) pidv vom P Pmiss Φo Φt U _ pl
                  (bv_unsigned inum) (era_node dn bm data) Ha0f
                  with "Hpriv Hfrag Hfds HP Hobs Htc"). } }
    (* ---- the major is a legal device index ---- *)
    iApply (wp_bltu_fall_s_sconf (CID := CID5) (mword_of_int (SO + 0x5a))
              (mword_of_int 188 : mword 13) Ra4 Ra5 M4 (K - 24)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HM4a4 HM4a5;
                    exact (so_major_in (di_major dn) Hin))
              with "Hcg Hpc []").
    { iApply (soi_05a with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    assert (Hpp5a : add_vec_int (mword_of_int (SO + 0x5a) : mword 64) 4
                    = mword_of_int (SO + 0x5e)) by pcw.
    iEval (rewrite Hpp5a) in "Hpc".
    (* ITEM (6), PAID: the [bltu] fell through, so the ZERO-EXTENDED
       halfword is at most 9 -- and that single compare IS the contract's
       [0 <= ma <= NDEV_max] (a negative short would have landed above
       0x8000).  Hoisted out of the application below: a [lia] inside an
       [ltac:] there sees the whole function context and starves. *)
    assert (Hmajb : bv_unsigned (di_type dn) = FsImg.T_DEVICE_z ->
                    0 <= bv_unsigned (di_major dn) <= NDEV_max).
    { intros _. split.
      - exact (proj1 (bv_unsigned_in_range _ (di_major dn))).
      - change NDEV_max with 9. exact Hin. }
    iDestruct (cpu_own_transport CID0 CID6 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID6 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID6 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID6)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    (* ITEM (6), PAID: the [bltu] fell through, so the zero-extended
       halfword is at most 9 -- which IS [0 <= ma <= NDEV_max]. *)
    iApply (Alloc.so_alloc_au (CID0 := CID6) gfl gf gs jx gl pd pav pu
              gil gisl
 kk qi s gy inum dn bm om lo nsj u
               pidv dqb dqs U m M4 sp0 K eb b lks w4 w5 w6 w24 bp
               data vom pl P Pmiss Φo Φt
               HKfull Hkk Hinb Hgeom Hsize Hbm0 Hbmcov Hbmlog
               Hist0 Hiblk Hiblog Hcovb Hiu Hj Hgl Hlkempty Hdir Hom
               Hmajb
               Hal23 Hsp0
               HM4sp HM4thr HM4s0 HM4s1 HM4s2 HM4s3 Hal Hnspos
               with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpe Hftab Hbio Hlog
                     Hseam Hgen Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd
                     Hdep Hidev Hiinum Hivalid Hflat Hshot Hfrz Hkeep Hru Hpriv Hprocs
                     Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hfrag Hf1
                     Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23lo H23hi H24
                     HP Hobs Htc Hcont").
  Qed.

End ProofSysOpenAUJoin.

End SysOpenAUJoin.
