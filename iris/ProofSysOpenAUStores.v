(* ProofSysOpenAUStores.v -- +0x88 .. +0xb4 AND THE +0x14e itrunc BLOCK, at
   the ARMED post: [ProofSysOpen.so_stores] with the O_TRUNC commit fired at
   the retag and the three success arms built where [ip->type] is known.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the open AU
   prover).  A PARALLEL block beside the landed one.

   ==== THE TRUNC FIRE REPLACES THE RETAG ===============================

   The landed block, after itrunc returns, moves the era row with
   [InodeRegion.ireg_top_retag] and re-seals the payload with
   [ProofSysOpenParts.so_trunc_loaded].  [FsAbsOpenFire.opf_atrunc_fire] IS
   that retag with the caller's two phases fused around its
   [ghost_map_update] -- same premise ([inode_local] at the truncated
   record, which the landed block already proves as [Hloctr]), same payout,
   plus the receipt.  So the O_TRUNC delta costs this block one lemma name
   and two row readings ([FsAbsOpenFire.opf_era_file_row] /
   [opf_trunc_row]); nothing else about the itrunc block moves.

   ==== WHY THE PAYLOAD ARRIVES PEELED ==================================

   [ProofSysOpenAUParts.so_flat], not [IcacheEscrow.ic_loaded]: the FILE
   arm's [bs0] is shared between the terminal observation (fired far above,
   in the walk block) and the trunc receipt, and both read it off THIS
   [data].  See that file's header.

   ==== WHERE THE ARM IS DECIDED ========================================

   Three exits, three arms: the +0xac exit (no O_TRUNC) and the +0xb4 exit
   (not a regular file) hand the trunc commit BACK, the +0x154 exit hands
   the RECEIPT.  Which of DEVICE / FILE / DIR is delivered is read off
   [di_type dn], whose enumeration is [inode_rec_local]'s (in the peeled
   payload) minus the zero [inode_ok] refutes.  The DEVICE arm's major
   bound is the join's [bltu], relayed as a premise. *)
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
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import OffBox.   (* [off_rows] / [off_free] -- the fd off cell (r25 item 24) *)
Require Import DirView.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecArgint.
Require Import SpecEndOp.
Require Import SpecIunlock.
Require Import SpecIunlockput.
Require Import SpecFileclose.
Require Import SpecFdalloc.
Require Import SpecItrunc.
Require Import CodeSysOpen.
Require Import ProofSysOpenParts.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.

Require Import ConsoleInv.
Require Import PathElems.
Require Import FsTree.
Require Import FsBytesGamma.
Require Import SpecSysOpenAU.
Require Import FsAbsOpenFire.
Require Import ProofSysOpenAUBits.
Require Import ProofSysOpenAUParts.
Require Import ProofSysOpenAUPub.
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

Module SysOpenAUStores (Iunlock : IUNLOCK) (Iunlockput : IUNLOCKPUT)
                       (EndOp : END_OP) (Fileclose : FILECLOSE)
                       (Itrunc : ITRUNC).

Module Pub := SysOpenAUPub Iunlock Iunlockput EndOp Fileclose.

Section ProofSysOpenAUStores.
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
  (*  +0x88 .. +0xb4 AND THE +0x14e itrunc BLOCK.                        *)
  (*                                                                    *)
  (*    sd s1,24(s2)          f->ip = ip                                 *)
  (*    lw a5,-180(s0)        the omode word, read ONCE for three masks  *)
  (*    andi/xori/sb          f->readable = !(omode & O_WRONLY)          *)
  (*    andi/snez/sb          f->writable = (omode & 3) != 0             *)
  (*    andi a5,a5,1024 ; c.beqz -> +0xb8                                *)
  (*    lh a4,68(s1) ; c.li a5,2 ; beq -> +0x14e   itrunc(ip)            *)
  (*                                                                    *)
  (*  ENTERED FROM TWO PLACES -- the FD_INODE fall-through at +0x84 and  *)
  (*  the FD_DEVICE block's [c.j] at +0x14c -- which is why the two      *)
  (*  type-dependent cells ([f->type], [f->major], and whether [f->off]  *)
  (*  was zeroed) are PARAMETERS here and not values.                    *)
  (*                                                                    *)
  (*  THE OMODE SLOT IS REJOINED the moment the [lw] gives its cell back: *)
  (*  nothing below reads the frame again, and every exit wants slot 23   *)
  (*  whole.                                                             *)
  (* ================================================================== *)
  Lemma so_stores_au `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (gil gisl : gname)
      (kk : nat) (qi s : Qp) (gy : gname) (loy tly : nat) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (kf fd : nat) (l : list nat) (pn : fpnames)
      (tyw : mword 32) (rd0 wr0 : bv 8) (pip ipold : mword 64) (maj : bv 16)
      (om voff lo : mword 32) (nsj : nat)
      (u : nat) (pidv : mword 32) (dqb dqs : dfrac)
      (U : ustate) (sts : list fdstate)
      (m N : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w6 w24 : mword 64)
      (bp : nat -> bv 8)
      (* ---- the AU side ---- *)
      (data : nat -> list (bv 8))
      (vom : mword 64) (pl : list (bv 8))
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (t : fdtype) :
    qi = s ->   (* r25 shapes: the parked ident fraction IS the travelling share (so_publish) *)
    (K_iunlock <= K - 24)%nat -> (K_end_op <= K - 24)%nat ->
    (K_itrunc <= K - 24)%nat ->
    (24 <= K)%nat -> ((K - 24) + 24 = K)%nat ->
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
    (2 <= u)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    (kf < NFILE)%nat -> (fd < NOFILE)%nat ->
    length (pv_ofile (us_V U)) = NOFILE ->
    fd_frees (pv_ofile (us_V U)) = fd :: l ->
    (tyw = FD_INODE \/ tyw = FD_DEVICE) ->
    (bv_unsigned (di_type dn) = T_DIR_z -> om = (mword_of_int 0 : mword 32)) ->
    (tyw = FD_INODE -> off_wf voff) ->
    (* ---- the AU side: the omode word is the caller's argument, and the
       two type-dependent cells the block above wrote agree with the record
       (the DEVICE arm's major bound is the join's [bltu], relayed) ---- *)
    om = arg_int32 vom ->
    (bv_unsigned (di_type dn) = FsImg.T_DEVICE_z ->
       tyw = FD_DEVICE /\ maj = di_major dn
       /\ 0 <= bv_unsigned (di_major dn) <= NDEV_max
       /\ t = FdDevice (bv_unsigned (di_major dn))) ->
    (bv_unsigned (di_type dn) <> FsImg.T_DEVICE_z ->
       tyw = FD_INODE /\ t = FdInode (bv_unsigned inum)) ->
    is_aligned_paddr (Physaddr (pa_stk sp0 23)) 8 = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 N -> so_thr m N ->
    (N !!! Regidx Rs0 : mword 64) = sp0 ->
    (N !!! Regidx Rs1 : mword 64) = ientry kk ->
    (N !!! Regidx Rs2 : mword 64) = fnode kf ->
    (N !!! Regidx Rs3 : mword 64) = (mword_of_int (Z.of_nat fd) : mword 64) ->
    so_al sp0 ->
    sie_cap_gpr KT1 N (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0x88)) -∗
    panic_env -∗
    bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
    log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
    fs_crash_seam fsc_cov fsc_logst -∗
    gen_cert -∗
    itable_inv -∗
    ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kk -∗
    ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
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
    (* the fresh slot, six cells PLAIN and [f->ip] WHOLE *)
    fref_tok gf kf 1 -∗
    flive_tok kf -∗
    fpay_tok gf kf 1 pn -∗
    a_ftype kf     ↦₄ tyw -∗
    a_freadable kf ↦ₘ rd0 -∗
    a_fwritable kf ↦ₘ wr0 -∗
    a_fpipe kf     ↦₈ pip -∗
    a_fmajor kf    ↦₂ maj -∗
    a_fip kf       ↦₈ ipold -∗
    (if bool_decide (tyw = FD_INODE) then a_foff kf ↦₄ voff else off_free kf 1) -∗
    (* the untyped slot's own unit, on its way back to the ledger -- see
       [so_tail_pub]'s row for why the entry ends up owing nothing *)
    iref_slot -∗
    proc_priv_core (proc_addr jx) pidv U -∗
    proc_ofiles_owe gf (pv_fdg (us_V U)) (proc_addr jx)
      (pv_ofile (upd_ofile (us_V U) fd (fnode kf))) ({[fd]} ∪ ∅) -∗
    procs_inv gs -∗
    dev_inv fsc_uart fsc_disk -∗
    disk_geom fsc_disk pd pav pu -∗
    is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
    log_opb icfg_log u -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
    bslots 3 -∗
    iref_slots nsj -∗
    fd_slot -∗
    (* the descriptor-state fragments, threaded exactly as the fd unit above
       is: sys_open spends one access, at the settle. *)
    fd_frags (pv_fdg (us_V U)) sts -∗
    (* ...and the descriptor's own AUTHORITY, at [FdClosed]: fdalloc handed
       it out when it made the cell non-null, and the settle below moves it
       to the new file's type. *)
    fd_st_auth (pv_fdg (us_V U)) fd FdClosed -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
    (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₄[KT1] lo -∗
    (pa_add (pa_stk sp0 23) 4) ↦₄[KT1] om -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    (* ---- THE AU RESIDUE: the cursor at the end of the walk, the FIRED
       terminal observation, and the trunc commit still in hand ---- *)
    P (length (path_elems pl)) (bv_unsigned inum) -∗
    so_obs Φo (bv_unsigned inum) (era_node dn bm data) -∗
    atrunc_commit_at (fs_gamma_L fsc_fs) fsabsE Φt -∗
    wp_next true (proc_addr jx)
      (so_cont_au gf nsj
               dqb dqs (proc_addr jx) pidv vom U sts P Pmiss Φo Φt m K eb b lks) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hqs HKiu HKeo HKit HK24 Kpop Hkk Hinb Hgeom Hsize Hbm0
           Hbmcov Hbmlog Hist0 Hiblk Hiblog Hcovb Hu2 Hj Hgl Hlkempty Hkf
           Hfdlt Hlen Hfrees Htyor Hdir Hwf Hom Htd Hti Hal23 Hsp0 HNsp HNthr
           HNs0 HNs1 HNs2 HNs3 Hal.

    (* [2 <= u] as a SHAPE, not an inequality: itrunc's uncredited entry
       level is [it_entry false u2 = S (S u2)], and destructing here is what
       lets the [log_op] hypothesis meet it without a rewrite. *)
    destruct u as [| [| u2]]; [ exfalso; lia | exfalso; lia | ].
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              #Hitinv #Hesck #Hireg #Hslkk Hslkd %Hley #Hfly #Hclaimsy Hdep Hoffr Hidev Hiinum
              Hivalid Hflat #Hshot Hfrz Hkeep Hru Hfref Hflive Hfpn Hfty Hfrd Hfwr
              Hfpip Hfmaj Hfip Hfoff Hiru Hcore Howe #Hprocs #Hdev #Hgeo #Hdlk Hop
              Hsbb Hsbi #Hbmres Hbsl Hisl Hfds Hfrag Hauth Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP
              H23lo H23hi H24 HP Hobs Htc Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ---- THE ARM'S THREE FACTS, read once off the peeled payload:
       [inode_rec_local]'s enumeration minus the zero [inode_ok] refutes, and
       the two conditional readings of the type-dependent cells. ---- *)
    iDestruct (so_flat_pure with "Hflat") as %[Hok0 Hrl0].
    assert (Htyen : bv_unsigned (di_type dn) = T_DIR_z
                    \/ bv_unsigned (di_type dn) = FsImg.T_FILE_z
                    \/ bv_unsigned (di_type dn) = FsImg.T_DEVICE_z).
    { destruct Hrl0 as [Hen _].
      destruct Hok0 as (_ & _ & _ & Hnz0 & _ & _ & _).
      destruct Hen as [Hz | Hrest]; [exfalso; exact (Hnz0 Hz) | exact Hrest]. }
    assert (Hdevb : bv_unsigned (di_type dn) = FsImg.T_DEVICE_z ->
                    0 <= bv_unsigned (di_major dn) <= NDEV_max
                    /\ t = FdDevice (bv_unsigned (di_major dn)))
      by (intros Hq; destruct (Htd Hq) as (_ & _ & Ha & Hbq); exact (conj Ha Hbq)).
    assert (Hinob : bv_unsigned (di_type dn) <> FsImg.T_DEVICE_z ->
                    t = FdInode (bv_unsigned inum))
      by (intros Hq; exact (proj2 (Hti Hq))).
    (* THE OWNER'S RULING (2026-08-29), AND THIS LANE OWES IT NOTHING NEW:
       [Htd] already says a T_DEVICE inode was stored as FD_DEVICE, so the
       contrapositive IS the payload's fifth conjunct.  [ProofSysOpen]'s
       landed twin has to take it as a premise because its store block
       carries no such tie -- the AU's [t] is what forced one here. *)
    assert (Hdvw : tyw = FD_INODE ->
                   bv_unsigned (di_type dn) <> FsImg.T_DEVICE_z).
    { intros Hi Hq. destruct (Htd Hq) as (Hd & _). rewrite Hi in Hd.
      apply (f_equal bv_unsigned) in Hd. by vm_compute in Hd. }
    assert (Hdirk : bv_unsigned (di_type dn) = T_DIR_z -> om_arg vom = 0).
    { intros Hq. rewrite -soau_om_arg -Hom (Hdir Hq). vm_compute. reflexivity. }
    (* ===== +0x88 sd s1,24(s2) -- f->ip = ip ===== *)
    iEval (rewrite /a_fip /foff_of) in "Hfip".
    iApply (wp_sd_s_sconf (kt := KT1) (ktd := KT0) (CID := CID0) (mword_of_int (SO + 0x88)) Rs1 Rs2
              (mword_of_int 24 : mword 12) N (K - 24)%nat ipold b
              with "Hcg Hpc [] [Hfip]").
    { iApply (soi_088 with "Htext"). }
    { iEval (rgne; rewrite HNs2). iExact "Hfip". }
    iIntros (CID1 Hq1) "Hcg Hpc Hfip".
    iEval (rgne; rewrite HNs2; rgne; rewrite HNs1) in "Hfip".
    assert (Hpp88 : add_vec_int (mword_of_int (SO + 0x88) : mword 64) 4
                    = mword_of_int (SO + 0x8c)) by pcw.
    iEval (rewrite Hpp88) in "Hpc".
    (* ===== +0x8c lw a5,-180(s0) -- the omode word ===== *)
    iApply (wp_lw_s_sconf (CID := CID1) (mword_of_int (SO + 0x8c)) Ra5 Rs0
              (mword_of_int 3916 : mword 12) N (K - 24)%nat om b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [H23hi]").
    { iApply (soi_08c with "Htext"). }
    { iEval (rgne; rewrite HNs0; rewrite so_omode). iExact "H23hi". }
    iIntros (CID2 Hq2) "Hcg Hpc H23hi".
    iEval (rgne; rewrite HNs0; rewrite so_omode) in "H23hi".
    iDestruct (so_omode_join sp0 lo om Hal23 with "H23lo H23hi") as "H23".
    set (N1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 om : mword 64)]> N).
    assert (HN1a5 : (N1 !!! Regidx Ra5 : mword 64) = so_omv om)
      by (rewrite /N1 /so_omv; apply upd_eq).
    assert (HN1sp : so_sp sp0 N1)
      by (rewrite /so_sp /N1 upd_ne; [exact HNsp | nz]).
    assert (HN1s0 : (N1 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /N1 upd_ne; [exact HNs0 | nz]).
    assert (HN1s1 : (N1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /N1 upd_ne; [exact HNs1 | nz]).
    assert (HN1s2 : (N1 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /N1 upd_ne; [exact HNs2 | nz]).
    assert (HN1s3 : (N1 !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64))
      by (rewrite /N1 upd_ne; [exact HNs3 | nz]).
    assert (HN1thr : so_thr m N1).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /N1 upd_ne; [| regne].
      exact (HNthr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp8c : add_vec_int (mword_of_int (SO + 0x8c) : mword 64) 4
                    = mword_of_int (SO + 0x90)) by pcw.
    iEval (rewrite Hpp8c) in "Hpc".
    (* ===== +0x90 andi a4,a5,1 ===== *)
    iApply (wp_andi_s_sconf (CID := CID2) (mword_of_int (SO + 0x90)) Ra4 Ra5
              (mword_of_int 1 : mword 12) (so_and om 1) N1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HN1a5; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_090 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (N2 := <[Regidx Ra4 := regval_into_reg (so_and om 1)]> N1).
    assert (HN2a4 : (N2 !!! Regidx Ra4 : mword 64) = so_and om 1)
      by (rewrite /N2; apply upd_eq).
    assert (HN2a5 : (N2 !!! Regidx Ra5 : mword 64) = so_omv om)
      by (rewrite /N2 upd_ne; [exact HN1a5 | nz]).
    assert (HN2s2 : (N2 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /N2 upd_ne; [exact HN1s2 | nz]).
    assert (Hpp90 : add_vec_int (mword_of_int (SO + 0x90) : mword 64) 4
                    = mword_of_int (SO + 0x94)) by pcw.
    iEval (rewrite Hpp90) in "Hpc".
    (* ===== +0x94 xori a4,a4,1 ===== *)
    iApply (wp_xori_s_sconf (CID := CID3) (mword_of_int (SO + 0x94)) Ra4 Ra4
              (mword_of_int 1 : mword 12) (so_rd_word om) N2 (K - 24)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HN2a4; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_094 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (N3 := <[Regidx Ra4 := regval_into_reg (so_rd_word om)]> N2).
    assert (HN3a4 : (N3 !!! Regidx Ra4 : mword 64) = so_rd_word om)
      by (rewrite /N3; apply upd_eq).
    assert (HN3a5 : (N3 !!! Regidx Ra5 : mword 64) = so_omv om)
      by (rewrite /N3 upd_ne; [exact HN2a5 | nz]).
    assert (HN3s2 : (N3 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /N3 upd_ne; [exact HN2s2 | nz]).
    assert (Hpp94 : add_vec_int (mword_of_int (SO + 0x94) : mword 64) 4
                    = mword_of_int (SO + 0x98)) by pcw.
    iEval (rewrite Hpp94) in "Hpc".
    (* ===== +0x98 sb a4,8(s2) -- f->readable ===== *)
    iEval (rewrite /a_freadable /foff_of) in "Hfrd".
    iApply (wp_sb_s_sconf (kt := KT1) (ktd := KT0) (CID := CID4) (mword_of_int (SO + 0x98)) Ra4 Rs2
              (mword_of_int 8 : mword 12) N3 (K - 24)%nat rd0 b
              with "Hcg Hpc [] [Hfrd]").
    { iApply (soi_098 with "Htext"). }
    { iEval (rgne; rewrite HN3s2). iExact "Hfrd". }
    iIntros (CID5 Hq5) "Hcg Hpc Hfrd".
    iEval (rgne; rewrite HN3s2; rgne; rewrite HN3a4) in "Hfrd".
    assert (Hpp98 : add_vec_int (mword_of_int (SO + 0x98) : mword 64) 4
                    = mword_of_int (SO + 0x9c)) by pcw.
    iEval (rewrite Hpp98) in "Hpc".
    (* ===== +0x9c andi a4,a5,3 ===== *)
    iApply (wp_andi_s_sconf (CID := CID5) (mword_of_int (SO + 0x9c)) Ra4 Ra5
              (mword_of_int 3 : mword 12) (so_and om 3) N3 (K - 24)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HN3a5; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_09c with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (N4 := <[Regidx Ra4 := regval_into_reg (so_and om 3)]> N3).
    assert (HN4a4 : (N4 !!! Regidx Ra4 : mword 64) = so_and om 3)
      by (rewrite /N4; apply upd_eq).
    assert (HN4a5 : (N4 !!! Regidx Ra5 : mword 64) = so_omv om)
      by (rewrite /N4 upd_ne; [exact HN3a5 | nz]).
    assert (HN4s2 : (N4 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /N4 upd_ne; [exact HN3s2 | nz]).
    assert (Hpp9c : add_vec_int (mword_of_int (SO + 0x9c) : mword 64) 4
                    = mword_of_int (SO + 0xa0)) by pcw.
    iEval (rewrite Hpp9c) in "Hpc".
    (* ===== +0xa0 snez a4,a4 ===== *)
    iDestruct (sie_cap_gpr_x0 N4 (K - 24)%nat b (proc_addr jx) Rz
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%HN4x0 Hcg]".
    iApply (wp_sltu_s_sconf (CID := CID6) (mword_of_int (SO + 0xa0)) Ra4 Rz Ra4
              (so_wr_word om) N4 (K - 24)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HN4x0; rgne; rewrite HN4a4; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_0a0 with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (N5 := <[Regidx Ra4 := regval_into_reg (so_wr_word om)]> N4).
    assert (HN5a4 : (N5 !!! Regidx Ra4 : mword 64) = so_wr_word om)
      by (rewrite /N5; apply upd_eq).
    assert (HN5a5 : (N5 !!! Regidx Ra5 : mword 64) = so_omv om)
      by (rewrite /N5 upd_ne; [exact HN4a5 | nz]).
    assert (HN5s2 : (N5 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /N5 upd_ne; [exact HN4s2 | nz]).
    assert (Hppa0 : add_vec_int (mword_of_int (SO + 0xa0) : mword 64) 4
                    = mword_of_int (SO + 0xa4)) by pcw.
    iEval (rewrite Hppa0) in "Hpc".
    (* ===== +0xa4 sb a4,9(s2) -- f->writable ===== *)
    iEval (rewrite /a_fwritable /foff_of) in "Hfwr".
    iApply (wp_sb_s_sconf (kt := KT1) (ktd := KT0) (CID := CID7) (mword_of_int (SO + 0xa4)) Ra4 Rs2
              (mword_of_int 9 : mword 12) N5 (K - 24)%nat wr0 b
              with "Hcg Hpc [] [Hfwr]").
    { iApply (soi_0a4 with "Htext"). }
    { iEval (rgne; rewrite HN5s2). iExact "Hfwr". }
    iIntros (CID8 Hq8) "Hcg Hpc Hfwr".
    iEval (rgne; rewrite HN5s2; rgne; rewrite HN5a4) in "Hfwr".
    assert (Hppa4 : add_vec_int (mword_of_int (SO + 0xa4) : mword 64) 4
                    = mword_of_int (SO + 0xa8)) by pcw.
    iEval (rewrite Hppa4) in "Hpc".
    (* ---- the published CONTENT, and the six cells as [file_fields] ---- *)
    set (C := MkFContent tyw (trunc8 (so_rd_word om)) (trunc8 (so_wr_word om))
                pip (ientry kk) maj).
    iAssert (file_fields kf 1 C) with "[Hfty Hfrd Hfwr Hfpip Hfip Hfmaj]"
      as "Hflds".
    { rewrite /file_fields /C; cbn [fc_type fc_readable fc_writable fc_pipe
                                    fc_ip fc_major].
      rewrite /a_ftype /a_freadable /a_fwritable /a_fpipe /a_fip /a_fmajor
              /foff_of.
      iFrame "Hfty Hfrd Hfwr Hfpip Hfip Hfmaj". }
    (* the published content's type, in the shape the publication asks for *)
    assert (Hfdty : (fc_type C = FD_INODE /\ t = FdInode (bv_unsigned inum))
                   \/ (fc_type C = FD_DEVICE
                       /\ t = FdDevice (bv_unsigned (fc_major C)))).
    { destruct (decide (bv_unsigned (di_type dn) = FsImg.T_DEVICE_z))
        as [Hdv | Hnd].
      - destruct (Htd Hdv) as (Hw & Hm & _ & Ht).
        right. rewrite /C; cbn [fc_type fc_major]. rewrite Hw Hm.
        split; [reflexivity | exact Ht].
      - destruct (Hti Hnd) as [Hw Ht].
        left. rewrite /C; cbn [fc_type]. rewrite Hw.
        split; [reflexivity | exact Ht]. }
    (* ===== +0xa8 andi a5,a5,1024 -- O_TRUNC ===== *)
    iApply (wp_andi_s_sconf (CID := CID8) (mword_of_int (SO + 0xa8)) Ra5 Ra5
              (mword_of_int 1024 : mword 12) (so_and om 1024) N5 (K - 24)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HN5a5; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_0a8 with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (N6 := <[Regidx Ra5 := regval_into_reg (so_and om 1024)]> N5).
    assert (HN6a5 : (N6 !!! Regidx Ra5 : mword 64) = so_and om 1024)
      by (rewrite /N6; apply upd_eq).
    assert (HN6sp : so_sp sp0 N6).
    { rewrite /so_sp /N6 upd_ne; [| nz]. rewrite /N5 upd_ne; [| nz].
      rewrite /N4 upd_ne; [| nz]. rewrite /N3 upd_ne; [| nz].
      rewrite /N2 upd_ne; [| nz]. exact HN1sp. }
    assert (HN6s1 : (N6 !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite /N6 upd_ne; [| nz]. rewrite /N5 upd_ne; [| nz].
      rewrite /N4 upd_ne; [| nz]. rewrite /N3 upd_ne; [| nz].
      rewrite /N2 upd_ne; [| nz]. exact HN1s1. }
    assert (HN6s3 : (N6 !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64)).
    { rewrite /N6 upd_ne; [| nz]. rewrite /N5 upd_ne; [| nz].
      rewrite /N4 upd_ne; [| nz]. rewrite /N3 upd_ne; [| nz].
      rewrite /N2 upd_ne; [| nz]. exact HN1s3. }
    assert (HN6thr : so_thr m N6).
    { intros c Hc N2b N8 N9 N18 N19.
      rewrite /N6 upd_ne; [| regne]. rewrite /N5 upd_ne; [| regne].
      rewrite /N4 upd_ne; [| regne]. rewrite /N3 upd_ne; [| regne].
      rewrite /N2 upd_ne; [| regne].
      exact (HN1thr c Hc N2b N8 N9 N18 N19). }
    assert (Hppa8 : add_vec_int (mword_of_int (SO + 0xa8) : mword 64) 4
                    = mword_of_int (SO + 0xac)) by pcw.
    iEval (rewrite Hppa8) in "Hpc".
    (* ===== +0xac c.beqz a5, +0xb8 ===== *)
    destruct (eq_vec (so_and om 1024) (zero_reg : mword 64)) eqn:Htr.
    { (* ---- no O_TRUNC: straight to ARM S ---- *)
      iApply (wp_cbeqz_taken_s_sconf (CID := CID9) (mword_of_int (SO + 0xac))
                (mword_of_int 6 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                N6 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HN6a5; exact Htr)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_0ac with "Htext"). }
      iIntros (CID10 Hq10). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgac : add_vec (mword_of_int (SO + 0xac) : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13 (concat_vec (mword_of_int 6 : mword 8) ('b"0"))))
                      = mword_of_int (SO + 0xb8)) by pcw.
      iEval (rewrite Htgac) in "Hpc".
      iDestruct (cpu_own_transport CID0 CID10 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CID0 CID10 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
      iDestruct (cpu_claim_ext_transport CID0 CID10 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID10)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      (* the mask was empty, so the caller's O_TRUNC bit is CLEAR and the
         arm is the plain one at whatever [ip->type] says *)
      assert (Hntf : om_trunc vom = false).
      { apply (proj1 (soau_trunc_zero_iff vom)). rewrite -Hom.
        apply eq_vec_true_iff in Htr. rewrite Htr.
        apply bv_eq; vm_compute; reflexivity. }
      iDestruct (so_flat_close with "Hflat") as "Hload".
      iDestruct (so_arm_notr gf (proc_addr jx) pidv vom P Φo Φt U sts pl
                   (bv_unsigned inum) dn bm data t
                   (or_introl Hntf) Hdirk Hdevb Hinob Htyen
                   with "HP Hobs Htc") as "Harm".
      iApply (Pub.so_tail_pub_au (CID0 := CID10) gf gs jx gl pd pav pu
                gil gisl
 kk qi s gy loy tly inum dn bm kf fd l C pn om voff nsj
                (S (S u2)) pidv dqb dqs U sts m N6 sp0 K eb b lks w6
                (word_of_words lo om) w24 bp vom P Pmiss Φo Φt t
                Hqs HKiu HKeo HK24 Kpop Hkk Hinb Hgeom Hj Hgl Hlkempty Hkf
                Hfdlt Hlen Hfrees eq_refl Htyor eq_refl eq_refl Hdir Hdvw Hwf
                Hom Hfdty
                Hsp0 HN6sp HN6thr HN6s1 HN6s3 Hal
                with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                      Hitinv Hesck Hslkk Hslkd [//] Hfly Hclaimsy Hdep Hoffr Hidev Hiinum Hivalid
                      Hload Hshot Hfrz Hkeep Hru Hfref Hflive Hflds Hfpn Hfoff
                      Hiru Hcore Howe Hprocs Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres
                      Hbsl Hisl Hfds Hfrag Hauth Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                      Harm Hcont"). }
    (* ---- O_TRUNC set: the type test at +0xb4 ---- *)
    iApply (wp_cbeqz_fall_s_sconf (CID := CID9) (mword_of_int (SO + 0xac))
              (mword_of_int 6 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              N6 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HN6a5; exact Htr)
              with "Hcg Hpc []").
    { iApply (soi_0ac with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc".
    assert (Hppac : add_vec_int (mword_of_int (SO + 0xac) : mword 64) 2
                    = mword_of_int (SO + 0xae)) by pcw.
    iEval (rewrite Hppac) in "Hpc".
    (* ===== +0xae lh a4,68(s1) ===== *)
    iDestruct (so_flat_meta with "Hflat") as "[Hmeta Hlback]".
    iDestruct (so_type_acc with "Hmeta") as "[Hity Hmback]".
    iEval (rewrite /i_type) in "Hity".
    iApply (wp_lh_s_sconf (CID := CID10) (kt := KT1) (ktd := KT0) (mword_of_int (SO + 0xae)) Ra4 Rs1
              (mword_of_int 68 : mword 12) N6 (K - 24)%nat
              (di_type dn : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hity]").
    { iApply (soi_0ae with "Htext"). }
    { iEval (rgne; rewrite HN6s1). iExact "Hity". }
    iIntros (CID11 Hq11) "Hcg Hpc Hity".
    iEval (rgne; rewrite HN6s1) in "Hity".
    iDestruct ("Hmback" with "[Hity]") as "Hmeta";
      [iEval (rewrite /i_type); iExact "Hity" |].
    iDestruct ("Hlback" with "Hmeta") as "Hflat".
    set (N7 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_type dn : mword 16) : mword 64)]> N6).
    assert (HN7a4 : (N7 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /N7; apply upd_eq).
    assert (Hppae : add_vec_int (mword_of_int (SO + 0xae) : mword 64) 4
                    = mword_of_int (SO + 0xb2)) by pcw.
    iEval (rewrite Hppae) in "Hpc".
    (* ===== +0xb2 c.li a5,2 ===== *)
    iApply (wp_cli_s_sconf (CID := CID11) (mword_of_int (SO + 0xb2)) Ra5
              (mword_of_int 2 : mword 6) (mword_of_int 2 : mword 64)
              N7 (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (soi_0b2 with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc".
    set (N8 := <[Regidx Ra5 := regval_into_reg (mword_of_int 2 : mword 64)]> N7).
    assert (HN8a4 : (N8 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /N8 upd_ne; [exact HN7a4 | nz]).
    assert (HN8a5 : (N8 !!! Regidx Ra5 : mword 64) = (mword_of_int 2 : mword 64))
      by (rewrite /N8; apply upd_eq).
    assert (HN8sp : so_sp sp0 N8).
    { rewrite /so_sp /N8 upd_ne; [| nz]. rewrite /N7 upd_ne; [| nz].
      exact HN6sp. }
    assert (HN8s1 : (N8 !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite /N8 upd_ne; [| nz]. rewrite /N7 upd_ne; [| nz]. exact HN6s1. }
    assert (HN8s3 : (N8 !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64)).
    { rewrite /N8 upd_ne; [| nz]. rewrite /N7 upd_ne; [| nz]. exact HN6s3. }
    assert (HN8thr : so_thr m N8).
    { intros c Hc N2b N9b N9 N18 N19.
      rewrite /N8 upd_ne; [| regne]. rewrite /N7 upd_ne; [| regne].
      exact (HN6thr c Hc N2b N9b N9 N18 N19). }
    assert (Hppb2 : add_vec_int (mword_of_int (SO + 0xb2) : mword 64) 2
                    = mword_of_int (SO + 0xb4)) by pcw.
    iEval (rewrite Hppb2) in "Hpc".
    (* ===== +0xb4 beq a4,a5, +0x14e ===== *)
    destruct (decide (di_type dn = (mword_of_int 2 : mword 16))) as [Hfile | Hnf].
    2:{ (* not a regular file: no itrunc, straight to ARM S *)
      iApply (wp_beq_fall_s_sconf (CID := CID12) (mword_of_int (SO + 0xb4))
                (mword_of_int 154 : mword 13) Ra5 Ra4 N8 (K - 24)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HN8a4 HN8a5;
                      exact (so_ty_ne (di_type dn) 2 so_tfile_range Hnf))
                with "Hcg Hpc []").
      { iApply (soi_0b4 with "Htext"). }
      iIntros (CID13 Hq13) "Hcg Hpc".
      assert (Hppb4 : add_vec_int (mword_of_int (SO + 0xb4) : mword 64) 4
                      = mword_of_int (SO + 0xb8)) by pcw.
      iEval (rewrite Hppb4) in "Hpc".
      iDestruct (cpu_own_transport CID0 CID13 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CID0 CID13 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
      iDestruct (cpu_claim_ext_transport CID0 CID13 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID13)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      (* the type test failed, so the node is NOT a regular file and the
         trunc commit comes back whatever the O_TRUNC bit said *)
      assert (Hnf2 : bv_unsigned (di_type dn) <> FsImg.T_FILE_z).
      { intros Hc. apply Hnf. apply bv_eq. rewrite Hc.
        vm_compute. reflexivity. }
      iDestruct (so_flat_close with "Hflat") as "Hload".
      iDestruct (so_arm_notr gf (proc_addr jx) pidv vom P Φo Φt U sts pl
                   (bv_unsigned inum) dn bm data t
                   (or_intror Hnf2) Hdirk Hdevb Hinob Htyen
                   with "HP Hobs Htc") as "Harm".
      iApply (Pub.so_tail_pub_au (CID0 := CID13) gf gs jx gl pd pav pu
                gil gisl
 kk qi s gy loy tly inum dn bm kf fd l C pn om voff nsj
                (S (S u2)) pidv dqb dqs U sts m N8 sp0 K eb b lks w6
                (word_of_words lo om) w24 bp vom P Pmiss Φo Φt t
                Hqs HKiu HKeo HK24 Kpop Hkk Hinb Hgeom Hj Hgl Hlkempty Hkf
                Hfdlt Hlen Hfrees eq_refl Htyor eq_refl eq_refl Hdir Hdvw Hwf
                Hom Hfdty
                Hsp0 HN8sp HN8thr HN8s1 HN8s3 Hal
                with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                      Hitinv Hesck Hslkk Hslkd [//] Hfly Hclaimsy Hdep Hoffr Hidev Hiinum Hivalid
                      Hload Hshot Hfrz Hkeep Hru Hfref Hflive Hflds Hfpn Hfoff
                      Hiru Hcore Howe Hprocs Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres
                      Hbsl Hisl Hfds Hfrag Hauth Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                      Harm Hcont"). }
    (* ---- T_FILE: the +0x14e itrunc block ---- *)
    iApply (wp_beq_taken_s_sconf (CID := CID12) (mword_of_int (SO + 0xb4))
              (mword_of_int 154 : mword 13) Ra5 Ra4 N8 (K - 24)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HN8a4 HN8a5;
                    exact (so_ty_eq (di_type dn) 2 so_tfile_range Hfile))
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_0b4 with "Htext"). }
    iIntros (CID13 Hq13). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgb4 : add_vec (mword_of_int (SO + 0xb4) : mword 64)
                      (sign_extend' 64 (mword_of_int 154 : mword 13))
                    = mword_of_int (SO + 0x14e)) by pcw.
    iEval (rewrite Htgb4) in "Hpc".
    (* ===== +0x14e c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID13) (mword_of_int (SO + 0x14e)) Ra0 Rs1
              N8 (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_14e with "Htext"). }
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (N8 !!! Regidx Rs1))]> N8).
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = ientry kk).
    { etransitivity; [ rewrite /P1; apply upd_eq |].
      rewrite add_vec_zero_l. exact HN8s1. }
    assert (HP1sp : so_sp sp0 P1)
      by (rewrite /so_sp /P1 upd_ne; [exact HN8sp | nz]).
    assert (HP1s1 : (P1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /P1 upd_ne; [exact HN8s1 | nz]).
    assert (HP1s3 : (P1 !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64))
      by (rewrite /P1 upd_ne; [exact HN8s3 | nz]).
    assert (HP1thr : so_thr m P1).
    { intros c Hc N2b N9b N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (HN8thr c Hc N2b N9b N9 N18 N19). }
    assert (Hpp14e : add_vec_int (mword_of_int (SO + 0x14e) : mword 64) 2
                     = mword_of_int (SO + 0x150)) by pcw.
    iEval (rewrite Hpp14e) in "Hpc".
    (* ===== +0x150 jal ra,itrunc ===== *)
    iApply (wp_jal_s_sconf (CID := CID14) (mword_of_int (SO + 0x150)) Rra
              (mword_of_int 2089098 : mword 21) P1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_150 with "Htext"). }
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (P2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x150) : mword 64) 4)]> P1).
    assert (Hjit : add_vec (mword_of_int (SO + 0x150) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089098 : mword 21))
                   = mword_of_int KernelSyms.itrunc) by pcw.
    iEval (rewrite Hjit) in "Hpc".
    assert (HP2ra : (P2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x150) : mword 64) 4)
      by (rewrite /P2; apply upd_eq).
    assert (HP2a0 : (P2 !!! Regidx Ra0 : mword 64) = ientry kk)
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (HP2sp : so_sp sp0 P2)
      by (rewrite /so_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /P2 upd_ne; [exact HP1s1 | nz]).
    assert (HP2s3 : (P2 !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s3 | nz]).
    assert (HP2thr : so_thr m P2).
    { intros c Hc N2b N9b N9 N18 N19. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2b N9b N9 N18 N19). }
    iDestruct (cpu_own_transport CID0 CID15 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID15 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID15 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    (* the locked record, opened whole for the one callee that rewrites it *)
    (* THE PEEL IS ALREADY DONE, and at THIS [data]: that is the whole
       reason the payload is threaded flat (ProofSysOpenAUParts' header). *)
    iEval (rewrite /so_flat) in "Hflat".
    iDestruct "Hflat"
      as "(%Hok & %Hrl & %Hdok & %Hddix & %Hdoc & %Hduq & Hlnk & Hat & Hmeta &
           Haddr & Hind & Hblk & Htop)".
    iAssert (inode_map fsc_fs (ientry kk) bm) with "[Haddr Hind]" as "Hmap".
    { rewrite /inode_map. iFrame "Haddr Hind". }
    destruct Hok as (Hbwf & Hbcov & Haddrs & Htynz & Hszcap & Hholes & Hsized).
    iDestruct (proc_priv_core_bare_acc with "Hcore") as "[Hpbare Hcback]".
    (* THE SET FORM, BECAUSE THE TOKEN IS PARKED (durable-disk B''-tx2).
       sys_open's own [ilock] armed the escrow with half of this
       transaction's element and keeps the other half inside the
       descriptor, so the walk holds no [LogInv.log_tx] at all across the
       locked window and cannot present [itrunc]'s counted [log_op].  The
       GEN contract wants exactly what is left: the budget at the walk's
       own set, epoch-named, with the tail flush's credit uncredited. *)
    iDestruct "Hop" as (Sb2) "Hop".
    iDestruct (log_opS_named with "Hop") as (e2) "Hop".
    iApply (Itrunc.wp_itrunc_gen (CID := CID15) gs jx gl pd pav pu

 (ientry kk) inum dn dn bm data u2 Sb2 false false e2
              pidv
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqb dqs
              P2 (K - 24)%nat eb b lks U
              HKit ltac:(discriminate)
              Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog Hinb
              Htynz (di_type_stable_refl dn) (di_nlink_stable_refl dn Htynz)
              Hbwf Hcovb Hsized Haddrs Hj Hgl HP2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hidev Hiinum
                    Hmeta Hmap Hblk Hsbb Hsbi Hbmres Hireg Hat Hpbare Hprocs
                    Hdev Hgeo Hdlk Hbsl [] Hop").
    { iApply (log_credit_own icfg_log false Sb2 e2 (IBLOCK inum icfg_ist)
                ltac:(discriminate)). }
    iIntros (CID16 Hq16 mit) "%Hcsit Hcg Hown Htce Hcce Hpc Hpbare Hidev Hiinum
                              Hsbb Hsbi Hmeta Hmap Hblk Hat Hbsl Hop".
    iDestruct "Hop" as (wit u3 Sb3)
      "(%Hsb3 & %Hib3 & %Hwit & %Hcrb3 & %Hu3g & Hop)".
    assert (Hu3 : (u2 <= u3 <= S u2)%nat).
    { rewrite /it_entry /it_bm /it_iu in Hu3g. destruct wit; cbn in Hu3g; lia. }
    iDestruct (log_opS_opb with "Hop") as "Hop".
    iDestruct ("Hcback" with "Hpbare") as "Hcore".
    assert (Hpcit : ret_pc (P2 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0x154)) by (rewrite HP2ra; pcw).
    iEval (rewrite Hpcit) in "Hpc".
    assert (Hitsp : so_sp sp0 mit).
    { rewrite /so_sp (callee_saved_lookup Hcsit csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HP2sp. }
    assert (Hits1 : (mit !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite (callee_saved_lookup Hcsit Rs1 ltac:(vm_compute; reflexivity)).
      exact HP2s1. }
    assert (Hits3 : (mit !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64)).
    { rewrite (callee_saved_lookup Hcsit Rs3 ltac:(vm_compute; reflexivity)).
      exact HP2s3. }
    assert (Hitthr : so_thr m mit).
    { intros c Hc N2b N9b N9 N18 N19. rewrite (callee_saved_lookup Hcsit c Hc).
      exact (HP2thr c Hc N2b N9b N9 N18 N19). }
    (* ---- THE O_TRUNC BRIDGE: rebuild [ic_loaded] at the truncated record ---- *)
    assert (Htynd : bv_unsigned (di_type dn) <> T_DIR_z).
    { rewrite Hfile. unfold T_DIR_z. vm_compute. discriminate. }
    (* itrunc MOVED the record and every block, so the era's abstract value
       is retagged at the truncated node before the seal (durable-disk
       2b-inode-3).  [ftopN] alone is opened. *)
    (* THE RETAG OWES THE ROW (durable-disk lane A): a truncated FILE is
       well-formed -- size 0, no blocks, the type and the count ride -- and
       these are [so_trunc_loaded]'s own four facts, taken a few lines
       early. *)
    assert (Hloctr : FsStateInode.inode_local (bv_unsigned inum)
              (era_node (di_trunc dn) bm_empty
                        (fun _ => replicate BSIZE (bv_0 8)))).
    { assert (Htyt : di_type (di_trunc dn) = di_type dn) by reflexivity.
      apply (inode_local_of_ok_rec (bv_unsigned inum) fsc_cov fsc_logst
               (di_trunc dn) bm_empty (fun _ => replicate BSIZE (bv_0 8))).
      - exact (so_trunc_ok dn Htynz).
      - exact (so_trunc_rec_local dn Hrl).
      - apply (FsTree.dir_uniq_not_dir (di_trunc dn) _). rewrite Htyt. exact Htynd.
      - apply (dir_dots_ix_not_dir (bv_unsigned inum) (di_trunc dn) _).
        rewrite Htyt. exact Htynd. }
    (* ---- THE TRUNC FIRE (SpecSysOpenAU item 3): the two phases FUSED
       with the retag they bracket, one [ftopN] critical section.  The
       pre-row is the OBSERVED one -- same fragment, same [data]. ---- *)
    assert (Htyfz : bv_unsigned (di_type dn) = FsImg.T_FILE_z)
      by (rewrite Hfile; vm_compute; reflexivity).
    iApply fupd_wp.
    iMod (opf_atrunc_fire fsc_fs ⊤ Φt (bv_unsigned inum)
            (fn_file_bytes (era_node dn bm data))
            (fn_nlink (era_node dn bm data))
            (era_node dn bm data)
            (era_node (di_trunc dn) bm_empty (fun _ => replicate BSIZE (bv_0 8)))
            ltac:(solve_ndisj) Hloctr
            (opf_era_file_row dn bm data Htyfz)
            (opf_trunc_row dn bm bm_empty data
               (fun _ => replicate BSIZE (bv_0 8)) Htyfz)
            with "[] Htc Htop") as "[Htop Htr2]";
      [iApply (ireg_inv_ftop with "Hireg") |].
    iModIntro.
    iDestruct (so_trunc_loaded kk inum dn Htynz Htynd Hrl
                 with "Hat Hmeta Hmap Hblk Htop") as "Hload".
    (* ===== +0x154 c.j +0xb8 ===== *)
    iApply (wp_cj_s_sconf (CID := CID16) (mword_of_int (SO + 0x154))
              (sign_extend' 21 (concat_vec (mword_of_int 1970 : mword 11) ('b"0")))
              mit (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_154 with "Htext"). }
    iIntros (CID17 Hq17). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htg154 : add_vec (mword_of_int (SO + 0x154) : mword 64)
                       (sign_extend' 64
                          (sign_extend' 21 (concat_vec (mword_of_int 1970 : mword 11) ('b"0"))))
                     = mword_of_int (SO + 0xb8)) by pcw.
    iEval (rewrite Htg154) in "Hpc".
    iDestruct (cpu_own_transport CID16 CID17 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID16 CID17 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID16 CID17 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID17)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    (* Fix the fact before elaborating the large application: an inline
       [ltac:(set_solver)] here sees its unresolved evars and the whole
       function context. *)
    (* the O_TRUNC file arm: the ONE arm of this surface that spends the
       trunc commit, at the row the observation read *)
    assert (Htrue : om_trunc vom = true).
    { destruct (om_trunc vom) eqn:Hot; [reflexivity |]. exfalso.
      assert (Hz : so_and om 1024 = (mword_of_int 0 : mword 64))
        by (rewrite Hom; apply (proj2 (soau_trunc_zero_iff vom)); exact Hot).
      rewrite Hz so_eqz_zero in Htr. discriminate. }
    assert (Htis : t = FdInode (bv_unsigned inum)).
    { destruct (Hti ltac:(rewrite Htyfz; vm_compute; discriminate)) as [_ Hq].
      exact Hq. }
    iEval (rewrite /so_obs (opf_era_file_row dn bm data Htyfz)) in "Hobs".
    iDestruct (so_arm_file_tr gf (proc_addr jx) pidv vom P Φo Φt U sts pl
                 (bv_unsigned inum) (fn_file_bytes (era_node dn bm data))
                 (fn_nlink (era_node dn bm data)) Htrue
                 with "HP Hobs Htr2") as "Harm".
    iEval (rewrite -Htis) in "Harm".
    iApply (Pub.so_tail_pub_au (CID0 := CID17) gf gs jx gl pd pav pu
              gil gisl
 kk qi s gy loy tly inum (di_trunc dn) bm_empty kf fd l C pn
              om voff nsj u3 pidv dqb dqs U sts m mit sp0 K
              eb b lks w6 (word_of_words lo om) w24 bp
              vom P Pmiss Φo Φt t
              Hqs HKiu HKeo HK24 Kpop Hkk Hinb Hgeom Hj Hgl Hlkempty Hkf
              Hfdlt Hlen Hfrees eq_refl Htyor eq_refl eq_refl Hdir Hdvw Hwf
              Hom Hfdty
              Hsp0 Hitsp Hitthr Hits1 Hits3 Hal
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hitinv Hesck Hslkk Hslkd [//] Hfly Hclaimsy Hdep Hoffr Hidev Hiinum Hivalid
                    Hload Hshot Hfrz Hkeep Hru Hfref Hflive Hflds Hfpn Hfoff
                    Hiru Hcore Howe Hprocs Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres
                    Hbsl Hisl Hfds Hfrag Hauth Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                    Harm Hcont").
  Qed.

End ProofSysOpenAUStores.

End SysOpenAUStores.
