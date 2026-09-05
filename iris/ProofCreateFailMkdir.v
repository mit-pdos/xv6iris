(* ProofCreate.v -- the walk of xv6's create (fs.c): the FOUND half and the
   ALLOCATE half's C-OK-FILE / A-FAIL arms.

     static struct inode*
     create(char *path, short type, short major, short minor)

   332 bytes.  The CFG is [SpecCreate.v]'s header and
   claude-notes/projects/fs-sysfile.md's verified listing; every immediate
   below is taken from [CodeCreate.v]'s own lemma statements and from
   nowhere else.

   ---- WHAT THIS FILE PROVES, AND WHAT IT PARKS -------------------------

   [cr_found_half] is create's contract on the FOUND half: the prologue,
   [nameiparent], ARM N, [ilock(dp)], the [dp->nlink == 0] guard and its
   ARM G, [dirlookup], and the two found arms F-BAD and F-OK -- with the
   whole ALLOCATE half (+0xa2 onward, reached by the [c.beqz] at +0x4c
   being TAKEN) parked behind ONE HYPOTHESIS, [cr_alloc_body].  That
   hypothesis is a PREMISE of the lemma, not an axiom and not an [admit]:
   [Print Assumptions cr_found_half] shows the standing platform six and
   nothing else, and the parked half appears in the STATEMENT.

   The cut is at +0x4c rather than at the failure family because the
   family's ARM FAIL is reached only through ialloc / ilock(ip) / three
   [sh]s / iupdate / dirlink -- i.e. through more code than everything
   before it.  The found half is the increment that stands alone.

   [cr_alloc_half] is the OTHER half, and it discharges [cr_alloc_body]:
   the eighth save at +0xa2, the fresh-type gate span (+0xa4..+0xb0,
   [ProofCreateFreshTy]), ARM A-FAIL (+0xec), the three metadata [sh]s, the
   LINK MINT at +0xc4 ([SpecIupdate.wp_iupdate_link]), the T_DIR branch at
   +0xca, the [dirlink(dp,name)] at +0xd8 and ARM C-OK-FILE (+0xe0..+0xea).
   Two of its branches leave through a PREMISE of their own -- the whole
   T_DIR sub-branch through [cr_mkdir_body] and the failing [dirlink]
   through [cr_fail_body] -- so its [Print Assumptions] is the standing six
   and nothing else.  Its conclusion is
   [wp_next]-wrapped for the reason stated at the lemma: the parked bodies
   and the contract's own continuation are anchored at the SECTION hart,
   and the allocate half runs at whatever hart the +0x4c [c.beqz] rebound
   to, so the entry hart's chain link IS the [wp_next] guard.

   ---- THE PIECES ------------------------------------------------------

   [cr_tail_body]  -- the epilogue funnel at +0x70 ([mv a0,s2], the seven
   restores, the pop, [c.ret]).  FOUR arms of this half reach it (N, G,
   F-BAD, F-OK) and two more will (C-OK, A-FAIL, FAIL), so it is
   [□]-persistent with an ABSTRACT continuation -- ProofDirlookup's shape --
   and speaks only of [cr_tregs] and the ten frame slots.

   [cr_alloc_body] -- the parked gate.  It takes the register file, the pc,
   the parent's [dn]/[bm]/[data] and the ledger triple as ARGUMENTS and
   the contract's own continuation as its last premise (ProofDirlink's
   [dl_after_body] shape), so the allocate half will discharge it as an
   ordinary block lemma and this file hands it [Hcont] unretargeted.

   NO LOOP, so no [∀ fuel] anywhere: create is the first fs whole-function
   walk that is straight-line-with-branches, which is why ProofDirlink and
   not ProofNamex is the model for everything except the guard.

   ---- THE ONE LEDGER SUBTLETY (ARM G) ---------------------------------

   [crz] is UNAVAILABLE ON ARM G BY CONSTRUCTION.  It buys itrunc's
   tail-flush unit with [InodeRegion.nlz_obs], which is minted only at an
   observation that the record's nlink is NONZERO -- and ARM G is the guard
   TAKEN, i.e. [di_nlink dn = 0] observed.  So its [iunlockput(dp)] runs at
   [crb = cru = crz = false] and spends [SpecIput.ip_spend_w w false false
   = ip_bm w + 1 <= 2].  It closes with room because nothing has been
   logged before the guard: the count is [CreateBudget.cr_uw w >= 9]
   against [iput_units = 3], which is [cr_budget_found_w]'s first two
   conjuncts.  The same figure covers ARM F-BAD's two uncredited
   [iunlockput]s.

   ---- SEAM NOTE (GR-2c FINDING 5) -------------------------------------

   Every [iunlockput] on this half reports its credited bound at
   [ip_spend_w w false false], which is STRONGER than the [iput_units = 3]
   the ledger cites.  Each seam weakens once, KEEPING the hypothesis name,
   exactly as ProofDirlink's found arm does.                            *)
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
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import KernelText KernelDataInv.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import FdSlots.
Require Import ProcGeom.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioInv.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED BEFORE
   [FsBlocks] on purpose -- the [FsState*] stack exports [fs_view] and
   [byte_range], both of which have live twins below, and the LAST import
   wins (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
Require Import FsStateInode.
Require Import FsBytesGamma.
Require Import FsStateEra.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import DinodeEnc.
(* [trunc16_sext64]: an [sh] of a register an [lh] filled is the identity on
   the halfword -- the three metadata stores at +0xb4 / +0xb8 are exactly
   that, at the ABI's sign-extended [major] / [minor] arguments. *)
Require Import DirView.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecPanic.
Require Import SpecIput SpecIupdate.
Require Import SpecIunlockput.
Require Import SpecCreate.
(* THE FRESH-TYPE SPAN: the four instructions +0xa4..+0xb0 that pin
   [di_type dn = ty] across [ialloc]/[ilock].  It is a stretch of create's
   OWN body rather than a callee, so it is NOT a functor argument -- the
   statement ([create_fresh_ty_body], spliced verbatim below), the span's
   register contract ([cr_cs_but_s3]) and the proof all live in
   [ProofCreateFreshTy.v], and this file applies [create_fresh_ty] directly,
   handing it [IA]/[IL] for its two callee hypotheses. *)
Require Import CodeCreate.
Require Import ProofCreateParts.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.
Require Import TsoCtx.
Require Import OffBox.   (* [off_rows] / [off_rows_dep] / [off_rows_to_dep] -- the inode's off rows (items 35/36) *)

(* claude-notes/optimization.md "Register maps": the leaves' premises are
   stated over [rget] (see e.g. [cri_*]'s consumers below), so with these
   three transparent every register-chain [iApply]'s unifier walks
   [rget -> tp_pin -> rf_upd] down the whole chain, and [Qed] re-walks it.
   ProofPipewrite.v is the measured instance (its own header): sealing all
   three is a net win on a file of this shape, PROVIDED no site hands a
   leaf a premise spelled with [!!!] where the leaf's statement says
   [rget] -- those used to bridge for free by delta and regress once the
   three are opaque.  Re-measure after sealing; restate any regressed
   premise in the [rget] spelling with [rget_ne] (HartTp.v) right before
   its [iApply], as ProofPipewrite's own three recoveries did. *)
Local Strategy opaque [rget].
Local Strategy opaque [tp_pin].
Local Strategy opaque [rf_upd].

(* claude-notes/durable-notes.md: a syscall-altitude goal carries
   [ProcInv.tf_page]'s 4096-conjunct big-op, and printing it turns a
   one-line mistake into a forty-minute non-answer. *)
Set Printing Depth 40.
(* ==================================================================== *)
(*  ProofCreateFailMkdir.v -- create's FailMkdir half. *)
(*                                                                      *)
(*  Split out of ProofCreate.v FOR THE BUILD DAG: create's five halves    *)
(*  take each other as PREMISES, not as callees, so only the             *)
(*  functor-free vocabulary in ProofCreateShared.v is shared and they     *)
(*  compile in parallel.                                                 *)
(* ==================================================================== *)

Require Import ProofCreateShared.

Module CreateFailMkdir (IUP : IUNLOCKPUT) (IU : IUPDATE).

Section ProofCreateFailMkdir.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  Lemma cr_fail_mkdir_half
      (γs : list gname) (j : nat) (γl : gname)
      (pd pav pu : mword 64)
      (γf : gname)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (U : ustate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
      (nf nsl : nat -> bv 8) (t : nat) :
    (K_create <= K)%nat ->
    16 * Z.of_nat icfg_nib <= 2 ^ 16 ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < fsc_size <= BPB ->
    0 <= fsc_bmapstart ->
    fsc_bmapstart ∈ fsc_cov ->
    ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
    0 <= icfg_ist ->
    cov_below fsc_cov fsc_size ->
    InodeInv.ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
    (create_slots <= ns)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (m !!! Regidx csp_rs1 : mword 64) = sp0 ->
    ret_pc (m !!! Regidx Rra : mword 64) = ret_tgt ->
    is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true ->
    eb = true ->
    kernel_text -∗ kernel_data -∗ panic_env -∗
    bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
    log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
    is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
    itable_inv -∗
    ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
    ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
    ireg_open -∗
    procs_inv γs -∗
    dev_inv fsc_uart fsc_disk -∗
    disk_geom fsc_disk pd pav pu -∗
    is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
    wp_next (CID0 := CID) true (proc_addr j) (fun CIDf : CpuId =>
      cr_fail_mkdir_body (CID := CID) γs j γl pd pav pu γf

                   plen pfun pv ty major minor U u Sb ns pidv
                   dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                   kd qd gd γil γisl dind nf nsl t CIDf).
  Proof.
    intros HK Hnib16 Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hcovb
           Hiregb Hns Hj Hgs Hspm Hrt Hal10 Hal9 Heb.
    destruct (cr_kb K HK)
      as (HK10 & HKnp & HKil & HKdlu & HKiup & HKia & HKiu & HKdlk & HKsum).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    iIntros "#Htext #Hkd #Hpenv #Hbio #Hlogc #Hitb2 #Hitbl #Hesc #Hiregi #Hiopen
             #Hprocs #Hdevi #Hgeom #Hdlk".
    iDestruct (cr_tail_half j m sp0 ret_tgt K b lks HKsum Hal10 Hal9 Hspm Hrt
                 with "Htext") as "#Htail".
    iIntros (CIDf Hsf).
    iIntros (Mx kslot q g gil gisl lo tl cinum dp bmp datap dc bmc datc
             n4 Sb4).
    iIntros "%HXregs %Htdir %Hkdlt %Hdib %Htydir %Hnl0 %Hiok %Hdok %Hddix %Hduq %Hrl %Hkslt
             %Hcpos %Hcinb %Htyc %Hcmaj %Hcmin %Hcnl1 %Hciok %Hrl_datc %Hcdok %Hcduq %Hcdots
             %Hsb4 %Hmem4 %Hn4 %Hledge".
    iIntros "Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
             #Hslkd Hslkdd Hdep Hoffr Hidev Hiinum Hivalid Hdlnk Hdiat
             Hmeta Hmap Hblocks Htop #Hshotl Hfrzl Hkeep Hrud
             #Hslkc Hcslkd Hcdep Hoffrc Hcidev Hciinum Hcivalid
             Hcdiat Hcmeta Hcmap Hcblocks Hctop #Hcshot Hcfrz %Hlek #Hflk Hckeep Hruc Htoken
             Hsbn Hsbi Hsbs Hsbb #Hbmr Hppid Hppback Hpath Hbsl Hislr Hop Hdirty
             Hcont".
    iDestruct "Hkeep" as (lod tld) "(%Hled & #Hfld & Hkeep)".
    iDestruct (is_itable2_claims with "Hitb2") as "#Hclaimscr".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb). clear Hbm.
    (* THE HELD SET IS EMPTY, AND SAID SO ONCE -- the level-0 pose the
       sibling [cr_fail_half] makes, for the same reason: create's contract
       carries no order premise because it needs none, and [lkbelow] closes
       each callee's bound from this EQUATION.  Keep the equation rather
       than substituting; [lks] is spelled by name in the bodies below. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    pose proof HXregs as HXr.
    destruct HXr as (X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & Xthr).
    destruct (Hiregb cinum Hcinb) as [Hcblk Hcblog].
    destruct (Hiregb dind Hdib) as [Hdblk Hdblog].
    assert (Htyz : bv_unsigned (di_type dc) <> 0).
    { rewrite Htyc Htdir. vm_compute. discriminate. }
    assert (Hcadd : di_addrs dc = bm_cells bmc)
      by exact (proj1 (proj2 (proj2 Hciok))).
    assert (Hcdirlen : length (bm_dir bmc) = NDIRECT)
      by exact (blkmap_wf_dir_len fsc_cov fsc_logst bmc (proj1 Hciok)).
    assert (Hcdok' : dir_ok icfg_nib dc datc) by (exact Hcdok).
    (* the ZEROED child's record, and the four fields the [sh] leaves alone *)
    assert (Hzty : di_type (cr_setf dc major minor (mword_of_int 0 : mword 16))
                   = di_type dc) by apply cr_setf_type.
    assert (Hzsz : di_size (cr_setf dc major minor (mword_of_int 0 : mword 16))
                   = di_size dc) by apply cr_setf_size.
    assert (Hznl : bv_unsigned (di_nlink
                     (cr_setf dc major minor (mword_of_int 0 : mword 16))) = 0)
      by (rewrite cr_setf_nlink; vm_compute; reflexivity).
    (* ===== +0x146 sh zero,74(s3) : ip->nlink = 0 ===================== *)
    iEval (rewrite /inode_meta) in "Hcmeta".
    iDestruct "Hcmeta" as "(Hcity & Hcimaj & Hcimin & Hcinl & Hcisz)".
    iEval (rewrite /i_nlink) in "Hcinl".
    iDestruct (sie_cap_gpr_x0 Mx (K - 10)%nat b (proc_addr j) Rz
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x146)) Rz Rs3
              (mword_of_int 74 : mword 12) Mx (K - 10)%nat
              (di_nlink dc : mword 16) b
              with "Hcg Hpc [] [Hcinl]").
    { iApply (cri_146 with "Htext"). }
    { iEval (rgne; rewrite X19). iExact "Hcinl". }
    iIntros (CIDG1 HqG1) "Hcg Hpc Hcinl".
    iEval (rgne; rgne; rewrite X19 Hx0 cr_trunc16_zero) in "Hcinl".
    assert (Hq14a : add_vec_int (mword_of_int (CK + 0x146) : mword 64) 4
                    = mword_of_int (CK + 0x14a)) by pcw.
    iEval (rewrite Hq14a) in "Hpc".
    iAssert (inode_meta (ientry kslot)
               (cr_setf dc major minor (mword_of_int 0 : mword 16)))
      with "[Hcity Hcimaj Hcimin Hcinl Hcisz]" as "Hcmeta".
    { rewrite /inode_meta cr_setf_type cr_setf_major cr_setf_minor
              cr_setf_nlink cr_setf_size /i_nlink.
      rewrite -Hcmaj -Hcmin. iFrame. }
    (* THE ORPHAN'S RE-PARK (durable-disk
       2b-inode-5): an ORPHAN owns NO tokens.  Its live records are named
       ["."] or [".."] ([DirView.dir_orphan_clean]'s [dir_dots_only], which
       is [Hcdots] carried onto the zeroed record), ["."] is never counted
       and an orphan's [".."] is tokenless -- so nothing is owed and the
       failing [dirlink] left nothing behind. *)
    assert (Hzholes : blk_holes_zero bmc datc)
      by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hciok)))))).
    assert (Hzcap : bv_unsigned (di_size (cr_setf dc major minor (mword_of_int 0 : mword 16)))
                    <= Z.of_nat MAXFILE * Z.of_nat BSIZE).
    { exact (proj1 (proj2 (proj2 (proj2 (proj2 Hciok))))). }
    assert (Hzdok : FsStateInode.ent_dset_ok (era_node (cr_setf dc major minor (mword_of_int 0 : mword 16)) bmc datc) ∅)
      by (intros tz Htz; exfalso; exact (not_elem_of_empty tz Htz)).
    assert (Hzxact : FsStateInode.node_exact (era_node (cr_setf dc major minor (mword_of_int 0 : mword 16)) bmc datc) ∅).
    { intros _.
      assert (Hfn0 : fn_nlink (era_node (cr_setf dc major minor (mword_of_int 0 : mword 16)) bmc datc) = 0%nat)
        by (rewrite /fn_nlink era_node_rec Hznl //).
      rewrite /fn_orphan Hfn0
        (bool_decide_eq_true_2 (0%nat = 0%nat) eq_refl) size_empty //. }
    iAssert (dlinks fsc_fs (bv_unsigned cinum) (cr_setf dc major minor (mword_of_int 0 : mword 16)) bmc datc)
      with "[]" as "Hcdlnk".
    { iApply (dlinks_intro _ _ _ _ _ ∅ Hzdok Hzxact with "[]").
      iApply (FsStateEra.ent_toks_era_dots_only (fs_gamma_L fsc_fs)
                (bv_unsigned cinum) (cr_setf dc major minor (mword_of_int 0 : mword 16)) bmc datc
                ∅ Hznl Hzholes Hzcap
                (dir_dots_only_of dc _ datc
                   ltac:(first [reflexivity
                               | rewrite cr_setf_size; reflexivity])
                   Hcdots)). }
    (* ===== +0x14a c.mv a0,s3 ========================================= *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x14a)) Ra0 Rs3 Mx
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_14a with "Htext"). }
    iIntros (CIDG2 HqG2) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (G1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Mx !!! Regidx Rs3))]> Mx).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Mx !!! Regidx Rs3))]> Mx) with G1.
    assert (HG1a0 : G1 !!! Regidx Ra0 = ientry kslot).
    { rewrite /G1 upd_eq. rewrite X19. apply add_vec_zero_l. }
    assert (HG1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G1)
      by (rewrite /G1; apply cr_regs3_caller; [exact Hcsa0 | exact HXregs]).
    assert (Hq14c : add_vec_int (mword_of_int (CK + 0x14a) : mword 64) 2
                    = mword_of_int (CK + 0x14c)) by pcw.
    iEval (rewrite Hq14c) in "Hpc".
    (* ===== +0x14c jal iupdate(ip) : THE UNLINK FLUSH ================= *)
    assert (Htgiu : add_vec (mword_of_int (CK + 0x14c) : mword 64)
              (sign_extend' 64 (mword_of_int 2090062 : mword 21))
              = mword_of_int KernelSyms.iupdate) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x14c)) Rra
              (mword_of_int 2090062 : mword 21) G1 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_14c with "Htext"). }
    iIntros (CIDG3 HqG3) "Hcg Hpc".
    iEval (rewrite Htgiu) in "Hpc".
    pose (G2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x14c) : mword 64) 4)]> G1).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x14c) : mword 64) 4)]> G1) with G2.
    assert (HG2ra : G2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x14c) : mword 64) 4)
      by (rewrite /G2; apply upd_eq).
    assert (HG2a0 : G2 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /G2 upd_ne; [exact HG1a0 | nz]).
    assert (HG2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G2)
      by (rewrite /G2; apply cr_regs3_caller; [exact Hcsra | exact HG1regs]).
    assert (Hstab : di_type_stable
                      (cr_setf dc major minor (mword_of_int 0 : mword 16)) dc).
    { apply di_type_stable_eq. rewrite cr_setf_type. reflexivity. }
    assert (Hdec : bv_unsigned (di_nlink dc)
                   = bv_unsigned (di_nlink
                       (cr_setf dc major minor (mword_of_int 0 : mword 16)))
                     + 1).
    { rewrite cr_setf_nlink Hcnl1. vm_compute. reflexivity. }
    assert (Hcadd0 : di_addrs (cr_setf dc major minor
                                 (mword_of_int 0 : mword 16)) = bm_cells bmc)
      by (rewrite cr_setf_addrs; exact Hcadd).
    assert (Htyz0 : bv_unsigned (di_type (cr_setf dc major minor
                      (mword_of_int 0 : mword 16))) <> 0)
      by (rewrite cr_setf_type; exact Htyz).
    destruct n4 as [| u0]; [exfalso; unfold iput_units in Hn4; lia |].
    iDestruct (cr_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    iDestruct (cpu_own_transport CIDf CIDG3 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (IU.wp_iupdate_unlink γs j γl pd pav pu
 (ientry kslot) cinum
              (cr_setf dc major minor (mword_of_int 0 : mword 16)) dc bmc
              u0 Sb4 true
              (cr_ity ty (bv_unsigned dind)) pidv
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
              G2 (K - 10)%nat eb b lks
              U ltac:(exact HKiu) ltac:(intros _; exact Hmem4)
              Hlg Hist0 Hcblk Hcblog Hcinb Hstab Htyz0
              Hdec
              Hcadd0 Hcdirlen Hj Hgs HG2a0 Heb
              with "Hcg Hcnt Htext Hkd Hpc Hpenv Hbio Hlogc Hcidev Hciinum
                    Hcmeta Hcmap Hsbi Hiregi Hcdiat [Htoken] Hppid Hprocs
                    Hdevi Hgeom Hdlk Hbs2 Hop").
    all: try lkbelow.
    { rewrite (cr_delta_eq ty major minor dc (mword_of_int 0 : mword 16)
                 Htyc ltac:(vm_compute; reflexivity)). iExact "Htoken". }
    iIntros (CIDG4 HsG4 mfl)
      "%Hcsfl Hcg Hcnt Hpc Hppid Hcidev Hciinum Hcmeta Hcmap Hsbi Hcdiat
       Hbs2 Hop".
    assert (Hpcfl : ret_pc (G2 !!! Regidx Rra : mword 64)
                    = mword_of_int (CK + 0x150)) by (rewrite HG2ra; pcw).
    iEval (rewrite Hpcfl) in "Hpc".
    assert (Hmflregs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                         (ientry kslot) ty major minor mfl)
      by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                  (ientry kslot) ty major minor G2 mfl Hcsfl HG2regs).
    pose proof Hmflregs as HFr.
    destruct HFr as (F2 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & Fthr).
    iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
      [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
    (* ===== +0x150 c.mv a0,s3 ========================================= *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x150)) Ra0 Rs3 mfl
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_150 with "Htext"). }
    iIntros (CIDG5 HqG5) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (G3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mfl !!! Regidx Rs3))]> mfl).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mfl !!! Regidx Rs3))]> mfl) with G3.
    assert (HG3a0 : G3 !!! Regidx Ra0 = ientry kslot).
    { rewrite /G3 upd_eq. rewrite F19. apply add_vec_zero_l. }
    assert (HG3regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G3)
      by (rewrite /G3; apply cr_regs3_caller; [exact Hcsa0 | exact Hmflregs]).
    assert (Hq152 : add_vec_int (mword_of_int (CK + 0x150) : mword 64) 2
                    = mword_of_int (CK + 0x152)) by pcw.
    iEval (rewrite Hq152) in "Hpc".
    (* ===== +0x152 jal iunlockput(ip) : THE PUT THAT FREES ============ *)
    assert (Htgu1 : add_vec (mword_of_int (CK + 0x152) : mword 64)
              (sign_extend' 64 (mword_of_int 2090832 : mword 21))
              = mword_of_int KernelSyms.iunlockput) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x152)) Rra
              (mword_of_int 2090832 : mword 21) G3 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_152 with "Htext"). }
    iIntros (CIDG6 HqG6) "Hcg Hpc".
    iEval (rewrite Htgu1) in "Hpc".
    pose (G4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x152) : mword 64) 4)]> G3).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x152) : mword 64) 4)]> G3) with G4.
    assert (HG4ra : G4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x152) : mword 64) 4)
      by (rewrite /G4; apply upd_eq).
    assert (HG4a0 : G4 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /G4 upd_ne; [exact HG3a0 | nz]).
    assert (HG4regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G4)
      by (rewrite /G4; apply cr_regs3_caller; [exact Hcsra | exact HG3regs]).
    (* ...and the ERA's abstract value follows the [sh zero,74(s3)]: the
       count moved, no block did (durable-disk 2b-inode-3). *)
    (* THE CHILD'S ROW COMES BACK HERE (durable-disk lane A).  This is the
       mkdir FAIL arm: the child is the dotless directory the shared
       prologue suspended, and the [sh zero,74(s3)] at +0x146 has just made
       it an ORPHAN -- which owes no dot entries at all.  So the retag is
       the disarming one: the row is re-established for this inum and the
       transaction token goes home. *)
    assert (Hlocorph : inode_local (bv_unsigned cinum)
              (era_node (cr_setf dc major minor (mword_of_int 0 : mword 16))
                        bmc datc)).
    { apply (inode_local_of_ok_rec (bv_unsigned cinum) fsc_cov fsc_logst _ bmc datc).
      - exact (cr_setf_inode_ok fsc_cov fsc_logst dc bmc datc major minor
                 (mword_of_int 0 : mword 16) Hciok).
      - exact (cr_setf_rec_local dc major minor (mword_of_int 0 : mword 16)
                 Hrl_datc cr_nl_short_0).
      - exact (dir_uniq_cong dc _ datc (cr_setf_type _ _ _ _)
                 (cr_setf_size _ _ _ _) Hcduq).
      - exact (dir_dots_ix_orphan (bv_unsigned cinum) _ datc Hznl). }
    iApply fupd_wp.
    iMod (cr_dirty_clear ⊤ t (bv_unsigned cinum)
            (era_node dc bmc datc)
            (era_node (cr_setf dc major minor (mword_of_int 0 : mword 16))
                      bmc datc)
            ltac:(solve_ndisj) Hlocorph with "[] [] Hdirty Hctop")
      as "[Htx Hctop]";
      [iApply (ireg_inv_ftop with "Hiregi") | iApply (ireg_inv_app with "Hiregi") |].
    iModIntro.
    iAssert (ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kslot cinum
               (cr_setf dc major minor (mword_of_int 0 : mword 16)) bmc)
      with "[Hcdlnk Hcdiat Hcmeta Hcmap Hcblocks Hctop]"
      as "Hcload".
    { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body. iExists datc.
      iSplitR; [iPureIntro;
                exact (cr_setf_inode_ok fsc_cov fsc_logst dc bmc datc major minor
                         _ Hciok) |].
      iSplitR; [iPureIntro;
                exact (cr_setf_rec_local dc major minor
                         (mword_of_int 0 : mword 16) Hrl_datc
                         cr_nl_short_0) |].
      iSplitR; [iPureIntro;
                exact (cr_setf_dir_ok icfg_nib dc datc major minor
                         _ Hcdok') |].
      (* the ["."]/[".."] clause needs no entry premise here, and that is
         the whole reason the guard names [nlink]: the [sh zero,74(s3)] at
         +0x146 has ALREADY zeroed the count, so whatever record the failing
         link left, what this re-parks is an ORPHAN.  All three [fail:]
         entries discharge through this one line -- at the first two the
         child has no [".."] at all. *)
      iSplitR; [iPureIntro;
                exact (dir_dots_ix_orphan (bv_unsigned cinum) _ datc Hznl) |].
      (* ...and the COMPLEMENT clause is where the entry premise is spent:
         the [sh] moved only the count, so the size -- hence [dir_nrec],
         hence the whole content -- is the entry's, and [dir_dots_only_of]
         carries it verbatim onto the orphaned record. *)
      iSplitR; [iPureIntro;
                apply dir_orphan_clean_of_only;
                apply (dir_dots_only_of dc _ datc);
                [rewrite cr_setf_size; reflexivity | exact Hcdots] |].
      (* ...and UNIQUENESS rides on the same observation one clause over:
         the [sh] moved the COUNT, and this clause reads only the type and
         the size. *)
      iSplitR; [iPureIntro;
                exact (dir_uniq_cong dc _ datc (cr_setf_type _ _ _ _)
                         (cr_setf_size _ _ _ _) Hcduq) |].
      iSplitL "Hcdlnk"; [iExact "Hcdlnk" |].
      iFrame "Hcdiat Hcmeta".
      iEval (rewrite /inode_map) in "Hcmap".
      iDestruct "Hcmap" as "[Hca Hci]". iFrame. }
    iAssert (ity_shot g (di_type (cr_setf dc major minor
                                    (mword_of_int 0 : mword 16))))
      as "#Hcshot'". { rewrite cr_setf_type. iExact "Hcshot". }
    iPoseProof (cr_esc_acc kslot Hkslt with "Hesc")
      as "#Hescc".
    iDestruct (inode_ref_short_gen_forget _ _ _ _ _ _ _ _ Hlek
                 with "Hflk Hckeep") as "Hckp".
    iDestruct (log_opS_named with "Hop") as (e0) "Hop".
    iDestruct (cpu_own_transport CIDG4 CIDG6 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct "Hcdep" as (locc tlcc) "(%Hlecc & #Hflcc & Hcdep)".
    (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
       goes in and the share it parked comes back in the post, so no
       bundleless out-state stands across the call. *)
    iDestruct (off_rows_to_dep with "Hoffrc") as "Hoffdc".
    iApply (IUP.wp_iunlockput_dep_gen γs j γl pd pav pu
              gil gisl
              kslot (q/2)%Qp (q/2)%Qp g locc tlcc (DepTx (q/2)%Qp icfg_dev cinum g locc t (1/4)%Qp) cinum
              (cr_setf dc major minor (mword_of_int 0 : mword 16)) bmc
              (S u0) (Sb4 ∪ {[IBLOCK cinum icfg_ist]})
              (bool_decide (fsc_bmapstart ∈ (Sb4 ∪ {[IBLOCK cinum icfg_ist]})))
              true false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
              G4 (K - 10)%nat eb b lks
              U ltac:(exact HKiup) eq_refl Hkslt
              ltac:(exact (cr_crb_honest (Sb4 ∪ {[IBLOCK cinum icfg_ist]})
                             fsc_bmapstart))
              ltac:(intros _; exact (cr_in_union_sing Sb4
                                       (IBLOCK cinum icfg_ist)))
              Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hcblk Hcblog Hcinb Hcovb
              ltac:(exact (proj1 Hn4)) Hj Hgs HG4a0 ltac:(lkbelow) eq_refl
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                    Hescc Hiregi Hiopen Hslkc Hcslkd [//] Hflcc Hclaimscr Hcdep Hoffdc Hcidev Hciinum
                    Hcivalid Hcload Hcshot' Hcfrz [$Hckp $Hruc] Hsbb Hsbi Hbmr Hppid Hprocs
                    Hdevi Hgeom Hdlk Hbsl [] Hop").
    all: try lkbelow.
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (CIDG7 HqG7 mu1 n5 Sb5 w1)
      "%Hcsu1 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
       %Hsb5 %Hw5 %Hw5c %Hn5 Hop Hisl1 Htq1".
    assert (Hipn5 : (iput_units <= n5)%nat).
    { destruct (decide (fsc_bmapstart ∈ (Sb4 ∪ {[IBLOCK cinum icfg_ist]})))
        as [Hin | Hout].
      - rewrite (Hw5c (cr_crb_claim _ _ Hin)) in Hn5.
        exact (cr_fail_ip_right (S u0) n5 (proj1 Hn4) (proj1 Hn5)).
      - destruct Hledge as [H4 | Hin4].
        + exact (cr_fail_ip_left (S u0) n5 w1 H4 (proj1 Hn5)).
        + exfalso. apply Hout.
          exact (cr_sub_union_sing Sb4 (IBLOCK cinum icfg_ist)
                   fsc_bmapstart Hin4). }
    assert (Hpcu1 : ret_pc (G4 !!! Regidx Rra : mword 64)
                    = mword_of_int (CK + 0x156)) by (rewrite HG4ra; pcw).
    iEval (rewrite Hpcu1) in "Hpc".
    assert (Hmu1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                         (ientry kslot) ty major minor mu1)
      by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                  (ientry kslot) ty major minor G4 mu1 Hcsu1 HG4regs).
    pose proof Hmu1regs as HUr.
    destruct HUr as (U2 & U8 & U9 & U18 & U19 & U20 & U21 & U22 & Uthr).
    (* ===== +0x156 c.mv a0,s1 ========================================= *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x156)) Ra0 Rs1 mu1
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_156 with "Htext"). }
    iIntros (CIDG8 HqG8) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (G5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mu1 !!! Regidx Rs1))]> mu1).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mu1 !!! Regidx Rs1))]> mu1) with G5.
    assert (HG5a0 : G5 !!! Regidx Ra0 = ientry kd).
    { rewrite /G5 upd_eq. rewrite U9. apply add_vec_zero_l. }
    assert (HG5regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G5)
      by (rewrite /G5; apply cr_regs3_caller; [exact Hcsa0 | exact Hmu1regs]).
    assert (Hq158 : add_vec_int (mword_of_int (CK + 0x156) : mword 64) 2
                    = mword_of_int (CK + 0x158)) by pcw.
    iEval (rewrite Hq158) in "Hpc".
    (* ===== +0x158 jal iunlockput(dp) ================================= *)
    assert (Htgu2 : add_vec (mword_of_int (CK + 0x158) : mword 64)
              (sign_extend' 64 (mword_of_int 2090826 : mword 21))
              = mword_of_int KernelSyms.iunlockput) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x158)) Rra
              (mword_of_int 2090826 : mword 21) G5 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_158 with "Htext"). }
    iIntros (CIDG9 HqG9) "Hcg Hpc".
    iEval (rewrite Htgu2) in "Hpc".
    pose (G6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x158) : mword 64) 4)]> G5).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x158) : mword 64) 4)]> G5) with G6.
    assert (HG6ra : G6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x158) : mword 64) 4)
      by (rewrite /G6; apply upd_eq).
    assert (HG6a0 : G6 !!! Regidx Ra0 = ientry kd)
      by (rewrite /G6 upd_ne; [exact HG5a0 | nz]).
    assert (HG6regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G6)
      by (rewrite /G6; apply cr_regs3_caller; [exact Hcsra | exact HG5regs]).
    (* THE PARENT NEEDS NO RE-PARK: all three entries sit before +0x134, so
       its record, its bytes and its ledger are the ones the walk handed
       over -- and the walk has already undone its own failing append. *)
    iAssert (ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kd dind dp bmp)
      with "[Hdlnk Hdiat Hmeta Hmap Hblocks Htop]" as "Hload".
    { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body. iExists datap.
      iSplitR; [iPureIntro; exact Hiok |].
      iSplitR; [iPureIntro; exact Hrl |].
      iSplitR; [iPureIntro;exact Hdok |].
      iSplitR; [iPureIntro; exact Hddix |].
      iSplitR; [iPureIntro; exact (cr_doc_of_live dp dp datap eq_refl Hnl0) |].
      iSplitR; [iPureIntro; exact Hduq |].
      iSplitL "Hdlnk"; [iExact "Hdlnk" |].
      iFrame "Hdiat Hmeta".
      iEval (rewrite /inode_map) in "Hmap".
      iDestruct "Hmap" as "[Haddrs Hind]". iFrame. }
    iPoseProof (cr_esc_acc kd Hkdlt with "Hesc")
      as "#Hescd".
    iDestruct (inode_ref_short_gen_forget _ _ _ _ _ _ _ _ Hled
                   with "Hfld Hkeep") as "Hkeep2".
    iDestruct (log_opS_named with "Hop") as (e1) "Hop".
    iDestruct (cpu_own_transport CIDG7 CIDG9 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct "Hdep" as (lodc tldc) "(%Hledc & #Hfldc & Hdep)".
    (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
       goes in and the share it parked comes back in the post, so no
       bundleless out-state stands across the call. *)
    iDestruct (off_rows_to_dep with "Hoffr") as "Hoffd".
    iApply (IUP.wp_iunlockput_dep_gen γs j γl pd pav pu
              γil γisl
              kd (qd/2)%Qp (qd/2)%Qp gd lodc tldc (DepTx (qd/2)%Qp icfg_dev dind gd lodc t (1/4)%Qp) dind dp bmp
              n5 Sb5 false false false e1 _ _ pidv (DfracOwn (1/4)) dqb dqs
              G6 (K - 10)%nat eb b lks
              U ltac:(exact HKiup) eq_refl Hkdlt ltac:(discriminate) ltac:(discriminate)
              Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib Hcovb
              ltac:(exact Hipn5) Hj Hgs HG6a0 ltac:(lkbelow) eq_refl
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                    Hescd Hiregi Hiopen Hslkd Hslkdd [//] Hfldc Hclaimscr Hdep Hoffd Hidev Hiinum
                    Hivalid Hload Hshotl Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr Hppid Hprocs
                    Hdevi Hgeom Hdlk Hbsl [] Hop").
    all: try lkbelow.
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (CIDGA HqGA mu2 n6 Sb6 w2)
      "%Hcsu2 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
       %Hsb6 %Hw6 %Hw6c %Hn6 Hop Hisl2 Htq2".
    iDestruct (log_tx_add icfg_log t (1/2) (1/4) (1/4)
                 (eq_sym Qp.quarter_quarter) with "Htq1 Htq2") as "Htp".
    iDestruct (log_tx_add icfg_log t 1 (1/2) (1/2)
                 (eq_sym Qp.half_half) with "Htp Htx") as "Htw".
    iDestruct (log_tx_full with "Htw") as "Htx".

    assert (Hpcu2 : ret_pc (G6 !!! Regidx Rra : mword 64)
                    = mword_of_int (CK + 0x15c)) by (rewrite HG6ra; pcw).
    iEval (rewrite Hpcu2) in "Hpc".
    assert (Hmu2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                         (ientry kslot) ty major minor mu2)
      by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                  (ientry kslot) ty major minor G6 mu2 Hcsu2 HG6regs).
    iDestruct ("Hppback" with "Hppid") as "Hpriv".
    (* ===== +0x15c c.ldsp s3,40(sp) : THE LAZY RESTORE ================ *)
    assert (HG7sp : mu2 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (destruct Hmu2regs as (H2 & _); exact H2).
    assert (HT5 : add_vec (mu2 !!! Regidx csp_rs1)
                    (zero_extend' 64
                       (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite HG7sp; apply cr_frm5).
    iEval (rewrite -HT5) in "Hb5".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x15c))
              (mword_of_int 5 : mword 6) Rs3 mu2 (K - 10)%nat
              (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] Hb5").
    { iApply (cri_15c with "Htext"). }
    iIntros (CIDGB HqGB) "Hcg Hpc Hb5".
    iEval (rewrite HT5) in "Hb5".
    pose (G7 := <[Regidx Rs3 := regval_into_reg
                  (m !!! Regidx Rs3 : mword 64)]> mu2).
    change (<[Regidx Rs3 := regval_into_reg
                  (m !!! Regidx Rs3 : mword 64)]> mu2) with G7.
    assert (HG7regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) ty major minor G7)
      by exact (cr_regs3_s3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                  (ientry kslot) (m !!! Regidx Rs3 : mword 64)
                  ty major minor mu2 _ eq_refl Hmu2regs).
    assert (HG7s2 : G7 !!! Regidx Rs2 = (mword_of_int 0 : mword 64)).
    { rewrite /G7 upd_ne; [| nz].
      destruct Hmu2regs as (_ & _ & _ & Hd18 & _). exact Hd18. }
    assert (Hq15e : add_vec_int (mword_of_int (CK + 0x15c) : mword 64) 2
                    = mword_of_int (CK + 0x15e)) by pcw.
    iEval (rewrite Hq15e) in "Hpc".
    (* ===== +0x15e c.j +0x70 ========================================== *)
    assert (Htg070f : add_vec (mword_of_int (CK + 0x15e) : mword 64)
              (sign_extend' 64 (sign_extend' 21
                 (concat_vec (mword_of_int 1929 : mword 11) ('b"0"))))
              = mword_of_int (CK + 0x70)) by pcw.
    iApply (wp_cj_s_sconf (mword_of_int (CK + 0x15e))
              (sign_extend' 21
                 (concat_vec (mword_of_int 1929 : mword 11) ('b"0")))
              G7 (K - 10)%nat b
              ltac:(rewrite Htg070f; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_15e with "Htext"). }
    iIntros (CIDGC HqGC). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htg070f) in "Hpc".
    iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2") as (nfj) "Hnb16".
    iPoseProof ("Htail" $! CIDGC) as "Ht".
    iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
    iApply ("Ht" $! G7 (m !!! Regidx Rs3 : mword 64) nfj with
              "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
    { exact (cr_tregs_of_regs3 m sp0 (ientry kd)
               (mword_of_int 0 : mword 64) ty major minor G7 HG7regs). }
    iIntros (CIDfin Hsfin mf) "%Hcsf %Ha0f Hcg Hpc".
    iDestruct (cpu_own_transport CIDGA CIDfin 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (iref_slots_combine with "Hisl1 Hisl2") as "Hisl".
    iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
    iSpecialize ("Hcont" $! CIDfin with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
              (mword_of_int 0 : mword 32) dp bmp n6 Sb6
              (1 + (1 + (ns - 2)))%nat
              with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv Hpath
                    Hbsl [%] Hisl [%] Hop [$Htx]").
    { exact Hcsf. }
    { exact (cr_slots_2 _ ns eq_refl Hns). }
    { split_and!.
      - exact (cr_sub3 _ _ _ _ Hsb4
                 (cr_sub_union_sing Sb4 (IBLOCK cinum icfg_ist))
                 (cr_sub2 _ _ _ Hsb5 Hsb6)).
      - pose proof (proj2 Hn6) as HB1. pose proof (proj2 Hn5) as HB2.
        pose proof (proj2 Hn4) as HB3. lia.
      - discriminate. }
    { iPureIntro. rewrite Ha0f. exact HG7s2. }
  Qed.

End ProofCreateFailMkdir.

End CreateFailMkdir.
