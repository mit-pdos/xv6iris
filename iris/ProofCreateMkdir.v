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
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import KernelText KernelDataInv.
Require Import StackOwn StackBytes.
Require Import CalleeSaved.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSmodeHalf.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SleepLock.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioInv.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED BEFORE
   [FsBlocks] on purpose -- the [FsState*] stack exports [fs_view] and
   [byte_range], both of which have live twins below, and the LAST import
   wins (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
Require Import FsState.
Require Import FsBytesGamma.
Require Import FsStateEra.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import DinodeEnc.
(* [trunc16_sext64]: an [sh] of a register an [lh] filled is the identity on
   the halfword -- the three metadata stores at +0xb4 / +0xb8 are exactly
   that, at the ABI's sign-extended [major] / [minor] arguments. *)
Require Import DinodeSlot.
Require Import DirentEnc.
Require Import BvShift.
Require Import PathElems.
Require Import DirView.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IregLinkNz.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecPrintk.
Require Import SpecPanic.
Require Import SpecBmap SpecWritei.
Require Import SpecIput SpecIalloc SpecIupdate.
Require Import SpecIlock SpecIunlockput.
Require Import SpecDirlookup SpecDirlink.
Require Import SpecNamex SpecNameiparent.
Require Import SpecCreate.
(* THE FRESH-TYPE SPAN: the four instructions +0xa4..+0xb0 that pin
   [di_type dn = ty] across [ialloc]/[ilock].  It is a stretch of create's
   OWN body rather than a callee, so it is NOT a functor argument -- the
   statement ([create_fresh_ty_body], spliced verbatim below), the span's
   register contract ([cr_cs_but_s3]) and the proof all live in
   [ProofCreateFreshTy.v], and this file applies [create_fresh_ty] directly,
   handing it [IA]/[IL] for its two callee hypotheses. *)
Require Import ProofCreateFreshTy.
Require Import CodeCreate.
Require Import ProofDirlookupParts ProofNamexParts ProofCreateParts.
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
(*  ProofCreateMkdir.v -- create's Mkdir half. *)
(*                                                                      *)
(*  Split out of ProofCreate.v FOR THE BUILD DAG: create's five halves    *)
(*  take each other as PREMISES, not as callees, so only the             *)
(*  functor-free vocabulary in ProofCreateShared.v is shared and they     *)
(*  compile in parallel.                                                 *)
(* ==================================================================== *)

Require Import ProofCreateShared.
Require Import ProofCreateFailMkdir.

Module CreateMkdir (IUP : IUNLOCKPUT) (IU : IUPDATE) (DLK : DIRLINK).
  Module FM := CreateFailMkdir IUP IU.
  Import FM.

Section ProofCreateMkdir.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  Lemma cr_mkdir_half
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
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
      (nf nsl : nat -> bv 8) (t : nat) :
    (K_create <= K)%nat ->
    icfg_dev = ROOTDEV ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < fsc_size <= BPB ->
    0 <= fsc_bmapstart ->
    fsc_bmapstart ∈ fsc_cov ->
    ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
    0 <= icfg_ist ->
    cov_below fsc_cov fsc_size ->
    bitmap_geom_ok fsc_cov fsc_logst fsc_bmapstart fsc_size ->
    InodeInv.ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
    1 < fsc_ninodes ->
    fsc_ninodes <= 16 * Z.of_nat icfg_nib ->
    fsc_ninodes < 2 ^ 31 ->
    16 * Z.of_nat icfg_nib <= 2 ^ 16 ->
    printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk ->
    (create_units <= u)%nat ->
    (create_slots <= ns)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (m !!! Regidx csp_rs1 : mword 64) = sp0 ->
    ret_pc (m !!! Regidx Rra : mword 64) = ret_tgt ->
    is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true ->
    eb = true ->
    kernel_text -∗ kernel_data -∗
    printk_env fsc_printk fsc_uart fsc_disk -∗
    bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
    log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
    kalloc_env fsc_kalloc None -∗
    is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
    itable_inv -∗
    ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
    ic_sleeplocks fsc_ic -∗
    ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
    ireg_open -∗
    procs_inv γs -∗
    dev_inv fsc_uart fsc_disk -∗
    disk_geom fsc_disk pd pav pu -∗
    is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
    wp_next (CID0 := CID) true (proc_addr j) (fun CIDm : CpuId =>
      cr_mkdir_body (CID := CID) γs j γl pd pav pu γf

                    plen pfun pv ty major minor U u Sb ns pidv
                    dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                    kd qd gd γil γisl dind dn bm data nf nsl t CIDm).
  Proof.
    intros HK Hroot Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0
           Hcovb Hbmgeo Hiregb Hni1 Hni2 Hni3 Hnib16 Hpkc Hu Hns Hj Hgs
           Hspm Hrt Hal10 Hal9 Heb.
    destruct (cr_kb K HK)
      as (HK10 & HKnp & HKil & HKdlu & HKiup & HKia & HKiu & HKdlk & HKsum).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    iIntros "#Htext #Hkd #Hpk #Hbio #Hlogc #Hkenv #Hitb2 #Hitbl #Hesc
             #Hslks #Hiregi #Hiopen #Hprocs #Hdevi #Hgeom #Hdlk".
    iPoseProof (printk_env_panic with "Hpk") as "#Hpenv".
    iDestruct (cr_tail_half j m sp0 ret_tgt K b lks HKsum Hal10 Hal9 Hspm Hrt
                 with "Htext") as "#Htail".
    iIntros (CIDm Hsm).
    iIntros (Mx kslot q g gil gisl lo tl cinum dnc bmc datc n3 Sb3).
    iIntros "%HXregs %Htdir %Hkdlt %Hdib %Htydir %Hnl0 %Hnlmax %Hiok %Hdok
             %Hddix %Hduq %Hrl %Hnpname %Hnone %Hkslt %Hcpos %Hcinb %Hfresh
             %Hrl_datc %Htyc %Hciok %Hcdok
             %Hsb3 %Hmem3 %Hn3 %Hcorr".
    iIntros "Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
             #Hslkd Hslkdd Hdep Hoffr Hidev Hiinum Hivalid Hdlnk Hdiat
             Hmeta Hmap Hblocks Htop #Hshotl Hfrzl Hkeep Hrud
             #Hslkc Hcslkd Hcdep Hoffrc Hcidev Hciinum Hcivalid
             Hcdlnk Hcdiat Hcmeta Hcmap Hcblocks Hctop #Hcshot Hcfrz %Hlek #Hflk Hckeep Hruc Htoken
             Hsbn Hsbi Hsbs Hsbb #Hbmr Hppid Hppback Hpath Hbsl Hislr Hop Hdirty
             Hcont".
    iDestruct "Hkeep" as (lod tld) "(%Hled & #Hfld & Hkeep)".
    iDestruct (is_itable2_claims with "Hitb2") as "#Hclaimscr".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb). clear Hbm.
    (* THE HELD SET IS EMPTY, AND SAID SO ONCE -- create's contract carries
       no order premise because it needs none, and [lkbelow] closes each
       callee's bound from this EQUATION.  Keep the equation rather than
       substituting; [lks] is spelled by name in the bodies below. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    pose proof HXregs as HXr.
    destruct HXr as (X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & Xthr).
    destruct (Hiregb cinum Hcinb) as [Hcblk Hcblog].
    destruct (Hiregb dind Hdib) as [Hdblk Hdblog].
    iDestruct (cr_esc_acc kslot Hkslt with "Hesc")
      as "#Hescc".
    iDestruct (cr_esc_acc kd Hkdlt with "Hesc")
      as "#Hescd".
    (* ---- the two rodata name windows, both PERSISTENT ---- *)
    assert (Hn3lo : (8 <= n3)%nat) by exact (proj1 Hn3).
    assert (Hn3u : (n3 <= u)%nat) by exact (proj2 Hn3).
    (* the nameiparent correlation, in the form the ledger lemmas take *)
    assert (Hcorr' : bool_decide (fsc_bmapstart ∈ Sb3) = false -> (9 <= n3)%nat).
    { intro Hf. destruct Hcorr as [Hin | Hge]; [| exact Hge].
      exfalso. rewrite (cr_crb_claim Sb3 fsc_bmapstart Hin) in Hf. discriminate. }
    (* ---- the parent's own [inode_ok] readings, once ---- *)
    assert (Hdz : bv_unsigned (di_type dn) = T_DIR_z)
      by (rewrite Htydir; vm_compute; reflexivity).
    assert (Hbmwf : blkmap_wf fsc_cov fsc_logst bm) by exact (proj1 Hiok).
    assert (Hbmcov : bm_covers bm (bv_unsigned (di_size dn)))
      by exact (proj1 (proj2 Hiok)).
    assert (Hdaddr : di_addrs dn = bm_cells bm)
      by exact (proj1 (proj2 (proj2 Hiok))).
    assert (Htynzd : bv_unsigned (di_type dn) <> 0)
      by exact (proj1 (proj2 (proj2 (proj2 Hiok)))).
    assert (Hszcap : bv_unsigned (di_size dn)
                     <= Z.of_nat MAXFILE * Z.of_nat BSIZE)
      by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hiok))))).
    assert (Hholes : blk_holes_zero bm data)
      by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hiok)))))).
    assert (Hsized : inode_sized data)
      by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hiok)))))).
    assert (Hsz31 : bv_unsigned (di_size dn) < 2 ^ 31)
      by (unfold MAXFILE, BSIZE in Hszcap; simpl in Hszcap; lia).
    (* ---- and the CHILD's, at the record the three [sh]s left ---- *)
    assert (Hcty : di_type (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                   = SpecDirlookup.T_DIR)
      by (rewrite cr_setf_type Htyc; exact Htdir).
    assert (Hctynz : bv_unsigned
                       (di_type (cr_setf dnc major minor
                                   (mword_of_int 1 : mword 16))) <> 0)
      by (rewrite Hcty; vm_compute; discriminate).
    assert (Hcdz : bv_unsigned
                     (di_type (cr_setf dnc major minor
                                 (mword_of_int 1 : mword 16))) = T_DIR_z)
      by (rewrite Hcty; vm_compute; reflexivity).
    assert (Hciok' : inode_ok fsc_cov fsc_logst
                       (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                       bmc datc)
      by exact (cr_setf_inode_ok fsc_cov fsc_logst dnc bmc datc major minor _ Hciok).
    assert (Hcdok' : dir_ok icfg_nib
                       (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                       datc)
      by exact (cr_setf_dir_ok icfg_nib dnc datc major minor _ Hcdok).
    assert (Hcsz0 : bv_unsigned
                      (di_size (cr_setf dnc major minor
                                  (mword_of_int 1 : mword 16))) = 0)
      by (rewrite cr_setf_size; exact (proj1 (proj2 Hfresh))).
    assert (Hcnrec0 : dir_nrec (bv_unsigned
              (di_size (cr_setf dnc major minor
                          (mword_of_int 1 : mword 16)))) = 0%nat)
      by (rewrite Hcsz0; exact cr_nrec_0).
    assert (Hck0 : dir_slot datc 0 = 0%nat) by apply cr_slot_0.
    assert (Hcbmwf : blkmap_wf fsc_cov fsc_logst bmc) by exact (proj1 Hciok').
    assert (Hcbmcov : bm_covers bmc (bv_unsigned
              (di_size (cr_setf dnc major minor
                          (mword_of_int 1 : mword 16)))))
      by exact (proj1 (proj2 Hciok')).
    assert (Hcaddr : di_addrs (cr_setf dnc major minor
                                 (mword_of_int 1 : mword 16)) = bm_cells bmc)
      by exact (proj1 (proj2 (proj2 Hciok'))).
    assert (Hccap : bv_unsigned (di_size (cr_setf dnc major minor
                       (mword_of_int 1 : mword 16)))
                    <= Z.of_nat MAXFILE * Z.of_nat BSIZE)
      by (rewrite Hcsz0; unfold MAXFILE, BSIZE; simpl; lia).
    assert (Hcholes : blk_holes_zero bmc datc)
      by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hciok')))))).
    assert (Hcsized : inode_sized datc)
      by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hciok')))))).
    assert (Hcsz31 : bv_unsigned (di_size (cr_setf dnc major minor
                       (mword_of_int 1 : mword 16))) < 2 ^ 31)
      by (rewrite Hcsz0; lia).
    (* the halfword bridges: both inums fit in sixteen bits *)
    assert (Hc16 : bv_unsigned cinum < 2 ^ 16) by lia.
    assert (Hcl16 : bv_unsigned (cr_low16 cinum) = bv_unsigned cinum)
      by exact (cr_low16_unsigned cinum Hc16).
    assert (Hd16 : bv_unsigned dind < 2 ^ 16) by lia.
    assert (Hdl16 : bv_unsigned (cr_low16 dind) = bv_unsigned dind)
      by exact (cr_low16_unsigned dind Hd16).
    assert (Hcl16b : bv_unsigned (cr_low16 cinum) < 16 * Z.of_nat icfg_nib)
      by (rewrite Hcl16; exact Hcinb).
    assert (Hdl16b : bv_unsigned (cr_low16 dind) < 16 * Z.of_nat icfg_nib)
      by (rewrite Hdl16; exact Hdib).
    (* the FIRST link's window is DIRECT and its slot is zero *)
    assert (Hind0 : SpecBmap.bmap_ind ((16 * 0) `div` BSIZE)%nat = false)
      by (vm_compute; reflexivity).
    assert (Hind1 : SpecBmap.bmap_ind ((16 * 1) `div` BSIZE)%nat = false)
      by (vm_compute; reflexivity).
    (* the fresh child's cell zero *)
    assert (Hcell0 : bv_unsigned (blkmap_get bmc 0) = 0).
    { apply cr_fresh_cell0.
      - rewrite -Hcaddr cr_setf_addrs. exact (proj1 (proj2 (proj2 Hfresh))).
      - exact (blkmap_wf_dir_len fsc_cov fsc_logst bmc Hcbmwf). }
    (* ===== +0xf8 lw a2,4(s3) : the child's inum ====================== *)
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0xf8)) Ra2 Rs3
              (mword_of_int 4 : mword 12) Mx (K - 10)%nat cinum b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hciinum]").
    { iApply (cri_0f8 with "Htext"). }
    { iEval (rgne; rewrite X19). iExact "Hciinum". }
    iIntros (CIDm1 Hqm1) "Hcg Hpc Hciinum".
    iEval (rgne; rewrite X19) in "Hciinum".
    pose (Z1 := <[Regidx Ra2 := regval_into_reg
                  (sign_extend' 64 cinum : mword 64)]> Mx).
    change (<[Regidx Ra2 := regval_into_reg
                  (sign_extend' 64 cinum : mword 64)]> Mx) with Z1.
    assert (HZ1a2 : Z1 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
      by (rewrite /Z1; apply upd_eq).
    assert (HZ1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor Z1)
      by (rewrite /Z1; apply cr_regs3_caller; [exact Hcsa2 | exact HXregs]).
    assert (Hq0fc : add_vec_int (mword_of_int (CK + 0xf8) : mword 64) 4
                    = mword_of_int (CK + 0xfc)) by pcw.
    iEval (rewrite Hq0fc) in "Hpc".
    (* ===== +0xfc auipc a1,0x3 ======================================= *)
    iApply (wp_auipc_s_sconf (mword_of_int (CK + 0xfc)) Ra1
              (mword_of_int 3 : mword 20) Z1 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_0fc with "Htext"). }
    iIntros (CIDm2 Hqm2) "Hcg Hpc".
    pose (Z2 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (mword_of_int (CK + 0xfc) : mword 64)
                     (auipc_off (mword_of_int 3 : mword 20)))]> Z1).
    change (<[Regidx Ra1 := regval_into_reg
                  (add_vec (mword_of_int (CK + 0xfc) : mword 64)
                     (auipc_off (mword_of_int 3 : mword 20)))]> Z1) with Z2.
    assert (HZ2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor Z2)
      by (rewrite /Z2; apply cr_regs3_caller; [exact Hcsa1 | exact HZ1regs]).
    assert (HZ2a2 : Z2 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
      by (rewrite /Z2 upd_ne; [exact HZ1a2 | nz]).
    assert (Hq100 : add_vec_int (mword_of_int (CK + 0xfc) : mword 64) 4
                    = mword_of_int (CK + 0x100)) by pcw.
    iEval (rewrite Hq100) in "Hpc".
    (* ===== +0x100 addi a1,a1,2450 : a1 = &"." ======================= *)
    iApply (wp_addi4_s_sconf (mword_of_int (CK + 0x100)) Ra1 Ra1
              (mword_of_int 2348 : mword 12) Z2 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_100 with "Htext"). }
    iIntros (CIDm3 Hqm3) "Hcg Hpc".
    pose (Z3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget Z2 Ra1)
                     (sign_extend' 64 (mword_of_int 2348 : mword 12)))]> Z2).
    change (<[Regidx Ra1 := regval_into_reg
                  (add_vec (rget Z2 Ra1)
                     (sign_extend' 64 (mword_of_int 2348 : mword 12)))]> Z2) with Z3.
    assert (HZ3a1 : Z3 !!! Regidx Ra1 = mword_of_int cr_dot_addr).
    { rewrite /Z3 upd_eq. rewrite rget_ne;
        [| intro Hz1; injection Hz1 as Hz2; vm_compute in Hz2; congruence ].
      rewrite /Z2 upd_eq. unfold cr_dot_addr. pcw. }
    assert (HZ3a2 : Z3 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
      by (rewrite /Z3 upd_ne; [exact HZ2a2 | nz]).
    assert (HZ3regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor Z3)
      by (rewrite /Z3; apply cr_regs3_caller; [exact Hcsa1 | exact HZ2regs]).
    assert (HZ3s3 : Z3 !!! Regidx Rs3 = ientry kslot)
      by (destruct HZ3regs as (_ & _ & _ & _ & H & _); exact H).
    assert (Hq104 : add_vec_int (mword_of_int (CK + 0x100) : mword 64) 4
                    = mword_of_int (CK + 0x104)) by pcw.
    iEval (rewrite Hq104) in "Hpc".
    (* ===== +0x104 c.mv a0,s3 : the CHILD ============================ *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x104)) Ra0 Rs3 Z3
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_104 with "Htext"). }
    iIntros (CIDm4 Hqm4) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (Z4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Z3 !!! Regidx Rs3))]> Z3).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Z3 !!! Regidx Rs3))]> Z3) with Z4.
    assert (HZ4a0 : Z4 !!! Regidx Ra0 = ientry kslot).
    { rewrite /Z4 upd_eq. rewrite HZ3s3. apply add_vec_zero_l. }
    assert (HZ4a1 : Z4 !!! Regidx Ra1 = mword_of_int cr_dot_addr)
      by (rewrite /Z4 upd_ne; [exact HZ3a1 | nz]).
    assert (HZ4a2 : Z4 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
      by (rewrite /Z4 upd_ne; [exact HZ3a2 | nz]).
    assert (HZ4regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor Z4)
      by (rewrite /Z4; apply cr_regs3_caller; [exact Hcsa0 | exact HZ3regs]).
    assert (Hq106 : add_vec_int (mword_of_int (CK + 0x104) : mword 64) 2
                    = mword_of_int (CK + 0x106)) by pcw.
    iEval (rewrite Hq106) in "Hpc".
    (* ===== +0x106 jal dirlink(ip, ".", ip->inum) ==================== *)
    assert (Htgd1 : add_vec (mword_of_int (CK + 0x106) : mword 64)
              (sign_extend' 64 (mword_of_int 2092330 : mword 21))
              = mword_of_int KernelSyms.dirlink) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x106)) Rra
              (mword_of_int 2092330 : mword 21) Z4 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_106 with "Htext"). }
    iIntros (CIDm5 Hqm5) "Hcg Hpc".
    iEval (rewrite Htgd1) in "Hpc".
    pose (Z5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x106) : mword 64) 4)]> Z4).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x106) : mword 64) 4)]> Z4) with Z5.
    assert (HZ5ra : Z5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x106) : mword 64) 4)
      by (rewrite /Z5; apply upd_eq).
    assert (HZ5a0 : Z5 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /Z5 upd_ne; [exact HZ4a0 | nz]).
    assert (HZ5a1 : Z5 !!! Regidx Ra1 = mword_of_int cr_dot_addr)
      by (rewrite /Z5 upd_ne; [exact HZ4a1 | nz]).
    assert (HZ5a2 : Z5 !!! Regidx Ra2
                    = (zero_extend' 64 (cr_low16 cinum) : mword 64)).
    { rewrite /Z5 upd_ne; [| nz]. rewrite HZ4a2.
      exact (cr_a2_low16 cinum Hc16). }
    assert (HZ5regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor Z5)
      by (rewrite /Z5; apply cr_regs3_caller; [exact Hcsra | exact HZ4regs]).
    iPoseProof (cr_dot_window_kt1 (Z5 !!! Regidx Ra1)
                  ltac:(exact HZ5a1) with "Hkd") as "Hdotw".
    assert (Hns3 : (1 + (ns - 3))%nat = (ns - 2)%nat) by exact (cr_ns_3 ns Hns).
    iEval (rewrite -Hns3 iref_slots_op) in "Hislr".
    iDestruct "Hislr" as "[Hislk Hislrr]".
    iDestruct (cpu_own_transport CIDm CIDm5 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iEval (rewrite /inode_map) in "Hcmap".
    iDestruct "Hcmap" as "[Hcaddrs Hcind]".
    iAssert (inode_map fsc_fs (ientry kslot) bmc) with "[Hcaddrs Hcind]"
      as "Hcmap".
    { rewrite /inode_map. iFrame. }
    (* THE BORROWED TICKET LIST FOR THE CHILD'S OWN [dirlink], hoisted here
       because the call now takes it (§7.5.6, row 3).  The body hands the
       child's ledger at [dnc]; [cr_setf] moves only [nlink]/[major]/[minor]
       and at a FRESH child the big-op is empty either way, so it is rebuilt
       rather than transported.  It comes back verbatim on both arms. *)
    iAssert (dlinks fsc_fs (bv_unsigned cinum)
               (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc)%I
      as "Hcdlnk0i".
    assert (Hc1dokE : FsStateInode.ent_dset_ok (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc) ∅)
      by (intros tz Htz; exfalso; exact (not_elem_of_empty tz Htz)).
    assert (Hc1xactE : FsStateInode.node_exact (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc) ∅).
    { intros _.
      assert (Hfn1 : fn_nlink (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc) = 1%nat)
        by (rewrite /fn_nlink era_node_rec cr_setf_nlink;
            vm_compute; reflexivity).
      rewrite /fn_orphan Hfn1
        (bool_decide_eq_false_2 (1%nat = 0%nat)
           ltac:(intros Hcz; discriminate Hcz)) size_empty //. }
    { rewrite /dlinks /FsStateInode.ent_toks_x. iExists ∅.
      iSplitR; [iPureIntro; exact Hc1dokE |].
      iSplitR; [iPureIntro; exact Hc1xactE |].
      iApply FsStateEra.ent_toks_era_nrec0.
      rewrite cr_setf_size; exact Hcnrec0. }
    (* THE LICENCE'S LEFT DISJUNCT HERE IS [ip->nlink = 1], flushed by the
       three [sh]s at +0xfc..+0x102 before this call (§7.5.6, row 3): the
       record the contract runs at IS [cr_setf dnc _ _ 1]. *)
    (* THE SHARE DIRLINK'S OWN [iput] MAY NEED (durable-disk B''-tx5).  Inside
       the armed span this walk holds no free residue -- a quarter is in each
       escrow and the registry's arm has the half -- so it shrinks the
       PARENT'S arm by an eighth for the duration of the call and grows it
       back at the return.  The eighth is enough: what iput's windows need is
       a POSITIVE share of an OPEN transaction, and any is. *)
    iDestruct "Hdep" as (lodc tldc) "(%Hledc & #Hfldc & Hdep)".
    iApply fupd_wp.
    iMod (ic_shrink_tx ⊤ fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kd (qd/2)%Qp icfg_dev dind gd _ true
            t (1/4) ((1/4)/2) ((1/4)/2) (eq_sym (Qp.div_2 (1/4)))
            ltac:(solve_ndisj) with "Hescd Hivalid Hdep")
      as "(Hivalid & Hdep & Htxs)".
    iModIntro.
    iApply (DLK.wp_dirlink_gen γs j γl pd pav pu
 γf
              (ientry kslot) cinum bmc datc
              (cr_setf dnc major minor (mword_of_int 1 : mword 16))
              (cr_setf dnc major minor (mword_of_int 1 : mword 16))
              cr_dot_f (cr_low16 cinum) n3 Sb3
              _ _
              pidv (DfracOwn (1/4)) (DfracOwn (1/2)) DfracDiscarded dqs
              dqb dqbs (DfracOwn (1/2))
              Z5 (K - 10)%nat eb b lks
              U ltac:(exact HKdlk) Hcty Hcbmcov Hccap
              ltac:(exact (Hcdok' Hcdz))
              ltac:(left; rewrite cr_setf_nlink; vm_compute; discriminate)
              ltac:(apply dir_orphan_clean_live;
                    rewrite cr_setf_nlink; vm_compute; discriminate)
              ltac:(exact (di_type_stable_refl _))
              ltac:(exact (di_nlink_stable_refl _ Hctynz))
              Hlg Hcbmwf Hcholes Hcaddr Hcsz31 Hist0 Hcblk Hcblog Hcinb
              Hcl16b Hbmgeo Hpkc Hsize Hbms0 Hbmsc Hbmsl Hcovb Hiregb
              ltac:(rewrite Hcnrec0 Hck0; rewrite Hind0;
                    exact (cr_alloc_dlneed n3 _ false Hn3lo))
              Hj Hgs HZ5a0 HZ5a2 Heb ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hkd Hpk Hbio Hlogc Hkenv
                    Hcidev Hciinum Hcmeta Hcmap Hcblocks Hdotw Hsbi Hsbs Hsbb
                    Hbmr Hiregi Hiopen Hcdiat Hppid Hprocs Hdevi Hgeom Hdlk Hbsl
                    Hitb2 Hitbl Hesc Hslks Hislk Hcdlnk0i Hop Htxs").
    all: try lkbelow.
    iIntros (CIDd1 Hsd1 md1 found1 bm1 dat1 dc1 dc01 n4 Sb4 tot1)
      "%Hcsd1 Hcg Hcnt Hpc Hcidev Hciinum Hcmeta Hcmap Hcblocks Hdotw1 Hsbi
       Hsbs Hsbb Hcdiat Hppid Hbsl Hislk Hcdlnk0 %Hn4c %Hsb4 %Hdlp1 %Hfd1
       Hop Htxs %Hcap1 %Hsizedp1 %Harm1".

    iApply fupd_wp.
    iMod (ic_grow_tx ⊤ fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kd (qd/2)%Qp icfg_dev dind gd _ true
            t (1/4) ((1/4)/2) ((1/4)/2) (eq_sym (Qp.div_2 (1/4)))
            ltac:(solve_ndisj) with "Hescd Hivalid Hdep Htxs")
      as "(Hivalid & Hdep)".
    iModIntro.

    (* the borrow comes back as the PAIR; open it here, because the deposit
       below files the child's ["."] entry among its own units *)
    iRename "Hcdlnk0" into "Hcdlnk0P".
    iDestruct (dlinks_open with "Hcdlnk0P")
      as "(%Dc & [%HcdokD %HcxactD] & Hcetk)".
    assert (Hpcd1 : ret_pc (Z5 !!! Regidx Rra : mword 64)
                    = mword_of_int (CK + 0x10a)) by (rewrite HZ5ra; pcw).
    iEval (rewrite Hpcd1) in "Hpc".
    assert (Hmd1regs : cr_regs3 m sp0 (ientry kd)
                         (mword_of_int 0 : mword 64) (ientry kslot)
                         ty major minor md1)
      by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                  (ientry kslot) ty major minor Z5 md1 Hcsd1 HZ5regs).
    assert (Htg146a : add_vec (mword_of_int (CK + 0x10a) : mword 64)
              (sign_extend' 64 (mword_of_int 60 : mword 13))
              = mword_of_int (CK + 0x146)) by pcw.
    (* the FOUND arm is refuted: an EMPTY directory has no records *)
    destruct found1.
    { exfalso. destruct Harm1 as (Hfst & _). apply Hfst.
      rewrite Hcnrec0. apply cr_first_0. }
    destruct Harm1 as (_ & Hwf1 & Hholes1 & Haddr1 & Hsz311 &
                       Hcov1 & Hdc1 & Hdc01 & Htot161 & Hrng1 & Hbl1).
    destruct (Hdlp1 eq_refl) as (Hspend1 & Hatom1 & Hmem1).
    rewrite Hcnrec0 Hck0 in Hspend1, Hmem1, Hrng1, Hdc1.
    (* the region's record IS the metadata one: the first link's writei ran
       its trailing [iupdate] ([dl16_post]'s preservation clause, at the
       [eq_refl] the caller's single [dinode_at] supplies). *)
    assert (Hdceq1 : dc01 = dc1) by exact (Hdc01 eq_refl).
    subst dc01.
    (* ---- the record the first link left, read back off its range clause *)
    assert (Hc1ty0 : di_type dc1
                     = di_type (cr_setf dnc major minor
                                  (mword_of_int 1 : mword 16)))
      by (rewrite Hdc1; reflexivity).
    assert (Hc1mj0 : di_major dc1
                     = di_major (cr_setf dnc major minor
                                   (mword_of_int 1 : mword 16)))
      by (rewrite Hdc1; reflexivity).
    assert (Hc1mn0 : di_minor dc1
                     = di_minor (cr_setf dnc major minor
                                   (mword_of_int 1 : mword 16)))
      by (rewrite Hdc1; reflexivity).
    assert (Hc1nl0 : di_nlink dc1
                     = di_nlink (cr_setf dnc major minor
                                   (mword_of_int 1 : mword 16)))
      by (rewrite Hdc1; reflexivity).
    assert (Hc1ty : di_type dc1 = ty)
      by (rewrite Hc1ty0 cr_setf_type; exact Htyc).
    assert (Hc1mj : di_major dc1 = major)
      by (rewrite Hc1mj0; apply cr_setf_major).
    assert (Hc1mn : di_minor dc1 = minor)
      by (rewrite Hc1mn0; apply cr_setf_minor).
    assert (Hc1nl : di_nlink dc1 = (mword_of_int 1 : mword 16))
      by (rewrite Hc1nl0; apply cr_setf_nlink).
    assert (Hc1tyd : di_type dc1 = SpecDirlookup.T_DIR)
      by (rewrite Hc1ty; exact Htdir).
    assert (Hc1tynz : bv_unsigned (di_type dc1) <> 0)
      by (rewrite Hc1ty Htdir; vm_compute; discriminate).
    assert (Hc1iok : inode_ok fsc_cov fsc_logst dc1 bm1 dat1).
    { rewrite /inode_ok. split_and!.
      - exact Hwf1.
      - exact Hcov1.
      - exact Haddr1.
      - exact Hc1tynz.
      - exact (Hcap1 Hccap).
      - exact Hholes1.
      - exact (Hsizedp1 Hcsized). }
    assert (Hc1szmax : bv_unsigned (di_size dc1)
              = Z.max (bv_unsigned (di_size (cr_setf dnc major minor
                          (mword_of_int 1 : mword 16))))
                  (Z.of_nat ((16 * 0)%nat + tot1)))
      by (rewrite Hdc1;
          exact (cr_wi_size_max _ bm1 (16 * 0)%nat tot1 ltac:(lia))).
    assert (Hc1dok : dir_ok icfg_nib dc1 dat1)
      by exact (dir_ok_dirlink icfg_nib
                  (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                  dc1 datc dat1 (cr_low16 cinum) (bname 14 cr_dot_f)
                  0%nat 0%nat tot1 (eq_sym Hcnrec0) (eq_sym Hck0) Htot161
                  Hcl16b Hc1ty0 Hc1szmax Hrng1 Hcdok').
    (* UNIQUENESS across the same link.  The entry is a FRESH child, whose
       size is 0 and which therefore has no records to collide; the guard
       [dir_first datc 0 _ = None] is free for the same reason. *)
    assert (Hc1duq : dir_uniq dc1 dat1)
      by exact (dir_uniq_dirlink
                  (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                  dc1 datc dat1 (cr_low16 cinum) (bname 14 cr_dot_f)
                  0%nat 0%nat tot1 (eq_sym Hcnrec0) (eq_sym Hck0) Hatom1
                  (bname_length_le 14 cr_dot_f) (cut_nul_nonul _)
                  Hc1ty0 Hc1szmax Hrng1 (cr_first_0 datc (bname 14 cr_dot_f))
                  (dir_uniq_size_zero _ datc Hcsz0)).
    (* FAIL ENTRY 1's content clause: on the short arm the ["."] write left
       fewer than sixteen bytes, so the child's size is [tot1 < 16] and it
       has NO records at all -- [dir_dots_only] is vacuous at [nrec = 0].
       Stated guarded so it can sit above the [Hbl1] split, beside the
       record facts the two arms share. *)
    assert (Hc1dots : (tot1 < 16)%nat -> dir_dots_only dc1 dat1).
    { intros Hlt k Hk. exfalso.
      assert (Hnr0 : dir_nrec (bv_unsigned (di_size dc1)) = 0%nat).
      { rewrite Hc1szmax Hcsz0. unfold dir_nrec.
        rewrite Z.div_small; [reflexivity | clear -Hlt; lia]. }
      rewrite Hnr0 in Hk. clear -Hk. lia. }
    (* the ledger, at the two figures this arm's exits are stated at *)
    rewrite (cr_crb_claim Sb3 (IBLOCK cinum icfg_ist) Hmem3) Hind0
      in Hspend1.
    destruct Hbl1 as [[Ha0z1 Ht161] | [Ha0m1 Htlt1]].
    - (* =============================================================== *)
      (*  the FIRST link went in whole: fall through to [dirlink(ip,"..")] *)
      (* =============================================================== *)
      (* ===== +0x10a bltz a0 : FALLS THROUGH ========================= *)
      iApply (wp_blt_x0_fall_s_sconf (mword_of_int (CK + 0x10a))
                (mword_of_int 60 : mword 13) Ra0 md1 (K - 10)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite Ha0z1; exact cr_bltz_zero)
                with "Hcg Hpc []").
      { iApply (cri_10a with "Htext"). }
      iIntros (CIDe1 Hqe1) "Hcg Hpc".
      assert (Hq10e : add_vec_int (mword_of_int (CK + 0x10a) : mword 64) 4
                      = mword_of_int (CK + 0x10e)) by pcw.
      iEval (rewrite Hq10e) in "Hpc".
      (* THE ["."] RECORD IS A SELF RECORD,
         so the entry it creates is TOKENLESS and no unit is spent
         (durable-disk 2b-inode-5, [FsStateInode.ent_tokenless]). *)
      (* THE ["."] ENTRY OWES A FRAGMENT NOW (lane G5).  The fill minted
         TWO -- this one and the one [dirlink(dp, name, ip)] files -- and
         this one is what PINS the child's [".."] target once the next
         [dirlink] writes it ([FsStateInode.ent_ty_ok]'s dot arm).  Its
         clause is VACUOUS here: the child has no records at all, so its
         [fn_dd] is [None]. *)
      assert (Htdirc : ty = SpecDirlookup.T_DIR).
      { apply bv_eq. rewrite -Htyc -(cr_setf_type dnc major minor
          (mword_of_int 1 : mword 16)) Hcdz. vm_compute. reflexivity. }
      assert (Hcfn1 : fn_nlink (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc) = 1%nat)
        by (rewrite /fn_nlink era_node_rec cr_setf_nlink;
            vm_compute; reflexivity).
      assert (HDc : Dc = ∅).
      { pose proof (HcxactD ltac:(rewrite /fn_is_dir /fn_type era_node_rec;
                                 apply bool_decide_eq_true; exact Hcdz)) as Hex.
        rewrite Hcfn1 /fn_orphan Hcfn1
          (bool_decide_eq_false_2 (1%nat = 0%nat)
           ltac:(intros Hcz; discriminate Hcz)) in Hex.
        apply leibniz_equiv, size_empty_inv. clear -Hex. lia. }
      assert (Hcents0 : dir_entries (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc) = ∅).
      { rewrite /dir_entries.
        destruct (fn_is_dir (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc)); [| reflexivity].
        change (fn_nrec (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc))
          with (dir_nrec (bv_unsigned (di_size (cr_setf dnc major minor (mword_of_int 1 : mword 16))))).
        rewrite cr_setf_size Hcnrec0 dir_view_nil //. }
      assert (Hcddnone : FsStateInode.fn_dd (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc) = None)
        by (rewrite /FsStateInode.fn_dd Hcents0 lookup_empty //).
      iEval (rewrite (cr_delta_dir ty Htdirc)
                     FsStateLink.link_toks_reps_S FsStateLink.link_reps_1)
        in "Htoken".
      iDestruct "Htoken" as "[Htokdot Htoken]".
      iDestruct (ent_toks_dirlink_arm (fs_gamma_L fsc_fs) (bv_unsigned cinum)
                   (cr_setf dnc major minor (mword_of_int 1 : mword 16)) dc1
                   bmc bm1 datc dat1 (cr_low16 cinum) (bname 14 cr_dot_f)
                   0%nat 0%nat tot1 Dc false (eq_sym Hcnrec0) (eq_sym Hck0)
                   Hatom1
                   (bname_length_le 14 cr_dot_f) (cut_nul_nonul _)
                   Hcdz Hc1ty0 Hc1nl0 Hc1szmax Hrng1
                   (cr_first_0 datc (bname 14 cr_dot_f))
                   Hcholes Hholes1 Hccap (Hcap1 Hccap)
                   ltac:(rewrite HDc; apply not_elem_of_empty)
                   ltac:(rewrite ProofCreateParts.cr_dot_name /DOTDOT;
                         intros Hcdd; discriminate Hcdd)
                   with "Hcetk [Htokdot]") as "Hcetk1".
      { iEval (rewrite -Hcl16) in "Htokdot".
        iApply (ent_tok_of_link (fs_gamma_L fsc_fs) (bv_unsigned cinum)
                  (FsStateInode.fn_dd (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc))
                  (fn_orphan (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc)) false
                  (bname 14 cr_dot_f) (bv_unsigned (cr_low16 cinum))
                  (cr_ity ty (bv_unsigned dind))
                  ltac:(rewrite Hcddnone;
                        apply FsStateInode.ent_ty_ok_dot_none)
                  with "Htokdot"). }
      assert (Hc1dok' : FsStateInode.ent_dset_ok (era_node dc1 bm1 dat1) Dc)
        by (rewrite HDc; intros tz Htz;
          exfalso; exact (not_elem_of_empty tz Htz)).
      assert (Hc1xact' : FsStateInode.node_exact (era_node dc1 bm1 dat1) Dc).
      { intros _.
        assert (Hfn : fn_nlink (era_node dc1 bm1 dat1) = 1%nat)
          by (rewrite /fn_nlink era_node_rec Hc1nl; vm_compute; reflexivity).
        rewrite Hfn /fn_orphan Hfn
          (bool_decide_eq_false_2 (1%nat = 0%nat)
           ltac:(intros Hcz; discriminate Hcz)) HDc
          size_empty //. }
      iDestruct (dlinks_intro _ _ _ _ _ Dc Hc1dok' Hc1xact'
                   with "Hcetk1") as "Hcdlnk1".
      (* THE FIRST LINK ALLOCATED, and the whole arm's ledger rests on it *)
      assert (Hc1sz : bv_unsigned (di_size dc1) = 16).
      { rewrite Hc1szmax Hcsz0 Ht161. clear -dc1. lia. }
      assert (Hal1 : SpecBmap.bmap_alloced bmc bm1 0 = true).
      { apply cr_alloced_first; [exact Hcell0 |].
        apply (bm_covers_get bm1 (bv_unsigned (di_size dc1)) 0%nat Hcov1
                 ltac:(unfold MAXFILE; lia)).
        rewrite Hc1sz. unfold BSIZE. lia. }
      assert (Hal1' : SpecBmap.bmap_alloced bmc bm1 (16 * 0 / BSIZE)%nat
                      = true) by exact Hal1.
      rewrite Hal1' in Hspend1.
      (* [Hmem1]'s premise, hoisted: spliced as [ltac:(lia)] it was reified
         against this arm's whole context three times over
         (claude-notes/optimization.md, "an [ltac:(lia)] in argument position
         cannot be fixed by [clear -] -- hoist it"). *)
      assert (Htot1pos : (0 < tot1)%nat) by (clear -Ht161; lia).
      assert (Hbmem4 : fsc_bmapstart ∈ Sb4)
        by exact (proj2 (proj2 (Hmem1 Htot1pos)) Hal1).
      assert (Hcmem4 : IBLOCK cinum icfg_ist ∈ Sb4)
        by exact (proj1 (proj2 (Hmem1 Htot1pos))).
      assert (Hdmem4 : wi_tgt_blk bm1 (16 * 0)%nat ∈ Sb4)
        by exact (proj1 (Hmem1 Htot1pos)).
      assert (Hcrb2 : bool_decide (fsc_bmapstart ∈ Sb4) = true)
        by exact (cr_crb_claim Sb4 fsc_bmapstart Hbmem4).
      (* the SECOND link's slot: record zero is LIVE at the child's inum *)
      assert (Hwin1 : forall jj, (jj < 16)%nat ->
                file_byte dat1 (16 * 0 + jj)%nat
                = dirent_bytes (de_of_name (cr_low16 cinum)
                                  (bname 14 cr_dot_f)) !!! jj).
      { intros jj Hjj. rewrite (Hrng1 (16 * 0 + jj)%nat).
        rewrite decide_True; [| clear -Hjj Ht161; lia].
        (* optimization.md: [replace ... by lia] pays the whole ambient
           context in its side proof; the identity needs [jj] alone. *)
        replace (16 * 0 + jj - 16 * 0)%nat with jj by (clear -jj; lia).
        reflexivity. }
      destruct (cr_dot_record dat1 (cr_low16 cinum) Hwin1)
        as [Hd1inum Hd1name].
      assert (Hd1live : dir_inum dat1 0 <> bv_0 16).
      { rewrite Hd1inum. intro Hc.
        assert (Hz : bv_unsigned (cr_low16 cinum) = 0)
          by (rewrite Hc; vm_compute; reflexivity).
        rewrite Hcl16 in Hz. pose proof (proj1 Hcpos) as Hp. lia. }
      assert (Hc1nrec : dir_nrec (bv_unsigned (di_size dc1)) = 1%nat)
        by (rewrite Hc1sz; exact cr_nrec_16).
      assert (Hc1k0 : dir_slot dat1 1 = 1%nat) by exact (cr_slot_1 dat1 Hd1live).
      (* THE CHILD'S ["."] ENTRY, as a fact about its ENTRY VIEW (lane G5).
         Every fail entry below this point has to reach through the child's
         payload for the fragment that record owes -- the [ip->nlink = 0]
         flush spends the WHOLE pile the fill minted, and one of its units
         is filed here -- so the reading is stated once, in the arm that
         wrote the record. *)
      assert (Hc1dzc : bv_unsigned (di_type dc1) = T_DIR_z)
        by (rewrite Hc1ty Htdirc; vm_compute; reflexivity).
      assert (Horph1c : fn_orphan (era_node dc1 bm1 dat1) = false).
      { rewrite /fn_orphan /fn_nlink era_node_rec Hc1nl.
        apply bool_decide_eq_false. clear. vm_compute. discriminate. }
      assert (Hdot1c : dir_entries (era_node dc1 bm1 dat1) !! DOT
                       = Some (bv_unsigned cinum)).
      { rewrite (dir_entries_era_node dc1 bm1 dat1 Hholes1 (Hcap1 Hccap))
          (bool_decide_eq_true_2 _ Hc1dzc) Hc1nrec -Hcl16 -Hd1inum.
        replace DOT with (dir_bname dat1 0%nat)
          by (rewrite /dir_bname Hd1name DOT_dot_name; reflexivity).
        exact (dir_view_live dat1 1%nat 0%nat
                 ltac:(rewrite -Hc1nrec; exact (Hc1duq Hc1dzc))
                 ltac:(clear; apply Nat.lt_0_succ) Hd1live). }
      (* ===== +0x10e c.lw a2,4(s1) : the PARENT's inum ================ *)
      iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x10e)) Ra2 Rs1
                (mword_of_int 4 : mword 12) md1 (K - 10)%nat dind b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hiinum]").
      { iApply (cri_10e with "Htext"). }
      { iEval (rgne; rewrite (proj1 (proj2 (proj2 Hmd1regs)))). iExact "Hiinum". }
      iIntros (CIDe2 Hqe2) "Hcg Hpc Hiinum".
      iEval (rgne; rewrite (proj1 (proj2 (proj2 Hmd1regs)))) in "Hiinum".
      pose (Y1 := <[Regidx Ra2 := regval_into_reg
                    (sign_extend' 64 dind : mword 64)]> md1).
      change (<[Regidx Ra2 := regval_into_reg
                    (sign_extend' 64 dind : mword 64)]> md1) with Y1.
      assert (HY1a2 : Y1 !!! Regidx Ra2 = (sign_extend' 64 dind : mword 64))
        by (rewrite /Y1; apply upd_eq).
      assert (HY1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor Y1)
        by (rewrite /Y1; apply cr_regs3_caller; [exact Hcsa2 | exact Hmd1regs]).
      assert (Hq110 : add_vec_int (mword_of_int (CK + 0x10e) : mword 64) 2
                      = mword_of_int (CK + 0x110)) by pcw.
      iEval (rewrite Hq110) in "Hpc".
      (* ===== +0x110 auipc a1,0x3 ==================================== *)
      iApply (wp_auipc_s_sconf (mword_of_int (CK + 0x110)) Ra1
                (mword_of_int 3 : mword 20) Y1 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cri_110 with "Htext"). }
      iIntros (CIDe3 Hqe3) "Hcg Hpc".
      pose (Y2 := <[Regidx Ra1 := regval_into_reg
                    (add_vec (mword_of_int (CK + 0x110) : mword 64)
                       (auipc_off (mword_of_int 3 : mword 20)))]> Y1).
      change (<[Regidx Ra1 := regval_into_reg
                    (add_vec (mword_of_int (CK + 0x110) : mword 64)
                       (auipc_off (mword_of_int 3 : mword 20)))]> Y1) with Y2.
      assert (HY2a2 : Y2 !!! Regidx Ra2 = (sign_extend' 64 dind : mword 64))
        by (rewrite /Y2 upd_ne; [exact HY1a2 | nz]).
      assert (HY2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor Y2)
        by (rewrite /Y2; apply cr_regs3_caller; [exact Hcsa1 | exact HY1regs]).
      assert (Hq114 : add_vec_int (mword_of_int (CK + 0x110) : mword 64) 4
                      = mword_of_int (CK + 0x114)) by pcw.
      iEval (rewrite Hq114) in "Hpc".
      (* ===== +0x114 addi a1,a1,2438 : a1 = &".." ==================== *)
      iApply (wp_addi4_s_sconf (mword_of_int (CK + 0x114)) Ra1 Ra1
                (mword_of_int 2336 : mword 12) Y2 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cri_114 with "Htext"). }
      iIntros (CIDe4 Hqe4) "Hcg Hpc".
      pose (Y3 := <[Regidx Ra1 := regval_into_reg
                    (add_vec (rget Y2 Ra1)
                       (sign_extend' 64 (mword_of_int 2336 : mword 12)))]> Y2).
      change (<[Regidx Ra1 := regval_into_reg
                    (add_vec (rget Y2 Ra1)
                       (sign_extend' 64 (mword_of_int 2336 : mword 12)))]> Y2) with Y3.
      assert (HY3a1 : Y3 !!! Regidx Ra1 = mword_of_int cr_dotdot_addr).
      { rewrite /Y3 upd_eq. rewrite rget_ne;
          [| intro Hz1; injection Hz1 as Hz2; vm_compute in Hz2; congruence ].
        rewrite /Y2 upd_eq. unfold cr_dotdot_addr. pcw. }
      assert (HY3a2 : Y3 !!! Regidx Ra2 = (sign_extend' 64 dind : mword 64))
        by (rewrite /Y3 upd_ne; [exact HY2a2 | nz]).
      assert (HY3regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor Y3)
        by (rewrite /Y3; apply cr_regs3_caller; [exact Hcsa1 | exact HY2regs]).
      assert (HY3s3 : Y3 !!! Regidx Rs3 = ientry kslot)
        by (destruct HY3regs as (_ & _ & _ & _ & H & _); exact H).
      assert (Hq118 : add_vec_int (mword_of_int (CK + 0x114) : mword 64) 4
                      = mword_of_int (CK + 0x118)) by pcw.
      iEval (rewrite Hq118) in "Hpc".
      (* ===== +0x118 c.mv a0,s3 : the CHILD ========================== *)
      iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x118)) Ra0 Rs3 Y3
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cri_118 with "Htext"). }
      iIntros (CIDe5 Hqe5) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (Y4 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Y3 !!! Regidx Rs3))]> Y3).
      change (<[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Y3 !!! Regidx Rs3))]> Y3) with Y4.
      assert (HY4a0 : Y4 !!! Regidx Ra0 = ientry kslot).
      { rewrite /Y4 upd_eq. rewrite HY3s3. apply add_vec_zero_l. }
      assert (HY4a1 : Y4 !!! Regidx Ra1 = mword_of_int cr_dotdot_addr)
        by (rewrite /Y4 upd_ne; [exact HY3a1 | nz]).
      assert (HY4a2 : Y4 !!! Regidx Ra2 = (sign_extend' 64 dind : mword 64))
        by (rewrite /Y4 upd_ne; [exact HY3a2 | nz]).
      assert (HY4regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor Y4)
        by (rewrite /Y4; apply cr_regs3_caller; [exact Hcsa0 | exact HY3regs]).
      assert (Hq11a : add_vec_int (mword_of_int (CK + 0x118) : mword 64) 2
                      = mword_of_int (CK + 0x11a)) by pcw.
      iEval (rewrite Hq11a) in "Hpc".
      (* ===== +0x11a jal dirlink(ip, "..", dp->inum) ================= *)
      assert (Htgd2 : add_vec (mword_of_int (CK + 0x11a) : mword 64)
                (sign_extend' 64 (mword_of_int 2092310 : mword 21))
                = mword_of_int KernelSyms.dirlink) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (CK + 0x11a)) Rra
                (mword_of_int 2092310 : mword 21) Y4 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_11a with "Htext"). }
      iIntros (CIDe6 Hqe6) "Hcg Hpc".
      iEval (rewrite Htgd2) in "Hpc".
      pose (Y5 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0x11a) : mword 64) 4)]> Y4).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0x11a) : mword 64) 4)]> Y4) with Y5.
      assert (HY5ra : Y5 !!! Regidx Rra
                      = add_vec_int (mword_of_int (CK + 0x11a) : mword 64) 4)
        by (rewrite /Y5; apply upd_eq).
      assert (HY5a0 : Y5 !!! Regidx Ra0 = ientry kslot)
        by (rewrite /Y5 upd_ne; [exact HY4a0 | nz]).
      assert (HY5a1 : Y5 !!! Regidx Ra1 = mword_of_int cr_dotdot_addr)
        by (rewrite /Y5 upd_ne; [exact HY4a1 | nz]).
      assert (HY5a2 : Y5 !!! Regidx Ra2
                      = (zero_extend' 64 (cr_low16 dind) : mword 64)).
      { rewrite /Y5 upd_ne; [| nz]. rewrite HY4a2.
        exact (cr_a2_low16 dind Hd16). }
      assert (HY5regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor Y5)
        by (rewrite /Y5; apply cr_regs3_caller; [exact Hcsra | exact HY4regs]).
      iPoseProof (cr_dotdot_window_kt1 (Y5 !!! Regidx Ra1)
                    ltac:(exact HY5a1) with "Hkd") as "Hddw".
      iDestruct (cpu_own_transport CIDd1 CIDe6 0%nat eb (proc_addr j) b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      (* claude-notes/optimization.md: an inline [ltac:] closer is priced by
         the DEPTH of its call site, and with [rget]/[tp_pin]/[rf_upd] sealed
         opaque above, this arm's ambient context is large enough that the
         inline form of this bound regressed [1.36 s -> 8.26 s] (measured,
         isolated [coqc -time], 2026-08-15) -- ProofPipewrite.v's Strategy
         header documents the same shape.  Hoisted to a named [assert] with
         an explicit [clear] down to the six facts [lia] actually draws on
         ([Hn3lo], the eighth-block floor threaded from three [dirlink]s up,
         is the one a first [clear -H..] attempt here dropped -- it is not
         mentioned by the rewrite/pose chain below, only by [lia] itself). *)
      assert (Hdlneed4 :
                (SpecDirlink.dl_need (bool_decide (fsc_bmapstart ∈ Sb4))
                   (SpecBmap.bmap_ind
                      ((16 * dir_slot dat1
                              (dir_nrec (bv_unsigned (di_size dc1))))
                       `div` BSIZE)%nat)
                 <= n4)%nat).
      { clear -Hc1nrec Hc1k0 Hind1 Hcrb2 Hspend1 Hn3lo.
        rewrite Hc1nrec Hc1k0 Hind1 Hcrb2
                (proj1 (proj2 SpecDirlink.dl_need_values)).
        pose proof (cr_mkdir_dl1 n3 n4 _ _ _ Hspend1); lia. }
    (* THE SHARE DIRLINK'S OWN [iput] MAY NEED (durable-disk B''-tx5).  Inside
       the armed span this walk holds no free residue -- a quarter is in each
       escrow and the registry's arm has the half -- so it shrinks the
       PARENT'S arm by an eighth for the duration of the call and grows it
       back at the return.  The eighth is enough: what iput's windows need is
       a POSITIVE share of an OPEN transaction, and any is. *)
    iApply fupd_wp.
    iMod (ic_shrink_tx ⊤ fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kd (qd/2)%Qp icfg_dev dind gd _ true
            t (1/4) ((1/4)/2) ((1/4)/2) (eq_sym (Qp.div_2 (1/4)))
            ltac:(solve_ndisj) with "Hescd Hivalid Hdep")
      as "(Hivalid & Hdep & Htxs)".
    iModIntro.
      iApply (DLK.wp_dirlink_gen γs j γl pd pav pu
 γf
                (ientry kslot) cinum bm1 dat1 dc1 dc1
                cr_dotdot_f (cr_low16 dind) n4 Sb4
                _ _
                pidv (DfracOwn (1/4)) (DfracOwn (1/2)) DfracDiscarded dqs
                dqb dqbs (DfracOwn (1/2))
                Y5 (K - 10)%nat eb b lks
                U ltac:(exact HKdlk) Hc1tyd Hcov1 (Hcap1 Hccap)
                ltac:(exact (Hc1dok ltac:(rewrite Hc1ty Htdir;
                                          vm_compute; reflexivity)))
                (* §7.5.6, row 4: LEFT disjunct from [ip->nlink = 1], the
                   value the three [sh]s flushed before the ["."] link and
                   which that link carried through unchanged ([Hc1nl]). *)
                ltac:(left; rewrite Hc1nl; vm_compute; discriminate)
                ltac:(apply dir_orphan_clean_live;
                      rewrite Hc1nl; vm_compute; discriminate)
                ltac:(exact (di_type_stable_refl _))
                ltac:(exact (di_nlink_stable_refl _ Hc1tynz))
                Hlg Hwf1 Hholes1 Haddr1 Hsz311 Hist0 Hcblk Hcblog Hcinb
                Hdl16b Hbmgeo Hpkc Hsize Hbms0 Hbmsc Hbmsl Hcovb Hiregb
                Hdlneed4
                Hj Hgs HY5a0 HY5a2 Heb ltac:(lkbelow)
                with "Hcg Hcnt Htext Hpc Hkd Hpk Hbio Hlogc Hkenv
                      Hcidev Hciinum Hcmeta Hcmap Hcblocks Hddw Hsbi Hsbs Hsbb
                      Hbmr Hiregi Hiopen Hcdiat Hppid Hprocs Hdevi Hgeom Hdlk Hbsl
                      Hitb2 Hitbl Hesc Hslks Hislk Hcdlnk1 Hop Htxs").
      all: try lkbelow.
      iIntros (CIDd2 Hsd2 md2 found2 bm2 dat2 dc2 dc02 n5 Sb5 tot2)
        "%Hcsd2 Hcg Hcnt Hpc Hcidev Hciinum Hcmeta Hcmap Hcblocks Hddw2 Hsbi
         Hsbs Hsbb Hcdiat Hppid Hbsl Hislk Hcdlnk1 %Hn5c %Hsb5 %Hdlp2 %Hfd2
         Hop Htxs %Hcap2 %Hsizedp2 %Harm2".

    iApply fupd_wp.
    iMod (ic_grow_tx ⊤ fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kd (qd/2)%Qp icfg_dev dind gd _ true
            t (1/4) ((1/4)/2) ((1/4)/2) (eq_sym (Qp.div_2 (1/4)))
            ltac:(solve_ndisj) with "Hescd Hivalid Hdep Htxs")
      as "(Hivalid & Hdep)".
    iModIntro.

      iRename "Hcdlnk1" into "Hcdlnk1P".
      iDestruct (dlinks_open with "Hcdlnk1P")
        as "(%Dc1 & [%Hcdok1 %Hcxact1] & Hcetk2)".
      assert (Hpcd2 : ret_pc (Y5 !!! Regidx Rra : mword 64)
                      = mword_of_int (CK + 0x11e)) by (rewrite HY5ra; pcw).
      iEval (rewrite Hpcd2) in "Hpc".
      assert (Hmd2regs : cr_regs3 m sp0 (ientry kd)
                           (mword_of_int 0 : mword 64) (ientry kslot)
                           ty major minor md2)
        by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (ientry kslot) ty major minor Y5 md2 Hcsd2 HY5regs).
      assert (Htg146b : add_vec (mword_of_int (CK + 0x11e) : mword 64)
                (sign_extend' 64 (mword_of_int 40 : mword 13))
                = mword_of_int (CK + 0x146)) by pcw.
      (* the FOUND arm is refuted: slot zero's name is ["."] and not [".."] *)
      destruct found2.
      { exfalso. destruct Harm2 as (Hfst & _). apply Hfst.
        rewrite Hc1nrec.
        exact (cr_first_miss_dotdot dat1 (cr_low16 cinum) Hwin1). }
      destruct Harm2 as (_ & Hwf2 & Hholes2 & Haddr2 & Hsz312 &
                         Hcov2 & Hdc2 & Hdc02 & Htot162 & Hrng2 & Hbl2).
      destruct (Hdlp2 eq_refl) as (Hspend2 & Hatom2 & Hmem2).
      rewrite Hc1nrec Hc1k0 in Hspend2, Hmem2, Hrng2, Hdc2.
      (* [crd] at the second link is NOT derivable -- [dl16_post]'s [crd]
         names the POST blkmap, and nothing relates it to the first link's.
         It is also not needed: at [crb2 = true] the spend is at most one at
         EVERY value of [crd2]. *)
      rewrite Hcrb2 (cr_crb_claim Sb4 (IBLOCK cinum icfg_ist) Hcmem4)
        Hind1 in Hspend2.
      assert (Hdceq2 : dc02 = dc2) by exact (Hdc02 eq_refl).
      subst dc02.
      assert (Hc2ty0 : di_type dc2 = di_type dc1) by (rewrite Hdc2; reflexivity).
      assert (Hc2mj0 : di_major dc2 = di_major dc1)
        by (rewrite Hdc2; reflexivity).
      assert (Hc2mn0 : di_minor dc2 = di_minor dc1)
        by (rewrite Hdc2; reflexivity).
      assert (Hc2nl0 : di_nlink dc2 = di_nlink dc1)
        by (rewrite Hdc2; reflexivity).
      assert (Hc2ty : di_type dc2 = ty) by (rewrite Hc2ty0; exact Hc1ty).
      assert (Hc2tyd : di_type dc2 = SpecDirlookup.T_DIR)
        by (rewrite Hc2ty; exact Htdir).
      assert (Hc2tynz : bv_unsigned (di_type dc2) <> 0)
        by (rewrite Hc2tyd; vm_compute; discriminate).
      assert (Hc2iok : inode_ok fsc_cov fsc_logst dc2 bm2 dat2).
      { rewrite /inode_ok. split_and!.
        - exact Hwf2.
        - exact Hcov2.
        - exact Haddr2.
        - exact Hc2tynz.
        - exact (Hcap2 (Hcap1 Hccap)).
        - exact Hholes2.
        - exact (Hsizedp2 (Hsizedp1 Hcsized)). }
      assert (Hc2szmax : bv_unsigned (di_size dc2)
                = Z.max (bv_unsigned (di_size dc1))
                    (Z.of_nat ((16 * 1)%nat + tot2)))
        by (rewrite Hdc2;
            exact (cr_wi_size_max _ bm2 (16 * 1)%nat tot2 ltac:(lia))).
      assert (Hc2dok : dir_ok icfg_nib dc2 dat2)
        by exact (dir_ok_dirlink icfg_nib dc1 dc2 dat1 dat2 (cr_low16 dind)
                    (bname 14 cr_dotdot_f) 1%nat 1%nat tot2
                    (eq_sym Hc1nrec) (eq_sym Hc1k0) Htot162 Hdl16b
                    Hc2ty0 Hc2szmax Hrng2 Hc1dok).
      (* ...and UNIQUENESS, whose guard here is the SAME [dir_first] miss
         that refutes the found arm above: record 0 is the ["."]. *)
      assert (Hc2duq : dir_uniq dc2 dat2)
        by exact (dir_uniq_dirlink dc1 dc2 dat1 dat2 (cr_low16 dind)
                    (bname 14 cr_dotdot_f) 1%nat 1%nat tot2
                    (eq_sym Hc1nrec) (eq_sym Hc1k0) Hatom2
                    (bname_length_le 14 cr_dotdot_f) (cut_nul_nonul _)
                    Hc2ty0 Hc2szmax Hrng2
                    (cr_first_miss_dotdot dat1 (cr_low16 cinum) Hwin1)
                    Hc1duq).
      (* the child's four field readings, at the record TWO links left --
         what [cr_fail_mkdir_body] takes and what [cr_cont_body]'s [made]
         arm asks for.  Both the ARM C-OK re-walk and two of the three
         [fail:] entries spend them, so they are stated once, here. *)
      assert (Hc2mj : di_major dc2 = major) by (rewrite Hc2mj0; exact Hc1mj).
      assert (Hc2mn : di_minor dc2 = minor) by (rewrite Hc2mn0; exact Hc1mn).
      assert (Hc2nl : di_nlink dc2 = (mword_of_int 1 : mword 16))
        by (rewrite Hc2nl0; exact Hc1nl).
      assert (Hc2nlz : bv_unsigned (di_nlink dc2) = 1)
        by (rewrite Hc2nl; vm_compute; reflexivity).
      assert (Hc2dokn : dir_ok icfg_nib dc2 dat2)
        by (exact Hc2dok).
      (* ================================================================ *)
      (*  THE ESTABLISHMENT.  [DirView.dir_dots_ix] is minted exactly once  *)
      (*  in this kernel and this is the site: the child's two interior     *)
      (*  links have written record 0 = ["."] at its own inum and record    *)
      (*  1 = [".."] at the PARENT's, and the second writei's size makes    *)
      (*  the count two.  Record 1's LIVENESS is [dp->inum <> 0], which has *)
      (*  no supplier anywhere in the tree -- [IcacheRef.inode_held] keeps  *)
      (*  only the upper bound and namex drops [SpecDirlookup]'s own        *)
      (*  [0 < inum] -- so it comes from the PARENT'S OWN copy of this      *)
      (*  clause, whose ["."] half says the parent's record 0 names the     *)
      (*  parent.  That is what the self half is carried for.               *)
      (*                                                                    *)
      (*  It is GUARDED on [tot2 = 16]: on the short arm the child keeps no  *)
      (*  [".."] and goes to [fail:], where the count is zeroed and the      *)
      (*  clause is vacuous.                                                *)
      (* ================================================================ *)
      assert (Hnl0z : bv_unsigned (di_nlink dn) <> 0).
      { intro Hc. apply Hnl0. apply bv_eq. rewrite Hc. vm_compute. reflexivity. }
      assert (Hdindnz : bv_unsigned dind <> 0)
        by exact (dir_dots_ix_self (bv_unsigned dind) dn data
                    ltac:(rewrite Htydir; vm_compute; reflexivity)
                    Hnl0z Hddix).
      assert (Hc2ddix : (tot2 = 16)%nat ->
                        dir_dots_ix (bv_unsigned cinum) dc2 dat2).
      { intro Ht16.
        assert (Hw02 : dir_win_agree dat1 dat2 0).
        { intros jj Hjj. rewrite (Hrng2 (16 * 0 + jj)%nat).
          rewrite decide_False; [reflexivity |].
          intros [Hlo Hhi]. clear -Hlo Hjj. lia. }
        assert (Hwin2 : forall jj, (jj < 16)%nat ->
                  file_byte dat2 (16 * 1 + jj)%nat
                  = dirent_bytes (de_of_name (cr_low16 dind)
                                    (bname 14 cr_dotdot_f)) !!! jj).
        { intros jj Hjj. rewrite (Hrng2 (16 * 1 + jj)%nat).
          rewrite decide_True; [| clear -Hjj Ht16; lia].
          replace (16 * 1 + jj - 16 * 1)%nat with jj by (clear -jj; lia).
          reflexivity. }
        destruct (cr_dotdot_record dat2 (cr_low16 dind) Hwin2)
          as [Hd2inum Hd2name].
        assert (Hn32 : dir_nrec 32 = 2%nat) by (vm_compute; reflexivity).
        assert (H32 : 32 <= bv_unsigned (di_size dc2))
          by (rewrite Hc2szmax; clear -Ht16; lia).
        pose proof (dir_nrec_mono 32 _ H32) as Hmono.
        intros _ _. split_and!.
        - clear -Hmono Hn32. lia.
        - unfold dir_live. rewrite (dir_inum_agree dat1 dat2 0 Hw02).
          exact Hd1live.
        - rewrite (dir_inum_agree dat1 dat2 0 Hw02) Hd1inum. exact Hcl16.
        - rewrite (dir_bname_agree dat1 dat2 0 Hw02) Hd1name. reflexivity.
        - unfold dir_live. rewrite Hd2inum. intro Hc. apply Hdindnz.
          rewrite <- Hdl16. rewrite Hc. reflexivity.
        - exact Hd2name. }
      (* FAIL ENTRIES 2 AND 3's content clause, and unlike the index clause
         it holds on BOTH arms of the second link -- which is the whole
         point of splitting the content out of the guard.  At [tot2 = 16]
         the child has two records and they ARE the two dots; at
         [tot2 < 16] it has one and it is the ["."].  Neither arm needs
         [dp->inum <> 0], so no parent fact enters here. *)
      assert (Hc2dots : dir_dots_only dc2 dat2).
      { assert (Hw02 : dir_win_agree dat1 dat2 0).
        { intros jj Hjj. rewrite (Hrng2 (16 * 0 + jj)%nat).
          rewrite decide_False; [reflexivity |].
          intros [Hlo Hhi]. clear -Hlo Hjj. lia. }
        assert (Hc1sz16 : bv_unsigned (di_size dc1) = 16)
          by (rewrite Hc1szmax Hcsz0 Ht161; vm_compute; reflexivity).
        assert (Hdot0 : bname 14 (dir_name dat2 0) = dot_name).
        { rewrite (dir_bname_agree dat1 dat2 0 Hw02) Hd1name. reflexivity. }
        destruct Hbl2 as [[_ Ht2] | [_ Ht2]].
        - assert (Hwin2 : forall jj, (jj < 16)%nat ->
                    file_byte dat2 (16 * 1 + jj)%nat
                    = dirent_bytes (de_of_name (cr_low16 dind)
                                      (bname 14 cr_dotdot_f)) !!! jj).
          { intros jj Hjj. rewrite (Hrng2 (16 * 1 + jj)%nat).
            rewrite decide_True; [| clear -Hjj Ht2; lia].
            replace (16 * 1 + jj - 16 * 1)%nat with jj by (clear -jj; lia).
            reflexivity. }
          destruct (cr_dotdot_record dat2 (cr_low16 dind) Hwin2)
            as [_ Hd2name2].
          assert (Hsz32 : bv_unsigned (di_size dc2) = 32)
            by (rewrite Hc2szmax Hc1sz16 Ht2; vm_compute; reflexivity).
          assert (Hn32 : dir_nrec 32 = 2%nat) by (vm_compute; reflexivity).
          intros k Hk _. rewrite Hsz32 Hn32 in Hk.
          destruct k as [| [| k]]; [| | exfalso; clear -Hk; lia].
          + left. exact Hdot0.
          + right. exact Hd2name2.
        - assert (Hnr1 : dir_nrec (bv_unsigned (di_size dc2)) = 1%nat).
          { rewrite Hc2szmax Hc1sz16.
            replace (Z.max 16 (Z.of_nat ((16 * 1)%nat + tot2)))
              with (Z.of_nat tot2 + 1 * 16) by (clear -Ht2; lia).
            unfold dir_nrec. rewrite Z.div_add; [| clear; lia].
            rewrite Z.div_small; [reflexivity | clear -Ht2; lia]. }
          intros k Hk _. rewrite Hnr1 in Hk.
          destruct k as [| k]; [| exfalso; clear -Hk; lia].
          left. exact Hdot0. }
      destruct Hbl2 as [[Ha0z2 Ht162] | [Ha0m2 Htlt2]].
      + (* ============================================================= *)
        (*  the [".."] link went in whole: on to [dirlink(dp, name)]      *)
        (* ============================================================= *)
        (* ===== +0x11e bltz a0 : FALLS THROUGH ======================= *)
        iApply (wp_blt_x0_fall_s_sconf (mword_of_int (CK + 0x11e))
                  (mword_of_int 40 : mword 13) Ra0 md2 (K - 10)%nat b
                  ltac:(nz)
                  ltac:(rgne; rewrite Ha0z2; exact cr_bltz_zero)
                  with "Hcg Hpc []").
        { iApply (cri_11e with "Htext"). }
        iIntros (CIDe7 Hqe7) "Hcg Hpc".
        assert (Hq122 : add_vec_int (mword_of_int (CK + 0x11e) : mword 64) 4
                        = mword_of_int (CK + 0x122)) by pcw.
        iEval (rewrite Hq122) in "Hpc".
        (* THE DEFERRED RE-PARK: slot ONE names the PARENT, whose fragment
           is minted only by the +0x140 flush, so the child's [dlinks] stays
           at [dc1]/[dat1] until then and the range clause travels with it. *)
        (* THE CHILD'S RECORD-ONLY FACTS AFTER ITS OWN TWO LINKS
           (durable-disk 2b-inode-3): the type rode both [dirlink]s, the
           count is still the literal 1, and the size is 32 -- two whole
           records, hence a multiple of sixteen.  Asserted HERE, where
           [tot2 = 16] first holds, because both this arm's exits re-park
           the child at [dc2]. *)
        assert (Hc2rl : inode_rec_local dc2).
        { apply (inode_rec_local_same_type dnc dc2 Hrl_datc).
          - rewrite Hc2ty0 Hc1ty0 cr_setf_type. reflexivity.
          - rewrite Hc2nlz. lia.
          - intros _. rewrite Hc2szmax Hc1szmax Hcsz0 Ht161 Ht162.
            exists 2%Z. vm_compute. reflexivity. }
        assert (Hbmem5 : fsc_bmapstart ∈ Sb5) by exact (Hsb5 _ Hbmem4).
        assert (Hcrb3 : bool_decide (fsc_bmapstart ∈ Sb5) = true)
          by exact (cr_crb_claim Sb5 fsc_bmapstart Hbmem5).
        assert (Hn5lo : (6 <= n5)%nat)
          by exact (cr_mkdir_n5 n3 n4 n5 _ _ _ _ _ Hn3lo Hcorr' Hspend1
                      Hspend2 eq_refl).
        (* ===== +0x122 lw a2,4(s3) : the child's inum ================ *)
        iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x122)) Ra2 Rs3
                  (mword_of_int 4 : mword 12) md2 (K - 10)%nat cinum b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hciinum]").
        { iApply (cri_122 with "Htext"). }
        { iEval (rgne; rewrite (proj1 (proj2 (proj2 (proj2 (proj2 Hmd2regs)))))).
          iExact "Hciinum". }
        iIntros (CIDe8 Hqe8) "Hcg Hpc Hciinum".
        iEval (rgne; rewrite (proj1 (proj2 (proj2 (proj2 (proj2 Hmd2regs))))))
          in "Hciinum".
        pose (W1 := <[Regidx Ra2 := regval_into_reg
                      (sign_extend' 64 cinum : mword 64)]> md2).
        change (<[Regidx Ra2 := regval_into_reg
                      (sign_extend' 64 cinum : mword 64)]> md2) with W1.
        assert (HW1a2 : W1 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
          by (rewrite /W1; apply upd_eq).
        assert (HW1regs : cr_regs3 m sp0 (ientry kd)
                            (mword_of_int 0 : mword 64) (ientry kslot)
                            ty major minor W1)
          by (rewrite /W1; apply cr_regs3_caller; [exact Hcsa2 | exact Hmd2regs]).
        assert (HW1s0 : W1 !!! Regidx Rs0 = sp0)
          by (destruct HW1regs as (_ & H & _); exact H).
        assert (HW1s1 : W1 !!! Regidx Rs1 = ientry kd)
          by (destruct HW1regs as (_ & _ & H & _); exact H).
        assert (Hq126 : add_vec_int (mword_of_int (CK + 0x122) : mword 64) 4
                        = mword_of_int (CK + 0x126)) by pcw.
        iEval (rewrite Hq126) in "Hpc".
        (* ===== +0x126 addi a1,s0,-80 : a1 = &name =================== *)
        iApply (wp_addi4_s_sconf (mword_of_int (CK + 0x126)) Ra1 Rs0
                  (mword_of_int 4016 : mword 12) W1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_126 with "Htext"). }
        iIntros (CIDe9 Hqe9) "Hcg Hpc".
        pose (W2 := <[Regidx Ra1 := regval_into_reg
                      (add_vec (rget W1 Rs0)
                         (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> W1).
        change (<[Regidx Ra1 := regval_into_reg
                      (add_vec (rget W1 Rs0)
                         (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> W1) with W2.
        assert (HW2a1 : W2 !!! Regidx Ra1 = pa_stk sp0 10).
        { rewrite /W2 upd_eq. rewrite rget_ne;
            [| intro Hz1; injection Hz1 as Hz2; vm_compute in Hz2; congruence ].
          rewrite HW1s0. apply cr_name_addr. }
        assert (HW2a2 : W2 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
          by (rewrite /W2 upd_ne; [exact HW1a2 | nz]).
        assert (HW2s1 : W2 !!! Regidx Rs1 = ientry kd)
          by (rewrite /W2 upd_ne; [exact HW1s1 | nz]).
        assert (HW2regs : cr_regs3 m sp0 (ientry kd)
                            (mword_of_int 0 : mword 64) (ientry kslot)
                            ty major minor W2)
          by (rewrite /W2; apply cr_regs3_caller; [exact Hcsa1 | exact HW1regs]).
        assert (Hq12a : add_vec_int (mword_of_int (CK + 0x126) : mword 64) 4
                        = mword_of_int (CK + 0x12a)) by pcw.
        iEval (rewrite Hq12a) in "Hpc".
        (* ===== +0x12a c.mv a0,s1 : the PARENT ======================= *)
        iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x12a)) Ra0 Rs1 W2
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_12a with "Htext"). }
        iIntros (CIDe10 Hqe10) "Hcg Hpc". iEval (rgne) in "Hcg".
        pose (W3 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64)
                         (W2 !!! Regidx Rs1))]> W2).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64)
                         (W2 !!! Regidx Rs1))]> W2) with W3.
        assert (HW3a0 : W3 !!! Regidx Ra0 = ientry kd).
        { rewrite /W3 upd_eq. rewrite HW2s1. apply add_vec_zero_l. }
        assert (HW3a1 : W3 !!! Regidx Ra1 = pa_stk sp0 10)
          by (rewrite /W3 upd_ne; [exact HW2a1 | nz]).
        assert (HW3a2 : W3 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
          by (rewrite /W3 upd_ne; [exact HW2a2 | nz]).
        assert (HW3regs : cr_regs3 m sp0 (ientry kd)
                            (mword_of_int 0 : mword 64) (ientry kslot)
                            ty major minor W3)
          by (rewrite /W3; apply cr_regs3_caller; [exact Hcsa0 | exact HW2regs]).
        assert (Hq12c : add_vec_int (mword_of_int (CK + 0x12a) : mword 64) 2
                        = mword_of_int (CK + 0x12c)) by pcw.
        iEval (rewrite Hq12c) in "Hpc".
        (* ===== +0x12c jal dirlink(dp, name, ip->inum) =============== *)
        assert (Htgd3 : add_vec (mword_of_int (CK + 0x12c) : mword 64)
                  (sign_extend' 64 (mword_of_int 2092292 : mword 21))
                  = mword_of_int KernelSyms.dirlink) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0x12c)) Rra
                  (mword_of_int 2092292 : mword 21) W3 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_12c with "Htext"). }
        iIntros (CIDe11 Hqe11) "Hcg Hpc".
        iEval (rewrite Htgd3) in "Hpc".
        pose (W4 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x12c) : mword 64) 4)]> W3).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x12c) : mword 64) 4)]> W3) with W4.
        assert (HW4ra : W4 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CK + 0x12c) : mword 64) 4)
          by (rewrite /W4; apply upd_eq).
        assert (HW4a0 : W4 !!! Regidx Ra0 = ientry kd)
          by (rewrite /W4 upd_ne; [exact HW3a0 | nz]).
        assert (HW4a1 : W4 !!! Regidx Ra1 = pa_stk sp0 10)
          by (rewrite /W4 upd_ne; [exact HW3a1 | nz]).
        assert (HW4a2 : W4 !!! Regidx Ra2
                        = (zero_extend' 64 (cr_low16 cinum) : mword 64)).
        { rewrite /W4 upd_ne; [| nz]. rewrite HW3a2.
          exact (cr_a2_low16 cinum Hc16). }
        assert (HW4regs : cr_regs3 m sp0 (ientry kd)
                            (mword_of_int 0 : mword 64) (ientry kslot)
                            ty major minor W4)
          by (rewrite /W4; apply cr_regs3_caller; [exact Hcsra | exact HW3regs]).
        iEval (rewrite -HW4a1) in "Hnb14".
        iEval (rewrite /inode_map) in "Hmap".
        iDestruct "Hmap" as "[Haddrs Hind]".
        iAssert (inode_map fsc_fs (ientry kd) bm) with "[Haddrs Hind]" as "Hmap".
        { rewrite /inode_map. iFrame. }
        iDestruct (cpu_own_transport CIDd2 CIDe11 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* the eighth dirlink's own [iput] may need -- see the two dot
           links above; here it comes off the CHILD's arm, because the call
           itself is over the parent. *)
        iDestruct "Hcdep" as (locc tlcc) "(%Hlecc & #Hflcc & Hcdep)".
        iApply fupd_wp.
        iMod (ic_shrink_tx ⊤ fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kslot (q/2)%Qp icfg_dev cinum g _
                true t (1/4) ((1/4)/2) ((1/4)/2) (eq_sym (Qp.div_2 (1/4)))
                ltac:(solve_ndisj) with "Hescc Hcivalid Hcdep")
          as "(Hcivalid & Hcdep & Htxs)".
        iModIntro.
        iApply (DLK.wp_dirlink_gen γs j γl pd pav pu
 γf
                  (ientry kd) dind bm data dn dn nf (cr_low16 cinum)
                  n5 Sb5
                  _ _
                  pidv (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn 1) dqs
                  dqb dqbs (DfracOwn (1/2))
                  W4 (K - 10)%nat eb b lks
                  U ltac:(exact HKdlk) Htydir Hbmcov Hszcap
                  ltac:(exact (Hdok Hdz))
                  (* §7.5.6, row 5 again, on the mkdir arm: LEFT disjunct
                     from the same [sysfile.c:269] guard, relayed into this
                     body as [Hnl0]. *)
                  ltac:(left; exact (cr_nl0z dn Hnl0))
                  ltac:(exact (cr_doc_of_live dn dn data eq_refl Hnl0))
                  ltac:(exact (di_type_stable_refl dn))
                  ltac:(exact (di_nlink_stable_refl dn Htynzd))
                  Hlg Hbmwf Hholes Hdaddr Hsz31 Hist0 Hdblk Hdblog Hdib
                  Hcl16b Hbmgeo Hpkc Hsize Hbms0 Hbmsc Hbmsl Hcovb Hiregb
                  ltac:(rewrite Hcrb3;
                        exact (cr_mkdir_dl3_need n3 n4 n5 _ _ _ _ _ true _
                                 Hn3lo Hcorr' Hspend1 Hspend2 eq_refl eq_refl))
                  Hj Hgs HW4a0 HW4a2 Heb ltac:(lkbelow)
                  with "Hcg Hcnt Htext Hpc Hkd Hpk Hbio Hlogc Hkenv
                        Hidev Hiinum Hmeta Hmap Hblocks Hnb14 Hsbi Hsbs Hsbb
                        Hbmr Hiregi Hiopen Hdiat Hppid Hprocs Hdevi Hgeom Hdlk Hbsl
                        Hitb2 Hitbl Hesc Hslks Hislk Hdlnk Hop Htxs").
        all: try lkbelow.
        iIntros (CIDd3 Hsd3 md3 found3 bm3 dat3 dp3 dp03 n6 Sb6 tot3)
          "%Hcsd3 Hcg Hcnt Hpc Hidev Hiinum Hmeta Hmap Hblocks Hnb14 Hsbi
           Hsbs Hsbb Hdiat Hppid Hbsl Hislk Hdlnk %Hn6c %Hsb6 %Hdlp3 %Hfd3
           Hop Htxs %Hcap3 %Hsizedp3 %Harm3".

        iApply fupd_wp.
        iMod (ic_grow_tx ⊤ fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kslot (q/2)%Qp icfg_dev cinum g _
                true t (1/4) ((1/4)/2) ((1/4)/2) (eq_sym (Qp.div_2 (1/4)))
                ltac:(solve_ndisj) with "Hescc Hcivalid Hcdep Htxs")
          as "(Hcivalid & Hcdep)".
        iModIntro.

        iDestruct (dlinks_open with "Hdlnk")
          as "(%D & [%Hdok0 %Hxact0] & Hetk)".
        iEval (rewrite HW4a1) in "Hnb14".
        assert (Hpcd3 : ret_pc (W4 !!! Regidx Rra : mword 64)
                        = mword_of_int (CK + 0x130)) by (rewrite HW4ra; pcw).
        iEval (rewrite Hpcd3) in "Hpc".
        assert (Hmd3regs : cr_regs3 m sp0 (ientry kd)
                             (mword_of_int 0 : mword 64) (ientry kslot)
                             ty major minor md3)
          by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                      (ientry kslot) ty major minor W4 md3 Hcsd3 HW4regs).
        assert (Htg146c : add_vec (mword_of_int (CK + 0x130) : mword 64)
                  (sign_extend' 64 (mword_of_int 22 : mword 13))
                  = mword_of_int (CK + 0x146)) by pcw.
        destruct found3.
        { exfalso. destruct Harm3 as (Hfst & _). exact (Hfst Hnone). }
        destruct Harm3 as (_ & Hwf3 & Hholes3 & Haddr3 & Hsz313 &
                           Hcov3 & Hdp3 & Hdp03 & Htot163 & Hrng3 & Hbl3).
        destruct (Hdlp3 eq_refl) as (Hspend3 & Hatom3 & Hmem3').
        rewrite Hcrb3 in Hspend3.
        assert (Hdpeq : dp03 = dp3) by exact (Hdp03 eq_refl).
        subst dp03.
        assert (Hp3ty : di_type dp3 = di_type dn) by (rewrite Hdp3; reflexivity).
        assert (Hp3nl : di_nlink dp3 = di_nlink dn)
          by (rewrite Hdp3; reflexivity).
        (* THE SIZE READ-BACK, IN ORIGIN'S [Hoff32] SHAPE.  The chain is
           four small facts and then ONE [lia] with the context CLEARED:
           written inline (a single [lia] over the whole syscall-altitude
           context) this sentence does not terminate -- the parent's [k0] is
           a [dir_slot data (dir_nrec ...)] term rather than a literal, so
           [lia]'s atom scan has to normalise it against every arithmetic
           hypothesis three [dirlink]s have accumulated. *)
        assert (Hk0le : (dir_slot data (dir_nrec (bv_unsigned (di_size dn)))
                         <= dir_nrec (bv_unsigned (di_size dn)))%nat)
          by apply dir_slot_le.
        assert (Hsznn : 0 <= bv_unsigned (di_size dn))
          by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
        destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hsznn)
          as [Hnr1 _].
        assert (Hmb : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)
          by (vm_compute; reflexivity).
        assert (Hnatle : (16 * dir_slot data
                            (dir_nrec (bv_unsigned (di_size dn))) + tot3
                          <= 16 * dir_nrec (bv_unsigned (di_size dn)) + 16)%nat).
        { clear -Hk0le Htot163. lia. }
        assert (HzA : (Z.of_nat (16 * dir_slot data
                          (dir_nrec (bv_unsigned (di_size dn))) + tot3)%nat
                       <= Z.of_nat (16 * dir_nrec
                            (bv_unsigned (di_size dn)) + 16)%nat)%Z)
          by (apply Nat2Z.inj_le; exact Hnatle).
        assert (HzB : Z.of_nat (16 * dir_nrec
                          (bv_unsigned (di_size dn)) + 16)%nat
                      = (Z.of_nat (16 * dir_nrec
                          (bv_unsigned (di_size dn)))%nat + 16)%Z)
          by (rewrite Nat2Z.inj_add; reflexivity).
        assert (Hoff32 : (Z.of_nat (16 * dir_slot data
                            (dir_nrec (bv_unsigned (di_size dn))) + tot3)
                          < 2 ^ 32)%Z).
        { rewrite Hmb in Hszcap. change (2 ^ 32)%Z with 4294967296%Z.
          clear -Hnatle HzA HzB Hszcap Hnr1. lia. }
        assert (Hp3szmax : bv_unsigned (di_size dp3)
                  = Z.max (bv_unsigned (di_size dn))
                      (Z.of_nat (16 * dir_slot data
                         (dir_nrec (bv_unsigned (di_size dn))) + tot3)))
          by (rewrite Hdp3; exact (cr_wi_size_max dn bm3 _ tot3 Hoff32)).
        assert (Hp3iok : inode_ok fsc_cov fsc_logst dp3 bm3 dat3).
        { rewrite /inode_ok. split_and!.
          - exact Hwf3.
          - exact Hcov3.
          - exact Haddr3.
          - rewrite Hp3ty. exact Htynzd.
          - exact (Hcap3 Hszcap).
          - exact Hholes3.
          - exact (Hsizedp3 Hsized). }
        assert (Hp3dok : dir_ok icfg_nib dp3 dat3)
          by exact (dir_ok_dirlink icfg_nib dn dp3 data dat3 (cr_low16 cinum)
                      (bname 14 nf) _ _ tot3 eq_refl eq_refl Htot163
                      Hcl16b Hp3ty Hp3szmax Hrng3 Hdok).
        assert (Hp3duq : dir_uniq dp3 dat3)
          by exact (dir_uniq_dirlink dn dp3 data dat3 (cr_low16 cinum)
                      (bname 14 nf) _ _ tot3 eq_refl eq_refl Hatom3
                      (bname_length_le 14 nf) (cut_nul_nonul _)
                      Hp3ty Hp3szmax Hrng3 Hnone Hduq).
        assert (Hp3szle : bv_unsigned (di_size dn)
                          <= bv_unsigned (di_size dp3))
          by (clear -Hp3szmax; rewrite Hp3szmax; lia).
        assert (Hp3ddix : dir_dots_ix (bv_unsigned dind) dp3 dat3)
          by exact (dir_dots_ix_dirlink (bv_unsigned dind) dn dp3 data dat3
                      (cr_low16 cinum) (bname 14 nf) _ _ tot3 eq_refl eq_refl
                      Htot163 Hp3ty Hp3nl Hp3szle Hrng3 Hddix).
        assert (Hp3setfsz : bv_unsigned (di_size dp3)
                  <= bv_unsigned (di_size (cr_setf dp3 (di_major dp3)
                       (di_minor dp3) (add_vec (di_nlink dp3 : mword 16)
                          (mword_of_int 1 : mword 16)))))
          by (clear; rewrite cr_setf_size; lia).
        assert (Hp3nlnz : bv_unsigned (di_nlink dp3) <> 0).
        { rewrite Hp3nl. intro Hc. apply Hnl0. apply bv_eq. rewrite Hc.
          vm_compute. reflexivity. }
        destruct Hbl3 as [[Ha0z3 Ht163] | [Ha0m3 Htlt3]].
        * (* =========================================================== *)
          (*  ARM C-OK-DIR: the parent's record went in, so the [++] and   *)
          (*  the flush follow and [c.j +0xe0] joins ARM C-OK's block.     *)
          (* =========================================================== *)
          (* THE THREE [tot] READINGS, HOISTED OUT OF ARGUMENT POSITION.  An
             inline [ltac:(lia)] here scans a context three [dirlink]s deep
             and does not terminate (>10 min, 20 GB); with the context
             cleared to the one equation it is instantaneous.  Same rule as
             [Hoff32] above -- durable-notes' "clear - H; lia". *)
          assert (Ht2le3 : (2 <= tot3)%nat) by (clear -Ht163; lia).
          assert (Ht0lt3 : (0 < tot3)%nat) by (clear -Ht163; lia).
          assert (Ht2le2 : (2 <= tot2)%nat) by (clear -Ht162; lia).
          (* ===== +0x130 bltz a0 : FALLS THROUGH ===================== *)
          iApply (wp_blt_x0_fall_s_sconf (mword_of_int (CK + 0x130))
                    (mword_of_int 22 : mword 13) Ra0 md3 (K - 10)%nat b
                    ltac:(nz)
                    ltac:(rgne; rewrite Ha0z3; exact cr_bltz_zero)
                    with "Hcg Hpc []").
          { iApply (cri_130 with "Htext"). }
          iIntros (CIDh1 Hqh1) "Hcg Hpc".
          assert (Hq134 : add_vec_int (mword_of_int (CK + 0x130) : mword 64) 4
                          = mword_of_int (CK + 0x134)) by pcw.
          iEval (rewrite Hq134) in "Hpc".
          (* the child is not the parent: two records held at once are two
             records ([InodeRegion.dinode_at_ne], pure, consumes neither) *)
          iDestruct (InodeRegion.dinode_at_ne fsc_ireg cinum dind _ _
                       with "Hcdiat Hdiat") as %Hcned.
          (* ===== +0x134 lhu a5,74(s1) : dp->nlink =================== *)
          iEval (rewrite /inode_meta) in "Hmeta".
          iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
          iEval (rewrite /i_nlink) in "Hinl".
          iApply (wp_lhu_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x134)) Ra5 Rs1
                    (mword_of_int 74 : mword 12) md3 (K - 10)%nat
                    (di_nlink dp3) b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc [] [Hinl]").
          { iApply (cri_134 with "Htext"). }
          { iEval (rgne; rewrite (proj1 (proj2 (proj2 Hmd3regs)))).
            iExact "Hinl". }
          iIntros (CIDh2 Hqh2) "Hcg Hpc Hinl".
          iEval (rgne; rewrite (proj1 (proj2 (proj2 Hmd3regs)))) in "Hinl".
          pose (V1 := <[Regidx Ra5 := regval_into_reg
                        (zero_extend' 64 (di_nlink dp3 : mword 16) : mword 64)]> md3).
          change (<[Regidx Ra5 := regval_into_reg
                        (zero_extend' 64 (di_nlink dp3 : mword 16) : mword 64)]> md3) with V1.
          assert (HV1a5 : V1 !!! Regidx Ra5
                          = (zero_extend' 64 (di_nlink dp3 : mword 16) : mword 64))
            by (rewrite /V1; apply upd_eq).
          assert (HV1regs : cr_regs3 m sp0 (ientry kd)
                              (mword_of_int 0 : mword 64) (ientry kslot)
                              ty major minor V1)
            by (rewrite /V1; apply cr_regs3_caller;
                [exact Hcsa5 | exact Hmd3regs]).
          assert (Hq138 : add_vec_int (mword_of_int (CK + 0x134) : mword 64) 4
                          = mword_of_int (CK + 0x138)) by pcw.
          iEval (rewrite Hq138) in "Hpc".
          (* ===== +0x138 c.addiw a5,1 =============================== *)
          iApply (wp_caddiw_s_sconf (mword_of_int (CK + 0x138)) Ra5
                    (mword_of_int 1 : mword 6) V1 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (cri_138 with "Htext"). }
          iIntros (CIDh3 Hqh3) "Hcg Hpc".
          pose (V2 := <[Regidx Ra5 := regval_into_reg
                        (sign_extend' 64 (subrange_vec_dec
                           (add_vec (rget V1 Ra5)
                              (sign_extend' 64
                                 (sign_extend' 12 (mword_of_int 1 : mword 6))))
                           31 0))]> V1).
          change (<[Regidx Ra5 := regval_into_reg
                        (sign_extend' 64 (subrange_vec_dec
                           (add_vec (rget V1 Ra5)
                              (sign_extend' 64
                                 (sign_extend' 12 (mword_of_int 1 : mword 6))))
                           31 0))]> V1) with V2.
          assert (HV2regs : cr_regs3 m sp0 (ientry kd)
                              (mword_of_int 0 : mword 64) (ientry kslot)
                              ty major minor V2)
            by (rewrite /V2; apply cr_regs3_caller;
                [exact Hcsa5 | exact HV1regs]).
          assert (HV2s1 : V2 !!! Regidx Rs1 = ientry kd)
            by (destruct HV2regs as (_ & _ & H & _); exact H).
          assert (Hq13a : add_vec_int (mword_of_int (CK + 0x138) : mword 64) 2
                          = mword_of_int (CK + 0x13a)) by pcw.
          iEval (rewrite Hq13a) in "Hpc".
          (* ===== +0x13a sh a5,74(s1) : dp->nlink++ ================== *)
          iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x13a)) Ra5 Rs1
                    (mword_of_int 74 : mword 12) V2 (K - 10)%nat
                    (di_nlink dp3) b with "Hcg Hpc [] [Hinl]").
          { iApply (cri_13a with "Htext"). }
          { iEval (rgne; rewrite HV2s1). iExact "Hinl". }
          iIntros (CIDh4 Hqh4) "Hcg Hpc Hinl".
          iEval (rgne; rgne; rewrite HV2s1 /V2 upd_eq; rgne;
                 rewrite HV1a5 cr_nlink_incr) in "Hinl".
          assert (Hq13e : add_vec_int (mword_of_int (CK + 0x13a) : mword 64) 4
                          = mword_of_int (CK + 0x13e)) by pcw.
          iEval (rewrite Hq13e) in "Hpc".
          iAssert (inode_meta (ientry kd)
                     (cr_setf dp3 (di_major dp3) (di_minor dp3)
                        (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16))))
            with "[Hity Himaj Himin Hinl Hisz]" as "Hmeta".
          { rewrite /inode_meta cr_setf_type cr_setf_major cr_setf_minor
                    cr_setf_nlink cr_setf_size /i_nlink. iFrame. }
          (* THE PARENT'S FRAGMENTS ACROSS THE DEPOSIT AND THE [++], IN
             ONE STEP.  The record at the append slot becomes live and
             MARKED, so the parent's marker set grows by exactly one --
             which is what the raised count on the other side of
             [FsStateInode.node_exact] costs. *)
          (* optimization.md's rule, as everywhere else in this walk: every
             one of the eight side facts is a NAMED assert with the context
             cleared to what it needs, never an inline [ltac:] in argument
             position at this depth. *)
          assert (Hdntdir : bv_unsigned (di_type dn) = T_DIR_z)
            by (clear -Htydir; rewrite Htydir; vm_compute; reflexivity).
          assert (Hdnnlnz : bv_unsigned (di_nlink dn) <> 0)
            by (clear -Hp3nlnz Hp3nl; rewrite <- Hp3nl; exact Hp3nlnz).
          assert (Hcl16nz : cr_low16 cinum <> bv_0 16).
          { assert (Hz0 : bv_unsigned (bv_0 16 : bv 16) = 0)
              by (vm_compute; reflexivity).
            clear -Hcpos Hcl16 Hz0. intro Hc.
            apply (f_equal bv_unsigned) in Hc. rewrite Hcl16 Hz0 in Hc. lia. }
          assert (Hcl16ne : bv_unsigned (cr_low16 cinum) <> bv_unsigned dind)
            by (clear -Hcned Hcl16; rewrite Hcl16; exact Hcned).
          assert (Hbumpty : di_type (cr_setf dp3 (di_major dp3) (di_minor dp3)
                              (add_vec (di_nlink dp3 : mword 16)
                                 (mword_of_int 1 : mword 16))) = di_type dn)
            by (clear -Hp3ty; rewrite cr_setf_type; exact Hp3ty).
          assert (Hbumpsz : bv_unsigned (di_size (cr_setf dp3 (di_major dp3)
                              (di_minor dp3) (add_vec (di_nlink dp3 : mword 16)
                                 (mword_of_int 1 : mword 16))))
                            = Z.max (bv_unsigned (di_size dn))
                                (Z.of_nat (16 * dir_slot data
                                   (dir_nrec (bv_unsigned (di_size dn)))
                                 + tot3)))
            by (clear -Hp3szmax; rewrite cr_setf_size; exact Hp3szmax).
          (* THE FUSED DEPOSIT IS DEFERRED PAST THE FLUSH.  The re-seal's
             exactness equation wants the EXACT [+1], and the only honest
             source of "the [++] did not wrap" is the flush's own nonzero
             read-back -- so the deposit fires three instructions below,
             right after [ireg_tok_nz], with the record and the fragment
             both still in hand.  Nothing in between touches either. *)
          (* ===== +0x13e c.mv a0,s1 ================================= *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x13e)) Ra0 Rs1 V2
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (cri_13e with "Htext"). }
          iIntros (CIDh5 Hqh5) "Hcg Hpc". iEval (rgne) in "Hcg".
          pose (V3 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (V2 !!! Regidx Rs1))]> V2).
          change (<[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (V2 !!! Regidx Rs1))]> V2) with V3.
          assert (HV3a0 : V3 !!! Regidx Ra0 = ientry kd).
          { rewrite /V3 upd_eq. rewrite HV2s1. apply add_vec_zero_l. }
          assert (HV3regs : cr_regs3 m sp0 (ientry kd)
                              (mword_of_int 0 : mword 64) (ientry kslot)
                              ty major minor V3)
            by (rewrite /V3; apply cr_regs3_caller;
                [exact Hcsa0 | exact HV2regs]).
          assert (Hq140 : add_vec_int (mword_of_int (CK + 0x13e) : mword 64) 2
                          = mword_of_int (CK + 0x140)) by pcw.
          iEval (rewrite Hq140) in "Hpc".
          (* ===== +0x140 jal iupdate(dp) : THE SECOND MINT =========== *)
          assert (Htgiu2 : add_vec (mword_of_int (CK + 0x140) : mword 64)
                    (sign_extend' 64 (mword_of_int 2090074 : mword 21))
                    = mword_of_int KernelSyms.iupdate) by pcw.
          iApply (wp_jal_s_sconf (mword_of_int (CK + 0x140)) Rra
                    (mword_of_int 2090074 : mword 21) V3 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_140 with "Htext"). }
          iIntros (CIDh6 Hqh6) "Hcg Hpc".
          iEval (rewrite Htgiu2) in "Hpc".
          pose (V4 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x140) : mword 64) 4)]>
                       V3).
          change (<[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x140) : mword 64) 4)]>
                       V3) with V4.
          assert (HV4ra : V4 !!! Regidx Rra
                          = add_vec_int (mword_of_int (CK + 0x140) : mword 64) 4)
            by (rewrite /V4; apply upd_eq).
          assert (HV4a0 : V4 !!! Regidx Ra0 = ientry kd)
            by (rewrite /V4 upd_ne; [exact HV3a0 | nz]).
          assert (HV4regs : cr_regs3 m sp0 (ientry kd)
                              (mword_of_int 0 : mword 64) (ientry kslot)
                              ty major minor V4)
            by (rewrite /V4; apply cr_regs3_caller;
                [exact Hcsra | exact HV3regs]).
          destruct (cr_mkdir_ip n3 n4 n5 n6 _ _ _ _ _ true _ _ _ _
                      Hn3lo Hcorr' Hspend1 Hspend2 Hspend3 eq_refl eq_refl)
            as [Hipn6 Hn6pos].
          (* the mint's premises, every one NAMED: an inline [ltac:] in
             argument position has to guess its type from an evar
             (durable-notes), and this contract has eight of them. *)
          assert (Hmtcru : true = true -> IBLOCK dind icfg_ist ∈ Sb6)
            by (intros _; exact (proj1 (proj2 (Hmem3' Ht0lt3)))).
          assert (Hmtstab : InodeRegion.di_type_stable
                    (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16)))
                    dp3)
            by (apply di_type_stable_eq; apply cr_setf_type).
          assert (Hmttynz : bv_unsigned (di_type
                    (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16))))
                    <> 0)
            by (rewrite cr_setf_type Hp3ty; exact Htynzd).
          assert (Hmtbump : di_nlink
                    (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16)))
                    = add_vec (di_nlink dp3 : mword 16) (mword_of_int 1))
            by apply cr_setf_nlink.
          assert (Hmtgrd : di_nlink dp3 <> (mword_of_int 32767 : mword 16))
            by (rewrite Hp3nl; exact Hnlmax).
          assert (Hmtaddr : di_addrs
                    (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16)))
                    = bm_cells bm3)
            by (rewrite cr_setf_addrs; exact Haddr3).
          assert (Hmtdirlen : length (bm_dir bm3) = NDIRECT)
            by exact (blkmap_wf_dir_len fsc_cov fsc_logst bm3 Hwf3).
          destruct n6 as [| u6]; [exfalso; lia |].
          iDestruct (cr_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
          iDestruct (cpu_own_transport CIDd3 CIDh6 0%nat eb (proc_addr j) b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          iApply (IU.wp_iupdate_link γs j γl pd pav pu
 (ientry kd) dind
                    (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16)))
                    dp3 bm3 u6 Sb6 true
                    (* pin = false: mkdir's [dp->nlink++] is RULING A's one
                       free site -- a live directory the caller has locked --
                       so it pays the PURE arm (§3.9). *) false
                    (* NO VALUE IS CHOSEN (lane G5): [dp]'s register already
                       stands, and the unit that comes out carries whatever
                       it holds -- which is all the child's [".."] entry
                       needs ([FsStateInode.ent_ty_ok]'s dotdot arm is
                       [True]). *)
                    None
                    pidv
                    (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
                    V4 (K - 10)%nat eb b lks
                    U HKiu Hmtcru
                    Hlg Hist0 Hdblk Hdblog Hdib
                    Hmtstab Hmttynz
                    ltac:(intros vz Hc; discriminate Hc)
                    Hmtbump Hmtgrd
                    Hmtaddr Hmtdirlen
                    Hj Hgs HV4a0 Heb
                    with "Hcg Hcnt Htext Hkd Hpc Hpenv Hbio Hlogc Hidev Hiinum
                          Hmeta Hmap Hsbi Hiregi Hdiat [%] Hppid Hprocs Hdevi
                          Hgeom Hdlk Hbs2 Hop").
          all: try lkbelow.
          { (* the PURE arm, RULING A's one free site: [dp] is the live
               directory create locked at +0x2e, whose [dp->nlink == 0]
               refusal is exactly [Hdpnl0]. *)
            rewrite /InodeRegion.ireg_link_pin. exact Hp3nlnz. }
          iIntros (CIDh7 Hsh7 mmt)
            "%Hcsmt Hcg Hcnt Hpc Hppid Hidev Hiinum Hmeta Hmap Hsbi Hdiat
             (%vend & [%Hvokend _] & Htokend) Hpin Hbs2 Hop".
          (* [dp] is a LIVE directory, so its multiplicity rises by one *)
          iEval (rewrite (InodeRegion.ireg_dot_delta_live _ _ Hp3nlnz)
                         FsStateLink.link_reps_1) in "Htokend".
          (* THE COUNT'S LOWER BOUND AT THE BUMPED RECORD, and it has to be
             taken HERE: the [link_tok] the flush just minted is the only
             witness, and three lines below it is spent into the child's
             [".."] entry.  It is what the complement dot clause needs at
             the re-park -- the [++] is the one create site where
             [dir_orphan_clean] is not free, because [nlink + 1 = 0] is a
             wrap the NLINK_MAX guard (a SIGNED test) does not exclude and
             no pure fact in this walk rules out.
             [IregLinkNz.ireg_tok_nz] is mask-preserving and hands
             everything back. *)
          iApply fupd_wp.
          iMod (ireg_tok_nz ⊤ fsc_ireg fsc_fs icfg_ist icfg_nib dind
                  (cr_setf dp3 (di_major dp3) (di_minor dp3)
                     (add_vec (di_nlink dp3 : mword 16)
                        (mword_of_int 1 : mword 16)))
                  vend ltac:(solve_ndisj) Hdib
                  with "Hiregi Hdiat Htokend")
            as "([%Hmtnz _] & Hdiat & Htokend)".
          iModIntro.
          (* THE FUSED DEPOSIT, DEFERRED TO HERE (see the note at +0x13a):
             the read-back [Hmtnz] is what turns the machine's [++] into
             the EXACT [+1] the lower clause needs. *)
          assert (Hbumpeq : bv_unsigned (di_nlink (cr_setf dp3 (di_major dp3)
                              (di_minor dp3) (add_vec (di_nlink dp3 : mword 16)
                                 (mword_of_int 1 : mword 16))))
                            = bv_unsigned (di_nlink dn) + 1).
          { rewrite cr_setf_nlink. rewrite <- Hp3nl.
            apply nlink_add1_nz_eq.
            rewrite cr_setf_nlink in Hmtnz. exact Hmtnz. }
          (* ============ THE MARKER SET AND THE ["."] RE-PIN ==========
             Everything the two [dirlink]s below owe the type register, in
             the ONE place where the walk still holds BOTH units the fill
             minted (durable-disk G5).  [Htoken] is the second one -- the
             first went into the child's ["."] entry at +0x10a -- and it is
             what values the ["."] fragment by the register's own
             agreement, which is what re-pins that fragment's clause when
             [dirlink(ip, "..", dp)] moves the child's [".."] target. *)
          assert (Htdirm : ty = SpecDirlookup.T_DIR).
          { apply bv_eq. rewrite -Hc1ty Hc1tyd. reflexivity. }
          destruct (dir_dots_miss_not_dots (bv_unsigned dind) dn data
                      (bname 14 nf) Hdntdir Hdnnlnz Hddix Hnone)
            as [Hnfd1m Hnfd2m].
          assert (Hnfd'm : bname 14 nf <> DOT)
            by (rewrite FsStateEra.DOT_dot; exact Hnfd1m).
          assert (Hnfdd'm : bname 14 nf <> DOTDOT)
            by (rewrite FsStateEra.DOTDOT_dotdot; exact Hnfd2m).
          assert (HsDm : bname 14 nf ∉ D).
          { intros Hin. destruct (Hdok0 _ Hin) as ([tt Htt] & _ & _).
            rewrite (dir_entries_era_node dn bm data Hholes Hszcap)
              (bool_decide_eq_true_2 _ Hdntdir)
              (proj2 (dir_view_lookup_None data _ (bname 14 nf)) Hnone)
              in Htt. discriminate. }
          (* the child's marker set is EMPTY: its count is exact and one *)
          assert (Hc1fn1 : fn_nlink (era_node dc1 bm1 dat1) = 1%nat)
            by (rewrite /fn_nlink era_node_rec Hc1nl; vm_compute; reflexivity).
          assert (Hc1dz : bv_unsigned (di_type dc1) = T_DIR_z)
            by (rewrite Hc1tyd; vm_compute; reflexivity).
          assert (Horph1 : fn_orphan (era_node dc1 bm1 dat1) = false)
            by (rewrite /fn_orphan Hc1fn1
                  (bool_decide_eq_false_2 (1%nat = 0%nat)
           ltac:(intros Hcz; discriminate Hcz)) //).
          assert (HDc1 : Dc1 = ∅).
          { pose proof (Hcxact1 ltac:(rewrite /fn_is_dir /fn_type era_node_rec;
                                      apply bool_decide_eq_true;
                                      exact Hc1dz)) as Hex.
            rewrite Hc1fn1 Horph1 in Hex.
            apply leibniz_equiv, size_empty_inv. clear -Hex. lia. }
          assert (Hdot1 : dir_entries (era_node dc1 bm1 dat1) !! DOT
                          = Some (bv_unsigned cinum)).
          { rewrite (dir_entries_era_node dc1 bm1 dat1 Hholes1 (Hcap1 Hccap))
              (bool_decide_eq_true_2 _ Hc1dz) Hc1nrec -Hcl16 -Hd1inum.
            replace DOT with (dir_bname dat1 0%nat)
              by (rewrite /dir_bname Hd1name DOT_dot_name; reflexivity).
            exact (dir_view_live dat1 1%nat 0%nat
                     ltac:(rewrite -Hc1nrec; exact (Hc1duq Hc1dz))
                     ltac:(clear; apply Nat.lt_0_succ) Hd1live). }
          iDestruct (FsStateInode.ent_toks_dot_take (fs_gamma_L fsc_fs)
                       (bv_unsigned cinum) (era_node dc1 bm1 dat1) Dc1
                       Hdot1 Horph1 with "Hcetk2")
            as "[(%vdot0 & Hdot0) Hcnodot]".
          iApply fupd_wp.
          iMod (IregLinkNz.ireg_toks_agree ⊤ fsc_ireg fsc_fs icfg_ist icfg_nib cinum _
                  vdot0 (cr_ity ty (bv_unsigned dind))
                  ltac:(solve_ndisj) Hcinb
                  with "Hiregi Hcdiat Hdot0 Htoken")
            as "([%Hvdot0 _] & Hcdiat & Hdot0 & Htoken)".
          iModIntro.
          (* THE PARENT'S RE-PARK, in TWO steps (durable-disk
             2b-inode-5): the append files the child's unit at the name the
             record now carries, and the [++] moves only the count, which
             the entry map does not read. *)
          iDestruct (ent_toks_dirlink_arm (fs_gamma_L fsc_fs) (bv_unsigned dind)
                       dn dp3 bm bm3 data dat3
                       (cr_low16 cinum) (bname 14 nf)
                       (dir_nrec (bv_unsigned (di_size dn)))
                       (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                       tot3 D true eq_refl eq_refl Hatom3
                       (bname_length_le 14 nf) (cut_nul_nonul _)
                       Hdntdir Hp3ty Hp3nl Hp3szmax Hrng3 Hnone
                       Hholes Hholes3 Hszcap (Hcap3 Hszcap) HsDm Hnfdd'm
                       with "Hetk [Htoken]") as "Hetk".
          { iEval (rewrite -Hcl16) in "Htoken".
            iApply (ent_tok_of_link (fs_gamma_L fsc_fs) (bv_unsigned dind)
                      (FsStateInode.fn_dd (era_node dn bm data))
                      (fn_orphan (era_node dn bm data)) true (bname 14 nf)
                      (bv_unsigned (cr_low16 cinum))
                      (cr_ity ty (bv_unsigned dind))
                      ltac:(apply FsStateInode.ent_ty_ok_name;
                            [exact Hnfd'm | exact Hnfdd'm |
                             exact (cr_ity_dir ty (bv_unsigned dind) Htdirm)])
                      with "Htoken"). }
          iDestruct (ent_toks_era_nlink (fs_gamma_L fsc_fs) (bv_unsigned dind)
                       dp3 (cr_setf dp3 (di_major dp3) (di_minor dp3)
                          (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16))) bm3 dat3
                       ({[bname 14 nf]} ∪ D)
                       (cr_setf_type dp3 _ _ _) (cr_setf_size dp3 _ _ _)
                       ltac:(rewrite Hp3nl; exact Hdnnlnz)
                       ltac:(rewrite cr_setf_nlink;
                             rewrite cr_setf_nlink in Hmtnz; exact Hmtnz)
                       with "Hetk") as "Hetk".
          (* THE COUNT AND THE MARKER SET RISE TOGETHER (G5's (D2), the
             write half): the appended name IS a subdirectory's, and the
             [++] two instructions back is what pays for it. *)
          assert (Hins3 := dir_entries_dirlink_ins dn dp3 bm bm3 data dat3
                     (cr_low16 cinum) (bname 14 nf)
                     (dir_nrec (bv_unsigned (di_size dn)))
                     (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                     eq_refl eq_refl
                     (bname_length_le 14 nf) (cut_nul_nonul _) Hcl16nz
                     Hdntdir Hp3ty ltac:(rewrite Hp3szmax Ht163; reflexivity)
                     ltac:(rewrite Ht163 in Hrng3; exact Hrng3) Hnone
                     Hholes Hholes3 Hszcap (Hcap3 Hszcap)).
          assert (Hgrow3 := dir_entries_dirlink_grow dn dp3 bm bm3 data dat3
                     (cr_low16 cinum) (bname 14 nf)
                     (dir_nrec (bv_unsigned (di_size dn)))
                     (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                     tot3 eq_refl eq_refl Hatom3
                     (bname_length_le 14 nf) (cut_nul_nonul _)
                     Hdntdir Hp3ty Hp3szmax Hrng3 Hnone
                     Hholes Hholes3 Hszcap (Hcap3 Hszcap)).
          assert (Hbumpdok : FsStateInode.ent_dset_ok
                    (era_node (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16)
                          (mword_of_int 1 : mword 16))) bm3 dat3) ({[bname 14 nf]} ∪ D)).
          { intros tz Htz.
            assert (Hents3 : dir_entries (era_node (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16)
                          (mword_of_int 1 : mword 16))) bm3 dat3)
                             = dir_entries (era_node dp3 bm3 dat3))
              by (rewrite /dir_entries /fn_is_dir /fn_type /fn_nrec /fn_size
                    /fn_data !era_node_rec cr_setf_type cr_setf_size //).
            rewrite Hents3.
            destruct (decide (tz = bname 14 nf)) as [-> | Hne].
            - split_and!; [| exact Hnfd'm | exact Hnfdd'm].
              rewrite Hins3 lookup_insert. by eexists.
            - destruct (Hdok0 tz ltac:(destruct (proj1 (elem_of_union _ _ _) Htz)
                                        as [Hc | Hc];
                                      [exfalso; apply Hne;
                                       exact (proj1 (elem_of_singleton _ _) Hc)
                                      | exact Hc]))
                as (Hsome & Hd & Hdd).
              split_and!; [exact (Hgrow3 tz Hsome) | exact Hd | exact Hdd]. }
          assert (Hbumpxact : FsStateInode.node_exact
                    (era_node (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16)
                          (mword_of_int 1 : mword 16))) bm3 dat3) ({[bname 14 nf]} ∪ D)).
          { apply (FsStateInode.node_exact_bump (era_node dn bm data)
                     (era_node (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16)
                          (mword_of_int 1 : mword 16))) bm3 dat3) D (bname 14 nf)).
            - rewrite /fn_is_dir /fn_type !era_node_rec cr_setf_type Hp3ty //.
            - rewrite /fn_nlink !era_node_rec Hbumpeq.
              pose proof (proj1 (bv_unsigned_in_range _ (di_nlink dn))) as Hb0.
              clear -Hb0. lia.
            - rewrite /fn_nlink era_node_rec. intros Hc. apply Hdnnlnz.
              pose proof (proj1 (bv_unsigned_in_range _ (di_nlink dn))) as Hb0.
              clear -Hb0 Hc. lia.
            - exact HsDm.
            - exact Hxact0. }
          iDestruct (dlinks_intro _ _ _ _ _ ({[bname 14 nf]} ∪ D)
                       Hbumpdok Hbumpxact with "Hetk") as "Hdlnk".
          assert (Hpcmt : ret_pc (V4 !!! Regidx Rra : mword 64)
                          = mword_of_int (CK + 0x144)) by (rewrite HV4ra; pcw).
          iEval (rewrite Hpcmt) in "Hpc".
          assert (Hmmtregs : cr_regs3 m sp0 (ientry kd)
                               (mword_of_int 0 : mword 64) (ientry kslot)
                               ty major minor mmt)
            by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor V4 mmt Hcsmt HV4regs).
          iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
            [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
          (* THE CHILD'S DEFERRED RE-PARK COMPLETES: the unit the
             [dp->nlink++] minted goes into the child's [".."] entry
             (durable-disk 2b-inode-5).  The [".."] side condition of
             [ent_tok_of_link] is the child's own [nlink = 1]. *)
          (* THE ["."] FRAGMENT IS RE-PINNED HERE (durable-disk G5): this
             is the write that moves the child's [".."] target off [None],
             so it is the one write in the kernel whose ["."] clause has to
             be re-established.  The value comes from the agreement taken
             above, against the sibling unit the fill minted. *)
          assert (Hdlne1 : bv_unsigned (cr_low16 dind) <> bv_unsigned cinum)
            by (rewrite Hdl16; intros Hc; apply Hcl16ne;
                rewrite Hcl16; exact (eq_sym Hc)).
          assert (Hdl16nz : cr_low16 dind <> bv_0 16).
          { intros Hc. assert (Hz : bv_unsigned (cr_low16 dind) = 0)
              by (rewrite Hc; vm_compute; reflexivity).
            rewrite Hdl16 in Hz. exact (Hdindnz Hz). }
          assert (Hddname : bname 14 cr_dotdot_f = DOTDOT)
            by (rewrite ProofCreateParts.cr_dotdot_name DOTDOT_dotdot;
                reflexivity).
          iDestruct (ent_toks_dirlink_dotdot (fs_gamma_L fsc_fs)
                       (bv_unsigned cinum) dc1 dc2 bm1 bm2 dat1 dat2
                       (cr_low16 dind) 1%nat 1%nat Dc1 vdot0 vend
                       (eq_sym Hc1nrec) (eq_sym Hc1k0) Hdl16nz
                       ltac:(rewrite Hc1ty Htdirm; vm_compute; reflexivity)
                       Hc2ty0 Hc2nl0
                       ltac:(rewrite Hc2szmax Ht162; reflexivity)
                       ltac:(rewrite -Hddname;
                             rewrite Ht162 in Hrng2; exact Hrng2)
                       ltac:(rewrite -Hddname;
                             exact (cr_first_miss_dotdot dat1
                                      (cr_low16 cinum) Hwin1))
                       Hholes1 Hholes2 (Hcap1 Hccap) (Hcap2 (Hcap1 Hccap))
                       ltac:(rewrite HDc1; apply not_elem_of_empty)
                       Hdlne1 Hdot1 Horph1
                       ltac:(rewrite Hvdot0
                                     (cr_ity_dir ty (bv_unsigned dind) Htdirm)
                                     Hdl16; reflexivity)
                       with "Hcnodot Hdot0 [Htokend]") as "Hcetk3".
          { iEval (rewrite -Hdl16) in "Htokend". iExact "Htokend". }
          assert (Hc2dokE : FsStateInode.ent_dset_ok
                             (era_node dc2 bm2 dat2) Dc1)
            by (rewrite HDc1; intros tz Htz;
                exfalso; exact (not_elem_of_empty tz Htz)).
          assert (Hc2xactE : FsStateInode.node_exact
                              (era_node dc2 bm2 dat2) Dc1).
          { intros _.
            assert (Hfn : fn_nlink (era_node dc2 bm2 dat2) = 1%nat)
              by (rewrite /fn_nlink era_node_rec Hc2nl;
                  vm_compute; reflexivity).
            rewrite Hfn /fn_orphan Hfn
              (bool_decide_eq_false_2 (1%nat = 0%nat)
           ltac:(intros Hcz; discriminate Hcz)) HDc1
              size_empty //. }
          iDestruct (dlinks_intro _ _ _ _ _ Dc1 Hc2dokE Hc2xactE
                       with "Hcetk3") as "Hcdlnk2".
          (* ===== +0x144 c.j +0xe0 : into ARM C-OK's own block ======= *)
          assert (Htg0e0 : add_vec (mword_of_int (CK + 0x144) : mword 64)
                    (sign_extend' 64 (sign_extend' 21
                       (concat_vec (mword_of_int 1998 : mword 11) ('b"0"))))
                    = mword_of_int (CK + 0xe0)) by pcw.
          iApply (wp_cj_s_sconf (mword_of_int (CK + 0x144))
                    (sign_extend' 21
                       (concat_vec (mword_of_int 1998 : mword 11) ('b"0")))
                    mmt (K - 10)%nat b
                    ltac:(rewrite Htg0e0; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_144 with "Htext"). }
          iIntros (CIDh8 Hqh8). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htg0e0) in "Hpc".
          (* ============================================================ *)
          (*  ARM C-OK, RE-WALKED (+0xe0..+0xea).  The join is BELOW      *)
          (*  [cr_alloc_half]'s branch, so there is nothing to share and   *)
          (*  these five instructions are proved again -- here against a   *)
          (*  parent at its BUMPED [nlink] and a child at the record its   *)
          (*  two interior links left.                                     *)
          (* ============================================================ *)
          assert (Hp3dokn : dir_ok icfg_nib dp3 dat3)
            by (exact Hp3dok).
          (* THE MOVER (namei-pinned-lookup.md §9 W3, dirlink's row): the
             parent's bytes moved, so its hold moves with them.  One free
             own-update; no delta is proved. *)
          iApply fupd_wp.
          iModIntro.
          assert (Hpfty : di_type (cr_setf dp3 (di_major dp3) (di_minor dp3)
                            (add_vec (di_nlink dp3 : mword 16)
                               (mword_of_int 1 : mword 16)))
                          = di_type dn)
            by (rewrite cr_setf_type; exact Hp3ty).
          iAssert (ity_shot gd (di_type (cr_setf dp3 (di_major dp3)
                     (di_minor dp3) (add_vec (di_nlink dp3 : mword 16)
                        (mword_of_int 1 : mword 16))))) as "#Hshotf".
          { rewrite Hpfty. iExact "Hshotl". }
          (* THE STRUCTURAL CONSTRUCTOR, not [iFrame]: [ic_loaded]'s tail is
             a 268-element big-op and [iFrame] re-searches it quadratically.
             Both [Hdiat] and [Hmeta] come back from the flush ALREADY at the
             bumped record, so unlike the file arm's site there is no
             trailing rewrite and [ic_mk_loaded] applies outright. *)
          iEval (rewrite /inode_map) in "Hmap".
          iDestruct "Hmap" as "[Hpaddrs Hpind]".
          (* ...and the ERA's abstract value at the bumped parent: mkdir's
             append moved the record AND the bytes, and [ireg_top_retag]
             opens [ftopN] alone (durable-disk 2b-inode-3). *)
          (* THE RECORD-ONLY FACTS AT THE BUMPED PARENT (durable-disk
             2b-inode-3): the type rides [cr_setf], the [++] is short by
             the walk's own [<> 32767] guard, and the size is a MAX of two
             multiples of sixteen.  They come BEFORE the retag now, because
             the retag owes the registry's row (durable-disk lane A). *)
          assert (Hbumprl : inode_rec_local
                    (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16)
                          (mword_of_int 1 : mword 16)))).
          { apply (inode_rec_local_same_type dn _ Hrl Hbumpty).
            - rewrite Hbumpeq. apply cr_nl_bump_short.
              + exact (proj1 (proj2 Hrl)).
              + exact (cr_nl_ne_32767 (di_nlink dn) Hnlmax).
            - intros _. rewrite Hbumpsz. apply cr_max_div16.
              + apply (proj2 (proj2 Hrl)). exact Hdntdir.
              + exists (Z.of_nat (dir_slot data
                          (dir_nrec (bv_unsigned (di_size dn)))) + 1)%Z.
                rewrite Ht163 Nat2Z.inj_add Nat2Z.inj_mul. lia. }
          (* ...and the ERA's abstract value at the bumped parent: mkdir's
             append moved the record AND the bytes, and [ireg_top_retag]
             opens [ftopN] alone (durable-disk 2b-inode-3).  A raised link
             count and an appended entry leave the parent well-formed, which
             is the row the retag owes (durable-disk lane A) -- and these are
             [ic_mk_loaded]'s own four facts, one line below. *)
          iApply fupd_wp.
          iMod (ireg_top_retag ⊤ fsc_fs (bv_unsigned dind)
                  (era_node dn bm data)
                  (era_node (cr_setf dp3 (di_major dp3) (di_minor dp3)
                               (add_vec (di_nlink dp3 : mword 16)
                                  (mword_of_int 1 : mword 16))) bm3 dat3)
                  ltac:(solve_ndisj)
                  (inode_local_of_ok_rec (bv_unsigned dind) fsc_cov fsc_logst _
                     bm3 dat3
                     (cr_setf_inode_ok fsc_cov fsc_logst dp3 bm3 dat3
                        (di_major dp3) (di_minor dp3) _ Hp3iok)
                     Hbumprl
                     (dir_uniq_cong dp3 _ dat3 (cr_setf_type _ _ _ _)
                        (cr_setf_size _ _ _ _) Hp3duq)
                     (dir_dots_ix_eq (bv_unsigned dind) dp3 _ dat3 dat3
                        (cr_setf_type _ _ _ _)
                        (fun _ => Hp3nlnz)
                        Hp3setfsz eq_refl Hp3ddix))
                  with "[] Htop") as "Htop";
            [iApply (ireg_inv_ftop with "Hiregi") |].
          iModIntro.
          iDestruct (ic_mk_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kd dind
                       (cr_setf dp3 (di_major dp3) (di_minor dp3)
                          (add_vec (di_nlink dp3 : mword 16)
                             (mword_of_int 1 : mword 16))) bm3 dat3
                       (cr_setf_inode_ok fsc_cov fsc_logst dp3 bm3 dat3
                          (di_major dp3) (di_minor dp3) _ Hp3iok)
                       Hbumprl
                       (cr_setf_dir_ok icfg_nib dp3 dat3 (di_major dp3)
                          (di_minor dp3) _ Hp3dokn)
                       (dir_dots_ix_eq (bv_unsigned dind) dp3 _ dat3 dat3
                          (cr_setf_type _ _ _ _)
                          (fun _ => Hp3nlnz)
                          Hp3setfsz eq_refl Hp3ddix)
                       (dir_orphan_clean_live _ dat3 Hmtnz)
                       (dir_uniq_cong dp3 _ dat3 (cr_setf_type _ _ _ _)
                          (cr_setf_size _ _ _ _) Hp3duq)
                       with "Hdlnk Hdiat Hmeta Hpaddrs Hpind Hblocks Htop")
            as "Hload".
          (* ===== +0xe0 c.mv a0,s1 ==================================== *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xe0)) Ra0 Rs1 mmt
                    (K - 10)%nat b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (cri_0e0 with "Htext"). }
          iIntros (CIDT1 HqT1) "Hcg Hpc". iEval (rgne) in "Hcg".
          pose (T1 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mmt !!! Regidx Rs1))]> mmt).
          change (<[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mmt !!! Regidx Rs1))]> mmt) with T1.
          assert (HT1a0 : T1 !!! Regidx Ra0 = ientry kd).
          { rewrite /T1 upd_eq.
            destruct Hmmtregs as (_ & _ & Hd9 & _). rewrite Hd9.
            apply add_vec_zero_l. }
          assert (HT1regs : cr_regs3 m sp0 (ientry kd)
                    (mword_of_int 0 : mword 64) (ientry kslot)
                    ty major minor T1)
            by (rewrite /T1; apply cr_regs3_caller;
                [exact Hcsa0 | exact Hmmtregs]).
          assert (Hq0e2 : add_vec_int (mword_of_int (CK + 0xe0) : mword 64) 2
                          = mword_of_int (CK + 0xe2)) by pcw.
          iEval (rewrite Hq0e2) in "Hpc".
          (* ===== +0xe2 jal iunlockput(dp) ============================= *)
          assert (Htgu2 : add_vec (mword_of_int (CK + 0xe2) : mword 64)
                    (sign_extend' 64 (mword_of_int 2090944 : mword 21))
                    = mword_of_int KernelSyms.iunlockput) by pcw.
          iApply (wp_jal_s_sconf (mword_of_int (CK + 0xe2)) Rra
                    (mword_of_int 2090944 : mword 21) T1 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_0e2 with "Htext"). }
          iIntros (CIDT2 HqT2) "Hcg Hpc".
          iEval (rewrite Htgu2) in "Hpc".
          pose (T2 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0xe2) : mword 64) 4)]>
                       T1).
          change (<[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0xe2) : mword 64) 4)]>
                       T1) with T2.
          assert (HT2ra : T2 !!! Regidx Rra
                          = add_vec_int (mword_of_int (CK + 0xe2) : mword 64) 4)
            by (rewrite /T2; apply upd_eq).
          assert (HT2a0 : T2 !!! Regidx Ra0 = ientry kd)
            by (rewrite /T2 upd_ne; [exact HT1a0 | nz]).
          assert (HT2regs : cr_regs3 m sp0 (ientry kd)
                    (mword_of_int 0 : mword 64) (ientry kslot)
                    ty major minor T2)
            by (rewrite /T2; apply cr_regs3_caller;
                [exact Hcsra | exact HT1regs]).
          (* BOTH CREDITS ARE IN HAND HERE, which is why this arm's
             [iunlockput(dp)] is FREE: the +0x140 flush unioned [IBLOCK dp]
             in itself, and [bmapstart] has been in the set since the first
             interior [dirlink] allocated the child's block 0.  [crb] pins
             the report [w = false] and [cru] kills the remaining unit, so
             the put spends nothing and [cr_budget_mkdir]'s ZERO-SLACK three
             survives it -- which is the floor create's [ok = true] post
             now owes, at the arm that has the least of it. *)
          assert (Hbm6 : fsc_bmapstart ∈ Sb6) by exact (Hsb6 _ Hbmem5).
          assert (Hcrbu : true = true
                    -> fsc_bmapstart ∈ (Sb6 ∪ {[IBLOCK dind icfg_ist]}))
            by (intros _;
                exact (cr_sub_union_sing Sb6 (IBLOCK dind icfg_ist)
                         fsc_bmapstart Hbm6)).
          assert (Hcruu : true = true
                    -> IBLOCK dind icfg_ist
                       ∈ (Sb6 ∪ {[IBLOCK dind icfg_ist]}))
            by (intros _; exact (cr_in_union_sing Sb6 (IBLOCK dind icfg_ist))).
          iDestruct (cpu_own_transport CIDh7 CIDT2 0%nat eb (proc_addr j) b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
             goes in and the share it parked comes back in the post, so no
             bundleless out-state stands across the call. *)
          iDestruct (log_opS_named with "Hop") as (e0) "Hop".
          iDestruct (inode_ref_short_gen_forget _ _ _ _ _ _ _ _ Hled
                     with "Hfld Hkeep") as "Hkeep2".
          iDestruct (off_rows_to_dep with "Hoffr") as "Hoffd".
          iApply (IUP.wp_iunlockput_dep_gen γs j γl pd pav pu
                    γil γisl
 kd (qd/2)%Qp (qd/2)%Qp gd lodc tldc (DepTx (qd/2)%Qp icfg_dev dind gd lodc t (1/4)%Qp) dind
                    (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16)))
                    bm3 (S u6) (Sb6 ∪ {[IBLOCK dind icfg_ist]})
                    true true false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
                    T2 (K - 10)%nat eb b lks
                    U ltac:(exact HKiup) eq_refl Hkdlt Hcrbu Hcruu
                    Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib Hcovb
                    ltac:(exact Hipn6) Hj Hgs HT2a0 ltac:(lkbelow) eq_refl
                    with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2
                          Hitbl Hescd Hiregi Hiopen Hslkd Hslkdd [//] Hfldc Hclaimscr Hdep Hoffd Hidev
                          Hiinum Hivalid Hload Hshotf Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr
                          Hppid Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
          all: try lkbelow.
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { iEval (cbn beta iota). iEmpIntro. }
          iIntros (CIDT3 HqT3 mu2 n7 Sb7 wf7)
            "%Hcsu2 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
             %Hsb7 %Hwf7 %Hwf7c %Hn7 Hop Hisl2 Htq2".
          assert (Hpcu2 : ret_pc (T2 !!! Regidx Rra : mword 64)
                          = mword_of_int (CK + 0xe6)) by (rewrite HT2ra; pcw).
          iEval (rewrite Hpcu2) in "Hpc".
          assert (Hmu2regs : cr_regs3 m sp0 (ientry kd)
                    (mword_of_int 0 : mword 64) (ientry kslot)
                    ty major minor mu2)
            by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor T2 mu2 Hcsu2 HT2regs).
          iDestruct ("Hppback" with "Hppid") as "Hpriv".
          (* ===== +0xe6 c.mv s2,s3 : the ANSWER ======================== *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xe6)) Rs2 Rs3 mu2
                    (K - 10)%nat b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (cri_0e6 with "Htext"). }
          iIntros (CIDT4 HqT4) "Hcg Hpc". iEval (rgne) in "Hcg".
          assert (Ht3v : add_vec (zero_reg : mword 64) (mu2 !!! Regidx Rs3)
                         = ientry kslot).
          { destruct Hmu2regs as (_ & _ & _ & _ & Hd19 & _). rewrite Hd19.
            apply add_vec_zero_l. }
          pose (T3 := <[Regidx Rs2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mu2 !!! Regidx Rs3))]> mu2).
          change (<[Regidx Rs2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mu2 !!! Regidx Rs3))]> mu2) with T3.
          assert (HT3s2 : T3 !!! Regidx Rs2 = ientry kslot)
            by (rewrite /T3 upd_eq; exact Ht3v).
          assert (HT3regs : cr_regs3 m sp0 (ientry kd) (ientry kslot)
                    (ientry kslot) ty major minor T3)
            by exact (cr_regs3_s2 m sp0 (ientry kd)
                        (mword_of_int 0 : mword 64) (ientry kslot)
                        (ientry kslot) ty major minor mu2 _ Ht3v Hmu2regs).
          assert (Hq0e8 : add_vec_int (mword_of_int (CK + 0xe6) : mword 64) 2
                          = mword_of_int (CK + 0xe8)) by pcw.
          iEval (rewrite Hq0e8) in "Hpc".
          (* ===== +0xe8 c.ldsp s3,40(sp) : the LAZY RESTORE ============ *)
          assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 10)
            by (destruct HT3regs as (H2 & _); exact H2).
          assert (HT5 : add_vec (T3 !!! Regidx csp_rs1)
                          (zero_extend' 64
                             (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                        = pa_stk sp0 5) by (rewrite HT3sp; apply cr_frm5).
          iEval (rewrite -HT5) in "Hb5".
          iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0xe8))
                    (mword_of_int 5 : mword 6) Rs3 T3 (K - 10)%nat
                    (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc [] Hb5").
          { iApply (cri_0e8 with "Htext"). }
          iIntros (CIDT5 HqT5) "Hcg Hpc Hb5".
          iEval (rewrite HT5) in "Hb5".
          pose (T4 := <[Regidx Rs3 := regval_into_reg
                        (m !!! Regidx Rs3 : mword 64)]> T3).
          change (<[Regidx Rs3 := regval_into_reg
                        (m !!! Regidx Rs3 : mword 64)]> T3) with T4.
          assert (HT4regs : cr_regs3 m sp0 (ientry kd) (ientry kslot)
                    (m !!! Regidx Rs3 : mword 64) ty major minor T4)
            by exact (cr_regs3_s3 m sp0 (ientry kd) (ientry kslot)
                        (ientry kslot) (m !!! Regidx Rs3 : mword 64)
                        ty major minor T3 _ eq_refl HT3regs).
          assert (HT4s2 : T4 !!! Regidx Rs2 = ientry kslot)
            by (rewrite /T4 upd_ne; [exact HT3s2 | nz]).
          assert (Hq0ea : add_vec_int (mword_of_int (CK + 0xe8) : mword 64) 2
                          = mword_of_int (CK + 0xea)) by pcw.
          iEval (rewrite Hq0ea) in "Hpc".
          (* ===== +0xea c.j +0x70 ====================================== *)
          assert (Htg070m : add_vec (mword_of_int (CK + 0xea) : mword 64)
                    (sign_extend' 64 (sign_extend' 21
                       (concat_vec (mword_of_int 1987 : mword 11) ('b"0"))))
                    = mword_of_int (CK + 0x70)) by pcw.
          iApply (wp_cj_s_sconf (mword_of_int (CK + 0xea))
                    (sign_extend' 21
                       (concat_vec (mword_of_int 1987 : mword 11) ('b"0")))
                    T4 (K - 10)%nat b
                    ltac:(rewrite Htg070m; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_0ea with "Htext"). }
          iIntros (CIDT6 HqT6). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htg070m) in "Hpc".
          iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2")
            as (nfj) "Hnb16".
          iPoseProof ("Htail" $! CIDT6) as "Ht".
          iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
          iApply ("Ht" $! T4 (m !!! Regidx Rs3 : mword 64) nfj with
                    "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
          { exact (cr_tregs_of_regs3 m sp0 (ientry kd) (ientry kslot)
                     ty major minor T4 HT4regs). }
          iIntros (CIDfm Hsfm mf) "%Hcsf %Ha0f Hcg Hpc".
          iDestruct (cpu_own_transport CIDT3 CIDfm 0%nat eb (proc_addr j) b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (iref_slots_combine with "Hislk Hisl2") as "Hisl".
          iDestruct (iref_slots_combine with "Hisl Hislrr") as "Hisl".
          (* THE MOVER (§9 W3): the child's own ["."] and [".."] links moved
             its bytes. *)
          iApply fupd_wp.
          (* ...and the ERA's abstract value at that same record
             (durable-disk 2b-inode-3). *)
          iMod (cr_dirty_clear ⊤ t (bv_unsigned cinum)
                  (era_node (cr_setf dnc major minor
                               (mword_of_int 1 : mword 16)) bmc datc)
                  (era_node dc2 bm2 dat2)
                  ltac:(solve_ndisj)
                  (inode_local_of_ok_rec (bv_unsigned cinum) fsc_cov fsc_logst
                     dc2 bm2 dat2 Hc2iok Hc2rl Hc2duq (Hc2ddix Ht162))
                  with "[] Hdirty Hctop") as "[Htx Hctop]";
            [iApply (ireg_inv_ftop with "Hiregi") |].
          iModIntro.
          iApply fupd_wp.
          iMod (ic_grow_tx ⊤ fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kslot (q/2)%Qp icfg_dev cinum g _
                  true t (1/2) (1/4) (1/4) (eq_sym Qp.quarter_quarter)
                  ltac:(solve_ndisj) with "Hescc Hcivalid Hcdep Htq2")
            as "(Hcivalid & Hcdep)".
          iModIntro.
          iDestruct (ic_tx_dep_intro with "Hcdep Htx") as "Hcdep".
          iSpecialize ("Hcont" $! CIDfm with "[%]"); [wp_next_chain |].
          iApply ("Hcont" $! mf true true kslot (q/2)%Qp (q/2)%Qp g cinum
                    dc2 bm2 n7 Sb7 (1 + (1 + (ns - 3)))%nat
                    with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv
                          Hpath Hbsl [%] Hisl [%] Hop [Hslkc Hcslkd
                          Hcdep Hoffrc Hcidev Hciinum Hcivalid Hcdlnk2 Hcdiat Hcmeta
                          Hcmap Hcblocks Hctop Hcfrz Hckeep
                          Hruc]").
          { exact Hcsf. }
          { exact (cr_slots_3 _ ns eq_refl Hns). }
          { split_and!.
            - exact (cr_sub2 _ _ _
                       (cr_sub2 _ _ _
                          (cr_sub2 _ _ _ (cr_sub2 _ _ _ Hsb3 Hsb4) Hsb5)
                          (cr_sub2 _ _ _ Hsb6
                             (cr_sub_union_sing Sb6
                                (IBLOCK dind icfg_ist)))) Hsb7).
            - clear -Hn7 Hn6c Hn5c Hn4c Hn3u. lia.
            - intros _. rewrite (Hwf7c eq_refl) in Hn7.
              exact (cr_fail_ip_right (S u6) n7 Hipn6 (proj1 Hn7)). }
          iEval (rewrite /inode_map) in "Hcmap".
          iDestruct "Hcmap" as "[Hcaddrs2 Hcind2]".
          iDestruct (ic_mk_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kslot cinum dc2 bm2 dat2
                       Hc2iok Hc2rl Hc2dokn (Hc2ddix Ht162)
                       (dir_orphan_clean_of_only dc2 dat2 Hc2dots) Hc2duq
                       with "Hcdlnk2 Hcdiat Hcmeta Hcaddrs2 Hcind2 Hcblocks
                             Hctop")
            as "Hcloadf".
          iAssert (ity_shot g (di_type dc2)) as "#Hcshot2".
          { rewrite Hc2ty0 Hc1ty0 cr_setf_type. iExact "Hcshot". }
          iSplitR.
          { iPureIntro. split; [rewrite Ha0f; exact HT4s2 |].
            split; [exact Hkslt |].
            split; [split; [exact (proj1 Hcpos) | exact Hcinb] |].
            split; [exact Hc2ty |].
            split; [exact Hc2mj |].
            split; [exact Hc2mn |].
            split; [exact Hc2nlz |].
            intro Hnd. exfalso. exact (Hnd Htdir). }
          iApply (create_locked_mk
 _ _ _ _ _ _ _ _ gil gisl eq_refl
                    with "Hslkc Hcslkd [Hcdep] Hoffrc Hcidev Hciinum
                          Hcivalid Hcloadf Hcshot2 Hcfrz [Hckeep] Hruc").
          { iExists locc, tlcc. iSplitR; [iPureIntro; exact Hlecc|].
            iFrame "Hflcc Hcdep". }
          { iExists lo, tl. iSplitR; [by iPureIntro|].
            iFrame "Hflk Hckeep". }
        * (* =========================================================== *)
          (*  FAIL ENTRY 3 (+0x130 taken): the PARENT's own [dirlink]     *)
          (*  fell short.  This entry sits BEFORE the +0x134 [lhu], so    *)
          (*  the parent's count is still its entry one and its entry     *)
          (*  fragments go back unchanged -- available because dirlink's  *)
          (*  atomicity at [tot < 16] IS [tot = 0].                       *)
          (* =========================================================== *)
          assert (Htot30 : tot3 = 0%nat).
          { destruct Hatom3 as [Hz | H16];
              [exact Hz | exfalso; clear -H16 Htlt3; lia]. }
          subst tot3.
          (* THE ENTRY UNITS RIDE (durable-disk 2b-inode-5):
             nothing was written, so the entry map does not move. *)
          iDestruct (ent_toks_dirlink_nop (fs_gamma_L fsc_fs) (bv_unsigned dind)
                       dn dp3 bm bm3 data dat3
                       (fun j => dirent_bytes (de_of_name (cr_low16 cinum)
                                   (bname 14 nf)) !!! j)
                       (dir_nrec (bv_unsigned (di_size dn)))
                       (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                       0%nat D eq_refl (dir_slot_le _ _) eq_refl
                       Hp3ty Hp3nl Hp3szmax Hrng3
                       Hholes Hholes3 Hszcap (Hcap3 Hszcap)
                       with "Hetk") as "Hetk".
          assert (Heqentm := dir_entries_dirlink_nop_eq dn dp3 bm bm3 data dat3
                     (fun j => dirent_bytes (de_of_name (cr_low16 cinum)
                                 (bname 14 nf)) !!! j)
                     (dir_nrec (bv_unsigned (di_size dn)))
                     (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                     0%nat eq_refl (dir_slot_le _ _) eq_refl
                     Hp3ty Hp3szmax Hrng3
                     Hholes Hholes3 Hszcap (Hcap3 Hszcap)).
          assert (Hgrowm : forall s',
                     is_Some (dir_entries (era_node dn bm data) !! s')
                     -> is_Some (dir_entries (era_node dp3 bm3 dat3) !! s'))
            by (intros s' Hs'; rewrite Heqentm; exact Hs').
          iDestruct (dlinks_intro _ _ _ _ _ D
                       ltac:(exact (FsStateInode.ent_dset_ok_grow _ _ D
                                      Hgrowm Hdok0))
                       ltac:(exact (FsStateInode.node_exact_cong
                                      (era_node dn bm data)
                                      (era_node dp3 bm3 dat3) D
                                      ltac:(rewrite /fn_is_dir /fn_type
                                              !era_node_rec Hp3ty //)
                                      ltac:(rewrite /fn_nlink !era_node_rec
                                              Hp3nl //)
                                      Hxact0))
                       with "Hetk") as "Hdlnk".
          iApply (wp_blt_x0_taken_s_sconf (mword_of_int (CK + 0x130))
                    (mword_of_int 22 : mword 13) Ra0 md3 (K - 10)%nat b
                    ltac:(nz)
                    ltac:(rgne; rewrite Ha0m3; exact cr_bltz_m1)
                    ltac:(rewrite Htg146c; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_130 with "Htext"). }
          iIntros (CIDX3 HqX3). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htg146c) in "Hpc".
          iDestruct (cpu_own_transport CIDd3 CIDX3 0%nat eb (proc_addr j) b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (iref_slots_combine with "Hislk Hislrr") as "Hislr".
          iEval (rewrite Hns3) in "Hislr".
          iAssert (ity_shot gd (di_type dp3)) as "#Hshotp3".
          { rewrite Hp3ty. iExact "Hshotl". }
          iAssert (ity_shot g (di_type dc2)) as "#Hcshot2".
          { rewrite Hc2ty0 Hc1ty0 cr_setf_type. iExact "Hcshot". }
          assert (Hipf3 : (iput_units <= n6)%nat)
            by exact (cr_mkdir_fail3 n5 n6 _ _ _ _ _ Hn5lo eq_refl Hspend3).
          (* THE MOVERS (namei-pinned-lookup.md §9 W3): the parent's append
             and the child's two interior links both moved bytes. *)
          (* THE PARENT'S RECORD-ONLY FACTS AT [dp3] (durable-disk
             2b-inode-3): the failing append is [tot = 0], so the record
             the entry re-parks is the walk's own, one MAX on.  They come
             BEFORE the retag now, because the retag owes the registry's
             row (durable-disk lane A). *)
          assert (Hp3rl : inode_rec_local dp3).
          { apply (inode_rec_local_same_type dn dp3 Hrl Hp3ty).
            - rewrite Hp3nl. exact (proj1 (proj2 Hrl)).
            - intros _. rewrite Hp3szmax. apply cr_max_div16.
              + apply (proj2 (proj2 Hrl)).
                rewrite Htydir. vm_compute. reflexivity.
              + exists (Z.of_nat (dir_slot data
                          (dir_nrec (bv_unsigned (di_size dn)))))%Z.
                rewrite Nat.add_0_r Nat2Z.inj_mul. lia. }
          iApply fupd_wp.
          iMod (ireg_top_retag ⊤ fsc_fs (bv_unsigned dind)
                  (era_node dn bm data) (era_node dp3 bm3 dat3)
                  ltac:(solve_ndisj)
                  (inode_local_of_ok_rec (bv_unsigned dind) fsc_cov fsc_logst dp3
                     bm3 dat3 Hp3iok Hp3rl Hp3duq Hp3ddix)
                  with "[] Htop") as "Htop";
            [iApply (ireg_inv_ftop with "Hiregi") |].
          (* ...and the ERA's abstract value at that same record
             (durable-disk 2b-inode-3). *)
          iMod (cr_dirty_retag ⊤ t (bv_unsigned cinum)
                  (era_node (cr_setf dnc major minor
                               (mword_of_int 1 : mword 16)) bmc datc)
                  (era_node dc2 bm2 dat2)
                  ltac:(solve_ndisj) with "[] Hdirty Hctop") as "[Hdirty Hctop]";
            [iApply (ireg_inv_ftop with "Hiregi") |].
          iModIntro.
          (* THE ["."] UNIT COMES BACK OUT OF THE CHILD'S PAYLOAD (lane
             G5).  [cr_fail_mkdir_body] takes the child WITHOUT its
             [dlinks] and re-mints one itself, so this walk is the
             last holder of the child's own tokens -- and the
             [ip->nlink = 0] flush below still needs the WHOLE pile the
             fill minted, one of whose units this arm's
             [dirlink(ip, ".", ip)] filed in the child's ["."] entry.  The
             value comes off the sibling the walk still holds, by the
             register's own agreement. *)
          iDestruct (FsStateInode.ent_toks_dot_take (fs_gamma_L fsc_fs)
                       (bv_unsigned cinum) (era_node dc1 bm1 dat1) Dc1
                       Hdot1c Horph1c with "Hcetk2") as "[(%vf1 & Hdotf1) _]".
          iApply fupd_wp.
          iMod (IregLinkNz.ireg_toks_agree ⊤ fsc_ireg fsc_fs icfg_ist icfg_nib cinum _
                  vf1 (cr_ity ty (bv_unsigned dind))
                  ltac:(solve_ndisj) Hcinb
                  with "Hiregi Hcdiat Hdotf1 Htoken")
            as "([%Hvf1 _] & Hcdiat & Hdotf1 & Htoken)".
          iModIntro.
          iAssert (FsStateLink.link_toks (fs_gamma_L fsc_fs) (bv_unsigned cinum)
                     (FsStateLink.link_reps (cr_delta ty)
                        (cr_ity ty (bv_unsigned dind))))
            with "[Htoken Hdotf1]" as "Htoken".
          { rewrite (cr_delta_dir ty Htdirc) FsStateLink.link_toks_reps_S
              FsStateLink.link_reps_1.
            iSplitL "Htoken"; [iExact "Htoken" | rewrite -Hvf1; iExact "Hdotf1"]. }
          iPoseProof (cr_fail_mkdir_half (CID := CID) γs j γl pd pav pu
 γf
 plen pfun pv ty major minor U u
                        Sb ns pidv dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                        kd qd gd γil γisl dind nf nsl t
                        HK Hnib16 Hlg Hsize Hbms0 Hbmsc Hbmsl
                        Hist0 Hcovb Hiregb Hns Hj Hgs Hspm Hrt Hal10 Hal9 Heb
                        with "Htext Hkd Hpenv Hbio Hlogc Hitb2 Hitbl Hesc Hiregi Hiopen
                              Hprocs Hdevi Hgeom Hdlk") as "Hfl".
          iPoseProof ("Hfl" $! CIDX3) as "Hf".
          iSpecialize ("Hf" with "[%]"); [wp_next_chain |].
          iAssert (∃ lo tl : nat,
              ⌜(lo <= tl)%nat⌝ ∗ IcacheRef.cred_floor lo tl ∗
              IcacheRef.inode_ref_short_genlo kd (qd/2 + qd/2)%Qp (qd/2)%Qp
                icfg_dev dind gd lo)%I with "[Hkeep]" as "Hkeep".
          { iExists lod, tld. iSplitR; [by iPureIntro|]. iFrame "Hfld Hkeep". }
          iAssert (∃ lodc tldc : nat,
              ⌜(lodc <= tldc)%nat⌝ ∗ IcacheRef.cred_floor lodc tldc ∗
              ic_handle fsc_ic kd (DepTx (qd/2)%Qp icfg_dev dind gd lodc t (1/4)))%I
            with "[Hdep]" as "Hdep".
          { iExists lodc, tldc. iSplitR; [by iPureIntro|]. iFrame "Hfldc Hdep". }
          iAssert (∃ locc tlcc : nat,
              ⌜(locc <= tlcc)%nat⌝ ∗ IcacheRef.cred_floor locc tlcc ∗
              ic_handle fsc_ic kslot (DepTx (q/2)%Qp icfg_dev cinum g locc t (1/4)))%I
            with "[Hcdep]" as "Hcdep".
          { iExists locc, tlcc. iSplitR; [by iPureIntro|]. iFrame "Hflcc Hcdep". }
          iApply ("Hf" $! md3 kslot q g gil gisl lo tl cinum dp3 bm3 dat3
                    dc2 bm2 dat2 n6 Sb6
                    with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                          [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                          [%]
                          Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14
                          Hnb2 Hslkd Hslkdd Hdep Hoffr Hidev Hiinum Hivalid
                          Hdlnk Hdiat Hmeta Hmap Hblocks Htop Hshotp3 Hfrzl Hkeep Hrud
                          Hslkc Hcslkd Hcdep Hoffrc Hcidev Hciinum Hcivalid
                          Hcdiat Hcmeta Hcmap Hcblocks Hctop Hcshot2 Hcfrz [%] Hflk Hckeep Hruc
                          Htoken
                          Hsbn Hsbi Hsbs Hsbb Hbmr Hppid Hppback Hpath Hbsl
                          Hislr Hop Hdirty Hcont").
          { exact Hmd3regs. }
          { exact Htdir. }
          { exact Hkdlt. }
          { exact Hdib. }
          { rewrite Hp3ty. exact Htydir. }
          { rewrite Hp3nl. exact Hnl0. }
          { exact Hp3iok. }
          { exact Hp3dok. }
          { exact Hp3ddix. }
          { exact Hp3duq. }
          { exact Hp3rl. }
          { exact Hkslt. }
          { exact Hcpos. }
          { exact Hcinb. }
          { exact Hc2ty. }
          { exact Hc2mj. }
          { exact Hc2mn. }
          { exact Hc2nl. }
          { exact Hc2iok. }
          { exact Hc2rl. }
          { exact Hc2dok. }
          { exact Hc2duq. }
          { exact Hc2dots. }
          { exact (cr_sub2 _ _ _
                     (cr_sub2 _ _ _ (cr_sub2 _ _ _ Hsb3 Hsb4) Hsb5) Hsb6). }
          { exact (Hsb6 _ (Hsb5 _ Hcmem4)). }
          { split; [exact Hipf3 | clear -Hn6c Hn5c Hn4c Hn3u; lia]. }
          { right. exact (Hsb6 _ Hbmem5). }
          { exact Hlek. }
      + (* ============================================================= *)
        (*  FAIL ENTRY 2 (+0x11e taken): the [".."] link fell short.  The *)
        (*  parent is still untouched; the child is [dc2], one record on. *)
        (* ============================================================= *)
        iApply (wp_blt_x0_taken_s_sconf (mword_of_int (CK + 0x11e))
                  (mword_of_int 40 : mword 13) Ra0 md2 (K - 10)%nat b
                  ltac:(nz)
                  ltac:(rgne; rewrite Ha0m2; exact cr_bltz_m1)
                  ltac:(rewrite Htg146b; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_11e with "Htext"). }
        iIntros (CIDX2 HqX2). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg146b) in "Hpc".
        iDestruct (cpu_own_transport CIDd2 CIDX2 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (iref_slots_combine with "Hislk Hislrr") as "Hislr".
        iEval (rewrite Hns3) in "Hislr".
        iAssert (ity_shot g (di_type dc2)) as "#Hcshot2".
        { rewrite Hc2ty0 Hc1ty0 cr_setf_type. iExact "Hcshot". }
        destruct (cr_mkdir_fail2 n3 n4 n5 _ _ _ _ _ Hn3lo Hspend1 Hspend2
                    eq_refl) as [Hipf2 HipfS2].
        (* the failing [".."] is dirlink's atomicity again: [tot < 16] IS
           [tot = 0], so the child's size is still the ["."] record's 16 --
           which is what the record-only facts need (2b-inode-3). *)
        assert (Htot20 : tot2 = 0%nat).
        { destruct Hatom2 as [Hz | H16];
            [exact Hz | exfalso; clear -H16 Htlt2; lia]. }
        assert (Hc2rl : inode_rec_local dc2).
        { apply (inode_rec_local_same_type dnc dc2 Hrl_datc).
          - rewrite Hc2ty0 Hc1ty0 cr_setf_type. reflexivity.
          - rewrite Hc2nlz. lia.
          - intros _. rewrite Hc2szmax Hc1szmax Hcsz0 Ht161 Htot20.
            exists 1%Z. vm_compute. reflexivity. }
        (* THE MOVER (§9 W3): the child's two interior links moved its bytes;
           the parent's own append has not run on this entry. *)
        iApply fupd_wp.
        (* ...and the ERA's abstract value at the same record. *)
        iMod (cr_dirty_retag ⊤ t (bv_unsigned cinum)
                (era_node (cr_setf dnc major minor
                             (mword_of_int 1 : mword 16)) bmc datc)
                (era_node dc2 bm2 dat2)
                ltac:(solve_ndisj) with "[] Hdirty Hctop") as "[Hdirty Hctop]";
          [iApply (ireg_inv_ftop with "Hiregi") |].
        iModIntro.
        (* THE ["."] UNIT COMES BACK OUT OF THE CHILD'S PAYLOAD (lane
           G5).  [cr_fail_mkdir_body] takes the child WITHOUT its
           [dlinks] and re-mints one itself, so this walk is the
           last holder of the child's own tokens -- and the
           [ip->nlink = 0] flush below still needs the WHOLE pile the
           fill minted, one of whose units this arm's
           [dirlink(ip, ".", ip)] filed in the child's ["."] entry.  The
           value comes off the sibling the walk still holds, by the
           register's own agreement. *)
        iDestruct (FsStateInode.ent_toks_dot_take (fs_gamma_L fsc_fs)
                     (bv_unsigned cinum) (era_node dc1 bm1 dat1) Dc1
                     Hdot1c Horph1c with "Hcetk2") as "[(%vf1 & Hdotf1) _]".
        iApply fupd_wp.
        iMod (IregLinkNz.ireg_toks_agree ⊤ fsc_ireg fsc_fs icfg_ist icfg_nib cinum _
                vf1 (cr_ity ty (bv_unsigned dind))
                ltac:(solve_ndisj) Hcinb
                with "Hiregi Hcdiat Hdotf1 Htoken")
          as "([%Hvf1 _] & Hcdiat & Hdotf1 & Htoken)".
        iModIntro.
        iAssert (FsStateLink.link_toks (fs_gamma_L fsc_fs) (bv_unsigned cinum)
                   (FsStateLink.link_reps (cr_delta ty)
                      (cr_ity ty (bv_unsigned dind))))
          with "[Htoken Hdotf1]" as "Htoken".
        { rewrite (cr_delta_dir ty Htdirc) FsStateLink.link_toks_reps_S
            FsStateLink.link_reps_1.
          iSplitL "Htoken"; [iExact "Htoken" | rewrite -Hvf1; iExact "Hdotf1"]. }
        iPoseProof (cr_fail_mkdir_half (CID := CID) γs j γl pd pav pu
 γf
 plen pfun pv ty major minor U u Sb ns pidv
                      dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                      kd qd gd γil γisl dind nf nsl t
                      HK Hnib16 Hlg Hsize Hbms0 Hbmsc Hbmsl
                      Hist0 Hcovb Hiregb Hns Hj Hgs Hspm Hrt Hal10 Hal9 Heb
                      with "Htext Hkd Hpenv Hbio Hlogc Hitb2 Hitbl Hesc Hiregi Hiopen
                            Hprocs Hdevi Hgeom Hdlk") as "Hfl".
        iPoseProof ("Hfl" $! CIDX2) as "Hf".
        iSpecialize ("Hf" with "[%]"); [wp_next_chain |].
        iAssert (∃ lo tl : nat,
            ⌜(lo <= tl)%nat⌝ ∗ IcacheRef.cred_floor lo tl ∗
            IcacheRef.inode_ref_short_genlo kd (qd/2 + qd/2)%Qp (qd/2)%Qp
              icfg_dev dind gd lo)%I with "[Hkeep]" as "Hkeep".
        { iExists lod, tld. iSplitR; [by iPureIntro|]. iFrame "Hfld Hkeep". }
        iAssert (∃ lodc tldc : nat,
            ⌜(lodc <= tldc)%nat⌝ ∗ IcacheRef.cred_floor lodc tldc ∗
            ic_handle fsc_ic kd (DepTx (qd/2)%Qp icfg_dev dind gd lodc t (1/4)))%I
          with "[Hdep]" as "Hdep".
        { iExists lodc, tldc. iSplitR; [by iPureIntro|]. iFrame "Hfldc Hdep". }
        iApply ("Hf" $! md2 kslot q g gil gisl lo tl cinum dn bm data dc2 bm2 dat2
                  n5 Sb5
                  with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                        [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                        Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
                        Hslkd Hslkdd Hdep Hoffr Hidev Hiinum Hivalid Hdlnk
                        Hdiat Hmeta Hmap Hblocks Htop Hshotl Hfrzl Hkeep Hrud
                        Hslkc Hcslkd Hcdep Hoffrc Hcidev Hciinum Hcivalid
                        Hcdiat Hcmeta Hcmap Hcblocks Hctop Hcshot2 Hcfrz [%] Hflk Hckeep Hruc Htoken
                        Hsbn Hsbi Hsbs Hsbb Hbmr Hppid Hppback Hpath Hbsl
                        Hislr Hop Hdirty Hcont").
        { exact Hmd2regs. }
        { exact Htdir. }
        { exact Hkdlt. }
        { exact Hdib. }
        { exact Htydir. }
        { exact Hnl0. }
        { exact Hiok. }
        { exact Hdok. }
        { exact Hddix. }
        { exact Hduq. }
        { exact Hrl. }
        { exact Hkslt. }
        { exact Hcpos. }
        { exact Hcinb. }
        { exact Hc2ty. }
        { exact Hc2mj. }
        { exact Hc2mn. }
        { exact Hc2nl. }
        { exact Hc2iok. }
        { exact Hc2rl. }
        { exact Hc2dok. }
        { exact Hc2duq. }
        { exact Hc2dots. }
        { exact (cr_sub2 _ _ _ (cr_sub2 _ _ _ Hsb3 Hsb4) Hsb5). }
        { exact (Hsb5 _ Hcmem4). }
        { split; [exact Hipf2 | clear -Hn5c Hn4c Hn3u; lia]. }
        { left. exact HipfS2. }
        { exact Hlek. }
    - (* =============================================================== *)
      (*  FAIL ENTRY 1 (+0x10a taken): the ["."] link fell short.  Both   *)
      (*  interior links are on the CHILD, so the parent goes over        *)
      (*  exactly as [cr_mkdir_body] handed it -- no re-park, no index    *)
      (*  description -- and the child is [dc1] at the record the failing *)
      (*  writei left.  The sibling's premises are all persistent, so     *)
      (*  this branch instantiates the lemma itself.                      *)
      (* =============================================================== *)
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (CK + 0x10a))
                (mword_of_int 60 : mword 13) Ra0 md1 (K - 10)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite Ha0m1; exact cr_bltz_m1)
                ltac:(rewrite Htg146a; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_10a with "Htext"). }
      iIntros (CIDX1 HqX1). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htg146a) in "Hpc".
      iDestruct (cpu_own_transport CIDd1 CIDX1 0%nat eb (proc_addr j) b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (iref_slots_combine with "Hislk Hislrr") as "Hislr".
      iEval (rewrite Hns3) in "Hislr".
      iAssert (ity_shot g (di_type dc1)) as "#Hcshot1".
      { rewrite Hc1ty0 cr_setf_type. iExact "Hcshot". }
      destruct (cr_mkdir_fail1 n3 n4 _ _ _ Hn3lo Hspend1) as [Hipf1 HipfS1].
      (* dirlink's atomicity once more: the failing ["."] is [tot = 0], so
         the child is still the fresh record's size (2b-inode-3). *)
      assert (Htot10 : tot1 = 0%nat).
      { destruct Hatom1 as [Hz | H16];
          [exact Hz | exfalso; clear -H16 Htlt1; lia]. }
      assert (Hc1rl : inode_rec_local dc1).
      { apply (inode_rec_local_same_type dnc dc1 Hrl_datc).
        - rewrite Hc1ty0 cr_setf_type. reflexivity.
        - rewrite Hc1nl. exact cr_nl_short_1.
        - intros _. rewrite Hc1szmax Hcsz0 Htot10.
          exists 0%Z. vm_compute. reflexivity. }
      (* THE MOVER (§9 W3): the child's first interior link moved its bytes. *)
      iApply fupd_wp.
      (* ...and the ERA's abstract value at the same record. *)
      iMod (cr_dirty_retag ⊤ t (bv_unsigned cinum)
              (era_node (cr_setf dnc major minor
                           (mword_of_int 1 : mword 16)) bmc datc)
              (era_node dc1 bm1 dat1)
              ltac:(solve_ndisj) with "[] Hdirty Hctop") as "[Hdirty Hctop]";
        [iApply (ireg_inv_ftop with "Hiregi") |].
      iModIntro.
      iPoseProof (cr_fail_mkdir_half (CID := CID) γs j γl pd pav pu
 γf
 plen pfun pv ty major minor U u Sb ns pidv
                    dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                    kd qd gd γil γisl dind nf nsl t
                    HK Hnib16 Hlg Hsize Hbms0 Hbmsc Hbmsl
                    Hist0 Hcovb Hiregb Hns Hj Hgs Hspm Hrt Hal10 Hal9 Heb
                    with "Htext Hkd Hpenv Hbio Hlogc Hitb2 Hitbl Hesc Hiregi Hiopen
                          Hprocs Hdevi Hgeom Hdlk") as "Hfl".
      iPoseProof ("Hfl" $! CIDX1) as "Hf".
      iSpecialize ("Hf" with "[%]"); [wp_next_chain |].
      iAssert (∃ lo tl : nat,
          ⌜(lo <= tl)%nat⌝ ∗ IcacheRef.cred_floor lo tl ∗
          IcacheRef.inode_ref_short_genlo kd (qd/2 + qd/2)%Qp (qd/2)%Qp
            icfg_dev dind gd lo)%I with "[Hkeep]" as "Hkeep".
      { iExists lod, tld. iSplitR; [by iPureIntro|]. iFrame "Hfld Hkeep". }
      iAssert (∃ lodc tldc : nat,
          ⌜(lodc <= tldc)%nat⌝ ∗ IcacheRef.cred_floor lodc tldc ∗
          ic_handle fsc_ic kd (DepTx (qd/2)%Qp icfg_dev dind gd lodc t (1/4)))%I
        with "[Hdep]" as "Hdep".
      { iExists lodc, tldc. iSplitR; [by iPureIntro|]. iFrame "Hfldc Hdep". }
      iApply ("Hf" $! md1 kslot q g gil gisl lo tl cinum dn bm data dc1 bm1 dat1
                n4 Sb4
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                      [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                      Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
                      Hslkd Hslkdd Hdep Hoffr Hidev Hiinum Hivalid Hdlnk
                      Hdiat Hmeta Hmap Hblocks Htop Hshotl Hfrzl Hkeep Hrud
                      Hslkc Hcslkd Hcdep Hoffrc Hcidev Hciinum Hcivalid
                      Hcdiat Hcmeta Hcmap Hcblocks Hctop Hcshot1 Hcfrz [%] Hflk Hckeep Hruc Htoken
                      Hsbn Hsbi Hsbs Hsbb Hbmr Hppid Hppback Hpath Hbsl
                      Hislr Hop Hdirty Hcont").
      { exact Hmd1regs. }
      { exact Htdir. }
      { exact Hkdlt. }
      { exact Hdib. }
      { exact Htydir. }
      { exact Hnl0. }
      { exact Hiok. }
      { exact Hdok. }
      { exact Hddix. }
      { exact Hduq. }
      { exact Hrl. }
      { exact Hkslt. }
      { exact Hcpos. }
      { exact Hcinb. }
      { exact Hc1ty. }
      { exact Hc1mj. }
      { exact Hc1mn. }
      { exact Hc1nl. }
      { exact Hc1iok. }
      { exact Hc1rl. }
      { exact Hc1dok. }
      { exact Hc1duq. }
      { exact (Hc1dots Htlt1). }
      { exact (cr_sub2 _ _ _ Hsb3 Hsb4). }
      { exact (Hsb4 _ Hmem3). }
      { split; [exact Hipf1 | clear -Hn4c Hn3u; lia]. }
      { left. exact HipfS1. }
      { exact Hlek. }
  Qed.

End ProofCreateMkdir.

End CreateMkdir.
