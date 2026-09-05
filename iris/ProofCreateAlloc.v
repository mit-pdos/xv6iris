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
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSmodeHalf.
Require Import WpSmodeIntr.
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
Require Import DinodeSlot.
Require Import DirentEnc.
Require Import DirView.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecPrintk.
Require Import SpecIput SpecIalloc SpecIupdate.
Require Import SpecIlock SpecIunlockput.
Require Import SpecDirlookup SpecDirlink.
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
(*  ProofCreateAlloc.v -- create's Alloc half. *)
(*                                                                      *)
(*  Split out of ProofCreate.v FOR THE BUILD DAG: create's five halves    *)
(*  take each other as PREMISES, not as callees, so only the             *)
(*  functor-free vocabulary in ProofCreateShared.v is shared and they     *)
(*  compile in parallel.                                                 *)
(* ==================================================================== *)

Require Import ProofCreateShared.

Module CreateAlloc (IL : ILOCK) (IUP : IUNLOCKPUT) (IA : IALLOC) (IU : IUPDATE) (DLK : DIRLINK).

Section ProofCreateAlloc.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  Lemma cr_alloc_half
      (γs : list gname) (j : nat) (γl : gname)
      (pd pav pu : mword 64)
      (γf : gname)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (U : ustate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
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
    (* mkfs's own [ushort] geometry, carried as a premise rather than as a
       slot widening (D0-a, the eleventh stop's item-2 ruling): it is what
       makes the [lw a2,4(s3)] at +0xce agree with dirlink's ZERO-extended
       halfword argument. *)
    16 * Z.of_nat icfg_nib <= 2 ^ 16 ->
    bv_unsigned ty <> 0 ->
    (* durable-disk 2b-inode-3: ialloc's claim box owes the region (L5) *)
    InodeRegion.ireg_ty_ok (ialloc_fresh ty) ->
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
    (* RULING B (iclaim-ledger.md §3.2): the sealed regime, for the
       [create_fresh_ty] span's [jal ialloc].  Persistent, borrowed. *)
    ireg_open -∗
    procs_inv γs -∗
    dev_inv fsc_uart fsc_disk -∗
    disk_geom fsc_disk pd pav pu -∗
    is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
    (* ---- THE T_DIR SUB-BRANCH, PARKED (D0-b consumes it) ---- *)
    (∀ (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
       (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
       (nf nsl : nat -> bv 8) (t : nat),
       wp_next (CID0 := CID) true (proc_addr j) (fun CIDm : CpuId =>
         cr_mkdir_body (CID := CID) γs j γl pd pav pu γf

                       plen pfun pv ty major minor U u Sb ns pidv
                       dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                       kd qd gd γil γisl dind dn bm data nf nsl t CIDm)) -∗
    (* ---- ARM FAIL's NON-DIRECTORY ENTRY, PARKED ---- *)
    (∀ (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
       (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
       (nf nsl : nat -> bv 8) (t : nat),
       wp_next (CID0 := CID) true (proc_addr j) (fun CIDf : CpuId =>
         cr_fail_body (CID := CID) γs j γl pd pav pu γf

                      plen pfun pv ty major minor U u Sb ns pidv
                      dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                      kd qd gd γil γisl dind dn bm data nf nsl t CIDf)) -∗
    (* THE CONCLUSION IS [wp_next]-WRAPPED, and it has to be.  The two parked
       bodies and [cr_alloc_body]'s own [Hcont] are all anchored at the
       SECTION hart, while the allocate half's resources arrive at whatever
       hart the [c.beqz] at +0x4c rebound to -- so the walk needs that hart's
       own chain link, which is exactly what [wp_next]'s guard is.  Stated at
       a bare [CIDa : CpuId] parameter the lemma is UNPROVABLE (nothing
       relates [CIDa] to [CID]), and this is also the shape [cr_found_half]
       takes its premise in, so the seal is one [iApply]. *)
    wp_next (CID0 := CID) true (proc_addr j) (fun CIDa : CpuId =>
      cr_alloc_body (CID := CID) γs j γl pd pav pu γf

                    plen pfun pv ty major minor U u Sb ns pidv dqb dqs dqbs dqn
                    m sp0 ret_tgt K eb b lks CIDa).
  Proof.
    intros HK Hroot Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0
           Hcovb Hbmgeo Hiregb Hni1 Hni2 Hni3 Hnib16 Htynz Htyk Hpkc Hu Hns Hj Hgs
           Hspm Hrt Hal10 Hal9 Heb.
    destruct (cr_kb K HK)
      as (HK10 & HKnp & HKil & HKdlu & HKiup & HKia & HKiu & HKdlk & HKsum).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    iIntros "#Htext #Hkd #Hpk #Hbio #Hlogc #Hkenv #Hitb2 #Hitbl #Hesc
             #Hslks #Hiregi #Hiopen #Hprocs #Hdevi #Hgeom #Hdlk Hmk Hfl".
    iPoseProof (printk_env_panic with "Hpk") as "#Hpenv".
    iDestruct (cr_tail_half j m sp0 ret_tgt K b lks HKsum Hal10 Hal9 Hspm Hrt
                 with "Htext") as "#Htail".
    iIntros (CIDa Hsa).
    iIntros (Ma w5 kd qd gd γil γisl dind dn bm data nf nsl n1 Sb1 w t).
    iIntros "%HAregs %Hkdlt %Hdib %Htydir %Hnl0 %Hnlmax %Hiok %Hdok %Hddix %Hduq %Hrl %Hnpname
             %Hnone %Hsb1 %Hwmem %Hnp1".
    iIntros "Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
             #Hslkd Hslkdd Hdep Hoffr Hidev Hiinum Hivalid Hdlnk Hdiat
             Hmeta Hmap Hblocks Htop #Hshotl Hfrzl Hkeep Hrud
             Hsbn Hsbi Hsbs Hsbb #Hbmr Hpriv Hpath Hbsl Hisl Hop Htx Hcont".
    iDestruct "Hkeep" as (lod tld) "(%Hled & #Hfld & Hkeep)".
    iDestruct (is_itable2_claims with "Hitb2") as "#Hclaimscr".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb). clear Hbm.
    (* THE HELD SET IS EMPTY, AND SAID SO ONCE.  create's contract carries no
       order premise because it does not need one: it is a level-0 contract,
       and [cpu_own_size_le] forces [lks = ∅] there.  Keep the EQUATION rather
       than substituting -- [lks] is spelled by name in every body below --
       and let [lkbelow] close each callee's bound from it. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    pose proof HAregs as HAr.
    destruct HAr as (A2 & A8 & A9 & A18 & A20 & A21 & A22 & Athr).
    (* the ledger row [CreateBudget.cr_budget_found_w] is stated at *)
    assert (Hn1lo : (9 <= n1)%nat) by exact (cr_n1_lo u n1 w Hu (proj1 Hnp1)).
    assert (Hn1u : (n1 <= u)%nat) by exact (proj2 Hnp1).
    destruct n1 as [| q1]; [exfalso; lia |].
    assert (Hq1 : (8 <= q1)%nat) by lia.
    assert (Hn1ip : (iput_units <= S q1)%nat) by exact (cr_ip_of9 _ Hn1lo).
    destruct (Hiregb dind Hdib) as [Hdblk Hdblog].
    iDestruct (cr_esc_acc kd Hkdlt with "Hesc") as "#Hescd".
    (* ===== +0xa2 c.sdsp s3,40(sp) : THE EIGHTH SAVE ================== *)
    assert (HAs3 : (Ma !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by exact (Athr Rs3 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                     ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
    assert (Hf5 : add_vec (Ma !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite A2; apply cr_frm5).
    iEval (rewrite -Hf5) in "Hb5".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0xa2)) (mword_of_int 5 : mword 6)
              Rs3 Ma (K - 10)%nat w5 b with "Hcg Hpc [] Hb5").
    { iApply (cri_0a2 with "Htext"). }
    iIntros (CIDA1 HqA1) "Hcg Hpc Hb5".
    iEval (rgne; rewrite HAs3 Hf5) in "Hb5".
    assert (Hq0a4 : add_vec_int (mword_of_int (CK + 0xa2) : mword 64) 2
                    = mword_of_int (CK + 0xa4)) by pcw.
    iEval (rewrite Hq0a4) in "Hpc".
    (* ---- the ledger, split for the gate ---- *)
    assert (Hns1 : (1 + (ns - 2))%nat = (ns - 1)%nat) by exact (cr_ns_1 ns Hns).
    iEval (rewrite -Hns1 iref_slots_op) in "Hisl".
    iDestruct "Hisl" as "[Hisl1 Hislr]".
    iDestruct (proc_priv_bare_acc γf (proc_addr j) pidv U with "Hpriv")
      as "[Hppid Hppback]".
    iDestruct (cpu_own_transport CIDa CIDA1 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    (* THE PARENT'S ARM SHRINKS BEFORE THE SPAN (durable-disk B''-tx3): the
       child's checkout is what parks the quarter, and the span's [ilock] is
       the checkout, so the quarter has to be in hand on the way IN.  On the
       ALLOC arm it comes back inside the child's deposit; on the FAIL arm,
       bare, and the parent's arm grows back to a half. *)
    iDestruct "Hdep" as (lodc tldc) "(%Hledc & #Hfldc & Hdep)".
    iApply fupd_wp.
    iMod (ic_shrink_tx ⊤ fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kd (qd/2)%Qp icfg_dev dind gd _ true
            t (1/2) (1/4) (1/4) (eq_sym Qp.quarter_quarter)
            ltac:(solve_ndisj) with "Hescd Hivalid Hdep")
      as "(Hivalid & Hdep & Htp)".
    iModIntro.
    (* THE CLAIM BOX'S SHARE (durable-disk C-5).  The span's [ialloc] leaves
       a claim box standing until its own [ilock] fills it, and what proves
       that window is inside a transaction is a POSITIVE share of this one
       parked in the region.  It cannot be the quarter the child's checkout
       parks -- the fill parks that at the same instant the claim returns
       this one -- so create lends a second quarter out of its own residue
       and takes it back on BOTH arms of the span. *)

    iDestruct (log_tx_split icfg_log t (1/2) (1/4) (1/4)
                 (eq_sym Qp.quarter_quarter) with "Htx") as "[Htcl Htx]".
    (* ===== +0xa4 .. +0xb0 : THE FRESH-TYPE GATE SPAN ================= *)
    iApply (create_fresh_ty γs j γl pd pav pu
 ty kd (DfracOwn (1/2))
              q1 Sb1 t (1/4)%Qp (1/4)%Qp
              pidv (DfracOwn (1/4)) dqs dqn Ma (K - 10)%nat eb b lks (upd_usM U _)
              ltac:(exact HKia) ltac:(exact HKil) Hlg Hist0 Hiregb Hni1 Hni2
              Hni3 Htynz Htyk Hpkc Hj Hgs Hroot A20 A9 Hkdlt Heb ltac:(lkbelow)
              (fun (CIDx : CpuId) (XIx : CurCtx) => IA.wp_ialloc_gen (CID := CIDx) (XI := XIx))
              (fun (CIDx : CpuId) (XIx : CurCtx) => IL.wp_ilock_dep_sconf (CID := CIDx) (XI := XIx))
              with "Hcg Hcnt Htext Hpc Hkd Hpk Hbio Hlogc Hitb2 Hitbl
                    Hesc Hslks Hiregi Hiopen Hprocs Hdevi Hgeom Hdlk Hsbn Hsbi
                    Hppid Hbsl Hisl1 Hidev Htp Htcl Hop").
    all: try lkbelow.
    iIntros (CIDo Hso Mo alloc kslot q g cinum gil gisl dnc bmc)
      "%Hcs3 Hcg Hcnt Hsbn Hsbi Hppid Hbsl Hidev Hres".
    destruct alloc.
    - (* ============================================================== *)
      (*  THE INODE WAS CLAIMED, LOCKED AND FILLED -- control at +0xb4   *)
      (* ============================================================== *)
      (* [Hcfrz] is A-prime's token, relayed out of the span (which ends at
         [ilock]'s return, and [SpecIlock]'s post now hands it over).  It is
         what pays the freeze pin at the +0xc4 [ip->nlink = 1] below, where
         the pure arm is FALSE. *)
      iDestruct "Hres" as "(%Hpure & Hpc & #Hslkc & Hcslkd & Hcdep & Hoffrc &
                            Hcidev & Hciinum & Hcivalid & Hcload & #Hcshot &
                            Hcfrz & Hckeep & Hruc & Htcl & Hop)".
      (* the claim box's quarter is home (durable-disk C-5) *)
      iDestruct (log_tx_join_q icfg_log t (1/2) (1/4) (1/4)
                   (eq_sym Qp.quarter_quarter) with "Htcl Htx") as "Htx".

      destruct Hpure as (Hs3 & Hkslt & Hcpos & Hcinb & Htyc & Hfresh).
      destruct (Hiregb cinum Hcinb) as [Hcblk Hcblog].
      (* A6.146: the fresh child's keep arrives GENLO with its credential
         (create_fresh_ty's post packs it); no interim pin needed. *)
      iDestruct "Hckeep" as (loC tlC) "(%HleC & #HflC & Hckeep)".
      assert (HMoregs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor Mo)
        by exact (cr_regs3_of_span m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (ientry kslot) ty major minor Ma Mo Hcs3 Hs3 HAregs).
      pose proof HMoregs as HMoR.
      destruct HMoR as (M2 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & Mthr).
      iDestruct (ic_loaded_open with "Hcload") as (datc)
        "(%Hciok & %Hrl_datc & %Hcdok & %Hcddix & %Hcdoc & %Hcduq & Hcdlnk & Hcdiat
          & Hcmeta & Hcaddrs & Hcind & Hcblocks & Hctop)".
      (* the child's record acquires [cr_setf]'s four fields below and NONE
         of them is [di_size], so its contents value never moves; convert the
         hold once, here (namei-pinned-lookup.md §9 W3). *)
      (* ...and the ERA's abstract value moves with the record, once, here:
         [cr_setf] rewrites four fields and no block, so the node's blkmap
         and data columns are untouched (durable-disk 2b-inode-3).

         AND THIS IS WHERE THE CHILD'S ROW IS SUSPENDED (durable-disk lane A,
         plan section 4b).  The record this store flushes carries
         [nlink = 1], and on the mkdir arm the child is a DIRECTORY whose two
         dot entries are still three calls away: that node is not
         well-formed, and it is the ONE mid-transaction state this kernel
         actually produces.  So create hands the registry its transaction
         token here and takes back the receipt; every arm below gives the
         token back at the point the child is well-formed again -- the dots
         on the mkdir arm, the [nlink = 0] flush on the two failing ones.
         The FILE arm disarms immediately (its child is well-formed the
         moment the count lands), which is why nothing outside create ever
         sees a suspended row on that path. *)
      (* BOTH INODES ARE WRITE-LOCKED NOW (durable-disk B''-tx2): the
         parent's arm shrank to a quarter before the span and the child's
         CHECKOUT parked what came back (B''-tx3), so the half that is left
         is what the registry's arm below parks.  Quarter + quarter + half =
         the whole element. *)
      iDestruct (cr_esc_acc kslot Hkslt with "Hesc")
        as "#Hescc".

      iApply fupd_wp.
      iMod (cr_dirty_arm ⊤ t (bv_unsigned cinum)
              (era_node dnc bmc datc)
              (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                        bmc datc)
              ltac:(solve_ndisj) with "[] [] Htx Hctop")
        as "[Hdirty Hctop]";
        [iApply (ireg_inv_ftop with "Hiregi") | iApply (ireg_inv_app with "Hiregi") |].
      iModIntro.
      iDestruct "Hcmeta" as "(Hcity & Hcimaj & Hcimin & Hcinl & Hcisz)".
      iEval (rewrite /i_major) in "Hcimaj".
      iEval (rewrite /i_minor) in "Hcimin".
      iEval (rewrite /i_nlink) in "Hcinl".
      (* ===== +0xb4 sh s5,70(s3) : ip->major = major ================== *)
      iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0xb4)) Rs5 Rs3
                (mword_of_int 70 : mword 12) Mo (K - 10)%nat (di_major dnc) b
                with "Hcg Hpc [] [Hcimaj]").
      { iApply (cri_0b4 with "Htext"). }
      { iEval (rgne; rewrite M19). iExact "Hcimaj". }
      iIntros (CIDB1 HqB1) "Hcg Hpc Hcimaj".
      iEval (rgne; rgne; rewrite M19 M21 trunc16_sext64) in "Hcimaj".
      assert (Hq0b8 : add_vec_int (mword_of_int (CK + 0xb4) : mword 64) 4
                      = mword_of_int (CK + 0xb8)) by pcw.
      iEval (rewrite Hq0b8) in "Hpc".
      (* ===== +0xb8 sh s6,72(s3) : ip->minor = minor ================== *)
      iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0xb8)) Rs6 Rs3
                (mword_of_int 72 : mword 12) Mo (K - 10)%nat (di_minor dnc) b
                with "Hcg Hpc [] [Hcimin]").
      { iApply (cri_0b8 with "Htext"). }
      { iEval (rgne; rewrite M19). iExact "Hcimin". }
      iIntros (CIDB2 HqB2) "Hcg Hpc Hcimin".
      iEval (rgne; rgne; rewrite M19 M22 trunc16_sext64) in "Hcimin".
      assert (Hq0bc : add_vec_int (mword_of_int (CK + 0xb8) : mword 64) 4
                      = mword_of_int (CK + 0xbc)) by pcw.
      iEval (rewrite Hq0bc) in "Hpc".
      (* ===== +0xbc c.li a4,1 ======================================== *)
      iApply (wp_cli_s_sconf (mword_of_int (CK + 0xbc)) Ra4
                (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                Mo (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                with "Hcg Hpc []").
      { iApply (cri_0bc with "Htext"). }
      iIntros (CIDB3 HqB3) "Hcg Hpc".
      pose (W1 := <[Regidx Ra4 := regval_into_reg
                    (mword_of_int 1 : mword 64)]> Mo).
      change (<[Regidx Ra4 := regval_into_reg
                    (mword_of_int 1 : mword 64)]> Mo) with W1.
      assert (HW1a4 : W1 !!! Regidx Ra4 = (mword_of_int 1 : mword 64))
        by (rewrite /W1; apply upd_eq).
      assert (HW1s3 : W1 !!! Regidx Rs3 = ientry kslot)
        by (rewrite /W1 upd_ne; [exact M19 | nz]).
      assert (HW1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor W1)
        by (rewrite /W1; apply cr_regs3_caller; [exact Hcsa4 | exact HMoregs]).
      assert (Hq0be : add_vec_int (mword_of_int (CK + 0xbc) : mword 64) 2
                      = mword_of_int (CK + 0xbe)) by pcw.
      iEval (rewrite Hq0be) in "Hpc".
      (* ===== +0xbe sh a4,74(s3) : ip->nlink = 1 ===================== *)
      iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0xbe)) Ra4 Rs3
                (mword_of_int 74 : mword 12) W1 (K - 10)%nat (di_nlink dnc) b
                with "Hcg Hpc [] [Hcinl]").
      { iApply (cri_0be with "Htext"). }
      { iEval (rgne; rewrite HW1s3). iExact "Hcinl". }
      iIntros (CIDB4 HqB4) "Hcg Hpc Hcinl".
      iEval (rgne; rgne; rewrite HW1s3 HW1a4 cr_trunc16_one) in "Hcinl".
      assert (Hq0c2 : add_vec_int (mword_of_int (CK + 0xbe) : mword 64) 4
                      = mword_of_int (CK + 0xc2)) by pcw.
      iEval (rewrite Hq0c2) in "Hpc".
      (* the record the three stores leave *)
      iAssert (inode_meta (ientry kslot)
                 (cr_setf dnc major minor (mword_of_int 1 : mword 16)))
        with "[Hcity Hcimaj Hcimin Hcinl Hcisz]" as "Hcmeta".
      { rewrite /inode_meta /cr_setf /=. rewrite /i_major /i_minor /i_nlink.
        iFrame. }
      iAssert (inode_map fsc_fs (ientry kslot) bmc)
        with "[Hcaddrs Hcind]" as "Hcmap".
      { rewrite /inode_map. iFrame. }
      (* ===== +0xc2 c.mv a0,s3 ====================================== *)
      iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xc2)) Ra0 Rs3 W1
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cri_0c2 with "Htext"). }
      iIntros (CIDB5 HqB5) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (W2 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (W1 !!! Regidx Rs3))]> W1).
      change (<[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (W1 !!! Regidx Rs3))]> W1) with W2.
      assert (HW2a0 : W2 !!! Regidx Ra0 = ientry kslot).
      { rewrite /W2 upd_eq. rewrite HW1s3. apply add_vec_zero_l. }
      assert (HW2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor W2)
        by (rewrite /W2; apply cr_regs3_caller; [exact Hcsa0 | exact HW1regs]).
      assert (Hq0c4 : add_vec_int (mword_of_int (CK + 0xc2) : mword 64) 2
                      = mword_of_int (CK + 0xc4)) by pcw.
      iEval (rewrite Hq0c4) in "Hpc".
      (* ===== +0xc4 jal iupdate : THE MINT ========================== *)
      assert (Htgiu : add_vec (mword_of_int (CK + 0xc4) : mword 64)
                (sign_extend' 64 (mword_of_int 2090198 : mword 21))
                = mword_of_int KernelSyms.iupdate) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (CK + 0xc4)) Rra
                (mword_of_int 2090198 : mword 21) W2 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_0c4 with "Htext"). }
      iIntros (CIDB6 HqB6) "Hcg Hpc".
      iEval (rewrite Htgiu) in "Hpc".
      pose (W3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0xc4) : mword 64) 4)]> W2).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0xc4) : mword 64) 4)]> W2) with W3.
      assert (HW3ra : W3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (CK + 0xc4) : mword 64) 4)
        by (rewrite /W3; apply upd_eq).
      assert (HW3a0 : W3 !!! Regidx Ra0 = ientry kslot)
        by (rewrite /W3 upd_ne; [exact HW2a0 | nz]).
      assert (HW3regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor W3)
        by (rewrite /W3; apply cr_regs3_caller; [exact Hcsra | exact HW2regs]).
      (* the mint's arithmetic and its membership premise *)
      assert (Htyz : bv_unsigned (di_type dnc) <> 0) by exact (proj1 Hfresh).
      (* THE MINT'S TWO WALK-LEVEL FACTS (the reshaped premise, the twelfth
         stop).  [wp_iupdate_link] no longer takes the Z-level increment --
         no caller could prove it at an arbitrary count -- but the value
         the [sh] committed and the guard's own disequality.  At the FRESH
         child both are [fresh_shape]'s zero, so both are [vm_compute]. *)
      assert (Hcnl0 : di_nlink dnc = (mword_of_int 0 : mword 16)).
      { apply bv_eq. rewrite (fresh_shape_nlink dnc Hfresh).
        vm_compute. reflexivity. }
      assert (Hbump : di_nlink (cr_setf dnc major minor
                                  (mword_of_int 1 : mword 16))
                      = add_vec (di_nlink dnc : mword 16) (mword_of_int 1)).
      { rewrite cr_setf_nlink Hcnl0. apply bv_eq; vm_compute; reflexivity. }
      assert (Hgrd : di_nlink dnc <> (mword_of_int 32767 : mword 16)).
      { rewrite Hcnl0. intro Hc. apply (f_equal bv_unsigned) in Hc.
        vm_compute in Hc. discriminate. }
      assert (Hcadd : di_addrs (cr_setf dnc major minor
                                 (mword_of_int 1 : mword 16)) = bm_cells bmc)
        by (rewrite cr_setf_addrs; exact (proj1 (proj2 (proj2 Hciok)))).
      assert (Hcdirlen : length (bm_dir bmc) = NDIRECT)
        by exact (blkmap_wf_dir_len fsc_cov fsc_logst bmc (proj1 Hciok)).
      destruct q1 as [| q2]; [exfalso; lia |].
      iDestruct (cr_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
      iDestruct (cpu_own_transport CIDo CIDB6 0%nat eb (proc_addr j) b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (IU.wp_iupdate_link γs j γl pd pav pu
 (ientry kslot) cinum
                (cr_setf dnc major minor (mword_of_int 1 : mword 16)) dnc bmc
                q2 (Sb1 ∪ {[IBLOCK cinum icfg_ist]}) true
                (* pin = true: this site pays the TOKEN arm (§3.9) *) true
                (Some (cr_ity ty (bv_unsigned dind)))
                pidv
                (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
                W3 (K - 10)%nat eb b lks
                U ltac:(exact HKiu)
                ltac:(intros _; exact (cr_in_union_sing Sb1 _))
                Hlg Hist0 Hcblk Hcblog Hcinb
                ltac:(exact (di_type_stable_eq _ _
                        (cr_setf_type dnc major minor _)))
                ltac:(exact (cr_setf_type_nz dnc major minor _ Htyz))

                (* THE FILL'S OWN PREMISE (lane G5): the claim box's
                   multiplicity is ZERO -- [fresh_shape_nlink]'s count --
                   so the value is free to be CHOSEN here, and the choice
                   is [TDir dp] at a directory (which is what lets [dp]'s
                   name record for the child assert "my target's parent is
                   me") and [TFile] otherwise. *)
                ltac:(exact (cr_fill_choice_ok ty major minor dnc dind
                               ltac:(rewrite Hcnl0; vm_compute; reflexivity)
                               Htyc))
                Hbump Hgrd
                (* ===== THE IIIc WALL, SITE 1 OF 2 -- PAID (RULING A-prime,
                   iclaim-ledger.md §3.9) =====================================
                   [SpecIupdate.wp_iupdate_link]'s freeze-pin premise is now
                   the two-armed
                     |_di_nlink dnc <> 0_| \/ ifreeze_off (bv_unsigned cinum),
                   and this site pays the RIGHT arm with [Hcfrz].  The LEFT
                   arm is FALSE here, not merely unavailable: this is
                   create's FRESH CHILD and [Hcnl0] -- read off
                   [fresh_shape_nlink] -- says its pre-count is exactly ZERO,
                   on BOTH the tagged mkdir arm and the plain file one
                   ([ip->nlink = 1] is a 0 -> 1 move either way).  No
                   record-level fact could ever have saved it (the B1/B2
                   debt, §0: a mid-free box and a fresh claim box are the
                   SAME record), which is why the supply had to be a LEDGER
                   COLUMN.  The token is BORROWED: it comes straight back in
                   the continuation below and travels on to the child's
                   iunlock. *)
                Hcadd Hcdirlen Hj Hgs HW3a0 Heb
                with "Hcg Hcnt Htext Hkd Hpc Hpenv Hbio Hlogc Hcidev Hciinum
                      Hcmeta Hcmap Hsbi Hiregi Hcdiat [Hcfrz] Hppid Hprocs
                      Hdevi Hgeom Hdlk Hbs2 Hop").
      all: try lkbelow.
      { rewrite /InodeRegion.ireg_link_pin. iExact "Hcfrz". }
      all: try lkbelow.
      iIntros (CIDiu Hsiu miu)
        "%Hcsiu Hcg Hcnt Hpc Hppid Hcidev Hciinum Hcmeta Hcmap Hsbi Hcdiat
         (%vfill & [%Hvok %Hvchoice] & Htoken) Hpin Hbs2 Hop".
      (* the FILL's value IS the one this site chose ([oty = Some _]) *)
      assert (Hvfill : vfill = cr_ity ty (bv_unsigned dind))
        by exact (Hvchoice _ eq_refl).
      subst vfill.
      (* ...and the pile is [cr_delta ty] wide: the claim box's count is
         zero, so [ireg_dot_delta] is TWO at a directory and ONE at a
         file. *)
      assert (Hdelta : InodeRegion.ireg_dot_delta (bv_unsigned (di_type dnc))
                         (bv_unsigned (di_nlink dnc)) = cr_delta ty).
      { rewrite /InodeRegion.ireg_dot_delta /cr_delta Htyc.
        assert (Hz : bv_unsigned (di_nlink dnc) = 0)
          by (rewrite Hcnl0; vm_compute; reflexivity).
        rewrite (bool_decide_eq_true_2 (bv_unsigned (di_nlink dnc) = 0) Hz)
          andb_true_r.
        assert (Hdty : InodeRegion.ireg_dir_ty
                       = bv_unsigned SpecDirlookup.T_DIR)
          by (vm_compute; reflexivity).
        rewrite Hdty.
        destruct (decide (ty = SpecDirlookup.T_DIR)) as [-> | Hne].
        - rewrite (bool_decide_eq_true_2 _ eq_refl) //.
        - rewrite (bool_decide_eq_false_2
                     (bv_unsigned ty = bv_unsigned SpecDirlookup.T_DIR)
                     ltac:(intros Hc; apply Hne; by apply bv_eq)) //. }
      iEval (rewrite Hdelta) in "Htoken".
      (* the pin premise came back, and at [pin = true] it IS the token
         ([InodeRegion.ireg_link_pin]'s own definition).  It goes home at the
         child's iunlock. *)
      iEval (rewrite /InodeRegion.ireg_link_pin) in "Hpin".
      iRename "Hpin" into "Hcfrz".
      assert (Hpciu : ret_pc (W3 !!! Regidx Rra : mword 64)
                      = mword_of_int (CK + 0xc8)) by (rewrite HW3ra; pcw).
      iEval (rewrite Hpciu) in "Hpc".
      assert (Hmiuregs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                           (ientry kslot) ty major minor miu)
        by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (ientry kslot) ty major minor W3 miu Hcsiu HW3regs).
      pose proof Hmiuregs as HmiuR.
      destruct HmiuR as (N2 & N8 & N9 & N18 & N19 & N20 & N21 & N22 & Nthr).
      iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
        [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
      (* ===== +0xc8 c.li a4,1 ====================================== *)
      iApply (wp_cli_s_sconf (mword_of_int (CK + 0xc8)) Ra4
                (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                miu (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                with "Hcg Hpc []").
      { iApply (cri_0c8 with "Htext"). }
      iIntros (CIDB7 HqB7) "Hcg Hpc".
      pose (W4 := <[Regidx Ra4 := regval_into_reg
                    (mword_of_int 1 : mword 64)]> miu).
      change (<[Regidx Ra4 := regval_into_reg
                    (mword_of_int 1 : mword 64)]> miu) with W4.
      assert (HW4a4 : W4 !!! Regidx Ra4 = (mword_of_int 1 : mword 64))
        by (rewrite /W4; apply upd_eq).
      assert (HW4s4 : W4 !!! Regidx Rs4 = (sign_extend' 64 ty : mword 64))
        by (rewrite /W4 upd_ne; [exact N20 | nz]).
      assert (HW4s3 : W4 !!! Regidx Rs3 = ientry kslot)
        by (rewrite /W4 upd_ne; [exact N19 | nz]).
      assert (HW4s1 : W4 !!! Regidx Rs1 = ientry kd)
        by (rewrite /W4 upd_ne; [exact N9 | nz]).
      assert (HW4s0 : W4 !!! Regidx Rs0 = sp0)
        by (rewrite /W4 upd_ne; [exact N8 | nz]).
      assert (HW4regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor W4)
        by (rewrite /W4; apply cr_regs3_caller; [exact Hcsa4 | exact Hmiuregs]).
      assert (Hq0ca : add_vec_int (mword_of_int (CK + 0xc8) : mword 64) 2
                      = mword_of_int (CK + 0xca)) by pcw.
      iEval (rewrite Hq0ca) in "Hpc".
      assert (Htg0f8 : add_vec (mword_of_int (CK + 0xca) : mword 64)
                (sign_extend' 64 (mword_of_int 46 : mword 13))
                = mword_of_int (CK + 0xf8)) by pcw.
      destruct (decide (ty = SpecDirlookup.T_DIR)) as [Htdir | Htdir].
      + (* ============================================================ *)
        (*  +0xca TAKEN: the whole T_DIR sub-branch, PARKED.  The child's *)
        (*  fragment is UNDEPOSITED here -- +0xc4 minted it and this arm's *)
        (*  own [dirlink(dp,name)] at +0x12c is what spends it.            *)
        (* ============================================================ *)
        iApply (wp_beq_taken_s_sconf (mword_of_int (CK + 0xca))
                  (mword_of_int 46 : mword 13) Ra4 Rs4 W4 (K - 10)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HW4s4 HW4a4;
                        exact (cr_tdir_eq ty Htdir))
                  ltac:(rewrite Htg0f8; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_0ca with "Htext"). }
        iIntros (CIDB8 HqB8). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg0f8) in "Hpc".
        iDestruct (cpu_own_transport CIDiu CIDB8 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* the child's suspended row travels into the mkdir arm, which is
           where its dot entries land and the row comes back (lane A) *)
        iSpecialize ("Hmk" $! kd qd gd γil γisl dind dn bm data nf nsl t).
        iPoseProof ("Hmk" $! CIDB8) as "Hm".
        iSpecialize ("Hm" with "[%]"); [wp_next_chain |].
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
        iApply ("Hm" $! W4 kslot q g gil gisl loC tlC cinum dnc bmc datc
                  (S q2) (Sb1 ∪ {[IBLOCK cinum icfg_ist]}
                          ∪ {[IBLOCK cinum icfg_ist]})
                  with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                        [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                        Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                        Hnb14 Hnb2 Hslkd Hslkdd Hdep Hoffr Hidev Hiinum
                        Hivalid Hdlnk Hdiat Hmeta Hmap Hblocks Htop Hshotl Hfrzl Hkeep Hrud
                        Hslkc Hcslkd Hcdep Hoffrc Hcidev Hciinum Hcivalid
                        Hcdlnk Hcdiat Hcmeta Hcmap Hcblocks Hctop Hcshot Hcfrz [%] []
                        Hckeep Hruc Htoken Hsbn Hsbi Hsbs Hsbb Hbmr Hppid Hppback Hpath
                        Hbsl Hislr Hop Hdirty Hcont").
        { exact HW4regs. }
        { exact Htdir. }
        { exact Hkdlt. }
        { exact Hdib. }
        { exact Htydir. }
        { exact Hnl0. }
        { exact (Hnlmax Htdir). }
        { exact Hiok. }
        { exact Hdok. }
        { exact Hddix. }
        { exact Hduq. }
        { exact Hrl. }
        { exact Hnpname. }
        { exact Hnone. }
        { exact Hkslt. }
        { exact Hcpos. }
        { exact Hcinb. }
        { exact Hfresh. }
        { exact Hrl_datc. }
        { exact Htyc. }
        { exact Hciok. }
        {exact Hcdok. }
        { exact (cr_sub2 _ _ _ (cr_sub2 _ _ _ Hsb1 (cr_sub_union_sing Sb1 _))
                   (cr_sub_union_sing _ _)). }
        { exact (cr_in_union_sing _ _). }
        { split; [lia | lia]. }
        (* THE CORRELATION, discharged where both halves are in hand. *)
        { destruct w.
          - left.
            exact (cr_sub2 _ _ _ (cr_sub_union_sing Sb1 _)
                     (cr_sub_union_sing _ _) _ (Hwmem eq_refl)).
          - right.
            exact (cr_n3_lo u q2 false Hu (proj1 Hnp1) eq_refl). }
        { exact HleC. }
        { iExact "HflC". }
      + (* ============================================================ *)
        (*  +0xca FALLS THROUGH: the non-directory path                  *)
        (* ============================================================ *)
        iApply (wp_beq_fall_s_sconf (mword_of_int (CK + 0xca))
                  (mword_of_int 46 : mword 13) Ra4 Rs4 W4 (K - 10)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HW4s4 HW4a4;
                        exact (cr_tdir_ne ty Htdir))
                  with "Hcg Hpc []").
        { iApply (cri_0ca with "Htext"). }
        iIntros (CIDB8 HqB8) "Hcg Hpc".
        assert (Htdirz : bv_unsigned (di_type dnc) <> T_DIR_z).
        { rewrite Htyc. intro Hc. apply Htdir.
          apply bv_eq. rewrite Hc. vm_compute. reflexivity. }
        (* THE CHILD'S ROW COMES BACK AT ONCE ON THIS ARM (durable-disk lane
           A): a FILE or DEVICE record at [nlink = 1] is well-formed the
           moment the count lands -- only a DIRECTORY owes dot entries -- so
           the suspension the shared prologue took out is released here and
           the transaction token goes home.  Nothing outside create ever
           sees a suspended row on this path. *)
        assert (Hlocfile : inode_local (bv_unsigned cinum)
                  (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                            bmc datc)).
        { apply (inode_local_of_ok_rec (bv_unsigned cinum) fsc_cov fsc_logst _ bmc
                   datc).
          - exact (cr_setf_inode_ok fsc_cov fsc_logst dnc bmc datc major minor
                     (mword_of_int 1 : mword 16) Hciok).
          - apply (cr_setf_rec_local dnc major minor
                     (mword_of_int 1 : mword 16) Hrl_datc).
            vm_compute. discriminate.
          - apply dir_uniq_not_dir. rewrite cr_setf_type. exact Htdirz.
          - apply dir_dots_ix_not_dir. rewrite cr_setf_type. exact Htdirz. }
        iApply fupd_wp.
        iMod (cr_dirty_clear_same ⊤ t (bv_unsigned cinum)
                (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                          bmc datc)
                (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                          bmc datc)
                ltac:(solve_ndisj) eq_refl Hlocfile with "[] [] Hdirty Hctop")
          as "[Htx Hctop]";
          [iApply (ireg_inv_ftop with "Hiregi") | iApply (ireg_inv_app with "Hiregi") |].
        iModIntro.
        assert (Hq0ce : add_vec_int (mword_of_int (CK + 0xca) : mword 64) 4
                        = mword_of_int (CK + 0xce)) by pcw.
        iEval (rewrite Hq0ce) in "Hpc".
        (* ===== +0xce lw a2,4(s3) : the child's inum ================ *)
        iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0xce)) Ra2 Rs3
                  (mword_of_int 4 : mword 12) W4 (K - 10)%nat cinum b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hciinum]").
        { iApply (cri_0ce with "Htext"). }
        { iEval (rgne; rewrite HW4s3). iExact "Hciinum". }
        iIntros (CIDC1 HqC1) "Hcg Hpc Hciinum".
        iEval (rgne; rewrite HW4s3) in "Hciinum".
        pose (X1 := <[Regidx Ra2 := regval_into_reg
                      (sign_extend' 64 cinum : mword 64)]> W4).
        change (<[Regidx Ra2 := regval_into_reg
                      (sign_extend' 64 cinum : mword 64)]> W4) with X1.
        assert (HX1a2 : X1 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
          by (rewrite /X1; apply upd_eq).
        assert (HX1s0 : X1 !!! Regidx Rs0 = sp0)
          by (rewrite /X1 upd_ne; [exact HW4s0 | nz]).
        assert (HX1s1 : X1 !!! Regidx Rs1 = ientry kd)
          by (rewrite /X1 upd_ne; [exact HW4s1 | nz]).
        assert (HX1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                            (ientry kslot) ty major minor X1)
          by (rewrite /X1; apply cr_regs3_caller; [exact Hcsa2 | exact HW4regs]).
        assert (Hq0d2 : add_vec_int (mword_of_int (CK + 0xce) : mword 64) 4
                        = mword_of_int (CK + 0xd2)) by pcw.
        iEval (rewrite Hq0d2) in "Hpc".
        (* ===== +0xd2 addi a1,s0,-80 : a1 = &name =================== *)
        iApply (wp_addi4_s_sconf (mword_of_int (CK + 0xd2)) Ra1 Rs0
                  (mword_of_int 4016 : mword 12) X1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_0d2 with "Htext"). }
        iIntros (CIDC2 HqC2) "Hcg Hpc".
        pose (X2 := <[Regidx Ra1 := regval_into_reg
                      (add_vec (rget X1 Rs0)
                         (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> X1).
        change (<[Regidx Ra1 := regval_into_reg
                      (add_vec (rget X1 Rs0)
                         (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> X1) with X2.
        assert (HX2a1 : X2 !!! Regidx Ra1 = pa_stk sp0 10).
        { rewrite /X2 upd_eq. rewrite rget_ne;
            [| intro Hz1; injection Hz1 as Hz2; vm_compute in Hz2; congruence ].
          rewrite HX1s0. apply cr_name_addr. }
        assert (HX2a2 : X2 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
          by (rewrite /X2 upd_ne; [exact HX1a2 | nz]).
        assert (HX2s1 : X2 !!! Regidx Rs1 = ientry kd)
          by (rewrite /X2 upd_ne; [exact HX1s1 | nz]).
        assert (HX2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                            (ientry kslot) ty major minor X2)
          by (rewrite /X2; apply cr_regs3_caller; [exact Hcsa1 | exact HX1regs]).
        assert (Hq0d6 : add_vec_int (mword_of_int (CK + 0xd2) : mword 64) 4
                        = mword_of_int (CK + 0xd6)) by pcw.
        iEval (rewrite Hq0d6) in "Hpc".
        (* ===== +0xd6 c.mv a0,s1 : the PARENT ======================= *)
        iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xd6)) Ra0 Rs1 X2
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_0d6 with "Htext"). }
        iIntros (CIDC3 HqC3) "Hcg Hpc". iEval (rgne) in "Hcg".
        pose (X3 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64)
                         (X2 !!! Regidx Rs1))]> X2).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64)
                         (X2 !!! Regidx Rs1))]> X2) with X3.
        assert (HX3a0 : X3 !!! Regidx Ra0 = ientry kd).
        { rewrite /X3 upd_eq. rewrite HX2s1. apply add_vec_zero_l. }
        assert (HX3a1 : X3 !!! Regidx Ra1 = pa_stk sp0 10)
          by (rewrite /X3 upd_ne; [exact HX2a1 | nz]).
        assert (HX3a2 : X3 !!! Regidx Ra2
                        = (sign_extend' 64 cinum : mword 64))
          by (rewrite /X3 upd_ne; [exact HX2a2 | nz]).
        assert (HX3regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                            (ientry kslot) ty major minor X3)
          by (rewrite /X3; apply cr_regs3_caller; [exact Hcsa0 | exact HX2regs]).
        assert (Hq0d8 : add_vec_int (mword_of_int (CK + 0xd6) : mword 64) 2
                        = mword_of_int (CK + 0xd8)) by pcw.
        iEval (rewrite Hq0d8) in "Hpc".
        (* ===== +0xd8 jal dirlink(dp, name, ip->inum) =============== *)
        (* THE HALFWORD BRIDGE: the [lw] sign-extends a 32-bit cell and
           dirlink's a2 premise is a ZERO-extended SIXTEEN-bit one.  The two
           agree below 2^16, and what bounds the inum there is the ruled
           premise [16 * nib <= 2^16]. *)
        assert (Hc16 : bv_unsigned cinum < 2 ^ 16) by lia.
        assert (Hcl16 : bv_unsigned (cr_low16 cinum) = bv_unsigned cinum)
          by exact (cr_low16_unsigned cinum Hc16).
        assert (Htgdlk : add_vec (mword_of_int (CK + 0xd8) : mword 64)
                  (sign_extend' 64 (mword_of_int 2092376 : mword 21))
                  = mword_of_int KernelSyms.dirlink) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0xd8)) Rra
                  (mword_of_int 2092376 : mword 21) X3 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_0d8 with "Htext"). }
        iIntros (CIDC4 HqC4) "Hcg Hpc".
        iEval (rewrite Htgdlk) in "Hpc".
        pose (X4 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0xd8) : mword 64) 4)]> X3).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0xd8) : mword 64) 4)]> X3) with X4.
        assert (HX4ra : X4 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CK + 0xd8) : mword 64) 4)
          by (rewrite /X4; apply upd_eq).
        assert (HX4a0 : X4 !!! Regidx Ra0 = ientry kd)
          by (rewrite /X4 upd_ne; [exact HX3a0 | nz]).
        assert (HX4a1 : X4 !!! Regidx Ra1 = pa_stk sp0 10)
          by (rewrite /X4 upd_ne; [exact HX3a1 | nz]).
        assert (HX4a2 : X4 !!! Regidx Ra2
                        = (zero_extend' 64 (cr_low16 cinum) : mword 64)).
        { rewrite /X4 upd_ne; [| nz]. rewrite HX3a2.
          exact (cr_a2_low16 cinum Hc16). }
        assert (HX4regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                            (ientry kslot) ty major minor X4)
          by (rewrite /X4; apply cr_regs3_caller; [exact Hcsra | exact HX3regs]).
        (* dirlink's premises, off the parent's [inode_ok] and [dir_ok] *)
        assert (Hdz : bv_unsigned (di_type dn) = T_DIR_z)
          by (rewrite Htydir; vm_compute; reflexivity).
        assert (Hbmwf : blkmap_wf fsc_cov fsc_logst bm) by exact (proj1 Hiok).
        assert (Hbmcov : bm_covers bm (bv_unsigned (di_size dn)))
          by exact (proj1 (proj2 Hiok)).
        assert (Hdaddr : di_addrs dn = bm_cells bm)
          by exact (proj1 (proj2 (proj2 Hiok))).
        assert (Hszcap : bv_unsigned (di_size dn)
                         <= Z.of_nat MAXFILE * Z.of_nat BSIZE)
          by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hiok))))).
        assert (Hholes : blk_holes_zero bm data)
          by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hiok)))))).
        assert (Htynzd : bv_unsigned (di_type dn) <> 0)
          by exact (proj1 (proj2 (proj2 (proj2 Hiok)))).
        assert (Hsized : inode_sized data)
          by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hiok)))))).
        assert (Hsz31 : bv_unsigned (di_size dn) < 2 ^ 31)
          by (unfold MAXFILE, BSIZE in Hszcap; simpl in Hszcap; lia).
        assert (Hcl16b : bv_unsigned (cr_low16 cinum) < 16 * Z.of_nat icfg_nib)
          by (rewrite Hcl16; exact Hcinb).
        iEval (rewrite -HX4a1) in "Hnb14".
        iEval (rewrite /inode_map) in "Hmap".
        iDestruct "Hmap" as "[Haddrs Hind]".
        iAssert (inode_map fsc_fs (ientry kd) bm) with "[Haddrs Hind]" as "Hmap".
        { rewrite /inode_map. iFrame. }
        assert (Hns2 : (1 + (ns - 3))%nat = (ns - 2)%nat)
          by exact (cr_ns_2 ns Hns).
        iEval (rewrite -Hns2 iref_slots_op) in "Hislr".
        iDestruct "Hislr" as "[Hislk Hislrr]".
        iDestruct (cpu_own_transport CIDiu CIDC4 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* dirlink borrows the LEDGER half alone (durable-disk 2b-inode-5);
           the counting RA's tokens stay in this walk's hand and the
           deposit below files the [+0xc4] mint's unit among them. *)
        (* dirlink's own [iput] may need a share (durable-disk B''-tx5); the
           FILE arm has the residue free, so it simply lends it. *)

        iApply (DLK.wp_dirlink_gen γs j γl pd pav pu
 γf
                  (ientry kd) dind bm data dn dn nf (cr_low16 cinum)
                  (S q2) (Sb1 ∪ {[IBLOCK cinum icfg_ist]}
                          ∪ {[IBLOCK cinum icfg_ist]})
                  _ _
                  pidv (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn 1) dqs
                  dqb dqbs (DfracOwn (1/2))
                  X4 (K - 10)%nat eb b lks
                  U ltac:(exact HKdlk) Htydir Hbmcov Hszcap
                  ltac:(exact (Hdok Hdz))
                  (* THE RELAYED LICENCE (§7.5.6, row 5).  LEFT disjunct,
                     earned by the same [sysfile.c:269] guard the found half
                     fell through at +0x2a/+0x2e and froze into [Hnl0]. *)
                  ltac:(left; exact (cr_nl0z dn Hnl0))
                  ltac:(exact (cr_doc_of_live dn dn data eq_refl Hnl0))
                  ltac:(exact (di_type_stable_refl dn))
                  ltac:(exact (di_nlink_stable_refl dn Htynzd))
                  Hlg Hbmwf Hholes Hdaddr Hsz31 Hist0 Hdblk Hdblog Hdib
                  Hcl16b Hbmgeo Hpkc Hsize Hbms0 Hbmsc Hbmsl Hcovb Hiregb
                  ltac:(exact (cr_alloc_dlneed (S q2) _ _ ltac:(lia)))
                  Hj Hgs HX4a0 HX4a2 Heb ltac:(lkbelow)
                  with "Hcg Hcnt Htext Hpc Hkd Hpk Hbio Hlogc Hkenv
                        Hidev Hiinum Hmeta Hmap Hblocks Hnb14 Hsbi Hsbs Hsbb
                        Hbmr Hiregi Hiopen Hdiat Hppid Hprocs Hdevi Hgeom Hdlk Hbsl
                        Hitb2 Hitbl Hesc Hslks Hislk Hdlnk Hop Htx").
        all: try lkbelow.
        iIntros (CIDdl Hsdl mdl found bm' data' dn' dn0' n' Sb' tot)
          "%Hcsdl Hcg Hcnt Hpc Hidev Hiinum Hmeta Hmap Hblocks Hnb14 Hsbi Hsbs
           Hsbb Hdiat Hppid Hbsl Hislk Hdlnk %Hn' %Hsb' %Hdl16 %Hfd0 Hop Htx
           %Hcapp %Hsizedp %Harm".

        (* the borrow comes back as the PAIR; open it here, because the
           deposit below files the [+0xc4] mint's unit among the home's
           entry units (durable-disk 2b-inode-5) *)
        iDestruct (dlinks_open with "Hdlnk")
          as "(%D & [%Hdok0 %Hxact0] & Hetk)".
        iEval (rewrite HX4a1) in "Hnb14".
        assert (Hpcdl : ret_pc (X4 !!! Regidx Rra : mword 64)
                        = mword_of_int (CK + 0xdc)) by (rewrite HX4ra; pcw).
        iEval (rewrite Hpcdl) in "Hpc".
        assert (Hmdlregs : cr_regs3 m sp0 (ientry kd)
                             (mword_of_int 0 : mword 64) (ientry kslot)
                             ty major minor mdl)
          by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                      (ientry kslot) ty major minor X4 mdl Hcsdl HX4regs).
        assert (Htg146 : add_vec (mword_of_int (CK + 0xdc) : mword 64)
                  (sign_extend' 64 (mword_of_int 106 : mword 13))
                  = mword_of_int (CK + 0x146)) by pcw.
        destruct found.
        * (* dirlookup INSIDE dirlink found the name -- refuted by the
             found half's own [dir_first ... = None] *)
          exfalso. destruct Harm as (Hfst & _). exact (Hfst Hnone).
        * destruct Harm as (_ & Hwf' & Hholes' & Haddr' & Hsz31' &
                            Hcov' & Hdn' & Hdn0' & Htot16 & Hrng & Hbl).
          (* the append arm's two halves: the spend is UNGUARDED (it prices
             the failing append at the same credit-aware figure), the
             memberships are guarded by [0 < tot] and this walk never wants
             them -- the parent's next call is an [iunlockput], which reads
             the ledger only. *)
          destruct (Hdl16 eq_refl) as (Hspend & Hatom & Hmem).
          (* the re-park's arithmetic: the append slot is inside the file *)
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
                              (dir_nrec (bv_unsigned (di_size dn))) + tot
                            <= 16 * dir_nrec (bv_unsigned (di_size dn)) + 16)%nat).
          { clear -Hk0le Htot16. lia. }
          assert (HzA : (Z.of_nat (16 * dir_slot data
                            (dir_nrec (bv_unsigned (di_size dn))) + tot)%nat
                         <= Z.of_nat (16 * dir_nrec
                              (bv_unsigned (di_size dn)) + 16)%nat)%Z)
            by (apply Nat2Z.inj_le; exact Hnatle).
          assert (HzB : Z.of_nat (16 * dir_nrec
                            (bv_unsigned (di_size dn)) + 16)%nat
                        = (Z.of_nat (16 * dir_nrec
                            (bv_unsigned (di_size dn)))%nat + 16)%Z)
            by (rewrite Nat2Z.inj_add; reflexivity).
          assert (Hoff32 : (Z.of_nat (16 * dir_slot data
                              (dir_nrec (bv_unsigned (di_size dn))) + tot)
                            < 2 ^ 32)%Z).
          { rewrite Hmb in Hszcap. change (2 ^ 32)%Z with 4294967296%Z.
            (* [lia] is quadratic-ish in how much of the context it has to
               scan for arithmetic atoms, and this is a syscall-altitude
               proof -- hundreds of unrelated hyps.  The four facts just
               built above are the whole chain; drop the rest first
               (durable-notes.md's "clear - H1 H2; lia" recipe). *)
            clear -Hnatle HzA HzB Hszcap Hnr1. lia. }
          assert (Hszmax : bv_unsigned (di_size dn')
                    = Z.max (bv_unsigned (di_size dn))
                        (Z.of_nat (16 * dir_slot data
                           (dir_nrec (bv_unsigned (di_size dn))) + tot)))
            by (rewrite Hdn'; exact (cr_wi_size_max dn bm' _ tot Hoff32)).
          assert (Hty' : di_type dn' = di_type dn) by (rewrite Hdn'; reflexivity).
          assert (Hnl' : di_nlink dn' = di_nlink dn)
            by (rewrite Hdn'; reflexivity).
          (* the branchless a0, which is what the [bltz] at +0xdc reads *)
          destruct Hbl as [[Ha0z Ht16] | [Ha0m Htlt]].
          -- (* ======================================================== *)
             (*  ARM C-OK-FILE: all sixteen bytes went in                 *)
             (* ======================================================== *)
             (* THE PARENT'S INODE BLOCK IS LOGGED ON THIS ARM, and that is
                what buys [cru := true] at the [iunlockput(dp)] below: the
                append went in whole, so [dl16_post]'s membership trio fires
                (it is guarded on [0 < tot], and the FAIL arms are exactly
                the ones that cannot have it).  With [cru] the put's spend is
                its bitmap report alone, and [cr_alloc_ip4]'s FOUR then
                leaves [iput_units] behind it -- the floor create's
                [ok = true] post now owes. *)
             assert (Ht0lt : (0 < tot)%nat) by (clear -Ht16; lia).
             assert (Hmemu : IBLOCK dind icfg_ist ∈ Sb')
               by exact (proj1 (proj2 (Hmem Ht0lt))).
             assert (Hcruu : true = true -> IBLOCK dind icfg_ist ∈ Sb')
               by (intros _; exact Hmemu).
             (* ===== +0xdc bltz a0 : FALLS THROUGH ================== *)
             iApply (wp_blt_x0_fall_s_sconf (mword_of_int (CK + 0xdc))
                       (mword_of_int 106 : mword 13) Ra0 mdl (K - 10)%nat b
                       ltac:(nz)
                       ltac:(rgne; rewrite Ha0z; exact cr_bltz_zero)
                       with "Hcg Hpc []").
             { iApply (cri_0dc with "Htext"). }
             iIntros (CIDD1 HqD1) "Hcg Hpc".
             assert (Hq0e0 : add_vec_int (mword_of_int (CK + 0xdc) : mword 64) 4
                             = mword_of_int (CK + 0xe0)) by pcw.
             iEval (rewrite Hq0e0) in "Hpc".
             (* THE PARENT'S RE-PARK (durable-disk 2b-inode-5): the unit the
                [ip->nlink = 1] flush minted goes in at the NAME the
                appended record now carries. *)
             (* the two facts the marker set owes at this append: the name
                is not an entry yet (so it is not marked), and it is not a
                dot name ([DirView.dir_dots_miss_not_dots]). *)
             destruct (dir_dots_miss_not_dots (bv_unsigned dind) dn data
                         (bname 14 nf)
                         ltac:(rewrite Htydir; vm_compute; reflexivity)
                         (cr_nl0z dn Hnl0) Hddix Hnone) as [Hnfd Hnfdd].
             assert (Hnfd' : bname 14 nf <> DOT)
               by (rewrite FsStateEra.DOT_dot; exact Hnfd).
             assert (Hnfdd' : bname 14 nf <> DOTDOT)
               by (rewrite FsStateEra.DOTDOT_dotdot; exact Hnfdd).
             assert (HsD : bname 14 nf ∉ D).
             { intros Hin. destruct (Hdok0 _ Hin) as ([tt Htt] & _ & _).
               rewrite (dir_entries_era_node dn bm data Hholes Hszcap)
                 (bool_decide_eq_true_2 _ Hdz)
                 (proj2 (dir_view_lookup_None data _ (bname 14 nf)) Hnone)
                 in Htt. discriminate. }
             iDestruct (ent_toks_dirlink_arm (fs_gamma_L fsc_fs) (bv_unsigned dind)
                          dn dn' bm bm' data data'
                          (cr_low16 cinum) (bname 14 nf)
                          (dir_nrec (bv_unsigned (di_size dn)))
                          (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                          tot D false eq_refl eq_refl Hatom
                          (bname_length_le 14 nf) (cut_nul_nonul _)
                          Hdz Hty' Hnl' Hszmax Hrng Hnone
                          Hholes Hholes' Hszcap (Hcapp Hszcap) HsD Hnfdd'
                          with "Hetk [Htoken]") as "Hetk".
             { iEval (rewrite -Hcl16) in "Htoken".
               rewrite (cr_delta_file ty Htdir) FsStateLink.link_reps_1.
               iApply (ent_tok_of_link (fs_gamma_L fsc_fs) (bv_unsigned dind)
                         (fn_dd (era_node dn bm data))
                         (fn_orphan (era_node dn bm data)) false
                         (bname 14 nf) (bv_unsigned (cr_low16 cinum))
                         (cr_ity ty (bv_unsigned dind))
                         ltac:(apply FsStateInode.ent_ty_ok_name;
                               [exact Hnfd' | exact Hnfdd' |
                                exact (cr_ity_file ty (bv_unsigned dind) Htdir)])
                         with "Htoken"). }
             assert (Hgrow := dir_entries_dirlink_grow dn dn' bm bm' data data'
                        (cr_low16 cinum) (bname 14 nf)
                        (dir_nrec (bv_unsigned (di_size dn)))
                        (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                        tot eq_refl eq_refl Hatom
                        (bname_length_le 14 nf) (cut_nul_nonul _)
                        Hdz Hty' Hszmax Hrng Hnone
                        Hholes Hholes' Hszcap (Hcapp Hszcap)).
             assert (Hisdir' : fn_is_dir (era_node dn' bm' data')
                               = fn_is_dir (era_node dn bm data))
               by (rewrite /fn_is_dir /fn_type !era_node_rec Hty' //).
             assert (Hnleq : fn_nlink (era_node dn' bm' data')
                             = fn_nlink (era_node dn bm data))
               by (rewrite /fn_nlink !era_node_rec Hnl' //).
             iDestruct (dlinks_intro _ _ _ _ _ D
                          ltac:(exact (FsStateInode.ent_dset_ok_grow _ _ D
                                         Hgrow Hdok0))
                          ltac:(exact (FsStateInode.node_exact_cong _ _ D
                                         Hisdir' Hnleq Hxact0))
                          with "Hetk") as "Hdlnk".
             assert (Hiok' : inode_ok fsc_cov fsc_logst dn' bm' data').
             { rewrite /inode_ok. split_and!.
               - exact Hwf'.
               - exact Hcov'.
               - exact Haddr'.
               - rewrite Hty'. exact (proj1 (proj2 (proj2 (proj2 Hiok)))).
               - exact (Hcapp Hszcap).
               - exact Hholes'.
               - exact (Hsizedp Hsized). }
             assert (Hdok' : dir_ok icfg_nib dn' data')
               by exact (dir_ok_dirlink icfg_nib dn dn' data data' (cr_low16 cinum)
                           (bname 14 nf) _ _ tot eq_refl eq_refl Htot16
                           Hcl16b Hty' Hszmax Hrng Hdok).
             (* ...and the dot records across the same write: the window is
                [dir_slot], which the clause's own liveness at 0 and 1 keeps
                away from both, and the count rides on [Hszmax]. *)
             assert (Hszle : bv_unsigned (di_size dn)
                             <= bv_unsigned (di_size dn'))
               by (clear -Hszmax; rewrite Hszmax; lia).
             assert (Hddix' : dir_dots_ix (bv_unsigned dind) dn' data')
               by exact (dir_dots_ix_dirlink (bv_unsigned dind) dn dn'
                           data data' (cr_low16 cinum) (bname 14 nf) _ _ tot
                           eq_refl eq_refl Htot16 Hty' Hnl' Hszle Hrng Hddix).
             (* ...and the UNIQUENESS clause across the same write: the
                atomicity ([Htot16], off dirlink's own relay) and the append
                guard [Hnone] are what pay for it. *)
             assert (Hduq' : dir_uniq dn' data')
               by exact (dir_uniq_dirlink dn dn' data data'
                           (cr_low16 cinum) (bname 14 nf) _ _ tot
                           eq_refl eq_refl Hatom
                           (bname_length_le 14 nf) (cut_nul_nonul _)
                           Hty' Hszmax Hrng Hnone Hduq).
             (* NOT [ic_mk_loaded]: [Hdiat]/[Hmeta] are stated at [dn0'], one
                rewrite short of the goal's [dn'], so the assembly stays
                inline here.  Only the tail -- [inode_addrs]/[ind_res]/
                [inode_blocks], the 268-element big-op -- is closed by name
                instead of [iFrame]. *)
             (* THE MOVER (namei-pinned-lookup.md §9 W3, dirlink's row) *)
             iApply fupd_wp.
             iModIntro.
             (* THE THREE RECORD-ONLY FACTS AT THE APPENDED PARENT
                (durable-disk 2b-inode-3): dirlink keeps the TYPE and the
                COUNT, and it grows the size to a MAX of two multiples of
                sixteen -- the old size (a directory's, by the incoming
                clause) and one whole record past a slot. *)
             assert (Hrl' : inode_rec_local dn').
             { apply (inode_rec_local_same_type dn dn' Hrl Hty').
               - rewrite Hnl'. exact (proj1 (proj2 Hrl)).
               - intros _. rewrite Hszmax. apply cr_max_div16.
                 + apply (proj2 (proj2 Hrl)).
                   rewrite Htydir. vm_compute. reflexivity.
                 + exists (Z.of_nat (dir_slot data
                             (dir_nrec (bv_unsigned (di_size dn)))) + 1)%Z.
                   rewrite Ht16 Nat2Z.inj_add Nat2Z.inj_mul. lia. }
             (* ...AND THE ERA'S ABSTRACT VALUE IS RETAGGED: dirlink MOVED
                the parent's record and its bytes, and
                [InodeRegion.ireg_top_retag_*] opens [ftopN] alone. *)
             iApply fupd_wp.
             (* THE RETAG OWES THE ROW (durable-disk lane A): an appended
                entry leaves the parent well-formed, and these are the four
                facts the re-pack below proves anyway. *)
             iMod (ireg_top_retag_auto ⊤ fsc_fs (bv_unsigned dind)
                     (era_node dn bm data) (era_node dn' bm' data')
                     ltac:(solve_ndisj) Logic.I
                     (inode_local_of_ok_rec (bv_unsigned dind) fsc_cov fsc_logst
                        dn' bm' data' Hiok' Hrl' Hduq' Hddix')
                     with "[] [] Htop") as "Htop";
               [iApply (ireg_inv_ftop with "Hiregi") | iApply (ireg_inv_app with "Hiregi") |].
             iModIntro.
             iAssert (ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kd dind dn' bm')
               with "[Hdlnk Hdiat Hmeta Hmap Hblocks Htop]"
               as "Hload".
             { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body. iExists data'.
               iSplitR; [iPureIntro; exact Hiok' |].
               iSplitR; [iPureIntro; exact Hrl' |].
               iSplitR; [iPureIntro;exact Hdok' |].
               iSplitR; [iPureIntro; exact Hddix' |].
               iSplitR; [iPureIntro;
                         exact (cr_doc_of_live dn dn' data' Hnl' Hnl0) |].
               iSplitR; [iPureIntro; exact Hduq' |].
               iSplitL "Hdlnk"; [iExact "Hdlnk" |].
               rewrite (Hdn0' eq_refl). iFrame "Hdiat Hmeta".
               iEval (rewrite /inode_map) in "Hmap".
               iDestruct "Hmap" as "[Haddrs Hind]".
               iSplitL "Haddrs"; [iExact "Haddrs" |].
               iSplitL "Hind"; [iExact "Hind" |].
               iSplitL "Hblocks"; [iExact "Hblocks" |].
               iExact "Htop". }
             (* ===== +0xe0 c.mv a0,s1 ============================== *)
             iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xe0)) Ra0 Rs1 mdl
                       (K - 10)%nat b ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc []").
             { iApply (cri_0e0 with "Htext"). }
             iIntros (CIDD2 HqD2) "Hcg Hpc". iEval (rgne) in "Hcg".
             pose (Y1 := <[Regidx Ra0 := regval_into_reg
                           (add_vec (zero_reg : mword 64)
                              (mdl !!! Regidx Rs1))]> mdl).
             change (<[Regidx Ra0 := regval_into_reg
                           (add_vec (zero_reg : mword 64)
                              (mdl !!! Regidx Rs1))]> mdl) with Y1.
             assert (HY1a0 : Y1 !!! Regidx Ra0 = ientry kd).
             { rewrite /Y1 upd_eq.
               destruct Hmdlregs as (_ & _ & Hd9 & _). rewrite Hd9.
               apply add_vec_zero_l. }
             assert (HY1regs : cr_regs3 m sp0 (ientry kd)
                       (mword_of_int 0 : mword 64) (ientry kslot)
                       ty major minor Y1)
               by (rewrite /Y1; apply cr_regs3_caller;
                   [exact Hcsa0 | exact Hmdlregs]).
             assert (Hq0e2 : add_vec_int (mword_of_int (CK + 0xe0) : mword 64) 2
                             = mword_of_int (CK + 0xe2)) by pcw.
             iEval (rewrite Hq0e2) in "Hpc".
             (* ===== +0xe2 jal iunlockput(dp) ====================== *)
             assert (Htgu2 : add_vec (mword_of_int (CK + 0xe2) : mword 64)
                       (sign_extend' 64 (mword_of_int 2090944 : mword 21))
                       = mword_of_int KernelSyms.iunlockput) by pcw.
             iApply (wp_jal_s_sconf (mword_of_int (CK + 0xe2)) Rra
                       (mword_of_int 2090944 : mword 21) Y1 (K - 10)%nat b
                       ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                       with "Hcg Hpc []").
             { iApply (cri_0e2 with "Htext"). }
             iIntros (CIDD3 HqD3) "Hcg Hpc".
             iEval (rewrite Htgu2) in "Hpc".
             pose (Y2 := <[Regidx Rra := regval_into_reg
                           (add_vec_int (mword_of_int (CK + 0xe2) : mword 64) 4)]> Y1).
             change (<[Regidx Rra := regval_into_reg
                           (add_vec_int (mword_of_int (CK + 0xe2) : mword 64) 4)]> Y1) with Y2.
             assert (HY2ra : Y2 !!! Regidx Rra
                             = add_vec_int (mword_of_int (CK + 0xe2) : mword 64) 4)
               by (rewrite /Y2; apply upd_eq).
             assert (HY2a0 : Y2 !!! Regidx Ra0 = ientry kd)
               by (rewrite /Y2 upd_ne; [exact HY1a0 | nz]).
             assert (HY2regs : cr_regs3 m sp0 (ientry kd)
                       (mword_of_int 0 : mword 64) (ientry kslot)
                       ty major minor Y2)
               by (rewrite /Y2; apply cr_regs3_caller;
                   [exact Hcsra | exact HY1regs]).
             assert (Hipn' : (iput_units <= n')%nat)
               by exact (cr_alloc_ip (S q2) n' _ _ _ _ _ ltac:(lia) Hspend).
             iDestruct (cpu_own_transport CIDdl CIDD3 0%nat eb (proc_addr j) b
                          ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
             (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
                goes in and the share it parked comes back in the post, so no
                bundleless out-state stands across the call. *)
             iDestruct (log_opS_named with "Hop") as (e0) "Hop".
             iDestruct (inode_ref_short_gen_forget _ _ _ _ _ _ _ _ Hled
                     with "Hfld Hkeep") as "Hkeep2".
             iAssert (ity_shot gd (di_type dn')) as "#Hshotl'".
             { rewrite Hty'. iExact "Hshotl". }
             iDestruct (off_rows_to_dep with "Hoffr") as "Hoffd".
             iApply (IUP.wp_iunlockput_dep_gen γs j γl pd pav pu
                       γil γisl
 kd (qd/2)%Qp (qd/2)%Qp gd lodc tldc (DepTx (qd/2)%Qp icfg_dev dind gd lodc t (1/4)%Qp) dind dn' bm'
                       n' Sb' false true false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
                       Y2 (K - 10)%nat eb b lks
                       U ltac:(exact HKiup) eq_refl Hkdlt ltac:(discriminate) Hcruu
                       Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib Hcovb
                       ltac:(exact Hipn') Hj Hgs HY2a0 ltac:(lkbelow) eq_refl
                       with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2
                             Hitbl Hescd Hiregi Hiopen Hslkd Hslkdd [//] Hfldc Hclaimscr Hdep Hoffd Hidev
                             Hiinum Hivalid Hload Hshotl' Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr
                             Hppid Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
             all: try lkbelow.
             { rewrite Heb /trap_csrs_ext. done. }
             { rewrite Heb /cpu_claim_ext. done. }
             { iEval (cbn beta iota). iEmpIntro. }
             iIntros (CIDU2 HqU2 mu2 n2 Sb2 wf2)
               "%Hcsu2 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
                %Hsb2 %Hwf2 %Hwf2c %Hn2 Hop Hisl2 Htp".
             assert (Hpcu2 : ret_pc (Y2 !!! Regidx Rra : mword 64)
                             = mword_of_int (CK + 0xe6)) by (rewrite HY2ra; pcw).
             iEval (rewrite Hpcu2) in "Hpc".
             assert (Hmu2regs : cr_regs3 m sp0 (ientry kd)
                       (mword_of_int 0 : mword 64) (ientry kslot)
                       ty major minor mu2)
               by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                           (ientry kslot) ty major minor Y2 mu2 Hcsu2 HY2regs).
             iDestruct ("Hppback" with "Hppid") as "Hpriv".
             (* ===== +0xe6 c.mv s2,s3 : the ANSWER ================= *)
             iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xe6)) Rs2 Rs3 mu2
                       (K - 10)%nat b ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc []").
             { iApply (cri_0e6 with "Htext"). }
             iIntros (CIDD4 HqD4) "Hcg Hpc". iEval (rgne) in "Hcg".
             assert (Hy2v : add_vec (zero_reg : mword 64) (mu2 !!! Regidx Rs3)
                            = ientry kslot).
             { destruct Hmu2regs as (_ & _ & _ & _ & Hd19 & _). rewrite Hd19.
               apply add_vec_zero_l. }
             pose (Y3 := <[Regidx Rs2 := regval_into_reg
                           (add_vec (zero_reg : mword 64)
                              (mu2 !!! Regidx Rs3))]> mu2).
             change (<[Regidx Rs2 := regval_into_reg
                           (add_vec (zero_reg : mword 64)
                              (mu2 !!! Regidx Rs3))]> mu2) with Y3.
             assert (HY3s2 : Y3 !!! Regidx Rs2 = ientry kslot)
               by (rewrite /Y3 upd_eq; exact Hy2v).
             assert (HY3regs : cr_regs3 m sp0 (ientry kd) (ientry kslot)
                       (ientry kslot) ty major minor Y3)
               by exact (cr_regs3_s2 m sp0 (ientry kd)
                           (mword_of_int 0 : mword 64) (ientry kslot)
                           (ientry kslot) ty major minor mu2 _ Hy2v Hmu2regs).
             assert (Hq0e8 : add_vec_int (mword_of_int (CK + 0xe6) : mword 64) 2
                             = mword_of_int (CK + 0xe8)) by pcw.
             iEval (rewrite Hq0e8) in "Hpc".
             (* ===== +0xe8 c.ldsp s3,40(sp) : the LAZY RESTORE ===== *)
             assert (HY3sp : Y3 !!! Regidx csp_rs1 = pa_stk sp0 10)
               by (destruct HY3regs as (H2 & _); exact H2).
             assert (HT5 : add_vec (Y3 !!! Regidx csp_rs1)
                             (zero_extend' 64
                                (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                           = pa_stk sp0 5) by (rewrite HY3sp; apply cr_frm5).
             iEval (rewrite -HT5) in "Hb5".
             iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0xe8))
                       (mword_of_int 5 : mword 6) Rs3 Y3 (K - 10)%nat
                       (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc [] Hb5").
             { iApply (cri_0e8 with "Htext"). }
             iIntros (CIDD5 HqD5) "Hcg Hpc Hb5".
             iEval (rewrite HT5) in "Hb5".
             pose (Y4 := <[Regidx Rs3 := regval_into_reg
                           (m !!! Regidx Rs3 : mword 64)]> Y3).
             change (<[Regidx Rs3 := regval_into_reg
                           (m !!! Regidx Rs3 : mword 64)]> Y3) with Y4.
             assert (HY4regs : cr_regs3 m sp0 (ientry kd) (ientry kslot)
                       (m !!! Regidx Rs3 : mword 64) ty major minor Y4)
               by exact (cr_regs3_s3 m sp0 (ientry kd) (ientry kslot)
                           (ientry kslot) (m !!! Regidx Rs3 : mword 64)
                           ty major minor Y3 _ eq_refl HY3regs).
             assert (HY4s2 : Y4 !!! Regidx Rs2 = ientry kslot)
               by (rewrite /Y4 upd_ne; [exact HY3s2 | nz]).
             assert (Hq0ea : add_vec_int (mword_of_int (CK + 0xe8) : mword 64) 2
                             = mword_of_int (CK + 0xea)) by pcw.
             iEval (rewrite Hq0ea) in "Hpc".
             (* ===== +0xea c.j +0x70 =============================== *)
             assert (Htg070c : add_vec (mword_of_int (CK + 0xea) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 1987 : mword 11) ('b"0"))))
                       = mword_of_int (CK + 0x70)) by pcw.
             iApply (wp_cj_s_sconf (mword_of_int (CK + 0xea))
                       (sign_extend' 21
                          (concat_vec (mword_of_int 1987 : mword 11) ('b"0")))
                       Y4 (K - 10)%nat b
                       ltac:(rewrite Htg070c; vm_compute; reflexivity)
                       with "Hcg Hpc []").
             { iApply (cri_0ea with "Htext"). }
             iIntros (CIDD6 HqD6). iApply bi.later_intro. iIntros "Hcg Hpc".
             iEval (rewrite Htg070c) in "Hpc".
             iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2")
               as (nfj) "Hnb16".
             iPoseProof ("Htail" $! CIDD6) as "Ht".
             iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
             iApply ("Ht" $! Y4 (m !!! Regidx Rs3 : mword 64) nfj with
                       "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
             { exact (cr_tregs_of_regs3 m sp0 (ientry kd) (ientry kslot)
                        ty major minor Y4 HY4regs). }
             iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
             iDestruct (cpu_own_transport CIDU2 CIDf 0%nat eb (proc_addr j) b
                          ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
             iDestruct (iref_slots_combine with "Hislk Hisl2") as "Hisl".
             iDestruct (iref_slots_combine with "Hisl Hislrr") as "Hisl".
             iDestruct "Hcdep" as (locg tlcg) "(%Hlecg & #Hflcg & Hcdep)".
             iApply fupd_wp.
             iMod (ic_grow_tx ⊤ fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kslot (q/2)%Qp icfg_dev cinum
                     g _ true t (1/2) (1/4) (1/4)
                     (eq_sym Qp.quarter_quarter) ltac:(solve_ndisj)
                     with "Hescc Hcivalid Hcdep Htp")
               as "(Hcivalid & Hcdep)".
             iModIntro.
             iDestruct (ic_tx_dep_intro with "Hcdep Htx") as "Hcdep".
             iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
             iApply ("Hcont" $! mf true true kslot (q/2)%Qp (q/2)%Qp g cinum
                       (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc
                       n2 Sb2 (1 + (1 + (ns - 3)))%nat
                       with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv
                             Hpath Hbsl [%] Hisl [%] Hop [Hslkc Hcslkd
                             Hcdep Hoffrc Hcidev Hciinum Hcivalid Hcdlnk Hcdiat Hcmeta
                             Hcmap Hcblocks Hctop Hcfrz Hckeep Hruc]").
             { exact Hcsf. }
             { exact (cr_slots_3 _ ns eq_refl Hns). }
             { split_and!.
               - exact (cr_sub3 _ _ _ _ Hsb1
                          (cr_sub2 _ _ _ (cr_sub_union_sing Sb1 _)
                             (cr_sub_union_sing _ _))
                          (cr_sub2 _ _ _ Hsb' Hsb2)).
               - pose proof (proj2 Hn2) as HB1. pose proof (proj2 Hn') as HB2.
                 (* optimization.md: [HB1]/[HB2] alone are not the whole
                    chain -- the goal [n2 <= u] needs the bridge from
                    [n' <= S q2] (HB2) back to [u] as well, which is
                    [Hn1u : S (S q2) <= u], threaded from the walk's own
                    budget call far above (found by a temporary
                    [idtac]-dump of the goal + full context at this site,
                    since the missing fact wasn't reachable by grepping
                    sibling call sites the way [dl_need]'s was). *)
                 clear -HB1 HB2 Hn1u. lia.
               - intros _.
                 exact (cr_fail_ip_left n' n2 wf2
                          (cr_alloc_ip4 (S q2) n' _ _ _ _ _ ltac:(lia) Hspend)
                          (proj1 Hn2)). }
             iSplitR.
             { iPureIntro. split; [rewrite Ha0f; exact HY4s2 |].
               split; [exact Hkslt |].
               split; [split; [exact (proj1 Hcpos) | exact Hcinb] |].
               split; [rewrite cr_setf_type; exact Htyc |].
               split; [reflexivity |].
               split; [reflexivity |].
               split; [rewrite cr_setf_nlink; vm_compute; reflexivity |].
               intros _. exact (cr_setf_fresh_made dnc ty major minor
                                  Hfresh Htyc). }
             (* the CHILD is not a directory on this arm, so its [dlinks]
                is [emp] at either dinode ([dlinks_not_dir]) and the
                flush's [nlink] bump is invisible to it. *)
             iAssert (dlinks fsc_fs (bv_unsigned cinum)
                        (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                        bmc datc)
               as "Hcdlnk1".
             { iApply (dlinks_not_dir fsc_fs (bv_unsigned cinum)
                         (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                         bmc datc).
               intros Hchdir. apply Htdirz.
               rewrite -(cr_setf_type dnc major minor
                           (mword_of_int 1 : mword 16)).
               exact Hchdir. }
             iDestruct "Hcmap" as "[Hca Hci]".
             iDestruct (ic_mk_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kslot cinum
                          (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                          bmc datc
                          (cr_setf_inode_ok fsc_cov fsc_logst dnc bmc datc major minor
                             _ Hciok)
                          (cr_setf_rec_local dnc major minor
                             (mword_of_int 1 : mword 16) Hrl_datc
                             cr_nl_short_1)
                          (cr_setf_dir_ok icfg_nib dnc datc major minor _ Hcdok)
                          (dir_dots_ix_not_dir (bv_unsigned cinum)
                             (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                             datc ltac:(rewrite cr_setf_type; exact Htdirz))
                          (dir_orphan_clean_not_dir
                             (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                             datc ltac:(rewrite cr_setf_type; exact Htdirz))
                          (dir_uniq_not_dir
                             (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                             datc ltac:(rewrite cr_setf_type; exact Htdirz))
                          with "Hcdlnk1 Hcdiat Hcmeta Hca Hci Hcblocks Hctop")
               as "Hcload".
             iAssert (ity_shot g (di_type (cr_setf dnc major minor
                                             (mword_of_int 1 : mword 16))))
               as "Hcshot1".
             { rewrite cr_setf_type. iExact "Hcshot". }
             iApply (create_locked_mk
 _ _ _ _ _ _ _ _ gil gisl eq_refl
                       with "Hslkc Hcslkd [Hcdep] Hoffrc Hcidev Hciinum
                             Hcivalid Hcload Hcshot1 Hcfrz [Hckeep] Hruc").
             { iExists locg, tlcg. iSplitR; [iPureIntro; exact Hlecg|].
               iFrame "Hflcg Hcdep". }
             { iExists loC, tlC. iSplitR; [iPureIntro; exact HleC|].
               iSplitR; [iExact "HflC"|]. iFrame "Hckeep". }
          -- (* ======================================================== *)
             (*  ARM FAIL's non-directory entry: the append fell short    *)
             (* ======================================================== *)
             iApply (wp_blt_x0_taken_s_sconf (mword_of_int (CK + 0xdc))
                       (mword_of_int 106 : mword 13) Ra0 mdl (K - 10)%nat b
                       ltac:(nz)
                       ltac:(rgne; rewrite Ha0m; exact cr_bltz_m1)
                       ltac:(rewrite Htg146; vm_compute; reflexivity)
                       with "Hcg Hpc []").
             { iApply (cri_0dc with "Htext"). }
             iIntros (CIDE1 HqE1). iApply bi.later_intro. iIntros "Hcg Hpc".
             iEval (rewrite Htg146) in "Hpc".
             iDestruct (cpu_own_transport CIDdl CIDE1 0%nat eb (proc_addr j) b
                          ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
             (* THE FAILING APPEND'S TWO ROUTES, and ONE figure prices both.
                [tot < 16] admits zero (writei's own -1 return, the full
                directory), and since the [dl16_post] collapse the spend
                clause is unguarded, so this is the SAME reading the C-OK
                branch above makes -- no [tot]-split, no constant.
                [CreateBudget.cr_fail_closes_with_credit] is the theorem. *)
             assert (Hipn'' : (iput_units <= n')%nat)
               by exact (cr_alloc_ip (S q2) n' _ _ _ _ _ ltac:(lia) Hspend).
             (* dirlink's slot is NET ZERO, so the ledger is back at [ns - 2]
                -- the figure the parked fail arm is stated at. *)
             iDestruct (iref_slots_combine with "Hislk Hislrr") as "Hislr".
             iEval (rewrite Hns2) in "Hislr".
             (* THE MOVER (namei-pinned-lookup.md §9 W3, dirlink's row): the
                append moved the parent's bytes even on the failing return,
                and [cr_fail_body] is stated at the POST record. *)
             iApply fupd_wp.
             iModIntro.
             (* THE ERA'S ABSTRACT VALUE IS NOT MOVED HERE (durable-disk
                lane A): the retag owes the registry's row, and the failing
                append's post record is proved well-formed inside
                [cr_fail_half] -- which is where the move now happens. *)
             (* nothing was written, so the tokens ride and the [+0xc4]
                mint's unit travels on to the fail arm's [ip->nlink = 0]
                (durable-disk 2b-inode-5). *)
             iDestruct (dlinks_intro _ _ _ _ _ D Hdok0 Hxact0
                          with "Hetk") as "Hdlnk".

             iSpecialize ("Hfl" $! kd qd gd γil γisl dind dn bm data nf nsl t).
             iPoseProof ("Hfl" $! CIDE1) as "Hf".
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
             iApply ("Hf" $! mdl kslot q g gil gisl loC tlC cinum dnc bmc datc
                       bm' data' dn' dn0' tot n' Sb'
                       with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                             [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                             [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                             Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                             Hnb14 Hnb2 Hslkd Hslkdd Hdep Hoffr Hidev Hiinum
                             Hivalid Hdlnk Hdiat Hmeta Hmap Hblocks Htop Hshotl
                             Hfrzl Hkeep Hrud Hslkc Hcslkd Hcdep Hoffrc Hcidev
                             Hciinum Hcivalid Hcdlnk Hcdiat Hcmeta Hcmap
                             Hcblocks Hctop Hcshot Hcfrz [%] [] Hckeep Hruc Htoken Hsbn Hsbi Hsbs Hsbb Hbmr
                             Hppid Hppback Hpath Hbsl Hislr Hop Htx Hcont").
             { exact Hmdlregs. }
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
             { exact Hfresh. }
             { exact Hrl_datc. }
             { exact Htyc. }
             { exact Hciok. }
             {exact Hcdok. }
             (* [tot < 16] AND dirlink's atomicity IS [tot = 0]: the shape
                the fail body's re-park needs. *)
             { destruct Hatom as [Hz | H16];
                 [exact Hz | exfalso; clear -H16 Htlt; lia]. }
             { exact Hwf'. }
             { exact Hholes'. }
             { exact Haddr'. }
             { exact Hsz31'. }
             { exact Hcov'. }
             { exact (Hcapp Hszcap). }
             { exact (Hsizedp Hsized). }
             { exact Hdn'. }
             { exact (Hdn0' eq_refl). }
             { exact Hrng. }
             { exact (cr_sub2 _ _ _
                        (cr_sub2 _ _ _ Hsb1
                           (cr_sub2 _ _ _ (cr_sub_union_sing Sb1 _)
                              (cr_sub_union_sing _ _))) Hsb'). }
             { exact (Hsb' _ (cr_in_union_sing _ _)). }
             { split; [exact Hipn'' |].
               (* optimization.md: same bridge as the sibling bullet in
                  [cr_found_half] above -- [HB2 : n' <= S q2] needs
                  [Hn1u : S (S q2) <= u] to reach the goal [n' <= u]. *)
               pose proof (proj2 Hn') as HB2.
               clear -HB2 Hn1u. lia. }
             (* the LEFT disjunct, and this entry has it unconditionally:
                eight into the dirlink and [wi16_spend <= 4] out. *)
             { left.
               exact (cr_alloc_ip4 (S q2) n' _ _ _ _ _ ltac:(lia) Hspend). }
             { exact HleC. }
             { iExact "HflC". }
    - (* ============================================================== *)
      (*  ARM A-FAIL (+0xec): ialloc returned 0, nothing was claimed     *)
      (* ============================================================== *)
      iDestruct "Hres" as "(%Hs3z & Hpc & Hislg & Htp & Htcl & Hop)".
      (* the claim box's quarter is home, unspent (durable-disk C-5) *)
      iDestruct (log_tx_join_q icfg_log t (1/2) (1/4) (1/4)
                   (eq_sym Qp.quarter_quarter) with "Htcl Htx") as "Htx".

      (* nothing was claimed, so no second lock was taken: the quarter goes
         straight back into the parent's arm (durable-disk B''-tx3). *)
      iApply fupd_wp.
      iMod (ic_grow_tx ⊤ fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kd (qd/2)%Qp icfg_dev dind gd _ true
              t (1/2) (1/4) (1/4) (eq_sym Qp.quarter_quarter)
              ltac:(solve_ndisj) with "Hescd Hivalid Hdep Htp")
        as "(Hivalid & Hdep)".
      iModIntro.
      assert (HMoregs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (mword_of_int 0 : mword 64) ty major minor Mo)
        by exact (cr_regs3_of_span m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (mword_of_int 0 : mword 64) ty major minor Ma Mo Hcs3 Hs3z
                    HAregs).
      (* ===== +0xec c.mv a0,s1 ====================================== *)
      iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xec)) Ra0 Rs1 Mo
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cri_0ec with "Htext"). }
      iIntros (CIDF1 HqF1) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (Z1 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Mo !!! Regidx Rs1))]> Mo).
      change (<[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Mo !!! Regidx Rs1))]> Mo) with Z1.
      assert (HZ1a0 : Z1 !!! Regidx Ra0 = ientry kd).
      { rewrite /Z1 upd_eq.
        destruct HMoregs as (_ & _ & Hd9 & _). rewrite Hd9.
        apply add_vec_zero_l. }
      assert (HZ1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (mword_of_int 0 : mword 64) ty major minor Z1)
        by (rewrite /Z1; apply cr_regs3_caller; [exact Hcsa0 | exact HMoregs]).
      assert (Hq0ee : add_vec_int (mword_of_int (CK + 0xec) : mword 64) 2
                      = mword_of_int (CK + 0xee)) by pcw.
      iEval (rewrite Hq0ee) in "Hpc".
      (* ===== +0xee jal iunlockput(dp), UNCREDITED =================== *)
      assert (Htgu : add_vec (mword_of_int (CK + 0xee) : mword 64)
                (sign_extend' 64 (mword_of_int 2090932 : mword 21))
                = mword_of_int KernelSyms.iunlockput) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (CK + 0xee)) Rra
                (mword_of_int 2090932 : mword 21) Z1 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_0ee with "Htext"). }
      iIntros (CIDF2 HqF2) "Hcg Hpc".
      iEval (rewrite Htgu) in "Hpc".
      pose (Z2 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0xee) : mword 64) 4)]> Z1).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0xee) : mword 64) 4)]> Z1) with Z2.
      assert (HZ2ra : Z2 !!! Regidx Rra
                      = add_vec_int (mword_of_int (CK + 0xee) : mword 64) 4)
        by (rewrite /Z2; apply upd_eq).
      assert (HZ2a0 : Z2 !!! Regidx Ra0 = ientry kd)
        by (rewrite /Z2 upd_ne; [exact HZ1a0 | nz]).
      assert (HZ2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (mword_of_int 0 : mword 64) ty major minor Z2)
        by (rewrite /Z2; apply cr_regs3_caller; [exact Hcsra | exact HZ1regs]).
      iEval (rewrite /inode_map) in "Hmap".
      iDestruct "Hmap" as "[Haddrs Hind]".
      assert (Hdok2 : dir_ok icfg_nib dn data) by (exact Hdok).
      pose proof Hddix as Hddix2.
      iDestruct (ic_mk_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kd dind dn bm data
                   Hiok Hrl Hdok2 Hddix2 (cr_doc_of_live dn dn data eq_refl Hnl0)
                   Hduq
                   with "Hdlnk Hdiat Hmeta Haddrs Hind Hblocks Htop")
        as "Hload".
      iDestruct (cpu_own_transport CIDo CIDF2 0%nat eb (proc_addr j) b
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
                kd (qd/2)%Qp (qd/2)%Qp gd lodc tldc (DepTx (qd/2)%Qp icfg_dev dind gd lodc t (1/2)%Qp) dind dn bm (S q1) Sb1
                false false false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
                Z2 (K - 10)%nat eb b lks
                U ltac:(exact HKiup) eq_refl Hkdlt ltac:(discriminate) ltac:(discriminate)
                Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib Hcovb
                ltac:(exact Hn1ip) Hj Hgs HZ2a0 ltac:(lkbelow) eq_refl
                with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                      Hescd Hiregi Hiopen Hslkd Hslkdd [//] Hfldc Hclaimscr Hdep Hoffd Hidev Hiinum
                      Hivalid Hload Hshotl Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr Hppid
                      Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
      all: try lkbelow.
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { iEval (cbn beta iota). iEmpIntro. }
      iIntros (CIDU HqU mu n2 Sb2 wf)
        "%Hcsu Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
         %Hsb2 %Hwf %Hwfc %Hn2 Hop Hisl Htp".
      iDestruct (log_tx_add icfg_log t 1 (1/2) (1/2)
                   (eq_sym Qp.half_half) with "Htp Htx") as "Htw".
      iDestruct (log_tx_full with "Htw") as "Htx".

      assert (Hpcu : ret_pc (Z2 !!! Regidx Rra : mword 64)
                     = mword_of_int (CK + 0xf2)) by (rewrite HZ2ra; pcw).
      iEval (rewrite Hpcu) in "Hpc".
      assert (Hmuregs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (mword_of_int 0 : mword 64) ty major minor mu)
        by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (mword_of_int 0 : mword 64) ty major minor Z2 mu Hcsu
                    HZ2regs).
      iDestruct ("Hppback" with "Hppid") as "Hpriv".
      (* ===== +0xf2 c.mv s2,s3 (s3 = 0) ============================= *)
      iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xf2)) Rs2 Rs3 mu
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cri_0f2 with "Htext"). }
      iIntros (CIDF3 HqF3) "Hcg Hpc". iEval (rgne) in "Hcg".
      assert (Hz2v : add_vec (zero_reg : mword 64) (mu !!! Regidx Rs3)
                     = (mword_of_int 0 : mword 64)).
      { destruct Hmuregs as (_ & _ & _ & _ & Hd19 & _). rewrite Hd19.
        apply add_vec_zero_l. }
      pose (Z3 := <[Regidx Rs2 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (mu !!! Regidx Rs3))]> mu).
      change (<[Regidx Rs2 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (mu !!! Regidx Rs3))]> mu) with Z3.
      assert (HZ3s2 : Z3 !!! Regidx Rs2 = (mword_of_int 0 : mword 64))
        by (rewrite /Z3 upd_eq; exact Hz2v).
      assert (HZ3regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (mword_of_int 0 : mword 64) ty major minor Z3)
        by exact (cr_regs3_s2 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (mword_of_int 0 : mword 64) (mword_of_int 0 : mword 64)
                    ty major minor mu _ Hz2v Hmuregs).
      assert (Hq0f4 : add_vec_int (mword_of_int (CK + 0xf2) : mword 64) 2
                      = mword_of_int (CK + 0xf4)) by pcw.
      iEval (rewrite Hq0f4) in "Hpc".
      (* ===== +0xf4 c.ldsp s3,40(sp) ================================ *)
      assert (HZ3sp : Z3 !!! Regidx csp_rs1 = pa_stk sp0 10)
        by (destruct HZ3regs as (H2 & _); exact H2).
      assert (HT5 : add_vec (Z3 !!! Regidx csp_rs1)
                      (zero_extend' 64
                         (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                    = pa_stk sp0 5) by (rewrite HZ3sp; apply cr_frm5).
      iEval (rewrite -HT5) in "Hb5".
      iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0xf4))
                (mword_of_int 5 : mword 6) Rs3 Z3 (K - 10)%nat
                (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc [] Hb5").
      { iApply (cri_0f4 with "Htext"). }
      iIntros (CIDF4 HqF4) "Hcg Hpc Hb5".
      iEval (rewrite HT5) in "Hb5".
      pose (Z4 := <[Regidx Rs3 := regval_into_reg
                    (m !!! Regidx Rs3 : mword 64)]> Z3).
      change (<[Regidx Rs3 := regval_into_reg
                    (m !!! Regidx Rs3 : mword 64)]> Z3) with Z4.
      assert (HZ4regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (m !!! Regidx Rs3 : mword 64) ty major minor Z4)
        by exact (cr_regs3_s3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (mword_of_int 0 : mword 64) (m !!! Regidx Rs3 : mword 64)
                    ty major minor Z3 _ eq_refl HZ3regs).
      assert (HZ4s2 : Z4 !!! Regidx Rs2 = (mword_of_int 0 : mword 64))
        by (rewrite /Z4 upd_ne; [exact HZ3s2 | nz]).
      assert (Hq0f6 : add_vec_int (mword_of_int (CK + 0xf4) : mword 64) 2
                      = mword_of_int (CK + 0xf6)) by pcw.
      iEval (rewrite Hq0f6) in "Hpc".
      (* ===== +0xf6 c.j +0x70 ======================================= *)
      assert (Htg070a : add_vec (mword_of_int (CK + 0xf6) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 1981 : mword 11) ('b"0"))))
                = mword_of_int (CK + 0x70)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (CK + 0xf6))
                (sign_extend' 21
                   (concat_vec (mword_of_int 1981 : mword 11) ('b"0")))
                Z4 (K - 10)%nat b
                ltac:(rewrite Htg070a; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_0f6 with "Htext"). }
      iIntros (CIDF5 HqF5). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htg070a) in "Hpc".
      iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2") as (nfj) "Hnb16".
      iPoseProof ("Htail" $! CIDF5) as "Ht".
      iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
      iApply ("Ht" $! Z4 (m !!! Regidx Rs3 : mword 64) nfj with
                "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
      { exact (cr_tregs_of_regs3 m sp0 (ientry kd)
                 (mword_of_int 0 : mword 64) ty major minor Z4 HZ4regs). }
      iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
      iDestruct (cpu_own_transport CIDU CIDf 0%nat eb (proc_addr j) b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (iref_slots_combine with "Hislg Hisl") as "Hisl".
      iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
                (mword_of_int 0 : mword 32) dn bm n2 Sb2
                (1 + (1 + (ns - 2)))%nat
                with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv Hpath
                      Hbsl [%] Hisl [%] Hop [$Htx]").
      { exact Hcsf. }
      { exact (cr_slots_2 _ ns eq_refl Hns). }
      { split_and!; [exact (cr_sub2 _ _ _ Hsb1 Hsb2)
                    | exact (cr_le2 _ _ _ (proj2 Hn2) (proj2 Hnp1))
                    | discriminate]. }
      { iPureIntro. rewrite Ha0f. exact HZ4s2. }
  Qed.

End ProofCreateAlloc.

End CreateAlloc.
