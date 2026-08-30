(* ProofSysOpenAUEntryC.v -- sys_open's O_CREATE ARM at the ARMED post:
   +0x38 .. +0x48 and ARM A-FAIL, with the T_FILE create-AU carry
   ([SpecCreateAUF.CREATE_AUF]) in place of the landed create, and the join
   at +0x4a entered through [ProofSysOpenAUCreArm]'s SHIM.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the open AU
   prover), create arm.  A PARALLEL block beside [ProofSysOpen.so_entry_c]
   -- R10: the landed contract, its proof, and every AU block below the
   join stay exactly where they are.  ARM A-FAIL is
   [ProofSysOpenTails.so_tail_a] VERBATIM (it moves no fs-abstract state)
   and the abstract payout there is [SpecCreateAUFOpen.cauf_fail_to_open],
   which is the WHOLE failure fold in one wand.

   ==== WHAT THIS BLOCK OWES, AND WHERE IT PAYS ========================

     c.li a3,0 ; c.li a2,0 ; c.li a1,2 ; addi a0,s0,-176 ;
     jal create ; c.mv s1,a0 ; c.beqz a0 -> +0xd2

   ITEM 1 (create form): the carry is [CreateAUF.wp_create_auf] and the
   walk one-shot the contract hands down is [mknod_walk_pre_era], which is
   create's [FsAbsStart.ep_start] at the fetched string by
   [FsAbsNparMknod.np_start_of_mknod] -- a rename, no proof.

   ITEM 2 (the terminal fire) SPLITS ON [made], and that is the arm's
   whole abstract content:

     made = false (ARM F-OK, the name was there).  [SpecSysOpenAU]'s
       EXISTS-OPENS arms want the observation FIRED at the found node, so
       it fires here, off the payload's own [top_frag]
       ([FsAbsOpenFire.opf_open_fire_1], the walk block's instant read at
       the create arm's own lock hold).
     made = true (ARM C-OK, a fresh child).  Every FRESH arm of the
       contract -- the success one and the -1 fold's (a) -- REFUNDS both
       the observation and the trunc commit ([delta_trunc_nil]: the child
       is [AFile []]).  So NOTHING fires: the two commits ride inside the
       shim residue and the plain tail runs at a PURE row receipt.

   ITEM 7 (the F-OK bridge) is the shim's refutation premise: a found
   [ADir] is ARM F-BAD and never reaches here, so [di_type dn] is T_FILE
   or T_DEVICE and the abstract row is an [AFile] or an [ADev]
   ([opf_era_file_row] / [opf_era_dev_row]) -- which is what kills the
   plain tail's DIRECTORY arm on the way out.

   BINDERS: [ProofSysOpenAUJoin]'s list verbatim. *)
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
Require Import WpSconfAlu WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
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
Require Import ProofSysOpenParts.
Require Import ProofSysOpenTails.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.

Require Import DirentEnc.        (* [bview]                                 *)
Require Import FsTree.
Require Import FsBytesGamma.
Require Import SpecSysOpenAU.
Require Import FsAbsEraMknod.
Require Import FsAbsNparMknod.   (* [np_start_of_mknod]                     *)
Require Import FsAbsMknodFire.
Require Import FsAbsOpenFire.
Require Import ProofSysOpenAUParts.
Require Import ProofSysOpenAUJoin.
Require Import SpecCreateAUF.     (* the T_FILE create-AU carry            *)
Require Import SpecCreateAUFOpen. (* [cauf_fail_to_open]                   *)
Require Import ProofSysOpenAUCreArm.
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

(* ===================================================================== *)
(*  THE SYSCALL'S EXIT CONTINUATION AT THE *CREATE* ARMS                  *)
(* ===================================================================== *)

Section ProofSysOpenAUEntryCCont.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  (* [ProofSysOpenAUParts.so_cont0_au] with [open_arms_plain] replaced by
     [open_arms_create] -- and that is the ONLY difference. *)
  Definition so_cont0_au_create `{GEN : GenId}
      (gf : gname)
      (ns : nat) (dqb dqs dqbs dqn : dfrac)
      (pj : mword 64) (pidv : mword 32) (vom : mword 64) (U : ustate)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Phiok Phiex : aview -> Z -> fname -> Z -> iProp Σ)
      (Phio : aview -> Z -> anode -> iProp Σ)
      (Phit : aview -> Z -> list (bv 8) -> iProp Σ)
      (m : regfile) (K : nat) (eb b : bool) (lks : gset string)
      : CpuId -> iProp Σ :=
    fun (CIDx : CpuId) =>
      (∀ (mf : regfile) (ns' : nat),
         ⌜callee_saved m mf⌝ -∗
         ⌜ns' = ns⌝ -∗
         sie_cap_gpr KT1 mf K b pj -∗
         cpu_own 0 eb pj b lks -∗
         trap_csrs_ext KT1 eb -∗
         cpu_claim_ext eb pj -∗
         pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
         sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
         sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
         sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
         sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
         bslots 3 -∗
         iref_slots ns' -∗
         open_arms_create (fs_gamma_L fsc_fs) fsc_fs gf pj pidv vom
           P Pmiss Phiok Phiex Phio Phit U (mf !!! Regidx Ra0 : mword 64) -∗
         WP (Loop : expr riscv_lang))%I.

End ProofSysOpenAUEntryCCont.

Module SysOpenAUEntryC (CreateAUF : CREATE_AUF) (Iunlock : IUNLOCK)
                       (Iunlockput : IUNLOCKPUT) (EndOp : END_OP)
                       (Fileclose : FILECLOSE) (Itrunc : ITRUNC)
                       (Filealloc : FILEALLOC) (Fdalloc : FDALLOC).

Module Join := SysOpenAUJoin Iunlock Iunlockput EndOp Fileclose Itrunc
                             Filealloc Fdalloc.
Module Tails := SysOpenTails Iunlock Iunlockput EndOp Fileclose.

Section ProofSysOpenAUEntryC.
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

  Lemma so_entry_c_au `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gfl gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (plen : nat) (bp : nat -> bv 8)
      (om lo : mword 32) (ns : nat) (Sb : gset Z)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (U : ustate)
      (m N : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w4 w5 w6 w24 : mword 64)
      (* ---- the AU side ---- *)
      (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Phiok Phiex : aview -> Z -> fname -> Z -> iProp Σ)
      (Phio : aview -> Z -> anode -> iProp Σ)
      (Phit : aview -> Z -> list (bv 8) -> iProp Σ) :
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
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0x38)) -∗
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
    log_tx icfg_log -∗
    bslots 3 -∗
    iref_slots ns -∗
    fd_slot -∗
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
    (* ---- THE AU BUNDLE (the contract's O_CREATE side, verbatim) ---- *)
    mknod_walk_pre_era fsc_fs P Pmiss -∗
    acre_commit_at (fs_gamma_L fsc_fs) ∅ (AFile []) Phiok -∗
    dlookup_commit_at (fs_gamma_L fsc_fs) ∅ Phiex -∗
    aopen_commit_at (fs_gamma_L fsc_fs) ∅ Phio -∗
    atrunc_commit_at (fs_gamma_L fsc_fs) ∅ Phit -∗
    wp_next true (proc_addr jx)
      (so_cont0_au_create gf ns
                dqb dqs dqbs dqn (proc_addr jx) pidv vom U
                P Pmiss Phiok Phiex Phio Phit m K eb b lks) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK HdevR Hnib0 Hgeom Hsize Hbm0 Hbmcov
           Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hpcstr Hplen Hni1 Hni2 Hni3 Hush
           Hprkc Hnsb Hj Hgl Heb Hlkempty Hom Hal23 Hsp0 HNsp HNthr HNs0 HNs2 HNs3
           Hal.
    pose proof HK as HKfull.
    destruct (so_kb K HK) as (HKcr & HKna & HKai & HKas & HKbo & HKeo & HKil &
                              HKiu & HKit & HKip & HKup & HKfc & HKfa & HKfd &
                              HK10 & HK24 & Kpop).
    iIntros "Hcg Hown Htce Hcce #Htext #Hdata Hpc #Hpre #Hftab #Hbio
              #Hlog Hseam Hgen #Hkenv #Hitab #Hitinv #Hescrows #Hslks #Hireg
              #Hropen
              Hsbn Hsbi Hsbs Hsbb #Hbmres Hpriv #Hprocs #Hdev #Hgeo #Hdlk HopS Htx
              Hbsl Hisl Hfds Hfrag Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23lo H23hi H24
              Hwp Hac Hdl Hoc Htc Hcont".
    iPoseProof (printk_env_panic with "Hpre") as "#Hpe".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0x38 c.li a3,0 -- minor ===== *)
    iApply (wp_cli_s_sconf (CID := CID0) (mword_of_int (SO + 0x38)) Ra3
              (mword_of_int 0 : mword 6)
              (sign_extend' 64 (mword_of_int 0 : mword 16)) N (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (soi_038 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (N1 := <[Regidx Ra3 := regval_into_reg
                  (sign_extend' 64 (mword_of_int 0 : mword 16))]> N).
    assert (HN1a3 : (N1 !!! Regidx Ra3 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N1; apply upd_eq).
    assert (Hpp38 : add_vec_int (mword_of_int (SO + 0x38) : mword 64) 2
                    = mword_of_int (SO + 0x3a)) by pcw.
    iEval (rewrite Hpp38) in "Hpc".
    (* ===== +0x3a c.li a2,0 -- major ===== *)
    iApply (wp_cli_s_sconf (CID := CID1) (mword_of_int (SO + 0x3a)) Ra2
              (mword_of_int 0 : mword 6)
              (sign_extend' 64 (mword_of_int 0 : mword 16)) N1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (soi_03a with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (N2 := <[Regidx Ra2 := regval_into_reg
                  (sign_extend' 64 (mword_of_int 0 : mword 16))]> N1).
    assert (HN2a2 : (N2 !!! Regidx Ra2 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N2; apply upd_eq).
    assert (HN2a3 : (N2 !!! Regidx Ra3 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N2 upd_ne; [exact HN1a3 | nz]).
    assert (Hpp3a : add_vec_int (mword_of_int (SO + 0x3a) : mword 64) 2
                    = mword_of_int (SO + 0x3c)) by pcw.
    iEval (rewrite Hpp3a) in "Hpc".
    (* ===== +0x3c c.li a1,2 -- T_FILE ===== *)
    iApply (wp_cli_s_sconf (CID := CID2) (mword_of_int (SO + 0x3c)) Ra1
              (mword_of_int 2 : mword 6)
              (sign_extend' 64 (SpecCreate.T_FILE : mword 16)) N2 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (soi_03c with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (N3 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (SpecCreate.T_FILE : mword 16))]> N2).
    assert (HN3a1 : (N3 !!! Regidx Ra1 : mword 64)
                    = (sign_extend' 64 (SpecCreate.T_FILE : mword 16)))
      by (rewrite /N3; apply upd_eq).
    assert (HN3a2 : (N3 !!! Regidx Ra2 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N3 upd_ne; [exact HN2a2 | nz]).
    assert (HN3a3 : (N3 !!! Regidx Ra3 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N3 upd_ne; [exact HN2a3 | nz]).
    assert (HN3s0 : (N3 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite /N1 upd_ne; [| nz]. exact HNs0. }
    assert (Hpp3c : add_vec_int (mword_of_int (SO + 0x3c) : mword 64) 2
                    = mword_of_int (SO + 0x3e)) by pcw.
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== +0x3e addi a0,s0,-176 -- the path buffer ===== *)
    iApply (wp_addi4_s_sconf (CID := CID3) (mword_of_int (SO + 0x3e)) Ra0 Rs0
              (mword_of_int 3920 : mword 12) N3 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_03e with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (N4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (N3 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3920 : mword 12)))]> N3).
    assert (HN4a0 : (N4 !!! Regidx Ra0 : mword 64) = pa_stk sp0 22).
    { etransitivity; [ rewrite /N4; apply upd_eq |].
      rewrite HN3s0. apply so_bufpath. }
    assert (HN4a1 : (N4 !!! Regidx Ra1 : mword 64)
                    = (sign_extend' 64 (SpecCreate.T_FILE : mword 16)))
      by (rewrite /N4 upd_ne; [exact HN3a1 | nz]).
    assert (HN4a2 : (N4 !!! Regidx Ra2 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N4 upd_ne; [exact HN3a2 | nz]).
    assert (HN4a3 : (N4 !!! Regidx Ra3 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N4 upd_ne; [exact HN3a3 | nz]).
    assert (Hpp3e : add_vec_int (mword_of_int (SO + 0x3e) : mword 64) 4
                    = mword_of_int (SO + 0x42)) by pcw.
    iEval (rewrite Hpp3e) in "Hpc".
    (* ===== +0x42 jal ra,create ===== *)
    iApply (wp_jal_s_sconf (CID := CID4) (mword_of_int (SO + 0x42)) Rra
              (mword_of_int 2095708 : mword 21) N4 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_042 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (N5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x42) : mword 64) 4)]> N4).
    assert (Hjcr : add_vec (mword_of_int (SO + 0x42) : mword 64)
                     (sign_extend' 64 (mword_of_int 2095708 : mword 21))
                   = mword_of_int KernelSyms.create) by pcw.
    iEval (rewrite Hjcr) in "Hpc".
    assert (HN5ra : (N5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x42) : mword 64) 4)
      by (rewrite /N5; apply upd_eq).
    assert (HN5a0 : (N5 !!! Regidx Ra0 : mword 64) = pa_stk sp0 22)
      by (rewrite /N5 upd_ne; [exact HN4a0 | nz]).
    assert (HN5a1 : (N5 !!! Regidx Ra1 : mword 64)
                    = (sign_extend' 64 (SpecCreate.T_FILE : mword 16)))
      by (rewrite /N5 upd_ne; [exact HN4a1 | nz]).
    assert (HN5a2 : (N5 !!! Regidx Ra2 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N5 upd_ne; [exact HN4a2 | nz]).
    assert (HN5a3 : (N5 !!! Regidx Ra3 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N5 upd_ne; [exact HN4a3 | nz]).
    assert (HN5sp : so_sp sp0 N5).
    { rewrite /so_sp /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz].
      rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite /N1 upd_ne; [| nz]. exact HNsp. }
    assert (HN5s0 : (N5 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz]. exact HN3s0. }
    assert (HN5s2 : (N5 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz].
      rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite /N1 upd_ne; [| nz]. exact HNs2. }
    assert (HN5s3 : (N5 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz].
      rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite /N1 upd_ne; [| nz]. exact HNs3. }
    assert (HN5thr : so_thr m N5).
    { intros c Hc N2b N8 N9 N18 N19.
      rewrite /N5 upd_ne; [| regne]. rewrite /N4 upd_ne; [| regne].
      rewrite /N3 upd_ne; [| regne]. rewrite /N2 upd_ne; [| regne].
      rewrite /N1 upd_ne; [| regne].
      exact (HNthr c Hc N2b N8 N9 N18 N19). }
    iDestruct (so_buf_split (pa_stk sp0 22) bp plen Hplen with "HbP")
      as "[Hbufk Hbufrest]".
    iDestruct (cpu_own_transport CID0 CID5 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (CreateAUF.wp_create_auf (CID := CID5) gs jx gl pd pav pu
              gf plen bp
              SpecCreate.T_FILE (mword_of_int 0) (mword_of_int 0)
              (upd_usM U _) MAXOPBLOCKS Sb ns pidv dqb dqs dqbs dqn
              N5 (K - 24)%nat eb b lks
              P Pmiss Phiok Phiex
              HKcr HdevR Hnib0 Hgeom Hsize Hbm0 Hbmcov
              Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hpcstr
              ltac:(assert (E31 : (2 ^ 31 = 2147483648)%Z)
                      by (vm_compute; reflexivity); lia)
              Hni1 Hni2 Hni3 Hush
              eq_refl Hprkc
              ltac:(unfold create_units; lia) Hnsb Hj Hgl
              HN5a1 HN5a2 HN5a3 Heb
              with "Hcg Hown Htext Hpc Hdata Hpre Hbio Hlog Hkenv Hitab
                    Hitinv Hescrows Hslks Hireg Hropen Hsbn Hsbi Hsbs Hsbb
                    Hbmres
                    Hpriv [Hbufk] Hprocs Hdev Hgeo Hdlk Hbsl Hisl HopS Htx
                    [Hwp] Hac Hdl").
    { iEval (rewrite HN5a0). iExact "Hbufk". }
    { iApply (np_start_of_mknod with "Hwp"). }
    iIntros (CID6 Hq6 mcr ok made kk qi ss gy inum dn bm u1 Sb1 ns1)
      "%Hcscr Hcg Hown Hpc Hsbn Hsbi Hsbs Hsbb Hpriv Hbufk Hbsl
       %Hns1 Hisl %Hu1 HopS Hok".
    iEval (rewrite HN5a0) in "Hbufk".
    assert (Hpccr : ret_pc (N5 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0x46)) by (rewrite HN5ra; pcw).
    iEval (rewrite Hpccr) in "Hpc".
    (* the buffer, joined and renamed: nothing below reads it *)
    iDestruct (so_buf_join (pa_stk sp0 22) bp plen Hplen with "Hbufk Hbufrest")
      as "HbA".
    iDestruct (so_bytes_name (pa_stk sp0 22) 128 with "HbA") as (bp1) "HbP".
    assert (Hcrsp : so_sp sp0 mcr).
    { rewrite /so_sp (callee_saved_lookup Hcscr csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HN5sp. }
    assert (Hcrs0 : (mcr !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcscr Rs0 ltac:(vm_compute; reflexivity)).
      exact HN5s0. }
    assert (Hcrs2 : (mcr !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcscr Rs2 ltac:(vm_compute; reflexivity)).
      exact HN5s2. }
    assert (Hcrs3 : (mcr !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcscr Rs3 ltac:(vm_compute; reflexivity)).
      exact HN5s3. }
    assert (Hcrthr : so_thr m mcr).
    { intros c Hc N2b N8 N9 N18 N19. rewrite (callee_saved_lookup Hcscr c Hc).
      exact (HN5thr c Hc N2b N8 N9 N18 N19). }
    (* ===== +0x46 c.mv s1,a0 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID6) (mword_of_int (SO + 0x46)) Rs1 Ra0
              mcr (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_046 with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (P1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec zero_reg (mcr !!! Regidx Ra0))]> mcr).
    assert (HP1s1 : (P1 !!! Regidx Rs1 : mword 64) = (mcr !!! Regidx Ra0 : mword 64)).
    { etransitivity; [ rewrite /P1; apply upd_eq |]. apply add_vec_zero_l. }
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mcr !!! Regidx Ra0 : mword 64))
      by (rewrite /P1 upd_ne; [reflexivity | nz]).
    assert (HP1sp : so_sp sp0 P1)
      by (rewrite /so_sp /P1 upd_ne; [exact Hcrsp | nz]).
    assert (HP1s0 : (P1 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /P1 upd_ne; [exact Hcrs0 | nz]).
    assert (HP1s2 : (P1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P1 upd_ne; [exact Hcrs2 | nz]).
    assert (HP1s3 : (P1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P1 upd_ne; [exact Hcrs3 | nz]).
    assert (HP1thr : so_thr m P1).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (Hcrthr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp46 : add_vec_int (mword_of_int (SO + 0x46) : mword 64) 2
                    = mword_of_int (SO + 0x48)) by pcw.
    iEval (rewrite Hpp46) in "Hpc".
    (* ===== +0x48 c.beqz a0, +0xd2  [ARM A-FAIL] ===== *)
    destruct ok.
    2:{ (* ---- create refused: NOTHING of open's own fired, and
             [cauf_fail_to_open] is the whole fold in one wand ---- *)
      iDestruct "Hok" as "(%Hcra0 & Htx & Hcf)".
      iApply (wp_cbeqz_taken_s_sconf (CID := CID7) (mword_of_int (SO + 0x48))
                (mword_of_int 69 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                P1 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HP1a0 Hcra0; exact so_eqz_zero)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_048 with "Htext"). }
      iIntros (CID8 Hq8). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg48 : add_vec (mword_of_int (SO + 0x48) : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13 (concat_vec (mword_of_int 69 : mword 8) ('b"0"))))
                      = mword_of_int (SO + 0xd2)) by pcw.
      iEval (rewrite Htg48) in "Hpc".
      iDestruct (so_omode_join sp0 lo om Hal23 with "H23lo H23hi") as "H23".
      iDestruct (proc_priv_bare_acc with "Hpriv") as "[Hpbare Hpback]".
      iDestruct (cpu_own_transport CID6 CID8 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (log_opS_op with "HopS Htx") as "Hop".
      iApply (Tails.so_tail_a (CID0 := CID8) gs jx gl pd pav pu
                u1 pidv (DfracOwn (1/4)) m P1 sp0 K eb b
                lks w4 w5 w6 (word_of_words lo om) w24 bp1 U
                HKeo HK24 Kpop Hgeom Hj Hgl Hlkempty Hsp0 HP1sp HP1thr HP1s2
                HP1s3 Hal
                with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                      Hpbare Hprocs Hdev Hgeo Hdlk Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
                      HbP H23 H24 [Hpback Hfds Hfrag Hisl Hsbn Hsbi Hsbs Hsbb
                      Hbsl Hcf Hoc Htc Hcont]").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc
                                           Hpbare".
      iDestruct ("Hpback" with "Hpbare") as "Hpriv".
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf ns1 with "[%] [%] Hcg Hown Htce Hcce Hpc
                Hsbn Hsbi Hsbs Hsbb Hbsl Hisl [Hpriv Hfds Hfrag Hcf Hoc Htc]").
      { exact Hcsf. }
      { cbn in Hns1. unfold sys_open_slots, create_slots in *. lia. }
      { rewrite /open_arms_create. iFrame "Hfds". iLeft.
        iSplitR; [iPureIntro; exact Ha0f |]. iFrame "Hpriv Hfrag".
        iApply (cauf_fail_to_open with "Hcf Hoc Htc"). } }
    (* ---- create SUCCEEDED: the locked inode, straight to the join ---- *)
    iDestruct "Hok" as "(%Hokf & Hlocked & Hcauf)".
    destruct Hokf as (Hcra0 & Hkk & Hinum & Hrep).
    assert (Hipnz : ientry kk <> (zero_reg : mword 64))
      by (apply ientry_ne_zero; lia).
    (* THE WITNESS, free on this arm: create ran at T_FILE, so the record
       it reports is never a directory. *)
    assert (Htyne : di_type dn <> (mword_of_int 1 : mword 16)).
    { destruct made.
      - rewrite Hrep create_made_type. unfold SpecCreate.T_FILE.
        intro Hc. apply (f_equal bv_unsigned) in Hc. by vm_compute in Hc.
      - destruct Hrep as [Hty | Hty]; rewrite Hty;
          [unfold SpecCreate.T_FILE | unfold SpecCreate.T_DEVICE];
          intro Hc; apply (f_equal bv_unsigned) in Hc; by vm_compute in Hc. }
    assert (Hdirw : bv_unsigned (di_type dn) = T_DIR_z ->
                    om = (mword_of_int 0 : mword 32)).
    { intro Hc. exfalso. exact (so_tdir_zne (di_type dn) Htyne Hc). }
    destruct (Hiregb inum ltac:(lia)) as [Hibcov Hiblog].
    iDestruct (so_esc_acc kk ltac:(lia) with "Hescrows") as "#Hesc".
    iDestruct "Hlocked" as (gil gisl)
      "(Hslk & Hslkd & Hdep & Hidev & Hiinum & Hivalid & Hload &
        Hshot & Hfrz & Href & Hru)".
    iApply (wp_cbeqz_fall_s_sconf (CID := CID7) (mword_of_int (SO + 0x48))
              (mword_of_int 69 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              P1 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HP1a0 Hcra0;
                    apply (proj2 (eq_vec_false_iff _ _)); exact Hipnz)
              with "Hcg Hpc []").
    { iApply (soi_048 with "Htext"). }
    iIntros (CID8 Hq8) "Hcg Hpc".
    assert (Hpp48 : add_vec_int (mword_of_int (SO + 0x48) : mword 64) 2
                    = mword_of_int (SO + 0x4a)) by pcw.
    iEval (rewrite Hpp48) in "Hpc".
    assert (HP1s1i : (P1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite HP1s1; exact Hcra0).
    iDestruct (log_opS_opb with "HopS") as "Hop".
    iDestruct (cpu_own_transport CID6 CID8 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    (* THE PAYLOAD, PEELED (ProofSysOpenAUParts, WHY THE PAYLOAD IS
       THREADED PEELED): the join and everything below it wants [so_flat],
       and on the EXISTS arm the fire below reads this same [data]. *)
    iDestruct (so_flat_open with "Hload") as (data) "Hflat".
    destruct made.
    - (* ============ ARM C-OK: a FRESH child ==========================
         The contract REFUNDS both of open's commits here, so neither
         fires: they ride the shim residue and the plain tail runs at a
         pure row receipt. *)
      assert (Htyf : bv_unsigned (di_type dn) = FsImg.T_FILE_z).
      { rewrite Hrep create_made_type. vm_compute. reflexivity. }
      assert (Harow : abs_of (era_node dn bm data)
                      = MkAnode (AFile (fn_file_bytes (era_node dn bm data)))
                                (fn_nlink (era_node dn bm data)))
        by exact (opf_era_file_row dn bm data Htyf).
      iAssert (socr_fresh P Phiok Phiex Phio Phit (bview plen bp)
                 (bv_unsigned inum))
        with "[Hcauf Hoc Htc]" as "HR".
      { rewrite /socr_fresh.
        iDestruct (cauf_ok_fresh with "Hcauf") as (d nm av ents nl)
          "(%Hl & %Hpre & HP & HPhi & Hdl)".
        iExists d, nm, av, ents, nl.
        iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
        iSplitR; [iPureIntro; lia |]. iFrame "HP HPhi Hdl Hoc Htc". }
      iAssert (so_obs (socr_Phio_pure (bv_unsigned inum)
                         (MkAnode (AFile (fn_file_bytes (era_node dn bm data)))
                                  (fn_nlink (era_node dn bm data))))
                      (bv_unsigned inum) (era_node dn bm data)) as "Hobs".
      { rewrite -Harow. iApply socr_obs_pure. }
      iAssert (wp_next true (proc_addr jx)
                 (so_cont_au gf ns1 dqb dqs (proc_addr jx) pidv vom U
                    (socr_P (socr_fresh P Phiok Phiex Phio Phit
                               (bview plen bp) (bv_unsigned inum))
                            (bv_unsigned inum))
                    (socr_Pm (socr_fresh P Phiok Phiex Phio Phit
                                (bview plen bp) (bv_unsigned inum)))
                    (socr_Phio_pure (bv_unsigned inum)
                       (MkAnode (AFile (fn_file_bytes (era_node dn bm data)))
                                (fn_nlink (era_node dn bm data))))
                    socr_Phit_triv m K eb b lks))
        with "[Hcont Hsbn Hsbs]" as "Hcontj".
      { iEval (rewrite /wp_next). iIntros (CIDz) "%Hqz".
        iEval (rewrite /so_cont_au). iIntros (mf ns2) "%Hcsf %Hns2".
        iIntros "Hcg Hown Htce Hcce Hpc Hsbb Hsbi Hbsl Hisl Hpost".
        iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
        iApply fupd_wp.
        iMod (socr_arms_fresh gf (proc_addr jx) pidv vom P Pmiss
                Phiok Phiex Phio Phit U _ (bview plen bp) (bv_unsigned inum)
                (fn_file_bytes (era_node dn bm data))
                (fn_nlink (era_node dn bm data)) with "Hpost") as "Hpost".
        iModIntro.
        iApply ("Hcont" $! mf ns2 with "[%] [%] Hcg Hown Htce Hcce Hpc
                  Hsbn Hsbi Hsbs Hsbb Hbsl Hisl Hpost").
        { exact Hcsf. }
        { cbn in Hns1. unfold sys_open_slots, create_slots in *. lia. } }
      iApply (Join.so_join_au (CID0 := CID8) gfl gf gs jx gl pd pav pu
                gil gisl kk qi ss gy inum dn bm om lo ns1 u1 pidv dqb dqs
                U m P1 sp0 K eb b lks w4 w5 w6 w24 bp1
                data vom (bview plen bp)
                (socr_P (socr_fresh P Phiok Phiex Phio Phit
                           (bview plen bp) (bv_unsigned inum))
                        (bv_unsigned inum))
                (socr_Pm (socr_fresh P Phiok Phiex Phio Phit
                            (bview plen bp) (bv_unsigned inum)))
                (socr_Phio_pure (bv_unsigned inum)
                   (MkAnode (AFile (fn_file_bytes (era_node dn bm data)))
                            (fn_nlink (era_node dn bm data))))
                socr_Phit_triv
                HKfull Hkk ltac:(exact (proj2 Hinum)) Hgeom Hsize Hbm0 Hbmcov Hbmlog
                Hist0 Hibcov Hiblog Hcovb
                ltac:(exact (proj2 (proj2 Hu1) eq_refl)) Hj Hgl Hlkempty
                Hdirw Hom Hal23 Hsp0 HP1sp HP1thr HP1s0 HP1s1i HP1s2 HP1s3
                Hal ltac:(cbn in Hns1; unfold sys_open_slots, create_slots in *; lia)
                with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hftab Hbio Hlog
                      Hseam Hgen Hitab Hitinv Hesc Hireg Hropen Hslk Hslkd Hdep
                      Hidev Hiinum Hivalid Hflat Hshot Hfrz Href Hru Hpriv Hprocs
                      Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hfrag Hf1
                      Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23lo H23hi H24
                      [HR] Hobs [] Hcontj").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { rewrite /socr_P. iSplitR; [by iPureIntro |]. iExact "HR". }
      { iApply atrunc_commit_at_unit. }
    - (* ============ ARM F-OK: the name was there =====================
         The contract wants the terminal observation FIRED at the found
         node, so it fires here, off the payload's own [top_frag]. *)
      assert (Hnd : forall (ents : gmap fname Z) (nl : nat),
                      abs_of (era_node dn bm data) <> MkAnode (ADir ents) nl).
      { destruct Hrep as [Hty | Hty].
        - rewrite (opf_era_file_row dn bm data
                     ltac:(rewrite Hty; vm_compute; reflexivity)).
          intros ents nl Hc. inversion Hc.
        - rewrite (opf_era_dev_row dn bm data
                     ltac:(rewrite Hty; vm_compute; discriminate)
                     ltac:(rewrite Hty; vm_compute; discriminate)).
          intros ents nl Hc. inversion Hc. }
      iDestruct (so_flat_top with "Hflat") as "[Htop Hflatb]".
      iApply fupd_wp.
      iMod (opf_open_fire_1 fsc_fs ⊤ Phio (bv_unsigned inum)
              (era_node dn bm data) ltac:(solve_ndisj) with "[] Hoc Htop")
        as "[Htop Hobs0]";
        [iApply (ireg_inv_ftop with "Hireg") |].
      iModIntro.
      iDestruct ("Hflatb" with "Htop") as "Hflat".
      iDestruct (socr_obs_tag (bv_unsigned inum) (era_node dn bm data) Phio
                   with "Hobs0") as "Hobs".
      iAssert (socr_exists P Phiok Phiex (bview plen bp) (bv_unsigned inum))
        with "[Hcauf]" as "HR".
      { rewrite /socr_exists.
        iDestruct (cauf_ok_exists with "Hcauf") as (d nm av ents nl)
          "(%Hl & %Hrow & %Hent & HP & HPhi & Hac)".
        iExists d, nm, av, ents, nl.
        iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
        iSplitR; [by iPureIntro |]. iFrame "HP HPhi Hac". }
      iAssert (wp_next true (proc_addr jx)
                 (so_cont_au gf ns1 dqb dqs (proc_addr jx) pidv vom U
                    (socr_P (socr_exists P Phiok Phiex (bview plen bp)
                               (bv_unsigned inum)) (bv_unsigned inum))
                    (socr_Pm (socr_exists P Phiok Phiex (bview plen bp)
                                (bv_unsigned inum)))
                    (socr_Phio_tag (bv_unsigned inum)
                       (abs_of (era_node dn bm data)) Phio)
                    Phit m K eb b lks))
        with "[Hcont Hsbn Hsbs]" as "Hcontj".
      { iEval (rewrite /wp_next). iIntros (CIDz) "%Hqz".
        iEval (rewrite /so_cont_au). iIntros (mf ns2) "%Hcsf %Hns2".
        iIntros "Hcg Hown Htce Hcce Hpc Hsbb Hsbi Hbsl Hisl Hpost".
        iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
        iApply fupd_wp.
        iMod (socr_arms_exists gf (proc_addr jx) pidv vom P Pmiss
                Phiok Phiex Phio Phit U _ (bview plen bp) (bv_unsigned inum)
                (abs_of (era_node dn bm data)) Hnd with "Hpost") as "Hpost".
        iModIntro.
        iApply ("Hcont" $! mf ns2 with "[%] [%] Hcg Hown Htce Hcce Hpc
                  Hsbn Hsbi Hsbs Hsbb Hbsl Hisl Hpost").
        { exact Hcsf. }
        { cbn in Hns1. unfold sys_open_slots, create_slots in *. lia. } }
      iApply (Join.so_join_au (CID0 := CID8) gfl gf gs jx gl pd pav pu
                gil gisl kk qi ss gy inum dn bm om lo ns1 u1 pidv dqb dqs
                U m P1 sp0 K eb b lks w4 w5 w6 w24 bp1
                data vom (bview plen bp)
                (socr_P (socr_exists P Phiok Phiex (bview plen bp)
                           (bv_unsigned inum)) (bv_unsigned inum))
                (socr_Pm (socr_exists P Phiok Phiex (bview plen bp)
                            (bv_unsigned inum)))
                (socr_Phio_tag (bv_unsigned inum)
                   (abs_of (era_node dn bm data)) Phio)
                Phit
                HKfull Hkk ltac:(exact (proj2 Hinum)) Hgeom Hsize Hbm0 Hbmcov Hbmlog
                Hist0 Hibcov Hiblog Hcovb
                ltac:(exact (proj2 (proj2 Hu1) eq_refl)) Hj Hgl Hlkempty
                Hdirw Hom Hal23 Hsp0 HP1sp HP1thr HP1s0 HP1s1i HP1s2 HP1s3
                Hal ltac:(cbn in Hns1; unfold sys_open_slots, create_slots in *; lia)
                with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hftab Hbio Hlog
                      Hseam Hgen Hitab Hitinv Hesc Hireg Hropen Hslk Hslkd Hdep
                      Hidev Hiinum Hivalid Hflat Hshot Hfrz Href Hru Hpriv Hprocs
                      Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hfrag Hf1
                      Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23lo H23hi H24
                      [HR] Hobs Htc Hcontj").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { rewrite /socr_P. iSplitR; [by iPureIntro |]. iExact "HR". }
  Qed.

End ProofSysOpenAUEntryC.

End SysOpenAUEntryC.
