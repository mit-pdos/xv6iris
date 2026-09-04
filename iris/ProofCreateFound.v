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
Require Import StackOwn.
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
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import DinodeEnc.
(* [trunc16_sext64]: an [sh] of a register an [lh] filled is the identity on
   the halfword -- the three metadata stores at +0xb4 / +0xb8 are exactly
   that, at the ABI's sign-extended [major] / [minor] arguments. *)
Require Import DirView.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecPrintk.
Require Import SpecIput SpecIalloc.
Require Import SpecIlock SpecIunlockput.
Require Import SpecDirlookup.
Require Import SpecNameiparent.
Require Import SpecCreate.
(* THE FRESH-TYPE SPAN: the four instructions +0xa4..+0xb0 that pin
   [di_type dn = ty] across [ialloc]/[ilock].  It is a stretch of create's
   OWN body rather than a callee, so it is NOT a functor argument -- the
   statement ([create_fresh_ty_body], spliced verbatim below), the span's
   register contract ([cr_cs_but_s3]) and the proof all live in
   [ProofCreateFreshTy.v], and this file applies [create_fresh_ty] directly,
   handing it [IA]/[IL] for its two callee hypotheses. *)
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
(*  ProofCreateFound.v -- create's Found half. *)
(*                                                                      *)
(*  Split out of ProofCreate.v FOR THE BUILD DAG: create's five halves    *)
(*  take each other as PREMISES, not as callees, so only the             *)
(*  functor-free vocabulary in ProofCreateShared.v is shared and they     *)
(*  compile in parallel.                                                 *)
(* ==================================================================== *)

Require Import ProofCreateShared.

Module CreateFound (NP : NAMEIPARENT) (IL : ILOCK) (IUP : IUNLOCKPUT) (DL : DIRLOOKUP).

Section ProofCreateFound.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  Lemma cr_found_half
      (γs : list gname) (j : nat) (γl : gname)
      (pd pav pu : mword 64)
      (γf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (ty major minor : mword 16)
      (U : ustate)
      (u : nat) (Sb : gset Z)
      (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    (K_create <= K)%nat ->
    icfg_dev = ROOTDEV ->
    (0 < icfg_nib)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < fsc_size <= BPB ->
    0 <= fsc_bmapstart ->
    fsc_bmapstart ∈ fsc_cov ->
    ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
    0 <= icfg_ist ->
    cov_below fsc_cov fsc_size ->
    bitmap_geom_ok fsc_cov fsc_logst fsc_bmapstart fsc_size ->
    InodeInv.ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
    bb_cstr pfun plen ->
    (Z.of_nat plen < 2 ^ 31)%Z ->
    1 < fsc_ninodes ->
    fsc_ninodes <= 16 * Z.of_nat icfg_nib ->
    fsc_ninodes < 2 ^ 31 ->
    bv_unsigned ty <> 0 ->
    (* durable-disk 2b-inode-3: ialloc's claim box owes the region (L5) *)
    InodeRegion.ireg_ty_ok (ialloc_fresh ty) ->
    printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk ->
    (create_units <= u)%nat ->
    (create_slots <= ns)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    m !!! Regidx Ra1 = (sign_extend' 64 ty : mword 64) ->
    m !!! Regidx Ra2 = (sign_extend' 64 major : mword 64) ->
    m !!! Regidx Ra3 = (sign_extend' 64 minor : mword 64) ->
    eb = true ->
    sie_cap_gpr KT1 m K b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    kernel_text -∗ pc_is (mword_of_int KernelSyms.create) -∗
    kernel_data -∗
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
    sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
    bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
    proc_priv γf (proc_addr j) pidv U -∗
    ([∗ list] i ∈ seq 0 (S plen),
       pa_add (m !!! Regidx Ra0 : mword 64) i ↦ₘ[KT1] pfun i) -∗
    procs_inv γs -∗
    dev_inv fsc_uart fsc_disk -∗
    disk_geom fsc_disk pd pav pu -∗
    is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
    bslots 3 -∗
    iref_slots ns -∗
    log_opS icfg_log u Sb -∗
    (* the transaction token, for the child's suspended row inside
       (durable-disk lane A) *)
    log_tx icfg_log -∗
    (* ---- THE PARKED ALLOCATE HALF, as a HYPOTHESIS ---- *)
    wp_next true (proc_addr j) (fun CIDa : CpuId =>
      cr_alloc_body (CID := CID) γs j γl pd pav pu γf

                    plen pfun (m !!! Regidx Ra0 : mword 64)
                    ty major minor U u Sb ns pidv dqb dqs dqbs dqn m
                    (m !!! Regidx csp_rs1 : mword 64)
                    (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks CIDa) -∗
    (* ---- the contract's own continuation ---- *)
    wp_next true (proc_addr j) (fun CIDc : CpuId =>
      cr_cont_body γf
 plen pfun (m !!! Regidx Ra0 : mword 64)
                   ty major minor U u Sb ns pidv dqb dqs dqbs dqn m K eb b lks j
                   (ret_pc (m !!! Regidx Rra : mword 64)) CIDc) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hroot Hnib0 Hlg Hsize Hbms0 Hbmsc Hbmsl
           Hist0 Hcovb Hbmgeo Hiregb Hcstr Hplen31 Hni1 Hni2 Hni3 Htynz Htyk Hpkc
           Hu Hns Hj Hgs Ha1 Ha2 Ha3 Heb.
    destruct (cr_kb K HK)
      as (HK10 & HKnp & HKil & HKdlu & HKiup & HKia & HKiu & HKdlk & HKsum).
    iIntros "Hcg Hcnt #Htext Hpc #Hkd #Hpk #Hbio #Hlogc #Hkenv
             #Hitb2 #Hitbl #Hesc #Hslks #Hiregi #Hiopen
             Hsbn Hsbi Hsbs Hsbb #Hbmr Hpriv Hpath #Hprocs #Hdevi #Hgeom #Hdlk
             Hbsl Hislots Hop Htx Halloc Hcont".
    iPoseProof (printk_env_panic with "Hpk") as "#Hpenv".
    (* PIN THE INDEX: at level 0 [cpu_own_eb_agree] gives [eb = b], and the
       crossings below are the literal [true] (create parks everywhere). *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb). clear Hbm.
    (* THE HELD SET IS EMPTY, AND SAID SO ONCE.  create's contract carries no
       order premise because it does not need one: it is a level-0 contract,
       and [cpu_own_size_le] forces [lks = ∅] there.  Keep the EQUATION rather
       than substituting -- [lks] is spelled by name in every body below --
       and let [lkbelow] close each callee's bound from it. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : (m !!! Regidx csp_rs1 : mword 64) = sp0) by reflexivity.
    pose (ret_tgt := ret_pc (m !!! Regidx Rra : mword 64)).
    (* ===== +0x00 c.addi16sp sp,-80 : the 10-slot frame ================ *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10)
      by apply cr_push.
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KernelSyms.create)
              (mword_of_int 59 : mword 6) m K 10 b
              ltac:(exact HK10) Hpush with "Hcg Hpc []").
    { iApply (cri_000 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    pose (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /R1 upd_eq; exact Hpush).
    assert (HR1o : forall c : mword 5, c <> csp_rs1 ->
                     R1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc. rewrite /R1 upd_ne;
        [reflexivity
        | intro Hq; apply Hc;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as
      "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (u3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    iDestruct "S5" as (u5) "Hb5". iDestruct "S6" as (u6) "Hb6".
    iDestruct "S7" as (u7) "Hb7". iDestruct "S8" as (u8) "Hb8".
    iDestruct "S9" as (u9) "Hb9". iDestruct "S10" as (u10) "Hb10".
    assert (Hf1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HR1sp; apply cr_frm1).
    assert (Hf2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HR1sp; apply cr_frm2).
    assert (Hf3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HR1sp; apply cr_frm3).
    assert (Hf4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HR1sp; apply cr_frm4).
    assert (Hf6 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (rewrite HR1sp; apply cr_frm6).
    assert (Hf7 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (rewrite HR1sp; apply cr_frm7).
    assert (Hf8 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (rewrite HR1sp; apply cr_frm8).
    iEval (rewrite -Hf1) in "Hb1". iEval (rewrite -Hf2) in "Hb2".
    iEval (rewrite -Hf3) in "Hb3". iEval (rewrite -Hf4) in "Hb4".
    iEval (rewrite -Hf6) in "Hb6". iEval (rewrite -Hf7) in "Hb7".
    iEval (rewrite -Hf8) in "Hb8".
    assert (Hp002 : add_vec_int (mword_of_int KernelSyms.create : mword 64) 2
                    = mword_of_int (CK + 0x02)) by pcw.
    iEval (rewrite Hp002) in "Hpc".
    (* ===== +0x02 .. +0x0e : the SEVEN saves (slot 40 is NOT touched) == *)
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x02)) (mword_of_int 9 : mword 6)
              Rra R1 (K - 10)%nat u1 b with "Hcg Hpc [] Hb1").
    { iApply (cri_002 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc Hb1".
    iEval (rgne; rewrite (HR1o Rra ltac:(nz)) Hf1) in "Hb1".
    assert (Hp004 : add_vec_int (mword_of_int (CK + 0x02) : mword 64) 2
                    = mword_of_int (CK + 0x04)) by pcw.
    iEval (rewrite Hp004) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x04)) (mword_of_int 8 : mword 6)
              Rs0 R1 (K - 10)%nat u2 b with "Hcg Hpc [] Hb2").
    { iApply (cri_004 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc Hb2".
    iEval (rgne; rewrite (HR1o Rs0 ltac:(nz)) Hf2) in "Hb2".
    assert (Hp006 : add_vec_int (mword_of_int (CK + 0x04) : mword 64) 2
                    = mword_of_int (CK + 0x06)) by pcw.
    iEval (rewrite Hp006) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x06)) (mword_of_int 7 : mword 6)
              Rs1 R1 (K - 10)%nat u3 b with "Hcg Hpc [] Hb3").
    { iApply (cri_006 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc Hb3".
    iEval (rgne; rewrite (HR1o Rs1 ltac:(nz)) Hf3) in "Hb3".
    assert (Hp008 : add_vec_int (mword_of_int (CK + 0x06) : mword 64) 2
                    = mword_of_int (CK + 0x08)) by pcw.
    iEval (rewrite Hp008) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x08)) (mword_of_int 6 : mword 6)
              Rs2 R1 (K - 10)%nat u4 b with "Hcg Hpc [] Hb4").
    { iApply (cri_008 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc Hb4".
    iEval (rgne; rewrite (HR1o Rs2 ltac:(nz)) Hf4) in "Hb4".
    assert (Hp00a : add_vec_int (mword_of_int (CK + 0x08) : mword 64) 2
                    = mword_of_int (CK + 0x0a)) by pcw.
    iEval (rewrite Hp00a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x0a)) (mword_of_int 4 : mword 6)
              Rs4 R1 (K - 10)%nat u6 b with "Hcg Hpc [] Hb6").
    { iApply (cri_00a with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc Hb6".
    iEval (rgne; rewrite (HR1o Rs4 ltac:(nz)) Hf6) in "Hb6".
    assert (Hp00c : add_vec_int (mword_of_int (CK + 0x0a) : mword 64) 2
                    = mword_of_int (CK + 0x0c)) by pcw.
    iEval (rewrite Hp00c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x0c)) (mword_of_int 3 : mword 6)
              Rs5 R1 (K - 10)%nat u7 b with "Hcg Hpc [] Hb7").
    { iApply (cri_00c with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc Hb7".
    iEval (rgne; rewrite (HR1o Rs5 ltac:(nz)) Hf7) in "Hb7".
    assert (Hp00e : add_vec_int (mword_of_int (CK + 0x0c) : mword 64) 2
                    = mword_of_int (CK + 0x0e)) by pcw.
    iEval (rewrite Hp00e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x0e)) (mword_of_int 2 : mword 6)
              Rs6 R1 (K - 10)%nat u8 b with "Hcg Hpc [] Hb8").
    { iApply (cri_00e with "Htext"). }
    iIntros (CID8 Hq8) "Hcg Hpc Hb8".
    iEval (rgne; rewrite (HR1o Rs6 ltac:(nz)) Hf8) in "Hb8".
    assert (Hp010 : add_vec_int (mword_of_int (CK + 0x0e) : mword 64) 2
                    = mword_of_int (CK + 0x10)) by pcw.
    iEval (rewrite Hp010) in "Hpc".
    (* ===== +0x10 c.addi4spn s0,sp,80 : the frame pointer ============== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (CK + 0x10))
              (Cregidx (mword_of_int 0)) (mword_of_int 20 : mword 8) Rs0
              R1 (K - 10)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (cri_010 with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc".
    pose (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> R1).
    change (<[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> R1) with R2.
    assert (HR2s0 : R2 !!! Regidx Rs0 = sp0).
    { rewrite /R2 upd_eq. rewrite HR1sp. apply cr_fp. }
    assert (HR2sp : R2 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2o : forall c : mword 5, c <> csp_rs1 -> c <> Rs0 ->
                     R2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c N2 N8. rewrite /R2 upd_ne;
        [ exact (HR1o c N2)
        | intro Hq; apply N8;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    assert (Hp012 : add_vec_int (mword_of_int (CK + 0x10) : mword 64) 2
                    = mword_of_int (CK + 0x12)) by pcw.
    iEval (rewrite Hp012) in "Hpc".
    (* ===== +0x12 / +0x14 / +0x16 : ty / major / minor to s4 / s5 / s6 = *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x12)) Rs4 Ra1 R2 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_012 with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (R3 := <[Regidx Rs4 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R2 !!! Regidx Ra1))]> R2).
    change (<[Regidx Rs4 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R2 !!! Regidx Ra1))]> R2) with R3.
    assert (HR3s4 : R3 !!! Regidx Rs4 = (sign_extend' 64 ty : mword 64)).
    { rewrite /R3 upd_eq. rewrite (HR2o Ra1 ltac:(nz) ltac:(nz)) Ha1.
      apply add_vec_zero_l. }
    assert (Hp014 : add_vec_int (mword_of_int (CK + 0x12) : mword 64) 2
                    = mword_of_int (CK + 0x14)) by pcw.
    iEval (rewrite Hp014) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x14)) Rs5 Ra2 R3 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_014 with "Htext"). }
    iIntros (CID11 Hq11) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (R4 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R3 !!! Regidx Ra2))]> R3).
    change (<[Regidx Rs5 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R3 !!! Regidx Ra2))]> R3) with R4.
    assert (HR4s5 : R4 !!! Regidx Rs5 = (sign_extend' 64 major : mword 64)).
    { rewrite /R4 upd_eq. rewrite /R3 upd_ne; [| nz].
      rewrite (HR2o Ra2 ltac:(nz) ltac:(nz)) Ha2. apply add_vec_zero_l. }
    assert (Hp016 : add_vec_int (mword_of_int (CK + 0x14) : mword 64) 2
                    = mword_of_int (CK + 0x16)) by pcw.
    iEval (rewrite Hp016) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x16)) Rs6 Ra3 R4 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_016 with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (R5 := <[Regidx Rs6 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R4 !!! Regidx Ra3))]> R4).
    change (<[Regidx Rs6 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R4 !!! Regidx Ra3))]> R4) with R5.
    assert (HR5s6 : R5 !!! Regidx Rs6 = (sign_extend' 64 minor : mword 64)).
    { rewrite /R5 upd_eq. rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite (HR2o Ra3 ltac:(nz) ltac:(nz)) Ha3. apply add_vec_zero_l. }
    assert (HR5s0 : R5 !!! Regidx Rs0 = sp0).
    { rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [exact HR2s0 | nz]. }
    assert (Hp018 : add_vec_int (mword_of_int (CK + 0x16) : mword 64) 2
                    = mword_of_int (CK + 0x18)) by pcw.
    iEval (rewrite Hp018) in "Hpc".
    (* ===== +0x18 addi a1,s0,-80 : a1 = &name = the frame's bottom ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (CK + 0x18)) Ra1 Rs0
              (mword_of_int 4016 : mword 12) R5 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_018 with "Htext"). }
    iIntros (CID13 Hq13) "Hcg Hpc".
    pose (R6 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget R5 Rs0)
                     (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> R5).
    change (<[Regidx Ra1 := regval_into_reg
                  (add_vec (rget R5 Rs0)
                     (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> R5) with R6.
    assert (HR6a1 : R6 !!! Regidx Ra1 = pa_stk sp0 10).
    { rewrite /R6 upd_eq. rewrite rget_ne;
        [| intro Hq1'; injection Hq1' as Hq2'; vm_compute in Hq2'; congruence ].
      rewrite HR5s0. apply cr_name_addr. }
    assert (Hp01c : add_vec_int (mword_of_int (CK + 0x18) : mword 64) 4
                    = mword_of_int (CK + 0x1c)) by pcw.
    iEval (rewrite Hp01c) in "Hpc".
    (* ===== +0x1c jal nameiparent ===================================== *)
    assert (Htgnp : add_vec (mword_of_int (CK + 0x1c) : mword 64)
              (sign_extend' 64 (mword_of_int 2092760 : mword 21))
              = mword_of_int KernelSyms.nameiparent) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x1c)) Rra
              (mword_of_int 2092760 : mword 21) R6 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_01c with "Htext"). }
    iIntros (CID14 Hq14) "Hcg Hpc".
    iEval (rewrite Htgnp) in "Hpc".
    pose (R7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x1c) : mword 64) 4)]> R6).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x1c) : mword 64) 4)]> R6) with R7.
    assert (HR7ra : R7 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x1c) : mword 64) 4)
      by (rewrite /R7; apply upd_eq).
    assert (HR7a0 : R7 !!! Regidx Ra0 = (m !!! Regidx Ra0 : mword 64)).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [| nz]. exact (HR2o Ra0 ltac:(nz) ltac:(nz)). }
    assert (HR7a1 : R7 !!! Regidx Ra1 = pa_stk sp0 10).
    { rewrite /R7 upd_ne; [exact HR6a1 | nz]. }
    assert (HR7regs : cr_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64) ty major minor R7).
    { unfold cr_regs. split_and!.
      - rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
        rewrite /R3 upd_ne; [exact HR2sp | nz].
      - rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        exact HR5s0.
      - rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
        rewrite /R3 upd_ne; [| nz]. exact (HR2o Rs1 ltac:(nz) ltac:(nz)).
      - rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
        rewrite /R3 upd_ne; [| nz]. exact (HR2o Rs2 ltac:(nz) ltac:(nz)).
      - rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz]. exact HR3s4.
      - rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        rewrite /R5 upd_ne; [| nz]. exact HR4s5.
      - rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz]. exact HR5s6.
      - intros c Hc N2 N8 N9 N18 N20 N21 N22.
        rewrite /R7 upd_ne; [| dlk_rne2 Hcsra Hc].
        rewrite /R6 upd_ne; [| dlk_rne2 Hcsa1 Hc].
        rewrite /R5 upd_ne; [| dlk_xne N22].
        rewrite /R4 upd_ne; [| dlk_xne N21].
        rewrite /R3 upd_ne; [| dlk_xne N20].
        exact (HR2o c N2 N8). }
    (* ---- the sixteen-byte [name] local, and the fourteen it lends ---- *)
    iDestruct (cr_slots_bytes sp0 u10 u9 with "Hb10 Hb9") as "[%Hal Hnb]".
    destruct Hal as [Hal10 Hal9].
    iDestruct (dlk_bytes_name with "Hnb") as (nf0) "Hnb".
    iEval (rewrite cr_split14) in "Hnb".
    iDestruct "Hnb" as "[Hnb14 Hnb2]".
    (* ---- the ledger: two slots out for nameiparent ---- *)
    assert (Hnsplit : ns = (2 + (ns - 2))%nat)
      by exact (cr_ns_split ns Hns).
    iEval (rewrite {1}Hnsplit iref_slots_op) in "Hislots".
    iDestruct "Hislots" as "[Hisl2 Hislr]".
    (* ---- the running process: the BLOCK and the cwd reference ---- *)
    iDestruct (proc_priv_bare_cref γf (proc_addr j) pidv U with "Hpriv")
      as "(Hppid & Hcref & Hpclose)".
    iDestruct (cwd_ref_held with "Hcref") as "Hcref".
    iEval (rewrite -HR7a0) in "Hpath".
    iEval (rewrite -HR7a1) in "Hnb14".
    iDestruct (cpu_own_transport CID CID14 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (NP.wp_nameiparent_gen γs j γl pd pav pu
 γf
              plen pfun nf0 u Sb pidv (DfracOwn (1/4)) dqb dqs (DfracOwn 1)
              R7 (K - 10)%nat eb b lks U
              ltac:(exact HKnp) Hroot Hnib0 Hlg Hsize
              Hbms0 Hbmsc Hbmsl Hist0 Hcovb Hiregb Hcstr Hplen31
              ltac:(exact (cr_walk_need _ u Hu)) Hj Hgs
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hkenv Hitb2 Hitbl
                    Hesc Hslks Hiregi Hiopen Hprocs Hdevi Hgeom Hdlk Hsbb Hsbi Hbmr
                    Hppid Hcref Hpath Hnb14 Hbsl Hisl2 [$Hop $Htx]").
    (* nameiparent is eb-generic now; create is still at [eb = true]. *)
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CIDnp Hsnp mnp n1 Sb1 okp nfp ipv w)
      "%Hcsnp Hcg Hcnt _ _ Hpc Hsbb Hsbi Hppid Hcref Hpath Hnb14
       Hbsl %Hsb1 %Hwmem %Hnp1 [Hop Htx] Hres".
    iEval (rewrite HR7a0) in "Hpath".
    iEval (rewrite HR7a1) in "Hnb14".
    assert (Hpcnp : ret_pc (R7 !!! Regidx Rra : mword 64)
                    = mword_of_int (CK + 0x20)) by (rewrite HR7ra; pcw).
    iEval (rewrite Hpcnp) in "Hpc".
    assert (Hmnpregs : cr_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                         (m !!! Regidx Rs2 : mword 64) ty major minor mnp)
      by exact (cr_regs_cs m sp0 _ _ ty major minor R7 mnp Hcsnp HR7regs).
    (* the process block goes back whole: create copies nothing to or from
       user memory, so [V] is unchanged. *)
    iDestruct (cwd_ref_of_held with "Hcref") as "Hcref".
    iDestruct ("Hpclose" with "Hppid Hcref") as "Hpriv".
    (* ===== +0x20 c.mv s1,a0 : s1 = dp ================================ *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x20)) Rs1 Ra0 mnp (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_020 with "Htext"). }
    iIntros (CID15 Hq15) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (Q1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mnp !!! Regidx Ra0))]> mnp).
    change (<[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mnp !!! Regidx Ra0))]> mnp) with Q1.
    assert (HQ1s1 : Q1 !!! Regidx Rs1
                    = add_vec (zero_reg : mword 64) (mnp !!! Regidx Ra0))
      by (rewrite /Q1; apply upd_eq).
    assert (HQ1a0 : Q1 !!! Regidx Ra0 = (mnp !!! Regidx Ra0 : mword 64))
      by (rewrite /Q1 upd_ne; [reflexivity | nz]).
    assert (Hp022 : add_vec_int (mword_of_int (CK + 0x20) : mword 64) 2
                    = mword_of_int (CK + 0x22)) by pcw.
    iEval (rewrite Hp022) in "Hpc".
    assert (Htg160 : add_vec (mword_of_int (CK + 0x22) : mword 64)
              (sign_extend' 64 (mword_of_int 318 : mword 13))
              = mword_of_int (CK + 0x160)) by pcw.
    (* ================================================================== *)
    (*  THE EPILOGUE FUNNEL at +0x70 -- SIX arms reach it, so the          *)
    (*  continuation is abstract and the body speaks only of [cr_tregs].   *)
    (* ================================================================== *)
    iDestruct (cr_tail_half j m sp0 ret_tgt K b lks HKsum Hal10 Hal9
                 eq_refl eq_refl with "Htext") as "#Htail".
    destruct okp.
    - (* ============================================================== *)
      (*  nameiparent SUCCEEDED -- the parent is a LOCKED-ABLE DIRECTORY  *)
      (* ============================================================== *)
      iDestruct "Hres" as "((%Hnpa0 & %Hnpname) & Hipty & Hisl1)".
      iDestruct "Hipty" as (kd qd dind gd lod tld)
        "(%Hie & %Hkd & %Hdib & %Hled & #Hfld & Href & #Hshotd & Hrud)".
      assert (Hdib' : bv_unsigned dind < 16 * Z.of_nat icfg_nib)
        by (exact Hdib).
      destruct (Hiregb dind Hdib') as [Hdblk Hdblog].
      (* ===== +0x22 beqz a0 : FALLS THROUGH (an entry is never null) === *)
      iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (CK + 0x22))
                (mword_of_int 318 : mword 13) Ra0 Q1 (K - 10)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite HQ1a0 Hnpa0 Hie;
                      apply (proj2 (eq_vec_false_iff _ _));
                      exact (ientry_ne_zero kd (Nat.lt_le_incl _ _ Hkd)))
                with "Hcg Hpc []").
      { iApply (cri_022 with "Htext"). }
      iIntros (CID16 Hq16) "Hcg Hpc".
      assert (Hp026 : add_vec_int (mword_of_int (CK + 0x22) : mword 64) 4
                      = mword_of_int (CK + 0x26)) by pcw.
      iEval (rewrite Hp026) in "Hpc".
      (* the [mv s1,a0]'s value, as its OWN equation: an inline [ltac:] in
         argument position would be spliced while [v] is still an evar
         (durable-notes). *)
      assert (Hs1v : add_vec (zero_reg : mword 64) (mnp !!! Regidx Ra0) = ipv)
        by (rewrite Hnpa0; apply add_vec_zero_l).
      assert (HQ1regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                          ty major minor Q1)
        by exact (cr_regs_s1 m sp0 (m !!! Regidx Rs1 : mword 64) ipv
                    (m !!! Regidx Rs2 : mword 64) ty major minor mnp _
                    Hs1v Hmnpregs).
      (* ---- THE SHED: ilock takes a share AT THE SAME GENERATION ------
         [nameiparent] handed back [inode_held_ty ipv T_DIR], i.e. the
         reference with its generation NAMED and that generation's type
         one-shot beside it.  Shedding at that generation is what lets the
         [ity_shot_agree] below read ilock's own one-shot against it, and
         is why create needs no parent type test of its own (fs-sysfile
         Blocker B, closed by fs-log.md G-4d). *)
      iEval (rewrite cr_shed_genlo) in "Href".
      iDestruct "Href" as "[Hkeep Hshr]".
      iDestruct (is_itable2_claims with "Hitb2") as "#Hclaimscr".
      iDestruct (cr_esc_acc kd Hkd with "Hesc") as "#Hescd".
      iDestruct (ic_sleeplocks_lookup fsc_ic kd Hkd with "Hslks") as (gild gisld) "#Hslkd".
      iDestruct (cr_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
      iDestruct (proc_priv_bare_acc γf (proc_addr j) pidv U with "Hpriv")
        as "[Hppid Hppback]".
      (* ===== +0x26 jal ilock (a0 is STILL dp -- not reloaded) ========= *)
      assert (Htgil : add_vec (mword_of_int (CK + 0x26) : mword 64)
                (sign_extend' 64 (mword_of_int 2090536 : mword 21))
                = mword_of_int KernelSyms.ilock) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (CK + 0x26)) Rra
                (mword_of_int 2090536 : mword 21) Q1 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_026 with "Htext"). }
      iIntros (CID17 Hq17) "Hcg Hpc".
      iEval (rewrite Htgil) in "Hpc".
      pose (Q2 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0x26) : mword 64) 4)]> Q1).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0x26) : mword 64) 4)]> Q1) with Q2.
      assert (HQ2ra : Q2 !!! Regidx Rra
                      = add_vec_int (mword_of_int (CK + 0x26) : mword 64) 4)
        by (rewrite /Q2; apply upd_eq).
      assert (HQ2a0 : Q2 !!! Regidx Ra0 = ientry kd).
      { rewrite /Q2 upd_ne; [| nz]. rewrite HQ1a0 Hnpa0. exact Hie. }
      assert (HQ2regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                          ty major minor Q2)
        by (rewrite /Q2; apply cr_regs_caller; [exact Hcsra | exact HQ1regs]).
      iDestruct (cpu_own_transport CIDnp CID17 0%nat eb (proc_addr j) b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      (* THE PARENT'S CHECKOUT IS ARMED (durable-disk B''-tx2) AT THE
         CHECKOUT ITSELF (B''-tx3), and the TRANSACTION ID IS NAMED FROM HERE
         ON.  create's second lock has to park at the SAME transaction as this
         one, so the id leaves [LogInv.log_tx]'s existential once, before the
         first lock, and re-enters it only at an exit that holds no lock at
         all. *)

      iDestruct (log_tx_open with "Htx") as (t) "Htw".
      iDestruct (log_tx_split icfg_log t 1 (1/2) (1/2)
                   (eq_sym Qp.half_half) with "Htw") as "[Htp Htx]".
      iPoseProof (TsoGhost.llb_0 loglen_name) as "#Hllb0".   (* r25 lane (ii): nothing to present at this ilock *)
      iApply (IL.wp_ilock_dep_sconf γs j γl pd pav pu
                gild gisld kd (qd/2)%Qp gd lod tld
                (DepTx (qd/2)%Qp icfg_dev dind gd lod t (1/2)) PlainK
 dind
                pidv (DfracOwn (1/4)) dqs Q2 (K - 10)%nat eb b lks
                U ltac:(exact HKil) eq_refl ltac:(discriminate)
                Hkd Hlg Hist0 Hdblk Hdib' Hj Hgs HQ2a0
                with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hitbl Hescd Hiregi
                      Hslkd [//] Hfld Hclaimscr Hshr [Htp] Hrud Hsbi Hppid Hprocs Hdevi Hgeom Hdlk Hbs1 Hllb0").
      all: try lkbelow.
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { rewrite /ic_dep_side. iExact "Htp". }
      iIntros (CIDil Hqil mil dnl bml fld)
        "%Hcsil _ Hcg Hcnt _ _ Hpc Hppid Hsbi Hbs1 Hslkdd Hdep Hoffr
         Hidev Hiinum Hivalid Hload #Hshotl Hfrzl %Hfrd Hrud %Hilkpd".
      iEval (rewrite /ic_dep_held /=) in "Hload".
      assert (Hpcil : ret_pc (Q2 !!! Regidx Rra : mword 64)
                      = mword_of_int (CK + 0x2a)) by (rewrite HQ2ra; pcw).
      iEval (rewrite Hpcil) in "Hpc".
      assert (Hmilregs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                           ty major minor mil)
        by exact (cr_regs_cs m sp0 _ _ ty major minor Q2 mil Hcsil HQ2regs).
      pose proof Hmilregs as HmilR.
      destruct HmilR as (Y2 & Y8 & Y9 & Y18 & Y20 & Y21 & Y22 & Ythr).
      (* THE PARENT IS A DIRECTORY, and the walker said so.  [ity_shot] is
         a one-shot per generation, so the two readings agree. *)
      iDestruct (ity_shot_agree with "Hshotd Hshotl") as %Htyd.
      assert (Htydir : di_type dnl = SpecDirlookup.T_DIR) by (symmetry; exact Htyd).
      iDestruct (ic_loaded_open with "Hload") as (datl)
        "(%Hiok & %Hrl_datl & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlnk & Hdiat & Hmeta
          & Haddrs & Hind & Hblocks & Htop)".
      iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
      iEval (rewrite /i_nlink) in "Hinl".
      (* ===== +0x2a lh a5,74(s1) : dp->nlink -- THE GUARD (9da28f5) ==== *)
      iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x2a)) Ra5 Rs1
                (mword_of_int 74 : mword 12) mil (K - 10)%nat
                (di_nlink dnl : mword 16) b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc [] [Hinl]").
      { iApply (cri_02a with "Htext"). }
      { iEval (rgne; rewrite Y9 Hie). iExact "Hinl". }
      iIntros (CID18 Hq18) "Hcg Hpc Hinl".
      iEval (rgne; rewrite Y9 Hie) in "Hinl".
      pose (Q3 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (di_nlink dnl : mword 16) : mword 64)]> mil).
      change (<[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (di_nlink dnl : mword 16) : mword 64)]> mil) with Q3.
      assert (HQ3a5 : Q3 !!! Regidx Ra5
                      = (sign_extend' 64 (di_nlink dnl : mword 16) : mword 64))
        by (rewrite /Q3; apply upd_eq).
      assert (HQ3regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                          ty major minor Q3)
        by (rewrite /Q3; apply cr_regs_caller; [exact Hcsa5 | exact Hmilregs]).
      assert (Hp02e : add_vec_int (mword_of_int (CK + 0x2a) : mword 64) 4
                      = mword_of_int (CK + 0x2e)) by pcw.
      iEval (rewrite Hp02e) in "Hpc".
      assert (Htg084 : add_vec (mword_of_int (CK + 0x2e) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 43 : mword 8) ('b"0"))))
                = mword_of_int (CK + 0x84)) by pcw.
      (* the ledger, as [CreateBudget.cr_budget_found_w]'s first row *)
      assert (Hn1lo : (9 <= n1)%nat) by exact (cr_n1_lo u n1 w Hu (proj1 Hnp1)).
      assert (Hn1ip : (iput_units <= n1)%nat) by exact (cr_ip_of9 n1 Hn1lo).
      destruct (decide (di_nlink dnl = (mword_of_int 0 : mword 16))) as [Hnl0 | Hnl0].
      + (* ========== ARM G: the guard FIRES -- nlink == 0 ============= *)
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (CK + 0x2e))
                  (mword_of_int 43 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  Q3 (K - 10)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HQ3a5; exact (nx_nlz_eq _ Hnl0))
                  ltac:(rewrite Htg084; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_02e with "Htext"). }
        iIntros (CID19 Hq19). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg084) in "Hpc".
        (* [ic_loaded]'s tail is [inode_blocks]' 268-element big-op
           ([IcacheEscrow.ic_mk_loaded]'s comment) -- assembled by the
           constructor, not by [iFrame], which would re-search the whole
           function context against that big-op's goal shape. *)
        iAssert (inode_meta (ientry kd) dnl)
          with "[Hity Himaj Himin Hinl Hisz]" as "Hmetal".
        { rewrite /inode_meta /i_type /i_nlink. iFrame. }
        iDestruct (ic_mk_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kd dind dnl bml datl
                     Hiok Hrl_datl Hdok Hddix Hdoc Hduq
                     with "Hdlnk Hdiat Hmetal Haddrs Hind Hblocks Htop")
          as "Hload".
        iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
          [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
        (* +0x84 c.mv a0,s1 *)
        iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x84)) Ra0 Rs1 Q3
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_084 with "Htext"). }
        iIntros (CID20 Hq20) "Hcg Hpc". iEval (rgne) in "Hcg".
        pose (G1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (Q3 !!! Regidx Rs1))]> Q3).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (Q3 !!! Regidx Rs1))]> Q3) with G1.
        assert (HG1a0 : G1 !!! Regidx Ra0 = ientry kd).
        { rewrite /G1 upd_eq. rewrite /Q3 upd_ne; [| nz].
          rewrite Y9 Hie. apply add_vec_zero_l. }
        assert (HG1regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor G1)
          by (rewrite /G1; apply cr_regs_caller; [exact Hcsa0 | exact HQ3regs]).
        assert (Hp086 : add_vec_int (mword_of_int (CK + 0x84) : mword 64) 2
                        = mword_of_int (CK + 0x86)) by pcw.
        iEval (rewrite Hp086) in "Hpc".
        (* +0x86 jal iunlockput (dp) -- AT crb = cru = crz = false.
           [crz] is unavailable BY CONSTRUCTION on this arm: it is bought
           with [InodeRegion.nlz_obs], minted only at a NONZERO nlink
           observation, and this arm IS the zero observation. *)
        assert (Htgup : add_vec (mword_of_int (CK + 0x86) : mword 64)
                  (sign_extend' 64 (mword_of_int 2091036 : mword 21))
                  = mword_of_int KernelSyms.iunlockput) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0x86)) Rra
                  (mword_of_int 2091036 : mword 21) G1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_086 with "Htext"). }
        iIntros (CID21 Hq21) "Hcg Hpc".
        iEval (rewrite Htgup) in "Hpc".
        pose (G2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x86) : mword 64) 4)]> G1).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x86) : mword 64) 4)]> G1) with G2.
        assert (HG2ra : G2 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CK + 0x86) : mword 64) 4)
          by (rewrite /G2; apply upd_eq).
        assert (HG2a0 : G2 !!! Regidx Ra0 = ientry kd)
          by (rewrite /G2 upd_ne; [exact HG1a0 | nz]).
        assert (HG2regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor G2)
          by (rewrite /G2; apply cr_regs_caller; [exact Hcsra | exact HG1regs]).
        iDestruct (cpu_own_transport CIDil CID21 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
           goes in and the share it parked comes back in the post, so no
           bundleless out-state stands across the call. *)
        iDestruct (log_opS_named with "Hop") as (e0) "Hop".
        iDestruct (inode_ref_short_gen_forget _ _ _ _ _ _ _ _ Hled
                     with "Hfld Hkeep") as "Hkeep2".
        iDestruct (off_rows_to_dep with "Hoffr") as "Hoffd".
        iApply (IUP.wp_iunlockput_dep_gen γs j γl pd pav pu
                  gild gisld
                  kd (qd/2)%Qp (qd/2)%Qp gd lod tld (DepTx (qd/2)%Qp icfg_dev dind gd lod t (1/2)%Qp) dind dnl bml n1 Sb1
                  false false false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
                  G2 (K - 10)%nat eb b lks
                  U ltac:(exact HKiup) eq_refl Hkd ltac:(discriminate) ltac:(discriminate)
                  Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib' Hcovb
                  ltac:(exact Hn1ip) Hj Hgs HG2a0 ltac:(lkbelow) eq_refl
                  with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                        Hescd Hiregi Hiopen Hslkd Hslkdd [//] Hfld Hclaimscr Hdep Hoffd Hidev Hiinum
                        Hivalid Hload Hshotl Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr Hppid
                        Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
        all: try lkbelow.
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { iEval (cbn beta iota). iEmpIntro. }
        iIntros (CIDup Hqup mup n2 Sb2 wg)
          "%Hcsup Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
           %Hsb2 %Hwg %Hwgc %Hn2 Hop Hisl Htp".
        iDestruct (log_tx_add icfg_log t 1 (1/2) (1/2)
                     (eq_sym Qp.half_half) with "Htp Htx") as "Htw".
        iDestruct (log_tx_full with "Htw") as "Htx".

        assert (Hpcup : ret_pc (G2 !!! Regidx Rra : mword 64)
                        = mword_of_int (CK + 0x8a)) by (rewrite HG2ra; pcw).
        iEval (rewrite Hpcup) in "Hpc".
        assert (Hmupregs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                             ty major minor mup)
          by exact (cr_regs_cs m sp0 _ _ ty major minor G2 mup Hcsup HG2regs).
        iDestruct ("Hppback" with "Hppid") as "Hpriv".
        (* +0x8a c.li s2,0 *)
        iApply (wp_cli_s_sconf (mword_of_int (CK + 0x8a)) Rs2
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  mup (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc []").
        { iApply (cri_08a with "Htext"). }
        iIntros (CID22 Hq22) "Hcg Hpc".
        pose (G3 := <[Regidx Rs2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> mup).
        change (<[Regidx Rs2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> mup) with G3.
        assert (HG3s2 : G3 !!! Regidx Rs2 = (mword_of_int 0 : mword 64))
          by (rewrite /G3; apply upd_eq).
        assert (Hg2v : (mword_of_int 0 : mword 64) = (mword_of_int 0 : mword 64))
          by reflexivity.
        assert (HG3regs : cr_regs m sp0 ipv (mword_of_int 0 : mword 64)
                            ty major minor G3)
          by exact (cr_regs_s2 m sp0 ipv _ _ ty major minor mup _
                      Hg2v Hmupregs).
        assert (Hp08c : add_vec_int (mword_of_int (CK + 0x8a) : mword 64) 2
                        = mword_of_int (CK + 0x8c)) by pcw.
        iEval (rewrite Hp08c) in "Hpc".
        (* +0x8c c.j +0x70 *)
        assert (Htg070g : add_vec (mword_of_int (CK + 0x8c) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 2034 : mword 11) ('b"0"))))
                  = mword_of_int (CK + 0x70)) by pcw.
        iApply (wp_cj_s_sconf (mword_of_int (CK + 0x8c))
                  (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")))
                  G3 (K - 10)%nat b
                  ltac:(rewrite Htg070g; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_08c with "Htext"). }
        iIntros (CID23 Hq23). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg070g) in "Hpc".
        iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2") as (nfj) "Hnb16".
        iPoseProof ("Htail" $! CID23) as "Ht".
        iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
        iApply ("Ht" $! G3 u5 nfj with
                  "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
        { exact (cr_tregs_of_regs m sp0 ipv _ ty major minor G3 HG3regs). }
        iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
        iDestruct (cpu_own_transport CIDup CIDf 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* the slot ledger comes back whole: nameiparent took two and gave
           one back, and this [iunlockput] gave the other. *)
        iDestruct (iref_slots_combine with "Hisl1 Hisl") as "Hisl".
        iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
        iEval (rewrite -Hnsplit) in "Hisl".
        iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
                  (mword_of_int 0 : mword 32) dnl bml n2 Sb2 ns
                  with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv Hpath
                        Hbsl [%] Hisl [%] Hop [$Htx]").
        { exact Hcsf. }
        { exact (cr_slots_ns _ ns eq_refl Hns). }
        { split_and!; [exact (cr_sub2 _ _ _ Hsb1 Hsb2)
                      | exact (cr_le2 _ _ _ (proj2 Hn2) (proj2 Hnp1))
                      | discriminate]. }
        { iPureIntro. rewrite Ha0f. exact HG3s2. }
      + (* ====== THE GUARD FALLS THROUGH: dp->nlink <> 0 ============== *)
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CK + 0x2e))
                  (mword_of_int 43 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  Q3 (K - 10)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HQ3a5; exact (nx_nlz_ne _ Hnl0))
                  with "Hcg Hpc []").
        { iApply (cri_02e with "Htext"). }
        iIntros (CID19 Hq19) "Hcg Hpc".
        assert (Hp030 : add_vec_int (mword_of_int (CK + 0x2e) : mword 64) 2
                        = mword_of_int (CK + 0x30)) by pcw.
        iEval (rewrite Hp030) in "Hpc".
        (* ============================================================== *)
        (*  THE NLINK_MAX GATE, +0x30 .. +0x3c (xv6 117c0e7): the parent   *)
        (*  of a NEW DIRECTORY is refused once its own link count has      *)
        (*  reached 32767, because the ".." the mkdir arm writes would     *)
        (*  raise it past what the on-disk [short] holds.                  *)
        (*                                                                *)
        (*  Six instructions and a DIAMOND: the [c.bnez] at +0x36 (the     *)
        (*  count is not at the maximum) and the [c.beqz] at +0x3c's       *)
        (*  fall-through (the type is not T_DIR) BOTH land at +0x3e.  So   *)
        (*  the rest of the found half is proven ONCE, as the first        *)
        (*  conjunct of an [∧] -- which hands the whole context to both    *)
        (*  arms exactly as the two arms of a [destruct] would, and is     *)
        (*  the only shape that does: an [iAssert] of the continuation     *)
        (*  alone would consume the resources ARM G2 also needs.  The      *)
        (*  second conjunct IS ARM G2, the guard's own exit block at       *)
        (*  +0x8e: [iunlockput(dp)] then [return 0], which is ARM G's      *)
        (*  block at a different address -- gcc emitted the two cold       *)
        (*  blocks in source order, so ARM G is at +0x84 and the new one   *)
        (*  below it.  (That ordering is also what [relayout_shift.py]     *)
        (*  gets wrong: difflib pairs the new [c.beqz] with the old one    *)
        (*  and reports the guard as landing at +0x2e.)                    *)
        (* ============================================================== *)
        (*  Each conjunct is [wp_next]-WRAPPED, and a bare [(CIDj : CpuId)]
            parameter would make it unprovable: the tail transports
            [cpu_own] from the harts the found half already visited, and a
            free hart has nothing tying it to them -- the missing link IS
            the [wp_next] guard (D₀-a's finding, one increment on). *)
        iAssert ((wp_next (CID0 := CID19) b (proc_addr j) (fun CIDj : CpuId =>
                    ∀ Mj : regfile,
                    ⌜cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                       ty major minor Mj⌝ -∗
                    (* THE GATE'S FALL-THROUGH FACT, carried by the JOIN
                       and not by either arm: the [c.bnez] arm proves it
                       from the count, the [c.beqz] arm from the type, and
                       what +0x3e knows is their disjunction written as an
                       implication.  The allocate half relays it and only
                       the T_DIR sub-branch spends it. *)
                    ⌜ty = SpecDirlookup.T_DIR ->
                       di_nlink dnl <> (mword_of_int 32767 : mword 16)⌝ -∗
                    sie_cap_gpr KT1 (CID := CIDj) Mj (K - 10)%nat b (proc_addr j) -∗
                    pc_is (CID := CIDj) (mword_of_int (CK + 0x3e)) -∗
                    WP (Loop : expr riscv_lang)))
                 ∧ (wp_next (CID0 := CID19) b (proc_addr j) (fun CIDg : CpuId =>
                    ∀ Mg : regfile,
                    ⌜cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                       ty major minor Mg⌝ -∗
                    sie_cap_gpr KT1 (CID := CIDg) Mg (K - 10)%nat b (proc_addr j) -∗
                    pc_is (CID := CIDg) (mword_of_int (CK + 0x8e)) -∗
                    WP (Loop : expr riscv_lang))))%I
          with "[-Hcg Hpc]" as "Hgate".
        { iSplit.
          - (* ===== THE JOIN AT +0x3e: dirlookup and everything after === *)
            iIntros (CIDj) "%Hqj". iIntros (Mj) "%HMjregs %Hnlmax Hcg Hpc".
            pose proof HMjregs as HMjR.
            destruct HMjR as (W2 & W8 & W9 & W18 & W20 & W21 & W22 & Wthr).
        (* the locked directory's payload, in the pieces dirlookup takes *)
        (* KEEP [Hiok] WHOLE -- the two re-parks below want it back, so take
           the three clauses dirlookup asks for as projections. *)
        assert (Hbmwf : blkmap_wf fsc_cov fsc_logst bml) by exact (proj1 Hiok).
        assert (Hbmcov : bm_covers bml (bv_unsigned (di_size dnl)))
          by exact (proj1 (proj2 Hiok)).
        assert (Hszcap : bv_unsigned (di_size dnl)
                         <= Z.of_nat MAXFILE * Z.of_nat BSIZE)
          by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hiok))))).
        assert (Hdz : bv_unsigned (di_type dnl) = T_DIR_z)
          by (rewrite Htydir; vm_compute; reflexivity).
        (* ===== +0x3e c.li a2,0 : dirlookup's [poff] is NOT wanted ===== *)
        iApply (wp_cli_s_sconf (mword_of_int (CK + 0x3e)) Ra2
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  Mj (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc []").
        { iApply (cri_03e with "Htext"). }
        iIntros (CID20 Hq20) "Hcg Hpc".
        pose (D1 := <[Regidx Ra2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> Mj).
        change (<[Regidx Ra2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> Mj) with D1.
        assert (HD1a2 : D1 !!! Regidx Ra2 = (mword_of_int 0 : mword 64))
          by (rewrite /D1; apply upd_eq).
        assert (HD1s0 : D1 !!! Regidx Rs0 = sp0).
        { rewrite /D1 upd_ne; [| nz]. exact W8. }
        assert (HD1s1 : D1 !!! Regidx Rs1 = ipv).
        { rewrite /D1 upd_ne; [| nz]. exact W9. }
        assert (HD1regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor D1)
          by (rewrite /D1; apply cr_regs_caller; [exact Hcsa2 | exact HMjregs]).
        assert (Hp040 : add_vec_int (mword_of_int (CK + 0x3e) : mword 64) 2
                        = mword_of_int (CK + 0x40)) by pcw.
        iEval (rewrite Hp040) in "Hpc".
        (* ===== +0x40 addi a1,s0,-80 : a1 = &name ====================== *)
        iApply (wp_addi4_s_sconf (mword_of_int (CK + 0x40)) Ra1 Rs0
                  (mword_of_int 4016 : mword 12) D1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_040 with "Htext"). }
        iIntros (CID21 Hq21) "Hcg Hpc".
        pose (D2 := <[Regidx Ra1 := regval_into_reg
                      (add_vec (rget D1 Rs0)
                         (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> D1).
        change (<[Regidx Ra1 := regval_into_reg
                      (add_vec (rget D1 Rs0)
                         (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> D1) with D2.
        assert (HD2a1 : D2 !!! Regidx Ra1 = pa_stk sp0 10).
        { rewrite /D2 upd_eq. rewrite rget_ne;
            [| intro Hz1; injection Hz1 as Hz2; vm_compute in Hz2; congruence ].
          rewrite HD1s0. apply cr_name_addr. }
        assert (HD2a2 : D2 !!! Regidx Ra2 = (mword_of_int 0 : mword 64))
          by (rewrite /D2 upd_ne; [exact HD1a2 | nz]).
        assert (HD2s1 : D2 !!! Regidx Rs1 = ipv)
          by (rewrite /D2 upd_ne; [exact HD1s1 | nz]).
        assert (HD2regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor D2)
          by (rewrite /D2; apply cr_regs_caller; [exact Hcsa1 | exact HD1regs]).
        assert (Hp044 : add_vec_int (mword_of_int (CK + 0x40) : mword 64) 4
                        = mword_of_int (CK + 0x44)) by pcw.
        iEval (rewrite Hp044) in "Hpc".
        (* ===== +0x44 c.mv a0,s1 ======================================= *)
        iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x44)) Ra0 Rs1 D2
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_044 with "Htext"). }
        iIntros (CID22 Hq22) "Hcg Hpc". iEval (rgne) in "Hcg".
        pose (D3 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (D2 !!! Regidx Rs1))]> D2).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (D2 !!! Regidx Rs1))]> D2) with D3.
        assert (HD3a0 : D3 !!! Regidx Ra0 = ientry kd).
        { rewrite /D3 upd_eq. rewrite HD2s1 Hie. apply add_vec_zero_l. }
        assert (HD3a1 : D3 !!! Regidx Ra1 = pa_stk sp0 10)
          by (rewrite /D3 upd_ne; [exact HD2a1 | nz]).
        assert (HD3a2 : D3 !!! Regidx Ra2 = (mword_of_int 0 : mword 64))
          by (rewrite /D3 upd_ne; [exact HD2a2 | nz]).
        assert (HD3regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor D3)
          by (rewrite /D3; apply cr_regs_caller; [exact Hcsa0 | exact HD2regs]).
        assert (Hp046 : add_vec_int (mword_of_int (CK + 0x44) : mword 64) 2
                        = mword_of_int (CK + 0x46)) by pcw.
        iEval (rewrite Hp046) in "Hpc".
        (* ===== +0x46 jal dirlookup(dp, name, 0) ======================= *)
        assert (Htgdl : add_vec (mword_of_int (CK + 0x46) : mword 64)
                  (sign_extend' 64 (mword_of_int 2092016 : mword 21))
                  = mword_of_int KernelSyms.dirlookup) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0x46)) Rra
                  (mword_of_int 2092016 : mword 21) D3 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_046 with "Htext"). }
        iIntros (CID23 Hq23) "Hcg Hpc".
        iEval (rewrite Htgdl) in "Hpc".
        pose (D4 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x46) : mword 64) 4)]> D3).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x46) : mword 64) 4)]> D3) with D4.
        assert (HD4ra : D4 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CK + 0x46) : mword 64) 4)
          by (rewrite /D4; apply upd_eq).
        assert (HD4a0 : D4 !!! Regidx Ra0 = ientry kd)
          by (rewrite /D4 upd_ne; [exact HD3a0 | nz]).
        assert (HD4a1 : D4 !!! Regidx Ra1 = pa_stk sp0 10)
          by (rewrite /D4 upd_ne; [exact HD3a1 | nz]).
        assert (HD4a2 : D4 !!! Regidx Ra2 = (mword_of_int 0 : mword 64))
          by (rewrite /D4 upd_ne; [exact HD3a2 | nz]).
        assert (HD4regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor D4)
          by (rewrite /D4; apply cr_regs_caller; [exact Hcsra | exact HD3regs]).
        iAssert (inode_meta (ientry kd) dnl)
          with "[Hity Himaj Himin Hinl Hisz]" as "Hmeta".
        { rewrite /inode_meta /i_type /i_nlink. iFrame. }
        iAssert (inode_map fsc_fs (ientry kd) bml) with "[Haddrs Hind]" as "Hmap".
        { rewrite /inode_map. iFrame. }
        iEval (rewrite -HD4a1) in "Hnb14".
        iDestruct (cpu_own_transport CIDil CID23 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* THE BORROWED LICENCE (fs-fragments.md §7.5.6, row 2).  The LEFT
           disjunct is what create brings, and the guard that earns it is
           [sysfile.c:269]'s [dp->nlink == 0] refusal at +0x2a/+0x2e: this
           branch is the [c.beqz] at +0x2e FALLING THROUGH, whose own
           hypothesis [Hnl0] says the parent's count is not zero.  The
           ticket list [Hdlnk] and the home's record [Hdiat] are lent to
           dirlookup's iget and come straight back on both arms -- nothing
           is spent, and both are already in hand out of
           [IcacheEscrow.ic_loaded]. *)
        (* dirlookup borrows the LEDGER half alone (durable-disk
           2b-inode-5); the counting RA's tokens stay in this walk's hand
           and go back into the payload with the same node. *)
        assert (Hholesl : blk_holes_zero bml datl)
          by (destruct Hiok as (_ & _ & _ & _ & _ & Hq & _); exact Hq).
        iApply (DL.wp_dirlookup_sconf γs j γl pd pav pu
 γf (ientry kd) dind bml datl
                  dnl dnl nfp
                  false (mword_of_int 0 : mword 32)
                  pidv (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn 1)
                  D4 (K - 10)%nat eb b lks
                  U ltac:(exact HKdlu) Htydir Hlg Hbmwf Hbmcov Hszcap Hholesl
                  ltac:(exact (Hdok Hdz))
                  ltac:(left; exact (cr_nl0z dnl Hnl0))
                  ltac:(exact Hdoc)
                  ltac:(rewrite Hdz; unfold T_DIR_z; lia)
                  (* premise (6'), iclaim-ledger.md §3.3: the region record
                     IS the in-core one here (both slots take [dnl]). *)
                  eq_refl
                  Hj Hgs HD4a0
                  ltac:(cbn [negb]; rewrite HD4a2 dlk_zero_moi;
                        exact (eq_vec_refl _))
                  with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hkenv Hidev Hmeta Hmap
                        Hblocks Hnb14 [] Hppid Hprocs Hdevi Hgeom Hdlk Hbs1
                        Hitb2 Hitbl Hesc Hiregi Hisl1 Hdlnk Hdiat").
        all: try lkbelow.
        (* dirlookup is eb-generic now; create is still at [eb = true]. *)
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { done. }
        iIntros (CIDdl Hsdl mdl found kk kslot qq)
          "%Hcsdl Hcg Hcnt _ _ Hpc Hidev Hmeta Hmap Hblocks Hnb14 Hppid Hbs1
           Hdlnk Hdiat Hres2".
        iEval (rewrite HD4a1) in "Hnb14".
        assert (Hpcdl : ret_pc (D4 !!! Regidx Rra : mword 64)
                        = mword_of_int (CK + 0x4a)) by (rewrite HD4ra; pcw).
        iEval (rewrite Hpcdl) in "Hpc".
        assert (Hmdlregs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                             ty major minor mdl)
          by exact (cr_regs_cs m sp0 _ _ ty major minor D4 mdl Hcsdl HD4regs).
        assert (Htg0a2 : add_vec (mword_of_int (CK + 0x4c) : mword 64)
                  (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 43 : mword 8) ('b"0"))))
                  = mword_of_int (CK + 0xa2)) by pcw.
        assert (Hp04c : add_vec_int (mword_of_int (CK + 0x4a) : mword 64) 2
                        = mword_of_int (CK + 0x4c)) by pcw.
        destruct found.
        * (* ========================================================== *)
          (*  THE NAME IS ALREADY THERE -- the FOUND half's two arms      *)
          (* ========================================================== *)
          iDestruct "Hres2" as "((%Hfst & %Hkslot & %Hdla0) & Hchild & Hruc & _)".
          (* the child's inum is inside the region, and NONZERO because a
             directory record is live exactly when its inum is. *)
          assert (Hklt : (kk < dir_nrec (bv_unsigned (di_size dnl)))%nat)
            by exact (dir_first_lt datl _ kk _ Hfst).
          assert (Hklive : dir_live datl kk)
            by exact (dir_first_live datl _ kk _ Hfst).
          pose (cinum := (zero_extend' 32 (dir_inum datl kk : mword 16) : mword 32)).
          assert (Hcu : bv_unsigned cinum = bv_unsigned (dir_inum datl kk))
            by (rewrite /cinum; apply dlk_zext32_unsigned).
          assert (Hcinb : bv_unsigned cinum < 16 * Z.of_nat icfg_nib)
            by (rewrite Hcu; exact (Hdok Hdz kk Hklt Hklive)).
          assert (Hcpos : 0 < bv_unsigned cinum).
          { rewrite Hcu.
            destruct (bv_unsigned_in_range _ (dir_inum datl kk)) as [Hlo _].
            destruct (Z.eq_dec (bv_unsigned (dir_inum datl kk)) 0) as [Hz | Hz];
              [| exact (cr_pos_of_nz _ Hlo Hz)].
            exfalso. apply Hklive. apply bv_eq. rewrite Hz. reflexivity. }
          destruct (Hiregb cinum Hcinb) as [Hcblk Hcblog].
          (* ===== +0x4a c.mv s2,a0 : s2 = ip ========================== *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x4a)) Rs2 Ra0 mdl
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (cri_04a with "Htext"). }
          iIntros (CID24 Hq24) "Hcg Hpc". iEval (rgne) in "Hcg".
          pose (F1 := <[Regidx Rs2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mdl !!! Regidx Ra0))]> mdl).
          change (<[Regidx Rs2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mdl !!! Regidx Ra0))]> mdl) with F1.
          assert (Hf1v : add_vec (zero_reg : mword 64) (mdl !!! Regidx Ra0)
                         = ientry kslot)
            by (rewrite Hdla0; apply add_vec_zero_l).
          assert (HF1s2 : F1 !!! Regidx Rs2 = ientry kslot)
            by (rewrite /F1 upd_eq; exact Hf1v).
          assert (HF1a0 : F1 !!! Regidx Ra0 = (mdl !!! Regidx Ra0 : mword 64))
            by (rewrite /F1 upd_ne; [reflexivity | nz]).
          assert (HF1regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F1)
            by exact (cr_regs_s2 m sp0 ipv _ _ ty major minor mdl _ Hf1v
                        Hmdlregs).
          iEval (rewrite Hp04c) in "Hpc".
          (* ===== +0x4c c.beqz a0 : FALLS THROUGH (a hit is an entry) == *)
          iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CK + 0x4c))
                    (mword_of_int 43 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                    F1 (K - 10)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HF1a0 Hdla0;
                          apply (proj2 (eq_vec_false_iff _ _));
                          exact (ientry_ne_zero kslot
                                   (Nat.lt_le_incl _ _ Hkslot)))
                    with "Hcg Hpc []").
          { iApply (cri_04c with "Htext"). }
          iIntros (CID25 Hq25) "Hcg Hpc".
          assert (Hp04e : add_vec_int (mword_of_int (CK + 0x4c) : mword 64) 2
                          = mword_of_int (CK + 0x4e)) by pcw.
          iEval (rewrite Hp04e) in "Hpc".
          (* ===== +0x4e c.mv a0,s1 : the PARENT, for iunlockput ======== *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x4e)) Ra0 Rs1 F1
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (cri_04e with "Htext"). }
          iIntros (CID26 Hq26) "Hcg Hpc". iEval (rgne) in "Hcg".
          pose (F2 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (F1 !!! Regidx Rs1))]> F1).
          change (<[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (F1 !!! Regidx Rs1))]> F1) with F2.
          assert (HF2a0 : F2 !!! Regidx Ra0 = ientry kd).
          { rewrite /F2 upd_eq. rewrite /F1 upd_ne; [| nz].
            destruct Hmdlregs as (_ & _ & Hd9 & _). rewrite Hd9 Hie.
            apply add_vec_zero_l. }
          assert (HF2regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F2)
            by (rewrite /F2; apply cr_regs_caller; [exact Hcsa0 | exact HF1regs]).
          assert (Hp050 : add_vec_int (mword_of_int (CK + 0x4e) : mword 64) 2
                          = mword_of_int (CK + 0x50)) by pcw.
          iEval (rewrite Hp050) in "Hpc".
          (* ===== +0x50 jal iunlockput (dp), UNCREDITED ================ *)
          assert (Htgup1 : add_vec (mword_of_int (CK + 0x50) : mword 64)
                    (sign_extend' 64 (mword_of_int 2091090 : mword 21))
                    = mword_of_int KernelSyms.iunlockput) by pcw.
          iApply (wp_jal_s_sconf (mword_of_int (CK + 0x50)) Rra
                    (mword_of_int 2091090 : mword 21) F2 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_050 with "Htext"). }
          iIntros (CID27 Hq27) "Hcg Hpc".
          iEval (rewrite Htgup1) in "Hpc".
          pose (F3 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x50) : mword 64) 4)]> F2).
          change (<[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x50) : mword 64) 4)]> F2) with F3.
          assert (HF3ra : F3 !!! Regidx Rra
                          = add_vec_int (mword_of_int (CK + 0x50) : mword 64) 4)
            by (rewrite /F3; apply upd_eq).
          assert (HF3a0 : F3 !!! Regidx Ra0 = ientry kd)
            by (rewrite /F3 upd_ne; [exact HF2a0 | nz]).
          assert (HF3regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F3)
            by (rewrite /F3; apply cr_regs_caller; [exact Hcsra | exact HF2regs]).
          iDestruct "Hmap" as "[Haddrs Hind]".
          iDestruct (ic_mk_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kd dind dnl bml datl
                       Hiok Hrl_datl Hdok Hddix Hdoc Hduq
                       with "Hdlnk Hdiat Hmeta Haddrs Hind Hblocks Htop")
            as "Hload".
          iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
            [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
          iDestruct (cpu_own_transport CIDdl CID27 0%nat eb (proc_addr j) b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
             goes in and the share it parked comes back in the post, so no
             bundleless out-state stands across the call. *)
          iDestruct (log_opS_named with "Hop") as (e0) "Hop".
          iDestruct (inode_ref_short_gen_forget _ _ _ _ _ _ _ _ Hled
                     with "Hfld Hkeep") as "Hkeep2".
          iDestruct (off_rows_to_dep with "Hoffr") as "Hoffd".
          iApply (IUP.wp_iunlockput_dep_gen γs j γl pd pav pu
                    gild gisld
 kd (qd/2)%Qp (qd/2)%Qp gd lod tld (DepTx (qd/2)%Qp icfg_dev dind gd lod t (1/2)%Qp) dind dnl bml n1 Sb1
                    false false false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
                    F3 (K - 10)%nat eb b lks
                    U ltac:(exact HKiup) eq_refl Hkd ltac:(discriminate) ltac:(discriminate)
                    Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib' Hcovb
                    ltac:(exact Hn1ip) Hj Hgs HF3a0 ltac:(lkbelow) eq_refl
                    with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                          Hescd Hiregi Hiopen Hslkd Hslkdd [//] Hfld Hclaimscr Hdep Hoffd Hidev Hiinum
                          Hivalid Hload Hshotl Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr Hppid
                          Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
          all: try lkbelow.
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { iEval (cbn beta iota). iEmpIntro. }
          iIntros (CIDu1 Hqu1 mu1 n2 Sb2 wf1)
            "%Hcsu1 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
             %Hsb2 %Hwf1 %Hwf1c %Hn2 Hop Hisl Htp".
          assert (Hpcu1 : ret_pc (F3 !!! Regidx Rra : mword 64)
                          = mword_of_int (CK + 0x54)) by (rewrite HF3ra; pcw).
          iEval (rewrite Hpcu1) in "Hpc".
          assert (Hmu1regs : cr_regs m sp0 ipv (ientry kslot) ty major minor mu1)
            by exact (cr_regs_cs m sp0 _ _ ty major minor F3 mu1 Hcsu1 HF3regs).
          (* GR-2c FINDING 5: the credited bound is STRONGER than the row
             the ledger cites; weaken ONCE, keeping the name. *)
          destruct (cr_after_ip n1 n2 wf1 Hn1lo (proj1 Hn2)) as [Hn2ip Hn2lo].
          (* ===== +0x54 c.mv a0,s2 : the CHILD ========================= *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x54)) Ra0 Rs2 mu1
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (cri_054 with "Htext"). }
          iIntros (CID28 Hq28) "Hcg Hpc". iEval (rgne) in "Hcg".
          pose (F4 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mu1 !!! Regidx Rs2))]> mu1).
          change (<[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mu1 !!! Regidx Rs2))]> mu1) with F4.
          assert (HF4a0 : F4 !!! Regidx Ra0 = ientry kslot).
          { rewrite /F4 upd_eq.
            destruct Hmu1regs as (_ & _ & _ & Hd18 & _). rewrite Hd18.
            apply add_vec_zero_l. }
          assert (HF4regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F4)
            by (rewrite /F4; apply cr_regs_caller; [exact Hcsa0 | exact Hmu1regs]).
          assert (Hp056 : add_vec_int (mword_of_int (CK + 0x54) : mword 64) 2
                          = mword_of_int (CK + 0x56)) by pcw.
          iEval (rewrite Hp056) in "Hpc".
          (* ===== +0x56 jal ilock (ip) ================================= *)
          assert (Htgil2 : add_vec (mword_of_int (CK + 0x56) : mword 64)
                    (sign_extend' 64 (mword_of_int 2090488 : mword 21))
                    = mword_of_int KernelSyms.ilock) by pcw.
          iApply (wp_jal_s_sconf (mword_of_int (CK + 0x56)) Rra
                    (mword_of_int 2090488 : mword 21) F4 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_056 with "Htext"). }
          iIntros (CID29 Hq29) "Hcg Hpc".
          iEval (rewrite Htgil2) in "Hpc".
          pose (F5 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x56) : mword 64) 4)]> F4).
          change (<[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x56) : mword 64) 4)]> F4) with F5.
          assert (HF5ra : F5 !!! Regidx Rra
                          = add_vec_int (mword_of_int (CK + 0x56) : mword 64) 4)
            by (rewrite /F5; apply upd_eq).
          assert (HF5a0 : F5 !!! Regidx Ra0 = ientry kslot)
            by (rewrite /F5 upd_ne; [exact HF4a0 | nz]).
          assert (HF5regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F5)
            by (rewrite /F5; apply cr_regs_caller; [exact Hcsra | exact HF4regs]).
          (* the child's reference, shed for ilock (generation UNNAMED on
             this side: dirlookup's iget hands back a plain [inode_ref]) *)
          iEval (rewrite inode_ref_shed) in "Hchild".
          iDestruct "Hchild" as "[Hckeep Hcshr]".
          iEval (rewrite inode_shr_gen_intro) in "Hcshr".
          iDestruct "Hcshr" as (gc loc tlc) "(%Hlec & #Hflc & Hcshr)".
          iEval (rewrite inode_ref_short_gen_intro) in "Hckeep".
          iDestruct "Hckeep" as (gck lock tlck) "(%Hleck & #Hflck & Hckeep)".
          iDestruct (inode_ref_short_shr_genlo_agree
                       with "Hckeep Hcshr") as %[-> <-].
          iDestruct (cr_esc_acc kslot Hkslot with "Hesc")
            as "#Hescc".
          iDestruct (ic_sleeplocks_lookup fsc_ic kslot Hkslot with "Hslks")
            as (gilc gislc) "#Hslkc".
          iDestruct (cr_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
          iDestruct (cpu_own_transport CIDu1 CID29 0%nat eb (proc_addr j) b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          (* THE CHILD'S CHECKOUT IS ARMED (durable-disk B''-tx2) AT THE
             CHECKOUT ITSELF (B''-tx3).  The parent went home at +0x50, so
             this arm parks exactly the half that came back from its disarm,
             at the same transaction. *)
          iPoseProof (TsoGhost.llb_0 loglen_name) as "#Hllb0b".   (* r25 lane (ii): nothing to present at this ilock *)
          iApply (IL.wp_ilock_dep_sconf γs j γl pd pav pu
                    gilc gislc kslot (qq/2)%Qp gc lock tlc
                    (DepTx (qq/2)%Qp icfg_dev cinum gc lock t (1/2)) PlainK
 cinum pidv (DfracOwn (1/4)) dqs F5 (K - 10)%nat eb b lks
                    U ltac:(exact HKil) eq_refl ltac:(discriminate)
                    Hkslot Hlg Hist0 Hcblk Hcinb Hj Hgs HF5a0
                    with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hitbl Hescc
                          Hiregi Hslkc [//] Hflc Hclaimscr Hcshr [Htp] Hruc Hsbi Hppid Hprocs Hdevi Hgeom
                          Hdlk Hbs1 Hllb0b").
          all: try lkbelow.
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { rewrite /ic_dep_side. iExact "Htp". }
          iIntros (CIDic Hqic mic dnc bmc flc)
            "%Hcsic _ Hcg Hcnt _ _ Hpc Hppid Hsbi Hbs1 Hcslkd Hcdep Hoffrc
             Hcidev Hciinum Hcivalid Hcload #Hcshot Hcfrz %Hfrc Hruc %Hilkpc".
          iEval (rewrite /ic_dep_held /=) in "Hcload".
          assert (Hpcic : ret_pc (F5 !!! Regidx Rra : mword 64)
                          = mword_of_int (CK + 0x5a)) by (rewrite HF5ra; pcw).
          iEval (rewrite Hpcic) in "Hpc".
          assert (Hmicregs : cr_regs m sp0 ipv (ientry kslot) ty major minor mic)
            by exact (cr_regs_cs m sp0 _ _ ty major minor F5 mic Hcsic HF5regs).
          pose proof Hmicregs as HmicR.
          destruct HmicR as (Z2 & Z8 & Z9 & Z18 & Z20 & Z21 & Z22 & Zthr).
          iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
            [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
          (* ============================================================ *)
          (*  ARM F-BAD (+0x98), reached from BOTH type tests -- so it is  *)
          (*  a [□]-persistent block that takes every linear resource,     *)
          (*  the contract's own continuation included, as an ARGUMENT.    *)
          (*  ONE [iunlockput], on the CHILD: the parent was released at   *)
          (*  +0x50, which is shared with F-OK.  Both are uncredited, and  *)
          (*  [CreateBudget.cr_budget_found_w]'s third conjunct is the     *)
          (*  row that closes it.                                          *)
          (* ============================================================ *)
          iAssert (□ wp_next (CID0 := CID) true (proc_addr j) (fun CIDb : CpuId =>
                     ∀ Mb : regfile,
                       ⌜cr_regs m sp0 ipv (ientry kslot) ty major minor Mb⌝ -∗
                       sie_cap_gpr KT1 Mb (K - 10)%nat b (proc_addr j) -∗
                       cpu_own 0 eb (proc_addr j) b lks -∗
                       pc_is (mword_of_int (CK + 0x98)) -∗
                       (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
                       (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
                       (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
                       (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
                       (pa_stk sp0 5) ↦₈[KT1] u5 -∗
                       (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) -∗
                       (pa_stk sp0 7) ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) -∗
                       (pa_stk sp0 8) ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) -∗
                       ([∗ list] jj ∈ seq 0 14,
                          pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nfp jj) -∗
                       ([∗ list] jj ∈ seq 14 2,
                          pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nf0 jj) -∗
                       sleeplocked_q gislc (qq/2)%Qp (i_lock (ientry kslot)) pidv -∗
                       ic_handle fsc_ic kslot (DepTx (qq/2)%Qp icfg_dev cinum gc lock t (1/2)) -∗
                       off_rows off_cfg kslot cur_ctx -∗
                       i_dev (ientry kslot) ↦₄{DfracOwn (1/2)} icfg_dev -∗
                       i_inum (ientry kslot) ↦₄{DfracOwn (1/2)} cinum -∗
                       i_valid (ientry kslot) ↦₄ valid_word true -∗
                       ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kslot cinum dnc bmc -∗
                       ity_shot gc (di_type dnc) -∗
                       (* the child payload's freeze token (§3.9) *)
                       ifreeze_off (bv_unsigned cinum) -∗
                       IcacheRef.inode_ref_short_genlo kslot
                         (qq/2 + qq/2)%Qp (qq/2)%Qp icfg_dev cinum gc lock -∗
                       (* the child's PROVENANCE UNIT (item 7a-wire). *)
                       runit_any (bv_unsigned cinum) -∗
                       sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
                       sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
                       sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
                       sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
                       proc_priv_bare (proc_addr j) pidv U -∗
                       (proc_priv_bare (proc_addr j) pidv U -∗
                          proc_priv γf (proc_addr j) pidv U) -∗
                       ([∗ list] i ∈ seq 0 (S plen),
                          pa_add (m !!! Regidx Ra0 : mword 64) i ↦ₘ[KT1] pfun i) -∗
                       bslots 3 -∗
                       iref_slots 1 -∗ iref_slots (ns - 2) -∗
                       log_opS icfg_log n2 Sb2 -∗
                       t ↪[ln_tx icfg_log]{#(1/2)} tt -∗
                       wp_next (CID0 := CID) true (proc_addr j)
                         (fun CIDc : CpuId =>
                            cr_cont_body γf
 plen pfun
                              (m !!! Regidx Ra0 : mword 64) ty major minor U u Sb
                              ns pidv dqb dqs dqbs dqn m K eb b lks j ret_tgt
                              CIDc) -∗
                       WP (Loop : expr riscv_lang)))%I
            with "[]" as "#Hfbad".
          { iModIntro.
            iIntros (CIDb Hsb Mb)
              "%HBr Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
               Hcslkd Hcdep Hoffrc Hcidev Hciinum Hcivalid Hcload Hcshotb
               Hcfrz Hckeep Hruc Hsbn Hsbi Hsbs Hsbb Hppid Hppback Hpath Hbsl
               Hisl Hislr Hop Htx Hcontb".
            pose proof HBr as HBr2.
            destruct HBr2 as (X2 & X8 & X9 & X18 & X20 & X21 & X22 & Xthr).
            (* +0x98 c.mv a0,s2 : the CHILD *)
            iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x98)) Ra0 Rs2 Mb
                      (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
            { iApply (cri_098 with "Htext"). }
            iIntros (CIDB1 HqB1) "Hcg Hpc". iEval (rgne) in "Hcg".
            pose (B1 := <[Regidx Ra0 := regval_into_reg
                          (add_vec (zero_reg : mword 64)
                             (Mb !!! Regidx Rs2))]> Mb).
            change (<[Regidx Ra0 := regval_into_reg
                          (add_vec (zero_reg : mword 64)
                             (Mb !!! Regidx Rs2))]> Mb) with B1.
            assert (HB1a0 : B1 !!! Regidx Ra0 = ientry kslot).
            { rewrite /B1 upd_eq. rewrite X18. apply add_vec_zero_l. }
            assert (HB1regs : cr_regs m sp0 ipv (ientry kslot) ty major minor B1)
              by (rewrite /B1; apply cr_regs_caller; [exact Hcsa0 | exact HBr]).
            assert (Hq09a : add_vec_int (mword_of_int (CK + 0x98) : mword 64) 2
                            = mword_of_int (CK + 0x9a)) by pcw.
            iEval (rewrite Hq09a) in "Hpc".
            (* +0x9a jal iunlockput (ip), at crb = cru = crz = false *)
            assert (Htgup2 : add_vec (mword_of_int (CK + 0x9a) : mword 64)
                      (sign_extend' 64 (mword_of_int 2091016 : mword 21))
                      = mword_of_int KernelSyms.iunlockput) by pcw.
            iApply (wp_jal_s_sconf (mword_of_int (CK + 0x9a)) Rra
                      (mword_of_int 2091016 : mword 21) B1 (K - 10)%nat b
                      ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                      with "Hcg Hpc []").
            { iApply (cri_09a with "Htext"). }
            iIntros (CIDB2 HqB2) "Hcg Hpc".
            iEval (rewrite Htgup2) in "Hpc".
            pose (B2 := <[Regidx Rra := regval_into_reg
                          (add_vec_int (mword_of_int (CK + 0x9a) : mword 64) 4)]> B1).
            change (<[Regidx Rra := regval_into_reg
                          (add_vec_int (mword_of_int (CK + 0x9a) : mword 64) 4)]> B1) with B2.
            assert (HB2ra : B2 !!! Regidx Rra
                            = add_vec_int (mword_of_int (CK + 0x9a) : mword 64) 4)
              by (rewrite /B2; apply upd_eq).
            assert (HB2a0 : B2 !!! Regidx Ra0 = ientry kslot)
              by (rewrite /B2 upd_ne; [exact HB1a0 | nz]).
            assert (HB2regs : cr_regs m sp0 ipv (ientry kslot) ty major minor B2)
              by (rewrite /B2; apply cr_regs_caller; [exact Hcsra | exact HB1regs]).
            iDestruct (cpu_own_transport CIDb CIDB2 0%nat eb (proc_addr j) b
                         ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
            (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
               goes in and the share it parked comes back in the post, so no
               bundleless out-state stands across the call. *)
            iDestruct (log_opS_named with "Hop") as (ec) "Hop".
            iDestruct (inode_ref_short_gen_forget _ _ _ _ _ _ _ _ Hleck
                     with "Hflck Hckeep") as "Hckeep2".
            iDestruct (off_rows_to_dep with "Hoffrc") as "Hoffdc".
            iApply (IUP.wp_iunlockput_dep_gen γs j γl pd pav pu
                      gilc gislc
 kslot (qq/2)%Qp (qq/2)%Qp gc lock tlc (DepTx (qq/2)%Qp icfg_dev cinum gc lock t (1/2)%Qp) cinum dnc bmc
                      n2 Sb2 false false false ec _ _ pidv (DfracOwn (1/4)) dqb dqs
                      B2 (K - 10)%nat eb b lks
                      U ltac:(exact HKiup) eq_refl Hkslot ltac:(discriminate)
                      ltac:(discriminate)
                      Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hcblk Hcblog Hcinb Hcovb
                      ltac:(exact Hn2ip) Hj Hgs HB2a0 ltac:(lkbelow) eq_refl
                      with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2
                            Hitbl Hescc Hiregi Hiopen Hslkc Hcslkd [//] Hflc Hclaimscr Hcdep Hoffdc
                            Hcidev Hciinum Hcivalid Hcload Hcshotb Hcfrz [$Hckeep2 $Hruc] Hsbb
                            Hsbi Hbmr Hppid Hprocs Hdevi Hgeom Hdlk Hbsl []
                            Hop").
            all: try lkbelow.
            { rewrite Heb /trap_csrs_ext. done. }
            { rewrite Heb /cpu_claim_ext. done. }
            { iEval (cbn beta iota). iEmpIntro. }
            iIntros (CIDU2 HqU2 mu2 n3 Sb3 wf2)
              "%Hcsu2 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
               %Hsb3 %Hwf2 %Hwf2c %Hn3 Hop Hisl2 Htp".
            iDestruct (log_tx_add icfg_log t 1 (1/2) (1/2)
                         (eq_sym Qp.half_half) with "Htp Htx") as "Htw".
            iDestruct (log_tx_full with "Htw") as "Htx".

            assert (Hpcu2 : ret_pc (B2 !!! Regidx Rra : mword 64)
                            = mword_of_int (CK + 0x9e)) by (rewrite HB2ra; pcw).
            iEval (rewrite Hpcu2) in "Hpc".
            assert (Hmu2regs : cr_regs m sp0 ipv (ientry kslot) ty major minor mu2)
              by exact (cr_regs_cs m sp0 _ _ ty major minor B2 mu2 Hcsu2 HB2regs).
            iDestruct ("Hppback" with "Hppid") as "Hpriv".
            (* +0x9e c.li s2,0 *)
            iApply (wp_cli_s_sconf (mword_of_int (CK + 0x9e)) Rs2
                      (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                      mu2 (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                      with "Hcg Hpc []").
            { iApply (cri_09e with "Htext"). }
            iIntros (CIDB3 HqB3) "Hcg Hpc".
            pose (B3 := <[Regidx Rs2 := regval_into_reg
                          (mword_of_int 0 : mword 64)]> mu2).
            change (<[Regidx Rs2 := regval_into_reg
                          (mword_of_int 0 : mword 64)]> mu2) with B3.
            assert (HB3s2 : B3 !!! Regidx Rs2 = (mword_of_int 0 : mword 64))
              by (rewrite /B3; apply upd_eq).
            assert (Hb3v : (mword_of_int 0 : mword 64)
                           = (mword_of_int 0 : mword 64)) by reflexivity.
            assert (HB3regs : cr_regs m sp0 ipv (mword_of_int 0 : mword 64)
                                ty major minor B3)
              by exact (cr_regs_s2 m sp0 ipv _ _ ty major minor mu2 _ Hb3v
                          Hmu2regs).
            assert (Hq0a0 : add_vec_int (mword_of_int (CK + 0x9e) : mword 64) 2
                            = mword_of_int (CK + 0xa0)) by pcw.
            iEval (rewrite Hq0a0) in "Hpc".
            (* +0xa0 c.j +0x70 *)
            assert (Htg070b : add_vec (mword_of_int (CK + 0xa0) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 2024 : mword 11) ('b"0"))))
                      = mword_of_int (CK + 0x70)) by pcw.
            iApply (wp_cj_s_sconf (mword_of_int (CK + 0xa0))
                      (sign_extend' 21
                         (concat_vec (mword_of_int 2024 : mword 11) ('b"0")))
                      B3 (K - 10)%nat b
                      ltac:(rewrite Htg070b; vm_compute; reflexivity)
                      with "Hcg Hpc []").
            { iApply (cri_0a0 with "Htext"). }
            iIntros (CIDB4 HqB4). iApply bi.later_intro. iIntros "Hcg Hpc".
            iEval (rewrite Htg070b) in "Hpc".
            iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2")
              as (nfjb) "Hnb16".
            iPoseProof ("Htail" $! CIDB4) as "Ht".
            iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
            iApply ("Ht" $! B3 u5 nfjb with
                      "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
            { exact (cr_tregs_of_regs m sp0 ipv _ ty major minor B3 HB3regs). }
            iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
            iDestruct (cpu_own_transport CIDU2 CIDf 0%nat eb (proc_addr j) b
                         ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
            iDestruct (iref_slots_combine with "Hisl2 Hisl") as "Hisl".
            iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
            iSpecialize ("Hcontb" $! CIDf with "[%]"); [wp_next_chain |].
            iApply ("Hcontb" $! mf false false 0%nat 1%Qp 1%Qp γf
                      (mword_of_int 0 : mword 32) dnc bmc n3 Sb3
                      (1 + (1 + (ns - 2)))%nat
                      with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv
                            Hpath Hbsl [%] Hisl [%] Hop [$Htx]").
            { exact Hcsf. }
            { exact (cr_slots_2 _ ns eq_refl Hns). }
            { split_and!;
                [exact (cr_sub3 _ _ _ _ Hsb1 Hsb2 Hsb3)
                | exact (cr_le3 _ _ _ _ (proj2 Hn3) (proj2 Hn2) (proj2 Hnp1))
                | discriminate]. }
            { iPureIntro. rewrite Ha0f. exact HB3s2. } }
          (* ===== +0x5a c.li a5,2 ===================================== *)
          iApply (wp_cli_s_sconf (mword_of_int (CK + 0x5a)) Ra5
                    (mword_of_int 2 : mword 6) (mword_of_int 2 : mword 64)
                    mic (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                    with "Hcg Hpc []").
          { iApply (cri_05a with "Htext"). }
          iIntros (CID30 Hq30) "Hcg Hpc".
          pose (F6 := <[Regidx Ra5 := regval_into_reg
                        (mword_of_int 2 : mword 64)]> mic).
          change (<[Regidx Ra5 := regval_into_reg
                        (mword_of_int 2 : mword 64)]> mic) with F6.
          assert (HF6a5 : F6 !!! Regidx Ra5 = (mword_of_int 2 : mword 64))
            by (rewrite /F6; apply upd_eq).
          assert (HF6s4 : F6 !!! Regidx Rs4 = (sign_extend' 64 ty : mword 64))
            by (rewrite /F6 upd_ne; [exact Z20 | nz]).
          assert (HF6s2 : F6 !!! Regidx Rs2 = ientry kslot)
            by (rewrite /F6 upd_ne; [exact Z18 | nz]).
          assert (HF6regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F6)
            by (rewrite /F6; apply cr_regs_caller; [exact Hcsa5 | exact Hmicregs]).
          assert (Hp05c : add_vec_int (mword_of_int (CK + 0x5a) : mword 64) 2
                          = mword_of_int (CK + 0x5c)) by pcw.
          iEval (rewrite Hp05c) in "Hpc".
          assert (Htg098 : add_vec (mword_of_int (CK + 0x5c) : mword 64)
                    (sign_extend' 64 (mword_of_int 60 : mword 13))
                    = mword_of_int (CK + 0x98)) by pcw.
          destruct (decide (ty = T_FILE)) as [Htyf | Htyf].
          -- (* the requested type IS T_FILE: the second test decides *)
             iApply (wp_bne_fall_s_sconf (mword_of_int (CK + 0x5c))
                       (mword_of_int 60 : mword 13) Ra5 Rs4 F6 (K - 10)%nat b
                       ltac:(nz) ltac:(nz)
                       ltac:(rgne; rgne; rewrite HF6a5 HF6s4;
                             exact (cr_tfile_eq _ Htyf))
                       with "Hcg Hpc []").
             { iApply (cri_05c with "Htext"). }
             iIntros (CID31 Hq31) "Hcg Hpc".
             assert (Hp060 : add_vec_int (mword_of_int (CK + 0x5c) : mword 64) 4
                             = mword_of_int (CK + 0x60)) by pcw.
             iEval (rewrite Hp060) in "Hpc".
             iDestruct (ic_loaded_open with "Hcload") as (datc)
        "(%Hciok & %Hrl_datc & %Hcdok & %Hcddix & %Hcdoc & %Hcduq & Hcdlnk & Hcdiat
          & Hcmeta & Hcaddrs & Hcind & Hcblocks & Hctop)".
      iDestruct "Hcmeta" as "(Hcity & Hcimaj & Hcimin & Hcinl & Hcisz)".
             iEval (rewrite /i_type) in "Hcity".
             (* ===== +0x60 lhu a5,68(s2) : ip->type, ZERO-extended ==== *)
             iApply (wp_lhu_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x60)) Ra5 Rs2
                       (mword_of_int 68 : mword 12) F6 (K - 10)%nat
                       (di_type dnc : mword 16) b ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc [] [Hcity]").
             { iApply (cri_060 with "Htext"). }
             { iEval (rgne; rewrite HF6s2). iExact "Hcity". }
             iIntros (CID32 Hq32) "Hcg Hpc Hcity".
             iEval (rgne; rewrite HF6s2) in "Hcity".
             pose (F7 := <[Regidx Ra5 := regval_into_reg
                           (zero_extend' 64 (di_type dnc : mword 16))]> F6).
             change (<[Regidx Ra5 := regval_into_reg
                           (zero_extend' 64 (di_type dnc : mword 16))]> F6) with F7.
             assert (HF7regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F7)
               by (rewrite /F7; apply cr_regs_caller; [exact Hcsa5 | exact HF6regs]).
             assert (Hp064 : add_vec_int (mword_of_int (CK + 0x60) : mword 64) 4
                             = mword_of_int (CK + 0x64)) by pcw.
             iEval (rewrite Hp064) in "Hpc".
             (* ===== +0x64 c.addiw a5,-2 ============================== *)
             iApply (wp_caddiw_s_sconf (mword_of_int (CK + 0x64)) Ra5
                       (mword_of_int 62 : mword 6) F7 (K - 10)%nat b
                       ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
             { iApply (cri_064 with "Htext"). }
             iIntros (CID33 Hq33) "Hcg Hpc".
             pose (F8 := <[Regidx Ra5 := regval_into_reg
                           (sign_extend' 64
                              (subrange_vec_dec
                                 (add_vec (rget F7 Ra5)
                                    (sign_extend' 64
                                       (sign_extend' 12
                                          (mword_of_int 62 : mword 6))))
                                 31 0))]> F7).
             change (<[Regidx Ra5 := regval_into_reg
                           (sign_extend' 64
                              (subrange_vec_dec
                                 (add_vec (rget F7 Ra5)
                                    (sign_extend' 64
                                       (sign_extend' 12
                                          (mword_of_int 62 : mword 6))))
                                 31 0))]> F7) with F8.
             assert (HF8regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F8)
               by (rewrite /F8; apply cr_regs_caller; [exact Hcsa5 | exact HF7regs]).
             assert (Hp066 : add_vec_int (mword_of_int (CK + 0x64) : mword 64) 2
                             = mword_of_int (CK + 0x66)) by pcw.
             iEval (rewrite Hp066) in "Hpc".
             (* ===== +0x66 c.slli a5,48 / +0x68 c.srli a5,48 ========== *)
             iApply (wp_cslli_s_sconf (mword_of_int (CK + 0x66))
                       (Regidx Ra5) Ra5 (mword_of_int 48 : mword 6)
                       F8 (K - 10)%nat b eq_refl ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc []").
             { iApply (cri_066 with "Htext"). }
             iIntros (CID34 Hq34) "Hcg Hpc".
             pose (F9 := <[Regidx Ra5 := regval_into_reg
                           (shift_bits_left (rget F8 Ra5)
                              (subrange_vec_dec (mword_of_int 48 : mword 6)
                                 (Z.sub log2_xlen 1) 0))]> F8).
             change (<[Regidx Ra5 := regval_into_reg
                           (shift_bits_left (rget F8 Ra5)
                              (subrange_vec_dec (mword_of_int 48 : mword 6)
                                 (Z.sub log2_xlen 1) 0))]> F8) with F9.
             assert (HF9regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F9)
               by (rewrite /F9; apply cr_regs_caller; [exact Hcsa5 | exact HF8regs]).
             assert (Hp068 : add_vec_int (mword_of_int (CK + 0x66) : mword 64) 2
                             = mword_of_int (CK + 0x68)) by pcw.
             iEval (rewrite Hp068) in "Hpc".
             iApply (wp_csrli_s_sconf (mword_of_int (CK + 0x68))
                       (Cregidx (mword_of_int 7)) Ra5 (mword_of_int 48 : mword 6)
                       F9 (K - 10)%nat b ltac:(vm_compute; reflexivity)
                       ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
             { iApply (cri_068 with "Htext"). }
             iIntros (CID35 Hq35) "Hcg Hpc".
             pose (FA := <[Regidx Ra5 := regval_into_reg
                           (shift_bits_right (rget F9 Ra5)
                              (subrange_vec_dec (mword_of_int 48 : mword 6)
                                 (Z.sub log2_xlen 1) 0))]> F9).
             change (<[Regidx Ra5 := regval_into_reg
                           (shift_bits_right (rget F9 Ra5)
                              (subrange_vec_dec (mword_of_int 48 : mword 6)
                                 (Z.sub log2_xlen 1) 0))]> F9) with FA.
             assert (HFAregs : cr_regs m sp0 ipv (ientry kslot) ty major minor FA)
               by (rewrite /FA; apply cr_regs_caller; [exact Hcsa5 | exact HF9regs]).
             (* THE THREE ALU LEAVES HAVE LEFT EXACTLY [cr_trange] IN a5.
                Each leaf spells its own output at [rget], so the chain is
                built one equation at a time, and the [rget] the STORED
                VALUE carries is normalised by [rgne] AFTER the [upd_eq]
                that exposes it.  It must be [rgne] and not a hand-written
                bridge: [rget] is HART-INDEXED, the leaf's output names the
                REBOUND hart, and an equation written fresh in the proof
                means the SECTION one -- so the two print identically and
                do not rewrite (durable-notes).  [cr_trange] then closes by
                conversion, which is the whole reason it was named. *)
             assert (HF7a5 : F7 !!! Regidx Ra5
                             = (zero_extend' 64 (di_type dnc : mword 16)
                                : mword 64))
               by (rewrite /F7; apply upd_eq).
             assert (HF8a5 : F8 !!! Regidx Ra5
                             = sign_extend' 64
                                 (subrange_vec_dec
                                    (add_vec (zero_extend' 64
                                                (di_type dnc : mword 16)
                                              : mword 64)
                                       (sign_extend' 64
                                          (sign_extend' 12
                                             (mword_of_int 62 : mword 6))))
                                    31 0)).
             { rewrite /F8 upd_eq. rgne. rewrite HF7a5. reflexivity. }
             assert (HF9a5 : F9 !!! Regidx Ra5
                             = shift_bits_left
                                 (sign_extend' 64
                                    (subrange_vec_dec
                                       (add_vec (zero_extend' 64
                                                   (di_type dnc : mword 16)
                                                 : mword 64)
                                          (sign_extend' 64
                                             (sign_extend' 12
                                                (mword_of_int 62 : mword 6))))
                                       31 0))
                                 (subrange_vec_dec (mword_of_int 48 : mword 6)
                                    (Z.sub log2_xlen 1) 0)).
             { rewrite /F9 upd_eq. rgne. rewrite HF8a5. reflexivity. }
             assert (HFAa5 : FA !!! Regidx Ra5 = cr_trange (di_type dnc)).
             { rewrite /FA upd_eq. rgne. rewrite HF9a5 /cr_trange. reflexivity. }
             assert (Hp06a : add_vec_int (mword_of_int (CK + 0x68) : mword 64) 2
                             = mword_of_int (CK + 0x6a)) by pcw.
             iEval (rewrite Hp06a) in "Hpc".
             (* ===== +0x6a c.li a4,1 ================================== *)
             iApply (wp_cli_s_sconf (mword_of_int (CK + 0x6a)) Ra4
                       (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                       FA (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                       with "Hcg Hpc []").
             { iApply (cri_06a with "Htext"). }
             iIntros (CID36 Hq36) "Hcg Hpc".
             pose (FB := <[Regidx Ra4 := regval_into_reg
                           (mword_of_int 1 : mword 64)]> FA).
             change (<[Regidx Ra4 := regval_into_reg
                           (mword_of_int 1 : mword 64)]> FA) with FB.
             assert (HFBa4 : FB !!! Regidx Ra4 = (mword_of_int 1 : mword 64))
               by (rewrite /FB; apply upd_eq).
             assert (HFBa5 : FB !!! Regidx Ra5 = cr_trange (di_type dnc))
               by (rewrite /FB upd_ne; [exact HFAa5 | nz]).
             assert (HFBs2 : FB !!! Regidx Rs2 = ientry kslot).
             { rewrite /FB upd_ne; [| nz]. rewrite /FA upd_ne; [| nz].
               rewrite /F9 upd_ne; [| nz]. rewrite /F8 upd_ne; [| nz].
               rewrite /F7 upd_ne; [exact HF6s2 | nz]. }
             assert (HFBregs : cr_regs m sp0 ipv (ientry kslot) ty major minor FB)
               by (rewrite /FB; apply cr_regs_caller; [exact Hcsa4 | exact HFAregs]).
             assert (Hp06c : add_vec_int (mword_of_int (CK + 0x6a) : mword 64) 2
                             = mword_of_int (CK + 0x6c)) by pcw.
             iEval (rewrite Hp06c) in "Hpc".
             assert (Htg098b : add_vec (mword_of_int (CK + 0x6c) : mword 64)
                       (sign_extend' 64 (mword_of_int 44 : mword 13))
                       = mword_of_int (CK + 0x98)) by pcw.
             iAssert (inode_meta (ientry kslot) dnc)
               with "[Hcity Hcimaj Hcimin Hcinl Hcisz]" as "Hcmetal".
             { rewrite /inode_meta /i_type. iFrame. }
             iDestruct (ic_mk_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kslot cinum dnc bmc
                          datc Hciok Hrl_datc Hcdok Hcddix Hcdoc Hcduq
                          with "Hcdlnk Hcdiat Hcmetal Hcaddrs Hcind Hcblocks
                                Hctop")
               as "Hcload".
             destruct (zopz0zI_u (mword_of_int 1 : mword 64)
                         (cr_trange (di_type dnc))) eqn:Hrng.
             ++ (* ===== ARM F-BAD (second entry): the type is out of
                    range, so the found inode is a directory or free ==== *)
                iApply (wp_bltu_taken_s_sconf (mword_of_int (CK + 0x6c))
                          (mword_of_int 44 : mword 13) Ra5 Ra4 FB (K - 10)%nat b
                          ltac:(nz) ltac:(nz)
                          ltac:(rgne; rgne; rewrite HFBa4 HFBa5; exact Hrng)
                          ltac:(rewrite Htg098b; vm_compute; reflexivity)
                          with "Hcg Hpc []").
                { iApply (cri_06c with "Htext"). }
                iIntros (CID37 Hq37). iApply bi.later_intro. iIntros "Hcg Hpc".
                iEval (rewrite Htg098b) in "Hpc".
                iDestruct (cpu_own_transport CIDic CID37 0%nat eb
                             (proc_addr j) b
                             ltac:(rewrite Hb; wp_next_chain) with "Hcnt")
                  as "Hcnt".
                iPoseProof ("Hfbad" $! CID37) as "Hfb".
                iSpecialize ("Hfb" with "[%]"); [wp_next_chain |].
                iApply ("Hfb" $! FB with
                          "[%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                           Hnb14 Hnb2 Hcslkd Hcdep Hoffrc Hcidev Hciinum
                           Hcivalid Hcload Hcshot Hcfrz Hckeep Hruc Hsbn Hsbi Hsbs
                           Hsbb
                           Hppid Hppback Hpath Hbsl Hisl Hislr Hop Htx Hcont").
                { exact HFBregs. }
             ++ (* ===== ARM F-OK: the found inode is a file or a device *)
                iApply (wp_bltu_fall_s_sconf (mword_of_int (CK + 0x6c))
                          (mword_of_int 44 : mword 13) Ra5 Ra4 FB (K - 10)%nat b
                          ltac:(nz) ltac:(nz)
                          ltac:(rgne; rgne; rewrite HFBa4 HFBa5; exact Hrng)
                          with "Hcg Hpc []").
                { iApply (cri_06c with "Htext"). }
                iIntros (CID37 Hq37) "Hcg Hpc".
                assert (Hp070 : add_vec_int (mword_of_int (CK + 0x6c) : mword 64) 4
                                = mword_of_int (CK + 0x70)) by pcw.
                iEval (rewrite Hp070) in "Hpc".
                iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2")
                  as (nfj) "Hnb16".
                iDestruct ("Hppback" with "Hppid") as "Hpriv".
                iPoseProof ("Htail" $! CID37) as "Ht".
                iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
                iApply ("Ht" $! FB u5 nfj with
                          "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
                { exact (cr_tregs_of_regs m sp0 ipv _ ty major minor FB HFBregs). }
                iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
                iDestruct (cpu_own_transport CIDic CIDf 0%nat eb (proc_addr j) b
                             ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
                iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
                iDestruct (ic_tx_dep_intro with "Hcdep Htx") as "Hcdep".
                iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
                iApply ("Hcont" $! mf true false kslot (qq/2)%Qp (qq/2)%Qp gc
                          cinum dnc bmc n2 Sb2 (1 + (ns - 2))%nat
                          with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv
                                Hpath Hbsl [%] Hisl [%] Hop [Hcslkd Hcdep Hoffrc
                                Hcidev Hciinum Hcivalid Hcload Hcfrz Hckeep Hruc]").
                { exact Hcsf. }
                { exact (cr_slots_1 _ ns eq_refl Hns). }
                { split_and!;
                    [exact (cr_sub2 _ _ _ Hsb1 Hsb2)
                    | exact (cr_le2 _ _ _ (proj2 Hn2) (proj2 Hnp1))
                    | intros _; exact Hn2ip]. }
                iSplitR.
                { iPureIntro. split; [rewrite Ha0f; exact HFBs2 |].
                  split; [exact Hkslot |].
                  split; [split; [exact Hcpos | exact Hcinb] |].
                  split; [exact Htyf |].
                  exact (cr_trange_in (di_type dnc) Hrng). }
                iApply (create_locked_mk
                          _ _ _ _ _ _ _ _ gilc gislc eq_refl
                          with "Hslkc Hcslkd [Hcdep] Hoffrc Hcidev Hciinum
                                Hcivalid Hcload Hcshot Hcfrz [Hckeep] Hruc").
                { iExists lock, tlc. iSplitR; [by iPureIntro|].
                  iFrame "Hflc Hcdep". }
                { iExists lock, tlck. iSplitR; [by iPureIntro|].
                  iFrame "Hflck Hckeep". }
          -- (* ===== ARM F-BAD (first entry): type != T_FILE ========== *)
             iApply (wp_bne_taken_s_sconf (mword_of_int (CK + 0x5c))
                       (mword_of_int 60 : mword 13) Ra5 Rs4 F6 (K - 10)%nat b
                       ltac:(nz) ltac:(nz)
                       ltac:(rgne; rgne; rewrite HF6a5 HF6s4;
                             exact (cr_tfile_ne _ Htyf))
                       ltac:(rewrite Htg098; vm_compute; reflexivity)
                       with "Hcg Hpc []").
             { iApply (cri_05c with "Htext"). }
             iIntros (CID31 Hq31). iApply bi.later_intro. iIntros "Hcg Hpc".
             iEval (rewrite Htg098) in "Hpc".
             iDestruct (cpu_own_transport CIDic CID31 0%nat eb
                          (proc_addr j) b
                          ltac:(rewrite Hb; wp_next_chain) with "Hcnt")
               as "Hcnt".
             iPoseProof ("Hfbad" $! CID31) as "Hfb".
             iSpecialize ("Hfb" with "[%]"); [wp_next_chain |].
             iApply ("Hfb" $! F6 with
                       "[%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                        Hnb14 Hnb2 Hcslkd Hcdep Hoffrc Hcidev Hciinum
                        Hcivalid Hcload Hcshot Hcfrz Hckeep Hruc Hsbn Hsbi Hsbs
                        Hsbb
                        Hppid Hppback Hpath Hbsl Hisl Hislr Hop Htx Hcont").
             { exact HF6regs. }
        * (* ========================================================== *)
          (*  THE NAME IS NOT THERE -- the ALLOCATE half, PARKED         *)
          (* ========================================================== *)
          iDestruct "Hres2" as "((%Hnone & %Hdla0) & Hisl1 & _)".
          (* +0x4a c.mv s2,a0 : s2 := 0, and it STAYS 0 all the way to
             +0xe6 / +0xf2 -- the live invariant the failure arms use. *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x4a)) Rs2 Ra0 mdl
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (cri_04a with "Htext"). }
          iIntros (CID24 Hq24) "Hcg Hpc". iEval (rgne) in "Hcg".
          pose (A1 := <[Regidx Rs2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mdl !!! Regidx Ra0))]> mdl).
          change (<[Regidx Rs2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mdl !!! Regidx Ra0))]> mdl) with A1.
          assert (Ha1v : add_vec (zero_reg : mword 64) (mdl !!! Regidx Ra0)
                         = (mword_of_int 0 : mword 64))
            by (rewrite Hdla0; apply add_vec_zero_l).
          assert (HA1a0 : A1 !!! Regidx Ra0 = (mdl !!! Regidx Ra0 : mword 64))
            by (rewrite /A1 upd_ne; [reflexivity | nz]).
          assert (HA1regs : cr_regs m sp0 ipv (mword_of_int 0 : mword 64)
                              ty major minor A1)
            by exact (cr_regs_s2 m sp0 ipv _ _ ty major minor mdl _ Ha1v
                        Hmdlregs).
          iEval (rewrite Hp04c) in "Hpc".
          (* ===== +0x4c c.beqz a0 : TAKEN -> the allocate half ======== *)
          iApply (wp_cbeqz_taken_s_sconf (mword_of_int (CK + 0x4c))
                    (mword_of_int 43 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                    A1 (K - 10)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HA1a0 Hdla0;
                          apply (proj2 (eq_vec_true_iff _ _));
                          exact dlk_zero_moi)
                    ltac:(rewrite Htg0a2; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_04c with "Htext"). }
          iIntros (CID25 Hq25). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htg0a2) in "Hpc".
          iDestruct ("Hppback" with "Hppid") as "Hpriv".
          iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
            [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
          iDestruct (iref_slots_combine with "Hisl1 Hislr") as "Hisl".
          assert (Hns1 : (1 + (ns - 2))%nat = (ns - 1)%nat)
            by exact (cr_ns_1 ns Hns).
          iEval (rewrite Hns1) in "Hisl".
          iDestruct (cpu_own_transport CIDdl CID25 0%nat eb (proc_addr j) b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          iPoseProof ("Halloc" $! CID25) as "Ha".
          iSpecialize ("Ha" with "[%]"); [wp_next_chain |].
          iAssert (∃ lo tl : nat,
              ⌜(lo <= tl)%nat⌝ ∗ IcacheRef.cred_floor lo tl ∗
              IcacheRef.inode_ref_short_genlo kd (qd/2 + qd/2)%Qp (qd/2)%Qp
                icfg_dev dind gd lo)%I with "[Hkeep]" as "Hkeep".
          { iExists lod, tld. iSplitR; [by iPureIntro|]. iFrame "Hfld Hkeep". }
          iApply ("Ha" $! A1 u5 kd qd gd gild gisld dind dnl bml datl nfp nf0
                    n1 Sb1 w t
                    with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                          [%] [%] [%]
                          Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                          Hnb14 Hnb2 Hslkd Hslkdd [Hdep] Hoffr Hidev Hiinum
                          Hivalid Hdlnk Hdiat Hmeta Hmap Hblocks Htop Hshotl Hfrzl Hkeep Hrud
                          Hsbn Hsbi Hsbs Hsbb Hbmr Hpriv Hpath Hbsl Hisl Hop Htx
                          Hcont").
          { rewrite -Hie. exact HA1regs. }
          { exact Hkd. }
          { exact Hdib'. }
          { exact Htydir. }
          { exact Hnl0. }
          { exact Hnlmax. }
          { exact Hiok. }
          {exact Hdok. }
          { exact Hddix. }
          { exact Hduq. }
          { exact Hrl_datl. }
          { exact Hnpname. }
          { exact Hnone. }
          { exact Hsb1. }
          { exact Hwmem. }
          { exact Hnp1. }
          { iExists lod, tld. iSplitR; [by iPureIntro|]. iFrame "Hfld Hdep". }
          - (* ===== ARM G2: the guard FIRES -- the parent is a full ====
               directory and the caller asked for another one.  The block
               is ARM G's, at +0x8e, and it closes the same way: the
               [iunlockput(dp)] runs uncredited and the answer is 0.  What
               differs is only the hypothesis it is under -- [nlink] is
               32767 here rather than 0 -- and no step below reads it. *)
            iIntros (CIDg) "%Hqg". iIntros (Mg) "%HMgregs Hcg Hpc".
            pose proof HMgregs as HMgR.
            destruct HMgR as (V2 & V8 & V9 & V18 & V20 & V21 & V22 & Vthr).
        (* Same fix as this file's other [ic_loaded] sites: assembled by
           the constructor, not by [iFrame], which would re-search the
           whole function context against the 268-element [inode_blocks]
           big-op. *)
        iAssert (inode_meta (ientry kd) dnl)
          with "[Hity Himaj Himin Hinl Hisz]" as "Hmetal".
        { rewrite /inode_meta /i_type /i_nlink. iFrame. }
        iDestruct (ic_mk_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kd dind dnl bml datl
                     Hiok Hrl_datl Hdok Hddix Hdoc Hduq
                     with "Hdlnk Hdiat Hmetal Haddrs Hind Hblocks Htop")
          as "Hload".
        iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
          [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
        (* +0x8e c.mv a0,s1 *)
        iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x8e)) Ra0 Rs1 Mg
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_08e with "Htext"). }
        iIntros (CID20 Hq20) "Hcg Hpc". iEval (rgne) in "Hcg".
        pose (J1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (Mg !!! Regidx Rs1))]> Mg).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (Mg !!! Regidx Rs1))]> Mg) with J1.
        assert (HJ1a0 : J1 !!! Regidx Ra0 = ientry kd).
        { rewrite /J1 upd_eq.
          rewrite V9 Hie. apply add_vec_zero_l. }
        assert (HJ1regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor J1)
          by (rewrite /J1; apply cr_regs_caller; [exact Hcsa0 | exact HMgregs]).
        assert (Hp090 : add_vec_int (mword_of_int (CK + 0x8e) : mword 64) 2
                        = mword_of_int (CK + 0x90)) by pcw.
        iEval (rewrite Hp090) in "Hpc".
        (* +0x90 jal iunlockput (dp) -- AT crb = cru = crz = false.
           [crz] is unavailable BY CONSTRUCTION on this arm: it is bought
           with [InodeRegion.nlz_obs], minted only at a NONZERO nlink
           observation, and this arm IS the zero observation. *)
        assert (HtgupG : add_vec (mword_of_int (CK + 0x90) : mword 64)
                  (sign_extend' 64 (mword_of_int 2091026 : mword 21))
                  = mword_of_int KernelSyms.iunlockput) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0x90)) Rra
                  (mword_of_int 2091026 : mword 21) J1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_090 with "Htext"). }
        iIntros (CID21 Hq21) "Hcg Hpc".
        iEval (rewrite HtgupG) in "Hpc".
        pose (J2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x90) : mword 64) 4)]> J1).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x90) : mword 64) 4)]> J1) with J2.
        assert (HJ2ra : J2 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CK + 0x90) : mword 64) 4)
          by (rewrite /J2; apply upd_eq).
        assert (HJ2a0 : J2 !!! Regidx Ra0 = ientry kd)
          by (rewrite /J2 upd_ne; [exact HJ1a0 | nz]).
        assert (HJ2regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor J2)
          by (rewrite /J2; apply cr_regs_caller; [exact Hcsra | exact HJ1regs]).
        iDestruct (cpu_own_transport CIDil CID21 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
           goes in and the share it parked comes back in the post, so no
           bundleless out-state stands across the call. *)
        iDestruct (log_opS_named with "Hop") as (e0) "Hop".
        iDestruct (inode_ref_short_gen_forget _ _ _ _ _ _ _ _ Hled
                     with "Hfld Hkeep") as "Hkeep2".
        iDestruct (off_rows_to_dep with "Hoffr") as "Hoffd".
        iApply (IUP.wp_iunlockput_dep_gen γs j γl pd pav pu
                  gild gisld
                  kd (qd/2)%Qp (qd/2)%Qp gd lod tld (DepTx (qd/2)%Qp icfg_dev dind gd lod t (1/2)%Qp) dind dnl bml n1 Sb1
                  false false false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
                  J2 (K - 10)%nat eb b lks
                  U ltac:(exact HKiup) eq_refl Hkd ltac:(discriminate) ltac:(discriminate)
                  Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib' Hcovb
                  ltac:(exact Hn1ip) Hj Hgs HJ2a0 ltac:(lkbelow) eq_refl
                  with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                        Hescd Hiregi Hiopen Hslkd Hslkdd [//] Hfld Hclaimscr Hdep Hoffd Hidev Hiinum
                        Hivalid Hload Hshotl Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr Hppid
                        Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
        all: try lkbelow.
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { iEval (cbn beta iota). iEmpIntro. }
        iIntros (CIDup Hqup mup n2 Sb2 wg)
          "%Hcsup Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
           %Hsb2 %Hwg %Hwgc %Hn2 Hop Hisl Htp".
        iDestruct (log_tx_add icfg_log t 1 (1/2) (1/2)
                     (eq_sym Qp.half_half) with "Htp Htx") as "Htw".
        iDestruct (log_tx_full with "Htw") as "Htx".

        assert (Hpcup : ret_pc (J2 !!! Regidx Rra : mword 64)
                        = mword_of_int (CK + 0x94)) by (rewrite HJ2ra; pcw).
        iEval (rewrite Hpcup) in "Hpc".
        assert (Hmupregs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                             ty major minor mup)
          by exact (cr_regs_cs m sp0 _ _ ty major minor J2 mup Hcsup HJ2regs).
        iDestruct ("Hppback" with "Hppid") as "Hpriv".
        (* +0x94 c.li s2,0 *)
        iApply (wp_cli_s_sconf (mword_of_int (CK + 0x94)) Rs2
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  mup (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc []").
        { iApply (cri_094 with "Htext"). }
        iIntros (CID22 Hq22) "Hcg Hpc".
        pose (J3 := <[Regidx Rs2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> mup).
        change (<[Regidx Rs2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> mup) with J3.
        assert (HJ3s2 : J3 !!! Regidx Rs2 = (mword_of_int 0 : mword 64))
          by (rewrite /J3; apply upd_eq).
        assert (Hg2v : (mword_of_int 0 : mword 64) = (mword_of_int 0 : mword 64))
          by reflexivity.
        assert (HJ3regs : cr_regs m sp0 ipv (mword_of_int 0 : mword 64)
                            ty major minor J3)
          by exact (cr_regs_s2 m sp0 ipv _ _ ty major minor mup _
                      Hg2v Hmupregs).
        assert (Hp096 : add_vec_int (mword_of_int (CK + 0x94) : mword 64) 2
                        = mword_of_int (CK + 0x96)) by pcw.
        iEval (rewrite Hp096) in "Hpc".
        (* +0x96 c.j +0x70 *)
        assert (Htg070h : add_vec (mword_of_int (CK + 0x96) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 2029 : mword 11) ('b"0"))))
                  = mword_of_int (CK + 0x70)) by pcw.
        iApply (wp_cj_s_sconf (mword_of_int (CK + 0x96))
                  (sign_extend' 21 (concat_vec (mword_of_int 2029 : mword 11) ('b"0")))
                  J3 (K - 10)%nat b
                  ltac:(rewrite Htg070h; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_096 with "Htext"). }
        iIntros (CID23 Hq23). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg070h) in "Hpc".
        iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2") as (nfj) "Hnb16".
        iPoseProof ("Htail" $! CID23) as "Ht".
        iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
        iApply ("Ht" $! J3 u5 nfj with
                  "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
        { exact (cr_tregs_of_regs m sp0 ipv _ ty major minor J3 HJ3regs). }
        iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
        iDestruct (cpu_own_transport CIDup CIDf 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* the slot ledger comes back whole: nameiparent took two and gave
           one back, and this [iunlockput] gave the other. *)
        iDestruct (iref_slots_combine with "Hisl1 Hisl") as "Hisl".
        iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
        iEval (rewrite -Hnsplit) in "Hisl".
        iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
                  (mword_of_int 0 : mword 32) dnl bml n2 Sb2 ns
                  with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv Hpath
                        Hbsl [%] Hisl [%] Hop [$Htx]").
        { exact Hcsf. }
        { exact (cr_slots_ns _ ns eq_refl Hns). }
        { split_and!; [exact (cr_sub2 _ _ _ Hsb1 Hsb2)
                      | exact (cr_le2 _ _ _ (proj2 Hn2) (proj2 Hnp1))
                      | discriminate]. }
        { iPureIntro. rewrite Ha0f. exact HJ3s2. }
        }
        (* ===== +0x30 c.lui a4,0xffff8 ================================= *)
        iApply (wp_clui_s_sconf (mword_of_int (CK + 0x30)) Ra4
                  (sign_extend' 20 (mword_of_int 56 : mword 6))
                  (mword_of_int (-32768) : mword 64) Q3 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_030 with "Htext"). }
        iIntros (CID20 Hq20) "Hcg Hpc".
        pose (N1 := <[Regidx Ra4 := regval_into_reg
                      (mword_of_int (-32768) : mword 64)]> Q3).
        change (<[Regidx Ra4 := regval_into_reg
                      (mword_of_int (-32768) : mword 64)]> Q3) with N1.
        assert (HN1a4 : N1 !!! Regidx Ra4 = (mword_of_int (-32768) : mword 64))
          by (rewrite /N1; apply upd_eq).
        assert (HN1a5 : N1 !!! Regidx Ra5
                        = (sign_extend' 64 (di_nlink dnl : mword 16) : mword 64))
          by (rewrite /N1 upd_ne; [exact HQ3a5 | nz]).
        assert (HN1regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor N1)
          by (rewrite /N1; apply cr_regs_caller; [exact Hcsa4 | exact HQ3regs]).
        assert (Hp032 : add_vec_int (mword_of_int (CK + 0x30) : mword 64) 2
                        = mword_of_int (CK + 0x32)) by pcw.
        iEval (rewrite Hp032) in "Hpc".
        (* ===== +0x32 c.addi a4,a4,1 : a4 = -NLINK_MAX ================= *)
        iApply (wp_caddi_s_sconf (mword_of_int (CK + 0x32)) Ra4
                  (mword_of_int 1 : mword 6) N1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_032 with "Htext"). }
        iIntros (CID21 Hq21) "Hcg Hpc". iEval (rgne) in "Hcg".
        pose (N2 := <[Regidx Ra4 := regval_into_reg
                      (add_vec (N1 !!! Regidx Ra4)
                         (sign_extend' 64
                            (sign_extend' 12 (mword_of_int 1 : mword 6))))]> N1).
        change (<[Regidx Ra4 := regval_into_reg
                      (add_vec (N1 !!! Regidx Ra4)
                         (sign_extend' 64
                            (sign_extend' 12 (mword_of_int 1 : mword 6))))]> N1) with N2.
        assert (HN2a4 : N2 !!! Regidx Ra4 = (mword_of_int (-32767) : mword 64)).
        { rewrite /N2 upd_eq HN1a4. apply bv_eq; vm_compute; reflexivity. }
        assert (HN2a5 : N2 !!! Regidx Ra5
                        = (sign_extend' 64 (di_nlink dnl : mword 16) : mword 64))
          by (rewrite /N2 upd_ne; [exact HN1a5 | nz]).
        assert (HN2regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor N2)
          by (rewrite /N2; apply cr_regs_caller; [exact Hcsa4 | exact HN1regs]).
        assert (Hp034 : add_vec_int (mword_of_int (CK + 0x32) : mword 64) 2
                        = mword_of_int (CK + 0x34)) by pcw.
        iEval (rewrite Hp034) in "Hpc".
        (* ===== +0x34 c.add a5,a5,a4 : a5 = nlink - NLINK_MAX ========== *)
        iApply (wp_cadd_s_sconf (mword_of_int (CK + 0x34)) Ra5 Ra4
                  N2 (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_034 with "Htext"). }
        iIntros (CID22 Hq22) "Hcg Hpc". iEval (rgne; rgne) in "Hcg".
        pose (N3 := <[Regidx Ra5 := regval_into_reg
                      (add_vec (N2 !!! Regidx Ra5) (N2 !!! Regidx Ra4))]> N2).
        change (<[Regidx Ra5 := regval_into_reg
                      (add_vec (N2 !!! Regidx Ra5) (N2 !!! Regidx Ra4))]> N2) with N3.
        assert (HN3a5 : N3 !!! Regidx Ra5
                        = add_vec
                            (sign_extend' 64 (di_nlink dnl : mword 16) : mword 64)
                            (mword_of_int (-32767) : mword 64)).
        { rewrite /N3 upd_eq HN2a5 HN2a4. reflexivity. }
        assert (HN3regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor N3)
          by (rewrite /N3; apply cr_regs_caller; [exact Hcsa5 | exact HN2regs]).
        pose proof HN3regs as HN3R.
        destruct HN3R as (_ & _ & _ & _ & HN3s4 & _ & _ & _).
        assert (Hp036 : add_vec_int (mword_of_int (CK + 0x34) : mword 64) 2
                        = mword_of_int (CK + 0x36)) by pcw.
        iEval (rewrite Hp036) in "Hpc".
        assert (Htg03e : add_vec (mword_of_int (CK + 0x36) : mword 64)
                  (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 4 : mword 8) ('b"0"))))
                  = mword_of_int (CK + 0x3e)) by pcw.
        destruct (decide (di_nlink dnl = (mword_of_int 32767 : mword 16)))
          as [Hnlm | Hnlm].
        * (* ---- the count IS at NLINK_MAX: on to the type test ------- *)
          iApply (wp_cbnez_fall_s_sconf (mword_of_int (CK + 0x36))
                    (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                    N3 (K - 10)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HN3a5; exact (cr_nlmax_eq _ Hnlm))
                    with "Hcg Hpc []").
          { iApply (cri_036 with "Htext"). }
          iIntros (CID23 Hq23) "Hcg Hpc".
          assert (Hp038 : add_vec_int (mword_of_int (CK + 0x36) : mword 64) 2
                          = mword_of_int (CK + 0x38)) by pcw.
          iEval (rewrite Hp038) in "Hpc".
          (* ===== +0x38 addi a5,s4,-1 : a5 = type - T_DIR ============== *)
          iApply (wp_addi4_s_sconf (mword_of_int (CK + 0x38)) Ra5 Rs4
                    (mword_of_int 4095 : mword 12) N3 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (cri_038 with "Htext"). }
          iIntros (CID24 Hq24) "Hcg Hpc". iEval (rgne) in "Hcg".
          pose (N4 := <[Regidx Ra5 := regval_into_reg
                        (add_vec (N3 !!! Regidx Rs4)
                           (sign_extend' 64 (mword_of_int 4095 : mword 12)))]> N3).
          change (<[Regidx Ra5 := regval_into_reg
                        (add_vec (N3 !!! Regidx Rs4)
                           (sign_extend' 64 (mword_of_int 4095 : mword 12)))]> N3) with N4.
          assert (HN4a5 : N4 !!! Regidx Ra5
                          = add_vec (sign_extend' 64 ty : mword 64)
                              (sign_extend' 64
                                 (mword_of_int 4095 : mword 12) : mword 64)).
          { rewrite /N4 upd_eq HN3s4. reflexivity. }
          assert (HN4regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                              ty major minor N4)
            by (rewrite /N4; apply cr_regs_caller; [exact Hcsa5 | exact HN3regs]).
          assert (Hp03c : add_vec_int (mword_of_int (CK + 0x38) : mword 64) 4
                          = mword_of_int (CK + 0x3c)) by pcw.
          iEval (rewrite Hp03c) in "Hpc".
          assert (Htg08e : add_vec (mword_of_int (CK + 0x3c) : mword 64)
                    (sign_extend' 64 (sign_extend' 13
                       (concat_vec (mword_of_int 41 : mword 8) ('b"0"))))
                    = mword_of_int (CK + 0x8e)) by pcw.
          destruct (decide (ty = SpecDirlookup.T_DIR)) as [Htdirg | Htdirg].
          ** (* ---- ARM G2: a new DIRECTORY under a full parent ------- *)
             iApply (wp_cbeqz_taken_s_sconf (mword_of_int (CK + 0x3c))
                       (mword_of_int 41 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                       N4 (K - 10)%nat b
                       ltac:(vm_compute; reflexivity) ltac:(nz)
                       ltac:(rgne; rewrite HN4a5; exact (cr_tym1_eq _ Htdirg))
                       ltac:(rewrite Htg08e; vm_compute; reflexivity)
                       with "Hcg Hpc []").
             { iApply (cri_03c with "Htext"). }
             iIntros (CID25 Hq25). iApply bi.later_intro. iIntros "Hcg Hpc".
             iEval (rewrite Htg08e) in "Hpc".
             iDestruct "Hgate" as "[_ Hg2]".
             iSpecialize ("Hg2" $! CID25 with "[%]"); [wp_next_chain |].
             iApply ("Hg2" $! N4 with "[%] Hcg Hpc").
             { exact HN4regs. }
          ** (* ---- not a directory: the gate does not apply ---------- *)
             iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CK + 0x3c))
                       (mword_of_int 41 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                       N4 (K - 10)%nat b
                       ltac:(vm_compute; reflexivity) ltac:(nz)
                       ltac:(rgne; rewrite HN4a5; exact (cr_tym1_ne _ Htdirg))
                       with "Hcg Hpc []").
             { iApply (cri_03c with "Htext"). }
             iIntros (CID25 Hq25) "Hcg Hpc".
             assert (Hp03e : add_vec_int (mword_of_int (CK + 0x3c) : mword 64) 2
                             = mword_of_int (CK + 0x3e)) by pcw.
             iEval (rewrite Hp03e) in "Hpc".
             iDestruct "Hgate" as "[Hj _]".
             iSpecialize ("Hj" $! CID25 with "[%]"); [wp_next_chain |].
             iApply ("Hj" $! N4 with "[%] [%] Hcg Hpc").
             { exact HN4regs. }
             { intros Hc. exfalso. exact (Htdirg Hc). }
        * (* ---- the count is below NLINK_MAX: jump the type test ----- *)
          iApply (wp_cbnez_taken_s_sconf (mword_of_int (CK + 0x36))
                    (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                    N3 (K - 10)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HN3a5; exact (cr_nlmax_ne _ Hnlm))
                    ltac:(rewrite Htg03e; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_036 with "Htext"). }
          iIntros (CID23 Hq23). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htg03e) in "Hpc".
          iDestruct "Hgate" as "[Hj _]".
          iSpecialize ("Hj" $! CID23 with "[%]"); [wp_next_chain |].
          iApply ("Hj" $! N3 with "[%] [%] Hcg Hpc").
          { exact HN3regs. }
          { intros _. exact Hnlm. }
    - (* ============================================================== *)
      (*  ARM N: nameiparent returned 0                                  *)
      (* ============================================================== *)
      iDestruct "Hres" as "(%Hnpa0 & Hisl2)".
      iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (CK + 0x22))
                (mword_of_int 318 : mword 13) Ra0 Q1 (K - 10)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite HQ1a0 Hnpa0;
                      apply (proj2 (eq_vec_true_iff _ _)); exact dlk_zero_moi)
                ltac:(rewrite Htg160; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_022 with "Htext"). }
      iIntros (CID16 Hq16). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htg160) in "Hpc".
      assert (Hs1v : add_vec (zero_reg : mword 64) (mnp !!! Regidx Ra0)
                     = (mword_of_int 0 : mword 64))
        by (rewrite Hnpa0; apply add_vec_zero_l).
      assert (HQ1regs : cr_regs m sp0 (mword_of_int 0 : mword 64)
                          (m !!! Regidx Rs2 : mword 64) ty major minor Q1)
        by exact (cr_regs_s1 m sp0 (m !!! Regidx Rs1 : mword 64)
                    (mword_of_int 0 : mword 64) (m !!! Regidx Rs2 : mword 64)
                    ty major minor mnp _ Hs1v Hmnpregs).
      (* +0x160 c.mv s2,a0 (a0 = 0) *)
      iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x160)) Rs2 Ra0 Q1
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cri_160 with "Htext"). }
      iIntros (CID17 Hq17) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (N1 := <[Regidx Rs2 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Q1 !!! Regidx Ra0))]> Q1).
      change (<[Regidx Rs2 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Q1 !!! Regidx Ra0))]> Q1) with N1.
      assert (HN1s2 : N1 !!! Regidx Rs2 = (mword_of_int 0 : mword 64)).
      { rewrite /N1 upd_eq. rewrite HQ1a0 Hnpa0. apply add_vec_zero_l. }
      assert (Hs2v : add_vec (zero_reg : mword 64) (Q1 !!! Regidx Ra0)
                     = (mword_of_int 0 : mword 64))
        by (rewrite HQ1a0 Hnpa0; apply add_vec_zero_l).
      assert (HN1regs : cr_regs m sp0 (mword_of_int 0 : mword 64)
                          (mword_of_int 0 : mword 64) ty major minor N1)
        by exact (cr_regs_s2 m sp0 _ _ _ ty major minor Q1 _ Hs2v HQ1regs).
      assert (Hp162 : add_vec_int (mword_of_int (CK + 0x160) : mword 64) 2
                      = mword_of_int (CK + 0x162)) by pcw.
      iEval (rewrite Hp162) in "Hpc".
      (* +0x162 c.j +0x70 *)
      assert (Htg070n : add_vec (mword_of_int (CK + 0x162) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 1927 : mword 11) ('b"0"))))
                = mword_of_int (CK + 0x70)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (CK + 0x162))
                (sign_extend' 21 (concat_vec (mword_of_int 1927 : mword 11) ('b"0")))
                N1 (K - 10)%nat b
                ltac:(rewrite Htg070n; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_162 with "Htext"). }
      iIntros (CID18 Hq18). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htg070n) in "Hpc".
      iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2") as (nfj) "Hnb16".
      iPoseProof ("Htail" $! CID18) as "Ht".
      iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
      iApply ("Ht" $! N1 u5 nfj with
                "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
      { exact (cr_tregs_of_regs m sp0 _ _ ty major minor N1 HN1regs). }
      iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
      iDestruct (cpu_own_transport CIDnp CIDf 0%nat eb (proc_addr j) b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (iref_slots_combine with "Hisl2 Hislr") as "Hisl".
      iEval (rewrite -Hnsplit) in "Hisl".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
                (mword_of_int 0 : mword 32)
                (MkDinode (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 32)
                          (replicate 13 (bv_0 32)))
                bm_empty n1 Sb1 ns
                with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv Hpath
                      Hbsl [%] Hisl [%] Hop [$Htx]").
      { exact Hcsf. }
      { exact (cr_slots_ns _ ns eq_refl Hns). }
      { split_and!; [exact Hsb1 | exact (proj2 Hnp1) | discriminate]. }
      { iPureIntro. rewrite Ha0f. exact HN1s2. }
  Qed.

End ProofCreateFound.

End CreateFound.
