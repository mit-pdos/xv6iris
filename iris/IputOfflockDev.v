(* ============================================================================
   DEV SCRATCH: ip_free_offlock -- the WP walk for the OFF-LOCK free tail block
   iput +0xa8 .. +0xd0 (bread; sh zero,88(a5); log_write; brelse; restore; j 0x30).

   Developed as a functor over BREAD/LOG_WRITE/BRELSE (as ProofIupdate is), so it
   compiles against the pre-built cone without touching IputProof's signature.
   The FINAL splice into ProofIput.v inlines the body of this lemma.
   ========================================================================== *)

From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import BufOwn.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeHalf.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import WpUart.
Require Import BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import DinodeSlot.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import SpecBread SpecBrelse SpecLogWrite.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import EscrowDefs.
Require Import EscrowInode.
Require Import EscrowDeposit.
Require Import CodeIput.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.

Set Printing Depth 40.

Module OfflockDev (BR : BREAD) (LW : LOG_WRITE) (BL : BRELSE).

Section OfflockDev.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra1  := (mword_of_int 11 : mword 5).
  Notation Ra4  := (mword_of_int 14 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).
  Notation Rs2  := (mword_of_int 18 : mword 5).
  Notation Rs3  := (mword_of_int 19 : mword 5).
  Notation Rs4  := (mword_of_int 20 : mword 5).
  Notation Rz   := (mword_of_int 0 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz  := vm_compute; discriminate.
  Local Ltac regne := reg_ne_side.

  (* the record the [sh zero,88(a5)] leaves in the marked slot: the loaded
     record with its 16-bit type field zeroed, EVERYTHING ELSE verbatim (the
     off-lock free writes ONLY type, unlike iupdate's full flush). *)
  Definition set_ditype0 (d : dinode) : dinode :=
    MkDinode (mword_of_int 0 : mword 16) (di_major d) (di_minor d)
             (di_nlink d) (di_size d) (di_addrs d).

  (* the register-threading invariant across the three calls (bread,
     log_write, brelse): every callee-saved reg but the frame's own
     (s1,s2,s3,s4 -- s1 holds bp across the calls, s2/3/4 restored at the
     tail) rides untouched from entry to 0x30. *)
  Definition ipo_thr (m M : regfile) : Prop :=
    forall c : mword 5, is_cs_idx c = true ->
      c <> csp_rs1 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
      M !!! Regidx c = (m !!! Regidx c : mword 64).

  (* [iu_held_L], inlined (ProofIupdate-module-local otherwise). *)
  Lemma ipo_held_L (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (pidv dv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) :
    bio_held bn (fs_view γfs γd dev cov) k pidv dv bno bs bsl bsd d -∗
      (uint bno ↪[fs_L γfs]{#(1/2)} bsl) ∗
      ((uint bno ↪[fs_L γfs]{#(1/2)} bsl) -∗
       bio_held bn (fs_view γfs γd dev cov) k pidv dv bno bs bsl bsd d).
  Proof.
    rewrite /bio_held /bio_pay /fs_view /=.
    iIntros "(%A & %B & %C & H1 & H2 & H3 & H4 & H5 & H6 & Hpay)".
    destruct d.
    - rewrite /fs_mdirty. iDestruct "Hpay" as "[[HL HD] Hq]".
      iFrame "HL". iIntros "HL".
      iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
      iFrame "H1 H2 H3 H4 H5 H6". iFrame "HL HD Hq".
    - rewrite /fs_mclean. iDestruct "Hpay" as "[[HL HD] %He]".
      iFrame "HL". iIntros "HL".
      iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
      iFrame "H1 H2 H3 H4 H5 H6". iFrame "HL HD". done.
  Qed.

  (* ======================================================================
     ip_free_offlock : the off-lock free tail, iput +0xa8 .. j 0x30.

     ENTRY (the (A) contract, at pc = iput+0xa8, the itable lock RELEASED):
       - a0 = dev, a1 = the IBLOCK word, s2 = inum (sign-extended);
       - s1 will be overwritten with bp; s3/s4 ride the frame;
       - the loaded record [dinode_at gi inum dn] with di_nlink dn = 0;
       - the EMPTY escrow minted at the +0x8a last close, [escA_inv ge gr gd
         gi inum], and its DEPOSIT ticket [redeem_ticketA gd];  [ireg_inv].
         NOT the pool bundle: under the reorder [ip_free_locked] has already
         parked that at the +0x94 release (IVd, see the entry note);
       - bread/log_write/brelse fabric (bio_ctx, log_ctx, disk, procs);
       - the 6-slot frame (ra,s0,s1 held through; s2,s3,s4 restored here).

     POST (at pc = iput+0x30, handed to the iput-return epilogue):
       - the machine restored (s2/s3/s4 <- saved frame values), sp unchanged;
       - the region side parked into [ireg_inv] by the deposit, and the
         escrow left FILLED for whoever redeems it (no pool entry: it was
         parked at +0x94);
       - log ledger grown by the inode block; the frame still held.
     ====================================================================== *)
  Lemma ip_free_offlock `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart inodestart : Z) (nib : nat)
      (dev : mword 32) (inum : mword 32) (dn : dinode)
      (ge gr gd : gname)
      (u : nat) (Sb : gset Z) (cru : bool) (e0 v : nat)
      (pidv : mword 32) (dq dqs : dfrac)
      (sp0 vra vs0 vs1 vs2 vs3 vs4 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) :
    let pj := proc_addr j in
    let bno := (mword_of_int (IBLOCK inum inodestart) : mword 32) in
    let dn' := set_ditype0 dn in
    (K_bread <= K)%nat -> (K_log_write <= K)%nat -> (K_brelse <= K)%nat ->
    (* [SpecLogWrite]'s [Z.of_nat n + 2 < 2^31] is a bound on the CPU NESTING
       LEVEL, not on the log's unit count, and this tail calls log_write at
       the literal level 0 -- so the premise this lemma used to carry for it
       was vacuous and is gone.  (It read as a bound on [u] purely because
       the two arguments happen to share a name at the call site.) *)
    log_geom_ok cov logstart ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    dinode_wf dn ->
    bv_unsigned (di_nlink dn) = 0 ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    sp0 = m !!! Regidx csp_rs1 ->
    m !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64) ->
    m !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64) ->
    m !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64) ->
    locks_below lks "log" ->
    sie_cap_gpr KT1 m K b pj -∗
    cpu_own 0 eb pj b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb pj -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (KernelSyms.iput + 0xa8) : mword 64) -∗
    panic_env -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    (* ---- THE LEDGER's UNCACHED CAPITAL IS NOT HERE (iclaim-ledger.md IVd),
       and under the REORDER it cannot be.  The count half at zero, the
       mirror's half DOWN and the escrow's REDEEM ticket are the evicted
       inum's POOL BUNDLE, and the reordered iput releases the itable lock at
       +0x94 -- BEFORE this tail runs.  At that release
       [IcacheEscrow.ic_ci_wf]'s [dom ci = dom M] already shows the inum
       uncached, so its bundle must be in the itable's free pool by then, and
       [ip_free_locked] parks it there on the AWAIT arm
       ([IcacheEscrow.ipool_shape_await]) out of the last close's own three
       outputs.  There is exactly one [icnt_half .. 0] and one
       [frzm_h .. false] in the system, so this tail can neither take them nor
       hand one back: the pending arm's [committedA] upgrade belongs to
       whoever later redeems the escrow, not to the depositor.

       WHAT THE DEPOSITOR STILL CARRIES is the escrow itself (persistent) and
       its DEPOSIT ticket, below -- the two things the +0xba fill needs. *)
    escA_inv ge gr gd γi (bv_unsigned inum) -∗
    (* THE DEPOSIT TICKET (A⁗, §3.16), in place of IVa's [ifreeze_post].  The
       standing freeze now lives in the ESCROW's EMPTY state -- it has to,
       because that is the only place from which a RECYCLER peeling the pool's
       await arm can find it and its licence refute it (§1.3) -- so the
       depositor carries the ticket that opens that state instead, and
       [EscrowInode.escA_deposit_acc] hands it the token, takes the retired
       one back, and rules out a second deposit. *)
    redeem_ticketA gd -∗
    p_pid pj ↦₄{dq} pidv -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bslots bn 2 -∗
    log_epoch_lb γ v -∗
    log_credit γ cru Sb e0 (IBLOCK inum inodestart) -∗
    log_opSe γ (S u) Sb e0 -∗
    (* the frame: ra/s0/s1 ride through to the epilogue; s2/s3/s4 restored here *)
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) ↦₈[KT1] vra -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) ↦₈[KT1] vs0 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) ↦₈[KT1] vs1 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) ↦₈[KT1] vs2 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) ↦₈[KT1] vs3 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) ↦₈[KT1] vs4 -∗
    (* THE CALLER'S CONTINUATION at 0x30 *)
    wp_next true pj (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜ipo_thr m mf /\ mf !!! Regidx csp_rs1 = sp0
          /\ mf !!! Regidx Rs2 = vs2 /\ mf !!! Regidx Rs3 = vs3
          /\ mf !!! Regidx Rs4 = vs4⌝ -∗
        sie_cap_gpr (CID := CID) KT1 mf K b pj -∗
        cpu_own (CID := CID) 0 eb pj b lks -∗
        trap_csrs_ext (CID := CID) KT1 eb -∗
        cpu_claim_ext (CID := CID) eb pj -∗
        pc_is (CID := CID) (mword_of_int (KernelSyms.iput + 0x30) : mword 64) -∗
        p_pid pj ↦₄{dq} pidv -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        (* no pool entry: [ip_free_locked] parked it at the +0x94 release,
           on the AWAIT arm -- see the entry note above *)
        bslots bn 2 -∗
        log_opS γ (if cru then S u else u) (Sb ∪ {[IBLOCK inum inodestart]}) -∗
        (∃ e : nat, logged_at γ e (IBLOCK inum inodestart) ∗ ⌜(v <= e)%nat⌝) -∗
        (* RULING G's RETURN LEG (iclaim-ledger.md §6′).  The +0xba deposit
           runs the region open that retires the freeze, and the slot's
           boot-shelter clause is on its SEALED arm there ([FrzPost] refutes
           ⌜f = FrzOff⌝) -- so the regime the caller lent at the mint comes
           back out with the [committedA] marker
           ([EscrowDeposit.ireg_free_deposit_au]'s second fupd). *)
        (ireg_open ∨ ireg_boot) -∗
        (* the frame ra/s0/s1 slots, still saved, for the epilogue *)
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) ↦₈[KT1] vra -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) ↦₈[KT1] vs0 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) ↦₈[KT1] vs1 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) ↦₈[KT1] vs2 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) ↦₈[KT1] vs3 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) ↦₈[KT1] vs4 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj bno dn' HKbr HKlw HKbl Hgeom Hst Hcov Hlog Hnib Hdnwf Hnl0
           Hj Hgl Hsp0 Ha0 Ha1 Hs2v Hbelow.
    (* ---- pure prelude (mirrors iu_main_gen) ---- *)
    destruct Hgeom as [Hcovok Hlogsub].
    destruct (Hcovok _ Hcov) as [Hibpos Hiblt].
    assert (Hib : 0 <= IBLOCK inum inodestart < 2147483648)
      by (change (2 ^ 31)%Z with 2147483648%Z in Hiblt; lia).
    assert (Hbno : uint bno = IBLOCK inum inodestart).
    { rewrite /bno bb_uint32 moi32_unsigned. apply bvw32_small.
      change (2^32)%Z with 4294967296%Z. lia. }
    assert (Hbnolt : (uint bno < 2147483648)%Z) by (rewrite Hbno; lia).
    assert (Hbnocov : uint bno ∈ bv_cov (fs_view γfs γd dev cov))
      by (rewrite Hbno; exact Hcov).
    pose proof (bv_unsigned_in_range _ inum) as [Hinum0 Hinum1].
    assert (Hm32 : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 4294967296)
      by (vm_compute; reflexivity).
    rewrite Hm32 in Hinum1.
    assert (Hslotz : Z.of_nat (DinodeEnc.islot inum) = bv_unsigned inum `mod` 16).
    { rewrite /DinodeEnc.islot Z2Nat.id; [reflexivity |].
      pose proof (Z.mod_pos_bound (bv_unsigned inum) 16 ltac:(lia)) as [Hz _].
      exact Hz. }
    pose proof (DinodeEnc.islot_lt inum) as Hslotlt.
    assert (Hdn'wf : dinode_wf dn') by (rewrite /dn' /set_ditype0 /dinode_wf /=; exact Hdnwf).
    assert (Hdn'ty : bv_unsigned (di_type dn') = 0) by (vm_compute; reflexivity).
    assert (Hnlst : di_nlink_stable dn' dn).
    { rewrite /di_nlink_stable /dn' /set_ditype0 /=. split; [reflexivity | intros _; exact Hnl0]. }
    iIntros "Hcg Hcnt Htc Hclm #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx #Hireg Hdn
             #Hesc Hdep Hppid #Hprocs #Hdevi #Hdgeom #Hdlock Hsb Hsl #Hvlb #Hcrd0 Hop
             Hra Hs0f Hs1f Hs2f Hs3f Hs4f Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    iDestruct (iu_slots_split bn 1 1 with "Hsl") as "[Hsl Hsl1]".
    (* ===== +0xa8 jal ra,bread ===== *)
    iPoseProof (ipi_a8 with "Htext") as "Hia8".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0xa8)) Rra
              (mword_of_int 2094910 : mword 21) m K b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hia8").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (R0 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0xa8) : mword 64) 4)]> m).
    assert (Htgtbr : add_vec (mword_of_int (KernelSyms.iput + 0xa8) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094910 : mword 21))
                     = mword_of_int KernelSyms.bread) by pcw.
    iEval (rewrite Htgtbr) in "Hpc".
    assert (HR0a0 : R0 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R0 upd_ne; [exact Ha0 | nz]).
    assert (HR0a1 : R0 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64))
      by (rewrite /R0 upd_ne; [exact Ha1 | nz]).
    assert (HR0s2 : R0 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /R0 upd_ne; [exact Hs2v | nz]).
    assert (HR0ra : R0 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0xa8) : mword 64) 4)
      by (rewrite /R0; apply upd_eq).
    iDestruct (cpu_own_transport CID0 CID1 0 eb pj b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID1 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Htc") as "Htc".
    iDestruct (cpu_claim_ext_transport CID0 CID1 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hclm") as "Hclm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID1) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    (* ===== bread ===== *)
    iApply (BR.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev bno dq
              R0 K eb b
              lks HKbr Hbnolt eq_refl Hbnocov eq_refl Hj Hgl HR0a0 HR0a1
              ltac:(lkbelow)
              with "Hcg Hcnt Htc Hclm Htext Hkd Hpc Hpenv Hbio Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hsl1").
    all: try lkbelow.
    iIntros (CID15 Hq15 mB kk bs0 bsd0 d0) "%Hfacts Hcg Hcnt Htc Hclm Hpc Hppid Hheld".
    destruct Hfacts as [Hcs1 HmBa0].
    assert (Hpc_ac : ret_pc (R0 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.iput + 0xac)) by (rewrite HR0ra; pcw).
    iEval (rewrite Hpc_ac) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmBs2 : mB !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64)).
    { rewrite (callee_saved_lookup Hcs1_cs Rs2 ltac:(vm_compute; reflexivity)). exact HR0s2. }
    (* ---- couple the buffer bytes to the region's parked [ds] ---- *)
    iEval (rewrite /bio_locked) in "Hheld".
    iDestruct (iu_held_k with "Hheld") as %Hkk.
    iDestruct (ipo_held_L with "Hheld") as "[HpL Hheldback0]".
    iApply fupd_wp.
    iMod (ireg_read ⊤ γi γfs inodestart nib inum dn (uint bno) bs0
            ltac:(solve_ndisj) Hnib Hbno
            with "Hireg Hdn HpL") as "(%Hex & Hdn & HpL)".
    iModIntro.
    iDestruct ("Hheldback0" with "HpL") as "Hheld".
    destruct Hex as (ds & Hdswf & Hbs0 & Hslteq).
    subst bs0.
    iDestruct (iu_held_swap with "Hheld") as "[Hbuf Hheldback]".
    iDestruct (iu_buf_bytes (bpa kk) bno (mword_of_int 0 : mword 32) ds Hdswf
                 with "Hbuf") as "[Hby Hbyback]".
    assert (Hslotal : dislot_align
              (pa_add (b_data (bnode kk)) (64 * DinodeEnc.islot inum)%nat)).
    { rewrite /dislot_align.
      assert (E0 : (64 * DinodeEnc.islot inum)%nat = (64 * DinodeEnc.islot inum + 0)%nat) by lia.
      split_and!.
      - rewrite E0. apply iu_align; [exact Hkk | exact Hslotlt | lia | left; reflexivity
                                   | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | right; reflexivity | reflexivity]. }
    iDestruct (diblk_slot_acc (b_data (bpa kk)) ds (DinodeEnc.islot inum)
                 Hdswf Hslotlt Hslotal with "Hby") as "[Hslot Hslotback]".
    iDestruct "Hslot" as "(Hd0 & Hd2 & Hd4 & Hd6 & Hd8 & Hda)".
    (* ===== +0xac c.mv s1,a0 : s1 := bp ===== *)
    iPoseProof (ipi_ac with "Htext") as "Hiac".
    iPoseProof (ipi_ae with "Htext") as "Hiae".
    iPoseProof (ipi_b2 with "Htext") as "Hib2".
    iPoseProof (ipi_b4 with "Htext") as "Hib4".
    iPoseProof (ipi_b6 with "Htext") as "Hib6".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0xac)) Rs1 Ra0
              mB K b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hiac").
    iIntros (CID16 Hq16) "Hcg Hpc".
    set (R1 := <[Regidx Rs1 := regval_into_reg (add_vec (zero_reg : mword 64) (rget mB Ra0))]> mB).
    assert (HR1s1 : R1 !!! Regidx Rs1 = bnode kk).
    { rewrite /R1 upd_eq. rgne. rewrite HmBa0. apply add_vec_zero_l. }
    assert (HR1a0 : R1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /R1 upd_ne; [exact HmBa0 | nz]).
    assert (HR1s2 : R1 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /R1 upd_ne; [exact HmBs2 | nz]).
    assert (Hppae : add_vec_int (mword_of_int (KernelSyms.iput + 0xac) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xae)) by pcw.
    iEval (rewrite Hppae) in "Hpc".
    (* ===== +0xae andi a5,s2,15 : a5 := inum % IPB ===== *)
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.iput + 0xae)) Ra5 Rs2
              (mword_of_int 15 : mword 12)
              (mword_of_int (bv_unsigned inum `mod` 16) : mword 64)
              R1 K b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hiae").
    { rgne. rewrite HR1s2.
      replace (sign_extend' 64 (mword_of_int 15 : mword 12) : mword 64)
        with (sign_extend' 64 (sign_extend' 12 (mword_of_int 15 : mword 6)) : mword 64)
        by pcw.
      rewrite iu_andi15 iu_sext_mod16. reflexivity. }
    iIntros (CID17 Hq17) "Hcg Hpc".
    set (R2 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int (bv_unsigned inum `mod` 16) : mword 64)]> R1).
    assert (HR2a5 : R2 !!! Regidx Ra5 = (mword_of_int (bv_unsigned inum `mod` 16) : mword 64))
      by (rewrite /R2; apply upd_eq).
    assert (HR2a0 : R2 !!! Regidx Ra0 = bnode kk)
      by (rewrite /R2 upd_ne; [exact HR1a0 | nz]).
    assert (Hppb2 : add_vec_int (mword_of_int (KernelSyms.iput + 0xae) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0xb2)) by pcw.
    iEval (rewrite Hppb2) in "Hpc".
    (* ===== +0xb2 c.slli a5,0x6 : a5 := (inum % IPB) * 64 ===== *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.iput + 0xb2)) (Regidx Ra5) Ra5
              (mword_of_int 6 : mword 6) R2 K b
              ltac:(reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc Hib2").
    iIntros (CID18 Hq18) "Hcg Hpc".
    set (R3 := <[Regidx Ra5 := regval_into_reg
                  (shift_bits_left (rget R2 Ra5)
                     (subrange_vec_dec (mword_of_int 6 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> R2).
    assert (HR3a5 : R3 !!! Regidx Ra5
                    = (mword_of_int (64 * (bv_unsigned inum `mod` 16)) : mword 64)).
    { rewrite /R3 upd_eq. rgne. rewrite HR2a5.
      apply iu_slli6.
      - apply Z.mod_pos_bound. lia.
      - apply Z.mod_pos_bound. lia. }
    assert (HR3a0 : R3 !!! Regidx Ra0 = bnode kk)
      by (rewrite /R3 upd_ne; [exact HR2a0 | nz]).
    assert (Hppb4 : add_vec_int (mword_of_int (KernelSyms.iput + 0xb2) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xb4)) by pcw.
    iEval (rewrite Hppb4) in "Hpc".
    (* ===== +0xb4 c.add a5,a5,a0 : a5 := bp + (inum%IPB)*64 ===== *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.iput + 0xb4)) Ra5 Ra0
              R3 K b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hib4").
    iIntros (CID19 Hq19) "Hcg Hpc".
    set (R4 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget R3 Ra5) (rget R3 Ra0))]> R3).
    assert (HR4a5 : R4 !!! Regidx Ra5
                    = add_vec (mword_of_int (64 * (bv_unsigned inum `mod` 16)) : mword 64)
                              (bnode kk)).
    { rewrite /R4 upd_eq. rgne. rgne. rewrite HR3a5 HR3a0. reflexivity. }
    assert (Hppb6 : add_vec_int (mword_of_int (KernelSyms.iput + 0xb4) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xb6)) by pcw.
    iEval (rewrite Hppb6) in "Hpc".
    (* ===== +0xb6 sh zero,88(a5) : dip->type = 0 ===== *)
    (* the store address is the marked slot's type cell *)
    assert (Hstore : add_vec (rget R4 Ra5) (sign_extend' 64 (mword_of_int 88 : mword 12))
                     = pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat).
    { rgne. rewrite HR4a5.
      rewrite -iu_slot_addr -iu_data_addr.
      change (bpa kk) with (bnode kk).
      apply bv_eq. rewrite !add_vec64_unsigned.
      rewrite !bv_wrap_add_idemp_l.
      assert (Hs88 : bv_unsigned (sign_extend' 64 (mword_of_int 88 : mword 12) : mword 64) = 88)
        by (vm_compute; reflexivity).
      assert (Hmoi64 : bv_unsigned (mword_of_int (64 * Z.of_nat (DinodeEnc.islot inum)) : mword 64)
                       = 64 * Z.of_nat (DinodeEnc.islot inum)).
      { apply moi64_small. pose proof (DinodeEnc.islot_lt inum). lia. }
      assert (Hmoi64' : bv_unsigned (mword_of_int (64 * (bv_unsigned inum `mod` 16)) : mword 64)
                        = 64 * (bv_unsigned inum `mod` 16)).
      { apply moi64_small. pose proof (Z.mod_pos_bound (bv_unsigned inum) 16 ltac:(lia)) as [_ Hb]. lia. }
      rewrite Hs88 Hmoi64 Hmoi64' Hslotz. f_equal. ring. }
    iDestruct (sie_cap_gpr_x0 R4 K b pj (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
    iEval (rewrite -Hstore) in "Hd0".
    iApply (wp_sh_s_sconf (mword_of_int (KernelSyms.iput + 0xb6)) Rz Ra5
              (mword_of_int 88 : mword 12) R4 K
              (di_type (ds !!! DinodeEnc.islot inum) : mword 16) b with "Hcg Hpc Hib6 Hd0").
    iIntros (CID20 Hq20) "Hcg Hpc Hd0".
    (* the store wrote 0 = di_type dn' into the type cell *)
    assert (Hstoreval : trunc16 (rget R4 Rz) = (di_type dn' : mword 16)).
    { rgne. rewrite Hx0 /dn' /set_ditype0 /=. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hstore Hstoreval) in "Hd0".
    (* ---- rebuild the slot at [dn'], then the buffer, then the handle ---- *)
    assert (Hmaj : di_major dn' = di_major dn) by (rewrite /dn' /set_ditype0; reflexivity).
    assert (Hmin : di_minor dn' = di_minor dn) by (rewrite /dn' /set_ditype0; reflexivity).
    assert (Hnlk : di_nlink dn' = di_nlink dn) by (rewrite /dn' /set_ditype0; reflexivity).
    assert (Hsz  : di_size  dn' = di_size  dn) by (rewrite /dn' /set_ditype0; reflexivity).
    assert (Hadr : di_addrs dn' = di_addrs dn) by (rewrite /dn' /set_ditype0; reflexivity).
    iEval (rewrite Hslteq) in "Hd2".
    iEval (rewrite Hslteq) in "Hd4".
    iEval (rewrite Hslteq) in "Hd6".
    iEval (rewrite Hslteq) in "Hd8".
    iEval (rewrite Hslteq) in "Hda".
    iAssert (dislot (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat) dn')
      with "[Hd0 Hd2 Hd4 Hd6 Hd8 Hda]" as "Hslot'".
    { rewrite /dislot Hmaj Hmin Hnlk Hsz Hadr. iFrame "Hd0 Hd2 Hd4 Hd6 Hd8 Hda". }
    iDestruct ("Hslotback" $! dn' with "[%] Hslot'") as "Hby'"; [exact Hdn'wf |].
    iDestruct ("Hbyback" $! (<[DinodeEnc.islot inum := dn']> ds) with "[%] Hby'") as "Hbuf'".
    { exact (diblk_wf_insert ds (DinodeEnc.islot inum) dn' Hdswf Hdn'wf). }
    iDestruct ("Hheldback" with "Hbuf'") as "Hheld".
    (* ===== +0xba jal ra,log_write ===== *)
    iPoseProof (ipi_ba with "Htext") as "Hiba".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0xba)) Rra
              (mword_of_int 2524 : mword 21) R4 K b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hiba").
    iIntros (CID21 Hq21) "Hcg Hpc".
    set (R5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0xba) : mword 64) 4)]> R4).
    assert (Htgtlw : add_vec (mword_of_int (KernelSyms.iput + 0xba) : mword 64)
                       (sign_extend' 64 (mword_of_int 2524 : mword 21))
                     = mword_of_int KernelSyms.log_write) by pcw.
    iEval (rewrite Htgtlw) in "Hpc".
    assert (HR4a0 : R4 !!! Regidx Ra0 = bnode kk).
    { rewrite /R4 upd_ne; [| nz]. exact HR3a0. }
    assert (HR5a0 : R5 !!! Regidx Ra0 = bnode kk)
      by (rewrite /R5 upd_ne; [exact HR4a0 | nz]).
    assert (HR5ra : R5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0xba) : mword 64) 4)
      by (rewrite /R5; apply upd_eq).
    (* ---- the deposit's AU, adapted to log_write's anchor form ---- *)
    iPoseProof (ireg_free_deposit_au ⊤ γi γfs inodestart nib inum dn dn' ds ge gr gd
                  ltac:(solve_ndisj) ltac:(solve_ndisj) Hnib Hdswf Hdn'wf Hdn'ty Hnlst
                  with "Hireg Hesc Hdn Hdep") as "Hau0".
    iEval (rewrite -Hbno) in "Hau0".
    iDestruct (lw_au_lb0 γ γfs (uint bno) (⊤ ∖ ↑iregN)
                 (diblk_bytes (<[DinodeEnc.islot inum := dn']> ds)) (diblk_bytes ds)
                 (committedA ge ∗ (ireg_open ∨ ireg_boot))%I e0 with "Hau0") as "Hau".
    (* ---- transports around the log_write park ---- *)
    iDestruct (cpu_own_transport CID15 CID21 0 eb pj b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID1) (CIDb := CID21) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iRename "Hop" into "HopS".
    iAssert (log_credit γ cru Sb e0 (uint bno)) as "#Hcrd";
      [rewrite Hbno; iExact "Hcrd0" |].
    iApply (LW.wp_log_write_au bn γ γfs γd cov logstart dev kk pidv bno
              (diblk_bytes (<[DinodeEnc.islot inum := dn']> ds)) (diblk_bytes ds) bsd0 d0 u
              cru Sb e0 v (⊤ ∖ ↑iregN) (committedA ge ∗ (ireg_open ∨ ireg_boot))%I
              R5 0%nat eb pj K b
              _ HKlw ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia) Hkk HR5a0
              ltac:(rewrite Hbno; exact Hcov)
              ltac:(rewrite Hbno; exact Hlog)
              Hbelow
              with "Hcg Hcnt Htext Hpc Hbio Hlctx Hsl Hvlb Hcrd HopS Hau Hheld").
    all: try lkbelow.
    iIntros (CID22 Hq22 mL) "Hcg Hcnt Hpc %Hcs2 HopS [#Hcom Hgreg] Hlk Hsl".
    (* NO POOL ENTRY IS ASSEMBLED HERE (IVd).  The bundle was parked at the
       +0x94 release on the AWAIT arm, which is the arm's own stated purpose;
       the [committedA] the deposit just produced is not needed to state it
       (the await arm is [pool_pending] minus exactly that fragment) and the
       upgrade, if anyone ever wants it, belongs to the redeemer. *)
    (* ---- the log ledger, in the public form ---- *)
    iEval (rewrite Hbno) in "HopS".
    iDestruct (log_opSwe_opSw with "HopS") as "HopS".
    iDestruct (log_opSw_witness with "HopS") as "[Hop Hwit]".
    (* ---- register facts for [R5] carried through log_write ---- *)
    assert (HR5s1 : R5 !!! Regidx Rs1 = bnode kk).
    { rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz]. exact HR1s1. }
    assert (HR5sp : R5 !!! Regidx csp_rs1 = sp0).
    { rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /R0 upd_ne; [| nz].
      exact (eq_sym Hsp0). }
    pose proof Hcs2 as Hcs2_cs.
    assert (HmLs1 : mL !!! Regidx Rs1 = bnode kk).
    { rewrite (callee_saved_lookup Hcs2_cs Rs1 ltac:(vm_compute; reflexivity)). exact HR5s1. }
    assert (HmLsp : mL !!! Regidx csp_rs1 = sp0).
    { rewrite (callee_saved_lookup Hcs2_cs csp_rs1 ltac:(vm_compute; reflexivity)). exact HR5sp. }
    assert (Hpcbe : ret_pc (R5 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.iput + 0xbe)) by (rewrite HR5ra; pcw).
    iEval (rewrite Hpcbe) in "Hpc".
    (* ===== +0xbe c.mv a0,s1 : a0 := bp ===== *)
    iPoseProof (ipi_be with "Htext") as "Hibe".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0xbe)) Ra0 Rs1
              mL K b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hibe").
    iIntros (CID23 Hq23) "Hcg Hpc".
    set (T0 := <[Regidx Ra0 := regval_into_reg (add_vec (zero_reg : mword 64) (rget mL Rs1))]> mL).
    assert (HT0a0 : T0 !!! Regidx Ra0 = bnode kk).
    { rewrite /T0 upd_eq. rgne. rewrite HmLs1. apply add_vec_zero_l. }
    assert (HT0sp : T0 !!! Regidx csp_rs1 = sp0)
      by (rewrite /T0 upd_ne; [exact HmLsp | nz]).
    assert (Hppc0 : add_vec_int (mword_of_int (KernelSyms.iput + 0xbe) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xc0)) by pcw.
    iEval (rewrite Hppc0) in "Hpc".
    (* ===== +0xc0 jal ra,brelse ===== *)
    iPoseProof (ipi_c0 with "Htext") as "Hic0".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0xc0)) Rra
              (mword_of_int 2095150 : mword 21) T0 K b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hic0").
    iIntros (CID24 Hq24) "Hcg Hpc".
    set (T1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0xc0) : mword 64) 4)]> T0).
    assert (Htgtbl : add_vec (mword_of_int (KernelSyms.iput + 0xc0) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095150 : mword 21))
                     = mword_of_int KernelSyms.brelse) by pcw.
    iEval (rewrite Htgtbl) in "Hpc".
    assert (HT1a0 : T1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /T1 upd_ne; [exact HT0a0 | nz]).
    assert (HT1sp : T1 !!! Regidx csp_rs1 = sp0)
      by (rewrite /T1 upd_ne; [exact HT0sp | nz]).
    assert (HT1ra : T1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0xc0) : mword 64) 4)
      by (rewrite /T1; apply upd_eq).
    (* transports around the brelse park *)
    iDestruct (cpu_own_transport CID22 CID24 0 eb pj b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID21) (CIDb := CID24) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kk
              pidv dev bno dq T1 K eb pj
              (diblk_bytes (<[DinodeEnc.islot inum := dn']> ds)) bsd0 true b
              lks HKbl Hkk HT1a0 ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hlk").
    all: try lkbelow.
    iIntros (CID25 Hq25 mR) "%Hcs3 Hcg Hcnt Hpc Hppid Hsl1".
    pose proof Hcs3 as Hcs3_cs.
    assert (Hpcc4 : ret_pc (T1 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.iput + 0xc4)) by (rewrite HT1ra; pcw).
    iEval (rewrite Hpcc4) in "Hpc".
    assert (HmRsp : mR !!! Regidx csp_rs1 = sp0).
    { rewrite (callee_saved_lookup Hcs3_cs csp_rs1 ltac:(vm_compute; reflexivity)). exact HT1sp. }
    iDestruct (iu_slots_join bn 1 1 with "Hsl Hsl1") as "Hsl".
    iEval (change (1 + 1)%nat with 2%nat) in "Hsl".
    (* ===== +0xc4/c6/c8 c.ldsp s2/s3/s4 : restore ===== *)
    iPoseProof (ipi_c4 with "Htext") as "Hic4".
    iPoseProof (ipi_c6 with "Htext") as "Hic6".
    iPoseProof (ipi_c8 with "Htext") as "Hic8".
    iPoseProof (ipi_ca with "Htext") as "Hica".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0xc4)) (mword_of_int 2 : mword 6) Rs2
              mR K vs2 b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hic4 [Hs2f]").
    { iEval (rewrite HmRsp). iExact "Hs2f". }
    iIntros (CID26 Hq26) "Hcg Hpc Hs2f".
    iEval (rewrite HmRsp) in "Hs2f".
    set (P1 := <[Regidx Rs2 := regval_into_reg vs2]> mR).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = sp0)
      by (rewrite /P1 upd_ne; [exact HmRsp | nz]).
    assert (Hppc6 : add_vec_int (mword_of_int (KernelSyms.iput + 0xc4) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xc6)) by pcw.
    iEval (rewrite Hppc6) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0xc6)) (mword_of_int 1 : mword 6) Rs3
              P1 K vs3 b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hic6 [Hs3f]").
    { iEval (rewrite HP1sp). iExact "Hs3f". }
    iIntros (CID27 Hq27) "Hcg Hpc Hs3f".
    iEval (rewrite HP1sp) in "Hs3f".
    set (P2 := <[Regidx Rs3 := regval_into_reg vs3]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = sp0)
      by (rewrite /P2 upd_ne; [exact HP1sp | nz]).
    assert (Hppc8 : add_vec_int (mword_of_int (KernelSyms.iput + 0xc6) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xc8)) by pcw.
    iEval (rewrite Hppc8) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0xc8)) (mword_of_int 0 : mword 6) Rs4
              P2 K vs4 b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hic8 [Hs4f]").
    { iEval (rewrite HP2sp). iExact "Hs4f". }
    iIntros (CID28 Hq28) "Hcg Hpc Hs4f".
    iEval (rewrite HP2sp) in "Hs4f".
    set (P3 := <[Regidx Rs4 := regval_into_reg vs4]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = sp0)
      by (rewrite /P3 upd_ne; [exact HP2sp | nz]).
    assert (Hppca : add_vec_int (mword_of_int (KernelSyms.iput + 0xc8) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xca)) by pcw.
    iEval (rewrite Hppca) in "Hpc".
    (* ===== +0xca c.j 0x30 : into the iput-return epilogue ===== *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.iput + 0xca))
              (sign_extend' 21 (concat_vec (mword_of_int 1971 : mword 11) ('b"0")))
              P3 K b ltac:(vm_compute; reflexivity) with "Hcg Hpc Hica").
    iIntros (CID29 Hst29). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt30 : add_vec (mword_of_int (KernelSyms.iput + 0xca) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 1971 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.iput + 0x30)) by pcw.
    iEval (rewrite Htgt30) in "Hpc".
    (* the final callee-saved threading, m -> P3, off the frame regs *)
    assert (Hthr : ipo_thr m P3).
    { intros c Hcs Ncsp Ns1 Ns2 Ns3 Ns4.
      rewrite /P3 upd_ne; [| congruence].
      rewrite /P2 upd_ne; [| congruence].
      rewrite /P1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs3_cs c Hcs).
      rewrite /T1 upd_ne; [| regne].
      rewrite /T0 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hcs2_cs c Hcs).
      rewrite /R5 upd_ne; [| regne].
      rewrite /R4 upd_ne; [| regne].
      rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      rewrite /R0 upd_ne; [| regne]. reflexivity. }
    assert (HP3s2 : P3 !!! Regidx Rs2 = vs2).
    { rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_ne; [| nz].
      rewrite /P1; apply upd_eq. }
    assert (HP3s3 : P3 !!! Regidx Rs3 = vs3).
    { rewrite /P3 upd_ne; [| nz]. rewrite /P2; apply upd_eq. }
    assert (HP3s4 : P3 !!! Regidx Rs4 = vs4) by (rewrite /P3; apply upd_eq).
    (* the final hart hop for the pass-through complement + cpu_own *)
    iDestruct (cpu_own_transport CID25 CID29 0 eb pj b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID15 CID29 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Htc") as "Htc".
    iDestruct (cpu_claim_ext_transport CID15 CID29 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hclm") as "Hclm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID24) (CIDb := CID29) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iSpecialize ("Hcont" $! CID29 with "[]"); [iPureIntro; wp_next_chain |].
    iApply ("Hcont" $! P3 with "[%] Hcg Hcnt Htc Hclm Hpc Hppid Hsb Hsl Hop Hwit
                                Hgreg Hra Hs0f Hs1f Hs2f Hs3f Hs4f").
    { split_and!; [exact Hthr | exact HP3sp | exact HP3s2 | exact HP3s3 | exact HP3s4]. }
  Qed.

End OfflockDev.
(* ---- IVb's ADMIT-FREEDOM CHECK (iclaim-ledger.md §3.14 as built) ---- *)
Print Assumptions ip_free_offlock.

End OfflockDev.
