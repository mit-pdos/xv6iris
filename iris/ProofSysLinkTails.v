(* ProofSysLinkTails.v -- sys_link's THREE "-1" tails, as block lemmas.
   These apply callees' contracts, so they live inside a module functor
   ([design/spec-modules.md]); the functor is NOT ascribed to a signature,
   because it is a parts layer -- [ProofSysLink.v] instantiates it beside
   its own callee arguments and the seal happens there.

     ARM B  (+0xb6 .. +0xbe)  namei(old) returned 0
                              end_op; a5 = -1; restore s1; join
     ARM C  (+0xc0 .. +0xce)  ip->type == T_DIR
                              iunlockput(ip); end_op; a5 = -1; restore s1
     ARM D  (+0xd0 .. +0xde)  ip->nlink == NLINK_MAX -- THE GUARD ARM
                              byte-identical to ARM C at a shifted address

   ARMS C AND D ARE THE SAME SIX INSTRUCTIONS AND ARE STILL TWO LEMMAS.
   Their decode facts are per-address ([slki_c0] vs [slki_d0]) and so is
   every [pc_is] equation, so a shared lemma would have to take six
   [instr]s and four pc equations as premises -- more interface than the
   two hundred lines it would save.

   WHY THE COUNTED [wp_iunlockput_sconf] IS ENOUGH ON C AND D, when the
   success arm needs the credited one: both arms are entered with the
   whole of begin_op's ten less the namei walk's at most one, so
   [iput_units] is in hand with six to spare and end_op takes [log_op] at
   any count ([SysLinkBudget]'s ledger stops mattering above the
   dirlink).  Neither arm has an [ilink] to spend either -- both branch
   BEFORE the [nlink++] mints one.

   THE SLOT-3 RELOAD IS PART OF EACH TAIL, not of the epilogue: the two
   callee-saved spills are shrink-wrapped and each arm restores exactly
   what its own path saved (SpecSysLink.v's header).  s2 is untouched on
   all three arms -- the [c.sdsp s2] at +0x5c is below every one of these
   branches -- so [M's s2 = m's s2] is a premise here and slot 4 rides
   through as the caller's junk. *)
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
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import StackOwn StackBytes.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfVc WpSconfBtype.
Require Import WpSmodeIntr WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import PanicStub.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import PathElems.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import IcacheBoot.
Require Import KallocInv.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecEndOp.
Require Import SpecIput.
Require Import SpecIunlockput.
Require Import SpecDirlink.
Require Import SpecNamex.
Require Import CodeSysLink.
Require Import SpecSysLink.
Require Import ProofSysLinkParts.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Set Printing Depth 40.

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.

Module SysLinkTails (Iunlockput : IUNLOCKPUT) (EndOp : END_OP).

Section ProofSysLinkTails.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !iregG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  (* ================================================================== *)
  (*  ARM B: +0xb6 end_op ; +0xba a5 = -1 ; +0xbc restore s1 ; +0xbe j   *)
  (* ================================================================== *)
  Lemma sl_tail_b `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (u : nat) (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool) (lks : gset string) (w4 : mword 64)
      (bnm bw bo : nat -> bv 8) :
    (K_end_op <= K - 38)%nat -> (38 <= K)%nat -> ((K - 38) + 38 = K)%nat ->
    log_geom_ok cov logstart ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    sl_sp sp0 M -> sl_thr m M ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    sl_al sp0 ->
    sie_cap_gpr M (K - 38) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) C b lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ pc_is (mword_of_int (SL + 0xb6)) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    p_pid (proc_addr jx) ↦₄{dq} pidv -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    log_op g u -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈ w4 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 6) jj ↦ₘ bnm jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ bw jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 38) jj ↦ₘ bo jj) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) C b lks -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr jx) ↦₄{dq} pidv -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKeo HK38 Kpop Hgeom Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs2 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext Hpc #Hpanic #Hbio #Hlog Hseam Hgen
              Hpid #Hprocs #Hdev #Hgeo #Hdlk Hop Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
              Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (slki_b6 with "Htext") as "Hib6".
    iPoseProof (slki_ba with "Htext") as "Hiba".
    iPoseProof (slki_bc with "Htext") as "Hibc".
    iPoseProof (slki_be with "Htext") as "Hibe".
    (* ===== +0xb6 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID0) (mword_of_int (SL + 0xb6)) Rra
              (mword_of_int 2092510 : mword 21) M (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hib6").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0xb6) : mword 64) 4)]> M).
    assert (Hjeo : add_vec (mword_of_int (SL + 0xb6) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092510 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0xb6) : mword 64) 4)
      by (rewrite /M1; apply upd_eq).
    assert (HM1sp : sl_sp sp0 M1)
      by (rewrite /sl_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs2 | nz]).
    assert (HM1thr : sl_thr m M1).
    { intros c Hc N2 N8 N9 N18. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID0 CID1 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID1) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev u pidv dq M1 (K - 38)%nat eb C b lks
              HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hpc Hpanic Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID2 Hq2 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpcba : ret_pc (M1 !!! Regidx Rra : mword 64)
                    = mword_of_int (SL + 0xba)) by (rewrite HM1ra; pcw).
    iEval (rewrite Hpcba) in "Hpc".
    assert (Heosp : sl_sp sp0 meo).
    { rewrite /sl_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM1sp. }
    assert (Heos2 : (meo !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs2 ltac:(vm_compute; reflexivity)).
      exact HM1s2. }
    assert (Heothr : sl_thr m meo).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HM1thr c Hc N2 N8 N9 N18). }
    (* ===== +0xba c.li a5,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID2) (mword_of_int (SL + 0xba)) Ra5
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 38)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hiba").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (P1 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> meo).
    assert (HP1a5 : (P1 !!! Regidx Ra5 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1sp : sl_sp sp0 P1)
      by (rewrite /sl_sp /P1 upd_ne; [exact Heosp | nz]).
    assert (HP1s2 : (P1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos2 | nz]).
    assert (HP1thr : sl_thr m P1).
    { intros c Hc N2 N8 N9 N18. rewrite /P1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8 N9 N18). }
    assert (Hppbc : add_vec_int (mword_of_int (SL + 0xba) : mword 64) 2
                    = mword_of_int (SL + 0xbc)) by pcw.
    iEval (rewrite Hppbc) in "Hpc".
    (* ===== +0xbc c.ldsp s1,280(sp) ===== *)
    assert (Hd3 : add_vec (P1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 35 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP1sp; apply sl_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID3) (mword_of_int (SL + 0xbc))
              (mword_of_int 35 : mword 6) Rs1 P1 (K - 38)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hibc [Hf3]").
    { iEval (rewrite Hd3). iExact "Hf3". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf3".
    iEval (rewrite Hd3) in "Hf3".
    set (P2 := <[Regidx Rs1 := regval_into_reg
                  (m !!! Regidx Rs1 : mword 64)]> P1).
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /P2; apply upd_eq).
    assert (HP2a5 : (P2 !!! Regidx Ra5 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1a5 | nz]).
    assert (HP2sp : sl_sp sp0 P2)
      by (rewrite /sl_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2s2 : (P2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s2 | nz]).
    assert (HP2thr : sl_thr m P2).
    { intros c Hc N2 N8 N9 N18. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2 N8 N9 N18). }
    assert (Hppbe : add_vec_int (mword_of_int (SL + 0xbc) : mword 64) 2
                    = mword_of_int (SL + 0xbe)) by pcw.
    iEval (rewrite Hppbe) in "Hpc".
    (* ===== +0xbe c.j +0x10c ===== *)
    iApply (wp_cj_s_sconf (CID := CID4) (mword_of_int (SL + 0xbe))
              (sign_extend' 21 (concat_vec (mword_of_int 39 : mword 11) ('b"0")))
              P2 (K - 38)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hibe").
    iIntros (CID5 Hq5). iNext. iIntros "Hcg Hpc".
    assert (Htg : add_vec (mword_of_int (SL + 0xbe) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 39 : mword 11) ('b"0"))))
                  = mword_of_int (SL + 0x10c)) by pcw.
    iEval (rewrite Htg) in "Hpc".
    iDestruct (cpu_own_transport CID2 CID5 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID2 CID5 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID2 CID5 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID5)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (sl_epilogue (CID0 := CID5) m P2 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) w4 bnm bw bo
              HK38 Kpop Hsp0 HP2sp HP2thr HP2s1 HP2s2 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
                    [Hown Htce Hcce Hpid Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha5f Hcg Hpc".
    iDestruct (cpu_own_transport CID5 CIDy 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID5 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID5 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf with "[%] [%] Hcg Hown Htce Hcce Hpc Hpid").
    { exact Hcsf. }
    { rewrite Ha5f. exact HP2a5. }
  Qed.


  (* ================================================================== *)
  (*  ARM C (+0xc0) AND ARM D (+0xd0): the two guard arms.               *)
  (*                                                                     *)
  (*    mv a0,s1 ; jal iunlockput ; jal end_op ; c.li a5,-1 ;             *)
  (*    c.ldsp s1,280(sp) ; c.j +0x10c                                    *)
  (*                                                                     *)
  (*  Six instructions, twice, at two addresses.  ARM C is the T_DIR      *)
  (*  test at +0x4c; ARM D is the NLINK_MAX guard at +0x58 -- the arm     *)
  (*  the kernel gained in 117c0e7, and the one whose FALL-THROUGH is     *)
  (*  what makes [SpecIupdate.wp_iupdate_link]'s disequality premise      *)
  (*  suppliable.  Neither arm has minted an [ilink] (both branch above   *)
  (*  the [nlink++]), so neither carries a ledger fragment and the        *)
  (*  COUNTED iunlockput is what both call.                               *)
  (* ================================================================== *)
  Lemma sl_tail_c `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used : gset Z)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (u : nat) (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool) (lks : gset string) (w4 : mword 64)
      (bnm bw bo : nat -> bv 8) :
    (K_iunlockput <= K - 38)%nat -> (K_end_op <= K - 38)%nat ->
    (38 <= K)%nat -> ((K - 38) + 38 = K)%nat ->
    (kk < NINODE)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    cov_below cov size ->
    (iput_units <= u)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    sl_sp sp0 M -> sl_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    sl_al sp0 ->
    sie_cap_gpr M (K - 38) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) C b lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ pc_is (mword_of_int (SL + 0xc0)) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart kk -∗
    ireg_inv gi gfs inodestart nib -∗
    is_sleeplock gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok cn kk) -∗
    sleeplocked gisl -∗
    sl_pid (i_lock (ientry kk)) ↦₄ pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    inode_ref_short kk (qi + s)%Qp qi dev inum -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used -∗
    p_pid (proc_addr jx) ↦₄{dq} pidv -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots bn 3 -∗
    log_op g u -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈ w4 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 6) jj ↦ₘ bnm jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ bw jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 38) jj ↦ₘ bo jj) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z),
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        ⌜used' ⊆ used⌝ -∗
        sie_cap_gpr mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) C b lks -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr jx) ↦₄{dq} pidv -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        bitmap_res gfs bmapstart cov logstart size used' -∗
        bslots bn 3 -∗
        iref_slot -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKup HKeo HK38 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
           Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1
           HMs2 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext Hpc #Hpanic #Hbio #Hlog Hseam Hgen
              #Hitab #Hitinv #Hesck #Hireg #Hslkk Hslkd Hslpid Hdep Hidev
              Hiinum Hivalid Hload #Hshot Hkeep Hsbb Hsbi Hbmres Hpid #Hprocs
              #Hdev #Hgeo #Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 HbN HbW HbO Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (slki_c0 with "Htext") as "Hi0".
    iPoseProof (slki_c2 with "Htext") as "Hi1".
    iPoseProof (slki_c6 with "Htext") as "Hi2".
    iPoseProof (slki_ca with "Htext") as "Hi3".
    iPoseProof (slki_cc with "Htext") as "Hi4".
    iPoseProof (slki_ce with "Htext") as "Hi5".
    (* ===== +0xc0 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID0) (mword_of_int (SL + 0xc0)) Ra0 Rs1
              M (K - 38)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs1))]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = ientry kk).
    { etransitivity; [ rewrite /M1; apply upd_eq |].
      rewrite add_vec_zero_l. exact HMs1. }
    assert (HM1sp : sl_sp sp0 M1)
      by (rewrite /sl_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs2 | nz]).
    assert (HM1thr : sl_thr m M1).
    { intros c Hc N2 N8 N9 N18. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18). }
    assert (Hpp1 : add_vec_int (mword_of_int (SL + 0xc0) : mword 64) 2
                   = mword_of_int (SL + 0xc2)) by pcw.
    iEval (rewrite Hpp1) in "Hpc".
    (* ===== +0xc2 jal ra,iunlockput ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SL + 0xc2)) Rra
              (mword_of_int 2090288 : mword 21) M1 (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0xc2) : mword 64) 4)]> M1).
    assert (Hjup : add_vec (mword_of_int (SL + 0xc2) : mword 64)
                     (sign_extend' 64 (mword_of_int 2090288 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0xc2) : mword 64) 4)
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2sp : sl_sp sp0 M2)
      by (rewrite /sl_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2s2 : (M2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s2 | nz]).
    assert (HM2thr : sl_thr m M2).
    { intros c Hc N2 N8 N9 N18. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID2 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID2 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (Iunlockput.wp_iunlockput_sconf (CID := CID2) gs jx gl gu gd gk
              pd pav pu bn g gfs gi cn gtl gil gisl cov logstart bmapstart
              inodestart nib size dev used kk qi s gy inum dn bm u pidv dq
              dqb dqs M2 (K - 38)%nat eb C b lks
              HKup Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog
              Hinb Hcovb Hiu Hj Hgl HM2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hpc Hpanic Hbio Hlog Hitab Hitinv
                    Hesck Hireg Hslkk Hslkd Hslpid Hdep Hidev Hiinum Hivalid
                    Hload Hshot Hkeep Hsbb Hsbi Hbmres Hpid Hprocs Hdev Hgeo
                    Hdlk Hbsl Hop").
    iIntros (CID3 Hq3 mup n2 used2)
      "%Hcsup Hcg Hown Htce Hcce Hpc Hpid Hsbb Hsbi %Hused2 Hbmres Hbsl %Hn2
       Hop Hislot".
    assert (Hpc2 : ret_pc (M2 !!! Regidx Rra : mword 64)
                   = mword_of_int (SL + 0xc6)) by (rewrite HM2ra; pcw).
    iEval (rewrite Hpc2) in "Hpc".
    assert (Hupsp : sl_sp sp0 mup).
    { rewrite /sl_sp (callee_saved_lookup Hcsup csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM2sp. }
    assert (Hups2 : (mup !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsup Rs2 ltac:(vm_compute; reflexivity)).
      exact HM2s2. }
    assert (Hupthr : sl_thr m mup).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcsup c Hc).
      exact (HM2thr c Hc N2 N8 N9 N18). }
    (* ===== +0xc6 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID3) (mword_of_int (SL + 0xc6)) Rra
              (mword_of_int 2092494 : mword 21) mup (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0xc6) : mword 64) 4)]> mup).
    assert (Hjeo : add_vec (mword_of_int (SL + 0xc6) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092494 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0xc6) : mword 64) 4)
      by (rewrite /M3; apply upd_eq).
    assert (HM3sp : sl_sp sp0 M3)
      by (rewrite /sl_sp /M3 upd_ne; [exact Hupsp | nz]).
    assert (HM3s2 : (M3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M3 upd_ne; [exact Hups2 | nz]).
    assert (HM3thr : sl_thr m M3).
    { intros c Hc N2 N8 N9 N18. rewrite /M3 upd_ne; [| regne].
      exact (Hupthr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID3 CID4 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID4) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev n2 pidv dq M3 (K - 38)%nat eb C b lks
              HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hpc Hpanic Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID5 Hq5 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpc3 : ret_pc (M3 !!! Regidx Rra : mword 64)
                   = mword_of_int (SL + 0xca)) by (rewrite HM3ra; pcw).
    iEval (rewrite Hpc3) in "Hpc".
    assert (Heosp : sl_sp sp0 meo).
    { rewrite /sl_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM3sp. }
    assert (Heos2 : (meo !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs2 ltac:(vm_compute; reflexivity)).
      exact HM3s2. }
    assert (Heothr : sl_thr m meo).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HM3thr c Hc N2 N8 N9 N18). }
    (* ===== +0xca c.li a5,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID5) (mword_of_int (SL + 0xca)) Ra5
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 38)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi3").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (P1 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> meo).
    assert (HP1a5 : (P1 !!! Regidx Ra5 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1sp : sl_sp sp0 P1)
      by (rewrite /sl_sp /P1 upd_ne; [exact Heosp | nz]).
    assert (HP1s2 : (P1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos2 | nz]).
    assert (HP1thr : sl_thr m P1).
    { intros c Hc N2 N8 N9 N18. rewrite /P1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8 N9 N18). }
    assert (Hpp4 : add_vec_int (mword_of_int (SL + 0xca) : mword 64) 2
                   = mword_of_int (SL + 0xcc)) by pcw.
    iEval (rewrite Hpp4) in "Hpc".
    (* ===== +0xcc c.ldsp s1,280(sp) ===== *)
    assert (Hd3 : add_vec (P1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 35 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP1sp; apply sl_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID6) (mword_of_int (SL + 0xcc))
              (mword_of_int 35 : mword 6) Rs1 P1 (K - 38)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi4 [Hf3]").
    { iEval (rewrite Hd3). iExact "Hf3". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf3".
    iEval (rewrite Hd3) in "Hf3".
    set (P2 := <[Regidx Rs1 := regval_into_reg
                  (m !!! Regidx Rs1 : mword 64)]> P1).
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /P2; apply upd_eq).
    assert (HP2a5 : (P2 !!! Regidx Ra5 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1a5 | nz]).
    assert (HP2sp : sl_sp sp0 P2)
      by (rewrite /sl_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2s2 : (P2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s2 | nz]).
    assert (HP2thr : sl_thr m P2).
    { intros c Hc N2 N8 N9 N18. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2 N8 N9 N18). }
    assert (Hpp5 : add_vec_int (mword_of_int (SL + 0xcc) : mword 64) 2
                   = mword_of_int (SL + 0xce)) by pcw.
    iEval (rewrite Hpp5) in "Hpc".
    (* ===== +0xce c.j +0x10c ===== *)
    iApply (wp_cj_s_sconf (CID := CID7) (mword_of_int (SL + 0xce))
              (sign_extend' 21 (concat_vec (mword_of_int 31 : mword 11) ('b"0")))
              P2 (K - 38)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi5").
    iIntros (CID8 Hq8). iNext. iIntros "Hcg Hpc".
    assert (Htg : add_vec (mword_of_int (SL + 0xce) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 31 : mword 11) ('b"0"))))
                  = mword_of_int (SL + 0x10c)) by pcw.
    iEval (rewrite Htg) in "Hpc".
    iDestruct (cpu_own_transport CID5 CID8 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID5 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID5 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID8)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (sl_epilogue (CID0 := CID8) m P2 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) w4 bnm bw bo
              HK38 Kpop Hsp0 HP2sp HP2thr HP2s1 HP2s2 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
                    [Hown Htce Hcce Hpid Hsbb Hsbi Hbmres Hbsl Hislot Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha5f Hcg Hpc".
    iDestruct (cpu_own_transport CID8 CIDy 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID8 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID8 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf used2 with "[%] [%] [%] Hcg Hown Htce Hcce Hpc Hpid
              Hsbb Hsbi Hbmres Hbsl Hislot").
    { exact Hcsf. }
    { rewrite Ha5f. exact HP2a5. }
    { exact Hused2. }
  Qed.


  (* ---- ARM D: the NLINK_MAX guard's own tail, ARM C's six
     instructions at +0xd0.  See ARM C's banner. ---- *)
  Lemma sl_tail_d `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used : gset Z)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (u : nat) (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool) (lks : gset string) (w4 : mword 64)
      (bnm bw bo : nat -> bv 8) :
    (K_iunlockput <= K - 38)%nat -> (K_end_op <= K - 38)%nat ->
    (38 <= K)%nat -> ((K - 38) + 38 = K)%nat ->
    (kk < NINODE)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    cov_below cov size ->
    (iput_units <= u)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    sl_sp sp0 M -> sl_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    sl_al sp0 ->
    sie_cap_gpr M (K - 38) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) C b lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ pc_is (mword_of_int (SL + 0xd0)) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart kk -∗
    ireg_inv gi gfs inodestart nib -∗
    is_sleeplock gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok cn kk) -∗
    sleeplocked gisl -∗
    sl_pid (i_lock (ientry kk)) ↦₄ pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    inode_ref_short kk (qi + s)%Qp qi dev inum -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used -∗
    p_pid (proc_addr jx) ↦₄{dq} pidv -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots bn 3 -∗
    log_op g u -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈ w4 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 6) jj ↦ₘ bnm jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ bw jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 38) jj ↦ₘ bo jj) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z),
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        ⌜used' ⊆ used⌝ -∗
        sie_cap_gpr mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) C b lks -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr jx) ↦₄{dq} pidv -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        bitmap_res gfs bmapstart cov logstart size used' -∗
        bslots bn 3 -∗
        iref_slot -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKup HKeo HK38 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
           Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1
           HMs2 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext Hpc #Hpanic #Hbio #Hlog Hseam Hgen
              #Hitab #Hitinv #Hesck #Hireg #Hslkk Hslkd Hslpid Hdep Hidev
              Hiinum Hivalid Hload #Hshot Hkeep Hsbb Hsbi Hbmres Hpid #Hprocs
              #Hdev #Hgeo #Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 HbN HbW HbO Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (slki_d0 with "Htext") as "Hi0".
    iPoseProof (slki_d2 with "Htext") as "Hi1".
    iPoseProof (slki_d6 with "Htext") as "Hi2".
    iPoseProof (slki_da with "Htext") as "Hi3".
    iPoseProof (slki_dc with "Htext") as "Hi4".
    iPoseProof (slki_de with "Htext") as "Hi5".
    (* ===== +0xd0 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID0) (mword_of_int (SL + 0xd0)) Ra0 Rs1
              M (K - 38)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs1))]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = ientry kk).
    { etransitivity; [ rewrite /M1; apply upd_eq |].
      rewrite add_vec_zero_l. exact HMs1. }
    assert (HM1sp : sl_sp sp0 M1)
      by (rewrite /sl_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs2 | nz]).
    assert (HM1thr : sl_thr m M1).
    { intros c Hc N2 N8 N9 N18. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18). }
    assert (Hpp1 : add_vec_int (mword_of_int (SL + 0xd0) : mword 64) 2
                   = mword_of_int (SL + 0xd2)) by pcw.
    iEval (rewrite Hpp1) in "Hpc".
    (* ===== +0xd2 jal ra,iunlockput ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SL + 0xd2)) Rra
              (mword_of_int 2090272 : mword 21) M1 (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0xd2) : mword 64) 4)]> M1).
    assert (Hjup : add_vec (mword_of_int (SL + 0xd2) : mword 64)
                     (sign_extend' 64 (mword_of_int 2090272 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0xd2) : mword 64) 4)
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2sp : sl_sp sp0 M2)
      by (rewrite /sl_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2s2 : (M2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s2 | nz]).
    assert (HM2thr : sl_thr m M2).
    { intros c Hc N2 N8 N9 N18. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID2 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID2 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (Iunlockput.wp_iunlockput_sconf (CID := CID2) gs jx gl gu gd gk
              pd pav pu bn g gfs gi cn gtl gil gisl cov logstart bmapstart
              inodestart nib size dev used kk qi s gy inum dn bm u pidv dq
              dqb dqs M2 (K - 38)%nat eb C b lks
              HKup Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog
              Hinb Hcovb Hiu Hj Hgl HM2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hpc Hpanic Hbio Hlog Hitab Hitinv
                    Hesck Hireg Hslkk Hslkd Hslpid Hdep Hidev Hiinum Hivalid
                    Hload Hshot Hkeep Hsbb Hsbi Hbmres Hpid Hprocs Hdev Hgeo
                    Hdlk Hbsl Hop").
    iIntros (CID3 Hq3 mup n2 used2)
      "%Hcsup Hcg Hown Htce Hcce Hpc Hpid Hsbb Hsbi %Hused2 Hbmres Hbsl %Hn2
       Hop Hislot".
    assert (Hpc2 : ret_pc (M2 !!! Regidx Rra : mword 64)
                   = mword_of_int (SL + 0xd6)) by (rewrite HM2ra; pcw).
    iEval (rewrite Hpc2) in "Hpc".
    assert (Hupsp : sl_sp sp0 mup).
    { rewrite /sl_sp (callee_saved_lookup Hcsup csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM2sp. }
    assert (Hups2 : (mup !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsup Rs2 ltac:(vm_compute; reflexivity)).
      exact HM2s2. }
    assert (Hupthr : sl_thr m mup).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcsup c Hc).
      exact (HM2thr c Hc N2 N8 N9 N18). }
    (* ===== +0xd6 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID3) (mword_of_int (SL + 0xd6)) Rra
              (mword_of_int 2092478 : mword 21) mup (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0xd6) : mword 64) 4)]> mup).
    assert (Hjeo : add_vec (mword_of_int (SL + 0xd6) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092478 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0xd6) : mword 64) 4)
      by (rewrite /M3; apply upd_eq).
    assert (HM3sp : sl_sp sp0 M3)
      by (rewrite /sl_sp /M3 upd_ne; [exact Hupsp | nz]).
    assert (HM3s2 : (M3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M3 upd_ne; [exact Hups2 | nz]).
    assert (HM3thr : sl_thr m M3).
    { intros c Hc N2 N8 N9 N18. rewrite /M3 upd_ne; [| regne].
      exact (Hupthr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID3 CID4 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID4) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev n2 pidv dq M3 (K - 38)%nat eb C b lks
              HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hpc Hpanic Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID5 Hq5 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpc3 : ret_pc (M3 !!! Regidx Rra : mword 64)
                   = mword_of_int (SL + 0xda)) by (rewrite HM3ra; pcw).
    iEval (rewrite Hpc3) in "Hpc".
    assert (Heosp : sl_sp sp0 meo).
    { rewrite /sl_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM3sp. }
    assert (Heos2 : (meo !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs2 ltac:(vm_compute; reflexivity)).
      exact HM3s2. }
    assert (Heothr : sl_thr m meo).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HM3thr c Hc N2 N8 N9 N18). }
    (* ===== +0xda c.li a5,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID5) (mword_of_int (SL + 0xda)) Ra5
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 38)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi3").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (P1 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> meo).
    assert (HP1a5 : (P1 !!! Regidx Ra5 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1sp : sl_sp sp0 P1)
      by (rewrite /sl_sp /P1 upd_ne; [exact Heosp | nz]).
    assert (HP1s2 : (P1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos2 | nz]).
    assert (HP1thr : sl_thr m P1).
    { intros c Hc N2 N8 N9 N18. rewrite /P1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8 N9 N18). }
    assert (Hpp4 : add_vec_int (mword_of_int (SL + 0xda) : mword 64) 2
                   = mword_of_int (SL + 0xdc)) by pcw.
    iEval (rewrite Hpp4) in "Hpc".
    (* ===== +0xdc c.ldsp s1,280(sp) ===== *)
    assert (Hd3 : add_vec (P1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 35 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP1sp; apply sl_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID6) (mword_of_int (SL + 0xdc))
              (mword_of_int 35 : mword 6) Rs1 P1 (K - 38)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi4 [Hf3]").
    { iEval (rewrite Hd3). iExact "Hf3". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf3".
    iEval (rewrite Hd3) in "Hf3".
    set (P2 := <[Regidx Rs1 := regval_into_reg
                  (m !!! Regidx Rs1 : mword 64)]> P1).
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /P2; apply upd_eq).
    assert (HP2a5 : (P2 !!! Regidx Ra5 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1a5 | nz]).
    assert (HP2sp : sl_sp sp0 P2)
      by (rewrite /sl_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2s2 : (P2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s2 | nz]).
    assert (HP2thr : sl_thr m P2).
    { intros c Hc N2 N8 N9 N18. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2 N8 N9 N18). }
    assert (Hpp5 : add_vec_int (mword_of_int (SL + 0xdc) : mword 64) 2
                   = mword_of_int (SL + 0xde)) by pcw.
    iEval (rewrite Hpp5) in "Hpc".
    (* ===== +0xde c.j +0x10c ===== *)
    iApply (wp_cj_s_sconf (CID := CID7) (mword_of_int (SL + 0xde))
              (sign_extend' 21 (concat_vec (mword_of_int 23 : mword 11) ('b"0")))
              P2 (K - 38)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi5").
    iIntros (CID8 Hq8). iNext. iIntros "Hcg Hpc".
    assert (Htg : add_vec (mword_of_int (SL + 0xde) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 23 : mword 11) ('b"0"))))
                  = mword_of_int (SL + 0x10c)) by pcw.
    iEval (rewrite Htg) in "Hpc".
    iDestruct (cpu_own_transport CID5 CID8 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID5 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID5 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID8)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (sl_epilogue (CID0 := CID8) m P2 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) w4 bnm bw bo
              HK38 Kpop Hsp0 HP2sp HP2thr HP2s1 HP2s2 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
                    [Hown Htce Hcce Hpid Hsbb Hsbi Hbmres Hbsl Hislot Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha5f Hcg Hpc".
    iDestruct (cpu_own_transport CID8 CIDy 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID8 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID8 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf used2 with "[%] [%] [%] Hcg Hown Htce Hcce Hpc Hpid
              Hsbb Hsbi Hbmres Hbsl Hislot").
    { exact Hcsf. }
    { rewrite Ha5f. exact HP2a5. }
    { exact Hused2. }
  Qed.

End ProofSysLinkTails.

End SysLinkTails.
