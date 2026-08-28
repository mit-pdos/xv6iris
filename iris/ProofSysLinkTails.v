(* ProofSysLinkTails.v -- sys_link's THREE "-1" tails, as block lemmas.
   These apply callees' contracts, so they live inside a module functor
   ([design/spec-modules.md]); the functor is NOT ascribed to a signature,
   because it is a parts layer -- [ProofSysLink.v] instantiates it beside
   its own callee arguments and the seal happens there.

     ARM B  (+0xbc .. +0xc4)  namei(old) returned 0
                              end_op; a5 = -1; restore s1; join
     ARM C  (+0xc6 .. +0xd4)  ip->type == T_DIR
                              iunlockput(ip); end_op; a5 = -1; restore s1
     ARM D  (+0xd6 .. +0xe4)  ip->nlink == NLINK_MAX -- THE NLINK_MAX ARM
                              byte-identical to ARM C at a shifted address
     ARM E2 (+0xe6 .. +0xec)  dp->nlink == 0 -- THE ORPHAN GUARD'S ARM
                              (xv6 f60ff58): ARM F's block one block
                              earlier, plus the [c.j] ARM F does not need

   ARMS C AND D ARE THE SAME SIX INSTRUCTIONS AND ARE STILL TWO LEMMAS.
   Their decode facts are per-address ([slki_c6] vs [slki_d6]) and so is
   every [pc_is] equation, so a shared lemma would have to take six
   [instr]s and four pc equations as premises -- more interface than the
   two hundred lines it would save.

   WHY THE COUNTED [wp_iunlockput_sconf] IS ENOUGH ON C AND D, when the
   success arm needs the credited one: both arms are entered with the
   whole of begin_op's ten less the namei walk's at most one, so
   [iput_units] is in hand with six to spare and end_op takes [log_op] at
   any count ([SysLinkBudget]'s ledger stops mattering above the
   dirlink).  Neither arm has a link token to spend either -- both branch
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
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved KernelText.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeIntr WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
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
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import DirView.
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import IcacheBoot.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import IregLinkNz.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecIupdate.
Require Import SpecIput.
Require Import SpecIunlockput.
Require Import CodeSysLink.
Require Import ProofSysLinkParts.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.

Set Printing Depth 40.

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.

Module SysLinkTails (Ilock : ILOCK) (Iupdate : IUPDATE)
                    (Iunlockput : IUNLOCKPUT) (EndOp : END_OP).

Section ProofSysLinkTails.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  (* the three-slot pool, split for ilock's / iupdate's needs and rejoined *)
  Lemma sl_bs3 :
    (bslots 3 : iProp Σ) ⊣⊢ bslot ∗ bslots 2.
  Proof. rewrite /bslot. change 3%nat with (1 + 2)%nat. apply bslots_op. Qed.

  (* ================================================================== *)
  (*  ARM B: +0xbc end_op ; +0xc0 a5 = -1 ; +0xc2 restore s1 ; +0xc4 j   *)
  (* ================================================================== *)
  Lemma sl_tail_b `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (u : nat) (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w4 : mword 64)
      (bnm bw bo : nat -> bv 8) (Vpr : pprivate) :
    (K_end_op <= K - 38)%nat -> (38 <= K)%nat -> ((K - 38) + 38 = K)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    sl_sp sp0 M -> sl_thr m M ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    sl_al sp0 ->
    sie_cap_gpr KT1 M (K - 38) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SL + 0xbc)) -∗
    panic_env -∗
    bio_ctx bn (fs_view fsc_fs gd icfg_dev fsc_cov) -∗
    log_ctx icfg_log bn fsc_fs fsc_cov fsc_logst icfg_dev -∗
    fs_crash_seam fsc_cov fsc_logst -∗
    gen_cert -∗
    proc_priv_bare (proc_addr jx) pidv Vpr -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    log_op icfg_log u -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 6) jj ↦ₘ[KT1] bnm jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bw jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 38) jj ↦ₘ[KT1] bo jj) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        proc_priv_bare (proc_addr jx) pidv Vpr -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKeo HK38 Kpop Hgeom Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs2 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              Hpid #Hprocs #Hdev #Hgeo #Hdlk Hop Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
              Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0xbc jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID0) (mword_of_int (SL + 0xbc)) Rra
              (mword_of_int 2092490 : mword 21) M (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_bc with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0xbc) : mword 64) 4)]> M).
    assert (Hjeo : add_vec (mword_of_int (SL + 0xbc) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092490 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0xbc) : mword 64) 4)
      by (rewrite /M1; apply upd_eq).
    assert (HM1sp : sl_sp sp0 M1)
      by (rewrite /sl_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs2 | nz]).
    assert (HM1thr : sl_thr m M1).
    { intros c Hc N2 N8 N9 N18. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID0 CID1 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID1) gs jx gl gu gd gk pd pav pu bn
              icfg_log fsc_fs fsc_cov fsc_logst icfg_dev u pidv dq M1 (K - 38)%nat eb b lks
              Vpr HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID2 Hq2 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpcc0 : ret_pc (M1 !!! Regidx Rra : mword 64)
                    = mword_of_int (SL + 0xc0)) by (rewrite HM1ra; pcw).
    iEval (rewrite Hpcc0) in "Hpc".
    assert (Heosp : sl_sp sp0 meo).
    { rewrite /sl_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM1sp. }
    assert (Heos2 : (meo !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs2 ltac:(vm_compute; reflexivity)).
      exact HM1s2. }
    assert (Heothr : sl_thr m meo).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HM1thr c Hc N2 N8 N9 N18). }
    (* ===== +0xc0 c.li a5,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID2) (mword_of_int (SL + 0xc0)) Ra5
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 38)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (slki_c0 with "Htext"). }
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
    assert (Hppc2 : add_vec_int (mword_of_int (SL + 0xc0) : mword 64) 2
                    = mword_of_int (SL + 0xc2)) by pcw.
    iEval (rewrite Hppc2) in "Hpc".
    (* ===== +0xc2 c.ldsp s1,280(sp) ===== *)
    assert (Hd3 : add_vec (P1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 35 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP1sp; apply sl_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID3) (mword_of_int (SL + 0xc2))
              (mword_of_int 35 : mword 6) Rs1 P1 (K - 38)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf3]").
    { iApply (slki_c2 with "Htext"). }
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
    assert (Hppc4 : add_vec_int (mword_of_int (SL + 0xc2) : mword 64) 2
                    = mword_of_int (SL + 0xc4)) by pcw.
    iEval (rewrite Hppc4) in "Hpc".
    (* ===== +0xc4 c.j +0x11a ===== *)
    iApply (wp_cj_s_sconf (CID := CID4) (mword_of_int (SL + 0xc4))
              (sign_extend' 21 (concat_vec (mword_of_int 43 : mword 11) ('b"0")))
              P2 (K - 38)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_c4 with "Htext"). }
    iIntros (CID5 Hq5). iNext. iIntros "Hcg Hpc".
    assert (Htg : add_vec (mword_of_int (SL + 0xc4) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 43 : mword 11) ('b"0"))))
                  = mword_of_int (SL + 0x11a)) by pcw.
    iEval (rewrite Htg) in "Hpc".
    iDestruct (cpu_own_transport CID2 CID5 0 eb (proc_addr jx) b
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
    iDestruct (cpu_own_transport CID5 CIDy 0 eb (proc_addr jx) b
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
  (*  ARM C (+0xc6) AND ARM D (+0xd6): the two guard arms.               *)
  (*                                                                     *)
  (*    mv a0,s1 ; jal iunlockput ; jal end_op ; c.li a5,-1 ;             *)
  (*    c.ldsp s1,280(sp) ; c.j +0x11a                                    *)
  (*                                                                     *)
  (*  Six instructions, twice, at two addresses.  ARM C is the T_DIR      *)
  (*  test at +0x4c; ARM D is the NLINK_MAX guard at +0x58 -- the arm     *)
  (*  the kernel gained in 117c0e7, and the one whose FALL-THROUGH is     *)
  (*  what makes [SpecIupdate.wp_iupdate_link]'s disequality premise      *)
  (*  suppliable.  Neither arm has minted a link token (both branch      *)
  (*  above the [nlink++]), so neither carries a fragment and the         *)
  (*  COUNTED iunlockput is what both call.                               *)
  (* ================================================================== *)
  Lemma sl_tail_c `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (gil gisl : gname)
      (bmapstart : Z)
      (size : Z)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (u : nat) (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w4 : mword 64)
      (bnm bw bo : nat -> bv 8) (Vpr : pprivate) :
    (K_iunlockput <= K - 38)%nat -> (K_end_op <= K - 38)%nat ->
    (38 <= K)%nat -> ((K - 38) + 38 = K)%nat ->
    (kk < NINODE)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ fsc_cov ->
    ~ (bmapstart ∈ log_region_set fsc_logst) ->
    0 <= icfg_ist ->
    IBLOCK inum icfg_ist ∈ fsc_cov ->
    ~ (IBLOCK inum icfg_ist ∈ log_region_set fsc_logst) ->
    bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
    cov_below fsc_cov size ->
    (iput_units <= u)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    sl_sp sp0 M -> sl_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    sl_al sp0 ->
    sie_cap_gpr KT1 M (K - 38) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SL + 0xc6)) -∗
    panic_env -∗
    bio_ctx bn (fs_view fsc_fs gd icfg_dev fsc_cov) -∗
    log_ctx icfg_log bn fsc_fs fsc_cov fsc_logst icfg_dev -∗
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
    ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    (* ...AND THE INUM'S FREEZE TOKEN, [SpecIunlockput]'s new premise since
       iclaim-ledger.md §3.9 (RULING A-prime): the payload's A-custody
       conjunct, relayed from the caller's own ilock. *)
    ifreeze_off (bv_unsigned inum) -∗
    inode_ref_short kk (qi + s)%Qp qi icfg_dev inum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned inum) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
    proc_priv_bare (proc_addr jx) pidv Vpr -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots 3 -∗
    (* the BUDGET half only: half this transaction's element is parked
       in the escrow's write arm for the whole locked window
       (durable-disk B''-tx); the release hands the whole one back *)
    log_opb icfg_log u -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 6) jj ↦ₘ[KT1] bnm jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bw jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 38) jj ↦ₘ[KT1] bo jj) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile),
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        proc_priv_bare (proc_addr jx) pidv Vpr -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
        bslots 3 -∗
        iref_slot -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKup HKeo HK38 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
           Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1
           HMs2 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              #Hitab #Hitinv #Hesck #Hireg #Hropen #Hslkk Hslkd Hdep Hidev
              Hiinum Hivalid Hload #Hshot Hfrz Hkeep Hru Hsbb Hsbi #Hbmres Hpid #Hprocs
              #Hdev #Hgeo #Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 HbN HbW HbO Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0xc6 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID0) (mword_of_int (SL + 0xc6)) Ra0 Rs1
              M (K - 38)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (slki_c6 with "Htext"). }
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
    assert (Hpp1 : add_vec_int (mword_of_int (SL + 0xc6) : mword 64) 2
                   = mword_of_int (SL + 0xc8)) by pcw.
    iEval (rewrite Hpp1) in "Hpc".
    (* ===== +0xc8 jal ra,iunlockput ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SL + 0xc8)) Rra
              (mword_of_int 2090268 : mword 21) M1 (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_c8 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0xc8) : mword 64) 4)]> M1).
    assert (Hjup : add_vec (mword_of_int (SL + 0xc8) : mword 64)
                     (sign_extend' 64 (mword_of_int 2090268 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0xc8) : mword 64) 4)
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
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID2 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID2 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (Iunlockput.wp_iunlockput_tx_sconf (CID := CID2) gs jx gl gu gd gk
              pd pav pu bn gil gisl bmapstart
 size kk qi s gy inum dn bm u pidv dq
              dqb dqs M2 (K - 38)%nat eb b lks
              Vpr HKup Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog
              Hinb Hcovb Hiu Hj Hgl HM2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hitab Hitinv
                    Hesck Hireg Hropen Hslkk Hslkd Hdep Hidev Hiinum Hivalid
                    Hload Hshot Hfrz [$Hkeep $Hru] Hsbb Hsbi Hbmres Hpid Hprocs Hdev Hgeo
                    Hdlk Hbsl Hop").
    iIntros (CID3 Hq3 mup n2)
      "%Hcsup Hcg Hown Htce Hcce Hpc Hpid Hsbb Hsbi Hbsl %Hn2
       Hop Hislot".
    assert (Hpc2 : ret_pc (M2 !!! Regidx Rra : mword 64)
                   = mword_of_int (SL + 0xcc)) by (rewrite HM2ra; pcw).
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
    (* ===== +0xcc jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID3) (mword_of_int (SL + 0xcc)) Rra
              (mword_of_int 2092474 : mword 21) mup (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_cc with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0xcc) : mword 64) 4)]> mup).
    assert (Hjeo : add_vec (mword_of_int (SL + 0xcc) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092474 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0xcc) : mword 64) 4)
      by (rewrite /M3; apply upd_eq).
    assert (HM3sp : sl_sp sp0 M3)
      by (rewrite /sl_sp /M3 upd_ne; [exact Hupsp | nz]).
    assert (HM3s2 : (M3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M3 upd_ne; [exact Hups2 | nz]).
    assert (HM3thr : sl_thr m M3).
    { intros c Hc N2 N8 N9 N18. rewrite /M3 upd_ne; [| regne].
      exact (Hupthr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID3 CID4 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID4) gs jx gl gu gd gk pd pav pu bn
              icfg_log fsc_fs fsc_cov fsc_logst icfg_dev n2 pidv dq M3 (K - 38)%nat eb b lks
              Vpr HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID5 Hq5 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpc3 : ret_pc (M3 !!! Regidx Rra : mword 64)
                   = mword_of_int (SL + 0xd0)) by (rewrite HM3ra; pcw).
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
    (* ===== +0xd0 c.li a5,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID5) (mword_of_int (SL + 0xd0)) Ra5
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 38)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (slki_d0 with "Htext"). }
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
    assert (Hpp4 : add_vec_int (mword_of_int (SL + 0xd0) : mword 64) 2
                   = mword_of_int (SL + 0xd2)) by pcw.
    iEval (rewrite Hpp4) in "Hpc".
    (* ===== +0xd2 c.ldsp s1,280(sp) ===== *)
    assert (Hd3 : add_vec (P1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 35 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP1sp; apply sl_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID6) (mword_of_int (SL + 0xd2))
              (mword_of_int 35 : mword 6) Rs1 P1 (K - 38)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf3]").
    { iApply (slki_d2 with "Htext"). }
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
    assert (Hpp5 : add_vec_int (mword_of_int (SL + 0xd2) : mword 64) 2
                   = mword_of_int (SL + 0xd4)) by pcw.
    iEval (rewrite Hpp5) in "Hpc".
    (* ===== +0xd4 c.j +0x11a ===== *)
    iApply (wp_cj_s_sconf (CID := CID7) (mword_of_int (SL + 0xd4))
              (sign_extend' 21 (concat_vec (mword_of_int 35 : mword 11) ('b"0")))
              P2 (K - 38)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_d4 with "Htext"). }
    iIntros (CID8 Hq8). iNext. iIntros "Hcg Hpc".
    assert (Htg : add_vec (mword_of_int (SL + 0xd4) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 35 : mword 11) ('b"0"))))
                  = mword_of_int (SL + 0x11a)) by pcw.
    iEval (rewrite Htg) in "Hpc".
    iDestruct (cpu_own_transport CID5 CID8 0 eb (proc_addr jx) b
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
                    [Hown Htce Hcce Hpid Hsbb Hsbi Hbsl Hislot Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha5f Hcg Hpc".
    iDestruct (cpu_own_transport CID8 CIDy 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID8 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID8 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf with "[%] [%] Hcg Hown Htce Hcce Hpc Hpid
              Hsbb Hsbi Hbsl Hislot").
    { exact Hcsf. }
    { rewrite Ha5f. exact HP2a5. }
  Qed.


  (* ---- ARM D: the NLINK_MAX guard's own tail, ARM C's six
     instructions at +0xd6.  See ARM C's banner. ---- *)
  Lemma sl_tail_d `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (gil gisl : gname)
      (bmapstart : Z)
      (size : Z)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (u : nat) (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w4 : mword 64)
      (bnm bw bo : nat -> bv 8) (Vpr : pprivate) :
    (K_iunlockput <= K - 38)%nat -> (K_end_op <= K - 38)%nat ->
    (38 <= K)%nat -> ((K - 38) + 38 = K)%nat ->
    (kk < NINODE)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ fsc_cov ->
    ~ (bmapstart ∈ log_region_set fsc_logst) ->
    0 <= icfg_ist ->
    IBLOCK inum icfg_ist ∈ fsc_cov ->
    ~ (IBLOCK inum icfg_ist ∈ log_region_set fsc_logst) ->
    bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
    cov_below fsc_cov size ->
    (iput_units <= u)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    sl_sp sp0 M -> sl_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    sl_al sp0 ->
    sie_cap_gpr KT1 M (K - 38) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SL + 0xd6)) -∗
    panic_env -∗
    bio_ctx bn (fs_view fsc_fs gd icfg_dev fsc_cov) -∗
    log_ctx icfg_log bn fsc_fs fsc_cov fsc_logst icfg_dev -∗
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
    ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    (* ...AND THE INUM'S FREEZE TOKEN, [SpecIunlockput]'s new premise since
       iclaim-ledger.md §3.9 (RULING A-prime): the payload's A-custody
       conjunct, relayed from the caller's own ilock. *)
    ifreeze_off (bv_unsigned inum) -∗
    inode_ref_short kk (qi + s)%Qp qi icfg_dev inum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned inum) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
    proc_priv_bare (proc_addr jx) pidv Vpr -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots 3 -∗
    (* the BUDGET half only: half this transaction's element is parked
       in the escrow's write arm for the whole locked window
       (durable-disk B''-tx); the release hands the whole one back *)
    log_opb icfg_log u -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 6) jj ↦ₘ[KT1] bnm jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bw jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 38) jj ↦ₘ[KT1] bo jj) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile),
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        proc_priv_bare (proc_addr jx) pidv Vpr -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
        bslots 3 -∗
        iref_slot -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKup HKeo HK38 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
           Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1
           HMs2 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              #Hitab #Hitinv #Hesck #Hireg #Hropen #Hslkk Hslkd Hdep Hidev
              Hiinum Hivalid Hload #Hshot Hfrz Hkeep Hru Hsbb Hsbi #Hbmres Hpid #Hprocs
              #Hdev #Hgeo #Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 HbN HbW HbO Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0xd6 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID0) (mword_of_int (SL + 0xd6)) Ra0 Rs1
              M (K - 38)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (slki_d6 with "Htext"). }
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
    assert (Hpp1 : add_vec_int (mword_of_int (SL + 0xd6) : mword 64) 2
                   = mword_of_int (SL + 0xd8)) by pcw.
    iEval (rewrite Hpp1) in "Hpc".
    (* ===== +0xd8 jal ra,iunlockput ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SL + 0xd8)) Rra
              (mword_of_int 2090252 : mword 21) M1 (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_d8 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0xd8) : mword 64) 4)]> M1).
    assert (Hjup : add_vec (mword_of_int (SL + 0xd8) : mword 64)
                     (sign_extend' 64 (mword_of_int 2090252 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0xd8) : mword 64) 4)
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
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID2 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID2 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (Iunlockput.wp_iunlockput_tx_sconf (CID := CID2) gs jx gl gu gd gk
              pd pav pu bn gil gisl bmapstart
 size kk qi s gy inum dn bm u pidv dq
              dqb dqs M2 (K - 38)%nat eb b lks
              Vpr HKup Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog
              Hinb Hcovb Hiu Hj Hgl HM2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hitab Hitinv
                    Hesck Hireg Hropen Hslkk Hslkd Hdep Hidev Hiinum Hivalid
                    Hload Hshot Hfrz [$Hkeep $Hru] Hsbb Hsbi Hbmres Hpid Hprocs Hdev Hgeo
                    Hdlk Hbsl Hop").
    iIntros (CID3 Hq3 mup n2)
      "%Hcsup Hcg Hown Htce Hcce Hpc Hpid Hsbb Hsbi Hbsl %Hn2
       Hop Hislot".
    assert (Hpc2 : ret_pc (M2 !!! Regidx Rra : mword 64)
                   = mword_of_int (SL + 0xdc)) by (rewrite HM2ra; pcw).
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
    (* ===== +0xdc jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID3) (mword_of_int (SL + 0xdc)) Rra
              (mword_of_int 2092458 : mword 21) mup (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_dc with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0xdc) : mword 64) 4)]> mup).
    assert (Hjeo : add_vec (mword_of_int (SL + 0xdc) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092458 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0xdc) : mword 64) 4)
      by (rewrite /M3; apply upd_eq).
    assert (HM3sp : sl_sp sp0 M3)
      by (rewrite /sl_sp /M3 upd_ne; [exact Hupsp | nz]).
    assert (HM3s2 : (M3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M3 upd_ne; [exact Hups2 | nz]).
    assert (HM3thr : sl_thr m M3).
    { intros c Hc N2 N8 N9 N18. rewrite /M3 upd_ne; [| regne].
      exact (Hupthr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID3 CID4 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID4) gs jx gl gu gd gk pd pav pu bn
              icfg_log fsc_fs fsc_cov fsc_logst icfg_dev n2 pidv dq M3 (K - 38)%nat eb b lks
              Vpr HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID5 Hq5 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpc3 : ret_pc (M3 !!! Regidx Rra : mword 64)
                   = mword_of_int (SL + 0xe0)) by (rewrite HM3ra; pcw).
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
    (* ===== +0xe0 c.li a5,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID5) (mword_of_int (SL + 0xe0)) Ra5
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 38)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (slki_e0 with "Htext"). }
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
    assert (Hpp4 : add_vec_int (mword_of_int (SL + 0xe0) : mword 64) 2
                   = mword_of_int (SL + 0xe2)) by pcw.
    iEval (rewrite Hpp4) in "Hpc".
    (* ===== +0xe2 c.ldsp s1,280(sp) ===== *)
    assert (Hd3 : add_vec (P1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 35 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP1sp; apply sl_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID6) (mword_of_int (SL + 0xe2))
              (mword_of_int 35 : mword 6) Rs1 P1 (K - 38)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf3]").
    { iApply (slki_e2 with "Htext"). }
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
    assert (Hpp5 : add_vec_int (mword_of_int (SL + 0xe2) : mword 64) 2
                   = mword_of_int (SL + 0xe4)) by pcw.
    iEval (rewrite Hpp5) in "Hpc".
    (* ===== +0xe4 c.j +0x11a ===== *)
    iApply (wp_cj_s_sconf (CID := CID7) (mword_of_int (SL + 0xe4))
              (sign_extend' 21 (concat_vec (mword_of_int 27 : mword 11) ('b"0")))
              P2 (K - 38)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_e4 with "Htext"). }
    iIntros (CID8 Hq8). iNext. iIntros "Hcg Hpc".
    assert (Htg : add_vec (mword_of_int (SL + 0xe4) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 27 : mword 11) ('b"0"))))
                  = mword_of_int (SL + 0x11a)) by pcw.
    iEval (rewrite Htg) in "Hpc".
    iDestruct (cpu_own_transport CID5 CID8 0 eb (proc_addr jx) b
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
                    [Hown Htce Hcce Hpid Hsbb Hsbi Hbsl Hislot Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha5f Hcg Hpc".
    iDestruct (cpu_own_transport CID8 CIDy 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID8 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID8 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf with "[%] [%] Hcg Hown Htce Hcce Hpc Hpid
              Hsbb Hsbi Hbsl Hislot").
    { exact Hcsf. }
    { rewrite Ha5f. exact HP2a5. }
  Qed.

  (* ================================================================== *)
  (*  THE [bad:] TAIL, +0xf4 .. +0x118 -- the ONLY arm that SPENDS the   *)
  (*  ledger fragment the [++] at +0x5e minted.                          *)
  (*                                                                     *)
  (*    +0xf4 c.mv a0,s1     ; +0xf6 jal ilock                            *)
  (*    +0xfa lhu a5,74(s1)  ; +0xfe c.addiw a5,-1 ; +0x100 sh a5,74(s1)   *)
  (*    +0x104 c.mv a0,s1     ; +0x106 jal iupdate                          *)
  (*    +0x10a c.mv a0,s1     ; +0x10c jal iunlockput                       *)
  (*    +0x110 jal end_op    ; +0x114 c.li a5,-1                          *)
  (*    +0x116 c.ldsp s1     ; +0x118 c.ldsp s2 ; fall into the epilogue  *)
  (*                                                                     *)
  (*  THREE THINGS ABOUT IT.                                             *)
  (*                                                                     *)
  (*  (1) THE RECORD IS A FRESH EXISTENTIAL AND THE TOKEN IS WHAT        *)
  (*  CROSSES.  +0x6c unlocked [ip] and this arm re-locks it, so the      *)
  (*  record the [lhu] reads is NOT the one the guard at +0x58 tested --  *)
  (*  another thread may hold the sleeplock in between.  The nonzero      *)
  (*  count [wp_iupdate_unlink]'s Z premise needs therefore cannot come   *)
  (*  from the walk; it comes from the FRAGMENT, by                       *)
  (*  [IregLinkNz.ireg_tok_nz].  That is the whole reason the token       *)
  (*  exists, exercised here for the first time.                          *)
  (*                                                                     *)
  (*  (2) THE RECEIPT GOES THROUGH THE LEFT DISJUNCT.  The nlink <> 0     *)
  (*  disjunct is UNSOUND here -- an unlinked-but-open file legitimately  *)
  (*  reaches nlink = 0 -- so the arm pays with the two AMBIENT TIES,     *)
  (*  which sys_link's contract already carries as premises.              *)
  (*                                                                     *)
  (*  (3) THE COUNTED [wp_iunlockput_sconf] IS ENOUGH, and that is        *)
  (*  [SysLinkBudget]'s finding, not an approximation: every route here   *)
  (*  leaves [iput_units] in hand once the CREDITED flush ([cru := true], *)
  (*  paid for by the [++]'s own log_write) has cost nothing.             *)
  (* ================================================================== *)
  Lemma sl_tail_bad `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (gil gisl : gname)
      (bmapstart : Z)
      (size : Z)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (ty : mword 16)
      (u : nat) (Sb : gset Z)
      (uty : ity)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (bnm bw bo : nat -> bv 8) (Vpr : pprivate) :
    (K_ilock <= K - 38)%nat -> (K_iupdate <= K - 38)%nat ->
    (K_iunlockput <= K - 38)%nat -> (K_end_op <= K - 38)%nat ->
    (38 <= K)%nat -> ((K - 38) + 38 = K)%nat ->
    (kk < NINODE)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ fsc_cov ->
    ~ (bmapstart ∈ log_region_set fsc_logst) ->
    0 <= icfg_ist ->
    IBLOCK inum icfg_ist ∈ fsc_cov ->
    ~ (IBLOCK inum icfg_ist ∈ log_region_set fsc_logst) ->
    bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
    cov_below fsc_cov size ->
    IBLOCK inum icfg_ist ∈ Sb ->
    (iput_units <= S u)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    eb = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    sl_sp sp0 M -> sl_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    sl_al sp0 ->
    (* THE TYPE THE CALLER SHOT, and the ONLY thing that gets the
       complement dot clause across this tail's own re-[ilock]: the record
       [ilock] hands back is an EXISTENTIAL, so nothing in the walk below
       can say it is not a directory.  [ity_shot_agree] against the shot the
       CALLER minted before its [iunlock] pins the type, and the generation
       is carriable because [SpecIunlock] returns the share gen-named. *)
    bv_unsigned ty <> T_DIR_z ->
    sie_cap_gpr KT1 M (K - 38) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SL + 0xf4)) -∗
    panic_env -∗
    bio_ctx bn (fs_view fsc_fs gd icfg_dev fsc_cov) -∗
    log_ctx icfg_log bn fsc_fs fsc_cov fsc_logst icfg_dev -∗
    fs_crash_seam fsc_cov fsc_logst -∗
    gen_cert -∗
    is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
    itable_inv -∗
    ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kk -∗
    ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
    ireg_open -∗
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok fsc_ic kk) (slh_tok (icfg_isl kk)) -∗
    (* THE REFERENCE, ALREADY SHED: the keep half is what iunlockput spends,
       the generation-named share is what this arm's own [ilock] consumes. *)
    inode_ref_short kk (qi + s)%Qp qi icfg_dev inum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned inum) -∗
    inode_shr_gen kk s icfg_dev inum gy -∗
    ity_shot gy ty -∗
    (* THE UNIT THE [--] SPENDS (durable-disk 2b-inode-5):
       the token the [ip->nlink++] minted and the failed [dirlink] never
       filed in a directory's [FsStateInode.ent_toks]. *)
    FsStateLink.link_tok (fs_gamma_L fsc_fs) (bv_unsigned inum) uty -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
    proc_priv_bare (proc_addr jx) pidv Vpr -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots 3 -∗
    log_opS icfg_log (S u) Sb -∗
    (* the transaction token beside the budget: this tail runs iupdate and
       then end_op, which takes the whole [log_op] (durable-disk lane A) *)
    log_tx icfg_log -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 6) jj ↦ₘ[KT1] bnm jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bw jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 38) jj ↦ₘ[KT1] bo jj) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile),
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        proc_priv_bare (proc_addr jx) pidv Vpr -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
        bslots 3 -∗
        iref_slot -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKil HKiup HKup HKeo HK38 Kpop Hkk Hgeom Hsize Hbm0
           Hbmcov Hbmlog Hist0 Hiblk Hiblog Hinb Hcovb Hmem Hiu Hj Hgl
           Hlkempty Heb Hsp0 HMsp HMthr HMs1 Hal Hncd.
    iIntros "Hcg Hown #Htext #Hdata Hpc #Hpe #Hbio #Hlog Hseam Hgen #Hitab #Hitinv
              #Hesck #Hireg #Hropen #Hslkk Hkeep Hru Hshr #Hshotc Htoken Hsbb Hsbi #Hbmres Hpid
              #Hprocs #Hdev #Hgeo #Hdlk Hbsl Hop Htx Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
              Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0xf4 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID0) (mword_of_int (SL + 0xf4)) Ra0 Rs1
              M (K - 38)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (slki_f4 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs1))]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = ientry kk).
    { etransitivity; [ rewrite /M1; apply upd_eq |].
      rewrite add_vec_zero_l. exact HMs1. }
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M1 upd_ne; [exact HMs1 | nz]).
    assert (HM1sp : sl_sp sp0 M1)
      by (rewrite /sl_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1thr : sl_thr m M1).
    { intros c Hc N2 N8 N9 N18. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18). }
    assert (Hpp1 : add_vec_int (mword_of_int (SL + 0xf4) : mword 64) 2
                   = mword_of_int (SL + 0xf6)) by pcw.
    iEval (rewrite Hpp1) in "Hpc".
    (* ===== +0xf6 jal ra,ilock ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SL + 0xf6)) Rra
              (mword_of_int 2089626 : mword 21) M1 (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_f6 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0xf6) : mword 64) 4)]> M1).
    assert (Hjil : add_vec (mword_of_int (SL + 0xf6) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089626 : mword 21))
                   = mword_of_int KernelSyms.ilock) by pcw.
    iEval (rewrite Hjil) in "Hpc".
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0xf6) : mword 64) 4)
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact HM1s1 | nz]).
    assert (HM2sp : sl_sp sp0 M2)
      by (rewrite /sl_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2thr : sl_thr m M2).
    { intros c Hc N2 N8 N9 N18. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (sl_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    (* ---- THE WRITE ARM (durable-fs-plan.md section 3, [ilock];
       durable-disk B''-tx): the bad tail re-locks the source inode to
       undo its nlink, and half the transaction's element sits in the
       escrow for that window. *)

    iApply (Ilock.wp_ilock_tx_sconf (CID := CID2) gs jx gl gu gd gk pd pav pu bn
              gil gisl kk s gy PlainK
 inum
              pidv dq dqs M2 (K - 38)%nat eb b lks
              Vpr HKil Hkk Hgeom Hist0 Hiblk Hinb Hj Hgl HM2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hitinv Hesck Hireg
                    Hslkk Hshr Hru Hsbi Hpid Hprocs Hdev Hgeo Hdlk Hbs1 Htx").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CID3 Hq3 mil dn bm fl)
      "%Hcsil Hcg Hown _ _ Hpc Hpid Hsbi Hbs1 Hslkd Hdep Hidev Hiinum
       Hivalid Hload #Hshot Hfrz %Hfl Hru %Hilkp".
    assert (Hpcfa : ret_pc (M2 !!! Regidx Rra : mword 64)
                    = mword_of_int (SL + 0xfa)) by (rewrite HM2ra; pcw).
    iEval (rewrite Hpcfa) in "Hpc".
    assert (Hilsp : sl_sp sp0 mil).
    { rewrite /sl_sp (callee_saved_lookup Hcsil csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM2sp. }
    assert (Hils1 : (mil !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite (callee_saved_lookup Hcsil Rs1 ltac:(vm_compute; reflexivity)).
      exact HM2s1. }
    assert (Hilthr : sl_thr m mil).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcsil c Hc).
      exact (HM2thr c Hc N2 N8 N9 N18). }
    iDestruct (ic_loaded_open with "Hload") as (dat)"(%Hiok & %Hrl_dat & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlnk & Hdiat & Hmeta & Haddrs & Hind & Hblocks & Hdview & Hfview)".
    iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
    iEval (rewrite /i_nlink) in "Hinl".
    (* THE TYPE, ACROSS THE CALLER'S OWN [iunlock].  [ilock] hands back a
       record this walk never chose, so the complement dot clause could not
       be discharged here at all until the share stopped being
       generation-erased: with the caller's [ity_shot] at the SAME [gy],
       [ity_shot_agree] pins [di_type dn] to the type the caller refused at
       its [+0x4a], and [dir_orphan_clean_not_dir] closes the re-park. *)
    iDestruct (ity_shot_agree gy ty (di_type dn) with "Hshotc Hshot")
      as %Htyshot.
    assert (Hnotdir : bv_unsigned (di_type dn) <> T_DIR_z)
      by (rewrite <- Htyshot; exact Hncd).
    (* THE COUNTING RA's OWN FACT: the token this arm is about to spend
       bounds the record's count below.  Nothing in the WALK can say it. *)
    iApply fupd_wp.
    iMod (ireg_tok_nz ⊤ fsc_ireg fsc_fs icfg_ist icfg_nib inum dn uty
            ltac:(solve_ndisj) Hinb
            with "Hireg Hdiat Htoken") as "([%Hnz %Htyok] & Hdiat & Htoken)".
    iModIntro.
    (* ===== +0xfa lhu a5,74(s1) ===== *)
    iApply (wp_lhu_s_sconf (CID := CID3) (kt := KT1) (ktd := KT0) (mword_of_int (SL + 0xfa)) Ra5 Rs1
              (mword_of_int 74 : mword 12) mil (K - 38)%nat
              (di_nlink dn : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hinl]").
    { iApply (slki_fa with "Htext"). }
    { iEval (rgne; rewrite Hils1). iExact "Hinl". }
    iIntros (CID4 Hq4) "Hcg Hpc Hinl".
    iEval (rgne; rewrite Hils1) in "Hinl".
    set (P1 := <[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (di_nlink dn : mword 16))]> mil).
    assert (HP1a5 : (P1 !!! Regidx Ra5 : mword 64)
                    = (zero_extend' 64 (di_nlink dn : mword 16) : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1s1 : (P1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /P1 upd_ne; [exact Hils1 | nz]).
    assert (HP1sp : sl_sp sp0 P1)
      by (rewrite /sl_sp /P1 upd_ne; [exact Hilsp | nz]).
    assert (HP1thr : sl_thr m P1).
    { intros c Hc N2 N8 N9 N18. rewrite /P1 upd_ne; [| regne].
      exact (Hilthr c Hc N2 N8 N9 N18). }
    assert (Hppfe : add_vec_int (mword_of_int (SL + 0xfa) : mword 64) 4
                    = mword_of_int (SL + 0xfe)) by pcw.
    iEval (rewrite Hppfe) in "Hpc".
    (* ===== +0xfe c.addiw a5,a5,-1 ===== *)
    iApply (wp_caddiw_s_sconf (CID := CID4) (mword_of_int (SL + 0xfe)) Ra5
              (mword_of_int 63 : mword 6) P1 (K - 38)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (slki_fe with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (P2 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (rget P1 Ra5)
                        (sign_extend' 64
                           (sign_extend' 12 (mword_of_int 63 : mword 6))))
                     31 0))]> P1).
    assert (HP2a5 : (P2 !!! Regidx Ra5 : mword 64)
                    = sign_extend' 64 (subrange_vec_dec
                        (add_vec (zero_extend' 64 (di_nlink dn : mword 16)
                                  : mword 64)
                           (sign_extend' 64
                              (sign_extend' 12 (mword_of_int 63 : mword 6))
                            : mword 64)) 31 0)).
    { rewrite /P2 upd_eq. rgne. rewrite HP1a5. reflexivity. }
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /P2 upd_ne; [exact HP1s1 | nz]).
    assert (HP2sp : sl_sp sp0 P2)
      by (rewrite /sl_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : sl_thr m P2).
    { intros c Hc N2 N8 N9 N18. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2 N8 N9 N18). }
    assert (Hpp100 : add_vec_int (mword_of_int (SL + 0xfe) : mword 64) 2
                    = mword_of_int (SL + 0x100)) by pcw.
    iEval (rewrite Hpp100) in "Hpc".
    (* ===== +0x100 sh a5,74(s1) ===== *)
    iApply (wp_sh_s_sconf (CID := CID5) (kt := KT1) (ktd := KT0) (mword_of_int (SL + 0x100)) Ra5 Rs1
              (mword_of_int 74 : mword 12) P2 (K - 38)%nat
              (di_nlink dn : mword 16) b with "Hcg Hpc [] [Hinl]").
    { iApply (slki_100 with "Htext"). }
    { iEval (rgne; rewrite HP2s1). iExact "Hinl". }
    iIntros (CID6 Hq6) "Hcg Hpc Hinl".
    iEval (rgne; rgne; rewrite HP2s1 HP2a5) in "Hinl".
    assert (Hfold : trunc16 (sign_extend' 64 (subrange_vec_dec
                      (add_vec (zero_extend' 64 (di_nlink dn : mword 16)
                                : mword 64)
                         (sign_extend' 64
                            (sign_extend' 12 (mword_of_int 63 : mword 6))
                          : mword 64)) 31 0))
                    = sl_ndec (di_nlink dn)) by reflexivity.
    iEval (rewrite Hfold) in "Hinl".
    set (dn' := sl_setnl dn (sl_ndec (di_nlink dn))).
    iAssert (inode_meta (ientry kk) dn')
      with "[Hity Himaj Himin Hinl Hisz]" as "Hmeta".
    { rewrite /inode_meta /dn' /sl_setnl /=. rewrite /i_nlink. iFrame. }
    iAssert (inode_map fsc_fs (ientry kk) bm) with "[Haddrs Hind]" as "Hmap".
    { rewrite /inode_map. iFrame. }
    assert (Hpp104 : add_vec_int (mword_of_int (SL + 0x100) : mword 64) 4
                    = mword_of_int (SL + 0x104)) by pcw.
    iEval (rewrite Hpp104) in "Hpc".
    (* ===== +0x104 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID6) (mword_of_int (SL + 0x104)) Ra0 Rs1
              P2 (K - 38)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (slki_104 with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (P3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (P2 !!! Regidx Rs1))]> P2).
    assert (HP3a0 : (P3 !!! Regidx Ra0 : mword 64) = ientry kk).
    { etransitivity; [ rewrite /P3; apply upd_eq |].
      rewrite add_vec_zero_l. exact HP2s1. }
    assert (HP3s1 : (P3 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /P3 upd_ne; [exact HP2s1 | nz]).
    assert (HP3sp : sl_sp sp0 P3)
      by (rewrite /sl_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (HP3thr : sl_thr m P3).
    { intros c Hc N2 N8 N9 N18. rewrite /P3 upd_ne; [| regne].
      exact (HP2thr c Hc N2 N8 N9 N18). }
    assert (Hpp106 : add_vec_int (mword_of_int (SL + 0x104) : mword 64) 2
                    = mword_of_int (SL + 0x106)) by pcw.
    iEval (rewrite Hpp106) in "Hpc".
    (* ===== +0x106 jal ra,iupdate ===== *)
    iApply (wp_jal_s_sconf (CID := CID7) (mword_of_int (SL + 0x106)) Rra
              (mword_of_int 2089430 : mword 21) P3 (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_106 with "Htext"). }
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (P4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0x106) : mword 64) 4)]> P3).
    assert (Hjiu : add_vec (mword_of_int (SL + 0x106) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089430 : mword 21))
                   = mword_of_int KernelSyms.iupdate) by pcw.
    iEval (rewrite Hjiu) in "Hpc".
    assert (HP4ra : (P4 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0x106) : mword 64) 4)
      by (rewrite /P4; apply upd_eq).
    assert (HP4a0 : (P4 !!! Regidx Ra0 : mword 64) = ientry kk)
      by (rewrite /P4 upd_ne; [exact HP3a0 | nz]).
    assert (HP4s1 : (P4 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /P4 upd_ne; [exact HP3s1 | nz]).
    assert (HP4sp : sl_sp sp0 P4)
      by (rewrite /sl_sp /P4 upd_ne; [exact HP3sp | nz]).
    assert (HP4thr : sl_thr m P4).
    { intros c Hc N2 N8 N9 N18. rewrite /P4 upd_ne; [| regne].
      exact (HP3thr c Hc N2 N8 N9 N18). }
    (* the four pure facts the flush takes, all off [inode_ok] *)
    assert (Htynz : bv_unsigned (di_type dn') <> 0).
    { rewrite /dn' sl_setnl_type.
      exact (proj1 (proj2 (proj2 (proj2 Hiok)))). }
    assert (Hdec : bv_unsigned (di_nlink dn)
                   = (bv_unsigned (di_nlink dn') + 1)%Z).
    { rewrite /dn' sl_setnl_nlink. exact (sl_ndec_decr (di_nlink dn) Hnz). }
    assert (Haddreq : di_addrs dn' = bm_cells bm).
    { rewrite /dn' sl_setnl_addrs. exact (proj1 (proj2 (proj2 Hiok))). }
    assert (Hdirlen : length (bm_dir bm) = NDIRECT)
      by exact (blkmap_wf_dir_len fsc_cov fsc_logst bm (proj1 Hiok)).
    iDestruct (cpu_own_transport CID3 CID8 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Iupdate.wp_iupdate_unlink (CID := CID8) gs jx gl gu gd gk pd pav pu
              bn (ientry kk) inum
              dn' dn bm u Sb true uty pidv dq (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
              P4 (K - 38)%nat eb b lks
              Vpr HKiup ltac:(intros _; exact Hmem) Hgeom Hist0 Hiblk Hiblog Hinb
              ltac:(exact (sl_setnl_type_stable dn (sl_ndec (di_nlink dn))))
              Htynz Hdec
              Haddreq Hdirlen Hj Hgl HP4a0 Heb
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htext Hdata Hpc Hpe Hbio Hlog Hidev Hiinum Hmeta Hmap
                    Hsbi Hireg Hdiat [Htoken] Hpid Hprocs Hdev Hgeo Hdlk Hbs2
                    Hop").
    { assert (Hdn'ty : bv_unsigned (di_type dn') <> T_DIR_z)
        by (rewrite /dn' sl_setnl_type; exact Hnotdir).
      rewrite (InodeRegion.ireg_dot_delta_not_dir _ _ Hdn'ty)
        FsStateLink.link_reps_1. iExact "Htoken". }
    iIntros (CID9 Hq9 miu)
      "%Hcsiu Hcg Hown Hpc Hpid Hidev Hiinum Hmeta Hmap Hsbi Hdiat Hbs2 Hop".
    assert (Hpc10a : ret_pc (P4 !!! Regidx Rra : mword 64)
                    = mword_of_int (SL + 0x10a)) by (rewrite HP4ra; pcw).
    iEval (rewrite Hpc10a) in "Hpc".
    assert (Hiusp : sl_sp sp0 miu).
    { rewrite /sl_sp (callee_saved_lookup Hcsiu csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HP4sp. }
    assert (Hius1 : (miu !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite (callee_saved_lookup Hcsiu Rs1 ltac:(vm_compute; reflexivity)).
      exact HP4s1. }
    assert (Hiuthr : sl_thr m miu).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcsiu c Hc).
      exact (HP4thr c Hc N2 N8 N9 N18). }
    (* THE PAYLOAD, RE-PARKED AT THE LOWERED RECORD.  Everything pure rides
       ([sl_setnl] moves one halfword), and the [dlinks] conjunct is free at
       a NON-directory: it owns no records, so it holds no fragment at all
       ([IcacheEscrow.dlinks_not_dir]). *)
    iClear "Hdlnk".
    iAssert (dlinks fsc_fs (bv_unsigned inum) dn' bm dat) as "Hdlnk".
    { iApply (dlinks_not_dir fsc_fs (bv_unsigned inum) dn' bm dat).
      rewrite /dn' sl_setnl_type. exact Hnotdir. }
    iAssert (ity_shot gy (di_type dn')) as "#Hshot'".
    { rewrite /dn' sl_setnl_type. iExact "Hshot". }
    (* [dn'] is [sl_setnl dn ..]: one halfword of the record, no byte, and
       [dv_of] reads only [di_size] -- so the contents value is unmoved
       (§9 W3, [dv_of_size]). *)
    iEval (rewrite (dv_of_size dn dn' dat (eq_sym (sl_setnl_size dn _))))
      in "Hdview".
    iEval (rewrite (fv_of_size dn dn' dat (eq_sym (sl_setnl_size dn _))))
      in "Hfview".
    (* THE ERA'S ABSTRACT VALUE IS RETAGGED (durable-disk 2b-inode-3): the
       payload's last name carries [fv_ride * top_frag], the flush MOVED
       the record, and [InodeRegion.ireg_top_retag] is the one-line move.
       It opens [ftopN] alone, so no mask this walk holds is disturbed. *)
    iDestruct "Hfview" as "[Hfview Htop]".
    (* THE RETAG OWES THE ROW (durable-disk lane A): the raised record is
       well-formed, and these are the four facts the re-pack below proves
       anyway -- a link count is the one column [sl_setnl] moves. *)
    assert (Hloc' : inode_local (bv_unsigned inum) (era_node dn' bm dat)).
    { apply (inode_local_of_ok_rec (bv_unsigned inum) fsc_cov fsc_logst dn' bm dat).
      - exact (sl_setnl_inode_ok fsc_cov fsc_logst dn bm dat _ Hiok).
      - apply (inode_rec_local_same_type dn dn' Hrl_dat
                 (sl_setnl_type dn _));
          [ pose proof (proj1 (proj2 Hrl_dat)); lia
          | intros Hd; exfalso; apply Hnotdir;
            rewrite /dn' sl_setnl_type in Hd; exact Hd ].
      - apply dir_uniq_not_dir. rewrite /dn' sl_setnl_type. exact Hnotdir.
      - exact (sl_setnl_ddix _ dn dat _ Hnz Hddix). }
    iApply fupd_wp.
    iMod (ireg_top_retag ⊤ fsc_fs (bv_unsigned inum)
            (era_node dn bm dat) (era_node dn' bm dat)
            ltac:(solve_ndisj) Hloc' with "[] Htop") as "Htop";
      [iApply (ireg_inv_ftop with "Hireg") |].
    iModIntro.
    iAssert (ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kk inum dn' bm)
      with "[Hdlnk Hdiat Hmeta Hmap Hblocks Hdview Hfview Htop]" as "Hload".
    { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body. iExists dat.
      iSplitR; [iPureIntro; exact (sl_setnl_inode_ok fsc_cov fsc_logst dn bm dat _ Hiok) |].
      (* [sl_setnl] moves the COUNT and nothing else, so the type and the
         size ride, the new count is BELOW one the region already bounded
         ([Hdec]) and the directory clause is vacuous at a non-directory
         (durable-disk 2b-inode-3). *)
      iSplitR; [iPureIntro;
                apply (inode_rec_local_same_type dn dn' Hrl_dat
                         (sl_setnl_type dn _));
                [ pose proof (proj1 (proj2 Hrl_dat)); lia
                | intros Hd; exfalso; apply Hnotdir;
                  rewrite /dn' sl_setnl_type in Hd; exact Hd ] |].
      iSplitR; [iPureIntro; exact (sl_setnl_dir_ok icfg_nib dn dat _ Hdok) |].
      iSplitR; [iPureIntro; exact (sl_setnl_ddix _ dn dat _ Hnz Hddix) |].
      iSplitR; [iPureIntro; apply dir_orphan_clean_not_dir;
                rewrite /dn' sl_setnl_type; exact Hnotdir |].
      iSplitR; [iPureIntro; apply dir_uniq_not_dir;
                rewrite /dn' sl_setnl_type; exact Hnotdir |].
      iSplitL "Hdlnk"; [iExact "Hdlnk" |].
      iFrame "Hdiat Hmeta". rewrite /inode_map.
      iDestruct "Hmap" as "[Ha Hi]".
      iFrame "Ha Hi Hblocks Hdview Hfview Htop". }
    iDestruct (sl_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
      [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
    (* ===== +0x10a c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID9) (mword_of_int (SL + 0x10a)) Ra0 Rs1
              miu (K - 38)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (slki_10a with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (Q1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (miu !!! Regidx Rs1))]> miu).
    assert (HQ1a0 : (Q1 !!! Regidx Ra0 : mword 64) = ientry kk).
    { etransitivity; [ rewrite /Q1; apply upd_eq |].
      rewrite add_vec_zero_l. exact Hius1. }
    assert (HQ1sp : sl_sp sp0 Q1)
      by (rewrite /sl_sp /Q1 upd_ne; [exact Hiusp | nz]).
    assert (HQ1thr : sl_thr m Q1).
    { intros c Hc N2 N8 N9 N18. rewrite /Q1 upd_ne; [| regne].
      exact (Hiuthr c Hc N2 N8 N9 N18). }
    assert (Hpp10c : add_vec_int (mword_of_int (SL + 0x10a) : mword 64) 2
                    = mword_of_int (SL + 0x10c)) by pcw.
    iEval (rewrite Hpp10c) in "Hpc".
    (* ===== +0x10c jal ra,iunlockput ===== *)
    iApply (wp_jal_s_sconf (CID := CID10) (mword_of_int (SL + 0x10c)) Rra
              (mword_of_int 2090200 : mword 21) Q1 (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_10c with "Htext"). }
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (Q2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0x10c) : mword 64) 4)]> Q1).
    assert (Hjup : add_vec (mword_of_int (SL + 0x10c) : mword 64)
                     (sign_extend' 64 (mword_of_int 2090200 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HQ2ra : (Q2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0x10c) : mword 64) 4)
      by (rewrite /Q2; apply upd_eq).
    assert (HQ2a0 : (Q2 !!! Regidx Ra0 : mword 64) = ientry kk)
      by (rewrite /Q2 upd_ne; [exact HQ1a0 | nz]).
    assert (HQ2sp : sl_sp sp0 Q2)
      by (rewrite /sl_sp /Q2 upd_ne; [exact HQ1sp | nz]).
    assert (HQ2thr : sl_thr m Q2).
    { intros c Hc N2 N8 N9 N18. rewrite /Q2 upd_ne; [| regne].
      exact (HQ1thr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID9 CID11 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Iunlockput.wp_iunlockput_tx_sconf (CID := CID11) gs jx gl gu gd gk
              pd pav pu bn gil gisl bmapstart
 size kk qi s gy inum dn' bm (S u) pidv dq
              dqb dqs Q2 (K - 38)%nat eb b lks
              Vpr HKup Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog
              Hinb Hcovb Hiu Hj Hgl HQ2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hitab Hitinv
                    Hesck Hireg Hropen Hslkk Hslkd Hdep Hidev Hiinum Hivalid
                    Hload Hshot' Hfrz [$Hkeep $Hru] Hsbb Hsbi Hbmres Hpid Hprocs Hdev Hgeo
                    Hdlk Hbsl [Hop]").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iApply (log_opS_opb with "Hop"). }
    iIntros (CID12 Hq12 mup n2)
      "%Hcsup Hcg Hown _ _ Hpc Hpid Hsbb Hsbi Hbsl %Hn2
       Hop Hislot".
    assert (Hpc110 : ret_pc (Q2 !!! Regidx Rra : mword 64)
                     = mword_of_int (SL + 0x110)) by (rewrite HQ2ra; pcw).
    iEval (rewrite Hpc110) in "Hpc".
    assert (Hupsp : sl_sp sp0 mup).
    { rewrite /sl_sp (callee_saved_lookup Hcsup csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HQ2sp. }
    assert (Hupthr : sl_thr m mup).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcsup c Hc).
      exact (HQ2thr c Hc N2 N8 N9 N18). }
    (* ===== +0x110 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID12) (mword_of_int (SL + 0x110)) Rra
              (mword_of_int 2092406 : mword 21) mup (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_110 with "Htext"). }
    iIntros (CID13 Hq13) "Hcg Hpc".
    set (Q3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0x110) : mword 64) 4)]> mup).
    assert (Hjeo : add_vec (mword_of_int (SL + 0x110) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092406 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HQ3ra : (Q3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0x110) : mword 64) 4)
      by (rewrite /Q3; apply upd_eq).
    assert (HQ3sp : sl_sp sp0 Q3)
      by (rewrite /sl_sp /Q3 upd_ne; [exact Hupsp | nz]).
    assert (HQ3thr : sl_thr m Q3).
    { intros c Hc N2 N8 N9 N18. rewrite /Q3 upd_ne; [| regne].
      exact (Hupthr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID12 CID13 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (EndOp.wp_end_op_sconf (CID := CID13) gs jx gl gu gd gk pd pav pu bn
              icfg_log fsc_fs fsc_cov fsc_logst icfg_dev n2 pidv dq Q3 (K - 38)%nat eb b lks
              Vpr HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CID14 Hq14 meo) "%Hcseo Hcg Hown _ _ Hpc Hpid".
    assert (Hpc114 : ret_pc (Q3 !!! Regidx Rra : mword 64)
                     = mword_of_int (SL + 0x114)) by (rewrite HQ3ra; pcw).
    iEval (rewrite Hpc114) in "Hpc".
    assert (Heosp : sl_sp sp0 meo).
    { rewrite /sl_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HQ3sp. }
    assert (Heothr : sl_thr m meo).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HQ3thr c Hc N2 N8 N9 N18). }
    (* ===== +0x114 c.li a5,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID14) (mword_of_int (SL + 0x114)) Ra5
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 38)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (slki_114 with "Htext"). }
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (R1 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> meo).
    assert (HR1a5 : (R1 !!! Regidx Ra5 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /R1; apply upd_eq).
    assert (HR1sp : sl_sp sp0 R1)
      by (rewrite /sl_sp /R1 upd_ne; [exact Heosp | nz]).
    assert (HR1thr : sl_thr m R1).
    { intros c Hc N2 N8 N9 N18. rewrite /R1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8 N9 N18). }
    assert (Hpp116 : add_vec_int (mword_of_int (SL + 0x114) : mword 64) 2
                     = mword_of_int (SL + 0x116)) by pcw.
    iEval (rewrite Hpp116) in "Hpc".
    (* ===== +0x116 c.ldsp s1,280(sp) ===== *)
    assert (Hd3 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 35 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HR1sp; apply sl_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID15) (mword_of_int (SL + 0x116))
              (mword_of_int 35 : mword 6) Rs1 R1 (K - 38)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf3]").
    { iApply (slki_116 with "Htext"). }
    { iEval (rewrite Hd3). iExact "Hf3". }
    iIntros (CID16 Hq16) "Hcg Hpc Hf3".
    iEval (rewrite Hd3) in "Hf3".
    set (R2 := <[Regidx Rs1 := regval_into_reg
                  (m !!! Regidx Rs1 : mword 64)]> R1).
    assert (HR2s1 : (R2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R2; apply upd_eq).
    assert (HR2a5 : (R2 !!! Regidx Ra5 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /R2 upd_ne; [exact HR1a5 | nz]).
    assert (HR2sp : sl_sp sp0 R2)
      by (rewrite /sl_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2thr : sl_thr m R2).
    { intros c Hc N2 N8 N9 N18. rewrite /R2 upd_ne; [| regne].
      exact (HR1thr c Hc N2 N8 N9 N18). }
    assert (Hpp118 : add_vec_int (mword_of_int (SL + 0x116) : mword 64) 2
                     = mword_of_int (SL + 0x118)) by pcw.
    iEval (rewrite Hpp118) in "Hpc".
    (* ===== +0x118 c.ldsp s2,272(sp) ===== *)
    assert (Hd4 : add_vec (R2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 34 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HR2sp; apply sl_frm4).
    iApply (wp_cldsp_s_sconf (CID := CID16) (mword_of_int (SL + 0x118))
              (mword_of_int 34 : mword 6) Rs2 R2 (K - 38)%nat
              (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf4]").
    { iApply (slki_118 with "Htext"). }
    { iEval (rewrite Hd4). iExact "Hf4". }
    iIntros (CID17 Hq17) "Hcg Hpc Hf4".
    iEval (rewrite Hd4) in "Hf4".
    set (R3 := <[Regidx Rs2 := regval_into_reg
                  (m !!! Regidx Rs2 : mword 64)]> R2).
    assert (HR3s2 : (R3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /R3; apply upd_eq).
    assert (HR3s1 : (R3 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2s1 | nz]).
    assert (HR3a5 : (R3 !!! Regidx Ra5 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2a5 | nz]).
    assert (HR3sp : sl_sp sp0 R3)
      by (rewrite /sl_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : sl_thr m R3).
    { intros c Hc N2 N8 N9 N18. rewrite /R3 upd_ne; [| regne].
      exact (HR2thr c Hc N2 N8 N9 N18). }
    assert (Hpp11a : add_vec_int (mword_of_int (SL + 0x118) : mword 64) 2
                     = mword_of_int (SL + 0x11a)) by pcw.
    iEval (rewrite Hpp11a) in "Hpc".
    (* ===== the epilogue, entered by FALLING THROUGH ===== *)
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID17)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (sl_epilogue (CID0 := CID17) m R3 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) (m !!! Regidx Rs2 : mword 64)
              bnm bw bo
              HK38 Kpop Hsp0 HR3sp HR3thr HR3s1 HR3s2 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
                    [Hown Hpid Hsbb Hsbi Hbsl Hislot Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha5f Hcg Hpc".
    iDestruct (cpu_own_transport CID14 CIDy 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf with "[%] [%] Hcg Hown [] [] Hpc Hpid
              Hsbb Hsbi Hbsl Hislot").
    { exact Hcsf. }
    { rewrite Ha5f. exact HR3a5. }
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
  Qed.

  (* ================================================================== *)
  (*  ARM F's ENTRY: +0xee c.mv a0,s2 ; +0xf0 jal iunlockput, then FALL   *)
  (*  THROUGH into [bad:].  Both dirlink failures and the (refuted)       *)
  (*  cross-device branch land here.                                      *)
  (*                                                                     *)
  (*  THIS iunlockput IS THE CREDITED ONE and the one in the tail is not, *)
  (*  which is not an inconsistency but the ledger's shape: the parent's  *)
  (*  free may absorb the bitmap block and the directory's own inode      *)
  (*  block, and whether it does is exactly what decides whether the      *)
  (*  tail's own three units are still there.  So the arm carries the     *)
  (*  claim booleans and the CLOSURE as a premise over the two figures    *)
  (*  the call reports -- which is [SysLinkBudget]'s theorems, verbatim,  *)
  (*  and nothing this lemma has to know.                                 *)
  (* ================================================================== *)
  Lemma sl_tail_f `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (gil gisl : gname) (gild gisld : gname)
      (bmapstart : Z)
      (size : Z)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (ty : mword 16)
      (kd : nat) (qd sd : Qp) (gyd : gname) (dinum : mword 32)
      (dnd : dinode) (bmd : blkmap)
      (n : nat) (Sb : gset Z) (crb cru : bool) (e0 : nat)
      (uty : ity)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (bnm bw bo : nat -> bv 8) (Vpr : pprivate) :
    (K_ilock <= K - 38)%nat -> (K_iupdate <= K - 38)%nat ->
    (K_iunlockput <= K - 38)%nat -> (K_end_op <= K - 38)%nat ->
    (38 <= K)%nat -> ((K - 38) + 38 = K)%nat ->
    (kk < NINODE)%nat -> (kd < NINODE)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ fsc_cov ->
    ~ (bmapstart ∈ log_region_set fsc_logst) ->
    0 <= icfg_ist ->
    IBLOCK inum icfg_ist ∈ fsc_cov ->
    ~ (IBLOCK inum icfg_ist ∈ log_region_set fsc_logst) ->
    bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
    IBLOCK dinum icfg_ist ∈ fsc_cov ->
    ~ (IBLOCK dinum icfg_ist ∈ log_region_set fsc_logst) ->
    bv_unsigned dinum < 16 * Z.of_nat icfg_nib ->
    cov_below fsc_cov size ->
    (crb = true -> bmapstart ∈ Sb) ->
    (cru = true -> IBLOCK dinum icfg_ist ∈ Sb) ->
    IBLOCK inum icfg_ist ∈ Sb ->
    (iput_units <= n)%nat ->
    (* THE LEDGER'S CLOSURE, over the two figures the parent's free
       REPORTS.  [SysLinkBudget]'s three arm theorems are exactly this. *)
    (forall (w : bool) (n' : nat),
       (crb = true -> w = false) ->
       ((n - ip_spend_w w cru false)%nat <= n')%nat ->
       (iput_units <= n')%nat) ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    eb = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    sl_sp sp0 M -> sl_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs2 : mword 64) = ientry kd ->
    sl_al sp0 ->
    (* THE TYPE THE CALLER SHOT, and the ONLY thing that gets the
       complement dot clause across this tail's own re-[ilock]: the record
       [ilock] hands back is an EXISTENTIAL, so nothing in the walk below
       can say it is not a directory.  [ity_shot_agree] against the shot the
       CALLER minted before its [iunlock] pins the type, and the generation
       is carriable because [SpecIunlock] returns the share gen-named. *)
    bv_unsigned ty <> T_DIR_z ->
    sie_cap_gpr KT1 M (K - 38) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SL + 0xee)) -∗
    panic_env -∗
    bio_ctx bn (fs_view fsc_fs gd icfg_dev fsc_cov) -∗
    log_ctx icfg_log bn fsc_fs fsc_cov fsc_logst icfg_dev -∗
    fs_crash_seam fsc_cov fsc_logst -∗
    gen_cert -∗
    is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
    itable_inv -∗
    ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kk -∗
    ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kd -∗
    ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
    ireg_open -∗
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok fsc_ic kk) (slh_tok (icfg_isl kk)) -∗
    is_sleeplock_gen gild gisld (i_lock (ientry kd)) "inode"%string (ic_tok fsc_ic kd) (slh_tok (icfg_isl kd)) -∗
    (* ---- the CHILD, unlocked, its reference already shed ---- *)
    inode_ref_short kk (qi + s)%Qp qi icfg_dev inum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned inum) -∗
    inode_shr_gen kk s icfg_dev inum gy -∗
    ity_shot gy ty -∗
    (* THE UNIT THE [--] SPENDS (durable-disk 2b-inode-5):
       the token the [ip->nlink++] minted and the failed [dirlink] never
       filed in a directory's [FsStateInode.ent_toks]. *)
    FsStateLink.link_tok (fs_gamma_L fsc_fs) (bv_unsigned inum) uty -∗
    (* ---- the PARENT, still locked ---- *)
    sleeplocked_q gisld sd (i_lock (ientry kd)) pidv -∗
    ic_tx_dep fsc_ic kd sd icfg_dev dinum gyd -∗
    i_dev (ientry kd) ↦₄{DfracOwn (1/2)} icfg_dev -∗
    i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dinum -∗
    i_valid (ientry kd) ↦₄ valid_word true -∗
    ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kd dinum dnd bmd -∗
    ity_shot gyd (di_type dnd) -∗
    (* ...and the parent payload's freeze token (§3.9, RULING A-prime) *)
    ifreeze_off (bv_unsigned dinum) -∗
    inode_ref_short kd (qd + sd)%Qp qd icfg_dev dinum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned dinum) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
    proc_priv_bare (proc_addr jx) pidv Vpr -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots 3 -∗
    log_opSe icfg_log n Sb e0 -∗
    (* the transaction token is INSIDE the checked-out descriptor while
       the lock is held (durable-disk B''-tx): the release below hands
       it back, and [sl_tail_bad] takes it from there. *)
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 6) jj ↦ₘ[KT1] bnm jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bw jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 38) jj ↦ₘ[KT1] bo jj) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile),
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        proc_priv_bare (proc_addr jx) pidv Vpr -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
        bslots 3 -∗
        iref_slots 2 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKil HKiup HKup HKeo HK38 Kpop Hkk Hkd Hgeom Hsize Hbm0
           Hbmcov Hbmlog Hist0 Hiblk Hiblog Hinb Hdblk Hdblog Hdnb Hcovb
           Hcrb Hcru Hmem Hiu Hclose Hj Hgl Hlkempty Heb Hsp0 HMsp HMthr
           HMs1 HMs2 Hal Hncd.
    iIntros "Hcg Hown #Htext #Hdata Hpc #Hpe #Hbio #Hlog Hseam Hgen #Hitab #Hitinv
              #Hesck #Hescd #Hireg #Hropen #Hslkk #Hslkd0 Hkeep Hru Hshr #Hshotc Htoken Hslkd
              Hdep Hidev Hiinum Hivalid Hload #Hshotd Hfrz Hkeepd Hrud Hsbb Hsbi
              #Hbmres Hpid #Hprocs #Hdev #Hgeo #Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4
              HbN HbW HbO Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0xee c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID0) (mword_of_int (SL + 0xee)) Ra0 Rs2
              M (K - 38)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (slki_ee with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs2))]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = ientry kd).
    { etransitivity; [ rewrite /M1; apply upd_eq |].
      rewrite add_vec_zero_l. exact HMs2. }
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M1 upd_ne; [exact HMs1 | nz]).
    assert (HM1sp : sl_sp sp0 M1)
      by (rewrite /sl_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1thr : sl_thr m M1).
    { intros c Hc N2 N8 N9 N18. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18). }
    assert (Hpp1 : add_vec_int (mword_of_int (SL + 0xee) : mword 64) 2
                   = mword_of_int (SL + 0xf0)) by pcw.
    iEval (rewrite Hpp1) in "Hpc".
    (* ===== +0xf0 jal ra,iunlockput ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SL + 0xf0)) Rra
              (mword_of_int 2090228 : mword 21) M1 (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_f0 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0xf0) : mword 64) 4)]> M1).
    assert (Hjup : add_vec (mword_of_int (SL + 0xf0) : mword 64)
                     (sign_extend' 64 (mword_of_int 2090228 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0xf0) : mword 64) 4)
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = ientry kd)
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact HM1s1 | nz]).
    assert (HM2sp : sl_sp sp0 M2)
      by (rewrite /sl_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2thr : sl_thr m M2).
    { intros c Hc N2 N8 N9 N18. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Iunlockput.wp_iunlockput_tx_gen (CID := CID2) gs jx gl gu gd gk
              pd pav pu bn gild gisld bmapstart
 size kd qd sd gyd dinum dnd bmd
              n Sb crb cru false e0 pidv dq dqb dqs
              M2 (K - 38)%nat eb b lks
              Vpr HKup Hkd Hcrb Hcru Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
              Hdblk Hdblog Hdnb Hcovb Hiu Hj Hgl HM2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hitab Hitinv
                    Hescd Hireg Hropen Hslkd0 Hslkd Hdep Hidev Hiinum Hivalid
                    Hload Hshotd Hfrz [$Hkeepd $Hrud] Hsbb Hsbi Hbmres Hpid Hprocs Hdev Hgeo
                    Hdlk Hbsl [] Hop").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { done. }
    iIntros (CID3 Hq3 mup n1 Sb1 w)
      "%Hcsup Hcg Hown _ _ Hpc Hpid Hsbb Hsbi Hbsl %Hsb1 %Hwm
       %Hcrbw %Hn1 Hop Htx Hislot".
    assert (Hpcf4 : ret_pc (M2 !!! Regidx Rra : mword 64)
                    = mword_of_int (SL + 0xf4)) by (rewrite HM2ra; pcw).
    iEval (rewrite Hpcf4) in "Hpc".
    assert (Hupsp : sl_sp sp0 mup).
    { rewrite /sl_sp (callee_saved_lookup Hcsup csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM2sp. }
    assert (Hups1 : (mup !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite (callee_saved_lookup Hcsup Rs1 ltac:(vm_compute; reflexivity)).
      exact HM2s1. }
    assert (Hupthr : sl_thr m mup).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcsup c Hc).
      exact (HM2thr c Hc N2 N8 N9 N18). }
    (* the ledger CLOSES, and the count is therefore a successor *)
    assert (Hiu1 : (iput_units <= n1)%nat)
      by exact (Hclose w n1 Hcrbw (proj1 Hn1)).
    destruct n1 as [| u1]; [exfalso; unfold iput_units in Hiu1; lia |].
    assert (Hmem1 : IBLOCK inum icfg_ist ∈ Sb1) by exact (Hsb1 _ Hmem).
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID3)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (sl_tail_bad (CID0 := CID3) gs jx gl gu gd gk pd pav pu bn
              gil gisl bmapstart size
              kk qi s gy inum ty u1 Sb1 uty pidv dq dqb dqs m mup sp0 K eb b
              lks bnm bw bo
              Vpr HKil HKiup HKup HKeo HK38 Kpop Hkk Hgeom Hsize Hbm0
              Hbmcov Hbmlog Hist0 Hiblk Hiblog Hinb Hcovb Hmem1 Hiu1 Hj Hgl
              Hlkempty Heb Hsp0 Hupsp Hupthr Hups1 Hal Hncd
              with "Hcg Hown Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen Hitab Hitinv
                    Hesck Hireg Hropen Hslkk Hkeep Hru Hshr Hshotc Htoken Hsbb Hsbi Hbmres Hpid
                    Hprocs Hdev Hgeo Hdlk Hbsl Hop Htx Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
                    [Hislot Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf)
      "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpid Hsbb Hsbi Hbsl
       Hislot2".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iDestruct (iref_slots_combine 1 1 with "Hislot Hislot2") as "Hislots".
    iApply ("Hcont" $! mf with "[%] [%] Hcg Hown Htce Hcce Hpc Hpid
              Hsbb Hsbi Hbsl Hislots").
    { exact Hcsf. }
    { exact Ha0f. }
  Qed.

  (* ================================================================== *)
  (*  ARM E2's ENTRY -- THE ORPHAN GUARD'S OWN ROUTE TO [bad:] (f60ff58): *)
  (*  +0xe6 c.mv a0,s2 ; +0xe8 jal iunlockput ; +0xec c.j [bad:].         *)
  (*                                                                     *)
  (*  It is ARM F's block one block earlier, plus the [c.j] ARM F does    *)
  (*  not need, and it is a SEPARATE LEMMA for the reason ARMs C and D    *)
  (*  are: every decode fact and every [pc_is] equation here is           *)
  (*  per-address, so sharing would mean five [instr]s and four pc        *)
  (*  equations as premises.                                             *)
  (*                                                                     *)
  (*  WHAT IT IS CHEAPER THAN ARM F BY is the whole credit apparatus.     *)
  (*  ARM F runs AFTER the dirlink, so the parent's free may absorb a     *)
  (*  bitmap block or the directory's own inode block and the arm has to  *)
  (*  carry both claim booleans.  This one runs BEFORE it -- nothing has  *)
  (*  been logged since nameiparent -- so both are [false] outright and   *)
  (*  the closure premise loses its credit hypothesis.                    *)
  (*                                                                     *)
  (*  WHAT IT IS NOT is a route that reaches [bad:] with no token to      *)
  (*  spend.  The [ip->nlink++] is at +0x5e, well ABOVE nameiparent, so   *)
  (*  the fragment is live on this arm exactly as on E and F and the      *)
  (*  tail's [ip->nlink--] consumes it back.  (Read the disassembly, not  *)
  (*  the C's reading order: the guard is after the mint, not before.)    *)
  (* ================================================================== *)
  Lemma sl_tail_e2 `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (gil gisl : gname) (gild gisld : gname)
      (bmapstart : Z)
      (size : Z)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (ty : mword 16)
      (kd : nat) (qd sd : Qp) (gyd : gname) (dinum : mword 32)
      (dnd : dinode) (bmd : blkmap)
      (n : nat) (Sb : gset Z) (e0 : nat)
      (uty : ity)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (bnm bw bo : nat -> bv 8) (Vpr : pprivate) :
    (K_ilock <= K - 38)%nat -> (K_iupdate <= K - 38)%nat ->
    (K_iunlockput <= K - 38)%nat -> (K_end_op <= K - 38)%nat ->
    (38 <= K)%nat -> ((K - 38) + 38 = K)%nat ->
    (kk < NINODE)%nat -> (kd < NINODE)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ fsc_cov ->
    ~ (bmapstart ∈ log_region_set fsc_logst) ->
    0 <= icfg_ist ->
    IBLOCK inum icfg_ist ∈ fsc_cov ->
    ~ (IBLOCK inum icfg_ist ∈ log_region_set fsc_logst) ->
    bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
    IBLOCK dinum icfg_ist ∈ fsc_cov ->
    ~ (IBLOCK dinum icfg_ist ∈ log_region_set fsc_logst) ->
    bv_unsigned dinum < 16 * Z.of_nat icfg_nib ->
    cov_below fsc_cov size ->
    IBLOCK inum icfg_ist ∈ Sb ->
    (iput_units <= n)%nat ->
    (* THE LEDGER'S CLOSURE, over the ONE figure the parent's free reports.
       [SysLinkBudget.sl_orphan_closes] is exactly this, and it takes no
       credit hypothesis because there is nothing here that could have
       claimed either block: no dirlink has run. *)
    (forall (w : bool) (n' : nat),
       ((n - ip_spend_w w false false)%nat <= n')%nat ->
       (iput_units <= n')%nat) ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    eb = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    sl_sp sp0 M -> sl_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs2 : mword 64) = ientry kd ->
    sl_al sp0 ->
    (* THE TYPE THE CALLER SHOT, and the ONLY thing that gets the
       complement dot clause across this tail's own re-[ilock]: the record
       [ilock] hands back is an EXISTENTIAL, so nothing in the walk below
       can say it is not a directory.  [ity_shot_agree] against the shot the
       CALLER minted before its [iunlock] pins the type, and the generation
       is carriable because [SpecIunlock] returns the share gen-named. *)
    bv_unsigned ty <> T_DIR_z ->
    sie_cap_gpr KT1 M (K - 38) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SL + 0xe6)) -∗
    panic_env -∗
    bio_ctx bn (fs_view fsc_fs gd icfg_dev fsc_cov) -∗
    log_ctx icfg_log bn fsc_fs fsc_cov fsc_logst icfg_dev -∗
    fs_crash_seam fsc_cov fsc_logst -∗
    gen_cert -∗
    is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
    itable_inv -∗
    ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kk -∗
    ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kd -∗
    ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
    ireg_open -∗
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok fsc_ic kk) (slh_tok (icfg_isl kk)) -∗
    is_sleeplock_gen gild gisld (i_lock (ientry kd)) "inode"%string (ic_tok fsc_ic kd) (slh_tok (icfg_isl kd)) -∗
    (* ---- the CHILD, unlocked, its reference already shed ---- *)
    inode_ref_short kk (qi + s)%Qp qi icfg_dev inum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned inum) -∗
    inode_shr_gen kk s icfg_dev inum gy -∗
    ity_shot gy ty -∗
    (* THE UNIT THE [--] SPENDS (durable-disk 2b-inode-5):
       the token the [ip->nlink++] minted and the failed [dirlink] never
       filed in a directory's [FsStateInode.ent_toks]. *)
    FsStateLink.link_tok (fs_gamma_L fsc_fs) (bv_unsigned inum) uty -∗
    (* ---- the PARENT, still locked ---- *)
    sleeplocked_q gisld sd (i_lock (ientry kd)) pidv -∗
    ic_tx_dep fsc_ic kd sd icfg_dev dinum gyd -∗
    i_dev (ientry kd) ↦₄{DfracOwn (1/2)} icfg_dev -∗
    i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dinum -∗
    i_valid (ientry kd) ↦₄ valid_word true -∗
    ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kd dinum dnd bmd -∗
    ity_shot gyd (di_type dnd) -∗
    (* ...and the parent payload's freeze token (§3.9, RULING A-prime) *)
    ifreeze_off (bv_unsigned dinum) -∗
    inode_ref_short kd (qd + sd)%Qp qd icfg_dev dinum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned dinum) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
    proc_priv_bare (proc_addr jx) pidv Vpr -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots 3 -∗
    log_opSe icfg_log n Sb e0 -∗
    (* the transaction token is INSIDE the checked-out descriptor while
       the lock is held (durable-disk B''-tx): the release below hands
       it back, and [sl_tail_bad] takes it from there. *)
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 6) jj ↦ₘ[KT1] bnm jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bw jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 38) jj ↦ₘ[KT1] bo jj) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile),
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        proc_priv_bare (proc_addr jx) pidv Vpr -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
        bslots 3 -∗
        iref_slots 2 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKil HKiup HKup HKeo HK38 Kpop Hkk Hkd Hgeom Hsize Hbm0
           Hbmcov Hbmlog Hist0 Hiblk Hiblog Hinb Hdblk Hdblog Hdnb Hcovb
           Hmem Hiu Hclose Hj Hgl Hlkempty Heb Hsp0 HMsp HMthr
           HMs1 HMs2 Hal Hncd.
    iIntros "Hcg Hown #Htext #Hdata Hpc #Hpe #Hbio #Hlog Hseam Hgen #Hitab #Hitinv
              #Hesck #Hescd #Hireg #Hropen #Hslkk #Hslkd0 Hkeep Hru Hshr #Hshotc Htoken Hslkd
              Hdep Hidev Hiinum Hivalid Hload #Hshotd Hfrz Hkeepd Hrud Hsbb Hsbi
              #Hbmres Hpid #Hprocs #Hdev #Hgeo #Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4
              HbN HbW HbO Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0xe6 c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID0) (mword_of_int (SL + 0xe6)) Ra0 Rs2
              M (K - 38)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (slki_e6 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs2))]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = ientry kd).
    { etransitivity; [ rewrite /M1; apply upd_eq |].
      rewrite add_vec_zero_l. exact HMs2. }
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M1 upd_ne; [exact HMs1 | nz]).
    assert (HM1sp : sl_sp sp0 M1)
      by (rewrite /sl_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1thr : sl_thr m M1).
    { intros c Hc N2 N8 N9 N18. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18). }
    assert (Hpp1 : add_vec_int (mword_of_int (SL + 0xe6) : mword 64) 2
                   = mword_of_int (SL + 0xe8)) by pcw.
    iEval (rewrite Hpp1) in "Hpc".
    (* ===== +0xe8 jal ra,iunlockput ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SL + 0xe8)) Rra
              (mword_of_int 2090236 : mword 21) M1 (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_e8 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0xe8) : mword 64) 4)]> M1).
    assert (Hjup : add_vec (mword_of_int (SL + 0xe8) : mword 64)
                     (sign_extend' 64 (mword_of_int 2090236 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0xe8) : mword 64) 4)
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = ientry kd)
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact HM1s1 | nz]).
    assert (HM2sp : sl_sp sp0 M2)
      by (rewrite /sl_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2thr : sl_thr m M2).
    { intros c Hc N2 N8 N9 N18. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Iunlockput.wp_iunlockput_tx_gen (CID := CID2) gs jx gl gu gd gk
              pd pav pu bn gild gisld bmapstart
 size kd qd sd gyd dinum dnd bmd
              n Sb false false false e0 pidv dq dqb dqs
              M2 (K - 38)%nat eb b lks
              Vpr HKup Hkd ltac:(discriminate) ltac:(discriminate) Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
              Hdblk Hdblog Hdnb Hcovb Hiu Hj Hgl HM2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hitab Hitinv
                    Hescd Hireg Hropen Hslkd0 Hslkd Hdep Hidev Hiinum Hivalid
                    Hload Hshotd Hfrz [$Hkeepd $Hrud] Hsbb Hsbi Hbmres Hpid Hprocs Hdev Hgeo
                    Hdlk Hbsl [] Hop").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { done. }
    iIntros (CID3 Hq3 mup n1 Sb1 w)
      "%Hcsup Hcg Hown _ _ Hpc Hpid Hsbb Hsbi Hbsl %Hsb1 %Hwm
       %Hcrbw %Hn1 Hop Htx Hislot".
    assert (Hpcec : ret_pc (M2 !!! Regidx Rra : mword 64)
                    = mword_of_int (SL + 0xec)) by (rewrite HM2ra; pcw).
    iEval (rewrite Hpcec) in "Hpc".
    (* ===== +0xec c.j -> [bad:] =====
       THE ONE INSTRUCTION THE TWO ARMS DO NOT SHARE.  ARM F's block is
       the last thing before [bad:] and falls through into it; this one
       sits a block EARLIER -- gcc emits the cold blocks in source order
       and the guard's [if] is the earlier one -- so it needs the explicit
       branch. *)
    assert (Htgf4 : add_vec (mword_of_int (SL + 0xec) : mword 64)
                      (sign_extend' 64
                         (sign_extend' 21
                            (concat_vec (mword_of_int 4 : mword 11) ('b"0"))))
                    = mword_of_int (SL + 0xf4)) by pcw.
    iApply (wp_cj_s_sconf (CID := CID3) (mword_of_int (SL + 0xec))
              (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0")))
              mup (K - 38)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (slki_ec with "Htext"). }
    iIntros (CID4 Hq4). iNext. iIntros "Hcg Hpc".
    iEval (rewrite Htgf4) in "Hpc".
    iDestruct (cpu_own_transport CID3 CID4 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    assert (Hupsp : sl_sp sp0 mup).
    { rewrite /sl_sp (callee_saved_lookup Hcsup csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM2sp. }
    assert (Hups1 : (mup !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite (callee_saved_lookup Hcsup Rs1 ltac:(vm_compute; reflexivity)).
      exact HM2s1. }
    assert (Hupthr : sl_thr m mup).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcsup c Hc).
      exact (HM2thr c Hc N2 N8 N9 N18). }
    (* the ledger CLOSES, and the count is therefore a successor *)
    assert (Hiu1 : (iput_units <= n1)%nat)
      by exact (Hclose w n1 (proj1 Hn1)).
    destruct n1 as [| u1]; [exfalso; unfold iput_units in Hiu1; lia |].
    assert (Hmem1 : IBLOCK inum icfg_ist ∈ Sb1) by exact (Hsb1 _ Hmem).
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID4)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (sl_tail_bad (CID0 := CID4) gs jx gl gu gd gk pd pav pu bn
              gil gisl bmapstart size
              kk qi s gy inum ty u1 Sb1 uty pidv dq dqb dqs m mup sp0 K eb b
              lks bnm bw bo
              Vpr HKil HKiup HKup HKeo HK38 Kpop Hkk Hgeom Hsize Hbm0
              Hbmcov Hbmlog Hist0 Hiblk Hiblog Hinb Hcovb Hmem1 Hiu1 Hj Hgl
              Hlkempty Heb Hsp0 Hupsp Hupthr Hups1 Hal Hncd
              with "Hcg Hown Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen Hitab Hitinv
                    Hesck Hireg Hropen Hslkk Hkeep Hru Hshr Hshotc Htoken Hsbb Hsbi Hbmres Hpid
                    Hprocs Hdev Hgeo Hdlk Hbsl Hop Htx Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
                    [Hislot Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf)
      "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpid Hsbb Hsbi Hbsl
       Hislot2".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iDestruct (iref_slots_combine 1 1 with "Hislot Hislot2") as "Hislots".
    iApply ("Hcont" $! mf with "[%] [%] Hcg Hown Htce Hcce Hpc Hpid
              Hsbb Hsbi Hbsl Hislots").
    { exact Hcsf. }
    { exact Ha0f. }
  Qed.

End ProofSysLinkTails.

End SysLinkTails.
