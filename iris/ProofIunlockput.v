(* ProofIunlockput.v -- iunlockput over the SIE-agnostic sconf world.

     void iunlockput(struct inode *ip) { iunlock(ip); iput(ip); }

   32 bytes, 14 instructions.  There is no control flow, no memory access
   outside the frame and no ghost move except ONE: at the instruction
   between the two calls the SHARE iunlock just handed back is gathered
   with the parent reference the caller retained
   ([IcacheRef.inode_ref_gather]), which is what turns iunlock's output into
   iput's input.  Everything else is the frame and the two [jal]s.

   The frame is 32 bytes but only THREE slots are used -- ra@24, s0@16,
   s1@8; the word at sp+0 is padding gcc never touches, so it rides through
   as an anonymous [stack_own] slot and goes back untouched at the pop. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import FdSlots.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import WpUart.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import IcacheEscrow.
Require Import CodeIunlockput.
Require Import SpecIunlock SpecIput.
Require Import SpecIunlockput.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Set Printing Depth 40.

Module IunlockputProof (IU : IUNLOCK) (IP : IPUT) : IUNLOCKPUT.

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac iuidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* the three registers the frame saves *)
Definition iulp_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition iulp_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))).

Section ProofIunlockputMain.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, ICFG : icfg,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE WALK IS THE GEN FORM (GR-2a finding 1).  iunlockput is a wrapper,
     so this is one call site's worth of threading; the counted seal is
     after the proof. *)
  Lemma wp_iunlockput_gen
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (k : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn' : dinode) (bm' : blkmap)
      (n : nat) (Sb : gset Z) (crb cru crz : bool) (e0 : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
    : wp_iunlockput_gen_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                             gil gisl cov logstart bmapstart inodestart nib
                             size dev used k qi s gy inum dn' bm' n Sb crb cru
                             crz e0 pidv dq dqb dqs m K eb b lks.
  Proof.
    cbv beta delta [wp_iunlockput_gen_body].
    intros pcE ip pj ret_tgt HK Hk Hcrb Hcru Hlg Hsize Hbm0 Hbmcov Hbmlog Hins0
           Hiblk Hiblklog Hinumb Hcovb Hnu Hj Hgl Ha0 Hfresh.
    pose proof HK as HK'. 
    assert (Hipe : ip = ientry k) by reflexivity.
    iIntros "Hcg Hcnt Htc Hclm #Htext #Hkd Hpc #Hpenv Hbio Hlogc Hitb2 #Hitbl #Hesc Hireg
              Hropen #Hslk Hstok Hpid Hdep Hidev Hinumc Hvalid Hlk #Hshot Hfrz Hparp
              Hbms Hins Hbitmap Hppid #Hprocs Hdev Hgeom Hdlk Hbslots Hnlz Hlogop
              Hcont".
    (* SIMP-2: the short parent arrives PACKAGED with its provenance unit
       ([IcacheRef.inode_refp_short]); split once, and the gather below is
       unchanged. *)
    iDestruct "Hparp" as "[Hpar Hru]".
    (* THE eb/b BRIDGE, once per top-level lemma (eb-generic-sweep.md). *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    iPoseProof (iulpi_00 with "Htext") as "Hi00".
    iPoseProof (iulpi_02 with "Htext") as "Hi02".
    iPoseProof (iulpi_04 with "Htext") as "Hi04".
    iPoseProof (iulpi_06 with "Htext") as "Hi06".
    iPoseProof (iulpi_08 with "Htext") as "Hi08".
    iPoseProof (iulpi_0a with "Htext") as "Hi0a".
    iPoseProof (iulpi_0c with "Htext") as "Hi0c".
    iPoseProof (iulpi_10 with "Htext") as "Hi10".
    iPoseProof (iulpi_12 with "Htext") as "Hi12".
    iPoseProof (iulpi_16 with "Htext") as "Hi16".
    iPoseProof (iulpi_18 with "Htext") as "Hi18".
    iPoseProof (iulpi_1a with "Htext") as "Hi1a".
    iPoseProof (iulpi_1c with "Htext") as "Hi1c".
    iPoseProof (iulpi_1e with "Htext") as "Hi1e".
    (* ===== +0x00 c.addi sp,sp,-32 ===== *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HR1sp : iulp_sp m R1) by (rewrite /iulp_sp /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (v1) "Hf1". iDestruct "S2" as (v2) "Hf2".
    iDestruct "S3" as (v3) "Hf3".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb1) in "Hf1". iEval (rewrite -Hb2) in "Hf2".
    iEval (rewrite -Hb3) in "Hf3".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2
                    = mword_of_int (KernelSyms.iunlockput + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 .. +0x06 : the three saves ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iunlockput + 0x02))
              (mword_of_int 3 : mword 6) Rra R1 (K - 4)%nat v1 b
              with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.iunlockput + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlockput + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iunlockput + 0x04))
              (mword_of_int 2 : mword 6) Rs0 R1 (K - 4)%nat v2 b
              with "Hcg Hpc Hi04 Hf2").
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.iunlockput + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlockput + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iunlockput + 0x06))
              (mword_of_int 1 : mword 6) Rs1 R1 (K - 4)%nat v3 b
              with "Hcg Hpc Hi06 Hf3").
    iIntros (CID4 Hq4) "Hcg Hpc Hf3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.iunlockput + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlockput + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s1 : (R1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hf2".
    iEval (rewrite Hb3; rgne; rewrite HR1s1) in "Hf3".
    (* ===== +0x08 c.addi4spn s0,sp,32 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.iunlockput + 0x08))
              (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) Rs0
              R1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (HR2sp : iulp_sp m R2)
      by (rewrite /iulp_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2a0 : R2 !!! Regidx Ra0 = ip)
      by (rewrite /R2 upd_ne; [| nz]; rewrite /R1 upd_ne; [exact Ha0 | nz]).
    assert (HR2thr : iulp_thr m R2).
    { intros c Hcs N2 N8 N9.
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.iunlockput + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlockput + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    (* ===== +0x0a c.mv s1,a0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iunlockput + 0x0a)) Rs1 Ra0
              R2 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0a").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (R3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R2 Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = ip).
    { rewrite /R3 upd_eq. rgne. rewrite HR2a0. apply add_vec_zero_l. }
    assert (HR3a0 : R3 !!! Regidx Ra0 = ip)
      by (rewrite /R3 upd_ne; [exact HR2a0 | nz]).
    assert (HR3sp : iulp_sp m R3)
      by (rewrite /iulp_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : iulp_thr m R3).
    { intros c Hcs N2 N8 N9.
      rewrite /R3 upd_ne; [| regne]. exact (HR2thr c Hcs N2 N8 N9). }
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.iunlockput + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlockput + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c jal ra,iunlock ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iunlockput + 0x0c)) Rra
              (mword_of_int 2096718 : mword 21) R3 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (R4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iunlockput + 0x0c) : mword 64) 4)]> R3).
    assert (Htgtiu : add_vec (mword_of_int (KernelSyms.iunlockput + 0x0c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096718 : mword 21))
                     = mword_of_int KernelSyms.iunlock) by pcw.
    iEval (rewrite Htgtiu) in "Hpc".
    assert (HR4a0 : R4 !!! Regidx Ra0 = ip)
      by (rewrite /R4 upd_ne; [exact HR3a0 | nz]).
    assert (HR4s1 : R4 !!! Regidx Rs1 = ip)
      by (rewrite /R4 upd_ne; [exact HR3s1 | nz]).
    assert (HR4sp : iulp_sp m R4)
      by (rewrite /iulp_sp /R4 upd_ne; [exact HR3sp | nz]).
    assert (HR4ra : R4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iunlockput + 0x0c) : mword 64) 4)
      by (rewrite /R4; apply upd_eq).
    assert (HR4thr : iulp_thr m R4).
    { intros c Hcs N2 N8 N9.
      rewrite /R4 upd_ne; [| regne]. exact (HR3thr c Hcs N2 N8 N9). }
    iDestruct (cpu_own_transport CID CID7 0%nat eb pj b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CID7) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    (* "sleep lock" outranks "itable": weaken [Hfresh]'s bound. *)
    assert (Hfresh_sl : locks_below lks "sleep lock")
      by lkbelow.
    iApply (IU.wp_iunlock_sconf gs gfs gi cn gil gisl cov logstart k s gy dev inum
              dn' bm' pidv dq R4 (K - 4)%nat eb pj b lks
              ltac:(lia) Hk ltac:(rewrite HR4a0; exact Hipe)
              Hfresh_sl
              with "Hcg Hcnt Htext Hpc Hitbl Hesc Hslk Hstok Hpid Hppid
                    Hprocs Hdep Hidev Hinumc Hvalid Hlk Hshot Hfrz").
    all: try lkbelow.
    iIntros (CID8 Hq8 mU) "%HcsU Hcg Hcnt Hpc Hppid Hshr".
    iDestruct (inode_shr_gen_forget with "Hshr") as "Hshr".
    assert (Hpc10 : ret_pc (R4 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.iunlockput + 0x10))
      by (rewrite HR4ra; pcw).
    iEval (rewrite Hpc10) in "Hpc".
    pose proof HcsU as HcsU_cs.
    assert (HmUs1 : mU !!! Regidx Rs1 = ip)
      by (rewrite (callee_saved_lookup HcsU_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HR4s1).
    assert (HmUsp : iulp_sp m mU).
    { rewrite /iulp_sp
        (callee_saved_lookup HcsU_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR4sp. }
    assert (HmUthr : iulp_thr m mU).
    { intros c Hcs N2 N8 N9.
      rewrite (callee_saved_lookup HcsU_cs c Hcs).
      exact (HR4thr c Hcs N2 N8 N9). }
    (* THE SEAM: the share iunlock gave back, gathered with the parent the
       caller retained, is the canonical reference iput spends. *)
    iDestruct (inode_ref_gather with "Hpar Hshr") as "Href".
    (* ===== +0x10 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iunlockput + 0x10)) Ra0 Rs1
              mU (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi10").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mU Rs1))]> mU).
    assert (HR5a0 : R5 !!! Regidx Ra0 = ip).
    { rewrite /R5 upd_eq. rgne. rewrite HmUs1. apply add_vec_zero_l. }
    assert (HR5sp : iulp_sp m R5)
      by (rewrite /iulp_sp /R5 upd_ne; [exact HmUsp | nz]).
    assert (HR5thr : iulp_thr m R5).
    { intros c Hcs N2 N8 N9.
      rewrite /R5 upd_ne; [| regne]. exact (HmUthr c Hcs N2 N8 N9). }
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.iunlockput + 0x10) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlockput + 0x12)) by pcw.
    iEval (rewrite Hpp12) in "Hpc".
    (* ===== +0x12 jal ra,iput ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iunlockput + 0x12)) Rra
              (mword_of_int 2096924 : mword 21) R5 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi12").
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (R6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iunlockput + 0x12) : mword 64) 4)]> R5).
    assert (Htgtip : add_vec (mword_of_int (KernelSyms.iunlockput + 0x12) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096924 : mword 21))
                     = mword_of_int KernelSyms.iput) by pcw.
    iEval (rewrite Htgtip) in "Hpc".
    assert (HR6a0 : R6 !!! Regidx Ra0 = ip)
      by (rewrite /R6 upd_ne; [exact HR5a0 | nz]).
    assert (HR6sp : iulp_sp m R6)
      by (rewrite /iulp_sp /R6 upd_ne; [exact HR5sp | nz]).
    assert (HR6ra : R6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iunlockput + 0x12) : mword 64) 4)
      by (rewrite /R6; apply upd_eq).
    assert (HR6thr : iulp_thr m R6).
    { intros c Hcs N2 N8 N9.
      rewrite /R6 upd_ne; [| regne]. exact (HR5thr c Hcs N2 N8 N9). }
    iDestruct (cpu_own_transport CID8 CID10 0%nat eb pj b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* THE WIDE HOP: iunlock is not in the ALREADY-GENERALIZED set, so the
       complement is still at the entry hart CID -- span all the way from
       there to right before iput's call, skipping iunlock's call in one hop
       (eb-generic-sweep.md). *)
    iDestruct (trap_csrs_ext_transport CID CID10 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Htc") as "Htc".
    iDestruct (cpu_claim_ext_transport CID CID10 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hclm") as "Hclm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID7) (CIDb := CID10) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    (* SIMP-1: iunlockput has no boot caller at all, so its own contracts
       state the regime at the persistent [ireg_open]; iput's gen form keeps
       the index, and this is it at [rg := true]. *)
    iEval (rewrite -ireg_regime_true) in "Hropen".
    iApply (IP.wp_iput_gen gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl gil gisl
              cov logstart bmapstart inodestart nib size dev used
              k (qi + s)%Qp inum n Sb crb cru crz e0 pidv dq dqb dqs R6 (K - 4)%nat eb b lks true
              ltac:(lia) Hk Hcrb Hcru
              Hlg Hsize Hbm0 Hbmcov Hbmlog Hins0 Hiblk Hiblklog
              Hinumb Hcovb Hnu Hj Hgl ltac:(rewrite HR6a0; exact Hipe)
              Hfresh
              with "Hcg Hcnt Htc Hclm Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl Hesc Hireg
                    Hropen Hslk [$Href $Hru] Hbms Hins Hbitmap Hppid Hprocs Hdev Hgeom Hdlk
                    Hbslots Hnlz Hlogop").
    all: try lkbelow.
    iIntros (CID11 Hq11 mP n' used' Sb' wp)
            "%HcsP Hcg Hcnt Htc Hclm Hpc Hppid Hbms Hins %Hsub Hbitmap Hbslots
             %Hssub %Hwbm %Hwc %Hbud Hlogop Hslot _".
    assert (Hpc16 : ret_pc (R6 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.iunlockput + 0x16))
      by (rewrite HR6ra; pcw).
    iEval (rewrite Hpc16) in "Hpc".
    pose proof HcsP as HcsP_cs.
    assert (HmPsp : iulp_sp m mP).
    { rewrite /iulp_sp
        (callee_saved_lookup HcsP_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR6sp. }
    assert (HmPthr : iulp_thr m mP).
    { intros c Hcs N2 N8 N9.
      rewrite (callee_saved_lookup HcsP_cs c Hcs).
      exact (HR6thr c Hcs N2 N8 N9). }
    (* ===== +0x16 .. +0x1a : the three restores ===== *)
    assert (Hc1 : add_vec (mP !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HmPsp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc2 : add_vec (mP !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HmPsp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc3 : add_vec (mP !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HmPsp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iunlockput + 0x16))
              (mword_of_int 3 : mword 6) Rra mP (K - 4)%nat
              (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi16 [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID12 Hq12) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> mP).
    assert (HP1sp : iulp_sp m P1)
      by (rewrite /iulp_sp /P1 upd_ne; [exact HmPsp | nz]).
    assert (HP1thr : iulp_thr m P1).
    { intros c Hcs N2 N8 N9.
      rewrite /P1 upd_ne; [| regne]. exact (HmPthr c Hcs N2 N8 N9). }
    assert (HP1ra : P1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.iunlockput + 0x16) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlockput + 0x18)) by pcw.
    iEval (rewrite Hpp18) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iunlockput + 0x18))
              (mword_of_int 2 : mword 6) Rs0 P1 (K - 4)%nat
              (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi18 [Hf2]").
    { iEval (rewrite HP1sp -HmPsp Hc2). iExact "Hf2". }
    iIntros (CID13 Hq13) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -HmPsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : iulp_sp m P2)
      by (rewrite /iulp_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : iulp_thr m P2).
    { intros c Hcs N2 N8 N9.
      rewrite /P2 upd_ne; [| regne]. exact (HP1thr c Hcs N2 N8 N9). }
    assert (HP2ra : P2 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.iunlockput + 0x18) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlockput + 0x1a)) by pcw.
    iEval (rewrite Hpp1a) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iunlockput + 0x1a))
              (mword_of_int 1 : mword 6) Rs1 P2 (K - 4)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi1a [Hf3]").
    { iEval (rewrite HP2sp -HmPsp Hc3). iExact "Hf3". }
    iIntros (CID14 Hq14) "Hcg Hpc Hf3".
    iEval (rewrite HP2sp -HmPsp Hc3) in "Hf3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : iulp_sp m P3)
      by (rewrite /iulp_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (HP3thr : iulp_thr m P3).
    { intros c Hcs N2 N8 N9.
      rewrite /P3 upd_ne; [| regne]. exact (HP2thr c Hcs N2 N8 N9). }
    assert (HP3ra : P3 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.iunlockput + 0x1a) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlockput + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== +0x1c c.addi16sp sp,32 : pop ===== *)
    assert (Hwv : add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP3sp. apply bv_eq.
      rewrite !add_vec64_unsigned.
      rewrite bv_wrap_add_idemp_l.
      assert (Hz : bv_unsigned (sign_extend' 64
                     (sign_extend' 12 (mword_of_int 32 : mword 6)) : mword 64)
                   = 18446744073709551584) by (vm_compute; reflexivity).
      assert (Hz2 : bv_unsigned (sign_extend' 64
                      (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64)
                    = 32) by (vm_compute; reflexivity).
      rewrite Hz Hz2.
      replace (bv_unsigned (m !!! Regidx csp_rs1 : mword 64)
                 + 18446744073709551584 + 32)
        with (bv_unsigned (m !!! Regidx csp_rs1 : mword 64)
                 + 18446744073709551616) by ring.
      rewrite -bv_wrap_add_idemp_r.
      assert (Hm0 : bv_wrap 64 18446744073709551616 = 0)
        by (vm_compute; reflexivity).
      rewrite Hm0 Z.add_0_r.
      apply bv_wrap_small. apply bv_unsigned_in_range. }
    assert (Hpop : (P3 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HP3sp. unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iAssert (stack_own (KTR := KT1) (m !!! Regidx csp_rs1 : mword 64) 4)
      with "[Hf1 Hf2 Hf3 S4]" as "Hstk".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1" |].
      iSplitL "Hf2"; [iExists _; iExact "Hf2" |].
      iSplitL "Hf3"; [iExists _; iExact "Hf3" |].
      iSplitL "S4"; [iExact "S4" |].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.iunlockput + 0x1c))
              (mword_of_int 2 : mword 6) P3 (K - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi1c Hstk").
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (P4 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P3).
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.iunlockput + 0x1c) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlockput + 0x1e)) by pcw.
    iEval (rewrite Hpp1e) in "Hpc".
    (* ===== +0x1e c.ret ===== *)
    assert (HP4ra : P4 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3ra | nz]).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.iunlockput + 0x1e)) Rra P4 K b
              ltac:(nz) with "Hcg Hpc Hi1e").
    iIntros (CID16 Hq16) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P4 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP4ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (Csp : P4 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P4 upd_eq; exact Hwv).
    assert (Cs0 : P4 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_eq. reflexivity. }
    assert (Cs1 : P4 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_eq. reflexivity. }
    assert (Hfin : iulp_thr m P4).
    { intros c Hcs N2 N8 N9.
      rewrite /P4 upd_ne; [| regne]. exact (HP3thr c Hcs N2 N8 N9). }
    assert (Cs2 : P4 !!! Regidx (mword_of_int 18 : mword 5)
                  = (m !!! Regidx (mword_of_int 18 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs3 : P4 !!! Regidx (mword_of_int 19 : mword 5)
                  = (m !!! Regidx (mword_of_int 19 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs4 : P4 !!! Regidx (mword_of_int 20 : mword 5)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs5 : P4 !!! Regidx (mword_of_int 21 : mword 5)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs6 : P4 !!! Regidx (mword_of_int 22 : mword 5)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs7 : P4 !!! Regidx (mword_of_int 23 : mword 5)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs8 : P4 !!! Regidx (mword_of_int 24 : mword 5)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs9 : P4 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs10 : P4 !!! Regidx (mword_of_int 26 : mword 5)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs11 : P4 !!! Regidx (mword_of_int 27 : mword 5)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    iDestruct (cpu_own_transport CID11 CID16 0%nat eb pj b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* iput IS generalized -- thread NORMALLY, matching cpu_own_transport's
       own span (fresh at iput's own return hart CID11). *)
    iDestruct (trap_csrs_ext_transport CID11 CID16 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Htc") as "Htc".
    iDestruct (cpu_claim_ext_transport CID11 CID16 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hclm") as "Hclm".
    iSpecialize ("Hcont" $! CID16 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! P4 n' used' Sb' wp with "[%] Hcg Hcnt Htc Hclm Hpc Hppid Hbms Hins [%]
                                             Hbitmap Hbslots [%] [%] [%] [%] Hlogop Hslot").
    { unfold callee_saved. split_and!; assumption. }
    { exact Hsub. }
    { exact Hssub. }
    { exact Hwbm. }
    { exact Hwc. }
    { exact Hbud. }
  Qed.

  (* ===================================================================== *)
  (*  THE COUNTED SEAL, at the [log_op] existential's own witness.          *)
  (*  [ip_spend_w w false false <= 2 <= iput_units], so the gen bound is    *)
  (*  weaker and the seal's arithmetic goes the easy way.                   *)
  (* ===================================================================== *)
  Lemma wp_iunlockput_sconf
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (k : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn' : dinode) (bm' : blkmap)
      (n : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
    : wp_iunlockput_sconf_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                               gil gisl cov logstart bmapstart inodestart nib
                               size dev used k qi s gy inum dn' bm' n
                               pidv dq dqb dqs m K eb b lks.
  Proof.
    cbv beta delta [wp_iunlockput_sconf_body].
    intros pcE ip pj ret_tgt HK Hk Hlg Hsize Hbm0 Hbmcov Hbmlog Hins0
           Hiblk Hiblklog Hinumb Hcovb Hnu Hj Hgl Ha0 Hfresh.
    iIntros "Hcg Hcnt Htc Hclm #Htext #Hkd Hpc #Hpenv Hbio Hlogc Hitb2 #Hitbl #Hesc Hireg
              Hropen #Hslk Hstok Hpid Hdep Hidev Hinumc Hvalid Hlk #Hshot Hfrz Hparp
              Hbms Hins Hbitmap Hppid #Hprocs Hdev Hgeom Hdlk Hbslots Hlogop
              Hcont".
    iDestruct "Hlogop" as (Sb0) "Hlogop".
    iDestruct (log_opS_named with "Hlogop") as (e00) "Hlogop".
    iApply (wp_iunlockput_gen gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl gil gisl
              cov logstart bmapstart inodestart nib size dev used
              k qi s gy inum dn' bm' n Sb0 false false false e00
              pidv dq dqb dqs m K eb b lks
              HK Hk ltac:(discriminate) ltac:(discriminate)
              Hlg Hsize Hbm0 Hbmcov Hbmlog Hins0 Hiblk Hiblklog
              Hinumb Hcovb Hnu Hj Hgl Ha0 Hfresh
              with "Hcg Hcnt Htc Hclm Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl Hesc Hireg
                    Hropen Hslk Hstok Hpid Hdep Hidev Hinumc Hvalid Hlk Hshot Hfrz
                    Hparp
                    Hbms Hins Hbitmap Hppid Hprocs Hdev Hgeom Hdlk Hbslots []
                    Hlogop [Hcont]").
    all: try lkbelow.
    { iEval (cbn beta iota). iEmpIntro. }
    iEval (rewrite /wp_next).
    iIntros (CIDf) "%Hchain".
    iIntros (mf n' used' Sb' wf) "%Hcs Hcg Hcnt Htc Hclm Hpc Hppid Hbms Hins
                               %Husub Hbitmap Hbslots %Hssub %Hwbm %Hwc %Hbnd Hlogop Hslot".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [exact Hchain|].
    iApply ("Hcont" $! mf n' used' with "[%] Hcg Hcnt Htc Hclm Hpc Hppid Hbms Hins
                     [%] Hbitmap Hbslots [%] [Hlogop] Hslot").
    { exact Hcs. }
    { exact Husub. }
    { unfold ip_spend_w, ip_bm in Hbnd. unfold iput_units.
      destruct wf; simpl in Hbnd; lia. }
    { iApply (log_opS_op with "Hlogop"). }
  Qed.

End ProofIunlockputMain.

End IunlockputProof.
