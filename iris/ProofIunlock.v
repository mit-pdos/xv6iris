(* ProofIunlock.v -- iunlock over the SIE-agnostic sconf world.

     void iunlock(struct inode *ip) {
       if (ip == 0 || !holdingsleep(&ip->lock) || ip->ref < 1)
         panic("iunlock");
       releasesleep(&ip->lock);
     }

   64 bytes, 25 instructions, straight-line once the three panic tests are
   refuted -- structurally brelse's first half, and proved the same way.

   THE PARK is [IcacheEscrow.ic_swap_park], fired in one mask-balanced
   opening of [ic_escrow] just before the releasesleep call: the checked-out
   bundle (the two identity halves, the FULL valid cell, the loaded content
   with its region fragment at the parked record -- PARKED-MEANS-FLUSHED,
   §13.1d) goes back in, and out come the CHECKOUT TOKEN -- which is now the
   whole of what the sleeplock protects, so it is exactly releasesleep's [R]
   -- and the caller's SHARE, at its own fraction, device and inum (v3: the
   checkout descriptor pins all three, §14.8).

   The three panic tests: [ip == 0] because the entry is slot [k]
   ([iul_entry_nonzero], i.e. [IcacheRef.ientry_unsigned]); [ip->ref < 1]
   from [IcacheInv.iref_live_load_au] against [itable_inv], over a LIVENESS
   SLICE borrowed out of the escrow's checked-out arm for that one atomic
   update ([ic_open_out]; the holder's FULL valid cell is what refutes the
   other two arms) -- after ilock's deposit the holder owns nothing of its
   own, and the arm's deposit is a share, which has no count fragment;
   and [!holdingsleep] from the holder's bundle -- the token, the lock's pid
   field and the caller's own pid cell agreeing -- which is what makes
   SpecHoldingsleep's HOLDER variant answer 1. *)
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
Require Import WpLock SleepLock.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpAu4.
Require Import FdSlots.
Require Import ProcGeom.
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import MinstretInv.
Require Import CodeIunlock.
Require Import SpecHoldingsleep SpecReleasesleep.
Require Import SpecIunlock.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Set Printing Depth 40.

(* the entry address is never zero -- [ProofIlock.il_entry_nonzero]'s twin
   (a proof file may not import another proof file) *)
Lemma iul_entry_nonzero (k : nat) : (k < NINODE)%nat -> uint (ientry k) <> 0.
Proof.
  intros Hk. rewrite uint_unsigned (ientry_unsigned k ltac:(lia)).
  unfold ISLOTSZ, KernelSyms.itable. lia.
Qed.


Module IunlockProof (HS : HOLDINGSLEEP) (RS : RELEASESLEEP) : IUNLOCK.

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne := reg_ne_side.

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac iuidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* the four registers the frame saves *)
Definition iul_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition iul_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))).

Section ProofIunlockMain.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, ICFG : icfg, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* iunlock's 32-byte frame: ra@24 s0@16 s1@8 s2@0 *)
  Definition iul_frame (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈[KT1] (m !!! Regidx Rs2 : mword 64))%I.

  Definition iul_cont `{CID0 : CpuId} 
      (cn : ic_names) (k : nat) (s : Qp) (g : gname) (dev inum : mword 32)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) : iProp Σ :=
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr KT1 mf K b p -∗
        cpu_own 0 eb p b lks -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid p ↦₄{dq} pidv -∗
        inode_shr_gen k s dev inum g -∗
        WP (Loop : expr riscv_lang))%I.

  Lemma wp_iunlock_sconf 
      (gs : list gname)
      (gfs : fs_names) (gi : gname)
      (cn : ic_names)
      (gil gisl : gname)
      (cov : gset Z) (logstart : Z)
      (k : nat) (s : Qp) (g : gname) (dev inum : mword 32)
      (dn' : dinode) (bm' : blkmap)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string)
    : wp_iunlock_sconf_body gs gfs gi cn gil gisl cov logstart k s g dev inum
                            dn' bm' pidv dq m K eb p b lks.
  Proof.
    cbv beta delta [wp_iunlock_sconf_body].
    intros pcE ip ret_tgt HK Hk Ha0 Hfresh.
    pose proof HK as HK'. 
    assert (Hipe : ip = ientry k) by reflexivity.
    assert (Hipnz : uint ip <> 0)
      by (rewrite Hipe; exact (iul_entry_nonzero k Hk)).
    iIntros "Hcg Hcnt #Htext Hpc #Hitbl #Hesc #Hslk Hstok Hpid Hppid
              #Hprocs Hdep Hidev Hinumc Hvalid Hlk #Hshot Hfrz Hcont".
    iEval (rewrite Hipe) in "Hidev".
    iEval (rewrite Hipe) in "Hinumc".
    iEval (rewrite Hipe) in "Hvalid".
    iAssert (iul_cont (CID0 := CID)  cn k s g dev inum pidv dq m K eb p b lks)%I
      with "[Hcont]" as "Hcont"; [rewrite /iul_cont; iExact "Hcont" |].
    iPoseProof (iui2_00 with "Htext") as "Hi00".
    iPoseProof (iui2_02 with "Htext") as "Hi02".
    iPoseProof (iui2_04 with "Htext") as "Hi04".
    iPoseProof (iui2_06 with "Htext") as "Hi06".
    iPoseProof (iui2_08 with "Htext") as "Hi08".
    iPoseProof (iui2_0a with "Htext") as "Hi0a".
    iPoseProof (iui2_0c with "Htext") as "Hi0c".
    iPoseProof (iui2_0e with "Htext") as "Hi0e".
    iPoseProof (iui2_10 with "Htext") as "Hi10".
    iPoseProof (iui2_14 with "Htext") as "Hi14".
    iPoseProof (iui2_16 with "Htext") as "Hi16".
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
    assert (HR1sp : iul_sp m R1) by (rewrite /iul_sp /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (v1) "Hf1". iDestruct "S2" as (v2) "Hf2".
    iDestruct "S3" as (v3) "Hf3". iDestruct "S4" as (v4) "Hf4".
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
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb1) in "Hf1". iEval (rewrite -Hb2) in "Hf2".
    iEval (rewrite -Hb3) in "Hf3". iEval (rewrite -Hb4) in "Hf4".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 .. +0x08 : the four saves ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iunlock + 0x02)) (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat v1 b with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iunlock + 0x04)) (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat v2 b with "Hcg Hpc Hi04 Hf2").
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iunlock + 0x06)) (mword_of_int 1 : mword 6) Rs1
              R1 (K - 4)%nat v3 b with "Hcg Hpc Hi06 Hf3").
    iIntros (CID4 Hq4) "Hcg Hpc Hf3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iunlock + 0x08)) (mword_of_int 0 : mword 6) Rs2
              R1 (K - 4)%nat v4 b with "Hcg Hpc Hi08 Hf4").
    iIntros (CID5 Hq5) "Hcg Hpc Hf4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s1 : (R1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s2 : (R1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hf2".
    iEval (rewrite Hb3; rgne; rewrite HR1s1) in "Hf3".
    iEval (rewrite Hb4; rgne; rewrite HR1s2) in "Hf4".
    iAssert (iul_frame m) with "[Hf1 Hf2 Hf3 Hf4]" as "Hframe".
    { rewrite /iul_frame.
      iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "Hf3"; [iExact "Hf3" |]. iExact "Hf4". }
    (* ===== +0x0a c.addi4spn s0,sp,32 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.iunlock + 0x0a)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 R1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (HR2sp : iul_sp m R2)
      by (rewrite /iul_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2a0 : R2 !!! Regidx Ra0 = ip)
      by (rewrite /R2 upd_ne; [| nz]; rewrite /R1 upd_ne; [exact Ha0 | nz]).
    assert (HR2thr : iul_thr m R2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c c.beqz a0 : DEAD panic arm, ip <> 0 ===== *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.iunlock + 0x0c))
              (mword_of_int 20 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              R2 (K - 4)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HR2a0; exact (inode_ptr_nonzero ip Hipnz))
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hq7) "Hcg Hpc".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x0e)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== +0x0e c.mv s1,a0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iunlock + 0x0e)) Rs1 Ra0
              R2 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0e").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (R3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R2 Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = ip).
    { rewrite /R3 upd_eq. rgne. rewrite HR2a0. apply add_vec_zero_l. }
    assert (HR3a0 : R3 !!! Regidx Ra0 = ip)
      by (rewrite /R3 upd_ne; [exact HR2a0 | nz]).
    assert (HR3sp : iul_sp m R3)
      by (rewrite /iul_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : iul_thr m R3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R3 upd_ne; [| regne]. exact (HR2thr c Hcs N2 N8 N9 N18). }
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ===== +0x10 addi s2,a0,16 : s2 := &ip->lock ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iunlock + 0x10)) Rs2 Ra0
              (mword_of_int 16 : mword 12) R3 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi10").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (R4 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (rget R3 Ra0)
                     (sign_extend' 64 (mword_of_int 16 : mword 12)))]> R3).
    assert (HR4s2 : R4 !!! Regidx Rs2 = i_lock ip).
    { rewrite /R4 upd_eq. rgne. rewrite HR3a0. reflexivity. }
    assert (HR4s1 : R4 !!! Regidx Rs1 = ip)
      by (rewrite /R4 upd_ne; [exact HR3s1 | nz]).
    assert (HR4sp : iul_sp m R4)
      by (rewrite /iul_sp /R4 upd_ne; [exact HR3sp | nz]).
    assert (HR4thr : iul_thr m R4).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R4 upd_ne; [| regne]. exact (HR3thr c Hcs N2 N8 N9 N18). }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x10) : mword 64) 4
                    = mword_of_int (KernelSyms.iunlock + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iunlock + 0x14)) Ra0 Rs2
              R4 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi14").
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R4 Rs2))]> R4).
    assert (HR5a0 : R5 !!! Regidx Ra0 = i_lock ip).
    { rewrite /R5 upd_eq. rgne. rewrite HR4s2. apply add_vec_zero_l. }
    assert (HR5s2 : R5 !!! Regidx Rs2 = i_lock ip)
      by (rewrite /R5 upd_ne; [exact HR4s2 | nz]).
    assert (HR5s1 : R5 !!! Regidx Rs1 = ip)
      by (rewrite /R5 upd_ne; [exact HR4s1 | nz]).
    assert (HR5sp : iul_sp m R5)
      by (rewrite /iul_sp /R5 upd_ne; [exact HR4sp | nz]).
    assert (HR5thr : iul_thr m R5).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R5 upd_ne; [| regne]. exact (HR4thr c Hcs N2 N8 N9 N18). }
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x14) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x16)) by pcw.
    iEval (rewrite Hpp16) in "Hpc".
    (* ===== +0x16 jal ra,holdingsleep ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iunlock + 0x16)) Rra
              (mword_of_int 3406 : mword 21) R5 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi16").
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (R6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iunlock + 0x16) : mword 64) 4)]> R5).
    assert (Htgths : add_vec (mword_of_int (KernelSyms.iunlock + 0x16) : mword 64)
                       (sign_extend' 64 (mword_of_int 3406 : mword 21))
                     = mword_of_int KernelSyms.holdingsleep) by pcw.
    iEval (rewrite Htgths) in "Hpc".
    assert (HR6a0 : R6 !!! Regidx Ra0 = i_lock ip)
      by (rewrite /R6 upd_ne; [exact HR5a0 | nz]).
    assert (HR6s2 : R6 !!! Regidx Rs2 = i_lock ip)
      by (rewrite /R6 upd_ne; [exact HR5s2 | nz]).
    assert (HR6s1 : R6 !!! Regidx Rs1 = ip)
      by (rewrite /R6 upd_ne; [exact HR5s1 | nz]).
    assert (HR6sp : iul_sp m R6)
      by (rewrite /iul_sp /R6 upd_ne; [exact HR5sp | nz]).
    assert (HR6ra : R6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iunlock + 0x16) : mword 64) 4)
      by (rewrite /R6; apply upd_eq).
    assert (HR6thr : iul_thr m R6).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R6 upd_ne; [| regne]. exact (HR5thr c Hcs N2 N8 N9 N18). }
   iDestruct (cpu_own_transport CID CID11 0%nat eb p b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (CIDa := CID) (CIDb := CID11) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (HS.wp_holdingsleep_gen_sconf (dq := dq) gil gisl "inode"%string
              (ic_tok cn k) (slh_tok (icfg_isl k)) s R6 p pidv (K - 4)%nat eb b lks
              ltac:(lia)
              Hfresh
              with "Hcg Hcnt Htext Hpc [] Hstok [Hpid] Hppid").
    all: try lkbelow.
    { iEval (rewrite HR6a0). iExact "Hslk". }
    { iEval (rewrite HR6a0). iExact "Hpid". }
    iIntros (CID12 Hq12 mH) "%Hhs Hcg Hcnt Hpc Hstok Hpid Hppid".
    destruct Hhs as [Hcs1 Hha0].
    iEval (rewrite HR6a0) in "Hpid".
    assert (Hpc1a : ret_pc (R6 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.iunlock + 0x1a)) by (rewrite HR6ra; pcw).
    iEval (rewrite Hpc1a) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmHs1 : mH !!! Regidx Rs1 = ip)
      by (rewrite (callee_saved_lookup Hcs1_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HR6s1).
    assert (HmHs2 : mH !!! Regidx Rs2 = i_lock ip)
      by (rewrite (callee_saved_lookup Hcs1_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HR6s2).
    assert (HmHsp : iul_sp m mH).
    { rewrite /iul_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR6sp. }
    assert (HmHthr : iul_thr m mH).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HR6thr c Hcs N2 N8 N9 N18). }
    (* ===== +0x1a c.beqz a0 : a0 = 1, the panic arm is DEAD ===== *)
    iPoseProof (iui2_1a with "Htext") as "Hi1a".
    iPoseProof (iui2_1c with "Htext") as "Hi1c".
    iPoseProof (iui2_1e with "Htext") as "Hi1e".
    iPoseProof (iui2_22 with "Htext") as "Hi22".
    iPoseProof (iui2_24 with "Htext") as "Hi24".
    assert (Hbeqz : eq_vec (mH !!! Regidx Ra0 : mword 64) (zero_reg : mword 64) = false)
      by (rewrite Hha0; vm_compute; reflexivity).
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.iunlock + 0x1a))
              (mword_of_int 13 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              mH (K - 4)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; exact Hbeqz) with "Hcg Hpc Hi1a").
    iIntros (CID13 Hq13) "Hcg Hpc".
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x1a) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== +0x1c c.lw a5,8(s1) : a5 := ip->ref, HOLDING NOTHING.
       The holder deposited its whole credential at ilock's checkout, so it
       BORROWS from the escrow's checked-out arm for the duration of this
       single atomic update -- [ic_open_out], refuting the other two arms
       with the FULL valid cell it is carrying (§13.1d).  What it borrows is
       the arm's LIVENESS SLICE, which BOTH deposit shapes carry (§14.8): the
       deposit here is a SHARE and has no count fragment at all, so the read
       goes through [iref_live_load_au] rather than [iref_load_au]. ===== *)
    assert (Hrefadr : add_vec (rget mH Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                      = i_ref ip).
    { rgne. rewrite HmHs1. reflexivity. }
    (* THE ADDRESS CLAIM, READ OFF THE CELL ITSELF.  The per-node form takes
       [WpSconfMem.wordw_claim] beside the (linear) atomic update, so it has
       to arrive first.  Both accessors this read uses RESTORE, so one peek
       -- the escrow's checked-out arm, then the itable's liveness read --
       hands out the ref word's own points-to; [wordw_claim_of] reads the
       claim off it and the peek closes with everything put back.  The claim
       is persistent, so it survives the close. *)
    iApply fupd_wp.
    iInv "Hesc" as ">Hbodyp" "Hclosep".
    iDestruct (ic_open_out cn gfs gi cov logstart k (DepShr s dev inum g) g true
                 eq_refl with "Hbodyp Hvalid Hdep")
      as "(Hvalid & Hdep & Hborp)".
    iDestruct "Hborp" as (sbp) "[Hlvp Hbbackp]".
    iMod (iref_live_load_au (⊤ ∖ ↑icEscN) k sbp
            ltac:(solve_ndisj) Hk with "Hitbl Hlvp") as (vp) "[Hcellp Hclp]".
    iDestruct (wordw_claim_of (KTR := KT0) 4 (i_ref (ientry k)) (DfracOwn 1) vp
                 ltac:(lia) with "Hcellp") as "#Hclaim0".
    iMod ("Hclp" with "Hcellp") as "[%Hbp Hlvp]".
    iMod ("Hclosep" with "[Hbbackp Hlvp]") as "_".
    { iNext. iApply ("Hbbackp" with "Hlvp"). }
    iModIntro.
    iApply (wp_lw_au_s_sconf true (mword_of_int (KernelSyms.iunlock + 0x1c)) Ra5 Rs1
              (mword_of_int 8 : mword 12) mH (K - 4)%nat
              (fun v => (⌜0 < bv_unsigned v < 2 ^ 31⌝ ∗
                         i_valid (ientry k) ↦₄ valid_word true ∗
                         ic_deposit cn k (DepShr s dev inum g))%I)
              (⊤ ∖ ↑minstretN ∖ ↑icEscN ∖ ↑icacheN) b
              ltac:(nz) ltac:(rdok) ltac:(solve_ndisj)
              with "Hcg Hpc Hi1c [] [Hvalid Hdep]").
    { rewrite Hrefadr Hipe. iExact "Hclaim0". }
    { rewrite Hrefadr Hipe.
      iInv "Hesc" as ">Hbody" "Hclose".
      (* IVd: the borrow names this holder's OWN descriptor half, which is
         what rules out [ic_out]'s frozen alternative -- the free path's
         window, which parks its live mass in [islot2] and deposits
         a [DepFrz], so there would be no slice to borrow. *)
      iDestruct (ic_open_out cn gfs gi cov logstart k (DepShr s dev inum g) g true
                   eq_refl with "Hbody Hvalid Hdep")
        as "(Hvalid & Hdep & Hbor)".
      iDestruct "Hbor" as (sb) "[Hlv Hbback]".
      iMod (iref_live_load_au (⊤ ∖ ↑minstretN ∖ ↑icEscN) k sb
              ltac:(solve_ndisj) Hk with "Hitbl Hlv") as (v) "[Hcell Hcl]".
      iModIntro. iExists v. iFrame "Hcell". iIntros "Hcell".
      iMod ("Hcl" with "Hcell") as "[%Hb Hlv]".
      iMod ("Hclose" with "[Hbback Hlv]") as "_".
      { iNext. iApply ("Hbback" with "Hlv"). }
      iModIntro. iFrame "Hvalid Hdep". iPureIntro. exact Hb. }
    iIntros (refv CID14 Hq14) "Hcg Hpc (%Href & Hvalid & Hdep)".
    set (R7 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 refv)]> mH).
    assert (HR7a5 : R7 !!! Regidx Ra5 = (sign_extend' 64 refv : mword 64))
      by (rewrite /R7; apply upd_eq).
    assert (HR7s2 : R7 !!! Regidx Rs2 = i_lock ip)
      by (rewrite /R7 upd_ne; [exact HmHs2 | nz]).
    assert (HR7sp : iul_sp m R7)
      by (rewrite /iul_sp /R7 upd_ne; [exact HmHsp | nz]).
    assert (HR7thr : iul_thr m R7).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R7 upd_ne; [| regne]. exact (HmHthr c Hcs N2 N8 N9 N18). }
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x1c) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x1e)) by pcw.
    iEval (rewrite Hpp1e) in "Hpc".
    (* ===== +0x1e bge x0,a5 : DEAD panic arm, ref >= 1 ===== *)
    iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.iunlock + 0x1e))
              (mword_of_int 22 : mword 13) Ra5 R7 (K - 4)%nat b ltac:(nz)
              ltac:(rgne; rewrite HR7a5; exact (inode_ref_spos refv Href))
              with "Hcg Hpc Hi1e").
    iIntros (CID15 Hq15) "Hcg Hpc".
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x1e) : mword 64) 4
                    = mword_of_int (KernelSyms.iunlock + 0x22)) by pcw.
    iEval (rewrite Hpp22) in "Hpc".
    (* ===== +0x22 c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iunlock + 0x22)) Ra0 Rs2
              R7 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi22").
    iIntros (CID16 Hq16) "Hcg Hpc".
    set (R8 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R7 Rs2))]> R7).
    assert (HR8a0 : R8 !!! Regidx Ra0 = i_lock ip).
    { rewrite /R8 upd_eq. rgne. rewrite HR7s2. apply add_vec_zero_l. }
    assert (HR8sp : iul_sp m R8)
      by (rewrite /iul_sp /R8 upd_ne; [exact HR7sp | nz]).
    assert (HR8thr : iul_thr m R8).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R8 upd_ne; [| regne]. exact (HR7thr c Hcs N2 N8 N9 N18). }
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x24)) by pcw.
    iEval (rewrite Hpp24) in "Hpc".
    (* ===== +0x24 jal ra,releasesleep ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iunlock + 0x24)) Rra
              (mword_of_int 3336 : mword 21) R8 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi24").
    iIntros (CID17 Hq17) "Hcg Hpc".
    set (R9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iunlock + 0x24) : mword 64) 4)]> R8).
    assert (Htgtrs : add_vec (mword_of_int (KernelSyms.iunlock + 0x24) : mword 64)
                       (sign_extend' 64 (mword_of_int 3336 : mword 21))
                     = mword_of_int KernelSyms.releasesleep) by pcw.
    iEval (rewrite Htgtrs) in "Hpc".
    assert (HR9a0 : R9 !!! Regidx Ra0 = i_lock ip)
      by (rewrite /R9 upd_ne; [exact HR8a0 | nz]).
    assert (HR9sp : iul_sp m R9)
      by (rewrite /iul_sp /R9 upd_ne; [exact HR8sp | nz]).
    assert (HR9ra : R9 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iunlock + 0x24) : mword 64) 4)
      by (rewrite /R9; apply upd_eq).
    assert (HR9thr : iul_thr m R9).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R9 upd_ne; [| regne]. exact (HR8thr c Hcs N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID12 CID17 0%nat eb p b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (CIDa := CID11) (CIDb := CID17) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    (* THE PARK: one mask-balanced opening of the escrow puts the whole
       checked-out bundle back and takes the CHECKOUT TOKEN -- which is all
       the sleeplock protects now -- and the caller's reference out. *)
    iApply fupd_wp.
    (* THE PARKED PAYLOAD, AND ITS TOKEN (iclaim-ledger.md §3.9).
       [IcacheEscrow.ic_payload] is the [_np] bundle plus the inum's
       [ifreeze_off]; the token is the one [SpecIlock]'s post handed this
       holder, threaded through its critical section untouched, and putting
       it back is what re-establishes the parked arm's A-custody conjunct. *)
    iAssert (ic_payload gfs gi cov logstart k inum g true)%I
      with "[Hlk Hfrz]" as "Hpay".
    { iApply (ic_payload_join with "[Hlk] Hfrz").
      rewrite /ic_payload_np. iExists dn', bm'.
      iSplitL "Hlk"; [iExact "Hlk" | iExact "Hshot"]. }
    iInv "Hesc" as ">Hbody" "Hclose".
    iMod (ic_swap_park cn gfs gi cov logstart k (DepShr s dev inum g) g
                 true dev inum eq_refl with "Hbody Hdep Hidev Hinumc Hvalid Hpay")
      as "(Hbody & Htok & Hrefout)".
    iMod ("Hclose" with "[Hbody]") as "_"; [iNext; iExact "Hbody" |].
    iModIntro.
    (* the descriptor pins the fraction and the identity: the share comes back
       at exactly [s], with no existential (§14.8) *)
    iDestruct "Hrefout" as "[_ Href]".
    iApply (RS.wp_releasesleep_gen_sconf gs gil gisl "inode"%string
              (ic_tok cn k) (slh_tok (icfg_isl k)) s R9 pidv p (K - 4)%nat eb b lks
              ltac:(lia)
              Hfresh
              with "Hcg Hcnt Htext Hpc [] Hstok [Hpid] Htok Hprocs").
    all: try lkbelow.
    { iEval (rewrite HR9a0). iExact "Hslk". }
    { iEval (rewrite HR9a0). iExact "Hpid". }
    (* the lock hands the deposit back at the holder's OWN fraction, which is
       what rebuilds the caller's share: the arm kept the other two slices. *)
    iIntros (CID18 Hq18 mR) "%Hcs2 Hcg Hcnt Hpc Hslh".
    (* the generation is NOT forgotten here any more -- see [SpecIunlock]'s
       post.  What the arm handed back is already at [g]. *)
    iAssert (inode_shr_gen k s dev inum g) with "[Href Hslh]" as "Href".
    { rewrite inode_shr_gen_bare_split. iFrame. }
    assert (Hpc28 : ret_pc (R9 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.iunlock + 0x28)) by (rewrite HR9ra; pcw).
    iEval (rewrite Hpc28) in "Hpc".
    pose proof Hcs2 as Hcs2_cs.
    assert (HmRsp : iul_sp m mR).
    { rewrite /iul_sp
        (callee_saved_lookup Hcs2_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR9sp. }
    assert (HmRthr : iul_thr m mR).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs2_cs c Hcs).
      exact (HR9thr c Hcs N2 N8 N9 N18). }
    (* ===== +0x28 .. +0x2e : the four restores ===== *)
    iPoseProof (iui2_28 with "Htext") as "Hi28".
    iPoseProof (iui2_2a with "Htext") as "Hi2a".
    iPoseProof (iui2_2c with "Htext") as "Hi2c".
    iPoseProof (iui2_2e with "Htext") as "Hi2e".
    iPoseProof (iui2_30 with "Htext") as "Hi30".
    iPoseProof (iui2_32 with "Htext") as "Hi32".
    rewrite /iul_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4)".
    assert (Hc1 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc2 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc3 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc4 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iunlock + 0x28)) (mword_of_int 3 : mword 6) Rra
              mR (K - 4)%nat (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi28 [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID19 Hq19) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> mR).
    assert (HP1sp : iul_sp m P1)
      by (rewrite /iul_sp /P1 upd_ne; [exact HmRsp | nz]).
    assert (HP1thr : iul_thr m P1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P1 upd_ne; [| regne]. exact (HmRthr c Hcs N2 N8 N9 N18). }
    assert (HP1ra : P1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x28) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x2a)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iunlock + 0x2a)) (mword_of_int 2 : mword 6) Rs0
              P1 (K - 4)%nat (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi2a [Hf2]").
    { iEval (rewrite HP1sp -HmRsp Hc2). iExact "Hf2". }
    iIntros (CID20 Hq20) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -HmRsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : iul_sp m P2)
      by (rewrite /iul_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : iul_thr m P2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P2 upd_ne; [| regne]. exact (HP1thr c Hcs N2 N8 N9 N18). }
    assert (HP2ra : P2 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x2a) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x2c)) by pcw.
    iEval (rewrite Hpp2c) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iunlock + 0x2c)) (mword_of_int 1 : mword 6) Rs1
              P2 (K - 4)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi2c [Hf3]").
    { iEval (rewrite HP2sp -HmRsp Hc3). iExact "Hf3". }
    iIntros (CID21 Hq21) "Hcg Hpc Hf3".
    iEval (rewrite HP2sp -HmRsp Hc3) in "Hf3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : iul_sp m P3)
      by (rewrite /iul_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (HP3thr : iul_thr m P3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P3 upd_ne; [| regne]. exact (HP2thr c Hcs N2 N8 N9 N18). }
    assert (HP3ra : P3 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x2c) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x2e)) by pcw.
    iEval (rewrite Hpp2e) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iunlock + 0x2e)) (mword_of_int 0 : mword 6) Rs2
              P3 (K - 4)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi2e [Hf4]").
    { iEval (rewrite HP3sp -HmRsp Hc4). iExact "Hf4". }
    iIntros (CID22 Hq22) "Hcg Hpc Hf4".
    iEval (rewrite HP3sp -HmRsp Hc4) in "Hf4".
    set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    assert (HP4sp : iul_sp m P4)
      by (rewrite /iul_sp /P4 upd_ne; [exact HP3sp | nz]).
    assert (HP4thr : iul_thr m P4).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P4 upd_ne; [| regne]. exact (HP3thr c Hcs N2 N8 N9 N18). }
    assert (HP4ra : P4 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3ra | nz]).
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x2e) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x30)) by pcw.
    iEval (rewrite Hpp30) in "Hpc".
    (* ===== +0x30 c.addi16sp sp,32 : pop ===== *)
    assert (Hwv : add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP4sp. apply bv_eq.
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
    assert (Hpop : (P4 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HP4sp. unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iAssert (stack_own (KTR := KT1) (m !!! Regidx csp_rs1 : mword 64) 4)
      with "[Hf1 Hf2 Hf3 Hf4]" as "Hstk".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1" |].
      iSplitL "Hf2"; [iExists _; iExact "Hf2" |].
      iSplitL "Hf3"; [iExists _; iExact "Hf3" |].
      iSplitL "Hf4"; [iExists _; iExact "Hf4" |].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.iunlock + 0x30))
              (mword_of_int 2 : mword 6) P4 (K - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi30 Hstk").
    iIntros (CID23 Hq23) "Hcg Hpc".
    set (P5 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P4).
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.iunlock + 0x30) : mword 64) 2
                    = mword_of_int (KernelSyms.iunlock + 0x32)) by pcw.
    iEval (rewrite Hpp32) in "Hpc".
    (* ===== +0x32 c.ret ===== *)
    assert (HP5ra : P5 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P5 upd_ne; [exact HP4ra | nz]).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.iunlock + 0x32)) Rra P5 K b ltac:(nz)
              with "Hcg Hpc Hi32").
    iIntros (CID24 Hq24) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P5 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP5ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (Csp : P5 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P5 upd_eq; exact Hwv).
    assert (Cs0 : P5 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_eq. reflexivity. }
    assert (Cs1 : P5 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_eq. reflexivity. }
    assert (Cs2 : P5 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_eq. reflexivity. }
    assert (Hfin : iul_thr m P5).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P5 upd_ne; [| regne]. exact (HP4thr c Hcs N2 N8 N9 N18). }
    assert (Cs3 : P5 !!! Regidx (mword_of_int 19 : mword 5)
                  = (m !!! Regidx (mword_of_int 19 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs4 : P5 !!! Regidx (mword_of_int 20 : mword 5)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs5 : P5 !!! Regidx (mword_of_int 21 : mword 5)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs6 : P5 !!! Regidx (mword_of_int 22 : mword 5)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs7 : P5 !!! Regidx (mword_of_int 23 : mword 5)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs8 : P5 !!! Regidx (mword_of_int 24 : mword 5)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs9 : P5 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs10 : P5 !!! Regidx (mword_of_int 26 : mword 5)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs11 : P5 !!! Regidx (mword_of_int 27 : mword 5)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    iDestruct (cpu_own_transport CID18 CID24 0%nat eb p b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    rewrite /iul_cont.
    iSpecialize ("Hcont" $! CID24 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! P5 with "[%] Hcg Hcnt Hpc Hppid Href").
    { unfold callee_saved. split_and!; assumption. }
  Qed.

End ProofIunlockMain.

End IunlockProof.
