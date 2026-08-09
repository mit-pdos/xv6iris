(* ProofItrunc.v -- itrunc's instruction chain.  The vocabulary it consumes
   (the map models, the freed-set arithmetic, the frame and the two loop
   states) is in ProofItruncParts.v; this file is about control flow.

   THE SHAPE.  A prologue, a twelve-iteration direct loop, a test on
   [ip->addrs[NDIRECT]] that either falls straight through or takes the
   indirect arm, and a shared tail ([ip->size = 0]; iupdate; epilogue).  The
   indirect arm rejoins the tail by an explicit [j] at +0x92, which is why
   the tail is a lemma rather than a straight continuation of the fallthrough
   path: both predecessors need it.

   S4 IS SAVED CONDITIONALLY.  [sd s4,0(sp)] is at +0x50 and [ld s4,0(sp)]
   at +0x90, both INSIDE the indirect arm, so the direct-only path owns the
   sixth frame slot without ever giving it a value.  [it_frame]'s sixth
   conjunct is existential for exactly that reason. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile HartTp WpNext WpGpr.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs WpSmodeIntr.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import BufOwn.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfVc WpSconfBtype.
Require Import WpSmodeHalf.
Require Import ByteCursor ByteBuf.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import SchedCtx.
Require Import WpUart.
Require Import BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapEnc BitmapInv.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import SpecBread SpecBrelse SpecBfree SpecIupdate.
Require Import SpecItrunc.
Require Import ProofBmapParts.
Require Import ProofItruncParts.
Require Import CodeItrunc.
From Kernel Require KernelSyms.
Import Defs.

Local Open Scope Z_scope.

Module ItruncProof (BR : BREAD) (BF : BFREE) (BL : BRELSE) (IU : IUPDATE).

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac itidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].
Notation Rz := (mword_of_int 0 : mword 5).

Notation IT := KernelSyms.itrunc.

(* ===================================================================== *)
(*  The continuation: itrunc's postcondition, as a resource               *)
(* ===================================================================== *)
Section ItruncCont.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  Definition it_cont `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γ : log_names) (γfs : fs_names) (bn : bio_names)
      (cov : gset Z) (logstart bmapstart inodestart size : Z)
      (used : gset Z) (dev : mword 32)
      (ip : mword 64) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (ds : list dinode) (u : nat)
      (pidv : mword 32) (dq dqd dqn dqb dqs : dfrac) (j : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) : iProp Σ :=
    wp_next b (proc_addr j) (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf K b (proc_addr j) -∗
        cpu_own 0 true (proc_addr j) C b -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        running_claim j -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        i_dev ip ↦₄{dqd} dev -∗
        i_inum ip ↦₄{dqn} inum -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        inode_meta ip (di_trunc dn) -∗
        inode_map γfs ip bm_empty -∗
        inode_blocks γfs bm_empty (fun _ => replicate BSIZE (bv_0 8)) -∗
        bitmap_res γfs bmapstart cov logstart size (used ∖ bm_blocks bm) -∗
        fsblock γfs (IBLOCK inum inodestart)
                (diblk_bytes (<[islot inum := di_trunc dn]> ds)) -∗
        bslots bn 2 -∗
        (∃ u' : nat, ⌜(u <= u' <= S u)%nat⌝ ∗ log_op γ u') -∗
        WP (Loop : expr riscv_lang))%I.

End ItruncCont.

(* the register-threading invariants: the five registers the frame saves *)
Definition it_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

(* itrunc pushes with [c.addi16sp sp,-48] (iti_00), not with the
   [sign_extend' 12] shape bfree's [c.addi sp,sp,-32] produces, so the
   offset is spelled as the decoder spells it. *)
Definition it_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))).

(* the push really is -48 and the pop really is +48 -- checked against the
   decoder rather than assumed, since [caddi16sp_imm]'s bit scramble is
   exactly the kind of thing that silently disagrees *)
Lemma it_push_imm :
  bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))
               : mword 64) = 18446744073709551568.
Proof. vm_compute; reflexivity. Qed.

Lemma it_pop_imm :
  bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))
               : mword 64) = 48.
Proof. vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  THE TAIL: ip->size = 0, iupdate, and the six-slot epilogue            *)
(*                                                                        *)
(*  Reached from BOTH predecessors -- the direct-only fallthrough at       *)
(*  +0x36 and the indirect arm's [j] at +0x92 -- which is why it is a      *)
(*  lemma.  By the time control is here the inode names nothing: the map   *)
(*  is [bm_empty], every block it named is back in the pool, and the only  *)
(*  budget still owed is iupdate's one unit.                              *)
(* ===================================================================== *)
Section ItruncTail.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  Local Lemma it_tail `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart bmapstart inodestart size : Z) (dev : mword 32)
      (used : gset Z) (ip : mword 64) (inum : mword 32)
      (dn : dinode) (bm : blkmap) (ds : list dinode)
      (u : nat) (pidv : mword 32) (dq dqd dqn dqb dqs : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ) (b : bool) :
    (K_itrunc <= K)%nat ->
    log_geom_ok cov logstart ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    diblk_wf ds ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    it_sp m M ->
    it_thr m M ->
    M !!! Regidx Rs3 = ip ->
    sie_cap_gpr M (K - 6)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) C b -∗
    kernel_text -∗
    pc_is (mword_of_int (IT + 0x38) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv Φ γs -∗
    scheds_inv Φ γs -∗
    it_frame m -∗
    running_claim j -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    i_dev ip ↦₄{dqd} dev -∗
    i_inum ip ↦₄{dqn} inum -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    inode_meta ip dn -∗
    inode_map γfs ip bm_empty -∗
    inode_blocks γfs bm_empty (fun _ => replicate BSIZE (bv_0 8)) -∗
    bitmap_res γfs bmapstart cov logstart size (used ∖ bm_blocks bm) -∗
    fsblock γfs (IBLOCK inum inodestart) (diblk_bytes ds) -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots bn 2 -∗
    log_op γ (S u) -∗
    it_cont (CID0 := CID0) Φ γ γfs bn cov logstart bmapstart inodestart size
            used dev ip inum dn bm ds u pidv dq dqd dqn dqb dqs j m K C b -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hist Hicov Hilog Hdswf Hj Hgl Hsp Hthr Hs3.
    pose proof HK as HK'. unfold K_itrunc in HK'.
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hlctx #Hprocs #Hscheds Hframe
              Hrun Hppid Hidev Hinum Hsbb Hsbi Hmeta Hmap Hblks Hbmr
              Hfsb #Hdevi #Hdgeom #Hdlock Hsl Hop Hcont".
    iPoseProof (iti_38 with "Htext") as "Hi38".
    iPoseProof (iti_3c with "Htext") as "Hi3c".
    iPoseProof (iti_3e with "Htext") as "Hi3e".
    (* ===== +0x38 sw zero,76(s3) : ip->size = 0 ===== *)
    rewrite /inode_meta.
    iDestruct "Hmeta" as "(Hty & Hmaj & Hmin & Hnl & Hsz)".
    assert (Hsza : add_vec (rget M Rs3)
                     (sign_extend' 64 (mword_of_int 76 : mword 12))
                   = i_size ip).
    { rgne. rewrite Hs3. reflexivity. }
    iEval (rewrite -Hsza) in "Hsz".
    iApply (wp_sw_s_sconf Φ (mword_of_int (IT + 0x38)) Rz Rs3
              (mword_of_int 76 : mword 12) M (K - 6)%nat (di_size dn) b
              with "Hcg Hpc Hi38 Hsz").
    iIntros (CID1 Hq1) "Hcg Hpc Hsz".
    iEval (rewrite Hsza) in "Hsz".
    iDestruct (sie_cap_gpr_x0 M (K - 6)%nat b (proc_addr j) Rz
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
    (* stated at [bv_0 32], which is the form [di_trunc]'s size field takes;
       [mword_of_int 0] is equal but not syntactically so, and iFrame wants
       the match *)
    assert (Hz32 : trunc32 (rget M Rz) = (bv_0 32 : mword 32))
      by (rgne; rewrite Hx0; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hz32) in "Hsz".
    (* the five scalars are now the TRUNCATED record's *)
    iAssert (inode_meta ip (di_trunc dn))
      with "[Hty Hmaj Hmin Hnl Hsz]" as "Hmeta".
    { rewrite /inode_meta /di_trunc. cbn [di_type di_major di_minor di_nlink di_size].
      iFrame "Hty Hmaj Hmin Hnl Hsz". }
    assert (Hp3c : add_vec_int (mword_of_int (IT + 0x38) : mword 64) 4
                   = mword_of_int (IT + 0x3c)) by pcw.
    iEval (rewrite Hp3c) in "Hpc".
    (* ===== +0x3c mv a0,s3 ===== *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (IT + 0x3c)) Ra0 Rs3
              M (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3c").
    iIntros (CID2 Hq2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs3 : mword 64))]> M).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget M Rs3))]> M)
      with T0.
    (* c.mv lands its result through [add_vec zero_reg], which is the
       identity on 64-bit words *)
    assert (Hzl : forall x : mword 64, add_vec zero_reg x = x).
    { intros x. apply bv_eq. rewrite add_vec64_unsigned.
      assert (Hz : bv_unsigned (zero_reg : mword 64) = 0)
        by (vm_compute; reflexivity).
      rewrite Hz Z.add_0_l. apply bv_wrap_small, bv_unsigned_in_range. }
    assert (HT0a0 : T0 !!! Regidx Ra0 = ip)
      by (rewrite /T0 upd_eq Hzl; exact Hs3).
    assert (Hp3e : add_vec_int (mword_of_int (IT + 0x3c) : mword 64) 2
                   = mword_of_int (IT + 0x3e)) by pcw.
    iEval (rewrite Hp3e) in "Hpc".
    (* ===== +0x3e jal iupdate ===== *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (IT + 0x3e)) Rra
              (mword_of_int 2096672 : mword 21) T0 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi3e").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (T1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (IT + 0x3e) : mword 64) 4)]> T0).
    assert (Htgtiu : add_vec (mword_of_int (IT + 0x3e) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096672 : mword 21))
                     = mword_of_int KernelSyms.iupdate) by pcw.
    iEval (rewrite Htgtiu) in "Hpc".
    assert (HT1a0 : T1 !!! Regidx Ra0 = ip)
      by (rewrite /T1 upd_ne; [exact HT0a0 | nz]).
    assert (HT1ra : T1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (IT + 0x3e) : mword 64) 4)
      by (rewrite /T1; apply upd_eq).
    assert (HT1sp : it_sp m T1).
    { rewrite /it_sp /T1 upd_ne; [| nz]. rewrite /T0 upd_ne; [| nz]. exact Hsp. }
    assert (HT1thr : it_thr m T1).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /T1 upd_ne; [| regne]. rewrite /T0 upd_ne; [| regne].
      exact (Hthr c Hcs N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID0 CID3 0 true (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (CIDa := CID0) (CIDb := CID3) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKiu : (K_iupdate <= K - 6)%nat) by (unfold K_iupdate; lia).
    assert (Hdirlen : length (bm_dir bm_empty) = NDIRECT)
      by (rewrite /bm_empty; cbn [bm_dir]; apply length_replicate).
    iApply (IU.wp_iupdate_sconf Φ γs j γl γu γd γk pd pav pu bn γ γfs
              cov logstart inodestart dev ip inum (di_trunc dn) bm_empty ds u
              pidv dq dqd dqn dqs T1 (K - 6)%nat true C b
              HKiu Hgeom Hist Hicov Hilog Hdswf (di_trunc_addrs dn) Hdirlen
              Hj Hgl HT1a0 eq_refl
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hidev Hinum Hmeta Hmap
                    Hsbi Hfsb Hppid Hprocs Hscheds Hrun Hdevi Hdgeom
                    Hdlock Hsl Hop").
    iIntros (CID4 Hq4 mI) "%Hcs1 Hcg Hcnt Hpc Hrun Hppid Hidev Hinum
                           Hmeta Hmap Hsbi Hfsb Hsl Hop".
    assert (Hpc42 : ret_pc (T1 !!! Regidx Rra : mword 64)
                    = mword_of_int (IT + 0x42)) by (rewrite HT1ra; pcw).
    iEval (rewrite Hpc42) in "Hpc".
    (* the callee preserved everything the frame cares about *)
    pose proof Hcs1 as Hcs1'.
    assert (HmIsp : it_sp m mI).
    { rewrite /it_sp
        (callee_saved_lookup Hcs1' csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HT1sp. }
    assert (HmIthr : it_thr m mI).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite (callee_saved_lookup Hcs1' c Hcs).
      exact (HT1thr c Hcs N2 N8 N9 N18 N19). }
    (* ===== the epilogue: five c.ldsp, the +48 pop, and c.ret ===== *)
    iPoseProof (iti_42 with "Htext") as "Hi42".
    iPoseProof (iti_44 with "Htext") as "Hi44".
    iPoseProof (iti_46 with "Htext") as "Hi46".
    iPoseProof (iti_48 with "Htext") as "Hi48".
    iPoseProof (iti_4a with "Htext") as "Hi4a".
    iPoseProof (iti_4c with "Htext") as "Hi4c".
    iPoseProof (iti_4e with "Htext") as "Hi4e".
    rewrite /it_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6)".
    (* the five saved slots, in the c.ldsp spelling.  Slot k sits at
       (6-k)*8 above the pushed sp. *)
    assert (Hc1 : add_vec (mI !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HmIsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc2 : add_vec (mI !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HmIsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc3 : add_vec (mI !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HmIsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc4 : add_vec (mI !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HmIsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc5 : add_vec (mI !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite HmIsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    (* +0x42 c.ldsp ra,40(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (IT + 0x42))
              (mword_of_int 5 : mword 6) Rra
              mI (K - 6)%nat (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi42 [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID5 Hq5) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> mI).
    assert (HP1sp : it_sp m P1)
      by (rewrite /it_sp /P1 upd_ne; [exact HmIsp | nz]).
    assert (HP1thr : it_thr m P1).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P1 upd_ne; [| regne]. exact (HmIthr c Hcs N2 N8 N9 N18 N19). }
    assert (HP1ra : P1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1spq : P1 !!! Regidx csp_rs1 = (mI !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P1 upd_ne; [reflexivity | nz]).
    assert (Hp44 : add_vec_int (mword_of_int (IT + 0x42) : mword 64) 2
                   = mword_of_int (IT + 0x44)) by pcw.
    iEval (rewrite Hp44) in "Hpc".
    (* +0x44 c.ldsp s0,32(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (IT + 0x44))
              (mword_of_int 4 : mword 6) Rs0
              P1 (K - 6)%nat (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi44 [Hf2]").
    { iEval (rewrite HP1spq Hc2). iExact "Hf2". }
    iIntros (CID6 Hq6) "Hcg Hpc Hf2".
    iEval (rewrite HP1spq Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : it_sp m P2)
      by (rewrite /it_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : it_thr m P2).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P2 upd_ne; [| regne]. exact (HP1thr c Hcs N2 N8 N9 N18 N19). }
    assert (HP2ra : P2 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (HP2spq : P2 !!! Regidx csp_rs1 = (mI !!! Regidx csp_rs1 : mword 64)).
    { rewrite /P2 upd_ne; [| nz]. rewrite /P1 upd_ne; [reflexivity | nz]. }
    assert (Hp46 : add_vec_int (mword_of_int (IT + 0x44) : mword 64) 2
                   = mword_of_int (IT + 0x46)) by pcw.
    iEval (rewrite Hp46) in "Hpc".
    (* +0x46 c.ldsp s1,24(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (IT + 0x46))
              (mword_of_int 3 : mword 6) Rs1
              P2 (K - 6)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi46 [Hf3]").
    { iEval (rewrite HP2spq Hc3). iExact "Hf3". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf3".
    iEval (rewrite HP2spq Hc3) in "Hf3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : it_sp m P3)
      by (rewrite /it_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (HP3thr : it_thr m P3).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P3 upd_ne; [| regne]. exact (HP2thr c Hcs N2 N8 N9 N18 N19). }
    assert (HP3ra : P3 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    assert (HP3spq : P3 !!! Regidx csp_rs1 = (mI !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2spq | nz]).
    assert (Hp48 : add_vec_int (mword_of_int (IT + 0x46) : mword 64) 2
                   = mword_of_int (IT + 0x48)) by pcw.
    iEval (rewrite Hp48) in "Hpc".
    (* +0x48 c.ldsp s2,16(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (IT + 0x48))
              (mword_of_int 2 : mword 6) Rs2
              P3 (K - 6)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi48 [Hf4]").
    { iEval (rewrite HP3spq Hc4). iExact "Hf4". }
    iIntros (CID8 Hq8) "Hcg Hpc Hf4".
    iEval (rewrite HP3spq Hc4) in "Hf4".
    set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    assert (HP4sp : it_sp m P4)
      by (rewrite /it_sp /P4 upd_ne; [exact HP3sp | nz]).
    assert (HP4thr : it_thr m P4).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P4 upd_ne; [| regne]. exact (HP3thr c Hcs N2 N8 N9 N18 N19). }
    assert (HP4ra : P4 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3ra | nz]).
    assert (HP4spq : P4 !!! Regidx csp_rs1 = (mI !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3spq | nz]).
    assert (Hp4a : add_vec_int (mword_of_int (IT + 0x48) : mword 64) 2
                   = mword_of_int (IT + 0x4a)) by pcw.
    iEval (rewrite Hp4a) in "Hpc".
    (* +0x4a c.ldsp s3,8(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (IT + 0x4a))
              (mword_of_int 1 : mword 6) Rs3
              P4 (K - 6)%nat (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi4a [Hf5]").
    { iEval (rewrite HP4spq Hc5). iExact "Hf5". }
    iIntros (CID9 Hq9) "Hcg Hpc Hf5".
    iEval (rewrite HP4spq Hc5) in "Hf5".
    set (P5 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> P4).
    assert (HP5sp : it_sp m P5)
      by (rewrite /it_sp /P5 upd_ne; [exact HP4sp | nz]).
    assert (HP5thr : it_thr m P5).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P5 upd_ne; [| regne]. exact (HP4thr c Hcs N2 N8 N9 N18 N19). }
    assert (HP5ra : P5 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P5 upd_ne; [exact HP4ra | nz]).
    assert (Hp4c : add_vec_int (mword_of_int (IT + 0x4a) : mword 64) 2
                   = mword_of_int (IT + 0x4c)) by pcw.
    iEval (rewrite Hp4c) in "Hpc".
    (* ===== +0x4c c.addi16sp sp,48 : the pop ===== *)
    assert (HP5spq : P5 !!! Regidx csp_rs1 = (mI !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P5 upd_ne; [exact HP4spq | nz]).
    assert (Hwv : add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP5sp. apply bv_eq.
      rewrite !add_vec64_unsigned bv_wrap_add_idemp_l.
      rewrite it_push_imm it_pop_imm.
      replace (bv_unsigned (m !!! Regidx csp_rs1 : mword 64)
                 + 18446744073709551568 + 48)
        with (bv_unsigned (m !!! Regidx csp_rs1 : mword 64)
                 + 18446744073709551616) by ring.
      rewrite -bv_wrap_add_idemp_r.
      assert (Hm0 : bv_wrap 64 18446744073709551616 = 0)
        by (vm_compute; reflexivity).
      rewrite Hm0 Z.add_0_r.
      apply bv_wrap_small. apply bv_unsigned_in_range. }
    assert (Hpop : (P5 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hwv HP5sp. unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iAssert (stack_own (m !!! Regidx csp_rs1 : mword 64) 6)
      with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6]" as "Hstk".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1" |].
      iSplitL "Hf2"; [iExists _; iExact "Hf2" |].
      iSplitL "Hf3"; [iExists _; iExact "Hf3" |].
      iSplitL "Hf4"; [iExists _; iExact "Hf4" |].
      iSplitL "Hf5"; [iExists _; iExact "Hf5" |].
      iSplitL "Hf6"; [iExact "Hf6" |].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (IT + 0x4c))
              (mword_of_int 3 : mword 6) P5 (K - 6)%nat 6 b Hpop
              with "Hcg Hpc Hi4c Hstk").
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (P6 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> P5).
    assert (Hnk : ((K - 6) + 6)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hp4e : add_vec_int (mword_of_int (IT + 0x4c) : mword 64) 2
                   = mword_of_int (IT + 0x4e)) by pcw.
    iEval (rewrite Hp4e) in "Hpc".
    (* ===== +0x4e c.ret ===== *)
    assert (HP6ra : P6 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P6 upd_ne; [exact HP5ra | nz]).
    iApply (wp_cret_s_sconf Φ (mword_of_int (IT + 0x4e)) Rra P6 K b
              ltac:(nz) with "Hcg Hpc Hi4e").
    iIntros (CID11 Hq11) "Hcg Hpc".
    assert (Hretf : ret_pc (P6 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP6ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== hand everything to the caller ===== *)
    iDestruct (cpu_own_transport CID4 CID11 0 true (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    rewrite /it_cont.
    iSpecialize ("Hcont" $! CID11 with "[%]"); [wp_next_chain|].
    (* the five saved registers are back at the caller's values, sp is
       popped, and everything else rode through on [it_thr] -- including
       s4, which the indirect arm restores at +0x90 BEFORE rejoining here *)
    assert (Csp : P6 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P6 upd_eq; exact Hwv).
    assert (Cs0 : P6 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_eq. reflexivity. }
    assert (Cs1 : P6 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_eq. reflexivity. }
    assert (Cs2 : P6 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_eq. reflexivity. }
    assert (Cs3 : P6 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_eq. reflexivity. }
    assert (Hfin : it_thr m P6).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P6 upd_ne; [| regne]. exact (HP5thr c Hcs N2 N8 N9 N18 N19). }
    assert (Cs4 : P6 !!! Regidx (mword_of_int 20 : mword 5)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; itidx).
    assert (Cs5 : P6 !!! Regidx (mword_of_int 21 : mword 5)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; itidx).
    assert (Cs6 : P6 !!! Regidx (mword_of_int 22 : mword 5)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; itidx).
    assert (Cs7 : P6 !!! Regidx (mword_of_int 23 : mword 5)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; itidx).
    assert (Cs8 : P6 !!! Regidx (mword_of_int 24 : mword 5)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; itidx).
    assert (Cs9 : P6 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; itidx).
    assert (Cs10 : P6 !!! Regidx (mword_of_int 26 : mword 5)
                   = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; itidx).
    assert (Cs11 : P6 !!! Regidx (mword_of_int 27 : mword 5)
                   = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; itidx).
    iApply ("Hcont" $! P6 with "[%] Hcg Hcnt Hpc Hrun Hppid Hidev Hinum
                                 Hsbb Hsbi Hmeta Hmap Hblks Hbmr Hfsb Hsl [Hop]").
    { unfold callee_saved. split_and!; assumption. }
    { iExists u. iSplitR; [iPureIntro; lia|]. iExact "Hop". }
  Qed.

End ItruncTail.

(* ===================================================================== *)
(*  THE DIRECT LOOP: ip->addrs[0 .. NDIRECT)                              *)
(*                                                                        *)
(*  A ROTATED loop.  The [j] at +0x18 jumps PAST the bounds check straight *)
(*  into the body test at +0x20, so the first iteration never runs [beq]   *)
(*  and the induction has to enter at +0x20 with k = 0 already known good. *)
(*  The [beq s1,s2] at +0x1c guards only the SUBSEQUENT iterations.        *)
(*                                                                        *)
(*  Fuel induction over NDIRECT - k, the lw_scan idiom.                    *)
(* ===================================================================== *)
Section ItruncDLoop.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  (* what the loop hands on at +0x32, once every direct entry is gone *)
  Definition it_dexit `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γ : log_names) (γfs : fs_names) (bn : bio_names)
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z)
      (dev : mword 32) (ip : mword 64) (bm : blkmap)
      (data : nat -> list (bv 8))
      (pidv : mword 32) (dq dqd dqb : dfrac) (j : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) : iProp Σ :=
    wp_next b (proc_addr j) (fun (CID : CpuId) =>
      ∀ Mx : regfile,
        ⌜it_sp m Mx⌝ -∗ ⌜it_thr m Mx⌝ -∗ ⌜Mx !!! Regidx Rs3 = ip⌝ -∗
        sie_cap_gpr Mx (K - 6)%nat b (proc_addr j) -∗
        cpu_own 0 true (proc_addr j) C b -∗
        pc_is (mword_of_int (IT + 0x32) : mword 64) -∗
        running_claim j -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        i_dev ip ↦₄{dqd} dev -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        bslots bn 2 -∗
        it_dir_state γ γfs ip bm data cov logstart bmapstart size used bn
                     NDIRECT -∗
        WP (Loop : expr riscv_lang))%I.

  Local Lemma it_dloop `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γs : list gname) (jx : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart bmapstart size : Z) (dev : mword 32)
      (used : gset Z) (ip : mword 64) (bm : blkmap)
      (data : nat -> list (bv 8))
      (pidv : mword 32) (dq dqd dqb : dfrac)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) (fuel : nat) :
    (K_itrunc <= K)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    blkmap_wf cov logstart bm ->
    (forall i : nat, (i <= MAXFILE)%nat -> bv_unsigned (bm_slot bm i) <> 0 ->
       bv_unsigned (bm_slot bm i) < size) ->
    (forall i : nat, length (data i) = BSIZE) ->
    (jx < NPROC)%nat ->
    γs !! jx = Some γl ->
    forall (k : nat) (M : regfile),
    (k < NDIRECT)%nat ->
    (NDIRECT - k <= fuel)%nat ->
    it_sp m M ->
    it_thr m M ->
    M !!! Regidx Rs1 = i_addr ip k ->
    M !!! Regidx Rs2 = i_addr ip NDIRECT ->
    M !!! Regidx Rs3 = ip ->
    sie_cap_gpr M (K - 6)%nat b (proc_addr jx) -∗
    cpu_own 0 true (proc_addr jx) C b -∗
    kernel_text -∗
    pc_is (mword_of_int (IT + 0x20) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv Φ γs -∗
    scheds_inv Φ γs -∗
    running_claim jx -∗
    p_pid (proc_addr jx) ↦₄{dq} pidv -∗
    i_dev ip ↦₄{dqd} dev -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots bn 2 -∗
    it_dir_state γ γfs ip bm data cov logstart bmapstart size used bn k -∗
    it_dexit (CID0 := CID0) Φ γ γfs bn cov logstart bmapstart size used dev
             ip bm data pidv dq dqd dqb jx m K C b -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hsize Hbm0 Hbmcov Hbmlog Hwf Hrange Hblen Hj Hgl.
    (* REVERT CID0 BEFORE THE INDUCTION (the ProofWritei.wi_loop idiom).
       At generic [b] the instruction chain really does advance the CID, so
       an IH pinned to the entry CID is unusable by the time the loop comes
       round; generalising it is what makes the recursive call typecheck.
       lw_scan gets away without this only because its loop runs at
       [b = false], where wp_next collapses and the CID never moves. *)
    revert CID0.
    induction fuel as [|fuel IH];
      intros CID0 k M Hk Hfuel Hsp Hthr Hs1 Hs2 Hs3;
      [ exfalso; unfold NDIRECT in Hk, Hfuel; lia |].
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hlctx #Hprocs #Hscheds Hrun Hppid Hidev Hsbb #Hdevi #Hdgeom #Hdlock Hsl Hst Hexit".
    pose proof HK as HK'. unfold K_itrunc in HK'.
    pose proof (blkmap_wf_dir_len _ _ _ Hwf) as Hdirlen.
    assert (Hzlen : length (bm_dir (bm_dir_zeroed bm k)) = NDIRECT)
      by (rewrite bm_dir_zeroed_len; [exact Hdirlen | lia]).
    iDestruct (it_dir_state_open with "Hst") as "(Hmap & Hblks & Hbmr & Hpaid)".
    (* the cursor cell: at index k the map still holds the ORIGINAL entry *)
    iDestruct (inode_map_dir_acc γfs ip (bm_dir_zeroed bm k) k Hzlen
                 ltac:(exact Hk) with "Hmap") as "[Hcell Hmapback]".
    assert (Hcur : blkmap_get (bm_dir_zeroed bm k) k = bm_dir bm !!! k).
    { rewrite blkmap_get_dir; [| exact Hk].
      apply bm_dir_zeroed_at. lia. }
    iEval (rewrite Hcur) in "Hcell".
    iPoseProof (iti_20 with "Htext") as "Hi20".
    iPoseProof (iti_22 with "Htext") as "Hi22".
    (* ===== +0x20 lw a1,0(s1) : a1 := ip->addrs[k] ===== *)
    assert (Hca : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                  = i_addr ip k).
    { rgne. rewrite Hs1. apply bv_eq. rewrite add_vec64_unsigned.
      assert (Hz : bv_unsigned (sign_extend' 64 (mword_of_int 0 : mword 12)
                                : mword 64) = 0) by (vm_compute; reflexivity).
      rewrite Hz Z.add_0_r. apply bvw64_small, bv_unsigned_in_range. }
    iEval (rewrite -Hca) in "Hcell".
    iApply (wp_clw_s_sconf Φ (mword_of_int (IT + 0x20)) Ra1 Rs1
              (mword_of_int 0 : mword 12) M (K - 6)%nat (bm_dir bm !!! k) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi20 Hcell [-]").
    iIntros (CID1 Hq1) "Hcg Hpc Hcell".
    iEval (rewrite Hca) in "Hcell".
    set (L0 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (bm_dir bm !!! k : mword 32))]> M).
    assert (HL0sp : it_sp m L0) by (rewrite /it_sp /L0 upd_ne; [exact Hsp | nz]).
    assert (HL0thr : it_thr m L0).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /L0 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18 N19). }
    assert (HL0s1 : L0 !!! Regidx Rs1 = i_addr ip k)
      by (rewrite /L0 upd_ne; [exact Hs1 | nz]).
    assert (HL0s2 : L0 !!! Regidx Rs2 = i_addr ip NDIRECT)
      by (rewrite /L0 upd_ne; [exact Hs2 | nz]).
    assert (HL0s3 : L0 !!! Regidx Rs3 = ip)
      by (rewrite /L0 upd_ne; [exact Hs3 | nz]).
    assert (HL0a1 : L0 !!! Regidx Ra1
                    = sign_extend' 64 (bm_dir bm !!! k : mword 32))
      by (rewrite /L0; apply upd_eq).
    assert (Hp22 : add_vec_int (mword_of_int (IT + 0x20) : mword 64) 2
                   = mword_of_int (IT + 0x22)) by pcw.
    iEval (rewrite Hp22) in "Hpc".
    (* ===== +0x22 c.beqz a1 : skip the free when the entry is zero ===== *)
    destruct (decide (bv_unsigned (bm_dir bm !!! k) = 0)) as [Hzero|Hnzero].
    - (* ---------- SKIP: the slot is already empty ---------- *)
      (* nothing moves: put the cell back unchanged, and the state at k IS
         the state at S k ([bm_dir_zeroed_skip], [bm_dir_freed_skip]) *)
      iDestruct ("Hmapback" $! (bm_dir bm !!! k : mword 32) with "Hcell")
        as "Hmap".
      assert (Hidins : <[k := bm_dir bm !!! k]> (bm_dir (bm_dir_zeroed bm k))
                       = bm_dir (bm_dir_zeroed bm k)).
      { rewrite -(bm_dir_zeroed_at bm k ltac:(lia)).
        apply list_insert_id, list_lookup_lookup_total_lt. lia. }
      iEval (rewrite Hidins) in "Hmap".
      iEval (cbn [bm_dir bm_ind bm_ent bm_dir_zeroed]) in "Hmap".
      assert (Hsk : bm_dir_zeroed bm (S k) = bm_dir_zeroed bm k)
        by (apply bm_dir_zeroed_skip; [lia | exact Hzero]).
      assert (Hfk : bm_dir_freed bm (S k) = bm_dir_freed bm k)
        by (apply bm_dir_freed_skip; exact Hzero).
      iAssert (it_dir_state γ γfs ip bm data cov logstart bmapstart size used
                            bn (S k))
        with "[Hmap Hblks Hbmr Hpaid]" as "Hst".
      { iApply (it_dir_state_close with "[Hmap] [Hblks] [Hbmr] Hpaid");
          [ rewrite Hsk; iExact "Hmap"
          | rewrite Hsk; iExact "Hblks"
          | rewrite Hfk; iExact "Hbmr" ]. }
      iPoseProof (iti_1a with "Htext") as "Hi1a".
      iPoseProof (iti_1c with "Htext") as "Hi1c".
      iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (IT + 0x22))
                (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 3)) Ra1
                L0 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HL0a1; exact (bm_eqz_true _ Hzero))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi22 [-]").
      iNext. iIntros (CID2 Hq2) "Hcg Hpc".
      assert (Htgt1a : add_vec (mword_of_int (IT + 0x22) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
                       = mword_of_int (IT + 0x1a)) by pcw.
      iEval (rewrite Htgt1a) in "Hpc".
      (* ===== +0x1a c.addi s1,s1,4 : bump the cursor ===== *)
      assert (Himm4 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))
                       : mword 64) = mword_of_int 4) by pcw.
      iApply (wp_caddi_s_sconf Φ (mword_of_int (IT + 0x1a)) Rs1
                (mword_of_int 4 : mword 6) L0 (K - 6)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1a").
      iIntros (CID3 Hq3) "Hcg Hpc".
      set (L1 := <[Regidx Rs1 := regval_into_reg
                    (add_vec (rget L0 Rs1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> L0).
      assert (HL1s1 : L1 !!! Regidx Rs1 = i_addr ip (S k)).
      { rewrite /L1 upd_eq. rgne. rewrite HL0s1 Himm4.
        rewrite -(it_dir_cursor ip k) /pa_add /add_vec_int.
        f_equal. }
      assert (HL1s2 : L1 !!! Regidx Rs2 = i_addr ip NDIRECT)
        by (rewrite /L1 upd_ne; [exact HL0s2 | nz]).
      assert (HL1s3 : L1 !!! Regidx Rs3 = ip)
        by (rewrite /L1 upd_ne; [exact HL0s3 | nz]).
      assert (HL1sp : it_sp m L1)
        by (rewrite /it_sp /L1 upd_ne; [exact HL0sp | nz]).
      assert (HL1thr : it_thr m L1).
      { intros c Hcs N2 N8 N9 N18 N19.
        rewrite /L1 upd_ne; [| regne]. exact (HL0thr c Hcs N2 N8 N9 N18 N19). }
      assert (Hp1c : add_vec_int (mword_of_int (IT + 0x1a) : mword 64) 2
                     = mword_of_int (IT + 0x1c)) by pcw.
      iEval (rewrite Hp1c) in "Hpc".
      (* ===== +0x1c beq s1,s2 : the bounds check ===== *)
      destruct (decide (S k = NDIRECT)) as [Hlast|Hmore].
      + (* the twelfth entry is done: leave the loop *)
        iPoseProof (iti_1c with "Htext") as "Hi1c'".
        iApply (wp_beq_taken_s_sconf Φ (mword_of_int (IT + 0x1c))
                  (mword_of_int 22 : mword 13) Rs2 Rs1 L1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HL1s1 HL1s2 Hlast;
                        apply eq_vec_true_iff; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi1c' [-]").
        iNext. iIntros (CID4 Hq4) "Hcg Hpc".
        assert (Htgt32 : add_vec (mword_of_int (IT + 0x1c) : mword 64)
                           (sign_extend' 64 (mword_of_int 22 : mword 13))
                         = mword_of_int (IT + 0x32)) by pcw.
        iEval (rewrite Htgt32) in "Hpc".
        rewrite /it_dexit.
        iDestruct (cpu_own_transport CID0 CID4 0 true (proc_addr jx) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iSpecialize ("Hexit" $! CID4 with "[%]"); [wp_next_chain|].
        rewrite Hlast.
        iApply ("Hexit" $! L1 with "[%] [%] [%] Hcg Hcnt Hpc Hrun Hppid
                                    Hidev Hsbb Hsl Hst");
          [exact HL1sp | exact HL1thr | exact HL1s3].
      + (* more entries to go: round again *)
        iPoseProof (iti_1c with "Htext") as "Hi1c'".
        assert (Hne : i_addr ip (S k) <> i_addr ip NDIRECT).
        { intros Hq. apply Hmore. apply (i_addr_inj ip); [lia | lia | exact Hq]. }
        iApply (wp_beq_fall_s_sconf Φ (mword_of_int (IT + 0x1c))
                  (mword_of_int 22 : mword 13) Rs2 Rs1 L1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HL1s1 HL1s2; apply eq_vec_false_iff;
                        exact Hne)
                  with "Hcg Hpc Hi1c' [-]").
        iIntros (CID4 Hq4) "Hcg Hpc".
        assert (Hp20 : add_vec_int (mword_of_int (IT + 0x1c) : mword 64) 4
                       = mword_of_int (IT + 0x20)) by pcw.
        iEval (rewrite Hp20) in "Hpc".
        assert (Hk' : (S k < NDIRECT)%nat)
          by (clear - Hk Hmore; unfold NDIRECT in *; lia).
        assert (Hf' : (NDIRECT - S k <= fuel)%nat)
          by (clear - Hk Hfuel Hmore; unfold NDIRECT in *; lia).
        (* the continuation and the cpu token move forward to the CID the
           chain has reached; the IH, being CID-generic, is applied there *)
        iDestruct (wp_next_shift (CIDa := CID0) (CIDb := CID4)
                     ltac:(wp_next_chain) with "Hexit") as "Hexit".
        iDestruct (cpu_own_transport CID0 CID4 0 true (proc_addr jx) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (IH CID4 (S k) L1 Hk' Hf' HL1sp HL1thr HL1s1 HL1s2 HL1s3
                  with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hprocs Hscheds
                        Hrun Hppid Hidev Hsbb Hdevi Hdgeom Hdlock Hsl
                        Hst Hexit").
    - (* ---------- FREE: the slot names a block ---------- *)
      iPoseProof (iti_24 with "Htext") as "Hi24".
      iPoseProof (iti_28 with "Htext") as "Hi28".
      iPoseProof (iti_2c with "Htext") as "Hi2c".
      iPoseProof (iti_30 with "Htext") as "Hi30".
      iPoseProof (iti_1a with "Htext") as "Hi1a".
      iPoseProof (iti_1c with "Htext") as "Hi1c".
      (* the block this slot names is a real, in-range, covered home block:
         all three come from [blkmap_wf] and the owed range premise, read at
         slot k of the ORIGINAL map (the cursor still holds it) *)
      assert (Hslotk : bm_slot bm k = bm_dir bm !!! k).
      { rewrite (bm_slot_lt bm k ltac:(unfold MAXFILE, NDIRECT in *; lia))
                blkmap_get_dir; [reflexivity | exact Hk]. }
      assert (Hbnz : bv_unsigned (bm_slot bm k) <> 0)
        by (rewrite Hslotk; exact Hnzero).
      destruct Hwf as (Hd & He & Hni & Hcv & Hinj).
      destruct (Hcv k ltac:(unfold MAXFILE, NDIRECT in *; lia) Hbnz)
        as [Hkcov Hklog].
      pose proof (Hrange k ltac:(unfold MAXFILE, NDIRECT in *; lia) Hbnz)
        as Hklt.
      rewrite Hslotk in Hkcov, Hklog, Hklt.
      (* the block leaves the bundle for good *)
      assert (Hgk : blkmap_get (bm_dir_zeroed bm k) k = bm_dir bm !!! k)
        by exact Hcur.
      iDestruct (inode_blocks_take γfs (bm_dir_zeroed bm k)
                   (bm_dir_zeroed bm (S k)) data k
                   ltac:(unfold MAXFILE, NDIRECT in *; lia)
                   ltac:(rewrite Hgk; exact Hnzero)
                   ltac:(rewrite blkmap_get_dir; [| lia];
                         rewrite (bm_dir_zeroed_below bm (S k) k); [reflexivity | lia | lia])
                   ltac:(intros t Ht Hne;
                         rewrite -(bm_slot_lt (bm_dir_zeroed bm (S k)) t Ht)
                                 -(bm_slot_lt (bm_dir_zeroed bm k) t Ht)
                                 (bm_dir_zeroed_slot bm (S k) t Hd
                                    ltac:(unfold NDIRECT in *; lia)
                                    ltac:(lia))
                                 (bm_dir_zeroed_slot bm k t Hd
                                    ltac:(unfold NDIRECT in *; lia)
                                    ltac:(lia));
                         destruct (decide (t < S k)%nat),
                                  (decide (t < k)%nat);
                           try reflexivity; lia)
                   with "Hblks") as "[[Hfsb Htok] Hblks]".
      iEval (rewrite Hgk) in "Hfsb". iEval (rewrite Hgk) in "Htok".
      (* ===== +0x22 c.beqz a1 : NOT taken, the slot names a block ===== *)
      iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (IT + 0x22))
                (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 3)) Ra1
                L0 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HL0a1; exact (bm_eqz_false _ Hnzero))
                with "Hcg Hpc Hi22 [-]").
      iIntros (CID1b Hq1b) "Hcg Hpc".
      assert (Hp24 : add_vec_int (mword_of_int (IT + 0x22) : mword 64) 2
                     = mword_of_int (IT + 0x24)) by pcw.
      iEval (rewrite Hp24) in "Hpc".
      (* ===== +0x24 lw a0,0(s3) : a0 := ip->dev ===== *)
      assert (Hdva : add_vec (rget L0 Rs3)
                       (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = i_dev ip).
      { rgne. rewrite HL0s3. reflexivity. }
      iEval (rewrite -Hdva) in "Hidev".
      iApply (wp_lw_s_sconf Φ (mword_of_int (IT + 0x24)) Ra0 Rs3
                (mword_of_int 0 : mword 12) L0 (K - 6)%nat dev b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi24 Hidev [-]").
      iIntros (CID2 Hq2) "Hcg Hpc Hidev".
      iEval (rewrite Hdva) in "Hidev".
      set (L2 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> L0).
      assert (HL2sp : it_sp m L2)
        by (rewrite /it_sp /L2 upd_ne; [exact HL0sp | nz]).
      assert (HL2thr : it_thr m L2).
      { intros c Hcs N2 N8 N9 N18 N19.
        rewrite /L2 upd_ne; [| regne]. exact (HL0thr c Hcs N2 N8 N9 N18 N19). }
      assert (HL2s1 : L2 !!! Regidx Rs1 = i_addr ip k)
        by (rewrite /L2 upd_ne; [exact HL0s1 | nz]).
      assert (HL2s2 : L2 !!! Regidx Rs2 = i_addr ip NDIRECT)
        by (rewrite /L2 upd_ne; [exact HL0s2 | nz]).
      assert (HL2s3 : L2 !!! Regidx Rs3 = ip)
        by (rewrite /L2 upd_ne; [exact HL0s3 | nz]).
      assert (HL2a0 : L2 !!! Regidx Ra0 = sign_extend' 64 dev)
        by (rewrite /L2; apply upd_eq).
      assert (HL2a1 : L2 !!! Regidx Ra1
                      = sign_extend' 64 (bm_dir bm !!! k : mword 32))
        by (rewrite /L2 upd_ne; [exact HL0a1 | nz]).
      assert (Hp28 : add_vec_int (mword_of_int (IT + 0x24) : mword 64) 4
                     = mword_of_int (IT + 0x28)) by pcw.
      iEval (rewrite Hp28) in "Hpc".
      (* ===== +0x28 jal bfree ===== *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (IT + 0x28)) Rra
                (mword_of_int 2095686 : mword 21) L2 (K - 6)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi28").
      iIntros (CID3 Hq3) "Hcg Hpc".
      set (L3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (IT + 0x28) : mword 64) 4)]> L2).
      assert (Htgtbf : add_vec (mword_of_int (IT + 0x28) : mword 64)
                         (sign_extend' 64 (mword_of_int 2095686 : mword 21))
                       = mword_of_int KernelSyms.bfree) by pcw.
      iEval (rewrite Htgtbf) in "Hpc".
      assert (HL3a0 : L3 !!! Regidx Ra0 = sign_extend' 64 dev)
        by (rewrite /L3 upd_ne; [exact HL2a0 | nz]).
      assert (HL3a1 : L3 !!! Regidx Ra1
                      = sign_extend' 64 (bm_dir bm !!! k : mword 32))
        by (rewrite /L3 upd_ne; [exact HL2a1 | nz]).
      assert (HL3ra : L3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (IT + 0x28) : mword 64) 4)
        by (rewrite /L3; apply upd_eq).
      assert (HL3sp : it_sp m L3)
        by (rewrite /it_sp /L3 upd_ne; [exact HL2sp | nz]).
      assert (HL3thr : it_thr m L3).
      { intros c Hcs N2 N8 N9 N18 N19.
        rewrite /L3 upd_ne; [| regne]. exact (HL2thr c Hcs N2 N8 N9 N18 N19). }
      (* THE BUDGET: bm_paid hands bfree a token with cr and the spare unit
         chosen to match, and takes back the same resource either way *)
      iDestruct (bm_paid_use with "Hpaid") as (cr u' Sb) "(%Hcrin & %Hbud & Hop & Hback)".
      iDestruct (cpu_own_transport CID0 CID3 0 true (proc_addr jx) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (wp_next_shift (CIDa := CID0) (CIDb := CID3)
                   ltac:(wp_next_chain) with "Hexit") as "Hexit".
      assert (HKbf : (K_bfree <= K - 6)%nat) by (unfold K_bfree; lia).
      iApply (BF.wp_bfree_gen Φ γs jx γl γu γd γk pd pav pu bn γ γfs
                cov logstart bmapstart size dev (used ∖ bm_dir_freed bm k)
                (bm_dir bm !!! k : mword 32) (data k) u' cr Sb
                pidv dq dqb L3 (K - 6)%nat true C b
                HKbf Hgeom Hsize Hbm0 Hbmcov Hbmlog
                ltac:(destruct (bv_unsigned_in_range 32 (bm_dir bm !!! k))
                        as [Hlo _]; split; [exact Hlo | exact Hklt])
                Hkcov Hklog
                (Hblen k)
                Hcrin Hj Hgl HL3a0 HL3a1 eq_refl
                with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hsbb [Hbmr] Hfsb Htok
                      Hppid Hprocs Hscheds Hrun Hdevi Hdgeom Hdlock Hsl Hop").
      { iExact "Hbmr". }
      iIntros (CID4 Hq4 mf) "%Hcs Hcg Hcnt Hpc Hrun Hppid Hsbb Hbmr
                             Hsl Hop".
      assert (Hpc2c : ret_pc (L3 !!! Regidx Rra : mword 64)
                      = mword_of_int (IT + 0x2c)) by (rewrite HL3ra; pcw).
      iEval (rewrite Hpc2c) in "Hpc".
      pose proof Hcs as Hcs'.
      assert (Hmfsp : it_sp m mf).
      { rewrite /it_sp
          (callee_saved_lookup Hcs' csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HL3sp. }
      assert (Hmfthr : it_thr m mf).
      { intros c Hcs2 N2 N8 N9 N18 N19.
        rewrite (callee_saved_lookup Hcs' c Hcs2).
        exact (HL3thr c Hcs2 N2 N8 N9 N18 N19). }
      assert (Hmfs1 : mf !!! Regidx Rs1 = i_addr ip k).
      { rewrite (callee_saved_lookup Hcs' Rs1 ltac:(vm_compute; reflexivity)).
        rewrite /L3 upd_ne; [| nz]. exact HL2s1. }
      assert (Hmfs2 : mf !!! Regidx Rs2 = i_addr ip NDIRECT).
      { rewrite (callee_saved_lookup Hcs' Rs2 ltac:(vm_compute; reflexivity)).
        rewrite /L3 upd_ne; [| nz]. exact HL2s2. }
      assert (Hmfs3 : mf !!! Regidx Rs3 = ip).
      { rewrite (callee_saved_lookup Hcs' Rs3 ltac:(vm_compute; reflexivity)).
        rewrite /L3 upd_ne; [| nz]. exact HL2s3. }
      (* ===== +0x2c sw zero,0(s1) : ip->addrs[k] = 0 ===== *)
      iDestruct (sie_cap_gpr_x0 mf (K - 6)%nat b (proc_addr jx) Rz
                   ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
      assert (Hsa : add_vec (rget mf Rs1)
                      (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = i_addr ip k).
      { rgne. rewrite Hmfs1. apply bv_eq. rewrite add_vec64_unsigned.
        assert (Hz : bv_unsigned (sign_extend' 64 (mword_of_int 0 : mword 12)
                                  : mword 64) = 0) by (vm_compute; reflexivity).
        rewrite Hz Z.add_0_r. apply bvw64_small, bv_unsigned_in_range. }
      iEval (rewrite -Hsa) in "Hcell".
      iApply (wp_sw_s_sconf Φ (mword_of_int (IT + 0x2c)) Rz Rs1
                (mword_of_int 0 : mword 12) mf (K - 6)%nat
                (bm_dir bm !!! k : mword 32) b
                with "Hcg Hpc Hi2c Hcell").
      iIntros (CID5 Hq5) "Hcg Hpc Hcell".
      iEval (rewrite Hsa) in "Hcell".
      assert (Hz32 : trunc32 (rget mf Rz) = (bv_0 32 : mword 32))
        by (rgne; rewrite Hx0; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hz32) in "Hcell".
      (* the cleared cell closes the map at the NEXT cursor *)
      iDestruct ("Hmapback" $! (bv_0 32) with "Hcell") as "Hmap".
      assert (Hstep : MkBlkmap (<[k := bv_0 32]> (bm_dir (bm_dir_zeroed bm k)))
                        (bm_ind (bm_dir_zeroed bm k))
                        (bm_ent (bm_dir_zeroed bm k))
                      = bm_dir_zeroed bm (S k)).
      { rewrite (bm_dir_zeroed_step bm k ltac:(lia)).
        rewrite /bm_dir_zeroed. cbn [bm_dir bm_ind bm_ent]. reflexivity. }
      iEval (rewrite Hstep) in "Hmap".
      (* the pool grew by exactly this block *)
      assert (Hfstep : used ∖ bm_dir_freed bm k
                       ∖ {[ bv_unsigned (bm_dir bm !!! k : mword 32) ]}
                       = used ∖ bm_dir_freed bm (S k)).
      { rewrite bm_dir_freed_step. clear -Hnzero. set_solver. }
      iEval (rewrite Hfstep) in "Hbmr".
      iDestruct ("Hback" with "[Hop]") as "Hpaid";
        [ rewrite Hbud; iExact "Hop" |].
      iAssert (it_dir_state γ γfs ip bm data cov logstart bmapstart size used
                            bn (S k))
        with "[Hmap Hblks Hbmr Hpaid]" as "Hst".
      { iApply (it_dir_state_close with "Hmap Hblks Hbmr Hpaid"). }
      (* ===== +0x30 c.j : back to the increment ===== *)
      assert (Hp30 : add_vec_int (mword_of_int (IT + 0x2c) : mword 64) 4
                     = mword_of_int (IT + 0x30)) by pcw.
      iEval (rewrite Hp30) in "Hpc".
      iApply (wp_cj_s_sconf Φ (mword_of_int (IT + 0x30))
                (sign_extend' 21 (concat_vec (mword_of_int 2037 : mword 11) ('b"0")))
                mf (K - 6)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi30 [-]").
      iIntros (CID6 Hq6). iNext. iIntros "Hcg Hpc".
      assert (Htgt1a' : add_vec (mword_of_int (IT + 0x30) : mword 64)
                          (sign_extend' 64 (sign_extend' 21
                             (concat_vec (mword_of_int 2037 : mword 11) ('b"0"))))
                        = mword_of_int (IT + 0x1a)) by pcw.
      iEval (rewrite Htgt1a') in "Hpc".
      (* ===== +0x1a / +0x1c : the same increment and bounds test ===== *)
      assert (Himm4' : (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))
                        : mword 64) = mword_of_int 4) by pcw.
      iApply (wp_caddi_s_sconf Φ (mword_of_int (IT + 0x1a)) Rs1
                (mword_of_int 4 : mword 6) mf (K - 6)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1a").
      iIntros (CID7 Hq7) "Hcg Hpc".
      set (N1 := <[Regidx Rs1 := regval_into_reg
                    (add_vec (rget mf Rs1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> mf).
      assert (HN1s1 : N1 !!! Regidx Rs1 = i_addr ip (S k)).
      { rewrite /N1 upd_eq. rgne. rewrite Hmfs1 Himm4'.
        rewrite -(it_dir_cursor ip k) /pa_add /add_vec_int. f_equal. }
      assert (HN1s2 : N1 !!! Regidx Rs2 = i_addr ip NDIRECT)
        by (rewrite /N1 upd_ne; [exact Hmfs2 | nz]).
      assert (HN1s3 : N1 !!! Regidx Rs3 = ip)
        by (rewrite /N1 upd_ne; [exact Hmfs3 | nz]).
      assert (HN1sp : it_sp m N1)
        by (rewrite /it_sp /N1 upd_ne; [exact Hmfsp | nz]).
      assert (HN1thr : it_thr m N1).
      { intros c Hcs2 N2 N8 N9 N18 N19.
        rewrite /N1 upd_ne; [| regne]. exact (Hmfthr c Hcs2 N2 N8 N9 N18 N19). }
      assert (Hp1c' : add_vec_int (mword_of_int (IT + 0x1a) : mword 64) 2
                      = mword_of_int (IT + 0x1c)) by pcw.
      iEval (rewrite Hp1c') in "Hpc".
      destruct (decide (S k = NDIRECT)) as [Hlast|Hmore].
      + iApply (wp_beq_taken_s_sconf Φ (mword_of_int (IT + 0x1c))
                  (mword_of_int 22 : mword 13) Rs2 Rs1 N1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HN1s1 HN1s2 Hlast;
                        apply eq_vec_true_iff; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi1c [-]").
        iNext. iIntros (CID8 Hq8) "Hcg Hpc".
        assert (Htgt32' : add_vec (mword_of_int (IT + 0x1c) : mword 64)
                            (sign_extend' 64 (mword_of_int 22 : mword 13))
                          = mword_of_int (IT + 0x32)) by pcw.
        iEval (rewrite Htgt32') in "Hpc".
        rewrite /it_dexit.
        iDestruct (cpu_own_transport CID4 CID8 0 true (proc_addr jx) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (wp_next_shift (CIDa := CID3) (CIDb := CID8)
                     ltac:(wp_next_chain) with "Hexit") as "Hexit".
        iSpecialize ("Hexit" $! CID8 with "[%]"); [wp_next_chain|].
        rewrite Hlast.
        iApply ("Hexit" $! N1 with "[%] [%] [%] Hcg Hcnt Hpc Hrun Hppid
                                    Hidev Hsbb Hsl Hst");
          [exact HN1sp | exact HN1thr | exact HN1s3].
      + assert (Hne' : i_addr ip (S k) <> i_addr ip NDIRECT).
        { intros Hq. apply Hmore. apply (i_addr_inj ip); [lia | lia | exact Hq]. }
        iApply (wp_beq_fall_s_sconf Φ (mword_of_int (IT + 0x1c))
                  (mword_of_int 22 : mword 13) Rs2 Rs1 N1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HN1s1 HN1s2;
                        apply eq_vec_false_iff; exact Hne')
                  with "Hcg Hpc Hi1c [-]").
        iIntros (CID8 Hq8) "Hcg Hpc".
        assert (Hp20' : add_vec_int (mword_of_int (IT + 0x1c) : mword 64) 4
                        = mword_of_int (IT + 0x20)) by pcw.
        iEval (rewrite Hp20') in "Hpc".
        assert (Hk'' : (S k < NDIRECT)%nat)
          by (clear - Hk Hmore; unfold NDIRECT in *; lia).
        assert (Hf'' : (NDIRECT - S k <= fuel)%nat)
          by (clear - Hk Hfuel Hmore; unfold NDIRECT in *; lia).
        iDestruct (cpu_own_transport CID4 CID8 0 true (proc_addr jx) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (wp_next_shift (CIDa := CID3) (CIDb := CID8)
                     ltac:(wp_next_chain) with "Hexit") as "Hexit".
        iApply (IH CID8 (S k) N1 Hk'' Hf'' HN1sp HN1thr HN1s1 HN1s2 HN1s3
                  with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hprocs Hscheds
                        Hrun Hppid Hidev Hsbb Hdevi Hdgeom Hdlock Hsl
                        Hst Hexit").
  Qed.

End ItruncDLoop.

(* ===================================================================== *)
(*  THE INDIRECT LOOP: the 256 entries inside the indirect block          *)
(*                                                                        *)
(*  Same rotated shape as the direct loop -- [j] at +0x64 lands on the     *)
(*  body test at +0x6c, and [beq] at +0x68 guards only later iterations.   *)
(*  What differs is that the entries live in the BUFFER, not the inode,    *)
(*  and the C never writes them back: it frees each and then frees the     *)
(*  whole block.  So [buf_own] rides the loop unchanged and there is no    *)
(*  store, no map, and no [inode_map] traffic at all.                      *)
(* ===================================================================== *)
Section ItruncELoop.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  Definition it_eexit `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γ : log_names) (γfs : fs_names) (bn : bio_names) (γd : disk_names)
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z)
      (dev : mword 32) (ip : mword 64) (bm : blkmap)
      (data : nat -> list (bv 8)) (kk : nat) (dsk : mword 32)
      (pidv : mword 32) (dq dqd dqb : dfrac) (j : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) : iProp Σ :=
    wp_next b (proc_addr j) (fun (CID : CpuId) =>
      ∀ Mx : regfile,
        ⌜it_sp m Mx⌝ -∗ ⌜it_thr m Mx⌝ -∗ ⌜Mx !!! Regidx Rs3 = ip⌝ -∗
        ⌜Mx !!! Regidx Rs4 = bnode kk⌝ -∗
        sie_cap_gpr Mx (K - 6)%nat b (proc_addr j) -∗
        cpu_own 0 true (proc_addr j) C b -∗
        pc_is (mword_of_int (IT + 0x7a) : mword 64) -∗
        running_claim j -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        i_dev ip ↦₄{dqd} dev -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        buf_own (bpa kk) (bm_ind bm) dsk (ind_bytes (bm_ent bm)) -∗
        it_ent_state γ γfs bm data cov logstart bmapstart size used
                     NINDIRECT -∗
        WP (Loop : expr riscv_lang))%I.

  Local Lemma it_eloop `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γs : list gname) (jx : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart bmapstart size : Z) (dev : mword 32)
      (used : gset Z) (ip : mword 64) (bm : blkmap)
      (data : nat -> list (bv 8)) (kk : nat) (dsk : mword 32)
      (pidv : mword 32) (dq dqd dqb : dfrac)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) (fuel : nat) :
    (K_itrunc <= K)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    blkmap_wf cov logstart bm ->
    (forall i : nat, (i <= MAXFILE)%nat -> bv_unsigned (bm_slot bm i) <> 0 ->
       bv_unsigned (bm_slot bm i) < size) ->
    (forall i : nat, length (data i) = BSIZE) ->
    (kk < NBUF)%nat ->
    (jx < NPROC)%nat ->
    γs !! jx = Some γl ->
    forall (q : nat) (M : regfile),
    (q < NINDIRECT)%nat ->
    (NINDIRECT - q <= fuel)%nat ->
    it_sp m M ->
    it_thr m M ->
    M !!! Regidx Rs1 = pa_add (b_data (bpa kk)) (4 * q)%nat ->
    M !!! Regidx Rs2 = pa_add (b_data (bpa kk)) (4 * NINDIRECT)%nat ->
    M !!! Regidx Rs3 = ip ->
    M !!! Regidx Rs4 = bnode kk ->
    sie_cap_gpr M (K - 6)%nat b (proc_addr jx) -∗
    cpu_own 0 true (proc_addr jx) C b -∗
    kernel_text -∗
    pc_is (mword_of_int (IT + 0x6c) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv Φ γs -∗
    scheds_inv Φ γs -∗
    running_claim jx -∗
    p_pid (proc_addr jx) ↦₄{dq} pidv -∗
    i_dev ip ↦₄{dqd} dev -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots bn 2 -∗
    buf_own (bpa kk) (bm_ind bm) dsk (ind_bytes (bm_ent bm)) -∗
    it_ent_state γ γfs bm data cov logstart bmapstart size used q -∗
    it_eexit (CID0 := CID0) Φ γ γfs bn γd cov logstart bmapstart size used dev
             ip bm data kk dsk pidv dq dqd dqb jx m K C b -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hsize Hbm0 Hbmcov Hbmlog Hwf Hrange Hblen Hkk Hj Hgl.
    revert CID0.
    induction fuel as [|fuel IH];
      intros CID0 q M Hq Hfuel Hsp Hthr Hs1 Hs2 Hs3 Hs4;
      [ exfalso; unfold NINDIRECT in Hq, Hfuel; lia |].
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hlctx #Hprocs #Hscheds Hrun Hppid Hidev Hsbb #Hdevi #Hdgeom #Hdlock Hsl Hbuf Hst Hexit".
    pose proof HK as HK'. unfold K_itrunc in HK'.
    pose proof (blkmap_wf_ent_len _ _ _ Hwf) as Hentlen.
    iDestruct (it_ent_state_open with "Hst") as "(Hres & Hbmr & Hpaid)".
    iPoseProof (iti_6c with "Htext") as "Hi6c".
    iPoseProof (iti_6e with "Htext") as "Hi6e".
    iPoseProof (iti_66 with "Htext") as "Hi66".
    iPoseProof (iti_68 with "Htext") as "Hi68".
    (* the entry word, borrowed out of the buffer *)
    assert (Hal : is_aligned_paddr
                    (Physaddr (pa_add (b_data (bnode kk)) (4 * q)%nat)) 4 = true)
      by (apply bm_align4; [exact Hkk | unfold NINDIRECT in Hq; lia]).
    iDestruct (bm_buf_word_acc (bpa kk) (bm_ind bm) dsk
                 (ind_bytes (bm_ent bm)) q Hal
                 ltac:(unfold NINDIRECT in Hq; lia)
                 with "Hbuf") as "(%Hlen0 & Hcell & Hbufback)".
    assert (Hentv : bb_mk (fun jj => ind_bytes (bm_ent bm) !!! jj) (4 * q)%nat
                    = bm_ent bm !!! q)
      by (apply bm_ent_read; rewrite Hentlen; exact Hq).
    iEval (rewrite Hentv) in "Hcell".
    (* ===== +0x6c lw a1,0(s1) : a1 := a[q] ===== *)
    assert (Hca : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                  = pa_add (b_data (bpa kk)) (4 * q)%nat).
    { rgne. rewrite Hs1. apply bv_eq. rewrite add_vec64_unsigned.
      assert (Hz : bv_unsigned (sign_extend' 64 (mword_of_int 0 : mword 12)
                                : mword 64) = 0) by (vm_compute; reflexivity).
      rewrite Hz Z.add_0_r. apply bvw64_small, bv_unsigned_in_range. }
    iEval (rewrite -Hca) in "Hcell".
    iApply (wp_clw_s_sconf Φ (mword_of_int (IT + 0x6c)) Ra1 Rs1
              (mword_of_int 0 : mword 12) M (K - 6)%nat (bm_ent bm !!! q) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi6c Hcell [-]").
    iIntros (CID1 Hq1) "Hcg Hpc Hcell".
    iEval (rewrite Hca) in "Hcell".
    (* the buffer is never written, so the word goes straight back *)
    iEval (rewrite -Hentv) in "Hcell".
    iDestruct ("Hbufback" $! (bb_mk (fun jj => ind_bytes (bm_ent bm) !!! jj)
                                (4 * q)%nat) with "Hcell") as "Hbuf".
    (* [bm_buf_restore] is exactly this: put the word back as it came and
       the byte image is the one you started with *)
    iEval (rewrite (bm_buf_restore (ind_bytes (bm_ent bm)) q Hlen0)) in "Hbuf".
    set (E0 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (bm_ent bm !!! q : mword 32))]> M).
    assert (HE0sp : it_sp m E0) by (rewrite /it_sp /E0 upd_ne; [exact Hsp | nz]).
    assert (HE0thr : it_thr m E0).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /E0 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18 N19). }
    assert (HE0s1 : E0 !!! Regidx Rs1 = pa_add (b_data (bpa kk)) (4 * q)%nat)
      by (rewrite /E0 upd_ne; [exact Hs1 | nz]).
    assert (HE0s2 : E0 !!! Regidx Rs2
                    = pa_add (b_data (bpa kk)) (4 * NINDIRECT)%nat)
      by (rewrite /E0 upd_ne; [exact Hs2 | nz]).
    assert (HE0s3 : E0 !!! Regidx Rs3 = ip)
      by (rewrite /E0 upd_ne; [exact Hs3 | nz]).
    assert (HE0s4 : E0 !!! Regidx Rs4 = bnode kk)
      by (rewrite /E0 upd_ne; [exact Hs4 | nz]).
    assert (HE0a1 : E0 !!! Regidx Ra1
                    = sign_extend' 64 (bm_ent bm !!! q : mword 32))
      by (rewrite /E0; apply upd_eq).
    assert (Hp6e : add_vec_int (mword_of_int (IT + 0x6c) : mword 64) 2
                   = mword_of_int (IT + 0x6e)) by pcw.
    iEval (rewrite Hp6e) in "Hpc".
    (* the cursor entry leaves the remaining bundle either way *)
    iDestruct (it_ent_res_peel γfs bm data q ltac:(exact Hq) with "Hres")
      as "[Hblk Hres]".
    (* ===== +0x6e c.beqz a1 ===== *)
    destruct (decide (bv_unsigned (bm_ent bm !!! q : mword 32) = 0))
      as [Hzero|Hnzero].
    - (* ---------- SKIP ---------- *)
      assert (Hfk : bm_ent_freed bm (S q) = bm_ent_freed bm q)
        by (apply bm_ent_freed_skip; exact Hzero).
      iAssert (it_ent_state γ γfs bm data cov logstart bmapstart size used (S q))
        with "[Hres Hbmr Hpaid]" as "Hst".
      { iApply (it_ent_state_close with "Hres [Hbmr] Hpaid").
        rewrite Hfk. iExact "Hbmr". }
      iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (IT + 0x6e))
                (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 3)) Ra1
                E0 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HE0a1; exact (bm_eqz_true _ Hzero))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi6e [-]").
      iNext. iIntros (CID2 Hq2) "Hcg Hpc".
      assert (Htgt66 : add_vec (mword_of_int (IT + 0x6e) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
                       = mword_of_int (IT + 0x66)) by pcw.
      iEval (rewrite Htgt66) in "Hpc".
      (* ===== +0x66 c.addi s1,s1,4 ; +0x68 beq s1,s2 ===== *)
      assert (Himm4 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))
                       : mword 64) = mword_of_int 4) by pcw.
      iApply (wp_caddi_s_sconf Φ (mword_of_int (IT + 0x66)) Rs1
                (mword_of_int 4 : mword 6) E0 (K - 6)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi66").
      iIntros (CIDa Hqa) "Hcg Hpc".
      set (E1 := <[Regidx Rs1 := regval_into_reg
                    (add_vec (rget E0 Rs1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> E0).
      assert (HE1s1 : E1 !!! Regidx Rs1
                      = pa_add (b_data (bpa kk)) (4 * S q)%nat).
      { rewrite /E1 upd_eq. rgne. rewrite HE0s1 Himm4.
        rewrite -(b_data_cursor (bpa kk) q) /pa_add /add_vec_int. f_equal. }
      assert (HE1s2 : E1 !!! Regidx Rs2
                      = pa_add (b_data (bpa kk)) (4 * NINDIRECT)%nat)
        by (rewrite /E1 upd_ne; [exact HE0s2 | nz]).
      assert (HE1s3 : E1 !!! Regidx Rs3 = ip)
        by (rewrite /E1 upd_ne; [exact HE0s3 | nz]).
      assert (HE1s4 : E1 !!! Regidx Rs4 = bnode kk)
        by (rewrite /E1 upd_ne; [exact HE0s4 | nz]).
      assert (HE1sp : it_sp m E1)
        by (rewrite /it_sp /E1 upd_ne; [exact HE0sp | nz]).
      assert (HE1thr : it_thr m E1).
      { intros c Hcs2 N2 N8 N9 N18 N19.
        rewrite /E1 upd_ne; [| regne]. exact (HE0thr c Hcs2 N2 N8 N9 N18 N19). }
      assert (Hp68 : add_vec_int (mword_of_int (IT + 0x66) : mword 64) 2
                     = mword_of_int (IT + 0x68)) by pcw.
      iEval (rewrite Hp68) in "Hpc".
      destruct (decide (S q = NINDIRECT)) as [Hlast|Hmore].
      + iApply (wp_beq_taken_s_sconf Φ (mword_of_int (IT + 0x68))
                  (mword_of_int 18 : mword 13) Rs2 Rs1 E1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HE1s1 HE1s2 Hlast;
                        apply eq_vec_true_iff; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi68 [-]").
        iNext. iIntros (CIDb Hqb) "Hcg Hpc".
        assert (Htgt7a : add_vec (mword_of_int (IT + 0x68) : mword 64)
                           (sign_extend' 64 (mword_of_int 18 : mword 13))
                         = mword_of_int (IT + 0x7a)) by pcw.
        iEval (rewrite Htgt7a) in "Hpc".
        rewrite /it_eexit.
        iDestruct (cpu_own_transport CID0 CIDb 0 true (proc_addr jx) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (wp_next_shift (CIDa := CID0) (CIDb := CIDb)
                     ltac:(wp_next_chain) with "Hexit") as "Hexit".
        iSpecialize ("Hexit" $! CIDb with "[%]"); [wp_next_chain|].
        rewrite Hlast.
        iApply ("Hexit" $! E1 with "[%] [%] [%] [%] Hcg Hcnt Hpc Hrun
                                    Hppid Hidev Hsbb Hbuf Hst");
          [exact HE1sp | exact HE1thr | exact HE1s3 | exact HE1s4].
      + assert (Hne : pa_add (b_data (bpa kk)) (4 * S q)%nat
                      <> pa_add (b_data (bpa kk)) (4 * NINDIRECT)%nat).
        { intros Hz. apply Hmore.
          apply (b_data_off_inj (bpa kk)); [lia | lia | exact Hz]. }
        iApply (wp_beq_fall_s_sconf Φ (mword_of_int (IT + 0x68))
                  (mword_of_int 18 : mword 13) Rs2 Rs1 E1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HE1s1 HE1s2;
                        apply eq_vec_false_iff; exact Hne)
                  with "Hcg Hpc Hi68 [-]").
        iIntros (CIDb Hqb) "Hcg Hpc".
        assert (Hp6c : add_vec_int (mword_of_int (IT + 0x68) : mword 64) 4
                       = mword_of_int (IT + 0x6c)) by pcw.
        iEval (rewrite Hp6c) in "Hpc".
        assert (Hq'' : (S q < NINDIRECT)%nat)
          by (clear - Hq Hmore; unfold NINDIRECT in *; lia).
        assert (Hf'' : (NINDIRECT - S q <= fuel)%nat)
          by (clear - Hq Hfuel Hmore; unfold NINDIRECT in *; lia).
        iDestruct (cpu_own_transport CID0 CIDb 0 true (proc_addr jx) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (wp_next_shift (CIDa := CID0) (CIDb := CIDb)
                     ltac:(wp_next_chain) with "Hexit") as "Hexit".
        iApply (IH CIDb (S q) E1 Hq'' Hf'' HE1sp HE1thr HE1s1 HE1s2 HE1s3 HE1s4
                  with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hprocs Hscheds
                        Hrun Hppid Hidev Hsbb Hdevi Hdgeom Hdlock Hsl
                        Hbuf Hst Hexit").

    - (* ---------- FREE ---------- *)
      iPoseProof (iti_70 with "Htext") as "Hi70".
      iPoseProof (iti_74 with "Htext") as "Hi74".
      iPoseProof (iti_78 with "Htext") as "Hi78".
      (* the slot this entry occupies, and what blkmap_wf says about it *)
      assert (Hslotq : bm_slot bm (NDIRECT + q)%nat = bm_ent bm !!! q).
      { rewrite (bm_slot_lt bm (NDIRECT + q)%nat
                   ltac:(unfold MAXFILE, NDIRECT, NINDIRECT in *; lia)).
        rewrite /blkmap_get.
        destruct (decide ((NDIRECT + q) < NDIRECT)%nat); [lia|].
        f_equal. lia. }
      assert (Hbnz : bv_unsigned (bm_slot bm (NDIRECT + q)%nat) <> 0)
        by (rewrite Hslotq; exact Hnzero).
      pose proof Hwf as Hwf2. destruct Hwf2 as (Hd & He & Hni & Hcv & Hinj).
      destruct (Hcv (NDIRECT + q)%nat
                  ltac:(unfold MAXFILE, NDIRECT, NINDIRECT in *; lia) Hbnz)
        as [Hqcov Hqlog].
      pose proof (Hrange (NDIRECT + q)%nat
                    ltac:(unfold MAXFILE, NDIRECT, NINDIRECT in *; lia) Hbnz)
        as Hqlt.
      rewrite Hslotq in Hqcov, Hqlog, Hqlt.
      iDestruct (blk_res_nz γfs (bm_ent bm !!! q) (data (NDIRECT + q)%nat)
                   Hnzero with "Hblk") as "[Hfsb Htok]".
      (* ===== +0x6e c.beqz a1 : NOT taken ===== *)
      iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (IT + 0x6e))
                (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 3)) Ra1
                E0 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HE0a1; exact (bm_eqz_false _ Hnzero))
                with "Hcg Hpc Hi6e [-]").
      iIntros (CIDx Hqx) "Hcg Hpc".
      assert (Hp70 : add_vec_int (mword_of_int (IT + 0x6e) : mword 64) 2
                     = mword_of_int (IT + 0x70)) by pcw.
      iEval (rewrite Hp70) in "Hpc".
      (* ===== +0x70 lw a0,0(s3) ===== *)
      assert (Hdva : add_vec (rget E0 Rs3)
                       (sign_extend' 64 (mword_of_int 0 : mword 12)) = i_dev ip).
      { rgne. rewrite HE0s3. reflexivity. }
      iEval (rewrite -Hdva) in "Hidev".
      iApply (wp_lw_s_sconf Φ (mword_of_int (IT + 0x70)) Ra0 Rs3
                (mword_of_int 0 : mword 12) E0 (K - 6)%nat dev b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi70 Hidev [-]").
      iIntros (CIDy Hqy) "Hcg Hpc Hidev".
      iEval (rewrite Hdva) in "Hidev".
      set (E2 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> E0).
      assert (HE2a0 : E2 !!! Regidx Ra0 = sign_extend' 64 dev)
        by (rewrite /E2; apply upd_eq).
      assert (HE2a1 : E2 !!! Regidx Ra1
                      = sign_extend' 64 (bm_ent bm !!! q : mword 32))
        by (rewrite /E2 upd_ne; [exact HE0a1 | nz]).
      assert (HE2sp : it_sp m E2)
        by (rewrite /it_sp /E2 upd_ne; [exact HE0sp | nz]).
      assert (HE2thr : it_thr m E2).
      { intros c Hcs2 N2 N8 N9 N18 N19.
        rewrite /E2 upd_ne; [| regne]. exact (HE0thr c Hcs2 N2 N8 N9 N18 N19). }
      assert (HE2s1 : E2 !!! Regidx Rs1 = pa_add (b_data (bpa kk)) (4 * q)%nat)
        by (rewrite /E2 upd_ne; [exact HE0s1 | nz]).
      assert (HE2s2 : E2 !!! Regidx Rs2
                      = pa_add (b_data (bpa kk)) (4 * NINDIRECT)%nat)
        by (rewrite /E2 upd_ne; [exact HE0s2 | nz]).
      assert (HE2s3 : E2 !!! Regidx Rs3 = ip)
        by (rewrite /E2 upd_ne; [exact HE0s3 | nz]).
      assert (HE2s4 : E2 !!! Regidx Rs4 = bnode kk)
        by (rewrite /E2 upd_ne; [exact HE0s4 | nz]).
      assert (Hp74 : add_vec_int (mword_of_int (IT + 0x70) : mword 64) 4
                     = mword_of_int (IT + 0x74)) by pcw.
      iEval (rewrite Hp74) in "Hpc".
      (* ===== +0x74 jal bfree ===== *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (IT + 0x74)) Rra
                (mword_of_int 2095610 : mword 21) E2 (K - 6)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi74").
      iIntros (CIDz Hqz) "Hcg Hpc".
      set (E3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (IT + 0x74) : mword 64) 4)]> E2).
      assert (Htgtbf : add_vec (mword_of_int (IT + 0x74) : mword 64)
                         (sign_extend' 64 (mword_of_int 2095610 : mword 21))
                       = mword_of_int KernelSyms.bfree) by pcw.
      iEval (rewrite Htgtbf) in "Hpc".
      assert (HE3a0 : E3 !!! Regidx Ra0 = sign_extend' 64 dev)
        by (rewrite /E3 upd_ne; [exact HE2a0 | nz]).
      assert (HE3a1 : E3 !!! Regidx Ra1
                      = sign_extend' 64 (bm_ent bm !!! q : mword 32))
        by (rewrite /E3 upd_ne; [exact HE2a1 | nz]).
      assert (HE3ra : E3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (IT + 0x74) : mword 64) 4)
        by (rewrite /E3; apply upd_eq).
      assert (HE3sp : it_sp m E3)
        by (rewrite /it_sp /E3 upd_ne; [exact HE2sp | nz]).
      assert (HE3thr : it_thr m E3).
      { intros c Hcs2 N2 N8 N9 N18 N19.
        rewrite /E3 upd_ne; [| regne]. exact (HE2thr c Hcs2 N2 N8 N9 N18 N19). }
      iDestruct (bm_paid_use with "Hpaid") as (cr u' Sb) "(%Hcrin & %Hbud & Hop & Hback)".
      iDestruct (cpu_own_transport CID0 CIDz 0 true (proc_addr jx) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (wp_next_shift (CIDa := CID0) (CIDb := CIDz)
                   ltac:(wp_next_chain) with "Hexit") as "Hexit".
      assert (HKbf : (K_bfree <= K - 6)%nat) by (unfold K_bfree; lia).
      iApply (BF.wp_bfree_gen Φ γs jx γl γu γd γk pd pav pu bn γ γfs
                cov logstart bmapstart size dev
                (used ∖ (bm_dir_freed bm NDIRECT ∪ bm_ent_freed bm q))
                (bm_ent bm !!! q : mword 32) (data (NDIRECT + q)%nat) u' cr Sb
                pidv dq dqb E3 (K - 6)%nat true C b
                HKbf Hgeom Hsize Hbm0 Hbmcov Hbmlog
                ltac:(destruct (bv_unsigned_in_range 32 (bm_ent bm !!! q))
                        as [Hlo _]; split; [exact Hlo | exact Hqlt])
                Hqcov Hqlog (Hblen (NDIRECT + q)%nat)
                Hcrin Hj Hgl HE3a0 HE3a1 eq_refl
                with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hsbb Hbmr Hfsb Htok
                      Hppid Hprocs Hscheds Hrun Hdevi Hdgeom Hdlock Hsl Hop").
      iIntros (CIDf Hqf mfE) "%Hcs Hcg Hcnt Hpc Hrun Hppid Hsbb Hbmr
                              Hsl Hop".
      assert (Hpc78 : ret_pc (E3 !!! Regidx Rra : mword 64)
                      = mword_of_int (IT + 0x78)) by (rewrite HE3ra; pcw).
      iEval (rewrite Hpc78) in "Hpc".
      pose proof Hcs as Hcs'.
      assert (HFsp : it_sp m mfE).
      { rewrite /it_sp
          (callee_saved_lookup Hcs' csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HE3sp. }
      assert (HFthr : it_thr m mfE).
      { intros c Hcs2 N2 N8 N9 N18 N19.
        rewrite (callee_saved_lookup Hcs' c Hcs2).
        exact (HE3thr c Hcs2 N2 N8 N9 N18 N19). }
      assert (HFs1 : mfE !!! Regidx Rs1 = pa_add (b_data (bpa kk)) (4 * q)%nat).
      { rewrite (callee_saved_lookup Hcs' Rs1 ltac:(vm_compute; reflexivity)).
        rewrite /E3 upd_ne; [| nz]. exact HE2s1. }
      assert (HFs2 : mfE !!! Regidx Rs2
                     = pa_add (b_data (bpa kk)) (4 * NINDIRECT)%nat).
      { rewrite (callee_saved_lookup Hcs' Rs2 ltac:(vm_compute; reflexivity)).
        rewrite /E3 upd_ne; [| nz]. exact HE2s2. }
      assert (HFs3 : mfE !!! Regidx Rs3 = ip).
      { rewrite (callee_saved_lookup Hcs' Rs3 ltac:(vm_compute; reflexivity)).
        rewrite /E3 upd_ne; [| nz]. exact HE2s3. }
      assert (HFs4 : mfE !!! Regidx Rs4 = bnode kk).
      { rewrite (callee_saved_lookup Hcs' Rs4 ltac:(vm_compute; reflexivity)).
        rewrite /E3 upd_ne; [| nz]. exact HE2s4. }
      (* the pool grew by exactly this entry *)
      assert (Hfstep : used ∖ (bm_dir_freed bm NDIRECT ∪ bm_ent_freed bm q)
                       ∖ {[ bv_unsigned (bm_ent bm !!! q : mword 32) ]}
                       = used ∖ (bm_dir_freed bm NDIRECT
                                 ∪ bm_ent_freed bm (S q))).
      { rewrite bm_ent_freed_step. clear -Hnzero. set_solver. }
      iEval (rewrite Hfstep) in "Hbmr".
      iDestruct ("Hback" with "[Hop]") as "Hpaid";
        [ rewrite Hbud; iExact "Hop" |].
      iAssert (it_ent_state γ γfs bm data cov logstart bmapstart size used (S q))
        with "[Hres Hbmr Hpaid]" as "Hst".
      { iApply (it_ent_state_close with "Hres Hbmr Hpaid"). }
      (* ===== +0x78 c.j : back to the increment ===== *)
      iApply (wp_cj_s_sconf Φ (mword_of_int (IT + 0x78))
                (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")))
                mfE (K - 6)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi78 [-]").
      iIntros (CIDw Hqw). iNext. iIntros "Hcg Hpc".
      assert (Htgt66f : add_vec (mword_of_int (IT + 0x78) : mword 64)
                          (sign_extend' 64 (sign_extend' 21
                             (concat_vec (mword_of_int 2039 : mword 11) ('b"0"))))
                        = mword_of_int (IT + 0x66)) by pcw.
      iEval (rewrite Htgt66f) in "Hpc".
      (* ===== +0x66 c.addi s1,s1,4 ; +0x68 beq s1,s2 ===== *)
      assert (Himm4f : (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))
                       : mword 64) = mword_of_int 4) by pcw.
      iApply (wp_caddi_s_sconf Φ (mword_of_int (IT + 0x66)) Rs1
                (mword_of_int 4 : mword 6) mfE (K - 6)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi66").
      iIntros (CIDp Hqp) "Hcg Hpc".
      set (F1 := <[Regidx Rs1 := regval_into_reg
                    (add_vec (rget mfE Rs1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> mfE).
      assert (HF1s1 : F1 !!! Regidx Rs1
                      = pa_add (b_data (bpa kk)) (4 * S q)%nat).
      { rewrite /F1 upd_eq. rgne. rewrite HFs1 Himm4f.
        rewrite -(b_data_cursor (bpa kk) q) /pa_add /add_vec_int. f_equal. }
      assert (HF1s2 : F1 !!! Regidx Rs2
                      = pa_add (b_data (bpa kk)) (4 * NINDIRECT)%nat)
        by (rewrite /F1 upd_ne; [exact HFs2 | nz]).
      assert (HF1s3 : F1 !!! Regidx Rs3 = ip)
        by (rewrite /F1 upd_ne; [exact HFs3 | nz]).
      assert (HF1s4 : F1 !!! Regidx Rs4 = bnode kk)
        by (rewrite /F1 upd_ne; [exact HFs4 | nz]).
      assert (HF1sp : it_sp m F1)
        by (rewrite /it_sp /F1 upd_ne; [exact HFsp | nz]).
      assert (HF1thr : it_thr m F1).
      { intros c Hcs2 N2 N8 N9 N18 N19.
        rewrite /F1 upd_ne; [| regne]. exact (HFthr c Hcs2 N2 N8 N9 N18 N19). }
      assert (Hp68f : add_vec_int (mword_of_int (IT + 0x66) : mword 64) 2
                     = mword_of_int (IT + 0x68)) by pcw.
      iEval (rewrite Hp68f) in "Hpc".
      destruct (decide (S q = NINDIRECT)) as [Hlastf|Hmoref].
      + iApply (wp_beq_taken_s_sconf Φ (mword_of_int (IT + 0x68))
                  (mword_of_int 18 : mword 13) Rs2 Rs1 F1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HF1s1 HF1s2 Hlastf;
                        apply eq_vec_true_iff; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi68 [-]").
        iNext. iIntros (CIDr Hqr) "Hcg Hpc".
        assert (Htgt7af : add_vec (mword_of_int (IT + 0x68) : mword 64)
                           (sign_extend' 64 (mword_of_int 18 : mword 13))
                         = mword_of_int (IT + 0x7a)) by pcw.
        iEval (rewrite Htgt7af) in "Hpc".
        rewrite /it_eexit.
        iDestruct (cpu_own_transport CIDf CIDr 0 true (proc_addr jx) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (wp_next_shift (CIDa := CIDz) (CIDb := CIDr)
                     ltac:(wp_next_chain) with "Hexit") as "Hexit".
        iSpecialize ("Hexit" $! CIDr with "[%]"); [wp_next_chain|].
        rewrite Hlastf.
        iApply ("Hexit" $! F1 with "[%] [%] [%] [%] Hcg Hcnt Hpc Hrun
                                    Hppid Hidev Hsbb Hbuf Hst");
          [exact HF1sp | exact HF1thr | exact HF1s3 | exact HF1s4].
      + assert (Hnef : pa_add (b_data (bpa kk)) (4 * S q)%nat
                      <> pa_add (b_data (bpa kk)) (4 * NINDIRECT)%nat).
        { intros Hz. apply Hmoref.
          apply (b_data_off_inj (bpa kk)); [lia | lia | exact Hz]. }
        iApply (wp_beq_fall_s_sconf Φ (mword_of_int (IT + 0x68))
                  (mword_of_int 18 : mword 13) Rs2 Rs1 F1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HF1s1 HF1s2;
                        apply eq_vec_false_iff; exact Hnef)
                  with "Hcg Hpc Hi68 [-]").
        iIntros (CIDr Hqr) "Hcg Hpc".
        assert (Hp6cf : add_vec_int (mword_of_int (IT + 0x68) : mword 64) 4
                       = mword_of_int (IT + 0x6c)) by pcw.
        iEval (rewrite Hp6cf) in "Hpc".
        assert (Hqf'' : (S q < NINDIRECT)%nat)
          by (clear - Hq Hmoref; unfold NINDIRECT in *; lia).
        assert (Hff'' : (NINDIRECT - S q <= fuel)%nat)
          by (clear - Hq Hfuel Hmoref; unfold NINDIRECT in *; lia).
        iDestruct (cpu_own_transport CIDf CIDr 0 true (proc_addr jx) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (wp_next_shift (CIDa := CIDz) (CIDb := CIDr)
                     ltac:(wp_next_chain) with "Hexit") as "Hexit".
        iApply (IH CIDr (S q) F1 Hqf'' Hff'' HF1sp HF1thr HF1s1 HF1s2 HF1s3 HF1s4
                  with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hprocs Hscheds
                        Hrun Hppid Hidev Hsbb Hdevi Hdgeom Hdlock Hsl
                        Hbuf Hst Hexit").

  Qed.

End ItruncELoop.

(* ===================================================================== *)
(*  THE INDIRECT ARM: +0x50 .. +0x92                                      *)
(*                                                                        *)
(*  Entered only when ip->addrs[NDIRECT] is nonzero.  Saves s4 (the ONLY   *)
(*  path that touches the sixth frame slot), breads the indirect block,    *)
(*  runs the 256-entry loop over it, brelses it, frees the block itself,   *)
(*  clears the cell, restores s4 and rejoins the tail at +0x38.            *)
(* ===================================================================== *)
Section ItruncIArm.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  (* what the arm hands to the tail: the inode names nothing at all *)
  Definition it_armexit `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γ : log_names) (γfs : fs_names) (bn : bio_names)
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z)
      (dev : mword 32) (ip : mword 64) (bm : blkmap)
      (pidv : mword 32) (dq dqd dqb : dfrac) (j : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) : iProp Σ :=
    wp_next b (proc_addr j) (fun (CID : CpuId) =>
      ∀ Mx : regfile,
        ⌜it_sp m Mx⌝ -∗ ⌜it_thr m Mx⌝ -∗ ⌜Mx !!! Regidx Rs3 = ip⌝ -∗
        sie_cap_gpr Mx (K - 6)%nat b (proc_addr j) -∗
        cpu_own 0 true (proc_addr j) C b -∗
        pc_is (mword_of_int (IT + 0x38) : mword 64) -∗
        running_claim j -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        i_dev ip ↦₄{dqd} dev -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈ v) -∗
        inode_map γfs ip bm_empty -∗
        inode_blocks γfs bm_empty (fun _ => replicate BSIZE (bv_0 8)) -∗
        bitmap_res γfs bmapstart cov logstart size (used ∖ bm_blocks bm) -∗
        bslots bn 2 -∗
        bm_paid γ bmapstart 1 -∗
        WP (Loop : expr riscv_lang))%I.

End ItruncIArm.

End ItruncProof.
