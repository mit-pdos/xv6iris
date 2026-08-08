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
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapEnc BitmapInv.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import SpecBread SpecBrelse SpecBfree SpecIupdate.
Require Import SpecItrunc.
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
        park_hlf j true -∗
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
        WP (Loop : expr riscv_lang) {{ Φ }})%I.

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
    park_hlf j true -∗
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
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hgeom Hist Hicov Hilog Hdswf Hj Hgl Hsp Hthr Hs3.
    pose proof HK as HK'. unfold K_itrunc in HK'.
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hlctx #Hprocs #Hscheds Hframe
              Hpark Hppid Hidev Hinum Hsbb Hsbi Hmeta Hmap Hblks Hbmr
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
                    Hsbi Hfsb Hppid Hprocs Hscheds Hpark Hdevi Hdgeom
                    Hdlock Hsl Hop").
    iIntros (CID4 Hq4 mI) "%Hcs1 Hcg Hcnt Hpc Hpark Hppid Hidev Hinum
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
    iApply ("Hcont" $! P6 with "[%] Hcg Hcnt Hpc Hpark Hppid Hidev Hinum
                                 Hsbb Hsbi Hmeta Hmap Hblks Hbmr Hfsb Hsl [Hop]").
    { unfold callee_saved. split_and!; assumption. }
    { iExists u. iSplitR; [iPureIntro; lia|]. iExact "Hop". }
  Qed.

End ItruncTail.

End ItruncProof.
