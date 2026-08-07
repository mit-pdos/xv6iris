(* ProofBmap.v -- bmap over the SIE-agnostic sconf world.

     static uint bmap(struct inode *ip, uint bn) {
       uint addr, *a;  struct buf *bp;
       if(bn < NDIRECT){
         if((addr = ip->addrs[bn]) == 0){
           addr = balloc(ip->dev);
           if(addr == 0) return 0;
           ip->addrs[bn] = addr; }
         return addr; }
       bn -= NDIRECT;
       if(bn < NINDIRECT){
         if((addr = ip->addrs[NDIRECT]) == 0){
           addr = balloc(ip->dev);
           if(addr == 0) return 0;
           ip->addrs[NDIRECT] = addr; }
         bp = bread(ip->dev, addr);
         a = (uint * ) bp->data;
         if((addr = a[bn]) == 0){
           addr = balloc(ip->dev);
           if(addr){ a[bn] = addr; log_write(bp); } }
         brelse(bp);
         return addr; }
       panic("bmap: out of range");
     }

   THE SHAPE OF THE PROOF.  Five live arms and a dead panic, joining at the
   shared epilogue +0x8a.  Four lemmas, entered strictly left to right:

     [bm_epilogue]      +0x8a .. +0x98   the join: a0 := s1, pop the frame,
                                         ret, and discharge the contract.
     [bm_release]       +0x82 .. +0x88   brelse, restore s4, fall into the
                                         epilogue.  THREE of the five arms
                                         end here (indirect hit, indirect
                                         data-balloc failure, indirect
                                         data-balloc success).
     [bm_indirect_tail] +0x62 .. +0x80   bread, read a[bn], and the
                                         allocate-and-log block +0x9a..+0xb0.
     [wp_bmap_sconf]    +0x00 .. +0x60   prologue, the direct arm, and the
                                         indirect head.

   THE s4 QUIRK is what fixes that division.  gcc pushes s4 only on the
   paths that reach bread ([c.sdsp s4,0(sp)] at +0x058 / +0x060) and pops it
   once at +0x088; the direct arm jumps to +0x08a having never touched it.
   So [bm_epilogue] is reached with s4 ALREADY equal to its entry value on
   every arm -- restored on the indirect ones, never written on the direct
   ones -- and its premise is exactly that ([bm_thr5], which covers s4),
   plus frame slot 6 held as an ANONYMOUS word ([bm_frame]).  Only the
   interior lemmas, where s4 really is live, carry the weaker [bm_thr6].

   THE PANIC ARM AT +0x0b2 IS DEAD: [bltu a5,a4] at +0x044 compares 255
   against bn-NDIRECT, and the contract's [fbn < MAXFILE] bounds that by
   255, so the branch always falls through.  Refuted, not proved.

   THE COUPLING THAT MAKES THE INDIRECT ARM WORK is [bm_held_content]: the
   caller's own [fsblock] half for the indirect block (inside [inode_map]'s
   [ind_res]) against the bio handle's machinery half pins the buffer's
   bytes to [ind_bytes (bm_ent bm)] -- so the word the code reads out of
   [bp->data + 4*(bn-12)] IS entry [bn-12] of the pure entry list.

   FRESHNESS.  Each of the three installs has to re-establish
   [blkmap_wf]'s injectivity, and the ONLY thing that can is balloc's
   exclusive [blk_own] token against the tokens inside [inode_map] /
   [inode_blocks] ([InodeInv.inode_fresh]); [fsblock] is a half element and
   two at one key are consistent.  That is also why bmap takes
   [inode_blocks]: the fresh DATA block's half is deposited there. *)
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
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfVc.
Require Import WpSmodeIntr.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SwtchCtx.
Require Import SchedCtx.
Require Import WpUart.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BlockWords.
Require Import InodeInv.
Require Import CodeBmap.
Require Import SpecPanic.
Require Import SpecBalloc SpecBread SpecBrelse SpecLogWrite.
Require Import ProofBmapParts.
Require Import SpecBmap.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

Module BmapProof (BA : BALLOC) (BR : BREAD) (BL : BRELSE) (LW : LOG_WRITE) : BMAP.


Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Rs4 := (mword_of_int 20 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac bmidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* ===================================================================== *)
(*  Vocabulary: the frame, the register-threading invariants, the         *)
(*  continuation.                                                         *)
(* ===================================================================== *)
Section BmapDefs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  (* bmap's 48-byte frame: ra@40 s0@32 s1@24 s2@16 s3@8, and slot 0 --
     s4's home -- held ANONYMOUSLY, because the direct arm never writes it
     and the indirect arms have read it back by the time the epilogue
     runs. *)
  Definition bm_frame (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈ (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈ (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈ (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈ (m !!! Regidx Rs2 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈ (m !!! Regidx Rs3 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈ v))%I.

  (* the frame with slot 0 pinned to s4's entry value: what the indirect
     arms hold between the [c.sdsp s4] and the [c.ldsp s4] *)
  Definition bm_frame4 (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈ (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈ (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈ (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈ (m !!! Regidx Rs2 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈ (m !!! Regidx Rs3 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈ (m !!! Regidx Rs4 : mword 64))%I.

  Lemma bm_frame_of4 (m : regfile) : bm_frame4 m -∗ bm_frame m.
  Proof.
    rewrite /bm_frame4 /bm_frame.
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6)".
    iSplitL "H1"; [iExact "H1"|]. iSplitL "H2"; [iExact "H2"|].
    iSplitL "H3"; [iExact "H3"|]. iSplitL "H4"; [iExact "H4"|].
    iSplitL "H5"; [iExact "H5"|]. iExists _. iExact "H6".
  Qed.

  (* THE CONTINUATION, named so it is not re-traversed by every proofmode
     split (claude-notes/optimization.md). *)
  Definition bm_cont `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γfs : fs_names) (bn : bio_names) (γ : log_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8))
      (fbn : nat) (n : nat)
      (pidv : mword 32) (dq dqd : dfrac) (j : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) : iProp Σ :=
    wp_next b (proc_addr j) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bm' : blkmap) (n' : nat) (data' : nat -> list (bv 8)),
        ⌜callee_saved m mf⌝ -∗
        ⌜blkmap_wf cov logstart bm'⌝ -∗
        ⌜forall i : nat, (i < MAXFILE)%nat -> i <> fbn ->
           blkmap_get bm' i = blkmap_get bm i⌝ -∗
        ⌜forall i : nat, (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) <> 0 ->
           blkmap_get bm' i = blkmap_get bm i⌝ -∗
        ⌜(mf !!! Regidx Ra0 = (mword_of_int 0 : mword 64)
          /\ bv_unsigned (blkmap_get bm' fbn) = 0)
         \/ (mf !!! Regidx Ra0 = sign_extend' 64 (blkmap_get bm' fbn : mword 32)
             /\ bv_unsigned (blkmap_get bm' fbn) <> 0)⌝ -∗
        sie_cap_gpr mf K b (proc_addr j) -∗
        cpu_own 0 true (proc_addr j) C b -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        own_ctx (p_context (proc_addr j)) -∗
        park_hlf j true -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        i_dev ip ↦₄{dqd} dev -∗
        inode_map γfs ip bm' -∗
        ⌜data' = data
         \/ (bv_unsigned (blkmap_get bm fbn) = 0
             /\ data' = <[fbn := replicate BSIZE (bv_0 8)]> data)⌝ -∗
        inode_blocks γfs bm' data' -∗
        bslots bn 3 -∗
        ⌜((n - 5)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
        log_op γ n' -∗
        WP (Loop : expr riscv_lang) {{ Φ }})%I.

End BmapDefs.

(* the two register-threading invariants: [bm_thr5] excludes the five
   registers the frame saves, [bm_thr6] also excludes s4 (live between the
   [c.sdsp s4] and the [c.ldsp s4]) *)
Definition bm_thr5 (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition bm_thr6 (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition bm_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))).

(* ===================================================================== *)
(*  +0x8a .. +0x98 : THE JOIN.                                            *)
(* ===================================================================== *)
Section BmapEpilogue.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  Local Lemma bm_epilogue `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (j : nat) (γfs : fs_names) (bn : bio_names) (γ : log_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (bm bm' : blkmap) (data data' : nat -> list (bv 8))
      (fbn : nat) (n n' : nat) (rv : mword 32)
      (pidv : mword 32) (dq dqd : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ) (b : bool) :
    (K_bmap <= K)%nat ->
    bm_sp m M ->
    bm_thr5 m M ->
    M !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64) ->
    blkmap_wf cov logstart bm' ->
    (forall i : nat, (i < MAXFILE)%nat -> i <> fbn ->
       blkmap_get bm' i = blkmap_get bm i) ->
    (forall i : nat, (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) <> 0 ->
       blkmap_get bm' i = blkmap_get bm i) ->
    ((bv_unsigned rv = 0 /\ bv_unsigned (blkmap_get bm' fbn) = 0)
     \/ (rv = blkmap_get bm' fbn /\ bv_unsigned (blkmap_get bm' fbn) <> 0)) ->
    (data' = data
     \/ (bv_unsigned (blkmap_get bm fbn) = 0
         /\ data' = <[fbn := replicate BSIZE (bv_0 8)]> data)) ->
    ((n - 5)%nat <= n')%nat -> (n' <= n)%nat ->
    sie_cap_gpr M (K - 6)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.bmap + 0x8a) : mword 64) -∗
    bm_frame m -∗
    own_ctx (p_context (proc_addr j)) -∗
    park_hlf j true -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    i_dev ip ↦₄{dqd} dev -∗
    inode_map γfs ip bm' -∗
    inode_blocks γfs bm' data' -∗
    bslots bn 3 -∗
    log_op γ n' -∗
    bm_cont (CID0 := CID0) Φ γfs bn γ cov logstart dev ip bm data fbn n
            pidv dq dqd j m K C b -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hsp Hthr Hs1 Hwf' Hag Hkeep Hrv Hdat Hlo Hhi.
    unfold K_bmap in HK.
    iIntros "Hcg Hcnt #Htext Hpc Hframe Hoctx Hpark Hppid Hidev Hmap Hblocks Hsl Hop Hcont".
    iPoseProof (bmi_8a with "Htext") as "Hi8a".
    iPoseProof (bmi_8c with "Htext") as "Hi8c".
    iPoseProof (bmi_8e with "Htext") as "Hi8e".
    iPoseProof (bmi_90 with "Htext") as "Hi90".
    iPoseProof (bmi_92 with "Htext") as "Hi92".
    iPoseProof (bmi_94 with "Htext") as "Hi94".
    iPoseProof (bmi_96 with "Htext") as "Hi96".
    iPoseProof (bmi_98 with "Htext") as "Hi98".
    rewrite /bm_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6)".
    (* the five loaded slots, at the addresses the [c.ldsp]s form *)
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc2 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc3 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc5 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc6 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    (* ===== +0x8a c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x8a)) Ra0 Rs1
              M (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8a").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (P0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget M Rs1))]> M).
    assert (HP0a0 : P0 !!! Regidx Ra0 = (sign_extend' 64 rv : mword 64)).
    { rewrite /P0 upd_eq. rgne. rewrite Hs1. apply add_vec_zero_l. }
    assert (HP0sp : bm_sp m P0)
      by (rewrite /bm_sp /P0 upd_ne; [exact Hsp | nz]).
    assert (HP0thr : bm_thr5 m P0).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P0 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18 N19). }
    assert (Hpp8c : add_vec_int (mword_of_int (KernelSyms.bmap + 0x8a) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x8c)) by pcw.
    iEval (rewrite Hpp8c) in "Hpc".
    (* ===== +0x8c c.ldsp ra,40(sp) ===== *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x8c)) (mword_of_int 5 : mword 6) Rra
              P0 (K - 6)%nat (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi8c [Hf1]").
    { iEval (rewrite HP0sp -Hsp Hc1). iExact "Hf1". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    iEval (rewrite HP0sp -Hsp Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> P0).
    assert (HP1a0 : P1 !!! Regidx Ra0 = (sign_extend' 64 rv : mword 64))
      by (rewrite /P1 upd_ne; [exact HP0a0 | nz]).
    assert (HP1sp : bm_sp m P1)
      by (rewrite /bm_sp /P1 upd_ne; [exact HP0sp | nz]).
    assert (HP1thr : bm_thr5 m P1).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P1 upd_ne; [| regne]. exact (HP0thr c Hcs N2 N8 N9 N18 N19). }
    assert (HP1ra : P1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (Hpp8e : add_vec_int (mword_of_int (KernelSyms.bmap + 0x8c) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x8e)) by pcw.
    iEval (rewrite Hpp8e) in "Hpc".
    (* ===== +0x8e c.ldsp s0,32(sp) ===== *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x8e)) (mword_of_int 4 : mword 6) Rs0
              P1 (K - 6)%nat (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi8e [Hf2]").
    { iEval (rewrite HP1sp -Hsp Hc2). iExact "Hf2". }
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -Hsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2a0 : P2 !!! Regidx Ra0 = (sign_extend' 64 rv : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (HP2sp : bm_sp m P2)
      by (rewrite /bm_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : bm_thr5 m P2).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P2 upd_ne; [| regne]. exact (HP1thr c Hcs N2 N8 N9 N18 N19). }
    assert (HP2ra : P2 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (Hpp90 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x8e) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x90)) by pcw.
    iEval (rewrite Hpp90) in "Hpc".
    (* ===== +0x90 c.ldsp s1,24(sp) ===== *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x90)) (mword_of_int 3 : mword 6) Rs1
              P2 (K - 6)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi90 [Hf3]").
    { iEval (rewrite HP2sp -Hsp Hc3). iExact "Hf3". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf3".
    iEval (rewrite HP2sp -Hsp Hc3) in "Hf3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3a0 : P3 !!! Regidx Ra0 = (sign_extend' 64 rv : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2a0 | nz]).
    assert (HP3sp : bm_sp m P3)
      by (rewrite /bm_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (HP3thr : bm_thr5 m P3).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P3 upd_ne; [| regne]. exact (HP2thr c Hcs N2 N8 N9 N18 N19). }
    assert (HP3ra : P3 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    assert (Hpp92 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x90) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x92)) by pcw.
    iEval (rewrite Hpp92) in "Hpc".
    (* ===== +0x92 c.ldsp s2,16(sp) ===== *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x92)) (mword_of_int 2 : mword 6) Rs2
              P3 (K - 6)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi92 [Hf4]").
    { iEval (rewrite HP3sp -Hsp Hc4). iExact "Hf4". }
    iIntros (CID5 Hq5) "Hcg Hpc Hf4".
    iEval (rewrite HP3sp -Hsp Hc4) in "Hf4".
    set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    assert (HP4a0 : P4 !!! Regidx Ra0 = (sign_extend' 64 rv : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3a0 | nz]).
    assert (HP4sp : bm_sp m P4)
      by (rewrite /bm_sp /P4 upd_ne; [exact HP3sp | nz]).
    assert (HP4thr : bm_thr5 m P4).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P4 upd_ne; [| regne]. exact (HP3thr c Hcs N2 N8 N9 N18 N19). }
    assert (HP4ra : P4 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3ra | nz]).
    assert (Hpp94 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x92) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x94)) by pcw.
    iEval (rewrite Hpp94) in "Hpc".
    (* ===== +0x94 c.ldsp s3,8(sp) ===== *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x94)) (mword_of_int 1 : mword 6) Rs3
              P4 (K - 6)%nat (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi94 [Hf5]").
    { iEval (rewrite HP4sp -Hsp Hc5). iExact "Hf5". }
    iIntros (CID6 Hq6) "Hcg Hpc Hf5".
    iEval (rewrite HP4sp -Hsp Hc5) in "Hf5".
    set (P5 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> P4).
    assert (HP5a0 : P5 !!! Regidx Ra0 = (sign_extend' 64 rv : mword 64))
      by (rewrite /P5 upd_ne; [exact HP4a0 | nz]).
    assert (HP5sp : bm_sp m P5)
      by (rewrite /bm_sp /P5 upd_ne; [exact HP4sp | nz]).
    assert (HP5thr : bm_thr5 m P5).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P5 upd_ne; [| regne]. exact (HP4thr c Hcs N2 N8 N9 N18 N19). }
    assert (HP5ra : P5 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P5 upd_ne; [exact HP4ra | nz]).
    assert (Hpp96 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x94) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x96)) by pcw.
    iEval (rewrite Hpp96) in "Hpc".
    (* ===== +0x96 c.addi16sp sp,48 : pop ===== *)
    iDestruct "Hf6" as (vfr) "Hf6".
    assert (Hwv : add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP5sp. apply bv_eq.
      rewrite !add_vec64_unsigned.
      rewrite bv_wrap_add_idemp_l.
      assert (Hz : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)) : mword 64)
                   = 18446744073709551568) by (vm_compute; reflexivity).
      assert (Hz2 : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)) : mword 64)
                    = 48) by (vm_compute; reflexivity).
      rewrite Hz Hz2.
      replace (bv_unsigned (m !!! Regidx csp_rs1 : mword 64) + 18446744073709551568 + 48)
        with (bv_unsigned (m !!! Regidx csp_rs1 : mword 64) + 18446744073709551616) by ring.
      rewrite -bv_wrap_add_idemp_r.
      assert (Hm0 : bv_wrap 64 18446744073709551616 = 0) by (vm_compute; reflexivity).
      rewrite Hm0 Z.add_0_r.
      apply bv_wrap_small. apply bv_unsigned_in_range. }
    assert (Hpop : (P5 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hwv HP5sp. unfold pa_stk, add_vec_int.
      apply f_equal. pcw. }
    iAssert (stack_own (m !!! Regidx csp_rs1 : mword 64) 6)
      with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6]" as "Hstk".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1"|].
      iSplitL "Hf2"; [iExists _; iExact "Hf2"|].
      iSplitL "Hf3"; [iExists _; iExact "Hf3"|].
      iSplitL "Hf4"; [iExists _; iExact "Hf4"|].
      iSplitL "Hf5"; [iExists _; iExact "Hf5"|].
      iSplitL "Hf6"; [iExists _; iExact "Hf6"|].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x96))
              (mword_of_int 3 : mword 6) P5 (K - 6)%nat 6 b Hpop
              with "Hcg Hpc Hi96 Hstk").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (P6 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> P5).
    assert (Hnk : ((K - 6) + 6)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp98 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x96) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x98)) by pcw.
    iEval (rewrite Hpp98) in "Hpc".
    (* ===== +0x98 c.ret ===== *)
    assert (HP6ra : P6 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P6 upd_ne; [exact HP5ra | nz]).
    iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x98)) Rra P6 K b ltac:(nz)
              with "Hcg Hpc Hi98").
    iIntros (CID8 Hq8) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P6 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP6ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
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
    assert (Hfin : bm_thr5 m P6).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P6 upd_ne; [| regne]. exact (HP5thr c Hcs N2 N8 N9 N18 N19). }
    assert (Cs4 : P6 !!! Regidx (mword_of_int 20 : mword 5)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; bmidx).
    assert (Cs5 : P6 !!! Regidx (mword_of_int 21 : mword 5)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; bmidx).
    assert (Cs6 : P6 !!! Regidx (mword_of_int 22 : mword 5)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; bmidx).
    assert (Cs7 : P6 !!! Regidx (mword_of_int 23 : mword 5)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; bmidx).
    assert (Cs8 : P6 !!! Regidx (mword_of_int 24 : mword 5)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; bmidx).
    assert (Cs9 : P6 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; bmidx).
    assert (Cs10 : P6 !!! Regidx (mword_of_int 26 : mword 5)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; bmidx).
    assert (Cs11 : P6 !!! Regidx (mword_of_int 27 : mword 5)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; bmidx).
    assert (HP6a0 : P6 !!! Regidx Ra0 = (sign_extend' 64 rv : mword 64))
      by (rewrite /P6 upd_ne; [exact HP5a0 | nz]).
    iDestruct (cpu_own_transport CID0 CID8 0 true (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    rewrite /bm_cont.
    iSpecialize ("Hcont" $! CID8 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P6 bm' n' data' with "[%] [%] [%] [%] [%] Hcg Hcnt Hpc Hoctx Hpark
                     Hppid Hidev Hmap [%] Hblocks Hsl [%] Hop").
    { unfold callee_saved. split_and!; assumption. }
    { exact Hwf'. }
    { exact Hag. }
    { exact Hkeep. }
    { destruct Hrv as [[Hz Hz'] | [He Hne]].
      - left. split; [rewrite HP6a0; exact (bm_sext_zero rv Hz) | exact Hz'].
      - right. split; [rewrite HP6a0 He; reflexivity | exact Hne]. }
    { exact Hdat. }
    { split; assumption. }
  Qed.

End BmapEpilogue.

(* ===================================================================== *)
(*  +0x82 .. +0x88 : brelse, restore s4, fall into the epilogue.          *)
(*  Reached by THREE of the five arms.                                    *)
(* ===================================================================== *)
Section BmapRelease.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  Local Lemma bm_release `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat)
      (γfs : fs_names) (γd : disk_names) (bn : bio_names) (γ : log_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (bm bm' : blkmap) (data data' : nat -> list (bv 8))
      (fbn : nat) (n n' : nat) (rv : mword 32)
      (kk : nat) (ibn : mword 32) (bsX bsdX : list (bv 8)) (dX : bool)
      (pidv : mword 32) (dq dqd : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ) (b : bool) :
    (K_bmap <= K)%nat ->
    bm_sp m M ->
    bm_thr6 m M ->
    M !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64) ->
    M !!! Regidx Rs4 = bnode kk ->
    (kk < NBUF)%nat ->
    blkmap_wf cov logstart bm' ->
    (forall i : nat, (i < MAXFILE)%nat -> i <> fbn ->
       blkmap_get bm' i = blkmap_get bm i) ->
    (forall i : nat, (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) <> 0 ->
       blkmap_get bm' i = blkmap_get bm i) ->
    ((bv_unsigned rv = 0 /\ bv_unsigned (blkmap_get bm' fbn) = 0)
     \/ (rv = blkmap_get bm' fbn /\ bv_unsigned (blkmap_get bm' fbn) <> 0)) ->
    (data' = data
     \/ (bv_unsigned (blkmap_get bm fbn) = 0
         /\ data' = <[fbn := replicate BSIZE (bv_0 8)]> data)) ->
    ((n - 5)%nat <= n')%nat -> (n' <= n)%nat ->
    sie_cap_gpr M (K - 6)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.bmap + 0x82) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    procs_inv Φ γs -∗
    bm_frame4 m -∗
    own_ctx (p_context (proc_addr j)) -∗
    park_hlf j true -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    i_dev ip ↦₄{dqd} dev -∗
    inode_map γfs ip bm' -∗
    inode_blocks γfs bm' data' -∗
    bslots bn 2 -∗
    log_op γ n' -∗
    bio_locked bn (fs_view γfs γd dev cov) kk pidv dev ibn bsX bsdX dX -∗
    bm_cont (CID0 := CID0) Φ γfs bn γ cov logstart dev ip bm data fbn n
            pidv dq dqd j m K C b -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hsp Hthr Hs1 Hs4 Hkk Hwf' Hag Hkeep Hrv Hdat Hlo Hhi.
    pose proof HK as HK'. unfold K_bmap in HK'.
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hprocs Hframe Hoctx Hpark Hppid
              Hidev Hmap Hblocks Hsl Hop Hlk Hcont".
    iPoseProof (bmi_82 with "Htext") as "Hi82".
    iPoseProof (bmi_84 with "Htext") as "Hi84".
    iPoseProof (bmi_88 with "Htext") as "Hi88".
    (* ===== +0x82 c.mv a0,s4 ===== *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x82)) Ra0 Rs4
              M (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi82").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (T0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget M Rs4))]> M).
    assert (HT0a0 : T0 !!! Regidx Ra0 = bnode kk).
    { rewrite /T0 upd_eq. rgne. rewrite Hs4. apply add_vec_zero_l. }
    assert (HT0s1 : T0 !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs1 | nz]).
    assert (HT0sp : bm_sp m T0)
      by (rewrite /bm_sp /T0 upd_ne; [exact Hsp | nz]).
    assert (HT0thr : bm_thr6 m T0).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite /T0 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18 N19 N20). }
    assert (Hpp84 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x82) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x84)) by pcw.
    iEval (rewrite Hpp84) in "Hpc".
    (* ===== +0x84 jal ra,brelse ===== *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x84)) Rra
              (mword_of_int 2096414 : mword 21) T0 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi84").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (T1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.bmap + 0x84) : mword 64) 4)]> T0).
    assert (Htgt : add_vec (mword_of_int (KernelSyms.bmap + 0x84) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096414 : mword 21))
                   = mword_of_int KernelSyms.brelse) by pcw.
    iEval (rewrite Htgt) in "Hpc".
    assert (HT1a0 : T1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /T1 upd_ne; [exact HT0a0 | nz]).
    assert (HT1s1 : T1 !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s1 | nz]).
    assert (HT1sp : bm_sp m T1)
      by (rewrite /bm_sp /T1 upd_ne; [exact HT0sp | nz]).
    assert (HT1ra : T1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.bmap + 0x84) : mword 64) 4)
      by (rewrite /T1; apply upd_eq).
    assert (HT1thr : bm_thr6 m T1).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite /T1 upd_ne; [| regne]. exact (HT0thr c Hcs N2 N8 N9 N18 N19 N20). }
    iDestruct (cpu_own_transport CID0 CID2 0 true (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (CIDa := CID0) (CIDb := CID2) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbl : (K_brelse <= K - 6)%nat) by (unfold K_brelse; lia).
    iApply (BL.wp_brelse_sconf Φ γs bn (fs_view γfs γd dev cov) kk
              pidv dev ibn dq T1 (K - 6)%nat true (proc_addr j) C bsX bsdX dX b
              HKbl Hkk HT1a0
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hppid Hprocs Hlk").
    iIntros (CID3 Hq3 mR) "%Hcs1 Hcg Hcnt Hpc Hppid Hsl1".
    assert (Hpc88 : ret_pc (T1 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.bmap + 0x88)).
    { rewrite HT1ra. pcw. }
    iEval (rewrite Hpc88) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmRs1 : mR !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HT1s1).
    assert (HmRsp : bm_sp m mR).
    { rewrite /bm_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HT1sp. }
    assert (HmRthr : bm_thr6 m mR).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HT1thr c Hcs N2 N8 N9 N18 N19 N20). }
    (* ===== +0x88 c.ldsp s4,0(sp) : the ONLY s4 restore ===== *)
    rewrite /bm_frame4.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6)".
    assert (Hc6 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x88)) (mword_of_int 0 : mword 6) Rs4
              mR (K - 6)%nat (m !!! Regidx Rs4 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi88 [Hf6]").
    { iEval (rewrite Hc6). iExact "Hf6". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf6".
    iEval (rewrite Hc6) in "Hf6".
    set (T2 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> mR).
    assert (HT2s1 : T2 !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64))
      by (rewrite /T2 upd_ne; [exact HmRs1 | nz]).
    assert (HT2sp : bm_sp m T2)
      by (rewrite /bm_sp /T2 upd_ne; [exact HmRsp | nz]).
    assert (HT2thr : bm_thr5 m T2).
    { intros c Hcs N2 N8 N9 N18 N19.
      destruct (decide (c = (mword_of_int 20 : mword 5))) as [->|N20].
      - rewrite /T2 upd_eq. reflexivity.
      - rewrite /T2 upd_ne; [| intro Hq; apply N20; exact (regidx_inj _ _ Hq)].
        exact (HmRthr c Hcs N2 N8 N9 N18 N19 N20). }
    assert (Hpp8a : add_vec_int (mword_of_int (KernelSyms.bmap + 0x88) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x8a)) by pcw.
    iEval (rewrite Hpp8a) in "Hpc".
    iAssert (bm_frame m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6]" as "Hframe".
    { rewrite /bm_frame.
      iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
      iSplitL "Hf5"; [iExact "Hf5"|]. iExists _. iExact "Hf6". }
    iDestruct (bm_slots_join bn 2 1 with "Hsl Hsl1") as "Hsl".
    iDestruct (cpu_own_transport CID3 CID4 0 true (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (bm_epilogue (CID0 := CID4) Φ j γfs bn γ cov logstart dev ip bm bm'
              data data' fbn n n' rv pidv dq dqd m T2 K C b
              HK HT2sp HT2thr HT2s1 Hwf' Hag Hkeep Hrv Hdat Hlo Hhi
              with "Hcg Hcnt Htext Hpc Hframe Hoctx Hpark Hppid Hidev Hmap
                    Hblocks [Hsl] Hop [Hcont]").
    { iExact "Hsl". }
    { iApply (wp_next_shift (CIDa := CID2) (CIDb := CID4) ltac:(wp_next_chain)
                with "Hcont"). }
  Qed.

End BmapRelease.

(* ===================================================================== *)
(*  +0x62 .. +0x80 and +0x9a .. +0xb0 : bread the indirect block, read    *)
(*  entry bn-NDIRECT, and (if it is empty) allocate one and log it.       *)
(* ===================================================================== *)
Section BmapTail.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  Local Lemma bm_indirect_tail `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (γfs : fs_names) (bn : bio_names) (γ : log_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (bm bmI : blkmap) (data : nat -> list (bv 8))
      (fbn q : nat) (n nI : nat)
      (pidv : mword 32) (dq dqd : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ) (b : bool) :
    (K_bmap <= K)%nat ->
    log_geom_ok cov logstart ->
    blkmap_wf cov logstart bmI ->
    fbn = (NDIRECT + q)%nat ->
    (q < NINDIRECT)%nat ->
    (forall i : nat, (i < MAXFILE)%nat -> blkmap_get bmI i = blkmap_get bm i) ->
    bv_unsigned (bm_ind bmI) <> 0 ->
    (3 <= nI)%nat -> ((n - 2)%nat <= nI)%nat -> (nI <= n)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    bm_sp m M ->
    bm_thr6 m M ->
    M !!! Regidx Rs1 = (sign_extend' 64 (bm_ind bmI : mword 32) : mword 64) ->
    M !!! Regidx Rs2 = ip ->
    M !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64) ->
    sie_cap_gpr M (K - 6)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.bmap + 0x62) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv Φ γs -∗
    scheds_inv Φ γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bm_frame4 m -∗
    own_ctx (p_context (proc_addr j)) -∗
    park_hlf j true -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    i_dev ip ↦₄{dqd} dev -∗
    inode_addrs ip (bm_cells bmI) -∗
    ind_blk γfs bmI -∗
    ind_tok γfs bmI -∗
    inode_blocks γfs bmI data -∗
    bslots bn 3 -∗
    log_op γ nI -∗
    bm_cont (CID0 := CID0) Φ γfs bn γ cov logstart dev ip bm data fbn n
            pidv dq dqd j m K C b -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hgeom HwfI Hfbn Hq Hagr Hindnz Hn3 Hnlo Hnhi Hj Hgl
           Hsp Hthr Hs1 Hs2 Hs3.
    pose proof HK as HK'. unfold K_bmap in HK'.
    assert (Hgeom0 : log_geom_ok cov logstart) by exact Hgeom.
    destruct Hgeom as [Hcovok Hlogsub].
    (* the indirect block is a covered home block with a small number *)
    destruct (blkmap_wf_ind_cov cov logstart bmI HwfI Hindnz) as [Hicov Hilog].
    destruct (Hcovok _ Hicov) as [Hipos Hilt].
    assert (Huind : uint (bm_ind bmI : mword 32) = bv_unsigned (bm_ind bmI)) by apply bb_uint32.
    assert (Hicov' : uint (bm_ind bmI : mword 32) ∈ bv_cov (fs_view γfs γd dev cov))
      by (rewrite Huind; exact Hicov).
    assert (Hilt' : (uint (bm_ind bmI : mword 32) < 2147483648)%Z).
    { rewrite Huind. change (2 ^ 31)%Z with 2147483648%Z in Hilt. lia. }
    assert (Hqu : bv_unsigned (mword_of_int (Z.of_nat q) : mword 64) = Z.of_nat q).
    { rewrite moi64_unsigned. apply bvw64_small.
      unfold NINDIRECT in Hq. change (2 ^ 64)%Z with 18446744073709551616%Z. lia. }
    assert (Hqlt : bv_unsigned (mword_of_int (Z.of_nat q) : mword 64) < 4294967296)
      by (rewrite Hqu; unfold NINDIRECT in Hq; lia).
    assert (Hgetq : blkmap_get bmI fbn = bm_ent bmI !!! q).
    { rewrite (blkmap_get_ent bmI fbn ltac:(lia)).
      f_equal. unfold NDIRECT in *. lia. }
    assert (Hentlen : length (bm_ent bmI) = 256%nat)
      by exact (blkmap_wf_ent_len cov logstart bmI HwfI).
    assert (Hfbnlt : (fbn < MAXFILE)%nat)
      by (unfold MAXFILE, NDIRECT, NINDIRECT in *; lia).
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hlctx #Hprocs #Hscheds
              #Hdevi #Hdgeom #Hdlock Hframe Hoctx Hpark Hppid Hidev
              Haddrs Hindblk Hindtok Hblocks Hsl Hop Hcont".
    iPoseProof (bmi_62 with "Htext") as "Hi62".
    iPoseProof (bmi_64 with "Htext") as "Hi64".
    iPoseProof (bmi_68 with "Htext") as "Hi68".
    (* ===== +0x62 c.mv a1,s1 ===== *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x62)) Ra1 Rs1
              M (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi62").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (I0 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget M Rs1))]> M).
    assert (HI0a1 : I0 !!! Regidx Ra1 = (sign_extend' 64 (bm_ind bmI : mword 32) : mword 64)).
    { rewrite /I0 upd_eq. rgne. rewrite Hs1. apply add_vec_zero_l. }
    assert (HI0s2 : I0 !!! Regidx Rs2 = ip)
      by (rewrite /I0 upd_ne; [exact Hs2 | nz]).
    assert (HI0s3 : I0 !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64))
      by (rewrite /I0 upd_ne; [exact Hs3 | nz]).
    assert (HI0sp : bm_sp m I0)
      by (rewrite /bm_sp /I0 upd_ne; [exact Hsp | nz]).
    assert (HI0thr : bm_thr6 m I0).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite /I0 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18 N19 N20). }
    assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x62) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x64)) by pcw.
    iEval (rewrite Hpp64) in "Hpc".
    (* ===== +0x64 lw a0,0(s2) : a0 := ip->dev ===== *)
    assert (Hdadr : add_vec (rget I0 Rs2) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = i_dev ip).
    { rgne. rewrite HI0s2. reflexivity. }
    iEval (rewrite -Hdadr) in "Hidev".
    iApply (wp_lw_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x64)) Ra0 Rs2
              (mword_of_int 0 : mword 12) I0 (K - 6)%nat dev b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi64 Hidev").
    iIntros (CID2 Hq2) "Hcg Hpc Hidev".
    iEval (rewrite Hdadr) in "Hidev".
    set (I1 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> I0).
    assert (HI1a0 : I1 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /I1; apply upd_eq).
    assert (HI1a1 : I1 !!! Regidx Ra1 = (sign_extend' 64 (bm_ind bmI : mword 32) : mword 64))
      by (rewrite /I1 upd_ne; [exact HI0a1 | nz]).
    assert (HI1s2 : I1 !!! Regidx Rs2 = ip)
      by (rewrite /I1 upd_ne; [exact HI0s2 | nz]).
    assert (HI1s3 : I1 !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64))
      by (rewrite /I1 upd_ne; [exact HI0s3 | nz]).
    assert (HI1sp : bm_sp m I1)
      by (rewrite /bm_sp /I1 upd_ne; [exact HI0sp | nz]).
    assert (HI1thr : bm_thr6 m I1).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite /I1 upd_ne; [| regne]. exact (HI0thr c Hcs N2 N8 N9 N18 N19 N20). }
    assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x64) : mword 64) 4
                    = mword_of_int (KernelSyms.bmap + 0x68)) by pcw.
    iEval (rewrite Hpp68) in "Hpc".
    (* ===== +0x68 jal ra,bread ===== *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x68)) Rra
              (mword_of_int 2096178 : mword 21) I1 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi68").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (I2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.bmap + 0x68) : mword 64) 4)]> I1).
    assert (Htgtbr : add_vec (mword_of_int (KernelSyms.bmap + 0x68) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096178 : mword 21))
                     = mword_of_int KernelSyms.bread) by pcw.
    iEval (rewrite Htgtbr) in "Hpc".
    assert (HI2a0 : I2 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /I2 upd_ne; [exact HI1a0 | nz]).
    assert (HI2a1 : I2 !!! Regidx Ra1 = (sign_extend' 64 (bm_ind bmI : mword 32) : mword 64))
      by (rewrite /I2 upd_ne; [exact HI1a1 | nz]).
    assert (HI2s2 : I2 !!! Regidx Rs2 = ip)
      by (rewrite /I2 upd_ne; [exact HI1s2 | nz]).
    assert (HI2s3 : I2 !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64))
      by (rewrite /I2 upd_ne; [exact HI1s3 | nz]).
    assert (HI2sp : bm_sp m I2)
      by (rewrite /bm_sp /I2 upd_ne; [exact HI1sp | nz]).
    assert (HI2ra : I2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.bmap + 0x68) : mword 64) 4)
      by (rewrite /I2; apply upd_eq).
    assert (HI2thr : bm_thr6 m I2).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite /I2 upd_ne; [| regne]. exact (HI1thr c Hcs N2 N8 N9 N18 N19 N20). }
    iDestruct (cpu_own_transport CID0 CID3 0 true (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (CIDa := CID0) (CIDb := CID3) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbr : (K_bread <= K - 6)%nat) by (unfold K_bread; lia).
    iDestruct (bm_slots_split bn 2 1 with "Hsl") as "[Hsl Hsl1]".
    iApply (BR.wp_bread_sconf Φ γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev (bm_ind bmI) dq
              I2 (K - 6)%nat true C b
              HKbr Hilt' eq_refl Hicov' eq_refl Hj Hgl HI2a0 HI2a1 eq_refl
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hppid Hprocs Hscheds Hoctx Hpark
                    Hdevi Hdgeom Hdlock Hsl1").
    iIntros (CID4 Hq4 mB kk bs0 bsd0 d0) "%Hfacts Hcg Hcnt Hpc Hoctx Hpark Hppid Hheld".
    destruct Hfacts as [Hcs1 HmBa0].
    assert (Hpc6c : ret_pc (I2 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.bmap + 0x6c)) by (rewrite HI2ra; pcw).
    iEval (rewrite Hpc6c) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmBs2 : mB !!! Regidx Rs2 = ip)
      by (rewrite (callee_saved_lookup Hcs1_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HI2s2).
    assert (HmBs3 : mB !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs3 ltac:(vm_compute; reflexivity));
          exact HI2s3).
    assert (HmBsp : bm_sp m mB).
    { rewrite /bm_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HI2sp. }
    assert (HmBthr : bm_thr6 m mB).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HI2thr c Hcs N2 N8 N9 N18 N19 N20). }
    (* THE COUPLING: the buffer's bytes ARE the entry list's byte image *)
    iEval (rewrite /bio_locked) in "Hheld".
    iDestruct (bm_held_k with "Hheld") as %Hkk.
    iEval (rewrite /ind_blk) in "Hindblk".
    destruct (decide (bv_unsigned (bm_ind bmI) = 0)) as [Hz0|_];
      [exfalso; exact (Hindnz Hz0)|].
    iEval (rewrite -Huind) in "Hindblk".
    iDestruct (bm_held_content with "Hindblk Hheld") as %Hbs0.
    subst bs0.
    iDestruct (bm_held_swap with "Hheld") as "[Hbuf Hheldback]".
    (* ===== +0x6c c.mv s4,a0 ===== *)
    iPoseProof (bmi_6c with "Htext") as "Hi6c".
    iPoseProof (bmi_6e with "Htext") as "Hi6e".
    iPoseProof (bmi_72 with "Htext") as "Hi72".
    iPoseProof (bmi_76 with "Htext") as "Hi76".
    iPoseProof (bmi_7a with "Htext") as "Hi7a".
    iPoseProof (bmi_7c with "Htext") as "Hi7c".
    iPoseProof (bmi_7e with "Htext") as "Hi7e".
    iPoseProof (bmi_80 with "Htext") as "Hi80".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x6c)) Rs4 Ra0
              mB (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi6c").
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (B1 := <[Regidx Rs4 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mB Ra0))]> mB).
    assert (HB1s4 : B1 !!! Regidx Rs4 = bnode kk).
    { rewrite /B1 upd_eq. rgne. rewrite HmBa0. apply add_vec_zero_l. }
    assert (HB1a0 : B1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B1 upd_ne; [exact HmBa0 | nz]).
    assert (HB1s2 : B1 !!! Regidx Rs2 = ip)
      by (rewrite /B1 upd_ne; [exact HmBs2 | nz]).
    assert (HB1s3 : B1 !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64))
      by (rewrite /B1 upd_ne; [exact HmBs3 | nz]).
    assert (HB1sp : bm_sp m B1)
      by (rewrite /bm_sp /B1 upd_ne; [exact HmBsp | nz]).
    assert (HB1thr : bm_thr6 m B1).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite /B1 upd_ne; [| intro Hqq; apply N20; exact (regidx_inj _ _ Hqq)].
      exact (HmBthr c Hcs N2 N8 N9 N18 N19 N20). }
    assert (Hpp6e : add_vec_int (mword_of_int (KernelSyms.bmap + 0x6c) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x6e)) by pcw.
    iEval (rewrite Hpp6e) in "Hpc".
    (* ===== +0x6e addi a5,a0,88 : a5 := bp->data ===== *)
    iApply (wp_addi4_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x6e)) Ra5 Ra0
              (mword_of_int 88 : mword 12) B1 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi6e").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (B2 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget B1 Ra0) (sign_extend' 64 (mword_of_int 88 : mword 12)))]> B1).
    assert (HB2a5 : B2 !!! Regidx Ra5 = b_data (bnode kk)).
    { rewrite /B2 upd_eq. rgne. rewrite HB1a0. apply bm_data_addr. }
    assert (HB2s3 : B2 !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64))
      by (rewrite /B2 upd_ne; [exact HB1s3 | nz]).
    assert (HB2s4 : B2 !!! Regidx Rs4 = bnode kk)
      by (rewrite /B2 upd_ne; [exact HB1s4 | nz]).
    assert (HB2s2 : B2 !!! Regidx Rs2 = ip)
      by (rewrite /B2 upd_ne; [exact HB1s2 | nz]).
    assert (HB2sp : bm_sp m B2)
      by (rewrite /bm_sp /B2 upd_ne; [exact HB1sp | nz]).
    assert (HB2thr : bm_thr6 m B2).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite /B2 upd_ne; [| regne]. exact (HB1thr c Hcs N2 N8 N9 N18 N19 N20). }
    assert (Hpp72 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x6e) : mword 64) 4
                    = mword_of_int (KernelSyms.bmap + 0x72)) by pcw.
    iEval (rewrite Hpp72) in "Hpc".
    (* ===== +0x72 slli a4,s3,0x20 ===== *)
    iApply (wp_slli_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x72)) Ra4 Rs3
              (mword_of_int 32 : mword 6)
              (shift_bits_left (mword_of_int (Z.of_nat q) : mword 64)
                 (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
              B2 (K - 6)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HB2s3; reflexivity) with "Hcg Hpc Hi72").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (B3 := <[Regidx Ra4 := regval_into_reg
                  (shift_bits_left (mword_of_int (Z.of_nat q) : mword 64)
                     (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> B2).
    assert (HB3a4 : B3 !!! Regidx Ra4
                    = shift_bits_left (mword_of_int (Z.of_nat q) : mword 64)
                        (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
      by (rewrite /B3; apply upd_eq).
    assert (HB3a5 : B3 !!! Regidx Ra5 = b_data (bnode kk))
      by (rewrite /B3 upd_ne; [exact HB2a5 | nz]).
    assert (HB3s3 : B3 !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64))
      by (rewrite /B3 upd_ne; [exact HB2s3 | nz]).
    assert (HB3s4 : B3 !!! Regidx Rs4 = bnode kk)
      by (rewrite /B3 upd_ne; [exact HB2s4 | nz]).
    assert (HB3s2 : B3 !!! Regidx Rs2 = ip)
      by (rewrite /B3 upd_ne; [exact HB2s2 | nz]).
    assert (HB3sp : bm_sp m B3)
      by (rewrite /bm_sp /B3 upd_ne; [exact HB2sp | nz]).
    assert (HB3thr : bm_thr6 m B3).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite /B3 upd_ne; [| regne]. exact (HB2thr c Hcs N2 N8 N9 N18 N19 N20). }
    assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x72) : mword 64) 4
                    = mword_of_int (KernelSyms.bmap + 0x76)) by pcw.
    iEval (rewrite Hpp76) in "Hpc".
    (* ===== +0x76 srli a1,a4,0x1e : a1 := 4*(bn-NDIRECT) ===== *)
    iApply (wp_srli4_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x76)) Ra1 Ra4
              (mword_of_int 30 : mword 6) B3 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi76").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (B4 := <[Regidx Ra1 := regval_into_reg
                  (shift_bits_right (rget B3 Ra4)
                     (subrange_vec_dec (mword_of_int 30 : mword 6) (Z.sub log2_xlen 1) 0))]> B3).
    assert (HB4a1 : B4 !!! Regidx Ra1 = (mword_of_int (4 * Z.of_nat q) : mword 64)).
    { rewrite /B4 upd_eq. rgne. rewrite HB3a4.
      rewrite (bm_slli32_srli30 (mword_of_int (Z.of_nat q) : mword 64) Hqlt) Hqu.
      reflexivity. }
    assert (HB4a5 : B4 !!! Regidx Ra5 = b_data (bnode kk))
      by (rewrite /B4 upd_ne; [exact HB3a5 | nz]).
    assert (HB4s4 : B4 !!! Regidx Rs4 = bnode kk)
      by (rewrite /B4 upd_ne; [exact HB3s4 | nz]).
    assert (HB4s2 : B4 !!! Regidx Rs2 = ip)
      by (rewrite /B4 upd_ne; [exact HB3s2 | nz]).
    assert (HB4sp : bm_sp m B4)
      by (rewrite /bm_sp /B4 upd_ne; [exact HB3sp | nz]).
    assert (HB4thr : bm_thr6 m B4).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite /B4 upd_ne; [| regne]. exact (HB3thr c Hcs N2 N8 N9 N18 N19 N20). }
    assert (Hpp7a : add_vec_int (mword_of_int (KernelSyms.bmap + 0x76) : mword 64) 4
                    = mword_of_int (KernelSyms.bmap + 0x7a)) by pcw.
    iEval (rewrite Hpp7a) in "Hpc".
    (* ===== +0x7a c.add a5,a5,a1 : a5 := &a[bn] ===== *)
    iApply (wp_cadd_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x7a)) Ra5 Ra1
              B4 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7a").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (B5 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget B4 Ra5) (rget B4 Ra1))]> B4).
    assert (HB5a5 : B5 !!! Regidx Ra5 = pa_add (b_data (bnode kk)) (4 * q)%nat).
    { rewrite /B5 upd_eq. rgne. rgne. rewrite HB4a5 HB4a1. apply bm_slot_addr. }
    assert (HB5s4 : B5 !!! Regidx Rs4 = bnode kk)
      by (rewrite /B5 upd_ne; [exact HB4s4 | nz]).
    assert (HB5s2 : B5 !!! Regidx Rs2 = ip)
      by (rewrite /B5 upd_ne; [exact HB4s2 | nz]).
    assert (HB5sp : bm_sp m B5)
      by (rewrite /bm_sp /B5 upd_ne; [exact HB4sp | nz]).
    assert (HB5thr : bm_thr6 m B5).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite /B5 upd_ne; [| regne]. exact (HB4thr c Hcs N2 N8 N9 N18 N19 N20). }
    assert (Hpp7c : add_vec_int (mword_of_int (KernelSyms.bmap + 0x7a) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x7c)) by pcw.
    iEval (rewrite Hpp7c) in "Hpc".
    (* ===== +0x7c c.mv s3,a5 ===== *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x7c)) Rs3 Ra5
              B5 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7c").
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (B6 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget B5 Ra5))]> B5).
    assert (HB6s3 : B6 !!! Regidx Rs3 = pa_add (b_data (bnode kk)) (4 * q)%nat).
    { rewrite /B6 upd_eq. rgne. rewrite HB5a5. apply add_vec_zero_l. }
    assert (HB6a5 : B6 !!! Regidx Ra5 = pa_add (b_data (bnode kk)) (4 * q)%nat)
      by (rewrite /B6 upd_ne; [exact HB5a5 | nz]).
    assert (HB6s4 : B6 !!! Regidx Rs4 = bnode kk)
      by (rewrite /B6 upd_ne; [exact HB5s4 | nz]).
    assert (HB6s2 : B6 !!! Regidx Rs2 = ip)
      by (rewrite /B6 upd_ne; [exact HB5s2 | nz]).
    assert (HB6sp : bm_sp m B6)
      by (rewrite /bm_sp /B6 upd_ne; [exact HB5sp | nz]).
    assert (HB6thr : bm_thr6 m B6).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite /B6 upd_ne; [| regne]. exact (HB5thr c Hcs N2 N8 N9 N18 N19 N20). }
    assert (Hpp7e : add_vec_int (mword_of_int (KernelSyms.bmap + 0x7c) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x7e)) by pcw.
    iEval (rewrite Hpp7e) in "Hpc".
    (* ===== +0x7e c.lw s1,0(a5) : the entry ===== *)
    assert (Hal : is_aligned_paddr
                    (Physaddr (pa_add (b_data (bnode kk)) (4 * q)%nat)) 4 = true)
      by (apply bm_align4; [exact Hkk | unfold NINDIRECT in Hq; lia]).
    iDestruct (bm_buf_word_acc (bpa kk) (bm_ind bmI) (mword_of_int 0 : mword 32)
                 (ind_bytes (bm_ent bmI)) q Hal ltac:(unfold NINDIRECT in Hq; lia)
                 with "Hbuf") as "(%Hlen0 & Hcell & Hbufback)".
    assert (Hentv : bb_mk (fun jj => ind_bytes (bm_ent bmI) !!! jj) (4 * q)%nat
                    = bm_ent bmI !!! q)
      by (apply bm_ent_read; rewrite Hentlen; unfold NINDIRECT in Hq; lia).
    assert (Hcadr : add_vec (rget B6 Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = pa_add (b_data (bnode kk)) (4 * q)%nat).
    { rgne. rewrite HB6a5. apply bm_off0. }
    iEval (rewrite -Hcadr) in "Hcell".
    iApply (wp_clw_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x7e)) Rs1 Ra5
              (mword_of_int 0 : mword 12) B6 (K - 6)%nat
              (bb_mk (fun jj => ind_bytes (bm_ent bmI) !!! jj) (4 * q)%nat) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7e Hcell").
    iIntros (CID11 Hq11) "Hcg Hpc Hcell".
    iEval (rewrite Hcadr) in "Hcell".
    set (B7 := <[Regidx Rs1 := regval_into_reg
                  (sign_extend' 64 (bb_mk (fun jj => ind_bytes (bm_ent bmI) !!! jj)
                                      (4 * q)%nat))]> B6).
    assert (HB7s1 : B7 !!! Regidx Rs1 = (sign_extend' 64 (bm_ent bmI !!! q : mword 32) : mword 64)).
    { rewrite /B7 upd_eq Hentv. reflexivity. }
    assert (HB7s3 : B7 !!! Regidx Rs3 = pa_add (b_data (bnode kk)) (4 * q)%nat)
      by (rewrite /B7 upd_ne; [exact HB6s3 | nz]).
    assert (HB7s4 : B7 !!! Regidx Rs4 = bnode kk)
      by (rewrite /B7 upd_ne; [exact HB6s4 | nz]).
    assert (HB7s2 : B7 !!! Regidx Rs2 = ip)
      by (rewrite /B7 upd_ne; [exact HB6s2 | nz]).
    assert (HB7sp : bm_sp m B7)
      by (rewrite /bm_sp /B7 upd_ne; [exact HB6sp | nz]).
    assert (HB7thr : bm_thr6 m B7).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite /B7 upd_ne; [| regne]. exact (HB6thr c Hcs N2 N8 N9 N18 N19 N20). }
    assert (Hpp80 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x7e) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x80)) by pcw.
    iEval (rewrite Hpp80) in "Hpc".
    (* ===== +0x80 c.beqz s1 ===== *)
    destruct (decide (bv_unsigned (bm_ent bmI !!! q) = 0)) as [Hentz|Hentnz].
    - (* ================= the entry is EMPTY: allocate ================= *)
      assert (Hjmp9a : add_vec (mword_of_int (KernelSyms.bmap + 0x80) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 13 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.bmap + 0x9a)) by pcw.
      iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x80))
                (mword_of_int 13 : mword 8) (Cregidx (mword_of_int 1)) Rs1
                B7 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HB7s1; exact (bm_eqz_true _ Hentz))
                ltac:(rewrite Hjmp9a; vm_compute; reflexivity)
                with "Hcg Hpc Hi80").
      iApply bi.later_intro.
      iIntros (CID12 Hq12) "Hcg Hpc".
      iEval (rewrite Hjmp9a) in "Hpc".
      iPoseProof (bmi_9a with "Htext") as "Hi9a".
      iPoseProof (bmi_9e with "Htext") as "Hi9e".
      iPoseProof (bmi_a2 with "Htext") as "Hia2".
      iPoseProof (bmi_a4 with "Htext") as "Hia4".
      (* ===== +0x9a lw a0,0(s2) ===== *)
      assert (Hdadr2 : add_vec (rget B7 Rs2)
                         (sign_extend' 64 (mword_of_int 0 : mword 12)) = i_dev ip).
      { rgne. rewrite HB7s2. reflexivity. }
      iEval (rewrite -Hdadr2) in "Hidev".
      iApply (wp_lw_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x9a)) Ra0 Rs2
                (mword_of_int 0 : mword 12) B7 (K - 6)%nat dev b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9a Hidev").
      iIntros (CID13 Hq13) "Hcg Hpc Hidev".
      iEval (rewrite Hdadr2) in "Hidev".
      set (A0 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> B7).
      assert (HA0a0 : A0 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
        by (rewrite /A0; apply upd_eq).
      assert (HA0s3 : A0 !!! Regidx Rs3 = pa_add (b_data (bnode kk)) (4 * q)%nat)
        by (rewrite /A0 upd_ne; [exact HB7s3 | nz]).
      assert (HA0s4 : A0 !!! Regidx Rs4 = bnode kk)
        by (rewrite /A0 upd_ne; [exact HB7s4 | nz]).
      assert (HA0sp : bm_sp m A0)
        by (rewrite /bm_sp /A0 upd_ne; [exact HB7sp | nz]).
      assert (HA0thr : bm_thr6 m A0).
      { intros c Hcs N2 N8 N9 N18 N19 N20.
        rewrite /A0 upd_ne; [| regne]. exact (HB7thr c Hcs N2 N8 N9 N18 N19 N20). }
      assert (Hpp9e : add_vec_int (mword_of_int (KernelSyms.bmap + 0x9a) : mword 64) 4
                      = mword_of_int (KernelSyms.bmap + 0x9e)) by pcw.
      iEval (rewrite Hpp9e) in "Hpc".
      (* ===== +0x9e jal ra,balloc ===== *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x9e)) Rra
                (mword_of_int 2096732 : mword 21) A0 (K - 6)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi9e").
      iIntros (CID14 Hq14) "Hcg Hpc".
      set (A1 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.bmap + 0x9e) : mword 64) 4)]> A0).
      assert (Htgtba : add_vec (mword_of_int (KernelSyms.bmap + 0x9e) : mword 64)
                         (sign_extend' 64 (mword_of_int 2096732 : mword 21))
                       = mword_of_int KernelSyms.balloc) by pcw.
      iEval (rewrite Htgtba) in "Hpc".
      assert (HA1a0 : A1 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
        by (rewrite /A1 upd_ne; [exact HA0a0 | nz]).
      assert (HA1s3 : A1 !!! Regidx Rs3 = pa_add (b_data (bnode kk)) (4 * q)%nat)
        by (rewrite /A1 upd_ne; [exact HA0s3 | nz]).
      assert (HA1s4 : A1 !!! Regidx Rs4 = bnode kk)
        by (rewrite /A1 upd_ne; [exact HA0s4 | nz]).
      assert (HA1sp : bm_sp m A1)
        by (rewrite /bm_sp /A1 upd_ne; [exact HA0sp | nz]).
      assert (HA1ra : A1 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.bmap + 0x9e) : mword 64) 4)
        by (rewrite /A1; apply upd_eq).
      assert (HA1thr : bm_thr6 m A1).
      { intros c Hcs N2 N8 N9 N18 N19 N20.
        rewrite /A1 upd_ne; [| regne]. exact (HA0thr c Hcs N2 N8 N9 N18 N19 N20). }
      iDestruct (cpu_own_transport CID4 CID14 0 true (proc_addr j) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (wp_next_shift (CIDa := CID3) (CIDb := CID14) ltac:(wp_next_chain)
                   with "Hcont") as "Hcont".
      assert (HKba : (K_balloc <= K - 6)%nat) by (unfold K_balloc; lia).
      remember (nI - 3)%nat as w eqn:Hweq.
      assert (Hnn : nI = (2 + S w)%nat) by lia.
      iEval (rewrite Hnn) in "Hop".
      iApply (BA.wp_balloc_sconf Φ γs j γl γu γd γk pd pav pu bn γ γfs
                cov logstart dev (S w) pidv dq A1 (K - 6)%nat true C b
                HKba Hgeom0 Hj Hgl HA1a0 eq_refl
                with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hppid Hprocs Hscheds
                      Hoctx Hpark Hdevi Hdgeom Hdlock Hsl Hop").
      iIntros (CID15 Hq15 mA) "%Hcs2 Hcg Hcnt Hpc Hoctx Hpark Hppid Hsl Harm".
      assert (Hpca2 : ret_pc (A1 !!! Regidx Rra : mword 64)
                      = mword_of_int (KernelSyms.bmap + 0xa2)) by (rewrite HA1ra; pcw).
      iEval (rewrite Hpca2) in "Hpc".
      pose proof Hcs2 as Hcs2_cs.
      assert (HmAs3 : mA !!! Regidx Rs3 = pa_add (b_data (bnode kk)) (4 * q)%nat)
        by (rewrite (callee_saved_lookup Hcs2_cs Rs3 ltac:(vm_compute; reflexivity));
            exact HA1s3).
      assert (HmAs4 : mA !!! Regidx Rs4 = bnode kk)
        by (rewrite (callee_saved_lookup Hcs2_cs Rs4 ltac:(vm_compute; reflexivity));
            exact HA1s4).
      assert (HmAsp : bm_sp m mA).
      { rewrite /bm_sp
          (callee_saved_lookup Hcs2_cs csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HA1sp. }
      assert (HmAthr : bm_thr6 m mA).
      { intros c Hcs N2 N8 N9 N18 N19 N20.
        rewrite (callee_saved_lookup Hcs2_cs c Hcs).
        exact (HA1thr c Hcs N2 N8 N9 N18 N19 N20). }
      iDestruct (cpu_own_transport CID15 CID15 0 true (proc_addr j) C b
                   ltac:(intro; reflexivity) with "Hcnt") as "Hcnt".
      iDestruct "Harm" as "[[%Ha0z Hop] | Hsucc]".
      + (* ---------- balloc FAILED: brelse and return 0 ---------- *)
        iEval (rewrite -Hnn) in "Hop".
        (* +0xa2 c.mv s1,a0 *)
        iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0xa2)) Rs1 Ra0
                  mA (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia2").
        iIntros (CID16 Hq16) "Hcg Hpc".
        set (F0 := <[Regidx Rs1 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (rget mA Ra0))]> mA).
        assert (HF0s1 : F0 !!! Regidx Rs1
                        = (sign_extend' 64 (mword_of_int 0 : mword 32) : mword 64)).
        { rewrite /F0 upd_eq. rgne. rewrite Ha0z add_vec_zero_l.
          symmetry. apply bm_sext_zero. apply moi32_small. lia. }
        assert (HF0a0 : F0 !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
          by (rewrite /F0 upd_ne; [exact Ha0z | nz]).
        assert (HF0s4 : F0 !!! Regidx Rs4 = bnode kk)
          by (rewrite /F0 upd_ne; [exact HmAs4 | nz]).
        assert (HF0sp : bm_sp m F0)
          by (rewrite /bm_sp /F0 upd_ne; [exact HmAsp | nz]).
        assert (HF0thr : bm_thr6 m F0).
        { intros c Hcs N2 N8 N9 N18 N19 N20.
          rewrite /F0 upd_ne; [| regne]. exact (HmAthr c Hcs N2 N8 N9 N18 N19 N20). }
        assert (Hppa4 : add_vec_int (mword_of_int (KernelSyms.bmap + 0xa2) : mword 64) 2
                        = mword_of_int (KernelSyms.bmap + 0xa4)) by pcw.
        iEval (rewrite Hppa4) in "Hpc".
        (* +0xa4 c.beqz a0 : TAKEN, back to +0x82 *)
        assert (Hjmp82 : add_vec (mword_of_int (KernelSyms.bmap + 0xa4) : mword 64)
                  (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 239 : mword 8) ('b"0"))))
                = mword_of_int (KernelSyms.bmap + 0x82)) by pcw.
        iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0xa4))
                  (mword_of_int 239 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  F0 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HF0a0; apply eq_vec_true_iff; pcw)
                  ltac:(rewrite Hjmp82; vm_compute; reflexivity)
                  with "Hcg Hpc Hia4").
        iApply bi.later_intro.
        iIntros (CID17 Hq17) "Hcg Hpc".
        iEval (rewrite Hjmp82) in "Hpc".
        (* put the borrowed word back unchanged and rebuild the handle *)
        iDestruct ("Hbufback" $! (bb_mk (fun jj => ind_bytes (bm_ent bmI) !!! jj)
                       (4 * q)%nat) with "Hcell") as "Hbuf".
        iEval (rewrite (bm_buf_restore (ind_bytes (bm_ent bmI)) q Hlen0)) in "Hbuf".
        iDestruct ("Hheldback" $! (ind_bytes (bm_ent bmI)) with "Hbuf") as "Hheld".
        iAssert (inode_map γfs ip bmI) with "[Haddrs Hindblk Hindtok]" as "Hmap".
        { rewrite /inode_map /ind_res /ind_blk.
          iSplitL "Haddrs"; [iExact "Haddrs"|].
          iSplitL "Hindblk"; [| iExact "Hindtok"].
          destruct (decide (bv_unsigned (bm_ind bmI) = 0)) as [Hz1|_];
            [exfalso; exact (Hindnz Hz1)|].
          iEval (rewrite -Huind). iExact "Hindblk". }
        iDestruct (cpu_own_transport CID15 CID17 0 true (proc_addr j) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (bm_release (CID0 := CID17) Φ γs j γfs γd bn γ cov logstart dev
                  ip bm bmI data data fbn n nI (mword_of_int 0 : mword 32)
                  kk (bm_ind bmI) (ind_bytes (bm_ent bmI)) bsd0 d0
                  pidv dq dqd m F0 K C b
                  HK HF0sp HF0thr HF0s1 HF0s4 Hkk HwfI
                  ltac:(intros i Hi _; exact (Hagr i Hi))
                  ltac:(intros i Hi _; exact (Hagr i Hi))
                  ltac:(left; split;
                        [apply moi32_small; lia
                        | rewrite Hgetq; exact Hentz])
                  ltac:(left; reflexivity) ltac:(lia) ltac:(lia)
                  with "Hcg Hcnt Htext Hpc Hpanic Hbio Hprocs Hframe Hoctx Hpark
                        Hppid Hidev Hmap Hblocks Hsl Hop Hheld [Hcont]").
        iApply (wp_next_shift (CIDa := CID14) (CIDb := CID17) ltac:(wp_next_chain)
                  with "Hcont").
      + (* ---------- balloc SUCCEEDED: install and log ---------- *)
        iDestruct "Hsucc" as (blk) "(%Ha0v & %Hblknz & %Hblkcov & %Hblklog & Hfsb & Htok & Hop)".
        (* the freshness that re-establishes injectivity *)
        iDestruct (inode_fresh γfs bmI data (bv_unsigned blk)
                     with "Htok Hindtok Hblocks") as %Hfresh.
        (* +0xa2 c.mv s1,a0 *)
        iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0xa2)) Rs1 Ra0
                  mA (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia2").
        iIntros (CID16 Hq16) "Hcg Hpc".
        set (G0 := <[Regidx Rs1 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (rget mA Ra0))]> mA).
        assert (HG0s1 : G0 !!! Regidx Rs1 = (sign_extend' 64 blk : mword 64)).
        { rewrite /G0 upd_eq. rgne. rewrite Ha0v. apply add_vec_zero_l. }
        assert (HG0a0 : G0 !!! Regidx Ra0 = (sign_extend' 64 blk : mword 64))
          by (rewrite /G0 upd_ne; [exact Ha0v | nz]).
        assert (HG0s3 : G0 !!! Regidx Rs3 = pa_add (b_data (bnode kk)) (4 * q)%nat)
          by (rewrite /G0 upd_ne; [exact HmAs3 | nz]).
        assert (HG0s4 : G0 !!! Regidx Rs4 = bnode kk)
          by (rewrite /G0 upd_ne; [exact HmAs4 | nz]).
        assert (HG0sp : bm_sp m G0)
          by (rewrite /bm_sp /G0 upd_ne; [exact HmAsp | nz]).
        assert (HG0thr : bm_thr6 m G0).
        { intros c Hcs N2 N8 N9 N18 N19 N20.
          rewrite /G0 upd_ne; [| regne]. exact (HmAthr c Hcs N2 N8 N9 N18 N19 N20). }
        assert (Hppa4 : add_vec_int (mword_of_int (KernelSyms.bmap + 0xa2) : mword 64) 2
                        = mword_of_int (KernelSyms.bmap + 0xa4)) by pcw.
        iEval (rewrite Hppa4) in "Hpc".
        (* +0xa4 c.beqz a0 : FALLS THROUGH *)
        iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0xa4))
                  (mword_of_int 239 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  G0 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HG0a0; exact (bm_eqz_false blk Hblknz))
                  with "Hcg Hpc Hia4").
        iIntros (CID17 Hq17) "Hcg Hpc".
        assert (Hppa6 : add_vec_int (mword_of_int (KernelSyms.bmap + 0xa4) : mword 64) 2
                        = mword_of_int (KernelSyms.bmap + 0xa6)) by pcw.
        iEval (rewrite Hppa6) in "Hpc".
        iPoseProof (bmi_a6 with "Htext") as "Hia6".
        iPoseProof (bmi_aa with "Htext") as "Hiaa".
        iPoseProof (bmi_ac with "Htext") as "Hiac".
        iPoseProof (bmi_b0 with "Htext") as "Hib0".
        (* ===== +0xa6 sw a0,0(s3) : a[bn] = addr ===== *)
        assert (Hsadr : add_vec (rget G0 Rs3)
                          (sign_extend' 64 (mword_of_int 0 : mword 12))
                        = pa_add (b_data (bnode kk)) (4 * q)%nat).
        { rgne. rewrite HG0s3. apply bm_off0. }
        iEval (rewrite -Hsadr) in "Hcell".
        iApply (wp_sw_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0xa6)) Ra0 Rs3
                  (mword_of_int 0 : mword 12) G0 (K - 6)%nat
                  (bb_mk (fun jj => ind_bytes (bm_ent bmI) !!! jj) (4 * q)%nat) b
                  with "Hcg Hpc Hia6 Hcell").
        iIntros (CID18 Hq18) "Hcg Hpc Hcell".
        iEval (rewrite Hsadr) in "Hcell".
        assert (Hst : trunc32 (rget G0 Ra0) = blk).
        { rgne. rewrite HG0a0. apply trunc32_sext64. }
        iEval (rewrite Hst) in "Hcell".
        assert (Hppaa : add_vec_int (mword_of_int (KernelSyms.bmap + 0xa6) : mword 64) 4
                        = mword_of_int (KernelSyms.bmap + 0xaa)) by pcw.
        iEval (rewrite Hppaa) in "Hpc".
        (* the buffer's new byte image IS the updated entry list *)
        iDestruct ("Hbufback" $! blk with "Hcell") as "Hbuf".
        assert (Hstore : (bb_set (fun jj => ind_bytes (bm_ent bmI) !!! jj)
                             (4 * q)%nat blk) <$> seq 0 1024
                         = ind_bytes (<[q := blk]> (bm_ent bmI))).
        { apply bm_ent_store; [exact Hentlen | unfold NINDIRECT in Hq; lia]. }
        iEval (rewrite Hstore) in "Hbuf".
        iDestruct ("Hheldback" $! (ind_bytes (<[q := blk]> (bm_ent bmI)))
                     with "Hbuf") as "Hheld".
        (* ===== +0xaa c.mv a0,s4 ===== *)
        iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0xaa)) Ra0 Rs4
                  G0 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hiaa").
        iIntros (CID19 Hq19) "Hcg Hpc".
        set (G1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (rget G0 Rs4))]> G0).
        assert (HG1a0 : G1 !!! Regidx Ra0 = bnode kk).
        { rewrite /G1 upd_eq. rgne. rewrite HG0s4. apply add_vec_zero_l. }
        assert (HG1s1 : G1 !!! Regidx Rs1 = (sign_extend' 64 blk : mword 64))
          by (rewrite /G1 upd_ne; [exact HG0s1 | nz]).
        assert (HG1s4 : G1 !!! Regidx Rs4 = bnode kk)
          by (rewrite /G1 upd_ne; [exact HG0s4 | nz]).
        assert (HG1sp : bm_sp m G1)
          by (rewrite /bm_sp /G1 upd_ne; [exact HG0sp | nz]).
        assert (HG1thr : bm_thr6 m G1).
        { intros c Hcs N2 N8 N9 N18 N19 N20.
          rewrite /G1 upd_ne; [| regne]. exact (HG0thr c Hcs N2 N8 N9 N18 N19 N20). }
        assert (Hppac : add_vec_int (mword_of_int (KernelSyms.bmap + 0xaa) : mword 64) 2
                        = mword_of_int (KernelSyms.bmap + 0xac)) by pcw.
        iEval (rewrite Hppac) in "Hpc".
        (* ===== +0xac jal ra,log_write ===== *)
        iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0xac)) Rra
                  (mword_of_int 3626 : mword 21) G1 (K - 6)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hiac").
        iIntros (CID20 Hq20) "Hcg Hpc".
        set (G2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.bmap + 0xac) : mword 64) 4)]> G1).
        assert (Htgtlw : add_vec (mword_of_int (KernelSyms.bmap + 0xac) : mword 64)
                           (sign_extend' 64 (mword_of_int 3626 : mword 21))
                         = mword_of_int KernelSyms.log_write) by pcw.
        iEval (rewrite Htgtlw) in "Hpc".
        assert (HG2a0 : G2 !!! Regidx Ra0 = bnode kk)
          by (rewrite /G2 upd_ne; [exact HG1a0 | nz]).
        assert (HG2s1 : G2 !!! Regidx Rs1 = (sign_extend' 64 blk : mword 64))
          by (rewrite /G2 upd_ne; [exact HG1s1 | nz]).
        assert (HG2s4 : G2 !!! Regidx Rs4 = bnode kk)
          by (rewrite /G2 upd_ne; [exact HG1s4 | nz]).
        assert (HG2sp : bm_sp m G2)
          by (rewrite /bm_sp /G2 upd_ne; [exact HG1sp | nz]).
        assert (HG2ra : G2 !!! Regidx Rra
                        = add_vec_int (mword_of_int (KernelSyms.bmap + 0xac) : mword 64) 4)
          by (rewrite /G2; apply upd_eq).
        assert (HG2thr : bm_thr6 m G2).
        { intros c Hcs N2 N8 N9 N18 N19 N20.
          rewrite /G2 upd_ne; [| regne]. exact (HG1thr c Hcs N2 N8 N9 N18 N19 N20). }
        iDestruct (cpu_own_transport CID15 CID20 0 true (proc_addr j) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        assert (HKlw : (K_log_write <= K - 6)%nat) by (unfold K_log_write; lia).
        iDestruct (bm_slots_split bn 1 1 with "Hsl") as "[Hsl1 Hslr]".
        iApply (LW.wp_log_write_sconf Φ bn γ γfs γd cov logstart dev kk pidv
                  (bm_ind bmI) (ind_bytes (<[q := blk]> (bm_ent bmI)))
                  (ind_bytes (bm_ent bmI)) bsd0 d0 w
                  G2 0%nat true (proc_addr j) C (K - 6)%nat b
                  HKlw ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia) Hkk HG2a0
                  ltac:(rewrite Huind; exact Hicov)
                  ltac:(rewrite Huind; exact Hilog)
                  with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hsl1 Hop Hindblk Hheld").
        iIntros (CID21 Hq21 mL) "Hcg Hcnt Hpc %Hcs3 Hop Hindblk Hheld Hsl1".
        assert (Hpcb0 : ret_pc (G2 !!! Regidx Rra : mword 64)
                        = mword_of_int (KernelSyms.bmap + 0xb0)) by (rewrite HG2ra; pcw).
        iEval (rewrite Hpcb0) in "Hpc".
        pose proof Hcs3 as Hcs3_cs.
        assert (HmLs1 : mL !!! Regidx Rs1 = (sign_extend' 64 blk : mword 64))
          by (rewrite (callee_saved_lookup Hcs3_cs Rs1 ltac:(vm_compute; reflexivity));
              exact HG2s1).
        assert (HmLs4 : mL !!! Regidx Rs4 = bnode kk)
          by (rewrite (callee_saved_lookup Hcs3_cs Rs4 ltac:(vm_compute; reflexivity));
              exact HG2s4).
        assert (HmLsp : bm_sp m mL).
        { rewrite /bm_sp
            (callee_saved_lookup Hcs3_cs csp_rs1 ltac:(vm_compute; reflexivity)).
          exact HG2sp. }
        assert (HmLthr : bm_thr6 m mL).
        { intros c Hcs N2 N8 N9 N18 N19 N20.
          rewrite (callee_saved_lookup Hcs3_cs c Hcs).
          exact (HG2thr c Hcs N2 N8 N9 N18 N19 N20). }
        (* ===== +0xb0 c.j -0x2e : back to the brelse block ===== *)
        assert (Hjmpb : add_vec (mword_of_int (KernelSyms.bmap + 0xb0) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 2025 : mword 11) ('b"0"))))
                = mword_of_int (KernelSyms.bmap + 0x82)) by pcw.
        iApply (wp_cj_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0xb0))
                  (sign_extend' 21 (concat_vec (mword_of_int 2025 : mword 11) ('b"0")))
                  mL (K - 6)%nat b ltac:(rewrite Hjmpb; vm_compute; reflexivity)
                  with "Hcg Hpc Hib0").
        iIntros (CID22 Hq22).
        iApply bi.later_intro.
        iIntros "Hcg Hpc".
        iEval (rewrite Hjmpb) in "Hpc".
        (* ---- THE NEW MAP, and everything it has to satisfy ---- *)
        set (bmJ := MkBlkmap (bm_dir bmI) (bm_ind bmI) (<[q := blk]> (bm_ent bmI))).
        assert (Hslotd : forall i : nat, (i <= MAXFILE)%nat ->
                  bm_slot bmJ i
                  = if decide (i = (NDIRECT + q)%nat) then blk else bm_slot bmI i)
          by (intros i Hi; apply bm_slot_insert_ent;
              [exact Hentlen | exact Hq | exact Hi]).
        assert (HwfJ : blkmap_wf cov logstart bmJ).
        { apply (blkmap_wf_slot_upd cov logstart bmI bmJ (NDIRECT + q)%nat blk HwfI).
          - rewrite /bmJ; cbn [bm_dir]. exact (blkmap_wf_dir_len cov logstart bmI HwfI).
          - rewrite /bmJ; cbn [bm_ent]. rewrite length_insert. exact Hentlen.
          - unfold MAXFILE, NDIRECT, NINDIRECT in *; lia.
          - exact Hslotd.
          - exact Hblknz.
          - exact Hblkcov.
          - exact Hblklog.
          - exact Hfresh.
          - rewrite /bmJ; cbn [bm_ind]. intro Hc. exfalso. exact (Hindnz Hc). }
        assert (HgetJ : forall i : nat, (i < MAXFILE)%nat -> i <> fbn ->
                  blkmap_get bmJ i = blkmap_get bmI i).
        { intros i Hi Hne.
          rewrite -(bm_slot_lt bmJ i Hi) -(bm_slot_lt bmI i Hi).
          rewrite (Hslotd i ltac:(lia)).
          destruct (decide (i = (NDIRECT + q)%nat)) as [->|_];
            [exfalso; apply Hne; lia | reflexivity]. }
        assert (HgetJf : blkmap_get bmJ fbn = blk).
        { rewrite -(bm_slot_lt bmJ fbn Hfbnlt) (Hslotd fbn ltac:(lia)).
          destruct (decide (fbn = (NDIRECT + q)%nat)) as [_|Hc];
            [reflexivity | exfalso; apply Hc; exact Hfbn]. }
        iAssert (inode_map γfs ip bmJ) with "[Haddrs Hindblk Hindtok]" as "Hmap".
        { rewrite /inode_map /ind_res /ind_blk /ind_tok /bmJ.
          cbn [bm_ind bm_ent bm_dir].
          iSplitL "Haddrs"; [iExact "Haddrs"|].
          iSplitL "Hindblk"; [| iExact "Hindtok"].
          destruct (decide (bv_unsigned (bm_ind bmI) = 0)) as [Hz1|_];
            [exfalso; exact (Hindnz Hz1)|].
          iEval (rewrite -Huind). iExact "Hindblk". }
        iDestruct (inode_blocks_insert γfs bmI bmJ data fbn blk
                     (replicate BSIZE (bv_0 8)) Hfbnlt
                     ltac:(rewrite Hgetq; exact Hentz) HgetJf HgetJ
                     with "Hblocks Hfsb Htok") as "Hblocks".
        iDestruct (bm_slots_join bn 1 1 with "Hslr Hsl1") as "Hsl".
        iDestruct (cpu_own_transport CID21 CID22 0 true (proc_addr j) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (bm_release (CID0 := CID22) Φ γs j γfs γd bn γ cov logstart dev
                  ip bm bmJ data (<[fbn := replicate BSIZE (bv_0 8)]> data)
                  fbn n w blk kk (bm_ind bmI)
                  (ind_bytes (<[q := blk]> (bm_ent bmI))) bsd0 true
                  pidv dq dqd m mL K C b
                  HK HmLsp HmLthr HmLs1 HmLs4 Hkk HwfJ
                  ltac:(intros i Hi Hne; rewrite (HgetJ i Hi Hne); exact (Hagr i Hi))
                  ltac:(intros i Hi Hnz;
                        destruct (decide (i = fbn)) as [->|Hne];
                        [ exfalso; apply Hnz;
                          rewrite -(Hagr fbn Hfbnlt) Hgetq; exact Hentz
                        | rewrite (HgetJ i Hi Hne); exact (Hagr i Hi) ])
                  ltac:(right; split;
                        [exact (eq_sym HgetJf)
                        | rewrite HgetJf; exact Hblknz])
                  ltac:(right; split;
                        [rewrite -(Hagr fbn Hfbnlt) Hgetq; exact Hentz | reflexivity]) ltac:(lia) ltac:(lia)
                  with "Hcg Hcnt Htext Hpc Hpanic Hbio Hprocs Hframe Hoctx Hpark
                        Hppid Hidev Hmap Hblocks Hsl Hop Hheld [Hcont]").
        iApply (wp_next_shift (CIDa := CID14) (CIDb := CID22) ltac:(wp_next_chain)
                  with "Hcont").
    - (* ================= the entry is PRESENT: brelse and return ====== *)
      iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x80))
                (mword_of_int 13 : mword 8) (Cregidx (mword_of_int 1)) Rs1
                B7 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HB7s1; exact (bm_eqz_false _ Hentnz))
                with "Hcg Hpc Hi80").
      iIntros (CID12 Hq12) "Hcg Hpc".
      assert (Hpp82 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x80) : mword 64) 2
                      = mword_of_int (KernelSyms.bmap + 0x82)) by pcw.
      iEval (rewrite Hpp82) in "Hpc".
      iDestruct ("Hbufback" $! (bb_mk (fun jj => ind_bytes (bm_ent bmI) !!! jj)
                     (4 * q)%nat) with "Hcell") as "Hbuf".
      iEval (rewrite (bm_buf_restore (ind_bytes (bm_ent bmI)) q Hlen0)) in "Hbuf".
      iDestruct ("Hheldback" $! (ind_bytes (bm_ent bmI)) with "Hbuf") as "Hheld".
      iAssert (inode_map γfs ip bmI) with "[Haddrs Hindblk Hindtok]" as "Hmap".
      { rewrite /inode_map /ind_res /ind_blk.
        iSplitL "Haddrs"; [iExact "Haddrs"|].
        iSplitL "Hindblk"; [| iExact "Hindtok"].
        destruct (decide (bv_unsigned (bm_ind bmI) = 0)) as [Hz1|_];
          [exfalso; exact (Hindnz Hz1)|].
        iEval (rewrite -Huind). iExact "Hindblk". }
      iDestruct (cpu_own_transport CID4 CID12 0 true (proc_addr j) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (bm_release (CID0 := CID12) Φ γs j γfs γd bn γ cov logstart dev
                ip bm bmI data data fbn n nI (bm_ent bmI !!! q)
                kk (bm_ind bmI) (ind_bytes (bm_ent bmI)) bsd0 d0
                pidv dq dqd m B7 K C b
                HK HB7sp HB7thr HB7s1 HB7s4 Hkk HwfI
                ltac:(intros i Hi _; exact (Hagr i Hi))
                ltac:(intros i Hi _; exact (Hagr i Hi))
                ltac:(right; split;
                      [exact (eq_sym Hgetq) | rewrite Hgetq; exact Hentnz])
                ltac:(left; reflexivity) ltac:(lia) ltac:(lia)
                with "Hcg Hcnt Htext Hpc Hpanic Hbio Hprocs Hframe Hoctx Hpark
                      Hppid Hidev Hmap Hblocks Hsl Hop Hheld [Hcont]").
      iApply (wp_next_shift (CIDa := CID3) (CIDb := CID12) ltac:(wp_next_chain)
                with "Hcont").
  Qed.

End BmapTail.

(* ===================================================================== *)
(*  +0x00 .. +0x60 : the prologue, the DIRECT arm, and the indirect head. *)
(* ===================================================================== *)
Section ProofBmapMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_bmap_sconf (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (fbn : nat)
      (n : nat)
      (pidv : mword 32) (dq dqd : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool)
    : wp_bmap_sconf_body Φ γs j γl γu γd γk pd pav pu bn γ γfs
                         cov logstart dev ip bm data fbn n pidv dq dqd m K eb C b.
  Proof.
    cbv beta delta [wp_bmap_sconf_body].
    intros pcE pj ret_tgt bnw HK Hn5 Hgeom Hfbn Hwf Hj Hgl Ha0 Ha1 Heb.
    subst eb.
    pose proof HK as HK'. unfold K_bmap in HK'.
    pose proof Hfbn as Hfbn0. unfold MAXFILE in Hfbn0.
    pose proof (blkmap_wf_dir_len cov logstart bm Hwf) as Hdirlen.
    pose proof (blkmap_wf_ent_len cov logstart bm Hwf) as Hentlen.
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hlctx Hidev Hmap Hblocks Hppid
              #Hprocs #Hscheds Hoctx Hpark #Hdevi #Hdgeom #Hdlock Hsl Hop Hcont".
    iAssert (bm_cont (CID0 := CID) Φ γfs bn γ cov logstart dev ip bm data fbn n
               pidv dq dqd j m K C b)%I with "[Hcont]" as "Hcont";
      [rewrite /bm_cont; iExact "Hcont"|].
    iDestruct "Hmap" as "[Haddrs [Hindblk Hindtok]]".
    (* the argument, as a plain literal *)
    assert (Hbn : m !!! Regidx Ra1 = (mword_of_int (Z.of_nat fbn) : mword 64)).
    { rewrite Ha1. exact (bm_sext32 (Z.of_nat fbn) ltac:(lia) ltac:(lia)). }
    assert (Hu11 : uint (mword_of_int 11 : mword 64) = 11)
      by (apply bm_uint_moi; lia).
    assert (Hufbn : uint (mword_of_int (Z.of_nat fbn) : mword 64) = Z.of_nat fbn)
      by (apply bm_uint_moi; lia).
    iPoseProof (bmi_00 with "Htext") as "Hi00".
    iPoseProof (bmi_02 with "Htext") as "Hi02".
    iPoseProof (bmi_04 with "Htext") as "Hi04".
    iPoseProof (bmi_06 with "Htext") as "Hi06".
    iPoseProof (bmi_08 with "Htext") as "Hi08".
    iPoseProof (bmi_0a with "Htext") as "Hi0a".
    iPoseProof (bmi_0c with "Htext") as "Hi0c".
    iPoseProof (bmi_0e with "Htext") as "Hi0e".
    iPoseProof (bmi_10 with "Htext") as "Hi10".
    iPoseProof (bmi_12 with "Htext") as "Hi12".
    (* ===== +0x00 c.addi16sp sp,-48 ===== *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iApply (wp_caddi16sp_push_s_sconf Φ pcE (mword_of_int 61 : mword 6) m K 6 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1 : mword 64)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m)
      with (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1 : mword 64)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    assert (HR1sp : bm_sp m R1) by (rewrite /bm_sp /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (v1) "Hf1". iDestruct "S2" as (v2) "Hf2".
    iDestruct "S3" as (v3) "Hf3". iDestruct "S4" as (v4) "Hf4".
    iDestruct "S5" as (v5) "Hf5". iDestruct "S6" as (v6) "Hf6".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb5 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb6 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb1) in "Hf1". iEval (rewrite -Hb2) in "Hf2".
    iEval (rewrite -Hb3) in "Hf3". iEval (rewrite -Hb4) in "Hf4".
    iEval (rewrite -Hb5) in "Hf5". iEval (rewrite -Hb6) in "Hf6".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.bmap + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 .. +0x0a : the five saves ===== *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x02)) (mword_of_int 5 : mword 6) Rra
              R1 (K - 6)%nat v1 b with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x04)) (mword_of_int 4 : mword 6) Rs0
              R1 (K - 6)%nat v2 b with "Hcg Hpc Hi04 Hf2").
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x06)) (mword_of_int 3 : mword 6) Rs1
              R1 (K - 6)%nat v3 b with "Hcg Hpc Hi06 Hf3").
    iIntros (CID4 Hq4) "Hcg Hpc Hf3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x08)) (mword_of_int 2 : mword 6) Rs2
              R1 (K - 6)%nat v4 b with "Hcg Hpc Hi08 Hf4").
    iIntros (CID5 Hq5) "Hcg Hpc Hf4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.bmap + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x0a)) (mword_of_int 1 : mword 6) Rs3
              R1 (K - 6)%nat v5 b with "Hcg Hpc Hi0a Hf5").
    iIntros (CID6 Hq6) "Hcg Hpc Hf5".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.bmap + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* the frame, restated at the entry file *)
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s1 : (R1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s2 : (R1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s3 : (R1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s4 : (R1 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hf2".
    iEval (rewrite Hb3; rgne; rewrite HR1s1) in "Hf3".
    iEval (rewrite Hb4; rgne; rewrite HR1s2) in "Hf4".
    iEval (rewrite Hb5; rgne; rewrite HR1s3) in "Hf5".
    iEval (rewrite Hb6) in "Hf6".
    (* ===== +0x0c c.addi4spn s0,sp,48 ===== *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x0c)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 R1 (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (HR2sp : bm_sp m R2)
      by (rewrite /bm_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2a0 : R2 !!! Regidx Ra0 = ip)
      by (rewrite /R2 upd_ne; [| nz]; rewrite /R1 upd_ne; [exact Ha0 | nz]).
    assert (HR2a1 : R2 !!! Regidx Ra1 = (mword_of_int (Z.of_nat fbn) : mword 64))
      by (rewrite /R2 upd_ne; [| nz]; rewrite /R1 upd_ne; [exact Hbn | nz]).
    assert (HR2thr : bm_thr5 m R2).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.bmap + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x0e)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== +0x0e c.mv s2,a0 : s2 := ip ===== *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x0e)) Rs2 Ra0
              R2 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0e").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (R3 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R2 Ra0))]> R2).
    assert (HR3s2 : R3 !!! Regidx Rs2 = ip).
    { rewrite /R3 upd_eq. rgne. rewrite HR2a0. apply add_vec_zero_l. }
    assert (HR3a0 : R3 !!! Regidx Ra0 = ip)
      by (rewrite /R3 upd_ne; [exact HR2a0 | nz]).
    assert (HR3a1 : R3 !!! Regidx Ra1 = (mword_of_int (Z.of_nat fbn) : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2a1 | nz]).
    assert (HR3sp : bm_sp m R3)
      by (rewrite /bm_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : bm_thr5 m R3).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /R3 upd_ne; [| regne]. exact (HR2thr c Hcs N2 N8 N9 N18 N19). }
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ===== +0x10 c.li a5,11 ===== *)
    iApply (wp_cli_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x10)) Ra5 (mword_of_int 11 : mword 6)
              (mword_of_int 11 : mword 64) R3 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi10").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (R4 := <[Regidx Ra5 := regval_into_reg (mword_of_int 11 : mword 64)]> R3).
    assert (HR4a5 : R4 !!! Regidx Ra5 = (mword_of_int 11 : mword 64))
      by (rewrite /R4; apply upd_eq).
    assert (HR4a1 : R4 !!! Regidx Ra1 = (mword_of_int (Z.of_nat fbn) : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3a1 | nz]).
    assert (HR4a0 : R4 !!! Regidx Ra0 = ip)
      by (rewrite /R4 upd_ne; [exact HR3a0 | nz]).
    assert (HR4s2 : R4 !!! Regidx Rs2 = ip)
      by (rewrite /R4 upd_ne; [exact HR3s2 | nz]).
    assert (HR4sp : bm_sp m R4)
      by (rewrite /bm_sp /R4 upd_ne; [exact HR3sp | nz]).
    assert (HR4thr : bm_thr5 m R4).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /R4 upd_ne; [| regne]. exact (HR3thr c Hcs N2 N8 N9 N18 N19). }
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x10) : mword 64) 2
                    = mword_of_int (KernelSyms.bmap + 0x12)) by pcw.
    iEval (rewrite Hpp12) in "Hpc".
    (* ===== +0x12 bltu a5,a1 : the direct / indirect split ===== *)
    destruct (decide ((fbn < NDIRECT)%nat)) as [Hdir|Hind].
    - (* ================== THE DIRECT ARM (bn < NDIRECT) ================== *)
      iApply (wp_bltu_fall_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x12))
                (mword_of_int 38 : mword 13) Ra1 Ra5 R4 (K - 6)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HR4a5 HR4a1; unfold zopz0zI_u;
                      rewrite Hu11 Hufbn; apply Z.ltb_ge;
                      unfold NDIRECT in Hdir; lia)
                with "Hcg Hpc Hi12").
      iIntros (CID10 Hq10) "Hcg Hpc".
      assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x12) : mword 64) 4
                      = mword_of_int (KernelSyms.bmap + 0x16)) by pcw.
      iEval (rewrite Hpp16) in "Hpc".
      iPoseProof (bmi_16 with "Htext") as "Hi16".
      iPoseProof (bmi_1a with "Htext") as "Hi1a".
      iPoseProof (bmi_1e with "Htext") as "Hi1e".
      iPoseProof (bmi_22 with "Htext") as "Hi22".
      iPoseProof (bmi_26 with "Htext") as "Hi26".
      assert (Hfu : bv_unsigned (mword_of_int (Z.of_nat fbn) : mword 64) = Z.of_nat fbn).
      { rewrite moi64_unsigned. apply bvw64_small.
        change (2 ^ 64)%Z with 18446744073709551616%Z. lia. }
      assert (Hflt : bv_unsigned (mword_of_int (Z.of_nat fbn) : mword 64) < 4294967296)
        by (rewrite Hfu; lia).
      (* ===== +0x16 slli a5,a1,0x20 ===== *)
      iApply (wp_slli_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x16)) Ra5 Ra1
                (mword_of_int 32 : mword 6)
                (shift_bits_left (mword_of_int (Z.of_nat fbn) : mword 64)
                   (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
                R4 (K - 6)%nat b ltac:(nz) ltac:(rdok)
                ltac:(rgne; rewrite HR4a1; reflexivity) with "Hcg Hpc Hi16").
      iIntros (CID11 Hq11) "Hcg Hpc".
      set (D0 := <[Regidx Ra5 := regval_into_reg
                    (shift_bits_left (mword_of_int (Z.of_nat fbn) : mword 64)
                       (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> R4).
      assert (HD0a5 : D0 !!! Regidx Ra5
                      = shift_bits_left (mword_of_int (Z.of_nat fbn) : mword 64)
                          (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
        by (rewrite /D0; apply upd_eq).
      assert (HD0a0 : D0 !!! Regidx Ra0 = ip)
        by (rewrite /D0 upd_ne; [exact HR4a0 | nz]).
      assert (HD0s2 : D0 !!! Regidx Rs2 = ip)
        by (rewrite /D0 upd_ne; [exact HR4s2 | nz]).
      assert (HD0sp : bm_sp m D0)
        by (rewrite /bm_sp /D0 upd_ne; [exact HR4sp | nz]).
      assert (HD0thr : bm_thr5 m D0).
      { intros c Hcs N2 N8 N9 N18 N19.
        rewrite /D0 upd_ne; [| regne]. exact (HR4thr c Hcs N2 N8 N9 N18 N19). }
      assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.bmap + 0x16) : mword 64) 4
                      = mword_of_int (KernelSyms.bmap + 0x1a)) by pcw.
      iEval (rewrite Hpp1a) in "Hpc".
      (* ===== +0x1a srli a1,a5,0x1e ===== *)
      iApply (wp_srli4_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x1a)) Ra1 Ra5
                (mword_of_int 30 : mword 6) D0 (K - 6)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1a").
      iIntros (CID12 Hq12) "Hcg Hpc".
      set (D1 := <[Regidx Ra1 := regval_into_reg
                    (shift_bits_right (rget D0 Ra5)
                       (subrange_vec_dec (mword_of_int 30 : mword 6) (Z.sub log2_xlen 1) 0))]> D0).
      assert (HD1a1 : D1 !!! Regidx Ra1 = (mword_of_int (4 * Z.of_nat fbn) : mword 64)).
      { rewrite /D1 upd_eq. rgne. rewrite HD0a5.
        rewrite (bm_slli32_srli30 (mword_of_int (Z.of_nat fbn) : mword 64) Hflt) Hfu.
        reflexivity. }
      assert (HD1a0 : D1 !!! Regidx Ra0 = ip)
        by (rewrite /D1 upd_ne; [exact HD0a0 | nz]).
      assert (HD1s2 : D1 !!! Regidx Rs2 = ip)
        by (rewrite /D1 upd_ne; [exact HD0s2 | nz]).
      assert (HD1sp : bm_sp m D1)
        by (rewrite /bm_sp /D1 upd_ne; [exact HD0sp | nz]).
      assert (HD1thr : bm_thr5 m D1).
      { intros c Hcs N2 N8 N9 N18 N19.
        rewrite /D1 upd_ne; [| regne]. exact (HD0thr c Hcs N2 N8 N9 N18 N19). }
      assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.bmap + 0x1a) : mword 64) 4
                      = mword_of_int (KernelSyms.bmap + 0x1e)) by pcw.
      iEval (rewrite Hpp1e) in "Hpc".
      (* ===== +0x1e add s3,a0,a1 ===== *)
      iApply (wp_add_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x1e)) Rs3 Ra0 Ra1
                (add_vec ip (mword_of_int (4 * Z.of_nat fbn))) D1 (K - 6)%nat b
                ltac:(nz) ltac:(rdok)
                ltac:(rgne; rgne; rewrite HD1a0 HD1a1; reflexivity)
                with "Hcg Hpc Hi1e").
      iIntros (CID13 Hq13) "Hcg Hpc".
      set (D2 := <[Regidx Rs3 := regval_into_reg
                    (add_vec ip (mword_of_int (4 * Z.of_nat fbn)))]> D1).
      assert (HD2s3 : D2 !!! Regidx Rs3 = add_vec ip (mword_of_int (4 * Z.of_nat fbn)))
        by (rewrite /D2; apply upd_eq).
      assert (HD2a0 : D2 !!! Regidx Ra0 = ip)
        by (rewrite /D2 upd_ne; [exact HD1a0 | nz]).
      assert (HD2s2 : D2 !!! Regidx Rs2 = ip)
        by (rewrite /D2 upd_ne; [exact HD1s2 | nz]).
      assert (HD2sp : bm_sp m D2)
        by (rewrite /bm_sp /D2 upd_ne; [exact HD1sp | nz]).
      assert (HD2thr : bm_thr5 m D2).
      { intros c Hcs N2 N8 N9 N18 N19.
        rewrite /D2 upd_ne; [| regne]. exact (HD1thr c Hcs N2 N8 N9 N18 N19). }
      assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x1e) : mword 64) 4
                      = mword_of_int (KernelSyms.bmap + 0x22)) by pcw.
      iEval (rewrite Hpp22) in "Hpc".
      (* ===== +0x22 lw s1,80(s3) : s1 := ip->addrs[bn] ===== *)
      iDestruct (inode_addrs_acc ip (bm_cells bm) fbn (blkmap_get bm fbn)
                   (bm_cells_dir bm fbn Hdirlen Hdir) with "Haddrs") as "[Hcell Hback]".
      assert (Hcadr : add_vec (rget D2 Rs3)
                        (sign_extend' 64 (mword_of_int 80 : mword 12)) = i_addr ip fbn).
      { rgne. rewrite HD2s3. symmetry. apply i_addr_indexed. }
      iEval (rewrite -Hcadr) in "Hcell".
      iApply (wp_lw_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x22)) Rs1 Rs3
                (mword_of_int 80 : mword 12) D2 (K - 6)%nat (blkmap_get bm fbn) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi22 Hcell").
      iIntros (CID14 Hq14) "Hcg Hpc Hcell".
      iEval (rewrite Hcadr) in "Hcell".
      set (D3 := <[Regidx Rs1 := regval_into_reg
                    (sign_extend' 64 (blkmap_get bm fbn : mword 32))]> D2).
      assert (HD3s1 : D3 !!! Regidx Rs1
                      = (sign_extend' 64 (blkmap_get bm fbn : mword 32) : mword 64))
        by (rewrite /D3; apply upd_eq).
      assert (HD3s3 : D3 !!! Regidx Rs3 = add_vec ip (mword_of_int (4 * Z.of_nat fbn)))
        by (rewrite /D3 upd_ne; [exact HD2s3 | nz]).
      assert (HD3a0 : D3 !!! Regidx Ra0 = ip)
        by (rewrite /D3 upd_ne; [exact HD2a0 | nz]).
      assert (HD3s2 : D3 !!! Regidx Rs2 = ip)
        by (rewrite /D3 upd_ne; [exact HD2s2 | nz]).
      assert (HD3sp : bm_sp m D3)
        by (rewrite /bm_sp /D3 upd_ne; [exact HD2sp | nz]).
      assert (HD3thr : bm_thr5 m D3).
      { intros c Hcs N2 N8 N9 N18 N19.
        rewrite /D3 upd_ne; [| regne]. exact (HD2thr c Hcs N2 N8 N9 N18 N19). }
      assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x22) : mword 64) 4
                      = mword_of_int (KernelSyms.bmap + 0x26)) by pcw.
      iEval (rewrite Hpp26) in "Hpc".
      (* ===== +0x26 c.bnez s1 ===== *)
      destruct (decide (bv_unsigned (blkmap_get bm fbn) = 0)) as [Hdz|Hdnz].
      + (* ---------- the slot is EMPTY: balloc and install ---------- *)
        iApply (wp_cbnez_fall_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x26))
                  (mword_of_int 50 : mword 8) (Cregidx (mword_of_int 1)) Rs1
                  D3 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HD3s1; unfold neq_vec;
                        rewrite (bm_eqz_true _ Hdz); reflexivity)
                  with "Hcg Hpc Hi26").
        iIntros (CID15 Hq15) "Hcg Hpc".
        assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x26) : mword 64) 2
                        = mword_of_int (KernelSyms.bmap + 0x28)) by pcw.
        iEval (rewrite Hpp28) in "Hpc".
        iPoseProof (bmi_28 with "Htext") as "Hi28".
        iPoseProof (bmi_2a with "Htext") as "Hi2a".
        iPoseProof (bmi_2e with "Htext") as "Hi2e".
        iPoseProof (bmi_30 with "Htext") as "Hi30".
        iPoseProof (bmi_32 with "Htext") as "Hi32".
        iPoseProof (bmi_36 with "Htext") as "Hi36".
        (* ===== +0x28 c.lw a0,0(a0) : a0 := ip->dev ===== *)
        assert (Hdadr : add_vec (rget D3 Ra0)
                          (sign_extend' 64 (mword_of_int 0 : mword 12)) = i_dev ip).
        { rgne. rewrite HD3a0. reflexivity. }
        iEval (rewrite -Hdadr) in "Hidev".
        iApply (wp_clw_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x28)) Ra0 Ra0
                  (mword_of_int 0 : mword 12) D3 (K - 6)%nat dev b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi28 Hidev").
        iIntros (CID16 Hq16) "Hcg Hpc Hidev".
        iEval (rewrite Hdadr) in "Hidev".
        set (D4 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> D3).
        assert (HD4a0 : D4 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
          by (rewrite /D4; apply upd_eq).
        assert (HD4s3 : D4 !!! Regidx Rs3 = add_vec ip (mword_of_int (4 * Z.of_nat fbn)))
          by (rewrite /D4 upd_ne; [exact HD3s3 | nz]).
        assert (HD4sp : bm_sp m D4)
          by (rewrite /bm_sp /D4 upd_ne; [exact HD3sp | nz]).
        assert (HD4thr : bm_thr5 m D4).
        { intros c Hcs N2 N8 N9 N18 N19.
          rewrite /D4 upd_ne; [| regne]. exact (HD3thr c Hcs N2 N8 N9 N18 N19). }
        assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.bmap + 0x28) : mword 64) 2
                        = mword_of_int (KernelSyms.bmap + 0x2a)) by pcw.
        iEval (rewrite Hpp2a) in "Hpc".
        (* ===== +0x2a jal ra,balloc ===== *)
        iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x2a)) Rra
                  (mword_of_int 2096848 : mword 21) D4 (K - 6)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi2a").
        iIntros (CID17 Hq17) "Hcg Hpc".
        set (D5 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.bmap + 0x2a) : mword 64) 4)]> D4).
        assert (Htgtba : add_vec (mword_of_int (KernelSyms.bmap + 0x2a) : mword 64)
                           (sign_extend' 64 (mword_of_int 2096848 : mword 21))
                         = mword_of_int KernelSyms.balloc) by pcw.
        iEval (rewrite Htgtba) in "Hpc".
        assert (HD5a0 : D5 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
          by (rewrite /D5 upd_ne; [exact HD4a0 | nz]).
        assert (HD5s3 : D5 !!! Regidx Rs3 = add_vec ip (mword_of_int (4 * Z.of_nat fbn)))
          by (rewrite /D5 upd_ne; [exact HD4s3 | nz]).
        assert (HD5sp : bm_sp m D5)
          by (rewrite /bm_sp /D5 upd_ne; [exact HD4sp | nz]).
        assert (HD5ra : D5 !!! Regidx Rra
                        = add_vec_int (mword_of_int (KernelSyms.bmap + 0x2a) : mword 64) 4)
          by (rewrite /D5; apply upd_eq).
        assert (HD5thr : bm_thr5 m D5).
        { intros c Hcs N2 N8 N9 N18 N19.
          rewrite /D5 upd_ne; [| regne]. exact (HD4thr c Hcs N2 N8 N9 N18 N19). }
        iDestruct (cpu_own_transport CID CID17 0 true (proc_addr j) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (wp_next_shift (CIDa := CID) (CIDb := CID17) ltac:(wp_next_chain)
                     with "Hcont") as "Hcont".
        assert (HKba : (K_balloc <= K - 6)%nat) by (unfold K_balloc; lia).
        remember (n - 2)%nat as u2 eqn:Hu2eq.
        assert (Hnn : n = (2 + u2)%nat) by lia.
        iEval (rewrite Hnn) in "Hop".
        iDestruct (bm_slots_split bn 2 1 with "Hsl") as "[Hsl Hslx]".
        iApply (BA.wp_balloc_sconf Φ γs j γl γu γd γk pd pav pu bn γ γfs
                  cov logstart dev u2 pidv dq D5 (K - 6)%nat true C b
                  HKba Hgeom Hj Hgl HD5a0 eq_refl
                  with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hppid Hprocs Hscheds
                        Hoctx Hpark Hdevi Hdgeom Hdlock Hsl Hop").
        iIntros (CID18 Hq18 mD) "%Hcs1 Hcg Hcnt Hpc Hoctx Hpark Hppid Hsl Harm".
        assert (Hpc2e : ret_pc (D5 !!! Regidx Rra : mword 64)
                        = mword_of_int (KernelSyms.bmap + 0x2e)) by (rewrite HD5ra; pcw).
        iEval (rewrite Hpc2e) in "Hpc".
        pose proof Hcs1 as Hcs1_cs.
        assert (HmDs3 : mD !!! Regidx Rs3 = add_vec ip (mword_of_int (4 * Z.of_nat fbn)))
          by (rewrite (callee_saved_lookup Hcs1_cs Rs3 ltac:(vm_compute; reflexivity));
              exact HD5s3).
        assert (HmDsp : bm_sp m mD).
        { rewrite /bm_sp
            (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
          exact HD5sp. }
        assert (HmDthr : bm_thr5 m mD).
        { intros c Hcs N2 N8 N9 N18 N19.
          rewrite (callee_saved_lookup Hcs1_cs c Hcs).
          exact (HD5thr c Hcs N2 N8 N9 N18 N19). }
        iDestruct (bm_slots_join bn 2 1 with "Hsl Hslx") as "Hsl".
        iDestruct "Harm" as "[[%Ha0z Hop] | Hsucc]".
        * (* ------ balloc FAILED: return 0 ------ *)
          iEval (rewrite -Hnn) in "Hop".
          iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x2e)) Rs1 Ra0
                    mD (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2e").
          iIntros (CID19 Hq19) "Hcg Hpc".
          set (E0 := <[Regidx Rs1 := regval_into_reg
                        (add_vec (zero_reg : mword 64) (rget mD Ra0))]> mD).
          assert (HE0s1 : E0 !!! Regidx Rs1
                          = (sign_extend' 64 (mword_of_int 0 : mword 32) : mword 64)).
          { rewrite /E0 upd_eq. rgne. rewrite Ha0z add_vec_zero_l.
            symmetry. apply bm_sext_zero. apply moi32_small. lia. }
          assert (HE0a0 : E0 !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
            by (rewrite /E0 upd_ne; [exact Ha0z | nz]).
          assert (HE0sp : bm_sp m E0)
            by (rewrite /bm_sp /E0 upd_ne; [exact HmDsp | nz]).
          assert (HE0thr : bm_thr5 m E0).
          { intros c Hcs N2 N8 N9 N18 N19.
            rewrite /E0 upd_ne; [| regne]. exact (HmDthr c Hcs N2 N8 N9 N18 N19). }
          assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x2e) : mword 64) 2
                          = mword_of_int (KernelSyms.bmap + 0x30)) by pcw.
          iEval (rewrite Hpp30) in "Hpc".
          assert (Hjmp8a : add_vec (mword_of_int (KernelSyms.bmap + 0x30) : mword 64)
                    (sign_extend' 64 (sign_extend' 13
                       (concat_vec (mword_of_int 45 : mword 8) ('b"0"))))
                  = mword_of_int (KernelSyms.bmap + 0x8a)) by pcw.
          iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x30))
                    (mword_of_int 45 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                    E0 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HE0a0; apply eq_vec_true_iff; pcw)
                    ltac:(rewrite Hjmp8a; vm_compute; reflexivity)
                    with "Hcg Hpc Hi30").
          iApply bi.later_intro.
          iIntros (CID20 Hq20) "Hcg Hpc".
          iEval (rewrite Hjmp8a) in "Hpc".
          iDestruct ("Hback" $! (blkmap_get bm fbn) with "Hcell") as "Haddrs".
          iEval (rewrite (list_insert_id (bm_cells bm) fbn (blkmap_get bm fbn)
                            (bm_cells_dir bm fbn Hdirlen Hdir))) in "Haddrs".
          iAssert (inode_map γfs ip bm) with "[Haddrs Hindblk Hindtok]" as "Hmap".
          { rewrite /inode_map /ind_res.
            iSplitL "Haddrs"; [iExact "Haddrs"|].
            iSplitL "Hindblk"; [iExact "Hindblk" | iExact "Hindtok"]. }
          iAssert (bm_frame m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6]" as "Hframe".
          { rewrite /bm_frame.
            iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
            iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
            iSplitL "Hf5"; [iExact "Hf5"|]. iExists _. iExact "Hf6". }
          iDestruct (cpu_own_transport CID18 CID20 0 true (proc_addr j) C b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iApply (bm_epilogue (CID0 := CID20) Φ j γfs bn γ cov logstart dev ip bm bm
                    data data fbn n n (mword_of_int 0 : mword 32) pidv dq dqd m E0 K C b
                    HK HE0sp HE0thr HE0s1 Hwf
                    ltac:(intros i _ _; reflexivity)
                    ltac:(intros i _ _; reflexivity)
                    ltac:(left; split; [apply moi32_small; lia | exact Hdz])
                    ltac:(left; reflexivity) ltac:(lia) ltac:(lia)
                    with "Hcg Hcnt Htext Hpc Hframe Hoctx Hpark Hppid Hidev Hmap
                          Hblocks Hsl Hop [Hcont]").
          iApply (wp_next_shift (CIDa := CID17) (CIDb := CID20) ltac:(wp_next_chain)
                    with "Hcont").
        * (* ------ balloc SUCCEEDED: install into addrs[bn] ------ *)
          iDestruct "Hsucc" as (blk) "(%Ha0v & %Hblknz & %Hblkcov & %Hblklog & Hfsb & Htok & Hop)".
          iDestruct (inode_fresh γfs bm data (bv_unsigned blk)
                       with "Htok Hindtok Hblocks") as %Hfresh.
          iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x2e)) Rs1 Ra0
                    mD (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2e").
          iIntros (CID19 Hq19) "Hcg Hpc".
          set (N0 := <[Regidx Rs1 := regval_into_reg
                        (add_vec (zero_reg : mword 64) (rget mD Ra0))]> mD).
          assert (HN0s1 : N0 !!! Regidx Rs1 = (sign_extend' 64 blk : mword 64)).
          { rewrite /N0 upd_eq. rgne. rewrite Ha0v. apply add_vec_zero_l. }
          assert (HN0a0 : N0 !!! Regidx Ra0 = (sign_extend' 64 blk : mword 64))
            by (rewrite /N0 upd_ne; [exact Ha0v | nz]).
          assert (HN0s3 : N0 !!! Regidx Rs3 = add_vec ip (mword_of_int (4 * Z.of_nat fbn)))
            by (rewrite /N0 upd_ne; [exact HmDs3 | nz]).
          assert (HN0sp : bm_sp m N0)
            by (rewrite /bm_sp /N0 upd_ne; [exact HmDsp | nz]).
          assert (HN0thr : bm_thr5 m N0).
          { intros c Hcs N2 N8 N9 N18 N19.
            rewrite /N0 upd_ne; [| regne]. exact (HmDthr c Hcs N2 N8 N9 N18 N19). }
          assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x2e) : mword 64) 2
                          = mword_of_int (KernelSyms.bmap + 0x30)) by pcw.
          iEval (rewrite Hpp30) in "Hpc".
          iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x30))
                    (mword_of_int 45 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                    N0 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HN0a0; exact (bm_eqz_false blk Hblknz))
                    with "Hcg Hpc Hi30").
          iIntros (CID20 Hq20) "Hcg Hpc".
          assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x30) : mword 64) 2
                          = mword_of_int (KernelSyms.bmap + 0x32)) by pcw.
          iEval (rewrite Hpp32) in "Hpc".
          (* ===== +0x32 sw a0,80(s3) : ip->addrs[bn] = addr ===== *)
          assert (Hsadr : add_vec (rget N0 Rs3)
                            (sign_extend' 64 (mword_of_int 80 : mword 12))
                          = i_addr ip fbn).
          { rgne. rewrite HN0s3. symmetry. apply i_addr_indexed. }
          iEval (rewrite -Hsadr) in "Hcell".
          iApply (wp_sw_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x32)) Ra0 Rs3
                    (mword_of_int 80 : mword 12) N0 (K - 6)%nat (blkmap_get bm fbn) b
                    with "Hcg Hpc Hi32 Hcell").
          iIntros (CID21 Hq21) "Hcg Hpc Hcell".
          iEval (rewrite Hsadr) in "Hcell".
          assert (Hst : trunc32 (rget N0 Ra0) = blk).
          { rgne. rewrite HN0a0. apply trunc32_sext64. }
          iEval (rewrite Hst) in "Hcell".
          assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x32) : mword 64) 4
                          = mword_of_int (KernelSyms.bmap + 0x36)) by pcw.
          iEval (rewrite Hpp36) in "Hpc".
          (* ===== +0x36 c.j +0x54 : to the shared epilogue ===== *)
          assert (Hjmp8a : add_vec (mword_of_int (KernelSyms.bmap + 0x36) : mword 64)
                    (sign_extend' 64 (sign_extend' 21
                       (concat_vec (mword_of_int 42 : mword 11) ('b"0"))))
                  = mword_of_int (KernelSyms.bmap + 0x8a)) by pcw.
          iApply (wp_cj_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x36))
                    (sign_extend' 21 (concat_vec (mword_of_int 42 : mword 11) ('b"0")))
                    N0 (K - 6)%nat b ltac:(rewrite Hjmp8a; vm_compute; reflexivity)
                    with "Hcg Hpc Hi36").
          iIntros (CID22 Hq22).
          iApply bi.later_intro.
          iIntros "Hcg Hpc".
          iEval (rewrite Hjmp8a) in "Hpc".
          (* ---- the new map ---- *)
          set (bmD := MkBlkmap (<[fbn := blk]> (bm_dir bm)) (bm_ind bm) (bm_ent bm)).
          assert (Hslotd : forall i : nat, (i <= MAXFILE)%nat ->
                    bm_slot bmD i
                    = if decide (i = fbn) then blk else bm_slot bm i)
            by (intros i Hi; apply bm_slot_insert_dir; [exact Hdirlen | exact Hdir | exact Hi]).
          assert (HwfD : blkmap_wf cov logstart bmD).
          { apply (blkmap_wf_slot_upd cov logstart bm bmD fbn blk Hwf).
            - rewrite /bmD; cbn [bm_dir]. rewrite length_insert. exact Hdirlen.
            - rewrite /bmD; cbn [bm_ent]. exact Hentlen.
            - lia.
            - exact Hslotd.
            - exact Hblknz.
            - exact Hblkcov.
            - exact Hblklog.
            - exact Hfresh.
            - rewrite /bmD; cbn [bm_ind bm_ent]. intro Hc.
              exact (blkmap_wf_no_ind cov logstart bm Hwf Hc). }
          assert (HgetD : forall i : nat, (i < MAXFILE)%nat -> i <> fbn ->
                    blkmap_get bmD i = blkmap_get bm i).
          { intros i Hi Hne.
            rewrite -(bm_slot_lt bmD i Hi) -(bm_slot_lt bm i Hi) (Hslotd i ltac:(lia)).
            destruct (decide (i = fbn)) as [->|_]; [exfalso; exact (Hne eq_refl) | reflexivity]. }
          assert (HgetDf : blkmap_get bmD fbn = blk).
          { rewrite -(bm_slot_lt bmD fbn Hfbn) (Hslotd fbn ltac:(lia)).
            destruct (decide (fbn = fbn)); [reflexivity | congruence]. }
          iDestruct ("Hback" $! blk with "Hcell") as "Haddrs".
          iEval (rewrite (bm_cells_insert_dir bm fbn blk Hdirlen Hdir)) in "Haddrs".
          iAssert (inode_map γfs ip bmD) with "[Haddrs Hindblk Hindtok]" as "Hmap".
          { rewrite /inode_map /ind_res /ind_blk /ind_tok /bmD.
            cbn [bm_ind bm_ent bm_dir].
            iSplitL "Haddrs"; [iExact "Haddrs"|].
            iSplitL "Hindblk"; [iExact "Hindblk" | iExact "Hindtok"]. }
          iDestruct (inode_blocks_insert γfs bm bmD data fbn blk
                       (replicate BSIZE (bv_0 8)) Hfbn Hdz HgetDf HgetD
                       with "Hblocks Hfsb Htok") as "Hblocks".
          iAssert (bm_frame m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6]" as "Hframe".
          { rewrite /bm_frame.
            iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
            iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
            iSplitL "Hf5"; [iExact "Hf5"|]. iExists _. iExact "Hf6". }
          iDestruct (cpu_own_transport CID18 CID22 0 true (proc_addr j) C b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iApply (bm_epilogue (CID0 := CID22) Φ j γfs bn γ cov logstart dev ip bm bmD
                    data (<[fbn := replicate BSIZE (bv_0 8)]> data) fbn n u2 blk
                    pidv dq dqd m N0 K C b
                    HK HN0sp HN0thr HN0s1 HwfD HgetD
                    ltac:(intros i Hi Hnz;
                          destruct (decide (i = fbn)) as [->|Hne];
                          [ exfalso; exact (Hnz Hdz) | exact (HgetD i Hi Hne) ])
                    ltac:(right; split;
                          [exact (eq_sym HgetDf) | rewrite HgetDf; exact Hblknz])
                    ltac:(right; split; [exact Hdz | reflexivity]) ltac:(lia) ltac:(lia)
                    with "Hcg Hcnt Htext Hpc Hframe Hoctx Hpark Hppid Hidev Hmap
                          Hblocks Hsl Hop [Hcont]").
          iApply (wp_next_shift (CIDa := CID17) (CIDb := CID22) ltac:(wp_next_chain)
                    with "Hcont").
      + (* ---------- the slot is ALREADY ALLOCATED: return it ---------- *)
        assert (Hjmp8a : add_vec (mword_of_int (KernelSyms.bmap + 0x26) : mword 64)
                  (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 50 : mword 8) ('b"0"))))
                = mword_of_int (KernelSyms.bmap + 0x8a)) by pcw.
        iApply (wp_cbnez_taken_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x26))
                  (mword_of_int 50 : mword 8) (Cregidx (mword_of_int 1)) Rs1
                  D3 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HD3s1; unfold neq_vec;
                        rewrite (bm_eqz_false _ Hdnz); reflexivity)
                  ltac:(rewrite Hjmp8a; vm_compute; reflexivity)
                  with "Hcg Hpc Hi26").
        iApply bi.later_intro.
        iIntros (CID15 Hq15) "Hcg Hpc".
        iEval (rewrite Hjmp8a) in "Hpc".
        iDestruct ("Hback" $! (blkmap_get bm fbn) with "Hcell") as "Haddrs".
        iEval (rewrite (list_insert_id (bm_cells bm) fbn (blkmap_get bm fbn)
                          (bm_cells_dir bm fbn Hdirlen Hdir))) in "Haddrs".
        iAssert (inode_map γfs ip bm) with "[Haddrs Hindblk Hindtok]" as "Hmap".
        { rewrite /inode_map /ind_res.
          iSplitL "Haddrs"; [iExact "Haddrs"|].
          iSplitL "Hindblk"; [iExact "Hindblk" | iExact "Hindtok"]. }
        iAssert (bm_frame m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6]" as "Hframe".
        { rewrite /bm_frame.
          iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
          iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
          iSplitL "Hf5"; [iExact "Hf5"|]. iExists _. iExact "Hf6". }
        iDestruct (cpu_own_transport CID CID15 0 true (proc_addr j) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (bm_epilogue (CID0 := CID15) Φ j γfs bn γ cov logstart dev ip bm bm
                  data data fbn n n (blkmap_get bm fbn) pidv dq dqd m D3 K C b
                  HK HD3sp HD3thr HD3s1 Hwf
                  ltac:(intros i _ _; reflexivity)
                  ltac:(intros i _ _; reflexivity)
                  ltac:(right; split; [reflexivity | exact Hdnz])
                  ltac:(left; reflexivity) ltac:(lia) ltac:(lia)
                  with "Hcg Hcnt Htext Hpc Hframe Hoctx Hpark Hppid Hidev Hmap
                        Hblocks Hsl Hop [Hcont]").
        iApply (wp_next_shift (CIDa := CID) (CIDb := CID15) ltac:(wp_next_chain)
                  with "Hcont").
    - (* ================ THE INDIRECT ARM (bn >= NDIRECT) ================ *)
      assert (Hge : (NDIRECT <= fbn)%nat) by lia.
      remember (fbn - NDIRECT)%nat as q eqn:Hqeq.
      assert (Hfbnq : fbn = (NDIRECT + q)%nat) by (unfold NDIRECT in *; lia).
      assert (Hqlt : (q < NINDIRECT)%nat) by (unfold NDIRECT, NINDIRECT in *; lia).
      assert (Hqz : Z.of_nat fbn - 12 = Z.of_nat q) by (unfold NDIRECT in *; lia).
      assert (Huq : uint (mword_of_int (Z.of_nat q) : mword 64) = Z.of_nat q)
        by (apply bm_uint_moi; unfold NINDIRECT in Hqlt; lia).
      assert (Hu255 : uint (mword_of_int 255 : mword 64) = 255)
        by (apply bm_uint_moi; lia).
      assert (Hjmp38 : add_vec (mword_of_int (KernelSyms.bmap + 0x12) : mword 64)
                (sign_extend' 64 (mword_of_int 38 : mword 13))
              = mword_of_int (KernelSyms.bmap + 0x38)) by pcw.
      iApply (wp_bltu_taken_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x12))
                (mword_of_int 38 : mword 13) Ra1 Ra5 R4 (K - 6)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HR4a5 HR4a1; unfold zopz0zI_u;
                      rewrite Hu11 Hufbn; apply Z.ltb_lt;
                      unfold NDIRECT in Hge; lia)
                ltac:(rewrite Hjmp38; vm_compute; reflexivity)
                with "Hcg Hpc Hi12").
      iApply bi.later_intro.
      iIntros (CID10 Hq10) "Hcg Hpc".
      iEval (rewrite Hjmp38) in "Hpc".
      iPoseProof (bmi_38 with "Htext") as "Hi38".
      iPoseProof (bmi_3c with "Htext") as "Hi3c".
      iPoseProof (bmi_3e with "Htext") as "Hi3e".
      iPoseProof (bmi_40 with "Htext") as "Hi40".
      iPoseProof (bmi_44 with "Htext") as "Hi44".
      iPoseProof (bmi_48 with "Htext") as "Hi48".
      iPoseProof (bmi_4c with "Htext") as "Hi4c".
      (* ===== +0x38 addiw a5,a1,-12 ===== *)
      iApply (wp_addiw_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x38)) Ra5 Ra1
                (mword_of_int 4084 : mword 12) R4 (K - 6)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi38").
      iIntros (CID11 Hq11) "Hcg Hpc".
      set (J0 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (rget R4 Ra1)
                          (sign_extend' 64 (mword_of_int 4084 : mword 12))) 31 0))]> R4).
      assert (HJ0a5 : J0 !!! Regidx Ra5 = (mword_of_int (Z.of_nat q) : mword 64)).
      { rewrite /J0 upd_eq. rgne. rewrite HR4a1.
        rewrite (bm_addiw_m12 (Z.of_nat fbn) ltac:(unfold NDIRECT in Hge; lia)
                   ltac:(lia)) Hqz. reflexivity. }
      assert (HJ0a0 : J0 !!! Regidx Ra0 = ip)
        by (rewrite /J0 upd_ne; [exact HR4a0 | nz]).
      assert (HJ0s2 : J0 !!! Regidx Rs2 = ip)
        by (rewrite /J0 upd_ne; [exact HR4s2 | nz]).
      assert (HJ0sp : bm_sp m J0)
        by (rewrite /bm_sp /J0 upd_ne; [exact HR4sp | nz]).
      assert (HJ0thr : bm_thr5 m J0).
      { intros c Hcs N2 N8 N9 N18 N19.
        rewrite /J0 upd_ne; [| regne]. exact (HR4thr c Hcs N2 N8 N9 N18 N19). }
      assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.bmap + 0x38) : mword 64) 4
                      = mword_of_int (KernelSyms.bmap + 0x3c)) by pcw.
      iEval (rewrite Hpp3c) in "Hpc".
      (* ===== +0x3c c.mv a4,a5 ===== *)
      iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x3c)) Ra4 Ra5
                J0 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3c").
      iIntros (CID12 Hq12) "Hcg Hpc".
      set (J1 := <[Regidx Ra4 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget J0 Ra5))]> J0).
      assert (HJ1a4 : J1 !!! Regidx Ra4 = (mword_of_int (Z.of_nat q) : mword 64)).
      { rewrite /J1 upd_eq. rgne. rewrite HJ0a5. apply add_vec_zero_l. }
      assert (HJ1a5 : J1 !!! Regidx Ra5 = (mword_of_int (Z.of_nat q) : mword 64))
        by (rewrite /J1 upd_ne; [exact HJ0a5 | nz]).
      assert (HJ1a0 : J1 !!! Regidx Ra0 = ip)
        by (rewrite /J1 upd_ne; [exact HJ0a0 | nz]).
      assert (HJ1s2 : J1 !!! Regidx Rs2 = ip)
        by (rewrite /J1 upd_ne; [exact HJ0s2 | nz]).
      assert (HJ1sp : bm_sp m J1)
        by (rewrite /bm_sp /J1 upd_ne; [exact HJ0sp | nz]).
      assert (HJ1thr : bm_thr5 m J1).
      { intros c Hcs N2 N8 N9 N18 N19.
        rewrite /J1 upd_ne; [| regne]. exact (HJ0thr c Hcs N2 N8 N9 N18 N19). }
      assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.bmap + 0x3c) : mword 64) 2
                      = mword_of_int (KernelSyms.bmap + 0x3e)) by pcw.
      iEval (rewrite Hpp3e) in "Hpc".
      (* ===== +0x3e c.mv s3,a5 : s3 := bn - NDIRECT ===== *)
      iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x3e)) Rs3 Ra5
                J1 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3e").
      iIntros (CID13 Hq13) "Hcg Hpc".
      set (J2 := <[Regidx Rs3 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget J1 Ra5))]> J1).
      assert (HJ2s3 : J2 !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64)).
      { rewrite /J2 upd_eq. rgne. rewrite HJ1a5. apply add_vec_zero_l. }
      assert (HJ2a4 : J2 !!! Regidx Ra4 = (mword_of_int (Z.of_nat q) : mword 64))
        by (rewrite /J2 upd_ne; [exact HJ1a4 | nz]).
      assert (HJ2a0 : J2 !!! Regidx Ra0 = ip)
        by (rewrite /J2 upd_ne; [exact HJ1a0 | nz]).
      assert (HJ2s2 : J2 !!! Regidx Rs2 = ip)
        by (rewrite /J2 upd_ne; [exact HJ1s2 | nz]).
      assert (HJ2sp : bm_sp m J2)
        by (rewrite /bm_sp /J2 upd_ne; [exact HJ1sp | nz]).
      assert (HJ2thr : bm_thr5 m J2).
      { intros c Hcs N2 N8 N9 N18 N19.
        rewrite /J2 upd_ne; [| regne]. exact (HJ1thr c Hcs N2 N8 N9 N18 N19). }
      assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x3e) : mword 64) 2
                      = mword_of_int (KernelSyms.bmap + 0x40)) by pcw.
      iEval (rewrite Hpp40) in "Hpc".
      (* ===== +0x40 li a5,255 ===== *)
      iApply (wp_li4_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x40)) Ra5
                (mword_of_int 255 : mword 12) (mword_of_int 255 : mword 64)
                J2 (K - 6)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                with "Hcg Hpc Hi40").
      iIntros (CID14 Hq14) "Hcg Hpc".
      set (J3 := <[Regidx Ra5 := regval_into_reg (mword_of_int 255 : mword 64)]> J2).
      assert (HJ3a5 : J3 !!! Regidx Ra5 = (mword_of_int 255 : mword 64))
        by (rewrite /J3; apply upd_eq).
      assert (HJ3a4 : J3 !!! Regidx Ra4 = (mword_of_int (Z.of_nat q) : mword 64))
        by (rewrite /J3 upd_ne; [exact HJ2a4 | nz]).
      assert (HJ3s3 : J3 !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64))
        by (rewrite /J3 upd_ne; [exact HJ2s3 | nz]).
      assert (HJ3a0 : J3 !!! Regidx Ra0 = ip)
        by (rewrite /J3 upd_ne; [exact HJ2a0 | nz]).
      assert (HJ3s2 : J3 !!! Regidx Rs2 = ip)
        by (rewrite /J3 upd_ne; [exact HJ2s2 | nz]).
      assert (HJ3sp : bm_sp m J3)
        by (rewrite /bm_sp /J3 upd_ne; [exact HJ2sp | nz]).
      assert (HJ3thr : bm_thr5 m J3).
      { intros c Hcs N2 N8 N9 N18 N19.
        rewrite /J3 upd_ne; [| regne]. exact (HJ2thr c Hcs N2 N8 N9 N18 N19). }
      assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x40) : mword 64) 4
                      = mword_of_int (KernelSyms.bmap + 0x44)) by pcw.
      iEval (rewrite Hpp44) in "Hpc".
      (* ===== +0x44 bltu a5,a4 : THE DEAD PANIC TEST, always false ===== *)
      iApply (wp_bltu_fall_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x44))
                (mword_of_int 110 : mword 13) Ra4 Ra5 J3 (K - 6)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HJ3a5 HJ3a4; unfold zopz0zI_u;
                      rewrite Hu255 Huq; apply Z.ltb_ge;
                      unfold NINDIRECT in Hqlt; lia)
                with "Hcg Hpc Hi44").
      iIntros (CID15 Hq15) "Hcg Hpc".
      assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x44) : mword 64) 4
                      = mword_of_int (KernelSyms.bmap + 0x48)) by pcw.
      iEval (rewrite Hpp48) in "Hpc".
      (* ===== +0x48 lw s1,128(a0) : s1 := ip->addrs[NDIRECT] ===== *)
      iDestruct (inode_addrs_acc ip (bm_cells bm) NDIRECT (bm_ind bm)
                   (bm_cells_ind bm Hdirlen) with "Haddrs") as "[Hcell Hback]".
      assert (Hiadr : add_vec (rget J3 Ra0)
                        (sign_extend' 64 (mword_of_int 128 : mword 12))
                      = i_addr ip NDIRECT).
      { rgne. rewrite HJ3a0. symmetry. apply i_addr_ndirect. }
      iEval (rewrite -Hiadr) in "Hcell".
      iApply (wp_lw_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x48)) Rs1 Ra0
                (mword_of_int 128 : mword 12) J3 (K - 6)%nat (bm_ind bm) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi48 Hcell").
      iIntros (CID16 Hq16) "Hcg Hpc Hcell".
      iEval (rewrite Hiadr) in "Hcell".
      set (J4 := <[Regidx Rs1 := regval_into_reg
                    (sign_extend' 64 (bm_ind bm : mword 32))]> J3).
      assert (HJ4s1 : J4 !!! Regidx Rs1
                      = (sign_extend' 64 (bm_ind bm : mword 32) : mword 64))
        by (rewrite /J4; apply upd_eq).
      assert (HJ4s3 : J4 !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64))
        by (rewrite /J4 upd_ne; [exact HJ3s3 | nz]).
      assert (HJ4a0 : J4 !!! Regidx Ra0 = ip)
        by (rewrite /J4 upd_ne; [exact HJ3a0 | nz]).
      assert (HJ4s2 : J4 !!! Regidx Rs2 = ip)
        by (rewrite /J4 upd_ne; [exact HJ3s2 | nz]).
      assert (HJ4sp : bm_sp m J4)
        by (rewrite /bm_sp /J4 upd_ne; [exact HJ3sp | nz]).
      assert (HJ4thr : bm_thr5 m J4).
      { intros c Hcs N2 N8 N9 N18 N19.
        rewrite /J4 upd_ne; [| regne]. exact (HJ3thr c Hcs N2 N8 N9 N18 N19). }
      assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.bmap + 0x48) : mword 64) 4
                      = mword_of_int (KernelSyms.bmap + 0x4c)) by pcw.
      iEval (rewrite Hpp4c) in "Hpc".
      (* ===== +0x4c c.bnez s1 ===== *)
      destruct (decide (bv_unsigned (bm_ind bm) = 0)) as [Hiz|Hinz].
      + (* ------ NO indirect block yet: allocate one ------ *)
        pose proof (blkmap_wf_no_ind cov logstart bm Hwf Hiz) as Hentzero.
        iApply (wp_cbnez_fall_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x4c))
                  (mword_of_int 10 : mword 8) (Cregidx (mword_of_int 1)) Rs1
                  J4 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HJ4s1; unfold neq_vec;
                        rewrite (bm_eqz_true _ Hiz); reflexivity)
                  with "Hcg Hpc Hi4c").
        iIntros (CID17 Hq17) "Hcg Hpc".
        assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.bmap + 0x4c) : mword 64) 2
                        = mword_of_int (KernelSyms.bmap + 0x4e)) by pcw.
        iEval (rewrite Hpp4e) in "Hpc".
        iPoseProof (bmi_4e with "Htext") as "Hi4e".
        iPoseProof (bmi_50 with "Htext") as "Hi50".
        iPoseProof (bmi_54 with "Htext") as "Hi54".
        iPoseProof (bmi_56 with "Htext") as "Hi56".
        iPoseProof (bmi_58 with "Htext") as "Hi58".
        iPoseProof (bmi_5a with "Htext") as "Hi5a".
        iPoseProof (bmi_5e with "Htext") as "Hi5e".
        (* ===== +0x4e c.lw a0,0(a0) ===== *)
        assert (Hdadr : add_vec (rget J4 Ra0)
                          (sign_extend' 64 (mword_of_int 0 : mword 12)) = i_dev ip).
        { rgne. rewrite HJ4a0. reflexivity. }
        iEval (rewrite -Hdadr) in "Hidev".
        iApply (wp_clw_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x4e)) Ra0 Ra0
                  (mword_of_int 0 : mword 12) J4 (K - 6)%nat dev b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4e Hidev").
        iIntros (CID18 Hq18) "Hcg Hpc Hidev".
        iEval (rewrite Hdadr) in "Hidev".
        set (P0 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> J4).
        assert (HP0a0 : P0 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
          by (rewrite /P0; apply upd_eq).
        assert (HP0s3 : P0 !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64))
          by (rewrite /P0 upd_ne; [exact HJ4s3 | nz]).
        assert (HP0s2 : P0 !!! Regidx Rs2 = ip)
          by (rewrite /P0 upd_ne; [exact HJ4s2 | nz]).
        assert (HP0sp : bm_sp m P0)
          by (rewrite /bm_sp /P0 upd_ne; [exact HJ4sp | nz]).
        assert (HP0thr : bm_thr5 m P0).
        { intros c Hcs N2 N8 N9 N18 N19.
          rewrite /P0 upd_ne; [| regne]. exact (HJ4thr c Hcs N2 N8 N9 N18 N19). }
        assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x4e) : mword 64) 2
                        = mword_of_int (KernelSyms.bmap + 0x50)) by pcw.
        iEval (rewrite Hpp50) in "Hpc".
        (* ===== +0x50 jal ra,balloc ===== *)
        iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x50)) Rra
                  (mword_of_int 2096810 : mword 21) P0 (K - 6)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi50").
        iIntros (CID19 Hq19) "Hcg Hpc".
        set (P1 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.bmap + 0x50) : mword 64) 4)]> P0).
        assert (Htgtba : add_vec (mword_of_int (KernelSyms.bmap + 0x50) : mword 64)
                           (sign_extend' 64 (mword_of_int 2096810 : mword 21))
                         = mword_of_int KernelSyms.balloc) by pcw.
        iEval (rewrite Htgtba) in "Hpc".
        assert (HP1a0 : P1 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
          by (rewrite /P1 upd_ne; [exact HP0a0 | nz]).
        assert (HP1s3 : P1 !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64))
          by (rewrite /P1 upd_ne; [exact HP0s3 | nz]).
        assert (HP1s2 : P1 !!! Regidx Rs2 = ip)
          by (rewrite /P1 upd_ne; [exact HP0s2 | nz]).
        assert (HP1sp : bm_sp m P1)
          by (rewrite /bm_sp /P1 upd_ne; [exact HP0sp | nz]).
        assert (HP1ra : P1 !!! Regidx Rra
                        = add_vec_int (mword_of_int (KernelSyms.bmap + 0x50) : mword 64) 4)
          by (rewrite /P1; apply upd_eq).
        assert (HP1thr : bm_thr5 m P1).
        { intros c Hcs N2 N8 N9 N18 N19.
          rewrite /P1 upd_ne; [| regne]. exact (HP0thr c Hcs N2 N8 N9 N18 N19). }
        iDestruct (cpu_own_transport CID CID19 0 true (proc_addr j) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (wp_next_shift (CIDa := CID) (CIDb := CID19) ltac:(wp_next_chain)
                     with "Hcont") as "Hcont".
        assert (HKba : (K_balloc <= K - 6)%nat) by (unfold K_balloc; lia).
        remember (n - 2)%nat as u2 eqn:Hu2eq.
        assert (Hnn : n = (2 + u2)%nat) by lia.
        iEval (rewrite Hnn) in "Hop".
        iDestruct (bm_slots_split bn 2 1 with "Hsl") as "[Hsl Hslx]".
        iApply (BA.wp_balloc_sconf Φ γs j γl γu γd γk pd pav pu bn γ γfs
                  cov logstart dev u2 pidv dq P1 (K - 6)%nat true C b
                  HKba Hgeom Hj Hgl HP1a0 eq_refl
                  with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hppid Hprocs Hscheds
                        Hoctx Hpark Hdevi Hdgeom Hdlock Hsl Hop").
        iIntros (CID20 Hq20 mP) "%Hcs1 Hcg Hcnt Hpc Hoctx Hpark Hppid Hsl Harm".
        assert (Hpc54 : ret_pc (P1 !!! Regidx Rra : mword 64)
                        = mword_of_int (KernelSyms.bmap + 0x54)) by (rewrite HP1ra; pcw).
        iEval (rewrite Hpc54) in "Hpc".
        pose proof Hcs1 as Hcs1_cs.
        assert (HmPs3 : mP !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64))
          by (rewrite (callee_saved_lookup Hcs1_cs Rs3 ltac:(vm_compute; reflexivity));
              exact HP1s3).
        assert (HmPs2 : mP !!! Regidx Rs2 = ip)
          by (rewrite (callee_saved_lookup Hcs1_cs Rs2 ltac:(vm_compute; reflexivity));
              exact HP1s2).
        assert (HmPsp : bm_sp m mP).
        { rewrite /bm_sp
            (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
          exact HP1sp. }
        assert (HmPthr : bm_thr5 m mP).
        { intros c Hcs N2 N8 N9 N18 N19.
          rewrite (callee_saved_lookup Hcs1_cs c Hcs).
          exact (HP1thr c Hcs N2 N8 N9 N18 N19). }
        iDestruct (bm_slots_join bn 2 1 with "Hsl Hslx") as "Hsl".
        (* ===== +0x54 c.mv s1,a0 ===== *)
        iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x54)) Rs1 Ra0
                  mP (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi54").
        iIntros (CID21 Hq21) "Hcg Hpc".
        set (P2 := <[Regidx Rs1 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (rget mP Ra0))]> mP).
        assert (HP2a0 : P2 !!! Regidx Ra0 = (mP !!! Regidx Ra0 : mword 64))
          by (rewrite /P2 upd_ne; [reflexivity | nz]).
        assert (HP2s3 : P2 !!! Regidx Rs3 = (mword_of_int (Z.of_nat q) : mword 64))
          by (rewrite /P2 upd_ne; [exact HmPs3 | nz]).
        assert (HP2s2 : P2 !!! Regidx Rs2 = ip)
          by (rewrite /P2 upd_ne; [exact HmPs2 | nz]).
        assert (HP2sp : bm_sp m P2)
          by (rewrite /bm_sp /P2 upd_ne; [exact HmPsp | nz]).
        assert (HP2thr : bm_thr5 m P2).
        { intros c Hcs N2 N8 N9 N18 N19.
          rewrite /P2 upd_ne; [| regne]. exact (HmPthr c Hcs N2 N8 N9 N18 N19). }
        assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x54) : mword 64) 2
                        = mword_of_int (KernelSyms.bmap + 0x56)) by pcw.
        iEval (rewrite Hpp56) in "Hpc".
        iDestruct "Harm" as "[[%Ha0z Hop] | Hsucc]".
        * (* ------ balloc FAILED: return 0 ------ *)
          iEval (rewrite -Hnn) in "Hop".
          assert (HP2s1 : P2 !!! Regidx Rs1
                          = (sign_extend' 64 (mword_of_int 0 : mword 32) : mword 64)).
          { rewrite /P2 upd_eq. rgne. rewrite Ha0z add_vec_zero_l.
            symmetry. apply bm_sext_zero. apply moi32_small. lia. }
          assert (HP2a0z : P2 !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
            by (rewrite HP2a0; exact Ha0z).
          assert (Hjmp8a : add_vec (mword_of_int (KernelSyms.bmap + 0x56) : mword 64)
                    (sign_extend' 64 (sign_extend' 13
                       (concat_vec (mword_of_int 26 : mword 8) ('b"0"))))
                  = mword_of_int (KernelSyms.bmap + 0x8a)) by pcw.
          iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x56))
                    (mword_of_int 26 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                    P2 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HP2a0z; apply eq_vec_true_iff; pcw)
                    ltac:(rewrite Hjmp8a; vm_compute; reflexivity)
                    with "Hcg Hpc Hi56").
          iApply bi.later_intro.
          iIntros (CID22 Hq22) "Hcg Hpc".
          iEval (rewrite Hjmp8a) in "Hpc".
          iDestruct ("Hback" $! (bm_ind bm) with "Hcell") as "Haddrs".
          iEval (rewrite (list_insert_id (bm_cells bm) NDIRECT (bm_ind bm)
                            (bm_cells_ind bm Hdirlen))) in "Haddrs".
          iAssert (inode_map γfs ip bm) with "[Haddrs Hindblk Hindtok]" as "Hmap".
          { rewrite /inode_map /ind_res.
            iSplitL "Haddrs"; [iExact "Haddrs"|].
            iSplitL "Hindblk"; [iExact "Hindblk" | iExact "Hindtok"]. }
          iAssert (bm_frame m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6]" as "Hframe".
          { rewrite /bm_frame.
            iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
            iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
            iSplitL "Hf5"; [iExact "Hf5"|]. iExists _. iExact "Hf6". }
          iDestruct (cpu_own_transport CID20 CID22 0 true (proc_addr j) C b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iApply (bm_epilogue (CID0 := CID22) Φ j γfs bn γ cov logstart dev ip bm bm
                    data data fbn n n (mword_of_int 0 : mword 32) pidv dq dqd m P2 K C b
                    HK HP2sp HP2thr HP2s1 Hwf
                    ltac:(intros i _ _; reflexivity)
                    ltac:(intros i _ _; reflexivity)
                    ltac:(left; split;
                          [apply moi32_small; lia
                          | rewrite (blkmap_get_ent bm fbn Hge) Hentzero
                              lookup_total_replicate_2;
                            [reflexivity | unfold NINDIRECT in *; lia]])
                    ltac:(left; reflexivity) ltac:(lia) ltac:(lia)
                    with "Hcg Hcnt Htext Hpc Hframe Hoctx Hpark Hppid Hidev Hmap
                          Hblocks Hsl Hop [Hcont]").
          iApply (wp_next_shift (CIDa := CID19) (CIDb := CID22) ltac:(wp_next_chain)
                    with "Hcont").
        * (* ------ balloc SUCCEEDED: install the indirect block ------ *)
          iDestruct "Hsucc" as (blk) "(%Ha0v & %Hblknz & %Hblkcov & %Hblklog & Hfsb & Htok & Hop)".
          iDestruct (inode_fresh γfs bm data (bv_unsigned blk)
                       with "Htok Hindtok Hblocks") as %Hfresh.
          assert (HP2s1 : P2 !!! Regidx Rs1 = (sign_extend' 64 blk : mword 64)).
          { rewrite /P2 upd_eq. rgne. rewrite Ha0v. apply add_vec_zero_l. }
          assert (HP2a0v : P2 !!! Regidx Ra0 = (sign_extend' 64 blk : mword 64))
            by (rewrite HP2a0; exact Ha0v).
          iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x56))
                    (mword_of_int 26 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                    P2 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HP2a0v; exact (bm_eqz_false blk Hblknz))
                    with "Hcg Hpc Hi56").
          iIntros (CID22 Hq22) "Hcg Hpc".
          assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x56) : mword 64) 2
                          = mword_of_int (KernelSyms.bmap + 0x58)) by pcw.
          iEval (rewrite Hpp58) in "Hpc".
          (* ===== +0x58 c.sdsp s4,0(sp) : s4 goes to the frame ===== *)
          assert (Hc6P : add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
          { rewrite HP2sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
            f_equal; try pcw. }
          iEval (rewrite -Hc6P) in "Hf6".
          iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x58)) (mword_of_int 0 : mword 6)
                    Rs4 P2 (K - 6)%nat v6 b with "Hcg Hpc Hi58 Hf6").
          iIntros (CID23 Hq23) "Hcg Hpc Hf6".
          assert (HP2s4 : (P2 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64))
            by (apply HP2thr; bmidx).
          iEval (rewrite Hc6P; rgne; rewrite HP2s4) in "Hf6".
          assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.bmap + 0x58) : mword 64) 2
                          = mword_of_int (KernelSyms.bmap + 0x5a)) by pcw.
          iEval (rewrite Hpp5a) in "Hpc".
          (* ===== +0x5a sw a0,128(s2) : ip->addrs[NDIRECT] = addr ===== *)
          assert (Hsadr : add_vec (rget P2 Rs2)
                            (sign_extend' 64 (mword_of_int 128 : mword 12))
                          = i_addr ip NDIRECT).
          { rgne. rewrite HP2s2. symmetry. apply i_addr_ndirect. }
          iEval (rewrite -Hsadr) in "Hcell".
          iApply (wp_sw_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x5a)) Ra0 Rs2
                    (mword_of_int 128 : mword 12) P2 (K - 6)%nat (bm_ind bm) b
                    with "Hcg Hpc Hi5a Hcell").
          iIntros (CID24 Hq24) "Hcg Hpc Hcell".
          iEval (rewrite Hsadr) in "Hcell".
          assert (Hst : trunc32 (rget P2 Ra0) = blk).
          { rgne. rewrite HP2a0v. apply trunc32_sext64. }
          iEval (rewrite Hst) in "Hcell".
          assert (Hpp5e : add_vec_int (mword_of_int (KernelSyms.bmap + 0x5a) : mword 64) 4
                          = mword_of_int (KernelSyms.bmap + 0x5e)) by pcw.
          iEval (rewrite Hpp5e) in "Hpc".
          (* ===== +0x5e c.j +0x4 ===== *)
          assert (Hjmp62 : add_vec (mword_of_int (KernelSyms.bmap + 0x5e) : mword 64)
                    (sign_extend' 64 (sign_extend' 21
                       (concat_vec (mword_of_int 2 : mword 11) ('b"0"))))
                  = mword_of_int (KernelSyms.bmap + 0x62)) by pcw.
          iApply (wp_cj_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x5e))
                    (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0")))
                    P2 (K - 6)%nat b ltac:(rewrite Hjmp62; vm_compute; reflexivity)
                    with "Hcg Hpc Hi5e").
          iIntros (CID25 Hq25).
          iApply bi.later_intro.
          iIntros "Hcg Hpc".
          iEval (rewrite Hjmp62) in "Hpc".
          (* ---- the map with the new indirect block ---- *)
          set (bmI := MkBlkmap (bm_dir bm) blk (replicate NINDIRECT (bv_0 32))).
          assert (Hsloti : forall i : nat, (i <= MAXFILE)%nat ->
                    bm_slot bmI i
                    = if decide (i = MAXFILE) then blk else bm_slot bm i)
            by (intros i Hi; apply bm_slot_insert_ind; [exact Hentzero | exact Hi]).
          assert (HwfI : blkmap_wf cov logstart bmI).
          { apply (blkmap_wf_slot_upd cov logstart bm bmI MAXFILE blk Hwf).
            - rewrite /bmI; cbn [bm_dir]. exact Hdirlen.
            - rewrite /bmI; cbn [bm_ent]. rewrite length_replicate. reflexivity.
            - lia.
            - exact Hsloti.
            - exact Hblknz.
            - exact Hblkcov.
            - exact Hblklog.
            - exact Hfresh.
            - rewrite /bmI; cbn [bm_ind]. intro Hc. exfalso. exact (Hblknz Hc). }
          assert (HgetI : forall i : nat, (i < MAXFILE)%nat ->
                    blkmap_get bmI i = blkmap_get bm i).
          { intros i Hi.
            rewrite -(bm_slot_lt bmI i Hi) -(bm_slot_lt bm i Hi) (Hsloti i ltac:(lia)).
            destruct (decide (i = MAXFILE)) as [->|_]; [lia | reflexivity]. }
          iDestruct ("Hback" $! blk with "Hcell") as "Haddrs".
          iEval (rewrite (bm_cells_insert_ind bm blk (replicate NINDIRECT (bv_0 32))
                            Hdirlen)) in "Haddrs".
          assert (Hindz : ind_bytes (replicate NINDIRECT (bv_0 32))
                          = replicate BSIZE (bv_0 8))
            by (unfold NINDIRECT, BSIZE; rewrite ind_bytes_replicate; reflexivity).
          iAssert (ind_blk γfs bmI) with "[Hfsb]" as "Hindblk2".
          { rewrite /ind_blk /bmI. cbn [bm_ind bm_ent].
            case_decide as Hz; [exfalso; exact (Hblknz Hz)|].
            rewrite Hindz. iExact "Hfsb". }
          iAssert (ind_tok γfs bmI) with "[Htok]" as "Hindtok2".
          { rewrite /ind_tok /bmI. cbn [bm_ind].
            case_decide as Hz; [exfalso; exact (Hblknz Hz)|]. iExact "Htok". }
          iDestruct (inode_blocks_frame γfs bm bmI data data
                       ltac:(intros i Hi; split; [exact (HgetI i Hi) | reflexivity])
                       with "Hblocks") as "Hblocks".
          iAssert (bm_frame4 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6]" as "Hframe".
          { rewrite /bm_frame4.
            iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
            iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
            iSplitL "Hf5"; [iExact "Hf5"|]. iExact "Hf6". }
          iDestruct (cpu_own_transport CID20 CID25 0 true (proc_addr j) C b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iApply (bm_indirect_tail (CID0 := CID25) Φ γs j γl γu γd γk pd pav pu
                    γfs bn γ cov logstart dev ip bm bmI data fbn q n u2
                    pidv dq dqd m P2 K C b
                    HK Hgeom HwfI Hfbnq Hqlt HgetI
                    ltac:(rewrite /bmI; cbn [bm_ind]; exact Hblknz)
                    ltac:(lia) ltac:(lia) ltac:(lia) Hj Hgl HP2sp
                    ltac:(intros c Hcs N2 N8 N9 N18 N19 N20;
                          exact (HP2thr c Hcs N2 N8 N9 N18 N19))
                    ltac:(rewrite /bmI; cbn [bm_ind]; exact HP2s1) HP2s2 HP2s3
                    with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hprocs Hscheds
                          Hdevi Hdgeom Hdlock Hframe Hoctx Hpark Hppid Hidev
                          Haddrs Hindblk2 Hindtok2 Hblocks Hsl Hop [Hcont]").
          iApply (wp_next_shift (CIDa := CID19) (CIDb := CID25) ltac:(wp_next_chain)
                    with "Hcont").
      + (* ------ the indirect block EXISTS ------ *)
        assert (Hjmp60 : add_vec (mword_of_int (KernelSyms.bmap + 0x4c) : mword 64)
                  (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 10 : mword 8) ('b"0"))))
                = mword_of_int (KernelSyms.bmap + 0x60)) by pcw.
        iApply (wp_cbnez_taken_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x4c))
                  (mword_of_int 10 : mword 8) (Cregidx (mword_of_int 1)) Rs1
                  J4 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HJ4s1; unfold neq_vec;
                        rewrite (bm_eqz_false _ Hinz); reflexivity)
                  ltac:(rewrite Hjmp60; vm_compute; reflexivity)
                  with "Hcg Hpc Hi4c").
        iApply bi.later_intro.
        iIntros (CID17 Hq17) "Hcg Hpc".
        iEval (rewrite Hjmp60) in "Hpc".
        iPoseProof (bmi_60 with "Htext") as "Hi60".
        (* ===== +0x60 c.sdsp s4,0(sp) ===== *)
        assert (Hc6J : add_vec (J4 !!! Regidx csp_rs1 : mword 64)
                  (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
        { rewrite HJ4sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
          f_equal; try pcw. }
        iEval (rewrite -Hc6J) in "Hf6".
        iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.bmap + 0x60)) (mword_of_int 0 : mword 6)
                  Rs4 J4 (K - 6)%nat v6 b with "Hcg Hpc Hi60 Hf6").
        iIntros (CID18 Hq18) "Hcg Hpc Hf6".
        assert (HJ4s4 : (J4 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64))
          by (apply HJ4thr; bmidx).
        iEval (rewrite Hc6J; rgne; rewrite HJ4s4) in "Hf6".
        assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.bmap + 0x60) : mword 64) 2
                        = mword_of_int (KernelSyms.bmap + 0x62)) by pcw.
        iEval (rewrite Hpp62) in "Hpc".
        iDestruct ("Hback" $! (bm_ind bm) with "Hcell") as "Haddrs".
        iEval (rewrite (list_insert_id (bm_cells bm) NDIRECT (bm_ind bm)
                          (bm_cells_ind bm Hdirlen))) in "Haddrs".
        iAssert (bm_frame4 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6]" as "Hframe".
        { rewrite /bm_frame4.
          iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
          iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
          iSplitL "Hf5"; [iExact "Hf5"|]. iExact "Hf6". }
        iDestruct (cpu_own_transport CID CID18 0 true (proc_addr j) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (bm_indirect_tail (CID0 := CID18) Φ γs j γl γu γd γk pd pav pu
                  γfs bn γ cov logstart dev ip bm bm data fbn q n n
                  pidv dq dqd m J4 K C b
                  HK Hgeom Hwf Hfbnq Hqlt ltac:(intros i _; reflexivity) Hinz
                  ltac:(lia) ltac:(lia) ltac:(lia) Hj Hgl HJ4sp
                  ltac:(intros c Hcs N2 N8 N9 N18 N19 N20;
                        exact (HJ4thr c Hcs N2 N8 N9 N18 N19))
                  HJ4s1 HJ4s2 HJ4s3
                  with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hprocs Hscheds
                        Hdevi Hdgeom Hdlock Hframe Hoctx Hpark Hppid Hidev
                        Haddrs Hindblk Hindtok Hblocks Hsl Hop [Hcont]").
        iApply (wp_next_shift (CIDa := CID) (CIDb := CID18) ltac:(wp_next_chain)
                  with "Hcont").
  Qed.

End ProofBmapMain.

End BmapProof.
