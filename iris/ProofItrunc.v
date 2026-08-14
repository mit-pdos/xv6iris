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
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfVc WpSconfBtype.
Require Import ByteBuf.
Require Import PanicStub.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import SchedCtx.
Require Import WpUart.
Require Import BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IcacheInv.
Require Import SpecBread SpecBrelse SpecBfree SpecIupdate.
Require Import SpecItrunc.
Require Import ProofBmapParts.
Require Import ProofItruncParts.
Require Import CodeItrunc.
From Kernel Require KernelSyms.
Import Defs.

Local Open Scope Z_scope.

Module ItruncProof (BR : BREAD) (BF : BFREE) (BL : BRELSE) (IU : IUPDATE)
  : ITRUNC.

Local Ltac regne := reg_ne_side.

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac itidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].
Notation Rz := (mword_of_int 0 : mword 5).

Notation IT := KernelSyms.itrunc.

(* ===================================================================== *)
(*  The continuation: itrunc's postcondition, as a resource               *)
(* ===================================================================== *)
Section ItruncCont.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}.

  Definition it_cont `{GEN : GenId} `{CID0 : CpuId}
      (γ : log_names) (γfs : fs_names) (γi : gname) (bn : bio_names)
      (cov : gset Z) (logstart bmapstart inodestart size : Z)
      (used : gset Z) (dev : mword 32)
      (ip : mword 64) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (u : nat) (Sbf : gset Z)
      (pidv : mword 32) (dq dqd dqn dqb dqs : dfrac) (j : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) (eb : bool) (lks : gset string) : iProp Σ :=
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf K b (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) C b lks -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        i_dev ip ↦₄{dqd} dev -∗
        i_inum ip ↦₄{dqn} inum -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        inode_meta ip (di_trunc dn) -∗
        inode_map γfs ip bm_empty -∗
        inode_blocks γfs bm_empty (fun _ => replicate BSIZE (bv_0 8)) -∗
        bitmap_res γfs bmapstart cov logstart size (used ∖ bm_blocks bm) -∗
        dinode_at γi inum (di_trunc dn) -∗
        bslots bn 3 -∗
        (* EXACTLY u, AT EXACTLY [Sbf]: iupdate always runs, so the tail
           always spends [it_iu cru] and always logs this inode's block.
           The contract's RANGE is about the bitmap unit, which the tail
           knows nothing about -- the main lemma does the widening, and it
           is also what turns this determinate pair into the contract's
           existential. *)
        log_opS γ u Sbf -∗
        WP (Loop : expr riscv_lang))%I.

End ItruncCont.

(* the register-threading invariants: the five registers the frame saves *)
Definition it_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

(* INSIDE THE INDIRECT ARM s4 holds bp, so [it_thr] -- which does not
   exclude s4 -- is simply false there.  The arm threads this weaker
   invariant instead, and recovers [it_thr] at the [ld s4,0(sp)] at +0x90.
   That is exactly what the conditional save at +0x50 is for. *)
Definition it_thr4 (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
    c <> Rs4 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Lemma it_thr_thr4 (m M : regfile) : it_thr m M -> it_thr4 m M.
Proof. intros H c Hcs N2 N8 N9 N18 N19 _. exact (H c Hcs N2 N8 N9 N18 N19). Qed.

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

(* THE POST'S TWO SET OBLIGATIONS, AT SET VARIABLES.  [wp_itrunc_gen] ends
   both of its exits by handing the contract [Sq ∪ {[IBLOCK inum
   inodestart]}] and proving the growth and the membership.  Both are one
   stdpp lemma, and they are stated HERE rather than closed by [set_solver]
   at the exit: a general-purpose closer at that altitude searches every
   hypothesis of the whole-function proof, and the four calls cost 76-132 s
   EACH -- 407 s, 87 % of the file (optimization.md, "Never let a
   general-purpose closer meet a large context").  Here the context is two
   wide and the cost is nil. *)
Lemma it_sub_union_l (A B S : gset Z) : A ⊆ B -> A ⊆ B ∪ S.
Proof. intros H. exact (union_subseteq_l' _ _ _ H). Qed.

Lemma it_in_union_sing (S : gset Z) (z : Z) : z ∈ S ∪ {[z]}.
Proof. apply elem_of_union_r, elem_of_singleton_2. reflexivity. Qed.

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
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}.

  Local Lemma it_tail `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart bmapstart inodestart size : Z) (nib : nat)
      (dev : mword 32)
      (used : gset Z) (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (u : nat) (Sb0 : gset Z) (cru : bool) (e0 : nat)
      (pidv : mword 32) (dq dqd dqn dqb dqs : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ) (b : bool) (eb : bool) (lks : gset string) :
    (K_itrunc <= K)%nat ->
    log_geom_ok cov logstart ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    bv_unsigned (di_type dn) <> 0 ->
    (* §19.6 Part 1: iupdate's type-stability premise, travelling. *)
    di_type_stable dn dn0 ->
    di_nlink_stable dn dn0 ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    it_sp m M ->
    it_thr m M ->
    M !!! Regidx Rs3 = ip ->
    (* it_tail's only lock-touching callee is the closing iupdate, at "log"
       (3). *)
    locks_below lks "log" ->
    sie_cap_gpr M (K - 6)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) C b lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (IT + 0x38) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    it_frame m -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    i_dev ip ↦₄{dqd} dev -∗
    i_inum ip ↦₄{dqn} inum -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    inode_meta ip dn -∗
    inode_map γfs ip bm_empty -∗
    inode_blocks γfs bm_empty (fun _ => replicate BSIZE (bv_0 8)) -∗
    bitmap_res γfs bmapstart cov logstart size (used ∖ bm_blocks bm) -∗
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn0 -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots bn 3 -∗
    (* the tail flush's absorption credit, travelling to iupdate unchanged --
       a RESOURCE at the walk's own birth epoch (fs-log.md §G.20) *)
    log_credit γ cru Sb0 e0 (IBLOCK inum inodestart) -∗
    log_opSe γ (S u) Sb0 e0 -∗
    it_cont (CID0 := CID0) γ γfs γi bn cov logstart bmapstart inodestart size
            used dev ip inum dn bm (if cru then S u else u)
            (Sb0 ∪ {[IBLOCK inum inodestart]})
            pidv dq dqd dqn dqb dqs j m K C b eb lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hist Hicov Hilog Hnib Hdtnz Hstab Hnlk Hj Hgl Hsp Hthr Hs3 Hlkbelow.
    pose proof HK as HK'. unfold K_itrunc in HK'.
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio #Hlctx #Hprocs Hframe Hppid Hidev Hinum Hsbb Hsbi Hmeta Hmap Hblks Hbmr
              #Hireg Hdn #Hdevi #Hdgeom #Hdlock Hsl #Hcrdu Hop Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
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
    iApply (wp_sw_s_sconf (mword_of_int (IT + 0x38)) Rz Rs3
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
    iApply (wp_cmv_s_sconf (mword_of_int (IT + 0x3c)) Ra0 Rs3
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
    iApply (wp_jal_s_sconf (mword_of_int (IT + 0x3e)) Rra
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
   iDestruct (cpu_own_transport CID0 CID3 0 eb (proc_addr j) C b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID3 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CID3 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID3) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKiu : (K_iupdate <= K - 6)%nat) by (unfold K_iupdate; lia).
    (* iupdate wants two; the third is parked across the call *)
    assert (Hthree : (3 = 2 + 1)%nat) by lia.
    iEval (rewrite Hthree bslots_op) in "Hsl".
    iDestruct "Hsl" as "[Hsl Hslp]".
    assert (Hdirlen : length (bm_dir bm_empty) = NDIRECT)
      by (rewrite /bm_empty; cbn [bm_dir]; apply length_replicate).
    (* THE CREDITED FLUSH.  [wp_iupdate_credgen] is the eb-generic credited
       walk (GR-2b): itrunc is a pure pass-through, so it threads its own
       complements here rather than pinning [eb := true] the way create's
       [wp_iupdate_cred] does. *)
    (* itrunc wants no zero-receipt: the anchor is the unit and the
       witness is dropped (fs-log.md §G.17) *)
    iApply fupd_wp. iMod (log_epoch_lb_0 γ) as "#Hlb0". iModIntro.
    (* THE CREDIT AND THE EPOCH ARE THE CALLER'S (fs-log.md §G.20).  Both
       arrive as premises now -- the credit as a RESOURCE, so that a [crz]
       iput can present a GROUP witness through the whole walk, and the
       birth epoch NAMED, because a credit is only sound against the epoch
       of the op presenting it.  iupdate's own post re-closes the epoch. *)
    iApply (IU.wp_iupdate_credgen γs j γl γu γd γk pd pav pu bn γ γfs γi
              cov logstart inodestart nib dev ip inum (di_trunc dn) dn0
              bm_empty u Sb0 cru e0 0%nat
              pidv dq dqd dqn dqs T1 (K - 6)%nat eb C b
              _ HKiu Hgeom Hist Hicov Hilog Hnib
              (* §19.6 Part 1: [di_trunc] keeps the type, so itrunc's own
                 [Hstab] about [dn] vs [dn0] is exactly what iupdate wants. *)
              Hstab Hnlk
              (di_trunc_addrs dn) Hdirlen
              Hj Hgl HT1a0 Hlkbelow
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hidev Hinum Hmeta Hmap
                    Hsbi Hireg Hdn Hppid Hprocs Hdevi Hdgeom
                    Hdlock Hsl Hlb0 Hcrdu Hop").
    all: try lkbelow.
    iIntros (CID4 Hq4 mI) "%Hcs1 Hcg Hcnt Hextc Hextm Hpc Hppid Hidev Hinum
                           Hmeta Hmap Hsbi Hdn Hsl Hop Hwit".
    (* §16.4: iupdate's payout is conditional on the flushed record's type,
       and [di_trunc] keeps the type -- so this is the allocated branch *)
    iDestruct (ireg_out_alloc_inv γi inum (di_trunc dn) Hdtnz with "Hdn")
      as "Hdn".
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
    iApply (wp_cldsp_s_sconf (mword_of_int (IT + 0x42))
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
    iApply (wp_cldsp_s_sconf (mword_of_int (IT + 0x44))
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
    iApply (wp_cldsp_s_sconf (mword_of_int (IT + 0x46))
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
    iApply (wp_cldsp_s_sconf (mword_of_int (IT + 0x48))
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
    iApply (wp_cldsp_s_sconf (mword_of_int (IT + 0x4a))
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
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (IT + 0x4c))
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
    iApply (wp_cret_s_sconf (mword_of_int (IT + 0x4e)) Rra P6 K b
              ltac:(nz) with "Hcg Hpc Hi4e").
    iIntros (CID11 Hq11) "Hcg Hpc".
    assert (Hretf : ret_pc (P6 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP6ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== hand everything to the caller ===== *)
    iDestruct (cpu_own_transport CID4 CID11 0 eb (proc_addr j) C b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID4 CID11 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID4 CID11 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
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
    iApply ("Hcont" $! P6 with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid Hidev Hinum
                                 Hsbb Hsbi Hmeta Hmap Hblks Hbmr Hdn [Hsl Hslp]
                                 [Hop]").
    { unfold callee_saved. split_and!; assumption. }
    { iEval (rewrite Hthree bslots_op). iSplitL "Hsl"; [iExact "Hsl"|].
      iExact "Hslp". }
    { iExact "Hop". }
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
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}.

  (* what the loop hands on at +0x32, once every direct entry is gone *)
  Definition it_dexit `{GEN : GenId} `{CID0 : CpuId} 
      (γ : log_names) (γfs : fs_names) (bn : bio_names)
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z)
      (dev : mword 32) (ip : mword 64) (bm : blkmap)
      (data : nat -> list (bv 8))
      (pidv : mword 32) (dq dqd dqb : dfrac) (j : nat)
      (crb : bool) (Sb : gset Z) (e0 : nat) (w : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) (eb : bool) (lks : gset string) : iProp Σ :=
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ Mx : regfile,
        ⌜it_sp m Mx⌝ -∗ ⌜it_thr m Mx⌝ -∗ ⌜Mx !!! Regidx Rs3 = ip⌝ -∗
        sie_cap_gpr Mx (K - 6)%nat b (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) C b lks -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (mword_of_int (IT + 0x32) : mword 64) -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        i_dev ip ↦₄{dqd} dev -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        bslots bn 2 -∗
        it_dir_state γ γfs ip bm data cov logstart bmapstart size used bn
                     crb Sb e0 w NDIRECT -∗
        WP (Loop : expr riscv_lang))%I.

  Local Lemma it_dloop `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (jx : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart bmapstart size : Z) (dev : mword 32)
      (used : gset Z) (ip : mword 64) (bm : blkmap)
      (data : nat -> list (bv 8))
      (pidv : mword 32) (dq dqd dqb : dfrac) (crb : bool) (Sb : gset Z) (e0 : nat)
      (w : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) (eb : bool) (fuel : nat) (lks : gset string) :
    (K_itrunc <= K)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    blkmap_wf cov logstart bm ->
    (forall i : nat, (i <= MAXFILE)%nat -> bv_unsigned (bm_slot bm i) <> 0 ->
       bv_unsigned (bm_slot bm i) < size) ->
    (forall i : nat, (i < MAXFILE)%nat -> length (data i) = BSIZE) ->
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
    (* it_dloop's only lock-touching callee is bfree, at "log" (3), on its
       own binder list so the recursive back-edge re-proves it. *)
    locks_below lks "log" ->
    sie_cap_gpr M (K - 6)%nat b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) C b lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗
    pc_is (mword_of_int (IT + 0x20) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    p_pid (proc_addr jx) ↦₄{dq} pidv -∗
    i_dev ip ↦₄{dqd} dev -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots bn 2 -∗
    it_dir_state γ γfs ip bm data cov logstart bmapstart size used bn crb Sb e0 w k -∗
    it_dexit (CID0 := CID0) γ γfs bn cov logstart bmapstart size used dev
             ip bm data pidv dq dqd dqb jx crb Sb e0 w m K C b eb lks -∗
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
      intros CID0 k M Hk Hfuel Hsp Hthr Hs1 Hs2 Hs3 Hlkbelow;
      [ exfalso; unfold NDIRECT in Hk, Hfuel; lia |].
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio #Hlctx #Hprocs Hppid Hidev Hsbb #Hdevi #Hdgeom #Hdlock Hsl Hst Hexit".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
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
    iApply (wp_clw_s_sconf (mword_of_int (IT + 0x20)) Ra1 Rs1
              (mword_of_int 0 : mword 12) M (K - 6)%nat (bm_dir bm !!! k) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi20 Hcell").
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
                            bn crb Sb e0 w (S k))
        with "[Hmap Hblks Hbmr Hpaid]" as "Hst".
      { iApply (it_dir_state_close with "[Hmap] [Hblks] [Hbmr] Hpaid");
          [ rewrite Hsk; iExact "Hmap"
          | rewrite Hsk; iExact "Hblks"
          | rewrite Hfk; iExact "Hbmr" ]. }
      iPoseProof (iti_1a with "Htext") as "Hi1a".
      iPoseProof (iti_1c with "Htext") as "Hi1c".
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (IT + 0x22))
                (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 3)) Ra1
                L0 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HL0a1; exact (bm_eqz_true _ Hzero))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi22").
      iApply bi.later_intro. iIntros (CID2 Hq2) "Hcg Hpc".
      assert (Htgt1a : add_vec (mword_of_int (IT + 0x22) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
                       = mword_of_int (IT + 0x1a)) by pcw.
      iEval (rewrite Htgt1a) in "Hpc".
      (* ===== +0x1a c.addi s1,s1,4 : bump the cursor ===== *)
      assert (Himm4 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))
                       : mword 64) = mword_of_int 4) by pcw.
      iApply (wp_caddi_s_sconf (mword_of_int (IT + 0x1a)) Rs1
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
        iApply (wp_beq_taken_s_sconf (mword_of_int (IT + 0x1c))
                  (mword_of_int 22 : mword 13) Rs2 Rs1 L1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HL1s1 HL1s2 Hlast;
                        apply eq_vec_true_iff; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi1c'").
        iApply bi.later_intro. iIntros (CID4 Hq4) "Hcg Hpc".
        assert (Htgt32 : add_vec (mword_of_int (IT + 0x1c) : mword 64)
                           (sign_extend' 64 (mword_of_int 22 : mword 13))
                         = mword_of_int (IT + 0x32)) by pcw.
        iEval (rewrite Htgt32) in "Hpc".
        rewrite /it_dexit.
        iDestruct (cpu_own_transport CID0 CID4 0 eb (proc_addr jx) C b 
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (trap_csrs_ext_transport CID0 CID4 eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CID0 CID4 eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
        iSpecialize ("Hexit" $! CID4 with "[%]"); [wp_next_chain|].
        rewrite Hlast.
        iApply ("Hexit" $! L1 with "[%] [%] [%] Hcg Hcnt Hextc Hextm Hpc Hppid
                                    Hidev Hsbb Hsl Hst");
          [exact HL1sp | exact HL1thr | exact HL1s3].
      + (* more entries to go: round again *)
        iPoseProof (iti_1c with "Htext") as "Hi1c'".
        assert (Hne : i_addr ip (S k) <> i_addr ip NDIRECT).
        { intros Hq. apply Hmore. apply (i_addr_inj ip); [lia | lia | exact Hq]. }
        iApply (wp_beq_fall_s_sconf (mword_of_int (IT + 0x1c))
                  (mword_of_int 22 : mword 13) Rs2 Rs1 L1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HL1s1 HL1s2; apply eq_vec_false_iff;
                        exact Hne)
                  with "Hcg Hpc Hi1c'").
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
        iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID4)
                     ltac:(wp_next_chain) with "Hexit") as "Hexit".
        iDestruct (cpu_own_transport CID0 CID4 0 eb (proc_addr jx) C b 
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (trap_csrs_ext_transport CID0 CID4 eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CID0 CID4 eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
        iApply (IH CID4 (S k) L1 Hk' Hf' HL1sp HL1thr HL1s1 HL1s2 HL1s3 Hlkbelow
                  with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hprocs Hppid Hidev Hsbb Hdevi Hdgeom Hdlock Hsl
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
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (IT + 0x22))
                (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 3)) Ra1
                L0 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HL0a1; exact (bm_eqz_false _ Hnzero))
                with "Hcg Hpc Hi22").
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
      iApply (wp_lw_s_sconf (mword_of_int (IT + 0x24)) Ra0 Rs3
                (mword_of_int 0 : mword 12) L0 (K - 6)%nat dev b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi24 Hidev").
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
      iApply (wp_jal_s_sconf (mword_of_int (IT + 0x28)) Rra
                (mword_of_int 2096118 : mword 21) L2 (K - 6)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi28").
      iIntros (CID3 Hq3) "Hcg Hpc".
      set (L3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (IT + 0x28) : mword 64) 4)]> L2).
      assert (Htgtbf : add_vec (mword_of_int (IT + 0x28) : mword 64)
                         (sign_extend' 64 (mword_of_int 2096118 : mword 21))
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
      iDestruct (bm_paidS_use with "Hpaid") as (cr u' Sq)
        "(%Hcrin & %Hbud & %Hqsub & Hop & Hback)".
      (* bfree's credit is a RESOURCE now (fs-log.md §G.20); the bitmap
         block is one this op logs itself, so the own-set disjunct is the
         whole conversion and the loop's claim is unchanged *)
      iPoseProof (log_credit_own γ cr Sq e0 bmapstart Hcrin) as "#Hcrbm".
      iDestruct (cpu_own_transport CID0 CID3 0 eb (proc_addr jx) C b 
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID0 CID3 eb (proc_addr jx)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID0 CID3 eb (proc_addr jx)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID3)
                   ltac:(wp_next_chain) with "Hexit") as "Hexit".
      assert (HKbf : (K_bfree <= K - 6)%nat) by (unfold K_bfree; lia).
      iApply (BF.wp_bfree_gen γs jx γl γu γd γk pd pav pu bn γ γfs
                cov logstart bmapstart size dev (used ∖ bm_dir_freed bm k)
                (bm_dir bm !!! k : mword 32) (data k) u' cr Sq e0
                pidv dq dqb L3 (K - 6)%nat eb C b
                _ HKbf Hgeom Hsize Hbm0 Hbmcov Hbmlog
                ltac:(destruct (bv_unsigned_in_range 32 (bm_dir bm !!! k))
                        as [Hlo _]; split; [exact Hlo | exact Hklt])
                Hkcov Hklog
                (Hblen k ltac:(unfold MAXFILE, NDIRECT in *; lia))
                Hj Hgl HL3a0 HL3a1
                Hlkbelow
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hsbb [Hbmr] Hfsb Htok
                      Hppid Hprocs Hdevi Hdgeom Hdlock Hsl Hcrbm Hop").
      all: try lkbelow.
      { iExact "Hbmr". }
      iIntros (CID4 Hq4 mf) "%Hcs Hcg Hcnt Hextc Hextm Hpc Hppid Hsbb Hbmr
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
      iApply (wp_sw_s_sconf (mword_of_int (IT + 0x2c)) Rz Rs1
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
      { rewrite bm_dir_freed_step. exact (freed_pool_grow _ _ _ Hnzero). }
      iEval (rewrite Hfstep) in "Hbmr".
      iDestruct ("Hback" with "[Hop]") as "Hpaid";
        [ rewrite Hbud; iExact "Hop" |].
      iAssert (it_dir_state γ γfs ip bm data cov logstart bmapstart size used
                            bn crb Sb e0 w (S k))
        with "[Hmap Hblks Hbmr Hpaid]" as "Hst".
      { iApply (it_dir_state_close with "Hmap Hblks Hbmr Hpaid"). }
      (* ===== +0x30 c.j : back to the increment ===== *)
      assert (Hp30 : add_vec_int (mword_of_int (IT + 0x2c) : mword 64) 4
                     = mword_of_int (IT + 0x30)) by pcw.
      iEval (rewrite Hp30) in "Hpc".
      iApply (wp_cj_s_sconf (mword_of_int (IT + 0x30))
                (sign_extend' 21 (concat_vec (mword_of_int 2037 : mword 11) ('b"0")))
                mf (K - 6)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi30").
      iIntros (CID6 Hq6). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgt1a' : add_vec (mword_of_int (IT + 0x30) : mword 64)
                          (sign_extend' 64 (sign_extend' 21
                             (concat_vec (mword_of_int 2037 : mword 11) ('b"0"))))
                        = mword_of_int (IT + 0x1a)) by pcw.
      iEval (rewrite Htgt1a') in "Hpc".
      (* ===== +0x1a / +0x1c : the same increment and bounds test ===== *)
      assert (Himm4' : (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))
                        : mword 64) = mword_of_int 4) by pcw.
      iApply (wp_caddi_s_sconf (mword_of_int (IT + 0x1a)) Rs1
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
      + iApply (wp_beq_taken_s_sconf (mword_of_int (IT + 0x1c))
                  (mword_of_int 22 : mword 13) Rs2 Rs1 N1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HN1s1 HN1s2 Hlast;
                        apply eq_vec_true_iff; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi1c").
        iApply bi.later_intro. iIntros (CID8 Hq8) "Hcg Hpc".
        assert (Htgt32' : add_vec (mword_of_int (IT + 0x1c) : mword 64)
                            (sign_extend' 64 (mword_of_int 22 : mword 13))
                          = mword_of_int (IT + 0x32)) by pcw.
        iEval (rewrite Htgt32') in "Hpc".
        rewrite /it_dexit.
        iDestruct (cpu_own_transport CID4 CID8 0 eb (proc_addr jx) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (trap_csrs_ext_transport CID4 CID8 eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CID4 CID8 eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
        iDestruct (wp_next_shift (b := true) (CIDa := CID3) (CIDb := CID8)
                     ltac:(wp_next_chain) with "Hexit") as "Hexit".
        iSpecialize ("Hexit" $! CID8 with "[%]"); [wp_next_chain|].
        rewrite Hlast.
        iApply ("Hexit" $! N1 with "[%] [%] [%] Hcg Hcnt Hextc Hextm Hpc Hppid
                                    Hidev Hsbb Hsl Hst");
          [exact HN1sp | exact HN1thr | exact HN1s3].
      + assert (Hne' : i_addr ip (S k) <> i_addr ip NDIRECT).
        { intros Hq. apply Hmore. apply (i_addr_inj ip); [lia | lia | exact Hq]. }
        iApply (wp_beq_fall_s_sconf (mword_of_int (IT + 0x1c))
                  (mword_of_int 22 : mword 13) Rs2 Rs1 N1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HN1s1 HN1s2;
                        apply eq_vec_false_iff; exact Hne')
                  with "Hcg Hpc Hi1c").
        iIntros (CID8 Hq8) "Hcg Hpc".
        assert (Hp20' : add_vec_int (mword_of_int (IT + 0x1c) : mword 64) 4
                        = mword_of_int (IT + 0x20)) by pcw.
        iEval (rewrite Hp20') in "Hpc".
        assert (Hk'' : (S k < NDIRECT)%nat)
          by (clear - Hk Hmore; unfold NDIRECT in *; lia).
        assert (Hf'' : (NDIRECT - S k <= fuel)%nat)
          by (clear - Hk Hfuel Hmore; unfold NDIRECT in *; lia).
        iDestruct (cpu_own_transport CID4 CID8 0 eb (proc_addr jx) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (trap_csrs_ext_transport CID4 CID8 eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CID4 CID8 eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
        iDestruct (wp_next_shift (b := true) (CIDa := CID3) (CIDb := CID8)
                     ltac:(wp_next_chain) with "Hexit") as "Hexit".
        iApply (IH CID8 (S k) N1 Hk'' Hf'' HN1sp HN1thr HN1s1 HN1s2 HN1s3 Hlkbelow
                  with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hprocs Hppid Hidev Hsbb Hdevi Hdgeom Hdlock Hsl
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
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}.

  Definition it_eexit `{GEN : GenId} `{CID0 : CpuId} 
      (γ : log_names) (γfs : fs_names) (bn : bio_names) (γd : disk_names)
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z)
      (dev : mword 32) (ip : mword 64) (bm : blkmap)
      (data : nat -> list (bv 8)) (kk : nat) (dsk : mword 32)
      (pidv : mword 32) (dq dqd dqb : dfrac) (j : nat)
      (crb : bool) (Sb : gset Z) (e0 : nat) (w : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) (eb : bool) (lks : gset string) : iProp Σ :=
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ Mx : regfile,
        ⌜it_sp m Mx⌝ -∗ ⌜it_thr4 m Mx⌝ -∗ ⌜Mx !!! Regidx Rs3 = ip⌝ -∗
        ⌜Mx !!! Regidx Rs4 = bnode kk⌝ -∗
        sie_cap_gpr Mx (K - 6)%nat b (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) C b lks -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (mword_of_int (IT + 0x7a) : mword 64) -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        i_dev ip ↦₄{dqd} dev -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        bslots bn 2 -∗
        buf_own (bpa kk) (bm_ind bm) dsk (ind_bytes (bm_ent bm)) -∗
        it_ent_state γ γfs bm data cov logstart bmapstart size used
                     crb Sb e0 w NINDIRECT -∗
        WP (Loop : expr riscv_lang))%I.

  Local Lemma it_eloop `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (jx : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart bmapstart size : Z) (dev : mword 32)
      (used : gset Z) (ip : mword 64) (bm : blkmap)
      (data : nat -> list (bv 8)) (kk : nat) (dsk : mword 32)
      (pidv : mword 32) (dq dqd dqb : dfrac) (crb : bool) (Sb : gset Z) (e0 : nat)
      (w : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) (eb : bool) (fuel : nat) (lks : gset string) :
    (K_itrunc <= K)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    blkmap_wf cov logstart bm ->
    (forall i : nat, (i <= MAXFILE)%nat -> bv_unsigned (bm_slot bm i) <> 0 ->
       bv_unsigned (bm_slot bm i) < size) ->
    (forall i : nat, (i < MAXFILE)%nat -> length (data i) = BSIZE) ->
    (kk < NBUF)%nat ->
    (jx < NPROC)%nat ->
    γs !! jx = Some γl ->
    forall (q : nat) (M : regfile),
    (q < NINDIRECT)%nat ->
    (NINDIRECT - q <= fuel)%nat ->
    it_sp m M ->
    it_thr4 m M ->
    M !!! Regidx Rs1 = pa_add (b_data (bpa kk)) (4 * q)%nat ->
    M !!! Regidx Rs2 = pa_add (b_data (bpa kk)) (4 * NINDIRECT)%nat ->
    M !!! Regidx Rs3 = ip ->
    M !!! Regidx Rs4 = bnode kk ->
    (* it_eloop's only lock-touching callee is bfree, at "log" (3), on its
       own binder list so the recursive back-edge re-proves it. *)
    locks_below lks "log" ->
    sie_cap_gpr M (K - 6)%nat b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) C b lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗
    pc_is (mword_of_int (IT + 0x6c) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    p_pid (proc_addr jx) ↦₄{dq} pidv -∗
    i_dev ip ↦₄{dqd} dev -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots bn 2 -∗
    buf_own (bpa kk) (bm_ind bm) dsk (ind_bytes (bm_ent bm)) -∗
    it_ent_state γ γfs bm data cov logstart bmapstart size used crb Sb e0 w q -∗
    it_eexit (CID0 := CID0) γ γfs bn γd cov logstart bmapstart size used dev
             ip bm data kk dsk pidv dq dqd dqb jx crb Sb e0 w m K C b eb lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hsize Hbm0 Hbmcov Hbmlog Hwf Hrange Hblen Hkk Hj Hgl.
    revert CID0.
    induction fuel as [|fuel IH];
      intros CID0 q M Hq Hfuel Hsp Hthr Hs1 Hs2 Hs3 Hs4 Hlkbelow;
      [ exfalso; unfold NINDIRECT in Hq, Hfuel; lia |].
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio #Hlctx #Hprocs Hppid Hidev Hsbb #Hdevi #Hdgeom #Hdlock Hsl Hbuf Hst Hexit".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
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
    iApply (wp_clw_s_sconf (mword_of_int (IT + 0x6c)) Ra1 Rs1
              (mword_of_int 0 : mword 12) M (K - 6)%nat (bm_ent bm !!! q) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi6c Hcell").
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
    assert (HE0thr : it_thr4 m E0).
    { intros c Hcs N2 N8 N9 N18 N19 N20.
      rewrite /E0 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18 N19 N20). }
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
      iAssert (it_ent_state γ γfs bm data cov logstart bmapstart size used crb Sb e0 w (S q))
        with "[Hres Hbmr Hpaid]" as "Hst".
      { iApply (it_ent_state_close with "Hres [Hbmr] Hpaid").
        rewrite Hfk. iExact "Hbmr". }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (IT + 0x6e))
                (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 3)) Ra1
                E0 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HE0a1; exact (bm_eqz_true _ Hzero))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi6e").
      iApply bi.later_intro. iIntros (CID2 Hq2) "Hcg Hpc".
      assert (Htgt66 : add_vec (mword_of_int (IT + 0x6e) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
                       = mword_of_int (IT + 0x66)) by pcw.
      iEval (rewrite Htgt66) in "Hpc".
      (* ===== +0x66 c.addi s1,s1,4 ; +0x68 beq s1,s2 ===== *)
      assert (Himm4 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))
                       : mword 64) = mword_of_int 4) by pcw.
      iApply (wp_caddi_s_sconf (mword_of_int (IT + 0x66)) Rs1
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
      assert (HE1thr : it_thr4 m E1).
      { intros c Hcs2 N2 N8 N9 N18 N19 N20.
        rewrite /E1 upd_ne; [| regne]. exact (HE0thr c Hcs2 N2 N8 N9 N18 N19 N20). }
      assert (Hp68 : add_vec_int (mword_of_int (IT + 0x66) : mword 64) 2
                     = mword_of_int (IT + 0x68)) by pcw.
      iEval (rewrite Hp68) in "Hpc".
      destruct (decide (S q = NINDIRECT)) as [Hlast|Hmore].
      + iApply (wp_beq_taken_s_sconf (mword_of_int (IT + 0x68))
                  (mword_of_int 18 : mword 13) Rs2 Rs1 E1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HE1s1 HE1s2 Hlast;
                        apply eq_vec_true_iff; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi68").
        iApply bi.later_intro. iIntros (CIDb Hqb) "Hcg Hpc".
        assert (Htgt7a : add_vec (mword_of_int (IT + 0x68) : mword 64)
                           (sign_extend' 64 (mword_of_int 18 : mword 13))
                         = mword_of_int (IT + 0x7a)) by pcw.
        iEval (rewrite Htgt7a) in "Hpc".
        rewrite /it_eexit.
        iDestruct (cpu_own_transport CID0 CIDb 0 eb (proc_addr jx) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (trap_csrs_ext_transport CID0 CIDb eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CID0 CIDb eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
        iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CIDb)
                     ltac:(wp_next_chain) with "Hexit") as "Hexit".
        iSpecialize ("Hexit" $! CIDb with "[%]"); [wp_next_chain|].
        rewrite Hlast.
        iApply ("Hexit" $! E1 with "[%] [%] [%] [%] Hcg Hcnt Hextc Hextm Hpc
                                    Hppid Hidev Hsbb Hsl Hbuf Hst");
          [exact HE1sp | exact HE1thr | exact HE1s3 | exact HE1s4].
      + assert (Hne : pa_add (b_data (bpa kk)) (4 * S q)%nat
                      <> pa_add (b_data (bpa kk)) (4 * NINDIRECT)%nat).
        { intros Hz. apply Hmore.
          apply (b_data_off_inj (bpa kk)); [lia | lia | exact Hz]. }
        iApply (wp_beq_fall_s_sconf (mword_of_int (IT + 0x68))
                  (mword_of_int 18 : mword 13) Rs2 Rs1 E1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HE1s1 HE1s2;
                        apply eq_vec_false_iff; exact Hne)
                  with "Hcg Hpc Hi68").
        iIntros (CIDb Hqb) "Hcg Hpc".
        assert (Hp6c : add_vec_int (mword_of_int (IT + 0x68) : mword 64) 4
                       = mword_of_int (IT + 0x6c)) by pcw.
        iEval (rewrite Hp6c) in "Hpc".
        assert (Hq'' : (S q < NINDIRECT)%nat)
          by (clear - Hq Hmore; unfold NINDIRECT in *; lia).
        assert (Hf'' : (NINDIRECT - S q <= fuel)%nat)
          by (clear - Hq Hfuel Hmore; unfold NINDIRECT in *; lia).
        iDestruct (cpu_own_transport CID0 CIDb 0 eb (proc_addr jx) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (trap_csrs_ext_transport CID0 CIDb eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CID0 CIDb eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
        iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CIDb)
                     ltac:(wp_next_chain) with "Hexit") as "Hexit".
        iApply (IH CIDb (S q) E1 Hq'' Hf'' HE1sp HE1thr HE1s1 HE1s2 HE1s3 HE1s4 Hlkbelow
                  with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hprocs Hppid Hidev Hsbb Hdevi Hdgeom Hdlock Hsl
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
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (IT + 0x6e))
                (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 3)) Ra1
                E0 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HE0a1; exact (bm_eqz_false _ Hnzero))
                with "Hcg Hpc Hi6e").
      iIntros (CIDx Hqx) "Hcg Hpc".
      assert (Hp70 : add_vec_int (mword_of_int (IT + 0x6e) : mword 64) 2
                     = mword_of_int (IT + 0x70)) by pcw.
      iEval (rewrite Hp70) in "Hpc".
      (* ===== +0x70 lw a0,0(s3) ===== *)
      assert (Hdva : add_vec (rget E0 Rs3)
                       (sign_extend' 64 (mword_of_int 0 : mword 12)) = i_dev ip).
      { rgne. rewrite HE0s3. reflexivity. }
      iEval (rewrite -Hdva) in "Hidev".
      iApply (wp_lw_s_sconf (mword_of_int (IT + 0x70)) Ra0 Rs3
                (mword_of_int 0 : mword 12) E0 (K - 6)%nat dev b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi70 Hidev").
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
      assert (HE2thr : it_thr4 m E2).
      { intros c Hcs2 N2 N8 N9 N18 N19 N20.
        rewrite /E2 upd_ne; [| regne]. exact (HE0thr c Hcs2 N2 N8 N9 N18 N19 N20). }
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
      iApply (wp_jal_s_sconf (mword_of_int (IT + 0x74)) Rra
                (mword_of_int 2096042 : mword 21) E2 (K - 6)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi74").
      iIntros (CIDz Hqz) "Hcg Hpc".
      set (E3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (IT + 0x74) : mword 64) 4)]> E2).
      assert (Htgtbf : add_vec (mword_of_int (IT + 0x74) : mword 64)
                         (sign_extend' 64 (mword_of_int 2096042 : mword 21))
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
      assert (HE3thr : it_thr4 m E3).
      { intros c Hcs2 N2 N8 N9 N18 N19 N20.
        rewrite /E3 upd_ne; [| regne]. exact (HE2thr c Hcs2 N2 N8 N9 N18 N19 N20). }
      iDestruct (bm_paidS_use with "Hpaid") as (cr u' Sq)
        "(%Hcrin & %Hbud & %Hqsub & Hop & Hback)".
      (* bfree's credit is a RESOURCE now (fs-log.md §G.20); the bitmap
         block is one this op logs itself, so the own-set disjunct is the
         whole conversion and the loop's claim is unchanged *)
      iPoseProof (log_credit_own γ cr Sq e0 bmapstart Hcrin) as "#Hcrbm".
      iDestruct (cpu_own_transport CID0 CIDz 0 eb (proc_addr jx) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID0 CIDz eb (proc_addr jx)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID0 CIDz eb (proc_addr jx)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CIDz)
                   ltac:(wp_next_chain) with "Hexit") as "Hexit".
      assert (HKbf : (K_bfree <= K - 6)%nat) by (unfold K_bfree; lia).
      iApply (BF.wp_bfree_gen γs jx γl γu γd γk pd pav pu bn γ γfs
                cov logstart bmapstart size dev
                (used ∖ (bm_dir_freed bm NDIRECT ∪ bm_ent_freed bm q))
                (bm_ent bm !!! q : mword 32) (data (NDIRECT + q)%nat) u' cr Sq e0
                pidv dq dqb E3 (K - 6)%nat eb C b
                _ HKbf Hgeom Hsize Hbm0 Hbmcov Hbmlog
                ltac:(destruct (bv_unsigned_in_range 32 (bm_ent bm !!! q))
                        as [Hlo _]; split; [exact Hlo | exact Hqlt])
                Hqcov Hqlog (Hblen (NDIRECT + q)%nat
                                    ltac:(unfold MAXFILE, NDIRECT, NINDIRECT in *;
                                          lia))
                Hj Hgl HE3a0 HE3a1
                Hlkbelow
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hsbb Hbmr Hfsb Htok
                      Hppid Hprocs Hdevi Hdgeom Hdlock Hsl Hcrbm Hop").
      all: try lkbelow.
      iIntros (CIDf Hqf mfE) "%Hcs Hcg Hcnt Hextc Hextm Hpc Hppid Hsbb Hbmr
                              Hsl Hop".
      assert (Hpc78 : ret_pc (E3 !!! Regidx Rra : mword 64)
                      = mword_of_int (IT + 0x78)) by (rewrite HE3ra; pcw).
      iEval (rewrite Hpc78) in "Hpc".
      pose proof Hcs as Hcs'.
      assert (HFsp : it_sp m mfE).
      { rewrite /it_sp
          (callee_saved_lookup Hcs' csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HE3sp. }
      assert (HFthr : it_thr4 m mfE).
      { intros c Hcs2 N2 N8 N9 N18 N19 N20.
        rewrite (callee_saved_lookup Hcs' c Hcs2).
        exact (HE3thr c Hcs2 N2 N8 N9 N18 N19 N20). }
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
      { rewrite bm_ent_freed_step. exact (freed_pool_grow2 _ _ _ _ Hnzero). }
      iEval (rewrite Hfstep) in "Hbmr".
      iDestruct ("Hback" with "[Hop]") as "Hpaid";
        [ rewrite Hbud; iExact "Hop" |].
      iAssert (it_ent_state γ γfs bm data cov logstart bmapstart size used crb Sb e0 w (S q))
        with "[Hres Hbmr Hpaid]" as "Hst".
      { iApply (it_ent_state_close with "Hres Hbmr Hpaid"). }
      (* ===== +0x78 c.j : back to the increment ===== *)
      iApply (wp_cj_s_sconf (mword_of_int (IT + 0x78))
                (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")))
                mfE (K - 6)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi78").
      iIntros (CIDw Hqw). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgt66f : add_vec (mword_of_int (IT + 0x78) : mword 64)
                          (sign_extend' 64 (sign_extend' 21
                             (concat_vec (mword_of_int 2039 : mword 11) ('b"0"))))
                        = mword_of_int (IT + 0x66)) by pcw.
      iEval (rewrite Htgt66f) in "Hpc".
      (* ===== +0x66 c.addi s1,s1,4 ; +0x68 beq s1,s2 ===== *)
      assert (Himm4f : (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))
                       : mword 64) = mword_of_int 4) by pcw.
      iApply (wp_caddi_s_sconf (mword_of_int (IT + 0x66)) Rs1
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
      assert (HF1thr : it_thr4 m F1).
      { intros c Hcs2 N2 N8 N9 N18 N19 N20.
        rewrite /F1 upd_ne; [| regne]. exact (HFthr c Hcs2 N2 N8 N9 N18 N19 N20). }
      assert (Hp68f : add_vec_int (mword_of_int (IT + 0x66) : mword 64) 2
                     = mword_of_int (IT + 0x68)) by pcw.
      iEval (rewrite Hp68f) in "Hpc".
      destruct (decide (S q = NINDIRECT)) as [Hlastf|Hmoref].
      + iApply (wp_beq_taken_s_sconf (mword_of_int (IT + 0x68))
                  (mword_of_int 18 : mword 13) Rs2 Rs1 F1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HF1s1 HF1s2 Hlastf;
                        apply eq_vec_true_iff; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi68").
        iApply bi.later_intro. iIntros (CIDr Hqr) "Hcg Hpc".
        assert (Htgt7af : add_vec (mword_of_int (IT + 0x68) : mword 64)
                           (sign_extend' 64 (mword_of_int 18 : mword 13))
                         = mword_of_int (IT + 0x7a)) by pcw.
        iEval (rewrite Htgt7af) in "Hpc".
        rewrite /it_eexit.
        iDestruct (cpu_own_transport CIDf CIDr 0 eb (proc_addr jx) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (trap_csrs_ext_transport CIDf CIDr eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CIDf CIDr eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
        iDestruct (wp_next_shift (b := true) (CIDa := CIDz) (CIDb := CIDr)
                     ltac:(wp_next_chain) with "Hexit") as "Hexit".
        iSpecialize ("Hexit" $! CIDr with "[%]"); [wp_next_chain|].
        rewrite Hlastf.
        iApply ("Hexit" $! F1 with "[%] [%] [%] [%] Hcg Hcnt Hextc Hextm Hpc
                                    Hppid Hidev Hsbb Hsl Hbuf Hst");
          [exact HF1sp | exact HF1thr | exact HF1s3 | exact HF1s4].
      + assert (Hnef : pa_add (b_data (bpa kk)) (4 * S q)%nat
                      <> pa_add (b_data (bpa kk)) (4 * NINDIRECT)%nat).
        { intros Hz. apply Hmoref.
          apply (b_data_off_inj (bpa kk)); [lia | lia | exact Hz]. }
        iApply (wp_beq_fall_s_sconf (mword_of_int (IT + 0x68))
                  (mword_of_int 18 : mword 13) Rs2 Rs1 F1 (K - 6)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HF1s1 HF1s2;
                        apply eq_vec_false_iff; exact Hnef)
                  with "Hcg Hpc Hi68").
        iIntros (CIDr Hqr) "Hcg Hpc".
        assert (Hp6cf : add_vec_int (mword_of_int (IT + 0x68) : mword 64) 4
                       = mword_of_int (IT + 0x6c)) by pcw.
        iEval (rewrite Hp6cf) in "Hpc".
        assert (Hqf'' : (S q < NINDIRECT)%nat)
          by (clear - Hq Hmoref; unfold NINDIRECT in *; lia).
        assert (Hff'' : (NINDIRECT - S q <= fuel)%nat)
          by (clear - Hq Hfuel Hmoref; unfold NINDIRECT in *; lia).
        iDestruct (cpu_own_transport CIDf CIDr 0 eb (proc_addr jx) C b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (trap_csrs_ext_transport CIDf CIDr eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CIDf CIDr eb (proc_addr jx)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
        iDestruct (wp_next_shift (b := true) (CIDa := CIDz) (CIDb := CIDr)
                     ltac:(wp_next_chain) with "Hexit") as "Hexit".
        iApply (IH CIDr (S q) F1 Hqf'' Hff'' HF1sp HF1thr HF1s1 HF1s2 HF1s3 HF1s4 Hlkbelow
                  with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hprocs Hppid Hidev Hsbb Hdevi Hdgeom Hdlock Hsl
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
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}.

  (* what the arm hands to the tail: the inode names nothing at all *)
  Definition it_armexit `{GEN : GenId} `{CID0 : CpuId}
      (γ : log_names) (γfs : fs_names) (bn : bio_names)
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z)
      (dev : mword 32) (ip : mword 64) (bm : blkmap)
      (pidv : mword 32) (dq dqd dqb : dfrac) (j : nat)
      (crb : bool) (Sb : gset Z) (e0 : nat) (w : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) (eb : bool) (lks : gset string) : iProp Σ :=
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ Mx : regfile,
        ⌜it_sp m Mx⌝ -∗ ⌜it_thr m Mx⌝ -∗ ⌜Mx !!! Regidx Rs3 = ip⌝ -∗
        sie_cap_gpr Mx (K - 6)%nat b (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) C b lks -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (mword_of_int (IT + 0x38) : mword 64) -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        i_dev ip ↦₄{dqd} dev -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈ v) -∗
        inode_map γfs ip bm_empty -∗
        inode_blocks γfs bm_empty (fun _ => replicate BSIZE (bv_0 8)) -∗
        bitmap_res γfs bmapstart cov logstart size (used ∖ bm_blocks bm) -∗
        bslots bn 3 -∗
        bm_paidS γ bmapstart crb w Sb e0 -∗
        WP (Loop : expr riscv_lang))%I.

  Local Lemma it_iarm `{GEN : GenId} `{CID0 : CpuId}       (γs : list gname) (jx : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart bmapstart size : Z) (dev : mword 32)
      (used : gset Z) (ip : mword 64) (bm : blkmap)
      (data : nat -> list (bv 8))
      (pidv : mword 32) (dq dqd dqb : dfrac) (crb : bool) (Sb : gset Z) (e0 : nat)
      (w : nat)
      (m M : regfile) (K : nat) (C : iProp Σ) (b : bool) (eb : bool) (lks : gset string) :
    (K_itrunc <= K)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart -> bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    blkmap_wf cov logstart bm ->
    (forall i : nat, (i <= MAXFILE)%nat -> bv_unsigned (bm_slot bm i) <> 0 ->
       bv_unsigned (bm_slot bm i) < size) ->
    (forall i : nat, (i < MAXFILE)%nat -> length (data i) = BSIZE) ->
    (* the arm is entered only when the indirect block exists *)
    bv_unsigned (bm_ind bm) <> 0 ->
    (jx < NPROC)%nat ->
    γs !! jx = Some γl ->
    it_sp m M ->
    it_thr m M ->
    M !!! Regidx Rs3 = ip ->
    (* a1 STILL HOLDS ip->addrs[NDIRECT], loaded at +0x32 BEFORE the branch
       that got us here.  The arm never reloads it for the bread -- it only
       re-reads the cell much later, at +0x80, for the block's own free. *)
    M !!! Regidx Ra1 = sign_extend' 64 (bm_ind bm : mword 32) ->
    (* it_iarm's cone: bread/brelse ("bcache", 4) for the indirect block,
       it_eloop and the block's own bfree ("log", 3) -- "log" is lowest. *)
    locks_below lks "log" ->
    sie_cap_gpr M (K - 6)%nat b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) C b lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗
    pc_is (mword_of_int (IT + 0x50) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    p_pid (proc_addr jx) ↦₄{dq} pidv -∗
    i_dev ip ↦₄{dqd} dev -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    (* the sixth frame slot -- this arm is the only writer *)
    (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈ v) -∗
    bslots bn 3 -∗
    inode_map γfs ip (bm_dir_zeroed bm NDIRECT) -∗
    it_ent_res γfs bm data 0 -∗
    bitmap_res γfs bmapstart cov logstart size (used ∖ bm_dir_freed bm NDIRECT) -∗
    bm_paidS γ bmapstart crb w Sb e0 -∗
    it_armexit (CID0 := CID0) γ γfs bn cov logstart bmapstart size used dev
               ip bm pidv dq dqd dqb jx crb Sb e0 w m K C b eb lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hsize Hbm0 Hbmcov Hbmlog Hwf Hrange Hblen Hindnz Hj Hgl
           Hsp Hthr Hs3 Ha1 Hlkbelow.
    pose proof HK as HK'. unfold K_itrunc in HK'.
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio #Hlctx #Hprocs Hppid Hidev Hsbb #Hdevi #Hdgeom #Hdlock Hslot6 Hsl Hmap
              Hres Hbmr Hpaid Hexit".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    iPoseProof (iti_50 with "Htext") as "Hi50".
    iPoseProof (iti_52 with "Htext") as "Hi52".
    iPoseProof (iti_56 with "Htext") as "Hi56".
    iPoseProof (iti_5a with "Htext") as "Hi5a".
    iPoseProof (iti_5c with "Htext") as "Hi5c".
    iPoseProof (iti_60 with "Htext") as "Hi60".
    iPoseProof (iti_64 with "Htext") as "Hi64".
    pose proof (blkmap_wf_dir_len _ _ _ Hwf) as Hdirlen.
    pose proof (blkmap_wf_ent_len _ _ _ Hwf) as Hentlen.
    assert (Hzlen : length (bm_dir (bm_dir_zeroed bm NDIRECT)) = NDIRECT)
      by (rewrite bm_dir_zeroed_len; [exact Hdirlen | lia]).
    (* the indirect block's own content half and token, out of the map *)
    iDestruct (inode_map_ind_acc γfs ip (bm_dir_zeroed bm NDIRECT) Hzlen
                 with "Hmap") as "(Hindcell & Hindres & Hmapback)".
    assert (Hindz : bm_ind (bm_dir_zeroed bm NDIRECT) = bm_ind bm)
      by (rewrite /bm_dir_zeroed; reflexivity).
    assert (Hentz : bm_ent (bm_dir_zeroed bm NDIRECT) = bm_ent bm)
      by (rewrite /bm_dir_zeroed; reflexivity).
    iDestruct (ind_res_nz γfs (bm_dir_zeroed bm NDIRECT)
                 ltac:(rewrite Hindz; exact Hindnz) with "Hindres")
      as "[Hindblk Hindtok]".
    iEval (rewrite Hindz Hentz) in "Hindblk".
    iEval (rewrite Hindz) in "Hindtok".
    iEval (rewrite Hindz) in "Hindcell".
    (* ===== +0x50 sd s4,0(sp) : the ONLY write to the sixth slot ===== *)
    iDestruct "Hslot6" as (v6) "Hslot6".
    assert (Hs6a : add_vec (M !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hs6a) in "Hslot6".
    iApply (wp_csdsp_s_sconf (mword_of_int (IT + 0x50))
              (mword_of_int 0 : mword 6) Rs4 M (K - 6)%nat v6 b
              with "Hcg Hpc Hi50 Hslot6").
    iIntros (CID1 Hq1) "Hcg Hpc Hslot6".
    iEval (rewrite Hs6a) in "Hslot6".
    (* what got stored is the CALLER's s4: it_thr still held on entry, and
       s4 is not one of the five the frame excludes *)
    assert (HMs4 : (M !!! Regidx Rs4 : mword 64)
                   = (m !!! Regidx Rs4 : mword 64))
      by (apply Hthr; first [vm_compute; reflexivity | nz]).
    iEval (rgne; rewrite HMs4) in "Hslot6".
    assert (Hp52 : add_vec_int (mword_of_int (IT + 0x50) : mword 64) 2
                   = mword_of_int (IT + 0x52)) by pcw.
    iEval (rewrite Hp52) in "Hpc".
    (* ===== +0x52 lw a0,0(s3) : a0 := ip->dev ===== *)
    assert (Hdva : add_vec (rget M Rs3)
                     (sign_extend' 64 (mword_of_int 0 : mword 12)) = i_dev ip).
    { rgne. rewrite Hs3. reflexivity. }
    iEval (rewrite -Hdva) in "Hidev".
    iApply (wp_lw_s_sconf (mword_of_int (IT + 0x52)) Ra0 Rs3
              (mword_of_int 0 : mword 12) M (K - 6)%nat dev b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi52 Hidev").
    iIntros (CID2 Hq2) "Hcg Hpc Hidev".
    iEval (rewrite Hdva) in "Hidev".
    set (A0 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> M).
    assert (HA0a0 : A0 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /A0; apply upd_eq).
    assert (HA0a1 : A0 !!! Regidx Ra1
                    = sign_extend' 64 (bm_ind bm : mword 32))
      by (rewrite /A0 upd_ne; [exact Ha1 | nz]).
    assert (HA0s3 : A0 !!! Regidx Rs3 = ip)
      by (rewrite /A0 upd_ne; [exact Hs3 | nz]).
    assert (HA0sp : it_sp m A0)
      by (rewrite /it_sp /A0 upd_ne; [exact Hsp | nz]).
    assert (HA0thr : it_thr m A0).
    { intros c Hcs2 N2 N8 N9 N18 N19.
      rewrite /A0 upd_ne; [| regne]. exact (Hthr c Hcs2 N2 N8 N9 N18 N19). }
    assert (Hp56 : add_vec_int (mword_of_int (IT + 0x52) : mword 64) 4
                   = mword_of_int (IT + 0x56)) by pcw.
    iEval (rewrite Hp56) in "Hpc".
    (* the indirect block is a covered home block, and small enough for
       bread's arithmetic -- both out of blkmap_wf at slot MAXFILE *)
    pose proof Hwf as Hwf2. destruct Hwf2 as (Hd & He & Hni & Hcv & Hinj).
    assert (Hstop : bm_slot bm MAXFILE = bm_ind bm) by apply bm_slot_top.
    destruct (Hcv MAXFILE ltac:(lia) ltac:(rewrite Hstop; exact Hindnz))
      as [Hicov Hilog].
    rewrite Hstop in Hicov, Hilog.
    destruct Hgeom as [Hcovok Hlogsub].
    destruct (Hcovok _ Hicov) as [Hipos Hilt].
    (* ===== +0x56 jal bread ===== *)
    (* one for the bread that stays checked out across the loop, two for
       the bfree calls inside it *)
    assert (Hthree : (3 = 1 + 2)%nat) by lia.
    iEval (rewrite Hthree bslots_op) in "Hsl".
    iDestruct "Hsl" as "[Hsl1 Hsl]".
    iApply (wp_jal_s_sconf (mword_of_int (IT + 0x56)) Rra
              (mword_of_int 2095140 : mword 21) A0 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi56").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (A1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (IT + 0x56) : mword 64) 4)]> A0).
    assert (Htgtbr : add_vec (mword_of_int (IT + 0x56) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095140 : mword 21))
                     = mword_of_int KernelSyms.bread) by pcw.
    iEval (rewrite Htgtbr) in "Hpc".
    assert (HA1a0 : A1 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /A1 upd_ne; [exact HA0a0 | nz]).
    assert (HA1a1 : A1 !!! Regidx Ra1
                    = sign_extend' 64 (bm_ind bm : mword 32))
      by (rewrite /A1 upd_ne; [exact HA0a1 | nz]).
    assert (HA1ra : A1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (IT + 0x56) : mword 64) 4)
      by (rewrite /A1; apply upd_eq).
    assert (HA1s3 : A1 !!! Regidx Rs3 = ip)
      by (rewrite /A1 upd_ne; [exact HA0s3 | nz]).
    assert (HA1sp : it_sp m A1)
      by (rewrite /it_sp /A1 upd_ne; [exact HA0sp | nz]).
    assert (HA1thr : it_thr m A1).
    { intros c Hcs2 N2 N8 N9 N18 N19.
      rewrite /A1 upd_ne; [| regne]. exact (HA0thr c Hcs2 N2 N8 N9 N18 N19). }
    assert (HKbr : (K_bread <= K - 6)%nat) by (unfold K_bread; lia).
    (* bread states its two block-number premises on [uint]; blkmap_wf gives
       them on [bv_unsigned].  bb_uint32 is the bridge at width 32. *)
    assert (Huc : uint (bm_ind bm : mword 32) = bv_unsigned (bm_ind bm))
      by apply bb_uint32.
    assert (Hicov32 : uint (bm_ind bm : mword 32)
                      ∈ bv_cov (fs_view γfs γd dev cov))
      by (rewrite Huc; exact Hicov).
    iDestruct (cpu_own_transport CID0 CID3 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID3 eb (proc_addr jx)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CID3 eb (proc_addr jx)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID3)
                 ltac:(wp_next_chain) with "Hexit") as "Hexit".
    iApply (BR.wp_bread_sconf γs jx γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev (bm_ind bm : mword 32) dq
              A1 (K - 6)%nat eb C b lks
              HKbr
              ltac:(rewrite Huc;
                    change (2 ^ 31)%Z with 2147483648%Z in Hilt; exact Hilt)
              eq_refl Hicov32 eq_refl Hj Hgl
              HA1a0 HA1a1
              (* bread's bound is "bcache"(4); it_iarm's own is "log"(3),
                 and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hppid Hprocs Hdevi Hdgeom Hdlock Hsl1").
    all: try lkbelow.
    iIntros (CID4 Hq4 mB kk bs0 bsd0 d0) "%Hfacts Hcg Hcnt Hextc Hextm Hpc
                                          Hppid Hheld".
    destruct Hfacts as [Hcs1 HmBa0].
    assert (Hpc5a : ret_pc (A1 !!! Regidx Rra : mword 64)
                    = mword_of_int (IT + 0x5a)) by (rewrite HA1ra; pcw).
    iEval (rewrite Hpc5a) in "Hpc".
    iDestruct (bio_locked_kbound with "Hheld") as "[%Hkk Hheld]".
    (* the handle's payload IS the caller's logged content.  [bm_held_content]
       states the block number with [uint]; ours is [bv_unsigned]. *)
    iEval (rewrite -Huc) in "Hindblk".
    iDestruct (bm_held_content bn γfs γd dev cov kk pidv dev
                 (bm_ind bm : mword 32) bs0 _ bsd0
                 (ind_bytes (bm_ent bm)) d0 with "Hindblk Hheld") as %Hbsl.
    iEval (rewrite Huc) in "Hindblk".
    (* ===== +0x5a mv s4,a0 : s4 := bp ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (IT + 0x5a)) Rs4 Ra0
              mB (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5a").
    iIntros (CID5 Hq5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A2 := <[Regidx Rs4 := regval_into_reg
                  (add_vec zero_reg (mB !!! Regidx Ra0 : mword 64))]> mB).
    change (<[Regidx Rs4 := regval_into_reg (add_vec zero_reg (rget mB Ra0))]> mB)
      with A2.
    assert (Hzl : forall x : mword 64, add_vec zero_reg x = x).
    { intros x. apply bv_eq. rewrite add_vec64_unsigned.
      assert (Hz : bv_unsigned (zero_reg : mword 64) = 0)
        by (vm_compute; reflexivity).
      rewrite Hz Z.add_0_l. apply bv_wrap_small, bv_unsigned_in_range. }
    assert (HA2s4 : A2 !!! Regidx Rs4 = bnode kk)
      by (rewrite /A2 upd_eq Hzl; exact HmBa0).
    assert (HA2a0 : A2 !!! Regidx Ra0 = bnode kk)
      by (rewrite /A2 upd_ne; [exact HmBa0 | nz]).
    assert (Hp5c : add_vec_int (mword_of_int (IT + 0x5a) : mword 64) 2
                   = mword_of_int (IT + 0x5c)) by pcw.
    iEval (rewrite Hp5c) in "Hpc".
    (* ===== +0x5c addi s1,a0,88 : s1 := bp->data ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (IT + 0x5c)) Rs1 Ra0
              (mword_of_int 88 : mword 12) A2 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5c").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (A3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (rget A2 Ra0)
                     (sign_extend' 64 (mword_of_int 88 : mword 12)))]> A2).
    assert (Hpa0 : forall x : mword 64, pa_add x 0%nat = x).
    { intros x. rewrite /pa_add /add_vec_int. apply bv_eq.
      rewrite add_vec64_unsigned.
      assert (Hz : bv_unsigned (mword_of_int (Z.of_nat 0) : mword 64) = 0)
        by (vm_compute; reflexivity).
      rewrite Hz Z.add_0_r. apply bvw64_small, bv_unsigned_in_range. }
    assert (Hs88 : (sign_extend' 64 (mword_of_int 88 : mword 12) : mword 64)
                   = mword_of_int 88) by pcw.
    assert (HA3s1 : A3 !!! Regidx Rs1
                    = pa_add (b_data (bnode kk)) (4 * 0)%nat).
    { rewrite /A3 upd_eq. rgne. rewrite HA2a0 Nat.mul_0_r Hpa0 Hs88.
      rewrite /b_data /pa_add /add_vec_int. f_equal. }
    assert (HA3a0 : A3 !!! Regidx Ra0 = bnode kk)
      by (rewrite /A3 upd_ne; [exact HA2a0 | nz]).
    assert (HA3s4 : A3 !!! Regidx Rs4 = bnode kk)
      by (rewrite /A3 upd_ne; [exact HA2s4 | nz]).
    assert (Hp60 : add_vec_int (mword_of_int (IT + 0x5c) : mword 64) 4
                   = mword_of_int (IT + 0x60)) by pcw.
    iEval (rewrite Hp60) in "Hpc".
    (* ===== +0x60 addi s2,a0,1112 : the limit, one past the last entry ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (IT + 0x60)) Rs2 Ra0
              (mword_of_int 1112 : mword 12) A3 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi60").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (A4 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (rget A3 Ra0)
                     (sign_extend' 64 (mword_of_int 1112 : mword 12)))]> A3).
    assert (Hs1112 : (sign_extend' 64 (mword_of_int 1112 : mword 12) : mword 64)
                     = mword_of_int 1112) by pcw.
    assert (HA4s2 : A4 !!! Regidx Rs2
                    = pa_add (b_data (bnode kk)) (4 * NINDIRECT)%nat).
    { rewrite /A4 upd_eq. rgne. rewrite HA3a0 Hs1112.
      rewrite /b_data pa_add_add /NINDIRECT /pa_add /add_vec_int.
      f_equal. }
    assert (HA4s1 : A4 !!! Regidx Rs1
                    = pa_add (b_data (bnode kk)) (4 * 0)%nat)
      by (rewrite /A4 upd_ne; [exact HA3s1 | nz]).
    assert (HA4s3 : A4 !!! Regidx Rs3 = ip).
    { rewrite /A4 upd_ne; [| nz]. rewrite /A3 upd_ne; [| nz].
      rewrite /A2 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcs1 Rs3 ltac:(vm_compute; reflexivity)).
      exact HA1s3. }
    assert (HA4s4 : A4 !!! Regidx Rs4 = bnode kk)
      by (rewrite /A4 upd_ne; [exact HA3s4 | nz]).
    assert (HA4sp : it_sp m A4).
    { rewrite /it_sp /A4 upd_ne; [| nz]. rewrite /A3 upd_ne; [| nz].
      rewrite /A2 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcs1 csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HA1sp. }
    (* s4 is now live, so only the weaker invariant survives from here to
       the [ld s4] at +0x90 *)
    assert (HA4thr : it_thr4 m A4).
    { intros c Hcs2 N2 N8 N9 N18 N19 N20.
      rewrite /A4 upd_ne; [| regne]. rewrite /A3 upd_ne; [| regne].
      rewrite /A2 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hcs1 c Hcs2).
      exact (HA1thr c Hcs2 N2 N8 N9 N18 N19). }
    assert (Hp64 : add_vec_int (mword_of_int (IT + 0x60) : mword 64) 4
                   = mword_of_int (IT + 0x64)) by pcw.
    iEval (rewrite Hp64) in "Hpc".
    (* ===== +0x64 c.j : into the body test ===== *)
    iApply (wp_cj_s_sconf (mword_of_int (IT + 0x64))
              (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0")))
              A4 (K - 6)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi64").
    iIntros (CID8 Hq8). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt6c : add_vec (mword_of_int (IT + 0x64) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 4 : mword 11) ('b"0"))))
                     = mword_of_int (IT + 0x6c)) by pcw.
    iEval (rewrite Htgt6c) in "Hpc".
    (* the buffer, out of the handle; the loop never writes it, so the same
       bytes go back at the exit *)
    iDestruct (bm_held_swap with "Hheld") as "[Hbuf Hheldback]".
    iEval (rewrite Hbsl) in "Hbuf".
    (* the entry bundle arrives at cursor 0 already -- the conversion from
       inode_blocks happens in the assembly, not here *)
    assert (Hfz : used ∖ bm_dir_freed bm NDIRECT
                  = used ∖ (bm_dir_freed bm NDIRECT ∪ bm_ent_freed bm 0)).
    { rewrite bm_ent_freed_0 union_empty_r_L. reflexivity. }
    iEval (rewrite Hfz) in "Hbmr".
    iAssert (it_ent_state γ γfs bm data cov logstart bmapstart size used crb Sb e0 w 0)
      with "[Hres Hbmr Hpaid]" as "Hst".
    { iApply (it_ent_state_close with "Hres Hbmr Hpaid"). }
    (* Hcnt came back from bread at CID4, not from the pre-call transport *)
    iDestruct (cpu_own_transport CID4 CID8 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID4 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID4 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iApply (it_eloop (CID0 := CID8) γs jx γl γu γd γk pd pav pu bn γ γfs
              cov logstart bmapstart size dev used ip bm data kk
              (mword_of_int 0 : mword 32) pidv dq dqd dqb crb Sb e0 w m K C b eb NINDIRECT lks
              HK ltac:(split; [exact Hcovok | exact Hlogsub]) Hsize Hbm0
              Hbmcov Hbmlog Hwf Hrange Hblen
              Hkk Hj Hgl
              0%nat A4 ltac:(unfold NINDIRECT; lia) ltac:(lia)
              HA4sp HA4thr HA4s1 HA4s2 HA4s3 HA4s4 Hlkbelow
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hprocs Hppid Hidev Hsbb Hdevi Hdgeom Hdlock Hsl Hbuf Hst").
    (* ===== the loop is done: +0x7a onwards ===== *)
    iIntros (CID9 Hq9 Mx) "%HMxsp %HMxthr %HMxs3 %HMxs4 Hcg Hcnt Hextc Hextm Hpc
                           Hppid Hidev Hsbb Hsl Hbuf Hst".
    iPoseProof (iti_7a with "Htext") as "Hi7a".
    iPoseProof (iti_7c with "Htext") as "Hi7c".
    iPoseProof (iti_80 with "Htext") as "Hi80".
    iPoseProof (iti_84 with "Htext") as "Hi84".
    iPoseProof (iti_88 with "Htext") as "Hi88".
    iPoseProof (iti_8c with "Htext") as "Hi8c".
    iPoseProof (iti_90 with "Htext") as "Hi90".
    iPoseProof (iti_92 with "Htext") as "Hi92".
    (* the buffer goes back into the handle unchanged: the loop only read *)
    iDestruct ("Hheldback" $! (ind_bytes (bm_ent bm)) with "Hbuf") as "Hheld".
    (* the payload index is the logged content, so the rebuilt handle is
       [bio_locked] -- both byte lists are the same one *)
    iEval (rewrite Hbsl) in "Hheld".
    iDestruct (it_ent_state_open with "Hst") as "(Hres & Hbmr & Hpaid)".
    (* ===== +0x7a mv a0,s4 : a0 := bp ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (IT + 0x7a)) Ra0 Rs4
              Mx (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7a").
    iIntros (CID10 Hq10) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (Mx !!! Regidx Rs4 : mword 64))]> Mx).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget Mx Rs4))]> Mx)
      with B0.
    assert (Hzl2 : forall x : mword 64, add_vec zero_reg x = x).
    { intros x. apply bv_eq. rewrite add_vec64_unsigned.
      assert (Hz : bv_unsigned (zero_reg : mword 64) = 0)
        by (vm_compute; reflexivity).
      rewrite Hz Z.add_0_l. apply bv_wrap_small, bv_unsigned_in_range. }
    assert (HB0a0 : B0 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B0 upd_eq Hzl2; exact HMxs4).
    assert (HB0s3 : B0 !!! Regidx Rs3 = ip)
      by (rewrite /B0 upd_ne; [exact HMxs3 | nz]).
    assert (HB0s4 : B0 !!! Regidx Rs4 = bnode kk)
      by (rewrite /B0 upd_ne; [exact HMxs4 | nz]).
    assert (HB0sp : it_sp m B0)
      by (rewrite /it_sp /B0 upd_ne; [exact HMxsp | nz]).
    assert (HB0thr : it_thr4 m B0).
    { intros c Hcs2 N2 N8 N9 N18 N19 N20.
      rewrite /B0 upd_ne; [| regne]. exact (HMxthr c Hcs2 N2 N8 N9 N18 N19 N20). }
    assert (Hp7c : add_vec_int (mword_of_int (IT + 0x7a) : mword 64) 2
                   = mword_of_int (IT + 0x7c)) by pcw.
    iEval (rewrite Hp7c) in "Hpc".
    (* ===== +0x7c jal brelse ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (IT + 0x7c)) Rra
              (mword_of_int 2095366 : mword 21) B0 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi7c").
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (B1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (IT + 0x7c) : mword 64) 4)]> B0).
    assert (Htgtbr2 : add_vec (mword_of_int (IT + 0x7c) : mword 64)
                        (sign_extend' 64 (mword_of_int 2095366 : mword 21))
                      = mword_of_int KernelSyms.brelse) by pcw.
    iEval (rewrite Htgtbr2) in "Hpc".
    assert (HB1a0 : B1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B1 upd_ne; [exact HB0a0 | nz]).
    assert (HB1ra : B1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (IT + 0x7c) : mword 64) 4)
      by (rewrite /B1; apply upd_eq).
    assert (HB1s3 : B1 !!! Regidx Rs3 = ip)
      by (rewrite /B1 upd_ne; [exact HB0s3 | nz]).
    assert (HB1s4 : B1 !!! Regidx Rs4 = bnode kk)
      by (rewrite /B1 upd_ne; [exact HB0s4 | nz]).
    assert (HB1sp : it_sp m B1)
      by (rewrite /it_sp /B1 upd_ne; [exact HB0sp | nz]).
    assert (HB1thr : it_thr4 m B1).
    { intros c Hcs2 N2 N8 N9 N18 N19 N20.
      rewrite /B1 upd_ne; [| regne]. exact (HB0thr c Hcs2 N2 N8 N9 N18 N19 N20). }
    assert (HKbl : (K_brelse <= K - 6)%nat) by (unfold K_brelse; lia).
    (* Hcnt arrived with the loop's exit at CID9 *)
    iDestruct (cpu_own_transport CID9 CID11 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kk
              pidv dev (bm_ind bm : mword 32) dq B1 (K - 6)%nat eb
              (proc_addr jx) C (ind_bytes (bm_ent bm)) bsd0 d0 b lks
              HKbl Hkk HB1a0
              (* brelse's bound is "bcache"(4); it_iarm's own is "log"(3),
                 and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hppid Hprocs Hheld").
    all: try lkbelow.
    iIntros (CID12 Hq12 mR) "%Hcs2 Hcg Hcnt Hpc Hppid Hsl1".
    assert (Hpc80 : ret_pc (B1 !!! Regidx Rra : mword 64)
                    = mword_of_int (IT + 0x80)) by (rewrite HB1ra; pcw).
    iEval (rewrite Hpc80) in "Hpc".
    (* the held slot is back: three again *)
    (* brelse returned the held unit as a single [bslot]; keep it parked
       rather than merging -- bfree wants exactly the pair *)
    set (B2 := <[Regidx Rra := regval_into_reg
                  (m !!! Regidx Rra : mword 64)]> mR).
    (* mR is brelse's callee_saved successor of B1 *)
    pose proof Hcs2 as Hcs2'.
    assert (HmRs3 : mR !!! Regidx Rs3 = ip).
    { rewrite (callee_saved_lookup Hcs2' Rs3 ltac:(vm_compute; reflexivity)).
      exact HB1s3. }
    assert (HmRsp : it_sp m mR).
    { rewrite /it_sp
        (callee_saved_lookup Hcs2' csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HB1sp. }
    assert (HmRthr : it_thr4 m mR).
    { intros c Hcs3 N2 N8 N9 N18 N19 N20.
      rewrite (callee_saved_lookup Hcs2' c Hcs3).
      exact (HB1thr c Hcs3 N2 N8 N9 N18 N19 N20). }
    (* ===== +0x80 lw a1,128(s3) : a1 := ip->addrs[NDIRECT] ===== *)
    assert (Hica : add_vec (rget mR Rs3)
                     (sign_extend' 64 (mword_of_int 128 : mword 12))
                   = i_addr ip NDIRECT).
    { rgne. rewrite HmRs3 it_dir_limit /pa_add /add_vec_int. f_equal. }
    iEval (rewrite -Hica) in "Hindcell".
    iApply (wp_lw_s_sconf (mword_of_int (IT + 0x80)) Ra1 Rs3
              (mword_of_int 128 : mword 12) mR (K - 6)%nat
              (bm_ind bm : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi80 Hindcell").
    iIntros (CID13 Hq13) "Hcg Hpc Hindcell".
    iEval (rewrite Hica) in "Hindcell".
    set (C0 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (bm_ind bm : mword 32))]> mR).
    assert (HC0a1 : C0 !!! Regidx Ra1
                    = sign_extend' 64 (bm_ind bm : mword 32))
      by (rewrite /C0; apply upd_eq).
    assert (HC0s3 : C0 !!! Regidx Rs3 = ip)
      by (rewrite /C0 upd_ne; [exact HmRs3 | nz]).
    assert (HC0sp : it_sp m C0)
      by (rewrite /it_sp /C0 upd_ne; [exact HmRsp | nz]).
    assert (HC0thr : it_thr4 m C0).
    { intros c Hcs3 N2 N8 N9 N18 N19 N20.
      rewrite /C0 upd_ne; [| regne]. exact (HmRthr c Hcs3 N2 N8 N9 N18 N19 N20). }
    assert (Hp84 : add_vec_int (mword_of_int (IT + 0x80) : mword 64) 4
                   = mword_of_int (IT + 0x84)) by pcw.
    iEval (rewrite Hp84) in "Hpc".
    (* ===== +0x84 lw a0,0(s3) : a0 := ip->dev ===== *)
    assert (Hdva2 : add_vec (rget C0 Rs3)
                      (sign_extend' 64 (mword_of_int 0 : mword 12)) = i_dev ip).
    { rgne. rewrite HC0s3. reflexivity. }
    iEval (rewrite -Hdva2) in "Hidev".
    iApply (wp_lw_s_sconf (mword_of_int (IT + 0x84)) Ra0 Rs3
              (mword_of_int 0 : mword 12) C0 (K - 6)%nat dev b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi84 Hidev").
    iIntros (CID14 Hq14) "Hcg Hpc Hidev".
    iEval (rewrite Hdva2) in "Hidev".
    set (C1 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> C0).
    assert (HC1a0 : C1 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /C1; apply upd_eq).
    assert (HC1a1 : C1 !!! Regidx Ra1
                    = sign_extend' 64 (bm_ind bm : mword 32))
      by (rewrite /C1 upd_ne; [exact HC0a1 | nz]).
    assert (HC1s3 : C1 !!! Regidx Rs3 = ip)
      by (rewrite /C1 upd_ne; [exact HC0s3 | nz]).
    assert (HC1sp : it_sp m C1)
      by (rewrite /it_sp /C1 upd_ne; [exact HC0sp | nz]).
    assert (HC1thr : it_thr4 m C1).
    { intros c Hcs3 N2 N8 N9 N18 N19 N20.
      rewrite /C1 upd_ne; [| regne]. exact (HC0thr c Hcs3 N2 N8 N9 N18 N19 N20). }
    assert (Hp88 : add_vec_int (mword_of_int (IT + 0x84) : mword 64) 4
                   = mword_of_int (IT + 0x88)) by pcw.
    iEval (rewrite Hp88) in "Hpc".
    (* ===== +0x88 jal bfree : the indirect block itself ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (IT + 0x88)) Rra
              (mword_of_int 2096022 : mword 21) C1 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi88").
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (C2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (IT + 0x88) : mword 64) 4)]> C1).
    assert (Htgtbf2 : add_vec (mword_of_int (IT + 0x88) : mword 64)
                        (sign_extend' 64 (mword_of_int 2096022 : mword 21))
                      = mword_of_int KernelSyms.bfree) by pcw.
    iEval (rewrite Htgtbf2) in "Hpc".
    assert (HC2a0 : C2 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /C2 upd_ne; [exact HC1a0 | nz]).
    assert (HC2a1 : C2 !!! Regidx Ra1
                    = sign_extend' 64 (bm_ind bm : mword 32))
      by (rewrite /C2 upd_ne; [exact HC1a1 | nz]).
    assert (HC2ra : C2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (IT + 0x88) : mword 64) 4)
      by (rewrite /C2; apply upd_eq).
    assert (HC2s3 : C2 !!! Regidx Rs3 = ip)
      by (rewrite /C2 upd_ne; [exact HC1s3 | nz]).
    assert (HC2sp : it_sp m C2)
      by (rewrite /it_sp /C2 upd_ne; [exact HC1sp | nz]).
    assert (HC2thr : it_thr4 m C2).
    { intros c Hcs3 N2 N8 N9 N18 N19 N20.
      rewrite /C2 upd_ne; [| regne]. exact (HC1thr c Hcs3 N2 N8 N9 N18 N19 N20). }
    assert (Hilt2 : bv_unsigned (bm_ind bm : mword 32) < size)
      by (rewrite -Hstop; exact (Hrange MAXFILE ltac:(lia)
            ltac:(rewrite Hstop; exact Hindnz))).
    iDestruct (bm_paidS_use with "Hpaid") as (cr u' Sq)
        "(%Hcrin & %Hbud & %Hqsub & Hop & Hback)".
    (* the credit as a resource, from the loop's own-set claim *)
    iPoseProof (log_credit_own γ cr Sq e0 bmapstart Hcrin) as "#Hcrbm".
    iDestruct (cpu_own_transport CID12 CID15 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* Hextc/Hextm were last transported at CID9, the it_eloop exit --
       brelse's contract does not mention them, so they are STRANDED there
       and must cross the WIDER span (CID9 -> CID15), skipping over brelse's
       own (narrower) cpu_own-only hop. *)
    iDestruct (trap_csrs_ext_transport CID9 CID15 eb (proc_addr jx)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID9 CID15 eb (proc_addr jx)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    (* Hexit was already moved to CID3 before the bread *)
    iDestruct (wp_next_shift (b := true) (CIDa := CID3) (CIDb := CID15)
                 ltac:(wp_next_chain) with "Hexit") as "Hexit".
    assert (HKbf2 : (K_bfree <= K - 6)%nat) by (unfold K_bfree; lia).
    iApply (BF.wp_bfree_gen γs jx γl γu γd γk pd pav pu bn γ γfs
              cov logstart bmapstart size dev
              (used ∖ (bm_dir_freed bm NDIRECT ∪ bm_ent_freed bm NINDIRECT))
              (bm_ind bm : mword 32) (ind_bytes (bm_ent bm)) u' cr Sq e0
              pidv dq dqb C2 (K - 6)%nat eb C b lks
              HKbf2 ltac:(split; [exact Hcovok | exact Hlogsub]) Hsize Hbm0
              Hbmcov Hbmlog
              ltac:(destruct (bv_unsigned_in_range 32 (bm_ind bm))
                      as [Hlo _]; split; [exact Hlo | exact Hilt2])
              Hicov Hilog
              ltac:(rewrite ind_bytes_length Hentlen; reflexivity)
              Hj Hgl HC2a0 HC2a1
              Hlkbelow
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hsbb Hbmr Hindblk
                    Hindtok Hppid Hprocs Hdevi Hdgeom Hdlock Hsl Hcrbm Hop").
    all: try lkbelow.
    iIntros (CID16 Hq16 mZ) "%Hcs3 Hcg Hcnt Hextc Hextm Hpc Hppid Hsbb Hbmr Hsl Hop".
    assert (Hpc8c : ret_pc (C2 !!! Regidx Rra : mword 64)
                    = mword_of_int (IT + 0x8c)) by (rewrite HC2ra; pcw).
    iEval (rewrite Hpc8c) in "Hpc".
    pose proof Hcs3 as Hcs3'.
    assert (HmZs3 : mZ !!! Regidx Rs3 = ip).
    { rewrite (callee_saved_lookup Hcs3' Rs3 ltac:(vm_compute; reflexivity)).
      exact HC2s3. }
    assert (HmZsp : it_sp m mZ).
    { rewrite /it_sp
        (callee_saved_lookup Hcs3' csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HC2sp. }
    assert (HmZthr : it_thr4 m mZ).
    { intros c Hcs4 N2 N8 N9 N18 N19 N20.
      rewrite (callee_saved_lookup Hcs3' c Hcs4).
      exact (HC2thr c Hcs4 N2 N8 N9 N18 N19 N20). }
    (* THE POOL IS WHOLE: the direct entries, the indirect entries and the
       indirect block itself are exactly [bm_blocks bm] ([bm_blocks_split]) *)
    assert (Hpool : used ∖ (bm_dir_freed bm NDIRECT ∪ bm_ent_freed bm NINDIRECT)
                    ∖ {[ bv_unsigned (bm_ind bm : mword 32) ]}
                    = used ∖ bm_blocks bm).
    { rewrite (bm_blocks_split bm Hdirlen Hentlen).
      exact (freed_pool_grow _ _ _ Hindnz). }
    iEval (rewrite Hpool) in "Hbmr".
    iDestruct ("Hback" with "[Hop]") as "Hpaid";
      [ rewrite Hbud; iExact "Hop" |].
    (* ===== +0x8c sw zero,128(s3) : ip->addrs[NDIRECT] = 0 ===== *)
    iDestruct (sie_cap_gpr_x0 mZ (K - 6)%nat b (proc_addr jx) Rz
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0z Hcg]".
    assert (Hica2 : add_vec (rget mZ Rs3)
                      (sign_extend' 64 (mword_of_int 128 : mword 12))
                    = i_addr ip NDIRECT).
    { rgne. rewrite HmZs3 it_dir_limit /pa_add /add_vec_int. f_equal. }
    iEval (rewrite -Hica2) in "Hindcell".
    iApply (wp_sw_s_sconf (mword_of_int (IT + 0x8c)) Rz Rs3
              (mword_of_int 128 : mword 12) mZ (K - 6)%nat
              (bm_ind bm : mword 32) b with "Hcg Hpc Hi8c Hindcell").
    iIntros (CID17 Hq17) "Hcg Hpc Hindcell".
    iEval (rewrite Hica2) in "Hindcell".
    assert (Hz32b : trunc32 (rget mZ Rz) = (bv_0 32 : mword 32))
      by (rgne; rewrite Hx0z; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hz32b) in "Hindcell".
    (* THE MAP IS EMPTY: the direct part was zeroed by the first loop, the
       indirect cell by that store, and the entry list is replaced wholesale
       because the block it lived in is gone *)
    iDestruct ("Hmapback" $! (bv_0 32) (replicate NINDIRECT (bv_0 32))
                 with "Hindcell []") as "Hmap".
    { rewrite /ind_res /ind_blk /ind_tok. cbn [bm_ind].
      destruct (decide (bv_unsigned (bv_0 32) = 0)) as [_|Hc];
        [iSplitR; done | exfalso; apply Hc; reflexivity]. }
    assert (Hmempty : MkBlkmap (bm_dir (bm_dir_zeroed bm NDIRECT)) (bv_0 32)
                        (replicate NINDIRECT (bv_0 32)) = bm_empty).
    { rewrite (bm_dir_zeroed_full bm Hdirlen). reflexivity. }
    iEval (rewrite Hmempty) in "Hmap".
    assert (Hp90 : add_vec_int (mword_of_int (IT + 0x8c) : mword 64) 4
                   = mword_of_int (IT + 0x90)) by pcw.
    iEval (rewrite Hp90) in "Hpc".
    (* ===== +0x90 ld s4,0(sp) : s4 back, and with it the FULL it_thr =====
       This is the instruction the tail depends on: it runs BEFORE the jump
       at +0x92, which is the only reason it_tail may assert the caller's s4
       is intact. *)
    assert (Hs6b : add_vec (mZ !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite HmZsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hs6b) in "Hslot6".
    iApply (wp_cldsp_s_sconf (mword_of_int (IT + 0x90))
              (mword_of_int 0 : mword 6) Rs4
              mZ (K - 6)%nat (m !!! Regidx Rs4 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi90 [Hslot6]").
    { iExact "Hslot6". }
    iIntros (CID18 Hq18) "Hcg Hpc Hslot6".
    iEval (rewrite Hs6b) in "Hslot6".
    set (D0 := <[Regidx Rs4 := regval_into_reg
                  (m !!! Regidx Rs4 : mword 64)]> mZ).
    assert (HD0s4 : D0 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64))
      by (rewrite /D0; apply upd_eq).
    assert (HD0s3 : D0 !!! Regidx Rs3 = ip)
      by (rewrite /D0 upd_ne; [exact HmZs3 | nz]).
    assert (HD0sp : it_sp m D0)
      by (rewrite /it_sp /D0 upd_ne; [exact HmZsp | nz]).
    (* the FULL threading invariant is back: s4 is the caller's again *)
    assert (HD0thr : it_thr m D0).
    { intros c Hcs4 N2 N8 N9 N18 N19.
      destruct (decide (c = Rs4)) as [->|Hne4].
      - rewrite HD0s4. reflexivity.
      - rewrite /D0 upd_ne; [| by intros Hq; apply Hne4; injection Hq].
        exact (HmZthr c Hcs4 N2 N8 N9 N18 N19 Hne4). }
    assert (Hp92 : add_vec_int (mword_of_int (IT + 0x90) : mword 64) 2
                   = mword_of_int (IT + 0x92)) by pcw.
    iEval (rewrite Hp92) in "Hpc".
    (* ===== +0x92 c.j : rejoin the tail at +0x38 ===== *)
    iApply (wp_cj_s_sconf (mword_of_int (IT + 0x92))
              (sign_extend' 21 (concat_vec (mword_of_int 2003 : mword 11) ('b"0")))
              D0 (K - 6)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi92").
    iIntros (CID19 Hq19). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt38 : add_vec (mword_of_int (IT + 0x92) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 2003 : mword 11) ('b"0"))))
                     = mword_of_int (IT + 0x38)) by pcw.
    iEval (rewrite Htgt38) in "Hpc".
    (* ===== hand the emptied inode to the tail ===== *)
    rewrite /it_armexit.
    iDestruct (cpu_own_transport CID16 CID19 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID16 CID19 eb (proc_addr jx)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID16 CID19 eb (proc_addr jx)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID15) (CIDb := CID19)
                 ltac:(wp_next_chain) with "Hexit") as "Hexit".
    iSpecialize ("Hexit" $! CID19 with "[%]"); [wp_next_chain|].
    iAssert (bslots bn 3) with "[Hsl Hsl1]" as "Hsl3".
    { assert (H3 : (3 = 2 + 1)%nat) by lia.
      rewrite H3 bslots_op. iSplitL "Hsl"; [iExact "Hsl" | iExact "Hsl1"]. }
    iApply ("Hexit" $! D0 with "[%] [%] [%] Hcg Hcnt Hextc Hextm Hpc Hppid Hidev Hsbb
                                [Hslot6] Hmap [] Hbmr Hsl3 Hpaid");
      [exact HD0sp | exact HD0thr | exact HD0s3
      | iExists _; iExact "Hslot6"
      | iApply inode_blocks_empty_any ].
  Qed.

End ItruncIArm.

(* ===================================================================== *)
(*  THE WHOLE FUNCTION: prologue, the direct loop, the indirect test,     *)
(*  and the shared tail.                                                  *)
(* ===================================================================== *)
Section ItruncMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}.

  (* THE WALK IS THE GEN FORM (GR-2a finding 1).  [log_opS] is an exclusive
     ghost_map element with no auth-monotone shadow, so a counted post hands
     back an element at an unrelated existential set and NOTHING recovers a
     relation to the caller's.  The credited/set-form contract therefore
     cannot be derived outside a walk; it has to BE the walk, and the counted
     contract is the ~20-line seal below, taken at the [log_op]
     existential's own witness. *)
  Lemma wp_itrunc_gen `{GEN : GenId} `{CID : CpuId}       (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z)
      (dev : mword 32) (used : gset Z)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) (u : nat) (Sb : gset Z) (crb cru : bool)
      (e0 : nat)
      (pidv : mword 32) (dq dqd dqn dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool) (lks : gset string)
    : wp_itrunc_gen_body γs j γl γu γd γk pd pav pu bn γ γfs γi
                         cov logstart bmapstart inodestart nib size dev used
                         ip inum dn dn0 bm data u Sb crb cru e0
                         pidv dq dqd dqn dqb dqs m K eb C b lks.
  Proof.
    cbv beta delta [wp_itrunc_gen_body].
    intros pcE pj ret_tgt HK Hcrb Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist Hicov Hilog
           Hnib Hdtnz Hstab Hnlk Hwf Hbelow Hblen Hadr Hj Hgl Ha0 Hlkbelow.
    pose proof HK as HK'. unfold K_itrunc in HK'.
    (* THE PER-SLOT RANGE FACT, no longer a premise: [blkmap_wf] already
       says every block the map names is covered, and [cov_below] bounds a
       covered block by the FS size (design §6(i)).  Everything below is
       unchanged -- the loops still take [Hrange] in its old shape. *)
    assert (Hrange : forall i : nat, (i <= MAXFILE)%nat ->
              bv_unsigned (bm_slot bm i) <> 0 ->
              bv_unsigned (bm_slot bm i) < size).
    { intros i Hi Hnz.
      exact (proj2 (blkmap_slot_inrange cov logstart size bm
                      (proj1 Hgeom) Hbelow Hwf i Hi Hnz)). }
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio #Hlctx Hidev Hinum Hmeta Hmap
              Hblks Hsbb Hsbi Hbmr #Hireg Hdn Hppid #Hprocs #Hdevi
              #Hdgeom #Hdlock Hsl #Hcru Hop Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    iPoseProof (iti_00 with "Htext") as "Hi00".
    iPoseProof (iti_02 with "Htext") as "Hi02".
    iPoseProof (iti_04 with "Htext") as "Hi04".
    iPoseProof (iti_06 with "Htext") as "Hi06".
    iPoseProof (iti_08 with "Htext") as "Hi08".
    iPoseProof (iti_0a with "Htext") as "Hi0a".
    iPoseProof (iti_0c with "Htext") as "Hi0c".
    iPoseProof (iti_0e with "Htext") as "Hi0e".
    iPoseProof (iti_10 with "Htext") as "Hi10".
    iPoseProof (iti_14 with "Htext") as "Hi14".
    iPoseProof (iti_18 with "Htext") as "Hi18".
    (* ===== +0x00 c.addi16sp sp,-48 : claim the six slots ===== *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6)
              m K 6 b ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hstk Hpc".
    assert (Hp02 : add_vec_int pcE 2 = mword_of_int (IT + 0x02)) by pcw.
    iEval (rewrite Hp02) in "Hpc".
    set (P0 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    assert (HP0sp : it_sp m P0) by (rewrite /it_sp /P0; apply upd_eq).
    assert (HP0thr : it_thr m P0).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P0 upd_ne;
        [reflexivity | intros Hq; injection Hq as Hq'; exact (N2 Hq')]. }
    assert (HP0a0 : P0 !!! Regidx Ra0 = ip)
      by (rewrite /P0 upd_ne; [exact Ha0 | nz]).
    rewrite stack_own_slots. cbn [seq].
    iDestruct "Hstk" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & _)".
    iDestruct "Hf1" as (v1) "Hf1". iDestruct "Hf2" as (v2) "Hf2".
    iDestruct "Hf3" as (v3) "Hf3". iDestruct "Hf4" as (v4) "Hf4".
    iDestruct "Hf5" as (v5) "Hf5".
    (* the five slot addresses, in the c.sdsp spelling *)
    assert (Hsl1 : add_vec (P0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                   = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hsl2 : add_vec (P0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                   = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hsl3 : add_vec (P0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                   = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hsl4 : add_vec (P0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                   = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hsl5 : add_vec (P0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (HP0ra : (P0 !!! Regidx Rra : mword 64)
                    = (m !!! Regidx Rra : mword 64))
      by (rewrite /P0 upd_ne; [reflexivity | nz]).
    assert (HP0s0 : (P0 !!! Regidx Rs0 : mword 64)
                    = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /P0 upd_ne; [reflexivity | nz]).
    assert (HP0s1 : (P0 !!! Regidx Rs1 : mword 64)
                    = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /P0 upd_ne; [reflexivity | nz]).
    assert (HP0s2 : (P0 !!! Regidx Rs2 : mword 64)
                    = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P0 upd_ne; [reflexivity | nz]).
    assert (HP0s3 : (P0 !!! Regidx Rs3 : mword 64)
                    = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P0 upd_ne; [reflexivity | nz]).
    (* +0x02 sd ra,40(sp) *)
    iEval (rewrite -Hsl1) in "Hf1".
    iApply (wp_csdsp_s_sconf (mword_of_int (IT + 0x02))
              (mword_of_int 5 : mword 6) Rra P0 (K - 6)%nat v1 b
              with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    iEval (rewrite Hsl1) in "Hf1". iEval (rgne) in "Hf1". iEval (rewrite HP0ra) in "Hf1".
    assert (Hp04 : add_vec_int (mword_of_int (IT + 0x02) : mword 64) 2
                   = mword_of_int (IT + 0x04)) by pcw.
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd rs0 *)
    iEval (rewrite -Hsl2) in "Hf2".
    iApply (wp_csdsp_s_sconf (mword_of_int (IT + 0x04))
              (mword_of_int 4 : mword 6) Rs0 P0 (K - 6)%nat v2 b
              with "Hcg Hpc Hi04 Hf2").
    iIntros (CID3x Hq3x) "Hcg Hpc Hf2".
    iEval (rewrite Hsl2) in "Hf2". iEval (rgne) in "Hf2". iEval (rewrite HP0s0) in "Hf2".
    assert (Hp06 : add_vec_int (mword_of_int (IT + 0x04) : mword 64) 2
                   = mword_of_int (IT + 0x06)) by pcw.
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 sd rs1 *)
    iEval (rewrite -Hsl3) in "Hf3".
    iApply (wp_csdsp_s_sconf (mword_of_int (IT + 0x06))
              (mword_of_int 3 : mword 6) Rs1 P0 (K - 6)%nat v3 b
              with "Hcg Hpc Hi06 Hf3").
    iIntros (CID4x Hq4x) "Hcg Hpc Hf3".
    iEval (rewrite Hsl3) in "Hf3". iEval (rgne) in "Hf3". iEval (rewrite HP0s1) in "Hf3".
    assert (Hp08 : add_vec_int (mword_of_int (IT + 0x06) : mword 64) 2
                   = mword_of_int (IT + 0x08)) by pcw.
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 sd rs2 *)
    iEval (rewrite -Hsl4) in "Hf4".
    iApply (wp_csdsp_s_sconf (mword_of_int (IT + 0x08))
              (mword_of_int 2 : mword 6) Rs2 P0 (K - 6)%nat v4 b
              with "Hcg Hpc Hi08 Hf4").
    iIntros (CID5x Hq5x) "Hcg Hpc Hf4".
    iEval (rewrite Hsl4) in "Hf4". iEval (rgne) in "Hf4". iEval (rewrite HP0s2) in "Hf4".
    assert (Hp0a : add_vec_int (mword_of_int (IT + 0x08) : mword 64) 2
                   = mword_of_int (IT + 0x0a)) by pcw.
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a sd rs3 *)
    iEval (rewrite -Hsl5) in "Hf5".
    iApply (wp_csdsp_s_sconf (mword_of_int (IT + 0x0a))
              (mword_of_int 1 : mword 6) Rs3 P0 (K - 6)%nat v5 b
              with "Hcg Hpc Hi0a Hf5").
    iIntros (CID6x Hq6x) "Hcg Hpc Hf5".
    iEval (rewrite Hsl5) in "Hf5". iEval (rgne) in "Hf5". iEval (rewrite HP0s3) in "Hf5".
    assert (Hp0c : add_vec_int (mword_of_int (IT + 0x0a) : mword 64) 2
                   = mword_of_int (IT + 0x0c)) by pcw.
    iEval (rewrite Hp0c) in "Hpc".
    (* the frame is complete: five saved registers and the sixth slot,
       which only the indirect arm ever writes *)
    iAssert (it_frame m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6]" as "Hframe".
    { rewrite /it_frame. iFrame "Hf1 Hf2 Hf3 Hf4 Hf5". iExact "Hf6". }
    (* ===== +0x0c c.addi4spn s0,sp,48 : the frame pointer, unused below ==== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (IT + 0x0c))
              (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) Rs0
              P0 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rdok) with "Hcg Hpc Hi0c").
    iIntros (CID7x Hq7x) "Hcg Hpc".
    set (Q0 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (P0 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> P0).
    assert (HQ0a0 : Q0 !!! Regidx Ra0 = ip)
      by (rewrite /Q0 upd_ne; [exact HP0a0 | nz]).
    assert (HQ0sp : it_sp m Q0)
      by (rewrite /it_sp /Q0 upd_ne; [exact HP0sp | nz]).
    assert (Hp0e : add_vec_int (mword_of_int (IT + 0x0c) : mword 64) 2
                   = mword_of_int (IT + 0x0e)) by pcw.
    iEval (rewrite Hp0e) in "Hpc".
    (* ===== +0x0e mv s3,a0 : s3 := ip, and it stays there ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (IT + 0x0e)) Rs3 Ra0
              Q0 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0e").
    iIntros (CID8x Hq8x) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (Q1 := <[Regidx Rs3 := regval_into_reg
                  (add_vec zero_reg (Q0 !!! Regidx Ra0 : mword 64))]> Q0).
    change (<[Regidx Rs3 := regval_into_reg (add_vec zero_reg (rget Q0 Ra0))]> Q0)
      with Q1.
    assert (Hzl3 : forall x : mword 64, add_vec zero_reg x = x).
    { intros x. apply bv_eq. rewrite add_vec64_unsigned.
      assert (Hz : bv_unsigned (zero_reg : mword 64) = 0)
        by (vm_compute; reflexivity).
      rewrite Hz Z.add_0_l. apply bv_wrap_small, bv_unsigned_in_range. }
    assert (HQ1s3 : Q1 !!! Regidx Rs3 = ip)
      by (rewrite /Q1 upd_eq Hzl3; exact HQ0a0).
    assert (HQ1a0 : Q1 !!! Regidx Ra0 = ip)
      by (rewrite /Q1 upd_ne; [exact HQ0a0 | nz]).
    assert (HQ1sp : it_sp m Q1)
      by (rewrite /it_sp /Q1 upd_ne; [exact HQ0sp | nz]).
    assert (Hp10 : add_vec_int (mword_of_int (IT + 0x0e) : mword 64) 2
                   = mword_of_int (IT + 0x10)) by pcw.
    iEval (rewrite Hp10) in "Hpc".
    (* ===== +0x10 addi s1,a0,80 : the direct cursor ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (IT + 0x10)) Rs1 Ra0
              (mword_of_int 80 : mword 12) Q1 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi10").
    iIntros (CID9x Hq9x) "Hcg Hpc".
    set (Q2 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (rget Q1 Ra0)
                     (sign_extend' 64 (mword_of_int 80 : mword 12)))]> Q1).
    assert (HQ2s1 : Q2 !!! Regidx Rs1 = i_addr ip 0).
    { rewrite /Q2 upd_eq. rgne. rewrite HQ1a0 /i_addr. f_equal. }
    assert (HQ2s3 : Q2 !!! Regidx Rs3 = ip)
      by (rewrite /Q2 upd_ne; [exact HQ1s3 | nz]).
    assert (HQ2a0 : Q2 !!! Regidx Ra0 = ip)
      by (rewrite /Q2 upd_ne; [exact HQ1a0 | nz]).
    assert (HQ2sp : it_sp m Q2)
      by (rewrite /it_sp /Q2 upd_ne; [exact HQ1sp | nz]).
    assert (Hp14 : add_vec_int (mword_of_int (IT + 0x10) : mword 64) 4
                   = mword_of_int (IT + 0x14)) by pcw.
    iEval (rewrite Hp14) in "Hpc".
    (* ===== +0x14 addi s2,a0,128 : the direct loop's limit ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (IT + 0x14)) Rs2 Ra0
              (mword_of_int 128 : mword 12) Q2 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi14").
    iIntros (CID10x Hq10x) "Hcg Hpc".
    set (Q3 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (rget Q2 Ra0)
                     (sign_extend' 64 (mword_of_int 128 : mword 12)))]> Q2).
    assert (HQ3s2 : Q3 !!! Regidx Rs2 = i_addr ip NDIRECT).
    { rewrite /Q3 upd_eq. rgne. rewrite HQ2a0 it_dir_limit
              /pa_add /add_vec_int. f_equal. }
    assert (HQ3s1 : Q3 !!! Regidx Rs1 = i_addr ip 0)
      by (rewrite /Q3 upd_ne; [exact HQ2s1 | nz]).
    assert (HQ3s3 : Q3 !!! Regidx Rs3 = ip)
      by (rewrite /Q3 upd_ne; [exact HQ2s3 | nz]).
    assert (HQ3sp : it_sp m Q3)
      by (rewrite /it_sp /Q3 upd_ne; [exact HQ2sp | nz]).
    (* the five saved registers are the caller's; s4 upward untouched *)
    assert (HQ3thr : it_thr m Q3).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /Q3 upd_ne; [| regne]. rewrite /Q2 upd_ne; [| regne].
      rewrite /Q1 upd_ne; [| regne]. rewrite /Q0 upd_ne; [| regne].
      exact (HP0thr c Hcs N2 N8 N9 N18 N19). }
    assert (Hp18 : add_vec_int (mword_of_int (IT + 0x14) : mword 64) 4
                   = mword_of_int (IT + 0x18)) by pcw.
    iEval (rewrite Hp18) in "Hpc".
    (* ===== +0x18 c.j : into the direct loop's body test ===== *)
    iApply (wp_cj_s_sconf (mword_of_int (IT + 0x18))
              (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0")))
              Q3 (K - 6)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi18").
    iIntros (CID11x Hq11x). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt20 : add_vec (mword_of_int (IT + 0x18) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 4 : mword 11) ('b"0"))))
                     = mword_of_int (IT + 0x20)) by pcw.
    iEval (rewrite Htgt20) in "Hpc".
    (* the loop's state at cursor 0: the map is [bm] itself *)
    assert (Hz0 : bm_dir_zeroed bm 0 = bm) by apply bm_dir_zeroed_0.
    assert (Hf0 : used ∖ bm_dir_freed bm 0 = used)
      by (rewrite bm_dir_freed_0 difference_empty_L; reflexivity).
    iDestruct (bm_paidS_intro γ bmapstart crb u Sb e0 Hcrb with "Hop") as "Hpaid".
    iAssert (it_dir_state γ γfs ip bm data cov logstart bmapstart size used
                          bn crb Sb e0 u 0)
      with "[Hmap Hblks Hbmr Hpaid]" as "Hst".
    { iApply (it_dir_state_close with "[Hmap] [Hblks] [Hbmr] Hpaid");
        [ rewrite Hz0; iExact "Hmap"
        | rewrite Hz0; iExact "Hblks"
        | rewrite Hf0; iExact "Hbmr" ]. }
    (* the direct loop needs two of the three slots; the third is parked
       until the indirect arm's bread wants it *)
    assert (H3 : (3 = 2 + 1)%nat) by lia.
    iEval (rewrite H3 bslots_op) in "Hsl".
    iDestruct "Hsl" as "[Hsl Hslp]".
    iDestruct (cpu_own_transport CID CID11x 0 eb (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID CID11x eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CID11x eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iApply (it_dloop (CID0 := CID11x) γs j γl γu γd γk pd pav pu bn γ γfs
              cov logstart bmapstart size dev used ip bm data
              pidv dq dqd dqb crb Sb e0 u m K C b eb NDIRECT lks
              HK Hgeom Hsize Hbm0 Hbmcov Hbmlog Hwf Hrange Hblen Hj Hgl
              0%nat Q3 ltac:(unfold NDIRECT; lia) ltac:(lia)
              HQ3sp HQ3thr HQ3s1 HQ3s2 HQ3s3 Hlkbelow
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hprocs
                    Hppid Hidev Hsbb Hdevi Hdgeom Hdlock Hsl Hst").
    (* ===== the direct loop is done: +0x32 onwards ===== *)
    iIntros (CID12x Hq12x Mx) "%HMsp %HMthr %HMs3 Hcg Hcnt Hextc Hextm Hpc Hppid
                               Hidev Hsbb Hsl Hst".
    iPoseProof (iti_32 with "Htext") as "Hi32".
    iPoseProof (iti_36 with "Htext") as "Hi36".
    iDestruct (it_dir_state_open with "Hst") as "(Hmap & Hblks & Hbmr & Hpaid)".
    pose proof (blkmap_wf_dir_len _ _ _ Hwf) as Hdirlen.
    pose proof (blkmap_wf_ent_len _ _ _ Hwf) as Hentlen.
    assert (Hzlen : length (bm_dir (bm_dir_zeroed bm NDIRECT)) = NDIRECT)
      by (rewrite bm_dir_zeroed_len; [exact Hdirlen | lia]).
    iDestruct (inode_map_ind_acc γfs ip (bm_dir_zeroed bm NDIRECT) Hzlen
                 with "Hmap") as "(Hindcell & Hindres & Hmapback)".
    assert (Hindz : bm_ind (bm_dir_zeroed bm NDIRECT) = bm_ind bm)
      by (rewrite /bm_dir_zeroed; reflexivity).
    iEval (rewrite Hindz) in "Hindcell".
    (* ===== +0x32 lw a1,128(s3) : a1 := ip->addrs[NDIRECT] ===== *)
    assert (Hica0 : add_vec (rget Mx Rs3)
                      (sign_extend' 64 (mword_of_int 128 : mword 12))
                    = i_addr ip NDIRECT).
    { rgne. rewrite HMs3 it_dir_limit /pa_add /add_vec_int. f_equal. }
    iEval (rewrite -Hica0) in "Hindcell".
    iApply (wp_lw_s_sconf (mword_of_int (IT + 0x32)) Ra1 Rs3
              (mword_of_int 128 : mword 12) Mx (K - 6)%nat
              (bm_ind bm : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi32 Hindcell").
    iIntros (CID13x Hq13x) "Hcg Hpc Hindcell".
    iEval (rewrite Hica0) in "Hindcell".
    set (R0 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (bm_ind bm : mword 32))]> Mx).
    assert (HR0a1 : R0 !!! Regidx Ra1
                    = sign_extend' 64 (bm_ind bm : mword 32))
      by (rewrite /R0; apply upd_eq).
    assert (HR0s3 : R0 !!! Regidx Rs3 = ip)
      by (rewrite /R0 upd_ne; [exact HMs3 | nz]).
    assert (HR0sp : it_sp m R0)
      by (rewrite /it_sp /R0 upd_ne; [exact HMsp | nz]).
    assert (HR0thr : it_thr m R0).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /R0 upd_ne; [| regne]. exact (HMthr c Hcs N2 N8 N9 N18 N19). }
    assert (Hp36 : add_vec_int (mword_of_int (IT + 0x32) : mword 64) 4
                   = mword_of_int (IT + 0x36)) by pcw.
    iEval (rewrite Hp36) in "Hpc".
    (* the map at this point is the direct-zeroed one; put the indirect
       cell back so either path has a whole [inode_map] to work from *)
    iDestruct ("Hmapback" $! (bm_ind bm) (bm_ent (bm_dir_zeroed bm NDIRECT))
                 with "[Hindcell] Hindres") as "Hmap";
      [ rewrite -Hindz; iExact "Hindcell" |].
    assert (Hmid : MkBlkmap (bm_dir (bm_dir_zeroed bm NDIRECT))
                     (bm_ind bm) (bm_ent (bm_dir_zeroed bm NDIRECT))
                   = bm_dir_zeroed bm NDIRECT)
      by (rewrite /bm_dir_zeroed; reflexivity).
    iEval (rewrite Hmid) in "Hmap".
    (* ===== +0x36 c.bnez a1 : is there an indirect block? ===== *)
    destruct (decide (bv_unsigned (bm_ind bm : mword 32) = 0)) as [Hnoind|Hyesind].
    - (* ---------- NO indirect block: straight to the tail ----------
         THIS is what blkmap_wf's third clause is for: no indirect block
         means no entries, so the direct-zeroed map IS bm_empty and there
         is nothing left to free. *)
      pose proof (blkmap_wf_no_ind cov logstart bm Hwf Hnoind) as Hentzero.
      assert (Hisempty : bm_dir_zeroed bm NDIRECT = bm_empty).
      { rewrite /bm_dir_zeroed /bm_empty.
        rewrite (drop_ge (bm_dir bm) NDIRECT); [| lia].
        rewrite app_nil_r Hentzero. f_equal.
        apply bv_eq. rewrite Hnoind. reflexivity. }
      assert (Hblkempty : bm_blocks bm = bm_dir_freed bm NDIRECT).
      { rewrite (bm_blocks_split bm Hdirlen Hentlen).
        assert (He0 : bm_ent_freed bm NINDIRECT = ∅).
        { apply set_eq. intros z. rewrite bm_ent_freed_spec.
          split; [|intros Hc; exfalso; exact (not_elem_of_empty _ Hc)].
          intros (Hnz & q & Hq & Hz). exfalso. apply Hnz. rewrite -Hz Hentzero.
          rewrite lookup_total_replicate_2; [reflexivity | lia]. }
        rewrite He0 Hnoind difference_diag_L !union_empty_r_L. reflexivity. }
      (* the test is BNE, so "no indirect block" FALLS THROUGH to the tail *)
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (IT + 0x36))
                (mword_of_int 13 : mword 8) (Cregidx (mword_of_int 3)) Ra1
                R0 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HR0a1; exact (it_neqz_false _ Hnoind))
                with "Hcg Hpc Hi36").
      iIntros (CID14x Hq14x) "Hcg Hpc".
      assert (Hp38 : add_vec_int (mword_of_int (IT + 0x36) : mword 64) 2
                     = mword_of_int (IT + 0x38)) by pcw.
      iEval (rewrite Hp38) in "Hpc".
      iEval (rewrite Hisempty) in "Hmap".
      iEval (rewrite Hisempty) in "Hblks".
      iEval (rewrite -Hblkempty) in "Hbmr".
      iDestruct (bm_paidS_elim with "Hpaid") as (wq n0 Sq)
        "(%Hqsub & %Hqbm & %Hwqc & %Hn0 & Hop)".
      (* iupdate wants a successor; bm_paidS guarantees at least S u *)
      destruct n0 as [|n1]; [exfalso; unfold it_entry in Hn0; lia|].
      (* the tail flush's credit travels through the loop's growth: the
         running set only grew, and [log_credit] is set-monotone exactly as
         the pure claim it generalises is (fs-log.md §G.20) *)
      iPoseProof (log_credit_mono γ cru Sb Sq e0 (IBLOCK inum inodestart) Hqsub
                    with "Hcru") as "#Hcru1".
      iDestruct (cpu_own_transport CID12x CID14x 0 eb (proc_addr j) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID12x CID14x eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID12x CID14x eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CID14x)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (it_tail (CID0 := CID14x) γs j γl γu γd γk pd pav pu bn γ γfs γi
                cov logstart bmapstart inodestart size nib dev used ip inum
                dn dn0 bm
                n1 Sq cru e0 pidv dq dqd dqn dqb dqs m R0 K C b eb lks
                HK
                Hgeom Hist Hicov Hilog Hnib Hdtnz Hstab Hnlk Hj Hgl HR0sp HR0thr HR0s3
                Hlkbelow
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hprocs
                      Hframe Hppid Hidev Hinum Hsbb Hsbi
                      Hmeta Hmap Hblks Hbmr Hireg Hdn Hdevi Hdgeom Hdlock
                      [Hsl Hslp] Hcru1 Hop [Hcont]").
      { assert (H3b : (3 = 2 + 1)%nat) by lia.
        rewrite H3b bslots_op. iSplitL "Hsl"; [iExact "Hsl" | iExact "Hslp"]. }
      (* it_tail's continuation IS itrunc's postcondition, except that the
         budget arrives as a concrete level and the contract states a range *)
      rewrite /it_cont.
      iIntros (CIDz) "%Hch". iSpecialize ("Hcont" $! CIDz with "[%]");
        [exact Hch|].
      iIntros (mf) "%Hcs Hsie Hcnt Hextc Hextm Hpc Hppid Hidev Hinum Hsbb Hsbi
                    Hmeta Hmap Hblks Hbmr Hdn Hsl Hop".
      iApply ("Hcont" $! mf with "[%] Hsie Hcnt Hextc Hextm Hpc Hppid Hidev Hinum
                                  Hsbb Hsbi Hmeta Hmap Hblks Hbmr Hdn Hsl
                                  [Hop]");
        [exact Hcs |].
      (* THE WIDENING, and the determinate membership.  The tail hands back
         a CONCRETE level and a CONCRETE set; the contract states a range and
         a growth.  [S n1 <= it_entry crb u] is what the [crb] guard on
         [bm_paidS]'s unpaid disjunct bought -- at [crb = true] it pins
         [n1 = u], which is what makes create's zero-spend fail arm close. *)
      iExists wq, (if cru then S n1 else n1), (Sq ∪ {[IBLOCK inum inodestart]}).
      iSplitR; [iPureIntro; exact (it_sub_union_l _ _ _ Hqsub)|].
      iSplitR; [iPureIntro; exact (it_in_union_sing _ _)|].
      (* THE REPORT TRAVELS THROUGH THE TAIL'S OWN GROWTH (G-4c): the
         bitmap membership the loops established is still there after the
         flush, because the set only grew. *)
      iSplitR; [iPureIntro; intros Hw; apply elem_of_union_l; exact (Hqbm Hw)|].
      iSplitR; [iPureIntro; exact Hwqc|].
      iSplitR; [iPureIntro; unfold it_entry, it_spend, it_iu, it_bm in *;
                destruct crb, cru, wq; simpl in *; lia|].
      iExact "Hop".
    - (* ---------- there is one: take the arm ---------- *)
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (IT + 0x36))
                (mword_of_int 13 : mword 8) (Cregidx (mword_of_int 3)) Ra1
                R0 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HR0a1; exact (it_neqz_true _ Hyesind))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi36").
      iApply bi.later_intro. iIntros (CID14y Hq14y) "Hcg Hpc".
      assert (Htgt50 : add_vec (mword_of_int (IT + 0x36) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 13 : mword 8) ('b"0"))))
                       = mword_of_int (IT + 0x50)) by pcw.
      iEval (rewrite Htgt50) in "Hpc".
      iDestruct (inode_blocks_to_ent_res γfs bm data Hdirlen Hentlen
                   with "Hblks") as "Hres0".
      rewrite /it_frame.
      iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6)".
      iDestruct (cpu_own_transport CID12x CID14y 0 eb (proc_addr j) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID12x CID14y eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID12x CID14y eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      iApply (it_iarm (CID0 := CID14y) γs j γl γu γd γk pd pav pu bn γ γfs
                cov logstart bmapstart size dev used ip bm data
                pidv dq dqd dqb crb Sb e0 u m R0 K C b eb lks
                HK Hgeom Hsize Hbm0 Hbmcov Hbmlog Hwf Hrange Hblen Hyesind
                Hj Hgl HR0sp HR0thr HR0s3 HR0a1 Hlkbelow
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hprocs
                      Hppid Hidev Hsbb Hdevi Hdgeom Hdlock [Hf6]
                      [Hsl Hslp] Hmap Hres0 Hbmr Hpaid").
      { iExact "Hf6". }
      { assert (H3c : (3 = 2 + 1)%nat) by lia.
        rewrite H3c bslots_op. iSplitL "Hsl"; [iExact "Hsl" | iExact "Hslp"]. }
      (* ===== the arm rejoins at +0x38: hand on to the tail ===== *)
      rewrite /it_armexit.
      iIntros (CID15y Hq15y Mz) "%HMzsp %HMzthr %HMzs3 Hcg Hcnt Hextc Hextm Hpc Hppid
                                 Hidev Hsbb Hslot6 Hmap Hblks Hbmr Hsl Hpaid".
      iDestruct (bm_paidS_elim with "Hpaid") as (wr n2 Sr)
        "(%Hrsub & %Hrbm & %Hwrc & %Hn2 & Hop)".
      destruct n2 as [|n3]; [exfalso; unfold it_entry in Hn2; lia|].
      iPoseProof (log_credit_mono γ cru Sb Sr e0 (IBLOCK inum inodestart) Hrsub
                    with "Hcru") as "#Hcru2".
      iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CID15y)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (it_tail (CID0 := CID15y) γs j γl γu γd γk pd pav pu bn γ γfs γi
                cov logstart bmapstart inodestart size nib dev used ip inum
                dn dn0 bm
                n3 Sr cru e0 pidv dq dqd dqn dqb dqs m Mz K C b eb lks
                HK
                Hgeom Hist Hicov Hilog Hnib Hdtnz Hstab Hnlk Hj Hgl HMzsp HMzthr HMzs3
                Hlkbelow
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hprocs
                      [Hf1 Hf2 Hf3 Hf4 Hf5 Hslot6] Hppid Hidev Hinum Hsbb
                      Hsbi Hmeta Hmap Hblks Hbmr Hireg Hdn Hdevi Hdgeom Hdlock
                      Hsl Hcru2 Hop [Hcont]").
      { rewrite /it_frame. iFrame "Hf1 Hf2 Hf3 Hf4 Hf5". iExact "Hslot6". }
      rewrite /it_cont.
      iIntros (CIDw) "%Hchw". iSpecialize ("Hcont" $! CIDw with "[%]");
        [exact Hchw|].
      iIntros (mf) "%Hcsw Hsie Hcnt Hextc Hextm Hpc Hppid Hidev Hinum Hsbb Hsbi
                    Hmeta Hmap Hblks Hbmr Hdn Hsl Hop".
      iApply ("Hcont" $! mf with "[%] Hsie Hcnt Hextc Hextm Hpc Hppid Hidev Hinum
                                  Hsbb Hsbi Hmeta Hmap Hblks Hbmr Hdn Hsl
                                  [Hop]");
        [exact Hcsw |].
      iExists wr, (if cru then S n3 else n3), (Sr ∪ {[IBLOCK inum inodestart]}).
      iSplitR; [iPureIntro; exact (it_sub_union_l _ _ _ Hrsub)|].
      iSplitR; [iPureIntro; exact (it_in_union_sing _ _)|].
      iSplitR; [iPureIntro; intros Hw; apply elem_of_union_l; exact (Hrbm Hw)|].
      iSplitR; [iPureIntro; exact Hwrc|].
      iSplitR; [iPureIntro; unfold it_entry, it_spend, it_iu, it_bm in *;
                destruct crb, cru, wr; simpl in *; lia|].
      iExact "Hop".
  Qed.

  (* ===================================================================== *)
  (*  THE COUNTED SEAL, derived at the [log_op] existential's OWN WITNESS   *)
  (*  (fs-icache.md section 18; [ProofIupdate.wp_iupdate_sconf], same       *)
  (*  shape).  [log_op γ (S (S u))] IS [∃ Sb, log_opS γ (S (S u)) Sb], and  *)
  (*  [S (S u) = it_entry false u] definitionally, so the counted form      *)
  (*  destructs its reservation, runs the gen walk UNCREDITED at whatever   *)
  (*  set was hiding there, and forgets the grown set again on the way out. *)
  (*  Deriving at [Sb := ∅] instead would force every counted caller to     *)
  (*  prove its set empty, which is both false and unnecessary.             *)
  (*                                                                        *)
  (*  The range collapses exactly: at [crb = cru = false] the gen bounds     *)
  (*  are [S (S u) - 2 <= u'] and [u' + 1 <= S (S u)], i.e. the landed       *)
  (*  [u <= u' <= S u].                                                     *)
  (* ===================================================================== *)
  Lemma wp_itrunc_sconf `{GEN : GenId} `{CID : CpuId}       (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z)
      (dev : mword 32) (used : gset Z)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) (u : nat)
      (pidv : mword 32) (dq dqd dqn dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool) (lks : gset string)
    : wp_itrunc_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs γi
                           cov logstart bmapstart inodestart nib size dev used
                           ip inum dn dn0 bm data u
                           pidv dq dqd dqn dqb dqs m K eb C b lks.
  Proof.
    cbv beta delta [wp_itrunc_sconf_body].
    intros pcE pj ret_tgt HK Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist Hicov Hilog
           Hnib Hdtnz Hstab Hnlk Hwf Hbelow Hblen Hadr Hj Hgl Ha0 Hlkbelow.
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio #Hlctx Hidev Hinum Hmeta Hmap
              Hblks Hsbb Hsbi Hbmr #Hireg Hdn Hppid #Hprocs #Hdevi
              #Hdgeom #Hdlock Hsl Hop Hcont".
    (* THE WITNESS: the set the counted reservation was hiding, and -- one
       tier down (fs-log.md §G.20) -- the birth epoch it was hiding too.
       Both are opened here and neither reaches a counted caller: the
       credit at [cru = false] is [emp]. *)
    iDestruct "Hop" as (Sb0) "Hop".
    iDestruct (log_opS_named with "Hop") as (e0) "Hop".
    iPoseProof (log_credit_own γ false Sb0 e0 (IBLOCK inum inodestart)
                  ltac:(discriminate)) as "#Hcru".
    iApply (wp_itrunc_gen γs j γl γu γd γk pd pav pu bn γ γfs γi
              cov logstart bmapstart inodestart nib size dev used
              ip inum dn dn0 bm data u Sb0 false false e0
              pidv dq dqd dqn dqb dqs m K eb C b lks
              HK ltac:(discriminate)
              Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist Hicov Hilog
              Hnib Hdtnz Hstab Hnlk Hwf Hbelow Hblen Hadr Hj Hgl Ha0 Hlkbelow
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hidev Hinum Hmeta Hmap
                    Hblks Hsbb Hsbi Hbmr Hireg Hdn Hppid Hprocs Hdevi
                    Hdgeom Hdlock Hsl Hcru Hop [Hcont]").
    all: try lkbelow.
    iEval (rewrite /wp_next).
    iIntros (CIDf) "%Hchain".
    iIntros (mf) "%Hcs Hcg Hcnt Hextc Hextm Hpc Hppid Hidev Hinum Hsbb Hsbi
                  Hmeta Hmap Hblks Hbmr Hdn Hsl Hop".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [exact Hchain|].
    iDestruct "Hop" as (wf u' Sb') "(_ & _ & _ & _ & %Hbnd & Hop)".
    iApply ("Hcont" $! mf with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid Hidev Hinum
                     Hsbb Hsbi Hmeta Hmap Hblks Hbmr Hdn Hsl [Hop]");
      [exact Hcs |].
    iExists u'. iSplitR.
    { iPureIntro. unfold it_entry, it_spend, it_iu, it_bm in Hbnd.
      destruct wf; simpl in Hbnd; lia. }
    iApply (log_opS_op with "Hop").
  Qed.

End ItruncMain.

End ItruncProof.
