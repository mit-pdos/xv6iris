(* ProofStati.v -- stati over the SIE-agnostic sconf world.

     void stati(struct inode *ip, struct stat *st) {
       st->dev = ip->dev;  st->ino = ip->inum;  st->type = ip->type;
       st->nlink = ip->nlink;  st->size = ip->size;
     }

   46 bytes, 18 instructions: a 2-slot frame and five load/store pairs, all
   through a5.  No branch, no call, no lock, no ghost move.

   The only non-frame content is the EXTENSION bookkeeping.  Four of the five
   pairs load and store at the SAME width, so the extension the load applied
   is undone by the store's truncation ([trunc32_sext64], and its halfword
   twin [trunc16_sext64] below -- the one lemma this file has to prove, and
   [RiscvExtras.trunc32_sext64]'s proof transposed to width 2).  The fifth
   pair does not: [lwu a5,76(a0)] followed by [sd a5,16(a1)] widens a 4-byte
   [uint] into an 8-byte field, so [st->size] is the ZERO-extension of
   [ip->size] and the AST's [is_unsigned = true] is load-bearing there and
   only there. *)
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
Require Import RegFile WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeHalf.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import CodeStati.
Require Import SpecStati.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Set Printing Depth 40.

(* [RiscvExtras.trunc32_sext64] at width 2: the round trip an [lh] feeding an
   [sh] performs.  (It belongs beside [WpSmodeHalf.trunc16]; kept here so
   nothing below it has to be rebuilt.) *)
Lemma trunc16_sext64 (w : mword 16) : trunc16 (sign_extend' 64 w) = w.
Proof.
  apply bv_eq. unfold trunc16. rewrite autocast_id.
  unfold subrange_vec_dec, to_word_idx, to_word, get_word,
         MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (Z.sub (Z.mul 2 8) 1 - 0 + 1)) with 16%N.
  rewrite (bv_wrap_bv_wrap 16 64 _ ltac:(lia)).
  unfold bv_signed. rewrite bv_wrap_swrap.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Module StatiProof : STATI.

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac stidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* the two registers the frame saves *)
Definition sti_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition sti_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))).

Section ProofStatiMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_stati_sconf
      (mm : regfile)
      (ip st : mword 64)
      (dev inum : mword 32) (dn : dinode)
      (dev0 ino0 : mword 32) (ty0 nl0 : mword 16) (sz0 : mword 64)
      (K : nat) (dqd dqn : dfrac) (b : bool) (p : mword 64)
    : wp_stati_sconf_body mm ip st dev inum dn dev0 ino0 ty0 nl0 sz0
                          K dqd dqn b p.
  Proof.
    cbv beta delta [wp_stati_sconf_body].
    intros pcE ret_tgt HK Ha0 Ha1.
    pose proof HK as HK'. 
    iIntros "Hcg #Htext Hpc Hidev Hinum Hmeta Hstat Hcont".
    iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
    iDestruct "Hstat" as "(Hsdev & Hsino & Hsty & Hsnl & Hssz)".
    iEval (rewrite /i_dev) in "Hidev".
    iEval (rewrite /i_inum) in "Hinum".
    iEval (rewrite /i_type) in "Hity".
    iEval (rewrite /i_nlink) in "Hinl".
    iEval (rewrite /i_size) in "Hisz".
    iEval (rewrite /st_dev) in "Hsdev".
    iEval (rewrite /st_ino) in "Hsino".
    iEval (rewrite /st_type) in "Hsty".
    iEval (rewrite /st_nlink) in "Hsnl".
    iEval (rewrite /st_size) in "Hssz".
    iPoseProof (sti_00 with "Htext") as "Hi00".
    iPoseProof (sti_02 with "Htext") as "Hi02".
    iPoseProof (sti_04 with "Htext") as "Hi04".
    iPoseProof (sti_06 with "Htext") as "Hi06".
    iPoseProof (sti_08 with "Htext") as "Hi08".
    iPoseProof (sti_0a with "Htext") as "Hi0a".
    iPoseProof (sti_0c with "Htext") as "Hi0c".
    iPoseProof (sti_0e with "Htext") as "Hi0e".
    iPoseProof (sti_10 with "Htext") as "Hi10".
    iPoseProof (sti_14 with "Htext") as "Hi14".
    iPoseProof (sti_18 with "Htext") as "Hi18".
    iPoseProof (sti_1c with "Htext") as "Hi1c".
    iPoseProof (sti_20 with "Htext") as "Hi20".
    iPoseProof (sti_24 with "Htext") as "Hi24".
    iPoseProof (sti_26 with "Htext") as "Hi26".
    iPoseProof (sti_28 with "Htext") as "Hi28".
    iPoseProof (sti_2a with "Htext") as "Hi2a".
    iPoseProof (sti_2c with "Htext") as "Hi2c".
    (* ===== +0x00 c.addi sp,sp,-16 ===== *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1 : mword 64) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) mm K 2 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (mm !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    assert (HR1sp : sti_sp mm R1) by (rewrite /sti_sp /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v1) "Hf1". iDestruct "S2" as (v2) "Hf2".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (mm !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (mm !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb1) in "Hf1". iEval (rewrite -Hb2) in "Hf2".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2
                    = mword_of_int (KernelSyms.stati + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 / +0x04 : the two saves ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.stati + 0x02))
              (mword_of_int 1 : mword 6) Rra R1 (K - 2)%nat v1 b
              with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.stati + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.stati + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.stati + 0x04))
              (mword_of_int 0 : mword 6) Rs0 R1 (K - 2)%nat v2 b
              with "Hcg Hpc Hi04 Hf2").
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.stati + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.stati + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (mm !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (mm !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hf2".
    (* ===== +0x06 c.addi4spn s0,sp,16 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.stati + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) Rs0
              R1 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    assert (HR2sp : sti_sp mm R2)
      by (rewrite /sti_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2a0 : R2 !!! Regidx Ra0 = ip)
      by (rewrite /R2 upd_ne; [| nz]; rewrite /R1 upd_ne; [exact Ha0 | nz]).
    assert (HR2a1 : R2 !!! Regidx Ra1 = st)
      by (rewrite /R2 upd_ne; [| nz]; rewrite /R1 upd_ne; [exact Ha1 | nz]).
    assert (HR2thr : sti_thr mm R2).
    { intros c Hcs N2 N8.
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.stati + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.stati + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    (* ===== +0x08 c.lw a5,0(a0) : ip->dev ===== *)
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.stati + 0x08)) Ra5 Ra0
              (mword_of_int 0 : mword 12) R2 (K - 2)%nat dev b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi08 [Hidev]").
    { iEval (rgne; rewrite HR2a0). iExact "Hidev". }
    iIntros (CID5 Hq5) "Hcg Hpc Hidev".
    iEval (rgne; rewrite HR2a0) in "Hidev".
    set (R3 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 dev : mword 64)]> R2).
    assert (HR3a5 : R3 !!! Regidx Ra5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R3; apply upd_eq).
    assert (HR3a0 : R3 !!! Regidx Ra0 = ip)
      by (rewrite /R3 upd_ne; [exact HR2a0 | nz]).
    assert (HR3a1 : R3 !!! Regidx Ra1 = st)
      by (rewrite /R3 upd_ne; [exact HR2a1 | nz]).
    assert (HR3sp : sti_sp mm R3)
      by (rewrite /sti_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : sti_thr mm R3).
    { intros c Hcs N2 N8.
      rewrite /R3 upd_ne; [| regne]. exact (HR2thr c Hcs N2 N8). }
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.stati + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.stati + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    (* ===== +0x0a c.sw a5,0(a1) : st->dev ===== *)
    iApply (wp_csw_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (KernelSyms.stati + 0x0a)) Ra5 Ra1
              (mword_of_int 0 : mword 12) R3 (K - 2)%nat dev0 b
              with "Hcg Hpc Hi0a [Hsdev]").
    { iEval (rgne; rewrite HR3a1). iExact "Hsdev". }
    iIntros (CID6 Hq6) "Hcg Hpc Hsdev".
    iEval (rgne; rgne; rewrite HR3a1 HR3a5 trunc32_sext64) in "Hsdev".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.stati + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.stati + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c c.lw a5,4(a0) : ip->inum ===== *)
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.stati + 0x0c)) Ra5 Ra0
              (mword_of_int 4 : mword 12) R3 (K - 2)%nat inum b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0c [Hinum]").
    { iEval (rgne; rewrite HR3a0). iExact "Hinum". }
    iIntros (CID7 Hq7) "Hcg Hpc Hinum".
    iEval (rgne; rewrite HR3a0) in "Hinum".
    set (R4 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 inum : mword 64)]> R3).
    assert (HR4a5 : R4 !!! Regidx Ra5 = (sign_extend' 64 inum : mword 64))
      by (rewrite /R4; apply upd_eq).
    assert (HR4a0 : R4 !!! Regidx Ra0 = ip)
      by (rewrite /R4 upd_ne; [exact HR3a0 | nz]).
    assert (HR4a1 : R4 !!! Regidx Ra1 = st)
      by (rewrite /R4 upd_ne; [exact HR3a1 | nz]).
    assert (HR4sp : sti_sp mm R4)
      by (rewrite /sti_sp /R4 upd_ne; [exact HR3sp | nz]).
    assert (HR4thr : sti_thr mm R4).
    { intros c Hcs N2 N8.
      rewrite /R4 upd_ne; [| regne]. exact (HR3thr c Hcs N2 N8). }
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.stati + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.stati + 0x0e)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== +0x0e c.sw a5,4(a1) : st->ino ===== *)
    iApply (wp_csw_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (KernelSyms.stati + 0x0e)) Ra5 Ra1
              (mword_of_int 4 : mword 12) R4 (K - 2)%nat ino0 b
              with "Hcg Hpc Hi0e [Hsino]").
    { iEval (rgne; rewrite HR4a1). iExact "Hsino". }
    iIntros (CID8 Hq8) "Hcg Hpc Hsino".
    iEval (rgne; rgne; rewrite HR4a1 HR4a5 trunc32_sext64) in "Hsino".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.stati + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.stati + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ===== +0x10 lh a5,68(a0) : ip->type ===== *)
    iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.stati + 0x10)) Ra5 Ra0
              (mword_of_int 68 : mword 12) R4 (K - 2)%nat (di_type dn : mword 16) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi10 [Hity]").
    { iEval (rgne; rewrite HR4a0). iExact "Hity". }
    iIntros (CID9 Hq9) "Hcg Hpc Hity".
    iEval (rgne; rewrite HR4a0) in "Hity".
    set (R5 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (di_type dn : mword 16) : mword 64)]> R4).
    assert (HR5a5 : R5 !!! Regidx Ra5
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /R5; apply upd_eq).
    assert (HR5a0 : R5 !!! Regidx Ra0 = ip)
      by (rewrite /R5 upd_ne; [exact HR4a0 | nz]).
    assert (HR5a1 : R5 !!! Regidx Ra1 = st)
      by (rewrite /R5 upd_ne; [exact HR4a1 | nz]).
    assert (HR5sp : sti_sp mm R5)
      by (rewrite /sti_sp /R5 upd_ne; [exact HR4sp | nz]).
    assert (HR5thr : sti_thr mm R5).
    { intros c Hcs N2 N8.
      rewrite /R5 upd_ne; [| regne]. exact (HR4thr c Hcs N2 N8). }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.stati + 0x10) : mword 64) 4
                    = mword_of_int (KernelSyms.stati + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 sh a5,8(a1) : st->type ===== *)
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (KernelSyms.stati + 0x14)) Ra5 Ra1
              (mword_of_int 8 : mword 12) R5 (K - 2)%nat ty0 b
              with "Hcg Hpc Hi14 [Hsty]").
    { iEval (rgne; rewrite HR5a1). iExact "Hsty". }
    iIntros (CID10 Hq10) "Hcg Hpc Hsty".
    iEval (rgne; rgne; rewrite HR5a1 HR5a5 trunc16_sext64) in "Hsty".
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.stati + 0x14) : mword 64) 4
                    = mword_of_int (KernelSyms.stati + 0x18)) by pcw.
    iEval (rewrite Hpp18) in "Hpc".
    (* ===== +0x18 lh a5,74(a0) : ip->nlink ===== *)
    iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.stati + 0x18)) Ra5 Ra0
              (mword_of_int 74 : mword 12) R5 (K - 2)%nat (di_nlink dn : mword 16) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi18 [Hinl]").
    { iEval (rgne; rewrite HR5a0). iExact "Hinl". }
    iIntros (CID11 Hq11) "Hcg Hpc Hinl".
    iEval (rgne; rewrite HR5a0) in "Hinl".
    set (R6 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (di_nlink dn : mword 16) : mword 64)]> R5).
    assert (HR6a5 : R6 !!! Regidx Ra5
                    = (sign_extend' 64 (di_nlink dn : mword 16) : mword 64))
      by (rewrite /R6; apply upd_eq).
    assert (HR6a0 : R6 !!! Regidx Ra0 = ip)
      by (rewrite /R6 upd_ne; [exact HR5a0 | nz]).
    assert (HR6a1 : R6 !!! Regidx Ra1 = st)
      by (rewrite /R6 upd_ne; [exact HR5a1 | nz]).
    assert (HR6sp : sti_sp mm R6)
      by (rewrite /sti_sp /R6 upd_ne; [exact HR5sp | nz]).
    assert (HR6thr : sti_thr mm R6).
    { intros c Hcs N2 N8.
      rewrite /R6 upd_ne; [| regne]. exact (HR5thr c Hcs N2 N8). }
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.stati + 0x18) : mword 64) 4
                    = mword_of_int (KernelSyms.stati + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== +0x1c sh a5,10(a1) : st->nlink ===== *)
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (KernelSyms.stati + 0x1c)) Ra5 Ra1
              (mword_of_int 10 : mword 12) R6 (K - 2)%nat nl0 b
              with "Hcg Hpc Hi1c [Hsnl]").
    { iEval (rgne; rewrite HR6a1). iExact "Hsnl". }
    iIntros (CID12 Hq12) "Hcg Hpc Hsnl".
    iEval (rgne; rgne; rewrite HR6a1 HR6a5 trunc16_sext64) in "Hsnl".
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.stati + 0x1c) : mword 64) 4
                    = mword_of_int (KernelSyms.stati + 0x20)) by pcw.
    iEval (rewrite Hpp20) in "Hpc".
    (* ===== +0x20 lwu a5,76(a0) : ip->size, ZERO-extended ===== *)
    iApply (wp_lwu_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.stati + 0x20)) Ra5 Ra0
              (mword_of_int 76 : mword 12) R6 (K - 2)%nat (di_size dn : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi20 [Hisz]").
    { iEval (rgne; rewrite HR6a0). iExact "Hisz". }
    iIntros (CID13 Hq13) "Hcg Hpc Hisz".
    iEval (rgne; rewrite HR6a0) in "Hisz".
    set (R7 := <[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (di_size dn : mword 32) : mword 64)]> R6).
    assert (HR7a5 : R7 !!! Regidx Ra5
                    = (zero_extend' 64 (di_size dn : mword 32) : mword 64))
      by (rewrite /R7; apply upd_eq).
    assert (HR7a1 : R7 !!! Regidx Ra1 = st)
      by (rewrite /R7 upd_ne; [exact HR6a1 | nz]).
    assert (HR7sp : sti_sp mm R7)
      by (rewrite /sti_sp /R7 upd_ne; [exact HR6sp | nz]).
    assert (HR7thr : sti_thr mm R7).
    { intros c Hcs N2 N8.
      rewrite /R7 upd_ne; [| regne]. exact (HR6thr c Hcs N2 N8). }
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.stati + 0x20) : mword 64) 4
                    = mword_of_int (KernelSyms.stati + 0x24)) by pcw.
    iEval (rewrite Hpp24) in "Hpc".
    (* ===== +0x24 c.sd a5,16(a1) : st->size (8 bytes) ===== *)
    iApply (wp_csd_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (KernelSyms.stati + 0x24)) Ra5 Ra1
              (mword_of_int 16 : mword 12) R7 (K - 2)%nat sz0 b
              with "Hcg Hpc Hi24 [Hssz]").
    { iEval (rgne; rewrite HR7a1). iExact "Hssz". }
    iIntros (CID14 Hq14) "Hcg Hpc Hssz".
    iEval (rgne; rgne; rewrite HR7a1 HR7a5) in "Hssz".
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.stati + 0x24) : mword 64) 2
                    = mword_of_int (KernelSyms.stati + 0x26)) by pcw.
    iEval (rewrite Hpp26) in "Hpc".
    (* ===== +0x26 / +0x28 : the two restores ===== *)
    assert (Hc1 : add_vec (R7 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (mm !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HR7sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc2 : add_vec (R7 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (mm !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HR7sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.stati + 0x26))
              (mword_of_int 1 : mword 6) Rra R7 (K - 2)%nat
              (mm !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi26 [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID15 Hq15) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra : mword 64)]> R7).
    assert (HP1sp : sti_sp mm P1)
      by (rewrite /sti_sp /P1 upd_ne; [exact HR7sp | nz]).
    assert (HP1thr : sti_thr mm P1).
    { intros c Hcs N2 N8.
      rewrite /P1 upd_ne; [| regne]. exact (HR7thr c Hcs N2 N8). }
    assert (HP1ra : P1 !!! Regidx Rra = (mm !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.stati + 0x26) : mword 64) 2
                    = mword_of_int (KernelSyms.stati + 0x28)) by pcw.
    iEval (rewrite Hpp28) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.stati + 0x28))
              (mword_of_int 0 : mword 6) Rs0 P1 (K - 2)%nat
              (mm !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi28 [Hf2]").
    { iEval (rewrite HP1sp -HR7sp Hc2). iExact "Hf2". }
    iIntros (CID16 Hq16) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -HR7sp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : sti_sp mm P2)
      by (rewrite /sti_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : sti_thr mm P2).
    { intros c Hcs N2 N8.
      rewrite /P2 upd_ne; [| regne]. exact (HP1thr c Hcs N2 N8). }
    assert (HP2ra : P2 !!! Regidx Rra = (mm !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.stati + 0x28) : mword 64) 2
                    = mword_of_int (KernelSyms.stati + 0x2a)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    (* ===== +0x2a c.addi sp,sp,16 : pop ===== *)
    assert (Hwv : add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))
                  = (mm !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP2sp. apply bv_eq.
      rewrite !add_vec64_unsigned.
      rewrite bv_wrap_add_idemp_l.
      assert (Hz : bv_unsigned (sign_extend' 64
                     (sign_extend' 12 (mword_of_int 48 : mword 6)) : mword 64)
                   = 18446744073709551600) by (vm_compute; reflexivity).
      assert (Hz2 : bv_unsigned (sign_extend' 64
                      (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)
                    = 16) by (vm_compute; reflexivity).
      rewrite Hz Hz2.
      replace (bv_unsigned (mm !!! Regidx csp_rs1 : mword 64)
                 + 18446744073709551600 + 16)
        with (bv_unsigned (mm !!! Regidx csp_rs1 : mword 64)
                 + 18446744073709551616) by ring.
      rewrite -bv_wrap_add_idemp_r.
      assert (Hm0 : bv_wrap 64 18446744073709551616 = 0)
        by (vm_compute; reflexivity).
      rewrite Hm0 Z.add_0_r.
      apply bv_wrap_small. apply bv_unsigned_in_range. }
    assert (Hpop : (P2 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv HP2sp. unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iAssert (stack_own (KTR := KT1) (mm !!! Regidx csp_rs1 : mword 64) 2)
      with "[Hf1 Hf2]" as "Hstk".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1" |].
      iSplitL "Hf2"; [iExists _; iExact "Hf2" |].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.stati + 0x2a))
              (mword_of_int 16 : mword 6) P2 (K - 2)%nat 2 b Hpop
              with "Hcg Hpc Hi2a Hstk").
    iIntros (CID17 Hq17) "Hcg Hpc".
    set (P3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> P2).
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.stati + 0x2a) : mword 64) 2
                    = mword_of_int (KernelSyms.stati + 0x2c)) by pcw.
    iEval (rewrite Hpp2c) in "Hpc".
    (* ===== +0x2c c.ret ===== *)
    assert (HP3ra : P3 !!! Regidx Rra = (mm !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.stati + 0x2c)) Rra P3 K b
              ltac:(nz) with "Hcg Hpc Hi2c").
    iIntros (CID18 Hq18) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P3 !!! Regidx Rra : mword 64)
                    = ret_pc (mm !!! Regidx Rra : mword 64))
      by (rewrite HP3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (Csp : P3 !!! Regidx csp_rs1 = (mm !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P3 upd_eq; exact Hwv).
    assert (Cs0 : P3 !!! Regidx Rs0 = (mm !!! Regidx Rs0 : mword 64)).
    { rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_eq. reflexivity. }
    assert (Hfin : sti_thr mm P3).
    { intros c Hcs N2 N8.
      rewrite /P3 upd_ne; [| regne]. exact (HP2thr c Hcs N2 N8). }
    assert (Cs1 : P3 !!! Regidx (mword_of_int 9 : mword 5)
                  = (mm !!! Regidx (mword_of_int 9 : mword 5) : mword 64))
      by (apply Hfin; stidx).
    assert (Cs2 : P3 !!! Regidx (mword_of_int 18 : mword 5)
                  = (mm !!! Regidx (mword_of_int 18 : mword 5) : mword 64))
      by (apply Hfin; stidx).
    assert (Cs3 : P3 !!! Regidx (mword_of_int 19 : mword 5)
                  = (mm !!! Regidx (mword_of_int 19 : mword 5) : mword 64))
      by (apply Hfin; stidx).
    assert (Cs4 : P3 !!! Regidx (mword_of_int 20 : mword 5)
                  = (mm !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; stidx).
    assert (Cs5 : P3 !!! Regidx (mword_of_int 21 : mword 5)
                  = (mm !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; stidx).
    assert (Cs6 : P3 !!! Regidx (mword_of_int 22 : mword 5)
                  = (mm !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; stidx).
    assert (Cs7 : P3 !!! Regidx (mword_of_int 23 : mword 5)
                  = (mm !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; stidx).
    assert (Cs8 : P3 !!! Regidx (mword_of_int 24 : mword 5)
                  = (mm !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; stidx).
    assert (Cs9 : P3 !!! Regidx (mword_of_int 25 : mword 5)
                  = (mm !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; stidx).
    assert (Cs10 : P3 !!! Regidx (mword_of_int 26 : mword 5)
                  = (mm !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; stidx).
    assert (Cs11 : P3 !!! Regidx (mword_of_int 27 : mword 5)
                  = (mm !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; stidx).
    iSpecialize ("Hcont" $! CID18 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! P3 with "[%] Hcg Hpc Hidev Hinum
                                 [Hity Himaj Himin Hinl Hisz]
                                 [Hsdev Hsino Hsty Hsnl Hssz]").
    { unfold callee_saved. split_and!; assumption. }
    { rewrite /inode_meta /i_type /i_nlink /i_size. iFrame. }
    { rewrite /stat_at /st_dev /st_ino /st_type /st_nlink /st_size. iFrame. }
  Qed.

End ProofStatiMain.

End StatiProof.
