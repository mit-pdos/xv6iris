(* ProofNamecmp.v -- namecmp over the SIE-agnostic sconf world.

     static int namecmp(const char *s, const char *t) {
       return strncmp(s, t, DIRSIZ);
     }

   22 bytes, 10 instructions: a 2-slot frame, [c.li a2,14], [jal strncmp],
   the epilogue.  namecmp does not even move its arguments -- a0/a1 go
   straight through -- so the machine part of this proof is the frame.

   THE ONE PIECE OF REAL WORK is the bridge from [SpecStrncmp.strncmp_res]
   to the boolean SpecNamecmp exposes, and it is two lemmas:

   - [nc_byte_of_zero], the arithmetic step N1 predicted: strncmp's stop arm
     returns [mword_of_int (bv_unsigned (f k) - bv_unsigned (g k))], and
     that word being zero has to mean [f k = g k].  Both bytes are below
     256, so the difference lies in (-256, 256); [bv_wrap 64] of a negative
     such difference is above 2^64 - 256 and so is never 0, and of a
     non-negative one is itself.

   - [nc_res_iff], which then reads the equivalence off
     [DirentEnc.nc_zero_iff] / [DirentEnc.nc_stop_iff].  Note
     [SpecStrncmp.strncmp_stop] and [DirentEnc.nc_stop] are the SAME
     proposition once [ByteBuf.bb_nonul] and [DirentEnc.NUL] are unfolded --
     N1 transcribed one from the other on purpose -- so no translation is
     needed beyond [unfold].                                                *)
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
Require Import RegFile WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeIntr.
Require Import ByteBuf.
Require Import DirentEnc.
Require Import CodeNamecmp.
Require Import SpecStrncmp.
Require Import SpecNamecmp.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  THE PURE BRIDGE                                                       *)
(* ===================================================================== *)

(* THE OWED ARITHMETIC STEP.  A 64-bit word holding the difference of two
   BYTES is zero only when the bytes are equal: the difference lies in
   (-256, 256), and [bv_wrap 64] is the identity on the non-negative part
   and lands above 2^64 - 256 on the negative part. *)
Lemma nc_byte_of_zero (a b : bv 8) :
  (mword_of_int (bv_unsigned a - bv_unsigned b) : mword 64)
  = (mword_of_int 0 : mword 64) -> a = b.
Proof.
  intros H.
  pose proof (bv_unsigned_in_range 8 a) as Ha.
  pose proof (bv_unsigned_in_range 8 b) as Hb.
  unfold bv_modulus in Ha, Hb.
  change (2 ^ Z.of_N 8)%Z with 256%Z in Ha, Hb.
  apply (f_equal bv_unsigned) in H.
  rewrite !moi64_unsigned in H.
  assert (Hz0 : bv_wrap 64 0 = 0) by (vm_compute; reflexivity).
  rewrite Hz0 in H.
  apply bv_eq.
  destruct (Z.le_gt_cases (bv_unsigned b) (bv_unsigned a)) as [Hle|Hgt].
  - rewrite bv_wrap_small in H; [lia |].
    unfold bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z. lia.
  - exfalso.
    unfold bv_wrap, bv_modulus in H.
    change (2 ^ Z.of_N 64)%Z with (2^64)%Z in H.
    rewrite <- (Z.mod_add (bv_unsigned a - bv_unsigned b) 1 (2^64)) in H
      by (intros Hc; lia).
    rewrite Z.mul_1_l in H.
    rewrite Z.mod_small in H; [lia | lia].
Qed.

(* [SpecStrncmp.strncmp_stop] IS [DirentEnc.nc_stop] -- one unfold apart. *)
Lemma nc_stop_of_strncmp (f g : nat -> bv 8) (n k : nat) :
  strncmp_stop f g n k -> nc_stop f g n k.
Proof.
  unfold strncmp_stop, nc_stop, bb_nonul, NUL. exact (fun H => H).
Qed.

(* THE CONTRACT'S RIGHT-HAND SIDE, read off strncmp's result. *)
Lemma nc_res_iff (f g : nat -> bv 8) (res : mword 64) :
  strncmp_res f g 14 res ->
  (res = (mword_of_int 0 : mword 64) <-> bname 14 f = bname 14 g).
Proof.
  intros Hres. split.
  - intros Hz. apply nc_zero_iff.
    destruct Hres as [[Hn _] | [_ [[kk [Hst Hre]] | [Hrun _]]]].
    + exfalso. lia.
    + left. exists kk.
      pose proof (nc_stop_of_strncmp f g 14 kk Hst) as Hnc.
      split; [exact Hnc |].
      apply nc_byte_of_zero. rewrite <- Hre. exact Hz.
    + right. intros jj Hjj. unfold NUL. exact (Hrun jj Hjj).
  - intros Hbn.
    destruct Hres as [[Hn _] | [_ [[kk [Hst Hre]] | [_ Hre]]]].
    + exfalso. lia.
    + pose proof (nc_stop_of_strncmp f g 14 kk Hst) as Hnc.
      apply (nc_stop_iff f g 14 kk Hnc) in Hbn.
      rewrite Hre Hbn. f_equal. lia.
    + exact Hre.
Qed.

(* ===================================================================== *)
(*  THE FUNCTION                                                          *)
(* ===================================================================== *)

Module NamecmpProof (SC : STRNCMP) : NAMECMP.

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac ncidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* the two registers the frame saves *)
Definition nc_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition nc_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))).

Section ProofNamecmpMain.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {ktf ktg : ktier}.

  Lemma wp_namecmp_sconf
      (mm : regfile) (f g : nat -> bv 8) (K : nat) (dq1 dq2 : dfrac)
      (b : bool) (p : mword 64)
    : wp_namecmp_sconf_body ktf ktg mm f g K dq1 dq2 b p.
  Proof.
    cbv beta delta [wp_namecmp_sconf_body].
    intros pcE s1 s2 ret_tgt HK.
    pose proof HK as HK'. 
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hcont".
    iPoseProof (nci_00 with "Htext") as "Hi00".
    iPoseProof (nci_02 with "Htext") as "Hi02".
    iPoseProof (nci_04 with "Htext") as "Hi04".
    iPoseProof (nci_06 with "Htext") as "Hi06".
    iPoseProof (nci_08 with "Htext") as "Hi08".
    iPoseProof (nci_0a with "Htext") as "Hi0a".
    iPoseProof (nci_0e with "Htext") as "Hi0e".
    iPoseProof (nci_10 with "Htext") as "Hi10".
    iPoseProof (nci_12 with "Htext") as "Hi12".
    iPoseProof (nci_14 with "Htext") as "Hi14".
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
    assert (HR1sp : nc_sp mm R1) by (rewrite /nc_sp /R1 upd_eq; reflexivity).
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
                    = mword_of_int (KernelSyms.namecmp + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 / +0x04 : the two saves ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.namecmp + 0x02))
              (mword_of_int 1 : mword 6) Rra R1 (K - 2)%nat v1 b
              with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.namecmp + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.namecmp + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.namecmp + 0x04))
              (mword_of_int 0 : mword 6) Rs0 R1 (K - 2)%nat v2 b
              with "Hcg Hpc Hi04 Hf2").
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.namecmp + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.namecmp + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (mm !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (mm !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hf2".
    (* ===== +0x06 c.addi4spn s0,sp,16 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.namecmp + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) Rs0
              R1 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    assert (HR2sp : nc_sp mm R2)
      by (rewrite /nc_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2a0 : R2 !!! Regidx Ra0 = (mm !!! Regidx Ra0 : mword 64))
      by (rewrite /R2 upd_ne; [| nz]; rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR2a1 : R2 !!! Regidx Ra1 = (mm !!! Regidx Ra1 : mword 64))
      by (rewrite /R2 upd_ne; [| nz]; rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR2thr : nc_thr mm R2).
    { intros c Hcs N2 N8.
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.namecmp + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.namecmp + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    (* ===== +0x08 c.li a2,14 -- THE DIRSIZ ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.namecmp + 0x08)) Ra2
              (mword_of_int 14 : mword 6) (mword_of_int (Z.of_nat 14) : mword 64)
              R2 (K - 2)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (R3 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int (Z.of_nat 14) : mword 64)]> R2).
    assert (HR3a2 : R3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 14) : mword 64))
      by (rewrite /R3; apply upd_eq).
    assert (HR3a0 : R3 !!! Regidx Ra0 = (mm !!! Regidx Ra0 : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2a0 | nz]).
    assert (HR3a1 : R3 !!! Regidx Ra1 = (mm !!! Regidx Ra1 : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2a1 | nz]).
    assert (HR3sp : nc_sp mm R3)
      by (rewrite /nc_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : nc_thr mm R3).
    { intros c Hcs N2 N8.
      rewrite /R3 upd_ne; [| regne]. exact (HR2thr c Hcs N2 N8). }
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.namecmp + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.namecmp + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    (* ===== +0x0a jal ra,strncmp ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.namecmp + 0x0a)) Rra
              (mword_of_int 2086268 : mword 21) R3 (K - 2)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (R4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.namecmp + 0x0a) : mword 64) 4)]> R3).
    assert (Htgt : add_vec (mword_of_int (KernelSyms.namecmp + 0x0a) : mword 64)
                     (sign_extend' 64 (mword_of_int 2086268 : mword 21))
                   = mword_of_int KernelSyms.strncmp) by pcw.
    iEval (rewrite Htgt) in "Hpc".
    assert (HR4a2 : R4 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 14) : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3a2 | nz]).
    assert (HR4a0 : R4 !!! Regidx Ra0 = (mm !!! Regidx Ra0 : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3a0 | nz]).
    assert (HR4a1 : R4 !!! Regidx Ra1 = (mm !!! Regidx Ra1 : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3a1 | nz]).
    assert (HR4sp : nc_sp mm R4)
      by (rewrite /nc_sp /R4 upd_ne; [exact HR3sp | nz]).
    assert (HR4ra : R4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.namecmp + 0x0a) : mword 64) 4)
      by (rewrite /R4; apply upd_eq).
    assert (HR4thr : nc_thr mm R4).
    { intros c Hcs N2 N8.
      rewrite /R4 upd_ne; [| regne]. exact (HR3thr c Hcs N2 N8). }
    iDestruct (wp_next_shift (CIDa := CID) (CIDb := CID6) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (SC.wp_strncmp_sconf ktf ktg R4 14%nat f g (K - 2)%nat dq1 dq2 b p
              ltac:(lia) HR4a2 ltac:(lia)
              with "Hcg Htext Hpc [Hb1] [Hb2]").
    { iEval (rewrite HR4a0). iExact "Hb1". }
    { iEval (rewrite HR4a1). iExact "Hb2". }
    iIntros (CID7 Hq7 mS) "Hcg Hpc Hb1 Hb2 %HcsS %Hres".
    iEval (rewrite HR4a0) in "Hb1".
    iEval (rewrite HR4a1) in "Hb2".
    assert (Hpc0e : ret_pc (R4 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.namecmp + 0x0e))
      by (rewrite HR4ra; pcw).
    iEval (rewrite Hpc0e) in "Hpc".
    pose proof HcsS as HcsS_cs.
    assert (HmSsp : nc_sp mm mS).
    { rewrite /nc_sp
        (callee_saved_lookup HcsS_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR4sp. }
    assert (HmSthr : nc_thr mm mS).
    { intros c Hcs N2 N8.
      rewrite (callee_saved_lookup HcsS_cs c Hcs).
      exact (HR4thr c Hcs N2 N8). }
    (* ===== +0x0e / +0x10 : the two restores ===== *)
    assert (Hc1 : add_vec (mS !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (mm !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HmSsp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc2 : add_vec (mS !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (mm !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HmSsp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.namecmp + 0x0e))
              (mword_of_int 1 : mword 6) Rra mS (K - 2)%nat
              (mm !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0e [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID8 Hq8) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra : mword 64)]> mS).
    assert (HP1sp : nc_sp mm P1)
      by (rewrite /nc_sp /P1 upd_ne; [exact HmSsp | nz]).
    assert (HP1thr : nc_thr mm P1).
    { intros c Hcs N2 N8.
      rewrite /P1 upd_ne; [| regne]. exact (HmSthr c Hcs N2 N8). }
    assert (HP1ra : P1 !!! Regidx Rra = (mm !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1a0 : P1 !!! Regidx Ra0 = (mS !!! Regidx Ra0 : mword 64))
      by (rewrite /P1 upd_ne; [reflexivity | nz]).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.namecmp + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.namecmp + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.namecmp + 0x10))
              (mword_of_int 0 : mword 6) Rs0 P1 (K - 2)%nat
              (mm !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi10 [Hf2]").
    { iEval (rewrite HP1sp -HmSsp Hc2). iExact "Hf2". }
    iIntros (CID9 Hq9) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -HmSsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : nc_sp mm P2)
      by (rewrite /nc_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : nc_thr mm P2).
    { intros c Hcs N2 N8.
      rewrite /P2 upd_ne; [| regne]. exact (HP1thr c Hcs N2 N8). }
    assert (HP2ra : P2 !!! Regidx Rra = (mm !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (HP2a0 : P2 !!! Regidx Ra0 = (mS !!! Regidx Ra0 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.namecmp + 0x10) : mword 64) 2
                    = mword_of_int (KernelSyms.namecmp + 0x12)) by pcw.
    iEval (rewrite Hpp12) in "Hpc".
    (* ===== +0x12 c.addi sp,sp,16 : pop ===== *)
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
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.namecmp + 0x12))
              (mword_of_int 16 : mword 6) P2 (K - 2)%nat 2 b Hpop
              with "Hcg Hpc Hi12 Hstk").
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (P3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> P2).
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.namecmp + 0x12) : mword 64) 2
                    = mword_of_int (KernelSyms.namecmp + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 c.ret ===== *)
    assert (HP3ra : P3 !!! Regidx Rra = (mm !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.namecmp + 0x14)) Rra P3 K b
              ltac:(nz) with "Hcg Hpc Hi14").
    iIntros (CID11 Hq11) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P3 !!! Regidx Rra : mword 64)
                    = ret_pc (mm !!! Regidx Rra : mword 64))
      by (rewrite HP3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (HP3a0 : P3 !!! Regidx Ra0 = (mS !!! Regidx Ra0 : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2a0 | nz]).
    assert (Csp : P3 !!! Regidx csp_rs1 = (mm !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P3 upd_eq; exact Hwv).
    assert (Cs0 : P3 !!! Regidx Rs0 = (mm !!! Regidx Rs0 : mword 64)).
    { rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_eq. reflexivity. }
    assert (Hfin : nc_thr mm P3).
    { intros c Hcs N2 N8.
      rewrite /P3 upd_ne; [| regne]. exact (HP2thr c Hcs N2 N8). }
    assert (Cs1 : P3 !!! Regidx (mword_of_int 9 : mword 5)
                  = (mm !!! Regidx (mword_of_int 9 : mword 5) : mword 64))
      by (apply Hfin; ncidx).
    assert (Cs2 : P3 !!! Regidx (mword_of_int 18 : mword 5)
                  = (mm !!! Regidx (mword_of_int 18 : mword 5) : mword 64))
      by (apply Hfin; ncidx).
    assert (Cs3 : P3 !!! Regidx (mword_of_int 19 : mword 5)
                  = (mm !!! Regidx (mword_of_int 19 : mword 5) : mword 64))
      by (apply Hfin; ncidx).
    assert (Cs4 : P3 !!! Regidx (mword_of_int 20 : mword 5)
                  = (mm !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; ncidx).
    assert (Cs5 : P3 !!! Regidx (mword_of_int 21 : mword 5)
                  = (mm !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; ncidx).
    assert (Cs6 : P3 !!! Regidx (mword_of_int 22 : mword 5)
                  = (mm !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; ncidx).
    assert (Cs7 : P3 !!! Regidx (mword_of_int 23 : mword 5)
                  = (mm !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; ncidx).
    assert (Cs8 : P3 !!! Regidx (mword_of_int 24 : mword 5)
                  = (mm !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; ncidx).
    assert (Cs9 : P3 !!! Regidx (mword_of_int 25 : mword 5)
                  = (mm !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; ncidx).
    assert (Cs10 : P3 !!! Regidx (mword_of_int 26 : mword 5)
                  = (mm !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; ncidx).
    assert (Cs11 : P3 !!! Regidx (mword_of_int 27 : mword 5)
                  = (mm !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; ncidx).
    iSpecialize ("Hcont" $! CID11 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! P3 with "[%] Hcg Hpc Hb1 Hb2 [%]").
    { unfold callee_saved. split_and!; assumption. }
    { rewrite HP3a0. exact (nc_res_iff f g (mS !!! Regidx Ra0) Hres). }
  Qed.

End ProofNamecmpMain.

End NamecmpProof.
