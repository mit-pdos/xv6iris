(* WpSconfMycpu.v: mycpu over the SIE-agnostic v2 bundle (stage 8, first
   whole function on the free-stack-owning sie_cap accounting).

   The spec threads sconf γ + sie_cap end-to-end at EITHER SIE arm; the
   2-slot frame comes straight out of the capability: the prologue's
   c.addi sp,-16 goes through [wp_caddi_sp_push_s_sconf] (n -> n - 2,
   handing out the frame region [sp', sp0)), and the epilogue's
   c.addi sp,16 feeds the frame back via [wp_caddi_sp_pop_s_sconf]
   (n - 2 -> n).  Leaf-by-leaf (the old den blocks contain the
   sp-moves, which the sconf VCgen guard forbids); the instruction
   facts myi_XX are imported from WpMycpu.v. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import WpAuipc VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpMycpu.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecMycpu.
Import Defs.

Module MycpuProof : MYCPU.

Section WpSconfMycpu.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_mycpu_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat)
    : wp_mycpu_sconf_body γ Φ m0 n.
  Proof.
    cbv beta delta [wp_mycpu_sconf_body].
    intros ra_idx tp_idx a0_idx pcE ra0 ret_tgt Hal0 Hn.
    pose (sp0 := (m0 !!! Regidx csp_rs1 : mword 64)).
    (* the per-instruction register-map chain (private to the proof) *)
    set (s0_idx := (mword_of_int 8 : mword 5)).
    set (a5_idx := (mword_of_int 15 : mword 5)).
    set (imm_entry := (mword_of_int 48 : mword 6)).
    set (imm_dealloc := (mword_of_int 16 : mword 6)).
    set (nzimm_s0 := (mword_of_int 4 : mword 8)).
    set (imm_auipc := (mword_of_int 0x11 : mword 20)).
    set (imm_addi := (mword_of_int 0xa86 : mword 12)).
    set (shamt_slli := (mword_of_int 7 : mword 6)).
    set (imm_addiw := (mword_of_int 0 : mword 6)).
    set (sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (s00 := m0 !!! Regidx s0_idx).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    set (m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1).
    set (m3 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx tp_idx))]> m2).
    set (m4 := <[Regidx a5_idx := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (m3 !!! Regidx a5_idx) (sign_extend' 64 (sign_extend' 12 imm_addiw))) 31 0))]> m3).
    set (m5 := <[Regidx a5_idx := regval_into_reg (shift_bits_left (m4 !!! Regidx a5_idx) (subrange_vec_dec shamt_slli (Z.sub log2_xlen 1) 0))]> m4).
    set (m6 := <[Regidx a0_idx := regval_into_reg (add_vec (add_vec_int (mword_of_int KernelSyms.mycpu : mword 64) 14) (auipc_off imm_auipc))]> m5).
    set (m7 := <[Regidx a0_idx := regval_into_reg (add_vec (m6 !!! Regidx a0_idx) (sign_extend' 64 imm_addi))]> m6).
    set (m8 := <[Regidx a0_idx := regval_into_reg (add_vec (m7 !!! Regidx a0_idx) (m7 !!! Regidx a5_idx))]> m7).
    set (m9 := <[Regidx ra_idx := regval_into_reg ra0]> m8).
    set (m10 := <[Regidx s0_idx := regval_into_reg s00]> m9).
    set (m11 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> m10).
    iIntros "Hcg #Htext Hpc Hcont".
    iPoseProof (myi_00 with "Htext") as "Hi00".
    iPoseProof (myi_02 with "Htext") as "Hi02".
    iPoseProof (myi_04 with "Htext") as "Hi04".
    iPoseProof (myi_06 with "Htext") as "Hi06".
    iPoseProof (myi_08 with "Htext") as "Hi08".
    iPoseProof (myi_0a with "Htext") as "Hi0a".
    iPoseProof (myi_0c with "Htext") as "Hi0c".
    iPoseProof (myi_0e with "Htext") as "Hi0e".
    iPoseProof (myi_12 with "Htext") as "Hi12".
    iPoseProof (myi_16 with "Htext") as "Hi16".
    iPoseProof (myi_18 with "Htext") as "Hi18".
    iPoseProof (myi_1a with "Htext") as "Hi1a".
    iPoseProof (myi_1c with "Htext") as "Hi1c".
    iPoseProof (myi_1e with "Htext") as "Hi1e".
    (* the sp geometry: sp' = pa_stk sp0 2; frame slot addresses *)
    assert (Hcsp1 : m1 !!! Regidx csp_rs1 = sp') by (apply upd_eq).
    assert (Hpush : sp' = pa_stk (m0 !!! Regidx csp_rs1) 2).
    { unfold sp', pa_stk, add_vec_int, imm_entry.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = pa_stk (m0 !!! Regidx csp_rs1) 2).
    { rewrite Hcsp1. exact Hpush. }
    (* ---- 0x00: c.addi sp,-16 -- the frame push ---- *)
    iApply (wp_caddi_sp_push_s_sconf γ Φ pcE imm_entry m0 n 2 Hn Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.mycpu + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (vr24 vs16) "[Hbra Hbs0]".
    (* the two frame cells at csdsp's own address spelling *)
    assert (Hpa1 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hbra".
    iEval (rewrite -Hpa2) in "Hbs0".
    (* ---- 0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (KernelSyms.mycpu + 0x02)) (mword_of_int 1 : mword 6) ra_idx m1 (n - 2)%nat vr24
              with "Hcg Hpc Hi02 Hbra [-]").
    iIntros "Hcg Hpc Hbra".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.mycpu + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.mycpu + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (KernelSyms.mycpu + 0x04)) (mword_of_int 0 : mword 6) s0_idx m1 (n - 2)%nat vs16
              with "Hcg Hpc Hi04 Hbs0 [-]").
    iIntros "Hcg Hpc Hbs0".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.mycpu + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.mycpu + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.addi4spn s0,sp,4 ---- *)
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (KernelSyms.mycpu + 0x06)) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx m1 (n - 2)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi06 [-]").
    iIntros "Hcg Hpc".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.mycpu + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.mycpu + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1) with m2.
    (* ---- 0x08: c.mv a5,tp ---- *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (KernelSyms.mycpu + 0x08)) a5_idx tp_idx m2 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi08 [-]").
    iIntros "Hcg Hpc".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.mycpu + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.mycpu + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx tp_idx))]> m2) with m3.
    (* ---- 0x0a: c.addiw a5,0 ---- *)
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (KernelSyms.mycpu + 0x0a)) a5_idx imm_addiw m3 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0a [-]").
    iIntros "Hcg Hpc".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.mycpu + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.mycpu + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (m3 !!! Regidx a5_idx) (sign_extend' 64 (sign_extend' 12 imm_addiw))) 31 0))]> m3) with m4.
    (* ---- 0x0c: c.slli a5,7 ---- *)
    iApply (wp_cslli_s_sconf γ Φ (mword_of_int (KernelSyms.mycpu + 0x0c)) (Regidx a5_idx) a5_idx shamt_slli m4 (n - 2)%nat
              eq_refl ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0c [-]").
    iIntros "Hcg Hpc".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.mycpu + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.mycpu + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (shift_bits_left (m4 !!! Regidx a5_idx) (subrange_vec_dec shamt_slli (Z.sub log2_xlen 1) 0))]> m4) with m5.
    (* ---- 0x0e: auipc a0,0x11 (pc respelled to the m6 chain's form) ---- *)
    assert (Hpc0e : (mword_of_int (KernelSyms.mycpu + 0x0e) : mword 64) = add_vec_int (mword_of_int KernelSyms.mycpu : mword 64) 14)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    iEval (rewrite Hpc0e) in "Hi0e".
    iApply (wp_auipc_s_sconf γ Φ (add_vec_int (mword_of_int KernelSyms.mycpu : mword 64) 14) a0_idx imm_auipc m5 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0e [-]").
    iIntros "Hcg Hpc".
    assert (Hpp12 : add_vec_int (add_vec_int (mword_of_int KernelSyms.mycpu : mword 64) 14) 4 = mword_of_int (KernelSyms.mycpu + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    change (<[Regidx a0_idx := regval_into_reg (add_vec (add_vec_int (mword_of_int KernelSyms.mycpu : mword 64) 14) (auipc_off imm_auipc))]> m5) with m6.
    (* ---- 0x12: addi a0,a0,0xa86 ---- *)
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (KernelSyms.mycpu + 0x12)) a0_idx a0_idx imm_addi m6 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi12 [-]").
    iIntros "Hcg Hpc".
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.mycpu + 0x12) : mword 64) 4 = mword_of_int (KernelSyms.mycpu + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    change (<[Regidx a0_idx := regval_into_reg (add_vec (m6 !!! Regidx a0_idx) (sign_extend' 64 imm_addi))]> m6) with m7.
    (* ---- 0x16: c.add a0,a5 ---- *)
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (KernelSyms.mycpu + 0x16)) a0_idx a5_idx m7 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi16 [-]").
    iIntros "Hcg Hpc".
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.mycpu + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.mycpu + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    change (<[Regidx a0_idx := regval_into_reg (add_vec (m7 !!! Regidx a0_idx) (m7 !!! Regidx a5_idx))]> m7) with m8.
    (* ---- 0x18: c.ldsp ra,8(sp) ---- *)
    assert (Hm8sp : m8 !!! Regidx csp_rs1 = sp').
    { unfold m8, m7, m6, m5, m4, m3, m2;
      repeat (rewrite upd_ne; [| vm_compute; discriminate]);
      unfold m1; rewrite upd_eq; reflexivity. }
    assert (Hpa1' : add_vec (m8 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hm8sp. rewrite -Hcsp1. exact Hpa1. }
    assert (Hpa2' : add_vec (m8 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hm8sp. rewrite -Hcsp1. exact Hpa2. }
    assert (Hra0v : m1 !!! Regidx ra_idx = ra0)
      by (unfold m1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs00v : m1 !!! Regidx s0_idx = s00)
      by (unfold m1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hpa1 -Hpa1' Hra0v) in "Hbra".
    iEval (rewrite Hpa2 -Hpa2' Hs00v) in "Hbs0".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (KernelSyms.mycpu + 0x18)) (mword_of_int 1 : mword 6) ra_idx m8 (n - 2)%nat ra0
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi18 Hbra [-]").
    iIntros "Hcg Hpc Hbra".
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.mycpu + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.mycpu + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    change (<[Regidx ra_idx := regval_into_reg ra0]> m8) with m9.
    (* ---- 0x1a: c.ldsp s0,0(sp) ---- *)
    assert (Hm9sp : m9 !!! Regidx csp_rs1 = m8 !!! Regidx csp_rs1)
      by (unfold m9; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite -Hm9sp) in "Hbs0".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (KernelSyms.mycpu + 0x1a)) (mword_of_int 0 : mword 6) s0_idx m9 (n - 2)%nat s00
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1a Hbs0 [-]").
    iIntros "Hcg Hpc Hbs0".
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.mycpu + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.mycpu + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg s00]> m9) with m10.
    (* ---- 0x1c: c.addi sp,16 -- the frame pop ---- *)
    assert (Hm10sp : m10 !!! Regidx csp_rs1 = sp').
    { unfold m10, m9; repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact Hcsp1. }
    assert (Hwv : add_vec (m10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)) = sp0).
    { rewrite Hm10sp. unfold sp', imm_dealloc, imm_entry, sp0. apply mycpu_frame_cancel. }
    assert (Hpop : m10 !!! Regidx csp_rs1
                   = pa_stk (add_vec (m10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc))) 2).
    { rewrite Hwv Hm10sp. exact Hpush. }
    iEval (rewrite Hpa1') in "Hbra".
    iEval (rewrite Hm9sp Hpa2') in "Hbs0".
    iDestruct (stack_own_2_intro sp0 with "Hbra Hbs0") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf γ Φ (mword_of_int (KernelSyms.mycpu + 0x1c)) imm_dealloc m10
              (n - 2)%nat 2 Hpop
              with "Hcg Hpc Hi1c Hframe [-]").
    iIntros "Hcg Hpc".
    assert (Hnk : ((n - 2) + 2)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.mycpu + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.mycpu + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (m10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> m10) with m11.
    (* ---- 0x1e: c.ret ---- *)
    assert (Hm11ra : m11 !!! Regidx ra_idx = ra0).
    { unfold m11, m10; repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold m9. rewrite upd_eq. reflexivity. }
    assert (Hal0' : eq_vec (access_vec_dec (update_vec_dec (add_vec (m11 !!! Regidx ra_idx) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite Hm11ra; exact Hal0).
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (KernelSyms.mycpu + 0x1e)) ra_idx m11 n
              ltac:(vm_compute; discriminate) Hal0'
              with "Hcg Hpc Hi1e [-]").
    iIntros "Hcg Hpc".
    assert (Hra_final : update_vec_dec (add_vec (m11 !!! Regidx ra_idx) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite Hm11ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! m11 with "Hcg Hpc [%]").
    split.
    - assert (Hm11w : m11 = apply_writes
        [ (csp_rs1, regval_into_reg (add_vec (m10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc))));
          (s0_idx,  regval_into_reg s00);
          (ra_idx,  regval_into_reg ra0);
          (a0_idx,  regval_into_reg (add_vec (m7 !!! Regidx a0_idx) (m7 !!! Regidx a5_idx)));
          (a0_idx,  regval_into_reg (add_vec (m6 !!! Regidx a0_idx) (sign_extend' 64 imm_addi)));
          (a0_idx,  regval_into_reg (add_vec (add_vec_int (mword_of_int KernelSyms.mycpu : mword 64) 14) (auipc_off imm_auipc)));
          (a5_idx,  regval_into_reg (shift_bits_left (m4 !!! Regidx a5_idx) (subrange_vec_dec shamt_slli (Z.sub log2_xlen 1) 0)));
          (a5_idx,  regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (m3 !!! Regidx a5_idx) (sign_extend' 64 (sign_extend' 12 imm_addiw))) 31 0)));
          (a5_idx,  regval_into_reg (add_vec zero_reg (m2 !!! Regidx tp_idx)));
          (s0_idx,  regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0))));
          (csp_rs1, regval_into_reg sp') ] m0) by reflexivity.
      rewrite Hm11w. apply callee_saved_apply_writes.
      repeat constructor.
      rewrite (outer_write_cons_eq (mword_of_int 2) csp_rs1);
        [ | vm_compute; reflexivity ].
      unfold regval_into_reg.
      rewrite Hm10sp.
      change (m0 !!! Regidx (mword_of_int 2)) with (m0 !!! Regidx csp_rs1).
      unfold sp', imm_dealloc, imm_entry.
      apply mycpu_frame_cancel.
    - rewrite /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /s00 /ra0.
      repeat first [ rewrite upd_eq
                   | rewrite upd_ne; [| vm_compute; discriminate] ].
      unfold mycpu_ret, mycpu_a5. reflexivity.
  Qed.


  (* jal-callable form: writes ra := P+4, runs mycpu, returns to P+4.
     The capability count n rides through unchanged (the jal moves no
     sp), and callee_saved composes across the ra write. *)
  Lemma wp_call_mycpu_sconf_cs (γ : gname) (Φ : mval -> iProp Σ)
      (P : mword 64) (jimm : mword 21)
      (m : regfile) (n : nat)
    : wp_call_mycpu_sconf_cs_body γ Φ P jimm m n.
  Proof.
    cbv beta delta [wp_call_mycpu_sconf_cs_body].
    intros ra_idx m0 pcE ra0 ret_tgt Htarget Halpce Hal0 Hn.
    iIntros "Hcg #Htext Hpc Hjal Hcont".
    iApply (wp_jal_s_sconf γ Φ P (mword_of_int 1) jimm m n
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Htarget; exact Halpce)
              with "Hcg Hpc Hjal [-]").
    iIntros "Hcg Hpc".
    iEval (rewrite Htarget) in "Hpc".
    iApply (wp_mycpu_sconf γ Φ m0 n Hal0 Hn
              with "Hcg Htext Hpc [-]").
    iIntros (m') "Hcg Hpc %Hcs".
    iApply ("Hcont" $! m' with "Hcg Hpc [%]").
    destruct Hcs as [Hcs Ha0].
    split.
    - eapply callee_saved_trans; [ | exact Hcs ].
      assert (Hm0w : m0 = apply_writes
        [ ((mword_of_int 1 : mword 5), regval_into_reg (add_vec_int P 4)) ] m) by reflexivity.
      rewrite Hm0w. apply callee_saved_apply_writes. repeat constructor.
    - rewrite Ha0. f_equal.
    all: reg_lookup.
  Qed.

End WpSconfMycpu.

End MycpuProof.
