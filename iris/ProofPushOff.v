(* ProofPushOff.v: push_off over the SIE-agnostic v2 bundle (stage 8).
   This file holds the SUFFIX (PO+0x18: second mycpu call, the noff
   increment, the epilogue frame-trade and c.ret) -- the shared tail of
   both branch arms -- and (next) the main lemma with the prologue, the
   fused csrrci flip, and the intena arm. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import IntrDefs.
Require Import IntrDefs.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfCsr.
Require Import WpGprCsrwCommon WpIntenaBits KernelRvcDecode KernelBaseDecode WpPushOffCsr WpMycpu SpecMycpu WpPushOffTop WpPopOff.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcGeom CpuOwn.
Require Import WpPushOffBridges.
Require Import SpecPushOff.
Import Defs.


(* +0x24  0x10016073  csrsi sstatus,2 (rd = x0) -- pop_off's intr_on.  Its
   decode is KernelBaseDecode.v's shared [bdec_10016073], stated with the csr
   field as [Ox"100"], which is (delta-)equal to the [csr_sstatus] the CSR
   leaves -- and the [instr] fact below -- are phrased with. *)

(* the epilogue +32 cancels a pa_stk 4 re-anchor (closed offsets). *)
Local Lemma po_up_cancel (X : mword 64) :
  pa_stk (add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4 = X.
Proof.
  unfold pa_stk, add_vec_int.
  rewrite pa_stk_off2.
  assert (Hz : bv_wrap 64 (uint (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64)
                           + uint (mword_of_int (- (8 * Z.of_nat 4)) : mword 64)) = 0%Z)
    by (vm_compute; reflexivity).
  rewrite Hz.
  change (add_vec X (mword_of_int 0)) with (add_vec_int X 0).
  apply avi0.
Qed.


Local Lemma addv_zero_l (x : mword 64) : add_vec zero_reg x = x.
Proof.
  assert (add_vec_unsigned : forall a b : mword 64,
            bv_unsigned (add_vec a b) = bv_wrap 64 (bv_unsigned a + bv_unsigned b)).
  { intros a b. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite add_vec_unsigned.
  change (bv_unsigned (zero_reg : mword 64)) with 0%Z. rewrite Z.add_0_l.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Local Lemma po_up_cancel16 (X : mword 64) :
  pa_stk (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2 = X.
Proof.
  unfold pa_stk, add_vec_int.
  rewrite pa_stk_off2.
  assert (Hz : bv_wrap 64 (uint (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)
                           + uint (mword_of_int (- (8 * Z.of_nat 2)) : mword 64)) = 0%Z)
    by (vm_compute; reflexivity).
  rewrite Hz.
  change (add_vec X (mword_of_int 0)) with (add_vec_int X 0).
  apply avi0.
Qed.


Module PushOffProof (Mycpu : MYCPU) : PUSHOFF.

Section ProofPushOff.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma ppi_24 : kernel_text -∗ instr (mword_of_int (PP + 0x24) : mword 64) false
      (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS)).
  Proof. mk_base (PP + 0x24)%Z (mword_of_int 0x10016073 : mword 32)
    (mword_of_int (PP + 0x24) : mword 64)
    (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS)) bdec_10016073. Qed.

  (* ------------------------------------------------------------------- *)
  (* pop_off's shared epilogue (PP+0x28..0x2e): restore ra/s0, trade the  *)
  (* 2-slot frame back through the capability, ret.  All three runtime    *)
  (* paths (early-noff, intena=0, post-restore) funnel here.              *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_pop_off_epi_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (M : regfile) (av : nat) (ra0e s00e : mword 64) :
    let spd := M !!! Regidx csp_rs1 in
    let sp0up := add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) in
    let ret_tgt := ret_pc ra0e in
    sie_cap_gpr γ M av -∗
    kernel_text -∗ pc_is (mword_of_int (PP + 0x28) : mword 64) -∗
    add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) ↦₈ ra0e -∗
    add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) ↦₈ s00e -∗
    ( ∀ mf,
      sie_cap_gpr γ mf (av + 2) -∗
      pc_is ret_tgt -∗
      ⌜ mf = <[Regidx csp_rs1 := regval_into_reg sp0up]>
             (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]>
              (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M)) ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros spd sp0up ret_tgt.
    set (M4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M).
    set (M5 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]> M4).
    set (M6 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (M5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> M5).
    iIntros "Hcg #Htext Hpc Hp8 Hp0 Hcont".
    iPoseProof (ppi_28 with "Htext") as "Hi28".
    iPoseProof (ppi_2a with "Htext") as "Hi2a".
    iPoseProof (ppi_2c with "Htext") as "Hi2c".
    iPoseProof (ppi_2e with "Htext") as "Hi2e".
    (* ---- 0x28: c.ldsp ra,8(sp) ---- *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PP + 0x28)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              M av ra0e
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi28 Hp8 [-]").
    iIntros "Hcg Hpc Hp8".
    assert (Hpc2a : add_vec_int (mword_of_int (PP + 0x28) : mword 64) 2 = mword_of_int (PP + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M) with M4.
    (* ---- 0x2a: c.ldsp s0,0(sp) ---- *)
    assert (Hsp4 : M4 !!! Regidx csp_rs1 = spd)
      by (rewrite /M4 upd_ne; [reflexivity | vm_compute; discriminate]).
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PP + 0x2a)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              M4 av s00e
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2a [Hp0] [-]").
    { iEval (rewrite Hsp4). iExact "Hp0". }
    iIntros "Hcg Hpc Hp0".
    assert (Hpc2c : add_vec_int (mword_of_int (PP + 0x2a) : mword 64) 2 = mword_of_int (PP + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]> M4) with M5.
    (* ---- 0x2c: c.addi sp,16 -- the frame trade back ---- *)
    assert (Hsp5 : M5 !!! Regidx csp_rs1 = spd)
      by (rewrite /M5 upd_ne; [exact Hsp4 | vm_compute; discriminate]).
    assert (HM6sp : M6 !!! Regidx csp_rs1 = sp0up).
    { rewrite /M6 upd_eq Hsp5. reflexivity. }
    assert (Hupc : pa_stk sp0up 2 = spd).
    { unfold sp0up. apply po_up_cancel16. }
    assert (Hwv : add_vec (M5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0up).
    { rewrite Hsp5. reflexivity. }
    assert (Hpop : M5 !!! Regidx csp_rs1
                   = pa_stk (add_vec (M5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv Hsp5. symmetry. exact Hupc. }
    assert (Hb1u : pa_stk sp0up 1
                    = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2u : pa_stk sp0up 2
                    = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iAssert (stack_own sp0up 2) with "[Hp8 Hp0]" as "Hframe".
    { iApply (stack_own_2_intro with "[Hp8] [Hp0]").
      - iEval (rewrite Hb1u). iExact "Hp8".
      - iEval (rewrite Hb2u -Hsp4). iExact "Hp0". }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf γ Φ (mword_of_int (PP + 0x2c)) (mword_of_int 16 : mword 6) M5 av 2 Hpop
              with "Hcg Hpc Hi2c Hframe [-]").
    iIntros "Hcg Hpc".
    assert (Hpc2e : add_vec_int (mword_of_int (PP + 0x2c) : mword 64) 2 = mword_of_int (PP + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (M5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> M5) with M6.
    (* ---- 0x2e: c.ret ---- *)
    assert (HM6ra : M6 !!! Regidx (mword_of_int 1 : mword 5) = ra0e).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4. apply upd_eq. }
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (PP + 0x2e)) (mword_of_int 1 : mword 5) M6 (av + 2)%nat
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2e [-]").
    iIntros "Hcg Hpc".
    assert (Hra_final : ret_pc (M6 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HM6ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! M6 with "Hcg Hpc [%]").
    rewrite /M6 /M5 /M4 Hsp5. reflexivity.
  Qed.

  Lemma wp_push_off_suffix_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (ms : regfile) (av : nat)
      (noff : mword 32) (ra0e s00e s10e vgap : mword 64)
      :
    let P : mword 64 := mword_of_int (PO + 0x18) in
    let spm := ms !!! Regidx csp_rs1 in
    let a0v := mycpu_ret (ms !!! Regidx (mword_of_int 4 : mword 5)) in
    let a8_noff := add_vec a0v (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a8_p24 := add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a8_p16 := add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a8_p8  := add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let sp0up := add_vec spm (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) in
    let noff_a5 := sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 noff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
    let storeval := (autocast (T := mword)
        (subrange_vec_dec noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let cret_tgt := ret_pc ra0e in
    (2 <= av)%nat ->
    sie_cap_gpr γ ms av -∗
    kernel_text -∗ pc_is P -∗
    a8_noff ↦₄ noff -∗
    a8_p24 ↦₈ ra0e -∗
    a8_p16 ↦₈ s00e -∗
    a8_p8 ↦₈ s10e -∗
    spm ↦₈ vgap -∗
    ( pc_is cret_tgt -∗
      (∃ mfin, sie_cap_gpr γ mfin (av + 4) ∗ ⌜ mfin !!! Regidx (mword_of_int 1 : mword 5) = ra0e /\
                                 mfin !!! Regidx (mword_of_int 8 : mword 5) = s00e /\
                                 mfin !!! Regidx (mword_of_int 9 : mword 5) = s10e /\
                                 mfin !!! Regidx csp_rs1 = add_vec spm (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) /\
                                 mfin !!! Regidx (mword_of_int 4 : mword 5) = ms !!! Regidx (mword_of_int 4 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 18 : mword 5) = ms !!! Regidx (mword_of_int 18 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 19 : mword 5) = ms !!! Regidx (mword_of_int 19 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 20 : mword 5) = ms !!! Regidx (mword_of_int 20 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 21 : mword 5) = ms !!! Regidx (mword_of_int 21 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 22 : mword 5) = ms !!! Regidx (mword_of_int 22 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 23 : mword 5) = ms !!! Regidx (mword_of_int 23 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 24 : mword 5) = ms !!! Regidx (mword_of_int 24 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 25 : mword 5) = ms !!! Regidx (mword_of_int 25 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 26 : mword 5) = ms !!! Regidx (mword_of_int 26 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 27 : mword 5) = ms !!! Regidx (mword_of_int 27 : mword 5) ⌝) -∗
      a8_noff ↦₄ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros P spm a0v a8_noff a8_p24 a8_p16 a8_p8 sp0up noff_a5 storeval cret_tgt Hav.
    set (s00 := ms !!! Regidx (mword_of_int 8 : mword 5)).
    assert (Hm0sp : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> ms) !!! Regidx csp_rs1 = spm)
      by (rewrite upd_ne; [ reflexivity | vm_compute; discriminate ]).
    iIntros "Hcg #Htext Hpc Hnoff Hpp24 Hpp16 Hpp8 Hgap Hcont".
    iPoseProof (poi_18 with "Htext") as "Hi18".
    iApply (Mycpu.wp_call_mycpu_sconf_cs γ Φ P (mword_of_int 0xcfe : mword 21) ms av
 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc Hi18 [-]").
    iIntros (mo) "Hcg Hpc %Hmo".
    destruct Hmo as [Hmo_cs Hmo_a0].
    destruct Hmo_cs as (Hcsp & Htp & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
    set (M1 := mo).
    set (M2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noff)]> M1).
    set (M3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (M2 !!! Regidx (mword_of_int 15 : mword 5))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> M2).
    set (M4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M3).
    set (M5 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]> M4).
    set (M6 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg s10e]> M5).
    set (M7 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (M6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> M6).
    (* normalise pc = ret_tgt to PO+0x1c *)
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc1c : ret_pc (add_vec_int P 4)
                    = (mword_of_int (PO + 0x1c) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    (* ---- 0x1c: c.lw a5,120(a0) : a5 := zext32(noff) ---- *)
    assert (Hm110 : M1 !!! Regidx (mword_of_int 10 : mword 5) = a0v) by exact Hmo_a0.
    iPoseProof (poi_1c with "Htext") as "Hi1c".
    iApply (wp_clw_s_sconf γ Φ (mword_of_int (PO + 0x1c)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) M1 av noff
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1c [Hnoff] [-]").
    { iEval (rewrite Hm110). iExact "Hnoff". }
    iIntros "Hcg Hpc Hnoff".
    iEval (rewrite Hm110) in "Hnoff".
    assert (Hpc1e : add_vec_int (mword_of_int (PO + 0x1c) : mword 64) 2 = mword_of_int (PO + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* ---- 0x1e: c.addiw a5,a5,1 : a5 := sext32(noff+1) ---- *)
    iPoseProof (poi_1e with "Htext") as "Hi1e".
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (PO + 0x1e)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6)
              M2 av   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1e [-]").
    iIntros "Hcg Hpc".
    assert (Hpc20 : add_vec_int (mword_of_int (PO + 0x1e) : mword 64) 2 = mword_of_int (PO + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc20) in "Hpc".
    (* ---- 0x20: c.sw a5,120(a0) : store noff+1 ---- *)
    assert (Hm310 : M3 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate]. exact Hmo_a0. }
    iPoseProof (poi_20 with "Htext") as "Hi20".
    iApply (wp_csw_s_sconf γ Φ (mword_of_int (PO + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) M3 av noff

              with "Hcg Hpc Hi20 [Hnoff] [-]").
    { iEval (rewrite Hm310). iExact "Hnoff". }
    iIntros "Hcg Hpc Hnoff".
    assert (Hpc22 : add_vec_int (mword_of_int (PO + 0x20) : mword 64) 2 = mword_of_int (PO + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* ---- 0x22: c.ldsp ra,24(sp) : ra := ra0e ---- *)
    assert (Hcsp3 : M3 !!! Regidx csp_rs1 = spm).
    { rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hcsp. }
    iPoseProof (poi_22 with "Htext") as "Hi22".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PO + 0x22)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              M3 av ra0e
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi22 [Hpp24] [-]").
    { iEval (rewrite Hcsp3). iExact "Hpp24". }
    iIntros "Hcg Hpc Hpp24".
    assert (Hpc24 : add_vec_int (mword_of_int (PO + 0x22) : mword 64) 2 = mword_of_int (PO + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    (* ---- 0x24: c.ldsp s0,16(sp) : s0 := s00e ---- *)
    assert (Hcsp4 : M4 !!! Regidx csp_rs1 = spm).
    { rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate]. exact Hcsp3. }
    iPoseProof (poi_24 with "Htext") as "Hi24".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PO + 0x24)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              M4 av s00e
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi24 [Hpp16] [-]").
    { iEval (rewrite Hcsp4). iExact "Hpp16". }
    iIntros "Hcg Hpc Hpp16".
    assert (Hpc26 : add_vec_int (mword_of_int (PO + 0x24) : mword 64) 2 = mword_of_int (PO + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    (* ---- 0x26: c.ldsp s1,8(sp) : s1 := s10e ---- *)
    assert (Hcsp5 : M5 !!! Regidx csp_rs1 = spm).
    { rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate]. exact Hcsp4. }
    iPoseProof (poi_26 with "Htext") as "Hi26".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PO + 0x26)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              M5 av s10e
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi26 [Hpp8] [-]").
    { iEval (rewrite Hcsp5). iExact "Hpp8". }
    iIntros "Hcg Hpc Hpp8".
    assert (Hpc28 : add_vec_int (mword_of_int (PO + 0x26) : mword 64) 2 = mword_of_int (PO + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* ---- 0x28: c.addi16sp sp,32 -- the frame trade back ---- *)
    assert (Hcsp6 : M6 !!! Regidx csp_rs1 = spm).
    { rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hcsp3. }
    assert (HM7sp : M7 !!! Regidx csp_rs1 = sp0up).
    { rewrite /M7. rewrite upd_eq. rewrite Hcsp6. reflexivity. }
    assert (Hupc : pa_stk sp0up 4 = spm).
    { unfold sp0up. apply po_up_cancel. }
    assert (Hwv : add_vec (M6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0up).
    { rewrite Hcsp6. reflexivity. }
    assert (Hpop : M6 !!! Regidx csp_rs1
                   = pa_stk (add_vec (M6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv Hcsp6. symmetry. exact Hupc. }
    assert (Hb1u : pa_stk sp0up 1
                    = add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2u : pa_stk sp0up 2
                    = add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3u : pa_stk sp0up 3
                    = add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite Hcsp3) in "Hpp24".
    iEval (rewrite Hcsp4) in "Hpp16".
    iEval (rewrite Hcsp5) in "Hpp8".
    iEval (rewrite -Hb1u) in "Hpp24".
    iEval (rewrite -Hb2u) in "Hpp16".
    iEval (rewrite -Hb3u) in "Hpp8".
    iEval (rewrite -Hupc) in "Hgap".
    iAssert (stack_own sp0up 4) with "[Hpp24 Hpp16 Hpp8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hpp24"; [by iExists _ |].
      iSplitL "Hpp16"; [by iExists _ |].
      iSplitL "Hpp8"; [by iExists _ |].
      iSplitL "Hgap"; [by iExists _ |].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iPoseProof (poi_28 with "Htext") as "Hi28".
    iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (PO + 0x28)) (mword_of_int 2 : mword 6) M6 av 4 Hpop
              with "Hcg Hpc Hi28 Hframe4 [-]").
    iIntros "Hcg Hpc".
    assert (Hpc2a : add_vec_int (mword_of_int (PO + 0x28) : mword 64) 2 = mword_of_int (PO + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* ---- 0x2a: c.ret : PC := ra0e (low bit cleared) ---- *)
    assert (Hra7 : M7 !!! Regidx (mword_of_int 1 : mword 5) = ra0e).
    { rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. apply upd_eq. }
    iPoseProof (poi_2a with "Htext") as "Hi2a".
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (PO + 0x2a)) (mword_of_int 1 : mword 5) M7 (av + 4)%nat
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2a [-]").
    iIntros "Hcg Hpc".
    iEval (rewrite Hra7) in "Hpc".
    (* ---- convert memory back to the postcondition addresses ---- *)
    assert (Hs00v : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> ms) !!! Regidx (mword_of_int 8 : mword 5) = s00)
      by (rewrite upd_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (HM315 : M3 !!! Regidx (mword_of_int 15 : mword 5) = noff_a5).
    { rewrite /M3 upd_eq /M2 upd_eq. reflexivity. }
    iEval (rewrite Hm310 HM315) in "Hnoff".
    iApply ("Hcont" with "Hpc [Hcg] Hnoff").
    iExists M7. iFrame "Hcg". iPureIntro.
    split; [exact Hra7|].
    repeat split.
    - rewrite /M7. rewrite upd_eq.
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite Hcsp5. reflexivity.
    - rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Htp.
    - (* s2 (x18): never written by the epilogue chain nor by mycpu *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs2.
    - (* s3 (x19) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs3.
    - (* s4 (x20) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs4.
    - (* s5 (x21) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs5.
    - (* s6 (x22) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs6.
    - (* s7 (x23) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs7.
    - (* s8 (x24) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs8.
    - (* s9 (x25) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs9.
    - (* s10 (x26) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs10.
    - (* s11 (x27) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs11.
  Qed.

  Lemma wp_push_off_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (av : nat)
      (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    : wp_push_off_sconf_body γ Φ m av n eb p C.
  Proof.
    cbv beta delta [wp_push_off_sconf_body].
    intros caller_ret Ha0cid Hnbound Hav.
    pose (a0f := mycpu_ret cid_word : mword 64).
    pose (noff := noff_val n : mword 32).
    assert (Ha0 : mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) = a0f)
      by (unfold a0f; rewrite Ha0cid; reflexivity).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (N0 := <[Regidx csp_rs1 := regval_into_reg spd]> m).
    set (N1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (N0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> N0).
    iIntros "Hcg Hcpu #Htext Hpc Hcont".
    iDestruct "Hcpu" as "(%Hbound & Hnoff & Hint & Hcnt & Hproc & HC)".
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hcsp0 : N0 !!! Regidx csp_rs1 = spd) by (rewrite /N0; apply upd_eq).
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x00: c.addi sp,-32 -- the frame push ---- *)
    iPoseProof (poi_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf γ Φ (mword_of_int (PO + 0x00)) (mword_of_int 32 : mword 6) m av 4
              ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24".
    iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8) "Hr8".
    iDestruct "S4" as (vgap) "Hgap".
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".
    assert (Hpp02 : add_vec_int (mword_of_int (PO + 0x00) : mword 64) 2 = mword_of_int (PO + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* ---- 0x02: c.sdsp ra,24(sp) ---- *)
    iPoseProof (poi_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PO + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              N0 (av - 4)%nat vr24
              with "Hcg Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr24". }
    iIntros "Hcg Hpc Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (PO + 0x02) : mword 64) 2 = mword_of_int (PO + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,16(sp) ---- *)
    iPoseProof (poi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PO + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              N0 (av - 4)%nat vr16
              with "Hcg Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr16". }
    iIntros "Hcg Hpc Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (PO + 0x04) : mword 64) 2 = mword_of_int (PO + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.sdsp s1,8(sp) ---- *)
    iPoseProof (poi_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PO + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              N0 (av - 4)%nat vr8
              with "Hcg Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr8". }
    iIntros "Hcg Hpc Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (PO + 0x06) : mword 64) 2 = mword_of_int (PO + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ---- 0x08: c.addi4spn s0,sp,32 ---- *)
    iPoseProof (poi_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (PO + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              N0 (av - 4)%nat
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi08 [-]").
    iIntros "Hcg Hpc".
    assert (Hpp0a : add_vec_int (mword_of_int (PO + 0x08) : mword 64) 2 = mword_of_int (PO + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* ---- 0x0a: csrrci a5,sstatus,2 ---- *)
    iPoseProof (poi_0a with "Htext") as "Hi0a".
    iApply (wp_csrci_sstatus_s_sconf γ Φ (mword_of_int (PO + 0x0a)) (mword_of_int 15 : mword 5) n eb
              N1 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hcnt Hpc Hi0a [-]").
    iIntros (mstatus0) "%Hmsf %Hsie Hcg Hcnt Htcp Hpc".
    iDestruct (intr_count_pos_off with "Hcnt") as "[Hc0 #Havail]".
    set (N2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read mstatus0)]> N1).
    set (N3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (N2 !!! Regidx (mword_of_int 15 : mword 5)))]> N2).
    assert (HN3tp : N3 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /N3 upd_ne; [| vm_compute; discriminate].
      rewrite /N2 upd_ne; [| vm_compute; discriminate].
      rewrite /N1 upd_ne; [| vm_compute; discriminate].
      rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (Hpp0e : add_vec_int (mword_of_int (PO + 0x0a) : mword 64) 4 = mword_of_int (PO + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* ---- 0x0e: c.mv s1,a5 ---- *)
    iPoseProof (poi_0e with "Htext") as "Hi0e".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PO + 0x0e)) (mword_of_int 9 : mword 5) (mword_of_int 15 : mword 5)
              N2 (av - 4)%nat
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0e [-]").
    iIntros "Hcg Hpc".
    assert (Hpp10 : add_vec_int (mword_of_int (PO + 0x0e) : mword 64) 2 = mword_of_int (PO + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* ---- 0x10: jal ra,mycpu (jimm=0xd06); a0 := &mycpu()[cpu] ---- *)
    assert (Hcsp3n : N3 !!! Regidx csp_rs1 = spd).
    { rewrite /N3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /N2. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /N1. rewrite upd_ne; [| vm_compute; discriminate]. exact Hcsp0. }
    assert (Hm0csp10 : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PO + 0x10) : mword 64) 4)]> N3) !!! Regidx csp_rs1 = spd)
      by (rewrite upd_ne; [ exact Hcsp3n | vm_compute; discriminate ]).
    iPoseProof (poi_10 with "Htext") as "Hi10".
    iApply (Mycpu.wp_call_mycpu_sconf_cs γ Φ (mword_of_int (PO + 0x10)) (mword_of_int 0xd06 : mword 21) N3 (av - 4)%nat
 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc Hi10 [-]").
    iIntros (mo1) "Hcg Hpc %Hmo4".
    set (N4 := mo1).
    destruct Hmo4 as [Hmo4cs Hmo4a0].
    destruct Hmo4cs as (Hcsp4 & Htp4 & Hs0_4 & Hs1_4 & Hs2_4 & Hs3_4 & Hs4_4 & Hs5_4 & Hs6_4 & Hs7_4 & Hs8_4 & Hs9_4 & Hs10_4 & Hs11_4).
    set (N5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noff)]> N4).
    assert (HN5tp : N5 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /N5 upd_ne; [| vm_compute; discriminate].
      rewrite Htp4. exact HN3tp. }
    assert (Ha0_10 : N4 !!! Regidx (mword_of_int 10 : mword 5) = a0f).
    { rewrite Hmo4a0 HN3tp. exact Ha0. }
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc14 : ret_pc (add_vec_int (mword_of_int (PO + 0x10) : mword 64) 4)
                    = (mword_of_int (PO + 0x14) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* ---- 0x14: c.lw a5,120(a0) : a5 := noff ---- *)
    assert (Hnoffaddr : N4 !!! Regidx (mword_of_int 10 : mword 5) = a0f) by (rewrite /N4; exact Ha0_10).
    iPoseProof (poi_14 with "Htext") as "Hi14".
    iApply (wp_clw_s_sconf γ Φ (mword_of_int (PO + 0x14)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) N4 (av - 4)%nat noff
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi14 [Hnoff] [-]").
    { iEval (rewrite Hnoffaddr). iExact "Hnoff". }
    iIntros "Hcg Hpc Hnoff".
    assert (Hpp16 : add_vec_int (mword_of_int (PO + 0x14) : mword 64) 2 = mword_of_int (PO + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* ---- 0x16: c.beqz a5, 0x2c ---- *)
    assert (Ha5 : N5 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 noff) by (rewrite /N5; apply upd_eq).
    assert (Hv1 : N0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /N0; rewrite upd_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (Hv8 : N0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /N0; rewrite upd_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (Hv9 : N0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /N0; rewrite upd_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (HcspN5 : N5 !!! Regidx csp_rs1 = spd).
    { rewrite /N5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite Hcsp4. exact Hcsp3n. }
    (* convert held memory to clean addresses/values (shared by both arms) *)
    iEval (rewrite Hnoffaddr) in "Hnoff".
    iEval (rewrite Hcsp0) in "Hr24". iEval (rewrite Hv1) in "Hr24".
    iEval (rewrite Hcsp0) in "Hr16". iEval (rewrite Hv8) in "Hr16".
    iEval (rewrite Hcsp0) in "Hr8". iEval (rewrite Hv9) in "Hr8".
    iPoseProof (poi_16 with "Htext") as "Hi16".
    destruct (eq_vec (sign_extend' 64 noff) zero_reg) eqn:Hcond.
    - (* ===== TAKEN arm: noff == 0 ===== *)
      assert (Hcondf : eq_vec (sign_extend' 64 (noff_val n)) zero_reg = true).
      { change (noff_val n) with noff. exact Hcond. }
      assert (Hn0 : n = 0%nat).
      { pose proof (noff_val_zero n Hbound) as HH. rewrite Hcondf in HH.
        symmetry in HH. apply Nat.eqb_eq in HH. exact HH. }
      subst n.
      iDestruct "Hint" as (iv0) "Hintena".
      iApply (wp_cbeqz_taken_s_sconf γ Φ (mword_of_int (PO + 0x16)) (mword_of_int 11 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) N5 (av - 4)%nat
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rewrite Ha5; exact Hcond)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi16 [-]").
      iNext.
      iIntros "Hcg Hpc".
      assert (Htgt2c : add_vec (mword_of_int (PO + 0x16) : mword 64)
                 (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0")))) = mword_of_int (PO + 0x2c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt2c) in "Hpc".
      (* ---- 0x2c: jal ra,mycpu (jimm=0xcea) ---- *)
      assert (Hm0csp2c : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PO + 0x2c) : mword 64) 4)]> N5) !!! Regidx csp_rs1 = spd)
        by (rewrite upd_ne; [ exact HcspN5 | vm_compute; discriminate ]).
      iPoseProof (poi_2c with "Htext") as "Hi2c".
      iApply (Mycpu.wp_call_mycpu_sconf_cs γ Φ (mword_of_int (PO + 0x2c)) (mword_of_int 0xcea : mword 21) N5 (av - 4)%nat
 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(lia)
                with "Hcg Htext Hpc Hi2c [-]").
      iIntros (mo2) "Hcg Hpc %Hmo6".
      set (N6 := mo2).
      destruct Hmo6 as [Hmo6cs Hmo6a0].
      destruct Hmo6cs as (Hcsp6 & Htp6 & Hs0_6 & Hs1_6 & Hs2_6 & Hs3_6 & Hs4_6 & Hs5_6 & Hs6_6 & Hs7_6 & Hs8_6 & Hs9_6 & Hs10_6 & Hs11_6).
      set (N7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (shift_bits_right (N6 !!! Regidx (mword_of_int 9 : mword 5))
             (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))]> N6).
      set (N8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (N7 !!! Regidx (mword_of_int 15 : mword 5))
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> N7).
      set (storeval32 := (autocast (T := mword)
          (subrange_vec_dec (N8 !!! Regidx (mword_of_int 15 : mword 5)) (Z.sub (Z.mul 4 8) 1) 0) : mword 32)).
      assert (HN8tp : N8 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
      { rewrite /N8 upd_ne; [| vm_compute; discriminate].
        rewrite /N7 upd_ne; [| vm_compute; discriminate].
        rewrite Htp6. exact HN5tp. }
      assert (Ha0_2c : N6 !!! Regidx (mword_of_int 10 : mword 5) = a0f).
      { rewrite Hmo6a0 HN5tp. exact Ha0. }
      assert (Ha0_18t : mycpu_ret (N8 !!! Regidx (mword_of_int 4 : mword 5)) = a0f)
        by (rewrite HN8tp; exact Ha0).
      assert (Hsv32 : storeval32 = po_intena_val mstatus0).
      { rewrite /storeval32 /N8 upd_eq /N7 upd_eq.
        rewrite Hs1_6 /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs1_4 /N3 upd_eq /N2 upd_eq.
        rewrite addv_zero_l. reflexivity. }
      iEval (rewrite upd_eq) in "Hpc".
      assert (Hpc30 : ret_pc (add_vec_int (mword_of_int (PO + 0x2c) : mword 64) 4)
                      = (mword_of_int (PO + 0x30) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc30) in "Hpc".
      (* ---- 0x30: srli a5,s1,1 ---- *)
      iPoseProof (poi_30 with "Htext") as "Hi30".
      iApply (wp_srli4_s_sconf γ Φ (mword_of_int (PO + 0x30)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (mword_of_int 1 : mword 6) N6 (av - 4)%nat
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi30 [-]").
      iIntros "Hcg Hpc".
      assert (Hpc34 : add_vec_int (mword_of_int (PO + 0x30) : mword 64) 4 = mword_of_int (PO + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc34) in "Hpc".
      (* ---- 0x34: andi a5,a5,1 ---- *)
      iPoseProof (poi_34 with "Htext") as "Hi34".
      iApply (wp_candi_s_sconf γ Φ (mword_of_int (PO + 0x34)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6)
                N7 (av - 4)%nat
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi34 [-]").
      iIntros "Hcg Hpc".
      assert (Hpc36 : add_vec_int (mword_of_int (PO + 0x34) : mword 64) 2 = mword_of_int (PO + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc36) in "Hpc".
      (* ---- 0x36: c.sw a5,124(a0) : store intena ---- *)
      assert (Hintaddr : N8 !!! Regidx (mword_of_int 10 : mword 5) = a0f).
      { rewrite /N8. rewrite upd_ne; [| vm_compute; discriminate].
        rewrite /N7. rewrite upd_ne; [| vm_compute; discriminate]. exact Ha0_2c. }
      iPoseProof (poi_36 with "Htext") as "Hi36".
      iApply (wp_csw_s_sconf γ Φ (mword_of_int (PO + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
                (mword_of_int 124 : mword 12) N8 (av - 4)%nat iv0

                with "Hcg Hpc Hi36 [Hintena] [-]").
      { iEval (rewrite Hintaddr). iExact "Hintena". }
      iIntros "Hcg Hpc Hintena".
      iEval (rewrite Hintaddr) in "Hintena".
      assert (Hpc38 : add_vec_int (mword_of_int (PO + 0x36) : mword 64) 2 = mword_of_int (PO + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc38) in "Hpc".
      (* ---- 0x38: c.j 0xbd8 ---- *)
      iPoseProof (poi_38 with "Htext") as "Hi38".
      iApply (wp_cj_s_sconf γ Φ (mword_of_int (PO + 0x38)) (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")))
                N8 (av - 4)%nat
 ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi38 [-]").
      iNext.
      iIntros "Hcg Hpc".
      assert (Htgt18t : add_vec (mword_of_int (PO + 0x38) : mword 64)
                 (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")))) = mword_of_int (PO + 0x18))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt18t) in "Hpc".
      assert (HcspN8 : N8 !!! Regidx csp_rs1 = spd).
      { rewrite /N8. rewrite upd_ne; [| vm_compute; discriminate].
        rewrite /N7. rewrite upd_ne; [| vm_compute; discriminate].
        rewrite Hcsp6. exact HcspN5. }
      (* ---- apply the suffix with ms = N8 ---- *)
      iApply (wp_push_off_suffix_sconf γ Φ N8 (av - 4)%nat noff
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5)) (m !!! Regidx (mword_of_int 9 : mword 5)) vgap
 ltac:(lia)
                with "Hcg Htext Hpc [Hnoff] [Hr24] [Hr16] [Hr8] [Hgap] [-]").
      { iEval (rewrite Ha0_18t). iExact "Hnoff". }
      { iEval (rewrite HcspN8). iExact "Hr24". }
      { iEval (rewrite HcspN8). iExact "Hr16". }
      { iEval (rewrite HcspN8). iExact "Hr8". }
      { iEval (rewrite HcspN8 -Hspd4). iExact "Hgap". }
      iIntros "Hpc Hmfin Hnoff".
      iEval (rewrite Ha0_18t) in "Hnoff".
      iDestruct "Hmfin" as (mfin) "(Hcg & %Hp)".
      destruct Hp as (Hra & Hs0 & Hs1 & Hsp & Htp & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
      assert (Hav4 : (av - 4 + 4)%nat = av) by lia.
      iEval (rewrite Hav4) in "Hcg".
      iApply ("Hcont" $! mstatus0 mfin with "[%] Hcg [Hnoff Hintena Hc0 Hproc HC] Htcp Hpc [%]").
      { exact Hmsf. }
      { (* cpu_own γ (S 0) eb p C *)
        rewrite /cpu_own.
        iSplitR.
        { iPureIntro. change (Z.of_nat (S 0)) with 1%Z. lia. }
        iSplitL "Hnoff".
        { assert (Hstore1 : (autocast (T := mword) (subrange_vec_dec (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = noff_val (S 0)).
          { change noff with (noff_val 0). apply push_storeval_succ. change (Z.of_nat 0) with 0%Z. lia. }
          iEval (rewrite Hstore1) in "Hnoff". iExact "Hnoff". }
        iSplitL "Hintena".
        { assert (Hival : intena_val eb = storeval32).
          { rewrite Hsv32. symmetry. apply po_intena_val_bridge. apply Hsie. reflexivity. }
          iEval (rewrite Hival). iExact "Hintena". }
        iSplitL "Hc0".
        { destruct eb.
          - iApply (intr_count_pack_S_on γ 0 with "Hc0 Havail").
          - iApply (intr_count_pack_S_off γ 0 with "Hc0"). }
        iSplitL "Hproc". { iExact "Hproc". } { iExact "HC". } }
      { unfold callee_saved. repeat split.
        - (* sp *)
          rewrite Hsp HcspN8 /spd /sp0 po_addv_assoc.
          assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                                (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite HAB. apply avi0.
        - (* tp *)
          rewrite Htp.
          rewrite /N8 upd_ne; [| vm_compute; discriminate].
          rewrite /N7 upd_ne; [| vm_compute; discriminate].
          rewrite Htp6.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Htp4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s0 *) exact Hs0.
        - (* s1 *) exact Hs1.
        - (* s2 *)
          rewrite Hs2.
          rewrite /N8 upd_ne; [| vm_compute; discriminate].
          rewrite /N7 upd_ne; [| vm_compute; discriminate].
          rewrite Hs2_6.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs2_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s3 *)
          rewrite Hs3.
          rewrite /N8 upd_ne; [| vm_compute; discriminate].
          rewrite /N7 upd_ne; [| vm_compute; discriminate].
          rewrite Hs3_6.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs3_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s4 *)
          rewrite Hs4.
          rewrite /N8 upd_ne; [| vm_compute; discriminate].
          rewrite /N7 upd_ne; [| vm_compute; discriminate].
          rewrite Hs4_6.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs4_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s5 *)
          rewrite Hs5.
          rewrite /N8 upd_ne; [| vm_compute; discriminate].
          rewrite /N7 upd_ne; [| vm_compute; discriminate].
          rewrite Hs5_6.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs5_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s6 *)
          rewrite Hs6.
          rewrite /N8 upd_ne; [| vm_compute; discriminate].
          rewrite /N7 upd_ne; [| vm_compute; discriminate].
          rewrite Hs6_6.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs6_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s7 *)
          rewrite Hs7.
          rewrite /N8 upd_ne; [| vm_compute; discriminate].
          rewrite /N7 upd_ne; [| vm_compute; discriminate].
          rewrite Hs7_6.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs7_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s8 *)
          rewrite Hs8.
          rewrite /N8 upd_ne; [| vm_compute; discriminate].
          rewrite /N7 upd_ne; [| vm_compute; discriminate].
          rewrite Hs8_6.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs8_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s9 *)
          rewrite Hs9.
          rewrite /N8 upd_ne; [| vm_compute; discriminate].
          rewrite /N7 upd_ne; [| vm_compute; discriminate].
          rewrite Hs9_6.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs9_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s10 *)
          rewrite Hs10.
          rewrite /N8 upd_ne; [| vm_compute; discriminate].
          rewrite /N7 upd_ne; [| vm_compute; discriminate].
          rewrite Hs10_6.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs10_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s11 *)
          rewrite Hs11.
          rewrite /N8 upd_ne; [| vm_compute; discriminate].
          rewrite /N7 upd_ne; [| vm_compute; discriminate].
          rewrite Hs11_6.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs11_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    - (* ===== FALL arm: noff <> 0 ===== *)
      destruct n as [|n'].
      { exfalso. pose proof (noff_val_zero 0 Hbound) as HH.
        change (noff_val 0) with noff in HH. rewrite Hcond in HH. discriminate HH. }
      iRename "Hint" into "Hintena".
      iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (PO + 0x16)) (mword_of_int 11 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) N5 (av - 4)%nat
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rewrite Ha5; exact Hcond)
                with "Hcg Hpc Hi16 [-]").
      iIntros "Hcg Hpc".
      assert (Hpc18 : add_vec_int (mword_of_int (PO + 0x16) : mword 64) 2 = mword_of_int (PO + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc18) in "Hpc".
      assert (Ha0_18f : mycpu_ret (N5 !!! Regidx (mword_of_int 4 : mword 5)) = a0f)
        by (rewrite HN5tp; exact Ha0).
      (* ---- apply the suffix with ms = N5 ---- *)
      iApply (wp_push_off_suffix_sconf γ Φ N5 (av - 4)%nat noff
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5)) (m !!! Regidx (mword_of_int 9 : mword 5)) vgap
 ltac:(lia)
                with "Hcg Htext Hpc [Hnoff] [Hr24] [Hr16] [Hr8] [Hgap] [-]").
      { iEval (rewrite Ha0_18f). iExact "Hnoff". }
      { iEval (rewrite HcspN5). iExact "Hr24". }
      { iEval (rewrite HcspN5). iExact "Hr16". }
      { iEval (rewrite HcspN5). iExact "Hr8". }
      { iEval (rewrite HcspN5 -Hspd4). iExact "Hgap". }
      iIntros "Hpc Hmfin Hnoff".
      iEval (rewrite Ha0_18f) in "Hnoff".
      iDestruct "Hmfin" as (mfin) "(Hcg & %Hp)".
      destruct Hp as (Hra & Hs0 & Hs1 & Hsp & Htp & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
      assert (Hav4 : (av - 4 + 4)%nat = av) by lia.
      iEval (rewrite Hav4) in "Hcg".
      iApply ("Hcont" $! mstatus0 mfin with "[%] Hcg [Hnoff Hintena Hc0 Hproc HC] Htcp Hpc [%]").
      { exact Hmsf. }
      { (* cpu_own γ (S (S n')) eb p C *)
        rewrite /cpu_own.
        iSplitR.
        { iPureIntro. rewrite Nat2Z.inj_succ. lia. }
        iSplitL "Hnoff".
        { assert (Hstoref : (autocast (T := mword) (subrange_vec_dec (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = noff_val (S (S n'))).
          { change noff with (noff_val (S n')). apply push_storeval_succ. exact Hnbound. }
          iEval (rewrite Hstoref) in "Hnoff". iExact "Hnoff". }
        iSplitL "Hintena". { iExact "Hintena". }
        iSplitL "Hc0".
        { destruct eb.
          - iApply (intr_count_pack_S_on γ (S n') with "Hc0 Havail").
          - iApply (intr_count_pack_S_off γ (S n') with "Hc0"). }
        iSplitL "Hproc". { iExact "Hproc". } { iExact "HC". } }
      { unfold callee_saved. repeat split.
        - (* sp *)
          rewrite Hsp HcspN5 /spd /sp0 po_addv_assoc.
          assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                                (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite HAB. apply avi0.
        - (* tp *)
          rewrite Htp.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Htp4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s0 *) exact Hs0.
        - (* s1 *) exact Hs1.
        - (* s2 *)
          rewrite Hs2.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs2_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s3 *)
          rewrite Hs3.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs3_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s4 *)
          rewrite Hs4.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs4_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s5 *)
          rewrite Hs5.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs5_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s6 *)
          rewrite Hs6.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs6_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s7 *)
          rewrite Hs7.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs7_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s8 *)
          rewrite Hs8.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs8_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s9 *)
          rewrite Hs9.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs9_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s10 *)
          rewrite Hs10.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs10_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s11 *)
          rewrite Hs11.
          rewrite /N5 upd_ne; [| vm_compute; discriminate].
          rewrite Hs11_4.
          rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_ne; [| vm_compute; discriminate].
          rewrite /N1 upd_ne; [| vm_compute; discriminate].
          rewrite /N0 upd_ne; [| vm_compute; discriminate]. reflexivity. }
  Qed.


  (* ------------------------------------------------------------------- *)
  (* pop_off over the v2 bundle.  The input disjunct is keyed on the      *)
  (* runtime intena value (the caller converts push_off's ⌜SIE ms⌝-keyed  *)
  (* payload with the intena-bit fact); BOTH cases carry the interrupts-  *)
  (* off token, which uniformly refutes the cap-'1' arm at the csrr       *)
  (* sanity check.  The restore path consumes payload + token through    *)
  (* the x0 csrsi leaf; the other two paths hand the input back.          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_pop_off_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    : wp_pop_off_sconf_body γ Φ m av n eb p C.
  Proof.
    cbv beta delta [wp_pop_off_sconf_body].
    intros pcE ret_tgt Ha0cid Hav.
    pose (a0v := mycpu_ret cid_word : mword 64).
    pose (noffv := noff_val (S n) : mword 32).
    pose (intenav := intena_val eb : mword 32).
    set (nv1 := sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)).
    set (storeval := (autocast (T := mword) (subrange_vec_dec nv1 (Z.sub (Z.mul 4 8) 1) 0) : mword 32)).
    set (a_noff := add_vec a0v (sign_extend' 64 (mword_of_int 120 : mword 12))).
    set (a_int := add_vec a0v (sign_extend' 64 (mword_of_int 124 : mword 12))).
    assert (Ha0 : mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) = a0v)
      by (unfold a0v; rewrite Ha0cid; reflexivity).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    set (P0 := <[Regidx csp_rs1 := regval_into_reg spd]> m).
    set (P1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (P0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> P0).
    iIntros "Hcg Hcpu Htcp #Htext Hpc Hcont".
    iDestruct "Hcpu" as "(%Hbound & Hnoff & Hint & Hcnt & Hproc & HC)".
    assert (Hcoup : neq_vec nv1 zero_reg = false <-> n = 0%nat)
      by (apply pop_nv1_zero_iff; exact Hbound).
    assert (Hnoffpos : zopz0zKzJ_s zero_reg (sign_extend' 64 noffv) = false)
      by (apply pop_noff_pos; exact Hbound).
    iDestruct (intr_count_pos_off with "Hcnt") as "[Htok #Havail]".
    iPoseProof (ppi_00 with "Htext") as "Hi00".
    iPoseProof (ppi_02 with "Htext") as "Hi02".
    iPoseProof (ppi_04 with "Htext") as "Hi04".
    iPoseProof (ppi_06 with "Htext") as "Hi06".
    iPoseProof (ppi_08 with "Htext") as "Hi08".
    iPoseProof (ppi_0c with "Htext") as "Hi0c".
    iPoseProof (ppi_10 with "Htext") as "Hi10".
    iPoseProof (ppi_12 with "Htext") as "Hi12".
    iPoseProof (ppi_14 with "Htext") as "Hi14".
    iPoseProof (ppi_16 with "Htext") as "Hi16".
    iPoseProof (ppi_1a with "Htext") as "Hi1a".
    iPoseProof (ppi_1c with "Htext") as "Hi1c".
    iPoseProof (ppi_1e with "Htext") as "Hi1e".
    assert (Hcsp0 : P0 !!! Regidx csp_rs1 = spd) by (rewrite /P0; apply upd_eq).
    assert (Hspd2 : pa_stk sp0 2 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x00: c.addi sp,-16 -- the frame push ---- *)
    iApply (wp_caddi_sp_push_s_sconf γ Φ pcE (mword_of_int 48) m av 2
              ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (PP + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (vr8 vr0) "[Hr8 Hr0]".
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- 0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PP + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              P0 (av - 2)%nat vr8
              with "Hcg Hpc Hi02 [Hr8] [-]").
    { iEval (rewrite Hcsp0 -Hb1). iExact "Hr8". }
    iIntros "Hcg Hpc Hr8".
    assert (Hpp04 : add_vec_int (mword_of_int (PP + 0x02) : mword 64) 2 = mword_of_int (PP + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PP + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              P0 (av - 2)%nat vr0
              with "Hcg Hpc Hi04 [Hr0] [-]").
    { iEval (rewrite Hcsp0 -Hb2). iExact "Hr0". }
    iIntros "Hcg Hpc Hr0".
    assert (Hpp06 : add_vec_int (mword_of_int (PP + 0x04) : mword 64) 2 = mword_of_int (PP + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.addi4spn s0,sp,4 ---- *)
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (PP + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              P0 (av - 2)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi06 [-]").
    iIntros "Hcg Hpc".
    assert (Hpp08 : add_vec_int (mword_of_int (PP + 0x06) : mword 64) 2 = mword_of_int (PP + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (P0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> P0) with P1.
    (* ---- 0x08: jal ra,mycpu ---- *)
    assert (Hcsp1 : P1 !!! Regidx csp_rs1 = spd)
      by (rewrite /P1 upd_ne; [exact Hcsp0 | vm_compute; discriminate]).
    iApply (Mycpu.wp_call_mycpu_sconf_cs γ Φ (mword_of_int (PP + 0x08)) (mword_of_int 0xc94 : mword 21) P1 (av - 2)%nat
 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc Hi08 [-]").
    iIntros (mo) "Hcg Hpc %Hmo".
    set (Cr := mo).
    destruct Hmo as [Hcs Hmo_a0].
    destruct Hcs as (HcspC & HtpC & Hs0C & Hs1C & Hs2C & Hs3C & Hs4C & Hs5C & Hs6C & Hs7C & Hs8C & Hs9C & Hs10C & Hs11C).
    assert (HtpP1 : P1 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /P1 upd_ne; [| vm_compute; discriminate].
      rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (Ha0C : Cr !!! Regidx (mword_of_int 10 : mword 5) = a0v)
      by (rewrite /Cr Hmo_a0 HtpP1 Ha0; reflexivity).
    assert (HcspC' : Cr !!! Regidx csp_rs1 = spd) by (rewrite /Cr HcspC; exact Hcsp1).
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc0c : ret_pc (add_vec_int (mword_of_int (PP + 0x08) : mword 64) 4)
                    = (mword_of_int (PP + 0x0c) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* ---- 0x0c: csrr a5,sstatus -- the interrupts-off sanity check ---- *)
    iApply (wp_csrr_sstatus_s_sconf γ Φ (mword_of_int (PP + 0x0c)) (mword_of_int 15 : mword 5) Cr (av - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0c [-]").
    iIntros (msr) "%Hmsfr Hhs Hsc Htr Hpc Hfile Harm".
    set (P3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read msr)]> Cr).
    iDestruct "Harm" as "[Hstk Hrep]".
    (* the cap must be at '0': the count token's eighth-'0' refutes the
       '1' arm by ghost agreement *)
    iDestruct "Hrep" as "[[%HSIEr Hq0] | (%HSIEr & Hq1 & Hrest)]".
    2:{ iDestruct (ghost_var_agree with "Htok Hq1") as %Habs.
        exfalso. apply (f_equal (@bv_unsigned _)) in Habs.
        vm_compute in Habs. discriminate. }
    iAssert (sie_cap γ P3 (av - 2)%nat) with "[Hstk Htr Hq0]" as "Hcapsc".
    { iFrame "Hstk Htr". iLeft. iExact "Hq0". }
    iDestruct (sie_cap_gpr_join with "Hhs Hsc Hcapsc Hfile") as "Hcg".
    assert (Hsst2 : neq_vec (and_vec (sstatus_read msr)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false).
    { apply pop_sstatus_clear_neq. rewrite HSIEr. vm_compute. reflexivity. }
    assert (Hpc10 : add_vec_int (mword_of_int (PP + 0x0c) : mword 64) 4 = mword_of_int (PP + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* ---- 0x10: c.andi a5,2 ---- *)
    iApply (wp_candi_s_sconf γ Φ (mword_of_int (PP + 0x10)) (mword_of_int 15 : mword 5) (mword_of_int 2 : mword 6)
              P3 (av - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi10 [-]").
    iIntros "Hcg Hpc".
    set (P4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (P3 !!! Regidx (mword_of_int 15 : mword 5))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> P3).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (P3 !!! Regidx (mword_of_int 15 : mword 5))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> P3) with P4.
    assert (Hpc12 : add_vec_int (mword_of_int (PP + 0x10) : mword 64) 2 = mword_of_int (PP + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* ---- 0x12: c.bnez a5 (falls: interrupts are off) ---- *)
    assert (Ha5P4 : P4 !!! Regidx (mword_of_int 15 : mword 5)
                     = and_vec (sstatus_read msr) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))).
    { rewrite /P4 upd_eq /P3 upd_eq. reflexivity. }
    iApply (wp_cbnez_fall_s_sconf γ Φ (mword_of_int (PP + 0x12)) (mword_of_int 15 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              P4 (av - 2)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5P4; exact Hsst2)
              with "Hcg Hpc Hi12 [-]").
    iIntros "Hcg Hpc".
    assert (Hpc14 : add_vec_int (mword_of_int (PP + 0x12) : mword 64) 2 = mword_of_int (PP + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* ---- 0x14: c.lw a5,120(a0) : a5 := noff ---- *)
    assert (Ha0P4 : P4 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      exact Ha0C. }
    iApply (wp_clw_s_sconf γ Φ (mword_of_int (PP + 0x14)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) P4 (av - 2)%nat noffv
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi14 [Hnoff] [-]").
    { iEval (rewrite Ha0P4). iExact "Hnoff". }
    iIntros "Hcg Hpc Hnoff".
    set (P5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noffv)]> P4).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noffv)]> P4) with P5.
    assert (Hpc16 : add_vec_int (mword_of_int (PP + 0x14) : mword 64) 2 = mword_of_int (PP + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* ---- 0x16: bge x0,a5 (falls: noff >= 1) ---- *)
    assert (Ha5P5 : P5 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 noffv)
      by (rewrite /P5; apply upd_eq).
    iApply (wp_bge_x0_fall_s_sconf γ Φ (mword_of_int (PP + 0x16)) (mword_of_int 0x26 : mword 13) (mword_of_int 15 : mword 5)
              P5 (av - 2)%nat
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5P5; exact Hnoffpos)
              with "Hcg Hpc Hi16 [-]").
    iIntros "Hcg Hpc".
    assert (Hpc1a : add_vec_int (mword_of_int (PP + 0x16) : mword 64) 4 = mword_of_int (PP + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* ---- 0x1a: c.addiw a5,-1 ---- *)
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (PP + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 63 : mword 6)
              P5 (av - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1a [-]").
    iIntros "Hcg Hpc".
    set (P6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (P5 !!! Regidx (mword_of_int 15 : mword 5))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> P5).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (P5 !!! Regidx (mword_of_int 15 : mword 5))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> P5) with P6.
    assert (Hpc1c : add_vec_int (mword_of_int (PP + 0x1a) : mword 64) 2 = mword_of_int (PP + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    assert (Ha5P6 : P6 !!! Regidx (mword_of_int 15 : mword 5) = nv1).
    { rewrite /P6 upd_eq Ha5P5. reflexivity. }
    (* ---- 0x1c: c.sw a5,120(a0) : store noff-1 ---- *)
    assert (Ha0P6 : P6 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_ne; [| vm_compute; discriminate].
      exact Ha0P4. }
    iApply (wp_csw_s_sconf γ Φ (mword_of_int (PP + 0x1c)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) P6 (av - 2)%nat noffv
              with "Hcg Hpc Hi1c [Hnoff] [-]").
    { iEval (rewrite Ha0P6 -Ha0P4). iExact "Hnoff". }
    iIntros "Hcg Hpc Hnoff".
    iEval (rewrite Ha0P6 Ha5P6) in "Hnoff".
    assert (Hpc1e : add_vec_int (mword_of_int (PP + 0x1c) : mword 64) 2 = mword_of_int (PP + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* ---- shared epilogue facts ---- *)
    assert (Hra0P : P0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /P0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs00P : P0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /P0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hcsp0 Hra0P) in "Hr8".
    iEval (rewrite Hcsp0 Hs00P) in "Hr0".
    assert (HcspP6 : P6 !!! Regidx csp_rs1 = spd).
    { rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      exact HcspC'. }
    assert (Hsp0up : add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite /spd /sp0 po_addv_assoc.
      assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
                            (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply avi0. }
    (* ---- 0x1e: c.bnez a5 : noff-1 = 0 ? ---- *)
    destruct (neq_vec nv1 zero_reg) eqn:Hnv.
    - (* noff-1 <> 0: TAKEN to the epilogue at 0x28; no restore *)
      iApply (wp_cbnez_taken_s_sconf γ Φ (mword_of_int (PP + 0x1e)) (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                P6 (av - 2)%nat
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5P6; exact Hnv)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1e [-]").
      iNext.
      iIntros "Hcg Hpc".
      assert (Htgt28 : add_vec (mword_of_int (PP + 0x1e) : mword 64)
                 (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0")))) = mword_of_int (PP + 0x28))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt28) in "Hpc".
      iApply (wp_pop_off_epi_sconf γ Φ P6 (av - 2)%nat
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
                with "Hcg Htext Hpc [Hr8] [Hr0] [-]").
      { iEval (rewrite HcspP6). iExact "Hr8". }
      { iEval (rewrite HcspP6). iExact "Hr0". }
      iIntros (mf) "Hcg Hpc %Hmf".
      assert (Hav2 : (av - 2 + 2)%nat = av) by lia.
      iEval (rewrite Hav2) in "Hcg".
      subst mf.
      (* still nested: neq nv1 0 = true, so n = S n'; the token rides
         through un-flipped, repacked one level lower. *)
      assert (Hn0 : n <> 0%nat).
      { intro Hz. pose proof (proj2 Hcoup Hz) as HH. congruence. }
      destruct n as [|n']; [ contradiction |].
      iApply ("Hcont" $! _ with "Hcg [Hnoff Hint Htok Hproc HC] Hpc [%]").
      { (* cpu_own γ (S n') eb p C *)
        rewrite /cpu_own.
        iSplitR.
        { iPureIntro. rewrite Nat2Z.inj_succ in Hbound |- *. lia. }
        iSplitL "Hnoff".
        { assert (Hdec : noff_val (S n') = storeval).
          { symmetry. rewrite /storeval /nv1. change noffv with (noff_val (S (S n'))).
            apply pop_storeval_pred. exact Hbound. }
          iEval (rewrite Hdec). iExact "Hnoff". }
        iSplitL "Hint". { iExact "Hint". }
        iSplitL "Htok".
        { destruct eb.
          - iApply (intr_count_pack_S_on γ n' with "Htok Havail").
          - iApply (intr_count_pack_S_off γ n' with "Htok"). }
        iSplitL "Hproc". { iExact "Hproc". } { iExact "HC". } }
      unfold callee_saved. repeat split.
      + rewrite upd_eq HcspP6 Hsp0up. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr HtpC. exact HtpP1.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs1C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs2C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs3C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs4C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs5C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs6C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs7C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs8C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs9C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs10C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs11C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    - (* noff-1 = 0: FALL to the intena check at 0x20 *)
      iApply (wp_cbnez_fall_s_sconf γ Φ (mword_of_int (PP + 0x1e)) (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                P6 (av - 2)%nat
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5P6; exact Hnv)
                with "Hcg Hpc Hi1e [-]").
      iIntros "Hcg Hpc".
      assert (Hpc20 : add_vec_int (mword_of_int (PP + 0x1e) : mword 64) 2 = mword_of_int (PP + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc20) in "Hpc".
      (* ---- 0x20: c.lw a5,124(a0) : a5 := intena ---- *)
      iPoseProof (ppi_20 with "Htext") as "Hi20".
      iPoseProof (ppi_22 with "Htext") as "Hi22".
      iApply (wp_clw_s_sconf γ Φ (mword_of_int (PP + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
                (mword_of_int 124 : mword 12) P6 (av - 2)%nat intenav
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi20 [Hint] [-]").
      { iEval (rewrite Ha0P6). iExact "Hint". }
      iIntros "Hcg Hpc Hint".
      iEval (rewrite Ha0P6) in "Hint".
      set (P7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 intenav)]> P6).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 intenav)]> P6) with P7.
      assert (Hpc22 : add_vec_int (mword_of_int (PP + 0x20) : mword 64) 2 = mword_of_int (PP + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc22) in "Hpc".
      assert (Ha5P7 : P7 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 intenav)
        by (rewrite /P7; apply upd_eq).
      assert (HcspP7 : P7 !!! Regidx csp_rs1 = spd)
        by (rewrite /P7 upd_ne; [exact HcspP6 | vm_compute; discriminate]).
      (* ---- 0x22: c.beqz a5 : intena = 0 ? ---- *)
      destruct (eq_vec (sign_extend' 64 intenav) zero_reg) eqn:Hie2.
      + (* intena = 0: TAKEN to the epilogue; no restore *)
        assert (HneqF : neq_vec (sign_extend' 64 intenav) zero_reg = false)
          by (unfold neq_vec; rewrite Hie2; reflexivity).
        iApply (wp_cbeqz_taken_s_sconf γ Φ (mword_of_int (PP + 0x22)) (mword_of_int 3 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                  P7 (av - 2)%nat
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite Ha5P7; exact Hie2)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi22 [-]").
        iNext.
        iIntros "Hcg Hpc".
        assert (Htgt28' : add_vec (mword_of_int (PP + 0x22) : mword 64)
                   (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")))) = mword_of_int (PP + 0x28))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt28') in "Hpc".
        iApply (wp_pop_off_epi_sconf γ Φ P7 (av - 2)%nat
                  (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
                  with "Hcg Htext Hpc [Hr8] [Hr0] [-]").
        { iEval (rewrite HcspP7). iExact "Hr8". }
        { iEval (rewrite HcspP7). iExact "Hr0". }
        iIntros (mf) "Hcg Hpc %Hmf".
        assert (Hav2 : (av - 2 + 2)%nat = av) by lia.
        iEval (rewrite Hav2) in "Hcg".
        subst mf.
        assert (Hn0B : n = 0%nat) by (apply (proj1 Hcoup); unfold neq_vec in *; congruence).
        subst n.
        assert (Hebf : eb = false).
        { assert (Hie2' : eq_vec (sign_extend' 64 (intena_val eb)) zero_reg = true)
            by (change (intena_val eb) with intenav; exact Hie2).
          pose proof (intena_val_zero eb) as HH. rewrite Hie2' in HH.
          destruct eb; [discriminate HH | reflexivity]. }
        subst eb.
        iApply ("Hcont" $! _ with "Hcg [Hnoff Hint Htok Hproc HC] Hpc [%]").
        { rewrite /cpu_own.
          iSplitR. { iPureIntro. change (Z.of_nat 0) with 0%Z. lia. }
          iSplitL "Hnoff".
          { assert (Hdec : noff_val 0 = storeval).
            { symmetry. rewrite /storeval /nv1. change noffv with (noff_val 1).
              apply pop_storeval_pred. exact Hbound. }
            iEval (rewrite Hdec). iExact "Hnoff". }
          iSplitL "Hint". { iExists intenav. iExact "Hint". }
          iSplitL "Htok". { rewrite /intr_count. iExact "Htok". }
          iSplitL "Hproc". { iExact "Hproc". } { iExact "HC". } }
        unfold callee_saved. repeat split.
        * rewrite upd_eq HcspP7 Hsp0up. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr HtpC. exact HtpP1.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs1C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs2C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs3C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs4C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs5C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs6C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs7C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs8C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs9C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs10C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs11C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.

      + (* intena <> 0: FALL into the restore *)
        assert (HneqT : neq_vec (sign_extend' 64 intenav) zero_reg = true)
          by (unfold neq_vec; rewrite Hie2; reflexivity).
        iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (PP + 0x22)) (mword_of_int 3 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                  P7 (av - 2)%nat
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite Ha5P7; exact Hie2)
                  with "Hcg Hpc Hi22 [-]").
        iIntros "Hcg Hpc".
        assert (Hpc24 : add_vec_int (mword_of_int (PP + 0x22) : mword 64) 2 = mword_of_int (PP + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc24) in "Hpc".
        assert (Hn0C : n = 0%nat).
        { apply (proj1 Hcoup). unfold neq_vec in *. congruence. }
        subst n.
        assert (Hebt : eb = true).
        { assert (Hie2' : eq_vec (sign_extend' 64 (intena_val eb)) zero_reg = false)
            by (change (intena_val eb) with intenav; exact Hie2).
          pose proof (intena_val_zero eb) as HH. rewrite Hie2' in HH.
          destruct eb; [reflexivity | discriminate HH]. }
        subst eb.
        assert (Htcseq : trap_csrs_pay 0 true = trap_csrs) by reflexivity.
        iEval (rewrite Htcseq) in "Htcp".
        (* ---- 0x24: csrsi sstatus,2 (rd = x0) -- the restore ---- *)
        iPoseProof (ppi_24 with "Htext") as "Hi24".
        iApply (wp_csrsi_sstatus_x0_s_sconf γ Φ (mword_of_int (PP + 0x24)) P7 (av - 2)%nat
                  with "Hcg [Htok] Htcp Hpc Hi24 [-]").
        { iApply (intr_count_pack_S_on γ 0 with "Htok Havail"). }
        iIntros (msi) "%Hmsfi Hcg Hcnt0 Hpc".
        assert (Hpc28 : add_vec_int (mword_of_int (PP + 0x24) : mword 64) 4 = mword_of_int (PP + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc28) in "Hpc".
        iApply (wp_pop_off_epi_sconf γ Φ P7 (av - 2)%nat
                  (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
                  with "Hcg Htext Hpc [Hr8] [Hr0] [-]").
        { iEval (rewrite HcspP7). iExact "Hr8". }
        { iEval (rewrite HcspP7). iExact "Hr0". }
        iIntros (mf) "Hcg Hpc %Hmf".
        assert (Hav2 : (av - 2 + 2)%nat = av) by lia.
        iEval (rewrite Hav2) in "Hcg".
        subst mf.
        iApply ("Hcont" $! _ with "Hcg [Hnoff Hint Hcnt0 Hproc HC] Hpc [%]").
        { rewrite /cpu_own.
          iSplitR. { iPureIntro. change (Z.of_nat 0) with 0%Z. lia. }
          iSplitL "Hnoff".
          { assert (Hdec : noff_val 0 = storeval).
            { symmetry. rewrite /storeval /nv1. change noffv with (noff_val 1).
              apply pop_storeval_pred. exact Hbound. }
            iEval (rewrite Hdec). iExact "Hnoff". }
          iSplitL "Hint". { iExists intenav. iExact "Hint". }
          iSplitL "Hcnt0". { iExact "Hcnt0". }
          iSplitL "Hproc". { iExact "Hproc". } { iExact "HC". } }
        unfold callee_saved. repeat split.
        * rewrite upd_eq HcspP7 Hsp0up. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr HtpC. exact HtpP1.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs1C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs2C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs3C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs4C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs5C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs6C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs7C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs8C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs9C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs10C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs11C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.

  Qed.

End ProofPushOff.

End PushOffProof.
