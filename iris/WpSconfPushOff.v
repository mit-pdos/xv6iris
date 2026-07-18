(* WpSconfPushOff.v: push_off over the SIE-agnostic v2 bundle (stage 8).
   This file holds the SUFFIX (PO+0x18: second mycpu call, the noff
   increment, the epilogue frame-trade and c.ret) -- the shared tail of
   both branch arms -- and (next) the main lemma with the prologue, the
   fused csrrci flip, and the intena arm. *)
Require Import WpSmodeLeafBase.
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpLoad WpLeafCommon WpGpr MinstretInv InstrBytes WpMmodeLeafBase.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree PtTreeAdue KptPt.
Require Import SmodeCore WpSmodeGpr WpMmodeJal.
Require Import KptTree SmodeCorePt WpSmodePtLeaves SRegime.
Require Import StackOwn CalleeSaved WpSmodeSret AlignBits KernelText.
Require Import WpIntrBits WpIntrCore IntrDefs WpIntrInv WpSmodeIntr.
Require Import WpAuipc VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfCsr.
Require Import WpGprCsrwCommon KernelRvcDecode WpMycpu WpCallMycpu WpSconfMycpu WpPushOffTop.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation PO := KernelSyms.push_off.

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


(* the value push_off stores into intena: bit 1 (SIE) of the saved
   sstatus view, extracted by srli/andi -- spelled operationally, as the
   instruction chain computes it. *)
Definition po_intena_val (ms : mword 64) : mword 32 :=
  (autocast (T := mword)
     (subrange_vec_dec
        (and_vec (shift_bits_right (sstatus_read ms)
                    (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
        (Z.sub (Z.mul 4 8) 1) 0) : mword 32).

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

Section WpSconfPushOff.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_push_off_suffix_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (ms : gmap regidx (mword 64))
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
    let cret_tgt := update_vec_dec (add_vec ra0e (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    eq_vec (access_vec_dec cret_tgt 0) ('b"0") = true ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn ms -∗
    tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is P -∗ gpr_file ms -∗
    stack_own (pa_stk spm kv_frame_slots) 2 -∗
    a8_noff ↦₄ noff -∗
    a8_p24 ↦₈ ra0e -∗
    a8_p16 ↦₈ s00e -∗
    a8_p8 ↦₈ s10e -∗
    spm ↦₈ vgap -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      tlb_inv_pt root_ppn -∗
      pc_is cret_tgt -∗
      (∃ mfin, gpr_file mfin ∗ sie_cap γ root_ppn mfin ∗ ⌜ mfin !!! Regidx (mword_of_int 1 : mword 5) = ra0e /\
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
      stack_own (pa_stk spm kv_frame_slots) 2 -∗
      stack_own (pa_stk sp0up kv_frame_slots) 4 -∗
      a8_noff ↦₄ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros P spm a0v a8_noff a8_p24 a8_p16 a8_p8 sp0up noff_a5 storeval cret_tgt Hret0.
    set (s00 := ms !!! Regidx (mword_of_int 8 : mword 5)).
    assert (Hm0sp : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> ms) !!! Regidx csp_rs1 = spm)
      by (rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
    iIntros "Hsc Hhs Hcap Htlbinv #Htext Hpc Hfile Hdeep2 Hnoff Hpp24 Hpp16 Hpp8 Hgap Hcont".
    iPoseProof (poi_18 with "Htext") as "Hi18".
    iApply (wp_call_mycpu_sconf_cs γ root_ppn Φ P (mword_of_int 0xcfe : mword 21) ms
 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              with "Hsc Hhs Hcap Htlbinv Htext Hpc Hfile Hi18 Hdeep2 [-]").
    iIntros (mo) "Hhs Hsc Hcap Htlbinv Hpc Hfile %Hmo Hdeep2".
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
    iEval (rewrite lookup_total_insert) in "Hpc".
    assert (Hpc1c : update_vec_dec (add_vec (add_vec_int P 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (PO + 0x1c) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    (* ---- 0x1c: c.lw a5,120(a0) : a5 := zext32(noff) ---- *)
    assert (Hm110 : M1 !!! Regidx (mword_of_int 10 : mword 5) = a0v) by exact Hmo_a0.
    iPoseProof (poi_1c with "Htext") as "Hi1c".
    iApply (wp_clw_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x1c)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) M1 noff
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi1c [Hnoff] [-]").
    { iEval (rewrite Hm110). iExact "Hnoff". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hnoff".
    iEval (rewrite Hm110) in "Hnoff".
    assert (Hpc1e : add_vec_int (mword_of_int (PO + 0x1c) : mword 64) 2 = mword_of_int (PO + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* ---- 0x1e: c.addiw a5,a5,1 : a5 := sext32(noff+1) ---- *)
    iPoseProof (poi_1e with "Htext") as "Hi1e".
    iApply (wp_caddiw_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x1e)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6)
              M2   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi1e [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    assert (Hpc20 : add_vec_int (mword_of_int (PO + 0x1e) : mword 64) 2 = mword_of_int (PO + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc20) in "Hpc".
    (* ---- 0x20: c.sw a5,120(a0) : store noff+1 ---- *)
    assert (Hm310 : M3 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hmo_a0. }
    iPoseProof (poi_20 with "Htext") as "Hi20".
    iApply (wp_csw_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) M3 noff 

              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi20 [Hnoff] [-]").
    { iEval (rewrite Hm310). iExact "Hnoff". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hnoff".
    assert (Hpc22 : add_vec_int (mword_of_int (PO + 0x20) : mword 64) 2 = mword_of_int (PO + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* ---- 0x22: c.ldsp ra,24(sp) : ra := ra0e ---- *)
    assert (Hcsp3 : M3 !!! Regidx csp_rs1 = spm).
    { rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hcsp. }
    iPoseProof (poi_22 with "Htext") as "Hi22".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x22)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              M3 ra0e
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi22 [Hpp24] [-]").
    { iEval (rewrite Hcsp3). iExact "Hpp24". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hpp24".
    assert (Hpc24 : add_vec_int (mword_of_int (PO + 0x22) : mword 64) 2 = mword_of_int (PO + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    (* ---- 0x24: c.ldsp s0,16(sp) : s0 := s00e ---- *)
    assert (Hcsp4 : M4 !!! Regidx csp_rs1 = spm).
    { rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hcsp3. }
    iPoseProof (poi_24 with "Htext") as "Hi24".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x24)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              M4 s00e
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi24 [Hpp16] [-]").
    { iEval (rewrite Hcsp4). iExact "Hpp16". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hpp16".
    assert (Hpc26 : add_vec_int (mword_of_int (PO + 0x24) : mword 64) 2 = mword_of_int (PO + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    (* ---- 0x26: c.ldsp s1,8(sp) : s1 := s10e ---- *)
    assert (Hcsp5 : M5 !!! Regidx csp_rs1 = spm).
    { rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hcsp4. }
    iPoseProof (poi_26 with "Htext") as "Hi26".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x26)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              M5 s10e
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi26 [Hpp8] [-]").
    { iEval (rewrite Hcsp5). iExact "Hpp8". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hpp8".
    assert (Hpc28 : add_vec_int (mword_of_int (PO + 0x26) : mword 64) 2 = mword_of_int (PO + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* ---- 0x28: c.addi16sp sp,32 -- the frame trade back ---- *)
    assert (Hcsp6 : M6 !!! Regidx csp_rs1 = spm).
    { rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hcsp3. }
    assert (HM7sp : M7 !!! Regidx csp_rs1 = sp0up).
    { rewrite /M7. rewrite lookup_total_insert. rewrite Hcsp6. reflexivity. }
    assert (Hupc : pa_stk sp0up 4 = spm).
    { unfold sp0up. apply po_up_cancel. }
    assert (Hup : M6 !!! Regidx csp_rs1 = pa_stk (M7 !!! Regidx csp_rs1) 4).
    { rewrite Hcsp6 HM7sp Hupc. reflexivity. }
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
    iPoseProof (poi_28 with "Htext") as "Hi28".
    iApply (wp_caddi16sp_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x28)) (mword_of_int 2 : mword 6) M6
              (stack_own (pa_stk sp0up kv_frame_slots) 4)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi28 [Hframe4] [-]").
    { iIntros "Hcap".
      iAssert (stack_own (M7 !!! Regidx csp_rs1) 4) with "[Hframe4]" as "Hframe4".
      { rewrite HM7sp. iExact "Hframe4". }
      iDestruct (sie_cap_move_up γ root_ppn M6 M7 4 Hup with "Hframe4 Hcap") as "[Hcap Hdeep4]".
      iEval (rewrite HM7sp) in "Hdeep4". iFrame "Hcap Hdeep4". }
    iIntros "Hhs Hsc Hcap Hdeep4 Htlbinv Hpc Hfile".
    assert (Hpc2a : add_vec_int (mword_of_int (PO + 0x28) : mword 64) 2 = mword_of_int (PO + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* ---- 0x2a: c.ret : PC := ra0e (low bit cleared) ---- *)
    assert (Hra7 : M7 !!! Regidx (mword_of_int 1 : mword 5) = ra0e).
    { rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. apply lookup_total_insert. }
    iPoseProof (poi_2a with "Htext") as "Hi2a".
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x2a)) (mword_of_int 1 : mword 5) M7
 
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra7; exact Hret0)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi2a [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    iEval (rewrite Hra7) in "Hpc".
    (* ---- convert memory back to the postcondition addresses ---- *)
    assert (Hs00v : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> ms) !!! Regidx (mword_of_int 8 : mword 5) = s00)
      by (rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (HM315 : M3 !!! Regidx (mword_of_int 15 : mword 5) = noff_a5).
    { rewrite /M3 lookup_total_insert /M2 lookup_total_insert. reflexivity. }
    iEval (rewrite Hm310 HM315) in "Hnoff".
    iApply ("Hcont" with "Hhs Hsc Htlbinv Hpc [Hfile Hcap] Hdeep2 Hdeep4 Hnoff").
    iExists M7. iFrame "Hfile Hcap". iPureIntro. split; [exact Hra7|].
    repeat split.
    - rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. apply lookup_total_insert.
    - rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. apply lookup_total_insert.
    - rewrite /M7. rewrite lookup_total_insert.
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hcsp5. reflexivity.
    - rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Htp.
    - (* s2 (x18): never written by the epilogue chain nor by mycpu *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs2.
    - (* s3 (x19) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs3.
    - (* s4 (x20) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs4.
    - (* s5 (x21) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs5.
    - (* s6 (x22) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs6.
    - (* s7 (x23) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs7.
    - (* s8 (x24) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs8.
    - (* s9 (x25) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs9.
    - (* s10 (x26) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs10.
    - (* s11 (x27) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs11.
  Qed.

  Lemma wp_push_off_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64))
      (noff intena_old : mword 32) (a0f : mword 64)
      :
    let sp0 := m !!! Regidx csp_rs1 in
    (* push_off's mstatus0-dependent register chain N2..N8 + storeval32 (which
       read [sstatus_read mstatus0]) are reconstructed inside the proof over the
       unbundled mstatus0; the statement stays mstatus0-free. *)
    let noff_a5 := sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 noff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
    let noff_store := (autocast (T := mword) (subrange_vec_dec noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let a_noff := add_vec a0f (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a_intena := add_vec a0f (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    let caller_ret := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    eq_vec (access_vec_dec caller_ret 0) ('b"0") = true ->
    mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) = a0f ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int (PO + 0x00) : mword 64) -∗ gpr_file m -∗
    (* the DEEP custody: the top 4 slots feed the prologue's frame trade,
       the deeper 2 ride for the mycpu calls at the moved sp. *)
    stack_own (pa_stk sp0 kv_frame_slots) 6 -∗
    a_noff ↦₄ noff -∗
    a_intena ↦₄ intena_old -∗
    ( ∀ (ms : mword 64) (mfin : gmap regidx (mword 64)),
      ⌜ sconf_ms_facts ms ⌝ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn mfin -∗
      tlb_inv_pt root_ppn -∗
      pc_is caller_ret -∗
      gpr_file mfin -∗
      ⌜ callee_saved m mfin ⌝ -∗
      stack_own (pa_stk sp0 kv_frame_slots) 6 -∗
      a_noff ↦₄ noff_store -∗
      a_intena ↦₄ (if eq_vec (sign_extend' 64 noff) zero_reg
                   then po_intena_val ms else intena_old) -∗
      ( ⌜ _get_Mstatus_SIE ms = ('b"0" : mword 1) ⌝
      ∨ (⌜ _get_Mstatus_SIE ms = ('b"1" : mword 1) ⌝ ∗
         (∃ handler : mword 64,
            intr_inv γ handler root_ppn MENVCFG_S ∗
            ▷ intr_handler_spec handler root_ppn MENVCFG_S) ∗
         (∃ v : mword 64, sepc ↦ᵣ v) ∗
         (∃ v : mword 64, scause ↦ᵣ v) ∗
         (∃ v : mword 64, stval ↦ᵣ v)) ) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 noff_a5 noff_store a_noff a_intena caller_ret Hcret0 Ha0.
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (N0 := <[Regidx csp_rs1 := regval_into_reg spd]> m).
    set (N1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (N0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> N0).
    iIntros "Hsc Hhs Hcap Htlbinv #Htext Hpc Hfile Hdeep6 Hnoff Hintena Hcont".
    (* split the deep custody: the top 4 feed the prologue's frame trade,
       the deeper 2 ride for the mycpu calls at the moved sp. *)
    iDestruct (stack_own_split_1 (pa_stk sp0 kv_frame_slots) 4 6 ltac:(lia)
                 with "Hdeep6") as "[Hd4 Hdeep2]".
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hcsp0 : N0 !!! Regidx csp_rs1 = spd) by (rewrite /N0; apply lookup_total_insert).
    assert (Hd2b : pa_stk (pa_stk sp0 kv_frame_slots) 4 = pa_stk spd kv_frame_slots)
      by (rewrite -Hspd4 !pa_stk_assoc; f_equal; lia).
    iEval (rewrite Hd2b) in "Hdeep2".
    assert (HspN0 : N0 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4)
      by (rewrite Hcsp0 Hspd4; reflexivity).
    (* ---- 0x00: c.addi sp,-32 -- the frame trade ---- *)
    iPoseProof (poi_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x00)) (mword_of_int 32 : mword 6) m
              (stack_own sp0 4)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi00 [Hd4] [-]").
    { iIntros "Hcap".
      iDestruct (sie_cap_move_down γ root_ppn m N0 4 HspN0 with "Hd4 Hcap") as "[Hcap Hframe]".
      iFrame "Hcap Hframe". }
    iIntros "Hhs Hsc Hcap Hframe Htlbinv Hpc Hfile".
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
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              N0 vr24
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi02 [Hr24] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr24". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (PO + 0x02) : mword 64) 2 = mword_of_int (PO + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,16(sp) ---- *)
    iPoseProof (poi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              N0 vr16
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi04 [Hr16] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr16". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (PO + 0x04) : mword 64) 2 = mword_of_int (PO + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.sdsp s1,8(sp) ---- *)
    iPoseProof (poi_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              N0 vr8
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi06 [Hr8] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr8". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (PO + 0x06) : mword 64) 2 = mword_of_int (PO + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ---- 0x08: c.addi4spn s0,sp,32 ---- *)
    iPoseProof (poi_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              N0
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    assert (Hpp0a : add_vec_int (mword_of_int (PO + 0x08) : mword 64) 2 = mword_of_int (PO + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* ---- 0x0a: csrrci a5,sstatus,2 ---- *)
    iPoseProof (poi_0a with "Htext") as "Hi0a".
    iApply (wp_csrci_sstatus_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x0a)) (mword_of_int 15 : mword 5)
              N1
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi0a [-]").
    iIntros (mstatus0) "%Hmsf Hhs Hsc Hcap Htlbinv Hpc Hfile Hpayload".
    set (N2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read mstatus0)]> N1).
    set (N3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (N2 !!! Regidx (mword_of_int 15 : mword 5)))]> N2).
    assert (HN3tp : N3 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (Hpp0e : add_vec_int (mword_of_int (PO + 0x0a) : mword 64) 4 = mword_of_int (PO + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* ---- 0x0e: c.mv s1,a5 ---- *)
    iPoseProof (poi_0e with "Htext") as "Hi0e".
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x0e)) (mword_of_int 9 : mword 5) (mword_of_int 15 : mword 5)
              N2
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi0e [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    assert (Hpp10 : add_vec_int (mword_of_int (PO + 0x0e) : mword 64) 2 = mword_of_int (PO + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* ---- 0x10: jal ra,mycpu (jimm=0xd06); a0 := &mycpu()[cpu] ---- *)
    assert (Hcsp3n : N3 !!! Regidx csp_rs1 = spd).
    { rewrite /N3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /N2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /N1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hcsp0. }
    assert (Hm0csp10 : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PO + 0x10) : mword 64) 4)]> N3) !!! Regidx csp_rs1 = spd)
      by (rewrite lookup_total_insert_ne; [ exact Hcsp3n | vm_compute; discriminate ]).
    iPoseProof (poi_10 with "Htext") as "Hi10".
    iApply (wp_call_mycpu_sconf_cs γ root_ppn Φ (mword_of_int (PO + 0x10)) (mword_of_int 0xd06 : mword 21) N3
 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              with "Hsc Hhs Hcap Htlbinv Htext Hpc Hfile Hi10 [Hdeep2] [-]").
    { iEval (rewrite Hcsp3n). iExact "Hdeep2". }
    iIntros (mo1) "Hhs Hsc Hcap Htlbinv Hpc Hfile %Hmo4 Hdeep2".
    set (N4 := mo1).
    destruct Hmo4 as [Hmo4cs Hmo4a0].
    destruct Hmo4cs as (Hcsp4 & Htp4 & Hs0_4 & Hs1_4 & Hs2_4 & Hs3_4 & Hs4_4 & Hs5_4 & Hs6_4 & Hs7_4 & Hs8_4 & Hs9_4 & Hs10_4 & Hs11_4).
    set (N5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noff)]> N4).
    assert (HN5tp : N5 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Htp4. exact HN3tp. }
    assert (Ha0_10 : N4 !!! Regidx (mword_of_int 10 : mword 5) = a0f).
    { rewrite Hmo4a0 HN3tp. exact Ha0. }
    iEval (rewrite Hcsp3n) in "Hdeep2".
    iEval (rewrite lookup_total_insert) in "Hpc".
    assert (Hpc14 : update_vec_dec (add_vec (add_vec_int (mword_of_int (PO + 0x10) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (PO + 0x14) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* ---- 0x14: c.lw a5,120(a0) : a5 := noff ---- *)
    assert (Hnoffaddr : N4 !!! Regidx (mword_of_int 10 : mword 5) = a0f) by (rewrite /N4; exact Ha0_10).
    iPoseProof (poi_14 with "Htext") as "Hi14".
    iApply (wp_clw_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x14)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) N4 noff
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi14 [Hnoff] [-]").
    { iEval (rewrite Hnoffaddr). iExact "Hnoff". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hnoff".
    assert (Hpp16 : add_vec_int (mword_of_int (PO + 0x14) : mword 64) 2 = mword_of_int (PO + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* ---- 0x16: c.beqz a5, 0x2c ---- *)
    assert (Ha5 : N5 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 noff) by (rewrite /N5; apply lookup_total_insert).
    assert (Hv1 : N0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /N0; rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (Hv8 : N0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /N0; rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (Hv9 : N0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /N0; rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (HcspN5 : N5 !!! Regidx csp_rs1 = spd).
    { rewrite /N5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hcsp4. exact Hcsp3n. }
    (* convert held memory to clean addresses/values (shared by both arms) *)
    iEval (rewrite Hnoffaddr) in "Hnoff".
    iEval (rewrite Hcsp0) in "Hr24". iEval (rewrite Hv1) in "Hr24".
    iEval (rewrite Hcsp0) in "Hr16". iEval (rewrite Hv8) in "Hr16".
    iEval (rewrite Hcsp0) in "Hr8". iEval (rewrite Hv9) in "Hr8".
    iPoseProof (poi_16 with "Htext") as "Hi16".
    destruct (eq_vec (sign_extend' 64 noff) zero_reg) eqn:Hcond.
    - (* ===== TAKEN arm: noff == 0 ===== *)
      iApply (wp_cbeqz_taken_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x16)) (mword_of_int 11 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) N5
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rewrite Ha5; exact Hcond)
                ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi16 [-]").
      iNext.
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      assert (Htgt2c : add_vec (mword_of_int (PO + 0x16) : mword 64)
                 (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0")))) = mword_of_int (PO + 0x2c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt2c) in "Hpc".
      (* ---- 0x2c: jal ra,mycpu (jimm=0xcea) ---- *)
      assert (Hm0csp2c : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PO + 0x2c) : mword 64) 4)]> N5) !!! Regidx csp_rs1 = spd)
        by (rewrite lookup_total_insert_ne; [ exact HcspN5 | vm_compute; discriminate ]).
      iPoseProof (poi_2c with "Htext") as "Hi2c".
      iApply (wp_call_mycpu_sconf_cs γ root_ppn Φ (mword_of_int (PO + 0x2c)) (mword_of_int 0xcea : mword 21) N5
 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Htext Hpc Hfile Hi2c [Hdeep2] [-]").
      { iEval (rewrite HcspN5). iExact "Hdeep2". }
      iIntros (mo2) "Hhs Hsc Hcap Htlbinv Hpc Hfile %Hmo6 Hdeep2".
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
      { rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Htp6. exact HN5tp. }
      assert (Ha0_2c : N6 !!! Regidx (mword_of_int 10 : mword 5) = a0f).
      { rewrite Hmo6a0 HN5tp. exact Ha0. }
      assert (Ha0_18t : mycpu_ret (N8 !!! Regidx (mword_of_int 4 : mword 5)) = a0f)
        by (rewrite HN8tp; exact Ha0).
      assert (Hsv32 : storeval32 = po_intena_val mstatus0).
      { rewrite /storeval32 /N8 lookup_total_insert /N7 lookup_total_insert.
        rewrite Hs1_6 /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hs1_4 /N3 lookup_total_insert /N2 lookup_total_insert.
        rewrite addv_zero_l. reflexivity. }
      iEval (rewrite HcspN5) in "Hdeep2".
      iEval (rewrite lookup_total_insert) in "Hpc".
      assert (Hpc30 : update_vec_dec (add_vec (add_vec_int (mword_of_int (PO + 0x2c) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                      = (mword_of_int (PO + 0x30) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc30) in "Hpc".
      (* ---- 0x30: srli a5,s1,1 ---- *)
      iPoseProof (poi_30 with "Htext") as "Hi30".
      iApply (wp_srli4_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x30)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (mword_of_int 1 : mword 6) N6
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi30 [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      assert (Hpc34 : add_vec_int (mword_of_int (PO + 0x30) : mword 64) 4 = mword_of_int (PO + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc34) in "Hpc".
      (* ---- 0x34: andi a5,a5,1 ---- *)
      iPoseProof (poi_34 with "Htext") as "Hi34".
      iApply (wp_candi_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x34)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6)
                N7
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi34 [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      assert (Hpc36 : add_vec_int (mword_of_int (PO + 0x34) : mword 64) 2 = mword_of_int (PO + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc36) in "Hpc".
      (* ---- 0x36: c.sw a5,124(a0) : store intena ---- *)
      assert (Hintaddr : N8 !!! Regidx (mword_of_int 10 : mword 5) = a0f).
      { rewrite /N8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /N7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Ha0_2c. }
      iPoseProof (poi_36 with "Htext") as "Hi36".
      iApply (wp_csw_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
                (mword_of_int 124 : mword 12) N8 intena_old

                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi36 [Hintena] [-]").
      { iEval (rewrite Hintaddr). iExact "Hintena". }
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hintena".
      iEval (rewrite Hintaddr) in "Hintena".
      assert (Hpc38 : add_vec_int (mword_of_int (PO + 0x36) : mword 64) 2 = mword_of_int (PO + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc38) in "Hpc".
      (* ---- 0x38: c.j 0xbd8 ---- *)
      iPoseProof (poi_38 with "Htext") as "Hi38".
      iApply (wp_cj_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x38)) (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")))
                N8
 ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi38 [-]").
      iNext.
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      assert (Htgt18t : add_vec (mword_of_int (PO + 0x38) : mword 64)
                 (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")))) = mword_of_int (PO + 0x18))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt18t) in "Hpc".
      assert (HcspN8 : N8 !!! Regidx csp_rs1 = spd).
      { rewrite /N8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /N7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hcsp6. exact HcspN5. }
      (* ---- apply the suffix with ms = N8 ---- *)
      iApply (wp_push_off_suffix_sconf γ root_ppn Φ N8 noff
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5)) (m !!! Regidx (mword_of_int 9 : mword 5)) vgap
 Hcret0
                with "Hsc Hhs Hcap Htlbinv Htext Hpc Hfile [Hdeep2] [Hnoff] [Hr24] [Hr16] [Hr8] [Hgap] [-]").
      { iEval (rewrite HcspN8). iExact "Hdeep2". }
      { iEval (rewrite Ha0_18t). iExact "Hnoff". }
      { iEval (rewrite HcspN8). iExact "Hr24". }
      { iEval (rewrite HcspN8). iExact "Hr16". }
      { iEval (rewrite HcspN8). iExact "Hr8". }
      { iEval (rewrite HcspN8 -Hspd4). iExact "Hgap". }
      iIntros "Hhs Hsc Htlbinv Hpc Hmfin Hdeep2 Hdeep4 Hnoff".
      iEval (rewrite Ha0_18t) in "Hnoff".
      iDestruct "Hmfin" as (mfin) "(Hmf & Hcap & %Hp)".
      destruct Hp as (Hra & Hs0 & Hs1 & Hsp & Htp & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
      (* recombine the deep custody: 4 (epilogue trade) + 2 (mycpu) *)
      assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
      { rewrite /spd /sp0 po_addv_assoc.
        assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                              (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite HAB. apply avi0. }
      iEval (rewrite HcspN8 Hsp0up) in "Hdeep4".
      iEval (rewrite HcspN8 -Hd2b) in "Hdeep2".
      iDestruct (stack_own_split_2 (pa_stk sp0 kv_frame_slots) 4 6 ltac:(lia)
                   with "[$Hdeep4 $Hdeep2]") as "Hdeep6".
      iApply ("Hcont" $! mstatus0 mfin with "[%] Hhs Hsc Hcap Htlbinv Hpc Hmf [%] Hdeep6 Hnoff [Hintena] [Hpayload]").
      { exact Hmsf. }
      { unfold callee_saved. repeat split.
        - (* sp *)
          rewrite Hsp HcspN8 /spd /sp0 po_addv_assoc.
          assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                                (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite HAB. apply avi0.
        - (* tp *)
          rewrite Htp.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Htp6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Htp4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s0 *) exact Hs0.
        - (* s1 *) exact Hs1.
        - (* s2 *)
          rewrite Hs2.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs2_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs2_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s3 *)
          rewrite Hs3.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs3_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs3_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s4 *)
          rewrite Hs4.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs4_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs4_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s5 *)
          rewrite Hs5.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs5_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs5_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s6 *)
          rewrite Hs6.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs6_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs6_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s7 *)
          rewrite Hs7.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs7_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs7_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s8 *)
          rewrite Hs8.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs8_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs8_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s9 *)
          rewrite Hs9.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs9_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs9_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s10 *)
          rewrite Hs10.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs10_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs10_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s11 *)
          rewrite Hs11.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs11_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs11_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
      { first [ iExact "Hintena" | (iEval (rewrite -Hsv32); iExact "Hintena") ]. }
      { (* the taken arm's iNext stripped the payload's later; re-introduce *)
        iDestruct "Hpayload" as "[%Hpb0 | (%Hpb1 & Hhx & Hsepcx & Hscausex & Hstvalx)]".
        - iLeft. iPureIntro. exact Hpb0.
        - iRight. iFrame "Hsepcx Hscausex Hstvalx".
          iSplitR; [iPureIntro; exact Hpb1 |].
          iDestruct "Hhx" as (h) "[Hi Hs]". iExists h. iFrame "Hi". iNext. iExact "Hs". }
    - (* ===== FALL arm: noff <> 0 ===== *)
      iApply (wp_cbeqz_fall_s_sconf γ root_ppn Φ (mword_of_int (PO + 0x16)) (mword_of_int 11 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) N5
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rewrite Ha5; exact Hcond)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi16 [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      assert (Hpc18 : add_vec_int (mword_of_int (PO + 0x16) : mword 64) 2 = mword_of_int (PO + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc18) in "Hpc".
      assert (Ha0_18f : mycpu_ret (N5 !!! Regidx (mword_of_int 4 : mword 5)) = a0f)
        by (rewrite HN5tp; exact Ha0).
      (* ---- apply the suffix with ms = N5 ---- *)
      iApply (wp_push_off_suffix_sconf γ root_ppn Φ N5 noff
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5)) (m !!! Regidx (mword_of_int 9 : mword 5)) vgap
 Hcret0
                with "Hsc Hhs Hcap Htlbinv Htext Hpc Hfile [Hdeep2] [Hnoff] [Hr24] [Hr16] [Hr8] [Hgap] [-]").
      { iEval (rewrite HcspN5). iExact "Hdeep2". }
      { iEval (rewrite Ha0_18f). iExact "Hnoff". }
      { iEval (rewrite HcspN5). iExact "Hr24". }
      { iEval (rewrite HcspN5). iExact "Hr16". }
      { iEval (rewrite HcspN5). iExact "Hr8". }
      { iEval (rewrite HcspN5 -Hspd4). iExact "Hgap". }
      iIntros "Hhs Hsc Htlbinv Hpc Hmfin Hdeep2 Hdeep4 Hnoff".
      iEval (rewrite Ha0_18f) in "Hnoff".
      iDestruct "Hmfin" as (mfin) "(Hmf & Hcap & %Hp)".
      destruct Hp as (Hra & Hs0 & Hs1 & Hsp & Htp & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
      (* recombine the deep custody: 4 (epilogue trade) + 2 (mycpu) *)
      assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
      { rewrite /spd /sp0 po_addv_assoc.
        assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                              (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite HAB. apply avi0. }
      iEval (rewrite HcspN5 Hsp0up) in "Hdeep4".
      iEval (rewrite HcspN5 -Hd2b) in "Hdeep2".
      iDestruct (stack_own_split_2 (pa_stk sp0 kv_frame_slots) 4 6 ltac:(lia)
                   with "[$Hdeep4 $Hdeep2]") as "Hdeep6".
      iApply ("Hcont" $! mstatus0 mfin with "[%] Hhs Hsc Hcap Htlbinv Hpc Hmf [%] Hdeep6 Hnoff [Hintena] Hpayload").
      { exact Hmsf. }
      { unfold callee_saved. repeat split.
        - (* sp *)
          rewrite Hsp HcspN5 /spd /sp0 po_addv_assoc.
          assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                                (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite HAB. apply avi0.
        - (* tp *)
          rewrite Htp.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Htp4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s0 *) exact Hs0.
        - (* s1 *) exact Hs1.
        - (* s2 *)
          rewrite Hs2.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs2_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s3 *)
          rewrite Hs3.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs3_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s4 *)
          rewrite Hs4.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs4_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s5 *)
          rewrite Hs5.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs5_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s6 *)
          rewrite Hs6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs6_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s7 *)
          rewrite Hs7.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs7_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s8 *)
          rewrite Hs8.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs8_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s9 *)
          rewrite Hs9.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs9_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s10 *)
          rewrite Hs10.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs10_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s11 *)
          rewrite Hs11.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs11_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
      { first [ iExact "Hintena" | (iEval (rewrite -Hsv32); iExact "Hintena") ]. }
  Qed.

End WpSconfPushOff.
