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
Require Import WpMycpu WpCallMycpu WpSconfMycpu WpPushOffTop.
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

End WpSconfPushOff.
