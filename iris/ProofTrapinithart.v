(* ProofTrapinithart.v -- whole-function proof of trapinithart
   (kernel/trap.c): w_stvec((uint64)kernelvec).

   Structure: a 2-slot frame push (ra/s0 saves; addi4spn s0), the auipc/addi
   pair that materializes &kernelvec into a5, the csrw stvec,a5 -- THE
   INSTALL -- and the 2-slot frame teardown + ret.  The [stvec] cell is
   threaded from the precondition through the write to the postcondition; the
   write lands verbatim because kernelvec's low two bits (the tvec MODE
   field) are 00 = Direct, so [legalize_tvec] is the identity on it. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad list_numbers bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore RegFile WpGpr WpMmodeLeafBase.
Require Import IntrDefs WpSmodeIntr WpSconfAlu WpSconfMem WpSconfCtl WpSconfCsr WpAuipc.
Require Import CalleeSaved StackOwn.
Require Import InstrBytes KernelRvcDecode.
Require Import WpTrapinithartDecode.
Require Import SpecTrapinithart.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section TrapinithartBody.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Lemma wp_trapinithart_sconf_proof
      (γ : gname) (Φ : mval -> iProp Σ) (mm : regfile) (K : nat)
      (tv0 : mword 64) :
    wp_trapinithart_sconf_body γ Φ mm K tv0.
  Proof.
    cbv beta delta [wp_trapinithart_sconf_body].
    intros pcE ret_tgt HK.
    iIntros "Hcg #Htext Hpc Hstv Hcont".
    (* frame-cell address facts (2-slot frame: ra @ slot 1, s0 @ slot 2) *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : add_vec (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk (mm !!! Regidx csp_rs1) 1).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk (mm !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (tii_00 with "Htext") as "Hi00".
    iPoseProof (tii_02 with "Htext") as "Hi02".
    iPoseProof (tii_04 with "Htext") as "Hi04".
    iPoseProof (tii_06 with "Htext") as "Hi06".
    iPoseProof (tii_08 with "Htext") as "Hi08".
    iPoseProof (tii_0c with "Htext") as "Hi0c".
    iPoseProof (tii_10 with "Htext") as "Hi10".
    iPoseProof (tii_14 with "Htext") as "Hi14".
    iPoseProof (tii_16 with "Htext") as "Hi16".
    iPoseProof (tii_18 with "Htext") as "Hi18".
    iPoseProof (tii_1a with "Htext") as "Hi1a".
    (* ============ +0x00 addi sp,sp,-16 : 2-slot frame push ============ *)
    iApply (wp_caddi_sp_push_s_sconf γ Φ (mword_of_int TIH) (mword_of_int 48 : mword 6) mm K 2 HK Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /W1 upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int TIH : mword 64) 2 = mword_of_int (TIH + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 sd ra,8(sp) -> slot 1 *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (TIH + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 2)%nat v1 with "Hcg Hpc Hi02 [Hc1] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros "Hcg Hpc Hc1". iEval (rewrite HspW1 Hb1) in "Hc1".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r1) in "Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (TIH + 0x02) : mword 64) 2 = mword_of_int (TIH + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd s0,0(sp) -> slot 2 *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (TIH + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat v2 with "Hcg Hpc Hi04 [Hc2] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros "Hcg Hpc Hc2". iEval (rewrite HspW1 Hb2) in "Hc2".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r8) in "Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (TIH + 0x04) : mword 64) 2 = mword_of_int (TIH + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 addi s0,sp,16 (value unused) *)
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (TIH + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi06 [-]").
    iIntros "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> W1).
    assert (Hp08 : add_vec_int (mword_of_int (TIH + 0x06) : mword 64) 2 = mword_of_int (TIH + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* ============ +0x08 auipc a5,0x3 ============ *)
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (TIH + 0x08)) (mword_of_int 15 : mword 5) (mword_of_int 3 : mword 20)
              W2 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi08 [-]").
    iIntros "Hcg Hpc".
    set (A0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (mword_of_int (TIH + 0x08) : mword 64) (auipc_off (mword_of_int 3 : mword 20)))]> W2).
    assert (Hp0c : add_vec_int (mword_of_int (TIH + 0x08) : mword 64) 4 = mword_of_int (TIH + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* ============ +0x0c addi a5,a5,-14 : a5 := kernelvec ============ *)
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (TIH + 0x0c)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 0xff2 : mword 12)
              A0 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0c [-]").
    iIntros "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (A0 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 0xff2 : mword 12)))]> A0).
    assert (Ha5 : A1 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int KernelSyms.kernelvec : mword 64)).
    { rewrite /A1 upd_eq. rewrite /A0 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp10 : add_vec_int (mword_of_int (TIH + 0x0c) : mword 64) 4 = mword_of_int (TIH + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* ============ +0x10 csrw stvec,a5 : THE INSTALL ============ *)
    iApply (wp_csrw_stvec_s_sconf γ Φ (mword_of_int (TIH + 0x10)) (mword_of_int 15 : mword 5)
              A1 (K - 2)%nat tv0 (mword_of_int KernelSyms.kernelvec : mword 64)
              ltac:(vm_compute; lia) Ha5 ltac:(vm_compute; discriminate)
              with "Hcg Hstv Hpc Hi10 [-]").
    iIntros "Hcg Hstv Hpc".
    assert (Hp14 : add_vec_int (mword_of_int (TIH + 0x10) : mword 64) 4 = mword_of_int (TIH + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* ============ epilogue: ld ra ; ld s0 ; addi sp,16 ; ret ============ *)
    assert (HA1sp : A1 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [| reg_neq].
      rewrite /W2 upd_ne; [| reg_neq]. exact HspW1. }
    (* +0x14 ld ra,8(sp) *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (TIH + 0x14)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              A1 (K - 2)%nat (mm !!! Regidx (mword_of_int 1))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi14 [Hc1] [-]").
    { iEval (rewrite HA1sp Hb1). iExact "Hc1". }
    iIntros "Hcg Hpc Hc1". iEval (rewrite HA1sp Hb1) in "Hc1".
    set (L1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1))]> A1).
    assert (HL1sp : L1 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /L1 upd_ne; [| reg_neq]; exact HA1sp).
    assert (Hp16 : add_vec_int (mword_of_int (TIH + 0x14) : mword 64) 2 = mword_of_int (TIH + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* +0x16 ld s0,0(sp) *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (TIH + 0x16)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              L1 (K - 2)%nat (mm !!! Regidx (mword_of_int 8))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi16 [Hc2] [-]").
    { iEval (rewrite HL1sp Hb2). iExact "Hc2". }
    iIntros "Hcg Hpc Hc2". iEval (rewrite HL1sp Hb2) in "Hc2".
    set (L2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8))]> L1).
    assert (HL2sp : L2 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /L2 upd_ne; [| reg_neq]; exact HL1sp).
    assert (Hp18 : add_vec_int (mword_of_int (TIH + 0x16) : mword 64) 2 = mword_of_int (TIH + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    (* +0x18 addi sp,sp,16 : the frame pop *)
    assert (Hwv : add_vec (L2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = mm !!! Regidx csp_rs1).
    { rewrite HL2sp. apply frame_cancel_16. }
    assert (Hpop : L2 !!! Regidx csp_rs1 = pa_stk (add_vec (L2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv. rewrite HL2sp. exact Hpush. }
    iAssert (stack_own (mm !!! Regidx csp_rs1) 2) with "[Hc1 Hc2]" as "Hframe".
    { rewrite stack_own_slots; cbn [seq].
      iSplitL "Hc1". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc1". }
      iSplitL "Hc2". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc2". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf γ Φ (mword_of_int (TIH + 0x18)) (mword_of_int 16 : mword 6)
              L2 (K - 2)%nat 2 Hpop with "Hcg Hpc Hi18 Hframe [-]").
    iIntros "Hcg Hpc".
    set (Efin := <[Regidx csp_rs1 := regval_into_reg (add_vec (L2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> L2).
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hp1a : add_vec_int (mword_of_int (TIH + 0x18) : mword 64) 2 = mword_of_int (TIH + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    (* +0x1a ret *)
    assert (HEfin1 : Efin !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /Efin upd_ne; [| reg_neq]. rewrite /L2 upd_ne; [| reg_neq]. rewrite /L1 upd_eq. reflexivity. }
    assert (Hrt : ret_pc (Efin !!! Regidx (mword_of_int 1 : mword 5)) = ret_pc (mm !!! Regidx (mword_of_int 1))) by (rewrite HEfin1; reflexivity).
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (TIH + 0x1a)) (mword_of_int 1 : mword 5) Efin K
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi1a [-]").
    iIntros "Hcg Hpc". iEval (rewrite Hrt) in "Hpc".
    iApply ("Hcont" $! Efin with "Hcg Hpc [%] Hstv").
    { (* callee_saved mm Efin *)
      unfold callee_saved.
      repeat split;
        first [ by (rewrite /Efin upd_eq; exact Hwv)
              | by (rewrite /Efin upd_ne; [| reg_neq]; rewrite /L2 upd_eq)
              | (rewrite /Efin /L2 /L1 /A1 /A0 /W2 /W1;
                 repeat (rewrite upd_ne; [| reg_neq]); reflexivity) ]. }
  Qed.

End TrapinithartBody.

Module TrapinithartProof : TRAPINITHART.
  Definition wp_trapinithart_sconf
      `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (mm : regfile) (K : nat)
      (tv0 : mword 64)
      : wp_trapinithart_sconf_body γ Φ mm K tv0 :=
    wp_trapinithart_sconf_proof γ Φ mm K tv0.
End TrapinithartProof.
