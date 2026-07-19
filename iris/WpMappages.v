(* WpMappages.v -- the whole-function proof of mappages() (kernel/vm.c):
   the bounded page-run loop over walk().  Spec of record: KvmSpec.v's
   [mappages_spec].  Architecture mirrors WpWalk.v: a Qed-sealed shared
   epilogue chunk, a fuel-inducted loop lemma (induction on the REMAINING
   page count -- no Löb), and the prologue lemma concluding the spec.  *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
From iris.base_logic.lib Require Import ghost_var.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText WpAuipc.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SRegime.
Require Import SmodeCore WpSmodeGpr.
Require Import WpMycpu WpLock.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KallocInv.
Require Import SmodePte Pt4kWalk CommonWalk PtAdBits PtTree PtTreeAdue KptTree SmodeCorePt.
Require Import PtBuild KvmSpec.
Require Import WpSmodePtLeaves WpSmodePtAlu WpSmodePtBtype WpSmodePtCtl.
Require Import WpSmodePtMem WpSmodePtMemWrap.
Require Import WpWalk WpMappagesInstr UserBits.
Require Export WpSmodeLeafBase.
From Kernel Require KernelSyms.
Import Defs.

Section Mappages.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation MP := KernelSyms.mappages.

  (* the -80/+80 c.addi16sp frame cancel *)
  Lemma mappages_sp_cancel (X : mword 64) :
    add_vec (add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))
            (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = X.
  Proof.
    assert (add_vec_unsigned : forall x y : mword 64,
              bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
    { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
        SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
      rewrite bv_add_unsigned. reflexivity. }
    apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
    assert (HA : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)) : mword 64) = 18446744073709551536) by (vm_compute; reflexivity).
    assert (HB : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)) : mword 64) = 80) by (vm_compute; reflexivity).
    rewrite HA HB. rewrite <- Z.add_assoc.
    replace (18446744073709551536 + 80) with (bv_modulus 64) by (vm_compute; reflexivity).
    rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
  Qed.

  (* ================================================================= *)
  (* THE SHARED EPILOGUE (+0x9c..+0xb0): both exits funnel here with a0  *)
  (* already holding the result, the nine frame cells still at their     *)
  (* entry values, and the tree/represented-map facts decided.           *)
  (* ================================================================= *)
  Lemma wp_mappages_epilogue (R : s_regime) (Φ : mval -> iProp Σ)
      (γ γc : gname) (bsie : mword 1)
      (mm Mf : gmap regidx (mword 64)) (t tf : ptree)
      (m : gmap (mword 27) (mword 64)) (npages k : nat) (perm : Z) (n : nat) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn0 := svpn_of va in
    let ppn0 := (autocast (T := mword) (subrange_vec_dec (mm !!! Regidx (mword_of_int 13)) 55 12) : mword 44) in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (32 <= n)%nat ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    pt_base tf = pt_base t ->
    pt_rep0 tf (pt_insert_run m vpn0 ppn0 perm k) ->
    ((k = npages /\ Mf !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0)
     \/ ((k < npages)%nat /\ Mf !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (-1))) ->
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
    sr_inv R -∗ kernel_text -∗
    pc_is (mword_of_int (MP + 0x9c)) -∗
    gpr_file Mf -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    pa_stk sp0 9 ↦₈ (mm !!! Regidx (mword_of_int 23)) -∗
    (∃ v00 : bv 64, pa_stk sp0 10 ↦₈ v00) -∗
    stack_own spr (n - 10) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
    kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
    ( ∀ (mr : gmap regidx (mword 64)) (t' : ptree) (k' : nat),
      smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
      sr_inv R -∗
      pc_is ret_tgt -∗
      gpr_file mr -∗ stack_own sp0 n -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜pt_base t' = pt_base t⌝ -∗
      ⌜pt_rep0 t' (pt_insert_run m vpn0 ppn0 perm k')⌝ -∗
      ⌜ (k' = npages /\ mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
        \/ ((k' < npages)%nat /\
            mr !!! Regidx (mword_of_int 10) = mword_of_int (-1)) ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros va vpn0 ppn0 sp0 spr ret_tgt Hn Hsp Htp Hx24 Hx25 Hx26 Hx27 Hbase Hrep Hpay.
    iIntros "Hcfg Htoken Htlbinv #Htext Hpc Hfile
             Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00ex
             Hdeep Hptree Henv Hcont".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 9).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 10 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (mi_9c with "Htext") as "Hi9c".
    iPoseProof (mi_9e with "Htext") as "Hi9e".
    iPoseProof (mi_a0 with "Htext") as "Hia0".
    iPoseProof (mi_a2 with "Htext") as "Hia2".
    iPoseProof (mi_a4 with "Htext") as "Hia4".
    iPoseProof (mi_a6 with "Htext") as "Hia6".
    iPoseProof (mi_a8 with "Htext") as "Hia8".
    iPoseProof (mi_aa with "Htext") as "Hiaa".
    iPoseProof (mi_ac with "Htext") as "Hiac".
    iPoseProof (mi_ae with "Htext") as "Hiae".
    iPoseProof (mi_b0 with "Htext") as "Hib0".
    pose proof Hsp as HspE0.
    (* +0x9c c.ldsp x1,72(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (MP + 0x9c)) (mword_of_int 9 : mword 6) (mword_of_int 1 : mword 5)
              Mf (mm !!! Regidx (mword_of_int 1 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi9c [Hc72] [-]").
    { iEval (rewrite HspE0 Hb1). iExact "Hc72". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc72".
    iEval (rewrite HspE0 Hb1) in "Hc72".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> Mf).
    assert (Hpp9cn : add_vec_int (mword_of_int (MP + 0x9c) : mword 64) 2 = mword_of_int (MP + 0x9e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp9cn) in "Hpc".
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spr).
    { rewrite /E1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE0. }
    (* +0x9e c.ldsp x8,64(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (MP + 0x9e)) (mword_of_int 8 : mword 6) (mword_of_int 8 : mword 5)
              E1 (mm !!! Regidx (mword_of_int 8 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi9e [Hc64] [-]").
    { iEval (rewrite HspE1 Hb2). iExact "Hc64". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc64".
    iEval (rewrite HspE1 Hb2) in "Hc64".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (Hpp9en : add_vec_int (mword_of_int (MP + 0x9e) : mword 64) 2 = mword_of_int (MP + 0xa0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp9en) in "Hpc".
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spr).
    { rewrite /E2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE1. }
    (* +0xa0 c.ldsp x9,56(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (MP + 0xa0)) (mword_of_int 7 : mword 6) (mword_of_int 9 : mword 5)
              E2 (mm !!! Regidx (mword_of_int 9 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hia0 [Hc56] [-]").
    { iEval (rewrite HspE2 Hb3). iExact "Hc56". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc56".
    iEval (rewrite HspE2 Hb3) in "Hc56".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (Hppa0n : add_vec_int (mword_of_int (MP + 0xa0) : mword 64) 2 = mword_of_int (MP + 0xa2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa0n) in "Hpc".
    assert (HspE3 : E3 !!! Regidx csp_rs1 = spr).
    { rewrite /E3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE2. }
    (* +0xa2 c.ldsp x18,48(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (MP + 0xa2)) (mword_of_int 6 : mword 6) (mword_of_int 18 : mword 5)
              E3 (mm !!! Regidx (mword_of_int 18 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hia2 [Hc48] [-]").
    { iEval (rewrite HspE3 Hb4). iExact "Hc48". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc48".
    iEval (rewrite HspE3 Hb4) in "Hc48".
    set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 18 : mword 5))]> E3).
    assert (Hppa2n : add_vec_int (mword_of_int (MP + 0xa2) : mword 64) 2 = mword_of_int (MP + 0xa4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa2n) in "Hpc".
    assert (HspE4 : E4 !!! Regidx csp_rs1 = spr).
    { rewrite /E4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE3. }
    (* +0xa4 c.ldsp x19,40(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (MP + 0xa4)) (mword_of_int 5 : mword 6) (mword_of_int 19 : mword 5)
              E4 (mm !!! Regidx (mword_of_int 19 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hia4 [Hc40] [-]").
    { iEval (rewrite HspE4 Hb5). iExact "Hc40". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc40".
    iEval (rewrite HspE4 Hb5) in "Hc40".
    set (E5 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 19 : mword 5))]> E4).
    assert (Hppa4n : add_vec_int (mword_of_int (MP + 0xa4) : mword 64) 2 = mword_of_int (MP + 0xa6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa4n) in "Hpc".
    assert (HspE5 : E5 !!! Regidx csp_rs1 = spr).
    { rewrite /E5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE4. }
    (* +0xa6 c.ldsp x20,32(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (MP + 0xa6)) (mword_of_int 4 : mword 6) (mword_of_int 20 : mword 5)
              E5 (mm !!! Regidx (mword_of_int 20 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hia6 [Hc32] [-]").
    { iEval (rewrite HspE5 Hb6). iExact "Hc32". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc32".
    iEval (rewrite HspE5 Hb6) in "Hc32".
    set (E6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 20 : mword 5))]> E5).
    assert (Hppa6n : add_vec_int (mword_of_int (MP + 0xa6) : mword 64) 2 = mword_of_int (MP + 0xa8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa6n) in "Hpc".
    assert (HspE6 : E6 !!! Regidx csp_rs1 = spr).
    { rewrite /E6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE5. }
    (* +0xa8 c.ldsp x21,24(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (MP + 0xa8)) (mword_of_int 3 : mword 6) (mword_of_int 21 : mword 5)
              E6 (mm !!! Regidx (mword_of_int 21 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hia8 [Hc24] [-]").
    { iEval (rewrite HspE6 Hb7). iExact "Hc24". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc24".
    iEval (rewrite HspE6 Hb7) in "Hc24".
    set (E7 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 21 : mword 5))]> E6).
    assert (Hppa8n : add_vec_int (mword_of_int (MP + 0xa8) : mword 64) 2 = mword_of_int (MP + 0xaa)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa8n) in "Hpc".
    assert (HspE7 : E7 !!! Regidx csp_rs1 = spr).
    { rewrite /E7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE6. }
    (* +0xaa c.ldsp x22,16(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (MP + 0xaa)) (mword_of_int 2 : mword 6) (mword_of_int 22 : mword 5)
              E7 (mm !!! Regidx (mword_of_int 22 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hiaa [Hc16] [-]").
    { iEval (rewrite HspE7 Hb8). iExact "Hc16". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc16".
    iEval (rewrite HspE7 Hb8) in "Hc16".
    set (E8 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 22 : mword 5))]> E7).
    assert (Hppaan : add_vec_int (mword_of_int (MP + 0xaa) : mword 64) 2 = mword_of_int (MP + 0xac)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppaan) in "Hpc".
    assert (HspE8 : E8 !!! Regidx csp_rs1 = spr).
    { rewrite /E8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE7. }
    (* +0xac c.ldsp x23,8(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (MP + 0xac)) (mword_of_int 1 : mword 6) (mword_of_int 23 : mword 5)
              E8 (mm !!! Regidx (mword_of_int 23 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hiac [Hc08] [-]").
    { iEval (rewrite HspE8 Hb9). iExact "Hc08". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc08".
    iEval (rewrite HspE8 Hb9) in "Hc08".
    set (E9 := <[Regidx (mword_of_int 23 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 23 : mword 5))]> E8).
    assert (Hppacn : add_vec_int (mword_of_int (MP + 0xac) : mword 64) 2 = mword_of_int (MP + 0xae)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppacn) in "Hpc".
    assert (HspE9 : E9 !!! Regidx csp_rs1 = spr).
    { rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE8. }
    (* +0xae c.addi16sp sp,+80 *)
    iApply (wp_caddi16sp_gpr_s_r R γc Φ (mword_of_int (MP + 0xae)) (mword_of_int 5 : mword 6) E9 1%Qp
              with "Hcfg Htlbinv Hpc Hfile Hiae [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (E10 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E9).
    assert (Hppaen : add_vec_int (mword_of_int (MP + 0xae) : mword 64) 2 = mword_of_int (MP + 0xb0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppaen) in "Hpc".
    assert (HspE10 : E10 !!! Regidx csp_rs1 = sp0).
    { rewrite /E10 lookup_total_insert. rewrite HspE9.
      unfold spr. apply mappages_sp_cancel. }
    (* +0xb0 ret *)
    assert (HE10ra : E10 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite lookup_total_insert. reflexivity. }
    assert (Hrt : update_vec_dec (add_vec (E10 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0" : mword 1) = ret_tgt).
    { rewrite HE10ra.
      replace (sign_extend' 64 (zeros' 12) : mword 64) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. reflexivity. }
    iApply (wp_cret_s_zca_scfg_r R γc Φ (mword_of_int (MP + 0xb0)) (mword_of_int 1 : mword 5) E10 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hrt; exact (bit0_update0_64 (mm !!! Regidx (mword_of_int 1))))
              with "Hcfg Htlbinv Hpc Hfile Hib0 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    iEval (rewrite Hrt) in "Hpc".
    (* ---- rebundle the stack and conclude ---- *)
    iAssert (stack_own sp0 10)%I with "[Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00ex]" as "Htop".
    { iEval (rewrite stack_own_slots; cbn [seq]).
      iSplitL "Hc72". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc72". }
      iSplitL "Hc64". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc64". }
      iSplitL "Hc56". { iExists (mm !!! Regidx (mword_of_int 9)). iExact "Hc56". }
      iSplitL "Hc48". { iExists (mm !!! Regidx (mword_of_int 18)). iExact "Hc48". }
      iSplitL "Hc40". { iExists (mm !!! Regidx (mword_of_int 19)). iExact "Hc40". }
      iSplitL "Hc32". { iExists (mm !!! Regidx (mword_of_int 20)). iExact "Hc32". }
      iSplitL "Hc24". { iExists (mm !!! Regidx (mword_of_int 21)). iExact "Hc24". }
      iSplitL "Hc16". { iExists (mm !!! Regidx (mword_of_int 22)). iExact "Hc16". }
      iSplitL "Hc08". { iExists (mm !!! Regidx (mword_of_int 23)). iExact "Hc08". }
      iSplitL "Hc00ex". { iExact "Hc00ex". }
      done. }
    iEval (rewrite -Hsprstk) in "Hdeep".
    iDestruct (stack_own_split_2 sp0 10 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
    assert (HE10a0 : E10 !!! Regidx (mword_of_int 10 : mword 5) = Mf !!! Regidx (mword_of_int 10 : mword 5)).
    { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      reflexivity. }
    iApply ("Hcont" $! E10 tf k with "Hcfg Htoken Htlbinv Hpc Hfile Hstk Hptree Henv [%] [%] [%] [%]").
    { (* callee_saved mm E10 *)
      unfold callee_saved.
      split.
      { rewrite /E10 lookup_total_insert. rewrite HspE9.
        unfold spr. apply mappages_sp_cancel. }
      split.
      { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        exact Htp. }
      split.
      { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      split.
      { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      split.
      { rewrite /E10 /E9 /E8 /E7 /E6 /E5.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      split.
      { rewrite /E10 /E9 /E8 /E7 /E6.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      split.
      { rewrite /E10 /E9 /E8 /E7.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      split.
      { rewrite /E10 /E9 /E8.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      split.
      { rewrite /E10 /E9.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      split.
      { rewrite /E10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E9 lookup_total_insert. reflexivity. }
      split.
      { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        exact Hx24. }
      split.
      { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        exact Hx25. }
      split.
      { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        exact Hx26. }
      { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        exact Hx27. }
    }
    { exact Hbase. }
    { exact Hrep. }
    { rewrite HE10a0. exact Hpay. }
  Qed.

End Mappages.
