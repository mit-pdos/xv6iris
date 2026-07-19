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

  (* ================================================================= *)
  (* THE LOOP (+0x3e..+0x68): induction on the REMAINING page count.    *)
  (* Each iteration: walk, remap-check read (zero by pt_rep0 + the      *)
  (* no-remap premise), leaf store, exit test.                          *)
  (* ================================================================= *)
  Lemma wp_mappages_loop (R : s_regime) (Φ : mval -> iProp Σ)
      (γ γc : gname) (bsie : mword 1)
      (mm : gmap regidx (mword 64)) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (npages : nat) (perm : Z) (n : nat)
      (rem : nat) :
    forall (k : nat) (Mk : gmap regidx (mword 64)) (tk : ptree),
    let va := mm !!! Regidx (mword_of_int 11) in
    let pa := mm !!! Regidx (mword_of_int 13) in
    let vpn0 := svpn_of va in
    let ppn0 := (autocast (T := mword) (subrange_vec_dec pa 55 12) : mword 44) in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (32 <= n)%nat ->
    (k + rem)%nat = npages -> (0 < rem)%nat ->
    mm !!! Regidx (mword_of_int 10)
      = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
    subrange_vec_dec va 11 0 = (zeros' 12 : mword 12) ->
    subrange_vec_dec pa 11 0 = (zeros' 12 : mword 12) ->
    mm !!! Regidx (mword_of_int 14) = mword_of_int perm ->
    mappages_perm_ok perm ->
    (uint va + Z.of_nat npages * 4096 <= 2 ^ 38)%Z ->
    (uint pa + Z.of_nat npages * 4096 < 2 ^ 56)%Z ->
    (forall i, (i < npages)%nat -> m !! vpn_at vpn0 i = None) ->
    Mk !!! Regidx csp_rs1 = spr ->
    Mk !!! Regidx (mword_of_int 9 : mword 5)
      = add_vec va (mword_of_int (4096 * Z.of_nat k)) ->
    Mk !!! Regidx (mword_of_int 18 : mword 5)
      = add_vec va (mword_of_int (4096 * Z.of_nat (npages - 1))) ->
    Mk !!! Regidx (mword_of_int 19 : mword 5) = sub_vec pa va ->
    Mk !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 10) ->
    Mk !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 14) ->
    Mk !!! Regidx (mword_of_int 22 : mword 5) = mword_of_int 1 ->
    bv_unsigned (Mk !!! Regidx (mword_of_int 23 : mword 5)) = 4096 ->
    Mk !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4) ->
    Mk !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mk !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mk !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mk !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    pt_base tk = pt_base t ->
    pt_rep0 tk (pt_insert_run m vpn0 ppn0 perm k) ->
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
    sr_inv R -∗ kernel_text -∗
    pc_is (mword_of_int (MP + 0x3e)) -∗
    gpr_file Mk -∗
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
    ptree_own 2 (DfracOwn 1) tk -∗
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
    induction rem as [| rem' IH]; intros k Mk tk va pa vpn0 ppn0 sp0 spr ret_tgt
      Hn Hkrem Hrem Hroot Hvaal Hpaal Hpermreg Hpok Hvab Hpab Hnone
      Hsp Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Htp Hx24 Hx25 Hx26 Hx27 Hbase Hrep;
      [lia |].
    iIntros "Hcfg Htoken Htlbinv #Htext Hpc Hfile
             Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00ex
             Hdeep Hptree Henv Hcont".
    (* useful bounds *)
    pose proof (bv_unsigned_in_range _ va) as Hvarange.
    unfold bv_modulus in Hvarange.
    change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616 in Hvarange.
    pose proof (bv_unsigned_in_range _ pa) as Hparange.
    unfold bv_modulus in Hparange.
    change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616 in Hparange.
    rewrite uint_unsigned in Hvab. rewrite uint_unsigned in Hpab.
    assert (Hklt : (k < npages)%nat) by lia.
    assert (Hk27 : (Z.of_nat npages < 134217728)%Z) by lia.
    iPoseProof (mi_3e with "Htext") as "Hi3e".
    iPoseProof (mi_40 with "Htext") as "Hi40".
    iPoseProof (mi_42 with "Htext") as "Hi42".
    iPoseProof (mi_44 with "Htext") as "Hi44".
    iPoseProof (mi_48 with "Htext") as "Hi48".
    iPoseProof (mi_4a with "Htext") as "Hi4a".
    iPoseProof (mi_4c with "Htext") as "Hi4c".
    iPoseProof (mi_4e with "Htext") as "Hi4e".
    iPoseProof (mi_50 with "Htext") as "Hi50".
    iPoseProof (mi_54 with "Htext") as "Hi54".
    iPoseProof (mi_56 with "Htext") as "Hi56".
    iPoseProof (mi_58 with "Htext") as "Hi58".
    iPoseProof (mi_5c with "Htext") as "Hi5c".
    iPoseProof (mi_60 with "Htext") as "Hi60".
    iPoseProof (mi_62 with "Htext") as "Hi62".
    iPoseProof (mi_66 with "Htext") as "Hi66".
    iPoseProof (mi_68 with "Htext") as "Hi68".
    iPoseProof (mi_9a with "Htext") as "Hi9a".
    iPoseProof (mi_b2 with "Htext") as "Hib2".
    iPoseProof (mi_b4 with "Htext") as "Hib4".
    (* +0x3e mv a2,s6 *)
    iApply (wp_cmv_gpr_s_config_scfg_r R γc Φ (mword_of_int (MP + 0x3e)) (mword_of_int 12 : mword 5) (mword_of_int 22 : mword 5)
              Mk (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi3e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W1 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (add_vec zero_reg (Mk !!! Regidx (mword_of_int 22 : mword 5)))]> Mk).
    assert (Hpp40 : add_vec_int (mword_of_int (MP + 0x3e) : mword 64) 2 = mword_of_int (MP + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    (* +0x40 mv a1,s1 *)
    iApply (wp_cmv_gpr_s_config_scfg_r R γc Φ (mword_of_int (MP + 0x40)) (mword_of_int 11 : mword 5) (mword_of_int 9 : mword 5)
              W1 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi40 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W2 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (W1 !!! Regidx (mword_of_int 9 : mword 5)))]> W1).
    assert (Hpp42 : add_vec_int (mword_of_int (MP + 0x40) : mword 64) 2 = mword_of_int (MP + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    (* +0x42 mv a0,s4 *)
    iApply (wp_cmv_gpr_s_config_scfg_r R γc Φ (mword_of_int (MP + 0x42)) (mword_of_int 10 : mword 5) (mword_of_int 20 : mword 5)
              W2 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi42 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (W2 !!! Regidx (mword_of_int 20 : mword 5)))]> W2).
    assert (Hpp44 : add_vec_int (mword_of_int (MP + 0x42) : mword 64) 2 = mword_of_int (MP + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    (* +0x44 jal walk *)
    iApply (wp_jal_gpr_s_zca_r R γc Φ (mword_of_int (MP + 0x44)) (mword_of_int 1 : mword 5) (mword_of_int 2096872 : mword 21)
              W3 1%Qp
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi44 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (MP + 0x44) : mword 64) 4)]> W3).
    assert (Hpcw : add_vec (mword_of_int (MP + 0x44) : mword 64) (sign_extend' 64 (mword_of_int 2096872 : mword 21)) = mword_of_int KernelSyms.walk) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcw) in "Hpc".
    (* facts on the call map *)
    assert (HW4a0 : W4 !!! Regidx (mword_of_int 10 : mword 5)
                    = zero_extend' 64 (concat_vec (pt_base tk) (zeros' 12 : mword 12))).
    { rewrite /W4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /W3 lookup_total_insert.
      rewrite /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite add_vec_zero_l. rewrite Hs4. rewrite Hroot. rewrite Hbase. reflexivity. }
    assert (HW4a1 : W4 !!! Regidx (mword_of_int 11 : mword 5)
                    = add_vec va (mword_of_int (4096 * Z.of_nat k))).
    { rewrite /W4 /W3.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite /W2 lookup_total_insert.
      rewrite /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite add_vec_zero_l. exact Hs1. }
    assert (HW4a2 : W4 !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int 1).
    { rewrite /W4 /W3 /W2.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite /W1 lookup_total_insert.
      rewrite add_vec_zero_l. rewrite Hs6. reflexivity. }
    assert (HW4tp : W4 !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Htp. }
    assert (HW4sp : W4 !!! Regidx csp_rs1 = spr).
    { rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hsp. }
    assert (Hvak_u : bv_unsigned (add_vec va (mword_of_int (4096 * Z.of_nat k)))
                     = bv_unsigned va + 4096 * Z.of_nat k)
      by (apply pb_va_k_unsigned; lia).
    assert (Hvpnk : svpn_of (add_vec va (mword_of_int (4096 * Z.of_nat k))) = vpn_at vpn0 k)
      by (apply svpn_of_run; lia).
    (* the walk call *)
    iApply (wp_walk_r R Φ γ γc bsie W4 tk (pt_insert_run m vpn0 ppn0 perm k) (n - 10)%nat
              ltac:(lia)
              HW4a0 HW4a2
              ltac:(rewrite HW4a1; rewrite uint_unsigned; rewrite Hvak_u; lia)
              Hrep
              with "Hcfg Htoken Htlbinv Htext Hpc Hfile [Hdeep] Hptree [Henv] [-]").
    { iEval (rewrite HW4sp). iExact "Hdeep". }
    { iEval (rewrite HW4tp). iExact "Henv". }
    iIntros (mr t') "Hcfg Htoken Htlbinv Hpc Hfile Hstk Hptree Henv %Hkcs %Hsame %Hpay".
    iEval (rewrite HW4sp) in "Hstk".
    iEval (rewrite HW4tp) in "Henv".
    (* pc back at +0x48 *)
    assert (Hlink : W4 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (MP + 0x44) : mword 64) 4).
    { rewrite /W4 lookup_total_insert. reflexivity. }
    assert (Hret48 : update_vec_dec (W4 !!! Regidx (mword_of_int 1 : mword 5)) 0 ('b"0" : mword 1) = mword_of_int (MP + 0x48)).
    { rewrite Hlink. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret48) in "Hpc".
    (* recovered callee-saved registers *)
    assert (Hmr9 : mr !!! Regidx (mword_of_int 9 : mword 5)
                   = add_vec va (mword_of_int (4096 * Z.of_nat k))).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hs1. }
    assert (Hmr18 : mr !!! Regidx (mword_of_int 18 : mword 5)
                    = add_vec va (mword_of_int (4096 * Z.of_nat (npages - 1)))).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hs2. }
    assert (Hmr19 : mr !!! Regidx (mword_of_int 19 : mword 5) = sub_vec pa va).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 19) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hs3. }
    assert (Hmr20 : mr !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 10)).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 20) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hs4. }
    assert (Hmr21 : mr !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 14)).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 21) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hs5. }
    assert (Hmr22 : mr !!! Regidx (mword_of_int 22 : mword 5) = mword_of_int 1).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 22) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hs6. }
    assert (Hmr23 : bv_unsigned (mr !!! Regidx (mword_of_int 23 : mword 5)) = 4096).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 23) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hs7. }
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HW4sp. }
    assert (Hmrtp : mr !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 4) ltac:(vm_compute; reflexivity)).
      exact HW4tp. }
    assert (Hmr24 : mr !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24)).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 24) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hx24. }
    assert (Hmr25 : mr !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 25) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hx25. }
    assert (Hmr26 : mr !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 26) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hx26. }
    assert (Hmr27 : mr !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 27) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hx27. }
    (* the walk-result facts *)
    assert (Hbase' : pt_base t' = pt_base t).
    { destruct Hsame as (Hb & _). rewrite Hb. exact Hbase. }
    assert (Hrep' : pt_rep0 t' (pt_insert_run m vpn0 ppn0 perm k))
      by (exact (pt_rep0_same tk t' _ Hsame Hrep)).
    rewrite HW4a1 in Hpay. rewrite Hvpnk in Hpay.
    (* massage the payload into ZERO vs NONZERO-slot *)
    assert (Hzcase :
        mr !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0
        \/ (exists p2 p1 w0,
             ptree_level0 t' (vpn_at vpn0 k) p2 p1 w0 /\
             mr !!! Regidx (mword_of_int 10 : mword 5) = pt_addr0 p1 (vpn_at vpn0 k) /\
             mr !!! Regidx (mword_of_int 10 : mword 5) <> mword_of_int 0)).
    { destruct Hpay as [Hz | (p2 & p1 & w0 & Hl0 & Ha0v)]; [left; exact Hz |].
      destruct (decide (mr !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0))
        as [He | Hne]; [left; exact He |].
      right. exists p2, p1, w0. auto. }
    clear Hpay.
    destruct Hzcase as [Ha0z | (p2 & p1 & w0 & Hl0 & Ha0v & Ha0nz)].
    { (* ---- walk returned NULL: ret -1 ---- *)
      iApply (wp_cbeqz_taken_s_zca_scfg_r R γc Φ (mword_of_int (MP + 0x48)) (mword_of_int 41 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
                mr (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0z; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi48 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Htgt9a : add_vec (mword_of_int (MP + 0x48) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 41 : mword 8) ('b"0"))))
              = mword_of_int (MP + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt9a) in "Hpc".
      (* +0x9a li a0,-1 *)
      iApply (wp_cli_gpr_s_config_scfg_r R γc Φ (mword_of_int (MP + 0x9a)) (mword_of_int 10 : mword 5) (mword_of_int 63 : mword 6)
                mr (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi9a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (F1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> mr).
      assert (Hpp9c : add_vec_int (mword_of_int (MP + 0x9a) : mword 64) 2 = mword_of_int (MP + 0x9c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp9c) in "Hpc".
      iApply (wp_mappages_epilogue R Φ γ γc bsie mm F1 t t' m npages k perm n Hn
                ltac:(rewrite /F1; rewrite lookup_total_insert_ne; [| vm_compute; discriminate]; exact Hmrsp)
                ltac:(rewrite /F1; rewrite lookup_total_insert_ne; [| vm_compute; discriminate]; exact Hmrtp)
                ltac:(rewrite /F1; rewrite lookup_total_insert_ne; [| vm_compute; discriminate]; exact Hmr24)
                ltac:(rewrite /F1; rewrite lookup_total_insert_ne; [| vm_compute; discriminate]; exact Hmr25)
                ltac:(rewrite /F1; rewrite lookup_total_insert_ne; [| vm_compute; discriminate]; exact Hmr26)
                ltac:(rewrite /F1; rewrite lookup_total_insert_ne; [| vm_compute; discriminate]; exact Hmr27)
                Hbase' Hrep'
                ltac:(right; split; [lia |];
                      rewrite /F1 lookup_total_insert;
                      apply bv_eq; vm_compute; reflexivity)
                with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                      Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00ex
                      Hstk Hptree Henv Hcont").
    }
    (* ---- walk returned the L0 slot: store the leaf ---- *)
    assert (Hw0z : w0 = mword_of_int 0).
    { apply (pt_rep0_level0_zero t' (pt_insert_run m vpn0 ppn0 perm k) (vpn_at vpn0 k) p2 p1 w0 Hrep').
      - apply pt_insert_run_lookup_None; [lia | lia |].
        apply Hnone. exact Hklt.
      - exact Hl0. }
    (* +0x48 c.beqz a0 FALLS *)
    iApply (wp_cbeqz_fall_s_config_scfg_r R γc Φ (mword_of_int (MP + 0x48)) (mword_of_int 41 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              mr (dq:=DfracOwn 1)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply eq_vec_false_iff; intro He; apply Ha0nz;
                    rewrite He; apply bv_eq; vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi48 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp4a : add_vec_int (mword_of_int (MP + 0x48) : mword 64) 2 = mword_of_int (MP + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* the remap-check cell *)
    iDestruct (ptree_own_level0_upd (DfracOwn 1) t' (vpn_at vpn0 k) p2 p1 w0 Hl0 with "Hptree") as "[Hcell Hupd]".
    assert (Hea0 : forall X : mword 64,
        add_vec X (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))) = X).
    { intro X.
      replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000"))) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* +0x4a c.ld a5,0(a0) *)
    iApply (wp_cld_s_scfg_r R γc Φ (mword_of_int (MP + 0x4a)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
              mr w0 (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi4a [Hcell] [-]").
    { iEval (rewrite Hea0 Ha0v). iExact "Hcell". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hcell".
    iEval (rewrite Hea0 Ha0v) in "Hcell".
    set (M5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg w0]> mr).
    assert (Hpp4c : add_vec_int (mword_of_int (MP + 0x4a) : mword 64) 2 = mword_of_int (MP + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4c) in "Hpc".
    (* +0x4c c.andi a5,1 *)
    iApply (wp_candi_s_scfg_r R γc Φ (mword_of_int (MP + 0x4c)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6)
              M5 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi4c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (M6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (M5 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M5).
    assert (Hpp4e : add_vec_int (mword_of_int (MP + 0x4c) : mword 64) 2 = mword_of_int (MP + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    (* +0x4e c.bnez a5 FALLS: the slot word is zero *)
    iApply (wp_cbnez_fall_s_scfg_r R γc Φ (mword_of_int (MP + 0x4e)) (mword_of_int 32 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              M6 (dq:=DfracOwn 1)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /M6 lookup_total_insert; rewrite /M5 lookup_total_insert;
                    rewrite Hw0z; vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi4e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp50 : add_vec_int (mword_of_int (MP + 0x4e) : mword 64) 2 = mword_of_int (MP + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 add a5,s1,s3 *)
    assert (HM6s1 : M6 !!! Regidx (mword_of_int 9 : mword 5)
                    = add_vec va (mword_of_int (4096 * Z.of_nat k))).
    { rewrite /M6 /M5.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hmr9. }
    assert (HM6s3 : M6 !!! Regidx (mword_of_int 19 : mword 5) = sub_vec pa va).
    { rewrite /M6 /M5.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hmr19. }
    iApply (wp_add_s_r R γc Φ (mword_of_int (MP + 0x50)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 19 : mword 5)
              (add_vec pa (mword_of_int (4096 * Z.of_nat k)))
              M6 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite HM6s1 HM6s3; apply mappages_pa_of_va)
              with "Hcfg Htlbinv Hpc Hfile Hi50 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (M7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec pa (mword_of_int (4096 * Z.of_nat k)))]> M6).
    assert (Hpp54 : add_vec_int (mword_of_int (MP + 0x50) : mword 64) 4 = mword_of_int (MP + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54) in "Hpc".
    (* +0x54 c.srli a5,12 *)
    iApply (wp_csrli_s_r R γc Φ (mword_of_int (MP + 0x54)) (mword_of_int 15 : mword 5) (mword_of_int 12 : mword 6)
              (shift_bits_right (M7 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
              M7 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi54 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (M8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (M7 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> M7).
    assert (Hpp56 : add_vec_int (mword_of_int (MP + 0x54) : mword 64) 2 = mword_of_int (MP + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56) in "Hpc".
    (* +0x56 c.slli a5,10 *)
    iApply (wp_cslli_s_r R γc Φ (mword_of_int (MP + 0x56)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 6)
              (shift_bits_left (M8 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
              M8 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi56 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (M9 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (M8 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> M8).
    assert (Hpp58 : add_vec_int (mword_of_int (MP + 0x56) : mword 64) 2 = mword_of_int (MP + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58) in "Hpc".
    (* +0x58 or a5,a5,s5 *)
    iApply (wp_or_s_r R γc Φ (mword_of_int (MP + 0x58)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 21 : mword 5)
              (or_vec (M9 !!! Regidx (mword_of_int 15 : mword 5)) (M9 !!! Regidx (mword_of_int 21 : mword 5)))
              M9 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi58 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (M10 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (or_vec (M9 !!! Regidx (mword_of_int 15 : mword 5)) (M9 !!! Regidx (mword_of_int 21 : mword 5)))]> M9).
    assert (Hpp5c : add_vec_int (mword_of_int (MP + 0x58) : mword 64) 4 = mword_of_int (MP + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    (* +0x5c ori a5,a5,1 *)
    iApply (wp_ori_s_r R γc Φ (mword_of_int (MP + 0x5c)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 12)
              (or_vec (M10 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
              M10 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi5c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (M11 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (or_vec (M10 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> M10).
    assert (Hpp60 : add_vec_int (mword_of_int (MP + 0x5c) : mword 64) 4 = mword_of_int (MP + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp60) in "Hpc".
    (* the computed word IS the run PTE *)
    assert (HPTE : M11 !!! Regidx (mword_of_int 15 : mword 5) = mappages_pte ppn0 perm k).
    { rewrite /M11 lookup_total_insert.
      rewrite {1}/M10 lookup_total_insert.
      rewrite {1}/M9 lookup_total_insert.
      rewrite {1}/M8 lookup_total_insert.
      rewrite {1}/M7 lookup_total_insert.
      assert (HM9s5 : M9 !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int perm).
      { rewrite /M9 /M8 /M7 /M6 /M5.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite Hmr21. exact Hpermreg. }
      rewrite HM9s5.
      destruct Hpok as (Hpr & _).
      assert (Hpaku : bv_unsigned (add_vec pa (mword_of_int (4096 * Z.of_nat k)))
                      = bv_unsigned pa + 4096 * Z.of_nat k)
        by (apply pb_va_k_unsigned; lia).
      unfold mappages_pte. unfold ppn0.
      rewrite <- (run_ppn pa k ltac:(lia)).
      apply (mappages_pte_compute (add_vec pa (mword_of_int (4096 * Z.of_nat k))) perm (mword_of_int perm)).
      - apply mappages_moi_small. lia.
      - exact Hpr.
      - rewrite Hpaku.
        pose proof (aligned12_unsigned pa Hpaal) as Hpal0.
        replace (bv_unsigned pa + 4096 * Z.of_nat k)
          with (bv_unsigned pa + Z.of_nat k * 4096) by lia.
        rewrite Z.mod_add; [exact Hpal0 | lia].
      - rewrite Hpaku. lia. }
    (* +0x60 c.sd a5,0(a0) *)
    assert (HM11a0 : M11 !!! Regidx (mword_of_int 10 : mword 5) = mr !!! Regidx (mword_of_int 10 : mword 5)).
    { rewrite /M11 /M10 /M9 /M8 /M7 /M6 /M5.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      reflexivity. }
    iApply (wp_csd_s_scfg_r R γc Φ (mword_of_int (MP + 0x60)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
              M11 w0 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi60 [Hcell] [-]").
    { iEval (rewrite Hea0 HM11a0 Ha0v). iExact "Hcell". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hcell".
    iEval (rewrite Hea0 HM11a0 Ha0v HPTE) in "Hcell".
    iDestruct ("Hupd" $! (mappages_pte ppn0 perm k) with "Hcell") as "Hptree".
    assert (Hpp62 : add_vec_int (mword_of_int (MP + 0x60) : mword 64) 2 = mword_of_int (MP + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp62) in "Hpc".
    (* the new tree facts *)
    set (tS := ptree_set_leaf t' (vpn_at vpn0 k) (mappages_pte ppn0 perm k)).
    assert (HbaseS : pt_base tS = pt_base t).
    { rewrite /tS ptree_set_leaf_base. exact Hbase'. }
    assert (HrepS : pt_rep0 tS (pt_insert_run m vpn0 ppn0 perm (S k))).
    { destruct (mappages_pte_class (add_vec_int ppn0 (Z.of_nat k)) perm Hpok) as (Hv & Hlf & Hnap & Hpb).
      cbn [pt_insert_run].
      exact (pt_rep0_insert t' (pt_insert_run m vpn0 ppn0 perm k) (vpn_at vpn0 k)
               p2 p1 w0 (mappages_pte ppn0 perm k) Hrep' Hl0 Hv Hlf Hnap Hpb). }
    (* +0x62 beq s1,s2 *)
    assert (HM11s1 : M11 !!! Regidx (mword_of_int 9 : mword 5)
                     = add_vec va (mword_of_int (4096 * Z.of_nat k))).
    { rewrite /M11 /M10 /M9 /M8 /M7 /M6 /M5.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hmr9. }
    assert (HM11s2 : M11 !!! Regidx (mword_of_int 18 : mword 5)
                     = add_vec va (mword_of_int (4096 * Z.of_nat (npages - 1)))).
    { rewrite /M11 /M10 /M9 /M8 /M7 /M6 /M5.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hmr18. }
    destruct rem' as [| rem''].
    { (* ---- LAST page: k = npages - 1; the beq is TAKEN, ret 0 ---- *)
      assert (Hlast : k = (npages - 1)%nat) by lia.
      iApply (wp_beq_taken_s_config_scfg_r R γc Φ (mword_of_int (MP + 0x62)) (mword_of_int 80 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
                M11 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HM11s1 HM11s2; rewrite Hlast; apply eq_vec_true_iff; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi62 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Htgtb2 : add_vec (mword_of_int (MP + 0x62) : mword 64) (sign_extend' 64 (mword_of_int 80 : mword 13)) = mword_of_int (MP + 0xb2)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtb2) in "Hpc".
      (* +0xb2 li a0,0 *)
      iApply (wp_cli_gpr_s_config_scfg_r R γc Φ (mword_of_int (MP + 0xb2)) (mword_of_int 10 : mword 5) (mword_of_int 0 : mword 6)
                M11 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hib2 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (F1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> M11).
      assert (Hppb4 : add_vec_int (mword_of_int (MP + 0xb2) : mword 64) 2 = mword_of_int (MP + 0xb4)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppb4) in "Hpc".
      (* +0xb4 c.j -> the epilogue *)
      iApply (wp_cj_s_scfg_r R γc Φ (mword_of_int (MP + 0xb4)) (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")))
                F1 (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hib4 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Htgt9c : add_vec (mword_of_int (MP + 0xb4) : mword 64)
                (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0"))))
              = mword_of_int (MP + 0x9c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt9c) in "Hpc".
      iApply (wp_mappages_epilogue R Φ γ γc bsie mm F1 t tS m npages (S k) perm n Hn
                ltac:(rewrite /F1 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                      exact Hmrsp)
                ltac:(rewrite /F1 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                      exact Hmrtp)
                ltac:(rewrite /F1 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                      exact Hmr24)
                ltac:(rewrite /F1 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                      exact Hmr25)
                ltac:(rewrite /F1 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                      exact Hmr26)
                ltac:(rewrite /F1 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                      exact Hmr27)
                HbaseS HrepS
                ltac:(left; split; [lia |];
                      rewrite /F1 lookup_total_insert;
                      apply bv_eq; vm_compute; reflexivity)
                with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                      Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00ex
                      Hstk Hptree Henv Hcont").
    }
    (* ---- MORE pages: the beq FALLS, step and loop ---- *)
    assert (Hne12 : add_vec va (mword_of_int (4096 * Z.of_nat k))
                    <> add_vec va (mword_of_int (4096 * Z.of_nat (npages - 1)))).
    { intro He.
      apply (mappages_va_eq_iff va k (npages - 1) ltac:(lia) ltac:(lia)) in He.
      lia. }
    iApply (wp_beq_fall_s_config_scfg_r R γc Φ (mword_of_int (MP + 0x62)) (mword_of_int 80 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
              M11 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HM11s1 HM11s2; apply eq_vec_false_iff; exact Hne12)
              with "Hcfg Htlbinv Hpc Hfile Hi62 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp66 : add_vec_int (mword_of_int (MP + 0x62) : mword 64) 4 = mword_of_int (MP + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp66) in "Hpc".
    (* +0x66 c.add s1,s1,s7 *)
    iApply (wp_cadd_s_scfg_r R γc Φ (mword_of_int (MP + 0x66)) (mword_of_int 9 : mword 5) (mword_of_int 23 : mword 5)
              M11 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi66 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (M12 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec (M11 !!! Regidx (mword_of_int 9 : mword 5)) (M11 !!! Regidx (mword_of_int 23 : mword 5)))]> M11).
    assert (Hpp68 : add_vec_int (mword_of_int (MP + 0x66) : mword 64) 2 = mword_of_int (MP + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp68) in "Hpc".
    (* +0x68 c.j -> loop head *)
    iApply (wp_cj_s_scfg_r R γc Φ (mword_of_int (MP + 0x68)) (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")))
              M12 (dq:=DfracOwn 1)
              ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi68 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Htgt3e : add_vec (mword_of_int (MP + 0x68) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0"))))
            = mword_of_int (MP + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt3e) in "Hpc".
    (* the stepped s1 *)
    assert (HM11s7 : M11 !!! Regidx (mword_of_int 23 : mword 5) = mr !!! Regidx (mword_of_int 23 : mword 5)).
    { rewrite /M11 /M10 /M9 /M8 /M7 /M6 /M5.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      reflexivity. }
    assert (HM12s1 : M12 !!! Regidx (mword_of_int 9 : mword 5)
                     = add_vec va (mword_of_int (4096 * Z.of_nat (S k)))).
    { rewrite /M12 lookup_total_insert.
      rewrite HM11s1 HM11s7.
      apply (mappages_va_step va k (mr !!! Regidx (mword_of_int 23 : mword 5)) Hmr23). }
    assert (HM12s7v : M12 !!! Regidx (mword_of_int 23 : mword 5)
                      = mr !!! Regidx (mword_of_int 23 : mword 5)).
    { rewrite /M12 /M11 /M10 /M9 /M8 /M7 /M6 /M5.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      reflexivity. }
    (* loop *)
    iApply (IH (S k) M12 tS
              Hn ltac:(lia) ltac:(lia) Hroot Hvaal Hpaal Hpermreg Hpok
              ltac:(rewrite uint_unsigned; exact Hvab)
              ltac:(rewrite uint_unsigned; exact Hpab) Hnone
              ltac:(rewrite /M12 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hmrsp)
              HM12s1
              ltac:(rewrite /M12 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hmr18)
              ltac:(rewrite /M12 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hmr19)
              ltac:(rewrite /M12 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hmr20)
              ltac:(rewrite /M12 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hmr21)
              ltac:(rewrite /M12 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hmr22)
              ltac:(rewrite HM12s7v; exact Hmr23)
              ltac:(rewrite /M12 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hmrtp)
              ltac:(rewrite /M12 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hmr24)
              ltac:(rewrite /M12 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hmr25)
              ltac:(rewrite /M12 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hmr26)
              ltac:(rewrite /M12 /M11 /M10 /M9 /M8 /M7 /M6 /M5;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hmr27)
              HbaseS HrepS
              with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                    Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00ex
                    Hstk Hptree Henv Hcont").
  Qed.


End Mappages.
