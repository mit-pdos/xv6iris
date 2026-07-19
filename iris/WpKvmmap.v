(* WpKvmmap.v -- the whole-function proof of kvmmap() (kernel/vm.c):
   a thin wrapper that swaps mappages's size/pa arguments, calls mappages,
   and panics on failure.  Spec of record: KvmSpec.v's [kvmmap_spec].
   The frame decodes are the shared 16-byte templates in KernelRvcDecode;
   only the three arg-shuffling c.mv, the failure c.bnez, and the base jals
   are decoded locally.  The -1 arm is absorbed by [panic_wp].            *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RiscvExtras.
Require Import RiscvExec RiscvTryStep RiscvFetchExec.
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
Require Import WpWalk WpMappages UserBits.
Require Import KernelRvcDecode WpRvcBridge WpDecode WpDecodeBridge.
Require Export WpSmodeLeafBase.
From Kernel Require KernelSyms.
Import Defs.

Section Kvmmap.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation KM := KernelSyms.kvmmap.

  (* ---- the arg-shuffle c.mv decode facts ---- *)
  Lemma kvdec_mv_a5a3 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x87b6 : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 13)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kvdec_mv_a3a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x86b2 : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 13), Regidx (mword_of_int 12)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kvdec_mv_a2a5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x863e : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 15)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kvdec_bnez s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xe509 : mword 16)) s
    = Some (C_BNEZ (mword_of_int 5, Cregidx (mword_of_int 2)), s).
  Proof. intro H. rvc_oneshot s H. Qed.

  (* ---- the base jals ---- *)
  Lemma kvdec_jal_mp s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xf3dff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2096956 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

  (* ---- instr facts ---- *)
  Local Notation KMP off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KM + off) : mword 64) rvc ast).

  Lemma ki_00 : KMP 0x00 true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KM + 0x00)%Z (mword_of_int 0x1141 : mword 16) (mword_of_int (KM + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_ccc exec_execute_C_ADDI. Qed.
  Lemma ki_02 : KMP 0x02 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KM + 0x02)%Z (mword_of_int 0xe406 : mword 16) (mword_of_int (KM + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) mdec_cce exec_execute_C_SDSP. Qed.
  Lemma ki_04 : KMP 0x04 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KM + 0x04)%Z (mword_of_int 0xe022 : mword 16) (mword_of_int (KM + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) mdec_cd0 exec_execute_C_SDSP. Qed.
  Lemma ki_06 : KMP 0x06 true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KM + 0x06)%Z (mword_of_int 0x0800 : mword 16) (mword_of_int (KM + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) mdec_cd2 exec_execute_C_ADDI4SPN. Qed.
  Lemma ki_08 : KMP 0x08 true (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (KM + 0x08)%Z (mword_of_int 0x87b6 : mword 16) (mword_of_int (KM + 0x08) : mword 64) (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 15), ADD)) kvdec_mv_a5a3 exec_execute_C_MV. Qed.
  Lemma ki_0a : KMP 0x0a true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 13), ADD)).
  Proof. mk_rvc (KM + 0x0a)%Z (mword_of_int 0x86b2 : mword 16) (mword_of_int (KM + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 13), ADD)) kvdec_mv_a3a2 exec_execute_C_MV. Qed.
  Lemma ki_0c : KMP 0x0c true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (KM + 0x0c)%Z (mword_of_int 0x863e : mword 16) (mword_of_int (KM + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 12), ADD)) kvdec_mv_a2a5 exec_execute_C_MV. Qed.
  Lemma ki_0e : KMP 0x0e false (JAL (mword_of_int 2096956 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KM + 0x0e)%Z (mword_of_int 0xf3dff0ef : mword 32) (mword_of_int (KM + 0x0e) : mword 64) (JAL (mword_of_int 2096956 : mword 21, Regidx (mword_of_int 1))) kvdec_jal_mp. Qed.
  Lemma ki_12 : KMP 0x12 true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)).
  Proof. mk_rvc (KM + 0x12)%Z (mword_of_int 0xe509 : mword 16) (mword_of_int (KM + 0x12) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)) kvdec_bnez exec_execute_C_BNEZ. Qed.
  Lemma ki_14 : KMP 0x14 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KM + 0x14)%Z (mword_of_int 0x60a2 : mword 16) (mword_of_int (KM + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) mdec_cea exec_execute_C_LDSP. Qed.
  Lemma ki_16 : KMP 0x16 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KM + 0x16)%Z (mword_of_int 0x6402 : mword 16) (mword_of_int (KM + 0x16) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) mdec_cec exec_execute_C_LDSP. Qed.
  Lemma ki_18 : KMP 0x18 true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KM + 0x18)%Z (mword_of_int 0x0141 : mword 16) (mword_of_int (KM + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_cee exec_execute_C_ADDI. Qed.
  Lemma ki_1a : KMP 0x1a true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KM + 0x1a)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int (KM + 0x1a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

  (* ---- the (unreachable-return) panic arm ---- *)
  Lemma kvdec_auipc s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00006517 : mword 32)) s
    = Some (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kvdec_addi s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x01650513 : mword 32)) s
    = Some (ITYPE (mword_of_int 0x16 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kvdec_jal_pn s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xf1cff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2094876 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

  Lemma ki_1c : KMP 0x1c false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KM + 0x1c)%Z (mword_of_int 0x00006517 : mword 32) (mword_of_int (KM + 0x1c) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)) kvdec_auipc. Qed.
  Lemma ki_20 : KMP 0x20 false (ITYPE (mword_of_int 0x16 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KM + 0x20)%Z (mword_of_int 0x01650513 : mword 32) (mword_of_int (KM + 0x20) : mword 64) (ITYPE (mword_of_int 0x16 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) kvdec_addi. Qed.
  Lemma ki_24 : KMP 0x24 false (JAL (mword_of_int 2094876 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KM + 0x24)%Z (mword_of_int 0xf1cff0ef : mword 32) (mword_of_int (KM + 0x24) : mword 64) (JAL (mword_of_int 2094876 : mword 21, Regidx (mword_of_int 1))) kvdec_jal_pn. Qed.

  (* ================================================================= *)
  (* THE WHOLE FUNCTION.                                                 *)
  (* ================================================================= *)
  Lemma wp_kvmmap_r (R : s_regime) (Φ : mval -> iProp Σ)
      (γ γc : gname) (bsie : mword 1)
      (mm : gmap regidx (mword 64)) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (npages : nat) (perm : Z) (n : nat) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let pa := mm !!! Regidx (mword_of_int 12) in
    let vpn0 := svpn_of va in
    let ppn0 := (autocast (T := mword) (subrange_vec_dec pa 55 12) : mword 44) in
    let sp0 := mm !!! Regidx csp_rs1 in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (34 <= n)%nat ->
    mm !!! Regidx (mword_of_int 10)
      = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
    subrange_vec_dec va 11 0 = (zeros' 12 : mword 12) ->
    subrange_vec_dec pa 11 0 = (zeros' 12 : mword 12) ->
    mm !!! Regidx (mword_of_int 13) = mword_of_int (Z.of_nat npages * 4096) ->
    (1 <= npages)%nat ->
    mm !!! Regidx (mword_of_int 14) = mword_of_int perm ->
    mappages_perm_ok perm ->
    (uint va + Z.of_nat npages * 4096 <= 2 ^ 38)%Z ->
    (uint pa + Z.of_nat npages * 4096 < 2 ^ 56)%Z ->
    pt_rep0 t m ->
    (forall i, (i < npages)%nat -> m !! vpn_at vpn0 i = None) ->
    panic_wp -∗
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
    sr_inv R -∗ kernel_text -∗
    pc_is (mword_of_int KM) -∗
    gpr_file mm -∗ stack_own sp0 n -∗
    ptree_own 2 (DfracOwn 1) t -∗
    kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
    ( ∀ (mr : gmap regidx (mword 64)) (t' : ptree),
      smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
      sr_inv R -∗
      pc_is ret_tgt -∗
      gpr_file mr -∗ stack_own sp0 n -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜pt_base t' = pt_base t⌝ -∗
      ⌜pt_rep0 t' (pt_insert_run m vpn0 ppn0 perm npages)⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros va pa vpn0 ppn0 sp0 ret_tgt
      Hn Hroot Hvaal Hpaal Hsz Hnp Hpermreg Hpok Hvab Hpab Hrep Hnone.
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    iIntros "#Hpanic Hcfg Htoken Htlbinv #Htext Hpc Hfile Hstk Hptree Henv Hcont".
    (* peel the 2-slot frame *)
    iDestruct (stack_own_split_1 sp0 2 n ltac:(lia) with "Hstk") as "[Htop Hdeep]".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Htop".
    iDestruct "Htop" as "(S1 & S2 & _)".
    iDestruct "S1" as (v8) "Hc1". iDestruct "S2" as (v0) "Hc2".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 2 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (ki_00 with "Htext") as "Hi00".
    iPoseProof (ki_02 with "Htext") as "Hi02".
    iPoseProof (ki_04 with "Htext") as "Hi04".
    iPoseProof (ki_06 with "Htext") as "Hi06".
    iPoseProof (ki_08 with "Htext") as "Hi08".
    iPoseProof (ki_0a with "Htext") as "Hi0a".
    iPoseProof (ki_0c with "Htext") as "Hi0c".
    iPoseProof (ki_0e with "Htext") as "Hi0e".
    iPoseProof (ki_12 with "Htext") as "Hi12".
    iPoseProof (ki_14 with "Htext") as "Hi14".
    iPoseProof (ki_16 with "Htext") as "Hi16".
    iPoseProof (ki_18 with "Htext") as "Hi18".
    iPoseProof (ki_1a with "Htext") as "Hi1a".
    (* +0x00 c.addi sp,-16 *)
    iApply (wp_caddi_gpr_s_r R γc Φ (mword_of_int KM) csp_rs1 (mword_of_int 48 : mword 6)
              mm (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr)
      by (rewrite /W1 lookup_total_insert; reflexivity).
    assert (Hpp02 : add_vec_int (mword_of_int KM : mword 64) 2 = mword_of_int (KM + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (KM + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              W1 v8 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi02 [Hc1] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc1".
    iEval (rewrite HspW1 Hb1) in "Hc1".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r1) in "Hc1".
    assert (Hpp04 : add_vec_int (mword_of_int (KM + 0x02) : mword 64) 2 = mword_of_int (KM + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (KM + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              W1 v0 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi04 [Hc2] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc2".
    iEval (rewrite HspW1 Hb2) in "Hc2".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
    { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r8) in "Hc2".
    assert (Hpp06 : add_vec_int (mword_of_int (KM + 0x04) : mword 64) 2 = mword_of_int (KM + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_gpr_s_r R γc Φ (mword_of_int (KM + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              W1 (dq:=DfracOwn 1)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi06 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (P2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> W1).
    assert (Hpp08 : add_vec_int (mword_of_int (KM + 0x06) : mword 64) 2 = mword_of_int (KM + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 mv a5,a3 (a5 := sz) *)
    iApply (wp_cmv_gpr_s_config_scfg_r R γc Φ (mword_of_int (KM + 0x08)) (mword_of_int 15 : mword 5) (mword_of_int 13 : mword 5)
              P2 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (P3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (P2 !!! Regidx (mword_of_int 13 : mword 5)))]> P2).
    assert (Hpp0a : add_vec_int (mword_of_int (KM + 0x08) : mword 64) 2 = mword_of_int (KM + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a mv a3,a2 (a3 := pa) *)
    iApply (wp_cmv_gpr_s_config_scfg_r R γc Φ (mword_of_int (KM + 0x0a)) (mword_of_int 13 : mword 5) (mword_of_int 12 : mword 5)
              P3 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (P4 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (add_vec zero_reg (P3 !!! Regidx (mword_of_int 12 : mword 5)))]> P3).
    assert (Hpp0c : add_vec_int (mword_of_int (KM + 0x0a) : mword 64) 2 = mword_of_int (KM + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c mv a2,a5 (a2 := sz) *)
    iApply (wp_cmv_gpr_s_config_scfg_r R γc Φ (mword_of_int (KM + 0x0c)) (mword_of_int 12 : mword 5) (mword_of_int 15 : mword 5)
              P4 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (P5 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (add_vec zero_reg (P4 !!! Regidx (mword_of_int 15 : mword 5)))]> P4).
    assert (Hpp0e : add_vec_int (mword_of_int (KM + 0x0c) : mword 64) 2 = mword_of_int (KM + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e jal mappages *)
    iApply (wp_jal_gpr_s_zca_r R γc Φ (mword_of_int (KM + 0x0e)) (mword_of_int 1 : mword 5) (mword_of_int 2096956 : mword 21)
              P5 1%Qp
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi0e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (P6 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KM + 0x0e) : mword 64) 4)]> P5).
    assert (Hpcmp : add_vec (mword_of_int (KM + 0x0e) : mword 64) (sign_extend' 64 (mword_of_int 2096956 : mword 21)) = mword_of_int KernelSyms.mappages) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcmp) in "Hpc".
    (* ---- the swapped-argument facts at mappages entry ---- *)
    assert (HP6sp : P6 !!! Regidx csp_rs1 = spr).
    { rewrite /P6 /P5 /P4 /P3 /P2.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact HspW1. }
    assert (HP6a0 : P6 !!! Regidx (mword_of_int 10 : mword 5)
                    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite /P6 /P5 /P4 /P3 /P2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hroot. }
    assert (HP6a1 : P6 !!! Regidx (mword_of_int 11 : mword 5) = va).
    { rewrite /P6 /P5 /P4 /P3 /P2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      reflexivity. }
    assert (HP6a2 : P6 !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int (Z.of_nat npages * 4096)).
    { rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /P5 lookup_total_insert.
      rewrite add_vec_zero_l.
      rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /P3 lookup_total_insert.
      rewrite add_vec_zero_l.
      rewrite /P2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hsz. }
    assert (HP6a3 : P6 !!! Regidx (mword_of_int 13 : mword 5) = pa).
    { rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /P4 lookup_total_insert.
      rewrite add_vec_zero_l.
      rewrite /P3 /P2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      reflexivity. }
    assert (HP6a4 : P6 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int perm).
    { rewrite /P6 /P5 /P4 /P3 /P2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hpermreg. }
    assert (HP6tp : P6 !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite /P6 /P5 /P4 /P3 /P2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      reflexivity. }
    (* [va]/[pa]/[vpn0]/[ppn0] for mappages coincide with kvmmap's *)
    assert (Hva_eq : P6 !!! Regidx (mword_of_int 11) = va) by exact HP6a1.
    assert (Hpa_eq : (autocast (T := mword) (subrange_vec_dec (P6 !!! Regidx (mword_of_int 13)) 55 12) : mword 44) = ppn0)
      by (rewrite HP6a3; reflexivity).
    (* the call *)
    iApply (wp_mappages_r R Φ γ γc bsie P6 t m npages perm (n - 2)%nat
              ltac:(lia)
              HP6a0
              ltac:(rewrite HP6a1; exact Hvaal)
              ltac:(rewrite HP6a3; exact Hpaal)
              HP6a2 Hnp HP6a4 Hpok
              ltac:(rewrite HP6a1; exact Hvab)
              ltac:(rewrite HP6a3; exact Hpab)
              Hrep
              ltac:(rewrite HP6a1; exact Hnone)
              with "Hcfg Htoken Htlbinv Htext Hpc Hfile [Hdeep] Hptree [Henv] [-]").
    { iEval (rewrite HP6sp). iEval (rewrite Hsprstk) in "Hdeep". iExact "Hdeep". }
    { iEval (rewrite HP6tp). iExact "Henv". }
    iIntros (mr t' k) "Hcfg Htoken Htlbinv Hpc Hfile Hstk Hptree Henv %Hkcs %Hbase' %Hrep' %Hpay".
    iEval (rewrite HP6sp) in "Hstk".
    iEval (rewrite HP6tp) in "Henv".
    (* pc back at +0x12; the frame cells recovered *)
    assert (HP6link : P6 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KM + 0x0e) : mword 64) 4).
    { rewrite /P6 lookup_total_insert. reflexivity. }
    assert (Hret12 : update_vec_dec (P6 !!! Regidx (mword_of_int 1 : mword 5)) 0 ('b"0" : mword 1) = mword_of_int (KM + 0x12)).
    { rewrite HP6link. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret12) in "Hpc".
    (* recovered facts *)
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HP6sp. }
    assert (Hmrtp : mr !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 4) ltac:(vm_compute; reflexivity)).
      exact HP6tp. }
    (* the vpn0/ppn0 in the mappages post are kvmmap's *)
    rewrite HP6a1 in Hrep'. rewrite HP6a3 in Hrep'.
    iPoseProof (ki_12 with "Htext") as "Hi12'".
    iPoseProof (ki_14 with "Htext") as "Hi14'".
    iPoseProof (ki_16 with "Htext") as "Hi16'".
    iPoseProof (ki_18 with "Htext") as "Hi18'".
    iPoseProof (ki_1a with "Htext") as "Hi1a'".
    destruct Hpay as [(Hkn & Ha0z) | (Hklt & Ha0m1)].
    2:{ (* ---- mappages FAILED (a0 = -1): bnez TAKEN -> panic ---- *)
      iApply (wp_cbnez_taken_s_zca_scfg_r R γc Φ (mword_of_int (KM + 0x12)) (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
                mr (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0m1; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi12' [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Htgt1c : add_vec (mword_of_int (KM + 0x12) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0"))))
              = mword_of_int (KM + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt1c) in "Hpc".
      iPoseProof (ki_1c with "Htext") as "Hi1c".
      iPoseProof (ki_20 with "Htext") as "Hi20".
      iPoseProof (ki_24 with "Htext") as "Hi24".
      (* +0x1c auipc a0 / +0x20 addi a0 / +0x24 jal panic -- the message
         setup does not matter; panic_wp accepts any register file *)
      iApply (wp_auipc_s_scfg_r R γc Φ (mword_of_int (KM + 0x1c)) (mword_of_int 10 : mword 5) (mword_of_int 6 : mword 20)
                mr (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi1c [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (Q1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec (mword_of_int (KM + 0x1c) : mword 64) (auipc_off (mword_of_int 6 : mword 20)))]> mr).
      assert (Hpp20 : add_vec_int (mword_of_int (KM + 0x1c) : mword 64) 4 = mword_of_int (KM + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      iApply (wp_addi4_s_scfg_r R γc Φ (mword_of_int (KM + 0x20)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0x16 : mword 12)
                Q1 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi20 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (Q2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec (Q1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x16 : mword 12)))]> Q1).
      assert (Hpp24 : add_vec_int (mword_of_int (KM + 0x20) : mword 64) 4 = mword_of_int (KM + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      iApply (wp_jal_gpr_s_zca_r R γc Φ (mword_of_int (KM + 0x24)) (mword_of_int 1 : mword 5) (mword_of_int 2094876 : mword 21)
                Q2 1%Qp
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi24 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpcpn : add_vec (mword_of_int (KM + 0x24) : mword 64) (sign_extend' 64 (mword_of_int 2094876 : mword 21)) = mword_of_int KernelSyms.panic) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpcpn) in "Hpc".
      iApply ("Hpanic" $! Φ _ with "Htext Hpc Hfile").
    }
    (* ---- mappages SUCCEEDED (k = npages, a0 = 0): bnez FALLS, epilogue ---- *)
    subst k.
    iApply (wp_cbnez_fall_s_scfg_r R γc Φ (mword_of_int (KM + 0x12)) (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              mr (dq:=DfracOwn 1)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0z; vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi12' [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp14 : add_vec_int (mword_of_int (KM + 0x12) : mword 64) 2 = mword_of_int (KM + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 ld ra,8(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (KM + 0x14)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              mr (mm !!! Regidx (mword_of_int 1)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi14' [Hc1] [-]").
    { iEval (rewrite Hmrsp Hb1). iExact "Hc1". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc1".
    iEval (rewrite Hmrsp Hb1) in "Hc1".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1))]> mr).
    assert (Hpp16 : add_vec_int (mword_of_int (KM + 0x14) : mword 64) 2 = mword_of_int (KM + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 ld s0,0(sp) *)
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spr).
    { rewrite /E1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hmrsp. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (KM + 0x16)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              E1 (mm !!! Regidx (mword_of_int 8)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi16' [Hc2] [-]").
    { iEval (rewrite HspE1 Hb2). iExact "Hc2". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc2".
    iEval (rewrite HspE1 Hb2) in "Hc2".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8))]> E1).
    assert (Hpp18 : add_vec_int (mword_of_int (KM + 0x16) : mword 64) 2 = mword_of_int (KM + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.addi sp,+16 *)
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spr).
    { rewrite /E2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact HspE1. }
    iApply (wp_caddi_gpr_s_r R γc Φ (mword_of_int (KM + 0x18)) csp_rs1 (mword_of_int 16 : mword 6)
              E2 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi18' [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (E3 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
    assert (Hpp1a : add_vec_int (mword_of_int (KM + 0x18) : mword 64) 2 = mword_of_int (KM + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    assert (HspE3 : E3 !!! Regidx csp_rs1 = sp0).
    { rewrite /E3 lookup_total_insert. rewrite HspE2.
      apply bv_eq. unfold spr, sp0.
      rewrite bv_add_unsigned. rewrite bv_add_unsigned.
      replace (bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)) : mword 64)) with 18446744073709551600 by (vm_compute; reflexivity).
      replace (bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)) with 16 by (vm_compute; reflexivity).
      rewrite bv_wrap_add_idemp_l.
      rewrite <- Z.add_assoc.
      replace (18446744073709551600 + 16) with (bv_modulus 64) by (vm_compute; reflexivity).
      rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned. }
    (* +0x1a ret *)
    assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /E3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /E2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /E1 lookup_total_insert. reflexivity. }
    assert (Hrt : update_vec_dec (add_vec (E3 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0" : mword 1) = ret_tgt).
    { rewrite HE3ra.
      replace (sign_extend' 64 (zeros' 12) : mword 64) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. reflexivity. }
    iApply (wp_cret_s_zca_scfg_r R γc Φ (mword_of_int (KM + 0x1a)) (mword_of_int 1 : mword 5) E3 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hrt; exact (bit0_update0_64 (mm !!! Regidx (mword_of_int 1))))
              with "Hcfg Htlbinv Hpc Hfile Hi1a' [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    iEval (rewrite Hrt) in "Hpc".
    (* ---- rebundle the frame and conclude ---- *)
    iAssert (stack_own sp0 2)%I with "[Hc1 Hc2]" as "Htop".
    { iEval (rewrite stack_own_slots; cbn [seq]).
      iSplitL "Hc1". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc1". }
      iSplitL "Hc2". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc2". }
      done. }
    iEval (rewrite -Hsprstk) in "Hstk".
    iDestruct (stack_own_split_2 sp0 2 n ltac:(lia) with "[$Htop $Hstk]") as "Hstk".
    iApply ("Hcont" $! E3 t' with "Hcfg Htoken Htlbinv Hpc Hfile Hstk Hptree Henv [%] [%] [%]").
    { (* callee_saved mm E3 *)
      pose proof (fun c Hc => callee_saved_lookup Hkcs c Hc) as Hcs.
      unfold callee_saved.
      assert (Hagree : forall c : mword 5, is_cs_idx c = true ->
                c <> mword_of_int 8 -> c <> csp_rs1 ->
                mr !!! Regidx c = mm !!! Regidx c).
      { intros c Hc Hc8 Hcsp.
        rewrite (Hcs c Hc).
        rewrite /P6 /P5 /P4 /P3 /P2 /W1.
        repeat (rewrite lookup_total_insert_ne;
          [| intros Habs; injection Habs as Habs2; subst c;
             first [ apply Hc8; reflexivity | apply Hcsp; reflexivity | vm_compute in Hc; discriminate ] ]).
        reflexivity. }
      split.
      { rewrite HspE3. reflexivity. }
      split.
      { rewrite /E3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite (Hcs (mword_of_int 4) ltac:(vm_compute; reflexivity)). exact HP6tp. }
      split.
      { rewrite /E3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E2 lookup_total_insert. reflexivity. }
      all: repeat split;
        (rewrite /E3; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
         rewrite /E2; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
         rewrite /E1; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
         apply Hagree; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]).
    }
    { exact Hbase'. }
    { exact Hrep'. }
  Qed.

  (* the record spec *)
  Lemma kvmmap_spec_holds (R : s_regime) : ⊢ kvmmap_spec R.
  Proof.
    iIntros (Φ γ γc bsie mm t m npages perm n)
      "%Hn %Hroot %Hvaal %Hpaal %Hsz %Hnp %Hpermreg %Hpok %Hvab %Hpab %Hrep %Hnone Hpanic".
    iApply (wp_kvmmap_r R Φ γ γc bsie mm t m npages perm n
              Hn Hroot Hvaal Hpaal Hsz Hnp Hpermreg Hpok Hvab Hpab Hrep Hnone
              with "Hpanic").
  Qed.

End Kvmmap.
